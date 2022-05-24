---
layout: post
title: Branch/cmove and compiler optimizations
---
I have recently seen several discussions on Twitter where people have been
surprised/annoyed by what the compilers do to their branchless code. Here
are some random comments on what the compilers do (and why).

# Branches vs. conditional move
Branch misprediction is very expensive. But conditional moves are also costly (as they increase the length of dependency chains), so it is not obvious that a branch that sometimes mispredicts is slower than a conditional move. [Agner Fog's optimization manual](https://www.agner.org/optimize/optimizing_assembly.pdf) says (for "`a = b > c ? d : e;`"):

> As a rule of thumb, we can say that a conditional jump is faster than a conditional move if the code is part of a dependency chain and the prediction rate is better than 75%.
> A conditional jump is also preferred if we can avoid a lengthy calculation of `d` or `e` when the other operand is chosen.

Most I see written about branches and conditional moves focus on writing branchless code. But branch predictors are amazing[^1] -- they can easily find a pattern in
how a branch is taken, and use correlated branches to improve the prediction rate.
So it is often the case that branches that seem unpredictable predict
better than 75% in reality, and doing it branchless makes the program slower.


# The ternary operator
One way that seems natural to get the compiler to generate branchless code
is to use the ternary operator, but that does not work. The reason is that
```c
r = c ? a : b;
```
does evaluate `a` only when the condition `c` is true and `b` only when
`c` is false, so the compiler front end must generate the same IR for this as for
```c
if (c)
  r = a;
else
  r = b;
```
At least when `a` and `b` may have side effects.

Both GCC and Clang generate IR with branches for ternary operators (even with
no side effects), so later optimization passes do not see any difference
between source code using the ternary operator or branches.


# Convincing GCC to make the right choice
### Branches
GCC is rather aggressive in using conditional moves for x86_64, and it is
common to find cases where using a branch instead would improve
performance.
It is often possible to make GCC emit a branch instruction by using
`__builtin_expect_with_probability` to tell it that the
branch is very likely.[^2] For example, the function
```c
int foo(int a, int b, int c)
{
  if (a == b)
    a &= c;
  return a;
}
```
is compiled to code using `cmove` while
```c
#define VERY_LIKELY(x) __builtin_expect_with_probability(!!(x), 1, 0.999)

int foo(int a, int b, int c)
{
  if (VERY_LIKELY(a == b))
    a &= c;
  return a;
}
```
is compiled to code with branches. ([godbolt](https://godbolt.org/z/Gzr7bEaef))

### Branchless
Many (most?) cases where GCC incorrectly decides to use a branch instead of
emitting branchless code comes from optimization passes transforming the
code to a form where the backend cannot change it to use conditional
moves.

For example, the program in [this blog post](https://lemire.me/blog/2021/07/14/faster-sorted-array-unions-by-reducing-branches/) has a loop ([godbolt](https://godbolt.org/z/ehhfzYqed))
```c++
while ((pos1 < size1) & (pos2 < size2)) {
  v1 = input1[pos1];
  v2 = input2[pos2];
  output_buffer[pos++] = (v1 <= v2) ? v1 : v2;
  pos1 = (v1 <= v2) ? pos1 + 1 : pos1;
  pos2 = (v1 >= v2) ? pos2 + 1 : pos2;
}
```
The comparisons are unpredictable, so the program runs faster if the loop
body is generated as branchless code, but GCC emits branches for updating `pos1` and `pos2`. The reason is that the sequence
```c++
  pos1 = (v1 <= v2) ? pos1 + 1 : pos1;
  pos2 = (v1 >= v2) ? pos2 + 1 : pos2;
```
has been optimized by [jump threading](https://developers.redhat.com/blog/2019/03/13/intro-jump-threading-optimizations#) to
```c
  if (v1 <= v2) {
    pos1 = pos1 + 1;
    if (v2 == v1)
      goto skip;
  } else {
skip:
    pos2 = pos2 + 1;
  }
```
which is too complex for the backend to emit as branchless code.

We can get rid of the branches in this case by rewriting the loop to prevent
jump threading from optimizing it:
```c++
while ((pos1 < size1) & (pos2 < size2)) {
  v1 = input1[pos1];
  v2 = input2[pos2];
  output_buffer[pos++] = (v1 <= v2) ? v1 : v2;
  pos1 += (v1 <= v2);
  pos2 += (v1 >= v2);
}
```


# LLVM backend introducing branches
LLVM optimization passes are aggressive in changing branchy code to use the
[`select`](https://llvm.org/docs/LangRef.html#select-instruction) IR
instruction (that choose one value based on a condition, without IR-level
branching) when possible. And `select` is typically generated as
a `cmove` instruction, so it should be easy to get branchless code. But `cmove`
is often slower than branches, so the backend can change `select` to branches
when it believes it is better.

This can be seen in this example taken from [Bug 39374](https://github.com/llvm/llvm-project/issues/39374) ([godbolt](https://godbolt.org/z/qxv96ofbM))
```c++
#include <cstddef>
#include <cstdint>
#include <utility>

void downHeap(uint64_t* top, size_t size, size_t pos) {
  size_t parent = pos;
  size_t child;
  while ((child = 2 * parent + 2) < size) {
    auto left = child - 1;
    child = top[left] < top[child] ? child : left;  // <<-- Unpredictable, should be CMOV
    if (top[parent] < top[child]) {
      std::swap(top[parent], top[child]);
      parent = child;
    } else {
      return;
    }
  }
  if (--child < size && top[parent] < top[child]) {
    std::swap(top[parent], top[child]);
  }
}
```
Clang supports `__builtin_unpredictable` that tells the compiler that the
branch condition is unpredictable and should therefore better be generated
as branchless code. But this built-in only affects the middle-end passes,
so it does not help the case above where it is the backend that is changing
the `select` instruction to branches.


# Straight-line code
Compilers may generate branches for straight-line code without ternary operators too.

### Clang
The function below (taken from a [blog post](https://dsprenkels.com/cmov-conversion.html) by Daan Sprenkels) tries to read an element from an array in a
side-channel resistant way, but the generated code generated by `clang`
contains branches that depend on the secret index.
([godbolt](https://godbolt.org/z/oM5aWeYW4))
```c++
#include <cstddef>
#include <cstdint>

// Select an element from an array in constant time.
uint64_t constant_time_lookup(const size_t secret_idx,
                              const uint64_t table[8]) {
  uint64_t result = 0;
  for (size_t i = 0; i < 8; i++) {
    const bool cond = i == secret_idx;
    const uint64_t mask = (-(int64_t)cond);
    result |= table[i] & mask;
  }
  return result;
}
```
Here, the LLVM `instcombine` pass has optimized the sequence
```
  %9 = icmp eq i64 %4, %0
  %11 = zext i1 %9 to i64
  %12 = sub nsw i64 0, %11
  %15 = and i64 %14, %12
```
to
```
  %9 = icmp eq i64 %4, %0
  %15 = select i1 %9, i64 %14, i64 0
```
and the `select` instruction is then changed to branches in the backend.

### GCC
GCC can also introduce branches in straight-line code. For example, the
front end generates IR for
```c
unsigned r = ((a & 0xffff0000) != 0) << 4;
```
as[^3]
```c
unsigned r;
if (a > 65535)
  r = 16;
else
  r = 0;
```
This is typically turned back to straight-line code by later optimizations,
but not always -- it is easy to construct similar examples where the branches
are present in the generated code: ([godbolt](https://godbolt.org/z/3GqMsY6v3))
```c
unsigned foo(unsigned a, unsigned b)
{
  unsigned t = ((a > 2) != 0) << 1;
  t |= ((a < 10) != 0) << 2;
  return b >> t;
}
```


# Conclusion
To summarize the main points made in this blog post:
* Branches are sometimes faster than `cmove`, and `cmove` is sometimes faster
  than branches.
* Sometimes compilers do the wrong thing:
  * `__builtin_expect` does not help convince GCC to use branches...
  * ... but `__builtin_expect_with_probability` may help.
  * `__builtin_unpredictable` does not guarantee that LLVM generates
    branchless code.
* Compilers may insert branches in straight-line code.

<br>
<br>

----

[^1]: Dan Luu has written [a good blog post](https://danluu.com/branch-prediction/)  about how branch prediction work.

[^2]: `__builtin_expect` does not mark it likely enough, so a new built-in function `__builtin_expect_with_probability`  was introduced in GCC 9 for this use case ([Bug 83610](https://gcc.gnu.org/bugzilla/show_bug.cgi?id=83610)).

[^3]: I guess the idea is to expose the constants in the IR to make it easier for the early optimization passes to see which values are possible.
