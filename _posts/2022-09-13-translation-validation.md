---
layout: post
title: GCC Translation Validation
---
I am planning to do some work with SMT solvers and GCC. I usually
start new projects by doing a naive implementation of the critical part
to get a feel for the problems and find out what I need to learn before
the real implementation. So I started this project by building a simple translation
validator, similar to the LLVM [Alive2](https://github.com/AliveToolkit/alive2)
(but with many limitations).

My implementation, [pysmtgcc](https://github.com/kristerw/pysmtgcc), is rather limited, but has already found a few bugs in GCC[^bugs] by running the tool on the `c-c++-common`, `gcc.c-torture`, `gcc.dg`, and `gcc.misc-tests` tests suites.


# What the tool does
The tool takes GIMPLE IR for two functions and checks that the second is a
refinement of the first. That is,

* The returned value is the same for both functions for all input that
  does not invoke undefined behavior.
* The second does not have any undefined behavior that the first does not have.
* The global memory is the same after invoking both functions with input
  that does not invoke undefined behavior.

The functionality is implemented as GCC python plugins: `plugin1.py` and `plugin2.py`.[^naming]

## plugin1.py
`plugin1.py` compares the IR before/after each GIMPLE pass[^each_pass] and
complains if the resulting IR is not a refinement of the input (that is, if the GIMPLE pass miscompiled the program).

For example, compiling the function `f7` from [PR 106523](https://gcc.gnu.org/bugzilla/show_bug.cgi?id=106523)
```c
unsigned char f7(unsigned char x, unsigned int y)
{
  unsigned int t = x;
  return (t << y) | (t >> ((-y) & 7));
}
```
with a compiler where PR 106523 is not fixed (for example, GCC 12.2) using `plugin1.py`
```
gcc -O3 -fno-strict-aliasing -c -fplugin=python -fplugin-arg-python-script=plugin1.py pr106523.c
```
gives us the output
```
pr106523.c: In function 'f7':
pr106523.c:1:15: note: Transformation ccp -> forwprop is not correct (retval).
    1 | unsigned char f7(unsigned char x, unsigned int y)
      |               ^~
pr106523.c:1:15: note: [y = 13, x = 198]
src retval: 24
tgt retval: 216
```
telling us that the forwprop[^passes] pass miscompiled the function so it now returns `216` instead of `24` when called as `f7(198, 13)`.



## plugin2.py
`plugin2.py` requires the translation unit to consist of two functions named `src` and `tgt`, and it verifies that `tgt` is a refinement of `src`.

For example, testing changing the order of signed addition
```c
int src(int a, int b, int c)
{
  return a + c + b;
}

int tgt(int a, int b, int c)
{
  return a + b + c;
}
```
by compiling as
```
gcc -O3 -fno-strict-aliasing -c -fplugin=python -fplugin-arg-python-script=plugin2.py example.c
```
gives us the output
```
example.c: In function 'tgt':
example.c:6:5: note: Transformation is not correct (UB).
    6 | int tgt(int a, int b, int c)
      |     ^~~
example.c:6:5: note: [c = 1793412222, a = 3429154139, b = 2508144171]
```
telling us that `tgt` invokes undefined behavior in cases where `src` does not,
and gives us an example of input where this happen (the values are, unfortunately, written as unsigned values. In this case, it means `[c = 1793412222, a = -865813157, b = -1786823125]`).

**Note**: `plugin2.py` works on the IR from the `ssa` pass, i.e., early enough that the compiler has not done many optimizations. But GCC does peephole optimizations earlier (even when compiling as `-O0`), so you cannot use this plugin to test such optimizations. It is good practice to check with `-fdump-tree-ssa` that the IR used by the tool looks as expected.


# Limitations
Some of the major limitations in the current version:
* Function calls are not implemented.
* Loops are not implemented.
* The `CONSTRUCTOR` tree-code is ignored[^constructor]. This is used for brace-enclosed initializers for a structure or an array, which means that the tool will report bogus errors for most programs initializing structures and arrays.
* Support for memory operations is a bit shaky:
  * The tool is not tracking uninitialized memory.
  * It is confused about what memory can be pointed to by global pointers.
  * `malloc` etc. are not supported.
  * The tool often reports spurious memory-related errors unless `-fno-strict-aliasing` is passed to the compiler.
  * Pointer size/memory order is hardcoded as 64 bits/little-endian.
  * ...

Another annoying limitation is that GCC is doing folding (i.e., peephole optimizations) before running GIMPLE passes, so the tool will not find bugs in that code. Alive/Alive2 found several bugs in the LLVM equivalent `instcombine` pass, so it is likely that GCC also has bugs in its peephole optimizations.

# How pysmtgcc works
I will follow up this blog post with a series of posts describing how this works, design decisions, and what I have learned. Tentative outline:
1. [Writing a GCC plugin in Python](https://kristerw.github.io/2022/10/20/gcc-python-plugin/)
2. [Verifying GCC optimizations using an SMT solver](https://kristerw.github.io/2022/11/01/verifying-optimizations/)
3. [Memory representation](https://kristerw.github.io/2023/07/17/memory-representation/)
4. [Address calculations](https://kristerw.github.io/2023/07/18/address-calculations/)
5. [Pointer alignment](https://kristerw.github.io/2023/07/20/pointer-alignment/)
6. Problems with pointers
7. Uninitialized memory
8. Control flow

# Further work
I plan to spend some time improving the memory handling, but then I'll declare this experiment to be "done" and start preparing for a better implementation (using C++ instead of Python).

----

[^bugs]: [106513](https://gcc.gnu.org/bugzilla/show_bug.cgi?id=106513), [106523](https://gcc.gnu.org/bugzilla/show_bug.cgi?id=106523), [106744](https://gcc.gnu.org/bugzilla/show_bug.cgi?id=106744), [106883](https://gcc.gnu.org/bugzilla/show_bug.cgi?id=106883), [106884](https://gcc.gnu.org/bugzilla/show_bug.cgi?id=106884), [106990](https://gcc.gnu.org/bugzilla/show_bug.cgi?id=106990), [108625](https://gcc.gnu.org/bugzilla/show_bug.cgi?id=108625), [109626](https://gcc.gnu.org/bugzilla/show_bug.cgi?id=109626)

[^naming]: Naming is hard.

[^each_pass]: Some passes are not checked as they do things that the tool cannot follow; mostly IPA passes, but also passes such as `esra` that give us spurious errors because of limitations in the current memory implementation.

[^passes]: The message says "`ccp -> forwprop`" where `ccp` is the pass before the offending pass. This makes it easier to identify which execution misbehaved for passes that are run multiple times (the python API does not give us the pass number used in GCC dumps).

[^constructor]: This is because `CONSTRUCTOR` is not fully implemented in `gcc-python-plugin` -- it gives us an object without any data. We could just report "not implemented", but that would make most tests fail to analyze as `CONSTRUCTOR` is also used to report the end of scope for memory objects.
