---
layout: post
title: "Part 6: Uninitialized memory"
---
_This post describes the implementation of [smtgcc](https://github.com/kristerw/smtgcc)._

Programs may have uninitialized variables, so smtgcc must be able to handle that.

## Uninitialized variables in C
A useful mental model when programming in C is that the use of uninitialized variables is always UB, but the situation is more complex when trying to formalize the semantics. The C standard says ([C23 6.3.2.1p2](https://www.open-std.org/jtc1/sc22/wg14/www/docs/n3096.pdf#subsubsection.6.3.2.1)):

> If the lvalue designates an object of automatic storage duration that could have been declared with the `register` storage class (never had its address taken), and that object is uninitialized (not declared with an initializer and no assignment to it has been performed prior to use), the behavior is undefined.

So the function below invokes undefined behavior when reading `tmp`:
```c
unsigned int foo1(void)
{
  unsigned int tmp;
  return tmp + 1;
}
```
But this is only UB when the address of `tmp` is not taken, so the code below is _not_ UB by 6.3.2.1:
```c
unsigned int foo2(void)
{
  unsigned int tmp;
  unsigned int *p = &tmp;
  return tmp + 1;
}
```
It is possible to interpret the standard in a way that makes this too UB, based on the text about non-value representations ([C23 6.2.6.1p5](https://www.open-std.org/jtc1/sc22/wg14/www/docs/n3096.pdf#subsubsection.6.2.6.1)):

> Certain object representations need not represent a value of the object type. If such a representation is read by an lvalue expression that does not have character type, the behavior is undefined.<sup>55)</sup> If such a representation is produced by a side effect that modifies all or any part of the object by an lvalue expression that does not have character type, the behavior is undefined. Such a representation is called a non-value representation.

Footnote 55 clarifies this:

> <sup>55)</sup>Thus, an automatic variable can be initialized to a non-value representation without causing undefined behavior, but the value of the variable cannot be used until a proper value is stored in it.

So `foo2` is also UB if we assume automatic variables are always created in a non-value representation. But the `char` type does not have a non-value representation, so it is still allowed to use uninitialized `char` variables:
```c
unsigned char foo3(void)
{
  unsigned char tmp;
  unsigned char *p = &tmp;
  return tmp + 1;
}
```
### Padding bits
Padding bits are also uninitialized (which is described in [C23 6.2.6.1p6](https://www.open-std.org/jtc1/sc22/wg14/www/docs/n3096.pdf#subsubsection.6.2.6.1)):

> When a value is stored in an object of structure or union type, including in a member object, the bytes of the object representation that correspond to any padding bytes take unspecified values.<sup>56)</sup> [...]

Footnote 56 clarifies that the compiler does not need to preserve the padding:

> <sup>56)</sup>Thus, for example, structure assignment need not copy any padding bits.

## Uninitialized variables in smtgcc
Smtgcc operates on the GIMPLE IR which has semantics similar to C, but the GIMPLE semantics is more permissive (for example, dead code elimination would not be allowed if GIMPLE followed C23 6.3.2.1p5), and there are cases where it is not completely clear what the GIMPLE semantics is.

It was unclear to me exactly what needed to be implemented. I have therefore done the implementation in small steps in order to figure out the details of the semantics and potential issues, while still having a useful (but imprecise) implementation.


# Implementation -- 1st attempt

The first implementation did not handle uninitialized memory in any special way --- the value read from an uninitialized variable is simply whatever happens to be in memory. The memory [is implemented as an SMT-LIB array](https://kristerw.github.io/2023/07/17/memory-representation/), so each byte is initialized with a symbolic value, and the SMT solver therefore checks that the optimized function produces the same result as the original for all possible values of the uninitialized variables.

This works well enough to be useful, but it reports spurious errors in some cases involving padding or uninitialized structure elements. To illustrate the issue, consider a function that copies a partially initialized structure:
```c
struct S
{
  int nof_elems;
  int elems[3];
};

struct S s;

void foo(int a, int b)
{
  struct S t;
  t.elems[0] = a;
  t.elems[1] = b;
  t.nof_elems = 2;
  s = t;
}
```
The GCC front end translates this to GIMPLE IR in the natural way:
```
void foo (int a, int b)
{
  struct S t;

  <bb 2> :
  t.elems[0] = a_2(D);
  t.elems[1] = b_4(D);
  t.nof_elems = 2;
  s = t;
  t ={v} {CLOBBER(eos)};
  return;
}
```
The SRA pass then optimizes this to code that writes to the global variable directly:
```
void foo (int a, int b)
{
  int t$elems$2;
  int t$elems$1;
  int t$elems$0;
  int t$nof_elems;
  struct S t;

  <bb 2> :
  t$elems$0_9 = a_2(D);
  t$elems$1_10 = b_4(D);
  t$nof_elems_11 = 2;
  s.nof_elems = t$nof_elems_11;
  MEM <int> [(struct S *)&s + 4B] = t$elems$0_9;
  MEM <int> [(struct S *)&s + 8B] = t$elems$1_10;
  MEM <int> [(struct S *)&s + 12B] = t$elems$2_15(D);
  return;
}
```
But the optimized function does not write the same value to `s.elems[2]`. In the original, `s.elems[2]` gets its value from the uninitialized `t.elems[2]`. In the optimized version, it instead gets the value from the uninitialized variable `t$elems$2`, which is not guaranteed to be the same. As a result, smtgcc reports that the SRA pass miscompiles the function because the memory state differs.

So smtgcc needs to handle uninitialized memory in a better way...


# Implementation -- 2nd attempt
The second implementation tracked the status of each bit as `0`, `1`, or `i` (indefinite), where `i` is used for padding bits and uninitialized variables. I intentionally use the term "indefinite" that does not appear in the C standard to avoid confusion with its notions of "indeterminate" and "unspecified value", as the GIMPLE/smtgcc semantics is not identical to the C semantics.

Smtgcc sets uninitialized local variables and padding bits in global variables to indefinite before analysis begins. Unions in global memory are somewhat tricky because we do not know which member type will actually be used, so bits that are uninitialized regardless of which union type applies are set to indefinite, while all other bits are treated as normal defined (symbolic) bits.

The comparison that verifies the returned result and global memory state for `src` and `tgt` ignores bits where `src` has an indefinite value. This fixes the issue with uninitialized bits in structures described in the previous section.

## Semantics

The first implementation was maximally permissive, so I decided to err in the other direction and make the second implementatio too strict in order to find interesting special cases. The idea is that the use of indefinite bits in general is UB, but a few cases must be permitted --- both because of structure padding, and to allow reasonable optimizations.

To begin with, it must be allowed to read/write values with indefinite bits, otherwise it would not be possible to implement, for example, `memcpy` of structures with padding. This implies that phi nodes must allow and propagate indefinite bits, because there are passes that can introduce a phi node for the stores. This can be seen with the following GIMPLE function:
```
int a, b, c;

void foo (int x)
{
  int b.0_1;
  int c.1_2;

  <bb 2> :
  if (x_4(D) == 0)
    goto <bb 3>;
  else
    goto <bb 4>;

  <bb 3> :
  b.0_1 = b;
  a = b.0_1;
  goto <bb 5>;

  <bb 4> :
  c.1_2 = c;
  a = c.1_2;

  <bb 5> :
  return;
}
```
The phiopt pass transforms this to:
```
int a, b, c;

void foo (int x)
{
  int b.0_1;
  int c.1_2;
  int cstore_6;

  <bb 2> :
  if (x_4(D) == 0)
    goto <bb 3>;
  else
    goto <bb 4>;

  <bb 3> :
  b.0_1 = b;
  goto <bb 5>;

  <bb 4> :
  c.1_2 = c;

  <bb 5> :
  # cstore_6 = PHI <b.0_1(3), c.1_2(4)>
  a = cstore_6;
  return;
}
```
The compiler may change simple if-statements to `COND_EXPR` (which selects between two values), so it follows that `COND_EXPR` must also be valid for indefinite values.

Bitwise operations on indefinite data must also be supported. Consider the GIMPLE function:
```
struct S
{
  unsigned char a:2, b:3;
} s;

void foo ()
{
  <bb 2> :
  s.a = 0;
  s.b = 7;
  return;
}

```
The store-merging pass transforms this into a single load and store using bitwise logic:
```
void foo ()
{
  unsigned char _4;
  unsigned char _5;
  unsigned char _6;

  <bb 2> :
  _4 = MEM[(struct S *)&s];
  _5 = _4 & 224;
  _6 = _5 | 28;
  MEM[(struct S *)&s] = _6;
  return;
}
```
If any use of indefinite bits were UB, this optimization would be invalid because the memory read `_4` contains indefinite padding bits, making `_4&224` UB. We must therefore special-case the bitwise `BIT_AND_EXPR`/`BIT_IOR_EXPR` operations so they propagate invalid bits instead of invoking UB, and the calculation is done so that
```
0 | i -> i
1 | i -> 1
0 & i -> 0
1 & i -> i
```
Similarly, GCC transforms some bit swizzling as shifts and bitwise logic, so we must allow shifts (and rotate for consistency) on indefinite data. In general, operations that are just moving bits (such as creating a vector out of elements, or permuting bits) are permitted with indefinite bits.

The semantics above resolves the problems found in the first implementation, but there are some new issues...

## Issues -- hoisting
Consider the C function `foo`:
```c
int a, b, c, d;

void foo(void)
{ 
  int j;
  while (1)
    { 
      d &= a > (b > 3 && j != 0);
      if (!c)
        break;
    }
}
```
This does not invoke UB as long as `b` is greater than 3. But compiling this with
```
-O2 -ftree-loop-if-convert
```
makes GCC hoist the comparison `j!=0` and the optimized function is now always UB.

The compiler should arguably detect that `j` is uninitialized and not hoist the comparison, but it cannot detect the use of uninitialized values in the general case. Consider this slightly modified function:
```c
int a, b, c, d;

void foo(int *p)
{ 
  int j = *p;
  while (1)
    { 
      d &= a > (b > 3 && j != 0);
      if (!c)
        break;
    }
}
```
The pointer `p` may point to uninitialized data, which would cause the same problem if the comparison is hoisted. So our semantics essentially forbids code hoisting.

## Issues -- vectorization
GIMPLE vector semantics is, for most vector operations, the same as for scalar operations on each element, but there are cases where this causes problems if use of indefinite data is UB. For example, the C function
```c
int foo(int *p, int n)
{
  for (int i = 0; i < n; i++)
    p[i] += 1;
}
```
when compiled for RISC-V as
```
riscv64-elf-gcc -O3 -march=rv64gcv -c foo.c
```
it is vectorized as
```
int foo (int * p, int n)
{
  vector([4,4]) int * vectp_p.10;
  vector([4,4]) int vect__5.9;
  vector([4,4]) int vect__4.8;
  vector([4,4]) int D.2930;
  vector([4,4]) int * vectp_p.6;
  vector([4,4]) int _7(D);
  unsigned long ivtmp_18;
  unsigned long _28;
  unsigned long ivtmp_29;
  unsigned long ivtmp_30;
  unsigned long _31;

  <bb 2> :
  if (n_9(D) > 0)
    goto <bb 3>;
  else
    goto <bb 5>;

  <bb 3> :
  _28 = (unsigned long) n_9(D);

  <bb 4> :
  # vectp_p.6_14 = PHI <vectp_p.6_13(4), p_10(D)(3)>
  # vectp_p.10_25 = PHI <vectp_p.10_26(4), p_10(D)(3)>
  # ivtmp_29 = PHI <ivtmp_30(4), _28(3)>
  _31 = .SELECT_VL (ivtmp_29, POLY_INT_CST [4, 4], { 0, ... });
  ivtmp_18 = _31 * 4;
  vect__4.8_6 = .MASK_LEN_LOAD (vectp_p.6_14, 32B, { -1, ... }, _7(D), _31, 0);
  vect__5.9_23 = vect__4.8_6 + { 1, ... };
  .MASK_LEN_STORE (vectp_p.10_25, 32B, { -1, ... }, _31, 0, vect__5.9_23);
  vectp_p.6_13 = vectp_p.6_14 + ivtmp_18;
  vectp_p.10_26 = vectp_p.10_25 + ivtmp_18;
  ivtmp_30 = ivtmp_29 - _31;
  if (ivtmp_30 != 0)
    goto <bb 4>;
  else
    goto <bb 5>;

  <bb 5> :
  return;
}
```
Here, `.MASK_LEN_LOAD` is how GCC represents a load corresponding to the RISC-V assembly
```
  vsetvli a5,a1,e32,m1,ta,ma
  vle32.v v1,0(a0)
```
It loads the number of bytes specified by `_31`, and the remaining bytes in the vector (if any) are filled from `_7(D)`, which is an uninitialized variable. The loaded vector is then used as
```
  vectp_p.10_26 = vectp_p.10_25 + ivtmp_18;
```
which is UB with our semantics if `.MASK_LEN_LOAD` has used the uninitialized variable for any element.

# Implementation -- 3rd attempt

For the third implementation (which is the current smtgcc as of April 2026), bits now have the value `0` or `1`, and each bit has a flag indicating whether it is indefinite. Operations propagate the indefinite flag in the same way as indefinite bits were propagated in the 2nd implementation, with the difference that operations that were UB due to indefinite bits now instead sets the indefinite flag on all bits in the result.

The bits marked as indefinite may change value between optimization passes, as described for the 1st attempt. That example now works correctly, but there are other cases where smtgcc could report spurious errors. For example:
```c
char a[256];

char foo(void)
{
  unsigned char x;
  a[x] = 0;
}
```
If a pass changes the underlying memory for `x`, then `a[x]` may write to a different element of the array compared to the original, causing smtgcc to report a miscompilation. This is fixed by making it UB to load or store with indefinite bits in the address.

A similar problem occurs with conditional branches:

```c
int foo(void)
{
  char c;
  if (c)
    return 0;
  else
    return 1;
}
```
We therefore make it UB to branch on an indefinite value. (For `COND_EXPR`, we mark all bits in the result as indefinite if the condition is indefinite). There is now a new special case to handle. GCC may optimize
```c
if (x != 0 | y != 0)
  ...
```
to
```c
if ((x | y) != 0)
  ...
```
This is a perfectly fine optimization, but it fails with our semantics when there are indefinite bits. Consider what happens when `x` has the value `1` and `y` has all bits indefinite. For the original if-statement, `x!=0` is `1` and `y!=0` is indefinite, but `1|i` is `1`, so the condition evaluates to `1`. For the optimized code, `x|y` has the value where the least significant bit is `1`, and the rest have the indefinite flag set, so the comparison is indefinite.

This is addressed by defining `EXPR_NE` and `EXPR_EQ` to return a defined result if the result is the same regardless of how we assign 0 or 1 to the indefinite bits. But this is not a good solution... We usually expect the equivalence:

$$
x < 0 \lor x > 0 \iff x \neq 0
$$

While our semantics only guarantee:

$$
x < 0 \lor x > 0 \implies x \neq 0
$$

This does not seem to be a problem in practice (as the compiler usually does not split `x!=0`), but the semantics is _wrong_.

## Workarounds
There are a few cases where smtgcc reports spurious errors because GCC treats the code as UB due to uninitialized variables, while smtgcc does not. Two workarounds have been implemented to eliminate most of these false positives.

### Workaround 1 -- VRP
Consider the C function `foo`:
```c
int foo(int a)
{
  int x;
  switch (a)
    {
    case 1:
      x = 1;
      break;
    case 10:
      x = 2;
      break;
    }
  return x;
}
```
which in GIMPLE is:
```
int foo (int a)
{
  int x;

  <bb 2> :
  switch (a_2(D)) <default: <L2> [INV], case 1: <L0> [INV], case 10: <L1> [INV]>

  <bb 3> :
<L0>:
  goto <bb 5>; [INV]

  <bb 4> :
<L1>:

  <bb 5> :
  # x_1 = PHI <x_3(D)(2), 1(3), 2(4)>
<L2>:
  return x_1;
}
```
The VRP pass assigns the range `[1, 2]` to `x_1`. This is not true if if the uninitialized value of `x` reaches the phi node, and smtgcc reports that the VRP pass has miscompiled the function.

As a workaround, the VRP range is ignored when the value contains indefinite bits.

### Workaround 2 -- new variables
Consider the function `foo`:
```c
int foo (int a, int b)
{
  int c[10];
  return a * c[1] == b * c[1];
}
```
which in GIMPLE is:
```
int foo (int a, int b)
{
  int c[10];
  int _1;
  int _2;
  int _3;
  int _4;
  _Bool _5;
  int _9;

  <bb 2> :
  _1 = c[1];
  _2 = _1 * a_7(D);
  _3 = c[1];
  _4 = _3 * b_8(D);
  _5 = _2 == _4;
  _9 = (int) _5;
  c ={v} {CLOBBER(eos)};
  return _9;
}
```
The SRA pass replaces the uninitialized `c[1]` with a new uninitialized variable `c$1`:
```
int foo (int a, int b)
{
  int c$1;
  int _1;
  int _2;
  int _3;
  int _4;
  _Bool _5;
  int _9;

  <bb 2> :
  _1 = c$1_11(D);
  _2 = _1 * a_7(D);
  _3 = c$1_11(D);
  _4 = _3 * b_8(D);
  _5 = _2 == _4;
  _9 = (int) _5;
  return _9;
}
```
The issue is that `c[1]` and `c$1` are not guaranteed to hold the same value. It is therefore possible for `a*c$1` to overflow in situations where `a*c[1]` would not, meaning the transformed program can become UB in cases where the original was not.

As a workaround, uninitialized `SSA_NAME` variables are initialized to 0, which in practice avoids the problem.


# Appendix: Details of the current implementation
The current implementation (as of April 2026) follows the "3rd attempt" described above.

Each bit in the program is tracked as two bits:
* One bit holding the value.
* One flag bit indicating whether the bit is indefinite.

For most operations, values containing indefinite bits behave normally, but the entire result is returned with all bits flagged as indefinite. For example, `PLUS_EXPR ` of two signed values adds the values and checks for overflow (which invokes undefined behavior). If any input bit is indefinite, then all bits in the result are marked as indefinite.

Some operations propagate indefinite bits differently:
 * **Vector operations that operate element-wise** produce each element through the corresponding scalar operation. For example, if only one element of a vector `PLUS_EXPR` has indefinite bits, only the corresponding element of the result is indefinite.
 * **Operations that only move bits** preserve both the bit values and their indefinite flags.
    * `COMPLEX_EXPR`, `IMAGPART_EXPR`, `REALPART_EXPR`
    * `VIEW_CONVERT_EXPR`
    * `BIT_FIELD_REF`, `BIT_INSERT_EXPR`
    * `PAREN_EXPR`
    * `CFN_BUILT_IN_BSWAP`
 * **Instructions that choose between values** are treated as moving the selected bits when the selection condition is not indefinite. If the condition is indefinite, the result is indefinite.
    * `COND_EXPR`
    * `VEC_COND_EXPR`
    * All `CFN_COND_*` built-in functions
    * `CFN_VCOND_MASK`, `CFN_VCOND_MASK_LEN`
    * `VEC_PERM_EXPR`
 * **Shift operations** where the shift amount contains indefinite bits return a result where all bits are indefinite. Otherwise, it is treated as moving the bits. For signed `RSHIFT_EXPR`, if the most significant bit is indefinite, the new bits added at the top during shifting are also indefinite.
     * `LSHIFT_EXPR`
     * `RROTATE_EXPR`
     * `LROTATE_EXPR`
     * `RSHIFT_EXPR`
 * **Bitwise operations** allow indefinite bits, where "`1|i`" evaluates to `1`, "`0&i`" evaluates to `0`, and in all other cases "`x op i`" evaluates to `i`.
     * `BIT_AND_EXPR`
     * `BIT_IOR_EXPR`
     * `BIT_NOT_EXPR`
     * `BIT_XOR_EXPR`
 * **Conversion instructions** between integral types propagate indefinite bits in the natural way: truncation behaves like a `BIT_FIELD_REF`, zero extension prepends `0` bits (with the indefinite flag cleared), and sign extension replicates the most significant bit (including its indefinite flag). Converting to a `RECORD_TYPE` or `UNION_TYPE` sets padding bits to indefinite.
     * `CONVERT_EXPR`
     * `NOP_EXPR`
 * **Equality comparisons** on values with indefinite bits return a result with the indefinite flag cleared if the result is independent of the indefinite bits.
    * `EQ_EXPR`
    * `NE_EXPR`

## Memory state
The initial memory state is configured so that local variables are indefinite, and padding in global variables is indefinite.

Loading an object of a type containing padding sets the indefinite flag on the padding bits. This is often redundant, but necessary to ensure correct padding bits when loading from memory initialized by a different type.

Storing an object of a type containing padding sets the indefinite flag on the padding bits.

## Workarounds
GIMPLE treats some uses of uninitialized data as undefined behavior, while the current smtgcc implementation does not. Two workarounds are implemented to avoid reporting spurious errors:
* The VRP range is ignored for variables containing indefinite bits.
* Uninitialized `SSA_NAME` variables are initialized to 0 with all bits marked as indefinite.
