---
layout: post
title: "Part 4: Address calculations"
---
_This post describes the implementation of [pysmtgcc](https://github.com/kristerw/pysmtgcc). See "[GCC Translation Validation](https://kristerw.github.io/2022/09/13/translation-validation/)" for background information._

Address calculations can be done in two ways in GIMPLE:
* `ARRAY_REF`/`COMPONENT_REF`
* `POINTER_PLUS`

## ARRAY_REF/COMPONENT_REF
`ARRAY_REF` and `COMPONENT_REF` are used when indexing into arrays and structures. For example, if `s` is a structure
```c
struct {
  int a[4];
  int b;
} s;
```
Then the IR for
```c
int x = s.a[i];
```
will use a `COMPONENT_REF` asking for element `a` in `s`, and an `ARRAY_REF` asking for the element at index `i` in the array it gets from `COMPONENT_REF`.

`ARRAY_REF`/`COMPONENT_REF` mostly follows the rules in the C standard, so the behavior is undefined if the `ARRAY_REF` index is outside of the accessed object when dereferencing an element. For example, GCC knows that `s.a[i]` cannot access the memory of `s.b` ([godbolt](https://godbolt.org/z/We3PeMcqT)).

One complication is that it is allowed to take the address of the element "one past" the array (in this case, `&s.a[5]`), so the implementation must allow taking the address of "one past", but keep track of this so it can mark the program as UB if the pointer is used for load/store. This is not implemented for `pysmtgcc`.


### Flexible arrays
Another complication comes from arrays at the end of structures -- they may be declared without a size (or with the GCC extension `a[0]`). `pysmtgcc` will, in this case, limit the indexing by the memory block size.

But these "flexible arrays" are rather new[^c99] -- old C code just used an arbitrary size and wrote outside the array, so GCC cannot assume that the access is in bounds for arrays at the last element of a structure.[^strict_flex_arrays] `pysmtgcc` has not implemented this special case.

### More issues
Consider the C program below that returns a value read from a structure
```c
struct s {
  int a;
  int b;
};

int foo(int c, struct s *p)
{
  int t;
  if (c)
    t = p->a;
  else
    t = p->b;
  return t;
}
```
The GIMPLE version of this looks like
```c
int foo (int c, struct s *p)
{
  int t;

  <bb 2>:
  if (c_2(D) != 0)
    goto <bb 3>;
  else
    goto <bb 4>;

  <bb 3>:
  t_6 = p_4(D)->a;
  goto <bb 5>;

  <bb 4>:
  t_5 = p_4(D)->b;

  <bb 5>:
  # t_1 = PHI <t_6(3), t_5(4)>
  return t_1;
}
```
The problem for us happens in the `phiopt2` pass that hoist loads from adjacent structure elements:[^hoisting]
```c
int foo (int c, struct s *p)
{
  int t;

  <bb 2>:
  t_6 = p_4(D)->a;
  t_5 = p_4(D)->b;
  if (c_2(D) != 0)
    goto <bb 3>;
  else
    goto <bb 4>;

  <bb 3>:
  goto <bb 5>;

  <bb 4>:

  <bb 5>:
  # t_1 = PHI <t_6(3), t_5(4)>
  return t_1;
}
```
This made `plugin1.py` report a miscompilation because calling the original function `foo` with `p` pointing to a "small" memory block, such as
```c
struct s *p = malloc(4);
if (p)
  foo(1, p);
```
only access valid memory, while the optimized version reads out of bounds.

I am not sure exactly what the correct GIMPLE semantics is. The current implementation treats the use of `COMPONENT_REF` and `ARRAY_REF` as undefined behavior if the whole object does not fit in the available memory (even if the calculated address is within valid memory).

## POINTER_PLUS
Pointer arithmetic in C and C++ are somewhat restricted -- pointers must point into a memory object (or to the byte after), and arithmetic must not make the pointer go out of that range. But it is often convenient for compilers to be more lenient[^vectorization], so I assume GIMPLE allows more general addition.

But one important thing for optimizers is that you cannot do pointer arithmetic to move one pointer from one object to another. For example, if we have two arrays
```c
int a[16];
int b[16];
```
and code doing something like
```c
int *p = a;
p = p + i;
*p = 0;
```
then  `*p` can never access memory in `b`.[^one_past] The actual semantics for C are complicated and underspecified,[^provenance] and it is unclear to me how GIMPLE handles this. My current implementation makes `POINTER_PLUS` UB if it changes the memory id of the pointer. This seems to work well enough for now.

---

[^c99]: Well, 1999. But the C ecosystem does not move that fast.

[^strict_flex_arrays]: Unless you pass `-fstrict-flex-arrays`. See the blog post ["Bounded Flexible Arrays in C"](https://people.kernel.org/kees/bounded-flexible-arrays-in-c) for how to modernize C arrays for greater memory safety.

[^hoisting]: I guess this is to better hide memory latency by moving the loads early, which is free for the cases when they may be vectorized. Later passes sink the loads back again if they have not been optimized.

[^vectorization]: For example, vectorized code must often handle the last elements as a special case when there are not enough elements to load a vector. It is convenient to check by adding the vector size to the pointer and checking if the result is outside the object.

[^provenance]: See the draft technical specification ["A Provenance-aware Memory Object Model for C"](https://www.open-std.org/jtc1/sc22/wg14/www/docs/n3005.pdf)

[^one_past]: The pointer `p` may points to `b` if `b` is placed directly after `a`, but the program must never access the memory through `p`. GCC does, however, not accept that it points to `b` either ([PR 61502](https://gcc.gnu.org/bugzilla/show_bug.cgi?id=61502)), so this is not something we need to care about. And the `pysmtgcc` memory blocks have space between them, so this cannot happen anyway.

