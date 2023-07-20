---
layout: post
title: "Part 5: Pointer alignment"
---
_This post describes the implementation of [pysmtgcc](https://github.com/kristerw/pysmtgcc). See "[GCC Translation Validation](https://kristerw.github.io/2022/09/13/translation-validation/)" for background information._

I was planning to skip alignment checks in the `pysmtgcc` prototype because I thought it was only used for instruction selection -- not for optimizations.[^vectorization] But I got failures where GCC performed optimizations that assumed aligned pointers.

To illustrate this, consider the function
```c
int foo(int *left, int *right)
{
  left[3] = right[1];
  return right[1] + left[2];
}
```
which as IR looks like
```c
int foo (int * left, int * right)
{
  int _2;
  int _4;
  int _6;
  int _11;

  <bb 2> :
  _2 = MEM[(int *)right_9(D) + 4B];
  MEM[(int *)left_7(D) + 12B] = _2;
  _4 = MEM[(int *)right_9(D) + 4B];
  _6 = MEM[(int *)left_7(D) + 8B];
  _11 = _4 + _6;
  return _11;
}
```
The code loads twice from `right[1]`, and the `fre` pass (doing value numbering) optimizes away the second load
```c
int foo (int * left, int * right)
{
  int _2;
  int _6;
  int _11;

  <bb 2> :
  _2 = MEM[(int *)right_9(D) + 4B];
  MEM[(int *)left_7(D) + 12B] = _2;
  _6 = MEM[(int *)left_7(D) + 8B];
  _11 = _2 + _6;
  return _11;
}
```
But this optimization requires that the pointers are aligned! If the pointers, for example, had values
```
left  = 0x0100000000000002;
right = 0x0100000000000007;
```
then
```c
left[3] = right[1];
```
would overwrite part of `right[1]` and modify its value.

I am not sure of the exact semantics in GIMPLE -- for now, `pysmtgcc` checks alignment when the memory is read/written, but it allows unaligned pointers in other contexts (such as casting an unaligned `char*` to `int*`).

## Next problem
Making `pysmtgcc` check alignment solves the original issue, but gives us new problems...

The `pysmtgcc` alignment check uses the alignment of the type:
```python
if expr.type.alignmentof > 1:
    smt_bb.add_ub((offset & (expr.type.alignmentof - 1)) != 0)
```
Programs may also increase alignment using `__builtin_assume_aligned`, which `pysmtgcc` implements as making it UB if the pointer does not have sufficient alignment:
```python
if stmt.fndecl.name == "__builtin_assume_aligned":
    ptr = get_tree_as_smt(stmt.rhs[2], smt_bb)
    alignment = stmt.rhs[3].constant
    if alignment > 1:
        smt_bb.add_ub((ptr.offset & (alignment - 1)) != 0)
```
This works fine in the early passes, but GCC removes the built-ins halfway through the compilation, and the information about extra alignment is kept in a GCC-internal data structure. The result is that `pysmtgcc` for the later passes thinks that pointers only have alignment constraints as given by the type and reports that the program is miscompiled when GCC does an optimization taking advantage of the extra alignment. One example of this can be seen in
```c
void baz(unsigned char *buf, unsigned char *tab)
{
  tab = __builtin_assume_aligned(tab, 2);
  buf = __builtin_assume_aligned(buf, 2);
  unsigned v = tab[1] ^ (tab[0] << 8);
  buf[0] = ~(v >> 8);
  buf[1] = v;
}
```
where the store-merging pass combines the two 8-bit stores to a 16-bit store, which is correct because of the `__builtin_assume_aligned`, but `pysmtgcc` has lost the information about extra alignment.

We could query the internal GCC structures for the alignment by calling `get_object_alignment`, but the Python API does not export it, so this has to wait until the `smtgcc` release.

---

[^vectorization]: Pointer alignment is used in vectorization optimizations, but only for restricting the optimization to cases where the instructions can handle the optimized code. And `pysmtgcc` does not support vectors anyway.
