---
layout: post
title: "Part 3: Memory representation"
---
_This post describes the implementation of [pysmtgcc](https://github.com/kristerw/pysmtgcc). See "[GCC Translation Validation](https://kristerw.github.io/2022/09/13/translation-validation/)" for background information._


Memory semantics is tricky to formalize. But we do not need a perfect formalization to find bugs in the compiler -- a simplistic formalization will make the tool miss some bugs (or report things that are not bugs), but it may still be useful.

My strategy has been to start with a simple model based on C and C++ and then refine the model as I find (valid) optimizations that are invalid with the overly simplistic model or things that I think `pysmtgcc` should be able to detect.

The memory semantics implemented in `pysmtgcc` is only the first step toward the goal, so this blog series will discuss how to improve the implementation. I have implemented most of this in my upcoming, vastly improved, C++ version of the tool (`smtgcc`) that I intend to release soon.

I believe my current implementation is reasonable, but it does not handle "strict aliasing" and `restrict`, so the tools report miscompilations when the compiler leverages the refined aliasing information. I always pass the options
```
-fno-strict-aliasing -D__restrict__="" -D__restrict="" -Drestrict=""
```
when using `pysmtgcc` or `smtgcc` to avoid this.

# Memory representation
`pysmtgcc` represent memory as a large array of bytes using a `z3.Array`. The `z3.Array` behaves similarly to a hash table or dictionary in that it doesn't allocate memory for elements that aren't in use. This feature allows us to generate an array of \\(2^{64}\\) elements indexed by the memory address (represented as a 64-bit bitvector), and the value corresponds to the byte's value at that address.
```python
memory = z3.Array(".memory", z3.BitVecSort(64), z3.BitVecSort(8))
```
Reading the byte pointed to by `ptr` is done as:
```python
value = z3.Select(memory, ptr)
```
Arrays are immutable, so writing `value` to `ptr` is done by the `z3.Store` function that generates a new array consisting of the original array but with one element changed:
```python
memory = z3.Store(memory, ptr, value)
```

# Variables and other valid memory
Memory accesses are only allowed in valid memory ranges (memory representing a variable, memory returned from `alloca` or `malloc`[^allocated_mem], etc.). These memory ranges are called "memory blocks" in the source code, and they consist of a "memory id" identifying the block and a "size" for the size of the block.

We treat the `PTR_ID_BITS` most significant bits of pointers as the memory id, and the remaining bits can be viewed as an offset into the memory block. Or in other words, the memory block is placed at address
```python
mem_id << PTR_OFFSET_BITS
```

## UB checks for invalid memory
We must check that a pointer `ptr` points at valid memory when we load/store a byte. This is done in two steps:
* Get the size for the memory block corresponding to the pointer's memory id.
* Check that the offset is less than the size of the memory block (the size for invalid memory blocks is set to 0, so this check always returns `false` for invalid memory).

The full UB check is done as
```python
mem_id = z3.Extract(63, PTR_OFFSET_BITS, ptr)
offset = z3.Extract(PTR_OFFSET_BITS - 1, 0, ptr)
mem_size = z3.Select(mem_sizes, mem_id)
add_ub(z3.UGE(offset, mem_size))
```
where `mem_sizes` is an array mapping memory id to a size:
```python
mem_sizes = z3.K(z3.BitVecSort(PTR_ID_BITS), z3.BitVecVal(0, PTR_OFFSET_BITS))
```
We use the function `z3.K` instead of `z3.Array` when creating the `mem_sizes` array -- `z3.K` makes an array where the unwritten elements have a default value.

## Extra memory blocks for pointers
It is not enough to add memory blocks for variables. For example,
```c
int foo(int *p)
{
  return *p;
}
```
would always be UB according to `pysmtgcc` unless we add one extra memory block, because otherwise there would not be any memory that `p` could point to! Similarly,
```c
int i;

int foo(int *p)
{
  *p = 0;
  return i;
}
```
would always return `0` according to `pysmtgcc` as `i` is the only memory that `p` could point to.

We, therefore, add one "anonymous" memory block (of size `ANON_MEM_SIZE`) for each pointer passed to the function.

This still does not solve all problems. For example,
```c
int64_t *p;

int64_t* foo(void)
{
  *p = 0;
  return p;
}
```
has a similar problem, so we should add one anonymous memory block for each pointer in global memory too.[^extra_memory] But adding memory is expensive -- the SMT solver will conceptually check all possible values for the pointers, so adding more memory makes it work harder.

But the SMT solver checking all values also mean that we do not need multiple blocks for all the anonymous memory -- it is enough to add one block with a size that is big enough that the SMT solver can place the values after each other in memory![^one_block] This does not solve all problems -- it is mainly the total size of the valid memory blocks that is expensive, not the number of blocks. But having only one anonymous memory block makes it easier to trade off between adding enough memory so that all reasonable paths in the code can be checked, but not adding too much memory so that it becomes needlessly slow.

## Local variables going out of scope

Local variables may go out of scope, which makes the memory block invalid. In GIMPLE this looks like
```c
a ={v} {CLOBBER(eol)};
```
and this makes `pysmtgcc` set the size to 0 in the `mem_size` array which makes it UB to read/write the memory.

But GCC does one transformation that treats the return of a pointer to such memory as invalid. Consider the program:
```c
int *ptr;

int *foo(void)
{
  int *p;
  {
    int a;
    p = &a;
  }
  ptr = p;
  return p;
}
```
The variable `a` goes out of scope, making the memory block pointed to by `p` invalid, which in GIMPLE looks like
```c
int * foo ()
{
  int a;

  <bb 2>
  a ={v} {CLOBBER(eol)};
  ptr = &a;
  return &a;
}
```
The `isolate-paths` pass then transform this to the equivalent of
```c
int * foo ()
{
  int a;

  <bb 2>
  a ={v} {CLOBBER(eol)};
  ptr = &a;
  return 0B;
}
```
It is unclear to me exactly what semantics EOL:ed pointer has in GIMPLE -- it seems like GCC only usees this to modify returned values (the store to `ptr` is not affected in the example above). `pysmtgcc` therefore keep track of EOL:ed memory blocks with yet another array
```python
mem_id_eol = z3.K(z3.BitVecSort(PTR_ID_BITS), z3.BoolVal(False))
```
in addition to setting the `mem_size` size to `0` so that all load/store operations know that it is invalid.

A better solution is probably to just treat a return of local pointers as UB, which would not need the `mem_id_eol` array.

## Constant memory
Store to constant memory is undefined behavior, so `pysmtgcc` must track which memory is `const`. We could have done it with an `Array` in the same way as EOL, but `pysmtgcc` is generating comparisons instead of a `Select` from an `Array`:
```python
def const_mem_ub_check(mem_id, smt_bb):
    const_mem_ids = smt_bb.smt_fun.state.const_mem_ids
    if const_mem_ids:
        is_ub = mem_id == const_mem_ids[0]
        for cmem_id in const_mem_ids[1:]:
            is_ub = Or(is_ub, mem_id == cmem_id)
        smt_bb.add_ub(is_ub)
```
This is because of historical reasons, but I have not changed it because it seems reasonable that the code is friendlier to the SMT solver (as it can see exactly which `mem_id` values are forbidden), but I have not verified that it is faster than an `Array`.

# Checking the result

We saw in [part 2](https://kristerw.github.io/2022/11/01/verifying-optimizations/) how to check that the returned value is the same from `src` and `tgt`. We must also check that the values in global memory are the same. More concretely, we should check that each byte in a memory block in global memory has the same value for `tgt` as for `src` (unless the `src` value is uninitialized, which will be discussed in part 7), which in `pysmtgcc` is done as
```python
solver = init_solver(src_smt_fun)
ptr = z3.Const(".ptr", BitVecSort(64))
mem_id = z3.Extract(63, PTR_OFFSET_BITS, ptr)
offset = z3.Extract(PTR_OFFSET_BITS - 1, 0, ptr)
valid_ptr = z3.BoolVal(False)
for mem_obj in src_smt_fun.state.global_memory:
    valid_id = mem_id == mem_obj.mem_id
    valid_offset = z3.ULT(offset, z3.Select(src_smt_fun.state.mem_sizes, mem_id))
    valid_ptr = z3.Or(valid_ptr, z3.And(valid_id, valid_offset))
src_mem = src_smt_fun.memory
tgt_mem = tgt_smt_fun.memory
src_is_init = src_smt_fun.is_initialized
tgt_is_init = tgt_smt_fun.is_initialized
solver.append(valid_ptr)
solver.append(Select(src_is_init, ptr))
solver.append(
    Or(
        z3.Select(src_mem, ptr) != z3.Select(tgt_mem, ptr),
        z3.Not(z3.Select(tgt_is_init, ptr)),
    )
)
res = solver.check()
if res == z3.unsat:
    print("Transformation seems to be correct.")
elif res == z3.sat:
    print(f"Incorrect: {solver.model()}")
else:
    print("Timeout")
```
---

[^allocated_mem]: `alloca`, `malloc`, etc., are not implemented in `pysmtgcc`. But all infrastructure is implemented, so it should be easy to add.

[^extra_memory]: `pysmtgcc` does not do this.

[^one_block]: This is the approach used for `smtgcc`.
