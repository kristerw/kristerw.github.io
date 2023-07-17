---
layout: post
title: "Part 2: Verifying GCC optimizations using an SMT solver"
---
_This post describes the implementation of [pysmtgcc](https://github.com/kristerw/pysmtgcc). See "[GCC Translation Validation](https://kristerw.github.io/2022/09/13/translation-validation/)" for background information._

# Using an SMT solver
SMT solvers are used to find solutions to a system of equations. As a first example, let's consider

$$
3x + xy = 12\\\\
x^2 + y^2 = 13
$$

where $$x,y\in\mathbb{Z}$$. There is a convenient Python API for Z3 and CVC5[^CVC5] that we can use this to solve this equation.

### Creating the variables
We start by creating the variables $$x$$ and $$y$$.
```python
x = z3.Const("x", z3.IntSort())
y = z3.Const("y", z3.IntSort())
```
`IntSort()` sets the type to be a bignum integer. We could have used some other type, such as BitVecSort(32) representing 32-bit integers.

### Creating the equations to solve
Next, we create a solver representing the problem to solve and populate it with our formulas
```python
solver = z3.Solver()
solver.append(z3.IntVal(3) * x + x * y == z3.IntVal(12))
solver.append(x * x + y * y == z3.IntVal(13))
```
The Python API can convert Python values to SMT values without an explicit cast, so we can write, e.g., `z3.IntVal(3)` as `3`, which makes this easier to read
```python
solver = z3.Solver()
solver.append(3 * x + x * y == 12)
solver.append(x * x + y * y == 13)
```

### Running the solver
Finally, we add a call to `solver.check()` to solve the equation. The solver will, in principle, test all possible values, but it has clever ways of eliminating cases that cannot be a solution, and it is surprisingly fast for most cases that happen in reality.

The SMT solver returns one of
  * `sat` -- the system of equations has a solution. The solution can then be obtained by calling `solver.model()`.
  * `unsat` -- no solution exists[^proof].
  * `unknown` -- the operation timed out, or the solver ran out of memory.

```python
res = solver.check()
if res == z3.sat:
    print(f"{solver.model()}")
elif res == z3.unsat:
    print("Has no solution")
else:
    print("Timeout")
```
### Summary
Putting all of this together gives us the Python script
```python
import z3

x = z3.Const("x", z3.IntSort())
y = z3.Const("y", z3.IntSort())

solver = z3.Solver()
solver.append(3 * x + x * y == 12)
solver.append(x * x + y * y == 13)

res = solver.check()
if res == z3.sat:
    print(f"{solver.model()}")
elif res == z3.unsat:
    print("Has no solution")
else:
    print("Timeout")
```

# Verifying compiler optimizations
We can use an SMT solver to verify compiler optimizations. The idea is that an optimization is valid if the original and optimized functions return the same value for all valid input[^memory], so we let the SMT solver try to find a solution to

$$f(x) \neq f_{optimized}(x)$$

The optimization is valid if it does not exist any solution.

**Example**: To check the optimization where
```c
unsigned src(unsigned a, unsigned b)
{
  return (a & ~b) - (a & b);
}
```
is optimized to
```c
unsigned tgt(unsigned a, unsigned b)
{
  return (a ^ b) - b;
}
```
we encode it as
```python
import z3

a = z3.Const("a", z3.BitVecSort(32))
b = z3.Const("b", z3.BitVecSort(32))

src_retval = (a & ~b) - (a & b)
tgt_retval = (a ^ b) - b

solver = z3.Solver()
solver.append(src_retval != tgt_retval)

res = solver.check()
if res == z3.unsat:
    print("Transformation seems to be correct.")
elif res == z3.sat:
    print(f"Incorrect: {solver.model()}")
else:
    print("Timeout")
```

## Undefined behavior
One complication is that some operations have restrictions on what values they accept. For example, the result of `1/x` is not defined for `x=0`. We must therefore exclude any input that invokes this undefined behavior for any instruction. We must also check that the optimized function does not introduce any new undefined behavior for values where the original function had a defined result.

This is done by adding two SMT formulas `src_invokes_ub` and `tgt_invokes_ub` that keep track of the cases where the two functions invoke UB, and we change the solver setup to
```
solver = z3.Solver()
solver.append(z3.Not(src_invokes_ub))
solver.append(Or(src_retval != tgt_retval, tgt_invokes_ub))
```

**Example**: To check the optimization where
```c
int src(int x)
{
  return 1 / x;
}
```
is optimized to
```c
int tgt(int x)
{
  return ((unsigned)x + 1) <= 2 ? x : 0;
}
```
we encode it as
```python
import z3

x = z3.Const("x", z3.BitVecSort(32))

src_retval = 1 / x
src_invokes_ub = x == 0
tgt_retval = z3.If(z3.ULE((x + 1), 2), x, 0)
tgt_invokes_ub = False

solver = z3.Solver()
solver.append(z3.Not(src_invokes_ub))
solver.append(z3.Or(src_retval != tgt_retval, tgt_invokes_ub))

res = solver.check()
if res == z3.unsat:
    print("Transformation seems to be correct.")
elif res == z3.sat:
    print(f"Incorrect: {solver.model()}")
else:
    print("Timeout")
```

**Note**: One must be careful with `src_invokes_ub` as it makes the SMT solver ignore all values where it is `True` -- e.g., a bug always setting it to `True` will say that all optimizations are correct, regardless of what they do!

`pysmtgcc` does that checking in two steps -- first, it checks that the functions return the same value
```python
solver = z3.Solver()
solver.append(z3.Not(src_invokes_ub))
solver.append(src_retval != tgt_retval, tgt_invokes_ub)
res = solver.check()
...
```
and then it checks that the optimized function does not have additional UB
```python
solver = z3.Solver()
solver.append(z3.Not(src_invokes_ub))
solver.append(tgt_invokes_ub)
res = solver.check()
...
```
The reason is that it made it easier for me to debug issues -- if the return value differs, then I can just take the model values and generate a test case. If it is UB that does not modify the return value, then it needs a closer look to determine which instruction that invokes undefined behavior.


# Translating GIMPLE functions

Generating an SMT formula for a GIMPLE function is done by iterating over the IR and building the SMT expressions as we go. We keep track of the translated expressions using a Python dictionary, which we use when looking up instruction operands
```python
def get_tree_as_smt(expr, smt_fun):
    if isinstance(expr, gcc.ParmDecl):
        return smt_fun.tree_to_smt[expr]
    if isinstance(expr, gcc.SsaName):
        return smt_fun.tree_to_smt[expr]
    if isinstance(expr, gcc.IntegerCst):
        if isinstance(expr.type, gcc.BooleanType):
            return BoolVal(expr.constant != 0)
        assert isinstance(expr.type, gcc.IntegerType)
        return BitVecVal(expr.constant, expr.type.precision)
    ...
```
The translation of a GIMPLE function is done as
```python
for bb in fun.cfg.inverted_post_order:
    for stmt in bb.gimple:
        if isinstance(stmt, gcc.GimpleAssign) and len(stmt.rhs) == 2:
            # Binary operation
            rhs0 = get_tree_as_smt(stmt.rhs[0], smt_fun)
            rhs1 = get_tree_as_smt(stmt.rhs[1], smt_fun)
            if stmt.exprcode == gcc.BitIorExpr:
                smt_fun.tree_to_smt[stmt.lhs] = rhs0 | rhs1
            elif stmt.exprcode == gcc.BitAndExpr:
                smt_fun.tree_to_smt[stmt.lhs] = rhs0 & rhs1
            elif stmt.exprcode == gcc.BitXorExpr:
                smt_fun.tree_to_smt[stmt.lhs] = rhs0 ^ rhs1
            elif ...
                ...
        elif ...
            ...
```
where `fun` is the GIMPLE function we receive from GCC, and `smt_fun` is the class representing this function in `pysmtgcc`.

Doing the translation in one pass works reasonably well for experiments like `pysmtgcc`, but it has problems. For example, it would be hard to handle loops with this method[^loops]. So a real implementation would need to transform the IR into a representation it can analyze and modify before generating the SMT formula.

## GIMPLE undefined behavior

GIMPLE undefined behavior is similar to how it is done in the C language. For example, arithmetic instructions such as `PLUS_EXPR` invokes undefined behavior if a signed addition wraps, and the program is then invalid[^llvm_ub]. So the implementation just builds `invokes_ub` as describes in "Verifying compiler optimizations" above. For example, integer addition is implemented as
```python
if stmt.exprcode == gcc.PlusExpr:
    res = rhs0 + rhs1
    if not stmt.lhs.type.overflow_wraps:
        erhs0 = SignExt(1, rhs0)
        erhs1 = SignExt(1, rhs1)
        eres = erhs0 + erhs1
        smt_fun.invokes_ub = Or(SignExt(1, res) != eres, smt_fun.invokes_ub)
    smt_fun.tree_to_smt[stmt.lhs] = res
```
It is, unfortunately, a bit unclear exactly what is UB in GIMPLE[^PR106811]. Some are documented in [`tree.def`](https://gcc.gnu.org/git/?p=gcc.git;a=blob;f=gcc/tree.def), but not all. And the text in `tree.def` is a bit unclear. For example, for the number of bits to shift by in shift instructions, it says

> Note that the result is undefined if the second operand is larger than or equal to the first operand's type size.

Does this mean that this invokes undefined behavior? Or that it is defined, but it can return an arbitrary value? Anyway, GCC optimizes code involving shift instructions in ways that are invalid for both interpretations[^PR106884].

# Annoyances
This section discusses some issues that annoyed me during the implementation.

## Floating point
The IEEE-754 floating-point representation for NaN is not unique -- for example, the significand may contain a payload thath can be used to pass additional information[^NaN]. The SMT solver does, however, canonicalize NaN to one value, which makes the result differ after some optimizations.

This is not a big problem -- different CPU architectures handle payload differently, so the GCC middle-end can only make a few assumptions. But it fails tests where a function
```c
int foo(int i)
{
  union {
    int i;
    float f;
  } u;
  u.i = i;
  u.f = u.f;
  return u.i;
}
```
is optimized to
```c
int foo(int i)
{
  return i;
}
```
as this gives different results for the SMT solver when, e.g., `i = -2`.

We could fix this particular case by always representing a floating-point number as a bit vector, and only making it a floating-point sort when needed. But that would give us a similar problem when optimizing
```c
int foo(int i)
{
  union {
    int i;
    float f;
  } u;
  float t = -0.0;
  u.i = i;
  u.f = u.f + t;
  return u.i;
}
```
as it converts the bit vector to a floating-point sort when doing the addition, but not when the addition with `-0.0` has been eliminated.

I cannot see any way to solve all the problems without writing my own SMT floating point implementation[^float]...

## Interprocedural optimizations
GCC does interprocedural optimizations that move code between functions etc., and this cannot be handled by `pysmtgcc` as it works on one function at a time. We mitigate this by skipping the interprocedural ("IPA") passes in `plugin1.py`, but that does not solve all problems...

The IPA passes do global analysis, which can then be queried by the normal GIMPLE passes that work one function at a time. There are two cases where use of such information incorrectly is reported as miscompilations:

* Initialized static variables that are never written work in the same ways as constants, so their uses can be substituted by the constants (that can then be constant folded etc.).

* Static functions that are always called with constants for some arguments can be optimized with knowledge of those values. For example, if a function
  ```c
  int foo(int a) {
    if (a > 10)
      return 42;
    return 23;
  }
  ```
only is called as `foo(1)` and `foo(9)`, then it can be optimized to the equivalent of
  ```c
  int foo(int a) {
    return 23;
  }
  ```

We can solve this by letting `pysmtgcc` query the IPA information, and generate SMT using that information:
* Treat global `static` variables in the same way as `const` if the IPA information says it is not written to.
* Adding extra constraints to function `gcc.ParmDecl`, restricting the values to the ones used in the calls.

But the `gcc-python-plugin` does not have APIs for querying the IPA information, so I currently ignore those issues (by passing `-Dstatic=""` to the compiler).

## Parallel Z3
It is possible to get Z3 to distribute its work over multiple threads by setting
the `parallel.enable` parameter to `True`:
```python
z3.set_param("parallel.enable", True)
```
I guess it makes Z3 faster, but timeouts stop working, so the resulting plugin is slower when some checks take "forever" to analyze instead of giving up after `SOLVER_TIMEOUT` seconds.

## Performance

It is common that optimization passes do not find anything to optimize, so the two functions we compare are often identical. Z3 seems to detect this and is generally fast when checking such, but I noticed that some functions timed out on each UB query (thus taking several hours to check the translation unit).

I initially did the checking as
```python
solver.append(z3.Not(src_invokes_ub))
solver.append(tgt_invokes_ub)
```
Changing this to
```python
solver.append(z3.Not(src_invokes_ub))
solver.append(tgt_invokes_ub != src_invokes_ub)
```
made it quick for the cases that used to time out. But other UB checks got slower for cases where `src_invokes_ub` and `tgt_invokes_ub` were not identical. So I am now using
```python
solver.append(z3.Not(src_invokes_ub))
solver.append(tgt_invokes_ub != src_invokes_ub)
solver.append(tgt_invokes_ub)
```
which seems to be the best of both worlds.

---

[^CVC5]: There are some minor API differences between Z3 and CVC5. For example, CVC5 is missing the `fpToIEEEBV` and `to_smt2` functions. I am currently only using Z3 as I have not figured out how to enable timeouts for CVC5 using the Python API. But I am using the [CVC5 API documentation](https://cvc5.github.io/docs/cvc5-1.0.2/api/python/pythonic/pythonic.html), which is much nicer than the Z3 documentation.

[^proof]: SMT solvers can, in general, generate a proof that it does not exist any solution. This is useful if we want to verify that the absence of a solution is not due to a bug in the SMT solver (solutions do not need a proof -- we can just substitute the values and verify that it is correct). We are not using that functionality in `pysmtgcc`.

[^memory]: Memory access complicates this. See [part 3](https://kristerw.github.io/2023/07/17/memory-representation/) of this blog series.

[^loops]: Control flow is discussed in part 8 of this blog series.

[^PR106811]: [PR 106811](https://gcc.gnu.org/bugzilla/show_bug.cgi?id=106811)

[^llvm_ub]: This is much simpler than how LLVM handles UB. For LLVM, the instruction is valid, but it returns a `poison` or `undef` value, and the program is invalid if the `poison`/`undef` is used in certain ways. This enables some optimizations that are not valid in GIMPLE (but GCC can do those optimizations in the back end where things like signed wrapping are not UB), but it makes the implementation more complex -- many of the bugs found by Alive2 are related to how optimization passes propagate `poison` and `undef` values.

[^PR106884]: [PR 106884](https://gcc.gnu.org/bugzilla/show_bug.cgi?id=106884)

[^NaN]: See e.g., Agner Fog's ["Floating point exception tracking and NAN propagation"](https://www.agner.org/optimize/nan_propagation.pdf)

[^float]: On the other hand, different CPU architectures handle this differently, so it is not obvious what the correct middle-end semantics is, even if we write our own SMT floating point implementation.
