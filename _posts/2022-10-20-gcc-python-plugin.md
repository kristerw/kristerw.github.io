---
layout: post
title: "Part 1: Writing a GCC plugin in Python"
---
_This post describes the implementation of [pysmtgcc](https://github.com/kristerw/pysmtgcc). See "[GCC Translation Validation](https://kristerw.github.io/2022/09/13/translation-validation/)" for background information._

I chose to use Python for the plugin for a few reasons:
* The main aim of this experiment was to get some experience translating GIMPLE to SMT, but I had not decided exactly what I wanted to do with it. Some of my ideas involved parsing output from disassembler, etc., which is much easier done in Python than in C++.
* The Z3 Python API is convenient to use.
* The [`gcc-python-plugin`](https://github.com/davidmalcolm/gcc-python-plugin) looked nifty, and I had planned for a long time to try it out.

This project later grew a bit more than I had planned[^project], so Python may not have been the right choice...

# GIMPLE IR
The GCC middle-end IR is called "GIMPLE", and you can see the IR by passing `-fdump-*` flags to the compiler. For example, `-fdump-tree-all` writes the IR to a file after each non-IPA GIMPLE pass. The IR is usually pretty-printed using a C-like syntax, but you can see the raw representation by adding "`-raw`" (i.e.,`-fdump-tree-all-raw`).

## GIMPLE statements
The GIMPLE operations are documented in [`gimple.def`](https://gcc.gnu.org/git/?p=gcc.git;a=blob;f=gcc/gimple.def), and the `tree` objects containing information in the GIMPLE statements (types, operands, etc.) are documented in [`tree.def`](https://gcc.gnu.org/git/?p=gcc.git;a=blob;f=gcc/tree.def).

There are many GIMPLE operations, but most encode optional information (branch prediction information, OpenMP attributes, etc.), so I only needed to handle
* `GIMPLE_ASSIGN` -- assignment
* `GIMPLE_CALL` -- function call
* `GIMPLE_COND` -- conditional jump
* `GIMPLE_LABEL` -- label (for `switch` statements)
* `GIMPLE_PHI` -- phi node
* `GIMPLE_RETURN` -- function return value
* `GIMPLE_SWITCH` -- multiway branch

## GIMPLE_ASSIGN
`GIMPLE_ASSIGN` is the GIMPLE instruction doing all the work that is not related to control flow[^controlflow]. It represents an assignment, such as
```c
a = b + c;
```
which in the raw form is written as
```
gimple_assign <plus_expr, a_5, b_2, c_4, NULL>
```
Load/store instructions are represented by a unary `GIMPLE_ASSIGN` where the input/output reference a variable or memory location. All other `GIMPLE_ASSIGN` statements must have SSA names or constants for the input/output.


# Using gcc-python-plugin
## Registering a pass
Creating and registering a pass is done as
```python
class MyPass(gcc.GimplePass):
    def execute(self, fun):
        # Do something with fun.
        ...

ps = MyPass(name="mypass")
ps.register_after("cfg")
```
This creates a GIMPLE pass where the `execute` function is called once for each function in the translation unit.

It is also possible to register callback functions that are called for various events -- `pysmtgcc` does this in `plugin1.py` as it must do work for each pass the compiler runs. See the [`gcc-python-plugin` manual](https://gcc-python-plugin.readthedocs.io/en/latest/callbacks.html) for details.


## Iterating over the IR

The next step is iterating over the GIMPLE instructions in the IR. This is usually done as
```python
for bb in fun.cfg.basic_blocks:
    for stmt in bb.gimple:
        # Do something with stmt.
        ...
```
I needed to iterate over the basic blocks in reverse post order, so I added support for this in my fork of `gcc-python-plugin`
```python
for bb in fun.cfg.reverse_post_order:
   ...
```

## GIMPLE statements

Each kind of GIMPLE statement is wrapped in a Python class. For example, `GIMPLE_ASSIGN` is represented as [`gcc.GimpleAssign`](https://gcc-python-plugin.readthedocs.io/en/latest/gimple.html#gcc.GimpleAssign) where the operation and arguments are available as member variables.

Much of the work done in many passes consists of matching and inspecting instructions, which for `pysmtgcc` looks like
```python
if isinstance(stmt, gcc.GimpleAssign):
    if stmt.exprcode == gcc.PlusExpr:
        if isinstance(stmt.lhs.type, gcc.IntegerType):
            # Handle integer addition.
            ...
        elif isinstance(stmt.lhs.type, gcc.RealType):
            # Handle floating point addition.
            ...
        else:
            ...
    elif stmt.exprcode == gcc.MultExpr:
        ...
    ...
elif isinstance(stmt, gcc.GimpleReturn):
    ...
```

# Example -- a spellchecker pass

The Python API makes it easy to prototype passes that iterate over the program to detect various problems. For example, the following pass[^example] implements a `-Wall` warning that complains about misspelled strings:
```python
import gcc
import enchant

spellingdict = enchant.Dict("en_US")

def spellcheck_node(node, loc):
    if isinstance(node, gcc.StringCst):
        words = node.constant.split()
        for word in words:
            if not spellingdict.check(word):
                gcc.warning(
                    loc,
                    f"Possibly misspelt word in string constant: {word}",
                    gcc.Option("-Wall"),
                )

class SpellcheckingPass(gcc.GimplePass):
    def execute(self, fun):
        for bb in fun.cfg.basic_blocks:
            for stmt in bb.gimple:
                stmt.walk_tree(spellcheck_node, stmt.loc)

ps = SpellcheckingPass(name="spellchecker")
ps.register_after("cfg")
```

**Note**: `execute` is called for each function, so the `spellchecker` pass does only check strings found in functions -- using the Python plugin to check global variables is much more annoying:

* We could iterate over the global variables as
  ```python
  for var in gcc.get_variables():
      # Do something with var.
  ```
  when handling the first function, but it does not work for translation units not having functions.
* There is no convenient `walk_tree` function for variables, so we need to handle all cases ourselves. For example,
  ```c
  char s1[] = "Hello worrld";
  char *s2 = "Helllo world";
  ```
  are different (`s2` has an extra `gcc.AddrExpr`) so we must do something like
  ```python
  for var in gcc.get_variables():
      if var.decl.initial:
          node = var.decl.initial
          if isinstance(node, gcc.AddrExpr):
              node = node.operand
          spellcheck_node(node, var.decl.location)
  ```
  Handling strings in structure/array initializers must (recursively) iterate over the elements.


# Problems
Using `gcc-python-plugin` worked reasonably well, but there are problems:
* Many instructions from `tree.def` are not fully implemented, so I had to extend `gcc-python-plugin` (or, in some cases, return "not implemented").
* The plugin crashes when trying to compile some files[^crash].

So my conclusion is that `gcc-python-plugin` is good for doing quick experiments, but probably not the right choice for developing a product quality tool.

---

[^project]: The plan was only to implement a few instructions, only handle 32-bit integers, etc. But the primitive tool found a GCC bug, so it seemed like it could actually be useful if some more functionality was added.

[^controlflow]: Control flow is discussed in part four of this blog series.

[^example]: Adapted from a [`gcc-python-plugin`](https://github.com/davidmalcolm/gcc-python-plugin)  example pass.

[^crash]: Some of the crashes may be due to my modifications of `gcc-python-plugin`, but not all of them.
