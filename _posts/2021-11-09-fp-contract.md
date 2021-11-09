---
layout: post
title: -ffp-contract=fast
---
GCC per default enables one optimization for x86_64 that can change the result of floating-point operations: `-ffp-contract=fast`.[^1] This allows the compiler to do floating-point expression contraction such as
combining multiplication and addition instructions with an FMA instruction.[^2]


Various optimizations and heuristics may affect which calculations are contracted:
* Optimizations such as inlining and loop unrolling may introduce new
  opportunities for contraction.
* It is not always a good idea to use an FMA instruction for a calculation `x*y+z`. For example, suppose `x` and `y` are available early in the function and `z` late. In that case, the compiler may reduce register pressure by doing the multiplication early (so it only needs to keep one register live until `z` is available).[^3]

This means that different optimization levels can make the code produce different results. And unrelated code changes may also change the result (if the compiler, for example, makes different inlining decisions because of the code change). This does not impact most programs, but it sometimes causes confusion when working with test suites that expect the result to be bit-exact.

Disabling floating-point contraction with `-ffp-contract=off` makes GCC generate code that produces a consistent result for x86_64.

----

[^1]: `-ffp-contract=fast` is enabled for C++ and GNU C. It is not enabled for standard C (that is, when compiling with `-std=c99`, etc.).

[^2]: The FMA instruction omits the rounding done in the multiplication instruction, making the calculations produce different results for some input values.

[^3]: Current GCC does, to my knowledge, not take advantage of this. But some other compilers use heuristics that take the instruction usage into account ([godbolt](https://godbolt.org/z/qE4dT3ov8)).
