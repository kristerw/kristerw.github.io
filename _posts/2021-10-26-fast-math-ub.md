---
layout: post
title: Strange behavior with NaN and -ffast-math
---
My [previous blog post](https://kristerw.github.io/2021/10/19/fast-math/) said that computations producing `Inf`, `NaN`, or `-0.0` in programs compiled with `-ffinite-math-only` and `-fno-signed-zeros` might cause the program to behave in strange ways, such as not evaluating either the true or false part of an `if`-statement.

I have received several questions about this, so let's look at an example of how this can happen.

# Example -- vectorization

There are cases where the compiler can generate better code by splitting an `if-then-else`
```c
if (x > y) {
  do_something();
} else {
  do_something_else();
}
```
into
```c
if (x > y) {
  do_something();
}
if (x <= y) {
  do_something_else();
}
```
This optimization is only allowed when `x` and `y` cannot be `NaN` because both comparisons evaluate to false if `x` or `y` is `NaN`.

`-ffinite-math-only` tells the compiler that no `NaN` values will ever be seen when running the program, enabling this transformation. But this means that neither `do_something` nor `do_something_else` is evaluated if `x` or `y` happens to be `NaN` when the program runs.

This splitting of `if-then-else` helps vectorization where it makes it easier to work with element masks. This can be seen with the function below when compiled with clang 13.0.0 ([godbolt](https://godbolt.org/z/cj51aaddn))
```c
float a[1024];
float b[1024];

void foo(void) {
  for (int i = 0; i < 1024; ++i) {
    if (b[i] > 42.0f) {
      a[i] = b[i] + 1.0f;
    } else {
      b[i] = a[i] + 1.0f;
    }
  }
}
```
The generated code uses masked moves to store the values
```nasm
  vmovups     ymm2, ymmword ptr [rax + b+4096]
  vcmpleps    ymm3, ymm2, ymm0
  vaddps      ymm4, ymm1, ymmword ptr [rax + a+4096]
  vmaskmovps  ymmword ptr [rax + b+4096], ymm3, ymm4
  vcmpltps    ymm3, ymm0, ymm2
  vaddps      ymm2, ymm2, ymm1
  vmaskmovps  ymmword ptr [rax + a+4096], ymm3, ymm2
```
The mask calculated by `vcmpleps` or `vcmpltps` is false when the corresponding element in `ymm2` (which contains `b[i]`) is `NaN`, so no value is stored when `b[i]` is `NaN`.

# How to avoid such problems
This kind of strange behavior is uncommon -- the usual failure mode is just that the program produces an incorrect value when `NaN`, `Inf`, or  `-0.0` is seen. But producing an incorrect value is not a desirable behavior either...

It is possible to detect the use of `NaN` and `Inf` by enabling trapping[^1] using
```c
feenableexcept(FE_OVERFLOW | FE_INVALID | FE_DIVBYZERO);
```
as described in the [previous blog post](https://kristerw.github.io/2021/10/19/fast-math/). But the best way to avoid problems is not to use `-ffast-math` at all -- I usually enable `-ffast-math` just to see if it improves the performance. If it does, I manually apply the profitable optimizations in the source code (if they are safe for my use case) to get the same performance without the flag.

----

[^1]: This does not detect `-0.0`. But `-0.0` is very unlikely to cause any problems.
