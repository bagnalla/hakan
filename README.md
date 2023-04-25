# hakan

A statically typed functional programming language with parametric
polymorphism and type inference.

See monad.hk for an example program that uses typeclasses, and base.hk
and prelude.hk for more example code. The other .hk files are probably
out of date.

## Instructions

To build hakan and run it on a test program:

`stack build && stack exec hakan-exe hk/monad.hk`

## Compilation to JS

`./compileJS.sh hk/monad.hk`

## Compilation to C

Compilation strategy based on lambda-lifting all functions to
top-level "supercombinators", each of which is compiled to a single C
function. Currently doesn't support the use of typeclasses. Hooks up
the resulting executable to to Boehm GC.

`./compileC.sh hk/ctest9.hk`
