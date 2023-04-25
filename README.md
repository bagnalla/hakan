# hakan

A statically typed functional programming language with parametric
polymorphism and type inference.

See monad.hk for an example program that uses typeclasses, and base.hk
and prelude.hk for more example code. The other .hk files are probably
out of date.

## Instructions

To build hakan and run the interpreter on a test program:

`stack build && stack exec hakan-exe hk/monad.hk`

## Compilation to JavaScript

[src/JS.hs](src/JS.hs) implements straightforward compilation to JavaScript. Try it out with:

`./compileJS.sh hk/monad.hk`

## Compilation to C

[src/C.hs](src/C.hs) implements compilation to C. It is less straightforward than the JS backend because of C's lack of innate support for higher-order functions / closures, and lack of garbage collection. Compilation proceeds by lambda-lifting all functions to top-level "supercombinators" which are then compiled to individual C functions. Currently doesn't support the use of typeclasses. The resulting executable is hooked up to Boehm GC.

`./compileC.sh hk/ctest9.hk`
