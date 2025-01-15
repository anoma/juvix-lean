# Juvix library for Lean 4

The Juvix Lean library provides primitives for verifying the correctness of Juvix compiler runs, i.e., proving that the semantics of a particular Juvix program is preserved by the compilation process.

The library includes:
- formalization of Juvix compiler internal representations (IRs) and their semantics,
- proof-producing metaprograms for verifying that Juvix compiler transformations preserve the semantics of concrete IR programs.
