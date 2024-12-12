# Juvix Lean formalization library

The Juvix Lean library provides primitives for verifying the correctness of Juvix compiler runs, i.e., proving that the semantics of a particular Juvix program is preserved by the compilation process.

The major components of the library include:
- formalization of Juvix compiler internal representations and their semantics,
- proof-producing metaprograms for verifying that individual Juvix compiler transformations preserve the semantics.
