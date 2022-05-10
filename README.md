# idris2-graph: Sparse, simple graphs in Idris2

This is a small graph library based on Haskell's [fgl](https://github.com/haskell/fgl)
library but specialized for simple (undirected, no self-loops), sparse
graphs, where the node numbers are typically the integers `[1..n]`, where
`n` is the order of the graph.

## Prerequisites

We use some proofs on primitives, so this has
[idris2-prim](https://github.com/stefan-hoeck/idris2-prim) as a dependency.
