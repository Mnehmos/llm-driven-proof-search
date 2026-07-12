import Mathlib

structure Multigraph (V E : Type) where
  endpoints : E → Sym2 V

-- A set of edges is a 2-factor (or union of disjoint cycles) if every vertex has degree exactly 0 or 2.
-- For the Cycle Double Cover, we can just say "a collection of subgraphs, each of which is a cycle".
-- Wait, the paper might construct a 2-factor which decomposes into cycles.
