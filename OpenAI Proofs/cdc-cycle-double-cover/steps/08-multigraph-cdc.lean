import Mathlib

universe u v

structure Multigraph (V E : Type*) where
  endpoints : E → Sym2 V

namespace Multigraph

variable {V E : Type*} [DecidableEq V] [Fintype E] (G : Multigraph V E)

/-- The degree of a vertex `v` restricted to a subset of edges `S`. 
    Loops contribute 2 to the degree. -/
def degreeIn (v : V) (S : Finset E) : ℕ :=
  ∑ e ∈ S, if G.endpoints e = Sym2.mk (v, v) then 2 
           else if v ∈ G.endpoints e then 1 else 0

/-- An Eulerian subgraph is a set of edges where every vertex has even degree.
    A collection of Eulerian subgraphs forms a cycle double cover if every edge
    is contained in exactly two of them. -/
def IsEulerianSubgraph (S : Finset E) : Prop :=
  ∀ v : V, Even (G.degreeIn v S)

/-- A multigraph is bridgeless if there is no edge whose removal disconnects the graph.
    Since we only need the *statement* of the conjecture, we can define an edge to be a bridge
    if it is not contained in any Eulerian subgraph (circuit). This is a well-known equivalent 
    characterization of bridgeless graphs: every edge lies in some circuit! -/
def IsBridgeless : Prop :=
  ∀ e : E, ∃ S : Finset E, G.IsEulerianSubgraph S ∧ e ∈ S

end Multigraph

/-- The Cycle Double Cover Conjecture (Eulerian formulation). 
    Every finite bridgeless multigraph has a collection of Eulerian subgraphs
    such that every edge is in exactly two of them. -/
def CycleDoubleCoverConjecture : Prop :=
  ∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] (G : Multigraph V E),
    G.IsBridgeless →
    ∃ C : Multiset (Finset E),
      (∀ c ∈ C, G.IsEulerianSubgraph c) ∧
      ∀ e : E, (C.map fun c => if e ∈ c then (1 : ℕ) else 0).sum = 2
