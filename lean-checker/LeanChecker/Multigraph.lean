import Mathlib

universe u v

/-- A multigraph where edges can be parallel or loops. -/
structure Multigraph (V E : Type*) where
  endpoints : E → Sym2 V

namespace Multigraph

/-- The degree of a vertex `v` restricted to a subset of edges `S`. 
    Loops contribute 2 to the degree. -/
def degreeIn {V E : Type*} [DecidableEq V] [Fintype E] (G : Multigraph V E) (v : V) (S : Finset E) : ℕ :=
  ∑ e ∈ S, if G.endpoints e = s(v, v) then 2 
           else if v ∈ G.endpoints e then 1 else 0

/-- An Eulerian subgraph is a set of edges where every vertex has even degree. -/
def IsEulerianSubgraph {V E : Type*} [DecidableEq V] [Fintype E] (G : Multigraph V E) (S : Finset E) : Prop :=
  ∀ v : V, Even (G.degreeIn v S)

/-- A multigraph is bridgeless if there is no edge whose removal disconnects the graph.
    Equivalent characterization: every edge lies in some circuit (Eulerian subgraph). -/
def IsBridgeless {V E : Type*} [DecidableEq V] [Fintype E] (G : Multigraph V E) : Prop :=
  ∀ e : E, ∃ S : Finset E, G.IsEulerianSubgraph S ∧ e ∈ S

/-- A (multigraph) cycle is a nonempty inclusion-minimal Eulerian subgraph. -/
structure Cycle {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype E] (G : Multigraph V E) where
  edges : Finset E
  nonempty : edges.Nonempty
  even : G.IsEulerianSubgraph edges
  minimal : ∀ D : Finset E, D.Nonempty → D ⊆ edges → G.IsEulerianSubgraph D → D = edges

/-- A cycle double cover is a multiset of cycles such that every edge is in exactly two cycles. -/
structure CycleDoubleCover {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype E] (G : Multigraph V E) where
  cycles : List G.Cycle
  coveredTwice : ∀ e : E, (cycles.filter fun C ↦ decide (e ∈ C.edges)).length = 2

end Multigraph
