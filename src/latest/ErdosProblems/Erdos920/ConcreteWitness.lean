import ErdosProblems.Erdos920.DStarProjective
import ErdosProblems.Erdos920.RamseyPackaging

/-!
# The concrete projective `D*` witness

This file connects the projective construction to the numerical interface in
`RamseyPackaging`.  All structural fields of a `DStarWitness` are supplied by
the finite projective geometry: the vertex type is finite, its cardinality has
the required lower bound, and its arc relation is `T_(t+1)`-free.  Thus the
only remaining input is the forward-independent-tuple estimate.
-/

namespace Erdos920.ConcreteWitness

open Erdos920.ProjectiveDStar
open Erdos920.RamseyPackaging

noncomputable section

/-- The projective `D*(t,q)` construction, packaged as a `DStarWitness`.

The hypothesis is precisely the forward-independent-tuple estimate required
by the packaging layer; all other witness fields follow from the concrete
projective construction. -/
def ofForwardBound (q t m : ℕ) [Fact q.Prime] (C : ℝ) (ht : 1 ≤ t)
    (hforward :
      ((@Digraph.forwardIndependentTupleCount
          (ProjectiveDStar.Vertex q t)
          (ProjectiveDStar.vertexFintype q t)
          (ProjectiveDStar.digraph q t) m : ℕ) : ℝ) ≤
        (C * (q : ℝ) ^ t) ^ m) :
    DStarWitness t m q C where
  V := ProjectiveDStar.Vertex q t
  fintypeV := ProjectiveDStar.vertexFintype q t
  D := ProjectiveDStar.digraph q t
  transitiveTournamentFree :=
    ProjectiveDStar.digraph_transitiveTournamentFree q t
  vertex_lower := ProjectiveDStar.vertex_lower_real q t ht
  forward_bound := hforward

/-- The type chosen by `ofForwardBound` is definitionally the incident-pair
projective vertex type. -/
@[simp] theorem ofForwardBound_vertexType (q t m : ℕ) [Fact q.Prime]
    (C : ℝ) (ht : 1 ≤ t) (hforward :
      ((@Digraph.forwardIndependentTupleCount
          (ProjectiveDStar.Vertex q t)
          (ProjectiveDStar.vertexFintype q t)
          (ProjectiveDStar.digraph q t) m : ℕ) : ℝ) ≤
        (C * (q : ℝ) ^ t) ^ m) :
    (ofForwardBound q t m C ht hforward).V =
      ProjectiveDStar.Vertex q t := rfl

/-- The packaged digraph is definitionally the projective arc digraph. -/
@[simp] theorem ofForwardBound_digraph (q t m : ℕ) [Fact q.Prime]
    (C : ℝ) (ht : 1 ≤ t) (hforward :
      ((@Digraph.forwardIndependentTupleCount
          (ProjectiveDStar.Vertex q t)
          (ProjectiveDStar.vertexFintype q t)
          (ProjectiveDStar.digraph q t) m : ℕ) : ℝ) ≤
        (C * (q : ℝ) ^ t) ^ m) :
    (ofForwardBound q t m C ht hforward).D =
      ProjectiveDStar.digraph q t := rfl

end

end Erdos920.ConcreteWitness
