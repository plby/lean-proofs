import ErdosProblems.Erdos593.Graph.NonInducedFactor
import ErdosProblems.Erdos593.TripleSystem.SequenceLiftBaseLetterSubgraph
import ErdosProblems.Erdos593.TripleSystem.SequenceLiftBaseFiberEquiv

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Local graph factors for canonical base fibres

For a chosen sequence-lift base fibre, its canonical base letters select a
subgraph of the host. This file packages the finite-carrier and non-induced
factor portions of that construction, together with the edge equivalence
available under a linearity assumption. It deliberately does not assert the
private-vertex-expansion isomorphism of the corresponding triple-system fibre.
-/

namespace Erdos593

universe u

namespace SequenceLift

variable {V : Type u} {G : _root_.SimpleGraph V}

/-- A finite selected sequence-lift edge set gives finite vertex support to
the host subgraph selected by the base letters of one chosen base fibre. -/
theorem baseFiberLetterSubgraph_finite
    {S : Set (Edge G)} (hS : S.Finite) (q : Node G) :
    Finite (baseLetterSubgraph G (baseLetter '' baseFiber S q)).verts :=
  Set.finite_coe_iff.mpr <|
    baseLetterSubgraph_finite_verts G <|
      (hS.subset (baseFiber_subset S q)).image baseLetter

/-- The host subgraph selected by one base fibre's base letters maps into the
host graph through its canonical non-induced copy. -/
noncomputable def baseFiberLetterSubgraphFactor
    (S : Set (Edge G)) (q : Node G) :
    Erdos593.SimpleGraph.NonInducedFactor
      (baseLetterSubgraph G (baseLetter '' baseFiber S q)).coe G :=
  Erdos593.SimpleGraph.NonInducedFactor.ofCopy
    (baseLetterSubgraph G (baseLetter '' baseFiber S q)).coeCopy

/-- Under linearity, the selected graph edges are canonically equivalent to
the chosen base fibre. -/
noncomputable def baseFiberLetterSubgraphEdgeEquiv_of_linear
    {S : Set (Edge G)} (q : Node G)
    (hlinear : ((system G).edgeRestriction S).Linear) :
    (baseLetterSubgraph G (baseLetter '' baseFiber S q)).coe.edgeSet ≃
      baseFiber S q :=
  (baseLetterSubgraphEdgeEquiv G (baseLetter '' baseFiber S q)).trans
    (baseFiberEquivBaseLetterImage_of_linear q hlinear).symm

/-- The finite-factor prefix needed for a finite base fibre: a finite vertex
type, a selected host subgraph on that type, and a non-induced factor into the
host. No triple-system expansion isomorphism is asserted here. -/
theorem exists_fintype_baseFiberLetterSubgraphFactor
    {S : Set (Edge G)} (hS : S.Finite) (q : Node G) :
    Exists (fun X : Type u =>
      Exists (fun _ : Fintype X =>
        Exists (fun J : _root_.SimpleGraph X =>
          Nonempty (Erdos593.SimpleGraph.NonInducedFactor J G)))) := by
  classical
  let K := baseLetterSubgraph G (baseLetter '' baseFiber S q)
  let : Finite K.verts := by
    dsimp [K]
    exact baseFiberLetterSubgraph_finite hS q
  let : Fintype K.verts := Fintype.ofFinite K.verts
  refine Exists.intro (K.verts : Type u) ?_
  apply Exists.intro (inferInstance : Fintype K.verts)
  apply Exists.intro K.coe
  exact Nonempty.intro (baseFiberLetterSubgraphFactor S q)

end SequenceLift

end Erdos593
