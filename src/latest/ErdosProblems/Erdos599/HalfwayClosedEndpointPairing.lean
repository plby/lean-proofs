/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.Blueprint931

/-!
# Claim-2-certified endpoint pairings

The proof of Assertion 9.31 compresses each finite assigned alternating path
to its two endpoints.  The transaction which follows uses only the resulting
injective endpoint relation and the set of sources assigned to infinity.

This distinction matters for a literal formalization.  Theorem 4.12 supplies
an injective final-terminal map, while Claim 2 classifies a pair only after an
alternating path with those same endpoints has been shown to avoid the closed
set internally.  Truncating an arbitrary assigned path at its first visit to
the closed set does not preserve terminal injectivity.  The record below is
therefore the exact interface between the missing selection argument and the
already formalized Claim 2: it retains the endpoint map, but asks only for an
existential certified witness for each selected pair.  It does not impose the
stronger and unnecessary `SimultaneousAssignment` leaving/maximality fields on
those witnesses.
-/

noncomputable section

open Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint

open DirectedPath Alternating

universe u

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

/-- A full Claim-2 witness for one selected finite endpoint pair. -/
structure FiniteClosedEndpointWitness
    (X before innerRoof outerRoof : Set V) (u v : V) where
  path : AltPath Gamma.graph
  starts_at : path.initial = u
  ends_at : path.terminal? = some v
  safe : IsSafe Y path
  eligible : HammockEligible before innerRoof outerRoof u (.vertex v)
  interior_disjoint :
    Disjoint (hammockInterior u (.vertex v) path) X
  outside : ¬ path.vertexSet ⊆ X

/-- A full Claim-2 witness for one source selected to run to infinity. -/
structure InfiniteClosedEndpointWitness
    (X before innerRoof outerRoof : Set V) (u : V) where
  path : AltPath Gamma.graph
  starts_at : path.initial = u
  infinite : path.IsInfinite
  safe : IsSafe Y path
  eligible : HammockEligible before innerRoof outerRoof u .infinity
  interior_disjoint : Disjoint (hammockInterior u .infinity path) X
  outside : ¬ path.vertexSet ⊆ X

/-- Minimal source-faithful output of the simultaneous selection needed by
Assertion 9.31.

The option-valued endpoint map is total.  `some v` is a compressed finite
edge and `none` marks a source which becomes a popular terminal.  Finite
targets are distinct, exactly as in Theorem 4.12.  The path witnesses are
allowed to be chosen independently of the internal representation used to
obtain the endpoint matching, but have the same exposed endpoints. -/
structure ClosedEndpointPairing
    (Zf : FracturedWarp Gamma)
    (X before innerRoof outerRoof : Set V) where
  endpoint :
    {z : V // z ∈ Gamma.initialSet Zf.paths \ Gamma.initialSet Y} → Option V
  finite_mem_terminal : ∀ s v, endpoint s = some v →
    v ∈ Gamma.terminalFrontier Zf.paths
  finite_injective : ∀ ⦃s t v⦄,
    endpoint s = some v → endpoint t = some v → s = t
  finite_witness : ∀ s v, endpoint s = some v →
    Nonempty (FiniteClosedEndpointWitness
      (Gamma := Gamma) (Y := Y) X before innerRoof outerRoof s.1 v)
  infinite_witness : ∀ s, endpoint s = none →
    Nonempty (InfiniteClosedEndpointWitness
      (Gamma := Gamma) (Y := Y) X before innerRoof outerRoof s.1)

namespace ClosedEndpointPairing

variable {Zf : FracturedWarp Gamma}
variable {X before innerRoof outerRoof persistent : Set V}

/-- The finite endpoint relation selected by the pairing. -/
def finiteEdges
    (A : ClosedEndpointPairing
      (Gamma := Gamma) (Y := Y) Zf X before innerRoof outerRoof) :
    Set (V × V) :=
  {e | ∃ s, A.endpoint s = some e.2 ∧ s.1 = e.1}

theorem mem_finiteEdges_iff
    (A : ClosedEndpointPairing
      (Gamma := Gamma) (Y := Y) Zf X before innerRoof outerRoof)
    {u v : V} :
    (u, v) ∈ A.finiteEdges ↔
      ∃ s, A.endpoint s = some v ∧ s.1 = u :=
  Iff.rfl

/-- The pairing is functional at its sources. -/
theorem finiteEdges_out_unique
    (A : ClosedEndpointPairing
      (Gamma := Gamma) (Y := Y) Zf X before innerRoof outerRoof)
    {u v w : V} (huv : (u, v) ∈ A.finiteEdges)
    (huw : (u, w) ∈ A.finiteEdges) : v = w := by
  obtain ⟨s, hsv, hsu⟩ := huv
  obtain ⟨t, htw, htu⟩ := huw
  have hst : s = t := by
    apply Subtype.ext
    exact hsu.trans htu.symm
  subst t
  simpa [hsv] using htw

/-- The selected finite targets are injective. -/
theorem finiteEdges_in_unique
    (A : ClosedEndpointPairing
      (Gamma := Gamma) (Y := Y) Zf X before innerRoof outerRoof)
    {u v w : V} (huw : (u, w) ∈ A.finiteEdges)
    (hvw : (v, w) ∈ A.finiteEdges) : u = v := by
  obtain ⟨s, hsw, hsu⟩ := huw
  obtain ⟨t, htw, htv⟩ := hvw
  have hst : s = t := A.finite_injective hsw htw
  exact hsu.symm.trans (congrArg Subtype.val hst) |>.trans htv

theorem finiteEdges_biUnique
    (A : ClosedEndpointPairing
      (Gamma := Gamma) (Y := Y) Zf X before innerRoof outerRoof) :
    Relator.BiUnique (fun u v ↦ (u, v) ∈ A.finiteEdges) := by
  constructor
  · intro u v w huw hvw
    exact A.finiteEdges_in_unique huw hvw
  · intro u v w huv huw
    exact A.finiteEdges_out_unique huv huw

/-- Sources paired with infinity. -/
def infiniteSources
    (A : ClosedEndpointPairing
      (Gamma := Gamma) (Y := Y) Zf X before innerRoof outerRoof) : Set V :=
  {u | ∃ s, s.1 = u ∧ A.endpoint s = none}

/-- Every selected finite pair is classified by Claim 2. -/
theorem finite_isImaginaryEdge
    (A : ClosedEndpointPairing
      (Gamma := Gamma) (Y := Y) Zf X before innerRoof outerRoof)
    (hclosed : HammockClosedUpTo Gamma Y X before innerRoof outerRoof kappa)
    {s v} (hsv : A.endpoint s = some v) :
    IsImaginaryEdge Gamma Y kappa s.1 v := by
  obtain ⟨Q⟩ := A.finite_witness s v hsv
  exact isImaginaryEdge_of_closed hclosed Q.eligible Q.safe Q.starts_at
    Q.ends_at Q.interior_disjoint Q.outside

theorem finiteEdges_subset_imaginaryGraph
    (A : ClosedEndpointPairing
      (Gamma := Gamma) (Y := Y) Zf X before innerRoof outerRoof)
    (hclosed : HammockClosedUpTo Gamma Y X before innerRoof outerRoof kappa) :
    A.finiteEdges ⊆
      {e | (imaginaryGraph Gamma Y kappa).Adj e.1 e.2} := by
  rintro ⟨u, v⟩ ⟨s, hsv, rfl⟩
  exact Or.inr (A.finite_isImaginaryEdge hclosed hsv)

/-- Every source paired with infinity is classified as popular by Claim 2. -/
theorem infiniteSources_popular
    (A : ClosedEndpointPairing
      (Gamma := Gamma) (Y := Y) Zf X before innerRoof outerRoof)
    (hclosed : HammockClosedUpTo Gamma Y X before innerRoof outerRoof kappa) :
    A.infiniteSources ⊆
      {u | IsPopular Gamma Y persistent kappa u} := by
  rintro u ⟨s, rfl, hs⟩
  obtain ⟨Q⟩ := A.infinite_witness s hs
  exact isPopular_of_closed_infinite hclosed Q.eligible Q.safe Q.starts_at
    Q.infinite Q.interior_disjoint Q.outside

end ClosedEndpointPairing

end LinkageBlueprint
end Blueprint
end Erdos599

