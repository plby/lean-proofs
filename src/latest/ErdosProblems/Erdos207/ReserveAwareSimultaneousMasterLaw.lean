/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.LinkReserveAccounting

/-!
# Reserve-aware law update for the simultaneous link stage

A positive-mass link-law outcome is both a packing and a family of genuine
link triangles.  Consequently every prescribed subfamily with nonzero
probability is a two-crossing packing.  This permits its ordinary C4 bound
to be sharpened to zero off that structural class, while the two crossing
edges per selected triangle are charged to the previously sampled reserve.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- A simultaneous link cover is, in particular, a packing on its own. -/
lemma IsSimultaneousLinkCover.isPacking
    {O V : Type*} [DecidableEq V]
    {F : ForbiddenFamilyOn V} {available P M : TripleSystemOn V}
    {K : O → BipartiteLink V}
    (hM : IsSimultaneousLinkCover F available P K M) : IsPackingOn M :=
  hM.2.2.1.mono (by
    intro T hT
    exact mem_union_right P hT)

/-- C4 plus structural support can be sharpened to the reserve-accounting
bound, which is zero for a prescribed family that cannot occur. -/
theorem FiniteLaw.probability_subset_le_twoCrossingPackingBound
    {O V : Type*} [Fintype V] [DecidableEq V]
    {law : FiniteLaw (TripleSystemOn V)}
    {U : Finset V} {center : O ↪ V} {K : O → BipartiteLink V}
    (hcenter : ∀ o, (K o).center = center o)
    (hout : ∀ o, center o ∉ U)
    (hleft : ∀ o, (K o).left ⊆ U)
    (hright : ∀ o, (K o).right ⊆ U)
    (hstruct : law.SupportedOn fun M ↦
      IsSimultaneousLinkFamily K M ∧ IsPackingOn M)
    (alpha : ℝ≥0)
    (hC4 : ∀ Q : TripleSystemOn V,
      law.probability (fun M ↦ Q ⊆ M) ≤ alpha ^ Q.card)
    (Q : TripleSystemOn V) :
    law.probability (fun M ↦ Q ⊆ M) ≤
      twoCrossingPackingBound U alpha Q := by
  classical
  by_cases hQ : IsTwoCrossingPacking U Q
  · simpa only [twoCrossingPackingBound, if_pos hQ] using hC4 Q
  · have hzero : law.probability (fun M ↦ Q ⊆ M) = 0 := by
      apply le_antisymm
      · calc
          law.probability (fun M ↦ Q ⊆ M) ≤
              law.probability (fun _M ↦ False) := by
            apply law.probability_mono_of_supported hstruct
            intro M hM hQM
            apply hQ
            exact (hM.1.mono hQM).isTwoCrossingPacking
              hcenter hout hleft hright (hM.2.mono hQM)
          _ = 0 := law.probability_false
      · exact zero_le
    rw [hzero]
    simp [twoCrossingPackingBound, hQ]

/-- Reserve-aware strong distribution survives adjoining a simultaneous
link law.  All combinatorial work is discharged here; the remaining input is
the scalar powerset-partition inequality with the exact `2 * |Q|` reserve
factor encoded by `familyCrossingEdges`. -/
theorem IsReserveStronglyWellDistributed.jointBind_simultaneousLink
    {Omega O V : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype O] [Fintype V] [DecidableEq V]
    {ell : ℕ} {law : FiniteLaw Omega}
    {linkLaw : Omega → FiniteLaw (TripleSystemOn V)}
    {W : Vortex V ell} {k next : Fin (ell + 1)}
    {initial later : Omega → TripleSystemOn V}
    {reserve : Omega → Finset (Sym2 V)}
    {U : Finset V} {center : Omega → O ↪ V}
    {K : Omega → O → BipartiteLink V}
    {p reserveDensity C b alpha p' C' b' : ℝ≥0}
    (hstrong : IsReserveStronglyWellDistributed law W k initial later reserve
      p reserveDensity C b)
    (hcenter : ∀ omega o, (K omega o).center = center omega o)
    (hout : ∀ omega o, center omega o ∉ U)
    (hleft : ∀ omega o, (K omega o).left ⊆ U)
    (hright : ∀ omega o, (K omega o).right ⊆ U)
    (hspokes : ∀ omega o, (K omega o).SpokesIn (reserve omega))
    (hstruct : ∀ omega, (linkLaw omega).SupportedOn fun M ↦
      IsSimultaneousLinkFamily (K omega) M ∧ IsPackingOn M)
    (hC4 : ∀ omega Q,
      (linkLaw omega).probability (fun M ↦ Q ⊆ M) ≤ alpha ^ Q.card)
    (hpartition : ∀ (Ifix Dfix : TripleSystemOn V)
      (Efix : Finset (Sym2 V)), Disjoint Ifix Dfix →
      ∀ S ∈ Dfix.powerset,
        twoCrossingPackingBound U alpha (Dfix \ S) *
          (C ^ (Ifix.card + S.card + Efix.card +
              (familyCrossingEdges U (Dfix \ S)).card) *
            (p ^ Efix.card *
                reserveDensity ^ (familyCrossingEdges U (Dfix \ S)).card *
                (Fintype.card V : ℝ≥0)⁻¹ ^ Ifix.card *
                laterTriangleScale W k p S + b)) ≤
          C' ^ (Ifix.card + Dfix.card + Efix.card) *
            (p' ^ Efix.card *
                (Fintype.card V : ℝ≥0)⁻¹ ^ Ifix.card *
                laterTriangleScale W next p' Dfix + b')) :
    IsStronglyWellDistributed (law.jointBind linkLaw) W next
      (jointInitial initial) (jointLater later (fun _omega M ↦ M))
      p' (2 * C') b' := by
  apply hstrong.jointBind_adjoin
    (added := fun _omega M ↦ M)
    (addedBound := twoCrossingPackingBound U alpha)
    (required := familyCrossingEdges U)
  · intro omega Q
    exact (linkLaw omega).probability_subset_le_twoCrossingPackingBound
      (hcenter omega) (hout omega) (hleft omega) (hright omega)
      (hstruct omega) alpha (hC4 omega) Q
  · intro omega M Q hmass hQM
    have hM := hstruct omega M hmass
    exact (hM.1.mono hQM).familyCrossingEdges_subset
      (hcenter omega) (hout omega) (hleft omega) (hright omega)
      (hspokes omega)
  · exact hpartition

/-- Convenient form of the preceding theorem.  Structurally impossible
powerset parts vanish; for every possible part the reserve-edge cardinality
is rewritten to `2 * |Q|`, exposing the exact factor
`alpha^|Q| * reserveDensity^(2*|Q|)`. -/
theorem IsReserveStronglyWellDistributed.jointBind_simultaneousLink_of_good_partition
    {Omega O V : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype O] [Fintype V] [DecidableEq V]
    {ell : ℕ} {law : FiniteLaw Omega}
    {linkLaw : Omega → FiniteLaw (TripleSystemOn V)}
    {W : Vortex V ell} {k next : Fin (ell + 1)}
    {initial later : Omega → TripleSystemOn V}
    {reserve : Omega → Finset (Sym2 V)}
    {U : Finset V} {center : Omega → O ↪ V}
    {K : Omega → O → BipartiteLink V}
    {p reserveDensity C b alpha p' C' b' : ℝ≥0}
    (hstrong : IsReserveStronglyWellDistributed law W k initial later reserve
      p reserveDensity C b)
    (hcenter : ∀ omega o, (K omega o).center = center omega o)
    (hout : ∀ omega o, center omega o ∉ U)
    (hleft : ∀ omega o, (K omega o).left ⊆ U)
    (hright : ∀ omega o, (K omega o).right ⊆ U)
    (hspokes : ∀ omega o, (K omega o).SpokesIn (reserve omega))
    (hstruct : ∀ omega, (linkLaw omega).SupportedOn fun M ↦
      IsSimultaneousLinkFamily (K omega) M ∧ IsPackingOn M)
    (hC4 : ∀ omega Q,
      (linkLaw omega).probability (fun M ↦ Q ⊆ M) ≤ alpha ^ Q.card)
    (hpartition : ∀ (Ifix Dfix : TripleSystemOn V)
      (Efix : Finset (Sym2 V)), Disjoint Ifix Dfix →
      ∀ S ∈ Dfix.powerset,
        IsTwoCrossingPacking U (Dfix \ S) →
        alpha ^ (Dfix \ S).card *
          (C ^ (Ifix.card + S.card + Efix.card +
              2 * (Dfix \ S).card) *
            (p ^ Efix.card *
                reserveDensity ^ (2 * (Dfix \ S).card) *
                (Fintype.card V : ℝ≥0)⁻¹ ^ Ifix.card *
                laterTriangleScale W k p S + b)) ≤
          C' ^ (Ifix.card + Dfix.card + Efix.card) *
            (p' ^ Efix.card *
                (Fintype.card V : ℝ≥0)⁻¹ ^ Ifix.card *
                laterTriangleScale W next p' Dfix + b')) :
    IsStronglyWellDistributed (law.jointBind linkLaw) W next
      (jointInitial initial) (jointLater later (fun _omega M ↦ M))
      p' (2 * C') b' := by
  apply hstrong.jointBind_simultaneousLink hcenter hout hleft hright hspokes
    hstruct hC4
  intro Ifix Dfix Efix hdisj S hS
  let Q := Dfix \ S
  by_cases hQ : IsTwoCrossingPacking U Q
  · have hcard := hQ.card_familyCrossingEdges
    simpa only [Q, twoCrossingPackingBound, if_pos hQ, hcard] using
      hpartition Ifix Dfix Efix hdisj S hS hQ
  · change ¬ IsTwoCrossingPacking U (Dfix \ S) at hQ
    simp [twoCrossingPackingBound, hQ]

end

end Erdos207
