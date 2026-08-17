/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos641.RegularFree

/-!
# Dense-prefix events in the JSS construction

This file connects the semantic dense-set obstruction to the coordinate
cylinders controlled by the PRS all-scales union bound.
-/

open Finset Fintype Filter
open scoped BigOperators Classical

namespace Erdos641

open SimpleGraph
open Erdos182

noncomputable section

/-- Regard `j + 1` as a layer index. -/
def jssSuccessorLayer {n : ℕ}
    (j : Fin (prsLayerCount n - 1)) : Fin (prsLayerCount n) :=
  ⟨j.val + 1, by omega⟩

@[simp] lemma val_jssSuccessorLayer {n : ℕ}
    (j : Fin (prsLayerCount n - 1)) :
    (jssSuccessorLayer j).val = j.val + 1 := rfl

/-- A bad event at layer `i`: a small set in the strict prefix spans at
least `ceil(11|S|/10)` selected edges. -/
def DenseJSSPrefixBadAt {n : ℕ} (G : SimpleGraph (JSSVertex n))
    (i : Fin (prsLayerCount n)) : Prop :=
  ∃ S : Finset (JSSVertex n),
    S.Nonempty ∧ S ⊆ jssPrefix n i ∧
      S.card ≤ 1000 * prsLayerSize n i.val ∧
        prsBadEdgeCount S.card ≤
          (G.induce (S : Set (JSSVertex n))).edgeFinset.card

/-- A semantic dense-prefix event supplies one of the concrete coordinate
cylinders in the PRS all-scales union bound. -/
lemma mem_prsDemandUnion_of_denseJSSPrefixBadAt
    {n : ℕ} (ω default : JSSOutcome n) (hω : ω ∈ jssOutcomeSpace n)
    (i : Fin (prsLayerCount n))
    (hbad : DenseJSSPrefixBadAt (jssGraph ω hω) i) :
    ∃ x : ℕ, 1 ≤ x ∧ x ≤ 1000 * prsLayerSize n i.val ∧
      ω ∈ prsDemandUnion jssAllowed x
        (fun S ↦ prefixJSSCoordinateDemands default i
          (prsBadEdgeCount x) S) := by
  classical
  obtain ⟨S, hSne, hSprefix, hSsmall, hdense⟩ := hbad
  let r := prsBadEdgeCount S.card
  have hr : r ≤ (realizedCandidateJSSDemands ω S).card := by
    rw [card_realizedCandidateJSSDemands ω hω S]
    exact hdense
  obtain ⟨R, hRsub, hRcard⟩ := Finset.exists_subset_card_eq hr
  have hRcandidate : R ⊆ candidateJSSDemands S := by
    intro d hd
    exact (mem_realizedCandidateJSSDemands.mp (hRsub hd)).1
  have hRcompatible : CompatibleJSSDemands R :=
    compatible_of_subset_realizedJSSDemands hRsub
  refine ⟨S.card, Finset.card_pos.mpr hSne, hSsmall, ?_⟩
  simp only [prsDemandUnion, Finset.mem_biUnion]
  refine ⟨S, ?_, coordinateDemandOfJSSDemands default R, ?_, ?_⟩
  · exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ S, rfl⟩
  · simp only [prefixJSSCoordinateDemands, if_pos hSprefix,
      candidateJSSCoordinateDemands]
    apply Finset.mem_image.mpr
    refine ⟨R, ?_, rfl⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_powersetCard.mpr ⟨hRcandidate, hRcard⟩, hRcompatible⟩
  · exact mem_coordinateDemand_outcomes_of_subset_realizedJSS
      ω default hω hRsub

/-- Eventually one admissible JSS outcome avoids every dense-prefix event at
the scales required by the deterministic obstruction. -/
theorem eventually_exists_jssOutcome_avoiding_dense :
    ∀ᶠ n : ℕ in atTop, ∃ ω : JSSOutcome n, ∃ hω : ω ∈ jssOutcomeSpace n,
      ∀ j : Fin (prsLayerCount n - 1),
        ¬ DenseJSSPrefixBadAt (jssGraph ω hω)
          (jssSuccessorLayer j) := by
  filter_upwards [eventually_two_le_prsLayerCount,
      eventually_prsLayerSize_bounds, eventually_card_JSSVertex_le,
      eventually_four_thousand_mul_prsLayerSize_succ_le,
      eventually_prs_error_lt_one, eventually_prs_badEvent_choose_bound] with
      n hcount hlayer hcard hseparate herror honeEvent
  classical
  have hlayerPos : ∀ i < prsLayerCount n, 0 < prsLayerSize n i :=
    fun i hi ↦ (hlayer i hi).1
  have hallowed : ∀ c : JSSCoordinate n, (jssAllowed c).Nonempty := by
    intro c
    apply Finset.card_pos.mp
    rw [card_jssAllowed]
    exact hlayerPos c.targetLayer c.targetLayer.isLt
  choose target htarget using hallowed
  let default : JSSOutcome n := fun c _hc ↦ target c
  have hdefault : default ∈ jssOutcomeSpace n := by
    rw [mem_jssOutcomeSpace]
    intro c
    exact htarget c
  have hstep : ∀ i, i + 1 < prsLayerCount n →
      prsLayerSize n (i + 1) ≤ prsLayerSize n i := by
    intro i hi
    have := hseparate i hi
    omega
  have hhalf : Real.exp (-(prsY n / 2)) ≤ (1 / 2 : ℝ) := by
    have hcountR : (2 : ℝ) ≤ prsLayerCount n := by exact_mod_cast hcount
    have hmul : 2 * 2 * Real.exp (-(prsY n / 2)) ≤
        2 * (prsLayerCount n : ℝ) * Real.exp (-(prsY n / 2)) := by
      gcongr
    linarith [Real.exp_pos (-(prsY n / 2))]
  obtain ⟨ω, hω, hAvoid⟩ :=
    exists_choice_avoiding_shifted_prs_demands n jssAllowed
      (fun j z S ↦ prefixJSSCoordinateDemands default
        (jssSuccessorLayer j) (prsBadEdgeCount (z.val + 1)) S)
      hcard hcount hlayerPos ⟨default, hdefault⟩ (by
        intro j z S hS
        have hScard := (Finset.mem_powersetCard.mp hS).2
        by_cases hprefix : S ⊆ jssPrefix n (jssSuccessorLayer j)
        · simpa [prefixJSSCoordinateDemands, hprefix, hScard] using
            card_candidateJSSCoordinateDemands_le_choose default S
              (prsBadEdgeCount (z.val + 1))
        · simp [prefixJSSCoordinateDemands, hprefix]) (by
        intro j z S hS d hd
        have hScard := (Finset.mem_powersetCard.mp hS).2
        simpa [hScard] using
          coords_card_of_mem_prefixJSSCoordinateDemands default
            (jssSuccessorLayer j) S (prsBadEdgeCount (z.val + 1)) hd) (by
        intro j z S _hS d hd c hc
        apply allowed_card_lower_of_mem_prefixJSSCoordinateDemands default
          (jssSuccessorLayer j) S (prsBadEdgeCount (z.val + 1))
          (prsLayerSize n j.val) (fun k hk ↦ ?_) hd hc
        have hk' : k.val < j.val + 1 := by
          change k.val < (jssSuccessorLayer j).val at hk
          simpa using hk
        exact prsLayerSize_antitone_below hstep (Nat.le_of_lt_succ hk') (by
          omega)) honeEvent hhalf herror
  refine ⟨ω, hω, ?_⟩
  intro j hbad
  obtain ⟨x, hx, hxcut, hxmem⟩ :=
    mem_prsDemandUnion_of_denseJSSPrefixBadAt ω default hω
      (jssSuccessorLayer j) hbad
  have hxcut' : x ≤ 1000 * prsLayerSize n (j.val + 1) := by
    simpa using hxcut
  let z : Fin (prsBadCutoff n j) := ⟨x - 1, by
    rw [prsBadCutoff]
    change x - 1 < 1000 * prsLayerSize n (j.val + 1)
    omega⟩
  apply hAvoid j z
  simpa [z, Nat.sub_add_cancel hx] using hxmem

end

end Erdos641
