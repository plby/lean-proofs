import ErdosProblems.Erdos486.BiasedCandidateGeometry
import ErdosProblems.Erdos486.BiasedCollisionUnion
import ErdosProblems.Erdos486.FourColorTail
import ErdosProblems.Erdos486.ColoringEnumeration
import ErdosProblems.Erdos486.BiasedNumerics
import ErdosProblems.Erdos486.FiniteAveraging
import ErdosProblems.Erdos486.BiasedSummability
import ErdosProblems.Erdos486.BiasedFootprintAverage
import ErdosProblems.Erdos486.BiasedAnchorTail

/- Ported to Lean/Mathlib 4.33.0; see README.md for source and modifications. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The finite biased-colouring block

This file completes the finite probabilistic-method argument by explicit
enumeration.  For every scale `j ≥ 400`, the uniform rational average of the
periodic footprint over all four-colourings is at most

`3 * (63 / 64) ^ (2 * biasedRadius j)`.

The three terms are the arithmetic collision union, the bad-anchor tail, and
the weighted union bound for good anchors.  All averages are finite sums; no
probability measure is used.
-/

open scoped BigOperators

namespace Erdos486

noncomputable section

private instance biasedFiniteBlockPeriodNeZero (j : ℕ) :
    NeZero (biasedPeriod j) :=
  ⟨(biasedPeriod_pos j).ne'⟩

private noncomputable instance biasedFiniteBlockColoringFintype (j : ℕ) :
    Fintype (BiasedColoring j) := by
  classical
  exact Pi.instFintype

private theorem fintypeAverage_mono {α : Type*} [Fintype α]
    {f g : α → ℚ} (h : ∀ x, f x ≤ g x) :
    fintypeAverage f ≤ fintypeAverage g := by
  unfold fintypeAverage
  exact div_le_div_of_nonneg_right
    (Finset.sum_le_sum fun x _hx ↦ h x) (Nat.cast_nonneg _)

private theorem fintypeAverage_add {α : Type*} [Fintype α]
    (f g : α → ℚ) :
    fintypeAverage (fun x ↦ f x + g x) =
      fintypeAverage f + fintypeAverage g := by
  simp only [fintypeAverage, Finset.sum_add_distrib, add_div]

private theorem fintypeAverage_mul_sum {α β : Type*}
    [Fintype α] [Fintype β] [Nonempty α]
    (a : ℚ) (f : β → α → ℚ) :
    fintypeAverage (fun x ↦ a * ∑ y, f y x) =
      a * ∑ y, fintypeAverage (f y) := by
  unfold fintypeAverage
  calc
    (∑ x : α, a * ∑ y : β, f y x) / Fintype.card α =
        (a * ∑ x : α, ∑ y : β, f y x) / Fintype.card α := by
      rw [Finset.mul_sum]
    _ = (a * ∑ y : β, ∑ x : α, f y x) / Fintype.card α := by
      rw [Finset.sum_comm]
    _ = a * ((∑ y : β, ∑ x : α, f y x) / Fintype.card α) := by
      ring
    _ = a * ∑ y : β, (∑ x : α, f y x) / Fintype.card α := by
      rw [Finset.sum_div]

private noncomputable def biasedCollisionIndicator (j : ℕ)
    (x : ZMod (biasedPeriod j)) : ℚ :=
  if x.val ∈ biasedCollisionUnion j then 1 else 0

private noncomputable def biasedGoodMajorant (j : ℕ)
    (x : ZMod (biasedPeriod j)) (c : BiasedColoring j) : ℚ :=
  if x.val ∈ biasedCollisionUnion j then 0 else
    (2 : ℚ) ^ (2 * biasedRadius j) *
      ∑ S : Finset (Fin (biasedK j)),
        weightedCandidate (biasedAnchor j x.val) (biasedQuery j x.val S) S c

private theorem weightedCandidate_nonneg {k : ℕ} {ι : Type*}
    (anchor query : Fin k → ι) (S : Finset (Fin k))
    (c : FourColoring ι) :
    0 ≤ weightedCandidate anchor query S c := by
  classical
  unfold weightedCandidate
  apply Finset.prod_nonneg
  intro o _ho
  cases o with
  | inl i =>
      by_cases hi : i ∈ S
      · by_cases hc : c (candidateOracle anchor query S (Sum.inl i)) = 0
        · simp [candidateOracleWeight, hi, selectedAnchorWeight, hc]
        · simp [candidateOracleWeight, hi, selectedAnchorWeight, hc]
      · by_cases hc : c (candidateOracle anchor query S (Sum.inl i)) = 0
        · simp [candidateOracleWeight, hi, halfBlackWeight, hc]
        · simp [candidateOracleWeight, hi, halfBlackWeight, hc]
  | inr i =>
      by_cases hc : c (candidateOracle anchor query S (Sum.inr i)) = 0
      · simp [candidateOracleWeight, nonblackQueryWeight, hc]
      · simp [candidateOracleWeight, nonblackQueryWeight, hc]

private theorem biasedGoodMajorant_nonneg (j : ℕ)
    (x : ZMod (biasedPeriod j)) (c : BiasedColoring j) :
    0 ≤ biasedGoodMajorant j x c := by
  classical
  unfold biasedGoodMajorant
  split
  · simp
  · exact mul_nonneg (by positivity)
      (Finset.sum_nonneg fun S _hS ↦
        weightedCandidate_nonneg
          (biasedAnchor j x.val) (biasedQuery j x.val S) S c)

/-! ## The collision term -/

private theorem mem_biasedCollisionUnion_lt {j n : ℕ}
    (hn : n ∈ biasedCollisionUnion j) :
    n < biasedPeriod j := by
  classical
  rw [biasedCollisionUnion, Finset.mem_biUnion] at hn
  obtain ⟨a, _ha, hn⟩ := hn
  exact Finset.mem_range.mp
    (Finset.mem_filter.mp hn).1

private theorem biasedCollisionIndicator_average (j : ℕ) :
    fintypeAverage (biasedCollisionIndicator j) =
      biasedCollisionUnionRatio j := by
  classical
  let e :
      {x : ZMod (biasedPeriod j) //
          x.val ∈ biasedCollisionUnion j} ≃
        ↥(biasedCollisionUnion j) :=
    { toFun := fun x ↦ ⟨x.1.val, x.2⟩
      invFun := fun n ↦
        ⟨(n.1 : ZMod (biasedPeriod j)), by
          rw [ZMod.val_natCast_of_lt
            (mem_biasedCollisionUnion_lt n.2)]
          exact n.2⟩
      left_inv := fun x ↦ by
        apply Subtype.ext
        exact ZMod.natCast_zmod_val x.1
      right_inv := fun n ↦ by
        apply Subtype.ext
        exact ZMod.val_natCast_of_lt
          (mem_biasedCollisionUnion_lt n.2) }
  have hcard :
      ((Finset.univ : Finset (ZMod (biasedPeriod j))).filter
          fun x ↦ x.val ∈ biasedCollisionUnion j).card =
        (biasedCollisionUnion j).card := by
    rw [← Fintype.card_subtype]
    exact (Fintype.card_congr e).trans
      (Fintype.card_coe (biasedCollisionUnion j))
  change
    (∑ x : ZMod (biasedPeriod j),
        if x.val ∈ biasedCollisionUnion j then (1 : ℚ) else 0) /
        Fintype.card (ZMod (biasedPeriod j)) =
      biasedCollisionUnionRatio j
  rw [Finset.sum_boole, hcard, biasedCollisionUnionRatio,
    ZMod.card]

private theorem biasedCollisionIndicator_average_le {j : ℕ}
    (hj : 400 ≤ j) :
    fintypeAverage (biasedCollisionIndicator j) ≤
      ((63 : ℚ) / 64) ^ (2 * biasedRadius j) := by
  rw [biasedCollisionIndicator_average]
  exact biasedCollisionUnionRatio_le hj

/-! ## The weighted good-anchor term -/

private theorem hasNoBiasedCollision_of_not_mem {j : ℕ}
    {x : ZMod (biasedPeriod j)}
    (hx : x.val ∉ biasedCollisionUnion j) :
    HasNoBiasedCollision j x.val := by
  classical
  intro S i hi hcollision
  apply hx
  rw [biasedCollisionUnion, Finset.mem_biUnion]
  refine ⟨(S, i),
    (mem_biasedCollisionIndices_iff j S i).2 hi, ?_⟩
  rw [biasedCollisionResidues, Finset.mem_filter]
  exact ⟨Finset.mem_range.mpr (ZMod.val_lt x), hcollision⟩

private theorem biasedGoodMajorant_average_le {j : ℕ}
    (_hj : 400 ≤ j) (x : ZMod (biasedPeriod j)) :
    fintypeAverage (biasedGoodMajorant j x) ≤
      ((63 : ℚ) / 64) ^ (2 * biasedRadius j) := by
  classical
  by_cases hcollision : x.val ∈ biasedCollisionUnion j
  · have hnonneg :
        (0 : ℚ) ≤ ((63 : ℚ) / 64) ^ (2 * biasedRadius j) := by
      positivity
    have hmajorant :
        biasedGoodMajorant j x = fun _c : BiasedColoring j ↦ 0 := by
      funext c
      simp [biasedGoodMajorant, hcollision]
    rw [hmajorant, fintypeAverage_const]
    exact hnonneg
  · have hno : HasNoBiasedCollision j x.val :=
      hasNoBiasedCollision_of_not_mem hcollision
    have hmajorant :
        biasedGoodMajorant j x =
          fun c : BiasedColoring j ↦
            (2 : ℚ) ^ (2 * biasedRadius j) *
              ∑ S : Finset (Fin (biasedK j)),
                weightedCandidate (biasedAnchor j x.val)
                  (biasedQuery j x.val S) S c := by
      funext c
      simp [biasedGoodMajorant, hcollision]
    rw [hmajorant]
    rw [fintypeAverage_mul_sum]
    simpa only [biasedK] using
      (scaled_sum_average_weightedCandidate_le
        (ι := BiasedCoordinate j) (biasedRadius j)
        (biasedAnchor j x.val)
        (fun S ↦ biasedQuery j x.val S)
        (fun S ↦ biasedCandidateOracle_injective hno S))

/-! ## Pointwise collision/bad/good domination -/

private theorem biasedCoverageIndicator_le_majorants {j : ℕ}
    (hj : 400 ≤ j) (x : ZMod (biasedPeriod j))
    (c : BiasedColoring j) :
    biasedCoverageIndicator j x c ≤
      biasedCollisionIndicator j x +
        (if 2 * biasedRadius j <
            anchorBlackCount (biasedAnchor j x.val) c then
          (1 : ℚ)
        else 0) +
        biasedGoodMajorant j x c := by
  classical
  have hmajorantNonneg : 0 ≤ biasedGoodMajorant j x c :=
    biasedGoodMajorant_nonneg j x c
  by_cases hcollision : x.val ∈ biasedCollisionUnion j
  · have hcovered_le : biasedCoverageIndicator j x c ≤ 1 := by
      unfold biasedCoverageIndicator
      split <;> norm_num
    have hcollisionIndicator : biasedCollisionIndicator j x = 1 := by
      simp [biasedCollisionIndicator, hcollision]
    rw [hcollisionIndicator]
    have hbadNonneg :
        0 ≤ if 2 * biasedRadius j <
            anchorBlackCount (biasedAnchor j x.val) c then
          (1 : ℚ)
        else 0 := by
      split <;> norm_num
    linarith
  · have hcollisionIndicator : biasedCollisionIndicator j x = 0 := by
      simp [biasedCollisionIndicator, hcollision]
    rw [hcollisionIndicator, zero_add]
    by_cases hcovered : IsBiasedCovered j c x
    · have hcoverageIndicator : biasedCoverageIndicator j x c = 1 := by
        simp [biasedCoverageIndicator, hcovered]
      rw [hcoverageIndicator]
      by_cases hbad : 2 * biasedRadius j <
          anchorBlackCount (biasedAnchor j x.val) c
      · rw [if_pos hbad]
        exact le_add_of_nonneg_right hmajorantNonneg
      · rw [if_neg hbad, zero_add]
        have hanchorGood :
            anchorBlackCount (biasedAnchor j x.val) c ≤
              2 * biasedRadius j := Nat.le_of_not_gt hbad
        obtain ⟨S, hvalid, hselected⟩ :=
          exists_candidate_of_isBiasedCovered hj c x hcovered
        have hoccurs :
            CandidateOccurs (biasedAnchor j x.val)
              (biasedQuery j x.val S) S c :=
          candidateOccurs_of_selectedPrimes_eq S c hvalid hselected
        have hone :
            (1 : ℚ) ≤ (2 : ℚ) ^ (2 * biasedRadius j) *
              weightedCandidate (biasedAnchor j x.val)
                (biasedQuery j x.val S) S c :=
          one_le_scaled_weightedCandidate_of_good
            (biasedAnchor j x.val) (biasedQuery j x.val S) S c
            hanchorGood hoccurs
        have hsum :
            weightedCandidate (biasedAnchor j x.val)
                (biasedQuery j x.val S) S c ≤
              ∑ T : Finset (Fin (biasedK j)),
                weightedCandidate (biasedAnchor j x.val)
                  (biasedQuery j x.val T) T c := by
          exact Finset.single_le_sum
            (fun T _hT ↦ weightedCandidate_nonneg
              (biasedAnchor j x.val) (biasedQuery j x.val T) T c)
            (Finset.mem_univ S)
        have hscaled := mul_le_mul_of_nonneg_left hsum
          (by positivity : (0 : ℚ) ≤
            (2 : ℚ) ^ (2 * biasedRadius j))
        have hmajorant :
            biasedGoodMajorant j x c =
              (2 : ℚ) ^ (2 * biasedRadius j) *
                ∑ T : Finset (Fin (biasedK j)),
                  weightedCandidate (biasedAnchor j x.val)
                    (biasedQuery j x.val T) T c := by
          simp [biasedGoodMajorant, hcollision]
        rw [hmajorant]
        exact hone.trans hscaled
    · have hcoverageIndicator : biasedCoverageIndicator j x c = 0 := by
        simp [biasedCoverageIndicator, hcovered]
      rw [hcoverageIndicator]
      exact add_nonneg (by split <;> norm_num) hmajorantNonneg

private theorem biasedCoverageAverage_le_collision_add_two {j : ℕ}
    (hj : 400 ≤ j) (x : ZMod (biasedPeriod j)) :
    fintypeAverage (fun c : BiasedColoring j ↦
        biasedCoverageIndicator j x c) ≤
      biasedCollisionIndicator j x +
        ((63 : ℚ) / 64) ^ (2 * biasedRadius j) +
        ((63 : ℚ) / 64) ^ (2 * biasedRadius j) := by
  have hpointwise :
      fintypeAverage (fun c : BiasedColoring j ↦
          biasedCoverageIndicator j x c) ≤
        fintypeAverage (fun c : BiasedColoring j ↦
          biasedCollisionIndicator j x +
            (if 2 * biasedRadius j <
                anchorBlackCount (biasedAnchor j x.val) c then
              (1 : ℚ)
            else 0) +
            biasedGoodMajorant j x c) :=
    fintypeAverage_mono fun c ↦
      biasedCoverageIndicator_le_majorants hj x c
  rw [fintypeAverage_add, fintypeAverage_add,
    fintypeAverage_const] at hpointwise
  have hbad :
      fintypeAverage
          (fun c : BiasedColoring j ↦
            if 2 * biasedRadius j <
                anchorBlackCount (biasedAnchor j x.val) c then
              (1 : ℚ)
            else 0) ≤
        ((63 : ℚ) / 64) ^ (2 * biasedRadius j) :=
    (biasedBadAnchorAverage_le j x).trans
      (bad_anchor_numeric_le (biasedRadius j))
  have hgood := biasedGoodMajorant_average_le hj x
  linarith

/-! ## The finite block average and deterministic colouring -/

/-- Uniformly averaging the exact rational footprint over all biased
four-colourings costs at most the sum of the collision, bad-anchor, and
good-anchor errors. -/
theorem fintypeAverage_biasedFootprintRat_le {j : ℕ}
    (hj : 400 ≤ j) :
    fintypeAverage
        (fun c : BiasedColoring j ↦ biasedFootprintRat j c) ≤
      3 * ((63 : ℚ) / 64) ^ (2 * biasedRadius j) := by
  rw [fintypeAverage_biasedFootprintRat]
  calc
    fintypeAverage
        (fun x : ZMod (biasedPeriod j) ↦
          fintypeAverage (fun c : BiasedColoring j ↦
            biasedCoverageIndicator j x c)) ≤
        fintypeAverage
          (fun x : ZMod (biasedPeriod j) ↦
            biasedCollisionIndicator j x +
              ((63 : ℚ) / 64) ^ (2 * biasedRadius j) +
              ((63 : ℚ) / 64) ^ (2 * biasedRadius j)) :=
      fintypeAverage_mono fun x ↦
        biasedCoverageAverage_le_collision_add_two hj x
    _ = fintypeAverage (biasedCollisionIndicator j) +
          ((63 : ℚ) / 64) ^ (2 * biasedRadius j) +
          ((63 : ℚ) / 64) ^ (2 * biasedRadius j) := by
      rw [fintypeAverage_add, fintypeAverage_add,
        fintypeAverage_const]
    _ ≤ ((63 : ℚ) / 64) ^ (2 * biasedRadius j) +
          ((63 : ℚ) / 64) ^ (2 * biasedRadius j) +
          ((63 : ℚ) / 64) ^ (2 * biasedRadius j) := by
      linarith [biasedCollisionIndicator_average_le hj]
    _ = 3 * ((63 : ℚ) / 64) ^ (2 * biasedRadius j) := by
      ring

/-- A deterministic biased colouring attaining the finite-block footprint
allowance. -/
theorem exists_biasedColoring_footprint_le {j : ℕ} (hj : 400 ≤ j) :
    ∃ c : BiasedColoring j, biasedFootprint j c ≤ biasedEta j := by
  obtain ⟨c, hc⟩ := exists_le_of_fintypeAverage_le
    (fun c : BiasedColoring j ↦ biasedFootprintRat j c)
    (fintypeAverage_biasedFootprintRat_le hj)
  refine ⟨c, ?_⟩
  have hcReal :
      ((biasedFootprintRat j c : ℚ) : ℝ) ≤
        ((3 * ((63 : ℚ) / 64) ^ (2 * biasedRadius j) : ℚ) : ℝ) := by
    exact_mod_cast hc
  rw [biasedFootprintRat_cast_real] at hcReal
  simpa [biasedEta] using hcReal

end

end Erdos486
