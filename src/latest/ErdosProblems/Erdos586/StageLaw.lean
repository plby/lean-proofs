/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos586.CongruenceMass
import ErdosProblems.Erdos586.PrimeStages

/-!
# The recursive distorted-measure law for Erdős Problem 586

This file joins the finite probability update to the prime-stage CRT
coordinates.  It deliberately contains no analytic estimates: the bad set
at a stage is the literal union of the selected congruence classes assigned
to that stage, and `stageDistribution` is obtained by distorting the uniform
lift of the preceding distribution and transporting it back through CRT.
-/

open scoped BigOperators

namespace Erdos586

noncomputable section

/-! ## Fixed distortion parameters -/

/-- The parameter choice used in the finite certificate: no distortion at
the first three prime stages and distortion `1/5` thereafter. -/
def distortionDelta (r : ℕ) : ℝ := if r ≤ 3 then 0 else 1 / 5

lemma distortionDelta_of_le_three {r : ℕ} (hr : r ≤ 3) :
    distortionDelta r = 0 := by simp [distortionDelta, hr]

lemma distortionDelta_of_three_lt {r : ℕ} (hr : 3 < r) :
    distortionDelta r = 1 / 5 := by simp [distortionDelta, Nat.not_le.mpr hr]

lemma distortionDelta_nonneg (r : ℕ) : 0 ≤ distortionDelta r := by
  unfold distortionDelta
  split_ifs <;> norm_num

lemma distortionDelta_le_half (r : ℕ) : distortionDelta r ≤ 1 / 2 := by
  unfold distortionDelta
  split_ifs <;> norm_num

/-- Finite probability mass is subadditive under union. -/
lemma FiniteProbability.mass_union_le
    {X : Type*} [Fintype X] (μ : FiniteProbability X) (S T : Set X) :
    μ.mass (S ∪ T) ≤ μ.mass S + μ.mass T := by
  classical
  unfold FiniteProbability.mass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x hx
  by_cases hS : x ∈ S <;> by_cases hT : x ∈ T <;>
    simp [hS, hT, μ.weight_nonneg x]

/-! ## Stage bad events -/

/-- The new prime-power coordinate exposed in the zero-indexed transition
from stage `r` to stage `r+1`. -/
abbrev StageCoordinate (Q r : ℕ) :=
  ZMod (stagePrime (r + 1) ^ stageExponent Q (r + 1))

local instance partialPeriodNeZero (Q r : ℕ) :
    NeZero (partialPeriod Q r) := ⟨(partialPeriod_pos Q r).ne'⟩

local instance stagePowerNeZero (Q r : ℕ) :
    NeZero (stagePrime (r + 1) ^ stageExponent Q (r + 1)) :=
  ⟨pow_ne_zero _ (stagePrime_pos (by omega)).ne'⟩

/-- Occurrences in the chosen subfamily whose modulus is first processed at
the transition from `r` to `r+1`. -/
def stageIndices (A : CoveringFamily) (s : Finset (Fin A.length))
    (Q r : ℕ) : Finset (Fin A.length) := by
  classical
  exact s.filter fun i => IsNewModulus Q (r + 1) (A.get i).modulus

lemma mem_stageIndices_iff {A : CoveringFamily} {s : Finset (Fin A.length)}
    {Q r : ℕ} {i : Fin A.length} :
    i ∈ stageIndices A s Q r ↔
      i ∈ s ∧ IsNewModulus Q (r + 1) (A.get i).modulus := by
  classical
  simp [stageIndices]

/-- A modulus assigned to a stage divides that stage's partial period. -/
lemma newModulus_dvd_partialPeriod_succ {Q r d : ℕ} (hQ : Q ≠ 0)
    (hnew : IsNewModulus Q (r + 1) d) :
    d ∣ partialPeriod Q (r + 1) := by
  obtain ⟨m, j, hm, hj, hjle, hp, hd⟩ :=
    newModulus_exists_oldPart_pow hQ hnew
  rw [partialPeriod_succ Q r, hd]
  exact Nat.mul_dvd_mul hm (Nat.pow_dvd_pow _ hjle)

/-- The union of all selected congruence classes newly processed in one
stage, written in the CRT product coordinates consumed by `distort`. -/
def stageBadEvent (A : CoveringFamily) (s : Finset (Fin A.length))
    (Q r : ℕ) (hQ : Q ≠ 0) :
    Set (ZMod (partialPeriod Q r) × StageCoordinate Q r) :=
  {z | ∃ i, ∃ hi : i ∈ stageIndices A s Q r,
    (stageCRTRingEquiv Q r).symm z ∈
      congruenceClass (partialPeriod Q (r + 1)) (A.get i).modulus
        (newModulus_dvd_partialPeriod_succ hQ
          ((mem_stageIndices_iff.mp hi).2))
        (A.get i).residue}

/-- The same stage union in the actual cyclic stage space. -/
def stageBadSet (A : CoveringFamily) (s : Finset (Fin A.length))
    (Q r : ℕ) (hQ : Q ≠ 0) : Set (ZMod (partialPeriod Q (r + 1))) :=
  (stageCRTRingEquiv Q r).symm '' stageBadEvent A s Q r hQ

lemma stageBadEvent_image (A : CoveringFamily)
    (s : Finset (Fin A.length)) (Q r : ℕ) (hQ : Q ≠ 0) :
    stageCRTRingEquiv Q r '' stageBadSet A s Q r hQ =
      stageBadEvent A s Q r hQ := by
  rw [stageBadSet]
  exact Equiv.image_symm_image _ _

/-! ## Recursive distorted distribution -/

/-- The uniform probability on `ZMod 1`, used before any prime coordinate
has been exposed. -/
def initialStageDistribution : FiniteProbability (ZMod 1) where
  weight _ := 1
  weight_nonneg _ := by norm_num
  sum_weight := by simp [ZMod.card]

/-- The recursive distorted measure on the successively exposed cyclic
groups.  At each transition it is first constructed in CRT product
coordinates and then transported back to the actual residue ring. -/
def stageDistribution (A : CoveringFamily)
    (s : Finset (Fin A.length)) (Q : ℕ) (hQ : Q ≠ 0) :
    (r : ℕ) → FiniteProbability (ZMod (partialPeriod Q r))
  | 0 => initialStageDistribution
  | r + 1 =>
      (distort (stageDistribution A s Q hQ r)
          (stageBadEvent A s Q r hQ) (distortionDelta (r + 1))
          (distortionDelta_nonneg (r + 1))
          (distortionDelta_le_half (r + 1))).mapEquiv
        (stageCRTRingEquiv Q r).toEquiv.symm

@[simp] lemma stageDistribution_zero (A : CoveringFamily)
    (s : Finset (Fin A.length)) (Q : ℕ) (hQ : Q ≠ 0) :
    stageDistribution A s Q hQ 0 = initialStageDistribution := rfl

@[simp] lemma stageDistribution_succ_weight (A : CoveringFamily)
    (s : Finset (Fin A.length)) (Q r : ℕ) (hQ : Q ≠ 0)
    (x : ZMod (partialPeriod Q (r + 1))) :
    (stageDistribution A s Q hQ (r + 1)).weight x =
      distortWeight (stageDistribution A s Q hQ r)
        (stageBadEvent A s Q r hQ) (distortionDelta (r + 1))
        (stageCRTRingEquiv Q r x) := rfl

/-- Exact mass conservation on every old-coordinate fibre. -/
lemma stageDistribution_fiber_conservation (A : CoveringFamily)
    (s : Finset (Fin A.length)) (Q r : ℕ) (hQ : Q ≠ 0)
    (x : ZMod (partialPeriod Q r)) :
    ∑ y : StageCoordinate Q r,
      (stageDistribution A s Q hQ (r + 1)).weight
        ((stageCRTRingEquiv Q r).symm (x, y)) =
      (stageDistribution A s Q hQ r).weight x := by
  simpa using distort_fiber_conservation
    (stageDistribution A s Q hQ r) (stageBadEvent A s Q r hQ)
      (distortionDelta (r + 1)) (distortionDelta_nonneg (r + 1))
      (distortionDelta_le_half (r + 1)) x

/-- Events depending only on the old coordinate have exactly invariant mass
under a stage update. -/
lemma stageDistribution_oldEvent_invariant (A : CoveringFamily)
    (s : Finset (Fin A.length)) (Q r : ℕ) (hQ : Q ≠ 0)
    (S : Set (ZMod (partialPeriod Q r))) :
    (stageDistribution A s Q hQ (r + 1)).mass
        {x | (stageCRTRingEquiv Q r x).1 ∈ S} =
    (stageDistribution A s Q hQ r).mass S := by
  classical
  change
    ((distort (stageDistribution A s Q hQ r)
      (stageBadEvent A s Q r hQ) (distortionDelta (r + 1))
      (distortionDelta_nonneg (r + 1))
      (distortionDelta_le_half (r + 1))).mapEquiv
        (stageCRTRingEquiv Q r).toEquiv.symm).mass
          {x | (stageCRTRingEquiv Q r x).1 ∈ S} = _
  rw [FiniteProbability.mapEquiv_mass]
  have hpre :
      (stageCRTRingEquiv Q r).symm ⁻¹'
          {x | (stageCRTRingEquiv Q r x).1 ∈ S} =
        {z | z.1 ∈ S} := by
    ext z
    change
      (stageCRTRingEquiv Q r ((stageCRTRingEquiv Q r).symm z)).1 ∈ S ↔
        z.1 ∈ S
    rw [(stageCRTRingEquiv Q r).apply_symm_apply]
  calc
    (distort (stageDistribution A s Q hQ r)
        (stageBadEvent A s Q r hQ) (distortionDelta (r + 1))
        (distortionDelta_nonneg (r + 1))
        (distortionDelta_le_half (r + 1))).mass
          ((stageCRTRingEquiv Q r).symm ⁻¹'
            {x | (stageCRTRingEquiv Q r x).1 ∈ S}) =
      (distort (stageDistribution A s Q hQ r)
        (stageBadEvent A s Q r hQ) (distortionDelta (r + 1))
        (distortionDelta_nonneg (r + 1))
        (distortionDelta_le_half (r + 1))).mass {z | z.1 ∈ S} :=
      congrArg _ hpre
    _ = (stageDistribution A s Q hQ r).mass S := by
      unfold FiniteProbability.mass
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro x hx
      by_cases hS : x ∈ S
      · simp only [Set.mem_setOf_eq, hS, ↓reduceIte]
        exact distort_fiber_conservation
          (stageDistribution A s Q hQ r) (stageBadEvent A s Q r hQ)
          (distortionDelta (r + 1)) (distortionDelta_nonneg (r + 1))
          (distortionDelta_le_half (r + 1)) x
      · simp [hS]

/-! ## Stage costs, survival, and the normalized quantity `f` -/

/-- Actual probability mass left on the bad set immediately after a stage
has been distorted. -/
def stageCost (A : CoveringFamily) (s : Finset (Fin A.length))
    (Q r : ℕ) (hQ : Q ≠ 0) : ℝ :=
  (stageDistribution A s Q hQ (r + 1)).mass (stageBadSet A s Q r hQ)

lemma stageCost_eq_product_mass (A : CoveringFamily)
    (s : Finset (Fin A.length)) (Q r : ℕ) (hQ : Q ≠ 0) :
    stageCost A s Q r hQ =
      (distort (stageDistribution A s Q hQ r)
        (stageBadEvent A s Q r hQ) (distortionDelta (r + 1))
        (distortionDelta_nonneg (r + 1))
        (distortionDelta_le_half (r + 1))).mass
          (stageBadEvent A s Q r hQ) := by
  rw [stageCost, stageBadSet]
  change
    ((distort (stageDistribution A s Q hQ r)
      (stageBadEvent A s Q r hQ) (distortionDelta (r + 1))
      (distortionDelta_nonneg (r + 1))
      (distortionDelta_le_half (r + 1))).mapEquiv
        (stageCRTRingEquiv Q r).toEquiv.symm).mass
          ((stageCRTRingEquiv Q r).symm ''
            stageBadEvent A s Q r hQ) = _
  rw [FiniteProbability.mapEquiv_mass]
  congr 1
  ext z
  simp

/-- The first-moment upper bound for the actual stage cost, including the
three zero-distortion stages. -/
lemma stageCost_le_firstMoment (A : CoveringFamily)
    (s : Finset (Fin A.length)) (Q r : ℕ) (hQ : Q ≠ 0) :
    stageCost A s Q r hQ ≤
      firstMoment (stageDistribution A s Q hQ r)
        (stageBadEvent A s Q r hQ) := by
  rw [stageCost_eq_product_mass]
  exact stage_cost_first_le _ _ _ (distortionDelta_nonneg _)
    (distortionDelta_le_half _)

/-- For positive distortion, the usual minimum of first- and second-moment
bounds controls the actual stage cost. -/
lemma stageCost_le_moments (A : CoveringFamily)
    (s : Finset (Fin A.length)) (Q r : ℕ) (hQ : Q ≠ 0)
    (hr : 3 < r + 1) :
    stageCost A s Q r hQ ≤
      min (firstMoment (stageDistribution A s Q hQ r)
          (stageBadEvent A s Q r hQ))
        (secondMoment (stageDistribution A s Q hQ r)
          (stageBadEvent A s Q r hQ) /
            (4 * distortionDelta (r + 1) *
              (1 - distortionDelta (r + 1)))) := by
  rw [stageCost_eq_product_mass]
  exact stage_cost_le _ _
    (by rw [distortionDelta_of_three_lt hr]; norm_num)
    (distortionDelta_le_half _)

/-- Remaining probability budget after the first `n` stage costs. -/
def stageSurvival (A : CoveringFamily) (s : Finset (Fin A.length))
    (Q n : ℕ) (hQ : Q ≠ 0) : ℝ :=
  1 - ∑ r ∈ Finset.range n, stageCost A s Q r hQ

@[simp] lemma stageSurvival_zero (A : CoveringFamily)
    (s : Finset (Fin A.length)) (Q : ℕ) (hQ : Q ≠ 0) :
    stageSurvival A s Q 0 hQ = 1 := by simp [stageSurvival]

lemma stageSurvival_succ (A : CoveringFamily)
    (s : Finset (Fin A.length)) (Q n : ℕ) (hQ : Q ≠ 0) :
    stageSurvival A s Q (n + 1) hQ =
      stageSurvival A s Q n hQ - stageCost A s Q n hQ := by
  simp only [stageSurvival, Finset.sum_range_succ]
  ring

/-- The Euler-product factor introduced at prime stage `r`. -/
def stageGrowthFactor (r : ℕ) : ℝ :=
  1 + ((3 * stagePrime r - 1 : ℕ) : ℝ) /
    ((1 - distortionDelta r) * ((stagePrime r - 1 : ℕ) : ℝ) ^ 2)

/-- The product occurring in the normalized recurrence after a cutoff. -/
def stageGrowthProduct (r₀ n : ℕ) : ℝ :=
  ∏ r ∈ Finset.Ioc r₀ n, stageGrowthFactor r

@[simp] lemma stageGrowthProduct_self (r₀ : ℕ) :
    stageGrowthProduct r₀ r₀ = 1 := by simp [stageGrowthProduct]

lemma stageGrowthProduct_succ {r₀ n : ℕ} (h : r₀ ≤ n) :
    stageGrowthProduct r₀ (n + 1) =
      stageGrowthProduct r₀ n * stageGrowthFactor (n + 1) := by
  rw [stageGrowthProduct, stageGrowthProduct,
    Finset.prod_Ioc_succ_top h]

/-- The normalized reciprocal-survival quantity used by the termination
certificate. -/
def stageF (κ : ℝ) (A : CoveringFamily) (s : Finset (Fin A.length))
    (Q r₀ n : ℕ) (hQ : Q ≠ 0) : ℝ :=
  κ / stageSurvival A s Q n hQ * stageGrowthProduct r₀ n

lemma stageF_at_cutoff (κ : ℝ) (A : CoveringFamily)
    (s : Finset (Fin A.length)) (Q r₀ : ℕ) (hQ : Q ≠ 0) :
    stageF κ A s Q r₀ r₀ hQ = κ / stageSurvival A s Q r₀ hQ := by
  simp [stageF]

/-! ## Positive survival produces an uncovered residue -/

/-- The union of all bad events processed through stage `n`.  The old union
is pulled back along the first CRT projection before the new event is added.
This recursive representation is what makes the probability accounting
definitionally follow the stage law. -/
def processedStageBadSet (A : CoveringFamily)
    (s : Finset (Fin A.length)) (Q : ℕ) (hQ : Q ≠ 0) :
    (n : ℕ) → Set (ZMod (partialPeriod Q n))
  | 0 => ∅
  | r + 1 =>
      {x | (stageCRTRingEquiv Q r x).1 ∈
        processedStageBadSet A s Q hQ r} ∪ stageBadSet A s Q r hQ

@[simp] lemma processedStageBadSet_zero (A : CoveringFamily)
    (s : Finset (Fin A.length)) (Q : ℕ) (hQ : Q ≠ 0) :
    processedStageBadSet A s Q hQ 0 = ∅ := rfl

@[simp] lemma processedStageBadSet_succ (A : CoveringFamily)
    (s : Finset (Fin A.length)) (Q r : ℕ) (hQ : Q ≠ 0) :
    processedStageBadSet A s Q hQ (r + 1) =
      {x | (stageCRTRingEquiv Q r x).1 ∈
        processedStageBadSet A s Q hQ r} ∪
          stageBadSet A s Q r hQ := rfl

/-- The final mass of the processed union is at most the sum of the actual
stage costs. -/
theorem processedStageBadSet_mass_le_cost_sum
    (A : CoveringFamily) (s : Finset (Fin A.length))
    (Q : ℕ) (hQ : Q ≠ 0) : ∀ n : ℕ,
    (stageDistribution A s Q hQ n).mass
        (processedStageBadSet A s Q hQ n) ≤
      ∑ r ∈ Finset.range n, stageCost A s Q r hQ := by
  intro n
  induction n with
  | zero =>
      rw [processedStageBadSet_zero, FiniteProbability.mass_empty]
      simp
  | succ n ih =>
      calc
        (stageDistribution A s Q hQ (n + 1)).mass
            (processedStageBadSet A s Q hQ (n + 1)) ≤
            (stageDistribution A s Q hQ (n + 1)).mass
                {x | (stageCRTRingEquiv Q n x).1 ∈
                  processedStageBadSet A s Q hQ n} +
              (stageDistribution A s Q hQ (n + 1)).mass
                (stageBadSet A s Q n hQ) := by
          rw [processedStageBadSet_succ]
          exact FiniteProbability.mass_union_le _ _ _
        _ = (stageDistribution A s Q hQ n).mass
              (processedStageBadSet A s Q hQ n) +
                stageCost A s Q n hQ := by
          rw [stageDistribution_oldEvent_invariant]
          rfl
        _ ≤ (∑ r ∈ Finset.range n, stageCost A s Q r hQ) +
              stageCost A s Q n hQ := add_le_add ih le_rfl
        _ = ∑ r ∈ Finset.range (n + 1), stageCost A s Q r hQ := by
          rw [Finset.sum_range_succ]

/-- An integer lying in a selected class newly exposed at transition `r+1`
belongs to that transition's cyclic bad set. -/
lemma intCast_mem_stageBadSet_of_isNewModulus
    (A : CoveringFamily) (s : Finset (Fin A.length))
    (Q r : ℕ) (hQ : Q ≠ 0) (i : Fin A.length) (hi : i ∈ s)
    (hnew : IsNewModulus Q (r + 1) (A.get i).modulus)
    {z : ℤ} (hz : z ≡ (A.get i).residue [ZMOD (A.get i).modulus]) :
    (z : ZMod (partialPeriod Q (r + 1))) ∈ stageBadSet A s Q r hQ := by
  rw [stageBadSet]
  refine ⟨stageCRTRingEquiv Q r
    (z : ZMod (partialPeriod Q (r + 1))), ?_, by simp⟩
  refine ⟨i, mem_stageIndices_iff.mpr ⟨hi, hnew⟩, ?_⟩
  simpa using (intCast_mem_congruenceClass
    (newModulus_dvd_partialPeriod_succ hQ hnew)
    z (A.get i).residue).2 hz

/-- Once an integer representative belongs to the processed union, its
canonical lift belongs after the next CRT stage as well. -/
lemma intCast_mem_processedStageBadSet_succ
    (A : CoveringFamily) (s : Finset (Fin A.length))
    (Q r : ℕ) (hQ : Q ≠ 0) {z : ℤ}
    (hz : (z : ZMod (partialPeriod Q r)) ∈
      processedStageBadSet A s Q hQ r) :
    (z : ZMod (partialPeriod Q (r + 1))) ∈
      processedStageBadSet A s Q hQ (r + 1) := by
  rw [processedStageBadSet_succ]
  left
  simpa [stageCRTRingEquiv, stageCRTInput] using hz

/-- A selected congruence class remains in the processed union at every
later stage. -/
lemma intCast_mem_processedStageBadSet_of_isNewModulus
    (A : CoveringFamily) (s : Finset (Fin A.length))
    (Q : ℕ) (hQ : Q ≠ 0) (i : Fin A.length) (hi : i ∈ s)
    {t n : ℕ} (ht : 0 < t) (htn : t ≤ n)
    (hnew : IsNewModulus Q t (A.get i).modulus)
    {z : ℤ} (hz : z ≡ (A.get i).residue [ZMOD (A.get i).modulus]) :
    (z : ZMod (partialPeriod Q n)) ∈ processedStageBadSet A s Q hQ n := by
  have ht_eq : t = (t - 1) + 1 := by omega
  have hbase :
      (z : ZMod (partialPeriod Q t)) ∈ processedStageBadSet A s Q hQ t := by
    rw [ht_eq, processedStageBadSet_succ]
    right
    have hnew' : IsNewModulus Q ((t - 1) + 1) (A.get i).modulus := by
      rw [← ht_eq]
      exact hnew
    exact intCast_mem_stageBadSet_of_isNewModulus A s Q (t - 1) hQ i hi
      hnew' hz
  exact Nat.le_induction hbase
    (fun r _ ihr => intCast_mem_processedStageBadSet_succ A s Q r hQ ihr)
    n htn

/-- Positive survival at the finite horizon produces an integer outside all
selected congruence classes.  In particular, the selected occurrences do
not cover the integers. -/
theorem positive_survival_at_horizon_not_coversIndices
    (A : CoveringFamily) (s : Finset (Fin A.length))
    (hsurv : 0 < stageSurvival A s (commonPeriod A)
      (stageHorizon (commonPeriod A)) (commonPeriod_pos A).ne') :
    ¬ CoversIndices A s := by
  let Q := commonPeriod A
  let n := stageHorizon Q
  let hQ : Q ≠ 0 := (commonPeriod_pos A).ne'
  let μ := stageDistribution A s Q hQ n
  let U := processedStageBadSet A s Q hQ n
  have hcost : μ.mass U ≤
      ∑ r ∈ Finset.range n, stageCost A s Q r hQ :=
    processedStageBadSet_mass_le_cost_sum A s Q hQ n
  have hsum : (∑ r ∈ Finset.range n, stageCost A s Q r hQ) < 1 := by
    change 0 < 1 - ∑ r ∈ Finset.range n, stageCost A s Q r hQ at hsurv
    linarith
  have hex : ∃ x : ZMod (partialPeriod Q n), x ∉ U := by
    by_contra h
    push_neg at h
    have hU : U = Set.univ := Set.eq_univ_of_forall h
    have hm : μ.mass U = 1 := by rw [hU, FiniteProbability.mass_univ]
    linarith
  obtain ⟨x, hx⟩ := hex
  intro hcover
  obtain ⟨i, hi, hxi⟩ := hcover (x.val : ℤ)
  let t := primeStage (largestPrimeFactor (A.get i).modulus)
  have htdata := divisor_processed_by_horizon_at_largestPrimeStage hQ
    (by simpa [Q] using modulus_dvd_commonPeriod A i)
    (A.get i).one_lt_modulus
  have htpos : 0 < t := primeStage_pos _
  have ht : t ≤ n := by simpa [t, n, Q] using htdata.1
  have htnew : IsNewModulus Q t (A.get i).modulus := by
    simpa [t, Q] using htdata.2
  have hmem :
      ((x.val : ℕ) : ZMod (partialPeriod Q n)) ∈ U := by
    simpa using
      (intCast_mem_processedStageBadSet_of_isNewModulus A s Q hQ i hi
        htpos ht htnew hxi)
  have hxval : ((x.val : ℕ) : ZMod (partialPeriod Q n)) = x :=
    ZMod.natCast_zmod_val x
  exact hx (hxval ▸ hmem)

end

end Erdos586
