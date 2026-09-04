/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex, Boris Alexeev
-/
import ErdosProblems.Erdos228.EdgeWalk

/-!
# Iterating the projected Rademacher edge walk

This file completes the deterministic iteration of the one-step score
inequality in `EdgeWalk`.  The walk uses step size `1 / q`, runs for
`5 * q ^ 2` steps, and freezes every coordinate or discrepancy row within
`delta` of its boundary.  Monotonicity of the frozen sets and the terminal
exponential potential force at least half of the coordinates to reach a
`delta`-neighbourhood of the cube boundary.  The compact endpoint then
removes `delta`.
-/

open Real Set
open scoped BigOperators

noncomputable section

namespace Erdos228.EdgeWalk

open Erdos228.Discrepancy Erdos228.ProjectionWalk

universe u v

variable {I : Type u} {J : Type v} [Fintype I] [Fintype J]
variable [DecidableEq I] [DecidableEq J]

/-! ## A deterministic choice of the next sign vector -/

/-- A sign vector witnessing the one-step score inequality. -/
def edgeChoice (gamma delta : ℝ) (t : ℕ)
    (v : J → I → ℝ) (x₀ : I → ℝ) (c : J → ℝ)
    (x : WalkSpace I) : I → ℝ :=
  Classical.choose (exists_sign_edgeScore_step gamma delta t v x₀ c x)

theorem edgeChoice_isSign (gamma delta : ℝ) (t : ℕ)
    (v : J → I → ℝ) (x₀ : I → ℝ) (c : J → ℝ)
    (x : WalkSpace I) :
    ∀ i, |edgeChoice gamma delta t v x₀ c x i| = 1 :=
  (Classical.choose_spec
    (exists_sign_edgeScore_step gamma delta t v x₀ c x)).1

theorem edgeChoice_score (gamma delta : ℝ) (t : ℕ)
    (v : J → I → ℝ) (x₀ : I → ℝ) (c : J → ℝ)
    (x : WalkSpace I) :
    edgeScore gamma t v x₀ c x +
        gamma ^ 2 * Module.finrank ℝ (edgeSubspace delta v x₀ c x) ≤
      edgeScore gamma (t + 1) v x₀ c
        (edgeStep delta gamma v x₀ c x
          (edgeChoice gamma delta t v x₀ c x)) :=
  (Classical.choose_spec
    (exists_sign_edgeScore_step gamma delta t v x₀ c x)).2

/-- The deterministic edge walk obtained by repeatedly taking `edgeChoice`. -/
def edgeWalk (delta gamma : ℝ) (v : J → I → ℝ)
    (x₀ : I → ℝ) (c : J → ℝ) : ℕ → WalkSpace I
  | 0 => toWalk x₀
  | t + 1 => edgeStep delta gamma v x₀ c (edgeWalk delta gamma v x₀ c t)
      (edgeChoice gamma delta t v x₀ c (edgeWalk delta gamma v x₀ c t))

@[simp] theorem edgeWalk_zero (delta gamma : ℝ) (v : J → I → ℝ)
    (x₀ : I → ℝ) (c : J → ℝ) :
    edgeWalk delta gamma v x₀ c 0 = toWalk x₀ := rfl

@[simp] theorem edgeWalk_succ (delta gamma : ℝ) (v : J → I → ℝ)
    (x₀ : I → ℝ) (c : J → ℝ) (t : ℕ) :
    edgeWalk delta gamma v x₀ c (t + 1) =
      edgeStep delta gamma v x₀ c (edgeWalk delta gamma v x₀ c t)
        (edgeChoice gamma delta t v x₀ c (edgeWalk delta gamma v x₀ c t)) := rfl

theorem edgeWalk_score_step (delta gamma : ℝ) (v : J → I → ℝ)
    (x₀ : I → ℝ) (c : J → ℝ) (t : ℕ) :
    edgeScore gamma t v x₀ c (edgeWalk delta gamma v x₀ c t) +
        gamma ^ 2 * Module.finrank ℝ
          (edgeSubspace delta v x₀ c (edgeWalk delta gamma v x₀ c t)) ≤
      edgeScore gamma (t + 1) v x₀ c
        (edgeWalk delta gamma v x₀ c (t + 1)) := by
  simpa only [edgeWalk_succ] using
    edgeChoice_score gamma delta t v x₀ c (edgeWalk delta gamma v x₀ c t)

/-! ## Cube and discrepancy invariants -/

theorem abs_apply_le_norm_walkSpace (x : WalkSpace I) (i : I) :
    |x i| ≤ ‖x‖ := by
  have hi : x i ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [norm_walkSpace_sq]
    exact Finset.single_le_sum (fun j _ ↦ sq_nonneg (x j)) (Finset.mem_univ i)
  nlinarith [sq_abs (x i), abs_nonneg (x i), norm_nonneg x]

theorem abs_edgeIncrement_le_sqrt_card
    (delta : ℝ) (v : J → I → ℝ) (x₀ : I → ℝ)
    (c : J → ℝ) (x : WalkSpace I) (omega : I → ℝ)
    (homega : ∀ i, |omega i| = 1) (i : I) :
    |edgeIncrement delta v x₀ c x omega i| ≤
      sqrt (Fintype.card I) := by
  exact (abs_apply_le_norm_walkSpace _ i).trans
    ((norm_edgeIncrement_le delta v x₀ c x omega).trans
      (norm_sampleVector_le_sqrt_card homega))

theorem abs_inner_edgeIncrement_le_sqrt_card
    (delta : ℝ) (v : J → I → ℝ) (x₀ : I → ℝ)
    (c : J → ℝ) (x : WalkSpace I) (omega : I → ℝ)
    (homega : ∀ i, |omega i| = 1) (j : J) :
    |inner ℝ (normalizedConstraint (v j))
        (edgeIncrement delta v x₀ c x omega)| ≤
      sqrt (Fintype.card I) := by
  calc
    |inner ℝ (normalizedConstraint (v j))
        (edgeIncrement delta v x₀ c x omega)| ≤
        ‖normalizedConstraint (v j)‖ *
          ‖edgeIncrement delta v x₀ c x omega‖ :=
      abs_real_inner_le_norm _ _
    _ ≤ 1 * sqrt (Fintype.card I) := by
      gcongr
      · exact norm_normalizedConstraint_le_one (v j)
      · exact (norm_edgeIncrement_le delta v x₀ c x omega).trans
          (norm_sampleVector_le_sqrt_card homega)
    _ = sqrt (Fintype.card I) := one_mul _

theorem edgeStep_inCube
    (delta gamma : ℝ) (v : J → I → ℝ) (x₀ : I → ℝ)
    (c : J → ℝ) (x : WalkSpace I) (omega : I → ℝ)
    (hx : InCube x) (homega : ∀ i, |omega i| = 1)
    (hgamma : 0 ≤ gamma)
    (hdelta : delta = gamma * sqrt (Fintype.card I)) :
    InCube (edgeStep delta gamma v x₀ c x omega) := by
  intro i
  by_cases hi : i ∈ activeCoordinates delta x
  · rw [edgeStep]
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
      edgeIncrement_apply_eq_zero_of_active delta v x₀ c x omega hi,
      mul_zero, add_zero]
    exact hx i
  · have hxi : |x i| < 1 - delta := by
      simpa only [mem_activeCoordinates, not_le] using hi
    have hinc := abs_edgeIncrement_le_sqrt_card
      delta v x₀ c x omega homega i
    rw [edgeStep]
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    calc
      |x i + gamma * edgeIncrement delta v x₀ c x omega i| ≤
          |x i| + |gamma * edgeIncrement delta v x₀ c x omega i| :=
        abs_add_le _ _
      _ = |x i| + gamma * |edgeIncrement delta v x₀ c x omega i| := by
        rw [abs_mul, abs_of_nonneg hgamma]
      _ ≤ |x i| + gamma * sqrt (Fintype.card I) := by gcongr
      _ ≤ 1 := by rw [← hdelta]; linarith

theorem edgeStep_normalizedDiscrepancy_le
    (delta gamma : ℝ) (v : J → I → ℝ) (x₀ : I → ℝ)
    (c : J → ℝ) (x : WalkSpace I) (omega : I → ℝ)
    (hx : ∀ j, |normalizedDiscrepancy (v j) x₀ x| ≤ c j)
    (homega : ∀ i, |omega i| = 1) (hgamma : 0 ≤ gamma)
    (hdelta : delta = gamma * sqrt (Fintype.card I)) :
    ∀ j, |normalizedDiscrepancy (v j) x₀
      (edgeStep delta gamma v x₀ c x omega)| ≤ c j := by
  intro j
  by_cases hv : l2Norm (v j) = 0
  · simpa [normalizedDiscrepancy, normalizedConstraint, hv] using hx j
  by_cases hj : j ∈ activeDiscrepancies delta v x₀ c x
  · rw [normalizedDiscrepancy_edgeStep,
      inner_edgeIncrement_eq_zero_of_active delta v x₀ c x omega hj,
      mul_zero, add_zero]
    exact hx j
  · have hvpos : 0 < l2Norm (v j) :=
      lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hv)
    have hy : |normalizedDiscrepancy (v j) x₀ x| < c j - delta := by
      simpa only [mem_activeDiscrepancies, hvpos, true_and, not_le] using hj
    have hinc := abs_inner_edgeIncrement_le_sqrt_card
      delta v x₀ c x omega homega j
    rw [normalizedDiscrepancy_edgeStep]
    calc
      |normalizedDiscrepancy (v j) x₀ x + gamma *
          inner ℝ (normalizedConstraint (v j))
            (edgeIncrement delta v x₀ c x omega)| ≤
          |normalizedDiscrepancy (v j) x₀ x| +
            |gamma * inner ℝ (normalizedConstraint (v j))
              (edgeIncrement delta v x₀ c x omega)| := abs_add_le _ _
      _ = |normalizedDiscrepancy (v j) x₀ x| + gamma *
            |inner ℝ (normalizedConstraint (v j))
              (edgeIncrement delta v x₀ c x omega)| := by
        rw [abs_mul, abs_of_nonneg hgamma]
      _ ≤ |normalizedDiscrepancy (v j) x₀ x| +
            gamma * sqrt (Fintype.card I) := by gcongr
      _ ≤ c j := by rw [← hdelta]; linarith

theorem edgeWalk_inCube
    (delta gamma : ℝ) (v : J → I → ℝ) (x₀ : I → ℝ)
    (c : J → ℝ) (hx₀ : InCube x₀) (hgamma : 0 ≤ gamma)
    (hdelta : delta = gamma * sqrt (Fintype.card I)) :
    ∀ t, InCube (edgeWalk delta gamma v x₀ c t) := by
  intro t
  induction t with
  | zero => simpa [edgeWalk] using hx₀
  | succ t ht =>
      rw [edgeWalk_succ]
      exact edgeStep_inCube delta gamma v x₀ c _ _ ht
        (edgeChoice_isSign gamma delta t v x₀ c _) hgamma hdelta

theorem edgeWalk_normalizedDiscrepancy_le
    (delta gamma : ℝ) (v : J → I → ℝ) (x₀ : I → ℝ)
    (c : J → ℝ) (hc : ∀ j, 0 ≤ c j) (hgamma : 0 ≤ gamma)
    (hdelta : delta = gamma * sqrt (Fintype.card I)) :
    ∀ t j, |normalizedDiscrepancy (v j) x₀
      (edgeWalk delta gamma v x₀ c t)| ≤ c j := by
  intro t
  induction t with
  | zero =>
      intro j
      simpa [edgeWalk, normalizedDiscrepancy] using hc j
  | succ t ht =>
      rw [edgeWalk_succ]
      exact edgeStep_normalizedDiscrepancy_le delta gamma v x₀ c _ _ ht
        (edgeChoice_isSign gamma delta t v x₀ c _) hgamma hdelta

/-! ## Monotonicity of the active sets -/

theorem activeCoordinates_mono_edgeStep
    (delta gamma : ℝ) (v : J → I → ℝ) (x₀ : I → ℝ)
    (c : J → ℝ) (x : WalkSpace I) (omega : I → ℝ) :
    activeCoordinates delta x ⊆
      activeCoordinates delta (edgeStep delta gamma v x₀ c x omega) := by
  intro i hi
  rw [mem_activeCoordinates]
  rw [edgeStep]
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
    edgeIncrement_apply_eq_zero_of_active delta v x₀ c x omega hi,
    mul_zero, add_zero]
  exact mem_activeCoordinates.mp hi

theorem activeDiscrepancies_mono_edgeStep
    (delta gamma : ℝ) (v : J → I → ℝ) (x₀ : I → ℝ)
    (c : J → ℝ) (x : WalkSpace I) (omega : I → ℝ) :
    activeDiscrepancies delta v x₀ c x ⊆
      activeDiscrepancies delta v x₀ c
        (edgeStep delta gamma v x₀ c x omega) := by
  intro j hj
  rw [mem_activeDiscrepancies]
  have hj' := (mem_activeDiscrepancies.mp hj)
  refine ⟨hj'.1, ?_⟩
  rw [normalizedDiscrepancy_edgeStep,
    inner_edgeIncrement_eq_zero_of_active delta v x₀ c x omega hj,
    mul_zero, add_zero]
  exact hj'.2

theorem activeCoordinates_mono_edgeWalk
    (delta gamma : ℝ) (v : J → I → ℝ) (x₀ : I → ℝ)
    (c : J → ℝ) {s t : ℕ} (hst : s ≤ t) :
    activeCoordinates delta (edgeWalk delta gamma v x₀ c s) ⊆
      activeCoordinates delta (edgeWalk delta gamma v x₀ c t) := by
  induction t, hst using Nat.le_induction with
  | base => exact Finset.Subset.rfl
  | succ t hst ih =>
      exact ih.trans (by
        rw [edgeWalk_succ]
        exact activeCoordinates_mono_edgeStep delta gamma v x₀ c _ _)

theorem activeDiscrepancies_mono_edgeWalk
    (delta gamma : ℝ) (v : J → I → ℝ) (x₀ : I → ℝ)
    (c : J → ℝ) {s t : ℕ} (hst : s ≤ t) :
    activeDiscrepancies delta v x₀ c (edgeWalk delta gamma v x₀ c s) ⊆
      activeDiscrepancies delta v x₀ c (edgeWalk delta gamma v x₀ c t) := by
  induction t, hst using Nat.le_induction with
  | base => exact Finset.Subset.rfl
  | succ t hst ih =>
      exact ih.trans (by
        rw [edgeWalk_succ]
        exact activeDiscrepancies_mono_edgeStep delta gamma v x₀ c _ _)

/-! ## The terminal potential -/

/-- A row within `delta` of its discrepancy boundary contributes at least
one unit to the compensated potential, throughout the first five units of
quadratic time.  The small-`a` case uses both signs of the potential; the
large-`a` case uses the sign agreeing with `y`. -/
theorem one_le_rowPotential_of_near_boundary
    (gamma delta : ℝ) (t : ℕ) (a y : ℝ)
    (ha : 0 ≤ a) (hdelta : 0 ≤ delta) (hdeltaSmall : delta ≤ 1 / 4)
    (htime : gamma ^ 2 * (t : ℝ) ≤ 5)
    (hnear : a - delta ≤ |y|) :
    1 ≤ rowPotential gamma t a y := by
  let Q : ℝ := (a / 5) ^ 2 * gamma ^ 2 * (t : ℝ) / 2
  have hQ : Q ≤ a ^ 2 / 10 := by
    have hmul := mul_le_mul_of_nonneg_left htime
      (div_nonneg (sq_nonneg (a / 5)) (by norm_num : (0 : ℝ) ≤ 2))
    dsimp only [Q]
    nlinarith
  by_cases hlarge : 16 * delta ≤ 3 * a
  · have hprod : 16 * a * delta ≤ 3 * a ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hlarge ha]
    by_cases hy : 0 ≤ y
    · have hay : a - delta ≤ y := by simpa [abs_of_nonneg hy] using hnear
      have haymul : a * (a - delta) ≤ a * y :=
        mul_le_mul_of_nonneg_left hay ha
      have hexponent :
          0 ≤ -a ^ 2 / 16 + a / 5 * y - Q := by
        nlinarith
      have hone : 1 ≤ signedRowPotential 1 gamma t a y := by
        rw [signedRowPotential, entropyWeight, ← exp_add]
        have heq : -a ^ 2 / 16 +
            (1 * (a / 5) * y - (a / 5) ^ 2 * gamma ^ 2 * (t : ℝ) / 2) =
            -a ^ 2 / 16 + a / 5 * y - Q := by
          dsimp only [Q]
          ring
        rw [heq]
        simpa only [exp_zero] using exp_le_exp.mpr hexponent
      exact hone.trans (le_add_of_nonneg_right
        (signedRowPotential_nonneg (-1) gamma t a y))
    · have hy' : y ≤ 0 := le_of_not_ge hy
      have hay : a - delta ≤ -y := by simpa [abs_of_nonpos hy'] using hnear
      have haymul : a * (a - delta) ≤ a * (-y) :=
        mul_le_mul_of_nonneg_left hay ha
      have hexponent :
          0 ≤ -a ^ 2 / 16 + (-1) * (a / 5) * y - Q := by
        nlinarith
      have hone : 1 ≤ signedRowPotential (-1) gamma t a y := by
        rw [signedRowPotential, entropyWeight, ← exp_add]
        have heq : -a ^ 2 / 16 +
            ((-1) * (a / 5) * y - (a / 5) ^ 2 * gamma ^ 2 * (t : ℝ) / 2) =
            -a ^ 2 / 16 + (-1) * (a / 5) * y - Q := by
          dsimp only [Q]
          ring
        rw [heq]
        simpa only [exp_zero] using exp_le_exp.mpr hexponent
      exact hone.trans (le_add_of_nonneg_left
        (signedRowPotential_nonneg 1 gamma t a y))
  · have haUpper : a < 4 / 3 := by
      have : 3 * a < 16 * delta := lt_of_not_ge hlarge
      nlinarith
    have haSq : 13 * a ^ 2 / 80 ≤ 1 / 2 := by
      nlinarith [sq_nonneg (a - 4 / 3)]
    have hbase : -1 / 2 ≤ -a ^ 2 / 16 - Q := by
      nlinarith
    let z : ℝ := a / 5 * y
    let base : ℝ := -a ^ 2 / 16 - Q
    have hsum : 1 ≤ (1 + (base + z)) + (1 + (base - z)) := by
      dsimp only [base]
      nlinarith
    calc
      1 ≤ (1 + (base + z)) + (1 + (base - z)) := hsum
      _ ≤ exp (base + z) + exp (base - z) :=
        add_le_add (by simpa [add_comm] using add_one_le_exp (base + z))
          (by simpa [add_comm] using add_one_le_exp (base - z))
      _ = rowPotential gamma t a y := by
        unfold rowPotential signedRowPotential entropyWeight
        rw [← exp_add, ← exp_add]
        dsimp only [base, z, Q]
        congr 1 <;> ring_nf

/-! ## Accumulated score and the half-coordinate conclusion -/

theorem edgeWalk_score_sum
    (delta gamma : ℝ) (v : J → I → ℝ) (x₀ : I → ℝ)
    (c : J → ℝ) (t : ℕ) :
    edgeScore gamma 0 v x₀ c (toWalk x₀) +
        gamma ^ 2 * ∑ s ∈ Finset.range t,
          (Module.finrank ℝ
            (edgeSubspace delta v x₀ c (edgeWalk delta gamma v x₀ c s)) : ℝ) ≤
      edgeScore gamma t v x₀ c (edgeWalk delta gamma v x₀ c t) := by
  induction t with
  | zero => simp
  | succ t ht =>
      rw [Finset.sum_range_succ]
      calc
        edgeScore gamma 0 v x₀ c (toWalk x₀) + gamma ^ 2 *
            ((∑ s ∈ Finset.range t,
              (Module.finrank ℝ (edgeSubspace delta v x₀ c
                (edgeWalk delta gamma v x₀ c s)) : ℝ)) +
              (Module.finrank ℝ (edgeSubspace delta v x₀ c
                (edgeWalk delta gamma v x₀ c t)) : ℝ)) =
            (edgeScore gamma 0 v x₀ c (toWalk x₀) + gamma ^ 2 *
              ∑ s ∈ Finset.range t,
                (Module.finrank ℝ (edgeSubspace delta v x₀ c
                  (edgeWalk delta gamma v x₀ c s)) : ℝ)) +
              gamma ^ 2 * (Module.finrank ℝ (edgeSubspace delta v x₀ c
                (edgeWalk delta gamma v x₀ c t)) : ℝ) := by ring
        _ ≤ edgeScore gamma t v x₀ c (edgeWalk delta gamma v x₀ c t) +
              gamma ^ 2 * (Module.finrank ℝ (edgeSubspace delta v x₀ c
                (edgeWalk delta gamma v x₀ c t)) : ℝ) :=
          add_le_add ht (le_refl _)
        _ ≤ edgeScore gamma (t + 1) v x₀ c
              (edgeWalk delta gamma v x₀ c (t + 1)) :=
          edgeWalk_score_step delta gamma v x₀ c t

theorem card_le_finrank_add_active
    (delta : ℝ) (v : J → I → ℝ) (x₀ : I → ℝ) (c : J → ℝ)
    (x : WalkSpace I) :
    Fintype.card I ≤
      Module.finrank ℝ (edgeSubspace delta v x₀ c x) +
        (activeCoordinates delta x).card +
        (activeDiscrepancies delta v x₀ c x).card := by
  have h := card_sub_tight_card_le_finrank
    (fun j ↦ normalizedConstraint (v j))
    (activeCoordinates delta x) (activeDiscrepancies delta v x₀ c x)
  change Fintype.card I -
      ((activeCoordinates delta x).card +
        (activeDiscrepancies delta v x₀ c x).card) ≤
    Module.finrank ℝ (edgeSubspace delta v x₀ c x) at h
  omega

theorem card_activeDiscrepancies_le_potential
    (gamma delta : ℝ) (t : ℕ)
    (v : J → I → ℝ) (x₀ : I → ℝ) (c : J → ℝ) (x : WalkSpace I)
    (hc : ∀ j, 0 ≤ c j) (hdelta : 0 ≤ delta)
    (hdeltaSmall : delta ≤ 1 / 4)
    (htime : gamma ^ 2 * (t : ℝ) ≤ 5) :
    ((activeDiscrepancies delta v x₀ c x).card : ℝ) ≤
      discrepancyPotential gamma t v x₀ c x := by
  let A := activeDiscrepancies delta v x₀ c x
  calc
    (A.card : ℝ) = ∑ _j ∈ A, (1 : ℝ) := by simp [A]
    _ ≤ ∑ j ∈ A,
        rowPotential gamma t (c j) (normalizedDiscrepancy (v j) x₀ x) := by
      apply Finset.sum_le_sum
      intro j hj
      exact one_le_rowPotential_of_near_boundary gamma delta t (c j)
        (normalizedDiscrepancy (v j) x₀ x) (hc j) hdelta hdeltaSmall htime
        ((mem_activeDiscrepancies.mp hj).2)
    _ ≤ ∑ j,
        rowPotential gamma t (c j) (normalizedDiscrepancy (v j) x₀ x) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A)
        (fun j hj₁ hj₂ ↦ rowPotential_nonneg gamma t (c j)
          (normalizedDiscrepancy (v j) x₀ x))
    _ = discrepancyPotential gamma t v x₀ c x := rfl

theorem norm_sq_le_card_of_inCube (x : WalkSpace I) (hx : InCube x) :
    ‖x‖ ^ 2 ≤ Fintype.card I := by
  rw [norm_walkSpace_sq]
  calc
    ∑ i, x i ^ 2 ≤ ∑ _i : I, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      have hsq := mul_self_le_mul_self (abs_nonneg (x i)) (hx i)
      nlinarith [sq_abs (x i)]
    _ = Fintype.card I := by simp

/-- If the walk runs for exactly five units of quadratic time, its terminal
active-coordinate set contains at least half of all coordinates. -/
theorem edgeWalk_terminal_half
    (delta gamma : ℝ) (T : ℕ)
    (v : J → I → ℝ) (x₀ : I → ℝ) (c : J → ℝ)
    (hx₀ : InCube x₀) (hc : ∀ j, 0 ≤ c j)
    (hentropy : (∑ j, exp (-(c j) ^ 2 / 16)) ≤
      (Fintype.card I : ℝ) / 16)
    (hgamma : 0 ≤ gamma)
    (hdeltaEq : delta = gamma * sqrt (Fintype.card I))
    (hdelta : 0 ≤ delta) (hdeltaSmall : delta ≤ 1 / 4)
    (htime : gamma ^ 2 * (T : ℝ) = 5) :
    Fintype.card I ≤ 2 *
      (activeCoordinates delta (edgeWalk delta gamma v x₀ c T)).card := by
  let xT := edgeWalk delta gamma v x₀ c T
  let C := (activeCoordinates delta xT).card
  let D := (activeDiscrepancies delta v x₀ c xT).card
  let N : ℝ := Fintype.card I
  by_contra hhalf
  have hClt : 2 * C < Fintype.card I := by
    exact Nat.lt_of_not_ge hhalf
  have hNpos : 0 < N := by
    dsimp only [N]
    exact_mod_cast (lt_of_le_of_lt (Nat.zero_le (2 * C)) hClt)
  have hrank (s : ℕ) (hs : s ∈ Finset.range T) :
      N - C - D ≤
        (Module.finrank ℝ
          (edgeSubspace delta v x₀ c (edgeWalk delta gamma v x₀ c s)) : ℝ) := by
    have hsT : s ≤ T := Nat.le_of_lt (Finset.mem_range.mp hs)
    have hcoord := Finset.card_le_card
      (activeCoordinates_mono_edgeWalk delta gamma v x₀ c hsT)
    have hdisc := Finset.card_le_card
      (activeDiscrepancies_mono_edgeWalk delta gamma v x₀ c hsT)
    have hdim := card_le_finrank_add_active delta v x₀ c
      (edgeWalk delta gamma v x₀ c s)
    have hcoordR :
        ((activeCoordinates delta (edgeWalk delta gamma v x₀ c s)).card : ℝ) ≤ C := by
      exact_mod_cast hcoord
    have hdiscR :
        ((activeDiscrepancies delta v x₀ c
          (edgeWalk delta gamma v x₀ c s)).card : ℝ) ≤ D := by
      exact_mod_cast hdisc
    have hdimR : N ≤
        (Module.finrank ℝ
          (edgeSubspace delta v x₀ c (edgeWalk delta gamma v x₀ c s)) : ℝ) +
        (activeCoordinates delta (edgeWalk delta gamma v x₀ c s)).card +
        (activeDiscrepancies delta v x₀ c
          (edgeWalk delta gamma v x₀ c s)).card := by
      dsimp only [N]
      exact_mod_cast hdim
    linarith
  have hrankSum : (T : ℝ) * (N - C - D) ≤
      ∑ s ∈ Finset.range T,
        (Module.finrank ℝ
          (edgeSubspace delta v x₀ c (edgeWalk delta gamma v x₀ c s)) : ℝ) := by
    calc
      (T : ℝ) * (N - C - D) =
          ∑ _s ∈ Finset.range T, (N - C - D) := by
        simp
        ring
      _ ≤ _ := Finset.sum_le_sum fun s hs ↦ hrank s hs
  have hscore := edgeWalk_score_sum delta gamma v x₀ c T
  have hprogress :
      edgeScore gamma 0 v x₀ c (toWalk x₀) + 5 * (N - C - D) ≤
        edgeScore gamma T v x₀ c xT := by
    have hmul := mul_le_mul_of_nonneg_left hrankSum (sq_nonneg gamma)
    calc
      edgeScore gamma 0 v x₀ c (toWalk x₀) + 5 * (N - C - D) =
          edgeScore gamma 0 v x₀ c (toWalk x₀) +
            gamma ^ 2 * ((T : ℝ) * (N - C - D)) := by
        rw [← htime]
        ring
      _ ≤ edgeScore gamma 0 v x₀ c (toWalk x₀) + gamma ^ 2 *
          ∑ s ∈ Finset.range T,
            (Module.finrank ℝ (edgeSubspace delta v x₀ c
              (edgeWalk delta gamma v x₀ c s)) : ℝ) := by linarith
      _ ≤ edgeScore gamma T v x₀ c xT := hscore
  have hD : (D : ℝ) ≤ discrepancyPotential gamma T v x₀ c xT := by
    exact card_activeDiscrepancies_le_potential gamma delta T v x₀ c xT hc
      hdelta hdeltaSmall htime.le
  have hP0 : discrepancyPotential gamma 0 v x₀ c (toWalk x₀) ≤ N / 8 := by
    rw [discrepancyPotential_zero]
    change 2 * ∑ j, exp (-(c j) ^ 2 / 16) ≤ N / 8
    linarith
  have hxTCube : InCube xT :=
    edgeWalk_inCube delta gamma v x₀ c hx₀ hgamma hdeltaEq T
  have hxTNorm : ‖xT‖ ^ 2 ≤ N :=
    norm_sq_le_card_of_inCube xT hxTCube
  have hx₀Norm : 0 ≤ ‖toWalk x₀‖ ^ 2 := sq_nonneg _
  have hlower : -5 * (N / 8) + 5 * (N - C) ≤ ‖xT‖ ^ 2 := by
    dsimp only [xT] at hprogress hD hxTNorm ⊢
    simp only [edgeScore] at hprogress
    nlinarith
  have hCltR : 2 * (C : ℝ) < N := by
    dsimp only [N]
    exact_mod_cast hClt
  nlinarith

/-! ## Arbitrary accuracy and compactness -/

theorem exists_walk_parameters (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ q : ℕ, 0 < q ∧
      let gamma : ℝ := 1 / (q : ℝ)
      let delta : ℝ := gamma * sqrt (Fintype.card I)
      let T : ℕ := 5 * q ^ 2
      0 ≤ gamma ∧ 0 ≤ delta ∧ delta ≤ 1 / 4 ∧ delta ≤ epsilon ∧
        gamma ^ 2 * (T : ℝ) = 5 := by
  obtain ⟨q, hq⟩ := exists_nat_gt
    (max 1 (max (4 * sqrt (Fintype.card I))
      (sqrt (Fintype.card I) / epsilon)))
  have hqOne : (1 : ℝ) < q := lt_of_le_of_lt (le_max_left _ _) hq
  have hqposR : (0 : ℝ) < q := lt_trans (by norm_num) hqOne
  have hqpos : 0 < q := by exact_mod_cast hqposR
  have hqFour : 4 * sqrt (Fintype.card I) < (q : ℝ) := by
    exact lt_of_le_of_lt (le_trans (le_max_left _ _)
      (le_max_right 1 _)) hq
  have hqEpsilon : sqrt (Fintype.card I) / epsilon < (q : ℝ) := by
    exact lt_of_le_of_lt (le_trans (le_max_right _ _)
      (le_max_right _ _)) hq
  refine ⟨q, hqpos, ?_⟩
  dsimp only
  have hgamma : 0 ≤ (1 : ℝ) / q := by positivity
  have hdelta : 0 ≤ (1 / (q : ℝ)) * sqrt (Fintype.card I) := by positivity
  have hdeltaForm : (1 / (q : ℝ)) * sqrt (Fintype.card I) =
      sqrt (Fintype.card I) / q := by ring
  have hdeltaSmall : (1 / (q : ℝ)) * sqrt (Fintype.card I) ≤ 1 / 4 := by
    rw [hdeltaForm, div_le_iff₀ hqposR]
    nlinarith
  have hdeltaEpsilon :
      (1 / (q : ℝ)) * sqrt (Fintype.card I) ≤ epsilon := by
    rw [hdeltaForm, div_le_iff₀ hqposR]
    have hsqrt : sqrt (Fintype.card I) < (q : ℝ) * epsilon := by
      have := (div_lt_iff₀ hepsilon).mp hqEpsilon
      nlinarith
    linarith
  refine ⟨hgamma, hdelta, hdeltaSmall, hdeltaEpsilon, ?_⟩
  push_cast
  field_simp

/-- The finite edge walk produces an approximate partial colouring at every
positive accuracy. -/
theorem exists_approximate_partialColoring
    (v : J → I → ℝ) (x₀ : I → ℝ) (c : J → ℝ)
    (hx₀ : InCube x₀) (hc : ∀ j, 0 ≤ c j)
    (hentropy : (∑ j, exp (-(c j) ^ 2 / 16)) ≤
      (Fintype.card I : ℝ) / 16)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ x : I → ℝ,
      InCube x ∧
        Fintype.card I ≤ 2 * (approximateFixedCoordinates epsilon x).card ∧
        ∀ j, |dot (x - x₀) (v j)| ≤ c j * l2Norm (v j) := by
  obtain ⟨q, hq, hgamma, hdelta, hdeltaSmall, hdeltaEpsilon, htime⟩ :=
    exists_walk_parameters (I := I) epsilon hepsilon
  let gamma : ℝ := 1 / (q : ℝ)
  let delta : ℝ := gamma * sqrt (Fintype.card I)
  let T : ℕ := 5 * q ^ 2
  let xT : WalkSpace I := edgeWalk delta gamma v x₀ c T
  have hgamma' : 0 ≤ gamma := hgamma
  have hdelta' : 0 ≤ delta := hdelta
  have hdeltaSmall' : delta ≤ 1 / 4 := hdeltaSmall
  have hdeltaEpsilon' : delta ≤ epsilon := hdeltaEpsilon
  have htime' : gamma ^ 2 * (T : ℝ) = 5 := htime
  have hhalf : Fintype.card I ≤
      2 * (activeCoordinates delta xT).card := by
    exact edgeWalk_terminal_half delta gamma T v x₀ c hx₀ hc hentropy
      hgamma' rfl hdelta' hdeltaSmall' htime'
  have hxTCube : InCube xT :=
    edgeWalk_inCube delta gamma v x₀ c hx₀ hgamma' rfl T
  have hnormalized : ∀ j,
      |normalizedDiscrepancy (v j) x₀ xT| ≤ c j :=
    edgeWalk_normalizedDiscrepancy_le delta gamma v x₀ c hc hgamma' rfl T
  let x : I → ℝ := fun i ↦ xT i
  refine ⟨x, hxTCube, ?_, ?_⟩
  · have hsubset : activeCoordinates delta xT ⊆
        approximateFixedCoordinates epsilon x := by
      intro i hi
      rw [mem_approximateFixedCoordinates]
      have hi' := mem_activeCoordinates.mp hi
      dsimp only [x]
      linarith
    exact hhalf.trans (Nat.mul_le_mul_left 2 (Finset.card_le_card hsubset))
  · intro j
    by_cases hv : l2Norm (v j) = 0
    · rw [dot_eq_zero_of_l2Norm_eq_zero (x - x₀) (v j) hv, hv]
      simp
    · have hvpos : 0 < l2Norm (v j) :=
        lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hv)
      have hscale := normalizedDiscrepancy_mul_l2Norm hvpos x₀ xT
      have hnormNonneg : 0 ≤ l2Norm (v j) := Real.sqrt_nonneg _
      change |dot (fun i ↦ xT i - x₀ i) (v j)| ≤ c j * l2Norm (v j)
      rw [← hscale, abs_mul, abs_of_nonneg hnormNonneg]
      exact mul_le_mul_of_nonneg_right (hnormalized j) hnormNonneg

omit [DecidableEq J] in
/-- The unconditional, universe-polymorphic Lovett--Meka partial-colouring
principle used by the Erdős 228 construction. -/
theorem partialColoringPrinciple (I : Type u) (J : Type v)
    [Fintype I] [Fintype J] [DecidableEq I] :
    Erdos228.Discrepancy.PartialColoringPrinciple I J := by
  let : DecidableEq J := Classical.decEq J
  intro v x₀ c hx₀ hc hentropy
  apply hasPartialColoring_of_approximate v x₀ c
  intro epsilon hepsilon
  exact exists_approximate_partialColoring v x₀ c hx₀ hc hentropy epsilon hepsilon

end Erdos228.EdgeWalk
