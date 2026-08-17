/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos896.Ford.OrderQ

/-!
# Volume of an ordered interval

Measure-theoretic support for Ford's ordered-simplex calculations.
-/

namespace Erdos896.Ford

open MeasureTheory Set
open scoped BigOperators ENNReal Pointwise

/-- The standard solid simplex in the positive orthant. -/
def positiveSimplex (k : ℕ) (t : ℝ) : Set (Fin k → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ t}

/-- The closed `ℓ¹` ball, written in coordinates. -/
def l1Ball (k : ℕ) (t : ℝ) : Set (Fin k → ℝ) :=
  {x | ∑ i, |x i| ≤ t}

/-- Reflect the coordinates selected by a Boolean sign vector. -/
def signFlip {k : ℕ} (s : Fin k → Bool) (x : Fin k → ℝ) : Fin k → ℝ :=
  fun i ↦ if s i then x i else -x i

/-- One orthant piece of the `ℓ¹` ball, expressed as the inverse image of
the positive simplex under a coordinate reflection. -/
def orthantSimplex (k : ℕ) (t : ℝ) (s : Fin k → Bool) : Set (Fin k → ℝ) :=
  signFlip s ⁻¹' positiveSimplex k t

theorem measurableSet_positiveSimplex (k : ℕ) (t : ℝ) :
    MeasurableSet (positiveSimplex k t) := by
  have hall : MeasurableSet (⋂ i, {x : Fin k → ℝ | 0 ≤ x i}) :=
    MeasurableSet.iInter fun i ↦
      measurableSet_le measurable_const (measurable_pi_apply i)
  have hsum : MeasurableSet {x : Fin k → ℝ | ∑ i, x i ≤ t} :=
    measurableSet_le
      (Finset.measurable_sum _ fun i _ ↦ measurable_pi_apply i) measurable_const
  have heq : positiveSimplex k t =
      (⋂ i, {x : Fin k → ℝ | 0 ≤ x i}) ∩ {x | ∑ i, x i ≤ t} := by
    ext x
    simp [positiveSimplex]
  rw [heq]
  exact hall.inter hsum

theorem measurable_signFlip {k : ℕ} (s : Fin k → Bool) :
    Measurable (signFlip s) := by
  change Measurable (fun (x : Fin k → ℝ) (i : Fin k) ↦ if s i then x i else -x i)
  refine measurable_pi_lambda _ ?_
  intro i
  by_cases h : s i = true
  · simp only [h, ↓reduceIte]
    exact measurable_pi_apply i
  · have hs : s i = false := Bool.eq_false_of_not_eq_true h
    simp only [hs, Bool.false_eq_true, ↓reduceIte]
    exact (measurable_pi_apply i :
      Measurable (fun x : Fin k → ℝ ↦ x i)).neg

theorem measurePreserving_signFlip {k : ℕ} (s : Fin k → Bool) :
    MeasurePreserving (signFlip s) (volume : Measure (Fin k → ℝ)) volume := by
  refine ⟨measurable_signFlip s, ?_⟩
  rw [volume_pi]
  have hmap := (volume_preserving_pi
    (f := fun i : Fin k ↦ fun z : ℝ ↦ if s i then z else -z)
    (fun i ↦ by
      by_cases h : s i = true
      · simp only [h, ↓reduceIte]
        change MeasurePreserving id (volume : Measure ℝ) volume
        exact MeasurePreserving.id volume
      · have hs : s i = false := Bool.eq_false_of_not_eq_true h
        simpa only [hs, Bool.false_eq_true, ↓reduceIte] using
          (Measure.measurePreserving_neg (volume : Measure ℝ)))).map_eq
  rw [volume_pi] at hmap
  change Measure.map (fun a i ↦ if s i then a i else -a i)
    (Measure.pi fun _ : Fin k ↦ (volume : Measure ℝ)) = Measure.pi fun _ ↦ volume
  exact hmap

theorem measurableSet_orthantSimplex (k : ℕ) (t : ℝ) (s : Fin k → Bool) :
    MeasurableSet (orthantSimplex k t s) :=
  (measurable_signFlip s) (measurableSet_positiveSimplex k t)

theorem volume_orthantSimplex (k : ℕ) (t : ℝ) (s : Fin k → Bool) :
    volume (orthantSimplex k t s) = volume (positiveSimplex k t) := by
  exact (measurePreserving_signFlip s).measure_preimage
    (measurableSet_positiveSimplex k t).nullMeasurableSet

theorem volume_coordinate_eq_zero {k : ℕ} (i : Fin k) :
    volume {x : Fin k → ℝ | x i = 0} = 0 := by
  rw [volume_pi]
  exact Measure.pi_hyperplane (fun _ : Fin k ↦ (volume : Measure ℝ)) i 0

theorem orthantSimplex_aedisjoint {k : ℕ} {t : ℝ} {s r : Fin k → Bool}
    (hsr : s ≠ r) :
    AEDisjoint (volume : Measure (Fin k → ℝ))
      (orthantSimplex k t s) (orthantSimplex k t r) := by
  obtain ⟨i, hi⟩ : ∃ i, s i ≠ r i := by
    by_contra h
    apply hsr
    funext i
    exact not_ne_iff.mp (not_exists.mp h i)
  rw [AEDisjoint]
  apply measure_mono_null (t := {x : Fin k → ℝ | x i = 0})
  · intro x hx
    have hs := hx.1.1 i
    have hr := hx.2.1 i
    cases his : s i <;> cases hir : r i <;>
      simp_all [signFlip] <;> linarith
  · exact volume_coordinate_eq_zero i

theorem l1Ball_eq_iUnion_orthantSimplex (k : ℕ) (t : ℝ) :
    l1Ball k t = ⋃ s : Fin k → Bool, orthantSimplex k t s := by
  ext x
  constructor
  · intro hx
    let s : Fin k → Bool := fun i ↦ decide (0 ≤ x i)
    apply mem_iUnion.mpr
    refine ⟨s, ?_⟩
    have hcoord (i : Fin k) : signFlip s x i = |x i| := by
      simp only [signFlip, s, decide_eq_true_eq]
      split_ifs with h
      · exact (abs_of_nonneg h).symm
      · exact (abs_of_neg (lt_of_not_ge h)).symm
    refine ⟨?_, ?_⟩
    · intro i
      rw [hcoord]
      exact abs_nonneg _
    · simpa only [l1Ball, mem_ofPred_eq, hcoord] using hx
  · intro hx
    rcases mem_iUnion.mp hx with ⟨s, hs⟩
    have hcoord (i : Fin k) : |x i| = signFlip s x i := by
      have hnonneg := hs.1 i
      cases hi : s i with
      | false =>
          simp only [signFlip, hi, Bool.false_eq_true, ↓reduceIte] at hnonneg ⊢
          rw [abs_of_nonpos (by linarith)]
      | true =>
          simp only [signFlip, hi, ↓reduceIte] at hnonneg ⊢
          rw [abs_of_nonneg hnonneg]
    change ∑ i, |x i| ≤ t
    simpa only [hcoord] using hs.2

theorem volume_l1Ball_eq_mul_volume_positiveSimplex (k : ℕ) (t : ℝ) :
    volume (l1Ball k t) =
      (2 : ℝ≥0∞) ^ k * volume (positiveSimplex k t) := by
  rw [l1Ball_eq_iUnion_orthantSimplex]
  rw [measure_iUnion₀]
  · rw [tsum_fintype]
    simp [volume_orthantSimplex]
  · intro s r hsr
    exact orthantSimplex_aedisjoint hsr
  · exact fun s ↦ (measurableSet_orthantSimplex k t s).nullMeasurableSet

theorem volume_l1Ball_succ (k : ℕ) (t : ℝ) :
    volume (l1Ball (k + 1) t) =
      ENNReal.ofReal t ^ (k + 1) *
        ENNReal.ofReal ((2 : ℝ) ^ (k + 1) / (k + 1).factorial) := by
  have h := MeasureTheory.volume_sum_rpow_le
    (Fin (k + 1)) (p := (1 : ℝ)) le_rfl t
  rw [show (1 / (1 : ℝ) + 1) = (1 : ℕ) + 1 by norm_num,
    Real.Gamma_nat_eq_factorial] at h
  rw [show ((Fintype.card (Fin (k + 1)) : ℝ) / 1 + 1) =
      ((k + 1 : ℕ) : ℝ) + 1 by simp,
    Real.Gamma_nat_eq_factorial] at h
  simpa [l1Ball] using h

theorem volume_positiveSimplex_succ (k : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    volume (positiveSimplex (k + 1) t) =
      ENNReal.ofReal (t ^ (k + 1) / (k + 1).factorial) := by
  refine (ENNReal.mul_left_inj (c := (2 : ℝ≥0∞) ^ (k + 1))
    (by positivity) (by simp)).mp ?_
  calc
    volume (positiveSimplex (k + 1) t) * (2 : ℝ≥0∞) ^ (k + 1) =
        (2 : ℝ≥0∞) ^ (k + 1) * volume (positiveSimplex (k + 1) t) := mul_comm _ _
    _ =
        volume (l1Ball (k + 1) t) :=
      (volume_l1Ball_eq_mul_volume_positiveSimplex (k + 1) t).symm
    _ = ENNReal.ofReal t ^ (k + 1) *
        ENNReal.ofReal ((2 : ℝ) ^ (k + 1) / (k + 1).factorial) :=
      volume_l1Ball_succ k t
    _ = (2 : ℝ≥0∞) ^ (k + 1) *
        ENNReal.ofReal (t ^ (k + 1) / (k + 1).factorial) := by
      rw [ENNReal.ofReal_div_of_pos (by positivity : (0 : ℝ) < (k + 1).factorial),
        ENNReal.ofReal_div_of_pos (by positivity : (0 : ℝ) < (k + 1).factorial),
        ENNReal.ofReal_pow ht, ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2),
        ENNReal.ofReal_natCast]
      norm_num
      simp only [div_eq_mul_inv]
      ac_rfl
    _ = ENNReal.ofReal (t ^ (k + 1) / (k + 1).factorial) *
        (2 : ℝ≥0∞) ^ (k + 1) := mul_comm _ _

/-- The lower-triangular cumulative-sum matrix. -/
noncomputable def cumulativeMatrix (k : ℕ) : Matrix (Fin k) (Fin k) ℝ :=
  fun i j ↦ if j ≤ i then 1 else 0

/-- The linear map taking gaps to their successive partial sums. -/
noncomputable def cumulativeMap (k : ℕ) : (Fin k → ℝ) →ₗ[ℝ] (Fin k → ℝ) :=
  Matrix.toLin' (cumulativeMatrix k)

@[simp]
theorem cumulativeMatrix_apply (k : ℕ) (i j : Fin k) :
    cumulativeMatrix k i j = if j ≤ i then 1 else 0 := by
  rfl

/-! ## Ordered interval corollaries

The permutation-chamber argument in `OrderQ` supplies the all-dimensional
formula, including the empty tuple.  The statements below record the
zero-based and length-parameterized forms used in Ford's integrations. -/

/-- Volume of the ordered simplex `0 ≤ x₀ ≤ ⋯ ≤ xₖ₋₁ ≤ t`, written without
an auxiliary set abbreviation. -/
theorem volume_orderedSimplex_zero (k : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    volume {x : Fin k → ℝ | (∀ i, 0 ≤ x i ∧ x i ≤ t) ∧ Monotone x} =
      ENNReal.ofReal (t ^ k / (k.factorial : ℝ)) := by
  simpa only [orderedSimplex, sub_zero] using
    (volume_orderedSimplex k (a := 0) (b := t) ht)

/-- Real-valued form of `volume_orderedSimplex_zero`. -/
theorem volume_orderedSimplex_zero_toReal (k : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    (volume {x : Fin k → ℝ |
      (∀ i, 0 ≤ x i ∧ x i ≤ t) ∧ Monotone x}).toReal =
      t ^ k / (k.factorial : ℝ) := by
  simpa only [orderedSimplex, sub_zero] using
    (volume_orderedSimplex_toReal k (a := 0) (b := t) ht)

/-- Length-parameterized affine interval form: translation by `a` does not
change the ordered-simplex volume. -/
theorem volume_orderedSimplex_affine (k : ℕ) (a : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    volume (orderedSimplex k a (a + t)) =
      ENNReal.ofReal (t ^ k / (k.factorial : ℝ)) := by
  simpa only [add_sub_cancel_left] using
    (volume_orderedSimplex k (a := a) (b := a + t) (by linarith))

/-- Real-valued affine interval form. -/
theorem volume_orderedSimplex_affine_toReal (k : ℕ) (a : ℝ) {t : ℝ}
    (ht : 0 ≤ t) :
    (volume (orderedSimplex k a (a + t))).toReal =
      t ^ k / (k.factorial : ℝ) := by
  simpa only [add_sub_cancel_left] using
    (volume_orderedSimplex_toReal k (a := a) (b := a + t) (by linarith))

end Erdos896.Ford
