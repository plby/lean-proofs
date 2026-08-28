import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedTetrahedronRotationBasic

/-!
# A nonsingular rotation of the closed square

We interpolate the identity and the quarter turn on the centered square,
then divide by `1 - ‖v‖ + ‖w‖`.  This denominator is strictly positive,
including at the center.  The resulting maps preserve the perimeter.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected

/-- Clockwise quarter turn on the ambient real plane with its sup norm. -/
def rotationVector (v : ℝ × ℝ) : ℝ × ℝ := (v.2, -v.1)

@[simp] theorem rotationVector_norm (v : ℝ × ℝ) : ‖rotationVector v‖ = ‖v‖ := by
  simp [rotationVector, Prod.norm_def, max_comm]

/-- Straight interpolation in the ambient plane; it never kills a nonzero vector. -/
def rotationBlend (t : ℝ) (v : ℝ × ℝ) : ℝ × ℝ :=
  ((1 - t) * v.1 + t * v.2, (1 - t) * v.2 - t * v.1)

@[simp] theorem rotationBlend_zero (v : ℝ × ℝ) : rotationBlend 0 v = v := by
  ext <;> simp [rotationBlend]

@[simp] theorem rotationBlend_one (v : ℝ × ℝ) : rotationBlend 1 v = rotationVector v := by
  ext <;> simp [rotationBlend, rotationVector]

@[simp] theorem rotationBlend_zero_vector (t : ℝ) : rotationBlend t 0 = 0 := by
  ext <;> simp [rotationBlend]

theorem rotationBlend_ne_zero (t : ℝ) {v : ℝ × ℝ} (hv : v ≠ 0) :
    rotationBlend t v ≠ 0 := by
  intro h
  have h₁ : (1 - t) * v.1 + t * v.2 = 0 := congrArg Prod.fst h
  have h₂ : (1 - t) * v.2 - t * v.1 = 0 := congrArg Prod.snd h
  have hd : (1 - t) ^ 2 + t ^ 2 ≠ 0 := by
    have hp : 0 < (1 - t) ^ 2 + t ^ 2 := by
      nlinarith [sq_nonneg (t - 1 / 2)]
    exact ne_of_gt hp
  have ha : ((1 - t) ^ 2 + t ^ 2) * v.1 = 0 := by
    linear_combination (1 - t) * h₁ - t * h₂
  have hb : ((1 - t) ^ 2 + t ^ 2) * v.2 = 0 := by
    linear_combination t * h₁ + (1 - t) * h₂
  apply hv
  exact Prod.ext (mul_eq_zero.mp ha |>.resolve_left hd)
    (mul_eq_zero.mp hb |>.resolve_left hd)

theorem rotationBlend_continuous :
    Continuous (fun z : ℝ × (ℝ × ℝ) => rotationBlend z.1 z.2) := by
  unfold rotationBlend
  fun_prop

/-- Translate and dilate the native unit square to the sup-norm unit ball. -/
def rotationCentered (u : Fin 2 → I) : ℝ × ℝ :=
  (2 * (u 0 : ℝ) - 1, 2 * (u 1 : ℝ) - 1)

theorem rotationCentered_continuous : Continuous rotationCentered := by
  unfold rotationCentered
  fun_prop

theorem rotationCentered_norm_le (u : Fin 2 → I) : ‖rotationCentered u‖ ≤ 1 := by
  rw [norm_prod_le_iff]
  constructor <;> rw [Real.norm_eq_abs, abs_le]
  · constructor <;> dsimp [rotationCentered] <;>
      linarith [(u 0).property.1, (u 0).property.2]
  · constructor <;> dsimp [rotationCentered] <;>
      linarith [(u 1).property.1, (u 1).property.2]

theorem rotationCentered_norm_boundary (u : Fin 2 → I)
    (hu : u ∈ Cube.boundary (Fin 2)) : ‖rotationCentered u‖ = 1 := by
  apply le_antisymm (rotationCentered_norm_le u)
  rcases hu with ⟨i, hi | hi⟩
  · fin_cases i
    · change u 0 = 0 at hi
      have hc : ‖(rotationCentered u).1‖ = 1 := by norm_num [rotationCentered, hi]
      exact hc ▸ norm_fst_le (rotationCentered u)
    · change u 1 = 0 at hi
      have hc : ‖(rotationCentered u).2‖ = 1 := by norm_num [rotationCentered, hi]
      exact hc ▸ norm_snd_le (rotationCentered u)
  · fin_cases i
    · change u 0 = 1 at hi
      have hc : ‖(rotationCentered u).1‖ = 1 := by norm_num [rotationCentered, hi]
      exact hc ▸ norm_fst_le (rotationCentered u)
    · change u 1 = 1 at hi
      have hc : ‖(rotationCentered u).2‖ = 1 := by norm_num [rotationCentered, hi]
      exact hc ▸ norm_snd_le (rotationCentered u)

/-- A normalization denominator which is nonsingular even at the center. -/
def rotationDenominator (t : I) (u : Fin 2 → I) : ℝ :=
  1 - ‖rotationCentered u‖ + ‖rotationBlend t (rotationCentered u)‖

theorem rotationDenominator_pos (t : I) (u : Fin 2 → I) :
    0 < rotationDenominator t u := by
  by_cases hv : rotationCentered u = 0
  · simp [rotationDenominator, hv]
  · have hnorm : 0 < ‖rotationBlend t (rotationCentered u)‖ :=
      norm_pos_iff.mpr (rotationBlend_ne_zero t hv)
    have hle := rotationCentered_norm_le u
    unfold rotationDenominator
    linarith

theorem rotationDenominator_continuous :
    Continuous (fun z : I × (Fin 2 → I) => rotationDenominator z.1 z.2) := by
  unfold rotationDenominator
  apply Continuous.add
  · exact continuous_const.sub (rotationCentered_continuous.comp continuous_snd).norm
  · apply Continuous.norm
    exact rotationBlend_continuous.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk
        (rotationCentered_continuous.comp continuous_snd))

/-- The normalized ambient homotopy on the centered unit square. -/
def rotationNormalized (t : I) (u : Fin 2 → I) : ℝ × ℝ :=
  (rotationDenominator t u)⁻¹ • rotationBlend t (rotationCentered u)

theorem rotationNormalized_continuous :
    Continuous (fun z : I × (Fin 2 → I) => rotationNormalized z.1 z.2) := by
  unfold rotationNormalized
  apply Continuous.smul
    (f := fun z : I × (Fin 2 → I) => (rotationDenominator z.1 z.2)⁻¹)
    (g := fun z : I × (Fin 2 → I) => rotationBlend z.1 (rotationCentered z.2))
  · exact rotationDenominator_continuous.inv₀
      (fun z => ne_of_gt (rotationDenominator_pos z.1 z.2))
  · exact rotationBlend_continuous.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk
        (rotationCentered_continuous.comp continuous_snd))

theorem rotationNormalized_norm_le (t : I) (u : Fin 2 → I) :
    ‖rotationNormalized t u‖ ≤ 1 := by
  have hd := rotationDenominator_pos t u
  rw [rotationNormalized, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hd.le)]
  rw [inv_mul_le_iff₀ hd, mul_one]
  unfold rotationDenominator
  linarith [rotationCentered_norm_le u]

theorem rotationNormalized_norm_boundary (t : I) (u : Fin 2 → I)
    (hu : u ∈ Cube.boundary (Fin 2)) : ‖rotationNormalized t u‖ = 1 := by
  have hd := rotationDenominator_pos t u
  have he : rotationDenominator t u = ‖rotationBlend t (rotationCentered u)‖ := by
    simp [rotationDenominator, rotationCentered_norm_boundary u hu]
  rw [rotationNormalized, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hd.le)]
  rw [← he, inv_mul_cancel₀ (ne_of_gt hd)]

@[simp] theorem rotationNormalized_zero (u : Fin 2 → I) :
    rotationNormalized 0 u = rotationCentered u := by
  simp [rotationNormalized, rotationDenominator]

@[simp] theorem rotationNormalized_one (u : Fin 2 → I) :
    rotationNormalized 1 u = rotationVector (rotationCentered u) := by
  simp [rotationNormalized, rotationDenominator]

end Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected
