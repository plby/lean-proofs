/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos984.HunterLabelBounds
import ErdosProblems.Erdos984.HunterCentersSeparation

/-!
# An integral parameter scale for Hunter's construction

The published proof permits wide constant margins.  These integer-power
parameters avoid every rounding issue while retaining the decisive feature
`X = N^(O(1/D))`.
-/

namespace Erdos984

noncomputable section

def hunterN (D : ℕ) : ℕ := D ^ (D ^ 2)

def hunterK (D : ℕ) : ℕ := D ^ (4 * D)

def hunterM (D : ℕ) : ℕ := D ^ (20 * D)

def hunterY (D : ℕ) : ℕ := D ^ (5 * D)

def hunterX (D : ℕ) : ℕ := D ^ (100000 * D)

def hunterLabelBlocks (D : ℕ) : ℕ := 2 * D ^ 3 + 1

noncomputable def hunterRho (D : ℕ) : ℝ := ((D : ℝ) ^ 100)⁻¹

noncomputable def hunterDelta (D : ℕ) : ℝ :=
  hunterRho D / (hunterK D + 1 : ℕ)

noncomputable def hunterTau (D : ℕ) : ℝ := (4 * (D : ℝ) ^ D)⁻¹

lemma hunterLabelBlocks_le_pow (D : ℕ) (hD : 4 ≤ D) :
    hunterLabelBlocks D ≤ D ^ D := by
  have hDpos : 0 < D := by omega
  have hpowpos : 0 < D ^ 3 := pow_pos hDpos 3
  have hL4 : 2 * D ^ 3 + 1 ≤ D ^ 4 := by
    calc
      2 * D ^ 3 + 1 ≤ 3 * D ^ 3 := by omega
      _ ≤ D * D ^ 3 := Nat.mul_le_mul_right (D ^ 3) (by omega)
      _ = D ^ 4 := by ring
  exact hL4.trans (Nat.pow_le_pow_right hDpos hD)

lemma hunterK_mul_labelBlocks_le_Y (D : ℕ) (hD : 4 ≤ D) :
    hunterK D * hunterLabelBlocks D ≤ hunterY D := by
  calc
    hunterK D * hunterLabelBlocks D ≤ hunterK D * D ^ D :=
      Nat.mul_le_mul_left _ (hunterLabelBlocks_le_pow D hD)
    _ = D ^ (4 * D + D) := by simp [hunterK, pow_add]
    _ = hunterY D := by
      unfold hunterY
      congr 1
      omega

lemma hunterY_le_M (D : ℕ) (hD : 0 < D) : hunterY D ≤ hunterM D := by
  unfold hunterY hunterM
  exact Nat.pow_le_pow_right hD (by omega)

lemma two_le_hunterX (D : ℕ) (hD : 2 ≤ D) : 2 ≤ hunterX D := by
  unfold hunterX
  have hexp : 0 < 100000 * D := by omega
  apply hD.trans
  rw [show 100000 * D = (100000 * D - 1) + 1 by omega, pow_succ]
  calc
    D = D * 1 := by simp
    _ ≤ D * D ^ (100000 * D - 1) :=
      Nat.mul_le_mul_left D (pow_pos (by omega : 0 < D) (100000 * D - 1))
    _ = D ^ (100000 * D - 1) * D := Nat.mul_comm _ _

lemma hunterN_sq_lt_two_pow_labelBlocks (D : ℕ) :
    hunterN D ^ 2 < 2 ^ hunterLabelBlocks D := by
  calc
    hunterN D ^ 2 = D ^ (2 * D ^ 2) := by
      rw [hunterN, ← pow_mul]
      congr 1
      omega
    _ ≤ (2 ^ D) ^ (2 * D ^ 2) :=
      Nat.pow_le_pow_left D.lt_two_pow_self.le _
    _ = 2 ^ (2 * D ^ 3) := by
      rw [← pow_mul]
      congr 1
      ring
    _ < 2 ^ hunterLabelBlocks D := by
      apply Nat.pow_lt_pow_right (by omega)
      simp [hunterLabelBlocks]

lemma hunter_radial_label_base_count (D : ℕ) (hD : 4 ≤ D) :
    hunterN D ^ 2 * hunterK D ^ hunterY D <
      (hunterK D + 1) ^ hunterY D := by
  apply radial_label_base_count_of_two_pow
  · exact pow_pos (by omega) _
  · exact hunterK_mul_labelBlocks_le_Y D hD
  · exact hunterN_sq_lt_two_pow_labelBlocks D

lemma hunterRho_pos {D : ℕ} (hD : 0 < D) : 0 < hunterRho D := by
  simp only [hunterRho]
  positivity

lemma hunterDelta_pos {D : ℕ} (hD : 0 < D) : 0 < hunterDelta D := by
  exact div_pos (hunterRho_pos hD) (by positivity)

lemma hunterTau_pos {D : ℕ} (hD : 0 < D) : 0 < hunterTau D := by
  simp only [hunterTau]
  positivity

lemma hunterTau_le_half {D : ℕ} (hD : 0 < D) :
    hunterTau D ≤ (1 : ℝ) / 2 := by
  have hDreal : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hpow : (1 : ℝ) ≤ (D : ℝ) ^ D := one_le_pow₀ hDreal
  rw [hunterTau, inv_le_iff_one_le_mul₀ (by positivity)]
  nlinarith

lemma hunter_radialLower_eq_rho (D : ℕ) :
    radialLower (hunterDelta D) (hunterK D + 1) = hunterRho D := by
  simp only [radialLower, hunterDelta, Nat.cast_add, Nat.cast_one]
  field_simp

lemma hunter_four_mul_rho_lt_one {D : ℕ} (hD : 2 ≤ D) :
    4 * hunterRho D < 1 := by
  have hDpos : (0 : ℝ) < D := by positivity
  have hDreal : (2 : ℝ) ≤ D := by exact_mod_cast hD
  have hpow : (4 : ℝ) < (D : ℝ) ^ 100 := by
    calc
      (4 : ℝ) < 2 ^ 100 := by norm_num
      _ ≤ (D : ℝ) ^ 100 := by gcongr
  rw [hunterRho, ← div_eq_mul_inv, div_lt_one (pow_pos hDpos 100)]
  exact hpow

lemma hunter_four_mul_rho_le_half {D : ℕ} (hD : 2 ≤ D) :
    4 * hunterRho D ≤ (1 : ℝ) / 2 := by
  have hDpos : (0 : ℝ) < D := by positivity
  have hDreal : (2 : ℝ) ≤ D := by exact_mod_cast hD
  have hpow : (8 : ℝ) ≤ (D : ℝ) ^ 100 := by
    calc
      (8 : ℝ) ≤ 2 ^ 100 := by norm_num
      _ ≤ (D : ℝ) ^ 100 := by gcongr
  rw [hunterRho, ← div_eq_mul_inv, div_le_iff₀ (pow_pos hDpos 100)]
  linarith

/-- Convert a real union-cost estimate into the `ℝ≥0∞` form used by Haar
measure. -/
lemma ennreal_nat_mul_ofReal_pow_lt_one
    {n d : ℕ} {x : ℝ} (hx : 0 ≤ x)
    (h : (n : ℝ) * x ^ d < 1) :
    (n : ENNReal) * (ENNReal.ofReal x) ^ d < 1 := by
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_pow hx,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg n), ENNReal.ofReal_lt_one]
  exact h

lemma hunter_haar_real_cost (D : ℕ) (hD : 0 < D) :
    (hunterN D : ℝ) * (2 * hunterTau D) ^ D = ((2 : ℝ) ^ D)⁻¹ := by
  have hD0 : (D : ℝ) ≠ 0 := by positivity
  have hpow0 : (D : ℝ) ^ (D ^ 2) ≠ 0 := pow_ne_zero _ hD0
  have htwo : 2 * hunterTau D = (2 * (D : ℝ) ^ D)⁻¹ := by
    rw [hunterTau]
    field_simp
    norm_num
  rw [htwo, inv_pow, mul_pow, ← pow_mul]
  simp only [hunterN, Nat.cast_pow]
  have hDD : D * D = D ^ 2 := by ring
  rw [hDD]
  field_simp

lemma hunter_haar_cost_lt_one (D : ℕ) (hD : 0 < D) :
    (hunterN D : ENNReal) *
      (ENNReal.ofReal (2 * hunterTau D)) ^ D < 1 := by
  apply ennreal_nat_mul_ofReal_pow_lt_one
  · exact mul_nonneg zero_le_two (hunterTau_pos hD).le
  · rw [hunter_haar_real_cost D hD]
    exact inv_lt_one₀ (by positivity) |>.2 (by
      exact one_lt_pow₀ (by norm_num) hD.ne')

lemma hunter_haar_cost_lt_half (D : ℕ) (hD : 2 ≤ D) :
    (hunterN D : ENNReal) *
      (ENNReal.ofReal (2 * hunterTau D)) ^ D <
        ENNReal.ofReal ((1 : ℝ) / 2) := by
  rw [← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_pow
      (mul_nonneg zero_le_two (hunterTau_pos (by omega)).le),
    ← ENNReal.ofReal_mul (by positivity), hunter_haar_real_cost D (by omega)]
  apply (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).2
  have hpow : (4 : ℝ) ≤ 2 ^ D := by
    calc
      (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ D := pow_le_pow_right₀ (by norm_num) hD
  rw [inv_lt_iff_one_lt_mul₀ (by positivity)]
  nlinarith

lemma hunter_width_lt_tau_sq (D : ℕ) (hD : 2 ≤ D) :
    radialSquaredWidth (hunterDelta D) (hunterK D) < hunterTau D ^ 2 := by
  have hDpos : 0 < D := by omega
  let k : ℝ := (hunterK D : ℕ)
  have hkpos : 0 < k := by
    dsimp [k, hunterK]
    positivity
  have hkone : (1 : ℝ) ≤ k := by
    dsimp [k, hunterK]
    exact_mod_cast pow_pos hDpos (4 * D)
  have hρpos : 0 < hunterRho D := hunterRho_pos hDpos
  have hΔnonneg : 0 ≤ hunterDelta D := (hunterDelta_pos hDpos).le
  have hcoef : (((2 * hunterK D + 1 : ℕ) : ℝ)) ≤ 3 * k := by
    push_cast
    dsimp [k]
    linarith
  have hdelta : hunterDelta D ≤ hunterRho D / k := by
    rw [hunterDelta]
    apply div_le_div_of_nonneg_left hρpos.le hkpos
    dsimp [k]
    exact_mod_cast Nat.le_succ (hunterK D)
  have hrough : radialSquaredWidth (hunterDelta D) (hunterK D) ≤
      3 * hunterRho D ^ 2 / k := by
    rw [radialSquaredWidth]
    calc
      (((2 * hunterK D + 1 : ℕ) : ℝ)) * hunterDelta D ^ 2 ≤
          (3 * k) * (hunterRho D / k) ^ 2 := by
        gcongr
      _ = 3 * hunterRho D ^ 2 / k := by field_simp
  refine hrough.trans_lt ?_
  dsimp [k, hunterK, hunterRho, hunterTau]
  push_cast
  have hDreal : (2 : ℝ) ≤ D := by exact_mod_cast hD
  have hbase : (48 : ℝ) < (D : ℝ) ^ (2 * D + 200) := by
    calc
      (48 : ℝ) < 2 ^ (2 * D + 200) := by
        have : 6 ≤ 2 * D + 200 := by omega
        exact (by norm_num : (48 : ℝ) < 2 ^ 6) |>.trans_le
          (pow_le_pow_right₀ (by norm_num) this)
      _ ≤ (D : ℝ) ^ (2 * D + 200) := by gcongr
  field_simp
  norm_num
  calc
    48 * ((D : ℝ) ^ D) ^ 2 = 48 * (D : ℝ) ^ (2 * D) := by
      rw [← pow_mul]
      congr 2
      ring
    _ < (D : ℝ) ^ (2 * D + 200) * (D : ℝ) ^ (2 * D) :=
      mul_lt_mul_of_pos_right hbase (by positivity)
    _ = (D : ℝ) ^ 200 * (D : ℝ) ^ (4 * D) := by
      rw [← pow_add, ← pow_add]
      ring

lemma hunter_center_real_cost_lt_one (D : ℕ) (hD : 2 ≤ D) :
    (hunterM D ^ 3 : ℕ) * (8 * hunterRho D) ^ D < (1 : ℝ) := by
  have hDpos : (0 : ℝ) < D := by positivity
  have hbase : (8 : ℝ) < (D : ℝ) ^ 40 := by
    calc
      (8 : ℝ) < 2 ^ 40 := by norm_num
      _ ≤ (D : ℝ) ^ 40 := by
        have hDreal : (2 : ℝ) ≤ D := by exact_mod_cast hD
        gcongr
  simp only [hunterM, hunterRho, Nat.cast_pow]
  rw [← pow_mul, ← div_eq_mul_inv, div_pow, ← pow_mul]
  have h60 : 20 * D * 3 = 60 * D := by ring
  rw [h60, ← mul_div_assoc]
  apply (div_lt_one (pow_pos hDpos (100 * D))).2
  have hp : (8 : ℝ) ^ D < (D : ℝ) ^ (40 * D) := by
    simpa only [← pow_mul] using
      (pow_lt_pow_left₀ hbase (by norm_num) (by omega : D ≠ 0))
  calc
    (D : ℝ) ^ (60 * D) * 8 ^ D <
        (D : ℝ) ^ (60 * D) * (D : ℝ) ^ (40 * D) :=
      mul_lt_mul_of_pos_left hp (by positivity)
    _ = (D : ℝ) ^ (100 * D) := by rw [← pow_add]; congr 2; ring

lemma hunter_center_cost_lt_one (D : ℕ) (hD : 2 ≤ D) :
    (hunterM D ^ 3 : ENNReal) *
      (ENNReal.ofReal (8 * hunterRho D)) ^ D < 1 := by
  simpa only [Nat.cast_pow] using
    (ennreal_nat_mul_ofReal_pow_lt_one
      (n := hunterM D ^ 3) (d := D) (x := 8 * hunterRho D)
      (mul_nonneg (by norm_num) (hunterRho_pos (by omega)).le)
      (hunter_center_real_cost_lt_one D hD))

/-- A rotation satisfying the uniform blue-step inequality at the explicit
Hunter scale. -/
lemma exists_hunter_theta (D : ℕ) (hD : 2 ≤ D) :
    ∃ θ : UnitAddTorus (Fin D), ∀ d : ℕ, 0 < d → d < hunterN D →
      radialSquaredWidth (hunterDelta D) (hunterK D) <
        squaredNorm (centeredTorusLift (d • θ)) := by
  let _ : Nonempty (Fin D) := ⟨⟨0, by omega⟩⟩
  apply exists_torus_with_step_squaredNorm_gt
    (D := Fin D) (hunterN D) (τ := hunterTau D)
  · exact (hunterTau_pos (by omega)).le
  · exact hunterTau_le_half (by omega)
  · simpa using hunter_haar_cost_lt_one D (by omega)
  · exact hunter_width_lt_tau_sq D hD

/-- A center family satisfying the geometric separation used to rule out
mixed-center blue progressions. -/
lemma exists_hunter_separated_centers (D : ℕ) (hD : 2 ≤ D) :
    ∃ center : Fin (hunterM D) → UnitAddTorus (Fin D),
      TorusCenterThreeSeparated center (hunterRho D) := by
  let _ : Nonempty (Fin D) := ⟨⟨0, by omega⟩⟩
  apply exists_torusCenterThreeSeparated
    (D := Fin D) (ι := Fin (hunterM D))
  · exact (hunterRho_pos (by omega)).le
  · exact hunter_four_mul_rho_le_half hD
  · simpa using hunter_center_cost_lt_one D hD

end

end Erdos984
