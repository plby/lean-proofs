/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos851.LocalEulerProducts
import ErdosProblems.Erdos851.Scales

/-!
# Euler-product mass at the roughness scale

The dimension-one Mertens estimate bounds the inverse one-shift Euler
product.  This file records the elementary inversion step that turns that
estimate into a lower bound for the first-moment scale
`J * localEulerProduct oneShiftDensity z Y`.

For the cutoff `Y = roughCutoff S J`, its logarithm is at most
`J * log 2 / (8*S)`.  Once `J` exceeds an explicit threshold depending on
the fixed lower endpoint `z`, the cutoff is also at least `z`.  Consequently
the first-moment Euler mass is eventually bounded below by a positive
quantity growing linearly in `S`.
-/

namespace Erdos851

open Filter
open scoped BigOperators Topology

/-- The inverse Euler product really is the inverse of the direct product. -/
theorem inverseLocalEulerProduct_eq_inv (g : ℕ → ℝ) (z y : ℕ) :
    inverseLocalEulerProduct g z y = (localEulerProduct g z y)⁻¹ := by
  simp only [inverseLocalEulerProduct, localEulerProduct,
    Finset.prod_inv_distrib]

/-- A logarithmic upper bound for the moving endpoint converts the
dimension-one inverse-product estimate into a positive lower bound for the
Euler mass.  The constant `C` is uniform in all endpoints and in `A`. -/
theorem exists_oneShift_eulerMass_lower_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ {A : ℝ} {z Y J : ℕ}, 0 < A → 2 ≤ z → z ≤ Y → 0 < J →
        Real.log (Y : ℝ) ≤ A * (J : ℝ) →
        Real.log (z : ℝ) / (C * A) ≤
          (J : ℝ) * localEulerProduct oneShiftDensity z Y := by
  obtain ⟨C, hC, hdimension⟩ := exists_oneShift_dimension_bound
  refine ⟨C, hC, ?_⟩
  intro A z Y J hA hz hzY hJ hlog
  have hlogz : 0 < Real.log (z : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < z by omega))
  have hJr : (0 : ℝ) < J := by exact_mod_cast hJ
  have hVpos : 0 < localEulerProduct oneShiftDensity z Y :=
    oneShift_localEulerProduct_pos
  have hinverse := hdimension z Y hz hzY
  rw [inverseLocalEulerProduct_eq_inv] at hinverse
  let B : ℝ := C * (A * (J : ℝ) / Real.log (z : ℝ))
  have hBpos : 0 < B := by
    dsimp [B]
    positivity
  have hinverseB :
      (localEulerProduct oneShiftDensity z Y)⁻¹ ≤ B := by
    refine hinverse.trans ?_
    dsimp [B]
    exact mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hlog hlogz.le) hC.le
  have hVlower : B⁻¹ ≤ localEulerProduct oneShiftDensity z Y :=
    (inv_le_comm₀ hVpos hBpos).mp hinverseB
  calc
    Real.log (z : ℝ) / (C * A) = (J : ℝ) * B⁻¹ := by
      dsimp [B]
      field_simp [hC.ne', hA.ne', hJr.ne', hlogz.ne']
    _ ≤ (J : ℝ) * localEulerProduct oneShiftDensity z Y :=
      mul_le_mul_of_nonneg_left hVlower hJr.le

/-- The rough cutoff eventually dominates any fixed lower endpoint.  The
hypothesis is an explicit sufficient threshold. -/
theorem le_roughCutoff_of_scale_le {S z J : ℕ} (hS : 0 < S)
    (hJ : 8 * S * (Nat.log 2 z + 1) ≤ J) :
    z ≤ roughCutoff S J := by
  have hden : 0 < 8 * S := Nat.mul_pos (by norm_num) hS
  have hquot : Nat.log 2 z + 1 ≤ J / (8 * S) := by
    apply (Nat.le_div_iff_mul_le hden).2
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hJ
  rw [roughCutoff]
  calc
    z ≤ 2 ^ (Nat.log 2 z + 1) :=
      (Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) z).le
    _ ≤ 2 ^ (J / (8 * S)) :=
      Nat.pow_le_pow_right (by norm_num) hquot

/-- The moving cutoff tends to infinity for every fixed positive sieve
depth parameter. -/
theorem tendsto_roughCutoff_atTop (S : ℕ) (hS : 0 < S) :
    Tendsto (roughCutoff S) atTop atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro z
  refine ⟨8 * S * (Nat.log 2 z + 1), ?_⟩
  intro J hJ
  exact le_roughCutoff_of_scale_le hS hJ

/-- The logarithm of the moving cutoff is at most `J * log 2 / (8*S)`. -/
theorem log_roughCutoff_le {S J : ℕ} (hS : 0 < S) :
    Real.log (roughCutoff S J : ℝ) ≤
      (J : ℝ) * Real.log 2 / ((8 * S : ℕ) : ℝ) := by
  rw [roughCutoff, Nat.cast_pow, Real.log_pow]
  have hden : 0 < 8 * S := Nat.mul_pos (by norm_num) hS
  have hdenR : (0 : ℝ) < ((8 * S : ℕ) : ℝ) := by exact_mod_cast hden
  have hmul : (J / (8 * S)) * (8 * S) ≤ J :=
    Nat.div_mul_le_self J (8 * S)
  have hmulR :
      ((J / (8 * S) : ℕ) : ℝ) * ((8 * S : ℕ) : ℝ) ≤ (J : ℝ) := by
    exact_mod_cast hmul
  have hquotR :
      ((J / (8 * S) : ℕ) : ℝ) ≤ (J : ℝ) / ((8 * S : ℕ) : ℝ) :=
    (le_div_iff₀ hdenR).2 hmulR
  calc
    ((J / (8 * S) : ℕ) : ℝ) * Real.log (2 : ℝ) ≤
        ((J : ℝ) / ((8 * S : ℕ) : ℝ)) * Real.log 2 :=
      mul_le_mul_of_nonneg_right hquotR (Real.log_nonneg (by norm_num))
    _ = (J : ℝ) * Real.log 2 / ((8 * S : ℕ) : ℝ) := by ring

/-- At the rough cutoff, the one-shift Euler mass has a lower bound growing
linearly in `S`, once the explicit scale threshold is met. -/
theorem exists_oneShift_roughCutoff_mass_lower_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ {S z J : ℕ}, 0 < S → 2 ≤ z →
        8 * S * (Nat.log 2 z + 1) ≤ J →
        ((8 * S : ℕ) : ℝ) * Real.log (z : ℝ) /
            (C * Real.log 2) ≤
          (J : ℝ) * localEulerProduct oneShiftDensity z
            (roughCutoff S J) := by
  obtain ⟨C, hC, hmass⟩ := exists_oneShift_eulerMass_lower_bound
  refine ⟨C, hC, ?_⟩
  intro S z J hS hz hJ
  have hthreshold : 0 < 8 * S * (Nat.log 2 z + 1) := by positivity
  have hJpos : 0 < J := hthreshold.trans_le hJ
  have hden : (0 : ℝ) < ((8 * S : ℕ) : ℝ) := by positivity
  have hlogTwo : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hA : 0 < Real.log 2 / ((8 * S : ℕ) : ℝ) :=
    div_pos hlogTwo hden
  have hlog : Real.log (roughCutoff S J : ℝ) ≤
      (Real.log 2 / ((8 * S : ℕ) : ℝ)) * (J : ℝ) := by
    calc
      Real.log (roughCutoff S J : ℝ) ≤
          (J : ℝ) * Real.log 2 / ((8 * S : ℕ) : ℝ) :=
        log_roughCutoff_le hS
      _ = (Real.log 2 / ((8 * S : ℕ) : ℝ)) * (J : ℝ) := by ring
  have hmain := hmass hA hz (le_roughCutoff_of_scale_le hS hJ) hJpos hlog
  calc
    ((8 * S : ℕ) : ℝ) * Real.log (z : ℝ) / (C * Real.log 2) =
        Real.log (z : ℝ) /
          (C * (Real.log 2 / ((8 * S : ℕ) : ℝ))) := by
      field_simp [hC.ne', hlogTwo.ne', hden.ne']
    _ ≤ (J : ℝ) * localEulerProduct oneShiftDensity z
          (roughCutoff S J) := hmain

/-- Eventual form of the rough-cutoff mass bound for fixed `S` and `z`. -/
theorem exists_eventually_oneShift_roughCutoff_mass_lower_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ {S z : ℕ}, 0 < S → 2 ≤ z →
      ∀ᶠ J : ℕ in atTop,
        ((8 * S : ℕ) : ℝ) * Real.log (z : ℝ) /
            (C * Real.log 2) ≤
          (J : ℝ) * localEulerProduct oneShiftDensity z
            (roughCutoff S J) := by
  obtain ⟨C, hC, hmass⟩ :=
    exists_oneShift_roughCutoff_mass_lower_bound
  refine ⟨C, hC, ?_⟩
  intro S z hS hz
  filter_upwards
    [Filter.eventually_ge_atTop (8 * S * (Nat.log 2 z + 1))] with J hJ
  exact hmass hS hz hJ

end Erdos851
