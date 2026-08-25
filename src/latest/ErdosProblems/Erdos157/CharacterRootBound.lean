import ErdosProblems.Erdos157.ElementaryBounds
import Mathlib.Analysis.Complex.Exponential

/-!
# An elementary zero-free-region criterion

The criterion isolates exactly the Euler-product positivity inequality which
must be supplied by the polynomial character sums. All estimates for the
inverse roots themselves are proved here by elementary complex algebra.
-/

namespace Erdos157.Elementary.ElementaryCharacterBound

open scoped BigOperators

/-- The real logarithmic derivative associated to a finite list of inverse roots. -/
noncomputable def rootSum {m : ℕ} (α : Fin m → ℂ) (z : ℂ) : ℝ :=
  ∑ i, (contribution (α i * z)).re

theorem contribution_mul_le_half {a z : ℂ} (ha : ‖a‖ ≤ 1) (hz : ‖z‖ < 1) :
    (contribution (a * z)).re ≤ 1 / 2 := by
  have hnorm : ‖a * z‖ < 1 := by
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg z) ha).trans_lt hz
  apply contribution_re_le_half hnorm.le
  intro heq
  simp [heq] at hnorm

theorem rootSum_le {m : ℕ} (α : Fin m → ℂ) (hα : ∀ i, ‖α i‖ ≤ 1)
    {z : ℂ} (hz : ‖z‖ < 1) : rootSum α z ≤ (m : ℝ) / 2 := by
  calc
    _ ≤ ∑ _i : Fin m, (1 / 2 : ℝ) :=
      Finset.sum_le_sum (fun i _ => contribution_mul_le_half (hα i) hz)
    _ = _ := by simp; ring

/-- Isolate the inverse root pointing directly towards the test point. -/
theorem rootSum_le_distinguished {m : ℕ} (α : Fin m → ℂ)
    (hα : ∀ i, ‖α i‖ ≤ 1) (j : Fin m) {z : ℂ} (hz : ‖z‖ < 1)
    {y : ℝ} (hreal : α j * z = (y : ℂ)) :
    rootSum α z ≤ -y / (1 - y) + ((m : ℝ) - 1) / 2 := by
  classical
  have hrest : (∑ i ∈ Finset.univ.erase j, (contribution (α i * z)).re) ≤
      ((m : ℝ) - 1) / 2 := by
    calc
      _ ≤ ∑ _i ∈ Finset.univ.erase j, (1 / 2 : ℝ) :=
        Finset.sum_le_sum (fun i _ => contribution_mul_le_half (hα i) hz)
      _ = _ := by
        have hm : 1 ≤ m := by have := j.isLt; omega
        simp [Finset.card_erase_of_mem, Nat.cast_sub hm]
        ring
  have hdist : (contribution (α j * z)).re = -y / (1 - y) := by
    rw [hreal]
    rw [contribution, ← Complex.ofReal_one, ← Complex.ofReal_sub,
      ← Complex.ofReal_neg, ← Complex.ofReal_div, Complex.ofReal_re]
  unfold rootSum
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j), hdist]
  linarith

/-- Square the phase without changing the radius. -/
noncomputable def squaredPhase (z : ℂ) : ℂ := z ^ 2 / (‖z‖ : ℂ)

theorem norm_squaredPhase (z : ℂ) : ‖squaredPhase z‖ = ‖z‖ := by
  rw [squaredPhase, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg z)]
  by_cases hz : ‖z‖ = 0
  · simp [hz]
  · field_simp

/-- Positivity of `3 + 4 cos θ + cos 2θ` gives a quantitative root gap.
The roots are normalized by the field cardinality, so the ambient disk has radius one. -/
theorem norm_root_lt_of_euler_positivity {m n H : ℕ} (hH : 1 ≤ H)
    (α : Fin m → ℂ) (β : Fin n → ℂ)
    (hm : m + 1 ≤ H) (hn : n + 1 ≤ H)
    (hα : ∀ i, ‖α i‖ ≤ 1) (hβ : ∀ i, ‖β i‖ ≤ 1)
    (hpositive : ∀ z : ℂ, ‖z‖ < 1 →
      0 ≤ 3 * (‖z‖ / (1 - ‖z‖)) + 4 * rootSum α z + rootSum β (squaredPhase z))
    (j : Fin m) : ‖α j‖ < 1 - 1 / (100 * (H : ℝ)) := by
  have hHreal : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hH0 : (0 : ℝ) < H := by linarith
  let x : ℝ := 1 - 1 / (10 * (H : ℝ))
  obtain ⟨hxpos, hxlt⟩ := test_radius_bounds hHreal
  change 0 < x at hxpos
  change x < 1 at hxlt
  by_contra hbad
  have hrlo : 1 - 1 / (100 * (H : ℝ)) ≤ ‖α j‖ := le_of_not_gt hbad
  have hrpos : 0 < ‖α j‖ := by
    have hfrac : 1 / (100 * (H : ℝ)) < 1 :=
      (div_lt_one (by positivity)).mpr (by linarith)
    linarith
  have hane : α j ≠ 0 := norm_pos_iff.mp hrpos
  let z : ℂ := ((‖α j‖ * x : ℝ) : ℂ) / α j
  have hznorm : ‖z‖ = x := by
    dsimp only [z]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (mul_pos hrpos hxpos)]
    exact mul_div_cancel_left₀ x hrpos.ne'
  have hz : ‖z‖ < 1 := hznorm ▸ hxlt
  have hreal : α j * z = ((‖α j‖ * x : ℝ) : ℂ) := mul_div_cancel₀ _ hane
  have hfirst := rootSum_le_distinguished α hα j hz hreal
  rw [neg_div] at hfirst
  have hsecond := rootSum_le β hβ (z := squaredPhase z) (by rwa [norm_squaredPhase])
  have hpos := hpositive z hz
  rw [hznorm] at hpos
  have hmreal : (m : ℝ) + 1 ≤ H := by exact_mod_cast hm
  have hnreal : (n : ℝ) + 1 ≤ H := by exact_mod_cast hn
  have hylo : (1 - 1 / (100 * (H : ℝ))) * x ≤ ‖α j‖ * x :=
    mul_le_mul_of_nonneg_right hrlo hxpos.le
  have hyhi : ‖α j‖ * x < 1 :=
    (mul_le_of_le_one_left hxpos.le (hα j)).trans_lt hxlt
  apply normalized_root_numeric_contradiction (H : ℝ) (‖α j‖ * x) hHreal hylo hyhi
  change 0 ≤ 3 * (x / (1 - x)) - 4 * (‖α j‖ * x / (1 - ‖α j‖ * x)) +
    (5 * (H : ℝ) - 9) / 2
  nlinarith

/-- The root gap gives an explicit exponentially decaying power-sum error. -/
theorem norm_rootPowerSum_le {m H : ℕ} (hH : 1 ≤ H) (α : Fin m → ℂ)
    (hα : ∀ i, ‖α i‖ ≤ 1 - 1 / (100 * (H : ℝ))) (d : ℕ) :
    ‖∑ i, α i ^ d‖ ≤ (m : ℝ) * Real.exp (-(d : ℝ) / (100 * (H : ℝ))) := by
  have hHreal : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hden : (0 : ℝ) < 100 * H := by positivity
  have hfrac : 1 / (100 * (H : ℝ)) ≤ 1 :=
    (div_le_one hden).mpr (by linarith)
  have hrho : 0 ≤ 1 - 1 / (100 * (H : ℝ)) := by linarith
  have hpow : (1 - 1 / (100 * (H : ℝ))) ^ d ≤
      Real.exp (-(d : ℝ) / (100 * (H : ℝ))) := by
    calc
      _ ≤ (Real.exp (-(1 / (100 * (H : ℝ))))) ^ d :=
        pow_le_pow_left₀ hrho (Real.one_sub_le_exp_neg _) d
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  calc
    _ ≤ ∑ i, ‖α i ^ d‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin m, (1 - 1 / (100 * (H : ℝ))) ^ d := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (hα i) d
    _ = (m : ℝ) * (1 - 1 / (100 * (H : ℝ))) ^ d := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hpow (by positivity)

end Erdos157.Elementary.ElementaryCharacterBound
