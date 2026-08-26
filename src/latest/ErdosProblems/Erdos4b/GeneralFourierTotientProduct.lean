/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierTotientFactor
import ErdosProblems.Erdos4b.GeneralFourierSingularProduct
import ErdosProblems.Erdos4b.GeneralFourierRelativeProduct

/-!
# Uniform infinite products of the totient corrections

All local numerators may vary with the arithmetic data and the Fourier
frequencies. A fixed bound on them gives the explicit product error
`exp (8 * A / w) - 1` and convergence to one.
-/

namespace Erdos4b

noncomputable section

open Filter
open scoped BigOperators Topology

def roughTotientFourierCorrection (w : ℕ) (a : ℕ → ℂ) (p : ℕ) : ℂ :=
  if w < p then totientFourierLocalCorrection p (a p) else 1

theorem summable_norm_roughTotientFourierCorrection_sub_one
    (a : ℕ → ℂ) {w : ℕ} {A : ℝ} (hA : 0 ≤ A) (hw : 2 * A ≤ w)
    (ha : ∀ p : Nat.Primes, w < p → ‖a p‖ ≤ A) :
    Summable (fun p : Nat.Primes ↦ ‖roughTotientFourierCorrection w a p - 1‖) := by
  apply Summable.of_nonneg_of_le (fun p ↦ norm_nonneg _) _
    (summable_prime_reciprocalSquare.mul_left (4 * A))
  intro p
  by_cases hwp : w < p.val
  · simp only [roughTotientFourierCorrection, if_pos hwp]
    simpa only [mul_one_div] using norm_totientFourierLocalCorrection_sub_one_le
      (by exact_mod_cast p.property.two_le) (hw.trans (by exact_mod_cast hwp.le)) (ha p hwp)
  · simp only [roughTotientFourierCorrection, if_neg hwp, sub_self, norm_zero]
    positivity

theorem multipliable_roughTotientFourierCorrection
    (a : ℕ → ℂ) {w : ℕ} {A : ℝ} (hA : 0 ≤ A) (hw : 2 * A ≤ w)
    (ha : ∀ p : Nat.Primes, w < p → ‖a p‖ ≤ A) :
    Multipliable (fun p : Nat.Primes ↦ roughTotientFourierCorrection w a p) := by
  simpa only [add_sub_cancel] using multipliable_one_add_of_summable
    (summable_norm_roughTotientFourierCorrection_sub_one a hA hw ha)

theorem sum_norm_roughTotientFourierCorrection_sub_one_le
    (a : ℕ → ℂ) {w : ℕ} {A : ℝ} (hA : 0 ≤ A) (hw0 : 0 < w) (hw : 2 * A ≤ w)
    (ha : ∀ p : Nat.Primes, w < p → ‖a p‖ ≤ A) (Q : Finset Nat.Primes) :
    (∑ p ∈ Q, ‖roughTotientFourierCorrection w a p - 1‖) ≤ 8 * A / w := by
  classical
  let R := Q.filter fun p : Nat.Primes ↦ w < p.val
  let P := R.image (fun p : Nat.Primes ↦ p.val)
  have hrough : ∀ p ∈ P, w < p := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    exact (Finset.mem_filter.mp hq).2
  calc
    _ = ∑ p ∈ R, ‖totientFourierLocalCorrection p (a p) - 1‖ := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro p hp
      by_cases hwp : w < p.val <;> simp [roughTotientFourierCorrection, hwp]
    _ ≤ ∑ p ∈ R, 4 * A / (p : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro p hp
      have hwp := (Finset.mem_filter.mp hp).2
      exact norm_totientFourierLocalCorrection_sub_one_le
        (by exact_mod_cast p.property.two_le) (hw.trans (by exact_mod_cast hwp.le)) (ha p hwp)
    _ = ∑ p ∈ P, 4 * A / (p : ℝ) ^ 2 := by
      exact (Finset.sum_image (s := R) (g := fun p : Nat.Primes ↦ p.val)
        (f := fun p : ℕ ↦ 4 * A / (p : ℝ) ^ 2)
        (fun p hp q hq h ↦ Subtype.ext h)).symm
    _ = 4 * A * (∑ p ∈ P, (1 : ℝ) / (p : ℝ) ^ 2) := by
      simp only [Finset.mul_sum, mul_one_div]
    _ ≤ 4 * A * (2 / (w : ℝ)) := mul_le_mul_of_nonneg_left
      (finite_rough_reciprocalSquare_sum_le P hw0 hrough) (by positivity)
    _ = _ := by ring

theorem norm_tprod_roughTotientFourierCorrection_sub_one_le
    (a : ℕ → ℂ) {w : ℕ} {A : ℝ} (hA : 0 ≤ A) (hw0 : 0 < w) (hw : 2 * A ≤ w)
    (ha : ∀ p : Nat.Primes, w < p → ‖a p‖ ≤ A) :
    ‖(∏' p : Nat.Primes, roughTotientFourierCorrection w a p) - 1‖ ≤
      Real.exp (8 * A / w) - 1 := by
  have hlim : Tendsto (fun Q : Finset Nat.Primes ↦
      ∏ p ∈ Q, roughTotientFourierCorrection w a p) atTop
      (𝓝 (∏' p : Nat.Primes, roughTotientFourierCorrection w a p)) :=
    (multipliable_roughTotientFourierCorrection a hA hw ha).hasProd
  apply le_of_tendsto (hlim.sub_const 1).norm
  apply Eventually.of_forall
  intro Q
  have hsum := sum_norm_roughTotientFourierCorrection_sub_one_le a hA hw0 hw ha Q
  have hp := norm_prod_one_add_error_le Q
    (fun p : Nat.Primes ↦ roughTotientFourierCorrection w a p - 1)
  simp only [add_sub_cancel] at hp
  exact hp.trans (sub_le_sub_right (Real.exp_le_exp.mpr hsum) 1)

theorem tendsto_tprod_roughTotientFourierCorrection_one
    {α : Type*} {l : Filter α} (w : α → ℕ) (a : α → ℕ → ℂ) {A : ℝ}
    (hA : 0 ≤ A) (hw : Tendsto w l atTop)
    (ha : ∀ᶠ x in l, ∀ p : Nat.Primes, w x < p → ‖a x p‖ ≤ A) :
    Tendsto (fun x ↦ ∏' p : Nat.Primes, roughTotientFourierCorrection (w x) (a x) p)
      l (𝓝 1) := by
  have hwR : Tendsto (fun x ↦ (w x : ℝ)) l atTop := tendsto_natCast_atTop_atTop.comp hw
  have hrec : Tendsto (fun x ↦ 8 * A / (w x : ℝ)) l (𝓝 0) :=
    tendsto_const_nhds.div_atTop hwR
  have hexp : Tendsto (fun x ↦ Real.exp (8 * A / (w x : ℝ)) - 1) l (𝓝 0) := by
    simpa only [Function.comp_def, Real.exp_zero, sub_self] using
      ((Real.continuous_exp.tendsto 0).comp hrec).sub_const 1
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun x ↦ norm_nonneg _) _ hexp
  filter_upwards [ha, hw.eventually_ge_atTop 1, hwR.eventually_ge_atTop (2 * A)]
    with x hax hx0 hxA
  exact norm_tprod_roughTotientFourierCorrection_sub_one_le (a x) hA hx0 hxA hax

end

end Erdos4b
