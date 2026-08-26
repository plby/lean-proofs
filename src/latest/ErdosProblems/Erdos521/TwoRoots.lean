/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Two roots force a small value unless the second-derivative energy is large.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.IntervalSquare
import ErdosProblems.Erdos521.EndpointCover

namespace Erdos521

open MeasureTheory Filter

theorem polynomial_sub_le_integral_abs_derivative (p : Polynomial ℝ) {a b x y : ℝ}
    (hx : x ∈ Set.Icc a b) (hy : y ∈ Set.Icc a b) :
    |p.eval y - p.eval x| ≤ ∫ t in a..b, |p.derivative.eval t| := by
  have hordered (u v : ℝ) (hu : u ∈ Set.Icc a b) (hv : v ∈ Set.Icc a b) (huv : u ≤ v) :
      |p.eval v - p.eval u| ≤ ∫ t in a..b, |p.derivative.eval t| := by
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ ↦ p.hasDerivAt t) (p.derivative.continuous.intervalIntegrable u v)
    have hnorm := intervalIntegral.norm_integral_le_integral_norm
      (μ := volume) (f := fun t ↦ p.derivative.eval t) huv
    rw [hFTC] at hnorm
    simp only [Real.norm_eq_abs] at hnorm
    exact hnorm.trans (intervalIntegral.integral_mono_interval hu.1 huv hv.2
      (Eventually.of_forall fun t ↦ abs_nonneg (p.derivative.eval t))
      (p.derivative.continuous.abs.intervalIntegrable a b))
  rcases le_total x y with h | h
  · exact hordered x y hx hy h
  · simpa only [abs_sub_comm] using hordered y x hy hx h

theorem two_roots_value_sq_le (p : Polynomial ℝ) {a b x y t : ℝ}
    (hx : x ∈ Set.Icc a b) (hy : y ∈ Set.Icc a b) (ht : t ∈ Set.Icc a b)
    (hxy : x < y) (hrootx : p.eval x = 0) (hrooty : p.eval y = 0) :
    (p.eval t) ^ 2 ≤ (b - a) ^ 3 * ∫ u in a..b, (p.derivative.derivative.eval u) ^ 2 := by
  obtain ⟨c, hc, hcderiv⟩ := exists_deriv_eq_zero hxy p.continuous.continuousOn
    (hrootx.trans hrooty.symm)
  rw [Polynomial.deriv] at hcderiv
  have hcI : c ∈ Set.Icc a b := ⟨hx.1.trans hc.1.le, hc.2.le.trans hy.2⟩
  have hab : a ≤ b := hx.1.trans hx.2
  let I := ∫ u in a..b, |p.derivative.derivative.eval u|
  have hI : 0 ≤ I := intervalIntegral.integral_nonneg_of_forall hab (fun _ ↦ abs_nonneg _)
  have hbound (u : ℝ) (hu : u ∈ Set.Icc a b) : ‖p.derivative.eval u‖ ≤ I := by
    have h := polynomial_sub_le_integral_abs_derivative p.derivative hcI hu
    simpa only [hcderiv, sub_zero, Real.norm_eq_abs] using h
  have h := (convex_Icc a b).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun u _ ↦ (p.hasDerivAt u).hasDerivWithinAt) hbound hx ht
  simp only [hrootx, sub_zero, Real.norm_eq_abs] at h
  have hdist : |t - x| ≤ b - a := abs_le.mpr
    ⟨by linarith [ht.1, hx.2], by linarith [ht.2, hx.1]⟩
  have hvalue : |p.eval t| ≤ I * (b - a) := h.trans (mul_le_mul_of_nonneg_left hdist hI)
  have hsq := interval_integral_sq_le (fun u ↦ |p.derivative.derivative.eval u|)
    p.derivative.derivative.continuous.abs hab
  simp only [sq_abs] at hsq
  calc
    (p.eval t) ^ 2 = |p.eval t| ^ 2 := (sq_abs _).symm
    _ ≤ (I * (b - a)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hvalue 2
    _ = I ^ 2 * (b - a) ^ 2 := mul_pow _ _ _
    _ ≤ ((b - a) * ∫ u in a..b, (p.derivative.derivative.eval u) ^ 2) * (b - a) ^ 2 :=
      mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
    _ = _ := by ring

theorem two_interval_roots_value_sq_le (ε : ℕ → ℝ) (n : ℕ) {a b : ℝ}
    (hcount : 2 ≤ intervalRootCount ε n a b) :
    ((polynomial ε n).eval b) ^ 2 ≤ (b - a) ^ 3 *
      ∫ u in a..b, ((polynomial ε n).derivative.derivative.eval u) ^ 2 := by
  classical
  obtain ⟨x, hx, y, hy, hne⟩ := Finset.one_lt_card.mp (show 1 <
      ((realRoots ε n).filter fun x ↦ x ∈ Set.Icc a b).card by exact hcount)
  obtain ⟨hxroot, hxI⟩ := Finset.mem_filter.mp hx
  obtain ⟨hyroot, hyI⟩ := Finset.mem_filter.mp hy
  have hrootx : (polynomial ε n).eval x = 0 :=
    Polynomial.isRoot_of_mem_roots (Multiset.mem_toFinset.mp hxroot)
  have hrooty : (polynomial ε n).eval y = 0 :=
    Polynomial.isRoot_of_mem_roots (Multiset.mem_toFinset.mp hyroot)
  have hb : b ∈ Set.Icc a b := ⟨hxI.1.trans hxI.2, le_rfl⟩
  rcases lt_or_gt_of_ne hne with h | h
  · exact two_roots_value_sq_le (polynomial ε n) hxI hyI hb h hrootx hrooty
  · exact two_roots_value_sq_le (polynomial ε n) hyI hxI hb h hrooty hrootx

end Erdos521
