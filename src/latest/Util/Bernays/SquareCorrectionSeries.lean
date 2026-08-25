import Util.Bernays.SquareSupportArithmetic
import Mathlib.Data.Nat.Sqrt
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.LSeries.Deriv

/-!
# Absolute convergence of the square-support correction on `re s > 1/2`
-/

open Filter Topology Asymptotics
open scoped Classical

namespace Bernays

theorem squareSupportAF_norm_cumsum_le (S : ℕ → Prop) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, ‖squareSupportAF S n‖) ≤ Real.sqrt (N : ℝ) + 1 := by
  let P : ℕ → Prop := fun n => 0 < n ∧ ParityAdmissible (fun _ => True) n ∧ PrimeSupported S n
  let T := (Finset.Icc 1 N).filter P
  have hsum : (∑ n ∈ Finset.Icc 1 N, ‖squareSupportAF S n‖) = (T.card : ℝ) := by
    have hnorm (n : ℕ) : ‖squareSupportAF S n‖ = if P n then (1 : ℝ) else 0 := by
      rw [squareSupportAF_eq]
      change ‖if P n then (1 : ℂ) else 0‖ = _
      split_ifs <;> simp
    simp_rw [hnorm]
    convert Finset.sum_boole (R := ℝ) P (Finset.Icc 1 N) using 1 <;> congr
  have hsquare (n : ℕ) (hn : n ∈ T) : Nat.sqrt n ^ 2 = n := by
    have hp := (Finset.mem_filter.mp hn).2
    exact (Nat.exists_mul_self' n).mp (parity_all_primes_isSquare hp.1 hp.2.1)
  have hinj : Set.InjOn Nat.sqrt T := by
    intro n hn m hm hnm
    exact (hsquare n hn).symm.trans ((congrArg (fun k : ℕ => k ^ 2) hnm).trans (hsquare m hm))
  have hsub : T.image Nat.sqrt ⊆ Finset.range (Nat.sqrt N + 1) := by
    intro r hr
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hr
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le
      (Nat.sqrt_le_sqrt (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).2))
  have hcard : T.card ≤ Nat.sqrt N + 1 := by
    rw [← Finset.card_image_of_injOn hinj]
    exact (Finset.card_le_card hsub).trans_eq (Finset.card_range _)
  have hsqrt : (Nat.sqrt N : ℝ) ≤ Real.sqrt (N : ℝ) := by
    apply (Real.le_sqrt (Nat.cast_nonneg _) (Nat.cast_nonneg _)).mpr
    exact_mod_cast Nat.sqrt_le' N
  rw [hsum]
  have hc : (T.card : ℝ) ≤ Nat.sqrt N + 1 := by exact_mod_cast hcard
  linarith

theorem squareSupportAF_summable (S : ℕ → Prop) {s : ℂ} (hs : (1 / 2 : ℝ) < s.re) :
    LSeriesSummable (squareSupportAF S) s := by
  have hO : (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, ‖squareSupportAF S n‖)
      =O[atTop] fun N : ℕ => (N : ℝ) ^ (1 / 2 : ℝ) := by
    apply IsBigO.of_bound 2
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hsqrt : (1 : ℝ) ≤ Real.sqrt (N : ℝ) := by
      apply (Real.le_sqrt (by norm_num) (Nat.cast_nonneg N)).mpr
      exact_mod_cast hN
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _)),
      Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _), ← Real.sqrt_eq_rpow]
    exact (squareSupportAF_norm_cumsum_le S N).trans (by linarith)
  exact LSeriesSummable_of_sum_norm_bigO hO (by norm_num) hs

theorem squareSupportLSeries_differentiableAt (S : ℕ → Prop) {s : ℂ}
    (hs : (1 / 2 : ℝ) < s.re) : DifferentiableAt ℂ (LSeries (squareSupportAF S)) s := by
  have hab : LSeries.abscissaOfAbsConv (squareSupportAF S) ≤ (1 / 2 : ℝ) :=
    LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable (fun x hx =>
      squareSupportAF_summable S (by simpa only [Complex.ofReal_re] using hx))
  exact (LSeries_hasDerivAt (hab.trans_lt (by exact_mod_cast hs))).differentiableAt

end Bernays
