import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.Basic
import Wikipedia.HopfProblem.TriangleHolomorphicDifferentialsPowerCoefficientsArithmetic

/-!
# Taylor coefficient support forced by root covariance

Scaling the input of an actual convergent power series multiplies its
degree-`n` coefficient by the corresponding `n`th power.  Uniqueness of
one-variable analytic power series therefore forces the support of a
root-covariant germ into the required congruence class.
-/

noncomputable section

open Filter
open scoped Topology

namespace Wikipedia.HopfProblem.TriangleHolomorphicDifferentials

/-- Germ covariance forces the actual Taylor coefficient identity,
without any assumption about coefficient support. -/
theorem powerSeries_coefficient_covariance
    {F : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ} {ζ : ℂ} {k : ℕ}
    (hp : HasFPowerSeriesAt F p 0)
    (hcov : ∀ᶠ s in 𝓝 0, F (ζ * s) * ζ ^ k = F s) (n : ℕ) :
    (ζ ^ (n + k) - 1) * p n (fun _ => 1) = 0 := by
  let u : ℂ →L[ℂ] ℂ := ζ • ContinuousLinearMap.id ℂ ℂ
  have hp' : HasFPowerSeriesAt F p (u 0) := by
    simpa only [map_zero] using hp
  have hrot := hp'.compContinuousLinearMap (u := u) (x := 0)
  have hscaled := hrot.const_smul (c := ζ ^ k)
  have hcov' : (ζ ^ k • (F ∘ u)) =ᶠ[𝓝 0] F := by
    filter_upwards [hcov] with s hs
    simpa only [Pi.smul_apply, Function.comp_apply, u, smul_apply,
      ContinuousLinearMap.id_apply, smul_eq_mul, mul_comm (ζ ^ k)] using hs
  have heq := hscaled.eq_formalMultilinearSeries_of_eventually hp hcov'
  have hn := congrArg (fun q : FormalMultilinearSeries ℂ ℂ ℂ => q n (fun _ => 1)) heq
  have hinput : p n (u ∘ (fun _ : Fin n => 1)) = ζ ^ n * p n (fun _ => 1) := by
    calc
      p n (u ∘ (fun _ : Fin n => 1)) = p n (fun _ => ζ) := by
        congr 1
        funext i
        simp [u]
      _ = ζ ^ n * p n (fun _ => 1) := by
        have hone : (1 : Fin n → ℂ) = (fun _ => 1) := by
          funext i
          rfl
        simpa only [smul_eq_mul, FormalMultilinearSeries.coeff, hone] using
          (FormalMultilinearSeries.apply_eq_pow_smul_coeff (p := p) (n := n) (z := ζ))
  have hcoef : ζ ^ k * (ζ ^ n * p n (fun _ => 1)) = p n (fun _ => 1) := by
    simpa only [FormalMultilinearSeries.smul_apply, smul_apply,
      FormalMultilinearSeries.compContinuousLinearMap_apply, hinput, smul_eq_mul] using hn
  rw [sub_mul, one_mul, pow_add, mul_comm (ζ ^ n) (ζ ^ k), mul_assoc, hcoef, sub_self]

/-- A primitive-root covariance relation makes every coefficient outside
the prescribed congruence class vanish. -/
theorem powerSeries_coefficient_eq_zero_of_not_dvd
    {F : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ} {ζ : ℂ} {m k : ℕ}
    (hζ : IsPrimitiveRoot ζ m) (hp : HasFPowerSeriesAt F p 0)
    (hcov : ∀ᶠ s in 𝓝 0, F (ζ * s) * ζ ^ k = F s)
    {n : ℕ} (hn : ¬ m ∣ n + k) : p n (fun _ => 1) = 0 := by
  have hne : ζ ^ (n + k) - 1 ≠ 0 := by
    intro hzero
    exact hn ((hζ.pow_eq_one_iff_dvd (n + k)).mp (sub_eq_zero.mp hzero))
  exact (mul_eq_zero.mp (powerSeries_coefficient_covariance hp hcov n)).resolve_left hne

/-- Coefficients below the least nonnegative permitted residue vanish. -/
theorem powerSeries_coefficient_eq_zero_of_lt_residue
    {F : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ} {ζ : ℂ} {m k r : ℕ}
    (hζ : IsPrimitiveRoot ζ m) (hp : HasFPowerSeriesAt F p 0)
    (hcov : ∀ᶠ s in 𝓝 0, F (ζ * s) * ζ ^ k = F s)
    (hrm : r < m) (hr : m ∣ r + k) {n : ℕ} (hnr : n < r) :
    p n (fun _ => 1) = 0 :=
  powerSeries_coefficient_eq_zero_of_not_dvd hζ hp hcov
    (TriangleHolomorphicDifferentialsPowerCoefficientsArithmetic.not_dvd_add_of_lt_residue
      hrm hr hnr)

/-- In weights `0 < k ≤ m`, all coefficients below `m - k` vanish. -/
theorem powerSeries_coefficient_eq_zero_of_lt_sub
    {F : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ} {ζ : ℂ} {m k : ℕ}
    (hζ : IsPrimitiveRoot ζ m) (hp : HasFPowerSeriesAt F p 0)
    (hcov : ∀ᶠ s in 𝓝 0, F (ζ * s) * ζ ^ k = F s)
    (hk : 0 < k) (hkm : k ≤ m) {n : ℕ} (hn : n < m - k) :
    p n (fun _ => 1) = 0 :=
  powerSeries_coefficient_eq_zero_of_not_dvd hζ hp hcov
    (TriangleHolomorphicDifferentialsPowerCoefficientsArithmetic.not_dvd_add_of_lt_sub hk hkm hn)

end Wikipedia.HopfProblem.TriangleHolomorphicDifferentials
