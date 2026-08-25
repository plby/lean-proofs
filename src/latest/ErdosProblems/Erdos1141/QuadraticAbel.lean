import ErdosProblems.Erdos1141.ConvolutionMean
import ErdosProblems.Erdos1141.SquareRootAbel

/-!
# Removing the pole from the quadratic zeta convolution

Subtracting `L(1, χ)` from the coefficients gives square-root cancellation.
Its Abel continuation is `ζ(s) * (L(s, χ) - L(1, χ))`, with the removable
singularity at one filled in by the derivative of `L`.
-/

open Complex Filter MeasureTheory Set
open scoped BigOperators Real Topology

namespace Erdos1141

noncomputable def centeredZetaCoefficients {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (n : ℕ) : ℂ :=
  χ.zetaMul n - χ.LFunction 1 * (ArithmeticFunction.zeta n : ℂ)

@[simp]
lemma centeredZetaCoefficients_zero {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    centeredZetaCoefficients χ 0 = 0 := by simp [centeredZetaCoefficients]

lemma centeredZetaCoefficients_prefix {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (X : ℕ) :
    (∑ n ∈ Finset.Icc 1 X, centeredZetaCoefficients χ n) =
      (∑ n ∈ Finset.Icc 1 X, χ.zetaMul n) - (X : ℂ) * χ.LFunction 1 := by
  simp only [centeredZetaCoefficients, Finset.sum_sub_distrib]
  congr 1
  have hz : ∀ n ∈ Finset.Icc 1 X,
      χ.LFunction 1 * (ArithmeticFunction.zeta n : ℂ) = χ.LFunction 1 := by
    intro n hn
    have hn0 : n ≠ 0 := by have := (Finset.mem_Icc.mp hn).1; omega
    simp only [ArithmeticFunction.zeta_apply, hn0, if_false, Nat.cast_one, mul_one]
  rw [Finset.sum_congr rfl hz]
  simp

noncomputable def centeredZetaLFunction {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) : ℂ → ℂ :=
  Function.update (fun s ↦ riemannZeta s * (χ.LFunction s - χ.LFunction 1)) 1
    (deriv χ.LFunction 1)

lemma centeredZetaLFunction_of_ne_one {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : s ≠ 1) :
    centeredZetaLFunction χ s = riemannZeta s * (χ.LFunction s - χ.LFunction 1) :=
  Function.update_of_ne hs _ _

lemma differentiableAt_centeredZetaLFunction_of_ne_one {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : s ≠ 1) :
    DifferentiableAt ℂ (centeredZetaLFunction χ) s := by
  apply DifferentiableAt.congr_of_eventuallyEq
  · exact (differentiableAt_riemannZeta hs).mul
      ((χ.differentiableAt_LFunction s (.inl hs)).sub_const (χ.LFunction 1))
  · filter_upwards [eventually_ne_nhds hs] with t ht
    exact centeredZetaLFunction_of_ne_one χ ht

lemma differentiable_centeredZetaLFunction {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) : Differentiable ℂ (centeredZetaLFunction χ) := by
  intro s
  rcases ne_or_eq s 1 with hs | rfl
  · exact differentiableAt_centeredZetaLFunction_of_ne_one χ hs
  refine (analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ ?_).differentiableAt
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact differentiableAt_centeredZetaLFunction_of_ne_one χ ht
  · let G := Function.update (fun s : ℂ ↦ (s - 1) * riemannZeta s) 1 1
    let H := Function.update (fun s : ℂ ↦ (χ.LFunction s - χ.LFunction 1) / (s - 1)) 1
      (deriv χ.LFunction 1)
    have hid : centeredZetaLFunction χ = G * H := by
      ext t
      rcases eq_or_ne t 1 with rfl | ht
      · simp [centeredZetaLFunction, G, H]
      · simp only [centeredZetaLFunction, G, H, Function.update_of_ne ht, Pi.mul_apply]
        field_simp
    rw [hid]
    apply ContinuousAt.mul
    · simpa only [G, continuousAt_update_same] using riemannZeta_residue_one
    · exact (χ.differentiableAt_LFunction 1 (.inr hχ)).hasDerivAt.continuousAt_div

lemma LSeriesSummable_centeredZetaCoefficients {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 < s.re) : LSeriesSummable (centeredZetaCoefficients χ) s := by
  change LSeriesSummable ((χ.zetaMul : ℕ → ℂ) -
    χ.LFunction 1 • (fun n ↦ (ArithmeticFunction.zeta n : ℂ))) s
  exact (χ.LSeriesSummable_zetaMul hs).sub
    ((ArithmeticFunction.LSeriesSummable_zeta_iff.mpr hs).smul (χ.LFunction 1))

lemma LSeries_zetaMul {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    LSeries χ.zetaMul s = riemannZeta s * χ.LFunction s := by
  have hχsum : LSeriesSummable (toArithmeticFunction (fun n ↦ χ (n : ZMod q))) s := by
    refine LSeriesSummable_of_bounded_of_one_lt_re (m := 1) (fun n hn ↦ ?_) hs
    simpa only [toArithmeticFunction, ArithmeticFunction.coe_mk, hn, if_false]
      using χ.norm_le_one (n : ZMod q)
  have hzcoe : ((ArithmeticFunction.zeta : ArithmeticFunction ℂ) : ℕ → ℂ) =
      (fun n ↦ (ArithmeticFunction.zeta n : ℂ)) := by
    funext n
    exact ArithmeticFunction.natCoe_apply
  have hzsum : LSeriesSummable (ArithmeticFunction.zeta : ArithmeticFunction ℂ) s := by
    rw [hzcoe]
    exact ArithmeticFunction.LSeriesSummable_zeta_iff.mpr hs
  have hprod := ArithmeticFunction.LSeries_mul'
    (f := (ArithmeticFunction.zeta : ArithmeticFunction ℂ))
    (g := toArithmeticFunction (fun n ↦ χ (n : ZMod q))) hzsum hχsum
  change LSeries χ.zetaMul s = _ at hprod
  rw [hprod]
  have hz : LSeries (ArithmeticFunction.zeta : ArithmeticFunction ℂ) s = riemannZeta s := by
    rw [hzcoe]
    exact ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs
  rw [hz, χ.LFunction_eq_LSeries hs]
  congr 1
  exact LSeries_congr (fun hn ↦ (χ.apply_eq_toArithmeticFunction_apply hn).symm) s

lemma centeredZetaLFunction_eq_LSeries {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 < s.re) :
    centeredZetaLFunction χ s = LSeries (centeredZetaCoefficients χ) s := by
  have hsne : s ≠ 1 := by intro h; simp only [h, one_re] at hs; linarith
  rw [centeredZetaLFunction_of_ne_one χ hsne]
  change riemannZeta s * (χ.LFunction s - χ.LFunction 1) =
    LSeries ((χ.zetaMul : ℕ → ℂ) - χ.LFunction 1 • (fun n ↦ (ArithmeticFunction.zeta n : ℂ))) s
  rw [LSeries_sub (χ.LSeriesSummable_zetaMul hs)
    ((ArithmeticFunction.LSeriesSummable_zeta_iff.mpr hs).smul (χ.LFunction 1))]
  rw [LSeries_smul, LSeries_zetaMul χ hs, ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs]
  ring

theorem centeredZetaLFunction_eq_abelIntegral {q : ℕ} [NeZero q]
    (hq : 1 < q) (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (s : ℂ) (hs : 1 / 2 < s.re) :
    centeredZetaLFunction χ s = s * ∫ y in Ioi (1 : ℝ),
      (∑ k ∈ Finset.Icc 1 ⌊y⌋₊, centeredZetaCoefficients χ k) * (y : ℂ) ^ (-(s + 1)) := by
  have hlog : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast hq.le)
  apply eq_abelIntegral_of_sqrt_prefix _ _
    (1 + 16 * Real.sqrt (q : ℝ) * Real.log (q : ℝ)) (by positivity)
  · intro n
    rw [centeredZetaCoefficients_prefix]
    exact norm_zetaMul_prefix_sub_main_le_sqrt hq χ hχ n
  · exact differentiable_centeredZetaLFunction χ hχ
  · exact fun s hs ↦ LSeriesSummable_centeredZetaCoefficients χ hs
  · exact fun s hs ↦ centeredZetaLFunction_eq_LSeries χ hs
  · exact hs

end Erdos1141
