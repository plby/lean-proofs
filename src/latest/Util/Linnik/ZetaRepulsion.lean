import Util.Linnik.CrossLevelRepulsion
import ErdosProblems.Erdos48.EndpointFarZero
import BoundedGaps.PrimeNumberTheorem.Analytic.StrongChebyshev

/-!
# The zeta contribution in the exceptional case

Repulsion also applies to the principal character.  Together with the
reciprocal-height zero count it gives a bound quadratic in the exceptional
gap.  This will be combined with the ordinary strong prime number theorem.
-/

namespace Linnik

open Complex Erdos48 BoundedGaps.Maynard
open scoped BigOperators Classical

theorem rpow_le_of_exp_repulsion
    {x sigma R H lambda : ℝ} (hx : 0 < x) (hsigma : sigma ≤ 1)
    (hscale : 2 * R * H ≤ Real.log x)
    (hrepulsion : Real.exp (-R * H * (1 - sigma)) ≤ lambda) :
    x ^ sigma ≤ x * lambda ^ 2 := by
  have hdelta : 0 ≤ 1 - sigma := sub_nonneg.mpr hsigma
  have hexp : Real.exp (-Real.log x * (1 - sigma)) ≤
      Real.exp (-R * H * (1 - sigma)) ^ 2 := by
    rw [← Real.exp_nat_mul, Real.exp_le_exp]
    norm_num only [Nat.cast_ofNat]
    nlinarith [mul_le_mul_of_nonneg_right hscale hdelta]
  have hpower : x ^ sigma = x * Real.exp (-Real.log x * (1 - sigma)) := by
    rw [Real.rpow_def_of_pos hx, ← Real.exp_log hx, ← Real.exp_add, Real.log_exp]
    congr 1
    ring
  rw [hpower]
  exact mul_le_mul_of_nonneg_left (hexp.trans
    (pow_le_pow_left₀ (Real.exp_pos _).le hrepulsion 2)) hx.le

theorem goldfeldCharactersDistinct_principal
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1) :
    goldfeldCharactersDistinct chi (1 : DirichletCharacter ℂ 1) := by
  let : NeZero (Nat.lcm q 1) := ⟨by simpa using NeZero.ne q⟩
  unfold goldfeldCharactersDistinct
  rw [DirichletCharacter.changeLevel_one]
  exact (DirichletCharacter.changeLevel_eq_one_iff _).not.mpr hchi

/-- The zeta zero kernel is bounded by a quadratic exceptional-gap term
and a far-left zero remainder, uniformly over conductor-height boxes. -/
theorem exists_zetaKernel_exceptional_bound :
    ∃ R C : ℝ, 1 ≤ R ∧ 1 ≤ C ∧
      ∀ (q Q : ℕ) [NeZero q], 1 < q → q ≤ Q →
        ∀ (chi : DirichletCharacter ℂ q), chi ≠ 1 → chi ^ 2 = 1 →
          ∀ beta : ℝ, 0 < beta → beta < 1 →
            DirichletCharacter.LFunction chi (beta : ℂ) = 0 →
            ∀ T x : ℝ, 2 ≤ T → 4 ≤ x →
              let H := Real.log ((Q : ℝ) * (T + 2))
              R * H ≤ Real.log x →
              ‖dirichletNontrivialZeroKernelSum (1 : DirichletCharacter ℂ 1) x T‖ ≤
                C * (x * (H * (1 - beta)) ^ 2 + x ^ (15 / 16 : ℝ)) * H ^ 2 := by
  obtain ⟨A, hA, hrepulsion⟩ := exists_crossLevel_exceptional_zero_repulsion
  obtain ⟨B, hB, hcount⟩ := exists_nat_dirichletNontrivialZeroReciprocalMultiplicitySum_le
  let R : ℝ := 16384 * A
  let b : ℝ := 262144 * A
  let C : ℝ := 96 * B * (b ^ 2 + 1)
  have hAreal : (37 : ℝ) ≤ A := by exact_mod_cast hA
  have hBreal : (37 : ℝ) ≤ B := by exact_mod_cast hB
  refine ⟨2 * R, C, ?_, ?_, ?_⟩
  · dsimp [R]; linarith
  · dsimp [C]; nlinarith [sq_nonneg b]
  intro q Q _ hq hqQ chi hchi hsquare beta hbeta₀ hbeta₁ hzero T x hT hx H hscale
  have hx₀ : 0 < x := by linarith
  have hQ : (1 : ℝ) ≤ Q := by exact_mod_cast (show 1 ≤ Q by omega)
  have hlog : Real.log (T + 2) ≤ H :=
    Real.log_le_log (by linarith) (by nlinarith)
  have hlog₀ : 0 ≤ Real.log (T + 2) := Real.log_nonneg (by linarith)
  have hH₀ : 0 ≤ H := hlog₀.trans hlog
  let lambda : ℝ := H * (1 - beta)
  let F : ℝ := x * (b * lambda) ^ 2 + x ^ (15 / 16 : ℝ)
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hpoint (rho : ℂ) (hrho : rho ∈
      dirichletNontrivialLFunctionZerosFinset (1 : DirichletCharacter ℂ 1) T) :
      ‖dirichletExplicitFormulaKernel x rho‖ ≤ 12 * F / (1 + |rho.im|) := by
    obtain ⟨hz, hheight⟩ := mem_dirichletNontrivialLFunctionZerosFinset_iff.mp hrho
    rw [abs_of_nonneg (by linarith : 0 ≤ T)] at hheight
    by_cases hre : (15 / 16 : ℝ) ≤ rho.re
    · have hrep := hrepulsion q 1 Q hq hqQ (by omega) chi 1 hchi hsquare
        beta hbeta₀ hbeta₁ hzero T (by linarith) rho hheight hz.2.1 hz.2.2 hz.1
        (Or.inl (goldfeldCharactersDistinct_principal chi hchi))
      have hrep' : Real.exp (-R * H * (1 - rho.re)) ≤ b * lambda := by
        simpa only [R, b, lambda, H, neg_mul, mul_assoc] using hrep.le
      have hpow := rpow_le_of_exp_repulsion hx₀ hz.2.2.le hscale hrep'
      have hk := norm_dirichletExplicitFormulaKernel_le_of_re_le hx
        (by linarith : 1 / 2 ≤ rho.re) hz.2.1 le_rfl
      apply hk.trans
      apply div_le_div_of_nonneg_right _ (by positivity)
      dsimp [F]
      have : 0 ≤ x ^ (15 / 16 : ℝ) := by positivity
      nlinarith
    · have hk := norm_dirichletExplicitFormulaKernel_le_of_re_le hx
        (by norm_num : (1 / 2 : ℝ) ≤ 15 / 16) hz.2.1 (le_of_not_ge hre)
      apply hk.trans
      apply div_le_div_of_nonneg_right _ (by positivity)
      dsimp [F]
      nlinarith [mul_nonneg hx₀.le (sq_nonneg (b * lambda))]
  have hsum : ‖dirichletNontrivialZeroKernelSum (1 : DirichletCharacter ℂ 1) x T‖ ≤
      12 * F * dirichletNontrivialZeroReciprocalMultiplicitySum
        (1 : DirichletCharacter ℂ 1) T := by
    unfold dirichletNontrivialZeroKernelSum dirichletNontrivialZeroReciprocalMultiplicitySum
    apply (norm_sum_le _ _).trans
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro rho hrho
    rw [norm_mul, Complex.norm_natCast]
    have h := mul_le_mul_of_nonneg_left (hpoint rho hrho)
      (Nat.cast_nonneg (α := ℝ) (analyticOrderNatAt
        (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1)) rho))
    convert h using 1 <;> ring
  have hcount' : dirichletNontrivialZeroReciprocalMultiplicitySum
      (1 : DirichletCharacter ℂ 1) T ≤ 8 * B * H ^ 2 := by
    have h := hcount 1 1 T hT
    norm_num only [Nat.cast_one, one_mul] at h
    exact h.trans (mul_le_mul_of_nonneg_left ((sq_le_sq₀ hlog₀ hH₀).mpr hlog) (by positivity))
  apply hsum.trans
  calc
    12 * F * dirichletNontrivialZeroReciprocalMultiplicitySum
        (1 : DirichletCharacter ℂ 1) T ≤ 12 * F * (8 * B * H ^ 2) :=
      mul_le_mul_of_nonneg_left hcount' (by positivity)
    _ = 96 * B * F * H ^ 2 := by ring
    _ ≤ C * (x * lambda ^ 2 + x ^ (15 / 16 : ℝ)) * H ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg H)
      dsimp [C]
      rw [mul_assoc (96 * (B : ℝ))]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      dsimp [F]
      nlinarith [mul_nonneg hx₀.le (sq_nonneg lambda),
        mul_nonneg (sq_nonneg b) (show 0 ≤ x ^ (15 / 16 : ℝ) by positivity)]

end Linnik
