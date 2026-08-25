import Util.Linnik.FamilyMoment
import Util.Linnik.FamilyKernel
import Util.Linnik.ExceptionalMainTerm
import Util.Linnik.PrincipalPowerScale
import Util.Linnik.PowerErrors
import Util.Linnik.Progression

/-!
# Linnik's theorem for the residue class one

Log-free density, exceptional-zero repulsion, and the explicit formula
give a positive theta sum at one fixed polynomial endpoint.  The finite
initial segment is absorbed in an absolute multiplicative constant.
-/

namespace Linnik

open Filter Complex Erdos48 BoundedGaps.Maynard
open scoped BigOperators Classical

local instance {Q : ℕ} (q : ↥(Finset.Ioc 1 Q)) : NeZero q.val :=
  ⟨by have hq := (Finset.mem_Ioc.mp q.property).1; omega⟩

theorem exists_fullFamily_endpoint_bound :
    ∃ K : ℕ, 1 ≤ K ∧ ∀ Q T x : ℕ, 2 ≤ T → 4 ≤ x → T ≤ x →
      (∑ q ∈ Finset.Ioc 1 Q, primitiveEndpointMass x q) ≤
        (Q : ℝ) ^ 2 * ((K : ℝ) * dirichletExplicitFormulaErrorScale x Q T) +
          ∑ q ∈ Finset.Ioc 1 Q, ∑ psi : primitiveCharacters q,
            ‖primitiveZeroKernelSumAt q psi x T‖ := by
  obtain ⟨K, hK, hbound⟩ := exists_nat_sum_nonexcluded_primitiveEndpointMass_le
  refine ⟨K, hK, ?_⟩
  intro Q T x hT hx hTx
  have hfilter : (Finset.Ioc 1 Q).filter (fun q ↦ q ≠ 0) = Finset.Ioc 1 Q := by
    apply Finset.filter_eq_self.mpr
    intro q hq
    have h := (Finset.mem_Ioc.mp hq).1
    omega
  simpa only [nonexcludedPrimitiveZeroKernelMass, hfilter] using hbound Q T x 0 hT hx hTx

theorem exists_eventual_polynomial_prime_bound :
    ∃ L : ℕ, 1 ≤ L ∧ ∀ᶠ n : ℕ in atTop,
      ∃ p : ℕ, p.Prime ∧ n ∣ p - 1 ∧ p ≤ n ^ L := by
  obtain ⟨kappa, H₀, D, hkappa, hkappa₁, hH₀, hD, hfamily⟩ :=
    exists_family_moment_bounds (by norm_num : (0 : ℝ) < 1 / 512)
  obtain ⟨R, hR, hprincipal⟩ := exists_principal_powerScale_exceptional_error
  obtain ⟨K, hK, hendpoint⟩ := exists_fullFamily_endpoint_bound
  obtain ⟨A, hA, hfar⟩ := exists_nat_primitiveFarZeroKernelMass_le
  obtain ⟨L, hL⟩ := exists_nat_ge (max (64 : ℝ) (max (6 * D) (6 * R)))
  have hL₆₄ : 64 ≤ L := by exact_mod_cast (le_max_left (64 : ℝ) _).trans hL
  have hLD : 6 * D ≤ L := (le_max_left _ _).trans ((le_max_right (64 : ℝ) _).trans hL)
  have hLR : 6 * R ≤ L := (le_max_right _ _).trans ((le_max_right (64 : ℝ) _).trans hL)
  have hL₁ : 1 ≤ L := by omega
  refine ⟨L, hL₁, ?_⟩
  have hpr := hprincipal L hL₆₄ hLR (1 / 64) (by norm_num)
  have hpnt := eventually_abs_psi_pow_sub_mul_logScale_sq_le
    (by norm_num : (0 : ℝ) < 1 / 64) hL₁
  have herr := eventually_powerScale_analyticErrors_le K A L hL₆₄
    (by norm_num : (0 : ℝ) < 1 / 64)
  have hcorr := eventually_powerScale_progressionCorrection_le L (by omega)
    (by norm_num : (0 : ℝ) < 1 / 64)
  filter_upwards [hpr, hpnt, herr, hcorr, eventually_uniform_quadratic_real_zero_gap,
    tendsto_logScale.eventually_ge_atTop H₀, eventually_ge_atTop 2]
    with n hpr hpnt herr hcorr heffective hH hn
  let x : ℝ := ((n ^ L : ℕ) : ℝ)
  let T : ℝ := ((n ^ 4 : ℕ) : ℝ)
  let H : ℝ := logScale n
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hn₀ : (0 : ℝ) < n := by linarith
  have hx : 4 ≤ n ^ L := by
    calc
      4 = 2 ^ 2 := by norm_num
      _ ≤ n ^ 2 := Nat.pow_le_pow_left hn 2
      _ ≤ n ^ L := Nat.pow_le_pow_right (by omega) (by omega)
  have hxR : 4 ≤ x := by dsimp [x]; exact_mod_cast hx
  have hx₁ : 1 ≤ x := by linarith
  have hx₀ : 0 < x := by linarith
  have hT : 2 ≤ n ^ 4 := hn.trans (Nat.le_pow (by norm_num))
  have hT₀ : 0 ≤ T := by dsimp [T]; positivity
  have hT₂ : 2 ≤ T := by dsimp [T]; exact_mod_cast hT
  have hTx : n ^ 4 ≤ n ^ L := Nat.pow_le_pow_right (by omega) (by omega)
  have hH₁₆ : 16 ≤ H := hH₀.trans hH
  have hH₀' : 0 ≤ H := by linarith
  have hlogeq : Real.log ((n : ℝ) * (T + 2)) = H := by simp only [T, H, logScale, Nat.cast_pow]
  have hscale : D * H ≤ Real.log x := logScale_mul_le_log_pow hn (by linarith) hLD
  have hHx : H ≤ Real.log x := (le_mul_of_one_le_left hH₀' hD).trans hscale
  have hlogx : 4 ≤ Real.log x := by linarith
  have hfam := hfamily n (n ^ 4) hn hT (by rw [hlogeq]; exact hH)
  rw [hlogeq] at hfam
  change ((∀ i : upperHighZeroIndex n T, kappa < H * upperHighZeroGap i) →
      (∑ i : upperHighZeroIndex n T, upperHighZeroWeight i *
        Real.exp (-D * (H * upperHighZeroGap i))) ≤ 1 / 512) ∧
    (∀ i₀ : upperHighZeroIndex n T, H * upperHighZeroGap i₀ ≤ kappa →
      i₀.2.1.1 ^ 2 = 1 ∧ i₀.2.2.val.im = 0 ∧ upperHighZeroWeight i₀ = 1 ∧
      (∑ i ∈ (Finset.univ : Finset (upperHighZeroIndex n T)).erase i₀,
        upperHighZeroWeight i * Real.exp (-D * (H * upperHighZeroGap i))) ≤
          (1 / 512) * (H * upperHighZeroGap i₀)) at hfam
  have hfarN := hfar n hn T hT₂ x (1 / 16) 0 hxR (by norm_num)
  norm_num only [Nat.zero_add, Nat.cast_one, one_mul,
    show (1 - 1 / 16 : ℝ) = 15 / 16 by norm_num] at hfarN
  rw [hlogeq] at hfarN
  have hmass := hendpoint n (n ^ 4) (n ^ L) hT hx hTx
  have hlower := totient_mul_thetaProgression_lower (x := n ^ L) (q := n)
    (by omega) (by omega) (Nat.coprime_one_left n)
  have hphi : 0 < (n.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < n)
  have hsmall : (1 / 64 : ℝ) * x / n ≤ x / 64 := by
    have h := div_le_self (show 0 ≤ (1 / 64 : ℝ) * x by positivity) hnR
    nlinarith only [h]
  by_cases hex : ∃ i₀ : upperHighZeroIndex n T, H * upperHighZeroGap i₀ ≤ kappa
  · obtain ⟨i₀, hi₀⟩ := hex
    obtain ⟨hsquare, him, hweight, hmoment⟩ := hfam.2 i₀ hi₀
    let beta : ℝ := i₀.2.2.val.re
    let lambda : ℝ := H * (1 - beta)
    have hdata := upperHighZero_zero_data hT₀ i₀
    have hbeta₀ : 0 < beta := hdata.2.1
    have hbeta₁ : beta < 1 := hdata.2.2.1
    have hbetaHalf : 1 / 2 ≤ beta := by
      have h := (upperHighZeroGap_bounds hT₀ i₀).2
      dsimp [upperHighZeroGap, beta] at h ⊢
      linarith
    have hrho : i₀.2.2.val = (beta : ℂ) := by apply Complex.ext <;> simp [beta, him]
    have hzero : DirichletCharacter.LFunction i₀.2.1.1 (beta : ℂ) = 0 := by
      rw [← hrho]
      exact hdata.1
    have hiq := Finset.mem_Ioc.mp i₀.1.property
    have hchi := primitiveCharacter_ne_one_of_one_lt hiq.1 i₀.2.1
    have hpsi := hpr i₀.1.val hiq.1 hiq.2 i₀.2.1.1 hchi hsquare
      beta hbeta₀ hbeta₁ hzero
    have hgap := heffective i₀.1.val hiq.1 hiq.2 i₀.2.1.1 hchi hsquare
      beta hbeta₁.le hzero
    have hlambda₀ : 0 < lambda := mul_pos (by linarith) (sub_pos.mpr hbeta₁)
    have hlambda₁ : lambda ≤ 1 := hi₀.trans hkappa₁
    have hlambdaLow : 1 / (n : ℝ) ≤ lambda := by
      dsimp [lambda]
      nlinarith only [hgap, hH₁₆, one_div_pos.mpr hn₀]
    have hsmall' : (1 / 64 : ℝ) * x / n ≤ x * lambda / 64 := by
      calc
        _ = (x / 64) * (1 / (n : ℝ)) := by ring
        _ ≤ (x / 64) * lambda := mul_le_mul_of_nonneg_left hlambdaLow (by positivity)
        _ = _ := by ring
    have hk := sum_primitiveKernel_norm_le_exceptional_moment_add_far hx₁ hT₀ hscale
      i₀ him hweight hmoment
    have hmass' : (∑ q ∈ Finset.Ioc 1 n, primitiveEndpointMass (n ^ L) q) ≤
        ‖dirichletExplicitFormulaKernel x (beta : ℂ)‖ + x * lambda / 64 +
          (1 / 64 : ℝ) * x / n := by
      dsimp [lambda, beta]
      dsimp [upperHighZeroGap] at hk
      nlinarith only [hmass, hk, hfarN, herr]
    have hmain := mainTerm_sub_exceptionalKernel_ge hx₁ hlogx hbetaHalf hbeta₁.le
    have hmin : lambda ≤ min 1 ((1 - beta) * Real.log x) := by
      refine le_min hlambda₁ ?_
      have h := mul_le_mul_of_nonneg_left hHx (sub_nonneg.mpr hbeta₁.le)
      dsimp [lambda]
      nlinarith only [h]
    have hmain' : x * lambda / 4 ≤ x - ‖dirichletExplicitFormulaKernel x (beta : ℂ)‖ := by
      have h := mul_le_mul_of_nonneg_left hmin (show 0 ≤ x / 4 by positivity)
      nlinarith only [h, hmain]
    have hpositive : 0 < Chebyshev.psi x -
        (∑ q ∈ Finset.Ioc 1 n, primitiveEndpointMass (n ^ L) q) -
        (n : ℝ) * (Real.log ((n * n ^ L : ℕ) : ℝ) ^ 2 +
          (Chebyshev.psi x - Chebyshev.theta x)) := by
      have hpsilow := (abs_le.mp hpsi).1
      have hxlambda : 0 < x * lambda := mul_pos hx₀ hlambda₀
      nlinarith only [hpsilow, hxlambda, hmass', hmain', hsmall', hcorr]
    apply exists_prime_of_thetaProgression_pos
    have hproduct := hpositive.trans_le hlower
    nlinarith only [hproduct, hphi]
  · have hgap (i : upperHighZeroIndex n T) : kappa < H * upperHighZeroGap i :=
      lt_of_not_ge (fun hi ↦ hex ⟨i, hi⟩)
    have hk := sum_primitiveKernel_norm_le_moment_add_far hx₁ hT₀ hscale (hfam.1 hgap)
    have hmass' : (∑ q ∈ Finset.Ioc 1 n, primitiveEndpointMass (n ^ L) q) ≤
        x / 64 + (1 / 64 : ℝ) * x / n := by nlinarith only [hmass, hk, hfarN, herr]
    have hpsi : |Chebyshev.psi x - x| ≤ x / 64 := by
      have hsq : 1 ≤ H ^ 2 := by nlinarith only [hH₁₆]
      have h := mul_le_mul_of_nonneg_left hsq (abs_nonneg (Chebyshev.psi x - x))
      nlinarith only [h, hpnt]
    have hpositive : 0 < Chebyshev.psi x -
        (∑ q ∈ Finset.Ioc 1 n, primitiveEndpointMass (n ^ L) q) -
        (n : ℝ) * (Real.log ((n * n ^ L : ℕ) : ℝ) ^ 2 +
          (Chebyshev.psi x - Chebyshev.theta x)) := by
      have hpsilow := (abs_le.mp hpsi).1
      nlinarith only [hpsilow, hx₀, hmass', hsmall, hcorr]
    apply exists_prime_of_thetaProgression_pos
    have hproduct := hpositive.trans_le hlower
    nlinarith only [hproduct, hphi]

/-- Absolute polynomial bound for a prime congruent to one modulo every
positive natural modulus. -/
theorem exists_polynomial_prime_dvd_sub_one :
    ∃ C : ℝ, ∃ L : ℕ, 1 ≤ C ∧ 1 ≤ L ∧
      ∀ M : ℕ, 1 ≤ M →
        ∃ p : ℕ, p.Prime ∧ M ∣ p - 1 ∧ (p : ℝ) ≤ C * (M : ℝ) ^ L := by
  obtain ⟨L, hL, heventual⟩ := exists_eventual_polynomial_prime_bound
  have hreal : ∀ᶠ M : ℕ in atTop,
      ∃ p : ℕ, p.Prime ∧ M ∣ p - 1 ∧ (p : ℝ) ≤ (M : ℝ) ^ L := by
    filter_upwards [heventual] with M hM
    obtain ⟨p, hp, hdiv, hbound⟩ := hM
    exact ⟨p, hp, hdiv, by exact_mod_cast hbound⟩
  obtain ⟨C, hC, hbound⟩ := exists_uniform_prime_bound_of_eventually hreal
  exact ⟨C, L, hC, hL, hbound⟩

end Linnik
