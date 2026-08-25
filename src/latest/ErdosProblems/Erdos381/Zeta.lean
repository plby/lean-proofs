import ErdosProblems.Erdos381.Core
import ErdosProblems.Erdos48.PointwiseZeroDetector
import ErdosProblems.Erdos48.LogDerivativeSeries
import ErdosProblems.Erdos48.SelectedZeroBandMass
import ErdosProblems.Erdos48.ZeroMultiplicityCover
import BoundedGaps.BombieriVinogradov.Analytic.RiemannZetaSelectedSubdivisor
import BoundedGaps.BombieriVinogradov.Analytic.RiemannZetaRadiusSixDivisorMass

namespace Erdos381

open Complex Metric Set
open BoundedGaps.Maynard
open Erdos48

noncomputable section

/-! A natural-valued package for the regularized-zeta divisor in the
fixed radius-six disk centered at `2 + it`. -/

noncomputable def zetaRadiusSixZeroMultiplicity
    (t : ℝ) : ℂ → ℕ := fun rho ↦
  if dist rho ((2 : ℂ) + t * I) ≤ 6 then
    analyticOrderNatAt riemannZeta₁ rho
  else 0

theorem zetaRadiusSixZeroMultiplicity_hasFiniteSupport (t : ℝ) :
    Function.HasFiniteSupport (zetaRadiusSixZeroMultiplicity t) := by
  apply (divisor_riemannZeta₁_closedBall_support_finite
    ((2 : ℂ) + t * I) 6).subset
  intro rho hrho
  rw [Function.mem_support] at hrho ⊢
  unfold zetaRadiusSixZeroMultiplicity at hrho
  split at hrho
  next hdist =>
    rw [divisor_riemannZeta₁_apply_eq_analyticOrderNatAt
      (mem_closedBall.mpr hdist)]
    exact_mod_cast hrho
  next hdist => exact False.elim (hrho rfl)

noncomputable def zetaRadiusSixZeroFinsupp (t : ℝ) : ℂ →₀ ℕ :=
  Finsupp.ofSupportFinite (zetaRadiusSixZeroMultiplicity t)
    (zetaRadiusSixZeroMultiplicity_hasFiniteSupport t)

@[simp] theorem zetaRadiusSixZeroFinsupp_apply (t : ℝ) (rho : ℂ) :
    zetaRadiusSixZeroFinsupp t rho =
      zetaRadiusSixZeroMultiplicity t rho := rfl

theorem zetaRadiusSixZeroFinsupp_apply_eq_divisor
    (t : ℝ) (rho : ℂ) :
    (zetaRadiusSixZeroFinsupp t rho : ℤ) =
      MeromorphicOn.divisor riemannZeta₁
        (closedBall ((2 : ℂ) + t * I) 6) rho := by
  rw [zetaRadiusSixZeroFinsupp_apply,
    zetaRadiusSixZeroMultiplicity]
  by_cases hdist : dist rho ((2 : ℂ) + t * I) ≤ 6
  · rw [if_pos hdist,
      divisor_riemannZeta₁_apply_eq_analyticOrderNatAt
        (mem_closedBall.mpr hdist)]
  · rw [if_neg hdist,
      Function.locallyFinsuppWithin.apply_eq_zero_of_notMem]
    · norm_cast
    · simpa [mem_closedBall] using hdist

theorem zetaRadiusSixZeroFinsupp_sum_eq_divisor_finsum (t : ℝ) :
    (zetaRadiusSixZeroFinsupp t).sum (fun _ m ↦ (m : ℤ)) =
      ∑ᶠ rho : ℂ,
        MeromorphicOn.divisor riemannZeta₁
          (closedBall ((2 : ℂ) + t * I) 6) rho := by
  let D := zetaRadiusSixZeroFinsupp t
  rw [Finsupp.sum]
  symm
  calc
    (∑ᶠ rho : ℂ,
        MeromorphicOn.divisor riemannZeta₁
          (closedBall ((2 : ℂ) + t * I) 6) rho) =
        ∑ rho ∈ D.support,
          MeromorphicOn.divisor riemannZeta₁
            (closedBall ((2 : ℂ) + t * I) 6) rho := by
      apply finsum_eq_sum_of_support_subset
      intro rho hrho
      rw [Function.mem_support] at hrho
      rw [Finset.mem_coe, Finsupp.mem_support_iff]
      intro hzero
      apply hrho
      rw [← zetaRadiusSixZeroFinsupp_apply_eq_divisor t rho,
        show zetaRadiusSixZeroFinsupp t rho = D rho by rfl,
        hzero]
      norm_num
    _ = ∑ rho ∈ D.support, (D rho : ℤ) := by
      apply Finset.sum_congr rfl
      intro rho hrho
      exact (zetaRadiusSixZeroFinsupp_apply_eq_divisor t rho).symm

theorem exists_zetaRadiusSixZeroFinsupp_mass_bound :
    ∃ A : ℕ, 37 ≤ A ∧ ∀ t : ℝ,
      (zetaRadiusSixZeroFinsupp t).sum
          (fun _ m ↦ (m : ℝ)) ≤
        2 * (A : ℝ) * Real.log (|t| + 2) := by
  obtain ⟨A, hA, hmass⟩ :=
    exists_nat_finsum_divisor_riemannZeta₁_radiusSix_le
  refine ⟨A, hA, ?_⟩
  intro t
  have heq := zetaRadiusSixZeroFinsupp_sum_eq_divisor_finsum t
  have hcast :
      (zetaRadiusSixZeroFinsupp t).sum
          (fun _ m ↦ (m : ℝ)) =
        (((∑ᶠ rho : ℂ,
          MeromorphicOn.divisor riemannZeta₁
            (closedBall ((2 : ℂ) + t * I) 6) rho : ℤ)) : ℝ) := by
    rw [← heq]
    push_cast
    rfl
  rw [hcast]
  exact hmass t

/-! The local radius-`4 eta` zero multiset used by Turan's detector. -/

noncomputable def zetaSmallDiskZeroMultiplicity
    (t eta : ℝ) : ℂ → ℕ := fun rho ↦
  if dist rho (((1 + eta : ℝ) : ℂ) + t * I) ≤ 4 * eta then
    analyticOrderNatAt riemannZeta₁ rho
  else 0

theorem zetaSmallDiskZeroMultiplicity_hasFiniteSupport (t eta : ℝ) :
    Function.HasFiniteSupport (zetaSmallDiskZeroMultiplicity t eta) := by
  let c : ℂ := ((1 + eta : ℝ) : ℂ) + t * I
  let D := MeromorphicOn.divisor riemannZeta₁ (closedBall c (4 * eta))
  have hD : D.support.Finite :=
    divisor_riemannZeta₁_closedBall_support_finite c (4 * eta)
  apply hD.subset
  intro rho hrho
  rw [Function.mem_support] at hrho ⊢
  unfold zetaSmallDiskZeroMultiplicity at hrho
  split at hrho
  next hdist =>
    have hrhoBall : rho ∈ closedBall c (4 * eta) := by
      simpa [c, mem_closedBall] using hdist
    rw [show D rho = (analyticOrderNatAt riemannZeta₁ rho : ℤ) by
      exact divisor_riemannZeta₁_apply_eq_analyticOrderNatAt hrhoBall]
    exact_mod_cast hrho
  next hdist => exact False.elim (hrho rfl)

noncomputable def zetaSmallDiskZeroFinsupp
    (t eta : ℝ) : ℂ →₀ ℕ :=
  Finsupp.ofSupportFinite (zetaSmallDiskZeroMultiplicity t eta)
    (zetaSmallDiskZeroMultiplicity_hasFiniteSupport t eta)

@[simp] theorem zetaSmallDiskZeroFinsupp_apply
    (t eta : ℝ) (rho : ℂ) :
    zetaSmallDiskZeroFinsupp t eta rho =
      zetaSmallDiskZeroMultiplicity t eta rho := rfl

theorem zetaSmallDiskZeroFinsupp_le_radiusSix
    (t eta : ℝ) (heta1 : eta ≤ 1) (rho : ℂ) :
    zetaSmallDiskZeroFinsupp t eta rho ≤
      if dist rho ((2 : ℂ) + t * I) ≤ 6 then
        analyticOrderNatAt riemannZeta₁ rho
      else 0 := by
  rw [zetaSmallDiskZeroFinsupp_apply]
  unfold zetaSmallDiskZeroMultiplicity
  split
  next hsmall =>
    have hcenters :
        dist (((1 + eta : ℝ) : ℂ) + t * I)
          ((2 : ℂ) + t * I) = 1 - eta := by
      rw [Complex.dist_eq]
      have heq :
          (((1 + eta : ℝ) : ℂ) + t * I) -
              ((2 : ℂ) + t * I) = ((eta - 1 : ℝ) : ℂ) := by
        push_cast
        ring
      rw [heq, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonpos (by linarith)]
      ring
    have hradius : dist rho ((2 : ℂ) + t * I) ≤ 6 := by
      calc
        dist rho ((2 : ℂ) + t * I) ≤
            dist rho (((1 + eta : ℝ) : ℂ) + t * I) +
              dist (((1 + eta : ℝ) : ℂ) + t * I)
                ((2 : ℂ) + t * I) := dist_triangle _ _ _
        _ ≤ 4 * eta + (1 - eta) := add_le_add hsmall hcenters.le
        _ ≤ 6 := by linarith
    simp [hradius]
  next hsmall => simp

theorem selected_zetaRadiusSix_subdivisor_sum_le_re_divisor_finsum
    (t : ℝ) (s : ℂ) (hs : 1 ≤ s.re) (Z : ℂ →₀ ℕ)
    (hZ : ∀ rho : ℂ,
      Z rho ≤ zetaRadiusSixZeroMultiplicity t rho) :
    Z.sum (fun rho m ↦
        (m : ℝ) * (((s - rho)⁻¹).re)) ≤
      (∑ᶠ rho : ℂ,
        ((MeromorphicOn.divisor riemannZeta₁
          (closedBall ((2 : ℂ) + t * I) 6) rho : ℤ) : ℂ) /
            (s - rho)).re := by
  let m : ℂ → ℕ := zetaRadiusSixZeroMultiplicity t
  have hm : (Function.support m).Finite :=
    zetaRadiusSixZeroMultiplicity_hasFiniteSupport t
  have hZsupport : Z.support ⊆ hm.toFinset := by
    intro rho hrho
    apply hm.mem_toFinset.mpr
    rw [Function.mem_support]
    intro hmrho
    have hZrho : Z rho = 0 :=
      Nat.eq_zero_of_le_zero ((hZ rho).trans_eq hmrho)
    exact Finsupp.mem_support_iff.mp hrho hZrho
  have hfullSupport :
      Function.support (fun rho : ℂ => (m rho : ℂ) / (s - rho)) ⊆
        hm.toFinset := by
    intro rho hrho
    apply hm.mem_toFinset.mpr
    rw [Function.mem_support] at hrho ⊢
    exact fun hmrho => hrho (by simp [hmrho])
  have hfullSum :
      (∑ᶠ rho : ℂ, (m rho : ℂ) / (s - rho)) =
        ∑ rho ∈ hm.toFinset, (m rho : ℂ) / (s - rho) :=
    finsum_eq_sum_of_support_subset
      (fun rho : ℂ => (m rho : ℂ) / (s - rho)) hfullSupport
  have hdivisor :
      (∑ᶠ rho : ℂ,
          ((MeromorphicOn.divisor riemannZeta₁
            (closedBall ((2 : ℂ) + t * I) 6) rho : ℤ) : ℂ) /
              (s - rho)) =
        ∑ᶠ rho : ℂ, (m rho : ℂ) / (s - rho) := by
    apply finsum_congr
    intro rho
    rw [← zetaRadiusSixZeroFinsupp_apply_eq_divisor t rho]
    change ((m rho : ℕ) : ℂ) / (s - rho) = _
    rfl
  rw [hdivisor, hfullSum, Complex.re_sum,
    Finsupp.sum_of_support_subset Z hZsupport _ (by simp)]
  apply Finset.sum_le_sum
  intro rho hrho
  by_cases hmrho : m rho = 0
  · have hZrho : Z rho = 0 :=
      Nat.eq_zero_of_le_zero ((hZ rho).trans_eq hmrho)
    simp [hZrho, hmrho]
  · have hzero : riemannZeta₁ rho = 0 := by
      apply apply_eq_zero_of_analyticOrderNatAt_ne_zero
      dsimp [m, zetaRadiusSixZeroMultiplicity] at hmrho
      split at hmrho
      · exact hmrho
      · exact False.elim (hmrho rfl)
    have hrhoRe : rho.re < 1 := riemannZeta₁_zero_re_lt_one hzero
    have hinv : 0 ≤ ((s - rho)⁻¹).re := by
      rw [Complex.inv_re]
      exact div_nonneg (by simp only [Complex.sub_re]; linarith)
        (Complex.normSq_nonneg _)
    have hcoeff : (Z rho : ℝ) ≤ (m rho : ℝ) := by
      exact_mod_cast hZ rho
    simpa [div_eq_mul_inv] using
      mul_le_mul_of_nonneg_right hcoeff hinv

theorem exists_selected_zetaRadiusSix_subdivisor_sum_sub_le_re_logDeriv :
    ∃ A : ℕ, 37 ≤ A ∧
      ∀ (t sigma : ℝ) (Z : ℂ →₀ ℕ),
        1 ≤ sigma → sigma ≤ 2 →
          riemannZeta₁ ((sigma : ℂ) + t * I) ≠ 0 →
            (∀ rho : ℂ,
              Z rho ≤ zetaRadiusSixZeroMultiplicity t rho) →
              Z.sum (fun rho m ↦
                  (m : ℝ) *
                    ((((sigma : ℂ) + t * I) - rho)⁻¹).re) -
                  16 * ((A : ℝ) * Real.log (|t| + 2)) / 3 ≤
                (logDeriv riemannZeta₁
                  ((sigma : ℂ) + t * I)).re := by
  obtain ⟨A, hA, hfixed⟩ :=
    exists_nat_norm_logDeriv_riemannZeta₁_sub_radiusSix_divisor_finsum_le
  refine ⟨A, hA, ?_⟩
  intro t sigma Z hsigma1 hsigma2 hzs hZ
  let s : ℂ := (sigma : ℂ) + t * I
  let E : ℝ := 16 * ((A : ℝ) * Real.log (|t| + 2)) / 3
  let S : ℂ := ∑ᶠ rho : ℂ,
    ((MeromorphicOn.divisor riemannZeta₁
      (closedBall ((2 : ℂ) + t * I) 6) rho : ℤ) : ℂ) /
        (s - rho)
  have hsball : s ∈ closedBall ((2 : ℂ) + t * I) 3 := by
    rw [mem_closedBall, Complex.dist_eq]
    have hdiff : s - ((2 : ℂ) + t * I) =
        ((sigma - 2 : ℝ) : ℂ) := by simp [s]
    rw [hdiff, Complex.norm_real, Real.norm_eq_abs]
    have : |sigma - 2| ≤ 1 := (abs_le).2 ⟨by linarith, by linarith⟩
    linarith
  have hsre : 1 ≤ s.re := by simpa [s] using hsigma1
  have hnorm : ‖logDeriv riemannZeta₁ s - S‖ ≤ E := by
    simpa [S, E, s] using hfixed t s hsball (by simpa [s] using hzs)
  have hselected :
      Z.sum (fun rho m ↦
        (m : ℝ) * (((s - rho)⁻¹).re)) ≤ S.re := by
    simpa [S] using
      selected_zetaRadiusSix_subdivisor_sum_le_re_divisor_finsum
        t s hsre Z hZ
  have hnormSwap : ‖S - logDeriv riemannZeta₁ s‖ ≤ E := by
    rw [norm_sub_rev]
    exact hnorm
  have hreal :
      (S - logDeriv riemannZeta₁ s).re ≤
        ‖S - logDeriv riemannZeta₁ s‖ := Complex.re_le_norm _
  rw [Complex.sub_re] at hreal
  simpa [s, E] using (show
    Z.sum (fun rho m ↦
        (m : ℝ) * (((s - rho)⁻¹).re)) - E ≤
      (logDeriv riemannZeta₁ s).re by linarith)

private theorem zeta_inv_sub_re_ge_inv_sixteen_mul
    (t eta : ℝ) (heta0 : 0 < eta) {rho : ℂ}
    (hsmall : dist rho (((1 + eta : ℝ) : ℂ) + t * I) ≤ 4 * eta)
    (hmul : analyticOrderNatAt riemannZeta₁ rho ≠ 0) :
    (16 * eta)⁻¹ ≤
      (((((1 + eta : ℝ) : ℂ) + t * I) - rho)⁻¹).re := by
  let s : ℂ := ((1 + eta : ℝ) : ℂ) + t * I
  have hzero : riemannZeta₁ rho = 0 :=
    apply_eq_zero_of_analyticOrderNatAt_ne_zero hmul
  have hrho : rho.re < 1 := riemannZeta₁_zero_re_lt_one hzero
  have hsre : s.re = 1 + eta := by simp [s]
  have hnum : eta ≤ (s - rho).re := by
    rw [Complex.sub_re, hsre]
    linarith
  have hne : s - rho ≠ 0 := by
    rw [sub_ne_zero]
    intro hsrho
    have hre := congrArg Complex.re hsrho
    rw [hsre] at hre
    linarith
  have hdenpos : 0 < Complex.normSq (s - rho) :=
    Complex.normSq_pos.mpr hne
  have hdist : ‖s - rho‖ ≤ 4 * eta := by
    simpa [s, Complex.dist_eq, norm_sub_rev] using hsmall
  have hden : Complex.normSq (s - rho) ≤ 16 * eta ^ 2 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg (s - rho)]
  change (16 * eta)⁻¹ ≤ ((s - rho)⁻¹).re
  rw [Complex.inv_re]
  have heta16 : 0 < 16 * eta := by positivity
  rw [inv_eq_one_div]
  change (1 : ℝ) / (16 * eta) ≤
    (s - rho).re / Complex.normSq (s - rho)
  rw [div_le_div_iff₀ heta16 hdenpos]
  nlinarith

theorem exists_zetaSmallDiskZeroMultiplicity_bound :
    ∃ A : ℕ, 37 ≤ A ∧
      ∀ (t eta : ℝ), 0 < eta → eta ≤ 1 →
        (zetaSmallDiskZeroFinsupp t eta).sum
            (fun _ m ↦ (m : ℝ)) ≤
          48 * (Real.log 4 + 4) +
            (256 * (A : ℝ) / 3) * eta *
              Real.log (|t| + 2) := by
  obtain ⟨A, hA, hselected⟩ :=
    exists_selected_zetaRadiusSix_subdivisor_sum_sub_le_re_logDeriv
  refine ⟨A, hA, ?_⟩
  intro t eta heta0 heta1
  let s : ℂ := ((1 + eta : ℝ) : ℂ) + t * I
  let Z : ℂ →₀ ℕ := zetaSmallDiskZeroFinsupp t eta
  have hsre : s.re = 1 + eta := by simp [s]
  have hs1 : 1 < s.re := by rw [hsre]; linarith
  have hsne : s ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    rw [hsre] at this
    norm_num at this
    linarith
  have hzeta : riemannZeta s ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re hs1.le
  have hzetaOne : riemannZeta₁ s ≠ 0 := by
    intro hzero
    have hfactor := riemannZeta_eq_inv_sub_mul hsne
    rw [hzero, mul_zero] at hfactor
    exact hzeta hfactor
  have hsel := hselected t (1 + eta) Z
    (by linarith) (by linarith)
    (by simpa [s] using hzetaOne)
    (by
      intro rho
      simpa [Z, zetaRadiusSixZeroMultiplicity] using
        zetaSmallDiskZeroFinsupp_le_radiusSix t eta heta1 rho)
  have hlogBound : ‖-logDeriv riemannZeta s‖ ≤
      (Real.log 4 + 4) * (1 + eta) / eta := by
    have h := norm_neg_logDeriv_LFunction_le_chebyshev_div_sub_one
      (1 : DirichletCharacter ℂ 1) hs1
    simpa [hsre] using h
  have hpoleNorm : ‖(s - 1)⁻¹‖ ≤ eta⁻¹ := by
    rw [norm_inv]
    have hnorm : eta ≤ ‖s - 1‖ := by
      calc
        eta = |(s - 1).re| := by
          rw [Complex.sub_re, hsre]
          norm_num
          exact (abs_of_pos heta0).symm
        _ ≤ ‖s - 1‖ := Complex.abs_re_le_norm _
    exact inv_anti₀ (by positivity) hnorm
  have hregularIdentity :=
    neg_logDeriv_riemannZeta_eq_pole_sub_regularized_of_ne_zero
      s hsne hzeta
  have hregularRe :
      (logDeriv riemannZeta₁ s).re ≤
        eta⁻¹ + (Real.log 4 + 4) * (1 + eta) / eta := by
    have hpoleRe : ((s - 1)⁻¹).re ≤ eta⁻¹ :=
      (Complex.re_le_norm _).trans hpoleNorm
    have hzetaRe : (logDeriv riemannZeta s).re ≤
        (Real.log 4 + 4) * (1 + eta) / eta := by
      calc
        (logDeriv riemannZeta s).re ≤
            ‖logDeriv riemannZeta s‖ := Complex.re_le_norm _
        _ = ‖-logDeriv riemannZeta s‖ := by rw [norm_neg]
        _ ≤ _ := hlogBound
    have hre := congrArg Complex.re hregularIdentity
    simp only [Complex.neg_re, Complex.sub_re] at hre
    linarith
  have hterm (rho : ℂ) (hrho : rho ∈ Z.support) :
      (16 * eta)⁻¹ ≤ ((s - rho)⁻¹).re := by
    have hZne : Z rho ≠ 0 := Finsupp.mem_support_iff.mp hrho
    have hm : zetaSmallDiskZeroMultiplicity t eta rho ≠ 0 := by
      simpa [Z, zetaSmallDiskZeroFinsupp_apply] using hZne
    unfold zetaSmallDiskZeroMultiplicity at hm
    split at hm
    next hsmall =>
      simpa [s] using
        zeta_inv_sub_re_ge_inv_sixteen_mul t eta heta0 hsmall hm
    next hsmall => exact False.elim (hm rfl)
  have hsumLower :
      (16 * eta)⁻¹ * Z.sum (fun _ m ↦ (m : ℝ)) ≤
        Z.sum (fun rho m ↦ (m : ℝ) * ((s - rho)⁻¹).re) := by
    rw [Finsupp.mul_sum]
    apply Finsupp.sum_le_sum
    intro rho hrho
    simpa [mul_comm] using
      mul_le_mul_of_nonneg_left (hterm rho hrho)
        (Nat.cast_nonneg (Z rho))
  have hsel' :
      Z.sum (fun rho m ↦ (m : ℝ) * ((s - rho)⁻¹).re) -
          16 * ((A : ℝ) * Real.log (|t| + 2)) / 3 ≤
        (logDeriv riemannZeta₁ s).re := by
    simpa [s, Z] using hsel
  have hraw :
      (16 * eta)⁻¹ * Z.sum (fun _ m ↦ (m : ℝ)) ≤
        eta⁻¹ + (Real.log 4 + 4) * (1 + eta) / eta +
          16 * ((A : ℝ) * Real.log (|t| + 2)) / 3 := by
    linarith
  have heta16 : 0 < 16 * eta := by positivity
  have hmul := mul_le_mul_of_nonneg_left hraw heta16.le
  have hleft :
      (16 * eta) * ((16 * eta)⁻¹ *
        Z.sum (fun _ m ↦ (m : ℝ))) =
          Z.sum (fun _ m ↦ (m : ℝ)) := by
    rw [← mul_assoc, mul_inv_cancel₀ heta16.ne', one_mul]
  rw [hleft] at hmul
  have hC : 1 ≤ Real.log 4 + 4 := by
    have : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    linarith
  simpa [Z] using (show
    Z.sum (fun _ m ↦ (m : ℝ)) ≤
      48 * (Real.log 4 + 4) +
        (256 * (A : ℝ) / 3) * eta * Real.log (|t| + 2) by
    calc
      Z.sum (fun _ m ↦ (m : ℝ)) ≤
          (16 * eta) *
            (eta⁻¹ + (Real.log 4 + 4) * (1 + eta) / eta +
              16 * ((A : ℝ) * Real.log (|t| + 2)) / 3) := hmul
      _ = 16 + 16 * (Real.log 4 + 4) * (1 + eta) +
          (256 * (A : ℝ) / 3) * eta * Real.log (|t| + 2) := by
        field_simp [heta0.ne']
        ring
      _ ≤ 48 * (Real.log 4 + 4) +
          (256 * (A : ℝ) / 3) * eta * Real.log (|t| + 2) := by
        nlinarith)

theorem zetaSmallDiskZeroFinsupp_eq_radiusSix_restrict
    (t eta : ℝ) (heta0 : 0 < eta) (heta1 : eta ≤ 1) (rho : ℂ) :
    zetaSmallDiskZeroFinsupp t eta rho =
      if dist rho (((1 + eta : ℝ) : ℂ) + t * I) ≤ 4 * eta then
        zetaRadiusSixZeroFinsupp t rho
      else 0 := by
  rw [zetaSmallDiskZeroFinsupp_apply,
    zetaSmallDiskZeroMultiplicity]
  split
  next hsmall =>
    rw [zetaRadiusSixZeroFinsupp_apply,
      zetaRadiusSixZeroMultiplicity]
    have hcenters :
        dist (((1 + eta : ℝ) : ℂ) + t * I)
          ((2 : ℂ) + t * I) = 1 - eta := by
      rw [Complex.dist_eq]
      have heq :
          (((1 + eta : ℝ) : ℂ) + t * I) -
              ((2 : ℂ) + t * I) = ((eta - 1 : ℝ) : ℂ) := by
        push_cast
        ring
      rw [heq, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonpos (by linarith)]
      ring
    have hfull : dist rho ((2 : ℂ) + t * I) ≤ 6 := by
      calc
        dist rho ((2 : ℂ) + t * I) ≤
            dist rho (((1 + eta : ℝ) : ℂ) + t * I) +
              dist (((1 + eta : ℝ) : ℂ) + t * I)
                ((2 : ℂ) + t * I) := dist_triangle _ _ _
        _ ≤ 4 * eta + (1 - eta) := add_le_add hsmall hcenters.le
        _ ≤ 6 := by linarith
    rw [if_pos hfull]
  next hsmall => rfl

private theorem zeta_dist_shifted_centers
    (t eta R : ℝ) :
    dist (((1 + eta : ℝ) : ℂ) + t * I)
        (((1 + R : ℝ) : ℂ) + t * I) = |eta - R| := by
  rw [Complex.dist_eq]
  have heq :
      (((1 + eta : ℝ) : ℂ) + t * I) -
          (((1 + R : ℝ) : ℂ) + t * I) =
        ((eta - R : ℝ) : ℂ) := by
    push_cast
    ring
  rw [heq, Complex.norm_real, Real.norm_eq_abs]

theorem zetaRadiusSix_eq_smallDisk_on_dyadicAnnularShell
    (t eta r : ℝ) (heta0 : 0 < eta) (hetaR : eta ≤ r)
    (k : ℕ) {rho : ℂ}
    (hrho : rho ∈ dyadicAnnularShell
      (zetaRadiusSixZeroFinsupp t)
      (((1 + eta : ℝ) : ℂ) + t * I) r k) :
    zetaRadiusSixZeroFinsupp t rho =
      zetaSmallDiskZeroFinsupp t
        (r * (2 : ℝ) ^ (k + 1)) rho := by
  let R : ℝ := r * (2 : ℝ) ^ (k + 1)
  have hrhoData := Finset.mem_filter.mp
    (show rho ∈
      (zetaRadiusSixZeroFinsupp t).support.filter
        (fun rho ↦
          r * (2 : ℝ) ^ k <
              dist rho (((1 + eta : ℝ) : ℂ) + t * I) ∧
            dist rho (((1 + eta : ℝ) : ℂ) + t * I) ≤
              r * (2 : ℝ) ^ (k + 1)) by
        simpa only [dyadicAnnularShell] using hrho)
  have hReta : eta ≤ R := by
    have hr0 : 0 < r := lt_of_lt_of_le heta0 hetaR
    have hone : (1 : ℝ) ≤ (2 : ℝ) ^ (k + 1) :=
      one_le_pow₀ (by norm_num)
    exact hetaR.trans (by simpa [R] using
      mul_le_mul_of_nonneg_left hone hr0.le)
  have hcenter :
      dist (((1 + eta : ℝ) : ℂ) + t * I)
        (((1 + R : ℝ) : ℂ) + t * I) = R - eta := by
    rw [zeta_dist_shifted_centers,
      abs_of_nonpos (sub_nonpos.mpr hReta)]
    ring
  have hsmall :
      dist rho (((1 + R : ℝ) : ℂ) + t * I) ≤ 4 * R := by
    calc
      dist rho (((1 + R : ℝ) : ℂ) + t * I) ≤
          dist rho (((1 + eta : ℝ) : ℂ) + t * I) +
            dist (((1 + eta : ℝ) : ℂ) + t * I)
              (((1 + R : ℝ) : ℂ) + t * I) := dist_triangle _ _ _
      _ ≤ R + (R - eta) := add_le_add hrhoData.2.2 hcenter.le
      _ ≤ 4 * R := by
        have hRpos : 0 < R := lt_of_lt_of_le heta0 hReta
        linarith
  have hfull : dist rho ((2 : ℂ) + t * I) ≤ 6 := by
    by_contra hnot
    have hzero : zetaRadiusSixZeroFinsupp t rho = 0 := by
      rw [zetaRadiusSixZeroFinsupp_apply,
        zetaRadiusSixZeroMultiplicity, if_neg hnot]
    exact (Finsupp.mem_support_iff.mp hrhoData.1) hzero
  rw [zetaRadiusSixZeroFinsupp_apply,
    zetaRadiusSixZeroMultiplicity, if_pos hfull,
    zetaSmallDiskZeroFinsupp_apply,
    zetaSmallDiskZeroMultiplicity, if_pos]
  simpa only [R] using hsmall

theorem exists_dyadicAnnularShell_zetaRadiusSix_mass_bound :
    ∃ A : ℕ, 37 ≤ A ∧
      ∀ (t eta r : ℝ), 0 < eta → eta ≤ r →
        ∀ k : ℕ, r * (2 : ℝ) ^ (k + 1) ≤ 1 →
          (∑ rho ∈ dyadicAnnularShell
                (zetaRadiusSixZeroFinsupp t)
                (((1 + eta : ℝ) : ℂ) + t * I) r k,
              (zetaRadiusSixZeroFinsupp t rho : ℝ)) ≤
            48 * (Real.log 4 + 4) +
              ((256 * (A : ℝ) / 3) * Real.log (|t| + 2)) *
                (r * (2 : ℝ) ^ (k + 1)) := by
  obtain ⟨A, hA, hlocal⟩ :=
    exists_zetaSmallDiskZeroMultiplicity_bound
  refine ⟨A, hA, ?_⟩
  intro t eta r heta0 hetaR k hR1
  let R : ℝ := r * (2 : ℝ) ^ (k + 1)
  let D : ℂ →₀ ℕ := zetaRadiusSixZeroFinsupp t
  let Z : ℂ →₀ ℕ := zetaSmallDiskZeroFinsupp t R
  let S : Finset ℂ := dyadicAnnularShell D
    (((1 + eta : ℝ) : ℂ) + t * I) r k
  have hRpos : 0 < R := by
    have hr0 : 0 < r := lt_of_lt_of_le heta0 hetaR
    positivity
  have heq (rho : ℂ) (hrho : rho ∈ S) : D rho = Z rho := by
    simpa only [D, Z, S, R] using
      zetaRadiusSix_eq_smallDisk_on_dyadicAnnularShell
        t eta r heta0 hetaR k hrho
  have hsubset : S ⊆ Z.support := by
    intro rho hrho
    rw [Finsupp.mem_support_iff, ← heq rho hrho]
    exact Finsupp.mem_support_iff.mp (Finset.mem_filter.mp hrho).1
  have hsum :
      (∑ rho ∈ S, (D rho : ℝ)) ≤
        Z.sum (fun _ m ↦ (m : ℝ)) := by
    rw [Finsupp.sum]
    calc
      (∑ rho ∈ S, (D rho : ℝ)) =
          ∑ rho ∈ S, (Z rho : ℝ) := by
        apply Finset.sum_congr rfl
        intro rho hrho
        rw [heq rho hrho]
      _ ≤ ∑ rho ∈ Z.support, (Z rho : ℝ) := by
        exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
          (fun _ _ _ ↦ Nat.cast_nonneg _)
  have hlocal' := hlocal t R hRpos hR1
  calc
    (∑ rho ∈ dyadicAnnularShell
          (zetaRadiusSixZeroFinsupp t)
          (((1 + eta : ℝ) : ℂ) + t * I) r k,
        (zetaRadiusSixZeroFinsupp t rho : ℝ)) ≤
        Z.sum (fun _ m ↦ (m : ℝ)) := by
      simpa only [D, S] using hsum
    _ ≤ 48 * (Real.log 4 + 4) +
        (256 * (A : ℝ) / 3) * R * Real.log (|t| + 2) := by
      simpa only [Z] using hlocal'
    _ = 48 * (Real.log 4 + 4) +
        ((256 * (A : ℝ) / 3) * Real.log (|t| + 2)) * R := by ring
    _ = _ := by rfl

theorem zetaRadiusSix_sum_sub_smallDisk_sum_eq_outside
    (t eta : ℝ) (heta0 : 0 < eta) (heta1 : eta ≤ 1) (j : ℕ) :
    let z : ℂ := ((1 + eta : ℝ) : ℂ) + t * I
    let D := zetaRadiusSixZeroFinsupp t
    let Z := zetaSmallDiskZeroFinsupp t eta
    D.sum (fun rho m ↦ (m : ℂ) / (z - rho) ^ j) -
        Z.sum (fun rho m ↦ (m : ℂ) / (z - rho) ^ j) =
      ∑ rho ∈ D.support.filter (fun rho ↦ 4 * eta < dist rho z),
        (D rho : ℂ) / (z - rho) ^ j := by
  dsimp only
  let z : ℂ := ((1 + eta : ℝ) : ℂ) + t * I
  let D := zetaRadiusSixZeroFinsupp t
  let Z := zetaSmallDiskZeroFinsupp t eta
  rw [Finsupp.sum, Finsupp.sum]
  have hZsub : Z.support ⊆ D.support := by
    intro rho hrho
    rw [Finsupp.mem_support_iff] at hrho ⊢
    have heq := zetaSmallDiskZeroFinsupp_eq_radiusSix_restrict
      t eta heta0 heta1 rho
    by_cases hsmall : dist rho z ≤ 4 * eta
    · have hZD : Z rho = D rho := by
        simpa only [Z, D, z, hsmall, if_true] using heq
      intro hDzero
      exact hrho (hZD.trans hDzero)
    · have : Z rho = 0 := by
        simpa only [Z, D, z, hsmall, if_false] using heq
      exact False.elim (hrho this)
  have hZsum :
      (∑ rho ∈ Z.support, (Z rho : ℂ) / (z - rho) ^ j) =
        ∑ rho ∈ D.support, (Z rho : ℂ) / (z - rho) ^ j := by
    apply Finset.sum_subset hZsub
    intro rho hrhoD hrhoZ
    have hZzero : Z rho = 0 := by
      simpa only [Finsupp.mem_support_iff, not_not] using hrhoZ
    simp [hZzero]
  rw [hZsum, ← Finset.sum_sub_distrib]
  calc
    (∑ rho ∈ D.support,
        ((D rho : ℂ) / (z - rho) ^ j -
          (Z rho : ℂ) / (z - rho) ^ j)) =
        ∑ rho ∈ D.support,
          if 4 * eta < dist rho z then
            (D rho : ℂ) / (z - rho) ^ j else 0 := by
      apply Finset.sum_congr rfl
      intro rho hrho
      have heq := zetaSmallDiskZeroFinsupp_eq_radiusSix_restrict
        t eta heta0 heta1 rho
      by_cases hsmall : dist rho z ≤ 4 * eta
      · have hZD : Z rho = D rho := by
          simpa only [Z, D, z, hsmall, if_true] using heq
        rw [if_neg (not_lt.mpr hsmall), hZD]
        ring
      · have hZzero : Z rho = 0 := by
          simpa only [Z, D, z, hsmall, if_false] using heq
        rw [if_pos (lt_of_not_ge hsmall), hZzero]
        simp
    _ = ∑ rho ∈ D.support.filter (fun rho ↦ 4 * eta < dist rho z),
        (D rho : ℂ) / (z - rho) ^ j := by
      rw [Finset.sum_filter]

theorem exists_norm_zetaRadiusSix_sub_smallDisk_powerSum_le :
    ∃ Aₗ Aₑ : ℕ, 37 ≤ Aₗ ∧ 37 ≤ Aₑ ∧
      ∀ (t eta : ℝ), 0 < eta → eta ≤ 1 / 8 →
        ∀ j : ℕ, 2 ≤ j →
          let z : ℂ := ((1 + eta : ℝ) : ℂ) + t * I
          let D := zetaRadiusSixZeroFinsupp t
          let Z := zetaSmallDiskZeroFinsupp t eta
          ‖D.sum (fun rho m ↦ (m : ℂ) / (z - rho) ^ j) -
              Z.sum (fun rho m ↦ (m : ℂ) / (z - rho) ^ j)‖ ≤
            96 * (Real.log 4 + 4) / (4 * eta) ^ j +
              ((1024 * (Aₗ : ℝ) / 3) * Real.log (|t| + 2)) /
                (4 * eta) ^ (j - 1) +
              (2 * (Aₑ : ℝ) * Real.log (|t| + 2)) /
                (1 / 2 : ℝ) ^ j := by
  obtain ⟨Aₗ, hAₗ, hlocal⟩ :=
    exists_dyadicAnnularShell_zetaRadiusSix_mass_bound
  obtain ⟨Aₑ, hAₑ, hfull⟩ :=
    exists_zetaRadiusSixZeroFinsupp_mass_bound
  refine ⟨Aₗ, Aₑ, hAₗ, hAₑ, ?_⟩
  intro t eta heta0 heta8 j hj
  dsimp only
  let z : ℂ := ((1 + eta : ℝ) : ℂ) + t * I
  let D := zetaRadiusSixZeroFinsupp t
  let Z := zetaSmallDiskZeroFinsupp t eta
  let r : ℝ := 4 * eta
  have hr0 : 0 < r := by positivity
  have hr1 : r ≤ 1 := by dsimp [r]; linarith
  obtain ⟨N, hRN, hRhalf⟩ := exists_dyadic_scale_le_one hr0 hr1
  let R : ℝ := r * (2 : ℝ) ^ N
  have hR0 : 0 < R := by positivity
  have hrR : r ≤ R := by
    dsimp [R]
    have hone : (1 : ℝ) ≤ (2 : ℝ) ^ N := one_le_pow₀ (by norm_num)
    simpa using mul_le_mul_of_nonneg_left hone hr0.le
  have hlog : 0 ≤ Real.log (|t| + 2) :=
    Real.log_nonneg (by linarith [abs_nonneg t])
  have hnear :
      ‖∑ rho ∈ D.support.filter (fun rho ↦
            r < dist rho z ∧ dist rho z ≤ R),
          (D rho : ℂ) / (z - rho) ^ j‖ ≤
        96 * (Real.log 4 + 4) / r ^ j +
          ((1024 * (Aₗ : ℝ) / 3) * Real.log (|t| + 2)) /
            r ^ (j - 1) := by
    have hann := norm_sum_annularTail_div_pow_le_of_affine_mass
      D z hr0 (by positivity : 0 ≤ 48 * (Real.log 4 + 4))
      (mul_nonneg (by positivity : 0 ≤ 256 * (Aₗ : ℝ) / 3) hlog)
      N j hj (by
        intro k hk
        apply hlocal t eta r heta0 (by linarith) k
        have hkN : k + 1 ≤ N := by omega
        exact (mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ (by norm_num) hkN) hr0.le).trans hRN)
    change ‖∑ rho ∈ D.support.filter (fun rho ↦
          r < dist rho z ∧ dist rho z ≤ r * (2 : ℝ) ^ N),
        (D rho : ℂ) / (z - rho) ^ j‖ ≤ _ at hann
    rw [show R = r * (2 : ℝ) ^ N by rfl]
    calc
      ‖∑ rho ∈ D.support.filter (fun rho ↦
            r < dist rho z ∧ dist rho z ≤ R),
          (D rho : ℂ) / (z - rho) ^ j‖ ≤
          2 * (48 * (Real.log 4 + 4)) / r ^ j +
            4 * ((256 * (Aₗ : ℝ) / 3) * Real.log (|t| + 2)) /
              r ^ (j - 1) := hann
      _ = _ := by ring
  have hfar :
      ‖∑ rho ∈ D.support.filter (fun rho ↦ R < dist rho z),
          (D rho : ℂ) / (z - rho) ^ j‖ ≤
        (2 * (Aₑ : ℝ) * Real.log (|t| + 2)) /
          (1 / 2 : ℝ) ^ j := by
    have hraw := norm_sum_farTail_div_pow_le D z hR0 j
    have hmass := hfull t
    have hnum : 0 ≤ 2 * (Aₑ : ℝ) * Real.log (|t| + 2) := by
      positivity
    calc
      ‖∑ rho ∈ D.support.filter (fun rho ↦ R < dist rho z),
          (D rho : ℂ) / (z - rho) ^ j‖ ≤
          D.sum (fun _ m ↦ (m : ℝ)) / R ^ j := hraw
      _ ≤ (2 * (Aₑ : ℝ) * Real.log (|t| + 2)) / R ^ j :=
        div_le_div_of_nonneg_right hmass (by positivity)
      _ ≤ (2 * (Aₑ : ℝ) * Real.log (|t| + 2)) /
          (1 / 2 : ℝ) ^ j := by
        exact div_le_div_of_nonneg_left hnum (by positivity)
          (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2)
            hRhalf.le j)
  have hdiff := zetaRadiusSix_sum_sub_smallDisk_sum_eq_outside
    t eta heta0 (by linarith : eta ≤ 1) j
  have hsplit := sum_outside_eq_annular_add_far D z hrR j
  change D.sum (fun rho m ↦ (m : ℂ) / (z - rho) ^ j) -
      Z.sum (fun rho m ↦ (m : ℂ) / (z - rho) ^ j) =
        ∑ rho ∈ D.support.filter (fun rho ↦ r < dist rho z),
          (D rho : ℂ) / (z - rho) ^ j at hdiff
  rw [hdiff, hsplit]
  calc
    ‖(∑ rho ∈ D.support.filter (fun rho ↦
          r < dist rho z ∧ dist rho z ≤ R),
        (D rho : ℂ) / (z - rho) ^ j) +
      ∑ rho ∈ D.support.filter (fun rho ↦ R < dist rho z),
        (D rho : ℂ) / (z - rho) ^ j‖ ≤
        ‖∑ rho ∈ D.support.filter (fun rho ↦
          r < dist rho z ∧ dist rho z ≤ R),
            (D rho : ℂ) / (z - rho) ^ j‖ +
          ‖∑ rho ∈ D.support.filter (fun rho ↦ R < dist rho z),
            (D rho : ℂ) / (z - rho) ^ j‖ := norm_add_le _ _
    _ ≤ (96 * (Real.log 4 + 4) / r ^ j +
          ((1024 * (Aₗ : ℝ) / 3) * Real.log (|t| + 2)) /
            r ^ (j - 1)) +
        (2 * (Aₑ : ℝ) * Real.log (|t| + 2)) /
          (1 / 2 : ℝ) ^ j := add_le_add hnear hfar
    _ = _ := by rfl

private theorem zetaRadiusSix_divisor_finsum_eq_finsupp
    (t : ℝ) (s : ℂ) :
    (∑ᶠ rho : ℂ,
        ((MeromorphicOn.divisor riemannZeta₁
          (closedBall ((2 : ℂ) + t * I) 6) rho : ℤ) : ℂ) /
            (s - rho)) =
      ∑ᶠ rho : ℂ,
        (zetaRadiusSixZeroFinsupp t rho : ℂ) / (s - rho) := by
  apply finsum_congr
  intro rho
  rw [← zetaRadiusSixZeroFinsupp_apply_eq_divisor t rho]
  norm_cast

private theorem zetaRadiusSix_poleSum_analyticAt
    (t : ℝ) {s : ℂ}
    (hne : ∀ rho ∈ (zetaRadiusSixZeroFinsupp t).support,
      s ≠ rho) :
    AnalyticAt ℂ (fun w : ℂ ↦
      ∑ᶠ rho : ℂ,
        (zetaRadiusSixZeroFinsupp t rho : ℂ) / (w - rho)) s := by
  let D := zetaRadiusSixZeroFinsupp t
  have hfun :
      (fun w : ℂ ↦ ∑ᶠ rho : ℂ, (D rho : ℂ) / (w - rho)) =
        (fun w : ℂ ↦ ∑ rho ∈ D.support,
          (D rho : ℂ) / (w - rho)) := by
    funext w
    apply finsum_eq_sum_of_support_subset
    intro rho hrho
    rw [Function.mem_support] at hrho
    rw [Finset.mem_coe, Finsupp.mem_support_iff]
    intro hzero
    exact hrho (by simp [hzero])
  rw [show (fun w : ℂ ↦
      ∑ᶠ rho : ℂ,
        (zetaRadiusSixZeroFinsupp t rho : ℂ) / (w - rho)) =
      (fun w : ℂ ↦ ∑ᶠ rho : ℂ,
        (D rho : ℂ) / (w - rho)) by rfl, hfun]
  have han : AnalyticAt ℂ
      (∑ rho ∈ D.support,
        (fun w : ℂ ↦ (D rho : ℂ) / (w - rho))) s := by
    apply Finset.analyticAt_sum D.support
    intro rho hrho
    exact (analyticAt_const.div
      (analyticAt_id.sub analyticAt_const)
      (sub_ne_zero.mpr (hne rho hrho)))
  convert han using 1
  funext w
  simp

theorem exists_zetaRadiusSix_iteratedDeriv_approximation :
    ∃ A : ℕ, 37 ≤ A ∧
      ∀ (t eta : ℝ), 0 < eta → eta ≤ 1 →
        ∀ k : ℕ,
          let z : ℂ := ((1 + eta : ℝ) : ℂ) + t * I
          ‖iteratedDeriv k (fun w ↦ -logDeriv riemannZeta₁ w) z -
              (-1 : ℂ) ^ (k + 1) * k.factorial *
                (zetaRadiusSixZeroFinsupp t).sum
                  (fun rho m ↦ (m : ℂ) / (z - rho) ^ (k + 1))‖ ≤
            k.factorial *
              (16 * ((A : ℝ) * Real.log (|t| + 2)) / 3) := by
  obtain ⟨A, hA, hgrowth⟩ :=
    exists_nat_norm_riemannZeta₁_radiusTwelveSphere_le_exp_mul_center
  refine ⟨A, hA, ?_⟩
  intro t eta heta0 heta1 k
  dsimp only
  let f : ℂ → ℂ := riemannZeta₁
  let c : ℂ := (2 : ℂ) + t * I
  let z : ℂ := ((1 + eta : ℝ) : ℂ) + t * I
  let B : ℝ := |t| + 2
  let M : ℝ := (A : ℝ) * Real.log B
  let D : ℂ →₀ ℕ := zetaRadiusSixZeroFinsupp t
  have hB2 : (2 : ℝ) ≤ B := by
    dsimp [B]
    linarith [abs_nonneg t]
  have hM : 0 < M := by
    dsimp [M]
    exact mul_pos (by exact_mod_cast (show 0 < A by omega))
      (Real.log_pos (by linarith))
  have hf : AnalyticOnNhd ℂ f (closedBall c (4 * (3 : ℝ))) := by
    intro w hw
    exact differentiable_riemannZeta₁.analyticAt w
  have hc : f c ≠ 0 := by
    have hcOne : c ≠ 1 := by
      intro h
      have := congrArg Complex.re h
      simp [c] at this
    have hzeta : riemannZeta c ≠ 0 :=
      riemannZeta_ne_zero_of_one_le_re (by simp [c])
    intro hzero
    change riemannZeta₁ c = 0 at hzero
    have hfactor := riemannZeta_eq_inv_sub_mul hcOne
    rw [hzero, mul_zero] at hfactor
    exact hzeta hfactor
  have hbound : ∀ w ∈ sphere c (4 * (3 : ℝ)),
      ‖f w‖ ≤ Real.exp M * ‖f c‖ := by
    intro w hw
    norm_num at hw
    simpa [f, c, M, B] using
      hgrowth t w (by simpa [c] using hw)
  obtain ⟨G, hG, hGne, hidentity, hGbound⟩ :=
    exists_regularizedLogDeriv_data_erdos48
      (f := f) (c := c) (R := (3 : ℝ)) (M := M)
      (by norm_num) hM hf hc hbound
  have hzre : z.re = 1 + eta := by simp [z]
  have hzc : dist z c = 1 - eta := by
    rw [Complex.dist_eq]
    have heq : z - c = ((eta - 1 : ℝ) : ℂ) := by
      simp only [z, c]
      push_cast
      ring
    rw [heq, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos (by linarith)]
    ring
  have hzball : z ∈ closedBall c 3 := by
    rw [mem_closedBall, hzc]
    linarith
  have hfz : f z ≠ 0 := by
    have hzOne : z ≠ 1 := by
      intro h
      have := congrArg Complex.re h
      rw [hzre] at this
      norm_num at this
      linarith
    have hzeta : riemannZeta z ≠ 0 :=
      riemannZeta_ne_zero_of_one_le_re (by rw [hzre]; linarith)
    intro hzero
    change riemannZeta₁ z = 0 at hzero
    have hfactor := riemannZeta_eq_inv_sub_mul hzOne
    rw [hzero, mul_zero] at hfactor
    exact hzeta hfactor
  have hDne : ∀ rho ∈ D.support, z ≠ rho := by
    intro rho hrho hzr
    subst rho
    have hDzero : D z = 0 := by
      change zetaRadiusSixZeroMultiplicity t z = 0
      unfold zetaRadiusSixZeroMultiplicity
      split
      next hdist =>
        by_contra horder
        exact hfz (by simpa [f] using
          apply_eq_zero_of_analyticOrderNatAt_ne_zero horder)
      next hdist => rfl
    exact (Finsupp.mem_support_iff.mp hrho) hDzero
  let P : ℂ → ℂ := fun w ↦
    ∑ᶠ rho : ℂ, (D rho : ℂ) / (w - rho)
  let U : Set ℂ := {w | 1 < w.re ∧ dist w c < 3}
  have hUopen : IsOpen U :=
    (isOpen_lt continuous_const continuous_re).inter
      (isOpen_lt (continuous_id.dist continuous_const) continuous_const)
  have hzU : z ∈ U := by
    refine ⟨by rw [hzre]; linarith, ?_⟩
    rw [hzc]
    linarith
  have heqOn : Set.EqOn (logDeriv G)
      (fun w ↦ logDeriv f w - P w) U := by
    intro w hw
    have hwball : w ∈ closedBall c 3 := mem_closedBall.mpr hw.2.le
    have hfw : f w ≠ 0 := by
      have hwOne : w ≠ 1 := by
        intro h
        have := congrArg Complex.re h
        exact (ne_of_gt hw.1) (by simpa using this)
      have hzeta : riemannZeta w ≠ 0 :=
        riemannZeta_ne_zero_of_one_le_re hw.1.le
      intro hzero
      change riemannZeta₁ w = 0 at hzero
      have hfactor := riemannZeta_eq_inv_sub_mul hwOne
      rw [hzero, mul_zero] at hfactor
      exact hzeta hfactor
    have hid := hidentity w hwball hfw
    change logDeriv G w = logDeriv riemannZeta₁ w -
      ∑ᶠ rho : ℂ,
        ((MeromorphicOn.divisor riemannZeta₁
          (closedBall ((2 : ℂ) + t * I) (2 * 3)) rho : ℤ) : ℂ) /
            (w - rho) at hid
    rw [show (2 : ℝ) * 3 = 6 by norm_num] at hid
    rw [hid]
    dsimp only [P, D, f]
    rw [zetaRadiusSix_divisor_finsum_eq_finsupp t w]
  have hderivEq := heqOn.iteratedDeriv_of_isOpen hUopen k hzU
  have hlogAnalytic : AnalyticAt ℂ (logDeriv f) z := by
    have hfzAnalytic : AnalyticAt ℂ f z := hf z (by
      exact closedBall_subset_closedBall
        (by norm_num : (3 : ℝ) ≤ 4 * 3) hzball)
    simpa [logDeriv] using hfzAnalytic.deriv.div hfzAnalytic hfz
  have hPAnalytic : AnalyticAt ℂ P z := by
    simpa only [P, D] using
      zetaRadiusSix_poleSum_analyticAt t hDne
  have hGP :
      iteratedDeriv k (logDeriv G) z =
        iteratedDeriv k (logDeriv f) z - iteratedDeriv k P z := by
    rw [hderivEq]
    exact iteratedDeriv_sub hlogAnalytic.contDiffAt hPAnalytic.contDiffAt
  have hPderiv : iteratedDeriv k P z =
      (-1 : ℂ) ^ k * k.factorial *
        D.sum (fun rho m ↦ (m : ℂ) / (z - rho) ^ (k + 1)) := by
    have hraw := iteratedDeriv_weighted_inv_sub_finsum (k := k)
      (b := fun rho ↦ (D rho : ℂ))
      (hb := by
        exact D.support.finite_toSet.subset <| by
          intro rho hrho
          rw [Function.mem_support] at hrho
          rw [Finset.mem_coe, Finsupp.mem_support_iff]
          intro hzero
          exact hrho (by simp [hzero]))
      (z := z) (hne := by
        intro rho hrho
        rw [Function.mem_support] at hrho
        apply hDne rho
        rw [Finsupp.mem_support_iff]
        intro hzero
        exact hrho (by simp [hzero]))
    have hsum :
        (∑ᶠ rho : ℂ, (D rho : ℂ) / (z - rho) ^ (k + 1)) =
          D.sum (fun rho m ↦ (m : ℂ) / (z - rho) ^ (k + 1)) := by
      rw [Finsupp.sum]
      apply finsum_eq_sum_of_support_subset
      intro rho hrho
      rw [Function.mem_support] at hrho
      rw [Finset.mem_coe, Finsupp.mem_support_iff]
      intro hzero
      exact hrho (by simp [hzero])
    rw [hsum] at hraw
    simpa only [P] using hraw
  have hGderiv := norm_iteratedDeriv_logDeriv_le_of_regularized_data
    (G := G) (c := c) (z := z) (R := (3 : ℝ)) (r := (1 : ℝ))
    (C := 16 * M / 3) (by norm_num) (by norm_num) hG hGne
    (by
      intro w hw
      rw [mem_closedBall] at hw ⊢
      calc
        dist w c ≤ dist w z + dist z c := dist_triangle _ _ _
        _ ≤ 1 + (1 - eta) := add_le_add hw hzc.le
        _ ≤ 3 := by linarith)
    hGbound k
  have hneg : iteratedDeriv k (fun w ↦ -logDeriv f w) z =
      -iteratedDeriv k (logDeriv f) z := iteratedDeriv_neg k _ _
  change ‖iteratedDeriv k (fun w ↦ -logDeriv f w) z -
      (-1 : ℂ) ^ (k + 1) * k.factorial *
        D.sum (fun rho m ↦ (m : ℂ) / (z - rho) ^ (k + 1))‖ ≤
      k.factorial * (16 * M / 3)
  rw [hneg]
  have hsign : -((-1 : ℂ) ^ k) = (-1 : ℂ) ^ (k + 1) := by
    rw [pow_succ]
    ring
  rw [← hsign]
  have hdiff :
      -iteratedDeriv k (logDeriv f) z -
          (-((-1 : ℂ) ^ k) * k.factorial *
            D.sum (fun rho m ↦ (m : ℂ) / (z - rho) ^ (k + 1))) =
        -iteratedDeriv k (logDeriv G) z := by
    calc
      -iteratedDeriv k (logDeriv f) z -
          (-((-1 : ℂ) ^ k) * k.factorial *
            D.sum (fun rho m ↦ (m : ℂ) / (z - rho) ^ (k + 1))) =
          -iteratedDeriv k (logDeriv f) z +
            ((-1 : ℂ) ^ k * k.factorial *
              D.sum (fun rho m ↦
                (m : ℂ) / (z - rho) ^ (k + 1))) := by ring
      _ = -iteratedDeriv k (logDeriv f) z +
          iteratedDeriv k P z := by rw [hPderiv]
      _ = -iteratedDeriv k (logDeriv G) z := by
        rw [hGP]
        ring
  rw [hdiff, norm_neg]
  simpa [M, B, f, z, D] using hGderiv

noncomputable def zetaPointwiseZeroDetectorError
    (Al Af Ad : ℕ) (t eta : ℝ) (j : ℕ) : ℝ :=
  96 * (Real.log 4 + 4) / (4 * eta) ^ j +
    ((1024 * (Al : ℝ) / 3) * Real.log (|t| + 2)) /
      (4 * eta) ^ (j - 1) +
    (2 * (Af : ℝ) * Real.log (|t| + 2)) /
      (1 / 2 : ℝ) ^ j +
    16 * ((Ad : ℝ) * Real.log (|t| + 2)) / 3

theorem exists_zeta_pointwise_zero_detector_of_error_budget :
    ∃ Am Al Af Ad : ℕ,
      37 ≤ Am ∧ 37 ≤ Al ∧ 37 ≤ Af ∧ 37 ≤ Ad ∧
      ∀ (t eta : ℝ), 0 < eta → eta ≤ 1 / 8 →
        ∀ (rho₀ : ℂ), riemannZeta₁ rho₀ = 0 →
          dist rho₀ (((1 + eta : ℝ) : ℂ) + t * I) ≤ 2 * eta →
          ∀ (L : ℕ), 2 ≤ L →
            let z : ℂ := ((1 + eta : ℝ) : ℂ) + t * I
            let Z := zetaSmallDiskZeroFinsupp t eta
            (∀ j : ℕ, L ≤ j → j ≤ L * Z.sum (fun _ m ↦ m) →
              zetaPointwiseZeroDetectorError Al Af Ad t eta j ≤
                (1 / 12 : ℝ) * (2 * eta)⁻¹ ^ j) →
            ∃ j : ℕ,
              L ≤ j ∧ j ≤ L * Z.sum (fun _ m ↦ m) ∧
                (j - 1).factorial * (1 / 12 : ℝ) *
                    (2 * eta)⁻¹ ^ j <
                  ‖iteratedDeriv (j - 1)
                    (fun w ↦ -logDeriv riemannZeta₁ w) z‖ := by
  obtain ⟨Am, hAm, hmass⟩ :=
    exists_zetaSmallDiskZeroMultiplicity_bound
  obtain ⟨Al, Af, hAl, hAf, htail⟩ :=
    exists_norm_zetaRadiusSix_sub_smallDisk_powerSum_le
  obtain ⟨Ad, hAd, hderiv⟩ :=
    exists_zetaRadiusSix_iteratedDeriv_approximation
  refine ⟨Am, Al, Af, Ad, hAm, hAl, hAf, hAd, ?_⟩
  intro t eta heta0 heta8 rho₀ hzero hrho₀ L hL
  dsimp only
  let z : ℂ := ((1 + eta : ℝ) : ℂ) + t * I
  let Z := zetaSmallDiskZeroFinsupp t eta
  let D := zetaRadiusSixZeroFinsupp t
  intro hbudget
  have hrhoRe : rho₀.re < 1 := riemannZeta₁_zero_re_lt_one hzero
  have hzre : z.re = 1 + eta := by simp [z]
  have hzrho₀ : z ≠ rho₀ := by
    intro hzr
    have := congrArg Complex.re hzr
    rw [hzre] at this
    linarith
  have horderNe : analyticOrderNatAt riemannZeta₁ rho₀ ≠ 0 := by
    have hsupp : rho₀ ∈
        (MeromorphicOn.divisor riemannZeta₁ Set.univ).support :=
      (mem_support_divisor_riemannZeta₁_iff (Set.mem_univ rho₀)).2 hzero
    rw [Function.mem_support,
      divisor_riemannZeta₁_apply_eq_analyticOrderNatAt
        (Set.mem_univ rho₀)] at hsupp
    exact_mod_cast hsupp
  have horder : 0 < analyticOrderNatAt riemannZeta₁ rho₀ :=
    Nat.pos_of_ne_zero horderNe
  have hZrho₀ : Z rho₀ ≠ 0 := by
    change zetaSmallDiskZeroMultiplicity t eta rho₀ ≠ 0
    rw [zetaSmallDiskZeroMultiplicity,
      if_pos (hrho₀.trans (by linarith : 2 * eta ≤ 4 * eta))]
    exact horder.ne'
  obtain ⟨j, hjL, hjupper, hjlarge⟩ :=
    exists_norm_sparseWeightedReciprocalPowerSum_gt_distinguished
      Z hZrho₀ hzrho₀ (Nat.zero_lt_of_lt hL)
  refine ⟨j, hjL, hjupper, ?_⟩
  have hj2 : 2 ≤ j := hL.trans hjL
  let Sz : ℂ := Z.sum
    (fun rho m ↦ (m : ℂ) / (z - rho) ^ j)
  let Sd : ℂ := D.sum
    (fun rho m ↦ (m : ℂ) / (z - rho) ^ j)
  have hinv : (2 * eta)⁻¹ ≤ ‖(z - rho₀)⁻¹‖ := by
    rw [norm_inv]
    have hnormPos : 0 < ‖z - rho₀‖ :=
      norm_pos_iff.mpr (sub_ne_zero.mpr hzrho₀)
    apply inv_anti₀ hnormPos
    simpa [z, dist_eq_norm, norm_sub_rev] using hrho₀
  have hinvpow : (2 * eta)⁻¹ ^ j ≤ ‖(z - rho₀)⁻¹‖ ^ j :=
    pow_le_pow_left₀ (by positivity) hinv j
  have hlocal : (1 / 6 : ℝ) * (2 * eta)⁻¹ ^ j < ‖Sz‖ := by
    exact (mul_le_mul_of_nonneg_left hinvpow (by norm_num)).trans_lt (by
      simpa only [Sz] using hjlarge)
  have htail' := htail t eta heta0 heta8 j hj2
  have htailNorm : ‖Sd - Sz‖ ≤
      96 * (Real.log 4 + 4) / (4 * eta) ^ j +
        ((1024 * (Al : ℝ) / 3) * Real.log (|t| + 2)) /
          (4 * eta) ^ (j - 1) +
        (2 * (Af : ℝ) * Real.log (|t| + 2)) /
          (1 / 2 : ℝ) ^ j := by
    simpa only [Sd, Sz, D, Z, z] using htail'
  have hderiv' := hderiv t eta heta0
    (by linarith : eta ≤ 1) (j - 1)
  have hjpred : j - 1 + 1 = j := by omega
  have hderivNorm :
      ‖iteratedDeriv (j - 1)
            (fun w ↦ -logDeriv riemannZeta₁ w) z -
          (-1 : ℂ) ^ j * (j - 1).factorial * Sd‖ ≤
        (j - 1).factorial *
          (16 * ((Ad : ℝ) * Real.log (|t| + 2)) / 3) := by
    simpa only [hjpred, Sd, D, z] using hderiv'
  have hbudget' := hbudget j hjL hjupper
  have herror :
      (96 * (Real.log 4 + 4) / (4 * eta) ^ j +
        ((1024 * (Al : ℝ) / 3) * Real.log (|t| + 2)) /
          (4 * eta) ^ (j - 1) +
        (2 * (Af : ℝ) * Real.log (|t| + 2)) /
          (1 / 2 : ℝ) ^ j) +
        16 * ((Ad : ℝ) * Real.log (|t| + 2)) / 3 ≤
        (1 / 12 : ℝ) * (2 * eta)⁻¹ ^ j := by
    simpa only [zetaPointwiseZeroDetectorError, add_assoc] using hbudget'
  have hSz : ‖Sz‖ ≤ ‖Sd‖ + ‖Sd - Sz‖ := by
    calc
      ‖Sz‖ = ‖Sd - (Sd - Sz)‖ := by ring_nf
      _ ≤ ‖Sd‖ + ‖Sd - Sz‖ := norm_sub_le _ _
  let F : ℂ := iteratedDeriv (j - 1)
    (fun w ↦ -logDeriv riemannZeta₁ w) z
  have hscaled : ((j - 1).factorial : ℝ) * ‖Sd‖ ≤
      ‖F‖ + ‖F - (-1 : ℂ) ^ j * (j - 1).factorial * Sd‖ := by
    have htri : ‖(-1 : ℂ) ^ j * (j - 1).factorial * Sd‖ ≤
        ‖F‖ + ‖F - (-1 : ℂ) ^ j * (j - 1).factorial * Sd‖ := by
      calc
        ‖(-1 : ℂ) ^ j * (j - 1).factorial * Sd‖ =
            ‖F - (F - (-1 : ℂ) ^ j *
              (j - 1).factorial * Sd)‖ := by
          congr 1
          ring
        _ ≤ _ := norm_sub_le _ _
    simpa [norm_mul] using htri
  have hfacPos : (0 : ℝ) < (j - 1).factorial := by positivity
  have hFbound :
      ((j - 1).factorial : ℝ) * (1 / 12 : ℝ) *
          (2 * eta)⁻¹ ^ j < ‖F‖ := by
    have htailNonneg : 0 ≤ ‖Sd - Sz‖ := norm_nonneg _
    have hderivNonneg : 0 ≤
        ‖F - (-1 : ℂ) ^ j * (j - 1).factorial * Sd‖ := norm_nonneg _
    have htailUse := htailNorm
    have hderivUse :
        ‖F - (-1 : ℂ) ^ j * (j - 1).factorial * Sd‖ ≤
          (j - 1).factorial *
            (16 * ((Ad : ℝ) * Real.log (|t| + 2)) / 3) := by
      simpa only [F] using hderivNorm
    nlinarith
  simpa only [F] using hFbound

/-- Fixed numerical parameters which make the conductor-one pointwise
detector error fit inside its Turán budget. -/
theorem exists_zetaPointwiseZeroDetector_parameters
    (Al Af Ad : ℕ) :
    ∃ L : ℕ, 2 ≤ L ∧ ∃ lambda : ℝ, 0 < lambda ∧
      ∀ (t eta : ℝ) (j : ℕ),
        0 < eta → eta ≤ 1 / 8 →
        eta * Real.log (|t| + 2) ≤ lambda →
        L ≤ j →
        zetaPointwiseZeroDetectorError Al Af Ad t eta j ≤
          (1 / 12 : ℝ) * (2 * eta)⁻¹ ^ j := by
  let C : ℝ := Real.log 4 + 4
  have hC : 0 < C := by dsimp [C]; positivity
  have htarget : 0 < (1 : ℝ) / (48 * (96 * C)) := by positivity
  obtain ⟨L₀, hL₀⟩ := exists_pow_lt_of_lt_one htarget
    (by norm_num : (1 / 2 : ℝ) < 1)
  let L := max 2 L₀
  have hL2 : 2 ≤ L := le_max_left _ _
  have hgeomL : 96 * C * (1 / 2 : ℝ) ^ L ≤ 1 / 48 := by
    have hpow : (1 / 2 : ℝ) ^ L ≤ (1 / 2 : ℝ) ^ L₀ :=
      pow_le_pow_of_le_one (by positivity) (by norm_num) (le_max_right _ _)
    have hsmall : 96 * C * (1 / 2 : ℝ) ^ L₀ < 1 / 48 := by
      have hpos : 0 < 48 * (96 * C) := by positivity
      calc
        96 * C * (1 / 2 : ℝ) ^ L₀ <
            96 * C * (1 / (48 * (96 * C))) := by
          exact mul_lt_mul_of_pos_left hL₀ (by positivity)
        _ = 1 / 48 := by field_simp
    exact (mul_le_mul_of_nonneg_left hpow (by positivity)).trans hsmall.le
  let K : ℝ := 1 + 4096 * (Al : ℝ) / 3 + 4 * (Af : ℝ) +
    8 * (Ad : ℝ) / 3
  have hK : 0 < K := by
    dsimp [K]
    positivity
  let lambda : ℝ := 1 / (96 * K)
  have hlambda : 0 < lambda := by dsimp [lambda]; positivity
  refine ⟨L, hL2, lambda, hlambda, ?_⟩
  intro t eta j heta0 heta8 hetalog hLj
  let u : ℝ := Real.log (|t| + 2)
  have hu : 0 ≤ u := Real.log_nonneg (by linarith [abs_nonneg t])
  have heta : 0 ≤ eta := heta0.le
  have hhalfj : (1 / 2 : ℝ) ^ j ≤ (1 / 2 : ℝ) ^ L :=
    pow_le_pow_of_le_one (by positivity) (by norm_num) hLj
  have hgeom : 96 * C * (1 / 2 : ℝ) ^ j ≤ 1 / 48 :=
    (mul_le_mul_of_nonneg_left hhalfj (by positivity)).trans hgeomL
  have hetaU : eta * u ≤ lambda := by simpa only [u] using hetalog
  have heta2U : eta ^ 2 * u ≤ lambda / 8 := by
    calc
      eta ^ 2 * u = eta * (eta * u) := by ring
      _ ≤ eta * lambda := mul_le_mul_of_nonneg_left hetaU heta
      _ ≤ (1 / 8 : ℝ) * lambda :=
        mul_le_mul_of_nonneg_right heta8 hlambda.le
      _ = lambda / 8 := by ring
  have hbase4 : 0 ≤ 4 * eta := by positivity
  have hbase4one : 4 * eta ≤ 1 := by linarith
  have hpow4 : (4 * eta) ^ j ≤ (4 * eta) ^ 2 :=
    pow_le_pow_of_le_one hbase4 hbase4one (hL2.trans hLj)
  have hbase2 : 0 ≤ 2 * eta := by positivity
  have hbase2one : 2 * eta ≤ 1 := by linarith
  have hpow2 : (2 * eta) ^ j ≤ (2 * eta) ^ 2 :=
    pow_le_pow_of_le_one hbase2 hbase2one (hL2.trans hLj)
  let c1 : ℝ := 96 * C * (1 / 2 : ℝ) ^ j
  let c2 : ℝ := (4096 * (Al : ℝ) / 3) * (eta * u) *
    (1 / 2 : ℝ) ^ j
  let c3 : ℝ := 2 * (Af : ℝ) * u * (4 * eta) ^ j
  let c4 : ℝ := 16 * (Ad : ℝ) * u / 3 * (2 * eta) ^ j
  have hc1 : c1 ≤ 1 / 48 := by simpa only [c1] using hgeom
  have hc2 : c2 ≤ (4096 * (Al : ℝ) / 3) * lambda := by
    dsimp [c2]
    have hhalfOne : (1 / 2 : ℝ) ^ j ≤ 1 := by
      exact pow_le_one₀ (by positivity) (by norm_num)
    have hcoef : 0 ≤ 4096 * (Al : ℝ) / 3 := by positivity
    calc
      (4096 * (Al : ℝ) / 3) * (eta * u) * (1 / 2 : ℝ) ^ j ≤
          (4096 * (Al : ℝ) / 3) * lambda * (1 / 2 : ℝ) ^ j := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hetaU hcoef) (by positivity)
      _ ≤ (4096 * (Al : ℝ) / 3) * lambda := by
        exact mul_le_of_le_one_right (by positivity) hhalfOne
  have hc3 : c3 ≤ 4 * (Af : ℝ) * lambda := by
    dsimp [c3]
    calc
      2 * (Af : ℝ) * u * (4 * eta) ^ j ≤
          2 * (Af : ℝ) * u * (4 * eta) ^ 2 := by
        exact mul_le_mul_of_nonneg_left hpow4 (mul_nonneg (by positivity) hu)
      _ = 32 * (Af : ℝ) * (eta ^ 2 * u) := by ring
      _ ≤ 32 * (Af : ℝ) * (lambda / 8) := by
        exact mul_le_mul_of_nonneg_left heta2U (by positivity)
      _ = 4 * (Af : ℝ) * lambda := by ring
  have hc4 : c4 ≤ 8 * (Ad : ℝ) / 3 * lambda := by
    dsimp [c4]
    calc
      16 * (Ad : ℝ) * u / 3 * (2 * eta) ^ j ≤
          16 * (Ad : ℝ) * u / 3 * (2 * eta) ^ 2 := by
        exact mul_le_mul_of_nonneg_left hpow2 (by positivity)
      _ = (64 * (Ad : ℝ) / 3) * (eta ^ 2 * u) := by ring
      _ ≤ (64 * (Ad : ℝ) / 3) * (lambda / 8) := by
        exact mul_le_mul_of_nonneg_left heta2U (by positivity)
      _ = 8 * (Ad : ℝ) / 3 * lambda := by ring
  have hrest : c2 + c3 + c4 ≤ K * lambda := by
    dsimp [K]
    linarith
  have hKlambda : K * lambda = 1 / 96 := by
    dsimp [lambda]
    field_simp
  have hcoeff : c1 + c2 + c3 + c4 ≤ 1 / 12 := by
    rw [hKlambda] at hrest
    nlinarith
  let X : ℝ := (2 * eta) ^ j
  have hXpos : 0 < X := by dsimp [X]; positivity
  have hratio : (2 * eta) / (4 * eta) = (1 / 2 : ℝ) := by
    field_simp [heta0.ne']
    norm_num
  have ht1 :
      (96 * C / (4 * eta) ^ j) * X = c1 := by
    dsimp [X, c1]
    calc
      (96 * C / (4 * eta) ^ j) * (2 * eta) ^ j =
          96 * C * ((2 * eta) ^ j / (4 * eta) ^ j) := by ring
      _ = 96 * C * ((2 * eta) / (4 * eta)) ^ j := by rw [div_pow]
      _ = 96 * C * (1 / 2 : ℝ) ^ j := by rw [hratio]
  have ht2 :
      (((1024 * (Al : ℝ) / 3) * u) / (4 * eta) ^ (j - 1)) * X = c2 := by
    let k := j - 1
    have hk : j - 1 = k := rfl
    have hj : j = k + 1 := by dsimp [k]; omega
    dsimp [X, c2]
    rw [show (1 / 2 : ℝ) ^ j =
        ((2 * eta) / (4 * eta)) ^ j by rw [hratio]]
    rw [div_pow, hk, hj, pow_succ, pow_succ]
    field_simp [heta0.ne']
    ring
  have ht3 :
      ((2 * (Af : ℝ) * u) / (1 / 2 : ℝ) ^ j) * X = c3 := by
    dsimp [X, c3]
    calc
      ((2 * (Af : ℝ) * u) / (1 / 2 : ℝ) ^ j) * (2 * eta) ^ j =
          2 * (Af : ℝ) * u *
            ((2 * eta) ^ j / (1 / 2 : ℝ) ^ j) := by ring
      _ = 2 * (Af : ℝ) * u *
            ((2 * eta) / (1 / 2 : ℝ)) ^ j := by rw [← div_pow]
      _ = 2 * (Af : ℝ) * u * (4 * eta) ^ j := by ring_nf
  have ht4 :
      (16 * ((Ad : ℝ) * u) / 3) * X = c4 := by
    dsimp [X, c4]
    ring
  have herrorMul :
      zetaPointwiseZeroDetectorError Al Af Ad t eta j * X =
        c1 + c2 + c3 + c4 := by
    dsimp [zetaPointwiseZeroDetectorError]
    change
      (96 * C / (4 * eta) ^ j +
          ((1024 * (Al : ℝ) / 3) * u) / (4 * eta) ^ (j - 1) +
          (2 * (Af : ℝ) * u) / (1 / 2 : ℝ) ^ j +
          16 * ((Ad : ℝ) * u) / 3) * X = _
    rw [add_mul, add_mul, add_mul, ht1, ht2, ht3, ht4]
  have hscaled :
      zetaPointwiseZeroDetectorError Al Af Ad t eta j * X ≤ 1 / 12 := by
    rw [herrorMul]
    exact hcoeff
  have htargetEq :
      (1 / 12 : ℝ) * (2 * eta)⁻¹ ^ j = (1 / 12 : ℝ) / X := by
    dsimp [X]
    rw [inv_pow]
    ring
  rw [htargetEq]
  exact (le_div_iff₀ hXpos).2 hscaled

/-- A finite, height-independent range of derivative orders detects every
zero of `riemannZeta₁` in the conductor-one log-free strip. -/
theorem exists_uniform_zeta_pointwise_zero_detector :
    ∃ L J : ℕ, 2 ≤ L ∧ L ≤ J ∧
      ∃ lambda : ℝ, 0 < lambda ∧
        ∀ (t eta : ℝ), 0 < eta → eta ≤ 1 / 8 →
          eta * Real.log (|t| + 2) ≤ lambda →
            ∀ rho₀ : ℂ,
              riemannZeta₁ rho₀ = 0 →
              dist rho₀ (((1 + eta : ℝ) : ℂ) + t * I) ≤ 2 * eta →
                ∃ j : ℕ,
                  L ≤ j ∧ j ≤ J ∧
                    (j - 1).factorial * (1 / 12 : ℝ) *
                        (2 * eta)⁻¹ ^ j <
                      ‖iteratedDeriv (j - 1)
                        (fun w ↦ -logDeriv riemannZeta₁ w)
                        (((1 + eta : ℝ) : ℂ) + t * I)‖ := by
  obtain ⟨Am, Al, Af, Ad, hAm, hAl, hAf, hAd, hdetector⟩ :=
    exists_zeta_pointwise_zero_detector_of_error_budget
  obtain ⟨L, hL2, lambda, hlambda, hparameters⟩ :=
    exists_zetaPointwiseZeroDetector_parameters Al Af Ad
  obtain ⟨Am', hAm', hmass⟩ := exists_zetaSmallDiskZeroMultiplicity_bound
  let C : ℝ := Real.log 4 + 4
  let M0 : ℝ := 48 * C + (256 * (Am' : ℝ) / 3) * lambda
  let M : ℕ := Nat.ceil M0
  let J : ℕ := L * M
  have hC : 0 < C := by dsimp [C]; positivity
  have hM0 : 0 < M0 := by
    dsimp [M0]
    positivity
  have hMpos : 0 < M := Nat.ceil_pos.mpr hM0
  have hLJ : L ≤ J := by
    dsimp [J]
    exact Nat.le_mul_of_pos_right L hMpos
  refine ⟨L, J, hL2, hLJ, lambda, hlambda, ?_⟩
  intro t eta heta0 heta8 hetalog rho₀ hzero hrho
  let Z := zetaSmallDiskZeroFinsupp t eta
  have hmass' := hmass t eta heta0 (by linarith : eta ≤ 1)
  have hmassM0 : Z.sum (fun _ m ↦ (m : ℝ)) ≤ M0 := by
    calc
      Z.sum (fun _ m ↦ (m : ℝ)) ≤
          48 * C + (256 * (Am' : ℝ) / 3) * eta *
            Real.log (|t| + 2) := by
        simpa only [Z, C] using hmass'
      _ ≤ 48 * C + (256 * (Am' : ℝ) / 3) * lambda := by
        have hsecond :
            (256 * (Am' : ℝ) / 3) * eta * Real.log (|t| + 2) ≤
              (256 * (Am' : ℝ) / 3) * lambda := by
          calc
          (256 * (Am' : ℝ) / 3) * eta * Real.log (|t| + 2) =
              (256 * (Am' : ℝ) / 3) *
                (eta * Real.log (|t| + 2)) := by ring
          _ ≤ (256 * (Am' : ℝ) / 3) * lambda :=
            mul_le_mul_of_nonneg_left hetalog (by positivity)
        exact add_le_add_right hsecond (48 * C)
      _ = M0 := rfl
  have hmassM : Z.sum (fun _ m ↦ m) ≤ M := by
    have hcast :
        ((Z.sum (fun _ m ↦ m) : ℕ) : ℝ) ≤ (M : ℝ) := by
      rw [Nat.cast_finsupp_sum]
      exact hmassM0.trans (Nat.le_ceil M0)
    exact_mod_cast hcast
  have hbudget :
      ∀ j : ℕ, L ≤ j → j ≤ L * Z.sum (fun _ m ↦ m) →
        zetaPointwiseZeroDetectorError Al Af Ad t eta j ≤
          (1 / 12 : ℝ) * (2 * eta)⁻¹ ^ j := by
    intro j hjL hjupper
    exact hparameters t eta j heta0 heta8 hetalog hjL
  obtain ⟨j, hjL, hjZ, hjlarge⟩ :=
    hdetector t eta heta0 heta8 rho₀ hzero hrho L hL2 hbudget
  refine ⟨j, hjL, ?_, hjlarge⟩
  exact hjZ.trans (Nat.mul_le_mul_left L hmassM)

/-- At ordinates separated from the pole, a detected high derivative of the
entire regularization gives a detector for the conductor-one von Mangoldt
Dirichlet series. -/
theorem exists_uniform_zeta_weightedLSeries_detector :
    ∃ L J : ℕ, 2 ≤ L ∧ L ≤ J ∧
      ∃ lambda : ℝ, 0 < lambda ∧
        ∀ (t eta : ℝ), 1 ≤ |t| → 0 < eta → eta ≤ 1 / 8 →
          eta * Real.log (|t| + 2) ≤ lambda →
            ∀ rho₀ : ℂ,
              riemannZeta₁ rho₀ = 0 →
              dist rho₀ (((1 + eta : ℝ) : ℂ) + t * I) ≤ 2 * eta →
                ∃ j : ℕ,
                  L ≤ j ∧ j ≤ J ∧
                    (j - 1).factorial * (1 / 48 : ℝ) *
                        (2 * eta)⁻¹ ^ j <
                      ‖LSeries (fun n : ℕ ↦
                          (Real.log n : ℂ) ^ (j - 1) *
                            (1 : DirichletCharacter ℂ 1) n *
                            (ArithmeticFunction.vonMangoldt n : ℂ))
                        (((1 + eta : ℝ) : ℂ) + t * I)‖ := by
  obtain ⟨L, J, hL2, hLJ, lambda, hlambda, hdetector⟩ :=
    exists_uniform_zeta_pointwise_zero_detector
  refine ⟨L, J, hL2, hLJ, lambda, hlambda, ?_⟩
  intro t eta ht heta0 heta8 hetalog rho₀ hzero hrho
  obtain ⟨j, hjL, hjJ, hjlarge⟩ :=
    hdetector t eta heta0 heta8 hetalog rho₀ hzero hrho
  refine ⟨j, hjL, hjJ, ?_⟩
  let z : ℂ := ((1 + eta : ℝ) : ℂ) + t * I
  let k : ℕ := j - 1
  have hzre : z.re = 1 + eta := by simp [z]
  have hz1 : 1 < z.re := by rw [hzre]; linarith
  have hzOne : z ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp [z] at hre
    linarith
  have hzeta : riemannZeta z ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re hz1.le
  have hzeta₁ : riemannZeta₁ z ≠ 0 := by
    intro hzero₁
    have hfactor := riemannZeta_eq_inv_sub_mul hzOne
    rw [hzero₁, mul_zero] at hfactor
    exact hzeta hfactor
  let U : Set ℂ := {w | 1 < w.re}
  have hUopen : IsOpen U := isOpen_lt continuous_const continuous_re
  have heq : Set.EqOn
      (fun w : ℂ ↦ -logDeriv riemannZeta w)
      (fun w : ℂ ↦ (w - 1)⁻¹ + (-logDeriv riemannZeta₁ w)) U := by
    intro w hw
    change 1 < w.re at hw
    have hwOne : w ≠ 1 := by
      intro h
      have hre := congrArg Complex.re h
      simp at hre
      linarith
    have hwzeta : riemannZeta w ≠ 0 :=
      riemannZeta_ne_zero_of_one_le_re hw.le
    simpa [sub_eq_add_neg] using
      neg_logDeriv_riemannZeta_eq_pole_sub_regularized_of_ne_zero
        w hwOne hwzeta
  have hderivEq := heq.iteratedDeriv_of_isOpen hUopen k hz1
  have hpoleAnalytic : AnalyticAt ℂ (fun w : ℂ ↦ (w - 1)⁻¹) z :=
    (analyticAt_id.sub analyticAt_const).inv (sub_ne_zero.mpr hzOne)
  have hregAnalytic : AnalyticAt ℂ
      (fun w : ℂ ↦ -logDeriv riemannZeta₁ w) z := by
    have hf := differentiable_riemannZeta₁.analyticAt z
    have hlog : AnalyticAt ℂ (logDeriv riemannZeta₁) z := by
      simpa [logDeriv] using hf.deriv.div hf hzeta₁
    have hlog' : AnalyticAt ℂ
        (fun w : ℂ ↦ logDeriv riemannZeta₁ w) z := by
      simpa only using hlog
    exact hlog'.neg
  have hadd :
      iteratedDeriv k
          (fun w : ℂ ↦ (w - 1)⁻¹ + (-logDeriv riemannZeta₁ w)) z =
        iteratedDeriv k (fun w : ℂ ↦ (w - 1)⁻¹) z +
          iteratedDeriv k (fun w : ℂ ↦ -logDeriv riemannZeta₁ w) z := by
    exact iteratedDeriv_add hpoleAnalytic.contDiffAt hregAnalytic.contDiffAt
  rw [hadd] at hderivEq
  have hregEq :
      iteratedDeriv k (fun w : ℂ ↦ -logDeriv riemannZeta₁ w) z =
        iteratedDeriv k (fun w : ℂ ↦ -logDeriv riemannZeta w) z -
          iteratedDeriv k (fun w : ℂ ↦ (w - 1)⁻¹) z := by
    rw [hderivEq]
    ring
  have hpoleFormula :
      iteratedDeriv k (fun w : ℂ ↦ (w - 1)⁻¹) z =
        (-1 : ℂ) ^ k * k.factorial *
          (z - 1) ^ (-1 - (k : ℤ)) := by
    have hinv := iter_deriv_inv_linear_sub (𝕜 := ℂ) k 1
    simp only [one_mul, one_pow] at hinv
    simpa [iteratedDeriv_eq_iterate] using congrFun (hinv (1 : ℂ)) z
  have hnormz : 1 ≤ ‖z - 1‖ := by
    calc
      1 ≤ |t| := ht
      _ = |(z - 1).im| := by simp [z]
      _ ≤ ‖z - 1‖ := Complex.abs_im_le_norm _
  have hzpow : ‖(z - 1) ^ (-1 - (k : ℤ))‖ ≤ 1 := by
    have hexp : (-1 - (k : ℤ)) = -((k + 1 : ℕ) : ℤ) := by omega
    rw [hexp, zpow_neg, zpow_natCast, norm_inv, norm_pow]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ hnormz)
  have hpoleNorm :
      ‖iteratedDeriv k (fun w : ℂ ↦ (w - 1)⁻¹) z‖ ≤ k.factorial := by
    rw [hpoleFormula, norm_mul, norm_mul, norm_pow, norm_neg, norm_one,
      one_pow, one_mul, Complex.norm_natCast]
    simpa only [Nat.cast_nonneg] using
      mul_le_of_le_one_right (Nat.cast_nonneg k.factorial) hzpow
  have htri :
      ‖iteratedDeriv k (fun w : ℂ ↦ -logDeriv riemannZeta₁ w) z‖ ≤
        ‖iteratedDeriv k (fun w : ℂ ↦ -logDeriv riemannZeta w) z‖ +
          ‖iteratedDeriv k (fun w : ℂ ↦ (w - 1)⁻¹) z‖ := by
    rw [hregEq]
    exact norm_sub_le _ _
  have hj2 : 2 ≤ j := hL2.trans hjL
  have hbase : (16 : ℝ) ≤ (2 * eta)⁻¹ ^ j := by
    have htwoeta : 0 < 2 * eta := by positivity
    have hinv4 : (4 : ℝ) ≤ (2 * eta)⁻¹ := by
      rw [inv_eq_one_div]
      rw [le_div_iff₀ htwoeta]
      nlinarith
    calc
      (16 : ℝ) = 4 ^ 2 := by norm_num
      _ ≤ 4 ^ j := pow_le_pow_right₀ (by norm_num) hj2
      _ ≤ (2 * eta)⁻¹ ^ j := pow_le_pow_left₀ (by positivity) hinv4 j
  have hzetalarge :
      ((j - 1).factorial : ℝ) * (1 / 48 : ℝ) *
          (2 * eta)⁻¹ ^ j <
        ‖iteratedDeriv (j - 1)
          (fun w : ℂ ↦ -logDeriv riemannZeta w) z‖ := by
    have hfacPos : (0 : ℝ) < (j - 1).factorial := by positivity
    have hpoleUse :
        ‖iteratedDeriv k (fun w : ℂ ↦ (w - 1)⁻¹) z‖ ≤
          ((j - 1).factorial : ℝ) := by simpa only [k] using hpoleNorm
    have htriUse := htri
    have hlargeUse :
        ((j - 1).factorial : ℝ) * (1 / 12 : ℝ) *
            (2 * eta)⁻¹ ^ j <
          ‖iteratedDeriv k
            (fun w : ℂ ↦ -logDeriv riemannZeta₁ w) z‖ := by
      simpa only [k, z] using hjlarge
    nlinarith
  have hseries :=
    iteratedDeriv_neg_logDeriv_LFunction_eq_weighted_LSeries
      (k := j - 1) (1 : DirichletCharacter ℂ 1) hz1
  rw [DirichletCharacter.LFunction_modOne_eq] at hseries
  rw [hseries] at hzetalarge
  simpa only [z, norm_mul, norm_pow, norm_neg, norm_one, one_pow,
    one_mul] using hzetalarge

/-- Enlarging the standard uniform truncation radius by `4 log 8` shrinks
its tail budget from `1/24` to `1/192`. -/
theorem exists_zeta_weighted_vonMangoldt_tail_budget (J : ℕ) :
    ∃ R : ℝ, 0 < R ∧
      ∀ (eta : ℝ), 0 < eta → eta ≤ 1 →
        ∀ k : ℕ, k + 1 ≤ J →
          Real.exp (-R / 4) * k.factorial * (4 / eta) ^ k *
              ((Real.log 4 + 4) * (1 + eta / 2) / (eta / 2)) ≤
            k.factorial * (1 / 192 : ℝ) * (2 * eta)⁻¹ ^ (k + 1) := by
  obtain ⟨R₀, hR₀, hbudget⟩ := exists_weighted_vonMangoldt_tail_budget J
  let R : ℝ := R₀ + 4 * Real.log 8
  have hlog8 : 0 < Real.log (8 : ℝ) := Real.log_pos (by norm_num)
  have hR : 0 < R := by dsimp [R]; positivity
  refine ⟨R, hR, ?_⟩
  intro eta heta heta1 k hkJ
  have hraw := hbudget eta heta heta1 k hkJ
  have hexp : Real.exp (-R / 4) = (1 / 8 : ℝ) * Real.exp (-R₀ / 4) := by
    have harg : -R / 4 = -Real.log 8 + (-R₀ / 4) := by
      dsimp [R]
      ring
    rw [harg, Real.exp_add, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 8)]
    ring
  calc
    Real.exp (-R / 4) * k.factorial * (4 / eta) ^ k *
        ((Real.log 4 + 4) * (1 + eta / 2) / (eta / 2)) =
      (1 / 8 : ℝ) *
        (Real.exp (-R₀ / 4) * k.factorial * (4 / eta) ^ k *
          ((Real.log 4 + 4) * (1 + eta / 2) / (eta / 2))) := by
        rw [hexp]
        ring
    _ ≤ (1 / 8 : ℝ) *
        (k.factorial * (1 / 24 : ℝ) * (2 * eta)⁻¹ ^ (k + 1)) :=
      mul_le_mul_of_nonneg_left hraw (by norm_num)
    _ = k.factorial * (1 / 192 : ℝ) *
        (2 * eta)⁻¹ ^ (k + 1) := by ring

/-- The conductor-one detector after uniform finite truncation. -/
theorem exists_uniform_zeta_finite_series_detector :
    ∃ L J : ℕ, 2 ≤ L ∧ L ≤ J ∧
      ∃ lambda R : ℝ, 0 < lambda ∧ 0 < R ∧
        ∀ (t eta : ℝ), 1 ≤ |t| → 0 < eta → eta ≤ 1 / 8 →
          eta * Real.log (|t| + 2) ≤ lambda →
            ∀ rho₀ : ℂ,
              riemannZeta₁ rho₀ = 0 →
              dist rho₀ (((1 + eta : ℝ) : ℂ) + t * I) ≤ 2 * eta →
                ∃ j : ℕ,
                  L ≤ j ∧ j ≤ J ∧
                    (j - 1).factorial * (1 / 64 : ℝ) *
                        (2 * eta)⁻¹ ^ j <
                      ‖∑ n ∈ Finset.Icc 1 (zeroDetectorCutoff R eta),
                        LSeries.term (fun m : ℕ ↦
                          (Real.log m : ℂ) ^ (j - 1) *
                            (1 : DirichletCharacter ℂ 1) m *
                            (ArithmeticFunction.vonMangoldt m : ℂ))
                          (((1 + eta : ℝ) : ℂ) + t * I) n‖ := by
  obtain ⟨L, J, hL2, hLJ, lambda, hlambda, hdetector⟩ :=
    exists_uniform_zeta_weightedLSeries_detector
  obtain ⟨R, hR, htailBudget⟩ :=
    exists_zeta_weighted_vonMangoldt_tail_budget J
  refine ⟨L, J, hL2, hLJ, lambda, R, hlambda, hR, ?_⟩
  intro t eta ht heta0 heta8 hetalog rho₀ hzero hrho
  obtain ⟨j, hjL, hjJ, hjfull⟩ :=
    hdetector t eta ht heta0 heta8 hetalog rho₀ hzero hrho
  let chi : DirichletCharacter ℂ 1 := 1
  let z : ℂ := ((1 + eta : ℝ) : ℂ) + t * I
  let c : ℕ → ℂ := fun m ↦
    (Real.log m : ℂ) ^ (j - 1) * chi m *
      (ArithmeticFunction.vonMangoldt m : ℂ)
  let N : ℕ := zeroDetectorCutoff R eta
  let P : ℂ := ∑ n ∈ Finset.Icc 1 N, LSeries.term c z n
  let Btail : ℝ := (j - 1).factorial * (1 / 192 : ℝ) *
    (2 * eta)⁻¹ ^ j
  let Bfinite : ℝ := (j - 1).factorial * (1 / 64 : ℝ) *
    (2 * eta)⁻¹ ^ j
  have hNpos : 0 < N := by
    simpa only [N] using zeroDetectorCutoff_pos R eta
  have hNexp : Real.exp (R / eta) ≤ (N : ℝ) := by
    simpa only [N] using exp_div_le_zeroDetectorCutoff R eta
  have htailRaw := norm_weighted_vonMangoldt_LSeries_sub_sum_le
    chi eta R t heta0 (by linarith : eta ≤ 1) N (j - 1)
      hNpos hNexp
  have horder : j - 1 + 1 ≤ J := by omega
  have htailBudget' := htailBudget eta heta0 (by linarith : eta ≤ 1)
    (j - 1) horder
  have htail : ‖LSeries c z - P‖ ≤ Btail := by
    exact htailRaw.trans (by
      simpa only [chi, c, z, N, P, Btail, show j - 1 + 1 = j by omega]
        using htailBudget')
  have hfull :
      (j - 1).factorial * (1 / 48 : ℝ) * (2 * eta)⁻¹ ^ j <
        ‖LSeries c z‖ := by
    simpa only [chi, c, z] using hjfull
  have htri : ‖LSeries c z‖ ≤ ‖P‖ + ‖LSeries c z - P‖ := by
    calc
      ‖LSeries c z‖ = ‖P + (LSeries c z - P)‖ := by congr 1; ring
      _ ≤ ‖P‖ + ‖LSeries c z - P‖ := norm_add_le _ _
  refine ⟨j, hjL, hjJ, ?_⟩
  change Bfinite < ‖P‖
  have hscale : 0 ≤ ((j - 1).factorial : ℝ) * (2 * eta)⁻¹ ^ j := by
    positivity
  dsimp [Btail, Bfinite] at htail ⊢
  nlinarith

/-- Every detected zeta zero produces a short interval on which its
conductor-one polynomial stays above the `1/96` threshold used by the
mean-square counting lemma. -/
theorem exists_uniform_propagated_zeta_finite_series_detector :
    ∃ L J : ℕ, 2 ≤ L ∧ L ≤ J ∧
      ∃ lambda R delta : ℝ,
        0 < lambda ∧ 0 < R ∧ 0 < delta ∧ delta ≤ 1 ∧
        ∀ (t eta : ℝ), 1 ≤ |t| → 0 < eta → eta ≤ 1 / 8 →
          eta * Real.log (|t| + 2) ≤ lambda →
            ∀ rho₀ : ℂ,
              riemannZeta₁ rho₀ = 0 →
              dist rho₀ (((1 + eta : ℝ) : ℂ) + t * I) ≤ 2 * eta →
                ∃ j : ℕ,
                  L ≤ j ∧ j ≤ J ∧
                    ∀ u : ℝ, |u - t| ≤ delta * eta →
                      (j - 1).factorial * (1 / 96 : ℝ) *
                          (2 * eta)⁻¹ ^ j <
                        ‖finiteZeroDetectorPolynomial
                          (1 : DirichletCharacter ℂ 1) eta (j - 1)
                          (zeroDetectorCutoff R eta) u‖ := by
  obtain ⟨L, J, hL2, hLJ, lambda, R, hlambda, hR, hdetector⟩ :=
    exists_uniform_zeta_finite_series_detector
  let C : ℝ := Real.log 4 + 4
  let delta₀ : ℝ := (144 * C * (J : ℝ) * (4 : ℝ) ^ J)⁻¹
  let delta : ℝ := delta₀ / 4
  have hJ : 1 ≤ J := by omega
  have hC : 0 < C := by dsimp [C]; positivity
  have hJR : (0 : ℝ) < J := by exact_mod_cast hJ
  have hdelta₀ : 0 < delta₀ := by dsimp [delta₀]; positivity
  have hdelta : 0 < delta := by dsimp [delta]; positivity
  have hdelta1 : delta ≤ 1 := by
    have hdelta₀1 : delta₀ ≤ 1 := by
      have hC1 : (1 : ℝ) ≤ C := by
        dsimp [C]
        have : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
        linarith
      have hJ1 : (1 : ℝ) ≤ J := by exact_mod_cast hJ
      have hpow1 : (1 : ℝ) ≤ (4 : ℝ) ^ J := one_le_pow₀ (by norm_num)
      apply inv_le_one_of_one_le₀
      calc
        (1 : ℝ) ≤ 144 * 1 * 1 * 1 := by norm_num
        _ ≤ 144 * C * (J : ℝ) * (4 : ℝ) ^ J := by gcongr
    dsimp [delta]
    linarith
  refine ⟨L, J, hL2, hLJ, lambda, R, delta,
    hlambda, hR, hdelta, hdelta1, ?_⟩
  intro t eta ht heta heta8 hetalog rho₀ hzero hrho
  obtain ⟨j, hjL, hjJ, hjlargeRaw⟩ :=
    hdetector t eta ht heta heta8 hetalog rho₀ hzero hrho
  have hj : 1 ≤ j := by omega
  let chi : DirichletCharacter ℂ 1 := 1
  let N : ℕ := zeroDetectorCutoff R eta
  let P : ℝ → ℂ := fun u ↦
    finiteZeroDetectorPolynomial chi eta (j - 1) N u
  let Bfinite : ℝ := (j - 1).factorial * (1 / 64 : ℝ) *
    (2 * eta)⁻¹ ^ j
  let Bdiff : ℝ := (j - 1).factorial * (1 / 192 : ℝ) *
    (2 * eta)⁻¹ ^ j
  let Bout : ℝ := (j - 1).factorial * (1 / 96 : ℝ) *
    (2 * eta)⁻¹ ^ j
  have htlarge : Bfinite < ‖P t‖ := by
    rw [show P t =
        ∑ n ∈ Finset.Icc 1 N,
          LSeries.term (fun m : ℕ ↦
            (Real.log m : ℂ) ^ (j - 1) * chi m *
              (ArithmeticFunction.vonMangoldt m : ℂ))
            (((1 + eta : ℝ) : ℂ) + t * I) n by
      dsimp [P]
      exact (weighted_vonMangoldt_LSeries_sum_eq_polynomial
        chi eta t (j - 1) N).symm]
    simpa only [chi, N, Bfinite] using hjlargeRaw
  refine ⟨j, hjL, hjJ, ?_⟩
  intro u hu
  have heta1 : eta ≤ 1 := by linarith
  have hsum := weightedVonMangoldtMajorant_tsum_le eta heta heta1 j
  have hsum0 : 0 ≤ ∑' n, weightedVonMangoldtMajorant eta j n :=
    tsum_nonneg fun n ↦ by unfold weightedVonMangoldtMajorant; positivity
  have htu : |t - u| ≤ delta * eta := by
    simpa only [abs_sub_comm] using hu
  have hlip := norm_finiteZeroDetectorPolynomial_sub_le_tsum
    chi eta heta (j - 1) N t u
  have hlip' : ‖P t - P u‖ ≤
      |t - u| * ∑' n, weightedVonMangoldtMajorant eta j n := by
    simpa only [P, show j - 1 + 1 = j by omega] using hlip
  have hbudget₀ := detector_propagation_budget J j hJ hj hjJ eta heta
  have hbudget :
      delta * eta *
          (3 * C * j.factorial * (2 / eta) ^ j / eta) ≤ Bdiff := by
    calc
      delta * eta *
          (3 * C * j.factorial * (2 / eta) ^ j / eta) =
        (1 / 4 : ℝ) *
          (delta₀ * eta *
            (3 * C * j.factorial * (2 / eta) ^ j / eta)) := by
          dsimp [delta]
          ring
      _ ≤ (1 / 4 : ℝ) *
          ((j - 1).factorial * (1 / 48 : ℝ) *
            (2 * eta)⁻¹ ^ j) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        simpa only [C, delta₀] using hbudget₀
      _ = Bdiff := by dsimp [Bdiff]; ring
  have hdiff : ‖P t - P u‖ ≤ Bdiff := by
    refine hlip'.trans ((mul_le_mul htu hsum hsum0 (by positivity)).trans ?_)
    exact hbudget
  have htri : ‖P t‖ ≤ ‖P u‖ + ‖P t - P u‖ := by
    calc
      ‖P t‖ = ‖P u + (P t - P u)‖ := by congr 1; ring
      _ ≤ ‖P u‖ + ‖P t - P u‖ := norm_add_le _ _
  change Bout < ‖P u‖
  have hscale : 0 ≤ ((j - 1).factorial : ℝ) * (2 * eta)⁻¹ ^ j := by
    positivity
  dsimp [Bfinite, Bdiff, Bout] at htlarge hdiff ⊢
  nlinarith

/-- Zeros of the entire regularization in the upper high-zero rectangle;
the lower ordinate is one so that the zeta pole-removal estimate is uniform. -/
noncomputable def zetaHighZeroRectangle (eta T : ℝ) : Finset ℂ :=
  let U : Set ℂ := closedBall 0 (T + 2)
  (divisor_riemannZeta₁_closedBall_support_finite 0 (T + 2)).toFinset.filter
    fun rho ↦
      1 - eta ≤ rho.re ∧ rho.re ≤ 1 ∧ 1 ≤ rho.im ∧ rho.im ≤ T

private theorem zetaHighZero_mem_closedBall
    {rho : ℂ} {eta T : ℝ} (heta1 : eta ≤ 1) (hT : 1 ≤ T)
    (hrelo : 1 - eta ≤ rho.re) (hrehi : rho.re ≤ 1)
    (himlo : 1 ≤ rho.im) (himhi : rho.im ≤ T) :
    rho ∈ closedBall (0 : ℂ) (T + 2) := by
  have hre0 : 0 ≤ rho.re := by linarith
  have him0 : 0 ≤ rho.im := by linarith
  rw [mem_closedBall, dist_zero_right]
  calc
    ‖rho‖ ≤ |rho.re| + |rho.im| := Complex.norm_le_abs_re_add_abs_im rho
    _ = rho.re + rho.im := by rw [abs_of_nonneg hre0, abs_of_nonneg him0]
    _ ≤ T + 2 := by linarith

theorem mem_zetaHighZeroRectangle_iff
    {eta T : ℝ} (heta1 : eta ≤ 1) (hT : 1 ≤ T) (rho : ℂ) :
    rho ∈ zetaHighZeroRectangle eta T ↔
      riemannZeta₁ rho = 0 ∧
        1 - eta ≤ rho.re ∧ rho.re ≤ 1 ∧
          1 ≤ rho.im ∧ rho.im ≤ T := by
  let U : Set ℂ := closedBall 0 (T + 2)
  change rho ∈
      (divisor_riemannZeta₁_closedBall_support_finite 0 (T + 2)).toFinset.filter
        (fun z ↦ 1 - eta ≤ z.re ∧ z.re ≤ 1 ∧ 1 ≤ z.im ∧ z.im ≤ T) ↔ _
  rw [Finset.mem_filter,
    (divisor_riemannZeta₁_closedBall_support_finite 0 (T + 2)).mem_toFinset]
  constructor
  · rintro ⟨hsupport, hrelo, hrehi, himlo, himhi⟩
    have hrhoU : rho ∈ U := by
      simpa only [U] using
        zetaHighZero_mem_closedBall heta1 hT hrelo hrehi himlo himhi
    exact ⟨(mem_support_divisor_riemannZeta₁_iff hrhoU).mp
      (by simpa only [U] using hsupport), hrelo, hrehi, himlo, himhi⟩
  · rintro ⟨hzero, hrelo, hrehi, himlo, himhi⟩
    have hrhoU : rho ∈ U := by
      simpa only [U] using
        zetaHighZero_mem_closedBall heta1 hT hrelo hrehi himlo himhi
    refine ⟨?_, hrelo, hrehi, himlo, himhi⟩
    simpa only [U] using (mem_support_divisor_riemannZeta₁_iff hrhoU).mpr hzero

noncomputable def zetaHighZeroOrdinates (eta T : ℝ) : Finset ℝ :=
  (zetaHighZeroRectangle eta T).image Complex.im

theorem mem_zetaHighZeroOrdinates_iff
    {eta T : ℝ} (heta1 : eta ≤ 1) (hT : 1 ≤ T) (t : ℝ) :
    t ∈ zetaHighZeroOrdinates eta T ↔
      ∃ rho : ℂ,
        riemannZeta₁ rho = 0 ∧
          1 - eta ≤ rho.re ∧ rho.re ≤ 1 ∧
            rho.im = t ∧ 1 ≤ t ∧ t ≤ T := by
  rw [zetaHighZeroOrdinates, Finset.mem_image]
  constructor
  · rintro ⟨rho, hrho, rfl⟩
    have hm := (mem_zetaHighZeroRectangle_iff heta1 hT rho).mp hrho
    exact ⟨rho, hm.1, hm.2.1, hm.2.2.1, rfl, hm.2.2.2.1, hm.2.2.2.2⟩
  · rintro ⟨rho, hzero, hrelo, hrehi, hrhoim, ht1, htT⟩
    refine ⟨rho, ?_, hrhoim⟩
    exact (mem_zetaHighZeroRectangle_iff heta1 hT rho).mpr
      ⟨hzero, hrelo, hrehi, by simpa [hrhoim] using ht1,
        by simpa [hrhoim] using htT⟩

noncomputable def zetaHighZeroRectangleMass (eta T : ℝ) : ℕ :=
  ∑ rho ∈ zetaHighZeroRectangle eta T,
    analyticOrderNatAt riemannZeta₁ rho

theorem exists_separated_zetaHighZeroOrdinates
    (eta T r : ℝ) (hr : 0 ≤ r) :
    ∃ S : Finset ℝ,
      S ⊆ zetaHighZeroOrdinates eta T ∧
        (∀ x ∈ S, ∀ y ∈ S, x ≠ y → r < dist x y) ∧
        ∀ x ∈ zetaHighZeroOrdinates eta T,
          ∃ y ∈ S, dist x y ≤ r := by
  let A : Set ℝ := zetaHighZeroOrdinates eta T
  have hA : A.Finite := (zetaHighZeroOrdinates eta T).finite_toSet
  obtain ⟨S, hSsub, hSfinite, hsep, hcover⟩ :=
    exists_finite_separated_cover A hA r hr
  refine ⟨hSfinite.toFinset, ?_, ?_, ?_⟩
  · intro x hx
    exact hSsub (hSfinite.mem_toFinset.mp hx)
  · intro x hx y hy hxy
    exact hsep x (hSfinite.mem_toFinset.mp hx)
      y (hSfinite.mem_toFinset.mp hy) hxy
  · intro x hx
    obtain ⟨y, hyS, hxy⟩ := hcover x hx
    exact ⟨y, hSfinite.mem_toFinset.mpr hyS, hxy⟩

private theorem zetaHighZero_dist_detector_center_le
    {rho : ℂ} {t eta : ℝ}
    (hrelo : 1 - eta ≤ rho.re) (hrehi : rho.re ≤ 1)
    (hrhoim : rho.im = t) (heta : 0 < eta) :
    dist rho (((1 + eta : ℝ) : ℂ) + t * I) ≤ 2 * eta := by
  rw [Complex.dist_eq]
  have heq :
      rho - (((1 + eta : ℝ) : ℂ) + t * I) =
        ((rho.re - (1 + eta) : ℝ) : ℂ) := by
    apply Complex.ext
    · simp
    · simp [hrhoim]
  rw [heq, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonpos (by linarith)]
  linarith

private theorem zeta_log_height_mono
    {t T : ℝ} (ht1 : 1 ≤ t) (htT : t ≤ T) :
    Real.log (|t| + 2) ≤ Real.log (T + 2) := by
  have hleft : 0 < |t| + 2 := by positivity
  have hright : 0 < T + 2 := by linarith
  apply Real.strictMonoOn_log.monotoneOn hleft hright
  rw [abs_of_nonneg (by linarith)]
  linarith

/-- A maximal separated family of upper zeta-zero ordinates, labelled by
the propagated detector order. -/
theorem exists_uniform_detected_zeta_zero_selection :
    ∃ L J : ℕ, 2 ≤ L ∧ L ≤ J ∧
      ∃ lambda R delta : ℝ,
        0 < lambda ∧ 0 < R ∧ 0 < delta ∧ delta ≤ 1 ∧
        ∀ (eta T : ℝ), 0 < eta → eta ≤ 1 / 8 → 1 ≤ T →
          eta * Real.log (T + 2) ≤ lambda →
            ∃ S : Finset ℝ, ∃ order : ℝ → ℕ,
              S ⊆ zetaHighZeroOrdinates eta T ∧
              (∀ x ∈ S, ∀ y ∈ S, x ≠ y →
                2 * delta * eta < dist x y) ∧
              (∀ x ∈ zetaHighZeroOrdinates eta T,
                ∃ y ∈ S, dist x y ≤ 2 * delta * eta) ∧
              ∀ t ∈ S,
                L ≤ order t ∧ order t ≤ J ∧
                  ∀ u : ℝ, |u - t| ≤ delta * eta →
                    (order t - 1).factorial * (1 / 96 : ℝ) *
                        (2 * eta)⁻¹ ^ order t <
                      ‖finiteZeroDetectorPolynomial
                        (1 : DirichletCharacter ℂ 1) eta (order t - 1)
                        (zeroDetectorCutoff R eta) u‖ := by
  obtain ⟨L, J, hL2, hLJ, lambda, R, delta,
      hlambda, hR, hdelta, hdelta1, hdetector⟩ :=
    exists_uniform_propagated_zeta_finite_series_detector
  refine ⟨L, J, hL2, hLJ, lambda, R, delta,
    hlambda, hR, hdelta, hdelta1, ?_⟩
  intro eta T heta heta8 hT hglobal
  obtain ⟨S, hSsub, hsep, hcover⟩ :=
    exists_separated_zetaHighZeroOrdinates eta T
      (2 * delta * eta) (by positivity)
  have hdet : ∀ t ∈ S, ∃ j : ℕ,
      L ≤ j ∧ j ≤ J ∧
        ∀ u : ℝ, |u - t| ≤ delta * eta →
          (j - 1).factorial * (1 / 96 : ℝ) *
              (2 * eta)⁻¹ ^ j <
            ‖finiteZeroDetectorPolynomial
              (1 : DirichletCharacter ℂ 1) eta (j - 1)
              (zeroDetectorCutoff R eta) u‖ := by
    intro t ht
    have htOrd := hSsub ht
    obtain ⟨rho, hzero, hrelo, hrehi, hrhoim, ht1, htT⟩ :=
      (mem_zetaHighZeroOrdinates_iff (by linarith) hT t).mp htOrd
    have hlog : eta * Real.log (|t| + 2) ≤ lambda :=
      (mul_le_mul_of_nonneg_left (zeta_log_height_mono ht1 htT) heta.le).trans
        hglobal
    have htAbs : 1 ≤ |t| := by
      calc
        1 ≤ t := ht1
        _ = |t| := (abs_of_nonneg (zero_le_one.trans ht1)).symm
    exact hdetector t eta htAbs
      heta heta8 hlog rho hzero
      (zetaHighZero_dist_detector_center_le hrelo hrehi hrhoim heta)
  let order : ℝ → ℕ := fun t ↦
    if ht : t ∈ S then Classical.choose (hdet t ht) else L
  have horder : ∀ t ∈ S,
      L ≤ order t ∧ order t ≤ J ∧
        ∀ u : ℝ, |u - t| ≤ delta * eta →
          (order t - 1).factorial * (1 / 96 : ℝ) *
              (2 * eta)⁻¹ ^ order t <
            ‖finiteZeroDetectorPolynomial
              (1 : DirichletCharacter ℂ 1) eta (order t - 1)
              (zeroDetectorCutoff R eta) u‖ := by
    intro t ht
    rw [show order t = Classical.choose (hdet t ht) by simp [order, ht]]
    exact Classical.choose_spec (hdet t ht)
  exact ⟨S, order, hSsub, hsep, hcover, horder⟩

private theorem zeta_norm_detector_prefix_le_majorant
    (eta : ℝ) (k M : ℕ) (t : ℝ) :
    ‖∑ n ∈ Finset.Icc 1 (2 ^ M),
        (weightedVonMangoldtMajorant eta k n : ℂ) *
          (1 : DirichletCharacter ℂ 1) n *
          Complex.exp (I * (((-t * Real.log n) : ℝ) : ℂ))‖ ≤
      ∑ n ∈ Finset.Icc 1 (2 ^ M),
        weightedVonMangoldtMajorant eta k n := by
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 (2 ^ M),
        ‖(weightedVonMangoldtMajorant eta k n : ℂ) *
          (1 : DirichletCharacter ℂ 1) n *
          Complex.exp (I * (((-t * Real.log n) : ℝ) : ℂ))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Icc 1 (2 ^ M),
        weightedVonMangoldtMajorant eta k n := by
      apply Finset.sum_le_sum
      intro n hn
      rw [norm_mul, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (by
          unfold weightedVonMangoldtMajorant
          positivity), Complex.norm_exp]
      have him :
          (I * (((-t * Real.log n) : ℝ) : ℂ)).re = 0 := by
        rw [Complex.mul_re]
        simp only [Complex.I_re, Complex.I_im, Complex.ofReal_re,
          Complex.ofReal_im, zero_mul, one_mul, sub_self]
      rw [him, Real.exp_zero, mul_one]
      exact mul_le_of_le_one_right (by
        unfold weightedVonMangoldtMajorant
        positivity)
        ((1 : DirichletCharacter ℂ 1).norm_le_one (n : ZMod 1))

private theorem zeta_full_detector_eq_prefix_add_band
    (eta : ℝ) (k N M : ℕ) (t : ℝ) (hMN : 2 ^ M ≤ N) :
    finiteZeroDetectorPolynomial (1 : DirichletCharacter ℂ 1) eta k N t =
      (∑ n ∈ Finset.Icc 1 (2 ^ M),
        (weightedVonMangoldtMajorant eta k n : ℂ) *
          (1 : DirichletCharacter ℂ 1) n *
          Complex.exp (I * (((-t * Real.log n) : ℝ) : ℂ))) +
      (∑ n ∈ Finset.Ioc (2 ^ M) N,
        (weightedVonMangoldtMajorant eta k n : ℂ) *
          (1 : DirichletCharacter ℂ 1) n *
          Complex.exp (I * (((-t * Real.log n) : ℝ) : ℂ))) := by
  classical
  unfold finiteZeroDetectorPolynomial
  rw [← Finset.sum_union]
  · have hunion : Finset.Icc 1 (2 ^ M) ∪ Finset.Ioc (2 ^ M) N =
        Finset.Icc 1 N := by
      have hpow : 1 ≤ 2 ^ M := Nat.one_le_pow M 2 (by omega)
      ext n
      simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]
      omega
    rw [hunion]
  · exact Finset.disjoint_left.mpr (by
      intro n hn1 hn2
      have h1 := Finset.mem_Icc.mp hn1
      have h2 := Finset.mem_Ioc.mp hn2
      omega)

private theorem zeta_detector_prefix_small
    {theta eta lambda : ℝ} {j M : ℕ}
    (htheta : theta = 1 / (1000 * (Real.log 4 + 4)))
    (heta : 0 < eta) (hetaSmall : eta ≤ theta / 36)
    (hlambdaSmall : lambda ≤ theta / 36)
    (hetaM : eta * (M : ℝ) ≤ 8 * lambda)
    (hj : 2 ≤ j) :
    2 * (Real.log 4 + 4) * (M : ℝ) *
        (((M + 1 : ℕ) : ℝ) * Real.log 2) ^ (j - 1) ≤
      (j - 1).factorial * (1 / 192 : ℝ) *
        (2 * eta)⁻¹ ^ j := by
  let C : ℝ := Real.log 4 + 4
  have hC : 1 ≤ C := by
    dsimp [C]
    have hlog : 0 < Real.log 4 := Real.log_pos (by norm_num)
    linarith
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hthetaPos : 0 < theta := by rw [htheta]; positivity
  have hthetaOne : theta ≤ 1 := by
    rw [htheta]
    have hden : (1 : ℝ) ≤ 1000 * C := by nlinarith
    exact (div_le_one (mul_pos (by norm_num) hCpos)).2 hden
  have hMle : (M : ℝ) ≤ ((M + 1 : ℕ) : ℝ) := by norm_num
  have hlogTwo : Real.log 2 ≤ 1 :=
    (Real.log_le_sub_one_of_pos (by norm_num)).trans_eq (by norm_num)
  have hetaM1 : eta * ((M + 1 : ℕ) : ℝ) ≤ theta / 4 := by
    rw [Nat.cast_add, Nat.cast_one]
    calc
      eta * ((M : ℝ) + 1) = eta * M + eta := by ring
      _ ≤ 8 * lambda + theta / 36 := add_le_add hetaM hetaSmall
      _ ≤ 8 * (theta / 36) + theta / 36 := by gcongr
      _ ≤ theta / 4 := by linarith
  have hbase' : 2 * eta * ((M + 1 : ℕ) : ℝ) ≤ theta / 2 := by
    calc
      2 * eta * ((M + 1 : ℕ) : ℝ) =
          2 * (eta * ((M + 1 : ℕ) : ℝ)) := by ring
      _ ≤ 2 * (theta / 4) := by gcongr
      _ = theta / 2 := by ring
  have hpow :
      (2 * eta * ((M + 1 : ℕ) : ℝ)) ^ j ≤ theta ^ j := by
    apply pow_le_pow_left₀ (by positivity)
    exact hbase'.trans (by linarith [hthetaPos])
  have hthetaPow : theta ^ j ≤ theta ^ 2 :=
    pow_le_pow_of_le_one hthetaPos.le hthetaOne hj
  have hnumeric : 2 * C * theta ^ 2 ≤ 1 / 192 := by
    rw [htheta]
    field_simp
    nlinarith
  have hscaled :
      (2 * C * (M : ℝ) *
          (((M + 1 : ℕ) : ℝ) * Real.log 2) ^ (j - 1)) *
          (2 * eta) ^ j ≤ 1 / 192 := by
    have hMnonneg : (0 : ℝ) ≤ M := by positivity
    have hfac :
        (M : ℝ) * (((M + 1 : ℕ) : ℝ) * Real.log 2) ^ (j - 1) *
            (2 * eta) ^ j ≤
          (2 * eta * ((M + 1 : ℕ) : ℝ)) ^ j := by
      let A : ℝ := ((M + 1 : ℕ) : ℝ) * Real.log 2
      have hA : 0 ≤ A := by dsimp [A]; positivity
      have hAstep : (M : ℝ) * A ^ (j - 1) * (2 * eta) ^ j ≤
          ((M + 1 : ℕ) : ℝ) * A ^ (j - 1) * (2 * eta) ^ j := by
        gcongr
      have hjpos : 0 < j := by omega
      have hAle : A ≤ ((M + 1 : ℕ) : ℝ) := by
        dsimp [A]
        calc
          ((M + 1 : ℕ) : ℝ) * Real.log 2 ≤
              ((M + 1 : ℕ) : ℝ) * 1 := by gcongr
          _ = ((M + 1 : ℕ) : ℝ) := by ring
      calc
        (M : ℝ) * A ^ (j - 1) * (2 * eta) ^ j ≤
            ((M + 1 : ℕ) : ℝ) * A ^ (j - 1) * (2 * eta) ^ j := hAstep
        _ ≤ ((M + 1 : ℕ) : ℝ) ^ j * (2 * eta) ^ j := by
          apply mul_le_mul_of_nonneg_right
          · calc
              ((M + 1 : ℕ) : ℝ) * A ^ (j - 1) ≤
                  ((M + 1 : ℕ) : ℝ) *
                    ((M + 1 : ℕ) : ℝ) ^ (j - 1) :=
                mul_le_mul_of_nonneg_left
                  (pow_le_pow_left₀ hA hAle (j - 1)) (by positivity)
              _ = ((M + 1 : ℕ) : ℝ) ^ j := by
                calc
                  ((M + 1 : ℕ) : ℝ) *
                      ((M + 1 : ℕ) : ℝ) ^ (j - 1) =
                      ((M + 1 : ℕ) : ℝ) ^ ((j - 1) + 1) := by
                    rw [pow_succ']
                  _ = ((M + 1 : ℕ) : ℝ) ^ j := by congr 1; omega
          · positivity
        _ = (2 * eta * ((M + 1 : ℕ) : ℝ)) ^ j := by
          rw [mul_pow]
          ring
    calc
      (2 * C * (M : ℝ) *
          (((M + 1 : ℕ) : ℝ) * Real.log 2) ^ (j - 1)) *
          (2 * eta) ^ j ≤
          2 * C * (2 * eta * ((M + 1 : ℕ) : ℝ)) ^ j := by
        nlinarith [hfac]
      _ ≤ 2 * C * theta ^ j := by gcongr
      _ ≤ 2 * C * theta ^ 2 := by gcongr
      _ ≤ 1 / 192 := hnumeric
  have hfactorial : (1 : ℝ) ≤ (j - 1).factorial := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hpowPos : 0 < (2 * eta) ^ j := by positivity
  rw [inv_pow]
  apply (le_div_iff₀ hpowPos).2
  calc
    (2 * C * (M : ℝ) *
        (((M + 1 : ℕ) : ℝ) * Real.log 2) ^ (j - 1)) *
        (2 * eta) ^ j ≤ 1 / 192 := hscaled
    _ ≤ (j - 1).factorial * (1 / 192 : ℝ) := by
      calc
        (1 / 192 : ℝ) = 1 * (1 / 192 : ℝ) := by ring
        _ ≤ (j - 1).factorial * (1 / 192 : ℝ) :=
          mul_le_mul_of_nonneg_right hfactorial (by norm_num)

/-- The zeta detector restricted beyond a fixed power of the ambient
height, retaining a uniform lower bound. -/
theorem exists_uniform_zeta_band_zero_detector :
    ∃ L J : ℕ, 2 ≤ L ∧ L ≤ J ∧
      ∃ lambda R delta eta₀ : ℝ,
        0 < lambda ∧ 0 < R ∧ 0 < delta ∧ delta ≤ 1 ∧
        0 < eta₀ ∧ eta₀ ≤ 1 / 8 ∧
        ∀ (T eta : ℝ), 1 ≤ T → 0 < eta → eta ≤ eta₀ →
          eta * Real.log (T + 2) ≤ lambda →
            ∃ S : Finset ℝ, ∃ order : ℝ → ℕ,
              S ⊆ zetaHighZeroOrdinates eta T ∧
              (∀ x ∈ S, ∀ y ∈ S, x ≠ y →
                2 * delta * eta < dist x y) ∧
              (∀ x ∈ zetaHighZeroOrdinates eta T,
                ∃ y ∈ S, dist x y ≤ 2 * delta * eta) ∧
              zeroDetectorLowerCutoff (T + 2) ≤
                zeroDetectorCutoff R eta ∧
              ∀ t ∈ S,
                L ≤ order t ∧ order t ≤ J ∧
                  ∀ u : ℝ, |u - t| ≤ delta * eta →
                    (order t - 1).factorial * (1 / 192 : ℝ) *
                        (2 * eta)⁻¹ ^ order t <
                      ‖bandZeroDetectorPolynomial
                        (1 : DirichletCharacter ℂ 1) eta (order t - 1)
                        (zeroDetectorCutoff R eta) (T + 2) u‖ := by
  obtain ⟨L, J, hL2, hLJ, lambdaD, R, delta,
      hlambdaD, hR, hdelta, hdelta1, hselection⟩ :=
    exists_uniform_detected_zeta_zero_selection
  let C : ℝ := Real.log 4 + 4
  let theta : ℝ := 1 / (1000 * C)
  let eta₀ : ℝ := min (1 / 8) (theta / 36)
  let lambda : ℝ := min lambdaD (min (theta / 36) (R / 16))
  have hC : 0 < C := by dsimp [C]; positivity
  have htheta : 0 < theta := by dsimp [theta]; positivity
  have heta₀ : 0 < eta₀ := by
    dsimp [eta₀]
    exact lt_min (by norm_num) (by positivity)
  have heta₀8 : eta₀ ≤ 1 / 8 := min_le_left _ _
  have hlambda : 0 < lambda := by
    dsimp [lambda]
    exact lt_min hlambdaD (lt_min (by positivity) (by positivity))
  have hlambdaD' : lambda ≤ lambdaD := min_le_left _ _
  have hlambdaTheta : lambda ≤ theta / 36 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hlambdaR : lambda ≤ R / 16 :=
    (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨L, J, hL2, hLJ, lambda, R, delta, eta₀,
    hlambda, hR, hdelta, hdelta1, heta₀, heta₀8, ?_⟩
  intro T eta hT heta hetaSmall hglobal
  have hselectionGlobal : eta * Real.log (T + 2) ≤ lambdaD :=
    hglobal.trans hlambdaD'
  obtain ⟨S, order, hSsub, hsep, hcover, horder⟩ :=
    hselection eta T heta (hetaSmall.trans heta₀8) hT hselectionGlobal
  let B : ℝ := T + 2
  let M : ℕ := zeroDetectorLowerLog B
  let N : ℕ := zeroDetectorCutoff R eta
  have hfloor : (M : ℝ) ≤ 8 * Real.log B := by
    dsimp [M, zeroDetectorLowerLog]
    exact Nat.floor_le (mul_nonneg (by norm_num)
      (Real.log_nonneg (by dsimp [B]; linarith)))
  have hetaM : eta * (M : ℝ) ≤ 8 * lambda := by
    calc
      eta * (M : ℝ) ≤ eta * (8 * Real.log B) :=
        mul_le_mul_of_nonneg_left hfloor heta.le
      _ = 8 * (eta * Real.log B) := by ring
      _ ≤ 8 * lambda := by
        exact mul_le_mul_of_nonneg_left (by simpa only [B] using hglobal)
          (by norm_num)
  have hMNreal : ((2 ^ M : ℕ) : ℝ) ≤ Real.exp (R / eta) := by
    calc
      ((2 ^ M : ℕ) : ℝ) = (2 : ℝ) ^ M := by norm_cast
      _ = (2 : ℝ) ^ (M : ℝ) := (Real.rpow_natCast 2 M).symm
      _ = Real.exp (Real.log 2 * (M : ℝ)) :=
        Real.rpow_def_of_pos (by norm_num) _
      _ ≤ Real.exp (R / eta) := by
        apply Real.exp_le_exp.mpr
        apply (le_div_iff₀ heta).2
        calc
          (Real.log 2 * (M : ℝ)) * eta ≤ 1 * (M : ℝ) * eta := by
            gcongr
            exact (Real.log_le_sub_one_of_pos (by norm_num)).trans_eq (by norm_num)
          _ = eta * M := by ring
          _ ≤ 8 * lambda := hetaM
          _ ≤ R := by
            calc
              8 * lambda ≤ 8 * (R / 16) := by gcongr
              _ ≤ R := by linarith
  have hMN : 2 ^ M ≤ N := by
    exact_mod_cast hMNreal.trans (exp_div_le_zeroDetectorCutoff R eta)
  refine ⟨S, order, hSsub, hsep, hcover, ?_, ?_⟩
  · change 2 ^ M ≤ N
    exact hMN
  · intro t ht
    obtain ⟨hLt, htJ, htPoly⟩ := horder t ht
    refine ⟨hLt, htJ, ?_⟩
    intro u hu
    have hfull := htPoly u hu
    let lowPart : ℂ :=
      ∑ n ∈ Finset.Icc 1 (2 ^ M),
        (weightedVonMangoldtMajorant eta (order t - 1) n : ℂ) *
          (1 : DirichletCharacter ℂ 1) n *
          Complex.exp (I * (((-u * Real.log n) : ℝ) : ℂ))
    have hprefix : ‖lowPart‖ ≤
        (order t - 1).factorial * (1 / 192 : ℝ) *
          (2 * eta)⁻¹ ^ order t := by
      calc
        ‖lowPart‖ ≤ ∑ n ∈ Finset.Icc 1 (2 ^ M),
            weightedVonMangoldtMajorant eta (order t - 1) n :=
          zeta_norm_detector_prefix_le_majorant eta (order t - 1) M u
        _ ≤ 2 * (Real.log 4 + 4) * (M : ℝ) *
            (((M + 1 : ℕ) : ℝ) * Real.log 2) ^ (order t - 1) :=
          sum_weightedVonMangoldtMajorant_Icc_two_pow_le
            eta heta (order t - 1) M
        _ ≤ _ := zeta_detector_prefix_small
          (theta := theta) (lambda := lambda)
          (by rfl) heta (hetaSmall.trans (min_le_right _ _))
          hlambdaTheta hetaM (hL2.trans hLt)
    have hdecomp := zeta_full_detector_eq_prefix_add_band
      eta (order t - 1) N M u hMN
    have htriangle :
        ‖finiteZeroDetectorPolynomial
            (1 : DirichletCharacter ℂ 1) eta (order t - 1) N u‖ ≤
          ‖lowPart‖ +
            ‖bandZeroDetectorPolynomial
              (1 : DirichletCharacter ℂ 1) eta (order t - 1) N B u‖ := by
      rw [hdecomp]
      simpa only [lowPart, bandZeroDetectorPolynomial,
        zeroDetectorLowerCutoff, M] using
          norm_add_le lowPart
            (∑ n ∈ Finset.Ioc (2 ^ M) N,
              (weightedVonMangoldtMajorant eta (order t - 1) n : ℂ) *
                (1 : DirichletCharacter ℂ 1) n *
                Complex.exp (I * (((-u * Real.log n) : ℝ) : ℂ)))
    change (order t - 1).factorial * (1 / 192 : ℝ) *
        (2 * eta)⁻¹ ^ order t < _
    dsimp only [N, B] at htriangle
    dsimp [lowPart] at hprefix htriangle
    have hscale : 0 ≤ ((order t - 1).factorial : ℝ) *
        (2 * eta)⁻¹ ^ order t := by positivity
    nlinarith

private theorem zeta_finset_sum_finsupp_apply_le_sum
    {alpha : Type*} (F : alpha →₀ ℕ) (s : Finset alpha) :
    ∑ x ∈ s, (F x : ℝ) ≤ F.sum (fun _ m ↦ (m : ℝ)) := by
  classical
  have heq :
      F.sum (fun _ m ↦ (m : ℝ)) =
        ∑ x ∈ F.support ∪ s, (F x : ℝ) := by
    exact Finsupp.sum_of_support_subset F Finset.subset_union_left
      (fun _ m ↦ (m : ℝ)) (by simp)
  rw [heq]
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_right
    (fun _ _ _ ↦ by positivity)

theorem zetaHighZeroRectangleMass_le_sum_smallDiskMass
    {eta T delta : ℝ} (heta : 0 < eta) (heta1 : eta ≤ 1)
    (hT : 1 ≤ T) (hdelta0 : 0 ≤ delta) (hdelta1 : delta ≤ 1)
    (S : Finset ℝ)
    (hcover : ∀ x ∈ zetaHighZeroOrdinates eta T,
      ∃ y ∈ S, dist x y ≤ 2 * delta * eta) :
    (zetaHighZeroRectangleMass eta T : ℝ) ≤
      ∑ y ∈ S,
        (zetaSmallDiskZeroFinsupp y eta).sum
          (fun _ m ↦ (m : ℝ)) := by
  classical
  let Z := zetaHighZeroRectangle eta T
  let F : ℝ → ℂ →₀ ℕ := fun y ↦ zetaSmallDiskZeroFinsupp y eta
  have hpoint (rho : ℂ) (hrho : rho ∈ Z) :
      (analyticOrderNatAt riemannZeta₁ rho : ℝ) ≤
        ∑ y ∈ S, (F y rho : ℝ) := by
    have hrhoData :=
      (mem_zetaHighZeroRectangle_iff heta1 hT rho).mp hrho
    have hrhoOrd : rho.im ∈ zetaHighZeroOrdinates eta T := by
      rw [zetaHighZeroOrdinates, Finset.mem_image]
      exact ⟨rho, hrho, rfl⟩
    obtain ⟨y, hyS, hy⟩ := hcover rho.im hrhoOrd
    have hdisk := highZero_mem_smallDisk_of_ordinate_near
      hrhoData.2.1 hrhoData.2.2.1 heta hdelta0 hdelta1 hy
    have hFy : F y rho = analyticOrderNatAt riemannZeta₁ rho := by
      rw [show F y rho = zetaSmallDiskZeroMultiplicity y eta rho by
        exact zetaSmallDiskZeroFinsupp_apply y eta rho]
      unfold zetaSmallDiskZeroMultiplicity
      rw [if_pos hdisk]
    rw [← hFy]
    exact_mod_cast Finset.single_le_sum
      (fun z _ ↦ Nat.zero_le (F z rho)) hyS
  calc
    (zetaHighZeroRectangleMass eta T : ℝ) =
        ∑ rho ∈ Z, (analyticOrderNatAt riemannZeta₁ rho : ℝ) := by
      simp only [zetaHighZeroRectangleMass, Z, Nat.cast_sum]
    _ ≤ ∑ rho ∈ Z, ∑ y ∈ S, (F y rho : ℝ) :=
      Finset.sum_le_sum fun rho hrho ↦ hpoint rho hrho
    _ = ∑ y ∈ S, ∑ rho ∈ Z, (F y rho : ℝ) := by
      rw [Finset.sum_comm]
    _ ≤ ∑ y ∈ S, (F y).sum (fun _ m ↦ (m : ℝ)) := by
      apply Finset.sum_le_sum
      intro y hy
      exact zeta_finset_sum_finsupp_apply_le_sum (F y) Z
    _ = _ := by rfl

/-- Local zeta divisor mass converts a covering ordinate family into a
bound for the exact multiplicity of the whole high-zero rectangle. -/
theorem exists_zetaHighZeroRectangleMass_cover_bound :
    ∃ A : ℕ, 37 ≤ A ∧
      ∀ (eta T lambda delta : ℝ),
        0 < eta → eta ≤ 1 → 1 ≤ T →
        0 ≤ delta → delta ≤ 1 →
        eta * Real.log (T + 2) ≤ lambda →
        ∀ S : Finset ℝ,
          S ⊆ zetaHighZeroOrdinates eta T →
          (∀ x ∈ zetaHighZeroOrdinates eta T,
            ∃ y ∈ S, dist x y ≤ 2 * delta * eta) →
          (zetaHighZeroRectangleMass eta T : ℝ) ≤
            (S.card : ℝ) *
              (48 * (Real.log 4 + 4) +
                (256 * (A : ℝ) / 3) * lambda) := by
  obtain ⟨A, hA, hlocal⟩ := exists_zetaSmallDiskZeroMultiplicity_bound
  refine ⟨A, hA, ?_⟩
  intro eta T lambda delta heta heta1 hT hdelta0 hdelta1 hglobal
    S hSsub hcover
  have hmass := zetaHighZeroRectangleMass_le_sum_smallDiskMass
    heta heta1 hT hdelta0 hdelta1 S hcover
  let K : ℝ := 48 * (Real.log 4 + 4) +
    (256 * (A : ℝ) / 3) * lambda
  have hterm : ∀ y ∈ S,
      (zetaSmallDiskZeroFinsupp y eta).sum (fun _ m ↦ (m : ℝ)) ≤ K := by
    intro y hy
    have hyOrd := hSsub hy
    obtain ⟨rho, hzero, hrelo, hrehi, hrhoim, hy1, hyT⟩ :=
      (mem_zetaHighZeroOrdinates_iff heta1 hT y).mp hyOrd
    have hlog : eta * Real.log (|y| + 2) ≤ lambda :=
      (mul_le_mul_of_nonneg_left (zeta_log_height_mono hy1 hyT) heta.le).trans
        hglobal
    have hb := hlocal y eta heta heta1
    dsimp [K]
    calc
      (zetaSmallDiskZeroFinsupp y eta).sum (fun _ m ↦ (m : ℝ)) ≤
          48 * (Real.log 4 + 4) +
            (256 * (A : ℝ) / 3) * eta * Real.log (|y| + 2) := hb
      _ ≤ 48 * (Real.log 4 + 4) +
          (256 * (A : ℝ) / 3) * lambda := by
        have hcoef : 0 ≤ (256 * (A : ℝ) / 3) := by positivity
        nlinarith
  calc
    (zetaHighZeroRectangleMass eta T : ℝ) ≤
        ∑ y ∈ S,
          (zetaSmallDiskZeroFinsupp y eta).sum
            (fun _ m ↦ (m : ℝ)) := hmass
    _ ≤ ∑ y ∈ S, K := Finset.sum_le_sum fun y hy ↦ hterm y hy
    _ = (S.card : ℝ) * K := by simp

noncomputable def zetaPrimitiveCharacter : primitiveCharacters 1 :=
  ⟨(1 : DirichletCharacter ℂ 1),
    DirichletCharacter.isPrimitive_one_level_one⟩

noncomputable local instance zetaPrimitiveCharactersOneUnique :
    Unique (primitiveCharacters 1) where
  default := zetaPrimitiveCharacter
  uniq psi := by
    apply Subtype.ext
    exact DirichletCharacter.level_one psi.1

private theorem zeta_sum_orderFiber_card_eq
    (S : Finset ℝ) (order : ℝ → ℕ) {L J : ℕ}
    (horder : ∀ t ∈ S, L ≤ order t ∧ order t ≤ J) :
    ∑ j ∈ Finset.Icc L J, (S.filter fun t ↦ order t = j).card = S.card := by
  classical
  calc
    ∑ j ∈ Finset.Icc L J, (S.filter fun t ↦ order t = j).card =
        ∑ j ∈ Finset.Icc L J, ∑ t ∈ S, if order t = j then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      simp
    _ = ∑ t ∈ S, ∑ j ∈ Finset.Icc L J,
          if order t = j then 1 else 0 := by rw [Finset.sum_comm]
    _ = ∑ _t ∈ S, 1 := by
      apply Finset.sum_congr rfl
      intro t ht
      have htRange : order t ∈ Finset.Icc L J :=
        Finset.mem_Icc.mpr (horder t ht)
      simp [htRange]
    _ = S.card := by simp

/-- The short disjoint intervals attached to a separated family of zeta
zero ordinates are controlled by the corresponding conductor-one detector
mean squares. -/
theorem zeta_selectedOrdinates_card_mul_le_detector_integrals
    (Y N T L J : ℕ) (eta delta : ℝ)
    (heta : 0 < eta) (heta1 : eta ≤ 1)
    (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (S : Finset ℝ) (order : ℝ → ℕ)
    (hS : ∀ t ∈ S, 0 ≤ t ∧ t ≤ T)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y →
      2 * delta * eta < dist x y)
    (horder : ∀ t ∈ S, L ≤ order t ∧ order t ≤ J)
    (hlower : ∀ t ∈ S, ∀ u : ℝ, |u - t| ≤ delta * eta →
      (1 / 192 : ℝ) ≤
        ‖∑ n ∈ Finset.Ioc Y N,
          (weightedVonMangoldtMajorant eta (order t - 1) n : ℂ) *
            (1 : DirichletCharacter ℂ 1) n *
            Complex.exp (I * (((-u * Real.log n) : ℝ) : ℂ))‖) :
    (S.card : ℝ) * (delta * eta) * (1 / 192 : ℝ) ^ 2 ≤
      ∑ j ∈ Finset.Icc L J,
        ∫ u in (0 : ℝ)..((T + 1 : ℕ) : ℝ),
          ‖∑ n ∈ Finset.Ioc Y N,
            (weightedVonMangoldtMajorant eta (j - 1) n : ℂ) *
              (1 : DirichletCharacter ℂ 1) n *
              Complex.exp (I * (((-u * Real.log n) : ℝ) : ℂ))‖ ^ 2 := by
  classical
  let r : ℝ := delta * eta
  let B : ℝ := (1 / 192 : ℝ) ^ 2
  let F : ℕ → Finset ℝ := fun j ↦ S.filter fun t ↦ order t = j
  let f : ℕ → ℝ → ℝ := fun j u ↦
    ‖∑ n ∈ Finset.Ioc Y N,
      (weightedVonMangoldtMajorant eta (j - 1) n : ℂ) *
        (1 : DirichletCharacter ℂ 1) n *
        Complex.exp (I * (((-u * Real.log n) : ℝ) : ℂ))‖ ^ 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hr1 : r ≤ 1 := by dsimp [r]; nlinarith
  have hfiber (j : ℕ) (hj : j ∈ Finset.Icc L J) :
      ((F j).card : ℝ) * r * B ≤
        ∫ u in (0 : ℝ)..((T + 1 : ℕ) : ℝ), f j u := by
    have hshort := card_mul_interval_lower_le_integral
      (F j) hr (show (0 : ℝ) ≤ T by positivity)
      (fun t ht ↦ hS t (Finset.mem_filter.mp ht).1)
      (fun x hx y hy hxy ↦ by
        simpa only [r, mul_assoc] using
          hsep x (Finset.mem_filter.mp hx).1 y
            (Finset.mem_filter.mp hy).1 hxy)
      (f j)
      (by dsimp [f]; fun_prop)
      (fun u ↦ by dsimp [f]; positivity)
      (fun t ht u hu ↦ by
        have htS := (Finset.mem_filter.mp ht).1
        have htOrder := (Finset.mem_filter.mp ht).2
        have huAbs : |u - t| ≤ r := by
          rw [abs_of_nonneg (sub_nonneg.mpr hu.1.le)]
          linarith [hu.2]
        have hl := hlower t htS u (by simpa only [r] using huAbs)
        dsimp [f, B]
        rw [← htOrder]
        exact (sq_le_sq₀ (by norm_num)
          (norm_nonneg (∑ n ∈ Finset.Ioc Y N,
            (weightedVonMangoldtMajorant eta (order t - 1) n : ℂ) *
              (1 : DirichletCharacter ℂ 1) n *
              Complex.exp (I * (((-u * Real.log n) : ℝ) : ℂ))))).2 hl)
    have hfi : IntervalIntegrable (f j) MeasureTheory.volume
        0 ((T + 1 : ℕ) : ℝ) := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        ((show Continuous (f j) by dsimp [f]; fun_prop).intervalIntegrable
          0 ((T : ℝ) + 1))
    exact hshort.trans (intervalIntegral.integral_mono_interval
      le_rfl (by positivity) (by
        dsimp [r]
        push_cast
        linarith) (Filter.Eventually.of_forall fun u ↦ by
          dsimp [f]
          positivity)
      hfi)
  have hsum := Finset.sum_le_sum fun j hj ↦ hfiber j hj
  have hcardEq := zeta_sum_orderFiber_card_eq S order horder
  calc
    (S.card : ℝ) * (delta * eta) * (1 / 192 : ℝ) ^ 2 =
        ∑ j ∈ Finset.Icc L J, ((F j).card : ℝ) * r * B := by
      rw [← hcardEq]
      push_cast
      simp_rw [Finset.sum_mul]
      dsimp [F, r, B]
    _ ≤ ∑ j ∈ Finset.Icc L J,
        ∫ u in (0 : ℝ)..((T + 1 : ℕ) : ℝ), f j u := hsum
    _ = _ := by rfl

theorem intervalIntegral_zetaDetector_eq_primitiveNegativeDirichletMass
    (Y N T k : ℕ) (eta : ℝ) :
    (∫ u in (0 : ℝ)..(T : ℝ),
        ‖∑ n ∈ Finset.Ioc Y N,
          (weightedVonMangoldtMajorant eta k n : ℂ) *
            (1 : DirichletCharacter ℂ 1) n *
            Complex.exp (I * (((-u * Real.log n) : ℝ) : ℂ))‖ ^ 2) =
      ∫ u in (0 : ℝ)..(T : ℝ),
        primitiveNegativeDirichletMass 1 (Finset.Ioc Y N)
          (fun n ↦ (weightedVonMangoldtMajorant eta k n : ℂ)) u := by
  have hdefault : (default : primitiveCharacters 1).1 =
      (1 : DirichletCharacter ℂ 1) := DirichletCharacter.level_one _
  rw [intervalIntegral_primitiveNegativeDirichletMass_eq]
  norm_num [zetaPrimitiveCharacter, hdefault]

end

end Erdos381
