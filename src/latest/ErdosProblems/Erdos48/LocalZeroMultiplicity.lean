import ErdosProblems.Erdos48.LogDerivativeSeries
import BoundedGaps.BombieriVinogradov.Analytic.PrimitiveLFunctionSelectedSubdivisor
import BoundedGaps.BombieriVinogradov.Analytic.ChebyshevPoleOrder

open Complex Metric Set

namespace Erdos48

open BoundedGaps.Maynard

noncomputable section

noncomputable def smallDiskZeroMultiplicity
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (t eta : ℝ) : ℂ → ℕ := fun rho =>
  if dist rho (((1 + eta : ℝ) : ℂ) + t * I) ≤ 4 * eta then
    analyticOrderNatAt (DirichletCharacter.LFunction chi) rho
  else 0

theorem smallDiskZeroMultiplicity_hasFiniteSupport
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi.IsPrimitive)
    (t eta : ℝ) :
    Function.HasFiniteSupport (smallDiskZeroMultiplicity chi t eta) := by
  let c : ℂ := ((1 + eta : ℝ) : ℂ) + t * I
  let D := MeromorphicOn.divisor (DirichletCharacter.LFunction chi)
    (closedBall c (4 * eta))
  have hD : D.support.Finite :=
    divisor_LFunction_closedBall_support_finite
      (character_ne_one_of_isPrimitive hq chi hchi) c (4 * eta)
  apply hD.subset
  intro rho hrho
  rw [Function.mem_support] at hrho ⊢
  dsimp [smallDiskZeroMultiplicity] at hrho
  split at hrho
  next hdist =>
    have hrhoBall : rho ∈ closedBall c (4 * eta) := by
      simpa [c, mem_closedBall] using hdist
    rw [show D rho =
        (analyticOrderNatAt (DirichletCharacter.LFunction chi) rho : ℤ) by
      exact divisor_LFunction_apply_eq_analyticOrderNatAt
        (character_ne_one_of_isPrimitive hq chi hchi) hrhoBall]
    exact_mod_cast hrho
  next hdist => exact False.elim (hrho rfl)

noncomputable def smallDiskZeroFinsupp
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi.IsPrimitive)
    (t eta : ℝ) : ℂ →₀ ℕ :=
  Finsupp.ofSupportFinite (smallDiskZeroMultiplicity chi t eta)
    (smallDiskZeroMultiplicity_hasFiniteSupport hq chi hchi t eta)

theorem smallDiskZeroFinsupp_apply
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi.IsPrimitive)
    (t eta : ℝ) (rho : ℂ) :
    smallDiskZeroFinsupp hq chi hchi t eta rho =
      smallDiskZeroMultiplicity chi t eta rho := rfl

theorem smallDiskZeroFinsupp_le_radiusSix
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi.IsPrimitive)
    (t eta : ℝ) (heta1 : eta ≤ 1) (rho : ℂ) :
    smallDiskZeroFinsupp hq chi hchi t eta rho ≤
      if dist rho ((2 : ℂ) + t * I) ≤ 6 then
        analyticOrderNatAt (DirichletCharacter.LFunction chi) rho
      else 0 := by
  rw [smallDiskZeroFinsupp_apply]
  unfold smallDiskZeroMultiplicity
  split
  next hsmall =>
    have hcenters :
        dist (((1 + eta : ℝ) : ℂ) + t * I) ((2 : ℂ) + t * I) = 1 - eta := by
      rw [Complex.dist_eq]
      have heq : (((1 + eta : ℝ) : ℂ) + t * I) - ((2 : ℂ) + t * I) =
          ((eta - 1 : ℝ) : ℂ) := by push_cast; ring
      rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
      ring
    have hradius : dist rho ((2 : ℂ) + t * I) ≤ 6 := by
      calc
        dist rho ((2 : ℂ) + t * I) ≤
            dist rho (((1 + eta : ℝ) : ℂ) + t * I) +
              dist (((1 + eta : ℝ) : ℂ) + t * I) ((2 : ℂ) + t * I) :=
          dist_triangle _ _ _
        _ ≤ 4 * eta + (1 - eta) := add_le_add hsmall hcenters.le
        _ ≤ 6 := by linarith
    simp [hradius]
  next hsmall => simp

private theorem inv_sub_re_ge_inv_sixteen_mul
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi.IsPrimitive)
    (t eta : ℝ) (heta0 : 0 < eta) {rho : ℂ}
    (hsmall : dist rho (((1 + eta : ℝ) : ℂ) + t * I) ≤ 4 * eta)
    (hmul : analyticOrderNatAt (DirichletCharacter.LFunction chi) rho ≠ 0) :
    (16 * eta)⁻¹ ≤
      (((((1 + eta : ℝ) : ℂ) + t * I) - rho)⁻¹).re := by
  let s : ℂ := ((1 + eta : ℝ) : ℂ) + t * I
  have hzero : DirichletCharacter.LFunction chi rho = 0 :=
    apply_eq_zero_of_analyticOrderNatAt_ne_zero hmul
  have hrho : rho.re < 1 :=
    LFunction_zero_re_lt_one_of_isPrimitive hq chi hchi hzero
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
  change (1 : ℝ) / (16 * eta) ≤ (s - rho).re / Complex.normSq (s - rho)
  rw [div_le_div_iff₀ heta16 hdenpos]
  nlinarith

theorem exists_smallDiskZeroMultiplicity_bound :
    ∃ A : ℕ, 37 ≤ A ∧
      ∀ (q : ℕ) [NeZero q], ∀ (hq : 1 < q),
        ∀ (chi : DirichletCharacter ℂ q), ∀ (hchi : chi.IsPrimitive),
          ∀ (t eta : ℝ), 0 < eta → eta ≤ 1 →
            (smallDiskZeroFinsupp hq chi hchi t eta).sum
                (fun _ m => (m : ℝ)) ≤
              16 * (Real.log 4 + 4) * (1 + eta) +
                (256 * (A : ℝ) / 3) * eta *
                  Real.log ((q : ℝ) * (|t| + 2)) := by
  obtain ⟨A, hA, hselected⟩ :=
    exists_nat_selected_radiusSix_subdivisor_sum_sub_le_re_logDeriv_LFunction
  refine ⟨A, hA, ?_⟩
  intro q _ hq chi hchi t eta heta0 heta1
  let s : ℂ := ((1 + eta : ℝ) : ℂ) + t * I
  let Z : ℂ →₀ ℕ := smallDiskZeroFinsupp hq chi hchi t eta
  have hsre : s.re = 1 + eta := by simp [s]
  have hs1 : 1 < s.re := by rw [hsre]; linarith
  have hLs : DirichletCharacter.LFunction chi s ≠ 0 :=
    chi.LFunction_ne_zero_of_one_le_re
      (.inl (character_ne_one_of_isPrimitive hq chi hchi)) hs1.le
  have hsel := hselected q hq chi hchi t (1 + eta) Z
    (by linarith) (by linarith)
    (by simpa [s] using hLs)
    (smallDiskZeroFinsupp_le_radiusSix hq chi hchi t eta heta1)
  have hlogBound : ‖-logDeriv (DirichletCharacter.LFunction chi) s‖ ≤
      (Real.log 4 + 4) * (1 + eta) / eta := by
    simpa [hsre] using
      norm_neg_logDeriv_LFunction_le_chebyshev_div_sub_one chi hs1
  have hreLog :
      (logDeriv (DirichletCharacter.LFunction chi) s).re ≤
        (Real.log 4 + 4) * (1 + eta) / eta := by
    calc
      (logDeriv (DirichletCharacter.LFunction chi) s).re ≤
          ‖logDeriv (DirichletCharacter.LFunction chi) s‖ := Complex.re_le_norm _
      _ = ‖-logDeriv (DirichletCharacter.LFunction chi) s‖ := by rw [norm_neg]
      _ ≤ (Real.log 4 + 4) * (1 + eta) / eta := hlogBound
  have hterm (rho : ℂ) (hrho : rho ∈ Z.support) :
      (16 * eta)⁻¹ ≤ ((s - rho)⁻¹).re := by
    have hZne : Z rho ≠ 0 := Finsupp.mem_support_iff.mp hrho
    have hm : smallDiskZeroMultiplicity chi t eta rho ≠ 0 := by
      simpa [Z, smallDiskZeroFinsupp_apply] using hZne
    unfold smallDiskZeroMultiplicity at hm
    split at hm
    next hsmall =>
      simpa [s] using inv_sub_re_ge_inv_sixteen_mul hq chi hchi t eta heta0 hsmall hm
    next hsmall => exact False.elim (hm rfl)
  have hsumLower :
      (16 * eta)⁻¹ * Z.sum (fun _ m => (m : ℝ)) ≤
        Z.sum (fun rho m => (m : ℝ) * ((s - rho)⁻¹).re) := by
    rw [Finsupp.mul_sum]
    apply Finsupp.sum_le_sum
    intro rho hrho
    simpa [mul_comm] using
      mul_le_mul_of_nonneg_left (hterm rho hrho) (Nat.cast_nonneg (Z rho))
  have hsel' :
      Z.sum (fun rho m => (m : ℝ) * ((s - rho)⁻¹).re) -
          16 * ((A : ℝ) * Real.log ((q : ℝ) * (|t| + 2))) / 3 ≤
        (logDeriv (DirichletCharacter.LFunction chi) s).re := by
    simpa [s, Z] using hsel
  have hraw :
      (16 * eta)⁻¹ * Z.sum (fun _ m => (m : ℝ)) ≤
        (Real.log 4 + 4) * (1 + eta) / eta +
          16 * ((A : ℝ) * Real.log ((q : ℝ) * (|t| + 2))) / 3 := by
    linarith
  have heta16 : 0 < 16 * eta := by positivity
  have hmul := mul_le_mul_of_nonneg_left hraw heta16.le
  have hleft :
      (16 * eta) * ((16 * eta)⁻¹ * Z.sum (fun _ m => (m : ℝ))) =
        Z.sum (fun _ m => (m : ℝ)) := by
    rw [← mul_assoc, mul_inv_cancel₀ heta16.ne', one_mul]
  rw [hleft] at hmul
  simpa [Z] using (show
    Z.sum (fun _ m => (m : ℝ)) ≤
      16 * (Real.log 4 + 4) * (1 + eta) +
        (256 * (A : ℝ) / 3) * eta *
          Real.log ((q : ℝ) * (|t| + 2)) by
    calc
      Z.sum (fun _ m => (m : ℝ)) ≤
          (16 * eta) * ((Real.log 4 + 4) * (1 + eta) / eta +
            16 * ((A : ℝ) * Real.log ((q : ℝ) * (|t| + 2))) / 3) := hmul
      _ = _ := by field_simp; ring)

end

end Erdos48
