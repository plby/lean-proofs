import BoundedGaps.BombieriVinogradov.Analytic.PrimitiveLFunctionRadiusTwelve
import BoundedGaps.BombieriVinogradov.Analytic.RiemannZetaRadiusTwelve
import BoundedGaps.BombieriVinogradov.Analytic.InducingEulerProduct

/-!
# Fixed-disk growth for all Dirichlet characters

The four-character positivity argument for zero repulsion includes induced
characters.  Their omitted Euler factors have polynomial growth on the same
radius-twelve disks as the primitive L-functions.
-/

namespace Linnik

open Complex Metric BoundedGaps.Maynard
open scoped BigOperators Classical

theorem norm_primeEulerProduct_le_pow
    {q d : ℕ} [NeZero q] (psi : DirichletCharacter ℂ d)
    {s : ℂ} (hs : -(10 : ℝ) ≤ s.re) :
    ‖∏ p ∈ q.primeFactors, (1 - psi p * (p : ℂ) ^ (-s))‖ ≤ (q : ℝ) ^ 11 := by
  calc
    ‖∏ p ∈ q.primeFactors, (1 - psi p * (p : ℂ) ^ (-s))‖ ≤
        ∏ p ∈ q.primeFactors, ‖1 - psi p * (p : ℂ) ^ (-s)‖ :=
      Finset.norm_prod_le _ _
    _ ≤ ∏ p ∈ q.primeFactors, (p : ℝ) ^ 11 := by
      apply Finset.prod_le_prod
      · intro p _
        positivity
      · intro p hp
        have hpPrime := Nat.prime_of_mem_primeFactors hp
        have hp₂ : (2 : ℝ) ≤ p := by exact_mod_cast hpPrime.two_le
        have hp₁ : (1 : ℝ) ≤ p := by linarith
        have hpow : (p : ℝ) ^ (-s.re) ≤ (p : ℝ) ^ 10 := by
          calc
            (p : ℝ) ^ (-s.re) ≤ (p : ℝ) ^ (10 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le hp₁ (by linarith)
            _ = (p : ℝ) ^ 10 := Real.rpow_natCast _ _
        have hten : (1 : ℝ) ≤ (p : ℝ) ^ 10 := one_le_pow₀ hp₁
        have hlarge : 1 + (p : ℝ) ^ 10 ≤ (p : ℝ) ^ 11 := by
          rw [pow_succ (p : ℝ) 10]
          nlinarith
        calc
          ‖1 - psi p * (p : ℂ) ^ (-s)‖ ≤
              1 + ‖psi p * (p : ℂ) ^ (-s)‖ := by
            simpa using norm_sub_le (1 : ℂ) (psi p * (p : ℂ) ^ (-s))
          _ = 1 + ‖psi p‖ * (p : ℝ) ^ (-s.re) := by
            rw [norm_mul, Complex.norm_natCast_cpow_of_pos hpPrime.pos, neg_re]
          _ ≤ 1 + 1 * (p : ℝ) ^ 10 := by
            gcongr
            exact psi.norm_le_one p
          _ ≤ (p : ℝ) ^ 11 := by simpa using hlarge
    _ = (∏ p ∈ q.primeFactors, (p : ℝ)) ^ 11 :=
      Finset.prod_pow q.primeFactors 11 (fun p : ℕ ↦ (p : ℝ))
    _ ≤ (q : ℝ) ^ 11 := by
      apply pow_le_pow_left₀ (by positivity)
      rw [← Nat.cast_prod]
      exact_mod_cast Nat.le_of_dvd (NeZero.pos q) (Nat.prod_primeFactors_dvd q)

theorem radiusTwelveSphere_re_lower (t : ℝ) {s : ℂ}
    (hs : s ∈ sphere ((2 : ℂ) + t * I) 12) : -(10 : ℝ) ≤ s.re := by
  have hdist : ‖s - ((2 : ℂ) + t * I)‖ = 12 := by
    simpa only [mem_sphere, dist_eq_norm] using hs
  have hre : |s.re - 2| ≤ 12 := by
    simpa [hdist] using Complex.abs_re_le_norm (s - ((2 : ℂ) + t * I))
  have hlower := (abs_le.mp hre).1
  linarith

/-- A radius-twelve polynomial bound uniform over nonprincipal characters,
including imprimitive characters. -/
theorem exists_nonprincipal_radiusTwelve_bound :
    ∃ E : ℕ, 36 ≤ E ∧
      ∀ (q : ℕ) [NeZero q], 1 < q →
        ∀ chi : DirichletCharacter ℂ q, chi ≠ 1 →
          ∀ (t : ℝ) (s : ℂ), s ∈ sphere ((2 : ℂ) + t * I) 12 →
            ‖DirichletCharacter.LFunction chi s‖ ≤
              ((q : ℝ) * (|t| + 2)) ^ E := by
  obtain ⟨E, hE, hprimitive⟩ := exists_nat_norm_LFunction_radiusTwelveSphere_le
  refine ⟨E + 11, by omega, ?_⟩
  intro q _ hq chi hchi t s hs
  let d := chi.conductor
  let psi := chi.primitiveCharacter
  have hd₀ : 0 < d := Nat.pos_of_ne_zero chi.conductor_ne_zero
  let _ : NeZero d := ⟨hd₀.ne'⟩
  have hd₁ : 1 < d := by
    have hne : d ≠ 1 := by
      intro hd
      apply hchi
      exact DirichletCharacter.eq_one_iff_conductor_eq_one.mpr hd
    omega
  have hpsi := hprimitive d hd₁ psi chi.primitiveCharacter_isPrimitive t s hs
  have hEuler := norm_primeEulerProduct_le_pow (q := q) psi
    (radiusTwelveSphere_re_lower t hs)
  have hqd : (d : ℝ) ≤ q := by
    exact_mod_cast Nat.le_of_dvd (NeZero.pos q) chi.conductor_dvd_level
  have hqB : (q : ℝ) ≤ (q : ℝ) * (|t| + 2) := by
    have hq₀ : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    nlinarith [abs_nonneg t]
  rw [LFunction_eq_inducingPrimitive_mul_inducingEulerProduct chi (.inl hchi), norm_mul]
  calc
    ‖DirichletCharacter.LFunction chi.primitiveCharacter s‖ *
        ‖inducingEulerProduct chi s‖ ≤
        ((d : ℝ) * (|t| + 2)) ^ E * (q : ℝ) ^ 11 :=
      mul_le_mul hpsi hEuler (norm_nonneg _) (by positivity)
    _ ≤ ((q : ℝ) * (|t| + 2)) ^ E *
        ((q : ℝ) * (|t| + 2)) ^ 11 := by gcongr
    _ = ((q : ℝ) * (|t| + 2)) ^ (E + 11) := (pow_add _ _ _).symm

/-- Remove the principal pole, leaving every nonprincipal character unchanged. -/
noncomputable def regularizedLFunction {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) : ℂ → ℂ :=
  if chi = 1 then DirichletCharacter.LFunctionTrivChar₁ q
  else DirichletCharacter.LFunction chi

theorem differentiable_regularizedLFunction {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) : Differentiable ℂ (regularizedLFunction chi) := by
  classical
  unfold regularizedLFunction
  split_ifs with hchi
  · exact DirichletCharacter.differentiable_LFunctionTrivChar₁ q
  · exact DirichletCharacter.differentiable_LFunction hchi

theorem regularizedLFunction_eq_mul {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) {s : ℂ} (hs : s ≠ 1) :
    regularizedLFunction chi s =
      (if chi = 1 then s - 1 else 1) * DirichletCharacter.LFunction chi s := by
  classical
  by_cases hchi : chi = 1
  · subst chi
    simp [regularizedLFunction, DirichletCharacter.LFunctionTrivChar₁,
      Function.update_of_ne hs, DirichletCharacter.LFunctionTrivChar]
  · simp [regularizedLFunction, hchi]

theorem regularizedLFunction_ne_zero_of_one_le_re {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 ≤ s.re) :
    regularizedLFunction chi s ≠ 0 := by
  classical
  by_cases hchi : chi = 1
  · subst chi
    by_cases hs₁ : s = 1
    · subst s
      simpa [regularizedLFunction] using
        DirichletCharacter.LFunctionTrivChar₁_apply_one_ne_zero q
    · rw [regularizedLFunction_eq_mul _ hs₁, if_pos rfl]
      exact mul_ne_zero (sub_ne_zero.mpr hs₁)
        ((1 : DirichletCharacter ℂ q).LFunction_ne_zero_of_one_le_re (.inr hs₁) hs)
  · simpa only [regularizedLFunction, if_neg hchi] using
      chi.LFunction_ne_zero_of_one_le_re (.inl hchi) hs

theorem regularizedLFunction_zero_re_lt_one {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) {rho : ℂ}
    (hrho : regularizedLFunction chi rho = 0) : rho.re < 1 := by
  by_contra h
  exact regularizedLFunction_ne_zero_of_one_le_re chi (le_of_not_gt h) hrho

theorem principal_regularization_eq_zeta_mul (q : ℕ) [NeZero q] (s : ℂ) :
    DirichletCharacter.LFunctionTrivChar₁ q s =
      riemannZeta₁ s * ∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-s)) := by
  by_cases hs : s = 1
  · subst s
    simp [DirichletCharacter.LFunctionTrivChar₁, riemannZeta₁_one, Complex.cpow_neg_one]
  · rw [DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hs,
      DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta hs,
      riemannZeta_eq_inv_sub_mul hs]
    field_simp [sub_ne_zero.mpr hs]

theorem exists_regularized_radiusTwelve_bound :
    ∃ E : ℕ, 36 ≤ E ∧
      ∀ (q : ℕ) [NeZero q], 1 < q →
        ∀ (chi : DirichletCharacter ℂ q) (t : ℝ) (s : ℂ),
          s ∈ sphere ((2 : ℂ) + t * I) 12 →
            ‖regularizedLFunction chi s‖ ≤ ((q : ℝ) * (|t| + 2)) ^ E := by
  classical
  obtain ⟨E₁, hE₁, hnonprincipal⟩ := exists_nonprincipal_radiusTwelve_bound
  obtain ⟨E₂, _, hzeta⟩ := exists_nat_norm_riemannZeta₁_radiusTwelveSphere_le
  refine ⟨max E₁ (E₂ + 11), hE₁.trans (le_max_left _ _), ?_⟩
  intro q _ hq chi t s hs
  let B : ℝ := (q : ℝ) * (|t| + 2)
  have hq₁ : (1 : ℝ) ≤ q := by exact_mod_cast hq.le
  have hT₁ : (1 : ℝ) ≤ |t| + 2 := by linarith [abs_nonneg t]
  have hB₁ : 1 ≤ B := one_le_mul_of_one_le_of_one_le hq₁ hT₁
  by_cases hchi : chi = 1
  · subst chi
    rw [regularizedLFunction, if_pos rfl, principal_regularization_eq_zeta_mul, norm_mul]
    have hEuler : ‖∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-s))‖ ≤ (q : ℝ) ^ 11 := by
      convert norm_primeEulerProduct_le_pow (q := q) (1 : DirichletCharacter ℂ 1)
        (radiusTwelveSphere_re_lower t hs) using 1
      congr 1
      apply Finset.prod_congr rfl
      intro p _
      rw [MulChar.one_apply (isUnit_of_subsingleton (p : ZMod 1)), one_mul]
    calc
      ‖riemannZeta₁ s‖ * ‖∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-s))‖ ≤
          (|t| + 2) ^ E₂ * (q : ℝ) ^ 11 :=
        mul_le_mul (hzeta t s hs) hEuler (norm_nonneg _) (by positivity)
      _ ≤ B ^ E₂ * B ^ 11 := by
        apply mul_le_mul (pow_le_pow_left₀ (by positivity : 0 ≤ |t| + 2) ?_ E₂)
          (pow_le_pow_left₀ (Nat.cast_nonneg q) ?_ 11) (by positivity) (by positivity)
        · dsimp [B]
          exact le_mul_of_one_le_left (by positivity) hq₁
        · dsimp [B]
          exact le_mul_of_one_le_right (Nat.cast_nonneg q) hT₁
      _ = B ^ (E₂ + 11) := (pow_add _ _ _).symm
      _ ≤ B ^ max E₁ (E₂ + 11) := pow_le_pow_right₀ hB₁ (le_max_right _ _)
  · rw [regularizedLFunction, if_neg hchi]
    exact (hnonprincipal q hq chi hchi t s hs).trans
      (pow_le_pow_right₀ hB₁ (le_max_left _ _))

theorem one_le_three_mul_norm_regularized_center {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (t : ℝ) :
    1 ≤ 3 * ‖regularizedLFunction chi ((2 : ℂ) + t * I)‖ := by
  let c : ℂ := (2 : ℂ) + t * I
  have hc₁ : c ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    norm_num [c] at this
  have hc : DirichletCharacter.LFunction chi c ≠ 0 :=
    chi.LFunction_ne_zero_of_one_le_re (.inr hc₁) (by simp [c])
  have hinv := norm_inv_LFunction_two_add_mul_I_le_three chi t
  have hL : 1 ≤ 3 * ‖DirichletCharacter.LFunction chi c‖ := by
    calc
      (1 : ℝ) = ‖(DirichletCharacter.LFunction chi c)⁻¹ *
          DirichletCharacter.LFunction chi c‖ := by rw [inv_mul_cancel₀ hc, norm_one]
      _ = ‖(DirichletCharacter.LFunction chi c)⁻¹‖ *
          ‖DirichletCharacter.LFunction chi c‖ := norm_mul _ _
      _ ≤ 3 * ‖DirichletCharacter.LFunction chi c‖ :=
        mul_le_mul_of_nonneg_right hinv (norm_nonneg _)
  have hfactor : 1 ≤ ‖if chi = 1 then c - 1 else (1 : ℂ)‖ := by
    split_ifs
    · have hre := Complex.abs_re_le_norm (c - 1)
      convert hre using 1
      norm_num [c]
    · simp
  have hnorm : ‖DirichletCharacter.LFunction chi c‖ ≤
      ‖regularizedLFunction chi c‖ := by
    rw [regularizedLFunction_eq_mul chi hc₁, norm_mul]
    exact le_mul_of_one_le_left (norm_nonneg _) hfactor
  exact hL.trans (mul_le_mul_of_nonneg_left hnorm (by norm_num))

/-- A single absolute logarithmic growth constant applies to the regularized
L-function of every character on the fixed disks used for zero repulsion. -/
theorem exists_regularized_radiusTwelve_relative_bound :
    ∃ A : ℕ, 37 ≤ A ∧
      ∀ (q : ℕ) [NeZero q], 1 < q →
        ∀ (chi : DirichletCharacter ℂ q) (t : ℝ) (s : ℂ),
          s ∈ sphere ((2 : ℂ) + t * I) 12 →
            ‖regularizedLFunction chi s‖ ≤
              Real.exp ((A : ℝ) * Real.log ((q : ℝ) * (|t| + 2))) *
                ‖regularizedLFunction chi ((2 : ℂ) + t * I)‖ := by
  obtain ⟨E, hE, hbound⟩ := exists_regularized_radiusTwelve_bound
  refine ⟨E + 2, by omega, ?_⟩
  intro q _ hq chi t s hs
  let B : ℝ := (q : ℝ) * (|t| + 2)
  have hq₂ : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hB₄ : 4 ≤ B := by
    dsimp [B]
    nlinarith [abs_nonneg t]
  have hcenter := one_le_three_mul_norm_regularized_center chi t
  have hnorm := norm_nonneg (regularizedLFunction chi ((2 : ℂ) + t * I))
  have hexp : Real.exp (((E + 2 : ℕ) : ℝ) * Real.log B) = B ^ (E + 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by linarith : 0 < B)]
  change ‖regularizedLFunction chi s‖ ≤
    Real.exp (((E + 2 : ℕ) : ℝ) * Real.log B) * _
  rw [hexp, pow_add]
  calc
    ‖regularizedLFunction chi s‖ ≤ B ^ E := hbound q hq chi t s hs
    _ ≤ B ^ E * (3 * ‖regularizedLFunction chi ((2 : ℂ) + t * I)‖) :=
      le_mul_of_one_le_right (by positivity) hcenter
    _ ≤ B ^ E * (B ^ 2 * ‖regularizedLFunction chi ((2 : ℂ) + t * I)‖) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul_of_nonneg_right (by nlinarith : (3 : ℝ) ≤ B ^ 2) hnorm
    _ = B ^ E * B ^ 2 * ‖regularizedLFunction chi ((2 : ℂ) + t * I)‖ := by ring

end Linnik
