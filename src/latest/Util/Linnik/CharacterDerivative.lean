import Util.Linnik.FixedDisk
import Util.Linnik.CharacterPositivity

/-!
# The principal pole in high character derivatives

Separate the principal pole from the regularized analytic function before
applying the finite zero-divisor estimate.
-/

namespace Linnik

open Complex Metric Set
open scoped BigOperators Classical

theorem neg_logDeriv_LFunction_eq_pole_sub_regularized
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 < s.re) :
    -logDeriv (DirichletCharacter.LFunction chi) s =
      (if chi = 1 then (s - 1)⁻¹ else 0) - logDeriv (regularizedLFunction chi) s := by
  have hs₁ : s ≠ 1 := by intro h; simp [h] at hs
  have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hs₁
  have hL : DirichletCharacter.LFunction chi s ≠ 0 :=
    chi.LFunction_ne_zero_of_one_le_re (.inr hs₁) hs.le
  by_cases hchi : chi = 1
  · subst chi
    rw [regularizedLFunction, if_pos rfl, if_pos rfl,
      logDeriv_apply, logDeriv_apply,
      DirichletCharacter.deriv_LFunctionTrivChar₁_apply_of_ne_one q hs₁,
      DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hs₁]
    change -(deriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)) s /
      DirichletCharacter.LFunction 1 s) = _
    dsimp only [DirichletCharacter.LFunctionTrivChar]
    field_simp [hsub, hL]
    ring
  · simp [regularizedLFunction, hchi]

theorem iteratedDeriv_principal_pole {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) {s : ℂ} (k : ℕ) :
    iteratedDeriv k (fun w : ℂ ↦ if chi = 1 then (w - 1)⁻¹ else 0) s =
      (-1 : ℂ) ^ k * k.factorial * (if chi = 1 then ((s - 1) ^ (k + 1))⁻¹ else 0) := by
  by_cases hchi : chi = 1
  · simp only [hchi, ite_true]
    have hinv := iter_deriv_inv_linear_sub (𝕜 := ℂ) k 1 1
    simp only [one_mul, one_pow] at hinv
    have h := congrFun hinv s
    rw [← iteratedDeriv_eq_iterate] at h
    have hexp : (-1 - (k : ℤ)) = -((k + 1 : ℕ) : ℤ) := by omega
    simpa only [hexp, zpow_neg, zpow_natCast, mul_one] using h
  · simp only [hchi, if_false, mul_zero]
    simp

theorem signedLogDerivative_eq_pole_sub_deriv
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 < s.re) (k : ℕ) :
    signedLogDerivative k chi s =
      k.factorial * (if chi = 1 then ((s - 1) ^ (k + 1))⁻¹ else 0) -
        (-1 : ℂ) ^ k * iteratedDeriv k (logDeriv (regularizedLFunction chi)) s := by
  let U : Set ℂ := {w | 1 < w.re}
  have hU : IsOpen U := isOpen_lt continuous_const continuous_re
  have heq : Set.EqOn (fun w ↦ -logDeriv (DirichletCharacter.LFunction chi) w)
      (fun w ↦ (if chi = 1 then (w - 1)⁻¹ else 0) -
        logDeriv (regularizedLFunction chi) w) U :=
    fun w hw ↦ neg_logDeriv_LFunction_eq_pole_sub_regularized chi hw
  have hs₁ : s ≠ 1 := by intro h; simp [h] at hs
  have hpole : AnalyticAt ℂ (fun w : ℂ ↦ if chi = 1 then (w - 1)⁻¹ else 0) s := by
    by_cases hchi : chi = 1
    · simp only [hchi, ite_true]
      exact (analyticAt_id.sub analyticAt_const).inv (sub_ne_zero.mpr hs₁)
    · simp only [hchi, if_false]
      exact analyticAt_const
  have hreg := (differentiable_regularizedLFunction chi).analyticAt s
  have hlog : AnalyticAt ℂ (logDeriv (regularizedLFunction chi)) s := by
    simpa only [logDeriv] using hreg.deriv.div hreg
      (regularizedLFunction_ne_zero_of_one_le_re chi hs.le)
  rw [signedLogDerivative, heq.iteratedDeriv_of_isOpen hU k hs,
    iteratedDeriv_fun_sub hpole.contDiffAt hlog.contDiffAt,
    iteratedDeriv_principal_pole chi, mul_sub]
  have hsign : (-1 : ℂ) ^ k * (-1 : ℂ) ^ k = 1 := by rw [← mul_pow]; simp
  simp only [← mul_assoc, hsign, one_mul]

theorem norm_signedLogDerivative_sub_diskZeros_le
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (t : ℝ) (k : ℕ)
    {E : ℝ}
    (happrox :
      ‖iteratedDeriv k (logDeriv (regularizedLFunction chi)) ((2 : ℂ) + t * I) -
          (-1 : ℂ) ^ k * k.factorial *
            (characterDiskZeros chi t).sum
              (fun rho m ↦ (m : ℂ) / ((2 : ℂ) + t * I - rho) ^ (k + 1))‖ ≤ E) :
    ‖signedLogDerivative k chi ((2 : ℂ) + t * I) -
        k.factorial *
          ((if chi = 1 then (((2 : ℂ) + t * I - 1) ^ (k + 1))⁻¹ else 0) -
            (characterDiskZeros chi t).sum
              (fun rho m ↦ (m : ℂ) / ((2 : ℂ) + t * I - rho) ^ (k + 1)))‖ ≤ E := by
  rw [signedLogDerivative_eq_pole_sub_deriv chi (by simp)]
  let Z : ℂ := (characterDiskZeros chi t).sum
    (fun rho m ↦ (m : ℂ) / ((2 : ℂ) + t * I - rho) ^ (k + 1))
  let F : ℂ := iteratedDeriv k (logDeriv (regularizedLFunction chi)) ((2 : ℂ) + t * I)
  let P : ℂ := if chi = 1 then (((2 : ℂ) + t * I - 1) ^ (k + 1))⁻¹ else 0
  have hsign : ((-1 : ℂ) ^ k) ^ 2 = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    norm_num
  have hid : (k.factorial : ℂ) * P - (-1 : ℂ) ^ k * F -
      k.factorial * (P - Z) =
      -(-1 : ℂ) ^ k * (F - (-1 : ℂ) ^ k * k.factorial * Z) := by
    calc
      _ = -(-1 : ℂ) ^ k * F + k.factorial * Z := by ring
      _ = -(-1 : ℂ) ^ k * F + ((-1 : ℂ) ^ k) ^ 2 * k.factorial * Z := by rw [hsign, one_mul]
      _ = _ := by ring
  change ‖(k.factorial : ℂ) * P - (-1 : ℂ) ^ k * F - k.factorial * (P - Z)‖ ≤ E
  rw [hid, norm_mul, norm_neg, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  exact happrox

theorem re_zeroSum_le_of_norm_bound {k : ℕ} {S P Z : ℂ} {E : ℝ}
    (h : ‖S - k.factorial * (P - Z)‖ ≤ (k.factorial : ℝ) * E) :
    Z.re ≤ P.re - S.re / (k.factorial : ℝ) + E := by
  have hfac : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  have hre : (S - k.factorial * (P - Z)).re ≤ (k.factorial : ℝ) * E :=
    (le_abs_self _).trans ((Complex.abs_re_le_norm _).trans h)
  simp only [Complex.sub_re, Complex.mul_re, Complex.natCast_re,
    Complex.natCast_im, zero_mul, sub_zero] at hre
  apply (mul_le_mul_iff_of_pos_right hfac).mp
  have hcancel : S.re / (k.factorial : ℝ) * k.factorial = S.re :=
    div_mul_cancel₀ _ hfac.ne'
  nlinarith

/-- A uniform real-part bound for every reciprocal zero-power sum. -/
theorem exists_re_characterDiskZeros_bound :
    ∃ A : ℕ, 37 ≤ A ∧
      ∀ (q : ℕ) [NeZero q], 1 < q →
        ∀ (chi : DirichletCharacter ℂ q) (t : ℝ) (k : ℕ),
          ((characterDiskZeros chi t).sum
            (fun rho m ↦ (m : ℂ) / ((2 : ℂ) + t * I - rho) ^ (k + 1))).re ≤
          (if chi = 1 then (((2 : ℂ) + t * I - 1) ^ (k + 1))⁻¹ else 0).re -
            (signedLogDerivative k chi ((2 : ℂ) + t * I)).re / (k.factorial : ℝ) +
            16 * ((A : ℝ) * Real.log ((q : ℝ) * (|t| + 2))) / (3 : ℝ) ^ (k + 1) := by
  obtain ⟨A, hA, hbound⟩ := exists_characterDiskZeros_bounds
  refine ⟨A, hA, ?_⟩
  intro q _ hq chi t k
  have h := norm_signedLogDerivative_sub_diskZeros_le chi t k ((hbound q hq chi t).2 k)
  apply re_zeroSum_le_of_norm_bound
  convert h using 1
  rw [pow_succ]
  field_simp

noncomputable def zeroPowerSum {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (t : ℝ) (n : ℕ) : ℂ :=
  (characterDiskZeros chi t).sum
    (fun rho m ↦ (m : ℂ) / ((2 : ℂ) + t * I - rho) ^ n)

noncomputable def principalPolePower {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (t : ℝ) (n : ℕ) : ℂ :=
  if chi = 1 then (((2 : ℂ) + t * I - 1) ^ n)⁻¹ else 0

/-- Combine positivity with the four local logarithmic-derivative expansions.
The only terms retained on the right are the principal poles and a decaying
regular-factor error. -/
theorem exists_quadratic_four_zeroPowerSum_bound :
    ∃ A : ℕ, 37 ≤ A ∧
      ∀ (q : ℕ) [NeZero q], 1 < q →
        ∀ (chi1 chi : DirichletCharacter ℂ q), chi1 ^ 2 = 1 →
          ∀ (t : ℝ) (n : ℕ), 1 ≤ n →
            (zeroPowerSum (1 : DirichletCharacter ℂ q) 0 n +
              zeroPowerSum chi1 0 n + zeroPowerSum chi t n +
              zeroPowerSum (chi * chi1) t n).re ≤
            (principalPolePower (1 : DirichletCharacter ℂ q) 0 n +
              principalPolePower chi1 0 n + principalPolePower chi t n +
              principalPolePower (chi * chi1) t n).re +
            64 * ((A : ℝ) * Real.log ((q : ℝ) * (|t| + 2))) / (3 : ℝ) ^ n := by
  obtain ⟨A, hA, hbound⟩ := exists_re_characterDiskZeros_bound
  refine ⟨A, hA, ?_⟩
  intro q _ hq chi1 chi hchi1 t n hn
  let k := n - 1
  have hk : k + 1 = n := by dsimp [k]; omega
  have h₀ := hbound q hq (1 : DirichletCharacter ℂ q) 0 k
  have h₁ := hbound q hq chi1 0 k
  have h₂ := hbound q hq chi t k
  have h₃ := hbound q hq (chi * chi1) t k
  have hpos := quadratic_four_signedLogDerivatives_nonneg k chi1 chi hchi1
    (by norm_num : (1 : ℝ) < 2) t
  have hq₀ : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hlog : Real.log ((q : ℝ) * (|0| + 2)) ≤
      Real.log ((q : ℝ) * (|t| + 2)) := by
    apply Real.log_le_log (by positivity)
    apply mul_le_mul_of_nonneg_left _ hq₀.le
    simp only [abs_zero, zero_add]
    linarith [abs_nonneg t]
  have hA₀ : (0 : ℝ) ≤ A := Nat.cast_nonneg A
  have herr := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hlog (show 0 ≤ 16 * (A : ℝ) by positivity))
    (show 0 ≤ (3 : ℝ) ^ n by positivity)
  have hfrac := div_nonneg hpos (show (0 : ℝ) ≤ k.factorial by positivity)
  simp only [add_div, Complex.ofReal_ofNat, mul_comm I (t : ℂ)] at hfrac
  simp only [hk] at h₀ h₁ h₂ h₃
  simp only [zeroPowerSum, principalPolePower, Complex.add_re, Complex.ofReal_zero,
    zero_mul, add_zero]
  simp only [Complex.ofReal_zero, zero_mul, add_zero] at h₀ h₁
  linear_combination h₀ + h₁ + h₂ + h₃ + hfrac + 2 * herr

end Linnik
