import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.Polynomial.GaussLucas
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Tactic

/-!
# Bernstein bounds for complex polynomials and finite Fourier sums

This file proves the sharp Bernstein inequality on the complex unit circle,
its iterated Euler-derivative form used by the Balister--Bollobás--Morris--
Sahasrabudhe--Tiba construction, and elementary coefficient bounds for finite
Fourier sums.  The sharp proof uses polynomial reflection, the maximum-modulus
principle, and Gauss--Lucas.
-/

namespace Erdos228.Bernstein

open scoped BigOperators

/-- The purely imaginary frequency corresponding to the character
`x ↦ exp (k x i)`. -/
def frequency (k : ℕ) : ℂ := (k : ℂ) * Complex.I

/-- The `r`-th formal derivative of a finite Fourier sum.  At `r = 0` this is
the original sum; increasing `r` multiplies the `k`-th coefficient by `k i`.
-/
noncomputable def fourierDerivative (r : ℕ) (s : Finset ℕ) (a : ℕ → ℂ) (x : ℝ) : ℂ :=
  ∑ k ∈ s, a k * frequency k ^ r *
    Complex.exp (((k : ℂ) * (x : ℂ)) * Complex.I)

@[simp]
theorem fourierDerivative_zero (s : Finset ℕ) (a : ℕ → ℂ) (x : ℝ) :
    fourierDerivative 0 s a x =
      ∑ k ∈ s, a k * Complex.exp (((k : ℂ) * (x : ℂ)) * Complex.I) := by
  simp [fourierDerivative]

theorem hasDerivAt_fourierDerivative (r : ℕ) (s : Finset ℕ) (a : ℕ → ℂ) (x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ fourierDerivative r s a y)
      (fourierDerivative (r + 1) s a x) x := by
  classical
  simp only [fourierDerivative]
  refine HasDerivAt.fun_sum fun k hk ↦ ?_
  have hlin : HasDerivAt
      (fun y : ℝ ↦ ((k : ℂ) * (y : ℂ)) * Complex.I)
      (frequency k) x := by
    simpa [frequency, mul_assoc] using
      ((((hasDerivAt_id x).ofReal_comp).const_mul (k : ℂ)).mul_const Complex.I)
  simpa [frequency, pow_succ, mul_assoc, mul_comm, mul_left_comm] using
    (((Complex.hasDerivAt_exp _).comp x hlin).const_mul (a k * frequency k ^ r))

theorem deriv_fourierDerivative (r : ℕ) (s : Finset ℕ) (a : ℕ → ℂ) (x : ℝ) :
    deriv (fun y : ℝ ↦ fourierDerivative r s a y) x =
      fourierDerivative (r + 1) s a x :=
  (hasDerivAt_fourierDerivative r s a x).deriv

/-- Iterating the analytic derivative agrees with the explicitly defined
formal Fourier derivative. -/
theorem iter_deriv_fourierDerivative (q r : ℕ) (s : Finset ℕ) (a : ℕ → ℂ) :
    deriv^[q] (fun y : ℝ ↦ fourierDerivative r s a y) =
      fun y : ℝ ↦ fourierDerivative (r + q) s a y := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [Function.iterate_succ_apply', ih]
      funext x
      simpa [Nat.add_assoc] using deriv_fourierDerivative (r + q) s a x

/-- In particular, the `r`-fold derivative of the original finite Fourier
sum is `fourierDerivative r`. -/
theorem iter_deriv_fourierSum (r : ℕ) (s : Finset ℕ) (a : ℕ → ℂ) :
    deriv^[r] (fun y : ℝ ↦ fourierDerivative 0 s a y) =
      fun y : ℝ ↦ fourierDerivative r s a y := by
  simpa using iter_deriv_fourierDerivative r 0 s a

/-! ### Maximum-modulus preparation for the sharp Bernstein inequality -/

/-- Evaluation identity for the reflection of a polynomial in degree `n`. -/
theorem eval_reflect_mul_pow {p : Polynomial ℂ} {n : ℕ} (hdeg : p.natDegree ≤ n)
    {w : ℂ} (hw : w ≠ 0) :
    (p.reflect n).eval w⁻¹ * w ^ n = p.eval w := by
  let iw : Invertible w := invertibleOfNonzero hw
  simpa [invOf_eq_inv] using
    (@Polynomial.eval₂_reflect_mul_pow ℂ _ ℂ _ (RingHom.id ℂ) w iw n p hdeg)

/-- The degree-`n` reflection is bounded throughout the unit disk whenever
the original polynomial is bounded on the unit circle. -/
theorem norm_reflect_eval_le_of_circle_bound {p : Polynomial ℂ} {n : ℕ}
    (hdeg : p.natDegree ≤ n) {M : ℝ}
    (hM : ∀ z : ℂ, ‖z‖ = 1 → ‖p.eval z‖ ≤ M)
    {u : ℂ} (hu : ‖u‖ ≤ 1) :
    ‖(p.reflect n).eval u‖ ≤ M := by
  let q := p.reflect n
  have hboundary : ∀ z : ℂ, ‖z‖ = 1 → ‖q.eval z‖ ≤ M := by
    intro z hz
    have hz0 : z ≠ 0 := by
      intro hzzero
      simp [hzzero] at hz
    have hzinv : ‖z⁻¹‖ = 1 := by simp [hz]
    have hrel := eval_reflect_mul_pow hdeg (w := z⁻¹) (inv_ne_zero hz0)
    have hnorm : ‖q.eval z‖ = ‖p.eval z⁻¹‖ := by
      have hpownorm : ‖(z⁻¹) ^ n‖ = 1 := by
        rw [norm_pow, hzinv, one_pow]
      calc
        ‖q.eval z‖ = ‖q.eval z‖ * 1 := by simp
        _ = ‖q.eval z‖ * ‖(z⁻¹) ^ n‖ := by rw [hpownorm]
        _ = ‖q.eval z * (z⁻¹) ^ n‖ := by rw [norm_mul]
        _ = ‖p.eval z⁻¹‖ := by
          rw [show q.eval z * (z⁻¹) ^ n = p.eval z⁻¹ by simpa [q] using hrel]
    rw [hnorm]
    exact hM z⁻¹ hzinv
  by_cases hueq : ‖u‖ = 1
  · exact hboundary u hueq
  have hult : ‖u‖ < 1 := lt_of_le_of_ne hu hueq
  apply Complex.norm_le_of_forall_mem_frontier_norm_le
      Metric.isBounded_ball
      ((p.reflect n).differentiableOn.diffContOnCl_ball Set.Subset.rfl)
      (C := M)
  · intro z hz
    apply hboundary z
    have hzsphere : z ∈ Metric.sphere (0 : ℂ) 1 :=
      Metric.frontier_ball_subset_sphere hz
    simpa [Metric.mem_sphere, dist_zero_right] using hzsphere
  · exact subset_closure (by simpa [Metric.mem_ball, dist_zero_right] using hult)

/-- Bernstein--Walsh outside the disk, in the elementary polynomial form
needed for the proof of the sharp circle derivative bound. -/
theorem norm_eval_le_circle_bound_mul_pow {p : Polynomial ℂ} {n : ℕ}
    (hdeg : p.natDegree ≤ n) {M : ℝ}
    (hM : ∀ z : ℂ, ‖z‖ = 1 → ‖p.eval z‖ ≤ M)
    {w : ℂ} (hw : 1 ≤ ‖w‖) :
    ‖p.eval w‖ ≤ M * ‖w‖ ^ n := by
  have hw0 : w ≠ 0 := by
    apply norm_ne_zero_iff.mp
    linarith
  have hu : ‖w⁻¹‖ ≤ 1 := by
    rw [norm_inv]
    exact (inv_le_one₀ (lt_of_lt_of_le zero_lt_one hw)).2 hw
  have hq := norm_reflect_eval_le_of_circle_bound hdeg hM hu
  have hrel := eval_reflect_mul_pow hdeg hw0
  calc
    ‖p.eval w‖ = ‖(p.reflect n).eval w⁻¹‖ * ‖w‖ ^ n := by
      rw [← hrel, norm_mul, norm_pow]
    _ ≤ M * ‖w‖ ^ n :=
      mul_le_mul_of_nonneg_right hq (by positivity)

/-- Every coefficient up to a prescribed degree is bounded by the uniform
bound on the unit circle.  We only need the top coefficient below. -/
theorem norm_coeff_le_of_circle_bound {p : Polynomial ℂ} {n : ℕ}
    (hdeg : p.natDegree ≤ n) {M : ℝ}
    (hM : ∀ z : ℂ, ‖z‖ = 1 → ‖p.eval z‖ ≤ M) :
    ‖p.coeff n‖ ≤ M := by
  have hq := norm_reflect_eval_le_of_circle_bound hdeg hM (u := (0 : ℂ)) (by norm_num)
  rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_reflect,
    Polynomial.revAt_zero] at hq
  exact hq

/-! ### Sharp Bernstein inequality on the unit circle -/

/-- **Bernstein's inequality on the unit circle.**  If a complex polynomial
has degree at most `n` and norm at most `M` on the unit circle, then its
derivative has norm at most `n M` there.

The proof is the classical short argument using polynomial reflection,
the maximum-modulus principle, and Gauss--Lucas.  If the asserted derivative
bound failed at `z`, subtract the monomial whose derivative cancels there.
The new polynomial has every zero strictly inside the unit disk, whereas
Gauss--Lucas would put the unit-circle point `z` in their convex hull.
-/
theorem norm_derivative_eval_le_degree_mul_circleSup {p : Polynomial ℂ} {n : ℕ}
    (hdeg : p.natDegree ≤ n) {M : ℝ}
    (hM : ∀ w : ℂ, ‖w‖ = 1 → ‖p.eval w‖ ≤ M)
    {z : ℂ} (hz : ‖z‖ = 1) :
    ‖p.derivative.eval z‖ ≤ (n : ℝ) * M := by
  by_cases hn : n = 0
  · subst n
    have hpdeg : p.natDegree = 0 := Nat.eq_zero_of_le_zero hdeg
    rw [Polynomial.derivative_eq_zero.mpr hpdeg]
    simp
  have hnNat : 0 < n := Nat.pos_of_ne_zero hn
  have hnReal : (0 : ℝ) < n := by exact_mod_cast hnNat
  by_contra hbound
  rw [not_le] at hbound
  have hz0 : z ≠ 0 := by
    intro hzero
    simp [hzero] at hz
  let β : ℂ := p.derivative.eval z / ((n : ℂ) * z ^ (n - 1))
  have hdenom : (n : ℂ) * z ^ (n - 1) ≠ 0 := by
    exact mul_ne_zero (by exact_mod_cast hn) (pow_ne_zero _ hz0)
  have hβcancel : β * (n : ℂ) * z ^ (n - 1) = p.derivative.eval z := by
    dsimp [β]
    field_simp
  have hβnorm : ‖β‖ = ‖p.derivative.eval z‖ / (n : ℝ) := by
    dsimp [β]
    rw [norm_div, norm_mul, norm_pow, hz, one_pow, mul_one]
    simp
  have hβM : M < ‖β‖ := by
    rw [hβnorm, lt_div_iff₀ hnReal]
    simpa [mul_comm] using hbound
  let P : Polynomial ℂ := p - Polynomial.C β * Polynomial.X ^ n
  have hpcoeff : ‖p.coeff n‖ ≤ M := norm_coeff_le_of_circle_bound hdeg hM
  have hcoeffne : p.coeff n ≠ β := by
    intro heq
    rw [heq] at hpcoeff
    exact (not_le_of_gt hβM) hpcoeff
  have hPcoeff : P.coeff n ≠ 0 := by
    simpa [P, Polynomial.coeff_C_mul_X_pow] using sub_ne_zero.mpr hcoeffne
  have hPnatDegreePos : 0 < P.natDegree :=
    hnNat.trans_le (Polynomial.le_natDegree_of_ne_zero hPcoeff)
  have hPdegreePos : 0 < P.degree :=
    Polynomial.natDegree_pos_iff_degree_pos.mp hPnatDegreePos
  have hPderiv : P.derivative.eval z = 0 := by
    rw [show P.derivative.eval z = p.derivative.eval z -
        β * (n : ℂ) * z ^ (n - 1) by
      simp only [P, Polynomial.derivative_sub, Polynomial.derivative_C_mul_X_pow,
        Polynomial.eval_sub, Polynomial.eval_C_mul, Polynomial.eval_X_pow]]
    exact sub_eq_zero.mpr hβcancel.symm
  have hPderiv_ne : P.derivative ≠ 0 := by
    rw [Polynomial.derivative_ne_zero]
    exact hPnatDegreePos.ne'
  have hzDerivRoot : z ∈ P.derivative.rootSet ℂ := by
    rw [Polynomial.mem_rootSet]
    exact ⟨hPderiv_ne, hPderiv⟩
  have hroots : P.rootSet ℂ ⊆ Metric.ball 0 1 := by
    intro w hwroot
    rw [Polynomial.mem_rootSet] at hwroot
    have hPeval0 : P.eval w = 0 := by
      simpa [Polynomial.coe_aeval_eq_eval] using hwroot.2
    have hPeval : p.eval w = β * w ^ n := by
      apply sub_eq_zero.mp
      simpa [P] using hPeval0
    have hwlt : ‖w‖ < 1 := by
      by_contra hwlt
      have hwge : 1 ≤ ‖w‖ := le_of_not_gt hwlt
      have hout := norm_eval_le_circle_bound_mul_pow hdeg hM hwge
      have hmul : ‖β‖ * ‖w‖ ^ n ≤ M * ‖w‖ ^ n := by
        rw [hPeval, norm_mul, norm_pow] at hout
        exact hout
      have hpow : 0 < ‖w‖ ^ n := pow_pos (lt_of_lt_of_le zero_lt_one hwge) n
      have : ‖β‖ ≤ M := le_of_mul_le_mul_right hmul hpow
      exact (not_le_of_gt hβM) this
    simpa [Metric.mem_ball, dist_zero_right] using hwlt
  have hconvex : convexHull ℝ (P.rootSet ℂ) ⊆ Metric.ball 0 1 :=
    convexHull_min hroots (convex_ball 0 1)
  have hzHull : z ∈ convexHull ℝ (P.rootSet ℂ) :=
    Polynomial.rootSet_derivative_subset_convexHull_rootSet hPdegreePos hzDerivRoot
  have hzlt : ‖z‖ < 1 := by
    simpa [Metric.mem_ball, dist_zero_right] using hconvex hzHull
  linarith

/-! ### Iteration for derivatives of `p (exp (i x))` -/

/-- The Euler derivative `z p'(z)`.  Under the substitution `z = exp (i x)`,
ordinary differentiation in `x` is multiplication of this operator by `i`.
-/
noncomputable def eulerDerivative (p : Polynomial ℂ) : Polynomial ℂ :=
  Polynomial.X * p.derivative

@[simp]
theorem eval_eulerDerivative (p : Polynomial ℂ) (z : ℂ) :
    (eulerDerivative p).eval z = z * p.derivative.eval z := by
  simp [eulerDerivative]

/-- The Euler derivative does not increase polynomial degree. -/
theorem natDegree_eulerDerivative_le (p : Polynomial ℂ) :
    (eulerDerivative p).natDegree ≤ p.natDegree := by
  by_cases hp : p.natDegree = 0
  · simp [eulerDerivative, Polynomial.derivative_of_natDegree_zero hp, hp]
  have hd := Polynomial.natDegree_derivative_le p
  calc
    (eulerDerivative p).natDegree ≤
        Polynomial.X.natDegree + p.derivative.natDegree := by
      exact Polynomial.natDegree_mul_le
    _ ≤ 1 + (p.natDegree - 1) := by
      simp only [Polynomial.natDegree_X]
      exact Nat.add_le_add_left hd 1
    _ = p.natDegree := by omega

/-- Every iterate of the Euler derivative has degree at most that of the
starting polynomial. -/
theorem natDegree_iterate_eulerDerivative_le (r : ℕ) (p : Polynomial ℂ) :
    (eulerDerivative^[r] p).natDegree ≤ p.natDegree := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [Function.iterate_succ_apply']
      exact (natDegree_eulerDerivative_le _).trans ih

/-- Iterated sharp Bernstein inequality for the Euler derivative.  This is
the precise uniform estimate used after composing a polynomial with the unit
circle parametrization. -/
theorem norm_iterate_eulerDerivative_eval_le_pow_mul_circleSup
    {p : Polynomial ℂ} {n : ℕ} (hdeg : p.natDegree ≤ n) {M : ℝ}
    (hM : ∀ w : ℂ, ‖w‖ = 1 → ‖p.eval w‖ ≤ M)
    (r : ℕ) {z : ℂ} (hz : ‖z‖ = 1) :
    ‖(eulerDerivative^[r] p).eval z‖ ≤ (n : ℝ) ^ r * M := by
  induction r generalizing z with
  | zero => simpa using hM z hz
  | succ r ih =>
      let q := eulerDerivative^[r] p
      have hqdeg : q.natDegree ≤ n :=
        (natDegree_iterate_eulerDerivative_le r p).trans hdeg
      have hqM : ∀ w : ℂ, ‖w‖ = 1 → ‖q.eval w‖ ≤ (n : ℝ) ^ r * M := by
        intro w hw
        exact ih hw
      have hderiv :=
        norm_derivative_eval_le_degree_mul_circleSup hqdeg hqM hz
      rw [Function.iterate_succ_apply']
      calc
        ‖(eulerDerivative q).eval z‖ = ‖q.derivative.eval z‖ := by
          rw [eval_eulerDerivative, norm_mul, hz, one_mul]
        _ ≤ (n : ℝ) * ((n : ℝ) ^ r * M) := hderiv
        _ = (n : ℝ) ^ (r + 1) * M := by rw [pow_succ]; ring

/-- Coefficient form of the derivative bound: the norm of an iterated
derivative is at most the weighted `ℓ1` norm of its coefficients. -/
theorem norm_fourierDerivative_le_weighted (r : ℕ) (s : Finset ℕ)
    (a : ℕ → ℂ) (x : ℝ) :
    ‖fourierDerivative r s a x‖ ≤ ∑ k ∈ s, ‖a k‖ * (k : ℝ) ^ r := by
  classical
  calc
    ‖fourierDerivative r s a x‖ ≤
        ∑ k ∈ s, ‖a k * frequency k ^ r *
          Complex.exp (((k : ℂ) * (x : ℂ)) * Complex.I)‖ := by
      exact norm_sum_le _ _
    _ = ∑ k ∈ s, ‖a k‖ * (k : ℝ) ^ r := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [norm_mul, norm_mul, norm_pow]
      have hexp :
          ‖Complex.exp (((k : ℂ) * (x : ℂ)) * Complex.I)‖ = 1 := by
        rw [show (((k : ℂ) * (x : ℂ)) * Complex.I) =
            ((((k : ℝ) * x : ℝ) : ℂ) * Complex.I) by norm_num]
        exact Complex.norm_exp_ofReal_mul_I ((k : ℝ) * x)
      simp [frequency, hexp]

/-- If every occurring frequency is at most `N`, the weighted coefficient
bound is at most `N^r` times the coefficient `ℓ1` norm. -/
theorem norm_fourierDerivative_le_degree (r N : ℕ) (s : Finset ℕ)
    (a : ℕ → ℂ) (hs : ∀ k ∈ s, k ≤ N) (x : ℝ) :
    ‖fourierDerivative r s a x‖ ≤
      (N : ℝ) ^ r * ∑ k ∈ s, ‖a k‖ := by
  refine (norm_fourierDerivative_le_weighted r s a x).trans ?_
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := by positivity
  have hkN : (k : ℝ) ≤ (N : ℝ) := by exact_mod_cast hs k hk
  simpa [mul_comm] using
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hk0 hkN r) (norm_nonneg (a k)))

/-- The specialization to coefficients of norm at most one. -/
theorem norm_fourierDerivative_le_card_mul_degree (r N : ℕ) (s : Finset ℕ)
    (a : ℕ → ℂ) (hs : ∀ k ∈ s, k ≤ N) (ha : ∀ k ∈ s, ‖a k‖ ≤ 1)
    (x : ℝ) :
    ‖fourierDerivative r s a x‖ ≤ s.card * (N : ℝ) ^ r := by
  calc
    ‖fourierDerivative r s a x‖ ≤
        (N : ℝ) ^ r * ∑ k ∈ s, ‖a k‖ :=
      norm_fourierDerivative_le_degree r N s a hs x
    _ ≤ (N : ℝ) ^ r * ∑ _k ∈ s, (1 : ℝ) := by
      exact mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun k hk ↦ ha k hk) (by positivity)
    _ = s.card * (N : ℝ) ^ r := by
      simp [mul_comm]

end Erdos228.Bernstein
