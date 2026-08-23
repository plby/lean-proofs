/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos240.BakerLemma4Concrete
import ErdosProblems.Erdos240.BakerRationalExtrapolation
import Mathlib.Analysis.Complex.Liouville

/-!
# An explicit, factorial-cancelled Hermite basis

For the consecutive nodes `1, ..., R`, let `A_r` be the product of all
linear factors except the factor at `r`.  The Taylor coefficients at `r` of
`(A_r^T)⁻¹` give the usual explicit Hermite basis.  Cauchy's estimate on the
circle of radius `1/2` bounds these coefficients, while the factorials in
`A_r(r)` cancel the same factorials in `A_r(l)`.  Thus evaluating the basis
at an integral target `l > R` costs only a power of two with exponent linear
in `(R+l)T`; in particular no `R*T*log R` term occurs.
-/

open scoped BigOperators

open Complex Finset Function Metric Polynomial Set

noncomputable section

namespace Erdos240.ExplicitHermiteBasis

open Erdos240.BakerLemma4Concrete

/-- The product of all integral-node factors except the factor at `r`. -/
def cofactorPolynomial (R r : ℕ) : ℂ[X] :=
  ∏ i ∈ range R,
    if i + 1 = r then 1 else X - C (((i + 1 : ℕ) : ℂ))

/-- The inverse of the `T`th power of the cofactor, as a holomorphic
function near the omitted node. -/
def inverseCofactorPower (R T r : ℕ) (z : ℂ) : ℂ :=
  ((cofactorPolynomial R r).eval z)⁻¹ ^ T

/-- The normalized Taylor coefficients of the inverse cofactor power. -/
def inverseCofactorJet (R T r j : ℕ) : ℂ :=
  iteratedDeriv j (inverseCofactorPower R T r) (r : ℂ) /
    (j.factorial : ℂ)

/-- The truncated Taylor polynomial of the inverse cofactor power, written
in the local coordinate `X-r`. -/
def inverseCofactorTaylor (R T r n : ℕ) : ℂ[X] :=
  ∑ j ∈ range n,
    C (inverseCofactorJet R T r j) * (X - C (r : ℂ)) ^ j

/-- The explicit normalized Hermite basis element for the `m`th jet at `r`. -/
def basisPolynomial (R T r m : ℕ) : ℂ[X] :=
  (X - C (r : ℂ)) ^ m * (cofactorPolynomial R r) ^ T *
    inverseCofactorTaylor R T r (T - m)

/-- One summand of the explicit Hermite basis. -/
def basisTerm (R T r m j : ℕ) : ℂ[X] :=
  (X - C (r : ℂ)) ^ m * (cofactorPolynomial R r) ^ T *
    (C (inverseCofactorJet R T r j) * (X - C (r : ℂ)) ^ j)

@[simp] theorem eval_cofactorPolynomial (R r : ℕ) (z : ℂ) :
    (cofactorPolynomial R r).eval z =
      ∏ i ∈ range R,
        if i + 1 = r then 1 else z - (((i + 1 : ℕ) : ℂ)) := by
  classical
  rw [cofactorPolynomial, Polynomial.eval_prod]
  apply Finset.prod_congr rfl
  intro i hi
  split_ifs <;> simp

theorem cofactorPolynomial_eval_ne_zero_of_mem_closedBall
    {R r : ℕ} (hr : 1 ≤ r) (hrR : r ≤ R)
    {z : ℂ} (hz : z ∈ closedBall (r : ℂ) (1 / 2 : ℝ)) :
    (cofactorPolynomial R r).eval z ≠ 0 := by
  rw [eval_cofactorPolynomial]
  classical
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  split_ifs with hir
  · simp
  · have hdist : 1 ≤ ‖((i + 1 : ℕ) : ℂ) - (r : ℂ)‖ := by
      have h := one_le_norm_integral_nodes_sub_of_ne
        (i := r - 1) (j := i) (by omega)
      simpa [Nat.sub_add_cancel hr] using h
    have hzhalf : ‖z - (r : ℂ)‖ ≤ 1 / 2 := by
      simpa [mem_closedBall, dist_eq_norm] using hz
    intro hzero
    have hzr : z = ((i + 1 : ℕ) : ℂ) := sub_eq_zero.mp hzero
    subst z
    have hzhalf' : ‖((i + 1 : ℕ) : ℂ) - (r : ℂ)‖ ≤ 1 / 2 := hzhalf
    linarith

/-- On the half-unit circle, the omitted-factor product retains the exact
factorials coming from the integer spacings. -/
theorem cofactorPolynomial_norm_lower_on_half_circle
    {R r : ℕ} (hr : 1 ≤ r) (hrR : r ≤ R)
    {z : ℂ} (hz : ‖z - (r : ℂ)‖ = 1 / 2) :
    (1 / 2 : ℝ) ^ (R - 1) * (r - 1).factorial * (R - r).factorial ≤
      ‖(cofactorPolynomial R r).eval z‖ := by
  have hfull := localCircle_denominator_lower hr hrR hz
  have hprod :
      (∏ i ∈ range R, ‖z - (((i + 1 : ℕ) : ℂ))‖) =
        ‖z - (r : ℂ)‖ * ‖(cofactorPolynomial R r).eval z‖ := by
    classical
    rw [eval_cofactorPolynomial, norm_prod]
    have hrmem : r - 1 ∈ range R := by simp; omega
    rw [← Finset.mul_prod_erase (range R)
      (fun i ↦ ‖z - (((i + 1 : ℕ) : ℂ))‖) hrmem]
    congr 1
    · rw [Nat.sub_add_cancel hr]
    · rw [← Finset.prod_erase (s := range R) (a := r - 1)
          (f := fun i ↦ ‖if i + 1 = r then (1 : ℂ)
            else z - (((i + 1 : ℕ) : ℂ))‖)]
      · apply Finset.prod_congr rfl
        intro i hi
        have hne : i ≠ r - 1 := (Finset.mem_erase.mp hi).1
        have hir : i + 1 ≠ r := by omega
        simp [hir]
      · simp [Nat.sub_add_cancel hr]
  rw [hprod, hz] at hfull
  have hpow : (1 / 2 : ℝ) ^ R =
      (1 / 2) * (1 / 2) ^ (R - 1) := by
    calc
      (1 / 2 : ℝ) ^ R = (1 / 2) ^ ((R - 1) + 1) := by congr 1 <;> omega
      _ = (1 / 2) * (1 / 2) ^ (R - 1) := by rw [pow_succ]; ring
  rw [hpow] at hfull
  nlinarith [norm_nonneg ((cofactorPolynomial R r).eval z)]

/-- Removing the centre factor from the full nodal product. -/
theorem full_nodal_norm_eq_center_mul_cofactor_norm
    {R r : ℕ} (hr : 1 ≤ r) (hrR : r ≤ R) (z : ℂ) :
    (∏ i ∈ range R, ‖z - (((i + 1 : ℕ) : ℂ))‖) =
      ‖z - (r : ℂ)‖ * ‖(cofactorPolynomial R r).eval z‖ := by
  classical
  rw [eval_cofactorPolynomial, norm_prod]
  have hrmem : r - 1 ∈ range R := by simp; omega
  rw [← Finset.mul_prod_erase (range R)
    (fun i ↦ ‖z - (((i + 1 : ℕ) : ℂ))‖) hrmem]
  congr 1
  · rw [Nat.sub_add_cancel hr]
  · rw [← Finset.prod_erase (s := range R) (a := r - 1)
        (f := fun i ↦ ‖if i + 1 = r then (1 : ℂ)
          else z - (((i + 1 : ℕ) : ℂ))‖)]
    · apply Finset.prod_congr rfl
      intro i hi
      have hne : i ≠ r - 1 := (Finset.mem_erase.mp hi).1
      have hir : i + 1 ≠ r := by omega
      simp [hir]
    · simp [Nat.sub_add_cancel hr]

theorem inverseCofactorPower_diffContOnCl_halfBall
    {R T r : ℕ} (hr : 1 ≤ r) (hrR : r ≤ R) :
    DiffContOnCl ℂ (inverseCofactorPower R T r)
      (ball (r : ℂ) (1 / 2 : ℝ)) := by
  have hpoly : DiffContOnCl ℂ
      (fun z : ℂ ↦ (cofactorPolynomial R r).eval z)
      (ball (r : ℂ) (1 / 2 : ℝ)) :=
    (Polynomial.differentiable _).diffContOnCl
  have hinv := hpoly.inv (fun z hz ↦
    cofactorPolynomial_eval_ne_zero_of_mem_closedBall hr hrR (by
      exact closure_ball_subset_closedBall hz))
  induction T with
  | zero =>
      change DiffContOnCl ℂ (fun _ : ℂ ↦ (1 : ℂ))
        (ball (r : ℂ) (1 / 2 : ℝ))
      exact diffContOnCl_const
  | succ T ih =>
      change DiffContOnCl ℂ
        (fun z ↦ ((cofactorPolynomial R r).eval z)⁻¹ ^ (T + 1)) _
      change DiffContOnCl ℂ
        (fun z ↦ ((cofactorPolynomial R r).eval z)⁻¹ ^ T) _ at ih
      exact ⟨ih.1.mul hinv.1, ih.2.mul hinv.2⟩

/-- Cauchy's estimate for the inverse-cofactor Taylor coefficients.  This
is where the half-unit circle turns the geometric loss into a power of two.
The factorials are kept explicit for the later cancellation. -/
theorem norm_inverseCofactorJet_le
    {R T r j : ℕ} (hr : 1 ≤ r) (hrR : r ≤ R) :
    ‖inverseCofactorJet R T r j‖ ≤
      (2 : ℝ) ^ ((R - 1) * T + j) /
        (((r - 1).factorial : ℝ) * (R - r).factorial) ^ T := by
  let D : ℝ := ((r - 1).factorial : ℝ) * (R - r).factorial
  have hD : 0 < D := by dsimp [D]; positivity
  have hC : ∀ z ∈ sphere (r : ℂ) (1 / 2 : ℝ),
      ‖inverseCofactorPower R T r z‖ ≤
        (2 : ℝ) ^ ((R - 1) * T) / D ^ T := by
    intro z hzSphere
    have hz : ‖z - (r : ℂ)‖ = 1 / 2 := by
      simpa [mem_sphere, dist_eq_norm] using hzSphere
    have hlower : (1 / 2 : ℝ) ^ (R - 1) * D ≤
        ‖(cofactorPolynomial R r).eval z‖ := by
      simpa [D, mul_assoc] using
        cofactorPolynomial_norm_lower_on_half_circle hr hrR hz
    have hbase : 0 < (1 / 2 : ℝ) ^ (R - 1) * D := by positivity
    have hnormpos : 0 < ‖(cofactorPolynomial R r).eval z‖ := hbase.trans_le hlower
    rw [inverseCofactorPower, norm_pow, norm_inv]
    change ‖(cofactorPolynomial R r).eval z‖⁻¹ ^ T ≤ _
    rw [show (2 : ℝ) ^ ((R - 1) * T) / D ^ T =
        ((2 : ℝ) ^ (R - 1) / D) ^ T by rw [div_pow, pow_mul]]
    apply pow_le_pow_left₀ (by positivity)
    rw [inv_le_iff_one_le_mul₀' hnormpos]
    calc
      1 ≤ ((1 / 2 : ℝ) ^ (R - 1) * D) *
          ((2 : ℝ) ^ (R - 1) / D) := by
        have hhalf : (1 / 2 : ℝ) ^ (R - 1) * 2 ^ (R - 1) = 1 := by
          rw [← mul_pow]
          norm_num
        have hEq : ((1 / 2 : ℝ) ^ (R - 1) * D) *
            ((2 : ℝ) ^ (R - 1) / D) = 1 := by
          rw [div_eq_mul_inv]
          calc
            (1 / 2 : ℝ) ^ (R - 1) * D *
                (2 ^ (R - 1) * D⁻¹) =
              ((1 / 2 : ℝ) ^ (R - 1) * 2 ^ (R - 1)) *
                (D * D⁻¹) := by ring
            _ = 1 := by rw [hhalf]; simp [hD.ne']
        exact hEq.ge
      _ ≤ ‖(cofactorPolynomial R r).eval z‖ *
          ((2 : ℝ) ^ (R - 1) / D) := by gcongr
  have hcauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    j (by norm_num : (0 : ℝ) < 1 / 2)
    (inverseCofactorPower_diffContOnCl_halfBall (T := T) hr hrR) hC
  rw [inverseCofactorJet, norm_div, Complex.norm_natCast]
  have hjfac : (0 : ℝ) < j.factorial := by positivity
  rw [div_le_iff₀ hjfac]
  calc
    ‖iteratedDeriv j (inverseCofactorPower R T r) (r : ℂ)‖ ≤
        (j.factorial : ℝ) *
          ((2 : ℝ) ^ ((R - 1) * T) / D ^ T) /
            (1 / 2 : ℝ) ^ j := hcauchy
    _ = (j.factorial : ℝ) *
        ((2 : ℝ) ^ ((R - 1) * T + j) / D ^ T) := by
      have hinvhalf : ((1 / 2 : ℝ) ^ j)⁻¹ = 2 ^ j := by
        rw [← inv_pow]
        norm_num
      rw [div_eq_mul_inv, hinvhalf, pow_add]
      ring
    _ = (2 : ℝ) ^ ((R - 1) * T + j) /
        (((r - 1).factorial : ℝ) * (R - r).factorial) ^ T *
          (j.factorial : ℝ) := by
      dsimp [D]
      ring

/-- The target numerator and the inverse-Taylor denominator cancel
factorially in every explicit-basis summand.  The remaining exponent is
linear in `(R+l)T`; there is no `log R` factor. -/
theorem norm_basisTerm_eval_natCast_le
    {R T r m j l : ℕ} (hr : 1 ≤ r) (hrR : r ≤ R)
    (hRl : R < l) (hmj : m + j ≤ T) :
    ‖(basisTerm R T r m j).eval (l : ℂ)‖ ≤
      (2 : ℝ) ^ ((3 * R + l + 1) * T) := by
  let D : ℝ := ((r - 1).factorial : ℝ) * (R - r).factorial
  let d : ℝ := (l - r : ℕ)
  let A : ℝ := ‖(cofactorPolynomial R r).eval (l : ℂ)‖
  have hD : 0 < D := by dsimp [D]; positivity
  have hd : 1 ≤ d := by
    dsimp [d]
    exact_mod_cast (show 1 ≤ l - r by omega)
  have hcenter : ‖(l : ℂ) - (r : ℂ)‖ = d := by
    rw [show (l : ℂ) - (r : ℂ) = (((l - r : ℕ) : ℝ) : ℂ) by
      norm_num [Nat.cast_sub (by omega : r ≤ l)]]
    simp [d]
  have hnum := localCircle_numerator_upper hr hrR hRl
  rw [full_nodal_norm_eq_center_mul_cofactor_norm hr hrR, hcenter] at hnum
  have hnum' : A * d ≤ (2 : ℝ) ^ (2 * R + l) * D := by
    simpa [A, D, mul_comm, mul_left_comm, mul_assoc] using hnum
  have hAd : A ^ T * d ^ (m + j) ≤
      (2 : ℝ) ^ ((2 * R + l) * T) * D ^ T := by
    calc
      A ^ T * d ^ (m + j) ≤ A ^ T * d ^ T := by
        gcongr
      _ = (A * d) ^ T := by rw [mul_pow]
      _ ≤ ((2 : ℝ) ^ (2 * R + l) * D) ^ T := by
        exact pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) (by positivity)) hnum' T
      _ = (2 : ℝ) ^ ((2 * R + l) * T) * D ^ T := by
        rw [mul_pow, pow_mul]
  have hjet := norm_inverseCofactorJet_le (T := T) (j := j) hr hrR
  have hmain :
      (A ^ T * d ^ (m + j)) * ‖inverseCofactorJet R T r j‖ ≤
        (2 : ℝ) ^ ((2 * R + l) * T) *
          (2 : ℝ) ^ ((R - 1) * T + j) := by
    calc
      (A ^ T * d ^ (m + j)) * ‖inverseCofactorJet R T r j‖ ≤
          ((2 : ℝ) ^ ((2 * R + l) * T) * D ^ T) *
            ((2 : ℝ) ^ ((R - 1) * T + j) / D ^ T) := by
        exact mul_le_mul hAd hjet (norm_nonneg _)
          (mul_nonneg (by positivity) (pow_nonneg hD.le _))
      _ = (2 : ℝ) ^ ((2 * R + l) * T) *
          (2 : ℝ) ^ ((R - 1) * T + j) := by
        have hDp : D ^ T ≠ 0 := pow_ne_zero _ hD.ne'
        field_simp
  simp only [basisTerm, eval_mul, eval_pow, eval_sub, eval_X, eval_C,
    norm_mul, norm_pow, hcenter]
  change d ^ m * A ^ T * (‖inverseCofactorJet R T r j‖ * d ^ j) ≤ _
  calc
    d ^ m * A ^ T * (‖inverseCofactorJet R T r j‖ * d ^ j) =
        (A ^ T * d ^ (m + j)) * ‖inverseCofactorJet R T r j‖ := by
      rw [pow_add]
      ring
    _ ≤
        (2 : ℝ) ^ ((2 * R + l) * T) *
          (2 : ℝ) ^ ((R - 1) * T + j) := hmain
    _ = (2 : ℝ) ^ (((2 * R + l) * T) + ((R - 1) * T + j)) := by
      simp only [pow_add]
    _ ≤ (2 : ℝ) ^ ((3 * R + l + 1) * T) := by
      apply pow_le_pow_right₀ (by norm_num)
      have hRT : (R - 1) * T ≤ R * T :=
        Nat.mul_le_mul_right T (Nat.sub_le R 1)
      have hjT : j ≤ T := (Nat.le_add_left j m).trans hmj
      have heq : (3 * R + l + 1) * T =
          (2 * R + l) * T + (R * T + T) := by ring
      rw [heq]
      omega

theorem basisPolynomial_eq_sum_basisTerm (R T r m : ℕ) :
    basisPolynomial R T r m =
      ∑ j ∈ range (T - m), basisTerm R T r m j := by
  simp only [basisPolynomial, inverseCofactorTaylor, basisTerm,
    Finset.mul_sum]

/-- Each complete explicit Hermite basis polynomial has an
`exp(O((R+l)T))` evaluation bound. -/
theorem norm_basisPolynomial_eval_natCast_le
    {R T r m l : ℕ} (hr : 1 ≤ r) (hrR : r ≤ R)
    (hRl : R < l) (hm : m < T) :
    ‖(basisPolynomial R T r m).eval (l : ℂ)‖ ≤
      (2 : ℝ) ^ ((3 * R + l + 2) * T) := by
  rw [basisPolynomial_eq_sum_basisTerm, Polynomial.eval_finsetSum]
  calc
    ‖∑ j ∈ range (T - m), (basisTerm R T r m j).eval (l : ℂ)‖ ≤
        ∑ j ∈ range (T - m),
          ‖(basisTerm R T r m j).eval (l : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ _j ∈ range (T - m),
        (2 : ℝ) ^ ((3 * R + l + 1) * T) := by
      apply Finset.sum_le_sum
      intro j hj
      apply norm_basisTerm_eval_natCast_le hr hrR hRl
      have hj' := Finset.mem_range.mp hj
      omega
    _ = ((T - m : ℕ) : ℝ) *
        (2 : ℝ) ^ ((3 * R + l + 1) * T) := by simp
    _ ≤ (T : ℝ) * (2 : ℝ) ^ ((3 * R + l + 1) * T) := by
      gcongr
      exact_mod_cast Nat.sub_le T m
    _ ≤ (2 : ℝ) ^ T * (2 : ℝ) ^ ((3 * R + l + 1) * T) := by
      gcongr
      exact_mod_cast nat_le_two_pow_for_localCircle T
    _ = (2 : ℝ) ^ ((3 * R + l + 2) * T) := by
      rw [← pow_add]
      congr 1
      ring

/-! ### Exact jet reconstruction -/

/-- The normalized iterated derivatives of a product are the convolution of
the normalized iterated derivatives. -/
theorem normalized_iteratedDeriv_mul
    {f g : ℂ → ℂ} {x : ℂ} {n : ℕ}
    (hf : ContDiffAt ℂ n f x) (hg : ContDiffAt ℂ n g x) :
    iteratedDeriv n (fun z ↦ f z * g z) x / (n.factorial : ℂ) =
      ∑ i ∈ range (n + 1),
        (iteratedDeriv i f x / (i.factorial : ℂ)) *
          (iteratedDeriv (n - i) g x / ((n - i).factorial : ℂ)) := by
  change iteratedDeriv n (f * g) x / (n.factorial : ℂ) = _
  rw [iteratedDeriv_mul hf hg]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  have hin : i ≤ n := by simpa using hi
  have hfac : ((n.choose i : ℕ) : ℂ) * (i.factorial : ℂ) *
      ((n - i).factorial : ℂ) = (n.factorial : ℂ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hin
  have hi0 : (i.factorial : ℂ) ≠ 0 := by
    exact_mod_cast i.factorial_ne_zero
  have hni0 : ((n - i).factorial : ℂ) ≠ 0 := by
    exact_mod_cast (n - i).factorial_ne_zero
  have hn0 : (n.factorial : ℂ) ≠ 0 := by
    exact_mod_cast n.factorial_ne_zero
  field_simp
  rw [← hfac]
  ring

/-- The cofactor power and its analytic inverse have convolution equal to
the unit Taylor series at the omitted node. -/
theorem cofactor_inverseJet_convolution
    {R T r n : ℕ} (hr : 1 ≤ r) (hrR : r ≤ R) :
    ∑ i ∈ range (n + 1),
        (hasseDeriv i ((cofactorPolynomial R r) ^ T)).eval (r : ℂ) *
          inverseCofactorJet R T r (n - i) =
      if n = 0 then 1 else 0 := by
  let A : ℂ[X] := (cofactorPolynomial R r) ^ T
  have hA : ContDiffAt ℂ n (fun z : ℂ ↦ A.eval z) (r : ℂ) :=
    (Polynomial.differentiable A).contDiff.contDiffAt
  have hcof : (cofactorPolynomial R r).eval (r : ℂ) ≠ 0 :=
    cofactorPolynomial_eval_ne_zero_of_mem_closedBall hr hrR (by
      simp [mem_closedBall])
  have hA0 : A.eval (r : ℂ) ≠ 0 := by
    dsimp [A]
    simp only [eval_pow]
    exact pow_ne_zero _ hcof
  have hB : ContDiffAt ℂ n (inverseCofactorPower R T r) (r : ℂ) := by
    have heq : inverseCofactorPower R T r = fun z : ℂ ↦ (A.eval z)⁻¹ := by
      funext z
      simp [inverseCofactorPower, A, inv_pow]
    rw [heq]
    exact hA.inv hA0
  have hprod :
      Filter.EventuallyEq (nhds (r : ℂ))
        (fun z : ℂ ↦ A.eval z * inverseCofactorPower R T r z)
        (fun _ : ℂ ↦ 1) := by
    have hne := hA.continuousAt.eventually_ne hA0
    filter_upwards [hne] with z hz
    simp only [A, eval_pow, inverseCofactorPower, inv_pow]
    apply mul_inv_cancel₀
    simpa [A] using hz
  simp only [inverseCofactorJet]
  simp_rw [Erdos240.BakerLemma4Concrete.hasseDeriv_eval_eq_iteratedDeriv_div_factorial]
  change (∑ i ∈ range (n + 1),
    (iteratedDeriv i (fun z : ℂ ↦ A.eval z) (r : ℂ) /
      (i.factorial : ℂ)) *
      (iteratedDeriv (n - i) (inverseCofactorPower R T r) (r : ℂ) /
        ((n - i).factorial : ℂ))) = _
  rw [← normalized_iteratedDeriv_mul hA hB]
  have hderiv := Filter.EventuallyEq.iteratedDeriv_eq n hprod
  rw [hderiv, iteratedDeriv_const]
  split_ifs with hn
  · simp [hn]
  · simp [hn]

/-- Multiplication by a power of the local parameter shifts Hasse jets. -/
theorem hasseDeriv_centerPow_mul_eval
    (B : ℂ[X]) (r : ℂ) (m k : ℕ) :
    (hasseDeriv k ((X - C r) ^ m * B)).eval r =
      if m ≤ k then (hasseDeriv (k - m) B).eval r else 0 := by
  rw [← taylor_coeff]
  rw [taylor_mul, taylor_pow, map_sub, taylor_X, taylor_C]
  simp only [add_sub_cancel_right]
  rw [coeff_X_pow_mul']
  split_ifs
  · rw [taylor_coeff]
  · rfl

/-- The explicitly truncated inverse series has exactly its prescribed
normalized jets below the truncation order. -/
theorem inverseCofactorTaylor_hasse
    {R T r n k : ℕ} (hk : k < n) :
    (hasseDeriv k (inverseCofactorTaylor R T r n)).eval (r : ℂ) =
      inverseCofactorJet R T r k := by
  classical
  rw [inverseCofactorTaylor, map_sum, eval_finsetSum]
  refine (Finset.sum_eq_single k (fun j hj hne ↦ ?_) ?_).trans ?_
  · rw [Finset.mem_range] at hj
    rw [mul_comm, hasseDeriv_centerPow_mul_eval]
    by_cases hjk : j ≤ k
    · have hpos : 0 < k - j := by omega
      rw [if_pos hjk, hasseDeriv_C _ _ hpos, eval_zero]
    · rw [if_neg hjk]
  · intro hnot
    exact (hnot (Finset.mem_range.mpr hk)).elim
  · rw [mul_comm, hasseDeriv_centerPow_mul_eval, if_pos le_rfl,
      Nat.sub_self, hasseDeriv_zero, LinearMap.id_apply, eval_C]

/-- Multiplying the cofactor power by the truncated analytic inverse agrees
with `1` in every Hasse jet below the truncation order. -/
theorem cofactor_mul_inverseCofactorTaylor_hasse
    {R T r n k : ℕ} (hr : 1 ≤ r) (hrR : r ≤ R) (hk : k < n) :
    (hasseDeriv k
      ((cofactorPolynomial R r) ^ T * inverseCofactorTaylor R T r n)).eval
        (r : ℂ) = if k = 0 then 1 else 0 := by
  rw [hasseDeriv_mul, eval_finsetSum]
  simp only [eval_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  calc
    ∑ i ∈ range (k + 1),
        (hasseDeriv i ((cofactorPolynomial R r) ^ T)).eval (r : ℂ) *
          (hasseDeriv (k - i) (inverseCofactorTaylor R T r n)).eval (r : ℂ) =
      ∑ i ∈ range (k + 1),
        (hasseDeriv i ((cofactorPolynomial R r) ^ T)).eval (r : ℂ) *
          inverseCofactorJet R T r (k - i) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [inverseCofactorTaylor_hasse]
        omega
    _ = if k = 0 then 1 else 0 :=
      cofactor_inverseJet_convolution hr hrR

/-- At its own node, an explicit basis element has the corresponding single
unit Hasse jet. -/
theorem basisPolynomial_hasse_same
    {R T r m k : ℕ} (hr : 1 ≤ r) (hrR : r ≤ R)
    (hm : m < T) (hk : k < T) :
    (hasseDeriv k (basisPolynomial R T r m)).eval (r : ℂ) =
      if k = m then 1 else 0 := by
  rw [basisPolynomial, mul_assoc, hasseDeriv_centerPow_mul_eval]
  by_cases hmk : m ≤ k
  · rw [if_pos hmk,
      cofactor_mul_inverseCofactorTaylor_hasse hr hrR (by omega)]
    by_cases hkm : k = m
    · subst k
      simp
    · have hpos : 0 < k - m := by omega
      simp [hkm, hpos.ne']
  · rw [if_neg hmk]
    have hkm : k ≠ m := by omega
    simp [hkm]

/-- The factor belonging to any non-omitted node divides the cofactor. -/
theorem centerPow_dvd_cofactor_pow
    {R T r s : ℕ} (hs : 1 ≤ s) (hsR : s ≤ R) (hsr : s ≠ r) :
    (X - C (s : ℂ)) ^ T ∣ (cofactorPolynomial R r) ^ T := by
  apply pow_dvd_pow_of_dvd
  rw [cofactorPolynomial]
  have hmem : s - 1 ∈ range R := by simp; omega
  have hdvd := Finset.dvd_prod_of_mem
    (fun i ↦ if i + 1 = r then (1 : ℂ[X])
      else X - C (((i + 1 : ℕ) : ℂ))) hmem
  simpa [Nat.sub_add_cancel hs, hsr] using hdvd

/-- Divisibility by the `T`th power of a local parameter kills every Hasse
jet of order below `T`. -/
theorem hasseDeriv_eval_eq_zero_of_centerPow_dvd
    {P : ℂ[X]} {s : ℂ} {T k : ℕ}
    (hdiv : (X - C s) ^ T ∣ P) (hk : k < T) :
    (hasseDeriv k P).eval s = 0 := by
  rw [← taylor_coeff]
  apply X_pow_dvd_iff.mp (show X ^ T ∣ taylor s P by
    change X ^ T ∣ P.comp (X + C s)
    rw [← X_sub_C_pow_dvd_iff]
    exact hdiv) k hk

/-- At every other integral node, all basis jets below the multiplicity
vanish. -/
theorem basisPolynomial_hasse_other
    {R T r s m k : ℕ} (hs : 1 ≤ s) (hsR : s ≤ R)
    (hsr : s ≠ r) (hk : k < T) :
    (hasseDeriv k (basisPolynomial R T r m)).eval (s : ℂ) = 0 := by
  apply hasseDeriv_eval_eq_zero_of_centerPow_dvd _ hk
  obtain ⟨Q, hQ⟩ := centerPow_dvd_cofactor_pow
    (T := T) (r := r) hs hsR hsr
  refine ⟨(X - C (r : ℂ)) ^ m * Q * inverseCofactorTaylor R T r (T - m), ?_⟩
  rw [basisPolynomial, hQ]
  ring

/-- The omitted-factor polynomial is the product over the erased node. -/
theorem cofactorPolynomial_eq_prod_erase
    {R r : ℕ} (hr : 1 ≤ r) (hrR : r ≤ R) :
    cofactorPolynomial R r =
      ∏ i ∈ (range R).erase (r - 1),
        (X - C (((i + 1 : ℕ) : ℂ))) := by
  classical
  rw [cofactorPolynomial]
  have hmem : r - 1 ∈ range R := by simp; omega
  rw [← Finset.mul_prod_erase (range R)
    (fun i ↦ if i + 1 = r then (1 : ℂ[X])
      else X - C (((i + 1 : ℕ) : ℂ))) hmem]
  simp only [Nat.sub_add_cancel hr, if_pos, one_mul]
  apply Finset.prod_congr rfl
  intro i hi
  have hir : i + 1 ≠ r := by
    have hine := (Finset.mem_erase.mp hi).1
    omega
  simp [hir]

theorem cofactorPolynomial_monic
    {R r : ℕ} (hr : 1 ≤ r) (hrR : r ≤ R) :
    (cofactorPolynomial R r).Monic := by
  rw [cofactorPolynomial_eq_prod_erase hr hrR]
  apply monic_prod_of_monic
  intro i hi
  exact monic_X_sub_C _

/-- There are exactly `R - 1` factors in the cofactor. -/
theorem cofactorPolynomial_natDegree
    {R r : ℕ} (hr : 1 ≤ r) (hrR : r ≤ R) :
    (cofactorPolynomial R r).natDegree = R - 1 := by
  rw [cofactorPolynomial_eq_prod_erase hr hrR, natDegree_prod_of_monic]
  · simp only [natDegree_X_sub_C, Finset.sum_const_nat]
    rw [Finset.card_erase_of_mem]
    · simp
    · simp
      omega
  · intro i hi
    exact monic_X_sub_C _

/-- The inverse Taylor truncation has degree strictly below its positive
truncation order. -/
theorem inverseCofactorTaylor_natDegree_lt
    {R T r n : ℕ} (hn : 0 < n) :
    (inverseCofactorTaylor R T r n).natDegree < n := by
  rw [inverseCofactorTaylor]
  apply lt_of_le_of_lt
    (Polynomial.natDegree_sum_le_of_forall_le
      (n := n - 1) (range n) (fun j ↦
        C (inverseCofactorJet R T r j) * (X - C (r : ℂ)) ^ j) ?_)
  · omega
  · intro j hj
    have hjn := Finset.mem_range.mp hj
    exact (natDegree_C_mul_le _ _).trans (by
      rw [natDegree_pow, natDegree_X_sub_C]
      simp only [mul_one]
      exact Nat.le_pred_of_lt hjn)

/-- Every explicit basis element has degree strictly below the total number
`R*T` of Hermite conditions. -/
theorem basisPolynomial_natDegree_lt
    {R T r m : ℕ} (hr : 1 ≤ r) (hrR : r ≤ R) (hm : m < T) :
    (basisPolynomial R T r m).natDegree < R * T := by
  have hcof : ((cofactorPolynomial R r) ^ T).natDegree = (R - 1) * T := by
    rw [natDegree_pow, cofactorPolynomial_natDegree hr hrR]
    exact Nat.mul_comm _ _
  have hinv : (inverseCofactorTaylor R T r (T - m)).natDegree ≤ T - m - 1 :=
    Nat.le_pred_of_lt (inverseCofactorTaylor_natDegree_lt (by omega))
  rw [basisPolynomial]
  calc
    (((X - C (r : ℂ)) ^ m * (cofactorPolynomial R r) ^ T) *
        inverseCofactorTaylor R T r (T - m)).natDegree ≤
      ((X - C (r : ℂ)) ^ m).natDegree +
        ((cofactorPolynomial R r) ^ T).natDegree +
          (inverseCofactorTaylor R T r (T - m)).natDegree := by
        have houter :
            (((X - C (r : ℂ)) ^ m * (cofactorPolynomial R r) ^ T) *
              inverseCofactorTaylor R T r (T - m)).natDegree ≤
              (((X - C (r : ℂ)) ^ m *
                (cofactorPolynomial R r) ^ T)).natDegree +
                (inverseCofactorTaylor R T r (T - m)).natDegree :=
          natDegree_mul_le
        have hinner :
            (((X - C (r : ℂ)) ^ m *
              (cofactorPolynomial R r) ^ T)).natDegree ≤
              ((X - C (r : ℂ)) ^ m).natDegree +
                ((cofactorPolynomial R r) ^ T).natDegree :=
          natDegree_mul_le
        omega
    _ ≤ m + (R - 1) * T + (T - m - 1) := by
      rw [natDegree_pow, natDegree_X_sub_C, mul_one, hcof]
      omega
    _ < R * T := by
      have hR : 1 ≤ R := hr.trans hrR
      rw [show R * T = (R - 1) * T + T by
        have hR' : R = (R - 1) + 1 := by omega
        calc
          R * T = ((R - 1) + 1) * T := congrArg (fun x : ℕ ↦ x * T) hR'
          _ = (R - 1) * T + T := by rw [add_mul, one_mul]]
      omega

/-- The polynomial obtained by summing the explicit basis against all Hasse
jets on `1, ..., R`. -/
def explicitInterpolant (R T : ℕ) (P : ℂ[X]) : ℂ[X] :=
  ∑ r : Fin R, ∑ m : Fin T,
    (hasseDeriv m.1 P).eval ((r.1 + 1 : ℕ) : ℂ) •
      basisPolynomial R T (r.1 + 1) m.1

/-- The explicit interpolant reproduces every one of its prescribed Hasse
jets. -/
theorem explicitInterpolant_hasse
    {R T : ℕ} (P : ℂ[X]) (r : Fin R) (k : Fin T) :
    (hasseDeriv k.1 (explicitInterpolant R T P)).eval
        ((r.1 + 1 : ℕ) : ℂ) =
      (hasseDeriv k.1 P).eval ((r.1 + 1 : ℕ) : ℂ) := by
  classical
  rw [explicitInterpolant, map_sum, eval_finsetSum]
  simp only [map_sum, map_smul, eval_finsetSum, eval_smul, smul_eq_mul]
  refine (Finset.sum_eq_single r (fun t ht htr ↦ ?_) ?_).trans ?_
  · apply Finset.sum_eq_zero
    intro m hm
    rw [basisPolynomial_hasse_other (by omega) (by omega) (by
      intro heq
      apply htr
      have hnat : r.1 + 1 = t.1 + 1 := by exact_mod_cast heq
      exact Fin.ext (by omega)) k.2, mul_zero]
  · intro hnot
    exact (hnot (Finset.mem_univ r)).elim
  · refine (Finset.sum_eq_single k (fun m hm hmk ↦ ?_) ?_).trans ?_
    · rw [basisPolynomial_hasse_same (by omega) (by omega) m.2 k.2,
        if_neg (fun h ↦ hmk (Fin.ext h.symm)), mul_zero]
    · intro hnot
      exact (hnot (Finset.mem_univ k)).elim
    · rw [basisPolynomial_hasse_same (by omega) (by omega) k.2 k.2,
        if_pos rfl, mul_one]

theorem mem_degreeLT_of_natDegree_lt
    {P : ℂ[X]} {n : ℕ} (hP : P.natDegree < n) :
    P ∈ Polynomial.degreeLT ℂ n := by
  rw [Polynomial.mem_degreeLT]
  by_cases hzero : P = 0
  · simp [hzero]
  · rw [degree_eq_natDegree hzero]
    exact_mod_cast hP

theorem explicitInterpolant_mem_degreeLT
    {R T : ℕ} (P : ℂ[X]) :
    explicitInterpolant R T P ∈ Polynomial.degreeLT ℂ (R * T) := by
  classical
  rw [explicitInterpolant]
  apply Submodule.sum_mem
  intro r hr
  apply Submodule.sum_mem
  intro m hm
  apply Submodule.smul_mem
  exact mem_degreeLT_of_natDegree_lt
    (basisPolynomial_natDegree_lt (by omega) (by omega) m.2)

/-- Exact explicit Hermite reconstruction for every polynomial of degree
below the total number of conditions. -/
theorem explicitHermite_reconstruction
    {R T : ℕ} {P : ℂ[X]} (hP : P.natDegree < R * T) :
    P = explicitInterpolant R T P := by
  have hRT : 0 < R * T := (Nat.zero_le P.natDegree).trans_lt hP
  let Psub : Polynomial.degreeLT ℂ (R * T) :=
    ⟨P, mem_degreeLT_of_natDegree_lt hP⟩
  let Qsub : Polynomial.degreeLT ℂ (R * T) :=
    ⟨explicitInterpolant R T P, explicitInterpolant_mem_degreeLT P⟩
  have hmap :
      Erdos240.BakerLemma4Concrete.integralHasseJetMap R T Psub =
        Erdos240.BakerLemma4Concrete.integralHasseJetMap R T Qsub := by
    funext ik
    rcases ik with ⟨r, k⟩
    simpa [Erdos240.BakerLemma4Concrete.integralHasseJetMap, Psub, Qsub] using
      (explicitInterpolant_hasse P r k).symm
  have hsub : Psub = Qsub :=
    Erdos240.BakerLemma4Concrete.integralHasseJetMap_injective R T hmap
  exact congrArg Subtype.val hsub

/-! ### Rational targets -/

/-- If `d ≥ 1/q`, reducing the power of `d` from `T` to `s` costs at
most `q^T`.  This is the elementary cancellation used at a nonintegral
rational target. -/
theorem pow_mul_pow_le_q_pow_mul_pow
    {A d q F : ℝ} {s T : ℕ}
    (hA : 0 ≤ A) (hd0 : 0 ≤ d) (hq : 1 ≤ q)
    (hd : 1 / q ≤ d) (hAF : A * d ≤ F) (hs : s ≤ T) :
    A ^ T * d ^ s ≤ q ^ T * F ^ T := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hqd : 1 ≤ q * d := by
    calc
      1 = q * (1 / q) := by field_simp
      _ ≤ q * d := by gcongr
  let u := T - s
  have hus : u + s = T := by dsimp [u]; omega
  have hnonneg : 0 ≤ A ^ T * d ^ s :=
    mul_nonneg (pow_nonneg hA _) (pow_nonneg hd0 _)
  have hF : 0 ≤ F :=
    (mul_nonneg hA hd0).trans hAF
  calc
    A ^ T * d ^ s ≤ (q * d) ^ u * (A ^ T * d ^ s) :=
      le_mul_of_one_le_left hnonneg (one_le_pow₀ hqd)
    _ = q ^ u * (A ^ T * (d ^ u * d ^ s)) := by
      rw [mul_pow]
      ring
    _ = q ^ u * (A ^ T * d ^ T) := by
      rw [← pow_add, hus]
    _ = q ^ u * (A * d) ^ T := by rw [mul_pow]
    _ ≤ q ^ u * F ^ T := by
      gcongr
    _ ≤ q ^ T * F ^ T :=
      mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ hq (Nat.sub_le T s)) (pow_nonneg hF _)

/-- A single summand of the explicit basis at a rational target in `[0,R]`
has only the expected `q^T exp(O(RT))` loss. -/
theorem norm_basisTerm_eval_ratCast_le
    {R T r m j l q : ℕ} (hq : 0 < q) (hnmid : ¬ q ∣ l)
    (hlR : l ≤ q * R) (hr : 1 ≤ r) (hrR : r ≤ R)
    (hmj : m + j ≤ T) :
    ‖(basisTerm R T r m j).eval ((l : ℂ) / (q : ℂ))‖ ≤
      (q : ℝ) ^ T * (2 : ℝ) ^ ((3 * R + 1) * T) := by
  let x : ℂ := (l : ℂ) / (q : ℂ)
  let D : ℝ := ((r - 1).factorial : ℝ) * (R - r).factorial
  let d : ℝ := ‖x - (r : ℂ)‖
  let A : ℝ := ‖(cofactorPolynomial R r).eval x‖
  have hD : 0 < D := by dsimp [D]; positivity
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hd : 1 / (q : ℝ) ≤ d := by
    dsimp [d, x]
    exact Erdos240.BakerRationalExtrapolation.one_div_le_norm_rational_sub_nat
      hq hnmid
  have hfull : d * A ≤ (R.factorial : ℝ) := by
    have h :=
      Erdos240.InterpolationProducts.norm_integralNodalProduct_ratCast_le_factorial_pow
        (l := l) (q := q) (R := R) (S := 1) hq hlR
    have hcast : ((((l : ℚ) / (q : ℚ) : ℚ)) : ℂ) = x := by
      dsimp [x]
      norm_num
    rw [Erdos240.InterpolationProducts.integralNodalProduct, hcast,
      norm_prod] at h
    simp only [pow_one] at h
    rw [full_nodal_norm_eq_center_mul_cofactor_norm hr hrR] at h
    simpa [d, A, mul_comm] using h
  have hAd : A ^ T * d ^ (m + j) ≤
      (q : ℝ) ^ T * (R.factorial : ℝ) ^ T := by
    apply pow_mul_pow_le_q_pow_mul_pow
      (A := A) (d := d) (q := (q : ℝ)) (F := (R.factorial : ℝ))
      (norm_nonneg _) (norm_nonneg _) hqR hd
    · simpa [mul_comm] using hfull
    · exact hmj
  have hfac := factorial_le_localCircle_factor_times_pow hr hrR
  have hfacpow : (R.factorial : ℝ) ^ T ≤
      (2 : ℝ) ^ ((2 * R) * T) * D ^ T := by
    calc
      (R.factorial : ℝ) ^ T ≤
          ((2 : ℝ) ^ (2 * R) * D) ^ T := by
        apply pow_le_pow_left₀ (by positivity)
        simpa [D, mul_assoc] using hfac
      _ = (2 : ℝ) ^ ((2 * R) * T) * D ^ T := by
        rw [mul_pow, ← pow_mul]
  have hjet := norm_inverseCofactorJet_le (T := T) (j := j) hr hrR
  have hmain :
      (A ^ T * d ^ (m + j)) * ‖inverseCofactorJet R T r j‖ ≤
        (q : ℝ) ^ T *
          ((2 : ℝ) ^ ((2 * R) * T) *
            (2 : ℝ) ^ ((R - 1) * T + j)) := by
    calc
      (A ^ T * d ^ (m + j)) * ‖inverseCofactorJet R T r j‖ ≤
          ((q : ℝ) ^ T * (R.factorial : ℝ) ^ T) *
            ((2 : ℝ) ^ ((R - 1) * T + j) / D ^ T) := by
        exact mul_le_mul hAd hjet (norm_nonneg _)
          (mul_nonneg (pow_nonneg (by positivity) _)
            (pow_nonneg (by positivity) _))
      _ ≤ ((q : ℝ) ^ T *
            ((2 : ℝ) ^ ((2 * R) * T) * D ^ T)) *
          ((2 : ℝ) ^ ((R - 1) * T + j) / D ^ T) := by
        gcongr
      _ = (q : ℝ) ^ T *
          ((2 : ℝ) ^ ((2 * R) * T) *
            (2 : ℝ) ^ ((R - 1) * T + j)) := by
        have hDp : D ^ T ≠ 0 := pow_ne_zero _ hD.ne'
        field_simp
  simp only [basisTerm, eval_mul, eval_pow, eval_sub, eval_X, eval_C,
    norm_mul, norm_pow]
  change d ^ m * A ^ T * (‖inverseCofactorJet R T r j‖ * d ^ j) ≤ _
  calc
    d ^ m * A ^ T * (‖inverseCofactorJet R T r j‖ * d ^ j) =
        (A ^ T * d ^ (m + j)) * ‖inverseCofactorJet R T r j‖ := by
      rw [pow_add]
      ring
    _ ≤ (q : ℝ) ^ T *
        ((2 : ℝ) ^ ((2 * R) * T) *
          (2 : ℝ) ^ ((R - 1) * T + j)) := hmain
    _ ≤ (q : ℝ) ^ T * (2 : ℝ) ^ ((3 * R + 1) * T) := by
      gcongr
      rw [← pow_add]
      apply pow_le_pow_right₀ (by norm_num)
      have hRT : (R - 1) * T ≤ R * T :=
        Nat.mul_le_mul_right T (Nat.sub_le R 1)
      have hjT : j ≤ T := (Nat.le_add_left j m).trans hmj
      have heq : (3 * R + 1) * T =
          (2 * R) * T + (R * T + T) := by ring
      rw [heq]
      omega

/-- A complete explicit basis polynomial at a nonintegral rational target. -/
theorem norm_basisPolynomial_eval_ratCast_le
    {R T r m l q : ℕ} (hq : 0 < q) (hnmid : ¬ q ∣ l)
    (hlR : l ≤ q * R) (hr : 1 ≤ r) (hrR : r ≤ R)
    (hm : m < T) :
    ‖(basisPolynomial R T r m).eval ((l : ℂ) / (q : ℂ))‖ ≤
      (q : ℝ) ^ T * (2 : ℝ) ^ ((3 * R + 2) * T) := by
  rw [basisPolynomial_eq_sum_basisTerm, Polynomial.eval_finsetSum]
  calc
    ‖∑ j ∈ range (T - m),
        (basisTerm R T r m j).eval ((l : ℂ) / (q : ℂ))‖ ≤
      ∑ j ∈ range (T - m),
        ‖(basisTerm R T r m j).eval ((l : ℂ) / (q : ℂ))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _j ∈ range (T - m),
        ((q : ℝ) ^ T * (2 : ℝ) ^ ((3 * R + 1) * T)) := by
      apply Finset.sum_le_sum
      intro j hj
      apply norm_basisTerm_eval_ratCast_le hq hnmid hlR hr hrR
      have hj' := Finset.mem_range.mp hj
      omega
    _ = ((T - m : ℕ) : ℝ) *
        ((q : ℝ) ^ T * (2 : ℝ) ^ ((3 * R + 1) * T)) := by simp
    _ ≤ (T : ℝ) *
        ((q : ℝ) ^ T * (2 : ℝ) ^ ((3 * R + 1) * T)) := by
      gcongr
      exact_mod_cast Nat.sub_le T m
    _ ≤ (2 : ℝ) ^ T *
        ((q : ℝ) ^ T * (2 : ℝ) ^ ((3 * R + 1) * T)) := by
      gcongr
      exact_mod_cast nat_le_two_pow_for_localCircle T
    _ = (q : ℝ) ^ T * (2 : ℝ) ^ ((3 * R + 2) * T) := by
      rw [show (3 * R + 2) * T = T + (3 * R + 1) * T by ring,
        pow_add]
      ring

/-- Direct evaluation of a degree-`< R*T` polynomial at a nonintegral
rational point from uniformly bounded integral Hasse jets.  The loss is
`q^T exp(O(RT))`, with no `R*T*log R` term. -/
theorem norm_eval_ratCast_le_of_hasse
    {R T l q : ℕ} {P : ℂ[X]} {delta : ℝ}
    (hq : 0 < q) (hnmid : ¬ q ∣ l) (hlR : l ≤ q * R)
    (hP : P.natDegree < R * T) (hdelta : 0 ≤ delta)
    (hjet : ∀ r : Fin R, ∀ m : Fin T,
      ‖(hasseDeriv m.1 P).eval ((r.1 + 1 : ℕ) : ℂ)‖ ≤ delta) :
    ‖P.eval ((l : ℂ) / (q : ℂ))‖ ≤
      (q : ℝ) ^ T * (2 : ℝ) ^ ((4 * R + 3) * T) * delta := by
  have hRT : 0 < R * T := (Nat.zero_le P.natDegree).trans_lt hP
  have hR : 0 < R := Nat.pos_of_ne_zero (fun hzero ↦ by
    subst R
    simp at hRT)
  have hT : 0 < T := Nat.pos_of_ne_zero (fun hzero ↦ by
    subst T
    simp at hRT)
  rw [explicitHermite_reconstruction hP, explicitInterpolant,
    Polynomial.eval_finsetSum]
  calc
    ‖∑ r : Fin R,
        (∑ m : Fin T,
          (hasseDeriv m.1 P).eval ((r.1 + 1 : ℕ) : ℂ) •
            basisPolynomial R T (r.1 + 1) m.1).eval
              ((l : ℂ) / (q : ℂ))‖ ≤
      ∑ r : Fin R,
        ‖(∑ m : Fin T,
          (hasseDeriv m.1 P).eval ((r.1 + 1 : ℕ) : ℂ) •
            basisPolynomial R T (r.1 + 1) m.1).eval
              ((l : ℂ) / (q : ℂ))‖ := norm_sum_le _ _
    _ ≤ ∑ _r : Fin R,
        (T : ℝ) *
          ((q : ℝ) ^ T * (2 : ℝ) ^ ((3 * R + 2) * T) * delta) := by
      apply Finset.sum_le_sum
      intro r hrmem
      rw [Polynomial.eval_finsetSum]
      calc
        ‖∑ m : Fin T,
            ((hasseDeriv m.1 P).eval ((r.1 + 1 : ℕ) : ℂ) •
              basisPolynomial R T (r.1 + 1) m.1).eval
                ((l : ℂ) / (q : ℂ))‖ ≤
          ∑ m : Fin T,
            ‖((hasseDeriv m.1 P).eval ((r.1 + 1 : ℕ) : ℂ) •
              basisPolynomial R T (r.1 + 1) m.1).eval
                ((l : ℂ) / (q : ℂ))‖ := norm_sum_le _ _
        _ ≤ ∑ _m : Fin T,
            ((q : ℝ) ^ T * (2 : ℝ) ^ ((3 * R + 2) * T) * delta) := by
          apply Finset.sum_le_sum
          intro m hmmem
          simp only [eval_smul, norm_smul]
          calc
            ‖(hasseDeriv m.1 P).eval ((r.1 + 1 : ℕ) : ℂ)‖ *
                ‖(basisPolynomial R T (r.1 + 1) m.1).eval
                  ((l : ℂ) / (q : ℂ))‖ ≤
              delta * ((q : ℝ) ^ T *
                (2 : ℝ) ^ ((3 * R + 2) * T)) := by
              gcongr
              · exact hjet r m
              · exact norm_basisPolynomial_eval_ratCast_le hq hnmid hlR
                  (Nat.succ_le_succ (Nat.zero_le r.1))
                  (Nat.succ_le_iff.mpr r.2) m.2
            _ = (q : ℝ) ^ T *
                (2 : ℝ) ^ ((3 * R + 2) * T) * delta := by ring
        _ = (T : ℝ) *
            ((q : ℝ) ^ T * (2 : ℝ) ^ ((3 * R + 2) * T) * delta) := by
          simp
    _ = (R : ℝ) * (T : ℝ) *
        ((q : ℝ) ^ T * (2 : ℝ) ^ ((3 * R + 2) * T) * delta) := by
      simp
      ring
    _ ≤ ((2 : ℝ) ^ R * (2 : ℝ) ^ T) *
        ((q : ℝ) ^ T * (2 : ℝ) ^ ((3 * R + 2) * T) * delta) := by
      gcongr
      · exact_mod_cast nat_le_two_pow_for_localCircle R
      · exact_mod_cast nat_le_two_pow_for_localCircle T
    _ ≤ (q : ℝ) ^ T * (2 : ℝ) ^ ((4 * R + 3) * T) * delta := by
      have hexp : R + T ≤ (R + 1) * T := by
        have hRT' : R ≤ R * T := by
          simpa only [mul_one] using
            Nat.mul_le_mul_left R (show 1 ≤ T by omega)
        calc
          R + T ≤ R * T + T := Nat.add_le_add_right hRT' T
          _ = (R + 1) * T := by ring
      rw [← pow_add]
      have hp : (2 : ℝ) ^ (R + T) ≤ (2 : ℝ) ^ ((R + 1) * T) :=
        pow_le_pow_right₀ (by norm_num) hexp
      have heq : (4 * R + 3) * T =
          (R + 1) * T + (3 * R + 2) * T := by ring
      calc
        (2 : ℝ) ^ (R + T) *
            ((q : ℝ) ^ T * (2 : ℝ) ^ ((3 * R + 2) * T) * delta) ≤
          (2 : ℝ) ^ ((R + 1) * T) *
            ((q : ℝ) ^ T * (2 : ℝ) ^ ((3 * R + 2) * T) * delta) := by
              exact mul_le_mul_of_nonneg_right hp (by positivity)
        _ = (q : ℝ) ^ T * (2 : ℝ) ^ ((4 * R + 3) * T) * delta := by
          rw [heq, pow_add]
          ring

#print axioms explicitHermite_reconstruction
#print axioms norm_basisPolynomial_eval_natCast_le
#print axioms norm_eval_ratCast_le_of_hasse

end Erdos240.ExplicitHermiteBasis
