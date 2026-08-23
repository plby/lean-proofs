/- leanprover/lean4:v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos240.BakerLemma4LocalResidues
import ErdosProblems.Erdos240.BakerLemma4SharpOuterProduct

/-!
# The outer-contour term in concrete Baker Lemma 4

This file combines the exact local-residue identity with the cancellation of
the Hermite polynomial on the outer circle.  Consequently the outer term
contains only the original entire function.  This is the quantitative form
of equation (9) needed in the source induction.
-/

open scoped BigOperators
open Complex Finset Function Metric Polynomial Set

noncomputable section

namespace Erdos240.BakerLemma4Concrete

open Erdos240.InterpolationProducts

/-! ## Arbitrary complex targets

The rational extrapolation step uses `x = l / q`, rather than a natural
target.  The algebraic principal-part decomposition in the local-residue
module does not use integrality of the target, so we record its complex
version here. -/

theorem exists_localPrincipal_decomposition_complex
    {R S : ℕ} (hR : 1 ≤ R) (hS : 1 ≤ S) (x : ℂ)
    (P : ℂ[X]) (hPdeg : P ∈ Polynomial.degreeLT ℂ (R * S)) :
    ∃ a : IntegralJetIndex R S → ℂ,
      C ((localNodalPolynomial R S).eval x) * P =
        C (P.eval x) * localNodalPolynomial R S +
          (X - C x) *
            ∑ rm, a rm • localPrincipalPolynomial R S rm := by
  let N : ℂ[X] :=
    C ((localNodalPolynomial R S).eval x) * P -
      C (P.eval x) * localNodalPolynomial R S
  have hNeval : N.eval x = 0 := by
    dsimp only [N]
    rw [eval_sub, eval_mul, eval_C, eval_mul, eval_C]
    ring
  have hdvd : X - C x ∣ N := by
    rw [dvd_iff_isRoot, IsRoot.def]
    exact hNeval
  obtain ⟨H, hH⟩ := hdvd
  have hNdeg : N.natDegree ≤ R * S := by
    dsimp only [N]
    apply (natDegree_sub_le _ _).trans
    apply max_le
    · exact (natDegree_C_mul_le _ P).trans (Nat.le_of_lt (by
        by_cases hP0 : P = 0
        · subst P
          simpa using Nat.mul_pos hR hS
        · exact (natDegree_lt_iff_degree_lt hP0).mpr
            (Polynomial.mem_degreeLT.mp hPdeg)))
    · exact (natDegree_C_mul_le _ _).trans_eq
        (localNodalPolynomial_natDegree R S)
  have hHdeg : H ∈ Polynomial.degreeLT ℂ (R * S) := by
    rw [Polynomial.mem_degreeLT]
    by_cases hH0 : H = 0
    · subst H
      simp
      exact WithBot.bot_lt_coe _
    · have hlinear : X - C x ≠ 0 := (monic_X_sub_C _).ne_zero
      have hNat : 1 + H.natDegree = N.natDegree := by
        rw [hH, natDegree_mul hlinear hH0, natDegree_X_sub_C]
      rw [degree_eq_natDegree hH0]
      exact_mod_cast (show H.natDegree < R * S by omega)
  let Hsub : Polynomial.degreeLT ℂ (R * S) := ⟨H, hHdeg⟩
  let a : IntegralJetIndex R S → ℂ := (localPrincipalEquiv R S).symm Hsub
  refine ⟨a, ?_⟩
  have ha : H = ∑ rm, a rm • localPrincipalPolynomial R S rm := by
    change Hsub.1 = ((localPrincipalMap R S) a).1
    rw [show localPrincipalMap R S =
      (localPrincipalEquiv R S).toLinearMap by rfl]
    simp [a]
  dsimp only [N] at hH
  rw [← ha]
  simpa [add_comm] using (sub_eq_iff_eq_add).mp hH

theorem eval_add_sum_last_eq_zero_of_localPrincipal_decomposition_complex
    {R S : ℕ} (hR : 1 ≤ R) (hS : 1 ≤ S) (x : ℂ)
    (P : ℂ[X]) (hPdeg : P ∈ Polynomial.degreeLT ℂ (R * S))
    (a : IntegralJetIndex R S → ℂ)
    (hdecomp :
      C ((localNodalPolynomial R S).eval x) * P =
        C (P.eval x) * localNodalPolynomial R S +
          (X - C x) *
            ∑ rm, a rm • localPrincipalPolynomial R S rm) :
    P.eval x + ∑ r : Fin R, a ⟨r, ⟨S - 1, by omega⟩⟩ = 0 := by
  have hcoeff := congrArg (fun Q : ℂ[X] => Q.coeff (R * S)) hdecomp
  have hPcoeff : P.coeff (R * S) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    by_cases hP0 : P = 0
    · subst P
      simpa using Nat.mul_pos hR hS
    · exact (natDegree_lt_iff_degree_lt hP0).mpr
        (Polynomial.mem_degreeLT.mp hPdeg)
  have hFcoeff : (localNodalPolynomial R S).coeff (R * S) = 1 := by
    rw [← (localNodalPolynomial_monic R S).coeff_natDegree,
      localNodalPolynomial_natDegree]
  have hQdeg : (∑ rm, a rm • localPrincipalPolynomial R S rm).natDegree <
      R * S := by
    let Qsub : Polynomial.degreeLT ℂ (R * S) := (localPrincipalMap R S) a
    by_cases hQ0 : Qsub.1 = 0
    · have hsum0 : ∑ rm, a rm • localPrincipalPolynomial R S rm = 0 := hQ0
      rw [hsum0, natDegree_zero]
      exact Nat.mul_pos hR hS
    · exact (natDegree_lt_iff_degree_lt hQ0).mpr
        (Polynomial.mem_degreeLT.mp Qsub.2)
  have hQtop : (∑ rm, a rm • localPrincipalPolynomial R S rm).coeff
      (R * S - 1) = ∑ r : Fin R, a ⟨r, ⟨S - 1, by omega⟩⟩ := by
    rw [Fintype.sum_sigma]
    change (Polynomial.lcoeff ℂ (R * S - 1))
        (∑ r : Fin R, ∑ m : Fin S,
          a ⟨r, m⟩ • localPrincipalPolynomial R S ⟨r, m⟩) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro r _
    rw [map_sum]
    simp only [Polynomial.lcoeff_apply, coeff_smul,
      localPrincipalPolynomial_coeff_top hS, smul_eq_mul, mul_ite, mul_one,
      mul_zero]
    let last : Fin S := ⟨S - 1, by omega⟩
    calc
      (∑ m : Fin S, if m.1 = S - 1 then a ⟨r, m⟩ else 0) =
          (if last.1 = S - 1 then a ⟨r, last⟩ else 0) := by
        apply Fintype.sum_eq_single last
        intro m hm
        rw [if_neg]
        intro heq
        exact hm (Fin.ext heq)
      _ = a ⟨r, ⟨S - 1, by omega⟩⟩ := by simp [last]
  have hQabove : (∑ rm, a rm • localPrincipalPolynomial R S rm).coeff
      (R * S) = 0 := coeff_eq_zero_of_natDegree_lt hQdeg
  have hmulcoeff : ((X - C x) *
      ∑ rm, a rm • localPrincipalPolynomial R S rm).coeff (R * S) =
        (∑ rm, a rm • localPrincipalPolynomial R S rm).coeff
          (R * S - 1) := by
    rw [sub_mul, coeff_sub, show R * S = (R * S - 1) + 1 by omega,
      coeff_X_mul, coeff_C_mul,
      show R * S - 1 + 1 = R * S by omega, hQabove]
    ring
  simp only [coeff_C_mul, coeff_add, hPcoeff, hFcoeff, hmulcoeff, hQtop]
    at hcoeff
  simpa using hcoeff.symm

theorem exists_localPrincipal_decomposition_with_last_sum_complex
    {R S : ℕ} (hR : 1 ≤ R) (hS : 1 ≤ S) (x : ℂ)
    (P : ℂ[X]) (hPdeg : P ∈ Polynomial.degreeLT ℂ (R * S)) :
    ∃ a : IntegralJetIndex R S → ℂ,
      C ((localNodalPolynomial R S).eval x) * P =
          C (P.eval x) * localNodalPolynomial R S +
            (X - C x) *
              ∑ rm, a rm • localPrincipalPolynomial R S rm ∧
        P.eval x + ∑ r : Fin R, a ⟨r, ⟨S - 1, by omega⟩⟩ = 0 := by
  obtain ⟨a, ha⟩ :=
    exists_localPrincipal_decomposition_complex hR hS x P hPdeg
  exact ⟨a, ha,
    eval_add_sum_last_eq_zero_of_localPrincipal_decomposition_complex
      hR hS x P hPdeg a ha⟩

/-- The outer polynomial kernel has zero normalized integral for every
complex target inside the contour.  In particular this applies to the
nonintegral rational target `x = l / q` in source Lemma 5. -/
theorem normalized_outerCircleIntegral_localPolynomialKernel_complex_eq_zero
    {R S : ℕ} (hR : 1 ≤ R) (hS : 1 ≤ S) (x : ℂ)
    (P : ℂ[X]) (hPdeg : P ∈ Polynomial.degreeLT ℂ (R * S))
    {c : ℂ} {rho : ℝ} (hxball : x ∈ Metric.ball c rho)
    (hnodes : ∀ r : Fin R,
      (((r.1 + 1 : ℕ) : ℂ)) ∈ Metric.ball c rho) :
    (2 * ((Real.pi : ℝ) : ℂ) * I)⁻¹ *
        (∮ z in C(c, rho), localPolynomialKernel R S x P z) = 0 := by
  obtain ⟨a, hdecomp, hlast⟩ :=
    exists_localPrincipal_decomposition_with_last_sum_complex
      hR hS x P hPdeg
  have hrho : 0 ≤ rho := (dist_nonneg.trans_lt hxball).le
  have hcircle : ∀ z ∈ Metric.sphere c rho,
      localPolynomialKernel R S x P z =
        P.eval x / (z - x) +
          ∑ rm, a rm /
            (z - ((rm.1.1 + 1 : ℕ) : ℂ)) ^ (S - rm.2.1) := by
    intro z hz
    apply localPolynomialKernel_eq_partialFractions hR hS P a hdecomp
    · exact Metric.sphere_disjoint_ball.ne_of_mem hz hxball
    · intro i
      exact Metric.sphere_disjoint_ball.ne_of_mem hz (hnodes i)
  have htarget : CircleIntegrable
      (fun z : ℂ => P.eval x / (z - x)) c rho := by
    apply ContinuousOn.circleIntegrable hrho
    exact continuousOn_const.div (continuousOn_id.sub continuousOn_const)
      (fun z hz hzero =>
        Metric.sphere_disjoint_ball.ne_of_mem hz hxball
          (sub_eq_zero.mp hzero))
  have hterm (rm : IntegralJetIndex R S) : CircleIntegrable
      (fun z : ℂ => a rm /
        (z - ((rm.1.1 + 1 : ℕ) : ℂ)) ^ (S - rm.2.1)) c rho := by
    apply ContinuousOn.circleIntegrable hrho
    exact continuousOn_const.div
      ((continuousOn_id.sub continuousOn_const).pow (S - rm.2.1))
      (fun z hz hzero =>
        Metric.sphere_disjoint_ball.ne_of_mem hz (hnodes rm.1)
          (sub_eq_zero.mp (eq_zero_of_pow_eq_zero hzero)))
  have hterms : CircleIntegrable
      (fun z : ℂ => ∑ rm, a rm /
        (z - ((rm.1.1 + 1 : ℕ) : ℂ)) ^ (S - rm.2.1)) c rho := by
    have hfun : (fun z : ℂ => ∑ rm, a rm /
        (z - ((rm.1.1 + 1 : ℕ) : ℂ)) ^ (S - rm.2.1)) =
        ∑ rm, fun z : ℂ => a rm /
          (z - ((rm.1.1 + 1 : ℕ) : ℂ)) ^ (S - rm.2.1) := by
      funext z
      simp
    rw [hfun]
    exact CircleIntegrable.sum Finset.univ (fun rm _ => hterm rm)
  rw [circleIntegral.integral_congr hrho hcircle,
    circleIntegral.integral_add htarget hterms,
    mul_add, circleIntegral.integral_fun_sum (fun rm _ => hterm rm), mul_sum]
  have htargetIntegral :
      (2 * ((Real.pi : ℝ) : ℂ) * I)⁻¹ *
          (∮ z in C(c, rho), P.eval x / (z - x)) = P.eval x := by
    rw [show (∮ z in C(c, rho), P.eval x / (z - x)) =
        P.eval x * (∮ z in C(c, rho), 1 / (z - x) ^ (1 : ℕ)) by
      simpa [div_eq_mul_inv] using circleIntegral.integral_const_mul
        (P.eval x) (fun z : ℂ => 1 / (z - x) ^ (1 : ℕ)) c rho]
    rw [show (2 * ((Real.pi : ℝ) : ℂ) * I)⁻¹ *
          (P.eval x * (∮ z in C(c, rho), 1 / (z - x) ^ (1 : ℕ))) =
        P.eval x * ((2 * ((Real.pi : ℝ) : ℂ) * I)⁻¹ *
          (∮ z in C(c, rho), 1 / (z - x) ^ (1 : ℕ))) by ring]
    rw [normalized_circleIntegral_one_div_sub_pow_of_mem_ball hxball,
      if_pos rfl, mul_one]
  rw [htargetIntegral]
  have hnodeIntegral (rm : IntegralJetIndex R S) :
      (2 * ((Real.pi : ℝ) : ℂ) * I)⁻¹ *
          (∮ z in C(c, rho), a rm /
            (z - ((rm.1.1 + 1 : ℕ) : ℂ)) ^ (S - rm.2.1)) =
        if rm.2.1 = S - 1 then a rm else 0 := by
    rw [show (∮ z in C(c, rho), a rm /
          (z - ((rm.1.1 + 1 : ℕ) : ℂ)) ^ (S - rm.2.1)) =
        a rm * (∮ z in C(c, rho),
          1 / (z - ((rm.1.1 + 1 : ℕ) : ℂ)) ^ (S - rm.2.1)) by
      simpa [div_eq_mul_inv] using circleIntegral.integral_const_mul (a rm)
        (fun z : ℂ => 1 /
          (z - ((rm.1.1 + 1 : ℕ) : ℂ)) ^ (S - rm.2.1)) c rho]
    rw [show (2 * ((Real.pi : ℝ) : ℂ) * I)⁻¹ *
          (a rm * (∮ z in C(c, rho),
            1 / (z - ((rm.1.1 + 1 : ℕ) : ℂ)) ^ (S - rm.2.1))) =
        a rm * ((2 * ((Real.pi : ℝ) : ℂ) * I)⁻¹ *
          (∮ z in C(c, rho),
            1 / (z - ((rm.1.1 + 1 : ℕ) : ℂ)) ^ (S - rm.2.1))) by ring]
    rw [normalized_circleIntegral_one_div_sub_pow_of_mem_ball (hnodes rm.1)]
    by_cases hm : rm.2.1 = S - 1
    · rw [if_pos hm, hm]
      have hpow : S - (S - 1) = 1 := by omega
      rw [hpow, if_pos rfl, mul_one]
    · rw [if_neg hm]
      have hpow : S - rm.2.1 ≠ 1 := by omega
      rw [if_neg hpow, mul_zero]
  rw [show (∑ rm, (2 * ((Real.pi : ℝ) : ℂ) * I)⁻¹ *
        (∮ z in C(c, rho), a rm /
          (z - ((rm.1.1 + 1 : ℕ) : ℂ)) ^ (S - rm.2.1))) =
      ∑ rm, if rm.2.1 = S - 1 then a rm else 0 by
    apply Finset.sum_congr rfl
    intro rm _
    exact hnodeIntegral rm]
  rw [Fintype.sum_sigma]
  have hcollapse :
      (∑ r : Fin R, ∑ m : Fin S,
          if m.1 = S - 1 then a ⟨r, m⟩ else 0) =
        ∑ r : Fin R, a ⟨r, ⟨S - 1, by omega⟩⟩ := by
    apply Finset.sum_congr rfl
    intro r _
    let last : Fin S := ⟨S - 1, by omega⟩
    calc
      (∑ m : Fin S, if m.1 = S - 1 then a ⟨r, m⟩ else 0) =
          (if last.1 = S - 1 then a ⟨r, last⟩ else 0) := by
        apply Fintype.sum_eq_single last
        intro m hm
        rw [if_neg]
        intro heq
        exact hm (Fin.ext heq)
      _ = a ⟨r, ⟨S - 1, by omega⟩⟩ := by simp [last]
  rw [hcollapse]
  exact hlast

/-- Exact source equation (9).  The value of an entire function at the new
integer is the outer integral of that function minus the sum of its old-node
Hasse jets against the local kernels.  The interpolating polynomial has
cancelled identically from the outer circle. -/
theorem entire_eval_eq_outer_sub_local
    {R S l : ℕ} (hR : 1 ≤ R) (hS : 1 ≤ S) (hRl : R < l)
    {c : ℂ} {rho : ℝ}
    (hlball : (l : ℂ) ∈ Metric.ball c rho)
    (hnodes : ∀ r : Fin R,
      (((r.1 + 1 : ℕ) : ℂ)) ∈ Metric.ball c rho)
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
    f (l : ℂ) =
      (2 * ((Real.pi : ℝ) : ℂ) * I)⁻¹ *
        (∮ z in C(c, rho), localEntireKernel R S (l : ℂ) f z) -
      ∑ r : Fin R, ∑ m : Fin S,
        (iteratedDeriv m.1 f ((r.1 + 1 : ℕ) : ℂ) /
            (m.1.factorial : ℂ)) *
          ((2 * ((Real.pi : ℝ) : ℂ) * I)⁻¹ *
            ∮ z in C(((r.1 + 1 : ℕ) : ℂ), (1 / 2 : ℝ)),
              localCircleKernel R S (r.1 + 1) l m.1 z) := by
  exact entire_eval_eq_outer_sub_sum_normalized_localCircleKernel
    hR hS hRl f hf hlball hnodes

/-- The sharp outer-circle bound in equation (9).  On the circle of radius
`3 * Rnext`, every old nodal denominator contributes `2 * Rnext`, whereas
the target numerator contributes at most `Rnext`.  The remaining Cauchy
denominator is the exact radial gap `3 * Rnext - l`. -/
theorem norm_normalized_outerCircleIntegral_localEntireKernel_le
    {Rold Rnext S l : ℕ} (hRnext : 0 < Rnext)
    (hRold : Rold ≤ Rnext) (hl : l ≤ Rnext)
    {f : ℂ → ℂ} {outer : ℝ} (houter : 0 ≤ outer)
    (hboundary : ∀ z : ℂ, ‖z‖ = 3 * (Rnext : ℝ) → ‖f z‖ ≤ outer) :
    ‖(2 * ((Real.pi : ℝ) : ℂ) * I)⁻¹ *
        (∮ z in C((0 : ℂ), 3 * (Rnext : ℝ)),
          localEntireKernel Rold S (l : ℂ) f z)‖ ≤
      (3 * (Rnext : ℝ)) *
        ((((Rnext : ℝ) / (2 * (Rnext : ℝ))) ^ (Rold * S) * outer) /
          (3 * (Rnext : ℝ) - l)) := by
  let decay : ℝ :=
    ((Rnext : ℝ) / (2 * (Rnext : ℝ))) ^ (Rold * S)
  let gap : ℝ := 3 * (Rnext : ℝ) - l
  have hRnextReal : (0 : ℝ) < Rnext := by exact_mod_cast hRnext
  have hgap : 0 < gap := by
    dsimp [gap]
    have hlReal : (l : ℝ) ≤ Rnext := by exact_mod_cast hl
    linarith
  have hdecay : 0 ≤ decay := by
    dsimp [decay]
    positivity
  have hkernel : ∀ z ∈ Metric.sphere (0 : ℂ) (3 * (Rnext : ℝ)),
      ‖localEntireKernel Rold S (l : ℂ) f z‖ ≤
        decay * outer / gap := by
    intro z hz
    have hznorm : ‖z‖ = 3 * (Rnext : ℝ) := by
      simpa [Metric.mem_sphere, dist_zero_right] using hz
    have hratio :
        ‖(localNodalPolynomial Rold S).eval (l : ℂ) /
            (localNodalPolynomial Rold S).eval z‖ ≤ decay := by
      rw [localNodalPolynomial_eval, localNodalPolynomial_eval]
      dsimp [decay]
      exact norm_integralNodalProduct_div_le
        (R := Rold) (S := S) (x := (l : ℂ)) (z := z)
        (show (0 : ℝ) ≤ Rnext by positivity)
        (show (0 : ℝ) < 2 * Rnext by positivity)
        (fun i hi => norm_natCast_sub_natCast_le hl
          (show i + 1 ≤ Rnext by omega))
        (fun i hi => two_mul_le_norm_sub_natCast_of_norm_eq_three_mul
          (show i + 1 ≤ Rnext by omega) hznorm)
    have hden : gap ≤ ‖z - (l : ℂ)‖ := by
      have hrev := norm_sub_norm_le z (l : ℂ)
      dsimp [gap]
      rw [hznorm, Complex.norm_natCast] at hrev
      exact hrev
    rw [localEntireKernel, norm_div, norm_mul]
    exact div_le_div₀ (mul_nonneg hdecay houter)
      (mul_le_mul hratio (hboundary z hznorm) (norm_nonneg _) hdecay)
      hgap hden
  have hint :=
    circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const
      (show (0 : ℝ) ≤ 3 * (Rnext : ℝ) by positivity) hkernel
  simpa only [smul_eq_mul, decay, gap] using hint

/-- The source-sharp outer-circle bound for a genuinely new integral
target.  Pairing the same old node in numerator and denominator retains a
factor `1 / 3` at every occurrence, rather than the uniform `1 / 2` bound
used above.  This is the nodal quotient printed in equation (9). -/
theorem norm_normalized_outerCircleIntegral_localEntireKernel_newTarget_le
    {Rold Rnext S l : ℕ} (hRnext : 0 < Rnext)
    (hRoldl : Rold < l) (hl : l ≤ Rnext)
    {f : ℂ → ℂ} {outer : ℝ} (houter : 0 ≤ outer)
    (hboundary : ∀ z : ℂ, ‖z‖ = 3 * (Rnext : ℝ) → ‖f z‖ ≤ outer) :
    ‖(2 * ((Real.pi : ℝ) : ℂ) * I)⁻¹ *
        (∮ z in C((0 : ℂ), 3 * (Rnext : ℝ)),
          localEntireKernel Rold S (l : ℂ) f z)‖ ≤
      (3 * (Rnext : ℝ)) *
        ((((1 / 3 : ℝ) ^ (Rold * S)) * outer) /
          (3 * (Rnext : ℝ) - l)) := by
  let decay : ℝ := (1 / 3 : ℝ) ^ (Rold * S)
  let gap : ℝ := 3 * (Rnext : ℝ) - l
  have hRnextReal : (0 : ℝ) < Rnext := by exact_mod_cast hRnext
  have hgap : 0 < gap := by
    dsimp [gap]
    have hlReal : (l : ℝ) ≤ Rnext := by exact_mod_cast hl
    linarith
  have hdecay : 0 ≤ decay := by
    dsimp [decay]
    positivity
  have hkernel : ∀ z ∈ Metric.sphere (0 : ℂ) (3 * (Rnext : ℝ)),
      ‖localEntireKernel Rold S (l : ℂ) f z‖ ≤
        decay * outer / gap := by
    intro z hz
    have hznorm : ‖z‖ = 3 * (Rnext : ℝ) := by
      simpa [Metric.mem_sphere, dist_zero_right] using hz
    have hratio :
        ‖(localNodalPolynomial Rold S).eval (l : ℂ) /
            (localNodalPolynomial Rold S).eval z‖ ≤ decay := by
      simp only [localNodalPolynomial_eval]
      exact norm_integralNodalProduct_newTarget_div_outerCircle_le_sharp
        hRoldl hl hznorm
    have hden : gap ≤ ‖z - (l : ℂ)‖ := by
      have hrev := norm_sub_norm_le z (l : ℂ)
      dsimp [gap]
      rw [hznorm, Complex.norm_natCast] at hrev
      exact hrev
    rw [localEntireKernel, norm_div, norm_mul]
    exact div_le_div₀ (mul_nonneg hdecay houter)
      (mul_le_mul hratio (hboundary z hznorm) (norm_nonneg _) hdecay)
      hgap hden
  have hint :=
    circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const
      (show (0 : ℝ) ≤ 3 * (Rnext : ℝ) by positivity) hkernel
  simpa only [smul_eq_mul, decay, gap] using hint

/-- The radial length and Cauchy gap in the sharp outer remainder cost at
most `3/2`.  This version leaves an arbitrary nonnegative nodal decay
factor visible, so it applies directly to the source's `3^(-R*S)` bound. -/
theorem sharpOuter_geometricFactor_le_three_halves
    {R l : ℕ} (hR : 0 < R) (hl : l ≤ R)
    {decay outer : ℝ} (hdecay : 0 ≤ decay) (houter : 0 ≤ outer) :
    (3 * (R : ℝ)) *
        ((decay * outer) / (3 * (R : ℝ) - l)) ≤
      (3 / 2 : ℝ) * (decay * outer) := by
  have hRreal : (0 : ℝ) < R := by exact_mod_cast hR
  have hlreal : (l : ℝ) ≤ R := by exact_mod_cast hl
  have hgap : 2 * (R : ℝ) ≤ 3 * R - l := by linarith
  have hgapPos : 0 < 3 * (R : ℝ) - l :=
    (mul_pos (by norm_num) hRreal).trans_le hgap
  let X : ℝ := decay * outer
  have hX : 0 ≤ X := mul_nonneg hdecay houter
  have hdiv : X / (3 * (R : ℝ) - l) ≤ X / (2 * R) :=
    div_le_div₀ hX le_rfl (mul_pos (by norm_num) hRreal) hgap
  calc
    (3 * (R : ℝ)) * (X / (3 * (R : ℝ) - l)) ≤
        (3 * R) * (X / (2 * R)) :=
      mul_le_mul_of_nonneg_left hdiv (by positivity)
    _ = (3 / 2 : ℝ) * X := by field_simp

/-- Quantitative source equation (9) with the outer Hermite polynomial
eliminated.  A `2/3` small-jet exponent and the `1/6` local-circle loss give
`exp (-A/2)`; the only remaining term is the original function on the outer
circle times the sharp nodal decay and Cauchy gap. -/
theorem norm_entire_eval_le_exp_neg_half_add_outer
    {Rold Rnext S l : ℕ} (hRoldPos : 1 ≤ Rold) (hS : 1 ≤ S)
    (hRoldl : Rold < l) (hRnext : 0 < Rnext)
    (hRold : Rold ≤ Rnext) (hl : l ≤ Rnext)
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {A delta outer : ℝ} (hA : 0 ≤ A) (hdelta : 0 ≤ delta)
    (houter : 0 ≤ outer)
    (hsmall : delta ≤ Real.exp (-(2 / 3) * A))
    (hcontour :
      (2 : ℝ) ^ (((3 * Rold + l) * S) + Rold * S) ≤
        Real.exp ((1 / 6) * A))
    (hjets : ∀ r : Fin Rold, ∀ m : Fin S,
      ‖iteratedDeriv m.1 f ((r.1 + 1 : ℕ) : ℂ) /
        (m.1.factorial : ℂ)‖ ≤ delta)
    (hboundary : ∀ z : ℂ, ‖z‖ = 3 * (Rnext : ℝ) → ‖f z‖ ≤ outer) :
    ‖f (l : ℂ)‖ ≤
      Real.exp (-(1 / 2) * A) +
        (3 * (Rnext : ℝ)) *
          ((((Rnext : ℝ) / (2 * (Rnext : ℝ))) ^ (Rold * S) * outer) /
            (3 * (Rnext : ℝ) - l)) := by
  have hlball : (l : ℂ) ∈ Metric.ball (0 : ℂ) (3 * (Rnext : ℝ)) := by
    rw [Metric.mem_ball, dist_zero_right, Complex.norm_natCast]
    have hlReal : (l : ℝ) ≤ Rnext := by exact_mod_cast hl
    have hRnextReal : (0 : ℝ) < Rnext := by exact_mod_cast hRnext
    linarith
  have hnodes : ∀ r : Fin Rold,
      (((r.1 + 1 : ℕ) : ℂ)) ∈ Metric.ball (0 : ℂ)
        (3 * (Rnext : ℝ)) := by
    intro r
    rw [Metric.mem_ball, dist_zero_right, Complex.norm_natCast]
    have hRnextReal : (0 : ℝ) < Rnext := by exact_mod_cast hRnext
    calc
      (((r.1 + 1 : ℕ) : ℝ)) ≤ (Rnext : ℝ) := by
        exact_mod_cast (show r.1 + 1 ≤ Rnext by omega)
      _ < 3 * (Rnext : ℝ) := by linarith
  have hid := entire_eval_eq_outer_sub_local hRoldPos hS hRoldl
    hlball hnodes hf
  have hlocal := norm_sum_normalized_localCircleKernel_integral_le_exp
    hRoldl hA hdelta hsmall hcontour
      (fun r m => iteratedDeriv m.1 f ((r.1 + 1 : ℕ) : ℂ) /
        (m.1.factorial : ℂ)) hjets
  have houterBound := norm_normalized_outerCircleIntegral_localEntireKernel_le
    (S := S) hRnext hRold hl houter hboundary
  rw [hid]
  calc
    ‖(2 * ((Real.pi : ℝ) : ℂ) * I)⁻¹ *
          (∮ z in C((0 : ℂ), 3 * (Rnext : ℝ)),
            localEntireKernel Rold S (l : ℂ) f z) -
        ∑ r : Fin Rold, ∑ m : Fin S,
          (iteratedDeriv m.1 f ((r.1 + 1 : ℕ) : ℂ) /
              (m.1.factorial : ℂ)) *
            ((2 * ((Real.pi : ℝ) : ℂ) * I)⁻¹ *
              ∮ z in C(((r.1 + 1 : ℕ) : ℂ), (1 / 2 : ℝ)),
                localCircleKernel Rold S (r.1 + 1) l m.1 z)‖ ≤
        ‖(2 * ((Real.pi : ℝ) : ℂ) * I)⁻¹ *
          (∮ z in C((0 : ℂ), 3 * (Rnext : ℝ)),
            localEntireKernel Rold S (l : ℂ) f z)‖ +
        ‖∑ r : Fin Rold, ∑ m : Fin S,
          (iteratedDeriv m.1 f ((r.1 + 1 : ℕ) : ℂ) /
              (m.1.factorial : ℂ)) *
            ((2 * ((Real.pi : ℝ) : ℂ) * I)⁻¹ *
              ∮ z in C(((r.1 + 1 : ℕ) : ℂ), (1 / 2 : ℝ)),
                localCircleKernel Rold S (r.1 + 1) l m.1 z)‖ := norm_sub_le _ _
    _ ≤ (3 * (Rnext : ℝ)) *
          ((((Rnext : ℝ) / (2 * (Rnext : ℝ))) ^ (Rold * S) * outer) /
            (3 * (Rnext : ℝ) - l)) +
        Real.exp (-(1 / 2) * A) := add_le_add houterBound hlocal
    _ = Real.exp (-(1 / 2) * A) +
        (3 * (Rnext : ℝ)) *
          ((((Rnext : ℝ) / (2 * (Rnext : ℝ))) ^ (Rold * S) * outer) /
            (3 * (Rnext : ℝ) - l)) := by ring

/-- Source-sharp quantitative equation (9).  It is identical to
`norm_entire_eval_le_exp_neg_half_add_outer`, except that the new-target
separation supplies the literal `(1/3)^(Rold*S)` nodal decay. -/
theorem norm_entire_eval_le_exp_neg_half_add_sharpOuter
    {Rold Rnext S l : ℕ} (hRoldPos : 1 ≤ Rold) (hS : 1 ≤ S)
    (hRoldl : Rold < l) (hRnext : 0 < Rnext) (hl : l ≤ Rnext)
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {A delta outer : ℝ} (hA : 0 ≤ A) (hdelta : 0 ≤ delta)
    (houter : 0 ≤ outer)
    (hsmall : delta ≤ Real.exp (-(2 / 3) * A))
    (hcontour :
      (2 : ℝ) ^ (((3 * Rold + l) * S) + Rold * S) ≤
        Real.exp ((1 / 6) * A))
    (hjets : ∀ r : Fin Rold, ∀ m : Fin S,
      ‖iteratedDeriv m.1 f ((r.1 + 1 : ℕ) : ℂ) /
        (m.1.factorial : ℂ)‖ ≤ delta)
    (hboundary : ∀ z : ℂ, ‖z‖ = 3 * (Rnext : ℝ) → ‖f z‖ ≤ outer) :
    ‖f (l : ℂ)‖ ≤
      Real.exp (-(1 / 2) * A) +
        (3 * (Rnext : ℝ)) *
          ((((1 / 3 : ℝ) ^ (Rold * S)) * outer) /
            (3 * (Rnext : ℝ) - l)) := by
  have hlball : (l : ℂ) ∈ Metric.ball (0 : ℂ) (3 * (Rnext : ℝ)) := by
    rw [Metric.mem_ball, dist_zero_right, Complex.norm_natCast]
    have hlReal : (l : ℝ) ≤ Rnext := by exact_mod_cast hl
    have hRnextReal : (0 : ℝ) < Rnext := by exact_mod_cast hRnext
    linarith
  have hnodes : ∀ r : Fin Rold,
      (((r.1 + 1 : ℕ) : ℂ)) ∈ Metric.ball (0 : ℂ)
        (3 * (Rnext : ℝ)) := by
    intro r
    rw [Metric.mem_ball, dist_zero_right, Complex.norm_natCast]
    have hRnextReal : (0 : ℝ) < Rnext := by exact_mod_cast hRnext
    have hrnext : r.1 + 1 ≤ Rnext :=
      (show r.1 + 1 ≤ Rold by omega).trans (hRoldl.le.trans hl)
    calc
      (((r.1 + 1 : ℕ) : ℝ)) ≤ (Rnext : ℝ) := by exact_mod_cast hrnext
      _ < 3 * (Rnext : ℝ) := by linarith
  have hid := entire_eval_eq_outer_sub_local hRoldPos hS hRoldl
    hlball hnodes hf
  have hlocal := norm_sum_normalized_localCircleKernel_integral_le_exp
    hRoldl hA hdelta hsmall hcontour
      (fun r m => iteratedDeriv m.1 f ((r.1 + 1 : ℕ) : ℂ) /
        (m.1.factorial : ℂ)) hjets
  have houterBound :=
    norm_normalized_outerCircleIntegral_localEntireKernel_newTarget_le
      (S := S) hRnext hRoldl hl houter hboundary
  rw [hid]
  calc
    ‖(2 * ((Real.pi : ℝ) : ℂ) * I)⁻¹ *
          (∮ z in C((0 : ℂ), 3 * (Rnext : ℝ)),
            localEntireKernel Rold S (l : ℂ) f z) -
        ∑ r : Fin Rold, ∑ m : Fin S,
          (iteratedDeriv m.1 f ((r.1 + 1 : ℕ) : ℂ) /
              (m.1.factorial : ℂ)) *
            ((2 * ((Real.pi : ℝ) : ℂ) * I)⁻¹ *
              ∮ z in C(((r.1 + 1 : ℕ) : ℂ), (1 / 2 : ℝ)),
                localCircleKernel Rold S (r.1 + 1) l m.1 z)‖ ≤
        ‖(2 * ((Real.pi : ℝ) : ℂ) * I)⁻¹ *
          (∮ z in C((0 : ℂ), 3 * (Rnext : ℝ)),
            localEntireKernel Rold S (l : ℂ) f z)‖ +
        ‖∑ r : Fin Rold, ∑ m : Fin S,
          (iteratedDeriv m.1 f ((r.1 + 1 : ℕ) : ℂ) /
              (m.1.factorial : ℂ)) *
            ((2 * ((Real.pi : ℝ) : ℂ) * I)⁻¹ *
              ∮ z in C(((r.1 + 1 : ℕ) : ℂ), (1 / 2 : ℝ)),
                localCircleKernel Rold S (r.1 + 1) l m.1 z)‖ := norm_sub_le _ _
    _ ≤ (3 * (Rnext : ℝ)) *
          ((((1 / 3 : ℝ) ^ (Rold * S)) * outer) /
            (3 * (Rnext : ℝ) - l)) +
        Real.exp (-(1 / 2) * A) := add_le_add houterBound hlocal
    _ = Real.exp (-(1 / 2) * A) +
        (3 * (Rnext : ℝ)) *
          ((((1 / 3 : ℝ) ^ (Rold * S)) * outer) /
            (3 * (Rnext : ℝ) - l)) := by ring

/-- Source-sharp equation (9) with an arbitrary factorial-contour loss
`B`.  The local part is `exp (-2*A/3 + B)` and the outer part retains the
literal `3^(-Rold*S)` decay.  In particular, choosing `B < A/6` preserves
strict room for the nonzero outer-circle remainder. -/
theorem norm_entire_eval_le_exp_neg_two_thirds_add_loss_add_sharpOuter
    {Rold Rnext S l : ℕ} (hRoldPos : 1 ≤ Rold) (hS : 1 ≤ S)
    (hRoldl : Rold < l) (hRnext : 0 < Rnext) (hl : l ≤ Rnext)
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {A B delta outer : ℝ} (hdelta : 0 ≤ delta) (houter : 0 ≤ outer)
    (hsmall : delta ≤ Real.exp (-(2 / 3) * A))
    (hcontour :
      (2 : ℝ) ^ (((3 * Rold + l) * S) + Rold * S) ≤ Real.exp B)
    (hjets : ∀ r : Fin Rold, ∀ m : Fin S,
      ‖iteratedDeriv m.1 f ((r.1 + 1 : ℕ) : ℂ) /
        (m.1.factorial : ℂ)‖ ≤ delta)
    (hboundary : ∀ z : ℂ, ‖z‖ = 3 * (Rnext : ℝ) → ‖f z‖ ≤ outer) :
    ‖f (l : ℂ)‖ ≤
      Real.exp (-(2 / 3) * A + B) +
        (3 * (Rnext : ℝ)) *
          ((((1 / 3 : ℝ) ^ (Rold * S)) * outer) /
            (3 * (Rnext : ℝ) - l)) := by
  have hlball : (l : ℂ) ∈ Metric.ball (0 : ℂ) (3 * (Rnext : ℝ)) := by
    rw [Metric.mem_ball, dist_zero_right, Complex.norm_natCast]
    have hlReal : (l : ℝ) ≤ Rnext := by exact_mod_cast hl
    have hRnextReal : (0 : ℝ) < Rnext := by exact_mod_cast hRnext
    linarith
  have hnodes : ∀ r : Fin Rold,
      (((r.1 + 1 : ℕ) : ℂ)) ∈ Metric.ball (0 : ℂ)
        (3 * (Rnext : ℝ)) := by
    intro r
    rw [Metric.mem_ball, dist_zero_right, Complex.norm_natCast]
    have hRnextReal : (0 : ℝ) < Rnext := by exact_mod_cast hRnext
    have hrnext : r.1 + 1 ≤ Rnext :=
      (show r.1 + 1 ≤ Rold by omega).trans (hRoldl.le.trans hl)
    calc
      (((r.1 + 1 : ℕ) : ℝ)) ≤ (Rnext : ℝ) := by exact_mod_cast hrnext
      _ < 3 * (Rnext : ℝ) := by linarith
  have hid := entire_eval_eq_outer_sub_local hRoldPos hS hRoldl
    hlball hnodes hf
  have hlocal := norm_sum_normalized_localCircleKernel_integral_le_exp_add
    hRoldl hdelta hsmall hcontour
      (fun r m => iteratedDeriv m.1 f ((r.1 + 1 : ℕ) : ℂ) /
        (m.1.factorial : ℂ)) hjets
  have houterBound :=
    norm_normalized_outerCircleIntegral_localEntireKernel_newTarget_le
      (S := S) hRnext hRoldl hl houter hboundary
  rw [hid]
  calc
    ‖(2 * ((Real.pi : ℝ) : ℂ) * I)⁻¹ *
          (∮ z in C((0 : ℂ), 3 * (Rnext : ℝ)),
            localEntireKernel Rold S (l : ℂ) f z) -
        ∑ r : Fin Rold, ∑ m : Fin S,
          (iteratedDeriv m.1 f ((r.1 + 1 : ℕ) : ℂ) /
              (m.1.factorial : ℂ)) *
            ((2 * ((Real.pi : ℝ) : ℂ) * I)⁻¹ *
              ∮ z in C(((r.1 + 1 : ℕ) : ℂ), (1 / 2 : ℝ)),
                localCircleKernel Rold S (r.1 + 1) l m.1 z)‖ ≤
        ‖(2 * ((Real.pi : ℝ) : ℂ) * I)⁻¹ *
          (∮ z in C((0 : ℂ), 3 * (Rnext : ℝ)),
            localEntireKernel Rold S (l : ℂ) f z)‖ +
        ‖∑ r : Fin Rold, ∑ m : Fin S,
          (iteratedDeriv m.1 f ((r.1 + 1 : ℕ) : ℂ) /
              (m.1.factorial : ℂ)) *
            ((2 * ((Real.pi : ℝ) : ℂ) * I)⁻¹ *
              ∮ z in C(((r.1 + 1 : ℕ) : ℂ), (1 / 2 : ℝ)),
                localCircleKernel Rold S (r.1 + 1) l m.1 z)‖ := norm_sub_le _ _
    _ ≤ (3 * (Rnext : ℝ)) *
          ((((1 / 3 : ℝ) ^ (Rold * S)) * outer) /
            (3 * (Rnext : ℝ) - l)) +
        Real.exp (-(2 / 3) * A + B) := add_le_add houterBound hlocal
    _ = Real.exp (-(2 / 3) * A + B) +
        (3 * (Rnext : ℝ)) *
          ((((1 / 3 : ℝ) ^ (Rold * S)) * outer) /
            (3 * (Rnext : ℝ) - l)) := by ring

/-- The source-ready arbitrary-loss equation-(9) estimate, with the radial
gap absorbed into `3/2`. -/
theorem
    norm_entire_eval_le_exp_neg_two_thirds_add_loss_add_three_halves_sharpOuter
    {Rold Rnext S l : ℕ} (hRoldPos : 1 ≤ Rold) (hS : 1 ≤ S)
    (hRoldl : Rold < l) (hRnext : 0 < Rnext) (hl : l ≤ Rnext)
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {A B delta outer : ℝ} (hdelta : 0 ≤ delta) (houter : 0 ≤ outer)
    (hsmall : delta ≤ Real.exp (-(2 / 3) * A))
    (hcontour :
      (2 : ℝ) ^ (((3 * Rold + l) * S) + Rold * S) ≤ Real.exp B)
    (hjets : ∀ r : Fin Rold, ∀ m : Fin S,
      ‖iteratedDeriv m.1 f ((r.1 + 1 : ℕ) : ℂ) /
        (m.1.factorial : ℂ)‖ ≤ delta)
    (hboundary : ∀ z : ℂ, ‖z‖ = 3 * (Rnext : ℝ) → ‖f z‖ ≤ outer) :
    ‖f (l : ℂ)‖ ≤
      Real.exp (-(2 / 3) * A + B) +
        (3 / 2 : ℝ) * ((1 / 3 : ℝ) ^ (Rold * S) * outer) := by
  have hsharp :=
    norm_entire_eval_le_exp_neg_two_thirds_add_loss_add_sharpOuter
      hRoldPos hS hRoldl hRnext hl hf hdelta houter hsmall hcontour
        hjets hboundary
  have hgeom := sharpOuter_geometricFactor_le_three_halves
    (decay := (1 / 3 : ℝ) ^ (Rold * S)) (outer := outer) hRnext hl
    (pow_nonneg (by norm_num) (Rold * S)) houter
  exact hsharp.trans (add_le_add le_rfl hgeom)

/-- Strict source equation (9) on an independently chosen exponent scale.
This is the form used when the freely enlarged small-form exponent `A` is
much larger than the fixed source height scale: the local and outer terms
are separately compared with `exp (-strong)`, and their sum is then below
`exp (-weak)` as soon as the exponent gap pays `log 2`. -/
theorem norm_entire_eval_lt_exp_neg_of_loss_and_sharpOuter
    {Rold Rnext S l : ℕ} (hRoldPos : 1 ≤ Rold) (hS : 1 ≤ S)
    (hRoldl : Rold < l) (hRnext : 0 < Rnext) (hl : l ≤ Rnext)
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {A B delta outer strong weak : ℝ}
    (hdelta : 0 ≤ delta) (houter : 0 ≤ outer)
    (hsmall : delta ≤ Real.exp (-(2 / 3) * A))
    (hcontour :
      (2 : ℝ) ^ (((3 * Rold + l) * S) + Rold * S) ≤ Real.exp B)
    (hjets : ∀ r : Fin Rold, ∀ m : Fin S,
      ‖iteratedDeriv m.1 f ((r.1 + 1 : ℕ) : ℂ) /
        (m.1.factorial : ℂ)‖ ≤ delta)
    (hboundary : ∀ z : ℂ, ‖z‖ = 3 * (Rnext : ℝ) → ‖f z‖ ≤ outer)
    (hlocal : Real.exp (-(2 / 3) * A + B) ≤ Real.exp (-strong))
    (hsharpOuter :
      (3 / 2 : ℝ) * ((1 / 3 : ℝ) ^ (Rold * S) * outer) ≤
        Real.exp (-strong))
    (hgap : Real.log 2 < strong - weak) :
    ‖f (l : ℂ)‖ < Real.exp (-weak) := by
  have hEqNine :=
    norm_entire_eval_le_exp_neg_two_thirds_add_loss_add_three_halves_sharpOuter
      hRoldPos hS hRoldl hRnext hl hf hdelta houter hsmall hcontour
        hjets hboundary
  have hsum :
      Real.exp (-strong) + Real.exp (-strong) < Real.exp (-weak) := by
    calc
      Real.exp (-strong) + Real.exp (-strong) =
          Real.exp (Real.log 2 - strong) := by
        rw [sub_eq_add_neg, Real.exp_add,
          Real.exp_log (by norm_num : (0 : ℝ) < 2)]
        ring
      _ < Real.exp (-weak) := by
        apply Real.exp_lt_exp.mpr
        linarith
  exact hEqNine.trans_lt
    ((add_le_add hlocal hsharpOuter).trans_lt hsum)

/-- The source-ready form of the sharp equation-(9) estimate.  The exact
radial gap has been absorbed into `3/2`, while the full `3^(-Rold*S)` nodal
decay remains. -/
theorem norm_entire_eval_le_exp_neg_half_add_three_halves_sharpOuter
    {Rold Rnext S l : ℕ} (hRoldPos : 1 ≤ Rold) (hS : 1 ≤ S)
    (hRoldl : Rold < l) (hRnext : 0 < Rnext) (hl : l ≤ Rnext)
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {A delta outer : ℝ} (hA : 0 ≤ A) (hdelta : 0 ≤ delta)
    (houter : 0 ≤ outer)
    (hsmall : delta ≤ Real.exp (-(2 / 3) * A))
    (hcontour :
      (2 : ℝ) ^ (((3 * Rold + l) * S) + Rold * S) ≤
        Real.exp ((1 / 6) * A))
    (hjets : ∀ r : Fin Rold, ∀ m : Fin S,
      ‖iteratedDeriv m.1 f ((r.1 + 1 : ℕ) : ℂ) /
        (m.1.factorial : ℂ)‖ ≤ delta)
    (hboundary : ∀ z : ℂ, ‖z‖ = 3 * (Rnext : ℝ) → ‖f z‖ ≤ outer) :
    ‖f (l : ℂ)‖ ≤
      Real.exp (-(1 / 2) * A) +
        (3 / 2 : ℝ) * ((1 / 3 : ℝ) ^ (Rold * S) * outer) := by
  have hsharp := norm_entire_eval_le_exp_neg_half_add_sharpOuter
    hRoldPos hS hRoldl hRnext hl hf hA hdelta houter hsmall hcontour
      hjets hboundary
  have hgeom := sharpOuter_geometricFactor_le_three_halves
    (decay := (1 / 3 : ℝ) ^ (Rold * S)) (outer := outer) hRnext hl
    (pow_nonneg (by norm_num) (Rold * S)) houter
  exact hsharp.trans (add_le_add le_rfl hgeom)

end Erdos240.BakerLemma4Concrete

#print axioms Erdos240.BakerLemma4Concrete.entire_eval_eq_outer_sub_local
#print axioms Erdos240.BakerLemma4Concrete.normalized_outerCircleIntegral_localPolynomialKernel_complex_eq_zero
#print axioms Erdos240.BakerLemma4Concrete.norm_normalized_outerCircleIntegral_localEntireKernel_le
#print axioms Erdos240.BakerLemma4Concrete.norm_entire_eval_le_exp_neg_half_add_outer
#print axioms Erdos240.BakerLemma4Concrete.norm_normalized_outerCircleIntegral_localEntireKernel_newTarget_le
#print axioms Erdos240.BakerLemma4Concrete.norm_entire_eval_le_exp_neg_half_add_sharpOuter
#print axioms Erdos240.BakerLemma4Concrete.norm_entire_eval_le_exp_neg_two_thirds_add_loss_add_sharpOuter
#print axioms Erdos240.BakerLemma4Concrete.norm_entire_eval_le_exp_neg_two_thirds_add_loss_add_three_halves_sharpOuter
#print axioms Erdos240.BakerLemma4Concrete.norm_entire_eval_lt_exp_neg_of_loss_and_sharpOuter
#print axioms Erdos240.BakerLemma4Concrete.sharpOuter_geometricFactor_le_three_halves
#print axioms Erdos240.BakerLemma4Concrete.norm_entire_eval_le_exp_neg_half_add_three_halves_sharpOuter
