/-
Copyright (c) 2026 The Erdos Problems Formalization Project.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Erdos Problems Formalization Project
-/
import ErdosProblems.Erdos1165.AppendixFirstMoment
import ErdosProblems.Erdos1165.StirlingLocalCLT

/-!
# The finite constrained-profile lower bound in the HLOZ appendix

This file begins the small-ball estimate in Proposition A.7 of
Hao--Li--Okada--Zheng.  The upcrossing transition from `a` to `b` is

`choose (a + b - 1) b / 2^(a+b)`.

For every interior binomial coefficient, the Robbins remainder from
`StirlingLocalCLT.lean` is bounded below by the sum of two reciprocal
factorial arguments.  We exponentiate that estimate and obtain an explicit
positive lower kernel for every transition.  We then lift
the one-edge estimate, without any probabilistic or asymptotic hypothesis, to
the product along a finite profile and finally to the sum over all profiles
satisfying `|m_k - 2 k^2| <= k^(1+delta)`.

The resulting theorem `constrainedStirlingWeight_le` is the exact finite
product lower bound needed before the remaining analytic step: Taylor-expand
the explicit `logBinomialMain` kernel into the Gaussian kernels `b_k` of
(A.11), and prove their lattice small-ball sum by comparison with Brownian
motion (Lemma A.8).  Neither of those estimates is assumed here.
-/

open scoped BigOperators

namespace Erdos1165.ProfileSmallBall

noncomputable section

open AppendixFirstMoment StirlingLocalCLT

/-- The positive reciprocal correction in the lower Robbins estimate for
`choose (a+b-1) b`.  Its two denominator indices are `b` and `a-1`. -/
def edgeRobbinsPenalty (a b : ℕ) : ℝ :=
  (1 : ℝ) / (12 * b) + 1 / (12 * (a + b - 1 - b : ℕ))

/-- The explicit one-edge lower kernel obtained by replacing the logarithmic
Stirling remainder of the binomial coefficient by its Robbins lower bound. -/
def edgeStirlingLower (a b : ℕ) : ℝ :=
  Real.exp (logBinomialMain (a + b - 1) b - edgeRobbinsPenalty a b) /
    (2 : ℝ) ^ (a + b)

/-- Logarithm of `edgeStirlingLower`, written additively for later Taylor
expansion and summation along a path. -/
def edgeStirlingExponent (a b : ℕ) : ℝ :=
  logBinomialMain (a + b - 1) b - edgeRobbinsPenalty a b -
    (a + b : ℝ) * Real.log 2

lemma edgeStirlingLower_eq_exp (a b : ℕ) :
    edgeStirlingLower a b = Real.exp (edgeStirlingExponent a b) := by
  rw [edgeStirlingLower, edgeStirlingExponent, Real.exp_sub]
  have hpow : Real.exp ((a + b : ℝ) * Real.log 2) = (2 : ℝ) ^ (a + b) := by
    rw [← Nat.cast_add, Real.exp_nat_mul,
      Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  simp only [Real.exp_sub]
  rw [hpow]

lemma edgeStirlingLower_pos (a b : ℕ) : 0 < edgeStirlingLower a b := by
  unfold edgeStirlingLower
  positivity

lemma edgeStirlingLower_nonneg (a b : ℕ) : 0 ≤ edgeStirlingLower a b :=
  (edgeStirlingLower_pos a b).le

/-- A direct, uniform lower bound for the critical negative-binomial
transition.  The two lower bounds on `a` and `b` are exactly what ensures that
the binomial coefficient is interior, so the uniform Stirling remainder
theorem applies. -/
theorem edgeStirlingLower_le_transitionMass {a b : ℕ}
    (ha : 2 ≤ a) (hb : 1 ≤ b) :
    edgeStirlingLower a b ≤ transitionMass a b := by
  have hb0 : b ≠ 0 := Nat.ne_of_gt hb
  have hbn : b < a + b - 1 := by omega
  have hrem := logBinomialRemainder_robbins_bounds hb0 hbn
  have hlog :
      logBinomialMain (a + b - 1) b - edgeRobbinsPenalty a b ≤
        Real.log (((a + b - 1).choose b : ℕ) : ℝ) := by
    unfold edgeRobbinsPenalty
    rw [Nat.cast_sub hbn.le]
    unfold logBinomialRemainder at hrem
    linarith
  have hchoose : (0 : ℝ) < ((a + b - 1).choose b : ℕ) := by
    exact_mod_cast Nat.choose_pos hbn.le
  have hexp :
      Real.exp (logBinomialMain (a + b - 1) b - edgeRobbinsPenalty a b) ≤
        (((a + b - 1).choose b : ℕ) : ℝ) := by
    have := Real.exp_le_exp.mpr hlog
    rwa [Real.exp_log hchoose] at this
  rw [edgeStirlingLower, transitionMass_formula (by omega : 0 < a)]
  exact div_le_div_of_nonneg_right hexp (by positivity)

/-- Product of the explicit Stirling lower kernels along successive entries
of a finite profile. -/
def stirlingLowerProduct : List ℕ → ℝ
  | [] => 1
  | [_] => 1
  | a :: b :: rest => edgeStirlingLower a b * stirlingLowerProduct (b :: rest)

/-- Additive exponent corresponding to `stirlingLowerProduct`. -/
def stirlingLogLower : List ℕ → ℝ
  | [] => 0
  | [_] => 0
  | a :: b :: rest => edgeStirlingExponent a b + stirlingLogLower (b :: rest)

@[simp] lemma stirlingLowerProduct_nil : stirlingLowerProduct [] = 1 := rfl

@[simp] lemma stirlingLowerProduct_singleton (a : ℕ) :
    stirlingLowerProduct [a] = 1 := rfl

@[simp] lemma stirlingLowerProduct_cons_cons (a b : ℕ) (rest : List ℕ) :
    stirlingLowerProduct (a :: b :: rest) =
      edgeStirlingLower a b * stirlingLowerProduct (b :: rest) := rfl

@[simp] lemma stirlingLogLower_nil : stirlingLogLower [] = 0 := rfl

@[simp] lemma stirlingLogLower_singleton (a : ℕ) : stirlingLogLower [a] = 0 := rfl

@[simp] lemma stirlingLogLower_cons_cons (a b : ℕ) (rest : List ℕ) :
    stirlingLogLower (a :: b :: rest) =
      edgeStirlingExponent a b + stirlingLogLower (b :: rest) := rfl

/-- The multiplicative lower kernel is exactly the exponential of the sum of
its finite edge exponents. -/
lemma stirlingLowerProduct_eq_exp (m : List ℕ) :
    stirlingLowerProduct m = Real.exp (stirlingLogLower m) := by
  induction m with
  | nil => simp
  | cons a tail ih =>
      cases tail with
      | nil => simp
      | cons b rest =>
          rw [stirlingLowerProduct_cons_cons, stirlingLogLower_cons_cons,
            edgeStirlingLower_eq_exp, ih, Real.exp_add]

lemma stirlingLowerProduct_pos (m : List ℕ) : 0 < stirlingLowerProduct m := by
  induction m with
  | nil => norm_num
  | cons a tail ih =>
      cases tail with
      | nil => norm_num
      | cons b rest =>
          rw [stirlingLowerProduct_cons_cons]
          exact mul_pos (edgeStirlingLower_pos a b) ih

lemma stirlingLowerProduct_nonneg (m : List ℕ) :
    0 ≤ stirlingLowerProduct m := (stirlingLowerProduct_pos m).le

/-- The one-edge lower estimate multiplies along every finite list whose
entries are at least two. -/
theorem stirlingLowerProduct_le_transitionProduct (m : List ℕ)
    (hm : ∀ a ∈ m, 2 ≤ a) :
    stirlingLowerProduct m ≤ transitionProduct m := by
  induction m with
  | nil => simp
  | cons a tail ih =>
      cases tail with
      | nil => simp
      | cons b rest =>
          rw [stirlingLowerProduct_cons_cons, transitionProduct_cons_cons]
          exact mul_le_mul
            (edgeStirlingLower_le_transitionMass
              (hm a (by simp)) ((hm b (by simp)).trans' (by omega)))
            (ih (fun c hc ↦ hm c (by simp [hc])))
            (stirlingLowerProduct_nonneg (b :: rest))
            (transitionMass_nonneg a b)

/-! ## The profile-window hypothesis supplies the positivity conditions -/

/-- If `delta <= 1`, a number in the HLOZ window around `2*l^2`, with
`l >= 2`, is at least two.  This also records why no boundary binomial
coefficient occurs in a constrained profile. -/
lemma two_le_of_inProfileWindow {delta : ℝ} (hdelta : delta ≤ 1)
    {l m : ℕ} (hl : 2 ≤ l) (hm : InProfileWindow delta l m) :
    2 ≤ m := by
  have hlReal : (1 : ℝ) ≤ l := by exact_mod_cast (show 1 ≤ l by omega)
  have hexponent : 1 + delta ≤ (2 : ℝ) := by linarith
  have hwindowPower :
      (l : ℝ) ^ (1 + delta) ≤ (l : ℝ) ^ (2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hlReal hexponent
  rw [Real.rpow_two] at hwindowPower
  rw [InProfileWindow, abs_le] at hm
  dsimp only [profileCenter] at hm
  push_cast at hm
  have hlTwo : (2 : ℝ) ≤ l := by exact_mod_cast hl
  have hmReal : (2 : ℝ) ≤ m := by
    nlinarith [sq_nonneg ((l : ℝ) - 2)]
  exact_mod_cast hmReal

lemma constrainedProfile_entry_two_le {n : ℕ} {delta : ℝ}
    (hdelta : delta ≤ 1) {m : Profile n}
    (hm : IsConstrainedProfile delta m) (i : Fin (n - 1)) :
    2 ≤ m i := by
  apply two_le_of_inProfileWindow hdelta (l := scaleIndex i)
  · simp [scaleIndex]
  · exact hm i

lemma constrainedProfile_all_entries_two_le {n : ℕ} {delta : ℝ}
    (hdelta : delta ≤ 1) {m : Profile n}
    (hm : IsConstrainedProfile delta m) :
    ∀ a ∈ profileList m, 2 ≤ a := by
  rw [profileList, List.forall_mem_ofFn_iff]
  exact constrainedProfile_entry_two_le hdelta hm

/-- The explicit Stirling product is a lower bound for the probability weight
of every path staying in the parabolic HLOZ window. -/
theorem constrainedProfile_stirlingLower_le_weight {n : ℕ} {delta : ℝ}
    (hdelta : delta ≤ 1) {m : Profile n}
    (hm : IsConstrainedProfile delta m) :
    stirlingLowerProduct (profileList m) ≤ profileWeight m := by
  exact stirlingLowerProduct_le_transitionProduct _
    (constrainedProfile_all_entries_two_le hdelta hm)

/-- The finite sum of the explicit Stirling products over all constrained
profiles. -/
noncomputable def constrainedStirlingWeight (n : ℕ) (delta : ℝ) : ℝ :=
  ∑ m ∈ constrainedProfiles n delta, stirlingLowerProduct (profileList m)

lemma constrainedStirlingWeight_nonneg (n : ℕ) (delta : ℝ) :
    0 ≤ constrainedStirlingWeight n delta := by
  exact Finset.sum_nonneg fun m _ ↦ stirlingLowerProduct_nonneg _

/-- **Finite constrained-profile product lower bound.**

Every path satisfying `|m_k - 2*k^2| <= k^(1+delta)` contributes at least its
fully explicit Stirling lower product.  Summing gives an unconditional lower
bound on the exact negative-binomial profile probability appearing in HLOZ
Proposition A.7. -/
theorem constrainedStirlingWeight_le (n : ℕ) {delta : ℝ}
    (hdelta : delta ≤ 1) :
    constrainedStirlingWeight n delta ≤ constrainedProfileWeight n delta := by
  unfold constrainedStirlingWeight constrainedProfileWeight
  exact Finset.sum_le_sum fun m hm ↦
    constrainedProfile_stirlingLower_le_weight hdelta
      ((mem_constrainedProfiles.mp hm))

/-- Log-additive version of `constrainedStirlingWeight_le`.  This is the form
to which the deterministic Taylor expansion and the Gaussian lattice
small-ball estimate of HLOZ (A.11)--(A.13) apply. -/
theorem constrained_exp_stirlingLogLower_le (n : ℕ) {delta : ℝ}
    (hdelta : delta ≤ 1) :
    (∑ m ∈ constrainedProfiles n delta,
        Real.exp (stirlingLogLower (profileList m))) ≤
      constrainedProfileWeight n delta := by
  simpa only [constrainedStirlingWeight, ← stirlingLowerProduct_eq_exp] using
    (show constrainedStirlingWeight n delta ≤ constrainedProfileWeight n delta from
      constrainedStirlingWeight_le n hdelta)

end

end Erdos1165.ProfileSmallBall
