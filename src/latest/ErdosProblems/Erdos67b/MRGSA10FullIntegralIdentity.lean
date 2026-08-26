import ErdosProblems.Erdos67b.MRGSA10ExponentialAverage
import ErdosProblems.Erdos67b.MRGSA10Reconstruction

/-!
# The finite two-parameter identity in GS Lemma 2.2

This file proves the coefficient-side identity preceding the A.10 contour
estimate.  All prefix sums are finite.  In particular, differentiating in
the two auxiliary real variables and applying the fundamental theorem of
calculus requires no interchange with an infinite Dirichlet series.
-/

open scoped BigOperators

namespace Erdos67b.MRHalaszBands

noncomputable section

/-- The unwindowed four-fold coefficient in the GS Lemma 2.2 identity. -/
def gsA10FullCoefficient
    (low high lambda : ArithmeticFunction ℂ) (alpha beta : ℝ) :
    ArithmeticFunction ℂ :=
  (low * gsRealShift (alpha + 2 * beta) high) *
    (gsRealShift alpha lambda * gsRealShift (alpha + 2 * beta) lambda)

/-- Real shifts preserve Dirichlet convolution. -/
theorem gsRealShift_mul
    (rho : ℝ) (a b : ArithmeticFunction ℂ) :
    gsRealShift rho (a * b) = gsRealShift rho a * gsRealShift rho b := by
  ext n
  by_cases hn : n = 0
  · subst n
    simp
  rw [gsRealShift_apply_of_ne_zero rho (a * b) hn,
    ArithmeticFunction.mul_apply, ArithmeticFunction.mul_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro xy hxy
  have hprod : xy.1 * xy.2 = n :=
    (Nat.mem_divisorsAntidiagonal.mp hxy).1
  have hx : xy.1 ≠ 0 := by
    intro hx
    rw [hx, zero_mul] at hprod
    exact hn hprod.symm
  have hy : xy.2 ≠ 0 := by
    intro hy
    rw [hy, mul_zero] at hprod
    exact hn hprod.symm
  rw [gsRealShift_apply_of_ne_zero rho a hx,
    gsRealShift_apply_of_ne_zero rho b hy]
  have hlog : Real.log n = Real.log xy.1 + Real.log xy.2 := by
    rw [← hprod, Nat.cast_mul, Real.log_mul (by exact_mod_cast hx)
      (by exact_mod_cast hy)]
  have hexp :
      Real.exp (-rho * Real.log n) =
        Real.exp (-rho * Real.log xy.1) *
          Real.exp (-rho * Real.log xy.2) := by
    rw [hlog, mul_add, Real.exp_add]
  rw [hexp]
  push_cast
  ring

/-- Shifting by zero does not change a positive arithmetic coefficient. -/
theorem gsRealShift_zero_parameter (a : ArithmeticFunction ℂ) :
    gsRealShift 0 a = a := by
  ext n
  by_cases hn : n = 0
  · subst n
    simp
  rw [gsRealShift_apply_of_ne_zero 0 a hn]
  simp

/-- Under the generalized-Mangoldt convolution identity, the four-fold
coefficient is the logarithmic derivative of the shifted high factor. -/
theorem gsA10FullCoefficient_eq_shift_logWeighted
    (low high lambda : ArithmeticFunction ℂ) (alpha beta : ℝ)
    (hlambda : lambda * high = gsLogWeighted high) :
    gsA10FullCoefficient low high lambda alpha beta =
      (low * gsRealShift alpha lambda) *
        gsRealShift (alpha + 2 * beta) (gsLogWeighted high) := by
  unfold gsA10FullCoefficient
  calc
    (low * gsRealShift (alpha + 2 * beta) high) *
          (gsRealShift alpha lambda *
            gsRealShift (alpha + 2 * beta) lambda) =
        (low * gsRealShift alpha lambda) *
          (gsRealShift (alpha + 2 * beta) lambda *
            gsRealShift (alpha + 2 * beta) high) := by
      ring
    _ = (low * gsRealShift alpha lambda) *
          gsRealShift (alpha + 2 * beta) (lambda * high) := by
      rw [gsRealShift_mul]
    _ = _ := by rw [hlambda]

/-- Each coefficient of a real-shifted arithmetic function varies
continuously in the shift. -/
theorem continuous_gsRealShift_apply
    (a : ArithmeticFunction ℂ) (n : ℕ) :
    Continuous (fun rho : ℝ ↦ gsRealShift rho a n) := by
  by_cases hn : n = 0
  · subst n
    simpa using (continuous_const : Continuous (fun _ : ℝ ↦ (0 : ℂ)))
  have hfun :
      (fun rho : ℝ ↦ gsRealShift rho a n) =
        (fun rho : ℝ ↦
          (Real.exp (-rho * Real.log n) : ℂ) * a n) := by
    funext rho
    rw [gsRealShift_apply_of_ne_zero rho a hn]
  rw [hfun]
  fun_prop

/-- A finite prefix of a convolution with one shifted factor varies
continuously in the shift. -/
theorem continuous_positivePrefixSum_mul_gsRealShift
    (a b : ArithmeticFunction ℂ) (X : ℕ) :
    Continuous (fun rho : ℝ ↦ positivePrefixSum
      (fun n ↦ (a * gsRealShift rho b) n) X) := by
  have hfun :
      (fun rho : ℝ ↦ positivePrefixSum
          (fun n ↦ (a * gsRealShift rho b) n) X) =
        (fun rho : ℝ ↦ ∑ n ∈ Finset.range (X + 1),
          ∑ xy ∈ n.divisorsAntidiagonal,
            a xy.1 * gsRealShift rho b xy.2) := by
    funext rho
    unfold positivePrefixSum
    simp only [ArithmeticFunction.map_zero, sub_zero,
      ArithmeticFunction.mul_apply]
  rw [hfun]
  apply continuous_finsetSum
  intro n hn
  apply continuous_finsetSum
  intro xy hxy
  exact (continuous_gsRealShift_apply b xy.2).const_mul (a xy.1)

/-- Coefficientwise derivative of a real shift. -/
theorem hasDerivAt_gsRealShift_apply
    (a : ArithmeticFunction ℂ) (n : ℕ) (rho : ℝ) :
    HasDerivAt (fun u : ℝ ↦ gsRealShift u a n)
      (-((Real.log n : ℝ) : ℂ) * gsRealShift rho a n) rho := by
  by_cases hn : n = 0
  · subst n
    simpa using (hasDerivAt_const (x := rho) (c := (0 : ℂ)))
  have hlin : HasDerivAt (fun u : ℝ ↦ -u * Real.log n)
      (-Real.log n) rho := by
    simpa [id_eq] using
      (hasDerivAt_id rho).neg.mul_const (Real.log n)
  have hexp : HasDerivAt (fun u : ℝ ↦ Real.exp (-u * Real.log n))
      (Real.exp (-rho * Real.log n) * (-Real.log n)) rho :=
    (Real.hasDerivAt_exp _).comp rho hlin
  have hcomplex := hexp.ofReal_comp.mul_const (a n)
  have hfun :
      (fun u : ℝ ↦ gsRealShift u a n) =
        (fun u : ℝ ↦ (Real.exp (-u * Real.log n) : ℂ) * a n) := by
    funext u
    rw [gsRealShift_apply_of_ne_zero u a hn]
  rw [hfun]
  apply hcomplex.congr_deriv
  rw [gsRealShift_apply_of_ne_zero rho a hn]
  push_cast
  ring

/-- Differentiating a shifted right convolution factor inserts its
logarithmic weight, with the expected minus sign. -/
theorem hasDerivAt_arithmetic_mul_gsRealShift_apply
    (a b : ArithmeticFunction ℂ) (n : ℕ) (rho : ℝ) :
    HasDerivAt (fun u : ℝ ↦ (a * gsRealShift u b) n)
      (-(a * gsRealShift rho (gsLogWeighted b)) n) rho := by
  have hsum := HasDerivAt.fun_sum
    (u := n.divisorsAntidiagonal)
    (A := fun xy u ↦ a xy.1 * gsRealShift u b xy.2)
    (A' := fun xy ↦
      a xy.1 *
        (-((Real.log xy.2 : ℝ) : ℂ) * gsRealShift rho b xy.2))
    (fun xy hxy ↦ (hasDerivAt_gsRealShift_apply b xy.2 rho).const_mul
      (a xy.1))
  have hfun :
      (fun u : ℝ ↦ (a * gsRealShift u b) n) =
        (fun u : ℝ ↦ ∑ xy ∈ n.divisorsAntidiagonal,
          a xy.1 * gsRealShift u b xy.2) := by
    funext u
    rw [ArithmeticFunction.mul_apply]
  rw [hfun]
  apply hsum.congr_deriv
  rw [ArithmeticFunction.mul_apply]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro xy hxy
  by_cases hy : xy.2 = 0
  · simp [hy]
  rw [gsRealShift_apply_of_ne_zero rho (gsLogWeighted b) hy,
    gsRealShift_apply_of_ne_zero rho b hy, gsLogWeighted_apply]
  push_cast
  ring

/-- Prefix-sum form of the shifted-convolution derivative. -/
theorem hasDerivAt_positivePrefixSum_mul_gsRealShift
    (a b : ArithmeticFunction ℂ) (X : ℕ) (rho : ℝ) :
    HasDerivAt
      (fun u : ℝ ↦ positivePrefixSum
        (fun n ↦ (a * gsRealShift u b) n) X)
      (-positivePrefixSum
        (fun n ↦ (a * gsRealShift rho (gsLogWeighted b)) n) X) rho := by
  have hsum := HasDerivAt.fun_sum
    (u := Finset.range (X + 1))
    (A := fun n u ↦ (a * gsRealShift u b) n)
    (A' := fun n ↦ -(a * gsRealShift rho (gsLogWeighted b)) n)
    (fun n hn ↦ hasDerivAt_arithmetic_mul_gsRealShift_apply a b n rho)
  have hfun :
      (fun u : ℝ ↦ positivePrefixSum
          (fun n ↦ (a * gsRealShift u b) n) X) =
        (fun u : ℝ ↦ ∑ n ∈ Finset.range (X + 1),
          (a * gsRealShift u b) n) := by
    funext u
    unfold positivePrefixSum
    simp only [ArithmeticFunction.map_zero, sub_zero]
  rw [hfun]
  apply hsum.congr_deriv
  unfold positivePrefixSum
  simp only [ArithmeticFunction.map_zero, sub_zero,
    Finset.sum_neg_distrib]

/-- The beta derivative in the rectangular A.10 average.  The factor two
is the source change of variables `beta_source = 2 * beta`. -/
theorem hasDerivAt_gsA10AuxiliaryPrefix_beta
    (low high lambda : ArithmeticFunction ℂ) (X : ℕ)
    (alpha beta : ℝ)
    (hlambda : lambda * high = gsLogWeighted high) :
    HasDerivAt
      (fun u : ℝ ↦ positivePrefixSum
        (fun n ↦ ((low * gsRealShift alpha lambda) *
          gsRealShift (alpha + 2 * u) high) n) X)
      (-2 * positivePrefixSum
        (gsA10FullCoefficient low high lambda alpha beta) X) beta := by
  have hrho : HasDerivAt (fun u : ℝ ↦ alpha + 2 * u) 2 beta := by
    have htwo : HasDerivAt (fun u : ℝ ↦ 2 * u) 2 beta := by
      simpa [id_eq, mul_comm] using
        (hasDerivAt_id beta).const_mul 2
    exact htwo.const_add alpha
  have h :=
    (hasDerivAt_positivePrefixSum_mul_gsRealShift
      (low * gsRealShift alpha lambda) high X (alpha + 2 * beta)).scomp
      beta hrho
  apply h.congr_deriv
  rw [gsA10FullCoefficient_eq_shift_logWeighted
    low high lambda alpha beta hlambda]
  rw [two_smul]
  ring

/-- The unwindowed full coefficient has a continuous finite prefix as a
function of the beta variable. -/
theorem continuous_positivePrefixSum_gsA10FullCoefficient_beta
    (low high lambda : ArithmeticFunction ℂ) (X : ℕ) (alpha : ℝ)
    (hlambda : lambda * high = gsLogWeighted high) :
    Continuous (fun beta : ℝ ↦ positivePrefixSum
      (gsA10FullCoefficient low high lambda alpha beta) X) := by
  have hfun :
      (fun beta : ℝ ↦ positivePrefixSum
          (gsA10FullCoefficient low high lambda alpha beta) X) =
        (fun beta : ℝ ↦ positivePrefixSum
          (fun n ↦ ((low * gsRealShift alpha lambda) *
            gsRealShift (alpha + 2 * beta) (gsLogWeighted high)) n) X) := by
    funext beta
    rw [gsA10FullCoefficient_eq_shift_logWeighted
      low high lambda alpha beta hlambda]
  rw [hfun]
  exact (continuous_positivePrefixSum_mul_gsRealShift
    (low * gsRealShift alpha lambda) (gsLogWeighted high) X).comp
      (by fun_prop)

/-- Integrating first in beta turns the double generalized-Mangoldt
coefficient into the difference of the two shifted high prefixes. -/
theorem two_mul_intervalIntegral_positivePrefixSum_gsA10FullCoefficient_eq
    (low high lambda : ArithmeticFunction ℂ) (X : ℕ)
    (alpha eta : ℝ)
    (hlambda : lambda * high = gsLogWeighted high) :
    2 * (∫ beta : ℝ in 0..eta,
        positivePrefixSum
          (gsA10FullCoefficient low high lambda alpha beta) X) =
      positivePrefixSum
          (fun n ↦ ((low * gsRealShift alpha lambda) *
            gsRealShift alpha high) n) X -
        positivePrefixSum
          (fun n ↦ ((low * gsRealShift alpha lambda) *
            gsRealShift (alpha + 2 * eta) high) n) X := by
  let F : ℝ → ℂ := fun beta ↦ positivePrefixSum
    (fun n ↦ ((low * gsRealShift alpha lambda) *
      gsRealShift (alpha + 2 * beta) high) n) X
  let G : ℝ → ℂ := fun beta ↦ positivePrefixSum
    (gsA10FullCoefficient low high lambda alpha beta) X
  have hderiv : ∀ beta ∈ Set.uIcc (0 : ℝ) eta,
      HasDerivAt F (-2 * G beta) beta := by
    intro beta hbeta
    exact hasDerivAt_gsA10AuxiliaryPrefix_beta
      low high lambda X alpha beta hlambda
  have hcont : Continuous G := by
    exact continuous_positivePrefixSum_gsA10FullCoefficient_beta
      low high lambda X alpha hlambda
  have hfund := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((hcont.const_mul (-2)).intervalIntegrable (0 : ℝ) eta)
  change (∫ beta : ℝ in 0..eta, -2 * G beta) = F eta - F 0 at hfund
  rw [intervalIntegral.integral_const_mul] at hfund
  have hcalc : 2 * (∫ beta : ℝ in 0..eta, G beta) = F 0 - F eta := by
    calc
    2 * (∫ beta : ℝ in 0..eta, G beta) =
        -((-2) * (∫ beta : ℝ in 0..eta, G beta)) := by ring
    _ = -(F eta - F 0) := congrArg Neg.neg hfund
    _ = F 0 - F eta := by ring
  simpa [F, G] using hcalc

/-- The alpha integration of one logarithmically weighted high factor is
the difference of its untwisted and shifted prefixes. -/
theorem intervalIntegral_positivePrefixSum_shift_logWeighted_eq
    (low high : ArithmeticFunction ℂ) (X : ℕ) (eta : ℝ) :
    (∫ alpha : ℝ in 0..eta,
        positivePrefixSum
          (fun n ↦ (low * gsRealShift alpha (gsLogWeighted high)) n) X) =
      positivePrefixSum (fun n ↦ (low * high) n) X -
        positivePrefixSum
          (fun n ↦ (low * gsRealShift eta high) n) X := by
  let F : ℝ → ℂ := fun alpha ↦ positivePrefixSum
    (fun n ↦ (low * gsRealShift alpha high) n) X
  let G : ℝ → ℂ := fun alpha ↦ positivePrefixSum
    (fun n ↦ (low * gsRealShift alpha (gsLogWeighted high)) n) X
  have hderiv : ∀ alpha ∈ Set.uIcc (0 : ℝ) eta,
      HasDerivAt F (-G alpha) alpha := by
    intro alpha halpha
    exact hasDerivAt_positivePrefixSum_mul_gsRealShift low high X alpha
  have hcont : Continuous G :=
    continuous_positivePrefixSum_mul_gsRealShift
      low (gsLogWeighted high) X
  have hfund := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (hcont.neg.intervalIntegrable (0 : ℝ) eta)
  change (∫ alpha : ℝ in 0..eta, -G alpha) = F eta - F 0 at hfund
  rw [intervalIntegral.integral_neg] at hfund
  have hcalc : (∫ alpha : ℝ in 0..eta, G alpha) = F 0 - F eta := by
    calc
      (∫ alpha : ℝ in 0..eta, G alpha) =
          -(-(∫ alpha : ℝ in 0..eta, G alpha)) := by ring
      _ = -(F eta - F 0) := congrArg Neg.neg hfund
      _ = F 0 - F eta := by ring
  simpa [F, G, gsRealShift_zero_parameter] using hcalc

/-- Exact finite coefficient identity in GS Lemma 2.2, after the source
change of variables `beta_source = 2 * beta`.  It uses only the finite
generalized-Mangoldt convolution identity; no Dirichlet-series convergence
or desired prefix estimate is assumed. -/
theorem two_mul_intervalIntegral_intervalIntegral_gsA10FullCoefficient_eq
    (low high lambda : ArithmeticFunction ℂ) (X : ℕ) (eta : ℝ)
    (hlambda : lambda * high = gsLogWeighted high) :
    2 * (∫ alpha : ℝ in 0..eta, ∫ beta : ℝ in 0..eta,
        positivePrefixSum
          (gsA10FullCoefficient low high lambda alpha beta) X) =
      positivePrefixSum (fun n ↦ (low * high) n) X -
        positivePrefixSum
          (fun n ↦ (low * gsRealShift eta high) n) X -
        ∫ alpha : ℝ in 0..eta,
          positivePrefixSum
            (fun n ↦ ((low * gsRealShift alpha lambda) *
              gsRealShift (2 * eta + alpha) high) n) X := by
  let A : ℝ → ℂ := fun alpha ↦ positivePrefixSum
    (fun n ↦ ((low * gsRealShift alpha lambda) *
      gsRealShift alpha high) n) X
  let B : ℝ → ℂ := fun alpha ↦ positivePrefixSum
    (fun n ↦ ((low * gsRealShift alpha lambda) *
      gsRealShift (alpha + 2 * eta) high) n) X
  have hAfun : A = fun alpha ↦ positivePrefixSum
      (fun n ↦ (low * gsRealShift alpha (gsLogWeighted high)) n) X := by
    funext alpha
    dsimp [A]
    have hcoef :
        (low * gsRealShift alpha lambda) * gsRealShift alpha high =
          low * gsRealShift alpha (gsLogWeighted high) := by
      rw [mul_assoc, ← gsRealShift_mul, hlambda]
    exact congrArg (fun c : ArithmeticFunction ℂ ↦
      positivePrefixSum (fun n ↦ c n) X) hcoef
  have hBfun : B = fun alpha ↦ positivePrefixSum
      (fun n ↦ (low * gsRealShift alpha
        (lambda * gsRealShift (2 * eta) high)) n) X := by
    funext alpha
    dsimp [B]
    have hcoef :
        (low * gsRealShift alpha lambda) *
            gsRealShift (alpha + 2 * eta) high =
          low * gsRealShift alpha
            (lambda * gsRealShift (2 * eta) high) := by
      rw [← gsRealShift_add alpha (2 * eta) high,
        mul_assoc, ← gsRealShift_mul]
    exact congrArg (fun c : ArithmeticFunction ℂ ↦
      positivePrefixSum (fun n ↦ c n) X) hcoef
  have hAcont : Continuous A := by
    rw [hAfun]
    exact continuous_positivePrefixSum_mul_gsRealShift
      low (gsLogWeighted high) X
  have hBcont : Continuous B := by
    rw [hBfun]
    exact continuous_positivePrefixSum_mul_gsRealShift
      low (lambda * gsRealShift (2 * eta) high) X
  have houter :
      2 * (∫ alpha : ℝ in 0..eta, ∫ beta : ℝ in 0..eta,
          positivePrefixSum
            (gsA10FullCoefficient low high lambda alpha beta) X) =
        (∫ alpha : ℝ in 0..eta, A alpha) -
          ∫ alpha : ℝ in 0..eta, B alpha := by
    calc
      2 * (∫ alpha : ℝ in 0..eta, ∫ beta : ℝ in 0..eta,
          positivePrefixSum
            (gsA10FullCoefficient low high lambda alpha beta) X) =
          ∫ alpha : ℝ in 0..eta,
            2 * (∫ beta : ℝ in 0..eta,
              positivePrefixSum
                (gsA10FullCoefficient low high lambda alpha beta) X) := by
        rw [intervalIntegral.integral_const_mul]
      _ = ∫ alpha : ℝ in 0..eta, A alpha - B alpha := by
        apply intervalIntegral.integral_congr
        intro alpha halpha
        exact two_mul_intervalIntegral_positivePrefixSum_gsA10FullCoefficient_eq
          low high lambda X alpha eta hlambda
      _ = (∫ alpha : ℝ in 0..eta, A alpha) -
          ∫ alpha : ℝ in 0..eta, B alpha := by
        rw [intervalIntegral.integral_sub
          (hAcont.intervalIntegrable (0 : ℝ) eta)
          (hBcont.intervalIntegrable (0 : ℝ) eta)]
  have hA : (∫ alpha : ℝ in 0..eta, A alpha) =
      positivePrefixSum (fun n ↦ (low * high) n) X -
        positivePrefixSum
          (fun n ↦ (low * gsRealShift eta high) n) X := by
    rw [hAfun]
    exact intervalIntegral_positivePrefixSum_shift_logWeighted_eq
      low high X eta
  have hB : (∫ alpha : ℝ in 0..eta, B alpha) =
      ∫ alpha : ℝ in 0..eta,
        positivePrefixSum
          (fun n ↦ ((low * gsRealShift alpha lambda) *
            gsRealShift (2 * eta + alpha) high) n) X := by
    apply intervalIntegral.integral_congr
    intro alpha halpha
    dsimp [B]
    rw [show alpha + 2 * eta = 2 * eta + alpha by ring]
  rw [houter, hA, hB]

end

end Erdos67b.MRHalaszBands
