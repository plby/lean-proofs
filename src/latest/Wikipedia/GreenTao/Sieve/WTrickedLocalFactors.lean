import Wikipedia.GreenTao.Primes.ReducedResidues
import Wikipedia.GreenTao.Sieve.ComplexLocalFactorControl
import Wikipedia.GreenTao.Sieve.LinearFormsExpansion

/-!
# Small-prime local factors for W-tricked affine forms

If `ψ` is an integer affine form, the affine form occurring after the
`W`-trick is

`x ↦ W * ψ(x) + b`.

At a prime `p ∣ W` this form is identically `b` modulo `p`.  When `b` is a
reduced residue modulo `W`, it is therefore nowhere zero modulo `p`.  This
makes every small-prime avoidance factor, including the complex factor
produced by paired Fourier inversion, exactly one.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-- The integer affine form obtained from `ψ` by the `W`-trick:
`x ↦ W * ψ(x) + b`. -/
def wTrickedAffineForm {ι : Type*}
    (W b : ℕ) (ψ : AffineForm ι ℤ) : AffineForm ι ℤ where
  constant := (W : ℤ) * ψ.constant + b
  coefficient i := (W : ℤ) * ψ.coefficient i

@[simp]
theorem wTrickedAffineForm_constant {ι : Type*}
    (W b : ℕ) (ψ : AffineForm ι ℤ) :
    (wTrickedAffineForm W b ψ).constant =
      (W : ℤ) * ψ.constant + b :=
  rfl

@[simp]
theorem wTrickedAffineForm_coefficient {ι : Type*}
    (W b : ℕ) (ψ : AffineForm ι ℤ) (i : ι) :
    (wTrickedAffineForm W b ψ).coefficient i =
      (W : ℤ) * ψ.coefficient i :=
  rfl

/-- Evaluation of the transformed form is the expected affine
transformation of the original evaluation. -/
theorem wTrickedAffineForm_eval {ι : Type*} [Fintype ι]
    (W b : ℕ) (ψ : AffineForm ι ℤ) (x : ι → ℤ) :
    (wTrickedAffineForm W b ψ).eval x =
      (W : ℤ) * ψ.eval x + b := by
  simp only [AffineForm.eval, wTrickedAffineForm_constant,
    wTrickedAffineForm_coefficient]
  have hsum :
      (∑ i, ((W : ℤ) * ψ.coefficient i) * x i) =
        (W : ℤ) * ∑ i, ψ.coefficient i * x i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    ring
  rw [hsum]
  ring

/-- The same evaluation identity after reduction modulo an arbitrary
modulus. -/
theorem wTrickedAffineForm_evalZMod {ι : Type*} [Fintype ι]
    (W b p : ℕ) (ψ : AffineForm ι ℤ) (x : ι → ZMod p) :
    (wTrickedAffineForm W b ψ).evalZMod p x =
      (W : ZMod p) * ψ.evalZMod p x + b := by
  have hlinear :
      (wTrickedAffineForm W b ψ).linearMapZMod p x =
        (W : ZMod p) * ψ.linearMapZMod p x := by
    change
      (∑ i,
          (((W : ℤ) * ψ.coefficient i : ℤ) : ZMod p) * x i) =
        (W : ZMod p) *
          ∑ i, (ψ.coefficient i : ZMod p) * x i
    push_cast
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    ring
  unfold AffineForm.evalZMod
  rw [hlinear]
  simp only [wTrickedAffineForm_constant]
  push_cast
  ring

/-- This modular identity also matches the natural-valued CFZ lift used in
the divisor-sum expansion. -/
theorem natCast_cfzWTrickedLinearValue_eq_evalZMod
    {k N : ℕ} [NeZero N]
    (W b : ℕ) (q : CFZFormIndex k) (x : CubePoint k N) :
    (cfzWTrickedLinearValue W b q x : ZMod N) =
      (wTrickedAffineForm W b (cfzAffineForm q)).evalZMod N
        (fun v => x v.1 v.2) := by
  rw [wTrickedAffineForm_evalZMod]
  have hform :
      (cfzAffineForm q).evalZMod N (fun v => x v.1 v.2) =
        apLinearForm k N q.1 q.2 x := by
    unfold AffineForm.evalZMod AffineForm.linearMapZMod
    simp only [cfzAffineForm_constant, Int.cast_zero, zero_add,
      cfzAffineForm_coefficient]
    exact cfzCoefficientEval_eq_apLinearForm k N q x
  rw [hform]
  simp [cfzWTrickedLinearValue, wTrickedValue]

/-- If `p ∣ W`, the transformed form is the constant `b` modulo `p`. -/
theorem wTrickedAffineForm_evalZMod_of_dvd
    {ι : Type*} [Fintype ι]
    {W p : ℕ} (hpW : p ∣ W) (b : ℕ)
    (ψ : AffineForm ι ℤ) (x : ι → ZMod p) :
    (wTrickedAffineForm W b ψ).evalZMod p x =
      (b : ZMod p) := by
  rw [wTrickedAffineForm_evalZMod]
  have hW : (W : ZMod p) = 0 :=
    (ZMod.natCast_eq_zero_iff W p).2 hpW
  simp [hW]

/-- A prime divisor of `W` cannot divide a reduced residue modulo `W`. -/
theorem not_dvd_of_prime_dvd_of_coprime
    {W b p : ℕ} (hp : p.Prime) (hpW : p ∣ W)
    (hWb : W.Coprime b) :
    ¬p ∣ b := by
  exact hp.coprime_iff_not_dvd.mp
    (hWb.coprime_dvd_left hpW)

/-- Consequently the reduced residue `b` is nonzero modulo each prime
divisor of `W`. -/
theorem natCast_ne_zero_of_prime_dvd_of_coprime
    {W b p : ℕ} (hp : p.Prime) (hpW : p ∣ W)
    (hWb : W.Coprime b) :
    (b : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  exact not_dvd_of_prime_dvd_of_coprime hp hpW hWb

/-- A W-tricked affine form has no zero modulo a prime dividing `W` when
`b` is a reduced residue. -/
theorem wTrickedAffineForm_zeroFinsetZMod_eq_empty
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {W b p : ℕ} [NeZero p]
    (hp : p.Prime) (hpW : p ∣ W) (hWb : W.Coprime b)
    (ψ : AffineForm ι ℤ) :
    (wTrickedAffineForm W b ψ).zeroFinsetZMod p = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hxzero :
      (wTrickedAffineForm W b ψ).evalZMod p x = 0 :=
    (AffineForm.mem_zeroFinsetZMod p
      (wTrickedAffineForm W b ψ) x).mp hx
  rw [wTrickedAffineForm_evalZMod_of_dvd hpW] at hxzero
  exact
    (natCast_ne_zero_of_prime_dvd_of_coprime hp hpW hWb)
      hxzero

/-- Every real avoidance product for a W-tricked system is pointwise one
at a prime dividing `W`. -/
theorem localAvoidanceProduct_wTricked_eq_one
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    {W b p : ℕ} [NeZero p]
    (hp : p.Prime) (hpW : p ∣ W) (hWb : W.Coprime b)
    (forms : κ → AffineForm ι ℤ) (x : ι → ZMod p) :
    localAvoidanceProduct p
        (fun q => wTrickedAffineForm W b (forms q)) x = 1 := by
  simp [localAvoidanceProduct,
    wTrickedAffineForm_zeroFinsetZMod_eq_empty hp hpW hWb]

/-- Every complex-weighted avoidance product for a W-tricked system is
pointwise one at a prime dividing `W`, independently of its coefficients. -/
theorem complexWeightedLocalAvoidanceProduct_wTricked_eq_one
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    {W b p : ℕ} [NeZero p]
    (hp : p.Prime) (hpW : p ∣ W) (hWb : W.Coprime b)
    (forms : κ → AffineForm ι ℤ) (a : κ → ℂ)
    (x : ι → ZMod p) :
    complexWeightedLocalAvoidanceProduct p
        (fun q => wTrickedAffineForm W b (forms q)) a x = 1 := by
  simp [complexWeightedLocalAvoidanceProduct,
    wTrickedAffineForm_zeroFinsetZMod_eq_empty hp hpW hWb]

/-- The averaged complex local factor of a W-tricked system is exactly one
at every prime divisor of `W`. -/
theorem complexWeightedLocalFactor_wTricked_eq_one
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    {W b p : ℕ} [NeZero p]
    (hp : p.Prime) (hpW : p ∣ W) (hWb : W.Coprime b)
    (forms : κ → AffineForm ι ℤ) (a : κ → ℂ) :
    complexWeightedLocalFactor p
        (fun q => wTrickedAffineForm W b (forms q)) a = 1 := by
  unfold complexWeightedLocalFactor
  rw [show
      complexWeightedLocalAvoidanceProduct p
          (fun q => wTrickedAffineForm W b (forms q)) a =
        fun _x => 1 by
      funext x
      exact
        complexWeightedLocalAvoidanceProduct_wTricked_eq_one
          hp hpW hWb forms a x]
  exact Fintype.expect_one

/-- In particular, the paired-Fourier local factor is one at every prime
dividing `W`. -/
theorem pairedFourierLocalFactor_wTricked_eq_one
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    {W b p : ℕ} [NeZero p]
    (hp : p.Prime) (hpW : p ∣ W) (hWb : W.Coprime b)
    (R : ℕ) (forms : κ → AffineForm ι ℤ)
    (t u : κ → ℝ) :
    pairedFourierLocalFactor R p
        (fun q => wTrickedAffineForm W b (forms q)) t u = 1 := by
  exact complexWeightedLocalFactor_wTricked_eq_one
    hp hpW hWb forms
      (fun q => pairedFourierPrimeCoefficient R p (t q) (u q))

/-- Small-prime specialization for the standard primorial choice of `W`. -/
theorem pairedFourierLocalFactor_wTricked_primorial_eq_one
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    {w b p : ℕ} [NeZero p]
    (hp : p.Prime) (hpw : p ≤ w)
    (hwb : (primorial w).Coprime b)
    (R : ℕ) (forms : κ → AffineForm ι ℤ)
    (t u : κ → ℝ) :
    pairedFourierLocalFactor R p
        (fun q =>
          wTrickedAffineForm (primorial w) b (forms q)) t u = 1 := by
  exact pairedFourierLocalFactor_wTricked_eq_one
    hp (hp.dvd_primorial_iff.mpr hpw) hwb R forms t u

/-- Concrete CFZ small-prime factor for the standard primorial W-trick. -/
theorem pairedFourierLocalFactor_wTricked_cfz_primorial_eq_one
    {k w b p : ℕ} [NeZero p]
    (hp : p.Prime) (hpw : p ≤ w)
    (hwb : (primorial w).Coprime b)
    (R : ℕ)
    (t u : CFZFormIndex k → ℝ) :
    pairedFourierLocalFactor R p
        (fun q : CFZFormIndex k =>
          wTrickedAffineForm (primorial w) b (cfzAffineForm q))
        t u = 1 := by
  exact
    pairedFourierLocalFactor_wTricked_primorial_eq_one
      hp hpw hwb R
      (fun q : CFZFormIndex k => cfzAffineForm q) t u

end Wikipedia.SzemeredisTheorem
