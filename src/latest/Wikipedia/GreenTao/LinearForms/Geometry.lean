import Mathlib.Data.Int.Lemmas
import Wikipedia.GreenTao.LinearForms.Independence

/-!
# Geometry of integer affine-form systems

The Goldston--Yıldırım estimate is stated for finite systems of integer
affine forms with nonzero, pairwise non-proportional coefficient vectors and
uniformly bounded coefficients.  This file packages those hypotheses and
verifies them for the Conlon--Fox--Zhao progression forms.
-/

namespace Wikipedia.SzemeredisTheorem

namespace AffineForm

/-- The homogeneous coefficient vector of an affine form. -/
def linearPart {ι R : Type*} [Zero R]
    (ψ : AffineForm ι R) : ι → R :=
  ψ.coefficient

@[simp]
theorem linearPart_apply {ι R : Type*} [Zero R]
    (ψ : AffineForm ι R) (i : ι) :
    ψ.linearPart i = ψ.coefficient i :=
  rfl

end AffineForm

/-- No form in a system has the zero coefficient vector. -/
def NonzeroCoefficientVectors {κ ι : Type*}
    (forms : κ → AffineForm ι ℤ) : Prop :=
  ∀ q, (forms q).coefficient ≠ 0

/-- Distinct forms have non-proportional coefficient vectors. -/
def PairwiseIndependentCoefficients {κ ι : Type*}
    (forms : κ → AffineForm ι ℤ) : Prop :=
  Pairwise fun q r =>
    ¬IntCoefficientProportional
      (forms q).coefficient (forms r).coefficient

/-- Every integer linear coefficient has absolute value at most `L`.
Affine constants are deliberately not bounded. -/
def CoefficientBound {κ ι : Type*}
    (forms : κ → AffineForm ι ℤ) (L : ℕ) : Prop :=
  ∀ q i, Int.natAbs ((forms q).coefficient i) ≤ L

theorem CoefficientBound.mono {κ ι : Type*}
    {forms : κ → AffineForm ι ℤ} {L L' : ℕ}
    (h : CoefficientBound forms L) (hLL' : L ≤ L') :
    CoefficientBound forms L' :=
  fun q i => (h q i).trans hLL'

/-- The integer affine form underlying one CFZ index. -/
def cfzAffineForm {k : ℕ} (q : CFZFormIndex k) :
    AffineForm (CFZVariable k) ℤ where
  constant := 0
  coefficient := cfzCoefficient q

@[simp]
theorem cfzAffineForm_constant {k : ℕ} (q : CFZFormIndex k) :
    (cfzAffineForm q).constant = 0 :=
  rfl

@[simp]
theorem cfzAffineForm_coefficient {k : ℕ}
    (q : CFZFormIndex k) :
    (cfzAffineForm q).coefficient = cfzCoefficient q :=
  rfl

theorem cfzAffineForms_nonzero {k : ℕ} (hk : 2 ≤ k) :
    NonzeroCoefficientVectors
      (fun q : CFZFormIndex k => cfzAffineForm q) :=
  fun q => cfzCoefficient_ne_zero hk q

theorem cfzAffineForms_pairwiseIndependent {k : ℕ}
    (hk : 2 ≤ k) :
    PairwiseIndependentCoefficients
      (fun q : CFZFormIndex k => cfzAffineForm q) :=
  cfzCoefficients_pairwise_not_proportional hk

/-- Every CFZ coefficient has absolute value strictly below `k`, hence at
most `k`. -/
theorem cfzCoefficient_natAbs_le {k : ℕ}
    (q : CFZFormIndex k) (v : CFZVariable k) :
    Int.natAbs (cfzCoefficient q v) ≤ k := by
  rw [cfzCoefficient]
  split
  next hneq =>
    split
    next hselected =>
      exact Int.natAbs_coe_sub_coe_le_of_le
        (Nat.le_of_lt v.1.isLt) (Nat.le_of_lt q.1.isLt)
    next hnotselected =>
      simp
  next heq =>
    simp

theorem cfzAffineForms_coefficientBound (k : ℕ) :
    CoefficientBound
      (fun q : CFZFormIndex k => cfzAffineForm q) k :=
  fun q v => cfzCoefficient_natAbs_le q v

end Wikipedia.SzemeredisTheorem
