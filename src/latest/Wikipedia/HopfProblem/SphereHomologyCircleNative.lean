import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircle
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.RingTheory.Finiteness.Basic

/-!
# Actual integral homology of the complex unit circle

The exponential homeomorphism identifies Mathlib's native complex unit
circle with the real quotient circle whose singular homology has already
been computed. The comparison maps below are the actual induced maps on
singular homology. Degree zero uses the native augmentation, degree one
uses the proved circle Mayer--Vietoris marking, and all higher groups
vanish. Every actual homology group is free and finitely generated.
-/

noncomputable section

open CategoryTheory Limits
open scoped ContinuousMap

namespace Wikipedia.HopfProblem.SphereHomology

open SingularMayerVietoris PeriodTorusHigherHomology

/-- The native complex unit circle and the actual quotient `ℝ / ℤ`. -/
def unitCircleAddCircleHomeomorph : _root_.Circle ≃ₜ CircleTopology.Circle :=
  (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm

/-- The inverse comparison is the actual exponential map on the quotient. -/
@[simp] theorem unitCircleAddCircleHomeomorph_symm_apply (x : CircleTopology.Circle) :
    unitCircleAddCircleHomeomorph.symm x = AddCircle.toCircle x :=
  AddCircle.homeomorphCircle_apply one_ne_zero x

/-- The actual native singular homology comparison in every degree. -/
def unitCircleHomologyEquiv (n : ℕ) :
    SingularHomology _root_.Circle n ≃ₗ[ℤ] SingularHomology CircleTopology.Circle n :=
  homeomorphHomologyEquiv unitCircleAddCircleHomeomorph n

@[simp] theorem unitCircleHomologyEquiv_apply (n : ℕ)
    (a : SingularHomology _root_.Circle n) :
    unitCircleHomologyEquiv n a =
      singularHomologyMap
        (unitCircleAddCircleHomeomorph : C(_root_.Circle, CircleTopology.Circle)) n a := rfl

@[simp] theorem unitCircleHomologyEquiv_symm_apply (n : ℕ)
    (a : SingularHomology CircleTopology.Circle n) :
    (unitCircleHomologyEquiv n).symm a =
      singularHomologyMap
        (unitCircleAddCircleHomeomorph.symm : C(CircleTopology.Circle, _root_.Circle)) n a := rfl

/-- Native degree-zero homology with its actual augmentation marking. -/
def unitCircleHomologyZeroEquiv : SingularHomology _root_.Circle 0 ≃ₗ[ℤ] ℤ :=
  connectedHomologyZeroEquiv _root_.Circle

/-- The augmentation agrees with transport through the actual circle homeomorphism. -/
theorem unitCircleHomologyZeroEquiv_apply (a : SingularHomology _root_.Circle 0) :
    unitCircleHomologyZeroEquiv a =
      circleHomologyZeroEquiv (unitCircleHomologyEquiv 0 a) :=
  (connectedHomologyZeroEquiv_natural
    (unitCircleAddCircleHomeomorph : C(_root_.Circle, CircleTopology.Circle)) a).symm

@[simp] theorem unitCircleHomologyZeroEquiv_pointClass (x : _root_.Circle) :
    unitCircleHomologyZeroEquiv (pointClass x) = 1 :=
  connectedHomologyZeroEquiv_pointClass x

/-- The actual degree-one group, marked by the proved quotient-circle generator. -/
def unitCircleHomologyOneEquiv : SingularHomology _root_.Circle 1 ≃ₗ[ℤ] ℤ :=
  (unitCircleHomologyEquiv 1).trans circleHomologyOneEquiv

/-- This marking applies the actual induced homeomorphism map before the known marking. -/
theorem unitCircleHomologyOneEquiv_apply (a : SingularHomology _root_.Circle 1) :
    unitCircleHomologyOneEquiv a =
      circleHomologyOneEquiv (unitCircleHomologyEquiv 1 a) := rfl

/-- Its inverse uses the actual map induced by the exponential homeomorphism. -/
theorem unitCircleHomologyOneEquiv_symm_apply (k : ℤ) :
    unitCircleHomologyOneEquiv.symm k =
      singularHomologyMap
        (unitCircleAddCircleHomeomorph.symm : C(CircleTopology.Circle, _root_.Circle)) 1
        (circleHomologyOneEquiv.symm k) := rfl

/-- Every actual homology group of the complex unit circle above degree one is trivial. -/
theorem unitCircle_homology_subsingleton (n : ℕ) :
    Subsingleton (SingularHomology _root_.Circle (n + 2)) := by
  let := circle_homology_subsingleton n
  exact (unitCircleHomologyEquiv (n + 2)).injective.subsingleton

theorem unitCircle_homology_isZero (n : ℕ) :
    IsZero (SingularHomology _root_.Circle (n + 2)) := by
  let := unitCircle_homology_subsingleton n
  exact ModuleCat.isZero_of_subsingleton _

/-- Higher actual homology is equivalent to the zero free module. -/
def unitCircleHomologyHigherEquivZero (n : ℕ) :
    SingularHomology _root_.Circle (n + 2) ≃ₗ[ℤ] (Fin 0 → ℤ) :=
  (unitCircleHomologyEquiv (n + 2)).trans (circleHomologyHigherEquivZero n)

/-- All native integral homology groups of the unit circle are free. -/
theorem unitCircle_homology_free : (n : ℕ) →
    Module.Free ℤ (SingularHomology _root_.Circle n)
  | 0 => Module.Free.of_equiv unitCircleHomologyZeroEquiv.symm
  | 1 => Module.Free.of_equiv unitCircleHomologyOneEquiv.symm
  | n + 2 => Module.Free.of_equiv (unitCircleHomologyHigherEquivZero n).symm

/-- All native integral homology groups of the unit circle are finitely generated. -/
theorem unitCircle_homology_finite : (n : ℕ) →
    Module.Finite ℤ (SingularHomology _root_.Circle n)
  | 0 => Module.Finite.of_surjective unitCircleHomologyZeroEquiv.symm.toLinearMap
      unitCircleHomologyZeroEquiv.symm.surjective
  | 1 => Module.Finite.of_surjective unitCircleHomologyOneEquiv.symm.toLinearMap
      unitCircleHomologyOneEquiv.symm.surjective
  | n + 2 => Module.Finite.of_surjective (unitCircleHomologyHigherEquivZero n).symm.toLinearMap
      (unitCircleHomologyHigherEquivZero n).symm.surjective

end Wikipedia.HopfProblem.SphereHomology
