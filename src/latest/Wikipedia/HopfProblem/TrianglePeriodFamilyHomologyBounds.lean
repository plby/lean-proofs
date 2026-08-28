import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologySourceSequence
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyTorusGroupsPeriod

/-!
# Degree-zero and high-degree bounds for actual regular-family homology

The actual fibre map is an isomorphism on degree-zero singular homology:
the cover endpoint gives surjectivity, and the proved source-difference
kernel is zero. Above degree five the two torus terms in the actual
source exact sequence vanish, forcing the actual family homology to vanish.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Homology

open SpecialPeriods SingularMayerVietoris PeriodTorusHigherHomology
open CategoryTheory CategoryTheory.Limits

variable (D : Data ℂ TriangleRegularPoint)

/-- Every actual degree-zero family class comes from any chosen fibre marking. -/
theorem familyFibreInclusion_zero_surjective (b : SlitBaseLift) :
    Function.Surjective (singularHomologyMap (familyFibreInclusion D b) 0) := by
  intro a
  have ha : a ∈ LinearMap.range (familyRightHomologyMap D 0) :=
    familyRightHomologyMap_zero_surjective D a
  rw [familyRightHomologyMap_range_eq_fibre D b 0] at ha
  exact ha

/-- The normalized actual fibre has zero kernel in degree zero. -/
theorem familyFibreInclusion_zero_injective :
    Function.Injective
      (singularHomologyMap (familyFibreInclusion D normalizedSlitBaseLift) 0) := by
  apply LinearMap.ker_eq_bot.mp
  rw [familyFibreInclusion_kernel, sourceDifference_zero, LinearMap.range_zero]

/-- The actual degree-zero fibre map is an integral linear equivalence. -/
def familyFibreHomologyZeroEquiv :
    SingularHomology RealTorus₄ 0 ≃ₗ[ℤ] SingularHomology D.Space 0 :=
  LinearEquiv.ofBijective
    (singularHomologyMap (familyFibreInclusion D normalizedSlitBaseLift) 0)
    ⟨familyFibreInclusion_zero_injective D,
      familyFibreInclusion_zero_surjective D normalizedSlitBaseLift⟩

@[simp] theorem familyFibreHomologyZeroEquiv_apply
    (a : SingularHomology RealTorus₄ 0) :
    familyFibreHomologyZeroEquiv D a =
      singularHomologyMap (familyFibreInclusion D normalizedSlitBaseLift) 0 a := rfl

/-- The actual degree-zero singular homology of the regular family is the integers. -/
def familyH0Equiv : SingularHomology D.Space 0 ≃ₗ[ℤ] ℤ :=
  (familyFibreHomologyZeroEquiv D).symm.trans (connectedHomologyZeroEquiv RealTorus₄)

/-- The degree-zero marking sends the actual fibre map to the torus augmentation. -/
@[simp] theorem familyH0Equiv_fibre (a : SingularHomology RealTorus₄ 0) :
    familyH0Equiv D
        (singularHomologyMap (familyFibreInclusion D normalizedSlitBaseLift) 0 a) =
      connectedHomologyZeroEquiv RealTorus₄ a := by
  change connectedHomologyZeroEquiv RealTorus₄
    ((familyFibreHomologyZeroEquiv D).symm (familyFibreHomologyZeroEquiv D a)) = _
  rw [LinearEquiv.symm_apply_apply]

/-- The inverse integer marking is the actual fibre map applied to the inverse augmentation. -/
@[simp] theorem familyH0Equiv_symm_apply (z : ℤ) :
    (familyH0Equiv D).symm z =
      singularHomologyMap (familyFibreInclusion D normalizedSlitBaseLift) 0
        ((connectedHomologyZeroEquiv RealTorus₄).symm z) := rfl

/-- Every point of the marked actual fibre represents the positive generator. -/
@[simp] theorem familyH0Equiv_fibre_point (f : RealTorus₄) :
    familyH0Equiv D (pointClass (D.quotient (normalizedSlitBaseLift.val, f))) = 1 := by
  have h := familyH0Equiv_fibre D (pointClass f)
  rw [singularHomologyMap_pointClass, familyFibreInclusion_apply,
    connectedHomologyZeroEquiv_pointClass] at h
  exact h

/-- The actual regular-family singular homology vanishes in every degree above five. -/
theorem family_homology_subsingleton_of_lt {n : ℕ} (hn : 5 < n) :
    Subsingleton (SingularHomology D.Space n) := by
  cases n with
  | zero => omega
  | succ m =>
      let := realTorus_homology_subsingleton_of_lt (n := m) (by omega)
      let := realTorus_homology_subsingleton_of_lt (n := m + 1) (by omega)
      have hz (x : SingularHomology D.Space (m + 1)) : x = 0 := by
        obtain ⟨q, hq⟩ := (sourceCoinvariantInclusion_kernelProjection_exact D m x).mp
          (Subsingleton.elim _ _)
        have hq0 : q = 0 := Subsingleton.elim _ _
        simpa only [hq0, map_zero] using hq.symm
      exact ⟨fun x y => (hz x).trans (hz y).symm⟩

/-- Every actual family homology class above the stated bound is zero. -/
theorem family_homology_eq_zero_of_lt {n : ℕ} (hn : 5 < n)
    (a : SingularHomology D.Space n) : a = 0 := by
  let := family_homology_subsingleton_of_lt D hn
  exact Subsingleton.elim _ _

/-- Categorical vanishing of the actual singular-homology object above degree five. -/
theorem family_homology_isZero_of_lt {n : ℕ} (hn : 5 < n) :
    IsZero (SingularHomology D.Space n) := by
  let := family_homology_subsingleton_of_lt D hn
  exact ModuleCat.isZero_of_subsingleton _

end Wikipedia.HopfProblem.TrianglePeriodFamily.Homology
