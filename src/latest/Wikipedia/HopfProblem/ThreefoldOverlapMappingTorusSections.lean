import Wikipedia.HopfProblem.ThreefoldOverlapMappingTorusSpaces
import Wikipedia.HopfProblem.ThreefoldOverlapMappingTorusEllipticSection

/-!
# Actual sections and fibre inclusions on the three boundary models

The cusp section uses the fixed zero of the original linear torus action.
The elliptic sections use the proved negative twist paths, so that their
endpoints close under the actual affine monodromy.  Composing with the
constructed boundary maps gives genuine sections in the original pieces.
-/

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace Wikipedia.HopfProblem.ThreefoldOverlapMappingTorus

open SpecialPeriods SpecialPeriods.Threefold

/-- The actual zero-coordinate section on the real cusp cylinder. -/
def cuspSectionCylinder : C(ℝ, Boundary none) :=
  ⟨fun t => MappingTorus.mk (monodromy none) (t, 0),
    (MappingTorus.mk_continuous _).comp (continuous_id.prodMk continuous_const)⟩

theorem cuspSectionCylinder_periodic : Function.Periodic cuspSectionCylinder 1 := by
  intro t
  change MappingTorus.mk (monodromy none) (t + 1, 0) =
    MappingTorus.mk (monodromy none) (t, 0)
  rw [MappingTorus.mk_add_one]
  exact congrArg (fun x => MappingTorus.mk (monodromy none) (t, x))
    (CuspFamily.cuspTorusHomeomorph_zero 1)

/-- The actual cusp boundary section, descended through its circle quotient. -/
def cuspBoundarySection : C(MappingTorus.Circle, Boundary none) where
  toFun := cuspSectionCylinder_periodic.lift
  continuous_toFun := by
    apply (QuotientAddGroup.isQuotientMap_mk (AddSubgroup.zmultiples (1 : ℝ))).continuous_iff.mpr
    exact cuspSectionCylinder.continuous

@[simp] theorem cuspBoundarySection_coe (t : ℝ) :
    cuspBoundarySection (t : MappingTorus.Circle) =
      MappingTorus.mk (monodromy none) (t, 0) := rfl

/-- All three sections are actual maps for the original monodromies. -/
def boundarySection (i : Puncture) : C(MappingTorus.Circle, Boundary i) := by
  cases i with
  | none => exact cuspBoundarySection
  | some j => exact Elliptic.boundarySection j j.twist j.matrix_fixes_twist

@[simp] theorem boundarySection_base (i : Puncture) (t : MappingTorus.Circle) :
    MappingTorus.base (monodromy i) (boundarySection i t) = t := by
  cases i with
  | none =>
      obtain ⟨s, rfl⟩ := QuotientAddGroup.mk_surjective t
      rfl
  | some j => exact Elliptic.boundarySection_base j j.twist j.matrix_fixes_twist t

@[simp] theorem boundarySection_zero (i : Puncture) :
    boundarySection i 0 = MappingTorus.HomologyCover.fibreInclusion (monodromy i) 0 := by
  cases i with
  | none => rfl
  | some j => exact Elliptic.boundarySection_zero j j.twist j.matrix_fixes_twist

/-- The original regular-family section curve obtained from the true boundary section. -/
def sectionToRegularFamily (i : Puncture) : C(MappingTorus.Circle, SpecialRegularFamily) :=
  (boundaryToRegularFamily i).comp (boundarySection i)

/-- The same actual section curve in the original filling piece. -/
def sectionToFilling (i : Puncture) : C(MappingTorus.Circle, localPiece (some i)) :=
  (boundaryToFilling i).comp (boundarySection i)

@[simp] theorem sectionToRegularFamily_zero (i : Puncture) :
    sectionToRegularFamily i 0 = fibreToRegularFamily i 0 :=
  congrArg (boundaryToRegularFamily i) (boundarySection_zero i)

@[simp] theorem sectionToFilling_zero (i : Puncture) :
    sectionToFilling i 0 = fibreToFilling i 0 :=
  congrArg (boundaryToFilling i) (boundarySection_zero i)

end Wikipedia.HopfProblem.ThreefoldOverlapMappingTorus
