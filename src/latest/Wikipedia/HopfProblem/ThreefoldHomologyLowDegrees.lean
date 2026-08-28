import Wikipedia.HopfProblem.ThreefoldFundamentalGroup
import Wikipedia.HopfProblem.FirstHurewiczEquivalence
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCirclePointClass
import Mathlib.Algebra.Module.Projective

/-!
# Actual integral homology of the threefold in degrees zero and one

The degree-zero equivalence is the genuine singular augmentation, with
the class of every actual point sent to one.  The degree-one statement
uses the proved first Hurewicz theorem: every actual singular homology
class comes from a based loop, and the constructed threefold's simple
connectedness contracts that loop.

No higher homology group, projectivity hypothesis in another degree, or
evaluation of the remaining boundary matrices is used.
-/

noncomputable section

open CategoryTheory Limits

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.LowDegrees

open SingularMayerVietoris PeriodTorusHigherHomology

/-- The actual integral singular augmentation is an equivalence in degree zero. -/
def singularH0Equiv : SingularHomology Space 0 ≃ₗ[ℤ] ℤ := by
  have := space_pathConnected
  exact connectedHomologyZeroEquiv Space

@[simp] theorem singularH0Equiv_toLinearMap :
    singularH0Equiv.toLinearMap =
      ((TopCat.of Space).singularHomology₀ε (ModuleCat.of ℤ ℤ)).hom := rfl

@[simp] theorem singularH0Equiv_pointClass (x : Space) :
    singularH0Equiv (pointClass x) = 1 := by
  have := space_pathConnected
  exact connectedHomologyZeroEquiv_pointClass x

theorem singularH0Equiv_symm_one (x : Space) :
    singularH0Equiv.symm 1 = pointClass x := by
  apply singularH0Equiv.injective
  rw [LinearEquiv.apply_symm_apply, singularH0Equiv_pointClass]

/-- This is the actual induced map in the augmentation coordinates. -/
theorem singularH0Equiv_natural {X : Type} [TopologicalSpace X] [PathConnectedSpace X]
    (f : C(X, Space)) (a : SingularHomology X 0) :
    singularH0Equiv (singularHomologyMap f 0 a) = connectedHomologyZeroEquiv X a := by
  have := space_pathConnected
  exact connectedHomologyZeroEquiv_natural f a

theorem singularH0_free : Module.Free ℤ (SingularHomology Space 0) :=
  Module.Free.of_equiv singularH0Equiv.symm

theorem singularH0_projective : Module.Projective ℤ (SingularHomology Space 0) := by
  have := singularH0_free
  infer_instance

theorem singularH0_finite : Module.Finite ℤ (SingularHomology Space 0) :=
  Module.Finite.of_surjective singularH0Equiv.symm.toLinearMap singularH0Equiv.symm.surjective

theorem singularH0_finrank : Module.finrank ℤ (SingularHomology Space 0) = 1 := by
  rw [singularH0Equiv.finrank_eq]
  simp

/-- Every genuine integral singular one-class is zero, by actual Hurewicz
surjectivity and the constructed endpoint-preserving loop contractions. -/
theorem singularH1_eq_zero (a : SingularHomology Space 1) : a = 0 := by
  have := space_pathConnected
  obtain ⟨p, hp⟩ := FirstHurewicz.loopHomologyClass_surjective PiOne.basepoint a
  exact hp.symm.trans
    ((FirstHurewicz.loopHomologyClass_homotopic (space_loops_nullhomotopic p)).trans
      (FirstHurewicz.loopHomologyClass_refl PiOne.basepoint))

theorem singularH1_subsingleton : Subsingleton (SingularHomology Space 1) :=
  ⟨fun a b => (singularH1_eq_zero a).trans (singularH1_eq_zero b).symm⟩

theorem singularH1_isZero : IsZero (SingularHomology Space 1) := by
  have := singularH1_subsingleton
  exact ModuleCat.isZero_of_subsingleton _

/-- A linear equivalence with the standard rank-zero integral module. -/
def singularH1EquivZero : SingularHomology Space 1 ≃ₗ[ℤ] (Fin 0 → ℤ) where
  toLinearMap := 0
  invFun _ := 0
  left_inv a := (singularH1_eq_zero a).symm
  right_inv _ := Subsingleton.elim _ _

theorem singularH1_free : Module.Free ℤ (SingularHomology Space 1) := by
  have := singularH1_subsingleton
  infer_instance

theorem singularH1_projective : Module.Projective ℤ (SingularHomology Space 1) := by
  have := singularH1_free
  infer_instance

theorem singularH1_finite : Module.Finite ℤ (SingularHomology Space 1) := by
  have := singularH1_subsingleton
  infer_instance

theorem singularH1_finrank : Module.finrank ℤ (SingularHomology Space 1) = 0 := by
  have := singularH1_subsingleton
  exact Module.finrank_zero_of_subsingleton

/-- In degree one every actual incoming homology map is the zero map. -/
theorem singularH1_map_eq_zero {X : Type} [TopologicalSpace X] (f : C(X, Space)) :
    singularHomologyMap f 1 = 0 := by
  ext a
  exact singularH1_eq_zero _

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.LowDegrees
