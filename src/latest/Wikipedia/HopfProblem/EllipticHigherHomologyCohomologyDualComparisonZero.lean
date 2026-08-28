import Wikipedia.HopfProblem.EllipticHigherHomologyDeckCoinvariantsZero
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.Data.ZMod.QuotientGroup

/-!
# The actual degree-zero period-cover dual isomorphism

The proved degree-zero isomorphism of the actual descended period cover
dualizes to an actual integral linear equivalence.  Consequently its
dual image has index one and its actual cokernel is zero, equivalently
`ZMod 1`.  No degree-zero coordinate or map formula is assumed.
-/

noncomputable section

namespace Wikipedia.HopfProblem.Elliptic.HigherHomology

open SingularMayerVietoris

/-- The dual of the genuine degree-zero covering equivalence. -/
def periodCoverDeckDualH0Equiv (j : Kind) (p : FixedPeriod j) :
    Module.Dual ℤ (SingularHomology (Surface j p j.twist (mainTwist_admissible j)) 0) ≃ₗ[ℤ]
      Module.Dual ℤ (PeriodDeckCoinvariants j p 0) :=
  (periodCoverFromDeckCoinvariantsH0Equiv j p).dualMap

@[simp] theorem periodCoverDeckDualH0Equiv_apply (j : Kind) (p : FixedPeriod j)
    (φ : Module.Dual ℤ
      (SingularHomology (Surface j p j.twist (mainTwist_admissible j)) 0)) :
    periodCoverDeckDualH0Equiv j p φ =
      (periodCoverFromDeckCoinvariants j p 0).dualMap φ := rfl

@[simp] theorem periodCoverDeckDualH0Equiv_toLinearMap (j : Kind) (p : FixedPeriod j) :
    (periodCoverDeckDualH0Equiv j p).toLinearMap =
      (periodCoverFromDeckCoinvariants j p 0).dualMap := rfl

theorem periodCoverDeckDual_h0_bijective (j : Kind) (p : FixedPeriod j) :
    Function.Bijective (periodCoverFromDeckCoinvariants j p 0).dualMap :=
  (periodCoverDeckDualH0Equiv j p).bijective

theorem periodCoverDeckDual_h0_range_eq_top (j : Kind) (p : FixedPeriod j) :
    LinearMap.range (periodCoverFromDeckCoinvariants j p 0).dualMap = ⊤ :=
  LinearMap.range_eq_top.mpr (periodCoverDeckDual_h0_bijective j p).surjective

theorem periodCoverDeckDual_h0_range_index (j : Kind) (p : FixedPeriod j) :
    (LinearMap.range (periodCoverFromDeckCoinvariants j p 0).dualMap).toAddSubgroup.index = 1 := by
  rw [periodCoverDeckDual_h0_range_eq_top]
  simp

theorem periodCoverDeckDual_h0_cokernel_subsingleton (j : Kind) (p : FixedPeriod j) :
    Subsingleton (Module.Dual ℤ (PeriodDeckCoinvariants j p 0) ⧸
      LinearMap.range (periodCoverFromDeckCoinvariants j p 0).dualMap) :=
  Submodule.Quotient.subsingleton_iff.mpr (periodCoverDeckDual_h0_range_eq_top j p)

/-- The actual degree-zero dual cokernel, in the same residue format as the other degrees. -/
def periodCoverDeckDualH0CokernelEquivZMod (j : Kind) (p : FixedPeriod j) :
    (Module.Dual ℤ (PeriodDeckCoinvariants j p 0) ⧸
      LinearMap.range (periodCoverFromDeckCoinvariants j p 0).dualMap) ≃ₗ[ℤ] ZMod 1 := by
  letI := periodCoverDeckDual_h0_cokernel_subsingleton j p
  exact LinearEquiv.ofSubsingleton _ _

@[simp] theorem periodCoverDeckDualH0CokernelEquivZMod_apply_mk
    (j : Kind) (p : FixedPeriod j) (φ : Module.Dual ℤ (PeriodDeckCoinvariants j p 0)) :
    periodCoverDeckDualH0CokernelEquivZMod j p (Submodule.Quotient.mk φ) = 0 :=
  Subsingleton.elim _ _

theorem periodCoverDeckDual_h0_cokernel_eq_zero (j : Kind) (p : FixedPeriod j)
    (a : Module.Dual ℤ (PeriodDeckCoinvariants j p 0) ⧸
      LinearMap.range (periodCoverFromDeckCoinvariants j p 0).dualMap) : a = 0 := by
  let := periodCoverDeckDual_h0_cokernel_subsingleton j p
  exact Subsingleton.elim _ _

end Wikipedia.HopfProblem.Elliptic.HigherHomology
