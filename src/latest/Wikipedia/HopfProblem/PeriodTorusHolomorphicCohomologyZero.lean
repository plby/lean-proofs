import Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomologyBasic
import Mathlib.Geometry.Manifold.Complex

/-!
# Degree zero of the actual holomorphic sheaf on every period torus

The compact connected native torus has only constant holomorphic
functions. Evaluation and Mathlib's genuine degree-zero comparison
give a complex-linear equivalence from its actual sheaf cohomology
to the complex numbers, with the literal constant-section inverse.
-/

noncomputable section

open CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomology

local notation "I₂" => modelWithCornersSelf ℂ ComplexPlane₂

/-- Constancy is proved for genuine holomorphic maps in the unchanged quotient atlas. -/
theorem holomorphic_apply_eq (p : PeriodDomain) (f : HolomorphicFunction p)
    (x y : p.Torus) : f x = f y :=
  (f.contMDiff.mdifferentiable (by simp)).apply_eq_of_compactSpace x y

/-- Literal evaluation of actual holomorphic functions is an algebra map. -/
def holomorphicEval (p : PeriodDomain) (x : p.Torus) : HolomorphicFunction p →ₐ[ℂ] ℂ where
  toFun f := f x
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

@[simp] theorem holomorphicEval_apply (p : PeriodDomain) (x : p.Torus)
    (f : HolomorphicFunction p) : holomorphicEval p x f = f x := rfl

/-- Compactness and connectedness make actual evaluation bijective. -/
def holomorphicEvalEquiv (p : PeriodDomain) (x : p.Torus) :
    HolomorphicFunction p ≃ₐ[ℂ] ℂ :=
  AlgEquiv.ofBijective (holomorphicEval p x) ⟨by
    intro f g h
    apply ContMDiffMap.ext
    intro y
    exact (holomorphic_apply_eq p f y x).trans
      (h.trans (holomorphic_apply_eq p g x y)), by
    intro c
    exact ⟨ContMDiffMap.const c, rfl⟩⟩

@[simp] theorem holomorphicEvalEquiv_apply (p : PeriodDomain) (x : p.Torus)
    (f : HolomorphicFunction p) : holomorphicEvalEquiv p x f = f x := rfl

@[simp] theorem holomorphicEvalEquiv_symm_apply (p : PeriodDomain) (x : p.Torus) (c : ℂ) :
    (holomorphicEvalEquiv p x).symm c = ContMDiffMap.const c := by
  apply (holomorphicEvalEquiv p x).injective
  rw [AlgEquiv.apply_symm_apply, holomorphicEvalEquiv_apply]
  rfl

/-- Evaluation of genuine global sheaf sections, not a dimension marking. -/
def globalEvalEquiv (p : PeriodDomain) (x : p.Torus) : GlobalSections p ≃ₐ[ℂ] ℂ :=
  (HolomorphicFunctionSheaf.globalSectionsAlgEquiv I₂ p.Torus).trans
    (holomorphicEvalEquiv p x)

@[simp] theorem globalEvalEquiv_apply (p : PeriodDomain) (x : p.Torus)
    (s : GlobalSections p) :
    globalEvalEquiv p x s = s (HolomorphicFunctionSheaf.toTopOpen p.Torus x) := rfl

@[simp] theorem globalEvalEquiv_symm_apply (p : PeriodDomain) (x : p.Torus) (c : ℂ) :
    (globalEvalEquiv p x).symm c = algebraMap ℂ (GlobalSections p) c := by
  apply (globalEvalEquiv p x).injective
  rw [AlgEquiv.apply_symm_apply, AlgEquiv.commutes]
  rfl

/-- The canonical Ext-zero/global-section comparison is linear for the sheaf-induced action. -/
def h0GlobalLinearEquiv (p : PeriodDomain) : H p 0 ≃ₗ[ℂ] GlobalSections p where
  __ := HolomorphicFunctionSheaf.h0GlobalAddEquiv I₂ p.Torus
  map_smul' c a :=
    (CategoryTheory.Sheaf.H.equiv₀_naturality
      (show CategoryTheory.Limits.IsTerminal
        (⊤ : TopologicalSpace.Opens (TopCat.of p.Torus)) from
          CategoryTheory.Limits.isTerminalTop)
      (HolomorphicFunctionSheaf.scalarSheafEnd I₂ p.Torus c) a).symm

@[simp] theorem h0GlobalLinearEquiv_apply (p : PeriodDomain) (a : H p 0) :
    h0GlobalLinearEquiv p a = HolomorphicFunctionSheaf.h0GlobalAddEquiv I₂ p.Torus a := rfl

/-- Genuine degree-zero holomorphic cohomology is identified by evaluation at the origin. -/
def h0Equiv (p : PeriodDomain) : H p 0 ≃ₗ[ℂ] ℂ :=
  (h0GlobalLinearEquiv p).trans (globalEvalEquiv p 0).toLinearEquiv

/-- The degree-zero class corresponding to a literal constant section. -/
def h0Constant (p : PeriodDomain) (c : ℂ) : H p 0 :=
  (h0GlobalLinearEquiv p).symm (algebraMap ℂ (GlobalSections p) c)

@[simp] theorem h0Equiv_constant (p : PeriodDomain) (c : ℂ) :
    h0Equiv p (h0Constant p c) = c := by
  change globalEvalEquiv p 0
    (h0GlobalLinearEquiv p
      ((h0GlobalLinearEquiv p).symm (algebraMap ℂ (GlobalSections p) c))) = c
  rw [LinearEquiv.apply_symm_apply, AlgEquiv.commutes]
  rfl

@[simp] theorem h0Equiv_symm_apply (p : PeriodDomain) (c : ℂ) :
    (h0Equiv p).symm c = h0Constant p c := by
  apply (h0Equiv p).injective
  rw [LinearEquiv.apply_symm_apply, h0Equiv_constant]

/-- The dimension assertion is a consequence of the genuine constant-section comparison. -/
theorem h0_finrank (p : PeriodDomain) : Module.finrank ℂ (H p 0) = 1 := by
  rw [(h0Equiv p).finrank_eq]
  exact Module.finrank_self ℂ

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomology
