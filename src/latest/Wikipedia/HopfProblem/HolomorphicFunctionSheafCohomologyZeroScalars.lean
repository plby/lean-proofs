import Wikipedia.HopfProblem.HolomorphicFunctionSheafCohomologyZeroBasic

/-!
# The actual scalar sheaf maps induce the scalar action on degree zero

Multiplication by a complex constant is an endomorphism of the actual
additive holomorphic-function sheaf.  Its naturality is the literal
compatibility of pointwise scalar multiplication with restriction.
Naturality of mathlib's degree-zero cohomology comparison then identifies
the induced map with the transported complex scalar action on `H0`.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicFunctionSheaf

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
  (M : Type) [TopologicalSpace M] [ChartedSpace H M]

/-- Pointwise multiplication by a complex constant on the actual additive
holomorphic-function sheaf. -/
def scalarSheafEnd (c : ℂ) : additiveSheaf I M ⟶ additiveSheaf I M where
  hom :=
    { app := fun U => AddCommGrpCat.ofHom
        ({ toFun := fun f => c • f
           map_zero' := smul_zero c
           map_add' := smul_add c } : Section I M U.unop →+ Section I M U.unop)
      naturality := fun U V h => by
        apply AddCommGrpCat.hom_ext
        apply AddMonoidHom.ext
        intro f
        apply ContMDiffMap.ext
        intro x
        rfl }

@[simp] theorem scalarSheafEnd_apply (c : ℂ)
    (U : (Opens (TopCat.of M))ᵒᵖ) (f : (additiveSheaf I M).presheaf.obj U) :
    (scalarSheafEnd I M c).hom.app U f = c • f := rfl

@[simp] theorem scalarSheafEnd_zero : scalarSheafEnd I M 0 = 0 := by
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro f
  exact zero_smul ℂ f

@[simp] theorem scalarSheafEnd_one : scalarSheafEnd I M 1 = 𝟙 (additiveSheaf I M) := by
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro f
  exact one_smul ℂ f

theorem scalarSheafEnd_add (c d : ℂ) :
    scalarSheafEnd I M (c + d) = scalarSheafEnd I M c + scalarSheafEnd I M d := by
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro f
  exact add_smul c d f

theorem scalarSheafEnd_mul (c d : ℂ) :
    scalarSheafEnd I M (c * d) = scalarSheafEnd I M d ≫ scalarSheafEnd I M c := by
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro f
  exact mul_smul c d f

/-- The actual cohomology map induced by the scalar sheaf endomorphism
is the complex scalar action on genuine degree-zero sheaf cohomology. -/
@[simp] theorem h0_map_scalarSheafEnd (c : ℂ) (x : H0 I M) :
    CategoryTheory.Sheaf.H.map (scalarSheafEnd I M c) 0 x = c • x := by
  apply (h0GlobalAddEquiv I M).injective
  rw [h0GlobalAddEquiv_smul]
  exact (CategoryTheory.Sheaf.H.equiv₀_naturality
    (hT := (show Limits.IsTerminal (⊤ : Opens (TopCat.of M)) from Limits.isTerminalTop))
    (scalarSheafEnd I M c) x).symm

end Wikipedia.HopfProblem.HolomorphicFunctionSheaf
