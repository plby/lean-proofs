import Wikipedia.NoExoticSixSphere.ModTwoCapProduct
import Wikipedia.HopfProblem.SingularCohomologyFreeCycles

/-!
# Integer enrichment of the original mod-two cochain complex

The cochains and differentials are the original additive cochains and
boundary-precomposition maps. Giving these abelian groups their canonical
integer-module structures permits the existing categorical cycle-quotient
API to be used. Forgetting that structure gives back the original cochain
complex definitionally.
-/

noncomputable section

open CategoryTheory
open Wikipedia.HopfProblem FirstHurewicz

namespace NoExoticSixSphere.ModTwoCapProduct

variable (X : Type) [TopologicalSpace X]

/-- The original mod-two cochain complex with its canonical integer-module structure. -/
def cochainComplex : CochainComplex (ModuleCat.{0} ℤ) ℕ where
  X n := ModuleCat.of ℤ (Cochain X n)
  d i j := ModuleCat.ofHom (ConstantSheafSingularComparison.addHomToIntLinearMap
    (ConstantSheafSingularComparison.dualDifferential (singularComplex X)
      (AddCommGrpCat.of (ZMod 2)) i j))
  shape i j hij := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro α
    apply AddMonoidHom.ext
    intro c
    change α (((singularComplex X).d j i).hom c) = 0
    rw [(singularComplex X).shape j i hij]
    exact α.map_zero
  d_comp_d' i j k _ _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro α
    apply AddMonoidHom.ext
    intro c
    change α (((singularComplex X).d j i).hom (((singularComplex X).d k j).hom c)) = 0
    have he := congrArg (fun f : Chains X k ⟶ Chains X i => f.hom c)
      ((singularComplex X).d_comp_d k j i)
    exact (congrArg α he).trans α.map_zero

/-- Forgetting integer scalars gives exactly the original additive singular cochain complex. -/
theorem forget_cochainComplex :
    ((forget₂ (ModuleCat.{0} ℤ) AddCommGrpCat).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj (cochainComplex X) =
      ConstantSheafSingularComparison.singularCochainComplex X (AddCommGrpCat.of (ZMod 2)) := rfl

/-- This differential is the same coboundary used in the original cap formula. -/
theorem cochainComplex_coboundary (p : ℕ) (α : Cochain X p) :
    ((cochainComplex X).d p (p + 1)).hom α = coboundary α := rfl

/-- Actual cohomology of the original mod-two singular cochain complex. -/
abbrev Cohomology (p : ℕ) := (cochainComplex X).homology p

/-- The original concrete cocycle kernel, not a prescribed cohomology model. -/
abbrev Cocycle (p : ℕ) := SingularCohomologyFree.Cocycle (cochainComplex X) p

theorem cocycle_coboundary_zero (p : ℕ) (α : Cocycle X p) : coboundary α.val = 0 :=
  SingularCohomologyFree.cocycle_condition (cochainComplex X) p α

/-- The original coboundary squares to zero. -/
theorem coboundary_squared (p : ℕ) (α : Cochain X p) : coboundary (coboundary α) = 0 :=
  congrArg (fun f : (cochainComplex X).X p ⟶ (cochainComplex X).X (p + 2) => f.hom α)
    ((cochainComplex X).d_comp_d p (p + 1) (p + 2))

theorem coboundary_zero (p : ℕ) : coboundary (0 : Cochain X p) = 0 :=
  map_zero ((cochainComplex X).d p (p + 1)).hom

end NoExoticSixSphere.ModTwoCapProduct
