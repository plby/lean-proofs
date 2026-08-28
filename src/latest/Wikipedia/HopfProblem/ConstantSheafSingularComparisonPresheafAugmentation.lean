import Wikipedia.HopfProblem.ConstantSheafSingularComparisonPresheafBasic
import Wikipedia.HopfProblem.ConstantSheafFirstCohomologyConstantBasic

/-!
# The actual constant augmentation of singular cochain presheaves

A coefficient value is sent to the degree-zero cochain taking that value
on each original singular vertex.  This assignment is additive, natural
under genuine inclusions and coefficient maps, and has zero coboundary.
-/

noncomputable section

open CategoryTheory Opposite TopologicalSpace

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison

open FirstHurewicz

variable (X : Type) [TopologicalSpace X] (A : AddCommGrpCat.{0})

/-- The actual degree-zero cochain associated to a constant coefficient. -/
def constantCochain : A →+ Cochains X A 0 where
  toFun a := cochainFromValues X A 0 (fun _ => a)
  map_zero' := by
    apply cochain_ext X A 0
    intro σ
    exact cochainFromValues_simplex X A 0 (fun _ => 0) σ
  map_add' a b := by
    apply cochain_ext X A 0
    intro σ
    simp only [AddMonoidHom.add_apply, cochainFromValues_simplex]

@[simp]
theorem constantCochain_simplex (a : A) (σ : SingularSimplex X 0) :
    constantCochain X A a (simplexChain X 0 σ) = a :=
  cochainFromValues_simplex X A 0 (fun _ => a) σ

/-- Every actual constant zero-cochain is closed. -/
theorem constantCochain_d_zero (a : A) :
    (singularCochainComplex X A).d 0 1 (constantCochain X A a) = 0 := by
  apply cochain_ext X A 1
  intro σ
  change constantCochain X A a (boundaryOne X (simplexChain X 1 σ)) = 0
  rw [boundaryOne_simplex, map_sub, constantCochain_simplex, constantCochain_simplex, sub_self]

/-- Nonempty spaces distinguish different constant zero-cochains. -/
theorem constantCochain_injective [Nonempty X] : Function.Injective (constantCochain X A) := by
  intro a b hab
  let x : X := Classical.choice (inferInstance : Nonempty X)
  let σ : SingularSimplex X 0 := ContinuousMap.const (Simplex 0) x
  have h := congrArg (fun φ : Cochains X A 0 => φ (simplexChain X 0 σ)) hab
  exact (constantCochain_simplex X A a σ).symm.trans
    (h.trans (constantCochain_simplex X A b σ))

variable {X} {Y : Type} [TopologicalSpace Y]

/-- The native pullback of a constant cochain is the same constant cochain. -/
theorem singularPullback_constant (f : C(X, Y)) (a : A) :
    (singularPullback A f).f 0 (constantCochain Y A a) = constantCochain X A a := by
  apply cochain_ext X A 0
  intro σ
  exact (singularPullback_simplex A f 0 (constantCochain Y A a) σ).trans
    ((constantCochain_simplex Y A a (f.comp σ)).trans
      (constantCochain_simplex X A a σ).symm)

theorem coefficientMap_constant (X : Type) [TopologicalSpace X]
    {B : AddCommGrpCat.{0}} (α : A ⟶ B) (a : A) :
    (coefficientMap X α).f 0 (constantCochain X A a) = constantCochain X B (α a) := by
  apply cochain_ext X B 0
  intro σ
  exact (congrArg α (constantCochain_simplex X A a σ)).trans
    (constantCochain_simplex X B (α a) σ).symm

/-- The canonical augmentation from the original constant presheaf. -/
def constantAugmentation (X : TopCat.{0}) (A : AddCommGrpCat.{0}) :
    ConstantSheafFirstCohomology.Constant.presheaf X A ⟶
    cochainPresheaf X A 0 where
  app U := AddCommGrpCat.ofHom (constantCochain U.unop A)
  naturality U V i := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro a
    exact (singularPullback_constant A ((Opens.toTopCat X).map i.unop).hom a).symm

@[simp]
theorem constantAugmentation_app (X : TopCat.{0}) (A : AddCommGrpCat.{0})
    (U : Opens X) (a : A) :
    (constantAugmentation X A).app (op U) a = constantCochain U A a := rfl

@[simp]
theorem constantAugmentation_simplex (X : TopCat.{0}) (A : AddCommGrpCat.{0})
    (U : Opens X) (a : A) (σ : SingularSimplex U 0) :
    (constantAugmentation X A).app (op U) a (simplexChain U 0 σ) = a :=
  constantCochain_simplex U A a σ

/-- The genuine augmentation followed by the genuine coboundary is zero. -/
@[reassoc]
theorem constantAugmentation_d (X : TopCat.{0}) (A : AddCommGrpCat.{0}) :
    constantAugmentation X A ≫ presheafDifferential X A 0 1 = 0 := by
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro a
  exact constantCochain_d_zero U.unop A a

end Wikipedia.HopfProblem.ConstantSheafSingularComparison
