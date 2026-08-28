import Wikipedia.HopfProblem.HolomorphicPicardCechExtensionBasic
import Mathlib.Algebra.Homology.ShortComplex.Basic
import Mathlib.Topology.Sheaves.Abelian

/-!
# The kernel and degree maps of the cocycle extension presheaf

The given sheaf maps to degree-zero compatible data by literal
restriction. Projection to the lifted integer coordinate gives the
actual quotient-presheaf map. Their composite is zero on the nose.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory

namespace Wikipedia.HopfProblem.HolomorphicPicard.CechExtension

open HolomorphicFunctionSheaf.SphereH1

variable {X : TopCat.{0}} {F : TopCat.Sheaf AddCommGrpCat.{0} X}
  {ι : Type} {U : ι → Opens X} (c : CechOneCocycle F U)

/-- A section of the original sheaf is included as its compatible
degree-zero family of literal restrictions. -/
def includeHom (V : Opens X) : Section F V →+ ExtensionSection c V where
  toFun a := ⟨⟨0, fun _ => res F inf_le_left a⟩, by
    intro i j
    change res F _ (res F _ a) - res F _ (res F _ a) =
      (0 : ℤ) • res F _ (c.value i j)
    simp only [res_trans, sub_self, zero_zsmul]⟩
  map_zero' := by
    apply extensionSection_ext
    · rfl
    · intro i
      exact map_zero _
  map_add' a b := by
    apply extensionSection_ext
    · rfl
    · intro i
      exact map_add _ _ _

@[simp] theorem includeHom_degree (V : Opens X) (a : Section F V) :
    degreeHom c V (includeHom c V a) = 0 := rfl

@[simp] theorem includeHom_coordinate (V : Opens X) (i : ι) (a : Section F V) :
    coordinateHom c V i (includeHom c V a) = res F inf_le_left a := rfl

theorem restrict_includeHom {V W : Opens X} (hWV : W ≤ V) (a : Section F V) :
    restrict c hWV (includeHom c V a) = includeHom c W (res F hWV a) := by
  apply extensionSection_ext
  · rfl
  · intro i
    change res F _ (res F _ a) = res F _ (res F _ a)
    rw [res_trans, res_trans]

/-- Inclusion of the actual original presheaf into the extension data. -/
def inclusionPre : F.obj ⟶ presheaf c where
  app V := AddCommGrpCat.ofHom (includeHom c V.unop)
  naturality V W f := by
    apply ConcreteCategory.hom_ext
    intro a
    exact (restrict_includeHom c (leOfHom f.unop) a).symm

/-- The literal constant lifted-integer presheaf, not a substitute for
the constant sheaf that will result from sheafification. -/
def degreePresheaf (X : TopCat.{0}) : TopCat.Presheaf AddCommGrpCat.{0} X :=
  (Functor.const (Opens X)ᵒᵖ).obj (AddCommGrpCat.of (ULift.{0} ℤ))

/-- The quotient-presheaf map is actual degree projection. -/
def projectionPre : presheaf c ⟶ degreePresheaf X where
  app V := AddCommGrpCat.ofHom (degreeHom c V.unop)
  naturality _ _ _ := by
    apply ConcreteCategory.hom_ext
    intro s
    rfl

@[simp] theorem inclusionPre_app (V : Opens X) (a : Section F V) :
    (inclusionPre c).app (op V) a = includeHom c V a := rfl

@[simp] theorem projectionPre_app (V : Opens X) (s : ExtensionSection c V) :
    (projectionPre c).app (op V) s = degreeHom c V s := rfl

theorem inclusionPre_projectionPre : inclusionPre c ≫ projectionPre c = 0 := by
  apply NatTrans.ext
  funext V
  apply ConcreteCategory.hom_ext
  intro a
  rfl

/-- The actual short complex of presheaves attached to the cocycle. -/
def presheafComplex : ShortComplex (TopCat.Presheaf AddCommGrpCat.{0} X) :=
  ShortComplex.mk (inclusionPre c) (projectionPre c) (inclusionPre_projectionPre c)

end Wikipedia.HopfProblem.HolomorphicPicard.CechExtension
