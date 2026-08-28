import Wikipedia.HopfProblem.HolomorphicMeromorphicAlgebra

/-!
# The genuine sheaf of commutative rings of meromorphic functions

The ring-valued sheaf has precisely the locally fraction-represented
sections of the original type-valued sheaf. Its restriction maps are
literal restriction, and the original holomorphic function sheaf embeds
by the canonical maps from holomorphic germs to their fraction fields.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicMeromorphic

variable {E H : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
  (M : Type) [TopologicalSpace M] [ChartedSpace H M]
  [I.Boundaryless] [IsManifold I ω M]

/-- The actual meromorphic section rings with literal restriction maps. -/
def presheaf : TopCat.Presheaf CommRingCat (TopCat.of M) where
  obj U := CommRingCat.of (Section I M U.unop)
  map h := CommRingCat.ofHom (restrictionRingHom I M (CategoryTheory.leOfHom h.unop))
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The sheaf condition is the proved local-fraction sheaf condition,
reflected from the underlying sheaf of types. -/
def sheaf : TopCat.Sheaf CommRingCat (TopCat.of M) where
  obj := presheaf I M
  property := by
    rw [CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget _ _
      (CategoryTheory.forget CommRingCat)]
    exact (typeSheaf I M).property

/-- Forgetting the pointwise ring operations recovers exactly the actual
sheaf of locally represented meromorphic germ-valued functions. -/
theorem forget_sheaf :
    (CategoryTheory.sheafCompose _ (CategoryTheory.forget CommRingCat)).obj (sheaf I M) =
      typeSheaf I M := rfl

theorem sheaf_obj_eq (U : (Opens (TopCat.of M))ᵒᵖ) :
    (sheaf I M).presheaf.obj U = CommRingCat.of (Section I M U.unop) := rfl

/-- The original holomorphic functions embed naturally into local meromorphic functions. -/
def ofHolomorphicPresheafHom : HolomorphicFunctionSheaf.presheaf I M ⟶ presheaf I M where
  app U := CommRingCat.ofHom (ofHolomorphicRingHom I M U.unop)
  naturality U V h := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro f
    exact ofHolomorphic_restrict I M (CategoryTheory.leOfHom h.unop) f

/-- The genuine inclusion of the holomorphic sheaf into the meromorphic sheaf. -/
def ofHolomorphicSheafHom : HolomorphicFunctionSheaf.sheaf I M ⟶ sheaf I M :=
  ⟨ofHolomorphicPresheafHom I M⟩

@[simp] theorem ofHolomorphicPresheafHom_app (U : Opens M)
    (f : HolomorphicFunctionSheaf.Section I M U) :
    (ofHolomorphicPresheafHom I M).app (op U) f = ofHolomorphic I M U f := rfl

end Wikipedia.HopfProblem.HolomorphicMeromorphic
