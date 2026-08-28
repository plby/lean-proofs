import Wikipedia.HopfProblem.OrbitPairNondegeneratePosetEmbeddings

/-!
# Native subdivision cells and their pointwise colimit

This construction applies to the actual left Kan extensions used for
ordinary and dual subdivision. It identifies their characteristic maps
with the native colimit legs, proves compatibility with every simplex
operator, and proves that these cells jointly cover every simplicial degree.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Simplicial

namespace Wikipedia.HopfProblem.OrbitPair.SubdivisionColimit

variable (A : SimplexCategory ⥤ SSet.{u}) (L : SSet.{u} ⥤ SSet.{u})
    (α : A ⟶ SSet.stdSimplex.{u} ⋙ L)

def cellMap (X : SSet.{u}) (n : ℕ) (x : X _⦋n⦌) : A.obj ⦋n⦌ ⟶ L.obj X :=
  α.app ⦋n⦌ ≫ L.map (SSet.yonedaEquiv.symm x)

theorem cellMap_operator (X : SSet.{u}) (m n : ℕ) (f : ⦋m⦌ ⟶ ⦋n⦌) (x : X _⦋n⦌) :
    cellMap A L α X m (X.map f.op x) = A.map f ≫ cellMap A L α X n x := by
  have hx : SSet.yonedaEquiv.symm (X.map f.op x) =
      SSet.stdSimplex.map f ≫ SSet.yonedaEquiv.symm x :=
    (SSet.yonedaEquiv_symm_naturality_left f x).symm
  unfold cellMap
  rw [hx, L.map_comp, ← Category.assoc]
  exact congrArg (fun g ↦ g ≫ L.map (SSet.yonedaEquiv.symm x)) (α.naturality f).symm

variable (X : SSet.{u})

local instance : Category.{0} (CostructuredArrow SSet.stdSimplex.{u} X) :=
  inferInstanceAs (Category.{0} (CostructuredArrow uliftYoneda.{u} X))

def cellCocone : Cocone (CostructuredArrow.proj SSet.stdSimplex.{u} X ⋙ A) :=
  (Functor.LeftExtension.mk L α).coconeAt X

def cellCoconeIsColimit [SSet.stdSimplex.{u}.HasPointwiseLeftKanExtension A]
    [L.IsLeftKanExtension α] : IsColimit (cellCocone A L α X) :=
  Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension L α X

theorem cellMap_eq_cocone_leg (a : CostructuredArrow SSet.stdSimplex.{u} X) :
    cellMap A L α X a.left.len (SSet.yonedaEquiv a.hom) = (cellCocone A L α X).ι.app a := by
  unfold cellMap
  rw [Equiv.symm_apply_apply]
  rfl

theorem exists_cell [SSet.stdSimplex.{u}.HasPointwiseLeftKanExtension A]
    [L.IsLeftKanExtension α] (k : ℕ) (y : (L.obj X) _⦋k⦌) :
    ∃ n : ℕ, ∃ x : X _⦋n⦌, ∃ t : (A.obj ⦋n⦌) _⦋k⦌,
      (cellMap A L α X n x).app (Opposite.op ⦋k⦌) t = y := by
  obtain ⟨a, t, ht⟩ := Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (SSet.evaluation.obj (Opposite.op ⦋k⦌))
      (cellCoconeIsColimit A L α X)) y
  refine ⟨a.left.len, SSet.yonedaEquiv a.hom, t, ?_⟩
  exact (congrArg (fun g ↦ g.app (Opposite.op ⦋k⦌) t) (cellMap_eq_cocone_leg A L α X a)).trans ht

end Wikipedia.HopfProblem.OrbitPair.SubdivisionColimit
