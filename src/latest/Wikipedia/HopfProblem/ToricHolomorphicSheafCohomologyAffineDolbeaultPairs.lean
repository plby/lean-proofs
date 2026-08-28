import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyAffineDolbeaultBasic
import Mathlib.Topology.Sheaves.AddCommGrpCat
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# The actual sheaf of affine smooth antiholomorphic one-forms

In the global coordinates on `ℂ × ℂ`, a `(0,1)`-form is the literal pair
of smooth coefficients of `dbar(z)` and `dbar(w)`. Restrictions are actual
coordinatewise restrictions, and gluing is proved in the genuine smooth
function sheaf in each coordinate.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.AffineDolbeault

/-- The actual two smooth coefficients of an affine `(0,1)`-form. -/
abbrev PairSection (U : Opens (ℂ × ℂ)) := SmoothSection U × SmoothSection U

/-- Literal coordinatewise restriction, including its complex linearity. -/
def pairRestriction {U V : Opens (ℂ × ℂ)} (h : U ≤ V) :
    PairSection V →ₗ[ℂ] PairSection U where
  toFun s := (restriction h s.1, restriction h s.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The actual additive presheaf of smooth coefficient pairs. -/
def pairPresheaf : TopCat.Presheaf AddCommGrpCat (TopCat.of (ℂ × ℂ)) where
  obj U := AddCommGrpCat.of (PairSection U.unop)
  map h := AddCommGrpCat.ofHom (pairRestriction (leOfHom h.unop)).toAddMonoidHom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Both genuine smooth coefficient sheaves glue, so actual pairs glue. -/
theorem pairPresheaf_isSheaf : pairPresheaf.IsSheaf := by
  apply (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing pairPresheaf).mpr
  intro ι U s hs
  have hfst : TopCat.Presheaf.IsCompatible smoothSheaf.obj U (fun i => (s i).1) :=
    fun i j => congrArg Prod.fst (hs i j)
  have hsnd : TopCat.Presheaf.IsCompatible smoothSheaf.obj U (fun i => (s i).2) :=
    fun i j => congrArg Prod.snd (hs i j)
  obtain ⟨a, ha, hau⟩ := smoothSheaf.existsUnique_gluing U (fun i => (s i).1) hfst
  obtain ⟨b, hb, hbu⟩ := smoothSheaf.existsUnique_gluing U (fun i => (s i).2) hsnd
  refine ⟨(a, b), fun i => Prod.ext (ha i) (hb i), ?_⟩
  intro t ht
  exact Prod.ext (hau t.1 (fun i => congrArg Prod.fst (ht i)))
    (hbu t.2 (fun i => congrArg Prod.snd (ht i)))

/-- The genuine sheaf of actual affine smooth `(0,1)`-forms. -/
def pairSheaf : TopCat.Sheaf AddCommGrpCat (TopCat.of (ℂ × ℂ)) where
  obj := pairPresheaf
  property := pairPresheaf_isSheaf

theorem pairSheaf_obj_eq (U : Opens (ℂ × ℂ)) :
    pairSheaf.obj.obj (op U) = AddCommGrpCat.of (PairSection U) := rfl

instance pairSheaf_obj_module (U : (Opens (TopCat.of (ℂ × ℂ)))ᵒᵖ) :
    Module ℂ (pairSheaf.obj.obj U) := inferInstanceAs (Module ℂ (PairSection U.unop))

/-- Actual pair-valued section maps determine a pair-sheaf endomorphism. -/
theorem pairSheafEnd_ext {f g : pairSheaf ⟶ pairSheaf}
    (h : ∀ (U : Opens (ℂ × ℂ)) (s : PairSection U),
      f.hom.app (op U) s = g.hom.app (op U) s) : f = g := by
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  exact AddMonoidHom.ext (h U.unop)

/-- Any actual smooth-function sheaf endomorphism acts on both coefficients. -/
def diagonal (f : smoothSheaf ⟶ smoothSheaf) : pairSheaf ⟶ pairSheaf where
  hom :=
    { app U := AddCommGrpCat.ofHom
        ((f.hom.app U).hom.prodMap (f.hom.app U).hom)
      naturality U V h := by
        apply AddCommGrpCat.hom_ext
        apply AddMonoidHom.ext
        intro s
        change (f.hom.app V (smoothSheaf.obj.map h s.1),
            f.hom.app V (smoothSheaf.obj.map h s.2)) =
          (smoothSheaf.obj.map h (f.hom.app U s.1),
            smoothSheaf.obj.map h (f.hom.app U s.2))
        exact Prod.ext (ConcreteCategory.congr_hom (f.hom.naturality h) s.1)
          (ConcreteCategory.congr_hom (f.hom.naturality h) s.2) }

@[simp] theorem diagonal_apply (f : smoothSheaf ⟶ smoothSheaf)
    (U : Opens (ℂ × ℂ)) (s : PairSection U) :
    (diagonal f).hom.app (op U) s = (f.hom.app (op U) s.1, f.hom.app (op U) s.2) := rfl

/-- Diagonal action respects the actual endomorphism ring operations. -/
def diagonalRingHom : End smoothSheaf →+* End pairSheaf where
  toFun := diagonal
  map_zero' := by
    apply pairSheafEnd_ext
    intro U s
    rfl
  map_one' := by
    apply pairSheafEnd_ext
    intro U s
    rfl
  map_add' f g := by
    apply pairSheafEnd_ext
    intro U s
    rfl
  map_mul' f g := by
    apply pairSheafEnd_ext
    intro U s
    rfl

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.AffineDolbeault
