import Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomologyDolbeaultBasic
import Mathlib.Topology.Sheaves.AddCommGrpCat
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# Genuine smooth coefficient pairs on the native period torus

The sections are literal pairs of real-smooth complex-valued functions
on open subsets of the original quotient torus. Restrictions act on
each coefficient, and gluing is proved in its actual smooth-function
sheaf. Endomorphisms of that sheaf act diagonally on the two coefficients.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomology.Dolbeault

variable (p : PeriodDomain)

/-- Two actual smooth complex coefficients on the given torus open set. -/
abbrev PairSection (U : Opens p.Torus) := SmoothSection p U × SmoothSection p U

/-- Literal coordinatewise restriction, with its actual complex linearity. -/
def pairRestriction {U V : Opens p.Torus} (h : U ≤ V) :
    PairSection p V →ₗ[ℂ] PairSection p U where
  toFun s := (restriction p h s.1, restriction p h s.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem pairRestriction_apply {U V : Opens p.Torus} (h : U ≤ V)
    (s : PairSection p V) :
    pairRestriction p h s = (restriction p h s.1, restriction p h s.2) := rfl

/-- The actual additive presheaf of smooth pairs on the native torus. -/
def pairPresheaf : TopCat.Presheaf AddCommGrpCat (TopCat.of p.Torus) where
  obj U := AddCommGrpCat.of (PairSection p U.unop)
  map h := AddCommGrpCat.ofHom (pairRestriction p (leOfHom h.unop)).toAddMonoidHom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Gluing each genuine smooth coefficient proves the sheaf condition
for the literal pair presheaf. -/
theorem pairPresheaf_isSheaf : (pairPresheaf p).IsSheaf := by
  apply (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing (pairPresheaf p)).mpr
  intro ι U s hs
  have hfst : TopCat.Presheaf.IsCompatible (smoothSheaf p).obj U (fun i => (s i).1) :=
    fun i j => congrArg Prod.fst (hs i j)
  have hsnd : TopCat.Presheaf.IsCompatible (smoothSheaf p).obj U (fun i => (s i).2) :=
    fun i j => congrArg Prod.snd (hs i j)
  obtain ⟨a, ha, hau⟩ := (smoothSheaf p).existsUnique_gluing U (fun i => (s i).1) hfst
  obtain ⟨b, hb, hbu⟩ := (smoothSheaf p).existsUnique_gluing U (fun i => (s i).2) hsnd
  refine ⟨(a, b), fun i => Prod.ext (ha i) (hb i), ?_⟩
  intro t ht
  exact Prod.ext (hau t.1 (fun i => congrArg Prod.fst (ht i)))
    (hbu t.2 (fun i => congrArg Prod.snd (ht i)))

/-- The genuine additive sheaf of the two original smooth coefficients. -/
def pairSheaf : TopCat.Sheaf AddCommGrpCat (TopCat.of p.Torus) where
  obj := pairPresheaf p
  property := pairPresheaf_isSheaf p

theorem pairSheaf_obj_eq (U : Opens p.Torus) :
    (pairSheaf p).obj.obj (op U) = AddCommGrpCat.of (PairSection p U) := rfl

instance pairSheaf_obj_module (U : (Opens (TopCat.of p.Torus))ᵒᵖ) :
    Module ℂ ((pairSheaf p).obj.obj U) :=
  inferInstanceAs (Module ℂ (PairSection p U.unop))

@[simp] theorem pairSheaf_map_apply {U V : Opens p.Torus} (h : U ≤ V)
    (s : PairSection p V) :
    (pairSheaf p).obj.map (homOfLE h).op s = pairRestriction p h s := rfl

/-- Equality on the actual pair sections determines a sheaf endomorphism. -/
theorem pairSheafEnd_ext {f g : pairSheaf p ⟶ pairSheaf p}
    (h : ∀ (U : Opens p.Torus) (s : PairSection p U),
      f.hom.app (op U) s = g.hom.app (op U) s) : f = g := by
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  exact AddMonoidHom.ext (h U.unop)

/-- Apply an actual smooth-function sheaf endomorphism to both coefficients. -/
def diagonal (f : smoothSheaf p ⟶ smoothSheaf p) : pairSheaf p ⟶ pairSheaf p where
  hom :=
    { app U := AddCommGrpCat.ofHom
        ((f.hom.app U).hom.prodMap (f.hom.app U).hom)
      naturality U V h := by
        apply AddCommGrpCat.hom_ext
        apply AddMonoidHom.ext
        intro s
        change (f.hom.app V ((smoothSheaf p).obj.map h s.1),
            f.hom.app V ((smoothSheaf p).obj.map h s.2)) =
          ((smoothSheaf p).obj.map h (f.hom.app U s.1),
            (smoothSheaf p).obj.map h (f.hom.app U s.2))
        exact Prod.ext (ConcreteCategory.congr_hom (f.hom.naturality h) s.1)
          (ConcreteCategory.congr_hom (f.hom.naturality h) s.2) }

@[simp] theorem diagonal_apply (f : smoothSheaf p ⟶ smoothSheaf p)
    (U : Opens p.Torus) (s : PairSection p U) :
    (diagonal p f).hom.app (op U) s =
      (f.hom.app (op U) s.1, f.hom.app (op U) s.2) := rfl

/-- Diagonal action preserves the actual endomorphism ring operations. -/
def diagonalRingHom : End (smoothSheaf p) →+* End (pairSheaf p) where
  toFun := diagonal p
  map_zero' := by
    apply pairSheafEnd_ext p
    intro U s
    rfl
  map_one' := by
    apply pairSheafEnd_ext p
    intro U s
    rfl
  map_add' f g := by
    apply pairSheafEnd_ext p
    intro U s
    rfl
  map_mul' f g := by
    apply pairSheafEnd_ext p
    intro U s
    rfl

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomology.Dolbeault
