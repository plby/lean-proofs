import Wikipedia.HopfProblem.HolomorphicFunctionSheafCohomologyZeroBasic
import Mathlib.Topology.Sheaves.Functors

/-!
# Actual holomorphic restriction between pushforward sheaves

A holomorphic map between two manifolds over the same topological base
pulls back functions on each actual open inverse image. These maps form
a genuine morphism of the pushed-forward holomorphic-function sheaves.
The cusp normalization resolution applies this to its two actual lifts
of each double curve into the normalization surface.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CuspNormalization.SheafOverBase

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
  (I : ModelWithCorners ℂ E H)
  {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  [TopologicalSpace G] {N : Type} [TopologicalSpace N] [ChartedSpace G N]
  (J : ModelWithCorners ℂ F G)
  {B : Type} [TopologicalSpace B]
  (p : TopCat.of M ⟶ TopCat.of B) (q : TopCat.of N ⟶ TopCat.of B)
  (g : ContMDiffMap J I N M ω) (hg : ∀ x : N, p (g x) = q x)

/-- The actual map on inverse images of a base open set. -/
def mapOnPreimages (U : Opens B) : (Opens.map q).obj U → (Opens.map p).obj U :=
  fun x => ⟨g x, by
    change p (g x) ∈ U
    rw [hg]
    exact x.property⟩

@[simp] theorem mapOnPreimages_val (U : Opens B) (x : (Opens.map q).obj U) :
    (mapOnPreimages I J p q g hg U x : M) = g x := rfl

/-- Actual holomorphicity is inherited on both open inverse images. -/
theorem mapOnPreimages_holomorphic (U : Opens B) :
    ContMDiff J I ω (mapOnPreimages I J p q g hg U) := by
  intro x
  have he : ContMDiffAt J I ω
      (fun y : (Opens.map q).obj U => (mapOnPreimages I J p q g hg U y : M)) x ↔
      ContMDiffAt J I ω (mapOnPreimages I J p q g hg U) x :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  exact he.mp ((g.contMDiff.comp contMDiff_subtype_val) x)

/-- Literal holomorphic pullback on every actual base-open inverse image. -/
def sectionPullback (U : Opens B) :
    HolomorphicFunctionSheaf.Section I M ((Opens.map p).obj U) →ₐ[ℂ]
      HolomorphicFunctionSheaf.Section J N ((Opens.map q).obj U) where
  toFun f := ⟨f ∘ mapOnPreimages I J p q g hg U,
    f.contMDiff.comp (mapOnPreimages_holomorphic I J p q g hg U)⟩
  map_zero' := by apply ContMDiffMap.ext; intro x; rfl
  map_one' := by apply ContMDiffMap.ext; intro x; rfl
  map_add' _ _ := by apply ContMDiffMap.ext; intro x; rfl
  map_mul' _ _ := by apply ContMDiffMap.ext; intro x; rfl
  commutes' _ := by apply ContMDiffMap.ext; intro x; rfl

@[simp] theorem sectionPullback_apply (U : Opens B)
    (f : HolomorphicFunctionSheaf.Section I M ((Opens.map p).obj U))
    (x : (Opens.map q).obj U) :
    sectionPullback I J p q g hg U f x = f (mapOnPreimages I J p q g hg U x) := rfl

/-- The actual ring-sheaf morphism over the original topological base. -/
def pullback :
    (TopCat.Sheaf.pushforward CommRingCat p).obj (HolomorphicFunctionSheaf.sheaf I M) ⟶
      (TopCat.Sheaf.pushforward CommRingCat q).obj (HolomorphicFunctionSheaf.sheaf J N) :=
  ObjectProperty.homMk
    { app U := CommRingCat.ofHom (sectionPullback I J p q g hg U.unop).toRingHom
      naturality _ _ _ := by ext f; rfl }

@[simp] theorem pullback_app (U : Opens B)
    (f : HolomorphicFunctionSheaf.Section I M ((Opens.map p).obj U)) :
    (pullback I J p q g hg).hom.app (op U) f = sectionPullback I J p q g hg U f := rfl

/-- The same actual pullback in the category of additive sheaves. -/
def additivePullback :
    (TopCat.Sheaf.pushforward AddCommGrpCat p).obj
      (HolomorphicFunctionSheaf.additiveSheaf I M) ⟶
    (TopCat.Sheaf.pushforward AddCommGrpCat q).obj
      (HolomorphicFunctionSheaf.additiveSheaf J N) :=
  (sheafCompose _ (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)).map
    (pullback I J p q g hg)

@[simp] theorem additivePullback_app (U : Opens B)
    (f : HolomorphicFunctionSheaf.Section I M ((Opens.map p).obj U)) :
    (additivePullback I J p q g hg).hom.app (op U) f =
      sectionPullback I J p q g hg U f := rfl

end Wikipedia.HopfProblem.CuspNormalization.SheafOverBase
