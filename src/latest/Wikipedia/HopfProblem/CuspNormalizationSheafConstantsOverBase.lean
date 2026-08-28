import Wikipedia.HopfProblem.CuspNormalizationSheafConstantsOverBaseBasic
import Wikipedia.HopfProblem.CuspNormalizationSheafConstantsAdditiveMaps
import Wikipedia.HopfProblem.CuspNormalizationSheafOverBase

/-!
# The actual constants square for holomorphic maps over a base

The independently constructed constant-sheaf map commutes with the
literal holomorphic-function pullback on each base-open inverse image.
The additive statement is the image of that actual ring-sheaf square
under the forgetful functor used by the normalization sequence.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CuspNormalization.SheafConstants

section Additive

variable {X Y B : TopCat.{0}} (p : Y ⟶ B) (q : X ⟶ B) (f : X ⟶ Y)
  (hf : ∀ x : X, p (f x) = q x)

/-- The actual constant-sheaf map over the base, after forgetting
multiplication and retaining the actual additive pushforward targets. -/
def additiveOverBaseMap :
    (TopCat.Sheaf.pushforward AddCommGrpCat p).obj (complexAdditiveSheaf Y) ⟶
      (TopCat.Sheaf.pushforward AddCommGrpCat q).obj (complexAdditiveSheaf X) :=
  (sheafCompose _ (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)).map
    (overBaseMap p q f hf)

@[simp] theorem additiveOverBaseMap_unit (U : Opens B) (c : ℂ) :
    (additiveOverBaseMap p q f hf).hom.app (op U)
        ((additiveUnit Y).app (op ((Opens.map p).obj U)) c) =
      (additiveUnit X).app (op ((Opens.map q).obj U)) c :=
  overBaseMap_unit p q f hf U c

end Additive

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
  (I : ModelWithCorners ℂ E H)
  {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  [TopologicalSpace G] {N : Type} [TopologicalSpace N] [ChartedSpace G N]
  (J : ModelWithCorners ℂ F G)

/-- The actual continuous map underlying a bundled holomorphic map. -/
def holomorphicTopMap (g : ContMDiffMap J I N M ω) : TopCat.of N ⟶ TopCat.of M :=
  TopCat.ofHom ⟨g, g.contMDiff.continuous⟩

@[simp] theorem holomorphicTopMap_apply (g : ContMDiffMap J I N M ω) (x : N) :
    holomorphicTopMap I J g x = g x := rfl

/-- The given literal holomorphic pullback with the target manifold
itself as base. -/
def nativeHolomorphicPullback (g : ContMDiffMap J I N M ω) :
    HolomorphicFunctionSheaf.sheaf I M ⟶
      (TopCat.Sheaf.pushforward CommRingCat (holomorphicTopMap I J g)).obj
        (HolomorphicFunctionSheaf.sheaf J N) :=
  SheafOverBase.pullback I J (𝟙 (TopCat.of M)) (holomorphicTopMap I J g) g (fun _ => rfl)

/-- Actual holomorphic pullback preserves the specified constant
representatives, so the native constant-sheaf square commutes. -/
theorem holomorphic_pullback_naturality (g : ContMDiffMap J I N M ω) :
    holomorphicMap I M ≫ nativeHolomorphicPullback I J g =
      pullbackMap (holomorphicTopMap I J g) ≫
        (TopCat.Sheaf.pushforward CommRingCat (holomorphicTopMap I J g)).map
          (holomorphicMap J N) := by
  apply pullback_naturality
  intro U c
  apply ContMDiffMap.ext
  intro x
  rfl

variable {B : Type} [TopologicalSpace B]
  (p : TopCat.of M ⟶ TopCat.of B) (q : TopCat.of N ⟶ TopCat.of B)
  (g : ContMDiffMap J I N M ω) (hg : ∀ x : N, p (g x) = q x)

/-- The generic over-base construction of the native pullback is
exactly the previously constructed literal holomorphic pullback. -/
theorem pushforwardOverBaseMap_nativeHolomorphicPullback :
    pushforwardOverBaseMap p q (holomorphicTopMap I J g) hg
        (HolomorphicFunctionSheaf.sheaf J N) (HolomorphicFunctionSheaf.sheaf I M)
        (nativeHolomorphicPullback I J g) =
      SheafOverBase.pullback I J p q g hg := by
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro s
  apply ContMDiffMap.ext
  intro x
  rfl

/-- The required square over the actual base, between the actual
constant-sheaf inclusions and the actual holomorphic-function pullback. -/
theorem holomorphic_overBase_naturality :
    (TopCat.Sheaf.pushforward CommRingCat p).map (holomorphicMap I M) ≫
        SheafOverBase.pullback I J p q g hg =
      overBaseMap p q (holomorphicTopMap I J g) hg ≫
        (TopCat.Sheaf.pushforward CommRingCat q).map (holomorphicMap J N) := by
  calc
    _ = (TopCat.Sheaf.pushforward CommRingCat p).map (holomorphicMap I M) ≫
        pushforwardOverBaseMap p q (holomorphicTopMap I J g) hg
          (HolomorphicFunctionSheaf.sheaf J N) (HolomorphicFunctionSheaf.sheaf I M)
          (nativeHolomorphicPullback I J g) :=
      congrArg _ (pushforwardOverBaseMap_nativeHolomorphicPullback I J p q g hg).symm
    _ = _ := pushforwardOverBaseMap_naturality p q (holomorphicTopMap I J g) hg
      (pullbackMap (holomorphicTopMap I J g)) (nativeHolomorphicPullback I J g)
      (holomorphicMap I M) (holomorphicMap J N) (holomorphic_pullback_naturality I J g)

/-- The same actual commuting square in additive sheaves, as used in
the termwise normalization comparison. -/
theorem additive_holomorphic_overBase_naturality :
    (TopCat.Sheaf.pushforward AddCommGrpCat p).map (holomorphicAdditiveMap I M) ≫
        SheafOverBase.additivePullback I J p q g hg =
      additiveOverBaseMap p q (holomorphicTopMap I J g) hg ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat q).map (holomorphicAdditiveMap J N) := by
  let forgetRings := sheafCompose (Opens.grothendieckTopology (TopCat.of B))
    (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)
  exact ((forgetRings.map_comp
      ((TopCat.Sheaf.pushforward CommRingCat p).map (holomorphicMap I M))
      (SheafOverBase.pullback I J p q g hg)).symm.trans
    (congrArg forgetRings.map (holomorphic_overBase_naturality I J p q g hg))).trans
      (forgetRings.map_comp (overBaseMap p q (holomorphicTopMap I J g) hg)
        ((TopCat.Sheaf.pushforward CommRingCat q).map (holomorphicMap J N)))

end Wikipedia.HopfProblem.CuspNormalization.SheafConstants
