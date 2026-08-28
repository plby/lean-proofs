import Wikipedia.HopfProblem.CuspNormalizationSheafConstantsAdditiveMaps
import Wikipedia.HopfProblem.CuspNormalizationSheafConstantsInjective
import Wikipedia.HopfProblem.CuspNormalizationSheafConstantsNaturality

/-!
# Additive constant inclusions and the actual normalization pullback square

Forgetting multiplication preserves the literal component maps.  Thus
the constant-to-holomorphic maps remain injective and their pullback
square commutes in the actual category of additive sheaves used for
normalization exact sequences.
-/

noncomputable section

open Set TopologicalSpace Opposite CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CuspNormalization.SheafConstants

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
  (I : ModelWithCorners ℂ E H)

/-- The actual additive inclusion of locally constant complex sections
into holomorphic sections is a monomorphism. -/
instance holomorphicAdditiveMap_mono : Mono (holomorphicAdditiveMap I M) :=
  CategoryTheory.Sheaf.mono_of_injective _ fun U =>
    holomorphicMap_app_injective I M U.unop

/-- The reduced-holomorphic inclusion is also genuinely injective after
forgetting multiplication. -/
instance reducedAdditiveMap_mono (S : Set M) : Mono (reducedAdditiveMap I S) :=
  CategoryTheory.Sheaf.mono_of_injective _ fun U =>
    reducedMap_app_injective I S U.unop

variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  [TopologicalSpace G] {N : Type} [TopologicalSpace N] [ChartedSpace G N]
  (J : ModelWithCorners ℂ F G) (S : Set M)
  (g : ContMDiffMap J I N M ω) (hg : ∀ x : N, g x ∈ S)

/-- The actual constants square commutes in additive sheaves, with the
actual reduced-function pullback and actual constant-sheaf pullback. -/
theorem reduced_holomorphic_additive_naturality :
    reducedAdditiveMap I S ≫ SheafPullback.additivePullback I J S g hg =
      additivePullbackMap (SheafPullback.topMap I J S g hg) ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat (SheafPullback.topMap I J S g hg)).map
          (holomorphicAdditiveMap J N) := by
  let forgetRings := sheafCompose (Opens.grothendieckTopology (TopCat.of S))
    (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)
  exact ((forgetRings.map_comp (reducedMap I S) (SheafPullback.pullback I J S g hg)).symm.trans
    (congrArg forgetRings.map (reduced_holomorphic_naturality I J S g hg))).trans
      (forgetRings.map_comp (pullbackMap (SheafPullback.topMap I J S g hg))
        ((TopCat.Sheaf.pushforward CommRingCat (SheafPullback.topMap I J S g hg)).map
          (holomorphicMap J N)))

end Wikipedia.HopfProblem.CuspNormalization.SheafConstants
