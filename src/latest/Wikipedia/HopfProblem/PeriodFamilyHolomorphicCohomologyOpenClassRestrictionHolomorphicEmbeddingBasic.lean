import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenClassRestrictionEmbeddingBasic
import Wikipedia.HopfProblem.HolomorphicFunctionSheafCohomologyZeroBasic

/-!
# Literal holomorphic section pullback along an open embedding

An actual holomorphic map into an actual open image lifts holomorphically
to that image in the given induced charts. Composition gives an actual
complex-algebra map on every open. Only forward holomorphicity is used;
no inverse holomorphicity or manifold regularity hypothesis is added.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology
namespace OpenClassRestriction.HolomorphicEmbedding

variable {M N : Type} [TopologicalSpace M] [TopologicalSpace N]

/-- The original map with its literal open-image membership witness. -/
def imageMap (f : TopCat.of M ⟶ TopCat.of N) (hf : Topology.IsOpenEmbedding f)
    (U : Opens M) : U → (Embedding.openImage f hf).obj U :=
  fun x => ⟨f x, ⟨x, x.property, rfl⟩⟩

@[simp] theorem imageMap_apply (f : TopCat.of M ⟶ TopCat.of N)
    (hf : Topology.IsOpenEmbedding f) (U : Opens M) (x : U) :
    (imageMap f hf U x : N) = f x := rfl

variable {E E' H H' : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup E'] [NormedSpace ℂ E']
  [TopologicalSpace H] [TopologicalSpace H']
  (I : ModelWithCorners ℂ E H) (J : ModelWithCorners ℂ E' H')
  [ChartedSpace H M] [ChartedSpace H' N]
  (f : TopCat.of M ⟶ TopCat.of N) (hf : Topology.IsOpenEmbedding f)
  (hhol : ContMDiff I J ω f)

include hhol

/-- The actual map into its open image is holomorphic in the given
original atlases and their induced open-subspace charts. -/
theorem imageMap_holomorphic (U : Opens M) : ContMDiff I J ω (imageMap f hf U) := by
  intro x
  apply (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..).mp
  exact hhol.contMDiffAt.comp x contMDiff_subtype_val.contMDiffAt

/-- Literal composition is a homomorphism of the actual holomorphic
section algebras on each original open and its actual image. -/
def sectionPullback (U : Opens M) :
    HolomorphicFunctionSheaf.Section J N ((Embedding.openImage f hf).obj U) →ₐ[ℂ]
      HolomorphicFunctionSheaf.Section I M U where
  toFun s := ⟨fun x => s (imageMap f hf U x),
    s.contMDiff.comp (imageMap_holomorphic I J f hf hhol U)⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

@[simp] theorem sectionPullback_apply (U : Opens M)
    (s : HolomorphicFunctionSheaf.Section J N ((Embedding.openImage f hf).obj U)) (x : U) :
    sectionPullback I J f hf hhol U s x = s (imageMap f hf U x) := rfl

/-- Actual section pullback commutes with the original restriction
maps, using the actual image-open morphism in the ambient sheaf. -/
theorem sectionPullback_restrict {U W : Opens M} (h : U ≤ W)
    (s : HolomorphicFunctionSheaf.Section J N ((Embedding.openImage f hf).obj W)) :
    HolomorphicFunctionSheaf.restrictionAlgHom I M h (sectionPullback I J f hf hhol W s) =
      sectionPullback I J f hf hhol U
        (HolomorphicFunctionSheaf.restrictionAlgHom J N
          ((Embedding.openImage f hf).map (homOfLE h)).le s) := by
  apply ContMDiffMap.ext
  intro x
  rfl

end OpenClassRestriction.HolomorphicEmbedding
end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology
