import Wikipedia.HopfProblem.DegreeCollapseIntegralNestedOpenCapNaturality

/-!
# Restrict coherent integral support classes to actual open subsets

Original integral excision transports a coherent family to every open
subset. No compactness or connectivity of that subset is needed.
For the constructed ambient fundamental family, these are exactly the
already constructed open-subset classes and their original cap maps.
-/

noncomputable section

open CategoryTheory TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralCompactSupportCohomology

open SingularMayerVietoris NoExoticSixSphere RelativeSingularHomology

variable {X : Type} [TopologicalSpace X] [T2Space X] (U : Set X) (hU : IsOpen U)

/-- Neighborhood cohomology restriction is the original relative subtype pullback. -/
theorem insideEquiv_toRelative (K : Compacts X) (hKU : (K : Set X) ⊆ U) (p : ℕ) :
    (insideEquiv U hU K hKU p).toLinearMap =
      RelativeIntegralCap.cohomologyPullback (subtypeInclusion U)
        (show Set.MapsTo (subtypeInclusion U) (overlapIn U (K : Set X)ᶜ) (K : Set X)ᶜ
          from fun _ hx => hx) p := rfl

end Wikipedia.HopfProblem.DegreeCollapse.IntegralCompactSupportCohomology

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralCoherentSupport

open FirstHurewicz SingularMayerVietoris NoExoticSixSphere SupportedRelativeHomology
open IntegralCompactSupportCohomology (imageCompact insideCompact insideEquiv neighborhoodOf)

variable (X : Type) [TopologicalSpace X] (d : ℕ)

abbrev ClassFamily := ∀ K : Compacts X, Homology (ModuleCat.of ℤ ℤ) (K : Set X) d

def Compatible (c : ClassFamily X d) : Prop :=
  ∀ (K L : Compacts X) (hKL : K ≤ L), restrict (ModuleCat.of ℤ ℤ) hKL d (c L) = c K

variable {X d} [T2Space X] (U : Set X) (hU : IsOpen U) (c : ClassFamily X d)

/-- Restriction through the inverse of the original open-subset pair inclusion. -/
def restrictToOpen : ClassFamily U d := fun K =>
  (IntegralOpenSupport.inclusionEquiv U hU (K : Set U) K.isCompact d).symm (c (imageCompact U K))

theorem restrictToOpen_inclusion (K : Compacts U) :
    IntegralOpenSupport.inclusionMap U (K : Set U) d (restrictToOpen U hU c K) =
      c (imageCompact U K) :=
  (IntegralOpenSupport.inclusionEquiv U hU (K : Set U) K.isCompact d).apply_symm_apply _

/-- Keep any separately named actual ambient compact image in the original pair map. -/
theorem restrictToOpen_inclusion_as (N : Compacts U) (K : Compacts X)
    (hK : (subtypeInclusion U) '' (N : Set U) = (K : Set X)) :
    IntegralOpenEmbeddingSupport.map (subtypeInclusion U) hU.isOpenEmbedding_subtypeVal
      (N : Set U) (K : Set X) hK d (restrictToOpen U hU c N) = c K := by
  have he : imageCompact U N = K := SetLike.coe_injective hK
  subst K
  exact restrictToOpen_inclusion U hU c N

/-- Original support restrictions commute with this inverse-excision family. -/
theorem restrictToOpen_restrict (hc : Compatible X d c) (K L : Compacts U) (hKL : K ≤ L) :
    restrict (ModuleCat.of ℤ ℤ) hKL d (restrictToOpen U hU c L) = restrictToOpen U hU c K := by
  let e : Homology (ModuleCat.of ℤ ℤ) (K : Set U) d ≃ₗ[ℤ]
      Homology (ModuleCat.of ℤ ℤ) (imageCompact U K : Set X) d :=
    IntegralOpenSupport.inclusionEquiv U hU (K : Set U) K.isCompact d
  have h₀ := (IntegralOpenSupport.inclusionMap_restrict U hKL d (restrictToOpen U hU c L)).symm
  have h₁ := congrArg (restrict (ModuleCat.of ℤ ℤ) (Set.image_mono hKL) d)
    (restrictToOpen_inclusion U hU c L)
  have h₂ := hc (imageCompact U K) (imageCompact U L) (Set.image_mono hKL)
  have h₃ := (restrictToOpen_inclusion U hU c K).symm
  exact e.injective (h₀.trans (h₁.trans (h₂.trans h₃)))

theorem restrictToOpen_compatible (hc : Compatible X d c) :
    Compatible U d (restrictToOpen U hU c) :=
  restrictToOpen_restrict U hU c hc

def capOnOpen (hc : Compatible X d c) {p q : ℕ} (h : p + q = d) :
    IntegralCompactSupportCohomology.Cohomology U p →ₗ[ℤ] (singularComplex U).homology q :=
  IntegralCompactSupportCap.withClasses h (restrictToOpen U hU c)
    (restrictToOpen_compatible U hU c hc)

/-- The original compact-neighborhood representative has its actual relative cap value. -/
theorem capOnOpen_neighborhoodOf (hc : Compatible X d c) (K : Compacts X)
    (hKU : (K : Set X) ⊆ U) {p q : ℕ} (h : p + q = d)
    (a : IntegralCompactSupportCohomology.Component X p K) :
    capOnOpen U hU c hc h (neighborhoodOf U hU K hKU p a) =
      RelativeIntegralCap.capProductInDegree ((insideCompact U K hKU : Set U)ᶜ) h
        (insideEquiv U hU K hKU p a) (restrictToOpen U hU c (insideCompact U K hKU)) := rfl

section Manifold

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (n : ℕ) [Fact (Module.finrank ℝ E = (n + 2) + 1)]
  {M : Type} [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [CompactSpace M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [SimplyConnectedSpace M]

/-- The family is constructed from the actual primitive ambient fundamental class. -/
def manifoldFamily : ClassFamily M (n + 3) := fun K =>
  IntegralManifoldFundamentalClass.supportedClass (E := E) n M (K : Set M)

theorem manifoldFamily_compatible : Compatible M (n + 3) (manifoldFamily (E := E) n (M := M)) :=
  fun _K _L hKL => IntegralManifoldFundamentalClass.supportedClass_restrict (E := E) n M hKL

theorem restrictToOpen_manifold (U : Set M) (hU : IsOpen U) (K : Compacts U) :
    restrictToOpen U hU (manifoldFamily (E := E) n) K =
      IntegralOpenFundamentalClass.supportedClass (E := E) n U hU (K : Set U) K.isCompact := rfl

/-- The general construction is exactly the original open-subset cap map. -/
theorem capOnOpen_manifold (U : Set M) (hU : IsOpen U) (p q : ℕ) (h : p + q = n + 3) :
    capOnOpen U hU (manifoldFamily (E := E) n) (manifoldFamily_compatible (E := E) n) h =
      IntegralOpenFundamentalClass.dualityMap (E := E) n U hU p q h := rfl

end Manifold

end Wikipedia.HopfProblem.DegreeCollapse.IntegralCoherentSupport
