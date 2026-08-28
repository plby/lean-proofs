import Wikipedia.HopfProblem.DegreeCollapseIntegralOpenSupportHomology
import Wikipedia.HopfProblem.DegreeCollapseIntegralCompactSupportCap

/-!
# Constructed primitive integral classes on actual open subsets

Restrict the constructed ambient fundamental class to the actual image
of a compact support, then apply the inverse of original integral
excision. The resulting classes in the open subset have coherent
primitive localizations and commute with all original support restrictions.
No compactness, simple connectivity, or orientation of the open subset
is assumed. The corresponding integral cap map is constructed, not
asserted to be bijective.
-/

noncomputable section

open TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralOpenFundamentalClass

open FirstHurewicz NoExoticSixSphere SupportedRelativeHomology IntegralOpenSupport

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (n : ℕ) [Fact (Module.finrank ℝ E = (n + 2) + 1)]
  {M : Type} [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [CompactSpace M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [SimplyConnectedSpace M]
  (U : Set M) (hU : IsOpen U)

/-- The original local inclusion equivalence with its coefficient-object types explicit. -/
def localEquiv (x : U) : Homology (ModuleCat.of ℤ ℤ) {x} (n + 3) ≃ₗ[ℤ]
    Homology (ModuleCat.of ℤ ℤ) {(x : M)} (n + 3) :=
  RelativeSingularHomology.neighborhoodEquiv U hU x (n + 3)

/-- The chosen ambient local generator transported through the original open inclusion. -/
def localClass (x : U) : Homology (ModuleCat.of ℤ ℤ) {x} (n + 3) :=
  (localEquiv n U hU x).symm
    (fromAbsolute (ModuleCat.of ℤ ℤ) {(x : M)} (n + 3)
      (IntegralManifoldFundamentalClass.fundamentalClass (E := E) n M))

theorem localClass_inclusion (x : U) :
    localEquiv n U hU x (localClass (E := E) n U hU x) =
      fromAbsolute (ModuleCat.of ℤ ℤ) {(x : M)} (n + 3)
        (IntegralManifoldFundamentalClass.fundamentalClass (E := E) n M) :=
  (localEquiv n U hU x).apply_symm_apply _

/-- Primitivity is transported by the actual local inclusion equivalence. -/
theorem localClass_generates (x : U) (c : Homology (ModuleCat.of ℤ ℤ) {x} (n + 3)) :
    ∃ k : ℤ, k • localClass (E := E) n U hU x = c := by
  let e : Homology (ModuleCat.of ℤ ℤ) {x} (n + 3) ≃ₗ[ℤ]
      Homology (ModuleCat.of ℤ ℤ) {(x : M)} (n + 3) :=
    localEquiv n U hU x
  obtain ⟨k, hk⟩ := IntegralManifoldFundamentalClass.fundamentalClass_isFundamental
    (E := E) n M (x : M) (e c)
  refine ⟨k, e.injective ?_⟩
  exact (map_zsmul e k (localClass (E := E) n U hU x)).trans
    ((congrArg (fun z => k • z) (localClass_inclusion (E := E) n U hU x)).trans hk)

/-- The actual class on a compact support in the open subset, obtained by inverse excision. -/
def supportedClass (K : Set U) (hK : IsCompact K) : Homology (ModuleCat.of ℤ ℤ) K (n + 3) :=
  (IntegralOpenSupport.inclusionEquiv U hU K hK (n + 3)).symm
    (IntegralManifoldFundamentalClass.supportedClass (E := E) n M (imageSupport U K))

theorem supportedClass_inclusion (K : Set U) (hK : IsCompact K) :
    IntegralOpenSupport.inclusionMap U K (n + 3) (supportedClass (E := E) n U hU K hK) =
      IntegralManifoldFundamentalClass.supportedClass (E := E) n M (imageSupport U K) :=
  (IntegralOpenSupport.inclusionEquiv U hU K hK (n + 3)).apply_symm_apply _

/-- Each original local evaluation is the same transported primitive generator. -/
theorem supportedClass_evaluate (K : Set U) (hK : IsCompact K) (x : U) (hx : x ∈ K) :
    evaluate (ModuleCat.of ℤ ℤ) K x hx (n + 3) (supportedClass (E := E) n U hU K hK) =
      localClass (E := E) n U hU x := by
  let e : Homology (ModuleCat.of ℤ ℤ) {x} (n + 3) ≃ₗ[ℤ]
      Homology (ModuleCat.of ℤ ℤ) {(x : M)} (n + 3) :=
    localEquiv n U hU x
  apply e.injective
  calc
    _ = evaluate (ModuleCat.of ℤ ℤ) (imageSupport U K) (x : M) ⟨x, hx, rfl⟩ (n + 3)
        (IntegralOpenSupport.inclusionMap U K (n + 3)
          (supportedClass (E := E) n U hU K hK)) :=
      (LinearMap.congr_fun (IntegralOpenSupport.evaluate_inclusion U K x hx (n + 3))
        (supportedClass (E := E) n U hU K hK)).symm
    _ = evaluate (ModuleCat.of ℤ ℤ) (imageSupport U K) (x : M) ⟨x, hx, rfl⟩ (n + 3)
        (IntegralManifoldFundamentalClass.supportedClass (E := E) n M (imageSupport U K)) :=
      congrArg (evaluate (ModuleCat.of ℤ ℤ) (imageSupport U K) (x : M) ⟨x, hx, rfl⟩ (n + 3))
        (supportedClass_inclusion (E := E) n U hU K hK)
    _ = fromAbsolute (ModuleCat.of ℤ ℤ) {(x : M)} (n + 3)
        (IntegralManifoldFundamentalClass.fundamentalClass (E := E) n M) :=
      IntegralManifoldFundamentalClass.supportedClass_evaluate (E := E) n M
        (imageSupport U K) (x : M) ⟨x, hx, rfl⟩
    _ = _ := (localClass_inclusion (E := E) n U hU x).symm

theorem supportedClass_evaluate_generates (K : Set U) (hK : IsCompact K) (x : U) (hx : x ∈ K)
    (c : Homology (ModuleCat.of ℤ ℤ) {x} (n + 3)) :
    ∃ k : ℤ, k • evaluate (ModuleCat.of ℤ ℤ) K x hx (n + 3)
      (supportedClass (E := E) n U hU K hK) = c := by
  obtain ⟨k, hk⟩ := localClass_generates (E := E) n U hU x c
  exact ⟨k, (congrArg (fun z => k • z)
    (supportedClass_evaluate (E := E) n U hU K hK x hx)).trans hk⟩

/-- The constructed open-subset classes commute with the original integral restrictions. -/
theorem supportedClass_restrict {K L : Set U} (hK : IsCompact K) (hL : IsCompact L) (hKL : K ⊆ L) :
    restrict (ModuleCat.of ℤ ℤ) hKL (n + 3) (supportedClass (E := E) n U hU L hL) =
      supportedClass (E := E) n U hU K hK := by
  apply (IntegralOpenSupport.inclusionEquiv U hU K hK (n + 3)).injective
  calc
    _ = restrict (ModuleCat.of ℤ ℤ) (Set.image_mono hKL) (n + 3)
        (IntegralOpenSupport.inclusionMap U L (n + 3) (supportedClass (E := E) n U hU L hL)) :=
      (IntegralOpenSupport.inclusionMap_restrict U hKL (n + 3)
        (supportedClass (E := E) n U hU L hL)).symm
    _ = restrict (ModuleCat.of ℤ ℤ) (Set.image_mono hKL) (n + 3)
        (IntegralManifoldFundamentalClass.supportedClass (E := E) n M (imageSupport U L)) :=
      congrArg (restrict (ModuleCat.of ℤ ℤ) (Set.image_mono hKL) (n + 3))
        (supportedClass_inclusion (E := E) n U hU L hL)
    _ = IntegralManifoldFundamentalClass.supportedClass (E := E) n M (imageSupport U K) :=
      IntegralManifoldFundamentalClass.supportedClass_restrict (E := E) n M (Set.image_mono hKL)
    _ = _ := (supportedClass_inclusion (E := E) n U hU K hK).symm

/-- The integral cap map on any actual open subset of the ambient manifold. -/
def dualityMap (p q : ℕ) (h : p + q = n + 3) :
    IntegralCompactSupportCohomology.Cohomology U p →ₗ[ℤ] (singularComplex U).homology q :=
  IntegralCompactSupportCap.withClasses h
    (fun K => supportedClass (E := E) n U hU (K : Set U) K.isCompact)
    (fun K L hKL => supportedClass_restrict (E := E) n U hU K.isCompact L.isCompact hKL)

theorem dualityMap_of (p q : ℕ) (h : p + q = n + 3) (K : Compacts U)
    (a : IntegralCompactSupportCohomology.Component U p K) :
    dualityMap (E := E) n U hU p q h (IntegralCompactSupportCohomology.of U p K a) =
      RelativeIntegralCap.capProductInDegree ((K : Set U)ᶜ) h a
        (supportedClass (E := E) n U hU (K : Set U) K.isCompact) := rfl

end Wikipedia.HopfProblem.DegreeCollapse.IntegralOpenFundamentalClass
