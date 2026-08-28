import Wikipedia.HopfProblem.DegreeCollapseIntegralHomeomorphicBallSupport
import Wikipedia.HopfProblem.DegreeCollapseIntegralOpenCapNaturality
import Wikipedia.HopfProblem.DegreeCollapseIntegralChartClassComparison

/-!
# Actual integral cap duality on Euclidean chart neighborhoods

Pulled-back closed balls are cofinal among the original compact supports.
Any coherent family of actual classes with primitive local evaluations
therefore gives a bijective original cap on a space homeomorphic to the
Euclidean model. In particular this applies directly to the constructed
classes on original open subsets of the ambient compact simply connected
manifold. No preferred marking sign or cap-duality input is supplied.
-/

noncomputable section

open Metric TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralEuclideanLikeCap

open FirstHurewicz NoExoticSixSphere SupportedRelativeHomology
open IntegralCompactSupportCohomology IntegralHomeomorphicBall

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (n : ℕ) [Fact (Module.finrank ℝ E = (n + 2) + 1)]
  {X : Type} [TopologicalSpace X]

/-- The actual limit cap is bijective for every coherent primitive family on this space. -/
theorem withClasses_bijective (e : X ≃ₜ E)
    (c : ∀ K : Compacts X, Homology (ModuleCat.of ℤ ℤ) (K : Set X) (n + 3))
    (hc : ∀ (K L : Compacts X) (hKL : K ≤ L),
      restrict (ModuleCat.of ℤ ℤ) hKL (n + 3) (c L) = c K)
    (hp : ∀ K : Compacts X, IntegralPrimitiveCap.IsPrimitiveOn (K : Set X) (n + 3) (c K))
    (p q : ℕ) (h : p + q = n + 3) :
    Function.Bijective (IntegralCompactSupportCap.withClasses h c hc) := by
  apply IntegralCompactSupportCap.withClasses_bijective_of_cofinal h c hc
  intro K
  obtain ⟨R, hR, hKR⟩ := (K.isCompact.image e.continuous).isBounded.subset_closedBall_lt 0 (0 : E)
  let B : Compacts X := ⟨support e R, support_isCompact e R⟩
  refine ⟨B, ?_, cap_bijective n e R hR.le (c B) (hp B) p q h⟩
  exact fun x hx => hKR ⟨x, hx, rfl⟩

/-- Off-dimension vanishing is also computed through original enclosing-ball extensions. -/
theorem cohomology_eq_zero (e : X ≃ₜ E) (p : ℕ) (hp : p ≠ n + 3) (a : Cohomology X p) : a = 0 := by
  obtain ⟨K, a, rfl⟩ := exists_representative X p a
  obtain ⟨R, hR, hKR⟩ := (K.isCompact.image e.continuous).isBounded.subset_closedBall_lt 0 (0 : E)
  let B : Compacts X := ⟨support e R, support_isCompact e R⟩
  have hK : K ≤ B := fun x hx => hKR ⟨x, hx, rfl⟩
  let := IntegralHomeomorphicBall.cohomology_subsingleton n e R hR.le p hp
  have he : transition X p K B hK a = 0 := Subsingleton.elim _ _
  exact (of_transition X p hK a).symm.trans
    ((congrArg (of X p B) he).trans (of X p B).map_zero)

theorem cohomology_subsingleton (e : X ≃ₜ E) (p : ℕ) (hp : p ≠ n + 3) :
    Subsingleton (Cohomology X p) :=
  ⟨fun a b => (cohomology_eq_zero n e p hp a).trans (cohomology_eq_zero n e p hp b).symm⟩

/-- A supplied partial chart with full model target gives its actual source homeomorphism. -/
def fullChartHomeomorph (e : OpenPartialHomeomorph X E)
    (he : e.target = Set.univ) : e.source ≃ₜ E :=
  e.toHomeomorphSourceTarget.trans ((Homeomorph.setCongr he).trans (Homeomorph.Set.univ E))

end Wikipedia.HopfProblem.DegreeCollapse.IntegralEuclideanLikeCap

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralOpenFundamentalClass

open FirstHurewicz

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (n : ℕ) [Fact (Module.finrank ℝ E = (n + 2) + 1)]
  {M : Type} [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [CompactSpace M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [SimplyConnectedSpace M]
  (U : Set M) (hU : IsOpen U)

/-- Actual cap duality on a Euclidean open neighborhood, using the constructed original classes. -/
theorem dualityMap_bijective_of_homeomorph (e : U ≃ₜ E)
    (p q : ℕ) (h : p + q = n + 3) : Function.Bijective (dualityMap (E := E) n U hU p q h) :=
  IntegralEuclideanLikeCap.withClasses_bijective n e
    (fun K => supportedClass (E := E) n U hU (K : Set U) K.isCompact)
    (fun K L hKL => supportedClass_restrict (E := E) n U hU K.isCompact L.isCompact hKL)
    (fun K x hx a => supportedClass_evaluate_generates (E := E) n U hU
      (K : Set U) K.isCompact x hx a) p q h

def dualityEquiv_of_homeomorph (e : U ≃ₜ E) (p q : ℕ) (h : p + q = n + 3) :
    IntegralCompactSupportCohomology.Cohomology U p ≃ₗ[ℤ] (singularComplex U).homology q :=
  LinearEquiv.ofBijective (dualityMap (E := E) n U hU p q h)
    (dualityMap_bijective_of_homeomorph (E := E) n U hU e p q h)

theorem dualityEquiv_of_homeomorph_toLinearMap (e : U ≃ₜ E) (p q : ℕ) (h : p + q = n + 3) :
    (dualityEquiv_of_homeomorph (E := E) n U hU e p q h).toLinearMap =
      dualityMap (E := E) n U hU p q h := rfl

omit U hU in
/-- A full-range actual chart supplies the local bijectivity with no comparison-sign input. -/
theorem dualityMap_bijective_of_full_chart (e : OpenPartialHomeomorph M E)
    (he : e.target = Set.univ) (p q : ℕ) (h : p + q = n + 3) :
    Function.Bijective (dualityMap (E := E) n e.source e.open_source p q h) :=
  dualityMap_bijective_of_homeomorph (E := E) n e.source e.open_source
    (IntegralEuclideanLikeCap.fullChartHomeomorph e he) p q h

end Wikipedia.HopfProblem.DegreeCollapse.IntegralOpenFundamentalClass

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralManifoldFundamentalClass

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (n : ℕ) [Fact (Module.finrank ℝ E = (n + 2) + 1)]
  (M : Type) [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [CompactSpace M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [SimplyConnectedSpace M]

theorem exists_full_chart_sign (e : OpenPartialHomeomorph M E) (he : e.target = Set.univ) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∀ (K : Set M) (hK : IsCompact K) (hKs : K ⊆ e.source),
      supportedClass (E := E) n M K =
        ε • IntegralChartOrientation.fundamentalClass (n + 1) e K hK hKs := by
  let : ContractibleSpace e.source :=
    (IntegralEuclideanLikeCap.fullChartHomeomorph e he).contractibleSpace
  exact exists_chart_sign (E := E) n M e

end Wikipedia.HopfProblem.DegreeCollapse.IntegralManifoldFundamentalClass
