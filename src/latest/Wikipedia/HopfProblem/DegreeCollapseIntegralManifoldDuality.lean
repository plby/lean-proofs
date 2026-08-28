import Wikipedia.HopfProblem.DegreeCollapseIntegralEuclideanOpenDuality

/-!
# Global integral duality for the original constructed manifold cap

Actual chart sources cover the original space. Open subsets contained
in one chart form an intersection-stable family and are homeomorphic
to Euclidean opens. Finite and directed union assembly prove the
primitive-family cap property on the manifold itself.

For a compact simply connected smooth manifold, the previously
constructed primitive integral family supplies all inputs. The actual
compact-support and absolute cap maps are therefore bijections, with
no orientation, fundamental-class, or duality premise.
-/

noncomputable section

open TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralCapDuality

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [hFinite : FiniteDimensional ℝ E] (n : ℕ)
  [hDim : Fact (Module.finrank ℝ E = (n + 2) + 1)]

section Chart

variable {M : Type} [TopologicalSpace M] [T2Space M] [ChartedSpace E M]

omit [T2Space M] [ChartedSpace E M] in
/-- Every original open subset contained in a chart has actual integral cap duality. -/
theorem duality_of_chart_subset (U : Opens M) (e : OpenPartialHomeomorph M E)
    (hU : (U : Set M) ⊆ e.source) : HomeomorphicDuality (n + 3) U := by
  let V : Opens E := ⟨e '' (U : Set M), e.isOpen_image_of_subset_source U.isOpen hU⟩
  let h : U ≃ₜ V := e.homeomorphOfImageSubsetSource hU rfl
  exact HomeomorphicDuality.of_homeomorph h.symm (euclidean_open_duality (E := E) n V)

end Chart

variable (M : Type) [TopologicalSpace M] [T2Space M] [hChart : ChartedSpace E M]

include hFinite hDim hChart

omit [T2Space M] in
/-- Global assembly uses the original chart sources and leaves the actual space unchanged. -/
theorem manifold_homeomorphicDuality : HomeomorphicDuality (n + 3) M := by
  let B (U : Opens M) : Prop := ∃ x : M, (U : Set M) ⊆ (chartAt E x).source
  have hB (U : Opens M) (hU : B U) : HomeomorphicDuality (n + 3) U := by
    obtain ⟨x, hx⟩ := hU
    exact duality_of_chart_subset (E := E) n U (chartAt E x) hx
  have hBI (U V : Opens M) (hU : B U) (_hV : B V) : B (U ⊓ V) := by
    obtain ⟨x, hx⟩ := hU
    exact ⟨x, Set.inter_subset_left.trans hx⟩
  let F (x : M) : Opens M := ⟨(chartAt E x).source, (chartAt E x).open_source⟩
  have hF (x : M) : B (F x) := ⟨x, Set.Subset.refl _⟩
  have he : (⨆ x, F x) = ⊤ := by
    apply le_antisymm le_top
    intro x _
    exact Opens.mem_iSup.mpr ⟨x, mem_chart_source E x⟩
  apply duality_of_opens_top (n + 3)
  exact (congrArg (fun U : Opens M => HomeomorphicDuality (n + 3) U) he).mp
    (duality_iSup_of_basic_family (n + 3) B hB hBI F hF)

/-- The identity copy gives actual integral cap duality on the original charted space. -/
theorem manifold_duality : Duality (n + 3) M :=
  (manifold_homeomorphicDuality (E := E) n M).self

end Wikipedia.HopfProblem.DegreeCollapse.IntegralCapDuality

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralCompactSupportCap

open FirstHurewicz IntegralCompactSupportCohomology

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (n : ℕ) [Fact (Module.finrank ℝ E = (n + 2) + 1)]
  (M : Type) [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [CompactSpace M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [SimplyConnectedSpace M]

/-- Global bijectivity of the actual cap with the constructed primitive fundamental class. -/
theorem dualityMap_bijective (p q : ℕ) (h : p + q = n + 3) :
    Function.Bijective (dualityMap (E := E) n M p q h) :=
  IntegralCapDuality.Duality.constructedMap_bijective (E := E) n
    (IntegralCapDuality.manifold_duality (E := E) n M) p q h

def dualityEquiv (p q : ℕ) (h : p + q = n + 3) :
    Cohomology M p ≃ₗ[ℤ] (singularComplex M).homology q :=
  LinearEquiv.ofBijective (dualityMap (E := E) n M p q h)
    (dualityMap_bijective (E := E) n M p q h)

theorem dualityEquiv_toLinearMap (p q : ℕ) (h : p + q = n + 3) :
    (dualityEquiv (E := E) n M p q h).toLinearMap = dualityMap (E := E) n M p q h := rfl

/-- Compactness identifies the source with original absolute integral cohomology. -/
theorem absoluteDualityMap_bijective (p q : ℕ) (h : p + q = n + 3) :
    Function.Bijective (absoluteDualityMap (E := E) n M p q h) :=
  (dualityMap_bijective (E := E) n M p q h).comp (absoluteEquiv M p).symm.bijective

def absoluteDualityEquiv (p q : ℕ) (h : p + q = n + 3) :
    SingularCohomologyFree.SingularCohomology M p ≃ₗ[ℤ] (singularComplex M).homology q :=
  LinearEquiv.ofBijective (absoluteDualityMap (E := E) n M p q h)
    (absoluteDualityMap_bijective (E := E) n M p q h)

theorem absoluteDualityEquiv_toLinearMap (p q : ℕ) (h : p + q = n + 3) :
    (absoluteDualityEquiv (E := E) n M p q h).toLinearMap =
      absoluteDualityMap (E := E) n M p q h := rfl

end Wikipedia.HopfProblem.DegreeCollapse.IntegralCompactSupportCap
