import Wikipedia.NoExoticSixSphere.EuclideanOpenCompactSupportDuality

/-!
# Original compact-support cap duality on the charted manifold

An actual open subset contained in a chart is homeomorphic to its
Euclidean open image, where the original cap has been proved bijective.
Such subsets are closed under intersections, and chart sources cover
the original manifold. Finite-union induction and directed-union
assembly prove bijectivity of the original cap in every complementary
degree, with no duality hypothesis and no change of the ambient atlas.
-/

noncomputable section

open TopologicalSpace
open Wikipedia.HopfProblem SphereHomologyCoefficients

namespace NoExoticSixSphere.CompactSupportCapMap

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (n : ℕ) [Fact (Module.finrank ℝ E = (n + 2) + 1)]

section Chart

variable {M : Type} [TopologicalSpace M] [T2Space M] [ChartedSpace E M]

/-- The actual cap-duality property holds on any open subset of an original chart source. -/
theorem duality_of_chart_subset (U : Opens M) (e : OpenPartialHomeomorph M E)
    (hU : (U : Set M) ⊆ e.source) : Duality (E := E) n U := by
  let V : Opens E := ⟨e '' (U : Set M), e.isOpen_image_of_subset_source U.isOpen hU⟩
  let h : U ≃ₜ V := e.homeomorphOfImageSubsetSource hU rfl
  exact Duality.of_homeomorph (E := E) n (X := V) (Y := U) h.symm
    (euclidean_open_duality (E := E) n V)

end Chart

variable (M : Type) [TopologicalSpace M] [T2Space M] [ChartedSpace E M]

/-- Actual cap duality and above-dimension vanishing, assembled from the original charts. -/
theorem manifold_duality : Duality (E := E) n M := by
  let B (U : Opens M) : Prop := ∃ x : M, (U : Set M) ⊆ (chartAt E x).source
  have hB (U : Opens M) (hU : B U) : Duality (E := E) n U := by
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
  apply duality_of_opens_top (E := E) n
  exact (congrArg (fun U : Opens M => Duality (E := E) n U) he).mp
    (duality_iSup_of_basic_family (E := E) n B hB hBI F hF)

/-- The original manifold compact-support cap is bijective in every complementary degree. -/
theorem manifold_bijective (p q : ℕ) (h : p + q = n + 3) :
    Function.Bijective (dualityMap (E := E) n M p q h) :=
  (manifold_duality (E := E) n M).1 p q h

/-- The actual cap map, now equipped with its proved inverse. -/
def manifoldEquiv (p q : ℕ) (h : p + q = n + 3) :
    CompactSupportCohomology.Cohomology M p ≃ₗ[ℤ] ModHomology 2 M q :=
  LinearEquiv.ofBijective (dualityMap (E := E) n M p q h)
    (manifold_bijective (E := E) n M p q h)

theorem manifoldEquiv_toLinearMap (p q : ℕ) (h : p + q = n + 3) :
    (manifoldEquiv (E := E) n M p q h).toLinearMap = dualityMap (E := E) n M p q h := rfl

end NoExoticSixSphere.CompactSupportCapMap
