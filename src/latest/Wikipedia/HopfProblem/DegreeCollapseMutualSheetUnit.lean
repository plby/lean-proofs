import Wikipedia.HopfProblem.DegreeCollapseMutualSheetFinite

/-!
# A unit mutual count constructs a single geometric intersection

The finite native Whitney reduction produces an actual first sheet in
its original ambient isotopy class. Injectivity of the fixed second sheet
turns the singleton source crossing set into exactly one source-pair
intersection. The unit count is an explicit geometric integer count;
existence of a homological dual or its count comparison is not assumed
to follow merely from the algebraic rank reduction.
-/

noncomputable section

open Set Function Topology ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.DegreeCollapse.MutualSheets

open Wikipedia.SmoothSixDPoincare
open OrbitPair.DeterminantSignCover

variable {D E M N P : Type*}
  [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] [SimplyConnectedSpace M]
  [TopologicalSpace N] [ChartedSpace D N] [IsManifold 𝓘(ℝ, D) ∞ N]
  [T2Space N] [CompactSpace N] [PathConnectedSpace N]
  [TopologicalSpace P] [ChartedSpace D P] [IsManifold 𝓘(ℝ, D) ∞ P]
  [T2Space P] [CompactSpace P] [PathConnectedSpace P]
  (oN : Orientation (tangentBundleCore 𝓘(ℝ, D) N))
  (oP : Orientation (tangentBundleCore 𝓘(ℝ, D) P))
  (oM : Orientation (tangentBundleCore 𝓘(ℝ, E) M))
  (K : (D × D) ≃L[ℝ] E)

theorem exists_single_crossing_of_unit_count
    (hdim : Module.finrank ℝ E = 6) (hsheet : Module.finrank ℝ D = 3)
    (F : C(N, M)) (G : C(P, M))
    (hG : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ G) (hinjG : Injective G)
    (hiG : ∀ y, Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) G y))
    (hgood : Good (D := D) (E := E) G F)
    (hcount : (signedCount oN oP oM K F G
      (finite_crossingPoints hdim hsheet hG hinjG hgood)).natAbs = 1) :
    ∃ ψ : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞,
      ∃ F' : C(N, M), ∃ q : N, ∃ u : P,
        SupportedDiffeomorph.IsotopicToIdentity ψ ∧ (∀ x, F' x = ψ (F x)) ∧
        Good (D := D) (E := E) G F' ∧
        ∀ x y, F' x = G y ↔ x = q ∧ y = u := by
  obtain ⟨ψ, F', hiso, heq, hgood', _, _, hsize⟩ :=
    exists_minimal_crossing_sheet oN oP oM K hdim hsheet F G hG hinjG hiG hgood
  have hone : (crossingPoints F' G).ncard = 1 := hsize.trans hcount
  obtain ⟨q, hq⟩ := Set.ncard_eq_one.mp hone
  have hqmem : q ∈ crossingPoints F' G := hq.symm ▸ Set.mem_singleton q
  obtain ⟨u, hu⟩ := hqmem
  refine ⟨ψ, F', q, u, hiso, heq, hgood', ?_⟩
  intro x y
  constructor
  · intro hxy
    have hx : x = q := by
      have hxmem : x ∈ crossingPoints F' G := ⟨y, hxy.symm⟩
      rw [hq] at hxmem
      exact hxmem
    refine ⟨hx, hinjG ?_⟩
    exact hxy.symm.trans ((congrArg F' hx).trans hu.symm)
  · rintro ⟨rfl, rfl⟩
    exact hu.symm

end Wikipedia.HopfProblem.DegreeCollapse.MutualSheets
