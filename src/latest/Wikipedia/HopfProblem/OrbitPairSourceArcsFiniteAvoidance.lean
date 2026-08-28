import Wikipedia.HopfProblem.OrbitPairDisjointSourceArcs

/-!
# Disjoint source arcs whose interiors avoid every collision source

The finite forbidden set may contain any of the four endpoints. First
avoid the set with those endpoints removed; arc injectivity and mutual
disjointness then exclude all four endpoints from both arc interiors.
-/

noncomputable section

open Set Function ContinuousMap
open scoped ContDiff Manifold Topology

namespace Wikipedia.HopfProblem.OrbitPair.SourceArcs

theorem interior_avoids_of_disjoint_arcs {M : Type*} {f g : ℝ → M} {C : Set M}
    (hinj : Injective (fun t : unitInterval => f t))
    (hdisj : Disjoint (range (fun t : unitInterval => f t))
      (range (fun t : unitInterval => g t)))
    (havoid : ∀ t ∈ Icc (0 : ℝ) 1,
      f t ∉ C \ (({f 0, f 1} : Set M) ∪ {g 0, g 1})) :
    ∀ t ∈ Ioo (0 : ℝ) 1, f t ∉ C := by
  intro t ht hC
  have htI : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
  have hend : f t ∈ ({f 0, f 1} : Set M) ∪ {g 0, g 1} := by
    by_contra hnot
    exact havoid t htI ⟨hC, hnot⟩
  simp only [mem_union, mem_insert_iff, mem_singleton_iff] at hend
  rcases hend with (heq | heq) | (heq | heq)
  · have hzero : (⟨t, htI⟩ : unitInterval) = 0 := hinj heq
    exact ht.1.ne' (congrArg (fun s : unitInterval => s.val) hzero)
  · have hone : (⟨t, htI⟩ : unitInterval) = 1 := hinj heq
    exact ht.2.ne (congrArg (fun s : unitInterval => s.val) hone)
  · exact disjoint_left.mp hdisj ⟨⟨t, htI⟩, rfl⟩ ⟨0, heq.symm⟩
  · exact disjoint_left.mp hdisj ⟨⟨t, htI⟩, rfl⟩ ⟨1, heq.symm⟩

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [PathConnectedSpace M]

theorem exists_disjoint_embedded_arc_pair_avoiding_finite
    (hdim : 2 ≤ Module.finrank ℝ E)
    {x₀ x₁ y₀ y₁ : M} (hxx : x₀ ≠ x₁) (hyy : y₀ ≠ y₁)
    (hcross : Disjoint ({x₀, x₁} : Set M) {y₀, y₁})
    {C : Set M} (hC : C.Finite) :
    ∃ f : C(ℝ, M), ∃ g : C(ℝ, M),
      ContMDiff 𝓘(ℝ, ℝ) I ∞ f ∧ ContMDiff 𝓘(ℝ, ℝ) I ∞ g ∧
      f 0 = x₀ ∧ f 1 = x₁ ∧ g 0 = y₀ ∧ g 1 = y₁ ∧
      Topology.IsClosedEmbedding (fun t : unitInterval => f t) ∧
      Topology.IsClosedEmbedding (fun t : unitInterval => g t) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, Injective (mfderiv 𝓘(ℝ, ℝ) I f t)) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, Injective (mfderiv 𝓘(ℝ, ℝ) I g t)) ∧
      Disjoint (range (fun t : unitInterval => f t)) (range (fun t : unitInterval => g t)) ∧
      (∀ t ∈ Ioo (0 : ℝ) 1, f t ∉ C) ∧
      (∀ t ∈ Ioo (0 : ℝ) 1, g t ∉ C) := by
  let S : Set M := C \ (({x₀, x₁} : Set M) ∪ {y₀, y₁})
  have hS : S.Finite := hC.subset sdiff_subset
  obtain ⟨f, g, hf, hg, hf0, hf1, hg0, hg1, hembf, hembg, hif, hig,
      hdisj, havoidf, havoidg⟩ := exists_disjoint_embedded_arc_pair (I := I)
    hdim hxx hyy hcross hS (by simp [S]) (by simp [S]) (by simp [S]) (by simp [S])
  refine ⟨f, g, hf, hg, hf0, hf1, hg0, hg1, hembf, hembg, hif, hig, hdisj, ?_, ?_⟩
  · apply interior_avoids_of_disjoint_arcs hembf.injective hdisj
    simpa only [hf0, hf1, hg0, hg1] using havoidf
  · apply interior_avoids_of_disjoint_arcs hembg.injective hdisj.symm
    simpa only [hf0, hf1, hg0, hg1, union_comm] using havoidg

end Wikipedia.HopfProblem.OrbitPair.SourceArcs
