import Wikipedia.HopfProblem.DegreeCollapseFiniteSurfaceImage
import Wikipedia.HopfProblem.DegreeCollapseRelativeSheetPassage

/-!
# A single full-sheet passage fixes the entire remaining finite family

The protected surface image is constructed as the exact finite disjoint
sum of the other original sheets. Its compactness supplies closedness.
The relative native passage then fixes every point of every other sheet
at all real times, with compact support disjoint from their whole images.
-/

noncomputable section

open Set Function Filter Metric Manifold Topology
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

open MorseRearrangement

local notation "D₂" => EuclideanSpace ℝ (Fin 2)

variable {ι E M X Y : Type} [Finite ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
  [TopologicalSpace X] [ChartedSpace D₂ X] [IsManifold (𝓡 2) ∞ X]
  [CompactSpace X] [SecondCountableTopology X]
  [TopologicalSpace Y] [ChartedSpace D₂ Y] [IsManifold (𝓡 2) ∞ Y]
  [CompactSpace Y] [SecondCountableTopology Y]

theorem exists_finite_family_single_passage (a : ι → X → M)
    (ha : ∀ j, ContMDiff (𝓡 2) 𝓘(ℝ, E) ∞ (a j))
    (hpair : Pairwise (fun j k => Disjoint (range (a j)) (range (a k))))
    (i : ι) {g : Y → M} (hg : ContMDiff (𝓡 2) 𝓘(ℝ, E) ∞ g)
    (hfe : IsEmbedding (a i)) (hge : IsEmbedding g)
    (hfi : ∀ x, Injective (mfderiv (𝓡 2) 𝓘(ℝ, E) (a i) x))
    (hgi : ∀ y, Injective (mfderiv (𝓡 2) 𝓘(ℝ, E) g y))
    (hdisj : Disjoint (range (a i)) (range g))
    (hdim : Module.finrank ℝ E = 5) (x : X) (y : Y)
    (hy : g y ∉ otherSheetImages a i) (γ : Path (a i x) (g y)) :
    ∃ τ ∈ Ioo (0 : ℝ) 1, ∃ (F : ℝ × M → M) (K : Set M),
      IsCompact K ∧ K ⊆ (otherSheetImages a i)ᶜ ∧
      ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞ F ∧
      (∀ z, F (0, z) = z) ∧
      (∀ t, ∃ d : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞, ∀ z, d z = F (t, z)) ∧
      (∀ t z, z ∉ K → F (t, z) = z) ∧
      (∀ t j, j ≠ i → ∀ z, F (t, a j z) = a j z) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ u : X, ∀ v : Y,
        F (t, a i u) = g v ↔ t = τ ∧ u = x ∧ v = y) ∧
      NativeTransversality.At (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 2) 𝓘(ℝ, E)
        (fun p : ℝ × X => F (p.1, a i p.2)) g (τ, x) y := by
  obtain ⟨n, b, hb, hbrange⟩ := exists_sheetSumMap_for_finite_family
    (fun j : {j : ι // j ≠ i} => a j.val) (fun j => ha j.val)
  have hrange : range b = otherSheetImages a i := hbrange
  have hbc : IsClosed (range b) := (isCompact_range hb.continuous).isClosed
  have hx : a i x ∉ range b := by
    rw [hrange]
    intro hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp hx
    exact Set.disjoint_left.mp (hpair (Ne.symm j.property)) (mem_range_self x) hj
  have hyb : g y ∉ range b := by rwa [hrange]
  obtain ⟨τ, hτ, F, K, hK, hKC, hF, hF0, hFd, hFfix, hbfix, hcount, htrans⟩ :=
    exists_supported_single_sheet_passage_fixing_image (ha i) hg hfe hge hfi hgi hdisj
      hb hbc hdim x y hx hyb γ
  refine ⟨τ, hτ, F, K, hK, ?_, hF, hF0, hFd, hFfix, ?_, hcount, htrans⟩
  · rwa [hrange] at hKC
  · intro t j hji z
    have hz : a j z ∈ range b := hrange.symm ▸ mem_otherSheetImages a i j hji z
    obtain ⟨w, hw⟩ := hz
    rw [← hw]
    exact hbfix t w

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
