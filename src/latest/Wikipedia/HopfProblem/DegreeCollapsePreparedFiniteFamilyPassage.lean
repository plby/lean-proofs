import Wikipedia.HopfProblem.DegreeCollapseFiniteFamilyPassage

/-!
# Construct both relative preparation and the finite-family passage

Initial disjointness from the crossed belt is constructed, not assumed.
The preparatory isotopy fixes every other original sheet and its ambient
germ. The subsequent passage also fixes those exact original sheets and
crosses the full original target once, with native transversality.
-/

noncomputable section

open Set Function Filter Metric Manifold Topology
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare SupportedDiffeomorph

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

open MorseRearrangement

local notation "D₂" => EuclideanSpace ℝ (Fin 2)

variable {ι E M X Y : Type} [Finite ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] [PathConnectedSpace M]
  [TopologicalSpace X] [ChartedSpace D₂ X] [IsManifold (𝓡 2) ∞ X]
  [CompactSpace X] [SecondCountableTopology X] [T2Space X]
  [TopologicalSpace Y] [ChartedSpace D₂ Y] [IsManifold (𝓡 2) ∞ Y]
  [CompactSpace Y] [SecondCountableTopology Y]

theorem exists_prepared_finite_family_passage (a : ι → X → M)
    (ha : ∀ j, ContMDiff (𝓡 2) 𝓘(ℝ, E) ∞ (a j))
    (hpair : Pairwise (fun j k => Disjoint (range (a j)) (range (a k))))
    (i : ι) {g : Y → M} (hg : ContMDiff (𝓡 2) 𝓘(ℝ, E) ∞ g)
    (hfe : IsEmbedding (a i)) (hge : IsEmbedding g)
    (hfi : ∀ x, Injective (mfderiv (𝓡 2) 𝓘(ℝ, E) (a i) x))
    (hgi : ∀ y, Injective (mfderiv (𝓡 2) 𝓘(ℝ, E) g y))
    (hdim : Module.finrank ℝ E = 5) (x : X) (y : Y)
    (hy : g y ∉ otherSheetImages a i) :
    ∃ (e : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞) (C : Set M),
      IsCompact C ∧ C ⊆ (otherSheetImages a i)ᶜ ∧
      Nonempty (SupportedRelativeIsotopy e C (otherSheetImages a i)) ∧
      ∃ τ ∈ Ioo (0 : ℝ) 1, ∃ (F : ℝ × M → M) (K : Set M),
        IsCompact K ∧ K ⊆ (otherSheetImages a i)ᶜ ∧
        ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞ F ∧
        (∀ z, F (0, z) = z) ∧
        (∀ t, ∃ d : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞, ∀ z, d z = F (t, z)) ∧
        (∀ t z, z ∉ K → F (t, z) = z) ∧
        (∀ t j, j ≠ i → ∀ z, F (t, a j z) = a j z) ∧
        (∀ t ∈ Icc (0 : ℝ) 1, ∀ u : X, ∀ v : Y,
          F (t, e (a i u)) = g v ↔ t = τ ∧ u = x ∧ v = y) ∧
        NativeTransversality.At (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 2) 𝓘(ℝ, E)
          (fun p : ℝ × X => F (p.1, e (a i p.2))) g (τ, x) y := by
  have hdim' : Module.finrank ℝ D₂ + Module.finrank ℝ D₂ < Module.finrank ℝ E := by
    simp only [finrank_euclideanSpace_fin, hdim]
    norm_num
  obtain ⟨e, C, hC, hCU, A, hdisj, -, -, -⟩ :=
    exists_finite_sheet_preparation a ha hpair hg hdim' i
  let a' : ι → X → M := fun j => e ∘ a j
  have ha' : ∀ j, ContMDiff (𝓡 2) 𝓘(ℝ, E) ∞ (a' j) := fun j => e.contMDiff.comp (ha j)
  have hpair' : Pairwise (fun j k => Disjoint (range (a' j)) (range (a' k))) :=
    pairwise_disjoint_ranges_postcomp a hpair e.injective
  have hfix (j : ι) (hji : j ≠ i) : a' j = a j := by
    funext z
    exact A.endpoint_fixed_on (a j z) (mem_otherSheetImages a i j hji z)
  have hothers : otherSheetImages a' i = otherSheetImages a i := by
    unfold otherSheetImages
    apply iUnion_congr
    intro j
    rw [hfix j.val j.property]
  have hfe' : IsEmbedding (a' i) := e.toHomeomorph.isEmbedding.comp hfe
  have hfi' : ∀ z, Injective (mfderiv (𝓡 2) 𝓘(ℝ, E) (a' i) z) := by
    intro z
    rw [mfderiv_comp z (e.mdifferentiable (by simp) _) ((ha i).mdifferentiable (by simp) z)]
    exact ((e.toOpenPartialHomeomorph_mdifferentiable (by simp)).mfderiv_injective
      (by trivial)).comp (hfi z)
  have hy' : g y ∉ otherSheetImages a' i := by rwa [hothers]
  obtain ⟨τ, hτ, F, K, hK, hKU, hF, hF0, hFd, hFfix, hfixed, hcount, htrans⟩ :=
    exists_finite_family_single_passage a' ha' hpair' i hg hfe' hge hfi' hgi hdisj
      hdim x y hy' (PathConnectedSpace.somePath (a' i x) (g y))
  refine ⟨e, C, hC, hCU, ⟨A⟩, τ, hτ, F, K, hK, ?_, hF, hF0, hFd, hFfix,
    ?_, hcount, htrans⟩
  · rwa [hothers] at hKU
  · intro t j hji z
    have hh := hfixed t j hji z
    rwa [hfix j hji] at hh

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
