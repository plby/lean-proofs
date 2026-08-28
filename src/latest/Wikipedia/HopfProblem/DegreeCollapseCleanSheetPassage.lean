import Wikipedia.HopfProblem.DegreeCollapseLongitudinalSheetTransversality

/-!
# Construct a supported single transverse passage of the original sheets

Starting with two disjoint compact embedded immersive surfaces in a native
five-manifold and a path between selected points, construct the clean tube,
compactly supported ambient isotopy, unique crossing time, full-sheet
intersection count, and native transversality. No disk placement, support,
normal chart, scalar motion, or transverse crossing is supplied as input.
-/

noncomputable section

open Set Function Filter Metric Manifold Topology
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

local notation "D₂" => EuclideanSpace ℝ (Fin 2)
local notation "V₄" => D₂ × D₂
local notation "W₅" => ℝ × V₄

variable {E M X Y : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
  [TopologicalSpace X] [ChartedSpace D₂ X] [IsManifold (𝓡 2) ∞ X]
  [CompactSpace X] [SecondCountableTopology X]
  [TopologicalSpace Y] [ChartedSpace D₂ Y] [IsManifold (𝓡 2) ∞ Y]
  [CompactSpace Y] [SecondCountableTopology Y]

theorem exists_supported_single_sheet_passage {f : X → M} {g : Y → M}
    (hf : ContMDiff (𝓡 2) 𝓘(ℝ, E) ∞ f) (hg : ContMDiff (𝓡 2) 𝓘(ℝ, E) ∞ g)
    (hfe : IsEmbedding f) (hge : IsEmbedding g)
    (hfi : ∀ x, Injective (mfderiv (𝓡 2) 𝓘(ℝ, E) f x))
    (hgi : ∀ y, Injective (mfderiv (𝓡 2) 𝓘(ℝ, E) g y))
    (hdisj : Disjoint (range f) (range g))
    (hdim : Module.finrank ℝ E = 5) (x : X) (y : Y) (γ : Path (f x) (g y)) :
    ∃ τ ∈ Ioo (0 : ℝ) 1, ∃ (F : ℝ × M → M) (K : Set M),
      IsCompact K ∧ ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞ F ∧
      (∀ z, F (0, z) = z) ∧
      (∀ t, ∃ d : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞, ∀ z, d z = F (t, z)) ∧
      (∀ t z, z ∉ K → F (t, z) = z) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ a : X, ∀ b : Y,
        F (t, f a) = g b ↔ t = τ ∧ a = x ∧ b = y) ∧
      NativeTransversality.At (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 2) 𝓘(ℝ, E)
        (fun p : ℝ × X => F (p.1, f p.2)) g (τ, x) y := by
  have hx : f x ∉ range g := fun h => (disjoint_left.mp hdisj) ⟨x, rfl⟩ h
  have hy : g y ∉ range f := fun h => (disjoint_left.mp hdisj) h ⟨y, rfl⟩
  obtain ⟨ε, hε, Φ, hΦ, hΦx, hΦy, hrecf, hrecg⟩ :=
    exists_clean_two_sheet_tube hf hg hfe hge hfi hgi hdim x y hx hy γ
  have haxis : Icc (0 : ℝ) 1 ×ˢ {(0 : V₄)} ⊆ Φ.source := by
    rintro ⟨t, z⟩ ⟨ht, hz⟩
    have hz0 : z = 0 := hz
    subst z
    exact hΦ ⟨ht, mem_closedBall_self hε.le⟩
  have h0 : (0 : W₅) ∈ Φ.source := haxis ⟨⟨le_rfl, zero_le_one⟩, rfl⟩
  obtain ⟨A⟩ := nonempty_longitudinalTubeMotion Φ haxis
  exact ⟨A.time, A.time_mem, A.family, A.support, A.compact_support, A.smooth,
    A.zero, A.slices, A.fixedOutside,
    A.whole_sheet_crossing_iff hfe.injective hge.injective hdisj hrecf hrecg
      x y hΦx hΦy h0,
    A.whole_sheet_transverse (hf.mdifferentiable (by simp) x)
      (hg.mdifferentiable (by simp) y) (hfi x) (hgi y) hrecf hrecg hΦx hΦy h0⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
