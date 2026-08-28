import Wikipedia.HopfProblem.DegreeCollapseCleanTubeAvoidingSheets

/-!
# Supported single passage fixing every protected sheet

The entire family is supported away from an additional closed smooth
surface image. Thus every point of every protected handle sphere is fixed
for every real time. The moving and crossed sheets retain their full
original intersection count and native transversality.
-/

noncomputable section

open Set Function Filter Metric Manifold Topology
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

local notation "D₂" => EuclideanSpace ℝ (Fin 2)
local notation "V₄" => D₂ × D₂
local notation "W₅" => ℝ × V₄

variable {E M X Y Z : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
  [TopologicalSpace X] [ChartedSpace D₂ X] [IsManifold (𝓡 2) ∞ X]
  [CompactSpace X] [SecondCountableTopology X]
  [TopologicalSpace Y] [ChartedSpace D₂ Y] [IsManifold (𝓡 2) ∞ Y]
  [CompactSpace Y] [SecondCountableTopology Y]
  [TopologicalSpace Z] [ChartedSpace D₂ Z] [IsManifold (𝓡 2) ∞ Z]
  [SecondCountableTopology Z]

theorem exists_supported_single_sheet_passage_fixing_image
    {f : X → M} {g : Y → M} {b : Z → M}
    (hf : ContMDiff (𝓡 2) 𝓘(ℝ, E) ∞ f) (hg : ContMDiff (𝓡 2) 𝓘(ℝ, E) ∞ g)
    (hfe : IsEmbedding f) (hge : IsEmbedding g)
    (hfi : ∀ x, Injective (mfderiv (𝓡 2) 𝓘(ℝ, E) f x))
    (hgi : ∀ y, Injective (mfderiv (𝓡 2) 𝓘(ℝ, E) g y))
    (hdisj : Disjoint (range f) (range g))
    (hb : ContMDiff (𝓡 2) 𝓘(ℝ, E) ∞ b) (hbc : IsClosed (range b))
    (hdim : Module.finrank ℝ E = 5) (x : X) (y : Y)
    (hbx : f x ∉ range b) (hby : g y ∉ range b) (γ : Path (f x) (g y)) :
    ∃ τ ∈ Ioo (0 : ℝ) 1, ∃ (F : ℝ × M → M) (K : Set M),
      IsCompact K ∧ K ⊆ (range b)ᶜ ∧
      ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞ F ∧
      (∀ z, F (0, z) = z) ∧
      (∀ t, ∃ d : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞, ∀ z, d z = F (t, z)) ∧
      (∀ t z, z ∉ K → F (t, z) = z) ∧
      (∀ t z, F (t, b z) = b z) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ a : X, ∀ c : Y,
        F (t, f a) = g c ↔ t = τ ∧ a = x ∧ c = y) ∧
      NativeTransversality.At (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 2) 𝓘(ℝ, E)
        (fun p : ℝ × X => F (p.1, f p.2)) g (τ, x) y := by
  have hx : f x ∉ range g := fun h => (disjoint_left.mp hdisj) ⟨x, rfl⟩ h
  have hy : g y ∉ range f := fun h => (disjoint_left.mp hdisj) h ⟨y, rfl⟩
  obtain ⟨ε, hε, Φ, hΦ, hΦx, hΦy, hrecf, hrecg, hΦb⟩ :=
    exists_clean_two_sheet_tube_avoiding hf hg hfe hge hfi hgi hb hbc hdim
      x y hx hy hbx hby γ
  have haxis : Icc (0 : ℝ) 1 ×ˢ {(0 : V₄)} ⊆ Φ.source := by
    rintro ⟨t, z⟩ ⟨ht, hz⟩
    have hz0 : z = 0 := hz
    subst z
    exact hΦ ⟨ht, mem_closedBall_self hε.le⟩
  have h0 : (0 : W₅) ∈ Φ.source := haxis ⟨⟨le_rfl, zero_le_one⟩, rfl⟩
  obtain ⟨A⟩ := nonempty_longitudinalTubeMotion Φ haxis
  have hKb : A.support ⊆ (range b)ᶜ := A.support_subset.trans hΦb
  refine ⟨A.time, A.time_mem, A.family, A.support, A.compact_support, hKb, A.smooth,
    A.zero, A.slices, A.fixedOutside, ?_,
    A.whole_sheet_crossing_iff hfe.injective hge.injective hdisj hrecf hrecg
      x y hΦx hΦy h0,
    A.whole_sheet_transverse (hf.mdifferentiable (by simp) x)
      (hg.mdifferentiable (by simp) y) (hfi x) (hgi y) hrecf hrecg hΦx hΦy h0⟩
  intro t z
  exact A.fixedOutside t (b z) (fun hz => hKb hz (mem_range_self z))

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
