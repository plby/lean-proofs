import Wikipedia.HopfProblem.DegreeCollapseGlobalBasinImages

/-!
# The closed low-backward obstruction on its own

For paths already in a minimum's forward basin, only backward basins below
the requested level obstruct projection to that level. Their entire union
is closed and has a countable smooth parametrization with dimension bounded
only by those low critical indices, not by any higher stable dimension.
-/

noncomputable section

open Set Function Filter Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

theorem isClosed_backwardLowBasins (S : AdaptedSurgeryWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (a : ℝ) :
    IsClosed (backwardLowBasins S a) := by
  rw [backwardLowBasins_eq_inter S hf]
  exact isClosed_iInter (fun t => isClosed_le
    (hf.continuous.comp (S.flow.continuous continuous_const continuous_id)) continuous_const)

abbrev LowBackwardBasinIndex (S : AdaptedSurgeryWindows E f) (a : ℝ) :=
  {p : criticalPoints E f // f p.val ≤ a} × ℕ

theorem lowBackwardBasinIndex_countable (S : AdaptedSurgeryWindows E f) (a : ℝ) :
    Countable (LowBackwardBasinIndex S a) := by
  let _ := S.finite.fintype
  unfold LowBackwardBasinIndex
  infer_instance

theorem AdaptedSurgeryWindows.exists_low_backward_obstruction_images
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (a : ℝ) {d : ℕ} (hlow : ∀ p : criticalPoints E f, f p ≤ a → nativeMorseIndex E f p ≤ d) :
    ∃ g : LowBackwardBasinIndex S a → EuclideanSpace ℝ (Fin d) → M,
      (∀ i, ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) 𝓘(ℝ, E) ∞ (g i)) ∧
      backwardLowBasins S a = ⋃ i, range (g i) := by
  choose g hg hcover using (fun p : {p : criticalPoints E f // f p.val ≤ a} =>
    S.exists_backward_basin_global_images hf p.val (hlow p.val p.property))
  refine ⟨fun i => g i.1 i.2, fun i => hg i.1 i.2, ?_⟩
  ext x
  constructor
  · rintro ⟨p, hp, hx⟩
    have hh : x ∈ ⋃ n, range (g ⟨p, hp⟩ n) := (hcover ⟨p, hp⟩) ▸ hx
    obtain ⟨n, hn⟩ := mem_iUnion.mp hh
    exact mem_iUnion.mpr ⟨(⟨p, hp⟩, n), hn⟩
  · intro hx
    obtain ⟨⟨p, n⟩, hn⟩ := mem_iUnion.mp hx
    have hh : x ∈ {x : M | Tendsto (fun t => S.flow t x) atBot (𝓝 p.val.val)} := by
      rw [hcover p]
      exact mem_iUnion.mpr ⟨n, hn⟩
    exact ⟨p.val, p.property, hh⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
