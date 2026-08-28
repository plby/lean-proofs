import Wikipedia.SmoothSixDPoincare.FlowEntryTranslation

/-! # The regular upper level is the actual sublevel frontier under a strict descending flow -/

noncomputable section

open Set Filter
open scoped Topology

namespace Wikipedia.SmoothSixDPoincare.FlowConstruction

variable {X : Type*} [TopologicalSpace X]

theorem frontier_sublevel_eq_of_strict_flow {f : X → ℝ} (hf : Continuous f)
    (F : Flow ℝ X) (hmono : ∀ x, Antitone (fun t => f (F t x))) {b : ℝ}
    (htop : ∀ x, f x = b → ∀ t : ℝ, 0 < t → f (F t x) < b) :
    frontier {x | f x ≤ b} = {x | f x = b} := by
  have hclosed : IsClosed {x | f x ≤ b} := isClosed_le hf continuous_const
  ext x
  rw [frontier, hclosed.closure_eq]
  constructor
  · rintro ⟨hx, hnot⟩
    apply le_antisymm hx
    by_contra hn
    have hlt : f x < b := lt_of_not_ge hn
    exact hnot (interior_maximal (fun y (hy : f y < b) => hy.le)
      (isOpen_lt hf continuous_const) hlt)
  · intro hx
    refine ⟨(show f x ≤ b from hx.le), ?_⟩
    intro hi
    have he : ∀ᶠ t : ℝ in 𝓝 0, F t x ∈ interior {y | f y ≤ b} := by
      have hcont : ContinuousAt (fun t : ℝ => F t x) 0 :=
        (F.continuous continuous_id continuous_const).continuousAt
      apply hcont.preimage_mem_nhds
      simpa only [F.map_zero_apply] using isOpen_interior.mem_nhds hi
    obtain ⟨s, hs, hsB⟩ := he.exists_lt
    have hy : F s x ∈ {y | f y ≤ b} := interior_subset hsB
    have hxy : f x ≤ f (F s x) := by
      have hh := hmono (F s x) (show (0 : ℝ) ≤ -s by linarith)
      simpa only [F.map_zero_apply, ← F.map_add, neg_add_cancel] using hh
    have hyeq : f (F s x) = b := le_antisymm hy (hx ▸ hxy)
    have hstrict := htop (F s x) hyeq (-s) (by linarith)
    rw [← F.map_add, neg_add_cancel, F.map_zero_apply, hx] at hstrict
    exact lt_irrefl b hstrict

end Wikipedia.SmoothSixDPoincare.FlowConstruction
