import StackExchange.Puzzling139335.CentralRotation.ArcPacking.Parameters

/-!
# Endpoint exclusion for subarcs of one simple arc

The interior of an actual subarc is relatively open in its containing simple
arc.  Consequently, if two subarc interiors are disjoint, the endpoints of one
subarc cannot lie in the interior of the other.
-/

open Set unitInterval Schoenflies

namespace Puzzling139335.CentralRotation.FirstOverlap

/-- Removing the two endpoints of an actual subarc gives a relatively open
subset of the containing simple arc. -/
theorem subarc_diff_isRelOpen
    {N J : Set Schoenflies.Plane} {n₀ n₁ p q : Schoenflies.Plane}
    (hN : IsArcBetween N n₀ n₁) (hJ : IsArcBetween J p q) (hJN : J ⊆ N) :
    ∃ V : Set Schoenflies.Plane, IsOpen V ∧ J \ {p, q} = V ∩ N := by
  obtain ⟨f, hf, hfi, himage, -, -⟩ := hN
  have hsub : J ⊆ f '' I := by simpa only [himage] using hJN
  obtain ⟨s, t, hs, ht, hst, -, hopen⟩ :=
    ArcPacking.exists_subarc_interval hf hfi hJ hsub
  obtain ⟨V, hVopen, hV⟩ := openArc_subarc_isRelOpen hf hfi hs ht
  refine ⟨V, hVopen, ?_⟩
  rw [hopen, ← himage]
  simpa only [uIoo_of_lt hst] using hV

/-- A simple arc is the closure of the arc with its two endpoints removed. -/
theorem arc_closure_diff_endpoints
    {K : Set Schoenflies.Plane} {a b : Schoenflies.Plane}
    (hK : IsArcBetween K a b) : closure (K \ {a, b}) = K := by
  refine subset_antisymm (closure_minimal sdiff_subset hK.isArc.isClosed) ?_
  intro x hx
  by_cases hxa : x = a
  · simpa only [hxa] using hK.left_mem_closure_diff
  by_cases hxb : x = b
  · simpa only [hxb] using hK.right_mem_closure_diff
  exact subset_closure ⟨hx, by simp only [mem_insert_iff, mem_singleton_iff, hxa, hxb,
    or_self, not_false_eq_true]⟩

/-- Disjoint interiors of two subarcs of a common simple arc exclude the
endpoints of the first subarc from the interior of the second as well. -/
theorem disjoint_of_disjoint_arc_interiors
    {N J K : Set Schoenflies.Plane} {n₀ n₁ p q a b : Schoenflies.Plane}
    (hN : IsArcBetween N n₀ n₁) (hJ : IsArcBetween J p q)
    (hK : IsArcBetween K a b) (hJN : J ⊆ N) (hKN : K ⊆ N)
    (hdisj : Disjoint (K \ {a, b}) (J \ {p, q})) :
    Disjoint K (J \ {p, q}) := by
  obtain ⟨V, hVopen, hV⟩ := subarc_diff_isRelOpen hN hJ hJN
  have hKV : Disjoint (K \ {a, b}) V := by
    refine disjoint_left.mpr ?_
    intro x hxK hxV
    apply disjoint_left.mp hdisj hxK
    rw [hV]
    exact ⟨hxV, hKN hxK.1⟩
  have hclosure := hKV.closure_left hVopen
  rw [arc_closure_diff_endpoints hK] at hclosure
  apply hclosure.mono_right
  rw [hV]
  exact inter_subset_left

end Puzzling139335.CentralRotation.FirstOverlap
