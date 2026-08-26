import ErdosProblems.Erdos547.ClusterReservoirs

/-!
# Free vertices after used images and future private sets are excluded
-/

namespace Erdos547

open Finset

theorem card_excluded_union_le {V : Type*} [DecidableEq V]
    (X Q used reserved : Finset V) :
    X.card ≤ (X \ (Q ∪ used ∪ reserved)).card +
      Q.card + (X ∩ used).card + (X ∩ reserved).card := by
  have hsplit := Finset.card_sdiff_add_card_inter X (Q ∪ used ∪ reserved)
  have hsub : X ∩ (Q ∪ used ∪ reserved) ⊆ Q ∪ (X ∩ used) ∪ (X ∩ reserved) := by
    intro v hv
    obtain ⟨hvX, hv⟩ := Finset.mem_inter.mp hv
    rcases Finset.mem_union.mp hv with hv | hv
    · rcases Finset.mem_union.mp hv with hv | hv
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ hv)
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hvX, hv⟩))
    · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hvX, hv⟩)
  have hcount := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hinner := Finset.card_union_le Q (X ∩ used)
  omega

theorem available_vertices_with_seed_loss {V : Type*} [DecidableEq V]
    (X Q used reserved : Finset V) (m m₀ q K : ℕ)
    (hX : X.card = m) (hQ : Q.card = q) (hmain : m₀ + 2 * q = m)
    (hload : (X ∩ used).card + (X ∩ reserved).card ≤ m₀ + K) :
    q ≤ (X \ (Q ∪ used ∪ reserved)).card + K := by
  have hh := card_excluded_union_le X Q used reserved
  omega

theorem available_vertices_half_buffer {V : Type*} [DecidableEq V]
    (X Q used reserved : Finset V) (m m₀ q K : ℕ)
    (hX : X.card = m) (hQ : Q.card = q) (hmain : m₀ + 2 * q = m)
    (hload : (X ∩ used).card + (X ∩ reserved).card ≤ m₀ + K) (hK : 2 * K ≤ q) :
    (q : ℝ) / 2 ≤ ((X \ (Q ∪ used ∪ reserved)).card : ℝ) := by
  have hh := available_vertices_with_seed_loss X Q used reserved m m₀ q K hX hQ hmain hload
  have hn : q ≤ 2 * (X \ (Q ∪ used ∪ reserved)).card := by omega
  have hr : (q : ℝ) ≤ 2 * ((X \ (Q ∪ used ∪ reserved)).card : ℝ) := by exact_mod_cast hn
  linarith only [hr]

theorem available_mono_away_from_released_set {V : Type*} [DecidableEq V]
    (X H Q used used' reserved reserved' : Finset V) (hXH : Disjoint X H)
    (hused : used ⊆ used') (hreserved : reserved ⊆ reserved' ∪ H) :
    X \ (Q ∪ used' ∪ reserved') ⊆ X \ (Q ∪ used ∪ reserved) := by
  intro v hv
  obtain ⟨hvX, hvfree⟩ := Finset.mem_sdiff.mp hv
  refine Finset.mem_sdiff.mpr ⟨hvX, ?_⟩
  intro hv
  rcases Finset.mem_union.mp hv with hv | hv
  · rcases Finset.mem_union.mp hv with hv | hv
    · exact hvfree (Finset.mem_union_left _ (Finset.mem_union_left _ hv))
    · exact hvfree (Finset.mem_union_left _ (Finset.mem_union_right _ (hused hv)))
  · rcases Finset.mem_union.mp (hreserved hv) with hv | hv
    · exact hvfree (Finset.mem_union_right _ hv)
    · exact Finset.disjoint_left.mp hXH hvX hv

end Erdos547

#print axioms Erdos547.available_vertices_half_buffer
