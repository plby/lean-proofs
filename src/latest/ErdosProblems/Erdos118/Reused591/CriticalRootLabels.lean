import ErdosProblems.Erdos118.Reused591.LastLastLabels

namespace Erdos118.Reused591

/-!
# Strict-case root overlaps at a prescribed lower critical body

The upper first body is the lower body of rank j; the upper last body
is the very next lower selected body. All intermediate upper bodies
lie in the gap between them. Later lower bodies are retained, with
both cardinalities and the critical rank fixed exactly.
-/

namespace Erdos591.Positive.Game

structure CriticalRootLabels (H : Set ℕ) (B e d j : ℕ) where
  lower : Finset ℕ
  upper : Finset ℕ
  shared : ℕ
  next : ℕ
  marker : ℕ
  lower_card : lower.card = e
  upper_card : upper.card = d
  shared_lower : shared ∈ lower
  shared_upper : shared ∈ upper
  next_lower : next ∈ lower
  next_upper : next ∈ upper
  shared_lt_next : shared < next
  shared_rank : (lower.filter (fun x => x ≤ shared)).card = j
  lower_gap : ∀ x ∈ lower, x ≤ shared ∨ next ≤ x
  upper_bounds : ∀ x ∈ upper, shared ≤ x ∧ x ≤ next
  lower_fresh : ∀ x ∈ lower, x ∈ H ∧ B < x ∧ x < marker
  upper_fresh : ∀ x ∈ upper, x ∈ H ∧ B < x ∧ x < marker
  marker_fresh : marker ∈ H ∧ B < marker

namespace CriticalRootLabels

theorem exists_of_infinite {H : Set ℕ} (hH : H.Infinite) (B e d j : ℕ)
    (hj : 0 < j) (hje : j < e) (hd : 2 ≤ d) : Nonempty (CriticalRootLabels H B e d j) := by
  classical
  obtain ⟨L⟩ := LastFirstLabels.exists_of_infinite hH B j d hj (by omega)
  let anchor := L.upper.sup id
  have hanchor : anchor ∈ L.upper := by
    simpa [anchor] using Finset.sup_mem_of_nonempty (f := id) ⟨_, L.pivot_upper⟩
  have hlt : L.pivot < anchor := L.pivot_lt_upper_sup hd
  have hanchorMarker := (L.upper_fresh _ hanchor).2.2
  have hanchorNot : anchor ∉ L.lower := fun h => not_le_of_gt hlt (L.lower_le _ h)
  obtain ⟨f, hmono, hfH, hfB, _⟩ :=
    FastSequence.exists_above_finite_bounds hH ∅ (fun _ => L.marker)
  let tail := (Finset.range (e - j - 1)).image f
  let lower := insert anchor L.lower ∪ tail
  have htail (x : ℕ) (hx : x ∈ tail) : x ∈ H ∧ L.marker < x ∧ x < f (e - j - 1) := by
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨hfH k, hfB k, hmono (Finset.mem_range.mp hk)⟩
  have hsmall (x : ℕ) (hx : x ∈ insert anchor L.lower) : x < L.marker := by
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hanchorMarker
    · exact (L.lower_fresh x hx).2.2
  have hdisjoint : Disjoint (insert anchor L.lower) tail := by
    apply Finset.disjoint_left.mpr
    intro x hx ht
    exact not_lt_of_ge (hsmall x hx).le (htail x ht).2.1
  have hrank : lower.filter (fun x => x ≤ L.pivot) = L.lower := by
    ext x
    constructor
    · intro hx
      obtain ⟨hx, hxp⟩ := Finset.mem_filter.mp hx
      rcases Finset.mem_union.mp hx with hx | hx
      · rcases Finset.mem_insert.mp hx with rfl | hx
        · exact (not_le_of_gt hlt hxp).elim
        · exact hx
      · have hlm := (L.lower_fresh _ L.pivot_lower).2.2
        exact (not_lt_of_ge (hxp.trans hlm.le) (htail x hx).2.1).elim
    · intro hx
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_union_left _ (Finset.mem_insert_of_mem hx), L.lower_le x hx⟩
  refine ⟨⟨lower, L.upper, L.pivot, anchor, f (e - j - 1), ?_, L.upper_card,
    Finset.mem_union_left _ (Finset.mem_insert_of_mem L.pivot_lower), L.pivot_upper,
    Finset.mem_union_left _ (Finset.mem_insert_self _ _), hanchor, hlt,
    by rw [hrank, L.lower_card], ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [Finset.card_union_of_disjoint hdisjoint, Finset.card_insert_of_notMem hanchorNot,
      L.lower_card, Finset.card_image_of_injective _ hmono.injective, Finset.card_range]
    omega
  · intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · rcases Finset.mem_insert.mp hx with rfl | hx
      · exact Or.inr le_rfl
      · exact Or.inl (L.lower_le x hx)
    · exact Or.inr (hanchorMarker.trans (htail x hx).2.1).le
  · intro x hx
    exact ⟨L.upper_ge x hx, Finset.le_sup (f := id) hx⟩
  · intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · have hfresh : x ∈ H ∧ B < x := by
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact ⟨(L.upper_fresh _ hanchor).1, (L.upper_fresh _ hanchor).2.1⟩
        · exact ⟨(L.lower_fresh _ hx).1, (L.lower_fresh _ hx).2.1⟩
      exact ⟨hfresh.1, hfresh.2, (hsmall x hx).trans (hfB _)⟩
    · exact ⟨(htail x hx).1, L.marker_fresh.2.trans (htail x hx).2.1, (htail x hx).2.2⟩
  · intro x hx
    have h := L.upper_fresh x hx
    exact ⟨h.1, h.2.1, h.2.2.trans (hfB _)⟩
  · exact ⟨hfH _, L.marker_fresh.2.trans (hfB _)⟩

variable {H : Set ℕ} {B e d j : ℕ}

theorem upper_sup (L : CriticalRootLabels H B e d j) : L.upper.sup id = L.next :=
  le_antisymm (Finset.sup_le (fun x hx => (L.upper_bounds x hx).2))
    (Finset.le_sup (f := id) L.next_upper)

theorem next_is_next (L : CriticalRootLabels H B e d j) (x : ℕ) (hx : x ∈ L.lower)
    (hgt : L.shared < x) : L.next ≤ x :=
  (L.lower_gap x hx).resolve_left (not_le_of_gt hgt)

theorem next_rank (L : CriticalRootLabels H B e d j) :
    (L.lower.filter (fun x => x ≤ L.next)).card = j + 1 := by
  classical
  have heq : L.lower.filter (fun x => x ≤ L.next) =
      insert L.next (L.lower.filter (fun x => x ≤ L.shared)) := by
    ext x
    constructor
    · intro hx
      obtain ⟨hx, hle⟩ := Finset.mem_filter.mp hx
      rcases L.lower_gap x hx with hsmall | hlarge
      · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hx, hsmall⟩)
      · exact Finset.mem_insert.mpr (Or.inl (le_antisymm hle hlarge))
    · intro hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact Finset.mem_filter.mpr ⟨L.next_lower, le_rfl⟩
      · obtain ⟨hx, hsmall⟩ := Finset.mem_filter.mp hx
        exact Finset.mem_filter.mpr ⟨hx, hsmall.trans L.shared_lt_next.le⟩
  rw [heq, Finset.card_insert_of_notMem, L.shared_rank]
  exact fun h => not_le_of_gt L.shared_lt_next (Finset.mem_filter.mp h).2

#print axioms exists_of_infinite
#print axioms next_rank

end CriticalRootLabels

end Erdos591.Positive.Game

end Erdos118.Reused591
