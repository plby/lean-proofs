import ErdosProblems.Erdos591.OverlapLabels

/-!
# Common first and last selections with separated interiors

The two cardinalities may differ and may equal two. Erase the shared
pivot from a last--first pair, and insert a new common first and last.
The singleton-to-full views supply the existing first-leaf response API.
-/

namespace Erdos591.Positive.Game

structure FirstLastLabels (H : Set ℕ) (B p q : ℕ) where
  lower : Finset ℕ
  upper : Finset ℕ
  first : ℕ
  last : ℕ
  marker : ℕ
  lower_card : lower.card = p
  upper_card : upper.card = q
  first_lower : first ∈ lower
  first_upper : first ∈ upper
  last_lower : last ∈ lower
  last_upper : last ∈ upper
  first_lt_last : first < last
  lower_bounds : ∀ x ∈ lower, first ≤ x ∧ x ≤ last
  upper_bounds : ∀ x ∈ upper, first ≤ x ∧ x ≤ last
  separated : ∀ x ∈ lower, ∀ y ∈ upper, x ≠ last → y ≠ first → x < y
  lower_fresh : ∀ x ∈ lower, x ∈ H ∧ B < x ∧ x < marker
  upper_fresh : ∀ x ∈ upper, x ∈ H ∧ B < x ∧ x < marker
  marker_fresh : marker ∈ H ∧ B < marker

namespace FirstLastLabels

theorem exists_of_infinite {H : Set ℕ} (hH : H.Infinite) (B p q : ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q) : Nonempty (FirstLastLabels H B p q) := by
  classical
  obtain ⟨f, _hf, hfH, hfB, _⟩ :=
    FastSequence.exists_above_finite_bounds hH ∅ (fun _ => B)
  let first := f 0
  obtain ⟨L⟩ := LastFirstLabels.exists_of_infinite hH first (p - 1) (q - 1)
    (by omega) (by omega)
  obtain ⟨g, _hg, hgH, hgB, _⟩ :=
    FastSequence.exists_above_finite_bounds hH ∅ (fun _ => L.marker)
  have hfirstMarker : first < L.marker := L.marker_fresh.2
  have hlFirst : first ∉ L.lower.erase L.pivot := fun h =>
    (lt_irrefl first) (L.lower_fresh first (Finset.mem_of_mem_erase h)).2.1
  have huFirst : first ∉ L.upper.erase L.pivot := fun h =>
    (lt_irrefl first) (L.upper_fresh first (Finset.mem_of_mem_erase h)).2.1
  have hlLast : L.marker ∉ L.lower.erase L.pivot := fun h =>
    (lt_irrefl L.marker) (L.lower_fresh L.marker (Finset.mem_of_mem_erase h)).2.2
  have huLast : L.marker ∉ L.upper.erase L.pivot := fun h =>
    (lt_irrefl L.marker) (L.upper_fresh L.marker (Finset.mem_of_mem_erase h)).2.2
  refine ⟨⟨insert first (insert L.marker (L.lower.erase L.pivot)),
    insert first (insert L.marker (L.upper.erase L.pivot)), first, L.marker, g 0,
    ?_, ?_, by simp, by simp, by simp, by simp, hfirstMarker, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [Finset.card_insert_of_notMem (by simp [hfirstMarker.ne, hlFirst]),
      Finset.card_insert_of_notMem hlLast, Finset.card_erase_of_mem L.pivot_lower, L.lower_card]
    omega
  · rw [Finset.card_insert_of_notMem (by simp [hfirstMarker.ne, huFirst]),
      Finset.card_insert_of_notMem huLast, Finset.card_erase_of_mem L.pivot_upper, L.upper_card]
    omega
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact ⟨le_rfl, hfirstMarker.le⟩
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact ⟨hfirstMarker.le, le_rfl⟩
    have h := L.lower_fresh x (Finset.mem_of_mem_erase hx)
    exact ⟨h.2.1.le, h.2.2.le⟩
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact ⟨le_rfl, hfirstMarker.le⟩
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact ⟨hfirstMarker.le, le_rfl⟩
    have h := L.upper_fresh x (Finset.mem_of_mem_erase hx)
    exact ⟨h.2.1.le, h.2.2.le⟩
  · intro x hx y hy hxl hyf
    have hy' : y ∈ insert L.marker (L.upper.erase L.pivot) :=
      (Finset.mem_insert.mp hy).resolve_left hyf
    rcases Finset.mem_insert.mp hx with rfl | hx
    · rcases Finset.mem_insert.mp hy' with rfl | hy
      · exact hfirstMarker
      · exact (L.upper_fresh y (Finset.mem_of_mem_erase hy)).2.1
    have hx' := (Finset.mem_insert.mp hx).resolve_left hxl
    rcases Finset.mem_insert.mp hy' with rfl | hy
    · exact (L.lower_fresh x (Finset.mem_of_mem_erase hx')).2.2
    have hxp : x < L.pivot := lt_of_le_of_ne
      (L.lower_le x (Finset.mem_of_mem_erase hx')) (Finset.ne_of_mem_erase hx')
    exact hxp.trans_le (L.upper_ge y (Finset.mem_of_mem_erase hy))
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact ⟨hfH 0, hfB 0, hfirstMarker.trans (hgB 0)⟩
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact ⟨L.marker_fresh.1, (hfB 0).trans hfirstMarker, hgB 0⟩
    have h := L.lower_fresh x (Finset.mem_of_mem_erase hx)
    exact ⟨h.1, (hfB 0).trans h.2.1, h.2.2.trans (hgB 0)⟩
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact ⟨hfH 0, hfB 0, hfirstMarker.trans (hgB 0)⟩
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact ⟨L.marker_fresh.1, (hfB 0).trans hfirstMarker, hgB 0⟩
    have h := L.upper_fresh x (Finset.mem_of_mem_erase hx)
    exact ⟨h.1, (hfB 0).trans h.2.1, h.2.2.trans (hgB 0)⟩
  · exact ⟨hgH 0, (hfB 0).trans (hfirstMarker.trans (hgB 0))⟩

variable {H : Set ℕ} {B p q : ℕ}

theorem intersection (L : FirstLastLabels H B p q) :
    L.lower ∩ L.upper = {L.first, L.last} := by
  classical
  ext x
  simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hl, hu⟩
    by_cases hf : x = L.first
    · exact Or.inl hf
    by_cases he : x = L.last
    · exact Or.inr he
    exact (lt_irrefl x (L.separated x hl x hu he hf)).elim
  · rintro (rfl | rfl)
    · exact ⟨L.first_lower, L.first_upper⟩
    · exact ⟨L.last_lower, L.last_upper⟩

def first_to_lower (L : FirstLastLabels H B p q) : LastFirstLabels H B 1 p where
  lower := {L.first}
  upper := L.lower
  pivot := L.first
  marker := L.marker
  lower_card := by simp
  upper_card := L.lower_card
  pivot_lower := by simp
  pivot_upper := L.first_lower
  lower_le := fun _ hx => (Finset.mem_singleton.mp hx).le
  upper_ge := fun x hx => (L.lower_bounds x hx).1
  lower_fresh := by
    intro x hx
    rw [Finset.mem_singleton.mp hx]
    exact L.lower_fresh _ L.first_lower
  upper_fresh := L.lower_fresh
  marker_fresh := L.marker_fresh

def first_to_upper (L : FirstLastLabels H B p q) : LastFirstLabels H B 1 q where
  lower := {L.first}
  upper := L.upper
  pivot := L.first
  marker := L.marker
  lower_card := by simp
  upper_card := L.upper_card
  pivot_lower := by simp
  pivot_upper := L.first_upper
  lower_le := fun _ hx => (Finset.mem_singleton.mp hx).le
  upper_ge := fun x hx => (L.upper_bounds x hx).1
  lower_fresh := by
    intro x hx
    rw [Finset.mem_singleton.mp hx]
    exact L.upper_fresh _ L.first_upper
  upper_fresh := L.upper_fresh
  marker_fresh := L.marker_fresh

theorem lower_sup (L : FirstLastLabels H B p q) : L.lower.sup id = L.last :=
  le_antisymm (Finset.sup_le fun x hx => (L.lower_bounds x hx).2)
    (Finset.le_sup (f := id) L.last_lower)

theorem upper_sup (L : FirstLastLabels H B p q) : L.upper.sup id = L.last :=
  le_antisymm (Finset.sup_le fun x hx => (L.upper_bounds x hx).2)
    (Finset.le_sup (f := id) L.last_upper)

#print axioms exists_of_infinite
#print axioms intersection

end FirstLastLabels

end Erdos591.Positive.Game
