import ErdosProblems.Erdos118.Reused591.OverlapLabels

namespace Erdos118.Reused591

/-!
# Two labels sharing only their last selected index

Every nonlast lower index precedes every upper index. The lower
penultimate index and the common last index are retained explicitly.
This leaves room for the delayed upper initial response between them.
-/

namespace Erdos591.Positive.Game

structure LastLastLabels (H : Set ℕ) (B n : ℕ) (c : ℕ := n) where
  lower : Finset ℕ
  upper : Finset ℕ
  penultimate : ℕ
  pivot : ℕ
  marker : ℕ
  lower_card : lower.card = n
  upper_card : upper.card = c
  penultimate_lower : penultimate ∈ lower
  pivot_lower : pivot ∈ lower
  pivot_upper : pivot ∈ upper
  penultimate_lt_pivot : penultimate < pivot
  lower_bounds : ∀ x ∈ lower, x = pivot ∨ x ≤ penultimate
  upper_bounds : ∀ x ∈ upper, penultimate < x ∧ x ≤ pivot
  upper_before_pivot : ∃ x ∈ upper, x < pivot
  lower_fresh : ∀ x ∈ lower, x ∈ H ∧ B < x ∧ x < marker
  upper_fresh : ∀ x ∈ upper, x ∈ H ∧ B < x ∧ x < marker
  marker_fresh : marker ∈ H ∧ B < marker

namespace LastLastLabels

theorem exists_sizes_of_infinite {H : Set ℕ} (hH : H.Infinite) (B n c : ℕ)
    (hn : 2 ≤ n) (hc : 2 ≤ c) : Nonempty (LastLastLabels H B n c) := by
  classical
  obtain ⟨L⟩ := LastFirstLabels.exists_of_infinite hH B (n - 1) c (by omega) (by omega)
  obtain ⟨f, _hmono, hfH, hfB, _⟩ :=
    FastSequence.exists_above_finite_bounds hH ∅ (fun _ => L.marker)
  let U := L.upper.erase L.pivot
  have hUcard : U.card = c - 1 := by
    rw [Finset.card_erase_of_mem L.pivot_upper, L.upper_card]
  have hUne : U.Nonempty := Finset.card_pos.mp (by rw [hUcard]; omega)
  have hnotLower : L.marker ∉ L.lower :=
    fun h => Nat.lt_irrefl _ (L.lower_fresh _ h).2.2
  have hnotUpper : L.marker ∉ U :=
    fun h => Nat.lt_irrefl _ (L.upper_fresh _ (Finset.mem_of_mem_erase h)).2.2
  refine ⟨⟨insert L.marker L.lower, insert L.marker U, L.pivot, L.marker, f 0,
    ?_, ?_, by simp [L.pivot_lower], by simp, by simp,
    (L.lower_fresh _ L.pivot_lower).2.2, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [Finset.card_insert_of_notMem hnotLower, L.lower_card]
    omega
  · rw [Finset.card_insert_of_notMem hnotUpper, hUcard]
    omega
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact Or.inl rfl
    · exact Or.inr (L.lower_le x hx)
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact ⟨(L.lower_fresh _ L.pivot_lower).2.2, le_rfl⟩
    · have hxmem := Finset.mem_of_mem_erase hx
      have hxne := Finset.ne_of_mem_erase hx
      have hle := L.upper_ge x hxmem
      exact ⟨by omega, (L.upper_fresh x hxmem).2.2.le⟩
  · obtain ⟨x, hx⟩ := hUne
    exact ⟨x, Finset.mem_insert_of_mem hx, (L.upper_fresh x (Finset.mem_of_mem_erase hx)).2.2⟩
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact ⟨L.marker_fresh.1, L.marker_fresh.2, hfB 0⟩
    · have hf := L.lower_fresh x hx
      exact ⟨hf.1, hf.2.1, hf.2.2.trans (hfB 0)⟩
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact ⟨L.marker_fresh.1, L.marker_fresh.2, hfB 0⟩
    · have hf := L.upper_fresh x (Finset.mem_of_mem_erase hx)
      exact ⟨hf.1, hf.2.1, hf.2.2.trans (hfB 0)⟩
  · exact ⟨hfH 0, L.marker_fresh.2.trans (hfB 0)⟩

theorem exists_of_infinite {H : Set ℕ} (hH : H.Infinite) (B n : ℕ) (hn : 2 ≤ n) :
    Nonempty (LastLastLabels H B n) := exists_sizes_of_infinite hH B n n hn hn

variable {H : Set ℕ} {B n c : ℕ}

def firstLower (L : LastLastLabels H B n c) : ℕ := L.lower.min' ⟨L.pivot, L.pivot_lower⟩

def firstUpper (L : LastLastLabels H B n c) : ℕ := L.upper.min' ⟨L.pivot, L.pivot_upper⟩

theorem firstLower_mem (L : LastLastLabels H B n c) : L.firstLower ∈ L.lower :=
  Finset.min'_mem _ _

theorem firstUpper_mem (L : LastLastLabels H B n c) : L.firstUpper ∈ L.upper :=
  Finset.min'_mem _ _

theorem firstLower_le (L : LastLastLabels H B n c) (x : ℕ) (hx : x ∈ L.lower) :
    L.firstLower ≤ x := Finset.min'_le _ _ hx

theorem firstUpper_le (L : LastLastLabels H B n c) (x : ℕ) (hx : x ∈ L.upper) :
    L.firstUpper ≤ x := Finset.min'_le _ _ hx

theorem firstLower_le_penultimate (L : LastLastLabels H B n c) :
    L.firstLower ≤ L.penultimate := L.firstLower_le _ L.penultimate_lower

theorem penultimate_lt_firstUpper (L : LastLastLabels H B n c) :
    L.penultimate < L.firstUpper := (L.upper_bounds _ L.firstUpper_mem).1

theorem firstUpper_lt_pivot (L : LastLastLabels H B n c) : L.firstUpper < L.pivot := by
  obtain ⟨x, hx, hxp⟩ := L.upper_before_pivot
  exact (L.firstUpper_le x hx).trans_lt hxp

theorem lower_le_pivot (L : LastLastLabels H B n c) (x : ℕ) (hx : x ∈ L.lower) :
    x ≤ L.pivot := (L.lower_bounds x hx).elim (fun he => he.le)
      (fun he => he.trans L.penultimate_lt_pivot.le)

theorem intersection (L : LastLastLabels H B n c) : L.lower ∩ L.upper = {L.pivot} := by
  ext x
  simp only [Finset.mem_inter, Finset.mem_singleton]
  constructor
  · rintro ⟨hl, hu⟩
    rcases L.lower_bounds x hl with he | he
    · exact he
    · exact (not_lt_of_ge he (L.upper_bounds x hu).1).elim
  · rintro rfl
    exact ⟨L.pivot_lower, L.pivot_upper⟩

def first_to_lower (L : LastLastLabels H B n c) : LastFirstLabels H B 1 n where
  lower := {L.firstLower}
  upper := L.lower
  pivot := L.firstLower
  marker := L.marker
  lower_card := by simp
  upper_card := L.lower_card
  pivot_lower := by simp
  pivot_upper := L.firstLower_mem
  lower_le := by
    intro x hx
    exact (Finset.mem_singleton.mp hx).le
  upper_ge := L.firstLower_le
  lower_fresh := by
    intro x hx
    rw [Finset.mem_singleton.mp hx]
    exact L.lower_fresh _ L.firstLower_mem
  upper_fresh := L.lower_fresh
  marker_fresh := L.marker_fresh

def first_to_upper (L : LastLastLabels H B n c) : LastFirstLabels H B 1 c where
  lower := {L.firstUpper}
  upper := L.upper
  pivot := L.firstUpper
  marker := L.marker
  lower_card := by simp
  upper_card := L.upper_card
  pivot_lower := by simp
  pivot_upper := L.firstUpper_mem
  lower_le := by
    intro x hx
    exact (Finset.mem_singleton.mp hx).le
  upper_ge := L.firstUpper_le
  lower_fresh := by
    intro x hx
    rw [Finset.mem_singleton.mp hx]
    exact L.upper_fresh _ L.firstUpper_mem
  upper_fresh := L.upper_fresh
  marker_fresh := L.marker_fresh

theorem lower_sup (L : LastLastLabels H B n c) : L.lower.sup id = L.pivot :=
  le_antisymm (Finset.sup_le L.lower_le_pivot) (Finset.le_sup (f := id) L.pivot_lower)

theorem upper_sup (L : LastLastLabels H B n c) : L.upper.sup id = L.pivot :=
  le_antisymm (Finset.sup_le (fun x hx => (L.upper_bounds x hx).2))
    (Finset.le_sup (f := id) L.pivot_upper)

#print axioms exists_sizes_of_infinite
#print axioms exists_of_infinite
#print axioms intersection

end LastLastLabels

namespace LastFirstLabels

theorem pivot_lt_upper_sup {H : Set ℕ} {B a c : ℕ} (L : LastFirstLabels H B a c)
    (hc : 2 ≤ c) : L.pivot < L.upper.sup id := by
  by_contra hn
  have hle : L.upper.sup id ≤ L.pivot := le_of_not_gt hn
  have hall (x : ℕ) (hx : x ∈ L.upper) : x = L.pivot :=
    le_antisymm ((Finset.le_sup (f := id) hx).trans hle) (L.upper_ge x hx)
  have hcard : L.upper.card ≤ 1 := Finset.card_le_one.mpr
    (fun x hx y hy => (hall x hx).trans (hall y hy).symm)
  rw [L.upper_card] at hcard
  omega

#print axioms pivot_lt_upper_sup

end LastFirstLabels

end Erdos591.Positive.Game

end Erdos118.Reused591
