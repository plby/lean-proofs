import ErdosProblems.Erdos118.Reused591.OverlapLabels

namespace Erdos118.Reused591

/-!
# Root labels sharing the lower penultimate and both final indices

The upper first selected body is the lower penultimate selected body;
the last selected body is common. The intermediate upper bodies lie
strictly between these two shared indices. Both cardinalities are
independent positive request sizes at least two.
-/

namespace Erdos591.Positive.Game

structure AlignedRootLabels (H : Set ℕ) (B e d : ℕ) where
  lower : Finset ℕ
  upper : Finset ℕ
  shared : ℕ
  last : ℕ
  marker : ℕ
  lower_card : lower.card = e
  upper_card : upper.card = d
  shared_lower : shared ∈ lower
  shared_upper : shared ∈ upper
  last_lower : last ∈ lower
  last_upper : last ∈ upper
  shared_lt_last : shared < last
  lower_bounds : ∀ x ∈ lower, x = last ∨ x ≤ shared
  upper_bounds : ∀ x ∈ upper, shared ≤ x ∧ x ≤ last
  lower_fresh : ∀ x ∈ lower, x ∈ H ∧ B < x ∧ x < marker
  upper_fresh : ∀ x ∈ upper, x ∈ H ∧ B < x ∧ x < marker
  marker_fresh : marker ∈ H ∧ B < marker

namespace AlignedRootLabels

theorem exists_of_infinite {H : Set ℕ} (hH : H.Infinite) (B e d : ℕ)
    (he : 2 ≤ e) (hd : 2 ≤ d) : Nonempty (AlignedRootLabels H B e d) := by
  classical
  obtain ⟨L⟩ := LastFirstLabels.exists_of_infinite hH B (e - 1) (d - 1) (by omega) (by omega)
  obtain ⟨f, _hmono, hfH, hfB, _⟩ :=
    FastSequence.exists_above_finite_bounds hH ∅ (fun _ => L.marker)
  have hnotLower : L.marker ∉ L.lower :=
    fun h => Nat.lt_irrefl _ (L.lower_fresh _ h).2.2
  have hnotUpper : L.marker ∉ L.upper :=
    fun h => Nat.lt_irrefl _ (L.upper_fresh _ h).2.2
  refine ⟨⟨insert L.marker L.lower, insert L.marker L.upper, L.pivot, L.marker, f 0,
    ?_, ?_, by simp [L.pivot_lower], by simp [L.pivot_upper], by simp, by simp,
    (L.lower_fresh _ L.pivot_lower).2.2, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [Finset.card_insert_of_notMem hnotLower, L.lower_card]
    omega
  · rw [Finset.card_insert_of_notMem hnotUpper, L.upper_card]
    omega
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact Or.inl rfl
    · exact Or.inr (L.lower_le x hx)
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact ⟨(L.upper_fresh _ L.pivot_upper).2.2.le, le_rfl⟩
    · exact ⟨L.upper_ge x hx, (L.upper_fresh x hx).2.2.le⟩
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact ⟨L.marker_fresh.1, L.marker_fresh.2, hfB 0⟩
    · have hf := L.lower_fresh x hx
      exact ⟨hf.1, hf.2.1, hf.2.2.trans (hfB 0)⟩
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact ⟨L.marker_fresh.1, L.marker_fresh.2, hfB 0⟩
    · have hf := L.upper_fresh x hx
      exact ⟨hf.1, hf.2.1, hf.2.2.trans (hfB 0)⟩
  · exact ⟨hfH 0, L.marker_fresh.2.trans (hfB 0)⟩

variable {H : Set ℕ} {B e d : ℕ}

theorem lower_le_last (L : AlignedRootLabels H B e d) (x : ℕ) (hx : x ∈ L.lower) :
    x ≤ L.last := (L.lower_bounds x hx).elim Eq.le (fun h => h.trans L.shared_lt_last.le)

theorem lower_sup (L : AlignedRootLabels H B e d) : L.lower.sup id = L.last :=
  le_antisymm (Finset.sup_le L.lower_le_last) (Finset.le_sup (f := id) L.last_lower)

theorem upper_sup (L : AlignedRootLabels H B e d) : L.upper.sup id = L.last :=
  le_antisymm (Finset.sup_le (fun x hx => (L.upper_bounds x hx).2))
    (Finset.le_sup (f := id) L.last_upper)

theorem upper_min (L : AlignedRootLabels H B e d) :
    L.upper.min' ⟨L.shared, L.shared_upper⟩ = L.shared :=
  le_antisymm (Finset.min'_le _ _ L.shared_upper)
    (L.upper_bounds _ (Finset.min'_mem _ _)).1

theorem lower_penultimate (L : AlignedRootLabels H B e d) :
    (L.lower.erase L.last).sup id = L.shared := by
  apply le_antisymm
  · apply Finset.sup_le
    intro x hx
    exact (L.lower_bounds x (Finset.mem_of_mem_erase hx)).resolve_left (Finset.ne_of_mem_erase hx)
  · exact Finset.le_sup (f := id) (Finset.mem_erase.mpr ⟨L.shared_lt_last.ne, L.shared_lower⟩)

theorem intersection (L : AlignedRootLabels H B e d) :
    L.lower ∩ L.upper = {L.shared, L.last} := by
  ext x
  simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hl, hu⟩
    rcases L.lower_bounds x hl with heq | hle
    · exact Or.inr heq
    · exact Or.inl (le_antisymm hle (L.upper_bounds x hu).1)
  · rintro (rfl | rfl)
    · exact ⟨L.shared_lower, L.shared_upper⟩
    · exact ⟨L.last_lower, L.last_upper⟩

#print axioms exists_of_infinite
#print axioms lower_penultimate
#print axioms intersection

end AlignedRootLabels

end Erdos591.Positive.Game

end Erdos118.Reused591
