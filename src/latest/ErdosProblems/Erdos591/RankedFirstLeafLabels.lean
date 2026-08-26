import ErdosProblems.Erdos591.CriticalLeafLabels

/-!
# A first target leaf at any positive nonfinal source rank

For a nonsingleton target, its second selection is exactly the source
maximum. A singleton target keeps just the shared pivot. This is the
strict T-anchor pattern and also handles a singleton upper U request.
-/

namespace Erdos591.Positive.Game

namespace LastFirstLabels

def singleton_first_view {H : Set ℕ} {B a c : ℕ}
    (L : LastFirstLabels H B a c) : LastFirstLabels H B 1 1 where
  lower := {L.pivot}
  upper := {L.pivot}
  pivot := L.pivot
  marker := L.marker
  lower_card := by simp
  upper_card := by simp
  pivot_lower := by simp
  pivot_upper := by simp
  lower_le := fun _ hx => (Finset.mem_singleton.mp hx).le
  upper_ge := fun _ hx => (Finset.mem_singleton.mp hx).ge
  lower_fresh := by
    intro x hx
    rw [Finset.mem_singleton.mp hx]
    exact L.lower_fresh _ L.pivot_lower
  upper_fresh := by
    intro x hx
    rw [Finset.mem_singleton.mp hx]
    exact L.upper_fresh _ L.pivot_upper
  marker_fresh := L.marker_fresh

end LastFirstLabels

structure RankedFirstLeafLabels (H : Set ℕ) (B n c s : ℕ) where
  source : Finset ℕ
  targetView : LastFirstLabels H B 1 c
  source_card : source.card = n
  pivot_source : targetView.pivot ∈ source
  pivot_rank : (source.filter (fun x => x ≤ targetView.pivot)).card = s
  pivot_lt_last : targetView.pivot < source.sup id
  last_target : 2 ≤ c → source.sup id ∈ targetView.upper
  target_next : ∀ x ∈ targetView.upper, targetView.pivot < x → source.sup id ≤ x
  source_fresh : ∀ x ∈ source, x ∈ H ∧ B < x ∧ x < targetView.marker

namespace RankedFirstLeafLabels

theorem exists_of_infinite {H : Set ℕ} (hH : H.Infinite) (B n c s : ℕ)
    (hs : 0 < s) (hsn : s < n) (hc : 0 < c) : Nonempty (RankedFirstLeafLabels H B n c s) := by
  by_cases htwo : 2 ≤ c
  · obtain ⟨L⟩ := CriticalLeafLabels.exists_of_infinite hH B n c s hs hsn htwo
    exact ⟨⟨L.lower, L.upperView, L.lower_card, L.pivot_lower, L.pivot_rank,
      L.pivot_lt_last, fun _ => L.last_upper, L.upper_next, L.lower_fresh⟩⟩
  · have heq : c = 1 := by omega
    subst c
    obtain ⟨L⟩ := CriticalLeafLabels.exists_of_infinite hH B n 2 s hs hsn (by omega)
    refine ⟨⟨L.lower, L.upperView.singleton_first_view, L.lower_card, L.pivot_lower,
      L.pivot_rank, L.pivot_lt_last, by omega, ?_, L.lower_fresh⟩⟩
    intro x hx hlt
    have hx' : x = L.upperView.pivot := Finset.mem_singleton.mp hx
    exact (not_lt_of_ge hx'.le hlt).elim

theorem target_singleton {H : Set ℕ} {B n s : ℕ}
    (L : RankedFirstLeafLabels H B n 1 s) : L.targetView.upper = {L.targetView.pivot} := by
  apply Finset.eq_singleton_iff_unique_mem.mpr
  exact ⟨L.targetView.pivot_upper, fun x hx => Finset.card_le_one.mp
    L.targetView.upper_card.le x hx L.targetView.pivot L.targetView.pivot_upper⟩

#print axioms exists_of_infinite
#print axioms target_singleton

end RankedFirstLeafLabels

end Erdos591.Positive.Game
