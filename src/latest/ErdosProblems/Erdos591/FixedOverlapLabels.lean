import ErdosProblems.Erdos591.OverlapLabels
import ErdosProblems.Erdos591.SparseReserves

/-!
# Last--first overlap without changing an existing lower label

A finite reserve between the last lower label and its existing marker
can supply the upper label. The lower label and marker are preserved
exactly. The existence of sufficiently large reserves in a particular
strategy history is a separate hypothesis, not an implicit assumption.
-/

namespace Erdos591.Positive.Game.LastFirstLabels

theorem exists_with_fixed_lower {H : Set ℕ} {B c p n : ℕ} (A R : Finset ℕ)
    (hc : 0 < c) (hp : p ∈ A) (hmax : ∀ x ∈ A, x ≤ p)
    (hA : ∀ x ∈ A, x ∈ H ∧ B < x ∧ x < n) (hn : n ∈ H ∧ B < n)
    (hcard : c - 1 ≤ R.card) (hR : ∀ x ∈ R, x ∈ H ∧ p < x ∧ x < n) :
    ∃ L : LastFirstLabels H B A.card c, L.lower = A ∧ L.pivot = p ∧ L.marker = n := by
  classical
  obtain ⟨S, hSR, hScard⟩ := Finset.exists_subset_card_eq hcard
  have hpS : p ∉ S := by
    intro hmem
    exact (Nat.lt_irrefl p) (hR p (hSR hmem)).2.1
  have hupperCard : (insert p S).card = c := by
    rw [Finset.card_insert_of_notMem hpS, hScard]
    omega
  have hupperGe : ∀ x ∈ insert p S, p ≤ x := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact le_rfl
    · exact (hR x (hSR hx)).2.1.le
  have hupperFresh : ∀ x ∈ insert p S, x ∈ H ∧ B < x ∧ x < n := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hA _ hp
    · have hg := hR x (hSR hx)
      exact ⟨hg.1, (hA p hp).2.1.trans hg.2.1, hg.2.2⟩
  exact ⟨⟨A, insert p S, p, n, rfl, hupperCard, hp, Finset.mem_insert_self _ _,
    hmax, hupperGe, hA, hupperFresh, hn⟩, rfl, rfl, rfl⟩

#print axioms exists_with_fixed_lower

end Erdos591.Positive.Game.LastFirstLabels
