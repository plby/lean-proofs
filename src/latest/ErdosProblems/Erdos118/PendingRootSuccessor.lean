import ErdosProblems.Erdos118.LabelRanks
import ErdosProblems.Erdos118.ExactSlots

/-! Identify the actual next root by its gap or consecutive prefix
rank, retaining every later root in the exact pending tail. -/

namespace Erdos118.PendingRootSuccessor

open LabelledExtensions LabelledFrames DecisionStates

theorem above_cons_of_gap (C : List ℕ) (hC : C.Pairwise (· < ·)) (i j : ℕ)
    (hj : j ∈ C) (hij : i < j) (hmin : ∀ x ∈ C, i < x → j ≤ x) :
    ∃ rest : List ℕ, ExactSlots.above C i = j :: rest := by
  have hm : j ∈ ExactSlots.above C i := List.mem_filter.mpr ⟨hj, decide_eq_true hij⟩
  cases he : ExactSlots.above C i with
  | nil => simp [he] at hm
  | cons a rest =>
    have ha : a ∈ ExactSlots.above C i := he ▸ List.mem_cons_self ..
    obtain ⟨haC, hai⟩ := List.mem_filter.mp ha
    have hja : j ≤ a := hmin a haC (of_decide_eq_true hai)
    have hinc : (a :: rest).Pairwise (· < ·) := he ▸ hC.sublist List.filter_sublist
    rw [he] at hm
    rcases List.mem_cons.mp hm with h | h
    · subst j
      exact ⟨rest, rfl⟩
    · exact (not_lt_of_ge hja ((List.pairwise_cons.mp hinc).1 j h)).elim

theorem of_gap (P : Pending) (hP : ExactSlots.Exact (.leaf P)) (c : ℕ)
    (hc : c ∈ P.position.stem.rootLabel) (hcur : P.position.stem.done.length + 1 < c)
    (hmin : ∀ x ∈ P.position.stem.rootLabel, P.position.stem.done.length + 1 < x → c ≤ x) :
    ∃ rest : List ℕ, P.roots = c :: rest := by
  rw [hP.1]
  exact above_cons_of_gap _ P.position.stem.label_pairwise _ c hc hcur hmin

theorem of_rank (P : Pending) (hP : ExactSlots.Exact (.leaf P)) (c : ℕ)
    (hc : c ∈ P.position.stem.rootLabel)
    (hrank : LabelRanks.rank P.position.stem.rootLabel c =
      LabelRanks.rank P.position.stem.rootLabel (P.position.stem.done.length + 1) + 1) :
    ∃ rest : List ℕ, P.roots = c :: rest := by
  have hcur : P.position.stem.done.length + 1 < c := by
    rcases lt_trichotomy (P.position.stem.done.length + 1) c with h | h | h
    · exact h
    · rw [← h] at hrank
      omega
    · have hlt := LabelRanks.rank_lt P.rootSelected h
      omega
  apply of_gap P hP c hc hcur
  intro x hx hix
  by_contra hn
  have hxc : x < c := Nat.lt_of_not_ge hn
  have h₁ := LabelRanks.rank_lt hx hix
  have h₂ := LabelRanks.rank_lt hc hxc
  omega

end Erdos118.PendingRootSuccessor
