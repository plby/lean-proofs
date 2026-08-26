import ErdosProblems.Erdos118.ExactSlots

/-! Minimal later labels give the actual next slot; equal ordinary words
and entry counts determine the literal stem, marker, and entries. -/

namespace Erdos118.NextSelectedLeaf

open LabelledExtensions LabelledFrames DecisionStates

theorem above_first (C : List ℕ) (hC : C.Pairwise (· < ·)) (i j : ℕ)
    (hj : j ∈ C) (hij : i < j) (hmin : ∀ k ∈ C, i < k → j ≤ k) :
    ∃ rest : List ℕ, ExactSlots.above C i = j :: rest := by
  have hm : j ∈ ExactSlots.above C i := List.mem_filter.mpr ⟨hj, decide_eq_true hij⟩
  obtain ⟨k, rest, he⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_mem hm)
  have hk : k ∈ ExactSlots.above C i := he ▸ List.mem_cons_self ..
  obtain ⟨hkC, hki⟩ := List.mem_filter.mp hk
  have hjk : j ≤ k := hmin k hkC (of_decide_eq_true hki)
  have hinc : (k :: rest).Pairwise (· < ·) := he ▸ hC.sublist List.filter_sublist
  have hkj : k ≤ j := by
    rw [he] at hm
    rcases List.mem_cons.mp hm with heq | hm
    · exact heq.symm.le
    · exact ((List.pairwise_cons.mp hinc).1 j hm).le
  have hkj' : k = j := le_antisymm hkj hjk
  subst k
  exact ⟨rest, he⟩

theorem next_leaf (P : Pending) (hP : ExactSlots.Exact (.leaf P)) (j : ℕ)
    (hj : j ∈ P.position.label) (hij : P.position.entries.length < j)
    (hmin : ∀ k ∈ P.position.label, P.position.entries.length < k → j ≤ k) :
    ∃ rest : List ℕ, P.leaves = j :: rest := by
  obtain ⟨rest, he⟩ := above_first P.position.label P.position.label_pairwise
    P.position.entries.length j hj hij hmin
  exact ⟨rest, hP.2.trans he⟩

theorem first_roots_nonempty (P : Pending) (hP : ExactSlots.Exact (.leaf P))
    (hfirst : P.position.stem.done.length + 1 = P.position.stem.rootLabel.headD 0)
    (hlen : 1 < P.position.stem.rootLabel.length) : P.roots ≠ [] := by
  rw [hP.1, hfirst, ExactSlots.above_head _ P.position.stem.label_pairwise]
  intro he
  have h := congrArg List.length he
  rw [List.length_tail] at h
  simp only [List.length_nil] at h
  omega

theorem ordinary_parts (P Q : Position) (hord : Q.ordinary = P.ordinary)
    (hlen : Q.entries.length = P.entries.length) :
    Q.stem.ordinary = P.stem.ordinary ∧ Q.size = P.size ∧ Q.entries = P.entries := by
  have htail : (Q.size :: Q.entries).length = (P.size :: P.entries).length := by simp [hlen]
  obtain ⟨hs, ht⟩ := List.append_inj' hord htail
  exact ⟨hs, (List.cons.inj ht).1, (List.cons.inj ht).2⟩

end Erdos118.NextSelectedLeaf
