import ErdosProblems.Erdos118.SkippedCuts

/-! Numerical order of genuine interior parses and threshold cuts. -/

namespace Erdos118.CutOrder

open Negative Negative.Exact LabelledExtensions LabelCoarsening CutIndices
open PrefixRealization (below)

theorem partial_prefix_counts {p q : G2} {n m : ℕ} {u v : List ℕ}
    (hv : v.length < m)
    (h : p.flatMap levelWord ++ n :: u <+: q.flatMap levelWord ++ m :: v) :
    p.length ≤ q.length ∧
      (p.length = q.length → p = q ∧ n = m ∧ u <+: v) := by
  induction p generalizing q with
  | nil =>
    refine ⟨Nat.zero_le _, ?_⟩
    intro hlen
    have hq : q = [] := List.eq_nil_of_length_eq_zero hlen.symm
    subst q
    have he : n = m ∧ u <+: v := by
      simpa only [List.flatMap_nil, List.nil_append, List.cons_prefix_cons] using h
    exact ⟨rfl, he⟩
  | cons a p ih =>
    cases q with
    | nil =>
      have he : a.length = m ∧ a ++ (p.flatMap levelWord ++ n :: u) <+: v := by
        simpa only [List.flatMap_cons, List.flatMap_nil, List.nil_append, levelWord,
          List.cons_append, List.append_assoc, List.cons_prefix_cons] using h
      have hlen := he.2.length_le
      simp only [List.length_append, List.length_cons] at hlen
      omega
    | cons b q =>
      have hh : levelWord a ++ (p.flatMap levelWord ++ n :: u) <+:
          levelWord b ++ (q.flatMap levelWord ++ m :: v) := by
        simpa only [List.flatMap_cons, List.append_assoc] using h
      obtain ⟨hab, ht⟩ := WordResponses.levelWord_prefix_cancel hh
      obtain ⟨hle, he⟩ := ih ht
      refine ⟨Nat.succ_le_succ hle, ?_⟩
      intro hlen
      obtain ⟨hpq, hnm, huv⟩ := he (Nat.succ.inj hlen)
      exact ⟨congrArg₂ List.cons hab hpq, hnm, huv⟩

theorem interior_prefix_counts {P Q : InteriorWords.Position} (h : P.word <+: Q.word) :
    P.done.length ≤ Q.done.length ∧
      (P.done.length = Q.done.length →
        P.done = Q.done ∧ P.size = Q.size ∧ P.entries <+: Q.entries) := by
  have he : P.root = Q.root ∧
      P.done.flatMap levelWord ++ P.size :: P.entries <+:
        Q.done.flatMap levelWord ++ Q.size :: Q.entries := by
    simpa only [InteriorWords.Position.word, PartialWordResponses.partialWord,
      List.cons_prefix_cons] using h
  exact partial_prefix_counts Q.unfinished he.2

theorem below_prefix {y z : ℕ} (hyz : y ≤ z) (xs : List ℕ) :
    below y xs <+: below z xs := by
  induction xs with
  | nil => exact List.prefix_rfl
  | cons a xs ih =>
    by_cases ha : a < y
    · have haz := ha.trans_le hyz
      simpa only [below, List.takeWhile_cons, decide_eq_true ha,
        decide_eq_true haz, Bool.true_eq, ↓reduceIte, List.cons_prefix_cons] using
        (show a = a ∧ below y xs <+: below z xs from ⟨rfl, ih⟩)
    · simp [below, ha]

theorem first_cut_bounds (S T : Stem) (P : InteriorWords.Position)
    (hP : P.word = below T.root S.ordinary) {i j : ℕ} (hcut : Cut S T i j) :
    P.done.length ≤ i ∧ (P.done.length = i → P.entries.length ≤ j) := by
  obtain ⟨y, hy, _, Q, hQ, hi, hj⟩ := hcut
  have hroot : T.root ≤ y := by
    have hp := (T.increasing.sublist T.ordinary_sublist).imp Nat.le_of_lt
    simpa only [Stem.ordinary, List.head_cons] using hp.rel_head hy
  have hprefix : P.word <+: Q.word := by
    rw [hP, hQ]
    exact below_prefix hroot _
  have hc := interior_prefix_counts hprefix
  refine ⟨hc.1.trans_eq hi, ?_⟩
  intro he
  exact ((hc.2 (he.trans hi.symm)).2.2.length_le).trans_eq hj

end Erdos118.CutOrder
