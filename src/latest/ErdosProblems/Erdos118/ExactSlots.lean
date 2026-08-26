import ErdosProblems.Erdos118.ConservativeRuns

/-!
Reachable decision states retain exactly the label coordinates above their
current selected indices. Empty remaining lists therefore identify actual
last labels, not merely a possibly incomplete bounded list of future slots.
-/

namespace Erdos118.ExactSlots

open LabelledExtensions LabelledFrames DecisionStates

def above (C : List ℕ) (i : ℕ) : List ℕ := C.filter (fun x ↦ decide (i < x))

theorem above_head (C : List ℕ) (hC : C.Pairwise (· < ·)) :
    above C (C.headD 0) = C.tail := by
  cases C with
  | nil => rfl
  | cons c C =>
    have hfilter : C.filter (fun x ↦ decide (c < x)) = C :=
      List.filter_eq_self.mpr (fun x hx ↦ decide_eq_true ((List.pairwise_cons.mp hC).1 x hx))
    simp [above, hfilter]

theorem above_after_first (C : List ℕ) (hC : C.Pairwise (· < ·)) {i j : ℕ}
    (hij : i < j) (rest : List ℕ) (h : above C i = j :: rest) : above C j = rest := by
  have hfilter : above (above C i) j = above C j := by
    unfold above
    rw [List.filter_filter]
    apply List.filter_congr
    intro x hx
    by_cases hjx : j < x
    · simp [hjx, hij.trans hjx]
    · simp [hjx]
  have hinc : (j :: rest).Pairwise (· < ·) := h ▸ hC.sublist List.filter_sublist
  calc
    above C j = above (above C i) j := hfilter.symm
    _ = above (j :: rest) j := congrArg (fun L ↦ above L j) h
    _ = rest := above_head (j :: rest) hinc

theorem last_of_above_empty (C : List ℕ) (hC : C.Pairwise (· < ·)) {i : ℕ}
    (hi : i ∈ C) (hempty : above C i = []) : C.getLastD 0 = i := by
  have hne : C ≠ [] := List.ne_nil_of_mem hi
  have hle : ∀ x ∈ C, x ≤ i := by
    intro x hx
    by_contra hnot
    have hix : i < x := Nat.lt_of_not_ge hnot
    have hm : x ∈ above C i := List.mem_filter.mpr ⟨hx, decide_eq_true hix⟩
    rw [hempty] at hm
    exact List.not_mem_nil hm
  have hilast : i ≤ C.getLast hne :=
    (hC.imp Nat.le_of_lt).rel_getLast hi
  have he : C.getLast hne = i := le_antisymm (hle _ (List.getLast_mem hne)) hilast
  rw [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hne, he]
  rfl

def Exact : State → Prop
  | .initial | .complete _ => True
  | .body D => D.roots = above D.stem.rootLabel (D.stem.done.length + 1)
  | .leaf F =>
      F.roots = above F.position.stem.rootLabel (F.position.stem.done.length + 1) ∧
      F.leaves = above F.position.label F.position.entries.length

theorem step_exact {S T : State} (h : DecisionStates.Step T S) (hS : Exact S) : Exact T := by
  cases h with
  | root A =>
    change A.stem.rootLabel.tail = above A.stem.rootLabel (A.stem.done.length + 1)
    rw [A.first_body, above_head _ A.stem.label_pairwise]
  | whole s => trivial
  | body D A =>
    change D.roots = above A.position.stem.rootLabel (A.position.stem.done.length + 1) ∧
      A.position.label.tail = above A.position.label A.position.entries.length
    constructor
    · rw [A.stem_eq]
      exact hS
    · rw [A.entries_length, above_head _ A.position.label_pairwise]
  | leaf F j rest hF A =>
    have hslot := F.leafSlots.bounded j (hF ▸ List.mem_cons_self ..)
    have he := above_after_first F.position.label F.position.label_pairwise hslot.1 rest
      (hS.2.symm.trans hF)
    change F.roots = above F.position.stem.rootLabel (F.position.stem.done.length + 1) ∧
      rest = above F.position.label (F.position.entries ++ A.newWord).length
    refine ⟨hS.1, ?_⟩
    rw [List.length_append, A.length_eq, Nat.add_sub_of_le hslot.1.le]
    exact he.symm
  | nextBody F c rest hR hL A =>
    have hslot := F.rootSlots.bounded c (hR ▸ List.mem_cons_self ..)
    have he := above_after_first F.position.stem.rootLabel F.position.stem.label_pairwise
      hslot.1 rest (hS.1.symm.trans hR)
    change rest = above A.stem.rootLabel (A.stem.done.length + 1)
    rw [A.rootLabel_eq, A.count, Nat.sub_add_cancel (by omega)]
    exact he.symm
  | finish F hR hL A => trivial

theorem run_exact_left {H : Set ℕ} {payoff : Completed → Completed → Bool} {S T : State × State}
    (h : ConservativeRuns.Run H payoff S T) (hS : Exact S.1) : Exact T.1 := by
  induction h with
  | refl => exact hS
  | tail hprev hstep ih =>
    cases hstep with
    | left n R hs hR a hH hlarge => exact step_exact (R.step a) ih
    | right n R hs hR a hH hlarge => exact ih

theorem run_exact_right {H : Set ℕ} {payoff : Completed → Completed → Bool} {S T : State × State}
    (h : ConservativeRuns.Run H payoff S T) (hS : Exact S.2) : Exact T.2 := by
  induction h with
  | refl => exact hS
  | tail hprev hstep ih =>
    cases hstep with
    | left n R hs hR a hH hlarge => exact ih
    | right n R hs hR a hH hlarge => exact step_exact (R.step a) ih

theorem run_exact {H : Set ℕ} {payoff : Completed → Completed → Bool} {S T : State × State}
    (h : ConservativeRuns.Run H payoff S T) (hS : Exact S.1 ∧ Exact S.2) :
    Exact T.1 ∧ Exact T.2 := ⟨run_exact_left h hS.1, run_exact_right h hS.2⟩

theorem pending_last_root (P : Pending) (hP : Exact (.leaf P)) (hR : P.roots = []) :
    P.position.stem.rootLabel.getLastD 0 = P.position.stem.done.length + 1 :=
  last_of_above_empty _ P.position.stem.label_pairwise P.rootSelected (hP.1.symm.trans hR)

theorem pending_last_leaf (P : Pending) (hP : Exact (.leaf P)) (hL : P.leaves = []) :
    P.position.label.getLastD 0 = P.position.entries.length :=
  last_of_above_empty _ P.position.label_pairwise P.leafSelected (hP.2.symm.trans hL)

theorem pending_next_last (P : Pending) (hP : Exact (.leaf P)) {j : ℕ}
    (hL : P.leaves = [j]) : P.position.label.getLastD 0 = j := by
  have hslot := P.leafSlots.bounded j (hL ▸ List.mem_singleton_self _)
  have he := above_after_first P.position.label P.position.label_pairwise hslot.1 []
    (hP.2.symm.trans hL)
  exact last_of_above_empty P.position.label P.position.label_pairwise hslot.2.2 he

theorem pending_next_last_root (P : Pending) (hP : Exact (.leaf P)) {c : ℕ}
    (hR : P.roots = [c]) : P.position.stem.rootLabel.getLastD 0 = c := by
  have hslot := P.rootSlots.bounded c (hR ▸ List.mem_singleton_self _)
  have he := above_after_first P.position.stem.rootLabel P.position.stem.label_pairwise
    hslot.1 [] (hP.1.symm.trans hR)
  exact last_of_above_empty P.position.stem.rootLabel P.position.stem.label_pairwise hslot.2.2 he

end Erdos118.ExactSlots
