import ErdosProblems.Erdos118.ConservativeRuns

/-!
Fixed cut indices determine a unique prefix of one word. A selected cut
with no foreign coordinate in its gap contradicts exact annotations.
This is a structural obstruction, not the adaptive triangle theorem.
-/

namespace Erdos118.SkippedCuts

open Negative Negative.Exact LabelledExtensions LabelledFrames LabelCoarsening CutIndices
open PrefixRealization (below)

theorem partial_prefix_same_lengths {p q : G2} {n m : ℕ} {u v : List ℕ}
    (hpq : p.length = q.length) (huv : u.length = v.length)
    (h : p.flatMap levelWord ++ n :: u <+: q.flatMap levelWord ++ m :: v) :
    p = q ∧ n = m ∧ u = v := by
  induction p generalizing q with
  | nil =>
    have hq : q = [] := List.eq_nil_of_length_eq_zero hpq.symm
    subst q
    have he : n = m ∧ u <+: v := by
      simpa only [List.flatMap_nil, List.nil_append, List.cons_prefix_cons] using h
    exact ⟨rfl, he.1, he.2.eq_of_length huv⟩
  | cons a p ih =>
    cases q with
    | nil => simp at hpq
    | cons b q =>
      have h' : levelWord a ++ (p.flatMap levelWord ++ n :: u) <+:
          levelWord b ++ (q.flatMap levelWord ++ m :: v) := by
        simpa only [List.flatMap_cons, List.append_assoc] using h
      obtain ⟨hab, htail⟩ := WordResponses.levelWord_prefix_cancel h'
      obtain ⟨hpq', hnm, huv'⟩ := ih (by simpa only [List.length_cons,
        Nat.add_right_cancel_iff] using hpq) htail
      exact ⟨congrArg₂ List.cons hab hpq', hnm, huv'⟩

theorem interior_prefix_same_indices {P Q : InteriorWords.Position}
    (h : P.word <+: Q.word) (hi : P.done.length = Q.done.length)
    (hj : P.entries.length = Q.entries.length) : P = Q := by
  have he : P.root = Q.root ∧
      P.done.flatMap levelWord ++ P.size :: P.entries <+:
        Q.done.flatMap levelWord ++ Q.size :: Q.entries := by
    simpa only [InteriorWords.Position.word, PartialWordResponses.partialWord,
      List.cons_prefix_cons] using h
  obtain ⟨hd, hs, hu⟩ := partial_prefix_same_lengths hi hj he.2
  apply interior_word_injective
  simp only [InteriorWords.Position.word, PartialWordResponses.partialWord, he.1, hd, hs, hu]

theorem interior_common_prefix_same_indices {P Q : InteriorWords.Position} {w : List ℕ}
    (hP : P.word <+: w) (hQ : Q.word <+: w) (hi : P.done.length = Q.done.length)
    (hj : P.entries.length = Q.entries.length) : P = Q := by
  rcases List.prefix_or_prefix_of_prefix hP hQ with hpq | hqp
  · exact interior_prefix_same_indices hpq hi hj
  · exact (interior_prefix_same_indices hqp hi.symm hj.symm).symm

theorem cut_at_position {P : InteriorWords.Position} {S T : Stem}
    (hP : P.word <+: S.ordinary) (h : Cut S T P.done.length P.entries.length) :
    ∃ y ∈ T.ordinary, below y S.ordinary = P.word := by
  obtain ⟨y, hy, _, Q, hQ, hi, hj⟩ := h
  have hQprefix : Q.word <+: S.ordinary := by
    rw [hQ]
    exact List.takeWhile_prefix _
  have he := interior_common_prefix_same_indices hQprefix hP hi hj
  subst Q
  exact ⟨y, hy, hQ.symm⟩

theorem no_cut_across_gap {P : InteriorWords.Position} {S T : Stem} {x z : ℕ}
    (hprefix : P.word ++ [z] <+: S.ordinary) (hx : x ∈ P.word)
    (hgap : ∀ y ∈ T.ordinary, y ≤ x ∨ z < y) :
    ¬ Cut S T P.done.length P.entries.length := by
  intro hcut
  have hP : P.word <+: S.ordinary := (List.prefix_append _ _).trans hprefix
  obtain ⟨y, hy, hcut⟩ := cut_at_position hP hcut
  obtain ⟨tail, htail⟩ := hprefix
  have hS : S.ordinary = P.word ++ z :: tail := by
    simpa only [List.append_assoc, List.singleton_append] using htail.symm
  have hb := below_split_bounds y P.word (z :: tail)
    (hS ▸ (S.increasing.sublist S.ordinary_sublist)) (by rw [← hS]; exact hcut)
  have hxy := hb.1 x hx
  have hyz := hb.2 z (List.mem_cons_self ..)
  rcases hgap y hy with h | h <;> omega

theorem not_exact_of_gap {P : Pending} {S T : Stem} (hS : S.done.length = S.root)
    (hlabels : LabelledFrames.LabelsExtend (.pending P) (.terminal S hS)) {x z : ℕ}
    (hprefix : P.position.ordinary ++ [z] <+: S.ordinary) (hx : x ∈ P.position.ordinary)
    (hgap : ∀ y ∈ T.ordinary, y ≤ x ∨ z < y) : ¬ ExactAnnotations S T := by
  intro hexact
  obtain ⟨hi, hmem⟩ := selected_body_mem P S hS hlabels
  have hcut := (hexact.body P.position.stem.done.length hi P.position.entries.length).mp hmem
  apply no_cut_across_gap (P := P.position.toInterior)
    (by simpa only [Position.toInterior_word] using hprefix)
    (by simpa only [Position.toInterior_word] using hx) hgap
  simpa only [Position.toInterior, List.length_map] using hcut

open DecisionStates AdaptiveGame

theorem state_ordinary_sublist (S : State) : S.ordinary.Sublist S.decorated := by
  cases S with
  | initial => exact List.Sublist.refl _
  | body D => exact D.stem.ordinary_sublist
  | leaf F => exact F.position.ordinary_sublist
  | complete T => exact T.stem.ordinary_sublist

structure StateExtension (S T : State) : Prop where
  ordinary : S.ordinary <+: T.ordinary
  decorated : S.decorated <+: T.decorated
  labels : DecisionStates.LabelsExtend S T

theorem StateExtension.refl (S : State) : StateExtension S S :=
  ⟨List.prefix_rfl, List.prefix_rfl, DecisionStates.LabelsExtend.refl _⟩

theorem StateExtension.trans {S T U : State} (hST : StateExtension S T)
    (hTU : StateExtension T U) : StateExtension S U :=
  ⟨hST.ordinary.trans hTU.ordinary, hST.decorated.trans hTU.decorated,
    hST.labels.trans hTU.labels⟩

theorem stateExtension_of_step {S T : State} (h : DecisionStates.Step T S) :
    StateExtension S T := by
  obtain ⟨v, d, hv, hd, _, _⟩ := DecisionStates.step_extensions h
  exact ⟨⟨v, hv.symm⟩, ⟨d, hd.symm⟩, DecisionStates.step_labels h⟩

theorem run_extensions {H : Set ℕ} {payoff : Completed → Completed → Bool}
    {S T : State × State} (h : ConservativeRuns.Run H payoff S T) :
    StateExtension S.1 T.1 ∧ StateExtension S.2 T.2 := by
  induction h with
  | refl => exact ⟨StateExtension.refl _, StateExtension.refl _⟩
  | tail hprev hstep ih =>
    cases hstep with
    | left n R hs hR a hH hlarge =>
      exact ⟨ih.1.trans (stateExtension_of_step (R.step a)), ih.2⟩
    | right n R hs hR a hH hlarge =>
      exact ⟨ih.1, ih.2.trans (stateExtension_of_step (R.step a))⟩

theorem run_right_future {H : Set ℕ} {payoff : Completed → Completed → Bool}
    {S T : State × State} (h : ConservativeRuns.Run H payoff S T)
    {x : ℕ} (hx : x ∈ S.1.decorated) :
    ∀ y ∈ T.2.decorated, y ∈ S.2.decorated ∨ x < y := by
  induction h with
  | refl => exact fun y hy ↦ Or.inl hy
  | @tail U V hprev hstep ih =>
    cases hstep with
    | left n R hs hR a hH hlarge => exact ih
    | right n R hs hR a hH hlarge =>
      obtain ⟨d, hd, hsupport⟩ := R.suffix a
      intro y hy
      rw [hd] at hy
      rcases List.mem_append.mp hy with hy | hy
      · exact ih y hy
      · have hxU : x ∈ U.1.decorated := (run_extensions hprev).1.decorated.subset hx
        exact Or.inr ((pairBound_left U hxU).trans_lt
          (R.large a y (hsupport ▸ List.mem_toFinset.mpr hy)))

theorem run_left_future {H : Set ℕ} {payoff : Completed → Completed → Bool}
    {S T : State × State} (h : ConservativeRuns.Run H payoff S T)
    {x : ℕ} (hx : x ∈ S.2.decorated) :
    ∀ y ∈ T.1.decorated, y ∈ S.1.decorated ∨ x < y := by
  induction h with
  | refl => exact fun y hy ↦ Or.inl hy
  | @tail U V hprev hstep ih =>
    cases hstep with
    | left n R hs hR a hH hlarge =>
      obtain ⟨d, hd, hsupport⟩ := R.suffix a
      intro y hy
      rw [hd] at hy
      rcases List.mem_append.mp hy with hy | hy
      · exact ih y hy
      · have hxU : x ∈ U.2.decorated := (run_extensions hprev).2.decorated.subset hx
        exact Or.inr ((pairBound_right U hxU).trans_lt
          (R.large a y (hsupport ▸ List.mem_toFinset.mpr hy)))
    | right n R hs hR a hH hlarge => exact ih

theorem response_ordinary_suffix {S : State} {b : ℕ} (R : Response S b)
    (a : R.family.members) :
    ∃ v : List ℕ, (R.result a).ordinary = S.ordinary ++ v ∧ v ≠ [] ∧
      ∀ x ∈ v, b < x := by
  obtain ⟨v, d, hv, hd, hvne, hvd⟩ := DecisionStates.step_extensions (R.step a)
  obtain ⟨e, he, hs⟩ := R.suffix a
  have hde : d = e := List.append_cancel_left (hd.symm.trans he)
  subst e
  exact ⟨v, hv, hvne, fun x hx ↦ R.large a x
    (hs ▸ List.mem_toFinset.mpr (hvd.subset hx))⟩

theorem consecutive_left_not_clear (W : State × State)
    (R : Response W.1 (pairBound W)) (a : R.family.members) (P : Pending)
    (hP : R.result a = .leaf P)
    (Q : Response (.leaf P) (pairBound (.leaf P, W.2))) (b : Q.family.members)
    (U V : Completed) {H : Set ℕ} {payoff : Completed → Completed → Bool}
    (hrun : ConservativeRuns.Run H payoff (Q.result b, W.2) (.complete U, .complete V)) :
    ¬ ClearPairs.ClearPair U.stem V.stem := by
  obtain ⟨v, hv, hvne, hvlarge⟩ := response_ordinary_suffix R a
  obtain ⟨x, xs, hxv⟩ := List.exists_cons_of_ne_nil hvne
  have hxvMem : x ∈ v := hxv ▸ List.mem_cons_self ..
  have hx : x ∈ P.position.ordinary := by
    have hx' : x ∈ (R.result a).ordinary := hv ▸ List.mem_append_right _ hxvMem
    simpa only [hP, State.ordinary] using hx'
  obtain ⟨w, hw, hwne, _⟩ := response_ordinary_suffix Q b
  obtain ⟨z, zs, hzw⟩ := List.exists_cons_of_ne_nil hwne
  have hz : z ∈ (Q.result b).decorated := by
    apply (state_ordinary_sublist _).subset
    rw [hw, hzw]
    exact List.mem_append_right _ (List.mem_cons_self ..)
  have hprefix : P.position.ordinary ++ [z] <+: U.stem.ordinary := by
    apply List.IsPrefix.trans (l₂ := (Q.result b).ordinary)
    · refine ⟨zs, ?_⟩
      simpa only [State.ordinary, hzw, List.append_assoc, List.singleton_append] using hw.symm
    · exact (run_extensions hrun).1.ordinary
  have hlabels : LabelledFrames.LabelsExtend (.pending P) (.terminal U.stem U.full) := by
    have h := ((stateExtension_of_step (Q.step b)).trans (run_extensions hrun).1).labels
    exact ⟨h.root, h.bodies⟩
  have hgap : ∀ y ∈ V.stem.ordinary, y ≤ x ∨ z < y := by
    intro y hy
    have hy' : y ∈ State.decorated (.complete V) := V.stem.ordinary_sublist.subset hy
    rcases run_right_future hrun hz y hy' with hold | hnew
    · exact Or.inl ((pairBound_right W hold).trans_lt (hvlarge x hxvMem)).le
    · exact Or.inr hnew
  exact fun hclear ↦ not_exact_of_gap U.full hlabels hprefix hx hgap hclear.exactLeft

theorem consecutive_right_not_clear (W : State × State)
    (R : Response W.2 (pairBound W)) (a : R.family.members) (P : Pending)
    (hP : R.result a = .leaf P)
    (Q : Response (.leaf P) (pairBound (W.1, .leaf P))) (b : Q.family.members)
    (U V : Completed) {H : Set ℕ} {payoff : Completed → Completed → Bool}
    (hrun : ConservativeRuns.Run H payoff (W.1, Q.result b) (.complete U, .complete V)) :
    ¬ ClearPairs.ClearPair U.stem V.stem := by
  obtain ⟨v, hv, hvne, hvlarge⟩ := response_ordinary_suffix R a
  obtain ⟨x, xs, hxv⟩ := List.exists_cons_of_ne_nil hvne
  have hxvMem : x ∈ v := hxv ▸ List.mem_cons_self ..
  have hx : x ∈ P.position.ordinary := by
    have hx' : x ∈ (R.result a).ordinary := hv ▸ List.mem_append_right _ hxvMem
    simpa only [hP, State.ordinary] using hx'
  obtain ⟨w, hw, hwne, _⟩ := response_ordinary_suffix Q b
  obtain ⟨z, zs, hzw⟩ := List.exists_cons_of_ne_nil hwne
  have hz : z ∈ (Q.result b).decorated := by
    apply (state_ordinary_sublist _).subset
    rw [hw, hzw]
    exact List.mem_append_right _ (List.mem_cons_self ..)
  have hprefix : P.position.ordinary ++ [z] <+: V.stem.ordinary := by
    apply List.IsPrefix.trans (l₂ := (Q.result b).ordinary)
    · refine ⟨zs, ?_⟩
      simpa only [State.ordinary, hzw, List.append_assoc, List.singleton_append] using hw.symm
    · exact (run_extensions hrun).2.ordinary
  have hlabels : LabelledFrames.LabelsExtend (.pending P) (.terminal V.stem V.full) := by
    have h := ((stateExtension_of_step (Q.step b)).trans (run_extensions hrun).2).labels
    exact ⟨h.root, h.bodies⟩
  have hgap : ∀ y ∈ U.stem.ordinary, y ≤ x ∨ z < y := by
    intro y hy
    have hy' : y ∈ State.decorated (.complete U) := U.stem.ordinary_sublist.subset hy
    rcases run_left_future hrun hz y hy' with hold | hnew
    · exact Or.inl ((pairBound_left W hold).trans_lt (hvlarge x hxvMem)).le
    · exact Or.inr hnew
  exact fun hclear ↦ not_exact_of_gap V.full hlabels hprefix hx hgap hclear.exactRight

end Erdos118.SkippedCuts
