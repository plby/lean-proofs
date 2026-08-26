import ErdosProblems.Erdos591.PreliminaryFirstPhase
import ErdosProblems.Erdos591.PreliminaryUpperSecond
import ErdosProblems.Erdos591.PreliminaryZeroUpper

/-!
# The three actual preliminary plays when the second group is empty

Record the upper T bound first, exhaust the old lower T body, submit
the upper second-leaf reply, and record its U continuation request.
Then share beta between the two lower plays. All old U coordinates
remain unchanged, and both S words are in their last selected body.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem preliminary_rank_one_start {N H J HD : Set ℕ}
    (hHN : H ⊆ N) (hJH : J ⊆ H) (hJ : J.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    (origin old p q upper : Concrete.Hist N) {a B P Q r BT n c s : ℕ}
    (L : PreliminaryPivotLabels J B P Q r 0) (D : CriticalLeafLabels HD BT n c s)
    (ha : 2 ≤ a) (hop : origin.position.pending = some ⟨false, .advance a⟩)
    (hboard : origin.position.board = Board.initial) (hmode : origin.position.mode = some true)
    (hwin : (exactGame N blue).ArchitectWins H b σ origin)
    (hfromOld : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin old)
    (hOldP : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) old p)
    (hfromQ : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin q)
    (hfromUpper : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin upper)
    (hOld : CriticalCheckpoint old)
    (hp : p.position.pending = some ⟨false, .advance P⟩)
    (hq : q.position.pending = some ⟨false, .advance Q⟩)
    (hstem : LabeledWord.SameStructure p.position.board.left q.position.board.left)
    (hmP : p.position.board.left.markerEvent = true)
    (hmQ : q.position.board.left.markerEvent = true)
    (hrootP : ∀ i ∈ p.position.board.left.rootLabel,
      i ≤ p.position.board.left.bodyLabels.length + 1)
    (hrootQ : ∀ i ∈ q.position.board.left.rootLabel,
      i ≤ q.position.board.left.bodyLabels.length + 1)
    (hotherP : p.position.board.right = old.position.board.right)
    (hBP : max p.position.bound (b p) ≤ B) (hBQ : max q.position.bound (b q) ≤ B)
    (hOldLabel : old.position.board.right.currentLabel = D.lower)
    (hOldIndex : old.position.board.right.leafIndex = D.upperView.pivot)
    (hrank : old.position.board.right.currentLabel.card -
      (old.position.board.right.currentLabel.filter
        (fun x => x ≤ old.position.board.right.leafIndex)).card = r)
    (hfutureT : ∃ i ∈ old.position.board.right.rootLabel,
      old.position.board.right.bodyLabels.length < i)
    (hTshape : LabeledWord.SameStructure upper.position.board.left old.position.board.right)
    (hTrel : upper.position.board.left.relaxed = true)
    (hTlabel : upper.position.board.left.currentLabel = D.upperView.upper)
    (hTindex : upper.position.board.left.leafIndex = D.upperView.pivot)
    (hUshape : LabeledWord.SameStructure q.position.board.right upper.position.board.right)
    (hUrel : upper.position.board.right.relaxed = true)
    (hUQrel : q.position.board.right.relaxed = true)
    (hUpending : Macro.Pending upper.position.board.right)
    (hUQpending : Macro.Pending q.position.board.right)
    (hUsep : ∀ x ∈ upper.position.board.left.coordinates,
      x ≤ upper.position.board.right.coordinates.getLastD 0)
    (hall : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin z →
      (exactGame N blue).kind z = .terminal w →
        z.position.board.left.beforeLastLeafCount < z.position.board.right.beforeLastLeafCount) :
    ∃ st su tu,
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ J b) p st ∧
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ J b) q su ∧
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ J b) upper tu ∧
      st.position.pending = some ⟨true, .advance 0⟩ ∧
      su.position.pending = some ⟨true, .advance 0⟩ ∧
      tu.position.pending = some ⟨true, .advance 0⟩ ∧
      LabeledWord.SameStructure st.position.board.left su.position.board.left ∧
      LabeledWord.SameStructure st.position.board.right tu.position.board.left ∧
      LabeledWord.SameStructure su.position.board.right tu.position.board.right ∧
      st.position.board.left.relaxed = true ∧ su.position.board.left.relaxed = true ∧
      st.position.board.left.currentLabel = L.lower ∧
      su.position.board.left.currentLabel = L.upper ∧
      st.position.board.left.leafIndex = L.beta ∧ su.position.board.left.leafIndex = L.beta ∧
      st.position.board.left.rootLabel = p.position.board.left.rootLabel ∧
      su.position.board.left.rootLabel = q.position.board.left.rootLabel ∧
      st.position.board.left.bodyLabels = p.position.board.left.bodyLabels ++ [L.lower] ∧
      su.position.board.left.bodyLabels = q.position.board.left.bodyLabels ++ [L.upper] ∧
      (∀ i ∈ st.position.board.left.rootLabel,
        i ≤ st.position.board.left.bodyLabels.length) ∧
      (∀ i ∈ su.position.board.left.rootLabel,
        i ≤ su.position.board.left.bodyLabels.length) ∧
      st.position.board.right.relaxed = true ∧ st.position.board.right.NoLeafPending ∧
      st.position.board.right.bodyLabels = old.position.board.right.bodyLabels ∧
      st.position.board.right.leafIndex = D.lower.sup id ∧
      su.position.board.right = q.position.board.right ∧
      tu.position.board.right = upper.position.board.right ∧
      tu.position.board.left.relaxed = true ∧
      tu.position.board.left.bodyLabels = upper.position.board.left.bodyLabels ∧
      tu.position.board.left.currentLabel = D.upperView.upper ∧
      tu.position.board.left.leafIndex = D.lower.sup id ∧
      (∀ x ∈ st.position.board.right.coordinates,
        x ≤ st.position.board.left.coordinates.getLastD 0) ∧
      (∀ x ∈ su.position.board.right.coordinates,
        x ≤ su.position.board.left.coordinates.getLastD 0) ∧
      (∀ x ∈ tu.position.board.right.coordinates,
        x ≤ tu.position.board.left.coordinates.getLastD 0) := by
  have hJN := hJH.trans hHN
  have pathH {v w : Concrete.Hist N}
      (h : Relation.ReflTransGen ((exactGame N blue).FollowStep σ J b) v w) :
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) v w :=
    Relation.ReflTransGen.mono (fun _ _ hs => FiniteResponseGame.FollowStep.mono
      (exactGame N blue) hJH (fun _ => le_rfl) hs) _ _ h
  have hwinUpper := (hwin.of_reachable (exactGame N blue) hfromUpper).mono
    (exactGame N blue) hJH (fun _ => le_rfl)
  have htarget : LabeledWord.UpToLeaf (D.lower.sup id) upper.position.board.left :=
    ⟨(of_decide_eq_true hTrel).2.1, hTlabel ▸ D.last_upper,
      by simpa only [hTindex] using D.pivot_lt_last.le⟩
  obtain ⟨u, hUpperU, huBoard, hup⟩ := winning_next_leaf_request_after_other hJN hJ blue
    hwinUpper false htarget (by simpa only [Board.get, hTindex] using D.pivot_lt_last)
    (by simpa only [Board.get, Bool.not_false] using hUrel)
    (by simpa only [Board.get, Bool.not_false] using hUsep)
  let F := max u.position.bound (b u)
  let K := J \ Set.Iic (max B F)
  have hKJ : K ⊆ J := fun _ hx => hx.1
  have hK : K.Infinite := hJ.sdiff (Set.finite_Iic _)
  have hKfresh : ∀ x ∈ K, max B F < x := fun _ hx => lt_of_not_ge hx.2
  obtain ⟨v, hPv, hvp, hvl, hvr, hvno, hvroot, hvlabels, hvcurrent, _hvmarker,
      hvTlabels, hvTindex, hvbeta, hvnext, _hvupper, k, xs, hparse, hcanon,
      _hlen, hinc, hpool, bs, hrunT, hpoolT⟩ :=
    preliminary_first_phase hHN hJH hKJ hK blue origin old p L ha hop hboard hmode
      hwin hfromOld hOldP hOld hp hmP hrootP hotherP hBP
      (by simpa only [hOldLabel, hOldIndex] using D.pivot_lt_last) hrank hKfresh hall
  have hTendpoint : v.position.board.right.leafIndex = D.lower.sup id := by
    simpa only [hOldLabel] using hvTindex
  obtain ⟨tu, hUTU, htuP, htuShape, htuRel, htuLabels, htuCurrent, htuIndex,
      htuOther, htuSep⟩ := preliminary_upper_second hJN hKJ hJ blue old v u D
        (hwinUpper.of_reachable (exactGame N blue) hUpperU) hup
        (by simpa only [huBoard] using hTshape)
        (by simpa only [huBoard] using hTrel)
        (by simpa only [huBoard] using hTlabel)
        (by simpa only [huBoard] using hTindex)
        hOld.right_relaxed hvTlabels hTendpoint
        (by simpa only [huBoard] using hUrel)
        (by simpa only [huBoard] using hUpending) hrunT hpoolT
  have hvTroot := hrunT.rootLabel_eq (LabeledWord.relaxed_ne_start
    ((Position.history_dataInvariant old).2.1 true).1 hOld.right_relaxed)
  have hvTpending : Macro.Pending v.position.board.right := by
    obtain ⟨i, hi, hlt⟩ := hfutureT
    exact Or.inl ⟨i, hvTroot.symm ▸ hi, by simpa only [hvTlabels] using hlt⟩
  have hfromV := hfromOld.trans (hOldP.trans (pathH hPv))
  have hwinV := (hwin.of_reachable (exactGame N blue) hfromV).mono
    (exactGame N blue) hJH (fun _ => le_rfl)
  have hwinQ := (hwin.of_reachable (exactGame N blue) hfromQ).mono
    (exactGame N blue) hJH (fun _ => le_rfl)
  have hparseQ := hstem.parser_eq.symm.trans hparse
  obtain ⟨st, su, hVST, hQSU, hstP, hsuP, hSshape, hstRel, hsuRel, hstLabel,
      hsuLabel, hstBeta, hsuBeta, hstLabels, hsuLabels, hstOther, hsuOther,
      hstSep, hsuSep⟩ := preliminary_zero_upper hJN hKJ hK blue v q L hwinV hwinQ
        hvp hq hvl hvcurrent hvbeta hvnext hmQ hparseQ hBQ hvr hUQrel
        hvTpending hUQpending xs hinc (fun x hx => (hpool x hx).1)
        (hcanon.trans (hstem.bodyLeafCursor L.lower L.upper L.marker k xs))
  obtain ⟨as, hrunS, _hpoolS⟩ := follow_word_inputs_above_bound hVST false
  have hstRoot : st.position.board.left.rootLabel = p.position.board.left.rootLabel :=
    (hrunS.rootLabel_eq (LabeledWord.relaxed_ne_start
      ((Position.history_dataInvariant v).2.1 false).1 hvl)).trans hvroot
  obtain ⟨cs, hrunSU, _hpoolSU⟩ := follow_word_inputs_above_bound hQSU false
  have hsuRoot : su.position.board.left.rootLabel = q.position.board.left.rootLabel :=
    hrunSU.rootLabel_eq (by simp only [Board.get, hparseQ]; simp)
  have hstFull := hstLabels.trans hvlabels
  refine ⟨st, su, tu, hPv.trans hVST, hQSU, hUpperU.trans hUTU, hstP, hsuP, htuP,
    hSshape, ?_, ?_, hstRel, hsuRel, hstLabel, hsuLabel, hstBeta, hsuBeta,
    hstRoot, hsuRoot, hstFull, hsuLabels, ?_, ?_, ?_, ?_, ?_, ?_, hsuOther,
    ?_, htuRel, ?_, htuCurrent, htuIndex, hstSep, hsuSep, htuSep⟩
  · simpa only [hstOther] using htuShape.symm
  · simpa only [hsuOther, htuOther, huBoard] using hUshape
  · intro i hi
    simpa only [hstFull, List.length_append, List.length_singleton] using
      hrootP i (hstRoot ▸ hi)
  · intro i hi
    simpa only [hsuLabels, List.length_append, List.length_singleton] using
      hrootQ i (hsuRoot ▸ hi)
  · simpa only [hstOther] using hvr
  · simpa only [hstOther] using hvno
  · simpa only [hstOther] using hvTlabels
  · simpa only [hstOther] using hTendpoint
  · simpa only [huBoard] using htuOther
  · simpa only [huBoard] using htuLabels

#print axioms preliminary_rank_one_start

end Erdos591.Positive.Game.Payoff
