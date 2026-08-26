import ErdosProblems.Erdos591.PreliminaryFirstPhase
import ErdosProblems.Erdos591.PreliminaryUpperSecond
import ErdosProblems.Erdos591.PreliminarySecondPhase
import ErdosProblems.Erdos591.PreliminarySharedBeta

/-!
# Both preliminary lower phases and the shared beta in three actual plays

The upper T reply is submitted between the two lower phases. Its
issued U request fixes the bound on the whole second-phase U prefix.
That prefix is retained, not yet identified with the upper U word:
it belongs either to its next-leaf reply or a delayed next-body reply.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem preliminary_nonempty_start {N H J HD : Set ℕ}
    (hHN : H ⊆ N) (hJH : J ⊆ H) (hJ : J.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    (origin oldT oldU p q upper : Concrete.Hist N) {a B P Q r t BT n c s : ℕ}
    (L : PreliminaryPivotLabels J B P Q r t) (D : CriticalLeafLabels HD BT n c s)
    (ha : 2 ≤ a) (hop : origin.position.pending = some ⟨false, .advance a⟩)
    (hboard : origin.position.board = Board.initial) (hmode : origin.position.mode = some true)
    (hwin : (exactGame N blue).ArchitectWins H b σ origin)
    (hfromOldT : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin oldT)
    (hfromOldU : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin oldU)
    (hOldTP : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) oldT p)
    (hOldUQ : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) oldU q)
    (hfromUpper : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin upper)
    (hOldT : CriticalCheckpoint oldT) (hOldU : CriticalCheckpoint oldU)
    (hp : p.position.pending = some ⟨false, .advance P⟩)
    (hq : q.position.pending = some ⟨false, .advance Q⟩)
    (hstem : LabeledWord.SameStructure p.position.board.left q.position.board.left)
    (hmP : p.position.board.left.markerEvent = true)
    (hmQ : q.position.board.left.markerEvent = true)
    (hrootP : ∀ i ∈ p.position.board.left.rootLabel,
      i ≤ p.position.board.left.bodyLabels.length + 1)
    (hrootQ : ∀ i ∈ q.position.board.left.rootLabel,
      i ≤ q.position.board.left.bodyLabels.length + 1)
    (hotherP : p.position.board.right = oldT.position.board.right)
    (hotherQ : q.position.board.right = oldU.position.board.right)
    (hBP : max p.position.bound (b p) ≤ B) (hBQ : max q.position.bound (b q) ≤ B)
    (hOldLabel : oldT.position.board.right.currentLabel = D.lower)
    (hOldIndex : oldT.position.board.right.leafIndex = D.upperView.pivot)
    (hrankT : oldT.position.board.right.currentLabel.card -
      (oldT.position.board.right.currentLabel.filter
        (fun x => x ≤ oldT.position.board.right.leafIndex)).card = r)
    (hrankU : oldU.position.board.right.currentLabel.card -
      (oldU.position.board.right.currentLabel.filter
        (fun x => x ≤ oldU.position.board.right.leafIndex)).card = t)
    (hUlt : oldU.position.board.right.leafIndex < oldU.position.board.right.currentLabel.sup id)
    (hfutureT : ∃ i ∈ oldT.position.board.right.rootLabel,
      oldT.position.board.right.bodyLabels.length < i)
    (hfutureU : ∃ i ∈ oldU.position.board.right.rootLabel,
      oldU.position.board.right.bodyLabels.length < i)
    (hTshape : LabeledWord.SameStructure upper.position.board.left oldT.position.board.right)
    (hTrel : upper.position.board.left.relaxed = true)
    (hTlabel : upper.position.board.left.currentLabel = D.upperView.upper)
    (hTindex : upper.position.board.left.leafIndex = D.upperView.pivot)
    (hUrel : upper.position.board.right.relaxed = true)
    (hUpending : Macro.Pending upper.position.board.right)
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
      st.position.board.right.relaxed = true ∧ su.position.board.right.relaxed = true ∧
      st.position.board.right.NoLeafPending ∧ su.position.board.right.NoLeafPending ∧
      st.position.board.right.rootLabel = oldT.position.board.right.rootLabel ∧
      su.position.board.right.rootLabel = oldU.position.board.right.rootLabel ∧
      st.position.board.right.bodyLabels = oldT.position.board.right.bodyLabels ∧
      su.position.board.right.bodyLabels = oldU.position.board.right.bodyLabels ∧
      st.position.board.right.leafIndex = D.lower.sup id ∧
      su.position.board.right.leafIndex = oldU.position.board.right.currentLabel.sup id ∧
      tu.position.board.right = upper.position.board.right ∧
      tu.position.board.left.relaxed = true ∧
      tu.position.board.left.bodyLabels = upper.position.board.left.bodyLabels ∧
      tu.position.board.left.currentLabel = D.upperView.upper ∧
      tu.position.board.left.leafIndex = D.lower.sup id ∧
      (∀ x ∈ st.position.board.right.coordinates,
        x ≤ st.position.board.left.coordinates.getLastD 0) ∧
      (∀ x ∈ su.position.board.right.coordinates,
        x ≤ su.position.board.left.coordinates.getLastD 0) ∧
      ∃ bs, LabeledWord.LegalRun oldU.position.board.right bs su.position.board.right ∧
        ∀ atom ∈ bs, atom.2 ∈ J ∧ max tu.position.bound (b tu) < atom.2 := by
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
      hvTlabels, hvTindex, hvbeta, hvnext, hvupper, k, xs, hparse, hcanon,
      hlen, hinc, hpool, bsT, hrunT, hpoolT⟩ :=
    preliminary_first_phase hHN hJH hKJ hK blue origin oldT p L ha hop hboard hmode
      hwin hfromOldT hOldTP hOldT hp hmP hrootP hotherP hBP
      (by simpa only [hOldLabel, hOldIndex] using D.pivot_lt_last) hrankT hKfresh hall
  have hTendpoint : v.position.board.right.leafIndex = D.lower.sup id := by
    simpa only [hOldLabel] using hvTindex
  obtain ⟨tu, hUTU, htuP, htuShape, htuRel, htuLabels, htuCurrent, htuIndex,
      htuOther, _htuSep⟩ := preliminary_upper_second hJN hKJ hJ blue oldT v u D
        (hwinUpper.of_reachable (exactGame N blue) hUpperU) hup
        (by simpa only [huBoard] using hTshape)
        (by simpa only [huBoard] using hTrel)
        (by simpa only [huBoard] using hTlabel)
        (by simpa only [huBoard] using hTindex)
        hOldT.right_relaxed hvTlabels hTendpoint
        (by simpa only [huBoard] using hUrel)
        (by simpa only [huBoard] using hUpending) hrunT hpoolT
  let C := max (max v.position.bound (b v)) (max tu.position.bound (b tu))
  let M := J \ Set.Iic C
  have hMJ : M ⊆ J := fun _ hx => hx.1
  have hM : M.Infinite := hJ.sdiff (Set.finite_Iic _)
  have hMfresh : ∀ x ∈ M, C < x := fun _ hx => lt_of_not_ge hx.2
  have hparseQ := hstem.parser_eq.symm.trans hparse
  have hbefore : xs.length < L.upper.min' ⟨_, L.beta_upper⟩ := by
    rw [hlen]
    exact hvupper _ (Finset.min'_mem _ _)
  obtain ⟨w, hQW, hwp, hwl, hwr, hwno, hwroot, hwlabels, hwcurrent, hwmarker,
      hwUlabels, hwUindex, hwbeta, hwnext, _hwsep, as, bsU, hrunS, hrunU, hpoolS, hpoolU⟩ :=
    preliminary_second_phase hHN hJH hMJ hM blue origin oldU q L ha hop hboard hmode
      hwin hfromOldU hOldUQ hOldU hq hmQ hrootQ hotherQ hBQ hUlt hrankU hMfresh hall
      xs hparseQ hinc (fun x hx => (hpool x hx).1) hbefore
  have hvTroot := hrunT.rootLabel_eq (LabeledWord.relaxed_ne_start
    ((Position.history_dataInvariant oldT).2.1 true).1 hOldT.right_relaxed)
  have hwUroot := hrunU.rootLabel_eq (LabeledWord.relaxed_ne_start
    ((Position.history_dataInvariant oldU).2.1 true).1 hOldU.right_relaxed)
  have hvTpending : Macro.Pending v.position.board.right := by
    obtain ⟨i, hi, hlt⟩ := hfutureT
    exact Or.inl ⟨i, hvTroot.symm ▸ hi, by simpa only [hvTlabels] using hlt⟩
  have hwUpending : Macro.Pending w.position.board.right := by
    obtain ⟨i, hi, hlt⟩ := hfutureU
    exact Or.inl ⟨i, hwUroot.symm ▸ hi, by simpa only [hwUlabels] using hlt⟩
  have hwinV := (hwin.of_reachable (exactGame N blue)
    (hfromOldT.trans (hOldTP.trans (pathH hPv)))).mono
      (exactGame N blue) hJH (fun _ => le_rfl)
  have hwinW := (hwin.of_reachable (exactGame N blue)
    (hfromOldU.trans (hOldUQ.trans (pathH hQW)))).mono
      (exactGame N blue) hJH (fun _ => le_rfl)
  obtain ⟨st, su, hVST, hWSU, hstP, hsuP, hSshape, hstRel, hsuRel, hstLabel,
      hsuLabel, hstBeta, hsuBeta, hstLabels, hsuLabels, hstOther, hsuOther,
      hstSep, hsuSep⟩ := preliminary_shared_beta hJN hJ blue v w L hwinV hwinW hvp hwp
        hvl hwl hvcurrent hwcurrent hvbeta hwbeta hvnext hwnext hvr hwr hvTpending hwUpending
        (hcanon.trans (hstem.bodyLeafCursor L.lower L.upper L.marker k xs)) hrunS
        (fun atom ha => ⟨hMJ (hpoolS atom ha).1,
          (le_max_left _ _).trans_lt (hpoolS atom ha).2⟩)
        (by simp only [hwlabels, LabeledWord.bodyLeafCursor]) hwmarker
  obtain ⟨asST, hrunST, _hpoolST⟩ := follow_word_inputs_above_bound hVST false
  have hstRoot : st.position.board.left.rootLabel = p.position.board.left.rootLabel :=
    (hrunST.rootLabel_eq (LabeledWord.relaxed_ne_start
      ((Position.history_dataInvariant v).2.1 false).1 hvl)).trans hvroot
  obtain ⟨asSU, hrunSU, _hpoolSU⟩ := follow_word_inputs_above_bound hWSU false
  have hsuRoot : su.position.board.left.rootLabel = q.position.board.left.rootLabel :=
    (hrunSU.rootLabel_eq (LabeledWord.relaxed_ne_start
      ((Position.history_dataInvariant w).2.1 false).1 hwl)).trans hwroot
  have hstFull := hstLabels.trans hvlabels
  have hsuFull := hsuLabels.trans hwlabels
  refine ⟨st, su, tu, hPv.trans hVST, hQW.trans hWSU, hUpperU.trans hUTU,
    hstP, hsuP, htuP, hSshape, ?_, hstRel, hsuRel, hstLabel, hsuLabel, hstBeta, hsuBeta,
    hstRoot, hsuRoot, hstFull, hsuFull, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, htuRel, ?_, htuCurrent, htuIndex, hstSep, hsuSep, bsU, ?_, ?_⟩
  · simpa only [hstOther] using htuShape.symm
  · intro i hi
    simpa only [hstFull, List.length_append, List.length_singleton] using
      hrootP i (hstRoot ▸ hi)
  · intro i hi
    simpa only [hsuFull, List.length_append, List.length_singleton] using
      hrootQ i (hsuRoot ▸ hi)
  · simpa only [hstOther] using hvr
  · simpa only [hsuOther] using hwr
  · simpa only [hstOther] using hvno
  · simpa only [hsuOther] using hwno
  · simpa only [hstOther] using hvTroot
  · simpa only [hsuOther] using hwUroot
  · simpa only [hstOther] using hvTlabels
  · simpa only [hsuOther] using hwUlabels
  · simpa only [hstOther] using hTendpoint
  · simpa only [hsuOther] using hwUindex
  · simpa only [huBoard] using htuOther
  · simpa only [huBoard] using htuLabels
  · simpa only [hsuOther] using hrunU
  · intro atom ha
    exact ⟨hMJ (hpoolU atom ha).1, (le_max_right _ _).trans_lt (hpoolU atom ha).2⟩

#print axioms preliminary_nonempty_start

end Erdos591.Positive.Game.Payoff
