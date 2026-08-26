import ErdosProblems.Erdos591.AlignedPenultimateRequest
import ErdosProblems.Erdos591.PairedMarkerRequests

/-!
# The first shared last-body marker in the aligned upper bridge

Both waiting lower response bounds are imposed before any upper input.
Stop the upper play at its two penultimate endpoints, then replay the
first word's new prefix in the waiting lower play. The second word's
fresh prefix is retained for its later common last-marker response.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem aligned_upper_marker_bridge {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy} (origin old tu : Concrete.Hist N)
    {a i : ℕ} (ha : 0 < a)
    (hop : origin.position.pending = some ⟨false, .advance a⟩)
    (hboard : origin.position.board = Board.initial) (hmode : origin.position.mode = some true)
    (hwin : (exactGame N blue).ArchitectWins H b σ origin)
    (hfromOld : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin old)
    (hfromTU : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin tu)
    (hall : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin z →
      (exactGame N blue).kind z = .terminal w → alignedBodyCountColor z = true)
    (hpOld : old.position.pending = some ⟨true, .advance 0⟩)
    (hrelOld : old.position.board.right.relaxed = true)
    (hnoOld : old.position.board.right.NoLeafPending)
    (hbeforeOld : LabeledWord.BeforeBody i old.position.board.right)
    (hnextOld : ∀ k ∈ old.position.board.right.rootLabel,
      old.position.board.right.bodyLabels.length < k → i ≤ k)
    (hT : LabeledWord.SameStructure old.position.board.right tu.position.board.left)
    (hTlast : tu.position.board.left.lastSelectedBody = i)
    (hnTU : tu.position.pending = none) (hUrel : tu.position.board.right.relaxed = true)
    (hUbefore : tu.position.board.right.bodyLabels.length <
      tu.position.board.right.lastSelectedBody)
    (hTUsep : ∀ x ∈ tu.position.board.left.coordinates,
      x ≤ tu.position.board.right.coordinates.getLastD 0)
    (K : ℕ) (hK : max old.position.bound (b old) ≤ K) :
    ∃ J, J ⊆ H ∧ J.Infinite ∧ (∀ x ∈ J, K < x) ∧ ∃ st upper p r,
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) old st ∧
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ J b) tu upper ∧
      (exactGame N blue).ArchitectWins J b σ upper ∧
      st.position.pending = some ⟨true, .advance p⟩ ∧
      upper.position.pending = some ⟨false, .advance r⟩ ∧ 0 < p ∧ 0 < r ∧
      LabeledWord.SameStructure st.position.board.right upper.position.board.left ∧
      st.position.board.right.markerEvent = true ∧ upper.position.board.left.markerEvent = true ∧
      st.position.board.right.bodyLabels.length + 1 = i ∧
      upper.position.board.left.bodyLabels.length + 1 = i ∧
      st.position.board.right.rootLabel = old.position.board.right.rootLabel ∧
      upper.position.board.left.rootLabel = tu.position.board.left.rootLabel ∧
      st.position.board.left = old.position.board.left ∧
      upper.position.board.right.relaxed = true ∧ upper.position.board.right.NoLeafPending ∧
      upper.position.board.right.bodyLabels.length < upper.position.board.right.lastSelectedBody ∧
      (∀ k ∈ upper.position.board.right.rootLabel,
        k < upper.position.board.right.lastSelectedBody →
          k ≤ upper.position.board.right.bodyLabels.length) ∧
      ∃ frontU, LabeledWord.LegalRun tu.position.board.right frontU upper.position.board.right ∧
        ∀ atom ∈ frontU, atom.2 ∈ H ∧ K < atom.2 := by
  let J := H \ Set.Iic K
  have hJH : J ⊆ H := fun _ hx => hx.1
  have hJ : J.Infinite := hH.sdiff (Set.finite_Iic K)
  have hJfresh : ∀ x ∈ J, K < x := fun _ hx => lt_of_not_ge hx.2
  have pathH {u v : Concrete.Hist N}
      (hp : Relation.ReflTransGen ((exactGame N blue).FollowStep σ J b) u v) :
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) u v :=
    Relation.ReflTransGen.mono (fun _ _ hs =>
      FiniteResponseGame.FollowStep.mono (exactGame N blue) hJH (fun _ => le_rfl) hs) _ _ hp
  have hpos : 0 < tu.position.board.left.coordinates.length := by
    obtain ⟨as, has⟩ := History.word_run old true
    simpa only [← hT.coordinates_eq, Board.get] using has.relaxed_coordinates_pos hrelOld
  obtain ⟨v, hTUv, hpV, hVlrel, hVlno, hVlbefore, hVlpen, hVrrel, hVrno,
      hVrbefore, hVrpen, _hVsep⟩ := aligned_penultimate_request_on_subset
    hHN hH hJH hJ blue origin tu ha hop hboard hmode hwin hfromTU hall
      hnTU hUrel hpos hUbefore hTUsep
  have hwinV := (hwin.of_reachable (exactGame N blue) (hfromTU.trans (pathH hTUv))).mono
    (exactGame N blue) hJH (fun _ => le_rfl)
  obtain ⟨frontT, hfrontT, hpoolT⟩ := follow_word_inputs hTUv 0 (fun _ => Nat.zero_le _) false
  obtain ⟨frontU, hfrontU, hpoolU⟩ := follow_word_inputs hTUv 0 (fun _ => Nat.zero_le _) true
  have hstartOld := LabeledWord.relaxed_ne_start
    ((Position.history_dataInvariant old).2.1 true).1 hrelOld
  have hstartTU : tu.position.board.left.parser ≠ .start :=
    fun hs => hstartOld (hT.parser_eq.trans hs)
  have hVroot : v.position.board.left.rootLabel = tu.position.board.left.rootLabel :=
    hfrontT.rootLabel_eq hstartTU
  have hVlast : v.position.board.left.lastSelectedBody = i := by
    simpa only [LabeledWord.lastSelectedBody, hVroot] using hTlast
  have hVmem : i ∈ v.position.board.left.rootLabel := by
    rw [← hVlast]
    simpa [LabeledWord.lastSelectedBody] using Finset.sup_mem_of_nonempty (f := id)
      ⟨_, (of_decide_eq_true hVlrel).2.1⟩
  have hVbefore : LabeledWord.BeforeBody i v.position.board.left :=
    ⟨hVmem, by simpa only [hVlast] using hVlbefore⟩
  have hVnext : ∀ k ∈ v.position.board.left.rootLabel,
      v.position.board.left.bodyLabels.length < k → i ≤ k := by
    intro k hk hlt
    by_contra hn
    have hle := hVlpen k hk (by simpa only [hVlast] using lt_of_not_ge hn)
    omega
  obtain ⟨st, upper, p, r, hOldST, hVupper, hpST, hpUpper, hp, hr, hshape, hmST, hmUpper,
      hiST, hiUpper, hrootST, hrootUpper, hSTother, hUpperOther⟩ :=
    paired_next_marker_requests hHN hH hJH hJ blue old v
      (hwin.of_reachable (exactGame N blue) hfromOld) hwinV true false hpOld hpV hT
      hfrontT (fun atom hatom =>
        ⟨hJH (hpoolT atom hatom).1, hK.trans_lt (hJfresh atom.2 (hpoolT atom hatom).1)⟩)
      (fun x hx => hK.trans_lt (hJfresh x hx)) hrelOld hnoOld hbeforeOld hnextOld
      hVlrel hVlno hVbefore hVnext
  change upper.position.board.right = v.position.board.right at hUpperOther
  change upper.position.board.left.rootLabel = v.position.board.left.rootLabel at hrootUpper
  refine ⟨J, hJH, hJ, hJfresh, st, upper, p, r, hOldST, hTUv.trans hVupper,
    hwinV.of_reachable (exactGame N blue) hVupper, hpST, hpUpper, hp, hr, hshape,
    hmST, hmUpper, hiST, hiUpper, hrootST, hrootUpper.trans hVroot, hSTother,
    ?_, ?_, ?_, ?_, frontU, ?_, ?_⟩
  · simpa only [hUpperOther] using hVrrel
  · simpa only [hUpperOther] using hVrno
  · simpa only [hUpperOther] using hVrbefore
  · simpa only [hUpperOther] using hVrpen
  · simpa only [hUpperOther, Board.get] using hfrontU
  · intro atom hatom
    exact ⟨hJH (hpoolU atom hatom).1, hJfresh atom.2 (hpoolU atom hatom).1⟩

#print axioms aligned_upper_marker_bridge

end Erdos591.Positive.Game.Payoff
