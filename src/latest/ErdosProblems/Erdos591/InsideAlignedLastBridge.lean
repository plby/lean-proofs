import ErdosProblems.Erdos591.InsideAlignedSecondFirst
import ErdosProblems.Erdos591.AlignedUpperMarkerBridge
import ErdosProblems.Erdos591.AlignedPendingLastSize
import ErdosProblems.Erdos591.SharedFirstThenMarker
import ErdosProblems.Erdos591.AlignedRootLabels

/-!
# The complete aligned bridge from the first lower last-body leaves

Keep both waiting bounds before moving the upper play. Its two marker
requests and both pairs of first leaves are genuine reachable histories.
The aligned count identity supplies all three size equations, and the
uniform right-last-body singleton test supplies the common alternative.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem inside_aligned_last_bridge_triangle {N H I : Set ℕ}
    (hHN : H ⊆ N) (hH : H.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    (origin st su tu : Concrete.Hist N) {a B C E p q e c f : ℕ}
    (S : FirstLastLabels H B p q) (T : AlignedRootLabels H C e a)
    (U : AlignedRootLabels I E f c) (ha : 2 ≤ a)
    (hop : origin.position.pending = some ⟨false, .advance a⟩)
    (hboard : origin.position.board = Board.initial) (hmode : origin.position.mode = some true)
    (hwin : (exactGame N blue).ArchitectWins H b σ origin)
    (hfromST : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin st)
    (hfromSU : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin su)
    (hfromTU : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin tu)
    (hall : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin z →
      (exactGame N blue).kind z = .terminal w → alignedBodyCountColor z = true)
    (hlarge : ∀ v d, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin v →
      v.position.pending = some ⟨false, .advance d⟩ → v.position.board.left.markerEvent = true →
      (∀ k ∈ v.position.board.left.rootLabel,
        k ≤ v.position.board.left.bodyLabels.length + 1) → 2 ≤ d)
    (value : Bool)
    (hone : ∀ v d, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin v →
      v.position.pending = some ⟨true, .advance d⟩ → v.position.board.right.markerEvent = true →
      (∀ k ∈ v.position.board.right.rootLabel,
        k ≤ v.position.board.right.bodyLabels.length + 1) → decide (d = 1) = value)
    (hpST : st.position.pending = some ⟨true, .advance 0⟩)
    (hpSU : su.position.pending = some ⟨true, .advance 0⟩) (hnTU : tu.position.pending = none)
    (hS : LabeledWord.SameStructure st.position.board.left su.position.board.left)
    (hrST : st.position.board.left.relaxed = true) (hrSU : su.position.board.left.relaxed = true)
    (hlST : st.position.board.left.currentLabel = S.lower)
    (hlSU : su.position.board.left.currentLabel = S.upper)
    (hiST : st.position.board.left.leafIndex = S.first)
    (hiSU : su.position.board.left.leafIndex = S.first)
    (hrootST : ∀ i ∈ st.position.board.left.rootLabel, i ≤ st.position.board.left.bodyLabels.length)
    (hrootSU : ∀ i ∈ su.position.board.left.rootLabel, i ≤ su.position.board.left.bodyLabels.length)
    (hrT : st.position.board.right.relaxed = true) (hnoT : st.position.board.right.NoLeafPending)
    (hrootT : st.position.board.right.rootLabel = T.lower)
    (hbodyT : st.position.board.right.bodyLabels.length = T.shared)
    (hrU : su.position.board.right.relaxed = true) (hnoU : su.position.board.right.NoLeafPending)
    (hrootU : su.position.board.right.rootLabel = U.lower)
    (hbodyU : su.position.board.right.bodyLabels.length = U.shared)
    (hT : LabeledWord.SameStructure st.position.board.right tu.position.board.left)
    (hU : LabeledWord.SameStructure su.position.board.right tu.position.board.right)
    (hrootTV : tu.position.board.left.rootLabel = T.upper)
    (hrootUV : tu.position.board.right.rootLabel = U.upper)
    (hrUV : tu.position.board.right.relaxed = true)
    (hsep : ∀ x ∈ tu.position.board.left.coordinates,
      x ≤ tu.position.board.right.coordinates.getLastD 0) :
    ¬ blue.CliqueFree 3 := by
  have hbeforeT : LabeledWord.BeforeBody T.last st.position.board.right :=
    ⟨hrootT ▸ T.last_lower, by rw [hbodyT]; exact T.shared_lt_last⟩
  have hnextT : ∀ i ∈ st.position.board.right.rootLabel,
      st.position.board.right.bodyLabels.length < i → T.last ≤ i := by
    intro i hi hlt
    rw [hbodyT] at hlt
    exact (T.lower_bounds i (hrootT ▸ hi)).elim Eq.ge (fun h => (not_lt_of_ge h hlt).elim)
  have hbeforeU : LabeledWord.BeforeBody U.last su.position.board.right :=
    ⟨hrootU ▸ U.last_lower, by rw [hbodyU]; exact U.shared_lt_last⟩
  have hnextU : ∀ i ∈ su.position.board.right.rootLabel,
      su.position.board.right.bodyLabels.length < i → U.last ≤ i := by
    intro i hi hlt
    rw [hbodyU] at hlt
    exact (U.lower_bounds i (hrootU ▸ hi)).elim Eq.ge (fun h => (not_lt_of_ge h hlt).elim)
  have hlastTV : tu.position.board.left.lastSelectedBody = T.last := by
    rw [LabeledWord.lastSelectedBody, hrootTV, T.upper_sup]
  have hlastUV : tu.position.board.right.lastSelectedBody = U.last := by
    rw [LabeledWord.lastSelectedBody, hrootUV, U.upper_sup]
  have hbeforeUV : tu.position.board.right.bodyLabels.length <
      tu.position.board.right.lastSelectedBody := by
    rw [← hU.body_length, hbodyU, hlastUV]
    exact U.shared_lt_last
  let K := max (max st.position.bound (b st)) (max su.position.bound (b su))
  obtain ⟨J, hJH, hJ, hJfresh, v, upper, t, r, hSTv, hTUupper, _hwinUpperJ,
      hpV, hpUpper, ht, _hr, hTmarker, hmV, hmUpper, hiV, hiUpper,
      hrootV, hrootUpper, hSfixed, hrUpperU, hnoUpperU, hbeforeUpperU, hpenUpperU,
      frontU, hfrontU, hpoolU⟩ :=
    aligned_upper_marker_bridge hHN hH blue origin st tu (by omega) hop hboard hmode hwin
      hfromST hfromTU hall hpST hrT hnoT hbeforeT hnextT hT hlastTV hnTU hrUV hbeforeUV
      hsep K (le_max_left _ _)
  have hTUupperH : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) tu upper :=
    Relation.ReflTransGen.mono (fun _ _ hs =>
      FiniteResponseGame.FollowStep.mono (exactGame N blue) hJH (fun _ => le_rfl) hs) _ _ hTUupper
  have hfromV := hfromST.trans hSTv
  have hfromUpper := hfromTU.trans hTUupperH
  have hboundV : ∀ i ∈ v.position.board.right.rootLabel,
      i ≤ v.position.board.right.bodyLabels.length + 1 := by
    rw [hiV, hrootV, hrootT]
    exact T.lower_le_last
  have hboundUpper : ∀ i ∈ upper.position.board.left.rootLabel,
      i ≤ upper.position.board.left.bodyLabels.length + 1 := by
    rw [hiUpper, hrootUpper, hrootTV]
    exact fun i hi => (T.upper_bounds i hi).2
  have hrLarge := hlarge upper r hfromUpper hpUpper hmUpper hboundUpper
  have hpSize : p = t + 1 := by
    have hsize := aligned_pending_right_last_size hHN hH blue origin v ha hop hboard hmode
      hwin hfromV hall hpV hmV hboundV
      (by simpa only [hSfixed] using hrST) (by simpa only [hSfixed] using hrootST)
    simpa only [hSfixed, hlST, S.lower_card] using hsize
  have hrootUpperU : upper.position.board.right.rootLabel = U.upper :=
    (hfrontU.rootLabel_eq (LabeledWord.relaxed_ne_start
      ((Position.history_dataInvariant tu).2.1 true).1 hrUV)).trans hrootUV
  have hlastUpperU : upper.position.board.right.lastSelectedBody = U.last := by
    rw [LabeledWord.lastSelectedBody, hrootUpperU, U.upper_sup]
  have hbeforeUpper : LabeledWord.BeforeBody U.last upper.position.board.right :=
    ⟨hrootUpperU ▸ U.last_upper, by simpa only [hlastUpperU] using hbeforeUpperU⟩
  have hnextUpper : ∀ i ∈ upper.position.board.right.rootLabel,
      upper.position.board.right.bodyLabels.length < i → U.last ≤ i := by
    intro i hi hlt
    by_contra hn
    have hle := hpenUpperU i hi (by simpa only [hlastUpperU] using lt_of_not_ge hn)
    exact not_lt_of_ge hle hlt
  let D := max (max v.position.bound (b v)) (max upper.position.bound (b upper))
  obtain ⟨TL, TV, hTfirst, hTmarkerEq, hTchoice⟩ :=
    first_second_label_choice hH D t r ht (by omega) (fun _ => hrLarge)
  have hSstrict : v.position.board.left.leafIndex < S.last := by
    rw [hSfixed, hiST]
    exact S.first_lt_last
  have hSup : LabeledWord.UpToLeaf S.last v.position.board.left :=
    ⟨by simpa only [hSfixed] using (of_decide_eq_true hrST).2.1,
      by simpa only [hSfixed, hlST] using S.last_lower, hSstrict.le⟩
  obtain ⟨st₁, su₁, tu₁, d, g, hvST, hsuSU, huTU, hpST₁, hpSU₁, hpTU₁, hd, hg,
      hTshape, hrSTt, hrTUt, hlSTt, hlTUt, hiSTt, hiTUt, hrootSTt, hrootTUt,
      hSTs, hSUs, hUshape, hmSU, hmTU, hiSU₁, hiTU₁, hrootSU₁, hrootTU₁⟩ :=
    shared_first_then_marker hHN hH hJH hJ blue v upper su TL TV hTfirst hTmarkerEq
      (hwin.of_reachable (exactGame N blue) hfromV)
      (hwin.of_reachable (exactGame N blue) hfromUpper)
      (hwin.of_reachable (exactGame N blue) hfromSU) hpV hpUpper hmV hmUpper hTmarker
      hboundV hboundUpper hSup hSstrict hrUpperU hnoUpperU hbeforeUpper hnextUpper
      (le_max_left _ _) (le_max_right _ _) hpSU hrU hnoU hbeforeU hnextU hU hfrontU
      (fun atom hatom => ⟨(hpoolU atom hatom).1,
        (le_max_right _ _).trans_lt (hpoolU atom hatom).2⟩)
      (fun x hx => (le_max_right _ _).trans_lt (hJfresh x hx))
  have hfromST₁ := hfromV.trans hvST
  have hfromSU₁ := hfromSU.trans hsuSU
  have hfromTU₁ := hfromUpper.trans huTU
  have hSTs' := hSTs.trans hSfixed
  have hboundSU : ∀ i ∈ su₁.position.board.right.rootLabel,
      i ≤ su₁.position.board.right.bodyLabels.length + 1 := by
    rw [hiSU₁, hrootSU₁, hrootU]
    exact U.lower_le_last
  have hboundTU : ∀ i ∈ tu₁.position.board.right.rootLabel,
      i ≤ tu₁.position.board.right.bodyLabels.length + 1 := by
    rw [hiTU₁, hrootTU₁, hrootUpperU]
    exact fun i hi => (U.upper_bounds i hi).2
  have hqSize : q = d + 1 := by
    have hsize := aligned_pending_right_last_size hHN hH blue origin su₁ ha hop hboard hmode
      hwin hfromSU₁ hall hpSU₁ hmSU hboundSU
      (by simpa only [hSUs] using hrSU) (by simpa only [hSUs] using hrootSU)
    simpa only [hSUs, hlSU, S.upper_card] using hsize
  have hrSize : r = g + 1 := by
    have hsize := aligned_pending_right_last_size hHN hH blue origin tu₁ ha hop hboard hmode
      hwin hfromTU₁ hall hpTU₁ hmTU hboundTU hrTUt hrootTUt
    simpa only [hlTUt, TV.upper_card] using hsize
  have hOneT := hone v t hfromV hpV hmV hboundV
  have hOneD := hone su₁ d hfromSU₁ hpSU₁ hmSU hboundSU
  have hOneG := hone tu₁ g hfromTU₁ hpTU₁ hmTU hboundTU
  have hTD : t = 1 ↔ d = 1 := by
    simpa only [decide_eq_decide] using hOneT.trans hOneD.symm
  have hDG : d = 1 ↔ g = 1 := by
    simpa only [decide_eq_decide] using hOneD.trans hOneG.symm
  exact inside_aligned_second_first_triangle hHN hH blue st₁ su₁ tu₁ S TL TV
    hTfirst hTchoice hpSize hqSize hrSize hd hg hTD hDG
    (hwin.of_reachable (exactGame N blue) hfromST₁)
    (hwin.of_reachable (exactGame N blue) hfromSU₁)
    (hwin.of_reachable (exactGame N blue) hfromTU₁)
    (follow_mode_some hfromST₁ hmode) (follow_mode_some hfromSU₁ hmode) hpST₁ hpSU₁ hpTU₁
    (by simpa only [hSTs', hSUs] using hS)
    (by simpa only [hSTs'] using hrST) (by simpa only [hSUs] using hrSU)
    (by simpa only [hSTs'] using hlST) (by simpa only [hSUs] using hlSU)
    (by simpa only [hSTs'] using hiST) (by simpa only [hSUs] using hiSU)
    (by simpa only [hSTs'] using hrootST) (by simpa only [hSUs] using hrootSU)
    hTshape hrSTt hrTUt hlSTt hlTUt hiSTt hiTUt hrootSTt hUshape hmSU hmTU hboundSU

#print axioms inside_aligned_last_bridge_triangle

end Erdos591.Positive.Game.Payoff
