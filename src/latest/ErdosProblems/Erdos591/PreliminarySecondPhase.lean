import ErdosProblems.Erdos591.DeferredBodyFirst
import ErdosProblems.Erdos591.PreliminaryUpperRun
import ErdosProblems.Erdos591.FreshLeafNextMarker

/-!
# The second actual preliminary phase after the retained first-phase S prefix

Complete the saved upper S-body response with fresh coordinates, then
exhaust the old critical U body. Leave its S response toward beta
pending. The combined new S tail can be replayed from the other play's
old structural prefix, and every new U input meets the recorded bound.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem preliminary_second_phase {N H J K : Set ℕ}
    (hHN : H ⊆ N) (hJH : J ⊆ H) (hKJ : K ⊆ J) (hK : K.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy} (origin old p : Concrete.Hist N)
    {a B P Q r t C k : ℕ} (L : PreliminaryPivotLabels J B P Q r t) (ha : 2 ≤ a)
    (hop : origin.position.pending = some ⟨false, .advance a⟩)
    (hboard : origin.position.board = Board.initial) (hmode : origin.position.mode = some true)
    (hwin : (exactGame N blue).ArchitectWins H b σ origin)
    (hfrom : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin old)
    (holdp : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) old p)
    (hOld : CriticalCheckpoint old)
    (hp : p.position.pending = some ⟨false, .advance Q⟩)
    (hm : p.position.board.left.markerEvent = true)
    (hSroot : ∀ i ∈ p.position.board.left.rootLabel,
      i ≤ p.position.board.left.bodyLabels.length + 1)
    (hother : p.position.board.right = old.position.board.right)
    (hB : max p.position.bound (b p) ≤ B)
    (hUlt : old.position.board.right.leafIndex < old.position.board.right.currentLabel.sup id)
    (hrank : old.position.board.right.currentLabel.card -
      (old.position.board.right.currentLabel.filter
        (fun x => x ≤ old.position.board.right.leafIndex)).card = t)
    (hfresh : ∀ x ∈ K, C < x)
    (hall : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin z →
      (exactGame N blue).kind z = .terminal w →
        z.position.board.left.beforeLastLeafCount < z.position.board.right.beforeLastLeafCount)
    (xs : List ℕ) (hparse : p.position.board.left.parser = .blocks (k + 1))
    (hinc : (L.marker :: xs).Pairwise (· < ·)) (hpool : ∀ x ∈ xs, x ∈ J)
    (hbefore : xs.length < L.upper.min' ⟨_, L.beta_upper⟩) :
    ∃ q, Relation.ReflTransGen ((exactGame N blue).FollowStep σ J b) p q ∧
      q.position.pending = some ⟨false, .advance 0⟩ ∧
      q.position.board.left.relaxed = true ∧ q.position.board.right.relaxed = true ∧
      q.position.board.right.NoLeafPending ∧
      q.position.board.left.rootLabel = p.position.board.left.rootLabel ∧
      q.position.board.left.bodyLabels = p.position.board.left.bodyLabels ++ [L.upper] ∧
      q.position.board.left.currentLabel = L.upper ∧ q.position.board.left.bodyMarker = L.marker ∧
      q.position.board.right.bodyLabels = old.position.board.right.bodyLabels ∧
      q.position.board.right.leafIndex = old.position.board.right.currentLabel.sup id ∧
      q.position.board.left.leafIndex < L.beta ∧
      (∀ x ∈ L.upper, q.position.board.left.leafIndex < x → L.beta ≤ x) ∧
      (∀ x ∈ q.position.board.left.coordinates,
        x ≤ q.position.board.right.coordinates.getLastD 0) ∧
      ∃ as bs, LabeledWord.LegalRun
        (LabeledWord.bodyLeafCursor p.position.board.left L.upper L.marker k xs)
          as q.position.board.left ∧
        LabeledWord.LegalRun old.position.board.right bs q.position.board.right ∧
        (∀ atom ∈ as, atom.2 ∈ K ∧ C < atom.2) ∧
        (∀ atom ∈ bs, atom.2 ∈ K ∧ C < atom.2) := by
  have hKH := hKJ.trans hJH
  have pathJ {u v : Concrete.Hist N}
      (hpath : Relation.ReflTransGen ((exactGame N blue).FollowStep σ K b) u v) :
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ J b) u v :=
    Relation.ReflTransGen.mono (fun _ _ hs => FiniteResponseGame.FollowStep.mono
      (exactGame N blue) hKJ (fun _ => le_rfl) hs) _ _ hpath
  have pathH {u v : Concrete.Hist N}
      (hpath : Relation.ReflTransGen ((exactGame N blue).FollowStep σ J b) u v) :
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) u v :=
    Relation.ReflTransGen.mono (fun _ _ hs => FiniteResponseGame.FollowStep.mono
      (exactGame N blue) hJH (fun _ => le_rfl) hs) _ _ hpath
  obtain ⟨first, ys, hpFirst, _hFirstNone, hFirstRel, hFirstRoot, hFirstLabels, hFirstCurrent,
      _hFirstIndex, hFirstMarker, hFirstOther, _hFirstSep, _hword, hFirstTail,
      _hlen, _hfullInc, hys⟩ := deferred_body_first_from_prefix (hJH.trans hHN) hKJ hK
        blue σ p false L.upper ⟨_, L.beta_upper⟩ L.upper_card L.upper_fresh L.marker_fresh
        hp hm hparse hB xs hinc hpool hbefore C
  simp only [Board.get] at hFirstRel hFirstRoot hFirstLabels hFirstCurrent hFirstMarker hFirstTail
  simp only [Board.get, Bool.not_false] at hFirstOther
  have hFirstU : first.position.board.right = old.position.board.right :=
    hFirstOther.trans hother
  have hFirstLast : ∀ i ∈ first.position.board.left.rootLabel,
      i ≤ first.position.board.left.bodyLabels.length := by
    intro i hi
    simpa only [hFirstLabels, List.length_append, List.length_singleton] using
      hSroot i (hFirstRoot ▸ hi)
  obtain ⟨v, hFirstV, _hvn, hvl, hvr, hvno, hvLabels, hvMarker, hvCurrent, hvUlabels,
      _hvUmarker, hvUindex, _hvRank, hvBeta, hvNext, hvSep, as, bs, has, hbs,
      hpoolS, hpoolU⟩ := preliminary_upper_run hHN hKH hK blue origin old first L ha
        hop hboard hmode hwin hfrom (holdp.trans (pathH (.single hpFirst))) hOld
        hFirstRel (by simpa only [hFirstU] using hOld.right_relaxed) hFirstLast hFirstCurrent
        (by rw [hFirstU]) (by simpa only [hFirstU] using hUlt) hrank hfresh hall
  have hpv := (Relation.ReflTransGen.single hpFirst).trans (pathJ hFirstV)
  have hwinV := (hwin.of_reachable (exactGame N blue)
    (hfrom.trans (holdp.trans (pathH hpv)))).mono (exactGame N blue) hKH (fun _ => le_rfl)
  have hpending : Macro.Pending v.position.board.left :=
    Or.inr ⟨(of_decide_eq_true hvl).2.1, L.beta, hvCurrent ▸ L.beta_upper, hvBeta⟩
  obtain ⟨q, hvq, hqBoard, hqp⟩ := winning_next_selection_after_fresh_leaf
    (hKH.trans hHN) hK blue hwinV true hvr hvSep hvl hpending
  have hrootV : v.position.board.left.rootLabel = p.position.board.left.rootLabel :=
    (has.rootLabel_eq (LabeledWord.relaxed_ne_start
      ((Position.history_dataInvariant first).2.1 false).1 hFirstRel)).trans hFirstRoot
  refine ⟨q, hpv.trans (pathJ hvq), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ys.map (fun y => (∅, y)) ++ as, bs, ?_, ?_, ?_, hpoolU⟩
  · simpa only [Bool.not_true] using hqp
  · simpa only [hqBoard] using hvl
  · simpa only [hqBoard] using hvr
  · simpa only [hqBoard] using hvno
  · simpa only [hqBoard] using hrootV
  · simpa only [hqBoard] using hvLabels.trans hFirstLabels
  · simpa only [hqBoard] using hvCurrent
  · simpa only [hqBoard] using hvMarker.trans hFirstMarker
  · simpa only [hqBoard] using hvUlabels
  · simpa only [hqBoard, hFirstU] using hvUindex
  · simpa only [hqBoard] using hvBeta
  · simpa only [hqBoard] using hvNext
  · simpa only [hqBoard] using hvSep
  · simpa only [hqBoard] using hFirstTail.append has
  · simpa only [hqBoard, hFirstU] using hbs
  · intro atom ha
    rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp ha
      exact hys y hy
    · exact hpoolS atom ha

#print axioms preliminary_second_phase

end Erdos591.Positive.Game.Payoff
