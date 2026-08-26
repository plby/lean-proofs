import ErdosProblems.Erdos118.Reused591.PrescribedBodyOpening
import ErdosProblems.Erdos118.Reused591.PreliminaryLowerRun
import ErdosProblems.Erdos118.Reused591.BodyPrefixExtension
import ErdosProblems.Erdos118.Reused591.FreshLeafNextMarker

namespace Erdos118.Reused591

/-!
# The first actual preliminary phase, including its issued S-body reply

Read the prescribed lower S label on its original pool, then use a
smaller future pool for all remaining coordinates. Stop when the old
critical T body is exhausted and leave S's beta response pending.
The full canonical S prefix is before every upper S selection; the T
prefix is ready for the already recorded upper second-leaf reply.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem preliminary_first_phase {N H J K : Set ℕ}
    (hHN : H ⊆ N) (hJH : J ⊆ H) (hKJ : K ⊆ J) (hK : K.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy} (origin old p : Concrete.Hist N)
    {a B P Q r t F : ℕ} (L : PreliminaryPivotLabels J B P Q r t) (ha : 2 ≤ a)
    (hop : origin.position.pending = some ⟨false, .advance a⟩)
    (hboard : origin.position.board = Board.initial) (hmode : origin.position.mode = some true)
    (hwin : (exactGame N blue).ArchitectWins H b σ origin)
    (hfrom : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin old)
    (holdp : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) old p)
    (hOld : CriticalCheckpoint old)
    (hp : p.position.pending = some ⟨false, .advance P⟩)
    (hm : p.position.board.left.markerEvent = true)
    (hSroot : ∀ i ∈ p.position.board.left.rootLabel,
      i ≤ p.position.board.left.bodyLabels.length + 1)
    (hother : p.position.board.right = old.position.board.right)
    (hB : max p.position.bound (b p) ≤ B)
    (hTlt : old.position.board.right.leafIndex < old.position.board.right.currentLabel.sup id)
    (hrank : old.position.board.right.currentLabel.card -
      (old.position.board.right.currentLabel.filter
        (fun x => x ≤ old.position.board.right.leafIndex)).card = r)
    (hfresh : ∀ x ∈ K, max B F < x)
    (hall : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin z →
      (exactGame N blue).kind z = .terminal w →
        z.position.board.left.beforeLastLeafCount < z.position.board.right.beforeLastLeafCount) :
    ∃ q, Relation.ReflTransGen ((exactGame N blue).FollowStep σ J b) p q ∧
      q.position.pending = some ⟨false, .advance 0⟩ ∧
      q.position.board.left.relaxed = true ∧ q.position.board.right.relaxed = true ∧
      q.position.board.right.NoLeafPending ∧
      q.position.board.left.rootLabel = p.position.board.left.rootLabel ∧
      q.position.board.left.bodyLabels = p.position.board.left.bodyLabels ++ [L.lower] ∧
      q.position.board.left.currentLabel = L.lower ∧
      q.position.board.left.bodyMarker = L.marker ∧
      q.position.board.right.bodyLabels = old.position.board.right.bodyLabels ∧
      q.position.board.right.leafIndex = old.position.board.right.currentLabel.sup id ∧
      q.position.board.left.leafIndex < L.beta ∧
      (∀ x ∈ L.lower, q.position.board.left.leafIndex < x → L.beta ≤ x) ∧
      (∀ x ∈ L.upper, q.position.board.left.leafIndex < x) ∧
      ∃ k xs, p.position.board.left.parser = .blocks (k + 1) ∧
        LabeledWord.SameStructure q.position.board.left
          (LabeledWord.bodyLeafCursor p.position.board.left L.lower L.marker k xs) ∧
        xs.length = q.position.board.left.leafIndex ∧
        (L.marker :: xs).Pairwise (· < ·) ∧
        (∀ x ∈ xs, x ∈ J ∧ B < x) ∧
        ∃ bs, LabeledWord.LegalRun old.position.board.right bs q.position.board.right ∧
          ∀ atom ∈ bs, atom.2 ∈ K ∧ F < atom.2 := by
  have hJ := hK.mono hKJ
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
  obtain ⟨first, hpFirst, _hFirstNone, hFirstRel, hFirstRoot, hFirstLabels, hFirstCurrent,
      _hFirstIndex, hFirstMarker, hFirstOther, k, xs, hparse, hword, _hlen, hinc, hpool⟩ :=
    prescribed_body_opening (hJH.trans hHN) hJ blue σ p false L.lower
      ⟨_, L.beta_lower⟩ L.lower_card L.lower_fresh L.marker_fresh hp hm hB
  simp only [Board.get] at hFirstRel hFirstRoot hFirstLabels hFirstCurrent
  simp only [Board.get, Bool.not_false] at hFirstMarker hFirstOther hparse hword
  have hFirstT : first.position.board.right = old.position.board.right :=
    hFirstOther.trans hother
  have hFirstLast : ∀ i ∈ first.position.board.left.rootLabel,
      i ≤ first.position.board.left.bodyLabels.length := by
    intro i hi
    simpa only [hFirstLabels, List.length_append, List.length_singleton] using
      hSroot i (hFirstRoot ▸ hi)
  obtain ⟨v, hFirstV, _hvn, hvl, hvr, hvno, hvLabels, hvMarker, hvCurrent, hvTlabels,
      _hvTmarker, hvTindex, _hvRank, hvBeta, hvNext, hvSep, as, bs, has, hbs,
      hpoolS, hpoolT⟩ := preliminary_lower_run hHN hKH hK blue origin old first L ha
        hop hboard hmode hwin hfrom (holdp.trans (pathH (.single hpFirst))) hOld
        hFirstRel (by simpa only [hFirstT] using hOld.right_relaxed) hFirstLast hFirstCurrent
        (by rw [hFirstT]) (by simpa only [hFirstT] using hTlt) hrank hfresh hall
  have hpv := (Relation.ReflTransGen.single hpFirst).trans (pathJ hFirstV)
  have hwinV := (hwin.of_reachable (exactGame N blue)
    (hfrom.trans (holdp.trans (pathH hpv)))).mono (exactGame N blue) hKH (fun _ => le_rfl)
  have hpending : Macro.Pending v.position.board.left :=
    Or.inr ⟨(of_decide_eq_true hvl).2.1, L.beta, hvCurrent ▸ L.beta_lower, hvBeta⟩
  obtain ⟨q, hvq, hqBoard, hqp⟩ := winning_next_selection_after_fresh_leaf
    (hKH.trans hHN) hK blue hwinV true hvr hvSep hvl hpending
  have hSindex : v.position.board.left.leafIndex < L.marker :=
    (L.lower_fresh _ (hvCurrent ▸ (of_decide_eq_true hvl).2.2)).2.2
  have has' : LabeledWord.LegalRun
      (LabeledWord.bodyLeafCursor p.position.board.left L.lower L.marker k xs)
        as v.position.board.left := hword ▸ has
  have hcount : v.position.board.left.bodyLabels.length =
      p.position.board.left.bodyLabels.length + 1 := by
    simp only [hvLabels, hFirstLabels, List.length_append, List.length_singleton]
  obtain ⟨hfullLen, hcoords, hcanon⟩ := has'.bodyLeafCursor_prefix hparse hcount hSindex.le
  have hfullInc : (L.marker :: (xs ++ as.map Prod.snd)).Pairwise (· < ·) := by
    have hi := ((Position.history_dataInvariant v).2.1 false).2
    change v.position.board.left.coordinates.Pairwise (· < ·) at hi
    rw [hcoords] at hi
    exact (List.pairwise_append.mp hi).2.1
  have hrootV : v.position.board.left.rootLabel = p.position.board.left.rootLabel :=
    (has.rootLabel_eq (LabeledWord.relaxed_ne_start
      ((Position.history_dataInvariant first).2.1 false).1 hFirstRel)).trans hFirstRoot
  refine ⟨q, hpv.trans (pathJ hvq), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    k, xs ++ as.map Prod.snd, hparse, ?_, ?_, hfullInc, ?_, bs, ?_, ?_⟩
  · simpa only [Bool.not_true] using hqp
  · simpa only [hqBoard] using hvl
  · simpa only [hqBoard] using hvr
  · simpa only [hqBoard] using hvno
  · simpa only [hqBoard] using hrootV
  · simpa only [hqBoard] using hvLabels.trans hFirstLabels
  · simpa only [hqBoard] using hvCurrent
  · simpa only [hqBoard] using hvMarker.trans hFirstMarker
  · simpa only [hqBoard] using hvTlabels
  · simpa only [hqBoard, hFirstT] using hvTindex
  · simpa only [hqBoard] using hvBeta
  · simpa only [hqBoard] using hvNext
  · intro x hx
    rw [hqBoard]
    rcases lt_or_ge x L.beta with hlt | hge
    · exact L.preliminary_order _ (hvCurrent ▸ (of_decide_eq_true hvl).2.2) hvBeta x hx hlt
    · exact hvBeta.trans_le hge
  · simpa only [hqBoard] using hcanon
  · simpa only [hqBoard] using hfullLen
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact ⟨(hpool x hx).1, L.marker_fresh.2.trans (hpool x hx).2⟩
    · obtain ⟨atom, ha, rfl⟩ := List.mem_map.mp hx
      exact ⟨hKJ (hpoolS atom ha).1, (le_max_left _ _).trans_lt (hpoolS atom ha).2⟩
  · simpa only [hqBoard, hFirstT] using hbs
  · intro atom ha
    exact ⟨(hpoolT atom ha).1, (le_max_right _ _).trans_lt (hpoolT atom ha).2⟩

#print axioms preliminary_first_phase

end Erdos591.Positive.Game.Payoff

end Erdos118.Reused591
