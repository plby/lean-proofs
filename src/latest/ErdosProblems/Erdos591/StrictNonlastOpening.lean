import ErdosProblems.Erdos591.StrictNonlastPreparation
import ErdosProblems.Erdos591.CriticalOpeningHandoff

/-! # The nonlast critical opening gives two actual compatible play prefixes -/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact
open Relay

theorem strict_nonlast_critical_opening {N H K : Set ℕ}
    (hHN : H ⊆ N) (hKH : K ⊆ H) (hK : K.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    (origin p : Concrete.Hist N)
    (R : CriticalRootPlan N K blue b σ p.position.board.right)
    (hRt : R.target = origin) (hRs : R.side = false)
    {a : ℕ} (ha : 2 ≤ a)
    (hop : origin.position.pending = some ⟨false, .advance a⟩)
    (hboard : origin.position.board = Board.initial) (hmode : origin.position.mode = some true)
    (hwin : (exactGame N blue).ArchitectWins H b σ origin)
    (hfrom : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin p)
    (hpos : 0 < p.position.board.left.coordinates.length)
    (hfirst : ∀ q v d, (exactGame N blue).FollowStep σ H b origin q →
      (exactGame N blue).FollowStep σ H b q v →
      v.position.pending = some ⟨false, .advance d⟩ → 2 ≤ d)
    (hall : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin z →
      (exactGame N blue).kind z = .terminal w →
        z.position.board.left.beforeLastLeafCount < z.position.board.right.beforeLastLeafCount)
    (hlast : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin z →
      (exactGame N blue).kind z = .terminal w → criticalLastColor z = false)
    (hfixed : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ K b) p z →
      (exactGame N blue).kind z = .terminal w →
        z.position.board.right.criticalBodyRank z.position.board.left.lastSelectedLabel.card =
          R.criticalRank) :
    ∃ L, L ⊆ K ∧ L.Infinite ∧ ∃ B d c s, ∃ D : CriticalLeafLabels L B d c s,
      2 ≤ c ∧ 0 < s ∧ s < d ∧ ∃ old upper,
        Relation.ReflTransGen ((exactGame N blue).FollowStep σ K b) p old ∧
        Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin upper ∧
        old.position.pending = some ⟨false, .advance 0⟩ ∧ CriticalCheckpoint old ∧
        old.position.board.right.rootLabel = R.labels.lower ∧
        old.position.board.right.bodyLabels.length = R.labels.shared ∧
        old.position.board.right.currentLabel = D.lower ∧
        old.position.board.right.leafIndex = D.upperView.pivot ∧
        upper.position.pending = none ∧
        LabeledWord.SameStructure old.position.board.right upper.position.board.left ∧
        upper.position.board.left.relaxed = true ∧
        upper.position.board.left.rootLabel = R.labels.upper ∧
        upper.position.board.left.bodyLabels.length = R.labels.shared ∧
        upper.position.board.left.currentLabel = D.upperView.upper ∧
        upper.position.board.left.leafIndex = D.upperView.pivot ∧
        upper.position.board.right = LabeledWord.initial ∧ upper.position.mode = some true := by
  have pathH {u v : Concrete.Hist N}
      (hpath : Relation.ReflTransGen ((exactGame N blue).FollowStep σ K b) u v) :
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) u v :=
    Relation.ReflTransGen.mono (fun _ _ hs =>
      FiniteResponseGame.FollowStep.mono (exactGame N blue) hKH (fun _ => le_rfl) hs) _ _ hpath
  obtain ⟨L, hLK, hL, B, d, c, s, D, hc, hs, hsd, q, hpq, _hqn, hcp, hroot, hbody,
      hlabel, hindex, P, hPs, _hPL, hPpivot, hPupper, hPpath, hPuroot, _hPuno, hPother⟩ :=
    strict_nonlast_critical_prepared hHN hKH hK blue origin p R hRt hRs ha hop hboard hmode
      hwin hfrom hpos hfirst hall hlast hfixed
  have pathK {u v : Concrete.Hist N}
      (hpath : Relation.ReflTransGen ((exactGame N blue).FollowStep σ L b) u v) :
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ K b) u v :=
    Relation.ReflTransGen.mono (fun _ _ hs =>
      FiniteResponseGame.FollowStep.mono (exactGame N blue) hLK (fun _ => le_rfl) hs) _ _ hpath
  have hwinQ := (hwin.of_reachable (exactGame N blue) (hfrom.trans (pathH hpq))).mono
    (exactGame N blue) (hLK.trans hKH) (fun _ => le_rfl)
  obtain ⟨old, upper, hqold, huStep, hOldBoard, hpend, hcpOld, huNone, hshape,
      huRel, huRoot, huLabel, huLeaf, huOther⟩ :=
    critical_opening_handoff ((hLK.trans hKH).trans hHN) hL blue q P hwinQ hcp
      (hindex.trans hPpivot.symm)
  have huPath := hPpath.trans (pathH (pathK (.single huStep)))
  have hshape' : LabeledWord.SameStructure old.position.board.right upper.position.board.left := by
    simpa only [hPs, Board.get] using hshape
  simp only [hPs, Bool.not_false, Board.get] at huRoot huOther
  refine ⟨L, hLK, hL, B, d, c, s, D, hc, hs, hsd, old, upper, hpq.trans (pathK hqold),
    huPath, hpend, hcpOld, ?_, ?_, ?_, ?_, huNone, hshape', ?_, ?_, ?_, ?_, ?_, ?_,
      follow_mode_some huPath hmode⟩
  · simpa only [hOldBoard] using hroot
  · simpa only [hOldBoard] using hbody
  · simpa only [hOldBoard] using hlabel
  · simpa only [hOldBoard] using hindex
  · simpa only [hPs, Board.get] using huRel
  · exact huRoot.trans hPuroot
  · rw [← hshape'.body_length, hOldBoard]
    exact hbody
  · simpa only [hPs, Board.get] using huLabel.trans hPupper
  · simpa only [hPs, Board.get] using huLeaf.trans hPpivot
  · exact huOther.trans hPother

#print axioms strict_nonlast_critical_opening

end Erdos591.Positive.Game.Payoff
