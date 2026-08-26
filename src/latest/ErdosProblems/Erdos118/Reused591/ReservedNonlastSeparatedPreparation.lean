import ErdosProblems.Erdos118.Reused591.ReservedStrictRoot
import ErdosProblems.Erdos118.Reused591.PrepareFirstRoot

namespace Erdos118.Reused591

/-! # Install the rank-one separated U root in the actual inserted SU play -/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact
open Relay

theorem reserved_nonlast_separated_preparation {N H M : Set ℕ}
    (hHN : H ⊆ N) (hMH : M ⊆ H) (hM : M.Infinite)
    (blue : SimpleGraph G) (htri : blue.CliqueFree 3) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy}
    (hroot : (exactGame N blue).ArchitectWins H b σ
      (History.initial (Position.Next N) Position.initial))
    (origin old upperOrigin : Concrete.Hist N) {B a g : ℕ}
    (S : LastLastLabels H B a) (ha : 2 ≤ a) (hg : 2 ≤ g)
    (hwin : (exactGame N blue).ArchitectWins H b σ origin)
    (hop : origin.position.pending = some ⟨false, .advance a⟩)
    (hboard : origin.position.board = Board.initial) (hmode : origin.position.mode = some true)
    (hB : max origin.position.bound (b origin) ≤ B)
    (hfromUpper : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin upperOrigin)
    (hOldBody : old.position.board.left.bodyLabels.length = S.penultimate)
    (hpUpper : upperOrigin.position.pending = some ⟨true, .advance g⟩)
    (hUpperInit : upperOrigin.position.board.right = LabeledWord.initial)
    (hall : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin z →
      (exactGame N blue).kind z = .terminal w →
        z.position.board.left.beforeLastLeafCount < z.position.board.right.beforeLastLeafCount)
    {as : List (Finset ℕ × ℕ)}
    (hraw : (LabeledCode.rootCursor S.lower S.marker).runAtoms as = some old.position.board.left)
    (hinc : (S.marker :: as.map Prod.snd).Pairwise (· < ·))
    (hpool : ∀ x ∈ as.map Prod.snd, x ∈ H) :
    ∃ K, K ⊆ M ∧ K.Infinite ∧ (∀ x ∈ K, max old.position.bound (b old) < x) ∧
      ∃ C e j, ∃ U : SeparatedRootLabels K C e g j, 0 < j ∧ j < e ∧
        ∃ fine, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin fine ∧
          (exactGame N blue).ArchitectWins K b σ fine ∧ fine.position.pending = none ∧
          fine.position.board.left.relaxed = true ∧ fine.position.board.left.rootLabel = S.upper ∧
          fine.position.board.left.bodyLabels.length = S.firstUpper ∧
          ∃ frontAtoms, LabeledWord.LegalRun
            (LabeledWord.rootRelabel S.upper old.position.board.left) frontAtoms
              fine.position.board.left ∧
            (∀ atom ∈ frontAtoms, atom.2 ∈ H ∧ max old.position.bound (b old) < atom.2) ∧
            ∃ R : FirstRootPlan N K blue b σ fine.position.board.right,
              R.target = upperOrigin ∧ R.side = true ∧ R.labels.lower = U.lower ∧
              R.labels.upper = U.upper ∧ R.labels.shared = U.first ∧ R.criticalRank = j ∧
              ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ K b) fine z →
                (exactGame N blue).kind z = .terminal w →
                  z.position.board.right.criticalBodyRank
                    z.position.board.left.lastSelectedLabel.card = R.criticalRank := by
  obtain ⟨J, hJM, hJ, hJfresh, suRoot, e, hfromSU, hwinSU, hpSU, he, hSUrel,
      hSUroot, hSUbody, hSUinit, frontAtoms, hfront, hfrontPool, K, hKJ, hK, j, hj, hje,
      hfixed⟩ := reserved_strict_root_request hHN hMH hM blue htri hroot origin old S ha hwin
        hop hboard hmode hB hOldBody hall hraw hinc hpool
  have hKM := hKJ.trans hJM
  have hKH := hKM.trans hMH
  have pathH {p q : Concrete.Hist N}
      (hpath : Relation.ReflTransGen ((exactGame N blue).FollowStep σ K b) p q) :
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p q :=
    Relation.ReflTransGen.mono (fun _ _ hs =>
      FiniteResponseGame.FollowStep.mono (exactGame N blue) hKH (fun _ => le_rfl) hs) _ _ hpath
  let C := max (max suRoot.position.bound (b suRoot))
    (max upperOrigin.position.bound (b upperOrigin))
  obtain ⟨U⟩ := SeparatedRootLabels.exists_of_infinite hK C e g j hj hje hg
  have hwinUpper := (hwin.of_reachable (exactGame N blue) hfromUpper).mono
    (exactGame N blue) hKH (fun _ => le_rfl)
  obtain ⟨fine, hRf, hnFine, _hmFine, hoFine, R, hRt, hRs, _hRL, hRlower, hRupper,
      hRshared⟩ := prepare_first_root (hKH.trans hHN) hK blue hwinUpper true true U.first_view
        hpSU hpUpper hSUinit hUpperInit (le_max_left _ _) (le_max_right _ _)
  have hFineS : fine.position.board.left = suRoot.position.board.left := hoFine
  have hfromFine := hfromSU.trans (pathH (.single hRf))
  have hRrank : R.criticalRank = j := by
    rw [← R.labels.shared_rank, hRlower, hRshared]
    exact U.first_rank
  refine ⟨K, hKM, hK, (fun x hx => hJfresh x (hKJ hx)), C, e, j, U, hj, hje, fine,
    hfromFine, (hwin.of_reachable (exactGame N blue) hfromFine).mono
      (exactGame N blue) hKH (fun _ => le_rfl), hnFine, ?_, ?_, ?_, frontAtoms, ?_,
      hfrontPool, R, hRt, hRs, hRlower, hRupper, hRshared, hRrank, ?_⟩
  · simpa only [hFineS] using hSUrel
  · simpa only [hFineS] using hSUroot
  · simpa only [hFineS] using hSUbody
  · simpa only [hFineS] using hfront
  · intro z w hpath hz
    simpa only [hRrank] using (hfixed z w ((Relation.ReflTransGen.single hRf).trans hpath) hz).1

#print axioms reserved_nonlast_separated_preparation

end Erdos591.Positive.Game.Payoff



end Erdos118.Reused591
