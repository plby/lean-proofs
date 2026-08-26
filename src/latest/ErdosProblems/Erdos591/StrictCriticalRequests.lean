import ErdosProblems.Erdos591.LocalCriticalUniformization
import ErdosProblems.Erdos591.FirstRootMarkerRequests

/-!
# Actual critical body requests followed by finite leaf-rank localization

This staged interface leaves all body-label choices to the caller.
The upper request may occur on either side of a previously reached
history. Its only size conclusion is the proved positive size. The
fixed global last/nonlast color determines whether the localized lower
leaf rank equals its full issued size.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact
open Relay

theorem strict_critical_requests_local {N H K : Set ℕ}
    (hHN : H ⊆ N) (hKH : K ⊆ H) (hK : K.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    (origin p : Concrete.Hist N)
    (R : FirstRootPlan N K blue b σ p.position.board.right)
    {a : ℕ} (ha : 2 ≤ a)
    (hop : origin.position.pending = some ⟨false, .advance a⟩)
    (hboard : origin.position.board = Board.initial) (hmode : origin.position.mode = some true)
    (hwin : (exactGame N blue).ArchitectWins H b σ origin)
    (hfrom : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin p)
    (hall : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin z →
      (exactGame N blue).kind z = .terminal w →
        z.position.board.left.beforeLastLeafCount < z.position.board.right.beforeLastLeafCount)
    (value : Bool)
    (hcolor : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin z →
      (exactGame N blue).kind z = .terminal w → criticalLastColor z = value)
    (hfixed : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ K b) p z →
      (exactGame N blue).kind z = .terminal w →
        z.position.board.right.criticalBodyRank z.position.board.left.lastSelectedLabel.card =
          R.criticalRank) :
    ∃ lower upper d c,
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ K b) p lower ∧
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ K b) R.target upper ∧
      lower.position.pending = some ⟨true, .advance d⟩ ∧
      upper.position.pending = some ⟨R.side, .advance c⟩ ∧ 0 < d ∧ 0 < c ∧
      lower.position.board.right.markerEvent = true ∧
      (upper.position.board.get R.side).markerEvent = true ∧
      LabeledWord.SameStructure lower.position.board.right (upper.position.board.get R.side) ∧
      lower.position.board.right.rootLabel = R.labels.lower ∧
      lower.position.board.right.bodyLabels.length + 1 = R.labels.shared ∧
      (upper.position.board.get R.side).rootLabel = R.labels.upper ∧
      (upper.position.board.get R.side).NoRootPassed ∧
      upper.position.board.get (!R.side) = R.target.position.board.get (!R.side) ∧
      ∃ L, L ⊆ K ∧ L.Infinite ∧ ∃ s, 0 < s ∧ s ≤ d ∧ (s = d ↔ value = true) ∧
        ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ L b) lower z →
        (exactGame N blue).kind z = .terminal w →
          z.position.board.right.criticalBodyRank z.position.board.left.lastSelectedLabel.card =
            (lower.position.board.right.rootLabel.filter
              (fun i => i ≤ lower.position.board.right.bodyLabels.length + 1)).card ∧
          z.position.board.right.criticalLeafRank z.position.board.left.lastSelectedLabel.card =
            s := by
  have pathH {u v : Concrete.Hist N}
      (hpath : Relation.ReflTransGen ((exactGame N blue).FollowStep σ K b) u v) :
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) u v :=
    Relation.ReflTransGen.mono (fun _ _ hs =>
      FiniteResponseGame.FollowStep.mono (exactGame N blue) hKH (fun _ => le_rfl) hs) _ _ hpath
  have hwinP := (hwin.of_reachable (exactGame N blue) hfrom).mono
    (exactGame N blue) hKH (fun _ => le_rfl)
  obtain ⟨lower, upper, d, c, hpl, hupper, hlp, hup, hd, hc, hlm, hum, hsame,
      hlroot, hli, hlrank, huroot, huno, huother⟩ :=
    R.request_shared true (hKH.trans hHN) hK hwinP
  have htoLower := hfrom.trans (pathH hpl)
  obtain ⟨L, hLK, hL, s, hs, hsd, hleaf⟩ := strict_critical_leaf_local_of_rank
    hHN hKH hK blue origin lower ha hop hboard hmode hwin htoLower hlp hlm hall hlrank
      (fun z w hpath hz => hfixed z w (hpl.trans hpath) hz)
  have pathK {u v : Concrete.Hist N}
      (hpath : Relation.ReflTransGen ((exactGame N blue).FollowStep σ L b) u v) :
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ K b) u v :=
    Relation.ReflTransGen.mono (fun _ _ hs =>
      FiniteResponseGame.FollowStep.mono (exactGame N blue) hLK (fun _ => le_rfl) hs) _ _ hpath
  obtain ⟨z, w, hlz, hz⟩ := (exactGame N blue).terminal_reachable_of_infinite
    ((hLK.trans hKH).trans hHN) hL b σ lower
  have hiff : s = d ↔ value = true := by
    have h := (hleaf z w hlz hz).2
    rw [hcolor z w (htoLower.trans (pathH (pathK hlz))) hz] at h
    exact h.symm
  refine ⟨lower, upper, d, c, hpl, hupper, hlp, hup, hd, hc, hlm, hum, hsame,
    hlroot, hli, huroot, huno, huother, L, hLK, hL, s, hs, hsd, hiff, ?_⟩
  intro z w hpath hz
  exact ⟨(hfixed z w (hpl.trans (pathK hpath)) hz).trans hlrank.symm,
    (hleaf z w hpath hz).1⟩

#print axioms strict_critical_requests_local

end Erdos591.Positive.Game.Payoff
