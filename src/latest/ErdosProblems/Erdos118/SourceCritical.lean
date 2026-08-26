import ErdosProblems.Erdos118.ControlledCritical
import ErdosProblems.Erdos118.DeferredSource

/-!
The source controller reaches an actual critical pair on a sampling
subalphabet. Its left suffix is fresh above the old response bound;
the opposite word keeps both its managed data and its exact target replay.
-/

namespace Erdos118.SourceCritical

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates AdaptiveGame
open BlueRuns PreparedRelays ReplaySources DeferredSource
open ManagedCritical (Early Critical early_before)

theorem checkpoint {H K : Set ℕ} (hK : K.Infinite) (hKH : K ⊆ H)
    {B : SimpleGraph G} {targetRight : Bool} {targetOther : Pending}
    (I : Source H B .inside targetRight targetOther) (hI : I.Exact)
    (hlate : ∀ S T : Completed, GraphPayoff.payoff B .inside S T = true →
      LastMarkerRefinement.lastMarker T < LastMarkerRefinement.lastMarker S)
    (hlast : ∀ S T : Completed, GraphPayoff.payoff B .inside S T = true →
      (LastBodyRefinement.lastLabel S).length ≠ 1)
    (d : ℕ) (S T : State) (hS : Early S) (hX : ExactSlots.Exact S) (M : Managed I T)
    (hblue : RamseyGame.Outcome H (GraphPayoff.game B .inside (S, T)) true)
    (hready : Critical S → RightBlue H (GraphPayoff.payoff B .inside) (S, T)) :
    ∃ P Q : Pending, ∃ c : ℕ, P.roots = [c] ∧ P.leaves = [] ∧
      Q.roots = [] ∧ Q.leaves ≠ [] ∧
      ExactSlots.Exact (.leaf P) ∧ ExactSlots.Exact (.leaf Q) ∧
      ConservativeRuns.Run K (GraphPayoff.payoff B .inside) (S, T) (.leaf P, .leaf Q) ∧
      RamseyGame.Outcome H (GraphPayoff.game B .inside (.leaf P, .leaf Q)) true ∧
      LeftBlue H (GraphPayoff.payoff B .inside) (.leaf P, .leaf Q) ∧
      ControlledCritical.FreshLeft K d S (.leaf P) ∧
      Nonempty (Managed I (.leaf Q)) ∧ Nonempty (Replay I Q) := by
  obtain ⟨P, U, c, hR, hL, ⟨MU⟩, hrun, hb, hh, hfP⟩ :=
    ControlledCritical.stop_handoff hK hKH B (Managed I)
      (fun S T hS M hb ↦ respond_right hK hKH I hI S T M (early_before hS) hb)
      d S T hS M hblue hready
  have hne : P.roots ≠ [] := by rw [hR]; simp
  obtain ⟨Q, ⟨MQ⟩, hrun', hb', hh'⟩ := right_handoff hK hKH I hI P U hne MU hh
  have hP := ExactSlots.run_exact_left hrun hX
  obtain ⟨hQR, hQL, _⟩ := LateMarkerCritical.before_last_body_right_nonlast
    (hK.mono hKH) B hlate hlast P Q c hP hR hL hh'
  exact ⟨P, Q, c, hR, hL, hQR, hQL, hP, MQ.exact,
    hrun.trans hrun', hb', hh', hfP, ⟨MQ⟩, MQ.fire (hK.mono hKH) hQR hQL⟩

end Erdos118.SourceCritical
