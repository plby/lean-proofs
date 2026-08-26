import ErdosProblems.Erdos118.Reused591.AtomicCoarsening
import ErdosProblems.Erdos118.Reused591.AtomicInterleave
import ErdosProblems.Erdos118.Reused591.GamePayoff

namespace Erdos118.Reused591

/-!
# The color consequence of an exact retrospective replay

In the all-builder-wins branch, every clear pair supplied by a replay
has no blue edge. The witnesses are vertices of the existing exact
carrier, and the flag is their actual maximum order.
-/

namespace Erdos591.Positive.Game.Atomic

open Erdos591.Negative.Exact

theorem not_blue_of_replay {N H : Set ℕ} (hHN : H ⊆ N) (blue : SimpleGraph G)
    (bound : Concrete.Hist N → ℕ) (mode : Bool)
    (hbuilder : (Payoff.exactGame N blue).AllBuilderWins H bound
      (History.initial (Position.Next N) Position.initial))
    (xs : List Atom) (last : Board) (ht : Trace Board.initial xs last)
    (hdone : Concrete.done last = true) (hinc : (inputs xs).Pairwise (· < ·))
    (hs : Spaced bound ∅ xs) (hH : ∀ x ∈ inputs xs, x ∈ H)
    (hpos : ∀ x ∈ inputs xs, 0 < x) (hfirst : ∀ a ∈ xs.head?, a.side = false)
    (s t : G) (hclear : Payoff.Clear last s t) (hmax : Payoff.MaxOrder mode last) :
    ¬ blue.Adj s t := by
  obtain ⟨k, hpath, hb, hturn, hm, _⟩ := replay_initial hHN (Payoff.payoff blue)
    bound mode xs last ht hdone hinc hs hH hpos hfirst
  intro hblue
  have hpay : Payoff.payoff blue mode last = true :=
    (Payoff.payoff_true_iff blue mode last).2 ⟨s, t, hclear, hblue, hmax⟩
  have hkind : (Payoff.exactGame N blue).kind k = .terminal true := by
    simp [Payoff.exactGame, Concrete.game, Concrete.kind, hturn, hb, hdone, hm, hpay]
  have hfalse := hbuilder k true hpath hkind
  cases hfalse

/-- The numerical conditions can be inherited directly from the full
chronological construction, including work on other root branches. -/
theorem not_blue_of_selected_replay {N H : Set ℕ} (hHN : H ⊆ N)
    (blue : SimpleGraph G) (bound : Concrete.Hist N → ℕ) (mode : Bool)
    (hbuilder : (Payoff.exactGame N blue).AllBuilderWins H bound
      (History.initial (Position.Next N) Position.initial))
    (xs original : List Atom) (hselect : Selects xs original) (last : Board)
    (ht : Trace Board.initial xs last) (hdone : Concrete.done last = true)
    (hinc : (inputs original).Pairwise (· < ·)) (hs : Spaced bound ∅ original)
    (hH : ∀ x ∈ inputs original, x ∈ H) (hpos : ∀ x ∈ inputs original, 0 < x)
    (hfirst : ∀ a ∈ xs.head?, a.side = false)
    (s t : G) (hclear : Payoff.Clear last s t) (hmax : Payoff.MaxOrder mode last) :
    ¬ blue.Adj s t := by
  have hsub := hselect.inputs_sublist
  exact not_blue_of_replay hHN blue bound mode hbuilder xs last ht hdone
    (hinc.sublist hsub) (hselect.spaced (Finset.Subset.refl _) hs)
    (fun x hx => hH x (hsub.subset hx)) (fun x hx => hpos x (hsub.subset hx))
    hfirst s t hclear hmax

/-- Only the explicit word geometry and chronological input conditions
remain as hypotheses. The entire legal trace, its scheduling, terminal
clarity, and support disjointness are derived inside the proof. -/
theorem not_blue_of_canonical_interleaving {N H : Set ℕ} (hHN : H ⊆ N)
    (blue : SimpleGraph G) (bound : Concrete.Hist N → ℕ) (mode : Bool)
    (hbuilder : (Payoff.exactGame N blue).AllBuilderWins H bound
      (History.initial (Position.Next N) Position.initial))
    (s t : G) (hs : CutLabels.Admissible s.val t.val)
    (ht : CutLabels.Admissible t.val s.val)
    (xs original : List Atom) (hselect : Selects xs original)
    (hproj : ∀ side, project xs side = cutProgram s.val t.val side)
    (hinc : (inputs original).Pairwise (· < ·)) (hspaced : Spaced bound ∅ original)
    (hH : ∀ x ∈ inputs original, x ∈ H) (hpos : ∀ x ∈ inputs original, 0 < x)
    (hfirst : ∀ a ∈ xs.head?, a.side = false)
    (hmax : Payoff.MaxOrder mode (cutBoard s.val t.val)) : ¬ blue.Adj s t := by
  have hinc' := hinc.sublist hselect.inputs_sublist
  have htrace := canonical_trace hs ht xs hproj hinc'
  have hdisj := projected_values_disjoint xs (hinc'.sublist (values_sublist_inputs xs))
  have hdisj' : Disjoint (word s.val).toFinset (word t.val).toFinset := by
    simpa only [hproj, cutProgram, LabeledCode.atoms_coordinates,
      CutLabels.erase_bodies] using hdisj
  have hclear : Payoff.Clear (cutBoard s.val t.val) s t :=
    ⟨CutLabels.clearSide s t hs, CutLabels.clearSide t s ht, hdisj'⟩
  exact not_blue_of_selected_replay hHN blue bound mode hbuilder xs original hselect
    (cutBoard s.val t.val) htrace rfl hinc hspaced hH hpos hfirst s t hclear hmax

#print axioms not_blue_of_selected_replay
#print axioms not_blue_of_canonical_interleaving

end Erdos591.Positive.Game.Atomic

end Erdos118.Reused591
