/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.RootedThreatTransport
import ErdosProblems.Erdos207.TerminalControlCertificate

/-!
# A finite deterministic certificate before terminal continuation

This theorem converts controls at an intermediate state into an outside
packing.  Its hypotheses explicitly reserve the worst-case additive growth
of vertex stars and rooted active witnesses over the remaining number of
greedy insertions.
-/

namespace Erdos207

open Finset

noncomputable section

/-- If the current terminal margins dominate every possible change in the
exhausting continuation, some continuation outcome is a KSSS outside
packing. -/
theorem exists_ksssOutsidePacking_of_terminalContinuationControls
    {V : Type*} [Fintype V] [DecidableEq V]
    {q d r K : ℕ} {H : SimpleGraph V} [DecidableRel H.Adj]
    {X : Finset V} {B : TripleSystemOn V} {S₀ : GreedyStateOn V}
    (hInv : AbsorberGreedyInvariant
      (absorberErdosForbiddenConfigurationsOn q B)
      (outsideAvailableTriangles H B) S₀)
    (hbudget : ∀ u v : V, u ≠ v → ¬H.Adj u v →
      H.degree u + H.degree v + B.card + (4 * d + r * q) ≤
        Fintype.card V - 2)
    (hstar : ∀ v : V,
      (triplesThrough S₀.chosen v).card + S₀.available.card < d)
    (husing : ∀ e : DistinctPair V, ∀ T : TripleOn V,
      (rootedThreatWitnessesUsing
        (absorberErdosForbiddenConfigurationsOn q B)
        e.1.1 e.1.2 T).card ≤ K)
    (hroot : ∀ e : DistinctPair V,
      (rootedActiveForbiddenConfigurations
          (absorberErdosForbiddenConfigurationsOn q B)
          S₀.chosen e.1.1 e.1.2).card * q +
        S₀.available.card * K < r) :
    ∃ P : TripleSystemOn V, HasKSSSOutsidePacking q H X B P := by
  let F := absorberErdosForbiddenConfigurationsOn q B
  let fuel := S₀.available.card
  let L := FiniteLaw.iterateKernel (greedyKernel F) fuel
    (FiniteLaw.pure S₀)
  have hpos : 0 < ∑ S, L.mass S := by
    rw [L.sum_mass]
    exact zero_lt_one
  obtain ⟨S, _hSuniv, hmass⟩ := Finset.sum_pos_iff.mp hpos
  have hterminal := absorberGreedyContinuationLaw_supported S₀ hInv S hmass
  have hstarSupport : ∀ v : V,
      (triplesThrough S.chosen v).card ≤
        (triplesThrough S₀.chosen v).card + fuel := by
    intro v
    exact iterateGreedyKernel_supported_triplesThrough_card_le
      F fuel S₀ v S hmass
  have hrootSupport : ∀ e : DistinctPair V,
      (rootedActiveForbiddenConfigurations F S.chosen
        e.1.1 e.1.2).card ≤
        (rootedActiveForbiddenConfigurations F S₀.chosen
          e.1.1 e.1.2).card * q + fuel * K := by
    intro e
    exact iterateGreedyKernel_supported_rootedActive_card_le
      F fuel S₀ e.1.1 e.1.2 q K
        (fun C hC ↦ card_le_cutoff_of_mem_absorberErdosForbidden hC)
        (husing e) S hmass
  refine ⟨S.chosen,
    hasKSSSOutsidePacking_of_exhausted_terminalControls
      hterminal.1 hterminal.2.2 hbudget ?_ ?_⟩
  · intro v
    exact (hstarSupport v).trans_lt (by simpa only [fuel] using hstar v)
  · intro e
    exact (hrootSupport e).trans_lt (by simpa only [F, fuel] using hroot e)

end

end Erdos207
