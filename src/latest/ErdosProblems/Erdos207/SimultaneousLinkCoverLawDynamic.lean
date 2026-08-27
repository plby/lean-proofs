/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SimultaneousLinkCoverLaw

/-!
# Dynamic realization of a simultaneous link-cover law

All reservoirs are exposed at once, but centers may still be processed in a
finite dynamic order.  At a good reservoir outcome, assume the robust
single-link extension is available at every state reachable inside the old
packing plus the exposed global reservoir.  The deterministic multi-link
iterator then returns a valid simultaneous cover contained in that same
reservoir.  Conditioning therefore retains the global C4 estimate.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- Statewise robust link extensions inside one exposed global reservoir
produce a simultaneous cover contained in that reservoir. -/
theorem exists_simultaneousLinkCover_of_statewise_reservoir_extensions
    {O V : Type*} [Fintype O] [DecidableEq O] [Fintype V] [DecidableEq V]
    (U : Finset V) (center : O ↪ V) (K : O → BipartiteLink V)
    (hcenter : ∀ o, (K o).center = center o)
    (hout : ∀ o, center o ∉ U)
    (hleft : ∀ o, (K o).left ⊆ U)
    (hright : ∀ o, (K o).right ⊆ U)
    (F : ForbiddenFamilyOn V) (available P : TripleSystemOn V)
    (hPpacking : IsPackingOn P) (hPavoid : AvoidsForbidden P F)
    (ω : SimultaneousLinkPair O V K → Bool)
    (hstep : ∀ (P' : TripleSystemOn V),
      P ⊆ P' →
      P' ⊆ P ∪ (available ∩ simultaneousLinkReservoir U center K hcenter
        hout hleft hright ω) →
      IsPackingOn P' → AvoidsForbidden P' F →
      ∀ o, HasLinkCoverExtension F
        (available ∩ simultaneousLinkReservoir U center K hcenter
          hout hleft hright ω) P' (K o)) :
    ∃ M : TripleSystemOn V,
      M ⊆ simultaneousLinkReservoir U center K hcenter hout hleft hright ω ∧
      IsSimultaneousLinkCover F available P K M := by
  obtain ⟨M, hMsub, hPMdisjoint, hPMpacking, hPMavoid, hlinks⟩ :=
    exists_simultaneous_bipartiteLink_cover F
      (available ∩ simultaneousLinkReservoir U center K hcenter hout hleft
        hright ω) P K hPpacking hPavoid hstep
  refine ⟨M, ?_, ?_⟩
  · intro T hTM
    exact (mem_inter.mp (hMsub hTM)).2
  · refine ⟨?_, hPMdisjoint, hPMpacking, hPMavoid, hlinks⟩
    intro T hTM
    exact (mem_inter.mp (hMsub hTM)).1

/-- A global good-event estimate together with statewise dynamic extensions
gives an actual C4 law supported on complete simultaneous link covers. -/
theorem exists_simultaneousLinkCoverLaw_of_dynamic_extensions
    {O V : Type*} [Fintype O] [DecidableEq O] [Fintype V] [DecidableEq V]
    (U : Finset V) (center : O ↪ V) (K : O → BipartiteLink V)
    (hcenter : ∀ o, (K o).center = center o)
    (hout : ∀ o, center o ∉ U)
    (hleft : ∀ o, (K o).left ⊆ U)
    (hright : ∀ o, (K o).right ⊆ U)
    (F : ForbiddenFamilyOn V) (available P : TripleSystemOn V)
    (hPpacking : IsPackingOn P) (hPavoid : AvoidsForbidden P F)
    (sigma : ℝ≥0) (hsigma : sigma ≤ 1)
    (Good : (SimultaneousLinkPair O V K → Bool) → Prop)
    (hbad : (FiniteLaw.independentBits
      (fun _ : SimultaneousLinkPair O V K ↦ sigma)
      (fun _ ↦ hsigma)).probability (fun ω ↦ ¬ Good ω) < 1)
    (hstep : ∀ ω, Good ω → ∀ (P' : TripleSystemOn V),
      P ⊆ P' →
      P' ⊆ P ∪ (available ∩ simultaneousLinkReservoir U center K hcenter
        hout hleft hright ω) →
      IsPackingOn P' → AvoidsForbidden P' F →
      ∀ o, HasLinkCoverExtension F
        (available ∩ simultaneousLinkReservoir U center K hcenter
          hout hleft hright ω) P' (K o)) :
    ∃ L : FiniteLaw (TripleSystemOn V),
      L.SupportedOn (IsSimultaneousLinkCover F available P K) ∧
      ∀ Q : TripleSystemOn V,
        L.probability (fun M ↦ Q ⊆ M) ≤
          sigma ^ Q.card /
            (FiniteLaw.independentBits
              (fun _ : SimultaneousLinkPair O V K ↦ sigma)
              (fun _ ↦ hsigma)).probability Good := by
  apply exists_simultaneousLinkCoverLaw_of_failure_lt_one
    U center K hcenter hout hleft hright F available P sigma hsigma
      Good hbad
  intro ω hω
  exact exists_simultaneousLinkCover_of_statewise_reservoir_extensions
    U center K hcenter hout hleft hright F available P hPpacking hPavoid ω
      (hstep ω hω)

end

end Erdos207
