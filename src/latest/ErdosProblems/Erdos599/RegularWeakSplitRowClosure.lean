/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.RegularWeakSplitRows

/-!
# Global closure of the weak-split causal carrier

The enhanced weak-split row rule retains every pair registration of the
ordinary regular causal rule.  Its final carrier is consequently closed
under the limiting canonical ladder warp.  Independently, the causal fair
schedule emits every carrier vertex, so the preferred-marker ladder captures
the carrier in its limiting roof.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace RegularWeakSplitRowClosure

universe u

variable {V : Type u}

/-- Re-export the pair-registration closure theorem at the weak-row module
boundary used by the selected source-9.15 provider. -/
theorem carrier_isLimitWarpClosed
    (G : DWeb V) {kappa : Cardinal.{u}}
    (hkappa : kappa.IsRegular) (hkappaUncountable : aleph0 < kappa)
    (hG : G.IsNormalized)
    (hlower : UniversalCardinalInductionBelow V kappa)
    (F : Set G.DPath) (hF : G.IsWarp F)
    (base : Set V) (hbase : #base ≤ kappa) :
    let Q := RegularRows.CausalRegular.weakSplitRowRule G hkappa
      hkappaUncountable hG hlower F hF base hbase
    let R := Q.rowSystem hkappa.aleph0_le
    let L := DWeb.KappaLadder.canonicalLadder G kappa
      (Q.preferred hkappa.aleph0_le)
    SliceSplice.IsLimitWarpClosed G L R.carrier :=
  RegularRows.CausalRegular.weakSplitRowCarrier_isLimitWarpClosed
    G hkappa hkappaUncountable hG hlower F hF base hbase

/-- Every vertex of the enhanced weak-split carrier is captured by the
preferred-marker ladder and therefore belongs to its limiting roof.  The
argument is generic for causal row rules; the extra triple registrations do
not change it. -/
theorem carrier_subset_limitRoof
    (G : DWeb V) {kappa : Cardinal.{u}}
    (hkappa : kappa.IsRegular) (hkappaUncountable : aleph0 < kappa)
    (hG : G.IsNormalized)
    (hlower : UniversalCardinalInductionBelow V kappa)
    (F : Set G.DPath) (hF : G.IsWarp F)
    (base : Set V) (hbase : #base ≤ kappa) :
    let Q := RegularRows.CausalRegular.weakSplitRowRule G hkappa
      hkappaUncountable hG hlower F hF base hbase
    let R := Q.rowSystem hkappa.aleph0_le
    let L := DWeb.KappaLadder.canonicalLadder G kappa
      (Q.preferred hkappa.aleph0_le)
    R.carrier ⊆ L.limitRoof := by
  dsimp only
  let Q := RegularRows.CausalRegular.weakSplitRowRule G hkappa
    hkappaUncountable hG hlower F hF base hbase
  let R := Q.rowSystem hkappa.aleph0_le
  let L := DWeb.KappaLadder.canonicalLadder G kappa
    (Q.preferred hkappa.aleph0_le)
  have hNoEnter : G.NoEdgeEnters G.source := by
    intro x y hxy hy
    exact (hG hxy).1 hy
  have hL : L.IsSplitLegal :=
    DWeb.KappaLadder.canonicalLadder_isSplitLegal
      (Q.preferred hkappa.aleph0_le) hkappa hkappaUncountable hNoEnter
  change R.carrier ⊆ L.limitRoof
  intro x hx
  obtain ⟨a, ha⟩ := Q.exists_preferred_eq_some_of_mem_carrier
    hkappa hkappaUncountable hx
  let b : Ladder.Stage kappa :=
    ⟨a.1 + 1, (Cardinal.isSuccLimit_ord hkappa.aleph0_le).succ_lt a.2⟩
  exact DWeb.KappaLadder.canonicalLadderCore_preferred_mem_limitRoof_of_fields
    (Q.preferred hkappa.aleph0_le) hG hL.freshMarkers hL.waveRungs
      hL.exactSuccessorArrows hL.roofsSourceAtStages a b rfl ha

end RegularWeakSplitRowClosure
end CardinalInduction
end Erdos599
