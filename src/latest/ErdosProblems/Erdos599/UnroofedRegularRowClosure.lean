/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.UnroofedRegularRowTransport
import ErdosProblems.Erdos599.RegularExtension

/-!
# Whole-path and limit-roof closure of the actual unroofed rows

The transported pair entries close every earlier row under both the old
warp and every accumulated warp. Two vertices of a limit path are already
visible together at an ordinary stage, so the final carrier is limit-closed.
-/

noncomputable section

namespace Erdos599.CardinalInduction.UnroofedRegularRows

open Set Cardinal RegularRows

universe u

variable {V : Type u} (G : DWeb V) {kappa : Cardinal.{u}}

private theorem pathsMeeting_eq_rowPathsMeeting (F : Set G.DPath) (S : Set V) :
    RegularExtension.pathsMeeting G F S = CausalRegular.rowPathsMeeting G F S := by
  ext p
  constructor
  · rintro ⟨hpF, x, hxp, hxS⟩
    exact ⟨hpF, Set.not_disjoint_iff.2 ⟨x, hxp, hxS⟩⟩
  · rintro ⟨hpF, hpS⟩
    obtain ⟨x, hxp, hxS⟩ := Set.not_disjoint_iff.1 hpS
    exact ⟨hpF, x, hxp, hxS⟩

variable (hregular : kappa.IsRegular) (huncountable : aleph0 < kappa)
  (hNorm : G.IsNormalized) (F : Set G.DPath) (hF : G.IsWarp F)
  (base : Set V) (hbase : #base ≤ kappa)

theorem carrier_registersOldLinkage :
    let Q := rowRule G hregular huncountable hNorm F hF base hbase
    let R := Q.rowSystem hregular.aleph0_le
    ∀ i, G.vertexSet (RegularExtension.pathsMeeting G F (R.row i)) ⊆ R.carrier := by
  dsimp only
  let Q := rowRule G hregular huncountable hNorm F hF base hbase
  let gamma : Ladder.Stage kappa := ⟨0, hregular.ord_pos⟩
  intro i
  rw [pathsMeeting_eq_rowPathsMeeting]
  exact Set.subset_union_left.trans (twoWarpRowRegistration_subset_carrier G hregular
    huncountable hNorm F hF base hbase i gamma)

theorem carrier_registersAccumulatedWarps :
    let Q := rowRule G hregular huncountable hNorm F hF base hbase
    let R := Q.rowSystem hregular.aleph0_le
    let L := DWeb.UnroofedMarker.causalLadder G Q hregular.aleph0_le
    ∀ i a, G.vertexSet (RegularExtension.pathsMeeting G (L.warpAt a) (R.row i)) ⊆
      R.carrier := by
  dsimp only
  intro i a
  rw [pathsMeeting_eq_rowPathsMeeting]
  exact Set.subset_union_right.trans (twoWarpRowRegistration_subset_carrier G hregular
    huncountable hNorm F hF base hbase i a)

theorem carrier_isLimitWarpClosed :
    let Q := rowRule G hregular huncountable hNorm F hF base hbase
    let R := Q.rowSystem hregular.aleph0_le
    let L := DWeb.UnroofedMarker.causalLadder G Q hregular.aleph0_le
    SliceSplice.IsLimitWarpClosed G L R.carrier := by
  dsimp only
  let Q := rowRule G hregular huncountable hNorm F hF base hbase
  have hNoEnter : G.NoEdgeEnters G.source := by
    intro x y hxy hy
    exact (hNorm hxy).1 hy
  apply RegularExtension.isLimitWarpClosed_of_rowRegistrations G
    (DWeb.UnroofedMarker.ladder_spliceGeometry G kappa (Q.preferred hregular.aleph0_le)
      hNoEnter hregular) (Q.rowSystem hregular.aleph0_le)
  exact carrier_registersAccumulatedWarps G hregular huncountable hNorm F hF base hbase

theorem carrier_subset_limitRoof :
    let Q := rowRule G hregular huncountable hNorm F hF base hbase
    (Q.rowSystem hregular.aleph0_le).carrier ⊆
      (DWeb.UnroofedMarker.causalLadder G Q hregular.aleph0_le).limitRoof := by
  dsimp only
  apply DWeb.UnroofedMarker.causalCarrier_subset_limitRoof G _ _ hregular huncountable
  intro x y hxy hy
  exact (hNorm hxy).1 hy

theorem exists_club_unhindered_stages (hG : G.IsUnhindered) :
    let Q := rowRule G hregular huncountable hNorm F hF base hbase
    let L := DWeb.UnroofedMarker.causalLadder G Q hregular.aleph0_le
    ∃ C : Set (Ladder.Stage kappa), Stationary.IsClubBelow kappa C ∧
      Disjoint C L.phi ∧ ∀ a ∈ C, (L.stageWeb a).IsUnhindered := by
  dsimp only
  apply DWeb.UnroofedMarker.causalLadder_exists_goodClub G _ _ hregular huncountable hNorm hG
  intro x y hxy hy
  exact (hNorm hxy).1 hy

#print axioms carrier_registersOldLinkage
#print axioms carrier_registersAccumulatedWarps
#print axioms carrier_isLimitWarpClosed
#print axioms carrier_subset_limitRoof
#print axioms exists_club_unhindered_stages

end Erdos599.CardinalInduction.UnroofedRegularRows
