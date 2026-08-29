/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.RegularRows
import ErdosProblems.Erdos599.RegularExtension
import ErdosProblems.Erdos599.RegularWeakSplitCandidate
import ErdosProblems.Erdos599.RegularWeakHalfwayRegistration
import ErdosProblems.Erdos599.RegularSplitLegality

/-!
# Causal rows with weak split-candidate registrations

This module is the bounded-registration analogue of
`RegularRows.CausalRegular.tripleEntry`.  It retains the existing annular
maverick registration and adds the target-carrier/clean-maverick
registration of `RegularWeakSplitCandidate` at the same triple owner.

It is kept as a separate row rule so the new causal table can be checked
without changing consumers of the original row rule.  The final theorem
shows that a coordinate chosen in the completed ladder is already closed
in the carrier of this enhanced causal rule.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace RegularRows.CausalRegular

universe u

variable {V : Type u}

/-- A harmless coordinate used to expose a fixed registration row. -/
def firstStage {kappa : Cardinal.{u}} (huncountable : aleph0 < kappa) :
    RegularCardinal.Stage kappa :=
  ⟨0, Cardinal.ord_pos.mpr (Cardinal.aleph0_pos.trans huncountable)⟩

/-- A causal owner strictly above two previously available coordinates. -/
def ownerStage {kappa : Cardinal.{u}} (hkappa : aleph0 ≤ kappa)
    (a b : RegularCardinal.Stage kappa) : RegularCardinal.Stage kappa :=
  ⟨max a.1 b.1 + 1,
    (Cardinal.isSuccLimit_ord hkappa).succ_lt (max_lt a.2 b.2)⟩

theorem left_lt_ownerStage {kappa : Cardinal.{u}}
    (hkappa : aleph0 ≤ kappa) (a b : RegularCardinal.Stage kappa) :
    a < ownerStage hkappa a b :=
  (le_max_left a.1 b.1).trans_lt (lt_add_one _)

theorem right_lt_ownerStage {kappa : Cardinal.{u}}
    (hkappa : aleph0 ≤ kappa) (a b : RegularCardinal.Stage kappa) :
    b < ownerStage hkappa a b :=
  (le_max_right a.1 b.1).trans_lt (lt_add_one _)

private theorem pathsMeeting_eq_rowPathsMeeting
    (G : DWeb V) (F : Set G.DPath) (S : Set V) :
    RegularExtension.pathsMeeting G F S = rowPathsMeeting G F S := by
  ext p
  constructor
  · rintro ⟨hpF, x, hxp, hxS⟩
    exact ⟨hpF, Set.not_disjoint_iff.2 ⟨x, hxp, hxS⟩⟩
  · rintro ⟨hpF, hpS⟩
    obtain ⟨x, hxp, hxS⟩ := Set.not_disjoint_iff.1 hpS
    exact ⟨hpF, x, hxp, hxS⟩

private theorem regularExtension_twoWarpRowRegistration_eq
    (G : DWeb V) (F Y : Set G.DPath) (S : Set V) :
    RegularExtension.twoWarpRowRegistration G F Y S =
      twoWarpRowRegistration G F Y S := by
  unfold RegularExtension.twoWarpRowRegistration twoWarpRowRegistration
  rw [pathsMeeting_eq_rowPathsMeeting G F S,
    pathsMeeting_eq_rowPathsMeeting G Y S]

/-- Pair-owned registration enhanced by the selected carrier of the causal
half-way row.  The old pair entry is retained verbatim as the left summand. -/
noncomputable def weakSplitPairEntry (G : DWeb V)
    {kappa : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hkappaUncountable : aleph0 < kappa) (F : Set G.DPath)
    (a : RegularCardinal.Stage kappa)
    (prior : ∀ b : RegularCardinal.Stage kappa,
      b < a → RegularRows.CausalState kappa V)
    (delta gamma : Set.Iio a) : Set V :=
  pairEntry G hlower hkappaUncountable F a prior delta gamma ∪
    RegularWeakHalfwayRegistration.registrationAt hlower
      hkappaUncountable (priorLadder G a prior)
      (priorRequest G hkappaUncountable.le a prior) delta.1 gamma.1

theorem mk_weakSplitPairEntry_le (G : DWeb V)
    {kappa : Cardinal.{u}} (hkappa : kappa.IsRegular)
    (hkappaUncountable : aleph0 < kappa) (hG : G.IsNormalized)
    (hlower : UniversalCardinalInductionBelow V kappa)
    (F : Set G.DPath) (hF : G.IsWarp F)
    (a : RegularCardinal.Stage kappa)
    (prior : ∀ b : RegularCardinal.Stage kappa,
      b < a → RegularRows.CausalState kappa V)
    (delta gamma : Set.Iio a) :
    #(weakSplitPairEntry G hlower hkappaUncountable F a prior
      delta gamma) ≤ kappa := by
  exact (Cardinal.mk_union_le _ _).trans
    (Cardinal.add_le_of_le hkappa.aleph0_le
      (mk_pairEntry_le G hkappa hkappaUncountable hG hlower F hF
        a prior delta gamma)
      (RegularWeakHalfwayRegistration.mk_registrationAt_le hkappa hlower
        hkappaUncountable (priorLadder G a prior)
        (priorRequest G hkappa.aleph0_le a prior) delta.1 gamma.1))

/-- Existing annular registration plus the weak split registration owned
by the same causal triple. -/
noncomputable def weakSplitTripleEntry (G : DWeb V)
    {kappa : Cardinal.{u}} (hkappa : aleph0 ≤ kappa)
    (a : RegularCardinal.Stage kappa)
    (prior : ∀ b : RegularCardinal.Stage kappa,
      b < a → RegularRows.CausalState kappa V)
    (delta beta gamma : Set.Iio a) : Set V :=
  tripleEntry G hkappa a prior delta beta gamma ∪
    RegularWeakSplitCandidate.registeredVerticesAt G
      (priorLadder G a prior) (priorRequest G hkappa a prior)
        delta.1 beta.1 gamma.1

theorem mk_weakSplitTripleEntry_le (G : DWeb V)
    {kappa : Cardinal.{u}} (hkappa : kappa.IsRegular)
    (a : RegularCardinal.Stage kappa)
    (prior : ∀ b : RegularCardinal.Stage kappa,
      b < a → RegularRows.CausalState kappa V)
    (delta beta gamma : Set.Iio a) :
    #(weakSplitTripleEntry G hkappa.aleph0_le a prior
      delta beta gamma) ≤ kappa := by
  exact (Cardinal.mk_union_le _ _).trans
    (Cardinal.add_le_of_le hkappa.aleph0_le
      (mk_tripleEntry_le G hkappa a prior delta beta gamma)
      (RegularWeakSplitCandidate.mk_registeredVerticesAt_le
        hkappa.aleph0_le G (priorLadder G a prior)
          (priorRequest G hkappa.aleph0_le a prior)
            delta.1 beta.1 gamma.1))

/-- The source-shaped causal rule with weak split coordinates registered
at every triple owner. -/
noncomputable def weakSplitRowRule (G : DWeb V)
    {kappa : Cardinal.{u}}
    (hkappa : kappa.IsRegular) (hkappaUncountable : aleph0 < kappa)
    (hG : G.IsNormalized)
    (hlower : UniversalCardinalInductionBelow V kappa)
    (F : Set G.DPath) (hF : G.IsWarp F)
    (base : Set V) (hbase : #base ≤ kappa) :
    RegularRows.CausalRowRule kappa V :=
  RegularRows.ofRegistrationTables hkappa.aleph0_le base hbase
    (weakSplitPairEntry G hlower hkappaUncountable F)
    (weakSplitTripleEntry G hkappa.aleph0_le)
    (mk_weakSplitPairEntry_le G hkappa hkappaUncountable hG hlower F hF)
    (mk_weakSplitTripleEntry_le G hkappa)

/-- Every pair-owned entry is retained by the enhanced row rule. -/
theorem pairEntry_subset_weakSplitRowRule_carrier
    (G : DWeb V) {kappa : Cardinal.{u}}
    (hkappa : kappa.IsRegular) (hkappaUncountable : aleph0 < kappa)
    (hG : G.IsNormalized)
    (hlower : UniversalCardinalInductionBelow V kappa)
    (F : Set G.DPath) (hF : G.IsWarp F)
    (base : Set V) (hbase : #base ≤ kappa)
    (a : RegularCardinal.Stage kappa) (delta gamma : Set.Iio a) :
    let Q := weakSplitRowRule G hkappa hkappaUncountable hG hlower
      F hF base hbase
    pairEntry G hlower hkappaUncountable F a
        (fun b _hba => Q.state hkappa.aleph0_le b) delta gamma ⊆
      (Q.rowSystem hkappa.aleph0_le).carrier := by
  dsimp only
  let Q := weakSplitRowRule G hkappa hkappaUncountable hG hlower
    F hF base hbase
  have hregistered : pairEntry G hlower hkappaUncountable F a
      (fun b _hba => Q.state hkappa.aleph0_le b) delta gamma ⊆
      RegularRows.pairRegistrations a
        (weakSplitPairEntry G hlower hkappaUncountable F a
          (fun b _hba => Q.state hkappa.aleph0_le b)) :=
    fun _ hx => RegularRows.pair_entry_subset_registrations a
      (weakSplitPairEntry G hlower hkappaUncountable F a
        (fun b _hba => Q.state hkappa.aleph0_le b)) delta gamma
      (Set.mem_union_left _ hx)
  have hrow : pairEntry G hlower hkappaUncountable F a
      (fun b _hba => Q.state hkappa.aleph0_le b) delta gamma ⊆
      (Q.state hkappa.aleph0_le a).row := by
    rw [RegularRows.CausalRowRule.state_row_eq]
    change _ ⊆
      (base ∪ RegularRows.pairRegistrations a
        (weakSplitPairEntry G hlower hkappaUncountable F a
          (fun b _hba => Q.state hkappa.aleph0_le b))) ∪
        RegularRows.tripleRegistrations a
          (weakSplitTripleEntry G hkappa.aleph0_le a
            (fun b _hba => Q.state hkappa.aleph0_le b))
    exact hregistered.trans
      (Set.subset_union_right.trans Set.subset_union_left)
  exact hrow.trans
    ((Q.rowSystem hkappa.aleph0_le).row_subset_carrier a)

/-- The combined half-way height/selected-carrier coordinate is retained by
the enhanced weak row. -/
theorem registrationAt_subset_weakSplitRowRule_carrier
    (G : DWeb V) {kappa : Cardinal.{u}}
    (hkappa : kappa.IsRegular) (hkappaUncountable : aleph0 < kappa)
    (hG : G.IsNormalized)
    (hlower : UniversalCardinalInductionBelow V kappa)
    (F : Set G.DPath) (hF : G.IsWarp F)
    (base : Set V) (hbase : #base ≤ kappa)
    (a : RegularCardinal.Stage kappa) (delta gamma : Set.Iio a) :
    let Q := weakSplitRowRule G hkappa hkappaUncountable hG hlower
      F hF base hbase
    RegularWeakHalfwayRegistration.registrationAt hlower
        hkappaUncountable
        (priorLadder G a (fun b _hba => Q.state hkappa.aleph0_le b))
        (priorRequest G hkappa.aleph0_le a
          (fun b _hba => Q.state hkappa.aleph0_le b))
        delta.1 gamma.1 ⊆
      (Q.rowSystem hkappa.aleph0_le).carrier := by
  dsimp only
  let Q := weakSplitRowRule G hkappa hkappaUncountable hG hlower
    F hF base hbase
  have hregistered :
      RegularWeakHalfwayRegistration.registrationAt hlower
          hkappaUncountable
          (priorLadder G a (fun b _hba => Q.state hkappa.aleph0_le b))
          (priorRequest G hkappa.aleph0_le a
            (fun b _hba => Q.state hkappa.aleph0_le b))
          delta.1 gamma.1 ⊆
        RegularRows.pairRegistrations a
          (weakSplitPairEntry G hlower hkappaUncountable F a
            (fun b _hba => Q.state hkappa.aleph0_le b)) :=
    fun _ hx => RegularRows.pair_entry_subset_registrations a
      (weakSplitPairEntry G hlower hkappaUncountable F a
        (fun b _hba => Q.state hkappa.aleph0_le b)) delta gamma
      (Set.mem_union_right _ hx)
  have hrow :
      RegularWeakHalfwayRegistration.registrationAt hlower
          hkappaUncountable
          (priorLadder G a (fun b _hba => Q.state hkappa.aleph0_le b))
          (priorRequest G hkappa.aleph0_le a
            (fun b _hba => Q.state hkappa.aleph0_le b))
          delta.1 gamma.1 ⊆
        (Q.state hkappa.aleph0_le a).row := by
    rw [RegularRows.CausalRowRule.state_row_eq]
    change _ ⊆
      (base ∪ RegularRows.pairRegistrations a
        (weakSplitPairEntry G hlower hkappaUncountable F a
          (fun b _hba => Q.state hkappa.aleph0_le b))) ∪
        RegularRows.tripleRegistrations a
          (weakSplitTripleEntry G hkappa.aleph0_le a
            (fun b _hba => Q.state hkappa.aleph0_le b))
    exact hregistered.trans
      (Set.subset_union_right.trans Set.subset_union_left)
  exact hrow.trans
    ((Q.rowSystem hkappa.aleph0_le).row_subset_carrier a)

/-- The fixed base belongs to the enhanced causal carrier. -/
theorem base_subset_weakSplitRowRule_carrier
    (G : DWeb V) {kappa : Cardinal.{u}}
    (hkappa : kappa.IsRegular) (hkappaUncountable : aleph0 < kappa)
    (hG : G.IsNormalized)
    (hlower : UniversalCardinalInductionBelow V kappa)
    (F : Set G.DPath) (hF : G.IsWarp F)
    (base : Set V) (hbase : #base ≤ kappa) :
    let Q := weakSplitRowRule G hkappa hkappaUncountable hG hlower
      F hF base hbase
    base ⊆ (Q.rowSystem hkappa.aleph0_le).carrier := by
  dsimp only
  let Q := weakSplitRowRule G hkappa hkappaUncountable hG hlower
    F hF base hbase
  let a := firstStage hkappaUncountable
  have hrow : base ⊆ (Q.state hkappa.aleph0_le a).row := by
    rw [RegularRows.CausalRowRule.state_row_eq]
    exact Set.subset_union_left.trans Set.subset_union_left
  exact hrow.trans
    ((Q.rowSystem hkappa.aleph0_le).row_subset_carrier a)

/-- The pair registration also closes the enhanced carrier under the old
complementary linkage. -/
theorem weakSplitRowCarrier_registersOldLinkage
    (G : DWeb V) {kappa : Cardinal.{u}}
    (hkappa : kappa.IsRegular) (hkappaUncountable : aleph0 < kappa)
    (hG : G.IsNormalized)
    (hlower : UniversalCardinalInductionBelow V kappa)
    (F : Set G.DPath) (hF : G.IsWarp F)
    (base : Set V) (hbase : #base ≤ kappa) :
    let Q := weakSplitRowRule G hkappa hkappaUncountable hG hlower
      F hF base hbase
    let R := Q.rowSystem hkappa.aleph0_le
    ∀ i, G.vertexSet (RegularExtension.pathsMeeting G F (R.row i)) ⊆
      R.carrier := by
  dsimp only
  let Q := weakSplitRowRule G hkappa hkappaUncountable hG hlower
    F hF base hbase
  let R := Q.rowSystem hkappa.aleph0_le
  let gamma := firstStage hkappaUncountable
  intro i
  change G.vertexSet
      (RegularExtension.pathsMeeting G F
        (Q.state hkappa.aleph0_le i).row) ⊆ R.carrier
  apply (RegularExtension.vertexSet_pathsMeeting_left_subset_twoWarpRowRegistration
    G F ((G.canonicalLadderCore kappa
      (Q.preferred hkappa.aleph0_le)).warpAt gamma)
        (Q.state hkappa.aleph0_le i).row).trans
  let owner := ownerStage hkappa.aleph0_le i gamma
  have hi : i < owner := left_lt_ownerStage hkappa.aleph0_le i gamma
  have hgamma : gamma < owner :=
    right_lt_ownerStage hkappa.aleph0_le i gamma
  have hpref : ∀ b, b < gamma →
      preferredOfPrior owner
          (fun c _hca => Q.state hkappa.aleph0_le c) b =
        Q.preferred hkappa.aleph0_le b := by
    intro b hb
    simp only [preferredOfPrior, dif_pos (hb.trans hgamma),
      RegularRows.CausalRowRule.preferred]
  have hwarp :
      (priorLadder G owner
        (fun c _hca => Q.state hkappa.aleph0_le c)).warpAt gamma =
      (G.canonicalLadderCore kappa
        (Q.preferred hkappa.aleph0_le)).warpAt gamma := by
    exact LadderPrefix.canonicalLadderCore_warpAt_eq_of_forall_lt
      G _ _ gamma hpref
  have hentry := pairEntry_subset_weakSplitRowRule_carrier G hkappa
    hkappaUncountable hG hlower F hF base hbase owner
      (⟨i, hi⟩ : Set.Iio owner) (⟨gamma, hgamma⟩ : Set.Iio owner)
  intro x hx
  apply hentry
  apply Set.mem_union_left
  rw [← regularExtension_twoWarpRowRegistration_eq]
  rw [hwarp]
  exact hx

/-- Every fixed-old-warp/current-ladder-stage closure of an actual enhanced
row was pre-registered at a later causal owner stage. -/
theorem twoWarpRowRegistration_subset_weakSplitRowRule_carrier
    (G : DWeb V) {kappa : Cardinal.{u}}
    (hkappa : kappa.IsRegular) (hkappaUncountable : aleph0 < kappa)
    (hG : G.IsNormalized)
    (hlower : UniversalCardinalInductionBelow V kappa)
    (F : Set G.DPath) (hF : G.IsWarp F)
    (base : Set V) (hbase : #base ≤ kappa)
    (i gamma : RegularCardinal.Stage kappa) :
    let Q := weakSplitRowRule G hkappa hkappaUncountable hG hlower
      F hF base hbase
    RegularExtension.twoWarpRowRegistration G F
        ((G.canonicalLadderCore kappa
          (Q.preferred hkappa.aleph0_le)).warpAt gamma)
        (Q.state hkappa.aleph0_le i).row ⊆
      (Q.rowSystem hkappa.aleph0_le).carrier := by
  dsimp only
  let Q := weakSplitRowRule G hkappa hkappaUncountable hG hlower
    F hF base hbase
  let owner := ownerStage hkappa.aleph0_le i gamma
  have hi : i < owner := left_lt_ownerStage hkappa.aleph0_le i gamma
  have hgamma : gamma < owner :=
    right_lt_ownerStage hkappa.aleph0_le i gamma
  have hpref : ∀ b, b < gamma →
      preferredOfPrior owner
          (fun c _hca ↦ Q.state hkappa.aleph0_le c) b =
        Q.preferred hkappa.aleph0_le b := by
    intro b hb
    simp only [preferredOfPrior, dif_pos (hb.trans hgamma),
      RegularRows.CausalRowRule.preferred]
  have hwarp :
      (priorLadder G owner
        (fun c _hca ↦ Q.state hkappa.aleph0_le c)).warpAt gamma =
      (G.canonicalLadderCore kappa
        (Q.preferred hkappa.aleph0_le)).warpAt gamma := by
    exact LadderPrefix.canonicalLadderCore_warpAt_eq_of_forall_lt
      G _ _ gamma hpref
  have hentry := pairEntry_subset_weakSplitRowRule_carrier G hkappa
    hkappaUncountable hG hlower F hF base hbase owner
      (⟨i, hi⟩ : Set.Iio owner) (⟨gamma, hgamma⟩ : Set.Iio owner)
  intro x hx
  apply hentry
  apply Set.mem_union_left
  rw [← regularExtension_twoWarpRowRegistration_eq]
  rw [hwarp]
  exact hx

/-- Adding the weak split triple registrations does not affect the pair-owned
closure argument.  Hence the enhanced carrier is closed under the limiting
canonical ladder warp exactly as for the original causal rule. -/
theorem weakSplitRowCarrier_isLimitWarpClosed
    (G : DWeb V) {kappa : Cardinal.{u}}
    (hkappa : kappa.IsRegular) (hkappaUncountable : aleph0 < kappa)
    (hG : G.IsNormalized)
    (hlower : UniversalCardinalInductionBelow V kappa)
    (F : Set G.DPath) (hF : G.IsWarp F)
    (base : Set V) (hbase : #base ≤ kappa) :
    let Q := weakSplitRowRule G hkappa hkappaUncountable hG hlower
      F hF base hbase
    let R := Q.rowSystem hkappa.aleph0_le
    let L := DWeb.KappaLadder.canonicalLadder G kappa
      (Q.preferred hkappa.aleph0_le)
    SliceSplice.IsLimitWarpClosed G L R.carrier := by
  dsimp only
  let Q := weakSplitRowRule G hkappa hkappaUncountable hG hlower
    F hF base hbase
  let R := Q.rowSystem hkappa.aleph0_le
  let L := DWeb.KappaLadder.canonicalLadder G kappa
    (Q.preferred hkappa.aleph0_le)
  have hNoEnter : G.NoEdgeEnters G.source := by
    intro x y hxy hy
    exact (hG hxy).1 hy
  have hsplit : L.IsSplitLegal :=
    DWeb.KappaLadder.canonicalLadder_isSplitLegal
      (Q.preferred hkappa.aleph0_le) hkappa hkappaUncountable hNoEnter
  have hgeometry : SliceSpliceConstructor.SpliceLadderGeometry G L :=
    ⟨hsplit.regular, hsplit.initialStage, hsplit.limitStages,
      hsplit.warpStages, hsplit.frontiersEssential,
      hsplit.frontierChronology, hsplit.strictFrontierChronology⟩
  change SliceSplice.IsLimitWarpClosed G L R.carrier
  apply RegularExtension.isLimitWarpClosed_of_rowRegistrations G hgeometry R
  intro i a
  change G.vertexSet
      (RegularExtension.pathsMeeting G (L.warpAt a)
        (Q.state hkappa.aleph0_le i).row) ⊆ R.carrier
  exact
    (RegularExtension.vertexSet_pathsMeeting_right_subset_twoWarpRowRegistration
      G F (L.warpAt a) (Q.state hkappa.aleph0_le i).row).trans
        (twoWarpRowRegistration_subset_weakSplitRowRule_carrier G hkappa
          hkappaUncountable hG hlower F hF base hbase i a)

/-- A weak split registration is literally present at its triple owner and
hence in the final carrier. -/
theorem registeredVerticesAt_subset_weakSplitRowRule_carrier
    (G : DWeb V) {kappa : Cardinal.{u}}
    (hkappa : kappa.IsRegular) (hkappaUncountable : aleph0 < kappa)
    (hG : G.IsNormalized)
    (hlower : UniversalCardinalInductionBelow V kappa)
    (F : Set G.DPath) (hF : G.IsWarp F)
    (base : Set V) (hbase : #base ≤ kappa)
    (delta beta gamma : RegularCardinal.Stage kappa) :
    let Q := weakSplitRowRule G hkappa hkappaUncountable hG hlower
      F hF base hbase
    let L := G.canonicalLadderCore kappa (Q.preferred hkappa.aleph0_le)
    RegularWeakSplitCandidate.registeredVerticesAt G L
        (finalRequest G Q hkappa.aleph0_le) delta beta gamma ⊆
      (Q.rowSystem hkappa.aleph0_le).carrier := by
  dsimp only
  let Q := weakSplitRowRule G hkappa hkappaUncountable hG hlower
    F hF base hbase
  let middle := ownerStage hkappa.aleph0_le delta beta
  let owner := ownerStage hkappa.aleph0_le middle gamma
  have hmiddle : middle < owner :=
    left_lt_ownerStage hkappa.aleph0_le middle gamma
  have hdelta : delta < owner :=
    (left_lt_ownerStage hkappa.aleph0_le delta beta).trans hmiddle
  have hbeta : beta < owner :=
    (right_lt_ownerStage hkappa.aleph0_le delta beta).trans hmiddle
  have hgamma : gamma < owner :=
    right_lt_ownerStage hkappa.aleph0_le middle gamma
  let prior := fun c (_hca : c < owner) ↦ Q.state hkappa.aleph0_le c
  let Lprior := priorLadder G owner prior
  let Lfinal := G.canonicalLadderCore kappa
    (Q.preferred hkappa.aleph0_le)
  have hpref (a : RegularCardinal.Stage kappa) (ha : a < owner) :
      ∀ b, b < a →
        preferredOfPrior owner prior b = Q.preferred hkappa.aleph0_le b := by
    intro b hb
    simp only [preferredOfPrior, prior, dif_pos (hb.trans ha),
      RegularRows.CausalRowRule.preferred]
  have hwarpDelta : Lprior.warpAt delta = Lfinal.warpAt delta :=
    LadderPrefix.canonicalLadderCore_warpAt_eq_of_forall_lt
      G _ _ delta (hpref delta hdelta)
  have hwarpBeta : Lprior.warpAt beta = Lfinal.warpAt beta :=
    LadderPrefix.canonicalLadderCore_warpAt_eq_of_forall_lt
      G _ _ beta (hpref beta hbeta)
  have hfrontierDelta : Lprior.frontier delta = Lfinal.frontier delta :=
    LadderPrefix.canonicalLadderCore_frontier_eq_of_forall_lt
      G _ _ delta (hpref delta hdelta)
  have hfrontierBeta : Lprior.frontier beta = Lfinal.frontier beta :=
    LadderPrefix.canonicalLadderCore_frontier_eq_of_forall_lt
      G _ _ beta (hpref beta hbeta)
  have hrequest : priorRequest G hkappa.aleph0_le owner prior delta gamma =
      finalRequest G Q hkappa.aleph0_le delta gamma :=
    RegularExtension.priorRequest_eq_finalRequest_of_lt
      (G := G) Q hkappa.aleph0_le hdelta hgamma
  have hcoordinate :=
    RegularWeakSplitCandidate.registeredVerticesAt_congr_stageData
      hwarpDelta hwarpBeta hfrontierDelta hfrontierBeta hrequest
  have hentry : weakSplitTripleEntry G hkappa.aleph0_le owner prior
      (⟨delta, hdelta⟩ : Set.Iio owner)
      (⟨beta, hbeta⟩ : Set.Iio owner)
      (⟨gamma, hgamma⟩ : Set.Iio owner) ⊆
      (Q.rowSystem hkappa.aleph0_le).carrier := by
    have hregistered : weakSplitTripleEntry G hkappa.aleph0_le owner prior
        (⟨delta, hdelta⟩ : Set.Iio owner)
        (⟨beta, hbeta⟩ : Set.Iio owner)
        (⟨gamma, hgamma⟩ : Set.Iio owner) ⊆
        RegularRows.tripleRegistrations owner
          (weakSplitTripleEntry G hkappa.aleph0_le owner prior) :=
      RegularRows.triple_entry_subset_registrations owner _ _ _ _
    have hrow : weakSplitTripleEntry G hkappa.aleph0_le owner prior
        (⟨delta, hdelta⟩ : Set.Iio owner)
        (⟨beta, hbeta⟩ : Set.Iio owner)
        (⟨gamma, hgamma⟩ : Set.Iio owner) ⊆
        (Q.state hkappa.aleph0_le owner).row := by
      intro x hx
      have hx' := hregistered hx
      have hx'' : x ∈ RegularRows.tripleRegistrations owner
          (weakSplitTripleEntry G hkappa.aleph0_le owner
            (fun c _hca ↦ Q.state hkappa.aleph0_le c)) := by
        simpa only [prior] using hx'
      rw [RegularRows.CausalRowRule.state_row_eq]
      change x ∈
        (base ∪ RegularRows.pairRegistrations owner
          (weakSplitPairEntry G hlower hkappaUncountable F owner
            (fun b _hba ↦ Q.state hkappa.aleph0_le b))) ∪
          RegularRows.tripleRegistrations owner
            (weakSplitTripleEntry G hkappa.aleph0_le owner
              (fun b _hba ↦ Q.state hkappa.aleph0_le b))
      exact Set.mem_union_right _ hx''
    exact hrow.trans
      ((Q.rowSystem hkappa.aleph0_le).row_subset_carrier owner)
  intro x hx
  apply hentry
  apply Set.mem_union_right
  change x ∈ RegularWeakSplitCandidate.registeredVerticesAt G Lprior
    (priorRequest G hkappa.aleph0_le owner prior) delta beta gamma
  rw [hcoordinate]
  exact hx

/-- Every chosen target-track vertex at a final coordinate is closed in the
enhanced causal carrier. -/
theorem chosenWeakSplitTarget_vertices_subset_carrier
    (G : DWeb V) {kappa : Cardinal.{u}}
    (hkappa : kappa.IsRegular) (hkappaUncountable : aleph0 < kappa)
    (hG : G.IsNormalized)
    (hlower : UniversalCardinalInductionBelow V kappa)
    (F : Set G.DPath) (hF : G.IsWarp F)
    (base : Set V) (hbase : #base ≤ kappa)
    (delta beta gamma : RegularCardinal.Stage kappa) :
    let Q := weakSplitRowRule G hkappa hkappaUncountable hG hlower
      F hF base hbase
    let L := G.canonicalLadderCore kappa (Q.preferred hkappa.aleph0_le)
    G.vertexSet
        (RegularWeakSplitCandidate.chosenWeakSplitCandidate
          G L (finalRequest G Q hkappa.aleph0_le)
            delta beta gamma).target ⊆
      (Q.rowSystem hkappa.aleph0_le).carrier := by
  dsimp only
  exact (RegularWeakSplitCandidate.chosen_target_vertices_subset_registered
    G _ _ delta beta gamma).trans
      (registeredVerticesAt_subset_weakSplitRowRule_carrier
        G hkappa hkappaUncountable hG hlower F hF base hbase
          delta beta gamma)

/-- Every chosen clean maverick vertex at a final coordinate is closed in
the enhanced causal carrier. -/
theorem chosenWeakSplitCleanMaverick_vertices_subset_carrier
    (G : DWeb V) {kappa : Cardinal.{u}}
    (hkappa : kappa.IsRegular) (hkappaUncountable : aleph0 < kappa)
    (hG : G.IsNormalized)
    (hlower : UniversalCardinalInductionBelow V kappa)
    (F : Set G.DPath) (hF : G.IsWarp F)
    (base : Set V) (hbase : #base ≤ kappa)
    (delta beta gamma : RegularCardinal.Stage kappa) :
    let Q := weakSplitRowRule G hkappa hkappaUncountable hG hlower
      F hF base hbase
    let L := G.canonicalLadderCore kappa (Q.preferred hkappa.aleph0_le)
    G.vertexSet (ControlledSlices.sliceMavericks G (L.warpAt beta)
        (RegularWeakSplitCandidate.chosenWeakSplitCandidate
          G L (finalRequest G Q hkappa.aleph0_le)
            delta beta gamma).clean) ⊆
      (Q.rowSystem hkappa.aleph0_le).carrier := by
  dsimp only
  exact
    (RegularWeakSplitCandidate.chosen_cleanMaverick_vertices_subset_registered
      G _ _ delta beta gamma).trans
        (registeredVerticesAt_subset_weakSplitRowRule_carrier
          G hkappa hkappaUncountable hG hlower F hF base hbase
            delta beta gamma)

end RegularRows.CausalRegular
end CardinalInduction
end Erdos599
