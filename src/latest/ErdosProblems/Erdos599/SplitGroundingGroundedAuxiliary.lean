/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingTargetPureChronology

/-!
# The grounded auxiliary for split legality

After the sound stationary split has selected the `phiGround` branch, the
Section 8.22 auxiliary must use exactly the grounded records.  This restores
the strict source chronology used in Assertion 8.19 while retaining the
successor-normalized `IsSplitLegal` ladder; no conversion to legacy
`IsLegal` is involved.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace DWeb
namespace KappaLadder

open _root_.Erdos599.DirectedPath

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

/-- The represented grounded ray, with split legality used only for its
bookkeeping certificate. -/
noncomputable def splitGroundedInfinitePath
    (L : Gamma.KappaLadder kappa) (_hL : L.IsSplitLegal)
    (i : L.groundedInfiniteRecords) : Gamma.DPath :=
  i.1

theorem splitGroundedInfinitePath_isRay
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitLegal)
    (i : L.groundedInfiniteRecords) :
    ∃ r : Ray Gamma.graph, L.splitGroundedInfinitePath hL i = .inr r := by
  obtain ⟨a, ha, hchosen⟩ := i.2
  obtain ⟨p, hp, hpRay⟩ :=
    L.bookkeeping.chosen_isRay_of_mem_phiInfinite
      hL.validBookkeeping ha.2
  have hip : i.1 = p := Option.some.inj (hchosen.symm.trans hp)
  rw [show L.splitGroundedInfinitePath hL i = p by
    simpa only [splitGroundedInfinitePath] using hip]
  rcases p with p | r
  · change (some p.finish : Option V) = none at hpRay
    cases hpRay
  · exact ⟨r, rfl⟩

/-- The literal grounded-record auxiliary under split legality. -/
noncomputable def splitGroundedPopularAuxiliaryInput
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitLegal) :
    PopularAuxiliary.Input Gamma L.groundedInfiniteRecords where
  ladder := ⟨L.limitWarp, hL.warpStages (Ladder.finalStage kappa)⟩
  finiteSource := L.groundedFiniteTerminalSet
  markerSet := L.markerSet
  proxyPath := L.splitGroundedInfinitePath hL
  proxy_isRay := L.splitGroundedInfinitePath_isRay hL

/-- Split legality suffices for the recorded-stage equality used by finite
grounded terminals. -/
theorem finiteTerminalStage_mem_phiGround_of_split
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitLegal)
    (x : L.groundedFiniteTerminalSet) :
    L.finiteTerminalIndex x ∈ L.phiGround := by
  obtain ⟨a, ha, p, hchosen, hterminal⟩ := x.2
  have hstage :
      L.finiteTerminalStage
          ⟨x.1, L.groundedFiniteTerminalSet_subset_finiteTerminalSet x.2⟩ = a :=
    L.finiteTerminalStage_eq_of_split hL hchosen hterminal
      (L.groundedFiniteTerminalSet_subset_finiteTerminalSet x.2)
  simpa only [finiteTerminalIndex, hstage] using ha.1

theorem groundedInfiniteStage_eq_of_split
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitLegal)
    (i : L.groundedInfiniteRecords) {a : Ladder.Stage kappa}
    (ha : L.chosen a = some i.1) :
    L.groundedInfiniteStage i = a :=
  L.bookkeeping.chosen_stage_unique hL.validBookkeeping
    (L.groundedInfiniteStage_spec i).2 ha

/-- The target marker chronology for the grounded split auxiliary. -/
noncomputable def splitGroundedTargetMarkerIndex
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitLegal) :
    (L.splitGroundedPopularAuxiliaryInput hL).targetMarkers ↪
      Stationary.Below kappa where
  toFun y := L.markerStage ⟨y.1, y.2.1⟩
  inj' := by
    intro y z hyz
    apply Subtype.ext
    exact congrArg (fun w : L.markerSet ↦ w.1)
      (L.markerStage.injective hyz)

/-- The grounded record stage attached to one source of the grounded split
auxiliary. -/
noncomputable def splitGroundedAuxiliarySourceIndex
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitLegal) :
    (L.splitGroundedPopularAuxiliaryInput hL).lambda.source →
      Stationary.Below kappa :=
  fun x ↦ match h : x.1 with
    | .old a => L.finiteTerminalIndex ⟨a, by
        have hx := h ▸ x.2
        exact ((L.splitGroundedPopularAuxiliaryInput hL)
          |>.mem_lambda_source_old a).1 hx⟩
    | .edge a b => False.elim <| by
        have hx := h ▸ x.2
        exact (L.splitGroundedPopularAuxiliaryInput hL)
          |>.not_mem_lambda_source_edge a b hx
    | .proxy i => L.groundedInfiniteStage i

theorem splitGroundedAuxiliarySourceIndex_injective
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitLegal) :
    Function.Injective (L.splitGroundedAuxiliarySourceIndex hL) := by
  let I := L.splitGroundedPopularAuxiliaryInput hL
  rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
  apply Subtype.ext
  cases x with
  | old a =>
      cases y with
      | old b =>
          let xa : L.groundedFiniteTerminalSet :=
            ⟨a, (I.mem_lambda_source_old a).1 hx⟩
          let yb : L.groundedFiniteTerminalSet :=
            ⟨b, (I.mem_lambda_source_old b).1 hy⟩
          change L.finiteTerminalIndex xa = L.finiteTerminalIndex yb at hxy
          exact congrArg PopularAuxiliary.Input.LambdaVertex.old
            (congrArg Subtype.val (L.finiteTerminalIndex_injective hxy))
      | edge c d => exact False.elim (I.not_mem_lambda_source_edge c d hy)
      | proxy i =>
          let xa : L.groundedFiniteTerminalSet :=
            ⟨a, (I.mem_lambda_source_old a).1 hx⟩
          let xa' : L.finiteTerminalSet :=
            ⟨xa.1, L.groundedFiniteTerminalSet_subset_finiteTerminalSet xa.2⟩
          change L.finiteTerminalStage xa' = L.groundedInfiniteStage i at hxy
          exact False.elim ((L.finiteTerminalStage_spec xa').1.2
            (hxy ▸ (L.groundedInfiniteStage_spec i).1.2))
  | edge a b => exact False.elim (I.not_mem_lambda_source_edge a b hx)
  | proxy i =>
      cases y with
      | old b =>
          let yb : L.groundedFiniteTerminalSet :=
            ⟨b, (I.mem_lambda_source_old b).1 hy⟩
          let yb' : L.finiteTerminalSet :=
            ⟨yb.1, L.groundedFiniteTerminalSet_subset_finiteTerminalSet yb.2⟩
          change L.groundedInfiniteStage i = L.finiteTerminalStage yb' at hxy
          exact False.elim ((L.finiteTerminalStage_spec yb').1.2
            (hxy.symm ▸ (L.groundedInfiniteStage_spec i).1.2))
      | edge c d => exact False.elim (I.not_mem_lambda_source_edge c d hy)
      | proxy j =>
          change L.groundedInfiniteStage i = L.groundedInfiniteStage j at hxy
          apply congrArg PopularAuxiliary.Input.LambdaVertex.proxy
          apply Subtype.ext
          have hi := (L.groundedInfiniteStage_spec i).2
          have hj := (L.groundedInfiniteStage_spec j).2
          rw [hxy] at hi
          exact Option.some.inj (hi.symm.trans hj)

theorem splitGroundedAuxiliarySourceIndex_eq_sourceIndex
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitLegal) :
    L.splitGroundedAuxiliarySourceIndex hL =
      (L.splitGroundedPopularAuxiliaryInput hL).sourceIndex
        L.finiteTerminalIndex L.groundedInfiniteStage := by
  funext x
  apply Subtype.ext
  rcases x with ⟨x, hx⟩
  cases x <;> rfl

/-- Every grounded obstruction stage is represented by a source of the
grounded split auxiliary. -/
theorem splitGroundedAuxiliarySourceRange_isStationary
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (hground : Stationary.IsStationaryBelow kappa L.phiGround) :
    Stationary.IsStationaryBelow kappa
      (Set.range (L.splitGroundedAuxiliarySourceIndex hL.legal)) := by
  let I := L.splitGroundedPopularAuxiliaryInput hL.legal
  apply hground.mono
  intro a ha
  obtain ⟨p, hchosen, hpSource⟩ := ha
  have haPhi : a ∈ L.phi :=
    (L.bookkeeping.mem_phi_iff_exists_chosen
      hL.legal.validBookkeeping).2 ⟨p, hchosen⟩
  rcases p with p | r
  · have haFinite : a ∈ L.phiFinite := by
      refine ⟨haPhi, ?_⟩
      intro haInfinite
      obtain ⟨q, hq, hqRay⟩ :=
        L.bookkeeping.chosen_isRay_of_mem_phiInfinite
          hL.legal.validBookkeeping haInfinite
      have hqp : q = (.inl p : Gamma.DPath) :=
        Option.some.inj (hq.symm.trans hchosen)
      subst q
      change (some p.finish : Option V) = none at hqRay
      cases hqRay
    let x : L.groundedFiniteTerminalSet :=
      ⟨p.finish, a, ⟨⟨.inl p, hchosen, hpSource⟩, haFinite⟩,
        .inl p, hchosen, rfl⟩
    let s : I.lambda.source :=
      ⟨.old x.1, (I.mem_lambda_source_old x.1).2 x.2⟩
    refine ⟨s, ?_⟩
    change L.finiteTerminalIndex x = a
    exact L.finiteTerminalStage_eq_of_split hL.legal hchosen rfl
      (L.groundedFiniteTerminalSet_subset_finiteTerminalSet x.2)
  · have haInfinite : a ∈ L.phiInfinite := by
      refine ⟨haPhi, .inr r, ?_, rfl⟩
      exact L.bookkeeping.chosen_mem_available
        hL.legal.validBookkeeping hchosen
    let i : L.groundedInfiniteRecords :=
      ⟨.inr r, ⟨a, ⟨⟨.inr r, hchosen, hpSource⟩, haInfinite⟩,
        hchosen⟩⟩
    let s : I.lambda.source := ⟨.proxy i, I.mem_lambda_source_proxy i⟩
    refine ⟨s, ?_⟩
    change L.groundedInfiniteStage i = a
    exact L.groundedInfiniteStage_eq_of_split hL.legal i hchosen

/-- The grounded split auxiliary indexed by its genuine record stages. -/
noncomputable def splitGroundedPopularAuxiliaryIndexed
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (hground : Stationary.IsStationaryBelow kappa L.phiGround) :
    Popular.KappaIndexed
      (L.splitGroundedPopularAuxiliaryInput hL.legal).lambda kappa where
  regular := hL.legal.regular
  uncountable := hL.legal.uncountable
  f := (L.splitGroundedPopularAuxiliaryInput hL.legal).sourceIndex
    L.finiteTerminalIndex L.groundedInfiniteStage
  g := (L.splitGroundedPopularAuxiliaryInput hL.legal).targetIndex
    (L.splitGroundedTargetMarkerIndex hL.legal)
  f_range_stationary := by
    rw [← L.splitGroundedAuxiliarySourceIndex_eq_sourceIndex hL.legal]
    exact L.splitGroundedAuxiliarySourceRange_isStationary hL hground

theorem splitGroundedPopularAuxiliaryIndexed_sourceIndexed
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (hground : Stationary.IsStationaryBelow kappa L.phiGround) :
    (L.splitGroundedPopularAuxiliaryIndexed hL hground).SourceIndexed := by
  change Function.Injective
    ((L.splitGroundedPopularAuxiliaryInput hL.legal).sourceIndex
      L.finiteTerminalIndex L.groundedInfiniteStage)
  rw [← L.splitGroundedAuxiliarySourceIndex_eq_sourceIndex hL.legal]
  exact L.splitGroundedAuxiliarySourceIndex_injective hL.legal

/-- The grounded split auxiliary has the standard strong-target/popular-
separator dichotomy. -/
theorem splitGroundedPopularAuxiliary_strongTarget_or_separator
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (hground : Stationary.IsStationaryBelow kappa L.phiGround) :
    Popular.IsStronglyPopular
        (L.splitGroundedPopularAuxiliaryIndexed hL hground)
        (L.splitGroundedPopularAuxiliaryInput hL.legal).lambda.target ∨
      Nonempty (Popular.PopularSeparator
        (L.splitGroundedPopularAuxiliaryIndexed hL hground)) := by
  let U := L.splitGroundedPopularAuxiliaryIndexed hL hground
  have hsource : U.SourceBounded :=
    U.sourceBounded_of_sourceIndexed
      (L.splitGroundedPopularAuxiliaryIndexed_sourceIndexed hL hground)
  exact Popular.stronglyPopular_target_or_popularSeparator U hsource

end KappaLadder
end DWeb
end Erdos599
