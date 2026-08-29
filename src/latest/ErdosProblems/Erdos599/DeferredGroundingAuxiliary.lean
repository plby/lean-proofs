/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.DeferredHindranceGrounding
import ErdosProblems.Erdos599.PopularAuxiliary
import ErdosProblems.Erdos599.PopularIndexedDichotomy
import ErdosProblems.Erdos599.PopularSwitching

/-!
# The Section 8 auxiliary for deferred bookkeeping

Every finite or infinite record of `Deferred.phi` is represented.  The
source index therefore has stationary range directly from the deferred
hindrance, while the global pressing-down theorem from
`DeferredHindranceGrounding` shows that every stationary subfamily of
obstruction indices has stationary grounded part.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace DWeb

namespace KappaLadder
namespace Deferred

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

/-- Finite terminals of paths recorded by deferred bookkeeping. -/
def finiteTerminalSet (L : Gamma.KappaLadder kappa) : Set V :=
  {x | ∃ a ∈ phiFinite L, ∃ p : Gamma.DPath,
    L.chosen a = some p ∧ Gamma.terminal? p = some x}

/-- Infinite paths recorded at deferred obstruction stages. -/
abbrev infiniteRecords (L : Gamma.KappaLadder kappa) :=
  {p : Gamma.DPath // ∃ a : Ladder.Stage kappa,
    a ∈ phiInfinite L ∧ L.chosen a = some p}

noncomputable def infinitePath (L : Gamma.KappaLadder kappa)
    (_hlegal : IsDeferredLegal L) (p : infiniteRecords L) : Gamma.DPath :=
  p.1

theorem infinitePath_isRay (L : Gamma.KappaLadder kappa)
    (hlegal : IsDeferredLegal L) (p : infiniteRecords L) :
    ∃ r : _root_.Erdos599.DirectedPath.Ray Gamma.graph,
      infinitePath L hlegal p = .inr r := by
  obtain ⟨a, ha, hchosen⟩ := p.2
  obtain ⟨q, hq, hqRay⟩ :=
    (bookkeeping L).chosen_isRay_of_mem_phiInfinite
      hlegal.validBookkeeping ha
  have hpq : p.1 = q := Option.some.inj (hchosen.symm.trans hq)
  rw [show infinitePath L hlegal p = q by simpa [infinitePath] using hpq]
  rcases q with q | r
  · change (some q.finish : Option V) = none at hqRay
    cases hqRay
  · exact ⟨r, rfl⟩

/-- Literal transformed web representing all deferred records. -/
noncomputable def popularAuxiliaryInput (L : Gamma.KappaLadder kappa)
    (hlegal : IsDeferredLegal L) :
    PopularAuxiliary.Input Gamma (infiniteRecords L) where
  ladder := ⟨L.limitWarp,
    hlegal.warpStages (Ladder.finalStage kappa)⟩
  finiteSource := finiteTerminalSet L
  markerSet := L.markerSet
  proxyPath := infinitePath L hlegal
  proxy_isRay := infinitePath_isRay L hlegal

/-- Two finite deferred records with the same terminal were selected at
the same stage. -/
theorem recordedStage_eq_of_same_terminal
    (L : Gamma.KappaLadder kappa) (hlegal : IsDeferredLegal L)
    {a b : Ladder.Stage kappa} {p q : Gamma.DPath} {x : V}
    (hpa : L.chosen a = some p) (hpx : Gamma.terminal? p = some x)
    (hqb : L.chosen b = some q) (hqx : Gamma.terminal? q = some x) :
    a = b := by
  rcases le_total a b with hab | hba
  · have hpWarp : p ∈ L.successorWarp b :=
      (L.recorded_mem_successor_inessential
        hlegal.recordedPathsPersist hpa hab).1
    have hqWarp : q ∈ L.successorWarp b :=
      (chosen_spec hlegal.validBookkeeping hqb).1.1
    by_cases hpq : p = q
    · subst q
      exact (bookkeeping L).chosen_stage_unique
        hlegal.validBookkeeping hpa hqb
    · exact False.elim <| Set.disjoint_left.1
        (hlegal.warpStages (Ladder.Stage.succExtended b)
          hpWarp hqWarp hpq)
        (Gamma.terminal_mem_support hpx) (Gamma.terminal_mem_support hqx)
  · have hqWarp : q ∈ L.successorWarp a :=
      (L.recorded_mem_successor_inessential
        hlegal.recordedPathsPersist hqb hba).1
    have hpWarp : p ∈ L.successorWarp a :=
      (chosen_spec hlegal.validBookkeeping hpa).1.1
    by_cases hpq : p = q
    · subst q
      exact (bookkeeping L).chosen_stage_unique
        hlegal.validBookkeeping hpa hqb
    · exact False.elim <| Set.disjoint_left.1
        (hlegal.warpStages (Ladder.Stage.succExtended a)
          hpWarp hqWarp hpq)
        (Gamma.terminal_mem_support hpx) (Gamma.terminal_mem_support hqx)

/-- The stage represented by a finite deferred terminal. -/
noncomputable def finiteTerminalStage (L : Gamma.KappaLadder kappa)
    (x : finiteTerminalSet L) : Ladder.Stage kappa :=
  Classical.choose x.2

theorem finiteTerminalStage_spec (L : Gamma.KappaLadder kappa)
    (x : finiteTerminalSet L) :
    finiteTerminalStage L x ∈ phiFinite L ∧
      ∃ p : Gamma.DPath,
        L.chosen (finiteTerminalStage L x) = some p ∧
          Gamma.terminal? p = some x.1 :=
  Classical.choose_spec x.2

theorem finiteTerminalStage_eq (L : Gamma.KappaLadder kappa)
    (hlegal : IsDeferredLegal L) {a : Ladder.Stage kappa}
    {p : Gamma.DPath} {x : V} (hchosen : L.chosen a = some p)
    (hterminal : Gamma.terminal? p = some x)
    (hx : x ∈ finiteTerminalSet L) :
    finiteTerminalStage L ⟨x, hx⟩ = a := by
  obtain ⟨_, q, hq, hqterminal⟩ := finiteTerminalStage_spec L ⟨x, hx⟩
  exact recordedStage_eq_of_same_terminal L hlegal
    hq hqterminal hchosen hterminal

noncomputable def finiteTerminalIndex (L : Gamma.KappaLadder kappa) :
    finiteTerminalSet L → Stationary.Below kappa :=
  finiteTerminalStage L

theorem finiteTerminalIndex_injective (L : Gamma.KappaLadder kappa)
    (_hlegal : IsDeferredLegal L) :
    Function.Injective (finiteTerminalIndex L) := by
  intro x y hxy
  obtain ⟨_, p, hp, hpx⟩ := finiteTerminalStage_spec L x
  obtain ⟨_, q, hq, hqy⟩ := finiteTerminalStage_spec L y
  have hpq : p = q := by
    apply Option.some.inj
    exact hp.symm.trans ((congrArg L.chosen hxy).trans hq)
  apply Subtype.ext
  exact Option.some.inj (hpx.symm.trans (hpq ▸ hqy))

/-- The stage represented by an infinite deferred proxy. -/
noncomputable def infiniteStage (L : Gamma.KappaLadder kappa) :
    infiniteRecords L → Ladder.Stage kappa :=
  fun p ↦ Classical.choose p.2

theorem infiniteStage_spec (L : Gamma.KappaLadder kappa)
    (p : infiniteRecords L) :
    infiniteStage L p ∈ phiInfinite L ∧
      L.chosen (infiniteStage L p) = some p.1 :=
  Classical.choose_spec p.2

theorem infiniteStage_eq (L : Gamma.KappaLadder kappa)
    (hlegal : IsDeferredLegal L) (p : infiniteRecords L)
    {a : Ladder.Stage kappa} (ha : L.chosen a = some p.1) :
    infiniteStage L p = a :=
  (bookkeeping L).chosen_stage_unique hlegal.validBookkeeping
    (infiniteStage_spec L p).2 ha

/-- The target marker stage map for the deferred auxiliary. -/
noncomputable def targetMarkerIndex (L : Gamma.KappaLadder kappa)
    (hlegal : IsDeferredLegal L) :
    (popularAuxiliaryInput L hlegal).targetMarkers ↪
      Stationary.Below kappa where
  toFun y := L.markerStage ⟨y.1, y.2.1⟩
  inj' := by
    intro y z hyz
    apply Subtype.ext
    exact congrArg (fun w : L.markerSet ↦ w.1)
      (L.markerStage.injective hyz)

/-- The obstruction-stage index on sources of the deferred auxiliary. -/
noncomputable def auxiliarySourceIndex
    (L : Gamma.KappaLadder kappa) (hlegal : IsDeferredLegal L) :
    (popularAuxiliaryInput L hlegal).lambda.source →
      Stationary.Below kappa :=
  fun x ↦ match h : x.1 with
    | .old a => finiteTerminalIndex L ⟨a, by
        have hx := h ▸ x.2
        exact ((popularAuxiliaryInput L hlegal)
          |>.mem_lambda_source_old a).1 hx⟩
    | .edge a b => False.elim <| by
        have hx := h ▸ x.2
        exact (popularAuxiliaryInput L hlegal)
          |>.not_mem_lambda_source_edge a b hx
    | .proxy i => infiniteStage L i

theorem auxiliarySourceIndex_injective
    (L : Gamma.KappaLadder kappa) (hlegal : IsDeferredLegal L) :
    Function.Injective (auxiliarySourceIndex L hlegal) := by
  let I := popularAuxiliaryInput L hlegal
  rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
  apply Subtype.ext
  cases x with
  | old a =>
      cases y with
      | old b =>
          let xa : finiteTerminalSet L :=
            ⟨a, (I.mem_lambda_source_old a).1 hx⟩
          let yb : finiteTerminalSet L :=
            ⟨b, (I.mem_lambda_source_old b).1 hy⟩
          change finiteTerminalIndex L xa = finiteTerminalIndex L yb at hxy
          exact congrArg PopularAuxiliary.Input.LambdaVertex.old
            (congrArg Subtype.val
              (finiteTerminalIndex_injective L hlegal hxy))
      | edge c d => exact False.elim (I.not_mem_lambda_source_edge c d hy)
      | proxy i =>
          let xa : finiteTerminalSet L :=
            ⟨a, (I.mem_lambda_source_old a).1 hx⟩
          change finiteTerminalStage L xa = infiniteStage L i at hxy
          exact False.elim ((finiteTerminalStage_spec L xa).1.2
            (hxy ▸ (infiniteStage_spec L i).1))
  | edge a b => exact False.elim (I.not_mem_lambda_source_edge a b hx)
  | proxy i =>
      cases y with
      | old b =>
          let yb : finiteTerminalSet L :=
            ⟨b, (I.mem_lambda_source_old b).1 hy⟩
          change infiniteStage L i = finiteTerminalStage L yb at hxy
          exact False.elim ((finiteTerminalStage_spec L yb).1.2
            (hxy.symm ▸ (infiniteStage_spec L i).1))
      | edge c d => exact False.elim (I.not_mem_lambda_source_edge c d hy)
      | proxy j =>
          change infiniteStage L i = infiniteStage L j at hxy
          apply congrArg PopularAuxiliary.Input.LambdaVertex.proxy
          apply Subtype.ext
          have hi := (infiniteStage_spec L i).2
          have hj := (infiniteStage_spec L j).2
          rw [hxy] at hi
          exact Option.some.inj (hi.symm.trans hj)

/-- Every deferred obstruction stage appears in the source-index range. -/
theorem auxiliarySourceRange_isStationary
    (L : Gamma.KappaLadder kappa) (hL : IsKappaHindrance L) :
    Stationary.IsStationaryBelow kappa
      (Set.range (auxiliarySourceIndex L hL.legal)) := by
  let I := popularAuxiliaryInput L hL.legal
  apply hL.stationary.mono
  intro a ha
  obtain ⟨p, hchosen⟩ :=
    ((bookkeeping L).mem_phi_iff_exists_chosen
      hL.legal.validBookkeeping).1 ha
  rcases p with q | r
  · have haNotInfinite : a ∉ phiInfinite L := by
      intro haInfinite
      obtain ⟨p, hp, hpRay⟩ :=
        (bookkeeping L).chosen_isRay_of_mem_phiInfinite
          hL.legal.validBookkeeping haInfinite
      have hpq : p = (.inl q : Gamma.DPath) :=
        Option.some.inj (hp.symm.trans hchosen)
      subst p
      change (some q.finish : Option V) = none at hpRay
      cases hpRay
    have haFinite : a ∈ phiFinite L := ⟨ha, haNotInfinite⟩
    let x : finiteTerminalSet L :=
      ⟨q.finish, a, haFinite, .inl q, hchosen, rfl⟩
    let s : I.lambda.source :=
      ⟨.old x.1, (I.mem_lambda_source_old x.1).2 x.2⟩
    refine ⟨s, ?_⟩
    change finiteTerminalStage L _ = a
    exact finiteTerminalStage_eq L hL.legal hchosen rfl x.2
  · have haInfinite : a ∈ phiInfinite L := by
      refine ⟨ha, .inr r, ?_, rfl⟩
      exact (bookkeeping L).chosen_mem_available
        hL.legal.validBookkeeping hchosen
    let i : infiniteRecords L :=
      ⟨.inr r, ⟨a, haInfinite, hchosen⟩⟩
    let s : I.lambda.source :=
      ⟨.proxy i, I.mem_lambda_source_proxy i⟩
    refine ⟨s, ?_⟩
    change infiniteStage L i = a
    exact infiniteStage_eq L hL.legal i hchosen

theorem auxiliarySourceIndex_eq_sourceIndex
    (L : Gamma.KappaLadder kappa) (hlegal : IsDeferredLegal L) :
    auxiliarySourceIndex L hlegal =
      (popularAuxiliaryInput L hlegal).sourceIndex
        (finiteTerminalIndex L) (infiniteStage L) := by
  funext x
  apply Subtype.ext
  rcases x with ⟨x, hx⟩
  cases x <;> rfl

/-- The indexed transformed web before imposing pathwise chronology. -/
noncomputable def popularAuxiliaryIndexed
    (L : Gamma.KappaLadder kappa) (hL : IsKappaHindrance L) :
    Popular.KappaIndexed (popularAuxiliaryInput L hL.legal).lambda kappa where
  regular := hL.legal.regular
  uncountable := hL.legal.uncountable
  f := (popularAuxiliaryInput L hL.legal).sourceIndex
    (finiteTerminalIndex L) (infiniteStage L)
  g := (popularAuxiliaryInput L hL.legal).targetIndex
    (targetMarkerIndex L hL.legal)
  f_range_stationary := by
    rw [← auxiliarySourceIndex_eq_sourceIndex L hL.legal]
    exact auxiliarySourceRange_isStationary L hL

theorem popularAuxiliaryIndexed_sourceIndexed
    (L : Gamma.KappaLadder kappa) (hL : IsKappaHindrance L) :
    (popularAuxiliaryIndexed L hL).SourceIndexed := by
  change Function.Injective
    ((popularAuxiliaryInput L hL.legal).sourceIndex
      (finiteTerminalIndex L) (infiniteStage L))
  rw [← auxiliarySourceIndex_eq_sourceIndex L hL.legal]
  exact auxiliarySourceIndex_injective L hL.legal

theorem auxiliarySourceIndex_mem_phi
    (L : Gamma.KappaLadder kappa) (hlegal : IsDeferredLegal L)
    (x : (popularAuxiliaryInput L hlegal).lambda.source) :
    auxiliarySourceIndex L hlegal x ∈ phi L := by
  let I := popularAuxiliaryInput L hlegal
  rcases x with ⟨x, hx⟩
  cases x with
  | old y =>
      let ys : finiteTerminalSet L :=
        ⟨y, (I.mem_lambda_source_old y).1 hx⟩
      change finiteTerminalStage L ys ∈ phi L
      exact (finiteTerminalStage_spec L ys).1.1
  | edge y z => exact False.elim (I.not_mem_lambda_source_edge y z hx)
  | proxy i =>
      change infiniteStage L i ∈ phi L
      exact (infiniteStage_spec L i).1.1

theorem equalSubwarp_initialIndices_subset_phi
    (L : Gamma.KappaLadder kappa) (hL : IsKappaHindrance L)
    (P : Popular.XSWarp
      (popularAuxiliaryInput L hL.legal).lambda
      (popularAuxiliaryInput L hL.legal).lambda.target) :
    Popular.initialIndicesOf (popularAuxiliaryIndexed L hL)
        ((popularAuxiliaryIndexed L hL).equalSubwarp P).paths
        ((popularAuxiliaryIndexed L hL).equalSubwarp P).starts_in_source
      ⊆ phi L := by
  let U := popularAuxiliaryIndexed L hL
  rintro a ⟨p, hp, hpa⟩
  have hsource := auxiliarySourceIndex_mem_phi L hL.legal
    ⟨p.start, (U.equalSubwarp P).starts_in_source hp⟩
  rw [auxiliarySourceIndex_eq_sourceIndex L hL.legal] at hsource
  exact hpa ▸ hsource

/-- A stationary equal-index output has stationary grounded indices;
deferred bookkeeping has no same-stage exception. -/
theorem equalSubwarp_ground_isStationary
    (L : Gamma.KappaLadder kappa) (hL : IsKappaHindrance L)
    (P : Popular.XSWarp
      (popularAuxiliaryInput L hL.legal).lambda
      (popularAuxiliaryInput L hL.legal).lambda.target)
    (hstat : Stationary.IsStationaryBelow kappa
      (Popular.initialIndicesOf (popularAuxiliaryIndexed L hL)
        ((popularAuxiliaryIndexed L hL).equalSubwarp P).paths
        ((popularAuxiliaryIndexed L hL).equalSubwarp P).starts_in_source)) :
    Stationary.IsStationaryBelow kappa
      (Popular.initialIndicesOf (popularAuxiliaryIndexed L hL)
          ((popularAuxiliaryIndexed L hL).equalSubwarp P).paths
          ((popularAuxiliaryIndexed L hL).equalSubwarp P).starts_in_source ∩
        phiGround L) := by
  let E := Popular.initialIndicesOf (popularAuxiliaryIndexed L hL)
    ((popularAuxiliaryIndexed L hL).equalSubwarp P).paths
    ((popularAuxiliaryIndexed L hL).equalSubwarp P).starts_in_source
  have hdiff : Stationary.IsStationaryBelow kappa
      (E \ phiHanging L) :=
    PopularSwitching.stationary_diff_of_stationary_of_nonstationary
      hL.legal.regular hL.legal.uncountable hstat
      (phiHanging_not_stationary L hL.legal)
  apply hdiff.mono
  rintro a ⟨haE, haNotHanging⟩
  refine ⟨haE, ?_⟩
  by_contra haGround
  exact haNotHanging ⟨equalSubwarp_initialIndices_subset_phi L hL P haE,
    haGround⟩

theorem strongTarget_or_separator
    (L : Gamma.KappaLadder kappa) (hL : IsKappaHindrance L) :
    Popular.IsStronglyPopular (popularAuxiliaryIndexed L hL)
        (popularAuxiliaryInput L hL.legal).lambda.target ∨
      Nonempty (Popular.PopularSeparator (popularAuxiliaryIndexed L hL)) := by
  have hsource : (popularAuxiliaryIndexed L hL).SourceBounded :=
    (popularAuxiliaryIndexed L hL).sourceBounded_of_sourceIndexed
      (popularAuxiliaryIndexed_sourceIndexed L hL)
  exact Popular.stronglyPopular_target_or_popularSeparator
    (popularAuxiliaryIndexed L hL) hsource

/-- Under weak chronology, the strong-target arm is already a grounded
stationary family; the other arm is the popular separator used by the
switch-prune construction. -/
theorem groundEqual_or_separator
    (L : Gamma.KappaLadder kappa) (hL : IsKappaHindrance L)
    (hmono : (popularAuxiliaryIndexed L hL).Nonincreasing) :
    (∃ P : Popular.XSWarp
        (popularAuxiliaryInput L hL.legal).lambda
        (popularAuxiliaryInput L hL.legal).lambda.target,
      Stationary.IsStationaryBelow kappa
        (Popular.initialIndicesOf (popularAuxiliaryIndexed L hL)
            ((popularAuxiliaryIndexed L hL).equalSubwarp P).paths
            ((popularAuxiliaryIndexed L hL).equalSubwarp P).starts_in_source ∩
          phiGround L)) ∨
      Nonempty (Popular.PopularSeparator (popularAuxiliaryIndexed L hL)) := by
  rcases strongTarget_or_separator L hL with hstrong | hseparator
  · obtain ⟨P, hP⟩ := (popularAuxiliaryIndexed L hL)
      |>.stronglyPopular_target_equal hmono hstrong
    exact Or.inl ⟨P, equalSubwarp_ground_isStationary L hL P hP⟩
  · exact Or.inr hseparator

end Deferred
end KappaLadder
end DWeb
end Erdos599
