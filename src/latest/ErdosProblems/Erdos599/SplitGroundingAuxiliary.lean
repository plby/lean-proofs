/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HindranceGrounding
import ErdosProblems.Erdos599.PopularIndexedDichotomy
import ErdosProblems.Erdos599.SplitHindranceGrounding

/-!
# The Section 8 auxiliary web for split-legal ladders

The legacy grounding auxiliary uses proxies only for infinite records in
`phiGround`.  That is insufficient for the successor-normalized ladder: a
genuinely new record may start at the marker born at the same stage, and it
may be a ray.  The sound auxiliary therefore represents every infinite
obstruction record.  Finite obstruction records are already all represented
by `finiteTerminalSet`.

With this correction the source-index range contains the whole stationary
set `phi`, without first discarding the same-stage branch.  The rest of the
popular-separator construction only needs this stationary range and the
injectivity of the source index, both proved below.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace DWeb

open DirectedPath

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace KappaLadder

/-- Infinite paths selected at arbitrary obstruction stages.  In contrast
to `groundedInfiniteRecords`, this also retains the genuine same-stage
hanging rays allowed by split legality. -/
abbrev splitInfiniteRecords (L : Gamma.KappaLadder kappa) :=
  {p : Gamma.DPath // exists a : Ladder.Stage kappa,
    a ∈ L.phiInfinite ∧ L.chosen a = some p}

/-- The path represented by a split auxiliary proxy. -/
noncomputable def splitInfinitePath (L : Gamma.KappaLadder kappa)
    (_hlegal : L.IsSplitLegal) (p : L.splitInfiniteRecords) : Gamma.DPath :=
  p.1

/-- Ray-priority bookkeeping makes every split proxy an actual ray. -/
theorem splitInfinitePath_isRay (L : Gamma.KappaLadder kappa)
    (hlegal : L.IsSplitLegal) (p : L.splitInfiniteRecords) :
    ∃ r : _root_.Erdos599.DirectedPath.Ray Gamma.graph,
      L.splitInfinitePath hlegal p = .inr r := by
  obtain ⟨a, ha, hchosen⟩ := p.2
  obtain ⟨q, hq, hqRay⟩ :=
    L.bookkeeping.chosen_isRay_of_mem_phiInfinite
      hlegal.validBookkeeping ha
  have hpq : p.1 = q := Option.some.inj (hchosen.symm.trans hq)
  have hpath : L.splitInfinitePath hlegal p = q := by
    simpa only [splitInfinitePath] using hpq
  rw [hpath]
  rcases q with q | r
  · change (some q.finish : Option V) = none at hqRay
    cases hqRay
  · exact ⟨r, rfl⟩

/-- The literal auxiliary input for split legality.  Its finite sources are
all finite records and its proxies are all infinite records. -/
noncomputable def splitPopularAuxiliaryInput (L : Gamma.KappaLadder kappa)
    (hlegal : L.IsSplitLegal) :
    PopularAuxiliary.Input Gamma L.splitInfiniteRecords where
  ladder := ⟨L.limitWarp,
    hlegal.warpStages (Ladder.finalStage kappa)⟩
  finiteSource := L.finiteTerminalSet
  markerSet := L.markerSet
  proxyPath := L.splitInfinitePath hlegal
  proxy_isRay := L.splitInfinitePath_isRay hlegal

/-- A record selected at the stage of its own initial marker is literally
the singleton marker component.  Both paths lie in the same successor warp
and meet at their common initial vertex, so warp disjointness forces them to
be equal. -/
theorem sameStageRecordedPath_eq_trivialPath
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsSplitLegal)
    {a : Ladder.Stage kappa} {p : Gamma.DPath}
    (hchosen : L.chosen a = some p)
    (hmarker : L.marker a = some p.initial) :
    p = Gamma.trivialPath p.initial := by
  have hpSuccessor : p ∈ L.successorWarp a :=
    ((L.bookkeeping.chosen_mem_available
      hlegal.validBookkeeping hchosen).1).1
  have hmarkerSuccessor : Gamma.trivialPath p.initial ∈
      L.successorWarp a :=
    (hlegal.freshMarkers.2 a p.initial hmarker).2
  by_contra hne
  exact Set.disjoint_left.1
      (hlegal.warpStages (Ladder.Stage.succExtended a)
        hpSuccessor hmarkerSuccessor hne)
    p.initial_mem_support (by
      rw [Gamma.support_trivialPath]
      exact Set.mem_singleton p.initial)

/-- Consequently the initial marker of a same-stage record is not retained
by the essential limiting ladder, and hence is not a target marker of the
split auxiliary.  This is the global persistence fact which removes the
genuine same-stage bookkeeping branch from an equal-index target warp. -/
theorem sameStageRecordedInitial_not_mem_targetMarkers
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsSplitLegal)
    {a : Ladder.Stage kappa} {p : Gamma.DPath}
    (hchosen : L.chosen a = some p)
    (hmarker : L.marker a = some p.initial) :
    p.initial ∉ (L.splitPopularAuxiliaryInput hlegal).targetMarkers := by
  intro htarget
  have hpEq : p = Gamma.trivialPath p.initial :=
    L.sameStageRecordedPath_eq_trivialPath hlegal hchosen hmarker
  have hpLimit : p ∈ Gamma.inessentialPaths L.limitWarp := by
    apply L.recorded_mem_inessential hlegal.recordedPathsPersist hchosen
    change a.1 + 1 ≤ kappa.ord
    exact (Order.add_one_le_iff).2 a.2
  obtain ⟨q, hqEssential, hpq⟩ := htarget.2
  have hmeet : (p.support ∩ q.support).Nonempty := by
    refine ⟨p.initial, p.initial_mem_support, ?_⟩
    exact hpq
  have hwarpLimit : Gamma.IsWarp L.limitWarp :=
    hlegal.warpStages (Ladder.finalStage kappa)
  exact (Gamma.not_mem_inessentialPaths_of_intersects_essential
      hwarpLimit hqEssential hmeet) hpLimit

/-- The recorded-stage uniqueness proof uses only persistence, warp
disjointness, and valid bookkeeping, hence is valid for split legality. -/
theorem IsSplitLegal.recordedStage_eq_of_same_terminal
    {L : Gamma.KappaLadder kappa} (hL : L.IsSplitLegal)
    {a b : Ladder.Stage kappa} {p q : Gamma.DPath} {x : V}
    (hpa : L.chosen a = some p) (hpx : Gamma.terminal? p = some x)
    (hqb : L.chosen b = some q) (hqx : Gamma.terminal? q = some x) :
    a = b := by
  rcases le_total a b with hab | hba
  · have hpWarp : p ∈ L.successorWarp b :=
      (L.recorded_mem_successor_inessential
        hL.recordedPathsPersist hpa hab).1
    have hqWarp : q ∈ L.successorWarp b :=
      ((L.bookkeeping.chosen_mem_available hL.validBookkeeping hqb).1).1
    by_cases hpq : p = q
    · subst q
      exact L.bookkeeping.chosen_stage_unique hL.validBookkeeping hpa hqb
    · exact False.elim <| Set.disjoint_left.1
        (hL.warpStages (Ladder.Stage.succExtended b)
          hpWarp hqWarp hpq)
        (Gamma.terminal_mem_support hpx) (Gamma.terminal_mem_support hqx)
  · have hqWarp : q ∈ L.successorWarp a :=
      (L.recorded_mem_successor_inessential
        hL.recordedPathsPersist hqb hba).1
    have hpWarp : p ∈ L.successorWarp a :=
      ((L.bookkeeping.chosen_mem_available hL.validBookkeeping hpa).1).1
    by_cases hpq : p = q
    · subst q
      exact L.bookkeeping.chosen_stage_unique hL.validBookkeeping hpa hqb
    · exact False.elim <| Set.disjoint_left.1
        (hL.warpStages (Ladder.Stage.succExtended a)
          hpWarp hqWarp hpq)
        (Gamma.terminal_mem_support hpx) (Gamma.terminal_mem_support hqx)

/-- A finite terminal still determines its unique record stage under split
legality. -/
theorem finiteTerminalStage_eq_of_split
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsSplitLegal)
    {a : Ladder.Stage kappa} {p : Gamma.DPath} {x : V}
    (hchosen : L.chosen a = some p)
    (hterminal : Gamma.terminal? p = some x)
    (hx : x ∈ L.finiteTerminalSet) :
    L.finiteTerminalStage ⟨x, hx⟩ = a := by
  obtain ⟨_, q, hq, hqterminal⟩ := L.finiteTerminalStage_spec ⟨x, hx⟩
  exact hlegal.recordedStage_eq_of_same_terminal
    hq hqterminal hchosen hterminal

/-- The split auxiliary represents every finite obstruction record, not just
the grounded ones used by the ordinary grounding auxiliary.  Its finite
source index is therefore the unrestricted finite-record stage map. -/
noncomputable def splitFiniteTerminalIndex
    (L : Gamma.KappaLadder kappa) :
    L.finiteTerminalSet → Stationary.Below kappa :=
  L.finiteTerminalStage

theorem splitFiniteTerminalIndex_injective
    (L : Gamma.KappaLadder kappa) :
    Function.Injective L.splitFiniteTerminalIndex :=
  L.finiteTerminalStage_injective

/-- Recover the obstruction stage represented by a split infinite proxy. -/
noncomputable def splitInfiniteStage (L : Gamma.KappaLadder kappa) :
    L.splitInfiniteRecords → Ladder.Stage kappa :=
  fun p ↦ Classical.choose p.2

theorem splitInfiniteStage_spec (L : Gamma.KappaLadder kappa)
    (p : L.splitInfiniteRecords) :
    L.splitInfiniteStage p ∈ L.phiInfinite ∧
      L.chosen (L.splitInfiniteStage p) = some p.1 :=
  Classical.choose_spec p.2

theorem splitInfiniteStage_eq (L : Gamma.KappaLadder kappa)
    (hlegal : L.IsSplitLegal) (p : L.splitInfiniteRecords)
    {a : Ladder.Stage kappa} (ha : L.chosen a = some p.1) :
    L.splitInfiniteStage p = a := by
  exact L.bookkeeping.chosen_stage_unique hlegal.validBookkeeping
    (L.splitInfiniteStage_spec p).2 ha

/-- The marker chronology map is unchanged by the provenance repair. -/
noncomputable def splitTargetMarkerIndex (L : Gamma.KappaLadder kappa)
    (hlegal : L.IsSplitLegal) :
    (L.splitPopularAuxiliaryInput hlegal).targetMarkers ↪
      Stationary.Below kappa where
  toFun y := L.markerStage ⟨y.1, y.2.1⟩
  inj' := by
    intro y z hyz
    apply Subtype.ext
    exact congrArg (fun w : L.markerSet ↦ w.1)
      (L.markerStage.injective hyz)

/-- The source-stage map for the split auxiliary. -/
noncomputable def splitAuxiliarySourceIndex
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsSplitLegal) :
    (L.splitPopularAuxiliaryInput hlegal).lambda.source →
      Stationary.Below kappa :=
  fun x ↦ match h : x.1 with
    | .old a => L.splitFiniteTerminalIndex ⟨a, by
        have hx := h ▸ x.2
        exact ((L.splitPopularAuxiliaryInput hlegal)
          |>.mem_lambda_source_old a).1 hx⟩
    | .edge a b => False.elim <| by
        have hx := h ▸ x.2
        exact (L.splitPopularAuxiliaryInput hlegal)
          |>.not_mem_lambda_source_edge a b hx
    | .proxy i => L.splitInfiniteStage i

/-- The source chronology is injective even across the finite/proxy split. -/
theorem splitAuxiliarySourceIndex_injective
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsSplitLegal) :
    Function.Injective (L.splitAuxiliarySourceIndex hlegal) := by
  let I := L.splitPopularAuxiliaryInput hlegal
  rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
  apply Subtype.ext
  cases x with
  | old a =>
      cases y with
      | old b =>
          let xa : L.finiteTerminalSet :=
            ⟨a, (I.mem_lambda_source_old a).1 hx⟩
          let yb : L.finiteTerminalSet :=
            ⟨b, (I.mem_lambda_source_old b).1 hy⟩
          change L.splitFiniteTerminalIndex xa =
            L.splitFiniteTerminalIndex yb at hxy
          exact congrArg PopularAuxiliary.Input.LambdaVertex.old
            (congrArg Subtype.val (L.splitFiniteTerminalIndex_injective hxy))
      | edge c d => exact False.elim (I.not_mem_lambda_source_edge c d hy)
      | proxy i =>
          let xa : L.finiteTerminalSet :=
            ⟨a, (I.mem_lambda_source_old a).1 hx⟩
          change L.finiteTerminalStage xa = L.splitInfiniteStage i at hxy
          have hfinite := (L.finiteTerminalStage_spec xa).1.2
          have hinfinite := (L.splitInfiniteStage_spec i).1
          exact False.elim (hfinite (hxy ▸ hinfinite))
  | edge a b => exact False.elim (I.not_mem_lambda_source_edge a b hx)
  | proxy i =>
      cases y with
      | old b =>
          let yb : L.finiteTerminalSet :=
            ⟨b, (I.mem_lambda_source_old b).1 hy⟩
          change L.splitInfiniteStage i = L.finiteTerminalStage yb at hxy
          have hfinite := (L.finiteTerminalStage_spec yb).1.2
          have hinfinite := (L.splitInfiniteStage_spec i).1
          exact False.elim (hfinite (hxy.symm ▸ hinfinite))
      | edge c d => exact False.elim (I.not_mem_lambda_source_edge c d hy)
      | proxy j =>
          change L.splitInfiniteStage i = L.splitInfiniteStage j at hxy
          apply congrArg PopularAuxiliary.Input.LambdaVertex.proxy
          apply Subtype.ext
          have hi := (L.splitInfiniteStage_spec i).2
          have hj := (L.splitInfiniteStage_spec j).2
          rw [hxy] at hi
          exact Option.some.inj (hi.symm.trans hj)

/-- The split source range contains every obstruction stage, so it is
stationary without eliminating any same-stage records. -/
theorem splitAuxiliarySourceRange_isStationary
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance) :
    Stationary.IsStationaryBelow kappa
      (Set.range (L.splitAuxiliarySourceIndex hL.legal)) := by
  let I := L.splitPopularAuxiliaryInput hL.legal
  apply hL.stationary.mono
  intro a ha
  obtain ⟨p, hchosen⟩ :=
    (L.bookkeeping.mem_phi_iff_exists_chosen
      hL.legal.validBookkeeping).1 ha
  rcases p with q | r
  · have haNotInfinite : a ∉ L.phiInfinite := by
      intro haInfinite
      obtain ⟨p, hp, hpRay⟩ :=
        L.bookkeeping.chosen_isRay_of_mem_phiInfinite
          hL.legal.validBookkeeping haInfinite
      have hpq : p = (.inl q : Gamma.DPath) :=
        Option.some.inj (hp.symm.trans hchosen)
      subst p
      change (some q.finish : Option V) = none at hpRay
      cases hpRay
    have haFinite : a ∈ L.phiFinite := ⟨ha, haNotInfinite⟩
    let x : L.finiteTerminalSet :=
      ⟨q.finish, a, haFinite, .inl q, hchosen, rfl⟩
    let s : I.lambda.source :=
      ⟨.old x.1, (I.mem_lambda_source_old x.1).2 x.2⟩
    refine ⟨s, ?_⟩
    change L.finiteTerminalStage _ = a
    exact L.finiteTerminalStage_eq_of_split hL.legal hchosen rfl x.2
  · have haInfinite : a ∈ L.phiInfinite := by
      refine ⟨ha, .inr r, ?_, rfl⟩
      exact L.bookkeeping.chosen_mem_available
        hL.legal.validBookkeeping hchosen
    let i : L.splitInfiniteRecords :=
      ⟨.inr r, ⟨a, haInfinite, hchosen⟩⟩
    let s : I.lambda.source := ⟨.proxy i, I.mem_lambda_source_proxy i⟩
    refine ⟨s, ?_⟩
    change L.splitInfiniteStage i = a
    exact L.splitInfiniteStage_eq hL.legal i hchosen

/-- Definitionally identify the installed source index. -/
theorem splitAuxiliarySourceIndex_eq_sourceIndex
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsSplitLegal) :
    L.splitAuxiliarySourceIndex hlegal =
      (L.splitPopularAuxiliaryInput hlegal).sourceIndex
        L.splitFiniteTerminalIndex L.splitInfiniteStage := by
  funext x
  apply Subtype.ext
  rcases x with ⟨x, hx⟩
  cases x <;> rfl

/-- The indexed auxiliary available before proving its weak chronology. -/
noncomputable def splitPopularAuxiliaryIndexed
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance) :
    Popular.KappaIndexed
      (L.splitPopularAuxiliaryInput hL.legal).lambda kappa where
  regular := hL.legal.regular
  uncountable := hL.legal.uncountable
  f := (L.splitPopularAuxiliaryInput hL.legal).sourceIndex
    L.splitFiniteTerminalIndex L.splitInfiniteStage
  g := (L.splitPopularAuxiliaryInput hL.legal).targetIndex
    (L.splitTargetMarkerIndex hL.legal)
  f_range_stationary := by
    rw [← L.splitAuxiliarySourceIndex_eq_sourceIndex hL.legal]
    exact L.splitAuxiliarySourceRange_isStationary hL

theorem splitPopularAuxiliaryIndexed_sourceIndexed
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance) :
    (L.splitPopularAuxiliaryIndexed hL).SourceIndexed := by
  change Function.Injective
    ((L.splitPopularAuxiliaryInput hL.legal).sourceIndex
      L.splitFiniteTerminalIndex L.splitInfiniteStage)
  rw [← L.splitAuxiliarySourceIndex_eq_sourceIndex hL.legal]
  exact L.splitAuxiliarySourceIndex_injective hL.legal

/-- Every source of the split auxiliary is indexed by the obstruction stage
which produced that finite terminal or infinite proxy. -/
theorem splitAuxiliarySourceIndex_mem_phi
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsSplitLegal)
    (x : (L.splitPopularAuxiliaryInput hlegal).lambda.source) :
    L.splitAuxiliarySourceIndex hlegal x ∈ L.phi := by
  let I := L.splitPopularAuxiliaryInput hlegal
  rcases x with ⟨x, hx⟩
  cases x with
  | old y =>
      let ys : L.finiteTerminalSet :=
        ⟨y, (I.mem_lambda_source_old y).1 hx⟩
      change L.finiteTerminalStage ys ∈ L.phi
      exact (L.finiteTerminalStage_spec ys).1.1
  | edge y z =>
      exact False.elim (I.not_mem_lambda_source_edge y z hx)
  | proxy i =>
      change L.splitInfiniteStage i ∈ L.phi
      exact (L.splitInfiniteStage_spec i).1.1

/-- In particular, all initial indices occurring in an equal target subwarp
are obstruction stages. -/
theorem splitEqualSubwarp_initialIndices_subset_phi
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (P : Popular.XSWarp
      (L.splitPopularAuxiliaryInput hL.legal).lambda
      (L.splitPopularAuxiliaryInput hL.legal).lambda.target) :
    Popular.initialIndicesOf (L.splitPopularAuxiliaryIndexed hL)
        ((L.splitPopularAuxiliaryIndexed hL).equalSubwarp P).paths
        ((L.splitPopularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source
      ⊆ L.phi := by
  let U := L.splitPopularAuxiliaryIndexed hL
  rintro a ⟨p, hp, hpa⟩
  have hsource :
      L.splitAuxiliarySourceIndex hL.legal
        ⟨p.start, (U.equalSubwarp P).starts_in_source hp⟩ ∈ L.phi :=
    L.splitAuxiliarySourceIndex_mem_phi hL.legal _
  rw [L.splitAuxiliarySourceIndex_eq_sourceIndex hL.legal] at hsource
  exact hpa ▸ hsource

/-- No equal-index target-warp path can have the index of a genuinely
same-stage hanging record.  Equality identifies its target marker stage
with the record stage, while the preceding lemma shows that the record's
own marker cannot belong to the target-marker set. -/
theorem splitEqualSubwarp_initialIndices_disjoint_freshSameStage
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (P : Popular.XSWarp
      (L.splitPopularAuxiliaryInput hL.legal).lambda
      (L.splitPopularAuxiliaryInput hL.legal).lambda.target) :
    Disjoint
      (Popular.initialIndicesOf (L.splitPopularAuxiliaryIndexed hL)
        ((L.splitPopularAuxiliaryIndexed hL).equalSubwarp P).paths
        ((L.splitPopularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source)
      L.freshSameStageHangingStages := by
  rw [Set.disjoint_left]
  intro a haIndex haSame
  let I := L.splitPopularAuxiliaryInput hL.legal
  let U := L.splitPopularAuxiliaryIndexed hL
  obtain ⟨r, hr, hra⟩ := haIndex
  obtain ⟨p, _haHanging, hchosen, _hpFresh, hmarker⟩ := haSame
  have hequal := U.equalSubwarp_index_eq P hr
  have hrTarget : r.finish ∈ I.lambda.target :=
    (U.equalSubwarp P).ends_in_target hr
  obtain ⟨y, hyTarget, hry⟩ := I.finish_of_mem_lambda_target r hrTarget
  have ht :
      U.g ⟨r.finish, (U.equalSubwarp P).ends_in_target hr⟩ =
        U.g ⟨.old y, (I.mem_lambda_target_old y).2 hyTarget⟩ := by
    apply congrArg U.g
    exact Subtype.ext hry
  have hstage : L.markerStage ⟨y, hyTarget.1⟩ = a := by
    calc
      L.markerStage ⟨y, hyTarget.1⟩ =
          U.g ⟨.old y, (I.mem_lambda_target_old y).2 hyTarget⟩ := rfl
      _ = U.g ⟨r.finish,
          (U.equalSubwarp P).ends_in_target hr⟩ := ht.symm
      _ = U.f ⟨r.start,
          (U.equalSubwarp P).starts_in_source hr⟩ := hequal
      _ = a := hra
  have hyAt : L.marker a = some y := by
    rw [← hstage]
    exact L.markerStage_spec ⟨y, hyTarget.1⟩
  have hpy : p.initial = y :=
    Option.some.inj (hmarker.symm.trans hyAt)
  exact L.sameStageRecordedInitial_not_mem_targetMarkers
    hL.legal hchosen hmarker (hpy ▸ hyTarget)

/-- A stationary equal-index target subwarp has stationary many grounded
obstruction indices.  Split provenance removes the strict hanging records,
and the preceding disjointness theorem removes the only successor-normalized
same-stage remainder. -/
theorem splitEqualSubwarp_ground_isStationary
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (P : Popular.XSWarp
      (L.splitPopularAuxiliaryInput hL.legal).lambda
      (L.splitPopularAuxiliaryInput hL.legal).lambda.target)
    (hstat : Stationary.IsStationaryBelow kappa
      (Popular.initialIndicesOf (L.splitPopularAuxiliaryIndexed hL)
        ((L.splitPopularAuxiliaryIndexed hL).equalSubwarp P).paths
        ((L.splitPopularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source)) :
    Stationary.IsStationaryBelow kappa
      (Popular.initialIndicesOf (L.splitPopularAuxiliaryIndexed hL)
          ((L.splitPopularAuxiliaryIndexed hL).equalSubwarp P).paths
          ((L.splitPopularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source ∩
        L.phiGround) := by
  let E : Set (Ladder.Stage kappa) :=
    Popular.initialIndicesOf (L.splitPopularAuxiliaryIndexed hL)
      ((L.splitPopularAuxiliaryIndexed hL).equalSubwarp P).paths
      ((L.splitPopularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source
  rcases L.stationary_ground_or_freshSameStageHanging
      hL.legal.splitLegalityInvariant E hstat
      (L.splitEqualSubwarp_initialIndices_subset_phi hL P) with
      hground | hsame
  · exact hground
  · obtain ⟨a, haE, haSame⟩ := hsame.nonempty
    exact False.elim <| Set.disjoint_left.1
      (L.splitEqualSubwarp_initialIndices_disjoint_freshSameStage hL P)
      haE haSame

/-- The exact strong-target/popular-separator branch for the split
auxiliary.  This theorem needs no chronology inequality; source indexing
alone supplies the required source-cardinality bound. -/
theorem splitPopularAuxiliary_strongTarget_or_separator
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance) :
    Popular.IsStronglyPopular (L.splitPopularAuxiliaryIndexed hL)
        (L.splitPopularAuxiliaryInput hL.legal).lambda.target ∨
      Nonempty
        (Popular.PopularSeparator (L.splitPopularAuxiliaryIndexed hL)) := by
  let U := L.splitPopularAuxiliaryIndexed hL
  have hsource : U.SourceBounded :=
    U.sourceBounded_of_sourceIndexed
      (L.splitPopularAuxiliaryIndexed_sourceIndexed hL)
  exact Popular.stronglyPopular_target_or_popularSeparator U hsource

/-- Under weak chronology, the strong-target branch is already grounded:
the strict part is nonstationary by pressing down, and the equal part cannot
use a same-stage hanging record. -/
theorem splitPopularAuxiliary_groundEqual_or_separator
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (hmono : (L.splitPopularAuxiliaryIndexed hL).Nonincreasing) :
    (∃ P : Popular.XSWarp
        (L.splitPopularAuxiliaryInput hL.legal).lambda
        (L.splitPopularAuxiliaryInput hL.legal).lambda.target,
      Stationary.IsStationaryBelow kappa
        (Popular.initialIndicesOf (L.splitPopularAuxiliaryIndexed hL)
            ((L.splitPopularAuxiliaryIndexed hL).equalSubwarp P).paths
            ((L.splitPopularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source ∩
          L.phiGround)) ∨
      Nonempty
        (Popular.PopularSeparator (L.splitPopularAuxiliaryIndexed hL)) := by
  rcases L.splitPopularAuxiliary_strongTarget_or_separator hL with
      hstrong | hseparator
  · obtain ⟨P, hP⟩ := (L.splitPopularAuxiliaryIndexed hL)
      |>.stronglyPopular_target_equal hmono hstrong
    exact Or.inl ⟨P, L.splitEqualSubwarp_ground_isStationary hL P hP⟩
  · exact Or.inr hseparator

/-- Under the weak successor chronology, the strong-target branch splits
into strict descent and the genuine equal-stage branch. -/
theorem splitPopularAuxiliary_strict_or_equal_or_separator
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (hmono : (L.splitPopularAuxiliaryIndexed hL).Nonincreasing) :
    (∃ P : Popular.XSWarp
        (L.splitPopularAuxiliaryInput hL.legal).lambda
        (L.splitPopularAuxiliaryInput hL.legal).lambda.target,
      Stationary.IsStationaryBelow kappa
        (Popular.initialIndicesOf (L.splitPopularAuxiliaryIndexed hL)
          ((L.splitPopularAuxiliaryIndexed hL).strictSubwarp P).paths
          ((L.splitPopularAuxiliaryIndexed hL).strictSubwarp P).starts_in_source)) ∨
      (∃ P : Popular.XSWarp
          (L.splitPopularAuxiliaryInput hL.legal).lambda
          (L.splitPopularAuxiliaryInput hL.legal).lambda.target,
        Stationary.IsStationaryBelow kappa
          (Popular.initialIndicesOf (L.splitPopularAuxiliaryIndexed hL)
            ((L.splitPopularAuxiliaryIndexed hL).equalSubwarp P).paths
            ((L.splitPopularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source)) ∨
        Nonempty
          (Popular.PopularSeparator (L.splitPopularAuxiliaryIndexed hL)) := by
  rcases L.splitPopularAuxiliary_strongTarget_or_separator hL with
      hstrong | hseparator
  · rcases (L.splitPopularAuxiliaryIndexed hL)
        |>.stronglyPopular_target_strict_or_equal hmono hstrong with
        hstrict | hequal
    · exact Or.inl hstrict
    · exact Or.inr (Or.inl hequal)
  · exact Or.inr (Or.inr hseparator)

end KappaLadder
end DWeb
end Erdos599
