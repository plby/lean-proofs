/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayNormalizationSeparator
import ErdosProblems.Erdos599.GeneralArrow315
import ErdosProblems.Erdos599.HalfwayClause

/-!
# Transporting altitude through normalization

The deletion set in a height witness is disjoint from the source.  This is
exactly the condition which makes the apparent mismatch between
`Gamma.normalized.quotient X` and `(Gamma.quotient X).normalized`
harmless at the level of waves: an original quotient path which uses an arc
entering the source has a final source--target suffix, and that suffix still
avoids `X`.  The lemmas below make this pathwise transport explicit.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace HalfwayNormalizationHeight

open DirectedPath

universe u

variable {V : Type u} {Gamma : DWeb V} {X C : Set V}

/-- Restoring the discarded arcs can only shrink a strict roof. -/
theorem strictRoof_subset_normalized_strictRoof (Gamma : DWeb V)
    (X : Set V) :
    Gamma.strictRoof X ⊆ Gamma.normalized.strictRoof X := by
  rintro x ⟨hxRoof, hxEssential⟩
  exact ⟨Gamma.roof_subset_normalized_roof X hxRoof,
    fun hx ↦ hxEssential (Gamma.essential_normalized_subset X hx)⟩

/-- Every vertex after the first one on a normalized path lies outside the
source. -/
theorem normalizedWalk_tail_avoids_source :
    ∀ {a b : V} (p : Walk Gamma.normalized.graph a b),
      ∀ {x}, x ∈ p.support.tail → x ∉ Gamma.source
  | _, _, .nil, _, hx => by simp at hx
  | _, _, .cons h p, x, hx => by
      simp only [Walk.support_cons, List.tail_cons] at hx
      rcases (RelationalRoof.mem_support_iff_start_or_mem_tail
        Gamma.normalized.graph.Adj p).1 hx with rfl | hx
      · exact h.2.1
      · exact normalizedWalk_tail_avoids_source p hx

/-- A normalized target path whose tail avoids `X` uses no vertex of the
strict roof of `X`. -/
theorem normalizedTargetPath_avoids_strictRoof
    (q : FinitePath Gamma.normalized.graph)
    (hqTarget : q.finish ∈ Gamma.target)
    (hqTail : ∀ {x}, x ∈ q.walk.support.tail → x ∉ X) :
    ∀ {x}, x ∈ q.support → x ∉ Gamma.normalized.strictRoof X := by
  intro x hx hxStrict
  let s := q.suffixFromAux x hx
  have hsTarget : Gamma.normalized.IsTargetPathFrom x s := by
    exact ⟨rfl, by simpa [s] using hqTarget⟩
  obtain ⟨y, hys, hyX⟩ := hxStrict.1 s hsTarget
  have hyq : y ∈ q.support := q.suffixFromAux_support_subset x hx hys
  have hyStart : y = q.start := by
    rcases (RelationalRoof.mem_support_iff_start_or_mem_tail
      Gamma.normalized.graph.Adj q.walk).1 hyq with hy | hy
    · exact hy
    · exact False.elim (hqTail hy hyX)
  by_cases hxStart : x = q.start
  · subst x
    apply hxStrict.2
    refine ⟨hyStart ▸ hyX, ?_⟩
    apply (Gamma.normalized.not_mem_roof_iff
      (X \ {q.start}) q.start).2
    refine ⟨q, ⟨rfl, hqTarget⟩, ?_⟩
    apply Set.disjoint_left.2
    intro z hzq hzDiff
    rcases (RelationalRoof.mem_support_iff_start_or_mem_tail
      Gamma.normalized.graph.Adj q.walk).1 hzq with hz | hz
    · exact hzDiff.2 (by simpa using hz)
    · exact hqTail hz hzDiff.1
  · exact (Gamma.normalized.start_not_mem_suffixFromAux_of_ne
      q x hx hxStart) (hyStart ▸ hys)

/-- A normalized target path whose tail avoids both `X` and the source
starts in the source of the normalized quotient by `X`. -/
theorem start_mem_normalizedQuotient_source
    (q : FinitePath Gamma.normalized.graph)
    (hqTarget : q.finish ∈ Gamma.target)
    (hqX : ∀ {x}, x ∈ q.walk.support.tail → x ∉ X)
    (hqSource : ∀ {x}, x ∈ q.walk.support.tail →
      x ∉ Gamma.source)
    (hstart : q.start ∈ X ∪ Gamma.source) :
    q.start ∈ (Gamma.normalized.quotient X).source := by
  change q.start ∈ Gamma.normalized.essential
    (Gamma.source ∪ X)
  refine ⟨hstart.symm, ?_⟩
  apply (Gamma.normalized.not_mem_roof_iff
    ((Gamma.source ∪ X) \ {q.start}) q.start).2
  refine ⟨q, ⟨rfl, hqTarget⟩, ?_⟩
  apply Set.disjoint_left.2
  intro z hzq hzDiff
  rcases (RelationalRoof.mem_support_iff_start_or_mem_tail
    Gamma.normalized.graph.Adj q.walk).1 hzq with hz | hz
  · exact hzDiff.2 (by simpa using hz)
  · rcases hzDiff.1 with hzSource | hzX
    · exact hqSource hz hzSource
    · exact hqX hz hzX

/-- Restrict the preceding normalized path to the normalized quotient. -/
noncomputable def restrictNormalizedTargetPathToQuotient
    (q : FinitePath Gamma.normalized.graph)
    (hqTarget : q.finish ∈ Gamma.target)
    (hqX : ∀ {x}, x ∈ q.walk.support.tail → x ∉ X) :
    FinitePath (Gamma.normalized.quotient X).graph :=
  Gamma.normalized.restrictFinitePathToQuotient X q
    (fun {_} hx ↦ normalizedTargetPath_avoids_strictRoof
      q hqTarget hqX hx) hqX

@[simp] theorem support_restrictNormalizedTargetPathToQuotient
    (q : FinitePath Gamma.normalized.graph)
    (hqTarget : q.finish ∈ Gamma.target)
    (hqX : ∀ {x}, x ∈ q.walk.support.tail → x ∉ X) :
    (restrictNormalizedTargetPathToQuotient q hqTarget hqX).support =
      q.support := by
  unfold restrictNormalizedTargetPathToQuotient
  exact Gamma.normalized.support_restrictFinitePathToQuotient X q
    (fun {_} hx ↦ normalizedTargetPath_avoids_strictRoof
      q hqTarget hqX hx) hqX

@[simp] theorem start_restrictNormalizedTargetPathToQuotient
    (q : FinitePath Gamma.normalized.graph)
    (hqTarget : q.finish ∈ Gamma.target)
    (hqX : ∀ {x}, x ∈ q.walk.support.tail → x ∉ X) :
    (restrictNormalizedTargetPathToQuotient q hqTarget hqX).start =
      q.start := rfl

@[simp] theorem finish_restrictNormalizedTargetPathToQuotient
    (q : FinitePath Gamma.normalized.graph)
    (hqTarget : q.finish ∈ Gamma.target)
    (hqX : ∀ {x}, x ∈ q.walk.support.tail → x ∉ X) :
    (restrictNormalizedTargetPathToQuotient q hqTarget hqX).finish =
      q.finish := rfl

/-- Every target path of the original quotient contains a target path of
the normalized quotient.  If the path visits the original source, retain a
final source--target suffix; otherwise the entire path can be normalized
without changing its support. -/
theorem exists_normalizedQuotient_targetPath
    (hX : X ⊆ Gamma.sourceᶜ)
    {a : V} (ha : a ∈ (Gamma.quotient X).source)
    (p : FinitePath (Gamma.quotient X).graph)
    (hp : (Gamma.quotient X).IsTargetPathFrom a p) :
    ∃ q : FinitePath (Gamma.normalized.quotient X).graph,
      q.start ∈ (Gamma.normalized.quotient X).source ∧
        q.finish ∈ Gamma.target ∧ q.support ⊆ p.support := by
  let lifted := p.lift (fun {_ _} h ↦ Gamma.quotient_adj_imp h)
  by_cases hmeetSource : ∃ y, y ∈ p.support ∧ y ∈ Gamma.source
  · obtain ⟨y, hyp, hySource⟩ := hmeetSource
    have hyLift : y ∈ lifted.support := by simpa [lifted] using hyp
    have hyX : y ∉ X := fun hyX ↦ hX hyX hySource
    let s := lifted.suffixFrom y hyLift
    have hsSource : s.start ∈ Gamma.source := by
      simpa [s] using hySource
    have hsTarget : s.finish ∈ Gamma.target := by
      change p.finish ∈ Gamma.target
      exact hp.2
    have hsAvoidX : Disjoint s.support X := by
      simpa [s, lifted] using
        (Gamma.suffixFrom_liftQuotientPath_avoids_commitment X p y hyp hyX)
    let q₀ := Gamma.normalizeFinitePath s hsSource hsTarget
    have hq₀Target : q₀.finish ∈ Gamma.target := by
      exact Gamma.normalizeFinitePath_finish_mem s hsSource hsTarget
    have hq₀X : ∀ {x}, x ∈ q₀.walk.support.tail → x ∉ X := by
      intro x hx hxX
      apply Set.disjoint_left.1 hsAvoidX
        (Gamma.normalizeFinitePath_support_subset s hsSource hsTarget
          (List.mem_of_mem_tail hx)) hxX
    have hq₀Source : ∀ {x}, x ∈ q₀.walk.support.tail →
        x ∉ Gamma.source := normalizedWalk_tail_avoids_source q₀.walk
    have hq₀Start : q₀.start ∈ X ∪ Gamma.source := by
      exact Or.inr (Gamma.normalizeFinitePath_start_mem s hsSource hsTarget)
    let q := restrictNormalizedTargetPathToQuotient q₀ hq₀Target hq₀X
    refine ⟨q, ?_, ?_, ?_⟩
    · exact start_mem_normalizedQuotient_source q₀ hq₀Target
        hq₀X hq₀Source hq₀Start
    · simpa [q] using hq₀Target
    · intro x hx
      have hxq₀ : x ∈ q₀.support := by simpa [q] using hx
      have hxs : x ∈ s.support :=
        Gamma.normalizeFinitePath_support_subset s hsSource hsTarget hxq₀
      have hxlift : x ∈ lifted.support :=
        lifted.suffixFrom_support_subset y hyLift hxs
      simpa [lifted] using hxlift
  · have htargetMeet : p.walk.Meets Gamma.target :=
      ⟨p.finish, p.finish_mem_support, hp.2⟩
    let f := p.firstHit Gamma.target htargetMeet
    have hfSource : ∀ {z}, z ∈ f.walk.support.tail →
        z ∉ Gamma.source := by
      intro z hz hzSource
      apply hmeetSource
      exact ⟨z, p.firstHit_support_subset Gamma.target htargetMeet
        (List.mem_of_mem_tail hz), hzSource⟩
    have hfTarget : ∀ {z}, z ∈ f.walk.support.dropLast →
        z ∉ Gamma.target := by
      intro z hz
      exact p.firstHit_no_mem_before Gamma.target htargetMeet hz
    have hfSourceLift : ∀ {z},
        z ∈ (f.walk.lift (fun {_ _} h ↦
          Gamma.quotient_adj_imp h)).support.tail →
          z ∉ Gamma.source := by
      intro z hz
      apply hfSource
      simpa using hz
    have hfTargetLift : ∀ {z},
        z ∈ (f.walk.lift (fun {_ _} h ↦
          Gamma.quotient_adj_imp h)).support.dropLast →
          z ∉ Gamma.target := by
      intro z hz
      apply hfTarget
      simpa using hz
    let q₀ : FinitePath Gamma.normalized.graph :=
      { start := f.start
        finish := f.finish
        walk := Gamma.normalizeWalk
          (f.walk.lift (fun {_ _} h ↦ Gamma.quotient_adj_imp h))
          hfSourceLift hfTargetLift
        isPath := by
          change (Gamma.normalizeWalk
            (f.walk.lift (fun {_ _} h ↦ Gamma.quotient_adj_imp h))
            hfSourceLift hfTargetLift).support.Nodup
          rw [Gamma.support_normalizeWalk, Walk.support_lift]
          exact f.isPath }
    have hq₀Target : q₀.finish ∈ Gamma.target := by
      exact p.firstHit_finish_mem Gamma.target htargetMeet
    have hq₀X : ∀ {x}, x ∈ q₀.walk.support.tail → x ∉ X := by
      intro x hx hxX
      have hxf : x ∈ f.walk.support.tail := by
        simpa [q₀, Gamma.support_normalizeWalk] using hx
      have hxp : x ∈ p.support :=
        p.firstHit_support_subset Gamma.target htargetMeet
          (List.mem_of_mem_tail hxf)
      rcases (RelationalRoof.mem_support_iff_start_or_mem_tail
        (Gamma.quotient X).graph.Adj p.walk).1 hxp with hxStart | hxTail
      · have hqStart : q₀.start = p.start := rfl
        apply DWeb.walk_start_not_mem_tail2 q₀.walk q₀.isPath
        simpa [hqStart, hxStart] using hx
      · exact (Gamma.quotientWalk_tail_avoids p.walk hxTail).2 hxX
    have hq₀Source : ∀ {x}, x ∈ q₀.walk.support.tail →
        x ∉ Gamma.source := normalizedWalk_tail_avoids_source q₀.walk
    have hq₀Start : q₀.start ∈ X ∪ Gamma.source := by
      have haUnion : a ∈ Gamma.source ∪ X := ha.1
      change p.start ∈ X ∪ Gamma.source
      rw [hp.1]
      exact haUnion.symm
    let q := restrictNormalizedTargetPathToQuotient q₀ hq₀Target hq₀X
    refine ⟨q, ?_, ?_, ?_⟩
    · exact start_mem_normalizedQuotient_source q₀ hq₀Target
        hq₀X hq₀Source hq₀Start
    · simpa [q] using hq₀Target
    · intro x hx
      have hxq₀ : x ∈ q₀.support := by simpa [q] using hx
      have hxf : x ∈ f.support := by
        change x ∈ (Gamma.normalizeWalk
          (f.walk.lift (fun {_ _} h ↦ Gamma.quotient_adj_imp h))
          hfSourceLift hfTargetLift).support at hxq₀
        rw [Gamma.support_normalizeWalk, Walk.support_lift] at hxq₀
        exact hxq₀
      exact p.firstHit_support_subset Gamma.target htargetMeet hxf

/-- Every normalized-quotient edge is an original-quotient edge. -/
theorem normalizedQuotient_adj_imp_quotient
    {u v : V}
    (h : (Gamma.normalized.quotient X).graph.Adj u v) :
    (Gamma.quotient X).graph.Adj u v := by
  exact ⟨h.1.1,
    fun hu ↦ h.2.1 (strictRoof_subset_normalized_strictRoof Gamma X hu),
    fun hv ↦ h.2.2.1
      (strictRoof_subset_normalized_strictRoof Gamma X hv),
    h.2.2.2⟩

/-- Regard a path in the normalized quotient as a path in the original
quotient. -/
def liftNormalizedQuotientPath
    (p : (Gamma.normalized.quotient X).DPath) :
    (Gamma.quotient X).DPath :=
  p.lift (fun {_ _} h ↦ normalizedQuotient_adj_imp_quotient h)

@[simp] theorem support_liftNormalizedQuotientPath
    (p : (Gamma.normalized.quotient X).DPath) :
    (liftNormalizedQuotientPath p : (Gamma.quotient X).DPath).support =
      p.support := by
  exact Path.support_lift
    (fun {_ _} h ↦ normalizedQuotient_adj_imp_quotient h) p

@[simp] theorem initial_liftNormalizedQuotientPath
    (p : (Gamma.normalized.quotient X).DPath) :
    (liftNormalizedQuotientPath p : (Gamma.quotient X).DPath).initial =
      p.initial := by
  rcases p with p | r <;> rfl

@[simp] theorem terminal?_liftNormalizedQuotientPath
    (p : (Gamma.normalized.quotient X).DPath) :
    (Gamma.quotient X).terminal? (liftNormalizedQuotientPath p) =
      (Gamma.normalized.quotient X).terminal? p := by
  rcases p with p | r <;> rfl

/-- Memberwise lift of a normalized-quotient family. -/
def liftNormalizedQuotientFamily
    (W : Set (Gamma.normalized.quotient X).DPath) :
    Set (Gamma.quotient X).DPath :=
  liftNormalizedQuotientPath '' W

theorem IsWarp.liftNormalizedQuotientFamily
    {W : Set (Gamma.normalized.quotient X).DPath}
    (hW : (Gamma.normalized.quotient X).IsWarp W) :
    (Gamma.quotient X).IsWarp
      (liftNormalizedQuotientFamily W) := by
  rintro p ⟨p₀, hp₀, rfl⟩ q ⟨q₀, hq₀, rfl⟩ hpq
  change Disjoint
    (liftNormalizedQuotientPath p₀ : (Gamma.quotient X).DPath).support
    (liftNormalizedQuotientPath q₀ : (Gamma.quotient X).DPath).support
  rw [support_liftNormalizedQuotientPath,
    support_liftNormalizedQuotientPath]
  apply hW hp₀ hq₀
  intro hp₀q₀
  subst q₀
  exact hpq rfl

@[simp] theorem initialSet_liftNormalizedQuotientFamily
    (W : Set (Gamma.normalized.quotient X).DPath) :
    (Gamma.quotient X).initialSet
        (liftNormalizedQuotientFamily W) =
      (Gamma.normalized.quotient X).initialSet W := by
  ext x
  constructor
  · rintro ⟨p, ⟨q, hq, rfl⟩, hpx⟩
    exact ⟨q, hq, by simpa using hpx⟩
  · rintro ⟨q, hq, hqx⟩
    exact ⟨liftNormalizedQuotientPath q, ⟨q, hq, rfl⟩,
      by simpa using hqx⟩

@[simp] theorem terminalFrontier_liftNormalizedQuotientFamily
    (W : Set (Gamma.normalized.quotient X).DPath) :
    (Gamma.quotient X).terminalFrontier
        (liftNormalizedQuotientFamily W) =
      (Gamma.normalized.quotient X).terminalFrontier W := by
  ext x
  constructor
  · rintro ⟨p, ⟨q, hq, rfl⟩, hpx⟩
    exact ⟨q, hq, by simpa using hpx⟩
  · rintro ⟨q, hq, hqx⟩
    exact ⟨liftNormalizedQuotientPath q, ⟨q, hq, rfl⟩,
      by simpa using hqx⟩

/-- A wave in the normalized quotient lifts to a wave in the original
quotient whenever the commitment set avoids the original source.  This is
the pathwise commutation result needed for altitude; equality of the two
quotient webs is neither claimed nor required. -/
theorem IsWave.liftNormalizedQuotientFamily
    (hX : X ⊆ Gamma.sourceᶜ)
    {W : Set (Gamma.normalized.quotient X).DPath}
    (hW : (Gamma.normalized.quotient X).IsWave W) :
    (Gamma.quotient X).IsWave
      (liftNormalizedQuotientFamily W) := by
  refine ⟨IsWarp.liftNormalizedQuotientFamily hW.1, ?_, ?_⟩
  · rw [initialSet_liftNormalizedQuotientFamily]
    intro x hx
    exact Gamma.essential_normalized_subset
      (Gamma.source ∪ X) (hW.2.1 hx)
  · intro a ha p hp
    obtain ⟨q, hqSource, hqTarget, hqp⟩ :=
      exists_normalizedQuotient_targetPath hX ha p hp
    obtain ⟨x, hxq, hxW⟩ := hW.2.2 hqSource q ⟨rfl, hqTarget⟩
    refine ⟨x, hqp hxq, ?_⟩
    simpa using hxW

/-- A normalized height witness transports to the original web when the
set whose height is measured already roofs the normalized source.  The
source-roof hypothesis also transports the normalized roof of the witness
frontier back to the original roof. -/
theorem IsHeightWitness.of_normalized_of_source_roof
    {Z X : Set V}
    (hsource : Gamma.normalized.source ⊆ Gamma.normalized.roof Z)
    (hZ : IsHeightWitness Gamma.normalized Z X) :
    IsHeightWitness Gamma Z X := by
  obtain ⟨hXsource, W, hW, hroof⟩ := hZ
  let S := (Gamma.normalized.quotient X).terminalFrontier W
  have hsourceS : Gamma.normalized.source ⊆
      Gamma.normalized.roof S :=
    hsource.trans (Gamma.normalized.roof_cut hroof)
  have hroofEq : Gamma.normalized.roof S = Gamma.roof S :=
    normalized_roof_eq_of_source_subset_roof hsourceS
  refine ⟨?_, liftNormalizedQuotientFamily W,
    IsWave.liftNormalizedQuotientFamily (Gamma := Gamma)
      hXsource hW, ?_⟩
  · simpa using hXsource
  · rw [terminalFrontier_liftNormalizedQuotientFamily]
    intro z hz
    have hzS : z ∈ Gamma.normalized.roof S := hroof hz
    rw [hroofEq] at hzS
    exact hzS

/-- Hence every normalized bounded-height certificate at a source-roofing
set is an original bounded-height certificate, with the same deletion set
and cardinal estimate. -/
theorem HeightAtMost.of_normalized_of_source_roof
    {Z : Set V} {kappa : Cardinal.{u}}
    (hsource : Gamma.normalized.source ⊆ Gamma.normalized.roof Z)
    (hZ : HeightAtMost Gamma.normalized Z kappa) :
    HeightAtMost Gamma Z kappa := by
  obtain ⟨X, hX, hcard⟩ := hZ
  exact ⟨X,
    IsHeightWitness.of_normalized_of_source_roof hsource hX, hcard⟩

/-- One-shot transport at the bounded stop-over selected by the normalized
construction.  All three pieces of the conclusion are derived here:
stop-over geometry by quotient commutation, target-linkability by edge
inclusion, and altitude by the pathwise height transport above. -/
theorem IsHalfwayLinkageOfAltitude.liftNormalized_at_boundedStopover_of_source_roof
    {A0 C : Set V} {kappa : Cardinal.{u}}
    {W : Set Gamma.normalized.DPath}
    (hW : IsHalfwayLinkageOfAltitude Gamma.normalized A0 kappa W)
    (hC : IsHalfwayStopover Gamma.normalized W C)
    (hCheight : HeightAtMost Gamma.normalized C kappa)
    (hsource : Gamma.source ⊆ Gamma.normalized.roof C) :
    IsHalfwayLinkageOfAltitude Gamma A0 kappa
      (Gamma.liftNormalizedFamily W) := by
  have hsource' : Gamma.normalized.source ⊆
      Gamma.normalized.roof C := by simpa using hsource
  exact halfwayLinkageOfAltitude_of_stopover
    (hC.liftNormalized_of_source_roof hsource')
    hW.2.1.liftNormalized
    (HeightAtMost.of_normalized_of_source_roof
      (Gamma := Gamma) hsource' hCheight)

/-- A formulation with no separately supplied quotient or height
certificate: choose the bounded stop-over guaranteed by `hW`; it is enough
that every such normalized stop-over roofs the original source. -/
theorem IsHalfwayLinkageOfAltitude.liftNormalized_of_stopovers_source_roof
    {A0 : Set V} {kappa : Cardinal.{u}}
    {W : Set Gamma.normalized.DPath}
    (hW : IsHalfwayLinkageOfAltitude Gamma.normalized A0 kappa W)
    (hsource : ∀ {C : Set V},
      IsHalfwayStopover Gamma.normalized W C →
        Gamma.source ⊆ Gamma.normalized.roof C) :
    IsHalfwayLinkageOfAltitude Gamma A0 kappa
      (Gamma.liftNormalizedFamily W) := by
  obtain ⟨C, hC, hCheight⟩ := hW.exists_stopover
  exact
    IsHalfwayLinkageOfAltitude.liftNormalized_at_boundedStopover_of_source_roof
      (Gamma := Gamma) hW hC hCheight (hsource hC)

/-- Preserve the scheduler-selected stop-over when extracting a linkage
from a globally resolved blueprint certificate.  The older existential
wrapper records only the packaged altitude conclusion, whereas
normalization transport needs the concrete stop-over and its concrete
height certificate. -/
theorem GloballyResolvedBlueprintCertificate.exists_boundedStopover
    {A0 : Set V} {kappa : Cardinal.{u}}
    (F : GloballyResolvedBlueprintCertificate Gamma A0 kappa) :
    ∃ W : Set Gamma.DPath,
      IsHalfwayStopover Gamma W F.stopover ∧
        LinksToTarget Gamma W A0 ∧
        HeightAtMost Gamma F.stopover kappa := by
  have hgraph : F.blueprint.familyGraph = F.blueprint.realPart := by
    change Blueprint.FamilyGraph.mk F.blueprint.familyGraph.vertices
        F.blueprint.familyGraph.edges =
      Blueprint.FamilyGraph.mk F.blueprint.realPart.vertices
        F.blueprint.realPart.edges
    apply congrArg₂ (fun vertices edges ↦
      Blueprint.FamilyGraph.mk vertices edges)
    · rfl
    · change F.blueprint.familyGraph.edges =
        F.blueprint.familyGraph.edges ∩
          {e | Gamma.graph.Adj e.1 e.2}
      apply Set.Subset.antisymm
      · intro e he
        exact ⟨he, F.edge_real he⟩
      · exact Set.inter_subset_left
  have hterminal : F.blueprint.terminalSet ⊆ Gamma.target := by
    intro x hx
    have hxterm := F.blueprint.terminalSet_subset_familyGraph_terminals
      F.blueprint_endpointPure hx
    rw [hgraph] at hxterm
    exact F.real_terminals_target hxterm
  have hlinks : F.blueprint.BlueprintLinksToTarget A0 :=
    F.blueprint.blueprintLinksToTarget_of_initial_terminal
      F.designated_source F.designated_initial
      F.blueprint_endpointPure hterminal
  exact exists_halfwayStopover_of_terminalBlueprint_withReference
    F.blueprint F.edge_real
    (F.blueprint.referenceRemainder F.slice)
    (F.blueprint.isWarp_referenceRemainder F.slice F.reference_isWarp)
    (F.blueprint.disjoint_referenceRemainder F.slice)
    F.source_cover F.terminal_frontier F.blueprint_endpointPure
    F.reference_endpointPure F.stopover_separator F.stopover_trimmed
    F.quotient_unhindered
    hlinks F.heightDelete_nonSource F.heightWave F.heightWave_isWave
    F.stopover_roofed F.heightDelete_card

/-- Public arbitrary-web transport for a normalized final scheduler
certificate.  A source-roof proof for its concrete stop-over is the only
additional fact; quotient unhinderedness and normalized height are read
from the certificate, and their original-web versions are derived. -/
theorem GloballyResolvedBlueprintCertificate.exists_original_halfwayLinkage_of_source_roof
    {A0 : Set V} {kappa : Cardinal.{u}}
    (F : GloballyResolvedBlueprintCertificate Gamma.normalized A0 kappa)
    (hsource : Gamma.source ⊆
      Gamma.normalized.roof F.stopover) :
    ∃ W : Set Gamma.DPath,
      IsHalfwayLinkageOfAltitude Gamma A0 kappa W := by
  obtain ⟨W, hstop, hlinks, hheight⟩ :=
    GloballyResolvedBlueprintCertificate.exists_boundedStopover F
  let hW : IsHalfwayLinkageOfAltitude
      Gamma.normalized A0 kappa W :=
    halfwayLinkageOfAltitude_of_stopover hstop hlinks hheight
  exact ⟨Gamma.liftNormalizedFamily W,
    IsHalfwayLinkageOfAltitude.liftNormalized_at_boundedStopover_of_source_roof
      (Gamma := Gamma) hW hstop hheight hsource⟩

end HalfwayNormalizationHeight
end CardinalInduction
end Erdos599
