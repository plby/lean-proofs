/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ExtensionClause
import ErdosProblems.Erdos599.SliceSegmentCore
import ErdosProblems.Erdos599.SliceSpliceSource
import ErdosProblems.Erdos599.SingularContinuation
import ErdosProblems.Erdos599.WaveLimits

/-!
# The quotient auxiliary web in the controlled-slice argument

After the first, half-way, linkage has stopped at a trimmed separator `C`,
the second linkage is constructed in the quotient by `C`, with its target
changed to the later ladder frontier.  This file makes that auxiliary web
explicit and supplies the three reusable facts needed in Assertion 9.15:

* a trimmed separating stop-over is exactly the source of the quotient;
* roofing the new target lifts any auxiliary hindrance to a hindrance in
  the unhindered quotient;
* the lower-cardinal extension clause consequently completes a linkage in
  the auxiliary web from a small exceptional source set and an ordinary
  linkage on its complement.

The final section gives the path-level concatenation operation used to join
the half-way paths to the resulting quotient paths.  Its hypotheses state
the exact sole-intersection condition needed for a simple concatenation;
the quotient geometry is responsible for this condition in the application.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace SliceAuxiliaryCore

open DirectedPath

universe u

variable {V : Type u}

/-! ## The auxiliary web -/

/-- The web used for the second join in 9.10/9.15: first quotient past the
half-way stop-over `C`, then regard the later frontier `T` as target. -/
def auxiliaryWeb (Q : DWeb V) (C T : Set V) : DWeb V :=
  (Q.quotient C).retarget T

@[simp] theorem auxiliaryWeb_graph (Q : DWeb V) (C T : Set V) :
    (auxiliaryWeb Q C T).graph = (Q.quotient C).graph :=
  rfl

@[simp] theorem auxiliaryWeb_source (Q : DWeb V) (C T : Set V) :
    (auxiliaryWeb Q C T).source = (Q.quotient C).source :=
  rfl

@[simp] theorem auxiliaryWeb_target (Q : DWeb V) (C T : Set V) :
    (auxiliaryWeb Q C T).target = T :=
  rfl

/-- A trimmed separator is precisely the new quotient source.  This is the
source identity silently used when the paper calls the second construction
a `C`--`T` linkage. -/
theorem quotient_source_eq_stopover
    (Q : DWeb V) {C : Set V}
    (hsep : IsSeparatorFrom Q Q.source C)
    (htrim : IsTrimmedSeparator Q C) :
    (Q.quotient C).source = C := by
  rw [DWeb.quotient_source, Set.union_comm]
  calc
    Q.essential (C ∪ Q.source) = Q.essential C :=
      RelationalRoof.essential_union_eq_of_subset_roof
        Q.graph.Adj Q.target hsep
    _ = C := htrim

theorem auxiliaryWeb_source_eq_stopover
    (Q : DWeb V) {C T : Set V}
    (hsep : IsSeparatorFrom Q Q.source C)
    (htrim : IsTrimmedSeparator Q C) :
    (auxiliaryWeb Q C T).source = C := by
  rw [auxiliaryWeb_source, quotient_source_eq_stopover Q hsep htrim]

/-- If the later frontier roofs the quotient source, retargeting the
unhindered quotient at that frontier remains unhindered.  A hindrance in
the retargeted web is a hindrance in the original quotient by separator
composition (`IsHindrance.of_retarget`). -/
theorem auxiliaryWeb_isUnhindered
    (Q : DWeb V) {C T : Set V}
    (hquotient : (Q.quotient C).IsUnhindered)
    (hroof : (Q.quotient C).source ⊆ (Q.quotient C).roof T) :
    (auxiliaryWeb Q C T).IsUnhindered := by
  rintro ⟨W, hW⟩
  apply hquotient
  refine ⟨W, ?_⟩
  exact DWeb.IsHindrance.of_retarget (Q.quotient C) hW hroof

/-- The same unhinderedness transfer stated with the stop-over itself as
the roofing hypothesis. -/
theorem auxiliaryWeb_isUnhindered_of_stopover
    (Q : DWeb V) {C T : Set V}
    (hsep : IsSeparatorFrom Q Q.source C)
    (htrim : IsTrimmedSeparator Q C)
    (hquotient : (Q.quotient C).IsUnhindered)
    (hroof : C ⊆ (Q.quotient C).roof T) :
    (auxiliaryWeb Q C T).IsUnhindered := by
  apply auxiliaryWeb_isUnhindered Q hquotient
  rwa [quotient_source_eq_stopover Q hsep htrim]

/-! ## Applying the lower-cardinal extension clause -/

/-- Apply the simultaneous induction hypothesis at the cardinality of the
small exceptional source set.  The supplied linkage on the complementary
sources is the family of surviving ordinary ladder segments in the source
application; the conclusion is a full linkage in the auxiliary web. -/
theorem exists_auxiliaryLinkage_of_lower
    {kappa : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (Delta : DWeb V) (hDelta : Delta.IsUnhindered)
    (E : Set V) (hEsub : E ⊆ Delta.source) (hE : #E < kappa)
    {F : Set Delta.DPath}
    (hF : IsLinkageBetween Delta (Delta.source \ E) Delta.target F) :
    ∃ R : Set Delta.DPath,
      IsLinkageBetween Delta Delta.source Delta.target R := by
  have hstep : CardinalInductionAt Delta #E :=
    hlower #E hE Delta hDelta
  exact hstep.extension E hEsub rfl ⟨F, hF⟩

/-- Construct the quotient/retarget auxiliary web, prove it unhindered,
and perform the lower-cardinal extension step in one theorem. -/
theorem exists_fullAuxiliaryLinkage_of_lower
    {kappa : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (Q : DWeb V) {C T E : Set V}
    (hsep : IsSeparatorFrom Q Q.source C)
    (htrim : IsTrimmedSeparator Q C)
    (hquotient : (Q.quotient C).IsUnhindered)
    (hroof : C ⊆ (Q.quotient C).roof T)
    (hEsub : E ⊆ C) (hE : #E < kappa)
    {F : Set (auxiliaryWeb Q C T).DPath}
    (hF : IsLinkageBetween (auxiliaryWeb Q C T)
      ((auxiliaryWeb Q C T).source \ E)
      (auxiliaryWeb Q C T).target F) :
    ∃ R : Set (auxiliaryWeb Q C T).DPath,
      IsLinkageBetween (auxiliaryWeb Q C T)
        (auxiliaryWeb Q C T).source
        (auxiliaryWeb Q C T).target R := by
  have hsource : (auxiliaryWeb Q C T).source = C :=
    auxiliaryWeb_source_eq_stopover Q hsep htrim
  have haux : (auxiliaryWeb Q C T).IsUnhindered :=
    auxiliaryWeb_isUnhindered_of_stopover Q hsep htrim hquotient hroof
  apply exists_auxiliaryLinkage_of_lower hlower
    (auxiliaryWeb Q C T) haux E
  · simpa only [hsource] using hEsub
  · exact hE
  · exact hF

/-! ## Tightening and lifting the auxiliary linkage -/

/-- Choose the finite representative of one member of a linkage. -/
noncomputable def linkageFinitePath
    {Gamma : DWeb V} {A B : Set V} {W : Set Gamma.DPath}
    (hW : IsLinkageBetween Gamma A B W) (p : W) :
    DirectedPath.FinitePath Gamma.graph :=
  Classical.choose (hW.finiteCharacter p.2)

theorem linkageFinitePath_spec
    {Gamma : DWeb V} {A B : Set V} {W : Set Gamma.DPath}
    (hW : IsLinkageBetween Gamma A B W) (p : W) :
    p.1 = .inl (linkageFinitePath hW p) :=
  Classical.choose_spec (hW.finiteCharacter p.2)

@[simp] theorem linkageFinitePath_start
    {Gamma : DWeb V} {A B : Set V} {W : Set Gamma.DPath}
    (hW : IsLinkageBetween Gamma A B W) (p : W) :
    (linkageFinitePath hW p).start = p.1.initial := by
  have h := congrArg DirectedPath.Path.initial (linkageFinitePath_spec hW p)
  exact h.symm

/-- Every chosen finite linkage member meets the right boundary at its
terminal vertex. -/
theorem linkageFinitePath_meets_target
    {Gamma : DWeb V} {A B : Set V} {W : Set Gamma.DPath}
    (hW : IsLinkageBetween Gamma A B W) (p : W) :
    (linkageFinitePath hW p).walk.Meets B := by
  refine ⟨(linkageFinitePath hW p).finish,
    (linkageFinitePath hW p).finish_mem_support, ?_⟩
  apply hW.terminalFrontier_subset
  refine ⟨p.1, p.2, ?_⟩
  rw [linkageFinitePath_spec hW p]
  rfl

/-- Truncate one linkage member at its first visit to the right boundary. -/
noncomputable def rightTightenedPath
    {Gamma : DWeb V} {A B : Set V} {W : Set Gamma.DPath}
    (hW : IsLinkageBetween Gamma A B W) (p : W) :
    DirectedPath.FinitePath Gamma.graph :=
  (linkageFinitePath hW p).firstHit B
    (linkageFinitePath_meets_target hW p)

@[simp] theorem rightTightenedPath_start
    {Gamma : DWeb V} {A B : Set V} {W : Set Gamma.DPath}
    (hW : IsLinkageBetween Gamma A B W) (p : W) :
    (rightTightenedPath hW p).start = p.1.initial :=
  linkageFinitePath_start hW p

@[simp] theorem rightTightenedPath_finish_mem
    {Gamma : DWeb V} {A B : Set V} {W : Set Gamma.DPath}
    (hW : IsLinkageBetween Gamma A B W) (p : W) :
    (rightTightenedPath hW p).finish ∈ B :=
  DirectedPath.FinitePath.firstHit_finish_mem _ _ _

theorem rightTightenedPath_support_subset
    {Gamma : DWeb V} {A B : Set V} {W : Set Gamma.DPath}
    (hW : IsLinkageBetween Gamma A B W) (p : W) :
    (rightTightenedPath hW p).support ⊆
      (linkageFinitePath hW p).support :=
  DirectedPath.FinitePath.firstHit_support_subset _ _ _

/-- A first-hit prefix meets its cutting set precisely at its terminal
vertex. -/
theorem rightTightenedPath_target_pure
    {Gamma : DWeb V} {A B : Set V} {W : Set Gamma.DPath}
    (hW : IsLinkageBetween Gamma A B W) (p : W) :
    (rightTightenedPath hW p).support ∩ B =
      {(rightTightenedPath hW p).finish} := by
  apply Set.Subset.antisymm
  · rintro x ⟨hx, hxB⟩
    apply Set.mem_singleton_iff.mpr
    by_contra hxFinish
    have hlast :
        (rightTightenedPath hW p).walk.support.getLast
            (rightTightenedPath hW p).walk.support_ne_nil =
          (rightTightenedPath hW p).finish :=
      (rightTightenedPath hW p).walk.getLast_support
    have hxLast : x ≠
        (rightTightenedPath hW p).walk.support.getLast
          (rightTightenedPath hW p).walk.support_ne_nil := by
      intro hx'
      exact hxFinish (hx'.trans hlast)
    exact DirectedPath.FinitePath.firstHit_no_mem_before
      (linkageFinitePath hW p) B (linkageFinitePath_meets_target hW p)
      (List.mem_dropLast_of_mem_of_ne_getLast hx hxLast) hxB
  · intro x hx
    have hxFinish : x = (rightTightenedPath hW p).finish :=
      Set.mem_singleton_iff.mp hx
    subst x
    exact ⟨(rightTightenedPath hW p).finish_mem_support,
      rightTightenedPath_finish_mem hW p⟩

/-- Tighten every member of a linkage at the first visit to its right
boundary.  This is the pruning step implicit before the two path families
are concatenated in Assertion 9.15. -/
noncomputable def rightTightenedFamily
    {Gamma : DWeb V} {A B : Set V} {W : Set Gamma.DPath}
    (hW : IsLinkageBetween Gamma A B W) : Set Gamma.DPath :=
  Set.range fun p : W ↦
    (Sum.inl (rightTightenedPath hW p) : Gamma.DPath)

/-- First-hit pruning turns any linkage into a tight linkage with the same
left and right boundary sets. -/
theorem tightLinkageBetween_rightTightenedFamily
    {Gamma : DWeb V} {A B : Set V} {W : Set Gamma.DPath}
    (hW : IsLinkageBetween Gamma A B W) :
    SliceSpliceSource.TightLinkageBetween Gamma A B
      (rightTightenedFamily hW) := by
  have hsource (p : W) :
      (rightTightenedPath hW p).support ∩ A =
        {(rightTightenedPath hW p).start} := by
    obtain ⟨f, hpf, _hends, hfsource⟩ := hW.endpointPure p.1 p.2
    have hfeq : f = linkageFinitePath hW p := by
      apply Sum.inl.inj
      exact hpf.symm.trans (linkageFinitePath_spec hW p)
    subst f
    apply Set.Subset.antisymm
    · rintro x ⟨hx, hxA⟩
      have hxold : x ∈ (linkageFinitePath hW p).support ∩ A :=
        ⟨rightTightenedPath_support_subset hW p hx, hxA⟩
      rw [hfsource] at hxold
      exact Set.mem_singleton_iff.mpr <|
        (Set.mem_singleton_iff.mp hxold).trans rfl
    · intro x hx
      have hxstart : x = (rightTightenedPath hW p).start :=
        Set.mem_singleton_iff.mp hx
      subst x
      have hold : (linkageFinitePath hW p).start ∈ A := by
        have : (linkageFinitePath hW p).start ∈
            (linkageFinitePath hW p).support ∩ A := by
          rw [hfsource]
          exact Set.mem_singleton _
        exact this.2
      exact ⟨(rightTightenedPath hW p).start_mem_support,
        rightTightenedPath_start hW p ▸
          linkageFinitePath_start hW p ▸ hold⟩
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rintro r ⟨p, rfl⟩ s ⟨q, rfl⟩ hrs
    have hpq : p.1 ≠ q.1 := by
      intro hpq
      have hpq' : p = q := Subtype.ext hpq
      subst q
      exact hrs rfl
    have hd := hW.isWarp p.2 q.2 hpq
    rw [linkageFinitePath_spec hW p,
      linkageFinitePath_spec hW q] at hd
    exact hd.mono
      (rightTightenedPath_support_subset hW p)
      (rightTightenedPath_support_subset hW q)
  · rintro r ⟨p, rfl⟩
    exact ⟨rightTightenedPath hW p, rfl⟩
  · ext x
    constructor
    · rintro ⟨r, ⟨p, rfl⟩, hrx⟩
      change (rightTightenedPath hW p).start = x at hrx
      rw [rightTightenedPath_start] at hrx
      rw [← hW.initialSet_eq]
      exact ⟨p.1, p.2, hrx⟩
    · intro hx
      have hx' : x ∈ Gamma.initialSet W := hW.initialSet_eq ▸ hx
      obtain ⟨p, hpW, hpx⟩ := hx'
      let ps : W := ⟨p, hpW⟩
      refine ⟨(Sum.inl (rightTightenedPath hW ps) : Gamma.DPath),
        ⟨ps, rfl⟩, ?_⟩
      exact (rightTightenedPath_start hW ps).trans hpx
  · rintro x ⟨r, ⟨p, rfl⟩, hrx⟩
    change some (rightTightenedPath hW p).finish = some x at hrx
    exact Option.some.inj hrx ▸ rightTightenedPath_finish_mem hW p
  · rintro r ⟨p, rfl⟩
    refine ⟨rightTightenedPath hW p, rfl, ?_, hsource p⟩
    rw [Set.inter_union_distrib_left, hsource p,
      rightTightenedPath_target_pure hW p]
    simp only [Set.singleton_union]
  · rintro r ⟨p, rfl⟩ x hx hxB
    have hx' : x ∈
        (rightTightenedPath hW p).support ∩ B := ⟨hx, hxB⟩
    rw [rightTightenedPath_target_pure hW p] at hx'
    exact congrArg some (Set.mem_singleton_iff.mp hx').symm

/-- Lifting paths out of a quotient preserves the full tight-linkage
structure, because lifting changes neither vertices nor endpoints. -/
theorem tightLinkageBetween_liftQuotientFamily
    (Q : DWeb V) (C : Set V) {A B : Set V}
    {R : Set (Q.quotient C).DPath}
    (hR : SliceSpliceSource.TightLinkageBetween
      (Q.quotient C) A B R) :
    SliceSpliceSource.TightLinkageBetween Q A B
      (Q.liftQuotientFamily C R) := by
  refine ⟨⟨hR.1.1.liftQuotientFamily Q, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rintro p ⟨q, hqR, rfl⟩
    obtain ⟨f, rfl⟩ := hR.1.2.1 hqR
    exact ⟨f.lift (fun {_ _} h ↦ Q.quotient_adj_imp h), rfl⟩
  · simpa only [Q.initialSet_liftQuotientFamily] using hR.1.2.2.1
  · simpa only [Q.terminalFrontier_liftQuotientFamily] using
      hR.1.2.2.2.1
  · rintro p ⟨q, hqR, rfl⟩
    obtain ⟨f, rfl, hends, hsource⟩ := hR.1.2.2.2.2 q hqR
    refine ⟨f.lift (fun {_ _} h ↦ Q.quotient_adj_imp h), rfl, ?_, ?_⟩
    · rw [DirectedPath.FinitePath.support_lift]
      exact hends
    · rw [DirectedPath.FinitePath.support_lift]
      exact hsource
  · rintro p ⟨q, hqR, rfl⟩ x hx hxB
    have hterm := hR.2 q hqR x (by simpa using hx) hxB
    simpa only [Q.terminal?_liftQuotientPath] using hterm

/-- Concatenate a tight source--stop-over linkage with a full linkage in
the quotient by that stop-over.  The auxiliary linkage is first tightened
at the later boundary, then lifted.  This theorem is the path-level join
used after `exists_fullAuxiliaryLinkage_of_lower` in Assertion 9.15. -/
theorem tightLinkageBetween_star_fullAuxiliary
    (Q : DWeb V) (hQ : Q.IsNormalized) {C T : Set V}
    {W : Set Q.DPath}
    (hW : SliceSpliceSource.TightLinkageBetween Q Q.source C W)
    (hsep : IsSeparatorFrom Q Q.source C)
    (htrim : IsTrimmedSeparator Q C)
    (hWT : SliceSpliceSource.MeetsOnlyAtTerminal Q W T)
    {R : Set (Q.quotient C).DPath}
    (hR : IsLinkageBetween (Q.quotient C) C T R) :
    ∃ hcompat : Q.StarCompatible W
        (Q.liftQuotientFamily C
          (rightTightenedFamily hR)),
      SliceSpliceSource.TightLinkageBetween Q Q.source T
        (Q.star hcompat) := by
  let Rtight := rightTightenedFamily hR
  have hRtight : SliceSpliceSource.TightLinkageBetween
      (Q.quotient C) C T Rtight :=
    tightLinkageBetween_rightTightenedFamily hR
  let Rlift := Q.liftQuotientFamily C Rtight
  have hRlift : SliceSpliceSource.TightLinkageBetween Q C T Rlift :=
    tightLinkageBetween_liftQuotientFamily Q C hRtight
  have hRinitial : (Q.quotient C).initialSet Rtight =
      (Q.quotient C).source := by
    rw [hRtight.1.initialSet_eq,
      SingularContinuation.quotient_source_eq_stopover Q hsep htrim]
  let hcompat : Q.StarCompatible W Rlift :=
    SingularContinuation.starCompatible_liftQuotientFamily_of_linkage
      Q hW.1 hsep htrim hW.2 hRinitial
  refine ⟨hcompat, ?_⟩
  exact SliceSpliceSource.tightLinkageBetween_star hQ Set.Subset.rfl
    hW hRlift hWT hcompat

/-- Direct wrapper for the output of `exists_fullAuxiliaryLinkage_of_lower`:
the retargeted auxiliary web has the same graph as the quotient, so its
full linkage can be tightened, lifted, and joined to the half-way linkage. -/
theorem exists_tightLinkage_of_fullAuxiliary
    (Q : DWeb V) (hQ : Q.IsNormalized) {C T : Set V}
    {W : Set Q.DPath}
    (hW : SliceSpliceSource.TightLinkageBetween Q Q.source C W)
    (hsep : IsSeparatorFrom Q Q.source C)
    (htrim : IsTrimmedSeparator Q C)
    (hWT : SliceSpliceSource.MeetsOnlyAtTerminal Q W T)
    {R : Set (auxiliaryWeb Q C T).DPath}
    (hR : IsLinkageBetween (auxiliaryWeb Q C T)
      (auxiliaryWeb Q C T).source
      (auxiliaryWeb Q C T).target R) :
    ∃ E : Set Q.DPath,
      SliceSpliceSource.TightLinkageBetween Q Q.source T E := by
  have hR' : IsLinkageBetween (Q.quotient C) C T R := by
    refine ⟨hR.isWarp, hR.finiteCharacter, ?_, ?_, ?_⟩
    · have hi := hR.initialSet_eq
      change DirectedPath.Path.initial '' R =
        (Q.quotient C).source at hi
      rw [SingularContinuation.quotient_source_eq_stopover Q hsep htrim]
        at hi
      exact hi
    · have ht := hR.terminalFrontier_subset
      change {x | ∃ p ∈ R, DirectedPath.Path.terminal? p = some x} ⊆ T
        at ht ⊢
      exact ht
    · intro p hp
      have hpure := hR.endpointPure p hp
      unfold IsPathBetween at hpure ⊢
      simp only [auxiliaryWeb_source, auxiliaryWeb_target,
        SingularContinuation.quotient_source_eq_stopover Q hsep htrim]
        at hpure
      exact hpure
  obtain ⟨hcompat, hlink⟩ :=
    tightLinkageBetween_star_fullAuxiliary Q hQ hW hsep htrim hWT hR'
  exact ⟨Q.star hcompat, hlink⟩

end SliceAuxiliaryCore
end CardinalInduction
end Erdos599
