/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.QuotientAssociativity

/-!
# Maximal quotient waves for Erdős Problem 599

This module closes Aharoni--Berger Corollary 3.28 after the concrete maximal
wave theorem.  It is separate from `RoofQuotient` because the latter is an
upstream dependency of `WaveLimits`.
-/

namespace Erdos599

open Set

universe u

namespace DWeb

variable {V : Type u} (G : DWeb V)

/-- Aharoni--Berger Corollary 3.28 for a forward-extension-maximal quotient
wave.  The intersection with `Xᶜ` in the strict-roof clause records the
represented vertex type of `G.delete X`; it is implicit in the paper. -/
theorem maximalQuotientWave_roofs_deleteWave
    {X : Set V} {U : Set (G.delete X).DPath}
    (hNoEnter : G.NoEdgeEnters G.source)
    (hSourceX : Disjoint G.source X)
    (hU : (G.delete X).IsWave U)
    (M : (G.quotient X).Wave) (hM : IsMax M) :
    (G.delete X).roof ((G.delete X).terminalFrontier U) ⊆
        G.roof ((G.quotient X).terminalFrontier M.1) ∧
      (G.delete X).strictRoof ((G.delete X).terminalFrontier U) ∩ Xᶜ ⊆
        G.strictRoof ((G.quotient X).terminalFrontier M.1) := by
  let hGreatest : ∀ R : Set (G.quotient X).DPath,
      (G.quotient X).IsWave R → (G.quotient X).RoofLE R M.1 :=
    fun R hR ↦ (G.quotient X).roofLE_of_isMax hM ⟨R, hR⟩
  exact ⟨
    G.delete_roof_subset_original_roof_of_roofGreatest_quotient
      hNoEnter hSourceX hU M.2 hGreatest,
    G.delete_strictRoof_subset_original_strictRoof_of_roofGreatest_quotient
      hNoEnter hSourceX hU M.2 hGreatest⟩

/-! ## Quotienting an arbitrary wave -/

/-- The normalized quotient-source formula does not require the commitment
set to be disjoint from the old source.  This strengthening is needed when
Lemma 3.5 is applied inside an earlier quotient. -/
theorem essential_union_eq_union_sdiff_strictRoof_of_noEdgeEnters_general
    {A X : Set V} (hA : G.NoEdgeEnters A) :
    G.essential (A ∪ X) = (A ∪ X) \ G.strictRoof X := by
  apply Set.Subset.antisymm
  · intro x hx
    refine ⟨hx.1, ?_⟩
    intro hxStrict
    apply hx.2
    by_cases hxX : x ∈ X
    · apply G.roof_mono (show X \ {x} ⊆ (A ∪ X) \ {x} by
        intro y hy
        exact ⟨Or.inr hy.1, hy.2⟩)
      by_contra hxNotRoof
      exact hxStrict.2 ⟨hxX, hxNotRoof⟩
    · apply G.roof_mono (show X ⊆ (A ∪ X) \ {x} by
        intro y hyX
        exact ⟨Or.inr hyX, fun hyx ↦ hxX (hyx ▸ hyX)⟩)
      exact hxStrict.1
  · rintro x ⟨hxAorX, hxNotStrict⟩
    refine ⟨hxAorX, ?_⟩
    by_cases hxX : x ∈ X
    · have hxEssX : x ∈ G.essential X := by
        by_contra hxNotEss
        exact hxNotStrict ⟨G.subset_roof X hxX, hxNotEss⟩
      obtain ⟨p, hp, hpAvoid⟩ :=
        (G.not_mem_roof_iff (X \ {x}) x).1 hxEssX.2
      apply (G.not_mem_roof_iff ((A ∪ X) \ {x}) x).2
      refine ⟨p, hp, ?_⟩
      apply Set.disjoint_left.2
      intro y hyp hy
      rcases hy.1 with hyA | hyX
      · by_cases hxA : x ∈ A
        · have hpStartA : p.start ∈ A := hp.1 ▸ hxA
          have hyStart :=
            G.targetPath_meets_noEdgeEnters_only_at_start hA p hpStartA hyp hyA
          exact hy.2 (hyStart.trans hp.1)
        · have hpStartNotA : p.start ∉ A :=
            fun hpStartA ↦ hxA (hp.1 ▸ hpStartA)
          exact G.walk_avoids_of_noEdgeEnters hA p.walk hpStartNotA hyp hyA
      · exact Set.disjoint_left.1 hpAvoid hyp ⟨hyX, hy.2⟩
    · have hxA : x ∈ A := hxAorX.resolve_right hxX
      have hxNotEssX : x ∉ G.essential X := fun hxEss ↦ hxX hxEss.1
      have hxNotRoofX : x ∉ G.roof X := by
        intro hxRoof
        exact hxNotStrict ⟨hxRoof, hxNotEssX⟩
      obtain ⟨p, hp, hpAvoidX⟩ := (G.not_mem_roof_iff X x).1 hxNotRoofX
      apply (G.not_mem_roof_iff ((A ∪ X) \ {x}) x).2
      refine ⟨p, hp, ?_⟩
      apply Set.disjoint_left.2
      intro y hyp hy
      rcases hy.1 with hyA | hyX
      · have hpStartA : p.start ∈ A := hp.1 ▸ hxA
        have hyStart :=
          G.targetPath_meets_noEdgeEnters_only_at_start hA p hpStartA hyp hyA
        exact hy.2 (hyStart.trans hp.1)
      · exact Set.disjoint_left.1 hpAvoidX hyp hyX

theorem quotient_source_eq_union_sdiff_strictRoof_of_noEdgeEnters_general
    {X : Set V} (hA : G.NoEdgeEnters G.source) :
    (G.quotient X).source = (G.source ∪ X) \ G.strictRoof X := by
  rw [G.quotient_source]
  exact G.essential_union_eq_union_sdiff_strictRoof_of_noEdgeEnters_general hA

/-- Quotients preserve the standard no-incoming-source normalization. -/
theorem NoEdgeEnters.quotient {X : Set V}
    (hA : G.NoEdgeEnters G.source) :
    (G.quotient X).NoEdgeEnters (G.quotient X).source := by
  rw [G.quotient_source_eq_union_sdiff_strictRoof_of_noEdgeEnters_general hA]
  intro u v huv hv
  rcases hv.1 with hvA | hvX
  · exact hA huv.1 hvA
  · exact huv.2.2.2 hvX

/-- The terminal component of a finite path after quotienting by `X`: if
the path meets `roof X`, retain the suffix from its last such vertex. -/
noncomputable def terminalRoofSuffix (X : Set V)
    (p : DirectedPath.FinitePath G.graph) : DirectedPath.FinitePath G.graph := by
  classical
  exact if h : p.walk.Meets (G.roof X) then p.lastHit (G.roof X) h else p

@[simp] theorem terminalRoofSuffix_finish (X : Set V)
    (p : DirectedPath.FinitePath G.graph) :
    (G.terminalRoofSuffix X p).finish = p.finish := by
  classical
  simp only [terminalRoofSuffix]
  split <;> rfl

theorem terminalRoofSuffix_support_subset (X : Set V)
    (p : DirectedPath.FinitePath G.graph) :
    (G.terminalRoofSuffix X p).support ⊆ p.support := by
  classical
  simp only [terminalRoofSuffix]
  split
  · exact p.lastHit_support_subset _ _
  · exact Set.Subset.rfl

theorem terminalRoofSuffix_start_mem_source_or_essential
    (X : Set V) (p : DirectedPath.FinitePath G.graph)
    (hpstart : p.start ∈ G.source) (hpfinish : p.finish ∉ G.strictRoof X) :
    (G.terminalRoofSuffix X p).start ∈
      G.source \ G.strictRoof X ∪ G.essential X := by
  classical
  simp only [terminalRoofSuffix]
  split
  next hmeet =>
    have hlast := G.canonicalLastRoofHit_mem_essential_or_finish X p hmeet
    rcases hlast with hEss | hfinish
    · exact Or.inr hEss
    · have hs : (p.lastHit (G.roof X) hmeet).start = p.finish :=
        Set.mem_singleton_iff.1 hfinish
      rw [hs]
      have hroof : p.finish ∈ G.roof X := by
        rw [← hs]
        exact p.lastHit_start_mem _ _
      apply Or.inr
      by_contra hnotEss
      exact hpfinish ⟨hroof, hnotEss⟩
  next hnot =>
    refine Or.inl ⟨hpstart, ?_⟩
    intro hstrict
    exact hnot ⟨p.start, p.start_mem_support, hstrict.1⟩

theorem pathQuotientAdmissible_terminalRoofSuffix
    (X : Set V) (p : DirectedPath.FinitePath G.graph)
    (hpfinish : p.finish ∉ G.strictRoof X) :
    G.PathQuotientAdmissible X (.inl (G.terminalRoofSuffix X p)) := by
  classical
  rw [terminalRoofSuffix]
  split
  next hmeet =>
    change (∀ {x}, x ∈ (p.lastHit (G.roof X) hmeet).walk.support →
        x ∉ G.strictRoof X) ∧
      ∀ {x}, x ∈ (p.lastHit (G.roof X) hmeet).walk.support.tail → x ∉ X
    constructor
    · intro x hx hstrict
      have hxCases := (RelationalRoof.mem_support_iff_start_or_mem_tail
        G.graph.Adj (p.lastHit (G.roof X) hmeet).walk).1 hx
      rcases hxCases with hxstart | hxtail
      · have hxroof : x ∈ G.roof X := hxstart ▸ p.lastHit_start_mem _ _
        have hxEss : x ∈ G.essential X := by
          have hlast := G.canonicalLastRoofHit_mem_essential_or_finish X p hmeet
          rcases hlast with hEss | hfinish
          · exact hxstart ▸ hEss
          · have hs : (p.lastHit (G.roof X) hmeet).start = p.finish :=
              Set.mem_singleton_iff.1 hfinish
            have hxf : x = p.finish := hxstart.trans hs
            by_contra hnotEss
            exact hpfinish ⟨hxf ▸ hxroof, hxf ▸ hnotEss⟩
        exact hstrict.2 hxEss
      · exact p.lastHit_no_mem_after (G.roof X) hmeet hxtail hstrict.1
    · intro x hx hxX
      exact p.lastHit_no_mem_after (G.roof X) hmeet hx (G.subset_roof X hxX)
  next hnot =>
    change (∀ {x}, x ∈ p.walk.support → x ∉ G.strictRoof X) ∧
      ∀ {x}, x ∈ p.walk.support.tail → x ∉ X
    constructor
    · intro x hx hstrict
      exact hnot ⟨x, hx, hstrict.1⟩
    · intro x hx hxX
      exact hnot ⟨x, List.mem_of_mem_tail hx, G.subset_roof X hxX⟩

/-- The terminal components of the finite members of a warp whose
terminals survive the quotient. -/
def terminalSuffixFamily (X : Set V) (U : Set G.DPath) : Set G.DPath :=
  {q | ∃ p : DirectedPath.FinitePath G.graph,
    (.inl p : G.DPath) ∈ U ∧ p.finish ∉ G.strictRoof X ∧
      q = .inl (G.terminalRoofSuffix X p)}

theorem IsWarp.terminalSuffixFamily {X : Set V} {U : Set G.DPath}
    (hU : G.IsWarp U) : G.IsWarp (G.terminalSuffixFamily X U) := by
  rintro q ⟨p, hpU, _hpfin, rfl⟩ r ⟨s, hsU, _hsfin, rfl⟩ hne
  have hps : (.inl p : G.DPath) ≠ .inl s := by
    intro h
    have : p = s := Sum.inl.inj h
    subst s
    exact hne rfl
  exact (hU hpU hsU hps).mono (G.terminalRoofSuffix_support_subset X p)
    (G.terminalRoofSuffix_support_subset X s)

theorem pathQuotientAdmissible_terminalSuffixFamily
    (X : Set V) (U : Set G.DPath) :
    ∀ q ∈ G.terminalSuffixFamily X U, G.PathQuotientAdmissible X q := by
  rintro q ⟨p, _hpU, hpfin, rfl⟩
  exact G.pathQuotientAdmissible_terminalRoofSuffix X p hpfin

/-- The concrete quotient `U/X` used in source Lemma 3.5. -/
noncomputable def generalWaveQuotient (X : Set V) (U : Set G.DPath) :
    Set (G.quotient X).DPath :=
  G.admissibleWarpQuotient X (G.terminalSuffixFamily X U)
    (G.pathQuotientAdmissible_terminalSuffixFamily X U)

theorem terminalFrontier_terminalSuffixFamily (X : Set V) (U : Set G.DPath) :
    G.terminalFrontier (G.terminalSuffixFamily X U) =
      G.terminalFrontier U \ G.strictRoof X := by
  ext x
  constructor
  · rintro ⟨q, ⟨p, hpU, hpfin, rfl⟩, hqx⟩
    have hfinish : p.finish = x := by
      simpa only [G.terminal?_finite, G.terminalRoofSuffix_finish,
        Option.some.injEq] using hqx
    exact ⟨⟨.inl p, hpU, by simpa [hfinish]⟩, hfinish ▸ hpfin⟩
  · rintro ⟨⟨q, hqU, hqx⟩, hx⟩
    rcases q with p | r
    · have hfinish : p.finish = x := Option.some.inj hqx
      refine ⟨.inl (G.terminalRoofSuffix X p),
        ⟨p, hqU, hfinish ▸ hx, rfl⟩, ?_⟩
      simpa [hfinish]
    · simp at hqx

theorem initialSet_terminalSuffixFamily_subset
    {X : Set V} {U : Set G.DPath} (hU : G.IsWave U) :
    G.initialSet (G.terminalSuffixFamily X U) ⊆
      G.source \ G.strictRoof X ∪ G.essential X := by
  rintro x ⟨q, ⟨p, hpU, hpfin, rfl⟩, hqx⟩
  have hpstart : p.start ∈ G.source := hU.2.1 ⟨.inl p, hpU, rfl⟩
  exact hqx ▸
    G.terminalRoofSuffix_start_mem_source_or_essential X p hpstart hpfin

theorem vertexSet_terminalSuffixFamily_subset (X : Set V) (U : Set G.DPath) :
    G.vertexSet (G.terminalSuffixFamily X U) ⊆ G.vertexSet U := by
  rintro x ⟨q, ⟨p, hpU, _hpfin, rfl⟩, hxq⟩
  exact ⟨.inl p, hpU, G.terminalRoofSuffix_support_subset X p hxq⟩

theorem roof_sdiff_strictRoof_subset_quotient_roof (X S : Set V) :
    G.roof S \ G.strictRoof X ⊆
      (G.quotient X).roof (S \ G.strictRoof X) := by
  rintro v ⟨hvRoof, hvStrict⟩ p hp
  let q : DirectedPath.FinitePath G.graph :=
    p.lift (fun {_ _} (h : (G.quotient X).graph.Adj _ _) ↦ h.1)
  obtain ⟨x, hxq, hxS⟩ := hvRoof q ⟨hp.1, hp.2⟩
  have hxp : x ∈ p.support := by
    simpa only [q, DirectedPath.FinitePath.support_lift] using hxq
  refine ⟨x, hxp, hxS, ?_⟩
  by_cases hxv : x = v
  · exact hxv ▸ hvStrict
  · exact (G.quotientPath_avoids_after_initial X (.inl p) hxp
      (by simpa only [DirectedPath.Path.initial, hp.1] using hxv)).1

theorem isWarp_generalWaveQuotient {X : Set V} {U : Set G.DPath}
    (hU : G.IsWarp U) :
    (G.quotient X).IsWarp (G.generalWaveQuotient X U) := by
  exact IsWarp.admissibleWarpQuotient G (IsWarp.terminalSuffixFamily G hU)
    (G.pathQuotientAdmissible_terminalSuffixFamily X U)

theorem terminalFrontier_generalWaveQuotient (X : Set V) (U : Set G.DPath) :
    (G.quotient X).terminalFrontier (G.generalWaveQuotient X U) =
      (G.terminalFrontier U \ G.strictRoof X) ∪
        (G.essential X \ G.vertexSet (G.terminalSuffixFamily X U)) := by
  rw [generalWaveQuotient, G.terminalFrontier_admissibleWarpQuotient,
    G.terminalFrontier_terminalSuffixFamily]

theorem initialSet_generalWaveQuotient_subset_source
    {X : Set V} {U : Set G.DPath}
    (hNoEnter : G.NoEdgeEnters G.source) (hU : G.IsWave U) :
    (G.quotient X).initialSet (G.generalWaveQuotient X U) ⊆
      (G.quotient X).source := by
  rw [G.quotient_source_eq_union_sdiff_strictRoof_of_noEdgeEnters_general
    hNoEnter]
  rw [generalWaveQuotient, G.initialSet_admissibleWarpQuotient]
  rintro x (hx | hx)
  · rcases G.initialSet_terminalSuffixFamily_subset hU hx with hxA | hxEss
    · exact ⟨Or.inl hxA.1, hxA.2⟩
    · exact ⟨Or.inr hxEss.1, fun hstrict ↦ hstrict.2 hxEss⟩
  · exact ⟨Or.inr hx.1.1, fun hstrict ↦ hstrict.2 hx.1⟩

/-- Aharoni--Berger Lemma 3.5: quotienting a wave produces a wave. -/
theorem isWave_generalWaveQuotient
    {X : Set V} {U : Set G.DPath}
    (hNoEnter : G.NoEdgeEnters G.source) (hU : G.IsWave U) :
    (G.quotient X).IsWave (G.generalWaveQuotient X U) := by
  refine ⟨G.isWarp_generalWaveQuotient hU.1,
    G.initialSet_generalWaveQuotient_subset_source hNoEnter hU, ?_⟩
  rw [G.quotient_source_eq_union_sdiff_strictRoof_of_noEdgeEnters_general
    hNoEnter]
  rintro x ⟨hxSource | hxX, hxNotStrict⟩
  · apply (G.quotient X).roof_mono ?_
    · simpa [G.terminalFrontier_generalWaveQuotient X U] using
        (G.roof_sdiff_strictRoof_subset_quotient_roof X
          (G.terminalFrontier U) ⟨hU.2.2 hxSource, hxNotStrict⟩)
    · intro y hy
      rw [G.terminalFrontier_generalWaveQuotient X U]
      exact Or.inl hy
  · have hxEss : x ∈ G.essential X := by
      by_contra hnotEss
      exact hxNotStrict ⟨G.subset_roof X hxX, hnotEss⟩
    by_cases hxUsed : x ∈ G.vertexSet (G.terminalSuffixFamily X U)
    · have hxOldVertex : x ∈ G.vertexSet U :=
        G.vertexSet_terminalSuffixFamily_subset X U hxUsed
      have hxNotStrict' : x ∉ G.strictRoof X :=
        Set.disjoint_left.1
          (G.vertexSet_disjoint_strictRoof_of_pathQuotientAdmissible
            (G.pathQuotientAdmissible_terminalSuffixFamily X U)) hxUsed
      apply (G.quotient X).roof_mono ?_
      · simpa [G.terminalFrontier_generalWaveQuotient X U] using
          (G.roof_sdiff_strictRoof_subset_quotient_roof X
            (G.terminalFrontier U)
              ⟨DWeb.IsWave.self_roofing (Γ := G) hU hxOldVertex,
                hxNotStrict'⟩)
      · intro y hy
        rw [G.terminalFrontier_generalWaveQuotient X U]
        exact Or.inl hy
    · apply (G.quotient X).subset_roof _
      rw [G.terminalFrontier_generalWaveQuotient X U]
      exact Or.inr ⟨hxEss, hxUsed⟩

/-! ## Common-quotient arrows -/

/-- Common-web core of source Lemma 3.29: the arrow of two waves is a wave
whose roof contains both old roofs.  Corollary 2.28 supplies the separate
transport of waves from smaller quotients into this common quotient. -/
theorem isWave_arrow_and_roofs
    {U W : Set G.DPath} (hU : G.IsWave U) (hW : G.IsWave W) :
    G.IsWave (G.arrow U W) ∧
      G.roof (G.terminalFrontier U) ∪
          G.roof (G.terminalFrontier W) ⊆
        G.roof (G.terminalFrontier (G.arrow U W)) := by
  refine ⟨G.isWave_arrow hU hW, ?_⟩
  intro x hx
  rw [G.roof_terminalFrontier_arrow_eq_union hU hW]
  rcases hx with hx | hx
  · exact G.roof_mono Set.subset_union_left hx
  · exact G.roof_mono Set.subset_union_right hx

/-- The left wave in source Lemma 3.29, quotiented once more and transported
through the left-hand equality of Corollary 2.28. -/
noncomputable def commonQuotientLeft
    {X₁ X₂ : Set V}
    (hNoEnter : G.NoEdgeEnters G.source)
    (hSource : Disjoint G.source (X₁ ∪ X₂))
    (W₁ : (G.quotient X₁).Wave) :
    (G.quotient (G.essential (X₁ ∪ X₂))).Wave := by
  let Y := G.essential (X₁ ∪ X₂)
  let Q : ((G.quotient X₁).quotient Y).Wave :=
    ⟨(G.quotient X₁).generalWaveQuotient Y W₁.1,
      (G.quotient X₁).isWave_generalWaveQuotient
        (DWeb.NoEdgeEnters.quotient G hNoEnter) W₁.2⟩
  have hEq : (G.quotient X₁).quotient Y = G.quotient Y := by
    simpa only [Y] using
      G.quotient_quotient_essential_union_left X₁ X₂ hNoEnter hSource
  exact hEq ▸ Q

/-- The right wave in source Lemma 3.29, transported to the same quotient. -/
noncomputable def commonQuotientRight
    {X₁ X₂ : Set V}
    (hNoEnter : G.NoEdgeEnters G.source)
    (hSource : Disjoint G.source (X₁ ∪ X₂))
    (W₂ : (G.quotient X₂).Wave) :
    (G.quotient (G.essential (X₁ ∪ X₂))).Wave := by
  let Y := G.essential (X₁ ∪ X₂)
  let Q : ((G.quotient X₂).quotient Y).Wave :=
    ⟨(G.quotient X₂).generalWaveQuotient Y W₂.1,
      (G.quotient X₂).isWave_generalWaveQuotient
        (DWeb.NoEdgeEnters.quotient G hNoEnter) W₂.2⟩
  have hEq : (G.quotient X₂).quotient Y = G.quotient Y := by
    simpa only [Y] using
      G.quotient_quotient_essential_union_right X₁ X₂ hNoEnter hSource
  exact hEq ▸ Q

/-- Aharoni--Berger Lemma 3.29: after transporting two quotient waves to
the common quotient of Corollary 2.28, their up-arrow is again a wave. -/
noncomputable def commonQuotientArrow
    {X₁ X₂ : Set V}
    (hNoEnter : G.NoEdgeEnters G.source)
    (hSource : Disjoint G.source (X₁ ∪ X₂))
    (W₁ : (G.quotient X₁).Wave) (W₂ : (G.quotient X₂).Wave) :
    (G.quotient (G.essential (X₁ ∪ X₂))).Wave :=
  let H := G.quotient (G.essential (X₁ ∪ X₂))
  let U := G.commonQuotientLeft hNoEnter hSource W₁
  let W := G.commonQuotientRight hNoEnter hSource W₂
  ⟨H.arrow U.1 W.1, H.isWave_arrow U.2 W.2⟩

/-- The two transported roofs are contained in the roof of the common
up-arrow, which is the roof clause of source Lemma 3.29. -/
theorem commonQuotientArrow_roofs
    {X₁ X₂ : Set V}
    (hNoEnter : G.NoEdgeEnters G.source)
    (hSource : Disjoint G.source (X₁ ∪ X₂))
    (W₁ : (G.quotient X₁).Wave) (W₂ : (G.quotient X₂).Wave) :
    let H := G.quotient (G.essential (X₁ ∪ X₂))
    H.RoofLE (G.commonQuotientLeft hNoEnter hSource W₁).1
        (G.commonQuotientArrow hNoEnter hSource W₁ W₂).1 ∧
      H.RoofLE (G.commonQuotientRight hNoEnter hSource W₂).1
        (G.commonQuotientArrow hNoEnter hSource W₁ W₂).1 := by
  dsimp only [commonQuotientArrow]
  constructor
  · exact
      (G.quotient (G.essential (X₁ ∪ X₂))).roofLE_of_forwardExtension
        (G.commonQuotientArrow hNoEnter hSource W₁ W₂).2
        ((G.quotient (G.essential (X₁ ∪ X₂))).forwardExtension_arrow _ _)
  · exact (G.quotient (G.essential (X₁ ∪ X₂))).roofLE_arrow_right
      (G.commonQuotientLeft hNoEnter hSource W₁).2
      (G.commonQuotientRight hNoEnter hSource W₂).2

/-- Finite stages of the recursively accumulated countable up-arrow. -/
noncomputable def omegaArrowStage (G : DWeb V) (W : ℕ → G.Wave) :
    ℕ → G.Wave
  | 0 => W 0
  | n + 1 =>
      ⟨G.arrow (G.omegaArrowStage W n).1 (W (n + 1)).1,
        G.isWave_arrow (G.omegaArrowStage W n).2 (W (n + 1)).2⟩

@[simp] theorem omegaArrowStage_zero (W : ℕ → G.Wave) :
    G.omegaArrowStage W 0 = W 0 := by
  rw [omegaArrowStage]

@[simp] theorem omegaArrowStage_succ (W : ℕ → G.Wave) (n : ℕ) :
    G.omegaArrowStage W (n + 1) =
      ⟨G.arrow (G.omegaArrowStage W n).1 (W (n + 1)).1,
        G.isWave_arrow (G.omegaArrowStage W n).2 (W (n + 1)).2⟩ := by
  rw [omegaArrowStage]

theorem omegaArrowStage_forward_succ (W : ℕ → G.Wave) (n : ℕ) :
    G.omegaArrowStage W n ≤ G.omegaArrowStage W (n + 1) := by
  rw [G.omegaArrowStage_succ]
  exact G.forwardExtension_arrow _ _

theorem omegaArrowStage_mono (W : ℕ → G.Wave) :
    Monotone (G.omegaArrowStage W) := by
  intro m n hmn
  induction n, hmn using Nat.le_induction with
  | base => exact le_rfl
  | succ n hmn ih =>
      exact le_trans ih (G.omegaArrowStage_forward_succ W n)

theorem omegaArrowStage_range_isChain (W : ℕ → G.Wave) :
    IsChain (· ≤ ·) (Set.range (G.omegaArrowStage W)) := by
  rintro U ⟨i, rfl⟩ R ⟨j, rfl⟩ _hne
  rcases le_total i j with hij | hji
  · exact Or.inl (G.omegaArrowStage_mono W hij)
  · exact Or.inr (G.omegaArrowStage_mono W hji)

theorem omegaArrowStage_range_nonempty (W : ℕ → G.Wave) :
    (Set.range (G.omegaArrowStage W)).Nonempty :=
  ⟨G.omegaArrowStage W 0, ⟨0, rfl⟩⟩

/-- The countable iterated up-arrow, formed as the direct limit of its
finite accumulated stages. -/
noncomputable def omegaArrow (W : ℕ → G.Wave) : G.Wave :=
  G.waveChainUpperWave (Set.range (G.omegaArrowStage W))
    (G.omegaArrowStage_range_nonempty W)
    (G.omegaArrowStage_range_isChain W)

/-- Common-web core of source Lemma 3.30: a countable up-arrow of waves in
one web is a wave. -/
theorem isWave_omegaArrow (W : ℕ → G.Wave) :
    G.IsWave (G.omegaArrow W).1 :=
  (G.omegaArrow W).2

/-- Every input wave lies below the countable up-arrow in roof order. -/
theorem roofLE_omegaArrow (W : ℕ → G.Wave) (n : ℕ) :
    G.RoofLE (W n).1 (G.omegaArrow W).1 := by
  let c := Set.range (G.omegaArrowStage W)
  let hcne := G.omegaArrowStage_range_nonempty W
  let hc := G.omegaArrowStage_range_isChain W
  have hstage : G.ForwardExtension (G.omegaArrowStage W n).1
      (G.omegaArrow W).1 := by
    exact G.le_waveChainUpperWave c hcne hc
      (Set.mem_range_self n)
  have hstageRoof : G.RoofLE (G.omegaArrowStage W n).1
      (G.omegaArrow W).1 :=
    G.roofLE_of_forwardExtension (G.omegaArrow W).2 hstage
  cases n with
  | zero => simpa using hstageRoof
  | succ n =>
      rw [G.omegaArrowStage_succ] at hstageRoof
      exact (G.roofLE_arrow_right
        (G.omegaArrowStage W n).2 (W (n + 1)).2).trans hstageRoof

end DWeb
end Erdos599
