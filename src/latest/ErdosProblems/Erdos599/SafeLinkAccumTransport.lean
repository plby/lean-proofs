/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SafeLinkClosureFinal

/-!
# Pathwise transport for the dependent Section 6 accumulation

This file packages two path-level consequences of the accumulated-wave
construction.  First, an essential member of the final countable arrow has,
at every sufficiently late finite arrow stage, a representative with exactly
the same support and terminal.  Second, a surviving finite member of a
dependent stage is transported to, and absorbed by, the chosen successor
wave.
-/

noncomputable section

namespace Erdos599

open Set DirectedPath

universe u

namespace DWeb

variable {V : Type u} (G : DWeb V)

/-- Strong pathwise form of finite stabilization in the countable arrow.

The support inclusion supplied by
`exists_later_omegaArrowStage_path_supporting_essential` is actually an
equality.  Indeed, the late-stage member extends to the final warp; since it
already meets the essential final member, disjointness of that warp forces
the extension to be that member itself.  Simplicity of the finite path then
prevents a proper prefix from containing its final vertex. -/
theorem exists_later_omegaArrowStage_path_same_support_terminal_of_essential
    (W : ℕ → G.Wave) (k : ℕ) {q : G.DPath}
    (hq : q ∈ G.essentialWarpPart (G.omegaArrow W).1) :
    ∃ m, k ≤ m ∧ ∃ p ∈ (G.omegaArrowStage W m).1,
      p.support = q.support ∧ G.terminal? p = G.terminal? q := by
  obtain ⟨m, hkm, p, hpStage, hqp⟩ :=
    G.exists_later_omegaArrowStage_path_supporting_essential W k hq
  obtain ⟨hqFinal, t, hqt, _htEssential⟩ := hq
  let c := Set.range (G.omegaArrowStage W)
  have hcne : c.Nonempty := G.omegaArrowStage_range_nonempty W
  have hc := G.omegaArrowStage_range_isChain W
  have hmFinal : G.ForwardExtension (G.omegaArrowStage W m).1
      (G.omegaArrow W).1 := by
    exact G.le_waveChainUpperWave c hcne hc (Set.mem_range_self m)
  obtain ⟨r, hrFinal, hpr⟩ := hmFinal.1 p hpStage
  have hqInitial : q.initial ∈ q.support := q.initial_mem_support
  have hpInitial : q.initial ∈ p.support := hqp hqInitial
  have hrInitial : q.initial ∈ r.support :=
    G.support_mono_of_extends hpr hpInitial
  have hrq : r = q := by
    by_contra hne
    exact Set.disjoint_left.1
      ((G.omegaArrow W).2.1 hrFinal hqFinal hne)
      hrInitial hqInitial
  subst r
  have hpq : G.Extends p q := hpr
  have hpqSupport : p.support ⊆ q.support :=
    G.support_mono_of_extends hpq
  have hsupport : p.support = q.support :=
    Set.Subset.antisymm hpqSupport hqp
  rcases hpPath : p with pf | pr
  · rcases hqPath : q with qf | qr
    · have hpqPrefix : pf.IsPrefixOf qf := by
        have hpq' : DirectedPath.Path.Extends (.inl pf) (.inl qf) := by
          simpa only [hpPath, hqPath] using hpq
        exact (DirectedPath.Path.extends_finite_finite pf qf).1 hpq'
      have hordered : pf.walk.support = qf.walk.support := by
        apply List.Nodup.eq_of_getLast_mem_of_prefix hpqPrefix
        · rw [qf.walk.getLast_support]
          have : qf.finish ∈ (p.support : Set V) := by
            rw [hsupport, hqPath]
            exact qf.finish_mem_support
          rw [hpPath] at this
          exact this
        · exact qf.isPath
      have hterminal : G.terminal? p = G.terminal? q := by
        simp only [hpPath, hqPath, G.terminal?_finite,
          Option.some.injEq]
        calc
          pf.finish = pf.walk.support.getLast pf.walk.support_ne_nil :=
            pf.walk.getLast_support.symm
          _ = qf.walk.support.getLast qf.walk.support_ne_nil :=
            List.getLast_congr pf.walk.support_ne_nil
              qf.walk.support_ne_nil hordered
          _ = qf.finish := qf.walk.getLast_support
      refine ⟨m, hkm, p, hpStage, ?_, ?_⟩
      · simpa only [hqPath] using hsupport
      · simpa only [hqPath] using hterminal
    · rw [hqPath] at hqt
      simp at hqt
  · rcases hqPath : q with qf | qr
    · exact (DirectedPath.Path.not_extends_ray_finite pr qf
        (by simpa only [hpPath, hqPath] using hpq)).elim
    · have hterminal : G.terminal? p = G.terminal? q := by
        simp only [hpPath, hqPath, G.terminal?_ray]
      refine ⟨m, hkm, p, hpStage, ?_, ?_⟩
      · simpa only [hqPath] using hsupport
      · simpa only [hqPath] using hterminal

private theorem initial_castWebPath {H K : DWeb V} (h : H = K)
    (p : H.DPath) : (h ▸ p).initial = p.initial := by
  subst K
  rfl

/-- Trimming successively by nested roofs has the same retained support as
trimming directly by the larger roof.  This is the support-level associativity
needed to carry a pre-entry predecessor through several dependent quotient
stages. -/
theorem terminalRoofSuffix_terminalRoofSuffix_support_eq
    {R S : Set V} (hRS : G.roof R ⊆ G.roof S)
    (p : DirectedPath.FinitePath G.graph) :
    (G.terminalRoofSuffix S (G.terminalRoofSuffix R p)).support =
      (G.terminalRoofSuffix S p).support := by
  classical
  by_cases hS : p.walk.Meets (G.roof S)
  · by_cases hR : p.walk.Meets (G.roof R)
    · let r := p.lastHit (G.roof R) hR
      have hSr : r.walk.Meets (G.roof S) := by
        let s := p.lastHit (G.roof S) hS
        refine ⟨s.start, ?_, p.lastHit_start_mem (G.roof S) hS⟩
        have hsSubset : s.support ⊆ r.support := by
          simpa only [r, s, terminalRoofSuffix, dif_pos hS, dif_pos hR] using
            G.terminalRoofSuffix_support_mono hRS p
        exact hsSubset s.start_mem_support
      have hrEq : G.terminalRoofSuffix R p = r := by
        simp only [terminalRoofSuffix, dif_pos hR, r]
      rw [hrEq, terminalRoofSuffix, dif_pos hSr,
        terminalRoofSuffix, dif_pos hS]
      let Lr := p.walk.lastHit (G.roof R) hR
      let L := Lr.walk.lastHit (G.roof S) hSr
      let L' : p.walk.LastHit (G.roof S) :=
        { startpoint := L.startpoint
          walk := L.walk
          startpoint_mem := L.startpoint_mem
          support_suffix := L.support_suffix.trans Lr.support_suffix
          no_mem_after := L.no_mem_after }
      have hlist := DirectedPath.FinitePath.lastHit_support_eq L'
        (p.walk.lastHit (G.roof S) hS)
      ext v
      change v ∈ L.walk.support ↔
        v ∈ (p.walk.lastHit (G.roof S) hS).walk.support
      rw [hlist]
    · have hrEq : G.terminalRoofSuffix R p = p := by
        simp only [terminalRoofSuffix, dif_neg hR]
      rw [hrEq]
  · have hR : ¬p.walk.Meets (G.roof R) := by
      intro h
      obtain ⟨x, hxp, hxR⟩ := h
      exact hS ⟨x, hxp, hRS hxR⟩
    have hrEq : G.terminalRoofSuffix R p = p := by
      simp only [terminalRoofSuffix, dif_neg hR]
    rw [hrEq, terminalRoofSuffix, dif_neg hS]

/-- Cross-quotient support preservation for terminal-roof trimming.

Suppose `X ⊆ Y ⊆ Z`.  A finite path in `G / Z` which starts in `X`
meets the roof of `Y`, as computed in `G / X`, only at its initial vertex.
Consequently any finite `G / X` path with the same support retains its whole
support when it is trimmed for transport through the intermediate quotient
by `Y`. -/
theorem terminalRoofSuffix_support_eq_of_crossQuotient
    (hNoEnter : G.NoEdgeEnters G.source)
    {X Y Z : Set V} (hXY : X ⊆ Y) (hYZ : Y ⊆ Z)
    (p : DirectedPath.FinitePath (G.quotient Z).graph)
    (q : DirectedPath.FinitePath (G.quotient X).graph)
    (hpStart : p.start ∈ X) (hqp : q.support = p.support) :
    ((G.quotient X).terminalRoofSuffix Y q).support = q.support := by
  let H := G.quotient X
  have hXZ : X ⊆ Z := hXY.trans hYZ
  have heq : H.quotient Z = G.quotient Z := by
    calc
      H.quotient Z = G.quotient (X ∪ Z) :=
        G.quotient_quotient_eq_union X Z hNoEnter
      _ = G.quotient Z := by rw [Set.union_eq_right.mpr hXZ]
  let p₀ : (H.quotient Z).DPath :=
    heq.symm ▸ (Sum.inl p : (G.quotient Z).DPath)
  have hp₀Support : p₀.support = p.support := by
    calc
      p₀.support = DirectedPath.Path.support
          (Sum.inl p : (G.quotient Z).DPath) :=
        DWeb.support_castWebPath heq.symm _
      _ = p.support := rfl
  have hp₀Initial : p₀.initial = p.start := by
    calc
      p₀.initial = DirectedPath.Path.initial
          (Sum.inl p : (G.quotient Z).DPath) :=
        initial_castWebPath heq.symm _
      _ = p.start := rfl
  have hqStart : q.start = p.start := by
    by_contra hne
    have hpq : p.start ∈ q.support := by
      rw [hqp]
      exact p.start_mem_support
    have hav := G.quotientPath_avoids_after_initial X
      (Sum.inl q : (G.quotient X).DPath) hpq
        (fun h ↦ hne h.symm)
    exact hav.2 hpStart
  have hOnlyStart : ∀ {x : V}, x ∈ q.support →
      x ∈ H.roof Y → x = q.start := by
    intro x hxq hxRoof
    by_contra hxne
    have hxp : x ∈ p.support := hqp ▸ hxq
    have hxp₀ : x ∈ p₀.support := hp₀Support.symm ▸ hxp
    have hxne₀ : x ≠ p₀.initial := by
      rw [hp₀Initial, ← hqStart]
      exact hxne
    have hav := H.quotientPath_avoids_after_initial Z p₀ hxp₀ hxne₀
    have hxRoofZ : x ∈ H.roof Z := H.roof_mono hYZ hxRoof
    rw [show H.roof Z = H.strictRoof Z ∪ H.essential Z by
      exact RelationalRoof.roof_eq_strictRoof_union_essential
        H.graph.Adj H.target Z] at hxRoofZ
    rcases hxRoofZ with hxStrict | hxEssential
    · exact hav.1 hxStrict
    · exact hav.2 (H.essential_subset Z hxEssential)
  have hqStartRoof : q.start ∈ H.roof Y := by
    apply H.subset_roof Y
    exact hXY (hqStart ▸ hpStart)
  have hmeet : q.walk.Meets (H.roof Y) :=
    ⟨q.start, q.start_mem_support, hqStartRoof⟩
  have hstartSuffix : q.start ∈ (H.terminalRoofSuffix Y q).support := by
    rw [terminalRoofSuffix, dif_pos hmeet]
    change q.start ∈ (q.walk.lastHit (H.roof Y) hmeet).walk.support
    have hlastStart : (q.walk.lastHit (H.roof Y) hmeet).startpoint = q.start :=
      hOnlyStart
        ((q.walk.lastHit (H.roof Y) hmeet).support_subset
          (q.walk.lastHit (H.roof Y) hmeet).walk.start_mem_support)
        (q.walk.lastHit (H.roof Y) hmeet).startpoint_mem
    simpa only [hlastStart] using
      (q.walk.lastHit (H.roof Y) hmeet).walk.start_mem_support
  exact H.terminalRoofSuffix_support_eq_of_start_mem Y q hstartSuffix

/-- Every vertex of a wave in a larger quotient survives the corresponding
second quotient from a smaller commitment set.  This is the vertex-level
form of quotient associativity needed to discharge successor survival. -/
theorem not_mem_strictRoof_of_mem_crossQuotientWave
    (hNoEnter : G.NoEdgeEnters G.source) {X Y : Set V} (hXY : X ⊆ Y)
    (W : (G.quotient Y).Wave) {p : (G.quotient Y).DPath}
    (hp : p ∈ W.1) {x : V} (hxp : x ∈ p.support) :
    x ∉ (G.quotient X).strictRoof Y := by
  let H := G.quotient X
  have heq : G.quotient Y = H.quotient Y := by
    symm
    calc
      H.quotient Y = G.quotient (X ∪ Y) :=
        G.quotient_quotient_eq_union X Y hNoEnter
      _ = G.quotient Y := by rw [Set.union_eq_right.mpr hXY]
  let W₀ : (H.quotient Y).Wave := heq ▸ W
  let p₀ : (H.quotient Y).DPath := heq ▸ p
  have hp₀ : p₀ ∈ W₀.1 := DWeb.mem_castWebWave heq W hp
  have hxp₀ : x ∈ p₀.support := by
    rw [show p₀.support = p.support by
      exact DWeb.support_castWebPath heq p]
    exact hxp
  exact H.quotientWave_vertexSet_subset_quotientVertexSet
    hNoEnter.quotient W₀.2 ⟨p₀, hp₀, hxp₀⟩

/-- Exact one-successor persistence for the dependent accumulation.

The path `p` lives in a later common quotient, while `q` is its current
dependent-stage representative.  Provided the old terminal survives the
successor quotient, cross-quotient trimming preserves the complete support;
the maximal successor wave then absorbs that finite path without passing its
terminal, since that terminal is essential for `S`. -/
theorem exists_sectionSixAccumNext_path_same_support_of_common_finite
    (hNoEnter : G.NoEdgeEnters G.source)
    (F K : V → Set V) (Y Q T : Set V)
    (s : G.SectionSixAccumStage) {X S : Set V}
    (hNextX : G.sectionSixAccumNextCarrier F K Y Q T s ⊆ X)
    (p : DirectedPath.FinitePath (G.quotient X).graph)
    (q : DirectedPath.FinitePath (G.quotient s.carrier).graph)
    (hpStart : p.start ∈ s.carrier)
    (hq : (Sum.inl q : (G.quotient s.carrier).DPath) ∈ s.wave.1)
    (hSupport : q.support = p.support) (hTerminal : q.finish = p.finish)
    (hSurvives : q.finish ∉ (G.quotient s.carrier).strictRoof
      (G.sectionSixAccumNextCarrier F K Y Q T s))
    (hStrict : G.strictRoof ((G.quotient
      (G.sectionSixAccumNextCarrier F K Y Q T s)).terminalFrontier
        (G.sectionSixAccumNext hNoEnter F K Y Q T s).wave.1) ⊆
      G.strictRoof S)
    (hEssential : p.finish ∈ G.essential S) :
    ∃ r ∈ (G.sectionSixAccumNext hNoEnter F K Y Q T s).wave.1,
      r.support = p.support ∧
      (G.quotient (G.sectionSixAccumNextCarrier F K Y Q T s)).terminal? r =
        some p.finish := by
  have hCarrierNext : s.carrier ⊆
      G.sectionSixAccumNextCarrier F K Y Q T s :=
    G.sectionSixAccumStage_carrier_subset_next F K Y Q T s
  have hSuffix : ((G.quotient s.carrier).terminalRoofSuffix
      (G.sectionSixAccumNextCarrier F K Y Q T s) q).support = q.support := by
    exact G.terminalRoofSuffix_support_eq_of_crossQuotient hNoEnter
      hCarrierNext hNextX p q hpStart hSupport
  obtain ⟨r, hrOld, hrSupport, hrTerminal⟩ :=
    G.exists_mem_waveToLargerQuotient_of_old_finite hNoEnter
      (G.sectionSixAccumStage_carrier_subset_next F K Y Q T s)
      s.wave q hq hSurvives
  have hrSupportP : r.support = p.support :=
    hrSupport.trans (hSuffix.trans hSupport)
  rcases hrPath : r with rf | rr
  · have hrfFinish : rf.finish = p.finish := by
      simpa only [hrPath, DWeb.terminal?_finite, Option.some.injEq,
        hTerminal] using hrTerminal
    have hrOld' : (Sum.inl rf : (G.quotient
        (G.sectionSixAccumNextCarrier F K Y Q T s)).DPath) ∈
        (G.waveToLargerQuotient hNoEnter
          (G.sectionSixAccumStage_carrier_subset_next F K Y Q T s)
          s.wave).1 := by
      simpa only [hrPath] using hrOld
    have hForward : (G.quotient
        (G.sectionSixAccumNextCarrier F K Y Q T s)).ForwardExtension
        (G.waveToLargerQuotient hNoEnter
          (G.sectionSixAccumStage_carrier_subset_next F K Y Q T s)
          s.wave).1
        (G.sectionSixAccumNext hNoEnter F K Y Q T s).wave.1 := by
      have hOldLe :=
        G.sectionSixAccumOldInNext_le_next hNoEnter F K Y Q T s
      change (G.quotient
        (G.sectionSixAccumNextCarrier F K Y Q T s)).ForwardExtension
          (G.waveToLargerQuotient hNoEnter
            (G.sectionSixAccumStage_carrier_subset_next F K Y Q T s)
            s.wave).1
          (G.sectionSixAccumNext hNoEnter F K Y Q T s).wave.1 at hOldLe
      exact hOldLe
    obtain ⟨w, hwNext, _hrw, hwSupport, hwTerminal⟩ :=
      G.exists_quotient_forwardExtension_path_same_support_of_essential
        hNoEnter
        (G.sectionSixAccumNext hNoEnter F K Y Q T s).wave.2
        hForward
        hStrict rf hrOld'
        (hrfFinish ▸ hEssential)
    refine ⟨w, hwNext, ?_, ?_⟩
    · have hrfSupport : rf.support = p.support := by
        change DirectedPath.Path.support
            (Sum.inl rf : (G.quotient
              (G.sectionSixAccumNextCarrier F K Y Q T s)).DPath) = p.support
        simpa only [hrPath] using hrSupportP
      exact hwSupport.trans hrfSupport
    · simpa only [G.sectionSixAccumNext_carrier, hrfFinish] using hwTerminal
  · rw [hrPath] at hrTerminal
    simp at hrTerminal

/-- Successor persistence with survival discharged by membership in a wave
of the final common quotient.  In applications `W` is the relevant finite
omega-arrow stage. -/
theorem exists_sectionSixAccumNext_path_same_support_of_commonWave_finite
    (hNoEnter : G.NoEdgeEnters G.source)
    (F K : V → Set V) (Y Q T : Set V)
    (s : G.SectionSixAccumStage) {X S : Set V}
    (hNextX : G.sectionSixAccumNextCarrier F K Y Q T s ⊆ X)
    (W : (G.quotient X).Wave)
    (p : DirectedPath.FinitePath (G.quotient X).graph)
    (hp : (Sum.inl p : (G.quotient X).DPath) ∈ W.1)
    (q : DirectedPath.FinitePath (G.quotient s.carrier).graph)
    (hpStart : p.start ∈ s.carrier)
    (hq : (Sum.inl q : (G.quotient s.carrier).DPath) ∈ s.wave.1)
    (hSupport : q.support = p.support) (hTerminal : q.finish = p.finish)
    (hStrict : G.strictRoof ((G.quotient
      (G.sectionSixAccumNextCarrier F K Y Q T s)).terminalFrontier
        (G.sectionSixAccumNext hNoEnter F K Y Q T s).wave.1) ⊆
      G.strictRoof S)
    (hEssential : p.finish ∈ G.essential S) :
    ∃ r ∈ (G.sectionSixAccumNext hNoEnter F K Y Q T s).wave.1,
      r.support = p.support ∧
      (G.quotient (G.sectionSixAccumNextCarrier F K Y Q T s)).terminal? r =
        some p.finish := by
  have hCarrierX : s.carrier ⊆ X :=
    (G.sectionSixAccumStage_carrier_subset_next F K Y Q T s).trans hNextX
  have hpFinishSurvivesX : p.finish ∉
      (G.quotient s.carrier).strictRoof X :=
    G.not_mem_strictRoof_of_mem_crossQuotientWave hNoEnter
      hCarrierX W hp p.finish_mem_support
  have hStrictMono : (G.quotient s.carrier).strictRoof
      (G.sectionSixAccumNextCarrier F K Y Q T s) ⊆
      (G.quotient s.carrier).strictRoof X := by
    apply (G.quotient s.carrier).strictRoof_mono_of_roof_mono
    exact (G.quotient s.carrier).roof_mono hNextX
  have hSurvives : q.finish ∉ (G.quotient s.carrier).strictRoof
      (G.sectionSixAccumNextCarrier F K Y Q T s) := by
    intro hqStrict
    exact hpFinishSurvivesX (hTerminal ▸ hStrictMono hqStrict)
  exact G.exists_sectionSixAccumNext_path_same_support_of_common_finite
    hNoEnter F K Y Q T s hNextX p q hpStart hq hSupport hTerminal
      hSurvives hStrict hEssential

/-- Successor persistence when the protected endpoint is essential in the
final common quotient rather than in the ambient web.  Membership of `p` in
a final-quotient wave still discharges survival, while the later-essential
forward-extension lemma prevents the successor wave from passing the common
terminal. -/
theorem exists_sectionSixAccumNext_path_same_support_of_laterEssential_finite
    (hNoEnter : G.NoEdgeEnters G.source)
    (F K : V → Set V) (Y Q T : Set V)
    (s : G.SectionSixAccumStage) {X : Set V}
    (hNextX : G.sectionSixAccumNextCarrier F K Y Q T s ⊆ X)
    (W M : (G.quotient X).Wave)
    (p : DirectedPath.FinitePath (G.quotient X).graph)
    (hp : (Sum.inl p : (G.quotient X).DPath) ∈ W.1)
    (q : DirectedPath.FinitePath (G.quotient s.carrier).graph)
    (hpStart : p.start ∈ s.carrier)
    (hq : (Sum.inl q : (G.quotient s.carrier).DPath) ∈ s.wave.1)
    (hSupport : q.support = p.support) (hTerminal : q.finish = p.finish)
    (hStrict : G.strictRoof ((G.quotient
      (G.sectionSixAccumNextCarrier F K Y Q T s)).terminalFrontier
        (G.sectionSixAccumNext hNoEnter F K Y Q T s).wave.1) ⊆
      G.strictRoof ((G.quotient X).terminalFrontier M.1))
    (hEssential : p.finish ∈ (G.quotient X).essential
      ((G.quotient X).terminalFrontier M.1)) :
    ∃ r ∈ (G.sectionSixAccumNext hNoEnter F K Y Q T s).wave.1,
      r.support = p.support ∧
      (G.quotient (G.sectionSixAccumNextCarrier F K Y Q T s)).terminal? r =
        some p.finish := by
  have hCarrierNext : s.carrier ⊆
      G.sectionSixAccumNextCarrier F K Y Q T s :=
    G.sectionSixAccumStage_carrier_subset_next F K Y Q T s
  have hCarrierX : s.carrier ⊆ X := hCarrierNext.trans hNextX
  have hpFinishSurvivesX : p.finish ∉
      (G.quotient s.carrier).strictRoof X :=
    G.not_mem_strictRoof_of_mem_crossQuotientWave hNoEnter
      hCarrierX W hp p.finish_mem_support
  have hStrictMono : (G.quotient s.carrier).strictRoof
      (G.sectionSixAccumNextCarrier F K Y Q T s) ⊆
      (G.quotient s.carrier).strictRoof X := by
    apply (G.quotient s.carrier).strictRoof_mono_of_roof_mono
    exact (G.quotient s.carrier).roof_mono hNextX
  have hSurvives : q.finish ∉ (G.quotient s.carrier).strictRoof
      (G.sectionSixAccumNextCarrier F K Y Q T s) := by
    intro hqStrict
    exact hpFinishSurvivesX (hTerminal ▸ hStrictMono hqStrict)
  have hSuffix : ((G.quotient s.carrier).terminalRoofSuffix
      (G.sectionSixAccumNextCarrier F K Y Q T s) q).support = q.support := by
    exact G.terminalRoofSuffix_support_eq_of_crossQuotient hNoEnter
      hCarrierNext hNextX p q hpStart hSupport
  obtain ⟨r, hrOld, hrSupport, hrTerminal⟩ :=
    G.exists_mem_waveToLargerQuotient_of_old_finite hNoEnter
      hCarrierNext s.wave q hq hSurvives
  have hrSupportP : r.support = p.support :=
    hrSupport.trans (hSuffix.trans hSupport)
  rcases hrPath : r with rf | rr
  · have hrfFinish : rf.finish = p.finish := by
      simpa only [hrPath, DWeb.terminal?_finite, Option.some.injEq,
        hTerminal] using hrTerminal
    have hrOld' : (Sum.inl rf : (G.quotient
        (G.sectionSixAccumNextCarrier F K Y Q T s)).DPath) ∈
        (G.sectionSixAccumOldInNext hNoEnter F K Y Q T s).1 := by
      simpa only [sectionSixAccumOldInNext, hrPath] using hrOld
    have hForward : (G.quotient
        (G.sectionSixAccumNextCarrier F K Y Q T s)).ForwardExtension
        (G.sectionSixAccumOldInNext hNoEnter F K Y Q T s).1
        (G.sectionSixAccumNext hNoEnter F K Y Q T s).wave.1 := by
      have hOldLe :=
        G.sectionSixAccumOldInNext_le_next hNoEnter F K Y Q T s
      change (G.quotient
        (G.sectionSixAccumNextCarrier F K Y Q T s)).ForwardExtension
          (G.sectionSixAccumOldInNext hNoEnter F K Y Q T s).1
          (G.sectionSixAccumNext hNoEnter F K Y Q T s).wave.1 at hOldLe
      exact hOldLe
    obtain ⟨w, hwNext, _hrw, hwSupport, hwTerminal⟩ :=
      G.exists_quotient_forwardExtension_path_same_support_of_later_essential
        hNoEnter hNextX
        (G.sectionSixAccumNext hNoEnter F K Y Q T s).wave.2
        hForward M hStrict rf hrOld' (hrfFinish ▸ hEssential)
    refine ⟨w, hwNext, ?_, ?_⟩
    · have hrfSupport : rf.support = p.support := by
        change DirectedPath.Path.support
            (Sum.inl rf : (G.quotient
              (G.sectionSixAccumNextCarrier F K Y Q T s)).DPath) = p.support
        simpa only [hrPath] using hrSupportP
      exact hwSupport.trans hrfSupport
    · simpa only [G.sectionSixAccumNext_carrier, hrfFinish] using hwTerminal
  · rw [hrPath] at hrTerminal
    simp at hrTerminal

/-- Stage-indexed form of later-essential successor persistence.  This is
the exact induction step for Section 6: a finite common-arrow path already
represented by the `n`th dependent wave has the same representative in the
`(n+1)`st wave. -/
theorem exists_sectionSixAccumStage_succ_path_same_support_of_laterEssential
    (hNoEnter : G.NoEdgeEnters G.source)
    (F K : V → Set V) (Y Q T : Set V) (y : V)
    (n k : ℕ)
    (p : DirectedPath.FinitePath
      (G.quotient (G.sectionSixAccumClosure
        hNoEnter F K Y Q T y)).graph)
    (hp : (Sum.inl p : (G.quotient (G.sectionSixAccumClosure
      hNoEnter F K Y Q T y)).DPath) ∈
        ((G.quotient (G.sectionSixAccumClosure hNoEnter F K Y Q T y)).omegaArrowStage
          (G.sectionSixAccumCommonStage hNoEnter F K Y Q T y) k).1)
    (q : DirectedPath.FinitePath
      (G.quotient (G.sectionSixAccumStage
        hNoEnter F K Y Q T y n).carrier).graph)
    (hpStart : p.start ∈
      (G.sectionSixAccumStage hNoEnter F K Y Q T y n).carrier)
    (hq : (Sum.inl q : (G.quotient (G.sectionSixAccumStage
      hNoEnter F K Y Q T y n).carrier).DPath) ∈
        (G.sectionSixAccumStage hNoEnter F K Y Q T y n).wave.1)
    (hSupport : q.support = p.support) (hTerminal : q.finish = p.finish)
    (hEssential : p.finish ∈
      (G.quotient (G.sectionSixAccumClosure hNoEnter F K Y Q T y)).essential
        ((G.quotient (G.sectionSixAccumClosure
          hNoEnter F K Y Q T y)).terminalFrontier
            (G.sectionSixAccumCommonWave hNoEnter F K Y Q T y).1)) :
    ∃ r ∈ (G.sectionSixAccumStage hNoEnter F K Y Q T y (n + 1)).wave.1,
      r.support = p.support ∧
      (G.quotient (G.sectionSixAccumStage
        hNoEnter F K Y Q T y (n + 1)).carrier).terminal? r =
          some p.finish := by
  let s := G.sectionSixAccumStage hNoEnter F K Y Q T y n
  let X := G.sectionSixAccumClosure hNoEnter F K Y Q T y
  let C := G.sectionSixAccumCommonStage hNoEnter F K Y Q T y
  let M := G.sectionSixAccumCommonWave hNoEnter F K Y Q T y
  have hNextX : G.sectionSixAccumNextCarrier F K Y Q T s ⊆ X := by
    change (G.sectionSixAccumStage hNoEnter F K Y Q T y (n + 1)).carrier ⊆ X
    exact G.sectionSixAccumStage_carrier_subset_closure
      hNoEnter F K Y Q T y (n + 1)
  have hStrict : G.strictRoof ((G.quotient
      (G.sectionSixAccumNextCarrier F K Y Q T s)).terminalFrontier
        (G.sectionSixAccumNext hNoEnter F K Y Q T s).wave.1) ⊆
      G.strictRoof ((G.quotient X).terminalFrontier M.1) := by
    change G.strictRoof ((G.quotient
      (G.sectionSixAccumStage hNoEnter F K Y Q T y (n + 1)).carrier).terminalFrontier
        (G.sectionSixAccumStage hNoEnter F K Y Q T y (n + 1)).wave.1) ⊆
      G.strictRoof ((G.quotient X).terminalFrontier M.1)
    exact G.sectionSixAccumStage_strictRoof_subset_commonWave
      hNoEnter F K Y Q T y (n + 1)
  have h := G.exists_sectionSixAccumNext_path_same_support_of_laterEssential_finite
    hNoEnter F K Y Q T s hNextX
      ((G.quotient X).omegaArrowStage C k) M p hp q hpStart hq
      hSupport hTerminal hStrict hEssential
  change ∃ r ∈ (G.sectionSixAccumNext hNoEnter F K Y Q T s).wave.1,
    r.support = p.support ∧
    (G.quotient (G.sectionSixAccumNext hNoEnter F K Y Q T s).carrier).terminal? r =
      some p.finish
  simpa only [G.sectionSixAccumNext_carrier] using h

/-- Every essential point of the new carrier starts a member of the chosen
successor wave.  The transported old wave contains such a member (retained
or inserted as a trivial path), and forward extension preserves its
initial vertex.  This is the isolated-path branch of the first-entry
argument. -/
theorem exists_sectionSixAccumNext_path_starting_of_essential
    (hNoEnter : G.NoEdgeEnters G.source)
    (F K : V → Set V) (Y Q T : Set V)
    (s : G.SectionSixAccumStage) {x : V}
    (hx : x ∈ G.essential (G.sectionSixAccumNextCarrier F K Y Q T s)) :
    ∃ q ∈ (G.sectionSixAccumNext hNoEnter F K Y Q T s).wave.1,
      q.initial = x := by
  have hxOld : x ∈ (G.quotient
      (G.sectionSixAccumNextCarrier F K Y Q T s)).initialSet
        (G.sectionSixAccumOldInNext hNoEnter F K Y Q T s).1 := by
    exact G.essential_subset_initialSet_waveToLargerQuotient hNoEnter
      (G.sectionSixAccumStage_carrier_subset_next F K Y Q T s) s.wave hx
  obtain ⟨r, hrOld, hrInitial⟩ := hxOld
  obtain ⟨q, hqNext, hrq⟩ :=
    (G.sectionSixAccumOldInNext_le_next hNoEnter F K Y Q T s).1 r hrOld
  exact ⟨q, hqNext,
    (G.quotient (G.sectionSixAccumNextCarrier F K Y Q T s)).extends_initial
      hrq |>.symm.trans hrInitial⟩

/-- Stage-indexed isolated-path entry: a point which is essential for the
successor carrier occurs on a successor-stage member beginning at that
point. -/
theorem exists_sectionSixAccumStage_succ_path_starting_of_essential
    (hNoEnter : G.NoEdgeEnters G.source)
    (F K : V → Set V) (Y Q T : Set V) (y : V) (n : ℕ) {x : V}
    (hx : x ∈ G.essential
      (G.sectionSixAccumStage hNoEnter F K Y Q T y (n + 1)).carrier) :
    ∃ q ∈ (G.sectionSixAccumStage hNoEnter F K Y Q T y (n + 1)).wave.1,
      q.initial = x := by
  exact G.exists_sectionSixAccumNext_path_starting_of_essential
    hNoEnter F K Y Q T
      (G.sectionSixAccumStage hNoEnter F K Y Q T y n) hx

/-- A carrier point which is essential for the final closure already has
the required lifted meeting-set provenance one stage later.  This closes
the trivial finite-arrow branch. -/
theorem mem_meetingVertexSet_sectionSixAccumStage_succ_of_essential
    (hNoEnter : G.NoEdgeEnters G.source)
    (F K : V → Set V) (Y Q T : Set V) (y : V) (n : ℕ) {x : V}
    (hxCarrier : x ∈
      (G.sectionSixAccumStage hNoEnter F K Y Q T y n).carrier)
    (hxEssential : x ∈ G.essential
      (G.sectionSixAccumClosure hNoEnter F K Y Q T y)) :
    x ∈ G.meetingVertexSet
      (G.sectionSixAccumStageLift
        (G.sectionSixAccumStage hNoEnter F K Y Q T y (n + 1)))
      (G.sectionSixAccumStage hNoEnter F K Y Q T y (n + 1)).carrier := by
  have hxNext : x ∈
      (G.sectionSixAccumStage hNoEnter F K Y Q T y (n + 1)).carrier :=
    G.sectionSixAccumStage_carrier_subset_succ
      hNoEnter F K Y Q T y n hxCarrier
  have hxNextEssential : x ∈ G.essential
      (G.sectionSixAccumStage hNoEnter F K Y Q T y (n + 1)).carrier :=
    G.mem_essential_of_mem_of_subset_of_mem_essential hxNext
      (G.sectionSixAccumStage_carrier_subset_closure
        hNoEnter F K Y Q T y (n + 1)) hxEssential
  obtain ⟨q, hqStage, hqInitial⟩ :=
    G.exists_sectionSixAccumStage_succ_path_starting_of_essential
      hNoEnter F K Y Q T y n hxNextEssential
  exact G.mem_meetingVertexSet_liftQuotientFamily hqStage
    (hqInitial ▸ q.initial_mem_support) hxNext
    (hqInitial ▸ q.initial_mem_support)

/-- A surviving finite path of an accumulated stage is represented in the
transported old wave at the successor carrier and is then absorbed by the
chosen successor wave.  The returned successor member contains the complete
terminal-roof suffix of the old path and has that suffix as a concrete
forward-extension predecessor. -/
theorem exists_sectionSixAccumNext_path_extending_old_finite
    (hNoEnter : G.NoEdgeEnters G.source)
    (F K : V → Set V) (Y Q T : Set V)
    (s : G.SectionSixAccumStage)
    (p : DirectedPath.FinitePath (G.quotient s.carrier).graph)
    (hp : (Sum.inl p : (G.quotient s.carrier).DPath) ∈ s.wave.1)
    (hpSurvives : p.finish ∉
      (G.quotient s.carrier).strictRoof
        (G.sectionSixAccumNextCarrier F K Y Q T s)) :
    ∃ r ∈ (G.sectionSixAccumOldInNext hNoEnter F K Y Q T s).1,
      r.support = ((G.quotient s.carrier).terminalRoofSuffix
          (G.sectionSixAccumNextCarrier F K Y Q T s) p).support ∧
      (G.quotient (G.sectionSixAccumNextCarrier F K Y Q T s)).terminal? r =
        some p.finish ∧
      ∃ q ∈ (G.sectionSixAccumNext hNoEnter F K Y Q T s).wave.1,
        (G.quotient (G.sectionSixAccumNextCarrier F K Y Q T s)).Extends r q ∧
        r.support ⊆ q.support := by
  obtain ⟨r, hrOld, hrSupport, hrTerminal⟩ :=
    G.exists_mem_waveToLargerQuotient_of_old_finite hNoEnter
      (G.sectionSixAccumStage_carrier_subset_next F K Y Q T s)
      s.wave p hp hpSurvives
  obtain ⟨q, hqNext, hrq⟩ :=
    (G.sectionSixAccumOldInNext_le_next hNoEnter F K Y Q T s).1
      r hrOld
  exact ⟨r, hrOld, hrSupport, hrTerminal, q, hqNext, hrq,
    (G.quotient (G.sectionSixAccumNextCarrier F K Y Q T s)).support_mono_of_extends
      hrq⟩

/-- Final essential meeting paths reduce to the exact finite-arrow ancestry
seam.  Besides exact support and terminal, the selected finite arrow stage
is late enough that its initial vertex already belongs to that dependent
stage's carrier. -/
theorem exists_finiteArrowStage_of_essentialMeeting_sectionSixAccum
    (hNoEnter : G.NoEdgeEnters G.source)
    (F K : V → Set V) (Y Q T : Set V) (y : V) :
    let X := G.sectionSixAccumClosure hNoEnter F K Y Q T y
    let C := G.sectionSixAccumCommonStage hNoEnter F K Y Q T y
    let M := G.sectionSixAccumCommonWave hNoEnter F K Y Q T y
    ∀ {q : (G.quotient X).DPath},
      q ∈ (G.quotient X).essentialMeetingPaths M.1 X →
      ∃ m, ∃ p : DirectedPath.FinitePath (G.quotient X).graph,
        (Sum.inl p : (G.quotient X).DPath) ∈
            ((G.quotient X).omegaArrowStage C m).1 ∧
        p.support = q.support ∧
        (G.quotient X).terminal? (.inl p) =
          (G.quotient X).terminal? q ∧
        p.start ∈
          (G.sectionSixAccumStage hNoEnter F K Y Q T y m).carrier ∧
        p.finish ∈ (G.quotient X).essential
          ((G.quotient X).terminalFrontier M.1) := by
  dsimp only
  intro q hq
  have hqInitialX : q.initial ∈
      G.sectionSixAccumClosure hNoEnter F K Y Q T y :=
    G.essentialMeetingPath_initial_mem hNoEnter
      (G.sectionSixAccumCommonWave hNoEnter F K Y Q T y).2 hq
  obtain ⟨k, hqInitialK⟩ := Set.mem_iUnion.mp hqInitialX
  obtain ⟨m, hkm, p, hpStage, hpSupport, hpTerminal⟩ :=
    DWeb.exists_later_omegaArrowStage_path_same_support_terminal_of_essential
      (G := G.quotient (G.sectionSixAccumClosure hNoEnter F K Y Q T y))
      (G.sectionSixAccumCommonStage hNoEnter F K Y Q T y) k hq.1
  have hqSource : q.initial ∈
      (G.quotient (G.sectionSixAccumClosure hNoEnter F K Y Q T y)).source :=
    (G.sectionSixAccumCommonWave hNoEnter F K Y Q T y).2.2.1
      ⟨q, hq.1.1, rfl⟩
  have hpInitial : q.initial = p.initial :=
    DWeb.NoEdgeEnters.eq_initial_of_mem_path
      (G := G.quotient (G.sectionSixAccumClosure hNoEnter F K Y Q T y))
      hNoEnter.quotient p (hpSupport ▸ q.initial_mem_support) hqSource
  have hpCarrier : p.initial ∈
      (G.sectionSixAccumStage hNoEnter F K Y Q T y m).carrier := by
    rw [← hpInitial]
    exact G.sectionSixAccumStage_carrier_mono hNoEnter F K Y Q T y hkm
      hqInitialK
  obtain ⟨_hqM, t, hqTerminal, htEssential⟩ := hq.1
  rcases hpPath : p with pf | pr
  · refine ⟨m, pf, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [hpPath] using hpStage
    · rw [hpPath] at hpSupport
      exact hpSupport
    · simpa only [hpPath] using hpTerminal
    · simpa only [hpPath, DirectedPath.Path.initial] using hpCarrier
    · have hpfTerminal :
          (G.quotient (G.sectionSixAccumClosure hNoEnter F K Y Q T y)).terminal?
              (.inl pf) = some t := by
        calc
          _ = (G.quotient
                (G.sectionSixAccumClosure hNoEnter F K Y Q T y)).terminal? q := by
            simpa only [hpPath] using hpTerminal
          _ = some t := hqTerminal
      have : pf.finish = t := by simpa using hpfTerminal
      exact this ▸ htEssential
  · have hpNone :
        (G.quotient (G.sectionSixAccumClosure hNoEnter F K Y Q T y)).terminal?
            (.inr pr) = none := rfl
    have hnoneSome : (none : Option V) = some t := by
      calc
        none = (G.quotient
              (G.sectionSixAccumClosure hNoEnter F K Y Q T y)).terminal?
                (.inr pr) := hpNone.symm
        _ = (G.quotient
              (G.sectionSixAccumClosure hNoEnter F K Y Q T y)).terminal? q := by
          simpa only [hpPath] using hpTerminal
        _ = some t := hqTerminal
    simp at hnoneSome

/-- A finite path in a transported wave is either one of the isolated
essential paths inserted by the quotient construction, or it is exactly the
final-roof suffix of a finite member of the old wave.  Keeping this
dichotomy explicit is useful in the finite-arrow ancestry induction: the
first alternative is the only way a commitment vertex can appear before it
belongs to the dependent carrier. -/
theorem finite_mem_waveToLargerQuotient_trivial_or_finalSuffix
    (hNoEnter : G.NoEdgeEnters G.source) {X Y : Set V} (hXY : X ⊆ Y)
    (W : (G.quotient X).Wave)
    (p : DirectedPath.FinitePath (G.quotient Y).graph)
    (hp : (Sum.inl p : (G.quotient Y).DPath) ∈
      (G.waveToLargerQuotient hNoEnter hXY W).1) :
    (Sum.inl p : (G.quotient Y).DPath) =
        (G.quotient Y).trivialPath p.start ∨
      ∃ q : DirectedPath.FinitePath (G.quotient X).graph,
        (Sum.inl q : (G.quotient X).DPath) ∈ W.1 ∧
        ((G.quotient X).terminalRoofSuffix Y q).support = p.support ∧
        q.finish = p.finish := by
  by_cases htrivial : (Sum.inl p : (G.quotient Y).DPath) =
      (G.quotient Y).trivialPath p.start
  · exact Or.inl htrivial
  · right
    obtain ⟨z, hzp, hzNe⟩ :=
      (G.quotient Y).exists_support_ne_initial_of_ne_trivial
        (Sum.inl p : (G.quotient Y).DPath) htrivial
    have hzY : z ∉ Y :=
      (G.quotientPath_avoids_after_initial Y
        (Sum.inl p : (G.quotient Y).DPath) hzp hzNe).2
    obtain ⟨q, hqW, _hqSurvives, hpSupport, hpTerminal⟩ :=
      G.exists_old_finite_path_of_mem_waveToLargerQuotient_of_not_mem
        hNoEnter hXY W hp hzp hzY
    refine ⟨q, hqW, ?_, ?_⟩
    · exact hpSupport.symm
    · simpa only [DWeb.terminal?_finite, Option.some.injEq] using
        hpTerminal.symm

/-- Stage-indexed form of
`finite_mem_waveToLargerQuotient_trivial_or_finalSuffix` for the common
quotient used in Section 6. -/
theorem finite_mem_sectionSixAccumCommonStage_trivial_or_finalSuffix
    (hNoEnter : G.NoEdgeEnters G.source)
    (F K : V → Set V) (Y Q T : Set V) (y : V) (n : ℕ)
    (p : DirectedPath.FinitePath
      (G.quotient (G.sectionSixAccumClosure hNoEnter F K Y Q T y)).graph)
    (hp : (Sum.inl p : (G.quotient
        (G.sectionSixAccumClosure hNoEnter F K Y Q T y)).DPath) ∈
      (G.sectionSixAccumCommonStage hNoEnter F K Y Q T y n).1) :
    (Sum.inl p : (G.quotient
        (G.sectionSixAccumClosure hNoEnter F K Y Q T y)).DPath) =
        (G.quotient
          (G.sectionSixAccumClosure hNoEnter F K Y Q T y)).trivialPath p.start ∨
      ∃ q : DirectedPath.FinitePath (G.quotient
          (G.sectionSixAccumStage hNoEnter F K Y Q T y n).carrier).graph,
        (Sum.inl q : (G.quotient
          (G.sectionSixAccumStage hNoEnter F K Y Q T y n).carrier).DPath) ∈
            (G.sectionSixAccumStage hNoEnter F K Y Q T y n).wave.1 ∧
        ((G.quotient
          (G.sectionSixAccumStage hNoEnter F K Y Q T y n).carrier).terminalRoofSuffix
            (G.sectionSixAccumClosure hNoEnter F K Y Q T y) q).support =
              p.support ∧
        q.finish = p.finish := by
  exact G.finite_mem_waveToLargerQuotient_trivial_or_finalSuffix hNoEnter
    (G.sectionSixAccumStage_carrier_subset_closure
      hNoEnter F K Y Q T y n)
    (G.sectionSixAccumStage hNoEnter F K Y Q T y n).wave p hp

/-- Once a finite common-quotient path has a final-suffix predecessor at
the corresponding dependent stage, every vertex of the common path has the
required lifted meeting-set provenance.  The exceptional trivial path is
handled one stage later using its essential commitment vertex. -/
theorem exists_sectionSixAccumStage_meeting_of_finiteArrow_of_finalSuffix
    (hNoEnter : G.NoEdgeEnters G.source)
    (F K : V → Set V) (Y Q T : Set V) (y : V) (n : ℕ)
    (p : DirectedPath.FinitePath
      (G.quotient (G.sectionSixAccumClosure hNoEnter F K Y Q T y)).graph)
    (hp : (Sum.inl p : (G.quotient
        (G.sectionSixAccumClosure hNoEnter F K Y Q T y)).DPath) ∈
      ((G.quotient
        (G.sectionSixAccumClosure hNoEnter F K Y Q T y)).omegaArrowStage
          (G.sectionSixAccumCommonStage hNoEnter F K Y Q T y) n).1)
    (hpStart : p.start ∈
      (G.sectionSixAccumStage hNoEnter F K Y Q T y n).carrier)
    (_hpEssential : p.finish ∈ (G.quotient
      (G.sectionSixAccumClosure hNoEnter F K Y Q T y)).essential
        ((G.quotient
          (G.sectionSixAccumClosure hNoEnter F K Y Q T y)).terminalFrontier
            (G.sectionSixAccumCommonWave hNoEnter F K Y Q T y).1))
    (hPred :
      (Sum.inl p : (G.quotient
          (G.sectionSixAccumClosure hNoEnter F K Y Q T y)).DPath) =
          (G.quotient
            (G.sectionSixAccumClosure hNoEnter F K Y Q T y)).trivialPath
              p.start ∨
        ∃ q : DirectedPath.FinitePath (G.quotient
            (G.sectionSixAccumStage hNoEnter F K Y Q T y n).carrier).graph,
          (Sum.inl q : (G.quotient
            (G.sectionSixAccumStage hNoEnter F K Y Q T y n).carrier).DPath) ∈
              (G.sectionSixAccumStage hNoEnter F K Y Q T y n).wave.1 ∧
          ((G.quotient
            (G.sectionSixAccumStage hNoEnter F K Y Q T y n).carrier).terminalRoofSuffix
              (G.sectionSixAccumClosure hNoEnter F K Y Q T y) q).support =
                p.support ∧
          q.finish = p.finish)
    {z : V} (hzp : z ∈ p.support) :
    ∃ m, z ∈ G.meetingVertexSet
      (G.sectionSixAccumStageLift
        (G.sectionSixAccumStage hNoEnter F K Y Q T y m))
      (G.sectionSixAccumStage hNoEnter F K Y Q T y m).carrier := by
  rcases hPred with htrivial | ⟨q, hqStage, hqSupport, _hqFinish⟩
  · have hzEq : z = p.start := by
      have hz : z ∈ ((G.quotient
          (G.sectionSixAccumClosure hNoEnter F K Y Q T y)).trivialPath
            p.start).support := htrivial ▸ hzp
      simpa only [(G.quotient
        (G.sectionSixAccumClosure hNoEnter F K Y Q T y)).support_trivialPath,
        Set.mem_singleton_iff] using hz
    subst z
    have hpVertex : p.start ∈ (G.quotient
        (G.sectionSixAccumClosure hNoEnter F K Y Q T y)).vertexSet
          ((G.quotient
            (G.sectionSixAccumClosure hNoEnter F K Y Q T y)).omegaArrowStage
              (G.sectionSixAccumCommonStage hNoEnter F K Y Q T y) n).1 :=
      ⟨Sum.inl p, hp, p.start_mem_support⟩
    have hpSurvives : p.start ∉ G.strictRoof
        (G.sectionSixAccumClosure hNoEnter F K Y Q T y) :=
      G.quotientWave_vertexSet_subset_quotientVertexSet hNoEnter
        ((G.quotient
          (G.sectionSixAccumClosure hNoEnter F K Y Q T y)).omegaArrowStage
            (G.sectionSixAccumCommonStage hNoEnter F K Y Q T y) n).2
        hpVertex
    have hpEssential : p.start ∈ G.essential
        (G.sectionSixAccumClosure hNoEnter F K Y Q T y) := by
      rw [← G.sdiff_strictRoof_self]
      exact ⟨G.sectionSixAccumStage_carrier_subset_closure
        hNoEnter F K Y Q T y n hpStart, hpSurvives⟩
    exact ⟨n + 1,
      G.mem_meetingVertexSet_sectionSixAccumStage_succ_of_essential
        hNoEnter F K Y Q T y n hpStart hpEssential⟩
  · have hpStartSuffix : p.start ∈ ((G.quotient
        (G.sectionSixAccumStage hNoEnter F K Y Q T y n).carrier).terminalRoofSuffix
          (G.sectionSixAccumClosure hNoEnter F K Y Q T y) q).support :=
      hqSupport.symm ▸ p.start_mem_support
    have hzSuffix : z ∈ ((G.quotient
        (G.sectionSixAccumStage hNoEnter F K Y Q T y n).carrier).terminalRoofSuffix
          (G.sectionSixAccumClosure hNoEnter F K Y Q T y) q).support :=
      hqSupport.symm ▸ hzp
    have hpStartQ : p.start ∈ q.support :=
      (G.quotient
        (G.sectionSixAccumStage hNoEnter F K Y Q T y n).carrier).terminalRoofSuffix_support_subset
          (G.sectionSixAccumClosure hNoEnter F K Y Q T y) q hpStartSuffix
    have hzQ : z ∈ q.support :=
      (G.quotient
        (G.sectionSixAccumStage hNoEnter F K Y Q T y n).carrier).terminalRoofSuffix_support_subset
          (G.sectionSixAccumClosure hNoEnter F K Y Q T y) q hzSuffix
    exact ⟨n, G.mem_meetingVertexSet_liftQuotientFamily
      hqStage hpStartQ hpStart hzQ⟩

/-- The exact finite-arrow invariant still needed by the countable
construction.  The endpoint condition is deliberately retained: it is what
prevents an unchanged finite predecessor from being extended to a ray or
past its terminal when it is moved to the next dependent stage. -/
def HasSectionSixAccumFiniteArrowFinalSuffix
    (hNoEnter : G.NoEdgeEnters G.source)
    (F K : V → Set V) (Y Q T : Set V) (y : V) : Prop :=
  Disjoint G.source
      (G.sectionSixAccumClosure hNoEnter F K Y Q T y) →
  ∀ (n : ℕ)
    (p : DirectedPath.FinitePath
      (G.quotient (G.sectionSixAccumClosure hNoEnter F K Y Q T y)).graph),
    (Sum.inl p : (G.quotient
        (G.sectionSixAccumClosure hNoEnter F K Y Q T y)).DPath) ∈
      ((G.quotient
        (G.sectionSixAccumClosure hNoEnter F K Y Q T y)).omegaArrowStage
          (G.sectionSixAccumCommonStage hNoEnter F K Y Q T y) n).1 →
    p.start ∈
      (G.sectionSixAccumStage hNoEnter F K Y Q T y n).carrier →
    p.finish ∈ (G.quotient
      (G.sectionSixAccumClosure hNoEnter F K Y Q T y)).essential
        ((G.quotient
          (G.sectionSixAccumClosure hNoEnter F K Y Q T y)).terminalFrontier
            (G.sectionSixAccumCommonWave hNoEnter F K Y Q T y).1) →
    (Sum.inl p : (G.quotient
        (G.sectionSixAccumClosure hNoEnter F K Y Q T y)).DPath) =
        (G.quotient
          (G.sectionSixAccumClosure hNoEnter F K Y Q T y)).trivialPath p.start ∨
      ∃ q : DirectedPath.FinitePath (G.quotient
          (G.sectionSixAccumStage hNoEnter F K Y Q T y n).carrier).graph,
        (Sum.inl q : (G.quotient
          (G.sectionSixAccumStage hNoEnter F K Y Q T y n).carrier).DPath) ∈
            (G.sectionSixAccumStage hNoEnter F K Y Q T y n).wave.1 ∧
        ((G.quotient
          (G.sectionSixAccumStage hNoEnter F K Y Q T y n).carrier).terminalRoofSuffix
            (G.sectionSixAccumClosure hNoEnter F K Y Q T y) q).support =
              p.support ∧
        q.finish = p.finish

/-- The finite-arrow final-suffix invariant implies the raw dependent-stage
provenance statement, before any of the special Section 6 data are
instantiated. -/
theorem sectionSixAccumProvenance_of_finiteArrowFinalSuffix
    (hNoEnter : G.NoEdgeEnters G.source)
    (F K : V → Set V) (Y Q T : Set V) (y : V)
    (hArrow : G.HasSectionSixAccumFiniteArrowFinalSuffix
      hNoEnter F K Y Q T y)
    (hSourceX : Disjoint G.source
      (G.sectionSixAccumClosure hNoEnter F K Y Q T y)) :
    ∀ z ∈ (G.quotient
      (G.sectionSixAccumClosure hNoEnter F K Y Q T y)).vertexSet
        ((G.quotient
          (G.sectionSixAccumClosure hNoEnter F K Y Q T y)).essentialMeetingPaths
            (G.sectionSixAccumCommonWave hNoEnter F K Y Q T y).1
            (G.sectionSixAccumClosure hNoEnter F K Y Q T y)),
      ∃ n, z ∈ G.meetingVertexSet
        (G.sectionSixAccumStageLift
          (G.sectionSixAccumStage hNoEnter F K Y Q T y n))
        (G.sectionSixAccumStage hNoEnter F K Y Q T y n).carrier := by
  intro z hz
  obtain ⟨q, hqMeeting, hzq⟩ := hz
  obtain ⟨m, p, hpStage, hpSupport, _hpTerminal, hpStart, hpEssential⟩ :=
    G.exists_finiteArrowStage_of_essentialMeeting_sectionSixAccum
      hNoEnter F K Y Q T y hqMeeting
  have hzp : z ∈ p.support := hpSupport ▸ hzq
  have hPred := hArrow hSourceX m p hpStage hpStart hpEssential
  exact G.exists_sectionSixAccumStage_meeting_of_finiteArrow_of_finalSuffix
    hNoEnter F K Y Q T y m p hpStage hpStart hpEssential hPred hzp

/-- A protected final-roof suffix can be advanced through one dependent
successor without assuming that its initial vertex is already committed.
The old member is first transported with its final suffix unchanged.  The
later-essential endpoint then prevents the maximal successor wave from
extending that transported member any further. -/
theorem exists_sectionSixAccumNext_path_finalSuffix_of_laterEssential
    (hNoEnter : G.NoEdgeEnters G.source)
    (F K : V → Set V) (Y Q T : Set V)
    (s : G.SectionSixAccumStage) {X : Set V}
    (hNextX : G.sectionSixAccumNextCarrier F K Y Q T s ⊆ X)
    (W M : (G.quotient X).Wave)
    (p : DirectedPath.FinitePath (G.quotient X).graph)
    (hp : (Sum.inl p : (G.quotient X).DPath) ∈ W.1)
    (q : DirectedPath.FinitePath (G.quotient s.carrier).graph)
    (hq : (Sum.inl q : (G.quotient s.carrier).DPath) ∈ s.wave.1)
    (hSuffix : ((G.quotient s.carrier).terminalRoofSuffix X q).support =
      p.support)
    (hTerminal : q.finish = p.finish)
    (hStrict : G.strictRoof ((G.quotient
      (G.sectionSixAccumNextCarrier F K Y Q T s)).terminalFrontier
        (G.sectionSixAccumNext hNoEnter F K Y Q T s).wave.1) ⊆
      G.strictRoof ((G.quotient X).terminalFrontier M.1))
    (hEssential : p.finish ∈ (G.quotient X).essential
      ((G.quotient X).terminalFrontier M.1)) :
    ∃ r : DirectedPath.FinitePath (G.quotient
        (G.sectionSixAccumNextCarrier F K Y Q T s)).graph,
      (Sum.inl r : (G.quotient
        (G.sectionSixAccumNextCarrier F K Y Q T s)).DPath) ∈
          (G.sectionSixAccumNext hNoEnter F K Y Q T s).wave.1 ∧
      ((G.quotient
        (G.sectionSixAccumNextCarrier F K Y Q T s)).terminalRoofSuffix X r).support =
          p.support ∧
      r.finish = p.finish := by
  let Xnext := G.sectionSixAccumNextCarrier F K Y Q T s
  let H := G.quotient Xnext
  have hCarrierNext : s.carrier ⊆ Xnext :=
    G.sectionSixAccumStage_carrier_subset_next F K Y Q T s
  have hCarrierX : s.carrier ⊆ X := hCarrierNext.trans hNextX
  have hpFinishSurvivesX : p.finish ∉
      (G.quotient s.carrier).strictRoof X :=
    G.not_mem_strictRoof_of_mem_crossQuotientWave hNoEnter
      hCarrierX W hp p.finish_mem_support
  have hStrictMono : (G.quotient s.carrier).strictRoof Xnext ⊆
      (G.quotient s.carrier).strictRoof X := by
    apply (G.quotient s.carrier).strictRoof_mono_of_roof_mono
    exact (G.quotient s.carrier).roof_mono hNextX
  have hqSurvives : q.finish ∉
      (G.quotient s.carrier).strictRoof Xnext := by
    intro hqStrict
    exact hpFinishSurvivesX (hTerminal ▸ hStrictMono hqStrict)
  obtain ⟨r, hrOld, hrTerminal, hrSuffix⟩ :=
    G.exists_mem_waveToLargerQuotient_of_old_finite_finalSuffix
      hNoEnter hCarrierNext hNextX s.wave q hq hqSurvives
  have hOldLe : H.ForwardExtension
      (G.sectionSixAccumOldInNext hNoEnter F K Y Q T s).1
      (G.sectionSixAccumNext hNoEnter F K Y Q T s).wave.1 := by
    exact G.sectionSixAccumOldInNext_le_next hNoEnter F K Y Q T s
  have hrFinish : r.finish = p.finish := by
    have : r.finish = q.finish := by
      simpa only [H.terminal?_finite, Option.some.injEq] using hrTerminal
    exact this.trans hTerminal
  obtain ⟨w, hwNext, hrw, hwSupport, hwTerminal⟩ :=
    G.exists_quotient_forwardExtension_path_same_support_of_later_essential
      hNoEnter hNextX
        (G.sectionSixAccumNext hNoEnter F K Y Q T s).wave.2 hOldLe
        M hStrict r hrOld (hrFinish ▸ hEssential)
  obtain ⟨wf, hwPath⟩ :=
    G.sectionSixAccumNext_hasFiniteCharacter hNoEnter F K Y Q T s hwNext
  subst w
  have hwFinish : wf.finish = r.finish := by
    simpa only [H.terminal?_finite, Option.some.injEq] using hwTerminal
  have hrPrefix : r.IsPrefixOf wf := by
    exact hrw
  have hwalk : r.walk.support = wf.walk.support :=
    SafeLinkGround.DirectedPath.FinitePath.support_eq_of_isPrefixOf_of_finish_mem
      hrPrefix (hwFinish ▸ r.finish_mem_support)
  have htrim : (H.terminalRoofSuffix X wf).support =
      (H.terminalRoofSuffix X r).support := by
    exact (H.terminalRoofSuffix_support_eq_of_walkSupport_eq
      (H := H) (R := X) (S := X) rfl wf r hwalk.symm)
  refine ⟨wf, hwNext, ?_, ?_⟩
  · exact htrim.trans (hrSuffix.trans hSuffix)
  · exact hwFinish.trans hrFinish

/-- Stage-indexed form of final-suffix successor persistence. -/
theorem exists_sectionSixAccumStage_succ_path_finalSuffix_of_laterEssential
    (hNoEnter : G.NoEdgeEnters G.source)
    (F K : V → Set V) (Y Q T : Set V) (y : V) (n k : ℕ)
    (p : DirectedPath.FinitePath
      (G.quotient (G.sectionSixAccumClosure hNoEnter F K Y Q T y)).graph)
    (hp : (Sum.inl p : (G.quotient
        (G.sectionSixAccumClosure hNoEnter F K Y Q T y)).DPath) ∈
      ((G.quotient
        (G.sectionSixAccumClosure hNoEnter F K Y Q T y)).omegaArrowStage
          (G.sectionSixAccumCommonStage hNoEnter F K Y Q T y) k).1)
    (q : DirectedPath.FinitePath (G.quotient
      (G.sectionSixAccumStage hNoEnter F K Y Q T y n).carrier).graph)
    (hq : (Sum.inl q : (G.quotient
      (G.sectionSixAccumStage hNoEnter F K Y Q T y n).carrier).DPath) ∈
        (G.sectionSixAccumStage hNoEnter F K Y Q T y n).wave.1)
    (hSuffix : ((G.quotient
      (G.sectionSixAccumStage hNoEnter F K Y Q T y n).carrier).terminalRoofSuffix
        (G.sectionSixAccumClosure hNoEnter F K Y Q T y) q).support = p.support)
    (hTerminal : q.finish = p.finish)
    (hEssential : p.finish ∈ (G.quotient
      (G.sectionSixAccumClosure hNoEnter F K Y Q T y)).essential
        ((G.quotient
          (G.sectionSixAccumClosure hNoEnter F K Y Q T y)).terminalFrontier
            (G.sectionSixAccumCommonWave hNoEnter F K Y Q T y).1)) :
    ∃ r : DirectedPath.FinitePath (G.quotient
        (G.sectionSixAccumStage hNoEnter F K Y Q T y (n + 1)).carrier).graph,
      (Sum.inl r : (G.quotient
        (G.sectionSixAccumStage hNoEnter F K Y Q T y (n + 1)).carrier).DPath) ∈
          (G.sectionSixAccumStage hNoEnter F K Y Q T y (n + 1)).wave.1 ∧
      ((G.quotient
        (G.sectionSixAccumStage hNoEnter F K Y Q T y (n + 1)).carrier).terminalRoofSuffix
          (G.sectionSixAccumClosure hNoEnter F K Y Q T y) r).support = p.support ∧
      r.finish = p.finish := by
  apply G.exists_sectionSixAccumNext_path_finalSuffix_of_laterEssential
    hNoEnter F K Y Q T
      (G.sectionSixAccumStage hNoEnter F K Y Q T y n)
      (G.sectionSixAccumStage_carrier_subset_closure
        hNoEnter F K Y Q T y (n + 1))
      ((G.quotient
        (G.sectionSixAccumClosure hNoEnter F K Y Q T y)).omegaArrowStage
          (G.sectionSixAccumCommonStage hNoEnter F K Y Q T y) k)
      (G.sectionSixAccumCommonWave hNoEnter F K Y Q T y)
      p hp q hq hSuffix hTerminal
  · exact G.sectionSixAccumStage_strictRoof_subset_commonWave
      hNoEnter F K Y Q T y (n + 1)
  · exact hEssential

end DWeb

end Erdos599
