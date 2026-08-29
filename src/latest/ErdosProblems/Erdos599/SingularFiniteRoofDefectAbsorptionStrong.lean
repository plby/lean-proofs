/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularFiniteRoofDefectAbsorption
import ErdosProblems.Erdos599.SingularFiniteTargetGapAbsorptionStrong

/-!
# Finite-character strengthening of finite roof-defect absorption

This is the state-preserving form of finite defect absorption.  In addition
to retaining the old initial set it records that the resulting wave still
has finite character, so it can be iterated as a genuine hindrance profile.
-/

noncomputable section

open Set

namespace Erdos599
namespace CardinalInduction
namespace SingularFiniteRoofDefectAbsorptionStrong

open DWeb
open SliceCandidate
open SliceSpliceSource
open SingularContinuation
open SingularFiniteExactBoundaryRepair
open SingularFiniteRoofDefectAbsorption
open SingularFiniteTargetGapAbsorptionStrong
open SingularMarkedResidualTouchedPaths
open _root_.Erdos599.Blueprint.LinkageBlueprint

universe u

variable {V : Type u}

/-- Absorb a finite roof defect while retaining both the initial profile and
finite character. -/
theorem exists_finiteCharacter_wave_initialSet_superset_of_finite_roof_defect
    {H : DWeb V} (hNorm : H.IsNormalized)
    {W : Set H.DPath} (hW : H.IsWarp W)
    (hfinite : H.HasFiniteCharacter W)
    (hinitial : H.initialSet W ⊆ H.source)
    {F : Set V} (hFfinite : F.Finite)
    (hroof : H.source ⊆ H.roof (H.terminalFrontier W ∪ F)) :
    ∃ U : Set H.DPath, H.IsWave U ∧ H.HasFiniteCharacter U ∧
      H.initialSet W ⊆ H.initialSet U := by
  let S := H.terminalFrontier W
  let D := S ∪ F
  let hL : IsLinkageBetween H (H.initialSet W) S W :=
    isLinkageBetween_own_endpoints hW hfinite
  let hsep : RelationalRoof.Separates H.graph.Adj
      (H.initialSet W) S D := by
    intro r t p _hr ht
    exact ⟨t, p.end_mem_support, Set.mem_union_left F ht⟩
  let Y := firstHitPrefixFamily hL hsep
  have hY : IsLinkageBetween H (H.initialSet W) D Y :=
    firstHitPrefixFamily_isLinkageBetween hL hsep
  have hYclean : TerminalCleanAt H Y D :=
    RegularCleanExchange.firstHitPrefixFamily_terminalClean hL hsep
  let PM := pathsMeetingVertices H W F
  have hPMfinite : PM.Finite :=
    pathsMeetingVertices_finite_of_isWarp hW hFfinite
  have hAvoidTight : MeetsOnlyAtTerminal H (W \ PM) D := by
    intro p hp x hxp hxD
    rcases hxD with hxS | hxF
    · exact H.fd_terminal_eq_of_mem_support_frontier
        hW hfinite hp.1 hxp hxS
    · exact False.elim (hp.2 ⟨hp.1, ⟨x, hxp, hxF⟩⟩)
  have hAvoidY : W \ PM ⊆ Y :=
    firstHitPrefixFamily_contains_of_subset_of_meetsOnlyAtTerminal
      hL hsep Set.sdiff_subset hAvoidTight
  have hgapFinite : (D \ H.terminalFrontier Y).Finite := by
    apply (hFfinite.union
      (terminalFrontier_finite_of_family_finite hPMfinite)).subset
    rintro x ⟨hxD, hxnotY⟩
    by_cases hxF : x ∈ F
    · exact Set.mem_union_left _ hxF
    · have hxS : x ∈ S := hxD.resolve_right hxF
      obtain ⟨p, hpW, hpTerminal⟩ := hxS
      by_cases hpPM : p ∈ PM
      · exact Set.mem_union_right _ ⟨p, hpPM, hpTerminal⟩
      · have hpY : p ∈ Y := hAvoidY ⟨hpW, hpPM⟩
        exact False.elim (hxnotY ⟨p, hpY, hpTerminal⟩)
  let K := H.retarget D
  let YK : Set K.DPath := Y
  have hYK : IsLinkageBetween K (H.initialSet W) D YK := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · change H.IsWarp Y
      exact hY.isWarp
    · change H.HasFiniteCharacter Y
      exact hY.finiteCharacter
    · change H.initialSet Y = H.initialSet W
      exact hY.initialSet_eq
    · change H.terminalFrontier Y ⊆ D
      exact hY.terminalFrontier_subset
    · intro p hp
      change IsPathBetween H (H.initialSet W) D p
      exact hY.endpointPure p hp
  have hYKclean : TerminalCleanAt K YK K.target := by
    intro p hp x hxp hxD
    change H.terminal? p = some x
    exact hYclean p hp x hxp hxD
  have hYsourceClean :
      ∀ p ∈ YK, p.support ∩ K.source ⊆ {p.initial} := by
    intro p hp x hx
    exact Set.mem_singleton_iff.mpr
      (hNorm.eq_initial_of_mem_path p hx.1 hx.2)
  let Yn := normalizeEndpointCleanFamily K hYK.finiteCharacter
    hYsourceClean hYKclean
  have hYnWarp : K.normalized.IsWarp Yn :=
    normalizeEndpointCleanFamily_isWarp K hYK.isWarp hYK.finiteCharacter
      hYsourceClean hYKclean
  have hYnFinite : K.normalized.HasFiniteCharacter Yn :=
    normalizeEndpointCleanFamily_finiteCharacter K hYK.finiteCharacter
      hYsourceClean hYKclean
  have hYnInitialEq :
      K.normalized.initialSet Yn = H.initialSet Y := by
    rw [show K.normalized.initialSet Yn = K.initialSet YK by
      exact initialSet_normalizeEndpointCleanFamily K hYK.finiteCharacter
        hYsourceClean hYKclean]
    ext x
    rfl
  have hYnTerminalEq :
      K.normalized.terminalFrontier Yn = H.terminalFrontier Y := by
    rw [show K.normalized.terminalFrontier Yn = K.terminalFrontier YK by
      exact terminalFrontier_normalizeEndpointCleanFamily K
        hYK.finiteCharacter hYsourceClean hYKclean]
    ext x
    rfl
  have hYnInitial : K.normalized.initialSet Yn ⊆ K.normalized.source := by
    rw [hYnInitialEq]
    change H.initialSet Y ⊆ H.source
    exact hY.initialSet_eq.symm ▸ hinitial
  have hYnTerminal :
      K.normalized.terminalFrontier Yn ⊆ K.normalized.target := by
    rw [hYnTerminalEq]
    change H.terminalFrontier Y ⊆ D
    exact hY.terminalFrontier_subset
  have hYnClean : K.normalized.IsCleanFiniteWarp Yn :=
    AlternativeMaximalLinkage.cleanFiniteWarp_of_normalized
      K.normalized_isNormalized hYnWarp hYnFinite hYnInitial hYnTerminal
  have hgapNormalized :
      (K.normalized.target \
        K.normalized.terminalFrontier Yn).Finite := by
    rw [hYnTerminalEq]
    change (D \ H.terminalFrontier Y).Finite
    exact hgapFinite
  obtain ⟨Un, hUn, hUnfinite, hYnUn⟩ :=
    exists_finiteCharacter_wave_initialSet_superset_of_finite_target_gap
      K.normalized_isNormalized hYnClean hgapNormalized
  let U := K.liftNormalizedFamily Un
  have hUK : K.IsWave U := hUn.liftNormalizedFamily
  have hUH : H.IsWave U := DWeb.IsWave.of_retarget H hUK hroof
  have hUfinite : H.HasFiniteCharacter U :=
    hasFiniteCharacter_liftNormalizedFamily K hUnfinite
  refine ⟨U, hUH, hUfinite, ?_⟩
  intro x hxW
  have hxY : x ∈ H.initialSet Y := by
    rw [hY.initialSet_eq]
    exact hxW
  have hxYn : x ∈ K.normalized.initialSet Yn := by
    rw [hYnInitialEq]
    exact hxY
  have hxUn : x ∈ K.normalized.initialSet Un := hYnUn hxYn
  change x ∈ K.initialSet (K.liftNormalizedFamily Un)
  rw [K.initialSet_liftNormalizedFamily]
  exact hxUn

#print axioms exists_finiteCharacter_wave_initialSet_superset_of_finite_roof_defect

end SingularFiniteRoofDefectAbsorptionStrong
end CardinalInduction
end Erdos599
