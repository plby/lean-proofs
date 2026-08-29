/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.FiniteDeletion
import ErdosProblems.Erdos599.SingularMarkedResidualExchange
import ErdosProblems.Erdos599.WaveLimits

/-!
# Target absorption by a maximal residual wave

The colour-preserving residual switch used in the singular safe-selection
argument is most naturally compared with a forward-maximal hindrance.  The
switch need not literally forward-extend that hindrance.  Roof maximality is
enough: every target vertex occurring on the terminal frontier of any wave
is already on the essential terminal frontier of a forward-maximal wave.

Consequently, a wave whose frontier contains a genuinely new target cannot
coexist with forward maximality.  This is the precise maximal-wave
contradiction needed in the branch where a marked residual route never uses
an edge of the designated linkage.
-/

noncomputable section

open Set

namespace Erdos599
namespace CardinalInduction
namespace SingularMaximalWaveTargetAbsorption

open DWeb SingularMarkedResidualExchange SingularResidualWaveExchange
  SingularRetargetedRow

universe u

variable {V : Type u}

/-- A target vertex roofed by a set belongs to that set.  The trivial target
path is the witnessing test path in the definition of the roof. -/
theorem target_mem_of_mem_roof
    {G : DWeb V} {S : Set V} {b : V}
    (hbTarget : b ∈ G.target) (hbRoof : b ∈ G.roof S) :
    b ∈ S := by
  let p : DirectedPath.FinitePath G.graph :=
    DirectedPath.FinitePath.trivial G.graph b
  obtain ⟨x, hxp, hxS⟩ := hbRoof p ⟨rfl, hbTarget⟩
  have hxb : x = b := by
    simpa only [p, DirectedPath.FinitePath.support_trivial,
      Set.mem_singleton_iff] using hxp
  exact hxb ▸ hxS

/-- Every target terminal of any wave belongs to the essential terminal
frontier of a forward-extension-maximal wave.  This packages Lemma 3.22
(`roofLE_of_isMax`) in the literal form needed by the residual colour
switch. -/
theorem target_mem_terminalFrontier_essentialWarpPart_of_isMax
    {G : DWeb V} (M : G.Wave) (hMmax : IsMax M)
    {W : Set G.DPath} (hW : G.IsWave W) {b : V}
    (hbTarget : b ∈ G.target)
    (hbW : b ∈ G.terminalFrontier W) :
    b ∈ G.terminalFrontier (G.essentialWarpPart M.1) := by
  have hroofLE : G.RoofLE W M.1 :=
    G.roofLE_of_isMax hMmax ⟨W, hW⟩
  have hbRoofM : b ∈ G.roof (G.terminalFrontier M.1) :=
    hroofLE (G.subset_roof (G.terminalFrontier W) hbW)
  have hbRoofEssential :
      b ∈ G.roof
        (G.terminalFrontier (G.essentialWarpPart M.1)) := by
    rw [G.terminalFrontier_essentialWarpPart, G.roof_essential]
    exact hbRoofM
  exact target_mem_of_mem_roof hbTarget hbRoofEssential

/-- Contradiction form: a wave cannot acquire a target terminal outside the
essential frontier of a forward-maximal wave. -/
theorem not_exists_wave_with_fresh_target_terminal_of_isMax
    {G : DWeb V} (M : G.Wave) (hMmax : IsMax M) {b : V}
    (hbTarget : b ∈ G.target)
    (hbFresh : b ∉ G.terminalFrontier (G.essentialWarpPart M.1)) :
    ¬ ∃ W : Set G.DPath,
      G.IsWave W ∧ b ∈ G.terminalFrontier W := by
  rintro ⟨W, hW, hbW⟩
  exact hbFresh
    (target_mem_terminalFrontier_essentialWarpPart_of_isMax
      M hMmax hW hbTarget hbW)

/-- The essential part of a maximal hindrance is a finite-character
hindrance.  It is the clean old residual colour to which the finite marked
route machinery is applied; maximality remains attached to `M` and is used
through the preceding roof-absorption theorem. -/
theorem essentialWarpPart_isHindrance_hasFiniteCharacter
    {G : DWeb V} (M : G.Wave) (hMh : G.IsHindrance M.1) :
    G.IsHindrance (G.essentialWarpPart M.1) ∧
      G.HasFiniteCharacter (G.essentialWarpPart M.1) := by
  refine ⟨⟨M.2.essentialWarpPart, ?_⟩,
    G.hasFiniteCharacter_essentialWarpPart M.1⟩
  intro hfull
  apply hMh.2
  apply Set.Subset.antisymm M.2.2.1
  intro a haSource
  have haEssential : a ∈ G.initialSet (G.essentialWarpPart M.1) :=
    hfull.symm ▸ haSource
  obtain ⟨p, hp, hpa⟩ := haEssential
  exact ⟨p, hp.1, hpa⟩

/-- A hindered web therefore supplies one finite residual colour together
with a maximal ambient wave whose essential frontier absorbs every target
terminal of every competing wave. -/
theorem exists_maximalHindrance_with_finiteEssentialPart
    {G : DWeb V} (hG : G.IsHindered) :
    ∃ M : G.Wave,
      IsMax M ∧ G.IsHindrance M.1 ∧
        G.IsHindrance (G.essentialWarpPart M.1) ∧
          G.HasFiniteCharacter (G.essentialWarpPart M.1) := by
  obtain ⟨M, hMmax, hMh⟩ := G.exists_maximal_hindrance hG
  exact ⟨M, hMmax, hMh,
    essentialWarpPart_isHindrance_hasFiniteCharacter M hMh⟩

/-! ## Feeding a specified maximal residual colour to the marked search -/

/-- Specified-hindrance form of the marked residual route theorem.  Unlike
`exists_markedRoute_of_residual_hindered`, this theorem does not choose a
new normalized hindrance internally.  It is therefore usable with the
finite essential part of a fixed maximal hindrance. -/
theorem exists_markedRoute_of_specified_residual_hindrance_targetFresh
    {G : DWeb V} (hNorm : G.IsNormalized) (hG : G.IsUnhindered)
    {A : Set V} (hA : A ⊆ G.source)
    {P : Set G.DPath}
    (hP : IsLinkageBetween G A G.target P)
    {U : Set ((G.delete (G.vertexSet P)).DPath)}
    (hU : (G.delete (G.vertexSet P)).IsHindrance U)
    (hUfin : (G.delete (G.vertexSet P)).HasFiniteCharacter U) :
    ∃ a b : V, ∃ l : List (OneHoleResidualState V),
      a ∈ (G.delete (G.vertexSet P)).source \
        (G.delete (G.vertexSet P)).initialSet U ∧
      b ∈ G.target \
        (G.delete (G.vertexSet P)).terminalFrontier U ∧
      b ∉ G.vertexSet P ∧
      IsReducedMarkedRoute
        (G.retarget
          (G.target ∪
            (G.delete (G.vertexSet P)).terminalFrontier U))
        (P ∪ G.liftDeleteFamily (G.vertexSet P) U) a b l := by
  let X := G.vertexSet P
  let H := G.delete X
  let L := G.liftDeleteFamily X U
  let C := G.target ∪ H.terminalFrontier U
  let K := G.retarget C
  let J := P ∪ L
  have hclean : K.IsCleanFiniteWarp J :=
    combinedWarp_isCleanFiniteWarp hNorm hA hP hU hUfin
  have hgapH : (H.source \ H.initialSet U).Nonempty := by
    rw [Set.nonempty_def]
    by_contra hempty
    apply hU.2
    apply Set.Subset.antisymm hU.1.2.1
    intro x hx
    by_contra hxU
    exact hempty ⟨x, hx, hxU⟩
  obtain ⟨a₀, ha₀⟩ := hgapH
  have hAsubX : A ⊆ X := by
    intro x hxA
    have hxInitial : x ∈ G.initialSet P := hP.initialSet_eq.symm ▸ hxA
    obtain ⟨p, hpP, rfl⟩ := hxInitial
    exact ⟨p, hpP, p.initial_mem_support⟩
  have ha₀Gap : a₀ ∈ K.source \ K.initialSet J := by
    constructor
    · exact ha₀.1.1
    · change a₀ ∉ G.initialSet (P ∪ L)
      rw [G.initialSet_union, hP.initialSet_eq,
        G.initialSet_liftDeleteFamily]
      intro ha
      rcases ha with haA | haU
      · exact ha₀.1.2 (hAsubX haA)
      · exact ha₀.2 haU
  have hKunhindered : K.IsUnhindered :=
    retarget_union_isUnhindered hG (H.terminalFrontier U)
  obtain ⟨a, b, l, ha, hb, hl⟩ :=
    exists_reducedMarkedRoute_to_target_of_unhindered
      K hKunhindered hclean ⟨a₀, ha₀Gap⟩
  have haNotX : a ∉ X := by
    rintro ⟨p, hpP, hap⟩
    have haSource : a ∈ G.source := ha.1
    have hae : a = p.initial := hNorm.eq_initial_of_mem_path p hap haSource
    have haA : a ∈ A := by
      rw [hae]
      rw [← hP.initialSet_eq]
      exact ⟨p, hpP, rfl⟩
    exact ha.2 (by
      change a ∈ G.initialSet (P ∪ L)
      rw [G.initialSet_union, hP.initialSet_eq]
      exact Or.inl haA)
  have haH : a ∈ H.source \ H.initialSet U := by
    refine ⟨⟨ha.1, haNotX⟩, ?_⟩
    intro haU
    apply ha.2
    change a ∈ G.initialSet (P ∪ L)
    rw [G.initialSet_union, G.initialSet_liftDeleteFamily]
    exact Or.inr haU
  have hbTarget : b ∈ G.target := by
    change b ∈ C \ G.terminalFrontier J at hb
    rcases hb.1 with hbG | hbU
    · exact hbG
    · exact False.elim (hb.2 (by
        change b ∈ G.terminalFrontier (P ∪ L)
        rw [G.terminalFrontier_union,
          G.terminalFrontier_liftDeleteFamily]
        exact Or.inr hbU))
  have hbFresh : b ∉ H.terminalFrontier U := by
    intro hbU
    apply hb.2
    change b ∈ G.terminalFrontier (P ∪ L)
    rw [G.terminalFrontier_union, G.terminalFrontier_liftDeleteFamily]
    exact Or.inr hbU
  have hbNotJ : b ∉ K.vertexSet J := by
    exact fun hbJ ↦
      Set.disjoint_left.1 hclean.target_gap_disjoint_vertexSet hb hbJ
  have hbNotX : b ∉ X := by
    intro hbX
    apply hbNotJ
    change b ∈ G.vertexSet (P ∪ L)
    rw [G.vertexSet_union]
    exact Or.inl hbX
  exact ⟨a, b, l, haH, ⟨hbTarget, hbFresh⟩, hbNotX, hl⟩

/-- Compatibility form of
`exists_markedRoute_of_specified_residual_hindrance_targetFresh`, retaining
the original endpoint interface. -/
theorem exists_markedRoute_of_specified_residual_hindrance
    {G : DWeb V} (hNorm : G.IsNormalized) (hG : G.IsUnhindered)
    {A : Set V} (hA : A ⊆ G.source)
    {P : Set G.DPath}
    (hP : IsLinkageBetween G A G.target P)
    {U : Set ((G.delete (G.vertexSet P)).DPath)}
    (hU : (G.delete (G.vertexSet P)).IsHindrance U)
    (hUfin : (G.delete (G.vertexSet P)).HasFiniteCharacter U) :
    ∃ a b : V, ∃ l : List (OneHoleResidualState V),
      a ∈ (G.delete (G.vertexSet P)).source \
        (G.delete (G.vertexSet P)).initialSet U ∧
      b ∈ G.target \
        (G.delete (G.vertexSet P)).terminalFrontier U ∧
      IsReducedMarkedRoute
        (G.retarget
          (G.target ∪
            (G.delete (G.vertexSet P)).terminalFrontier U))
        (P ∪ G.liftDeleteFamily (G.vertexSet P) U) a b l := by
  obtain ⟨a, b, l, ha, hb, _hbNotP, hl⟩ :=
    exists_markedRoute_of_specified_residual_hindrance_targetFresh
      hNorm hG hA hP hU hUfin
  exact ⟨a, b, l, ha, hb, hl⟩

/-- The exact maximal-colour input for the selective switch.  If deleting
the designated linkage is hindered, choose a maximal residual hindrance,
pass to its finite essential part, and run the marked search against that
specific colour. -/
theorem exists_maximalHindrance_markedRoute_of_residual_hindered
    {G : DWeb V} (hNorm : G.IsNormalized) (hG : G.IsUnhindered)
    {A : Set V} (hA : A ⊆ G.source)
    {P : Set G.DPath}
    (hP : IsLinkageBetween G A G.target P)
    (hresidual : (G.delete (G.vertexSet P)).IsHindered) :
    ∃ M : (G.delete (G.vertexSet P)).Wave,
      IsMax M ∧ (G.delete (G.vertexSet P)).IsHindrance M.1 ∧
      let U := (G.delete (G.vertexSet P)).essentialWarpPart M.1
      (G.delete (G.vertexSet P)).IsHindrance U ∧
      (G.delete (G.vertexSet P)).HasFiniteCharacter U ∧
      ∃ a b : V, ∃ l : List (OneHoleResidualState V),
        a ∈ (G.delete (G.vertexSet P)).source \
          (G.delete (G.vertexSet P)).initialSet U ∧
        b ∈ G.target \
          (G.delete (G.vertexSet P)).terminalFrontier U ∧
        IsReducedMarkedRoute
          (G.retarget
            (G.target ∪
              (G.delete (G.vertexSet P)).terminalFrontier U))
          (P ∪ G.liftDeleteFamily (G.vertexSet P) U) a b l := by
  obtain ⟨M, hMmax, hMh, hEssH, hEssFin⟩ :=
    exists_maximalHindrance_with_finiteEssentialPart hresidual
  obtain ⟨a, b, l, ha, hb, hl⟩ :=
    exists_markedRoute_of_specified_residual_hindrance
      hNorm hG hA hP hEssH hEssFin
  exact ⟨M, hMmax, hMh, hEssH, hEssFin, a, b, l, ha, hb, hl⟩

/-- Endpoint-fresh refinement of
`exists_maximalHindrance_markedRoute_of_residual_hindered`.  The final
marked target lies outside the designated carrier, which is the hypothesis
needed by the last-contact colour-order lemma. -/
theorem exists_maximalHindrance_markedRoute_targetFresh_of_residual_hindered
    {G : DWeb V} (hNorm : G.IsNormalized) (hG : G.IsUnhindered)
    {A : Set V} (hA : A ⊆ G.source)
    {P : Set G.DPath}
    (hP : IsLinkageBetween G A G.target P)
    (hresidual : (G.delete (G.vertexSet P)).IsHindered) :
    ∃ M : (G.delete (G.vertexSet P)).Wave,
      IsMax M ∧ (G.delete (G.vertexSet P)).IsHindrance M.1 ∧
      let U := (G.delete (G.vertexSet P)).essentialWarpPart M.1
      (G.delete (G.vertexSet P)).IsHindrance U ∧
      (G.delete (G.vertexSet P)).HasFiniteCharacter U ∧
      ∃ a b : V, ∃ l : List (OneHoleResidualState V),
        a ∈ (G.delete (G.vertexSet P)).source \
          (G.delete (G.vertexSet P)).initialSet U ∧
        b ∈ G.target \
          (G.delete (G.vertexSet P)).terminalFrontier U ∧
        b ∉ G.vertexSet P ∧
        IsReducedMarkedRoute
          (G.retarget
            (G.target ∪
              (G.delete (G.vertexSet P)).terminalFrontier U))
          (P ∪ G.liftDeleteFamily (G.vertexSet P) U) a b l := by
  obtain ⟨M, hMmax, hMh, hEssH, hEssFin⟩ :=
    exists_maximalHindrance_with_finiteEssentialPart hresidual
  obtain ⟨a, b, l, ha, hb, hbNotP, hl⟩ :=
    exists_markedRoute_of_specified_residual_hindrance_targetFresh
      hNorm hG hA hP hEssH hEssFin
  exact ⟨M, hMmax, hMh, hEssH, hEssFin,
    a, b, l, ha, hb, hbNotP, hl⟩

/-! ## Turning an avoiding colour switch into a residual wave -/

/-- An exact one-point augmentation of a lifted residual wave becomes a
wave in the deleted web whenever its newly decomposed carrier still avoids
the deleted set.  The proof uses only the endpoint equations of the
augmentation: its old residual frontier remains on the new frontier, hence
continues to roof the residual source. -/
theorem residualWave_of_avoiding_onePointAugmentation
    (G : DWeb V) (X : Set V)
    {U : Set (G.delete X).DPath} (hU : (G.delete X).IsWave U)
    {Jplus : Set G.DPath}
    (hplus :
      (G.retarget
        (G.target ∪ (G.delete X).terminalFrontier U)).IsOnePointAugmentation
        (G.liftDeleteFamily X U) Jplus)
    (havoid : Disjoint X (G.vertexSet Jplus)) :
    (G.delete X).IsWave (G.restrictDeleteFamily X Jplus havoid.symm) := by
  obtain ⟨a, ha, b, hb, hwarp, _hfinite, hinitial, hterminal⟩ := hplus
  have hwarpG : G.IsWarp Jplus := hwarp
  have hinitialG : G.initialSet Jplus =
      insert a (G.initialSet (G.liftDeleteFamily X U)) := hinitial
  have hterminalG : G.terminalFrontier Jplus =
      insert b (G.terminalFrontier (G.liftDeleteFamily X U)) := hterminal
  have haVertex : a ∈ G.vertexSet Jplus := by
    have haInitial : a ∈ G.initialSet Jplus := by
      rw [hinitialG]
      exact Or.inl rfl
    obtain ⟨p, hp, hpa⟩ := haInitial
    exact ⟨p, hp, hpa ▸ p.initial_mem_support⟩
  have haFresh : a ∉ X := fun haX ↦
    Set.disjoint_left.1 havoid haX haVertex
  refine ⟨DWeb.IsWarp.restrictDeleteFamily G hwarpG havoid.symm, ?_, ?_⟩
  · rw [G.initialSet_restrictDeleteFamily, hinitialG,
      G.initialSet_liftDeleteFamily]
    rintro x (hxa | hxU)
    · subst x
      exact ⟨ha.1, haFresh⟩
    · exact hU.2.1 hxU
  · apply hU.2.2.trans
    apply (G.delete X).roof_mono
    intro x hx
    rw [G.terminalFrontier_restrictDeleteFamily, hterminalG,
      G.terminalFrontier_liftDeleteFamily]
    exact Or.inr hx

#print axioms target_mem_terminalFrontier_essentialWarpPart_of_isMax
#print axioms not_exists_wave_with_fresh_target_terminal_of_isMax
#print axioms essentialWarpPart_isHindrance_hasFiniteCharacter
#print axioms exists_maximalHindrance_with_finiteEssentialPart
#print axioms exists_markedRoute_of_specified_residual_hindrance_targetFresh
#print axioms exists_markedRoute_of_specified_residual_hindrance
#print axioms exists_maximalHindrance_markedRoute_of_residual_hindered
#print axioms exists_maximalHindrance_markedRoute_targetFresh_of_residual_hindered
#print axioms residualWave_of_avoiding_onePointAugmentation

end SingularMaximalWaveTargetAbsorption
end CardinalInduction
end Erdos599
