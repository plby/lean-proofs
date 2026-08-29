/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularMaximalWaveTargetAbsorption

/-!
# A maximal residual exchange must use the freed carrier

Changing a designated target linkage from `P` to `P'` may free vertices of
the old carrier.  If a one-point augmentation of the essential part of a
maximal residual hindrance avoids the new carrier, it cannot also avoid all
of those freed vertices.  Otherwise it avoids the whole old carrier, hence
restricts to a residual wave whose new target-frontier point contradicts
maximality.

This is the contact form needed by a finite roof-defect correction.  It does
not assert the false statement that an arbitrary finite exchange preserves
the old residual wave.
-/

noncomputable section

open Set

namespace Erdos599
namespace CardinalInduction
namespace SingularFreedCarrierForcedContact

open DWeb
open SingularMaximalWaveTargetAbsorption

universe u

variable {V : Type u}

/-- A residual one-point augmentation behind the new carrier must meet the
part of the old carrier which the target-linkage update freed. -/
theorem not_disjoint_freedCarrier_residualAugmentation_of_maximal
    (G : DWeb V) {P P' : Set G.DPath}
    (M : (G.delete (G.vertexSet P)).Wave) (hMmax : IsMax M)
    (hMh : (G.delete (G.vertexSet P)).IsHindrance M.1)
    {Rplus : Set G.DPath}
    (hplus :
      let U := (G.delete (G.vertexSet P)).essentialWarpPart M.1
      (G.retarget
        (G.target ∪
          (G.delete (G.vertexSet P)).terminalFrontier U)).IsOnePointAugmentation
        (G.liftDeleteFamily (G.vertexSet P) U) Rplus)
    (havoidNew : Disjoint (G.vertexSet P') (G.vertexSet Rplus)) :
    ¬ Disjoint (G.vertexSet P \ G.vertexSet P')
        (G.vertexSet Rplus) := by
  let X := G.vertexSet P
  let H := G.delete X
  let U := H.essentialWarpPart M.1
  let L := G.liftDeleteFamily X U
  let K := G.retarget (G.target ∪ H.terminalFrontier U)
  have hUh : H.IsHindrance U :=
    (essentialWarpPart_isHindrance_hasFiniteCharacter M hMh).1
  change K.IsOnePointAugmentation L Rplus at hplus
  intro havoidFreed
  have havoidOld : Disjoint X (G.vertexSet Rplus) := by
    rw [Set.disjoint_left]
    intro x hxP hxR
    by_cases hxP' : x ∈ G.vertexSet P'
    · exact Set.disjoint_left.1 havoidNew hxP' hxR
    · exact Set.disjoint_left.1 havoidFreed ⟨hxP, hxP'⟩ hxR
  have hW : H.IsWave
      (G.restrictDeleteFamily X Rplus havoidOld.symm) :=
    residualWave_of_avoiding_onePointAugmentation
      G X hUh.1 hplus havoidOld
  obtain ⟨a, ha, b, hb, _hwarp, _hfinite, _hinitial, hterminal⟩ := hplus
  have hbNotOldFrontier : b ∉ H.terminalFrontier U := by
    intro hbU
    apply hb.2
    change b ∈ G.terminalFrontier L
    rw [G.terminalFrontier_liftDeleteFamily]
    exact hbU
  have hbTarget : b ∈ G.target := by
    rcases hb.1 with hbG | hbU
    · exact hbG
    · exact False.elim (hbNotOldFrontier hbU)
  have hbRplus : b ∈ G.terminalFrontier Rplus := by
    change G.terminalFrontier Rplus =
      insert b (G.terminalFrontier L) at hterminal
    rw [hterminal]
    exact Or.inl rfl
  have hbNotX : b ∉ X := by
    intro hbX
    obtain ⟨p, hp, hpterm⟩ := hbRplus
    exact Set.disjoint_left.1 havoidOld hbX
      ⟨p, hp, G.terminal_mem_support hpterm⟩
  have hbHTarget : b ∈ H.target := ⟨hbTarget, hbNotX⟩
  have hbW : b ∈ H.terminalFrontier
      (G.restrictDeleteFamily X Rplus havoidOld.symm) := by
    rw [G.terminalFrontier_restrictDeleteFamily]
    exact hbRplus
  exact hbNotOldFrontier
    (target_mem_terminalFrontier_essentialWarpPart_of_isMax
      M hMmax hW hbHTarget hbW)

/-- Path-level form of the forced contact: an old designated path and a new
residual path meet at a vertex which is absent from the new designated
carrier.  This is the form used by finite contact-window arguments. -/
theorem exists_oldPath_residualPath_contact_outside_newCarrier
    (G : DWeb V) {P P' : Set G.DPath}
    (M : (G.delete (G.vertexSet P)).Wave) (hMmax : IsMax M)
    (hMh : (G.delete (G.vertexSet P)).IsHindrance M.1)
    {Rplus : Set G.DPath}
    (hplus :
      let U := (G.delete (G.vertexSet P)).essentialWarpPart M.1
      (G.retarget
        (G.target ∪
          (G.delete (G.vertexSet P)).terminalFrontier U)).IsOnePointAugmentation
        (G.liftDeleteFamily (G.vertexSet P) U) Rplus)
    (havoidNew : Disjoint (G.vertexSet P') (G.vertexSet Rplus)) :
    ∃ p ∈ P, ∃ r ∈ Rplus, ∃ x : V,
      x ∈ p.support ∧ x ∈ r.support ∧ x ∉ G.vertexSet P' := by
  have hcontact :=
    not_disjoint_freedCarrier_residualAugmentation_of_maximal
      G M hMmax hMh hplus havoidNew
  obtain ⟨x, hxFreed, hxResidual⟩ := Set.not_disjoint_iff.mp hcontact
  obtain ⟨p, hp, hxp⟩ := hxFreed.1
  obtain ⟨r, hr, hxr⟩ := hxResidual
  exact ⟨p, hp, r, hr, x, hxp, hxr, hxFreed.2⟩

#print axioms not_disjoint_freedCarrier_residualAugmentation_of_maximal
#print axioms exists_oldPath_residualPath_contact_outside_newCarrier

end SingularFreedCarrierForcedContact
end CardinalInduction
end Erdos599
