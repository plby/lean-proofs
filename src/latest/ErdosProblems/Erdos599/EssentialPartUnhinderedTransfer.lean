/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HeightRoofBridge

/-!
# Unhinderedness transferred from the essential part with unchanged source

This extracts the sound source-restriction argument from the historical
scheduler module without importing its unrelated stale final certificates.
-/

namespace Erdos599.DWeb

open Set
open _root_.Erdos599.CardinalInduction

universe u

/-- Fullness also transfers in the other direction, without requiring
source equality: lift the wave and then restrict its full set of initials. -/
theorem essentialPart_isUnhindered_of_isUnhindered {V : Type u}
    (Q : DWeb V) (hQ : Q.IsUnhindered) : Q.essentialPart.IsUnhindered := by
  rw [Q.essentialPart.isUnhindered_iff]
  intro W hW
  let U : Set Q.DPath := Q.liftEssentialPartFamily W
  have hU : Q.IsWave U := Q.isWave_liftEssentialPartFamily hW
  have hfull : Q.initialSet U = Q.source := Q.isUnhindered_iff.mp hQ U hU
  have hinitial : Q.essentialPart.initialSet W = Q.source := by
    simpa only [U, Q.initialSet_liftEssentialPartFamily] using hfull
  apply Set.Subset.antisymm hW.2.1
  intro x hx
  rw [hinitial]
  rw [DWeb.essentialPart_source] at hx
  exact hx.1

/-- Restricting each wave to its target-reaching essential components
retains all sources when the essential part has the same source set. -/
theorem isUnhindered_of_essentialPart_of_source_eq {V : Type u}
    (Q : DWeb V) (hsource : Q.essentialPart.source = Q.source)
    (hessential : Q.essentialPart.IsUnhindered) : Q.IsUnhindered := by
  rw [Q.isUnhindered_iff]
  intro W hW
  let U := SliceCandidate.restrictEssentialWarpPartFamily Q W
  have hU : Q.essentialPart.IsWave U := SliceCandidate.isWave_restrictEssentialWarpPartFamily Q hW
  have hUinitial : Q.essentialPart.initialSet U = Q.essentialPart.source :=
    Q.essentialPart.isUnhindered_iff.mp hessential U hU
  apply Set.Subset.antisymm hW.2.1
  intro x hx
  have hxEssential : x ∈ Q.essentialPart.source := hsource.symm ▸ hx
  have hxInitial : x ∈ Q.essentialPart.initialSet U := hUinitial.symm ▸ hxEssential
  obtain ⟨q, ⟨p, rfl⟩, hqx⟩ := hxInitial
  refine ⟨p.1, p.2.1, ?_⟩
  simpa only [SliceCandidate.initial_restrictEssentialPartPath] using hqx

#print axioms isUnhindered_of_essentialPart_of_source_eq
#print axioms essentialPart_isUnhindered_of_isUnhindered

end Erdos599.DWeb
