/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.VortexLevelGreedy

/-!
# Sweeping all levels of a finite vortex

Each level is run to a positive stopping threshold for a horizon longer than
the finite triangle ground set.  Later phases only delete available
triangles, so thresholds already reached remain valid.
-/

namespace Erdos207

open Finset

noncomputable section

/-- Iterate saturated fixed-level phases over an explicit list of levels. -/
def vortexSweepListLaw
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (F : ForbiddenFamilyOn V) (W : Vortex V ell)
    (D : Fin (ell + 1) → ℕ) :
    List (Fin (ell + 1)) → GreedyStateOn V → FiniteLaw (GreedyStateOn V)
  | [], S => FiniteLaw.pure S
  | k :: ks, S =>
      FiniteLaw.bind
        (stoppedVortexLevelGreedyProcessLaw F W k (D k)
          (vortexPackingSaturationFuel V) S)
        (vortexSweepListLaw F W D ks)

/-- A smaller global available set has a smaller available set at every
fixed vortex level. -/
lemma vortexLevelAvailable_mono
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {W : Vortex V ell} {k : Fin (ell + 1)} {S S' : GreedyStateOn V}
    (hsub : S'.available ⊆ S.available) :
    vortexLevelAvailable W k S' ⊆ vortexLevelAvailable W k S := by
  intro T hT
  rw [mem_vortexLevelAvailable_iff] at hT ⊢
  exact ⟨hsub hT.1, hT.2⟩

/-- The level-filter cardinality agrees with `Vortex.levelCount`. -/
lemma card_vortexLevelAvailable
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (k : Fin (ell + 1)) (S : GreedyStateOn V) :
    (vortexLevelAvailable W k S).card = W.levelCount S.available k := by
  apply congrArg Finset.card
  ext T
  simp [vortexLevelAvailable, Vortex.levelCount, Vortex.trianglesAtLevel]

/-- Every listed threshold is reached, the absorber invariant is retained,
and the final availability is contained in the initial availability. -/
theorem vortexSweepListLaw_supported
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {F : ForbiddenFamilyOn V} {A : TripleSystemOn V} {W : Vortex V ell}
    {D : Fin (ell + 1) → ℕ} (hD : ∀ k, 0 < D k) :
    ∀ (ks : List (Fin (ell + 1))) (S₀ : GreedyStateOn V),
      AbsorberGreedyInvariant F A S₀ →
      (vortexSweepListLaw F W D ks S₀).SupportedOn
        (fun S ↦ AbsorberGreedyInvariant F A S ∧
          (∀ k ∈ ks, (vortexLevelAvailable W k S).card < D k) ∧
          S.available ⊆ S₀.available) := by
  intro ks
  induction ks with
  | nil =>
      intro S₀ hS₀
      exact FiniteLaw.supportedOn_pure _ ⟨hS₀, by simp, Subset.rfl⟩
  | cons k ks ih =>
      intro S₀ hS₀
      let L := stoppedVortexLevelGreedyProcessLaw F W k (D k)
        (vortexPackingSaturationFuel V) S₀
      have hsmall := stoppedVortexLevelGreedyProcessLaw_supported_belowThreshold_packing
        (W := W) (k := k) hS₀ (hD k)
      have hsub := stoppedVortexLevelGreedyProcessLaw_supported_available_subset
        F W k (D k) S₀ (vortexPackingSaturationFuel V)
      have hphase : L.SupportedOn (fun S ↦
          AbsorberGreedyInvariant F A S ∧
          (vortexLevelAvailable W k S).card < D k ∧
          S.available ⊆ S₀.available) := by
        intro S hmass
        exact ⟨(hsmall S hmass).1, (hsmall S hmass).2, hsub S hmass⟩
      change (FiniteLaw.bind L (vortexSweepListLaw F W D ks)).SupportedOn _
      refine hphase.bind _ ?_
      intro S₁ hS₁
      have htail := ih S₁ hS₁.1
      intro S₂ hmass
      have hS₂ := htail S₂ hmass
      refine ⟨hS₂.1, ?_, hS₂.2.2.trans hS₁.2.2⟩
      intro j hj
      simp only [List.mem_cons] at hj
      rcases hj with rfl | hj
      · exact (card_le_card
          (vortexLevelAvailable_mono hS₂.2.2)).trans_lt hS₁.2.1
      · exact hS₂.2.1 j hj

/-- The canonical sweep visits every vortex level exactly once. -/
def vortexSweepLaw
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (F : ForbiddenFamilyOn V) (W : Vortex V ell)
    (D : Fin (ell + 1) → ℕ) (S : GreedyStateOn V) :
    FiniteLaw (GreedyStateOn V) :=
  vortexSweepListLaw F W D (List.ofFn id) S

/-- A complete sweep leaves at most the sum of the level thresholds many
available triangles. -/
theorem vortexSweepLaw_supported_globalBound
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {F : ForbiddenFamilyOn V} {A : TripleSystemOn V} {W : Vortex V ell}
    {D : Fin (ell + 1) → ℕ} (hD : ∀ k, 0 < D k)
    {S₀ : GreedyStateOn V} (hS₀ : AbsorberGreedyInvariant F A S₀) :
    (vortexSweepLaw F W D S₀).SupportedOn
      (fun S ↦ AbsorberGreedyInvariant F A S ∧
        S.available.card ≤ ∑ k, D k ∧ S.available ⊆ S₀.available) := by
  have hsweep := vortexSweepListLaw_supported (W := W) hD
    (List.ofFn id) S₀ hS₀
  intro S hmass
  have hS := hsweep S hmass
  refine ⟨hS.1, ?_, hS.2.2⟩
  rw [← W.sum_levelCount S.available]
  apply sum_le_sum
  intro k _hk
  rw [← card_vortexLevelAvailable W k S]
  exact Nat.le_of_lt (hS.2.1 k
    (List.mem_ofFn.mpr ⟨k, rfl⟩))

/-- Deterministic extraction from the positive-mass support of the complete
vortex sweep. -/
theorem exists_vortexSweep_state_globalBound
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {F : ForbiddenFamilyOn V} {A : TripleSystemOn V} {W : Vortex V ell}
    {D : Fin (ell + 1) → ℕ} (hD : ∀ k, 0 < D k)
    {S₀ : GreedyStateOn V} (hS₀ : AbsorberGreedyInvariant F A S₀) :
    ∃ S : GreedyStateOn V,
      AbsorberGreedyInvariant F A S ∧
      S.available.card ≤ ∑ k, D k ∧ S.available ⊆ S₀.available := by
  let L := vortexSweepLaw F W D S₀
  have hpos : 0 < ∑ S, L.mass S := by
    rw [L.sum_mass]
    exact zero_lt_one
  obtain ⟨S, _hSuniv, hSmass⟩ := Finset.sum_pos_iff.mp hpos
  exact ⟨S,
    vortexSweepLaw_supported_globalBound hD hS₀ S hSmass⟩

end

end Erdos207
