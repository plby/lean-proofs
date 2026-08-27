/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.TerminalProfileAugmentation

/-! # Pure outer profiles and their exact source scale -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def vortexPureProfile {ell : ℕ} (i : Fin ell) (f : ℕ) : VortexProfile ell :=
  fun a ↦ if a = i then f else 0

@[simp] theorem vortexPureProfile_apply_self {ell : ℕ} (i : Fin ell) (f : ℕ) :
    vortexPureProfile i f i = f := by simp [vortexPureProfile]

@[simp] theorem vortexPureProfile_mass {ell : ℕ} (i : Fin ell) (f : ℕ) :
    (vortexPureProfile i f).mass = f := by
  simp [VortexProfile.mass, vortexPureProfile]

theorem Vortex.profileScale_pure
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (i : Fin ell) (f : ℕ) :
    W.profileScale (vortexPureProfile i f) = (W.U i.castSucc).card ^ f := by
  unfold profileScale vortexPureProfile
  rw [prod_eq_single i]
  · simp
  · intro a _ hai
    simp [hai]
  · simp

theorem Vortex.outerProfile_eq_pure_of_level
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (C : TripleSystemOn V) (i : Fin ell)
    (hlevel : ∀ T ∈ C, W.level T = i.castSucc) :
    W.outerProfile C = vortexPureProfile i C.card := by
  funext a
  by_cases hai : a = i
  · subst a
    have hinter : C ∩ W.trianglesAtLevel i.castSucc = C := by
      apply inter_eq_left.mpr
      intro T hT
      exact (W.mem_trianglesAtLevel_iff _ T).mpr (hlevel T hT)
    simp [outerProfile, levelCount, hinter]
  · have hinter : C ∩ W.trianglesAtLevel a.castSucc = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro T hT
      obtain ⟨hTC, hTa⟩ := mem_inter.mp hT
      have heq := (W.mem_trianglesAtLevel_iff _ T).mp hTa
      have hv : a.val = i.val :=
        congrArg (fun x : Fin (ell + 1) ↦ x.val) (heq.symm.trans (hlevel T hTC))
      exact hai (Fin.ext hv)
    simp [outerProfile, levelCount, hinter, vortexPureProfile, hai]

theorem Vortex.level_eq_of_outerProfile_pure
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (C : TripleSystemOn V) (i : Fin ell)
    (hprofile : W.outerProfile C = vortexPureProfile i C.card) :
    ∀ T ∈ C, W.level T = i.castSucc := by
  have hc : (C ∩ W.trianglesAtLevel i.castSucc).card = C.card := by
    simpa only [outerProfile, levelCount, vortexPureProfile_apply_self] using congrFun hprofile i
  have heq : C ∩ W.trianglesAtLevel i.castSucc = C :=
    eq_of_subset_of_card_le inter_subset_left hc.ge
  intro T hT
  exact (W.mem_trianglesAtLevel_iff _ T).mp (mem_inter.mp (heq.symm ▸ hT)).2

theorem Vortex.sourceProfileScale_pure
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (i : Fin ell) (d f : ℕ) :
    W.sourceProfileScale d (vortexPureProfile i f) =
      (W.terminalSize : ℝ≥0) ^ d * ((W.U i.castSucc).card : ℝ≥0) ^ f /
        (W.terminalSize : ℝ≥0) ^ f := by
  simp only [sourceProfileScale, profileScale_pure, vortexPureProfile_mass, Nat.cast_pow]

theorem Vortex.levelSize_pow_le_sourceProfileScale_pure
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (i : Fin ell) (d f : ℕ)
    (hterminal : 0 < W.terminalSize) (hdf : d ≤ f) :
    ((W.U i.castSucc).card : ℝ≥0) ^ d ≤ W.sourceProfileScale d (vortexPureProfile i f) := by
  have hpos : (0 : ℝ≥0) < W.terminalSize := by exact_mod_cast hterminal
  have hsize : (W.terminalSize : ℝ≥0) ≤ (W.U i.castSucc).card := by
    exact_mod_cast card_le_card (W.antitone i.castSucc (Fin.last ell) (Fin.le_last _))
  rw [W.sourceProfileScale_pure, le_div_iff₀ (pow_pos hpos f)]
  have hp (x : ℝ≥0) : x ^ f = x ^ d * x ^ (f - d) := by
    rw [← pow_add, Nat.add_sub_of_le hdf]
  calc
    ((W.U i.castSucc).card : ℝ≥0) ^ d * (W.terminalSize : ℝ≥0) ^ f =
        (W.terminalSize : ℝ≥0) ^ d * ((W.U i.castSucc).card : ℝ≥0) ^ d *
          (W.terminalSize : ℝ≥0) ^ (f - d) := by rw [hp]; ring
    _ ≤ (W.terminalSize : ℝ≥0) ^ d * ((W.U i.castSucc).card : ℝ≥0) ^ d *
          ((W.U i.castSucc).card : ℝ≥0) ^ (f - d) := by gcongr
    _ = _ := by rw [hp]; ring

end

end Erdos207
