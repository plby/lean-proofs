/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.GainDefectWitness
import ErdosProblems.Erdos207.RootedThreatAbsorberBound

/-! # Summing fourth-moment weights over the second configuration's order -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def GainDefectWitness.secondUnionCode
    {W I : Type*} [Fintype W] [DecidableEq W] [Fintype I]
    (F : Finset (Finset W)) (G : I → Finset (Finset W)) (T : W) (z : ℕ)
    (w : GainDefectWitness F (univ.biUnion G) T z) : Σ i : I, GainDefectWitness F (G i) T z := by
  classical
  have hs : ∃ i, w.second ∈ G i := by simpa using w.second_mem
  exact ⟨hs.choose, { w with second_mem := hs.choose_spec }⟩

theorem GainDefectWitness.secondUnionCode_injective
    {W I : Type*} [Fintype W] [DecidableEq W] [Fintype I]
    (F : Finset (Finset W)) (G : I → Finset (Finset W)) (T : W) (z : ℕ) :
    Function.Injective (secondUnionCode F G T z) := by
  intro w u h
  have hf : w.first = u.first := congrArg (fun p ↦ p.2.first) h
  have hs : w.second = u.second := congrArg (fun p ↦ p.2.second) h
  have ho : w.omitted = u.omitted := congrArg (fun p ↦ p.2.omitted) h
  cases w
  cases u
  simp_all

theorem gainDefect_secondUnion_hasExtensionBound
    {W I : Type*} [Fintype W] [DecidableEq W] [Fintype I]
    (F : Finset (Finset W)) (G : I → Finset (Finset W)) (T : W) (z : ℕ)
    (p : W → ℝ≥0) (κ : I → ℝ≥0)
    (hκ : ∀ i, HasExtensionBound (fun w : GainDefectWitness F (G i) T z ↦ w.remainder) p (κ i)) :
    HasExtensionBound (fun w : GainDefectWitness F (univ.biUnion G) T z ↦ w.remainder)
      p (∑ i, κ i) := by
  classical
  intro H
  have h := sum_le_sum_of_injective_code (GainDefectWitness.secondUnionCode F G T z)
    (GainDefectWitness.secondUnionCode_injective F G T z)
    (fun w ↦ if H ⊆ w.remainder then setWeight p (w.remainder \ H) else 0)
    (fun u : Σ i : I, GainDefectWitness F (G i) T z ↦
      if H ⊆ u.2.remainder then setWeight p (u.2.remainder \ H) else 0)
    (fun _ ↦ le_rfl)
  have h' : extensionWeight (fun w : GainDefectWitness F (univ.biUnion G) T z ↦ w.remainder) p H ≤
      ∑ i, extensionWeight (fun w : GainDefectWitness F (G i) T z ↦ w.remainder) p H := by
    simpa only [Fintype.sum_sigma, extensionWeight] using h
  exact h'.trans (sum_le_sum fun i _ ↦ hκ i H)

end

end Erdos207
