/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.CommonThreatWitness
import ErdosProblems.Erdos207.RootedThreatAbsorberBound

/-! # Summing common-threat extension bounds over configuration families -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

namespace CommonThreatWitness

theorem ext_data {W : Type*} [DecidableEq W]
    {F G : Finset (Finset W)} {T T' : W} (w z : CommonThreatWitness F G T T')
    (hb : w.bridge = z.bridge) (hf : w.first = z.first) (hs : w.second = z.second) :
    w = z := by
  cases w
  cases z
  simp_all

def unionCode {W I J : Type*} [Fintype W] [DecidableEq W] [Fintype I] [Fintype J]
    (F : I → Finset (Finset W)) (G : J → Finset (Finset W)) (T T' : W)
    (w : CommonThreatWitness (univ.biUnion F) (univ.biUnion G) T T') :
    Σ i : I, Σ j : J, CommonThreatWitness (F i) (G j) T T' := by
  classical
  have hf : ∃ i, w.first ∈ F i := by simpa using w.first_mem
  have hs : ∃ j, w.second ∈ G j := by simpa using w.second_mem
  exact ⟨hf.choose, hs.choose,
    { w with first_mem := hf.choose_spec, second_mem := hs.choose_spec }⟩

theorem unionCode_injective
    {W I J : Type*} [Fintype W] [DecidableEq W] [Fintype I] [Fintype J]
    (F : I → Finset (Finset W)) (G : J → Finset (Finset W)) (T T' : W) :
    Function.Injective (unionCode F G T T') := by
  intro w z h
  apply ext_data
  · exact congrArg (fun u ↦ u.2.2.bridge) h
  · exact congrArg (fun u ↦ u.2.2.first) h
  · exact congrArg (fun u ↦ u.2.2.second) h

@[simp] theorem unionCode_remainder
    {W I J : Type*} [Fintype W] [DecidableEq W] [Fintype I] [Fintype J]
    (F : I → Finset (Finset W)) (G : J → Finset (Finset W)) (T T' : W)
    (w : CommonThreatWitness (univ.biUnion F) (univ.biUnion G) T T') :
    (unionCode F G T T' w).2.2.remainder = w.remainder := rfl

end CommonThreatWitness

theorem extensionWeight_commonThreat_union_le
    {W I J : Type*} [Fintype W] [DecidableEq W] [Fintype I] [Fintype J]
    (F : I → Finset (Finset W)) (G : J → Finset (Finset W)) (T T' : W)
    (p : W → ℝ≥0) (H : Finset W) :
    extensionWeight (fun w : CommonThreatWitness (univ.biUnion F) (univ.biUnion G) T T' ↦
      w.remainder) p H ≤
      ∑ i, ∑ j, extensionWeight
        (fun w : CommonThreatWitness (F i) (G j) T T' ↦ w.remainder) p H := by
  classical
  have h := sum_le_sum_of_injective_code (CommonThreatWitness.unionCode F G T T')
    (CommonThreatWitness.unionCode_injective F G T T')
    (fun w ↦ if H ⊆ w.remainder then setWeight p (w.remainder \ H) else 0)
    (fun u : Σ i : I, Σ j : J, CommonThreatWitness (F i) (G j) T T' ↦
      if H ⊆ u.2.2.remainder then setWeight p (u.2.2.remainder \ H) else 0)
    (fun _ ↦ le_rfl)
  simpa only [Fintype.sum_sigma, extensionWeight] using h

theorem commonThreat_union_hasExtensionBound
    {W I J : Type*} [Fintype W] [DecidableEq W] [Fintype I] [Fintype J]
    (F : I → Finset (Finset W)) (G : J → Finset (Finset W)) (T T' : W)
    (p : W → ℝ≥0) (κ : I → J → ℝ≥0)
    (hκ : ∀ i j, HasExtensionBound
      (fun w : CommonThreatWitness (F i) (G j) T T' ↦ w.remainder) p (κ i j)) :
    HasExtensionBound
      (fun w : CommonThreatWitness (univ.biUnion F) (univ.biUnion G) T T' ↦ w.remainder)
      p (∑ i, ∑ j, κ i j) := by
  intro H
  exact (extensionWeight_commonThreat_union_le F G T T' p H).trans
    (sum_le_sum fun i _ ↦ sum_le_sum fun j _ ↦ hκ i j H)

end

end Erdos207
