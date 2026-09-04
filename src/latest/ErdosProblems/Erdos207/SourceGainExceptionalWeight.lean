/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceGainForwardBound
import ErdosProblems.Erdos207.GainDefectExceptionalWeight

/-! # The distinct equal-remainder gain branch is controlled by source WS2 -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def sourceGainExceptionalClass
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (F G : ForbiddenFamilyOn V) (T : TripleOn V) (a : ℕ) (H : TripleSystemOn V) :=
  (gainDefectExceptionalClass F G T a H).filter
    fun u ↦ ∀ U ∈ u.omittedRoot, W.level U = Fin.last ell

theorem GainDefectWitness.left_omission_complement
    {V : Type*} [Fintype V] [DecidableEq V] {F G : ForbiddenFamilyOn V} {T : TripleOn V} {a : ℕ}
    (u : GainDefectWitness F G T a) : u.first.erase T \ u.leftRemainder = u.omitted := by
  have h := u.forward_first_omitted ∅ (empty_subset _)
  simpa only [GainDefectWitness.firstExposureRoot, inter_empty, insert_empty_eq,
    sdiff_empty, sdiff_singleton_eq_erase] using h

def sourceGainExceptionalCode
    {V : Type*} [Fintype V] [DecidableEq V] {ell j a : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {T T' : TripleOn V}
    (hcard : ∀ E ∈ F, E.card = j - 2)
    (u : sourceGainExceptionalClass W F F T a {T'}) :
    terminalOmissionCodes W (distinctEqualRemainderPairs F T T') (fun E ↦ E.1.erase T)
      (j - 2 - (a + 1)) := by
  classical
  have hd := mem_filter.mp u.2
  let p := gainDefectExceptionalEmbedding F T T' a ⟨u.1, hd.1⟩
  have hp := mem_equalRemainderOmissionCodes_iff.mp p.2
  refine ⟨((u.1.first, u.1.second), u.1.leftRemainder), mem_terminalOmissionCodes_iff.mpr ?_⟩
  refine ⟨hp.1, mem_terminalRemainderChoices_iff.mpr ⟨?_, ?_, ?_⟩⟩
  · intro U hU
    have hm := mem_sdiff.mp hU
    exact mem_erase.mpr ⟨fun heq ↦ hm.2 (mem_insert.mpr (Or.inl heq)), hm.1⟩
  · rw [u.1.leftRemainder_card, hcard u.1.first u.1.first_mem]
  · intro U hU
    rw [u.1.left_omission_complement] at hU
    exact hd.2 U (mem_insert_of_mem hU)

theorem sourceGainExceptionalCode_injective
    {V : Type*} [Fintype V] [DecidableEq V] {ell j a : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {T T' : TripleOn V}
    (hcard : ∀ E ∈ F, E.card = j - 2) :
    Function.Injective (sourceGainExceptionalCode (W := W) (T := T) (T' := T') (a := a) hcard) := by
  intro u v huv
  have hf := congrArg (fun x ↦ x.1.1.1) huv
  have hs := congrArg (fun x ↦ x.1.1.2) huv
  have hl := congrArg (fun x ↦ x.1.2) huv
  change u.1.first = v.1.first at hf
  change u.1.second = v.1.second at hs
  change u.1.leftRemainder = v.1.leftRemainder at hl
  have ho : u.1.omitted = v.1.omitted := by
    rw [← u.1.left_omission_complement, ← v.1.left_omission_complement, hf, hl]
  apply Subtype.ext
  rcases u with ⟨u, hu⟩
  rcases v with ⟨v, hv⟩
  cases u
  cases v
  simp_all

theorem sourceGainExceptional_weight_le_omission
    {V : Type*} [Fintype V] [DecidableEq V] {ell j a : ℕ}
    (W : Vortex V ell) (F : ForbiddenFamilyOn V) (T T' : TripleOn V)
    (hcard : ∀ E ∈ F, E.card = j - 2) (w : ℝ≥0) :
    ∑ u : sourceGainExceptionalClass W F F T a {T'},
      setWeight (vortexTripleWeight W w) (u.1.remainder \ {T'}) ≤
      sourceDistinctOmissionWeight W F T T' (j - 2 - (a + 1)) w := by
  classical
  rw [sourceDistinctOmissionWeight, Finset.sum_subtype
    (terminalOmissionCodes W (distinctEqualRemainderPairs F T T') (fun E ↦ E.1.erase T) (j - 2 - (a + 1)))
    (p := fun x ↦ x ∈ terminalOmissionCodes W (distinctEqualRemainderPairs F T T')
      (fun E ↦ E.1.erase T) (j - 2 - (a + 1))) (fun _ ↦ Iff.rfl)]
  apply sum_le_sum_of_injective_code (sourceGainExceptionalCode hcard) (sourceGainExceptionalCode_injective hcard)
  intro u
  change setWeight (vortexTripleWeight W w) (u.1.remainder \ {T'}) ≤
    setWeight (vortexTripleWeight W w) u.1.leftRemainder
  rw [u.1.remainder_sdiff_eq_left_of_forwardExceptional {T'}
    (mem_filter.mp (mem_filter.mp u.2).1).2.2.1]

theorem SourceVortexWellSpread.exceptional_gain_weight_le
    {V : Type*} [Fintype V] [DecidableEq V] {ell j a : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {y z : ℝ≥0}
    (hF : SourceVortexWellSpread W j F y z) (ha : 1 ≤ a)
    (T : TripleOn V) (H : TripleSystemOn V) (w : ℝ≥0) (hw : 1 ≤ w) :
    ∑ u : sourceGainExceptionalClass W F F T a H,
      setWeight (vortexTripleWeight W w) (u.1.remainder \ H) ≤
      ((((j + 1) ^ ell : ℕ) : ℝ≥0) * (2 : ℝ≥0) ^ j * z * w ^ j) *
        (W.terminalSize : ℝ≥0) ^ (a - 1) := by
  classical
  by_cases hH : H.card = 1
  · obtain ⟨T', rfl⟩ := card_eq_one.mp hH
    let f := j - 2 - (a + 1)
    let C : ℝ≥0 := (((f + 1) ^ ell : ℕ) : ℝ≥0) * ((2 : ℝ≥0) ^ (j - 3) * z) * w ^ f
    have hn : (1 : ℝ≥0) ≤ W.terminalSize := by exact_mod_cast hF.terminal_nonempty
    have hj := hF.order
    have hratio := source_weight_power_ratio_le (W.terminalSize : ℝ≥0) C (j - 4) f (a - 1)
      hn (by dsimp only [f]; omega)
    have hcoeff : C ≤ (((j + 1) ^ ell : ℕ) : ℝ≥0) * (2 : ℝ≥0) ^ j * z * w ^ j := by
      have hf : f ≤ j := by dsimp only [f]; omega
      have hp : (((f + 1) ^ ell : ℕ) : ℝ≥0) ≤ (((j + 1) ^ ell : ℕ) : ℝ≥0) := by
        exact_mod_cast Nat.pow_le_pow_left (by omega : f + 1 ≤ j + 1) ell
      dsimp only [C]
      rw [← mul_assoc]
      exact mul_le_mul' (mul_le_mul' (mul_le_mul' hp (pow_le_pow_right₀ (by norm_num) (Nat.sub_le j 3))) le_rfl)
        (pow_le_pow_right₀ hw hf)
    exact (sourceGainExceptional_weight_le_omission W F T T'
      (fun E hE ↦ (hF.uniform E hE).1) w).trans
      ((hF.distinct_omission_weight_le T T' w).trans
        (hratio.trans (mul_le_mul_of_nonneg_right hcoeff zero_le)))
  · have : IsEmpty (sourceGainExceptionalClass W F F T a H) := by
      refine ⟨fun u ↦ ?_⟩
      exact hH (mem_filter.mp (mem_filter.mp u.2).1).2.2.2.1
    simp only [Fintype.sum_empty, zero_le]

end

end Erdos207
