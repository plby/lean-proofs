/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.LocalizedCommonThreatLift
import ErdosProblems.Erdos207.SourceCommonExposureGeometry
import ErdosProblems.Erdos207.CommonThreatExceptionalWeight

/-! # WS2 pays for the distinct equal-remainder common-threat exception -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def sourceExceptionalCommonThreats
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (F : ForbiddenFamilyOn V) (T T' : TripleOn V) :=
  (sourceCommonThreats W F F T T').filter fun u ↦ u.first.erase T = u.second.erase T'

def sourceExceptionalCommonCode
    {V : Type*} [Fintype V] [DecidableEq V] {ell j : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {T T' : TripleOn V}
    (hcard : ∀ E ∈ F, E.card = j - 2)
    (u : sourceExceptionalCommonThreats W F T T') :
    terminalOmissionCodes W (distinctEqualRemainderPairs F T T') (fun E ↦ E.1.erase T) (j - 4) := by
  have hd := mem_filter.mp u.2
  have hterm := (mem_filter.mp hd.1).2
  refine ⟨((u.1.first, u.1.second), u.1.leftRemainder), mem_terminalOmissionCodes_iff.mpr ?_⟩
  refine ⟨mem_distinctEqualRemainderPairs_iff.mpr
    ⟨u.1.first_mem, u.1.second_mem, u.1.different, u.1.first_root, u.1.second_root, hd.2⟩,
    mem_terminalRemainderChoices_iff.mpr ⟨erase_subset _ _, ?_, ?_⟩⟩
  · rw [u.1.leftRemainder_card, hcard u.1.first u.1.first_mem]
    omega
  · intro R hR
    change R ∈ (u.1.first.erase T) \ (u.1.first.erase T).erase u.1.bridge at hR
    rw [sdiff_erase_self (mem_erase.mpr ⟨u.1.bridge_ne_first, u.1.bridge_first⟩), mem_singleton] at hR
    simpa only [hR] using hterm

theorem sourceExceptionalCommonCode_injective
    {V : Type*} [Fintype V] [DecidableEq V] {ell j : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {T T' : TripleOn V}
    (hcard : ∀ E ∈ F, E.card = j - 2) :
    Function.Injective (sourceExceptionalCommonCode (W := W) (T := T) (T' := T') hcard) := by
  intro u v huv
  have hfirst := congrArg (fun x ↦ x.1.1.1) huv
  have hsecond := congrArg (fun x ↦ x.1.1.2) huv
  have hleft := congrArg (fun x ↦ x.1.2) huv
  change u.1.first = v.1.first at hfirst
  change u.1.second = v.1.second at hsecond
  change u.1.leftRemainder = v.1.leftRemainder at hleft
  have homit_u : u.1.first.erase T \ u.1.leftRemainder = {u.1.bridge} :=
    sdiff_erase_self (mem_erase.mpr ⟨u.1.bridge_ne_first, u.1.bridge_first⟩)
  have homit_v : v.1.first.erase T \ v.1.leftRemainder = {v.1.bridge} :=
    sdiff_erase_self (mem_erase.mpr ⟨v.1.bridge_ne_first, v.1.bridge_first⟩)
  have hbridge : u.1.bridge = v.1.bridge := by
    apply singleton_injective
    rw [← homit_u, ← homit_v, hfirst, hleft]
  apply Subtype.ext
  rcases u with ⟨u, hu⟩
  rcases v with ⟨v, hv⟩
  cases u
  cases v
  simp_all

theorem sourceExceptionalCommon_weight_le_omission
    {V : Type*} [Fintype V] [DecidableEq V] {ell j : ℕ}
    (W : Vortex V ell) (F : ForbiddenFamilyOn V) (T T' : TripleOn V)
    (hcard : ∀ E ∈ F, E.card = j - 2) (w : ℝ≥0) :
    ∑ u : sourceExceptionalCommonThreats W F T T', setWeight (vortexTripleWeight W w) u.1.remainder ≤
      sourceDistinctOmissionWeight W F T T' (j - 4) w := by
  rw [sourceDistinctOmissionWeight, Finset.sum_subtype
    (terminalOmissionCodes W (distinctEqualRemainderPairs F T T') (fun E ↦ E.1.erase T) (j - 4))
    (p := fun x ↦ x ∈ terminalOmissionCodes W (distinctEqualRemainderPairs F T T')
      (fun E ↦ E.1.erase T) (j - 4)) (fun _ ↦ Iff.rfl)]
  apply sum_le_sum_of_injective_code (sourceExceptionalCommonCode hcard)
    (sourceExceptionalCommonCode_injective hcard)
  intro u
  change setWeight (vortexTripleWeight W w) u.1.remainder ≤
    setWeight (vortexTripleWeight W w) u.1.leftRemainder
  rw [commonThreat_remainder_eq_left_of_equal_remainders u.1 (mem_filter.mp u.2).2]

theorem SourceVortexWellSpread.exceptional_common_weight_le
    {V : Type*} [Fintype V] [DecidableEq V] {ell j : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {y z : ℝ≥0}
    (hF : SourceVortexWellSpread W j F y z) (T T' : TripleOn V) (w : ℝ≥0) :
    ∑ u : sourceExceptionalCommonThreats W F T T', setWeight (vortexTripleWeight W w) u.1.remainder ≤
      (((j - 3) ^ ell : ℕ) : ℝ≥0) * ((2 : ℝ≥0) ^ (j - 3) * z) * w ^ (j - 4) := by
  have hb := hF.distinct_omission_weight_le T T' w (f := j - 4)
  have hn : (0 : ℝ≥0) < W.terminalSize := by exact_mod_cast hF.terminal_nonempty
  rw [mul_div_assoc, div_self (ne_of_gt (pow_pos hn (j - 4))), mul_one] at hb
  have hj : j - 4 + 1 = j - 3 := by have := hF.order; omega
  rw [hj] at hb
  exact (sourceExceptionalCommon_weight_le_omission W F T T'
    (fun E hE ↦ (hF.uniform E hE).1) w).trans hb

end

end Erdos207
