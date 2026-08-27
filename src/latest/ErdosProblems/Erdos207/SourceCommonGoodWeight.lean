/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceCommonExposureBound
import ErdosProblems.Erdos207.LocalizedCommonThreatLift
import ErdosProblems.Erdos207.CommonThreatGoodWeight

/-! # Summing the good terminal-bridge common-threat exposure classes -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def sourceCommonGoodWeight
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (F G : ForbiddenFamilyOn V) (T T' : TripleOn V)
    (H : TripleSystemOn V) (r s : ℕ) (w : ℝ≥0) : ℝ≥0 :=
  ∑ u ∈ (sourceCommonThreats W F G T T').filter
    (fun u ↦ H ⊆ u.remainder ∧ (u.exposureCode H).IsGood H r s),
      setWeight (vortexTripleWeight W w) (u.remainder \ H)

theorem sourceCommonGoodWeight_eq_code_sum
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (F G : ForbiddenFamilyOn V) (T T' : TripleOn V)
    (H : TripleSystemOn V) (q r s : ℕ) (w : ℝ≥0)
    (hF : ∀ E ∈ F, E.card ≤ q) (hG : ∀ E ∈ G, E.card ≤ q) :
    sourceCommonGoodWeight W F G T T' H r s w =
      ∑ c ∈ commonThreatExposureCodeSupport T T' H q,
        if c.IsGood H r s then
          ∑ u : sourceCommonExposureClass W F G T T' H c.1.1 c.1.2 c.2.1 c.2.2,
            setWeight (vortexTripleWeight W w) (u.1.remainder \ H)
        else 0 := by
  classical
  let active := (sourceCommonThreats W F G T T').filter
    (fun u ↦ H ⊆ u.remainder ∧ (u.exposureCode H).IsGood H r s)
  change (∑ u ∈ active, setWeight (vortexTripleWeight W w) (u.remainder \ H)) = _
  calc
    _ = ∑ c ∈ commonThreatExposureCodeSupport T T' H q,
        ∑ u ∈ active with u.exposureCode H = c,
          setWeight (vortexTripleWeight W w) (u.remainder \ H) := by
      symm
      apply sum_fiberwise_of_maps_to
      intro u _hu
      exact u.exposureCode_mem_support H q (hF u.first u.first_mem) (hG u.second u.second_mem)
    _ = _ := by
      apply sum_congr rfl
      intro c _hc
      by_cases hgood : c.IsGood H r s
      · rw [if_pos hgood]
        have hfibre : {u ∈ active | u.exposureCode H = c} =
            sourceCommonExposureClass W F G T T' H c.1.1 c.1.2 c.2.1 c.2.2 := by
          rw [sourceCommonExposureClass, commonThreatExposureClass_eq_code_fibre]
          ext u
          by_cases hcode : u.exposureCode H = c <;>
            simp [active, sourceCommonThreats, hcode, hgood, and_comm, and_left_comm]
        rw [hfibre]
        exact Finset.sum_subtype
          (sourceCommonExposureClass W F G T T' H c.1.1 c.1.2 c.2.1 c.2.2)
          (p := fun u ↦ u ∈ sourceCommonExposureClass W F G T T' H c.1.1 c.1.2 c.2.1 c.2.2)
          (fun _ ↦ Iff.rfl) (fun u ↦ setWeight (vortexTripleWeight W w) (u.remainder \ H))
      · rw [if_neg hgood]
        have hfibre : {u ∈ active | u.exposureCode H = c} = ∅ := by
          apply eq_empty_iff_forall_notMem.mpr
          intro u hu
          obtain ⟨hu, hcode⟩ := mem_filter.mp hu
          have hg := (mem_filter.mp hu).2.2
          rw [hcode] at hg
          exact hgood hg
        rw [hfibre, sum_empty]

def sourceCommonGoodCoefficient (ell q : ℕ) (w z z' : ℝ≥0) : ℝ≥0 :=
  ((2 ^ (4 * q) * (q + 1) ^ 2 : ℕ) : ℝ≥0) * sourceCommonClassCoefficient ell q w z z'

theorem sourceCommonGoodWeight_le
    {V : Type*} [Fintype V] [DecidableEq V] {ell q r s : ℕ}
    {W : Vortex V ell} {F G : ForbiddenFamilyOn V} {y z y' z' : ℝ≥0}
    (hF : SourceVortexWellSpread W r F y z) (hG : SourceVortexWellSpread W s G y' z')
    (hr : r ≤ q) (hs : s ≤ q) (T T' : TripleOn V) (H : TripleSystemOn V)
    (w : ℝ≥0) (hw : 1 ≤ w) :
    sourceCommonGoodWeight W F G T T' H r s w ≤ sourceCommonGoodCoefficient ell q w z z' := by
  classical
  have hf : ∀ E ∈ F, E.card ≤ q := fun E hE ↦ ((hF.uniform E hE).1.le).trans ((Nat.sub_le r 2).trans hr)
  have hg : ∀ E ∈ G, E.card ≤ q := fun E hE ↦ ((hG.uniform E hE).1.le).trans ((Nat.sub_le s 2).trans hs)
  by_cases hH : H.card ≤ 2 * q
  · rw [sourceCommonGoodWeight_eq_code_sum W F G T T' H q r s w hf hg]
    calc
      _ ≤ ∑ _c ∈ commonThreatExposureCodeSupport T T' H q, sourceCommonClassCoefficient ell q w z z' := by
        apply sum_le_sum
        intro c hc
        split_ifs with hgood
        · exact sourceCommonExposureClass_good_weight_le hF hG hr hs T T' H c.1.1 c.1.2
            ((card_second_root_of_mem_commonThreatExposureCodeSupport hc).trans (by omega)) hgood w hw
        · exact zero_le
      _ = (commonThreatExposureCodeSupport T T' H q).card * sourceCommonClassCoefficient ell q w z z' := by simp
      _ ≤ sourceCommonGoodCoefficient ell q w z z' := by
        apply mul_le_mul_of_nonneg_right _ zero_le
        have hc := card_commonThreatExposureCodeSupport_le T T' H q
        have htwo : (2 : ℕ) ^ (2 * H.card) ≤ 2 ^ (4 * q) :=
          Nat.pow_le_pow_right (by omega) (by omega)
        exact_mod_cast hc.trans (Nat.mul_le_mul_right ((q + 1) ^ 2) htwo)
  · have himpossible : ∀ u : CommonThreatWitness F G T T', ¬ H ⊆ u.remainder := by
      intro u hsub
      have hc := card_le_card hsub
      have hrem := u.remainder_card
      have hfirst := hf u.first u.first_mem
      have hsecond := hg u.second u.second_mem
      omega
    simp only [sourceCommonGoodWeight, himpossible, false_and, filter_false, sum_empty, zero_le]

end

end Erdos207
