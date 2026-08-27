/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceGainReverseBound
import ErdosProblems.Erdos207.LocalizedGainDefectLift
import ErdosProblems.Erdos207.GainDefectReverseGoodWeight

/-! # Summing all reverse gain-defect source exposures -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def sourceGainReverseGoodWeight
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (F G : ForbiddenFamilyOn V) (T : TripleOn V) (a : ℕ)
    (H : TripleSystemOn V) (r s : ℕ) (w : ℝ≥0) : ℝ≥0 := by
  classical
  exact ∑ u ∈ (sourceGainDefects W F G T a).filter
    (fun u ↦ H ⊆ u.remainder ∧ u.ForwardExceptional H ∧
      s + 4 ≤ vortexRootExponent r u.reverseFirstRoot.card + vortexRootExponent s (u.reverseSecondRoot H).card),
      setWeight (vortexTripleWeight W w) (u.remainder \ H)

theorem sourceGainReverseGoodWeight_eq_code_sum
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (F G : ForbiddenFamilyOn V) (T : TripleOn V) (a : ℕ)
    (H : TripleSystemOn V) (q r s : ℕ) (w : ℝ≥0) (hF : ∀ E ∈ F, E.card ≤ q) :
    sourceGainReverseGoodWeight W F G T a H r s w =
      ∑ c ∈ gainDefectReverseCodeSupport T H q,
        if s + 4 ≤ vortexRootExponent r c.2 + vortexRootExponent s c.1.card then
          ∑ u : sourceGainReverseClass W F G T a H c.1 c.2,
            setWeight (vortexTripleWeight W w) (u.1.remainder \ H)
        else 0 := by
  classical
  let code := fun u : GainDefectWitness F G T a ↦ (u.reverseSecondRoot H, u.reverseFirstRoot.card)
  let active := (sourceGainDefects W F G T a).filter
    (fun u ↦ H ⊆ u.remainder ∧ u.ForwardExceptional H ∧
      s + 4 ≤ vortexRootExponent r u.reverseFirstRoot.card + vortexRootExponent s (u.reverseSecondRoot H).card)
  change (∑ u ∈ active, setWeight (vortexTripleWeight W w) (u.remainder \ H)) = _
  calc
    _ = ∑ c ∈ gainDefectReverseCodeSupport T H q,
        ∑ u ∈ active with code u = c, setWeight (vortexTripleWeight W w) (u.remainder \ H) := by
      symm
      apply sum_fiberwise_of_maps_to
      intro u _hu
      exact u.reverseCode_mem_support H q (hF u.first u.first_mem)
    _ = _ := by
      apply sum_congr rfl
      intro c _hc
      by_cases hgood : s + 4 ≤ vortexRootExponent r c.2 + vortexRootExponent s c.1.card
      · rw [if_pos hgood]
        have hfibre : {u ∈ active | code u = c} = sourceGainReverseClass W F G T a H c.1 c.2 := by
          ext u
          constructor
          · intro hu
            obtain ⟨hu, hc⟩ := mem_filter.mp hu
            have hd := (mem_filter.mp hu).2
            have ht := (mem_filter.mp (mem_filter.mp hu).1).2
            have hQ : u.reverseSecondRoot H = c.1 := congrArg Prod.fst hc
            have hb : u.reverseFirstRoot.card = c.2 := congrArg Prod.snd hc
            exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, hd.1, hd.2.1, hQ, hb⟩, ht⟩
          · intro hu
            have hd := (mem_filter.mp (mem_filter.mp hu).1).2
            have ht := (mem_filter.mp hu).2
            refine mem_filter.mpr ⟨mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, ht⟩,
              hd.1, hd.2.1, ?_⟩, Prod.ext hd.2.2.1 hd.2.2.2⟩
            simpa only [hd.2.2.1, hd.2.2.2] using hgood
        rw [hfibre]
        exact Finset.sum_subtype (sourceGainReverseClass W F G T a H c.1 c.2)
          (p := fun u ↦ u ∈ sourceGainReverseClass W F G T a H c.1 c.2)
          (fun _ ↦ Iff.rfl) (fun u ↦ setWeight (vortexTripleWeight W w) (u.remainder \ H))
      · rw [if_neg hgood]
        have hfibre : {u ∈ active | code u = c} = ∅ := by
          apply eq_empty_iff_forall_notMem.mpr
          intro u hu
          obtain ⟨hu, hc⟩ := mem_filter.mp hu
          have hg := (mem_filter.mp hu).2.2.2
          have hQ : u.reverseSecondRoot H = c.1 := congrArg Prod.fst hc
          have hb : u.reverseFirstRoot.card = c.2 := congrArg Prod.snd hc
          exact hgood (by simpa only [hQ, hb] using hg)
        rw [hfibre, sum_empty]

def sourceGainReverseGoodCoefficient (ell q : ℕ) (w z z' : ℝ≥0) : ℝ≥0 :=
  (2 * (q + 1) : ℝ≥0) * sourceCommonClassCoefficient ell q w z' z

theorem sourceGainReverseGoodWeight_le
    {V : Type*} [Fintype V] [DecidableEq V] {ell q r s a : ℕ}
    {W : Vortex V ell} {F G : ForbiddenFamilyOn V} {y z y' z' : ℝ≥0}
    (hF : SourceVortexWellSpread W r F y z) (hG : SourceVortexWellSpread W s G y' z')
    (hr : r ≤ q) (hs : s ≤ q) (ha : 1 ≤ a) (T : TripleOn V) (H : TripleSystemOn V)
    (w : ℝ≥0) (hw : 1 ≤ w) :
    sourceGainReverseGoodWeight W F G T a H r s w ≤
      sourceGainReverseGoodCoefficient ell q w z z' * (W.terminalSize : ℝ≥0) ^ (a - 1) := by
  classical
  have hf : ∀ E ∈ F, E.card ≤ q := fun E hE ↦ ((hF.uniform E hE).1.le).trans ((Nat.sub_le r 2).trans hr)
  rw [sourceGainReverseGoodWeight_eq_code_sum W F G T a H q r s w hf]
  let C := sourceCommonClassCoefficient ell q w z' z * (W.terminalSize : ℝ≥0) ^ (a - 1)
  calc
    _ ≤ ∑ _c ∈ gainDefectReverseCodeSupport T H q, C := by
      apply sum_le_sum
      intro c _hc
      split_ifs with hgood
      · exact sourceGainReverseClass_good_weight_le hF hG hr hs ha T H c.1 hgood w hw
      · exact zero_le
    _ = (gainDefectReverseCodeSupport T H q).card * C := by simp
    _ ≤ (2 * (q + 1) : ℝ≥0) * C := by
      apply mul_le_mul_of_nonneg_right _ zero_le
      have hc : (gainDefectReverseCodeSupport T H q).card ≤ 2 * (q + 1) := by
        rw [gainDefectReverseCodeSupport, card_product, card_range]
        exact Nat.mul_le_mul_right _ ((card_insert_le H {insert T H}).trans (by simp))
      exact_mod_cast hc
    _ = _ := by dsimp only [C, sourceGainReverseGoodCoefficient]; ring

end

end Erdos207
