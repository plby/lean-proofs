/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Witness
import ErdosProblems.Erdos186.TrivialWitness

/-!
# Trivial enhanced CFP witnesses

The ordinary rank-zero discard-all witness becomes an enhanced witness as
soon as the reserve scale is positive and the fixed scale numerator is at
most its denominator.  This is the exact finite construction used for the
bounded-cardinality branch of the source-correct CFP corollaries.
-/

namespace Erdos186.CFP

open scoped BigOperators
open Filter

noncomputable section

variable {d : ℕ}

/-- A nonempty input and the source lower-scale hypothesis force a positive
natural reserve scale. -/
theorem scale_pos_of_nonempty
    {A : Finset (LatticePoint d)} {eta : ℝ} {s : ℕ}
    (hA : A.Nonempty) (heta : 0 ≤ eta)
    (hlower : Real.rpow (A.card : ℝ) eta ≤ (s : ℝ)) : 0 < s := by
  have hcard : (1 : ℝ) ≤ (A.card : ℝ) := by
    exact_mod_cast hA.card_pos
  have hone : (1 : ℝ) ≤ Real.rpow (A.card : ℝ) eta := by
    exact Real.one_le_rpow hcard heta
  have : (1 : ℝ) ≤ (s : ℝ) := hone.trans hlower
  exact_mod_cast this

/-- Discard every input point and use the symmetric rank-zero progression at
positive dilation `s`. -/
def discardAllEnhancedWitness
    (A : Finset (LatticePoint d)) (s D loss scaleNum scaleDen : ℕ)
    (hs : 0 < s) (hnum : 0 < scaleNum) (hden : 0 < scaleDen)
    (hscale : scaleNum ≤ scaleDen) (hcard : A.card ≤ loss) :
    EnhancedCFPWitness A s D s loss where
  toCFPWitness := discardAllWitness A s D s loss hcard
  k_pos := hs
  scaleNum := scaleNum
  scaleDen := scaleDen
  scaleNum_pos := hnum
  scaleDen_pos := hden
  scale_lower := Nat.mul_le_mul_right s hscale
  scale_upper := Nat.le_refl s
  progression_proper := by
    change (zeroGAP d).Proper
    intro x y _hxy
    funext i
    exact Fin.elim0 i
  progression_symmetric := by
    change (zeroGAP d).Symmetric
    refine ⟨Fin.elim0, ?_⟩
    constructor
    · funext i
      exact Fin.elim0 i
    · funext j
      simp [zeroGAP]
  progression_nondegenerate := by
    change (zeroGAP d).Nondegenerate
    exact fun i ↦ Fin.elim0 i
  covered_translate_homogeneous := by
    change ∃ z : Fin 0 → ℤ,
      (0 : LatticePoint d) + ((zeroGAP d).dilate s).offset =
        (fun j ↦ ∑ i, z i * (zeroGAP d).steps i j)
    refine ⟨Fin.elim0, ?_⟩
    funext j
    simp [zeroGAP]

/-- Fixed-scale packaging of `discardAllEnhancedWitness`. -/
def discardAllFixedScaleWitness
    (A : Finset (LatticePoint d)) (s D loss scaleNum scaleDen : ℕ)
    (hs : 0 < s) (hnum : 0 < scaleNum) (hden : 0 < scaleDen)
    (hscale : scaleNum ≤ scaleDen) (hcard : A.card ≤ loss) :
    FixedScaleWitness A s D s loss scaleNum scaleDen :=
  ⟨discardAllEnhancedWitness A s D loss scaleNum scaleDen
      hs hnum hden hscale hcard,
    rfl, rfl⟩

/-- On a nonempty set of cardinality at most `cutoff`, discarding every
point obeys the standard CFP logarithmic loss estimate with loss constant
`cutoff`. -/
theorem card_le_cutoff_mul_scale_mul_logb_add_one
    (A : Finset (LatticePoint d)) (s cutoff : ℕ)
    (hA : A.Nonempty) (hs : 0 < s) (hcard : A.card ≤ cutoff) :
    (A.card : ℝ) ≤ (cutoff : ℝ) * (s : ℝ) *
        Real.logb 2 (A.card : ℝ) + 1 := by
  by_cases hone : A.card = 1
  · simp [hone]
  · have htwo : 2 ≤ A.card := by
      have hpos := hA.card_pos
      omega
    have hcardReal : (2 : ℝ) ≤ (A.card : ℝ) := by
      exact_mod_cast htwo
    have hlogbOne : 1 ≤ Real.logb 2 (A.card : ℝ) := by
      rw [Real.logb, le_div_iff₀ (Real.log_pos (by norm_num))]
      simpa using Real.strictMonoOn_log.monotoneOn
        (by norm_num : (0 : ℝ) < 2)
        (zero_lt_two.trans_le hcardReal) hcardReal
    have hcardCutoff : (A.card : ℝ) ≤ (cutoff : ℝ) := by
      exact_mod_cast hcard
    have hsReal : (1 : ℝ) ≤ (s : ℝ) := by
      exact_mod_cast hs
    calc
      (A.card : ℝ) ≤ (cutoff : ℝ) := hcardCutoff
      _ ≤ (cutoff : ℝ) * (s : ℝ) := by
        nlinarith [show (0 : ℝ) ≤ (cutoff : ℝ) by positivity, hsReal]
      _ ≤ (cutoff : ℝ) * (s : ℝ) *
          Real.logb 2 (A.card : ℝ) := by
        exact le_mul_of_one_le_right (by positivity) hlogbOne
      _ ≤ (cutoff : ℝ) * (s : ℝ) *
          Real.logb 2 (A.card : ℝ) + 1 := by norm_num

/-- Complete fixed-scale output for the bounded-cardinality branch. -/
theorem exists_fixedScaleWitness_of_card_le
    (A : Finset (LatticePoint d)) (s D scaleNum scaleDen cutoff : ℕ)
    (hA : A.Nonempty) (hs : 0 < s)
    (hnum : 0 < scaleNum) (hden : 0 < scaleDen)
    (hscale : scaleNum ≤ scaleDen) (hcard : A.card ≤ cutoff) :
    ∃ k loss : ℕ,
      Nonempty (FixedScaleWitness A s D k loss scaleNum scaleDen) ∧
      (loss : ℝ) ≤ (cutoff : ℝ) * (s : ℝ) *
        Real.logb 2 (A.card : ℝ) + 1 := by
  exact ⟨s, A.card,
    ⟨discardAllFixedScaleWitness A s D A.card scaleNum scaleDen
      hs hnum hden hscale (Nat.le_refl A.card)⟩,
    card_le_cutoff_mul_scale_mul_logb_add_one A s cutoff
      hA hs hcard⟩

/-- Above a uniform cardinality threshold, the positive power lower bound on
`s` and the fixed-scale comparison force the returned dilation to dominate
any prescribed factor.  This is the large-input complement of
`exists_fixedScaleWitness_of_card_le`. -/
theorem exists_cardThreshold_factor_le_dilation
    (eta : ℝ) (scaleNum scaleDen factor : ℕ)
    (heta : 0 < eta) (hnum : 0 < scaleNum) (hden : 0 < scaleDen) :
    ∃ cutoff : ℕ, ∀ (card s k : ℕ),
      cutoff ≤ card →
      Real.rpow (card : ℝ) eta ≤ (s : ℝ) →
      scaleNum * s ≤ scaleDen * k →
      factor ≤ k := by
  have heventual :=
    ((tendsto_rpow_atTop heta).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop
      ((scaleDen * factor : ℕ) : ℝ)
  obtain ⟨cutoff, hcutoff⟩ := eventually_atTop.1 heventual
  refine ⟨cutoff, ?_⟩
  intro card s k hcard hlower hscale
  have hdenFactorReal : ((scaleDen * factor : ℕ) : ℝ) ≤ (s : ℝ) :=
    (hcutoff card hcard).trans hlower
  have hdenFactor : scaleDen * factor ≤ s := by
    exact_mod_cast hdenFactorReal
  have hsNum : s ≤ scaleNum * s := by
    calc
      s = 1 * s := by simp
      _ ≤ scaleNum * s := Nat.mul_le_mul_right s hnum
  have hmul : scaleDen * factor ≤ scaleDen * k :=
    hdenFactor.trans (hsNum.trans hscale)
  exact Nat.le_of_mul_le_mul_left hmul hden

end

end Erdos186.CFP

#print axioms Erdos186.CFP.discardAllFixedScaleWitness
