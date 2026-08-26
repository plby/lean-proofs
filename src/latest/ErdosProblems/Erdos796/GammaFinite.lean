import ErdosProblems.Erdos796.SidonCardBound
import ErdosProblems.Erdos796.CofactorMajorant
import ErdosProblems.Erdos796.GammaCertificate

/- Ported to Lean/Mathlib 4.33.0; imports and tactic elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Unconditional finiteness of the cofactor variational constant

The explicit multiplicative-Sidon estimate supplies a summable pointwise
majorant for every compatible fibre.  This discharges the boundedness
hypothesis in the certified lower bound for `Gamma`.
-/

namespace Erdos796

/-- The sharp two-term large-index majorant furnished by the factor-graph
argument. -/
noncomputable def explicitSidonMajorant (j : ℕ) : ℝ :=
  (j : ℝ) ^ (5 / 6 : ℝ) + (3 / 2 : ℝ) * (j : ℝ) ^ (2 / 3 : ℝ)

/-- For the finitely many indices below the cutoff of the factorization
lemma, the trivial cardinal bound is used. -/
noncomputable def fullSidonMajorant (j : ℕ) : ℝ :=
  if j < 8 then (j : ℝ) else explicitSidonMajorant j

theorem excess_le_index {U : ℕ → Finset ℕ} (hU : Compatible U) (j : ℕ) :
    excess U j ≤ (j : ℝ) := by
  have hcardNat : (U j).card ≤ j := by
    have hsub := Finset.card_le_card (hU.1 j)
    simpa [positiveIcc] using! hsub
  have hcard : ((U j).card : ℝ) ≤ (j : ℝ) := by
    exact_mod_cast hcardNat
  have hprime : 0 ≤ (Nat.primeCounting j : ℝ) := by positivity
  have hreal :
      ((U j).card : ℝ) - 1 - (Nat.primeCounting j : ℝ) ≤ (j : ℝ) := by
    linarith
  simpa [excess, excessInt, Int.cast_sub, Int.cast_natCast] using! hreal

theorem compatible_excess_le_fullSidonMajorant
    (U : ℕ → Finset ℕ) (hU : Compatible U) (j : ℕ) :
    excess U j ≤ fullSidonMajorant j := by
  by_cases hj : 8 ≤ j
  · have hnot : ¬j < 8 := by omega
    rw [fullSidonMajorant, if_neg hnot]
    exact SidonCardBound.compatible_fiber_excess_le hU hj
  · have hjlt : j < 8 := by omega
    rw [fullSidonMajorant, if_pos hjlt]
    exact excess_le_index hU j

theorem explicitSidonMajorant_nonneg (j : ℕ) :
    0 ≤ explicitSidonMajorant j := by
  rw [explicitSidonMajorant]
  positivity

theorem explicitSidonMajorant_le_sidonMajorant {j : ℕ} (hj : 1 ≤ j) :
    explicitSidonMajorant j ≤ sidonMajorant j := by
  have hjReal : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have hpowers :
      (j : ℝ) ^ (2 / 3 : ℝ) ≤ (j : ℝ) ^ (5 / 6 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hjReal (by norm_num)
  rw [explicitSidonMajorant, sidonMajorant]
  calc
    (j : ℝ) ^ (5 / 6 : ℝ) +
          (3 / 2 : ℝ) * (j : ℝ) ^ (2 / 3 : ℝ) ≤
        (j : ℝ) ^ (5 / 6 : ℝ) +
          (3 / 2 : ℝ) * (j : ℝ) ^ (5 / 6 : ℝ) := by
      gcongr
    _ ≤ 3 * (j : ℝ) ^ (5 / 6 : ℝ) := by
      have hnonneg : 0 ≤ (j : ℝ) ^ (5 / 6 : ℝ) := by positivity
      linarith

theorem weightedMajorant_explicit_nonneg (k : ℕ) :
    0 ≤ weightedMajorant explicitSidonMajorant k := by
  rw [weightedMajorant]
  exact mul_nonneg (cofactorWeight_nonneg _) (explicitSidonMajorant_nonneg _)

theorem weightedMajorant_explicit_le_sidon (k : ℕ) :
    weightedMajorant explicitSidonMajorant k ≤
      weightedMajorant sidonMajorant k := by
  rw [weightedMajorant, weightedMajorant]
  exact mul_le_mul_of_nonneg_left
    (explicitSidonMajorant_le_sidonMajorant (Nat.succ_le_succ (Nat.zero_le k)))
    (cofactorWeight_nonneg _)

theorem summable_weightedMajorant_explicit :
    Summable (weightedMajorant explicitSidonMajorant) := by
  exact Summable.of_nonneg_of_le weightedMajorant_explicit_nonneg
    weightedMajorant_explicit_le_sidon summable_weightedMajorant_sidon

theorem eventually_weightedMajorant_full_eq_explicit :
    weightedMajorant explicitSidonMajorant =ᶠ[Filter.atTop]
      weightedMajorant fullSidonMajorant := by
  filter_upwards [Filter.eventually_ge_atTop 7] with k hk
  have hnot : ¬k + 1 < 8 := by omega
  simp [weightedMajorant, fullSidonMajorant, hnot]

theorem summable_weightedMajorant_full :
    Summable (weightedMajorant fullSidonMajorant) :=
  summable_weightedMajorant_explicit.congr_atTop
    eventually_weightedMajorant_full_eq_explicit

/-- The set of all finite compatible cofactor scores is now unconditionally
bounded above. -/
theorem gammaScores_bddAbove : BddAbove gammaScores :=
  gammaScores_bddAbove_of_uniform_majorant
    compatible_excess_le_fullSidonMajorant summable_weightedMajorant_full

/-- The finite certificate gives the unconditional lower bound. -/
theorem four_fifteenths_le_Gamma : (4 : ℝ) / 15 ≤ Gamma :=
  four_fifteenths_le_Gamma_of_bddAbove gammaScores_bddAbove

theorem Gamma_nonneg : 0 ≤ Gamma :=
  Gamma_nonneg_of_bddAbove gammaScores_bddAbove

end Erdos796
