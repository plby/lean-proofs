import ErdosProblems.Erdos1166.Erdos1166HLOZUrn

namespace Erdos1166.HLOZUrn

open scoped BigOperators

/-- Integer formulation of `j` lying within distance `w` of the mean `i / 15`. -/
def InNegBinMeanBand (i w j : ℕ) : Prop :=
  15 * j ≤ i + 15 * w ∧ i ≤ 15 * j + 15 * w

/-- A uniform one-step comparison factor for the negative-binomial mass on a mean band. -/
noncomputable def negBinBandFactor (i w : ℕ) : ℝ :=
  1 + 32 * ((w : ℝ) + 1) / (i : ℝ)

lemma negBinBandFactor_nonneg (i w : ℕ) : 0 ≤ negBinBandFactor i w := by
  unfold negBinBandFactor
  positivity

/-- Forward adjacent masses on a mean band differ by at most `negBinBandFactor`. -/
lemma negBinMass_succ_le_bandFactor (i w j : ℕ) (hi : 1 ≤ i)
    (hsize : 30 * (w + 1) ≤ i) (hj : InNegBinMeanBand i w j) :
    negBinMass i (j + 1) ≤ negBinBandFactor i w * negBinMass i j := by
  rw [negBinMass_adjacent_ratio i j hi]
  apply mul_le_mul_of_nonneg_right _ (negBinMass_nonneg i j)
  have hiR : (0 : ℝ) < i := by exact_mod_cast (show 0 < i by omega)
  have hlowj : i ≤ 30 * (j + 1) := by
    unfold InNegBinMeanBand at hj
    omega
  have hdev : i ≤ 15 * j + 15 * w := hj.2
  unfold negBinBandFactor
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 16 * (j + 1))).2
  have hlowjR : (i : ℝ) ≤ 30 * (j + 1) := by exact_mod_cast hlowj
  have hdevR : (i : ℝ) ≤ 15 * j + 15 * w := by exact_mod_cast hdev
  field_simp
  nlinarith [mul_nonneg (show (0 : ℝ) ≤ i by positivity)
      (sub_nonneg.mpr hdevR),
    mul_nonneg (show (0 : ℝ) ≤ w + 1 by positivity)
      (sub_nonneg.mpr hlowjR)]

/-- Reverse adjacent masses on a mean band differ by at most `negBinBandFactor`. -/
lemma negBinMass_le_bandFactor_succ (i w j : ℕ) (hi : 1 ≤ i)
    (hj : InNegBinMeanBand i w j) :
    negBinMass i j ≤ negBinBandFactor i w * negBinMass i (j + 1) := by
  have hadj := negBinMass_adjacent i j hi
  have hiR : (0 : ℝ) < i := by exact_mod_cast (show 0 < i by omega)
  have hdev : 15 * j ≤ i + 15 * w := hj.1
  have hcoef : (16 : ℝ) * (j + 1) ≤
      (i + j : ℝ) * negBinBandFactor i w := by
    unfold negBinBandFactor
    have hdevR : (15 : ℝ) * j ≤ i + 15 * w := by exact_mod_cast hdev
    field_simp
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ i + j by positivity)
      (show (0 : ℝ) ≤ w + 1 by positivity)]
  apply le_of_mul_le_mul_left (a := (i + j : ℝ)) _ (by positivity)
  calc
    (i + j : ℝ) * negBinMass i j =
        16 * (j + 1) * negBinMass i (j + 1) := hadj.symm
    _ ≤ ((i + j : ℝ) * negBinBandFactor i w) * negBinMass i (j + 1) :=
      mul_le_mul_of_nonneg_right hcoef (negBinMass_nonneg i (j + 1))
    _ = (i + j : ℝ) *
        (negBinBandFactor i w * negBinMass i (j + 1)) := by ring

lemma inNegBinMeanBand_between {i w j₁ j₂ k : ℕ}
    (h₁ : InNegBinMeanBand i w j₁) (h₂ : InNegBinMeanBand i w j₂)
    (h₁k : j₁ ≤ k) (hk₂ : k ≤ j₂) : InNegBinMeanBand i w k := by
  unfold InNegBinMeanBand at h₁ h₂ ⊢
  omega

lemma negBinMass_forward_pow_aux (i w j : ℕ) (hi : 1 ≤ i)
    (hsize : 30 * (w + 1) ≤ i) : ∀ d : ℕ,
    (∀ k, j ≤ k → k ≤ j + d → InNegBinMeanBand i w k) →
    negBinMass i (j + d) ≤ negBinBandFactor i w ^ d * negBinMass i j := by
  intro d
  induction d with
  | zero => simp
  | succ d ih =>
      intro hband
      have hband' : ∀ k, j ≤ k → k ≤ j + d → InNegBinMeanBand i w k := by
        intro k hjk hkd
        exact hband k hjk (by omega)
      have hstep := negBinMass_succ_le_bandFactor i w (j + d) hi hsize
        (hband (j + d) (by omega) (by omega))
      calc
        negBinMass i (j + (d + 1)) = negBinMass i ((j + d) + 1) := by rfl
        _ ≤ negBinBandFactor i w * negBinMass i (j + d) := hstep
        _ ≤ negBinBandFactor i w *
            (negBinBandFactor i w ^ d * negBinMass i j) :=
          mul_le_mul_of_nonneg_left (ih hband') (negBinBandFactor_nonneg i w)
        _ = negBinBandFactor i w ^ (d + 1) * negBinMass i j := by
          rw [pow_succ]
          ring

lemma negBinMass_reverse_pow_aux (i w j : ℕ) (hi : 1 ≤ i) : ∀ d : ℕ,
    (∀ k, j ≤ k → k ≤ j + d → InNegBinMeanBand i w k) →
    negBinMass i j ≤ negBinBandFactor i w ^ d * negBinMass i (j + d) := by
  intro d
  induction d with
  | zero => simp
  | succ d ih =>
      intro hband
      have hband' : ∀ k, j ≤ k → k ≤ j + d → InNegBinMeanBand i w k := by
        intro k hjk hkd
        exact hband k hjk (by omega)
      have hstep := negBinMass_le_bandFactor_succ i w (j + d) hi
        (hband (j + d) (by omega) (by omega))
      calc
        negBinMass i j ≤ negBinBandFactor i w ^ d * negBinMass i (j + d) := ih hband'
        _ ≤ negBinBandFactor i w ^ d *
            (negBinBandFactor i w * negBinMass i ((j + d) + 1)) :=
          mul_le_mul_of_nonneg_left hstep (pow_nonneg (negBinBandFactor_nonneg i w) d)
        _ = negBinBandFactor i w ^ (d + 1) * negBinMass i (j + (d + 1)) := by
          rw [show j + (d + 1) = (j + d) + 1 by omega, pow_succ]
          ring

/-- Product-of-adjacent-ratios upper comparison for two ordered masses in a mean band. -/
theorem negBinMass_forward_pow (i w j₁ j₂ : ℕ) (hi : 1 ≤ i)
    (hsize : 30 * (w + 1) ≤ i) (h₁₂ : j₁ ≤ j₂)
    (h₁ : InNegBinMeanBand i w j₁) (h₂ : InNegBinMeanBand i w j₂) :
    negBinMass i j₂ ≤
      negBinBandFactor i w ^ (j₂ - j₁) * negBinMass i j₁ := by
  have hadd : j₁ + (j₂ - j₁) = j₂ := Nat.add_sub_of_le h₁₂
  have haux := negBinMass_forward_pow_aux i w j₁ hi hsize (j₂ - j₁) (by
    intro k h₁k hk₂
    exact inNegBinMeanBand_between h₁ h₂ h₁k (by omega))
  simpa only [hadd] using haux

/-- Product-of-adjacent-ratios lower comparison for two ordered masses in a mean band. -/
theorem negBinMass_reverse_pow (i w j₁ j₂ : ℕ) (hi : 1 ≤ i)
    (h₁₂ : j₁ ≤ j₂)
    (h₁ : InNegBinMeanBand i w j₁) (h₂ : InNegBinMeanBand i w j₂) :
    negBinMass i j₁ ≤
      negBinBandFactor i w ^ (j₂ - j₁) * negBinMass i j₂ := by
  have hadd : j₁ + (j₂ - j₁) = j₂ := Nat.add_sub_of_le h₁₂
  have haux := negBinMass_reverse_pow_aux i w j₁ hi (j₂ - j₁) (by
    intro k h₁k hk₂
    exact inNegBinMeanBand_between h₁ h₂ h₁k (by omega))
  simpa only [hadd] using haux

lemma negBinBandFactor_pow_le_exp_one (i w d : ℕ) (hi : 1 ≤ i)
    (hd : d ≤ 2 * w) (hscale : 64 * w * (w + 1) ≤ i) :
    negBinBandFactor i w ^ d ≤ Real.exp 1 := by
  let x : ℝ := 32 * ((w : ℝ) + 1) / (i : ℝ)
  have hiR : (0 : ℝ) < i := by exact_mod_cast (show 0 < i by omega)
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hfactor : negBinBandFactor i w ≤ Real.exp x := by
    dsimp [negBinBandFactor, x]
    simpa only [add_comm] using Real.add_one_le_exp (32 * ((w : ℝ) + 1) / (i : ℝ))
  have hnum : 32 * d * (w + 1) ≤ i := by
    calc
      32 * d * (w + 1) ≤ 32 * (2 * w) * (w + 1) := by
        exact Nat.mul_le_mul_right (w + 1) (Nat.mul_le_mul_left 32 hd)
      _ = 64 * w * (w + 1) := by ring
      _ ≤ i := hscale
  have hdx : (d : ℝ) * x ≤ 1 := by
    dsimp [x]
    have hnumR : (32 : ℝ) * d * (w + 1) ≤ i := by exact_mod_cast hnum
    rw [show (d : ℝ) * (32 * ((w : ℝ) + 1) / (i : ℝ)) =
        ((d : ℝ) * 32 * ((w : ℝ) + 1)) / (i : ℝ) by ring]
    apply (div_le_iff₀ hiR).2
    nlinarith
  calc
    negBinBandFactor i w ^ d ≤ (Real.exp x) ^ d :=
      pow_le_pow_left₀ (negBinBandFactor_nonneg i w) hfactor d
    _ = Real.exp ((d : ℝ) * x) := by rw [Real.exp_nat_mul]
    _ ≤ Real.exp 1 := Real.exp_le_exp.mpr hdx

/-- Fixed-constant mass comparability on a mean-centered band.

If both indices are within integer distance `w` of the mean `i / 15`, their distance is
at most `2w`, and `w^2` is small relative to `i`, then their masses differ by at most `e`.
-/
theorem negBinMass_compare_exp_one_of_le (i w j₁ j₂ : ℕ)
    (hi : 1 ≤ i) (hw : 1 ≤ w) (hscale : 64 * w * (w + 1) ≤ i)
    (h₁₂ : j₁ ≤ j₂) (hdist : j₂ - j₁ ≤ 2 * w)
    (h₁ : InNegBinMeanBand i w j₁) (h₂ : InNegBinMeanBand i w j₂) :
    negBinMass i j₂ ≤ Real.exp 1 * negBinMass i j₁ ∧
      negBinMass i j₁ ≤ Real.exp 1 * negBinMass i j₂ := by
  have hsize : 30 * (w + 1) ≤ i := by
    apply le_trans _ hscale
    nlinarith
  have hpow := negBinBandFactor_pow_le_exp_one i w (j₂ - j₁) hi hdist hscale
  constructor
  · exact (negBinMass_forward_pow i w j₁ j₂ hi hsize h₁₂ h₁ h₂).trans
      (mul_le_mul_of_nonneg_right hpow (negBinMass_nonneg i j₁))
  · exact (negBinMass_reverse_pow i w j₁ j₂ hi h₁₂ h₁ h₂).trans
      (mul_le_mul_of_nonneg_right hpow (negBinMass_nonneg i j₂))

end Erdos1166.HLOZUrn
