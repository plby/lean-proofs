import ErdosProblems.Erdos157.MaskFailure

/-! Counting all simultaneous logarithm and tag-moment targets at one level. -/

namespace Erdos157.Elementary

open AuxiliaryModuli PolynomialCharacters

variable (K : Type*) [Field K] [DecidableEq K] [Fintype K] [CharP K 2]

noncomputable def maskTargetEquiv (k : ℕ) : MaskTarget K k ≃
    LogVector K k × (∀ i : Fin k, TagField i) × (∀ i : Fin k, TagField i) where
  toFun z := (z.logarithm, z.firstMoment, z.secondMoment)
  invFun z := ⟨z.1, z.2.1, z.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance maskTargetFintype (k : ℕ) : Fintype (MaskTarget K k) :=
  Fintype.ofEquiv _ (maskTargetEquiv K k).symm

theorem card_logVector_le (k : ℕ) : Fintype.card (LogVector K k) ≤ Fintype.card K ^ (k ^ 2) := by
  rw [← Nat.card_eq_fintype_card, ← Nat.card_congr (unitLogEquiv K k)]
  have hb := natCard_adjoinRoot_units_le (product K k) (product_monic K k)
  rwa [product_natDegree] at hb

theorem card_tagVector_le (k : ℕ) :
    Fintype.card (∀ i : Fin k, TagField i) ≤ 7 ^ (k * (k + 2)) := by
  classical
  rw [Fintype.card_pi]
  calc
    _ ≤ ∏ _i : Fin k, 7 ^ (k + 2) := Finset.prod_le_prod (fun _ _ => Nat.zero_le _) (fun i _ => by
      rw [card_tagField]
      exact Nat.pow_le_pow_right (by decide) (by omega))
    _ = _ := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul, mul_comm]

theorem card_maskTarget_le (k : ℕ) : Fintype.card (MaskTarget K k) ≤
    Fintype.card K ^ (k ^ 2) * 7 ^ (2 * k * (k + 2)) := by
  rw [Fintype.card_congr (maskTargetEquiv K k), Fintype.card_prod, Fintype.card_prod]
  calc
    _ ≤ Fintype.card K ^ (k ^ 2) *
        (7 ^ (k * (k + 2)) * 7 ^ (k * (k + 2))) :=
      Nat.mul_le_mul (card_logVector_le K k)
        (Nat.mul_le_mul (card_tagVector_le k) (card_tagVector_le k))
    _ = _ := by rw [← pow_add]; congr 2; ring

theorem card_maskTarget_le_exp (k : ℕ) (hk : 1 ≤ k) :
    (Fintype.card (MaskTarget K k) : ℝ) ≤
      Real.exp ((Real.log (Fintype.card K) + 6 * Real.log 7) * (k : ℝ) ^ 2) := by
  have hq : (0 : ℝ) < Fintype.card K := by exact_mod_cast Fintype.card_pos (α := K)
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have h7 : 0 ≤ Real.log 7 := Real.log_nonneg (by norm_num)
  have hb : (Fintype.card (MaskTarget K k) : ℝ) ≤
      (Fintype.card K : ℝ) ^ (k ^ 2) * (7 : ℝ) ^ (2 * k * (k + 2)) := by
    exact_mod_cast card_maskTarget_le K k
  calc
    _ ≤ _ := hb
    _ = Real.exp ((k : ℝ) ^ 2 * Real.log (Fintype.card K) +
        (2 * (k : ℝ) * (k + 2)) * Real.log 7) := by
      rw [Real.exp_add]
      congr 1
      · rw [show (k : ℝ) ^ 2 = ((k ^ 2 : ℕ) : ℝ) by push_cast; rfl,
          Real.exp_nat_mul, Real.exp_log hq]
      · rw [show 2 * (k : ℝ) * (k + 2) = ((2 * k * (k + 2) : ℕ) : ℝ) by push_cast; rfl,
          Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 7)]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hn : 2 * (k : ℝ) * (k + 2) ≤ 6 * (k : ℝ) ^ 2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right hn h7]

end Erdos157.Elementary
