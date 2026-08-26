import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Finite Euclidean bookkeeping for list decoding

This module packages the Cauchy--Schwarz calculation used in the paper's
simplex proof of the short code list bound.  It is independent of the later
choice of alphabet and encoder.
-/

namespace Erdos788

open scoped BigOperators

/-- The ordinary dot product of two real vectors on a finite type. -/
noncomputable def finiteDot {κ : Type*} [Fintype κ]
    (u v : κ → ℝ) : ℝ :=
  ∑ k, u k * v k

theorem finiteDot_sum_left {κ ι : Type*} [Fintype κ]
    (L : Finset ι) (v : ι → κ → ℝ) (w : κ → ℝ) :
    finiteDot (fun k ↦ ∑ i ∈ L, v i k) w =
      ∑ i ∈ L, finiteDot (v i) w := by
  classical
  simp only [finiteDot, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem finiteDot_sum_norm_expand {κ ι : Type*} [Fintype κ]
    (L : Finset ι) (v : ι → κ → ℝ) :
    (∑ k, (∑ i ∈ L, v i k) ^ 2) =
      ∑ i ∈ L, ∑ j ∈ L, finiteDot (v i) (v j) := by
  classical
  simp only [pow_two, Finset.sum_mul, Finset.mul_sum, finiteDot]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _hj
  apply Finset.sum_congr rfl
  intro k _hk
  rw [mul_comm]

/-- Abstract simplex/Johnson calculation.  If all listed unit vectors have
pairwise inner product at most `β` and correlate with one unit received word
by more than `γ`, then the list has the standard rational size bound. -/
theorem card_lt_simplex_list_bound
    {κ ι : Type*} [Fintype κ] [DecidableEq ι]
    (L : Finset ι) (v : ι → κ → ℝ) (w : κ → ℝ)
    (β γ : ℝ)
    (hL : L.Nonempty)
    (hw : ∑ k, w k ^ 2 = 1)
    (hdiag : ∀ i ∈ L, finiteDot (v i) (v i) ≤ 1)
    (hoff : ∀ i ∈ L, ∀ j ∈ L, i ≠ j → finiteDot (v i) (v j) ≤ β)
    (hcorr : ∀ i ∈ L, γ < finiteDot (v i) w)
    (hγ : 0 ≤ γ) (hgap : β < γ ^ 2) :
    (L.card : ℝ) < (1 - β) / (γ ^ 2 - β) := by
  classical
  let S : κ → ℝ := fun k ↦ ∑ i ∈ L, v i k
  have hcardposNat : 0 < L.card := Finset.card_pos.mpr hL
  have hcardpos : (0 : ℝ) < L.card := by exact_mod_cast hcardposNat
  have hcorrSum : (L.card : ℝ) * γ < finiteDot S w := by
    rw [finiteDot_sum_left]
    obtain ⟨i₀, hi₀⟩ := hL
    have hsum : ∑ _i ∈ L, γ < ∑ i ∈ L, finiteDot (v i) w :=
      Finset.sum_lt_sum (fun i hi ↦ (hcorr i hi).le)
        ⟨i₀, hi₀, hcorr i₀ hi₀⟩
    simpa using! hsum
  have hleft_nonneg : 0 ≤ (L.card : ℝ) * γ :=
    mul_nonneg hcardpos.le hγ
  have hdotpos : 0 < finiteDot S w := hleft_nonneg.trans_lt hcorrSum
  have hsquareStrict : ((L.card : ℝ) * γ) ^ 2 < (finiteDot S w) ^ 2 := by
    nlinarith
  have hcauchy : (finiteDot S w) ^ 2 ≤
      (∑ k, S k ^ 2) * ∑ k, w k ^ 2 := by
    exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ S w
  rw [hw, mul_one] at hcauchy
  have hrow : ∀ i ∈ L,
      (∑ j ∈ L, finiteDot (v i) (v j)) ≤
        1 + (L.card - 1 : ℕ) * β := by
    intro i hi
    rw [← Finset.sum_erase_add _ _ hi]
    have hoffsum : ∑ j ∈ L.erase i, finiteDot (v i) (v j) ≤
        ∑ _j ∈ L.erase i, β := by
      exact Finset.sum_le_sum fun j hj ↦
        hoff i hi j (Finset.mem_of_mem_erase hj) (Finset.ne_of_mem_erase hj).symm
    calc
      (∑ j ∈ L.erase i, finiteDot (v i) (v j)) + finiteDot (v i) (v i)
          ≤ (∑ _j ∈ L.erase i, β) + 1 :=
        add_le_add hoffsum (hdiag i hi)
      _ = 1 + (L.card - 1 : ℕ) * β := by
        rw [Finset.sum_const, Finset.card_erase_of_mem hi]
        simp only [nsmul_eq_mul]
        ring
  have hnorm : ∑ k, S k ^ 2 ≤
      (L.card : ℝ) * (1 + (L.card - 1 : ℕ) * β) := by
    rw [finiteDot_sum_norm_expand]
    calc
      (∑ i ∈ L, ∑ j ∈ L, finiteDot (v i) (v j)) ≤
          ∑ _i ∈ L, (1 + (L.card - 1 : ℕ) * β) :=
        Finset.sum_le_sum hrow
      _ = (L.card : ℝ) * (1 + (L.card - 1 : ℕ) * β) := by
        rw [Finset.sum_const]
        simp only [nsmul_eq_mul]
  have hmaster : ((L.card : ℝ) * γ) ^ 2 <
      (L.card : ℝ) * (1 + (L.card - 1 : ℕ) * β) :=
    hsquareStrict.trans_le (hcauchy.trans hnorm)
  have hcastSub : ((L.card - 1 : ℕ) : ℝ) = (L.card : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  rw [hcastSub] at hmaster
  have hdenom : 0 < γ ^ 2 - β := sub_pos.mpr hgap
  apply (lt_div_iff₀ hdenom).2
  nlinarith

/-- Scale-invariant form of `card_lt_simplex_list_bound`.  This avoids
introducing square roots when the regular-simplex vectors all have the same
positive squared norm `q`. -/
theorem card_lt_simplex_list_bound_scaled
    {κ ι : Type*} [Fintype κ] [DecidableEq ι]
    (L : Finset ι) (v : ι → κ → ℝ) (w : κ → ℝ)
    (q β γ : ℝ)
    (hL : L.Nonempty) (hq : 0 < q)
    (hw : ∑ k, w k ^ 2 = q)
    (hdiag : ∀ i ∈ L, finiteDot (v i) (v i) ≤ q)
    (hoff : ∀ i ∈ L, ∀ j ∈ L, i ≠ j →
      finiteDot (v i) (v j) ≤ q * β)
    (hcorr : ∀ i ∈ L, q * γ < finiteDot (v i) w)
    (hγ : 0 ≤ γ) (hgap : β < γ ^ 2) :
    (L.card : ℝ) < (1 - β) / (γ ^ 2 - β) := by
  classical
  let S : κ → ℝ := fun k ↦ ∑ i ∈ L, v i k
  have hcardposNat : 0 < L.card := Finset.card_pos.mpr hL
  have hcardpos : (0 : ℝ) < L.card := by exact_mod_cast hcardposNat
  have hcorrSum : (L.card : ℝ) * (q * γ) < finiteDot S w := by
    rw [finiteDot_sum_left]
    obtain ⟨i₀, hi₀⟩ := hL
    have hsum : ∑ _i ∈ L, q * γ < ∑ i ∈ L, finiteDot (v i) w :=
      Finset.sum_lt_sum (fun i hi ↦ (hcorr i hi).le)
        ⟨i₀, hi₀, hcorr i₀ hi₀⟩
    simpa using! hsum
  have hleft_nonneg : 0 ≤ (L.card : ℝ) * (q * γ) :=
    mul_nonneg hcardpos.le (mul_nonneg hq.le hγ)
  have hdotpos : 0 < finiteDot S w := hleft_nonneg.trans_lt hcorrSum
  have hsquareStrict : ((L.card : ℝ) * (q * γ)) ^ 2 <
      (finiteDot S w) ^ 2 := by
    nlinarith
  have hcauchy : (finiteDot S w) ^ 2 ≤
      (∑ k, S k ^ 2) * ∑ k, w k ^ 2 := by
    exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ S w
  rw [hw] at hcauchy
  have hrow : ∀ i ∈ L,
      (∑ j ∈ L, finiteDot (v i) (v j)) ≤
        q * (1 + (L.card - 1 : ℕ) * β) := by
    intro i hi
    rw [← Finset.sum_erase_add _ _ hi]
    have hoffsum : ∑ j ∈ L.erase i, finiteDot (v i) (v j) ≤
        ∑ _j ∈ L.erase i, q * β := by
      exact Finset.sum_le_sum fun j hj ↦
        hoff i hi j (Finset.mem_of_mem_erase hj)
          (Finset.ne_of_mem_erase hj).symm
    calc
      (∑ j ∈ L.erase i, finiteDot (v i) (v j)) + finiteDot (v i) (v i)
          ≤ (∑ _j ∈ L.erase i, q * β) + q :=
        add_le_add hoffsum (hdiag i hi)
      _ = q * (1 + (L.card - 1 : ℕ) * β) := by
        rw [Finset.sum_const, Finset.card_erase_of_mem hi]
        simp only [nsmul_eq_mul]
        ring
  have hnorm : ∑ k, S k ^ 2 ≤
      (L.card : ℝ) * (q * (1 + (L.card - 1 : ℕ) * β)) := by
    rw [finiteDot_sum_norm_expand]
    calc
      (∑ i ∈ L, ∑ j ∈ L, finiteDot (v i) (v j)) ≤
          ∑ _i ∈ L, q * (1 + (L.card - 1 : ℕ) * β) :=
        Finset.sum_le_sum hrow
      _ = (L.card : ℝ) *
          (q * (1 + (L.card - 1 : ℕ) * β)) := by
        rw [Finset.sum_const]
        simp only [nsmul_eq_mul]
  have hmaster : ((L.card : ℝ) * (q * γ)) ^ 2 <
      ((L.card : ℝ) * (q * (1 + (L.card - 1 : ℕ) * β))) * q :=
    hsquareStrict.trans_le (hcauchy.trans (mul_le_mul_of_nonneg_right hnorm hq.le))
  have hmasterNormalized : ((L.card : ℝ) * γ) ^ 2 <
      (L.card : ℝ) * (1 + (L.card - 1 : ℕ) * β) := by
    apply (mul_lt_mul_iff_right₀ (sq_pos_of_pos hq)).mp
    calc
      q ^ 2 * ((L.card : ℝ) * γ) ^ 2 =
          ((L.card : ℝ) * (q * γ)) ^ 2 := by ring
      _ < ((L.card : ℝ) *
          (q * (1 + (L.card - 1 : ℕ) * β))) * q := hmaster
      _ = q ^ 2 *
          ((L.card : ℝ) * (1 + (L.card - 1 : ℕ) * β)) := by ring
  have hcastSub : ((L.card - 1 : ℕ) : ℝ) = (L.card : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  rw [hcastSub] at hmasterNormalized
  have hdenom : 0 < γ ^ 2 - β := sub_pos.mpr hgap
  apply (lt_div_iff₀ hdenom).2
  nlinarith

end Erdos788
