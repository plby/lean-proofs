import ErdosProblems.Erdos380.AntiSieve
import Mathlib.Data.Nat.Choose.Bounds

/-!
# A uniform version of the finite residue sieve

For comparable prime moduli there is no need to select and remove the
largest weights. A binomial coefficient lower bound counts subsets of
moduli, each of which contributes at least the same weight.
-/

open scoped BigOperators Function

namespace Erdos380

lemma choose_ge_half_ratio_pow {M k : ℕ} (hk : 0 < k) (hMk : 2 * k ≤ M) :
    ((M : ℝ) / (2 * k)) ^ k ≤ (M.choose k : ℝ) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hcast : (M : ℝ) / 2 ≤ ((M + 1 - k : ℕ) : ℝ) := by
    have h : M ≤ 2 * (M + 1 - k) := by omega
    exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr (by
      exact_mod_cast (show M ≤ (M + 1 - k) * 2 by simpa only [mul_comm] using h))
  have hfac : (k.factorial : ℝ) ≤ (k : ℝ) ^ k := by exact_mod_cast Nat.factorial_le_pow k
  calc
    ((M : ℝ) / (2 * k)) ^ k ≤ (((M + 1 - k : ℕ) : ℝ) / k) ^ k := by
      apply pow_le_pow_left₀ (by positivity)
      rw [← div_div]
      exact div_le_div_of_nonneg_right hcast hkR.le
    _ = (((M + 1 - k : ℕ) : ℝ) ^ k) / (k : ℝ) ^ k := div_pow _ _ _
    _ ≤ (((M + 1 - k : ℕ) : ℝ) ^ k) / k.factorial :=
      div_le_div_of_nonneg_left (by positivity) (by exact_mod_cast Nat.factorial_pos k) hfac
    _ ≤ _ := Nat.pow_le_choose k M

lemma fixedCardSubsets_weight_sum_ge
    {I : Type*} [Fintype I] [DecidableEq I] (k : ℕ) (w : I → ℝ)
    {a : ℝ} (ha : 0 ≤ a) (hw : ∀ i, a ≤ w i) :
    ((Fintype.card I).choose k : ℝ) * a ^ k ≤
      ∑ T : fixedCardSubsets I k, ∏ i ∈ T.1, w i := by
  classical
  have hsum : (∑ T : fixedCardSubsets I k, ∏ i ∈ T.1, w i) =
      ∑ T ∈ (Finset.univ : Finset I).powersetCard k, ∏ i ∈ T, w i := by
    symm
    exact Finset.sum_subtype (p := fun T : Finset I => T.card = k)
      ((Finset.univ : Finset I).powersetCard k) (fun T => by simp) (fun T => ∏ i ∈ T, w i)
  rw [hsum]
  calc
    ((Fintype.card I).choose k : ℝ) * a ^ k =
        ∑ _T ∈ (Finset.univ : Finset I).powersetCard k, a ^ k := by simp
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro T hT
      have hcard : T.card = k := (Finset.mem_powersetCard.mp hT).2
      calc
        a ^ k = ∏ _i ∈ T, a := by rw [Finset.prod_const, hcard]
        _ ≤ ∏ i ∈ T, w i := Finset.prod_le_prod (fun _ _ => ha) (fun i _ => hw i)

theorem residueClassSurvivors_card_le_uniform
    {I : Type*} [Fintype I] [DecidableEq I]
    (modulus : I → ℕ) [∀ i, NeZero (modulus i)]
    (hcoprime : Pairwise (Nat.Coprime on modulus))
    (vanishing : ∀ i, Finset (ZMod (modulus i)))
    {k H Q : ℕ} (hk : 0 < k) (hH : 0 < H) (hQ : 0 < Q)
    (hcard : 2 * k ≤ Fintype.card I)
    (hmod : ∀ i, modulus i ≤ Q)
    (hvanish : ∀ i, (vanishing i).card = H)
    (hproper : ∀ i, H < modulus i)
    (m₀ N : ℕ) (hpower : Q ^ (2 * k) ≤ N) :
    ((residueClassSurvivors vanishing m₀ N).card : ℝ) ≤
      ((N : ℝ) + N) / (((Fintype.card I : ℝ) * H / (2 * k * Q)) ^ k) := by
  classical
  have hI : 0 < Fintype.card I := by omega
  have hsubsets : Nonempty (fixedCardSubsets I k) := by
    obtain ⟨T, hT⟩ := Finset.powersetCard_nonempty.mpr
      (show k ≤ (Finset.univ : Finset I).card by simpa using (show k ≤ Fintype.card I by omega))
    exact ⟨⟨T, (Finset.mem_powersetCard.mp hT).2⟩⟩
  have hprod (T : fixedCardSubsets I k) : (∏ i ∈ T.1, modulus i) ≤ Q ^ k := by
    calc
      (∏ i ∈ T.1, modulus i) ≤ ∏ _i ∈ T.1, Q := Finset.prod_le_prod' fun i _ => hmod i
      _ = Q ^ k := by rw [Finset.prod_const, T.2]
  have hproducts (T U : fixedCardSubsets I k) :
      (∏ i ∈ T.1, modulus i) * (∏ i ∈ U.1, modulus i) ≤ N := by
    exact (Nat.mul_le_mul (hprod T) (hprod U)).trans
      (by simpa only [← pow_add, two_mul] using hpower)
  have hsieve := residueClassSurvivors_card_le_powerset_ratio modulus hcoprime vanishing
    k m₀ N hsubsets hproducts
    (fun i => Finset.card_pos.mp (by rw [hvanish i]; exact hH))
    (fun i => by rw [hvanish i]; exact hproper i)
  have hratio (i : I) : (H : ℝ) / Q ≤ residueRemovalRatio modulus vanishing i := by
    unfold residueRemovalRatio
    rw [hvanish i]
    apply div_le_div_of_nonneg_left (Nat.cast_nonneg H)
    · exact_mod_cast Nat.sub_pos_of_lt (hproper i)
    · exact_mod_cast (Nat.sub_le (modulus i) H).trans (hmod i)
  have hdenom : (((Fintype.card I : ℝ) * H / (2 * k * Q)) ^ k) ≤
      ∑ T : fixedCardSubsets I k, ∏ i ∈ T.1, residueRemovalRatio modulus vanishing i := by
    calc
      (((Fintype.card I : ℝ) * H / (2 * k * Q)) ^ k) =
          ((Fintype.card I : ℝ) / (2 * k)) ^ k * ((H : ℝ) / Q) ^ k := by
        rw [← mul_pow]
        congr 1
        ring
      _ ≤ ((Fintype.card I).choose k : ℝ) * ((H : ℝ) / Q) ^ k :=
        mul_le_mul_of_nonneg_right (choose_ge_half_ratio_pow hk hcard) (by positivity)
      _ ≤ _ := fixedCardSubsets_weight_sum_ge k _ (by positivity) hratio
  exact hsieve.trans (div_le_div_of_nonneg_left (by positivity) (by positivity) hdenom)

end Erdos380
