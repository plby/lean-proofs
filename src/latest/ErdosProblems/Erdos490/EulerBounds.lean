import ErdosProblems.Erdos490.Dyadic
import ErdosProblems.Erdos490.PrimeProductBound

noncomputable section
namespace Erdos490
open Finset BigOperators
set_option maxHeartbeats 800000

lemma inverse_euler_eq (p : ℕ) (hp : p.Prime) :
    (1 - 1/(p : ℝ))⁻¹ = (p : ℝ)/(p-1) := by
  have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hp1 : (p : ℝ)-1 ≠ 0 := by exact sub_ne_zero.mpr (Nat.cast_ne_one.mpr hp.ne_one)
  field_simp

lemma inverse_euler_ge_one (p : ℕ) (hp : p.Prime) : 1 ≤ (1-1/(p : ℝ))⁻¹ := by
  rw [inverse_euler_eq p hp]
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  apply (le_div_iff₀ (by linarith)).mpr
  linarith

lemma E_val_le_full_product (lam : ℝ) (k r : ℕ) :
    E_val lam k r ≤ ∏ p ∈ I_layer lam k, (1-1/(p : ℝ))⁻¹ := by
  apply Finset.sup'_le
  intro T hT
  have hsub := Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1
  rw [← Finset.prod_sdiff hsub]
  apply le_mul_of_one_le_left
  · exact Finset.prod_nonneg fun p hp =>
      zero_le_one.trans (inverse_euler_ge_one p (Finset.mem_filter.mp (hsub hp)).2)
  · exact Finset.one_le_prod fun p hp =>
      inverse_euler_ge_one p (Finset.mem_filter.mp (Finset.mem_sdiff.mp hp).1).2

lemma log_E_val_le (lam : ℝ) (k r : ℕ) (hY : 1 < Y_val lam k) :
    Real.log (E_val lam k r) ≤ (r : ℝ)/(Y_val lam k-1) := by
  have hden : 0 < Y_val lam k-1 := by linarith
  have hterm (p : ℕ) (hp : p ∈ I_layer lam k) :
      Real.log ((1-1/(p : ℝ))⁻¹) ≤ 1/(Y_val lam k-1) := by
    have hpprime := (Finset.mem_filter.mp hp).2
    have hpY : Y_val lam k ≤ (p : ℝ) :=
      (Nat.le_ceil _).trans (Nat.cast_le.mpr (Finset.mem_Ico.mp (Finset.mem_filter.mp hp).1).1)
    have hpden : 0 < (p : ℝ)-1 := by linarith
    rw [inverse_euler_eq p hpprime]
    calc
      _ ≤ (p : ℝ)/(p-1)-1 := Real.log_le_sub_one_of_pos
        (div_pos (Nat.cast_pos.mpr hpprime.pos) hpden)
      _ = 1/((p : ℝ)-1) := by field_simp; ring
      _ ≤ _ := one_div_le_one_div_of_le hden (by linarith)
  have hE : E_val lam k r ≤ Real.exp ((r : ℝ)/(Y_val lam k-1)) := by
    apply Finset.sup'_le
    intro T hT
    have hsub := Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1
    have hcard := (Finset.mem_filter.mp hT).2
    have hpos (p : ℕ) (hp : p ∈ T) : 0 < (1-1/(p : ℝ))⁻¹ :=
      zero_lt_one.trans_le (inverse_euler_ge_one p (Finset.mem_filter.mp (hsub hp)).2)
    calc
      _ = Real.exp (∑ p ∈ T, Real.log ((1-1/(p : ℝ))⁻¹)) := by
        rw [Real.exp_sum]
        exact Finset.prod_congr rfl fun p hp => (Real.exp_log (hpos p hp)).symm
      _ ≤ Real.exp ((T.card : ℝ)/(Y_val lam k-1)) := by
        apply Real.exp_le_exp.mpr
        simpa [div_eq_mul_inv] using Finset.sum_le_sum (fun p hp => hterm p (hsub hp))
      _ ≤ _ := Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (Nat.cast_le.mpr hcard) hden.le)
  have := Real.log_le_log (zero_lt_one.trans_le (E_val_ge_one lam k r)) hE
  simpa only [Real.log_exp] using this

lemma layer_product_eq_interval (k : ℕ) :
    (∏ p ∈ I_layer 2 k, (1-1/(p : ℝ))⁻¹) =
      ∏ p ∈ Finset.Ico (dyadicScale k) (dyadicScale (k+1)), primeReciprocalFactor p := by
  rw [I_layer_two, dyadicScale_succ, Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro p hp
  simp only [primeReciprocalFactor]
  split_ifs with hpprime
  · exact inverse_euler_eq p hpprime
  · rfl

lemma layer_products_telescope (K : ℕ) :
    (∏ k ∈ Finset.range K, ∏ p ∈ I_layer 2 k, (1-1/(p : ℝ))⁻¹) =
      ∏ p ∈ Finset.Ico 2 (dyadicScale K), primeReciprocalFactor p := by
  induction K with
  | zero => simp [dyadicScale]
  | succ K ih =>
    rw [Finset.prod_range_succ, ih, layer_product_eq_interval]
    exact Finset.prod_Ico_consecutive _
      (by unfold dyadicScale; exact Nat.le_self_pow (by omega) 2)
      (by rw [dyadicScale_succ]; omega)

lemma primeReciprocalFactor_ge_one (p : ℕ) : 1 ≤ primeReciprocalFactor p := by
  unfold primeReciprocalFactor
  split_ifs with hp
  · rw [← inverse_euler_eq p hp]
    exact inverse_euler_ge_one p hp
  · rfl

lemma reciprocalPrefix_mono : Monotone reciprocalPrefix := by
  apply monotone_nat_of_le_succ
  intro n
  unfold reciprocalPrefix
  rw [Finset.prod_range_succ]
  exact le_mul_of_one_le_right (Finset.prod_nonneg (fun i hi => primeReciprocalFactor_nonneg _))
    (primeReciprocalFactor_ge_one _)

lemma finite_E_product_lt (m : ℕ → ℕ) :
    (∏ k ∈ Finset.range 16, E_val 2 k (m k)) < (211/10 : ℝ) := by
  have hle : (∏ k ∈ Finset.range 16, E_val 2 k (m k)) ≤
      ∏ k ∈ Finset.range 16, ∏ p ∈ I_layer 2 k, (1-1/(p : ℝ))⁻¹ :=
    Finset.prod_le_prod (fun k hk => zero_le_one.trans (E_val_ge_one _ _ _))
      (fun k hk => E_val_le_full_product _ _ _)
  rw [layer_products_telescope] at hle
  have heq : (∏ p ∈ Finset.Ico 2 (dyadicScale 16), primeReciprocalFactor p) =
      reciprocalPrefix 131070 := by
    rw [Finset.prod_Ico_eq_prod_range]
    norm_num only [dyadicScale, Nat.reduceAdd, Nat.reducePow, Nat.reduceSub]
    simp only [reciprocalPrefix, Nat.add_comm]
  rw [heq] at hle
  exact (hle.trans (reciprocalPrefix_mono (by norm_num : 131070 ≤ 131071))).trans_lt
    reciprocalPrefix_131071_lt

end Erdos490
