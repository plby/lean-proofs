import ErdosProblems.Erdos490.Basic
import Util.MertensThird

noncomputable section

namespace Erdos490

open Finset BigOperators Nat Real

def dyadicScale (k : ℕ) : ℕ := 2 ^ (k + 1)

lemma Y_val_two (k : ℕ) : Y_val 2 k = (dyadicScale k : ℝ) := by
  simp [Y_val, dyadicScale, pow_succ, mul_comm]

lemma dyadicScale_pos (k : ℕ) : 0 < dyadicScale k := by
  unfold dyadicScale
  positivity

lemma dyadicScale_succ (k : ℕ) : dyadicScale (k + 1) = 2 * dyadicScale k := by
  simp [dyadicScale, pow_succ, mul_comm]

lemma I_layer_two (k : ℕ) : I_layer 2 k =
    (Finset.Ico (dyadicScale k) (2 * dyadicScale k)).filter Nat.Prime := by
  simp only [I_layer, Y_val_two, Nat.ceil_natCast, dyadicScale_succ]

lemma M_layer_positive (lam : ℝ) (k : ℕ) : 0 < M_layer lam k := by
  apply Finset.prod_pos
  intro p hp
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  exact sub_pos.mpr ((div_lt_one hp0).mpr hp1)

lemma dyadic_prime_count (k : ℕ) (hk : 1 ≤ k) :
    (N_layer 2 k : ℝ) ≤
      2 * dyadicScale k * Real.log 2 / Real.log (dyadicScale k) := by
  let Y := dyadicScale k
  have hY : 2 ≤ Y := by
    dsimp [Y, dyadicScale]
    exact Nat.le_self_pow (by omega) 2
  have hYnot : ¬ Y.Prime := Nat.Prime.not_prime_pow (by omega : 2 ≤ k + 1)
  have hprime (p : ℕ) (hp : p ∈ I_layer 2 k) : p.Prime := (Finset.mem_filter.mp hp).2
  have hbounds (p : ℕ) (hp : p ∈ I_layer 2 k) : Y < p ∧ p < 2 * Y := by
    rw [I_layer_two] at hp
    have h := (Finset.mem_Ico.mp (Finset.mem_filter.mp hp).1)
    exact ⟨lt_of_le_of_ne h.1 (by intro he; exact hYnot (he ▸ (Finset.mem_filter.mp hp).2)), h.2⟩
  have hdvd : (∏ p ∈ I_layer 2 k, p) ∣ Nat.choose (2 * Y) Y := by
    apply Finset.prod_primes_dvd
    · intro p hp
      exact (hprime p hp).prime
    · intro p hp
      have hb := hbounds p hp
      exact (hprime p hp).dvd_choose hb.1 (by omega) hb.2.le
  have hchoose : 0 < Nat.choose (2 * Y) Y := Nat.choose_pos (by omega)
  have hprod : (∏ p ∈ I_layer 2 k, (p : ℝ)) ≤ (4 : ℝ)^Y := by
    have hle := (Nat.le_of_dvd hchoose hdvd).trans (Nat.centralBinom_le_four_pow Y)
    have hcast := Nat.cast_le (α := ℝ).mpr hle
    simpa only [Nat.cast_prod, Nat.cast_pow, Nat.cast_ofNat] using hcast
  have hprodpos : 0 < ∏ p ∈ I_layer 2 k, (p : ℝ) := by
    exact Finset.prod_pos fun p hp => Nat.cast_pos.mpr (hprime p hp).pos
  have hsum : (N_layer 2 k : ℝ) * Real.log Y ≤ Real.log (∏ p ∈ I_layer 2 k, (p : ℝ)) := by
    rw [Real.log_prod (fun p hp => (Nat.cast_pos.mpr (hprime p hp).pos).ne')]
    calc
      _ = ∑ p ∈ I_layer 2 k, Real.log (Y : ℝ) := by simp [N_layer]
      _ ≤ _ := Finset.sum_le_sum fun p hp => Real.log_le_log
        (by exact_mod_cast (show 0 < Y by omega)) (by exact_mod_cast (hbounds p hp).1.le)
  have hlog := Real.log_le_log hprodpos hprod
  rw [Real.log_pow, Real.log_four_eq] at hlog
  apply (le_div_iff₀ (Real.log_pos (by exact_mod_cast (show 1 < Y by omega)))).mpr
  dsimp [Y] at hsum hlog ⊢
  nlinarith

lemma dyadic_mertens_lower (k : ℕ) :
    1 / (3 * Real.log (2 * (dyadicScale k : ℝ))) ≤ M_layer 2 k := by
  have hY : 3 ≤ 2 * dyadicScale k := by
    have := dyadicScale_pos k
    have h2 : 2 ≤ dyadicScale k := by
      unfold dyadicScale
      exact Nat.le_self_pow (by omega) 2
    omega
  have h := mertens_third_theorem (2 * dyadicScale k) hY
  have hf : ⌊(2 : ℝ) * (dyadicScale k : ℝ)⌋₊ = 2 * dyadicScale k := by
    norm_cast
    exact Nat.floor_natCast _
  simpa only [M_layer, primesUpTo, Y_val_two, dyadicScale_succ,
    Nat.cast_mul, Nat.cast_ofNat, hf] using h

lemma dyadicScale_log (k : ℕ) : Real.log (dyadicScale k : ℝ) = ((k : ℝ)+1)*Real.log 2 := by
  simp [dyadicScale, Real.log_pow]

lemma dyadic_density_bound (k : ℕ) (hk : 16 ≤ k) :
    (N_layer 2 k : ℝ) / (Y_val 2 k * Real.sqrt (M_layer 2 k)) ≤ (72/100 : ℝ) := by
  have hY : 0 < Y_val 2 k := by rw [Y_val_two]; exact_mod_cast dyadicScale_pos k
  have hM : 0 < M_layer 2 k := M_layer_positive _ _
  have hs : 0 < Real.sqrt (M_layer 2 k) := Real.sqrt_pos.mpr hM
  have hK : (16 : ℝ) ≤ k := by exact_mod_cast hk
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hn := dyadic_prime_count k (by omega)
  rw [dyadicScale_log, ← Y_val_two] at hn
  have hn' : (N_layer 2 k : ℝ) ≤ 2 * Y_val 2 k / ((k : ℝ)+1) := by
    convert hn using 1
    field_simp
  have hm := dyadic_mertens_lower k
  rw [Real.log_mul (by norm_num) (Nat.cast_pos.mpr (dyadicScale_pos k)).ne',
    dyadicScale_log] at hm
  have hm' : 1 ≤ 3 * ((k : ℝ)+2) * Real.log 2 * M_layer 2 k := by
    have heq : 3 * (Real.log 2 + ((k : ℝ)+1)*Real.log 2) =
        3 * ((k : ℝ)+2) * Real.log 2 := by ring
    rw [heq, div_le_iff₀ (by positivity)] at hm
    nlinarith
  have hcoef : 3 * ((k : ℝ)+2) * Real.log 2 ≤ (72/100 : ℝ)^2/4 * ((k : ℝ)+1)^2 := by
    have hl : Real.log 2 < (6932/10000 : ℝ) := by linarith [Real.log_two_lt_d9]
    have hquad : 289 * ((k : ℝ)+2) ≤ 18 * ((k : ℝ)+1)^2 := by
      nlinarith [sq_nonneg ((k : ℝ)-16)]
    nlinarith [mul_le_mul_of_nonneg_left hl.le (show 0 ≤ 3*((k : ℝ)+2) by positivity)]
  have hsquare : 4 ≤ (72/100 : ℝ)^2 * ((k : ℝ)+1)^2 * M_layer 2 k := by
    have := mul_le_mul_of_nonneg_right hcoef hM.le
    nlinarith
  have hroot : 2 ≤ (72/100 : ℝ) * ((k : ℝ)+1) * Real.sqrt (M_layer 2 k) := by
    apply (sq_le_sq₀ (by norm_num) (by positivity)).mp
    rw [mul_pow, mul_pow, Real.sq_sqrt hM.le]
    norm_num at hsquare ⊢
    exact hsquare
  apply (div_le_iff₀ (mul_pos hY hs)).mpr
  refine hn'.trans ?_
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < k+1)).mpr
  nlinarith [mul_le_mul_of_nonneg_left hroot hY.le]

end Erdos490
