/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Licensed under the Apache License, Version 2.0; see LICENSE.
Modified for this repository and Lean/Mathlib 4.33.0. -/
/-
Erdős Problem 884.
Informal proof: Daniel Larsen, building on Terence Tao's construction.
Formal proof: Claude Fable 5, with minor guidance from R. J. Honicky.
Source: https://www.erdosproblems.com/884#post-7362
https://github.com/honicky/erdos884/tree/323e9a01306df1e094b434beaa48c018370fe258
Original Lean/Mathlib version: 4.31.0.
Original Mathlib commit: fabf563a7c95a166b8d7b6efca11c8b4dc9d911f.
The port reuses the repository's existing PNT+ Selberg sieve by Arend Mellendijk.
-/
import ErdosProblems.Erdos884.ScaleStep

open Finset

set_option linter.mathlibStandardSet false

/-!
# Erdős Problem 884 — the multiscale construction

We iterate the single-scale construction (`OneScale884`) via the incremental step
(`ScaleStep884`), with scales produced by `Selection884`, to build integers `n` whose
pair sum `pairSum n.divisors` exceeds `C * (1 + gapSum n.divisors)` for any fixed `C`.

Export: `exists_ratio_large`.
-/

namespace Erdos884

/-! ### Elementary real-analysis helpers -/

/-- `(x/k)^k ≤ exp x` for `x ≥ 0`. -/
lemma ms_div_pow_le_exp (k : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    (x / k) ^ k ≤ Real.exp x := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    simpa using Real.one_le_exp hx
  · have hk0 : (k : ℝ) ≠ 0 := by positivity
    have h1 : x / k ≤ Real.exp (x / k) := by
      have := Real.add_one_le_exp (x / k)
      linarith
    have h2 : (x / k) ^ k ≤ (Real.exp (x / k)) ^ k :=
      pow_le_pow_left₀ (by positivity) h1 k
    calc (x / k) ^ k ≤ (Real.exp (x / k)) ^ k := h2
      _ = Real.exp ((k : ℝ) * (x / k)) := (Real.exp_nat_mul _ _).symm
      _ = Real.exp x := by rw [mul_div_cancel₀ _ hk0]

/-- `log y ≤ y/a + a` for `1 ≤ a`, `0 < y`. -/
lemma ms_log_le_div_add {a y : ℝ} (ha : 1 ≤ a) (hy : 0 < y) :
    Real.log y ≤ y / a + a := by
  have ha0 : (0:ℝ) < a := by linarith
  have h1 : Real.log y = Real.log (y / a) + Real.log a := by
    rw [← Real.log_mul (by positivity) (by positivity), div_mul_cancel₀ _ ha0.ne']
  have h2 : Real.log (y / a) ≤ y / a - 1 := Real.log_le_sub_one_of_pos (by positivity)
  have h3 : Real.log a ≤ a - 1 := Real.log_le_sub_one_of_pos ha0
  linarith

/-! ### pairSum monotonicity and superadditivity consequences -/

/-- Monotonicity of `pairSum` under set inclusion. -/
lemma ms_pairSum_mono {B A : Finset ℕ} (h : B ⊆ A) : pairSum B ≤ pairSum A := by
  have := sum_pairSum_le_pairSum (ι := ℕ) (I := {0}) (B := fun _ => B) (A := A)
    (fun _ _ => h) (fun i hi j hj hij => by
      simp only [Finset.mem_singleton] at hi hj; omega)
  simpa using this

/-- Any member of `B` bounds the product of `B` from below. -/
lemma ms_le_prodB {B : Finset ℕ} (hB : ∀ p ∈ B, p.Prime) {p : ℕ} (hp : p ∈ B) :
    p ≤ ∏ q ∈ B, q :=
  Finset.single_le_prod' (fun q hq => (hB q hq).one_lt.le.trans' (by norm_num)) hp

/-- Superadditivity across a new scale: if all primes of `B` exceed `n`, then
`pairSum n.divisors + pairSum B ≤ pairSum ((n * ∏ B).divisors)`. -/
lemma ms_pairSum_add_le {n : ℕ} (hn : n ≠ 0) {B : Finset ℕ}
    (hB : ∀ p ∈ B, p.Prime) (hgt : ∀ p ∈ B, n < p) :
    pairSum n.divisors + pairSum B ≤ pairSum ((n * ∏ p ∈ B, p).divisors) := by
  classical
  have hm : (∏ p ∈ B, p) ≠ 0 := os_prodB_ne_zero hB
  have hnm : n * (∏ p ∈ B, p) ≠ 0 := mul_ne_zero hn hm
  have hsub1 : n.divisors ⊆ (n * ∏ p ∈ B, p).divisors := by
    intro d hd
    rw [Nat.mem_divisors] at hd ⊢
    exact ⟨hd.1.mul_right _, hnm⟩
  have hsub2 : B ⊆ (n * ∏ p ∈ B, p).divisors := by
    intro p hp
    rw [Nat.mem_divisors]
    exact ⟨(Finset.dvd_prod_of_mem _ hp).mul_left n, hnm⟩
  have hdisj : Disjoint n.divisors B := by
    rw [Finset.disjoint_left]
    intro d hd hdB
    have h1 : d ≤ n := Nat.divisor_le hd
    have h2 := hgt d hdB
    omega
  have := sum_pairSum_le_pairSum (ι := ℕ) (I := {0, 1})
    (B := fun i => if i = 0 then n.divisors else B) (A := (n * ∏ p ∈ B, p).divisors)
    (fun i _ => by split <;> [exact hsub1; exact hsub2])
    (fun i hi j hj hij => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj
      rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
      · exact absurd rfl hij
      · simpa using hdisj
      · simpa using hdisj.symm
      · exact absurd rfl hij)
  simpa using this

/-! ### Quotient monotonicity workhorse -/

lemma ms_div_le_div {a b c d : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hd : 0 < d) (hdc : d ≤ c) :
    a / c ≤ b / d := by
  have hc : 0 < c := lt_of_lt_of_le hd hdc
  rw [div_le_div_iff₀ hc hd]
  nlinarith

/-! ### Parameter estimates for one scale -/

/-- The window-size condition `8·(2H)^(K+1) ≤ exp L` from `K ≤ L/(12Λ)`, `H ≤ 7KL`. -/
lemma ms_hbig_aux {Λ L : ℝ} {K H : ℕ} (hΛ : 30 ≤ Λ) (hL : Real.exp Λ = L)
    (hH1 : 1 ≤ (H:ℝ)) (hK1 : 1 ≤ (K:ℝ)) (hK12 : (K:ℝ)*(12*Λ) ≤ L)
    (hHb : (H:ℝ) ≤ 7*K*L) :
    (8:ℝ)*(2*H)^(K+1) ≤ Real.exp L := by
  have hΛ0 : (0:ℝ) < Λ := by linarith
  have hL1 : Λ + 1 ≤ L := by rw [← hL]; exact Real.add_one_le_exp Λ
  have hL31 : 31 ≤ L := by linarith
  have hL0 : (0:ℝ) < L := by linarith
  have hK0 : (0:ℝ) < K := by linarith
  have h2H0 : (0:ℝ) < 2*(H:ℝ) := by linarith
  have hlogL : Real.log L = Λ := by rw [← hL, Real.log_exp]
  have hlogK : Real.log (K:ℝ) ≤ Λ := by
    have hKL : (K:ℝ) ≤ L := by nlinarith
    have h1 : Real.log (K:ℝ) ≤ Real.log L := Real.log_le_log hK0 hKL
    rwa [hlogL] at h1
  have hlog2H : Real.log (2*(H:ℝ)) ≤ 3*Λ := by
    have h14 : 2*(H:ℝ) ≤ 14*((K:ℝ)*L) := by nlinarith
    have h1 : Real.log (2*(H:ℝ)) ≤ Real.log (14*((K:ℝ)*L)) := Real.log_le_log h2H0 h14
    have h2 : Real.log (14*((K:ℝ)*L)) = Real.log 14 + (Real.log K + Real.log L) := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_mul (by positivity) (by positivity)]
    have h3 : Real.log (14:ℝ) ≤ 13 := by
      have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 14 by norm_num); linarith
    rw [h2, hlogL] at h1
    linarith
  have hpow0 : (0:ℝ) < (2*(H:ℝ))^(K+1) := by positivity
  have hmain : Real.log ((8:ℝ)*(2*H)^(K+1)) ≤ L := by
    have h1 : Real.log ((8:ℝ)*(2*(H:ℝ))^(K+1)) = Real.log 8 + ((K:ℝ)+1)*Real.log (2*(H:ℝ)) := by
      rw [Real.log_mul (by norm_num) hpow0.ne', Real.log_pow]
      push_cast; ring
    have hlog8 : Real.log (8:ℝ) ≤ 7 := by
      have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 8 by norm_num); linarith
    have hlog2H0 : 0 ≤ Real.log (2*(H:ℝ)) := Real.log_nonneg (by linarith)
    have h2 : ((K:ℝ)+1)*Real.log (2*(H:ℝ)) ≤ (2*(K:ℝ))*(3*Λ) :=
      mul_le_mul (by linarith) hlog2H (by linarith) (by linarith)
    have h3 : (2*(K:ℝ))*(3*Λ) ≤ L/2 := by nlinarith
    rw [h1]
    linarith
  calc (8:ℝ)*(2*H)^(K+1)
      = Real.exp (Real.log ((8:ℝ)*(2*(H:ℝ))^(K+1))) := (Real.exp_log (by positivity)).symm
    _ ≤ Real.exp L := Real.exp_le_exp.mpr hmain

/-- The `2KH ≤ γ·exp L` estimate. -/
lemma ms_KH_aux {Λ L γ : ℝ} {K H : ℕ} (hγ : 0 < γ) (hΛγ : 3584/γ ≤ Λ)
    (hΛ : 30 ≤ Λ) (hL : Real.exp Λ = L) (hKL : (K:ℝ) ≤ L)
    (hHb : (H:ℝ) ≤ 7*K*L) :
    2*(K:ℝ)*H ≤ γ * Real.exp L := by
  have hK0 : (0:ℝ) ≤ (K:ℝ) := Nat.cast_nonneg K
  have hΛ0 : (0:ℝ) < Λ := by linarith
  have hL1 : Λ + 1 ≤ L := by rw [← hL]; exact Real.add_one_le_exp Λ
  have hL0 : (0:ℝ) < L := by linarith
  have h1 : 2*(K:ℝ)*H ≤ 14*L^3 := by
    nlinarith [mul_le_mul_of_nonneg_left hHb (show (0:ℝ) ≤ 2*(K:ℝ) by positivity),
      mul_le_mul_of_nonneg_right (mul_self_le_mul_self hK0 hKL) hL0.le]
  have hγΛ : 3584 ≤ γ*Λ := by
    have h := mul_le_mul_of_nonneg_left hΛγ hγ.le
    have heq : γ*(3584/γ) = 3584 := by field_simp
    linarith
  have hγL : 3584 ≤ γ*L := by nlinarith
  have hp4 : L^4/256 ≤ Real.exp L := by
    calc L^4/256 = (L/4)^4 := by ring
      _ ≤ Real.exp L := ms_div_pow_le_exp 4 hL0.le
  have h4 : 14*L^3 ≤ γ*(L^4/256) := by
    nlinarith [mul_le_mul_of_nonneg_right hγL (show (0:ℝ) ≤ L^3 by positivity)]
  have h3 : γ*(L^4/256) ≤ γ*Real.exp L := mul_le_mul_of_nonneg_left hp4 hγ.le
  linarith

/-- The exponential-junk error terms are at most `η` once `Λ ≥ 6(E+20)/η`. -/
lemma ms_err_aux {Λ L E η : ℝ} {K x₀ : ℕ} (hE : 0 ≤ E) (hη : 0 < η)
    (hΛ : 30 ≤ Λ) (hΛE : 6*(E+20)/η ≤ Λ) (hL : Real.exp Λ = L)
    (hK6 : 2*(K:ℝ) ≤ L/6) (hKL : (K:ℝ) ≤ L) (hx₀ : Real.exp L ≤ (x₀:ℝ)) :
    E*(K:ℝ)/x₀ + 2*(2*(4:ℝ)^K/x₀ + (2:ℝ)^(K+3)*K/x₀) ≤ η := by
  have hΛ0 : (0:ℝ) < Λ := by linarith
  have hL1 : Λ + 1 ≤ L := by rw [← hL]; exact Real.add_one_le_exp Λ
  have hL0 : (0:ℝ) < L := by linarith
  have ht0 : (0:ℝ) < Real.exp L := Real.exp_pos L
  have hx0 : (0:ℝ) < (x₀:ℝ) := lt_of_lt_of_le ht0 hx₀
  have hK0 : (0:ℝ) ≤ (K:ℝ) := Nat.cast_nonneg K
  have hexp2 : (4:ℝ) ≤ Real.exp 2 := by
    have h1 : (2:ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1:ℝ); linarith
    have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]; norm_num
    nlinarith
  have h4K : (4:ℝ)^K ≤ Real.exp (2*(K:ℝ)) := by
    calc (4:ℝ)^K ≤ (Real.exp 2)^K := pow_le_pow_left₀ (by norm_num) hexp2 K
      _ = Real.exp ((K:ℕ)*(2:ℝ)) := (Real.exp_nat_mul 2 K).symm
      _ = Real.exp (2*(K:ℝ)) := by rw [mul_comm]
  have h2K : (2:ℝ)^K ≤ Real.exp (2*(K:ℝ)) := by
    calc (2:ℝ)^K ≤ (4:ℝ)^K := pow_le_pow_left₀ (by norm_num) (by norm_num) K
      _ ≤ Real.exp (2*(K:ℝ)) := h4K
  have he2K1 : (1:ℝ) ≤ Real.exp (2*(K:ℝ)) := Real.one_le_exp (by positivity)
  have hL1' : (1:ℝ) ≤ L := by linarith
  -- numerator bound
  have hU : E*(K:ℝ) + 4*(4:ℝ)^K + 2*((2:ℝ)^(K+3)*K)
      ≤ (E+20)*L*Real.exp (2*(K:ℝ)) := by
    have hEK : E*(K:ℝ) ≤ E*L*Real.exp (2*(K:ℝ)) := by
      have ha : E*(K:ℝ) ≤ E*L := mul_le_mul_of_nonneg_left hKL hE
      have hb : E*L*1 ≤ E*L*Real.exp (2*(K:ℝ)) :=
        mul_le_mul_of_nonneg_left he2K1 (mul_nonneg hE (by linarith))
      linarith
    have h44 : 4*(4:ℝ)^K ≤ 4*L*Real.exp (2*(K:ℝ)) := by
      have hc : (1:ℝ)*Real.exp (2*(K:ℝ)) ≤ L*Real.exp (2*(K:ℝ)) :=
        mul_le_mul_of_nonneg_right hL1' (Real.exp_pos _).le
      linarith [h4K]
    have hp : (2:ℝ)^(K+3) = 8*(2:ℝ)^K := by ring
    have h2K3 : 2*((2:ℝ)^(K+3)*K) ≤ 16*L*Real.exp (2*(K:ℝ)) := by
      rw [hp]
      nlinarith [mul_le_mul_of_nonneg_right h2K hK0,
        mul_le_mul_of_nonneg_left hKL (Real.exp_pos (2*(K:ℝ))).le]
    linarith
  have hmono : Real.exp (2*(K:ℝ)) ≤ Real.exp (L/6) := Real.exp_le_exp.mpr hK6
  have hV : E*(K:ℝ) + 4*(4:ℝ)^K + 2*((2:ℝ)^(K+3)*K)
      ≤ (E+20)*L*Real.exp (L/6) := by
    have h := mul_le_mul_of_nonneg_left hmono (mul_nonneg (by linarith : (0:ℝ) ≤ E+20) hL0.le)
    linarith
  have hU0 : (0:ℝ) ≤ E*(K:ℝ) + 4*(4:ℝ)^K + 2*((2:ℝ)^(K+3)*K) := by
    have := mul_nonneg hE hK0; positivity
  -- key quotient chain
  have hquot : (E+20)*L*Real.exp (L/6) / Real.exp L = (E+20)*L/Real.exp (5*L/6) := by
    have hsplit : Real.exp L = Real.exp (L/6) * Real.exp (5*L/6) := by
      rw [← Real.exp_add]; ring_nf
    rw [hsplit]
    field_simp
  have h56 : 25*L^2/144 ≤ Real.exp (5*L/6) := by
    calc 25*L^2/144 = ((5*L/6)/2)^2 := by ring
      _ ≤ Real.exp (5*L/6) := ms_div_pow_le_exp 2 (by positivity)
  have hd : (E+20)*L/Real.exp (5*L/6) ≤ (E+20)*L/(25*L^2/144) :=
    ms_div_le_div (by nlinarith) (le_refl _) (by positivity) h56
  have heq : (E+20)*L/(25*L^2/144) = 144*(E+20)/(25*L) := by
    field_simp
  have hstep : 144*(E+20)/(25*L) ≤ 6*(E+20)/L := by
    rw [div_le_div_iff₀ (by positivity) hL0]
    nlinarith
  have hfinal : 6*(E+20)/L ≤ η := by
    rw [div_le_iff₀ hL0]
    have h1 : η*(6*(E+20)/η) = 6*(E+20) := by field_simp
    nlinarith [mul_le_mul_of_nonneg_left hΛE hη.le, mul_le_mul_of_nonneg_left hL1 hη.le]
  -- assemble
  have hLHS : E*(K:ℝ)/x₀ + 2*(2*(4:ℝ)^K/x₀ + (2:ℝ)^(K+3)*K/x₀)
      = (E*(K:ℝ) + 4*(4:ℝ)^K + 2*((2:ℝ)^(K+3)*K))/x₀ := by ring
  rw [hLHS]
  calc (E*(K:ℝ) + 4*(4:ℝ)^K + 2*((2:ℝ)^(K+3)*K))/(x₀:ℝ)
      ≤ ((E+20)*L*Real.exp (L/6))/Real.exp L := ms_div_le_div hU0 hV ht0 hx₀
    _ = (E+20)*L/Real.exp (5*L/6) := hquot
    _ ≤ (E+20)*L/(25*L^2/144) := hd
    _ = 144*(E+20)/(25*L) := heq
    _ ≤ 6*(E+20)/L := hstep
    _ ≤ η := hfinal

/-- Lower bound `Λ/2 ≤ log(K/2)` for the floor-chosen `K`. -/
lemma ms_logK2_ge {Λ L : ℝ} {K M : ℕ} (hM1 : 1 ≤ M) (hΛM : 3*(M:ℝ)+30 ≤ Λ)
    (hL : Real.exp Λ = L) (hKlow : L/(2*(M:ℝ)*Λ) ≤ (K:ℝ)) :
    Λ/2 ≤ Real.log ((K:ℝ)/2) := by
  have hMR : (1:ℝ) ≤ (M:ℝ) := by exact_mod_cast hM1
  have hM0 : (0:ℝ) < (M:ℝ) := by linarith
  have hΛ0 : (0:ℝ) < Λ := by linarith
  have hL0 : (0:ℝ) < L := by rw [← hL]; exact Real.exp_pos Λ
  have hq0 : (0:ℝ) < L/(4*(M:ℝ)*Λ) := by positivity
  have hK2 : L/(4*(M:ℝ)*Λ) ≤ (K:ℝ)/2 := by
    have heq : L/(4*(M:ℝ)*Λ) = (L/(2*(M:ℝ)*Λ))/2 := by ring
    rw [heq]
    linarith
  have h1 : Real.log (L/(4*(M:ℝ)*Λ)) ≤ Real.log ((K:ℝ)/2) := Real.log_le_log hq0 hK2
  have h2 : Real.log (L/(4*(M:ℝ)*Λ)) = Real.log L - Real.log (4*(M:ℝ)*Λ) :=
    Real.log_div hL0.ne' (by positivity)
  have h3 : Real.log L = Λ := by rw [← hL, Real.log_exp]
  have h4 : Real.log (4*(M:ℝ)*Λ) ≤ Λ/2 := by
    have ha : Real.log (4*(M:ℝ)*Λ) = Real.log 4 + Real.log (M:ℝ) + Real.log Λ := by
      rw [Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by norm_num) (by positivity)]
    have hb : Real.log (4:ℝ) ≤ 3 := by
      have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 4 by norm_num); linarith
    have hc : Real.log (M:ℝ) ≤ (M:ℝ) := by
      have := Real.log_le_sub_one_of_pos hM0; linarith
    have hd : Real.log Λ ≤ Λ/8 + 8 := ms_log_le_div_add (by norm_num) hΛ0
    rw [ha]
    linarith
  linarith [h2 ▸ h1]

/-- The per-scale target `1/(112 M)` is below `K·log(K/2)/(28 L)`. -/
lemma ms_tau_ge {Λ L : ℝ} {K M : ℕ} (hΛ0 : 0 < Λ) (hL0 : 0 < L) (hM0 : 0 < M)
    (hKlow : L/(2*(M:ℝ)*Λ) ≤ (K:ℝ)) (hlg : Λ/2 ≤ Real.log ((K:ℝ)/2)) :
    1/(112*(M:ℝ)) ≤ (K:ℝ)*Real.log ((K:ℝ)/2)/(28*L) := by
  have hM0R : (0:ℝ) < (M:ℝ) := by exact_mod_cast hM0
  have h1 : L/(2*(M:ℝ)*Λ)*(Λ/2) ≤ (K:ℝ)*Real.log ((K:ℝ)/2) :=
    mul_le_mul hKlow hlg (by positivity) (Nat.cast_nonneg K)
  have heq : L/(2*(M:ℝ)*Λ)*(Λ/2) = L/(4*(M:ℝ)) := by field_simp; ring
  have h2 : L/(4*(M:ℝ))/(28*L) = 1/(112*(M:ℝ)) := by field_simp; ring
  rw [← h2]
  exact ms_div_le_div (by positivity) (heq ▸ h1) (by positivity) (le_refl _)

/-- Energy lower bound in the window form used by the recursion. -/
lemma ms_pairSum_ge {B : Finset ℕ} {x₀ H K : ℕ} {L : ℝ}
    (hcard : B.card = K) (hK4 : 4 ≤ K) (hH1 : 1 ≤ H)
    (hwin : ∀ p ∈ B, x₀ < p ∧ p ≤ x₀ + H)
    (hHb : (H:ℝ) ≤ 7*K*L) (hL0 : 0 < L)
    (hlg0 : 0 ≤ Real.log ((K:ℝ)/2)) :
    (K:ℝ)*Real.log ((K:ℝ)/2)/(28*L) ≤ pairSum B := by
  have hH0 : (1:ℝ) ≤ (H:ℝ) := by exact_mod_cast hH1
  have hK0 : (0:ℝ) < (K:ℝ) := by
    have : 0 < K := by omega
    exact_mod_cast this
  have hdiam : ∀ a ∈ B, ∀ b ∈ B, (b:ℝ) - (a:ℝ) ≤ (H:ℝ) := by
    intro a ha b hb
    have h1 : x₀ + 1 ≤ a := (hwin a ha).1
    have h2 : b ≤ x₀ + H := (hwin b hb).2
    have h1' : ((x₀:ℝ) + 1) ≤ (a:ℝ) := by exact_mod_cast h1
    have h2' : (b:ℝ) ≤ (x₀:ℝ) + (H:ℝ) := by exact_mod_cast h2
    linarith
  have hE := pairSum_ge_energy (A := B) (H := (H:ℝ))
    (by omega : 4 ≤ B.card) hH0 hdiam
  rw [hcard] at hE
  have h4H : (0:ℝ) < 4*(H:ℝ) := by linarith
  have hnum : (0:ℝ) ≤ (K:ℝ)^2*Real.log ((K:ℝ)/2) := mul_nonneg (by positivity) hlg0
  have hchain : (K:ℝ)*Real.log ((K:ℝ)/2)/(28*L)
      ≤ (K:ℝ)^2*Real.log ((K:ℝ)/2)/(4*(H:ℝ)) := by
    have heq : (K:ℝ)*Real.log ((K:ℝ)/2)/(28*L) = (K:ℝ)^2*Real.log ((K:ℝ)/2)/(28*(K:ℝ)*L) := by
      field_simp
    rw [heq]
    exact ms_div_le_div hnum (le_refl _) h4H (by nlinarith)
  calc (K:ℝ)*Real.log ((K:ℝ)/2)/(28*L)
      ≤ (K:ℝ)^2*Real.log ((K:ℝ)/2)/(4*(H:ℝ)) := hchain
    _ ≤ pairSum B := hE

/-- The two main gap-cost terms are at most `P/(8C)` for any `P ≥ K·log(K/2)/(28L)`. -/
lemma ms_main_aux {Λ L ε C P : ℝ} {K N : ℕ}
    (hC : 0 < C) (hε : 0 < ε) (hΛ : 30 ≤ Λ) (hL0 : 0 < L)
    (hK0 : 0 < (K:ℝ)) (hN0 : 0 < (N:ℝ))
    (hlogKΛ : Real.log K ≤ Λ)
    (hlg : Λ/2 ≤ Real.log ((K:ℝ)/2))
    (hεΛ : 1792*C ≤ ε*Λ)
    (hε2L : 7168*C ≤ ε^2*L)
    (hNlow : ε*L ≤ (N:ℝ))
    (hP : (K:ℝ)*Real.log ((K:ℝ)/2)/(28*L) ≤ P) :
    2*((K:ℝ)/N + 2*K*(1 + Real.log K)/N^2) ≤ P/(8*C) := by
  have hlg0 : (0:ℝ) < Real.log ((K:ℝ)/2) := by linarith
  have hεL0 : (0:ℝ) < ε*L := by positivity
  have hKlg0 : (0:ℝ) ≤ (K:ℝ)*Real.log ((K:ℝ)/2) := by positivity
  have ht1 : 2*(K:ℝ)/N ≤ (K:ℝ)*Real.log ((K:ℝ)/2)/(28*L)/(16*C) := by
    rw [div_div, div_le_div_iff₀ hN0 (by positivity)]
    have h1 : (K:ℝ)*(Λ/2)*(ε*L) ≤ (K:ℝ)*Real.log ((K:ℝ)/2)*N :=
      mul_le_mul (mul_le_mul_of_nonneg_left hlg hK0.le) hNlow hεL0.le hKlg0
    have h2 : (K:ℝ)*L*(1792*C) ≤ (K:ℝ)*L*(ε*Λ) :=
      mul_le_mul_of_nonneg_left hεΛ (by positivity)
    nlinarith [h1, h2]
  have ht2 : 2*(2*(K:ℝ)*(1 + Real.log K)/N^2) ≤ (K:ℝ)*Real.log ((K:ℝ)/2)/(28*L)/(16*C) := by
    have hlhs : 2*(2*(K:ℝ)*(1 + Real.log K)/N^2) = (4*(K:ℝ)*(1 + Real.log K))/(N:ℝ)^2 := by
      ring
    rw [hlhs, div_div, div_le_div_iff₀ (by positivity : (0:ℝ) < ((N:ℝ))^2) (by positivity)]
    have hN2 : (ε*L)^2 ≤ ((N:ℝ))^2 := pow_le_pow_left₀ hεL0.le hNlow 2
    have h1 : (K:ℝ)*(Λ/2)*((ε*L)^2) ≤ (K:ℝ)*Real.log ((K:ℝ)/2)*((N:ℝ))^2 :=
      mul_le_mul (mul_le_mul_of_nonneg_left hlg hK0.le) hN2 (by positivity) hKlg0
    have h2 : 1 + Real.log K ≤ 2*Λ := by linarith
    have h3 := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right h2 (show (0:ℝ) ≤ 28*L*(16*C) by positivity))
      (show (0:ℝ) ≤ 2*(2*(K:ℝ)) by positivity)
    have h4 : 7168*C*L ≤ ε^2*L*L := mul_le_mul_of_nonneg_right hε2L hL0.le
    have h5 := mul_le_mul_of_nonneg_left h4 (show (0:ℝ) ≤ (K:ℝ)*(Λ/2) by positivity)
    nlinarith [h1, h3, h5]
  have hPC : (K:ℝ)*Real.log ((K:ℝ)/2)/(28*L)/(16*C) + (K:ℝ)*Real.log ((K:ℝ)/2)/(28*L)/(16*C)
      = ((K:ℝ)*Real.log ((K:ℝ)/2)/(28*L))/(8*C) := by
    field_simp
    ring
  have hfin : ((K:ℝ)*Real.log ((K:ℝ)/2)/(28*L))/(8*C) ≤ P/(8*C) :=
    ms_div_le_div (by positivity) hP (by positivity) (le_refl _)
  have hsum : 2*((K:ℝ)/N + 2*(K:ℝ)*(1 + Real.log K)/N^2)
      = 2*(K:ℝ)/N + 2*(2*(K:ℝ)*(1 + Real.log K)/N^2) := by ring
  rw [hsum]
  linarith [ht1, ht2, hPC, hfin]

/-! ### The scale-setup lemma -/

/-- The conclusion of `separated_primes_selection` for fixed `ε, T_C`. -/
def ms_SelProp (ε T_C : ℝ) : Prop :=
  ∀ t : ℝ, T_C ≤ t → ∀ K : ℕ, 2 ≤ K →
    (K : ℝ) ≤ Real.log t / Real.log (Real.log t) →
    ∃ (B : Finset ℕ) (x₀ N H : ℕ),
      (∀ p ∈ B, Nat.Prime p) ∧ B.card = K ∧
      (t ≤ (x₀:ℝ)) ∧ ((x₀:ℝ) ≤ 8*t) ∧
      (∀ p ∈ B, x₀ < p ∧ p ≤ x₀ + H) ∧
      (∀ p ∈ B, ∀ q ∈ B, p < q → N < q - p) ∧
      (ε * Real.log t ≤ (N:ℝ)) ∧ ((N:ℝ) ≤ Real.log t) ∧ 1 ≤ N ∧
      ((H:ℝ) ≤ 7 * K * Real.log t) ∧ 1 ≤ H ∧ ((x₀:ℝ) + H ≤ 9*t)

set_option maxHeartbeats 1600000 in
/-- One scale, fully prepared: primes `B` in a window above `Θ`, with all side conditions
for `oneScale`/`scaleStep`, a pair-sum contribution of at least `1/(112M)`, main gap-cost
controlled by `pairSum B/(8C)`, and all junk terms below `η`. -/
lemma ms_scale_setup {ε T_C : ℝ} (C : ℝ) (hC : 0 < C) (hε : 0 < ε)
    (hsel : ms_SelProp ε T_C) (M : ℕ) (hM : 12 ≤ M)
    (Θ E η γ : ℝ) (hE : 0 ≤ E) (hη : 0 < η) (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    ∃ (B : Finset ℕ) (x₀ N H K : ℕ),
      (∀ p ∈ B, Nat.Prime p) ∧ B.card = K ∧ 4 ≤ K ∧
      (∀ p ∈ B, x₀ < p ∧ p ≤ x₀ + H) ∧
      (∀ p ∈ B, ∀ q ∈ B, p < q → N < q - p) ∧
      1 ≤ N ∧ 1 ≤ H ∧ 4 ≤ x₀ ∧ Θ ≤ (x₀:ℝ) ∧
      8 * (2*H)^(K+1) ≤ x₀ ∧ 2*K*H ≤ x₀ ∧
      2 * (1 + Real.log K) ≤ (N:ℝ) ∧
      2*(K:ℝ)*H ≤ γ * x₀ ∧
      2*(K:ℝ)/x₀ ≤ η ∧
      1/(112*(M:ℝ)) ≤ pairSum B ∧
      2*((K:ℝ)/N + 2*K*(1 + Real.log K)/N^2) ≤ pairSum B / (8*C) ∧
      E*(K:ℝ)/x₀ + 2*(2*(4:ℝ)^K/x₀ + (2:ℝ)^(K+3)*K/x₀) ≤ η := by
  -- an opaque threshold Λ dominating every requirement
  obtain ⟨Λ, h30, hc20M, hc3M, hc16ε, hc1792, hc7168, hcγ, hcE, hcΘ, hcT, hcη⟩ :
      ∃ Λ : ℝ, 30 ≤ Λ ∧ 20*(M:ℝ) ≤ Λ ∧ 3*(M:ℝ)+30 ≤ Λ ∧ 16/ε ≤ Λ ∧ 1792*C/ε ≤ Λ ∧
        7168*C/ε^2 ≤ Λ ∧ 3584/γ ≤ Λ ∧ 6*(E+20)/η ≤ Λ ∧ Θ ≤ Λ ∧ T_C ≤ Λ ∧ 8/η ≤ Λ := by
    refine ⟨max 30 (max (20*(M:ℝ)) (max (3*(M:ℝ)+30) (max (16/ε) (max (1792*C/ε)
      (max (7168*C/ε^2) (max (3584/γ) (max (6*(E+20)/η) (max Θ (max T_C (8/η)))))))))),
      le_max_left _ _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact le_max_of_le_right (le_max_left _ _)
    · exact le_max_of_le_right (le_max_of_le_right (le_max_left _ _))
    · exact le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))
    · exact le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
        (le_max_of_le_right (le_max_left _ _))))
    · exact le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
        (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))))
    · exact le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
        (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _))))))
    · exact le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
        (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
          (le_max_of_le_right (le_max_left _ _)))))))
    · exact le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
        (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
          (le_max_of_le_right (le_max_of_le_right (le_max_left _ _))))))))
    · exact le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
        (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
          (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))))))))
    · exact le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
        (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
          (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_right _ _)))))))))
  have hMR : (12:ℝ) ≤ (M:ℝ) := by exact_mod_cast hM
  have hM1R : (1:ℝ) ≤ (M:ℝ) := by linarith
  have hΛ0 : (0:ℝ) < Λ := by linarith
  -- an opaque L with exp Λ = L
  obtain ⟨L, hexpΛ⟩ : ∃ L : ℝ, Real.exp Λ = L := ⟨_, rfl⟩
  have hL1 : Λ + 1 ≤ L := by rw [← hexpΛ]; exact Real.add_one_le_exp Λ
  have hL0 : (0:ℝ) < L := by rw [← hexpΛ]; exact Real.exp_pos Λ
  have hL31 : 31 ≤ L := by linarith
  have hLΛ : Λ ≤ L := by linarith
  have hLsq : Λ^2/4 ≤ L := by
    calc Λ^2/4 = (Λ/2)^2 := by ring
      _ ≤ Real.exp Λ := ms_div_pow_le_exp 2 hΛ0.le
      _ = L := hexpΛ
  have ht1 : L + 1 ≤ Real.exp L := Real.add_one_le_exp L
  have ht0 : (0:ℝ) < Real.exp L := Real.exp_pos L
  have hlogL : Real.log L = Λ := by rw [← hexpΛ, Real.log_exp]
  have hx5 : 5 ≤ L/((M:ℝ)*Λ) := by
    have h1 : 5 ≤ (Λ^2/4)/((M:ℝ)*Λ) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_right hc20M hΛ0.le]
    have h2 : (Λ^2/4)/((M:ℝ)*Λ) ≤ L/((M:ℝ)*Λ) :=
      ms_div_le_div (by positivity) hLsq (by positivity) (le_refl _)
    linarith
  -- an opaque K with the floor properties
  obtain ⟨K, hK4, hKx, hxK⟩ :
      ∃ K : ℕ, 4 ≤ K ∧ (K:ℝ) ≤ L/((M:ℝ)*Λ) ∧ L/((M:ℝ)*Λ) < (K:ℝ)+1 := by
    refine ⟨⌊L/((M:ℝ)*Λ)⌋₊, ?_, Nat.floor_le (by positivity), Nat.lt_floor_add_one _⟩
    exact Nat.le_floor (by push_cast; linarith)
  have hK2 : 2 ≤ K := by omega
  have hK1N : 1 ≤ K := by omega
  have hK0 : (0:ℝ) < (K:ℝ) := by
    have h4 : (4:ℝ) ≤ (K:ℝ) := by exact_mod_cast hK4
    linarith
  have hK1R : (1:ℝ) ≤ (K:ℝ) := by linarith
  have hKlow : L/(2*(M:ℝ)*Λ) ≤ (K:ℝ) := by
    have heq : L/(2*(M:ℝ)*Λ) = (L/((M:ℝ)*Λ))/2 := by ring
    rw [heq]
    linarith
  have hKMΛ : (K:ℝ)*((M:ℝ)*Λ) ≤ L := (le_div_iff₀ (by positivity)).mp hKx
  have hK12 : (K:ℝ)*(12*Λ) ≤ L := by
    nlinarith [mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hMR hΛ0.le) hK0.le]
  have hKL : (K:ℝ) ≤ L := by
    nlinarith [mul_le_mul_of_nonneg_left (show (1:ℝ) ≤ 12*Λ by linarith) hK0.le]
  have hK6 : 2*(K:ℝ) ≤ L/6 := by
    nlinarith [mul_le_mul_of_nonneg_left (show (12:ℝ) ≤ 12*Λ by linarith) hK0.le]
  have hlogKΛ : Real.log (K:ℝ) ≤ Λ := by
    have h1 : Real.log (K:ℝ) ≤ Real.log L := Real.log_le_log hK0 hKL
    rwa [hlogL] at h1
  have hlg : Λ/2 ≤ Real.log ((K:ℝ)/2) :=
    ms_logK2_ge (by omega) (by linarith) hexpΛ hKlow
  have hlg0 : (0:ℝ) ≤ Real.log ((K:ℝ)/2) := by linarith
  have hεΛ16 : 16 ≤ ε*Λ := by
    have heq : ε*(16/ε) = 16 := by field_simp
    nlinarith [mul_le_mul_of_nonneg_left hc16ε hε.le]
  have hεΛC : 1792*C ≤ ε*Λ := by
    have heq : ε*(1792*C/ε) = 1792*C := by field_simp
    nlinarith [mul_le_mul_of_nonneg_left hc1792 hε.le]
  have hε2L : 7168*C ≤ ε^2*L := by
    have heq : ε^2*(7168*C/ε^2) = 7168*C := by field_simp
    have h1 : ε^2*Λ ≤ ε^2*L := mul_le_mul_of_nonneg_left hLΛ (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left hc7168 (show (0:ℝ) ≤ ε^2 by positivity)]
  have hTt : T_C ≤ Real.exp L := by linarith
  have hKcap : (K:ℝ) ≤ Real.log (Real.exp L) / Real.log (Real.log (Real.exp L)) := by
    rw [Real.log_exp, hlogL, le_div_iff₀ hΛ0]
    nlinarith [mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hM1R hΛ0.le) hK0.le]
  obtain ⟨B, x₀, N, H, hBp, hBcard, hx₀t, hx₀8t, hwin, hsep, hNlow, hNup, hN1, hHb, hH1, hx₀H⟩ :=
    hsel (Real.exp L) hTt K hK2 hKcap
  rw [Real.log_exp] at hNlow hNup hHb
  have hx₀0 : (0:ℝ) < (x₀:ℝ) := lt_of_lt_of_le ht0 hx₀t
  have hN0 : (0:ℝ) < (N:ℝ) := by
    have h1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN1
    linarith
  have hH1R : (1:ℝ) ≤ (H:ℝ) := by exact_mod_cast hH1
  have hPS : (K:ℝ)*Real.log ((K:ℝ)/2)/(28*L) ≤ pairSum B :=
    ms_pairSum_ge hBcard hK4 hH1 hwin hHb hL0 hlg0
  have hbigR := ms_hbig_aux h30 hexpΛ hH1R hK1R hK12 hHb
  have hKHR := ms_KH_aux hγ hcγ h30 hexpΛ hKL hHb
  refine ⟨B, x₀, N, H, K, hBp, hBcard, hK4, hwin, hsep, hN1, hH1,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- 4 ≤ x₀
    have h4 : (4:ℝ) ≤ (x₀:ℝ) := by linarith
    exact_mod_cast h4
  · -- Θ ≤ x₀
    linarith
  · -- hbig
    have hcast : ((8*(2*H)^(K+1) : ℕ):ℝ) ≤ (x₀:ℝ) := by push_cast; linarith
    exact_mod_cast hcast
  · -- hKH
    have h1 : γ*Real.exp L ≤ Real.exp L := by
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1-γ) ht0.le]
    have hcast : ((2*K*H : ℕ):ℝ) ≤ (x₀:ℝ) := by push_cast; linarith
    exact_mod_cast hcast
  · -- hlogK
    have h1 : ε*(Λ^2/4) ≤ ε*L := mul_le_mul_of_nonneg_left hLsq hε.le
    have h2 : 4*Λ ≤ ε*(Λ^2/4) := by
      nlinarith [mul_le_mul_of_nonneg_right hεΛ16 hΛ0.le]
    linarith [hlogKΛ]
  · -- 2KH ≤ γ x₀
    have h1 : γ*Real.exp L ≤ γ*(x₀:ℝ) := mul_le_mul_of_nonneg_left hx₀t hγ.le
    linarith
  · -- 2K/x₀ ≤ η
    have h1 : 2*(K:ℝ)/x₀ ≤ 2*L/Real.exp L :=
      ms_div_le_div (by positivity) (by linarith) ht0 hx₀t
    have hsqt : L^2/4 ≤ Real.exp L := by
      calc L^2/4 = (L/2)^2 := by ring
        _ ≤ Real.exp L := ms_div_pow_le_exp 2 hL0.le
    have h2 : 2*L/Real.exp L ≤ 2*L/(L^2/4) :=
      ms_div_le_div (by positivity) (le_refl _) (by positivity) hsqt
    have h3 : 2*L/(L^2/4) = 8/L := by
      field_simp
      ring
    have h4 : 8/L ≤ η := by
      rw [div_le_iff₀ hL0]
      have heq : η*(8/η) = 8 := by field_simp
      nlinarith [mul_le_mul_of_nonneg_left hcη hη.le, mul_le_mul_of_nonneg_left hLΛ hη.le]
    linarith [h3 ▸ h2]
  · -- pairSum lower bound
    exact le_trans (ms_tau_ge hΛ0 hL0 (by omega) hKlow hlg) hPS
  · -- main terms
    exact ms_main_aux hC hε h30 hL0 hK0 hN0 hlogKΛ hlg hεΛC hε2L hNlow hPS
  · -- error terms
    exact ms_err_aux hE hη h30 hcE hexpΛ hK6 hKL hx₀t

/-! ### The multiscale recursion -/

/-- The growing sequence of states: at stage `r` we have `n` with harmonic-type
pair-sum mass `A` and gap sum controlled by `A/(8C) + 3`. -/
lemma ms_grow {ε T_C : ℝ} (C : ℝ) (hC : 0 < C) (hε : 0 < ε)
    (hsel : ms_SelProp ε T_C) (n₀ : ℕ) :
    ∀ r : ℕ, 1 ≤ r → ∃ (n : ℕ) (A : ℝ), n ≠ 0 ∧ n₀ ≤ n ∧
      (∑ d ∈ n.divisors, ((d:ℝ))⁻¹ ≤ 2 - (1/2:ℝ)^r) ∧
      (∑ i ∈ Finset.Icc 1 r, 1/((i:ℝ)+12))/112 ≤ A ∧
      A ≤ pairSum n.divisors ∧
      gapSum n.divisors ≤ A/(8*C) + 3 - (1/2:ℝ)^r := by
  intro r hr
  induction r with
  | zero => omega
  | succ r ih =>
    rcases Nat.eq_zero_or_pos r with rfl | hr1
    · -- base case: a single scale
      obtain ⟨B, x₀, N, H, K, hBp, hBcard, hK4, hwin, hsep, hN1, hH1, hx₀4, hΘ,
          hbig, hKH, hlogK, hγb, hη2K, hPlow, hmain, herr⟩ :=
        ms_scale_setup C hC hε hsel 13 (by norm_num) (n₀:ℝ) 0 (1/8) 1
          (le_refl 0) (by norm_num) one_pos (le_refl 1)
      have hm0 : (∏ p ∈ B, p) ≠ 0 := os_prodB_ne_zero hBp
      have hBne : B.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨p₀, hp₀⟩ := hBne
      have hn₀m : n₀ ≤ ∏ p ∈ B, p := by
        have h1 : n₀ ≤ x₀ := by exact_mod_cast hΘ
        have h3 : x₀ < p₀ := (hwin p₀ hp₀).1
        have h4 : p₀ ≤ ∏ p ∈ B, p := ms_le_prodB hBp hp₀
        omega
      have h2K : 2*B.card ≤ x₀ := by
        rw [hBcard]
        calc 2*K = 2*K*1 := (mul_one _).symm
          _ ≤ 2*K*H := Nat.mul_le_mul_left _ hH1
          _ ≤ x₀ := hKH
      have hσm : ∑ d ∈ (∏ p ∈ B, p).divisors, ((d:ℝ))⁻¹ ≤ 1 + 2*(K:ℝ)/x₀ := by
        have h := sum_inv_divisors_le hBp (fun p hp => (hwin p hp).1.le) h2K (by omega)
        rwa [hBcard] at h
      have hOS := oneScale_gapSum_le hBp hBcard hN1 hH1 hwin hsep hbig hKH hx₀4 hlogK
      have hBsub : B ⊆ (∏ p ∈ B, p).divisors := fun p hp =>
        Nat.mem_divisors.mpr ⟨Finset.dvd_prod_of_mem _ hp, hm0⟩
      have hPnn : 0 ≤ pairSum B := pairSum_nonneg B
      simp only [zero_add, pow_one]
      refine ⟨∏ p ∈ B, p, pairSum B, hm0, hn₀m, ?_, ?_, ms_pairSum_mono hBsub, ?_⟩
      · -- σ invariant
        linarith
      · -- A lower bound
        have h13 : ((1:ℕ):ℝ) + 12 = 13 := by norm_num
        rw [Finset.Icc_self, Finset.sum_singleton, h13]
        norm_num at hPlow
        linarith
      · -- gap sum invariant
        have hhalf : pairSum B/(16*C) = (pairSum B/(8*C))/2 := by ring
        have hPC : 0 ≤ pairSum B/(8*C) := by positivity
        norm_num at herr
        linarith [hOS, hmain, herr, hPC]
    · -- inductive step
      obtain ⟨n, A, hn0, hnn₀, hσ, hAlow, hAup, hG⟩ := ih hr1
      obtain ⟨δ, hδ0, hδ1, hδ⟩ := exists_min_log_gap n hn0
      have hGnn : 0 ≤ gapSum n.divisors := gapSum_nonneg _
      have hE0 : 0 ≤ 2*gapSum n.divisors + 16/δ :=
        add_nonneg (by linarith) (div_nonneg (by norm_num) hδ0.le)
      obtain ⟨B, x₀, N, H, K, hBp, hBcard, hK4, hwin, hsep, hN1, hH1, hx₀4, hΘ,
          hbig, hKH, hlogK, hγb, hη2K, hPlow, hmain, herr⟩ :=
        ms_scale_setup C hC hε hsel (r+13) (by omega) (4*(n:ℝ))
          (2*gapSum n.divisors + 16/δ) ((1/2:ℝ)^(r+2)) δ hE0 (by positivity) hδ0 hδ1
      have hm0 : (∏ p ∈ B, p) ≠ 0 := os_prodB_ne_zero hBp
      have hnm0 : n * ∏ p ∈ B, p ≠ 0 := mul_ne_zero hn0 hm0
      have hnx₀ : n ≤ x₀ := by
        have h1 : (n:ℝ) ≤ (x₀:ℝ) := by
          have h2 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
          linarith
        exact_mod_cast h1
      have hngt : ∀ p ∈ B, n < p := fun p hp => lt_of_le_of_lt hnx₀ (hwin p hp).1
      have hcop : n.Coprime (∏ p ∈ B, p) :=
        ss_coprime_prod hn0 hBp (fun p hp => (hwin p hp).1) hnx₀
      have hp0 : (0:ℝ) < (1/2:ℝ)^r := by positivity
      have hpow1 : ((1/2:ℝ))^(r+1) = ((1/2:ℝ))^r/2 := by rw [pow_succ]; ring
      have hpow2 : ((1/2:ℝ))^(r+2) = ((1/2:ℝ))^r/4 := by rw [pow_succ, pow_succ]; ring
      have hp1 : ((1/2:ℝ))^r ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      have hσ2 : ∑ e ∈ n.divisors, ((e:ℝ))⁻¹ ≤ 2 := by linarith
      have hSS := scaleStep_gapSum_le hn0 hBp hBcard hN1 hH1 hx₀4 hwin hsep
        hbig hKH hlogK hδ0 hδ1 hδ hσ2 hΘ hγb
      -- σ invariant for the new state
      have h2K : 2*B.card ≤ x₀ := by
        rw [hBcard]
        calc 2*K = 2*K*1 := (mul_one _).symm
          _ ≤ 2*K*H := Nat.mul_le_mul_left _ hH1
          _ ≤ x₀ := hKH
      have hσm : ∑ d ∈ (∏ p ∈ B, p).divisors, ((d:ℝ))⁻¹ ≤ 1 + 2*(K:ℝ)/x₀ := by
        have h := sum_inv_divisors_le hBp (fun p hp => (hwin p hp).1.le) h2K (by omega)
        rwa [hBcard] at h
      have hσm_nn : 0 ≤ ∑ d ∈ (∏ p ∈ B, p).divisors, ((d:ℝ))⁻¹ :=
        Finset.sum_nonneg fun d _ => by positivity
      have hσ' : ∑ d ∈ (n * ∏ p ∈ B, p).divisors, ((d:ℝ))⁻¹ ≤ 2 - (1/2:ℝ)^(r+1) := by
        rw [sum_inv_divisors_mul hcop]
        have hσm' : ∑ d ∈ (∏ p ∈ B, p).divisors, ((d:ℝ))⁻¹ ≤ 1 + ((1/2:ℝ))^r/4 := by
          linarith
        have hprod := mul_le_mul hσ hσm' hσm_nn (by linarith)
        have hfin : (2 - (1/2:ℝ)^r)*(1 + (1/2:ℝ)^r/4) ≤ 2 - (1/2:ℝ)^r/2 := by
          nlinarith [sq_nonneg ((1/2:ℝ)^r)]
        rw [hpow1]
        linarith
      have hadd := ms_pairSum_add_le hn0 hBp hngt
      have hPnn : 0 ≤ pairSum B := pairSum_nonneg B
      refine ⟨n * ∏ p ∈ B, p, A + pairSum B, hnm0, ?_, hσ', ?_, ?_, ?_⟩
      · -- n₀ ≤ n·m
        exact le_trans hnn₀ (Nat.le_mul_of_pos_right n (Nat.pos_of_ne_zero hm0))
      · -- A lower bound
        rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ r+1), add_div]
        have hkey : 1/(((r+1:ℕ):ℝ)+12)/112 ≤ pairSum B := by
          have heq : 1/(((r+1:ℕ):ℝ)+12)/112 = 1/(112*(((r+13:ℕ)):ℝ)) := by
            push_cast
            rw [div_div]
            ring_nf
          rw [heq]
          exact hPlow
        linarith [hAlow, hkey]
      · -- A upper bound
        linarith [hAup, hadd]
      · -- gap sum invariant
        have hx₀R : (0:ℝ) < (x₀:ℝ) := by
          have h1 : 0 < x₀ := by omega
          exact_mod_cast h1
        have hbr : 16*(K:ℝ)/(δ*(x₀:ℝ)) = 16/δ*(K:ℝ)/(x₀:ℝ) := by
          rw [div_eq_mul_inv, mul_inv]
          ring
        rw [hbr] at hSS
        have hexp : gapSum n.divisors * (1 + 2*(K:ℝ)/(x₀:ℝ))
            = gapSum n.divisors + 2*gapSum n.divisors*((K:ℝ)/(x₀:ℝ)) := by ring
        rw [hexp] at hSS
        have hEexp : (2*gapSum n.divisors + 16/δ)*(K:ℝ)/(x₀:ℝ)
            = 2*gapSum n.divisors*((K:ℝ)/(x₀:ℝ)) + 16/δ*(K:ℝ)/(x₀:ℝ) := by ring
        rw [hEexp] at herr
        have hkey : gapSum ((n * ∏ p ∈ B, p).divisors)
            ≤ gapSum n.divisors + (1/2:ℝ)^(r+2) + pairSum B/(8*C) := by
          linarith [hSS, herr, hmain]
        have hsplit : (A + pairSum B)/(8*C) = A/(8*C) + pairSum B/(8*C) := by ring
        linarith [hkey, hG, hp0, hpow1, hpow2, hsplit]

/-! ### The export: divisor pair sums beat gap sums by any constant factor -/

/-- **Multiscale construction.**  For every `C > 0` and every threshold `n₀` there is an
`n ≥ n₀` with `C * (1 + S(n)) < T(n)`, where `S` is the sum of reciprocals of consecutive
divisor gaps and `T` the sum of reciprocals of all divisor differences. -/
theorem exists_ratio_large :
    ∀ C : ℝ, 0 < C → ∀ n₀ : ℕ, ∃ n : ℕ, n₀ ≤ n ∧ n ≠ 0 ∧
      C * (1 + gapSum n.divisors) < pairSum n.divisors := by
  intro C hC n₀
  obtain ⟨ε, hε, hε1, T_C, hTC, hsel⟩ := separated_primes_selection
  -- choose a stage r whose harmonic mass exceeds 560·C
  obtain ⟨r, hr1, hSr⟩ :
      ∃ r : ℕ, 1 ≤ r ∧ 560*C ≤ ∑ i ∈ Finset.Icc 1 r, 1/((i:ℝ)+12) := by
    obtain ⟨R, hRgt⟩ := exists_nat_gt (Real.exp (7280*C))
    refine ⟨R + 1, by omega, ?_⟩
    have hexpR : Real.exp (7280*C) ≤ ((R+1:ℕ):ℝ) + 1 := by push_cast; linarith
    have h2 : 7280*C ≤ Real.log (((R+1:ℕ):ℝ)+1) := by
      have h3 := Real.log_le_log (Real.exp_pos _) hexpR
      rwa [Real.log_exp] at h3
    have h4 := log_le_sum_inv (R+1)
    have h5 : ∑ i ∈ Finset.Icc 1 (R+1), ((i:ℝ))⁻¹
        ≤ 13 * ∑ i ∈ Finset.Icc 1 (R+1), 1/((i:ℝ)+12) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i hi
      have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
      have hiR : (1:ℝ) ≤ (i:ℝ) := by exact_mod_cast hi1
      rw [mul_one_div, inv_eq_one_div, div_le_div_iff₀ (by linarith) (by linarith)]
      linarith
    linarith
  obtain ⟨n, A, hn0, hnn₀, hσ, hAlow, hAup, hG⟩ := ms_grow C hC hε hsel n₀ r hr1
  refine ⟨n, hnn₀, hn0, ?_⟩
  have hA5C : 5*C ≤ A := by linarith
  have hp0 : (0:ℝ) < (1/2:ℝ)^r := by positivity
  have hCne : C ≠ 0 := hC.ne'
  have h1 : C*(1 + gapSum n.divisors) ≤ C*(4 + A/(8*C)) := by
    apply mul_le_mul_of_nonneg_left _ hC.le
    linarith
  have hCA : C * (A/(8*C)) = A/8 := by
    field_simp
  have h2 : C*(4 + A/(8*C)) = 4*C + C*(A/(8*C)) := by ring
  have h3 : 4*C + A/8 < A := by linarith
  linarith [h1, h2, hCA, h3, hAup]

end Erdos884
