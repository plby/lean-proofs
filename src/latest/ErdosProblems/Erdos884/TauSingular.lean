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
import ErdosProblems.Erdos884.PolyGap

set_option linter.mathlibStandardSet false

/-!
# Erdős 884 — Lemma B auxiliary sums (TauBound and B.4)

Exports:
* `sum_inv_le_one_add_log` : `∑_{1 ≤ e ≤ y} 1/e ≤ 1 + log y`
* `sum_pow_primeFactors_le` : `∑_{1 ≤ d ≤ y} c^{ω(d)} ≤ y (1 + log y)^{c-1}` for `c ≥ 1`
* `sum_totient_ratio_sq_le` : `∑_{1 ≤ h ≤ N} (h/φ(h))² ≤ 200 N`
-/

namespace Erdos884

/-! ### Harmonic sum: `∑_{e ≤ y} 1/e ≤ 1 + log y` -/

lemma one_add_log_natCast_nonneg (y : ℕ) : (0:ℝ) ≤ 1 + Real.log y := by
  have := Real.log_natCast_nonneg y
  linarith

theorem sum_inv_le_one_add_log (y : ℕ) :
    ∑ e ∈ Finset.Icc 1 y, ((e:ℝ))⁻¹ ≤ 1 + Real.log y := by
  have h1 : ((harmonic y : ℚ) : ℝ) = ∑ e ∈ Finset.Icc 1 y, ((e:ℝ))⁻¹ := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    rfl
  rw [← h1]
  exact_mod_cast harmonic_le_one_add_log y

/-! ### Telescoping: `∑_{2 ≤ n ≤ M} 2/(n-1)² ≤ 4 - 4/M` -/

lemma sum_two_div_sq_le (M : ℕ) (hM : 1 ≤ M) :
    ∑ n ∈ Finset.Icc 2 M, 2 / (((n:ℝ) - 1) ^ 2) ≤ 4 - 4 / (M:ℝ) := by
  induction M, hM using Nat.le_induction with
  | base =>
    rw [Finset.Icc_eq_empty (by omega)]
    norm_num
  | succ M hM ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 2 ≤ M + 1)]
    have hM' : (1:ℝ) ≤ (M:ℝ) := by exact_mod_cast hM
    have hM0 : (0:ℝ) < (M:ℝ) := by linarith
    have hM1 : (0:ℝ) < (M:ℝ) + 1 := by linarith
    have key : 2 / ((M:ℝ)) ^ 2 ≤ 4 / (M:ℝ) - 4 / ((M:ℝ) + 1) := by
      rw [div_sub_div _ _ hM0.ne' hM1.ne']
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [sq_nonneg ((M:ℝ) - 1)]
    push_cast
    have e1 : (M:ℝ) + 1 - 1 = (M:ℝ) := by ring
    rw [e1]
    linarith [ih]

/-! ### Pointwise bound `(c+1)^{ω d} ≤ ∑_{e ∣ d} c^{ω e}` -/

lemma pow_card_powerset_expand (c : ℕ) (P : Finset ℕ) :
    ((c:ℝ) + 1) ^ P.card = ∑ S ∈ P.powerset, (c:ℝ) ^ S.card := by
  classical
  calc ((c:ℝ) + 1) ^ P.card
      = ∏ _p ∈ P, ((c:ℝ) + 1) := by rw [Finset.prod_const]
    _ = ∑ S ∈ P.powerset, (∏ _p ∈ S, (c:ℝ)) * ∏ _p ∈ P \ S, 1 := Finset.prod_add _ _ _
    _ = ∑ S ∈ P.powerset, (c:ℝ) ^ S.card := by simp [Finset.prod_const]

lemma pow_omega_le_sum_divisors (c : ℕ) {d : ℕ} (hd : d ≠ 0) :
    ((c:ℝ) + 1) ^ d.primeFactors.card
      ≤ ∑ e ∈ d.divisors, (c:ℝ) ^ e.primeFactors.card := by
  classical
  have hprime : ∀ S ∈ d.primeFactors.powerset, ∀ p ∈ S, Nat.Prime p := fun S hS p hp =>
    Nat.prime_of_mem_primeFactors (Finset.mem_powerset.mp hS hp)
  have hinj : Set.InjOn (fun S : Finset ℕ => ∏ p ∈ S, p) ↑d.primeFactors.powerset := by
    intro S hS T hT hST
    rw [Finset.mem_coe] at hS hT
    have h1 := Nat.primeFactors_prod (hprime S hS)
    have h2 := Nat.primeFactors_prod (hprime T hT)
    dsimp only at hST
    rw [← h1, ← h2, hST]
  calc ((c:ℝ) + 1) ^ d.primeFactors.card
      = ∑ S ∈ d.primeFactors.powerset, (c:ℝ) ^ S.card := pow_card_powerset_expand c _
    _ = ∑ S ∈ d.primeFactors.powerset, (c:ℝ) ^ (∏ p ∈ S, p).primeFactors.card :=
        Finset.sum_congr rfl fun S hS => by rw [Nat.primeFactors_prod (hprime S hS)]
    _ = ∑ e ∈ d.primeFactors.powerset.image (fun S => ∏ p ∈ S, p),
          (c:ℝ) ^ e.primeFactors.card :=
        (Finset.sum_image (f := fun e => (c:ℝ) ^ e.primeFactors.card) hinj).symm
    _ ≤ ∑ e ∈ d.divisors, (c:ℝ) ^ e.primeFactors.card := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro e he
          rw [Finset.mem_image] at he
          obtain ⟨S, hS, rfl⟩ := he
          rw [Nat.mem_divisors]
          exact ⟨(Finset.prod_dvd_prod_of_subset S d.primeFactors (fun p => p)
            (Finset.mem_powerset.mp hS)).trans (Nat.prod_primeFactors_dvd d), hd⟩
        · intro e _ _
          positivity

/-! ### Hyperbola-style swap for `∑_{d ≤ y} ∑_{ef = d}` -/

lemma sum_sum_divisorsAntidiagonal_le (F : ℕ → ℝ) (y : ℕ) :
    ∑ d ∈ Finset.Icc 1 y, ∑ p ∈ d.divisorsAntidiagonal, F p.2
      ≤ ∑ e ∈ Finset.Icc 1 y, ∑ f ∈ Finset.Icc 1 (y / e), F f := by
  classical
  have swap : ∑ d ∈ Finset.Icc 1 y, ∑ p ∈ d.divisorsAntidiagonal, F p.2
      = ∑ p ∈ (Finset.Icc 1 y ×ˢ Finset.Icc 1 y).filter (fun p : ℕ × ℕ => p.1 * p.2 ≤ y),
          ∑ _d ∈ ({p.1 * p.2} : Finset ℕ), F p.2 := by
    apply Finset.sum_comm'
    intro d p
    simp only [Nat.mem_divisorsAntidiagonal, Finset.mem_Icc, Finset.mem_filter,
      Finset.mem_product, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨hd1, hd2⟩, heq, hne⟩
      have hp1 : 1 ≤ p.1 := Nat.one_le_iff_ne_zero.mpr fun h => hne (by rw [← heq, h, zero_mul])
      have hp2 : 1 ≤ p.2 := Nat.one_le_iff_ne_zero.mpr fun h => hne (by rw [← heq, h, mul_zero])
      have hle1 : p.1 ≤ y :=
        le_trans (le_trans (le_mul_of_one_le_right (Nat.zero_le _) hp2) heq.le) hd2
      have hle2 : p.2 ≤ y :=
        le_trans (le_trans (le_mul_of_one_le_left (Nat.zero_le _) hp1) heq.le) hd2
      exact ⟨heq.symm, ⟨⟨hp1, hle1⟩, hp2, hle2⟩, le_of_eq_of_le heq hd2⟩
    · rintro ⟨hdeq, ⟨⟨hp11, hp12⟩, hp21, hp22⟩, hmul⟩
      subst hdeq
      refine ⟨⟨?_, hmul⟩, rfl, ?_⟩
      · exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
      · exact Nat.mul_ne_zero (by omega) (by omega)
  have hdisj : (↑(Finset.Icc 1 y) : Set ℕ).PairwiseDisjoint
      (fun e => ({e} : Finset ℕ) ×ˢ Finset.Icc 1 (y / e)) := by
    intro e1 _ e2 _ hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    rintro ⟨a, b⟩ h1 h2
    simp only [Finset.mem_product, Finset.mem_singleton] at h1 h2
    exact hne (h1.1.symm.trans h2.1)
  have hTU : (Finset.Icc 1 y ×ˢ Finset.Icc 1 y).filter (fun p : ℕ × ℕ => p.1 * p.2 ≤ y)
      = (Finset.Icc 1 y).biUnion (fun e => ({e} : Finset ℕ) ×ˢ Finset.Icc 1 (y / e)) := by
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_biUnion,
      Finset.mem_singleton]
    constructor
    · rintro ⟨⟨⟨ha1, ha2⟩, hb1, hb2⟩, hab⟩
      exact ⟨a, ⟨ha1, ha2⟩, rfl,
        hb1, (Nat.le_div_iff_mul_le (by omega : 0 < a)).mpr (by rw [mul_comm]; exact hab)⟩
    · rintro ⟨e, ⟨he1, he2⟩, rfl, hb1, hb2⟩
      have hba : b * a ≤ y := (Nat.le_div_iff_mul_le (by omega : 0 < a)).mp hb2
      exact ⟨⟨⟨he1, he2⟩, hb1, le_trans hb2 (Nat.div_le_self y a)⟩,
        by rw [mul_comm]; exact hba⟩
  rw [swap]
  simp only [Finset.sum_singleton]
  rw [hTU, Finset.sum_biUnion hdisj]
  apply le_of_eq
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Finset.sum_product]
  simp

/-! ### TauBound: `∑_{d ≤ y} c^{ω(d)} ≤ y (1 + log y)^{c-1}` -/

theorem sum_pow_primeFactors_le (c y : ℕ) (hc : 1 ≤ c) :
    ∑ d ∈ Finset.Icc 1 y, (c:ℝ) ^ (d.primeFactors.card) ≤ (y:ℝ) * (1 + Real.log y)^(c-1) := by
  induction c, hc using Nat.le_induction generalizing y with
  | base => simp [Nat.card_Icc]
  | succ c hc ih =>
    have step1 : ∑ d ∈ Finset.Icc 1 y, ((c:ℝ) + 1) ^ d.primeFactors.card
        ≤ ∑ d ∈ Finset.Icc 1 y, ∑ p ∈ d.divisorsAntidiagonal, (c:ℝ) ^ p.2.primeFactors.card := by
      apply Finset.sum_le_sum
      intro d hd
      rw [Finset.mem_Icc] at hd
      have hconv : ∑ p ∈ d.divisorsAntidiagonal, (c:ℝ) ^ p.2.primeFactors.card
          = ∑ e ∈ d.divisors, (c:ℝ) ^ e.primeFactors.card := by
        rw [Nat.sum_divisorsAntidiagonal (M := ℝ)
          (fun _ j => (c:ℝ) ^ j.primeFactors.card) (n := d)]
        exact Nat.sum_div_divisors (α := ℝ) d (fun e => (c:ℝ) ^ e.primeFactors.card)
      rw [hconv]
      exact pow_omega_le_sum_divisors c (by omega)
    have step2 := sum_sum_divisorsAntidiagonal_le (fun n => (c:ℝ) ^ n.primeFactors.card) y
    have step3 : ∑ e ∈ Finset.Icc 1 y, ∑ f ∈ Finset.Icc 1 (y / e), (c:ℝ) ^ f.primeFactors.card
        ≤ ∑ e ∈ Finset.Icc 1 y, (y:ℝ) / e * (1 + Real.log y) ^ (c - 1) := by
      apply Finset.sum_le_sum
      intro e he
      rw [Finset.mem_Icc] at he
      have h1 : (((y / e : ℕ)):ℝ) ≤ (y:ℝ) / e := Nat.cast_div_le
      have hde : 1 ≤ y / e := (Nat.one_le_div_iff (by omega)).mpr he.2
      have h2 : Real.log ((y / e : ℕ):ℝ) ≤ Real.log (y:ℝ) := by
        apply Real.log_le_log
        · exact_mod_cast hde
        · exact_mod_cast Nat.div_le_self y e
      have h3 : (0:ℝ) ≤ 1 + Real.log ((y / e : ℕ):ℝ) := one_add_log_natCast_nonneg _
      calc ∑ f ∈ Finset.Icc 1 (y / e), (c:ℝ) ^ f.primeFactors.card
          ≤ ((y / e : ℕ):ℝ) * (1 + Real.log ((y / e : ℕ):ℝ)) ^ (c - 1) := ih (y / e)
        _ ≤ (y:ℝ) / e * (1 + Real.log (y:ℝ)) ^ (c - 1) := by
            apply mul_le_mul h1 _ (pow_nonneg h3 _) (by positivity)
            exact pow_le_pow_left₀ h3 (by linarith) _
    have step5 : ∑ e ∈ Finset.Icc 1 y, (y:ℝ) / e * (1 + Real.log y) ^ (c - 1)
        ≤ (y:ℝ) * (1 + Real.log y) ^ c := by
      have h0 : (0:ℝ) ≤ 1 + Real.log y := one_add_log_natCast_nonneg y
      have hb : (0:ℝ) ≤ (y:ℝ) * (1 + Real.log y) ^ (c - 1) :=
        mul_nonneg (Nat.cast_nonneg y) (pow_nonneg h0 _)
      have hrw : ∑ e ∈ Finset.Icc 1 y, (y:ℝ) / e * (1 + Real.log y) ^ (c - 1)
          = (y:ℝ) * (1 + Real.log y) ^ (c - 1) * ∑ e ∈ Finset.Icc 1 y, ((e:ℝ))⁻¹ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [div_eq_mul_inv]
        ring
      rw [hrw]
      calc (y:ℝ) * (1 + Real.log y) ^ (c - 1) * ∑ e ∈ Finset.Icc 1 y, ((e:ℝ))⁻¹
          ≤ (y:ℝ) * (1 + Real.log y) ^ (c - 1) * (1 + Real.log y) :=
            mul_le_mul_of_nonneg_left (sum_inv_le_one_add_log y) hb
        _ = (y:ℝ) * (1 + Real.log y) ^ (c - 1 + 1) := by rw [pow_succ]; ring
        _ = (y:ℝ) * (1 + Real.log y) ^ c := by rw [Nat.sub_add_cancel hc]
    rw [Nat.add_sub_cancel]
    push_cast
    exact le_trans step1 (le_trans step2 (le_trans step3 step5))

/-! ### B.4: `∑_{h ≤ N} (h/φ(h))² ≤ 200 N` -/

/-- The weight `(2p-1)/(p-1)²`, so that `(p/(p-1))² = 1 + totientWeight p`. -/
noncomputable def totientWeight (p : ℕ) : ℝ := (2 * (p:ℝ) - 1) / ((p:ℝ) - 1) ^ 2

lemma totientWeight_nonneg {p : ℕ} (hp : 2 ≤ p) : 0 ≤ totientWeight p := by
  have h2 : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp
  unfold totientWeight
  apply div_nonneg
  · linarith
  · positivity

/-- Expansion of a product of `1 + g p` as a sum over subsets. -/
lemma prod_one_add_expand (P : Finset ℕ) (g : ℕ → ℝ) :
    ∏ p ∈ P, (1 + g p) = ∑ S ∈ P.powerset, ∏ p ∈ S, g p := by
  classical
  calc ∏ p ∈ P, (1 + g p)
      = ∏ p ∈ P, (g p + 1) := Finset.prod_congr rfl fun p _ => add_comm 1 (g p)
    _ = ∑ S ∈ P.powerset, (∏ p ∈ S, g p) * ∏ p ∈ P \ S, 1 := Finset.prod_add _ _ _
    _ = ∑ S ∈ P.powerset, ∏ p ∈ S, g p := by simp

/-- `(h/φ(h))² = ∏_{p ∣ h} (1 + (2p-1)/(p-1)²)`. -/
lemma totient_ratio_sq_eq_prod {h : ℕ} (hh : 1 ≤ h) :
    ((h:ℝ) / (Nat.totient h)) ^ 2 = ∏ p ∈ h.primeFactors, (1 + totientWeight p) := by
  have hφpos : 0 < Nat.totient h := Nat.totient_pos.mpr (by omega)
  have hφ : (0:ℝ) < (Nat.totient h : ℝ) := by exact_mod_cast hφpos
  have hfac : ∀ p ∈ h.primeFactors, (2:ℝ) ≤ (p:ℝ) := fun p hp => by
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
  have hprodpos : (0:ℝ) < ∏ p ∈ h.primeFactors, ((p:ℝ) - 1) := by
    apply Finset.prod_pos
    intro p hp
    have := hfac p hp
    linarith
  have hkeyR : (Nat.totient h : ℝ) * ∏ p ∈ h.primeFactors, (p:ℝ)
      = (h:ℝ) * ∏ p ∈ h.primeFactors, ((p:ℝ) - 1) := by
    have hcast : ∏ p ∈ h.primeFactors, ((p:ℝ) - 1)
        = ((∏ p ∈ h.primeFactors, (p - 1) : ℕ) : ℝ) := by
      push_cast
      refine Finset.prod_congr rfl fun p hp => ?_
      rw [Nat.cast_pred (Nat.prime_of_mem_primeFactors hp).pos]
    have hcast2 : ∏ p ∈ h.primeFactors, (p:ℝ) = ((∏ p ∈ h.primeFactors, p : ℕ) : ℝ) := by
      push_cast
      rfl
    rw [hcast, hcast2]
    exact_mod_cast congrArg (Nat.cast (R := ℝ)) (Nat.totient_mul_prod_primeFactors h)
  have hratio : (h:ℝ) / (Nat.totient h : ℝ)
      = ∏ p ∈ h.primeFactors, ((p:ℝ) / ((p:ℝ) - 1)) := by
    rw [Finset.prod_div_distrib]
    rw [div_eq_div_iff hφ.ne' hprodpos.ne']
    linear_combination -hkeyR
  rw [hratio, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun p hp => ?_
  have h2 := hfac p hp
  have hne : (p:ℝ) - 1 ≠ 0 := by linarith
  unfold totientWeight
  field_simp
  ring

/-- Swap the sum over `h` and over subsets of prime factors of `h`. -/
lemma totient_powerset_swap (N : ℕ) (g : Finset ℕ → ℝ) :
    ∑ h ∈ Finset.Icc 1 N, ∑ S ∈ h.primeFactors.powerset, g S
      = ∑ S ∈ ((Finset.Icc 1 N).filter Nat.Prime).powerset,
          ∑ _ ∈ (Finset.Icc 1 N).filter (fun h => (∏ p ∈ S, p) ∣ h), g S := by
  classical
  apply Finset.sum_comm'
  intro h S
  simp only [Finset.mem_Icc, Finset.mem_powerset, Finset.mem_filter]
  constructor
  · rintro ⟨⟨h1, h2⟩, hS⟩
    refine ⟨⟨⟨h1, h2⟩, ?_⟩, ?_⟩
    · exact (Finset.prod_dvd_prod_of_subset S h.primeFactors (fun p => p) hS).trans
        (Nat.prod_primeFactors_dvd h)
    · intro p hp
      have hp' := hS hp
      rw [Nat.mem_primeFactors] at hp'
      obtain ⟨hpp, hpd, -⟩ := hp'
      rw [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨hpp.one_lt.le, (Nat.le_of_dvd (by omega) hpd).trans h2⟩, hpp⟩
  · rintro ⟨⟨⟨h1, h2⟩, hdvd⟩, hS⟩
    refine ⟨⟨h1, h2⟩, ?_⟩
    intro p hp
    have hpP := hS hp
    rw [Finset.mem_filter] at hpP
    rw [Nat.mem_primeFactors]
    exact ⟨hpP.2, dvd_trans (Finset.dvd_prod_of_mem (fun p => p) hp) hdvd, by omega⟩

lemma exp_four_le_55 : Real.exp 4 ≤ 55 := by
  have h1 : Real.exp 1 ≤ 2.7182818286 := Real.exp_one_lt_d9.le
  have h4 : Real.exp 4 = Real.exp 1 ^ 4 := by
    rw [Real.exp_one_pow]
    norm_num
  rw [h4]
  calc Real.exp 1 ^ 4 ≤ (2.7182818286:ℝ) ^ 4 :=
        pow_le_pow_left₀ (Real.exp_pos 1).le h1 4
    _ ≤ 55 := by norm_num

theorem sum_totient_ratio_sq_le (N : ℕ) :
    ∑ h ∈ Finset.Icc 1 N, ((h:ℝ) / (Nat.totient h))^2 ≤ 200 * N := by
  classical
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  have hN0 : (0:ℝ) ≤ (N:ℝ) := Nat.cast_nonneg N
  set P := (Finset.Icc 1 N).filter Nat.Prime with hPdef
  have hPprime : ∀ p ∈ P, Nat.Prime p := fun p hp => (Finset.mem_filter.mp hp).2
  have hSprime : ∀ S ∈ P.powerset, ∀ p ∈ S, Nat.Prime p := fun S hS p hp =>
    hPprime p (Finset.mem_powerset.mp hS hp)
  have hwtS : ∀ S ∈ P.powerset, 0 ≤ ∏ p ∈ S, totientWeight p := fun S hS =>
    Finset.prod_nonneg fun p hp => totientWeight_nonneg (hSprime S hS p hp).two_le
  -- the exponent bound
  have hexp4 : ∑ p ∈ P, totientWeight p / (p:ℝ) ≤ 4 := by
    have hstep : ∀ p ∈ P, totientWeight p / (p:ℝ) ≤ 2 / (((p:ℝ) - 1) ^ 2) := by
      intro p hp
      have h2 : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast (hPprime p hp).two_le
      have hp1 : (0:ℝ) < (p:ℝ) - 1 := by linarith
      have hp0 : (0:ℝ) < (p:ℝ) := by linarith
      unfold totientWeight
      rw [div_div, div_le_div_iff₀ (mul_pos (pow_pos hp1 2) hp0) (pow_pos hp1 2)]
      nlinarith [sq_nonneg ((p:ℝ) - 1)]
    calc ∑ p ∈ P, totientWeight p / (p:ℝ)
        ≤ ∑ p ∈ P, 2 / (((p:ℝ) - 1) ^ 2) := Finset.sum_le_sum hstep
      _ ≤ ∑ n ∈ Finset.Icc 2 N, 2 / (((n:ℝ) - 1) ^ 2) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro p hp
            rw [Finset.mem_Icc]
            exact ⟨(hPprime p hp).two_le, (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2⟩
          · intro n _ _
            positivity
      _ ≤ 4 - 4 / (N:ℝ) := sum_two_div_sq_le N hN
      _ ≤ 4 := by
          have : (0:ℝ) ≤ 4 / (N:ℝ) := by positivity
          linarith
  -- rewrite the summand and swap
  have hstep1 : ∑ h ∈ Finset.Icc 1 N, ((h:ℝ) / (Nat.totient h)) ^ 2
      = ∑ S ∈ P.powerset, ∑ h ∈ (Finset.Icc 1 N).filter (fun h => (∏ p ∈ S, p) ∣ h),
          ∏ p ∈ S, totientWeight p := by
    rw [← totient_powerset_swap N (fun S => ∏ p ∈ S, totientWeight p)]
    refine Finset.sum_congr rfl fun h hh => ?_
    rw [totient_ratio_sq_eq_prod (Finset.mem_Icc.mp hh).1, prod_one_add_expand]
  -- count multiples of ∏ S
  have hcount : ∀ S ∈ P.powerset,
      ∑ h ∈ (Finset.Icc 1 N).filter (fun h => (∏ p ∈ S, p) ∣ h), ∏ p ∈ S, totientWeight p
        = ((N / ∏ p ∈ S, p : ℕ) : ℝ) * ∏ p ∈ S, totientWeight p := by
    intro S _
    rw [Finset.sum_const]
    rw [show Finset.Icc 1 N = Finset.Ioc 0 N from rfl, Nat.Ioc_filter_dvd_card_eq_div]
    rw [nsmul_eq_mul]
  rw [hstep1, Finset.sum_congr rfl hcount]
  calc ∑ S ∈ P.powerset, ((N / ∏ p ∈ S, p : ℕ) : ℝ) * ∏ p ∈ S, totientWeight p
      ≤ ∑ S ∈ P.powerset, (N:ℝ) * ∏ p ∈ S, (totientWeight p / (p:ℝ)) := by
        apply Finset.sum_le_sum
        intro S hS
        have h1 : ((N / ∏ p ∈ S, p : ℕ) : ℝ) ≤ (N:ℝ) / ((∏ p ∈ S, p : ℕ) : ℝ) :=
          Nat.cast_div_le
        calc ((N / ∏ p ∈ S, p : ℕ) : ℝ) * ∏ p ∈ S, totientWeight p
            ≤ (N:ℝ) / ((∏ p ∈ S, p : ℕ) : ℝ) * ∏ p ∈ S, totientWeight p :=
              mul_le_mul_of_nonneg_right h1 (hwtS S hS)
          _ = (N:ℝ) * ∏ p ∈ S, (totientWeight p / (p:ℝ)) := by
              rw [Nat.cast_prod, Finset.prod_div_distrib]
              ring
    _ = (N:ℝ) * ∑ S ∈ P.powerset, ∏ p ∈ S, (totientWeight p / (p:ℝ)) := by
        rw [Finset.mul_sum]
    _ = (N:ℝ) * ∏ p ∈ P, (1 + totientWeight p / (p:ℝ)) := by
        rw [prod_one_add_expand]
    _ ≤ (N:ℝ) * ∏ p ∈ P, Real.exp (totientWeight p / (p:ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ hN0
        apply Finset.prod_le_prod
        · intro p hp
          have hw := totientWeight_nonneg (hPprime p hp).two_le
          have hp0 : (0:ℝ) < (p:ℝ) := by exact_mod_cast (hPprime p hp).pos
          positivity
        · intro p hp
          have := Real.add_one_le_exp (totientWeight p / (p:ℝ))
          linarith
    _ = (N:ℝ) * Real.exp (∑ p ∈ P, totientWeight p / (p:ℝ)) := by
        rw [Real.exp_sum]
    _ ≤ (N:ℝ) * Real.exp 4 :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp4) hN0
    _ ≤ 200 * (N:ℝ) := by
        nlinarith [exp_four_le_55, hN0, Real.exp_pos (4:ℝ)]

end Erdos884
