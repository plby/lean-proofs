import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Order.Interval.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic
import ErdosProblems.Erdos387.AnalyticInputs
import ErdosProblems.Erdos387.CoverLemma

/-!
# BNPZ cover infrastructure before the uniform analytic input

This is the axiom-free prefix of the public `CoverBPZ.lean` development,
ported to Lean/Mathlib 4.33.  It contains the cover/certificate structures and
all construction and arithmetic lemmas preceding
`wideCoverBuildData_exists`, the first theorem that invokes the presently
missing growing-parameter shifted Siegel--Walfisz estimate.
-/

open scoped BigOperators
open Real Classical
open Erdos387.ANT Erdos387

namespace Erdos387.CoverBPZ




open Finset

theorem sum_eq_sum_card_ge {ι : Type*} [DecidableEq ι] (s : Finset ι) (E : ι → ℕ) (U : ℕ)
    (hU : ∀ i ∈ s, E i ≤ U) :
    (∑ i ∈ s, E i) = ∑ u ∈ Icc 1 U, (s.filter (fun i => u ≤ E i)).card := by
  classical
  revert hU
  refine Finset.induction_on s ?_ ?_
  · intro _; simp
  · intro x t hxi ih hU'
    have hU'' : ∀ i ∈ t, E i ≤ U := fun i hi => hU' i (mem_insert_of_mem hi)
    have hxU : E x ≤ U := hU' x (mem_insert_self x t)
    rw [Finset.sum_insert hxi, ih hU'']
    have step : ∀ u ∈ Icc 1 U,
        ((insert x t).filter (fun i => u ≤ E i)).card =
          (t.filter (fun i => u ≤ E i)).card + (if u ≤ E x then 1 else 0) := by
      intro u _
      rw [Finset.filter_insert]
      by_cases hu : u ≤ E x
      · simp only [hu, if_true]
        rw [Finset.card_insert_of_notMem]
        exact fun h => hxi (Finset.mem_of_mem_filter _ h)
      · simp [hu]
    rw [Finset.sum_congr rfl step, Finset.sum_add_distrib]
    have hcount : (∑ u ∈ Icc 1 U, (if u ≤ E x then 1 else 0)) = E x := by
      have h_sum_eq : (∑ u ∈ Icc 1 U, (if u ≤ E x then (1:ℕ) else 0))
            = ((Icc 1 U).filter (fun u => u ≤ E x)).card := by
        rw [Finset.card_filter]
      rw [h_sum_eq]
      have h_eq : (Icc 1 U).filter (fun u => u ≤ E x) = Icc 1 (E x) := by
        ext u
        simp only [Finset.mem_filter, mem_Icc]
        refine ⟨fun ⟨⟨h1, _⟩, h2⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨⟨h1, h2.trans hxU⟩, h2⟩⟩
      rw [h_eq, Nat.card_Icc]
      omega
    omega

theorem padicValNat_factorial_eq_sum (p k : ℕ) [hp : Fact p.Prime] :
    padicValNat p k.factorial = ∑ u ∈ Ico 1 (Nat.log p k + 1), k / p^u := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk; simp
  exact padicValNat_factorial (Nat.lt_succ_of_le (le_refl _))

def liftAbove (p u a : ℕ) : ℕ := p^u - p + a

theorem liftAbove_pos {p u a : ℕ} (hp : 1 < p) (ha : 1 ≤ a) (hu : 1 ≤ u) :
    0 < liftAbove p u a := by
  unfold liftAbove
  omega

theorem liftAbove_lt {p u a : ℕ} (hp : 1 < p) (ha : 1 ≤ a) (haq : a < p) (hu : 1 ≤ u) :
    liftAbove p u a < p^u := by
  unfold liftAbove
  have hple : p ≤ p^u := by
    have h := Nat.pow_le_pow_right (le_of_lt hp) hu
    simpa using h
  omega

theorem liftAbove_mod_p (p u a : ℕ) (hp : 1 < p) (ha : a < p) (hu : 1 ≤ u) :
    liftAbove p u a % p = a := by
  unfold liftAbove
  have hple : p ≤ p^u := by
    have h := Nat.pow_le_pow_right (le_of_lt hp) hu
    simpa using h
  have hpdvd : p ∣ p^u := dvd_pow_self p (by omega : u ≠ 0)
  have hpdvd_sub : p ∣ p^u - p := Nat.dvd_sub hpdvd dvd_rfl
  obtain ⟨c, hc⟩ := hpdvd_sub
  rw [hc, Nat.add_comm, Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt ha

theorem liftAbove_nested (p u a : ℕ) (hp : 1 ≤ p) :
    liftAbove p (u+1) a % p^u = liftAbove p u a % p^u := by
  unfold liftAbove
  rcases Nat.eq_zero_or_pos u with hu0 | hu
  · subst hu0
    simp [Nat.mod_one]
  have hple_u : p ≤ p^u := by
    have h := Nat.pow_le_pow_right hp hu
    simpa using h
  have hpow : p^(u+1) = p^u * p := by ring
  have hpu_pu : p^u ≤ p^u * p := by
    calc p^u = p^u * 1 := (Nat.mul_one _).symm
      _ ≤ p^u * p := Nat.mul_le_mul_left _ hp
  have hpow_ge_pu : p^u ≤ p^(u+1) := hpow ▸ hpu_pu
  have hple_u1 : p ≤ p^(u+1) := le_trans hple_u hpow_ge_pu
  have h_mul_eq : p^u * (p - 1) = p^u * p - p^u := by
    rw [Nat.mul_sub_one]
  have hdiff : p^(u+1) - p + a = p^u * (p - 1) + (p^u - p + a) := by
    rw [hpow, h_mul_eq]
    omega
  rw [hdiff, Nat.add_comm, Nat.add_mul_mod_self_left]

theorem liftAbove_above_kModPow {p k u a : ℕ}
    (hp : 1 < p) (hpk : p ∣ k) (hpos : 1 ≤ a) (hlt : a < p) (hu : 1 ≤ u) :
    k % p^u < liftAbove p u a := by
  unfold liftAbove
  have hp_pos : 0 < p := by omega
  have hpu_pos : 0 < p^u := Nat.pow_pos hp_pos
  have hple : p ≤ p^u := by
    have h := Nat.pow_le_pow_right (le_of_lt hp) hu
    simpa using h
  have hkmod_lt : k % p^u < p^u := Nat.mod_lt _ hpu_pos
  have hp_dvd_pu : p ∣ p^u := dvd_pow_self p (by omega : u ≠ 0)
  have hp_dvd_kmod : p ∣ k % p^u := by
    have hk_split : p^u * (k / p^u) + k % p^u = k := Nat.div_add_mod k (p^u)
    have hp_dvd_pumul : p ∣ p^u * (k / p^u) := Dvd.dvd.mul_right hp_dvd_pu _
    have hle : p^u * (k / p^u) ≤ k := Nat.le.intro hk_split
    have hk_eq : k % p^u = k - p^u * (k / p^u) := by omega
    rw [hk_eq]
    exact Nat.dvd_sub hpk hp_dvd_pumul
  obtain ⟨m, hm⟩ := hp_dvd_kmod
  have hpu_eq : p^u = p^(u-1) * p := by
    have hu_eq : u = (u-1) + 1 := by omega
    conv_lhs => rw [hu_eq]
    ring
  have hpu_eq' : p^u = p * p^(u-1) := by rw [hpu_eq, Nat.mul_comm]
  have hpu1_pos : 0 < p^(u-1) := Nat.pow_pos hp_pos
  have hm_lt : m < p^(u-1) := by
    have hlt2 : p * m < p * p^(u-1) := by
      calc p * m = k % p^u := hm.symm
        _ < p^u := hkmod_lt
        _ = p * p^(u-1) := hpu_eq'
    exact Nat.lt_of_mul_lt_mul_left hlt2
  have hm_le : m ≤ p^(u-1) - 1 := by omega
  have hcalc : p * m ≤ p * (p^(u-1) - 1) := Nat.mul_le_mul_left p hm_le
  have hpu_sub : p * (p^(u-1) - 1) = p^u - p := by
    rw [Nat.mul_sub_one, ← hpu_eq']
  have hkmod_le : k % p^u ≤ p^u - p := by
    rw [hpu_sub] at hcalc
    rw [hm]
    exact hcalc
  omega



theorem prod_eq_of_factorization_eq {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hf : ∀ p, a.factorization p = b.factorization p) :
    a = b := by
  have h_eq : a.factorization = b.factorization := Finsupp.ext hf
  exact (Nat.factorization_inj (by simp [ha.ne']) (by simp [hb.ne'])) h_eq

theorem prod_B_eq_factorial {k : ℕ} (B : Fin k → ℕ) (hpos : ∀ j, 0 < B j)
    (hval : ∀ p, p.Prime →
        (∏ j, B j).factorization p = k.factorial.factorization p) :
    (∏ j, B j) = k.factorial := by
  have h_prod_pos : 0 < ∏ j, B j := Finset.prod_pos (fun j _ => hpos j)
  have h_fact_pos : 0 < k.factorial := Nat.factorial_pos k
  refine prod_eq_of_factorization_eq h_prod_pos h_fact_pos ?_
  intro p
  by_cases hp : p.Prime
  · exact hval p hp
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]



open Finset

theorem card_Ioc_mod_eq_aux (q k a : ℕ) (hq : 1 ≤ q) (ha0 : 0 < a) (haq : a < q)
    (hak : k % q < a) :
    ((Ioc 0 k).filter (· % q = a)).card = k / q := by
  classical
  set t := k / q with ht_def
  let f : ℕ → ℕ := fun ℓ => a + ℓ * q
  have hq_pos : 0 < q := hq
  have f_inj : Function.Injective f := by
    intro x y hxy
    have : x * q = y * q := by
      have := hxy
      simp only [f] at this
      omega
    exact Nat.eq_of_mul_eq_mul_right hq_pos this
  let S : Finset ℕ := (range t).image f
  have hS_card : S.card = t := by
    rw [Finset.card_image_of_injective _ f_inj, card_range]
  have hk_eq : k = t * q + k % q := (Nat.div_add_mod k q).symm |>.trans (by ring)
  have hr_lt : k % q < q := Nat.mod_lt _ hq_pos
  have hS_eq : S = (Ioc 0 k).filter (· % q = a) := by
    ext n
    simp only [S, mem_image, mem_range, mem_filter, mem_Ioc, f]
    constructor
    · rintro ⟨ℓ, hℓ, rfl⟩
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · positivity
      · have hℓ_le : ℓ + 1 ≤ t := hℓ
        have hmul : (ℓ + 1) * q ≤ t * q := Nat.mul_le_mul_right q hℓ_le
        have : a + ℓ * q < (ℓ + 1) * q := by
          have : a < q := haq
          have hexpand : (ℓ + 1) * q = ℓ * q + q := by ring
          omega
        omega
      · rw [Nat.add_mul_mod_self_right]
        exact Nat.mod_eq_of_lt haq
    · rintro ⟨⟨hn0, hnk⟩, hnmod⟩
      have hna : a ≤ n := by
        rcases Nat.lt_or_ge n a with h | h
        · exfalso
          have hnq : n % q = n := Nat.mod_eq_of_lt (lt_of_lt_of_le h haq.le)
          omega
        · exact h
      have hn_div : n / q * q + n % q = n := by
        have h1 : q * (n / q) + n % q = n := Nat.div_add_mod n q
        have h2 : q * (n / q) = n / q * q := Nat.mul_comm q (n / q)
        omega
      refine ⟨n / q, ?_, ?_⟩
      · by_contra hge
        push_neg at hge
        have hmul : t * q ≤ (n / q) * q := Nat.mul_le_mul_right q hge
        have hreach : a + t * q ≤ n := by omega
        have htq_a : t * q + a > t * q + k % q := by omega
        have : t * q + a > k := by rw [hk_eq]; omega
        omega
      · omega
  rw [← hS_eq, hS_card]

theorem card_Icc_mod_eq {q k a : ℕ} (hq : 1 ≤ q) (ha0 : 0 < a) (haq : a < q)
    (hak : k % q < a) :
    ((Icc 1 k).filter (· % q = a)).card = k / q := by
  classical
  have h_eq : (Icc 1 k) = (Ioc 0 k) := by
    ext x
    simp [Nat.lt_iff_add_one_le]
  rw [h_eq]
  exact card_Ioc_mod_eq_aux q k a hq ha0 haq hak

structure GlobalResidueCertificate (m k : ℕ) where
  B : Fin k → ℕ
  Mk : ℕ
  R : ℤ
  hMk_pos : 0 < Mk
  hB_pos : ∀ j, 0 < B j
  hB_ge : ∀ j, m ≤ B j
  hB_dvd_Mk : ∀ j, B j ∣ Mk
  hMk_overB_p :
    ∀ (j : Fin k) (p : ℕ), p.Prime → p ≤ k → (p * B j) ∣ Mk
  hMk_smooth : ∀ p : ℕ, p.Prime → p ∣ Mk → p ≤ k
  hprod_B : ∏ j, B j = k.factorial
  hR_div :
    ∀ j : Fin k, (B j : ℤ) ∣ R - (k : ℤ) + ((j.val : ℤ) + 1)
  hPairwise_coprime :
    ∀ (n : ℕ) (i j : Fin k), i ≠ j →
      Int.gcd
        ((R + (Mk : ℤ) * n - (k : ℤ) + ((i.val : ℤ) + 1)) / (B i : ℤ))
        ((R + (Mk : ℤ) * n - (k : ℤ) + ((j.val : ℤ) + 1)) / (B j : ℤ)) = 1

theorem exists_N₀_via_CRT_cert
    {m k : ℕ} (cert : GlobalResidueCertificate m k) :
    ∃ N₀ : ℤ,
      (∀ (n : ℕ) (j : Fin k),
          (cert.B j : ℤ) ∣ (N₀ + (cert.Mk : ℤ) * n - (k : ℤ) + ((j.val : ℤ) + 1))) ∧
      (∀ n : ℕ, 0 < N₀ + (cert.Mk : ℤ) * n) ∧
      (∀ n : ℕ, k < (N₀ + (cert.Mk : ℤ) * n).toNat) ∧
      (∀ (n : ℕ) (i j : Fin k), i ≠ j →
        Int.gcd
          ((N₀ + (cert.Mk : ℤ) * n - (k : ℤ) + ((i.val : ℤ) + 1)) / (cert.B i : ℤ))
          ((N₀ + (cert.Mk : ℤ) * n - (k : ℤ) + ((j.val : ℤ) + 1)) / (cert.B j : ℤ)) = 1) := by
  set T : ℕ := Int.natAbs cert.R + k + 1 with hT_def
  set N₀ : ℤ := cert.R + (cert.Mk : ℤ) * (T : ℤ) with hN₀_def
  refine ⟨N₀, ?_, ?_, ?_, ?_⟩
  · intro n j
    rcases cert.hR_div j with ⟨q, hq⟩
    rcases cert.hB_dvd_Mk j with ⟨c, hc⟩
    refine ⟨q + (c : ℤ) * ((T : ℤ) + (n : ℤ)), ?_⟩
    have hMkeq : (cert.Mk : ℤ) = (cert.B j : ℤ) * (c : ℤ) := by exact_mod_cast hc
    rw [hN₀_def, hMkeq]
    linear_combination hq
  · intro n
    have hMkz : (0 : ℤ) < (cert.Mk : ℤ) := by exact_mod_cast cert.hMk_pos
    have hT_eq : (T : ℤ) = (Int.natAbs cert.R : ℤ) + (k : ℤ) + 1 := by
      rw [hT_def]; push_cast; ring
    have hk_nn : (0 : ℤ) ≤ (k : ℤ) := by exact_mod_cast Nat.zero_le k
    have hnatAbs_nn : (0 : ℤ) ≤ (Int.natAbs cert.R : ℤ) := by exact_mod_cast Nat.zero_le _
    have hMkz_one : (1 : ℤ) ≤ (cert.Mk : ℤ) := hMkz
    have hT_pos : (1 : ℤ) ≤ (T : ℤ) := by rw [hT_eq]; linarith
    have hnn_n : (0 : ℤ) ≤ (n : ℤ) := by exact_mod_cast Nat.zero_le n
    have hMk_n_nn : (0 : ℤ) ≤ (cert.Mk : ℤ) * (n : ℤ) := mul_nonneg hMkz.le hnn_n
    have hR_lb : -((Int.natAbs cert.R : ℤ)) ≤ cert.R := by
      have h1 : (Int.natAbs (-cert.R) : ℤ) = (Int.natAbs cert.R : ℤ) := by
        simp [Int.natAbs_neg]
      have h2 : -cert.R ≤ (Int.natAbs (-cert.R) : ℤ) := Int.le_natAbs
      linarith
    have hMkT_ge : (Int.natAbs cert.R : ℤ) + 1 ≤ (cert.Mk : ℤ) * (T : ℤ) := by
      have h1 : (Int.natAbs cert.R : ℤ) + 1 ≤ (T : ℤ) := by linarith
      nlinarith
    have hN₀_pos : 0 < N₀ := by rw [hN₀_def]; linarith
    linarith
  · intro n
    have hMkz : (0 : ℤ) < (cert.Mk : ℤ) := by exact_mod_cast cert.hMk_pos
    have hT_eq : (T : ℤ) = (Int.natAbs cert.R : ℤ) + (k : ℤ) + 1 := by
      rw [hT_def]; push_cast; ring
    have hnn_n : (0 : ℤ) ≤ (n : ℤ) := by exact_mod_cast Nat.zero_le n
    have hk_nn : (0 : ℤ) ≤ (k : ℤ) := by exact_mod_cast Nat.zero_le k
    have hnatAbs_nn : (0 : ℤ) ≤ (Int.natAbs cert.R : ℤ) := by exact_mod_cast Nat.zero_le _
    have hMk_n_nn : (0 : ℤ) ≤ (cert.Mk : ℤ) * (n : ℤ) := mul_nonneg hMkz.le hnn_n
    have hR_lb : -((Int.natAbs cert.R : ℤ)) ≤ cert.R := by
      have h1 : (Int.natAbs (-cert.R) : ℤ) = (Int.natAbs cert.R : ℤ) := by
        simp [Int.natAbs_neg]
      have h2 : -cert.R ≤ (Int.natAbs (-cert.R) : ℤ) := Int.le_natAbs
      linarith
    have hT_ge_k1 : (k : ℤ) + 1 + (Int.natAbs cert.R : ℤ) ≤ (T : ℤ) := by
      rw [hT_eq]; linarith
    have hMkT_ge : (k : ℤ) + 1 + (Int.natAbs cert.R : ℤ) ≤ (cert.Mk : ℤ) * (T : ℤ) := by
      nlinarith
    have hk_lt : (k : ℤ) < N₀ + (cert.Mk : ℤ) * (n : ℤ) := by rw [hN₀_def]; linarith
    have hpos : 0 ≤ N₀ + (cert.Mk : ℤ) * (n : ℤ) := by linarith
    have htoNat : ((N₀ + (cert.Mk : ℤ) * n).toNat : ℤ) = N₀ + (cert.Mk : ℤ) * (n : ℤ) :=
      Int.toNat_of_nonneg hpos
    have h_cast : (k : ℤ) < ((N₀ + (cert.Mk : ℤ) * n).toNat : ℤ) := by rw [htoNat]; exact hk_lt
    exact_mod_cast h_cast
  · intro n i j hij
    have key :
        N₀ + (cert.Mk : ℤ) * (n : ℤ) = cert.R + (cert.Mk : ℤ) * ((T : ℤ) + (n : ℤ)) := by
      rw [hN₀_def]; ring
    have hT_n_nat : ∃ n' : ℕ, (n' : ℤ) = (T : ℤ) + (n : ℤ) :=
      ⟨T + n, by push_cast; ring⟩
    obtain ⟨n', hn'⟩ := hT_n_nat
    have h_eq_i :
        N₀ + (cert.Mk : ℤ) * (n : ℤ) - (k : ℤ) + ((i.val : ℤ) + 1)
          = cert.R + (cert.Mk : ℤ) * (n' : ℤ) - (k : ℤ) + ((i.val : ℤ) + 1) := by
      rw [key, hn']
    have h_eq_j :
        N₀ + (cert.Mk : ℤ) * (n : ℤ) - (k : ℤ) + ((j.val : ℤ) + 1)
          = cert.R + (cert.Mk : ℤ) * (n' : ℤ) - (k : ℤ) + ((j.val : ℤ) + 1) := by
      rw [key, hn']
    rw [h_eq_i, h_eq_j]
    exact cert.hPairwise_coprime n' i j hij



open Finset

theorem valuation_sum_non_excess_lift (p k : ℕ) [hp : Fact p.Prime] (hpk_dvd : p ∣ k)
    (a : ℕ) (hapos : 1 ≤ a) (halt : a < p) (hk_pos : 0 < k) :
    ∀ u ∈ Icc 1 (Nat.log p k),
      ((Icc 1 k).filter (· % p^u = liftAbove p u a)).card = k / p^u := by
  intro u hu
  rw [mem_Icc] at hu
  have hu_pos : 1 ≤ u := hu.1
  have hp_prime : p.Prime := hp.out
  have hp_pos : 1 ≤ p := hp_prime.one_lt.le
  have hp_lt : 1 < p := hp_prime.one_lt
  have hpu_pos : 0 < p^u := Nat.pow_pos hp_prime.pos
  have hpu_ge_1 : 1 ≤ p^u := hpu_pos
  have h_lift_pos : 0 < liftAbove p u a := liftAbove_pos hp_lt hapos hu_pos
  have h_lift_lt : liftAbove p u a < p^u := liftAbove_lt hp_lt hapos halt hu_pos
  have h_lift_above : k % p^u < liftAbove p u a :=
    liftAbove_above_kModPow hp_lt hpk_dvd hapos halt hu_pos
  exact card_Icc_mod_eq hpu_ge_1 h_lift_pos h_lift_lt h_lift_above



open Finset

def baseK (m : ℕ) : ℕ := 2 * m * m

def smallSet (m : ℕ) : Finset ℕ := Finset.Ioo 0 m

def donorSet (m : ℕ) : Finset ℕ :=
  (Finset.Ioo 0 m).image (fun t => m * (m + t))

def baseBAt (m x : ℕ) : ℕ :=
  if x ∈ smallSet m then
    x * m
  else if x ∈ donorSet m then
    x / m
  else
    x

theorem baseBAt_small (m x : ℕ) (hx : x ∈ smallSet m) :
    baseBAt m x = x * m := by
  unfold baseBAt; simp [hx]

theorem baseBAt_donor (m t : ℕ) (hm : 1 ≤ m) (ht1 : 1 ≤ t) (htm : t < m) :
    baseBAt m (m * (m + t)) = m + t := by
  have hmpos : 0 < m := hm
  have hge : m ≤ m * (m + t) := by
    have : 1 * m ≤ (m + t) * m := Nat.mul_le_mul_right m (by omega)
    nlinarith
  have hsmall_not : m * (m + t) ∉ smallSet m := by
    intro h
    simp [smallSet, Finset.mem_Ioo] at h
    omega
  have hdon : m * (m + t) ∈ donorSet m := by
    unfold donorSet
    rw [Finset.mem_image]
    exact ⟨t, by simp only [mem_Ioo]; exact ⟨ht1, htm⟩, rfl⟩
  unfold baseBAt
  simp only [hsmall_not, ↓reduceIte, hdon]
  rw [Nat.mul_div_cancel_left _ hmpos]

theorem baseBAt_other (m x : ℕ) (hnotS : x ∉ smallSet m) (hnotD : x ∉ donorSet m) :
    baseBAt m x = x := by
  unfold baseBAt
  simp [hnotS, hnotD]

theorem baseBAt_ge_m_small (m x : ℕ) (hm : 3 ≤ m) (hx : x ∈ smallSet m) :
    m ≤ baseBAt m x := by
  rw [baseBAt_small m x hx]
  simp [smallSet, Finset.mem_Ioo] at hx
  have : 1 * m ≤ x * m := Nat.mul_le_mul_right m hx.1
  simpa using this

theorem baseBAt_ge_m_donor (m t : ℕ) (hm : 3 ≤ m) (ht1 : 1 ≤ t) (htm : t < m) :
    m ≤ baseBAt m (m * (m + t)) := by
  rw [baseBAt_donor m t (by omega) ht1 htm]
  omega

theorem baseBAt_ge_m_other (m x : ℕ) (hm : 3 ≤ m) (hxpos : 1 ≤ x)
    (hnotS : x ∉ smallSet m) (hnotD : x ∉ donorSet m) :
    m ≤ baseBAt m x := by
  rw [baseBAt_other m x hnotS hnotD]
  simp [smallSet, Finset.mem_Ioo] at hnotS
  omega

theorem baseBAt_ge_m (m x : ℕ) (hm : 3 ≤ m) (hxpos : 1 ≤ x) :
    m ≤ baseBAt m x := by
  by_cases hS : x ∈ smallSet m
  · exact baseBAt_ge_m_small m x hm hS
  · by_cases hD : x ∈ donorSet m
    · simp [donorSet, Finset.mem_image, Finset.mem_Ioo] at hD
      obtain ⟨t, ⟨ht1, htm⟩, rfl⟩ := hD
      exact baseBAt_ge_m_donor m t hm ht1 htm
    · exact baseBAt_ge_m_other m x hm hxpos hS hD

theorem smallSet_subset_baseK (m : ℕ) (hm : 3 ≤ m) :
    smallSet m ⊆ Finset.Icc 1 (baseK m) := by
  intro x hx
  simp only [smallSet, mem_Ioo] at hx
  simp only [mem_Icc, baseK]
  refine ⟨hx.1, ?_⟩
  nlinarith

theorem donorSet_subset_baseK (m : ℕ) (hm : 3 ≤ m) :
    donorSet m ⊆ Finset.Icc 1 (baseK m) := by
  intro y hy
  rw [donorSet] at hy
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hy
  obtain ⟨ht0, htm⟩ := Finset.mem_Ioo.mp ht
  rw [Finset.mem_Icc]
  constructor
  · have hm0 : 0 < m := by omega
    exact Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero (Nat.ne_of_gt hm0) (Nat.ne_of_gt (Nat.add_pos_left hm0 t)))
  · have hmt : m * t ≤ m * m := Nat.mul_le_mul_left m (Nat.le_of_lt htm)
    calc
      m * (m + t) = m * m + m * t := Nat.mul_add m m t
      _ ≤ m * m + m * m := Nat.add_le_add_left hmt (m * m)
      _ = baseK m := by simp [baseK, two_mul, Nat.add_mul]

theorem small_donor_disjoint (m : ℕ) (hm : 3 ≤ m) :
    Disjoint (smallSet m) (donorSet m) := by
  rw [Finset.disjoint_iff_ne]
  intro x hx y hy
  rw [smallSet, Finset.mem_Ioo] at hx
  rw [donorSet, Finset.mem_image] at hy
  obtain ⟨t, ht, rfl⟩ := hy
  rw [Finset.mem_Ioo] at ht
  intro heq
  nlinarith

theorem donor_image_inj (m : ℕ) (hm : 1 ≤ m) :
    ∀ a ∈ Finset.Ioo (0 : ℕ) m, ∀ b ∈ Finset.Ioo (0 : ℕ) m,
      m * (m + a) = m * (m + b) → a = b := by
  intro a _ b _ hab
  have hmpos : 0 < m := hm
  have : m + a = m + b := Nat.eq_of_mul_eq_mul_left hmpos hab
  omega

theorem prod_donorSet_baseBAt (m : ℕ) (hm : 3 ≤ m) :
    ∏ y ∈ donorSet m, baseBAt m y = ∏ t ∈ Finset.Ioo 0 m, (m + t) := by
  unfold donorSet
  rw [Finset.prod_image (donor_image_inj m (by omega))]
  apply Finset.prod_congr rfl
  intro t ht
  simp [Finset.mem_Ioo] at ht
  exact baseBAt_donor m t (by omega) ht.1 ht.2

theorem prod_smallSet_baseBAt (m : ℕ) :
    ∏ x ∈ smallSet m, baseBAt m x = ∏ t ∈ Finset.Ioo 0 m, t * m := by
  unfold smallSet
  apply Finset.prod_congr rfl
  intro t ht
  apply baseBAt_small
  simp [smallSet, Finset.mem_Ioo]
  exact (Finset.mem_Ioo.mp ht)

theorem prod_donorSet_id (m : ℕ) (hm : 1 ≤ m) :
    ∏ y ∈ donorSet m, y = ∏ t ∈ Finset.Ioo 0 m, m * (m + t) := by
  unfold donorSet
  rw [Finset.prod_image (donor_image_inj m hm)]

theorem base_pair_match (m : ℕ) :
    (∏ t ∈ Finset.Ioo 0 m, t * m) * (∏ t ∈ Finset.Ioo 0 m, (m + t)) =
      (∏ t ∈ Finset.Ioo 0 m, t) * (∏ t ∈ Finset.Ioo 0 m, m * (m + t)) := by
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro t _
  ring

theorem prod_baseBAt_smallUnionDonor_eq (m : ℕ) (hm : 3 ≤ m) :
    ∏ x ∈ smallSet m ∪ donorSet m, baseBAt m x =
      ∏ x ∈ smallSet m ∪ donorSet m, x := by
  rw [Finset.prod_union (small_donor_disjoint m hm)]
  rw [Finset.prod_union (small_donor_disjoint m hm)]
  rw [prod_smallSet_baseBAt, prod_donorSet_baseBAt m hm]
  rw [prod_donorSet_id m (by omega)]
  have hsm : (∏ x ∈ smallSet m, x) = ∏ t ∈ Finset.Ioo 0 m, t := rfl
  rw [hsm]
  exact base_pair_match m

theorem outside_smallUnionDonor_eq_self (m : ℕ) (hm : 3 ≤ m) :
    ∀ x ∈ Finset.Icc 1 (baseK m) \ (smallSet m ∪ donorSet m),
      baseBAt m x = x := by
  intro x hx
  simp [Finset.mem_sdiff, Finset.mem_union] at hx
  obtain ⟨_, hxnotS, hxnotD⟩ := hx
  exact baseBAt_other m x hxnotS hxnotD

theorem prod_baseBAt_Icc_eq_factorial (m : ℕ) (hm : 3 ≤ m) :
    ∏ x ∈ Finset.Icc 1 (baseK m), baseBAt m x = (baseK m).factorial := by
  have hsmall_sub : smallSet m ⊆ Finset.Icc 1 (baseK m) := smallSet_subset_baseK m hm
  have hdon_sub : donorSet m ⊆ Finset.Icc 1 (baseK m) := donorSet_subset_baseK m hm
  have hunion_sub : smallSet m ∪ donorSet m ⊆ Finset.Icc 1 (baseK m) :=
    Finset.union_subset hsmall_sub hdon_sub
  have hsplit_baseBAt :
      ∏ x ∈ Finset.Icc 1 (baseK m), baseBAt m x =
        (∏ x ∈ smallSet m ∪ donorSet m, baseBAt m x) *
        (∏ x ∈ Finset.Icc 1 (baseK m) \ (smallSet m ∪ donorSet m), baseBAt m x) := by
    rw [← Finset.prod_union (Finset.disjoint_sdiff)]
    congr 1
    rw [Finset.union_sdiff_of_subset hunion_sub]
  have hsplit_id :
      (baseK m).factorial = (∏ x ∈ smallSet m ∪ donorSet m, x) *
        (∏ x ∈ Finset.Icc 1 (baseK m) \ (smallSet m ∪ donorSet m), x) := by
    rw [← Finset.prod_union (Finset.disjoint_sdiff)]
    rw [Finset.union_sdiff_of_subset hunion_sub]
    have h_icc_ico :
        Finset.Icc 1 (baseK m) = Finset.Ico 1 (baseK m + 1) := by
      ext x
      simp [Finset.mem_Icc, Finset.mem_Ico, Nat.lt_succ_iff]
    rw [h_icc_ico, Finset.prod_Ico_id_eq_factorial]
  rw [hsplit_baseBAt, hsplit_id]
  congr 1
  · exact prod_baseBAt_smallUnionDonor_eq m hm
  · apply Finset.prod_congr rfl
    exact outside_smallUnionDonor_eq_self m hm

def baseB (m : ℕ) : Fin (baseK m) → ℕ := fun j => baseBAt m (j.val + 1)

theorem prod_fin_baseB_eq_prod_Icc (m : ℕ) :
    (∏ j : Fin (baseK m), baseB m j) =
      ∏ x ∈ Finset.Icc 1 (baseK m), baseBAt m x := by
  unfold baseB
  rw [Fin.prod_univ_eq_prod_range (fun v => baseBAt m (v + 1)) (baseK m)]
  have hbij :
      ∀ x ∈ Finset.Icc 1 (baseK m), x - 1 ∈ Finset.range (baseK m) := by
    intro x hx
    simp [Finset.mem_Icc] at hx
    simp [Finset.mem_range]; omega
  symm
  apply Finset.prod_bij (fun x _ => x - 1) hbij
  · intro a ha b hb hab
    simp [Finset.mem_Icc] at ha hb
    omega
  · intro v hv
    simp [Finset.mem_range] at hv
    refine ⟨v + 1, ?_, by omega⟩
    simp [Finset.mem_Icc]; omega
  · intro a ha
    simp [Finset.mem_Icc] at ha
    have : a - 1 + 1 = a := by omega
    rw [this]

theorem exists_factorization_base_square (m : ℕ) (hm : 3 ≤ m) :
    ∃ B : Fin (baseK m) → ℕ,
      (∏ j, B j = (baseK m).factorial) ∧ (∀ j, m ≤ B j) := by
  refine ⟨baseB m, ?_, ?_⟩
  · rw [prod_fin_baseB_eq_prod_Icc]
    exact prod_baseBAt_Icc_eq_factorial m hm
  · intro j
    unfold baseB
    apply baseBAt_ge_m m (j.val + 1) hm
    omega

theorem extend_factorization {m k : ℕ} (hmk : m ≤ k + 1)
    (h : ∃ B : Fin k → ℕ, (∏ j, B j = k.factorial) ∧ (∀ j, m ≤ B j)) :
    ∃ B : Fin (k + 1) → ℕ,
      (∏ j, B j = (k + 1).factorial) ∧ (∀ j, m ≤ B j) := by
  obtain ⟨B, hprod, hge⟩ := h
  refine ⟨Fin.snoc B (k + 1), ?_, ?_⟩
  · rw [Fin.prod_snoc]
    rw [hprod]
    rw [Nat.factorial_succ]
    ring
  · intro j
    refine Fin.lastCases ?_ ?_ j
    · rw [Fin.snoc_last]
      omega
    · intro i
      rw [Fin.snoc_castSucc]
      exact hge i

theorem exists_factorization_existence (m k : ℕ) (hm : 3 ≤ m) (hk : baseK m ≤ k) :
    ∃ B : Fin k → ℕ, (∏ j, B j = k.factorial) ∧ (∀ j, m ≤ B j) := by
  induction k, hk using Nat.le_induction with
  | base => exact exists_factorization_base_square m hm
  | succ k hk ih =>
    refine extend_factorization ?_ ih
    have : m ≤ baseK m := by unfold baseK; nlinarith
    omega



structure ExactValuationData (m k : ℕ) where
  N₀ : ℤ
  Mk : ℕ
  Mk_pos : 0 < Mk
  B : Fin k → ℕ
  prod_B : ∏ j, B j = k.factorial
  B_ge_m : ∀ j, m ≤ B j
  Mk_smooth : ∀ p : ℕ, p.Prime → p ∣ Mk → p ≤ k
  B_dvd_Mk : ∀ j, B j ∣ Mk
  L_div : ∀ (n : ℕ) (j : Fin k),
    (B j : ℤ) ∣ (N₀ + (Mk : ℤ) * n - (k : ℤ) + ((j.val : ℤ) + 1))
  N_pos : ∀ n : ℕ, 0 < N₀ + (Mk : ℤ) * n
  binom_eq : ∀ n : ℕ,
    (((N₀ + (Mk : ℤ) * n).toNat).choose k : ℤ) =
      ∏ j, (N₀ + (Mk : ℤ) * n - (k : ℤ) + ((j.val : ℤ) + 1)) / (B j : ℤ)
  pairwise_coprime : ∀ n : ℕ, ∀ i j : Fin k, i ≠ j →
    Int.gcd
      ((N₀ + (Mk : ℤ) * n - (k : ℤ) + ((i.val : ℤ) + 1)) / (B i : ℤ))
      ((N₀ + (Mk : ℤ) * n - (k : ℤ) + ((j.val : ℤ) + 1)) / (B j : ℤ)) = 1
  k_lt_N_toNat : ∀ n : ℕ, k < (N₀ + (Mk : ℤ) * n).toNat

theorem factorial_prime_le_aux (k p : ℕ) (hp : p.Prime) (hdvd : p ∣ k.factorial) :
    p ≤ k :=
  (Nat.Prime.dvd_factorial hp).mp hdvd

theorem prod_L_eq_descFactorial (k : ℕ) (B : Fin k → ℕ) (N : ℤ)
    (hprod : ∏ j, B j = k.factorial)
    (hL_div : ∀ j : Fin k, (B j : ℤ) ∣ (N - (k : ℤ) + ((j.val : ℤ) + 1))) :
    (∏ j : Fin k, (N - (k : ℤ) + ((j.val : ℤ) + 1)) / (B j : ℤ)) * (k.factorial : ℤ) =
      ∏ j : Fin k, (N - (k : ℤ) + ((j.val : ℤ) + 1)) := by
  have hprod_int : ((∏ j, B j : ℕ) : ℤ) = (k.factorial : ℤ) := by exact_mod_cast hprod
  rw [← hprod_int]
  push_cast
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  rw [Int.ediv_mul_cancel (hL_div j)]

theorem prod_Fin_eq_prod_range_descFactorial (N : ℤ) (k : ℕ) :
    (∏ j : Fin k, (N - (k : ℤ) + ((j.val : ℤ) + 1))) =
      (∏ i ∈ Finset.range k, (N - (i : ℤ))) := by
  have h1 : (∏ j : Fin k, (N - (k : ℤ) + ((j.val : ℤ) + 1))) =
      ∏ j ∈ Finset.range k, (N - (k : ℤ) + ((j : ℤ) + 1)) :=
    Fin.prod_univ_eq_prod_range (fun v => N - (k : ℤ) + ((v : ℤ) + 1)) k
  rw [h1]
  have h2 : (∏ j ∈ Finset.range k, (N - (k : ℤ) + ((j : ℤ) + 1))) =
      ∏ j ∈ Finset.range k, (N - ((k - 1 - j : ℕ) : ℤ)) := by
    apply Finset.prod_congr rfl
    intro j hj
    simp only [Finset.mem_range] at hj
    have hcast : ((k - 1 - j : ℕ) : ℤ) = (k : ℤ) - 1 - j := by
      have : j + 1 ≤ k := hj
      push_cast
      omega
    rw [hcast]; ring
  rw [h2]
  exact Finset.prod_range_reflect (fun i => N - (i : ℤ)) k

theorem descFactorial_int_eq (N : ℤ) (k : ℕ) (hN : (k : ℤ) ≤ N) (hN_nn : 0 ≤ N) :
    (∏ i ∈ Finset.range k, (N - (i : ℤ))) =
      ((N.toNat.descFactorial k : ℕ) : ℤ) := by
  rw [Nat.descFactorial_eq_prod_range]
  push_cast
  apply Finset.prod_congr rfl
  intro i hi
  simp only [Finset.mem_range] at hi
  have hi_le_N : (i : ℤ) ≤ N.toNat := by
    have : (k : ℤ) ≤ N.toNat := by
      rw [Int.toNat_of_nonneg hN_nn]; exact hN
    have : (i : ℤ) ≤ (k : ℤ) := by exact_mod_cast Nat.le_of_lt_succ (Nat.lt_succ_of_lt hi)
    omega
  rw [show ((N.toNat - i : ℕ) : ℤ) = (N.toNat : ℤ) - i from by omega]
  rw [Int.toNat_of_nonneg hN_nn]

theorem N₀_gives_binom_decomposition (m k : ℕ) (B : Fin k → ℕ) (Mk : ℕ) (N₀ : ℤ)
    (_hMk_pos : 0 < Mk) (hprod : ∏ j, B j = k.factorial) (_hBge : ∀ j, m ≤ B j)
    (hL_div : ∀ (n : ℕ) (j : Fin k),
        (B j : ℤ) ∣ (N₀ + (Mk : ℤ) * n - (k : ℤ) + ((j.val : ℤ) + 1)))
    (hN_pos : ∀ n : ℕ, 0 < N₀ + (Mk : ℤ) * n)
    (hkN : ∀ n : ℕ, k ≤ (N₀ + (Mk : ℤ) * n).toNat) :
    ∀ n : ℕ,
      (((N₀ + (Mk : ℤ) * n).toNat).choose k : ℤ) =
        ∏ j, (N₀ + (Mk : ℤ) * n - (k : ℤ) + ((j.val : ℤ) + 1)) / (B j : ℤ) := by
  intro n
  set N := N₀ + (Mk : ℤ) * n with hN_def
  have hN_pos_n : 0 < N := hN_pos n
  have hkN_n : k ≤ N.toNat := hkN n
  have hk_le_N : (k : ℤ) ≤ N := by
    have := hkN_n
    have : (k : ℤ) ≤ (N.toNat : ℤ) := by exact_mod_cast this
    rw [Int.toNat_of_nonneg hN_pos_n.le] at this
    exact this
  have hL_div' : ∀ j : Fin k, (B j : ℤ) ∣ (N - (k : ℤ) + ((j.val : ℤ) + 1)) := hL_div n
  have h_prod_eq : (∏ j : Fin k, (N - (k : ℤ) + ((j.val : ℤ) + 1)) / (B j : ℤ)) *
      (k.factorial : ℤ) = ∏ j : Fin k, (N - (k : ℤ) + ((j.val : ℤ) + 1)) :=
    prod_L_eq_descFactorial k B N hprod hL_div'
  have h_prod_descFact : (∏ j : Fin k, (N - (k : ℤ) + ((j.val : ℤ) + 1))) =
      ((N.toNat.descFactorial k : ℕ) : ℤ) := by
    rw [prod_Fin_eq_prod_range_descFactorial]
    exact descFactorial_int_eq N k hk_le_N hN_pos_n.le
  have h_dF_choose : (N.toNat.descFactorial k : ℤ) = (N.toNat.choose k : ℤ) * (k.factorial : ℤ) := by
    have : N.toNat.descFactorial k = k.factorial * N.toNat.choose k :=
      Nat.descFactorial_eq_factorial_mul_choose _ _
    rw [this]; push_cast; ring
  have hkf_pos : 0 < (k.factorial : ℤ) := by exact_mod_cast Nat.factorial_pos k
  have hkf_ne : (k.factorial : ℤ) ≠ 0 := hkf_pos.ne'
  have h_final : (∏ j : Fin k, (N - (k : ℤ) + ((j.val : ℤ) + 1)) / (B j : ℤ)) *
      (k.factorial : ℤ) = (N.toNat.choose k : ℤ) * (k.factorial : ℤ) := by
    rw [h_prod_eq, h_prod_descFact, h_dF_choose]
  have := mul_right_cancel₀ hkf_ne h_final
  linarith [this]

theorem exists_full_construction_from_cert (m k : ℕ) (_hk : 2 ≤ k)
    (cert : GlobalResidueCertificate m k) :
    Nonempty (ExactValuationData m k) := by
  obtain ⟨N₀, hL_div, hN_pos, hkN, hcopr⟩ :=
    exists_N₀_via_CRT_cert cert
  have hkN_le : ∀ n : ℕ, k ≤ (N₀ + (cert.Mk : ℤ) * n).toNat := fun n => (hkN n).le
  have hbinom := N₀_gives_binom_decomposition m k cert.B cert.Mk N₀ cert.hMk_pos cert.hprod_B
    cert.hB_ge hL_div hN_pos hkN_le
  exact ⟨
    { N₀ := N₀
      Mk := cert.Mk
      Mk_pos := cert.hMk_pos
      B := cert.B
      prod_B := cert.hprod_B
      B_ge_m := cert.hB_ge
      Mk_smooth := cert.hMk_smooth
      B_dvd_Mk := cert.hB_dvd_Mk
      L_div := hL_div
      N_pos := hN_pos
      binom_eq := hbinom
      pairwise_coprime := hcopr
      k_lt_N_toNat := hkN }⟩




structure CoverData (m k : ℕ) where
  a : ℕ → ℕ
  q : ℕ
  q_prime : q.Prime
  m_le_q : m ≤ q
  q_le_2m : q ≤ 2 * m - 2
  k_ge_4m : 4 * m + 4 ≤ k
  q_dvd_k : q ∣ k
  a_lt_p : ∀ p, p.Prime → a p < p
  a_bound : ∀ p, p.Prime → m ≤ p → p < k → a p < p - k % p
  covers : ∀ j, 1 ≤ j → j ≤ k →
    ∃ p, p.Prime ∧ m ≤ p ∧ p ≤ k ∧ j % p = a p ∧
      (a p = 0 ∨ p ≤ k / 2 ∨ j ≤ p)
  scaffold : ∀ p, p.Prime → a p ≠ 0 →
    p = q ∨ (k / 2 < p ∧ p ≤ k ∧ p % q = 1)

noncomputable def alphaP (k p : ℕ) : ℕ := Nat.log p k

noncomputable def liftAtLevel (a : ℕ → ℕ) (p u : ℕ) : ℕ :=
  if a p = 0 then 0
  else if u = 0 then 0
  else if u = 1 then a p
  else liftAbove p u (a p)

open Classical in
noncomputable def exponent (k : ℕ) (a : ℕ → ℕ) (j p : ℕ) : ℕ :=
  if a p = 0 then padicValNat p j
  else
    (Finset.Icc 0 (alphaP k p)).sup
      (fun u => if j % p ^ u = liftAtLevel a p u then u else 0)

noncomputable def innerB (k : ℕ) (a : ℕ → ℕ) (j : ℕ) : ℕ :=
  ∏ p ∈ (Finset.Icc 1 k).filter Nat.Prime, p ^ exponent k a j p

open Classical in
noncomputable def scaffoldExcess (k : ℕ) (a : ℕ → ℕ) (j : ℕ) : Finset ℕ :=
  ((Finset.Icc 1 k).filter Nat.Prime).filter
    (fun p => a p ≠ 0 ∧ k / 2 < p ∧ p < j ∧ (j - p) % p = a p ∧ j - p ≥ 1)

noncomputable def outerB (k : ℕ) (a : ℕ → ℕ) (j : ℕ) : ℕ :=
  innerB k a j / ∏ p ∈ scaffoldExcess k a j, p

noncomputable def globalMk (k : ℕ) : ℕ :=
  ∏ p ∈ (Finset.Icc 1 k).filter Nat.Prime, p ^ (alphaP k p + 1)

theorem globalMk_pos (k : ℕ) : 0 < globalMk k := by
  unfold globalMk
  exact Finset.prod_pos (fun p hp => by
    rw [Finset.mem_filter] at hp
    exact Nat.pos_of_ne_zero (pow_ne_zero _ (Nat.Prime.ne_zero hp.2)))

theorem innerB_pos (k : ℕ) (a : ℕ → ℕ) (j : ℕ) : 0 < innerB k a j := by
  unfold innerB
  apply Finset.prod_pos
  intro p hp
  rw [Finset.mem_filter] at hp
  exact Nat.pos_of_ne_zero (pow_ne_zero _ hp.2.ne_zero)

theorem scaffold_prod_pos (k : ℕ) (a : ℕ → ℕ) (j : ℕ) :
    0 < ∏ p ∈ scaffoldExcess k a j, p := by
  apply Finset.prod_pos
  intro p hp
  unfold scaffoldExcess at hp
  rw [Finset.mem_filter, Finset.mem_filter] at hp
  exact hp.1.2.pos

theorem liftAtLevel_one (a : ℕ → ℕ) (p : ℕ) (ha : a p ≠ 0) :
    liftAtLevel a p 1 = a p := by
  unfold liftAtLevel
  rw [if_neg ha, if_neg (by omega : (1:ℕ) ≠ 0), if_pos rfl]

theorem scaffold_member_exponent_pos (k : ℕ) (a : ℕ → ℕ) (j : ℕ)
    (p : ℕ) (hp_mem : p ∈ scaffoldExcess k a j) :
    1 ≤ exponent k a j p := by
  unfold scaffoldExcess at hp_mem
  simp only [Finset.mem_filter, Finset.mem_Icc] at hp_mem
  obtain ⟨⟨⟨hp1, hpk⟩, hp_prime⟩, ha_ne_zero, _hk2lt, hp_lt_j, hmod, hjpge⟩ := hp_mem
  have hj_mod_p : j % p = a p := by
    have heq : j = (j - p) + p := by omega
    have hmod_eq : ((j - p) + p) % p = (j - p) % p := by
      rw [Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod]
    rw [heq, hmod_eq, hmod]
  unfold exponent
  rw [if_neg ha_ne_zero]
  have hk_pos : 0 < k := by omega
  have h1_le_alphaP : 1 ≤ alphaP k p := by
    unfold alphaP
    have : p ^ 1 ≤ k := by rw [pow_one]; exact hpk
    exact (Nat.le_log_iff_pow_le hp_prime.one_lt hk_pos.ne').mpr this
  have h1_mem : (1 : ℕ) ∈ Finset.Icc 0 (alphaP k p) := by
    rw [Finset.mem_Icc]; exact ⟨Nat.zero_le _, h1_le_alphaP⟩
  have hf1 : (fun u => if j % p ^ u = liftAtLevel a p u then u else 0) 1 = 1 := by
    show (if j % p ^ 1 = liftAtLevel a p 1 then 1 else 0 : ℕ) = 1
    rw [pow_one, liftAtLevel_one a p ha_ne_zero, hj_mod_p, if_pos rfl]
  have hle : (1 : ℕ) ≤
    (Finset.Icc 0 (alphaP k p)).sup
      (fun u => if j % p ^ u = liftAtLevel a p u then u else 0) := by
    rw [← hf1]
    exact Finset.le_sup (f := fun u => if j % p ^ u = liftAtLevel a p u then u else 0) h1_mem
  exact hle

theorem exponent_pos_pow_dvd_innerB (k : ℕ) (a : ℕ → ℕ) (j : ℕ) (p : ℕ)
    (hp_in : p ∈ ((Finset.Icc 1 k).filter Nat.Prime))
    (he_pos : 1 ≤ exponent k a j p) :
    p ∣ innerB k a j := by
  unfold innerB
  have hpdvd : p ∣ p ^ exponent k a j p := dvd_pow_self _ (by omega : exponent k a j p ≠ 0)
  exact dvd_trans hpdvd (Finset.dvd_prod_of_mem _ hp_in)

theorem scaffoldExcess_subset_primes (k : ℕ) (a : ℕ → ℕ) (j : ℕ) :
    scaffoldExcess k a j ⊆ (Finset.Icc 1 k).filter Nat.Prime := by
  intro p hp
  unfold scaffoldExcess at hp
  exact (Finset.mem_filter.mp hp).1

theorem scaffold_prime_dvd_innerB (k : ℕ) (a : ℕ → ℕ) (j : ℕ) (p : ℕ)
    (hp_mem : p ∈ scaffoldExcess k a j) :
    p ∣ innerB k a j := by
  have he_pos := scaffold_member_exponent_pos k a j p hp_mem
  have hp_in := scaffoldExcess_subset_primes k a j hp_mem
  exact exponent_pos_pow_dvd_innerB k a j p hp_in he_pos

theorem scaffold_dvd_innerB (k : ℕ) (a : ℕ → ℕ) (j : ℕ) :
    (∏ p ∈ scaffoldExcess k a j, p) ∣ innerB k a j := by
  classical
  apply Finset.prod_dvd_of_isRelPrime (s := id)
  · intro p hp q hq hpq
    have hpsub := scaffoldExcess_subset_primes k a j hp
    have hqsub := scaffoldExcess_subset_primes k a j hq
    have hp_prime : p.Prime := (Finset.mem_filter.mp hpsub).2
    have hq_prime : q.Prime := (Finset.mem_filter.mp hqsub).2
    have hcop : Nat.Coprime p q := (Nat.coprime_primes hp_prime hq_prime).mpr hpq
    show IsRelPrime p q
    exact Nat.coprime_iff_isRelPrime.mp hcop
  · intro p hp
    exact scaffold_prime_dvd_innerB k a j p hp

theorem outerB_pos_of_a {k : ℕ} (a : ℕ → ℕ) (j : ℕ) (hj : 1 ≤ j) (hjk : j ≤ k) :
    0 < outerB k a j := by
  unfold outerB
  have hdvd := scaffold_dvd_innerB k a j
  have hpos := innerB_pos k a j
  have hsc_pos := scaffold_prod_pos k a j
  rcases hdvd with ⟨c, hc⟩
  rw [hc]
  rw [Nat.mul_div_cancel_left _ hsc_pos]
  rcases Nat.eq_zero_or_pos c with hc0 | hc0
  · subst hc0
    rw [Nat.mul_zero] at hc
    omega
  · exact hc0

theorem outerB_pos {m k : ℕ} (hk : 3 ≤ k) (cov : CoverData m k) (j : Fin k) :
    0 < outerB k cov.a (j.val + 1) :=
  outerB_pos_of_a cov.a (j.val + 1) (Nat.succ_le_iff.mpr (Nat.zero_lt_succ _)) j.isLt

theorem exponent_pos_when_mod_a_eq (k : ℕ) (cov_a : ℕ → ℕ) (j : ℕ) (p : ℕ)
    (hp : p.Prime) (hpk : p ≤ k) (hk_pos : 0 < k) (hj_pos : 0 < j) (hj_le : j ≤ k)
    (hjmod : j % p = cov_a p) :
    1 ≤ exponent k cov_a j p := by
  unfold exponent
  by_cases hap : cov_a p = 0
  · rw [if_pos hap]
    have hp_dvd_j : p ∣ j := by
      rw [Nat.dvd_iff_mod_eq_zero]
      rw [hjmod, hap]
    have : Fact p.Prime := ⟨hp⟩
    exact one_le_padicValNat_of_dvd (by omega : j ≠ 0) hp_dvd_j
  · rw [if_neg hap]
    have h1_le_alphaP : 1 ≤ alphaP k p := by
      unfold alphaP
      have : p ^ 1 ≤ k := by rw [pow_one]; exact hpk
      exact (Nat.le_log_iff_pow_le hp.one_lt hk_pos.ne').mpr this
    have h1_mem : (1 : ℕ) ∈ Finset.Icc 0 (alphaP k p) := by
      rw [Finset.mem_Icc]; exact ⟨Nat.zero_le _, h1_le_alphaP⟩
    have hf1 : (fun u => if j % p ^ u = liftAtLevel cov_a p u then u else 0) 1 = 1 := by
      show (if j % p ^ 1 = liftAtLevel cov_a p 1 then 1 else 0 : ℕ) = 1
      rw [pow_one, liftAtLevel_one cov_a p hap, hjmod, if_pos rfl]
    have hle : (1 : ℕ) ≤
      (Finset.Icc 0 (alphaP k p)).sup
        (fun u => if j % p ^ u = liftAtLevel cov_a p u then u else 0) := by
      rw [← hf1]
      exact Finset.le_sup (f := fun u => if j % p ^ u = liftAtLevel cov_a p u then u else 0) h1_mem
    exact hle

theorem q_le_k_half {m k : ℕ} (cov : CoverData m k) (hm : 3 ≤ m) :
    cov.q ≤ k / 2 := by
  have h1 := cov.q_le_2m
  have h2 := cov.k_ge_4m
  omega

theorem outerB_ge_m_from_outside_scaffold {m k : ℕ} (hm : 3 ≤ m) (hk : 3 ≤ k)
    (cov : CoverData m k) (j : Fin k)
    (p : ℕ) (hp_prime : p.Prime) (hmp : m ≤ p) (hpk : p ≤ k)
    (hjmod : (j.val + 1) % p = cov.a p)
    (hp_notin_scaffold : p ∉ scaffoldExcess k cov.a (j.val + 1)) :
    m ≤ outerB k cov.a (j.val + 1) := by
  have hk_pos : 0 < k := by omega
  have hjp_pos : 0 < j.val + 1 := Nat.succ_pos _
  have hjle : j.val + 1 ≤ k := j.isLt
  have hexp_pos := exponent_pos_when_mod_a_eq k cov.a (j.val + 1) p hp_prime hpk
    hk_pos hjp_pos hjle hjmod
  have hp_in : p ∈ (Finset.Icc 1 k).filter Nat.Prime := by
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hp_prime.one_lt.le, hpk⟩, hp_prime⟩
  have hp_dvd_inner := exponent_pos_pow_dvd_innerB k cov.a (j.val + 1) p hp_in hexp_pos
  have hp_coprime_scaffold :
      Nat.Coprime p (∏ q ∈ scaffoldExcess k cov.a (j.val + 1), q) := by
    apply Nat.Coprime.prod_right
    intro q hq
    have hq_sub := scaffoldExcess_subset_primes k cov.a (j.val + 1) hq
    have hq_prime : q.Prime := (Finset.mem_filter.mp hq_sub).2
    have hpq_ne : p ≠ q := fun heq => hp_notin_scaffold (heq ▸ hq)
    exact (Nat.coprime_primes hp_prime hq_prime).mpr hpq_ne
  have hp_dvd_outer : p ∣ outerB k cov.a (j.val + 1) := by
    rcases scaffold_dvd_innerB k cov.a (j.val + 1) with ⟨c, hc⟩
    have hc_eq : outerB k cov.a (j.val + 1) = c := by
      unfold outerB
      rw [hc, Nat.mul_div_cancel_left _ (scaffold_prod_pos k cov.a (j.val + 1))]
    rw [hc_eq]
    rw [hc] at hp_dvd_inner
    exact hp_coprime_scaffold.dvd_of_dvd_mul_left hp_dvd_inner
  have hp_le_outer : p ≤ outerB k cov.a (j.val + 1) :=
    Nat.le_of_dvd (outerB_pos hk cov j) hp_dvd_outer
  exact le_trans hmp hp_le_outer

theorem outerB_ge_m {m k : ℕ} (hm : 3 ≤ m) (hk : 3 ≤ k) (cov : CoverData m k)
    (j : Fin k) : m ≤ outerB k cov.a (j.val + 1) := by
  have hjpos : 1 ≤ j.val + 1 := Nat.succ_pos _
  have hjle : j.val + 1 ≤ k := j.isLt
  obtain ⟨p, hp_prime, hmp, hpk, hjmod, hnon_scaffold⟩ :=
    cov.covers (j.val + 1) hjpos hjle
  have hp_not_in : p ∉ scaffoldExcess k cov.a (j.val + 1) := by
    intro hin
    unfold scaffoldExcess at hin
    simp only [Finset.mem_filter, Finset.mem_Icc] at hin
    obtain ⟨_, hap_ne, hk2_lt, hp_lt_j, _, _⟩ := hin
    rcases hnon_scaffold with hap0 | hpk2 | hjp
    · exact hap_ne hap0
    · omega
    · omega
  exact outerB_ge_m_from_outside_scaffold hm hk cov j p hp_prime hmp hpk hjmod hp_not_in

theorem scaffoldExcess_value_eq (k : ℕ) (a : ℕ → ℕ) (p j : ℕ) (hjk : j ≤ k)
    (hp : p ∈ scaffoldExcess k a j) :
    j = p + a p := by
  unfold scaffoldExcess at hp
  simp only [Finset.mem_filter, Finset.mem_Icc] at hp
  obtain ⟨⟨⟨_, _⟩, _⟩, _, hk2lt, hp_lt_j, hmod, hjpge⟩ := hp
  have h2p : 2 * p > k := by omega
  have hjp_lt_p : j - p < p := by omega
  rw [Nat.mod_eq_of_lt hjp_lt_p] at hmod
  omega

theorem scaffoldExcess_unique_j {k : ℕ} (a : ℕ → ℕ) (p j₁ j₂ : ℕ)
    (hj₁k : j₁ ≤ k) (hj₂k : j₂ ≤ k)
    (h₁ : p ∈ scaffoldExcess k a j₁) (h₂ : p ∈ scaffoldExcess k a j₂) :
    j₁ = j₂ := by
  rw [scaffoldExcess_value_eq k a p j₁ hj₁k h₁,
      scaffoldExcess_value_eq k a p j₂ hj₂k h₂]

noncomputable def excessPrimesSet (k : ℕ) (a : ℕ → ℕ) : Finset ℕ :=
  ((Finset.Icc 1 k).filter Nat.Prime).filter
    (fun p => a p ≠ 0 ∧ k / 2 < p ∧ 1 ≤ a p ∧ p + a p ≤ k)

theorem mem_excessPrimesSet {k : ℕ} {a : ℕ → ℕ} {p : ℕ} :
    p ∈ excessPrimesSet k a ↔
      p.Prime ∧ 1 ≤ p ∧ p ≤ k ∧ a p ≠ 0 ∧ k / 2 < p ∧ 1 ≤ a p ∧ p + a p ≤ k := by
  unfold excessPrimesSet
  simp only [Finset.mem_filter, Finset.mem_Icc]
  tauto

theorem scaffold_in_excess (k : ℕ) (a : ℕ → ℕ) (j : ℕ) (hjle : j ≤ k) (p : ℕ)
    (hp : p ∈ scaffoldExcess k a j) : p ∈ excessPrimesSet k a := by
  unfold scaffoldExcess at hp
  simp only [Finset.mem_filter, Finset.mem_Icc] at hp
  obtain ⟨⟨⟨hp1, hpk⟩, hp_prime⟩, hap, hk2lt, hp_lt_j, hmod, hjpge⟩ := hp
  have h2p : 2 * p > k := by omega
  have hjp_lt_p : j - p < p := by omega
  rw [Nat.mod_eq_of_lt hjp_lt_p] at hmod
  have hj_eq : j = p + a p := by omega
  have hap_lt_p : a p < p := by
    have := scaffoldExcess_value_eq k a p j hjle
      (by unfold scaffoldExcess
          rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc]
          exact ⟨⟨⟨hp1, hpk⟩, hp_prime⟩, hap, hk2lt, hp_lt_j, by rw [Nat.mod_eq_of_lt hjp_lt_p]; exact hmod, hjpge⟩)
    omega
  rw [mem_excessPrimesSet]
  refine ⟨hp_prime, hp1, hpk, hap, hk2lt, ?_, ?_⟩
  · omega
  · omega

theorem excess_prime_ge_m {m k : ℕ} (cov : CoverData m k) (p : ℕ)
    (hp : p ∈ excessPrimesSet k cov.a) : m ≤ p := by
  rw [mem_excessPrimesSet] at hp
  have hk_ge := cov.k_ge_4m
  have hk2_lt_p : k / 2 < p := hp.2.2.2.2.1
  omega

theorem excess_prime_a_lt_p {m k : ℕ} (cov : CoverData m k) (p : ℕ)
    (hp : p ∈ excessPrimesSet k cov.a) : cov.a p < p := by
  rw [mem_excessPrimesSet] at hp
  obtain ⟨hp_prime, hp_pos, hpk, hap_ne, hk2lt, hap_pos, hp_ap_le⟩ := hp
  by_cases hp_eq_k : p = k
  · subst hp_eq_k
    omega
  · have hp_lt_k : p < k := lt_of_le_of_ne hpk hp_eq_k
    have hmp : m ≤ p := excess_prime_ge_m cov p
      (by rw [mem_excessPrimesSet]; exact ⟨hp_prime, hp_pos, hpk, hap_ne, hk2lt, hap_pos, hp_ap_le⟩)
    have hbound := cov.a_bound p hp_prime hmp hp_lt_k
    have hk_mod_p : k % p = k - p := by
      have h2 : k < 2 * p := by omega
      have h4 : k - p < p := by omega
      have h5 : k = p + (k - p) := by omega
      have h_pos : 0 < p := by omega
      conv_lhs => rw [h5]
      rw [Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_eq_of_lt h4, Nat.mod_eq_of_lt h4]
    rw [hk_mod_p] at hbound
    omega

theorem excess_in_scaffold (k : ℕ) (a : ℕ → ℕ) (p : ℕ)
    (hp : p ∈ excessPrimesSet k a) (hap_lt_p : a p < p) :
    p ∈ scaffoldExcess k a (p + a p) := by
  rw [mem_excessPrimesSet] at hp
  obtain ⟨hp_prime, hp_pos, hpk, hap, hk2lt, hap_pos, hp_ap_le⟩ := hp
  unfold scaffoldExcess
  rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc]
  refine ⟨⟨⟨hp_pos, hpk⟩, hp_prime⟩, hap, hk2lt, by omega, ?_, by omega⟩
  show (p + a p - p) % p = a p
  rw [show p + a p - p = a p from by omega]
  exact Nat.mod_eq_of_lt hap_lt_p

theorem excess_in_scaffold_cov {m k : ℕ} (cov : CoverData m k) (p : ℕ)
    (hp : p ∈ excessPrimesSet k cov.a) :
    p ∈ scaffoldExcess k cov.a (p + cov.a p) :=
  excess_in_scaffold k cov.a p hp (excess_prime_a_lt_p cov p hp)

theorem biUnion_scaffolds_eq_excess {m k : ℕ} (cov : CoverData m k) :
    (Finset.univ : Finset (Fin k)).biUnion
        (fun j => scaffoldExcess k cov.a (j.val + 1)) = excessPrimesSet k cov.a := by
  ext p
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, hj⟩
    exact scaffold_in_excess k cov.a (j.val + 1) (by have := j.isLt; omega) p hj
  · intro hp
    have hp_mem := excess_in_scaffold_cov cov p hp
    rw [mem_excessPrimesSet] at hp
    obtain ⟨_, hp_pos, _, _, _, hap_pos, hp_ap_le⟩ := hp
    have hk_pos : 0 < k := by omega
    have hj_lt : p + cov.a p - 1 < k := by omega
    refine ⟨⟨p + cov.a p - 1, hj_lt⟩, ?_⟩
    have hj_eq : (⟨p + cov.a p - 1, hj_lt⟩ : Fin k).val + 1 = p + cov.a p := by
      show p + cov.a p - 1 + 1 = p + cov.a p
      omega
    rw [hj_eq]
    exact hp_mem

theorem outerB_dvd_innerB (k : ℕ) (a : ℕ → ℕ) (j : ℕ) :
    outerB k a j ∣ innerB k a j := by
  rw [show innerB k a j = outerB k a j * ∏ p ∈ scaffoldExcess k a j, p from ?_]
  · exact dvd_mul_right _ _
  · unfold outerB
    rcases scaffold_dvd_innerB k a j with ⟨c, hc⟩
    rw [hc, Nat.mul_div_cancel_left _ (scaffold_prod_pos k a j), mul_comm]

theorem innerB_eq_outerB_mul_scaffold (k : ℕ) (a : ℕ → ℕ) (j : ℕ) :
    innerB k a j = outerB k a j * ∏ p ∈ scaffoldExcess k a j, p := by
  unfold outerB
  rcases scaffold_dvd_innerB k a j with ⟨c, hc⟩
  rw [hc, Nat.mul_div_cancel_left _ (scaffold_prod_pos k a j), mul_comm]

theorem sum_padicValNat_succ_eq_factorial (k p : ℕ) (hp : p.Prime) :
    ∑ j : Fin k, padicValNat p (j.val + 1) = padicValNat p k.factorial := by
  have : Fact p.Prime := ⟨hp⟩
  have hprod_range : k.factorial = ∏ i ∈ Finset.range k, (i + 1) :=
    Nat.factorial_eq_prod_range_add_one k
  have hreindex : ∑ j : Fin k, padicValNat p (j.val + 1) =
      ∑ i ∈ Finset.range k, padicValNat p (i + 1) :=
    Fin.sum_univ_eq_sum_range (fun i => padicValNat p (i + 1)) k
  rw [hreindex, hprod_range]
  clear hreindex hprod_range
  induction k with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.prod_range_succ]
    have hpos : 0 < n + 1 := Nat.succ_pos _
    have h2 : 0 < ∏ i ∈ Finset.range n, (i + 1) :=
      Finset.prod_pos (fun i _ => Nat.succ_pos _)
    rw [padicValNat.mul h2.ne' hpos.ne', ih]

theorem sum_exponent_a_zero {m k : ℕ} (cov : CoverData m k) (p : ℕ) (hp : p.Prime)
    (ha0 : cov.a p = 0) :
    ∑ j : Fin k, exponent k cov.a (j.val + 1) p = padicValNat p k.factorial := by
  have heq : ∀ j : Fin k, exponent k cov.a (j.val + 1) p = padicValNat p (j.val + 1) := by
    intro j
    unfold exponent
    rw [if_pos ha0]
  simp_rw [heq]
  exact sum_padicValNat_succ_eq_factorial k p hp

theorem prod_scaffolds_eq_biUnion (k : ℕ) (a : ℕ → ℕ) :
    ∏ j : Fin k, ∏ p ∈ scaffoldExcess k a (j.val + 1), p =
      ∏ p ∈ (Finset.univ : Finset (Fin k)).biUnion
        (fun j => scaffoldExcess k a (j.val + 1)), p := by
  classical
  rw [Finset.prod_biUnion]
  intro j₁ _ j₂ _ hne
  rw [Function.onFun, Finset.disjoint_left]
  intro p hp1 hp2
  apply hne
  have h1 : j₁.val + 1 ≤ k := j₁.isLt
  have h2 : j₂.val + 1 ≤ k := j₂.isLt
  have h_eq := scaffoldExcess_unique_j a p _ _ h1 h2 hp1 hp2
  exact Fin.ext (by omega)

theorem prod_innerB_eq_prod_outerB_mul_scaffolds {m k : ℕ} (cov : CoverData m k) :
    ∏ j : Fin k, innerB k cov.a (j.val + 1) =
      (∏ j : Fin k, outerB k cov.a (j.val + 1)) *
        ∏ j : Fin k, ∏ p ∈ scaffoldExcess k cov.a (j.val + 1), p := by
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl (fun j _ => innerB_eq_outerB_mul_scaffold k cov.a (j.val + 1))

theorem prod_scaffolds_eq_excess_prod {m k : ℕ} (cov : CoverData m k) :
    ∏ j : Fin k, ∏ p ∈ scaffoldExcess k cov.a (j.val + 1), p =
      ∏ p ∈ excessPrimesSet k cov.a, p := by
  rw [prod_scaffolds_eq_biUnion, biUnion_scaffolds_eq_excess]

theorem prod_innerB_eq_outerB_mul_excess {m k : ℕ} (cov : CoverData m k) :
    ∏ j : Fin k, innerB k cov.a (j.val + 1) =
      (∏ j : Fin k, outerB k cov.a (j.val + 1)) *
        ∏ p ∈ excessPrimesSet k cov.a, p := by
  rw [prod_innerB_eq_prod_outerB_mul_scaffolds, prod_scaffolds_eq_excess_prod]

theorem p_not_in_excess_of_a_zero {k : ℕ} {a : ℕ → ℕ} {p : ℕ} (ha0 : a p = 0) :
    p ∉ excessPrimesSet k a := by
  rw [mem_excessPrimesSet]
  rintro ⟨_, _, _, hap, _, _, _⟩
  exact hap ha0

theorem val_sum_innerB_a_zero {m k : ℕ} (cov : CoverData m k) (p : ℕ) (hp : p.Prime)
    (ha0 : cov.a p = 0) :
    ∑ j : Fin k, exponent k cov.a (j.val + 1) p =
      padicValNat p k.factorial +
        (if p ∈ excessPrimesSet k cov.a then 1 else 0) := by
  rw [if_neg (p_not_in_excess_of_a_zero ha0)]
  rw [Nat.add_zero]
  exact sum_exponent_a_zero cov p hp ha0

theorem excessPrimesSet_prod_pos {m k : ℕ} (cov : CoverData m k) :
    0 < ∏ p ∈ excessPrimesSet k cov.a, p := by
  apply Finset.prod_pos
  intro p hp
  rw [mem_excessPrimesSet] at hp
  exact hp.1.pos

theorem prod_outerB_eq_factorial_from_innerB {m k : ℕ} (cov : CoverData m k)
    (h_innerB : ∏ j : Fin k, innerB k cov.a (j.val + 1) =
        k.factorial * ∏ p ∈ excessPrimesSet k cov.a, p) :
    ∏ j : Fin k, outerB k cov.a (j.val + 1) = k.factorial := by
  have h_eq := prod_innerB_eq_outerB_mul_excess cov
  rw [h_innerB] at h_eq
  have h_excess_pos := excessPrimesSet_prod_pos cov
  exact (Nat.eq_of_mul_eq_mul_right h_excess_pos h_eq).symm

theorem prod_innerB_pos {m k : ℕ} (cov : CoverData m k) :
    0 < ∏ j : Fin k, innerB k cov.a (j.val + 1) :=
  Finset.prod_pos (fun j _ => innerB_pos k cov.a (j.val + 1))

theorem factorial_mul_excess_pos (m k : ℕ) (cov : CoverData m k) :
    0 < k.factorial * ∏ p ∈ excessPrimesSet k cov.a, p :=
  Nat.mul_pos (Nat.factorial_pos k) (excessPrimesSet_prod_pos cov)

theorem innerB_is_k_smooth (k : ℕ) (a : ℕ → ℕ) (j : ℕ) (p : ℕ) (hp : p.Prime)
    (hpdvd : p ∣ innerB k a j) :
    p ≤ k := by
  unfold innerB at hpdvd
  classical
  obtain ⟨q, hq_mem, hpq⟩ := (Prime.dvd_finset_prod_iff hp.prime _).mp hpdvd
  rw [Finset.mem_filter, Finset.mem_Icc] at hq_mem
  have hq_le_k : q ≤ k := hq_mem.1.2
  have hq_prime : q.Prime := hq_mem.2
  have hp_eq_q : p = q :=
    (Nat.prime_dvd_prime_iff_eq hp hq_prime).mp (Nat.Prime.dvd_of_dvd_pow hp hpq)
  rw [hp_eq_q]; exact hq_le_k

theorem prod_innerB_is_k_smooth (k : ℕ) (a : ℕ → ℕ) (p : ℕ) (hp : p.Prime)
    (hpdvd : p ∣ ∏ j : Fin k, innerB k a (j.val + 1)) :
    p ≤ k := by
  classical
  obtain ⟨j, _, hp_dvd_j⟩ := (Prime.dvd_finset_prod_iff hp.prime _).mp hpdvd
  exact innerB_is_k_smooth k a (j.val + 1) p hp hp_dvd_j

theorem factorization_prod_excessPrimesSet (k : ℕ) (a : ℕ → ℕ) (p : ℕ) (hp : p.Prime) :
    (∏ q ∈ excessPrimesSet k a, q).factorization p =
      if p ∈ excessPrimesSet k a then 1 else 0 := by
  classical
  rw [Nat.factorization_prod_apply
    (fun q hq => (mem_excessPrimesSet.mp hq).1.pos.ne')]
  by_cases hp_mem : p ∈ excessPrimesSet k a
  · rw [if_pos hp_mem]
    rw [Finset.sum_eq_single p]
    · exact Nat.Prime.factorization_self hp
    · intro q hq_mem hqp
      have hq_prime := (mem_excessPrimesSet.mp hq_mem).1
      rw [hq_prime.factorization, Finsupp.single_apply]
      exact if_neg hqp
    · intro hp_notin
      exact absurd hp_mem hp_notin
  · rw [if_neg hp_mem]
    apply Finset.sum_eq_zero
    intro q hq_mem
    have hq_prime := (mem_excessPrimesSet.mp hq_mem).1
    have hq_ne_p : q ≠ p := fun h => hp_mem (h ▸ hq_mem)
    rw [hq_prime.factorization, Finsupp.single_apply]
    exact if_neg hq_ne_p

theorem factorization_innerB_eq_exponent (k : ℕ) (a : ℕ → ℕ) (j : ℕ) (p : ℕ)
    (hp : p.Prime) (hpk : p ≤ k) :
    (innerB k a j).factorization p = exponent k a j p := by
  classical
  unfold innerB
  rw [Nat.factorization_prod_apply
    (fun q hq_mem => pow_ne_zero _ (Finset.mem_filter.mp hq_mem).2.ne_zero)]
  rw [Finset.sum_eq_single p]
  · rw [Nat.factorization_pow, Finsupp.smul_apply, hp.factorization_self,
      smul_eq_mul, mul_one]
  · intro q hq_mem hqp
    have hq_prime : q.Prime := (Finset.mem_filter.mp hq_mem).2
    rw [Nat.factorization_pow, Finsupp.smul_apply, hq_prime.factorization,
      Finsupp.single_apply, if_neg hqp]
    simp
  · intro hp_notin
    exfalso
    apply hp_notin
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hp.pos, hpk⟩, hp⟩

theorem factorization_prod_innerB_eq_sum_exponent (k : ℕ) (a : ℕ → ℕ) (p : ℕ) (hp : p.Prime)
    (hpk : p ≤ k) :
    (∏ j : Fin k, innerB k a (j.val + 1)).factorization p =
      ∑ j : Fin k, exponent k a (j.val + 1) p := by
  rw [Nat.factorization_prod_apply (fun j _ => (innerB_pos k a (j.val + 1)).ne')]
  exact Finset.sum_congr rfl (fun j _ =>
    factorization_innerB_eq_exponent k a (j.val + 1) p hp hpk)

theorem factorization_factorial_mul_excess {m k : ℕ} (cov : CoverData m k) (p : ℕ)
    (hp : p.Prime) :
    (k.factorial * ∏ q ∈ excessPrimesSet k cov.a, q).factorization p =
      padicValNat p k.factorial + (if p ∈ excessPrimesSet k cov.a then 1 else 0) := by
  rw [Nat.factorization_mul (Nat.factorial_pos k).ne'
    (excessPrimesSet_prod_pos cov).ne']
  rw [Finsupp.add_apply]
  rw [Nat.factorization_def _ hp]
  rw [factorization_prod_excessPrimesSet k cov.a p hp]

theorem padicValNat_factorial_eq_zero_of_lt {p k : ℕ} (hp : p.Prime) (hpk : k < p) :
    padicValNat p k.factorial = 0 := by
  rw [← Nat.factorization_def _ hp]
  rw [Nat.factorization_eq_zero_iff]
  right; left
  intro hdvd
  have := (Nat.Prime.dvd_factorial hp).mp hdvd
  omega

theorem excessPrimesSet_le_k {k : ℕ} {a : ℕ → ℕ} {p : ℕ} (hp : p ∈ excessPrimesSet k a) :
    p ≤ k := (mem_excessPrimesSet.mp hp).2.2.1

theorem prod_innerB_eq_factorial_mul_excess_from_val_sum {m k : ℕ} (hk : 3 ≤ k)
    (cov : CoverData m k)
    (h_val_sum : ∀ p : ℕ, p.Prime → p ≤ k →
      ∑ j : Fin k, exponent k cov.a (j.val + 1) p =
        padicValNat p k.factorial + (if p ∈ excessPrimesSet k cov.a then 1 else 0)) :
    ∏ j : Fin k, innerB k cov.a (j.val + 1) =
      k.factorial * ∏ p ∈ excessPrimesSet k cov.a, p := by
  apply Nat.eq_of_factorization_eq (prod_innerB_pos cov).ne'
    (factorial_mul_excess_pos m k cov).ne'
  intro p
  by_cases hp_prime : p.Prime
  · by_cases hpk : p ≤ k
    · rw [factorization_prod_innerB_eq_sum_exponent k cov.a p hp_prime hpk]
      rw [factorization_factorial_mul_excess cov p hp_prime]
      exact h_val_sum p hp_prime hpk
    · push_neg at hpk
      have h_LHS_0 : (∏ j : Fin k, innerB k cov.a (j.val + 1)).factorization p = 0 := by
        rw [Nat.factorization_eq_zero_iff]
        right; left; intro hdvd
        exact absurd (prod_innerB_is_k_smooth k cov.a p hp_prime hdvd) (by omega)
      have h_RHS_0 : (k.factorial * ∏ q ∈ excessPrimesSet k cov.a, q).factorization p = 0 := by
        rw [factorization_factorial_mul_excess cov p hp_prime]
        rw [padicValNat_factorial_eq_zero_of_lt hp_prime hpk]
        rw [if_neg (fun h_excess => absurd (excessPrimesSet_le_k h_excess) (by omega))]
      rw [h_LHS_0, h_RHS_0]
  · rw [Nat.factorization_eq_zero_of_not_prime _ hp_prime]
    rw [Nat.factorization_eq_zero_of_not_prime _ hp_prime]

theorem alphaP_eq_one_of_gt_half {k p : ℕ} (hp : p.Prime) (hpk : p ≤ k)
    (hp_gt : k / 2 < p) (hk_ge : 4 ≤ k) :
    alphaP k p = 1 := by
  unfold alphaP
  apply Nat.log_eq_of_pow_le_of_lt_pow
  · rw [pow_one]; exact hpk
  · have hk_lt_2p : k < p * 2 := (Nat.div_lt_iff_lt_mul (by norm_num : (0 : ℕ) < 2)).mp hp_gt
    have hp_ge_2 : 2 ≤ p := hp.two_le
    have : p * 2 ≤ p * p := Nat.mul_le_mul_left p hp_ge_2
    have h_pow : p ^ (1 + 1) = p * p := by ring
    omega

theorem exponent_eq_indicator_at_one {k : ℕ} (a : ℕ → ℕ) (j p : ℕ)
    (hp : p.Prime) (hpk : p ≤ k) (hp_gt : k / 2 < p) (hk_ge : 4 ≤ k)
    (ha : a p ≠ 0) :
    exponent k a j p = (if j % p = a p then 1 else 0) := by
  unfold exponent
  rw [if_neg ha]
  rw [alphaP_eq_one_of_gt_half hp hpk hp_gt hk_ge]
  show ((Finset.Icc 0 1 : Finset ℕ).sup
      fun u => if j % p ^ u = liftAtLevel a p u then u else 0) = _
  have hIcc : Finset.Icc 0 1 = {0, 1} := by decide
  rw [hIcc]
  rw [Finset.sup_insert, Finset.sup_singleton]
  have h0 : (if j % p ^ 0 = liftAtLevel a p 0 then (0 : ℕ) else 0) = 0 := by
    split_ifs <;> rfl
  rw [h0, Nat.zero_max]
  rw [pow_one, liftAtLevel_one a p ha]

theorem count_residue_large_prime (k p a : ℕ) (hp_pos : 0 < p) (hp_gt : k / 2 < p)
    (hpk : p ≤ k) (ha_pos : 1 ≤ a) (ha_lt : a < p) :
    ((Finset.Icc 1 k).filter (fun x => x % p = a)).card =
      (if a + p ≤ k then 2 else 1) := by
  classical
  have hk_lt_2p' : k < 2 * p := by
    have h := (Nat.div_lt_iff_lt_mul (by norm_num : (0 : ℕ) < 2)).mp hp_gt
    linarith
  by_cases hcase : a + p ≤ k
  · rw [if_pos hcase]
    have hset : (Finset.Icc 1 k).filter (fun x => x % p = a) = {a, a + p} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        have h_x_lt_2p : x < 2 * p := lt_of_le_of_lt h2 hk_lt_2p'
        have h_div_lt_2 : x / p < 2 := (Nat.div_lt_iff_lt_mul hp_pos).mpr h_x_lt_2p
        have h_eq : x = x % p + p * (x / p) := (Nat.mod_add_div x p).symm
        interval_cases (x / p)
        · left; omega
        · right; omega
      · rintro (rfl | rfl)
        · refine ⟨⟨ha_pos, by omega⟩, Nat.mod_eq_of_lt ha_lt⟩
        · refine ⟨⟨by linarith, hcase⟩, ?_⟩
          have : a + p = p * 1 + a := by ring
          rw [this, Nat.mul_add_mod]
          exact Nat.mod_eq_of_lt ha_lt
    rw [hset, Finset.card_insert_of_notMem, Finset.card_singleton]
    rw [Finset.mem_singleton]; omega
  · rw [if_neg hcase]
    have hcase' : k < a + p := by omega
    have hset : (Finset.Icc 1 k).filter (fun x => x % p = a) = {a} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        have h_x_lt_2p : x < 2 * p := lt_of_le_of_lt h2 hk_lt_2p'
        have h_div_lt_2 : x / p < 2 := (Nat.div_lt_iff_lt_mul hp_pos).mpr h_x_lt_2p
        have h_eq : x = x % p + p * (x / p) := (Nat.mod_add_div x p).symm
        interval_cases (x / p)
        · omega
        · exfalso; omega
      · rintro rfl
        refine ⟨⟨ha_pos, by omega⟩, Nat.mod_eq_of_lt ha_lt⟩
    rw [hset, Finset.card_singleton]

theorem padicValNat_factorial_eq_one_of_gt_half {p k : ℕ} (hp : p.Prime) (hpk : p ≤ k)
    (hp_gt : k / 2 < p) :
    padicValNat p k.factorial = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have hk_pos : 0 < k := by omega
  have hk_lt_2p : k < 2 * p := by
    have h := (Nat.div_lt_iff_lt_mul (by norm_num : (0 : ℕ) < 2)).mp hp_gt
    linarith
  have hp_ge_2 := hp.two_le
  have h_log : Nat.log p k = 1 :=
    Nat.log_eq_of_pow_le_of_lt_pow (by rw [pow_one]; exact hpk) (by
      have : p * 2 ≤ p * p := Nat.mul_le_mul_left p hp_ge_2
      have : p ^ (1 + 1) = p * p := by ring
      omega)
  rw [padicValNat_factorial (b := 2) (by omega)]
  rw [show (Finset.Ico 1 2 : Finset ℕ) = {1} from rfl]
  rw [Finset.sum_singleton, pow_one]
  exact Nat.div_eq_of_lt_le (by linarith) (by linarith)

theorem prime_a_nonzero_small_eq_q {m k : ℕ} (cov : CoverData m k) (p : ℕ)
    (hp : p.Prime) (ha : cov.a p ≠ 0) (hpk_half : p ≤ k / 2) : p = cov.q := by
  rcases cov.scaffold p hp ha with hpq | ⟨hk2_lt, _, _⟩
  · exact hpq
  · omega

theorem val_sum_innerB_scaffold {m k : ℕ} (cov : CoverData m k) (p : ℕ)
    (hp : p.Prime) (hpk : p ≤ k) (hp_gt : k / 2 < p) (ha : cov.a p ≠ 0) :
    ∑ j : Fin k, exponent k cov.a (j.val + 1) p =
      padicValNat p k.factorial +
        (if p ∈ excessPrimesSet k cov.a then 1 else 0) := by
  have hk_ge_4m := cov.k_ge_4m
  have hk_ge_4 : 4 ≤ k := by omega
  have hap_lt_p : cov.a p < p := cov.a_lt_p p hp
  have h_exp_eq : ∀ j : Fin k, exponent k cov.a (j.val + 1) p =
      (if (j.val + 1) % p = cov.a p then 1 else 0) := fun j =>
    exponent_eq_indicator_at_one cov.a (j.val + 1) p hp hpk hp_gt hk_ge_4 ha
  rw [show ∑ j : Fin k, exponent k cov.a (j.val + 1) p =
      ∑ j : Fin k, (if (j.val + 1) % p = cov.a p then 1 else 0) from
    Finset.sum_congr rfl (fun j _ => h_exp_eq j)]
  have hap_pos : 1 ≤ cov.a p := by omega
  have hsum_eq_card :
      ∑ j : Fin k, (if (j.val + 1) % p = cov.a p then 1 else 0) =
      ((Finset.Icc 1 k).filter (fun x => x % p = cov.a p)).card := by
    classical
    rw [Finset.card_filter]
    rw [show (Finset.Icc 1 k) =
        (Finset.univ : Finset (Fin k)).image (fun j : Fin k => j.val + 1) from ?_]
    · rw [Finset.sum_image]
      intros a _ b _ hab
      apply Fin.ext
      show a.val = b.val
      simp at hab; omega
    · ext x
      simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_Icc]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨⟨x - 1, by omega⟩, by simp; omega⟩
      · rintro ⟨j, rfl⟩
        exact ⟨Nat.succ_pos _, j.isLt⟩
  rw [hsum_eq_card]
  rw [count_residue_large_prime k p (cov.a p) hp.pos hp_gt hpk hap_pos hap_lt_p]
  rw [padicValNat_factorial_eq_one_of_gt_half hp hpk hp_gt]
  by_cases hexcess : p ∈ excessPrimesSet k cov.a
  · rw [if_pos hexcess]
    rw [if_pos]
    have hex := (mem_excessPrimesSet.mp hexcess).2.2.2.2.2.2
    omega
  · rw [if_neg hexcess]
    rw [if_neg]
    intro h_ap_pk
    apply hexcess
    rw [mem_excessPrimesSet]
    refine ⟨hp, hp.pos, hpk, ha, hp_gt, hap_pos, ?_⟩
    omega

theorem q_notin_excessPrimesSet {m k : ℕ} (cov : CoverData m k) (hm : 3 ≤ m) :
    cov.q ∉ excessPrimesSet k cov.a := by
  rw [mem_excessPrimesSet]
  rintro ⟨_, _, _, _, hk2_lt, _, _⟩
  have h := q_le_k_half cov hm
  omega

theorem liftAtLevel_nested (a : ℕ → ℕ) (p u : ℕ) (hp : 1 < p) (hap_lt_p : a p < p) :
    liftAtLevel a p (u + 1) % p ^ u = liftAtLevel a p u % p ^ u := by
  by_cases ha : a p = 0
  · unfold liftAtLevel
    rw [if_pos ha, if_pos ha]
  · unfold liftAtLevel
    rw [if_neg ha, if_neg ha]
    by_cases hu_zero : u = 0
    · subst hu_zero
      simp [Nat.mod_one]
    · by_cases hu_one : u = 1
      · subst hu_one
        rw [if_neg (by omega : (1 : ℕ) ≠ 0), if_pos rfl]
        rw [if_neg (by omega : (2 : ℕ) ≠ 0), if_neg (by omega : (2 : ℕ) ≠ 1)]
        rw [pow_one]
        have hap_pos : 1 ≤ a p := Nat.one_le_iff_ne_zero.mpr ha
        have h_lift_mod : liftAbove p 2 (a p) % p = a p :=
          liftAbove_mod_p p 2 (a p) hp hap_lt_p (by omega)
        rw [h_lift_mod]
        exact (Nat.mod_eq_of_lt hap_lt_p).symm
      · have hu_ge_2 : 2 ≤ u := by omega
        rw [if_neg (by omega : u + 1 ≠ 0), if_neg (by omega : u + 1 ≠ 1)]
        rw [if_neg hu_zero, if_neg hu_one]
        exact liftAbove_nested p u (a p) (by omega)

theorem liftAtLevel_lt_pow (a : ℕ → ℕ) (p u : ℕ) (hp : 1 < p) (hap_pos : 1 ≤ a p)
    (hap_lt_p : a p < p) :
    liftAtLevel a p u < p ^ u := by
  unfold liftAtLevel
  have ha_ne : a p ≠ 0 := by omega
  rw [if_neg ha_ne]
  rcases Nat.eq_zero_or_pos u with hu0 | hu_pos
  · subst hu0
    rw [if_pos rfl, pow_zero]
    omega
  · rw [if_neg (by omega : u ≠ 0)]
    by_cases hu1 : u = 1
    · subst hu1
      rw [if_pos rfl, pow_one]; exact hap_lt_p
    · rw [if_neg hu1]
      exact liftAbove_lt hp hap_pos hap_lt_p (by omega)

theorem cond_downward (k : ℕ) (a : ℕ → ℕ) (j p u : ℕ) (hp : 1 < p) (hap_pos : 1 ≤ a p)
    (hap_lt_p : a p < p) (hu_pos : 1 ≤ u)
    (hcond : j % p ^ u = liftAtLevel a p u) :
    j % p ^ (u - 1) = liftAtLevel a p (u - 1) := by
  have hu_eq : u - 1 + 1 = u := by omega
  have h_pow_dvd : p ^ (u - 1) ∣ p ^ u := pow_dvd_pow p (by omega)
  have h_mod_pow : j % p ^ u % p ^ (u - 1) = j % p ^ (u - 1) :=
    Nat.mod_mod_of_dvd j h_pow_dvd
  rw [← h_mod_pow, hcond]
  have h_nested : liftAtLevel a p u % p ^ (u - 1) = liftAtLevel a p (u - 1) % p ^ (u - 1) := by
    conv_lhs => rw [← hu_eq]
    exact liftAtLevel_nested a p (u - 1) hp hap_lt_p
  rw [h_nested]
  apply Nat.mod_eq_of_lt
  exact liftAtLevel_lt_pow a p (u - 1) hp hap_pos hap_lt_p

theorem cond_downward_iter (k : ℕ) (a : ℕ → ℕ) (j p : ℕ) (hp : 1 < p)
    (hap_pos : 1 ≤ a p) (hap_lt_p : a p < p) {u v : ℕ} (hvu : v ≤ u)
    (hcond : j % p ^ u = liftAtLevel a p u) :
    j % p ^ v = liftAtLevel a p v := by
  induction u with
  | zero =>
    interval_cases v
    exact hcond
  | succ n ih =>
    by_cases hv_eq : v = n + 1
    · subst hv_eq; exact hcond
    · have hvn : v ≤ n := by omega
      apply ih hvn
      have h := cond_downward k a j p (n + 1) hp hap_pos hap_lt_p (by omega) hcond
      have hn_eq : n + 1 - 1 = n := by omega
      rw [hn_eq] at h
      exact h

theorem le_exponent_iff_cond {k : ℕ} (a : ℕ → ℕ) (j p u : ℕ) (hp : p.Prime)
    (hap_pos : 1 ≤ a p) (hap_lt_p : a p < p)
    (hu_pos : 1 ≤ u) (hu_le : u ≤ alphaP k p) :
    u ≤ exponent k a j p ↔ j % p ^ u = liftAtLevel a p u := by
  have ha_ne : a p ≠ 0 := by omega
  constructor
  · intro hu_le_exp
    unfold exponent at hu_le_exp
    rw [if_neg ha_ne] at hu_le_exp
    have : ∃ v ∈ Finset.Icc 0 (alphaP k p),
        u ≤ (if j % p ^ v = liftAtLevel a p v then v else 0) := by
      by_contra h_no
      push_neg at h_no
      have hu_pos' : (⊥ : ℕ) < u := by exact hu_pos
      have h_sup_lt : (Finset.Icc 0 (alphaP k p)).sup
          (fun v => if j % p ^ v = liftAtLevel a p v then v else 0) < u := by
        rw [Finset.sup_lt_iff hu_pos']
        intro v hv
        have := h_no v hv
        omega
      omega
    obtain ⟨v, hv_mem, hv_le⟩ := this
    have hv_cond : j % p ^ v = liftAtLevel a p v := by
      by_contra h
      rw [if_neg h] at hv_le
      omega
    rw [if_pos hv_cond] at hv_le
    rw [Finset.mem_Icc] at hv_mem
    exact cond_downward_iter k a j p hp.one_lt hap_pos hap_lt_p hv_le hv_cond
  · intro hcond
    unfold exponent
    rw [if_neg ha_ne]
    have h_mem : u ∈ Finset.Icc 0 (alphaP k p) :=
      Finset.mem_Icc.mpr ⟨Nat.zero_le _, hu_le⟩
    have hle := Finset.le_sup (f := fun v =>
      if j % p ^ v = liftAtLevel a p v then v else 0) h_mem
    simpa [hcond] using hle

theorem nat_eq_sum_indicator_le {α : ℕ} {n : ℕ} (hn : n ≤ α) :
    n = ∑ u ∈ Finset.Icc 1 α, (if u ≤ n then 1 else 0) := by
  classical
  rw [Finset.sum_boole]
  have hset : (Finset.Icc 1 α).filter (fun u => u ≤ n) = Finset.Icc 1 n := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  rw [hset, Nat.card_Icc]
  cases n with
  | zero => simp
  | succ m => simp

theorem tail_sum_identity {k α : ℕ} (f : Fin k → ℕ) (h_bound : ∀ j, f j ≤ α) :
    ∑ j : Fin k, f j =
      ∑ u ∈ Finset.Icc 1 α,
        ((Finset.univ : Finset (Fin k)).filter (fun j => u ≤ f j)).card := by
  classical
  conv_lhs =>
    rw [show ∑ j : Fin k, f j = ∑ j : Fin k,
        ∑ u ∈ Finset.Icc 1 α, (if u ≤ f j then 1 else 0) from
      Finset.sum_congr rfl (fun j _ => nat_eq_sum_indicator_le (h_bound j))]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  rw [Finset.sum_boole]
  rfl

theorem exponent_le_alphaP_general (k : ℕ) (a : ℕ → ℕ) (j p : ℕ) (hp : p.Prime)
    (hpk : p ≤ k) (hj_pos : 0 < j) (hj_le : j ≤ k) :
    exponent k a j p ≤ alphaP k p := by
  unfold exponent
  split_ifs with hap
  · have hk_pos : 0 < k := lt_of_lt_of_le hj_pos hj_le
    have hpj_dvd : p ^ padicValNat p j ∣ j := pow_padicValNat_dvd
    have hpj_le : p ^ padicValNat p j ≤ j := Nat.le_of_dvd hj_pos hpj_dvd
    have hpj_le_k : p ^ padicValNat p j ≤ k := le_trans hpj_le hj_le
    rw [alphaP]
    exact (Nat.le_log_iff_pow_le hp.one_lt hk_pos.ne').mpr hpj_le_k
  · refine Finset.sup_le ?_
    intro u hu
    split_ifs
    · exact (Finset.mem_Icc.mp hu).2
    · exact Nat.zero_le _

theorem sum_exponent_eq_sum_count {k : ℕ} (a : ℕ → ℕ) (p : ℕ) (hp : p.Prime)
    (hap_pos : 1 ≤ a p) (hap_lt_p : a p < p) (hpk : p ≤ k) :
    ∑ j : Fin k, exponent k a (j.val + 1) p =
      ∑ u ∈ Finset.Icc 1 (alphaP k p),
        ((Finset.univ : Finset (Fin k)).filter
          (fun j => (j.val + 1) % p ^ u = liftAtLevel a p u)).card := by
  classical
  rw [tail_sum_identity (f := fun j => exponent k a (j.val + 1) p) (α := alphaP k p) ?_]
  · apply Finset.sum_congr rfl
    intro u hu
    rw [Finset.mem_Icc] at hu
    congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact le_exponent_iff_cond (k := k) a (j.val + 1) p u hp hap_pos hap_lt_p hu.1 hu.2
  · intro j
    have hjp_pos : 0 < j.val + 1 := Nat.succ_pos _
    have hjle : j.val + 1 ≤ k := j.isLt
    exact exponent_le_alphaP_general k a (j.val + 1) p hp hpk hjp_pos hjle

theorem card_Fin_filter_eq_Icc_filter {k : ℕ} (P : ℕ → Prop) [DecidablePred P] :
    ((Finset.univ : Finset (Fin k)).filter (fun j => P (j.val + 1))).card =
    ((Finset.Icc 1 k).filter P).card := by
  classical
  rw [show (Finset.Icc 1 k) =
      (Finset.univ : Finset (Fin k)).image (fun j : Fin k => j.val + 1) from ?_]
  · rw [Finset.filter_image]
    rw [Finset.card_image_of_injOn]
    intros a _ b _ hab
    apply Fin.ext
    show a.val = b.val
    simp at hab; omega
  · ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_Icc]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨⟨x - 1, by omega⟩, by simp; omega⟩
    · rintro ⟨j, rfl⟩
      exact ⟨Nat.succ_pos _, j.isLt⟩

theorem liftAtLevel_eq_liftAbove (a : ℕ → ℕ) (p u : ℕ) (ha : a p ≠ 0) (hu_pos : 1 ≤ u) :
    liftAtLevel a p u = liftAbove p u (a p) := by
  unfold liftAtLevel
  rw [if_neg ha, if_neg (by omega : u ≠ 0)]
  by_cases hu_one : u = 1
  · subst hu_one
    rw [if_pos rfl]
    unfold liftAbove
    rw [pow_one]; omega
  · rw [if_neg hu_one]

theorem val_sum_innerB_anchor {m k : ℕ} (hm : 3 ≤ m) (cov : CoverData m k)
    (ha : cov.a cov.q ≠ 0) :
    ∑ j : Fin k, exponent k cov.a (j.val + 1) cov.q =
      padicValNat cov.q k.factorial := by
  classical
  have : Fact cov.q.Prime := ⟨cov.q_prime⟩
  have hq_prime := cov.q_prime
  have hq_pos : 0 < cov.q := hq_prime.pos
  have hap_lt_p : cov.a cov.q < cov.q := cov.a_lt_p cov.q hq_prime
  have hap_pos : 1 ≤ cov.a cov.q := by omega
  have hq_le_k_half := q_le_k_half cov hm
  have hk_pos : 0 < k := by
    have := cov.k_ge_4m; omega
  have hq_le_k : cov.q ≤ k := by
    have := q_le_k_half cov hm
    have := Nat.div_le_self k 2
    omega
  rw [sum_exponent_eq_sum_count cov.a cov.q hq_prime hap_pos hap_lt_p hq_le_k]
  have h_count_eq : ∀ u ∈ Finset.Icc 1 (alphaP k cov.q),
      ((Finset.univ : Finset (Fin k)).filter
        (fun j => (j.val + 1) % cov.q ^ u = liftAtLevel cov.a cov.q u)).card =
        k / cov.q ^ u := by
    intro u hu_mem
    rw [Finset.mem_Icc] at hu_mem
    have hu_pos := hu_mem.1
    have hu_le : u ≤ Nat.log cov.q k := hu_mem.2
    have h_lift_eq : liftAtLevel cov.a cov.q u = liftAbove cov.q u (cov.a cov.q) :=
      liftAtLevel_eq_liftAbove cov.a cov.q u ha hu_pos
    rw [h_lift_eq]
    rw [card_Fin_filter_eq_Icc_filter (fun x => x % cov.q ^ u = liftAbove cov.q u (cov.a cov.q))]
    exact valuation_sum_non_excess_lift cov.q k cov.q_dvd_k
      (cov.a cov.q) hap_pos hap_lt_p hk_pos u (Finset.mem_Icc.mpr ⟨hu_pos, hu_le⟩)
  rw [Finset.sum_congr rfl h_count_eq]
  have h_log_lt : Nat.log cov.q k < Nat.log cov.q k + 1 := Nat.lt_succ_self _
  rw [padicValNat_factorial (b := Nat.log cov.q k + 1) h_log_lt]
  apply Finset.sum_bij (fun (x : ℕ) (_ : x ∈ Finset.Icc 1 (alphaP k cov.q)) => x)
  · intro x hx
    rw [Finset.mem_Icc] at hx
    rw [Finset.mem_Ico]
    refine ⟨hx.1, ?_⟩
    have : alphaP k cov.q = Nat.log cov.q k := rfl
    omega
  · intros; assumption
  · intro x hx
    rw [Finset.mem_Ico] at hx
    refine ⟨x, ?_, rfl⟩
    rw [Finset.mem_Icc]
    refine ⟨hx.1, ?_⟩
    have : alphaP k cov.q = Nat.log cov.q k := rfl
    omega
  · intros; rfl

theorem val_sum_innerB_a_nonzero {m k : ℕ} (hm : 3 ≤ m) (cov : CoverData m k) (p : ℕ)
    (hp : p.Prime) (hpk : p ≤ k) (ha : cov.a p ≠ 0) :
    ∑ j : Fin k, exponent k cov.a (j.val + 1) p =
      padicValNat p k.factorial +
        (if p ∈ excessPrimesSet k cov.a then 1 else 0) := by
  by_cases hp_gt : k / 2 < p
  · exact val_sum_innerB_scaffold cov p hp hpk hp_gt ha
  · push_neg at hp_gt
    have hp_eq_q : p = cov.q := prime_a_nonzero_small_eq_q cov p hp ha hp_gt
    subst hp_eq_q
    rw [if_neg (q_notin_excessPrimesSet cov hm), Nat.add_zero]
    exact val_sum_innerB_anchor hm cov ha

theorem val_sum_innerB {m k : ℕ} (hm : 3 ≤ m) (cov : CoverData m k) (p : ℕ)
    (hp : p.Prime) (hpk : p ≤ k) :
    ∑ j : Fin k, exponent k cov.a (j.val + 1) p =
      padicValNat p k.factorial +
        (if p ∈ excessPrimesSet k cov.a then 1 else 0) := by
  by_cases ha : cov.a p = 0
  · exact val_sum_innerB_a_zero cov p hp ha
  · exact val_sum_innerB_a_nonzero hm cov p hp hpk ha

theorem excessPrimesSet_prime {k : ℕ} {a : ℕ → ℕ} {p : ℕ}
    (hp : p ∈ excessPrimesSet k a) : p.Prime :=
  (mem_excessPrimesSet.mp hp).1

theorem prod_innerB_eq_factorial_mul_excess {m k : ℕ} (hm : 3 ≤ m) (hk : 3 ≤ k)
    (cov : CoverData m k) :
    ∏ j : Fin k, innerB k cov.a (j.val + 1) =
      k.factorial * ∏ p ∈ excessPrimesSet k cov.a, p :=
  prod_innerB_eq_factorial_mul_excess_from_val_sum hk cov (val_sum_innerB hm cov)

theorem prod_outerB_eq_factorial {m k : ℕ} (hm : 3 ≤ m) (hk : 3 ≤ k)
    (cov : CoverData m k) :
    ∏ j : Fin k, outerB k cov.a (j.val + 1) = k.factorial :=
  prod_outerB_eq_factorial_from_innerB cov
    (prod_innerB_eq_factorial_mul_excess hm hk cov)

theorem exponent_le_alphaP {m k : ℕ} (cov : CoverData m k) (j p : ℕ) (hp : p.Prime)
    (hpk : p ≤ k) (hj_pos : 0 < j) (hj_le : j ≤ k) :
    exponent k cov.a j p ≤ alphaP k p := by
  unfold exponent
  split_ifs with hap
  · have hk_pos : 0 < k := lt_of_lt_of_le hj_pos hj_le
    have hpj_dvd : p ^ padicValNat p j ∣ j := pow_padicValNat_dvd
    have hpj_le : p ^ padicValNat p j ≤ j := Nat.le_of_dvd hj_pos hpj_dvd
    have hpj_le_k : p ^ padicValNat p j ≤ k := le_trans hpj_le hj_le
    rw [alphaP]
    exact (Nat.le_log_iff_pow_le hp.one_lt hk_pos.ne').mpr hpj_le_k
  · refine Finset.sup_le ?_
    intro u hu
    split_ifs
    · exact (Finset.mem_Icc.mp hu).2
    · exact Nat.zero_le _

theorem innerB_dvd_globalMk_of_a {k : ℕ} (a : ℕ → ℕ) (j : ℕ) (hj : 1 ≤ j) (hjk : j ≤ k) :
    innerB k a j ∣ globalMk k := by
  unfold innerB globalMk
  apply Finset.prod_dvd_prod_of_dvd
  intro p hp
  rw [Finset.mem_filter, Finset.mem_Icc] at hp
  obtain ⟨⟨_, hpk⟩, hpp⟩ := hp
  have hexp_le := exponent_le_alphaP_general k a j p hpp hpk hj hjk
  exact Nat.pow_dvd_pow p (Nat.le_succ_of_le hexp_le)

theorem outerB_dvd_globalMk_of_a {k : ℕ} (a : ℕ → ℕ) (j : ℕ) (hj : 1 ≤ j) (hjk : j ≤ k) :
    outerB k a j ∣ globalMk k := by
  unfold outerB
  have hdvd_inner := innerB_dvd_globalMk_of_a a j hj hjk
  have hsc_dvd := scaffold_dvd_innerB k a j
  rcases hsc_dvd with ⟨c, hc⟩
  rw [hc]
  rw [Nat.mul_div_cancel_left _ (scaffold_prod_pos k a j)]
  rcases hdvd_inner with ⟨d, hd⟩
  rw [hc] at hd
  refine ⟨(∏ p ∈ scaffoldExcess k a j, p) * d, ?_⟩
  linarith

theorem outerB_dvd_globalMk {m k : ℕ} (hk : 3 ≤ k) (cov : CoverData m k) (j : Fin k) :
    outerB k cov.a (j.val + 1) ∣ globalMk k :=
  outerB_dvd_globalMk_of_a cov.a (j.val + 1) (Nat.succ_pos _) j.isLt

theorem p_mul_innerB_dvd_globalMk {m k : ℕ} (cov : CoverData m k) (j : ℕ)
    (hjpos : 0 < j) (hjle : j ≤ k)
    (p : ℕ) (hp : p.Prime) (hpk : p ≤ k) :
    p * innerB k cov.a j ∣ globalMk k := by
  classical
  unfold innerB globalMk
  set S := (Finset.Icc 1 k).filter Nat.Prime with hSdef
  have hp_mem : p ∈ S := by
    rw [hSdef, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hp.one_lt.le, hpk⟩, hp⟩
  rw [← Finset.mul_prod_erase S (fun q => q ^ exponent k cov.a j q) hp_mem]
  rw [← Finset.mul_prod_erase S (fun q => q ^ (alphaP k q + 1)) hp_mem]
  have hassoc : p * (p ^ exponent k cov.a j p *
        ∏ q ∈ S.erase p, q ^ exponent k cov.a j q) =
      p ^ (exponent k cov.a j p + 1) *
        ∏ q ∈ S.erase p, q ^ exponent k cov.a j q := by
    rw [pow_succ]; ring
  rw [hassoc]
  apply mul_dvd_mul
  · apply Nat.pow_dvd_pow
    have he := exponent_le_alphaP cov j p hp hpk hjpos hjle
    omega
  · apply Finset.prod_dvd_prod_of_dvd
    intro q hq
    rw [Finset.mem_erase] at hq
    have hq_in : q ∈ S := hq.2
    have hq_prime : q.Prime := (Finset.mem_filter.mp hq_in).2
    have hq_le : q ≤ k := (Finset.mem_Icc.mp (Finset.mem_filter.mp hq_in).1).2
    apply Nat.pow_dvd_pow
    have heq := exponent_le_alphaP cov j q hq_prime hq_le hjpos hjle
    omega

theorem globalMk_mul_outerB_dvd {m k : ℕ} (hk : 3 ≤ k) (cov : CoverData m k)
    (j : Fin k) (p : ℕ) (hp : p.Prime) (hpk : p ≤ k) :
    p * outerB k cov.a (j.val + 1) ∣ globalMk k := by
  have houter_inner : outerB k cov.a (j.val + 1) ∣ innerB k cov.a (j.val + 1) := by
    unfold outerB
    have hdvd := scaffold_dvd_innerB k cov.a (j.val + 1)
    rcases hdvd with ⟨c, hc⟩
    refine ⟨∏ p' ∈ scaffoldExcess k cov.a (j.val + 1), p', ?_⟩
    rw [hc]
    rw [Nat.mul_div_cancel_left _ (scaffold_prod_pos k cov.a (j.val + 1))]
    ring
  have hjpos : 0 < j.val + 1 := Nat.succ_pos _
  have hjle : j.val + 1 ≤ k := j.isLt
  have hp_inner := p_mul_innerB_dvd_globalMk cov (j.val + 1) hjpos hjle p hp hpk
  exact dvd_trans (mul_dvd_mul_left p houter_inner) hp_inner

theorem globalMk_smooth (k : ℕ) (p : ℕ) (hp : p.Prime) (hp_dvd : p ∣ globalMk k) :
    p ≤ k := by
  unfold globalMk at hp_dvd
  classical
  obtain ⟨q, hq_mem, hp_dvd_q⟩ :=
    (Prime.dvd_finset_prod_iff hp.prime _).mp hp_dvd
  rw [Finset.mem_filter, Finset.mem_Icc] at hq_mem
  have hq_prime : q.Prime := hq_mem.2
  have hp_eq_q : p = q := by
    have := (Nat.Prime.dvd_of_dvd_pow hp hp_dvd_q)
    exact (Nat.prime_dvd_prime_iff_eq hp hq_prime).mp this
  rw [hp_eq_q]; exact hq_mem.1.2

theorem exponent_pos_cong_at_one {m k : ℕ} (cov : CoverData m k) (j p : ℕ)
    (hp : p.Prime) (hpk : p ≤ k) (hj_pos : 0 < j) (hj_le : j ≤ k)
    (he_pos : 1 ≤ exponent k cov.a j p) :
    j % p = if cov.a p = 0 then 0 else cov.a p := by
  by_cases ha : cov.a p = 0
  · rw [if_pos ha]
    have : Fact p.Prime := ⟨hp⟩
    have hexp : exponent k cov.a j p = padicValNat p j := by
      unfold exponent; rw [if_pos ha]
    rw [hexp] at he_pos
    have hpj : p ∣ j := dvd_of_one_le_padicValNat he_pos
    exact Nat.mod_eq_zero_of_dvd hpj
  · rw [if_neg ha]
    have hap_lt_p : cov.a p < p := cov.a_lt_p p hp
    have hap_pos : 1 ≤ cov.a p := by omega
    have h_alpha_pos : 1 ≤ alphaP k p := by
      unfold alphaP
      have hk_pos : 0 < k := lt_of_lt_of_le hj_pos hj_le
      have hp_pow_one : p ^ 1 ≤ k := by rw [pow_one]; exact hpk
      exact (Nat.le_log_iff_pow_le hp.one_lt hk_pos.ne').mpr hp_pow_one
    have h_cond := (le_exponent_iff_cond cov.a j p 1 hp hap_pos hap_lt_p (by omega)
      h_alpha_pos).mp he_pos
    rw [pow_one, liftAtLevel_one cov.a p ha] at h_cond
    exact h_cond

theorem prime_dvd_outerB_implies_exponent_pos {m k : ℕ} (hk : 3 ≤ k) (cov : CoverData m k)
    (j : Fin k) (p : ℕ) (hp : p.Prime) (hpdvd : p ∣ outerB k cov.a (j.val + 1)) :
    p ≤ k ∧ 1 ≤ exponent k cov.a (j.val + 1) p := by
  have hp_le_k : p ≤ k :=
    globalMk_smooth k p hp (dvd_trans hpdvd (outerB_dvd_globalMk hk cov j))
  refine ⟨hp_le_k, ?_⟩
  have hp_dvd_innerB : p ∣ innerB k cov.a (j.val + 1) :=
    dvd_trans hpdvd (outerB_dvd_innerB k cov.a (j.val + 1))
  have h_fact_pos : 0 < (innerB k cov.a (j.val + 1)).factorization p :=
    Nat.Prime.factorization_pos_of_dvd hp (innerB_pos k cov.a _).ne' hp_dvd_innerB
  rw [factorization_innerB_eq_exponent k cov.a (j.val + 1) p hp hp_le_k] at h_fact_pos
  exact h_fact_pos

theorem exponent_ge_implies_mod_eq {m k : ℕ} (cov : CoverData m k) (i j p u : ℕ)
    (hp : p.Prime) (hu_le : u ≤ alphaP k p)
    (hei : u ≤ exponent k cov.a i p) (hej : u ≤ exponent k cov.a j p) :
    i % p ^ u = j % p ^ u := by
  by_cases hu0 : u = 0
  · subst hu0; simp [Nat.mod_one]
  · have hu_pos : 1 ≤ u := by omega
    by_cases ha : cov.a p = 0
    · have hexp_i : exponent k cov.a i p = padicValNat p i := by
        unfold exponent; rw [if_pos ha]
      have hexp_j : exponent k cov.a j p = padicValNat p j := by
        unfold exponent; rw [if_pos ha]
      rw [hexp_i] at hei
      rw [hexp_j] at hej
      have : Fact p.Prime := ⟨hp⟩
      have hpi : p ^ u ∣ i := dvd_trans (pow_dvd_pow p hei) pow_padicValNat_dvd
      have hpj : p ^ u ∣ j := dvd_trans (pow_dvd_pow p hej) pow_padicValNat_dvd
      rw [Nat.mod_eq_zero_of_dvd hpi, Nat.mod_eq_zero_of_dvd hpj]
    · have hap_lt_p : cov.a p < p := cov.a_lt_p p hp
      have hap_pos : 1 ≤ cov.a p := by omega
      have hi_cond := (le_exponent_iff_cond cov.a i p u hp hap_pos hap_lt_p hu_pos hu_le).mp hei
      have hj_cond := (le_exponent_iff_cond cov.a j p u hp hap_pos hap_lt_p hu_pos hu_le).mp hej
      rw [hi_cond, hj_cond]

theorem mod_eq_implies_int_dvd_diff (i j p u : ℕ) (h_eq : i % p ^ u = j % p ^ u) :
    ((p ^ u : ℕ) : ℤ) ∣ ((i : ℤ) - (j : ℤ)) := by
  rcases Nat.lt_or_ge i j with hlt | hle
  · have hdvd : p ^ u ∣ j - i := (Nat.modEq_iff_dvd' hlt.le).mp h_eq
    have h_int : ((p ^ u : ℕ) : ℤ) ∣ ((j - i : ℕ) : ℤ) := by exact_mod_cast hdvd
    have h_arith : ((j - i : ℕ) : ℤ) = (j : ℤ) - (i : ℤ) := by
      push_cast [Nat.sub_add_cancel hlt.le]; omega
    rw [h_arith] at h_int
    have := dvd_neg.mpr h_int
    have h_neg : -((j : ℤ) - (i : ℤ)) = (i : ℤ) - (j : ℤ) := by ring
    rw [h_neg] at this
    exact this
  · have hdvd : p ^ u ∣ i - j := (Nat.modEq_iff_dvd' hle).mp h_eq.symm
    have h_int : ((p ^ u : ℕ) : ℤ) ∣ ((i - j : ℕ) : ℤ) := by exact_mod_cast hdvd
    have h_arith : ((i - j : ℕ) : ℤ) = (i : ℤ) - (j : ℤ) := by
      push_cast [Nat.sub_add_cancel hle]; omega
    rwa [h_arith] at h_int

theorem exponent_ge_implies_int_dvd {m k : ℕ} (cov : CoverData m k) (i j p u : ℕ)
    (hp : p.Prime) (hu_le : u ≤ alphaP k p)
    (hei : u ≤ exponent k cov.a i p) (hej : u ≤ exponent k cov.a j p) :
    ((p ^ u : ℕ) : ℤ) ∣ ((i : ℤ) - (j : ℤ)) :=
  mod_eq_implies_int_dvd_diff i j p u
    (exponent_ge_implies_mod_eq cov i j p u hp hu_le hei hej)

theorem outerB_factorization_le_exponent_of_a {k : ℕ} (a : ℕ → ℕ) (j : ℕ)
    (hj : 1 ≤ j) (hjk : j ≤ k) (p : ℕ) (hp : p.Prime) :
    (outerB k a j).factorization p ≤ exponent k a j p := by
  by_cases hpk : p ≤ k
  · have h_outerB_dvd : outerB k a j ∣ innerB k a j := outerB_dvd_innerB k a j
    have h_outerB_ne : outerB k a j ≠ 0 := (outerB_pos_of_a a j hj hjk).ne'
    have h_innerB_ne : innerB k a j ≠ 0 := (innerB_pos k a _).ne'
    have h_fact_le : (outerB k a j).factorization ≤ (innerB k a j).factorization :=
      (Nat.factorization_le_iff_dvd h_outerB_ne h_innerB_ne).mpr h_outerB_dvd
    have h_fact_le_p : (outerB k a j).factorization p ≤ (innerB k a j).factorization p := h_fact_le p
    rw [factorization_innerB_eq_exponent k a j p hp hpk] at h_fact_le_p
    exact h_fact_le_p
  · push_neg at hpk
    have h_fact_zero : (outerB k a j).factorization p = 0 := by
      rw [Nat.factorization_eq_zero_iff]
      right; left
      intro hdvd
      have h_gMk : p ∣ globalMk k := dvd_trans hdvd (outerB_dvd_globalMk_of_a a j hj hjk)
      have := globalMk_smooth k p hp h_gMk
      omega
    rw [h_fact_zero]
    exact Nat.zero_le _

theorem outerB_factorization_le_exponent {m k : ℕ} (hk : 3 ≤ k) (cov : CoverData m k)
    (j : Fin k) (p : ℕ) (hp : p.Prime) :
    (outerB k cov.a (j.val + 1)).factorization p ≤ exponent k cov.a (j.val + 1) p :=
  outerB_factorization_le_exponent_of_a cov.a (j.val + 1) (Nat.succ_pos _) j.isLt p hp

theorem outerB_gcd_factorization_le_exponent {m k : ℕ} (hk : 3 ≤ k) (cov : CoverData m k)
    (i j : Fin k) (p : ℕ) (hp : p.Prime) :
    (Nat.gcd (outerB k cov.a (i.val + 1)) (outerB k cov.a (j.val + 1))).factorization p ≤
      exponent k cov.a (i.val + 1) p ∧
    (Nat.gcd (outerB k cov.a (i.val + 1)) (outerB k cov.a (j.val + 1))).factorization p ≤
      exponent k cov.a (j.val + 1) p := by
  have hi_ne : outerB k cov.a (i.val + 1) ≠ 0 := (outerB_pos hk cov i).ne'
  have hj_ne : outerB k cov.a (j.val + 1) ≠ 0 := (outerB_pos hk cov j).ne'
  rw [Nat.factorization_gcd hi_ne hj_ne, Finsupp.inf_apply]
  refine ⟨?_, ?_⟩
  · exact le_trans (min_le_left _ _) (outerB_factorization_le_exponent hk cov i p hp)
  · exact le_trans (min_le_right _ _) (outerB_factorization_le_exponent hk cov j p hp)

theorem outerB_gcd_pow_dvd_diff_at_prime {m k : ℕ} (hk : 3 ≤ k) (cov : CoverData m k)
    (i j : Fin k) (p : ℕ) (hp : p.Prime) :
    ((p ^ (Nat.gcd (outerB k cov.a (i.val + 1)) (outerB k cov.a (j.val + 1))).factorization p : ℕ)
      : ℤ) ∣ ((i.val : ℤ) - (j.val : ℤ)) := by
  obtain ⟨hi, hj⟩ := outerB_gcd_factorization_le_exponent hk cov i j p hp
  set u := (Nat.gcd (outerB k cov.a (i.val + 1)) (outerB k cov.a (j.val + 1))).factorization p
  have hu_le_alpha : u ≤ alphaP k p := by
    have hi_pos : 0 < i.val + 1 := Nat.succ_pos _
    have hi_le : i.val + 1 ≤ k := i.isLt
    by_cases hpk : p ≤ k
    · exact le_trans hi (exponent_le_alphaP_general k cov.a (i.val + 1) p hp hpk hi_pos hi_le)
    · push_neg at hpk
      have h_outerB_fact_zero : (outerB k cov.a (i.val + 1)).factorization p = 0 := by
        rw [Nat.factorization_eq_zero_iff]
        right; left; intro hdvd
        have h_gMk : p ∣ globalMk k :=
          dvd_trans hdvd (outerB_dvd_globalMk hk cov i)
        have := globalMk_smooth k p hp h_gMk
        omega
      have hu_le_outerB :
          u ≤ (outerB k cov.a (i.val + 1)).factorization p := by
        show u ≤ _
        have hi_ne : outerB k cov.a (i.val + 1) ≠ 0 := (outerB_pos hk cov i).ne'
        have hj_ne : outerB k cov.a (j.val + 1) ≠ 0 := (outerB_pos hk cov j).ne'
        rw [show u = (Nat.gcd (outerB k cov.a (i.val + 1))
              (outerB k cov.a (j.val + 1))).factorization p from rfl]
        rw [Nat.factorization_gcd hi_ne hj_ne, Finsupp.inf_apply]
        exact min_le_left _ _
      rw [h_outerB_fact_zero] at hu_le_outerB
      omega
  have := exponent_ge_implies_int_dvd cov (i.val + 1) (j.val + 1) p u hp hu_le_alpha hi hj
  have h_arith : ((i.val + 1 : ℕ) : ℤ) - ((j.val + 1 : ℕ) : ℤ) = (i.val : ℤ) - (j.val : ℤ) := by
    push_cast; ring
  rw [h_arith] at this
  exact this

theorem outerB_gcd_dvd_diff {m k : ℕ} (hk : 3 ≤ k) (cov : CoverData m k) (i j : Fin k) :
    ((Nat.gcd (outerB k cov.a (i.val + 1)) (outerB k cov.a (j.val + 1)) : ℕ) : ℤ) ∣
      ((i.val : ℤ) - (j.val : ℤ)) := by
  by_cases hij : i = j
  · subst hij; simp
  set g := Nat.gcd (outerB k cov.a (i.val + 1)) (outerB k cov.a (j.val + 1)) with hg_def
  have hi_ne : outerB k cov.a (i.val + 1) ≠ 0 := (outerB_pos hk cov i).ne'
  have hj_ne : outerB k cov.a (j.val + 1) ≠ 0 := (outerB_pos hk cov j).ne'
  have hg_ne : g ≠ 0 := by
    intro h; rw [hg_def] at h
    rcases Nat.gcd_eq_zero_iff.mp h with ⟨h1, _⟩
    exact hi_ne h1
  have hdiff_ne : (i.val : ℤ) - (j.val : ℤ) ≠ 0 := by
    intro h; apply hij; apply Fin.ext
    have : (i.val : ℤ) = (j.val : ℤ) := by linarith
    exact_mod_cast this
  set n := ((i.val : ℤ) - (j.val : ℤ)).natAbs with hn_def
  have hn_ne : n ≠ 0 := Int.natAbs_ne_zero.mpr hdiff_ne
  have h_g_dvd_n : g ∣ n := by
    rw [← Nat.factorization_le_iff_dvd hg_ne hn_ne]
    intro p
    by_cases hp : p.Prime
    · have h_pow_dvd_int := outerB_gcd_pow_dvd_diff_at_prime hk cov i j p hp
      have h_pow_dvd_n : p ^ g.factorization p ∣ n := by
        rw [hn_def]
        exact Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr h_pow_dvd_int)
      exact (Nat.Prime.pow_dvd_iff_le_factorization hp hn_ne).mp h_pow_dvd_n
    · rw [Nat.factorization_eq_zero_of_not_prime _ hp]
      exact Nat.zero_le _
  have h_int : (g : ℤ) ∣ (n : ℤ) := Int.natCast_dvd_natCast.mpr h_g_dvd_n
  rw [hn_def] at h_int
  exact Int.dvd_natAbs.mp h_int

theorem outerB_residues_compat_modEq {m k : ℕ} (hk : 3 ≤ k) (cov : CoverData m k) (i j : Fin k) :
    (k - (i.val + 1)) ≡ (k - (j.val + 1)) [MOD
      Nat.gcd (outerB k cov.a (i.val + 1)) (outerB k cov.a (j.val + 1))] := by
  rw [Nat.modEq_iff_dvd]
  have hdvd := outerB_gcd_dvd_diff hk cov i j
  have hi_le : i.val + 1 ≤ k := i.isLt
  have hj_le : j.val + 1 ≤ k := j.isLt
  have h_arith :
      ((k - (j.val + 1) : ℕ) : ℤ) - ((k - (i.val + 1) : ℕ) : ℤ) = (i.val : ℤ) - (j.val : ℤ) := by
    push_cast [Nat.sub_add_cancel hi_le, Nat.sub_add_cancel hj_le]
    omega
  rw [h_arith]; exact hdvd

noncomputable def primeSet (k : ℕ) : Finset ℕ :=
  (Finset.Icc 1 k).filter Nat.Prime

noncomputable def localMod (k p : ℕ) : ℕ :=
  p ^ (alphaP k p + 1)

noncomputable def localLift (k : ℕ) (a : ℕ → ℕ) (p : ℕ) : ℕ :=
  liftAtLevel a p (alphaP k p + 1)

noncomputable def localResidue (k : ℕ) (a : ℕ → ℕ) (p : ℕ) : ℤ :=
  (k : ℤ) - (localLift k a p : ℤ)

theorem mem_primeSet {k p : ℕ} :
    p ∈ primeSet k ↔ 1 ≤ p ∧ p ≤ k ∧ p.Prime := by
  unfold primeSet
  rw [Finset.mem_filter, Finset.mem_Icc]
  tauto

theorem primeSet_prime {k p : ℕ} (hp : p ∈ primeSet k) : p.Prime :=
  (mem_primeSet.mp hp).2.2

theorem localMod_pos {k p : ℕ} (hp : p.Prime) : 0 < localMod k p := by
  unfold localMod
  exact pow_pos hp.pos _

theorem localMod_coprime {k p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    Nat.Coprime (localMod k p) (localMod k q) := by
  unfold localMod
  exact Nat.Coprime.pow _ _ ((Nat.coprime_primes hp hq).mpr hpq)

theorem exists_R_local_modEq_of_a (k : ℕ) (a : ℕ → ℕ) :
    ∃ R : ℤ, ∀ p ∈ primeSet k,
      R ≡ localResidue k a p [ZMOD (localMod k p : ℤ)] := by
  classical
  let l := (primeSet k).toList
  let a_fn : ℕ → ℕ := fun p =>
    Int.toNat (((k : ℤ) - (localLift k a p : ℤ)) % (localMod k p : ℤ))
  let s_fn : ℕ → ℕ := localMod k
  have hcoprime : List.Pairwise (Function.onFun Nat.Coprime s_fn) l := by
    apply List.Pairwise.imp_of_mem (R := fun p q => p ≠ q ∧ p.Prime ∧ q.Prime)
    · rintro p q hp_mem hq_mem ⟨hpq, hp_prime, hq_prime⟩
      exact localMod_coprime hp_prime hq_prime hpq
    · rw [List.pairwise_iff_forall_sublist]
      intro p q hsub
      have hpq_ne : p ≠ q := by
        intro h
        rw [h] at hsub
        have h_nodup : (primeSet k).toList.Nodup := (primeSet k).nodup_toList
        have : ¬ [q, q].Sublist (primeSet k).toList := by
          intro h
          have := List.Sublist.nodup h h_nodup
          simp at this
        exact this hsub
      have hp_mem : p ∈ (primeSet k).toList := by
        have h : p ∈ ([p, q] : List ℕ) := List.mem_cons_self
        exact hsub.subset h
      have hq_mem : q ∈ (primeSet k).toList := by
        have h : q ∈ ([p, q] : List ℕ) := by simp
        exact hsub.subset h
      have hp_prime := primeSet_prime (Finset.mem_toList.mp hp_mem)
      have hq_prime := primeSet_prime (Finset.mem_toList.mp hq_mem)
      exact ⟨hpq_ne, hp_prime, hq_prime⟩
  obtain ⟨R0, hR0⟩ := Nat.chineseRemainderOfList a_fn s_fn l hcoprime
  refine ⟨(R0 : ℤ), ?_⟩
  intro p hp_set
  have hp_list : p ∈ l := Finset.mem_toList.mpr hp_set
  have h_modeq_nat := hR0 p hp_list
  have hp_prime := primeSet_prime hp_set
  have h_mod_pos : 0 < localMod k p := localMod_pos hp_prime
  have h_mod_pos_int : (0 : ℤ) < (localMod k p : ℤ) := by exact_mod_cast h_mod_pos
  show (R0 : ℤ) ≡ localResidue k a p [ZMOD (localMod k p : ℤ)]
  have h_step1 : (R0 : ℤ) ≡ (a_fn p : ℤ) [ZMOD (localMod k p : ℤ)] := by
    have : (R0 : ℤ) % (localMod k p : ℤ) = (a_fn p : ℤ) % (localMod k p : ℤ) := by
      have hn : ((R0 % (s_fn p) : ℕ) : ℤ) = (R0 : ℤ) % (s_fn p : ℤ) := Int.natCast_mod _ _
      have ha : ((a_fn p % (s_fn p) : ℕ) : ℤ) = (a_fn p : ℤ) % (s_fn p : ℤ) := Int.natCast_mod _ _
      have : ((R0 % (s_fn p) : ℕ) : ℤ) = ((a_fn p % (s_fn p) : ℕ) : ℤ) := by
        exact_mod_cast h_modeq_nat
      rw [hn, ha] at this; exact this
    exact this
  have h_a_fn_eq : (a_fn p : ℤ) =
      ((k : ℤ) - (localLift k a p : ℤ)) % (localMod k p : ℤ) := by
    show (Int.toNat _ : ℤ) = _
    apply Int.toNat_of_nonneg
    exact Int.emod_nonneg _ h_mod_pos_int.ne'
  have h_step2 : (a_fn p : ℤ) ≡ localResidue k a p [ZMOD (localMod k p : ℤ)] := by
    rw [h_a_fn_eq]
    exact Int.emod_emod_of_dvd _ (dvd_refl _)
  exact h_step1.trans h_step2

theorem exists_R_local_modEq {m k : ℕ} (cov : CoverData m k) :
    ∃ R : ℤ, ∀ p ∈ primeSet k,
      R ≡ localResidue k cov.a p [ZMOD (localMod k p : ℤ)] :=
  exists_R_local_modEq_of_a k cov.a

theorem outerB_factorization_le_alphaP_succ_of_a {k : ℕ} (a : ℕ → ℕ) (j : ℕ)
    (hj : 1 ≤ j) (hjk : j ≤ k) (p : ℕ) (hp : p.Prime) :
    (outerB k a j).factorization p ≤ alphaP k p + 1 := by
  by_cases hpk : p ≤ k
  · have h1 := outerB_factorization_le_exponent_of_a a j hj hjk p hp
    have h2 := exponent_le_alphaP_general k a j p hp hpk hj hjk
    omega
  · push_neg at hpk
    have h_zero : (outerB k a j).factorization p = 0 := by
      rw [Nat.factorization_eq_zero_iff]
      right; left; intro hdvd
      exact absurd (globalMk_smooth k p hp (dvd_trans hdvd (outerB_dvd_globalMk_of_a a j hj hjk)))
        (by omega)
    omega

theorem localLift_mod_lower {k : ℕ} (a : ℕ → ℕ) (p u : ℕ) (hp : p.Prime)
    (ha_pos : 1 ≤ a p) (ha_lt : a p < p) (hu_le : u ≤ alphaP k p + 1) :
    localLift k a p % p ^ u = liftAtLevel a p u := by
  unfold localLift
  have hself : liftAtLevel a p (alphaP k p + 1) % p ^ (alphaP k p + 1) =
      liftAtLevel a p (alphaP k p + 1) :=
    Nat.mod_eq_of_lt (liftAtLevel_lt_pow a p (alphaP k p + 1) hp.one_lt ha_pos ha_lt)
  exact cond_downward_iter k a (liftAtLevel a p (alphaP k p + 1)) p
    hp.one_lt ha_pos ha_lt hu_le hself

theorem outerB_pow_dvd_num_at_prime_of_a {k : ℕ} (a : ℕ → ℕ) (j : ℕ)
    (hj : 1 ≤ j) (hjk : j ≤ k)
    (ha_lt : ∀ p, p.Prime → a p < p)
    (R : ℤ) (p : ℕ) (hp : p.Prime)
    (hRloc : R ≡ localResidue k a p [ZMOD (localMod k p : ℤ)]) :
    ((p ^ (outerB k a j).factorization p : ℕ) : ℤ) ∣
      R - (k : ℤ) + (j : ℤ) := by
  set u := (outerB k a j).factorization p with hu_def
  have hu_le_succ : u ≤ alphaP k p + 1 :=
    outerB_factorization_le_alphaP_succ_of_a a j hj hjk p hp
  have h_pow_dvd_localMod : (p ^ u : ℤ) ∣ (localMod k p : ℤ) := by
    unfold localMod; exact_mod_cast pow_dvd_pow p hu_le_succ
  have hR_mod_pu : R ≡ localResidue k a p [ZMOD (p ^ u : ℤ)] := hRloc.of_dvd h_pow_dvd_localMod
  have h_cong_nat : j % p ^ u = localLift k a p % p ^ u := by
    by_cases ha : a p = 0
    · have h_localLift_zero : localLift k a p = 0 := by
        unfold localLift liftAtLevel; rw [if_pos ha]
      rw [h_localLift_zero, Nat.zero_mod]
      have h_exp_eq : exponent k a j p = padicValNat p j := by
        unfold exponent; rw [if_pos ha]
      have hu_le_exp : u ≤ exponent k a j p := by
        by_cases hpk : p ≤ k
        · exact outerB_factorization_le_exponent_of_a a j hj hjk p hp
        · push_neg at hpk
          have h_zero : u = 0 := by
            rw [hu_def, Nat.factorization_eq_zero_iff]
            right; left; intro hdvd
            exact absurd (globalMk_smooth k p hp
              (dvd_trans hdvd (outerB_dvd_globalMk_of_a a j hj hjk))) (by omega)
          omega
      rw [h_exp_eq] at hu_le_exp
      have : Fact p.Prime := ⟨hp⟩
      have h_pow_dvd : p ^ u ∣ j :=
        dvd_trans (pow_dvd_pow p hu_le_exp) pow_padicValNat_dvd
      exact Nat.mod_eq_zero_of_dvd h_pow_dvd
    · have hap_lt_p : a p < p := ha_lt p hp
      have hap_pos : 1 ≤ a p := by omega
      have hu_le_exp : u ≤ exponent k a j p := by
        by_cases hpk : p ≤ k
        · exact outerB_factorization_le_exponent_of_a a j hj hjk p hp
        · push_neg at hpk
          have h_zero : u = 0 := by
            rw [hu_def, Nat.factorization_eq_zero_iff]
            right; left; intro hdvd
            exact absurd (globalMk_smooth k p hp
              (dvd_trans hdvd (outerB_dvd_globalMk_of_a a j hj hjk))) (by omega)
          omega
      have hu_le_alpha : u ≤ alphaP k p := by
        by_cases hpk : p ≤ k
        · exact le_trans hu_le_exp (exponent_le_alphaP_general k a j p hp hpk hj hjk)
        · push_neg at hpk
          have h_zero : u = 0 := by
            rw [hu_def, Nat.factorization_eq_zero_iff]
            right; left; intro hdvd
            exact absurd (globalMk_smooth k p hp
              (dvd_trans hdvd (outerB_dvd_globalMk_of_a a j hj hjk))) (by omega)
          omega
      by_cases hu_zero : u = 0
      · simp [hu_zero, Nat.mod_one]
      · have hu_pos : 1 ≤ u := by omega
        have hj_cond := (le_exponent_iff_cond a j p u hp hap_pos hap_lt_p
          hu_pos hu_le_alpha).mp hu_le_exp
        rw [hj_cond]
        rw [localLift_mod_lower a p u hp hap_pos hap_lt_p (by omega)]
  have h_int_eq : ((j : ℕ) : ℤ) % (p ^ u : ℤ) =
      (localLift k a p : ℤ) % (p ^ u : ℤ) := by
    have h1 : ((j % p ^ u : ℕ) : ℤ) = ((j : ℕ) : ℤ) % (p ^ u : ℤ) := by
      push_cast; exact Int.natCast_mod _ _
    have h2 : ((localLift k a p % p ^ u : ℕ) : ℤ) =
        (localLift k a p : ℤ) % (p ^ u : ℤ) := by
      push_cast; exact Int.natCast_mod _ _
    have h3 : ((j % p ^ u : ℕ) : ℤ) = ((localLift k a p % p ^ u : ℕ) : ℤ) := by
      exact_mod_cast h_cong_nat
    rw [h1, h2] at h3; exact h3
  have h_cong_int : ((j : ℕ) : ℤ) ≡ (localLift k a p : ℤ) [ZMOD (p ^ u : ℤ)] := h_int_eq
  show (p ^ u : ℤ) ∣ R - (k : ℤ) + (j : ℤ)
  have h_localResidue_def : localResidue k a p = (k : ℤ) - (localLift k a p : ℤ) := rfl
  have h_chain : R - (k : ℤ) + (j : ℤ) =
      -(localResidue k a p - R) - ((localLift k a p : ℤ) - (j : ℤ)) := by
    rw [h_localResidue_def]; push_cast; ring
  rw [h_chain]
  exact dvd_sub (Dvd.dvd.neg_right hR_mod_pu.dvd) h_cong_int.dvd

theorem outerB_dvd_num_of_a {k : ℕ} (a : ℕ → ℕ) (j : ℕ) (hj : 1 ≤ j) (hjk : j ≤ k)
    (ha_lt : ∀ p, p.Prime → a p < p)
    (R : ℤ)
    (hRloc : ∀ p ∈ primeSet k, R ≡ localResidue k a p [ZMOD (localMod k p : ℤ)]) :
    (outerB k a j : ℤ) ∣ R - (k : ℤ) + (j : ℤ) := by
  set x := R - (k : ℤ) + (j : ℤ) with hx_def
  set B := outerB k a j with hB_def
  have hB_pos : 0 < B := outerB_pos_of_a a j hj hjk
  have hB_ne : B ≠ 0 := hB_pos.ne'
  by_cases hx_zero : x = 0
  · rw [hx_zero]; exact dvd_zero _
  have hx_natAbs_ne : x.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hx_zero
  have hB_dvd_natAbs : B ∣ x.natAbs := by
    rw [← Nat.factorization_le_iff_dvd hB_ne hx_natAbs_ne]
    intro p
    by_cases hp : p.Prime
    · have h_pow_dvd_int : ((p ^ B.factorization p : ℕ) : ℤ) ∣ x := by
        by_cases hpk : p ≤ k
        · have hp_set : p ∈ primeSet k := mem_primeSet.mpr ⟨hp.one_lt.le, hpk, hp⟩
          exact outerB_pow_dvd_num_at_prime_of_a a j hj hjk ha_lt R p hp (hRloc p hp_set)
        · push_neg at hpk
          have h_fact_zero : B.factorization p = 0 := by
            rw [Nat.factorization_eq_zero_iff]
            right; left; intro hdvd
            exact absurd (globalMk_smooth k p hp
              (dvd_trans hdvd (outerB_dvd_globalMk_of_a a j hj hjk))) (by omega)
          rw [h_fact_zero, pow_zero]; simp
      have h_pow_dvd_natAbs : p ^ B.factorization p ∣ x.natAbs :=
        Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr h_pow_dvd_int)
      exact (Nat.Prime.pow_dvd_iff_le_factorization hp hx_natAbs_ne).mp h_pow_dvd_natAbs
    · rw [Nat.factorization_eq_zero_of_not_prime _ hp]
      exact Nat.zero_le _
  have h_int : (B : ℤ) ∣ (x.natAbs : ℤ) := Int.natCast_dvd_natCast.mpr hB_dvd_natAbs
  rw [Int.natCast_natAbs] at h_int
  exact (dvd_abs _ _).mp h_int

theorem outerB_dvd_num {m k : ℕ} (hk : 3 ≤ k) (cov : CoverData m k)
    (R : ℤ) (j : Fin k)
    (hRloc : ∀ p ∈ primeSet k, R ≡ localResidue k cov.a p [ZMOD (localMod k p : ℤ)]) :
    (outerB k cov.a (j.val + 1) : ℤ) ∣ R - (k : ℤ) + ((j.val : ℤ) + 1) := by
  have h := outerB_dvd_num_of_a cov.a (j.val + 1) (Nat.succ_pos _) j.isLt cov.a_lt_p R hRloc
  have h_cast : ((j.val + 1 : ℕ) : ℤ) = (j.val : ℤ) + 1 := by push_cast; ring
  rw [h_cast] at h
  exact h

theorem factorization_scaffold_prod (k : ℕ) (a : ℕ → ℕ) (j p : ℕ) (hp : p.Prime) :
    (∏ q ∈ scaffoldExcess k a j, q).factorization p =
      if p ∈ scaffoldExcess k a j then 1 else 0 := by
  classical
  rw [Nat.factorization_prod_apply
    (fun q hq => ((Finset.mem_filter.mp
      (scaffoldExcess_subset_primes k a j hq)).2.pos).ne')]
  by_cases hmem : p ∈ scaffoldExcess k a j
  · rw [if_pos hmem]
    rw [Finset.sum_eq_single p]
    · exact hp.factorization_self
    · intro q hq hqp
      have hqPrime : q.Prime := (Finset.mem_filter.mp (scaffoldExcess_subset_primes k a j hq)).2
      rw [hqPrime.factorization, Finsupp.single_apply, if_neg hqp]
    · intro hnot; exact absurd hmem hnot
  · rw [if_neg hmem]
    apply Finset.sum_eq_zero
    intro q hq
    have hqPrime : q.Prime := (Finset.mem_filter.mp (scaffoldExcess_subset_primes k a j hq)).2
    have hneq : q ≠ p := fun h => hmem (h ▸ hq)
    rw [hqPrime.factorization, Finsupp.single_apply, if_neg hneq]

theorem factorization_outerB_eq_exponent_sub_scaffold_of_a {k : ℕ} (a : ℕ → ℕ) (j : ℕ)
    (hj : 1 ≤ j) (hjk : j ≤ k) (p : ℕ) (hp : p.Prime) (hpk : p ≤ k) :
    (outerB k a j).factorization p =
      exponent k a j p - (if p ∈ scaffoldExcess k a j then 1 else 0) := by
  have h_inner := innerB_eq_outerB_mul_scaffold k a j
  have h_outerB_pos := outerB_pos_of_a a j hj hjk
  have h_innerB_pos := innerB_pos k a j
  have h_scaffold_pos : 0 < ∏ q ∈ scaffoldExcess k a j, q := scaffold_prod_pos k a j
  have h_outerB_ne := h_outerB_pos.ne'
  have h_scaffold_ne := h_scaffold_pos.ne'
  have h_fact_eq : (innerB k a j).factorization p =
      (outerB k a j).factorization p +
        (∏ q ∈ scaffoldExcess k a j, q).factorization p := by
    rw [h_inner, Nat.factorization_mul h_outerB_ne h_scaffold_ne]; rfl
  rw [factorization_innerB_eq_exponent k a j p hp hpk] at h_fact_eq
  rw [factorization_scaffold_prod k a j p hp] at h_fact_eq
  omega

theorem localLift_gt_k_scaffold_of_a {k : ℕ} (hk_ge_4 : 4 ≤ k) (a : ℕ → ℕ)
    (p : ℕ) (hp : p.Prime) (hpk : p ≤ k) (hp_gt : k / 2 < p)
    (ha_lt : a p < p) (ha : a p ≠ 0) : k < localLift k a p := by
  have halpha : alphaP k p = 1 := alphaP_eq_one_of_gt_half hp hpk hp_gt hk_ge_4
  unfold localLift
  have hap_pos : 1 ≤ a p := by omega
  have h_lift_eq : liftAtLevel a p (alphaP k p + 1) = liftAbove p (alphaP k p + 1) (a p) :=
    liftAtLevel_eq_liftAbove a p (alphaP k p + 1) ha (by omega : 1 ≤ alphaP k p + 1)
  rw [h_lift_eq, halpha]
  unfold liftAbove
  have hk_lt_2p : k < 2 * p := by
    have := (Nat.div_lt_iff_lt_mul (by norm_num : (0 : ℕ) < 2)).mp hp_gt
    linarith
  have hp_ge_3 : 3 ≤ p := by
    by_contra h_not
    push_neg at h_not
    have hp_eq_2 : p = 2 := by have := hp.two_le; omega
    subst hp_eq_2; omega
  show k < p ^ (1 + 1) - p + a p
  have h_pow : p ^ (1 + 1) = p * p := by ring
  rw [h_pow]
  have : p * p ≥ 3 * p := Nat.mul_le_mul_right p hp_ge_3
  have : p * p ≥ k + p := by omega
  omega

theorem localLift_gt_k_scaffold {m k : ℕ} (hk : 3 ≤ k) (cov : CoverData m k)
    (p : ℕ) (hp : p.Prime) (hpk : p ≤ k) (hp_gt : k / 2 < p)
    (ha : cov.a p ≠ 0) : k < localLift k cov.a p :=
  localLift_gt_k_scaffold_of_a (by have := cov.k_ge_4m; omega) cov.a p hp hpk hp_gt
    (cov.a_lt_p p hp) ha

theorem localLift_gt_k_p_dvd_k_of_a {k : ℕ} (a : ℕ → ℕ)
    (p : ℕ) (hp : p.Prime) (hp_dvd_k : p ∣ k) (ha_lt : a p < p) (ha : a p ≠ 0) :
    k < localLift k a p := by
  have hap_pos : 1 ≤ a p := by omega
  unfold localLift
  rw [liftAtLevel_eq_liftAbove a p (alphaP k p + 1) ha (by omega)]
  have hlt := Nat.lt_pow_succ_log_self hp.one_lt k
  have hk_mod_self : k % p ^ (alphaP k p + 1) = k := Nat.mod_eq_of_lt hlt
  have h_lift_gt :=
    liftAbove_above_kModPow hp.one_lt hp_dvd_k hap_pos ha_lt (by omega : 1 ≤ alphaP k p + 1)
  rw [hk_mod_self] at h_lift_gt
  exact h_lift_gt

theorem localLift_gt_k_p_dvd_k {m k : ℕ} (hk : 3 ≤ k) (cov : CoverData m k)
    (p : ℕ) (hp : p.Prime) (hp_dvd_k : p ∣ k) (ha : cov.a p ≠ 0) :
    k < localLift k cov.a p :=
  localLift_gt_k_p_dvd_k_of_a cov.a p hp hp_dvd_k (cov.a_lt_p p hp) ha

theorem localLift_gt_k_anchor {m k : ℕ} (hk : 3 ≤ k) (cov : CoverData m k)
    (hm : 3 ≤ m) (ha : cov.a cov.q ≠ 0) :
    k < localLift k cov.a cov.q :=
  localLift_gt_k_p_dvd_k hk cov cov.q cov.q_prime cov.q_dvd_k ha

theorem localLift_gt_k {m k : ℕ} (hk : 3 ≤ k) (cov : CoverData m k) (hm : 3 ≤ m)
    (p : ℕ) (hp : p.Prime) (hpk : p ≤ k) (ha : cov.a p ≠ 0) :
    k < localLift k cov.a p := by
  by_cases hp_gt : k / 2 < p
  · exact localLift_gt_k_scaffold hk cov p hp hpk hp_gt ha
  · push_neg at hp_gt
    have hp_eq_q : p = cov.q := prime_a_nonzero_small_eq_q cov p hp ha hp_gt
    subst hp_eq_q
    exact localLift_gt_k_anchor hk cov hm ha

/-- Wide version: `localLift k a p > k` from the `p ∣ k ∨ k/2 < p` shape (LevelSafe). -/
theorem not_pow_succ_dvd_num_at_prime_truly_of_a {k : ℕ} (a : ℕ → ℕ)
    (ha_lt : ∀ p, p.Prime → a p < p)
    (j : Fin k) (R : ℤ) (p : ℕ) (hp : p.Prime) (hpk : p ≤ k)
    (h_lift_gt_k : a p ≠ 0 → k < localLift k a p)
    (hRloc : R ≡ localResidue k a p [ZMOD (localMod k p : ℤ)]) :
    ¬ ((p ^ (exponent k a (j.val + 1) p + 1) : ℕ) : ℤ) ∣
      R - (k : ℤ) + ((j.val : ℤ) + 1) := by
  intro h_dvd_succ
  set e := exponent k a (j.val + 1) p with he_def
  have hj_pos : 0 < j.val + 1 := Nat.succ_pos _
  have hj_le : j.val + 1 ≤ k := j.isLt
  have he_le_alpha : e ≤ alphaP k p :=
    exponent_le_alphaP_general k a (j.val + 1) p hp hpk hj_pos hj_le
  have h_e_succ_le : e + 1 ≤ alphaP k p + 1 := by omega
  have h_pow_dvd_localMod : (p ^ (e + 1) : ℤ) ∣ (localMod k p : ℤ) := by
    unfold localMod; exact_mod_cast pow_dvd_pow p h_e_succ_le
  have hR_mod : R ≡ localResidue k a p [ZMOD (p ^ (e + 1) : ℤ)] :=
    hRloc.of_dvd h_pow_dvd_localMod
  have h_localResidue_def :
      localResidue k a p = (k : ℤ) - (localLift k a p : ℤ) := rfl
  have h_pow_cast : ((p ^ (e + 1) : ℕ) : ℤ) = (p ^ (e + 1) : ℤ) := by push_cast; rfl
  have h_dvd_succ_int : (p ^ (e + 1) : ℤ) ∣ R - (k : ℤ) + ((j.val : ℤ) + 1) := by
    rw [← h_pow_cast]; exact h_dvd_succ
  have h_jL : (p ^ (e + 1) : ℤ) ∣
      ((localLift k a p : ℤ) - ((j.val + 1 : ℕ) : ℤ)) := by
    have h1 : (p ^ (e + 1) : ℤ) ∣ -(localResidue k a p - R) :=
      Dvd.dvd.neg_right hR_mod.dvd
    have hdiff_dvd := dvd_sub h1 h_dvd_succ_int
    have h_arith :
        -(localResidue k a p - R) - (R - (k : ℤ) + ((j.val : ℤ) + 1)) =
        ((localLift k a p : ℤ) - ((j.val + 1 : ℕ) : ℤ)) := by
      rw [h_localResidue_def]; push_cast; ring
    rw [h_arith] at hdiff_dvd
    exact hdiff_dvd
  have h_cong_nat : (j.val + 1) % p ^ (e + 1) = localLift k a p % p ^ (e + 1) := by
    have h_int_eq : ((j.val + 1 : ℕ) : ℤ) % (p ^ (e + 1) : ℤ) =
        (localLift k a p : ℤ) % (p ^ (e + 1) : ℤ) := by
      have h_sym : (p ^ (e + 1) : ℤ) ∣
          (((j.val + 1 : ℕ) : ℤ) - (localLift k a p : ℤ)) := by
        have : -((localLift k a p : ℤ) - ((j.val + 1 : ℕ) : ℤ)) =
            ((j.val + 1 : ℕ) : ℤ) - (localLift k a p : ℤ) := by ring
        rw [← this]; exact Dvd.dvd.neg_right h_jL
      exact Int.ModEq.symm (Int.modEq_iff_dvd.mpr h_sym)
    have h_jmod : ((j.val + 1) % p ^ (e + 1) : ℤ) =
        ((j.val + 1 : ℕ) : ℤ) % (p ^ (e + 1) : ℤ) := by push_cast; exact Int.natCast_mod _ _
    have h_lmod : ((localLift k a p % p ^ (e + 1) : ℕ) : ℤ) =
        (localLift k a p : ℤ) % (p ^ (e + 1) : ℤ) := by push_cast; exact Int.natCast_mod _ _
    have h_combined : ((j.val + 1) % p ^ (e + 1) : ℤ) =
        ((localLift k a p % p ^ (e + 1) : ℕ) : ℤ) := by
      rw [h_jmod, h_lmod, h_int_eq]
    exact_mod_cast h_combined
  by_cases ha : a p = 0
  · have h_localLift_zero : localLift k a p = 0 := by
      unfold localLift liftAtLevel; rw [if_pos ha]
    rw [h_localLift_zero, Nat.zero_mod] at h_cong_nat
    have h_e_eq : e = padicValNat p (j.val + 1) := by
      unfold exponent at he_def; rw [if_pos ha] at he_def; exact he_def
    have : Fact p.Prime := ⟨hp⟩
    have h_pow_dvd : p ^ (e + 1) ∣ (j.val + 1) := Nat.dvd_of_mod_eq_zero h_cong_nat
    have h_le_padic : e + 1 ≤ padicValNat p (j.val + 1) :=
      (Nat.Prime.pow_dvd_iff_le_factorization hp (by omega)).mp h_pow_dvd
        |>.trans_eq (Nat.factorization_def _ hp)
    omega
  · have hap_lt_p : a p < p := ha_lt p hp
    have hap_pos : 1 ≤ a p := by omega
    by_cases h_e_eq_alpha : e = alphaP k p
    · have hj_lt_pow : j.val + 1 < p ^ (e + 1) := by
        rw [h_e_eq_alpha]
        exact lt_of_le_of_lt hj_le (Nat.lt_pow_succ_log_self hp.one_lt k)
      have hl_lt_pow : localLift k a p < p ^ (e + 1) := by
        rw [h_e_eq_alpha]
        unfold localLift
        exact liftAtLevel_lt_pow a p (alphaP k p + 1) hp.one_lt hap_pos hap_lt_p
      have hj_self : (j.val + 1) % p ^ (e + 1) = j.val + 1 := Nat.mod_eq_of_lt hj_lt_pow
      have hl_self : localLift k a p % p ^ (e + 1) = localLift k a p :=
        Nat.mod_eq_of_lt hl_lt_pow
      rw [hj_self, hl_self] at h_cong_nat
      have h_lift_gt := h_lift_gt_k ha
      omega
    · have h_e_lt_alpha : e + 1 ≤ alphaP k p := by omega
      have h_lift_mod := localLift_mod_lower a p (e + 1) hp hap_pos hap_lt_p
        (by omega : e + 1 ≤ alphaP k p + 1)
      rw [h_lift_mod] at h_cong_nat
      have hu_pos : 1 ≤ e + 1 := by omega
      have h_cond : (j.val + 1) % p ^ (e + 1) = liftAtLevel a p (e + 1) := h_cong_nat
      have h_e_ge_succ :=
        (le_exponent_iff_cond a (j.val + 1) p (e + 1) hp hap_pos hap_lt_p hu_pos
          h_e_lt_alpha).mpr h_cond
      omega

theorem not_pow_succ_dvd_num_at_prime_of_a {m k : ℕ} (hk : 3 ≤ k) (cov : CoverData m k)
    (j : Fin k) (R : ℤ) (p : ℕ) (hp : p.Prime) (hpk : p ≤ k)
    (h_lift_gt_k : cov.a p ≠ 0 → k < localLift k cov.a p)
    (hRloc : R ≡ localResidue k cov.a p [ZMOD (localMod k p : ℤ)]) :
    ¬ ((p ^ (exponent k cov.a (j.val + 1) p + 1) : ℕ) : ℤ) ∣
      R - (k : ℤ) + ((j.val : ℤ) + 1) :=
  not_pow_succ_dvd_num_at_prime_truly_of_a cov.a cov.a_lt_p j R p hp hpk h_lift_gt_k hRloc

theorem not_pow_succ_dvd_num_shifted_at_prime_truly_of_a {k : ℕ} (a : ℕ → ℕ)
    (ha_lt : ∀ p, p.Prime → a p < p)
    (R : ℤ) (n : ℤ) (j : Fin k) (p : ℕ) (hp : p.Prime) (hpk : p ≤ k)
    (h_lift_gt_k : a p ≠ 0 → k < localLift k a p)
    (hRloc : R ≡ localResidue k a p [ZMOD (localMod k p : ℤ)]) :
    ¬ ((p ^ (exponent k a (j.val + 1) p + 1) : ℕ) : ℤ) ∣
      R + (globalMk k : ℤ) * n - (k : ℤ) + ((j.val : ℤ) + 1) := by
  intro h_dvd
  set e := exponent k a (j.val + 1) p with he_def
  have he_le_alpha : e ≤ alphaP k p :=
    exponent_le_alphaP_general k a (j.val + 1) p hp hpk (Nat.succ_pos _) j.isLt
  have h_pe_le_palpha : (p ^ (e + 1) : ℕ) ∣ (p ^ (alphaP k p + 1) : ℕ) :=
    pow_dvd_pow p (by omega)
  have h_dvd_Mkn : ((p ^ (e + 1) : ℕ) : ℤ) ∣ (globalMk k : ℤ) * n := by
    have h_pow_dvd_globalMk : ((p ^ (alphaP k p + 1) : ℕ) : ℤ) ∣ (globalMk k : ℤ) := by
      have : p ^ (alphaP k p + 1) ∣ globalMk k := by
        unfold globalMk; apply Finset.dvd_prod_of_mem
        rw [Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨hp.one_lt.le, hpk⟩, hp⟩
      exact_mod_cast this
    have h2 : ((p ^ (e + 1) : ℕ) : ℤ) ∣ ((p ^ (alphaP k p + 1) : ℕ) : ℤ) := by
      exact_mod_cast h_pe_le_palpha
    exact (h2.trans h_pow_dvd_globalMk).mul_right _
  have h_dvd_R : ((p ^ (e + 1) : ℕ) : ℤ) ∣ R - (k : ℤ) + ((j.val : ℤ) + 1) := by
    have h_arith :
        R - (k : ℤ) + ((j.val : ℤ) + 1) =
          (R + (globalMk k : ℤ) * n - (k : ℤ) + ((j.val : ℤ) + 1)) -
            (globalMk k : ℤ) * n := by ring
    rw [h_arith]
    exact dvd_sub h_dvd h_dvd_Mkn
  exact not_pow_succ_dvd_num_at_prime_truly_of_a a ha_lt j R p hp hpk h_lift_gt_k hRloc h_dvd_R

theorem not_pow_succ_dvd_num_shifted_at_prime_of_a {m k : ℕ} (hk : 3 ≤ k) (cov : CoverData m k)
    (R : ℤ) (n : ℤ) (j : Fin k) (p : ℕ) (hp : p.Prime) (hpk : p ≤ k)
    (h_lift_gt_k : cov.a p ≠ 0 → k < localLift k cov.a p)
    (hRloc : R ≡ localResidue k cov.a p [ZMOD (localMod k p : ℤ)]) :
    ¬ ((p ^ (exponent k cov.a (j.val + 1) p + 1) : ℕ) : ℤ) ∣
      R + (globalMk k : ℤ) * n - (k : ℤ) + ((j.val : ℤ) + 1) :=
  not_pow_succ_dvd_num_shifted_at_prime_truly_of_a cov.a cov.a_lt_p R n j p hp hpk
    h_lift_gt_k hRloc

theorem outerB_dvd_num_shifted_of_a {k : ℕ} (a : ℕ → ℕ) (j : ℕ) (hj : 1 ≤ j) (hjk : j ≤ k)
    (R : ℤ) (n : ℤ)
    (hR_dvd : (outerB k a j : ℤ) ∣ R - (k : ℤ) + (j : ℤ)) :
    (outerB k a j : ℤ) ∣ R + (globalMk k : ℤ) * n - (k : ℤ) + (j : ℤ) := by
  have h_outerB_dvd_globalMk : (outerB k a j : ℤ) ∣ (globalMk k : ℤ) := by
    exact_mod_cast outerB_dvd_globalMk_of_a a j hj hjk
  have h_arith : R + (globalMk k : ℤ) * n - (k : ℤ) + (j : ℤ) =
      (R - (k : ℤ) + (j : ℤ)) + (globalMk k : ℤ) * n := by ring
  rw [h_arith]
  exact dvd_add hR_dvd (h_outerB_dvd_globalMk.mul_right _)

theorem outerB_dvd_num_shifted {m k : ℕ} (hk : 3 ≤ k) (cov : CoverData m k)
    (R : ℤ) (j : Fin k) (n : ℕ)
    (hR_dvd : (outerB k cov.a (j.val + 1) : ℤ) ∣ R - (k : ℤ) + ((j.val : ℤ) + 1)) :
    (outerB k cov.a (j.val + 1) : ℤ) ∣
      R + (globalMk k : ℤ) * n - (k : ℤ) + ((j.val : ℤ) + 1) := by
  have h_cast : ((j.val + 1 : ℕ) : ℤ) = (j.val : ℤ) + 1 := by push_cast; ring
  have hR_dvd' : (outerB k cov.a (j.val + 1) : ℤ) ∣ R - (k : ℤ) + ((j.val + 1 : ℕ) : ℤ) := by
    rw [h_cast]; exact hR_dvd
  have h := outerB_dvd_num_shifted_of_a cov.a (j.val + 1) (Nat.succ_pos _) j.isLt R n hR_dvd'
  rw [h_cast] at h
  exact h

theorem small_prime_div_quotient_imp_scaffold_truly_of_a {k : ℕ} (a : ℕ → ℕ)
    (ha_lt : ∀ p, p.Prime → a p < p)
    (R : ℤ) (n : ℤ) (j : Fin k) (p : ℕ)
    (hp : p.Prime) (hpk : p ≤ k)
    (h_lift_gt_k : a p ≠ 0 → k < localLift k a p)
    (hRloc : ∀ q ∈ primeSet k, R ≡ localResidue k a q [ZMOD (localMod k q : ℤ)])
    (hp_dvd_quot : (p : ℤ) ∣
      (R + (globalMk k : ℤ) * n - (k : ℤ) + ((j.val : ℤ) + 1)) /
      (outerB k a (j.val + 1) : ℤ)) :
    p ∈ scaffoldExcess k a (j.val + 1) := by
  set B := outerB k a (j.val + 1) with hB_def
  have hB_pos : 0 < B := outerB_pos_of_a a (j.val + 1) (Nat.succ_pos _) j.isLt
  have hB_int_pos : (0 : ℤ) < (B : ℤ) := by exact_mod_cast hB_pos
  have hB_ne_int : (B : ℤ) ≠ 0 := hB_int_pos.ne'
  have hp_set : p ∈ primeSet k := mem_primeSet.mpr ⟨hp.one_lt.le, hpk, hp⟩
  have hRloc_p := hRloc p hp_set
  have hB_dvd_R : (B : ℤ) ∣ R - (k : ℤ) + ((j.val : ℤ) + 1) := by
    have h_cast : ((j.val + 1 : ℕ) : ℤ) = (j.val : ℤ) + 1 := by push_cast; ring
    have h := outerB_dvd_num_of_a a (j.val + 1) (Nat.succ_pos _) j.isLt ha_lt R hRloc
    rw [h_cast] at h; exact h
  have hB_dvd_shifted : (B : ℤ) ∣ R + (globalMk k : ℤ) * n - (k : ℤ) + ((j.val : ℤ) + 1) := by
    have h_cast : ((j.val + 1 : ℕ) : ℤ) = (j.val : ℤ) + 1 := by push_cast; ring
    have hB_dvd_R' : (B : ℤ) ∣ R - (k : ℤ) + ((j.val + 1 : ℕ) : ℤ) := by rw [h_cast]; exact hB_dvd_R
    have h := outerB_dvd_num_shifted_of_a a (j.val + 1) (Nat.succ_pos _) j.isLt R n hB_dvd_R'
    rw [h_cast] at h; exact h
  have hpB_dvd : (p : ℤ) * (B : ℤ) ∣
      R + (globalMk k : ℤ) * n - (k : ℤ) + ((j.val : ℤ) + 1) := by
    set num := R + (globalMk k : ℤ) * n - (k : ℤ) + ((j.val : ℤ) + 1) with hnum_def
    have h_num_eq : num = (B : ℤ) * (num / (B : ℤ)) :=
      (EuclideanDomain.mul_div_cancel' hB_ne_int hB_dvd_shifted).symm
    rcases hp_dvd_quot with ⟨c, hc⟩
    rw [h_num_eq, hc]
    exact ⟨c, by ring⟩
  by_contra hp_notin
  have h_fact_eq := factorization_outerB_eq_exponent_sub_scaffold_of_a a (j.val + 1)
    (Nat.succ_pos _) j.isLt p hp hpk
  rw [if_neg hp_notin, Nat.sub_zero] at h_fact_eq
  have h_pow_dvd : ((p ^ (exponent k a (j.val + 1) p + 1) : ℕ) : ℤ) ∣
      R + (globalMk k : ℤ) * n - (k : ℤ) + ((j.val : ℤ) + 1) := by
    have h_p_pow_succ_dvd_pB : (p ^ (exponent k a (j.val + 1) p + 1) : ℕ) ∣ p * B := by
      have h_B_dvd : p ^ (B).factorization p ∣ B := Nat.ordProj_dvd B p
      have h_p_pow_pB_eq : p * B = p ^ 1 * B := by ring
      rw [h_p_pow_pB_eq, ← h_fact_eq]
      have h_pB_pow : p ^ 1 * (p ^ (B).factorization p) = p ^ ((B).factorization p + 1) := by
        rw [pow_succ]; ring
      have h_pow_dvd : p ^ 1 * (p ^ (B).factorization p) ∣ p ^ 1 * B :=
        mul_dvd_mul_left _ h_B_dvd
      rw [h_pB_pow] at h_pow_dvd
      exact h_pow_dvd
    have h_pB_dvd_int : ((p * B : ℕ) : ℤ) ∣
        R + (globalMk k : ℤ) * n - (k : ℤ) + ((j.val : ℤ) + 1) := by
      push_cast; exact hpB_dvd
    have h_pow_dvd_pB :
        ((p ^ (exponent k a (j.val + 1) p + 1) : ℕ) : ℤ) ∣ ((p * B : ℕ) : ℤ) := by
      exact_mod_cast h_p_pow_succ_dvd_pB
    exact h_pow_dvd_pB.trans h_pB_dvd_int
  exact not_pow_succ_dvd_num_shifted_at_prime_truly_of_a a ha_lt R n j p hp hpk
    h_lift_gt_k hRloc_p h_pow_dvd

theorem small_prime_div_quotient_imp_scaffold_of_a {m k : ℕ} (hk : 3 ≤ k) (cov : CoverData m k)
    (R : ℤ) (n : ℤ) (j : Fin k) (p : ℕ)
    (hp : p.Prime) (hpk : p ≤ k)
    (h_lift_gt_k : cov.a p ≠ 0 → k < localLift k cov.a p)
    (hRloc : ∀ q ∈ primeSet k, R ≡ localResidue k cov.a q [ZMOD (localMod k q : ℤ)])
    (hp_dvd_quot : (p : ℤ) ∣
      (R + (globalMk k : ℤ) * n - (k : ℤ) + ((j.val : ℤ) + 1)) /
      (outerB k cov.a (j.val + 1) : ℤ)) :
    p ∈ scaffoldExcess k cov.a (j.val + 1) :=
  small_prime_div_quotient_imp_scaffold_truly_of_a cov.a cov.a_lt_p R n j p hp hpk
    h_lift_gt_k hRloc hp_dvd_quot

theorem small_prime_div_quotient_imp_scaffold {m k : ℕ} (hk : 3 ≤ k) (hm : 3 ≤ m)
    (cov : CoverData m k) (R : ℤ) (n : ℕ) (j : Fin k) (p : ℕ)
    (hp : p.Prime) (hpk : p ≤ k)
    (hRloc : ∀ q ∈ primeSet k, R ≡ localResidue k cov.a q [ZMOD (localMod k q : ℤ)])
    (hp_dvd_quot : (p : ℤ) ∣
      (R + (globalMk k : ℤ) * (n : ℤ) - (k : ℤ) + ((j.val : ℤ) + 1)) /
      (outerB k cov.a (j.val + 1) : ℤ)) :
    p ∈ scaffoldExcess k cov.a (j.val + 1) :=
  small_prime_div_quotient_imp_scaffold_of_a hk cov R (n : ℤ) j p hp hpk
    (fun ha => localLift_gt_k hk cov hm p hp hpk ha) hRloc hp_dvd_quot

theorem int_gcd_eq_one_of_no_prime_common {x y : ℤ}
    (h : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ x → (p : ℤ) ∣ y → False) :
    Int.gcd x y = 1 := by
  by_contra hne
  by_cases h_zero : Int.gcd x y = 0
  · rcases Int.gcd_eq_zero_iff.mp h_zero with ⟨hx, hy⟩
    exact h 2 Nat.prime_two (by rw [hx]; exact dvd_zero _) (by rw [hy]; exact dvd_zero _)
  · have h_ge_two : 2 ≤ Int.gcd x y := by
      rcases Nat.lt_or_ge (Int.gcd x y) 2 with hlt | hge
      · interval_cases (Int.gcd x y)
        · exact absurd rfl h_zero
        · exact absurd rfl hne
      · exact hge
    obtain ⟨ℓ, hℓ_prime, hℓ_dvd_gcd⟩ : ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ∣ Int.gcd x y :=
      (Int.gcd x y).exists_prime_and_dvd (by omega)
    have hℓ_dvd_gcd_int : (ℓ : ℤ) ∣ (Int.gcd x y : ℤ) := by exact_mod_cast hℓ_dvd_gcd
    exact h ℓ hℓ_prime
      (hℓ_dvd_gcd_int.trans (Int.gcd_dvd_left x y))
      (hℓ_dvd_gcd_int.trans (Int.gcd_dvd_right x y))

theorem quotient_pairwise_coprime {m k : ℕ} (hk : 3 ≤ k) (hm : 3 ≤ m)
    (cov : CoverData m k) (R : ℤ)
    (hRloc : ∀ q ∈ primeSet k, R ≡ localResidue k cov.a q [ZMOD (localMod k q : ℤ)])
    (n : ℕ) (i j : Fin k) (hij : i ≠ j) :
    Int.gcd
      ((R + (globalMk k : ℤ) * n - (k : ℤ) + ((i.val : ℤ) + 1)) /
        (outerB k cov.a (i.val + 1) : ℤ))
      ((R + (globalMk k : ℤ) * n - (k : ℤ) + ((j.val : ℤ) + 1)) /
        (outerB k cov.a (j.val + 1) : ℤ)) = 1 := by
  apply int_gcd_eq_one_of_no_prime_common
  intro p hp hp_i hp_j
  by_cases hpk : p ≤ k
  · have hsi := small_prime_div_quotient_imp_scaffold hk hm cov R n i p hp hpk hRloc hp_i
    have hsj := small_prime_div_quotient_imp_scaffold hk hm cov R n j p hp hpk hRloc hp_j
    have huniq := scaffoldExcess_unique_j cov.a p (i.val + 1) (j.val + 1)
      i.isLt j.isLt hsi hsj
    exact hij (Fin.ext (by omega))
  · push_neg at hpk
    have hBi_dvd_R : (outerB k cov.a (i.val + 1) : ℤ) ∣ R - (k : ℤ) + ((i.val : ℤ) + 1) :=
      outerB_dvd_num hk cov R i hRloc
    have hBj_dvd_R : (outerB k cov.a (j.val + 1) : ℤ) ∣ R - (k : ℤ) + ((j.val : ℤ) + 1) :=
      outerB_dvd_num hk cov R j hRloc
    have hBi_dvd_si : (outerB k cov.a (i.val + 1) : ℤ) ∣
        R + (globalMk k : ℤ) * n - (k : ℤ) + ((i.val : ℤ) + 1) :=
      outerB_dvd_num_shifted hk cov R i n hBi_dvd_R
    have hBj_dvd_sj : (outerB k cov.a (j.val + 1) : ℤ) ∣
        R + (globalMk k : ℤ) * n - (k : ℤ) + ((j.val : ℤ) + 1) :=
      outerB_dvd_num_shifted hk cov R j n hBj_dvd_R
    have hp_dvd_numi : (p : ℤ) ∣ R + (globalMk k : ℤ) * n - (k : ℤ) + ((i.val : ℤ) + 1) := by
      have h_eq : R + (globalMk k : ℤ) * n - (k : ℤ) + ((i.val : ℤ) + 1) =
          (outerB k cov.a (i.val + 1) : ℤ) *
            ((R + (globalMk k : ℤ) * n - (k : ℤ) + ((i.val : ℤ) + 1)) /
              (outerB k cov.a (i.val + 1) : ℤ)) :=
        (EuclideanDomain.mul_div_cancel'
          (by exact_mod_cast (outerB_pos hk cov i).ne' : (outerB k cov.a (i.val + 1) : ℤ) ≠ 0)
          hBi_dvd_si).symm
      rw [h_eq]; exact dvd_mul_of_dvd_right hp_i _
    have hp_dvd_numj : (p : ℤ) ∣ R + (globalMk k : ℤ) * n - (k : ℤ) + ((j.val : ℤ) + 1) := by
      have h_eq : R + (globalMk k : ℤ) * n - (k : ℤ) + ((j.val : ℤ) + 1) =
          (outerB k cov.a (j.val + 1) : ℤ) *
            ((R + (globalMk k : ℤ) * n - (k : ℤ) + ((j.val : ℤ) + 1)) /
              (outerB k cov.a (j.val + 1) : ℤ)) :=
        (EuclideanDomain.mul_div_cancel'
          (by exact_mod_cast (outerB_pos hk cov j).ne' : (outerB k cov.a (j.val + 1) : ℤ) ≠ 0)
          hBj_dvd_sj).symm
      rw [h_eq]; exact dvd_mul_of_dvd_right hp_j _
    have hp_dvd_diff : (p : ℤ) ∣ ((i.val : ℤ) - (j.val : ℤ)) := by
      have h_arith :
          (R + (globalMk k : ℤ) * n - (k : ℤ) + ((i.val : ℤ) + 1)) -
            (R + (globalMk k : ℤ) * n - (k : ℤ) + ((j.val : ℤ) + 1)) =
          (i.val : ℤ) - (j.val : ℤ) := by ring
      rw [← h_arith]
      exact dvd_sub hp_dvd_numi hp_dvd_numj
    have habs : p ∣ ((i.val : ℤ) - (j.val : ℤ)).natAbs :=
      Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr hp_dvd_diff)
    have h_abs_lt : ((i.val : ℤ) - (j.val : ℤ)).natAbs < k := by
      have hi := i.isLt; have hj := j.isLt
      have hii : (0 : ℤ) ≤ i.val := by exact_mod_cast Nat.zero_le _
      have hjj : (0 : ℤ) ≤ j.val := by exact_mod_cast Nat.zero_le _
      have hi_int : (i.val : ℤ) < (k : ℤ) := by exact_mod_cast hi
      have hj_int : (j.val : ℤ) < (k : ℤ) := by exact_mod_cast hj
      have hub : ((i.val : ℤ) - (j.val : ℤ)).natAbs ≤ max i.val j.val := by
        omega
      have hmax_lt : max i.val j.val < k := max_lt hi hj
      omega
    have h_ne_zero : ((i.val : ℤ) - (j.val : ℤ)).natAbs ≠ 0 := by
      intro hz
      apply hij; apply Fin.ext
      have : (i.val : ℤ) = (j.val : ℤ) := by
        have := Int.natAbs_eq_zero.mp hz
        linarith
      exact_mod_cast this
    have hp_pos : 0 < ((i.val : ℤ) - (j.val : ℤ)).natAbs := Nat.pos_of_ne_zero h_ne_zero
    have hp_le_abs : p ≤ ((i.val : ℤ) - (j.val : ℤ)).natAbs := Nat.le_of_dvd hp_pos habs
    omega

theorem exists_R_for_cover {m k : ℕ} (hm : 3 ≤ m) (hk : 3 ≤ k) (cov : CoverData m k) :
    ∃ R : ℤ,
      (∀ j : Fin k, (outerB k cov.a (j.val + 1) : ℤ) ∣
          R - (k : ℤ) + ((j.val : ℤ) + 1)) ∧
      (∀ (n : ℕ) (i j : Fin k), i ≠ j →
          Int.gcd
            ((R + (globalMk k : ℤ) * n - (k : ℤ) + ((i.val : ℤ) + 1)) /
              (outerB k cov.a (i.val + 1) : ℤ))
            ((R + (globalMk k : ℤ) * n - (k : ℤ) + ((j.val : ℤ) + 1)) /
              (outerB k cov.a (j.val + 1) : ℤ)) = 1) := by
  obtain ⟨R, hRloc⟩ := exists_R_local_modEq cov
  refine ⟨R, ?_, ?_⟩
  · intro j; exact outerB_dvd_num hk cov R j hRloc
  · intro n i j hij
    exact quotient_pairwise_coprime hk hm cov R hRloc n i j hij

theorem cover_to_certificate {m k : ℕ} (hm : 3 ≤ m) (hk : 3 ≤ k)
    (cov : CoverData m k) :
    Nonempty (GlobalResidueCertificate m k) := by
  obtain ⟨R, hRdiv, hRcoprime⟩ := exists_R_for_cover hm hk cov
  refine ⟨{
    B := fun j => outerB k cov.a (j.val + 1)
    Mk := globalMk k
    R := R
    hMk_pos := globalMk_pos k
    hB_pos := fun j => outerB_pos hk cov j
    hB_ge := fun j => outerB_ge_m hm hk cov j
    hB_dvd_Mk := fun j => outerB_dvd_globalMk hk cov j
    hMk_overB_p := fun j p hp hpk => globalMk_mul_outerB_dvd hk cov j p hp hpk
    hMk_smooth := fun p hp hpd => globalMk_smooth k p hp hpd
    hprod_B := prod_outerB_eq_factorial hm hk cov
    hR_div := hRdiv
    hPairwise_coprime := hRcoprime
  }⟩



structure AbsorberCover (m k : ℕ) where
  N₀ : ℤ
  Mk : ℕ
  Mk_pos : 0 < Mk
  B : Fin k → ℕ
  B_ge_m : ∀ j, m ≤ B j
  prod_B_eq_factorial : ∏ j, B j = k.factorial

namespace AbsorberCover

variable {m k : ℕ}

def N (cov : AbsorberCover m k) (n : ℕ) : ℤ := cov.N₀ + (cov.Mk : ℤ) * n

def L (cov : AbsorberCover m k) (n : ℕ) (j : Fin k) : ℤ :=
  (cov.N n - (k : ℤ) + (j.val + 1 : ℤ)) / (cov.B j : ℤ)

end AbsorberCover

structure AbsorberCoverValid (m k : ℕ) extends AbsorberCover m k where
  L_div : ∀ n j, ((toAbsorberCover.B j : ℤ)) ∣
    (toAbsorberCover.N n - (k : ℤ) + (j.val + 1 : ℤ))
  N_pos : ∀ n, 0 < toAbsorberCover.N n
  binom_eq : ∀ n,
    (((toAbsorberCover.N n).toNat).choose k : ℤ) = ∏ j, toAbsorberCover.L n j
  pairwise_coprime : ∀ n, ∀ i j : Fin k, i ≠ j →
    Int.gcd (toAbsorberCover.L n i) (toAbsorberCover.L n j) = 1
  k_lt_N_toNat : ∀ n, k < (toAbsorberCover.N n).toNat
  Mk_smooth : ∀ p : ℕ, p.Prime → p ∣ toAbsorberCover.Mk → p ≤ k
  B_dvd_Mk : ∀ j, toAbsorberCover.B j ∣ toAbsorberCover.Mk

theorem B_pos {m k : ℕ} (cov : AbsorberCover m k) (j : Fin k) :
    0 < cov.B j := by
  have hprod : ∏ i, cov.B i = k.factorial := cov.prod_B_eq_factorial
  have hfact_pos : 0 < k.factorial := Nat.factorial_pos k
  have hprod_pos : 0 < ∏ i, cov.B i := by rw [hprod]; exact hfact_pos
  rcases Nat.eq_zero_or_pos (cov.B j) with hBj_zero | hBj_pos
  · exfalso
    have hzero : ∏ i, cov.B i = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ j) hBj_zero
    omega
  · exact hBj_pos

noncomputable def mk_AbsorberCoverValid_from_data {m k : ℕ}
    (N₀ : ℤ) (Mk : ℕ) (B : Fin k → ℕ)
    (hMk_pos : 0 < Mk)
    (hprod : ∏ j, B j = k.factorial)
    (hBge : ∀ j, m ≤ B j)
    (hMk_smooth : ∀ p : ℕ, p.Prime → p ∣ Mk → p ≤ k)
    (hB_dvd : ∀ j, B j ∣ Mk)
    (hL_div : ∀ (n : ℕ) (j : Fin k), (B j : ℤ) ∣
        (N₀ + (Mk : ℤ) * n - (k : ℤ) + ((j.val : ℤ) + 1)))
    (hN_pos : ∀ n : ℕ, 0 < N₀ + (Mk : ℤ) * n)
    (hbinom : ∀ n : ℕ,
        (((N₀ + (Mk : ℤ) * n).toNat).choose k : ℤ) =
          ∏ j, (N₀ + (Mk : ℤ) * n - (k : ℤ) + ((j.val : ℤ) + 1)) / (B j : ℤ))
    (hcopr : ∀ n : ℕ, ∀ i j : Fin k, i ≠ j →
        Int.gcd
          ((N₀ + (Mk : ℤ) * n - (k : ℤ) + ((i.val : ℤ) + 1)) / (B i : ℤ))
          ((N₀ + (Mk : ℤ) * n - (k : ℤ) + ((j.val : ℤ) + 1)) / (B j : ℤ)) = 1)
    (hkN : ∀ n : ℕ, k < (N₀ + (Mk : ℤ) * n).toNat) :
    AbsorberCoverValid m k :=
  { N₀ := N₀
    Mk := Mk
    Mk_pos := hMk_pos
    B := B
    B_ge_m := hBge
    prod_B_eq_factorial := hprod
    L_div := hL_div
    N_pos := hN_pos
    binom_eq := hbinom
    pairwise_coprime := hcopr
    k_lt_N_toNat := hkN
    Mk_smooth := hMk_smooth
    B_dvd_Mk := hB_dvd }

theorem absorber_cover_from_cert (m k : ℕ) (hk : 2 ≤ k)
    (cert : GlobalResidueCertificate m k) :
    Nonempty (AbsorberCoverValid m k) := by
  obtain ⟨data⟩ := exists_full_construction_from_cert m k hk cert
  exact ⟨mk_AbsorberCoverValid_from_data data.N₀ data.Mk data.B data.Mk_pos data.prod_B
    data.B_ge_m data.Mk_smooth data.B_dvd_Mk data.L_div data.N_pos data.binom_eq
    data.pairwise_coprime data.k_lt_N_toNat⟩

abbrev NonExcessResidueAssignment := CoverData

theorem exists_nonexcess_residue_assignment_above
    (m K₀ : ℕ) (hm : 3 ≤ m) :
    ∃ k : ℕ, K₀ ≤ k ∧ 3 ≤ k ∧ Nonempty (NonExcessResidueAssignment m k) := by
  obtain ⟨_C_m, hC⟩ := cover_lemma m hm
  obtain ⟨k, hkK₀, hkm, hk4m, a, q, hq, hmq, hq2m, hqk, h_a_lt_p, h_a_bound, h_covers, _h_count,
      _h_excess, h_scaffold⟩ := hC (max K₀ 3)
  let h_covers' : ∀ j, 1 ≤ j → j ≤ k →
      ∃ p, p.Prime ∧ m ≤ p ∧ p ≤ k ∧ j % p = a p ∧
        (a p = 0 ∨ p ≤ k / 2 ∨ j ≤ p) := h_covers
  refine ⟨k, le_trans (le_max_left _ _) hkK₀, le_trans (le_max_right _ _) hkK₀, ?_⟩
  exact ⟨⟨a, q, hq, hmq, hq2m, hk4m, hqk, h_a_lt_p, h_a_bound, h_covers', h_scaffold⟩⟩

theorem residue_assignment_to_certificate
    {m k : ℕ} (hm : 3 ≤ m) (hk : 3 ≤ k)
    (assn : NonExcessResidueAssignment m k) :
    Nonempty (GlobalResidueCertificate m k) :=
  cover_to_certificate hm hk assn

theorem exists_residue_certificate_above
    (m K₀ : ℕ) (hm : 3 ≤ m) :
    ∃ k : ℕ, K₀ ≤ k ∧ 3 ≤ k ∧
      Nonempty (GlobalResidueCertificate m k) := by
  obtain ⟨k, hkK₀, hk3, ⟨assn⟩⟩ := exists_nonexcess_residue_assignment_above m K₀ hm
  exact ⟨k, hkK₀, hk3, residue_assignment_to_certificate hm hk3 assn⟩

noncomputable def Nk_formula (k : ℕ) : ℕ :=
  ∏ p ∈ (Finset.range (k + 1)).filter Nat.Prime, p ^ (Nat.log p k + 1)

theorem Nk_formula_pos (k : ℕ) : 0 < Nk_formula k := by
  unfold Nk_formula
  apply Finset.prod_pos
  intro p hp
  rw [Finset.mem_filter] at hp
  exact Nat.pow_pos (a := p) hp.2.pos

theorem Nk_formula_eq_globalMk (k : ℕ) : Nk_formula k = globalMk k := by
  unfold Nk_formula globalMk alphaP
  apply Finset.prod_congr
  · ext p
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
    refine ⟨fun ⟨hpk, hp⟩ => ⟨⟨hp.one_lt.le, by omega⟩, hp⟩,
            fun ⟨⟨_, hpk⟩, hp⟩ => ⟨by omega, hp⟩⟩
  · intros; rfl

theorem p_dvd_localMod {k p : ℕ} : p ∣ localMod k p := by
  unfold localMod
  exact dvd_pow_self p (by omega)

theorem p_dvd_localMod_int {k p : ℕ} : (p : ℤ) ∣ (localMod k p : ℤ) := by
  exact_mod_cast p_dvd_localMod (k := k) (p := p)

theorem R_local_mod_p_of_a {k : ℕ} (a : ℕ → ℕ) (p : ℕ) (hp_prime : p.Prime)
    (hp_le_k : p ≤ k) (R : ℤ)
    (hRloc : ∀ p ∈ primeSet k, R ≡ localResidue k a p [ZMOD (localMod k p : ℤ)]) :
    R ≡ localResidue k a p [ZMOD (p : ℤ)] := by
  have hp_in : p ∈ primeSet k := mem_primeSet.mpr ⟨hp_prime.one_lt.le, hp_le_k, hp_prime⟩
  exact Int.ModEq.of_dvd p_dvd_localMod_int (hRloc p hp_in)

theorem liftAtLevel_mod_p {a : ℕ → ℕ} {p u : ℕ} (hp : 1 < p) (hap : a p < p) (hu : 1 ≤ u) :
    liftAtLevel a p u % p = a p % p := by
  rw [Nat.mod_eq_of_lt hap]
  unfold liftAtLevel
  by_cases hap0 : a p = 0
  · rw [if_pos hap0, hap0]; simp
  · rw [if_neg hap0]
    have hu_ne : u ≠ 0 := by omega
    rw [if_neg hu_ne]
    by_cases h1 : u = 1
    · rw [if_pos h1, Nat.mod_eq_of_lt hap]
    · rw [if_neg h1]
      exact liftAbove_mod_p p u (a p) hp hap hu

theorem localLift_mod_p {k p : ℕ} {a : ℕ → ℕ} (hp_prime : p.Prime) (hap : a p < p) :
    (localLift k a p : ℤ) ≡ (a p : ℤ) [ZMOD (p : ℤ)] := by
  unfold localLift
  have hu : 1 ≤ alphaP k p + 1 := by omega
  have h_nat : liftAtLevel a p (alphaP k p + 1) % p = a p % p :=
    liftAtLevel_mod_p hp_prime.one_lt hap hu
  show (liftAtLevel a p (alphaP k p + 1) : ℤ) % p = (a p : ℤ) % p
  have h1 : ((liftAtLevel a p (alphaP k p + 1) : ℕ) : ℤ) % (p : ℤ) =
      ((liftAtLevel a p (alphaP k p + 1) % p : ℕ) : ℤ) := (Int.natCast_mod _ _).symm
  have h2 : ((a p : ℕ) : ℤ) % (p : ℤ) = ((a p % p : ℕ) : ℤ) := (Int.natCast_mod _ _).symm
  rw [h1, h2]; exact_mod_cast h_nat

theorem R_mod_p_eq_of_a {k : ℕ} (a : ℕ → ℕ) (p : ℕ) (hp_prime : p.Prime)
    (hp_le_k : p ≤ k) (ha_lt : a p < p) (R : ℤ)
    (hRloc : ∀ p ∈ primeSet k, R ≡ localResidue k a p [ZMOD (localMod k p : ℤ)]) :
    R ≡ (k : ℤ) - (a p : ℤ) [ZMOD (p : ℤ)] := by
  have hR := R_local_mod_p_of_a a p hp_prime hp_le_k R hRloc
  have h_lift := localLift_mod_p (k := k) hp_prime ha_lt
  unfold localResidue at hR
  exact hR.trans (Int.ModEq.sub_left (k : ℤ) h_lift)

theorem globalMk_factorization_at_prime (k p : ℕ) (hp : p.Prime) (hp_le : p ≤ k) :
    p ^ (alphaP k p + 1) ∣ globalMk k := by
  unfold globalMk
  have hp_mem : p ∈ (Finset.Icc 1 k).filter Nat.Prime :=
    Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp.one_lt.le, hp_le⟩, hp⟩
  exact Finset.dvd_prod_of_mem _ hp_mem

theorem Nk_formula_factorization (k p : ℕ) (hp : p.Prime) (hp_le : p ≤ k) :
    p ^ (Nat.log p k + 1) ∣ Nk_formula k := by
  rw [Nk_formula_eq_globalMk]
  exact globalMk_factorization_at_prime k p hp hp_le

theorem n_minus_i_v_p_eq_R_minus_i {k : ℕ} (R : ℤ) (n : ℤ) (p : ℕ)
    (hp : p.Prime) (hp_le : p ≤ k) (hn_mod : (globalMk k : ℤ) ∣ n - R) :
    (p : ℤ) ∣ (n - R) ∧ ∀ u : ℕ, u ≤ alphaP k p + 1 → ((p : ℤ) ^ u ∣ n - R) := by
  constructor
  · have h_pdvd_Mk : (p : ℤ) ∣ (globalMk k : ℤ) := by
      have h_nat : p ∣ globalMk k := by
        have hp_dvd_pow : p ∣ p ^ (alphaP k p + 1) := dvd_pow_self p (by omega)
        have hp_mem : p ∈ (Finset.Icc 1 k).filter Nat.Prime :=
          Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp.one_lt.le, hp_le⟩, hp⟩
        unfold globalMk
        exact hp_dvd_pow.trans (Finset.dvd_prod_of_mem _ hp_mem)
      exact_mod_cast h_nat
    exact h_pdvd_Mk.trans hn_mod
  · intro u hu
    have h_pow_dvd_Mk : (p : ℤ) ^ u ∣ (globalMk k : ℤ) := by
      have h_pow_dvd_alphap : p ^ u ∣ p ^ (alphaP k p + 1) := pow_dvd_pow p hu
      have h_alphap_dvd_Mk : p ^ (alphaP k p + 1) ∣ globalMk k :=
        globalMk_factorization_at_prime k p hp hp_le
      have h_nat : p ^ u ∣ globalMk k := h_pow_dvd_alphap.trans h_alphap_dvd_Mk
      exact_mod_cast h_nat
    exact h_pow_dvd_Mk.trans hn_mod

theorem alphaP_pow_le {p k : ℕ} (hp : 1 < p) (hk : 1 ≤ k) :
    p ^ alphaP k p ≤ k := by
  unfold alphaP
  exact Nat.pow_log_le_self p (by omega)

theorem alphaP_succ_pow_gt {p k : ℕ} (hp : 1 < p) :
    k < p ^ (alphaP k p + 1) := by
  unfold alphaP
  exact Nat.lt_pow_succ_log_self hp k

theorem alphaP_pow_succ_ne_zero {p k : ℕ} (hp : 1 < p) :
    p ^ (alphaP k p + 1) ≠ 0 := by
  apply Nat.pos_iff_ne_zero.mp
  exact Nat.pow_pos (a := p) (by omega : 0 < p)

noncomputable def levelCount (k m c : ℕ) : ℕ :=
  ((Finset.Ico 0 k).filter (· % m = c)).card

theorem levelCount_zero_iff (k m c : ℕ) : levelCount k m c = 0 ↔
    ∀ i, i < k → i % m ≠ c := by
  unfold levelCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  constructor
  · intro h i hi
    have hmem : i ∈ Finset.Ico 0 k := by
      rw [Finset.mem_Ico]; exact ⟨Nat.zero_le _, hi⟩
    exact h hmem
  · intro h i hi
    rw [Finset.mem_Ico] at hi
    exact h i hi.2

theorem levelCount_zero_of_c_ge_k (k m c : ℕ) (hc : k ≤ c) :
    levelCount k m c = 0 := by
  rw [levelCount_zero_iff]
  intro i hi hmod
  have hi_eq : i % m = i := by
    rcases Nat.eq_zero_or_pos m with hm0 | hm0
    · subst hm0
      have : i % 0 = i := Nat.mod_zero i
      rw [this] at hmod; omega
    · rcases lt_or_ge i m with him | him
      · exact Nat.mod_eq_of_lt him
      · have hc_lt_m : c < m := by
          have : i % m < m := Nat.mod_lt _ hm0
          omega
        omega
  omega

theorem alpha_p_succ_levelCount_zero_a_zero (k p : ℕ) (hp : 1 < p) :
    levelCount k (p ^ (alphaP k p + 1)) (k % p ^ (alphaP k p + 1)) = 0 := by
  apply levelCount_zero_of_c_ge_k
  have hk_lt : k < p ^ (alphaP k p + 1) := alphaP_succ_pow_gt hp
  rw [Nat.mod_eq_of_lt hk_lt]

theorem levelCount_eq_count (k m c : ℕ) :
    levelCount k m c = Nat.count (fun x => x % m = c) k := by
  rw [Nat.count_eq_card_filter_range]
  unfold levelCount
  rw [← Finset.range_eq_Ico]

theorem levelCount_formula (k m c : ℕ) (hm : 0 < m) (hc : c < m) :
    levelCount k m c = k / m + (if c < k % m then 1 else 0) := by
  rw [levelCount_eq_count]
  have h_eq : Nat.count (fun x => x % m = c) k =
      Nat.count (fun x => x ≡ c [MOD m]) k := by
    congr 1
    funext x
    unfold Nat.ModEq
    rw [Nat.mod_eq_of_lt hc, eq_comm]
  rw [h_eq, Nat.count_modEq_card k hm c, Nat.mod_eq_of_lt hc]

theorem levelCount_eq_div_of_non_excess (k m c : ℕ) (hm : 0 < m) (hc : c < m)
    (h_non_excess : k % m ≤ c) :
    levelCount k m c = k / m := by
  rw [levelCount_formula k m c hm hc]
  have : ¬ (c < k % m) := by omega
  simp [this]

theorem padicValNat_k_factorial (k p : ℕ) [hp : Fact p.Prime] :
    padicValNat p k.factorial = ∑ u ∈ Finset.Ico 1 (alphaP k p + 1), k / p ^ u := by
  apply padicValNat_factorial
  unfold alphaP
  omega

theorem sum_levelCount_eq_v_p_factorial_of_non_excess (k p : ℕ) [hp : Fact p.Prime]
    (c : ℕ → ℕ) (hc_bound : ∀ u, 1 ≤ u → c u < p ^ u)
    (hc_non_excess : ∀ u, 1 ≤ u → u ≤ alphaP k p → k % p ^ u ≤ c u) :
    ∑ u ∈ Finset.Ico 1 (alphaP k p + 1), levelCount k (p ^ u) (c u) =
      padicValNat p k.factorial := by
  rw [padicValNat_k_factorial k p]
  apply Finset.sum_congr rfl
  intro u hu
  rw [Finset.mem_Ico] at hu
  have hp_one : 1 < p := hp.out.one_lt
  have hp_pow_pos : 0 < p ^ u := Nat.pow_pos (a := p) (by omega : 0 < p)
  have hu_le : u ≤ alphaP k p := by omega
  exact levelCount_eq_div_of_non_excess k (p ^ u) (c u) hp_pow_pos (hc_bound u hu.1)
    (hc_non_excess u hu.1 hu_le)

theorem descFactorial_eq_factorial_mul_choose_padic (n k p : ℕ) [hp : Fact p.Prime]
    (hkn : k ≤ n) :
    padicValNat p (n.descFactorial k) =
      padicValNat p k.factorial + padicValNat p (n.choose k) := by
  rw [Nat.descFactorial_eq_factorial_mul_choose n k]
  rw [padicValNat.mul (Nat.factorial_ne_zero k) (Nat.choose_pos hkn).ne']

theorem padicValNat_eq_sum_indicator (p a U : ℕ) [hp : Fact p.Prime]
    (ha : a ≠ 0) (hU : padicValNat p a < U) :
    padicValNat p a = ∑ u ∈ Finset.Ico 1 U, (if p ^ u ∣ a then 1 else 0) := by
  set v := padicValNat p a with hv_def
  have hv_lt : v < U := hU
  have h_split : Finset.Ico 1 U = Finset.Ico 1 (v + 1) ∪ Finset.Ico (v + 1) U := by
    rw [← Finset.Ico_union_Ico_eq_Ico (by omega : 1 ≤ v + 1) (by omega : v + 1 ≤ U)]
  rw [h_split, Finset.sum_union (Finset.Ico_disjoint_Ico_consecutive 1 (v + 1) U)]
  have h_first : ∑ u ∈ Finset.Ico 1 (v + 1), (if p ^ u ∣ a then 1 else 0) = v := by
    have : ∀ u ∈ Finset.Ico 1 (v + 1), (if p ^ u ∣ a then 1 else 0) = 1 := by
      intro u hu
      rw [Finset.mem_Ico] at hu
      have hu_le : u ≤ v := by omega
      have : p ^ u ∣ a := (padicValNat_dvd_iff_le ha).mpr hu_le
      simp [this]
    rw [Finset.sum_congr rfl this]
    simp [Nat.card_Ico]
  have h_second : ∑ u ∈ Finset.Ico (v + 1) U, (if p ^ u ∣ a then 1 else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro u hu
    rw [Finset.mem_Ico] at hu
    have hu_gt : v < u := by omega
    have : ¬ p ^ u ∣ a := by
      intro hd
      have : u ≤ v := (padicValNat_dvd_iff_le ha).mp hd
      omega
    simp [this]
  rw [h_first, h_second]; omega

theorem dvd_sub_nat_iff_mod_eq (n i m : ℕ) (hi : i ≤ n) :
    m ∣ n - i ↔ i ≡ n [MOD m] :=
  (Nat.modEq_iff_dvd' hi).symm

theorem count_dvd_eq_levelCount (n k m : ℕ) (hkn : k ≤ n) (hm : 0 < m) :
    ∑ i ∈ Finset.range k, (if m ∣ n - i then 1 else 0) =
      levelCount k m (n % m) := by
  unfold levelCount
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul, mul_one]
  congr 1
  rw [← Finset.range_eq_Ico]
  apply Finset.filter_congr
  intro i hi
  rw [Finset.mem_range] at hi
  have hi_le : i ≤ n := by omega
  have h_iff : m ∣ n - i ↔ i ≡ n [MOD m] := dvd_sub_nat_iff_mod_eq n i m hi_le
  rw [h_iff]
  unfold Nat.ModEq
  exact Iff.rfl

theorem v_p_descFactorial_eq_sum_levelCount (n k p : ℕ) [hp : Fact p.Prime]
    (hkn : k ≤ n) (U : ℕ) (hU : ∀ i ∈ Finset.range k, padicValNat p (n - i) < U) :
    padicValNat p (n.descFactorial k) =
      ∑ u ∈ Finset.Ico 1 U, levelCount k (p ^ u) (n % p ^ u) := by
  rw [show n.descFactorial k = ∏ i ∈ Finset.range k, (n - i) from
       Nat.descFactorial_eq_prod_range n k]
  rw [show padicValNat p (∏ i ∈ Finset.range k, (n - i)) =
       ∑ i ∈ Finset.range k, padicValNat p (n - i) from ?_]
  · have h_step : ∀ i ∈ Finset.range k,
        padicValNat p (n - i) = ∑ u ∈ Finset.Ico 1 U, (if p ^ u ∣ n - i then 1 else 0) := by
      intro i hi
      rw [Finset.mem_range] at hi
      have hni_pos : 0 < n - i := by omega
      exact padicValNat_eq_sum_indicator p (n - i) U hni_pos.ne' (hU i (Finset.mem_range.mpr hi))
    rw [Finset.sum_congr rfl h_step]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u hu
    rw [Finset.mem_Ico] at hu
    have hpu_pos : 0 < p ^ u := Nat.pow_pos (a := p) hp.out.pos
    exact count_dvd_eq_levelCount n k (p ^ u) hkn hpu_pos
  · rw [← Nat.factorization_def _ hp.out]
    rw [Nat.factorization_prod (fun i hi => by
      rw [Finset.mem_range] at hi; omega)]
    rw [Finsupp.finset_sum_apply]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    rw [← Nat.factorization_def _ hp.out]

theorem v_p_bound_from_non_excess (n k p : ℕ) [hp : Fact p.Prime] (hkn : k ≤ n)
    (h_top : ∀ i ∈ Finset.range k, ¬ p ^ (alphaP k p + 1) ∣ n - i) :
    ∀ i ∈ Finset.range k, padicValNat p (n - i) < alphaP k p + 1 := by
  intro i hi
  rw [Finset.mem_range] at hi
  have hni_pos : 0 < n - i := by omega
  by_contra hge
  push_neg at hge
  have : p ^ (alphaP k p + 1) ∣ n - i :=
    (padicValNat_dvd_iff_le hni_pos.ne').mpr hge
  exact h_top i (Finset.mem_range.mpr hi) this

theorem p_not_dvd_choose_of_non_excess (n k p : ℕ) [hp : Fact p.Prime] (hkn : k ≤ n)
    (h_top : ∀ i ∈ Finset.range k, ¬ p ^ (alphaP k p + 1) ∣ n - i)
    (h_non_excess : ∀ u, 1 ≤ u → u ≤ alphaP k p → k % p ^ u ≤ (n % p ^ u)) :
    ¬ p ∣ Nat.choose n k := by
  have hU := v_p_bound_from_non_excess n k p hkn h_top
  have h_val_sum := v_p_descFactorial_eq_sum_levelCount n k p hkn (alphaP k p + 1) hU
  have h_bound : ∀ u, 1 ≤ u → n % p ^ u < p ^ u := fun u _ =>
    Nat.mod_lt _ (Nat.pow_pos (a := p) hp.out.pos)
  have h_levelcount := sum_levelCount_eq_v_p_factorial_of_non_excess k p
    (fun u => n % p ^ u) (fun u hu => h_bound u hu)
    (fun u hu hu_le => h_non_excess u hu hu_le)
  rw [h_levelcount] at h_val_sum
  have h_desc_decomp := descFactorial_eq_factorial_mul_choose_padic n k p hkn
  rw [h_desc_decomp] at h_val_sum
  have h_choose_zero : padicValNat p (n.choose k) = 0 := by omega
  have hch_ne : n.choose k ≠ 0 := (Nat.choose_pos hkn).ne'
  intro hdvd
  have h_ge : 1 ≤ padicValNat p (n.choose k) :=
    (padicValNat_dvd_iff_le hch_ne).mp (by simpa using hdvd)
  omega

def IsNonExcessAt (a : ℕ → ℕ) (k p : ℕ) : Prop :=
  a p = 0 ∨ k % p < a p

def AllNonExcess (a : ℕ → ℕ) (k m : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → m ≤ p → p ≤ k → IsNonExcessAt a k p

theorem IsNonExcessAt_of_zero {a : ℕ → ℕ} {k p : ℕ} (hap : a p = 0) :
    IsNonExcessAt a k p := Or.inl hap

theorem IsNonExcessAt_of_excess_witness {a : ℕ → ℕ} {k p : ℕ}
    (hap : a p ≠ 0) (h : k % p < a p) : IsNonExcessAt a k p := Or.inr h

theorem k_mod_p_le_a_p_of_non_excess {a : ℕ → ℕ} {k p : ℕ}
    (h : IsNonExcessAt a k p) (hap_lt : a p < p) :
    k % p ≤ a p ∨ a p = 0 := by
  rcases h with h | h
  · exact Or.inr h
  · exact Or.inl (le_of_lt h)

theorem IsNonExcessAt_of_zero_or_anchor_buffer {a : ℕ → ℕ} {k p m q : ℕ}
    (h_struct : a p ≠ 0 → p = q ∨ (k / 2 < p ∧ p ≤ k ∧ p % q = 1))
    (hq_dvd_k : q ∣ k) (hap_lt : a p < p) (hap_pos : 1 ≤ a p ∨ a p = 0)
    (h_anchor_residue : p = q → a p = 1) :
    a p = 0 ∨ (p = q ∨ (k / 2 < p ∧ p ≤ k ∧ p % q = 1)) := by
  by_cases hap : a p = 0
  · exact Or.inl hap
  · exact Or.inr (h_struct hap)

theorem anchor_non_excess {a : ℕ → ℕ} {k q : ℕ} (hq_dvd_k : q ∣ k)
    (ha_q : a q = 1) : k % q < a q := by
  have : k % q = 0 := Nat.mod_eq_zero_of_dvd hq_dvd_k
  rw [this, ha_q]; omega

noncomputable def deltaConst : ℝ := 1 / 20

theorem deltaConst_pos : 0 < deltaConst := by unfold deltaConst; norm_num

theorem deltaConst_lt_one_tenth : deltaConst < 1 / 10 := by unfold deltaConst; norm_num

def M_B (B : ℕ) : ℕ := B * 21

theorem M_B_pos (B : ℕ) (hB : 1 ≤ B) : 0 < M_B B := by
  unfold M_B; omega

def A_const (B : ℕ) : ℕ := 100 * (M_B B + 10)

theorem A_const_pos (B : ℕ) (hB : 1 ≤ B) : 0 < A_const B := by
  unfold A_const M_B; omega

noncomputable def Y_param (X : ℝ) (A : ℕ) : ℝ := Real.log X ^ A

theorem Y_param_pos {X : ℝ} {A : ℕ} (hX : Real.exp 1 < X) : 0 < Y_param X A := by
  unfold Y_param
  have h_log_pos : 0 < Real.log X := by
    have h1 : Real.log (Real.exp 1) = 1 := Real.log_exp 1
    have h2 : Real.log (Real.exp 1) < Real.log X :=
      Real.log_lt_log (by positivity) hX
    rw [h1] at h2; linarith
  positivity

noncomputable def zQ (j Q : ℕ) : ℕ := j / Q ^ (padicValNat Q j)

noncomputable def smallDeficientSet (B Y Q : ℕ) : Finset ℕ :=
  (Finset.Icc 1 Y).filter (fun j => j % Q ≠ 1 ∧ zQ j Q < B)

theorem smallDeficientSet_subset (B Y Q : ℕ) :
    smallDeficientSet B Y Q ⊆ Finset.Icc 1 Y :=
  Finset.filter_subset _ _

theorem smallDeficientSet_card_le_Y (B Y Q : ℕ) :
    (smallDeficientSet B Y Q).card ≤ Y := by
  calc (smallDeficientSet B Y Q).card
      ≤ (Finset.Icc 1 Y).card := Finset.card_le_card (smallDeficientSet_subset B Y Q)
    _ = Y := by rw [Nat.card_Icc]; omega

theorem zQ_mul_Q_pow_eq (j Q : ℕ) (hQ : 1 < Q) :
    zQ j Q * Q ^ (padicValNat Q j) = j := by
  unfold zQ
  exact Nat.div_mul_cancel (pow_padicValNat_dvd)

theorem zQ_pos {j Q : ℕ} (hj : 0 < j) (hQ : 1 < Q) : 0 < zQ j Q := by
  have h := zQ_mul_Q_pow_eq j Q hQ
  have hQpow_pos : 0 < Q ^ (padicValNat Q j) := Nat.pow_pos (a := Q) (by omega)
  by_contra hz
  push_neg at hz
  interval_cases (zQ j Q)
  · simp at h; omega

theorem padicValNat_le_log {j Q : ℕ} (hj : 0 < j) (hQ : 1 < Q) :
    padicValNat Q j ≤ Nat.log Q j := by
  have h_dvd : Q ^ (padicValNat Q j) ∣ j := pow_padicValNat_dvd
  exact Nat.le_log_of_pow_le hQ (Nat.le_of_dvd hj h_dvd)

theorem padicValNat_le_log_of_le {j Y Q : ℕ} (hj : 0 < j) (hjY : j ≤ Y) (hQ : 1 < Q) :
    padicValNat Q j ≤ Nat.log Q Y :=
  (padicValNat_le_log hj hQ).trans (Nat.log_mono_right hjY)

theorem smallDeficientSet_card_le_inj (B Y Q : ℕ) (hQ : 1 < Q) :
    (smallDeficientSet B Y Q).card ≤ B * (Nat.log Q Y + 1) := by
  classical
  set f : ℕ → ℕ × ℕ := fun j => (zQ j Q, padicValNat Q j)
  have h_mem : ∀ j ∈ smallDeficientSet B Y Q, 1 ≤ j ∧ j ≤ Y ∧ zQ j Q < B := by
    intro j hj
    unfold smallDeficientSet at hj
    rw [Finset.mem_filter, Finset.mem_Icc] at hj
    exact ⟨hj.1.1, hj.1.2, hj.2.2⟩
  have f_inj : Set.InjOn f (smallDeficientSet B Y Q) := by
    intro j hj k hk hjk
    obtain ⟨hj_pos, _, _⟩ := h_mem j hj
    obtain ⟨hk_pos, _, _⟩ := h_mem k hk
    have h1 := zQ_mul_Q_pow_eq j Q hQ
    have h2 := zQ_mul_Q_pow_eq k Q hQ
    simp only [Prod.mk.injEq, f] at hjk
    rw [hjk.1, hjk.2] at h1
    linarith
  have h_target : ∀ j ∈ smallDeficientSet B Y Q,
      f j ∈ Finset.Ico 1 (B + 1) ×ˢ Finset.Iic (Nat.log Q Y) := by
    intro j hj
    obtain ⟨hj_pos, hjY, hzQ⟩ := h_mem j hj
    simp only [Finset.mem_product, Finset.mem_Ico, Finset.mem_Iic, f]
    refine ⟨⟨zQ_pos (by omega) hQ, by omega⟩, ?_⟩
    exact padicValNat_le_log_of_le (by omega) hjY hQ
  calc (smallDeficientSet B Y Q).card
      = ((smallDeficientSet B Y Q).image f).card := (Finset.card_image_of_injOn f_inj).symm
    _ ≤ (Finset.Ico 1 (B + 1) ×ˢ Finset.Iic (Nat.log Q Y)).card := by
        apply Finset.card_le_card
        intro x hx
        simp only [Finset.mem_image] at hx
        obtain ⟨j, hj_mem, rfl⟩ := hx
        exact h_target j hj_mem
    _ = B * (Nat.log Q Y + 1) := by
        rw [Finset.card_product, Nat.card_Ico, Nat.card_Iic]
        have : B + 1 - 1 = B := by omega
        rw [this]

noncomputable def zSet (t : ℕ) (Q : ℕ) (bs : Finset ℕ) : ℕ :=
  t / (Q ^ padicValNat Q t * ∏ b ∈ bs, b ^ padicValNat b t)

noncomputable def residualSet (B X Y Q : ℕ) (b : ℕ → ℕ) : Finset ℕ :=
  (Finset.Icc 1 (2 * X)).filter (fun t =>
    zSet t Q ((smallDeficientSet B Y Q).image b) < B ∧
    t % Q ≠ 1 ∧
    ∀ d ∈ smallDeficientSet B Y Q, t % b d ≠ d)

theorem residualSet_subset (B X Y Q : ℕ) (b : ℕ → ℕ) :
    residualSet B X Y Q b ⊆ Finset.Icc 1 (2 * X) :=
  Finset.filter_subset _ _

theorem residualSet_mono_X
    {B X₁ X₂ Y q : ℕ} {b : ℕ → ℕ} (hX : X₁ ≤ X₂) :
    residualSet B X₁ Y q b ⊆ residualSet B X₂ Y q b := by
  intro t ht
  unfold residualSet at ht ⊢
  rw [Finset.mem_filter, Finset.mem_Icc] at ht ⊢
  obtain ⟨⟨ht1, ht2⟩, hz, hqm, hb⟩ := ht
  refine ⟨⟨ht1, ?_⟩, hz, hqm, hb⟩
  omega

theorem residualSet_ext_of_agree_on_D
    {B X Y q : ℕ} {b₁ b₂ : ℕ → ℕ}
    (h_agree : ∀ d ∈ smallDeficientSet B Y q, b₁ d = b₂ d) :
    residualSet B X Y q b₁ = residualSet B X Y q b₂ := by
  unfold residualSet
  ext t
  rw [Finset.mem_filter, Finset.mem_filter]
  have h_image_eq :
      (smallDeficientSet B Y q).image b₁ =
        (smallDeficientSet B Y q).image b₂ := by
    apply Finset.image_congr
    intro d hd
    exact h_agree d hd
  have h_zSet_eq :
      zSet t q ((smallDeficientSet B Y q).image b₁) =
        zSet t q ((smallDeficientSet B Y q).image b₂) := by
    rw [h_image_eq]
  have h_dvd_cond :
      (∀ d ∈ smallDeficientSet B Y q, t % b₁ d ≠ d) ↔
      (∀ d ∈ smallDeficientSet B Y q, t % b₂ d ≠ d) := by
    constructor
    · intro h d hd; rw [← h_agree d hd]; exact h d hd
    · intro h d hd; rw [h_agree d hd]; exact h d hd
  constructor
  · rintro ⟨ht_in, hz, hqm, hb⟩
    refine ⟨ht_in, ?_, hqm, ?_⟩
    · rw [← h_zSet_eq]; exact hz
    · exact h_dvd_cond.mp hb
  · rintro ⟨ht_in, hz, hqm, hb⟩
    refine ⟨ht_in, ?_, hqm, ?_⟩
    · rw [h_zSet_eq]; exact hz
    · exact h_dvd_cond.mpr hb

noncomputable def H_X (M_B : ℕ) (X : ℕ) : ℕ := (Nat.log 2 X + 1) ^ (M_B + 5)

theorem H_X_pos (M_B X : ℕ) (hX : 1 ≤ X) : 0 < H_X M_B X := by
  unfold H_X
  exact Nat.pow_pos (a := Nat.log 2 X + 1) (by omega)

theorem M_B_ge {B : ℕ} (hB : 1 ≤ B) : 21 ≤ M_B B := by
  unfold M_B; omega

theorem M_B_eq_21B (B : ℕ) : M_B B = 21 * B := by
  unfold M_B; ring

theorem A_const_eq (B : ℕ) : A_const B = 100 * (21 * B + 10) := by
  unfold A_const M_B; ring

theorem Y_param_def (X : ℝ) (A : ℕ) : Y_param X A = Real.log X ^ A := rfl

theorem H_X_def (M_B X : ℕ) : H_X M_B X = (Nat.log 2 X + 1) ^ (M_B + 5) := rfl

theorem H_X_ge_one (M_B X : ℕ) (hX : 1 ≤ X) : 1 ≤ H_X M_B X := H_X_pos M_B X hX

theorem H_X_monotone_in_X {M_B X X' : ℕ} (hX : X ≤ X') : H_X M_B X ≤ H_X M_B X' := by
  unfold H_X
  exact Nat.pow_le_pow_left (by have := Nat.log_mono_right (b := 2) hX; omega) _

theorem log_Q_Y_le_of_pow_gt {Q Y : ℕ} (hQ : 1 < Q) (N : ℕ) (h : Y < Q ^ (N + 1)) :
    Nat.log Q Y ≤ N := by
  by_contra h_gt
  push_neg at h_gt
  have hY_pos : 0 < Y := by
    rcases Nat.eq_zero_or_pos Y with hY0 | hY0
    · subst hY0
      have : Nat.log Q 0 = 0 := Nat.log_zero_right Q
      omega
    · exact hY0
  have h_pow_le : Q ^ (N + 1) ≤ Y :=
    (Nat.le_log_iff_pow_le (by omega) hY_pos.ne').mp h_gt
  omega

theorem smallDeficientSet_card_le_via_log {B Y Q N : ℕ} (hQ : 1 < Q) (h_log : Y < Q ^ (N + 1)) :
    (smallDeficientSet B Y Q).card ≤ B * (N + 1) := by
  calc (smallDeficientSet B Y Q).card
      ≤ B * (Nat.log Q Y + 1) := smallDeficientSet_card_le_inj B Y Q hQ
    _ ≤ B * (N + 1) := by
        apply Nat.mul_le_mul_left
        have := log_Q_Y_le_of_pow_gt hQ N h_log
        omega

noncomputable def W_product (Q : ℕ) (B Y : ℕ) (b : ℕ → ℕ) : ℕ :=
  Q * ∏ d ∈ smallDeficientSet B Y Q, b d

theorem W_product_pos {Q B Y : ℕ} {b : ℕ → ℕ} (hQ : 0 < Q)
    (hb : ∀ d ∈ smallDeficientSet B Y Q, 0 < b d) :
    0 < W_product Q B Y b := by
  unfold W_product
  exact Nat.mul_pos hQ (Finset.prod_pos hb)

theorem Q_dvd_W (Q B Y : ℕ) (b : ℕ → ℕ) : Q ∣ W_product Q B Y b :=
  ⟨_, rfl⟩

theorem buffer_dvd_W (Q B Y : ℕ) (b : ℕ → ℕ) (d : ℕ)
    (hd : d ∈ smallDeficientSet B Y Q) :
    b d ∣ W_product Q B Y b := by
  unfold W_product
  exact (Finset.dvd_prod_of_mem b hd).mul_left Q

theorem W_le_Q_pow_card_card {Q B Y N : ℕ} {b : ℕ → ℕ}
    (hQ : 1 < Q) (h_log : Y < Q ^ (N + 1))
    (hb_le : ∀ d ∈ smallDeficientSet B Y Q, b d ≤ Q ^ N) :
    W_product Q B Y b ≤ Q ^ (1 + (smallDeficientSet B Y Q).card * N) := by
  unfold W_product
  calc Q * ∏ d ∈ smallDeficientSet B Y Q, b d
      ≤ Q * ∏ _d ∈ smallDeficientSet B Y Q, Q ^ N := by
        apply Nat.mul_le_mul_left
        apply Finset.prod_le_prod (fun _ _ => Nat.zero_le _) hb_le
    _ = Q * Q ^ ((smallDeficientSet B Y Q).card * N) := by
        rw [Finset.prod_const, ← pow_mul]; ring_nf
    _ = Q ^ (1 + (smallDeficientSet B Y Q).card * N) := by
        rw [add_comm, pow_succ]; ring

theorem padicValNat_eq_zero_of_lt {p n : ℕ} (hp : 1 < p) (h : n < p) :
    padicValNat p n = 0 := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp [padicValNat]
  · by_contra hne
    have h_pos : 0 < padicValNat p n := Nat.pos_of_ne_zero hne
    have h_p_dvd : p ∣ n := by
      have h_pow_dvd : p ^ padicValNat p n ∣ n := pow_padicValNat_dvd
      have h_p_dvd_pow : p ∣ p ^ padicValNat p n := dvd_pow_self p h_pos.ne'
      exact h_p_dvd_pow.trans h_pow_dvd
    have h_p_le : p ≤ n := Nat.le_of_dvd hn h_p_dvd
    omega

theorem padicValNat_eq_zero_of_le_lt {n p : ℕ} (hp : 1 < p) (h_le : n ≤ p - 1) :
    padicValNat p n = 0 :=
  padicValNat_eq_zero_of_lt hp (by omega)

theorem padicValNat_b_d_eq_zero_of_t_lt {B Y Q : ℕ} {b : ℕ → ℕ} {d t : ℕ}
    (hd_mem : d ∈ smallDeficientSet B Y Q) (h_b_gt_t : t < b d) (hb : 1 < b d) :
    padicValNat (b d) t = 0 :=
  padicValNat_eq_zero_of_lt hb h_b_gt_t

theorem buffer_prod_padicValNat_eq_one {B Y Q t : ℕ} {b : ℕ → ℕ}
    (h_t_lt_b : ∀ d ∈ smallDeficientSet B Y Q, t < b d)
    (h_b_gt_1 : ∀ d ∈ smallDeficientSet B Y Q, 1 < b d) :
    ∏ d ∈ smallDeficientSet B Y Q, b d ^ padicValNat (b d) t = 1 := by
  apply Finset.prod_eq_one
  intro d hd
  rw [padicValNat_eq_zero_of_lt (h_b_gt_1 d hd) (h_t_lt_b d hd)]
  simp

theorem mod_self_eq_self_of_lt {t b : ℕ} (h : t < b) : t % b = t :=
  Nat.mod_eq_of_lt h

theorem buffer_self_in_D_Y_contradicts_residual
    {B X Y Q : ℕ} {b : ℕ → ℕ} {t : ℕ}
    (h_t_in_D : t ∈ smallDeficientSet B Y Q)
    (h_t_lt_b : t < b t)
    (h_t_in_U : t ∈ residualSet B X Y Q b) : False := by
  unfold residualSet at h_t_in_U
  rw [Finset.mem_filter] at h_t_in_U
  obtain ⟨_, _, _, h_t_mod_b⟩ := h_t_in_U
  have h_t_mod_b_t : t % b t ≠ t := h_t_mod_b t h_t_in_D
  exact h_t_mod_b_t (mod_self_eq_self_of_lt h_t_lt_b)

noncomputable def Z_modulus (k : ℕ) (a : ℕ → ℕ) : ℕ :=
  ∏ p ∈ (Finset.Icc 1 k).filter (fun p => p.Prime ∧ a p = 0),
    p ^ (Nat.log p k + 1)

theorem Z_modulus_pos (k : ℕ) (a : ℕ → ℕ) : 0 < Z_modulus k a := by
  unfold Z_modulus
  apply Finset.prod_pos
  intro p hp
  rw [Finset.mem_filter] at hp
  exact Nat.pow_pos (a := p) hp.2.1.pos

theorem Z_modulus_dvd_globalMk {k : ℕ} (a : ℕ → ℕ) :
    Z_modulus k a ∣ globalMk k := by
  unfold Z_modulus globalMk
    alphaP
  apply Finset.prod_dvd_prod_of_subset
  intro p hp
  rw [Finset.mem_filter] at hp ⊢
  exact ⟨hp.1, hp.2.1⟩

theorem Nat_log_p_eq_one_of_lt_sq {p k : ℕ} (hp : 1 < p) (hp_le : p ≤ k)
    (hp_sq_gt : k < p * p) :
    Nat.log p k = 1 := by
  rw [Nat.log_eq_one_iff']
  exact ⟨hp_le, hp_sq_gt⟩

theorem prime_in_third_to_half_log_one {k p : ℕ} (hp : 1 < p) (hk_ge : 10 ≤ k)
    (hp_range : k / 3 < p ∧ p ≤ k / 2) : Nat.log p k = 1 := by
  have h_p_sq_gt : k < p * p := by
    have h_p_gt : k / 3 < p := hp_range.1
    have h_3p_gt_k : k ≤ 3 * (k / 3) + 2 := by omega
    nlinarith
  have h_p_le_k : p ≤ k := by have := hp_range.2; omega
  exact Nat_log_p_eq_one_of_lt_sq hp h_p_le_k h_p_sq_gt

theorem prime_in_third_to_half_zero_residue
    {k p : ℕ} {a : ℕ → ℕ} {q : ℕ} {bs : Finset ℕ} {scaffolds : Finset ℕ}
    (h_struct : ∀ r, r.Prime → a r ≠ 0 → r = q ∨ r ∈ bs ∨ r ∈ scaffolds)
    (h_q_small : q ≤ k / 3) (h_bs_small : ∀ b ∈ bs, b ≤ k / 3)
    (h_scaffolds_large : ∀ s ∈ scaffolds, k / 2 < s)
    (hp : p.Prime) (hp_range : k / 3 < p ∧ p ≤ k / 2) :
    a p = 0 := by
  by_contra h_ne
  rcases h_struct p hp h_ne with h_eq | h_mem_bs | h_mem_scaffolds
  · subst h_eq
    omega
  · have : p ≤ k / 3 := h_bs_small p h_mem_bs
    omega
  · have : k / 2 < p := h_scaffolds_large p h_mem_scaffolds
    omega

theorem Z_modulus_ge_prod_subset {k : ℕ} (a : ℕ → ℕ)
    (S : Finset ℕ) (hS_sub : S ⊆ (Finset.Icc 1 k).filter (fun p => p.Prime ∧ a p = 0))
    (h_pow_le : ∀ p ∈ S, p ^ 2 ≤ p ^ (Nat.log p k + 1)) :
    ∏ p ∈ S, p ^ 2 ≤ Z_modulus k a := by
  unfold Z_modulus
  calc ∏ p ∈ S, p ^ 2
      ≤ ∏ p ∈ S, p ^ (Nat.log p k + 1) :=
        Finset.prod_le_prod (fun p _ => Nat.zero_le _) h_pow_le
    _ ≤ ∏ p ∈ (Finset.Icc 1 k).filter (fun p => p.Prime ∧ a p = 0),
          p ^ (Nat.log p k + 1) := by
        apply Finset.prod_le_prod_of_subset_of_one_le' hS_sub
        intro p hp_mem _
        rw [Finset.mem_filter, Finset.mem_Icc] at hp_mem
        have hp_pos : 0 < p := by omega
        have : 0 < p ^ (Nat.log p k + 1) := Nat.pow_pos hp_pos
        omega

theorem n_ge_k_plus_Z_of_progression
    {k : ℕ} {a : ℕ → ℕ} {N_k α_k : ℕ} {n : ℕ}
    (h_Z_dvd_N : Z_modulus k a ∣ N_k)
    (h_alpha_mod_Z : α_k % Z_modulus k a = k % Z_modulus k a)
    (h_n_mod : n % N_k = α_k % N_k) (h_n_gt : k < n) :
    k + Z_modulus k a ≤ n := by
  have h_Z_pos : 0 < Z_modulus k a := Z_modulus_pos k a
  have h_n_mod_Z : n % Z_modulus k a = k % Z_modulus k a := by
    have h_n_eq_alpha_mod_Z : n % Z_modulus k a = α_k % Z_modulus k a := by
      have h_step : n % Z_modulus k a = (n % N_k) % Z_modulus k a :=
        (Nat.mod_mod_of_dvd n h_Z_dvd_N).symm
      have h_step2 : α_k % Z_modulus k a = (α_k % N_k) % Z_modulus k a :=
        (Nat.mod_mod_of_dvd α_k h_Z_dvd_N).symm
      rw [h_step, h_step2, h_n_mod]
    rw [h_n_eq_alpha_mod_Z, h_alpha_mod_Z]
  have h_Z_dvd_n_k : Z_modulus k a ∣ n - k := by
    have h_diff : n % Z_modulus k a = k % Z_modulus k a := h_n_mod_Z
    have hk_le : k ≤ n := by omega
    exact (Nat.modEq_iff_dvd' hk_le).mp h_diff.symm
  have h_pos_diff : 0 < n - k := by omega
  have : Z_modulus k a ≤ n - k := Nat.le_of_dvd h_pos_diff h_Z_dvd_n_k
  omega

theorem B_j_le_prod_prime_powers_le_k {k : ℕ} (P_plus : Finset ℕ)
    (h_subset : P_plus ⊆ (Finset.Icc 1 k).filter Nat.Prime) (e : ℕ → ℕ)
    (h_e_le : ∀ p ∈ P_plus, p ^ e p ≤ k) :
    ∏ p ∈ P_plus, p ^ e p ≤ k ^ P_plus.card := by
  calc ∏ p ∈ P_plus, p ^ e p
      ≤ ∏ _p ∈ P_plus, k := Finset.prod_le_prod (fun _ _ => Nat.zero_le _) h_e_le
    _ = k ^ P_plus.card := by rw [Finset.prod_const]

theorem n_k_j_gt_B_j {n k j Z B_j : ℕ} (hn : k + Z ≤ n) (h_Z_gt : B_j < Z)
    (hj : 1 ≤ j) : B_j < n - k + j := by omega

theorem L_j_gt_one {n k j B_j : ℕ} (h_div : B_j ∣ n - k + j)
    (h_gt : B_j < n - k + j) (hB_j_pos : 0 < B_j) :
    1 < (n - k + j) / B_j := by
  by_contra h_le
  push_neg at h_le
  have h_div_eq : (n - k + j) = B_j * ((n - k + j) / B_j) := (Nat.div_mul_cancel h_div).symm |>.trans (by ring)
  have : (n - k + j) ≤ B_j * 1 := by
    calc n - k + j = B_j * ((n - k + j) / B_j) := h_div_eq
      _ ≤ B_j * 1 := Nat.mul_le_mul_left B_j h_le
  omega

theorem L_j_has_prime_factor_gt_k
    {L_j k : ℕ} (hL_gt_one : 1 < L_j)
    (h_no_small_prime : ∀ p : ℕ, p.Prime → p ≤ k → ¬ p ∣ L_j) :
    ∃ p, p.Prime ∧ k < p ∧ p ∣ L_j := by
  obtain ⟨p, hp_prime, hp_dvd⟩ := Nat.exists_prime_and_dvd hL_gt_one.ne'
  refine ⟨p, hp_prime, ?_, hp_dvd⟩
  by_contra h_le
  push_neg at h_le
  exact h_no_small_prime p hp_prime h_le hp_dvd

theorem n_sub_i_eq_n_sub_k_plus_j {n k i : ℕ} (hi : i < k) (hk_le_n : k ≤ n) :
    n - i = n - k + (k - i) := by omega

theorem n_sub_i_has_prime_ge_B
    {n k i B_j : ℕ} (hi : i < k) (hk_le_n : k ≤ n)
    (h_Bj_dvd : B_j ∣ n - k + (k - i))
    (h_Lj_gt_one : 1 < (n - k + (k - i)) / B_j)
    (h_no_small_prime : ∀ p : ℕ, p.Prime → p ≤ k →
      ¬ p ∣ (n - k + (k - i)) / B_j)
    (hB_j_pos : 0 < B_j) (hkB : B ≤ k) :
    ∃ p, p.Prime ∧ B ≤ p ∧ p ∣ n - i := by
  obtain ⟨p, hp_prime, hp_gt_k, hp_dvd_Lj⟩ :=
    L_j_has_prime_factor_gt_k h_Lj_gt_one h_no_small_prime
  refine ⟨p, hp_prime, ?_, ?_⟩
  · omega
  · rw [n_sub_i_eq_n_sub_k_plus_j hi hk_le_n]
    have h_Lj_dvd : (n - k + (k - i)) / B_j ∣ n - k + (k - i) := Nat.div_dvd_of_dvd h_Bj_dvd
    exact hp_dvd_Lj.trans h_Lj_dvd

theorem L_j_dvd_n_sub_k_plus_j {n k j B_j : ℕ} (h_div : B_j ∣ n - k + j) :
    (n - k + j) / B_j ∣ n - k + j := Nat.div_dvd_of_dvd h_div

theorem Z_modulus_dvd_Nk_formula {k : ℕ} (a : ℕ → ℕ) :
    Z_modulus k a ∣ Nk_formula k := by
  rw [Nk_formula_eq_globalMk]
  exact Z_modulus_dvd_globalMk a

noncomputable def P_plus (k : ℕ) (a : ℕ → ℕ) : Finset ℕ :=
  (Finset.Icc 1 k).filter (fun p => p.Prime ∧ a p ≠ 0)

theorem P_plus_subset_primes (k : ℕ) (a : ℕ → ℕ) :
    P_plus k a ⊆ (Finset.Icc 1 k).filter Nat.Prime := by
  intro p hp
  simp only [P_plus, Finset.mem_filter, Finset.mem_Icc] at hp
  simp only [Finset.mem_filter, Finset.mem_Icc]
  exact ⟨hp.1, hp.2.1⟩

theorem P_plus_card_le_of_structure
    {k Q : ℕ} (a : ℕ → ℕ) (D_Y_image : Finset ℕ) (U_X_image : Finset ℕ)
    (h_struct : ∀ p, p.Prime → 1 ≤ p → p ≤ k → a p ≠ 0 →
      p = Q ∨ p ∈ D_Y_image ∨ p ∈ U_X_image) :
    (P_plus k a).card ≤ 1 + D_Y_image.card + U_X_image.card := by
  classical
  have h_subset : P_plus k a ⊆ {Q} ∪ D_Y_image ∪ U_X_image := by
    intro p hp
    simp only [P_plus, Finset.mem_filter, Finset.mem_Icc] at hp
    rcases h_struct p hp.2.1 hp.1.1 hp.1.2 hp.2.2 with hQ | hD | hU
    · subst hQ; simp
    · simp [hD]
    · simp [hU]
  calc (P_plus k a).card
      ≤ ({Q} ∪ D_Y_image ∪ U_X_image).card := Finset.card_le_card h_subset
    _ ≤ ({Q} ∪ D_Y_image).card + U_X_image.card := Finset.card_union_le _ _
    _ ≤ ({Q} : Finset ℕ).card + D_Y_image.card + U_X_image.card := by
        have := Finset.card_union_le ({Q} : Finset ℕ) D_Y_image
        omega
    _ = 1 + D_Y_image.card + U_X_image.card := by simp

theorem B_j_le_k_pow_P_plus_card
    {k : ℕ} (a : ℕ → ℕ) (e : ℕ → ℕ)
    (h_e_le : ∀ p ∈ P_plus k a, p ^ e p ≤ k) :
    ∏ p ∈ P_plus k a, p ^ e p ≤ k ^ (P_plus k a).card :=
  B_j_le_prod_prime_powers_le_k (P_plus k a) (P_plus_subset_primes k a) e h_e_le

theorem D_Y_card_le_via_M_B {B Y Q N : ℕ} (hQ : 1 < Q) (h_log : Y < Q ^ (N + 1))
    (h_M_B : M_B B = B * (N + 1)) :
    (smallDeficientSet B Y Q).card ≤ M_B B := by
  rw [h_M_B]; exact smallDeficientSet_card_le_via_log hQ h_log

theorem one_plus_DY_plus_UX_le_two_HX
    {DY_card UX_card HX : ℕ}
    (h_DY_le : DY_card + 1 ≤ HX) (h_UX_le : UX_card ≤ HX) :
    1 + DY_card + UX_card ≤ 2 * HX := by omega

theorem P_plus_card_le_2_HX
    {k Q : ℕ} (a : ℕ → ℕ) (D_Y_image U_X_image : Finset ℕ) (HX : ℕ)
    (h_struct : ∀ p, p.Prime → 1 ≤ p → p ≤ k → a p ≠ 0 →
      p = Q ∨ p ∈ D_Y_image ∨ p ∈ U_X_image)
    (h_DY : D_Y_image.card + 1 ≤ HX) (h_UX : U_X_image.card ≤ HX) :
    (P_plus k a).card ≤ 2 * HX :=
  (P_plus_card_le_of_structure a D_Y_image U_X_image h_struct).trans
    (one_plus_DY_plus_UX_le_two_HX h_DY h_UX)

theorem two_pow_ge_succ (n : ℕ) : n + 1 ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ k ih =>
    have h1 : 2 ^ (k + 1) = 2 ^ k * 2 := by ring
    have h2 : 2 ^ k * 2 = 2 ^ k + 2 ^ k := by ring
    have h_pos : 1 ≤ 2 ^ k := Nat.one_le_pow _ _ (by omega)
    omega

theorem H_X_ge_M_B_succ (M_B X : ℕ) (hX : 2 ≤ X) :
    M_B + 1 ≤ H_X M_B X := by
  unfold H_X
  have h_log_ge : 1 ≤ Nat.log 2 X := by
    rw [Nat.one_le_iff_ne_zero]
    intro h_eq
    have := Nat.log_eq_zero_iff.mp h_eq
    omega
  have h_base_ge : 2 ≤ Nat.log 2 X + 1 := by omega
  have h_pow_ge : 2 ^ (M_B + 5) ≤ (Nat.log 2 X + 1) ^ (M_B + 5) := by
    exact Nat.pow_le_pow_left h_base_ge _
  have h_succ : M_B + 5 + 1 ≤ 2 ^ (M_B + 5) := two_pow_ge_succ _
  omega

theorem D_Y_card_succ_le_H_X
    {B Y Q N X : ℕ} (hQ : 1 < Q) (h_log : Y < Q ^ (N + 1))
    (h_M_B : M_B B = B * (N + 1)) (hX : 2 ≤ X) :
    (smallDeficientSet B Y Q).card + 1 ≤ H_X (M_B B) X := by
  have h_card : (smallDeficientSet B Y Q).card ≤ M_B B :=
    D_Y_card_le_via_M_B hQ h_log h_M_B
  have h_M_B_succ : M_B B + 1 ≤ H_X (M_B B) X := H_X_ge_M_B_succ (M_B B) X hX
  omega

theorem B_j_le_k_pow_two_HX
    {k Q : ℕ} (a : ℕ → ℕ) (e : ℕ → ℕ) (D_Y_image U_X_image : Finset ℕ) (HX : ℕ)
    (hk : 1 ≤ k)
    (h_e_le : ∀ p ∈ P_plus k a, p ^ e p ≤ k)
    (h_struct : ∀ p, p.Prime → 1 ≤ p → p ≤ k → a p ≠ 0 →
      p = Q ∨ p ∈ D_Y_image ∨ p ∈ U_X_image)
    (h_DY : D_Y_image.card + 1 ≤ HX) (h_UX : U_X_image.card ≤ HX) :
    ∏ p ∈ P_plus k a, p ^ e p ≤ k ^ (2 * HX) := by
  calc ∏ p ∈ P_plus k a, p ^ e p
      ≤ k ^ (P_plus k a).card := B_j_le_k_pow_P_plus_card a e h_e_le
    _ ≤ k ^ (2 * HX) := by
        apply Nat.pow_le_pow_right hk
        exact P_plus_card_le_2_HX a D_Y_image U_X_image HX h_struct h_DY h_UX

theorem Z_gt_B_j_from_log_bounds {Z B_j : ℕ} (hZ_pos : 0 < Z) (hB_pos : 0 < B_j)
    (h_gt : B_j < Z) : B_j < Z := h_gt

theorem n_minus_i_has_prime_ge_B_from_Z_gt_B_j
    {n k i B_j : ℕ} (B : ℕ) (a : ℕ → ℕ)
    (hkn : k ≤ n) (hi : i < k) (hkB : B ≤ k)
    (h_Z_dvd_N : Z_modulus k a ∣ Nk_formula k)
    (h_alpha_mod_Z : ∃ α_k : ℕ, α_k % Z_modulus k a = k % Z_modulus k a ∧
      n % Nk_formula k = α_k % Nk_formula k ∧ k < n)
    (h_Bj_dvd : B_j ∣ n - k + (k - i))
    (h_Bj_lt_Z : B_j < Z_modulus k a)
    (hB_j_pos : 0 < B_j)
    (h_no_small_prime : ∀ p : ℕ, p.Prime → p ≤ k →
      ¬ p ∣ (n - k + (k - i)) / B_j) :
    ∃ p, p.Prime ∧ B ≤ p ∧ p ∣ n - i := by
  obtain ⟨α_k, h_alpha_eq, h_n_eq, h_n_gt⟩ := h_alpha_mod_Z
  have h_n_ge : k + Z_modulus k a ≤ n :=
    n_ge_k_plus_Z_of_progression h_Z_dvd_N h_alpha_eq h_n_eq h_n_gt
  have hj_pos : 1 ≤ k - i := by omega
  have h_lt : B_j < n - k + (k - i) := by
    have : Z_modulus k a ≤ n - k := by omega
    have : 1 + B_j ≤ n - k + (k - i) := by omega
    omega
  have h_Lj_gt : 1 < (n - k + (k - i)) / B_j := L_j_gt_one h_Bj_dvd h_lt hB_j_pos
  exact n_sub_i_has_prime_ge_B hi hkn h_Bj_dvd h_Lj_gt h_no_small_prime hB_j_pos hkB

noncomputable def hallScaffoldImage {m k : ℕ} (cov : CoverData m k) : Finset ℕ :=
  ((Finset.Icc 1 k).filter Nat.Prime).filter (fun p => k / 2 < p ∧ cov.a p ≠ 0)

theorem cover_lemma_struct_split_to_P_plus
    {m k : ℕ} (cov : CoverData m k) :
    ∀ p, p.Prime → 1 ≤ p → p ≤ k → cov.a p ≠ 0 →
      p = cov.q ∨ p ∈ (∅ : Finset ℕ) ∨ p ∈ hallScaffoldImage cov := by
  intro p hp_prime _ hpk hap
  rcases cov.scaffold p hp_prime hap with hq | ⟨hk2, hpk', _⟩
  · exact Or.inl hq
  · right; right
    simp only [hallScaffoldImage, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨⟨hp_prime.one_lt.le, hpk⟩, hp_prime⟩, hk2, hap⟩

theorem P_plus_card_le_two_HX_from_cov
    {m k : ℕ} (cov : CoverData m k) (HX : ℕ)
    (h_scaffold_card_le : (hallScaffoldImage cov).card ≤ HX)
    (h_HX_one : 1 ≤ HX) :
    (P_plus k cov.a).card ≤ 2 * HX := by
  apply P_plus_card_le_2_HX cov.a (∅ : Finset ℕ) (hallScaffoldImage cov) HX
    (cover_lemma_struct_split_to_P_plus cov)
  · simp; omega
  · exact h_scaffold_card_le

theorem hallScaffoldImage_subset_primes {m k : ℕ}
    (cov : CoverData m k) :
    hallScaffoldImage cov ⊆ (Finset.Icc 1 k).filter Nat.Prime := by
  intro p hp
  simp only [hallScaffoldImage, Finset.mem_filter, Finset.mem_Icc] at hp
  simp only [Finset.mem_filter, Finset.mem_Icc]
  exact ⟨hp.1.1, hp.1.2⟩

theorem hallScaffoldImage_card_le_primes_Ioc {m k : ℕ}
    (cov : CoverData m k) :
    (hallScaffoldImage cov).card ≤ ((Finset.Ioc (k / 2) k).filter Nat.Prime).card := by
  classical
  apply Finset.card_le_card
  intro p hp
  simp only [hallScaffoldImage, Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc] at hp
  simp only [Finset.mem_filter, Finset.mem_Ioc]
  exact ⟨⟨hp.2.1, hp.1.1.2⟩, hp.1.2⟩


theorem lemma2_when_zSet_eq_zQ
    {B X Y Q : ℕ} {b : ℕ → ℕ}
    (h_b_gt_Y : ∀ d ∈ smallDeficientSet B Y Q, Y < b d)
    (t : ℕ) (ht_in_U : t ∈ residualSet B X Y Q b) (ht_le_Y : t ≤ Y)
    (h_zSet_eq : zSet t Q ((smallDeficientSet B Y Q).image b) = zQ t Q) :
    False := by
  unfold residualSet at ht_in_U
  rw [Finset.mem_filter, Finset.mem_Icc] at ht_in_U
  obtain ⟨⟨ht_ge, _⟩, h_zset_lt, h_t_mod_Q, h_t_mod_b⟩ := ht_in_U
  have h_zQ_lt : zQ t Q < B := h_zSet_eq ▸ h_zset_lt
  have h_t_in_D : t ∈ smallDeficientSet B Y Q := by
    unfold smallDeficientSet
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨ht_ge, ht_le_Y⟩, h_t_mod_Q, h_zQ_lt⟩
  have h_t_lt_bt : t < b t := by
    have : Y < b t := h_b_gt_Y t h_t_in_D
    omega
  exact h_t_mod_b t h_t_in_D (mod_self_eq_self_of_lt h_t_lt_bt)

theorem zSet_mul_support_eq {B Y q t : ℕ} {b : ℕ → ℕ}
    (hq : q.Prime)
    (hb_prime : ∀ d ∈ smallDeficientSet B Y q, (b d).Prime)
    (hb_inj : Set.InjOn b (smallDeficientSet B Y q))
    (hb_ne_q : ∀ d ∈ smallDeficientSet B Y q, b d ≠ q) :
    zSet t q ((smallDeficientSet B Y q).image b) *
      (q ^ padicValNat q t *
        ∏ d ∈ smallDeficientSet B Y q, b d ^ padicValNat (b d) t) = t := by
  unfold zSet
  set D := smallDeficientSet B Y q
  set qvq := q ^ padicValNat q t with hqvq_def
  set prodB := ∏ d ∈ D, b d ^ padicValNat (b d) t with hprod_def
  have h_image_prod : ∏ r ∈ D.image b, r ^ padicValNat r t = prodB := by
    rw [Finset.prod_image hb_inj]
  rw [h_image_prod]
  have h_q_dvd : qvq ∣ t := pow_padicValNat_dvd
  have h_b_dvd : ∀ d ∈ D, b d ^ padicValNat (b d) t ∣ t :=
    fun _ _ => pow_padicValNat_dvd
  have h_pairwise_b : (D : Set ℕ).Pairwise
      (Function.onFun IsRelPrime (fun d => b d ^ padicValNat (b d) t)) := by
    intro x hx y hy hxy
    have hxprime := hb_prime x hx
    have hyprime := hb_prime y hy
    have hxy_ne : b x ≠ b y := fun h => hxy (hb_inj hx hy h)
    have hc : Nat.Coprime (b x) (b y) := (Nat.coprime_primes hxprime hyprime).mpr hxy_ne
    exact Nat.coprime_iff_isRelPrime.mp (hc.pow _ _)
  have h_prodB_dvd : prodB ∣ t :=
    Finset.prod_dvd_of_isRelPrime h_pairwise_b h_b_dvd
  have h_q_coprime_prodB : Nat.Coprime qvq prodB := by
    rw [hprod_def]
    apply Nat.Coprime.prod_right
    intro d hd
    have h_q_ne_bd : q ≠ b d := (hb_ne_q d hd).symm
    have hc : Nat.Coprime q (b d) := (Nat.coprime_primes hq (hb_prime d hd)).mpr h_q_ne_bd
    exact hc.pow _ _
  have h_relprime : IsRelPrime qvq prodB := Nat.coprime_iff_isRelPrime.mp h_q_coprime_prodB
  have h_M_dvd : qvq * prodB ∣ t := h_relprime.mul_dvd h_q_dvd h_prodB_dvd
  exact Nat.div_mul_cancel h_M_dvd

theorem padicValNat_le_log_two {p t X : ℕ} (hp : 2 ≤ p) (ht_le : t ≤ 2 * X) :
    padicValNat p t ≤ Nat.log 2 (2 * X) := by
  have h1 : padicValNat p t ≤ Nat.log p t := padicValNat_le_nat_log t
  have h2 : Nat.log p t ≤ Nat.log 2 t := Nat.log_anti_left (by norm_num) hp
  have h3 : Nat.log 2 t ≤ Nat.log 2 (2 * X) := Nat.log_mono_right ht_le
  omega

noncomputable def residualCode (B Y q : ℕ) (b : ℕ → ℕ) (t : ℕ) :
    ℕ × ℕ × ({d // d ∈ smallDeficientSet B Y q} → ℕ) :=
  ( zSet t q ((smallDeficientSet B Y q).image b),
    padicValNat q t,
    fun d => padicValNat (b d.val) t )

theorem residualCode_injective {B X Y q : ℕ} {b : ℕ → ℕ}
    (hq : q.Prime)
    (hb_prime : ∀ d ∈ smallDeficientSet B Y q, (b d).Prime)
    (hb_inj : Set.InjOn b (smallDeficientSet B Y q))
    (hb_ne_q : ∀ d ∈ smallDeficientSet B Y q, b d ≠ q) :
    Set.InjOn (residualCode B Y q b) (residualSet B X Y q b) := by
  intro t1 _ t2 _ hcode
  have h1 := zSet_mul_support_eq (B := B) (Y := Y) (t := t1) hq hb_prime hb_inj hb_ne_q
  have h2 := zSet_mul_support_eq (B := B) (Y := Y) (t := t2) hq hb_prime hb_inj hb_ne_q
  simp only [residualCode, Prod.mk.injEq] at hcode
  obtain ⟨h_zSet, h_vq, h_vbd_fun⟩ := hcode
  have h_prod_eq : ∏ d ∈ smallDeficientSet B Y q, b d ^ padicValNat (b d) t1 =
      ∏ d ∈ smallDeficientSet B Y q, b d ^ padicValNat (b d) t2 := by
    apply Finset.prod_congr rfl
    intro d hd
    have h := congrFun h_vbd_fun ⟨d, hd⟩
    simp only at h
    rw [h]
  rw [← h1, ← h2, h_zSet, h_vq, h_prod_eq]

theorem residualSet_card_le_code {B X Y q : ℕ} {b : ℕ → ℕ}
    (hq : q.Prime)
    (hb_prime : ∀ d ∈ smallDeficientSet B Y q, (b d).Prime)
    (hb_inj : Set.InjOn b (smallDeficientSet B Y q))
    (hb_ne_q : ∀ d ∈ smallDeficientSet B Y q, b d ≠ q) :
    let L := Nat.log 2 (2 * X) + 1
    (residualSet B X Y q b).card ≤
      B * L * L ^ (smallDeficientSet B Y q).card := by
  classical
  set D := smallDeficientSet B Y q with hD_def
  set L := Nat.log 2 (2 * X) + 1 with hL_def
  let CF : Finset (ℕ × ℕ × ({d // d ∈ D} → ℕ)) :=
    (Finset.range B) ×ˢ (Finset.range L) ×ˢ (Fintype.piFinset (fun _ => Finset.range L))
  have h_inj : Set.InjOn (residualCode B Y q b) (residualSet B X Y q b) :=
    residualCode_injective hq hb_prime hb_inj hb_ne_q
  have h_card : (residualSet B X Y q b).card ≤ CF.card := by
    apply Finset.card_le_card_of_injOn (residualCode B Y q b) ?_ h_inj
    intro t ht
    have ht' : t ∈ residualSet B X Y q b := ht
    unfold residualSet at ht'
    rw [Finset.mem_filter, Finset.mem_Icc] at ht'
    obtain ⟨⟨_, ht_le⟩, h_zset_lt, _, _⟩ := ht'
    simp only [CF, Finset.mem_coe, Finset.mem_product, Finset.mem_range,
      Fintype.mem_piFinset, residualCode]
    refine ⟨h_zset_lt, ?_, ?_⟩
    · have := padicValNat_le_log_two hq.two_le ht_le; omega
    · intro d
      have hbd_prime := hb_prime d.val d.property
      have := padicValNat_le_log_two hbd_prime.two_le ht_le; omega
  have h_CF_card : CF.card = B * L * L ^ D.card := by
    change (Finset.range B ×ˢ Finset.range L ×ˢ
      Fintype.piFinset fun _ : {d // d ∈ D} => Finset.range L).card = B * L * L ^ D.card
    rw [Finset.card_product, Finset.card_product, Finset.card_range, Finset.card_range,
        Fintype.card_piFinset]
    simp
    ring
  omega

theorem residualSet_card_le_HX {B X Y q : ℕ} {b : ℕ → ℕ}
    (hq : q.Prime)
    (hb_prime : ∀ d ∈ smallDeficientSet B Y q, (b d).Prime)
    (hb_inj : Set.InjOn b (smallDeficientSet B Y q))
    (hb_ne_q : ∀ d ∈ smallDeficientSet B Y q, b d ≠ q)
    (h_numeric :
      B * (Nat.log 2 (2 * X) + 1) *
        (Nat.log 2 (2 * X) + 1) ^ (smallDeficientSet B Y q).card
        ≤ H_X (M_B B) X) :
    (residualSet B X Y q b).card ≤ H_X (M_B B) X :=
  (residualSet_card_le_code hq hb_prime hb_inj hb_ne_q).trans h_numeric

theorem prod_image_buffer_padic_eq_one
    {B Y Q t : ℕ} {b : ℕ → ℕ}
    (hb_inj : Set.InjOn b (smallDeficientSet B Y Q))
    (h_t_lt_b : ∀ d ∈ smallDeficientSet B Y Q, t < b d)
    (h_b_gt_1 : ∀ d ∈ smallDeficientSet B Y Q, 1 < b d) :
    ∏ r ∈ (smallDeficientSet B Y Q).image b, r ^ padicValNat r t = 1 := by
  rw [Finset.prod_image hb_inj]
  exact buffer_prod_padicValNat_eq_one h_t_lt_b h_b_gt_1

theorem residualSet_no_small
    {B X Y q : ℕ} {b : ℕ → ℕ}
    (hb_inj : Set.InjOn b (smallDeficientSet B Y q))
    (h_b_gt_Y : ∀ d ∈ smallDeficientSet B Y q, Y < b d)
    (h_b_gt_1 : ∀ d ∈ smallDeficientSet B Y q, 1 < b d) :
    ∀ t, t ∈ residualSet B X Y q b → Y < t := by
  intro t ht
  by_contra hle
  push_neg at hle
  have h_t_lt_b : ∀ d ∈ smallDeficientSet B Y q, t < b d := by
    intro d hd
    have h := h_b_gt_Y d hd
    omega
  have h_prod_one :
      ∏ r ∈ (smallDeficientSet B Y q).image b, r ^ padicValNat r t = 1 :=
    prod_image_buffer_padic_eq_one hb_inj h_t_lt_b h_b_gt_1
  have h_z_eq : zSet t q ((smallDeficientSet B Y q).image b) = zQ t q := by
    unfold zSet zQ
    rw [h_prod_one, Nat.mul_one]
  exact lemma2_when_zSet_eq_zQ h_b_gt_Y t ht hle h_z_eq

theorem lift_non_excess_level_ge_2_of_p_dvd_k
    {p u a k : ℕ} (hp : 1 < p) (hp_dvd_k : p ∣ k) (hap_pos : 1 ≤ a) (hap_lt : a < p)
    (hu : 1 ≤ u) :
    k % p ^ u < liftAbove p u a :=
  liftAbove_above_kModPow hp hp_dvd_k hap_pos hap_lt hu

theorem alphaP_eq_one_of_lt_p_sq {k p : ℕ} (hp : 1 < p) (hk_lt : k < p * p) (hk_pos : 0 < k) :
    alphaP k p ≤ 1 := by
  unfold alphaP
  by_contra h_gt
  push_neg at h_gt
  have h_pow_le : p ^ 2 ≤ k := (Nat.le_log_iff_pow_le (by omega) hk_pos.ne').mp h_gt
  have h_sq_eq : p ^ 2 = p * p := by ring
  omega

theorem alphaP_le_one_of_scaffold {k p : ℕ} (hp : 1 < p) (hpk : k / 2 < p) (hpk_le : p ≤ k)
    (hk_ge : 4 ≤ k) :
    alphaP k p ≤ 1 := by
  apply alphaP_eq_one_of_lt_p_sq hp _ (by omega)
  have hp_ge_2 : 2 ≤ p := by omega
  have h_2p_lt : k < 2 * p := by omega
  nlinarith

def IsNonExcessCov {B k : ℕ} (cov : CoverData B k) : Prop :=
  ∀ p, p.Prime → B ≤ p → p ≤ k → cov.a p ≠ 0 → k % p < cov.a p

theorem localLift_eq_zero_of_a_eq_zero {a : ℕ → ℕ} {p u : ℕ} (hap : a p = 0) :
    liftAtLevel a p u = 0 := by
  unfold liftAtLevel
  rw [if_pos hap]

theorem localResidue_eq_k_when_a_zero {k p : ℕ} {a : ℕ → ℕ} (hap : a p = 0) :
    localResidue k a p = (k : ℤ) := by
  unfold localResidue
    localLift
  rw [localLift_eq_zero_of_a_eq_zero hap]
  simp

theorem localMod_dvd_Nk_formula {k p : ℕ} (hp_prime : p.Prime) (hp_le : p ≤ k) :
    (localMod k p : ℤ) ∣ (Nk_formula k : ℤ) := by
  rw [Nk_formula_eq_globalMk]
  unfold localMod
    globalMk
  have hp_mem : p ∈ (Finset.Icc 1 k).filter Nat.Prime :=
    Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp_prime.one_lt.le, hp_le⟩, hp_prime⟩
  exact_mod_cast Finset.dvd_prod_of_mem _ hp_mem

theorem n_mod_pow_eq_localResidue_of_a {k p : ℕ} (a : ℕ → ℕ) (R n : ℤ)
    (hp : p.Prime) (hp_le_k : p ≤ k)
    (hRloc : ∀ p ∈ primeSet k,
      R ≡ localResidue k a p [ZMOD
        (localMod k p : ℤ)])
    (h_n_mod : (Nk_formula k : ℤ) ∣ n - R)
    (u : ℕ) (hu : u ≤ alphaP k p + 1) :
    n ≡ localResidue k a p [ZMOD ((p ^ u : ℕ) : ℤ)] := by
  have hp_mem : p ∈ primeSet k :=
    mem_primeSet.mpr ⟨hp.one_lt.le, hp_le_k, hp⟩
  have hRmod := hRloc p hp_mem
  have h_pow_dvd_global : p ^ (alphaP k p + 1) ∣
      globalMk k := globalMk_factorization_at_prime k p hp hp_le_k
  have h_pow_u_dvd_global : (p ^ u : ℕ) ∣ globalMk k :=
    (Nat.pow_dvd_pow p hu).trans h_pow_dvd_global
  have h_pow_u_dvd_Nk : ((p ^ u : ℕ) : ℤ) ∣ (Nk_formula k : ℤ) := by
    rw [Nk_formula_eq_globalMk]; exact_mod_cast h_pow_u_dvd_global
  have h_n_R_pow : ((p ^ u : ℕ) : ℤ) ∣ n - R := h_pow_u_dvd_Nk.trans h_n_mod
  have h_neg_n_R : ((p ^ u : ℕ) : ℤ) ∣ R - n := by
    rw [show R - n = -(n - R) by ring]; exact dvd_neg.mpr h_n_R_pow
  have h_n_eq_R_pow : n ≡ R [ZMOD ((p ^ u : ℕ) : ℤ)] :=
    Int.modEq_iff_dvd.mpr h_neg_n_R
  have h_localMod_dvd : ((p ^ u : ℕ) : ℤ) ∣
      (localMod k p : ℤ) := by
    unfold localMod
    exact_mod_cast Nat.pow_dvd_pow p hu
  have hR_eq_localResidue_pow :
      R ≡ localResidue k a p [ZMOD ((p ^ u : ℕ) : ℤ)] :=
    hRmod.of_dvd h_localMod_dvd
  exact h_n_eq_R_pow.trans hR_eq_localResidue_pow

theorem n_mod_pow_eq_localResidue {B k p : ℕ}
    (cov : CoverData B k) (R n : ℤ)
    (hp : p.Prime) (hp_le_k : p ≤ k)
    (hRloc : ∀ p ∈ primeSet k,
      R ≡ localResidue k cov.a p [ZMOD
        (localMod k p : ℤ)])
    (h_n_mod : (Nk_formula k : ℤ) ∣ n - R)
    (u : ℕ) (hu : u ≤ alphaP k p + 1) :
    n ≡ localResidue k cov.a p [ZMOD ((p ^ u : ℕ) : ℤ)] :=
  n_mod_pow_eq_localResidue_of_a cov.a R n hp hp_le_k hRloc h_n_mod u hu

theorem n_mod_pow_eq_k_mod_pow_of_a_zero_of_a {k p u : ℕ} (a : ℕ → ℕ) (R : ℤ) (n : ℤ)
    (hp : p.Prime) (hp_le_k : p ≤ k)
    (hRloc : ∀ p ∈ primeSet k,
      R ≡ localResidue k a p [ZMOD
        (localMod k p : ℤ)])
    (h_n_mod : (Nk_formula k : ℤ) ∣ n - R)
    (hu : u ≤ alphaP k p + 1)
    (hzero : a p = 0) :
    n ≡ (k : ℤ) [ZMOD ((p ^ u : ℕ) : ℤ)] := by
  have h_n_eq_local := n_mod_pow_eq_localResidue_of_a a R n hp hp_le_k hRloc h_n_mod u hu
  rw [localResidue_eq_k_when_a_zero hzero] at h_n_eq_local
  exact h_n_eq_local

theorem n_mod_pow_eq_k_mod_pow_of_a_zero {B k p u : ℕ}
    (cov : CoverData B k) (R : ℤ) (n : ℤ)
    (hp : p.Prime) (hp_le_k : p ≤ k)
    (hRloc : ∀ p ∈ primeSet k,
      R ≡ localResidue k cov.a p [ZMOD
        (localMod k p : ℤ)])
    (h_n_mod : (Nk_formula k : ℤ) ∣ n - R)
    (hu : u ≤ alphaP k p + 1)
    (hzero : cov.a p = 0) :
    n ≡ (k : ℤ) [ZMOD ((p ^ u : ℕ) : ℤ)] :=
  n_mod_pow_eq_k_mod_pow_of_a_zero_of_a cov.a R n hp hp_le_k hRloc h_n_mod hu hzero

theorem mod_sub_lift_ge_k_mod {k p u lift : ℕ} (hpow_pos : 0 < p ^ u)
    (hlift_lt : lift < p ^ u) (h_gt : k % p ^ u < lift) :
    k % p ^ u ≤ (k + p ^ u - lift) % p ^ u := by
  set m := p ^ u
  have hk_div_mod : m * (k / m) + k % m = k := Nat.div_add_mod k m
  have h_lt_m : k % m + m - lift < m := by omega
  have h_sum : k + m - lift = (k % m + m - lift) + m * (k / m) := by omega
  rw [h_sum, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h_lt_m]
  omega

theorem liftAtLevel_nonzero_non_excess_of_p_dvd_k
    {a : ℕ → ℕ} {k p u : ℕ}
    (hp : p.Prime) (hp_dvd_k : p ∣ k)
    (ha_pos : 1 ≤ a p) (ha_lt : a p < p) (hu : 1 ≤ u) :
    k % p ^ u < liftAtLevel a p u := by
  unfold liftAtLevel
  rw [if_neg (by omega : a p ≠ 0), if_neg (by omega : u ≠ 0)]
  by_cases hu1 : u = 1
  · rw [if_pos hu1, hu1, pow_one]
    have h_k_mod_p : k % p = 0 := Nat.mod_eq_zero_of_dvd hp_dvd_k
    omega
  · rw [if_neg hu1]
    have hu2 : 2 ≤ u := by omega
    exact lift_non_excess_level_ge_2_of_p_dvd_k hp.one_lt hp_dvd_k ha_pos ha_lt hu

theorem liftAtLevel_top_gt_k_of_p_dvd_k {a : ℕ → ℕ} {k p : ℕ}
    (hp : p.Prime) (hp_dvd_k : p ∣ k) (ha_pos : 1 ≤ a p) (ha_lt : a p < p)
    (hk_pos : 0 < k) :
    k < liftAtLevel a p
        (alphaP k p + 1) := by
  have h_ne : k % p ^ (alphaP k p + 1) <
      liftAtLevel a p
        (alphaP k p + 1) :=
    liftAtLevel_nonzero_non_excess_of_p_dvd_k hp hp_dvd_k ha_pos ha_lt (by omega)
  have hk_lt_pow : k < p ^ (alphaP k p + 1) :=
    alphaP_succ_pow_gt hp.one_lt
  have hk_mod_eq : k % p ^ (alphaP k p + 1) = k :=
    Nat.mod_eq_of_lt hk_lt_pow
  omega

theorem liftAtLevel_top_gt_k_of_scaffold {a : ℕ → ℕ} {k p : ℕ}
    (hp : p.Prime) (hp_half : k / 2 < p) (hp_le_k : p ≤ k) (hk_ge : 4 ≤ k)
    (ha_pos : 1 ≤ a p) (ha_lt : a p < p) :
    k < liftAtLevel a p
        (alphaP k p + 1) := by
  have h_alpha_le : alphaP k p ≤ 1 :=
    alphaP_le_one_of_scaffold hp.one_lt hp_half hp_le_k hk_ge
  have h_alpha_pos : 0 < alphaP k p := by
    unfold alphaP
    have hp_le_k_log : p ≤ k := hp_le_k
    have : 1 ≤ Nat.log p k := by
      rw [Nat.one_le_iff_ne_zero]
      intro h_eq
      have := Nat.log_eq_zero_iff.mp h_eq
      rcases this with h | h <;> omega
    omega
  have h_alpha_eq : alphaP k p = 1 := by omega
  unfold liftAtLevel
  rw [if_neg (by omega : a p ≠ 0), if_neg (by omega : (alphaP k p + 1) ≠ 0),
      if_neg (by omega : (alphaP k p + 1) ≠ 1)]
  unfold liftAbove
  rw [h_alpha_eq]
  have hp_ge_2 : 2 ≤ p := hp.two_le
  have h_2p : k + 1 ≤ 2 * p := by omega
  have hp_pp_ge : p + k ≤ p * p := by nlinarith
  rw [show p ^ (1 + 1) = p * p from by ring]
  omega

theorem liftAtLevel_lt_pow_top_of_a {k p : ℕ} (a : ℕ → ℕ)
    (hp : p.Prime) (ha_lt : a p < p) :
    liftAtLevel a p
        (alphaP k p + 1) <
      p ^ (alphaP k p + 1) := by
  unfold liftAtLevel
  have hp_pow_pos : 0 < p ^ (alphaP k p + 1) :=
    Nat.pow_pos (a := p) hp.pos
  split_ifs with h0 h1 h2
  · exact hp_pow_pos
  · exact hp_pow_pos
  · have hp_le_pow : p ≤ p ^ (alphaP k p + 1) := by
      have : p ^ 1 ≤ p ^ (alphaP k p + 1) :=
        Nat.pow_le_pow_right hp.one_lt.le (by omega)
      simpa using this
    omega
  · unfold liftAbove
    have hp_le_pow : p ≤ p ^ (alphaP k p + 1) := by
      have : p ^ 1 ≤ p ^ (alphaP k p + 1) :=
        Nat.pow_le_pow_right hp.one_lt.le (by omega)
      simpa using this
    omega

theorem liftAtLevel_lt_pow_top {B k p : ℕ}
    (cov : CoverData B k)
    (hp : p.Prime) :
    liftAtLevel cov.a p
        (alphaP k p + 1) <
      p ^ (alphaP k p + 1) :=
  liftAtLevel_lt_pow_top_of_a cov.a hp (cov.a_lt_p p hp)

theorem n_toNat_mod_pow_top_of_lift_lt_pow_of_a {k p : ℕ} (a : ℕ → ℕ) (R : ℤ) (n : ℤ)
    (hp : p.Prime) (hp_le_k : p ≤ k) (ha_lt : a p < p)
    (hRloc : ∀ p ∈ primeSet k,
      R ≡ localResidue k a p [ZMOD
        (localMod k p : ℤ)])
    (h_n_mod : (Nk_formula k : ℤ) ∣ n - R)
    (h_n_nonneg : 0 ≤ n) :
    n.toNat % p ^ (alphaP k p + 1) =
      (k + p ^ (alphaP k p + 1) -
        liftAtLevel a p
          (alphaP k p + 1)) %
      p ^ (alphaP k p + 1) := by
  set α1 := alphaP k p + 1
  set lift := liftAtLevel a p α1
  have h_lift_lt_pow : lift < p ^ α1 := liftAtLevel_lt_pow_top_of_a a hp ha_lt
  have h_n_eq_int : (n.toNat : ℤ) = n := Int.toNat_of_nonneg h_n_nonneg
  have h_n_mod_R : n ≡ localResidue k a p
      [ZMOD ((p ^ α1 : ℕ) : ℤ)] :=
    n_mod_pow_eq_localResidue_of_a a R n hp hp_le_k hRloc h_n_mod α1 (le_refl _)
  have h_localRes_eq : localResidue k a p =
      (k : ℤ) - (lift : ℤ) := rfl
  rw [h_localRes_eq] at h_n_mod_R
  have h_n_mod_int : n % ((p ^ α1 : ℕ) : ℤ) =
      ((k : ℤ) - (lift : ℤ)) % ((p ^ α1 : ℕ) : ℤ) := h_n_mod_R
  have h_diff_eq_int : ((k + p ^ α1 - lift : ℕ) : ℤ) =
      (k : ℤ) - (lift : ℤ) + ((p ^ α1 : ℕ) : ℤ) := by
    have h_le : lift ≤ k + p ^ α1 := by have := h_lift_lt_pow; omega
    push_cast [Nat.cast_sub h_le]; ring
  have h_diff_mod_int : ((k + p ^ α1 - lift : ℕ) : ℤ) % ((p ^ α1 : ℕ) : ℤ) =
      ((k : ℤ) - (lift : ℤ)) % ((p ^ α1 : ℕ) : ℤ) := by
    rw [h_diff_eq_int]
    exact Int.add_emod_right _ _
  have h_n_mod_int' : ((n.toNat : ℤ)) % ((p ^ α1 : ℕ) : ℤ) =
      ((k + p ^ α1 - lift : ℕ) : ℤ) % ((p ^ α1 : ℕ) : ℤ) := by
    rw [h_n_eq_int, h_n_mod_int, ← h_diff_mod_int]
  have h_target_int : ((n.toNat % p ^ α1 : ℕ) : ℤ) = (((k + p ^ α1 - lift) % p ^ α1 : ℕ) : ℤ) := by
    have h1 : ((n.toNat % p ^ α1 : ℕ) : ℤ) = (n.toNat : ℤ) % ((p ^ α1 : ℕ) : ℤ) := by push_cast; rfl
    have h2 : (((k + p ^ α1 - lift) % p ^ α1 : ℕ) : ℤ) =
        ((k + p ^ α1 - lift : ℕ) : ℤ) % ((p ^ α1 : ℕ) : ℤ) := by push_cast; rfl
    rw [h1, h2, h_n_mod_int']
  exact_mod_cast h_target_int

theorem n_toNat_mod_pow_top_of_lift_lt_pow {B k p : ℕ}
    (cov : CoverData B k) (R : ℤ) (n : ℤ)
    (hp : p.Prime) (hp_le_k : p ≤ k)
    (hRloc : ∀ p ∈ primeSet k,
      R ≡ localResidue k cov.a p [ZMOD
        (localMod k p : ℤ)])
    (h_n_mod : (Nk_formula k : ℤ) ∣ n - R)
    (h_n_nonneg : 0 ≤ n) :
    n.toNat % p ^ (alphaP k p + 1) =
      (k + p ^ (alphaP k p + 1) -
        liftAtLevel cov.a p
          (alphaP k p + 1)) %
      p ^ (alphaP k p + 1) :=
  n_toNat_mod_pow_top_of_lift_lt_pow_of_a cov.a R n hp hp_le_k (cov.a_lt_p p hp) hRloc h_n_mod h_n_nonneg

theorem h_top_of_liftTop_gt_k_of_a {k p : ℕ} (a : ℕ → ℕ) (R : ℤ) (n : ℤ)
    (hp : p.Prime) (hp_le_k : p ≤ k) (ha_lt : a p < p)
    (hRloc : ∀ p ∈ primeSet k,
      R ≡ localResidue k a p [ZMOD
        (localMod k p : ℤ)])
    (h_n_mod : (Nk_formula k : ℤ) ∣ n - R)
    (h_n_nonneg : 0 ≤ n) (h_n_ge_k : k ≤ n.toNat)
    (h_lift_gt_k : k < liftAtLevel a p
      (alphaP k p + 1)) :
    ∀ i ∈ Finset.range k,
      ¬ p ^ (alphaP k p + 1) ∣ n.toNat - i := by
  intro i hi h_dvd
  rw [Finset.mem_range] at hi
  set α1 := alphaP k p + 1
  set lift := liftAtLevel a p α1
  have hp_pow_pos : 0 < p ^ α1 := Nat.pow_pos (a := p) hp.pos
  have hk_lt_pow : k < p ^ α1 := alphaP_succ_pow_gt hp.one_lt
  have h_lift_lt_pow : lift < p ^ α1 := liftAtLevel_lt_pow_top_of_a a hp ha_lt
  have h_n_natMod := n_toNat_mod_pow_top_of_lift_lt_pow_of_a a R n hp hp_le_k ha_lt hRloc
    h_n_mod h_n_nonneg
  have h_diff_lt : k + p ^ α1 - lift < p ^ α1 := by omega
  have h_diff_gt_k : k < k + p ^ α1 - lift := by omega
  have h_n_mod_val : n.toNat % p ^ α1 = k + p ^ α1 - lift := by
    rw [h_n_natMod]; exact Nat.mod_eq_of_lt h_diff_lt
  have hi_le_n : i ≤ n.toNat := by omega
  have h_modeq : i ≡ n.toNat [MOD p ^ α1] := (Nat.modEq_iff_dvd' hi_le_n).mpr h_dvd
  have h_i_mod : i % p ^ α1 = n.toNat % p ^ α1 := h_modeq
  have hi_lt_pow : i < p ^ α1 := by omega
  rw [Nat.mod_eq_of_lt hi_lt_pow, h_n_mod_val] at h_i_mod
  omega

theorem h_top_of_liftTop_gt_k {B k p : ℕ}
    (cov : CoverData B k) (R : ℤ) (n : ℤ)
    (hp : p.Prime) (hp_le_k : p ≤ k)
    (hRloc : ∀ p ∈ primeSet k,
      R ≡ localResidue k cov.a p [ZMOD
        (localMod k p : ℤ)])
    (h_n_mod : (Nk_formula k : ℤ) ∣ n - R)
    (h_n_nonneg : 0 ≤ n) (h_n_ge_k : k ≤ n.toNat)
    (h_lift_gt_k : k < liftAtLevel cov.a p
      (alphaP k p + 1)) :
    ∀ i ∈ Finset.range k,
      ¬ p ^ (alphaP k p + 1) ∣ n.toNat - i :=
  h_top_of_liftTop_gt_k_of_a cov.a R n hp hp_le_k (cov.a_lt_p p hp) hRloc h_n_mod h_n_nonneg
    h_n_ge_k h_lift_gt_k

theorem h_non_excess_of_a_zero_of_a {k p u : ℕ} (a : ℕ → ℕ) (R : ℤ) (n : ℤ)
    (hp : p.Prime) (hp_le_k : p ≤ k)
    (hRloc : ∀ p ∈ primeSet k,
      R ≡ localResidue k a p [ZMOD
        (localMod k p : ℤ)])
    (h_n_mod : (Nk_formula k : ℤ) ∣ n - R) (h_n_nonneg : 0 ≤ n)
    (hu : u ≤ alphaP k p + 1) (hzero : a p = 0) :
    k % p ^ u ≤ n.toNat % p ^ u := by
  have h_n_eq_k := n_mod_pow_eq_k_mod_pow_of_a_zero_of_a a R n hp hp_le_k hRloc h_n_mod hu hzero
  have h_n_eq_int : (n.toNat : ℤ) = n := Int.toNat_of_nonneg h_n_nonneg
  have h_int : ((n.toNat % p ^ u : ℕ) : ℤ) = ((k % p ^ u : ℕ) : ℤ) := by
    have h_n_mod_int : (n.toNat : ℤ) % ((p ^ u : ℕ) : ℤ) = (k : ℤ) % ((p ^ u : ℕ) : ℤ) := by
      rw [h_n_eq_int]; exact h_n_eq_k
    push_cast
    push_cast at h_n_mod_int
    exact h_n_mod_int
  have h_eq : n.toNat % p ^ u = k % p ^ u := by exact_mod_cast h_int
  omega

theorem h_non_excess_of_a_zero {B k p u : ℕ}
    (cov : CoverData B k) (R : ℤ) (n : ℤ)
    (hp : p.Prime) (hp_le_k : p ≤ k)
    (hRloc : ∀ p ∈ primeSet k,
      R ≡ localResidue k cov.a p [ZMOD
        (localMod k p : ℤ)])
    (h_n_mod : (Nk_formula k : ℤ) ∣ n - R) (h_n_nonneg : 0 ≤ n)
    (hu : u ≤ alphaP k p + 1) (hzero : cov.a p = 0) :
    k % p ^ u ≤ n.toNat % p ^ u :=
  h_non_excess_of_a_zero_of_a cov.a R n hp hp_le_k hRloc h_n_mod h_n_nonneg hu hzero

theorem liftAtLevel_lt_pow' {a : ℕ → ℕ} {p u : ℕ}
    (hp : 1 < p) (ha_lt : a p < p) :
    liftAtLevel a p u < p ^ u := by
  unfold liftAtLevel
  have hp_pow_pos : 0 < p ^ u := Nat.pow_pos (a := p) (by omega)
  split_ifs with h0 h1 h2
  · exact hp_pow_pos
  · exact hp_pow_pos
  · subst h2
    rw [pow_one]; omega
  · unfold liftAbove
    have hu_ge_2 : 2 ≤ u := by omega
    have hp_lt_pow : p ≤ p ^ u := by
      have : p ^ 1 ≤ p ^ u := Nat.pow_le_pow_right hp.le (by omega)
      simpa using this
    omega

theorem liftAtLevel_top_mod_pow_eq {a : ℕ → ℕ} {k p u : ℕ}
    (hp : 1 < p) (ha_lt : a p < p) (hu_lo : 1 ≤ u)
    (hu_hi : u ≤ alphaP k p + 1) :
    liftAtLevel a p
        (alphaP k p + 1) % p ^ u =
      liftAtLevel a p u := by
  by_cases hap : a p = 0
  · rw [localLift_eq_zero_of_a_eq_zero hap, localLift_eq_zero_of_a_eq_zero hap]; simp
  · unfold liftAtLevel
    rw [if_neg hap, if_neg hap]
    set α1 := alphaP k p + 1
    rw [if_neg (by omega : α1 ≠ 0), if_neg (by omega : u ≠ 0)]
    by_cases hα1_one : α1 = 1
    · rw [if_pos hα1_one]
      have hu_one : u = 1 := by omega
      rw [if_pos hu_one, hu_one, pow_one, Nat.mod_eq_of_lt ha_lt]
    · rw [if_neg hα1_one]
      by_cases hu_one : u = 1
      · rw [if_pos hu_one, hu_one, pow_one]
        exact liftAbove_mod_p p α1 (a p) hp ha_lt (by omega)
      · rw [if_neg hu_one]
        unfold liftAbove
        have h_pow_u_dvd : p ^ u ∣ p ^ α1 := Nat.pow_dvd_pow p hu_hi
        have hp_le_u : p ≤ p ^ u := by
          have : p ^ 1 ≤ p ^ u := Nat.pow_le_pow_right hp.le hu_lo
          simpa using this
        have hu_pow_le : p ^ u ≤ p ^ α1 := Nat.pow_le_pow_right hp.le hu_hi
        have h_sum : p ^ α1 - p + a p = (p ^ α1 - p ^ u) + (p ^ u - p + a p) := by omega
        have h_dvd_first : p ^ u ∣ (p ^ α1 - p ^ u) :=
          Nat.dvd_sub h_pow_u_dvd dvd_rfl
        have h_inner_lt : p ^ u - p + a p < p ^ u := by omega
        rw [h_sum, Nat.add_mod, Nat.mod_eq_zero_of_dvd h_dvd_first, Nat.zero_add,
            Nat.mod_mod, Nat.mod_eq_of_lt h_inner_lt]

theorem n_mod_pow_eq_k_sub_liftU_of_a {k p u : ℕ} (a : ℕ → ℕ) (R : ℤ) (n : ℤ)
    (hp : p.Prime) (hp_le_k : p ≤ k) (ha_lt : a p < p)
    (hRloc : ∀ p ∈ primeSet k,
      R ≡ localResidue k a p [ZMOD
        (localMod k p : ℤ)])
    (h_n_mod : (Nk_formula k : ℤ) ∣ n - R)
    (hu_lo : 1 ≤ u) (hu_hi : u ≤ alphaP k p + 1) :
    n ≡ (k : ℤ) - (liftAtLevel a p u : ℤ)
        [ZMOD ((p ^ u : ℕ) : ℤ)] := by
  have h_n_top := n_mod_pow_eq_localResidue_of_a a R n hp hp_le_k hRloc h_n_mod u hu_hi
  unfold localResidue at h_n_top
  have h_lift_eq := liftAtLevel_top_mod_pow_eq (a := a) (k := k) (p := p) (u := u)
    hp.one_lt ha_lt hu_lo hu_hi
  have h_localLift_eq : localLift k a p =
      liftAtLevel a p
        (alphaP k p + 1) := rfl
  rw [h_localLift_eq] at h_n_top
  have h_liftU_lt : liftAtLevel a p u < p ^ u :=
    liftAtLevel_lt_pow' hp.one_lt ha_lt
  have h_liftU_mod : (liftAtLevel a p u : ℕ) % p ^ u =
      liftAtLevel a p u := Nat.mod_eq_of_lt h_liftU_lt
  have h_int_eq : ((liftAtLevel a p
        (alphaP k p + 1) : ℕ) : ℤ) %
      ((p ^ u : ℕ) : ℤ) =
      ((liftAtLevel a p u : ℕ) : ℤ) := by
    push_cast; exact_mod_cast h_lift_eq
  unfold Int.ModEq at h_n_top ⊢
  rw [h_n_top]
  conv_lhs => rw [Int.sub_emod]
  conv_rhs => rw [Int.sub_emod]
  rw [h_int_eq]
  have h_liftU_int_mod :
      ((liftAtLevel a p u : ℕ) : ℤ) %
        ((p ^ u : ℕ) : ℤ) =
      ((liftAtLevel a p u : ℕ) : ℤ) := by
    push_cast; exact_mod_cast h_liftU_mod
  rw [h_liftU_int_mod]

theorem n_mod_pow_eq_k_sub_liftU {B k p u : ℕ}
    (cov : CoverData B k) (R : ℤ) (n : ℤ)
    (hp : p.Prime) (hp_le_k : p ≤ k)
    (hRloc : ∀ p ∈ primeSet k,
      R ≡ localResidue k cov.a p [ZMOD
        (localMod k p : ℤ)])
    (h_n_mod : (Nk_formula k : ℤ) ∣ n - R)
    (hu_lo : 1 ≤ u) (hu_hi : u ≤ alphaP k p + 1) :
    n ≡ (k : ℤ) - (liftAtLevel cov.a p u : ℤ)
        [ZMOD ((p ^ u : ℕ) : ℤ)] :=
  n_mod_pow_eq_k_sub_liftU_of_a cov.a R n hp hp_le_k (cov.a_lt_p p hp) hRloc h_n_mod hu_lo hu_hi

theorem h_non_excess_for_p_dvd_k_at_u_of_a {k p u : ℕ} (a : ℕ → ℕ) (R : ℤ) (n : ℤ)
    (hp : p.Prime) (hp_le_k : p ≤ k) (hp_dvd_k : p ∣ k) (ha_lt : a p < p)
    (hRloc : ∀ p ∈ primeSet k,
      R ≡ localResidue k a p [ZMOD
        (localMod k p : ℤ)])
    (h_n_mod : (Nk_formula k : ℤ) ∣ n - R) (h_n_nonneg : 0 ≤ n)
    (hnz : a p ≠ 0)
    (hu_lo : 1 ≤ u) (hu_hi : u ≤ alphaP k p + 1) :
    k % p ^ u ≤ n.toNat % p ^ u := by
  have h_a_pos : 1 ≤ a p := Nat.one_le_iff_ne_zero.mpr hnz
  have h_lift_lt : liftAtLevel a p u < p ^ u :=
    liftAtLevel_lt_pow' hp.one_lt ha_lt
  have h_lift_gt : k % p ^ u < liftAtLevel a p u :=
    liftAtLevel_nonzero_non_excess_of_p_dvd_k hp hp_dvd_k h_a_pos ha_lt hu_lo
  have h_pow_pos : 0 < p ^ u := Nat.pow_pos (a := p) hp.pos
  have h_n_eq_int : (n.toNat : ℤ) = n := Int.toNat_of_nonneg h_n_nonneg
  have h_n_modeq : n ≡ (k : ℤ) - (liftAtLevel a p u : ℤ)
      [ZMOD ((p ^ u : ℕ) : ℤ)] :=
    n_mod_pow_eq_k_sub_liftU_of_a a R n hp hp_le_k ha_lt hRloc h_n_mod hu_lo hu_hi
  have h_lift_le_sum : liftAtLevel a p u ≤ k + p ^ u := by
    have := h_lift_lt; omega
  have h_n_natMod : n.toNat % p ^ u =
      (k + p ^ u - liftAtLevel a p u) % p ^ u := by
    have h_diff_int :
        ((k + p ^ u - liftAtLevel a p u : ℕ) : ℤ) =
        (k : ℤ) - (liftAtLevel a p u : ℤ) +
          ((p ^ u : ℕ) : ℤ) := by
      rw [Nat.cast_sub h_lift_le_sum]
      push_cast; ring
    have h_lhs : ((n.toNat % p ^ u : ℕ) : ℤ) = n % ((p ^ u : ℕ) : ℤ) := by
      push_cast; rw [← h_n_eq_int]; rfl
    have h_rhs :
        (((k + p ^ u - liftAtLevel a p u) % p ^ u : ℕ) : ℤ) =
        ((k + p ^ u - liftAtLevel a p u : ℕ) : ℤ) %
          ((p ^ u : ℕ) : ℤ) := by push_cast; rfl
    have h_target_int : ((n.toNat % p ^ u : ℕ) : ℤ) =
        (((k + p ^ u - liftAtLevel a p u) % p ^ u : ℕ) : ℤ) := by
      rw [h_lhs, h_rhs, h_diff_int, Int.add_emod_right]; exact h_n_modeq
    exact_mod_cast h_target_int
  rw [h_n_natMod]
  exact mod_sub_lift_ge_k_mod h_pow_pos h_lift_lt h_lift_gt

theorem h_non_excess_for_p_dvd_k_at_u {B k p u : ℕ}
    (cov : CoverData B k) (R : ℤ) (n : ℤ)
    (hp : p.Prime) (hp_le_k : p ≤ k) (hp_dvd_k : p ∣ k)
    (hRloc : ∀ p ∈ primeSet k,
      R ≡ localResidue k cov.a p [ZMOD
        (localMod k p : ℤ)])
    (h_n_mod : (Nk_formula k : ℤ) ∣ n - R) (h_n_nonneg : 0 ≤ n)
    (hnz : cov.a p ≠ 0)
    (hu_lo : 1 ≤ u) (hu_hi : u ≤ alphaP k p + 1) :
    k % p ^ u ≤ n.toNat % p ^ u :=
  h_non_excess_for_p_dvd_k_at_u_of_a cov.a R n hp hp_le_k hp_dvd_k (cov.a_lt_p p hp) hRloc
    h_n_mod h_n_nonneg hnz hu_lo hu_hi

theorem n_mod_p_eq_k_sub_a_of_a {k p : ℕ} (a : ℕ → ℕ) (R : ℤ) (n : ℤ)
    (hp : p.Prime) (hp_le_k : p ≤ k) (ha_lt : a p < p)
    (hRloc : ∀ p ∈ primeSet k,
      R ≡ localResidue k a p [ZMOD
        (localMod k p : ℤ)])
    (h_n_mod : (Nk_formula k : ℤ) ∣ n - R) :
    n ≡ (k : ℤ) - (a p : ℤ) [ZMOD (p : ℤ)] := by
  have hR_eq := R_mod_p_eq_of_a a p hp hp_le_k ha_lt R hRloc
  have hp_dvd_Nk : (p : ℤ) ∣ (Nk_formula k : ℤ) := by
    rw [Nk_formula_eq_globalMk]
    have h_pow_dvd : p ^ (alphaP k p + 1) ∣
        globalMk k :=
      globalMk_factorization_at_prime k p hp hp_le_k
    have h_p_dvd_pow : p ∣ p ^ (alphaP k p + 1) :=
      dvd_pow_self p (by omega)
    exact_mod_cast h_p_dvd_pow.trans h_pow_dvd
  have h_n_eq_R : n ≡ R [ZMOD (p : ℤ)] := by
    have h_dvd : (p : ℤ) ∣ n - R := hp_dvd_Nk.trans h_n_mod
    have h_neg : (p : ℤ) ∣ R - n := by
      rw [show R - n = -(n - R) by ring]; exact dvd_neg.mpr h_dvd
    exact Int.modEq_iff_dvd.mpr h_neg
  exact h_n_eq_R.trans hR_eq

theorem n_mod_p_eq_k_sub_a {B k p : ℕ}
    (cov : CoverData B k) (R : ℤ) (n : ℤ)
    (hp : p.Prime) (hp_le_k : p ≤ k)
    (hRloc : ∀ p ∈ primeSet k,
      R ≡ localResidue k cov.a p [ZMOD
        (localMod k p : ℤ)])
    (h_n_mod : (Nk_formula k : ℤ) ∣ n - R) :
    n ≡ (k : ℤ) - (cov.a p : ℤ) [ZMOD (p : ℤ)] :=
  n_mod_p_eq_k_sub_a_of_a cov.a R n hp hp_le_k (cov.a_lt_p p hp) hRloc h_n_mod

theorem h_non_excess_at_one_nonzero_of_a {k p : ℕ} (a : ℕ → ℕ) (R : ℤ) (n : ℤ)
    (hp : p.Prime) (hp_le_k : p ≤ k) (ha_lt : a p < p)
    (hRloc : ∀ p ∈ primeSet k,
      R ≡ localResidue k a p [ZMOD
        (localMod k p : ℤ)])
    (h_n_mod : (Nk_formula k : ℤ) ∣ n - R) (h_n_nonneg : 0 ≤ n)
    (h_ne : k % p < a p) :
    k % p ≤ n.toNat % p := by
  have h_n_mod_int := n_mod_p_eq_k_sub_a_of_a a R n hp hp_le_k ha_lt hRloc h_n_mod
  have hp_pos : 0 < p := hp.pos
  have h_n_toNat_eq : (n.toNat : ℤ) = n := Int.toNat_of_nonneg h_n_nonneg
  have h_n_natMod : n.toNat % p = (k + p - a p) % p := by
    have h_target_int : ((n.toNat % p : ℕ) : ℤ) = (((k + p - a p) % p : ℕ) : ℤ) := by
      have h_diff_int : ((k + p - a p : ℕ) : ℤ) = (k : ℤ) - (a p : ℤ) + (p : ℤ) := by
        push_cast; omega
      have h_lhs : ((n.toNat % p : ℕ) : ℤ) = n % (p : ℤ) := by
        push_cast; rw [← h_n_toNat_eq]; rfl
      have h_rhs : (((k + p - a p) % p : ℕ) : ℤ) =
          ((k + p - a p : ℕ) : ℤ) % (p : ℤ) := by
        push_cast; rfl
      rw [h_lhs, h_rhs, h_diff_int]
      change n % (p : ℤ) = ((k : ℤ) - (a p : ℤ) + (p : ℤ)) % (p : ℤ)
      rw [Int.add_emod_right]
      exact h_n_mod_int
    exact_mod_cast h_target_int
  rw [h_n_natMod]
  have h_ne_pow : k % p ^ 1 < a p := by rw [pow_one]; exact h_ne
  have h_lt_pow : a p < p ^ 1 := by rw [pow_one]; exact ha_lt
  have h_pow_pos : 0 < p ^ 1 := by rw [pow_one]; exact hp_pos
  have h_result := mod_sub_lift_ge_k_mod h_pow_pos h_lt_pow h_ne_pow
  rw [pow_one] at h_result
  exact h_result

theorem h_non_excess_at_one_nonzero {B k p : ℕ}
    (cov : CoverData B k) (R : ℤ) (n : ℤ)
    (hp : p.Prime) (hp_le_k : p ≤ k)
    (hRloc : ∀ p ∈ primeSet k,
      R ≡ localResidue k cov.a p [ZMOD
        (localMod k p : ℤ)])
    (h_n_mod : (Nk_formula k : ℤ) ∣ n - R) (h_n_nonneg : 0 ≤ n)
    (h_ne : k % p < cov.a p) :
    k % p ≤ n.toNat % p :=
  h_non_excess_at_one_nonzero_of_a cov.a R n hp hp_le_k (cov.a_lt_p p hp) hRloc h_n_mod
    h_n_nonneg h_ne

theorem a_eq_zero_of_p_lt_B {B k : ℕ}
    (cov : CoverData B k)
    (p : ℕ) (hp : p.Prime) (hp_lt_B : p < B) : cov.a p = 0 := by
  by_contra hne
  rcases cov.scaffold p hp hne with hpq | ⟨hk2, _, _⟩
  · have := cov.m_le_q; omega
  · have := cov.k_ge_4m; omega

theorem h_top_of_a_zero_of_a {k p : ℕ} (a : ℕ → ℕ) (R : ℤ) (n : ℤ)
    (hp : p.Prime) (hp_le_k : p ≤ k)
    (hRloc : ∀ p ∈ primeSet k,
      R ≡ localResidue k a p [ZMOD
        (localMod k p : ℤ)])
    (h_n_mod : (Nk_formula k : ℤ) ∣ n - R) (hzero : a p = 0)
    (h_n_nonneg : 0 ≤ n) :
    ∀ i ∈ Finset.range k,
      ¬ p ^ (alphaP k p + 1) ∣ n.toNat - i := by
  intro i hi h_dvd
  rw [Finset.mem_range] at hi
  have h_n_eq_k_int :=
    n_mod_pow_eq_k_mod_pow_of_a_zero_of_a a R n hp hp_le_k hRloc h_n_mod
      (le_refl _) hzero
  have h_n_eq : (n.toNat : ℤ) = n := Int.toNat_of_nonneg h_n_nonneg
  set α1 := alphaP k p + 1
  have hk_lt_pow : k < p ^ α1 := alphaP_succ_pow_gt hp.one_lt
  have h_k_mod_eq : (k : ℤ) % ((p ^ α1 : ℕ) : ℤ) = (k : ℤ) := by
    push_cast
    exact Int.emod_eq_of_lt (by exact_mod_cast Nat.zero_le k) (by exact_mod_cast hk_lt_pow)
  have h_n_mod_eq_k : n % ((p ^ α1 : ℕ) : ℤ) = (k : ℤ) := by
    have := h_n_eq_k_int
    unfold Int.ModEq at this
    rw [this, h_k_mod_eq]
  have h_n_toNat_mod : n.toNat % p ^ α1 = k := by
    have h_cast := h_n_mod_eq_k
    have : (n % ((p ^ α1 : ℕ) : ℤ) : ℤ) = (k : ℤ) := h_n_mod_eq_k
    have h_n_mod_natCast : ((n.toNat % p ^ α1 : ℕ) : ℤ) = (k : ℤ) := by
      rw [← h_n_eq] at this
      have h_ge : (0 : ℤ) ≤ ((p ^ α1 : ℕ) : ℤ) := by exact_mod_cast Nat.zero_le _
      push_cast at this ⊢
      omega
    exact_mod_cast h_n_mod_natCast
  have h_n_toNat_ge : k ≤ n.toNat := by
    have h_pow_pos : 0 < p ^ α1 := Nat.pow_pos (a := p) hp.pos
    by_contra h_lt
    push_neg at h_lt
    have h_n_lt_pow : n.toNat < p ^ α1 := by omega
    have h_n_mod_self : n.toNat % p ^ α1 = n.toNat := Nat.mod_eq_of_lt h_n_lt_pow
    rw [h_n_mod_self] at h_n_toNat_mod
    omega
  have h_i_mod_n : n.toNat % p ^ α1 = i % p ^ α1 := by
    have hi_le_n : i ≤ n.toNat := by omega
    have h_modeq : i ≡ n.toNat [MOD p ^ α1] := (Nat.modEq_iff_dvd' hi_le_n).mpr h_dvd
    exact h_modeq.symm
  have h_i_mod : i % p ^ α1 = k := by rw [← h_i_mod_n]; exact h_n_toNat_mod
  have hi_lt_pow : i < p ^ α1 := by omega
  rw [Nat.mod_eq_of_lt hi_lt_pow] at h_i_mod
  omega

theorem h_top_of_a_zero {B k p : ℕ}
    (cov : CoverData B k) (R : ℤ) (n : ℤ)
    (hp : p.Prime) (hp_le_k : p ≤ k)
    (hRloc : ∀ p ∈ primeSet k,
      R ≡ localResidue k cov.a p [ZMOD
        (localMod k p : ℤ)])
    (h_n_mod : (Nk_formula k : ℤ) ∣ n - R) (hzero : cov.a p = 0)
    (h_n_nonneg : 0 ≤ n) :
    ∀ i ∈ Finset.range k,
      ¬ p ^ (alphaP k p + 1) ∣ n.toNat - i :=
  h_top_of_a_zero_of_a cov.a R n hp hp_le_k hRloc h_n_mod hzero h_n_nonneg

theorem n_mod_localMod_eq_k_when_a_zero {B k : ℕ}
    (cov : CoverData B k) (R : ℤ)
    (hRloc : ∀ p ∈ primeSet k,
      R ≡ localResidue k cov.a p [ZMOD
        (localMod k p : ℤ)])
    (n : ℤ) (h_n_mod : (Nk_formula k : ℤ) ∣ n - R)
    (p : ℕ) (hp_prime : p.Prime) (hp_le : p ≤ k) (hap : cov.a p = 0) :
    n ≡ (k : ℤ) [ZMOD (localMod k p : ℤ)] := by
  have hp_mem : p ∈ primeSet k :=
    mem_primeSet.mpr ⟨hp_prime.one_lt.le, hp_le, hp_prime⟩
  have hRmod := hRloc p hp_mem
  rw [localResidue_eq_k_when_a_zero hap] at hRmod
  have h_pow_dvd : (localMod k p : ℤ) ∣ (Nk_formula k : ℤ) :=
    localMod_dvd_Nk_formula hp_prime hp_le
  have h_dvd_loc : (localMod k p : ℤ) ∣ n - R :=
    h_pow_dvd.trans h_n_mod
  have h_neg : (localMod k p : ℤ) ∣ R - n := by
    rw [show R - n = -(n - R) by ring]; exact dvd_neg.mpr h_dvd_loc
  have h_n_eq_R : n ≡ R [ZMOD (localMod k p : ℤ)] :=
    Int.modEq_iff_dvd.mpr h_neg
  exact h_n_eq_R.trans hRmod

def LevelSafe (a : ℕ → ℕ) (k B : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → B ≤ p → p ≤ k → a p ≠ 0 → p ∣ k ∨ k / 2 < p

theorem val_sum_clause1_proof {B : ℕ} (hB : 3 ≤ B) (k : ℕ) (hk3 : 3 ≤ k)
    (cov : CoverData B k) (R : ℤ)
    (hRloc : ∀ p ∈ primeSet k,
      R ≡ localResidue k cov.a p [ZMOD
        (localMod k p : ℤ)])
    (hNE : IsNonExcessCov cov) (hSafe : LevelSafe cov.a k B) :
    ∀ n : ℤ, (k : ℤ) < n → (Nk_formula k : ℤ) ∣ n - R →
      ∀ p : ℕ, p.Prime → p ≤ k → ¬ (p : ℤ) ∣ ((n.toNat).choose k : ℤ) := by
  intro n hn_gt h_n_mod p hp hp_le_k h_dvd_int
  have hp_fact : Fact p.Prime := ⟨hp⟩
  have h_k_nonneg : (0 : ℤ) ≤ (k : ℤ) := by exact_mod_cast Nat.zero_le k
  have hn_nonneg : 0 ≤ n := by linarith
  have hn_eq : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hn_nonneg
  have hkn : k ≤ n.toNat := by
    have : (k : ℤ) ≤ (n.toNat : ℤ) := by rw [hn_eq]; linarith
    exact_mod_cast this
  have h_dvd_nat : p ∣ (n.toNat).choose k := by exact_mod_cast h_dvd_int
  have hk_ge_4 : 4 ≤ k := by have := cov.k_ge_4m; omega
  by_cases hBp : B ≤ p
  · by_cases hzero : cov.a p = 0
    · have h_top := h_top_of_a_zero cov R n hp hp_le_k hRloc h_n_mod hzero hn_nonneg
      have h_ne : ∀ u, 1 ≤ u → u ≤ alphaP k p →
          k % p ^ u ≤ n.toNat % p ^ u := fun u _ hu_hi =>
        h_non_excess_of_a_zero cov R n hp hp_le_k hRloc h_n_mod hn_nonneg (by omega) hzero
      exact p_not_dvd_choose_of_non_excess n.toNat k p hkn h_top h_ne h_dvd_nat
    · have hNE_p : k % p < cov.a p := hNE p hp hBp hp_le_k hzero
      rcases hSafe p hp hBp hp_le_k hzero with hp_dvd_k | hp_half
      · have h_lift_gt : k < liftAtLevel cov.a p
            (alphaP k p + 1) :=
          liftAtLevel_top_gt_k_of_p_dvd_k hp hp_dvd_k
            (Nat.one_le_iff_ne_zero.mpr hzero) (cov.a_lt_p p hp) (by omega)
        have h_top := h_top_of_liftTop_gt_k cov R n hp hp_le_k hRloc h_n_mod hn_nonneg hkn h_lift_gt
        have h_ne : ∀ u, 1 ≤ u → u ≤ alphaP k p →
            k % p ^ u ≤ n.toNat % p ^ u := fun u hu_lo hu_hi =>
          h_non_excess_for_p_dvd_k_at_u cov R n hp hp_le_k hp_dvd_k hRloc h_n_mod hn_nonneg hzero
            hu_lo (by omega)
        exact p_not_dvd_choose_of_non_excess n.toNat k p hkn h_top h_ne h_dvd_nat
      · have h_lift_gt : k < liftAtLevel cov.a p
            (alphaP k p + 1) :=
          liftAtLevel_top_gt_k_of_scaffold hp hp_half hp_le_k (by omega)
            (Nat.one_le_iff_ne_zero.mpr hzero) (cov.a_lt_p p hp)
        have h_top := h_top_of_liftTop_gt_k cov R n hp hp_le_k hRloc h_n_mod hn_nonneg hkn h_lift_gt
        have h_alpha_le : alphaP k p ≤ 1 :=
          alphaP_le_one_of_scaffold hp.one_lt hp_half hp_le_k (by omega)
        have h_ne : ∀ u, 1 ≤ u → u ≤ alphaP k p →
            k % p ^ u ≤ n.toNat % p ^ u := by
          intro u hu_lo hu_hi
          have hu1 : u = 1 := by omega
          rw [hu1, pow_one]
          exact h_non_excess_at_one_nonzero cov R n hp hp_le_k hRloc h_n_mod hn_nonneg hNE_p
        exact p_not_dvd_choose_of_non_excess n.toNat k p hkn h_top h_ne h_dvd_nat
  · push_neg at hBp
    have hzero : cov.a p = 0 := a_eq_zero_of_p_lt_B cov p hp hBp
    have h_top := h_top_of_a_zero cov R n hp hp_le_k hRloc h_n_mod hzero hn_nonneg
    have h_ne : ∀ u, 1 ≤ u → u ≤ alphaP k p →
        k % p ^ u ≤ n.toNat % p ^ u := fun u _ hu_hi =>
      h_non_excess_of_a_zero cov R n hp hp_le_k hRloc h_n_mod hn_nonneg (by omega) hzero
    exact p_not_dvd_choose_of_non_excess n.toNat k p hkn h_top h_ne h_dvd_nat

theorem val_sum_clause1_proof_wide {B : ℕ} (hB : 3 ≤ B) (k : ℕ) (hk3 : 3 ≤ k)
    (a : ℕ → ℕ) (q : ℕ)
    (ha_lt : ∀ p, p.Prime → a p < p)
    (k_ge_4m : 4 * B + 4 ≤ k)
    (a_zero_of_lt_B : ∀ p, p.Prime → p < B → a p = 0)
    (R : ℤ)
    (hRloc : ∀ p ∈ primeSet k,
      R ≡ localResidue k a p [ZMOD
        (localMod k p : ℤ)])
    (hNE : ∀ p, p.Prime → B ≤ p → p ≤ k → a p ≠ 0 → k % p < a p)
    (hSafe : LevelSafe a k B) :
    ∀ n : ℤ, (k : ℤ) < n → (Nk_formula k : ℤ) ∣ n - R →
      ∀ p : ℕ, p.Prime → p ≤ k → ¬ (p : ℤ) ∣ ((n.toNat).choose k : ℤ) := by
  intro n hn_gt h_n_mod p hp hp_le_k h_dvd_int
  have hp_fact : Fact p.Prime := ⟨hp⟩
  have h_k_nonneg : (0 : ℤ) ≤ (k : ℤ) := by exact_mod_cast Nat.zero_le k
  have hn_nonneg : 0 ≤ n := by linarith
  have hn_eq : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hn_nonneg
  have hkn : k ≤ n.toNat := by
    have : (k : ℤ) ≤ (n.toNat : ℤ) := by rw [hn_eq]; linarith
    exact_mod_cast this
  have h_dvd_nat : p ∣ (n.toNat).choose k := by exact_mod_cast h_dvd_int
  have hk_ge_4 : 4 ≤ k := by omega
  by_cases hBp : B ≤ p
  · by_cases hzero : a p = 0
    · have h_top := h_top_of_a_zero_of_a a R n hp hp_le_k hRloc h_n_mod hzero hn_nonneg
      have h_ne : ∀ u, 1 ≤ u → u ≤ alphaP k p →
          k % p ^ u ≤ n.toNat % p ^ u := fun u _ hu_hi =>
        h_non_excess_of_a_zero_of_a a R n hp hp_le_k hRloc h_n_mod hn_nonneg (by omega) hzero
      exact p_not_dvd_choose_of_non_excess n.toNat k p hkn h_top h_ne h_dvd_nat
    · have hNE_p : k % p < a p := hNE p hp hBp hp_le_k hzero
      rcases hSafe p hp hBp hp_le_k hzero with hp_dvd_k | hp_half
      · have h_lift_gt : k < liftAtLevel a p
            (alphaP k p + 1) :=
          liftAtLevel_top_gt_k_of_p_dvd_k hp hp_dvd_k
            (Nat.one_le_iff_ne_zero.mpr hzero) (ha_lt p hp) (by omega)
        have h_top := h_top_of_liftTop_gt_k_of_a a R n hp hp_le_k (ha_lt p hp) hRloc h_n_mod
          hn_nonneg hkn h_lift_gt
        have h_ne : ∀ u, 1 ≤ u → u ≤ alphaP k p →
            k % p ^ u ≤ n.toNat % p ^ u := fun u hu_lo hu_hi =>
          h_non_excess_for_p_dvd_k_at_u_of_a a R n hp hp_le_k hp_dvd_k (ha_lt p hp) hRloc h_n_mod
            hn_nonneg hzero hu_lo (by omega)
        exact p_not_dvd_choose_of_non_excess n.toNat k p hkn h_top h_ne h_dvd_nat
      · have h_lift_gt : k < liftAtLevel a p
            (alphaP k p + 1) :=
          liftAtLevel_top_gt_k_of_scaffold hp hp_half hp_le_k (by omega)
            (Nat.one_le_iff_ne_zero.mpr hzero) (ha_lt p hp)
        have h_top := h_top_of_liftTop_gt_k_of_a a R n hp hp_le_k (ha_lt p hp) hRloc h_n_mod
          hn_nonneg hkn h_lift_gt
        have h_alpha_le : alphaP k p ≤ 1 :=
          alphaP_le_one_of_scaffold hp.one_lt hp_half hp_le_k (by omega)
        have h_ne : ∀ u, 1 ≤ u → u ≤ alphaP k p →
            k % p ^ u ≤ n.toNat % p ^ u := by
          intro u hu_lo hu_hi
          have hu1 : u = 1 := by omega
          rw [hu1, pow_one]
          exact h_non_excess_at_one_nonzero_of_a a R n hp hp_le_k (ha_lt p hp) hRloc h_n_mod
            hn_nonneg hNE_p
        exact p_not_dvd_choose_of_non_excess n.toNat k p hkn h_top h_ne h_dvd_nat
  · push_neg at hBp
    have hzero : a p = 0 := a_zero_of_lt_B p hp hBp
    have h_top := h_top_of_a_zero_of_a a R n hp hp_le_k hRloc h_n_mod hzero hn_nonneg
    have h_ne : ∀ u, 1 ≤ u → u ≤ alphaP k p →
        k % p ^ u ≤ n.toNat % p ^ u := fun u _ hu_hi =>
      h_non_excess_of_a_zero_of_a a R n hp hp_le_k hRloc h_n_mod hn_nonneg (by omega) hzero
    exact p_not_dvd_choose_of_non_excess n.toNat k p hkn h_top h_ne h_dvd_nat

structure WideCoverData (B k : ℕ) where
  a : ℕ → ℕ
  q : ℕ
  q_prime : q.Prime
  B_le_q : B ≤ q
  q_le_k_half : q ≤ k / 2
  k_ge_4m : 4 * B + 4 ≤ k
  q_dvd_k : q ∣ k
  a_lt_p : ∀ p, p.Prime → a p < p
  a_bound : ∀ p, p.Prime → B ≤ p → p < k → a p < p - k % p
  a_zero_of_lt_B : ∀ p, p.Prime → p < B → a p = 0
  scaffold : ∀ p, p.Prime → a p ≠ 0 →
    p ∣ k ∨ (k / 2 < p ∧ p ≤ k ∧ p % q = 1)

noncomputable def CoverData.toWide {B k : ℕ}
    (cov : CoverData B k) : WideCoverData B k where
  a := cov.a
  q := cov.q
  q_prime := cov.q_prime
  B_le_q := cov.m_le_q
  q_le_k_half := by
    have h1 := cov.q_le_2m
    have h2 := cov.k_ge_4m
    omega
  k_ge_4m := cov.k_ge_4m
  q_dvd_k := cov.q_dvd_k
  a_lt_p := cov.a_lt_p
  a_bound := cov.a_bound
  a_zero_of_lt_B := fun p hp hpB => by
    by_contra hne
    rcases cov.scaffold p hp hne with hpq | ⟨hk2, _, _⟩
    · subst hpq; have := cov.m_le_q; omega
    · have := cov.k_ge_4m; omega
  scaffold := fun p hp hnz => by
    rcases cov.scaffold p hp hnz with hpq | h
    · left; rw [hpq]; exact cov.q_dvd_k
    · right; exact h

noncomputable def WideCoverData.ofRawData {B k : ℕ} (a : ℕ → ℕ) (q : ℕ)
    (hq_prime : q.Prime) (hB_le_q : B ≤ q) (hq_le_k_half : q ≤ k / 2)
    (hk_ge_4B : 4 * B + 4 ≤ k) (hq_dvd_k : q ∣ k)
    (ha_lt_p : ∀ p, p.Prime → a p < p)
    (ha_bound : ∀ p, p.Prime → B ≤ p → p < k → a p < p - k % p)
    (ha_zero_of_lt_B : ∀ p, p.Prime → p < B → a p = 0)
    (h_scaffold : ∀ p, p.Prime → a p ≠ 0 →
      p ∣ k ∨ (k / 2 < p ∧ p ≤ k ∧ p % q = 1)) :
    WideCoverData B k where
  a := a
  q := q
  q_prime := hq_prime
  B_le_q := hB_le_q
  q_le_k_half := hq_le_k_half
  k_ge_4m := hk_ge_4B
  q_dvd_k := hq_dvd_k
  a_lt_p := ha_lt_p
  a_bound := ha_bound
  a_zero_of_lt_B := ha_zero_of_lt_B
  scaffold := h_scaffold

theorem LevelSafe_of_wide {B k : ℕ} (cov : WideCoverData B k) :
    LevelSafe cov.a k B := by
  intro p hp _ _ hnz
  rcases cov.scaffold p hp hnz with hp_dvd | ⟨hk2, _, _⟩
  · exact Or.inl hp_dvd
  · exact Or.inr hk2

def IsNonExcessWide {B k : ℕ} (cov : WideCoverData B k) : Prop :=
  ∀ p, p.Prime → B ≤ p → p ≤ k → cov.a p ≠ 0 → k % p < cov.a p

theorem n_toNat_mod_Z_eq_k_of_a {k : ℕ} (a : ℕ → ℕ) (R n : ℤ)
    (hRloc : ∀ p ∈ primeSet k,
      R ≡ localResidue k a p [ZMOD
        (localMod k p : ℤ)])
    (h_n_mod : (Nk_formula k : ℤ) ∣ n - R)
    (h_n_nonneg : 0 ≤ n) (h_n_ge_k : k ≤ n.toNat) :
    n.toNat % Z_modulus k a = k % Z_modulus k a := by
  set S := (Finset.Icc 1 k).filter (fun p => p.Prime ∧ a p = 0) with hS_def
  set f : ℕ → ℕ := fun p => p ^ (Nat.log p k + 1) with hf_def
  have hZ_eq : Z_modulus k a = ∏ p ∈ S, f p := rfl
  have h_each : ∀ p ∈ S, (f p : ℕ) ∣ n.toNat - k := by
    intro p hp_in
    rw [Finset.mem_filter, Finset.mem_Icc] at hp_in
    obtain ⟨⟨_, hp_le_k⟩, hp_prime, hzero⟩ := hp_in
    have h_int := n_mod_pow_eq_k_mod_pow_of_a_zero_of_a a R n hp_prime hp_le_k hRloc h_n_mod
      (u := Nat.log p k + 1) (le_refl _) hzero
    have h_n_eq : (n.toNat : ℤ) = n := Int.toNat_of_nonneg h_n_nonneg
    have h_diff : (f p : ℤ) ∣ (n.toNat : ℤ) - (k : ℤ) := by
      have h_cast : ((p ^ (Nat.log p k + 1) : ℕ) : ℤ) = (f p : ℤ) := by simp [hf_def]
      rw [← h_cast]
      rw [← h_n_eq] at h_int
      exact Int.ModEq.dvd h_int.symm
    have h_cast_diff : ((n.toNat - k : ℕ) : ℤ) = (n.toNat : ℤ) - (k : ℤ) := by
      rw [Nat.cast_sub h_n_ge_k]
    rw [← h_cast_diff] at h_diff
    exact_mod_cast h_diff
  have h_pairwise : (S : Set ℕ).Pairwise (Function.onFun IsRelPrime f) := by
    intro p hp q hq hpq
    simp only [Function.onFun]
    rw [Finset.mem_coe, Finset.mem_filter] at hp hq
    have hc : Nat.Coprime p q := (Nat.coprime_primes hp.2.1 hq.2.1).mpr hpq
    exact Nat.coprime_iff_isRelPrime.mp (hc.pow (Nat.log p k + 1) (Nat.log q k + 1))
  have h_prod_dvd : (∏ p ∈ S, f p) ∣ n.toNat - k :=
    Finset.prod_dvd_of_isRelPrime h_pairwise h_each
  rw [← hZ_eq] at h_prod_dvd
  exact ((Nat.modEq_iff_dvd' h_n_ge_k).mpr h_prod_dvd).symm

theorem scaffoldExcess_empty_wide {B k : ℕ} (cov : WideCoverData B k)
    (hNE : IsNonExcessWide cov)
    (i : ℕ) :
    ∀ p, p ∉ scaffoldExcess k cov.a (k - i) := by
  intro p hp_mem
  unfold scaffoldExcess at hp_mem
  rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc] at hp_mem
  obtain ⟨⟨⟨_, hpk⟩, hp_prime⟩, hap_ne, hp_gt, _hp_lt_j, h_mod, _h_sub_ge⟩ := hp_mem
  have hap_lt : cov.a p < p := cov.a_lt_p p hp_prime
  have hBp : B ≤ p := by
    by_contra hpB
    push_neg at hpB
    exact hap_ne (cov.a_zero_of_lt_B p hp_prime hpB)
  have hne : k % p < cov.a p := hNE p hp_prime hBp hpk hap_ne
  have hk_lt_2p : k < 2 * p := by omega
  have h_k_mod : k % p = k - p := by
    have h_lt : k - p < p := by omega
    have h_eq : k = (k - p) + p := by omega
    rw [h_eq, Nat.add_mod_right, Nat.mod_eq_of_lt h_lt]
    omega
  have hk_i_p_lt : k - i - p < p := by omega
  rw [Nat.mod_eq_of_lt hk_i_p_lt] at h_mod
  omega

theorem h_lift_gt_k_of_wide {B k : ℕ} (cov : WideCoverData B k)
    (hSafe : LevelSafe cov.a k B) (p : ℕ) (hp : p.Prime) (hpk : p ≤ k)
    (hap_ne : cov.a p ≠ 0) :
    k < localLift k cov.a p := by
  have hap_lt : cov.a p < p := cov.a_lt_p p hp
  have hBp : B ≤ p := by
    by_contra hpB
    push_neg at hpB
    exact hap_ne (cov.a_zero_of_lt_B p hp hpB)
  have hk_ge_4 : 4 ≤ k := by have := cov.k_ge_4m; omega
  rcases hSafe p hp hBp hpk hap_ne with hp_dvd | hp_gt
  · exact localLift_gt_k_p_dvd_k_of_a
      cov.a p hp hp_dvd hap_lt hap_ne
  · exact localLift_gt_k_scaffold_of_a
      hk_ge_4 cov.a p hp hpk hp_gt hap_lt hap_ne

theorem outerB_dvd_term_of_progression_wide {k : ℕ} (a : ℕ → ℕ)
    (ha_lt : ∀ p, p.Prime → a p < p)
    (R n : ℤ)
    (hRloc : ∀ p ∈ primeSet k,
      R ≡ localResidue k a p [ZMOD
        (localMod k p : ℤ)])
    (h_n_mod : (Nk_formula k : ℤ) ∣ n - R) (h_n_nonneg : 0 ≤ n)
    (h_n_ge_k : k ≤ n.toNat) (i : ℕ) (hi : i < k) :
    outerB k a (k - i) ∣ n.toNat - i := by
  set j := k - i with hj_def
  have hj_pos : 1 ≤ j := by omega
  have hj_le : j ≤ k := by omega
  have h_i_le_k : i ≤ k := Nat.le_of_lt hi
  have hB_dvd_int : (outerB k a j : ℤ) ∣
      R - (k : ℤ) + (j : ℤ) :=
    outerB_dvd_num_of_a a j hj_pos hj_le ha_lt R hRloc
  obtain ⟨m, hm_eq⟩ := h_n_mod
  rw [Nk_formula_eq_globalMk k] at hm_eq
  have h_n_eq : n = R + (globalMk k : ℤ) * m := by linarith
  have hB_dvd_shifted : (outerB k a j : ℤ) ∣
      R + (globalMk k : ℤ) * m - (k : ℤ) + (j : ℤ) :=
    outerB_dvd_num_shifted_of_a a j hj_pos hj_le R m hB_dvd_int
  rw [← h_n_eq] at hB_dvd_shifted
  have h_n_int : n = (n.toNat : ℤ) := (Int.toNat_of_nonneg h_n_nonneg).symm
  have h_rw : n - (k : ℤ) + (j : ℤ) = (n.toNat : ℤ) - (i : ℤ) := by
    have h_j_eq : (j : ℤ) = (k : ℤ) - (i : ℤ) := by rw [hj_def, Nat.cast_sub h_i_le_k]
    rw [h_j_eq]; rw [← h_n_int]; ring
  rw [h_rw] at hB_dvd_shifted
  have hi_le_n : i ≤ n.toNat := by omega
  have h_cast : ((n.toNat - i : ℕ) : ℤ) = (n.toNat : ℤ) - (i : ℤ) := by
    rw [Nat.cast_sub hi_le_n]
  rw [← h_cast] at hB_dvd_shifted
  exact_mod_cast hB_dvd_shifted

theorem quotient_has_no_prime_le_k_wide {B k : ℕ} (cov : WideCoverData B k)
    (hk : 3 ≤ k) (hNE : IsNonExcessWide cov) (hSafe : LevelSafe cov.a k B)
    (R n : ℤ)
    (hRloc : ∀ p ∈ primeSet k,
      R ≡ localResidue k cov.a p [ZMOD
        (localMod k p : ℤ)])
    (h_n_mod : (Nk_formula k : ℤ) ∣ n - R) (h_n_nonneg : 0 ≤ n)
    (h_n_ge_k : k ≤ n.toNat) (i : ℕ) (hi : i < k) :
    ∀ p : ℕ, p.Prime → p ≤ k →
      ¬ p ∣ (n.toNat - k + (k - i)) /
        outerB k cov.a (k - i) := by
  intro p hp_prime hpk h_dvd_nat
  have hj_lt : k - i - 1 < k := by omega
  set j : Fin k := ⟨k - i - 1, hj_lt⟩ with hj_def
  have hj_val_succ : j.val + 1 = k - i := by simp [hj_def]; omega
  have hi_le_k : i ≤ k := Nat.le_of_lt hi
  have h_Nat_eq : n.toNat - k + (k - i) = n.toNat - i := by omega
  rw [h_Nat_eq] at h_dvd_nat
  obtain ⟨m, hm_eq⟩ := h_n_mod
  rw [Nk_formula_eq_globalMk] at hm_eq
  have h_n_int_eq : n = R + (globalMk k : ℤ) * m := by linarith
  have h_n_toNat_int : (n.toNat : ℤ) = n := Int.toNat_of_nonneg h_n_nonneg
  have hi_le_n : i ≤ n.toNat := by omega
  have h_cast_nat : ((n.toNat - i : ℕ) : ℤ) = (n.toNat : ℤ) - (i : ℤ) := Nat.cast_sub hi_le_n
  set B_n := outerB k cov.a (k - i)
  have h_dvd_int : (p : ℤ) ∣ ((n.toNat - i : ℕ) : ℤ) / (B_n : ℤ) := by
    have h_div_cast : (((n.toNat - i) / B_n : ℕ) : ℤ) =
        ((n.toNat - i : ℕ) : ℤ) / ((B_n : ℕ) : ℤ) := Int.natCast_div (n.toNat - i) B_n
    have h_p_dvd_int : (p : ℤ) ∣ (((n.toNat - i) / B_n : ℕ) : ℤ) := by exact_mod_cast h_dvd_nat
    rw [h_div_cast] at h_p_dvd_int
    exact h_p_dvd_int
  have h_num_eq : (R + (globalMk k : ℤ) * m
        - (k : ℤ) + ((j.val : ℤ) + 1)) = ((n.toNat - i : ℕ) : ℤ) := by
    rw [← h_n_int_eq, h_cast_nat, h_n_toNat_int]
    have h_j_eq : (j.val : ℤ) + 1 = (k : ℤ) - (i : ℤ) := by
      have h_succ_eq : (j.val + 1 : ℕ) = k - i := hj_val_succ
      have h_cast : ((j.val + 1 : ℕ) : ℤ) = ((k - i : ℕ) : ℤ) := by exact_mod_cast h_succ_eq
      have h_k_i_int : ((k - i : ℕ) : ℤ) = (k : ℤ) - (i : ℤ) := Nat.cast_sub hi_le_k
      push_cast at h_cast
      linarith
    linarith
  have h_outerB_eq : outerB k cov.a (j.val + 1) = B_n := by
    rw [hj_val_succ]
  have h_dvd_int' : (p : ℤ) ∣
      (R + (globalMk k : ℤ) * m - (k : ℤ) +
        ((j.val : ℤ) + 1)) /
      (outerB k cov.a (j.val + 1) : ℤ) := by
    rw [h_outerB_eq, h_num_eq]; exact h_dvd_int
  have h_lift_gt_k_p := h_lift_gt_k_of_wide cov hSafe p hp_prime hpk
  have hp_in : p ∈
      scaffoldExcess k cov.a (j.val + 1) :=
    small_prime_div_quotient_imp_scaffold_truly_of_a
      cov.a cov.a_lt_p R m j p hp_prime hpk h_lift_gt_k_p hRloc h_dvd_int'
  rw [hj_val_succ] at hp_in
  exact scaffoldExcess_empty_wide cov hNE i p hp_in

theorem clause2_holds_from_Z_gt_Bj_wide {B : ℕ} (hB : 3 ≤ B) (k : ℕ) (hk3 : 3 ≤ k)
    (cov : WideCoverData B k) (hNE : IsNonExcessWide cov) (hSafe : LevelSafe cov.a k B)
    (hZ : ∀ j : Fin k,
      outerB k cov.a (j.val + 1) < Z_modulus k cov.a)
    (R : ℤ)
    (hRloc : ∀ p ∈ primeSet k,
      R ≡ localResidue k cov.a p [ZMOD
        (localMod k p : ℤ)]) :
    ∀ n : ℤ, (k : ℤ) < n → (Nk_formula k : ℤ) ∣ n - R →
      ∀ i : ℕ, i < k → ∃ p : ℕ, p.Prime ∧ B ≤ p ∧ (p : ℤ) ∣ n - (i : ℤ) := by
  intro n hn_gt h_n_mod i hi
  have h_n_nonneg : 0 ≤ n := by linarith
  have h_n_toNat_int : (n.toNat : ℤ) = n := Int.toNat_of_nonneg h_n_nonneg
  have h_n_ge_k : k ≤ n.toNat := by
    have : (k : ℤ) ≤ (n.toNat : ℤ) := by rw [h_n_toNat_int]; linarith
    exact_mod_cast this
  have h_k_lt_n_toNat : k < n.toNat := by
    have : (k : ℤ) < (n.toNat : ℤ) := by rw [h_n_toNat_int]; exact hn_gt
    exact_mod_cast this
  have hkB : B ≤ k := by have := cov.k_ge_4m; omega
  have hj_lt : k - i - 1 < k := by omega
  set j : Fin k := ⟨k - i - 1, hj_lt⟩ with hj_def
  have hj_val_succ : j.val + 1 = k - i := by simp [hj_def]; omega
  set B_j := outerB k cov.a (k - i) with hBj_def
  have hB_j_pos : 0 < B_j :=
    outerB_pos_of_a cov.a (k - i) (by omega) (by omega)
  have h_Z_dvd_N : Z_modulus k cov.a ∣ Nk_formula k := Z_modulus_dvd_Nk_formula cov.a
  have h_alpha_mod_Z : n.toNat % Z_modulus k cov.a = k % Z_modulus k cov.a :=
    n_toNat_mod_Z_eq_k_of_a cov.a R n hRloc h_n_mod h_n_nonneg h_n_ge_k
  have h_alpha_pack : ∃ α_k : ℕ,
      α_k % Z_modulus k cov.a = k % Z_modulus k cov.a ∧
      n.toNat % Nk_formula k = α_k % Nk_formula k ∧ k < n.toNat :=
    ⟨n.toNat, h_alpha_mod_Z, rfl, h_k_lt_n_toNat⟩
  have h_Bj_dvd_int : (B_j : ℤ) ∣ (n.toNat - i : ℕ) := by
    have h_C2 : B_j ∣ n.toNat - i :=
      outerB_dvd_term_of_progression_wide cov.a cov.a_lt_p R n hRloc h_n_mod h_n_nonneg h_n_ge_k i hi
    exact_mod_cast h_C2
  have h_Bj_dvd : B_j ∣ n.toNat - k + (k - i) := by
    have h_eq : n.toNat - k + (k - i) = n.toNat - i := by omega
    rw [h_eq]
    exact outerB_dvd_term_of_progression_wide cov.a cov.a_lt_p R n hRloc h_n_mod
      h_n_nonneg h_n_ge_k i hi
  have h_Bj_lt_Z : B_j < Z_modulus k cov.a := by
    have h_eq : j.val + 1 = k - i := hj_val_succ
    have := hZ j
    rw [h_eq] at this
    exact this
  have h_no_small_prime : ∀ p : ℕ, p.Prime → p ≤ k →
      ¬ p ∣ (n.toNat - k + (k - i)) / B_j :=
    quotient_has_no_prime_le_k_wide cov hk3 hNE hSafe R n hRloc h_n_mod h_n_nonneg h_n_ge_k i hi
  obtain ⟨p, hp_prime, hBp, hp_dvd_nat⟩ :=
    n_minus_i_has_prime_ge_B_from_Z_gt_B_j B cov.a h_n_ge_k hi hkB h_Z_dvd_N h_alpha_pack
      h_Bj_dvd h_Bj_lt_Z hB_j_pos h_no_small_prime
  refine ⟨p, hp_prime, hBp, ?_⟩
  have hi_le_n : i ≤ n.toNat := by omega
  have h_cast : ((n.toNat - i : ℕ) : ℤ) = n - (i : ℤ) := by
    rw [Nat.cast_sub hi_le_n, h_n_toNat_int]
  have h_p_dvd_int : (p : ℤ) ∣ ((n.toNat - i : ℕ) : ℤ) := by exact_mod_cast hp_dvd_nat
  rw [h_cast] at h_p_dvd_int
  exact h_p_dvd_int

theorem clause1_holds_for_nonexcess_wide {B : ℕ} (hB : 3 ≤ B) (k : ℕ) (hk3 : 3 ≤ k)
    (cov : WideCoverData B k) (hNE : IsNonExcessWide cov)
    (hSafe : LevelSafe cov.a k B)
    (R : ℤ)
    (hRloc : ∀ p ∈ primeSet k,
      R ≡ localResidue k cov.a p [ZMOD
        (localMod k p : ℤ)]) :
    ∀ n : ℤ, (k : ℤ) < n → (Nk_formula k : ℤ) ∣ n - R →
      ∀ p : ℕ, p.Prime → p ≤ k → ¬ (p : ℤ) ∣ ((n.toNat).choose k : ℤ) :=
  val_sum_clause1_proof_wide hB k hk3 cov.a cov.q cov.a_lt_p cov.k_ge_4m cov.a_zero_of_lt_B
    R hRloc hNE hSafe

theorem LevelSafe_of_cov {B k : ℕ}
    (cov : CoverData B k) :
    LevelSafe cov.a k B := by
  intro p hp _ _ hnz
  rcases cov.scaffold p hp hnz with hpq | ⟨hk2, _, _⟩
  · left; rw [hpq]; exact cov.q_dvd_k
  · right; exact hk2

theorem k_mod_p_eq_k_sub_p_of_half {k p : ℕ} (h_lo : k / 2 < p) (h_hi : p ≤ k) :
    k % p = k - p := by
  have h_p_pos : 0 < p := by omega
  have h_div : k / p = 1 :=
    Nat.div_eq_of_lt_le (k := 1) (by simp; omega) (by show k < 2 * p; omega)
  have h_mod_add := Nat.div_add_mod k p
  rw [h_div, Nat.mul_one] at h_mod_add
  omega

structure ScaffoldMatching (k Y : ℕ) where
  T : Finset ℕ
  T_subset : T ⊆ Finset.Ioc Y (k - Y)
  scaffold : T → ℕ
  scaffold_prime : ∀ t : T, (scaffold t).Prime
  scaffold_in_range : ∀ t : T, k - Y / 2 < scaffold t ∧ scaffold t ≤ k
  scaffold_inj : Function.Injective scaffold

theorem ScaffoldMatching.t_le_k_sub_Y {k Y : ℕ}
    (sm : ScaffoldMatching k Y) (t : sm.T) : t.val ≤ k - Y := by
  have := sm.T_subset t.property
  simp only [Finset.mem_Ioc] at this
  exact this.2

theorem ScaffoldMatching.t_gt_Y {k Y : ℕ}
    (sm : ScaffoldMatching k Y) (t : sm.T) : Y < t.val := by
  have := sm.T_subset t.property
  simp only [Finset.mem_Ioc] at this
  exact this.1

theorem ScaffoldMatching.t_lt_scaffold {k Y : ℕ}
    (sm : ScaffoldMatching k Y) (t : sm.T) : t.val < sm.scaffold t := by
  have h_t_le := sm.t_le_k_sub_Y t
  have h_p_lo := (sm.scaffold_in_range t).1
  omega

theorem ScaffoldMatching.non_excess_at_scaffold {k Y : ℕ}
    (sm : ScaffoldMatching k Y) (hY : 2 ≤ Y) (t : sm.T) :
    k % sm.scaffold t < t.val := by
  have h_t_lt := sm.t_lt_scaffold t
  have h_t_gt := sm.t_gt_Y t
  obtain ⟨h_lo, h_hi⟩ := sm.scaffold_in_range t
  have h_p_half : k / 2 < sm.scaffold t := by
    have h_t_le := sm.t_le_k_sub_Y t
    omega
  rw [k_mod_p_eq_k_sub_p_of_half h_p_half h_hi]
  omega

structure ScaffoldMatchingQ (k Y q : ℕ) extends ScaffoldMatching k Y where
  scaffold_mod_q : ∀ t : T, scaffold t % q = 1

theorem ScaffoldMatchingQ.scaffold_structural {k Y q : ℕ} (smq : ScaffoldMatchingQ k Y q)
    (hY_le : 2 * Y ≤ k) (t : smq.T) :
    k / 2 < smq.scaffold t ∧ smq.scaffold t ≤ k ∧ smq.scaffold t % q = 1 := by
  have h_lo := (smq.scaffold_in_range t).1
  have h_hi := (smq.scaffold_in_range t).2
  refine ⟨?_, h_hi, smq.scaffold_mod_q t⟩
  have h_t_gt := smq.t_gt_Y t
  omega

noncomputable def ScaffoldMatching.residue {k Y : ℕ} (sm : ScaffoldMatching k Y)
    (p : ℕ) : ℕ :=
  if h : ∃ t : sm.T, sm.scaffold t = p then h.choose.val else 0

theorem ScaffoldMatching.residue_eq_t {k Y : ℕ} (sm : ScaffoldMatching k Y)
    (t : sm.T) : sm.residue (sm.scaffold t) = t.val := by
  unfold ScaffoldMatching.residue
  have h : ∃ t' : sm.T, sm.scaffold t' = sm.scaffold t := ⟨t, rfl⟩
  rw [dif_pos h]
  have h_eq : h.choose = t := sm.scaffold_inj h.choose_spec
  rw [h_eq]

theorem ScaffoldMatching.residue_lt_p {k Y : ℕ} (sm : ScaffoldMatching k Y) (p : ℕ) :
    sm.residue p < p ∨ p = 0 := by
  unfold ScaffoldMatching.residue
  by_cases h : ∃ t : sm.T, sm.scaffold t = p
  · left
    rw [dif_pos h]
    have h_lt := sm.t_lt_scaffold h.choose
    rw [h.choose_spec] at h_lt
    exact h_lt
  · rw [dif_neg h]
    by_cases hp : p = 0
    · right; exact hp
    · left; omega

theorem ScaffoldMatching.residue_non_excess {k Y : ℕ} (sm : ScaffoldMatching k Y)
    (hY : 2 ≤ Y) (p : ℕ) (h_nz : sm.residue p ≠ 0) :
    k % p < sm.residue p := by
  unfold ScaffoldMatching.residue at h_nz ⊢
  by_cases h : ∃ t : sm.T, sm.scaffold t = p
  · rw [dif_pos h]
    rw [dif_pos h] at h_nz
    have := sm.non_excess_at_scaffold hY h.choose
    rw [h.choose_spec] at this
    exact this
  · rw [dif_neg h] at h_nz
    exact absurd rfl h_nz

structure BufferData (k Y : ℕ) where
  D : Finset ℕ
  D_subset : D ⊆ Finset.Icc 1 Y
  buffer : D → ℕ
  buffer_prime : ∀ d : D, (buffer d).Prime
  buffer_in_range : ∀ d : D, Y * Y < buffer d ∧ buffer d ≤ 2 * Y * Y
  buffer_dvd_k : ∀ d : D, buffer d ∣ k
  buffer_inj : Function.Injective buffer

noncomputable def BufferData.residue {k Y : ℕ} (bd : BufferData k Y) (p : ℕ) : ℕ :=
  if h : ∃ d : bd.D, bd.buffer d = p then h.choose.val else 0

theorem BufferData.residue_eq_d {k Y : ℕ} (bd : BufferData k Y) (d : bd.D) :
    bd.residue (bd.buffer d) = d.val := by
  unfold BufferData.residue
  have h : ∃ d' : bd.D, bd.buffer d' = bd.buffer d := ⟨d, rfl⟩
  rw [dif_pos h]
  have h_eq : h.choose = d := bd.buffer_inj h.choose_spec
  rw [h_eq]

theorem BufferData.residue_lt_p {k Y : ℕ} (bd : BufferData k Y) (hY : 1 ≤ Y) (p : ℕ) :
    bd.residue p < p ∨ p = 0 := by
  unfold BufferData.residue
  by_cases h : ∃ d : bd.D, bd.buffer d = p
  · left
    rw [dif_pos h]
    have h_d_le : h.choose.val ≤ Y := by
      have := bd.D_subset h.choose.property
      simp only [Finset.mem_Icc] at this; exact this.2
    have h_p_lo := (bd.buffer_in_range h.choose).1
    have h_step : h.choose.val < bd.buffer h.choose := by nlinarith
    have h_eq : bd.buffer h.choose = p := h.choose_spec
    omega
  · rw [dif_neg h]; by_cases hp : p = 0
    · right; exact hp
    · left; omega

theorem BufferData.residue_non_excess {k Y : ℕ} (bd : BufferData k Y) (p : ℕ)
    (h_nz : bd.residue p ≠ 0) :
    k % p < bd.residue p := by
  unfold BufferData.residue at h_nz ⊢
  by_cases h : ∃ d : bd.D, bd.buffer d = p
  · rw [dif_pos h] at h_nz ⊢
    have h_d_ge : 1 ≤ h.choose.val := by
      have := bd.D_subset h.choose.property
      simp only [Finset.mem_Icc] at this; exact this.1
    have h_buf_dvd : bd.buffer h.choose ∣ k := bd.buffer_dvd_k h.choose
    have h_eq : bd.buffer h.choose = p := h.choose_spec
    have h_p_dvd : p ∣ k := h_eq ▸ h_buf_dvd
    have h_k_mod : k % p = 0 := Nat.mod_eq_zero_of_dvd h_p_dvd
    rw [h_k_mod]; omega
  · rw [dif_neg h] at h_nz
    exact absurd rfl h_nz

noncomputable def combinedResidue {k Y : ℕ} (q : ℕ) (bd : BufferData k Y)
    (sm : ScaffoldMatching k Y) (p : ℕ) : ℕ :=
  if p = q then 1
  else if bd.residue p ≠ 0 then bd.residue p
  else sm.residue p

theorem combinedResidue_lt_p {k Y q : ℕ} (bd : BufferData k Y) (sm : ScaffoldMatching k Y)
    (hq : 1 < q) (hY : 1 ≤ Y) (p : ℕ) (hp_pos : 0 < p) :
    combinedResidue q bd sm p < p := by
  unfold combinedResidue
  split_ifs with hpq hbd
  · omega
  · rcases bd.residue_lt_p hY p with h | h
    · exact h
    · omega
  · rcases sm.residue_lt_p p with h | h
    · exact h
    · omega

theorem combinedResidue_non_excess {k Y q : ℕ} (bd : BufferData k Y)
    (sm : ScaffoldMatching k Y) (hY : 2 ≤ Y) (hq_dvd : q ∣ k) (p : ℕ)
    (h_nz : combinedResidue q bd sm p ≠ 0) :
    k % p < combinedResidue q bd sm p := by
  unfold combinedResidue at h_nz ⊢
  by_cases hpq : p = q
  · rw [if_pos hpq]
    rw [Nat.mod_eq_zero_of_dvd (hpq ▸ hq_dvd)]; omega
  · rw [if_neg hpq] at h_nz ⊢
    by_cases hbd : bd.residue p ≠ 0
    · rw [if_pos hbd] at h_nz ⊢
      exact bd.residue_non_excess p hbd
    · rw [if_neg hbd] at h_nz ⊢
      exact sm.residue_non_excess hY p h_nz

theorem ScaffoldMatching.residue_a_bound {k Y : ℕ} (sm : ScaffoldMatching k Y) (hY : 2 ≤ Y)
    (p : ℕ) (h_nz : sm.residue p ≠ 0) :
    sm.residue p < p - k % p := by
  unfold ScaffoldMatching.residue at h_nz ⊢
  by_cases h : ∃ t : sm.T, sm.scaffold t = p
  · rw [dif_pos h] at h_nz ⊢
    have h_t_le := sm.t_le_k_sub_Y h.choose
    have h_lo := (sm.scaffold_in_range h.choose).1
    have h_hi := (sm.scaffold_in_range h.choose).2
    have h_p_eq : sm.scaffold h.choose = p := h.choose_spec
    have h_p_half' : k / 2 < p := by have := sm.t_gt_Y h.choose; omega
    have h_p_le' : p ≤ k := h_p_eq ▸ h_hi
    rw [k_mod_p_eq_k_sub_p_of_half h_p_half' h_p_le']
    omega
  · rw [dif_neg h] at h_nz; exact absurd rfl h_nz

theorem BufferData.residue_a_bound {k Y : ℕ} (bd : BufferData k Y) (hY : 1 ≤ Y) (p : ℕ)
    (h_nz : bd.residue p ≠ 0) :
    bd.residue p < p - k % p := by
  unfold BufferData.residue at h_nz ⊢
  by_cases h : ∃ d : bd.D, bd.buffer d = p
  · rw [dif_pos h] at h_nz ⊢
    have h_d_le : h.choose.val ≤ Y := by
      have := bd.D_subset h.choose.property
      simp only [Finset.mem_Icc] at this; exact this.2
    have h_p_lo := (bd.buffer_in_range h.choose).1
    have h_eq : bd.buffer h.choose = p := h.choose_spec
    have h_p_dvd : p ∣ k := h_eq ▸ bd.buffer_dvd_k h.choose
    rw [Nat.mod_eq_zero_of_dvd h_p_dvd, Nat.sub_zero]
    have : h.choose.val < bd.buffer h.choose := by nlinarith
    omega
  · rw [dif_neg h] at h_nz; exact absurd rfl h_nz

theorem combinedResidue_a_bound {k Y q : ℕ} (bd : BufferData k Y)
    (sm : ScaffoldMatching k Y) (hY : 2 ≤ Y) (hq_dvd : q ∣ k) (hq : 1 < q) (p : ℕ)
    (h_nz : combinedResidue q bd sm p ≠ 0) :
    combinedResidue q bd sm p < p - k % p := by
  unfold combinedResidue at h_nz ⊢
  by_cases hpq : p = q
  · rw [if_pos hpq]
    rw [hpq, Nat.mod_eq_zero_of_dvd hq_dvd, Nat.sub_zero]
    exact hq
  · rw [if_neg hpq] at h_nz ⊢
    by_cases hbd : bd.residue p ≠ 0
    · rw [if_pos hbd] at h_nz ⊢
      exact bd.residue_a_bound (by omega) p hbd
    · rw [if_neg hbd] at h_nz ⊢
      exact sm.residue_a_bound hY p h_nz

theorem combinedResidue_at_q {k Y q : ℕ} (bd : BufferData k Y)
    (sm : ScaffoldMatching k Y) : combinedResidue q bd sm q = 1 := by
  unfold combinedResidue; rw [if_pos rfl]

theorem combinedResidue_at_buffer {k Y q : ℕ} (bd : BufferData k Y)
    (sm : ScaffoldMatching k Y) (d : bd.D)
    (h_neq_q : bd.buffer d ≠ q) (hd_pos : 1 ≤ d.val) :
    combinedResidue q bd sm (bd.buffer d) = d.val := by
  unfold combinedResidue
  rw [if_neg h_neq_q]
  have h_res : bd.residue (bd.buffer d) = d.val := bd.residue_eq_d d
  rw [if_pos (by rw [h_res]; omega : bd.residue (bd.buffer d) ≠ 0)]
  exact h_res

theorem combinedResidue_at_scaffold {k Y q : ℕ} (bd : BufferData k Y)
    (sm : ScaffoldMatching k Y) (t : sm.T)
    (h_neq_q : sm.scaffold t ≠ q) (h_neq_buf : bd.residue (sm.scaffold t) = 0) :
    combinedResidue q bd sm (sm.scaffold t) = t.val := by
  unfold combinedResidue
  rw [if_neg h_neq_q, if_neg (by rw [h_neq_buf]; simp)]
  exact sm.residue_eq_t t

noncomputable def BufferData.total {k Y : ℕ} (bd : BufferData k Y) : ℕ → ℕ :=
  fun d => if hd : d ∈ bd.D then bd.buffer ⟨d, hd⟩ else 1

theorem BufferData.total_of_mem {k Y : ℕ} (bd : BufferData k Y)
    {d : ℕ} (hd : d ∈ bd.D) :
    bd.total d = bd.buffer ⟨d, hd⟩ := by
  unfold BufferData.total
  rw [dif_pos hd]

theorem BufferData.total_of_notMem {k Y : ℕ} (bd : BufferData k Y)
    {d : ℕ} (hd : d ∉ bd.D) :
    bd.total d = 1 := by
  unfold BufferData.total
  rw [dif_neg hd]

theorem BufferData.total_prime_of_mem {k Y : ℕ} (bd : BufferData k Y)
    {d : ℕ} (hd : d ∈ bd.D) : (bd.total d).Prime := by
  rw [bd.total_of_mem hd]
  exact bd.buffer_prime ⟨d, hd⟩

theorem BufferData.total_inj_on_D {k Y : ℕ} (bd : BufferData k Y) :
    Set.InjOn bd.total bd.D := by
  intro a ha b hb hab
  rw [bd.total_of_mem ha, bd.total_of_mem hb] at hab
  have : (⟨a, ha⟩ : bd.D) = ⟨b, hb⟩ := bd.buffer_inj hab
  exact Subtype.mk.injEq _ _ _ _ |>.mp this

theorem BufferData.total_dvd_k_of_mem {k Y : ℕ} (bd : BufferData k Y)
    {d : ℕ} (hd : d ∈ bd.D) : bd.total d ∣ k := by
  rw [bd.total_of_mem hd]
  exact bd.buffer_dvd_k ⟨d, hd⟩

theorem BufferData.total_in_range_of_mem {k Y : ℕ} (bd : BufferData k Y)
    {d : ℕ} (hd : d ∈ bd.D) : Y * Y < bd.total d ∧ bd.total d ≤ 2 * Y * Y := by
  rw [bd.total_of_mem hd]
  exact bd.buffer_in_range ⟨d, hd⟩

theorem BufferData.total_gt_Y_of_mem {k Y : ℕ} (bd : BufferData k Y) (hY : 1 ≤ Y)
    {d : ℕ} (hd : d ∈ bd.D) : Y < bd.total d := by
  have hrange := bd.total_in_range_of_mem hd
  have hYY : Y ≤ Y * Y := Nat.le_mul_of_pos_left _ hY
  omega

theorem residualSet_no_small_total
    {B k X Y q : ℕ} (bd : BufferData k Y) (hY : 1 ≤ Y)
    (hD_eq : bd.D = smallDeficientSet B Y q)
    (hb_inj : Set.InjOn bd.total bd.D) :
    ∀ t, t ∈ residualSet B X Y q bd.total → Y < t := by
  refine residualSet_no_small (B := B) (X := X) (Y := Y) (q := q) (b := bd.total)
    ?_ ?_ ?_
  · intro x hx y hy hxy
    have hx' : x ∈ bd.D := by rwa [hD_eq]
    have hy' : y ∈ bd.D := by rwa [hD_eq]
    exact hb_inj hx' hy' hxy
  · intro d hd
    have hd' : d ∈ bd.D := by rwa [hD_eq]
    exact bd.total_gt_Y_of_mem hY hd'
  · intro d hd
    have hd' : d ∈ bd.D := by rwa [hD_eq]
    exact (bd.total_prime_of_mem hd').one_lt

theorem residualSet_card_le_HX_total
    {B X Y q k : ℕ} (bd : BufferData k Y) (hq : q.Prime)
    (hD_eq : bd.D = smallDeficientSet B Y q)
    (hb_inj : Set.InjOn bd.total bd.D)
    (hb_ne_q : ∀ d ∈ smallDeficientSet B Y q, bd.total d ≠ q)
    (h_numeric :
      B * (Nat.log 2 (2 * X) + 1) *
        (Nat.log 2 (2 * X) + 1) ^ (smallDeficientSet B Y q).card
        ≤ H_X (M_B B) X) :
    (residualSet B X Y q bd.total).card ≤ H_X (M_B B) X := by
  refine residualSet_card_le_HX (B := B) (X := X) (Y := Y) (q := q) (b := bd.total)
    hq ?_ ?_ hb_ne_q h_numeric
  · intro d hd
    have hd' : d ∈ bd.D := by rwa [hD_eq]
    exact bd.total_prime_of_mem hd'
  · intro x hx y hy hxy
    have hx' : x ∈ bd.D := by rwa [hD_eq]
    have hy' : y ∈ bd.D := by rwa [hD_eq]
    exact hb_inj hx' hy' hxy

noncomputable def BufferData.empty (k Y : ℕ) : BufferData k Y where
  D := ∅
  D_subset := by simp
  buffer := fun d => absurd d.property (Finset.notMem_empty _)
  buffer_prime := fun d => absurd d.property (Finset.notMem_empty _)
  buffer_in_range := fun d => absurd d.property (Finset.notMem_empty _)
  buffer_dvd_k := fun d => absurd d.property (Finset.notMem_empty _)
  buffer_inj := fun a _ _ => absurd a.property (Finset.notMem_empty _)

noncomputable def CandidatePrimes (k Y q : ℕ) : Finset ℕ :=
  (Finset.Ioc (k - Y / 2) k).filter (fun p => p.Prime ∧ p % q = 1)

theorem CandidatePrimes_card_le_Y {k Y q : ℕ} :
    (CandidatePrimes k Y q).card ≤ Y := by
  classical
  unfold CandidatePrimes
  calc ((Finset.Ioc (k - Y / 2) k).filter (fun p => p.Prime ∧ p % q = 1)).card
      ≤ (Finset.Ioc (k - Y / 2) k).card := Finset.card_filter_le _ _
    _ = k - (k - Y / 2) := Nat.card_Ioc _ _
    _ ≤ Y := by omega

theorem CandidatePrimes_subset_filter (k Y q : ℕ) :
    CandidatePrimes k Y q ⊆
      (Finset.Ioc (k - Y / 2) k).filter (fun p => p.Prime ∧ p % q = 1) := by
  unfold CandidatePrimes; exact fun _ h => h

noncomputable def BadK (X Y W : ℕ) (U : Finset ℕ) : Finset ℕ :=
  (Finset.Icc X (2 * X)).filter
    (fun k => W ∣ k ∧ ∃ t ∈ U, k - Y < t ∧ t ≤ k)

theorem BadK_subset_biUnion (X Y W : ℕ) (U : Finset ℕ) :
    BadK X Y W U ⊆ U.biUnion (fun t =>
      (Finset.Icc t (t + Y - 1)).filter (W ∣ ·)) := by
  classical
  intro k hk
  unfold BadK at hk
  rw [Finset.mem_filter] at hk
  obtain ⟨_, hk_dvd, t, ht_in, h_lo, h_hi⟩ := hk
  rw [Finset.mem_biUnion]
  refine ⟨t, ht_in, ?_⟩
  rw [Finset.mem_filter, Finset.mem_Icc]
  refine ⟨⟨h_hi, ?_⟩, hk_dvd⟩
  by_cases hY : Y = 0
  · subst hY; omega
  · omega

theorem BadK_card_le_sum_filter (X Y W : ℕ) (U : Finset ℕ) :
    (BadK X Y W U).card ≤
      ∑ t ∈ U, ((Finset.Icc t (t + Y - 1)).filter (W ∣ ·)).card := by
  classical
  calc (BadK X Y W U).card
      ≤ (U.biUnion (fun t => (Finset.Icc t (t + Y - 1)).filter (W ∣ ·))).card :=
        Finset.card_le_card (BadK_subset_biUnion X Y W U)
    _ ≤ ∑ t ∈ U, ((Finset.Icc t (t + Y - 1)).filter (W ∣ ·)).card :=
        Finset.card_biUnion_le

theorem good_k_no_residual_in_top_window (X Y W : ℕ) (U : Finset ℕ) (k : ℕ)
    (hk_range : k ∈ Finset.Icc X (2 * X)) (hk_dvd : W ∣ k)
    (hk_not_bad : k ∉ BadK X Y W U) :
    ∀ t ∈ U, ¬ (k - Y < t ∧ t ≤ k) := by
  intro t ht_in ⟨h_lo, h_hi⟩
  apply hk_not_bad
  unfold BadK
  rw [Finset.mem_filter]
  exact ⟨hk_range, hk_dvd, t, ht_in, h_lo, h_hi⟩

theorem good_k_residual_endpoint {B X Y q W : ℕ} {b : ℕ → ℕ} (k : ℕ)
    (hk_range : k ∈ Finset.Icc X (2 * X)) (hk_dvd : W ∣ k)
    (hk_not_bad : k ∉ BadK X Y W (residualSet B X Y q b)) :
    ∀ t ∈ residualSet B X Y q b, t ≤ k → t ≤ k - Y := by
  intro t ht_in h_le_k
  by_contra h
  push_neg at h
  exact good_k_no_residual_in_top_window X Y W _ k hk_range hk_dvd hk_not_bad t ht_in
    ⟨h, h_le_k⟩

theorem residualSet_filter_le_k_subset_Ioc {B X Y q k : ℕ} {b : ℕ → ℕ}
    (hb_inj : Set.InjOn b (smallDeficientSet B Y q))
    (hb_gt_Y : ∀ d ∈ smallDeficientSet B Y q, Y < b d)
    (hb_gt_1 : ∀ d ∈ smallDeficientSet B Y q, 1 < b d)
    (h_endpoint : ∀ t, t ∈ residualSet B X Y q b → t ≤ k → t ≤ k - Y) :
    (residualSet B X Y q b).filter (fun t => t ≤ k) ⊆ Finset.Ioc Y (k - Y) := by
  intro t ht
  rw [Finset.mem_filter] at ht
  obtain ⟨h_in, h_le_k⟩ := ht
  rw [Finset.mem_Ioc]
  exact ⟨residualSet_no_small hb_inj hb_gt_Y hb_gt_1 t h_in, h_endpoint t h_in h_le_k⟩

noncomputable def BufferData.ofSubtypeMap {B Y q k : ℕ}
    (hD_subset : smallDeficientSet B Y q ⊆ Finset.Icc 1 Y)
    (b : {d // d ∈ smallDeficientSet B Y q} → ℕ)
    (hb_prime : ∀ d, (b d).Prime)
    (hb_range : ∀ d, Y * Y < b d ∧ b d ≤ 2 * Y * Y)
    (hb_dvd_k : ∀ d, b d ∣ k)
    (hb_inj : Function.Injective b) :
    BufferData k Y where
  D := smallDeficientSet B Y q
  D_subset := hD_subset
  buffer := b
  buffer_prime := hb_prime
  buffer_in_range := hb_range
  buffer_dvd_k := hb_dvd_k
  buffer_inj := hb_inj

theorem BufferData.dvd_k_of_residue_ne_zero {k Y : ℕ} (bd : BufferData k Y)
    {p : ℕ} (h : bd.residue p ≠ 0) : p ∣ k := by
  unfold BufferData.residue at h
  by_cases hEx : ∃ d : bd.D, bd.buffer d = p
  · rw [dif_pos hEx] at h
    exact hEx.choose_spec ▸ bd.buffer_dvd_k hEx.choose
  · rw [dif_neg hEx] at h
    exact False.elim (h rfl)

theorem combinedResidue_support
    {k Y q : ℕ} (bd : BufferData k Y) (sm : ScaffoldMatching k Y)
    {p : ℕ} (h : combinedResidue q bd sm p ≠ 0) :
    p = q ∨ bd.residue p ≠ 0 ∨ sm.residue p ≠ 0 := by
  unfold combinedResidue at h
  by_cases hpq : p = q
  · exact Or.inl hpq
  · rw [if_neg hpq] at h
    by_cases hb : bd.residue p ≠ 0
    · exact Or.inr (Or.inl hb)
    · rw [if_neg hb] at h
      exact Or.inr (Or.inr h)

theorem BufferData.empty_residue (k Y p : ℕ) :
    (BufferData.empty k Y).residue p = 0 := by
  unfold BufferData.residue
  rw [dif_neg]
  rintro ⟨d, _⟩
  exact absurd d.property (Finset.notMem_empty _)

structure CoverBuildData (B k : ℕ) where
  Y : ℕ
  Y_pos : 2 ≤ Y
  Y_le_half : 2 * Y ≤ k
  q : ℕ
  q_prime : q.Prime
  m_le_q : B ≤ q
  q_le_2m : q ≤ 2 * B - 2
  k_ge_4m : 4 * B + 4 ≤ k
  q_dvd_k : q ∣ k
  smq : ScaffoldMatchingQ k Y q
  scaffold_neq_q : ∀ t : smq.T, smq.scaffold t ≠ q
  covers : ∀ j, 1 ≤ j → j ≤ k →
    ∃ p, p.Prime ∧ B ≤ p ∧ p ≤ k ∧
      j % p = combinedResidue q (BufferData.empty k Y) smq.toScaffoldMatching p ∧
      (combinedResidue q (BufferData.empty k Y) smq.toScaffoldMatching p = 0 ∨
       p ≤ k / 2 ∨ j ≤ p)

noncomputable def CoverBuildData.a {B k : ℕ} (cbd : CoverBuildData B k) : ℕ → ℕ :=
  combinedResidue cbd.q (BufferData.empty k cbd.Y) cbd.smq.toScaffoldMatching

theorem CoverBuildData.a_lt_p {B k : ℕ} (cbd : CoverBuildData B k)
    (p : ℕ) (hp : p.Prime) : cbd.a p < p :=
  combinedResidue_lt_p (BufferData.empty k cbd.Y) cbd.smq.toScaffoldMatching
    cbd.q_prime.one_lt (by have := cbd.Y_pos; omega : 1 ≤ cbd.Y) p hp.pos

theorem CoverBuildData.a_bound {B k : ℕ} (cbd : CoverBuildData B k)
    (p : ℕ) (hp : p.Prime) (hBp : B ≤ p) (hpk : p < k) :
    cbd.a p < p - k % p := by
  unfold CoverBuildData.a
  by_cases h_nz : combinedResidue cbd.q (BufferData.empty k cbd.Y) cbd.smq.toScaffoldMatching p = 0
  · rw [h_nz]
    have h_mod_lt : k % p < p := Nat.mod_lt _ hp.pos
    omega
  · exact combinedResidue_a_bound (BufferData.empty k cbd.Y) cbd.smq.toScaffoldMatching
      cbd.Y_pos cbd.q_dvd_k cbd.q_prime.one_lt p h_nz

theorem CoverBuildData.non_excess {B k : ℕ} (cbd : CoverBuildData B k)
    (p : ℕ) (h_nz : cbd.a p ≠ 0) : k % p < cbd.a p :=
  combinedResidue_non_excess (BufferData.empty k cbd.Y) cbd.smq.toScaffoldMatching
    cbd.Y_pos cbd.q_dvd_k p h_nz

theorem CoverBuildData.scaffold_field {B k : ℕ} (cbd : CoverBuildData B k)
    (p : ℕ) (h_nz : cbd.a p ≠ 0) :
    p = cbd.q ∨ (k / 2 < p ∧ p ≤ k ∧ p % cbd.q = 1) := by
  unfold CoverBuildData.a combinedResidue at h_nz
  by_cases hpq : p = cbd.q
  · left; exact hpq
  · right
    rw [if_neg hpq] at h_nz
    rw [if_neg (by rw [BufferData.empty_residue]; simp)] at h_nz
    unfold ScaffoldMatching.residue at h_nz
    by_cases h_ex : ∃ t : cbd.smq.toScaffoldMatching.T,
        cbd.smq.toScaffoldMatching.scaffold t = p
    · obtain ⟨t, ht_eq⟩ := h_ex
      have h_struct := cbd.smq.scaffold_structural cbd.Y_le_half t
      rw [ht_eq] at h_struct
      exact h_struct
    · rw [dif_neg h_ex] at h_nz
      exact absurd rfl h_nz

theorem CoverBuildData.scaffold_non_excess_at_scaffold {B k : ℕ} (cbd : CoverBuildData B k)
    (p : ℕ) (hp : p.Prime) (hBp : B ≤ p) (hp_le_k : p ≤ k)
    (h_nz : cbd.a p ≠ 0) (_h_half : k / 2 < p) :
    k % p < cbd.a p := cbd.non_excess p h_nz

structure WideCoverBuildCore (B k : ℕ) where
  X : ℕ
  Y : ℕ
  Y_pos : 2 ≤ Y
  Y_le_half : 2 * Y ≤ k
  Y_sq_small : 6 * Y * Y ≤ k
  q : ℕ
  q_prime : q.Prime
  m_le_q : B ≤ q
  q_dvd_k : q ∣ k
  q_pow20_le_Y : q ^ 20 ≤ Y
  Y_lt_q_pow21 : Y < q ^ 21
  k_ge_4m : 4 * B + 4 ≤ k
  q_le_k_half : q ≤ k / 2
  bd : BufferData k Y
  smq : ScaffoldMatchingQ k Y q
  scaffold_neq_q : ∀ t : smq.T, smq.scaffold t ≠ q
  buffer_neq_q : ∀ d : bd.D, bd.buffer d ≠ q
  scaffold_neq_buffer : ∀ t : smq.T, ∀ d : bd.D, smq.scaffold t ≠ bd.buffer d
  DY_card_succ_le_HX : bd.D.card + 1 ≤ H_X (M_B B) X
  scaffold_card_le_HX : smq.T.card ≤ H_X (M_B B) X

noncomputable def WideCoverBuildCore.a {B k : ℕ} (core : WideCoverBuildCore B k) : ℕ → ℕ :=
  combinedResidue core.q core.bd core.smq.toScaffoldMatching

theorem WideCoverBuildCore.non_excess {B k : ℕ}
    (core : WideCoverBuildCore B k) (p : ℕ) (h_nz : core.a p ≠ 0) :
    k % p < core.a p :=
  combinedResidue_non_excess core.bd core.smq.toScaffoldMatching
    core.Y_pos core.q_dvd_k p h_nz

theorem WideCoverBuildCore.scaffoldExcess_empty {B k : ℕ}
    (core : WideCoverBuildCore B k) (i : ℕ) :
    ∀ p, p ∉ scaffoldExcess k core.a (k - i) := by
  classical
  intro p hp
  unfold scaffoldExcess at hp
  rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc] at hp
  obtain ⟨⟨⟨_, hpk⟩, _⟩, ha_ne_zero, hk2lt, hp_lt_j, h_mod, h_jpge⟩ := hp
  have h_ne := core.non_excess p ha_ne_zero
  have h_k_mod : k % p = k - p := by
    have h_lt : k - p < p := by omega
    have h_eq : k = (k - p) + p := by omega
    rw [h_eq, Nat.add_mod_right, Nat.mod_eq_of_lt h_lt]
    omega
  have h_ji_mod_p_lt : k - i - p < p := by omega
  rw [Nat.mod_eq_of_lt h_ji_mod_p_lt] at h_mod
  omega

structure WideCoverBuildData (B k : ℕ) where
  X : ℕ
  Y : ℕ
  Y_pos : 2 ≤ Y
  Y_le_half : 2 * Y ≤ k
  Y_sq_small : 6 * Y * Y ≤ k
  q : ℕ
  q_prime : q.Prime
  m_le_q : B ≤ q
  q_dvd_k : q ∣ k
  q_pow20_le_Y : q ^ 20 ≤ Y
  Y_lt_q_pow21 : Y < q ^ 21
  k_ge_4m : 4 * B + 4 ≤ k
  q_le_k_half : q ≤ k / 2
  bd : BufferData k Y
  smq : ScaffoldMatchingQ k Y q
  scaffold_neq_q : ∀ t : smq.T, smq.scaffold t ≠ q
  buffer_neq_q : ∀ d : bd.D, bd.buffer d ≠ q
  scaffold_neq_buffer : ∀ t : smq.T, ∀ d : bd.D, smq.scaffold t ≠ bd.buffer d
  DY_card_succ_le_HX : bd.D.card + 1 ≤ H_X (M_B B) X
  scaffold_card_le_HX : smq.T.card ≤ H_X (M_B B) X
  Z_gt_B_j :
    ∀ j : Fin k,
      outerB k
        (combinedResidue q bd smq.toScaffoldMatching) (j.val + 1)
        < Z_modulus k (combinedResidue q bd smq.toScaffoldMatching)
  a_zero_of_lt_B :
    ∀ p, p.Prime → p < B →
      combinedResidue q bd smq.toScaffoldMatching p = 0
  outerB_ge_B_i :
    ∀ i : Fin k, B ≤ outerB k
      (combinedResidue q bd smq.toScaffoldMatching) (k - i.val)

noncomputable def WideCoverBuildData.a {B k : ℕ} (wcbd : WideCoverBuildData B k) : ℕ → ℕ :=
  combinedResidue wcbd.q wcbd.bd wcbd.smq.toScaffoldMatching

noncomputable def WideCoverBuildCore.toData {B k : ℕ} (core : WideCoverBuildCore B k)
    (hZ : ∀ j : Fin k, outerB k
      (combinedResidue core.q core.bd core.smq.toScaffoldMatching) (j.val + 1)
      < Z_modulus k (combinedResidue core.q core.bd core.smq.toScaffoldMatching))
    (hzero : ∀ p, p.Prime → p < B →
      combinedResidue core.q core.bd core.smq.toScaffoldMatching p = 0)
    (hCov : ∀ i : Fin k, B ≤ outerB k
      (combinedResidue core.q core.bd core.smq.toScaffoldMatching) (k - i.val)) :
    WideCoverBuildData B k where
  X := core.X
  Y := core.Y
  Y_pos := core.Y_pos
  Y_le_half := core.Y_le_half
  Y_sq_small := core.Y_sq_small
  q := core.q
  q_prime := core.q_prime
  m_le_q := core.m_le_q
  q_dvd_k := core.q_dvd_k
  q_pow20_le_Y := core.q_pow20_le_Y
  Y_lt_q_pow21 := core.Y_lt_q_pow21
  k_ge_4m := core.k_ge_4m
  q_le_k_half := core.q_le_k_half
  bd := core.bd
  smq := core.smq
  scaffold_neq_q := core.scaffold_neq_q
  buffer_neq_q := core.buffer_neq_q
  scaffold_neq_buffer := core.scaffold_neq_buffer
  DY_card_succ_le_HX := core.DY_card_succ_le_HX
  scaffold_card_le_HX := core.scaffold_card_le_HX
  Z_gt_B_j := hZ
  a_zero_of_lt_B := hzero
  outerB_ge_B_i := hCov

theorem WideCoverBuildData.a_lt_p {B k : ℕ} (wcbd : WideCoverBuildData B k)
    (p : ℕ) (hp : p.Prime) : wcbd.a p < p :=
  combinedResidue_lt_p wcbd.bd wcbd.smq.toScaffoldMatching
    wcbd.q_prime.one_lt (by have := wcbd.Y_pos; omega : 1 ≤ wcbd.Y) p hp.pos

theorem WideCoverBuildData.a_bound {B k : ℕ} (wcbd : WideCoverBuildData B k)
    (p : ℕ) (hp : p.Prime) (hBp : B ≤ p) (hpk : p < k) :
    wcbd.a p < p - k % p := by
  unfold WideCoverBuildData.a
  by_cases h_nz : combinedResidue wcbd.q wcbd.bd wcbd.smq.toScaffoldMatching p = 0
  · rw [h_nz]
    have h_mod_lt : k % p < p := Nat.mod_lt _ hp.pos
    omega
  · exact combinedResidue_a_bound wcbd.bd wcbd.smq.toScaffoldMatching
      wcbd.Y_pos wcbd.q_dvd_k wcbd.q_prime.one_lt p h_nz

theorem WideCoverBuildData.non_excess {B k : ℕ} (wcbd : WideCoverBuildData B k)
    (p : ℕ) (h_nz : wcbd.a p ≠ 0) : k % p < wcbd.a p :=
  combinedResidue_non_excess wcbd.bd wcbd.smq.toScaffoldMatching
    wcbd.Y_pos wcbd.q_dvd_k p h_nz

theorem WideCoverBuildData.scaffold_field {B k : ℕ} (wcbd : WideCoverBuildData B k)
    (p : ℕ) (h_nz : wcbd.a p ≠ 0) :
    p ∣ k ∨ (k / 2 < p ∧ p ≤ k ∧ p % wcbd.q = 1) := by
  unfold WideCoverBuildData.a at h_nz
  rcases combinedResidue_support wcbd.bd wcbd.smq.toScaffoldMatching h_nz with hpq | hb_or_hs
  · left; rw [hpq]; exact wcbd.q_dvd_k
  · rcases hb_or_hs with hb | hs
    · left; exact wcbd.bd.dvd_k_of_residue_ne_zero hb
    · right
      unfold ScaffoldMatching.residue at hs
      by_cases h_ex : ∃ t : wcbd.smq.toScaffoldMatching.T,
          wcbd.smq.toScaffoldMatching.scaffold t = p
      · obtain ⟨t, ht_eq⟩ := h_ex
        have h_struct := wcbd.smq.scaffold_structural wcbd.Y_le_half t
        rw [ht_eq] at h_struct
        exact h_struct
      · rw [dif_neg h_ex] at hs
        exact absurd rfl hs

theorem exists_scaffoldMatchingQ_of_card_le {k Y q : ℕ} {T C : Finset ℕ}
    (hT_subset : T ⊆ Finset.Ioc Y (k - Y))
    (hC_subset : C ⊆ (Finset.Ioc (k - Y / 2) k).filter (fun p => p.Prime ∧ p % q = 1))
    (hcard : T.card ≤ C.card) :
    ∃ smq : ScaffoldMatchingQ k Y q, smq.T = T := by
  classical
  have hcard_subtype : Fintype.card {t // t ∈ T} ≤ Fintype.card {p // p ∈ C} := by
    simpa using hcard
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard_subtype
  refine ⟨{
    T := T
    T_subset := hT_subset
    scaffold := fun t => (e t).val
    scaffold_prime := ?_
    scaffold_in_range := ?_
    scaffold_inj := ?_
    scaffold_mod_q := ?_
  }, rfl⟩
  · intro t
    have h_in : (e t).val ∈ (Finset.Ioc (k - Y / 2) k).filter (fun p => p.Prime ∧ p % q = 1) :=
      hC_subset (e t).property
    rw [Finset.mem_filter] at h_in
    exact h_in.2.1
  · intro t
    have h_in : (e t).val ∈ (Finset.Ioc (k - Y / 2) k).filter (fun p => p.Prime ∧ p % q = 1) :=
      hC_subset (e t).property
    rw [Finset.mem_filter, Finset.mem_Ioc] at h_in
    exact h_in.1
  · intro x y hxy
    have heq : e x = e y := Subtype.ext hxy
    exact e.injective heq
  · intro t
    have h_in : (e t).val ∈ (Finset.Ioc (k - Y / 2) k).filter (fun p => p.Prime ∧ p % q = 1) :=
      hC_subset (e t).property
    rw [Finset.mem_filter] at h_in
    exact h_in.2.2

theorem exists_buffer_primes {B Y q : ℕ}
    (h_many :
      (smallDeficientSet B Y q).card
        ≤ ((Finset.Ioc (Y * Y) (2 * Y * Y)).filter Nat.Prime).card) :
    ∃ b : {d // d ∈ smallDeficientSet B Y q} → ℕ,
      Function.Injective b ∧
      (∀ d, (b d).Prime) ∧
      (∀ d, Y * Y < b d ∧ b d ≤ 2 * Y * Y) := by
  classical
  let D := smallDeficientSet B Y q
  let C := (Finset.Ioc (Y * Y) (2 * Y * Y)).filter Nat.Prime
  have hcard : Fintype.card {d // d ∈ D} ≤ Fintype.card {p // p ∈ C} := by
    simpa using h_many
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
  refine ⟨fun d => (e d).val, ?_, ?_, ?_⟩
  · intro x y hxy
    have heq : e x = e y := Subtype.ext hxy
    exact e.injective heq
  · intro d
    have h_in : (e d).val ∈ (Finset.Ioc (Y * Y) (2 * Y * Y)).filter Nat.Prime :=
      (e d).property
    rw [Finset.mem_filter] at h_in
    exact h_in.2
  · intro d
    have h_in : (e d).val ∈ (Finset.Ioc (Y * Y) (2 * Y * Y)).filter Nat.Prime :=
      (e d).property
    rw [Finset.mem_filter, Finset.mem_Ioc] at h_in
    exact h_in.1

noncomputable def WideCoverBuildCore.bufferImage {B k : ℕ}
    (core : WideCoverBuildCore B k) : Finset ℕ :=
  core.bd.D.attach.image core.bd.buffer

noncomputable def WideCoverBuildCore.scaffoldImage {B k : ℕ}
    (core : WideCoverBuildCore B k) : Finset ℕ :=
  core.smq.toScaffoldMatching.T.attach.image core.smq.toScaffoldMatching.scaffold

noncomputable def WideCoverBuildData.bufferImage {B k : ℕ}
    (wcbd : WideCoverBuildData B k) : Finset ℕ :=
  wcbd.bd.D.attach.image wcbd.bd.buffer

noncomputable def WideCoverBuildData.scaffoldImage {B k : ℕ}
    (wcbd : WideCoverBuildData B k) : Finset ℕ :=
  wcbd.smq.T.attach.image wcbd.smq.scaffold

theorem WideCoverBuildCore.struct_split {B k : ℕ} (core : WideCoverBuildCore B k)
    (p : ℕ) (_hp : p.Prime) (_hp_pos : 1 ≤ p) (_hpk : p ≤ k) (h_nz : core.a p ≠ 0) :
    p = core.q ∨ p ∈ core.bufferImage ∨ p ∈ core.scaffoldImage := by
  unfold WideCoverBuildCore.a at h_nz
  rcases combinedResidue_support core.bd core.smq.toScaffoldMatching h_nz with hpq | hb_or_hs
  · exact Or.inl hpq
  · rcases hb_or_hs with hb | hs
    · right; left
      unfold BufferData.residue at hb
      by_cases hEx : ∃ d : core.bd.D, core.bd.buffer d = p
      · obtain ⟨d, hd⟩ := hEx
        unfold WideCoverBuildCore.bufferImage
        exact Finset.mem_image.mpr ⟨d, Finset.mem_attach _ _, hd⟩
      · rw [dif_neg hEx] at hb
        exact absurd rfl hb
    · right; right
      unfold ScaffoldMatching.residue at hs
      by_cases hEx : ∃ t : core.smq.toScaffoldMatching.T,
          core.smq.toScaffoldMatching.scaffold t = p
      · obtain ⟨t, ht⟩ := hEx
        unfold WideCoverBuildCore.scaffoldImage
        exact Finset.mem_image.mpr ⟨t, Finset.mem_attach _ _, ht⟩
      · rw [dif_neg hEx] at hs
        exact absurd rfl hs

theorem WideCoverBuildCore.P_plus_card_le {B k : ℕ} (core : WideCoverBuildCore B k) :
    (P_plus k core.a).card ≤ 1 + core.bufferImage.card + core.scaffoldImage.card :=
  P_plus_card_le_of_structure core.a core.bufferImage core.scaffoldImage core.struct_split

theorem WideCoverBuildCore.bufferImage_card_le {B k : ℕ} (core : WideCoverBuildCore B k) :
    core.bufferImage.card ≤ core.bd.D.card := by
  unfold WideCoverBuildCore.bufferImage
  exact (Finset.card_image_le).trans_eq core.bd.D.card_attach

theorem WideCoverBuildCore.scaffoldImage_card_le {B k : ℕ} (core : WideCoverBuildCore B k) :
    core.scaffoldImage.card ≤ core.smq.T.card := by
  unfold WideCoverBuildCore.scaffoldImage
  exact (Finset.card_image_le).trans_eq core.smq.T.card_attach

theorem WideCoverBuildCore.P_plus_card_le_two_HX {B k : ℕ} (core : WideCoverBuildCore B k) :
    (P_plus k core.a).card ≤ 2 * H_X (M_B B) core.X := by
  have h1 := core.P_plus_card_le
  have h_buf := core.bufferImage_card_le
  have h_scaf := core.scaffoldImage_card_le
  have h_DY := core.DY_card_succ_le_HX
  have h_smq := core.scaffold_card_le_HX
  omega

theorem WideCoverBuildData.struct_split {B k : ℕ} (wcbd : WideCoverBuildData B k)
    (p : ℕ) (_hp : p.Prime) (_hp_pos : 1 ≤ p) (_hpk : p ≤ k) (h_nz : wcbd.a p ≠ 0) :
    p = wcbd.q ∨ p ∈ wcbd.bufferImage ∨ p ∈ wcbd.scaffoldImage := by
  unfold WideCoverBuildData.a at h_nz
  rcases combinedResidue_support wcbd.bd wcbd.smq.toScaffoldMatching h_nz with hpq | hb_or_hs
  · exact Or.inl hpq
  · rcases hb_or_hs with hb | hs
    · right; left
      unfold BufferData.residue at hb
      by_cases hEx : ∃ d : wcbd.bd.D, wcbd.bd.buffer d = p
      · obtain ⟨d, hd⟩ := hEx
        unfold WideCoverBuildData.bufferImage
        exact Finset.mem_image.mpr ⟨d, Finset.mem_attach _ _, hd⟩
      · rw [dif_neg hEx] at hb
        exact absurd rfl hb
    · right; right
      unfold ScaffoldMatching.residue at hs
      by_cases hEx : ∃ t : wcbd.smq.toScaffoldMatching.T,
          wcbd.smq.toScaffoldMatching.scaffold t = p
      · obtain ⟨t, ht⟩ := hEx
        unfold WideCoverBuildData.scaffoldImage
        exact Finset.mem_image.mpr ⟨t, Finset.mem_attach _ _, ht⟩
      · rw [dif_neg hEx] at hs
        exact absurd rfl hs

theorem WideCoverBuildData.P_plus_card_le {B k : ℕ} (wcbd : WideCoverBuildData B k) :
    (P_plus k wcbd.a).card ≤ 1 + wcbd.bufferImage.card + wcbd.scaffoldImage.card :=
  P_plus_card_le_of_structure wcbd.a wcbd.bufferImage wcbd.scaffoldImage
    wcbd.struct_split

theorem WideCoverBuildData.bufferImage_card_le {B k : ℕ} (wcbd : WideCoverBuildData B k) :
    wcbd.bufferImage.card ≤ wcbd.bd.D.card := by
  unfold WideCoverBuildData.bufferImage
  exact (Finset.card_image_le).trans_eq wcbd.bd.D.card_attach

theorem WideCoverBuildData.scaffoldImage_card_le {B k : ℕ} (wcbd : WideCoverBuildData B k) :
    wcbd.scaffoldImage.card ≤ wcbd.smq.T.card := by
  unfold WideCoverBuildData.scaffoldImage
  exact (Finset.card_image_le).trans_eq wcbd.smq.T.card_attach

theorem WideCoverBuildData.P_plus_card_le_two_HX {B k : ℕ} (wcbd : WideCoverBuildData B k) :
    (P_plus k wcbd.a).card ≤ 2 * H_X (M_B B) wcbd.X := by
  have h1 := wcbd.P_plus_card_le
  have h_buf := wcbd.bufferImage_card_le
  have h_scaf := wcbd.scaffoldImage_card_le
  have h_DY : wcbd.bd.D.card + 1 ≤ H_X (M_B B) wcbd.X := wcbd.DY_card_succ_le_HX
  have h_smq : wcbd.smq.T.card ≤ H_X (M_B B) wcbd.X := wcbd.scaffold_card_le_HX
  omega

noncomputable def WideCoverBuildData.toWide {B k : ℕ} (wcbd : WideCoverBuildData B k) :
    WideCoverData B k where
  a := wcbd.a
  q := wcbd.q
  q_prime := wcbd.q_prime
  B_le_q := wcbd.m_le_q
  q_le_k_half := wcbd.q_le_k_half
  k_ge_4m := wcbd.k_ge_4m
  q_dvd_k := wcbd.q_dvd_k
  a_lt_p := wcbd.a_lt_p
  a_bound := wcbd.a_bound
  a_zero_of_lt_B := wcbd.a_zero_of_lt_B
  scaffold := fun p _ h_nz => wcbd.scaffold_field p h_nz

theorem WideCoverBuildData.q_lt_Y_sq {B k : ℕ} (wcbd : WideCoverBuildData B k) :
    wcbd.q < wcbd.Y * wcbd.Y := by
  have h_q_pow20 := wcbd.q_pow20_le_Y
  have h_q_ge_2 : 2 ≤ wcbd.q := wcbd.q_prime.two_le
  have h_Y_ge_2 : 2 ≤ wcbd.Y := wcbd.Y_pos
  by_contra h
  push_neg at h
  have h_q_pow20_ge : wcbd.q ^ 20 ≥ (wcbd.Y * wcbd.Y) ^ 20 := Nat.pow_le_pow_left h 20
  have h_Y_sq_pow_lower : (wcbd.Y * wcbd.Y) ^ 20 ≥ wcbd.Y * wcbd.Y * wcbd.Y := by
    have h1 : (wcbd.Y * wcbd.Y) ^ 20 ≥ (wcbd.Y * wcbd.Y) ^ 2 :=
      Nat.pow_le_pow_right (by nlinarith) (by omega)
    nlinarith [h1]
  nlinarith [h_q_pow20]

theorem WideCoverBuildData.prime_in_third_to_half_zero_wide {B k : ℕ}
    (wcbd : WideCoverBuildData B k) {p : ℕ}
    (hp : p.Prime) (hlo : k / 3 < p) (hhi : p ≤ k / 2) :
    wcbd.a p = 0 := by
  by_contra h_nz
  have hpk : p ≤ k := by
    have hk_div_2_le : k / 2 ≤ k := Nat.div_le_self k 2
    omega
  rcases wcbd.struct_split p hp hp.one_lt.le hpk h_nz with hpq | hb_or_hs
  · rw [hpq] at hlo
    have h_q_lt : wcbd.q < k / 3 := by
      have h_q_lt_Y_sq : wcbd.q < wcbd.Y * wcbd.Y := wcbd.q_lt_Y_sq
      have h_Y_sq : 6 * wcbd.Y * wcbd.Y ≤ k := wcbd.Y_sq_small
      have h_Y_pos : 2 ≤ wcbd.Y := wcbd.Y_pos
      have h_div_bound : 2 * wcbd.Y * wcbd.Y ≤ k / 3 := by
        rw [Nat.le_div_iff_mul_le (by norm_num)]; linarith
      nlinarith
    omega
  · rcases hb_or_hs with hb | hs
    · unfold WideCoverBuildData.bufferImage at hb
      rw [Finset.mem_image] at hb
      obtain ⟨d, _, hd_eq⟩ := hb
      have h_buf_range := (wcbd.bd.buffer_in_range d).2
      have h_Y_sq := wcbd.Y_sq_small
      have h_div_bound : 2 * wcbd.Y * wcbd.Y ≤ k / 3 := by
        rw [Nat.le_div_iff_mul_le (by norm_num)]; linarith
      have h_buf_le_k_third : wcbd.bd.buffer d ≤ k / 3 := by omega
      rw [hd_eq] at h_buf_le_k_third
      omega
    · unfold WideCoverBuildData.scaffoldImage at hs
      rw [Finset.mem_image] at hs
      obtain ⟨t, _, ht_eq⟩ := hs
      have h_scaf := (wcbd.smq.toScaffoldMatching.scaffold_in_range t).1
      have h_Y_le_half : 2 * wcbd.Y ≤ k := wcbd.Y_le_half
      have h_Y_pos : 2 ≤ wcbd.Y := wcbd.Y_pos
      rw [ht_eq] at h_scaf
      omega

theorem WideCoverBuildData.Z_ge_third_half_square_product {B k : ℕ}
    (wcbd : WideCoverBuildData B k) (hk_ge : 10 ≤ k) :
    ∏ p ∈ (Finset.Ioc (k / 3) (k / 2)).filter Nat.Prime, p ^ 2 ≤ Z_modulus k wcbd.a := by
  set S := (Finset.Ioc (k / 3) (k / 2)).filter Nat.Prime
  have hS_sub : S ⊆ (Finset.Icc 1 k).filter (fun p => p.Prime ∧ wcbd.a p = 0) := by
    intro p hp_in
    rw [Finset.mem_filter, Finset.mem_Ioc] at hp_in
    obtain ⟨⟨hlo, hhi⟩, hp_prime⟩ := hp_in
    have hpk : p ≤ k := by
      have hk_div_2_le : k / 2 ≤ k := Nat.div_le_self k 2
      omega
    have h_az : wcbd.a p = 0 := wcbd.prime_in_third_to_half_zero_wide hp_prime hlo hhi
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hp_prime.one_lt.le, hpk⟩, hp_prime, h_az⟩
  have h_pow_le : ∀ p ∈ S, p ^ 2 ≤ p ^ (Nat.log p k + 1) := by
    intro p hp_in
    rw [Finset.mem_filter, Finset.mem_Ioc] at hp_in
    obtain ⟨⟨hlo, hhi⟩, hp_prime⟩ := hp_in
    have h_log : Nat.log p k = 1 :=
      prime_in_third_to_half_log_one hp_prime.one_lt hk_ge ⟨hlo, hhi⟩
    rw [h_log]
  exact Z_modulus_ge_prod_subset wcbd.a S hS_sub h_pow_le

noncomputable def ThirdHalfPrimes (k : ℕ) : Finset ℕ :=
  (Finset.Ioc (k / 3) (k / 2)).filter Nat.Prime

theorem third_half_prime_sq_gt_k {k p : ℕ} (hk10 : 10 ≤ k)
    (hp_in : p ∈ ThirdHalfPrimes k) : k < p ^ 2 := by
  unfold ThirdHalfPrimes at hp_in
  rw [Finset.mem_filter, Finset.mem_Ioc] at hp_in
  obtain ⟨⟨hlo, _⟩, _⟩ := hp_in
  have h3 : k ≤ 3 * (k / 3) + 2 := by omega
  have h_sq : p ^ 2 = p * p := by ring
  rw [h_sq]
  nlinarith

theorem third_half_square_product_dominates_of_count {B k : ℕ}
    (hk10 : 10 ≤ k)
    (hcount : 2 * H_X (M_B B) k + 1 < (ThirdHalfPrimes k).card) :
    k ^ (2 * H_X (M_B B) k + 1) < ∏ p ∈ ThirdHalfPrimes k, p ^ 2 := by
  set E := 2 * H_X (M_B B) k + 1
  set S := ThirdHalfPrimes k
  have h_kp1_le_psq : ∀ p ∈ S, k + 1 ≤ p ^ 2 := by
    intro p hp_in
    have := third_half_prime_sq_gt_k hk10 hp_in
    omega
  have h_prod_lower : (k + 1) ^ S.card ≤ ∏ p ∈ S, p ^ 2 := by
    have : ∏ _p ∈ S, (k + 1) ≤ ∏ p ∈ S, p ^ 2 :=
      Finset.prod_le_prod (fun _ _ => Nat.zero_le _) h_kp1_le_psq
    simpa [Finset.prod_const, mul_comm] using this
  have h_k_lt_kp1 : k < k + 1 := Nat.lt_succ_self k
  have h1 : k ^ E < (k + 1) ^ E := Nat.pow_lt_pow_left h_k_lt_kp1 (by omega : E ≠ 0)
  have h2 : (k + 1) ^ E ≤ (k + 1) ^ S.card :=
    Nat.pow_le_pow_right (by omega : 1 ≤ k + 1) hcount.le
  exact lt_of_lt_of_le h1 (h2.trans h_prod_lower)

theorem WideCoverBuildData.scaffold_gt_q_at {B k : ℕ} (wcbd : WideCoverBuildData B k)
    (t : wcbd.smq.toScaffoldMatching.T) :
    wcbd.q < wcbd.smq.toScaffoldMatching.scaffold t := by
  have h_scaf := (wcbd.smq.toScaffoldMatching.scaffold_in_range t).1
  have h_Y_le := wcbd.Y_le_half
  have h_Y_pos := wcbd.Y_pos
  have h_q_lt_Y_sq := wcbd.q_lt_Y_sq
  have h_Y_sq := wcbd.Y_sq_small
  have h_Y2_le : 2 * (wcbd.Y * wcbd.Y) ≤ k / 3 := by
    rw [Nat.le_div_iff_mul_le (by norm_num)]; nlinarith
  have h_q_lt_k_third : wcbd.q < k / 3 := by nlinarith
  omega

theorem WideCoverBuildData.scaffold_gt_buffer_at {B k : ℕ}
    (wcbd : WideCoverBuildData B k)
    (t : wcbd.smq.toScaffoldMatching.T) (d : wcbd.bd.D) :
    wcbd.bd.buffer d < wcbd.smq.toScaffoldMatching.scaffold t := by
  have h_scaf := (wcbd.smq.toScaffoldMatching.scaffold_in_range t).1
  have h_buf := (wcbd.bd.buffer_in_range d).2
  have h_Y_le := wcbd.Y_le_half
  have h_Y_pos := wcbd.Y_pos
  have h_Y_sq := wcbd.Y_sq_small
  have h_Y2_le : 2 * (wcbd.Y * wcbd.Y) ≤ k / 3 := by
    rw [Nat.le_div_iff_mul_le (by norm_num)]; nlinarith
  have h_buf_le_k_third : wcbd.bd.buffer d ≤ k / 3 := by nlinarith
  omega

theorem WideCoverBuildData.buffer_gt_q_at {B k : ℕ} (wcbd : WideCoverBuildData B k)
    (d : wcbd.bd.D) : wcbd.q < wcbd.bd.buffer d := by
  have h_buf := (wcbd.bd.buffer_in_range d).1
  have h_q_lt_Y_sq := wcbd.q_lt_Y_sq
  omega

theorem WideCoverBuildData.B_le_Y_sq {B k : ℕ} (wcbd : WideCoverBuildData B k) :
    B ≤ wcbd.Y * wcbd.Y := by
  have h_q_lt := wcbd.q_lt_Y_sq
  have h_B_le := wcbd.m_le_q
  omega

theorem WideCoverBuildData.B_lt_k_half {B k : ℕ} (wcbd : WideCoverBuildData B k) :
    B < k / 2 := by
  have h_k_ge := wcbd.k_ge_4m
  omega

theorem outerB_le_innerB {k : ℕ} (a : ℕ → ℕ) (j : ℕ) :
    outerB k a j ≤
      innerB k a j :=
  Nat.le_of_dvd (innerB_pos k a j)
    (outerB_dvd_innerB k a j)

theorem innerB_split {k : ℕ} (a : ℕ → ℕ) (j : ℕ) :
    innerB k a j =
      (∏ p ∈ ((Finset.Icc 1 k).filter Nat.Prime).filter (fun p => a p ≠ 0),
        p ^ exponent k a j p) *
      (∏ p ∈ ((Finset.Icc 1 k).filter Nat.Prime).filter (fun p => a p = 0),
        p ^ exponent k a j p) := by
  classical
  unfold innerB
  rw [← Finset.prod_filter_mul_prod_filter_not
    ((Finset.Icc 1 k).filter Nat.Prime) (fun p => a p ≠ 0)
    (fun p => p ^ exponent k a j p)]
  have h_filter_eq : ((Finset.Icc 1 k).filter Nat.Prime).filter
      (fun p => ¬ a p ≠ 0) =
      ((Finset.Icc 1 k).filter Nat.Prime).filter (fun p => a p = 0) := by
    ext p; simp
  rw [h_filter_eq]

theorem innerB_zero_part_le_j {k : ℕ} (a : ℕ → ℕ) (j : ℕ) (hj_pos : 0 < j) :
    ∏ p ∈ ((Finset.Icc 1 k).filter Nat.Prime).filter (fun p => a p = 0),
      p ^ exponent k a j p ≤ j := by
  set S := ((Finset.Icc 1 k).filter Nat.Prime).filter (fun p => a p = 0)
  have h_eq : ∏ p ∈ S, p ^ exponent k a j p =
      ∏ p ∈ S, p ^ padicValNat p j := by
    apply Finset.prod_congr rfl
    intro p hp_in
    rw [Finset.mem_filter] at hp_in
    unfold exponent
    rw [if_pos hp_in.2]
  rw [h_eq]
  have h_dvd_each : ∀ p ∈ S, p ^ padicValNat p j ∣ j :=
    fun _ _ => pow_padicValNat_dvd
  have h_pairwise : (S : Set ℕ).Pairwise (Function.onFun IsRelPrime
      (fun p => p ^ padicValNat p j)) := by
    intro p hp q hq hpq
    simp only [Function.onFun]
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_filter] at hp hq
    have hc : Nat.Coprime p q := (Nat.coprime_primes hp.1.2 hq.1.2).mpr hpq
    exact Nat.coprime_iff_isRelPrime.mp (hc.pow _ _)
  exact Nat.le_of_dvd hj_pos (Finset.prod_dvd_of_isRelPrime h_pairwise h_dvd_each)

theorem WideCoverBuildData.outerB_le_k_pow_two_HX_succ {B k : ℕ}
    (wcbd : WideCoverBuildData B k) (j : Fin k) :
    outerB k wcbd.a (j.val + 1) ≤
      k ^ (2 * H_X (M_B B) wcbd.X + 1) := by
  have hj_pos : 0 < j.val + 1 := Nat.succ_pos _
  have hjk : j.val + 1 ≤ k := j.isLt
  have hk_pos : 0 < k := by linarith
  have h_outerB_le_inner : outerB k wcbd.a (j.val + 1) ≤
      innerB k wcbd.a (j.val + 1) :=
    outerB_le_innerB wcbd.a (j.val + 1)
  have h_split := innerB_split (k := k) wcbd.a (j.val + 1)
  set Z := ((Finset.Icc 1 k).filter Nat.Prime).filter (fun p => wcbd.a p = 0)
  have hP_plus_eq : P_plus k wcbd.a =
      ((Finset.Icc 1 k).filter Nat.Prime).filter (fun p => wcbd.a p ≠ 0) := by
    unfold P_plus
    ext p; simp [Finset.mem_filter]; tauto
  have h_e_le : ∀ p ∈ P_plus k wcbd.a,
      p ^ exponent k wcbd.a (j.val + 1) p ≤ k := by
    intro p hp_in
    unfold P_plus at hp_in
    rw [Finset.mem_filter, Finset.mem_Icc] at hp_in
    obtain ⟨⟨_, hpk⟩, hp_prime, _⟩ := hp_in
    have h_exp := exponent_le_alphaP_general
      k wcbd.a (j.val + 1) p hp_prime hpk hj_pos hjk
    calc p ^ exponent k wcbd.a (j.val + 1) p
        ≤ p ^ alphaP k p :=
          Nat.pow_le_pow_right hp_prime.one_lt.le h_exp
      _ ≤ k := Nat.pow_log_le_self p hk_pos.ne'
  have h_nz_le : (∏ p ∈ P_plus k wcbd.a,
      p ^ exponent k wcbd.a (j.val + 1) p) ≤
      k ^ (2 * H_X (M_B B) wcbd.X) :=
    (B_j_le_k_pow_P_plus_card wcbd.a _ h_e_le).trans
      (Nat.pow_le_pow_right (by omega) wcbd.P_plus_card_le_two_HX)
  have h_z_le_k : ∏ p ∈ Z,
      p ^ exponent k wcbd.a (j.val + 1) p ≤ k :=
    (innerB_zero_part_le_j wcbd.a (j.val + 1) hj_pos).trans hjk
  rw [← hP_plus_eq] at h_split
  have h_inner_le : innerB k wcbd.a (j.val + 1) ≤
      k ^ (2 * H_X (M_B B) wcbd.X) * k := by
    rw [h_split]; exact Nat.mul_le_mul h_nz_le h_z_le_k
  calc outerB k wcbd.a (j.val + 1)
      ≤ innerB k wcbd.a (j.val + 1) := h_outerB_le_inner
    _ ≤ k ^ (2 * H_X (M_B B) wcbd.X) * k := h_inner_le
    _ = k ^ (2 * H_X (M_B B) wcbd.X + 1) := by rw [pow_succ]

theorem WideCoverBuildCore.outerB_le_k_pow_two_HX_succ {B k : ℕ}
    (core : WideCoverBuildCore B k) (j : Fin k) :
    outerB k core.a (j.val + 1) ≤
      k ^ (2 * H_X (M_B B) core.X + 1) := by
  have hj_pos : 0 < j.val + 1 := Nat.succ_pos _
  have hjk : j.val + 1 ≤ k := j.isLt
  have hk_pos : 0 < k := by have := core.k_ge_4m; linarith
  have h_outerB_le_inner :=
    outerB_le_innerB (k := k) core.a (j.val + 1)
  have h_split := innerB_split (k := k) core.a (j.val + 1)
  set Z := ((Finset.Icc 1 k).filter Nat.Prime).filter (fun p => core.a p = 0)
  have hP_plus_eq : P_plus k core.a =
      ((Finset.Icc 1 k).filter Nat.Prime).filter (fun p => core.a p ≠ 0) := by
    unfold P_plus
    ext p; simp [Finset.mem_filter]; tauto
  have h_e_le : ∀ p ∈ P_plus k core.a,
      p ^ exponent k core.a (j.val + 1) p ≤ k := by
    intro p hp_in
    unfold P_plus at hp_in
    rw [Finset.mem_filter, Finset.mem_Icc] at hp_in
    obtain ⟨⟨_, hpk⟩, hp_prime, _⟩ := hp_in
    have h_exp := exponent_le_alphaP_general
      k core.a (j.val + 1) p hp_prime hpk hj_pos hjk
    calc p ^ exponent k core.a (j.val + 1) p
        ≤ p ^ alphaP k p :=
          Nat.pow_le_pow_right hp_prime.one_lt.le h_exp
      _ ≤ k := Nat.pow_log_le_self p hk_pos.ne'
  have h_nz_le : (∏ p ∈ P_plus k core.a,
      p ^ exponent k core.a (j.val + 1) p) ≤
      k ^ (2 * H_X (M_B B) core.X) :=
    (B_j_le_k_pow_P_plus_card core.a _ h_e_le).trans
      (Nat.pow_le_pow_right (by omega) core.P_plus_card_le_two_HX)
  have h_z_le_k : ∏ p ∈ Z,
      p ^ exponent k core.a (j.val + 1) p ≤ k :=
    (innerB_zero_part_le_j core.a (j.val + 1) hj_pos).trans hjk
  rw [← hP_plus_eq] at h_split
  have h_inner_le : innerB k core.a (j.val + 1) ≤
      k ^ (2 * H_X (M_B B) core.X) * k := by
    rw [h_split]; exact Nat.mul_le_mul h_nz_le h_z_le_k
  calc outerB k core.a (j.val + 1)
      ≤ innerB k core.a (j.val + 1) := h_outerB_le_inner
    _ ≤ k ^ (2 * H_X (M_B B) core.X) * k := h_inner_le
    _ = k ^ (2 * H_X (M_B B) core.X + 1) := by rw [pow_succ]

theorem WideCoverBuildCore.q_lt_Y_sq {B k : ℕ} (core : WideCoverBuildCore B k) :
    core.q < core.Y * core.Y := by
  have h_q_pow20 := core.q_pow20_le_Y
  have h_q_ge_2 : 2 ≤ core.q := core.q_prime.two_le
  have h_Y_ge_2 : 2 ≤ core.Y := core.Y_pos
  by_contra h
  push_neg at h
  have h_q_pow20_ge : core.q ^ 20 ≥ (core.Y * core.Y) ^ 20 := Nat.pow_le_pow_left h 20
  have h_Y_sq_pow_lower : (core.Y * core.Y) ^ 20 ≥ core.Y * core.Y * core.Y := by
    have h1 : (core.Y * core.Y) ^ 20 ≥ (core.Y * core.Y) ^ 2 :=
      Nat.pow_le_pow_right (by nlinarith) (by omega)
    nlinarith [h1]
  nlinarith [h_q_pow20]

theorem WideCoverBuildCore.prime_in_third_to_half_zero {B k : ℕ}
    (core : WideCoverBuildCore B k) {p : ℕ}
    (hp : p.Prime) (hlo : k / 3 < p) (hhi : p ≤ k / 2) :
    core.a p = 0 := by
  by_contra h_nz
  have hpk : p ≤ k := by
    have hk_div_2_le : k / 2 ≤ k := Nat.div_le_self k 2
    omega
  rcases core.struct_split p hp hp.one_lt.le hpk h_nz with hpq | hb_or_hs
  · rw [hpq] at hlo
    have h_q_lt : core.q < k / 3 := by
      have h_q_lt_Y_sq : core.q < core.Y * core.Y := core.q_lt_Y_sq
      have h_Y_sq : 6 * core.Y * core.Y ≤ k := core.Y_sq_small
      have h_Y_pos : 2 ≤ core.Y := core.Y_pos
      have h_div_bound : 2 * core.Y * core.Y ≤ k / 3 := by
        rw [Nat.le_div_iff_mul_le (by norm_num)]; nlinarith
      nlinarith
    omega
  · rcases hb_or_hs with hb | hs
    · unfold WideCoverBuildCore.bufferImage at hb
      rw [Finset.mem_image] at hb
      obtain ⟨d, _, hd_eq⟩ := hb
      have h_buf_range := (core.bd.buffer_in_range d).2
      have h_Y_sq := core.Y_sq_small
      have h_div_bound : 2 * core.Y * core.Y ≤ k / 3 := by
        rw [Nat.le_div_iff_mul_le (by norm_num)]; nlinarith
      have h_buf_le_k_third : core.bd.buffer d ≤ k / 3 := by omega
      rw [hd_eq] at h_buf_le_k_third
      omega
    · unfold WideCoverBuildCore.scaffoldImage at hs
      rw [Finset.mem_image] at hs
      obtain ⟨t, _, ht_eq⟩ := hs
      have h_scaf := (core.smq.toScaffoldMatching.scaffold_in_range t).1
      have h_Y_le_half : 2 * core.Y ≤ k := core.Y_le_half
      have h_Y_pos : 2 ≤ core.Y := core.Y_pos
      rw [ht_eq] at h_scaf
      omega

theorem WideCoverBuildCore.Z_ge_third_half_square_product {B k : ℕ}
    (core : WideCoverBuildCore B k) (hk_ge : 10 ≤ k) :
    ∏ p ∈ (Finset.Ioc (k / 3) (k / 2)).filter Nat.Prime, p ^ 2 ≤ Z_modulus k core.a := by
  set S := (Finset.Ioc (k / 3) (k / 2)).filter Nat.Prime
  have hS_sub : S ⊆ (Finset.Icc 1 k).filter (fun p => p.Prime ∧ core.a p = 0) := by
    intro p hp_in
    rw [Finset.mem_filter, Finset.mem_Ioc] at hp_in
    obtain ⟨⟨hlo, hhi⟩, hp_prime⟩ := hp_in
    have hpk : p ≤ k := by
      have hk_div_2_le : k / 2 ≤ k := Nat.div_le_self k 2
      omega
    have h_az : core.a p = 0 := core.prime_in_third_to_half_zero hp_prime hlo hhi
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hp_prime.one_lt.le, hpk⟩, hp_prime, h_az⟩
  have h_pow_le : ∀ p ∈ S, p ^ 2 ≤ p ^ (Nat.log p k + 1) := by
    intro p hp_in
    rw [Finset.mem_filter, Finset.mem_Ioc] at hp_in
    obtain ⟨⟨hlo, hhi⟩, hp_prime⟩ := hp_in
    have h_log : Nat.log p k = 1 :=
      prime_in_third_to_half_log_one hp_prime.one_lt hk_ge ⟨hlo, hhi⟩
    rw [h_log]
  exact Z_modulus_ge_prod_subset core.a S hS_sub h_pow_le

theorem WideCoverBuildCore.Z_gt_B_j_from_dominance {B k : ℕ}
    (core : WideCoverBuildCore B k) (hk_ge : 10 ≤ k)
    (h_dom : k ^ (2 * H_X (M_B B) core.X + 1) <
      ∏ p ∈ (Finset.Ioc (k / 3) (k / 2)).filter Nat.Prime, p ^ 2) :
    ∀ j : Fin k, outerB k core.a (j.val + 1) <
      Z_modulus k core.a := by
  intro j
  have h_outerB_le := core.outerB_le_k_pow_two_HX_succ j
  have h_Z_ge := core.Z_ge_third_half_square_product hk_ge
  exact lt_of_le_of_lt h_outerB_le (lt_of_lt_of_le h_dom h_Z_ge)

theorem WideCoverBuildData.Z_gt_B_j_from_dominance {B k : ℕ}
    (wcbd : WideCoverBuildData B k) (hk_ge : 10 ≤ k)
    (h_outerB_le : ∀ j : Fin k,
      outerB k wcbd.a (j.val + 1) ≤
        k ^ (2 * H_X (M_B B) wcbd.X + 1))
    (h_dom : k ^ (2 * H_X (M_B B) wcbd.X + 1) <
      ∏ p ∈ (Finset.Ioc (k / 3) (k / 2)).filter Nat.Prime, p ^ 2) :
    ∀ j : Fin k, outerB k wcbd.a (j.val + 1) <
      Z_modulus k wcbd.a := by
  intro j
  have h_Z := wcbd.Z_ge_third_half_square_product hk_ge
  have h_chain := lt_of_le_of_lt (h_outerB_le j) h_dom
  exact lt_of_lt_of_le h_chain h_Z

theorem WideCoverBuildData.Z_gt_B_j_from_pnt {B k : ℕ}
    (wcbd : WideCoverBuildData B k) (hk_ge : 10 ≤ k)
    (h_dom : k ^ (2 * H_X (M_B B) wcbd.X + 1) <
      ∏ p ∈ (Finset.Ioc (k / 3) (k / 2)).filter Nat.Prime, p ^ 2) :
    ∀ j : Fin k, outerB k wcbd.a (j.val + 1) <
      Z_modulus k wcbd.a := by
  intro j
  have h_outerB_le := wcbd.outerB_le_k_pow_two_HX_succ j
  have h_Z_ge := wcbd.Z_ge_third_half_square_product hk_ge
  exact lt_of_le_of_lt h_outerB_le (lt_of_lt_of_le h_dom h_Z_ge)

noncomputable def ScaffoldMatchingQ.empty (k Y q : ℕ) : ScaffoldMatchingQ k Y q where
  T := ∅
  T_subset := by simp
  scaffold := fun t => absurd t.property (Finset.notMem_empty _)
  scaffold_prime := fun t => absurd t.property (Finset.notMem_empty _)
  scaffold_in_range := fun t => absurd t.property (Finset.notMem_empty _)
  scaffold_inj := fun t _ _ => absurd t.property (Finset.notMem_empty _)
  scaffold_mod_q := fun t => absurd t.property (Finset.notMem_empty _)

theorem ScaffoldMatchingQ.empty_residue (k Y q p : ℕ) :
    (ScaffoldMatchingQ.empty k Y q).toScaffoldMatching.residue p = 0 := by
  unfold ScaffoldMatching.residue
  rw [dif_neg]
  rintro ⟨t, _⟩
  exact absurd t.property (Finset.notMem_empty _)

theorem combinedResidue_empty_at_q {k Y q : ℕ} :
    combinedResidue q (BufferData.empty k Y) (ScaffoldMatchingQ.empty k Y q).toScaffoldMatching
      q = 1 := combinedResidue_at_q _ _

theorem combinedResidue_empty_other {k Y q p : ℕ} (hpq : p ≠ q) :
    combinedResidue q (BufferData.empty k Y)
        (ScaffoldMatchingQ.empty k Y q).toScaffoldMatching p = 0 := by
  unfold combinedResidue
  rw [if_neg hpq, BufferData.empty_residue, if_neg (by simp), ScaffoldMatchingQ.empty_residue]

noncomputable def CoverBuildData.toCoverData {B k : ℕ} (cbd : CoverBuildData B k) :
    CoverData B k where
  a := cbd.a
  q := cbd.q
  q_prime := cbd.q_prime
  m_le_q := cbd.m_le_q
  q_le_2m := cbd.q_le_2m
  k_ge_4m := cbd.k_ge_4m
  q_dvd_k := cbd.q_dvd_k
  a_lt_p := cbd.a_lt_p
  a_bound := cbd.a_bound
  covers := cbd.covers
  scaffold := fun p hp h_nz => cbd.scaffold_field p h_nz

theorem CoverBuildData.toCoverData_a {B k : ℕ} (cbd : CoverBuildData B k) :
    cbd.toCoverData.a = cbd.a := rfl

theorem IsNonExcessCov_from_scaffold_non_excess {B k : ℕ}
    (cov : CoverData B k)
    (h_scaffold_ne : ∀ p, p.Prime → B ≤ p → p ≤ k → cov.a p ≠ 0 →
      k / 2 < p → k % p < cov.a p) :
    IsNonExcessCov cov := by
  intro p hp hBp hp_le_k hnz
  rcases cov.scaffold p hp hnz with hpq | ⟨hk2, _, _⟩
  · subst hpq
    rw [Nat.mod_eq_zero_of_dvd cov.q_dvd_k]
    exact Nat.one_le_iff_ne_zero.mpr hnz
  · exact h_scaffold_ne p hp hBp hp_le_k hnz hk2

theorem buffer_polylog_bound (B : ℕ) :
    ∃ N : ℕ, ∀ Y : ℕ, N ≤ Y →
      42 * M_B B * (Nat.log 2 (Y * Y) + 1) ≤ Y * Y := by
  obtain ⟨N, hN⟩ := polylog_le_self (42 * M_B B) 1
  refine ⟨N + 1, ?_⟩
  intro Y hY
  have hY_pos : 0 < Y := by omega
  have hYY_ge_N : N ≤ Y * Y := by
    have hY_ge_N : N ≤ Y := by omega
    calc N ≤ Y := hY_ge_N
      _ ≤ Y * Y := Nat.le_mul_of_pos_left _ hY_pos
  have := hN (Y * Y) hYY_ge_N
  simpa using this

theorem real_log_lt_nat_log_succ {n : ℕ} (hn : 1 ≤ n) :
    Real.log (n : ℝ) < (Nat.log 2 n + 1 : ℕ) := by
  have h_log2_le : Real.log 2 < 1 := Real.log_two_lt_d9.trans (by norm_num)
  have h_pow : (n : ℝ) ≤ 2 ^ (Nat.log 2 n + 1) := by
    have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) n
    exact_mod_cast h.le
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  calc Real.log (n : ℝ) ≤ Real.log ((2 : ℝ) ^ (Nat.log 2 n + 1)) :=
        Real.log_le_log hn_pos h_pow
    _ = ((Nat.log 2 n + 1 : ℕ) : ℝ) * Real.log 2 := by
        rw [Real.log_pow]
    _ < (Nat.log 2 n + 1 : ℕ) * 1 := by
        apply mul_lt_mul_of_pos_left h_log2_le
        push_cast; positivity
    _ = (Nat.log 2 n + 1 : ℕ) := by ring

theorem prime_filter_eq_odd_filter {a b : ℕ} (ha : 2 ≤ a) :
    (Finset.Ioc a b).filter Nat.Prime =
      (Finset.Ioc a b).filter (fun p => p.Prime ∧ p % 2 = 1) := by
  apply Finset.filter_congr
  intro x hx
  rw [Finset.mem_Ioc] at hx
  refine ⟨fun hp => ⟨hp, ?_⟩, fun ⟨hp, _⟩ => hp⟩
  rcases hp.eq_two_or_odd with h2 | hodd
  · omega
  · exact hodd

theorem buffer_prime_supply (B : ℕ) :
    ∃ Y₀ : ℕ, ∀ Y : ℕ, Y₀ ≤ Y →
      M_B B ≤ ((Finset.Ioc (Y * Y) (2 * Y * Y)).filter Nat.Prime).card := by
  obtain ⟨X₀, hX₀⟩ := central_primes_AP_lower 2 Nat.prime_two (le_refl 2)
  obtain ⟨N_poly, hN_poly⟩ := buffer_polylog_bound B
  refine ⟨max 2 (max N_poly (Nat.sqrt X₀ + 1)), ?_⟩
  intro Y hY
  have hY_2 : 2 ≤ Y := le_trans (le_max_left _ _) hY
  have hY_N : N_poly ≤ Y :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hY)
  have hY_sq : Nat.sqrt X₀ + 1 ≤ Y :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hY)
  have hYY_ge_X₀ : X₀ ≤ Y * Y := by
    have h_sqrt : X₀ < (Nat.sqrt X₀ + 1) ^ 2 := Nat.lt_succ_sqrt' X₀
    have h_pow_eq : (Nat.sqrt X₀ + 1) ^ 2 = (Nat.sqrt X₀ + 1) * (Nat.sqrt X₀ + 1) := sq _
    rw [h_pow_eq] at h_sqrt
    have h_le : (Nat.sqrt X₀ + 1) * (Nat.sqrt X₀ + 1) ≤ Y * Y := Nat.mul_le_mul hY_sq hY_sq
    omega
  have h_central := hX₀ (Y * Y) 0 hYY_ge_X₀ (Nat.zero_le _)
  have hYY_pos : 0 < Y * Y := Nat.mul_pos (by omega) (by omega)
  have h_2YY_sub_0 : 2 * (Y * Y) - 0 = 2 * (Y * Y) := by omega
  rw [h_2YY_sub_0] at h_central
  have h_2YY_eq : 2 * (Y * Y) = 2 * Y * Y := by ring
  have h_filter_eq :
      (Finset.Ioc (Y * Y) (2 * Y * Y)).filter Nat.Prime =
        (Finset.Ioc (Y * Y) (2 * (Y * Y))).filter
          (fun p => p.Prime ∧ p % 2 = 1) := by
    rw [h_2YY_eq]
    exact prime_filter_eq_odd_filter (by nlinarith)
  rw [h_filter_eq]
  have h_central_simp :
      ((Y * Y : ℕ) : ℝ) / (8 * Real.log (2 * (Y * Y : ℕ) : ℝ)) ≤
        (((Finset.Ioc (Y * Y) (2 * (Y * Y))).filter
          (fun p => p.Prime ∧ p % 2 = 1)).card : ℝ) := by
    have h_log_eq : Real.log (2 * (Y * Y : ℕ) : ℝ) =
        Real.log (2 * (Y * Y : ℕ) : ℝ) := rfl
    have := h_central
    have h_q_simp : ((2 : ℕ) : ℝ) - 1 = 1 := by norm_num
    rw [h_q_simp] at this
    have h_mul_one : (8 : ℝ) * (1 * Real.log (2 * (Y * Y : ℕ) : ℝ)) =
        8 * Real.log (2 * (Y * Y : ℕ) : ℝ) := by ring
    rw [h_mul_one] at this
    exact this
  have h_MB_bound : (M_B B : ℝ) ≤
      ((Y * Y : ℕ) : ℝ) / (8 * Real.log (2 * (Y * Y : ℕ) : ℝ)) := by
    have hYY_pos : 0 < Y * Y := Nat.mul_pos (by omega) (by omega)
    have hYY_pos_real : (0 : ℝ) < (Y * Y : ℕ) := by exact_mod_cast hYY_pos
    have h2YY_pos : 1 ≤ 2 * (Y * Y) := by omega
    have h_real_lt := real_log_lt_nat_log_succ h2YY_pos
    have h_2YY_log : Nat.log 2 (2 * (Y * Y)) = Nat.log 2 (Y * Y) + 1 := by
      have h_comm : 2 * (Y * Y) = (Y * Y) * 2 := by ring
      rw [h_comm, Nat.log_mul_base (by norm_num : 1 < 2)
        (by positivity : Y * Y ≠ 0)]
    rw [h_2YY_log] at h_real_lt
    have h_log_pos : 0 < Real.log (2 * (Y * Y : ℕ) : ℝ) := by
      apply Real.log_pos
      have : (4 : ℝ) ≤ 2 * (Y * Y : ℕ) := by exact_mod_cast (by nlinarith : 4 ≤ 2 * (Y * Y))
      linarith
    have hN := hN_poly Y hY_N
    rw [le_div_iff₀ (by positivity)]
    have h_8_pos : (0 : ℝ) ≤ (8 : ℝ) * (M_B B : ℝ) := by positivity
    have h_log_cast_eq :
        Real.log (2 * (Y * Y : ℕ) : ℝ) = Real.log ((2 * (Y * Y) : ℕ) : ℝ) := by
      congr 1; push_cast; ring
    have h_chain1 : (M_B B : ℝ) * (8 * Real.log (2 * (Y * Y : ℕ) : ℝ)) ≤
        (M_B B : ℝ) * (8 * ((Nat.log 2 (Y * Y) + 1 + 1 : ℕ) : ℝ)) := by
      rw [h_log_cast_eq]
      apply mul_le_mul_of_nonneg_left
      · apply mul_le_mul_of_nonneg_left h_real_lt.le
        norm_num
      · exact_mod_cast Nat.zero_le _
    have h_chain2 : (M_B B : ℝ) * (8 * ((Nat.log 2 (Y * Y) + 1 + 1 : ℕ) : ℝ)) ≤
        ((Y * Y : ℕ) : ℝ) := by
      have h_nat : 8 * M_B B * (Nat.log 2 (Y * Y) + 1 + 1) ≤ Y * Y := by
        have h1 : 8 * M_B B * (Nat.log 2 (Y * Y) + 1 + 1) ≤
            16 * M_B B * (Nat.log 2 (Y * Y) + 1) := by nlinarith
        linarith
      have : (M_B B : ℝ) * (8 * ((Nat.log 2 (Y * Y) + 1 + 1 : ℕ) : ℝ)) =
          ((8 * M_B B * (Nat.log 2 (Y * Y) + 1 + 1) : ℕ) : ℝ) := by push_cast; ring
      rw [this]
      exact_mod_cast h_nat
    linarith
  have h_MB_le_count_real :
      (M_B B : ℝ) ≤
        (((Finset.Ioc (Y * Y) (2 * (Y * Y))).filter
          (fun p => p.Prime ∧ p % 2 = 1)).card : ℝ) :=
    le_trans h_MB_bound h_central_simp
  exact_mod_cast h_MB_le_count_real

theorem floor_nat_div_eq (k n : ℕ) (hn : 0 < n) :
    ⌊((k : ℝ) / (n : ℝ))⌋₊ = k / n := by
  apply (Nat.floor_eq_iff (by positivity)).mpr
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
  constructor
  · rw [le_div_iff₀ hn_pos]
    have h1 : (k / n : ℕ) * n ≤ k := Nat.div_mul_le_self k n
    exact_mod_cast h1
  · rw [div_lt_iff₀ hn_pos]
    have h_mod : k % n < n := Nat.mod_lt k hn
    have h_bound : k < (k / n + 1) * n := by
      have h_eq : k = n * (k / n) + k % n := (Nat.div_add_mod k n).symm
      have : (k / n + 1) * n = n * (k / n) + n := by ring
      omega
    exact_mod_cast h_bound

theorem third_half_polylog_bound (B : ℕ) :
    ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
      48 * (Nat.log 2 k + 1) ^ (M_B B + 6) ≤ k :=
  polylog_le_self 48 (M_B B + 6)

theorem third_half_prime_count_dominates_HX (B : ℕ) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      2 * H_X (M_B B) k + 1 < (ThirdHalfPrimes k).card := by
  obtain ⟨x₀_real, hx₀_ge, hx₀⟩ :=
    PNT_fixed_modulus 2 1 (by norm_num) (by norm_num)
      (Nat.coprime_one_left 2) (1/2 : ℝ) (by norm_num) (1/2 : ℝ) (by norm_num)
  obtain ⟨N_poly, hN_poly⟩ := third_half_polylog_bound B
  refine ⟨max (4 * ⌈x₀_real⌉₊) (max N_poly 24), ?_⟩
  intro k hk
  have hk_x₀ : 4 * ⌈x₀_real⌉₊ ≤ k := le_trans (le_max_left _ _) hk
  have hk_N : N_poly ≤ k := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hk)
  have hk_24 : 24 ≤ k := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hk)
  have hk_pos : 0 < k := by omega
  have hk_real_pos : (0 : ℝ) < k := by exact_mod_cast hk_pos
  have h_ceil : (⌈x₀_real⌉₊ : ℝ) ≥ x₀_real := Nat.le_ceil _
  have hx₀_le_k4 : x₀_real ≤ (k : ℝ) / 4 := by
    have : 4 * (⌈x₀_real⌉₊ : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk_x₀
    linarith
  have h_u_ge : (k : ℝ) / 4 ≤ (k : ℝ) / 3 := by linarith
  have h_u_lt_v : (k : ℝ) / 3 < (k : ℝ) / 2 := by linarith
  have h_v_le : (k : ℝ) / 2 ≤ 2 * ((k : ℝ) / 4) := by linarith
  have h_δ_le : (1/2 : ℝ) * ((k : ℝ) / 4) ≤ (k : ℝ) / 2 - (k : ℝ) / 3 := by linarith
  have h_pnt := hx₀ ((k : ℝ) / 4) hx₀_le_k4 ((k : ℝ) / 3) ((k : ℝ) / 2)
    h_u_ge h_u_lt_v h_v_le h_δ_le
  have h_filter_eq :
      (Finset.Ioc ⌊((k : ℝ) / 3)⌋₊ ⌊((k : ℝ) / 2)⌋₊).filter
          (fun p => p.Prime ∧ p % 2 = 1) =
        ThirdHalfPrimes k := by
    have h_3 : ⌊((k : ℝ) / 3)⌋₊ = k / 3 := by
      show ⌊((k : ℝ) / ((3 : ℕ) : ℝ))⌋₊ = k / 3
      exact floor_nat_div_eq k 3 (by norm_num)
    have h_2 : ⌊((k : ℝ) / 2)⌋₊ = k / 2 := by
      show ⌊((k : ℝ) / ((2 : ℕ) : ℝ))⌋₊ = k / 2
      exact floor_nat_div_eq k 2 (by norm_num)
    rw [h_3, h_2]
    unfold ThirdHalfPrimes
    have h_k3_ge_2 : 2 ≤ k / 3 := by omega
    exact (prime_filter_eq_odd_filter h_k3_ge_2).symm
  rw [h_filter_eq] at h_pnt
  have h_tot : (Nat.totient 2 : ℝ) = 1 := by
    show ((Nat.totient 2 : ℕ) : ℝ) = 1
    have : Nat.totient 2 = 1 := by decide
    exact_mod_cast this
  rw [h_tot, one_mul] at h_pnt
  have h_k4_pos : (1 : ℝ) < (k : ℝ) / 4 := by
    have : (24 : ℝ) ≤ k := by exact_mod_cast hk_24
    linarith
  have h_log_k4_pos : 0 < Real.log ((k : ℝ) / 4) := Real.log_pos h_k4_pos
  have h_v_minus_u : (k : ℝ) / 2 - (k : ℝ) / 3 = (k : ℝ) / 6 := by ring
  rw [h_v_minus_u] at h_pnt
  have h_abs_lb := (abs_le.mp h_pnt).1
  have h_count_ge :
      ((k : ℝ) / 6) / Real.log ((k : ℝ) / 4) -
        (1/2 : ℝ) * ((k : ℝ) / 6) / Real.log ((k : ℝ) / 4) ≤
      ((ThirdHalfPrimes k).card : ℝ) := by linarith
  have h_simp : ((k : ℝ) / 6) / Real.log ((k : ℝ) / 4) -
      (1/2 : ℝ) * ((k : ℝ) / 6) / Real.log ((k : ℝ) / 4) =
      ((k : ℝ) / 12) / Real.log ((k : ℝ) / 4) := by field_simp; ring
  rw [h_simp] at h_count_ge
  have h_log_k4_lt : Real.log ((k : ℝ) / 4) < ((Nat.log 2 k + 1 : ℕ) : ℝ) := by
    have h1 : Real.log ((k : ℝ) / 4) ≤ Real.log (k : ℝ) := by
      apply Real.log_le_log (by linarith)
      have : (4 : ℝ) ≥ 1 := by norm_num
      have hk_real : (0 : ℝ) < (k : ℝ) := hk_real_pos
      have : (k : ℝ) / 4 ≤ (k : ℝ) := by linarith
      exact this
    have h2 : Real.log (k : ℝ) < ((Nat.log 2 k + 1 : ℕ) : ℝ) :=
      real_log_lt_nat_log_succ (by omega : 1 ≤ k)
    linarith
  have h_HX_pos : 0 < H_X (M_B B) k := H_X_pos _ _ (by omega : 1 ≤ k)
  have h_2HX_p1_le_3HX : 2 * H_X (M_B B) k + 1 ≤ 3 * H_X (M_B B) k := by omega
  have h_HX_eq : H_X (M_B B) k = (Nat.log 2 k + 1) ^ (M_B B + 5) := H_X_def _ _
  have hN := hN_poly k hk_N
  have h_key : (12 : ℝ) * ((2 * H_X (M_B B) k + 1 : ℕ) : ℝ) *
      Real.log ((k : ℝ) / 4) < (k : ℝ) := by
    have h_pos1 : (0 : ℝ) < 12 * ((2 * H_X (M_B B) k + 1 : ℕ) : ℝ) := by positivity
    have h_step1 : (12 : ℝ) * ((2 * H_X (M_B B) k + 1 : ℕ) : ℝ) *
        Real.log ((k : ℝ) / 4) <
        12 * ((2 * H_X (M_B B) k + 1 : ℕ) : ℝ) * ((Nat.log 2 k + 1 : ℕ) : ℝ) := by
      nlinarith [h_log_k4_lt, h_pos1]
    have h_step2 : (12 : ℝ) * ((2 * H_X (M_B B) k + 1 : ℕ) : ℝ) *
        ((Nat.log 2 k + 1 : ℕ) : ℝ) ≤
        (36 : ℝ) * ((H_X (M_B B) k * (Nat.log 2 k + 1) : ℕ) : ℝ) := by
      have hle : 12 * (2 * H_X (M_B B) k + 1) * (Nat.log 2 k + 1) ≤
          36 * (H_X (M_B B) k * (Nat.log 2 k + 1)) := by nlinarith
      have := hle
      push_cast
      have hle_real : (12 : ℝ) * (2 * H_X (M_B B) k + 1 : ℕ) * (Nat.log 2 k + 1 : ℕ) ≤
          (36 : ℝ) * ((H_X (M_B B) k : ℕ) * (Nat.log 2 k + 1 : ℕ) : ℕ) := by exact_mod_cast this
      push_cast at hle_real
      linarith
    have h_step3 : (36 : ℝ) * ((H_X (M_B B) k * (Nat.log 2 k + 1) : ℕ) : ℝ) <
        (k : ℝ) := by
      have h_nat : 36 * (H_X (M_B B) k * (Nat.log 2 k + 1)) < k := by
        have h_eq : H_X (M_B B) k * (Nat.log 2 k + 1) =
            (Nat.log 2 k + 1) ^ (M_B B + 6) := by
          rw [h_HX_eq, ← pow_succ]
        rw [h_eq]
        omega
      exact_mod_cast h_nat
    linarith
  have h_final : ((2 * H_X (M_B B) k + 1 : ℕ) : ℝ) <
      ((k : ℝ) / 12) / Real.log ((k : ℝ) / 4) := by
    rw [lt_div_iff₀ h_log_k4_pos]
    nlinarith [h_key, h_log_k4_pos]
  have h_count_real : ((2 * H_X (M_B B) k + 1 : ℕ) : ℝ) <
      ((ThirdHalfPrimes k).card : ℝ) := lt_of_lt_of_le h_final h_count_ge
  exact_mod_cast h_count_real

theorem third_half_square_product_dominates_HX (B : ℕ) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      k ^ (2 * H_X (M_B B) k + 1) < ∏ p ∈ ThirdHalfPrimes k, p ^ 2 := by
  obtain ⟨k₀, hk₀⟩ := third_half_prime_count_dominates_HX B
  refine ⟨max k₀ 10, ?_⟩
  intro k hk
  have hk_ge_k₀ : k₀ ≤ k := le_trans (le_max_left _ _) hk
  have hk10 : 10 ≤ k := le_trans (le_max_right _ _) hk
  exact third_half_square_product_dominates_of_count hk10 (hk₀ k hk_ge_k₀)

theorem multiples_in_short_interval_card_le_local
    {W Y t : ℕ} (hW : 0 < W) :
    ((Finset.Icc t (t + Y)).filter (fun k => W ∣ k)).card ≤ Y / W + 2 := by
  classical
  have h_target_card : (Finset.Icc (t / W) (t / W + Y / W + 1)).card = Y / W + 2 := by
    rw [Nat.card_Icc]
    set a := t / W
    set b := Y / W
    show a + b + 1 + 1 - a = b + 2
    rw [show a + b + 1 + 1 = a + (b + 2) from by ring, Nat.add_sub_cancel_left]
  rw [← h_target_card]
  refine Finset.card_le_card_of_injOn (· / W) ?_ ?_
  · intro k hk
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_Icc] at hk
    obtain ⟨⟨ht_le, hle_tY⟩, hWk⟩ := hk
    simp only [Finset.mem_coe, Finset.mem_Icc]
    refine ⟨Nat.div_le_div_right ht_le, ?_⟩
    have h2 : (t + Y) / W ≤ t / W + Y / W + 1 := by
      have h := Nat.add_div hW (a := t) (b := Y)
      have h3 : (t + Y) / W = t / W + Y / W +
        if W ≤ t % W + Y % W then 1 else 0 := h
      split_ifs at h3 <;> omega
    exact le_trans (Nat.div_le_div_right hle_tY) h2
  · intro a ha b hb hab
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_coe] at ha hb
    obtain ⟨_, hWa⟩ := ha
    obtain ⟨_, hWb⟩ := hb
    have ha_eq : (a / W) * W = a := Nat.div_mul_cancel hWa
    have hb_eq : (b / W) * W = b := Nat.div_mul_cancel hWb
    have h_simple : a / W = b / W := hab
    calc a = (a / W) * W := ha_eq.symm
      _ = (b / W) * W := by rw [h_simple]
      _ = b := hb_eq

theorem BadK_card_le_refined_local
    {B X Y q W : ℕ} {b : ℕ → ℕ} (hW : 0 < W) :
    (BadK X Y W (residualSet B X Y q b)).card
      ≤ (residualSet B X Y q b).card * (Y / W + 2) := by
  classical
  calc (BadK X Y W (residualSet B X Y q b)).card
      ≤ ∑ t ∈ residualSet B X Y q b,
          ((Finset.Icc t (t + Y - 1)).filter (W ∣ ·)).card :=
        BadK_card_le_sum_filter X Y W _
    _ ≤ ∑ _t ∈ residualSet B X Y q b, (Y / W + 2) := by
        refine Finset.sum_le_sum (fun t _ => ?_)
        have hsub : (Finset.Icc t (t + Y - 1)).filter (W ∣ ·) ⊆
            (Finset.Icc t (t + Y)).filter (W ∣ ·) := by
          intro k hk
          rw [Finset.mem_filter, Finset.mem_Icc] at hk ⊢
          obtain ⟨⟨h1, h2⟩, h3⟩ := hk
          exact ⟨⟨h1, by omega⟩, h3⟩
        exact (Finset.card_le_card hsub).trans
          (multiples_in_short_interval_card_le_local hW)
    _ = (residualSet B X Y q b).card * (Y / W + 2) := by
        rw [Finset.sum_const, smul_eq_mul]

theorem exists_multiple_not_in_BadK_local
    {B X Y q W : ℕ} {b : ℕ → ℕ}
    (hW_pos : 0 < W)
    (h_more_mult :
      (residualSet B X Y q b).card * (Y / W + 2) <
        ((Finset.Icc X (2 * X)).filter (W ∣ ·)).card) :
    ∃ k : ℕ,
      X ≤ k ∧ k ≤ 2 * X ∧ W ∣ k ∧
      k ∉ BadK X Y W (residualSet B X Y q b) := by
  classical
  by_contra h_no_good
  push_neg at h_no_good
  have h_all_bad :
      (Finset.Icc X (2 * X)).filter (W ∣ ·) ⊆
        BadK X Y W (residualSet B X Y q b) := by
    intro k hk
    rw [Finset.mem_filter, Finset.mem_Icc] at hk
    obtain ⟨⟨hX, h2X⟩, hWk⟩ := hk
    by_contra h_not_bad
    exact h_not_bad (h_no_good k hX h2X hWk)
  have h1 : ((Finset.Icc X (2 * X)).filter (W ∣ ·)).card ≤
      (BadK X Y W (residualSet B X Y q b)).card :=
    Finset.card_le_card h_all_bad
  have h2 := BadK_card_le_refined_local (B := B) (X := X) (Y := Y) (q := q) (W := W) (b := b) hW_pos
  omega

theorem bTotal_d_le_q41
    {B q Y : ℕ} (hq_prime : q.Prime) (hY_eq : Y = q^20)
    (b : ℕ → ℕ) (hb : ∀ d ∈ smallDeficientSet B Y q,
      ∃ bd_val : ℕ, b d = bd_val ∧ Y * Y < bd_val ∧ bd_val ≤ 2 * Y * Y) :
    ∀ d ∈ smallDeficientSet B Y q, b d ≤ q ^ 41 := by
  intro d hd
  obtain ⟨bd_val, hbd_eq, _, hbd_le⟩ := hb d hd
  rw [hbd_eq]
  have hq_ge_2 : 2 ≤ q := hq_prime.two_le
  have hYY_eq : Y * Y = q ^ 40 := by rw [hY_eq, ← pow_add]
  have h_2YY_le : 2 * Y * Y ≤ q ^ 41 := by
    rw [show 2 * Y * Y = 2 * (Y * Y) from by ring, hYY_eq,
      show q ^ 41 = q * q ^ 40 from by rw [pow_succ]; ring]
    exact Nat.mul_le_mul_right (q^40) hq_ge_2
  linarith

theorem W_product_le_q_pow
    {q B Y : ℕ} (hq_prime : q.Prime) (hq_ge_2 : 2 ≤ q)
    (b : ℕ → ℕ)
    (hb_le : ∀ d ∈ smallDeficientSet B Y q, b d ≤ q^41)
    (hM_B : M_B B = B * (20 + 1))
    (hD_card_le : (smallDeficientSet B Y q).card ≤ M_B B) :
    W_product q B Y b ≤ q ^ (861 * B + 1) := by
  show q * ∏ d ∈ smallDeficientSet B Y q, b d ≤ q ^ (861 * B + 1)
  have h_prod_le :
      ∏ d ∈ smallDeficientSet B Y q, b d ≤
        (q^41) ^ (smallDeficientSet B Y q).card := by
    have h1 : ∏ d ∈ smallDeficientSet B Y q, b d ≤
        ∏ _d ∈ smallDeficientSet B Y q, q^41 :=
      Finset.prod_le_prod (fun d _ => Nat.zero_le _) hb_le
    have h2 : ∏ _d ∈ smallDeficientSet B Y q, q^41 =
        (q^41) ^ (smallDeficientSet B Y q).card := by
      rw [Finset.prod_const]
    omega
  have h_card_le_21B : (smallDeficientSet B Y q).card ≤ 21 * B := by
    have h1 := hD_card_le; rw [hM_B] at h1; omega
  have h_pow_le : (q ^ 41) ^ (smallDeficientSet B Y q).card ≤ (q ^ 41) ^ (21 * B) :=
    Nat.pow_le_pow_right (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ hq_prime.pos.ne'))
      h_card_le_21B
  have h_simp : (q ^ 41) ^ (21 * B) = q ^ (861 * B) := by
    rw [← pow_mul]; congr 1; ring
  rw [h_simp] at h_pow_le
  have h_W_bound : q * ∏ d ∈ smallDeficientSet B Y q, b d ≤ q * q ^ (861 * B) :=
    Nat.mul_le_mul_left q (h_prod_le.trans h_pow_le)
  have h_qq : q * q ^ (861 * B) = q ^ (861 * B + 1) := by rw [pow_succ]; ring
  rw [h_qq] at h_W_bound
  exact h_W_bound

theorem multiples_in_long_interval_card_ge_no_dvd_local
    {X W : ℕ} (hW_pos : 0 < W) (hW_le : W ≤ X) :
    X / W ≤ ((Finset.Icc X (2 * X)).filter (W ∣ ·)).card := by
  classical
  set m := X / W with hm_def
  have hm_pos : 1 ≤ m := by
    rw [hm_def]; exact Nat.one_le_div_iff hW_pos |>.mpr hW_le
  have h_image_subset :
      (Finset.Icc (m + 1) (2 * m)).image (fun r => W * r) ⊆
        (Finset.Icc X (2 * X)).filter (W ∣ ·) := by
    intro k hk
    rw [Finset.mem_image] at hk
    obtain ⟨r, hr, hkr⟩ := hk
    rw [Finset.mem_Icc] at hr
    obtain ⟨hr_lo, hr_hi⟩ := hr
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [← hkr]
      have hX_le : X ≤ W * (m + 1) := by
        have h_X_eq : X = W * m + X % W := (Nat.div_add_mod X W).symm
        have h_mod_lt : X % W < W := Nat.mod_lt _ hW_pos
        have : X = W * m + X % W := h_X_eq
        have : W * (m + 1) = W * m + W := by ring
        omega
      have : W * (m + 1) ≤ W * r := Nat.mul_le_mul_left W hr_lo
      omega
    · rw [← hkr]
      have h2X : W * (2 * m) ≤ 2 * X := by
        have h_X_eq : X = W * m + X % W := (Nat.div_add_mod X W).symm
        have : W * (2 * m) = 2 * (W * m) := by ring
        omega
      have : W * r ≤ W * (2 * m) := Nat.mul_le_mul_left W hr_hi
      omega
    · rw [← hkr]; exact dvd_mul_right W r
  have h_image_card : ((Finset.Icc (m + 1) (2 * m)).image (fun r => W * r)).card = m := by
    rw [Finset.card_image_of_injOn]
    · rw [Nat.card_Icc]; omega
    · intro a _ b _ hab
      exact Nat.eq_of_mul_eq_mul_left hW_pos hab
  calc X / W
      = m := hm_def
    _ = ((Finset.Icc (m + 1) (2 * m)).image (fun r => W * r)).card := h_image_card.symm
    _ ≤ ((Finset.Icc X (2 * X)).filter (W ∣ ·)).card :=
        Finset.card_le_card h_image_subset

theorem multiples_in_long_interval_card_ge_local
    {X W : ℕ} (hW_pos : 0 < W) (hW_dvd : W ∣ X) (hW_le : W ≤ X) :
    X / W + 1 ≤ ((Finset.Icc X (2 * X)).filter (W ∣ ·)).card := by
  classical
  set m := X / W with hm_def
  have hXm : X = W * m := by
    rw [hm_def, Nat.mul_div_cancel' hW_dvd]
  have h_image_subset :
      (Finset.Icc m (2 * m)).image (fun r => W * r) ⊆
        (Finset.Icc X (2 * X)).filter (W ∣ ·) := by
    intro k hk
    rw [Finset.mem_image] at hk
    obtain ⟨r, hr, hkr⟩ := hk
    rw [Finset.mem_Icc] at hr
    obtain ⟨hr_lo, hr_hi⟩ := hr
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [hXm, ← hkr]
      exact Nat.mul_le_mul_left W hr_lo
    · rw [← hkr]
      have h2X : 2 * X = W * (2 * m) := by rw [hXm]; ring
      rw [h2X]
      exact Nat.mul_le_mul_left W hr_hi
    · rw [← hkr]; exact dvd_mul_right W r
  have h_image_card : ((Finset.Icc m (2 * m)).image (fun r => W * r)).card = m + 1 := by
    rw [Finset.card_image_of_injOn]
    · rw [Nat.card_Icc]; omega
    · intro a _ b _ hab
      exact Nat.eq_of_mul_eq_mul_left hW_pos hab
  calc X / W + 1
      = m + 1 := by rw [hm_def]
    _ = ((Finset.Icc m (2 * m)).image (fun r => W * r)).card := h_image_card.symm
    _ ≤ ((Finset.Icc X (2 * X)).filter (W ∣ ·)).card :=
        Finset.card_le_card h_image_subset

theorem exists_good_k_for_scaffold_final
    {B X Y q W : ℕ} {b : ℕ → ℕ}
    (hW_pos : 0 < W)
    (hU_card :
      (residualSet B (2 * X) Y q b).card ≤ H_X (M_B B) (2 * X))
    (hSupply :
      4 * H_X (M_B B) (2 * X) *
          (((Finset.Icc X (2 * X)).filter (W ∣ ·)).card)
        ≤
      ∑ k ∈ ((Finset.Icc X (2 * X)).filter (W ∣ ·)),
        (CandidatePrimes k Y q).card)
    (hBadSmall :
      (residualSet B (2 * X) Y q b).card * (Y / W + 2) * Y
        + H_X (M_B B) (2 * X) *
          (((Finset.Icc X (2 * X)).filter (W ∣ ·)).card)
        <
      4 * H_X (M_B B) (2 * X) *
          (((Finset.Icc X (2 * X)).filter (W ∣ ·)).card)) :
    ∃ k : ℕ,
      X ≤ k ∧ k ≤ 2 * X ∧
      W ∣ k ∧
      H_X (M_B B) (2 * X) ≤ (CandidatePrimes k Y q).card ∧
      k ∉ BadK X Y W (residualSet B (2 * X) Y q b) := by
  classical
  set Ω := ((Finset.Icc X (2 * X)).filter (W ∣ ·)) with hΩ_def
  set U := residualSet B (2 * X) Y q b with hU_def
  set Bad := BadK X Y W U with hBad_def
  by_contra hnone
  push_neg at hnone
  have hbad_card : Bad.card ≤ U.card * (Y / W + 2) := by
    classical
    rw [hBad_def, hU_def]
    calc (BadK X Y W (residualSet B (2 * X) Y q b)).card
        ≤ ∑ t ∈ residualSet B (2 * X) Y q b,
            ((Finset.Icc t (t + Y - 1)).filter (W ∣ ·)).card :=
          BadK_card_le_sum_filter X Y W _
      _ ≤ ∑ _t ∈ residualSet B (2 * X) Y q b, (Y / W + 2) := by
          refine Finset.sum_le_sum (fun t _ => ?_)
          have hsub : (Finset.Icc t (t + Y - 1)).filter (W ∣ ·) ⊆
              (Finset.Icc t (t + Y)).filter (W ∣ ·) := by
            intro k hk
            rw [Finset.mem_filter, Finset.mem_Icc] at hk ⊢
            obtain ⟨⟨h1, h2⟩, h3⟩ := hk
            exact ⟨⟨h1, by omega⟩, h3⟩
          exact (Finset.card_le_card hsub).trans
            (multiples_in_short_interval_card_le_local hW_pos)
      _ = (residualSet B (2 * X) Y q b).card * (Y / W + 2) := by
          rw [Finset.sum_const, smul_eq_mul]
  have hbad_sum :
      ∑ k ∈ Ω.filter (fun k => k ∈ Bad), (CandidatePrimes k Y q).card
        ≤ Bad.card * Y := by
    calc ∑ k ∈ Ω.filter (fun k => k ∈ Bad), (CandidatePrimes k Y q).card
        ≤ ∑ _k ∈ Ω.filter (fun k => k ∈ Bad), Y := by
          apply Finset.sum_le_sum
          intro k _; exact CandidatePrimes_card_le_Y
      _ = (Ω.filter (fun k => k ∈ Bad)).card * Y := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ Bad.card * Y := by
          exact Nat.mul_le_mul_right Y
            (Finset.card_le_card (by
              intro k hk
              rw [Finset.mem_filter] at hk
              exact hk.2))
  have hgood_sum :
      ∑ k ∈ Ω.filter (fun k => k ∉ Bad), (CandidatePrimes k Y q).card
        ≤ H_X (M_B B) (2 * X) *
          (Ω.filter (fun k => k ∉ Bad)).card := by
    calc ∑ k ∈ Ω.filter (fun k => k ∉ Bad), (CandidatePrimes k Y q).card
        ≤ ∑ _k ∈ Ω.filter (fun k => k ∉ Bad), H_X (M_B B) (2 * X) := by
          apply Finset.sum_le_sum
          intro k hk
          rw [Finset.mem_filter] at hk
          have hkΩ : k ∈ Ω := hk.1
          have hkNotBad : k ∉ Bad := hk.2
          have hkIcc : k ∈ Finset.Icc X (2 * X) := by
            rw [hΩ_def, Finset.mem_filter] at hkΩ
            exact hkΩ.1
          have hWd : W ∣ k := by
            rw [hΩ_def, Finset.mem_filter] at hkΩ
            exact hkΩ.2
          have hkIcc' := Finset.mem_Icc.mp hkIcc
          have hkNotBad' : k ∉ BadK X Y W (residualSet B (2 * X) Y q b) := by
            rw [← hU_def, ← hBad_def]; exact hkNotBad
          by_contra hge
          push_neg at hge
          have hnotgood := hnone k hkIcc'.1 hkIcc'.2 hWd hge.le
          exact hkNotBad' hnotgood
      _ = H_X (M_B B) (2 * X) *
          (Ω.filter (fun k => k ∉ Bad)).card := by
          rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have hsplit :
      ∑ k ∈ Ω, (CandidatePrimes k Y q).card
        =
      ∑ k ∈ Ω.filter (fun k => k ∈ Bad), (CandidatePrimes k Y q).card
        +
      ∑ k ∈ Ω.filter (fun k => k ∉ Bad), (CandidatePrimes k Y q).card := by
    rw [← Finset.sum_filter_add_sum_filter_not Ω (fun k => k ∈ Bad)
      (fun k => (CandidatePrimes k Y q).card)]
  have hsum_upper :
      ∑ k ∈ Ω, (CandidatePrimes k Y q).card
        ≤ U.card * (Y / W + 2) * Y
          + H_X (M_B B) (2 * X) * Ω.card := by
    rw [hsplit]
    have h1 :
        ∑ k ∈ Ω.filter (fun k => k ∈ Bad), (CandidatePrimes k Y q).card
          ≤ U.card * (Y / W + 2) * Y :=
      hbad_sum.trans (Nat.mul_le_mul_right Y hbad_card)
    have h2 :
        ∑ k ∈ Ω.filter (fun k => k ∉ Bad), (CandidatePrimes k Y q).card
          ≤ H_X (M_B B) (2 * X) * Ω.card :=
      hgood_sum.trans
        (Nat.mul_le_mul_left _ (Finset.card_le_card (Finset.filter_subset _ _)))
    omega
  have h_supply_unfolded :
      4 * H_X (M_B B) (2 * X) * Ω.card
        ≤
      ∑ k ∈ Ω, (CandidatePrimes k Y q).card := by
    rw [hΩ_def]; exact hSupply
  have h_bad_unfolded :
      U.card * (Y / W + 2) * Y + H_X (M_B B) (2 * X) * Ω.card
        < 4 * H_X (M_B B) (2 * X) * Ω.card := by
    rw [hU_def, hΩ_def]; exact hBadSmall
  have hcontra :
      4 * H_X (M_B B) (2 * X) * Ω.card
        ≤ U.card * (Y / W + 2) * Y + H_X (M_B B) (2 * X) * Ω.card :=
    h_supply_unfolded.trans hsum_upper
  omega

theorem const_le_log_pow_4 (a : ℕ) :
    ∃ N : ℕ, ∀ X : ℕ, N ≤ X → a ≤ (Nat.log 2 X + 1) ^ 4 := by
  refine ⟨2 ^ (a + 1), ?_⟩
  intro X hX
  have h_log_pow : Nat.log 2 (2 ^ (a + 1)) = a + 1 :=
    Nat.log_pow (by norm_num) (a + 1)
  have h_log_X : a + 1 ≤ Nat.log 2 X := by
    have h := Nat.log_mono_right (b := 2) hX
    rw [h_log_pow] at h
    exact h
  have h_base : a + 1 ≤ Nat.log 2 X + 1 := by omega
  have h_pow_ge : (a + 1) ^ 4 ≤ (Nat.log 2 X + 1) ^ 4 :=
    Nat.pow_le_pow_left h_base 4
  have h_a_le : a ≤ (a + 1) ^ 4 := by
    have : 1 ≤ (a + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
    calc a ≤ a + 1 := by omega
      _ = (a + 1) ^ 1 := (pow_one _).symm
      _ ≤ (a + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  omega

theorem outerB_ge_B_from_residue_match_local {B k : ℕ} (hk : 3 ≤ k)
    (a : ℕ → ℕ) (j : ℕ) (hj : 1 ≤ j) (hjk : j ≤ k)
    (h_excess_empty : scaffoldExcess k a j = ∅)
    (p : ℕ) (hp : p.Prime) (hBp : B ≤ p) (hpk : p ≤ k)
    (hjmod : j % p = a p) :
    B ≤ outerB k a j := by
  have hk_pos : 0 < k := by omega
  have hj_pos : 0 < j := by omega
  have hp_in : p ∈ ((Finset.Icc 1 k).filter Nat.Prime) := by
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hp.one_lt.le, hpk⟩, hp⟩
  have hexp_pos := exponent_pos_when_mod_a_eq
    k a j p hp hpk hk_pos hj_pos hjk hjmod
  have hp_dvd_inner :=
    exponent_pos_pow_dvd_innerB k a j p hp_in hexp_pos
  have h_outer_eq_inner : outerB k a j =
      innerB k a j := by
    unfold outerB
    rw [h_excess_empty, Finset.prod_empty]
    exact Nat.div_one _
  rw [h_outer_eq_inner]
  have hp_le_inner : p ≤ innerB k a j :=
    Nat.le_of_dvd (innerB_pos k a j) hp_dvd_inner
  omega

theorem eq_of_prime_gt_half_dvd_le_k_local
    {p j k : ℕ} (hp : p.Prime) (hp_half : k / 2 < p)
    (hj_pos : 1 ≤ j) (hj_le : j ≤ k) (hpdvd : p ∣ j) :
    j = p := by
  obtain ⟨r, hr⟩ := hpdvd
  have hp_pos : 0 < p := hp.pos
  match r, hr with
  | 0, hr => omega
  | 1, hr => rw [hr]; ring
  | (n + 2), hr =>
      exfalso
      have h2p_le_j : 2 * p ≤ j := by rw [hr]; nlinarith
      have h2p_le_k : 2 * p ≤ k := h2p_le_j.trans hj_le
      omega

theorem zSet_dvd_innerB_zero_part_local
    {k j q : ℕ} (a : ℕ → ℕ) (S : Finset ℕ)
    (hj_pos : 1 ≤ j) (hj_le : j ≤ k)
    (hz_pos : 0 < zSet j q S) (hz_dvd_j : zSet j q S ∣ j)
    (hzero :
      ∀ p, p.Prime → p ∣ zSet j q S → p ≠ q → p ∉ S → a p = 0)
    (hq_or_S :
      ∀ p, p.Prime → p ∣ zSet j q S → p ≠ q ∧ p ∉ S) :
    zSet j q S ∣ innerB k a j := by
  classical
  have hinner_pos : 0 < innerB k a j :=
    innerB_pos k a j
  rw [← Nat.factorization_le_iff_dvd hz_pos.ne' hinner_pos.ne']
  intro p
  by_cases hp : p.Prime
  · by_cases hp_dvd : p ∣ zSet j q S
    · obtain ⟨hp_ne_q, hp_notin_S⟩ := hq_or_S p hp hp_dvd
      have ha_p : a p = 0 := hzero p hp hp_dvd hp_ne_q hp_notin_S
      have hp_dvd_j : p ∣ j := hp_dvd.trans hz_dvd_j
      have hp_le : p ≤ k :=
        (Nat.le_of_dvd hj_pos hp_dvd_j).trans hj_le
      have h_zSet_fact_le_j :
          (zSet j q S).factorization p ≤ j.factorization p :=
        (Nat.factorization_le_iff_dvd hz_pos.ne' (by omega : j ≠ 0)).mpr hz_dvd_j p
      have h_jfact :
          j.factorization p = padicValNat p j :=
        Nat.factorization_def j hp
      have h_innerB_fact :
          (innerB k a j).factorization p =
            exponent k a j p := by
        unfold innerB
        rw [Nat.factorization_prod (fun r hr => by
          rw [Finset.mem_filter, Finset.mem_Icc] at hr
          exact pow_ne_zero _ hr.2.ne_zero)]
        simp only [Finsupp.coe_finset_sum, Finset.sum_apply]
        rw [Finset.sum_eq_single p]
        · rw [Nat.Prime.factorization_pow hp]
          simp
        · intro r hr hrp
          rw [Finset.mem_filter, Finset.mem_Icc] at hr
          have hr_prime : r.Prime := hr.2
          rw [Nat.Prime.factorization_pow hr_prime]
          simp only [Finsupp.single_apply]
          rw [if_neg]
          intro h
          exact hrp h
        · intro hp_notin
          rw [Finset.mem_filter, Finset.mem_Icc] at hp_notin
          exfalso
          apply hp_notin
          exact ⟨⟨hp.one_lt.le, hp_le⟩, hp⟩
      have h_exp_eq :
          exponent k a j p = padicValNat p j := by
        unfold exponent
        rw [if_pos ha_p]
      rw [h_innerB_fact, h_exp_eq, ← h_jfact]
      exact h_zSet_fact_le_j
    · rw [Nat.factorization_eq_zero_of_not_dvd hp_dvd]
      exact Nat.zero_le _
  · rw [Nat.factorization_eq_zero_of_not_prime _ hp]
    exact Nat.zero_le _

theorem zSet_dvd_outerB_zero_case_local
    {B k j : ℕ} (core : WideCoverBuildCore B k)
    (hj_pos : 1 ≤ j) (hj_le : j ≤ k)
    (h_no_scaffold_collision :
      ∀ t : core.smq.T, core.smq.scaffold t ≠ j)
    (hz_pos : 0 < zSet j core.q core.bufferImage)
    (hz_dvd_j : zSet j core.q core.bufferImage ∣ j)
    (hq_or_S :
      ∀ p, p.Prime → p ∣ zSet j core.q core.bufferImage →
        p ≠ core.q ∧ p ∉ core.bufferImage) :
    zSet j core.q core.bufferImage ∣
      outerB k core.a j := by
  classical
  have hSE : ∀ p, p ∉ scaffoldExcess k core.a j := by
    have h := core.scaffoldExcess_empty (k - j)
    have hk_sub : k - (k - j) = j := by omega
    intro p hp
    have := h p
    rw [hk_sub] at this
    exact this hp
  have hSE_empty : scaffoldExcess k core.a j = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    exact hSE
  have h_outer_eq :
      outerB k core.a j =
        innerB k core.a j := by
    unfold outerB
    rw [hSE_empty, Finset.prod_empty]
    exact Nat.div_one _
  rw [h_outer_eq]
  have hzero :
      ∀ p, p.Prime → p ∣ zSet j core.q core.bufferImage →
        p ≠ core.q → p ∉ core.bufferImage → core.a p = 0 := by
    intro p hp hp_dvd hp_ne_q hp_notin_S
    by_contra h_nz
    have hp_dvd_j : p ∣ j := hp_dvd.trans hz_dvd_j
    have hpk : p ≤ k := (Nat.le_of_dvd hj_pos hp_dvd_j).trans hj_le
    rcases core.struct_split p hp hp.one_lt.le hpk h_nz with hpq | hb_or_hs
    · exact hp_ne_q hpq
    · rcases hb_or_hs with hb | hs
      · exact hp_notin_S hb
      · unfold WideCoverBuildCore.scaffoldImage at hs
        rw [Finset.mem_image] at hs
        obtain ⟨t, _, ht_eq⟩ := hs
        have h_scaf := core.smq.toScaffoldMatching.scaffold_in_range t
        have h_p_half : k / 2 < p := by
          have hY_le_half := core.Y_le_half
          rw [← ht_eq]
          omega
        have hj_eq : j = p :=
          eq_of_prime_gt_half_dvd_le_k_local hp h_p_half hj_pos hj_le hp_dvd_j
        apply h_no_scaffold_collision t
        rw [hj_eq, ht_eq]
  exact zSet_dvd_innerB_zero_part_local core.a core.bufferImage
    hj_pos hj_le hz_pos hz_dvd_j hzero hq_or_S

theorem outerB_ge_B_from_core_anchor_local
    {B k : ℕ} (hk : 3 ≤ k) (core : WideCoverBuildCore B k)
    (j : ℕ) (hj : 1 ≤ j) (hjk : j ≤ k)
    (h_excess_empty : scaffoldExcess k core.a j = ∅)
    (h_anchor : j % core.q = 1) :
    B ≤ outerB k core.a j := by
  have hqB : B ≤ core.q := core.m_le_q
  have hq_prime : core.q.Prime := core.q_prime
  have hqk : core.q ≤ k := by
    have := core.q_le_k_half
    have := Nat.div_le_self k 2
    omega
  have h_aq : core.a core.q = 1 := by
    show combinedResidue core.q core.bd core.smq.toScaffoldMatching core.q = 1
    exact combinedResidue_at_q core.bd core.smq.toScaffoldMatching
  have hjmod : j % core.q = core.a core.q := by rw [h_aq, h_anchor]
  exact outerB_ge_B_from_residue_match_local hk core.a j hj hjk h_excess_empty
    core.q hq_prime hqB hqk hjmod

theorem outerB_ge_B_from_core_buffer_local
    {B k : ℕ} (hk : 3 ≤ k) (core : WideCoverBuildCore B k)
    (j : ℕ) (hj : 1 ≤ j) (hjk : j ≤ k)
    (h_excess_empty : scaffoldExcess k core.a j = ∅)
    (d : core.bd.D) (h_buffer : j % core.bd.buffer d = d.val) :
    B ≤ outerB k core.a j := by
  set p := core.bd.buffer d
  have hp_prime : p.Prime := core.bd.buffer_prime d
  have hp_in_range : core.Y * core.Y < p ∧ p ≤ 2 * core.Y * core.Y :=
    core.bd.buffer_in_range d
  have hYsq : 6 * core.Y * core.Y ≤ k := core.Y_sq_small
  have hpk : p ≤ k := by
    have h1 : 2 * core.Y * core.Y ≤ 3 * (core.Y * core.Y) := by ring_nf; linarith
    have : p ≤ 3 * (core.Y * core.Y) := le_trans hp_in_range.2 h1
    have h2 : 3 * (core.Y * core.Y) ≤ 6 * core.Y * core.Y := by ring_nf; linarith
    omega
  have hBp : B ≤ p := by
    have hq_le_Y : core.q ≤ core.Y := by
      calc core.q = core.q ^ 1 := (pow_one core.q).symm
        _ ≤ core.q ^ 20 := Nat.pow_le_pow_right core.q_prime.pos (by omega)
        _ ≤ core.Y := core.q_pow20_le_Y
    have hY_le_YY : core.Y ≤ core.Y * core.Y :=
      Nat.le_mul_of_pos_left core.Y (by have := core.Y_pos; omega)
    have hB_le_YY : B ≤ core.Y * core.Y := core.m_le_q.trans (hq_le_Y.trans hY_le_YY)
    omega
  have h_d_pos : 1 ≤ d.val := by
    have hd_in : d.val ∈ core.bd.D := d.property
    have h_sub : core.bd.D ⊆ Finset.Icc 1 core.Y := core.bd.D_subset
    have h_in_Icc : d.val ∈ Finset.Icc 1 core.Y := h_sub hd_in
    exact (Finset.mem_Icc.mp h_in_Icc).1
  have h_buf_ne_q : core.bd.buffer d ≠ core.q := core.buffer_neq_q d
  have h_aBp : core.a p = d.val := by
    show combinedResidue core.q core.bd core.smq.toScaffoldMatching p = d.val
    exact combinedResidue_at_buffer core.bd core.smq.toScaffoldMatching d
      h_buf_ne_q h_d_pos
  have hjmod : j % p = core.a p := by rw [h_aBp, h_buffer]
  exact outerB_ge_B_from_residue_match_local hk core.a j hj hjk h_excess_empty
    p hp_prime hBp hpk hjmod

theorem outerB_ge_B_from_core_scaffold_local
    {B k : ℕ} (hk : 3 ≤ k) (core : WideCoverBuildCore B k)
    (j : ℕ) (hj : 1 ≤ j) (hjk : j ≤ k)
    (h_excess_empty : scaffoldExcess k core.a j = ∅)
    (t : core.smq.T) (h_scaffold : j % core.smq.scaffold t = t.val) :
    B ≤ outerB k core.a j := by
  set p := core.smq.scaffold t
  have hp_prime : p.Prime := core.smq.scaffold_prime t
  have hp_in_range : k - core.Y / 2 < p ∧ p ≤ k :=
    core.smq.scaffold_in_range t
  have hpk : p ≤ k := hp_in_range.2
  have hY_le_half := core.Y_le_half
  have hY_pos := core.Y_pos
  have hBp : B ≤ p := by
    have hq_le_Y : core.q ≤ core.Y := by
      calc core.q = core.q ^ 1 := (pow_one core.q).symm
        _ ≤ core.q ^ 20 := Nat.pow_le_pow_right core.q_prime.pos (by omega)
        _ ≤ core.Y := core.q_pow20_le_Y
    have hBq : B ≤ core.q := core.m_le_q
    have hBY : B ≤ core.Y := hBq.trans hq_le_Y
    have h_lo := hp_in_range.1
    omega
  have h_scaf_ne_q : core.smq.scaffold t ≠ core.q := core.scaffold_neq_q t
  have h_buf_zero : core.bd.residue (core.smq.scaffold t) = 0 := by
    unfold BufferData.residue
    by_cases hex : ∃ d : core.bd.D, core.bd.buffer d = core.smq.scaffold t
    · obtain ⟨d, hd⟩ := hex
      exfalso
      exact core.scaffold_neq_buffer t d hd.symm
    · rw [dif_neg hex]
  have h_aBp : core.a p = t.val := by
    show combinedResidue core.q core.bd core.smq.toScaffoldMatching p = t.val
    exact combinedResidue_at_scaffold core.bd core.smq.toScaffoldMatching t
      h_scaf_ne_q h_buf_zero
  have hjmod : j % p = core.a p := by rw [h_aBp, h_scaffold]
  exact outerB_ge_B_from_residue_match_local hk core.a j hj hjk h_excess_empty
    p hp_prime hBp hpk hjmod

theorem WideCoverBuildCore.outerB_ge_B_i_from_matching_local
    {B k : ℕ} (hk : 3 ≤ k) (core : WideCoverBuildCore B k)
    (hD_eq : core.bd.D = smallDeficientSet B core.Y core.q)
    (hT_eq :
      core.smq.T =
        (residualSet B core.X core.Y core.q core.bd.total).filter
          (fun t => t ≤ k))
    (hk_le_2X : k ≤ 2 * core.X)
    (h_zSet_aux :
      ∀ j, 1 ≤ j → j ≤ k →
        zSet j core.q core.bufferImage ∣ j ∧
        0 < zSet j core.q core.bufferImage ∧
        ∀ p, p.Prime → p ∣ zSet j core.q core.bufferImage →
          p ≠ core.q ∧ p ∉ core.bufferImage)
    (h_zSet_eq_total :
      ∀ j, 1 ≤ j → j ≤ k →
        zSet j core.q core.bufferImage =
        zSet j core.q ((smallDeficientSet B core.Y core.q).image core.bd.total)) :
    ∀ i : Fin k,
      B ≤ outerB k core.a (k - i.val) := by
  classical
  intro i
  set j := k - i.val with hj_def
  have hj_pos : 1 ≤ j := by
    have hi := i.isLt
    simp only [hj_def]; omega
  have hj_le : j ≤ k := by simp only [hj_def]; omega
  have hSE_all := core.scaffoldExcess_empty i.val
  have hSE_at_j : ∀ p,
      p ∉ scaffoldExcess k core.a j := by
    intro p
    have := hSE_all p
    exact this
  have hSE : scaffoldExcess k core.a j = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    exact hSE_at_j
  by_cases h_anchor : j % core.q = 1
  · exact outerB_ge_B_from_core_anchor_local hk core j hj_pos hj_le hSE h_anchor
  by_cases h_buffer : ∃ d : core.bd.D, j % core.bd.buffer d = d.val
  · obtain ⟨d, hd⟩ := h_buffer
    exact outerB_ge_B_from_core_buffer_local hk core j hj_pos hj_le hSE d hd
  by_cases h_residual :
      j ∈ residualSet B core.X core.Y core.q core.bd.total
  · have hj_in_T : j ∈ core.smq.T := by
      rw [hT_eq, Finset.mem_filter]
      exact ⟨h_residual, hj_le⟩
    have hjmod_scaf : j % core.smq.scaffold ⟨j, hj_in_T⟩ =
        (⟨j, hj_in_T⟩ : core.smq.T).val := by
      have h_tval := core.smq.t_lt_scaffold ⟨j, hj_in_T⟩
      rw [Nat.mod_eq_of_lt h_tval]
    exact outerB_ge_B_from_core_scaffold_local hk core j hj_pos hj_le hSE
      ⟨j, hj_in_T⟩ hjmod_scaf
  · obtain ⟨h_zSet_dvd, h_zSet_pos, h_zSet_disjoint⟩ := h_zSet_aux j hj_pos hj_le
    have hz_ge : B ≤ zSet j core.q core.bufferImage := by
      by_contra hlt
      push_neg at hlt
      apply h_residual
      unfold residualSet
      rw [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨hj_pos, ?_⟩, ?_, h_anchor, ?_⟩
      · exact hj_le.trans hk_le_2X
      · rw [← h_zSet_eq_total j hj_pos hj_le]
        exact hlt
      · intro d hdD
        by_contra hmod
        apply h_buffer
        have hdD' : d ∈ core.bd.D := by rwa [hD_eq]
        refine ⟨⟨d, hdD'⟩, ?_⟩
        rw [core.bd.total_of_mem hdD'] at hmod
        exact hmod
    have h_no_scaffold_collision :
        ∀ t : core.smq.T, core.smq.scaffold t ≠ j := by
      intro t ht_eq
      have hmod := core.smq.scaffold_mod_q t
      rw [ht_eq] at hmod
      exact h_anchor hmod
    have hz_dvd_outer :
        zSet j core.q core.bufferImage ∣
          outerB k core.a j :=
      zSet_dvd_outerB_zero_case_local core hj_pos hj_le h_no_scaffold_collision
        h_zSet_pos h_zSet_dvd h_zSet_disjoint
    exact le_trans hz_ge
      (Nat.le_of_dvd
        (outerB_pos_of_a core.a j hj_pos hj_le)
        hz_dvd_outer)

noncomputable def ShiftSet (Y q : ℕ) : Finset ℕ :=
  (Finset.Ico 0 (Y / 2)).filter (fun h => h % q = q - 1)

theorem ShiftSet_card_lower {Y q : ℕ} (hq : 2 ≤ q) (hY_big : 8 * q ≤ Y) :
    Y / (4 * q) ≤ (ShiftSet Y q).card := by
  classical
  let f : ℕ → ℕ := fun r => (q - 1) + q * r
  have hq_pos : 0 < q := by omega
  have hf_inj : Set.InjOn f (Finset.Ico 0 (Y / (4 * q))) := by
    intro a _ b _ hab
    have h : q * a = q * b := by
      have ha : f a = (q - 1) + q * a := rfl
      have hb : f b = (q - 1) + q * b := rfl
      omega
    exact Nat.eq_of_mul_eq_mul_left hq_pos h
  have hkey : 4 * (q * (Y / (4 * q))) ≤ Y := by
    have e1 : 4 * (q * (Y / (4 * q))) = 4 * q * (Y / (4 * q)) := by ring
    rw [e1]
    exact Nat.mul_div_le Y (4 * q)
  have hq_div_le_Y4 : q * (Y / (4 * q)) ≤ Y / 4 :=
    (Nat.le_div_iff_mul_le (by norm_num : 0 < 4)).mpr (by linarith)
  have hY4_lt_Y2 : Y / 4 < Y / 2 := by
    have h1 := Nat.div_add_mod Y 4
    have h2 := Nat.div_add_mod Y 2
    omega
  have hf_mem : ∀ r ∈ Finset.Ico 0 (Y / (4 * q)), f r ∈ ShiftSet Y q := by
    intro r hr
    rw [Finset.mem_Ico] at hr
    obtain ⟨_, hr_lt⟩ := hr
    unfold ShiftSet
    rw [Finset.mem_filter, Finset.mem_Ico]
    refine ⟨⟨Nat.zero_le _, ?_⟩, ?_⟩
    · change (q - 1) + q * r < Y / 2
      have h3 : q * (r + 1) ≤ q * (Y / (4 * q)) := Nat.mul_le_mul_left q hr_lt
      have hexpand : q * (r + 1) = q + q * r := by ring
      rw [hexpand] at h3
      omega
    · change ((q - 1) + q * r) % q = q - 1
      rw [Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt (by omega)
  have h_image_sub : (Finset.Ico 0 (Y / (4 * q))).image f ⊆ ShiftSet Y q := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨r, hr, hrx⟩ := hx
    rw [← hrx]
    exact hf_mem r hr
  have h_card_ico : (Finset.Ico 0 (Y / (4 * q))).card = Y / (4 * q) := by simp
  calc Y / (4 * q)
      = (Finset.Ico 0 (Y / (4 * q))).card := h_card_ico.symm
    _ = ((Finset.Ico 0 (Y / (4 * q))).image f).card :=
        (Finset.card_image_of_injOn hf_inj).symm
    _ ≤ (ShiftSet Y q).card := Finset.card_le_card h_image_sub

theorem coprime_h_W_product
    {B Y q h : ℕ} {b : ℕ → ℕ}
    (hq_prime : q.Prime)
    (hb_prime : ∀ d ∈ smallDeficientSet B Y q, (b d).Prime)
    (hb_range : ∀ d ∈ smallDeficientSet B Y q, Y * Y < b d ∧ b d ≤ 2 * Y * Y)
    (hY_pos : 1 ≤ Y) (hh_lt : h < Y / 2) (hh_mod : h % q = q - 1) :
    Nat.Coprime h (W_product q B Y b) := by
  classical
  have hq_ge_2 : 2 ≤ q := hq_prime.two_le
  unfold W_product
  rw [Nat.coprime_mul_iff_right]
  refine ⟨?_, ?_⟩
  · rw [Nat.coprime_comm, hq_prime.coprime_iff_not_dvd]
    intro hdvd
    have : h % q = 0 := Nat.mod_eq_zero_of_dvd hdvd
    omega
  · rw [Nat.coprime_prod_right_iff]
    intro d hd
    have hbd_prime := hb_prime d hd
    have hbd_range := hb_range d hd
    have hh_pos : 0 < h := by
      rcases Nat.eq_zero_or_pos h with h0 | hpos
      · subst h0
        simp at hh_mod
        omega
      · exact hpos
    rw [Nat.coprime_comm, hbd_prime.coprime_iff_not_dvd]
    intro hdvd
    have hbd_le_h : b d ≤ h := Nat.le_of_dvd hh_pos hdvd
    have hY_le_YY : Y ≤ Y * Y := Nat.le_mul_of_pos_left _ (by omega)
    omega

theorem W_product_polylog_bound
    {B q L Aq Csw : ℕ} {b : ℕ → ℕ}
    (hD : (smallDeficientSet B (q ^ 20) q).card ≤ 21 * B)
    (hq_le : q ≤ 2 * L ^ Aq)
    (hL_ge_2 : 2 ≤ L)
    (hb_le : ∀ d ∈ smallDeficientSet B (q ^ 20) q, b d ≤ 2 * (q ^ 20) * (q ^ 20))
    (hCsw_big : 1000 * B * Aq + Aq + 1000 * B + 200 ≤ Csw) :
    W_product q B (q ^ 20) b ≤ L ^ Csw := by
  classical
  unfold W_product
  set D := smallDeficientSet B (q ^ 20) q
  set n := D.card with hn_def
  have hn_le : n ≤ 21 * B := hD
  have hbd_le_q40 : ∀ d ∈ D, b d ≤ 2 * q ^ 40 := by
    intro d hd
    have hbd := hb_le d hd
    have heq : 2 * q ^ 20 * q ^ 20 = 2 * q ^ 40 := by
      have : q ^ 20 * q ^ 20 = q ^ 40 := by rw [← pow_add]
      linarith
    linarith
  have hprod_le_pow : ∏ d ∈ D, b d ≤ (2 * q ^ 40) ^ n := by
    calc ∏ d ∈ D, b d
        ≤ ∏ _d ∈ D, (2 * q ^ 40) :=
          Finset.prod_le_prod (fun _ _ => Nat.zero_le _) hbd_le_q40
      _ = (2 * q ^ 40) ^ n := by rw [Finset.prod_const]
  have hq40_le : q ^ 40 ≤ 2 ^ 40 * L ^ (40 * Aq) := by
    have h1 : q ^ 40 ≤ (2 * L ^ Aq) ^ 40 := Nat.pow_le_pow_left hq_le 40
    have h2 : (2 * L ^ Aq) ^ 40 = 2 ^ 40 * L ^ (40 * Aq) := by
      rw [mul_pow, ← pow_mul]; ring_nf
    linarith
  have h2q40_le : 2 * q ^ 40 ≤ 2 ^ 41 * L ^ (40 * Aq) := by
    calc 2 * q ^ 40 ≤ 2 * (2 ^ 40 * L ^ (40 * Aq)) := Nat.mul_le_mul_left 2 hq40_le
      _ = 2 ^ 41 * L ^ (40 * Aq) := by ring
  have hprodpow_le :
      (2 * q ^ 40) ^ n ≤ 2 ^ (41 * n) * L ^ (40 * Aq * n) := by
    calc (2 * q ^ 40) ^ n
        ≤ (2 ^ 41 * L ^ (40 * Aq)) ^ n := Nat.pow_le_pow_left h2q40_le n
      _ = (2 ^ 41) ^ n * (L ^ (40 * Aq)) ^ n := by rw [mul_pow]
      _ = 2 ^ (41 * n) * L ^ (40 * Aq * n) := by rw [← pow_mul, ← pow_mul]
  have hprod_final : ∏ d ∈ D, b d ≤ 2 ^ (41 * n) * L ^ (40 * Aq * n) :=
    hprod_le_pow.trans hprodpow_le
  have hW_le :
      q * ∏ d ∈ D, b d ≤ 2 ^ (41 * n + 1) * L ^ (Aq + 40 * Aq * n) := by
    calc q * ∏ d ∈ D, b d
        ≤ (2 * L ^ Aq) * (2 ^ (41 * n) * L ^ (40 * Aq * n)) :=
          Nat.mul_le_mul hq_le hprod_final
      _ = 2 ^ (41 * n + 1) * L ^ (Aq + 40 * Aq * n) := by
          rw [pow_succ, pow_add]; ring
  have h2_le_L_pow : ∀ k : ℕ, 2 ^ k ≤ L ^ k :=
    fun k => Nat.pow_le_pow_left hL_ge_2 k
  have h_two_pow_le : 2 ^ (41 * n + 1) ≤ L ^ (41 * n + 1) := h2_le_L_pow _
  have hL_pos : 1 ≤ L := by omega
  have hW_le_Lpow :
      q * ∏ d ∈ D, b d ≤ L ^ (41 * n + 1 + Aq + 40 * Aq * n) := by
    calc q * ∏ d ∈ D, b d
        ≤ 2 ^ (41 * n + 1) * L ^ (Aq + 40 * Aq * n) := hW_le
      _ ≤ L ^ (41 * n + 1) * L ^ (Aq + 40 * Aq * n) :=
          Nat.mul_le_mul_right _ h_two_pow_le
      _ = L ^ (41 * n + 1 + Aq + 40 * Aq * n) := by
          rw [← pow_add]; ring_nf
  have hexp_le : 41 * n + 1 + Aq + 40 * Aq * n ≤ Csw := by
    have h1 : 41 * n ≤ 41 * (21 * B) := Nat.mul_le_mul_left 41 hn_le
    have h2 : 40 * Aq * n ≤ 40 * Aq * (21 * B) := Nat.mul_le_mul_left (40 * Aq) hn_le
    have e1 : 41 * (21 * B) = 861 * B := by ring
    have e2 : 40 * Aq * (21 * B) = 840 * Aq * B := by ring
    have e3 : 840 * Aq * B = 840 * B * Aq := by ring
    rw [e1] at h1
    rw [e2, e3] at h2
    nlinarith [hn_le, hCsw_big, h1, h2]
  calc q * ∏ d ∈ D, b d
      ≤ L ^ (41 * n + 1 + Aq + 40 * Aq * n) := hW_le_Lpow
    _ ≤ L ^ Csw := Nat.pow_le_pow_right hL_pos hexp_le

theorem Y_polylog_bound {q L Aq Csw : ℕ}
    (hq_le : q ≤ 2 * L ^ Aq) (hL_ge_2 : 2 ≤ L)
    (hCsw_big : 20 * Aq + 30 ≤ Csw) :
    q ^ 20 ≤ L ^ Csw := by
  have h1 : q ^ 20 ≤ (2 * L ^ Aq) ^ 20 := Nat.pow_le_pow_left hq_le 20
  have h2 : (2 * L ^ Aq) ^ 20 = 2 ^ 20 * L ^ (20 * Aq) := by
    rw [mul_pow, ← pow_mul]; ring_nf
  have h3 : (2 : ℕ) ^ 20 ≤ L ^ 20 := Nat.pow_le_pow_left hL_ge_2 20
  have hL_pos : 1 ≤ L := by omega
  have h4 : 2 ^ 20 * L ^ (20 * Aq) ≤ L ^ 20 * L ^ (20 * Aq) :=
    Nat.mul_le_mul_right _ h3
  have h5 : L ^ 20 * L ^ (20 * Aq) = L ^ (20 + 20 * Aq) := by rw [← pow_add]
  have hexp : 20 + 20 * Aq ≤ Csw := by omega
  calc q ^ 20
      ≤ (2 * L ^ Aq) ^ 20 := h1
    _ = 2 ^ 20 * L ^ (20 * Aq) := h2
    _ ≤ L ^ 20 * L ^ (20 * Aq) := h4
    _ = L ^ (20 + 20 * Aq) := h5
    _ ≤ L ^ Csw := Nat.pow_le_pow_right hL_pos hexp

theorem shifted_prime_injection_to_candidates
    {X Y q W h p : ℕ}
    (hq_prime : q.Prime) (hq_dvd_W : q ∣ W) (hW_pos : 0 < W)
    (_hY_pos : 1 ≤ Y) (hX_ge_h : h ≤ X)
    (hh_lt : h < Y / 2) (hh_mod_q : h % q = q - 1)
    (hp_mem : p ∈ (Finset.Ioc (X - h) (2 * X - h)).filter
            (fun p => p.Prime ∧ p % W = (W - h % W) % W)) :
    (p + h) ∈ ((Finset.Icc X (2 * X)).filter (fun k => W ∣ k)) ∧
    p ∈ CandidatePrimes (p + h) Y q := by
  classical
  rw [Finset.mem_filter, Finset.mem_Ioc] at hp_mem
  obtain ⟨⟨hp_lo, hp_hi⟩, hp_prime, hp_mod⟩ := hp_mem
  have hq_ge_2 : 2 ≤ q := hq_prime.two_le
  have hq_pos : 0 < q := by omega
  have hph_lo : X ≤ p + h := by omega
  have hph_hi : p + h ≤ 2 * X := by omega
  have h_mod_W_lt : h % W < W := Nat.mod_lt _ hW_pos
  have h_mod_W_le : h % W ≤ W := h_mod_W_lt.le
  have h_dvd : W ∣ (p + h) := by
    rw [Nat.dvd_iff_mod_eq_zero]
    have h_add : (p + h) % W = (p % W + h % W) % W := Nat.add_mod p h W
    rw [h_add, hp_mod]
    by_cases hzero : h % W = 0
    · rw [hzero]; simp [Nat.mod_self]
    · have hpos : 0 < h % W := Nat.pos_of_ne_zero hzero
      have hlt : W - h % W < W := by omega
      rw [Nat.mod_eq_of_lt hlt]
      have heq : W - h % W + h % W = W := Nat.sub_add_cancel h_mod_W_le
      rw [heq]
      exact Nat.mod_self W
  refine ⟨?_, ?_⟩
  · rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hph_lo, hph_hi⟩, h_dvd⟩
  · unfold CandidatePrimes
    rw [Finset.mem_filter, Finset.mem_Ioc]
    refine ⟨⟨?_, ?_⟩, hp_prime, ?_⟩
    ·
      have : Y / 2 > h := hh_lt
      omega
    · omega
    ·
      have hq_dvd_ph : q ∣ (p + h) := dvd_trans hq_dvd_W h_dvd
      have hph_mod : (p + h) % q = 0 := Nat.mod_eq_zero_of_dvd hq_dvd_ph
      have hadd_q : (p + h) % q = (p % q + h % q) % q := Nat.add_mod p h q
      rw [hh_mod_q, hph_mod] at hadd_q
      have hpq_lt : p % q < q := Nat.mod_lt _ hq_pos
      have hpq_ge : 0 ≤ p % q := Nat.zero_le _
      have hmod_rewrite : (p % q + (q - 1)) % q = if p % q = 0 then q - 1 else p % q - 1 := by
        by_cases h_zero : p % q = 0
        · rw [h_zero]
          simp only [Nat.zero_add, if_true]
          exact Nat.mod_eq_of_lt (by omega)
        · have hge : 1 ≤ p % q := Nat.one_le_iff_ne_zero.mpr h_zero
          have hsum_eq : p % q + (q - 1) = (p % q - 1) + q * 1 := by omega
          rw [hsum_eq, Nat.add_mul_mod_self_left]
          rw [if_neg h_zero]
          exact Nat.mod_eq_of_lt (by omega)
      rw [hmod_rewrite] at hadd_q
      split_ifs at hadd_q with h_zero
      · omega
      · omega

theorem prime_supply_sum_lower_from_SW
    {B X Y q W Csw : ℕ} {b : ℕ → ℕ}
    (hq_prime : q.Prime) (hq_ge_2 : 2 ≤ q)
    (hY_eq : Y = q ^ 20)
    (hW_pos : 0 < W)
    (hW_le_X : W ≤ X)
    (hY_le_X : Y ≤ X)
    (hW_poly : W ≤ (Nat.log 2 X + 1) ^ Csw)
    (hY_poly : Y ≤ (Nat.log 2 X + 1) ^ Csw)
    (hY_big : 8 * q ≤ Y)
    (h_q_dvd_W : q ∣ W)
    (hbTotal_prime : ∀ d ∈ smallDeficientSet B Y q, (b d).Prime)
    (hbTotal_range : ∀ d ∈ smallDeficientSet B Y q, Y * Y < b d ∧ b d ≤ 2 * Y * Y)
    (hcop : ∀ h ∈ ShiftSet Y q, Nat.Coprime h W)
    (hSW : ∀ Q a h : ℕ, 2 ≤ Q → Q ≤ (Nat.log 2 X + 1) ^ Csw →
        h ≤ (Nat.log 2 X + 1) ^ Csw → Nat.Coprime a Q →
        ((Finset.Ioc (X - h) (2 * X - h)).filter
          (fun p => p.Prime ∧ p % Q = a % Q)).card
          ≥ X / (8 * Q * (Nat.log 2 X + 1)))
    (h_HX_bound :
      4 * H_X (M_B B) (2 * X) *
          (((Finset.Icc X (2 * X)).filter (W ∣ ·)).card)
        ≤ (ShiftSet Y q).card * (X / (8 * W * (Nat.log 2 X + 1)))) :
    4 * H_X (M_B B) (2 * X) *
        (((Finset.Icc X (2 * X)).filter (W ∣ ·)).card)
      ≤
    ∑ k ∈ ((Finset.Icc X (2 * X)).filter (W ∣ ·)),
      (CandidatePrimes k Y q).card := by
  classical
  set Ω := (Finset.Icc X (2 * X)).filter (W ∣ ·) with hΩ_def
  set Pset : ℕ → Finset ℕ := fun h =>
    (Finset.Ioc (X - h) (2 * X - h)).filter
      (fun p => p.Prime ∧ p % W = (W - h % W) % W) with hPset_def
  set L := Nat.log 2 X + 1 with hL_def
  have hW_ge_2 : 2 ≤ W := by
    have : q ≤ W := Nat.le_of_dvd hW_pos h_q_dvd_W
    omega
  have hY_pos : 1 ≤ Y := by
    have h2Y : 2 ≤ Y := by
      rw [hY_eq]
      calc 2 ≤ q := hq_ge_2
        _ = q ^ 1 := (pow_one q).symm
        _ ≤ q ^ 20 := Nat.pow_le_pow_right hq_prime.pos (by omega)
    omega
  have h_each : ∀ h ∈ ShiftSet Y q, X / (8 * W * L) ≤ (Pset h).card := by
    intro h hh
    have hh_filter := Finset.mem_filter.mp hh
    obtain ⟨hh_ico, hh_mod_q⟩ := hh_filter
    rw [Finset.mem_Ico] at hh_ico
    have hh_lt : h < Y / 2 := hh_ico.2
    have hh_le_Y : h ≤ Y := by
      have hY_half : Y / 2 ≤ Y := Nat.div_le_self _ _
      omega
    have hh_le_LCsw : h ≤ L ^ Csw := hh_le_Y.trans hY_poly
    have hcop_h : Nat.Coprime h W := hcop h hh
    have h_mod_le : h % W ≤ W := (Nat.mod_lt _ hW_pos).le
    have hcop_hmodW : Nat.Coprime (h % W) W := by
      rw [Nat.Coprime, ← Nat.gcd_rec, Nat.gcd_comm]
      exact hcop_h
    have hcop_sub : Nat.Coprime (W - h % W) W :=
      (Nat.coprime_self_sub_left h_mod_le).mpr hcop_hmodW
    have hSW_h := hSW W (W - h % W) h hW_ge_2 hW_poly hh_le_LCsw hcop_sub
    simpa [Pset] using hSW_h
  have h_sum_le :
      ∑ h ∈ ShiftSet Y q, (Pset h).card ≤
      ∑ k ∈ Ω, (CandidatePrimes k Y q).card := by
    classical
    set T : Finset (Σ _ : ℕ, ℕ) :=
      (ShiftSet Y q).sigma (fun h => Pset h) with hT_def
    set T' : Finset (Σ _ : ℕ, ℕ) :=
      Ω.sigma (fun k => CandidatePrimes k Y q) with hT'_def
    have hT_card : T.card = ∑ h ∈ ShiftSet Y q, (Pset h).card := by
      rw [hT_def]; exact Finset.card_sigma _ _
    have hT'_card : T'.card = ∑ k ∈ Ω, (CandidatePrimes k Y q).card := by
      rw [hT'_def]; exact Finset.card_sigma _ _
    let φ : (Σ _ : ℕ, ℕ) → (Σ _ : ℕ, ℕ) := fun x => ⟨x.2 + x.1, x.2⟩
    have hmap : Set.MapsTo φ (T : Set _) (T' : Set _) := by
      intro x hx
      have hx' : x ∈ T := hx
      rw [hT_def, Finset.mem_sigma] at hx'
      obtain ⟨hh, hp⟩ := hx'
      have hh_filter := Finset.mem_filter.mp hh
      obtain ⟨hh_ico, hh_mod_q⟩ := hh_filter
      rw [Finset.mem_Ico] at hh_ico
      have hh_lt : x.1 < Y / 2 := hh_ico.2
      have hh_le_Y : x.1 ≤ Y := by
        have hY_half : Y / 2 ≤ Y := Nat.div_le_self _ _
        omega
      have hh_le_X : x.1 ≤ X := hh_le_Y.trans hY_le_X
      have hp' :
          x.2 ∈ (Finset.Ioc (X - x.1) (2 * X - x.1)).filter
            (fun p => p.Prime ∧ p % W = (W - x.1 % W) % W) := by
        simpa [Pset] using hp
      have hres := shifted_prime_injection_to_candidates
        (X := X) (Y := Y) (q := q) (W := W) (h := x.1) (p := x.2)
        hq_prime h_q_dvd_W hW_pos hY_pos hh_le_X hh_lt hh_mod_q hp'
      obtain ⟨hmem_Ω, hmem_cand⟩ := hres
      have hφ_mem : φ x ∈ T' := by
        rw [hT'_def, Finset.mem_sigma]
        exact ⟨hmem_Ω, hmem_cand⟩
      exact hφ_mem
    have hinj : Set.InjOn φ (T : Set _) := by
      intro x _ y _ hxy
      have h1 : x.2 + x.1 = y.2 + y.1 := by
        have := congrArg Sigma.fst hxy
        simpa [φ] using this
      have h2 : x.2 = y.2 := by
        have := (Sigma.mk.inj_iff.mp hxy).2
        exact eq_of_heq this
      have h3 : x.1 = y.1 := by
        have : x.2 + x.1 = x.2 + y.1 := by rw [h1, h2]
        omega
      rcases x with ⟨x1, x2⟩
      rcases y with ⟨y1, y2⟩
      simp_all
    have hcard_le : T.card ≤ T'.card := Finset.card_le_card_of_injOn φ hmap hinj
    rw [hT_card, hT'_card] at hcard_le
    exact hcard_le
  calc 4 * H_X (M_B B) (2 * X) * Ω.card
      ≤ (ShiftSet Y q).card * (X / (8 * W * L)) := h_HX_bound
    _ = ∑ _h ∈ ShiftSet Y q, X / (8 * W * L) := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ h ∈ ShiftSet Y q, (Pset h).card := Finset.sum_le_sum h_each
    _ ≤ ∑ k ∈ Ω, (CandidatePrimes k Y q).card := h_sum_le

structure ScaffoldScaleBounds (B K Y₀ k₀ Xsw : ℕ) where
  X : ℕ
  X_ge_K : K ≤ X
  X_ge_SW : Xsw ≤ X
  X_ge_100 : 100 ≤ X
  consts_le_log4 :
    max B (max Y₀ (max k₀ (max K (B * 2 ^ (21 * B + 1))))) ≤
      (Nat.log 2 X + 1) ^ 4
  polylog_dominates_bad :
    1000000 * (B + 1) *
      (Nat.log 2 X + 1) ^
        (3000 * (B + 1) * (M_B B + 20) + 3000) ≤ X

theorem exists_scaffold_scale_bounds (B K Y₀ k₀ Xsw : ℕ) :
    Nonempty (ScaffoldScaleBounds B K Y₀ k₀ Xsw) := by
  obtain ⟨Nconst, hNconst⟩ :=
    const_le_log_pow_4
      (max B (max Y₀ (max k₀ (max K (B * 2 ^ (21 * B + 1))))))
  obtain ⟨Npoly, hNpoly⟩ :=
    polylog_le_self (1000000 * (B + 1))
      (3000 * (B + 1) * (M_B B + 20) + 3000)
  let X : ℕ := max 100 (max Xsw (max K (max Nconst Npoly)))
  refine ⟨X, ?_, ?_, ?_, ?_, ?_⟩
  ·
    have : K ≤ max K (max Nconst Npoly) := le_max_left _ _
    exact this.trans ((le_max_right _ _).trans (le_max_right _ _))
  ·
    have : Xsw ≤ max Xsw (max K (max Nconst Npoly)) := le_max_left _ _
    exact this.trans (le_max_right _ _)
  ·
    exact le_max_left _ _
  ·
    apply hNconst
    have : Nconst ≤ max Nconst Npoly := le_max_left _ _
    exact this.trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans (le_max_right _ _)))
  ·
    apply hNpoly
    have : Npoly ≤ max Nconst Npoly := le_max_right _ _
    exact this.trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans (le_max_right _ _)))

theorem wcbd_Csw_le_E_big (B Aq : ℕ)
    (hAq_def : Aq + 1 = 21 * B + 16) :
    2000 * (B + 1) * (Aq + 1) + 2000 ≤
      3000 * (B + 1) * (21 * B + 20) + 3000 := by
  rw [hAq_def]
  nlinarith [Nat.zero_le B, sq_nonneg B]

theorem wcbd_Csw_succ_le_E_big (B Aq : ℕ)
    (hAq_def : Aq + 1 = 21 * B + 16) :
    2000 * (B + 1) * (Aq + 1) + 2000 + 1 ≤
      3000 * (B + 1) * (21 * B + 20) + 3000 := by
  rw [hAq_def]
  nlinarith [Nat.zero_le B, sq_nonneg B]

theorem wcbd_40Aq_le_E_big (B Aq : ℕ)
    (hAq_def : Aq = 21 * B + 15) :
    40 * (Aq + 1) + 3 ≤ 3000 * (B + 1) * (21 * B + 20) + 3000 := by
  rw [hAq_def]
  nlinarith [Nat.zero_le B, sq_nonneg B]

theorem wcbd_Aq2_le_E_big (B Aq : ℕ)
    (hAq_def : Aq = 21 * B + 15) :
    Aq + 2 ≤ 3000 * (B + 1) * (21 * B + 20) + 3000 := by
  rw [hAq_def]
  nlinarith [Nat.zero_le B, sq_nonneg B]

theorem wcbd_3072_le_q20
    {B L Aq q : ℕ}
    (hAq_eq : Aq = 21 * B + 15)
    (hL_pos : 0 < L)
    (hL_ge_2 : 2 ≤ L)
    (hL_ge_7 : 7 ≤ L)
    (hq_ge_Qscale : L ^ Aq ≤ q)
    (hq_le_L_pow_Aq1 : q ≤ L ^ (Aq + 1)) :
    3072 * L ^ (21 * B + 10) * (4 * q) ≤ q ^ 20 := by
  have h_q_le_L_21B16 : q ≤ L ^ (21 * B + 16) := by
    have : Aq + 1 = 21 * B + 16 := by omega
    rw [this] at hq_le_L_pow_Aq1
    exact hq_le_L_pow_Aq1
  have hq20_ge : L ^ (420 * B + 300) ≤ q ^ 20 := by
    have h1 : (L ^ Aq) ^ 20 ≤ q ^ 20 := Nat.pow_le_pow_left hq_ge_Qscale 20
    have h2 : (L ^ Aq) ^ 20 = L ^ (Aq * 20) := by rw [← pow_mul]
    have h3 : Aq * 20 = (21 * B + 15) * 20 := by rw [hAq_eq]
    have h4 : (21 * B + 15) * 20 = 420 * B + 300 := by ring
    rw [h3, h4] at h2
    rw [← h2]; exact h1
  calc 3072 * L ^ (21 * B + 10) * (4 * q)
      ≤ 3072 * L ^ (21 * B + 10) * (4 * L ^ (21 * B + 16)) := by
        have h1 : 4 * q ≤ 4 * L ^ (21 * B + 16) :=
          Nat.mul_le_mul_left _ h_q_le_L_21B16
        exact Nat.mul_le_mul_left _ h1
    _ = 12288 * (L ^ (21 * B + 10) * L ^ (21 * B + 16)) := by ring
    _ = 12288 * L ^ (42 * B + 26) := by
        rw [← pow_add]; congr 2; ring
    _ ≤ L ^ 5 * L ^ (42 * B + 26) := by
        have h_12288_le_L5 : (12288 : ℕ) ≤ L ^ 5 := by
          calc (12288 : ℕ) ≤ 16807 := by norm_num
            _ = 7 ^ 5 := by norm_num
            _ ≤ L ^ 5 := Nat.pow_le_pow_left hL_ge_7 _
        exact Nat.mul_le_mul_right _ h_12288_le_L5
    _ = L ^ (42 * B + 31) := by rw [← pow_add]; congr 1; ring
    _ ≤ L ^ (420 * B + 300) := by
        apply Nat.pow_le_pow_right hL_pos
        nlinarith [Nat.zero_le B]
    _ ≤ q ^ 20 := hq20_ge

theorem wcbd_6YY_le_LE
    {B L Aq q : ℕ}
    (hAq_eq : Aq = 21 * B + 15)
    (hL_pos : 0 < L)
    (hL_ge_2 : 2 ≤ L)
    (hq_le_L_pow_Aq1 : q ≤ L ^ (Aq + 1)) :
    6 * q ^ 20 * q ^ 20 ≤
      L ^ (3000 * (B + 1) * (21 * B + 20) + 3000) := by
  set E_big : ℕ :=
    3000 * (B + 1) * (21 * B + 20) + 3000 with hE_big_def
  have hY_tight : q ^ 20 ≤ L ^ (20 * (Aq + 1)) := by
    calc q ^ 20 ≤ (L ^ (Aq + 1)) ^ 20 := Nat.pow_le_pow_left hq_le_L_pow_Aq1 _
      _ = L ^ ((Aq + 1) * 20) := by rw [← pow_mul]
      _ = L ^ (20 * (Aq + 1)) := by ring_nf
  have hYY_le :
      6 * q ^ 20 * q ^ 20 ≤
        6 * L ^ (20 * (Aq + 1)) * L ^ (20 * (Aq + 1)) := by
    have h1 : 6 * q ^ 20 ≤ 6 * L ^ (20 * (Aq + 1)) :=
      Nat.mul_le_mul_left 6 hY_tight
    exact Nat.mul_le_mul h1 hY_tight
  have h6_le : (6 : ℕ) ≤ L ^ 3 := by
    have : (8 : ℕ) ≤ L ^ 3 := by
      calc (8 : ℕ) = 2 ^ 3 := by norm_num
        _ ≤ L ^ 3 := Nat.pow_le_pow_left hL_ge_2 _
    omega
  have hYY_le2 :
      6 * L ^ (20 * (Aq + 1)) * L ^ (20 * (Aq + 1)) ≤
        L ^ (40 * (Aq + 1) + 3) := by
    calc 6 * L ^ (20 * (Aq + 1)) * L ^ (20 * (Aq + 1))
        ≤ L ^ 3 * L ^ (20 * (Aq + 1)) * L ^ (20 * (Aq + 1)) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h6_le)
      _ = L ^ (3 + 20 * (Aq + 1) + 20 * (Aq + 1)) := by
          rw [← pow_add, ← pow_add]
      _ = L ^ (40 * (Aq + 1) + 3) := by ring_nf
  have hExp_le : 40 * (Aq + 1) + 3 ≤ E_big :=
    wcbd_40Aq_le_E_big B Aq hAq_eq
  have hYY_le3 : L ^ (40 * (Aq + 1) + 3) ≤ L ^ E_big :=
    Nat.pow_le_pow_right hL_pos hExp_le
  exact (hYY_le.trans hYY_le2).trans hYY_le3

theorem wcbd_HX_2X_bound
    {B X L : ℕ}
    (hL_def : L = Nat.log 2 X + 1)
    (hX_ge_100 : 100 ≤ X)
    (hHXconst_le_L4 : B * 2 ^ (21 * B + 1) ≤ L ^ 4)
    (hB_pos : 1 ≤ B) :
    H_X (M_B B) (2 * X) ≤ 16 * L ^ (21 * B + 9) := by
  rw [H_X_def]
  have h_log_2X : Nat.log 2 (2 * X) = Nat.log 2 X + 1 := by
    rw [show 2 * X = X * 2 from by ring]
    exact Nat.log_mul_base (by norm_num) (by omega)
  have h_eq : Nat.log 2 (2 * X) + 1 = L + 1 := by
    rw [hL_def, h_log_2X]
  rw [h_eq]
  have hM : M_B B + 5 = 21 * B + 5 := by unfold M_B; ring
  rw [hM]
  have h_succ : L + 1 ≤ 2 * L := by
    have hL_pos : 1 ≤ L := by
      rw [hL_def]; omega
    omega
  have h1 : (L + 1) ^ (21 * B + 5) ≤ (2 * L) ^ (21 * B + 5) :=
    Nat.pow_le_pow_left h_succ _
  have h2 : (2 * L) ^ (21 * B + 5) = 2 ^ (21 * B + 5) * L ^ (21 * B + 5) :=
    Nat.mul_pow _ _ _
  have h3 : 2 ^ (21 * B + 5) ≤ 16 * L ^ 4 := by
    have h2pow : 2 ^ (21 * B + 5) = 16 * 2 ^ (21 * B + 1) := by
      have : 21 * B + 5 = 4 + (21 * B + 1) := by ring
      rw [this, pow_add]; ring
    rw [h2pow]
    have h_2pow_le : 2 ^ (21 * B + 1) ≤ L ^ 4 := by
      have : 1 * 2 ^ (21 * B + 1) ≤ B * 2 ^ (21 * B + 1) :=
        Nat.mul_le_mul_right _ hB_pos
      rw [one_mul] at this
      exact this.trans hHXconst_le_L4
    exact Nat.mul_le_mul_left 16 h_2pow_le
  calc (L + 1) ^ (21 * B + 5)
      ≤ 2 ^ (21 * B + 5) * L ^ (21 * B + 5) := by rw [← h2]; exact h1
    _ ≤ 16 * L ^ 4 * L ^ (21 * B + 5) :=
        Nat.mul_le_mul_right _ h3
    _ = 16 * L ^ (21 * B + 9) := by
        have heq : L ^ 4 * L ^ (21 * B + 5) = L ^ (21 * B + 9) := by
          rw [← pow_add]; congr 1; ring
        rw [mul_assoc, heq]

theorem wcbd_residual_card_bound
    {B Y q Z : ℕ} {b : ℕ → ℕ}
    (hq_prime : q.Prime)
    (hb_prime : ∀ d ∈ smallDeficientSet B Y q, (b d).Prime)
    (hb_inj : Set.InjOn b (smallDeficientSet B Y q))
    (hb_ne_q : ∀ d ∈ smallDeficientSet B Y q, b d ≠ q)
    (hD_card_le : (smallDeficientSet B Y q).card ≤ 21 * B)
    (hHXconst_le : B * 2 ^ (21 * B + 1) ≤ (Nat.log 2 Z + 1) ^ 4)
    (hZ_ge_2 : 2 ≤ Z) :
    (residualSet B Z Y q b).card ≤ H_X (M_B B) Z := by
  refine residualSet_card_le_HX hq_prime hb_prime hb_inj hb_ne_q ?_
  have h_log_2Z : Nat.log 2 (2 * Z) = Nat.log 2 Z + 1 := by
    rw [show 2 * Z = Z * 2 from by ring]
    exact Nat.log_mul_base (by norm_num) (by omega)
  set LZ := Nat.log 2 Z + 1 with hLZ_def
  have hLZ_ge_2 : 2 ≤ LZ := by
    have h_log_pos : 1 ≤ Nat.log 2 Z := by
      rw [Nat.one_le_iff_ne_zero]
      intro h_eq
      have := Nat.log_eq_zero_iff.mp h_eq
      omega
    simp [hLZ_def]; omega
  have h_succL : LZ + 1 ≤ 2 * LZ := by omega
  have h_succL_pow :
      (LZ + 1) ^ ((smallDeficientSet B Y q).card + 1) ≤
        2 ^ ((smallDeficientSet B Y q).card + 1) *
          LZ ^ ((smallDeficientSet B Y q).card + 1) := by
    calc (LZ + 1) ^ ((smallDeficientSet B Y q).card + 1)
        ≤ (2 * LZ) ^ ((smallDeficientSet B Y q).card + 1) :=
          Nat.pow_le_pow_left h_succL _
      _ = 2 ^ ((smallDeficientSet B Y q).card + 1) *
            LZ ^ ((smallDeficientSet B Y q).card + 1) :=
          Nat.mul_pow _ _ _
  have hL1 : Nat.log 2 (2 * Z) + 1 = LZ + 1 := by omega
  have h_LHS_rearrange :
      B * (Nat.log 2 (2 * Z) + 1) *
          (Nat.log 2 (2 * Z) + 1) ^ (smallDeficientSet B Y q).card
        = B * (LZ + 1) ^ ((smallDeficientSet B Y q).card + 1) := by
    rw [hL1, pow_succ]; ring
  rw [h_LHS_rearrange]
  have hMB_eq : M_B B + 5 = 21 * B + 5 := by unfold M_B; ring
  have hH_X_unfold : H_X (M_B B) Z = LZ ^ (21 * B + 5) := by
    rw [H_X_def, ← hLZ_def, hMB_eq]
  rw [hH_X_unfold]
  calc B * (LZ + 1) ^ ((smallDeficientSet B Y q).card + 1)
      ≤ B * (2 ^ ((smallDeficientSet B Y q).card + 1) *
            LZ ^ ((smallDeficientSet B Y q).card + 1)) :=
        Nat.mul_le_mul_left B h_succL_pow
    _ = B * 2 ^ ((smallDeficientSet B Y q).card + 1) *
          LZ ^ ((smallDeficientSet B Y q).card + 1) := by ring
    _ ≤ B * 2 ^ (21 * B + 1) *
          LZ ^ ((smallDeficientSet B Y q).card + 1) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _
          (Nat.pow_le_pow_right (by norm_num)
            (by have := hD_card_le; omega)))
    _ ≤ LZ ^ 4 * LZ ^ ((smallDeficientSet B Y q).card + 1) :=
        Nat.mul_le_mul_right _ hHXconst_le
    _ = LZ ^ (4 + ((smallDeficientSet B Y q).card + 1)) := by
        rw [← pow_add]
    _ ≤ LZ ^ (21 * B + 5) :=
        Nat.pow_le_pow_right (by omega)
          (by have := hD_card_le; omega)

theorem wcbd_X_ge_step_direct
    {B L Aq q W : ℕ}
    (hB : 1 ≤ B)
    (hAq_def : Aq = 21 * B + 15)
    (hL_ge_2 : 2 ≤ L)
    (hq_le : q ≤ 2 * L ^ Aq)
    (hW_le_qpow : W ≤ q ^ (861 * B + 1)) :
    (2 * q ^ 20 + 1) * W ≤
      1000000 * (B + 1) *
        L ^ (3000 * (B + 1) * (M_B B + 20) + 3000) := by
  have hMB : M_B B = 21 * B := by unfold M_B; ring
  set E_big : ℕ := 3000 * (B + 1) * (M_B B + 20) + 3000 with hE_big_def
  by_cases hqz : q = 0
  · subst hqz
    have hWzero : W = 0 := by simpa using hW_le_qpow
    rw [hWzero]; omega
  have hq_pos : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr hqz
  have hq20 : 1 ≤ q ^ 20 := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero 20 hqz)
  have h1 : 2 * q ^ 20 + 1 ≤ 3 * q ^ 20 := by omega
  have h2 : 3 * q ^ 20 * W ≤ 3 * q ^ 20 * q ^ (861 * B + 1) :=
    Nat.mul_le_mul_left _ hW_le_qpow
  have h3 : q ^ 20 * q ^ (861 * B + 1) = q ^ (861 * B + 21) := by
    rw [← pow_add]; congr 1; omega
  have h4 : 3 * q ^ 20 * q ^ (861 * B + 1) = 3 * q ^ (861 * B + 21) := by
    rw [mul_assoc, h3]
  have hq_pow_le : q ^ (861 * B + 21) ≤ (2 * L ^ Aq) ^ (861 * B + 21) :=
    Nat.pow_le_pow_left hq_le _
  have hexp_eq : (2 * L ^ Aq) ^ (861 * B + 21)
      = 2 ^ (861 * B + 21) * L ^ (Aq * (861 * B + 21)) := by
    rw [mul_pow, ← pow_mul]
  have h2_le_L : 2 ^ (861 * B + 21) ≤ L ^ (861 * B + 21) :=
    Nat.pow_le_pow_left hL_ge_2 _
  have hL_pos : 1 ≤ L := by omega
  have hcomb : 2 ^ (861 * B + 21) * L ^ (Aq * (861 * B + 21)) ≤
      L ^ (861 * B + 21) * L ^ (Aq * (861 * B + 21)) :=
    Nat.mul_le_mul_right _ h2_le_L
  have hpow_add : L ^ (861 * B + 21) * L ^ (Aq * (861 * B + 21))
      = L ^ ((Aq + 1) * (861 * B + 21)) := by
    rw [← pow_add]; congr 1; ring
  have hexp_ineq : (Aq + 1) * (861 * B + 21) ≤ E_big := by
    rw [hAq_def, hE_big_def, hMB]
    nlinarith [Nat.zero_le B, hB]
  have hL_E : L ^ ((Aq + 1) * (861 * B + 21)) ≤ L ^ E_big :=
    Nat.pow_le_pow_right hL_pos hexp_ineq
  have h_qpow_le_LE :
      q ^ (861 * B + 21) ≤ L ^ E_big := by
    calc q ^ (861 * B + 21) ≤ (2 * L ^ Aq) ^ (861 * B + 21) := hq_pow_le
      _ = 2 ^ (861 * B + 21) * L ^ (Aq * (861 * B + 21)) := hexp_eq
      _ ≤ L ^ (861 * B + 21) * L ^ (Aq * (861 * B + 21)) := hcomb
      _ = L ^ ((Aq + 1) * (861 * B + 21)) := hpow_add
      _ ≤ L ^ E_big := hL_E
  have h_3_le_M : 3 ≤ 1000000 * (B + 1) := by
    have : 1 ≤ B + 1 := by omega
    nlinarith
  calc (2 * q ^ 20 + 1) * W
      ≤ 3 * q ^ 20 * W := Nat.mul_le_mul_right _ h1
    _ ≤ 3 * q ^ 20 * q ^ (861 * B + 1) := h2
    _ = 3 * q ^ (861 * B + 21) := h4
    _ ≤ 3 * L ^ E_big := Nat.mul_le_mul_left _ h_qpow_le_LE
    _ ≤ 1000000 * (B + 1) * L ^ E_big :=
        Nat.mul_le_mul_right _ h_3_le_M

theorem wcbd_bad_mass_strict_lt
    {B X Y q W : ℕ} (b : ℕ → ℕ)
    (hW_pos : 0 < W)
    (hY_lt_W : Y < W)
    (hX_big : (2 * Y + 1) * W ≤ X)
    (hUbig_card_le :
      (residualSet B (2 * X) Y q b).card ≤ H_X (M_B B) (2 * X))
    (hHX_pos : 0 < H_X (M_B B) (2 * X)) :
    (residualSet B (2 * X) Y q b).card * (Y / W + 2) * Y
        + H_X (M_B B) (2 * X) *
          (((Finset.Icc X (2 * X)).filter (W ∣ ·)).card)
        <
      4 * H_X (M_B B) (2 * X) *
          (((Finset.Icc X (2 * X)).filter (W ∣ ·)).card) := by
  classical
  set H := H_X (M_B B) (2 * X) with hH_def
  set Ω := (Finset.Icc X (2 * X)).filter (W ∣ ·) with hΩ_def
  set U := residualSet B (2 * X) Y q b with hU_def
  have hY_div_W : Y / W = 0 := Nat.div_eq_of_lt hY_lt_W
  have hW_le_X : W ≤ X := by
    have hY_pos_or_zero : 0 ≤ Y := Nat.zero_le _
    have hWmul : 1 * W ≤ (2 * Y + 1) * W :=
      Nat.mul_le_mul_right W (by omega)
    have : W ≤ X := by
      have : 1 * W ≤ X := hWmul.trans hX_big
      simpa using this
    exact this
  have hΩ_lower : X / W ≤ Ω.card := by
    rw [hΩ_def]
    exact multiples_in_long_interval_card_ge_no_dvd_local hW_pos hW_le_X
  have h2Y1_le_div : 2 * Y + 1 ≤ X / W :=
    (Nat.le_div_iff_mul_le hW_pos).mpr hX_big
  have h2Y1_le_Ω : 2 * Y + 1 ≤ Ω.card := h2Y1_le_div.trans hΩ_lower
  have h_strict : 2 * Y < 3 * Ω.card := by omega
  have hU_card_le_H : U.card ≤ H := hUbig_card_le
  have hLHS_eq : U.card * (Y / W + 2) * Y = U.card * 2 * Y := by
    rw [hY_div_W]
  rw [hLHS_eq]
  have hUH2Y : U.card * 2 * Y ≤ H * 2 * Y :=
    Nat.mul_le_mul_right Y (Nat.mul_le_mul_right 2 hU_card_le_H)
  have hStrict2 : H * (2 * Y) < H * (3 * Ω.card) :=
    (Nat.mul_lt_mul_left hHX_pos).mpr h_strict
  nlinarith [hUH2Y, hStrict2, Nat.zero_le H, Nat.zero_le Ω.card, h_strict]

theorem bufferImage_eq_image_total {k Y : ℕ} (bd : BufferData k Y) :
    bd.D.attach.image bd.buffer = bd.D.image bd.total := by
  classical
  ext p
  simp only [Finset.mem_image, Finset.mem_attach, true_and]
  constructor
  · rintro ⟨d, hd_eq⟩
    refine ⟨d.val, d.property, ?_⟩
    rw [bd.total_of_mem d.property]; exact hd_eq
  · rintro ⟨d, hd, hd_eq⟩
    refine ⟨⟨d, hd⟩, ?_⟩
    rw [← hd_eq, bd.total_of_mem hd]

theorem wcbd_buf_neq_q {k Y q : ℕ} (bd : BufferData k Y)
    (hq_le_Y_sq : q ≤ Y * Y) : ∀ d : bd.D, bd.buffer d ≠ q := by
  intro d h_eq
  have h_buf := (bd.buffer_in_range d).1
  rw [h_eq] at h_buf
  omega

theorem wcbd_scaffold_neq_q {k Y q : ℕ}
    (smq : ScaffoldMatchingQ k Y q)
    (hq_le_Y : q ≤ Y)
    (hY_le_half : 2 * Y ≤ k) : ∀ t : smq.T, smq.scaffold t ≠ q := by
  intro t h
  have h_lo := (smq.scaffold_in_range t).1
  rw [h] at h_lo
  have hY_half : Y / 2 ≤ Y := Nat.div_le_self _ _
  omega

theorem wcbd_scaffold_neq_buffer {k Y q : ℕ}
    (bd : BufferData k Y)
    (smq : ScaffoldMatchingQ k Y q)
    (h_2YY_Y_le_k : 2 * Y * Y + Y ≤ k) :
    ∀ t : smq.T, ∀ d : bd.D, smq.scaffold t ≠ bd.buffer d := by
  intro t d h
  have h_lo := (smq.scaffold_in_range t).1
  have h_buf := (bd.buffer_in_range d).2
  rw [h] at h_lo
  have hYd2 : Y / 2 ≤ Y := Nat.div_le_self _ _
  omega

theorem wcbd_W_poly_bound
    {B q L Aq Csw : ℕ} (b : ℕ → ℕ)
    (hAq_ge_5 : 5 ≤ Aq)
    (hCsw_def : Csw = 2000 * (B + 1) * (Aq + 1) + 2000)
    (hD_card_le_21B : (smallDeficientSet B (q ^ 20) q).card ≤ 21 * B)
    (hq_le_2Lpow : q ≤ 2 * L ^ Aq)
    (hL_ge_2 : 2 ≤ L)
    (hb_le : ∀ d ∈ smallDeficientSet B (q ^ 20) q, b d ≤ 2 * (q ^ 20) * (q ^ 20)) :
    W_product q B (q ^ 20) b ≤ L ^ Csw := by
  refine W_product_polylog_bound (B := B) (q := q) (L := L) (Aq := Aq) (Csw := Csw)
    (b := b) hD_card_le_21B hq_le_2Lpow hL_ge_2 hb_le ?_
  rw [hCsw_def]
  have h1 : 1000 * B * Aq + Aq + 1000 * B + 200 ≤
      2000 * B * Aq + 2 * Aq + 2000 * B + 200 := by
    nlinarith [hAq_ge_5, Nat.zero_le B, Nat.zero_le Aq]
  have h2 : 2000 * (B + 1) * (Aq + 1) + 2000 =
      2000 * B * Aq + 2000 * Aq + 2000 * B + 4000 := by ring
  omega

theorem wcbd_Y_poly_bound
    {B q L Aq Csw : ℕ}
    (hAq_ge_5 : 5 ≤ Aq)
    (hCsw_def : Csw = 2000 * (B + 1) * (Aq + 1) + 2000)
    (hq_le_2Lpow : q ≤ 2 * L ^ Aq)
    (hL_ge_2 : 2 ≤ L) :
    q ^ 20 ≤ L ^ Csw := by
  refine Y_polylog_bound (q := q) (L := L) (Aq := Aq) (Csw := Csw) hq_le_2Lpow hL_ge_2 ?_
  rw [hCsw_def]
  have h1 : 20 * Aq + 30 ≤ 2000 * (Aq + 1) := by
    have heq : 2000 * (Aq + 1) = 2000 * Aq + 2000 := by ring
    omega
  have h2 : 2000 * (Aq + 1) ≤ 2000 * (B + 1) * (Aq + 1) := by
    have hB1 : 1 ≤ B + 1 := by omega
    have hL : 2000 ≤ 2000 * (B + 1) := by
      have := Nat.mul_le_mul_left 2000 hB1
      linarith
    exact Nat.mul_le_mul_right (Aq + 1) hL
  linarith

theorem wcbd_Y_lt_W
    {B Y q W : ℕ} (b : ℕ → ℕ)
    (hB_ge_3 : 3 ≤ B)
    (hq_prime : q.Prime)
    (hq_ge_B : B ≤ q)
    (hq_ge_3 : 3 ≤ q)
    (hY_pos : 2 ≤ Y)
    (hq_pow20_le_Y : q ^ 20 ≤ Y)
    (hW_pos : 0 < W)
    (hb_dvd_W : ∀ d ∈ smallDeficientSet B Y q, b d ∣ W)
    (hb_range : ∀ d ∈ smallDeficientSet B Y q,
        Y * Y < b d ∧ b d ≤ 2 * Y * Y) :
    Y < W := by
  classical
  have hD_card : 1 ≤ (smallDeficientSet B Y q).card := by
    have h2_in : 2 ∈ smallDeficientSet B Y q := by
      unfold smallDeficientSet
      rw [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨by omega, ?_⟩, ?_, ?_⟩
      · have hq_le_Y : q ≤ Y := by
          calc q = q ^ 1 := (pow_one _).symm
            _ ≤ q ^ 20 := Nat.pow_le_pow_right hq_prime.pos (by omega)
            _ ≤ Y := hq_pow20_le_Y
        omega
      · have : 2 % q ≠ 1 := by
          rw [Nat.mod_eq_of_lt (by omega : 2 < q)]
          omega
        exact this
      · unfold zQ
        have hq2 : Nat.Coprime 2 q := by
          have hq_odd : Odd q := hq_prime.odd_of_ne_two (by
            intro h; rw [h] at hq_ge_3; omega)
          exact (Nat.coprime_two_left).mpr hq_odd
        have hv2 : padicValNat q 2 = 0 := by
          apply padicValNat.eq_zero_of_not_dvd
          intro hdvd
          have := Nat.le_of_dvd (by omega : 0 < 2) hdvd
          omega
        rw [hv2, pow_zero, Nat.div_one]
        omega
    exact Finset.card_pos.mpr ⟨2, h2_in⟩
  obtain ⟨d, hd⟩ := Finset.card_pos.mp hD_card
  have hbd_dvd_W : b d ∣ W := hb_dvd_W d hd
  have hbd_gt_YY : Y * Y < b d := (hb_range d hd).1
  have hbd_le_W : b d ≤ W := Nat.le_of_dvd hW_pos hbd_dvd_W
  have hY_le_YY : Y ≤ Y * Y := Nat.le_mul_of_pos_left _ (by omega)
  omega

theorem wcbd_6YY_le_X
    {B X q L Aq E_big : ℕ}
    (hL_pos : 0 < L)
    (hL_ge_2 : 2 ≤ L)
    (hX_ge_LE_loose : L ^ E_big ≤ X)
    (hAq_eq : Aq = 21 * B + 15)
    (hE_big_eq : E_big = 3000 * (B + 1) * (21 * B + 20) + 3000)
    (hq_le_L_pow_Aq1 : q ≤ L ^ (Aq + 1)) :
    6 * q ^ 20 * q ^ 20 ≤ X := by
  have h := wcbd_6YY_le_LE hAq_eq hL_pos hL_ge_2 hq_le_L_pow_Aq1
  rw [← hE_big_eq] at h
  exact h.trans hX_ge_LE_loose

theorem wcbd_4Bp4_le_X
    {B X L E_big : ℕ}
    (hL_pos : 0 < L)
    (hL_ge_2 : 2 ≤ L)
    (hL_ge_7 : 7 ≤ L)
    (hB_le_L4 : B ≤ L ^ 4)
    (hX_ge_LE_loose : L ^ E_big ≤ X)
    (hE_big_ge_5 : 5 ≤ E_big) :
    4 * B + 4 ≤ X := by
  have hB4 : 4 * B + 4 ≤ 4 * L ^ 4 + 4 := by omega
  have hL5 : 4 * L ^ 4 + 4 ≤ L ^ 5 := by
    have h_5L4 : 5 * L ^ 4 ≤ L ^ 5 := by
      have h_L_ge_5 : 5 ≤ L := by omega
      calc 5 * L ^ 4 ≤ L * L ^ 4 := Nat.mul_le_mul_right (L ^ 4) h_L_ge_5
        _ = L ^ 5 := by ring
    have h_4_le_L4 : (4 : ℕ) ≤ L ^ 4 := by
      calc (4 : ℕ) ≤ L := by omega
        _ = L ^ 1 := (pow_one _).symm
        _ ≤ L ^ 4 := Nat.pow_le_pow_right hL_pos (by omega)
    omega
  have hL5_le_LE : L ^ 5 ≤ L ^ E_big :=
    Nat.pow_le_pow_right hL_pos hE_big_ge_5
  exact (hB4.trans hL5).trans (hL5_le_LE.trans hX_ge_LE_loose)

theorem wcbd_2q_le_X
    {B X q L Aq E_big : ℕ}
    (hL_pos : 0 < L)
    (hL_ge_2 : 2 ≤ L)
    (hq_le_2Lpow : q ≤ 2 * L ^ Aq)
    (hAq_eq : Aq = 21 * B + 15)
    (hE_big_eq_main : E_big = 3000 * (B + 1) * (21 * B + 20) + 3000)
    (hX_ge_LE_loose : L ^ E_big ≤ X) :
    2 * q ≤ X := by
  have h1 : 2 * q ≤ 2 * (2 * L ^ Aq) := Nat.mul_le_mul_left 2 hq_le_2Lpow
  have h2 : 2 * (2 * L ^ Aq) = 4 * L ^ Aq := by ring
  have h3 : (4 : ℕ) ≤ L ^ 2 := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ L ^ 2 := Nat.pow_le_pow_left hL_ge_2 _
  have h4 : 4 * L ^ Aq ≤ L ^ (Aq + 2) := by
    calc 4 * L ^ Aq ≤ L ^ 2 * L ^ Aq := Nat.mul_le_mul_right _ h3
      _ = L ^ (Aq + 2) := by rw [← pow_add]; ring_nf
  have hAq2 : Aq + 2 ≤ E_big := by
    rw [hE_big_eq_main, hAq_eq]
    exact wcbd_Aq2_le_E_big B (21 * B + 15) rfl
  have h5 : L ^ (Aq + 2) ≤ L ^ E_big := Nat.pow_le_pow_right hL_pos hAq2
  have hSum : 2 * q ≤ L ^ E_big := by linarith
  exact hSum.trans hX_ge_LE_loose

theorem wcbd_supply_HX_bound
    {B X Y q W L Csw Aq E_big : ℕ}
    (hL_pos : 0 < L)
    (hL_ge_2 : 2 ≤ L)
    (hL_ge_7 : 7 ≤ L)
    (hW_pos : 0 < W)
    (hW_le_X : W ≤ X)
    (hW_poly : W ≤ L ^ Csw)
    (hHX_bound : H_X (M_B B) (2 * X) ≤ 16 * L ^ (21 * B + 9))
    (hX_ge_LE : 1000000 * (B + 1) * L ^ E_big ≤ X)
    (hCsw1_le_E_big : Csw + 1 ≤ E_big)
    (hAq_eq : Aq = 21 * B + 15)
    (hq_ge_Qscale : L ^ Aq ≤ q)
    (hq_le_L_pow_Aq1 : q ≤ L ^ (Aq + 1))
    (hq_pow20_le_Y : q ^ 20 ≤ Y)
    (hShiftSet_lower : Y / (4 * q) ≤ (ShiftSet Y q).card) :
    4 * H_X (M_B B) (2 * X) *
        (((Finset.Icc X (2 * X)).filter (W ∣ ·)).card) ≤
      (ShiftSet Y q).card * (X / (8 * W * L)) := by
  classical
  set Ω := (Finset.Icc X (2 * X)).filter (W ∣ ·) with hΩ_def
  have hΩ_card_le : Ω.card ≤ X / W + 2 := by
    rw [hΩ_def]
    have h := multiples_in_short_interval_card_le_local (W := W) (Y := X) (t := X) hW_pos
    have h_eq : (Finset.Icc X (X + X)).filter (fun k => W ∣ k) =
                (Finset.Icc X (2 * X)).filter (fun k => W ∣ k) := by
      congr 1; congr 1; ring
    rw [h_eq] at h
    exact h
  have hXW_pos : 1 ≤ X / W := (Nat.one_le_div_iff hW_pos).mpr hW_le_X
  have hΩ_card_le' : Ω.card ≤ 3 * (X / W) := by
    have : X / W + 2 ≤ 3 * (X / W) := by omega
    exact hΩ_card_le.trans this
  have hLHS_step :
      4 * H_X (M_B B) (2 * X) * Ω.card ≤ 192 * L ^ (21 * B + 9) * (X / W) := by
    calc 4 * H_X (M_B B) (2 * X) * Ω.card
        ≤ 4 * (16 * L ^ (21 * B + 9)) * (3 * (X / W)) := by
          have h1 := Nat.mul_le_mul_left 4 hHX_bound
          have h2 := Nat.mul_le_mul h1 hΩ_card_le'
          exact h2
      _ = 192 * L ^ (21 * B + 9) * (X / W) := by ring
  have h_WL_le_LCsw1 : 8 * W * L ≤ 8 * L ^ (Csw + 1) := by
    calc 8 * W * L ≤ 8 * L ^ Csw * L :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hW_poly)
      _ = 8 * L ^ (Csw + 1) := by rw [pow_succ]; ring
  have h8WL_pos : 0 < 8 * W * L := by positivity
  have hX_div_8WL_ge :
      (X / W) / (8 * L) ≤ X / (8 * W * L) := by
    have hWL_eq : 8 * W * L = W * (8 * L) := by ring
    rw [hWL_eq, Nat.div_div_eq_div_mul]
  have hXW_ge_8L : 8 * L ≤ X / W := by
    have h_div_mono : X / L ^ Csw ≤ X / W := Nat.div_le_div_left hW_poly hW_pos
    have hX_div_LCsw_ge : 1000000 * (B + 1) * L ^ (E_big - Csw) ≤ X / L ^ Csw := by
      rw [Nat.le_div_iff_mul_le (Nat.pow_pos hL_pos)]
      calc 1000000 * (B + 1) * L ^ (E_big - Csw) * L ^ Csw
          = 1000000 * (B + 1) * (L ^ (E_big - Csw) * L ^ Csw) := by ring
        _ = 1000000 * (B + 1) * L ^ ((E_big - Csw) + Csw) := by rw [← pow_add]
        _ = 1000000 * (B + 1) * L ^ E_big := by
            congr 2; omega
        _ ≤ X := hX_ge_LE
    have h_easy : 8 * L ≤ 1000000 * (B + 1) * L ^ (E_big - Csw) := by
      have h1 : 8 * L ≤ 1000000 * L := by
        have : 8 ≤ 1000000 := by norm_num
        exact Nat.mul_le_mul_right _ this
      have h2 : 1000000 * L ≤ 1000000 * (B + 1) * L := by
        have : 1 ≤ B + 1 := by omega
        nlinarith [Nat.zero_le L, Nat.zero_le B, hL_pos]
      have h3 : L ≤ L ^ (E_big - Csw) := by
        have hE_Csw_ge : 1 ≤ E_big - Csw := by omega
        calc L = L ^ 1 := (pow_one _).symm
          _ ≤ L ^ (E_big - Csw) :=
              Nat.pow_le_pow_right hL_pos hE_Csw_ge
      calc 8 * L ≤ 1000000 * (B + 1) * L := h1.trans h2
        _ ≤ 1000000 * (B + 1) * L ^ (E_big - Csw) :=
            Nat.mul_le_mul_left _ h3
    exact h_easy.trans (hX_div_LCsw_ge.trans h_div_mono)
  have h_XW_le_16L_quot : X / W ≤ 16 * L * ((X / W) / (8 * L)) := by
    have h8L_pos : 0 < 8 * L := by positivity
    have h_mod_lt : (X / W) % (8 * L) < 8 * L := Nat.mod_lt _ h8L_pos
    have h_quot_pos : 1 ≤ (X / W) / (8 * L) :=
      (Nat.one_le_div_iff h8L_pos).mpr hXW_ge_8L
    have hLE_lhs : X / W ≤ 8 * L * ((X / W) / (8 * L)) + 8 * L := by
      have hLt := h_mod_lt
      have h_div_mul : (X / W) = (8 * L) * ((X / W) / (8 * L)) + (X / W) % (8 * L) :=
        (Nat.div_add_mod _ _).symm
      omega
    have h_8L_le : 8 * L ≤ 8 * L * ((X / W) / (8 * L)) := by
      nlinarith [h_quot_pos, h8L_pos]
    calc X / W ≤ 8 * L * ((X / W) / (8 * L)) + 8 * L := hLE_lhs
      _ ≤ 8 * L * ((X / W) / (8 * L)) + 8 * L * ((X / W) / (8 * L)) := by omega
      _ = 16 * L * ((X / W) / (8 * L)) := by ring
  have h_3072_le_ShiftSet :
      3072 * L ^ (21 * B + 10) ≤ (ShiftSet Y q).card := by
    refine hShiftSet_lower.trans' ?_
    have h4q_pos : 0 < 4 * q := by
      have hq_pos : 0 < q := by
        have hLAq_pos : 0 < L ^ Aq := Nat.pow_pos hL_pos
        omega
      positivity
    rw [Nat.le_div_iff_mul_le h4q_pos]
    have h := wcbd_3072_le_q20 hAq_eq hL_pos hL_ge_2 hL_ge_7
      hq_ge_Qscale hq_le_L_pow_Aq1
    exact h.trans hq_pow20_le_Y
  have h1 := hLHS_step
  have h2 := h_XW_le_16L_quot
  have h3 : 192 * L ^ (21 * B + 9) * (X / W) ≤
            3072 * L ^ (21 * B + 10) * ((X / W) / (8 * L)) := by
    have := Nat.mul_le_mul_left (192 * L ^ (21 * B + 9)) h2
    calc 192 * L ^ (21 * B + 9) * (X / W)
        ≤ 192 * L ^ (21 * B + 9) * (16 * L * ((X / W) / (8 * L))) := this
      _ = 3072 * (L ^ (21 * B + 9) * L) * ((X / W) / (8 * L)) := by ring
      _ = 3072 * L ^ (21 * B + 10) * ((X / W) / (8 * L)) := by
          have hpow : L ^ (21 * B + 9) * L = L ^ (21 * B + 10) := by
            have : L ^ (21 * B + 10) = L ^ (21 * B + 9) * L := by
              rw [show (21 * B + 10) = (21 * B + 9) + 1 from by ring]
              exact pow_succ L (21 * B + 9)
            exact this.symm
          rw [hpow]
  have h4 : 3072 * L ^ (21 * B + 10) * ((X / W) / (8 * L)) ≤
            3072 * L ^ (21 * B + 10) * (X / (8 * W * L)) :=
    Nat.mul_le_mul_left _ hX_div_8WL_ge
  have h5 : 3072 * L ^ (21 * B + 10) * (X / (8 * W * L)) ≤
            (ShiftSet Y q).card * (X / (8 * W * L)) :=
    Nat.mul_le_mul_right _ h_3072_le_ShiftSet
  exact h1.trans (h3.trans (h4.trans h5))

theorem wcbd_combinedResidue_zero_lt_B
    {B k Y q : ℕ} (bd : BufferData k Y)
    (smq : ScaffoldMatchingQ k Y q)
    (hq_ge_B : B ≤ q)
    (hB_le_buffer : ∀ d : bd.D, B ≤ bd.buffer d)
    (hB_le_scaffold : ∀ t : smq.T, B ≤ smq.scaffold t) :
    ∀ p, p.Prime → p < B →
      combinedResidue q bd smq.toScaffoldMatching p = 0 := by
  intro p hp hpB
  by_contra hnz
  rcases combinedResidue_support bd smq.toScaffoldMatching hnz with hpq | hb_or_hs
  · subst hpq
    omega
  · rcases hb_or_hs with hbres | hsres
    · unfold BufferData.residue at hbres
      by_cases hEx : ∃ d : bd.D, bd.buffer d = p
      · obtain ⟨d, hd⟩ := hEx
        have hB_buf := hB_le_buffer d
        rw [hd] at hB_buf
        omega
      · rw [dif_neg hEx] at hbres
        exact hbres rfl
    · unfold ScaffoldMatching.residue at hsres
      by_cases hEx : ∃ t : smq.toScaffoldMatching.T,
          smq.toScaffoldMatching.scaffold t = p
      · obtain ⟨t, ht⟩ := hEx
        have hB_scaf := hB_le_scaffold t
        rw [ht] at hB_scaf
        omega
      · rw [dif_neg hEx] at hsres
        exact hsres rfl

theorem wcbd_zSet_aux_for_total {B Y q : ℕ}
    (hq_prime : q.Prime)
    (b : ℕ → ℕ)
    (hb_prime_on : ∀ d ∈ smallDeficientSet B Y q, (b d).Prime)
    (hb_inj_on : Set.InjOn b (smallDeficientSet B Y q))
    (hb_ne_q_on : ∀ d ∈ smallDeficientSet B Y q, b d ≠ q)
    (j : ℕ) (hj_pos : 1 ≤ j) :
    zSet j q ((smallDeficientSet B Y q).image b) ∣ j ∧
    0 < zSet j q ((smallDeficientSet B Y q).image b) ∧
    ∀ p, p.Prime → p ∣ zSet j q ((smallDeficientSet B Y q).image b) →
      p ≠ q ∧ p ∉ (smallDeficientSet B Y q).image b := by
  classical
  have h_zsupp_eq :=
    zSet_mul_support_eq (B := B) (Y := Y) (q := q) (t := j) (b := b)
      hq_prime hb_prime_on hb_inj_on hb_ne_q_on
  set Z := zSet j q ((smallDeficientSet B Y q).image b) with hZ_def
  set Mdenom :=
    q ^ padicValNat q j *
      ∏ d ∈ smallDeficientSet B Y q, b d ^ padicValNat (b d) j
      with hMdenom_def
  have hZM : Z * Mdenom = j := h_zsupp_eq
  have hj_ne : j ≠ 0 := by omega
  have hZ_ne : Z ≠ 0 := by
    intro h; rw [h, Nat.zero_mul] at hZM; exact hj_ne hZM.symm
  have hM_ne : Mdenom ≠ 0 := by
    intro h; rw [h, Nat.mul_zero] at hZM; exact hj_ne hZM.symm
  have hZ_dvd_j : Z ∣ j := ⟨Mdenom, hZM.symm⟩
  have hZ_pos : 0 < Z := Nat.pos_of_ne_zero hZ_ne
  refine ⟨hZ_dvd_j, hZ_pos, ?_⟩
  intro p hp hp_dvd
  refine ⟨?_, ?_⟩
  · intro hpq
    subst hpq
    have : Fact (Nat.Prime p) := ⟨hp⟩
    have h_q_pow_dvd_M : p ^ padicValNat p j ∣ Mdenom := by
      rw [hMdenom_def]
      exact dvd_mul_right _ _
    have h_mul_dvd : p * p ^ padicValNat p j ∣ Z * Mdenom :=
      Nat.mul_dvd_mul hp_dvd h_q_pow_dvd_M
    rw [hZM] at h_mul_dvd
    have h_eq : p * p ^ padicValNat p j = p ^ (padicValNat p j + 1) := by ring
    rw [h_eq] at h_mul_dvd
    exact pow_succ_padicValNat_not_dvd hj_ne h_mul_dvd

  · intro hp_in
    obtain ⟨d, hd, hd_eq⟩ := Finset.mem_image.mp hp_in
    have hp_eq : b d = p := hd_eq
    have : Fact (Nat.Prime p) := ⟨hp⟩
    have h_p_pow_dvd_M : p ^ padicValNat p j ∣ Mdenom := by
      rw [hMdenom_def]
      have h_factor_in_prod :
          b d ^ padicValNat (b d) j ∣
            ∏ d' ∈ smallDeficientSet B Y q, b d' ^ padicValNat (b d') j :=
        Finset.dvd_prod_of_mem _ hd
      rw [hp_eq] at h_factor_in_prod
      exact Dvd.dvd.mul_left h_factor_in_prod _
    have h_mul_dvd : p * p ^ padicValNat p j ∣ Z * Mdenom :=
      Nat.mul_dvd_mul hp_dvd h_p_pow_dvd_M
    rw [hZM] at h_mul_dvd
    have h_eq : p * p ^ padicValNat p j = p ^ (padicValNat p j + 1) := by ring
    rw [h_eq] at h_mul_dvd
    exact pow_succ_padicValNat_not_dvd hj_ne h_mul_dvd

end Erdos387.CoverBPZ
