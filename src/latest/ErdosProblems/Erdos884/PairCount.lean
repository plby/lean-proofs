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
import ErdosProblems.Erdos884.Bridge

set_option linter.mathlibStandardSet false

/-!
# Erdős 884 — Lemma B: counting prime pairs with small gap

Exports `Erdos884.prime_pairs_bound`: the number of prime pairs `(p, q)` with
`p < q ≤ 9t` and `q - p ≤ N ≤ (log t)²` is at most `C_B · N · t / (log t)²`.

Route: fiber the pairs over the gap `h = q - p`.  Odd gaps contribute at most `1`
each (`p = 2` forced).  Even gaps are handled by the Selberg pair sieve
(`pairSieve_pairs_le`), whose bounding sum is bounded below via
`pairSieve_boundingSum_ge` + `coprime_squarefree_sum_lower`; the sum of the
resulting `(2h/φ(2h))²` weights is controlled by `sum_totient_ratio_sq_le`.
-/

namespace Erdos884

/-! ## Fibering the pair count over the gap `h` -/

lemma pc_pair_fiber (M N : ℕ) :
    ((Finset.Icc 1 M ×ˢ Finset.Icc 1 M).filter
        (fun pq => Nat.Prime pq.1 ∧ Nat.Prime pq.2 ∧ pq.1 < pq.2 ∧ pq.2 - pq.1 ≤ N)).card
      ≤ ∑ h ∈ Finset.Icc 1 N,
          ((Finset.Icc 1 M).filter (fun n => Nat.Prime n ∧ Nat.Prime (n + h))).card := by
  have hsub : (Finset.Icc 1 M ×ˢ Finset.Icc 1 M).filter
        (fun pq => Nat.Prime pq.1 ∧ Nat.Prime pq.2 ∧ pq.1 < pq.2 ∧ pq.2 - pq.1 ≤ N)
      ⊆ (Finset.Icc 1 N).biUnion (fun h =>
          ((Finset.Icc 1 M).filter (fun n => Nat.Prime n ∧ Nat.Prime (n + h))).image
            (fun p => (p, p + h))) := by
    intro pq hpq
    obtain ⟨a, b⟩ := pq
    rw [Finset.mem_filter, Finset.mem_product] at hpq
    obtain ⟨⟨h1, h2⟩, hp, hq, hlt, hle⟩ := hpq
    rw [Finset.mem_Icc] at h1 h2
    rw [Finset.mem_biUnion]
    refine ⟨b - a, Finset.mem_Icc.mpr ⟨by omega, hle⟩, ?_⟩
    rw [Finset.mem_image]
    have he : a + (b - a) = b := by omega
    refine ⟨a, ?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨h1.1, h1.2⟩, hp, by rw [he]; exact hq⟩
    · rw [he]
  calc ((Finset.Icc 1 M ×ˢ Finset.Icc 1 M).filter
        (fun pq => Nat.Prime pq.1 ∧ Nat.Prime pq.2 ∧ pq.1 < pq.2 ∧ pq.2 - pq.1 ≤ N)).card
      ≤ ((Finset.Icc 1 N).biUnion (fun h =>
          ((Finset.Icc 1 M).filter (fun n => Nat.Prime n ∧ Nat.Prime (n + h))).image
            (fun p => (p, p + h)))).card := Finset.card_le_card hsub
    _ ≤ ∑ h ∈ Finset.Icc 1 N, (((Finset.Icc 1 M).filter
          (fun n => Nat.Prime n ∧ Nat.Prime (n + h))).image (fun p => (p, p + h))).card :=
        Finset.card_biUnion_le
    _ ≤ _ := Finset.sum_le_sum (fun h _ => Finset.card_image_le)

/-! ## Odd gaps: at most one pair -/

lemma pc_odd_card (M h : ℕ) (hodd : ¬ 2 ∣ h) :
    ((Finset.Icc 1 M).filter (fun n => Nat.Prime n ∧ Nat.Prime (n + h))).card ≤ 1 := by
  have hmem : ∀ n ∈ (Finset.Icc 1 M).filter (fun n => Nat.Prime n ∧ Nat.Prime (n + h)),
      n = 2 := by
    intro n hn
    rw [Finset.mem_filter] at hn
    obtain ⟨-, hp, hq⟩ := hn
    by_contra hne
    have hn3 : 3 ≤ n := by have := hp.two_le; omega
    have hnodd : n % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hne)
    have hdvd : 2 ∣ n + h := by omega
    rcases hq.eq_one_or_self_of_dvd 2 hdvd with h1 | h1 <;> omega
  rw [Finset.card_le_one]
  intro a ha b hb
  rw [hmem a ha, hmem b hb]

/-! ## The error-sum bound -/

lemma pc_err_sum (z : ℝ) (hz : 1 ≤ z) :
    ∑ d ∈ Finset.Icc 1 ⌊z⌋₊, (6:ℝ)^(d.primeFactors.card) ≤ z * (1 + Real.log z)^5 := by
  have h0 := sum_pow_primeFactors_le 6 ⌊z⌋₊ (by norm_num)
  norm_num at h0
  have h1 : (1:ℝ) ≤ ((⌊z⌋₊ : ℕ) : ℝ) := by
    have : (1:ℕ) ≤ ⌊z⌋₊ := Nat.le_floor (by exact_mod_cast hz)
    exact_mod_cast this
  have h2 : ((⌊z⌋₊ : ℕ) : ℝ) ≤ z := Nat.floor_le (by linarith)
  have h3 : Real.log ((⌊z⌋₊ : ℕ) : ℝ) ≤ Real.log z := Real.log_le_log (by linarith) h2
  have h4 : (0:ℝ) ≤ 1 + Real.log ((⌊z⌋₊ : ℕ) : ℝ) := by
    have := Real.log_nonneg h1
    linarith
  refine h0.trans ?_
  exact mul_le_mul h2 (pow_le_pow_left₀ h4 (by linarith) 5) (pow_nonneg h4 5) (by linarith)

/-! ## The totient-ratio sum over even gaps -/

lemma pc_totient_sum (N : ℕ) :
    ∑ h ∈ (Finset.Icc 1 N).filter (fun h => 2 ∣ h),
        (((2*h : ℕ) : ℝ) / (Nat.totient (2*h) : ℝ))^2 ≤ 400 * N := by
  have h1 : ∑ h ∈ (Finset.Icc 1 N).filter (fun h => 2 ∣ h),
        (((2*h : ℕ) : ℝ) / (Nat.totient (2*h) : ℝ))^2
      ≤ ∑ h' ∈ Finset.Icc 1 (2*N), ((h' : ℝ) / (Nat.totient h' : ℝ))^2 := by
    apply cs_sum_le_sum_inj (fun h => 2*h)
    · intro a ha
      rw [Finset.mem_filter, Finset.mem_Icc] at ha
      rw [Finset.mem_Icc]
      omega
    · intro a _ b _ hab
      simp only at hab
      omega
    · intro a _
      exact le_rfl
    · intro b _
      positivity
  have h2 := sum_totient_ratio_sq_le (2*N)
  have h3 : (200:ℝ) * ((2*N : ℕ) : ℝ) = 400 * N := by push_cast; ring
  linarith

/-! ## Junk-term absorption: `4√t(1+log t)⁵ ≤ t/(log t)²` for large `t` -/

lemma pc_sqrt_lower (t : ℝ) (ht : 1 ≤ t) (hL : (2:ℝ)^40 ≤ Real.log t) :
    4 * (1 + Real.log t)^5 * (Real.log t)^2 ≤ Real.sqrt t := by
  set L := Real.log t with hLdef
  have hL1 : (1:ℝ) ≤ L := le_trans (by norm_num) hL
  have hL0 : (0:ℝ) < L := by linarith
  have ht0 : (0:ℝ) < t := by linarith
  have hspos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
  -- `√t = exp (L/2) ≥ (L/16)⁸`
  have hlogs : Real.log (Real.sqrt t) = L / 2 := by
    rw [Real.log_sqrt ht0.le]
  have hs_eq : Real.sqrt t = Real.exp (L / 2) := by
    rw [← hlogs, Real.exp_log hspos]
  have hexp8 : Real.exp (L/16) ^ 8 = Real.exp (L / 2) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have he3 : L/16 ≤ Real.exp (L/16) := by
    linarith [Real.add_one_le_exp (L/16)]
  have hexp_low : (L/16)^8 ≤ Real.exp (L / 2) := by
    calc (L/16)^8 ≤ Real.exp (L/16) ^ 8 := pow_le_pow_left₀ (by positivity) he3 8
      _ = Real.exp (L / 2) := hexp8
  have hmid : 128 * L^7 ≤ (L/16)^8 := by
    have hpow : (L/16)^8 = L^8 / 16^8 := by
      rw [div_pow]
    rw [hpow, le_div_iff₀ (by positivity : (0:ℝ) < 16^8)]
    have hLbig : (128:ℝ) * 16^8 ≤ L := by
      norm_num at hL ⊢
      linarith
    calc 128 * L^7 * 16^8 = (128 * 16^8) * L^7 := by ring
      _ ≤ L * L^7 := mul_le_mul_of_nonneg_right hLbig (by positivity)
      _ = L^8 := by ring
  calc 4 * (1 + L)^5 * L^2
      ≤ 4 * (2*L)^5 * L^2 := by
        have h5 : (1 + L)^5 ≤ (2*L)^5 := pow_le_pow_left₀ (by linarith) (by linarith) 5
        have := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left h5 (by norm_num : (0:ℝ) ≤ 4))
          (by positivity : (0:ℝ) ≤ L^2)
        linarith
    _ = 128 * L^7 := by ring
    _ ≤ (L/16)^8 := hmid
    _ ≤ Real.exp (L / 2) := hexp_low
    _ = Real.sqrt t := hs_eq.symm

lemma pc_junk_le (t : ℝ) (ht : 1 ≤ t) (hL : (2:ℝ)^40 ≤ Real.log t) :
    4 * Real.sqrt t * (1 + Real.log t)^5 ≤ t / (Real.log t)^2 := by
  set L := Real.log t with hLdef
  have hL0 : (0:ℝ) < L := lt_of_lt_of_le (by norm_num) hL
  have key := pc_sqrt_lower t ht hL
  have hs : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt (by linarith)
  rw [le_div_iff₀ (by positivity : (0:ℝ) < L^2)]
  calc 4 * Real.sqrt t * (1 + L)^5 * L^2
      = Real.sqrt t * (4 * (1 + L)^5 * L^2) := by ring
    _ ≤ Real.sqrt t * Real.sqrt t :=
        mul_le_mul_of_nonneg_left key (Real.sqrt_nonneg t)
    _ = t := hs

/-! ## The main theorem -/

theorem prime_pairs_bound :
    ∃ C_B : ℝ, 1 ≤ C_B ∧ ∃ T_B : ℝ, 3 ≤ T_B ∧ ∀ t : ℝ, T_B ≤ t → ∀ N : ℕ, 2 ≤ N →
      (N:ℝ) ≤ (Real.log t)^2 →
      (((Finset.Icc 1 ⌊9*t⌋₊ ×ˢ Finset.Icc 1 ⌊9*t⌋₊).filter
          (fun pq => Nat.Prime pq.1 ∧ Nat.Prime pq.2 ∧ pq.1 < pq.2 ∧ pq.2 - pq.1 ≤ N)).card : ℝ)
        ≤ C_B * N * t / (Real.log t)^2 := by
  obtain ⟨c₀, hc₀, w₀, hlower⟩ := coprime_squarefree_sum_lower
  have hCB1 : (1:ℝ) ≤ 90000 / c₀ + 1 := by
    have : (0:ℝ) ≤ 90000 / c₀ := by positivity
    linarith
  have hTB3 : (3:ℝ) ≤ max (Real.exp ((2:ℝ)^40)) (((w₀:ℝ)+1)^4) := by
    have h1 : (3:ℝ) ≤ Real.exp ((2:ℝ)^40) := by
      have h2 := Real.add_one_le_exp ((2:ℝ)^40)
      have h3 : (3:ℝ) ≤ (2:ℝ)^40 + 1 := by norm_num
      linarith
    exact le_trans h1 (le_max_left _ _)
  refine ⟨90000 / c₀ + 1, hCB1, max (Real.exp ((2:ℝ)^40)) (((w₀:ℝ)+1)^4), hTB3, ?_⟩
  intro t ht N hN2 hNlog
  -- basic facts about `t`
  have htexp : Real.exp ((2:ℝ)^40) ≤ t := le_trans (le_max_left _ _) ht
  have htw : ((w₀:ℝ)+1)^4 ≤ t := le_trans (le_max_right _ _) ht
  have hL : (2:ℝ)^40 ≤ Real.log t := by
    have h1 := Real.log_le_log (Real.exp_pos _) htexp
    rwa [Real.log_exp] at h1
  set L := Real.log t with hLdef
  have hL0 : (0:ℝ) < L := lt_of_lt_of_le (by norm_num) hL
  have hL250 : (250:ℝ) ≤ L := le_trans (by norm_num) hL
  have ht16 : (16:ℝ) ≤ t := by
    have h1 := Real.add_one_le_exp ((2:ℝ)^40)
    have h2 : (16:ℝ) ≤ (2:ℝ)^40 + 1 := by norm_num
    linarith
  have ht1 : (1:ℝ) ≤ t := by linarith
  have ht0 : (0:ℝ) < t := by linarith
  -- the sieve level `z = √t`
  set z := Real.sqrt t with hzdef
  have hz : (1:ℝ) ≤ z := by
    rw [hzdef]
    refine (Real.le_sqrt (by norm_num) (by linarith)).mpr ?_
    norm_num
    linarith
  have hz4 : (4:ℝ) ≤ z := by
    rw [hzdef]
    refine (Real.le_sqrt (by norm_num) (by linarith)).mpr ?_
    norm_num
    linarith
  have hlogz : Real.log z = L / 2 := by
    rw [hzdef, Real.log_sqrt ht0.le]
  -- the total mass `M = ⌊9t⌋₊`
  set M := ⌊9*t⌋₊ with hMdef
  have hM9t : (M:ℝ) ≤ 9*t := Nat.floor_le (by linarith)
  -- the fourth-root scale `w = ⌊√z⌋₊`
  have hu2 : (2:ℝ) ≤ Real.sqrt z := by
    refine (Real.le_sqrt (by norm_num) (by linarith)).mpr ?_
    norm_num
    linarith
  have hfloorw : Real.sqrt z / 2 ≤ ((⌊Real.sqrt z⌋₊ : ℕ) : ℝ) := by
    have h1 := Nat.lt_floor_add_one (Real.sqrt z)
    linarith
  have hw₀w : w₀ ≤ ⌊Real.sqrt z⌋₊ := by
    apply Nat.le_floor
    have hx4 : (((w₀:ℝ)+1)^2)^2 ≤ t := by
      calc (((w₀:ℝ)+1)^2)^2 = ((w₀:ℝ)+1)^4 := by ring
        _ ≤ t := htw
    have hx2 : ((w₀:ℝ)+1)^2 ≤ z := by
      rw [hzdef]
      exact (Real.le_sqrt (by positivity) (by linarith)).mpr hx4
    have hx1 : (w₀:ℝ)+1 ≤ Real.sqrt z :=
      (Real.le_sqrt (by positivity) (by linarith)).mpr hx2
    linarith
  have hw1R : (1:ℝ) ≤ ((⌊Real.sqrt z⌋₊ : ℕ) : ℝ) := by linarith
  have hlogw : L/5 ≤ Real.log ((⌊Real.sqrt z⌋₊ : ℕ) : ℝ) := by
    have hlogu : Real.log (Real.sqrt z) = L/4 := by
      rw [Real.log_sqrt (by linarith : (0:ℝ) ≤ z), hlogz]
      ring
    have h1 : Real.log (Real.sqrt z / 2) ≤ Real.log ((⌊Real.sqrt z⌋₊ : ℕ) : ℝ) :=
      Real.log_le_log (by linarith) hfloorw
    have h2 : Real.log (Real.sqrt z / 2) = L/4 - Real.log 2 := by
      rw [Real.log_div (ne_of_gt (by linarith : (0:ℝ) < Real.sqrt z)) (by norm_num), hlogu]
    have h3 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
    linarith
  -- the per-`h` bound for even gaps
  have hkey : ∀ h ∈ (Finset.Icc 1 N).filter (fun h => 2 ∣ h),
      (((Finset.Icc 1 M).filter (fun n => Nat.Prime n ∧ Nat.Prime (n + h))).card : ℝ)
        ≤ 225 * t / (c₀ * L^2) * (((2*h : ℕ) : ℝ) / (Nat.totient (2*h) : ℝ))^2
          + (z * (1 + L)^5 + (z + 1)) := by
    intro h hh
    rw [Finset.mem_filter, Finset.mem_Icc] at hh
    obtain ⟨⟨hh1, hhN⟩, heven⟩ := hh
    have hh0 : 0 < h := hh1
    have hbound := pairSieve_pairs_le M h z hz heven hh0
    have hSpos := pairSieve_boundingSum_pos M h z hz
    have hge := pairSieve_boundingSum_ge M h z hz
    -- lower bound on the Selberg bounding sum
    have hm1 : 1 ≤ 2*h := by omega
    have hmw : ((2*h : ℕ) : ℝ) ≤ (Real.log ((⌊Real.sqrt z⌋₊ : ℕ) : ℝ))^3 := by
      have h1 : ((2*h : ℕ) : ℝ) ≤ 2*(N:ℝ) := by
        push_cast
        have : (h:ℝ) ≤ (N:ℝ) := by exact_mod_cast hhN
        linarith
      have h2 : 2*(N:ℝ) ≤ 2*L^2 := by linarith
      have h3 : 2*L^2 ≤ (L/5)^3 := by
        have h4 := mul_le_mul_of_nonneg_right hL250 (sq_nonneg L)
        nlinarith [h4]
      have h5 : (L/5)^3 ≤ (Real.log ((⌊Real.sqrt z⌋₊ : ℕ) : ℝ))^3 :=
        pow_le_pow_left₀ (by linarith) hlogw 3
      linarith
    have hlow := hlower ⌊Real.sqrt z⌋₊ hw₀w (2*h) hm1 hmw
    have hφpos : (0:ℝ) < (Nat.totient (2*h) : ℝ) := by
      exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < 2*h)
    have hmpos : (0:ℝ) < ((2*h : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 0 < 2*h)
    have hlow2 : c₀ * ((Nat.totient (2*h) : ℝ) / ((2*h : ℕ) : ℝ))^2 * (L/5)^2
        ≤ (pairSieve M h z hz).selbergBoundingSum := by
      have hsq : (L/5)^2 ≤ (Real.log ((⌊Real.sqrt z⌋₊ : ℕ) : ℝ))^2 :=
        pow_le_pow_left₀ (by linarith) hlogw 2
      calc c₀ * ((Nat.totient (2*h) : ℝ) / ((2*h : ℕ) : ℝ))^2 * (L/5)^2
          ≤ c₀ * ((Nat.totient (2*h) : ℝ) / ((2*h : ℕ) : ℝ))^2
              * (Real.log ((⌊Real.sqrt z⌋₊ : ℕ) : ℝ))^2 :=
            mul_le_mul_of_nonneg_left hsq (by positivity)
        _ ≤ ∑ ℓ ∈ (Finset.Icc 1 ⌊Real.sqrt z⌋₊).filter
              (fun ℓ => Squarefree ℓ ∧ ℓ.Coprime (2*h)),
              (2:ℝ)^(ℓ.primeFactors.card) / ℓ := hlow
        _ ≤ _ := hge
    -- `M / S ≤ 225·t·(2h/φ(2h))²/(c₀ L²)`
    have hX0 : (0:ℝ) ≤ 225 * t / (c₀ * L^2)
        * (((2*h : ℕ) : ℝ) / (Nat.totient (2*h) : ℝ))^2 := by positivity
    have hXlow : (225 * t / (c₀ * L^2) * (((2*h : ℕ) : ℝ) / (Nat.totient (2*h) : ℝ))^2)
          * (c₀ * ((Nat.totient (2*h) : ℝ) / ((2*h : ℕ) : ℝ))^2 * (L/5)^2) = 9 * t := by
      field_simp
      ring
    have hMX : (M:ℝ) / (pairSieve M h z hz).selbergBoundingSum
        ≤ 225 * t / (c₀ * L^2) * (((2*h : ℕ) : ℝ) / (Nat.totient (2*h) : ℝ))^2 := by
      rw [div_le_iff₀ hSpos]
      calc (M:ℝ) ≤ 9 * t := hM9t
        _ = _ := hXlow.symm
        _ ≤ _ := mul_le_mul_of_nonneg_left hlow2 hX0
    -- the error term
    have herr : ∑ d ∈ Finset.Icc 1 ⌊z⌋₊, (6:ℝ)^(d.primeFactors.card) ≤ z * (1 + L)^5 := by
      have h1 := pc_err_sum z hz
      have h2 : (0:ℝ) ≤ 1 + Real.log z := by
        have := Real.log_nonneg hz
        linarith
      calc ∑ d ∈ Finset.Icc 1 ⌊z⌋₊, (6:ℝ)^(d.primeFactors.card)
          ≤ z * (1 + Real.log z)^5 := h1
        _ ≤ z * (1 + L)^5 := by
            have h3 : (1 + Real.log z)^5 ≤ (1 + L)^5 :=
              pow_le_pow_left₀ h2 (by rw [hlogz]; linarith) 5
            exact mul_le_mul_of_nonneg_left h3 (by linarith)
    calc (((Finset.Icc 1 M).filter (fun n => Nat.Prime n ∧ Nat.Prime (n + h))).card : ℝ)
        ≤ (M:ℝ) / (pairSieve M h z hz).selbergBoundingSum
          + ∑ d ∈ Finset.Icc 1 ⌊z⌋₊, (6:ℝ)^(d.primeFactors.card) + (z + 1) := hbound
      _ ≤ 225 * t / (c₀ * L^2) * (((2*h : ℕ) : ℝ) / (Nat.totient (2*h) : ℝ))^2
          + (z * (1 + L)^5 + (z + 1)) := by linarith
  -- assemble: fiber the pair count over the gap
  have hfiberR : (((Finset.Icc 1 M ×ˢ Finset.Icc 1 M).filter
        (fun pq => Nat.Prime pq.1 ∧ Nat.Prime pq.2 ∧ pq.1 < pq.2 ∧ pq.2 - pq.1 ≤ N)).card : ℝ)
      ≤ ∑ h ∈ Finset.Icc 1 N, (((Finset.Icc 1 M).filter
          (fun n => Nat.Prime n ∧ Nat.Prime (n + h))).card : ℝ) := by
    exact_mod_cast pc_pair_fiber M N
  have hsplit : ∑ h ∈ Finset.Icc 1 N, (((Finset.Icc 1 M).filter
        (fun n => Nat.Prime n ∧ Nat.Prime (n + h))).card : ℝ)
      = ∑ h ∈ (Finset.Icc 1 N).filter (fun h => 2 ∣ h), (((Finset.Icc 1 M).filter
          (fun n => Nat.Prime n ∧ Nat.Prime (n + h))).card : ℝ)
        + ∑ h ∈ (Finset.Icc 1 N).filter (fun h => ¬ 2 ∣ h), (((Finset.Icc 1 M).filter
          (fun n => Nat.Prime n ∧ Nat.Prime (n + h))).card : ℝ) :=
    (Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 N) (fun h => 2 ∣ h) _).symm
  -- even gaps
  have hJ0 : (0:ℝ) ≤ z * (1 + L)^5 + (z + 1) := by
    have := mul_nonneg (show (0:ℝ) ≤ z by linarith)
      (pow_nonneg (show (0:ℝ) ≤ 1 + L by linarith) 5)
    linarith
  have heven_sum : ∑ h ∈ (Finset.Icc 1 N).filter (fun h => 2 ∣ h),
        (((Finset.Icc 1 M).filter (fun n => Nat.Prime n ∧ Nat.Prime (n + h))).card : ℝ)
      ≤ 225 * t / (c₀ * L^2) * (400 * N) + (N:ℝ) * (z * (1 + L)^5 + (z + 1)) := by
    calc ∑ h ∈ (Finset.Icc 1 N).filter (fun h => 2 ∣ h),
          (((Finset.Icc 1 M).filter (fun n => Nat.Prime n ∧ Nat.Prime (n + h))).card : ℝ)
        ≤ ∑ h ∈ (Finset.Icc 1 N).filter (fun h => 2 ∣ h),
            (225 * t / (c₀ * L^2) * (((2*h : ℕ) : ℝ) / (Nat.totient (2*h) : ℝ))^2
              + (z * (1 + L)^5 + (z + 1))) := Finset.sum_le_sum hkey
      _ = 225 * t / (c₀ * L^2) * (∑ h ∈ (Finset.Icc 1 N).filter (fun h => 2 ∣ h),
            (((2*h : ℕ) : ℝ) / (Nat.totient (2*h) : ℝ))^2)
          + (((Finset.Icc 1 N).filter (fun h => 2 ∣ h)).card : ℝ)
            * (z * (1 + L)^5 + (z + 1)) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
      _ ≤ 225 * t / (c₀ * L^2) * (400 * N) + (N:ℝ) * (z * (1 + L)^5 + (z + 1)) := by
          have hE400 := pc_totient_sum N
          have hEcard : ((Finset.Icc 1 N).filter (fun h => 2 ∣ h)).card ≤ N := by
            calc ((Finset.Icc 1 N).filter (fun h => 2 ∣ h)).card
                ≤ (Finset.Icc 1 N).card := Finset.card_filter_le _ _
              _ = N := by rw [Nat.card_Icc]; omega
          have hEcardR : (((Finset.Icc 1 N).filter (fun h => 2 ∣ h)).card : ℝ) ≤ (N:ℝ) := by
            exact_mod_cast hEcard
          have t1 := mul_le_mul_of_nonneg_left hE400
            (show (0:ℝ) ≤ 225 * t / (c₀ * L^2) by positivity)
          have t2 := mul_le_mul_of_nonneg_right hEcardR hJ0
          linarith
  -- odd gaps
  have hodd_sum : ∑ h ∈ (Finset.Icc 1 N).filter (fun h => ¬ 2 ∣ h),
        (((Finset.Icc 1 M).filter (fun n => Nat.Prime n ∧ Nat.Prime (n + h))).card : ℝ)
      ≤ (N:ℝ) := by
    calc ∑ h ∈ (Finset.Icc 1 N).filter (fun h => ¬ 2 ∣ h),
          (((Finset.Icc 1 M).filter (fun n => Nat.Prime n ∧ Nat.Prime (n + h))).card : ℝ)
        ≤ ∑ _h ∈ (Finset.Icc 1 N).filter (fun h => ¬ 2 ∣ h), (1:ℝ) := by
          apply Finset.sum_le_sum
          intro h hh
          rw [Finset.mem_filter] at hh
          exact_mod_cast pc_odd_card M h hh.2
      _ = (((Finset.Icc 1 N).filter (fun h => ¬ 2 ∣ h)).card : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ ≤ (N:ℝ) := by
          have h1 : ((Finset.Icc 1 N).filter (fun h => ¬ 2 ∣ h)).card ≤ N := by
            calc ((Finset.Icc 1 N).filter (fun h => ¬ 2 ∣ h)).card
                ≤ (Finset.Icc 1 N).card := Finset.card_filter_le _ _
              _ = N := by rw [Nat.card_Icc]; omega
          exact_mod_cast h1
  -- absorb the junk terms
  have hjunk := pc_junk_le t ht1 hL
  rw [← hzdef] at hjunk
  have hp1 : (1:ℝ) ≤ (1 + L)^5 := by
    have := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) (by linarith : (1:ℝ) ≤ 1 + L) 5
    simpa using this
  have h1z : (1:ℝ) ≤ z * (1 + L)^5 := by
    have := mul_le_mul hz hp1 (by norm_num) (by linarith)
    linarith
  have hzz : z ≤ z * (1 + L)^5 :=
    le_mul_of_one_le_right (by linarith) hp1
  have hjunk2 : (N:ℝ) * (z * (1 + L)^5 + (z + 1)) + (N:ℝ) ≤ (N:ℝ) * (t / L^2) := by
    have hN0 : (0:ℝ) ≤ (N:ℝ) := Nat.cast_nonneg N
    have hchain : z * (1 + L)^5 + (z + 1) + 1 ≤ 4 * (z * (1 + L)^5) := by linarith
    calc (N:ℝ) * (z * (1 + L)^5 + (z + 1)) + (N:ℝ)
        = (N:ℝ) * (z * (1 + L)^5 + (z + 1) + 1) := by ring
      _ ≤ (N:ℝ) * (4 * (z * (1 + L)^5)) := mul_le_mul_of_nonneg_left hchain hN0
      _ ≤ (N:ℝ) * (t / L^2) := by
          apply mul_le_mul_of_nonneg_left _ hN0
          linarith [hjunk]
  -- conclusion
  have hmain : 225 * t / (c₀ * L^2) * (400 * (N:ℝ)) = 90000/c₀ * ((N:ℝ) * (t / L^2)) := by
    field_simp
    ring
  have hfinal : 90000/c₀ * ((N:ℝ) * (t / L^2)) + (N:ℝ) * (t / L^2)
      = (90000 / c₀ + 1) * (N:ℝ) * t / L^2 := by
    ring
  calc (((Finset.Icc 1 M ×ˢ Finset.Icc 1 M).filter
        (fun pq => Nat.Prime pq.1 ∧ Nat.Prime pq.2 ∧ pq.1 < pq.2 ∧ pq.2 - pq.1 ≤ N)).card : ℝ)
      ≤ ∑ h ∈ Finset.Icc 1 N, (((Finset.Icc 1 M).filter
          (fun n => Nat.Prime n ∧ Nat.Prime (n + h))).card : ℝ) := hfiberR
    _ ≤ 225 * t / (c₀ * L^2) * (400 * N) + (N:ℝ) * (z * (1 + L)^5 + (z + 1)) + (N:ℝ) := by
        rw [hsplit]
        linarith
    _ ≤ 90000/c₀ * ((N:ℝ) * (t / L^2)) + (N:ℝ) * (t / L^2) := by
        rw [← hmain]
        linarith
    _ = (90000 / c₀ + 1) * (N:ℝ) * t / L^2 := hfinal

end Erdos884
