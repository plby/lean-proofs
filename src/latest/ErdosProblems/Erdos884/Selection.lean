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
import ErdosProblems.Erdos884.OneScale

set_option linter.mathlibStandardSet false

/-!
# Erdős 884 — Lemma C: selection of well-separated primes in a short window

Exports `Erdos884.separated_primes_selection`: for suitable `ε` and all large `t`, and any
`2 ≤ K ≤ log t / log log t`, there are `K` primes in a window `(x₀, x₀ + H]` with
`t ≤ x₀ ≤ 8t`, `H ≤ 7K log t`, pairwise gaps exceeding `N ≍ ε log t`.

Route: Chebyshev (`primesBetween_lower` at `t+1`) provides `≳ (3/2) t / log t` primes in
`(⌊t+1⌋₊, ⌊8t⌋₊]`; the pair-sieve bound (`prime_pairs_bound`) shows at most `t/(8 log t)`
of them are within `N` of a smaller one (greedy filtering, no recursion); pigeonholing the
survivors over windows of length `H` produces a window containing `K` of them.
-/

namespace Erdos884

/-! ## Numeric helper: `100 (log t)² ≤ t` for `t ≥ 2 560 000` -/

lemma sel_log_sq_le {t : ℝ} (ht : 2560000 ≤ t) : 100 * (Real.log t)^2 ≤ t := by
  have ht1 : (1:ℝ) ≤ t := by linarith
  have ht0 : (0:ℝ) < t := by linarith
  have hs0 : (0:ℝ) ≤ Real.sqrt t := Real.sqrt_nonneg t
  have hs_pos : (0:ℝ) < Real.sqrt t := Real.sqrt_pos.mpr ht0
  have hu_pos : (0:ℝ) < Real.sqrt (Real.sqrt t) := Real.sqrt_pos.mpr hs_pos
  have h1 : Real.log t = 4 * Real.log (Real.sqrt (Real.sqrt t)) := by
    rw [Real.log_sqrt hs0, Real.log_sqrt ht0.le]; ring
  have h2 : Real.log (Real.sqrt (Real.sqrt t)) ≤ Real.sqrt (Real.sqrt t) :=
    (Real.log_le_sub_one_of_pos hu_pos).trans (by linarith)
  have h3 : Real.log t ≤ 4 * Real.sqrt (Real.sqrt t) := by rw [h1]; linarith
  have hlog0 : 0 ≤ Real.log t := Real.log_nonneg ht1
  have h4 : (Real.log t)^2 ≤ 16 * Real.sqrt t := by
    calc (Real.log t)^2 ≤ (4 * Real.sqrt (Real.sqrt t))^2 := pow_le_pow_left₀ hlog0 h3 2
      _ = 16 * (Real.sqrt (Real.sqrt t))^2 := by ring
      _ = 16 * Real.sqrt t := by rw [Real.sq_sqrt hs0]
  have h5 : (1600:ℝ) ≤ Real.sqrt t := by
    rw [show (1600:ℝ) = Real.sqrt (1600^2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num; linarith)
  calc 100 * (Real.log t)^2 ≤ 100 * (16 * Real.sqrt t) := by linarith
    _ = 1600 * Real.sqrt t := by ring
    _ ≤ Real.sqrt t * Real.sqrt t := mul_le_mul_of_nonneg_right h5 hs0
    _ = t := Real.mul_self_sqrt ht0.le

/-! ## Window arithmetic -/

lemma sel_window {b H p w : ℕ} (hH : 0 < H) (hbp : b < p)
    (hw : (p - b - 1) / H = w) : b + w * H < p ∧ p ≤ b + w * H + H := by
  have h1 : H * ((p - b - 1) / H) + (p - b - 1) % H = p - b - 1 := Nat.div_add_mod _ _
  have h2 : (p - b - 1) % H < H := Nat.mod_lt _ hH
  rw [hw] at h1
  have h3 : w * H = H * w := Nat.mul_comm w H
  set m := (p - b - 1) % H with hm
  set z := H * w with hz
  rw [h3]
  omega

/-! ## The greedy separated subfamily -/

/-- From any finite set `P ⊆ ℕ`, one can extract a subset `kept` whose pairwise gaps all
exceed `N`, discarding at most `S.card` elements, where `S` is any set of pairs containing
all `(q, p)` with `p, q ∈ P`, `q < p`, `p - q ≤ N`. -/
lemma sel_greedy (P : Finset ℕ) (N : ℕ) (S : Finset (ℕ × ℕ))
    (hS : ∀ p ∈ P, ∀ q ∈ P, q < p → p - q ≤ N → (q, p) ∈ S) :
    ∃ kept : Finset ℕ, kept ⊆ P ∧
      (∀ p ∈ kept, ∀ q ∈ kept, p < q → N < q - p) ∧
      P.card ≤ kept.card + S.card := by
  classical
  set kept := P.filter (fun p => ∀ q ∈ P, ¬(q < p ∧ p - q ≤ N)) with hkeptdef
  refine ⟨kept, Finset.filter_subset _ _, ?_, ?_⟩
  · intro p hp q hq hpq
    rw [hkeptdef, Finset.mem_filter] at hp hq
    by_contra hle
    push Not at hle
    exact hq.2 p hp.1 ⟨hpq, hle⟩
  · have hD : ∀ p ∈ P \ kept, ∃ q, q ∈ P ∧ q < p ∧ p - q ≤ N := by
      intro p hp
      rw [Finset.mem_sdiff, hkeptdef, Finset.mem_filter] at hp
      obtain ⟨hpP, hpk⟩ := hp
      push Not at hpk
      obtain ⟨q, hqP, hql, hqN⟩ := hpk hpP
      exact ⟨q, hqP, hql, hqN⟩
    have key : (P \ kept).card ≤ S.card := by
      apply Finset.card_le_card_of_injOn
        (fun p => ((if h : ∃ q, q ∈ P ∧ q < p ∧ p - q ≤ N then h.choose else 0), p))
      · intro p hp
        rw [Finset.mem_coe] at hp
        obtain ⟨q, hqP, hql, hqN⟩ := hD p hp
        have hex : ∃ q, q ∈ P ∧ q < p ∧ p - q ≤ N := ⟨q, hqP, hql, hqN⟩
        simp only [dif_pos hex]
        obtain ⟨h1, h2, h3⟩ := hex.choose_spec
        exact hS p (Finset.mem_sdiff.mp hp).1 _ h1 h2 h3
      · intro a _ b _ hab
        simpa using congrArg Prod.snd hab
    have hsplit : (P \ kept).card + kept.card = P.card :=
      Finset.card_sdiff_add_card_eq_card (Finset.filter_subset _ _)
    omega

/-! ## The selection theorem -/

theorem separated_primes_selection :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∃ T_C : ℝ, 3 ≤ T_C ∧ ∀ t : ℝ, T_C ≤ t → ∀ K : ℕ, 2 ≤ K →
      (K : ℝ) ≤ Real.log t / Real.log (Real.log t) →
      ∃ (B : Finset ℕ) (x₀ N H : ℕ),
        (∀ p ∈ B, Nat.Prime p) ∧ B.card = K ∧
        (t ≤ (x₀:ℝ)) ∧ ((x₀:ℝ) ≤ 8*t) ∧
        (∀ p ∈ B, x₀ < p ∧ p ≤ x₀ + H) ∧
        (∀ p ∈ B, ∀ q ∈ B, p < q → N < q - p) ∧
        (ε * Real.log t ≤ (N:ℝ)) ∧ ((N:ℝ) ≤ Real.log t) ∧ 1 ≤ N ∧
        ((H:ℝ) ≤ 7 * K * Real.log t) ∧ 1 ≤ H ∧ ((x₀:ℝ) + H ≤ 9*t) := by
  classical
  obtain ⟨C_B, hCB1, T_B, hTB3, hPB⟩ := prime_pairs_bound
  obtain ⟨T_A, hTA3, hCheb⟩ := primesBetween_lower
  have hCB0 : (0:ℝ) < C_B := by linarith
  set ε₀ : ℝ := min (1/(8*C_B)) 1 with hε₀def
  have hε₀pos : 0 < ε₀ := lt_min (by positivity) one_pos
  have hε₀le1 : ε₀ ≤ 1 := min_le_right _ _
  have hε₀CB : C_B * ε₀ ≤ 1/8 := by
    have h1 : ε₀ ≤ 1/(8*C_B) := min_le_left _ _
    calc C_B * ε₀ ≤ C_B * (1/(8*C_B)) := by gcongr
      _ = 1/8 := by field_simp
  refine ⟨ε₀/2, by positivity, by linarith,
    max (max T_A T_B) (max (Real.exp (max 3 (2/ε₀))) 2560000), ?_, ?_⟩
  · exact le_trans (by norm_num) (le_trans (le_max_right _ _) (le_max_right _ _))
  intro t ht K hK2 hKle
  -- unpack the threshold
  have hTA : T_A ≤ t := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) ht
  have hTB : T_B ≤ t := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) ht
  have hexp : Real.exp (max 3 (2/ε₀)) ≤ t :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) ht
  have h256 : (2560000:ℝ) ≤ t := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) ht
  have ht0 : (0:ℝ) < t := by linarith
  have ht1 : (1:ℝ) ≤ t := by linarith
  -- Chebyshev at t+1 (before introducing local abbreviations)
  have hcheb := hCheb (t+1) (by linarith)
  -- the log scale
  set L := Real.log t with hLdef
  have hLmax : max 3 (2/ε₀) ≤ L := by
    have h1 := Real.log_le_log (Real.exp_pos _) hexp
    rwa [Real.log_exp] at h1
  have hL3 : (3:ℝ) ≤ L := le_trans (le_max_left _ _) hLmax
  have hL0 : (0:ℝ) < L := by linarith
  have hε₀L : (2:ℝ) ≤ ε₀ * L := by
    have h1 : 2/ε₀ ≤ L := le_trans (le_max_right _ _) hLmax
    calc (2:ℝ) = ε₀ * (2/ε₀) := by field_simp
      _ ≤ ε₀ * L := by gcongr
  have h100L : 100 * L^2 ≤ t := sel_log_sq_le h256
  -- K ≤ L
  have hlogL1 : (1:ℝ) ≤ Real.log L := by
    rw [Real.le_log_iff_exp_le hL0]
    have h1 := Real.exp_one_lt_d9
    linarith
  have hKL : (K:ℝ) ≤ L := by
    have h1 : L / Real.log L ≤ L := div_le_self hL0.le hlogL1
    linarith [hKle]
  have hKR : (2:ℝ) ≤ (K:ℝ) := by exact_mod_cast hK2
  have hKposR : (0:ℝ) < (K:ℝ) := by linarith
  -- the separation scale N
  set N := ⌊ε₀ * L⌋₊ with hNdef
  have hN2 : 2 ≤ N := Nat.le_floor (by exact_mod_cast hε₀L)
  have hNleR : (N:ℝ) ≤ ε₀ * L := Nat.floor_le (mul_nonneg hε₀pos.le hL0.le)
  have hNleL : (N:ℝ) ≤ L := by nlinarith only [hNleR, hε₀le1, hL0]
  have hNge : (ε₀/2) * L ≤ (N:ℝ) := by
    have h1 : ε₀ * L < (N:ℝ) + 1 := Nat.lt_floor_add_one _
    linarith only [h1, hε₀L]
  -- the window length H
  set Hn := ⌈6 * (K:ℝ) * L⌉₊ with hHdef
  have h6KL : (0:ℝ) < 6 * (K:ℝ) * L := mul_pos (mul_pos (by norm_num) hKposR) hL0
  have hH1 : 1 ≤ Hn := Nat.ceil_pos.mpr h6KL
  have hHgeR : 6 * (K:ℝ) * L ≤ (Hn:ℝ) := Nat.le_ceil _
  have hHleR : (Hn:ℝ) ≤ 7 * (K:ℝ) * L := by
    have h1 : (Hn:ℝ) < 6 * (K:ℝ) * L + 1 := Nat.ceil_lt_add_one h6KL.le
    nlinarith only [h1, hKR, hL3]
  have hHt : (Hn:ℝ) ≤ t := by
    nlinarith only [hHleR, hKL, hL0, h100L, hKposR]
  -- the pair bound at (t, N)
  have hNL2 : (N:ℝ) ≤ Real.log t ^ 2 := by
    rw [← hLdef]
    nlinarith only [hNleL, hL3, hL0]
  have hbad := hPB t hTB N hN2 hNL2
  rw [← hLdef] at hbad
  -- interval endpoints
  set b := ⌊t+1⌋₊ with hbdef
  set U := ⌊8*t⌋₊ with hUdef
  set V := ⌊8*(t+1)⌋₊ with hVdef
  have hbt : t ≤ (b:ℝ) := by
    have h1 := Nat.lt_floor_add_one (t+1)
    rw [← hbdef] at h1
    linarith only [h1]
  have hU8t : (U:ℝ) ≤ 8*t := Nat.floor_le (by linarith)
  have hU8t' : 8*t < (U:ℝ) + 1 := by
    have h1 := Nat.lt_floor_add_one (8*t)
    rw [← hUdef] at h1
    exact h1
  have hbU : b ≤ U := Nat.floor_le_floor (by linarith)
  have hUV : U ≤ V := Nat.floor_le_floor (by linarith)
  have hV8 : (V:ℝ) ≤ 8*t + 8 := by
    have h1 : (V:ℝ) ≤ 8*(t+1) := Nat.floor_le (by linarith)
    linarith only [h1]
  have hVU8 : V ≤ U + 8 := by
    by_contra hcon
    push Not at hcon
    have h1 : ((U + 9 : ℕ):ℝ) ≤ (V:ℝ) := by exact_mod_cast hcon
    push_cast at h1
    linarith only [h1, hV8, hU8t']
  -- the prime reservoirs
  set P := (Finset.Ioc b U).filter Nat.Prime with hPdef
  set P₀ := (Finset.Ioc b V).filter Nat.Prime with hP₀def
  -- Chebyshev lower bound for P₀, then P
  have hlog1 : (0:ℝ) < Real.log (t+1) := Real.log_pos (by linarith)
  have hlogt1 : Real.log (t+1) ≤ (4/3) * L := by
    have h1 : Real.log (t+1) ≤ Real.log (2*t) := Real.log_le_log (by linarith) (by linarith)
    have h2 : Real.log (2*t) = Real.log 2 + L := by
      rw [hLdef]; exact Real.log_mul (by norm_num) (by linarith)
    have h3 := Real.log_two_lt_d9
    linarith only [h1, h2, h3, hL3]
  have hchain : (3/2) * t / L ≤ 2*(t+1)/Real.log (t+1) := by
    rw [div_le_div_iff₀ hL0 hlog1]
    have hprod : t * Real.log (t+1) ≤ t * ((4/3)*L) :=
      mul_le_mul_of_nonneg_left hlogt1 ht0.le
    nlinarith only [hprod, hL0, ht0]
  have hP₀R : (3/2) * t / L ≤ (P₀.card : ℝ) := le_trans hchain hcheb
  have hsplitP : P₀.card ≤ P.card + 8 := by
    have hunion : Finset.Ioc b V = Finset.Ioc b U ∪ Finset.Ioc U V :=
      (Finset.Ioc_union_Ioc_eq_Ioc hbU hUV).symm
    have h1 : P₀ ⊆ P ∪ (Finset.Ioc U V).filter Nat.Prime := by
      rw [hP₀def, hPdef, hunion, Finset.filter_union]
    have h2 : P₀.card ≤ (P ∪ (Finset.Ioc U V).filter Nat.Prime).card :=
      Finset.card_le_card h1
    have h3 : (P ∪ (Finset.Ioc U V).filter Nat.Prime).card
        ≤ P.card + ((Finset.Ioc U V).filter Nat.Prime).card := Finset.card_union_le _ _
    have h4 : ((Finset.Ioc U V).filter Nat.Prime).card ≤ 8 := by
      calc ((Finset.Ioc U V).filter Nat.Prime).card ≤ (Finset.Ioc U V).card :=
            Finset.card_filter_le _ _
        _ = V - U := Nat.card_Ioc U V
        _ ≤ 8 := by omega
    omega
  have hPR : (3/2)*t/L - 8 ≤ (P.card : ℝ) := by
    have h1 : (P₀.card : ℝ) ≤ (P.card : ℝ) + 8 := by exact_mod_cast hsplitP
    linarith only [h1, hP₀R]
  -- membership of close pairs of P in the sieve-counted pair set
  have h9t : U ≤ ⌊9*t⌋₊ := Nat.floor_le_floor (by linarith)
  have hSmem : ∀ p ∈ P, ∀ q ∈ P, q < p → p - q ≤ N →
      (q, p) ∈ (Finset.Icc 1 ⌊9*t⌋₊ ×ˢ Finset.Icc 1 ⌊9*t⌋₊).filter
        (fun pq => Nat.Prime pq.1 ∧ Nat.Prime pq.2 ∧ pq.1 < pq.2 ∧ pq.2 - pq.1 ≤ N) := by
    intro p hp q hq hqp hgap
    rw [hPdef, Finset.mem_filter, Finset.mem_Ioc] at hp hq
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
    exact ⟨⟨⟨hq.2.one_lt.le, le_trans hq.1.2 h9t⟩, ⟨hp.2.one_lt.le, le_trans hp.1.2 h9t⟩⟩,
      hq.2, hp.2, hqp, hgap⟩
  -- greedy extraction of an N-separated subfamily
  obtain ⟨kept, hkP, hsep, hcard⟩ := sel_greedy P N _ hSmem
  have hcardR := (Nat.cast_le (α := ℝ)).mpr hcard
  push_cast at hcardR
  -- the kept family is large
  have hkeptR : (11/8)*t/L - 8 ≤ (kept.card : ℝ) := by
    have h1 : C_B * (N:ℝ) ≤ L/8 := by
      nlinarith only [hNleR, hε₀CB, hL0, hCB0]
    have hL2pos : (0:ℝ) < L^2 := pow_pos hL0 2
    have hL8pos : (0:ℝ) < 8*L := by linarith only [hL0]
    have h4 : C_B * (N:ℝ) * t / L^2 ≤ t / (8*L) := by
      rw [div_le_div_iff₀ hL2pos hL8pos]
      have hint : (0:ℝ) ≤ (L/8 - C_B * (N:ℝ)) * t * L :=
        mul_nonneg (mul_nonneg (sub_nonneg.mpr h1) ht0.le) hL0.le
      nlinarith only [hint]
    have h7 : (3/2)*t/L - t/(8*L) = (11/8)*t/L := by ring
    linarith only [hcardR, hbad, hPR, h4, h7]
  -- windows of length Hn
  set W := (U - b)/Hn + 1 with hWdef
  have hmaps : ∀ p ∈ kept, (p - b - 1)/Hn ∈ Finset.range W := by
    intro p hp
    have hpP := hkP hp
    rw [hPdef, Finset.mem_filter, Finset.mem_Ioc] at hpP
    rw [Finset.mem_range, hWdef]
    have h1 : p - b - 1 ≤ U - b := by omega
    exact Nat.lt_succ_of_le (Nat.div_le_div_right h1)
  have hWK : W * K ≤ kept.card := by
    have hHnpos : (0:ℝ) < (Hn:ℝ) := by exact_mod_cast hH1
    have hWR : (W:ℝ) ≤ 7*t/(Hn:ℝ) + 1 := by
      rw [hWdef]
      push_cast
      have h1 : ((U - b : ℕ):ℝ) ≤ 7*t := by
        rw [Nat.cast_sub hbU]
        linarith only [hU8t, hbt]
      have h2 : (((U - b)/Hn : ℕ):ℝ) ≤ ((U - b : ℕ):ℝ)/(Hn:ℝ) := Nat.cast_div_le
      have h3 : ((U - b : ℕ):ℝ)/(Hn:ℝ) ≤ 7*t/(Hn:ℝ) := by gcongr
      linarith only [h2, h3]
    have h6L : (0:ℝ) < 6*L := by linarith only [hL0]
    have hdK : 7*t/(Hn:ℝ)*(K:ℝ) ≤ 7*t/(6*L) := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ hHnpos h6L]
      have hmul := mul_le_mul_of_nonneg_left hHgeR (show (0:ℝ) ≤ 7*t by linarith only [ht0])
      nlinarith only [hmul]
    have hq : 100*L ≤ t/L := by
      rw [le_div_iff₀ hL0]
      nlinarith only [h100L]
    have hnum : 7*t/(6*L) + L ≤ (11/8)*t/L - 8 := by
      have h30 : 7*t/(6*L) = (7/6)*(t/L) := by ring
      have h31 : (11/8)*t/L = (11/8)*(t/L) := by ring
      linarith only [hq, hL3, h30, h31]
    have hcastWK : (W:ℝ) * (K:ℝ) ≤ (kept.card:ℝ) := by
      calc (W:ℝ)*(K:ℝ) ≤ (7*t/(Hn:ℝ) + 1)*(K:ℝ) :=
            mul_le_mul_of_nonneg_right hWR hKposR.le
        _ = 7*t/(Hn:ℝ)*(K:ℝ) + (K:ℝ) := by ring
        _ ≤ 7*t/(6*L) + (K:ℝ) := by linarith only [hdK]
        _ ≤ 7*t/(6*L) + L := by linarith only [hKL]
        _ ≤ (11/8)*t/L - 8 := hnum
        _ ≤ (kept.card:ℝ) := hkeptR
    exact_mod_cast hcastWK
  -- pigeonhole: some window holds K of the kept primes
  have hW1 : 1 ≤ W := by
    rw [hWdef]
    exact Nat.le_add_left 1 _
  have hne : (Finset.range W).Nonempty := ⟨0, Finset.mem_range.mpr hW1⟩
  obtain ⟨w, hwW, hfib⟩ := Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to
    hmaps hne (by rwa [Finset.card_range])
  obtain ⟨B, hBsub, hBcard⟩ := Finset.exists_subset_card_eq hfib
  have hBk : ∀ x ∈ B, x ∈ kept := fun x hx => (Finset.mem_filter.mp (hBsub hx)).1
  have hBw : ∀ x ∈ B, (x - b - 1)/Hn = w := fun x hx => (Finset.mem_filter.mp (hBsub hx)).2
  have hBP : ∀ x ∈ B, x ∈ P := fun x hx => hkP (hBk x hx)
  -- the window start
  have hwlt : w < W := Finset.mem_range.mp hwW
  have hx₀U : b + w * Hn ≤ U := by
    have hwle : w ≤ (U - b)/Hn := by
      rw [hWdef] at hwlt
      exact Nat.lt_succ_iff.mp hwlt
    calc b + w * Hn ≤ b + ((U - b)/Hn) * Hn :=
          Nat.add_le_add_left (Nat.mul_le_mul_right _ hwle) b
      _ ≤ b + (U - b) := Nat.add_le_add_left (Nat.div_mul_le_self _ _) b
      _ = U := Nat.add_sub_cancel' hbU
  have hx₀R : ((b + w * Hn : ℕ):ℝ) ≤ 8*t := by
    have h1 : ((b + w * Hn : ℕ):ℝ) ≤ (U:ℝ) := by exact_mod_cast hx₀U
    linarith only [h1, hU8t]
  -- assemble
  refine ⟨B, b + w * Hn, N, Hn, ?_, hBcard, ?_, hx₀R, ?_, ?_, hNge, hNleL, by omega, hHleR,
    hH1, ?_⟩
  · intro p hp
    have h1 := hBP p hp
    rw [hPdef, Finset.mem_filter] at h1
    exact h1.2
  · push_cast
    have h1 : (0:ℝ) ≤ (w:ℝ) * (Hn:ℝ) := by positivity
    linarith only [h1, hbt]
  · intro p hp
    have h1 := hBP p hp
    rw [hPdef, Finset.mem_filter, Finset.mem_Ioc] at h1
    exact sel_window (by omega) h1.1.1 (hBw p hp)
  · intro p hp q hq hpq
    exact hsep p (hBk p hp) q (hBk q hq) hpq
  · push_cast
    push_cast at hx₀R
    linarith only [hx₀R, hHt]

end Erdos884
