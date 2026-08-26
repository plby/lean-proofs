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
import ErdosProblems.Erdos884.CoprimeSum

open Finset ArithmeticFunction
open scoped ArithmeticFunction.omega

set_option linter.mathlibStandardSet false

/-!
# Erdős 884 — the pair sieve (Lemma B, bullets 1–5)

A Selberg sieve detecting prime pairs `(n, n+h)`: we sieve the values `n(n+h)` for
`n ∈ [1, M]` by the primes up to `z`.  The density is `ν(d) = ρ_h(d)/d` where `ρ_h` is
multiplicative with `ρ_h(p) = 1` if `p ∣ 2h` and `2` otherwise (the number of roots of
`X(X+h) mod p` for even `h`; using `2h` instead of `h` makes `ν(2) = 1/2 < 1`
unconditionally, and agrees with the root count whenever `h` is even).
-/

namespace Erdos884

/-- `ρ_h`: the multiplicative function with `ρ_h(p) = 1` if `p ∣ 2h` and `2` otherwise. -/
noncomputable def rhoFun (h : ℕ) : ArithmeticFunction ℝ :=
  ArithmeticFunction.prodPrimeFactors (fun p => if p ∣ 2 * h then (1 : ℝ) else 2)

lemma rhoFun_apply_prime {p : ℕ} (hp : p.Prime) (h : ℕ) :
    rhoFun h p = if p ∣ 2 * h then (1 : ℝ) else 2 := by
  rw [rhoFun, ArithmeticFunction.prodPrimeFactors_apply hp.ne_zero, hp.primeFactors,
    Finset.prod_singleton]

/-- The density function of the pair sieve: `ν(d) = ρ_h(d)/d`. -/
noncomputable def pairNu (h : ℕ) : ArithmeticFunction ℝ := (rhoFun h).pdiv .id

lemma pairNu_apply (h d : ℕ) : pairNu h d = rhoFun h d / d := by
  simp [pairNu, ArithmeticFunction.pdiv_apply, ArithmeticFunction.natCoe_apply,
    ArithmeticFunction.id_apply]

/-- The Selberg sieve detecting prime pairs `(n, n+h)`, `n ∈ [1,M]`, sieving by primes
`≤ z`.  Support: the values `n(n+h)`; weights `1`; total mass `M`; level `z`. -/
noncomputable def pairSieve (M h : ℕ) (z : ℝ) (hz : 1 ≤ z) : SelbergSieve where
  support := (Finset.Icc 1 M).image (fun n => n * (n + h))
  prodPrimes := primorial ⌊z⌋₊
  prodPrimes_squarefree := Sieve.primorial_squarefree _
  weights := fun _ => 1
  weights_nonneg := fun _ => zero_le_one
  totalMass := (M : ℝ)
  nu := pairNu h
  nu_mult := by unfold pairNu rhoFun; arith_mult
  nu_pos_of_prime := fun p hp _ => by
    simp only [pairNu, ArithmeticFunction.pdiv_apply, rhoFun_apply_prime hp,
      ArithmeticFunction.natCoe_apply, ArithmeticFunction.id_apply]
    have hp0 : (0:ℝ) < p := by exact_mod_cast hp.pos
    split_ifs <;> positivity
  nu_lt_one_of_prime := fun p hp _ => by
    simp only [pairNu, ArithmeticFunction.pdiv_apply, rhoFun_apply_prime hp,
      ArithmeticFunction.natCoe_apply, ArithmeticFunction.id_apply]
    have hp0 : (0:ℝ) < p := by exact_mod_cast hp.pos
    rw [div_lt_one hp0]
    split_ifs with hdvd
    · exact_mod_cast hp.one_lt
    · have hp2 : p ≠ 2 := fun h2 => hdvd (h2 ▸ ⟨h, rfl⟩)
      have h3 : 3 ≤ p := by have := hp.two_le; omega
      exact_mod_cast (by omega : 2 < p)
  level := z
  one_le_level := hz

@[simp] lemma pairSieve_prodPrimes (M h : ℕ) (z : ℝ) (hz : 1 ≤ z) :
    (pairSieve M h z hz).prodPrimes = primorial ⌊z⌋₊ := rfl

@[simp] lemma pairSieve_level (M h : ℕ) (z : ℝ) (hz : 1 ≤ z) :
    (pairSieve M h z hz).level = z := rfl

@[simp] lemma pairSieve_nu (M h : ℕ) (z : ℝ) (hz : 1 ≤ z) :
    (pairSieve M h z hz).nu = pairNu h := rfl

@[simp] lemma pairSieve_totalMass (M h : ℕ) (z : ℝ) (hz : 1 ≤ z) :
    (pairSieve M h z hz).totalMass = (M : ℝ) := rfl

/-- Positivity of the Selberg bounding sum of the pair sieve (re-export of
`SelbergSieve.selbergBoundingSum_pos` for downstream use). -/
theorem pairSieve_boundingSum_pos (M h : ℕ) (z : ℝ) (hz : 1 ≤ z) :
    (pairSieve M h z hz).selbergBoundingSum > 0 :=
  SelbergSieve.selbergBoundingSum_pos _

/-! ## Counting the roots of `X(X+h)` modulo `d` -/

/-- The number of residues `r < d` with `d ∣ r(r+h)`. -/
def nroots (h d : ℕ) : ℕ := ((Finset.range d).filter (fun r => d ∣ r * (r + h))).card

lemma nroots_zero (h : ℕ) : nroots h 0 = 0 := by simp [nroots]

lemma nroots_one (h : ℕ) : nroots h 1 = 1 := by simp [nroots]

/-- Divisibility of `n(n+h)` by `d` only depends on `n mod d`. -/
lemma dvd_shift_iff_mod (d h n : ℕ) : d ∣ n * (n + h) ↔ d ∣ (n % d) * (n % d + h) := by
  have h1 : (n % d) * (n % d + h) ≡ n * (n + h) [MOD d] :=
    (Nat.mod_modEq n d).mul ((Nat.mod_modEq n d).add_right h)
  constructor
  · intro hdvd
    exact Nat.modEq_zero_iff_dvd.mp (h1.trans (Nat.modEq_zero_iff_dvd.mpr hdvd))
  · intro hdvd
    exact Nat.modEq_zero_iff_dvd.mp (h1.symm.trans (Nat.modEq_zero_iff_dvd.mpr hdvd))

/-- The root count as the size of the zero set of `x(x+h)` in `ZMod d`. -/
lemma nroots_eq_card_zmod (h d : ℕ) [NeZero d] :
    nroots h d =
      (Finset.univ.filter (fun x : ZMod d => x * (x + (h : ZMod d)) = 0)).card := by
  unfold nroots
  apply Finset.card_bij (fun (r : ℕ) _ => (r : ZMod d))
  · intro r hr
    simp only [Finset.mem_filter, Finset.mem_range] at hr
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hc : ((r * (r + h) : ℕ) : ZMod d) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hr.2
    push_cast at hc
    exact hc
  · intro r₁ hr₁ r₂ hr₂ heq
    simp only [Finset.mem_filter, Finset.mem_range] at hr₁ hr₂
    have := congrArg ZMod.val heq
    rwa [ZMod.val_cast_of_lt hr₁.1, ZMod.val_cast_of_lt hr₂.1] at this
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    have hval : x.val ∈ (Finset.range d).filter (fun r => d ∣ r * (r + h)) := by
      simp only [Finset.mem_filter, Finset.mem_range]
      refine ⟨ZMod.val_lt x, (ZMod.natCast_eq_zero_iff _ _).mp ?_⟩
      push_cast
      rw [ZMod.natCast_rightInverse x]
      exact hx
    exact ⟨x.val, hval, ZMod.natCast_rightInverse x⟩

/-- CRT: the root count is multiplicative. -/
lemma nroots_mul (h : ℕ) {m n : ℕ} (hcop : Nat.Coprime m n) :
    nroots h (m * n) = nroots h m * nroots h n := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have hn1 : n = 1 := by simpa using hcop
    subst hn1; simp [nroots_zero, nroots_one]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hm1 : m = 1 := by simpa using hcop
    subst hm1; simp [nroots_zero, nroots_one]
  have : NeZero m := ⟨hm.ne'⟩
  have : NeZero n := ⟨hn.ne'⟩
  have : NeZero (m * n) := ⟨by positivity⟩
  rw [nroots_eq_card_zmod, nroots_eq_card_zmod, nroots_eq_card_zmod,
    ← Finset.card_product, ← Finset.filter_product, Finset.univ_product_univ]
  have crt := ZMod.chineseRemainder hcop
  have hiff : ∀ x : ZMod (m * n),
      (x * (x + (h : ZMod (m * n))) = 0) ↔
        ((crt x).1 * ((crt x).1 + (h : ZMod m)) = 0 ∧
          (crt x).2 * ((crt x).2 + (h : ZMod n)) = 0) := by
    intro x
    rw [← EmbeddingLike.map_eq_zero_iff (f := crt), map_mul, map_add, map_natCast,
      Prod.ext_iff]
    simp [Prod.fst_mul, Prod.fst_add, Prod.snd_mul, Prod.snd_add]
  apply Finset.card_bij (fun x _ => crt x)
  · intro x hxmem
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hxmem ⊢
    exact (hiff x).mp hxmem
  · intro x₁ _ x₂ _ heq
    exact crt.injective heq
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    refine ⟨crt.symm y, ?_, crt.apply_symm_apply y⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hiff (crt.symm y), crt.apply_symm_apply y]
    exact hy

/-- Root count at a prime: `1` root if `p ∣ 2h`, else `2` (`h` even). -/
lemma nroots_prime {p : ℕ} (hp : p.Prime) {h : ℕ} (heven : 2 ∣ h) :
    nroots h p = if p ∣ 2 * h then 1 else 2 := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have : Fact p.Prime := ⟨hp⟩
  rw [nroots_eq_card_zmod]
  have hset : (Finset.univ.filter (fun x : ZMod p => x * (x + (h : ZMod p)) = 0))
      = {0, -(h : ZMod p)} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro hx
      rcases mul_eq_zero.mp hx with h0 | h1
      · exact Or.inl h0
      · exact Or.inr (eq_neg_of_add_eq_zero_left h1)
    · rintro (rfl | rfl)
      · simp
      · simp
  rw [hset]
  by_cases hph : p ∣ h
  · have h0 : (h : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hph
    rw [if_pos (hph.mul_left 2), h0, neg_zero]
    simp
  · have h0 : (h : ZMod p) ≠ 0 := fun hc => hph ((ZMod.natCast_eq_zero_iff _ _).mp hc)
    have hnodvd : ¬ p ∣ 2 * h := by
      intro hc
      rcases (Nat.Prime.dvd_mul hp).mp hc with h2 | hh
      · have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2
        exact hph (hp2 ▸ heven)
      · exact hph hh
    rw [if_neg hnodvd]
    have hne : (0 : ZMod p) ∉ ({-(h : ZMod p)} : Finset (ZMod p)) := by
      simp only [Finset.mem_singleton]
      intro hc
      exact h0 (neg_eq_zero.mp hc.symm)
    rw [Finset.card_insert_of_notMem hne, Finset.card_singleton]

/-! ## `ρ_h` equals the root count on squarefree numbers (for even `h`) -/

/-- The root count as an arithmetic function. -/
def nrootsA (h : ℕ) : ArithmeticFunction ℕ := ⟨nroots h, nroots_zero h⟩

@[simp] lemma nrootsA_apply (h d : ℕ) : nrootsA h d = nroots h d := rfl

lemma nrootsA_isMultiplicative (h : ℕ) : (nrootsA h).IsMultiplicative := by
  constructor
  · exact nroots_one h
  · intro m n hcop
    exact nroots_mul h hcop

lemma nroots_eq_prod_primeFactors (h : ℕ) {d : ℕ} (hd : Squarefree d) :
    nroots h d = ∏ p ∈ d.primeFactors, nroots h p := by
  have hmap := (nrootsA_isMultiplicative h).map_prod_of_subset_primeFactors d
    d.primeFactors Finset.Subset.rfl
  simp only [nrootsA_apply] at hmap
  conv_lhs => rw [← Nat.prod_primeFactors_of_squarefree hd]
  exact hmap

lemma rhoFun_eq_nroots {h : ℕ} (heven : 2 ∣ h) {d : ℕ} (hd : Squarefree d) :
    rhoFun h d = (nroots h d : ℝ) := by
  rw [rhoFun, ArithmeticFunction.prodPrimeFactors_apply hd.ne_zero,
    nroots_eq_prod_primeFactors h hd]
  push_cast
  apply Finset.prod_congr rfl
  intro p hp
  rw [nroots_prime (Nat.prime_of_mem_primeFactors hp) heven]
  split_ifs <;> norm_num

lemma rhoFun_nonneg (h d : ℕ) : 0 ≤ rhoFun h d := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  · rw [rhoFun, ArithmeticFunction.prodPrimeFactors_apply hd.ne']
    apply Finset.prod_nonneg
    intro p _
    split_ifs <;> norm_num

lemma rhoFun_le_two_pow (h : ℕ) {d : ℕ} (hd : d ≠ 0) :
    rhoFun h d ≤ 2 ^ d.primeFactors.card := by
  rw [rhoFun, ArithmeticFunction.prodPrimeFactors_apply hd]
  calc ∏ p ∈ d.primeFactors, (if p ∣ 2 * h then (1:ℝ) else 2)
      ≤ ∏ p ∈ d.primeFactors, (2:ℝ) := by
        apply Finset.prod_le_prod
        · intro p _; split_ifs <;> norm_num
        · intro p _; split_ifs <;> norm_num
    _ = 2 ^ d.primeFactors.card := by rw [Finset.prod_const]

/-! ## Counting a residue class in `[1, M]` -/

lemma range_succ_eq_insert_Icc (M : ℕ) :
    Finset.range (M + 1) = insert 0 (Finset.Icc 1 M) := by
  ext n
  simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
  omega

/-- The number of `n ∈ [1, M]` in a fixed residue class mod `d` is within `1`
of `M/d`. -/
lemma card_Icc_filter_mod (M : ℕ) {d r : ℕ} (hd : 0 < d) (hr : r < d) :
    |(((Finset.Icc 1 M).filter (fun n => n % d = r)).card : ℝ) - M / d| ≤ 1 := by
  have hcount : ((Finset.range (M + 1)).filter (fun n => n % d = r)).card
      = (M + 1) / d + if r < (M + 1) % d then 1 else 0 := by
    have h1 : (Finset.range (M + 1)).filter (fun n => n % d = r)
        = (Finset.range (M + 1)).filter (fun x => x ≡ r [MOD d]) := by
      apply Finset.filter_congr
      intro n _
      simp [Nat.ModEq, Nat.mod_eq_of_lt hr]
    rw [h1, ← Nat.count_eq_card_filter_range, Nat.count_modEq_card _ hd r,
      Nat.mod_eq_of_lt hr]
  have hsplit : ((Finset.range (M + 1)).filter (fun n => n % d = r)).card
      = ((Finset.Icc 1 M).filter (fun n => n % d = r)).card
        + if r = 0 then 1 else 0 := by
    rw [range_succ_eq_insert_Icc, Finset.filter_insert]
    by_cases hr0 : r = 0
    · rw [if_pos (show (0:ℕ) % d = r by rw [Nat.zero_mod, hr0]), if_pos hr0,
        Finset.card_insert_of_notMem (by simp)]
    · rw [if_neg (show ¬ (0:ℕ) % d = r by
        rw [Nat.zero_mod]; exact fun hc => hr0 hc.symm), if_neg hr0, add_zero]
  have hkey : ((Finset.Icc 1 M).filter (fun n => n % d = r)).card
        + (if r = 0 then 1 else 0)
      = (M + 1) / d + if r < (M + 1) % d then 1 else 0 := by
    rw [← hsplit, hcount]
  have hdm : d * ((M + 1) / d) + (M + 1) % d = M + 1 := Nat.div_add_mod (M + 1) d
  have hsd : (M + 1) % d < d := Nat.mod_lt _ hd
  set c := ((Finset.Icc 1 M).filter (fun n => n % d = r)).card with hcdef
  set a := (M + 1) / d with hadef
  set s := (M + 1) % d with hsdef
  have hdR : (0:ℝ) < d := by exact_mod_cast hd
  have hdmR : (d:ℝ) * a + s = M + 1 := by exact_mod_cast hdm
  have hsdR : (s:ℝ) + 1 ≤ d := by exact_mod_cast hsd
  have hs0 : (0:ℝ) ≤ s := by positivity
  have hub : (M:ℝ) / d ≤ c + 1 := by
    rw [div_le_iff₀ hdR]
    rcases eq_or_ne r 0 with hr0 | hr0
    · rw [if_pos hr0] at hkey
      by_cases hε : r < s
      · rw [if_pos hε] at hkey
        have hca : (c:ℝ) = a := by exact_mod_cast (by omega : c = a)
        rw [hca]; nlinarith
      · rw [if_neg hε] at hkey
        have hs0' : s = 0 := by omega
        have hca : (c:ℝ) + 1 = a := by exact_mod_cast hkey
        have : (s:ℝ) = 0 := by exact_mod_cast hs0'
        nlinarith
    · rw [if_neg hr0] at hkey
      by_cases hε : r < s
      · rw [if_pos hε] at hkey
        have hca : (c:ℝ) = a + 1 := by exact_mod_cast hkey
        rw [hca]; nlinarith
      · rw [if_neg hε] at hkey
        have hca : (c:ℝ) = a := by exact_mod_cast (by omega : c = a)
        rw [hca]; nlinarith
  have hlb : (c:ℝ) - 1 ≤ M / d := by
    rw [le_div_iff₀ hdR]
    rcases eq_or_ne r 0 with hr0 | hr0
    · rw [if_pos hr0] at hkey
      by_cases hε : r < s
      · rw [if_pos hε] at hkey
        have hs1 : (1:ℝ) ≤ s := by exact_mod_cast (by omega : 1 ≤ s)
        have hca : (c:ℝ) = a := by exact_mod_cast (by omega : c = a)
        rw [hca]; nlinarith
      · rw [if_neg hε] at hkey
        have hca : (c:ℝ) + 1 = a := by exact_mod_cast hkey
        nlinarith
    · rw [if_neg hr0] at hkey
      by_cases hε : r < s
      · rw [if_pos hε] at hkey
        have hs1 : (1:ℝ) ≤ s := by exact_mod_cast (by omega : 1 ≤ s)
        have hca : (c:ℝ) = a + 1 := by exact_mod_cast hkey
        rw [hca]; nlinarith
      · rw [if_neg hε] at hkey
        have hca : (c:ℝ) = a := by exact_mod_cast (by omega : c = a)
        rw [hca]; nlinarith
  rw [abs_le]
  constructor <;> linarith

/-! ## The multiplicity sum and remainder of the pair sieve -/

@[simp] lemma pairSieve_support (M h : ℕ) (z : ℝ) (hz : 1 ≤ z) :
    (pairSieve M h z hz).support = (Finset.Icc 1 M).image (fun n => n * (n + h)) := rfl

@[simp] lemma pairSieve_weights (M h : ℕ) (z : ℝ) (hz : 1 ≤ z) :
    (pairSieve M h z hz).weights = fun _ => 1 := rfl

lemma mul_shift_injOn (h M : ℕ) :
    Set.InjOn (fun n => n * (n + h)) ((Finset.Icc 1 M : Finset ℕ) : Set ℕ) := by
  intro a ha b hb heq
  simp only [Finset.coe_Icc, Set.mem_Icc] at ha hb
  dsimp only at heq
  rcases Nat.lt_trichotomy a b with hab | hab | hab
  · exact absurd heq
      (Nat.ne_of_lt (mul_lt_mul'' hab (by omega) (Nat.zero_le _) (Nat.zero_le _)))
  · exact hab
  · exact absurd heq.symm
      (Nat.ne_of_lt (mul_lt_mul'' hab (by omega) (Nat.zero_le _) (Nat.zero_le _)))

lemma pairSieve_multSum (M h : ℕ) (z : ℝ) (hz : 1 ≤ z) (d : ℕ) :
    BoundingSieve.multSum (s := (pairSieve M h z hz).toBoundingSieve) d
      = (((Finset.Icc 1 M).filter (fun n => d ∣ n * (n + h))).card : ℝ) := by
  unfold BoundingSieve.multSum
  simp only [pairSieve_support, pairSieve_weights]
  rw [Finset.sum_image (mul_shift_injOn h M)]
  simp only [Finset.sum_boole]

/-- The key remainder estimate: for squarefree `d` and even `h`,
`|multSum d − ν(d)·M| ≤ 2^ω(d)`. -/
lemma pairSieve_abs_rem_le (M h : ℕ) (z : ℝ) (hz : 1 ≤ z) (heven : 2 ∣ h)
    {d : ℕ} (hd : Squarefree d) :
    |BoundingSieve.rem (s := (pairSieve M h z hz).toBoundingSieve) d|
      ≤ 2 ^ d.primeFactors.card := by
  have hd0 : 0 < d := Nat.pos_of_ne_zero hd.ne_zero
  have hmaps : Set.MapsTo (fun n => n % d)
      (((Finset.Icc 1 M).filter (fun n => d ∣ n * (n + h)) : Finset ℕ) : Set ℕ)
      (((Finset.range d).filter (fun r => d ∣ r * (r + h)) : Finset ℕ) : Set ℕ) := by
    intro n hn
    rw [Finset.mem_coe, Finset.mem_filter] at hn
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.mod_lt n hd0, (dvd_shift_iff_mod d h n).mp hn.2⟩
  have hdecomp := Finset.card_eq_sum_card_fiberwise hmaps
  have hfib : ∀ r ∈ (Finset.range d).filter (fun r => d ∣ r * (r + h)),
      (((Finset.Icc 1 M).filter (fun n => d ∣ n * (n + h))).filter
          (fun n => n % d = r))
        = (Finset.Icc 1 M).filter (fun n => n % d = r) := by
    intro r hr
    rw [Finset.mem_filter, Finset.mem_range] at hr
    rw [Finset.filter_filter]
    apply Finset.filter_congr
    intro n _
    constructor
    · exact fun hx => hx.2
    · intro hx
      exact ⟨(dvd_shift_iff_mod d h n).mpr (by rw [hx]; exact hr.2), hx⟩
  have hdecomp' : (((Finset.Icc 1 M).filter (fun n => d ∣ n * (n + h))).card : ℝ)
      = ∑ r ∈ (Finset.range d).filter (fun r => d ∣ r * (r + h)),
          (((Finset.Icc 1 M).filter (fun n => n % d = r)).card : ℝ) := by
    rw [hdecomp, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro r hr
    rw [hfib r hr]
  have hnu : pairNu h d * (M : ℝ)
      = ∑ _r ∈ (Finset.range d).filter (fun r => d ∣ r * (r + h)), (M : ℝ) / d := by
    rw [Finset.sum_const, nsmul_eq_mul, pairNu_apply, rhoFun_eq_nroots heven hd]
    have hcard : (((Finset.range d).filter (fun r => d ∣ r * (r + h))).card : ℝ)
        = (nroots h d : ℝ) := rfl
    rw [hcard]
    ring
  unfold BoundingSieve.rem
  rw [pairSieve_multSum, pairSieve_nu, pairSieve_totalMass]
  calc |(((Finset.Icc 1 M).filter (fun n => d ∣ n * (n + h))).card : ℝ)
        - pairNu h d * (M : ℝ)|
      = |∑ r ∈ (Finset.range d).filter (fun r => d ∣ r * (r + h)),
          ((((Finset.Icc 1 M).filter (fun n => n % d = r)).card : ℝ) - (M : ℝ) / d)| := by
        rw [hdecomp', hnu, Finset.sum_sub_distrib]
    _ ≤ ∑ r ∈ (Finset.range d).filter (fun r => d ∣ r * (r + h)),
          |(((Finset.Icc 1 M).filter (fun n => n % d = r)).card : ℝ) - (M : ℝ) / d| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _r ∈ (Finset.range d).filter (fun r => d ∣ r * (r + h)), (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro r hr
        rw [Finset.mem_filter, Finset.mem_range] at hr
        exact card_Icc_filter_mod M hd0 hr.1
    _ = (nroots h d : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]
        rfl
    _ = rhoFun h d := (rhoFun_eq_nroots heven hd).symm
    _ ≤ 2 ^ d.primeFactors.card := rhoFun_le_two_pow h hd.ne_zero

/-! ## The error sum bound -/

lemma omega_eq_card_primeFactors (d : ℕ) :
    ArithmeticFunction.cardDistinctFactors d = d.primeFactors.card := by
  rw [ArithmeticFunction.cardDistinctFactors_apply, ← List.card_toFinset]
  rfl

/-! ## Prime pairs land in the sifted set -/

lemma pairs_card_le_siftedSum_add (M h : ℕ) (z : ℝ) (hz : 1 ≤ z) (hh : 0 < h) :
    (((Finset.Icc 1 M).filter (fun n => Nat.Prime n ∧ Nat.Prime (n + h))).card : ℝ)
      ≤ BoundingSieve.siftedSum (s := (pairSieve M h z hz).toBoundingSieve) + (z + 1) := by
  classical
  have hsift := Sieve.siftedSum_eq (pairSieve M h z hz) (fun _ _ => rfl) z hz rfl
  set A := (Finset.Icc 1 M).filter (fun n => Nat.Prime n ∧ Nat.Prime (n + h)) with hA
  have hsplit : A.card = (A.filter (fun n : ℕ => (n:ℝ) ≤ z)).card
      + (A.filter (fun n : ℕ => ¬ ((n:ℝ) ≤ z))).card :=
    (Finset.card_filter_add_card_filter_not (fun n : ℕ => (n:ℝ) ≤ z)).symm
  have h1 : (A.filter (fun n : ℕ => (n:ℝ) ≤ z)).card ≤ ⌊z⌋₊ := by
    have hsub : A.filter (fun n : ℕ => (n:ℝ) ≤ z) ⊆ Finset.Icc 1 ⌊z⌋₊ := by
      intro n hn
      rw [Finset.mem_filter, hA, Finset.mem_filter, Finset.mem_Icc] at hn
      rw [Finset.mem_Icc]
      exact ⟨hn.1.1.1, Nat.le_floor hn.2⟩
    calc (A.filter (fun n : ℕ => (n:ℝ) ≤ z)).card ≤ (Finset.Icc 1 ⌊z⌋₊).card :=
          Finset.card_le_card hsub
      _ = ⌊z⌋₊ := by rw [Nat.card_Icc]; omega
  have h2 : (A.filter (fun n : ℕ => ¬ ((n:ℝ) ≤ z))).card
      ≤ (((pairSieve M h z hz).support).filter
          (fun d => ∀ p : ℕ, p.Prime → (p:ℝ) ≤ z → ¬ p ∣ d)).card := by
    apply Finset.card_le_card_of_injOn (fun n => n * (n + h))
    · intro n hn
      have hn' : n ∈ A.filter (fun n : ℕ => ¬ ((n:ℝ) ≤ z)) := hn
      rw [Finset.mem_filter, hA, Finset.mem_filter, Finset.mem_Icc] at hn'
      obtain ⟨⟨⟨hn1, hnM⟩, hp, hq⟩, hzn⟩ := hn'
      have hgoal : n * (n + h) ∈ ((pairSieve M h z hz).support).filter
          (fun d => ∀ p : ℕ, p.Prime → (p:ℝ) ≤ z → ¬ p ∣ d) := by
        rw [Finset.mem_filter]
        constructor
        · rw [pairSieve_support]
          exact Finset.mem_image_of_mem _ (Finset.mem_Icc.mpr ⟨hn1, hnM⟩)
        · intro p hpp hpz hpdvd
          rcases (Nat.Prime.dvd_mul hpp).mp hpdvd with hd | hd
          · rcases (Nat.prime_dvd_prime_iff_eq hpp hp).mp hd with rfl
            exact hzn hpz
          · have hpn : p = n + h := (Nat.prime_dvd_prime_iff_eq hpp hq).mp hd
            apply hzn
            have hle : ((n + h : ℕ) : ℝ) ≤ z := by rw [← hpn]; exact hpz
            push_cast at hle
            have hh0 : (0:ℝ) ≤ h := by positivity
            linarith
      exact hgoal
    · apply (mul_shift_injOn h M).mono
      intro n hn
      have hn' : n ∈ A.filter (fun n : ℕ => ¬ ((n:ℝ) ≤ z)) := hn
      have hnA : n ∈ A := Finset.mem_of_mem_filter _ hn'
      rw [hA] at hnA
      exact Finset.mem_coe.mpr (Finset.mem_of_mem_filter _ hnA)
  rw [hsift]
  have hfloor : ((⌊z⌋₊ : ℕ) : ℝ) ≤ z := Nat.floor_le (by linarith)
  have h1R : ((A.filter (fun n : ℕ => (n:ℝ) ≤ z)).card : ℝ) ≤ z :=
    le_trans (by exact_mod_cast h1) hfloor
  have h2R : ((A.filter (fun n : ℕ => ¬ ((n:ℝ) ≤ z))).card : ℝ)
      ≤ ((((pairSieve M h z hz).support).filter
          (fun d => ∀ p : ℕ, p.Prime → (p:ℝ) ≤ z → ¬ p ∣ d)).card : ℝ) := by
    exact_mod_cast h2
  have hAR : (A.card : ℝ) = ((A.filter (fun n : ℕ => (n:ℝ) ≤ z)).card : ℝ)
      + ((A.filter (fun n : ℕ => ¬ ((n:ℝ) ≤ z))).card : ℝ) := by
    exact_mod_cast hsplit
  rw [hAR]
  linarith

/-! ## The main sieve bound for prime pairs -/

theorem pairSieve_pairs_le (M h : ℕ) (z : ℝ) (hz : 1 ≤ z) (heven : 2 ∣ h) (hh : 0 < h) :
    (((Finset.Icc 1 M).filter (fun n => Nat.Prime n ∧ Nat.Prime (n+h))).card : ℝ)
      ≤ (M : ℝ) / (pairSieve M h z hz).selbergBoundingSum
        + ∑ d ∈ Finset.Icc 1 ⌊z⌋₊, (6:ℝ)^(d.primeFactors.card) + (z + 1) := by
  have hpairs := pairs_card_le_siftedSum_add M h z hz hh
  refine hpairs.trans ?_
  have hb := SelbergSieve.selberg_bound_simple (pairSieve M h z hz)
  simp only [pairSieve_totalMass, pairSieve_prodPrimes, pairSieve_level] at hb
  refine ((add_le_add_iff_right (z + 1)).mpr hb).trans ?_
  refine (add_le_add_iff_right (z + 1)).mpr ?_
  refine (add_le_add_iff_left _).mpr ?_
  -- error sum ≤ ∑_{d ≤ ⌊z⌋} 6^ω(d)
  refine le_trans (Finset.sum_le_sum
    (g := fun d : ℕ => if (d:ℝ) ≤ z then (6:ℝ) ^ d.primeFactors.card else 0) ?_) ?_
  · intro d hd
    have hsq : Squarefree d :=
      (Sieve.primorial_squarefree _).squarefree_of_dvd (Nat.dvd_of_mem_divisors hd)
    by_cases hdz : (d : ℝ) ≤ z
    · simp only [hdz, if_true]
      calc (3:ℝ) ^ (ω d)
            * |BoundingSieve.rem (s := (pairSieve M h z hz).toBoundingSieve) d|
          ≤ (3:ℝ) ^ (ω d) * 2 ^ d.primeFactors.card := by
            apply mul_le_mul_of_nonneg_left (pairSieve_abs_rem_le M h z hz heven hsq)
            positivity
        _ = (6:ℝ) ^ d.primeFactors.card := by
            rw [omega_eq_card_primeFactors, ← mul_pow]
            norm_num
    · simp [hdz]
  · rw [← Finset.sum_filter]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro d hd
      rw [Finset.mem_filter] at hd
      rw [Finset.mem_Icc]
      exact ⟨Nat.pos_of_mem_divisors hd.1, Nat.le_floor hd.2⟩
    · intro d _ _
      positivity

/-! ## Lower bound for the Selberg bounding sum -/

theorem pairSieve_boundingSum_ge (M h : ℕ) (z : ℝ) (hz : 1 ≤ z) :
    ∑ ℓ ∈ (Finset.Icc 1 ⌊Real.sqrt z⌋₊).filter
        (fun ℓ => Squarefree ℓ ∧ ℓ.Coprime (2*h)),
        (2:ℝ)^(ℓ.primeFactors.card) / ℓ
      ≤ (pairSieve M h z hz).selbergBoundingSum := by
  have hz0 : (0:ℝ) ≤ z := by linarith
  -- every ℓ in the index set is a divisor of the primorial with ℓ² ≤ z
  have hmem : ∀ ℓ ∈ (Finset.Icc 1 ⌊Real.sqrt z⌋₊).filter
      (fun ℓ => Squarefree ℓ ∧ ℓ.Coprime (2*h)),
      ℓ ∈ (primorial ⌊z⌋₊).divisors.filter (fun l : ℕ => (l:ℝ)^2 ≤ z) := by
    intro ℓ hℓ
    rw [Finset.mem_filter, Finset.mem_Icc] at hℓ
    obtain ⟨⟨hℓ1, hℓsqrt⟩, hℓsq, hℓcop⟩ := hℓ
    have hℓR : (ℓ:ℝ) ≤ Real.sqrt z :=
      le_trans (Nat.cast_le.mpr hℓsqrt) (Nat.floor_le (Real.sqrt_nonneg z))
    have hsq : ((ℓ:ℝ))^2 ≤ z := by
      calc ((ℓ:ℝ))^2 ≤ (Real.sqrt z)^2 := by gcongr
        _ = z := Real.sq_sqrt hz0
    have hdvd : ℓ ∣ primorial ⌊z⌋₊ := by
      rw [← Nat.prod_primeFactors_of_squarefree hℓsq]
      apply Sieve.prod_primes_dvd_of_dvd
      · intro p hp
        rw [Sieve.prime_dvd_primorial_iff _ _ (Nat.prime_of_mem_primeFactors hp)]
        have hpl : p ≤ ℓ := Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors hp)
        have hsz : Real.sqrt z ≤ z := Sieve.sqrt_le_self z hz
        exact le_trans hpl (le_trans hℓsqrt (Nat.floor_mono hsz))
      · intro p hp
        exact Nat.prime_of_mem_primeFactors hp
    rw [Finset.mem_filter, Nat.mem_divisors]
    exact ⟨⟨hdvd, (Sieve.primorial_squarefree _).ne_zero⟩, hsq⟩
  -- termwise: 2^ω(ℓ)/ℓ = ν(ℓ) ≤ g(ℓ)
  have hterm : ∀ ℓ ∈ (Finset.Icc 1 ⌊Real.sqrt z⌋₊).filter
      (fun ℓ => Squarefree ℓ ∧ ℓ.Coprime (2*h)),
      (2:ℝ)^(ℓ.primeFactors.card) / ℓ
        ≤ SelbergSieve.selbergTerms (pairSieve M h z hz).toBoundingSieve ℓ := by
    intro ℓ hℓ
    have hℓdvd : ℓ ∣ primorial ⌊z⌋₊ := by
      have hm := hmem ℓ hℓ
      rw [Finset.mem_filter, Nat.mem_divisors] at hm
      exact hm.1.1
    rw [Finset.mem_filter, Finset.mem_Icc] at hℓ
    obtain ⟨⟨hℓ1, _⟩, hℓsq, hℓcop⟩ := hℓ
    have hnu_eq : pairNu h ℓ = (2:ℝ)^(ℓ.primeFactors.card) / ℓ := by
      rw [pairNu_apply, rhoFun, ArithmeticFunction.prodPrimeFactors_apply hℓsq.ne_zero]
      congr 1
      calc (∏ p ∈ ℓ.primeFactors, if p ∣ 2*h then (1:ℝ) else 2)
          = ∏ _p ∈ ℓ.primeFactors, (2:ℝ) := by
            apply Finset.prod_congr rfl
            intro p hp
            rw [if_neg]
            intro hpdvd
            have hpp := Nat.prime_of_mem_primeFactors hp
            have hone : p ∣ 1 :=
              hℓcop ▸ Nat.dvd_gcd (Nat.dvd_of_mem_primeFactors hp) hpdvd
            exact hpp.ne_one (Nat.dvd_one.mp hone)
        _ = (2:ℝ) ^ ℓ.primeFactors.card := by rw [Finset.prod_const]
    rw [SelbergSieve.selbergTerms_apply, pairSieve_nu, ← hnu_eq]
    have hν : 0 ≤ pairNu h ℓ := by rw [hnu_eq]; positivity
    have hfac : ∀ p ∈ ℓ.primeFactors, (1:ℝ) ≤ 1 / (1 - pairNu h p) := by
      intro p hp
      have hpp := Nat.prime_of_mem_primeFactors hp
      have hpP : p ∣ primorial ⌊z⌋₊ := (Nat.dvd_of_mem_primeFactors hp).trans hℓdvd
      have h1 : 0 < pairNu h p := by
        have hpos := BoundingSieve.nu_pos_of_dvd_prodPrimes
          (s := (pairSieve M h z hz).toBoundingSieve) (d := p) hpP
        simpa [pairSieve_nu] using hpos
      have h2 : pairNu h p < 1 := by
        have hlt := (pairSieve M h z hz).nu_lt_one_of_prime p hpp hpP
        simpa [pairSieve_nu] using hlt
      have hpos : 0 < 1 - pairNu h p := by linarith
      rw [le_div_iff₀ hpos, one_mul]
      linarith
    have hprod : (1:ℝ) ≤ ∏ p ∈ ℓ.primeFactors, 1 / (1 - pairNu h p) := by
      have hle : ∏ _p ∈ ℓ.primeFactors, (1:ℝ)
          ≤ ∏ p ∈ ℓ.primeFactors, 1 / (1 - pairNu h p) := by
        apply Finset.prod_le_prod
        · intro p _
          norm_num
        · intro p hp
          exact hfac p hp
      simpa using hle
    linarith [mul_le_mul_of_nonneg_left hprod hν]
  calc ∑ ℓ ∈ (Finset.Icc 1 ⌊Real.sqrt z⌋₊).filter
        (fun ℓ => Squarefree ℓ ∧ ℓ.Coprime (2*h)),
        (2:ℝ)^(ℓ.primeFactors.card) / ℓ
      ≤ ∑ ℓ ∈ (Finset.Icc 1 ⌊Real.sqrt z⌋₊).filter
          (fun ℓ => Squarefree ℓ ∧ ℓ.Coprime (2*h)),
          SelbergSieve.selbergTerms (pairSieve M h z hz).toBoundingSieve ℓ :=
        Finset.sum_le_sum hterm
    _ ≤ ∑ l ∈ (primorial ⌊z⌋₊).divisors.filter (fun l : ℕ => (l:ℝ)^2 ≤ z),
          SelbergSieve.selbergTerms (pairSieve M h z hz).toBoundingSieve l := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (fun ℓ hℓ => hmem ℓ hℓ)
        intro l hl _
        apply le_of_lt
        apply SelbergSieve.selbergTerms_pos
        rw [Finset.mem_filter, Nat.mem_divisors] at hl
        exact hl.1.1
    _ = (pairSieve M h z hz).selbergBoundingSum := by
        rw [Finset.sum_filter]
        simp only [SelbergSieve.selbergBoundingSum, pairSieve_prodPrimes, pairSieve_level]
        apply Finset.sum_congr rfl
        intro l _
        by_cases hle : (l : ℝ)^2 ≤ z <;> simp [hle]

end Erdos884
