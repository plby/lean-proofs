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
import ErdosProblems.Erdos884.Selection

set_option linter.mathlibStandardSet false

/-!
# Erdős 884 — the incremental multiscale step (`ScaleStep884`)

For coprime `n` and `m := ∏ p ∈ B, p` (a fresh window of `K` primes, all exceeding
everything about `n`), we bound `gapSum ((n*m).divisors)` by classifying consecutive
divisor pairs `(d₁, d₂)` via their coprime components `d = gcd d n * gcd d m`:

* (C1) equal `m`-component: projects to a consecutive pair of `n.divisors`;
* (C2) equal `n`-component: projects to a consecutive pair of `m.divisors`
  (handled by `oneScale_gapSum_le`);
* (C3) both components differ: the gap is at least `δ/4` of the endpoint, where `δ`
  is the minimal log-gap of `n.divisors`.

Exports: `scaleStep_gapSum_le`, `exists_min_log_gap`, `sum_inv_divisors_mul`.
All internal helpers are prefixed `ss_`.
-/

namespace Erdos884

/-! ### Coprimality and the component decomposition of divisors of `n * m` -/

lemma ss_coprime_prod {n x₀ : ℕ} {B : Finset ℕ} (hn : n ≠ 0)
    (hprime : ∀ p ∈ B, p.Prime) (hwin : ∀ p ∈ B, x₀ < p) (hnx : n ≤ x₀) :
    n.Coprime (∏ p ∈ B, p) := by
  refine Nat.Coprime.prod_right fun p hp => ?_
  refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd (hprime p hp)).mpr ?_)
  intro hdvd
  have h1 : p ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdvd
  have h2 := hwin p hp
  omega

lemma ss_decomp {n m : ℕ} (hcop : n.Coprime m) {d : ℕ} (hd : d ∈ (n * m).divisors) :
    d = d.gcd n * d.gcd m ∧ d.gcd n ∈ n.divisors ∧ d.gcd m ∈ m.divisors := by
  have hnm : n * m ≠ 0 := (Nat.mem_divisors.mp hd).2
  have hn : n ≠ 0 := fun h => hnm (by simp [h])
  have hm : m ≠ 0 := fun h => hnm (by simp [h])
  have hdvd : d ∣ n * m := (Nat.mem_divisors.mp hd).1
  refine ⟨?_, Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right d n, hn⟩,
    Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right d m, hm⟩⟩
  calc d = Nat.gcd d (n * m) := (Nat.gcd_eq_left hdvd).symm
    _ = d.gcd n * d.gcd m := Nat.Coprime.gcd_mul d hcop

lemma ss_comp_eq {n m : ℕ} (hcop : n.Coprime m) {e a : ℕ} (he : e ∣ n) (ha : a ∣ m) :
    (e * a).gcd n = e ∧ (e * a).gcd m = a := by
  constructor
  · have h1 : e ∣ Nat.gcd (e * a) n := Nat.dvd_gcd (dvd_mul_right e a) he
    have hga : Nat.Coprime (Nat.gcd (e * a) n) a :=
      Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_right _ _)
        (Nat.Coprime.coprime_dvd_right ha hcop)
    exact Nat.dvd_antisymm
      (Nat.Coprime.dvd_of_dvd_mul_right hga (Nat.gcd_dvd_left _ _)) h1
  · have h1 : a ∣ Nat.gcd (e * a) m := Nat.dvd_gcd (dvd_mul_left a e) ha
    have hge : Nat.Coprime (Nat.gcd (e * a) m) e :=
      Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_right _ _)
        (Nat.Coprime.coprime_dvd_right he hcop.symm)
    exact Nat.dvd_antisymm
      (Nat.Coprime.dvd_of_dvd_mul_left hge (Nat.gcd_dvd_left _ _)) h1

lemma ss_mul_mem {n m e a : ℕ} (he : e ∈ n.divisors) (ha : a ∈ m.divisors) :
    e * a ∈ (n * m).divisors :=
  Nat.mem_divisors.mpr
    ⟨mul_dvd_mul (Nat.mem_divisors.mp he).1 (Nat.mem_divisors.mp ha).1,
     mul_ne_zero (Nat.mem_divisors.mp he).2 (Nat.mem_divisors.mp ha).2⟩

/-- `invGap` scales when both endpoints are multiplied by the same factor. -/
lemma ss_invGap_mul (a u v : ℕ) : invGap (u * a) (v * a) = ((a:ℝ))⁻¹ * invGap u v := by
  unfold invGap
  push_cast
  rw [show (v:ℝ) * a - u * a = (a:ℝ) * ((v:ℝ) - u) by ring, mul_inv]

/-- `pairSumOn` as a sum over an explicitly filtered pair set (any decidability
instance). -/
lemma ss_pairSumOn_eq (A : Finset ℕ) (C : ℕ → ℕ → Prop)
    [DecidablePred fun q : ℕ × ℕ => q.1 < q.2 ∧ C q.1 q.2] :
    pairSumOn A C
      = ∑ q ∈ (A ×ˢ A).filter (fun q : ℕ × ℕ => q.1 < q.2 ∧ C q.1 q.2),
          invGap q.1 q.2 := by
  have memf : ∀ {q : ℕ × ℕ → Prop} {inst : DecidablePred q} {s : Finset (ℕ × ℕ)}
      {x : ℕ × ℕ}, x ∈ @Finset.filter _ q inst s ↔ x ∈ s ∧ q x := by
    intro q inst s x
    let := inst
    exact Finset.mem_filter
  unfold pairSumOn
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext q
  rw [memf, memf]

/-! ### An elementary exponential inequality -/

lemma ss_half_le_one_sub_exp {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    x/2 ≤ 1 - Real.exp (-x) := by
  have h2 : x + 1 ≤ Real.exp x := Real.add_one_le_exp x
  have h3 : Real.exp (-x) ≤ (1+x)⁻¹ := by
    rw [Real.exp_neg]
    exact inv_anti₀ (by linarith) (by linarith)
  have h4 : (1+x)⁻¹ ≤ 1 - x/2 := by
    rw [inv_le_iff_one_le_mul₀ (by linarith : (0:ℝ) < 1 + x)]
    nlinarith
  linarith

/-! ### The minimal log-gap of the divisors of `n` -/

theorem exists_min_log_gap (n : ℕ) (hn : n ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      ∀ d ∈ n.divisors, ∀ e ∈ n.divisors, d < e → δ ≤ Real.log e - Real.log d := by
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
  have hnR : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn1
  refine ⟨1/(2*(n:ℝ)), by positivity, ?_, ?_⟩
  · rw [div_le_one (by positivity)]
    linarith
  · intro d hd e he hlt
    have hd1 : 1 ≤ d := Nat.pos_of_mem_divisors hd
    have hdn : d ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Nat.mem_divisors.mp hd).1
    have hdR : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd1
    have h1 : Real.log ((d:ℝ)+1) ≤ Real.log e := by
      apply Real.log_le_log (by linarith)
      have : d + 1 ≤ e := hlt
      exact_mod_cast this
    have h2 : Real.log ((d:ℝ)/((d:ℝ)+1)) ≤ (d:ℝ)/((d:ℝ)+1) - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    have h3 : Real.log ((d:ℝ)/((d:ℝ)+1)) = Real.log d - Real.log ((d:ℝ)+1) :=
      Real.log_div (by positivity) (by positivity)
    have h4 : (d:ℝ)/((d:ℝ)+1) - 1 = -(1/((d:ℝ)+1)) := by
      field_simp
      ring
    have h5 : 1/((d:ℝ)+1) ≤ Real.log ((d:ℝ)+1) - Real.log d := by
      rw [h3, h4] at h2
      linarith
    have hdn' : (d:ℝ) + 1 ≤ 2*(n:ℝ) := by
      have hdR' : (d:ℝ) ≤ (n:ℝ) := by exact_mod_cast hdn
      linarith
    have h6 : 1/(2*(n:ℝ)) ≤ 1/((d:ℝ)+1) :=
      one_div_le_one_div_of_le (by positivity) hdn'
    calc 1/(2*(n:ℝ)) ≤ 1/((d:ℝ)+1) := h6
      _ ≤ Real.log ((d:ℝ)+1) - Real.log d := h5
      _ ≤ Real.log e - Real.log d := by linarith

/-! ### Multiplicativity of the sum of reciprocals of divisors -/

theorem sum_inv_divisors_mul {a b : ℕ} (h : a.Coprime b) :
    ∑ d ∈ (a*b).divisors, ((d:ℝ))⁻¹ =
      (∑ d ∈ a.divisors, ((d:ℝ))⁻¹) * (∑ d ∈ b.divisors, ((d:ℝ))⁻¹) := by
  calc ∑ d ∈ (a*b).divisors, ((d:ℝ))⁻¹
      = ∑ q ∈ a.divisors ×ˢ b.divisors, ((q.1:ℝ))⁻¹ * ((q.2:ℝ))⁻¹ := by
        refine Finset.sum_nbij' (i := fun d => (d.gcd a, d.gcd b))
          (j := fun q : ℕ × ℕ => q.1 * q.2) ?_ ?_ ?_ ?_ ?_
        · intro d hd
          obtain ⟨-, h1, h2⟩ := ss_decomp h hd
          exact Finset.mem_product.mpr ⟨h1, h2⟩
        · intro q hq
          have hq' := Finset.mem_product.mp hq
          exact ss_mul_mem hq'.1 hq'.2
        · intro d hd
          exact (ss_decomp h hd).1.symm
        · intro q hq
          have hq' := Finset.mem_product.mp hq
          have := ss_comp_eq h (Nat.mem_divisors.mp hq'.1).1 (Nat.mem_divisors.mp hq'.2).1
          exact Prod.ext this.1 this.2
        · intro d hd
          conv_lhs => rw [(ss_decomp h hd).1]
          push_cast
          rw [mul_inv]
    _ = ∑ i ∈ a.divisors, ∑ j ∈ b.divisors, ((i:ℝ))⁻¹ * ((j:ℝ))⁻¹ :=
        Finset.sum_product _ _ _
    _ = (∑ d ∈ a.divisors, ((d:ℝ))⁻¹) * (∑ d ∈ b.divisors, ((d:ℝ))⁻¹) := by
        rw [Finset.sum_mul_sum]

/-! ### Consecutive pairs with equal `m`-component project to consecutive pairs -/

/-- If a consecutive pair of `(n*m).divisors` has equal `m`-components, then the
`n`-components form a consecutive pair of `n.divisors`. -/
lemma ss_consec_proj {n m : ℕ} (hcop : n.Coprime m)
    {d₁ d₂ : ℕ} (hcons : IsConsecutive ((n * m).divisors) d₁ d₂)
    (haeq : d₁.gcd m = d₂.gcd m) :
    IsConsecutive n.divisors (d₁.gcd n) (d₂.gcd n) := by
  obtain ⟨hd₁, hd₂, hlt, hbet⟩ := hcons
  obtain ⟨heq₁, he₁, ha₁⟩ := ss_decomp hcop hd₁
  obtain ⟨heq₂, he₂, ha₂⟩ := ss_decomp hcop hd₂
  have hapos : 0 < d₁.gcd m := Nat.pos_of_mem_divisors ha₁
  have hlt' : d₁.gcd n < d₂.gcd n := by
    have h1 : d₁.gcd n * d₁.gcd m < d₂.gcd n * d₁.gcd m := by
      conv_rhs => rw [haeq]
      rw [← heq₁, ← heq₂]
      exact hlt
    exact Nat.lt_of_mul_lt_mul_right h1
  refine ⟨he₁, he₂, hlt', ?_⟩
  intro c hc hcc
  refine hbet (c * d₁.gcd m) (ss_mul_mem hc ha₁) ⟨?_, ?_⟩
  · calc d₁ = d₁.gcd n * d₁.gcd m := heq₁
      _ < c * d₁.gcd m := Nat.mul_lt_mul_of_pos_right hcc.1 hapos
  · calc c * d₁.gcd m < d₂.gcd n * d₁.gcd m := Nat.mul_lt_mul_of_pos_right hcc.2 hapos
      _ = d₂.gcd n * d₂.gcd m := by rw [haeq]
      _ = d₂ := heq₂.symm

/-! ### Class C1: equal `m`-component -/

/-- Consecutive pairs of `(n*m).divisors` with equal `m`-component are controlled by
`gapSum n.divisors` times the sum of inverse divisors of `m`. -/
lemma ss_C1_le {n m : ℕ} (hcop : n.Coprime m) :
    pairSumOn ((n * m).divisors)
        (fun d₁ d₂ => d₁.gcd m = d₂.gcd m ∧ IsConsecutive ((n * m).divisors) d₁ d₂)
      ≤ (∑ a ∈ m.divisors, ((a:ℝ))⁻¹) * gapSum n.divisors := by
  classical
  refine os_pairSumOn_le_of_forall fun S hS => ?_
  set CP := (n.divisors ×ˢ n.divisors).filter
      (fun q : ℕ × ℕ => q.1 < q.2 ∧ IsConsecutive n.divisors q.1 q.2) with hCP
  have hgap : gapSum n.divisors = ∑ q ∈ CP, invGap q.1 q.2 := by
    unfold gapSum
    exact ss_pairSumOn_eq n.divisors (IsConsecutive n.divisors)
  set φ : ℕ × ℕ → ℕ × (ℕ × ℕ) := fun p => (p.1.gcd m, (p.1.gcd n, p.2.gcd n)) with hφ
  have hterm : ∀ p ∈ S, invGap p.1 p.2
      = ((p.1.gcd m : ℝ))⁻¹ * invGap (p.1.gcd n) (p.2.gcd n) := by
    intro p hp
    obtain ⟨hd₁, hd₂, hlt, haeq, hcons⟩ := hS p hp
    obtain ⟨heq₁, -, -⟩ := ss_decomp hcop hd₁
    obtain ⟨heq₂, -, -⟩ := ss_decomp hcop hd₂
    conv_lhs => rw [heq₁, heq₂, ← haeq]
    exact ss_invGap_mul _ _ _
  have hinj : ∀ p ∈ S, ∀ p' ∈ S, φ p = φ p' → p = p' := by
    intro p hp p' hp' he
    obtain ⟨hd₁, hd₂, -, haeq, -⟩ := hS p hp
    obtain ⟨hd₁', hd₂', -, haeq', -⟩ := hS p' hp'
    have h1 : p.1.gcd m = p'.1.gcd m := congrArg Prod.fst he
    have h2 : p.1.gcd n = p'.1.gcd n := congrArg (fun x => x.2.1) he
    have h3 : p.2.gcd n = p'.2.gcd n := congrArg (fun x => x.2.2) he
    have e1 : p.1 = p'.1 := by
      rw [(ss_decomp hcop hd₁).1, (ss_decomp hcop hd₁').1, h1, h2]
    have e2 : p.2 = p'.2 := by
      rw [(ss_decomp hcop hd₂).1, (ss_decomp hcop hd₂').1, ← haeq, ← haeq', h1, h3]
    exact Prod.ext e1 e2
  have himg : ∀ p ∈ S, φ p ∈ m.divisors ×ˢ CP := by
    intro p hp
    obtain ⟨hd₁, hd₂, hlt, haeq, hcons⟩ := hS p hp
    have hproj := ss_consec_proj hcop hcons haeq
    refine Finset.mem_product.mpr ⟨(ss_decomp hcop hd₁).2.2, ?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hproj.1, hproj.2.1⟩,
      hproj.2.2.1, hproj⟩
  have hnn : ∀ y ∈ m.divisors ×ˢ CP, 0 ≤ ((y.1:ℝ))⁻¹ * invGap y.2.1 y.2.2 := by
    intro y hy
    have hy' := Finset.mem_product.mp hy
    have hq := Finset.mem_filter.mp hy'.2
    exact mul_nonneg (by positivity) (invGap_pos hq.2.1).le
  calc ∑ p ∈ S, invGap p.1 p.2
      = ∑ p ∈ S, ((p.1.gcd m : ℝ))⁻¹ * invGap (p.1.gcd n) (p.2.gcd n) :=
        Finset.sum_congr rfl hterm
    _ = ∑ y ∈ S.image φ, ((y.1:ℝ))⁻¹ * invGap y.2.1 y.2.2 :=
        (Finset.sum_image
          (f := fun y : ℕ × (ℕ × ℕ) => ((y.1:ℝ))⁻¹ * invGap y.2.1 y.2.2) hinj).symm
    _ ≤ ∑ y ∈ m.divisors ×ˢ CP, ((y.1:ℝ))⁻¹ * invGap y.2.1 y.2.2 := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun y hy _ => hnn y hy
        intro y hy
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hy
        exact himg p hp
    _ = (∑ a ∈ m.divisors, ((a:ℝ))⁻¹) * ∑ q ∈ CP, invGap q.1 q.2 := by
        rw [Finset.sum_mul_sum]
        exact Finset.sum_product _ _ _
    _ = (∑ a ∈ m.divisors, ((a:ℝ))⁻¹) * gapSum n.divisors := by rw [hgap]

/-! ### Nontrivial divisors of the prime product exceed the window base -/

lemma ss_x0_lt_of_ne_one {B : Finset ℕ} {x₀ : ℕ} (hprime : ∀ p ∈ B, p.Prime)
    (hwin : ∀ p ∈ B, x₀ < p) {a : ℕ}
    (ha : a ∈ (∏ p ∈ B, p).divisors) (ha1 : a ≠ 1) : x₀ < a := by
  have hpf : a.primeFactors ⊆ B := os_primeFactors_subset hprime ha
  have hane : a.primeFactors.Nonempty := by
    rw [Nat.nonempty_primeFactors]
    have := Nat.pos_of_mem_divisors ha
    omega
  obtain ⟨p, hp⟩ := hane
  have hpa : p ∣ a := Nat.dvd_of_mem_primeFactors hp
  have hple : p ≤ a := Nat.le_of_dvd (Nat.pos_of_mem_divisors ha) hpa
  have := hwin p (hpf hp)
  omega

/-! ### The log-ratio of two same-`ω` divisors of the prime product is small -/

lemma ss_log_ratio_le {B : Finset ℕ} {x₀ H K : ℕ} (hprime : ∀ p ∈ B, p.Prime)
    (hcard : B.card = K) (hwin : ∀ p ∈ B, x₀ < p ∧ p ≤ x₀ + H) (hx₀ : 0 < x₀)
    {u v : ℕ} (hu : u ∈ (∏ p ∈ B, p).divisors) (hv : v ∈ (∏ p ∈ B, p).divisors)
    (hk : u.primeFactors.card = v.primeFactors.card) :
    Real.log v - Real.log u ≤ (K:ℝ) * H / x₀ := by
  have hx0R : (0:ℝ) < (x₀:ℝ) := by exact_mod_cast hx₀
  have hkK : u.primeFactors.card ≤ K := by
    rw [← hcard]
    exact Finset.card_le_card (os_primeFactors_subset hprime hu)
  have hu_low : (x₀:ℝ)^u.primeFactors.card ≤ (u:ℝ) := os_le_prod hprime hwin hu
  have hv_up : (v:ℝ) ≤ ((x₀:ℝ) + H)^u.primeFactors.card := by
    have h := os_prod_le hprime hwin hv
    rwa [← hk] at h
  have hupos : (0:ℝ) < (u:ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors hu
  have hvpos : (0:ℝ) < (v:ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors hv
  have h1 : Real.log v ≤ (u.primeFactors.card : ℝ) * Real.log ((x₀:ℝ) + H) := by
    calc Real.log v ≤ Real.log (((x₀:ℝ) + H)^u.primeFactors.card) :=
          Real.log_le_log hvpos hv_up
      _ = (u.primeFactors.card : ℝ) * Real.log ((x₀:ℝ) + H) := Real.log_pow _ _
  have h2 : (u.primeFactors.card : ℝ) * Real.log x₀ ≤ Real.log u := by
    calc (u.primeFactors.card : ℝ) * Real.log x₀
        = Real.log ((x₀:ℝ)^u.primeFactors.card) := (Real.log_pow _ _).symm
      _ ≤ Real.log u := Real.log_le_log (by positivity) hu_low
  have h3 : Real.log ((x₀:ℝ) + H) - Real.log x₀ ≤ (H:ℝ)/x₀ := by
    have hd : Real.log (((x₀:ℝ) + H)/x₀) ≤ ((x₀:ℝ) + H)/x₀ - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    have he : Real.log (((x₀:ℝ) + H)/x₀) = Real.log ((x₀:ℝ) + H) - Real.log x₀ :=
      Real.log_div (by positivity) (by positivity)
    have hf : ((x₀:ℝ) + H)/x₀ - 1 = (H:ℝ)/x₀ := by
      field_simp
      ring
    rw [he, hf] at hd
    exact hd
  have h7 : Real.log v - Real.log u
      ≤ (u.primeFactors.card : ℝ) * (Real.log ((x₀:ℝ) + H) - Real.log x₀) := by
    have hring : (u.primeFactors.card : ℝ) * (Real.log ((x₀:ℝ) + H) - Real.log x₀)
        = (u.primeFactors.card : ℝ) * Real.log ((x₀:ℝ) + H)
          - (u.primeFactors.card : ℝ) * Real.log x₀ := by ring
    linarith [h1, h2, hring]
  have h5 : (u.primeFactors.card : ℝ) * (Real.log ((x₀:ℝ) + H) - Real.log x₀)
      ≤ (u.primeFactors.card : ℝ) * ((H:ℝ)/x₀) :=
    mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg _)
  have h6 : (u.primeFactors.card : ℝ) * ((H:ℝ)/x₀) ≤ (K:ℝ) * ((H:ℝ)/x₀) := by
    have hc : (u.primeFactors.card : ℝ) ≤ (K:ℝ) := by exact_mod_cast hkK
    exact mul_le_mul_of_nonneg_right hc (by positivity)
  calc Real.log v - Real.log u
      ≤ (u.primeFactors.card : ℝ) * (Real.log ((x₀:ℝ) + H) - Real.log x₀) := h7
    _ ≤ (u.primeFactors.card : ℝ) * ((H:ℝ)/x₀) := h5
    _ ≤ (K:ℝ) * ((H:ℝ)/x₀) := h6
    _ = (K:ℝ) * H / x₀ := by ring

/-! ### The C3 gap bound -/

/-- A consecutive-candidate pair whose `n`- and `m`-components both differ has gap
at least `δ/4` times its upper endpoint, and the upper endpoint has a nontrivial
`m`-component. -/
lemma ss_C3_gap {n : ℕ} (hn : n ≠ 0) {B : Finset ℕ} {x₀ H K : ℕ}
    (hprime : ∀ p ∈ B, p.Prime) (hcard : B.card = K)
    (hwin : ∀ p ∈ B, x₀ < p ∧ p ≤ x₀ + H)
    (hKH : 2*K*H ≤ x₀) (hx₀ : 4 ≤ x₀)
    {δ : ℝ} (hδpos : 0 < δ) (hδ1 : δ ≤ 1)
    (hδ : ∀ d ∈ n.divisors, ∀ e ∈ n.divisors, d < e → δ ≤ Real.log e - Real.log d)
    (hlarge₁ : 4*(n:ℝ) ≤ x₀)
    (hlarge₂ : 2*(K:ℝ)*H ≤ δ * x₀)
    {d₁ d₂ : ℕ} (hd₁ : d₁ ∈ (n * ∏ p ∈ B, p).divisors)
    (hd₂ : d₂ ∈ (n * ∏ p ∈ B, p).divisors) (hlt : d₁ < d₂)
    (hne_e : d₁.gcd n ≠ d₂.gcd n)
    (hne_a : d₁.gcd (∏ p ∈ B, p) ≠ d₂.gcd (∏ p ∈ B, p)) :
    δ/4 * (d₂:ℝ) ≤ (d₂:ℝ) - (d₁:ℝ) ∧ d₂.gcd (∏ p ∈ B, p) ≠ 1 := by
  have hx₀pos : 0 < x₀ := by omega
  have hx0R : (0:ℝ) < (x₀:ℝ) := by exact_mod_cast hx₀pos
  have hx1R : (1:ℝ) ≤ (x₀:ℝ) := by exact_mod_cast (by omega : 1 ≤ x₀)
  have hnx : n ≤ x₀ := by
    have h1 : (n:ℝ) ≤ (x₀:ℝ) := by
      have h0 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
      linarith
    exact_mod_cast h1
  have hcop : n.Coprime (∏ p ∈ B, p) :=
    ss_coprime_prod hn hprime (fun p hp => (hwin p hp).1) hnx
  obtain ⟨heq₁, he₁, ha₁⟩ := ss_decomp hcop hd₁
  obtain ⟨heq₂, he₂, ha₂⟩ := ss_decomp hcop hd₂
  have hd₁pos : 0 < d₁ := Nat.pos_of_mem_divisors hd₁
  have hd₂pos : 0 < d₂ := Nat.pos_of_mem_divisors hd₂
  have hd₁R : (0:ℝ) < (d₁:ℝ) := by exact_mod_cast hd₁pos
  have hd₂R : (0:ℝ) < (d₂:ℝ) := by exact_mod_cast hd₂pos
  have he₁R : (0:ℝ) < (d₁.gcd n : ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors he₁
  have he₂R : (0:ℝ) < (d₂.gcd n : ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors he₂
  have ha₁R : (0:ℝ) < (d₁.gcd (∏ p ∈ B, p) : ℝ) := by
    exact_mod_cast Nat.pos_of_mem_divisors ha₁
  have ha₂R : (0:ℝ) < (d₂.gcd (∏ p ∈ B, p) : ℝ) := by
    exact_mod_cast Nat.pos_of_mem_divisors ha₂
  -- the upper endpoint has a nontrivial `m`-component
  have ha₂1 : d₂.gcd (∏ p ∈ B, p) ≠ 1 := by
    intro h1
    have ha₁1 : d₁.gcd (∏ p ∈ B, p) ≠ 1 := fun h => hne_a (h.trans h1.symm)
    have hx₀a₁ : x₀ < d₁.gcd (∏ p ∈ B, p) :=
      ss_x0_lt_of_ne_one hprime (fun p hp => (hwin p hp).1) ha₁ ha₁1
    have hd₂n : d₂ ≤ n := by
      have hd₂e : d₂ = d₂.gcd n := by
        conv_lhs => rw [heq₂]
        rw [h1, mul_one]
      calc d₂ = d₂.gcd n := hd₂e
        _ ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Nat.mem_divisors.mp he₂).1
    have ha₁d : d₁.gcd (∏ p ∈ B, p) ≤ d₁ :=
      Nat.le_of_dvd hd₁pos (Nat.gcd_dvd_left d₁ _)
    omega
  refine ⟨?_, ha₂1⟩
  have hlogd₁ : Real.log (d₁:ℝ)
      = Real.log (d₁.gcd n : ℝ) + Real.log (d₁.gcd (∏ p ∈ B, p) : ℝ) := by
    conv_lhs => rw [heq₁]
    push_cast
    exact Real.log_mul he₁R.ne' ha₁R.ne'
  have hlogd₂ : Real.log (d₂:ℝ)
      = Real.log (d₂.gcd n : ℝ) + Real.log (d₂.gcd (∏ p ∈ B, p) : ℝ) := by
    conv_lhs => rw [heq₂]
    push_cast
    exact Real.log_mul he₂R.ne' ha₂R.ne'
  by_cases hkeq : (d₁.gcd (∏ p ∈ B, p)).primeFactors.card
      = (d₂.gcd (∏ p ∈ B, p)).primeFactors.card
  · -- Case A: same ω — use the log-resolution δ of `n.divisors`
    have hlog_a : Real.log (d₂.gcd (∏ p ∈ B, p) : ℝ)
        - Real.log (d₁.gcd (∏ p ∈ B, p) : ℝ) ≤ (K:ℝ)*H/x₀ :=
      ss_log_ratio_le hprime hcard hwin hx₀pos ha₁ ha₂ hkeq
    have hlog_a' : Real.log (d₁.gcd (∏ p ∈ B, p) : ℝ)
        - Real.log (d₂.gcd (∏ p ∈ B, p) : ℝ) ≤ (K:ℝ)*H/x₀ :=
      ss_log_ratio_le hprime hcard hwin hx₀pos ha₂ ha₁ hkeq.symm
    have hKH2 : (K:ℝ)*H/x₀ ≤ δ/2 := by
      rw [div_le_div_iff₀ hx0R (by norm_num : (0:ℝ) < 2)]
      linarith
    have hlog_lt : Real.log (d₁:ℝ) < Real.log (d₂:ℝ) :=
      Real.log_lt_log hd₁R (by exact_mod_cast hlt)
    have hgap : δ/2 ≤ Real.log (d₂:ℝ) - Real.log (d₁:ℝ) := by
      rcases lt_or_gt_of_ne hne_e with h | h
      · have hδe := hδ _ he₁ _ he₂ h
        rw [hlogd₁, hlogd₂]
        linarith
      · exfalso
        have hδe := hδ _ he₂ _ he₁ h
        rw [hlogd₁, hlogd₂] at hlog_lt
        linarith
    have hd₁d₂ : (d₁:ℝ) ≤ (d₂:ℝ) * Real.exp (-(δ/2)) := by
      have h1 : Real.log (d₁:ℝ) ≤ Real.log (d₂:ℝ) - δ/2 := by linarith
      calc (d₁:ℝ) = Real.exp (Real.log (d₁:ℝ)) := (Real.exp_log hd₁R).symm
        _ ≤ Real.exp (Real.log (d₂:ℝ) - δ/2) := Real.exp_le_exp.mpr h1
        _ = Real.exp (Real.log (d₂:ℝ)) * Real.exp (-(δ/2)) := by
            rw [← Real.exp_add]
            ring_nf
        _ = (d₂:ℝ) * Real.exp (-(δ/2)) := by rw [Real.exp_log hd₂R]
    have hexp : δ/2/2 ≤ 1 - Real.exp (-(δ/2)) :=
      ss_half_le_one_sub_exp (by linarith) (by linarith)
    have key : (0:ℝ) ≤ (d₂:ℝ) * (1 - Real.exp (-(δ/2)) - δ/4) :=
      mul_nonneg hd₂R.le (by linarith)
    nlinarith [key, hd₁d₂]
  · -- Case B: different ω — the ratio is at least 2
    have hk₁K : (d₁.gcd (∏ p ∈ B, p)).primeFactors.card ≤ K := by
      rw [← hcard]
      exact Finset.card_le_card (os_primeFactors_subset hprime ha₁)
    have hk₂K : (d₂.gcd (∏ p ∈ B, p)).primeFactors.card ≤ K := by
      rw [← hcard]
      exact Finset.card_le_card (os_primeFactors_subset hprime ha₂)
    have he₁n : (d₁.gcd n : ℝ) ≤ (n:ℝ) := by
      exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Nat.mem_divisors.mp he₁).1
    have he₂n : (d₂.gcd n : ℝ) ≤ (n:ℝ) := by
      exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Nat.mem_divisors.mp he₂).1
    have hd₁cast : (d₁:ℝ) = (d₁.gcd n : ℝ) * (d₁.gcd (∏ p ∈ B, p) : ℝ) := by
      conv_lhs => rw [heq₁]
      push_cast
      ring
    have hd₂cast : (d₂:ℝ) = (d₂.gcd n : ℝ) * (d₂.gcd (∏ p ∈ B, p) : ℝ) := by
      conv_lhs => rw [heq₂]
      push_cast
      ring
    have h2d : 2*(d₁:ℝ) ≤ (d₂:ℝ) := by
      rcases Nat.lt_or_ge (d₁.gcd (∏ p ∈ B, p)).primeFactors.card
          (d₂.gcd (∏ p ∈ B, p)).primeFactors.card with hklt | hkge
      · -- ω(a₁) < ω(a₂)
        have ha₁up : (d₁.gcd (∏ p ∈ B, p) : ℝ)
            ≤ 2*(x₀:ℝ)^(d₁.gcd (∏ p ∈ B, p)).primeFactors.card :=
          le_trans (os_prod_le hprime hwin ha₁) (os_window_pow_le hx₀pos hKH hk₁K)
        have ha₂low : (x₀:ℝ)^((d₁.gcd (∏ p ∈ B, p)).primeFactors.card + 1)
            ≤ (d₂.gcd (∏ p ∈ B, p) : ℝ) := by
          refine le_trans ?_ (os_le_prod hprime hwin ha₂)
          exact pow_le_pow_right₀ (by linarith) hklt
        have ha₂d : (d₂.gcd (∏ p ∈ B, p) : ℝ) ≤ (d₂:ℝ) := by
          exact_mod_cast Nat.le_of_dvd hd₂pos (Nat.gcd_dvd_left d₂ _)
        have hpk : (0:ℝ) ≤ (x₀:ℝ)^(d₁.gcd (∏ p ∈ B, p)).primeFactors.card := by
          positivity
        calc 2*(d₁:ℝ)
            = 2*((d₁.gcd n : ℝ) * (d₁.gcd (∏ p ∈ B, p) : ℝ)) := by rw [hd₁cast]
          _ ≤ 2*((n:ℝ) * (2*(x₀:ℝ)^(d₁.gcd (∏ p ∈ B, p)).primeFactors.card)) := by
              gcongr
          _ = 4*(n:ℝ) * (x₀:ℝ)^(d₁.gcd (∏ p ∈ B, p)).primeFactors.card := by ring
          _ ≤ (x₀:ℝ) * (x₀:ℝ)^(d₁.gcd (∏ p ∈ B, p)).primeFactors.card :=
              mul_le_mul_of_nonneg_right hlarge₁ hpk
          _ = (x₀:ℝ)^((d₁.gcd (∏ p ∈ B, p)).primeFactors.card + 1) := by
              rw [pow_succ]
              ring
          _ ≤ (d₂.gcd (∏ p ∈ B, p) : ℝ) := ha₂low
          _ ≤ (d₂:ℝ) := ha₂d
      · -- ω(a₂) < ω(a₁): impossible since d₁ < d₂
        exfalso
        have hklt : (d₂.gcd (∏ p ∈ B, p)).primeFactors.card
            < (d₁.gcd (∏ p ∈ B, p)).primeFactors.card :=
          lt_of_le_of_ne hkge (fun h => hkeq h.symm)
        have ha₂up : (d₂.gcd (∏ p ∈ B, p) : ℝ)
            ≤ 2*(x₀:ℝ)^(d₂.gcd (∏ p ∈ B, p)).primeFactors.card :=
          le_trans (os_prod_le hprime hwin ha₂) (os_window_pow_le hx₀pos hKH hk₂K)
        have ha₁low : (x₀:ℝ)^((d₂.gcd (∏ p ∈ B, p)).primeFactors.card + 1)
            ≤ (d₁.gcd (∏ p ∈ B, p) : ℝ) := by
          refine le_trans ?_ (os_le_prod hprime hwin ha₁)
          exact pow_le_pow_right₀ (by linarith) hklt
        have ha₁d : (d₁.gcd (∏ p ∈ B, p) : ℝ) ≤ (d₁:ℝ) := by
          exact_mod_cast Nat.le_of_dvd hd₁pos (Nat.gcd_dvd_left d₁ _)
        have hpk : (0:ℝ) < (x₀:ℝ)^(d₂.gcd (∏ p ∈ B, p)).primeFactors.card := by
          positivity
        have hn1 : (1:ℝ) ≤ (n:ℝ) := by
          exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
        have hcontra : (d₂:ℝ) < (d₂:ℝ) := by
          calc (d₂:ℝ) = (d₂.gcd n : ℝ) * (d₂.gcd (∏ p ∈ B, p) : ℝ) := hd₂cast
            _ ≤ (n:ℝ) * (2*(x₀:ℝ)^(d₂.gcd (∏ p ∈ B, p)).primeFactors.card) := by
                gcongr
            _ = 2*(n:ℝ) * (x₀:ℝ)^(d₂.gcd (∏ p ∈ B, p)).primeFactors.card := by ring
            _ < 4*(n:ℝ) * (x₀:ℝ)^(d₂.gcd (∏ p ∈ B, p)).primeFactors.card := by
                have : (0:ℝ) < (n:ℝ) * (x₀:ℝ)^(d₂.gcd (∏ p ∈ B, p)).primeFactors.card := by
                  positivity
                nlinarith
            _ ≤ (x₀:ℝ) * (x₀:ℝ)^(d₂.gcd (∏ p ∈ B, p)).primeFactors.card :=
                mul_le_mul_of_nonneg_right hlarge₁ hpk.le
            _ = (x₀:ℝ)^((d₂.gcd (∏ p ∈ B, p)).primeFactors.card + 1) := by
                rw [pow_succ]
                ring
            _ ≤ (d₁.gcd (∏ p ∈ B, p) : ℝ) := ha₁low
            _ ≤ (d₁:ℝ) := ha₁d
            _ < (d₂:ℝ) := by exact_mod_cast hlt
        exact lt_irrefl _ hcontra
    have key : (0:ℝ) ≤ (d₂:ℝ) * (1/2 - δ/4) := mul_nonneg hd₂R.le (by linarith)
    nlinarith [key, h2d]

/-! ### Sum of inverse divisors with nontrivial `m`-component -/

lemma ss_sum_inv_comp_le {n m : ℕ} (hcop : n.Coprime m) :
    ∑ d ∈ (n*m).divisors.filter (fun d => d.gcd m ≠ 1), ((d:ℝ))⁻¹
      ≤ (∑ e ∈ n.divisors, ((e:ℝ))⁻¹) * (∑ a ∈ m.divisors.erase 1, ((a:ℝ))⁻¹) := by
  classical
  have hmem : ∀ d ∈ (n*m).divisors.filter (fun d => d.gcd m ≠ 1),
      d ∈ (n*m).divisors ∧ d.gcd m ≠ 1 := fun d hd => Finset.mem_filter.mp hd
  have hterm : ∀ d ∈ (n*m).divisors.filter (fun d => d.gcd m ≠ 1),
      ((d:ℝ))⁻¹ = ((d.gcd n : ℝ))⁻¹ * ((d.gcd m : ℝ))⁻¹ := by
    intro d hd
    conv_lhs => rw [(ss_decomp hcop (hmem d hd).1).1]
    push_cast
    rw [mul_inv]
  have hinj : ∀ d ∈ (n*m).divisors.filter (fun d => d.gcd m ≠ 1),
      ∀ d' ∈ (n*m).divisors.filter (fun d => d.gcd m ≠ 1),
      (fun d : ℕ => (d.gcd n, d.gcd m)) d = (fun d : ℕ => (d.gcd n, d.gcd m)) d'
        → d = d' := by
    intro d hd d' hd' he
    have h1 : d.gcd n = d'.gcd n := congrArg Prod.fst he
    have h2 : d.gcd m = d'.gcd m := congrArg Prod.snd he
    rw [(ss_decomp hcop (hmem d hd).1).1, (ss_decomp hcop (hmem d' hd').1).1, h1, h2]
  have himg : ∀ d ∈ (n*m).divisors.filter (fun d => d.gcd m ≠ 1),
      (d.gcd n, d.gcd m) ∈ n.divisors ×ˢ (m.divisors.erase 1) := by
    intro d hd
    obtain ⟨hdm, hne⟩ := hmem d hd
    obtain ⟨-, h1, h2⟩ := ss_decomp hcop hdm
    exact Finset.mem_product.mpr ⟨h1, Finset.mem_erase.mpr ⟨hne, h2⟩⟩
  calc ∑ d ∈ (n*m).divisors.filter (fun d => d.gcd m ≠ 1), ((d:ℝ))⁻¹
      = ∑ d ∈ (n*m).divisors.filter (fun d => d.gcd m ≠ 1),
          ((d.gcd n : ℝ))⁻¹ * ((d.gcd m : ℝ))⁻¹ := Finset.sum_congr rfl hterm
    _ = ∑ y ∈ ((n*m).divisors.filter (fun d => d.gcd m ≠ 1)).image
          (fun d : ℕ => (d.gcd n, d.gcd m)), ((y.1:ℝ))⁻¹ * ((y.2:ℝ))⁻¹ :=
        (Finset.sum_image
          (f := fun y : ℕ × ℕ => ((y.1:ℝ))⁻¹ * ((y.2:ℝ))⁻¹) hinj).symm
    _ ≤ ∑ y ∈ n.divisors ×ˢ (m.divisors.erase 1), ((y.1:ℝ))⁻¹ * ((y.2:ℝ))⁻¹ := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun y _ _ => by positivity
        intro y hy
        obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hy
        exact himg d hd
    _ = (∑ e ∈ n.divisors, ((e:ℝ))⁻¹) * (∑ a ∈ m.divisors.erase 1, ((a:ℝ))⁻¹) := by
        rw [Finset.sum_mul_sum]
        exact Finset.sum_product _ _ _

/-! ### Class C3: both components differ -/

lemma ss_C3_le {n : ℕ} (hn : n ≠ 0) {B : Finset ℕ} {x₀ H K : ℕ}
    (hprime : ∀ p ∈ B, p.Prime) (hcard : B.card = K)
    (hwin : ∀ p ∈ B, x₀ < p ∧ p ≤ x₀ + H)
    (hKH : 2*K*H ≤ x₀) (hx₀ : 4 ≤ x₀) (hH : 1 ≤ H)
    {δ : ℝ} (hδpos : 0 < δ) (hδ1 : δ ≤ 1)
    (hδ : ∀ d ∈ n.divisors, ∀ e ∈ n.divisors, d < e → δ ≤ Real.log e - Real.log d)
    (hσ : ∑ e ∈ n.divisors, ((e:ℝ))⁻¹ ≤ 2)
    (hlarge₁ : 4*(n:ℝ) ≤ x₀)
    (hlarge₂ : 2*(K:ℝ)*H ≤ δ * x₀) :
    pairSumOn ((n * ∏ p ∈ B, p).divisors)
        (fun d₁ d₂ => d₁.gcd n ≠ d₂.gcd n ∧
          d₁.gcd (∏ p ∈ B, p) ≠ d₂.gcd (∏ p ∈ B, p) ∧
          IsConsecutive ((n * ∏ p ∈ B, p).divisors) d₁ d₂)
      ≤ 16*K/(δ*(x₀:ℝ)) := by
  classical
  have hx₀pos : 0 < x₀ := by omega
  have hx0R : (0:ℝ) < (x₀:ℝ) := by exact_mod_cast hx₀pos
  have hnx : n ≤ x₀ := by
    have h1 : (n:ℝ) ≤ (x₀:ℝ) := by
      have h0 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
      linarith
    exact_mod_cast h1
  have hcop : n.Coprime (∏ p ∈ B, p) :=
    ss_coprime_prod hn hprime (fun p hp => (hwin p hp).1) hnx
  have hgnn : ∀ d : ℕ,
      (0:ℝ) ≤ (if d.gcd (∏ p ∈ B, p) ≠ 1 then 4/(δ*(d:ℝ)) else 0) := by
    intro d
    split
    · positivity
    · exact le_rfl
  -- Step 1: the pair sum is at most the weighted divisor sum
  have hmain : pairSumOn ((n * ∏ p ∈ B, p).divisors)
      (fun d₁ d₂ => d₁.gcd n ≠ d₂.gcd n ∧
        d₁.gcd (∏ p ∈ B, p) ≠ d₂.gcd (∏ p ∈ B, p) ∧
        IsConsecutive ((n * ∏ p ∈ B, p).divisors) d₁ d₂)
      ≤ ∑ d ∈ (n * ∏ p ∈ B, p).divisors,
          (if d.gcd (∏ p ∈ B, p) ≠ 1 then 4/(δ*(d:ℝ)) else 0) := by
    refine os_pairSumOn_le_of_forall fun S hS => ?_
    have hterm : ∀ p ∈ S, invGap p.1 p.2
        ≤ (if p.2.gcd (∏ p ∈ B, p) ≠ 1 then 4/(δ*(p.2:ℝ)) else 0) := by
      intro p hp
      obtain ⟨hd₁, hd₂, hlt, hnee, hnea, hcons⟩ := hS p hp
      obtain ⟨hgap, hne1⟩ := ss_C3_gap hn hprime hcard hwin hKH hx₀ hδpos hδ1 hδ
        hlarge₁ hlarge₂ hd₁ hd₂ hlt hnee hnea
      have hd₂R : (0:ℝ) < (p.2:ℝ) := by
        exact_mod_cast Nat.pos_of_mem_divisors hd₂
      have hpos : (0:ℝ) < δ/4 * (p.2:ℝ) := by positivity
      have h1 : invGap p.1 p.2 ≤ (δ/4 * (p.2:ℝ))⁻¹ := by
        unfold invGap
        exact inv_anti₀ hpos hgap
      have h2 : (δ/4 * (p.2:ℝ))⁻¹ = 4/(δ*(p.2:ℝ)) := by
        rw [show δ/4 * (p.2:ℝ) = δ*(p.2:ℝ)/4 by ring, inv_div]
      rw [if_pos hne1]
      rw [← h2]
      exact h1
    have hinj : ∀ p ∈ S, ∀ p' ∈ S,
        (fun q : ℕ × ℕ => q.2) p = (fun q : ℕ × ℕ => q.2) p' → p = p' := by
      intro p hp p' hp' he
      obtain ⟨-, -, -, -, -, hcons⟩ := hS p hp
      obtain ⟨-, -, -, -, -, hcons'⟩ := hS p' hp'
      have he' : p.2 = p'.2 := he
      have h1 : p.1 = p'.1 := os_consec_pred_unique hcons (he' ▸ hcons')
      exact Prod.ext h1 he'
    calc ∑ p ∈ S, invGap p.1 p.2
        ≤ ∑ p ∈ S, (if p.2.gcd (∏ p ∈ B, p) ≠ 1 then 4/(δ*(p.2:ℝ)) else 0) :=
          Finset.sum_le_sum hterm
      _ = ∑ d ∈ S.image (fun q : ℕ × ℕ => q.2),
            (if d.gcd (∏ p ∈ B, p) ≠ 1 then 4/(δ*(d:ℝ)) else 0) :=
          (Finset.sum_image
            (f := fun d : ℕ => if d.gcd (∏ p ∈ B, p) ≠ 1
              then 4/(δ*(d:ℝ)) else 0) hinj).symm
      _ ≤ ∑ d ∈ (n * ∏ p ∈ B, p).divisors,
            (if d.gcd (∏ p ∈ B, p) ≠ 1 then 4/(δ*(d:ℝ)) else 0) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun d _ _ => hgnn d
          intro d hd
          obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hd
          exact (hS p hp).2.1
  -- Step 2: the weighted divisor sum
  have hsuma : ∑ a ∈ (∏ p ∈ B, p).divisors.erase 1, ((a:ℝ))⁻¹ ≤ 2*(K:ℝ)/x₀ := by
    have h := sum_inv_divisors_erase_one_le hprime (fun p hp => (hwin p hp).1.le)
      (by rw [hcard]; nlinarith : 2 * B.card ≤ x₀) hx₀pos
    rw [hcard] at h
    exact h
  have hsumnn : (0:ℝ) ≤ ∑ a ∈ (∏ p ∈ B, p).divisors.erase 1, ((a:ℝ))⁻¹ :=
    Finset.sum_nonneg fun a _ => by positivity
  have hstep2 : ∑ d ∈ (n * ∏ p ∈ B, p).divisors,
      (if d.gcd (∏ p ∈ B, p) ≠ 1 then 4/(δ*(d:ℝ)) else 0)
      ≤ 16*K/(δ*(x₀:ℝ)) := by
    calc ∑ d ∈ (n * ∏ p ∈ B, p).divisors,
          (if d.gcd (∏ p ∈ B, p) ≠ 1 then 4/(δ*(d:ℝ)) else 0)
        = ∑ d ∈ (n * ∏ p ∈ B, p).divisors.filter
            (fun d => d.gcd (∏ p ∈ B, p) ≠ 1), 4/(δ*(d:ℝ)) :=
          (Finset.sum_filter _ _).symm
      _ = (4/δ) * ∑ d ∈ (n * ∏ p ∈ B, p).divisors.filter
            (fun d => d.gcd (∏ p ∈ B, p) ≠ 1), ((d:ℝ))⁻¹ := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun d _ => ?_
          rw [div_eq_mul_inv, mul_inv, div_eq_mul_inv]
          ring
      _ ≤ (4/δ) * ((∑ e ∈ n.divisors, ((e:ℝ))⁻¹)
            * (∑ a ∈ (∏ p ∈ B, p).divisors.erase 1, ((a:ℝ))⁻¹)) := by
          refine mul_le_mul_of_nonneg_left (ss_sum_inv_comp_le hcop) (by positivity)
      _ ≤ (4/δ) * (2 * (2*(K:ℝ)/x₀)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul hσ hsuma hsumnn (by norm_num)
      _ = 16*K/(δ*(x₀:ℝ)) := by
          field_simp
          ring
  exact le_trans hmain hstep2

/-! ### The scale step -/

/-- **The incremental multiscale step.**  For `n ≠ 0` with inverse-divisor sum at most
`2` and minimal divisor log-gap `δ`, and a fresh window `B` of `K` primes in
`(x₀, x₀+H]` with pairwise gaps `> N` (with `x₀` large as in `hlarge₁`/`hlarge₂`),
the gap sum of `n * ∏ p ∈ B, p` is controlled by that of `n` plus the one-scale
bounds plus a `16K/(δx₀)` cross-term. -/
theorem scaleStep_gapSum_le {n : ℕ} (hn : n ≠ 0) {B : Finset ℕ} {x₀ H N K : ℕ}
    (hprime : ∀ p ∈ B, p.Prime) (hcard : B.card = K) (hN : 1 ≤ N)
    (hH : 1 ≤ H) (hx₀ : 4 ≤ x₀)
    (hwin : ∀ p ∈ B, x₀ < p ∧ p ≤ x₀ + H)
    (hsep : ∀ p ∈ B, ∀ q ∈ B, p < q → N < q - p)
    (hbig : 8 * (2*H)^(K+1) ≤ x₀) (hKH : 2*K*H ≤ x₀)
    (hlogK : 2 * (1 + Real.log K) ≤ N)
    {δ : ℝ} (hδpos : 0 < δ) (hδ1 : δ ≤ 1)
    (hδ : ∀ d ∈ n.divisors, ∀ e ∈ n.divisors, d < e → δ ≤ Real.log e - Real.log d)
    (hσ : ∑ e ∈ n.divisors, ((e:ℝ))⁻¹ ≤ 2)
    (hlarge₁ : 4*(n:ℝ) ≤ x₀)
    (hlarge₂ : 2*(K:ℝ)*H ≤ δ * x₀) :
    gapSum ((n * ∏ p ∈ B, p).divisors)
      ≤ gapSum (n.divisors) * (1 + 2*K/(x₀:ℝ))
        + 2 * ((K:ℝ)/N + 2*K*(1 + Real.log K)/N^2 + 2*(4:ℝ)^K/x₀ + (2:ℝ)^(K+3)*K/x₀)
        + 16*K/(δ*(x₀:ℝ)) := by
  classical
  have hx₀pos : 0 < x₀ := by omega
  have hx0R : (0:ℝ) < (x₀:ℝ) := by exact_mod_cast hx₀pos
  have hnx : n ≤ x₀ := by
    have h1 : (n:ℝ) ≤ (x₀:ℝ) := by
      have h0 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
      linarith
    exact_mod_cast h1
  have hcop : n.Coprime (∏ p ∈ B, p) :=
    ss_coprime_prod hn hprime (fun p hp => (hwin p hp).1) hnx
  -- cover the consecutive pairs by three classes
  have hcover : ∀ a b, IsConsecutive ((n * ∏ p ∈ B, p).divisors) a b →
      ((a.gcd (∏ p ∈ B, p) = b.gcd (∏ p ∈ B, p) ∧
          IsConsecutive ((n * ∏ p ∈ B, p).divisors) a b) ∨
        ((a.gcd n = b.gcd n ∧ IsConsecutive ((n * ∏ p ∈ B, p).divisors) a b) ∨
         (a.gcd n ≠ b.gcd n ∧ a.gcd (∏ p ∈ B, p) ≠ b.gcd (∏ p ∈ B, p) ∧
          IsConsecutive ((n * ∏ p ∈ B, p).divisors) a b))) := by
    intro a b hcons
    by_cases h1 : a.gcd (∏ p ∈ B, p) = b.gcd (∏ p ∈ B, p)
    · exact Or.inl ⟨h1, hcons⟩
    · by_cases h2 : a.gcd n = b.gcd n
      · exact Or.inr (Or.inl ⟨h2, hcons⟩)
      · exact Or.inr (Or.inr ⟨h2, h1, hcons⟩)
  -- C1: equal `m`-component
  have hsum_m : ∑ a ∈ (∏ p ∈ B, p).divisors, ((a:ℝ))⁻¹ ≤ 1 + 2*(K:ℝ)/x₀ := by
    have h := sum_inv_divisors_le hprime (fun p hp => (hwin p hp).1.le)
      (by rw [hcard]; nlinarith : 2 * B.card ≤ x₀) hx₀pos
    rw [hcard] at h
    exact h
  have hC1 : pairSumOn ((n * ∏ p ∈ B, p).divisors)
      (fun d₁ d₂ => d₁.gcd (∏ p ∈ B, p) = d₂.gcd (∏ p ∈ B, p) ∧
        IsConsecutive ((n * ∏ p ∈ B, p).divisors) d₁ d₂)
      ≤ (1 + 2*(K:ℝ)/x₀) * gapSum n.divisors := by
    refine le_trans (ss_C1_le hcop) ?_
    exact mul_le_mul_of_nonneg_right hsum_m (gapSum_nonneg _)
  -- C2: equal `n`-component, via the one-scale bound
  have hC2 : pairSumOn ((n * ∏ p ∈ B, p).divisors)
      (fun d₁ d₂ => d₁.gcd n = d₂.gcd n ∧
        IsConsecutive ((n * ∏ p ∈ B, p).divisors) d₁ d₂)
      ≤ 2 * ((K:ℝ)/N + (2*K*(1 + Real.log K)/N^2 + 2*(4:ℝ)^K/x₀)
          + (2:ℝ)^(K+3)*K/x₀) := by
    have hswap : pairSumOn (((∏ p ∈ B, p) * n).divisors)
        (fun d₁ d₂ => d₁.gcd n = d₂.gcd n ∧
          IsConsecutive (((∏ p ∈ B, p) * n).divisors) d₁ d₂)
        ≤ (∑ e ∈ n.divisors, ((e:ℝ))⁻¹) * gapSum ((∏ p ∈ B, p).divisors) :=
      ss_C1_le hcop.symm
    rw [mul_comm n (∏ p ∈ B, p)]
    refine le_trans hswap ?_
    have hone := oneScale_gapSum_le hprime hcard hN hH hwin hsep hbig hKH hx₀ hlogK
    calc (∑ e ∈ n.divisors, ((e:ℝ))⁻¹) * gapSum ((∏ p ∈ B, p).divisors)
        ≤ 2 * gapSum ((∏ p ∈ B, p).divisors) :=
          mul_le_mul_of_nonneg_right hσ (gapSum_nonneg _)
      _ ≤ 2 * ((K:ℝ)/N + (2*K*(1 + Real.log K)/N^2 + 2*(4:ℝ)^K/x₀)
            + (2:ℝ)^(K+3)*K/x₀) :=
          mul_le_mul_of_nonneg_left hone (by norm_num)
  -- C3: both components differ
  have hC3 := ss_C3_le hn hprime hcard hwin hKH hx₀ hH hδpos hδ1 hδ hσ hlarge₁ hlarge₂
  -- assemble
  have h1 : gapSum ((n * ∏ p ∈ B, p).divisors)
      ≤ (1 + 2*(K:ℝ)/x₀) * gapSum n.divisors
        + (2 * ((K:ℝ)/N + (2*K*(1 + Real.log K)/N^2 + 2*(4:ℝ)^K/x₀)
            + (2:ℝ)^(K+3)*K/x₀)
          + 16*K/(δ*(x₀:ℝ))) := by
    refine le_trans (gapSum_le_pairSumOn hcover) ?_
    refine le_trans (pairSumOn_or_le _ _ _) ?_
    refine add_le_add hC1 ?_
    refine le_trans (pairSumOn_or_le _ _ _) ?_
    exact add_le_add hC2 hC3
  have heq : (1 + 2*(K:ℝ)/x₀) * gapSum n.divisors
      + (2 * ((K:ℝ)/N + (2*K*(1 + Real.log K)/N^2 + 2*(4:ℝ)^K/x₀)
          + (2:ℝ)^(K+3)*K/x₀)
        + 16*K/(δ*(x₀:ℝ)))
      = gapSum (n.divisors) * (1 + 2*K/(x₀:ℝ))
        + 2 * ((K:ℝ)/N + 2*K*(1 + Real.log K)/N^2 + 2*(4:ℝ)^K/x₀
          + (2:ℝ)^(K+3)*K/x₀)
        + 16*K/(δ*(x₀:ℝ)) := by ring
  linarith [h1, heq]

end Erdos884
