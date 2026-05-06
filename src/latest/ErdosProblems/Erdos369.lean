/-
The most difficult (and, in my opinion, most sensible) interpretation of Erdős Problem #369 (https://www.erdosproblems.com/369) reads:

For every ε > 0 and k ≥ 2, there exists N₀ such that for every N ≥ N₀, there exist k consecutive integers a-k+1, ..., a in [N/2, N] with P⁺(m) ≤ m^ε for each m in {a-k+1, ..., a}, where P⁺(m) denotes the largest prime factor of m.

Back in 1998, Balog and Woody proved that infinitely many such N exist, but did not prove it for all large enough N.

Balog, Antal and Wooley, Trevor D., On strings of consecutive integers with no large prime factors. J. Austral. Math. Soc. Ser. A (1998), 266-276.

The proof that it holds true for all large enough N was given by Sky Yang, with a sketch that can be found here:

https://drive.google.com/file/d/1MxgrA2haXKv_NKSa7sqUI2hZYyZ5JmfP/view

Aristotle from Harmonic (aristotle-harmonic@harmonic.fun) managed to formalize their proof, which can be found below.

Lean version: leanprover/lean4:v4.28.0
Mathlib version: 8f9d9cff6bd728b17a24e163c9402775d9e6a365
-/

import Mathlib

set_option linter.style.setOption false
set_option linter.deprecated false
set_option linter.flexible false
set_option linter.style.cases false
set_option linter.style.induction false
set_option linter.style.longLine false
set_option linter.style.maxHeartbeats false
set_option linter.style.multiGoal false
set_option linter.style.refine false

open Finset Nat BigOperators

noncomputable section

/-- The largest prime factor of a natural number n.
    Returns 0 if n ≤ 1 (no prime factors). -/
def Nat.largestPrimeFactor (n : ℕ) : ℕ :=
  if n ≤ 1 then 0 else n.primeFactors.sup id

lemma Nat.largestPrimeFactor_le (n : ℕ) : n.largestPrimeFactor ≤ n := by
  unfold Nat.largestPrimeFactor; rcases n with ( _ | _ | n ) <;> simp +arith +decide;
  exact fun p pp dp => Nat.le_of_dvd ( Nat.succ_pos _ ) dp

lemma Nat.le_largestPrimeFactor {n p : ℕ} (hp : p ∈ n.primeFactors) :
    p ≤ n.largestPrimeFactor := by
  unfold Nat.largestPrimeFactor;
  split_ifs <;> simp_all +decide;
  · interval_cases n <;> aesop;
  · exact Finset.le_sup ( f := id ) ( by aesop )

/-- The product ∏_{X₀ < p ≤ X₁} (1 - 1/p) can be made arbitrarily small. -/
lemma exists_prime_interval_small_euler_product (θ : ℝ) (hθ : 0 < θ) (X₀ : ℕ) :
    ∃ X₁ : ℕ, X₀ < X₁ ∧
      ∏ p ∈ (Finset.Icc (X₀ + 1) X₁).filter Nat.Prime, (1 - (1 : ℝ) / p) < θ := by
  have h_prod_zero : Filter.Tendsto (fun X₁ : ℕ => ∏ p ∈ Finset.filter Nat.Prime (Finset.Icc (X₀ + 1) X₁), (1 - 1 / (p : ℝ))) Filter.atTop (nhds 0) := by
    have h_sum_diverges : Filter.Tendsto (fun X₁ => ∑ p ∈ Finset.filter Nat.Prime (Finset.Icc (X₀ + 1) X₁), (1 / (p : ℝ))) Filter.atTop Filter.atTop := by
      have h_sum_diverges : Filter.Tendsto (fun X₁ : ℕ => ∑ p ∈ Finset.filter Nat.Prime (Finset.range X₁), (1 / (p : ℝ))) Filter.atTop Filter.atTop := by
        convert Nat.Primes.not_summable_one_div using 1;
        constructor <;> intro h <;> rw [ Filter.tendsto_atTop_atTop ] at *;
        · convert Nat.Primes.not_summable_one_div using 1;
        · intro b
          obtain ⟨i, hi⟩ : ∃ i : Finset ℕ, (∀ p ∈ i, Nat.Prime p) ∧ (∑ p ∈ i, (1 / (p : ℝ))) > b := by
            contrapose! h;
            refine' summable_of_sum_le _ _;
            exacts [ b, fun _ => by positivity, fun u => by simpa using h ( u.image Subtype.val ) fun p hp => by obtain ⟨ q, hq, rfl ⟩ := Finset.mem_image.mp hp; exact q.2 ];
          exact ⟨ i.sup id + 1, fun n hn => hi.2.le.trans <| Finset.sum_le_sum_of_subset_of_nonneg ( fun p hp => Finset.mem_filter.mpr ⟨ Finset.mem_range.mpr <| lt_of_le_of_lt ( Finset.le_sup ( f := id ) hp ) hn, hi.1 p hp ⟩ ) fun _ _ _ => by positivity ⟩;
      have h_eq : ∀ X₁ : ℕ, X₁ ≥ X₀ + 1 → ∑ p ∈ Finset.filter Nat.Prime (Finset.Icc (X₀ + 1) X₁), (1 / (p : ℝ)) = (∑ p ∈ Finset.filter Nat.Prime (Finset.range (X₁ + 1)), (1 / (p : ℝ))) - (∑ p ∈ Finset.filter Nat.Prime (Finset.range (X₀ + 1)), (1 / (p : ℝ))) := by
        intro X₁ hX₁; erw [ eq_sub_iff_add_eq' ] ; erw [ Finset.sum_filter, Finset.sum_filter, Finset.sum_filter ] ; erw [ Finset.sum_Ico_eq_sub _ ] ; aesop;
        linarith;
      exact Filter.Tendsto.congr' ( by filter_upwards [ Filter.eventually_ge_atTop ( X₀ + 1 ) ] with X₁ hX₁; aesop ) ( h_sum_diverges.comp ( Filter.tendsto_add_atTop_nat 1 ) |> Filter.Tendsto.atTop_add <| tendsto_const_nhds.neg );
    have h_exp_bound : ∀ X₁ : ℕ, ∏ p ∈ Finset.filter Nat.Prime (Finset.Icc (X₀ + 1) X₁), (1 - 1 / (p : ℝ)) ≤ Real.exp (-∑ p ∈ Finset.filter Nat.Prime (Finset.Icc (X₀ + 1) X₁), (1 / (p : ℝ))) := by
      intro X₁; rw [ Real.exp_neg, Real.exp_sum ] ; norm_num;
      rw [ ← Finset.prod_inv_distrib ] ; exact Finset.prod_le_prod ( fun _ _ => sub_nonneg.2 <| inv_le_one_of_one_le₀ <| mod_cast Nat.Prime.pos <| by aesop ) fun _ _ => by rw [ ← Real.exp_neg ] ; exact Real.add_one_le_exp _ |> le_trans ( by norm_num ) ;
    exact squeeze_zero ( fun _ => Finset.prod_nonneg fun _ _ => sub_nonneg.2 <| div_le_self zero_le_one <| mod_cast Nat.Prime.pos <| by aesop ) h_exp_bound <| Real.tendsto_exp_atBot.comp <| Filter.tendsto_neg_atTop_atBot.comp h_sum_diverges;
  exact Filter.eventually_atTop.mp ( h_prod_zero.eventually ( gt_mem_nhds hθ ) ) |> fun ⟨ X₁, hX₁ ⟩ => ⟨ X₀ + X₁ + 1, by linarith, hX₁ _ <| by linarith ⟩

/-
log 2 / log 3 is irrational, because 2^a = 3^b has no solution in positive naturals.
-/
lemma irrational_log2_div_log3 : Irrational (Real.log 2 / Real.log 3) := by
  intro ⟨ a, ha ⟩;
  -- Then we have $2^q = 3^p$.
  obtain ⟨p, q, hpq⟩ : ∃ p q : ℕ, p > 0 ∧ q > 0 ∧ 2 ^ q = 3 ^ p := by
    obtain ⟨p, q, hpq⟩ : ∃ p q : ℤ, p > 0 ∧ q > 0 ∧ (2 : ℝ) ^ q = 3 ^ p := by
      -- Then we have $2^q = 3^p$ by properties of logarithms.
      obtain ⟨p, q, hpq⟩ : ∃ p q : ℤ, p > 0 ∧ q > 0 ∧ (Real.log 2) * q = (Real.log 3) * p := by
        obtain ⟨p, q, hpq⟩ : ∃ p q : ℤ, p > 0 ∧ q > 0 ∧ (Real.log 2 / Real.log 3) = p / q := by
          exact ⟨ a.num, a.den, Rat.num_pos.mpr ( show 0 < a by exact_mod_cast ha.symm ▸ div_pos ( Real.log_pos ( by norm_num ) ) ( Real.log_pos ( by norm_num ) ) ), Nat.cast_pos.mpr a.pos, by simpa only [ Rat.cast_def ] using ha.symm ⟩;
        exact ⟨ p, q, hpq.1, hpq.2.1, by rw [ div_eq_div_iff ] at hpq <;> norm_num at * <;> linarith ⟩;
      exact ⟨ p, q, hpq.1, hpq.2.1, by rw [ ← Real.rpow_intCast, ← Real.rpow_intCast, Real.rpow_def_of_pos, Real.rpow_def_of_pos ] <;> norm_num ; linarith ⟩;
    rcases p with ( _ | p ) <;> rcases q with ( _ | q ) <;> norm_num at * ; norm_cast at * ; aesop;
  exact absurd ( congr_arg Even hpq.2.2 ) ( by norm_num [ hpq.1.ne', hpq.2.1.ne', parity_simps ] )

/-
For any positive reals α, β with α/β irrational, and any δ > 0,
    the set {u * α mod β : u ∈ ℕ} is δ-dense in [0, β).
    In particular, there exists a finite bound U such that among
    u = 0, 1, ..., U, every interval of length δ in [0, β) is hit.
-/
set_option maxHeartbeats 800000 in
lemma exists_nat_mul_mod_near (α β : ℝ) (hβ : 0 < β)
    (hirr : Irrational (α / β)) (δ : ℝ) (hδ : 0 < δ) :
    ∃ U : ℕ, ∀ t : ℝ, 0 ≤ t → t < β →
      ∃ u : ℕ, u ≤ U ∧ ∃ w : ℤ, |u * α - w * β - t| < δ := by
  -- Let's set $X = \beta / \delta$ and apply `exists_prime_interval_small_euler_product`.
  set X₀ := Nat.ceil (β / δ) with hX₀_def
  set X₁ := X₀ + 1 with hX₁_def;
  -- By the pigeonhole principle, there exist integers $u_1$ and $u_2$ such that $0 \leq u_1 < u_2 \leq X₀$ and $|(u_2 * α - ⌊(u_2 * α) / β⌋ * β) - (u_1 * α - ⌊(u_1 * α) / β⌋ * β)| < δ$.
  obtain ⟨u₁, u₂, hu₁u₂, hu₁, hu₂⟩ : ∃ u₁ u₂ : ℕ, 0 ≤ u₁ ∧ u₁ < u₂ ∧ u₂ ≤ X₀ ∧ |(u₂ * α - ⌊(u₂ * α) / β⌋ * β) - (u₁ * α - ⌊(u₁ * α) / β⌋ * β)| < δ := by
    -- By the pigeonhole principle, since there are $X₀ + 1$ numbers and only $X₀$ intervals, at least two of these numbers must fall into the same interval.
    have h_pigeonhole : ∃ u₁ u₂ : ℕ, 0 ≤ u₁ ∧ u₁ < u₂ ∧ u₂ ≤ X₀ ∧ ⌊((u₂ * α - ⌊(u₂ * α) / β⌋ * β) / δ)⌋ = ⌊((u₁ * α - ⌊(u₁ * α) / β⌋ * β) / δ)⌋ := by
      by_contra! h;
      have h_pigeonhole : Finset.card (Finset.image (fun u : ℕ => ⌊((u * α - ⌊(u * α) / β⌋ * β) / δ)⌋) (Finset.range (X₀ + 1))) ≤ X₀ := by
        have h_pigeonhole : Finset.image (fun u : ℕ => ⌊((u * α - ⌊(u * α) / β⌋ * β) / δ)⌋) (Finset.range (X₀ + 1)) ⊆ Finset.Ico 0 X₀ := by
          exact Finset.image_subset_iff.mpr fun u hu => Finset.mem_Ico.mpr ⟨ Int.floor_nonneg.mpr <| div_nonneg ( sub_nonneg.mpr <| by nlinarith [ Int.floor_le ( ( u : ℝ ) * α / β ), mul_div_cancel₀ ( ( u : ℝ ) * α ) hβ.ne' ] ) hδ.le, Int.floor_lt.mpr <| by rw [ div_lt_iff₀ hδ ] ; norm_num; nlinarith [ Nat.le_ceil ( β / δ ), mul_div_cancel₀ β hδ.ne', Int.lt_floor_add_one ( ( u : ℝ ) * α / β ), mul_div_cancel₀ ( ( u : ℝ ) * α ) hβ.ne' ] ⟩;
        exact le_trans ( Finset.card_le_card h_pigeonhole ) ( by simp );
      rw [ Finset.card_image_of_injOn fun u hu v hv huv => le_antisymm ( not_lt.mp fun hlt => h _ _ ( Nat.zero_le _ ) hlt ( by linarith [ Finset.mem_range.mp hu, Finset.mem_range.mp hv ] ) <| by aesop ) ( not_lt.mp fun hlt => h _ _ ( Nat.zero_le _ ) hlt ( by linarith [ Finset.mem_range.mp hu, Finset.mem_range.mp hv ] ) <| by aesop ) ] at h_pigeonhole ; simp +arith +decide at h_pigeonhole;
    obtain ⟨ u₁, u₂, hu₁, hu₂, hu₃, hu₄ ⟩ := h_pigeonhole; use u₁, u₂; simp_all +decide [ Int.floor_eq_iff ] ;
    rw [ abs_lt ] ; constructor <;> nlinarith [ Int.floor_le ( ( ( u₁ : ℝ ) * α - ⌊ ( u₁ : ℝ ) * α / β⌋ * β ) / δ ), Int.lt_floor_add_one ( ( ( u₁ : ℝ ) * α - ⌊ ( u₁ : ℝ ) * α / β⌋ * β ) / δ ), mul_div_cancel₀ ( ( u₁ : ℝ ) * α - ⌊ ( u₁ : ℝ ) * α / β⌋ * β ) hδ.ne', mul_div_cancel₀ ( ( u₂ : ℝ ) * α - ⌊ ( u₂ : ℝ ) * α / β⌋ * β ) hδ.ne' ] ;
  -- Let $γ = (u₂ - u₁) * α mod β$, which satisfies $0 < γ < δ$ (or $β - δ < γ < β$).
  set γ := (u₂ - u₁) * α - (⌊(u₂ * α) / β⌋ - ⌊(u₁ * α) / β⌋) * β with hγ_def
  have hγ_pos : 0 < γ ∨ γ < 0 := by
    by_contra hγ_zero
    have h_eq : (u₂ - u₁) * α = (⌊(u₂ * α) / β⌋ - ⌊(u₁ * α) / β⌋) * β := by
      exact eq_of_sub_eq_zero ( by push Not at hγ_zero; linarith ) ;
    have h_rat : ∃ q : ℚ, α / β = q := by
      exact ⟨ ( ⌊ ( u₂ : ℝ ) * α / β⌋ - ⌊ ( u₁ : ℝ ) * α / β⌋ ) / ( u₂ - u₁ ), by push_cast; rw [ div_eq_div_iff ] <;> nlinarith [ show ( u₂ : ℝ ) > u₁ by norm_cast ] ⟩ ;
    exact hirr ⟨h_rat.choose, h_rat.choose_spec.symm⟩
  have hγ_lt_delta : |γ| < δ := by
    convert hu₂.2 using 2 ; ring!;
  have hγ_ne_zero : γ ≠ 0 := by
    cases hγ_pos <;> linarith [ abs_lt.mp hγ_lt_delta ] ;
  generalize_proofs at *; (
  -- Let $U = \lceil \beta / |\gamma| \rceil \cdot (u₂ - u₁)$.
  set U := Nat.ceil (β / |γ|) * (u₂ - u₁) with hU_def
  generalize_proofs at *; (
  -- For any $t \in [0, \beta)$, there exists $k \in \mathbb{N}$ such that $|k\gamma - t| < \delta$ (mod $\beta$).
  have h_k_gamma : ∀ t : ℝ, 0 ≤ t → t < β → ∃ k : ℕ, k ≤ Nat.ceil (β / |γ|) ∧ |k * γ - t| < δ ∨ ∃ k : ℕ, k ≤ Nat.ceil (β / |γ|) ∧ |k * γ - (t - β)| < δ := by
    intro t ht₁ ht₂
    by_cases hγ_pos : 0 < γ
    generalize_proofs at *; (
    -- Let $k$ be the integer such that $k\gamma \leq t < (k+1)\gamma$.
    obtain ⟨k, hk⟩ : ∃ k : ℕ, k * γ ≤ t ∧ t < (k + 1) * γ := by
      exact ⟨ ⌊t / γ⌋₊, by nlinarith [ Nat.floor_le ( show 0 ≤ t / γ by exact div_nonneg ht₁ hγ_pos.le ), mul_div_cancel₀ t hγ_pos.ne' ], by nlinarith [ Nat.lt_floor_add_one ( t / γ ), mul_div_cancel₀ t hγ_pos.ne' ] ⟩
    generalize_proofs at *; (
    use k; left; exact ⟨by
    exact Nat.le_of_lt_succ <| by rw [ ← @Nat.cast_lt ℝ ] ; push_cast; nlinarith [ Nat.le_ceil ( β / |γ| ), abs_of_pos hγ_pos, mul_div_cancel₀ β ( ne_of_gt <| abs_pos.mpr hγ_ne_zero ) ] ;, by
      grind⟩;));
    -- Since $γ < 0$, we can write $γ = -|γ|$.
    have hγ_neg : γ = -|γ| := by
      rw [ abs_of_nonpos ( le_of_not_gt hγ_pos ), neg_neg ]
    generalize_proofs at *; (
    -- Since $γ < 0$, we can write $γ = -|γ|$ and consider the interval $[0, β)$.
    obtain ⟨k, hk⟩ : ∃ k : ℕ, k ≤ Nat.ceil (β / |γ|) ∧ |k * |γ| - (β - t)| < δ := by
      refine' ⟨ ⌊ ( β - t ) / |γ|⌋₊, _, _ ⟩
      generalize_proofs at *; (
      exact Nat.floor_le_ceil _ |> le_trans <| Nat.ceil_mono <| by gcongr ; linarith;);
      rw [ abs_lt ] at * ; constructor <;> nlinarith [ Nat.floor_le ( show 0 ≤ ( β - t ) / |γ| by exact div_nonneg ( by linarith ) ( abs_nonneg _ ) ), Nat.lt_floor_add_one ( ( β - t ) / |γ| ), mul_div_cancel₀ ( β - t ) ( ne_of_gt ( abs_pos.mpr hγ_ne_zero ) ) ] ;
    generalize_proofs at *; (
    exact ⟨ k, Or.inr ⟨ k, hk.1, by rw [ hγ_neg ] ; exact abs_lt.mpr ⟨ by linarith [ abs_lt.mp hk.2 ], by linarith [ abs_lt.mp hk.2 ] ⟩ ⟩ ⟩))
  generalize_proofs at *; (
  use U; intros t ht ht'; obtain ⟨ k, hk ⟩ := h_k_gamma t ht ht'; rcases hk with ( ⟨ hk₁, hk₂ ⟩ | ⟨ k, hk₁, hk₂ ⟩ ) <;> [ refine' ⟨ k * ( u₂ - u₁ ), _, _ ⟩ ; refine' ⟨ k * ( u₂ - u₁ ), _, _ ⟩ ] <;> norm_num [ Nat.cast_sub hu₁.le ] at *;
  · exact Nat.mul_le_mul_right _ hk₁ |> le_trans <| Nat.mul_le_mul_left _ <| Nat.sub_le_sub_right le_rfl _;
  · use k * (⌊(u₂ * α) / β⌋ - ⌊(u₁ * α) / β⌋) + 0; simp_all +decide [ mul_assoc ] ; ring_nf at *; aesop;
  · exact Nat.mul_le_mul_right _ hk₁ |> le_trans <| Nat.mul_le_mul_left _ <| Nat.sub_le_sub_right ( by linarith ) _;
  · use k * (⌊(u₂ * α) / β⌋ - ⌊(u₁ * α) / β⌋) - 1; simp_all +decide [ mul_assoc, sub_mul ] ; ring_nf at *; aesop;)))

/-
For natural numbers a, b, 2^a * 3^b = exp(a * log 2 + b * log 3).
-/
lemma two_pow_mul_three_pow_eq_exp (a b : ℕ) :
    (2 : ℝ) ^ a * 3 ^ b = Real.exp (a * Real.log 2 + b * Real.log 3) := by
  rw [ Real.exp_add, ← Real.rpow_natCast, ← Real.rpow_natCast, Real.rpow_def_of_pos, Real.rpow_def_of_pos ] <;> ring_nf <;> norm_num

/-
For any L > 0, the semigroup L·ℕ·log 2 + L·ℕ·log 3 hits every interval (T - log(4/3), T) for large enough T.
-/
lemma exists_log_combination_in_interval (L : ℕ) (hL : 0 < L) :
    ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      ∃ u v : ℕ, T - Real.log (4/3) < ↑(L * u) * Real.log 2 + ↑(L * v) * Real.log 3 ∧
        ↑(L * u) * Real.log 2 + ↑(L * v) * Real.log 3 < T := by
  -- Set α = L * log 2, β = L * log 3, δ = log (4 / 3). Note α / β = log 2 / log 3 is irrational by irrational_log2_div_log3, and α > 0, β > 0, δ > 0.
  set α : ℝ := L * Real.log 2
  set β : ℝ := L * Real.log 3
  set δ : ℝ := Real.log (4 / 3)
  have hα_pos : 0 < α := by
    positivity
  have hβ_pos : 0 < β := by
    positivity
  have hδ_pos : 0 < δ := by
    positivity
  have h_irr : Irrational (α / β) := by
    rw [ mul_div_mul_left _ _ ( by positivity ) ] ; exact irrational_log2_div_log3;
  -- By exists_nat_mul_mod_near, there exists U such that for any t ∈ [0, β), there exists u ≤ U and integer w with |u*α - w*β - t| < δ.
  obtain ⟨U, hU⟩ : ∃ U : ℕ, ∀ t : ℝ, 0 ≤ t → t < β → ∃ u : ℕ, u ≤ U ∧ ∃ w : ℤ, u * α - w * β ∈ Set.Ioo (t - δ) t := by
    have := exists_nat_mul_mod_near α β hβ_pos h_irr ( δ / 2 ) ( half_pos hδ_pos );
    obtain ⟨ U, hU ⟩ := this;
    use U + 1;
    intros t ht_nonneg ht_lt_beta
    obtain ⟨u, hu_le_U, w, hw⟩ := hU (t - δ / 2 + if t - δ / 2 < 0 then β else 0) (by
    split_ifs <;> linarith [ show δ ≤ β by exact le_trans ( Real.log_le_log ( by norm_num ) ( show ( 4 : ℝ ) / 3 ≤ 3 by norm_num ) ) ( le_mul_of_one_le_left ( Real.log_nonneg ( by norm_num ) ) ( mod_cast hL ) ) ]) (by
    grind);
    split_ifs at hw <;> simp_all +decide [ abs_lt ];
    · exact ⟨ u, by linarith, w + 1, by push_cast; linarith, by push_cast; linarith ⟩;
    · exact ⟨ u, by linarith, w, by linarith, by linarith ⟩;
  use β * ( U + 2 ) + δ;
  intro T hT;
  obtain ⟨ u, hu, w, hw ⟩ := hU ( T - ⌊T / β⌋ * β ) ( by nlinarith [ Int.floor_le ( T / β ), mul_div_cancel₀ T hβ_pos.ne' ] ) ( by nlinarith [ Int.lt_floor_add_one ( T / β ), mul_div_cancel₀ T hβ_pos.ne' ] );
  refine' ⟨ u, Int.natAbs ( ⌊T / β⌋ - w ), _, _ ⟩ <;> norm_num at *;
  · cases abs_cases ( ( ⌊T / β⌋ : ℝ ) - w ) <;> push_cast [ * ] at * <;> nlinarith [ show ( u : ℝ ) ≤ U by norm_cast, show ( L : ℝ ) * Real.log 2 > 0 by positivity, show ( L : ℝ ) * Real.log 3 > 0 by positivity ];
  · rw [ abs_of_nonneg ] <;> norm_num at *;
    · nlinarith [hw.2];
    · exact Int.le_of_lt_add_one ( by rw [ ← @Int.cast_lt ℝ ] ; push_cast; nlinarith [ show ( u : ℝ ) ≤ U by norm_cast, show ( α : ℝ ) ≤ L * Real.log 3 by exact mul_le_mul_of_nonneg_left ( Real.log_le_log ( by norm_num ) ( by norm_num ) ) ( Nat.cast_nonneg _ ) ] )

/-
For any L > 0, numbers of the form 2^(Lu) · 3^(Lv) are dense enough
that they hit any interval (3Y/4, Y) for large Y.
-/
lemma exists_smooth_power_in_interval (L : ℕ) (hL : 0 < L) :
    ∃ Y₀ : ℕ, ∀ Y : ℕ, Y₀ ≤ Y →
      ∃ u v : ℕ, (3 * Y : ℝ) / 4 < (2 : ℝ) ^ (L * u) * 3 ^ (L * v) ∧
        (2 : ℝ) ^ (L * u) * 3 ^ (L * v) < Y := by
  -- Set Y₀ = exp(T₀) + 1 where T₀ is from Lemma 25.
  obtain ⟨T₀, hT₀⟩ := exists_log_combination_in_interval L hL
  set Y₀ := Nat.ceil (Real.exp T₀) + 1 with hY₀_def;
  use Y₀ + 2, fun y hy => ?_;
  -- Apply the Kronecker's theorem result to find $u$ and $v$ such that $T - \log(4/3) < Lu \log 2 + Lv \log 3 < T$.
  obtain ⟨u, v, huv⟩ : ∃ u v : ℕ, Real.log y - Real.log (4 / 3) < (L * u : ℝ) * Real.log 2 + (L * v : ℝ) * Real.log 3 ∧ (L * u : ℝ) * Real.log 2 + (L * v : ℝ) * Real.log 3 < Real.log y := by
    simpa using hT₀ ( Real.log y ) ( Real.le_log_iff_exp_le ( by norm_cast; linarith ) |>.2 <| le_trans ( Nat.le_ceil _ ) <| mod_cast by linarith ) |> fun ⟨ u, v, hu, hv ⟩ => ⟨ u, v, by simpa using hu, by simpa using hv ⟩;
  -- Exponentiating both sides of the inequalities from huv, we get the desired result.
  have h_exp : (Real.exp (Real.log y - Real.log (4 / 3))) < (2 : ℝ) ^ (L * u) * (3 : ℝ) ^ (L * v) ∧ (2 : ℝ) ^ (L * u) * (3 : ℝ) ^ (L * v) < Real.exp (Real.log y) := by
    convert Real.exp_lt_exp.mpr huv.1 |> And.intro <| Real.exp_lt_exp.mpr huv.2 using 1 <;> norm_num [ Real.exp_add, Real.exp_nat_mul, Real.exp_log ] ; ring_nf;
    · norm_num [ ← Real.exp_add, mul_assoc, mul_comm, mul_left_comm ];
      rw [ ← Real.log_lt_log_iff ( by positivity ) ( by positivity ), Real.log_mul ( by positivity ) ( by positivity ), Real.log_pow, Real.log_pow ] ; ring_nf ; norm_num;
      ring_nf;
    · norm_num [ ← Real.exp_add, mul_assoc, mul_comm, mul_left_comm ];
      rw [ ← Real.log_lt_log_iff ( by positivity ) ( by positivity ), Real.log_mul ( by positivity ) ( by positivity ), Real.log_pow, Real.log_pow ] ; ring_nf ; norm_num [ Real.exp_add, Real.exp_nat_mul, Real.exp_log ] ;
      ring_nf;
  norm_num [ Real.exp_sub, Real.exp_log ] at *;
  exact ⟨ u, v, by rw [ Real.exp_log ( Nat.cast_pos.mpr <| by linarith ) ] at h_exp; linarith, by rw [ Real.exp_log ( Nat.cast_pos.mpr <| by linarith ) ] at h_exp; linarith ⟩

/-
Cyclotomic polynomial evaluation bound: Φ_d(b) ≤ (b+1)^φ(d).
-/
lemma cyclotomic_eval_le_pow_totient {b : ℕ} (hb : 1 < (b : ℝ)) (d : ℕ) :
    Polynomial.eval (b : ℝ) (Polynomial.cyclotomic d ℝ) ≤ ((b : ℝ) + 1) ^ d.totient :=
  Polynomial.cyclotomic_eval_le_add_one_pow_totient hb d

/-
When ε ≥ 1, the theorem is trivial: P⁺(m) ≤ m ≤ m^ε for m ≥ 1.
-/
lemma erdos_369_eps_ge_one (k : ℕ) (hk : 2 ≤ k) (ε : ℝ) (hε : 1 ≤ ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∃ a : ℕ, N / 2 ≤ a - (k - 1) ∧ a ≤ N ∧ k ≤ a ∧
        ∀ j : ℕ, j < k → (Nat.largestPrimeFactor (a - j) : ℝ) ≤ ((a - j : ℕ) : ℝ) ^ ε := by
  refine' ⟨ 2 * k, _ ⟩;
  intro N hN
  use N
  simp;
  refine' ⟨ _, _, _ ⟩;
  · omega;
  · linarith;
  · intro j hj; exact le_trans ( Nat.cast_le.mpr ( Nat.largestPrimeFactor_le _ ) ) ( by simpa using Real.rpow_le_rpow_of_exponent_le ( mod_cast Nat.sub_pos_of_lt ( by linarith ) ) hε ) ;

/-
For a squarefree number that is a product of a set of primes S,
    φ(n)/n = ∏_{p ∈ S} (1 - 1/p).
-/
lemma totient_div_eq_euler_product (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p) :
    (↑(Nat.totient (∏ p ∈ S, p)) : ℝ) / ↑(∏ p ∈ S, p) =
      ∏ p ∈ S, (1 - (1 : ℝ) / p) := by
  induction S using Finset.induction <;> simp_all +decide [Finset.prod_insert, sub_mul];
  rw [ Nat.totient_mul ];
  · simp_all +decide [ mul_div_mul_comm, Nat.totient_prime ];
    rw [ Nat.cast_sub hS.1.pos ] ; ring_nf ; norm_num [ hS.1.ne_zero ];
    ring;
  · exact Nat.Coprime.prod_right fun x hx => hS.1.coprime_iff_not_dvd.mpr fun h => ‹¬_› <| by have := Nat.prime_dvd_prime_iff_eq hS.1 ( hS.2 x hx ) ; aesop;

/-
Step 1: Building moduli with small totient ratio.
    Given θ > 0 and m ≥ 1, we can find m squarefree pairwise coprime
    integers r₁,...,r_m with φ(r_i)/r_i < θ, each > 1, and with
    all prime factors > some X₀ ≥ max(3, m+1).

-/
set_option maxHeartbeats 800000 in
lemma exists_coprime_moduli_small_totient (θ : ℝ) (hθ : 0 < θ) (m : ℕ) (hm : 1 ≤ m) :
    ∃ (r : Fin m → ℕ) (X₀ : ℕ),
      (∀ i, 1 < r i) ∧
      (∀ i j, i ≠ j → Nat.Coprime (r i) (r j)) ∧
      (∀ i, (↑(Nat.totient (r i)) : ℝ) / ↑(r i) < θ) ∧
      X₀ ≥ m + 2 ∧
      (∀ i, ∀ p, p ∈ (r i).primeFactors → X₀ < p) := by
  -- Set X₀ = m + 2.
  set X₀ := m + 2 with hX₀;
  -- We'll use induction to construct the sequence $r$.
  have hr_exists : ∃ r : Fin m → ℕ, (∀ i, 1 < r i) ∧ (∀ i j, i ≠ j → Nat.Coprime (r i) (r j)) ∧ (∀ i, (Nat.totient (r i) : ℝ) / (r i) < θ) ∧ (∀ i, ∀ p ∈ Nat.primeFactors (r i), X₀ < p) := by
    -- For each $i$, choose a set of primes $S_i$ such that $\prod_{p \in S_i} (1 - 1/p) < \theta$ and all primes in $S_i$ are greater than $X₀$.
    have h_prime_sets : ∀ i : Fin m, ∃ S : Finset ℕ, (∀ p ∈ S, Nat.Prime p) ∧ (∀ p ∈ S, X₀ < p) ∧ (∏ p ∈ S, (1 - (1 : ℝ) / p)) < θ ∧ 1 < ∏ p ∈ S, p := by
      intro i
      obtain ⟨S, hS⟩ : ∃ S : Finset ℕ, (∀ p ∈ S, Nat.Prime p) ∧ (∀ p ∈ S, X₀ < p) ∧ (∏ p ∈ S, (1 - (1 : ℝ) / p)) < θ ∧ S.Nonempty := by
        -- By the properties of the Euler product, we can find such a set $S$.
        have h_euler_product : Filter.Tendsto (fun n : ℕ => ∏ p ∈ Finset.filter Nat.Prime (Finset.Icc (X₀ + 1) n), (1 - (1 : ℝ) / p)) Filter.atTop (nhds 0) := by
          have h_euler_product : Filter.Tendsto (fun n : ℕ => ∏ p ∈ Finset.filter Nat.Prime (Finset.Icc (X₀ + 1) n), (1 - (1 : ℝ) / p)) Filter.atTop (nhds 0) := by
            have h_prod_zero : ∀ θ > 0, ∃ N : ℕ, ∀ n ≥ N, ∏ p ∈ Finset.filter Nat.Prime (Finset.Icc (X₀ + 1) n), (1 - (1 : ℝ) / p) < θ := by
              intros θ hθ_pos
              obtain ⟨N, hN⟩ : ∃ N : ℕ, ∏ p ∈ Finset.filter Nat.Prime (Finset.Icc (X₀ + 1) N), (1 - (1 : ℝ) / p) < θ := by
                have := exists_prime_interval_small_euler_product θ hθ_pos ( X₀ ) ; aesop;
              generalize_proofs at *; (
              use N + 1; intros n hn; refine' lt_of_le_of_lt _ hN; (
              rw [ ← Finset.prod_sdiff <| show Finset.filter Nat.Prime ( Finset.Icc ( X₀ + 1 ) N ) ⊆ Finset.filter Nat.Prime ( Finset.Icc ( X₀ + 1 ) n ) from Finset.filter_subset_filter _ <| Finset.Icc_subset_Icc_right <| by linarith ];
              exact mul_le_of_le_one_left ( Finset.prod_nonneg fun _ _ => sub_nonneg.2 <| div_le_self zero_le_one <| mod_cast Nat.Prime.pos <| by aesop ) <| Finset.prod_le_one ( fun _ _ => sub_nonneg.2 <| div_le_self zero_le_one <| mod_cast Nat.Prime.pos <| by aesop ) fun _ _ => sub_le_self _ <| by positivity;);)
            rw [ Metric.tendsto_nhds ];
            norm_num +zetaDelta at *;
            exact fun ε hε => by obtain ⟨ N, hN ⟩ := h_prod_zero ε hε; exact ⟨ N, fun n hn => by rw [ Finset.prod_congr rfl fun x hx => abs_of_nonneg <| sub_nonneg.2 <| inv_le_one_of_one_le₀ <| mod_cast Nat.Prime.pos <| by aesop ] ; exact hN n hn ⟩ ;
          convert h_euler_product using 1;
        have := h_euler_product.eventually ( gt_mem_nhds hθ );
        simp +zetaDelta at *;
        obtain ⟨ N, hN ⟩ := this;
        obtain ⟨ p, hp ⟩ := Nat.exists_infinite_primes ( N + m + 3 );
        exact ⟨ Finset.filter Nat.Prime ( Finset.Icc ( m + 2 + 1 ) p ), fun q hq => Finset.mem_filter.mp hq |>.2, fun q hq => by linarith [ Finset.mem_Icc.mp ( Finset.mem_filter.mp hq |>.1 ) ], hN p ( by linarith ), ⟨ p, Finset.mem_filter.mpr ⟨ Finset.mem_Icc.mpr ⟨ by linarith, by linarith ⟩, hp.2 ⟩ ⟩ ⟩;
      exact ⟨ S, hS.1, hS.2.1, hS.2.2.1, lt_of_lt_of_le ( Nat.Prime.one_lt ( hS.1 _ hS.2.2.2.choose_spec ) ) ( Nat.le_of_dvd ( Finset.prod_pos fun p hp => Nat.Prime.pos ( hS.1 p hp ) ) ( Finset.dvd_prod_of_mem _ hS.2.2.2.choose_spec ) ) ⟩;
    choose S hS₁ hS₂ hS₃ hS₄ using h_prime_sets;
    -- Choose the sets $S_i$ to be pairwise disjoint.
    obtain ⟨T, hT⟩ : ∃ T : Fin m → Finset ℕ, (∀ i, (∀ p ∈ T i, Nat.Prime p)) ∧ (∀ i, (∀ p ∈ T i, X₀ < p)) ∧ (∀ i, (∏ p ∈ T i, (1 - (1 : ℝ) / p)) < θ) ∧ (∀ i, 1 < ∏ p ∈ T i, p) ∧ (∀ i j, i ≠ j → Disjoint (T i) (T j)) := by
      -- Choose the sets $S_i$ to be pairwise disjoint by selecting primes greater than $X₀$ and ensuring no overlap.
      have h_disjoint : ∀ (n : ℕ), ∃ T : Fin n → Finset ℕ, (∀ i, (∀ p ∈ T i, Nat.Prime p)) ∧ (∀ i, (∀ p ∈ T i, X₀ < p)) ∧ (∀ i, (∏ p ∈ T i, (1 - (1 : ℝ) / p)) < θ) ∧ (∀ i, 1 < ∏ p ∈ T i, p) ∧ (∀ i j, i ≠ j → Disjoint (T i) (T j)) := by
        intro n
        induction' n with n ih;
        · exact ⟨ fun _ => ∅, by simp +decide ⟩;
        · obtain ⟨ T, hT₁, hT₂, hT₃, hT₄, hT₅ ⟩ := ih;
          -- Choose a new set $S_{n+1}$ of primes greater than $X₀$ and ensure it is disjoint from all previous sets $T_i$.
          obtain ⟨ S, hS₁, hS₂, hS₃, hS₄ ⟩ : ∃ S : Finset ℕ, (∀ p ∈ S, Nat.Prime p) ∧ (∀ p ∈ S, X₀ < p) ∧ (∏ p ∈ S, (1 - (1 : ℝ) / p)) < θ ∧ 1 < ∏ p ∈ S, p ∧ Disjoint S (Finset.biUnion Finset.univ T) := by
            -- Choose a new set $S_{n+1}$ of primes greater than $X₀$ and ensure it is disjoint from all previous sets $T_i$ by selecting primes greater than $X₀$ and ensuring no overlap.
            obtain ⟨ S, hS₁, hS₂, hS₃, hS₄ ⟩ : ∃ S : Finset ℕ, (∀ p ∈ S, Nat.Prime p) ∧ (∀ p ∈ S, X₀ < p) ∧ (∏ p ∈ S, (1 - (1 : ℝ) / p)) < θ ∧ 1 < ∏ p ∈ S, p ∧ ∀ p ∈ S, p > Finset.sup (Finset.biUnion Finset.univ T) id := by
              have h_exists_prime_interval : ∀ (X₀ : ℕ), ∃ S : Finset ℕ, (∀ p ∈ S, Nat.Prime p) ∧ (∀ p ∈ S, X₀ < p) ∧ (∏ p ∈ S, (1 - (1 : ℝ) / p)) < θ ∧ 1 < ∏ p ∈ S, p := by
                intro X₀
                obtain ⟨ S, hS₁, hS₂ ⟩ : ∃ S : Finset ℕ, (∀ p ∈ S, Nat.Prime p) ∧ (∀ p ∈ S, X₀ < p) ∧ (∏ p ∈ S, (1 - (1 : ℝ) / p)) < θ := by
                  have := exists_prime_interval_small_euler_product θ hθ ( X₀ + 1 );
                  grind +locals;
                by_cases hS_empty : S = ∅;
                · simp_all +decide [ Finset.prod_empty ];
                  exact ⟨ { Nat.find ( Nat.exists_infinite_primes ( X₀ + 1 ) ) }, by simpa using Nat.find_spec ( Nat.exists_infinite_primes ( X₀ + 1 ) ) |>.2, by simpa using Nat.find_spec ( Nat.exists_infinite_primes ( X₀ + 1 ) ) |>.1, by simpa using hS₂.trans_le' <| by norm_num, by simpa using Nat.Prime.one_lt <| Nat.find_spec ( Nat.exists_infinite_primes ( X₀ + 1 ) ) |>.2 ⟩;
                · exact ⟨ S, hS₁, hS₂.1, hS₂.2, lt_of_lt_of_le ( Nat.Prime.one_lt ( hS₁ _ ( Classical.choose_spec ( Finset.nonempty_of_ne_empty hS_empty ) ) ) ) ( Nat.le_of_dvd ( Finset.prod_pos fun p hp => Nat.Prime.pos ( hS₁ p hp ) ) ( Finset.dvd_prod_of_mem _ ( Classical.choose_spec ( Finset.nonempty_of_ne_empty hS_empty ) ) ) ) ⟩;
              obtain ⟨ S, hS₁, hS₂, hS₃, hS₄ ⟩ := h_exists_prime_interval ( Finset.sup ( Finset.biUnion Finset.univ T ) id + X₀ + 1 );
              exact ⟨ S, hS₁, fun p hp => by linarith [ hS₂ p hp ], hS₃, hS₄, fun p hp => by linarith [ hS₂ p hp ] ⟩;
            exact ⟨ S, hS₁, hS₂, hS₃, hS₄.1, Finset.disjoint_left.mpr fun p hp₁ hp₂ => not_lt_of_ge ( Finset.le_sup ( f := id ) hp₂ ) ( hS₄.2 p hp₁ ) ⟩;
          use Fin.cons S T;
          simp_all +decide [ Fin.forall_fin_succ, Fin.cons ];
          exact ⟨ hT₁, hT₂, fun i hi => Finset.disjoint_left.mpr fun x hx₁ hx₂ => Finset.disjoint_left.mp hS₄.2 hx₁ <| Finset.mem_biUnion.mpr ⟨ i, Finset.mem_univ _, hx₂ ⟩, fun i => Finset.disjoint_left.mpr fun x hx₁ hx₂ => Finset.disjoint_left.mp hS₄.2 hx₂ <| Finset.mem_biUnion.mpr ⟨ i, Finset.mem_univ _, hx₁ ⟩ ⟩;
      exact h_disjoint m;
    use fun i => ∏ p ∈ T i, p;
    refine' ⟨ hT.2.2.2.1, _, _, _ ⟩;
    · exact fun i j hij => Nat.Coprime.prod_left fun p hp => Nat.Coprime.prod_right fun q hq => by have := Nat.coprime_primes ( hT.1 i p hp ) ( hT.1 j q hq ) ; exact this.2 <| by intro t; have := hT.2.2.2.2 i j hij; exact Finset.disjoint_left.mp this hp <| t ▸ hq;
    · intro i;
      convert hT.2.2.1 i using 1;
      convert totient_div_eq_euler_product ( T i ) ( hT.1 i ) using 1;
    · simp_all +decide;
      intro i p pp dp _; rw [ Nat.Prime.dvd_iff_not_coprime pp ] at dp; simp_all +decide [Nat.coprime_prod_right_iff] ;
      obtain ⟨ q, hq₁, hq₂ ⟩ := dp; have := Nat.coprime_primes pp ( hT.1 i q hq₁ ) ; aesop;
  obtain ⟨ r, hr₁, hr₂, hr₃, hr₄ ⟩ := hr_exists; exact ⟨ r, X₀, hr₁, hr₂, hr₃, le_rfl, hr₄ ⟩ ;

/-
Step 2: CRT construction of the multiplier C.
    Given pairwise coprime moduli r₁,...,r_m and a bound k,
    construct C such that j | C for each j ≤ k-1,
    v_q(C) ≡ v_q(j) (mod r_j) for each prime q | j,
    and C only has prime factors ≤ k-1 (plus 2 and 3).
-/
set_option maxHeartbeats 800000 in
lemma exists_crt_multiplier (k : ℕ) (hk : 2 ≤ k) (m : ℕ) (hm : m = k - 1)
    (r : Fin m → ℕ) (hr_pos : ∀ i, 1 < r i)
    (hr_coprime : ∀ i j, i ≠ j → Nat.Coprime (r i) (r j))
    (X₀ : ℕ) (hX₀ : X₀ ≥ m + 2)
    (hr_primes : ∀ i, ∀ p, p ∈ (r i).primeFactors → X₀ < p) :
    ∃ C : ℕ, 0 < C ∧
      (∀ j : ℕ, 1 ≤ j → j < k → j ∣ C) ∧
      (∀ j : ℕ, 1 ≤ j → j < k → ∀ q : ℕ, Nat.Prime q → q ∣ j →
        ∀ (i : Fin m), (i : ℕ) + 1 = j →
          (r i) ∣ ((C / j).factorization q)) ∧
      (∀ p : ℕ, Nat.Prime p → p ∣ C → p ≤ max 3 (k - 1)) := by
  -- Define the exponent $e_q$ for each prime $q \leq \max(3, k-1)$ using the Chinese Remainder Theorem.
  have h_exp : ∀ q : ℕ, Nat.Prime q → q ≤ max 3 (k - 1) → ∃ e_q : ℕ, (∀ j ∈ Finset.Ico 1 k, ∀ i : Fin m, i.val + 1 = j → (r i) ∣ (e_q - Nat.factorization j q)) ∧ e_q ≥ Finset.sup (Finset.Ico 1 k) (fun j => Nat.factorization j q) := by
    -- By the Chinese Remainder Theorem, there exists $e_q$ such that $e_q \equiv \text{Nat.factorization } j q \pmod{r_i}$ for all $j \in \{1, \ldots, k-1\}$ and $i$ such that $i.val + 1 = j$.
    intros q hq_prime hq_le
    have h_crt : ∃ e_q : ℕ, ∀ i : Fin m, e_q ≡ Nat.factorization (i.val + 1) q [MOD r i] := by
      -- Applying the Chinese Remainder Theorem.
      have h_crt : ∀ i : Fin m, ∃ x, x ≡ Nat.factorization (i + 1) q [MOD r i] ∧ ∀ j : Fin m, j ≠ i → x ≡ 0 [MOD r j] := by
        -- For each $i$, let $y_i$ be the multiplicative inverse of $\prod_{j \neq i} r_j$ modulo $r_i$.
        intro i
        obtain ⟨y_i, hy_i⟩ : ∃ y_i : ℕ, y_i * (∏ j ∈ Finset.univ.erase i, r j) ≡ 1 [MOD r i] := by
          have := Nat.exists_mul_mod_eq_one_of_coprime ( show Nat.Coprime ( ∏ j ∈ Finset.univ.erase i, r j ) ( r i ) from Nat.Coprime.prod_left fun j hj => hr_coprime _ _ <| by aesop );
          exact Exists.elim ( this ( hr_pos i ) ) fun x hx => ⟨ x, by rw [ mul_comm, ← hx.2, Nat.ModEq, Nat.mod_mod ] ⟩;
        use y_i * (∏ j ∈ Finset.univ.erase i, r j) * Nat.factorization (i + 1) q;
        exact ⟨ by simpa using hy_i.mul_right _, fun j hj => Nat.modEq_zero_iff_dvd.mpr <| dvd_mul_of_dvd_left ( dvd_mul_of_dvd_right ( Finset.dvd_prod_of_mem _ <| by aesop ) _ ) _ ⟩;
      choose f hf₁ hf₂ using h_crt;
      use ∑ i, f i;
      intro i; simp_all +decide only [ModEq];
      rw [ Finset.sum_nat_mod, Finset.sum_eq_single i ] <;> aesop;
    cases' h_crt with e_q he_q;
    -- Let $M = \prod_{i=0}^{m-1} r_i$.
    set M := Finset.prod Finset.univ r with hM_def;
    refine' ⟨ e_q + M * ( Finset.sup ( Finset.Ico 1 k ) ( fun j => Nat.factorization j q ) + 1 ), _, _ ⟩ <;> simp_all +decide [ Nat.ModEq, Nat.dvd_iff_mod_eq_zero ];
    · intro j hj₁ hj₂ i hi; rw [ ← Nat.dvd_iff_mod_eq_zero ] ; simp +decide [ *, Finset.prod_eq_prod_diff_singleton_mul <| Finset.mem_univ i ] ;
      rw [ ← Nat.mod_add_div ( e_q + ( ∏ x ∈ Finset.univ \ { i }, r x ) * r i * ( Finset.sup ( Finset.Ico 1 k ) ( fun j => j.factorization q ) + 1 ) ) ( r i ), ← Nat.mod_add_div ( j.factorization q ) ( r i ) ] ; simp +decide [ *, Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt ( hr_pos i ) ] ;
      norm_num [ Nat.add_sub_add_left, ← mul_tsub ];
    · intro b hb₁ hb₂; nlinarith [ show Finset.sup ( Finset.Ico 1 k ) ( fun j => Nat.factorization j q ) ≥ Nat.factorization b q from Finset.le_sup ( f := fun j => Nat.factorization j q ) ( Finset.mem_Ico.mpr ⟨ hb₁, hb₂ ⟩ ), show 0 < M from Finset.prod_pos fun i _ => zero_lt_one.trans ( hr_pos i ) ] ;
  choose! e he₁ he₂ using h_exp;
  refine' ⟨ ∏ q ∈ Finset.filter Nat.Prime ( Finset.Icc 1 ( Max.max 3 ( k - 1 ) ) ), q ^ e q, _, _, _, _ ⟩;
  · exact Finset.prod_pos fun q hq => pow_pos ( Nat.Prime.pos ( Finset.mem_filter.mp hq |>.2 ) ) _;
  · intro j hj₁ hj₂; rw [ ← Nat.factorization_prod_pow_eq_self ( by linarith : j ≠ 0 ) ] ;
    rw [ ← Finset.prod_sdiff <| show j.factorization.support ⊆ Finset.filter Nat.Prime ( Finset.Icc 1 ( Max.max 3 ( k - 1 ) ) ) from ?_ ];
    · refine' dvd_mul_of_dvd_right _ _;
      exact Finset.prod_dvd_prod_of_dvd _ _ fun p hp => pow_dvd_pow _ <| le_trans ( Finset.le_sup ( f := fun j => j.factorization p ) <| Finset.mem_Ico.mpr ⟨ hj₁, hj₂ ⟩ ) <| he₂ p ( Nat.prime_of_mem_primeFactors hp ) <| le_trans ( Nat.le_of_mem_primeFactors hp ) <| le_max_of_le_right <| Nat.le_sub_one_of_lt <| by linarith;
    · exact fun p hp => Finset.mem_filter.mpr ⟨ Finset.mem_Icc.mpr ⟨ Nat.pos_of_mem_primeFactors hp, le_trans ( Nat.le_of_mem_primeFactors hp ) ( by omega ) ⟩, Nat.prime_of_mem_primeFactors hp ⟩;
  · intro j hj₁ hj₂ q hq hq' i hi; rw [ Nat.factorization_div ] <;> norm_num;
    · rw [ Nat.factorization_prod ] <;> norm_num;
      · rw [ Finset.sum_eq_single q ] <;> simp_all +decide;
        · exact he₁ q hq ( Or.inr <| Nat.le_sub_one_of_lt <| by linarith [ Nat.le_of_dvd hj₁ hq' ] ) j hj₁ hj₂ i hi;
        · exact fun h => absurd ( h hq.pos ) ( by rintro ⟨ hq₁, hq₂ ⟩ ; linarith [ Nat.le_of_dvd ( by linarith ) hq', Nat.sub_add_cancel ( by linarith : 1 ≤ k ) ] );
      · aesop;
    · rw [ ← Nat.factorization_prod_pow_eq_self ( by linarith : j ≠ 0 ) ];
      rw [ ← Finset.prod_sdiff <| show j.factorization.support ⊆ Finset.filter Nat.Prime ( Finset.Icc 1 ( Max.max 3 ( k - 1 ) ) ) from ?_ ];
      · refine' dvd_mul_of_dvd_right _ _;
        exact Finset.prod_dvd_prod_of_dvd _ _ fun p hp => pow_dvd_pow p ( show Nat.factorization j p ≤ e p from le_trans ( Finset.le_sup ( f := fun j => Nat.factorization j p ) ( Finset.mem_Ico.mpr ⟨ hj₁, hj₂ ⟩ ) ) ( he₂ p ( Nat.prime_of_mem_primeFactors hp ) ( by exact le_trans ( Nat.le_of_mem_primeFactors hp ) ( by omega ) ) ) );
      · exact fun p hp => Finset.mem_filter.mpr ⟨ Finset.mem_Icc.mpr ⟨ Nat.pos_of_mem_primeFactors hp, le_trans ( Nat.le_of_mem_primeFactors hp ) ( by omega ) ⟩, Nat.prime_of_mem_primeFactors hp ⟩;
  · intro p pp dp; contrapose! dp; simp_all +decide [ Nat.Prime.dvd_iff_not_coprime, Nat.coprime_prod_right_iff ] ;
    exact fun x hx₁ hx₂ hx₃ => Nat.Coprime.pow_right _ <| pp.coprime_iff_not_dvd.mpr <| Nat.not_dvd_of_pos_of_lt hx₁ <| by omega;

/-
Step 3: Given a/j is a perfect r-th power (b^r), prime factors of
    a - j = j*(b^r - 1) are bounded by max(k-1, (2b)^{φ(r)}).
-/
lemma prime_factor_bound_of_perfect_power (a j b R : ℕ)
    (hj : 1 ≤ j) (hR : 1 < R) (hb : 1 ≤ b)
    (hpow : a = j * b ^ R) :
    ∀ p : ℕ, p ∈ (a - j).primeFactors →
      p ≤ j ∨ (p : ℝ) ≤ ((2 * b : ℕ) : ℝ) ^ (R.totient : ℝ) := by
  -- If p is a prime factor of a - j, then p divides either j or (b^R - 1).
  intro p hp
  by_cases hpj : p ∣ j;
  · exact Or.inl ( Nat.le_of_dvd hj hpj );
  · -- Since p divides b^R - 1, there exists some d dividing R such that p divides Φ_d(b).
    obtain ⟨d, hd_div, hd_prime⟩ : ∃ d, d ∣ R ∧ p ∣ (Polynomial.eval (b : ℤ) (Polynomial.cyclotomic d ℤ)).natAbs := by
      -- Since p divides a - j and a = j * b^R, we have p divides j * (b^R - 1). Since p does not divide j, it must divide b^R - 1.
      have hp_div_b_pow : p ∣ (b ^ R - 1) := by
        simp_all +decide ;
        exact Or.resolve_left ( hp.1.dvd_mul.mp ( by convert hp.2.1 using 1; rw [ show j * b ^ R - j = j * ( b ^ R - 1 ) by rw [ Nat.mul_sub_left_distrib, Nat.mul_one ] ] ) ) hpj;
      have hp_div_cyclotomic : p ∣ (∏ d ∈ Nat.divisors R, (Polynomial.eval (b : ℤ) (Polynomial.cyclotomic d ℤ)).natAbs) := by
        have hp_div_cyclotomic : (b ^ R - 1 : ℤ) = ∏ d ∈ Nat.divisors R, (Polynomial.eval (b : ℤ) (Polynomial.cyclotomic d ℤ)) := by
          have := Polynomial.prod_cyclotomic_eq_X_pow_sub_one ( by linarith : 1 ≤ R ) ℤ;
          simpa [ Polynomial.eval_prod ] using congr_arg ( Polynomial.eval ( b : ℤ ) ) this.symm;
        rw [ ← Int.natCast_dvd_natCast ] at *;
        cases b <;> cases R <;> simp_all +decide [ ← Finset.abs_prod ];
      contrapose! hp_div_cyclotomic; simp_all +decide [ Nat.Prime.dvd_iff_not_coprime, Nat.coprime_prod_right_iff ] ;
    -- By cyclotomic_eval_le_pow_totient, we have Φ_d(b) ≤ (b+1)^{φ(d)}.
    have h_cyclotomic_bound : (Polynomial.eval (b : ℤ) (Polynomial.cyclotomic d ℤ)).natAbs ≤ (b + 1) ^ (Nat.totient d) := by
      have h_phi_bound : (Polynomial.eval (b : ℝ) (Polynomial.cyclotomic d ℝ)) ≤ (b + 1) ^ (Nat.totient d : ℕ) := by
        convert cyclotomic_eval_le_pow_totient _ _ using 1;
        norm_cast;
        rcases b with ( _ | _ | b ) <;> simp_all +decide;
      have h_phi_bound : (Polynomial.eval (b : ℤ) (Polynomial.cyclotomic d ℤ)) ≤ (b + 1) ^ (Nat.totient d : ℕ) := by
        convert h_phi_bound using 1;
        erw [ ← @Int.cast_le ℝ ] ; norm_num [ Polynomial.cyclotomic ] ; ring_nf;
        split_ifs <;> norm_num [ Polynomial.eval_map ];
      rw [ ← Int.ofNat_le, Int.natAbs_of_nonneg ( by { exact_mod_cast Polynomial.cyclotomic_nonneg d ( by linarith ) } ) ] ; norm_cast;
    -- Since p divides Φ_d(b), we have p ≤ (b + 1)^{φ(d)}.
    have h_p_bound : (p : ℝ) ≤ ((b + 1) : ℝ) ^ (Nat.totient d) := by
      exact_mod_cast le_trans ( Nat.le_of_dvd ( by exact Int.natAbs_pos.mpr ( show Polynomial.eval ( b : ℤ ) ( Polynomial.cyclotomic d ℤ ) ≠ 0 from by { exact ne_of_gt <| by { exact ( by { have := Polynomial.cyclotomic_pos' d ( show ( b : ℤ ) > 1 from mod_cast lt_of_le_of_ne hb <| Ne.symm <| by aesop_cat ) ; aesop_cat } ) } } ) ) hd_prime ) h_cyclotomic_bound;
    -- Since $b \geq 1$, we have $b + 1 \leq 2b$.
    have h_b_plus_one_le_two_b : (b + 1 : ℝ) ≤ (2 * b : ℝ) := by
      norm_cast ; linarith;
    refine' Or.inr ( le_trans h_p_bound _ );
    exact_mod_cast le_trans ( pow_le_pow_left₀ ( by positivity ) h_b_plus_one_le_two_b _ ) ( pow_le_pow_right₀ ( by norm_cast; linarith ) ( Nat.le_of_dvd ( by positivity ) ( Nat.totient_dvd_of_dvd hd_div ) ) )

/-
For any L > 1 with φ(L)/L < θ, and a = b^L with b = 2^u · 3^v,
    each prime factor of a - 1 = b^L - 1 is bounded by (2b)^{φ(L)} ≤ 2^L · N^θ.
-/
lemma smooth_pair_exists (θ : ℝ) (hθ : 0 < θ) :
    ∃ K : ℝ, 0 < K ∧
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∃ a : ℕ, 3 * N / 4 ≤ a ∧ a ≤ N ∧
          (Nat.largestPrimeFactor a : ℝ) ≤ K * (N : ℝ) ^ θ ∧
          (Nat.largestPrimeFactor (a - 1) : ℝ) ≤ K * (N : ℝ) ^ θ := by
  -- Choose $L > 1$ such that $\frac{\phi(L)}{L} < \theta$.
  obtain ⟨L, hL1, hL2⟩ : ∃ L : ℕ, 1 < L ∧ (Nat.totient L : ℝ) / L < θ := by
    have := exists_coprime_moduli_small_totient θ hθ 1 ( by norm_num ) ; aesop;
  -- Set $K = \max(3, 2^L)$.
  set K := max 3 (2 ^ L : ℝ) with hK_def;
  obtain ⟨ Y₀, hY₀ ⟩ := exists_smooth_power_in_interval L ( by linarith );
  refine' ⟨ K, _, Y₀ + 1, _ ⟩ <;> norm_num;
  · positivity;
  · intro N hN
    obtain ⟨u, v, hu⟩ := hY₀ N (by linarith);
    refine' ⟨ 2 ^ ( L * u ) * 3 ^ ( L * v ), _, _, _, _ ⟩ <;> norm_cast at *;
    · exact Nat.div_le_of_le_mul <| by rw [ ← @Nat.cast_le ℝ ] ; push_cast at *; linarith;
    · linarith;
    · -- Since $a = 2^{Lu} \cdot 3^{Lv}$, its largest prime factor is at most 3.
      have h_largest_prime_factor_a : (Nat.largestPrimeFactor (2 ^ (L * u) * 3 ^ (L * v))) ≤ 3 := by
        rw [ Nat.largestPrimeFactor ];
        split_ifs <;> norm_num [ Nat.primeFactors_mul, Nat.primeFactors_pow ] at *;
        rintro b ( ⟨ hb₁, hb₂ ⟩ | ⟨ hb₁, hb₂ ⟩ ) <;> have := Nat.Prime.dvd_of_dvd_pow hb₁ hb₂ <;> have := Nat.le_of_dvd ( by positivity ) this <;> interval_cases b <;> trivial;
      exact le_trans ( Nat.cast_le.mpr h_largest_prime_factor_a ) ( by rw [ hK_def ] ; exact le_trans ( by norm_num ) ( le_mul_of_one_le_right ( by positivity ) ( Real.one_le_rpow ( mod_cast by linarith ) ( by positivity ) ) ) );
    · -- By Lemma 2, each prime factor of $a - 1$ is bounded by $(2b)^{\phi(L)} \leq 2^L \cdot N^\theta$.
      have h_prime_factor_bound : ∀ p : ℕ, p ∈ (2 ^ (L * u) * 3 ^ (L * v) - 1).primeFactors → p ≤ (2 * (2 ^ u * 3 ^ v) : ℝ) ^ (Nat.totient L : ℝ) := by
        have := prime_factor_bound_of_perfect_power ( 2 ^ ( L * u ) * 3 ^ ( L * v ) ) 1 ( 2 ^ u * 3 ^ v ) L ?_ ?_ ?_ ?_ <;> norm_num at *;
        · exact fun p pp dp dp' => Or.resolve_left ( this p pp dp dp' ) ( not_le_of_gt pp.one_lt );
        · linarith;
        · exact Nat.mul_pos ( pow_pos ( by decide ) _ ) ( pow_pos ( by decide ) _ );
        · ring;
      -- Since $b^L = a \leq N$, we have $b \leq N^{1/L}$.
      have hb_bound : (2 ^ u * 3 ^ v : ℝ) ≤ N ^ (1 / L : ℝ) := by
        have hb_bound : (2 ^ (L * u) * 3 ^ (L * v) : ℝ) ≤ N := by
          exact_mod_cast hu.2.le;
        contrapose! hb_bound;
        convert pow_lt_pow_left₀ hb_bound ( by positivity ) ( by positivity : ( L : ℕ ) ≠ 0 ) using 1 <;> norm_num [ pow_mul' ];
        · rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( Nat.cast_nonneg _ ), inv_mul_cancel₀ ( by positivity ), Real.rpow_one ];
        · ring;
      -- Therefore, $(2b)^{\phi(L)} \leq (2N^{1/L})^{\phi(L)} = 2^{\phi(L)} \cdot N^{\phi(L)/L} \leq 2^L \cdot N^\theta$.
      have h_bound : (2 * (2 ^ u * 3 ^ v) : ℝ) ^ (Nat.totient L : ℝ) ≤ 2 ^ L * N ^ θ := by
        refine le_trans ( Real.rpow_le_rpow ( by positivity ) ( mul_le_mul_of_nonneg_left hb_bound <| by positivity ) <| by positivity ) ?_;
        rw [ Real.mul_rpow ( by positivity ) ( by positivity ), ← Real.rpow_natCast, ← Real.rpow_mul ( by positivity ), mul_comm ];
        rw [ mul_comm ] ; gcongr;
        · norm_num;
        · exact Nat.totient_le L;
        · exact_mod_cast Nat.one_le_iff_ne_zero.mpr ( by aesop_cat );
        · simpa [ div_eq_inv_mul ] using hL2.le;
      refine' le_trans _ ( mul_le_mul_of_nonneg_right ( le_max_right _ _ ) ( by positivity ) );
      refine' le_trans _ h_bound;
      by_cases h : 2 ^ ( L * u ) * 3 ^ ( L * v ) - 1 = 0 <;> simp_all +decide [ Nat.largestPrimeFactor ];
      · positivity;
      · split_ifs <;> norm_cast at * ; aesop;
        exact Finset.sup_le fun p hp => h_prime_factor_bound p ( Nat.prime_of_mem_primeFactors hp ) ( Nat.dvd_of_mem_primeFactors hp )

/-
If every prime exponent in the factorization of n is divisible by r, then n is a perfect r-th power.
-/
lemma is_perfect_power_of_factorization_dvd (n r : ℕ) (hn : n ≠ 0)
    (h : ∀ p : ℕ, Nat.Prime p → r ∣ n.factorization p) :
    ∃ b : ℕ, n = b ^ r := by
  exact ⟨ ∏ p ∈ Nat.primeFactors n, p ^ ( n.factorization p / r ), by nth_rw 1 [ ← Nat.factorization_prod_pow_eq_self hn ] ; rw [ ← Finset.prod_pow ] ; exact Finset.prod_congr rfl fun p hp => by rw [ ← pow_mul, Nat.div_mul_cancel <| h p <| Nat.prime_of_mem_primeFactors hp ] ⟩

/-
The smooth pair result implies smooth_consecutive_exists for k = 2.
-/
lemma smooth_consecutive_exists_k2 (θ : ℝ) (hθ : 0 < θ) :
    ∃ K : ℝ, 0 < K ∧
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∃ a : ℕ, 3 * N / 4 ≤ a ∧ a ≤ N ∧
          ∀ j : ℕ, j < 2 →
            (Nat.largestPrimeFactor (a - j) : ℝ) ≤ K * (N : ℝ) ^ θ := by
  obtain ⟨ K, hK₀, N₀, hN₀ ⟩ := smooth_pair_exists θ hθ;
  use K, hK₀, N₀;
  intro N hN;
  obtain ⟨ a, ha₁, ha₂, ha₃, ha₄ ⟩ := hN₀ N hN;
  exact ⟨ a, ha₁, ha₂, fun j hj => by interval_cases j <;> aesop ⟩

/-
Stronger CRT multiplier with full factorization conditions .
-/
set_option maxHeartbeats 800000 in
lemma exists_crt_multiplier_strong (k : ℕ) (hk : 2 ≤ k) (m : ℕ) (hm : m = k - 1)
    (r : Fin m → ℕ) (hr_pos : ∀ i, 1 < r i)
    (hr_coprime : ∀ i j, i ≠ j → Nat.Coprime (r i) (r j))
    (X₀ : ℕ) (hX₀ : X₀ ≥ m + 2)
    (hr_primes : ∀ i, ∀ p, p ∈ (r i).primeFactors → X₀ < p) :
    ∃ C : ℕ, 0 < C ∧
      (∀ j : ℕ, 1 ≤ j → j < k → j ∣ C) ∧
      (∀ (i : Fin m) (q : ℕ), Nat.Prime q → q ∣ C →
        (r i) ∣ (C.factorization q - (i.val + 1).factorization q)) ∧
      (∀ p : ℕ, Nat.Prime p → p ∣ C → p ≤ max 3 (k - 1)) := by
  -- Let $C = \prod_{q \leq \max(3, k-1)} q^{e_q}$ where $e_q$ is chosen by CRT.
  obtain ⟨e, he⟩ : ∃ e : ℕ → ℕ, ∀ q, Nat.Prime q → q ≤ max (3 : ℕ) (k - 1) → ∀ i : Fin m, r i ∣ (e q - (Nat.factorization (i.val + 1) q)) ∧ e q ≥ Nat.factorization (i.val + 1) q := by
    -- For each prime $q \leq \max(3, k-1)$, choose $e_q$ such that $e_q \equiv (i+1).factorization q \pmod{r_i}$ for all $i$.
    have h_choose_e : ∀ q, Nat.Prime q → q ≤ max (3 : ℕ) (k - 1) → ∃ e_q : ℕ, ∀ i : Fin m, r i ∣ (e_q - (Nat.factorization (i.val + 1) q)) ∧ e_q ≥ Nat.factorization (i.val + 1) q := by
      intro q hq hq';
      -- By the Chinese Remainder Theorem, there exists an integer $e_q$ such that $e_q \equiv (i+1).factorization q \pmod{r_i}$ for all $i$.
      obtain ⟨e_q, he_q⟩ : ∃ e_q : ℕ, ∀ i : Fin m, e_q ≡ (Nat.factorization (i.val + 1) q) [MOD r i] := by
        have h_crt : ∀ i : Fin m, ∃ e_i : ℕ, e_i ≡ (Nat.factorization (i.val + 1) q) [MOD r i] ∧ ∀ j : Fin m, j ≠ i → e_i ≡ 0 [MOD r j] := by
          intro i
          have h_coprime : Nat.Coprime (r i) (∏ j ∈ Finset.univ.erase i, r j) := by
            exact Nat.Coprime.prod_right fun j hj => hr_coprime i j <| by aesop;
          -- By the Chinese Remainder Theorem, there exists an $e_i$ such that $e_i \equiv (i.val + 1).factorization q \pmod{r_i}$ and $e_i \equiv 0 \pmod{\prod_{j \neq i} r_j}$.
          obtain ⟨e_i, he_i⟩ : ∃ e_i : ℕ, e_i ≡ (Nat.factorization (i.val + 1) q) [MOD r i] ∧ e_i ≡ 0 [MOD ∏ j ∈ Finset.univ.erase i, r j] := by
            have := Nat.chineseRemainder h_coprime
            generalize_proofs at *; (
            exact ⟨ _, this _ _ |>.2.1, this _ _ |>.2.2 ⟩)
          generalize_proofs at *; (
          exact ⟨ e_i, he_i.1, fun j hj => he_i.2.of_dvd <| Finset.dvd_prod_of_mem _ <| by aesop ⟩)
        generalize_proofs at *; (
        choose e he₁ he₂ using h_crt
        generalize_proofs at *; (
        use ∑ i, e i; intro i; simp_all +decide [ ← ZMod.natCast_eq_natCast_iff ] ; ring_nf; (
        rw [ Finset.sum_eq_single i ] <;> simp_all +decide [ add_comm ] ; ring_nf;
        exact fun j hj => he₂ _ _ ( Ne.symm hj ) ▸ by norm_num;);))
      generalize_proofs at *; (
      refine' ⟨ e_q + ( ∏ i : Fin m, r i ) * ( ∑ i : Fin m, Nat.factorization ( i.val + 1 ) q + 1 ), fun i => ⟨ _, _ ⟩ ⟩ <;> simp_all +decide [ Nat.ModEq ];
      · rw [ ← Nat.mod_add_div ( e_q + ( ∏ i : Fin m, r i ) * ( ∑ i : Fin m, ( i.val + 1 |> Nat.factorization ) q + 1 ) ) ( r i ), ← Nat.mod_add_div ( ( i.val + 1 |> Nat.factorization ) q ) ( r i ) ] ; simp +decide [ Nat.add_mod, Nat.mul_mod, Finset.prod_eq_prod_diff_singleton_mul ( Finset.mem_univ i ), he_q ] ; ring_nf;
        norm_num [ Nat.add_sub_add_left, ← mul_tsub ];
      · exact le_add_of_nonneg_of_le ( Nat.zero_le _ ) ( by nlinarith [ show 0 < ∏ i : Fin m, r i from Finset.prod_pos fun _ _ => zero_lt_one.trans ( hr_pos _ ), show ( Nat.factorization ( i.val + 1 ) q ) ≤ ∑ i : Fin m, ( Nat.factorization ( i.val + 1 ) q ) from Finset.single_le_sum ( fun a _ => Nat.zero_le ( Nat.factorization ( a.val + 1 ) q ) ) ( Finset.mem_univ i ), Nat.zero_le ( ∑ i : Fin m, ( Nat.factorization ( i.val + 1 ) q ) ) ] ) ;)
    generalize_proofs at *; (
    choose! e he using h_choose_e ; exact ⟨ e, fun q hq hq' i => he q hq hq' i ⟩ ;)
  generalize_proofs at *; (
  refine' ⟨ ∏ q ∈ Finset.filter Nat.Prime ( Finset.Iic ( max 3 ( k - 1 ) ) ), q ^ e q, _, _, _, _ ⟩ <;> norm_num +zetaDelta at *; (
  exact fun _ _ _ => pow_pos ( Nat.Prime.pos ‹_› ) _;);
  · -- For any $j$ such that $1 \leq j < k$, $j$ can be written as a product of primes $q \leq \max(3, k-1)$. Each prime $q$ in the factorization of $j$ will have an exponent in $j$ that is less than or equal to $e_q$ (since $e_q$ is chosen to be at least the maximum exponent of $q$ in any $j$).
    intros j hj1 hj2
    have h_factorization : j = ∏ q ∈ Finset.filter Nat.Prime (Finset.Iic (max 3 (k - 1))), q ^ (Nat.factorization j q) := by
      conv_lhs => rw [ ← Nat.factorization_prod_pow_eq_self ( by linarith : j ≠ 0 ) ] ;
      rw [ Finsupp.prod_of_support_subset ] <;> norm_num +zetaDelta at *; (
      exact fun p hp => Finset.mem_filter.mpr ⟨ Finset.mem_Iic.mpr ( le_trans ( Nat.le_of_mem_primeFactors hp ) ( Nat.le_trans ( Nat.le_sub_one_of_lt hj2 ) ( Nat.le_max_right _ _ ) ) ), Nat.prime_of_mem_primeFactors hp ⟩ ;)
    generalize_proofs at *; (
    refine' h_factorization ▸ Finset.prod_dvd_prod_of_dvd _ _ fun q hq => pow_dvd_pow _ _ ; simp +decide at * ; (
    exact he q hq.2 hq.1 ⟨ j - 1, by omega ⟩ |>.2 |> le_trans ( by cases j <;> norm_num at * ) ;));
  · intro i q hq hq' ; erw [ Nat.factorization_prod ] <;> simp_all +decide [ Nat.Prime.dvd_iff_not_coprime ] ; (
    by_cases hq'' : q ≤ max 3 ( k - 1 ) <;> simp_all +decide [ Nat.coprime_prod_right_iff ] ; (
    rw [ Finset.sum_eq_single q ] <;> simp_all +decide ;);
    obtain ⟨ x, hx₁, hx₂, hx₃ ⟩ := hq'; simp_all +decide [ Nat.Prime.coprime_iff_not_dvd ] ;
    exact absurd ( hq.dvd_of_dvd_pow hx₃ ) ( Nat.not_dvd_of_pos_of_lt hx₂.pos ( by omega ) ) ;);
    aesop;
  · intro p pp dp; contrapose! dp; simp_all +decide [Nat.Prime.dvd_iff_not_coprime,
    Nat.coprime_prod_right_iff] ;
    exact fun x hx hx' => Nat.Coprime.pow_right _ <| pp.coprime_iff_not_dvd.mpr fun h => by have := Nat.le_of_dvd ( Nat.pos_of_ne_zero hx'.ne_zero ) h; omega;)

set_option maxHeartbeats 800000 in
lemma quotient_is_perfect_power_of_crt (k : ℕ) (hk : 2 ≤ k) (m : ℕ) (hm : m = k - 1)
    (r : Fin m → ℕ) (hr_pos : ∀ i, 1 < r i)
    (hr_coprime : ∀ i j, i ≠ j → Nat.Coprime (r i) (r j))
    (X₀ : ℕ) (hX₀ : X₀ ≥ m + 2)
    (hr_primes : ∀ i, ∀ p, p ∈ (r i).primeFactors → X₀ < p)
    (C : ℕ) (hC : 0 < C)
    (hC_div : ∀ j : ℕ, 1 ≤ j → j < k → j ∣ C)
    (hC_fact : ∀ (i : Fin m) (q : ℕ), Nat.Prime q → q ∣ C →
        (r i) ∣ (C.factorization q - (i.val + 1).factorization q))
    (hC_primes : ∀ p : ℕ, Nat.Prime p → p ∣ C → p ≤ max 3 (k - 1))
    (L : ℕ) (hL : L = ∏ i, r i)
    (u v : ℕ) (i : Fin m) :
    ∃ b : ℕ, C * (2 ^ (L * u) * 3 ^ (L * v)) = (i.val + 1) * b ^ (r i) := by
  obtain ⟨ D, hD ⟩ := hC_div ( i + 1 ) ( by linarith [ Fin.is_lt i ] ) ( by linarith [ Fin.is_lt i, Nat.sub_add_cancel ( by linarith : 1 ≤ k ) ] );
  -- We need to show that $D \cdot 2^{Lu} \cdot 3^{Lv}$ is a perfect $r_i$-th power.
  have h_perfect_power : ∀ q : ℕ, Nat.Prime q → r i ∣ (D * 2 ^ (L * u) * 3 ^ (L * v)).factorization q := by
    intro q hq; by_cases hq2 : q = 2 <;> by_cases hq3 : q = 3 <;> simp_all +decide [ Nat.factorization_mul, ne_of_gt ] ;
    · have := hC_fact i 2 Nat.prime_two; simp_all +decide ;
      by_cases h : 2 ∣ ( i + 1 ) * D <;> simp_all +decide [ Nat.dvd_add_right, Nat.Prime.dvd_mul ];
      · exact dvd_mul_of_dvd_left ( Finset.dvd_prod_of_mem _ ( Finset.mem_univ _ ) ) _;
      · simp_all +decide [ Nat.factorization_eq_zero_of_not_dvd, Nat.dvd_iff_mod_eq_zero ];
        exact Nat.mod_eq_zero_of_dvd ( dvd_mul_of_dvd_left ( Finset.dvd_prod_of_mem _ ( Finset.mem_univ _ ) ) _ );
    · specialize hC_fact i 3 Nat.prime_three ; simp_all +decide [ Nat.Prime.dvd_mul ];
      exact dvd_add ( if h : 3 ∣ ( i : ℕ ) + 1 ∨ 3 ∣ D then hC_fact h else by
        rw [ Nat.factorization_eq_zero_of_not_dvd ] <;> aesop ) ( dvd_mul_of_dvd_left ( Finset.dvd_prod_of_mem _ ( Finset.mem_univ i ) ) _ ) ;
    · by_cases hq4 : q ∣ C <;> simp_all +decide;
      · specialize hC_fact i q hq hq4; aesop;
      · simp_all +decide [ Nat.factorization_eq_zero_of_not_dvd, Nat.Prime.dvd_mul ];
  -- By definition of $b$, we have $b = \prod_{q \in \text{primeFactors}(D \cdot 2^{Lu} \cdot 3^{Lv})} q^{(\text{factorization}(D \cdot 2^{Lu} \cdot 3^{Lv}) q) / r_i}$.
  obtain ⟨b, hb⟩ : ∃ b : ℕ, D * 2 ^ (L * u) * 3 ^ (L * v) = b ^ (r i) := by
    exact is_perfect_power_of_factorization_dvd _ _ ( by aesop_cat ) h_perfect_power |> fun ⟨ b, hb ⟩ => ⟨ b, hb ⟩ ;
  generalize_proofs at *; (
  exact ⟨ b, by rw [ ← hb, hD ] ; ring ⟩ ;)

/-
If b^r ≤ N then b ≤ N^{1/r}.
-/
lemma rpow_inv_le_of_pow_le {b N : ℕ} {r : ℕ} (hr : 0 < r) (h : b ^ r ≤ N) :
    (b : ℝ) ≤ (N : ℝ) ^ (1 / (r : ℝ)) := by
  exact le_trans ( by rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( by positivity ), mul_one_div_cancel ( by positivity ), Real.rpow_one ] ) ( Real.rpow_le_rpow ( by positivity ) ( show ( b : ℝ ) ^ r ≤ ↑N by exact_mod_cast h ) ( by positivity ) )

/-
Largest prime factor of product with {2,3}-smooth and bounded-prime numbers is bounded.
-/
lemma largest_prime_factor_mul_pow23_le (k : ℕ) {C : ℕ} {Lu Lv : ℕ}
    (hC : 0 < C)
    (hC_primes : ∀ p : ℕ, Nat.Prime p → p ∣ C → p ≤ max 3 (k - 1)) :
    Nat.largestPrimeFactor (C * (2 ^ Lu * 3 ^ Lv)) ≤ max 3 (k - 1) := by
  rw [ Nat.largestPrimeFactor ];
  simp_all +decide [ Nat.primeFactors_mul, hC.ne' ];
  rcases Lu with ( _ | Lu ) <;> rcases Lv with ( _ | Lv ) <;> norm_num [ Nat.primeFactors_pow ] at *;
  · split_ifs <;> simp_all +decide [ Finset.sup_le_iff ];
    grind +ring;
  · split_ifs <;> simp_all +decide [ Nat.pow_succ' ];
    grind +ring;
  · split_ifs <;> norm_num;
    grind;
  · split_ifs <;> simp_all +decide ;
    grind +ring

/-
The rpow bound (2b)^{φ(R)} ≤ 2^L * N^θ.
-/
lemma two_mul_rpow_totient_le {b N R L : ℕ} {θ : ℝ}
    (hR : 0 < R) (hθ : 0 < θ)
    (hb : (b : ℝ) ≤ (N : ℝ) ^ (1 / (R : ℝ)))
    (htot : (Nat.totient R : ℝ) / (R : ℝ) < θ)
    (hRL : R ≤ L) :
    ((2 * b : ℕ) : ℝ) ^ (Nat.totient R : ℝ) ≤ 2 ^ (L : ℝ) * (N : ℝ) ^ θ := by
  -- Applying the hypothesis that $b \leq N^{1/R}$ and raising both sides to the power of $\phi(R)$, we get $(2b)^{\phi(R)} \leq (2N^{1/R})^{\phi(R)}$.
  suffices h_suff : (2 * (b : ℝ)) ^ (Nat.totient R : ℝ) ≤ (2 * (N : ℝ) ^ (1 / R : ℝ)) ^ (Nat.totient R : ℝ) by
    simp_all +decide [mul_pow, Real.rpow_natCast];
    refine' le_trans ( mul_le_mul_of_nonneg_left h_suff <| by positivity ) _;
    gcongr <;> norm_cast;
    · exact le_trans ( Nat.totient_le _ ) hRL;
    · rw [ ← Real.rpow_natCast, ← Real.rpow_mul ] <;> norm_num [ hR ];
      by_cases hN : N = 0 <;> simp_all +decide [ div_eq_inv_mul ];
      · rw [ Real.zero_rpow ( by positivity ), Real.zero_rpow ( by positivity ) ];
      · exact Real.rpow_le_rpow_of_exponent_le ( mod_cast Nat.one_le_iff_ne_zero.mpr hN ) htot.le;
  gcongr

set_option maxHeartbeats 3200000 in
lemma smooth_consecutive_exists (θ : ℝ) (hθ : 0 < θ) (k : ℕ) (hk : 2 ≤ k) :
    ∃ K : ℝ, 0 < K ∧
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∃ a : ℕ, 3 * N / 4 ≤ a ∧ a ≤ N ∧
          ∀ j : ℕ, j < k →
            (Nat.largestPrimeFactor (a - j) : ℝ) ≤ K * (N : ℝ) ^ θ := by
  -- Step 1: Get moduli
  obtain ⟨r, X₀, hr_pos, hr_coprime, hr_totient, hX₀, hr_primes⟩ :=
    exists_coprime_moduli_small_totient θ hθ (k - 1) (by omega)
  set L := ∏ i, r i with hL_def
  have hL_pos : 0 < L := Finset.prod_pos fun i _ => lt_trans zero_lt_one (hr_pos i)
  -- Step 2: Get CRT multiplier
  obtain ⟨C, hC_pos, hC_div, hC_fact, hC_primes⟩ :=
    exists_crt_multiplier_strong k hk (k - 1) rfl r hr_pos hr_coprime X₀ hX₀ hr_primes
  -- Step 3: Get smooth power placement
  obtain ⟨Y₀, hY₀⟩ := exists_smooth_power_in_interval L hL_pos
  -- Step 4: Set K and N₀
  refine ⟨max (↑(max 3 (k - 1)) : ℝ) ((2 : ℝ) ^ (L : ℝ)), by positivity,
         C * (Y₀ + 1), fun N hN => ?_⟩
  -- Step 5: Get smooth power in interval
  have hY : Y₀ ≤ N / C + 1 := by
    have h1 : (Y₀ + 1) * C ≤ N := by linarith [mul_comm C (Y₀ + 1)]
    have h2 : Y₀ + 1 ≤ N / C := (Nat.le_div_iff_mul_le hC_pos).mpr h1
    omega
  obtain ⟨u, v, hu_lo, hu_hi⟩ := hY₀ (N / C + 1) hY
  refine ⟨C * (2 ^ (L * u) * 3 ^ (L * v)), ?_, ?_, fun j hj => ?_⟩
  · -- 3N/4 ≤ a
    nontriviality;
    -- By simplifying, we can see that this inequality holds.
    field_simp at *;
    norm_cast at *; rw [ Nat.div_le_iff_le_mul_add_pred ] <;> norm_num ; nlinarith [ Nat.div_add_mod N C, Nat.mod_lt N hC_pos ] ;
  · -- a ≤ N
    norm_cast at * ; nlinarith [ Nat.div_mul_le_self N C ] ;
  · -- P⁺(a-j) ≤ K * N^θ
    -- Let's consider the two cases: $j = 0$ and $j > 0$.
    by_cases hj_zero : j = 0;
    · -- Apply the lemma largest_prime_factor_mul_pow23_le to get the bound.
      have h_bound : Nat.largestPrimeFactor (C * (2 ^ (L * u) * 3 ^ (L * v))) ≤ max 3 (k - 1) := by
        apply largest_prime_factor_mul_pow23_le k hC_pos hC_primes;
      refine le_trans ?_ ( le_mul_of_one_le_right ?_ ?_ ) <;> norm_num [ hj_zero ];
      · grind;
      · exact Real.one_le_rpow ( mod_cast by nlinarith ) ( by positivity );
    · -- Let $i = \langle j - 1, by sorry \rangle$.
      obtain ⟨i, hi⟩ : ∃ i : Fin (k - 1), i.val + 1 = j := by
        exact ⟨ ⟨ j - 1, by omega ⟩, Nat.succ_pred_eq_of_pos ( Nat.pos_of_ne_zero hj_zero ) ⟩;
      -- Apply quotient_is_perfect_power_of_crt to get $b$ such that $C * (2 ^ (L * u) * 3 ^ (L * v)) = (i.val + 1) * b ^ (r i)$.
      obtain ⟨b, hb⟩ : ∃ b : ℕ, C * (2 ^ (L * u) * 3 ^ (L * v)) = (i.val + 1) * b ^ (r i) := by
        apply quotient_is_perfect_power_of_crt k hk (k - 1) rfl r hr_pos hr_coprime X₀ hX₀ hr_primes C hC_pos hC_div hC_fact hC_primes L rfl u v i;
      -- Apply prime_factor_bound_of_perfect_power to get the bound on the largest prime factor.
      have h_prime_factor_bound : ∀ p ∈ (C * (2 ^ (L * u) * 3 ^ (L * v)) - j).primeFactors, p ≤ max 3 (k - 1) ∨ p ≤ (2 * b : ℕ) ^ (Nat.totient (r i) : ℕ) := by
        intros p hp
        have h_prime_factor_bound : p ≤ j ∨ p ≤ (2 * b : ℕ) ^ (Nat.totient (r i) : ℕ) := by
          have h_prime_factor_bound : p ≤ j ∨ p ≤ (2 * b : ℕ) ^ (Nat.totient (r i) : ℕ) := by
            have h_eq : C * (2 ^ (L * u) * 3 ^ (L * v)) - j = j * (b ^ (r i) - 1) := by
              rw [ hb, hi.symm, Nat.mul_sub_left_distrib, Nat.mul_one ]
            have h_prime_factor_bound : ∀ p ∈ (j * (b ^ (r i) - 1)).primeFactors, p ≤ j ∨ p ≤ (2 * b : ℕ) ^ (Nat.totient (r i) : ℕ) := by
              intros p hp
              have h_prime_factor_bound : p ≤ j ∨ p ≤ (2 * b : ℕ) ^ (Nat.totient (r i) : ℕ) := by
                have h_eq : j * (b ^ (r i) - 1) = j * b ^ (r i) - j := by
                  rw [ Nat.mul_sub_left_distrib, Nat.mul_one ]
                convert prime_factor_bound_of_perfect_power ( j * b ^ r i ) j b ( r i ) ( Nat.pos_of_ne_zero hj_zero ) ( hr_pos i ) ( Nat.pos_of_ne_zero ( show b ≠ 0 from by aesop_cat ) ) ( by aesop_cat ) p using 1
                generalize_proofs at *; (
                norm_cast ; aesop ( simp_config := { singlePass := true } ) ;)
              generalize_proofs at *; (
              exact h_prime_factor_bound);
            exact h_prime_factor_bound p ( h_eq ▸ hp ) |> Or.imp id fun h => by simpa [ ← @Nat.cast_le ℝ ] using h;
          exact h_prime_factor_bound;
        exact Or.imp ( fun h => le_trans h ( by omega ) ) id h_prime_factor_bound;
      -- Apply the bound on the largest prime factor to conclude the proof.
      have h_largest_prime_factor_bound : (Nat.largestPrimeFactor (C * (2 ^ (L * u) * 3 ^ (L * v)) - j)) ≤ max (max 3 (k - 1)) ((2 * b : ℕ) ^ (Nat.totient (r i) : ℕ)) := by
        unfold Nat.largestPrimeFactor;
        split_ifs <;> norm_num;
        grind;
      -- Apply the bound on $b$ to conclude the proof.
      have h_b_bound : (2 * b : ℝ) ^ (Nat.totient (r i) : ℝ) ≤ 2 ^ (L : ℝ) * (N : ℝ) ^ θ := by
        have h_b_bound : (b : ℝ) ≤ (N : ℝ) ^ (1 / (r i : ℝ)) := by
          have h_b_bound : (b : ℝ) ^ (r i : ℝ) ≤ N := by
            norm_cast at *;
            nlinarith [ Nat.div_mul_le_self N C, Nat.zero_le ( 2 ^ ( L * u ) * 3 ^ ( L * v ) ), Nat.zero_le ( b ^ r i ) ];
          exact le_trans ( by rw [ ← Real.rpow_mul ( Nat.cast_nonneg _ ), mul_one_div_cancel ( by norm_cast; linarith [ hr_pos i ] ), Real.rpow_one ] ) ( Real.rpow_le_rpow ( by positivity ) h_b_bound ( by positivity ) );
        convert two_mul_rpow_totient_le ( show 0 < r i from pos_of_gt ( hr_pos i ) ) hθ h_b_bound ( hr_totient i ) ( show r i ≤ L from Nat.le_of_dvd hL_pos ( Finset.dvd_prod_of_mem _ ( Finset.mem_univ _ ) ) ) using 1 ; norm_num [ mul_pow, Real.mul_rpow ];
      refine le_trans ( Nat.cast_le.mpr h_largest_prime_factor_bound ) ?_;
      simp +zetaDelta at *;
      refine' ⟨ _, _, _ ⟩;
      · refine' le_trans _ ( le_mul_of_one_le_right _ _ ) <;> norm_num [ hθ.le ];
        exact Real.one_le_rpow ( mod_cast by nlinarith [ Nat.div_add_mod N C, Nat.mod_lt N hC_pos ] ) hθ.le;
      · refine' le_trans _ ( le_mul_of_one_le_right _ _ );
        · exact le_max_of_le_left ( le_max_right _ _ );
        · positivity;
        · exact Real.one_le_rpow ( mod_cast by nlinarith [ Nat.div_add_mod N C, Nat.mod_lt N hC_pos ] ) hθ.le;
      · exact le_trans h_b_bound ( mul_le_mul_of_nonneg_right ( le_max_right _ _ ) ( by positivity ) )

lemma erdos_369_eps_lt_one (k : ℕ) (hk : 2 ≤ k) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∃ a : ℕ, N / 2 ≤ a - (k - 1) ∧ a ≤ N ∧ k ≤ a ∧
        ∀ j : ℕ, j < k → (Nat.largestPrimeFactor (a - j) : ℝ) ≤ ((a - j : ℕ) : ℝ) ^ ε := by
  -- From the core construction to the main result for ε < 1:
  obtain ⟨K, hK₀, N₀', hN₀'⟩ : ∃ K > 0, ∃ N₀' : ℕ, ∀ N : ℕ, N₀' ≤ N → ∃ a : ℕ, 3 * N / 4 ≤ a ∧ a ≤ N ∧ ∀ j : ℕ, j < k → (Nat.largestPrimeFactor (a - j) : ℝ) ≤ K * (N : ℝ) ^ (ε / 2) := by
    convert smooth_consecutive_exists ( ε / 2 ) ( half_pos hε ) k hk using 1;
  -- Choose N₁ large enough that K * N^{ε/2} ≤ (N/2)^ε for all N ≥ N₁.
  obtain ⟨N₁, hN₁⟩ : ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N → K * (N : ℝ) ^ (ε / 2) ≤ (N / 2 : ℝ) ^ ε := by
    -- We can divide both sides by $N^{\varepsilon/2}$ to get $K \leq (1/2)^{\varepsilon} N^{\varepsilon/2}$.
    suffices h_div : ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N → K ≤ (1 / 2 : ℝ) ^ ε * (N : ℝ) ^ (ε / 2) by
      obtain ⟨ N₁, hN₁ ⟩ := h_div; use N₁; intro N hN; convert mul_le_mul_of_nonneg_right ( hN₁ N hN ) ( Real.rpow_nonneg ( Nat.cast_nonneg N ) ( ε / 2 ) ) using 1 ; ring_nf;
      rw [ Real.mul_rpow ( by positivity ) ( by positivity ), ← Real.rpow_natCast, ← Real.rpow_mul ( by positivity ) ] ; ring_nf;
    have h_div : Filter.Tendsto (fun N : ℕ => (1 / 2 : ℝ) ^ ε * (N : ℝ) ^ (ε / 2)) Filter.atTop Filter.atTop := by
      exact Filter.Tendsto.const_mul_atTop ( by positivity ) ( tendsto_rpow_atTop ( by positivity ) |> Filter.Tendsto.comp <| tendsto_natCast_atTop_atTop );
    exact Filter.eventually_atTop.mp ( h_div.eventually_ge_atTop K );
  -- Choose N₀ = max(N₀', N₁, 4k).
  use max (max N₀' N₁) (4 * k);
  intro N hN;
  obtain ⟨ a, ha₁, ha₂, ha₃ ⟩ := hN₀' N ( by aesop );
  refine' ⟨ a, _, _, _, _ ⟩ <;> norm_num at *;
  · omega;
  · linarith;
  · omega;
  · intro j hj; refine' le_trans ( ha₃ j hj ) _;
    refine' le_trans ( hN₁ N hN.2.1 ) _;
    gcongr;
    rw [ div_le_iff₀ ] <;> norm_cast ; omega

/-
Main theorem: Erdős Problem #369.
    For every ε > 0 and k ≥ 2, there exists N₀ such that for every N ≥ N₀,
    there exists a with N/2 ≤ a-k+1 < ··· < a ≤ N and P⁺(m) ≤ m^ε
    for all m ∈ {a-k+1, ..., a}.
-/
theorem erdos_problem_369 (ε : ℝ) (hε : 0 < ε) (k : ℕ) (hk : 2 ≤ k) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∃ a : ℕ, N / 2 ≤ a - (k - 1) ∧ a ≤ N ∧ k ≤ a ∧
        ∀ j : ℕ, j < k → (Nat.largestPrimeFactor (a - j) : ℝ) ≤ ((a - j : ℕ) : ℝ) ^ ε := by
  by_cases hε1 : ε ≥ 1;
  · exact erdos_369_eps_ge_one k hk ε hε1;
  · convert erdos_369_eps_lt_one k hk ε hε using 1

#print axioms erdos_problem_369
-- 'erdos_problem_369' depends on axioms: [propext, Classical.choice, Quot.sound]
