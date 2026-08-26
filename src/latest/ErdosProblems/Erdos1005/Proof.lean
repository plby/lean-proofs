import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-
Let `a_1/b_1, … , a_N/b_N` be the Farey sequence of order `n`. Erdős proved that
there exists a positive constant `c` such that if `k, l` are such that
`1 ≤ k ≤ l ≤ N` and `l ≤ k + c n`, then the Farey terms `a_k/b_k` and `a_l/b_l`
satisfy `(a_l - a_k)(b_l - b_k) ≥ 0`.

Erdős, P., A note on Farey series. Quart. J. Math. Oxford Ser. (1943), 82--85.

I showed that one can take `c = 1/12 + o(1)` and conjectured that this can be
improved to `c = 1/4`, which would be optimal.

W. van Doorn, Improved bounds for the Mayer-Erdős phenomenon on similarly
ordered Farey fractions. arXiv:2509.00121 (2025).

This is now recorded as Erdos Problem #1005 (https://www.erdosproblems.com/1005)
and was solved in a preprint posted by Ricky Cipollini.

R. Cipollini, Optimality of Wouter van Doorn’s Upper Bound for the
Mayer–Erdős Farey Problem. arXiv:2607.23302 (2026).

Ricky also used Aristotle by Harmonic (aristotle-harmonic@harmonic.fun) to
obtain a formalization of the proof, which is available here:

https://github.com/mrricky22/erdos-1005-lean

I thought it would be nice to have the formalization in one single file. The
result can be found below and was also obtained by Aristotle.

Lean version: leanprover/lean4:v4.28.0
-/

open scoped BigOperators
open Filter Topology Finset ArithmeticFunction

namespace Erdos1005

/-- A rational `q` is a Farey fraction of order `n` if it lies in `[0,1]` and has
denominator at most `n`. Recall every `q : ℚ` is stored in lowest terms, so `q.den`
is the reduced denominator and `q.num` the reduced numerator. -/
def IsFarey (n : ℕ) (q : ℚ) : Prop := 0 ≤ q ∧ q ≤ 1 ∧ q.den ≤ n

/-- The number of Farey fractions of order `n` strictly between `x` and `y`. -/
noncomputable def betweenCount (n : ℕ) (x y : ℚ) : ℕ :=
  {q : ℚ | IsFarey n q ∧ x < q ∧ q < y}.ncard

/-- Two Farey fractions `x = a/b < y = c/d` are *badly ordered* if `a < c` but `b > d`. -/
def BadlyOrdered (n : ℕ) (x y : ℚ) : Prop :=
  IsFarey n x ∧ IsFarey n y ∧ x < y ∧ x.num < y.num ∧ y.den < x.den

/-- `f(n)` is the minimum number of Farey fractions strictly between the endpoints of a
badly ordered pair in `F_n`. (If no badly ordered pair exists, `sInf ∅ = 0`.) -/
noncomputable def fVal (n : ℕ) : ℕ :=
  sInf {k | ∃ x y, BadlyOrdered n x y ∧ betweenCount n x y = k}

/-- The totient summatory function `Φ(m) = ∑_{j ≤ m} φ(j)`. -/
def Phi (m : ℕ) : ℕ := ∑ j ∈ Finset.range (m + 1), Nat.totient j

/-- The number of *ordered* coprime pairs `(a,b)` with `1 ≤ a,b ≤ m`. -/
def Pcard (m : ℕ) : ℕ :=
  ((Finset.Icc 1 m ×ˢ Finset.Icc 1 m).filter (fun p => Nat.Coprime p.1 p.2)).card

/-
Classifying ordered coprime pairs by `max(a,b)` gives
`2·Φ(m) = P(m) + 1` for `m ≥ 1`.
-/
theorem two_mul_Phi_eq (m : ℕ) (hm : 1 ≤ m) : 2 * Phi m = Pcard m + 1 := by
  induction hm <;> simp_all +decide [ Finset.sum_range_succ, Phi, Pcard ];
  rename_i k hk ih;
  rw [ show Finset.filter ( fun p : ℕ × ℕ => Nat.Coprime p.1 p.2 ) ( Finset.Icc 1 ( k + 1 ) ×ˢ Finset.Icc 1 ( k + 1 ) ) = Finset.filter ( fun p : ℕ × ℕ => Nat.Coprime p.1 p.2 ) ( Finset.Icc 1 k ×ˢ Finset.Icc 1 k ) ∪ Finset.filter ( fun p : ℕ × ℕ => Nat.Coprime p.1 p.2 ) ( Finset.image ( fun x => ( k + 1, x ) ) ( Finset.Icc 1 ( k + 1 ) ) ) ∪ Finset.filter ( fun p : ℕ × ℕ => Nat.Coprime p.1 p.2 ) ( Finset.image ( fun x => ( x, k + 1 ) ) ( Finset.Icc 1 k ) ) from ?_, Finset.card_union_of_disjoint, Finset.card_union_of_disjoint ];
  · simp_all +decide [ Finset.filter_image, Nat.coprime_comm ];
    rw [ Finset.card_image_of_injective, Finset.card_image_of_injective ] <;> norm_num [ Function.Injective ];
    rw [ show # ( Finset.filter ( fun a => Nat.Coprime a ( k + 1 ) ) ( Finset.Icc 1 ( k + 1 ) ) ) = Nat.totient ( k + 1 ) from ?_, show # ( Finset.filter ( fun a => Nat.Coprime a ( k + 1 ) ) ( Finset.Icc 1 k ) ) = Nat.totient ( k + 1 ) from ?_ ];
    · grind;
    · congr 1 with x ; simp +decide [ Nat.coprime_comm ];
      grind;
    · congr 1 with x ; simp +decide [ Nat.coprime_comm ];
      exact fun hx => ⟨ fun h => Nat.le_of_lt_succ <| h.2.lt_of_ne <| by aesop_cat, fun h => ⟨ Nat.pos_of_ne_zero <| by aesop_cat, by linarith ⟩ ⟩;
  · rw [ Finset.disjoint_left ] ; aesop;
  · rw [ Finset.disjoint_left ] ; aesop;
  · grind

/-
The ordered pairs in `[1,m]²` that are not coprime are at most
`∑_{p ≤ m, p prime} ⌊m/p⌋²`. Equivalently a lower bound on `P(m)`.
-/
theorem Pcard_ge (m : ℕ) :
    m * m ≤ Pcard m + ∑ p ∈ (Finset.Icc 2 m).filter Nat.Prime, (m / p) ^ 2 := by
  -- Let $N$ be the number of non-coprime pairs in $[1,m]^2$.
  set N := ((Finset.Icc 1 m ×ˢ Finset.Icc 1 m).filter (fun p => ¬Nat.Coprime p.1 p.2)).card;
  -- Every non-coprime pair $(a,b)$ (with $a,b \ge 1$) has gcd > 1, hence has a prime divisor $p = \text{minFac}(\gcd(a,b))$; this $p$ is prime, $p \mid a$, $p \mid b$, and $p \le a \le m$. Thus the non-coprime set is a subset of the union over primes $p \le m$ of $S_p := \{(a,b) \in [1,m]^2 : p \mid a \land p \mid b\}$.
  have h_subset : N ≤ ∑ p ∈ (Finset.Icc 2 m).filter Nat.Prime, ((Finset.Icc 1 m).filter (fun a => p ∣ a)).card ^ 2 := by
    have h_subset : N ≤ Finset.card (Finset.biUnion ((Finset.Icc 2 m).filter Nat.Prime) (fun p => Finset.image (fun (a, b) => (a, b)) (Finset.filter (fun a => p ∣ a) (Finset.Icc 1 m) ×ˢ Finset.filter (fun b => p ∣ b) (Finset.Icc 1 m)))) := by
      refine Finset.card_mono ?_;
      intro p hp; simp_all +decide [ Nat.coprime_iff_gcd_eq_one ] ;
      exact ⟨ Nat.minFac ( Nat.gcd p.1 p.2 ), ⟨ ⟨ Nat.Prime.two_le ( Nat.minFac_prime hp.2 ), Nat.le_trans ( Nat.minFac_le ( Nat.gcd_pos_of_pos_left _ hp.1.1.1 ) ) ( Nat.le_trans ( Nat.le_of_dvd hp.1.1.1 ( Nat.gcd_dvd_left _ _ ) ) hp.1.1.2 ) ⟩, Nat.minFac_prime hp.2 ⟩, Nat.dvd_trans ( Nat.minFac_dvd _ ) ( Nat.gcd_dvd_left _ _ ), Nat.dvd_trans ( Nat.minFac_dvd _ ) ( Nat.gcd_dvd_right _ _ ) ⟩;
    refine le_trans h_subset <| le_trans ( Finset.card_biUnion_le ) ?_;
    norm_num [ sq ];
  -- For each prime $p$, $|S_p| = \lfloor m/p \rfloor^2$ (since the conditions on $a$ and $b$ are independent — $S_p$ is a product).
  have h_card_Sp : ∀ p ∈ (Finset.Icc 2 m).filter Nat.Prime, ((Finset.Icc 1 m).filter (fun a => p ∣ a)).card = m / p := by
    intro p hp; rw [ show Finset.filter ( fun a => p ∣ a ) ( Finset.Icc 1 m ) = Finset.image ( fun a => p * a ) ( Finset.Icc 1 ( m / p ) ) from ?_ ] ; rw [ Finset.card_image_of_injective _ fun a b h => mul_left_cancel₀ ( Nat.Prime.ne_zero <| Finset.mem_filter.mp hp |>.2 ) h ] ; simp +decide;
    ext a; simp [Finset.mem_image];
    exact ⟨ fun h => ⟨ a / p, ⟨ Nat.div_pos ( Nat.le_of_dvd h.1.1 h.2 ) ( Nat.Prime.pos ( Finset.mem_filter.mp hp |>.2 ) ), Nat.div_le_div_right h.1.2 ⟩, Nat.mul_div_cancel' h.2 ⟩, by rintro ⟨ k, ⟨ hk₁, hk₂ ⟩, rfl ⟩ ; exact ⟨ ⟨ by nlinarith [ Finset.mem_Icc.mp ( Finset.mem_filter.mp hp |>.1 ) ], by nlinarith [ Finset.mem_Icc.mp ( Finset.mem_filter.mp hp |>.1 ), Nat.div_mul_le_self m p ] ⟩, by simp +decide ⟩ ⟩;
  convert! Nat.add_le_add_left h_subset ( Pcard m ) using 1;
  · rw [ show Pcard m = Finset.card ( Finset.filter ( fun p : ℕ × ℕ => Nat.Coprime p.1 p.2 ) ( Finset.Icc 1 m ×ˢ Finset.Icc 1 m ) ) from rfl ] ; rw [ Finset.card_filter_add_card_filter_not ] ; aesop;
  · exact congr rfl ( Finset.sum_congr rfl fun x hx => by rw [ h_card_Sp x hx ] )

/-
`∑_{p ≤ m, p prime} 1/p² ≤ 97/200`.
-/
theorem prime_recip_sq_bound (m : ℕ) :
    ∑ p ∈ (Finset.Icc 2 m).filter Nat.Prime, (1 / (p : ℝ)) ^ 2 ≤ 97 / 200 := by
  -- Split the sum into two parts: one over primes equal to 2 and one over odd primes.
  have h_split_sum : ∀ m : ℕ, (∑ p ∈ ((Finset.Icc 2 m).filter Nat.Prime), (1 / (p : ℝ)) ^ 2) ≤ 1 / 4 + ∑ p ∈ ((Finset.Icc 3 m).filter (fun p => Nat.Prime p ∧ p % 2 = 1)), (1 / (p : ℝ)) ^ 2 := by
    intro m
    have h_split : ((Finset.Icc 2 m).filter Nat.Prime) ⊆ {2} ∪ ((Finset.Icc 3 m).filter (fun p => Nat.Prime p ∧ p % 2 = 1)) := by
      intro p hp; rcases p with ( _ | _ | _ | p ) <;> simp_all +arith +decide;
      exact hp.2.eq_two_or_odd.resolve_left ( by linarith );
    refine le_trans ( Finset.sum_le_sum_of_subset_of_nonneg h_split fun _ _ _ => sq_nonneg _ ) ?_ ; norm_num [ Finset.sum_union ];
  -- Bound the odd tail. Write odd j = 2k+3 (k ≥ 0). Peel the first 6 terms (k = 0..5, i.e. j = 3,5,7,9,11,13) exactly and telescope the rest:
  have h_odd_tail_bound : ∀ m : ℕ, (∑ p ∈ ((Finset.Icc 3 m).filter (fun p => Nat.Prime p ∧ p % 2 = 1)), (1 / (p : ℝ)) ^ 2) ≤ (∑ k ∈ Finset.range 6, (1 / ((2 * k + 3) : ℝ)) ^ 2) + (∑' k : ℕ, (1 / ((2 * (k + 6) + 3) : ℝ)) ^ 2) := by
    intros m
    have h_odd_tail_bound : (∑ p ∈ ((Finset.Icc 3 m).filter (fun p => Nat.Prime p ∧ p % 2 = 1)), (1 / (p : ℝ)) ^ 2) ≤ (∑ k ∈ Finset.range 6, (1 / ((2 * k + 3) : ℝ)) ^ 2) + (∑ k ∈ Finset.Ico 6 (m / 2 + 1), (1 / ((2 * k + 3) : ℝ)) ^ 2) := by
      have h_odd_tail_bound : ((Finset.Icc 3 m).filter (fun p => Nat.Prime p ∧ p % 2 = 1)) ⊆ Finset.image (fun k => 2 * k + 3) (Finset.range (m / 2 + 1)) := by
        intro p hp; simp_all +decide;
        exact ⟨ p / 2 - 1, by omega, by omega ⟩;
      refine le_trans ( Finset.sum_le_sum_of_subset_of_nonneg h_odd_tail_bound fun _ _ _ => sq_nonneg _ ) ?_;
      rcases n : m / 2 with ( _ | _ | _ | _ | _ | _ | k ) <;> norm_num [ Finset.sum_range_succ, Finset.sum_Ico_eq_sub _ ] at *;
    refine le_trans h_odd_tail_bound ?_;
    norm_num [ add_assoc, mul_add, Finset.sum_Ico_eq_sum_range ];
    exact le_trans ( Finset.sum_le_sum fun _ _ => by ring_nf; norm_num ) ( Summable.sum_le_tsum ( Finset.range ( m / 2 + 1 - 6 ) ) ( fun _ _ => by positivity ) ( by exact_mod_cast Summable.comp_injective ( Real.summable_nat_pow_inv.2 one_lt_two ) fun a b h => by simpa using! h ) );
  -- Bound the telescoping series.
  have h_telescoping_bound : (∑' k : ℕ, (1 / ((2 * (k + 6) + 3) : ℝ)) ^ 2) ≤ (∑' k : ℕ, (1 / ((2 * (k + 6) + 2) * (2 * (k + 6) + 4) : ℝ))) := by
    refine' Summable.tsum_le_tsum _ _ _;
    · exact fun k => by rw [ div_pow, div_le_div_iff₀ ] <;> ring_nf <;> nlinarith;
    · exact Summable.of_nonneg_of_le ( fun _ => sq_nonneg _ ) ( fun n => by rw [ div_pow, div_le_div_iff₀ ] <;> norm_cast <;> ring_nf <;> nlinarith ) ( summable_nat_add_iff 1 |>.2 <| Real.summable_one_div_nat_pow.2 one_lt_two );
    · exact Summable.of_nonneg_of_le ( fun _ => by positivity ) ( fun n => by rw [ div_le_div_iff₀ ] <;> norm_cast <;> ring_nf <;> nlinarith ) ( summable_nat_add_iff 1 |>.2 <| Real.summable_one_div_nat_pow.2 one_lt_two );
  -- Evaluate the telescoping series.
  have h_telescoping_eval : (∑' k : ℕ, (1 / ((2 * (k + 6) + 2) * (2 * (k + 6) + 4) : ℝ))) = (1 / 4) * (1 / (6 + 1 : ℝ)) := by
    -- Recognize that this is a telescoping series.
    have h_telescoping_series : ∀ n : ℕ, ∑ k ∈ Finset.range n, (1 / ((2 * (k + 6) + 2) * (2 * (k + 6) + 4) : ℝ)) = (1 / 4) * (1 / (6 + 1 : ℝ)) - (1 / 4) * (1 / (n + 6 + 1 : ℝ)) := by
      intro n; induction n <;> norm_num [ Finset.sum_range_succ ] at *;
      grind;
    -- Taking the limit of the partial sum as $n$ approaches infinity, we have:
    have h_limit : Filter.Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n, (1 / ((2 * (k + 6) + 2) * (2 * (k + 6) + 4) : ℝ))) Filter.atTop (nhds ((1 / 4) * (1 / (6 + 1 : ℝ)))) := by
      simpa only [ h_telescoping_series ] using! le_trans ( tendsto_const_nhds.sub <| tendsto_const_nhds.mul <| tendsto_const_nhds.div_atTop <| Filter.tendsto_atTop_mono ( fun n => by linarith ) tendsto_natCast_atTop_atTop ) <| by norm_num;
    exact tendsto_nhds_unique ( by exact ( Summable.hasSum <| by exact ( by by_contra h; exact not_tendsto_atTop_of_tendsto_nhds ( h_limit ) <| by exact not_summable_iff_tendsto_nat_atTop_of_nonneg ( fun _ => by positivity ) |>.1 h ) ) |> HasSum.tendsto_sum_nat ) h_limit;
  exact le_trans ( h_split_sum m ) ( by linarith [ h_odd_tail_bound m, show ( ∑ k ∈ Finset.range 6, ( 1 / ( 2 * k + 3 : ℝ ) ) ^ 2 ) = 1 / 9 + 1 / 25 + 1 / 49 + 1 / 81 + 1 / 121 + 1 / 169 by norm_num ] )

/-
`Φ(m) ≥ m(m+1)/4`, in the integer form `4·Φ(m) ≥ m(m+1)`.
-/
theorem four_mul_Phi_ge (m : ℕ) : m * (m + 1) ≤ 4 * Phi m := by
  by_cases hm : m ≤ 31;
  · interval_cases m <;> decide
  · -- For $m \geq 32$, we use the provided bounds to show the inequality.
    have h_bound : (m * m : ℝ) ≤ (Pcard m : ℝ) + m^2 * (97 / 200) := by
      have h_bound : (m * m : ℝ) ≤ (Pcard m : ℝ) + ∑ p ∈ (Finset.Icc 2 m).filter Nat.Prime, (m / p : ℝ)^2 := by
        have h_bound : (m * m : ℝ) ≤ (Pcard m : ℝ) + ∑ p ∈ (Finset.Icc 2 m).filter Nat.Prime, (m / p : ℕ)^2 := by
          exact_mod_cast Pcard_ge m;
        refine le_trans h_bound ?_ ; norm_num [ Finset.sum_add_distrib ];
        exact Finset.sum_le_sum fun x hx => by gcongr ; exact Nat.cast_div_le ..;
      refine le_trans h_bound ?_;
      norm_num [ div_pow, ← Finset.mul_sum _ _ _ ];
      convert! mul_le_mul_of_nonneg_left ( prime_recip_sq_bound m ) ( sq_nonneg ( m : ℝ ) ) using 1 ; norm_num [ div_eq_mul_inv, Finset.mul_sum _ _ _ ];
    have h_bound : (2 * Phi m : ℝ) = (Pcard m : ℝ) + 1 := by
      exact_mod_cast two_mul_Phi_eq m ( by linarith );
    exact Nat.le_of_lt_succ <| by rw [ ← @Nat.cast_lt ℝ ] ; push_cast ; nlinarith [ show ( m : ℝ ) ≥ 32 by exact_mod_cast not_le.mp hm ] ;

/-
`∑_{d ∣ n} μ(d)/d = φ(n)/n`.
-/
theorem moebius_div_sum_eq_totient_div (n : ℕ) (hn : 1 ≤ n) :
    ∑ d ∈ n.divisors, ((ArithmeticFunction.moebius d : ℝ) / (d : ℝ))
      = (Nat.totient n : ℝ) / (n : ℝ) := by
  convert! congr_arg ( fun x : ℝ => x / n ) ( show ∑ d ∈ n.divisors, ( ArithmeticFunction.moebius d : ℝ ) * ( n / d : ℕ ) = ( Nat.totient n : ℝ ) from ?_ ) using 1;
  · rw [ Finset.sum_div _ _ _ ] ; refine' Finset.sum_congr rfl fun x hx => _ ; rw [ Nat.cast_div ( Nat.dvd_of_mem_divisors hx ) ] ; ring_nf ; aesop;
    aesop;
  · have := @ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq ℤ;
    specialize @this ( by infer_instance ) ( fun n => Nat.totient n ) ( fun n => n ) ; norm_cast at *;
    convert! this.mp ( fun n hn => Nat.sum_totient n ) n hn using 1;
    rw [ ← Nat.sum_divisorsAntidiagonal fun x y => ( moebius x : ℝ ) * ( y : ℝ ) ] ; norm_cast

/-
The number of integers `q` with `A < q < B` and `q ≡ c [ZMOD M]` is within `1` of
`(B - A)/M`.
-/
theorem residue_interval_count (M : ℕ) (hM : 1 ≤ M) (c : ℤ) (A B : ℝ) (hAB : A ≤ B) :
    |(({q : ℤ | A < (q : ℝ) ∧ (q : ℝ) < B ∧ (M : ℤ) ∣ (q - c)}.ncard : ℝ) - (B - A) / M)|
      ≤ 1 := by
  -- Let's define the interval $I = (A, B)$ and the residue class $c \pmod{M}$.
  set I := Set.Ioo A B
  set S := {q : ℤ | (q : ℝ) ∈ I ∧ (M : ℤ) ∣ q - c};
  -- The set $S$ is in bijection with the set of integers $k$ such that $⌊α⌋ < k < ⌈β⌉$.
  have h_bij : S = Finset.image (fun k : ℤ => c + M * k) (Finset.Ioo (⌊(A - c) / (M : ℝ)⌋) (⌈(B - c) / (M : ℝ)⌉)) := by
    ext q;
    constructor;
    · intro hq
      obtain ⟨hqI, hqM⟩ := hq
      have hq_div : ∃ k : ℤ, q = c + M * k := by
        exact ⟨ hqM.choose, eq_add_of_sub_eq' hqM.choose_spec ⟩;
      rcases hq_div with ⟨ k, rfl ⟩ ; simp_all +decide [ Int.floor_lt, Int.lt_ceil ];
      exact ⟨ k, ⟨ by rw [ div_lt_iff₀ ( by positivity ) ] ; linarith [ hqI.1 ], by rw [ lt_div_iff₀ ( by positivity ) ] ; linarith [ hqI.2 ] ⟩, Or.inl rfl ⟩;
    · simp +zetaDelta at *;
      rintro x hx₁ hx₂ rfl; exact ⟨ ⟨ by rw [ Int.floor_lt ] at hx₁; rw [ div_lt_iff₀ ( by positivity ) ] at hx₁; norm_num at *; linarith, by rw [ Int.lt_ceil ] at hx₂; rw [ lt_div_iff₀ ( by positivity ) ] at hx₂; norm_num at *; linarith ⟩, by norm_num ⟩ ;
  -- Therefore, the cardinality of $S$ is equal to the cardinality of the interval $(⌊α⌋, ⌈β⌉)$.
  have h_card : Set.ncard S = (⌈(B - c) / (M : ℝ)⌉ - ⌊(A - c) / (M : ℝ)⌋ - 1 : ℤ).toNat := by
    rw [ h_bij, Set.ncard_coe_finset, Finset.card_image_of_injective ] <;> norm_num [ Function.Injective, hM, ne_of_gt ( zero_lt_one.trans_le hM ) ];
  -- Therefore, the cardinality of $S$ is within $1$ of $(B - A)/M$.
  have h_bound : |(⌈(B - c) / (M : ℝ)⌉ - ⌊(A - c) / (M : ℝ)⌋ - 1 : ℤ).toNat - (B - A) / (M : ℝ)| ≤ 1 := by
    rw [ abs_le ] ; constructor <;> cases' h : ⌈ ( B - c ) / M⌉ - ⌊ ( A - c ) / M⌋ - 1 with h <;> norm_num at *;
    · rw [ ← @Int.cast_inj ℝ ] at * ; norm_num at *;
      rw [ div_le_iff₀ ( by positivity ) ];
      nlinarith [ Int.floor_le ( ( A - c ) / M ), Int.lt_floor_add_one ( ( A - c ) / M ), Int.le_ceil ( ( B - c ) / M ), Int.ceil_lt_add_one ( ( B - c ) / M ), show ( M : ℝ ) ≥ 1 by norm_cast, mul_div_cancel₀ ( A - c ) ( by positivity : ( M : ℝ ) ≠ 0 ), mul_div_cancel₀ ( B - c ) ( by positivity : ( M : ℝ ) ≠ 0 ) ];
    · rw [ div_le_iff₀ ( by positivity ) ];
      rw [ Int.negSucc_eq ] at h ; norm_num at h ; rw [ sub_sub, sub_eq_iff_eq_add ] at h ; norm_num [ Int.ceil_eq_iff, Int.floor_eq_iff ] at *;
      nlinarith [ Int.floor_le ( ( A - c ) / M : ℝ ), Int.lt_floor_add_one ( ( A - c ) / M : ℝ ), show ( M : ℝ ) ≥ 1 by norm_cast, mul_div_cancel₀ ( B - c ) ( by positivity : ( M : ℝ ) ≠ 0 ), mul_div_cancel₀ ( A - c ) ( by positivity : ( M : ℝ ) ≠ 0 ) ];
    · rw [ ← @Int.cast_inj ℝ ] at * ; norm_num at *;
      nlinarith [ Int.floor_le ( ( A - c ) / M ), Int.lt_floor_add_one ( ( A - c ) / M ), Int.le_ceil ( ( B - c ) / M ), Int.ceil_lt_add_one ( ( B - c ) / M ), show ( M : ℝ ) ≥ 1 by norm_cast, mul_div_cancel₀ ( B - A ) ( by positivity : ( M : ℝ ) ≠ 0 ), mul_div_cancel₀ ( B - c ) ( by positivity : ( M : ℝ ) ≠ 0 ), mul_div_cancel₀ ( A - c ) ( by positivity : ( M : ℝ ) ≠ 0 ) ];
    · exact le_trans ( neg_nonpos_of_nonneg ( div_nonneg ( sub_nonneg.mpr hAB ) ( Nat.cast_nonneg _ ) ) ) ( by norm_num );
  grind

/-
For `d, s ≥ 1`, `h` coprime to `s`, and `d ∣ e`, the set of `q` satisfying
`d ∣ q` and `(s*d) ∣ (h*q - e)` is a single residue class modulo `s*d`.
-/
theorem residue_class_of_conditions (d s : ℕ) (hd : 1 ≤ d) (h : ℤ)
    (hcop : IsCoprime h (s : ℤ)) (e : ℕ) (hde : (d : ℤ) ∣ (e : ℤ)) :
    ∃ c : ℤ, ∀ q : ℤ,
      ((d : ℤ) ∣ q ∧ ((s * d : ℕ) : ℤ) ∣ (h * q - e)) ↔ (((s * d : ℕ) : ℤ) ∣ (q - c)) := by
  obtain ⟨c, hc⟩ : ∃ c : ℤ, (d : ℤ) ∣ c ∧ (s * d : ℤ) ∣ (h * c - e) := by
    obtain ⟨ u, v, h ⟩ := hcop;
    obtain ⟨ e', he' ⟩ := hde;
    use d * u * e';
    exact ⟨ ⟨ u * e', by ring ⟩, ⟨ -v * e', by linear_combination' h * e' * d - he' ⟩ ⟩;
  use c;
  intro q; constructor <;> intro hq <;> simp_all +decide [ ← ZMod.intCast_zmod_eq_zero_iff_dvd ] ;
  · obtain ⟨ k, hk ⟩ := hq.2; obtain ⟨ m, hm ⟩ := hc.2; simp_all +decide [ sub_eq_iff_eq_add ] ;
    -- Since $h$ and $s$ are coprime, $s$ must divide $k - m$.
    have h_div : (s : ℤ) ∣ (q - c) / d := by
      have h_div : (s : ℤ) ∣ (h * ((q - c) / d)) := by
        exact ⟨ k - m, by cases lt_or_ge 0 h <;> nlinarith [ Int.ediv_mul_cancel ( show ( d : ℤ ) ∣ q - c from by rw [ ← ZMod.intCast_zmod_eq_zero_iff_dvd ] ; aesop ) ] ⟩;
      exact hcop.symm.dvd_of_dvd_mul_left h_div;
    convert! mul_dvd_mul h_div ( dvd_refl ( d : ℤ ) ) using 1 ; rw [ Int.ediv_mul_cancel ] ; simp_all +decide [ ← ZMod.intCast_zmod_eq_zero_iff_dvd ] ;
  · obtain ⟨ k, hk ⟩ := hq; simp_all +decide [ sub_eq_iff_eq_add ] ;
    convert! dvd_add ( dvd_mul_right ( s * d : ℤ ) ( h * k ) ) hc.2 using 1 ; ring

/-- **Per-`d` count.** For `d ∈ e.divisors`, the number of `q ∈ (A,B)` with `d ∣ q` and
`(s*d) ∣ (h*q - e)` is within `1` of `(B - A)/(s*d)`. -/
theorem Nd_count_bound (d s : ℕ) (hd : 1 ≤ d) (hs : 1 ≤ s) (h : ℤ)
    (hcop : IsCoprime h (s : ℤ)) (e : ℕ) (hde : (d : ℤ) ∣ (e : ℤ)) (A B : ℝ) (hAB : A ≤ B) :
    |(({q : ℤ | A < (q : ℝ) ∧ (q : ℝ) < B ∧ (d : ℤ) ∣ q ∧ ((s * d : ℕ) : ℤ) ∣ (h * q - e)}.ncard : ℝ)
        - (B - A) / (s * d : ℕ))| ≤ 1 := by
  obtain ⟨c, hc⟩ := residue_class_of_conditions d s hd h hcop e hde
  have hset : {q : ℤ | A < (q : ℝ) ∧ (q : ℝ) < B ∧ (d : ℤ) ∣ q ∧ ((s * d : ℕ) : ℤ) ∣ (h * q - e)}
      = {q : ℤ | A < (q : ℝ) ∧ (q : ℝ) < B ∧ ((s * d : ℕ) : ℤ) ∣ (q - c)} := by
    ext q; simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩; exact ⟨h1, h2, (hc q).mp ⟨h3, h4⟩⟩
    · rintro ⟨h1, h2, h3⟩; obtain ⟨h4, h5⟩ := (hc q).mpr h3; exact ⟨h1, h2, h4, h5⟩
  rw [hset]
  have hM : 1 ≤ s * d := Nat.one_le_iff_ne_zero.mpr (by positivity)
  simpa using! residue_interval_count (s * d) hM c A B hAB

/-
For `h` coprime to `s ≥ 1`, `e ≥ 1`, and reals `A ≤ B`, the number of integers
`q ∈ (A,B)` such that `s ∣ (h*q - e)` and the resulting `p = (h*q-e)/s` is
coprime to `q`, is at least `(φ(e)/e)·(B-A)/s - τ(e)`, where
`τ(e) = e.divisors.card`.
-/
set_option maxHeartbeats 1000000 in
theorem prim_prog_lower (h : ℤ) (s : ℕ) (hs : 1 ≤ s) (hcop : IsCoprime h (s : ℤ))
    (e : ℕ) (he : 1 ≤ e) (A B : ℝ) (hAB : A ≤ B) :
    ((Nat.totient e : ℝ) / e) * (B - A) / s - (e.divisors.card : ℝ)
      ≤ ({q : ℤ | A < (q : ℝ) ∧ (q : ℝ) < B ∧ (s : ℤ) ∣ (h * q - e) ∧
            IsCoprime ((h * q - e) / s) q}.ncard : ℝ) := by
  -- By the Möbius inversion formula, we have
  have h_moebius : ∑ d ∈ e.divisors, (ArithmeticFunction.moebius d : ℝ) * (Set.ncard {q : ℤ | A < (q : ℝ) ∧ (q : ℝ) < B ∧ (d : ℤ) ∣ q ∧ ((s * d : ℕ) : ℤ) ∣ (h * q - e)}) = (Set.ncard {q : ℤ | A < (q : ℝ) ∧ (q : ℝ) < B ∧ (s : ℤ) ∣ (h * q - e) ∧ IsCoprime ((h * q - e) / s) q}) := by
    -- By the properties of the Möbius function and the definition of the sets involved, we can rewrite the left-hand side of the equation.
    have h_sum_indicator : ∀ q : ℤ, (∑ d ∈ e.divisors, (ArithmeticFunction.moebius d : ℝ) * (if A < (q : ℝ) ∧ (q : ℝ) < B ∧ (d : ℤ) ∣ q ∧ ((s * d : ℕ) : ℤ) ∣ (h * q - e) then 1 else 0)) = (if A < (q : ℝ) ∧ (q : ℝ) < B ∧ (s : ℤ) ∣ (h * q - e) ∧ IsCoprime ((h * q - e) / s) q then 1 else 0) := by
      intro q
      by_cases hq : A < (q : ℝ) ∧ (q : ℝ) < B ∧ (s : ℤ) ∣ (h * q - e);
      · -- Let $g = \gcd((h * q - e) / s, q)$.
        set g := Int.gcd ((h * q - e) / s) q with hg_def
        have hg_div_e : (g : ℤ) ∣ e := by
          have hg_div_e : (g : ℤ) ∣ (h * q - e) := by
            exact dvd_trans ( Int.gcd_dvd_left _ _ ) ( Int.ediv_dvd_of_dvd hq.2.2 ) |> fun x => x.trans ( by norm_num ) ;
          convert! dvd_sub ( dvd_mul_of_dvd_right ( Int.gcd_dvd_right _ _ ) h ) hg_div_e using 1 ; ring
        have hg_divisors : (∑ d ∈ e.divisors, (ArithmeticFunction.moebius d : ℝ) * (if (d : ℤ) ∣ g then 1 else 0)) = if g = 1 then 1 else 0 := by
          have hg_divisors : ∑ d ∈ Nat.divisors g, (ArithmeticFunction.moebius d : ℝ) = if g = 1 then 1 else 0 := by
            have hg_divisors : ∑ d ∈ Nat.divisors g, (ArithmeticFunction.moebius d : ℝ) = (ArithmeticFunction.moebius * ArithmeticFunction.zeta) g := by
              simp +decide [ ArithmeticFunction.moebius, ArithmeticFunction.zeta ];
              rw [ Nat.sum_divisorsAntidiagonal fun x y => if y = 0 then 0 else if Squarefree x then ( -1 : ℝ ) ^ cardFactors x else 0 ];
              exact Finset.sum_congr rfl fun x hx => by rw [ if_neg ( Nat.ne_of_gt ( Nat.div_pos ( Nat.le_of_dvd ( Nat.pos_of_ne_zero ( by aesop ) ) ( Nat.dvd_of_mem_divisors hx ) ) ( Nat.pos_of_mem_divisors hx ) ) ) ] ;
            generalize_proofs at *; (
            rw [ hg_divisors, ArithmeticFunction.moebius_mul_coe_zeta ] ; aesop;)
          generalize_proofs at *; (
          rw [ ← hg_divisors, ← Finset.sum_subset ( show Nat.divisors g ⊆ Nat.divisors e from ?_ ) ];
          · exact Finset.sum_congr rfl fun x hx => by rw [ if_pos ( mod_cast Nat.dvd_of_mem_divisors hx ) ] ; ring;
          · simp +contextual [ Nat.mem_divisors ];
            exact fun x hx₁ hx₂ hx₃ hx₄ => absurd ( hx₃ <| Int.natCast_dvd_natCast.mp hx₄ ) ( by aesop ) ;
          · exact fun x hx => Nat.mem_divisors.mpr ⟨ dvd_trans ( Nat.dvd_of_mem_divisors hx ) ( mod_cast hg_div_e ), by linarith ⟩)
        have h_indicator : (∑ d ∈ e.divisors, (ArithmeticFunction.moebius d : ℝ) * (if A < (q : ℝ) ∧ (q : ℝ) < B ∧ (d : ℤ) ∣ q ∧ ((s * d : ℕ) : ℤ) ∣ (h * q - e) then 1 else 0)) = (∑ d ∈ e.divisors, (ArithmeticFunction.moebius d : ℝ) * (if (d : ℤ) ∣ g then 1 else 0)) := by
          refine' Finset.sum_congr rfl fun x hx => _ ; simp_all +decide [ Int.natCast_dvd_natCast ] ;
          split_ifs <;> simp_all +decide;
          · rename_i h₁ h₂;
            exact False.elim <| h₂ <| Nat.dvd_gcd ( Int.natCast_dvd.mp <| by exact Int.dvd_div_of_mul_dvd <| by simpa [ mul_comm ] using! h₁.2 ) ( Int.natCast_dvd.mp h₁.1 );
          · rename_i h₁ h₂; contrapose! h₁; simp_all +decide;
            exact ⟨ Int.dvd_trans ( Int.natCast_dvd_natCast.mpr h₂ ) ( Int.gcd_dvd_right _ _ ), by convert! mul_dvd_mul_left ( s : ℤ ) ( Int.natCast_dvd_natCast.mpr h₂ |> Int.dvd_trans <| Int.gcd_dvd_left _ _ ) using 1; rw [ Int.mul_ediv_cancel' hq.2.2 ] ⟩
        simp_all +decide [ Int.isCoprime_iff_gcd_eq_one ];
      · rw [ Finset.sum_eq_zero ] <;> simp_all +decide;
        exact fun x hx₁ hx₂ hx₃ hx₄ hx₅ hx₆ => False.elim <| hq hx₃ hx₄ <| dvd_of_mul_right_dvd hx₆;
    -- Apply the sum indicator equality to rewrite the left-hand side of the equation.
    have h_sum_rewrite : ∑ d ∈ e.divisors, (ArithmeticFunction.moebius d : ℝ) * (Set.ncard {q : ℤ | A < (q : ℝ) ∧ (q : ℝ) < B ∧ (d : ℤ) ∣ q ∧ ((s * d : ℕ) : ℤ) ∣ (h * q - e)}) = ∑ q ∈ Finset.Icc (Int.floor A + 1) (Int.ceil B - 1), (∑ d ∈ e.divisors, (ArithmeticFunction.moebius d : ℝ) * (if A < (q : ℝ) ∧ (q : ℝ) < B ∧ (d : ℤ) ∣ q ∧ ((s * d : ℕ) : ℤ) ∣ (h * q - e) then 1 else 0)) := by
      rw [ Finset.sum_comm, Finset.sum_congr rfl ];
      intro d hd; rw [ ← Finset.mul_sum _ _ _ ] ; norm_cast; simp +decide;
      rw [ ← Set.ncard_coe_finset ] ; norm_num [ Set.ncard_eq_toFinset_card' ];
      exact Or.inl ( congr_arg _ ( by ext; exact ⟨ fun hx => ⟨ ⟨ Int.floor_lt.mpr hx.1, Int.lt_ceil.mpr hx.2.1 ⟩, hx ⟩, fun hx => hx.2 ⟩ ) );
    rw [ h_sum_rewrite, Finset.sum_congr rfl fun q hq => h_sum_indicator q ];
    simp +zetaDelta at *;
    rw [ ← Set.ncard_coe_finset ] ; congr ; ext ; simp +decide [ Int.floor_lt, Int.lt_ceil ] ;
    tauto;
  -- Applying the bound from `Nd_count_bound` to each term in the sum.
  have h_bound : |∑ d ∈ e.divisors, (ArithmeticFunction.moebius d : ℝ) * (Set.ncard {q : ℤ | A < (q : ℝ) ∧ (q : ℝ) < B ∧ (d : ℤ) ∣ q ∧ ((s * d : ℕ) : ℤ) ∣ (h * q - e)}) - ∑ d ∈ e.divisors, (ArithmeticFunction.moebius d : ℝ) * ((B - A) / (s * d))| ≤ (e.divisors.card : ℝ) := by
    have h_bound : ∀ d ∈ e.divisors, |(ArithmeticFunction.moebius d : ℝ) * (Set.ncard {q : ℤ | A < (q : ℝ) ∧ (q : ℝ) < B ∧ (d : ℤ) ∣ q ∧ ((s * d : ℕ) : ℤ) ∣ (h * q - e)}) - (ArithmeticFunction.moebius d : ℝ) * ((B - A) / (s * d))| ≤ 1 := by
      intro d hd
      have h_bound : |((Set.ncard {q : ℤ | A < (q : ℝ) ∧ (q : ℝ) < B ∧ (d : ℤ) ∣ q ∧ ((s * d : ℕ) : ℤ) ∣ (h * q - e)}) : ℝ) - ((B - A) / (s * d))| ≤ 1 := by
        convert! Nd_count_bound d s ( Nat.pos_of_mem_divisors hd ) hs h hcop e ( Int.natCast_dvd_natCast.mpr ( Nat.dvd_of_mem_divisors hd ) ) A B hAB using 1;
        norm_cast;
      simp_all +decide [ ← mul_sub, abs_mul ];
      exact le_trans ( mul_le_of_le_one_left ( abs_nonneg _ ) ( by exact_mod_cast ArithmeticFunction.abs_moebius_le_one ) ) h_bound;
    simpa only [ ← Finset.sum_sub_distrib ] using! le_trans ( Finset.abs_sum_le_sum_abs _ _ ) ( le_trans ( Finset.sum_le_sum h_bound ) ( by norm_num ) );
  -- Applying the identity from `moebius_div_sum_eq_totient_div`.
  have h_identity : ∑ d ∈ e.divisors, (ArithmeticFunction.moebius d : ℝ) * ((B - A) / (s * d)) = (B - A) / s * (Nat.totient e : ℝ) / e := by
    convert! congr_arg ( fun x : ℝ => ( B - A ) / s * x ) ( moebius_div_sum_eq_totient_div e he ) using 1 <;> ring_nf;
    simp +decide only [mul_assoc, mul_left_comm, Finset.sum_sub_distrib, Finset.mul_sum _ _ _];
  ring_nf at *; linarith [ abs_le.mp h_bound ] ;

/-
The matching upper bound: the same count is at most `(phi(e)/e)*(B-A)/s + tau(e)`.
-/
set_option maxHeartbeats 1000000 in
theorem prim_prog_upper (h : ℤ) (s : ℕ) (hs : 1 ≤ s) (hcop : IsCoprime h (s : ℤ))
    (e : ℕ) (he : 1 ≤ e) (A B : ℝ) (hAB : A ≤ B) :
    ({q : ℤ | A < (q : ℝ) ∧ (q : ℝ) < B ∧ (s : ℤ) ∣ (h * q - e) ∧
            IsCoprime ((h * q - e) / s) q}.ncard : ℝ)
      ≤ ((Nat.totient e : ℝ) / e) * (B - A) / s + (e.divisors.card : ℝ) := by
  -- By Moebius inversion, the number of coprime solutions is $\sum_{d \mid e} \mu(d) \cdot N_d$.
  have h_moebius : ((Set.ncard {q : ℤ | A < q ∧ q < B ∧ (s : ℤ) ∣ (h * q - e) ∧ IsCoprime ((h * q - e) / s) q}) : ℝ) = ∑ d ∈ e.divisors, (ArithmeticFunction.moebius d : ℝ) * ((Set.ncard {q : ℤ | A < q ∧ q < B ∧ (d : ℤ) ∣ q ∧ ((s * d : ℕ) : ℤ) ∣ (h * q - e)}) : ℝ) := by
    have h_moebius : ∀ q : ℤ, (if A < q ∧ q < B ∧ (s : ℤ) ∣ (h * q - e) ∧ IsCoprime ((h * q - e) / s) q then 1 else 0) = ∑ d ∈ e.divisors, (ArithmeticFunction.moebius d : ℝ) * (if A < q ∧ q < B ∧ (d : ℤ) ∣ q ∧ ((s * d : ℕ) : ℤ) ∣ (h * q - e) then 1 else 0) := by
      intro q
      by_cases hq : A < q ∧ q < B ∧ (s : ℤ) ∣ (h * q - e);
      · -- Let $d = \gcd((h * q - e) / s, q)$. Then $d \mid e$.
        set d := Nat.gcd (Int.natAbs ((h * q - e) / s)) (Int.natAbs q) with hd'
        have hd_div_e : d ∣ e := by
          have hd_div_e : (d : ℤ) ∣ (h * q - e) := by
            convert! Int.natCast_dvd.mpr ( Nat.gcd_dvd_left _ _ ) |> fun x => x.mul_left ( s : ℤ ) using 1;
            rw [ Int.mul_ediv_cancel' hq.2.2 ];
          rw [ ← Int.natCast_dvd_natCast ];
          convert! dvd_sub ( dvd_mul_of_dvd_right ( Int.natCast_dvd.mpr ( Nat.gcd_dvd_right _ _ ) ) h ) hd_div_e using 1 ; ring;
        -- Since $d \mid e$, we can rewrite the sum as $\sum_{d \mid e} \mu(d) \cdot \mathbf{1}_{d \mid \gcd((h * q - e) / s, q)}$.
        have h_sum_div : ∑ d ∈ e.divisors, (ArithmeticFunction.moebius d : ℝ) * (if (d : ℤ) ∣ q ∧ ((s * d : ℕ) : ℤ) ∣ (h * q - e) then 1 else 0) = ∑ d ∈ Nat.divisors d, (ArithmeticFunction.moebius d : ℝ) := by
          rw [ ← Finset.sum_subset ( show Nat.divisors d ⊆ Nat.divisors e from fun x hx => Nat.mem_divisors.mpr ⟨ dvd_trans ( Nat.dvd_of_mem_divisors hx ) hd_div_e, by aesop ⟩ ) ];
          · refine' Finset.sum_congr rfl fun x hx => _;
            simp +zetaDelta at *;
            intro hx'; contrapose! hx'; simp_all +decide [ Nat.dvd_gcd_iff ] ;
            exact ⟨ Int.natCast_dvd.mpr hx.1.2, by convert! mul_dvd_mul_left ( s : ℤ ) ( Int.natCast_dvd.mpr hx.1.1 ) using 1; rw [ Int.mul_ediv_cancel' hq.2.2 ] ⟩;
          · intro x hx hx'; split_ifs <;> simp_all +decide [ Nat.dvd_gcd_iff ] ;
            have := hx' ( Int.natAbs_dvd_natAbs.mpr <| show ( x : ℤ ) ∣ ( h * q - e ) / s from ?_ ) ( Int.natAbs_dvd_natAbs.mpr <| show ( x : ℤ ) ∣ q from ?_ ) ; aesop;
            · exact Int.dvd_div_of_mul_dvd ( by simpa only [ mul_comm ] using! ‹ ( x : ℤ ) ∣ q ∧ ( s : ℤ ) * x ∣ h * q - e ›.2 );
            · tauto;
        -- Since $d \mid e$, we can rewrite the sum as $\sum_{d \mid e} \mu(d) \cdot \mathbf{1}_{d \mid \gcd((h * q - e) / s, q)}$ and use the fact that $\sum_{d \mid n} \mu(d) = 0$ for $n > 1$.
        have h_sum_zero : ∑ d ∈ Nat.divisors d, (ArithmeticFunction.moebius d : ℝ) = if d = 1 then 1 else 0 := by
          have h_sum_zero : ∑ d ∈ Nat.divisors d, (ArithmeticFunction.moebius d : ℝ) = (ArithmeticFunction.moebius * ArithmeticFunction.zeta) d := by
            simp +decide [ ArithmeticFunction.moebius, ArithmeticFunction.zeta ];
            rw [ Nat.sum_divisorsAntidiagonal fun x y => if y = 0 then 0 else if Squarefree x then ( -1 : ℝ ) ^ cardFactors x else 0 ];
            exact Finset.sum_congr rfl fun x hx => by rw [ if_neg ( Nat.ne_of_gt ( Nat.div_pos ( Nat.le_of_dvd ( Nat.pos_of_ne_zero ( by aesop ) ) ( Nat.dvd_of_mem_divisors hx ) ) ( Nat.pos_of_mem_divisors hx ) ) ) ] ;
          convert! h_sum_zero using 1;
          erw [ ArithmeticFunction.moebius_mul_coe_zeta ] ; aesop;
        simp_all +decide [ Int.isCoprime_iff_gcd_eq_one ];
        norm_num [ Int.gcd, Int.natAbs_abs ];
      · rw [ Finset.sum_eq_zero ] ; aesop;
        intro x hx; split_ifs <;> simp_all +decide;
        exact False.elim <| hq <| dvd_of_mul_right_dvd <| by tauto;
    convert! congr_arg ( fun x : ℝ => x ) ( Finset.sum_congr rfl fun q hq => h_moebius q ) using 1;
    any_goals exact Finset.Ico ⌊A⌋ ⌈B⌉;
    · simp +zetaDelta at *;
      rw [ ← Set.ncard_coe_finset ] ; congr ; ext ; simp +decide [ Int.lt_ceil ];
      exact fun _ _ _ _ => ⟨ Int.le_of_lt_add_one <| Int.floor_lt.2 <| by norm_num; linarith, by assumption ⟩;
    · rw [ Finset.sum_comm, Finset.sum_congr rfl ];
      simp +decide [ Finset.sum_ite ];
      intro x hx he; rw [ mul_comm ] ; rw [ ← Set.ncard_coe_finset ] ; congr; ext; simp +decide [ Int.lt_ceil ] ;
      exact fun _ _ _ _ => ⟨ Int.le_of_lt_add_one <| Int.floor_lt.2 <| by norm_num; linarith, by linarith ⟩;
  -- By Nd_count_bound, we have $|N_d - (B-A)/(s*d)| \le 1$ for each $d \mid e$.
  have h_bound : ∀ d ∈ e.divisors, |((Set.ncard {q : ℤ | A < q ∧ q < B ∧ (d : ℤ) ∣ q ∧ ((s * d : ℕ) : ℤ) ∣ (h * q - e)}) : ℝ) - (B - A) / (s * d)| ≤ 1 := by
    intro d hd;
    convert! Nd_count_bound d s ( Nat.pos_of_mem_divisors hd ) hs h hcop e ( Int.natCast_dvd_natCast.mpr ( Nat.dvd_of_mem_divisors hd ) ) A B hAB using 1;
    norm_cast;
  -- Applying the bound from `h_bound` to each term in the sum, we get:
  have h_sum_bound : |∑ d ∈ e.divisors, (ArithmeticFunction.moebius d : ℝ) * ((Set.ncard {q : ℤ | A < q ∧ q < B ∧ (d : ℤ) ∣ q ∧ ((s * d : ℕ) : ℤ) ∣ (h * q - e)}) : ℝ) - ∑ d ∈ e.divisors, (ArithmeticFunction.moebius d : ℝ) * ((B - A) / (s * d))| ≤ (e.divisors.card : ℝ) := by
    have h_sum_bound : ∀ d ∈ e.divisors, |(ArithmeticFunction.moebius d : ℝ) * ((Set.ncard {q : ℤ | A < q ∧ q < B ∧ (d : ℤ) ∣ q ∧ ((s * d : ℕ) : ℤ) ∣ (h * q - e)}) : ℝ) - (ArithmeticFunction.moebius d : ℝ) * ((B - A) / (s * d))| ≤ 1 := by
      intro d hd; specialize h_bound d hd; simp_all +decide [ ← mul_sub, abs_mul ] ;
      exact le_trans ( mul_le_of_le_one_left ( abs_nonneg _ ) ( by exact_mod_cast ArithmeticFunction.abs_moebius_le_one ) ) h_bound;
    simpa only [ ← Finset.sum_sub_distrib ] using! le_trans ( Finset.abs_sum_le_sum_abs _ _ ) ( le_trans ( Finset.sum_le_sum h_sum_bound ) ( by norm_num ) );
  -- By moebius_div_sum_eq_totient_div, we have $\sum_{d \mid e} \mu(d) \cdot \frac{1}{d} = \frac{\phi(e)}{e}$.
  have h_identity : ∑ d ∈ e.divisors, (ArithmeticFunction.moebius d : ℝ) * (1 / (d : ℝ)) = (Nat.totient e : ℝ) / e := by
    convert! moebius_div_sum_eq_totient_div e he using 1;
    exact Finset.sum_congr rfl fun _ _ => by ring;
  -- Substitute the identity into the sum.
  have h_substitute : ∑ d ∈ e.divisors, (ArithmeticFunction.moebius d : ℝ) * ((B - A) / (s * d)) = (Nat.totient e : ℝ) / e * (B - A) / s := by
    rw [ ← h_identity ] ; rw [ Finset.sum_mul _ _ _ ] ; rw [ Finset.sum_div ] ; congr ; ext ; ring;
  linarith [ abs_le.mp h_sum_bound ]

/-
The set of order-`n` Farey fractions is finite.
-/
theorem farey_finite (n : ℕ) : {q : ℚ | IsFarey n q}.Finite := by
  refine' Set.Finite.subset ( Set.toFinite ( Set.image ( fun p : ℤ × ℕ => ( p.1 : ℚ ) / p.2 ) ( Set.Icc ( -n : ℤ ) n ×ˢ Set.Icc ( 1 : ℕ ) n ) ) ) fun q hq => _;
  use (q.num, q.den);
  simp_all +decide [ IsFarey ];
  exact ⟨ ⟨ ⟨ by linarith [ q.num_nonneg.mpr hq.1 ], q.pos ⟩, by linarith [ show q.num ≤ q.den from by simpa [ Rat.le_iff ] using! hq.2.1 ] ⟩, q.num_div_den ⟩

/-- The set of order-`n` Farey fractions strictly between `x` and `y` is finite. -/
theorem fareyBetween_finite (n : ℕ) (x y : ℚ) :
    {q : ℚ | IsFarey n q ∧ x < q ∧ q < y}.Finite := by
  apply (farey_finite n).subset
  intro q hq; exact hq.1

/-- `betweenCount` is monotone in the right endpoint: shrinking `y` cannot increase the count. -/
theorem betweenCount_mono_right (n : ℕ) (x : ℚ) {y y' : ℚ} (h : y' ≤ y) :
    betweenCount n x y' ≤ betweenCount n x y := by
  apply Set.ncard_le_ncard _ (fareyBetween_finite n x y)
  intro q hq
  exact ⟨hq.1, hq.2.1, lt_of_lt_of_le hq.2.2 h⟩

/-- The right endpoint of the elementary interval `I_{a,b} = (a/b, (a+1)/(b-1))`,
where `a = x.num`, `b = x.den`. -/
noncomputable def elemR (x : ℚ) : ℚ :=
  ((x.num + 1 : ℤ) : ℚ) / (((x.den : ℤ) - 1 : ℤ) : ℚ)

/-
For a badly ordered pair `x = a/b < y = c/d` we have `(a+1)/(b-1) ≤ y`.
-/
theorem elemR_le {n : ℕ} {x y : ℚ} (h : BadlyOrdered n x y) : elemR x ≤ y := by
  obtain ⟨ hx₁, hx₂, hx₃, hx₄, hx₅ ⟩ := h;
  rw [ elemR, div_le_iff₀ ];
  · rw [ ← Rat.num_div_den y ];
    rw [ div_mul_eq_mul_div, le_div_iff₀ ] <;> norm_cast;
    · rw [ Int.subNatNat_eq_coe ] ; push_cast ; nlinarith [ show x.num ≥ 0 from Rat.num_nonneg.mpr hx₁.1, show y.num ≤ y.den from by simpa [ Rat.le_iff ] using! hx₂.2.1 ];
    · exact y.pos;
  · simp +zetaDelta at *;
    linarith [ y.pos ]

/-- Every badly ordered pair contains the elementary interval `I_{a,b}`, so its
  Farey count is at least that of the elementary interval. -/
theorem betweenCount_ge_elementary {n : ℕ} {x y : ℚ} (h : BadlyOrdered n x y) :
    betweenCount n x (elemR x) ≤ betweenCount n x y :=
  betweenCount_mono_right n x (elemR_le h)

/-- The mediant `(a+c)/(b+d)` of two rationals `x = a/b`, `y = c/d`. -/
noncomputable def mediant (x y : ℚ) : ℚ :=
  ((x.num + y.num : ℤ) : ℚ) / ((x.den + y.den : ℕ) : ℚ)

/-
The mediant is strictly greater than the smaller fraction.
-/
theorem lt_mediant {x y : ℚ} (hxy : x < y) : x < mediant x y := by
  rw [ mediant ];
  rw [ lt_div_iff₀ ( by positivity ) ];
  simp +decide [ mul_add ];
  rw [ ← Rat.mul_den_eq_num ];
  exact mul_lt_mul_of_pos_right hxy ( Nat.cast_pos.mpr y.pos )

/-
The mediant is strictly less than the larger fraction.
-/
theorem mediant_lt {x y : ℚ} (hxy : x < y) : mediant x y < y := by
  unfold mediant;
  rw [ div_lt_iff₀ ] <;> norm_cast <;> norm_num;
  · rw [ ← Rat.mul_den_eq_num, ← Rat.mul_den_eq_num ];
    nlinarith [ show ( x.den : ℚ ) > 0 by exact Nat.cast_pos.mpr x.pos ];
  · exact Or.inl x.pos

/-
The denominator of the mediant is at most the sum of the denominators.
-/
theorem mediant_den_le (x y : ℚ) : (mediant x y).den ≤ x.den + y.den := by
  unfold mediant;
  rw [ div_eq_mul_inv, Rat.mul_den ] ; norm_num;
  norm_cast ; norm_num;
  exact Nat.div_le_self _ _ |> le_trans <| by norm_cast;

/-
The mediant of two nonnegative fractions is nonnegative.
-/
theorem mediant_nonneg {x y : ℚ} (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 ≤ mediant x y := by
  exact div_nonneg ( mod_cast add_nonneg ( Rat.num_nonneg.mpr hx ) ( Rat.num_nonneg.mpr hy ) ) ( Nat.cast_nonneg _ )

/-
The mediant of two fractions `≤ 1` is `≤ 1`.
-/
theorem mediant_le_one {x y : ℚ} (hx : x ≤ 1) (hy : y ≤ 1) : mediant x y ≤ 1 := by
  apply div_le_one_of_le₀;
  · have := Rat.num_div_den x; ( have := Rat.num_div_den y; simp_all +decide [ Rat.le_iff ] );
    norm_cast at *;
    erw [ Rat.num_natCast ] ; norm_num ; linarith;
  · positivity

/-
If `x, y` are consecutive Farey fractions of order `Q`, then `x.den + y.den > Q`.
-/
theorem farey_neighbor_den_sum {Q : ℕ} {x y : ℚ}
    (hx : IsFarey Q x) (hy : IsFarey Q y) (hxy : x < y)
    (hgap : ∀ z : ℚ, IsFarey Q z → x < z → z < y → False) :
    Q < x.den + y.den := by
  -- Assume for contradiction that $x.den + y.den \leq Q$.
  by_contra h_contra;
  exact hgap ( mediant x y ) ⟨ mediant_nonneg hx.1 hy.1, mediant_le_one hx.2.1 hy.2.1, mediant_den_le x y |> le_trans <| mod_cast by linarith ⟩ ( lt_mediant hxy ) ( mediant_lt hxy )

/-
If `x < y` are consecutive Farey fractions of order `Q`, then
`x.den · y.num - x.num · y.den = 1`.
-/
theorem farey_neighbor_det {Q : ℕ} {x y : ℚ}
    (hx : IsFarey Q x) (hy : IsFarey Q y) (hxy : x < y)
    (hgap : ∀ z : ℚ, IsFarey Q z → x < z → z < y → False) :
    (x.den : ℤ) * y.num - x.num * (y.den : ℤ) = 1 := by
  contrapose! hgap;
  -- Let $D = x.den \cdot y.num - x.num \cdot y.den$. Since $D \geq 2$, we can find integers $p$ and $q$ such that $s \cdot p - h \cdot q = 1$ and $0 \leq A < D$.
  obtain ⟨p, q, hpq⟩ : ∃ p q : ℤ, (x.den : ℤ) * p - x.num * q = 1 ∧ 0 ≤ y.num * q - y.den * p ∧ y.num * q - y.den * p < x.den * y.num - x.num * y.den := by
    obtain ⟨p, q, hpq⟩ : ∃ p q : ℤ, (x.den : ℤ) * p - x.num * q = 1 := by
      have := Int.gcd_eq_gcd_ab x.den x.num;
      exact ⟨ Int.gcdA x.den x.num, -Int.gcdB x.den x.num, by linarith [ show Int.gcd x.den x.num = 1 from x.reduced.symm ] ⟩;
    -- Choose $t$ such that $0 \leq A < D$.
    obtain ⟨t, ht⟩ : ∃ t : ℤ, 0 ≤ y.num * (q + t * x.den) - y.den * (p + t * x.num) ∧ y.num * (q + t * x.den) - y.den * (p + t * x.num) < x.den * y.num - x.num * y.den := by
      have h_det_pos : 0 < x.den * y.num - x.num * y.den := by
        rw [ Rat.lt_iff ] at hxy;
        grind +splitIndPred;
      exact ⟨ - ( ( y.num * q - y.den * p ) / ( x.den * y.num - x.num * y.den ) ), by linarith [ Int.mul_ediv_add_emod ( y.num * q - y.den * p ) ( x.den * y.num - x.num * y.den ), Int.emod_nonneg ( y.num * q - y.den * p ) h_det_pos.ne' ], by linarith [ Int.mul_ediv_add_emod ( y.num * q - y.den * p ) ( x.den * y.num - x.num * y.den ), Int.emod_lt_of_pos ( y.num * q - y.den * p ) h_det_pos ] ⟩;
    exact ⟨ p + t * x.num, q + t * x.den, by linear_combination hpq, by linarith, by linarith ⟩;
  refine' ⟨ p / q, _, _, _, trivial ⟩;
  · refine' ⟨ _, _, _ ⟩;
    · refine' div_nonneg _ _ <;> norm_cast;
      · nlinarith [ hx.1, hx.2.1, hy.1, hy.2.1, Rat.num_nonneg.mpr hx.1, Rat.num_nonneg.mpr hy.1, Rat.den_pos x, Rat.den_pos y ];
      · nlinarith [ hx.1, hx.2.1, hy.1, hy.2.1, x.num_nonneg.mpr hx.1, y.num_nonneg.mpr hy.1 ];
    · rw [ div_le_iff₀ ] <;> norm_cast;
      · nlinarith [ show x.num ≤ x.den from by { have := hx.1; have := hx.2.1; rw [ Rat.le_iff ] at *; norm_num at *; linarith }, show y.num ≤ y.den from by { have := hy.1; have := hy.2.1; rw [ Rat.le_iff ] at *; norm_num at *; linarith } ];
      · nlinarith [ hx.1, hx.2, hy.1, hy.2, show ( x.den : ℤ ) > 0 from Nat.cast_pos.mpr x.pos, show ( y.den : ℤ ) > 0 from Nat.cast_pos.mpr y.pos ];
    · -- Since $q \leq Q$, we have $(p / q).den \leq Q$.
      have hq_le_Q : q.natAbs ≤ Q := by
        cases abs_cases q <;> cases max_cases x.den y.den <;> nlinarith [ hx.2.1, hy.2.1, hx.2.2, hy.2.2, show ( x.num : ℤ ) * y.den < x.den * y.num from by rw [ ← @Int.cast_lt ℚ ] ; push_cast; rw [ ← Rat.num_div_den x, ← Rat.num_div_den y ] at hxy; rw [ div_lt_div_iff₀ ] at hxy <;> norm_cast at * <;> linarith [ x.pos, y.pos ] ];
      rw [ div_eq_mul_inv ];
      rw [ Rat.mul_den ] ; norm_num;
      split_ifs <;> simp_all +decide [ Int.natAbs_mul, Int.natAbs_sign ];
      · linarith [ hx.2.2, hy.2.2, x.pos, y.pos ];
      · exact le_trans ( Nat.div_le_self _ _ ) hq_le_Q;
  · rw [ Rat.lt_iff ] at *;
    rw [ Rat.num_div_eq_of_coprime, Rat.den_div_eq_of_coprime ];
    · linarith;
    · nlinarith [ x.pos, y.pos ];
    · exact Int.isCoprime_iff_nat_coprime.mp ( by exact ⟨ x.den, -x.num, by linarith ⟩ );
    · nlinarith [ x.pos, y.pos ];
    · exact Int.isCoprime_iff_nat_coprime.mp ( by exact ⟨ x.den, -x.num, by linarith ⟩ );
  · rw [ div_lt_iff₀ ];
    · rw [ ← Rat.num_div_den y ];
      rw [ div_mul_eq_mul_div, lt_div_iff₀ ] <;> norm_cast;
      · by_cases h_eq : y.num * q - y.den * p = 0;
        · have h_contra : x.den * y.num - x.num * y.den ∣ y.den := by
            exact ⟨ q, by nlinarith ⟩;
          have h_contra : x.den * y.num - x.num * y.den ∣ 1 := by
            have h_contra : Int.gcd (x.den * y.num - x.num * y.den) y.den = 1 := by
              have h_coprime : Int.gcd (x.num : ℤ) x.den = 1 ∧ Int.gcd (y.num : ℤ) y.den = 1 := by
                exact ⟨ x.reduced, y.reduced ⟩;
              simp_all +decide [ Int.gcd_eq_natAbs ];
              refine' Nat.Coprime.symm <| Nat.coprime_of_dvd' _;
              intro k hk hk₁ hk₂; have := Nat.dvd_gcd ( show k ∣ y.num.natAbs from ?_ ) hk₁; simp_all +decide [ Nat.Coprime, Nat.Coprime.gcd_eq_one ] ;
              rw [ ← Int.natCast_dvd ] at *;
              haveI := Fact.mk hk; simp_all +decide [ ← ZMod.intCast_zmod_eq_zero_iff_dvd ] ;
              replace hpq := congr_arg ( ( ↑ ) : ℤ → ZMod k ) hpq.1 ; simp_all +decide;
              replace h_eq := congr_arg ( ( ↑ ) : ℤ → ZMod k ) h_eq ; simp_all +decide;
              grind;
            exact Int.dvd_coe_gcd ( dvd_refl _ ) ‹_› |> fun h => h.trans ( by simp +decide [ h_contra ] );
          exact False.elim <| hgap <| by linarith [ Int.le_of_dvd ( by linarith ) h_contra ] ;
        · grind;
      · exact y.pos;
    · norm_num +zetaDelta at *;
      nlinarith [ hx.1, hx.2.1, hy.1, hy.2.1, Rat.num_nonneg.mpr hx.1, Rat.num_nonneg.mpr hy.1, Rat.den_pos x, Rat.den_pos y ]

/-
If no order-`Q` Farey fraction lies strictly inside `(x, w)` (with
`0 ≤ x < w ≤ 1`, `Q ≥ 1`), then there are consecutive order-`Q` Farey fractions
`gL ≤ x < w ≤ gR`.
-/
theorem farey_gap_between (Q : ℕ) (hQ : 1 ≤ Q) (x w : ℚ) (hx0 : 0 ≤ x) (hw1 : w ≤ 1)
    (hxw : x < w) (hno : ∀ f : ℚ, IsFarey Q f → x < f → f < w → False) :
    ∃ gL gR : ℚ, IsFarey Q gL ∧ IsFarey Q gR ∧ gL ≤ x ∧ w ≤ gR ∧ gL < gR ∧
      (∀ f : ℚ, IsFarey Q f → gL < f → f < gR → False) := by
  -- The set `F := {f : ℚ | IsFarey Q f}` is finite (`farey_finite Q`).
  have h_finite : Set.Finite {f : ℚ | IsFarey Q f} := by
    refine Set.Finite.subset ( Set.toFinite ( Finset.image ( fun p : ℤ × ℕ => ( p.1 : ℚ ) / p.2 ) ( Finset.Icc ( -Q : ℤ ) Q ×ˢ Finset.Icc 1 Q ) ) ) ?_;
    intro f hf; obtain ⟨ hf₀, hf₁, hf₂ ⟩ := hf; simp_all +decide [ IsFarey ] ;
    use f.num, f.den;
    exact ⟨ ⟨ ⟨ by linarith [ show ( f.num : ℤ ) ≥ 0 by exact_mod_cast Rat.num_nonneg.mpr hf₀ ], by linarith [ f.pos ] ⟩, by linarith [ show ( f.num : ℤ ) ≤ Q by exact_mod_cast ( by nlinarith [ show ( f.num : ℚ ) ≤ f.den by exact_mod_cast ( by nlinarith [ Rat.num_div_den f, mul_div_cancel₀ ( f.num : ℚ ) ( Nat.cast_ne_zero.mpr f.pos.ne' ) ] : ( f.num : ℚ ) ≤ f.den ), ( by norm_cast : ( f.den : ℚ ) ≤ Q ) ] : ( f.num : ℚ ) ≤ Q ) ], hf₂ ⟩, f.num_div_den ⟩;
  -- Let `gL := SL.max'` (greatest element `≤ x`) and `gR := SR.min'` (least element `≥ w`).
  obtain ⟨gL, hgL⟩ : ∃ gL : ℚ, gL ∈ {f : ℚ | IsFarey Q f} ∧ gL ≤ x ∧ ∀ f ∈ {f : ℚ | IsFarey Q f}, f ≤ x → f ≤ gL := by
    obtain ⟨gL, hgL⟩ : ∃ gL ∈ {f : ℚ | IsFarey Q f} ∩ Set.Iic x, ∀ f ∈ {f : ℚ | IsFarey Q f} ∩ Set.Iic x, f ≤ gL := by
      apply_rules [ Set.exists_max_image ];
      · exact h_finite.inter_of_left _;
      · exact ⟨ 0, ⟨ ⟨ by norm_num, by norm_num, by norm_num; linarith ⟩, hx0 ⟩ ⟩;
    exact ⟨ gL, hgL.1.1, hgL.1.2, fun f hf hf' => hgL.2 f ⟨ hf, hf' ⟩ ⟩
  obtain ⟨gR, hgR⟩ : ∃ gR : ℚ, gR ∈ {f : ℚ | IsFarey Q f} ∧ w ≤ gR ∧ ∀ f ∈ {f : ℚ | IsFarey Q f}, w ≤ f → gR ≤ f := by
    obtain ⟨gR, hgR⟩ : ∃ gR : ℚ, gR ∈ {f : ℚ | IsFarey Q f} ∧ w ≤ gR := by
      exact ⟨ 1, ⟨ by norm_num, by norm_num, by norm_num; linarith ⟩, hw1 ⟩;
    exact ⟨ Finset.min' ( h_finite.toFinset.filter fun f => w ≤ f ) ⟨ gR, by aesop ⟩, by simpa using! Finset.min'_mem ( h_finite.toFinset.filter fun f => w ≤ f ) ⟨ gR, by aesop ⟩, by simp, fun f hf hf' => Finset.min'_le _ _ <| by aesop ⟩;
  grind

/-- An `O(1)` upper bound and an `o(n)` lower bound imply `f(n)/n → 1/4`. -/
theorem erdos_1005_of_bounds
    (hU : ∃ C : ℝ, ∀ n : ℕ, (fVal n : ℝ) ≤ (n : ℝ) / 4 + C)
    (hL : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, (1 / 4 - ε) * (n : ℝ) ≤ (fVal n : ℝ)) :
    Tendsto (fun n : ℕ => (fVal n : ℝ) / n) atTop (nhds (1 / 4)) := by
  obtain ⟨C, hC⟩ := hU
  have hC' : ∀ n : ℕ, (fVal n : ℝ) ≤ (1 / 4 : ℝ) * n + C := by
    intro n; have := hC n; rw [show (1/4 : ℝ) * n = (n : ℝ) / 4 by ring]; linarith
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hCdiv : Tendsto (fun n : ℕ => |C| / (n : ℝ)) atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat |C|
  have h1 : ∀ᶠ n : ℕ in atTop, |C| / (n : ℝ) < ε / 2 := by
    have := (hCdiv.eventually (gt_mem_nhds (by positivity : (0:ℝ) < ε/2)))
    simpa using! this
  have h2 : ∀ᶠ n : ℕ in atTop, (1 / 4 - ε/2) * (n : ℝ) ≤ (fVal n : ℝ) :=
    hL (ε/2) (by positivity)
  have h3 : ∀ᶠ n : ℕ in atTop, (1 : ℕ) ≤ n := eventually_atTop.2 ⟨1, fun n hn => hn⟩
  have key : ∀ᶠ n : ℕ in atTop, dist ((fVal n : ℝ) / n) (1 / 4) < ε := by
    filter_upwards [h1, h2, h3] with n hn1 hn2 hn3
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn3
    rw [Real.dist_eq, abs_lt]
    refine ⟨?_, ?_⟩
    · have : (1 / 4 - ε/2) ≤ (fVal n : ℝ) / n := by
        rw [le_div_iff₀ hnpos]; linarith [hn2]
      linarith
    · have hub : (fVal n : ℝ) ≤ (1 / 4 : ℝ) * n + |C| := by
        linarith [hC' n, le_abs_self C]
      have hcc : |C| / (n:ℝ) * n = |C| := by field_simp
      have : (fVal n : ℝ) / n ≤ 1 / 4 + |C| / n := by
        rw [div_le_iff₀ hnpos]; nlinarith [hub, hcc]
      linarith [hn1]
  exact eventually_atTop.1 key

/-- `f(n)` is a lower bound for the count over any badly ordered pair: this is the
defining `sInf` property. -/
theorem fVal_le_of_badlyOrdered {n : ℕ} {x y : ℚ} (h : BadlyOrdered n x y) :
    fVal n ≤ betweenCount n x y := by
  apply Nat.sInf_le
  exact ⟨x, y, h, rfl⟩

/-- Left endpoint of the construction: `L = (2m-1)/(4m)`. -/
noncomputable def Lf (m : ℕ) : ℚ := ((2 * (m : ℤ) - 1 : ℤ) : ℚ) / ((4 * (m : ℤ) : ℤ) : ℚ)

/-- Right endpoint of the construction: `R = 2m/(4m-1)`. -/
noncomputable def Rf (m : ℕ) : ℚ := ((2 * (m : ℤ) : ℤ) : ℚ) / ((4 * (m : ℤ) - 1 : ℤ) : ℚ)

/-- The explicit pair `L = (2m-1)/(4m)`, `R = 2m/(4m-1)` is badly ordered in `F_n`,
provided `m ≥ 1` and `4m ≤ n`. -/
theorem badlyOrdered_construction (n m : ℕ) (hm : 1 ≤ m) (hn : 4 * m ≤ n) :
    BadlyOrdered n (Lf m) (Rf m) := by
  unfold Lf Rf
  refine' ⟨ _, _, _, _, _ ⟩ <;> norm_num
  · refine' ⟨ _, _, _ ⟩
    · exact div_nonneg ( sub_nonneg_of_le ( by norm_cast; linarith ) ) ( by positivity )
    · rw [ div_le_iff₀ ] <;> linarith [ ( by norm_cast : ( 1 : ℚ ) ≤ m ) ]
    · rw [ div_eq_mul_inv ]
      norm_cast ; norm_num [ Rat.mul_den, Rat.mul_num ]
      split_ifs <;> simp_all +decide [ Int.sign_eq_one_of_pos ( by positivity : 0 < ( m : ℤ ) ) ]
      exact le_trans ( Nat.div_le_self _ _ ) ( by linarith )
  · refine' ⟨ _, _, _ ⟩
    · exact div_nonneg ( by positivity ) ( by linarith [ show ( m : ℚ ) ≥ 1 by norm_cast ] )
    · rw [ div_le_iff₀ ] <;> linarith [ show ( m : ℚ ) ≥ 1 by norm_cast ]
    · rw [ div_eq_mul_inv ]
      erw [ Rat.mul_den ] ; norm_num
      norm_cast ; simp_all +decide
      norm_num [ Int.subNatNat_eq_coe, Rat.mul_den, Rat.mul_num ]
      exact le_trans ( Nat.div_le_self _ _ ) ( by omega )
  · rw [ div_lt_div_iff₀ ] <;> nlinarith [ ( by norm_cast : ( 1 : ℚ ) ≤ m ) ]
  · have h_num_L : ((2 * m - 1 : ℚ) / (4 * m)).num = 2 * m - 1 := by
      convert! Rat.num_div_eq_of_coprime ?_ ?_
      all_goals norm_cast
      · linarith
      · rw [ Int.subNatNat_of_le ( by linarith ) ] ; norm_cast
        rcases m with ( _ | _ | m ) <;> simp_all +arith +decide [ Nat.mul_succ ]
        norm_num [ ( by ring : 4 * m + 8 = 2 * ( 2 * m + 3 ) + 2 ) ]
        grind
    have h_num_R : ((2 * m : ℚ) / (4 * m - 1)).num = 2 * m := by
      have h_coprime : Int.gcd (2 * m : ℤ) (4 * m - 1) = 1 := by
        norm_num [ show ( 4 * m - 1 : ℤ ) = 2 * m * 2 - 1 by ring ]
      convert! Rat.num_div_eq_of_coprime _ _ using 1
      rotate_left
      exacts [ 4 * m - 1, by omega, by simpa [ Int.gcd, Int.natAbs_neg ] using! h_coprime, by norm_cast ]
    linarith
  · have h_denom_L : ((2 * m - 1 : ℚ) / (4 * m)).den = 4 * m := by
      convert! Rat.den_div_eq_of_coprime _ _ using 1 <;> norm_cast
      convert! Int.natCast_inj.symm
      · positivity
      · rw [ Int.subNatNat_of_le ( by linarith ) ] ; norm_cast
        rcases m with ( _ | _ | m ) <;> simp_all +arith +decide [ Nat.mul_succ ]
        norm_num [ ( by ring : 4 * m + 8 = 2 * ( 2 * m + 3 ) + 2 ) ]
        grind
    have h_denom_R : ((2 * m : ℚ) / (4 * m - 1)).den = 4 * m - 1 := by
      convert! Rat.den_div_eq_of_coprime _ _ using 1
      rotate_left
      exact 2 * m
      exact 4 * m - 1
      · grind +splitImp
      · refine' Nat.Coprime.symm ( Nat.coprime_of_dvd' _ )
        intro k hk hk₁ hk₂; have := Int.natAbs_dvd_natAbs.mpr ( Int.dvd_sub ( Int.natCast_dvd.mpr hk₂ |> fun x => x.mul_left 2 ) ( Int.natCast_dvd.mpr hk₁ ) ) ; norm_num at this
        exact this.trans ( by ring_nf; norm_num )
      · norm_cast
        rw [ Int.subNatNat_of_le ( by linarith ) ] ; norm_cast
    omega

/-- The candidate finite set capturing every Farey fraction strictly between `L` and `R`.
The `e = den - 2·num = 1` family `a/(2a+1)` (with `a ∈ [m, 2m+1]`) is the dominant part;
the remaining `O(1)` exceptional fractions (from `e ∈ {-1,0,3}`) are listed explicitly. -/
noncomputable def Tset (m : ℕ) : Finset ℚ :=
  ((Finset.Icc (m : ℤ) (2 * m + 1)).image (fun a : ℤ => (a : ℚ) / (2 * a + 1)))
    ∪ {1 / 2, (2 * (m : ℚ) + 1) / (4 * m + 1), (2 * (m : ℚ) + 2) / (4 * m + 3), 2 / 7}

/-
The candidate set has at most `m + 6` elements.
-/
lemma Tset_card_le (m : ℕ) : (Tset m).card ≤ m + 6 := by
  refine' le_trans ( Finset.card_union_le _ _ ) _;
  refine' le_trans ( add_le_add ( Finset.card_image_le ) ( Finset.card_insert_le _ _ ) ) _ ; norm_num [ Finset.card_insert_of_notMem ] ; ring_nf ; norm_cast ; simp +arith +decide;
  grind +qlia

/-
Integer-inequality form of membership in the between-set. For `q` strictly between
`L = (2m-1)/(4m)` and `R = 2m/(4m-1)` and `q ∈ F_n`, writing `a = q.num`, `b = q.den`:
`1 ≤ a ≤ b ≤ n`, `(2m-1)·b < 4m·a` and `(4m-1)·a < 2m·b`.
-/
lemma between_ineqs {n m : ℕ} (hm : 1 ≤ m) {q : ℚ}
    (hF : IsFarey n q) (hL : Lf m < q) (hR : q < Rf m) :
    1 ≤ q.num ∧ q.num ≤ (q.den : ℤ) ∧ (q.den : ℤ) ≤ (n : ℤ) ∧
      (2 * (m : ℤ) - 1) * (q.den : ℤ) < 4 * (m : ℤ) * q.num ∧
      (4 * (m : ℤ) - 1) * q.num < 2 * (m : ℤ) * (q.den : ℤ) := by
  refine' ⟨ _, _, _, _, _ ⟩;
  · contrapose! hL; simp_all +decide [ Lf ] ;
    exact le_trans ( Rat.num_nonpos.mp ( by linarith ) ) ( by exact div_nonneg ( sub_nonneg.mpr ( by norm_cast; linarith ) ) ( by positivity ) );
  · simpa [ Rat.le_iff ] using! hF.2.1;
  · exact_mod_cast hF.2.2;
  · unfold Lf Rf at *;
    rw [ div_lt_iff₀ ] at hL <;> norm_cast at *;
    · rw [ ← Rat.num_div_den q ] at hL;
      rw [ div_mul_eq_mul_div, lt_div_iff₀ ] at hL <;> norm_cast at * ; linarith [ q.pos ];
      exact q.pos;
    · linarith;
  · have hR_cast : (q.num : ℚ) / q.den < (2 * m : ℚ) / (4 * m - 1) := by
      convert! hR using 1 <;> norm_num [ Rat.num_div_den ];
      unfold Rf; norm_num;
    rw [ div_lt_div_iff₀ ] at hR_cast <;> norm_cast at *;
    · grind;
    · exact q.pos;
    · rw [ Int.subNatNat_eq_coe ] ; norm_num ; linarith

/-
Every order-`n` Farey fraction strictly between `L` and `R` lies in the explicit
finite set `Tset m` (with `4m ≤ n ≤ 4m+3`, `m ≥ 1`).
-/
set_option maxHeartbeats 1000000 in
lemma between_mem_Tset {n m : ℕ} (hm : 1 ≤ m) (hn : n ≤ 4 * m + 3) {q : ℚ}
    (hF : IsFarey n q) (hL : Lf m < q) (hR : q < Rf m) : q ∈ Tset m := by
  obtain ⟨a, b, hab⟩ : ∃ a b : ℤ, 1 ≤ a ∧ a ≤ b ∧ b ≤ n ∧ (2 * m - 1) * b < 4 * m * a ∧ (4 * m - 1) * a < 2 * m * b ∧ q = a / b := by
    have := between_ineqs hm hF hL hR;
    exact ⟨ q.num, q.den, this.1, this.2.1, mod_cast this.2.2.1, mod_cast this.2.2.2.1, mod_cast this.2.2.2.2, q.num_div_den.symm ⟩;
  -- From the inequalities, we derive that $b = 2a + k$ for some $k \in \{-2, -1, 0, 1, 2, 3\}$.
  obtain ⟨k, hk⟩ : ∃ k : ℤ, b = 2 * a + k ∧ -2 ≤ k ∧ k ≤ 3 := by
    exact ⟨ b - 2 * a, by ring, by nlinarith, by nlinarith ⟩;
  rcases hk with ⟨ rfl, hk₁, hk₂ ⟩ ; interval_cases k <;> simp_all +decide;
  any_goals nlinarith;
  · -- From the inequalities, we derive that $a = 2m + 1$ or $a = 2m + 2$.
    have ha : a = 2 * m + 1 ∨ a = 2 * m + 2 := by
      grind +qlia;
    rcases ha with ( rfl | rfl ) <;> norm_num [ Tset ];
    · exact Or.inr <| Or.inl <| by ring;
    · grind +qlia;
  · ring_nf at *; norm_num [ show a ≠ 0 by linarith ] at *;
    rw [ mul_inv_cancel₀ ( by norm_cast; linarith ) ] ; norm_num [ Tset ];
  · exact Finset.mem_union_left _ <| Finset.mem_image.mpr ⟨ a, Finset.mem_Icc.mpr ⟨ by linarith, by linarith ⟩, rfl ⟩;
  · -- From the inequalities, we derive that $a = 2m$.
    have ha : a = 2 * m := by
      grind;
    have := hF.2.2; simp_all +decide [ IsFarey ] ;
    norm_num [ show ( 2 * ( 2 * m ) + 2 : ℚ ) = 2 * ( 2 * m + 1 ) by ring, Rat.divInt_eq_div ] at *;
    norm_num [ show ( 2 * m : ℚ ) / ( 2 * ( 2 * m + 1 ) ) = m / ( 2 * m + 1 ) by rw [ div_eq_div_iff ] <;> ring_nf <;> positivity ] at *;
    exact Finset.mem_union_left _ ( Finset.mem_image.mpr ⟨ m, Finset.mem_Icc.mpr ⟨ by linarith, by linarith ⟩, by push_cast; ring ⟩ );
  · -- From the inequalities, we derive that $a = 2$ and $m = 1$.
    have ha : a = 2 := by
      nlinarith only [ hab, hm, hn ]
    have hm : m = 1 := by
      grind +splitIndPred
    subst ha
    subst hm
    norm_num [ Tset ] at *

/-- There is an absolute constant `C₀` such that for `m = ⌊n/4⌋`, the number of
    order-`n` Farey fractions strictly between `L = (2m-1)/(4m)` and
    `R = 2m/(4m-1)` is at most `m + C₀`. -/
theorem upper_count_bound :
    ∃ C₀ : ℕ, ∀ n m : ℕ, 1 ≤ m → 4 * m ≤ n → n ≤ 4 * m + 3 →
      betweenCount n (Lf m) (Rf m) ≤ m + C₀ := by
  refine ⟨6, ?_⟩
  intro n m hm _ hn
  have hsub : {q : ℚ | IsFarey n q ∧ Lf m < q ∧ q < Rf m} ⊆ ↑(Tset m) := by
    rintro q ⟨hF, hL, hR⟩
    exact between_mem_Tset hm hn hF hL hR
  have hle : betweenCount n (Lf m) (Rf m) ≤ (Tset m).card := by
    unfold betweenCount
    rw [← Set.ncard_coe_finset (Tset m)]
    exact Set.ncard_le_ncard hsub (Tset m).finite_toSet
  exact le_trans hle (Tset_card_le m)

/-- There is an absolute constant `C` such that `f(n) ≤ n/4 + C` for all `n`. -/
theorem fVal_upper_bound : ∃ C : ℝ, ∀ n : ℕ, (fVal n : ℝ) ≤ (n : ℝ) / 4 + C := by
  obtain ⟨C₀, hC₀⟩ := upper_count_bound
  refine ⟨(C₀ : ℝ) + (fVal 0 + fVal 1 + fVal 2 + fVal 3 : ℕ), ?_⟩
  intro n
  rcases lt_or_ge n 4 with hsmall | hbig
  · -- Small cases n ∈ {0,1,2,3}: bound by the (finite) sum of those values.
    have hle : fVal n ≤ (fVal 0 + fVal 1 + fVal 2 + fVal 3 : ℕ) := by
      interval_cases n <;> omega
    have : (fVal n : ℝ) ≤ (fVal 0 + fVal 1 + fVal 2 + fVal 3 : ℕ) := by exact_mod_cast hle
    have hn0 : (0:ℝ) ≤ (n:ℝ) / 4 := by positivity
    push_cast at this ⊢
    nlinarith [this, hn0]
  · -- Main case: m = n/4 ≥ 1, 4m ≤ n ≤ 4m+3.
    set m := n / 4 with hmdef
    have hm1 : 1 ≤ m := by omega
    have hmle : 4 * m ≤ n := by omega
    have hmge : n ≤ 4 * m + 3 := by omega
    have hbad := badlyOrdered_construction n m hm1 hmle
    have h1 : fVal n ≤ betweenCount n (Lf m) (Rf m) := fVal_le_of_badlyOrdered hbad
    have h2 : betweenCount n (Lf m) (Rf m) ≤ m + C₀ := hC₀ n m hm1 hmle hmge
    have h3 : fVal n ≤ m + C₀ := le_trans h1 h2
    have h4 : (fVal n : ℝ) ≤ (m : ℝ) + C₀ := by exact_mod_cast h3
    have h5 : (m : ℝ) ≤ (n : ℝ) / 4 := by
      have : (4 * m : ℕ) ≤ n := hmle
      have : (4 : ℝ) * m ≤ n := by exact_mod_cast this
      linarith
    have h6 : (0:ℝ) ≤ (fVal 0 + fVal 1 + fVal 2 + fVal 3 : ℕ) := by positivity
    push_cast at h4 h6 ⊢
    nlinarith [h4, h5, h6]

/-- The function `S(x) = ∑_{1 ≤ e < x} (1 - e/x) · φ(e)/e`. -/
noncomputable def Sfun (x : ℝ) : ℝ :=
  ∑ e ∈ Finset.range ⌈x⌉₊, (1 - (e : ℝ) / x) * (Nat.totient e / e)

/-- The auxiliary partial sum `A_m = ∑_{e ≤ m} φ(e)/e`. -/
noncomputable def Afun (m : ℕ) : ℝ :=
  ∑ e ∈ Finset.range (m + 1), (Nat.totient e / e : ℝ)

/-- `F(x) = S(x) - x/4`. -/
noncomputable def Ffun (x : ℝ) : ℝ := Sfun x - x / 4

/-- `S(1) = 0`. -/
theorem Sfun_one : Sfun 1 = 0 := by
  unfold Sfun; norm_num

/-- `S(2) = 1/2`. -/
theorem Sfun_two : Sfun 2 = 1 / 2 := by
  unfold Sfun; norm_num [Finset.sum_range_succ]

/-
For `m ≥ 1` and `x ∈ [m, m+1]`, `S(x) = A_m - Φ(m)/x`.
-/
theorem Sfun_eq_on_Icc {m : ℕ} (hm : 1 ≤ m) {x : ℝ}
    (hx1 : (m : ℝ) ≤ x) (hx2 : x ≤ (m : ℝ) + 1) :
    Sfun x = Afun m - (Phi m : ℝ) / x := by
  -- For `x ∈ [m, m+1]` with `m ≥ 1`, the nat ceiling `⌈x⌉₊` is either `m` (only when `x = m`) or `m+1` (when `m < x ≤ m+1`).
  by_cases hx : x = m;
  · unfold Sfun Afun Phi; simp +decide [ Finset.sum_range_succ, hx ] ; ring_nf;
    simp +decide [ Finset.mul_sum _ _ _, mul_assoc, mul_comm, mul_left_comm, Finset.sum_add_distrib ];
    exact Finset.sum_congr rfl fun x hx => by by_cases h : x = 0 <;> simp +decide [ h ] ;
  · -- For `x ∈ [m, m+1]` with `m ≥ 1`, the nat ceiling `⌈x⌉₊` is `m+1`.
    have h_ceil : ⌈x⌉₊ = m + 1 := by
      exact Nat.ceil_eq_iff ( by positivity ) |>.2 ⟨ by norm_num; contrapose! hx; linarith, by norm_num; contrapose! hx; linarith ⟩;
    unfold Sfun Afun Phi;
    simp_all +decide [ sub_mul, Finset.sum_div _ _ _ ];
    exact Finset.sum_congr rfl fun i hi => by by_cases hi0 : i = 0 <;> simp +decide [ div_eq_mul_inv, mul_assoc, mul_comm, hi0 ] ;

/-
`S(m+1) - S(m) = Φ(m) / (m(m+1))` for `m ≥ 1`.
-/
theorem Sfun_int_increment {m : ℕ} (hm : 1 ≤ m) :
    Sfun (m + 1) - Sfun m = (Phi m : ℝ) / ((m : ℝ) * ((m : ℝ) + 1)) := by
  convert! congr_arg₂ ( · - · ) ( Sfun_eq_on_Icc hm ( show ( m : ℝ ) ≤ ( m + 1 : ℝ ) by linarith ) ( show ( m + 1 : ℝ ) ≤ ( m + 1 : ℝ ) by linarith ) ) ( Sfun_eq_on_Icc hm ( show ( m : ℝ ) ≤ ( m : ℝ ) by linarith ) ( show ( m : ℝ ) ≤ ( m + 1 : ℝ ) by linarith ) ) using 1;
  -- Combine and simplify the fractions on the right-hand side.
  field_simp
  ring

/-
`F` is nondecreasing at consecutive integers.
-/
theorem Ffun_int_mono {m : ℕ} (hm : 1 ≤ m) : Ffun (m : ℝ) ≤ Ffun ((m : ℝ) + 1) := by
  -- By definition of $Ffun$, we have $Ffun (m + 1) - Ffun m = (Sfun (m + 1) - Sfun m) - 1/4$.
  have h_diff : Ffun (m + 1 : ℝ) - Ffun (m : ℝ) = (Phi m : ℝ) / (m * (m + 1)) - 1 / 4 := by
    unfold Ffun; have := Sfun_int_increment hm; norm_num at *; ring_nf at *; linarith;
  -- By `four_mul_Phi_ge`, we have $m(m+1) \leq 4 \Phi(m)$.
  have h_four_mul_Phi_ge : (m : ℝ) * (m + 1) ≤ 4 * (Phi m : ℝ) := by
    exact_mod_cast four_mul_Phi_ge m;
  nlinarith [ show ( 0 : ℝ ) < m * ( m + 1 ) by positivity, div_mul_cancel₀ ( Phi m : ℝ ) ( by positivity : ( m : ℝ ) * ( m + 1 ) ≠ 0 ) ]

/-
`F` is nondecreasing along positive integers.
-/
theorem Ffun_int_mono_le {m k : ℕ} (hm : 1 ≤ m) (hmk : m ≤ k) :
    Ffun (m : ℝ) ≤ Ffun (k : ℝ) := by
  induction hmk <;> norm_num at *;
  exact le_trans ‹_› ( Ffun_int_mono <| by linarith )

/-- `F(2) = 0`. -/
theorem Ffun_two : Ffun 2 = 0 := by
  unfold Ffun; rw [Sfun_two]; norm_num

/-
`S(m) ≥ m/4` for integers `m ≥ 2`.
-/
theorem Sfun_ge_quarter {m : ℕ} (hm : 2 ≤ m) : (m : ℝ) / 4 ≤ Sfun (m : ℝ) := by
  -- By Ffun_int_mono_le applied with 2 ≤ m, Ffun 2 ≤ Ffun m. Since Ffun 2 = 0 (Ffun_two), we get 0 ≤ Ffun m = Sfun m - m/4, i.e. m/4 ≤ Sfun m.
  have h1 : 0 ≤ Ffun (m : ℝ) := by
    convert! Ffun_int_mono_le ( by norm_num : 1 ≤ 2 ) hm using 1 ; norm_num [ Ffun_two ];
  unfold Ffun at h1; linarith;

/-
Exact difference of `F` within a unit interval `[m, m+1]`.
-/
theorem Ffun_diff_on_unit {m : ℕ} (hm : 1 ≤ m) {a b : ℝ}
    (ha : (m : ℝ) ≤ a) (hab : a ≤ b) (hb : b ≤ (m : ℝ) + 1) :
    Ffun b - Ffun a = (b - a) * ((Phi m : ℝ) / (a * b) - 1 / 4) := by
  rw [ show Ffun b = Sfun b - b / 4 by rfl, show Ffun a = Sfun a - a / 4 by rfl ];
  rw [ Sfun_eq_on_Icc hm ha ( by linarith ), Sfun_eq_on_Icc hm ( by linarith ) hb ] ; ring_nf;
  by_cases ha : a = 0 <;> by_cases hb : b = 0 <;> simp_all +decide; ring_nf;
  · linarith [ ( by norm_cast : ( 1 : ℝ ) ≤ m ) ];
  · ring

/-
`F` lies above the minimum of the endpoint values on a unit interval.
-/
theorem Ffun_ge_min_on_unit {k : ℕ} (hk : 1 ≤ k) {x : ℝ}
    (hx1 : (k : ℝ) ≤ x) (hx2 : x ≤ (k : ℝ) + 1) :
    min (Ffun (k : ℝ)) (Ffun ((k : ℝ) + 1)) ≤ Ffun x := by
  have h_group : (x - k) * ((Phi k : ℝ) / (k * x) - 1 / 4) = Ffun x - Ffun k ∧ (k + 1 - x) * ((Phi k : ℝ) / (x * (k + 1)) - 1 / 4) = Ffun (k + 1) - Ffun x := by
    constructor <;> rw [ Ffun_diff_on_unit ] <;> aesop;
  by_contra h_contra; push_neg at h_contra; (
  -- From the first inequality, we have $P/(kx) < 1/4$, which implies $4P < kx$.
  have h1 : 4 * (Phi k : ℝ) < k * x := by
    have h1 : (Phi k : ℝ) / (k * x) < 1 / 4 := by
      cases lt_or_eq_of_le hx1 <;> cases lt_or_eq_of_le hx2 <;> nlinarith [ show ( k : ℝ ) ≥ 1 by norm_cast, min_le_left ( Ffun k ) ( Ffun ( k + 1 ) ), min_le_right ( Ffun k ) ( Ffun ( k + 1 ) ) ];
    rw [ div_lt_iff₀ ] at h1 <;> nlinarith [ show ( k : ℝ ) ≥ 1 by norm_cast, show ( x : ℝ ) ≥ k by exact_mod_cast hx1 ];
  by_cases hx : x = k + 1 <;> simp_all +decide [ sub_eq_iff_eq_add ];
  nlinarith [ show ( k : ℝ ) ≥ 1 by norm_cast, show ( Phi k : ℝ ) ≥ 0 by positivity, mul_div_cancel₀ ( Phi k : ℝ ) ( show ( x * ( k + 1 ) : ℝ ) ≠ 0 by exact mul_ne_zero ( by linarith [ show ( k : ℝ ) ≥ 1 by norm_cast ] ) ( by linarith [ show ( k : ℝ ) ≥ 1 by norm_cast ] ) ), mul_pos ( show ( k + 1 - x : ℝ ) > 0 by exact sub_pos.mpr ( lt_of_le_of_ne hx2 hx ) ) ( show ( x : ℝ ) > 0 by linarith [ show ( k : ℝ ) ≥ 1 by norm_cast ] ) ]);

/-
`F` is at least its value at any integer `j ≥ 1` for all larger arguments.
-/
theorem Ffun_ge_int_for_ge {j : ℕ} (hj : 1 ≤ j) {t : ℝ} (ht : (j : ℝ) ≤ t) :
    Ffun (j : ℝ) ≤ Ffun t := by
  -- Let $k = \lfloor t \rfloor$ (Nat.floor $t$). Since $t \geq j \geq 1 \geq 0$, we have $k \geq j$ and $k \geq 1$.
  set k : ℕ := Nat.floor t
  have hk1 : k ≥ j := by
    exact Nat.le_floor ht
  have hk2 : k ≥ 1 := by
    bv_omega;
  -- Also, $k \leq t$ (Nat.floor_le, $t \geq 0$) and $t \leq k+1$ (Nat.lt_floor_add_one gives $t < \lfloor t \rfloor + 1$, so $t \leq k+1$).
  have hk3 : (k : ℝ) ≤ t := by
    exact Nat.floor_le ( by linarith )
  have hk4 : t ≤ (k : ℝ) + 1 := by
    exact le_of_lt <| Nat.lt_floor_add_one t;
  convert! le_trans _ ( Ffun_ge_min_on_unit hk2 hk3 hk4 ) using 1;
  exact le_min ( Ffun_int_mono_le hj hk1 ) ( by exact_mod_cast Ffun_int_mono_le hj ( Nat.le_succ_of_le hk1 ) )

/-
`(m+1)² ≤ 4·Φ(m)` for `m ≥ 7`.
-/
set_option maxRecDepth 10000 in
theorem Phi_quad_lower {m : ℕ} (hm : 7 ≤ m) : ((m : ℝ) + 1) ^ 2 ≤ 4 * (Phi m : ℝ) := by
  -- For m ≥ 67, use the analytic chain: 2·Phi m = Pcard m + 1 (two_mul_Phi_eq, needs m ≥ 1), and m·m ≤ Pcard m + ∑_{p ≤ m prime} (m/p)^2 (Pcard_ge), with ∑_{p ≤ m prime} (1/p)^2 ≤ 97/200 (prime_recip_sq_bound).
  have h_analytic : ∀ m : ℕ, 67 ≤ m → (2 : ℝ) * Phi m ≥ (m : ℝ) ^ 2 * (103 / 200) + 1 := by
    intro m hm
    have h_two_mul_Phi_eq : (2 : ℝ) * Phi m = (Pcard m : ℝ) + 1 := by
      exact_mod_cast two_mul_Phi_eq m ( by linarith )
    have h_Pcard_ge : (m : ℝ) * m ≤ (Pcard m : ℝ) + ∑ p ∈ Finset.filter Nat.Prime (Finset.Icc 2 m), (m / p : ℝ) ^ 2 := by
      have h_Pcard_ge : (m : ℝ) * m ≤ (Pcard m : ℝ) + ∑ p ∈ Finset.filter Nat.Prime (Finset.Icc 2 m), (m / p : ℕ) ^ 2 := by
        exact_mod_cast Pcard_ge m;
      refine le_trans h_Pcard_ge ?_;
      norm_num [ Finset.sum_div _ _ _ ];
      exact Finset.sum_le_sum fun x hx => by rw [ div_pow, le_div_iff₀ ] <;> norm_cast <;> nlinarith [ Finset.mem_Icc.mp ( Finset.mem_filter.mp hx |>.1 ), Nat.div_mul_le_self m x, Nat.div_add_mod m x, Nat.mod_lt m ( by linarith [ Finset.mem_Icc.mp ( Finset.mem_filter.mp hx |>.1 ) ] : 0 < x ) ] ;
    have h_prime_recip_sq_bound : ∑ p ∈ Finset.filter Nat.Prime (Finset.Icc 2 m), (1 / (p : ℝ)) ^ 2 ≤ 97 / 200 := by
      convert! prime_recip_sq_bound m using 1
    have h_sum_recip_sq_bound : ∑ p ∈ Finset.filter Nat.Prime (Finset.Icc 2 m), (m / p : ℝ) ^ 2 ≤ (m : ℝ) ^ 2 * (97 / 200) := by
      convert! mul_le_mul_of_nonneg_left h_prime_recip_sq_bound ( sq_nonneg ( m : ℝ ) ) using 1 ; norm_num [ div_eq_mul_inv, mul_pow, Finset.mul_sum _ _ _ ]
    have h_Pcard_ge_final : (Pcard m : ℝ) ≥ (m : ℝ) ^ 2 * (103 / 200) := by
      linarith
    linarith [h_two_mul_Phi_eq, h_Pcard_ge_final];
  by_cases hm67 : m ≥ 67;
  · nlinarith [ show ( m : ℝ ) ≥ 67 by norm_cast, h_analytic m hm67 ];
  · interval_cases m <;> exact mod_cast by decide

/-
`F` is nondecreasing on a unit interval `[m, m+1]` for `m ≥ 7`.
-/
theorem Ffun_mono_on_unit_ge7 {m : ℕ} (hm : 7 ≤ m) {a b : ℝ}
    (ha : (m : ℝ) ≤ a) (hab : a ≤ b) (hb : b ≤ (m : ℝ) + 1) : Ffun a ≤ Ffun b := by
  -- By Ffun_diff_on_unit (m ≥ 7 ≥ 1), Ffun b - Ffun a = (b - a)·((Phi m)/(a·b) - 1/4).
  have h_diff : Ffun b - Ffun a = (b - a) * ((Phi m : ℝ) / (a * b) - 1 / 4) := by
    convert! Ffun_diff_on_unit ( by linarith : 1 ≤ m ) ha hab hb using 1;
  -- By Phi_quad_lower, (m+1)^2 ≤ 4·(Phi m). Hence a·b ≤ 4·Phi m.
  have h_ab_le : a * b ≤ 4 * (Phi m : ℝ) := by
    exact le_trans ( by nlinarith [ ( by norm_cast : ( 7 :ℝ ) ≤ m ) ] ) ( Phi_quad_lower hm );
  nlinarith [ show ( 0 : ℝ ) < a * b by exact mul_pos ( lt_of_lt_of_le ( by positivity ) ha ) ( lt_of_lt_of_le ( lt_of_lt_of_le ( by positivity ) ha ) hab ), div_mul_cancel₀ ( Phi m : ℝ ) ( show ( a * b ) ≠ 0 by exact ne_of_gt ( mul_pos ( lt_of_lt_of_le ( by positivity ) ha ) ( lt_of_lt_of_le ( lt_of_lt_of_le ( by positivity ) ha ) hab ) ) ) ]

/-
`F(x) ≤ F(m+2)` for `x ∈ [m, m+1]`.
-/
theorem Ffun_unit_le_succ2 {m : ℕ} {x : ℝ}
    (hx1 : (m : ℝ) ≤ x) (hx2 : x ≤ (m : ℝ) + 1) :
    Ffun x ≤ Ffun ((m : ℝ) + 2) := by
  by_cases hm : m = 0;
  · -- Since $m = 0$, we have $x \in [0, 1]$. By definition of $Sfun$, we know that $Sfun(x) = 0$ for $x \in [0, 1]$.
    have h_Sfun_zero : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → Sfun x = 0 := by
      unfold Sfun;
      intro x hx₁ hx₂; rcases eq_or_lt_of_le hx₁ with rfl | hx₁' <;> norm_num [ Finset.sum_range_succ' ] ;
      rw [ show ⌈x⌉₊ = 1 by exact Nat.ceil_eq_iff ( by positivity ) |>.2 ⟨ by norm_num; linarith, by norm_num; linarith ⟩ ] ; norm_num;
    simp_all +decide [ Ffun ];
    rw [ Sfun_two ] ; linarith;
  · -- For $1 \leq m \leq 6$, we can check each case individually.
    by_cases hm_cases : m ≤ 6;
    · rw [ Ffun, Ffun, Sfun_eq_on_Icc, Sfun ];
      any_goals assumption;
      · interval_cases m <;> norm_num [ Finset.sum_range_succ, Nat.totient_prime, Phi, Afun ] at *;
        all_goals norm_num [ show Nat.totient 4 = 2 by rfl, show Nat.totient 6 = 2 by rfl ] at *; ring_nf at *; nlinarith [ inv_mul_cancel₀ ( by linarith : x ≠ 0 ) ] ;
      · exact Nat.pos_of_ne_zero hm;
    · -- For $m \geq 7$, we can use the fact that $F$ is nondecreasing on $[m, m+1]$.
      have h_mono : Ffun x ≤ Ffun ((m : ℝ) + 1) := by
        apply Ffun_mono_on_unit_ge7 (by linarith) hx1 (by linarith) (by linarith);
      exact le_trans h_mono ( mod_cast Ffun_int_mono ( by linarith ) )

/-
`F(x) ≤ F(x+1)` for all `x ≥ 1`.
-/
theorem Ffun_step_le {x : ℝ} (hx : 1 ≤ x) : Ffun x ≤ Ffun (x + 1) := by
  by_cases hm : Nat.floor x ≥ 7;
  · -- By Ffun_mono_on_unit_ge7 (index m) with a=x, b=(m:ℝ)+1: Ffun x ≤ Ffun ((m:ℝ)+1).
    have h_mono1 : Ffun x ≤ Ffun ((Nat.floor x : ℝ) + 1) := by
      apply Ffun_mono_on_unit_ge7 hm (Nat.floor_le (by linarith)) (by linarith [Nat.lt_floor_add_one x]) (by linarith [Nat.lt_floor_add_one x]);
    refine le_trans h_mono1 ?_;
    convert! Ffun_ge_int_for_ge _ _;
    rotate_left;
    exacts [ ⌊x⌋₊ + 1, by linarith, by push_cast; linarith [ Nat.floor_le ( by linarith : 0 ≤ x ) ], by push_cast; ring ];
  · -- Since $m < 7$, we have $1 \leq m \leq 6$. We can split into subcases based on the value of $m$.
    have hm_cases : ∃ m : ℕ, m ∈ [1, 2, 3, 4, 5, 6] ∧ m ≤ x ∧ x < m + 1 := by
      use Nat.floor x;
      exact ⟨ by have := Nat.floor_pos.mpr hx; interval_cases ⌊x⌋₊ <;> trivial, Nat.floor_le <| by positivity, Nat.lt_floor_add_one _ ⟩;
    obtain ⟨ m, hm₁, hm₂, hm₃ ⟩ := hm_cases;
    -- By definition of $Ffun$, we have $Ffun x = Afun m - (Phi m : ℝ) / x - x / 4$ and $Ffun (x + 1) = Afun (m + 1) - (Phi (m + 1) : ℝ) / (x + 1) - (x + 1) / 4$.
    have hFfun_def : Ffun x = Afun m - (Phi m : ℝ) / x - x / 4 ∧ Ffun (x + 1) = Afun (m + 1) - (Phi (m + 1) : ℝ) / (x + 1) - (x + 1) / 4 := by
      have hFfun_def : Sfun x = Afun m - (Phi m : ℝ) / x ∧ Sfun (x + 1) = Afun (m + 1) - (Phi (m + 1) : ℝ) / (x + 1) := by
        apply And.intro;
        · apply Sfun_eq_on_Icc;
          · fin_cases hm₁ <;> trivial;
          · linarith;
          · linarith;
        · apply Sfun_eq_on_Icc;
          · linarith;
          · norm_num; linarith;
          · norm_num; linarith;
      exact ⟨ by rw [ ← hFfun_def.1, Ffun ], by rw [ ← hFfun_def.2, Ffun ] ⟩;
    simp_all +decide [ Afun, Phi ];
    rcases hm₁ with ( rfl | rfl | rfl | rfl | rfl | rfl ) <;> norm_num [ Finset.sum_range_succ, Nat.totient_prime ] at *;
    all_goals norm_num [ show Nat.totient 4 = 2 by rfl, show Nat.totient 6 = 2 by rfl ] at *;
    all_goals field_simp;
    all_goals nlinarith [ sq_nonneg ( x - 2 ) ]

/-
`F` lies above the minimum of the values at any two points of a unit interval.
-/
theorem Ffun_ge_min_on_unit_gen {k : ℕ} (hk : 1 ≤ k) {a z b : ℝ}
    (ha : (k : ℝ) ≤ a) (haz : a ≤ z) (hzb : z ≤ b) (hb : b ≤ (k : ℝ) + 1) :
    min (Ffun a) (Ffun b) ≤ Ffun z := by
  by_contra h_contra;
  -- From the assumption, we have $Ffun a > Ffun z$ and $Ffun b > Ffun z$.
  have hFfun_a : Ffun a > Ffun z := by
    exact lt_of_not_ge fun h => h_contra <| le_trans ( min_le_left _ _ ) h
  have hFfun_b : Ffun b > Ffun z := by
    grind;
  -- From the assumption, we have $4 \cdot \Phi(k) < a \cdot z$ and $4 \cdot \Phi(k) > z \cdot b$.
  have h_bounds : 4 * (Phi k : ℝ) < a * z ∧ 4 * (Phi k : ℝ) > z * b := by
    have h_bounds : (Phi k : ℝ) / (a * z) - 1 / 4 < 0 ∧ (Phi k : ℝ) / (z * b) - 1 / 4 > 0 := by
      constructor;
      · have hFfun_diff : Ffun z - Ffun a = (z - a) * ((Phi k : ℝ) / (a * z) - 1 / 4) := by
          convert! Ffun_diff_on_unit hk ( by linarith : ( k : ℝ ) ≤ a ) ( by linarith : a ≤ z ) ( by linarith : z ≤ ( k : ℝ ) + 1 ) using 1;
        nlinarith [ show ( k : ℝ ) ≥ 1 by norm_cast, show ( z : ℝ ) ≥ a by linarith ];
      · have := Ffun_diff_on_unit hk ( show ( k : ℝ ) ≤ z by linarith ) ( show z ≤ b by linarith ) ( show b ≤ ( k : ℝ ) + 1 by linarith ) ; nlinarith [ show 0 < b - z by exact sub_pos.mpr ( lt_of_le_of_ne hzb ( by rintro rfl; norm_num at * ) ) ] ;
    constructor <;> nlinarith [ show 0 < a * z by exact mul_pos ( by linarith [ show ( k : ℝ ) ≥ 1 by norm_cast ] ) ( by linarith [ show ( k : ℝ ) ≥ 1 by norm_cast ] ), show 0 < z * b by exact mul_pos ( by linarith [ show ( k : ℝ ) ≥ 1 by norm_cast ] ) ( by linarith [ show ( k : ℝ ) ≥ 1 by norm_cast ] ), div_mul_cancel₀ ( Phi k : ℝ ) ( show a * z ≠ 0 by exact ne_of_gt ( mul_pos ( by linarith [ show ( k : ℝ ) ≥ 1 by norm_cast ] ) ( by linarith [ show ( k : ℝ ) ≥ 1 by norm_cast ] ) ) ), div_mul_cancel₀ ( Phi k : ℝ ) ( show z * b ≠ 0 by exact ne_of_gt ( mul_pos ( by linarith [ show ( k : ℝ ) ≥ 1 by norm_cast ] ) ( by linarith [ show ( k : ℝ ) ≥ 1 by norm_cast ] ) ) ) ];
  nlinarith [ show ( k : ℝ ) ≥ 1 by norm_cast, show ( Phi k : ℝ ) ≥ 0 by positivity ]

/-
Real increment (case `x ≥ 1, y ≥ 1`).
-/
theorem Sfun_increment_ge_one {x y : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y) :
    y / 4 ≤ Sfun (x + y) - Sfun x := by
  -- Let $m = \lfloor x \rfloor$.
  set m := Nat.floor x with hm_def;
  -- Set $z = x + y \geq x + 1$.
  set z := x + y with hz_def;
  -- Case 1: $z \geq m + 2$.
  by_cases h_case1 : z ≥ m + 2;
  · -- Then $Ffun x \leq Ffun ((m:ℝ)+2)$ by Ffun_unit_le_succ2, and $Ffun ((m:ℝ)+2) = Ffun (((m+2:ℕ)):ℝ) \leq Ffun z$ by Ffun_ge_int_for_ge (j = m+2 ≥ 1, z ≥ (m+2:ℝ)).
    have h_case1_ineq : Ffun x ≤ Ffun ((m + 2 : ℕ) : ℝ) ∧ Ffun ((m + 2 : ℕ) : ℝ) ≤ Ffun z := by
      apply And.intro;
      · convert! Ffun_unit_le_succ2 ( show ( m : ℝ ) ≤ x from Nat.floor_le ( by positivity ) ) ( show x ≤ ( m : ℝ ) + 1 from Nat.lt_floor_add_one x |> le_of_lt ) using 1;
        norm_cast;
      · apply Ffun_ge_int_for_ge;
        · linarith;
        · aesop;
    unfold Ffun at *; linarith;
  · -- Case 2: $z < m + 2$.
    have h_case2 : min (Ffun (x + 1)) (Ffun (m + 2)) ≤ Ffun z := by
      apply Ffun_ge_min_on_unit_gen;
      exact Nat.succ_pos m;
      · norm_num; linarith [ Nat.floor_le ( by positivity : 0 ≤ x ) ];
      · linarith;
      · linarith;
      · norm_num [ add_assoc ];
    -- Now $Ffun x \leq Ffun (x+1)$ by $Ffun_step_le$ (x ≥ 1), and $Ffun x \leq Ffun ((m:ℝ)+2)$ by $Ffun_unit_le_succ2$.
    have h_case2_le : Ffun x ≤ Ffun (x + 1) ∧ Ffun x ≤ Ffun (m + 2) := by
      apply And.intro;
      · exact Ffun_step_le hx;
      · convert! Ffun_unit_le_succ2 ( show ( m : ℝ ) ≤ x from Nat.floor_le ( by positivity ) ) ( show x ≤ ( m : ℝ ) + 1 from Nat.lt_floor_add_one x |> le_of_lt ) using 1;
    unfold Ffun at *;
    grind

/-
Real increment (case `x ≥ 0, y ≥ 2`).
-/
theorem Sfun_increment_ge_two {x y : ℝ} (hx : 0 ≤ x) (hy : 2 ≤ y) :
    y / 4 ≤ Sfun (x + y) - Sfun x := by
  -- Let $m = \lfloor x \rfloor$ (a natural number $\geq 0$).
  set m := Nat.floor x with hm_def;
  -- By Ffun_unit_le_succ2 (hx1 : (m:ℝ) ≤ x, hx2 : x ≤ (m:ℝ)+1): Ffun x ≤ Ffun ((m:ℝ)+2).
  have h_unit : Ffun x ≤ Ffun ((m : ℝ) + 2) := by
    convert! Ffun_unit_le_succ2 ( show ( m : ℝ ) ≤ x from Nat.floor_le hx ) ( show x ≤ ( m : ℝ ) + 1 from Nat.lt_floor_add_one x |> le_of_lt ) using 1;
  -- By Ffun_ge_int_for_ge (j = m+2, which is ≥ 1) with z ≥ (m+2:ℝ): Ffun ((m+2:ℕ):ℝ) ≤ Ffun z.
  have h_ge_int : Ffun ((m + 2 : ℕ) : ℝ) ≤ Ffun (x + y) := by
    apply Erdos1005.Ffun_ge_int_for_ge;
    · linarith;
    · norm_num; linarith [ Nat.floor_le hx ];
  unfold Ffun at *; norm_num at *; linarith;

/-
`∑_{d=1}^{N} 1/d ≤ 1 + log N`.
-/
theorem harmonic_le_one_add_log (N : ℕ) :
    ∑ d ∈ Finset.Icc 1 N, (1 : ℝ) / d ≤ 1 + Real.log N := by
  induction' N with N ih <;> norm_num [ Finset.sum_Ioc_succ_top, (Nat.succ_eq_succ ▸ Finset.Icc_succ_left_eq_Ioc) ] at *;
  rcases N.eq_zero_or_pos with rfl | hN;
  · norm_num;
  · have := Real.log_le_sub_one_of_pos ( by positivity : 0 < ( N : ℝ ) / ( N + 1 ) );
    rw [ Real.log_div ] at this <;> norm_num at * <;> nlinarith [ mul_div_cancel₀ ( N : ℝ ) ( by positivity : ( N : ℝ ) + 1 ≠ 0 ), inv_mul_cancel₀ ( by positivity : ( N : ℝ ) + 1 ≠ 0 ) ]

/-
`∑_{e=1}^{N} τ(e) ≤ N·(1 + log N)`.
-/
theorem divisor_sum_le (N : ℕ) :
    ∑ e ∈ Finset.Icc 1 N, (e.divisors.card : ℝ) ≤ (N : ℝ) * (1 + Real.log N) := by
  have h_sum_divisors : ∑ e ∈ Finset.Icc 1 N, (Nat.divisors e).card = ∑ d ∈ Finset.Icc 1 N, (N / d : ℕ) := by
    erw [ Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range ];
    induction N <;> simp_all +decide [ Nat.succ_div, Finset.sum_range_succ ];
    simp_all +decide [ Finset.sum_add_distrib, Nat.add_comm 1 _, Nat.div_eq_of_lt ];
    rw [ ← Nat.cons_self_properDivisors ] <;> simp +arith +decide [ Nat.properDivisors ];
    rw [ Finset.card_filter, Finset.card_filter ];
    rw [ Finset.sum_Ico_eq_sum_range ] ; norm_num [ add_comm, add_left_comm ];
  rw_mod_cast [ h_sum_divisors ];
  refine' le_trans _ ( mul_le_mul_of_nonneg_left ( harmonic_le_one_add_log N ) ( Nat.cast_nonneg _ ) );
  push_cast [ Finset.mul_sum _ _ _ ];
  exact Finset.sum_le_sum fun x hx => by rw [ mul_one_div, le_div_iff₀ ] <;> norm_cast <;> linarith [ Finset.mem_Icc.mp hx, Nat.div_mul_le_self N x ] ;

/-
For `q ≥ 1` and reals `A ≤ B`, the number of integers `p ∈ (A,B)` coprime to `q`
is at least `(B-A)·φ(q)/q - τ(q)`.
-/
theorem coprime_count_lower (q : ℕ) (hq : 1 ≤ q) (A B : ℝ) (hAB : A ≤ B) :
    (B - A) * (Nat.totient q : ℝ) / q - (q.divisors.card : ℝ)
      ≤ ({p : ℤ | A < (p : ℝ) ∧ (p : ℝ) < B ∧ IsCoprime p (q : ℤ)}.ncard : ℝ) := by
  have h_residue_interval_count : ∀ d ∈ q.divisors, |((Set.ncard {p : ℤ | A < (p : ℝ) ∧ (p : ℝ) < B ∧ (d : ℤ) ∣ p}) - (B - A) / d : ℝ)| ≤ 1 := by
    intro d hd; have := @residue_interval_count d ( Nat.pos_of_mem_divisors hd ) 0 A B hAB; aesop;
  have h_coprime_count : (Set.ncard {p : ℤ | A < (p : ℝ) ∧ (p : ℝ) < B ∧ IsCoprime p q}) = ∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℝ) * (Set.ncard {p : ℤ | A < (p : ℝ) ∧ (p : ℝ) < B ∧ (d : ℤ) ∣ p}) := by
    have h_coprime_count : ∀ p : ℤ, (if A < (p : ℝ) ∧ (p : ℝ) < B ∧ IsCoprime p q then 1 else 0) = ∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℝ) * (if A < (p : ℝ) ∧ (p : ℝ) < B ∧ (d : ℤ) ∣ p then 1 else 0) := by
      intro p
      by_cases hp : A < (p : ℝ) ∧ (p : ℝ) < B;
      · have h_coprime_indicator : (if IsCoprime p q then 1 else 0 : ℝ) = ∑ d ∈ Nat.divisors (Int.gcd p q), (ArithmeticFunction.moebius d : ℝ) := by
          have h_coprime_indicator : ∑ d ∈ Nat.divisors (Int.gcd p q), (ArithmeticFunction.moebius d : ℝ) = if Int.gcd p q = 1 then 1 else 0 := by
            have h_coprime_indicator : ∑ d ∈ Nat.divisors (Int.gcd p q), (ArithmeticFunction.moebius d : ℝ) = (ArithmeticFunction.moebius * ArithmeticFunction.zeta) (Int.gcd p q) := by
              simp +decide [ zeta ];
              rw [ Nat.sum_divisorsAntidiagonal fun x y => if y = 0 then 0 else ( moebius x : ℝ ) ];
              exact Finset.sum_congr rfl fun x hx => by rw [ if_neg ( Nat.ne_of_gt ( Nat.div_pos ( Nat.le_of_dvd ( Nat.pos_of_ne_zero ( by aesop ) ) ( Nat.dvd_of_mem_divisors hx ) ) ( Nat.pos_of_mem_divisors hx ) ) ) ] ;
            aesop;
          simp_all +decide [ Int.isCoprime_iff_gcd_eq_one ];
        simp_all +decide [ Finset.sum_ite ];
        refine' Finset.sum_bij ( fun x hx => x ) _ _ _ _ <;> simp_all +decide [ Int.gcd_eq_natAbs ];
        · exact fun a ha₁ ha₂ => ⟨ ⟨ Nat.dvd_trans ha₁ ( Nat.gcd_dvd_right _ _ ), by linarith ⟩, Int.natCast_dvd.mpr ( Nat.dvd_trans ha₁ ( Nat.gcd_dvd_left _ _ ) ) ⟩;
        · exact fun b hb₁ hb₂ hb₃ => Nat.dvd_gcd ( Int.natAbs_dvd_natAbs.mpr hb₃ ) hb₁;
      · rw [ Finset.sum_eq_zero ] <;> aesop;
    have h_coprime_count : ∑ p ∈ Finset.Icc (Int.floor A) (Int.ceil B), (if A < (p : ℝ) ∧ (p : ℝ) < B ∧ IsCoprime p q then 1 else 0) = ∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℝ) * ∑ p ∈ Finset.Icc (Int.floor A) (Int.ceil B), (if A < (p : ℝ) ∧ (p : ℝ) < B ∧ (d : ℤ) ∣ p then 1 else 0) := by
      rw [ Finset.sum_congr rfl fun p hp => h_coprime_count p, Finset.sum_comm, Finset.sum_congr rfl fun d hd => Finset.mul_sum _ _ _ ];
    convert! h_coprime_count using 1;
    · simp +zetaDelta at *;
      rw [ ← Set.ncard_coe_finset ] ; congr ; ext ; simp +decide;
      exact fun _ _ _ => ⟨ Int.le_of_lt_add_one <| Int.floor_lt.2 <| by norm_num; linarith, Int.le_of_lt_add_one <| by rw [ ← @Int.cast_lt ℝ ] ; push_cast; linarith [ Int.le_ceil B ] ⟩;
    · refine' Finset.sum_congr rfl fun d hd => _;
      simp +zetaDelta at *;
      rw [ ← Set.ncard_coe_finset ] ; norm_num;
      exact Or.inl ( congr_arg _ ( by ext; exact ⟨ fun h => ⟨ ⟨ Int.le_of_lt_add_one ( by rw [ ← @Int.cast_lt ℝ ] ; push_cast; linarith [ h.1, Int.floor_le A ] ), Int.le_of_lt_add_one ( by rw [ ← @Int.cast_lt ℝ ] ; push_cast; linarith [ h.2.1, Int.le_ceil B ] ) ⟩, h ⟩, fun h => h.2 ⟩ ) );
  -- Applying the bound from `h_residue_interval_count` to each term in the sum.
  have h_sum_bound : |(∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℝ) * (Set.ncard {p : ℤ | A < (p : ℝ) ∧ (p : ℝ) < B ∧ (d : ℤ) ∣ p})) - (∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℝ) * ((B - A) / d))| ≤ ∑ d ∈ q.divisors, |(ArithmeticFunction.moebius d : ℝ)| := by
    rw [ ← Finset.sum_sub_distrib ];
    exact le_trans ( Finset.abs_sum_le_sum_abs _ _ ) ( Finset.sum_le_sum fun x hx => by rw [ ← mul_sub ] ; exact abs_mul ( _ : ℝ ) _ ▸ mul_le_of_le_one_right ( abs_nonneg _ ) ( h_residue_interval_count x hx ) );
  -- Applying the bound from `h_sum_bound` to the sum.
  have h_sum_bound_simplified : |(∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℝ) * (Set.ncard {p : ℤ | A < (p : ℝ) ∧ (p : ℝ) < B ∧ (d : ℤ) ∣ p})) - ((B - A) * (Nat.totient q : ℝ) / q)| ≤ (q.divisors.card : ℝ) := by
    have h_sum_bound_simplified : ∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℝ) * ((B - A) / d) = (B - A) * (Nat.totient q : ℝ) / q := by
      convert! congr_arg ( fun x : ℝ => ( B - A ) * x ) ( moebius_div_sum_eq_totient_div q hq ) using 1 <;> ring_nf;
      simp +decide only [mul_assoc, mul_left_comm, sum_sub_distrib, Finset.mul_sum _ _ _];
    exact h_sum_bound_simplified ▸ h_sum_bound.trans ( le_trans ( Finset.sum_le_sum fun _ _ => show |_| ≤ 1 by exact mod_cast by { unfold ArithmeticFunction.moebius; aesop } ) ( by norm_num ) );
  linarith [ abs_le.mp h_sum_bound_simplified ]

/-
The number of order-`n` Farey fractions in `(x, y)` is at least the sum over
denominators `q` in `[1,n]` of the per-`q` coprime counts.
-/
set_option maxHeartbeats 1000000 in
theorem density_bridge (n : ℕ) (x y : ℚ) (hx : 0 ≤ x) (hy : y ≤ 1) :
    (∑ q ∈ Finset.Icc 1 n,
        ({p : ℤ | (x : ℝ) * q < (p : ℝ) ∧ (p : ℝ) < (y : ℝ) * q ∧ IsCoprime p (q : ℤ)}.ncard : ℝ))
      ≤ (betweenCount n x y : ℝ) := by
  rw_mod_cast [ Erdos1005.betweenCount ];
  have h_biUnion : ∀ q ∈ Finset.Icc 1 n, ({p : ℤ | (x : ℝ) * q < p ∧ p < (y : ℝ) * q ∧ IsCoprime p q} : Set ℤ).ncard ≤ ({r : ℚ | r.den = q ∧ IsFarey n r ∧ x < r ∧ r < y} : Set ℚ).ncard := by
    intro q hq
    have h_image : Set.image (fun p : ℤ => (p : ℚ) / q) {p : ℤ | (x : ℝ) * q < p ∧ p < (y : ℝ) * q ∧ IsCoprime p q} ⊆ {r : ℚ | r.den = q ∧ IsFarey n r ∧ x < r ∧ r < y} := by
      intro r hr; obtain ⟨ p, hp, rfl ⟩ := hr; simp_all +decide [ IsFarey ] ;
      have h_den : (p / q : ℚ).den = q := by
        rw [ div_eq_mul_inv, Rat.mul_den ] ; norm_num [ hp.2.2 ];
        simp_all +decide [ Int.sign_eq_one_of_pos ( by norm_cast; linarith : 0 < ( q : ℤ ) ) ];
        split_ifs <;> simp_all +decide [ Int.isCoprime_iff_gcd_eq_one ];
        simp_all +decide [ Int.gcd ];
      simp_all +decide [ le_div_iff₀, div_le_iff₀, show q > 0 by linarith ];
      norm_cast at *;
      exact ⟨ ⟨ by exact_mod_cast ( by nlinarith [ ( by norm_cast; linarith : ( 1 : ℚ ) ≤ q ) ] : ( 0 : ℚ ) ≤ p ), by exact_mod_cast ( by nlinarith [ ( by norm_cast; linarith : ( 1 : ℚ ) ≤ q ) ] : ( p : ℚ ) ≤ q ) ⟩, by rw [ Rat.divInt_eq_div ] ; rw [ lt_div_iff₀ ] <;> norm_cast at * <;> linarith, by rw [ Rat.divInt_eq_div ] ; rw [ div_lt_iff₀ ] <;> norm_cast at * <;> linarith ⟩;
    have h_card_image : Set.ncard (Set.image (fun p : ℤ => (p : ℚ) / q) {p : ℤ | (x : ℝ) * q < p ∧ p < (y : ℝ) * q ∧ IsCoprime p q}) ≤ Set.ncard {r : ℚ | r.den = q ∧ IsFarey n r ∧ x < r ∧ r < y} := by
      apply_rules [ Set.ncard_le_ncard ];
      exact Set.Finite.subset ( fareyBetween_finite n x y ) fun r hr => ⟨ hr.2.1, hr.2.2.1, hr.2.2.2 ⟩;
    rwa [ Set.ncard_image_of_injective _ fun a b h => by simpa [ div_eq_iff, show q ≠ 0 by linarith [ Finset.mem_Icc.mp hq ] ] using h ] at h_card_image;
  convert! Finset.sum_le_sum h_biUnion using 1;
  · norm_cast;
  · have h_card_biUnion : ∀ {S : Finset ℕ} (hS : ∀ q ∈ S, 1 ≤ q ∧ q ≤ n), ({r : ℚ | ∃ q ∈ S, r.den = q ∧ IsFarey n r ∧ x < r ∧ r < y}.ncard = ∑ q ∈ S, ({r : ℚ | r.den = q ∧ IsFarey n r ∧ x < r ∧ r < y}.ncard)) := by
      intros S hS;
      induction S using Finset.induction <;> simp_all +decide [ Set.ncard_eq_toFinset_card' ];
      rw [ ← ‹ { r : ℚ | r.den ∈ _ ∧ IsFarey n r ∧ x < r ∧ r < y }.ncard = ∑ q ∈ _, _ ›, ← @Set.ncard_union_eq ];
      · exact congr_arg _ ( by ext; aesop );
      · grind +splitImp;
      · exact Set.Finite.subset ( farey_finite n ) fun x hx => hx.2.1;
      · exact Set.Finite.subset ( farey_finite n ) fun x hx => hx.2.1;
    convert! h_card_biUnion fun q hq => Finset.mem_Icc.mp hq using 2;
    ext; simp [IsFarey];
    exact fun _ _ _ _ _ => ⟨ Rat.pos _, by assumption ⟩

/-
`betweenCount n x y ≥ (y-x)·Φ(n) - ∑_{q≤n} τ(q) ≥ (y-x)·n(n+1)/4 - n·(1+log n)`.
-/
theorem density_count_lower (n : ℕ) (x y : ℚ) (hx : 0 ≤ x) (hy : y ≤ 1) (hxy : x < y) :
    ((y : ℝ) - x) * ((n : ℝ) * ((n : ℝ) + 1) / 4) - (n : ℝ) * (1 + Real.log n)
      ≤ (betweenCount n x y : ℝ) := by
  have h_density : (betweenCount n x y : ℝ) ≥ (∑ q ∈ Finset.Icc 1 n, ((y - x) * (Nat.totient q : ℝ) - (q.divisors.card : ℝ))) := by
    -- Apply the density bridge theorem to get the lower bound.
    have h_lower_bound : (betweenCount n x y : ℝ) ≥ ∑ q ∈ Finset.Icc 1 n, ((y - x) * (Nat.totient q : ℝ) - (q.divisors.card : ℝ)) := by
      have := density_bridge n x y hx hy
      refine' le_trans ( Finset.sum_le_sum _ ) this;
      intro q hq; specialize hq; have := coprime_count_lower q ( by linarith [ Finset.mem_Icc.mp hq ] ) ( x * q ) ( y * q ) ( by nlinarith [ show ( q : ℝ ) ≥ 1 by norm_cast; linarith [ Finset.mem_Icc.mp hq ], show ( x : ℝ ) < y by exact_mod_cast hxy ] ) ; simp_all +decide [ mul_comm, mul_div_assoc ] ;
      rwa [ ← mul_sub, mul_div_cancel_left₀ _ ( by norm_cast; linarith ) ] at this
    generalize_proofs at *; (
    convert! h_lower_bound using 1);
  refine le_trans ?_ h_density;
  -- By `four_mul_Phi_ge n : n*(n+1) ≤ 4*Phi n` (i.e. `(Phi n : ℝ) ≥ n*(n+1)/4`).
  have h_phi : (Phi n : ℝ) ≥ (n * (n + 1) / 4 : ℝ) := by
    exact div_le_iff₀' ( by positivity ) |>.2 ( mod_cast four_mul_Phi_ge n );
  convert! sub_le_sub ( mul_le_mul_of_nonneg_left h_phi <| sub_nonneg.mpr <| Rat.cast_le.mpr hxy.le ) <| divisor_sum_le n using 1;
  unfold Phi; erw [ Finset.sum_Ico_eq_sub _ _ ] <;> norm_num [ Finset.mul_sum _ _ _, Finset.sum_range_succ' ] ;
  erw [ Finset.sum_Ico_eq_sub _ _ ] <;> norm_num [ Finset.sum_range_succ' ]

/-
Fix a reference rational `z` and a left endpoint `x` with `0 ≤ x < z ≤ 1`. For
`e ≥ 1` and an integer denominator `d` with `0 < d ≤ n`, `z.den ∣ (z.num·d − e)`,
the numerator `p = (z.num·d − e)/z.den` coprime to `d`, and the lower bound
`x.den·e < (z.num·x.den − x.num·z.den)·d` (i.e. `x < p/d`), the fraction `p/d`
is an order-`n` Farey fraction strictly between `x` and `z`.
-/
theorem left_frac_mem (x z : ℚ) (hx0 : 0 ≤ x) (hz1 : z ≤ 1)
    (n : ℕ) (e : ℕ) (he : 1 ≤ e) (d : ℤ)
    (hd_pos : 0 < d) (hdn : d ≤ (n : ℤ))
    (hdvd : (z.den : ℤ) ∣ (z.num * d - e))
    (hlow : (x.den : ℤ) * e < (z.num * (x.den : ℤ) - x.num * (z.den : ℤ)) * d) :
    IsFarey n (((z.num * d - e) / z.den : ℤ) / (d : ℚ)) ∧
      x < (((z.num * d - e) / z.den : ℤ) / (d : ℚ)) ∧
      (((z.num * d - e) / z.den : ℤ) / (d : ℚ)) < z := by
  refine' ⟨ _, _, _ ⟩;
  · refine' ⟨ _, _, _ ⟩;
    · refine' div_nonneg _ _ <;> norm_cast;
      · refine' Int.ediv_nonneg _ _ <;> norm_num;
        nlinarith [ show x.num * z.den ≥ 0 by exact mul_nonneg ( Rat.num_nonneg.mpr hx0 ) ( Nat.cast_nonneg _ ) ];
      · grind;
    · rw [ div_le_iff₀ ] <;> norm_cast;
      rw [ Int.ediv_le_iff_le_mul ] <;> norm_num;
      · nlinarith [ show z.num ≤ z.den from by simpa [ Rat.le_iff ] using! hz1, show ( z.den : ℤ ) > 0 from mod_cast z.pos ];
      · exact z.pos;
    · rw [ div_eq_mul_inv ];
      erw [ Rat.mul_den ] ; norm_num [ hd_pos.ne', hdn ];
      exact le_trans ( Nat.div_le_self _ _ ) ( by linarith [ abs_of_pos hd_pos ] );
  · rw [ lt_div_iff₀ ] <;> norm_cast;
    rw [ ← Rat.num_div_den x ];
    rw [ div_mul_eq_mul_div, div_lt_iff₀ ] <;> norm_cast;
    · nlinarith [ Int.ediv_mul_cancel hdvd ];
    · exact x.pos;
  · rw [ div_lt_iff₀ ] <;> norm_cast;
    rw [ Int.cast_div ] <;> norm_num [ hdvd ];
    rw [ div_lt_iff₀ ] <;> norm_cast;
    · rw [ mul_right_comm, Rat.mul_den_eq_num ];
      rw [ Int.cast_sub, Int.cast_mul ] ; norm_num ; linarith;
    · exact z.pos

/-- The per-`e` fiber of left-side denominators: exactly the `prim_prog_lower` set with
reference `z`, window lower end `A_e = x.den·e/u` (`u = z.num·x.den − x.num·z.den`) and
upper end `n+1` (so `d < n+1 ↔ d ≤ n`). -/
noncomputable def leftFiber (x z : ℚ) (n e : ℕ) : Set ℤ :=
  {q : ℤ | ((x.den : ℝ) * e / ((z.num * (x.den : ℤ) - x.num * (z.den : ℤ) : ℤ) : ℝ)) < (q : ℝ)
      ∧ (q : ℝ) < (n : ℝ) + 1 ∧ (z.den : ℤ) ∣ (z.num * q - e)
      ∧ IsCoprime ((z.num * q - e) / z.den) q}

/-
For `0 ≤ x < z ≤ 1`, the number of order-`n` Farey fractions strictly between
`x` and `z` is at least the sum over `e ∈ [1,E]` of the per-`e` fiber counts.
-/
set_option maxHeartbeats 1000000 in
theorem left_count_bridge (x z : ℚ) (hx0 : 0 ≤ x) (hxz : x < z) (hz1 : z ≤ 1) (n E : ℕ) :
    (∑ e ∈ Finset.Icc 1 E, ((leftFiber x z n e).ncard : ℝ)) ≤ (betweenCount n x z : ℝ) := by
  -- Define the mapping g from the fibers to the Farey fractions.
  set g : ℕ × ℤ → ℚ := fun ⟨e, d⟩ => (((z.num * d - e) / z.den : ℤ) : ℚ) / (d : ℚ);
  -- Show that the image of the fibers under g is a subset of the Farey fractions.
  have h_image_subset : ∀ e ∈ Finset.Icc 1 E, ∀ d ∈ leftFiber x z n e, g (e, d) ∈ {q : ℚ | IsFarey n q ∧ x < q ∧ q < z} := by
    intros e he d hd
    apply left_frac_mem x z hx0 hz1 n e (Finset.mem_Icc.mp he).left d (by
    unfold leftFiber at hd;
    norm_num +zetaDelta at *;
    exact_mod_cast hd.1.trans_le' ( div_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( Nat.cast_nonneg _ ) ) ( sub_nonneg.mpr ( by rw [ ← Rat.num_div_den x, ← Rat.num_div_den z ] at hxz; rw [ div_lt_div_iff₀ ] at hxz <;> norm_cast at * <;> nlinarith [ x.pos, z.pos ] ) ) )) (by
    exact Int.le_of_lt_add_one ( by rw [ ← @Int.cast_lt ℝ ] ; push_cast; linarith [ hd.2.1 ] )) (by
    exact hd.2.2.1) (by
    obtain ⟨ hd₁, hd₂, hd₃, hd₄ ⟩ := hd;
    rw [ div_lt_iff₀ ] at hd₁ <;> norm_cast at *;
    · linarith;
    · rw [ Rat.lt_iff ] at hxz ; aesop);
  -- Show that the image of the fibers under g is injective.
  have h_image_inj : ∀ e₁ e₂ : ℕ, e₁ ∈ Finset.Icc 1 E → e₂ ∈ Finset.Icc 1 E → ∀ d₁ d₂ : ℤ, d₁ ∈ leftFiber x z n e₁ → d₂ ∈ leftFiber x z n e₂ → g (e₁, d₁) = g (e₂, d₂) → e₁ = e₂ ∧ d₁ = d₂ := by
    intros e₁ e₂ he₁ he₂ d₁ d₂ hd₁ hd₂ h_eq
    have h_den : d₁ = d₂ := by
      have h_den : (g (e₁, d₁)).den = d₁.natAbs ∧ (g (e₂, d₂)).den = d₂.natAbs := by
        have h_denom : ∀ e : ℕ, ∀ d : ℤ, d ∈ leftFiber x z n e → IsCoprime ((z.num * d - e) / z.den) d → (g (e, d)).den = d.natAbs := by
          intros e d hd h_coprime
          simp [g];
          rw [ div_eq_mul_inv, Rat.mul_den ];
          erw [ Rat.inv_intCast_den, Rat.inv_intCast_num ] ; norm_num;
          split_ifs <;> simp_all +decide [ Int.natAbs_mul, Int.natAbs_sign ];
          · have := hd.1; norm_num at this;
            contrapose! this;
            exact div_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( Nat.cast_nonneg _ ) ) ( sub_nonneg_of_le <| by rw [ ← Rat.num_div_den x, ← Rat.num_div_den z ] at hxz; rw [ div_lt_div_iff₀ ] at hxz <;> norm_cast at * <;> nlinarith [ x.pos, z.pos ] );
          · rw [ Nat.Coprime.gcd_eq_one ] <;> norm_num [ Int.isCoprime_iff_gcd_eq_one ] at * ; aesop;
        exact ⟨ h_denom e₁ d₁ hd₁ hd₁.2.2.2, h_denom e₂ d₂ hd₂ hd₂.2.2.2 ⟩;
      have h_den_pos : 0 < d₁ ∧ 0 < d₂ := by
        have h_den_pos : ∀ e ∈ Finset.Icc 1 E, ∀ d ∈ leftFiber x z n e, 0 < d := by
          intros e he d hd
          have h_den_pos : 0 < (x.den : ℝ) * e / ((z.num * (x.den : ℤ) - x.num * (z.den : ℤ) : ℤ) : ℝ) := by
            refine' div_pos ( mul_pos ( Nat.cast_pos.mpr x.pos ) ( Nat.cast_pos.mpr ( Finset.mem_Icc.mp he |>.1 ) ) ) ( Int.cast_pos.mpr _ );
            rw [ Rat.lt_iff ] at hxz ; aesop;
          exact_mod_cast hd.1.trans_le' h_den_pos.le;
        exact ⟨ h_den_pos e₁ he₁ d₁ hd₁, h_den_pos e₂ he₂ d₂ hd₂ ⟩;
      grind
    have h_num : e₁ = e₂ := by
      simp +zetaDelta at *;
      have := hd₁.2.2.1; have := hd₂.2.2.1; simp_all +decide;
      simp_all +decide [ div_eq_mul_inv ];
      exact h_eq.resolve_right ( by linarith [ show 0 < d₂ from by exact_mod_cast hd₁.1.trans_le' ( div_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( Nat.cast_nonneg _ ) ) ( by exact_mod_cast sub_nonneg.mpr ( show ( z.num * x.den : ℤ ) ≥ x.num * z.den from by rw [ Rat.lt_iff ] at hxz; linarith ) ) ) ] ) ▸ rfl
    exact ⟨h_num, h_den⟩;
  -- By definition of $g$, we know that the image of the fibers under $g$ is a subset of the Farey fractions.
  have h_image_subset : Finset.card (Finset.biUnion (Finset.Icc 1 E) (fun e => Finset.image (fun d => g (e, d)) (Set.Finite.toFinset (show Set.Finite (leftFiber x z n e) from by
                                                                                                                                        refine' Set.Finite.subset ( Set.finite_Icc ( 0 : ℤ ) ( n : ℤ ) ) _;
                                                                                                                                        intro d hd; exact ⟨ by
                                                                                                                                          have := hd.1;
                                                                                                                                          contrapose! this;
                                                                                                                                          exact le_trans ( mod_cast this.le ) ( div_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( Nat.cast_nonneg _ ) ) ( mod_cast by nlinarith [ show 0 < z.num * x.den - x.num * z.den from by rw [ Rat.lt_iff ] at hxz; linarith ] ) ), by
                                                                                                                                          exact Int.le_of_lt_add_one ( by rw [ ← @Int.cast_lt ℝ ] ; push_cast; linarith [ hd.2.1 ] ) ⟩ ;)))) ≤ (betweenCount n x z : ℕ) := by
                                                                                                                                        rw [ ← Set.ncard_coe_finset ];
                                                                                                                                        apply Set.ncard_le_ncard;
                                                                                                                                        · simp +zetaDelta at *;
                                                                                                                                          exact fun e he₁ he₂ => fun d hd => h_image_subset e he₁ he₂ d hd;
                                                                                                                                        · exact fareyBetween_finite n x z
  generalize_proofs at *;
  rw [ Finset.card_biUnion ] at h_image_subset;
  · rw [ Finset.sum_congr rfl fun e he => Finset.card_image_of_injOn <| fun d₁ hd₁ d₂ hd₂ h => by specialize h_image_inj e e he he d₁ d₂ ; aesop ] at h_image_subset ; norm_cast;
    convert! h_image_subset using 2;
    rw [ ← Set.ncard_coe_finset ] ; congr ; aesop;
  · intros e₁ he₁ e₂ he₂ he_ne; simp [Finset.disjoint_left, Finset.mem_image];
    exact fun a ha b hb hab => he_ne <| h_image_inj e₁ e₂ he₁ he₂ a b ha hb hab.symm |>.1

/-
The number of order-`n` Farey fractions strictly between `x` and `z` is at least
`((n+1)/z.den) * S(mu*u) - sum_{e=1}^{ceil(mu*u)-1} tau(e)`, where
`mu = (n+1)/x.den` and `u = z.num*x.den - x.num*z.den`.
-/
set_option maxHeartbeats 1000000 in
theorem left_count_main (x z : ℚ) (hx0 : 0 ≤ x) (hxz : x < z) (hz1 : z ≤ 1) (n : ℕ) :
    ((n : ℝ) + 1) / z.den
        * Sfun (((n : ℝ) + 1) / x.den * ((z.num * (x.den : ℤ) - x.num * (z.den : ℤ) : ℤ) : ℝ))
      - (∑ e ∈ Finset.Icc 1
          (⌈((n : ℝ) + 1) / x.den * ((z.num * (x.den : ℤ) - x.num * (z.den : ℤ) : ℤ) : ℝ)⌉₊ - 1),
          (e.divisors.card : ℝ))
      ≤ (betweenCount n x z : ℝ) := by
  -- Apply the `prim_prog_lower` bound to each term in the sum.
  have h_prime_lower_bound (e : ℕ) (he : 1 ≤ e) (he_le : e ≤ Nat.ceil ((n + 1) / x.den * (z.num * x.den - x.num * z.den : ℝ)) - 1) :
      ((Nat.totient e : ℝ) / e) * ((n + 1) - (x.den * e : ℝ) / ((z.num * x.den - x.num * z.den : ℤ) : ℝ)) / z.den - ((e.divisors.card : ℝ)) ≤ (leftFiber x z n e).ncard := by
        convert! prim_prog_lower z.num z.den ( mod_cast z.pos ) _ e he _ _ _ using 1;
        · exact Int.isCoprime_iff_gcd_eq_one.mpr ( by simpa [ Int.gcd, Int.natAbs_abs ] using! z.reduced );
        · rw [ div_le_iff₀ ] <;> norm_cast;
          · rw [ Nat.le_sub_iff_add_le ] at he_le;
            · contrapose! he_le;
              rw [ Nat.lt_succ_iff, Nat.ceil_le ];
              rw [ div_mul_eq_mul_div, div_le_iff₀ ] <;> norm_cast at *;
              · exact he_le.le.trans ( by norm_cast; linarith );
              · exact x.pos;
            · grind;
          · rw [ Rat.lt_iff ] at hxz ; aesop;
  -- Summing the bounds from `h_prime_lower_bound` over all `e` in the range.
  have h_sum_lower_bound :
      (∑ e ∈ Finset.Icc 1 (Nat.ceil ((n + 1) / x.den * (z.num * x.den - x.num * z.den : ℝ)) - 1), ((Nat.totient e : ℝ) / e) * ((n + 1) - (x.den * e : ℝ) / ((z.num * x.den - x.num * z.den : ℤ) : ℝ)) / z.den) -
      (∑ e ∈ Finset.Icc 1 (Nat.ceil ((n + 1) / x.den * (z.num * x.den - x.num * z.den : ℝ)) - 1), ((e.divisors.card : ℝ))) ≤
      (betweenCount n x z : ℝ) := by
        refine' le_trans _ ( left_count_bridge x z hx0 hxz hz1 n _ );
        simpa only [ ← Finset.sum_sub_distrib ] using! Finset.sum_le_sum fun e he => h_prime_lower_bound e ( Finset.mem_Icc.mp he |>.1 ) ( Finset.mem_Icc.mp he |>.2 );
  by_cases h : ⌈ ( n + 1 : ℝ ) / x.den * ( z.num * x.den - x.num * z.den ) ⌉₊ = 0 <;> simp_all +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm ];
  · contrapose! h;
    refine' mul_pos ( inv_pos.mpr ( Nat.cast_pos.mpr x.pos ) ) ( mul_pos _ ( Nat.cast_add_one_pos _ ) );
    rw [ Rat.lt_iff ] at hxz ; norm_cast at *;
    linarith;
  · convert! h_sum_lower_bound using 1;
    rw [ show Sfun ( ( x.den : ℝ ) ⁻¹ * ( ( z.num * x.den - x.num * z.den ) * ( n + 1 ) ) ) = ∑ e ∈ Finset.range ⌈ ( x.den : ℝ ) ⁻¹ * ( ( z.num * x.den - x.num * z.den ) * ( n + 1 ) ) ⌉₊, ( 1 - ( e : ℝ ) / ( ( x.den : ℝ ) ⁻¹ * ( ( z.num * x.den - x.num * z.den ) * ( n + 1 ) ) ) ) * ( Nat.totient e / e ) from rfl ] ; simp +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ] ;
    erw [ Finset.sum_Ico_eq_sub _ ] <;> norm_num [ Finset.sum_range_succ' ];
    cases k : ⌈ ( x.den : ℝ ) ⁻¹ * ( ( z.num * x.den - x.num * z.den ) * ( n + 1 ) ) ⌉₊ <;> simp_all +decide [ Finset.sum_range_succ' ] ; ring_nf;
    grind

/-
The count over `(x,w)` is at least the sum of the counts over `(x,z)` and
`(z,w)`.
-/
theorem betweenCount_split (n : ℕ) (x z w : ℚ) (hxz : x ≤ z) (hzw : z ≤ w) :
    betweenCount n x z + betweenCount n z w ≤ betweenCount n x w := by
  by_contra h_contra;
  unfold betweenCount at *;
  apply h_contra;
  rw [ ← @Set.ncard_union_eq ];
  · apply Set.ncard_le_ncard;
    · rintro q ( ⟨ hq₁, hq₂, hq₃ ⟩ | ⟨ hq₁, hq₂, hq₃ ⟩ ) <;> exact ⟨ hq₁, by linarith, by linarith ⟩;
    · exact fareyBetween_finite n x w;
  · exact Set.disjoint_left.mpr fun q hq₁ hq₂ => by linarith [ hq₁.2.2, hq₂.2.1 ] ;
  · exact Set.Finite.subset ( farey_finite n ) fun q hq => hq.1;
  · exact fareyBetween_finite n z w

/-
The count over `(a,c)` is at most the counts over `(a,b)` and `(b,c)` plus one
(for the interior point `b` itself).
-/
theorem betweenCount_split_le (n : ℕ) (a b c : ℚ) :
    betweenCount n a c ≤ betweenCount n a b + betweenCount n b c + 1 := by
  -- Let's define the sets $A$, $B$, and $C$ as given in the provided solution.
  set A := {r : ℚ | IsFarey n r ∧ a < r ∧ r < c}
  set B := {r : ℚ | IsFarey n r ∧ a < r ∧ r < b}
  set C := {r : ℚ | IsFarey n r ∧ b < r ∧ r < c};
  -- By definition of $A$, $B$, and $C$, we have $A \subseteq B \cup C \cup \{b\}$.
  have h_subset : A ⊆ B ∪ C ∪ {b} := by
    grind;
  -- Using the subset relationship, we can bound the cardinality of $A$.
  have h_card : Set.ncard A ≤ Set.ncard (B ∪ C) + Set.ncard ({b} : Set ℚ) := by
    refine' le_trans _ ( Set.ncard_union_le _ _ );
    apply_rules [ Set.ncard_le_ncard ];
    exact Set.Finite.union ( Set.Finite.union ( fareyBetween_finite n a b ) ( fareyBetween_finite n b c ) ) ( Set.finite_singleton b );
  refine le_trans h_card ?_;
  refine' add_le_add ( Set.ncard_union_le _ _ ) _;
  norm_num

/-
The order-reversing involution `q ↦ 1 - q` preserves Farey order-`n`
(`(1-q).den = q.den`), so the count over `(z,w)` equals the count over `(1-w, 1-z)`.
-/
theorem betweenCount_reflect (n : ℕ) (z w : ℚ) :
    betweenCount n z w = betweenCount n (1 - w) (1 - z) := by
  fapply Set.ncard_congr;
  use fun q hq => 1 - q;
  · simp +contextual [ IsFarey ];
  · grind;
  · simp +zetaDelta at *;
    intro b hb hb' hb''; use 1 - b; simp_all +decide [ IsFarey ] ;
    grind +splitImp

/-
If `u, v ≥ 1`, `s ≥ 2` and `s + 1 ≤ u + v`, then `S(u) + S(v) ≥ s/4`.
-/
theorem Sfun_pair_ge (u v : ℕ) (hu : 1 ≤ u) (hv : 1 ≤ v) (s : ℕ) (hs : 2 ≤ s)
    (hsum : s + 1 ≤ u + v) : (s : ℝ) / 4 ≤ Sfun u + Sfun v := by
  rcases u with ( _ | _ | u ) <;> rcases v with ( _ | _ | v ) <;> norm_num at *;
  · grind;
  · rw [ Sfun_one ] ; norm_num;
    have := Sfun_ge_quarter ( show 2 ≤ ( v + 1 + 1 : ℕ ) by linarith ) ; norm_num at * ; linarith [ ( by norm_cast : ( s : ℝ ) + 1 ≤ 1 + ( v + 1 + 1 ) ) ] ;
  · rw [ Sfun_one ] ; norm_num;
    have := Sfun_ge_quarter ( by linarith : 2 ≤ u + 1 + 1 ) ; norm_num at * ; linarith [ ( by norm_cast : ( s : ℝ ) ≤ u + 2 ) ] ;
  · linarith [ show Sfun ( u + 1 + 1 : ℝ ) ≥ ( u + 1 + 1 : ℝ ) / 4 by exact_mod_cast Sfun_ge_quarter ( by linarith ), show Sfun ( v + 1 + 1 : ℝ ) ≥ ( v + 1 + 1 : ℝ ) / 4 by exact_mod_cast Sfun_ge_quarter ( by linarith ), ( by norm_cast : ( s : ℝ ) + 1 ≤ u + 1 + 1 + ( v + 1 + 1 ) ) ]

/-- `S(j) ≤ S(t)` whenever `j` is a positive integer and `t ≥ j`. -/
theorem Sfun_ge_int {j : ℕ} (hj : 1 ≤ j) {t : ℝ} (ht : (j : ℝ) ≤ t) : Sfun (j : ℝ) ≤ Sfun t := by
  have := Ffun_ge_int_for_ge hj ht
  unfold Ffun at this
  linarith

/-
`S` vanishes on `[0, 1)`.
-/
theorem Sfun_eq_zero_of_lt_one {t : ℝ} (h0 : 0 ≤ t) (h1 : t < 1) : Sfun t = 0 := by
  unfold Sfun;
  cases eq_or_ne t 0 <;> simp_all +decide;
  rw [ show ⌈t⌉₊ = 1 by exact Nat.ceil_eq_iff ( by positivity ) |>.2 ⟨ by norm_num; linarith [ show ( 0 : ℝ ) < t by positivity ], by norm_num; linarith ⟩ ] ; norm_num

/-
Under the listed size conditions, `((n+1)/s)·(S aX − S aE) ≥ n/4`.
-/
theorem caseB_ratio_ge (n s : ℕ) (hs : 1 ≤ s) (aX aE : ℝ) (haE0 : 0 ≤ aE)
    (h2X : (2 : ℝ) ≤ aX) (hdiff : (s : ℝ) ≤ aX - aE)
    (hbig : (n : ℝ) ≤ ((n : ℝ) + 1) / s * (aX - aE)) :
    (n : ℝ) / 4 ≤ ((n : ℝ) + 1) / s * (Sfun aX - Sfun aE) := by
  by_cases hs2 : s ≥ 2;
  · have h_case2 : Sfun aX - Sfun aE ≥ (aX - aE) / 4 := by
      have := Sfun_increment_ge_two haE0 ( show 2 ≤ aX - aE from le_trans ( mod_cast hs2 ) hdiff ) ; aesop;
    nlinarith [ show ( 0 : ℝ ) ≤ ( n + 1 ) / s by positivity ];
  · interval_cases s;
    by_cases haE1 : aE < 1;
    · rw [ Sfun_eq_zero_of_lt_one haE0 haE1 ] ; norm_num;
      have := Sfun_ge_int ( by norm_num : 1 ≤ 2 ) ( by linarith : ( 2 : ℝ ) ≤ aX ) ; norm_num at * ; nlinarith [ Sfun_two ] ;
    · have := Erdos1005.Sfun_increment_ge_one ( show 1 ≤ aE by linarith ) ( show 1 ≤ aX - aE by norm_num at *; linarith ) ; ( norm_num at * ; nlinarith; )

/-
The reflection `q ↦ 1 - q` preserves the denominator.
-/
theorem one_sub_den (q : ℚ) : (1 - q).den = q.den := by
  norm_num [ Rat.sub_def ];
  rw [ Nat.Coprime.gcd_eq_one ];
  · norm_num;
  · refine' Nat.Coprime.symm ( Nat.coprime_of_dvd' _ );
    intro k hk hk₁ hk₂; have := Nat.dvd_gcd hk₁ ( show k ∣ q.num.natAbs from ?_ ) ; simp_all +decide;
    · simp_all +decide [ Rat.reduced, Nat.Coprime, Nat.Coprime.symm ];
    · rw [ ← Int.natCast_dvd ] at *;
      simpa using! dvd_sub ( Int.natCast_dvd_natCast.mpr hk₁ ) hk₂

/-- Abbreviation for the error term of the left count `(x, z)`. -/
noncomputable def errTerm (x z : ℚ) (n : ℕ) : ℝ :=
  ∑ e ∈ Finset.Icc 1
    (⌈((n : ℝ) + 1) / x.den * ((z.num * (x.den : ℤ) - x.num * (z.den : ℤ) : ℤ) : ℝ)⌉₊ - 1),
    (e.divisors.card : ℝ)

/-
Every order-`n` Farey fraction in `(x, z)` lies in some per-`e` fiber, so the
between-count is at most the sum of the fiber counts.
-/
set_option maxHeartbeats 1000000 in
theorem left_count_bridge_upper (x z : ℚ) (hxz : x < z) (n : ℕ) :
    (betweenCount n x z : ℝ)
      ≤ ∑ e ∈ Finset.Icc 1
          (⌈((n : ℝ) + 1) / x.den * ((z.num * (x.den : ℤ) - x.num * (z.den : ℤ) : ℤ) : ℝ)⌉₊ - 1),
          ((leftFiber x z n e).ncard : ℝ) := by
  -- Let `Bset := {r : ℚ | IsFarey n r ∧ x < r ∧ r < z}` (finite, `fareyBetween_finite`).
  set Bset := {r : ℚ | IsFarey n r ∧ x < r ∧ r < z} with hBset_def;
  -- By definition of `Bset`, we can partition it into subsets based on the value of `e`.
  have h_partition : Bset = ⋃ e ∈ Finset.Icc 1 (⌈((n + 1) / x.den * ((z.num * x.den - x.num * z.den) : ℤ) : ℝ)⌉₊ - 1), {r ∈ Bset | (z.num * r.den - z.den * r.num : ℤ).toNat = e} := by
    ext r
    simp [hBset_def];
    intro hr hxz hz1
    have h_e : 1 ≤ (z.num * r.den - z.den * r.num : ℤ).toNat := by
      grind +suggestions
    have h_e_le : (z.num * r.den - z.den * r.num : ℤ) < ((n + 1) / x.den * ((z.num * x.den - x.num * z.den) : ℤ) : ℝ) := by
      rw [ div_mul_eq_mul_div, lt_div_iff₀ ] <;> norm_cast at * <;> simp_all +decide [ Rat.lt_iff ];
      · nlinarith [ hr.2.2, show ( r.den : ℤ ) ≤ n from mod_cast hr.2.2 ];
      · exact x.pos
    generalize_proofs at *;
    rw [ Nat.cast_sub ] <;> norm_num;
    · norm_num [ Rat.mul_den, Rat.mul_num ] at *;
      exact ⟨ h_e, by linarith [ Nat.le_ceil ( ( n + 1 : ℝ ) / x.den * ( z.num * x.den - x.num * z.den ) ), show ( z.num * r.den : ℤ ) ≤ ⌈ ( n + 1 : ℝ ) / x.den * ( z.num * x.den - x.num * z.den ) ⌉₊ - 1 + z.den * r.num from by { exact Int.le_of_lt_add_one <| by { rw [ ← @Int.cast_lt ℝ ] ; push_cast; linarith [ Nat.le_ceil ( ( n + 1 : ℝ ) / x.den * ( z.num * x.den - x.num * z.den ) ) ] } } ] ⟩;
    · refine' mul_pos _ _ <;> norm_cast;
      · exact div_pos ( Nat.cast_pos.mpr ( Nat.succ_pos _ ) ) ( Nat.cast_pos.mpr ( Rat.pos _ ) );
      · rw [ Rat.lt_iff ] at * ; aesop;
  -- Each subset in the partition injects into the corresponding `leftFiber`.
  have h_injection : ∀ e ∈ Finset.Icc 1 (⌈((n + 1) / x.den * ((z.num * x.den - x.num * z.den) : ℤ) : ℝ)⌉₊ - 1), Set.ncard {r ∈ Bset | (z.num * r.den - z.den * r.num : ℤ).toNat = e} ≤ Set.ncard (leftFiber x z n e) := by
    intros e he
    have h_inj : Set.InjOn (fun r : ℚ => (r.den : ℤ)) {r ∈ Bset | (z.num * r.den - z.den * r.num : ℤ).toNat = e} := by
      intros r hr s hs hrs;
      -- Since $r.den = s.den$, we have $r.num = s.num$ because $r$ and $s$ are in lowest terms.
      have h_num_eq : r.num = s.num := by
        have h_num_eq : z.num * r.den - z.den * r.num = z.num * s.den - z.den * s.num := by
          grind +revert;
        norm_num +zetaDelta at *;
        rw [ hrs ] at h_num_eq; nlinarith [ show ( z.den : ℤ ) > 0 from Nat.cast_pos.mpr z.pos ] ;
      exact Rat.eq_iff_mul_eq_mul.mpr ( by simp +decide [ h_num_eq, hrs ] );
    have h_image : Set.image (fun r : ℚ => (r.den : ℤ)) {r ∈ Bset | (z.num * r.den - z.den * r.num : ℤ).toNat = e} ⊆ leftFiber x z n e := by
      intro d hd
      obtain ⟨r, hr, rfl⟩ := hd
      simp [leftFiber] at *;
      refine' ⟨ _, _, _, _ ⟩;
      · rw [ div_lt_iff₀ ] <;> norm_cast;
        · have := hr.1.2.1; rw [ Rat.lt_iff ] at this; norm_num at *;
          rw [ ← hr.2, Int.toNat_of_nonneg ];
          · nlinarith [ show ( z.den : ℤ ) > 0 by exact_mod_cast z.pos ];
          · have := hr.1.2.2; rw [ Rat.lt_iff ] at this; norm_num at *; linarith;
        · rw [ Rat.lt_iff ] at hxz ; linarith;
      · exact_mod_cast Nat.lt_succ_of_le ( hr.1.1.2.2 );
      · rw [ ← hr.2 ];
        rw [ Int.toNat_of_nonneg ];
        · norm_num;
        · grind;
      · rw [ ← hr.2, Int.toNat_of_nonneg ];
        · exact Int.isCoprime_iff_gcd_eq_one.mpr ( by simpa [ Int.gcd_natCast_natCast ] using! r.reduced );
        · grind +suggestions;
    rw [ ← Set.InjOn.ncard_image h_inj ];
    apply_rules [ Set.ncard_le_ncard ];
    refine' Set.Finite.subset ( Set.finite_Ioo ( 0 : ℤ ) ( n + 1 ) ) _;
    intro q hq; exact ⟨ by
      have := hq.1; rw [ div_lt_iff₀ ] at this <;> norm_cast at * ;
      · nlinarith [ show 0 < z.num * x.den - x.num * z.den from by rw [ Rat.lt_iff ] at hxz; linarith ];
      · rw [ Rat.lt_iff ] at hxz ; linarith, by
      exact_mod_cast hq.2.1 ⟩ ;
  have h_card_union : Set.ncard Bset ≤ ∑ e ∈ Finset.Icc 1 (⌈((n + 1) / x.den * ((z.num * x.den - x.num * z.den) : ℤ) : ℝ)⌉₊ - 1), Set.ncard {r ∈ Bset | (z.num * r.den - z.den * r.num : ℤ).toNat = e} := by
    have h_card_union : ∀ (s : Finset ℕ) (f : ℕ → Set ℚ), Set.ncard (⋃ e ∈ s, f e) ≤ ∑ e ∈ s, Set.ncard (f e) := by
      intros s f;
      induction' s using Finset.induction with e s hes ih;
      · norm_num;
      · rw [ Finset.set_biUnion_insert, Finset.sum_insert hes ];
        refine ( Set.ncard_union_le _ _ ).trans ?_;
        exact Nat.add_le_add_left ih _;
    convert! h_card_union _ _ using 2;
    convert! h_partition using 1;
  exact_mod_cast h_card_union.trans ( Finset.sum_le_sum h_injection )

/-
The matching upper bound to `left_count_main`:
`betweenCount n x z <= ((n+1)/z.den)*S(mu*u) + errTerm x z n`.
-/
set_option maxHeartbeats 1000000 in
theorem left_count_upper (x z : ℚ) (hxz : x < z) (n : ℕ) :
    (betweenCount n x z : ℝ)
      ≤ ((n : ℝ) + 1) / z.den
          * Sfun (((n : ℝ) + 1) / x.den * ((z.num * (x.den : ℤ) - x.num * (z.den : ℤ) : ℤ) : ℝ))
        + errTerm x z n := by
  refine le_trans ( left_count_bridge_upper x z hxz n ) ?_;
  -- Applying the upper bound from `prim_prog_upper` to each term in the sum.
  have h_upper_bound : ∀ e ∈ Finset.Icc 1 (Nat.ceil (((n + 1) / x.den * (z.num * x.den - x.num * z.den : ℤ) : ℝ)) - 1), ((leftFiber x z n e).ncard : ℝ) ≤ ((Nat.totient e / e : ℝ) * ((n + 1) - ((x.den : ℝ) * e / ((z.num * (x.den : ℤ) - x.num * (z.den : ℤ) : ℤ) : ℝ))) / z.den) + (e.divisors.card : ℝ) := by
    intro e he;
    convert! prim_prog_upper z.num z.den _ _ e _ _ _ _ using 1;
    · exact z.pos;
    · exact Int.isCoprime_iff_gcd_eq_one.mpr ( by simpa [ Int.gcd, Int.natAbs_abs ] using! z.reduced );
    · linarith [ Finset.mem_Icc.mp he ];
    · rw [ div_le_iff₀ ] <;> norm_cast;
      · rw [ ← @Int.cast_le ℝ ] at * ; simp_all +decide [ mul_comm, mul_left_comm, div_eq_mul_inv ];
        rw [ Nat.le_sub_iff_add_le ] at he;
        · contrapose! he;
          exact fun _ => Nat.lt_succ_of_le <| Nat.ceil_le.mpr <| by rw [ inv_mul_le_iff₀ <| Nat.cast_pos.mpr x.pos ] ; linarith;
        · omega;
      · rw [ Rat.lt_iff ] at hxz ; aesop;
  convert! Finset.sum_le_sum h_upper_bound using 1;
  norm_num [ Finset.sum_add_distrib, Finset.mul_sum _ _ _, Finset.sum_div, Sfun, errTerm ];
  erw [ Finset.sum_Ico_eq_sub _ ] <;> norm_num [ Finset.sum_range_succ' ];
  cases h : ⌈ ( ( n : ℝ ) + 1 ) / x.den * ( z.num * x.den - x.num * z.den ) ⌉₊ <;> simp_all +decide [ Finset.sum_range_succ' ];
  field_simp;
  exact Finset.sum_congr rfl fun _ _ => by ring;

/-
The mirror of `left_count_main` via the reflection `q ↦ 1-q`: for
`0 ≤ z < w ≤ 1`, the count over `(z, w)` is at least
`((n+1)/z.den) * S((n+1)*z.den*(w-z)) - errTerm (1-w) (1-z) n`.
-/
set_option maxHeartbeats 1000000 in
theorem right_count_main (z w : ℚ) (hz0 : 0 ≤ z) (hzw : z < w) (hw1 : w ≤ 1) (n : ℕ) :
    ((n : ℝ) + 1) / z.den * Sfun (((n : ℝ) + 1) * z.den * ((w : ℝ) - z))
      - errTerm (1 - w) (1 - z) n ≤ (betweenCount n z w : ℝ) := by
  convert! left_count_main ( 1 - w ) ( 1 - z ) _ _ _ n using 1;
  · congr! 1;
    congr! 2;
    · exact_mod_cast one_sub_den z |> Eq.symm;
    · rw [ div_mul_eq_mul_div, eq_div_iff ] <;> norm_cast <;> norm_num;
      rw [ ← Rat.mul_den_eq_num, ← Rat.mul_den_eq_num ] ; ring_nf;
      grind +suggestions;
  · rw [ Erdos1005.betweenCount_reflect ];
  · linarith;
  · linarith;
  · linarith

/-
The mirror of `left_count_upper` via `q ↦ 1-q`: for `0 <= z < w <= 1`,
`betweenCount n z w <= ((n+1)/z.den)*S((n+1)*z.den*(w-z)) + errTerm (1-w) (1-z) n`.
-/
set_option maxHeartbeats 1000000 in
theorem right_count_upper (z w : ℚ) (hzw : z < w) (n : ℕ) :
    (betweenCount n z w : ℝ) ≤ ((n : ℝ) + 1) / z.den * Sfun (((n : ℝ) + 1) * z.den * ((w : ℝ) - z))
      + errTerm (1 - w) (1 - z) n := by
  -- Apply `left_count_upper` to the reflected interval `(1-w, 1-z)`.
  have h_left_count_upper : (betweenCount n (1 - w) (1 - z) : ℝ) ≤ ((n + 1) / (1 - z).den) * Sfun ((n + 1) / (1 - w).den * ((1 - z).num * (1 - w).den - (1 - w).num * (1 - z).den)) + errTerm (1 - w) (1 - z) n := by
    convert! left_count_upper ( 1 - w ) ( 1 - z ) _ n using 1 <;> norm_num;
    · linarith;
  convert! h_left_count_upper using 2;
  · convert! betweenCount_reflect n z w using 1;
  · congr! 2;
    · rw [ one_sub_den ];
    · rw [ div_mul_eq_mul_div, eq_div_iff ] <;> norm_cast <;> norm_num [ Rat.den_nz ];
      rw [ ← Rat.mul_den_eq_num, ← Rat.mul_den_eq_num ] ; ring_nf;
      grind +suggestions

/-
`errTerm x z n ≤ M·(1 + log M)`, where `M = ⌈((n+1)/x.den)·u⌉₊` and
`u = z.num·x.den − x.num·z.den`.
-/
theorem errTerm_le (x z : ℚ) (n : ℕ) :
    errTerm x z n
      ≤ (⌈((n : ℝ) + 1) / x.den * ((z.num * (x.den : ℤ) - x.num * (z.den : ℤ) : ℤ) : ℝ)⌉₊ : ℝ)
          * (1 + Real.log (⌈((n : ℝ) + 1) / x.den * ((z.num * (x.den : ℤ) - x.num * (z.den : ℤ) : ℤ) : ℝ)⌉₊)) := by
  refine' le_trans _ ( divisor_sum_le _ );
  refine' Finset.sum_le_sum_of_subset_of_nonneg ( Finset.Icc_subset_Icc_right _ ) fun _ _ _ => Nat.cast_nonneg _;
  exact Nat.pred_le _

/-
If the reference `z` is a reduced rational strictly inside `(0,1)` and strictly
inside the elementary interval `(x, elemR x)` (with `0 ≤ x` and `elemR x ≤ 1`),
then the number of order-`n` Farey fractions in `(x, elemR x)` is at least `n/4`
minus the two error terms.
-/
theorem caseA_count (n : ℕ) (x z : ℚ) (hx0 : 0 ≤ x) (helemR1 : elemR x ≤ 1)
    (hz0 : 0 < z) (hz1 : z < 1) (hxz : x < z) (hzR : z < elemR x)
    (hmuL : (x.den : ℝ) ≤ (n : ℝ) + 1) :
    (n : ℝ) / 4 - errTerm x z n - errTerm (1 - elemR x) (1 - z) n
      ≤ (betweenCount n x (elemR x) : ℝ) := by
  -- From `0 < z < 1` reduced: `z.num ≥ 1` and `z.num < z.den`, so `z.den ≥ 2`.
  have hzden_ge_two : 2 ≤ z.den := by
    rw [ Rat.lt_iff ] at * ; norm_num at *;
    linarith [ show z.num > 0 from Rat.num_pos.mpr hz0 ];
  -- Note that from `0 ≤ x` and `x.den > 0` (by `Rat.den_pos`), `x.den ≥ 2`.
  have hxden_ge_two : 2 ≤ x.den := by
    contrapose! hzR; interval_cases _ : x.den <;> simp_all +decide [ elemR ] ;
    grind;
  -- From `x < z` reduced and `z.num ≥ 1` (by `Rat.num_pos.mpr`), `u = z.num * x.den - x.num * z.den > 0`.
  set u := z.num * x.den - x.num * z.den with hu
  have hu_pos : 0 < u := by
    exact sub_pos_of_lt ( by rw [ Rat.lt_iff ] at *; linarith );
  -- From `z < elemR x`, `v = (x.num + 1) * z.den - (x.den - 1) * z.num > 0`.
  set v := (x.num + 1) * z.den - (x.den - 1) * z.num with hv
  have hv_pos : 0 < v := by
    contrapose! hzR;
    unfold elemR;
    rw [ div_le_iff₀ ] <;> norm_cast at *;
    · rw [ ← Rat.num_div_den z ];
      rw [ div_mul_eq_mul_div, le_div_iff₀ ] <;> norm_cast at *;
      · grind;
      · positivity;
    · grind +splitIndPred;
  -- The arguments of `Sfun` satisfy `argL ≥ u` and `argR ≥ v`.
  have hargL_ge_u : ((n + 1 : ℝ) / x.den) * u ≥ u := by
    exact le_mul_of_one_le_left ( by positivity ) ( by rw [ le_div_iff₀ ( by positivity ) ] ; linarith )
  have hargR_ge_v : ((n + 1 : ℝ) * z.den * (elemR x - z)) ≥ v := by
    -- By definition of `elemR`, we have `elemR x = (x.num + 1) / (x.den - 1)`.
    have h_elemR : (elemR x : ℝ) = (x.num + 1) / (x.den - 1) := by
      unfold elemR; norm_num;
    simp_all +decide [ Rat.cast_def ];
    rw [ div_sub_div, mul_div, div_add', le_div_iff₀ ] <;> try nlinarith [ ( by norm_cast : ( 2 : ℝ ) ≤ x.den ), ( by norm_cast : ( 2 : ℝ ) ≤ z.den ) ];
    norm_cast at *;
    norm_num [ Int.subNatNat_eq_coe ] at * ; nlinarith [ mul_le_mul_of_nonneg_left hmuL ( show 0 ≤ z.den by positivity ) ];
  -- By `Sfun_ge_int`, `Sfun argL ≥ Sfun u.toNat` and `Sfun argR ≥ Sfun v.toNat`.
  have hSfun_ge_u : Sfun (((n + 1 : ℝ) / x.den) * u) ≥ Sfun u.toNat := by
    convert! Sfun_ge_int _ _ using 1;
    · linarith [ Int.toNat_of_nonneg hu_pos.le ];
    · convert! hargL_ge_u.le using 1;
      exact_mod_cast Int.toNat_of_nonneg hu_pos.le
  have hSfun_ge_v : Sfun (((n + 1 : ℝ) * z.den * (elemR x - z))) ≥ Sfun v.toNat := by
    convert! Sfun_ge_int _ _ using 1;
    · grind;
    · exact le_trans ( mod_cast by rw [ Int.toNat_of_nonneg hv_pos.le ] ) hargR_ge_v;
  -- By `Sfun_pair_ge`, `Sfun u.toNat + Sfun v.toNat ≥ z.den / 4`.
  have hSfun_pair_ge : Sfun u.toNat + Sfun v.toNat ≥ (z.den : ℝ) / 4 := by
    have hSfun_pair_ge : u.toNat + v.toNat ≥ z.den + 1 := by
      linarith [ Int.toNat_of_nonneg hu_pos.le, Int.toNat_of_nonneg hv_pos.le, show z.num ≥ 1 from Rat.num_pos.mpr hz0 ];
    convert! Sfun_pair_ge u.toNat v.toNat _ _ z.den _ _ using 1 <;> norm_cast;
    · linarith [ Int.toNat_of_nonneg hu_pos.le ];
    · grind;
  -- By `left_count_main` and `right_count_main`, we have:
  have h_left_count : (betweenCount n x z : ℝ) ≥ ((n + 1 : ℝ) / z.den) * Sfun (((n + 1 : ℝ) / x.den) * u) - errTerm x z n := by
    apply left_count_main x z hx0 hxz hz1.le n
  have h_right_count : (betweenCount n z (elemR x) : ℝ) ≥ ((n + 1 : ℝ) / z.den) * Sfun (((n + 1 : ℝ) * z.den * (elemR x - z))) - errTerm (1 - elemR x) (1 - z) n := by
    convert! right_count_main z ( elemR x ) hz0.le hzR helemR1 n using 1;
  -- By `betweenCount_split`, we have:
  have h_betweenCount_split : (betweenCount n x (elemR x) : ℝ) ≥ (betweenCount n x z : ℝ) + (betweenCount n z (elemR x) : ℝ) := by
    exact_mod_cast betweenCount_split n x z ( elemR x ) hxz.le hzR.le;
  nlinarith [ show ( z.den : ℝ ) ≥ 2 by norm_cast, show ( x.den : ℝ ) ≥ 2 by norm_cast, mul_div_cancel₀ ( ( n : ℝ ) + 1 ) ( by positivity : ( z.den : ℝ ) ≠ 0 ) ]

/-
If the reference `z` lies to the right of the elementary interval with `0 ≤ x`,
`x.num ≤ x.den - 2`, `|I| = elemR x - x ≥ 1/x.den`, and `2 ≤ (n+1)·z.den·(z - x)`,
then the number of order-`n` Farey fractions in `(x, elemR x)` is at least `n/4`
minus the two error terms and one.
-/
theorem caseB_count (n : ℕ) (x z : ℚ) (hx0 : 0 ≤ x)
    (hxR : x < elemR x) (hRz : elemR x < z) (hz1 : z ≤ 1)
    (hbn : (x.den : ℝ) ≤ n) (hIb : (1 : ℝ) / x.den ≤ (elemR x : ℝ) - x)
    (h2X : (2 : ℝ) ≤ ((n : ℝ) + 1) * z.den * ((z : ℝ) - x)) :
    (n : ℝ) / 4 - errTerm x z n - errTerm (elemR x) z n - 1
      ≤ (betweenCount n x (elemR x) : ℝ) := by
  have h_caseB : (betweenCount n x (elemR x) : ℝ) ≥ (n : ℝ) / 4 - errTerm x z n - errTerm (elemR x) z n - 1 := by
    have h1 := betweenCount_split_le n x (elemR x) z
    have h2 := left_count_main x z hx0 (by
    linarith) (by
    linarith) n
    have h3 := left_count_upper (elemR x) z (by
    linarith) n
    -- Combining 1–4: `betweenCount n x (elemR x) ≥ ((n:ℝ)+1)/s * (Sfun argX - Sfun argE) - errTerm x z n - errTerm (elemR x) z n - 1`.
    have h4 : (n : ℝ) / 4 ≤ ((n : ℝ) + 1) / z.den * (Sfun ((n + 1) * z.den * (z - x)) - Sfun ((n + 1) * z.den * (z - elemR x))) := by
      convert! caseB_ratio_ge n z.den ( mod_cast z.pos ) ( ( n + 1 ) * z.den * ( z - x ) ) ( ( n + 1 ) * z.den * ( z - elemR x ) ) _ _ _ _ using 1;
      · exact mul_nonneg ( mul_nonneg ( by positivity ) ( Nat.cast_nonneg _ ) ) ( sub_nonneg.mpr ( mod_cast hRz.le ) );
      · convert! h2X using 1;
      · have h_caseB : (n + 1 : ℝ) * z.den * (elemR x - x) ≥ z.den := by
          refine' le_trans _ ( mul_le_mul_of_nonneg_left hIb <| by positivity );
          rw [ mul_one_div, le_div_iff₀ ] <;> norm_cast at * <;> nlinarith [ x.pos ];
        nlinarith only [h_caseB]
      · field_simp;
        rw [ div_le_iff₀ ] at hIb <;> norm_num at *;
        · nlinarith [ show ( x.den : ℝ ) ≤ n by norm_cast, show ( x.den : ℝ ) ≥ 1 by exact_mod_cast x.pos ];
        · exact x.pos;
    have h5 : (n + 1 : ℝ) / x.den * (z.num * x.den - x.num * z.den : ℝ) = (n + 1) * z.den * (z - x) ∧ (n + 1 : ℝ) / (elemR x).den * (z.num * (elemR x).den - (elemR x).num * z.den : ℝ) = (n + 1) * z.den * (z - elemR x) := by
      constructor <;> rw [ div_mul_eq_mul_div, div_eq_iff ] <;> norm_cast <;> norm_num [ Rat.num_div_den ]; all_goals rw [ ← Rat.mul_den_eq_num, ← Rat.mul_den_eq_num ] ; ring;
    simp_all +decide [ errTerm ];
    linarith [ ( by norm_cast : ( betweenCount n x z : ℝ ) ≤ betweenCount n x ( elemR x ) + betweenCount n ( elemR x ) z + 1 ) ];
  exact h_caseB

/-
Mirror of `caseB_count` with the reference `z` to the left (`0 ≤ z < x`).
-/
theorem caseB_count_left (n : ℕ) (x z : ℚ) (hz0 : 0 ≤ z) (hzx : z < x) (helemR1 : elemR x ≤ 1)
    (hxR : x < elemR x) (hbn : (x.den : ℝ) ≤ n) (hIb : (1 : ℝ) / x.den ≤ (elemR x : ℝ) - x)
    (h2X : (2 : ℝ) ≤ ((n : ℝ) + 1) * z.den * ((elemR x : ℝ) - z)) :
    (n : ℝ) / 4 - errTerm (1 - elemR x) (1 - z) n - errTerm (1 - x) (1 - z) n - 1
      ≤ (betweenCount n x (elemR x) : ℝ) := by
  -- Apply the two right-count lemmas, then `caseB_ratio_ge`, then `linarith`.
  have := @caseB_ratio_ge n;
  specialize this z.den (mod_cast z.pos) ((n + 1) * z.den * (elemR x - z)) ((n + 1) * z.den * (x - z)) ?_ ?_ ?_ ?_;
  · exact mul_nonneg ( mul_nonneg ( by positivity ) ( Nat.cast_nonneg _ ) ) ( sub_nonneg.mpr ( mod_cast hzx.le ) );
  · convert! h2X using 1;
  · rw [ div_le_iff₀ ( Nat.cast_pos.mpr <| Nat.pos_of_ne_zero x.den_nz ) ] at hIb;
    rw [ ← mul_sub ];
    rw [ mul_right_comm ];
    exact le_mul_of_one_le_left ( Nat.cast_nonneg _ ) ( by nlinarith [ show ( x.den : ℝ ) ≥ 1 by exact_mod_cast x.pos, show ( z.den : ℝ ) ≥ 1 by exact_mod_cast z.pos ] );
  · field_simp;
    rw [ div_le_iff₀ ] at hIb <;> norm_num at *;
    · nlinarith [ show ( x.den : ℝ ) ≤ n by norm_cast, show ( x.den : ℝ ) ≥ 1 by exact_mod_cast x.pos ];
    · exact x.pos;
  · have h_betweenCount_split : (betweenCount n z (elemR x) : ℝ) ≤ (betweenCount n z x : ℝ) + (betweenCount n x (elemR x) : ℝ) + 1 := by
      exact_mod_cast betweenCount_split_le n z x ( elemR x );
    have := right_count_main z (elemR x) hz0 (hzx.trans hxR) helemR1 n
    have := right_count_upper z x hzx n
    linarith

/-! # Final assembly of the elementary-interval lower bound

We prove `elem_interval_count_lower_final` by splitting on the size of `b = x.den`:

* **Small `b`** (`b*b < n`): the interval `I_{a,b}` has length `> 1/b > 1/√n`, so the
  crude density bound `density_count_lower` already gives a count `≥ (n+1)√n/4 - n(1+log n)`,
  which dominates `(1/4-ε)n`.

* **Large `b`** (`n ≤ b*b`): choose `Q` with `Q^3 ≤ n ≤ Q^4` (so `Q ≤ n^{1/3} < √n ≤ b`).
  The reference rational `z` is chosen by the Farey–gap dichotomy at order `Q`, and the count
  is bounded via `caseA_count` / `caseB_count` / `caseB_count_left` / `left_count_main`,
  with the error terms controlled uniformly by `Q ≤ n^{1/3}`.
-/

/-- Uniform ceiling used to bound every error term arising in the large-`b` case. -/
noncomputable def Kmax (n Q : ℕ) : ℕ :=
  ⌈(4 * ((n : ℝ) + 1) * (Q : ℝ)) / Real.sqrt n⌉₊ + 2

/-- `n`-only upper bound for `Kmax n Q` when `Q ≤ n^{1/3}` (i.e. `Q^3 ≤ n`). -/
noncomputable def Kbar (n : ℕ) : ℕ :=
  ⌈(4 * ((n : ℝ) + 1)) * (n : ℝ) ^ ((1 : ℝ) / 3) / Real.sqrt n⌉₊ + 2

/-
Derived facts for the left endpoint of a badly ordered pair.
`a = x.num ≥ 1`, `b = x.den ≥ 4`, `a + 3 ≤ b`, `0 < x < elemR x < 1`, `b ≤ n`.
-/
theorem badly_left_facts {n : ℕ} {x : ℚ} (h : ∃ y, BadlyOrdered n x y) :
    0 < x ∧ x < elemR x ∧ elemR x < 1 ∧ 4 ≤ x.den ∧ x.den ≤ n ∧
      1 ≤ x.num ∧ x.num + 3 ≤ (x.den : ℤ) := by
  have := h.choose_spec.1.2.2;
  obtain ⟨y, hy⟩ := h
  have hxy : x < y := by
    exact hy.2.2.1
  have hxy' : x.num < y.num := by
    exact hy.2.2.2.1
  have hyx' : y.den < x.den := by
    exact hy.2.2.2.2
  have hx_pos : 0 < x := by
    by_cases hx_zero : x = 0;
    · aesop;
    · exact lt_of_le_of_ne ( hy.1.1 ) ( Ne.symm hx_zero )
  have hx_lt_elemR : x < elemR x := by
    unfold elemR;
    rw [ lt_div_iff₀ ] <;> norm_num;
    · have := Rat.num_div_den x;
      rw [ ← this ] ; ring_nf ; norm_num [ hx_pos.ne' ];
      exact neg_lt_iff_pos_add'.mpr ( by positivity );
    · linarith [ y.pos ]
  have h_elemR_lt_1 : elemR x < 1 := by
    have h_elemR_lt_1 : elemR x ≤ y := by
      apply elemR_le; assumption;
    exact lt_of_le_of_lt h_elemR_lt_1 ( hy.2.1.2.1.lt_of_ne ( by rintro rfl; exact absurd hxy' ( by norm_num; linarith [ Rat.num_pos.mpr hx_pos ] ) ) )
  have hx_den_ge_4 : 4 ≤ x.den := by
    by_contra h_contra;
    interval_cases _ : x.den <;> simp_all +decide [ elemR ];
    · grind;
    · linarith [ show ( x.num : ℚ ) ≥ 1 by exact_mod_cast Rat.num_pos.mpr hx_pos ]
  have hx_num_ge_1 : 1 ≤ x.num := by
    exact Rat.num_pos.mpr hx_pos
  have hx_num_plus_3_le_den : x.num + 3 ≤ x.den := by
    unfold elemR at *;
    rw [ div_lt_iff₀ ] at h_elemR_lt_1 <;> norm_cast at *;
    · rw [ Int.subNatNat_eq_coe ] at h_elemR_lt_1 ; omega;
    · rw [ Int.subNatNat_eq_coe ] ; norm_num ; linarith
  exact ⟨hx_pos, hx_lt_elemR, h_elemR_lt_1, hx_den_ge_4, this, hx_num_ge_1, hx_num_plus_3_le_den⟩

/-
The elementary interval length exceeds `1/b`.
-/
theorem elemR_sub_gt {x : ℚ} (hb : 4 ≤ x.den) (ha : 1 ≤ x.num) :
    (1 : ℝ) / (x.den : ℝ) < (elemR x : ℝ) - (x : ℝ) := by
  rw [ div_lt_iff₀ ( by positivity ) ];
  rw [ show elemR x = ( x.num + 1 ) / ( x.den - 1 ) from ?_, show ( x : ℝ ) = x.num / x.den from ?_ ];
  · field_simp;
    rw [ lt_sub_iff_add_lt, lt_iff_not_ge ] ; norm_cast;
    rw [ Rat.divInt_eq_div, div_mul_eq_mul_div, div_le_iff₀ ] <;> norm_cast;
    · grind +extAll;
    · grind +locals;
  · exact_mod_cast x.num_div_den.symm;
  · unfold elemR; norm_num;

/-
**Small-`b` bound.** If `b*b < n` then the count in the elementary interval is at least
`(n+1)√n/4 - n(1+log n)` (independent of `x`).
-/
theorem smallb_bound {n : ℕ} {x : ℚ} (h : ∃ y, BadlyOrdered n x y)
    (hsmall : x.den * x.den < n) :
    ((n : ℝ) + 1) * Real.sqrt n / 4 - (n : ℝ) * (1 + Real.log n)
      ≤ (betweenCount n x (elemR x) : ℝ) := by
  convert! density_count_lower n x ( elemR x ) _ _ _ |> le_trans _ using 1;
  · have h_elemR_sub : 1 / (x.den : ℝ) < (elemR x : ℝ) - (x : ℝ) := by
      convert! elemR_sub_gt _ _;
      · exact badly_left_facts h |>.2.2.2.1;
      · have := badly_left_facts h; aesop;
    gcongr;
    refine' le_trans _ ( mul_le_mul_of_nonneg_right h_elemR_sub.le _ );
    · rw [ div_mul_eq_mul_div, div_le_div_iff₀ ] <;> norm_cast;
      · norm_num ; nlinarith [ sq_nonneg ( Real.sqrt n - x.den : ℝ ), Real.mul_self_sqrt ( Nat.cast_nonneg n ), ( by norm_cast : ( x.den :ℝ ) * x.den + 1 ≤ n ) ];
      · exact x.pos;
    · positivity;
  · exact h.choose_spec.1.1;
  · exact badly_left_facts h |>.2.2.1.le;
  · exact badly_left_facts h |>.2.1

/-
Existence of a suitable order `Q` for the large-`b` case.
-/
theorem largeb_Q_exists (n : ℕ) (hn : 81 ≤ n) :
    ∃ Q : ℕ, 3 ≤ Q ∧ Q ^ 3 ≤ n ∧ n ≤ Q ^ 4 := by
  -- By definition of $Q$, we know that $Q^3 \leq n$.
  obtain ⟨Q, hQ⟩ : ∃ Q : ℕ, 3 ≤ Q ∧ Q^3 ≤ n ∧ (Q + 1)^3 > n := by
    obtain ⟨Q, hQ⟩ : ∃ Q : ℕ, Q^3 ≤ n ∧ n < (Q + 1)^3 := by
      use Nat.floor (Real.rpow n (1/3 : ℝ));
      norm_num +zetaDelta at *;
      exact ⟨ by rw [ ← @Nat.cast_le ℝ ] ; push_cast; exact le_trans ( pow_le_pow_left₀ ( by positivity ) ( Nat.floor_le ( by positivity ) ) _ ) ( by rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( by positivity ) ] ; norm_num ), by rw [ ← @Nat.cast_lt ℝ ] ; push_cast; exact lt_of_le_of_lt ( by rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( by positivity ) ] ; norm_num ) ( pow_lt_pow_left₀ ( Nat.lt_floor_add_one _ ) ( by positivity ) ( by positivity ) ) ⟩;
    exact ⟨ Q, le_of_not_gt fun h => by interval_cases Q <;> linarith, hQ.1, hQ.2 ⟩
  use Q, hQ.left, hQ.right.left, by
    nlinarith [ Nat.pow_le_pow_left hQ.1 2 ]

/-
The determinant `z.num·x.den − x.num·z.den` equals `x.den · z.den · (z − x)`.
-/
theorem det_real_eq (x z : ℚ) :
    ((z.num * (x.den : ℤ) - x.num * (z.den : ℤ) : ℤ) : ℝ)
      = (z.den : ℝ) * (x.den : ℝ) * ((z : ℝ) - (x : ℝ)) := by
  rw [ Rat.cast_def, Rat.cast_def ] ; ring_nf;
  simp +decide [ mul_assoc, mul_comm, mul_left_comm, ne_of_gt x.pos, ne_of_gt z.pos ]

/-
Ceiling comparison against the uniform bound `Kmax`.
-/
theorem ceil_le_Kmax {n Q : ℕ} (A : ℝ)
    (hA : A ≤ (4 * ((n : ℝ) + 1) * (Q : ℝ)) / Real.sqrt n) : ⌈A⌉₊ ≤ Kmax n Q := by
  exact Nat.le_succ_of_le ( Nat.le_succ_of_le ( Nat.ceil_mono hA ) )

/-
An error term is bounded by the uniform quantity `Kmax·(1+log Kmax)` provided its
defining ceiling is `≤ Kmax`.
-/
theorem errTerm_le_Kmax {n Q : ℕ} (x z : ℚ)
    (hM : ⌈((n : ℝ) + 1) / x.den * ((z.num * (x.den : ℤ) - x.num * (z.den : ℤ) : ℤ) : ℝ)⌉₊
            ≤ Kmax n Q) :
    errTerm x z n ≤ (Kmax n Q : ℝ) * (1 + Real.log (Kmax n Q)) := by
  refine' le_trans ( errTerm_le x z n ) _;
  by_cases h : ⌈ ( n + 1 : ℝ ) / x.den * ( z.num * x.den - x.num * z.den ) ⌉₊ = 0 <;> simp_all +decide [ mul_add ];
  · rw [ Nat.ceil_eq_zero.mpr h ] ; norm_num;
    exact add_nonneg ( Nat.cast_nonneg _ ) ( mul_nonneg ( Nat.cast_nonneg _ ) ( Real.log_nonneg ( mod_cast Nat.one_le_iff_ne_zero.mpr ( by unfold Kmax; positivity ) ) ) );
  · gcongr; all_goals exact Nat.ceil_le.mpr hM

/-
**Large-`b`, Case I.** The right endpoint `elemR x` is itself a low-order Farey fraction
(`(elemR x).den ≤ Q`). Apply `left_count_main` with reference `z = elemR x`.
-/
theorem largeb_caseI {n Q : ℕ} {x : ℚ} (h : ∃ y, BadlyOrdered n x y)
    (hbig : n ≤ x.den * x.den)
    (hsw : (elemR x).den ≤ Q) :
    (n : ℝ) / 4 - 2 * ((Kmax n Q : ℝ) * (1 + Real.log (Kmax n Q))) - 1
      ≤ (betweenCount n x (elemR x) : ℝ) := by
  -- Let's obtain the necessary facts from `h`.
  obtain ⟨hx0, hxz, hz1, hb, ha, hab⟩ := badly_left_facts h;
  -- Let's simplify the expression for `det`.
  have hdet : (elemR x).num * (x.den : ℤ) - x.num * (elemR x).den = (elemR x).den + (elemR x).num := by
    unfold elemR; norm_num;
    have := Rat.num_div_den ( ( x.num + 1 : ℚ ) / ( x.den - 1 ) );
    rw [ div_eq_div_iff ] at this <;> norm_cast at * <;> simp_all +decide [ sub_eq_iff_eq_add ];
    · rw [ Int.subNatNat_eq_coe ] at * ; push_cast at * ; linarith;
    · grind +splitImp;
  -- Let's simplify the expression for `argX`.
  set argX := ((n + 1 : ℝ) / x.den) * ((elemR x).num * (x.den : ℤ) - x.num * (elemR x).den : ℝ) with hargX_def
  have hargX_ge_two : 2 ≤ argX := by
    -- Since $w.num \geq 1$ and $w.den \geq 1$, we have $w.den + w.num \geq 2$.
    have h_det_ge_two : (elemR x).den + (elemR x).num ≥ 2 := by
      linarith [ Rat.num_pos.mpr ( show 0 < elemR x from lt_trans hx0 hxz ), Rat.den_pos ( elemR x ) ];
    refine' le_trans _ ( mul_le_mul_of_nonneg_left ( show ( ( elemR x |> Rat.num ) : ℝ ) * x.den - x.num * ( elemR x |> Rat.den ) ≥ 2 by exact_mod_cast hdet.symm ▸ h_det_ge_two ) ( by positivity ) );
    rw [ div_mul_eq_mul_div, le_div_iff₀ ] <;> norm_cast <;> nlinarith only [ hb, ha, hbig ]
  have hargX_le_4Q : argX ≤ 4 * (n + 1) * Q / Real.sqrt n := by
    -- By `elemR_sub_gt` (with the facts): 1/b < (w:ℝ)-x. Also (w:ℝ)-x < 2/b: indeed (w:ℝ)-x = (a+b)/(b(b-1)) (cast elemR) and a+3≤b gives a+b < 2(b-1), so (a+b)/(b(b-1)) < 2/b.
    have h_diff_bounds : 1 / (x.den : ℝ) < (elemR x : ℝ) - x ∧ (elemR x : ℝ) - x < 2 / (x.den : ℝ) := by
      convert! elemR_sub_gt hb hab.1 using 1;
      norm_num [ elemR ];
      rw [ Rat.cast_def ] ; ring_nf;
      intro h; nlinarith [ show ( x.den : ℝ ) ≥ 4 by norm_cast, inv_pos.mpr ( show ( x.den : ℝ ) > 0 by positivity ), inv_pos.mpr ( show ( -1 + x.den : ℝ ) > 0 by linarith [ show ( x.den : ℝ ) ≥ 4 by norm_cast ] ), mul_inv_cancel₀ ( show ( x.den : ℝ ) ≠ 0 by positivity ), mul_inv_cancel₀ ( show ( -1 + x.den : ℝ ) ≠ 0 by linarith [ show ( x.den : ℝ ) ≥ 4 by norm_cast ] ), show ( x.num : ℝ ) ≥ 1 by exact_mod_cast hab.1, show ( x.num : ℝ ) + 3 ≤ x.den by exact_mod_cast hab.2 ] ;
    -- Substitute the bounds for `w - x` into the expression for `argX`.
    have h_argX_bounds : argX ≤ (n + 1 : ℝ) * (elemR x).den * (2 / (x.den : ℝ)) := by
      have h_argX_bounds : argX = (n + 1 : ℝ) * (elemR x).den * ((elemR x : ℝ) - x) := by
        have := det_real_eq x ( elemR x ) ; simp_all +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm ] ;
        rw [ inv_mul_eq_div, div_eq_iff ] <;> norm_cast at * <;> simp_all +decide [ sub_eq_iff_eq_add ] ;
        ring;
      exact h_argX_bounds.symm ▸ mul_le_mul_of_nonneg_left h_diff_bounds.2.le ( by positivity );
    -- Since $x.den \geq \sqrt{n}$, we have $2 / x.den \leq 2 / \sqrt{n}$.
    have h_den_sqrt : (x.den : ℝ) ≥ Real.sqrt n := by
      exact Real.sqrt_le_iff.mpr ⟨ by positivity, by norm_cast; linarith ⟩;
    refine le_trans h_argX_bounds ?_;
    field_simp;
    rw [ le_div_iff₀ ( Real.sqrt_pos.mpr <| Nat.cast_pos.mpr <| by linarith ) ];
    nlinarith only [ show ( elemR x |> Rat.den : ℝ ) ≤ Q by exact_mod_cast hsw, show ( x.den : ℝ ) ≥ Real.sqrt n by exact h_den_sqrt, Real.sqrt_nonneg n, Real.sq_sqrt <| Nat.cast_nonneg n ];
  -- Let's simplify the expression for `main`.
  have hmain_ge_n_div_4 : ((n + 1 : ℝ) / (elemR x).den) * Sfun argX ≥ (n : ℝ) / 4 := by
    have hmain_ge_n_div_4 : ((n + 1 : ℝ) / (elemR x).den) * Sfun argX ≥ ((n + 1 : ℝ) / (elemR x).den) * (argX / 4) := by
      gcongr;
      convert! Sfun_increment_ge_two ( show 0 ≤ 0 by norm_num ) ( show 2 ≤ argX by linarith ) |> le_trans <| le_rfl using 1 ; norm_num [ Sfun_eq_zero_of_lt_one ];
    have hmain_ge_n_div_4 : ((n + 1 : ℝ) / (elemR x).den) * (argX / 4) = ((n + 1 : ℝ) ^ 2 * ((elemR x : ℝ) - x)) / 4 := by
      have hmain_ge_n_div_4 : ((elemR x).num * (x.den : ℤ) - x.num * (elemR x).den : ℝ) = (elemR x).den * (x.den : ℝ) * ((elemR x : ℝ) - x) := by
        convert! det_real_eq x ( elemR x ) using 1;
        norm_num;
      grind +qlia;
    have hmain_ge_n_div_4 : ((n + 1 : ℝ) ^ 2 * ((elemR x : ℝ) - x)) / 4 ≥ (n : ℝ) / 4 := by
      have hmain_ge_n_div_4 : (elemR x : ℝ) - x > 1 / (x.den : ℝ) := by
        apply elemR_sub_gt hb hab.left;
      refine' le_trans _ ( div_le_div_of_nonneg_right ( mul_le_mul_of_nonneg_left hmain_ge_n_div_4.le <| sq_nonneg _ ) zero_le_four );
      field_simp;
      norm_cast ; nlinarith only [ ha, hb, hbig ];
    linarith;
  -- Let's simplify the expression for `errTerm`.
  have herrTerm_le_Kmax : errTerm x (elemR x) n ≤ (Kmax n Q : ℝ) * (1 + Real.log (Kmax n Q)) := by
    apply errTerm_le_Kmax;
    convert! ceil_le_Kmax _ hargX_le_4Q using 1;
    norm_num [ hargX_def ];
  have := left_count_main x ( elemR x ) ( le_of_lt hx0 ) hxz ( le_of_lt hz1 ) n;
  simp_all +decide [ errTerm ];
  rw [ show ( elemR x |> Rat.den : ℝ ) + ( elemR x |> Rat.num : ℝ ) = ( elemR x |> Rat.num : ℝ ) * x.den - x.num * ( elemR x |> Rat.den : ℝ ) by exact mod_cast hdet.symm ] at * ; linarith [ show ( 0 :ℝ ) ≤ Kmax n Q * ( 1 + Real.log ( Kmax n Q ) ) by exact mul_nonneg ( Nat.cast_nonneg _ ) ( add_nonneg zero_le_one ( Real.log_nonneg ( mod_cast Nat.one_le_iff_ne_zero.mpr <| by unfold Kmax; positivity ) ) ) ] ;

/-
**Large-`b`, Case II.** Some order-`Q` Farey fraction `z` lies strictly inside the
elementary interval. Apply `caseA_count`.
-/
theorem largeb_caseII {n Q : ℕ} {x : ℚ} (h : ∃ y, BadlyOrdered n x y)
    (hQ : 3 ≤ Q) (hQ3 : Q ^ 3 ≤ n) (hbig : n ≤ x.den * x.den)
    (z : ℚ) (hzF : IsFarey Q z) (hxz : x < z) (hzR : z < elemR x) :
    (n : ℝ) / 4 - 2 * ((Kmax n Q : ℝ) * (1 + Real.log (Kmax n Q))) - 1
      ≤ (betweenCount n x (elemR x) : ℝ) := by
  -- We have $errTerm x z n \leq Kmax n Q * (1 + Real.log (Kmax n Q))$ and $errTerm (1 - elemR x) (1 - z) n \leq Kmax n Q * (1 + Real.log (Kmax n Q))$.
  have h_errTerm_xz : errTerm x z n ≤ (Kmax n Q : ℝ) * (1 + Real.log (Kmax n Q)) := by
    apply errTerm_le_Kmax;
    refine' Nat.ceil_le.mpr _;
    have h_det_bound : ((n : ℝ) + 1) * (z.den : ℝ) * ((z : ℝ) - x) ≤ 4 * ((n : ℝ) + 1) * (Q : ℝ) / Real.sqrt n := by
      have h_det_bound : ((z : ℝ) - x) < 2 / (x.den : ℝ) := by
        have h_det_bound : (elemR x : ℝ) - x < 2 / (x.den : ℝ) := by
          unfold elemR; norm_num; ring_nf;
          have := badly_left_facts h; rcases this with ⟨ hx₀, hx₁, hx₂, hx₃, hx₄, hx₅, hx₆ ⟩ ; rw [ Rat.cast_def ] ; ring_nf ;
          field_simp;
          rw [ div_sub_one, mul_div, ← add_div, div_lt_iff₀ ] <;> nlinarith only [ show ( x.den : ℝ ) ≥ 4 by norm_cast, show ( x.num : ℝ ) ≥ 1 by norm_cast, show ( x.num : ℝ ) + 3 ≤ x.den by norm_cast ];
        exact lt_of_le_of_lt ( sub_le_sub_right ( mod_cast hzR.le ) _ ) h_det_bound;
      have h_det_bound : ((n : ℝ) + 1) * (z.den : ℝ) * (2 / (x.den : ℝ)) ≤ 4 * ((n : ℝ) + 1) * (Q : ℝ) / Real.sqrt n := by
        have h_det_bound : (z.den : ℝ) ≤ Q ∧ (x.den : ℝ) ≥ Real.sqrt n := by
          exact ⟨ mod_cast hzF.2.2, Real.sqrt_le_iff.mpr ⟨ by positivity, by norm_cast; linarith ⟩ ⟩;
        field_simp;
        rw [ le_div_iff₀ ] <;> nlinarith [ show 0 < Real.sqrt n by exact Real.sqrt_pos.mpr ( Nat.cast_pos.mpr ( by nlinarith [ pow_succ' Q 2 ] ) ), show ( Q : ℝ ) ≥ 3 by norm_cast, show ( z.den : ℝ ) ≤ Q by exact_mod_cast h_det_bound.1, show ( x.den : ℝ ) ≥ Real.sqrt n by exact_mod_cast h_det_bound.2 ];
      exact le_trans ( mul_le_mul_of_nonneg_left ( le_of_lt ‹_› ) ( by positivity ) ) h_det_bound;
    convert! h_det_bound.trans _ using 1;
    · simp +decide [ Rat.cast_def, mul_sub, sub_mul, mul_assoc, mul_comm, mul_left_comm, div_eq_mul_inv ];
    · exact le_trans ( Nat.le_ceil _ ) ( by norm_num [ Kmax ] )
  have h_errTerm_1w_1z : errTerm (1 - elemR x) (1 - z) n ≤ (Kmax n Q : ℝ) * (1 + Real.log (Kmax n Q)) := by
    apply errTerm_le_Kmax;
    refine' ceil_le_Kmax _ _;
    have h_det : ((n : ℝ) + 1) / (1 - elemR x).den * ((1 - z).num * (1 - elemR x).den - (1 - elemR x).num * (1 - z).den : ℤ) = (n + 1) * z.den * ((elemR x : ℝ) - z) := by
      have := det_real_eq ( 1 - elemR x ) ( 1 - z ) ; simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ] ;
      rw [ ← mul_assoc, mul_div_cancel₀ _ ( Nat.cast_ne_zero.mpr <| Rat.den_nz _ ) ];
    have h_det_bound : (elemR x : ℝ) - z < 2 / x.den := by
      have h_det_bound : (elemR x : ℝ) - x < 2 / x.den := by
        have := badly_left_facts h
        unfold elemR; norm_num; ring_nf;
        rw [ Rat.cast_def ];
        field_simp;
        rw [ div_sub', div_lt_iff₀ ] <;> nlinarith [ show ( x.den : ℝ ) ≥ 4 by norm_cast; linarith, show ( x.num : ℝ ) ≥ 1 by norm_cast; linarith, show ( x.num : ℝ ) + 3 ≤ x.den by norm_cast; linarith ];
      exact lt_of_le_of_lt ( sub_le_sub_left ( mod_cast hxz.le ) _ ) h_det_bound;
    have h_det_bound : (n + 1) * z.den * ((elemR x : ℝ) - z) ≤ (n + 1) * Q * (2 / x.den) := by
      gcongr;
      · exact sub_nonneg_of_le <| mod_cast hzR.le;
      · exact hzF.2.2;
    have h_det_bound : (n + 1) * Q * (2 / x.den) ≤ 4 * (n + 1) * Q / Real.sqrt n := by
      field_simp;
      rw [ le_div_iff₀ ] <;> norm_num;
      · nlinarith only [ show ( n : ℝ ) ≤ x.den * x.den by norm_cast, Real.mul_self_sqrt ( Nat.cast_nonneg n ), show ( x.den : ℝ ) ≥ 1 by exact_mod_cast x.pos ];
      · exact Nat.pos_of_ne_zero ( by rintro rfl; linarith [ pow_pos ( by linarith : 0 < Q ) 3 ] );
    grind +splitImp;
  convert! caseA_count n x z _ _ _ _ _ _ _ |> le_trans _ using 1;
  any_goals linarith [ badly_left_facts h ];
  exact_mod_cast Nat.le_succ_of_le ( show x.den ≤ n from by nlinarith [ show x.den ≤ n from by { obtain ⟨ y, hy ⟩ := h; exact hy.1.2.2 } ] )

/-
**Case III-a** (small endpoint on the right). The reference is `gR`, the smaller-denominator
endpoint of the `F_Q`-gap `gL < gR` containing `I`. Apply `caseB_count`.
-/
theorem largeb_caseIIIa {n Q : ℕ} {x gL gR : ℚ} (h : ∃ y, BadlyOrdered n x y)
    (hQ4 : n ≤ Q ^ 4)
    (hgLF : IsFarey Q gL) (hgRF : IsFarey Q gR)
    (hgLx : gL < x) (hRgR : elemR x < gR)
    (hdet : (gL.den : ℤ) * gR.num - gL.num * (gR.den : ℤ) = 1)
    (hsum : Q < gL.den + gR.den) (hle : gR.den ≤ gL.den) :
    (n : ℝ) / 4 - 2 * ((Kmax n Q : ℝ) * (1 + Real.log (Kmax n Q))) - 1
      ≤ (betweenCount n x (elemR x) : ℝ) := by
  -- Let's obtain the facts from `badly_left_facts` regarding `x`.
  obtain ⟨hx0, hxR, hRz, hb, hle, ha, hab⟩ := badly_left_facts h;
  refine' le_trans _ ( _ : ( betweenCount n x ( elemR x ) : ℝ ) ≥ _ );
  exact ( n : ℝ ) / 4 - errTerm x gR n - errTerm ( elemR x ) gR n - 1;
  · -- Apply the error bounds from `errTerm_le_Kmax`.
    have h_err1 : errTerm x gR n ≤ (Kmax n Q : ℝ) * (1 + Real.log (Kmax n Q)) := by
      apply errTerm_le_Kmax;
      refine' ceil_le_Kmax _ _;
      -- By simplifying, we can see that this inequality holds.
      have h_simplified : (gR.num * x.den - x.num * gR.den : ℝ) ≤ 4 * Q * x.den / Real.sqrt n := by
        have h_det_le : (gR.num * x.den - x.num * gR.den : ℝ) ≤ gR.den * x.den * (1 / (gL.den * gR.den : ℝ)) := by
          have h_det_le : (gR.num * x.den - x.num * gR.den : ℝ) ≤ gR.den * x.den * ((gR : ℝ) - (gL : ℝ)) := by
            rw [ Rat.cast_def, Rat.cast_def ] at *;
            field_simp;
            nlinarith [ show ( gL.num : ℝ ) * x.den < x.num * gL.den from by rw [ ← @Rat.num_div_den gL, ← @Rat.num_div_den x ] at hgLx; rw [ div_lt_div_iff₀ ] at hgLx <;> norm_cast at * <;> linarith [ Rat.pos x, Rat.pos gL ] ];
          have h_det_le : (gR : ℝ) - (gL : ℝ) = 1 / (gL.den * gR.den : ℝ) := by
            rw [ Rat.cast_def, Rat.cast_def ];
            rw [ div_sub_div ] <;> try positivity;
            exact congrArg₂ _ ( by norm_cast; linarith ) ( by ring );
          aesop;
        refine le_trans h_det_le ?_;
        rw [ mul_one_div, div_le_div_iff₀ ] <;> try positivity;
        · -- By simplifying, we can see that this inequality holds because $gL.den \geq Q/2$ and $gR.den \leq Q$.
          have h_simplified : Real.sqrt n ≤ 4 * Q * gL.den := by
            rw [ Real.sqrt_le_left ] <;> norm_cast;
            · exact hQ4.trans ( by nlinarith only [ show Q ^ 2 ≤ 4 * Q * gL.den by nlinarith only [ hsum, ‹gR.den ≤ gL.den›, hgLF.2.2, hgRF.2.2 ] ] );
            · positivity;
          convert! mul_le_mul_of_nonneg_left h_simplified ( show ( 0 : ℝ ) ≤ gR.den * x.den by positivity ) using 1 ; ring;
        · exact Real.sqrt_pos.mpr ( Nat.cast_pos.mpr ( by linarith ) );
      convert! mul_le_mul_of_nonneg_left h_simplified ( show ( 0 : ℝ ) ≤ ( n + 1 ) / x.den by positivity ) using 1 ; ring_nf;
      · push_cast; ring;
      · ring_nf ; norm_num [ ne_of_gt ( Rat.pos _ ) ]
    have h_err2 : errTerm (elemR x) gR n ≤ (Kmax n Q : ℝ) * (1 + Real.log (Kmax n Q)) := by
      apply errTerm_le_Kmax;
      refine' ceil_le_Kmax _ _;
      -- By simplifying, we can see that the inequality holds.
      have h_simplify : (n + 1 : ℝ) * gR.den * ((gR : ℝ) - (elemR x : ℝ)) ≤ 4 * (n + 1) * Q / Real.sqrt n := by
        have h_simplify : (gR : ℝ) - (elemR x : ℝ) ≤ 1 / (gL.den * gR.den : ℝ) := by
          have h_simplify : (gR - gL : ℝ) = 1 / (gL.den * gR.den : ℝ) := by
            rw [ Rat.cast_def, Rat.cast_def ];
            rw [ div_sub_div ] <;> norm_cast <;> norm_num [ Rat.den_nz ];
            rw [ show gR.num * gL.den - gR.den * gL.num = 1 by linarith ] ; norm_num [ Rat.divInt_eq_div ] ; ring;
          linarith [ show ( gL : ℝ ) ≤ x from mod_cast hgLx.le, show ( elemR x : ℝ ) ≥ x from mod_cast hxR.le ];
        refine le_trans ( mul_le_mul_of_nonneg_left h_simplify <| by positivity ) ?_;
        rw [ mul_one_div, div_le_div_iff₀ ] <;> try positivity;
        · -- By simplifying, we can see that the inequality holds because $Q \geq 3$ and $n \leq Q^4$.
          have h_simplify : Real.sqrt n ≤ 4 * Q * gL.den := by
            rw [ Real.sqrt_le_left ] <;> norm_cast <;> try nlinarith only [ hQ4, hsum, ‹gR.den ≤ gL.den› ] ;
            exact hQ4.trans ( by nlinarith only [ show Q ^ 2 ≤ 4 * Q * gL.den by nlinarith only [ hsum, ‹gR.den ≤ gL.den›, hgLF.2.2, hgRF.2.2 ] ] );
          nlinarith [ show 0 ≤ ( n + 1 : ℝ ) * gR.den by positivity ];
        · exact Real.sqrt_pos.mpr ( Nat.cast_pos.mpr ( by linarith ) );
      convert! h_simplify using 1;
      rw [ div_mul_eq_mul_div, div_eq_iff ] <;> norm_cast <;> norm_num [ Rat.cast_def ] ; ring_nf;
      rw [ ← Rat.mul_den_eq_num, ← Rat.mul_den_eq_num ] ; ring;
    linarith;
  · apply caseB_count n x gR hx0.le hxR hRgR hgRF.2.1;
    · norm_cast;
    · convert! elemR_sub_gt hb ha |> le_of_lt using 1;
    · -- By `det_real_eq`, we have `(gR.num * (x.den : ℤ) - x.num * (gR.den : ℤ) : ℝ) = (gR.den : ℝ) * (x.den : ℝ) * ((gR : ℝ) - (x : ℝ))`.
      have h_det_real : (gR.num * (x.den : ℤ) - x.num * (gR.den : ℤ) : ℝ) = (gR.den : ℝ) * (x.den : ℝ) * ((gR : ℝ) - (x : ℝ)) := by
        simp +decide [ mul_sub, Rat.cast_def ];
        simp +decide [ mul_assoc, mul_comm, mul_left_comm, div_eq_mul_inv, ne_of_gt ( Rat.pos _ ) ];
      have h_det_ge_two : (gR.num * (x.den : ℤ) - x.num * (gR.den : ℤ) : ℝ) ≥ 2 := by
        have h_det_ge_two : (gR.num * (x.den : ℤ) - x.num * (gR.den : ℤ) : ℝ) > (gR.den : ℝ) := by
          have h_det_ge_two : (gR : ℝ) - (x : ℝ) > 1 / (x.den : ℝ) := by
            have h_det_ge_two : (elemR x : ℝ) - (x : ℝ) > 1 / (x.den : ℝ) := by
              convert! elemR_sub_gt hb ha using 1;
            exact h_det_ge_two.trans_le ( sub_le_sub_right ( mod_cast hRgR.le ) _ );
          simp_all +decide [ div_eq_mul_inv ];
          rw [ inv_eq_one_div, div_lt_iff₀ ] at h_det_ge_two <;> nlinarith [ show ( x.den : ℝ ) ≥ 4 by norm_cast, show ( gR.den : ℝ ) ≥ 1 by exact_mod_cast gR.pos ];
        norm_cast at *;
        linarith [ show gR.den ≥ 1 from gR.pos ];
      nlinarith [ show ( x.den : ℝ ) ≤ n by norm_cast ]

/-- If `(n+1)·q.den·(q−p)` is below the uniform threshold then
`errTerm p q n ≤ Kmax·(1+log Kmax)`. -/
theorem errTerm_le_Kmax' {n Q : ℕ} (p q : ℚ)
    (hM : ((n : ℝ) + 1) * (q.den : ℝ) * ((q : ℝ) - (p : ℝ))
            ≤ (4 * ((n : ℝ) + 1) * (Q : ℝ)) / Real.sqrt n) :
    errTerm p q n ≤ (Kmax n Q : ℝ) * (1 + Real.log (Kmax n Q)) := by
  apply errTerm_le_Kmax
  apply ceil_le_Kmax
  have hp : (p.den : ℝ) ≠ 0 := by exact_mod_cast p.den_nz
  rw [show ((n : ℝ) + 1) / p.den
        * ((q.num * (p.den : ℤ) - p.num * (q.den : ℤ) : ℤ) : ℝ)
        = ((n : ℝ) + 1) * (q.den : ℝ) * ((q : ℝ) - (p : ℝ)) from by
    rw [det_real_eq p q]; field_simp]
  exact hM

/-
The `h2X` lower bound for the left-reference Case III-b: `2 ≤ (n+1)·gL.den·(elemR x − gL)`.
-/
theorem h2X_left {n : ℕ} {x gL : ℚ} (h : ∃ y, BadlyOrdered n x y) (hgLx : gL < x) :
    (2 : ℝ) ≤ ((n : ℝ) + 1) * (gL.den : ℝ) * ((elemR x : ℝ) - (gL : ℝ)) := by
  -- From badly_left_facts h: 0<x, x<elemR x, elemR x<1, 4≤x.den, x.den≤n, 1≤x.num, x.num+3≤x.den.
  obtain ⟨hx_pos, hx_lt_elemR, h_elemR_lt_one, hx_den_ge_4, hx_den_le_n, hx_num_ge_1, hx_num_plus_3_le_den⟩ := badly_left_facts h;
  -- From STEP 2: (elemR x:ℝ) - (gL:ℝ) = (RW:ℝ)/(((b:ℝ)-1)*(s:ℝ)), and RW ≥ 2.
  have h_RW_ge_2 : (x.num + 1) * (gL.den : ℤ) - gL.num * (x.den - 1) ≥ 2 := by
    have h_RW_ge_2 : (x.num + 1) * (gL.den : ℝ) - gL.num * (x.den - 1) ≥ (gL.den : ℝ) * ((x.num + x.den) / x.den) := by
      have h_RW_ge_2 : (x.num + 1 : ℝ) / (x.den - 1) - gL.num / gL.den ≥ (x.num + x.den : ℝ) / (x.den * (x.den - 1)) := by
        have h_RW_ge_2 : (gL.num : ℝ) / gL.den ≤ x.num / x.den := by
          rw [ div_le_div_iff₀ ] <;> norm_cast;
          · simpa [ Rat.le_iff ] using! hgLx.le;
          · exact gL.pos;
          · grind;
        refine le_trans ?_ ( sub_le_sub_left h_RW_ge_2 _ );
        rw [ div_sub_div, div_le_div_iff₀ ] <;> nlinarith [ show ( x.den : ℝ ) ≥ 4 by norm_cast, show ( x.num : ℝ ) ≥ 1 by norm_cast, show ( x.den : ℝ ) ≥ x.num + 3 by norm_cast ];
      field_simp at h_RW_ge_2;
      rw [ div_le_iff₀ ] at h_RW_ge_2 <;> nlinarith [ show ( x.den : ℝ ) ≥ 4 by norm_cast, mul_div_cancel₀ ( ( x.num + x.den : ℝ ) ) ( show ( x.den : ℝ ) ≠ 0 by positivity ), mul_div_cancel₀ ( ( x.num + 1 : ℝ ) * gL.den ) ( show ( x.den - 1 : ℝ ) ≠ 0 by exact sub_ne_zero_of_ne ( by norm_cast; linarith ) ) ];
    have h_RW_ge_2 : (gL.den : ℝ) * ((x.num + x.den) / x.den) > 1 := by
      field_simp;
      exact_mod_cast ( by nlinarith [ show ( gL.den : ℤ ) ≥ 1 from mod_cast gL.pos ] : ( x.den : ℤ ) < gL.den * ( x.num + x.den ) );
    exact Int.le_of_lt_add_one ( by rw [ ← @Int.cast_lt ℝ ] ; push_cast; linarith )
  -- From STEP 3: ((n:ℝ)+1)*(s:ℝ)*((elemR x:ℝ)-gL) = ((n:ℝ)+1)*(RW:ℝ)/((b:ℝ)-1)
  have h_eq : ((n : ℝ) + 1) * (gL.den : ℝ) * ((elemR x : ℝ) - gL) = ((n : ℝ) + 1) * ((x.num + 1) * (gL.den : ℤ) - gL.num * (x.den - 1) : ℝ) / ((x.den : ℝ) - 1) := by
    unfold elemR; push_cast; rw [ div_sub', mul_div_assoc' ];
    · rw [ Rat.cast_def ] ; ring_nf;
      simpa [ mul_assoc, mul_comm, mul_left_comm, ne_of_gt ( Rat.pos _ ) ] using! by ring;
    · linarith [ show ( x.den : ℝ ) ≥ 4 by norm_cast ];
  rw [ h_eq, le_div_iff₀ ] <;> norm_cast;
  · rw [ Int.subNatNat_eq_coe ] ; push_cast ; nlinarith;
  · rw [ Int.subNatNat_eq_coe ] ; norm_num ; linarith

/-
**Case III-b** (small endpoint on the left). The reference is `gL`. Apply `caseB_count_left`.
-/
theorem largeb_caseIIIb {n Q : ℕ} {x gL gR : ℚ} (h : ∃ y, BadlyOrdered n x y)
    (hQ4 : n ≤ Q ^ 4) (hbig : n ≤ x.den * x.den)
    (hgLF : IsFarey Q gL) (hgRF : IsFarey Q gR)
    (hgLx : gL < x) (hRgR : elemR x < gR)
    (hdet : (gL.den : ℤ) * gR.num - gL.num * (gR.den : ℤ) = 1)
    (hsum : Q < gL.den + gR.den) (hle : gL.den ≤ gR.den) :
    (n : ℝ) / 4 - 2 * ((Kmax n Q : ℝ) * (1 + Real.log (Kmax n Q))) - 1
      ≤ (betweenCount n x (elemR x) : ℝ) := by
  have := @caseB_count_left n x gL;
  specialize this (by
  exact hgLF.1) hgLx (by
  exact ( badly_left_facts h ) |>.2.2.1.le |> le_trans <| by norm_num;) (by
  have := badly_left_facts h; aesop;) (by
  exact_mod_cast h.choose_spec.1.2.2) (by
  have := badly_left_facts h;
  exact elemR_sub_gt this.2.2.2.1 this.2.2.2.2.2.1 |> le_of_lt) (by
  convert! h2X_left h hgLx using 1);
  have h2 : ((n + 1) : ℝ) * (gL.den : ℝ) * ((elemR x : ℝ) - (gL : ℝ)) ≤ 4 * ((n + 1) : ℝ) * (Q : ℝ) / Real.sqrt n := by
    have h2 : ((n + 1) : ℝ) * (gL.den : ℝ) * ((elemR x : ℝ) - (gL : ℝ)) ≤ (n + 1) / (gR.den : ℝ) := by
      have h2 : ((elemR x : ℝ) - (gL : ℝ)) ≤ 1 / ((gL.den : ℝ) * (gR.den : ℝ)) := by
        have h2 : ((gR : ℝ) - (gL : ℝ)) = 1 / (gL.den * gR.den : ℝ) := by
          rw [ eq_div_iff ] <;> norm_cast at * <;> simp_all +decide;
          rw [ Rat.sub_def' ];
          simp +decide [ mul_comm, Rat.mkRat_eq_div ];
          rw [ mul_div_cancel₀ _ ( by norm_cast; aesop ) ] ; norm_cast ; linarith;
        exact h2 ▸ sub_le_sub_right ( mod_cast hRgR.le ) _;
      convert! mul_le_mul_of_nonneg_left h2 ( show ( 0 : ℝ ) ≤ ( n + 1 ) * gL.den by positivity ) using 1 ; ring_nf;
      norm_num [ hgLF.2.2, hgRF.2.2 ];
    have h3 : (n + 1) / (gR.den : ℝ) ≤ 2 * (n + 1) / (Q : ℝ) := by
      rw [ div_le_div_iff₀ ] <;> norm_cast;
      · nlinarith;
      · exact gR.pos;
      · rcases Q with ( _ | _ | Q ) <;> norm_num at *;
        cases hgLF ; cases hgRF ; aesop;
    refine le_trans h2 <| h3.trans ?_;
    rcases n with ( _ | _ | n ) <;> norm_num at *;
    · obtain ⟨ y, hy ⟩ := h;
      have := hy.1.2.2; aesop;
    · rcases Q with ( _ | _ | Q ) <;> norm_num at *;
      rw [ div_le_iff₀ ] <;> nlinarith only [ sq ( Q : ℝ ) ];
    · rw [ div_le_div_iff₀ ] <;> try positivity;
      · have h4 : (Q : ℝ) ^ 2 ≥ Real.sqrt (n + 1 + 1) := by
          exact Real.sqrt_le_iff.mpr ⟨ by positivity, by norm_cast; nlinarith ⟩;
        nlinarith only [ h4, Real.sqrt_nonneg ( n + 1 + 1 : ℝ ), Real.mul_self_sqrt ( show ( n : ℝ ) + 1 + 1 ≥ 0 by positivity ) ];
      · exact Nat.cast_pos.mpr ( Nat.pos_of_ne_zero ( by rintro rfl; norm_num at hQ4 ) );
  have h3 : ((n + 1) : ℝ) * (gL.den : ℝ) * ((x : ℝ) - (gL : ℝ)) ≤ 4 * ((n + 1) : ℝ) * (Q : ℝ) / Real.sqrt n := by
    refine le_trans ?_ h2;
    gcongr;
    exact le_of_lt ( badly_left_facts h |>.2.1 );
  have h4 : errTerm (1 - elemR x) (1 - gL) n ≤ (Kmax n Q : ℝ) * (1 + Real.log (Kmax n Q)) := by
    apply errTerm_le_Kmax';
    convert! h2 using 1;
    rw [ one_sub_den ] ; ring_nf;
    norm_num ; ring
  have h5 : errTerm (1 - x) (1 - gL) n ≤ (Kmax n Q : ℝ) * (1 + Real.log (Kmax n Q)) := by
    apply errTerm_le_Kmax';
    convert! h3 using 1 ; norm_num [ one_sub_den ]
  linarith [h4, h5]

/-- **Large-`b`, Case III.** No order-`Q` Farey fraction lies inside `I` and `(elemR x).den > Q`.
The interval lies in a single gap `gL < gR` of `F_Q`; use `caseB_count` / `caseB_count_left`
with the smaller-denominator endpoint. -/
theorem largeb_caseIII {n Q : ℕ} {x : ℚ} (h : ∃ y, BadlyOrdered n x y)
    (hQ : 3 ≤ Q) (hQ4 : n ≤ Q ^ 4)
    (hQb : Q < x.den) (hbig : n ≤ x.den * x.den)
    (hsw : Q < (elemR x).den)
    (hno : ∀ f : ℚ, IsFarey Q f → x < f → f < elemR x → False) :
    (n : ℝ) / 4 - 2 * ((Kmax n Q : ℝ) * (1 + Real.log (Kmax n Q))) - 1
      ≤ (betweenCount n x (elemR x) : ℝ) := by
  obtain ⟨hx0', hxw, hw1', hb, hbn, ha, hab⟩ := badly_left_facts h
  obtain ⟨gL, gR, hgLF, hgRF, hgLx0, hRgR0, hgLR, hgap⟩ :=
    farey_gap_between Q (by omega) x (elemR x) (le_of_lt hx0') (le_of_lt hw1') hxw hno
  have hdet := farey_neighbor_det hgLF hgRF hgLR hgap
  have hsum := farey_neighbor_den_sum hgLF hgRF hgLR hgap
  have hgLx : gL < x := by
    rcases lt_or_eq_of_le hgLx0 with hlt | heq
    · exact hlt
    · exfalso; have : gL.den ≤ Q := hgLF.2.2; rw [heq] at this; omega
  have hRgR : elemR x < gR := by
    rcases lt_or_eq_of_le hRgR0 with hlt | heq
    · exact hlt
    · exfalso; have : gR.den ≤ Q := hgRF.2.2; rw [← heq] at this; omega
  by_cases hcase : gR.den ≤ gL.den
  · exact largeb_caseIIIa h hQ4 hgLF hgRF hgLx hRgR hdet hsum hcase
  · push_neg at hcase
    exact largeb_caseIIIb h hQ4 hbig hgLF hgRF hgLx hRgR hdet hsum (le_of_lt hcase)

/-- **Large-`b` core.** With `Q^3 ≤ n ≤ Q^4`, `Q < b`, and `n ≤ b*b`, the elementary-interval
count is at least `n/4` minus twice the uniform error `Kmax n Q · (1 + log (Kmax n Q))`. -/
theorem largeb_core {n Q : ℕ} {x : ℚ} (h : ∃ y, BadlyOrdered n x y)
    (hQ : 3 ≤ Q) (hQ3 : Q ^ 3 ≤ n) (hQ4 : n ≤ Q ^ 4)
    (hQb : Q < x.den) (hbig : n ≤ x.den * x.den) :
    (n : ℝ) / 4 - 2 * ((Kmax n Q : ℝ) * (1 + Real.log (Kmax n Q))) - 1
      ≤ (betweenCount n x (elemR x) : ℝ) := by
  by_cases hsw : (elemR x).den ≤ Q
  · exact largeb_caseI h hbig hsw
  · push_neg at hsw
    by_cases hex : ∃ z : ℚ, IsFarey Q z ∧ x < z ∧ z < elemR x
    · obtain ⟨z, hzF, hxz, hzR⟩ := hex
      exact largeb_caseII h hQ hQ3 hbig z hzF hxz hzR
    · exact largeb_caseIII h hQ hQ4 hQb hbig hsw
        (fun f hf h1 h2 => hex ⟨f, hf, h1, h2⟩)

/-
`Kmax n Q ≤ Kbar n` whenever `Q^3 ≤ n`.
-/
theorem Kmax_le_Kbar {n Q : ℕ} (hn : 1 ≤ n) (hQ3 : Q ^ 3 ≤ n) : Kmax n Q ≤ Kbar n := by
  -- It suffices to show that $Q \leq n^{1/3}$.
  have hQ_le_n13 : (Q : ℝ) ≤ (n : ℝ) ^ (1 / 3 : ℝ) := by
    exact le_trans ( by rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( Nat.cast_nonneg Q ) ] ; norm_num ) ( Real.rpow_le_rpow ( by positivity ) ( show ( Q : ℝ ) ^ 3 ≤ n by exact_mod_cast hQ3 ) ( by positivity ) );
  refine' Nat.add_le_add_right ( Nat.ceil_mono _ ) 2;
  gcongr

/-
Small-`b` eventual estimate.
-/
theorem smallb_eventually {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      (1 / 4 - ε) * (n : ℝ) ≤ ((n : ℝ) + 1) * Real.sqrt n / 4 - (n : ℝ) * (1 + Real.log n) := by
  -- We'll use that $Real.log n$ grows slower than any linear function to find such an $N$.
  have h_log_growth : Filter.Tendsto (fun n : ℕ => (Real.log n : ℝ) / Real.sqrt n) Filter.atTop (nhds 0) := by
    -- Let $y = \sqrt{n}$, so we can rewrite the limit as $\lim_{y \to \infty} \frac{\log(y^2)}{y}$.
    suffices h_log_sqrt_y : Filter.Tendsto (fun y : ℝ => Real.log (y^2) / y) Filter.atTop (nhds 0) by
      have := h_log_sqrt_y.comp ( show Filter.Tendsto ( fun n : ℕ => Real.sqrt n ) Filter.atTop ( Filter.atTop ) by simpa only [ Real.sqrt_eq_rpow ] using! tendsto_rpow_atTop ( by norm_num ) |> Filter.Tendsto.comp <| tendsto_natCast_atTop_atTop );
      exact this.congr fun n => by rw [ Function.comp_apply, Real.sq_sqrt ( Nat.cast_nonneg _ ) ] ;
    -- Let $z = \frac{1}{y}$, so we can rewrite the limit as $\lim_{z \to 0^+} 2z \log(1/z)$.
    suffices h_log_recip : Filter.Tendsto (fun z : ℝ => 2 * z * Real.log (1 / z)) (Filter.map (fun y => 1 / y) Filter.atTop) (nhds 0) by
      exact h_log_recip.congr ( by simp +contextual [ div_eq_mul_inv, mul_assoc, mul_comm ] );
    norm_num;
    exact tendsto_nhdsWithin_of_tendsto_nhds ( by have := Real.continuous_mul_log.tendsto 0; simpa [ mul_assoc ] using! this.neg.const_mul 2 );
  have := h_log_growth.eventually ( gt_mem_nhds <| show 0 < 1 / 16 by norm_num );
  filter_upwards [ this, Filter.eventually_gt_atTop 0, Filter.eventually_gt_atTop ⌈ ( 16 * ( 1 + ε ) ) ^ 2⌉₊ ] with n hn hn' hn'' ; rw [ div_lt_iff₀ ( by positivity ) ] at hn ; nlinarith [ Nat.le_ceil ( ( 16 * ( 1 + ε ) ) ^ 2 ), show ( n : ℝ ) ≥ ⌈ ( 16 * ( 1 + ε ) ) ^ 2⌉₊ + 1 by exact_mod_cast hn'', Real.sqrt_nonneg n, Real.sq_sqrt <| Nat.cast_nonneg n, mul_self_nonneg <| Real.sqrt n - ( 16 * ( 1 + ε ) ) ] ;

/-
Large-`b` eventual estimate: the uniform error is eventually `≤ ε n`.
-/
theorem largeb_eventually {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      2 * ((Kbar n : ℝ) * (1 + Real.log (Kbar n))) + 1 ≤ ε * (n : ℝ) := by
  -- To prove the limit is 0, we can use the fact that $n^{-1/6} \cdot \log n \to 0$ as $n \to \infty$.
  have h_log_div_n : Filter.Tendsto (fun n : ℕ => (1 + Real.log (4 * (n : ℝ) + 7)) / (n : ℝ) ^ (1 / 6 : ℝ)) Filter.atTop (nhds 0) := by
    -- We can use the fact that $\frac{\log(n)}{n^{1/6}}$ tends to $0$ as $n$ tends to infinity.
    have h_log_div_n : Filter.Tendsto (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ) ^ (1 / 6 : ℝ)) Filter.atTop (nhds 0) := by
      -- Let $y = \frac{1}{n^{1/6}}$, so we can rewrite the limit as $\lim_{y \to 0^+} y \log(1/y^6)$.
      suffices h_log_recip : Filter.Tendsto (fun y : ℝ => y * Real.log (1 / y^6)) (Filter.map (fun n => 1 / (n : ℝ) ^ (1 / 6 : ℝ)) Filter.atTop) (nhds 0) by
        rw [ Filter.tendsto_map'_iff ] at h_log_recip;
        refine h_log_recip.comp tendsto_natCast_atTop_atTop |> Filter.Tendsto.congr' ?_ ; filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn ; norm_num [ Real.rpow_neg, hn.ne' ] ; ring_nf;
        rw [ Real.log_rpow ( by positivity ) ] ; ring;
      norm_num;
      refine' Filter.Tendsto.comp _ ( tendsto_inv_atTop_zero.comp ( tendsto_rpow_atTop ( by norm_num ) ) );
      have := Real.continuous_mul_log.tendsto 0 ; convert! this.neg.const_mul 6 using 2 <;> ring;
    -- We can use the fact that $\frac{\log(4n+7)}{n^{1/6}}$ tends to $0$ as $n$ tends to infinity.
    have h_log_div_n : Filter.Tendsto (fun n : ℕ => Real.log (4 * (n : ℝ) + 7) / (n : ℝ) ^ (1 / 6 : ℝ)) Filter.atTop (nhds 0) := by
      have h_log_div_n : Filter.Tendsto (fun n : ℕ => (Real.log (n : ℝ) + Real.log (4 + 7 / (n : ℝ))) / (n : ℝ) ^ (1 / 6 : ℝ)) Filter.atTop (nhds 0) := by
        simpa [ add_div ] using! h_log_div_n.add ( Filter.Tendsto.div_atTop ( Filter.Tendsto.log ( tendsto_const_nhds.add ( tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop ) ) ( by norm_num ) ) ( tendsto_rpow_atTop ( by norm_num ) |> Filter.Tendsto.comp <| tendsto_natCast_atTop_atTop ) );
      refine h_log_div_n.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn using by rw [ ← Real.log_mul ( by positivity ) ( by positivity ), mul_add, mul_div_cancel₀ _ ( by positivity ) ] ; ring_nf );
    simpa [ add_div ] using! Filter.Tendsto.add ( tendsto_inv_atTop_zero.comp ( tendsto_rpow_atTop ( by norm_num ) |> Filter.Tendsto.comp <| tendsto_natCast_atTop_atTop ) ) h_log_div_n;
  -- Using the bound on $K(n)$, we can show that the expression tends to 0.
  have h_bound : Filter.Tendsto (fun n : ℕ => (2 * ((4 * ((n : ℝ) + 1) * (n : ℝ) ^ (1 / 3 : ℝ) / Real.sqrt n + 3) * (1 + Real.log (4 * (n : ℝ) + 7)) + 1) : ℝ) / (n : ℝ)) Filter.atTop (nhds 0) := by
    -- Simplify the expression inside the limit.
    suffices h_simplify : Filter.Tendsto (fun n : ℕ => (8 * (1 + 1 / (n : ℝ)) * (1 + Real.log (4 * (n : ℝ) + 7)) / (n : ℝ) ^ (1 / 6 : ℝ) + 6 * (1 + Real.log (4 * (n : ℝ) + 7)) / (n : ℝ) + 2 / (n : ℝ))) Filter.atTop (nhds 0) by
      refine h_simplify.congr' ?_;
      filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn ; norm_num [ Real.sqrt_eq_rpow, Real.rpow_neg, hn.ne', le_of_lt hn ] ; ring_nf;
      norm_num [ ← Real.rpow_neg ( Nat.cast_nonneg _ ), ← Real.rpow_add ( Nat.cast_pos.mpr hn ), hn.ne' ] ; ring_nf;
      norm_num [ mul_assoc, ← Real.rpow_add ( Nat.cast_pos.mpr hn ) ];
    -- We'll use the fact that $n^{-1/6} \cdot \log n \to 0$ as $n \to \infty$.
    have h_log_div_n : Filter.Tendsto (fun n : ℕ => (1 + Real.log (4 * (n : ℝ) + 7)) / (n : ℝ)) Filter.atTop (nhds 0) := by
      refine' squeeze_zero_norm' _ h_log_div_n;
      filter_upwards [ Filter.eventually_gt_atTop 1 ] with n hn using by rw [ Real.norm_of_nonneg ( by exact div_nonneg ( add_nonneg zero_le_one ( Real.log_nonneg ( by linarith ) ) ) ( Nat.cast_nonneg _ ) ) ] ; exact div_le_div_of_nonneg_left ( by exact add_nonneg zero_le_one ( Real.log_nonneg ( by linarith ) ) ) ( by positivity ) ( by exact le_trans ( Real.rpow_le_rpow_of_exponent_le ( by norm_cast; linarith ) ( show ( 1 : ℝ ) / 6 ≤ 1 by norm_num ) ) ( by norm_num ) ) ;
    simpa [ mul_div_assoc ] using! Filter.Tendsto.add ( Filter.Tendsto.add ( Filter.Tendsto.mul ( tendsto_const_nhds.mul ( tendsto_const_nhds.add ( tendsto_one_div_atTop_nhds_zero_nat ) ) ) ‹Tendsto ( fun n : ℕ => ( 1 + Real.log ( 4 * ↑n + 7 ) ) / ↑n ^ ( 1 / 6 : ℝ ) ) atTop ( 𝓝 0 ) › ) ( Filter.Tendsto.const_mul 6 h_log_div_n ) ) ( tendsto_const_nhds.mul tendsto_inv_atTop_nhds_zero_nat );
  have h_bound : ∀ᶠ n in Filter.atTop, (2 * (Kbar n * (1 + Real.log (Kbar n)) + 1) : ℝ) / (n : ℝ) ≤ (2 * ((4 * ((n : ℝ) + 1) * (n : ℝ) ^ (1 / 3 : ℝ) / Real.sqrt n + 3) * (1 + Real.log (4 * (n : ℝ) + 7)) + 1) : ℝ) / (n : ℝ) := by
    have h_bound : ∀ᶠ n in Filter.atTop, Kbar n ≤ 4 * ((n : ℝ) + 1) * (n : ℝ) ^ (1 / 3 : ℝ) / Real.sqrt n + 3 := by
      refine' Filter.eventually_atTop.mpr ⟨ 1, fun n hn => _ ⟩ ; norm_num [ Kbar ];
      linarith [ Nat.ceil_lt_add_one ( show 0 ≤ 4 * ( n + 1 : ℝ ) * n ^ ( 1 / 3 : ℝ ) / Real.sqrt n by positivity ) ];
    filter_upwards [ h_bound, Filter.eventually_gt_atTop 0 ] with n hn hn' ; gcongr;
    · exact Nat.cast_pos.mpr ( Nat.succ_pos _ );
    · refine le_trans hn ?_;
      rw [ div_add', div_le_iff₀ ] <;> try positivity;
      nlinarith only [ show ( n : ℝ ) ≥ 1 by exact_mod_cast hn', show ( n : ℝ ) ^ ( 1 / 3 : ℝ ) ≤ Real.sqrt n by rw [ Real.sqrt_eq_rpow ] ; exact Real.rpow_le_rpow_of_exponent_le ( by norm_cast ) ( by norm_num ), Real.sqrt_nonneg n, Real.sq_sqrt ( Nat.cast_nonneg n ) ];
  filter_upwards [ h_bound, ‹Filter.Tendsto ( fun n : ℕ => 2 * ( ( 4 * ( n + 1 ) * n ^ ( 1 / 3 : ℝ ) / Real.sqrt n + 3 ) * ( 1 + Real.log ( 4 * n + 7 ) ) + 1 ) / n ) atTop ( nhds 0 ) ›.eventually ( gt_mem_nhds hε ), Filter.eventually_gt_atTop 0 ] with n hn hn' hn'' using by rw [ div_le_iff₀ ( by positivity ) ] at hn; nlinarith [ show ( n : ℝ ) ≥ 1 by exact_mod_cast hn'' ] ;

/-
Monotonicity of `t ↦ t·(1 + log t)` on `[1, ∞)`.
-/
theorem mul_one_add_log_mono {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    a * (1 + Real.log a) ≤ b * (1 + Real.log b) := by
  nlinarith [ Real.log_nonneg ha, Real.log_le_log ( by linarith ) hab ]

/-- For every `ε > 0`, eventually every badly-ordered left endpoint has at least
  `(1/4 - ε) n` order-`n` Farey fractions in its elementary interval. -/
theorem elem_interval_count_lower_final :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ x : ℚ,
      (∃ y, BadlyOrdered n x y) → (1 / 4 - ε) * (n : ℝ) ≤ (betweenCount n x (elemR x) : ℝ) := by
  intro ε hε
  have hlog : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ Real.log n :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  filter_upwards [smallb_eventually hε, largeb_eventually hε,
    eventually_ge_atTop 81] with n hsmallE hlargeE hn81
  intro x hx
  by_cases hcase : x.den * x.den < n
  · -- small b
    have := smallb_bound hx hcase
    linarith
  · -- large b: n ≤ b*b
    have hbig : n ≤ x.den * x.den := by omega
    obtain ⟨Q, hQ, hQ3, hQ4⟩ := largeb_Q_exists n hn81
    obtain ⟨-, -, -, hb4, -, -, -⟩ := badly_left_facts hx
    -- Q < b : since Q^3 ≤ n ≤ b*b and b ≥ 4 we get Q < b
    have hQb : Q < x.den := by
      by_contra hle
      push_neg at hle
      have h1 : x.den ^ 3 ≤ Q ^ 3 := Nat.pow_le_pow_left hle 3
      have h2 : x.den ^ 3 ≤ x.den * x.den := le_trans (le_trans h1 hQ3) hbig
      nlinarith [hb4]
    have hcore := largeb_core hx hQ hQ3 hQ4 hQb hbig
    have hKle : Kmax n Q ≤ Kbar n := Kmax_le_Kbar (by omega) hQ3
    -- monotonicity of t*(1+log t) to pass from Kmax to Kbar
    have hKmax1 : (1 : ℝ) ≤ (Kmax n Q : ℝ) := by
      have : 2 ≤ Kmax n Q := by unfold Kmax; omega
      exact_mod_cast le_trans (by norm_num) this
    have hmono : (Kmax n Q : ℝ) * (1 + Real.log (Kmax n Q))
        ≤ (Kbar n : ℝ) * (1 + Real.log (Kbar n)) :=
      mul_one_add_log_mono hKmax1 (by exact_mod_cast hKle)
    linarith [hcore, hlargeE, hmono]

/-- For every `ε > 0`, eventually `f(n) ≥ (1/4 - ε) n`. -/
theorem fVal_lower_bound :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, (1 / 4 - ε) * (n : ℝ) ≤ (fVal n : ℝ) := by
  intro ε hε
  have hbig : ∀ᶠ n : ℕ in atTop, 4 ≤ n := eventually_atTop.2 ⟨4, fun n hn => hn⟩
  filter_upwards [elem_interval_count_lower_final ε hε, hbig] with n hcore hn4
  set m := n / 4 with hmdef
  have hm1 : 1 ≤ m := by omega
  have hmle : 4 * m ≤ n := by omega
  have hbad := badlyOrdered_construction n m hm1 hmle
  set S := {k | ∃ x y, BadlyOrdered n x y ∧ betweenCount n x y = k} with hS
  have hSne : S.Nonempty := ⟨betweenCount n (Lf m) (Rf m), Lf m, Rf m, hbad, rfl⟩
  have hmem : fVal n ∈ S := Nat.sInf_mem hSne
  obtain ⟨x, y, hxy, hcount⟩ := hmem
  have h1 : betweenCount n x (elemR x) ≤ betweenCount n x y := betweenCount_ge_elementary hxy
  have h2 : (1 / 4 - ε) * (n : ℝ) ≤ (betweenCount n x (elemR x) : ℝ) := hcore x ⟨y, hxy⟩
  have h3 : (betweenCount n x (elemR x) : ℝ) ≤ (betweenCount n x y : ℝ) := by exact_mod_cast h1
  have h4 : (betweenCount n x y : ℝ) = (fVal n : ℝ) := by exact_mod_cast hcount
  linarith [h2, h3, h4.ge, h4.le]

/-- With `f(n)` the minimum number of Farey fractions strictly between two badly
  ordered Farey fractions of order `n`, we have `f(n) = (1/4 + o(1)) n`. -/
theorem source_limit :
    Tendsto (fun n : ℕ => (fVal n : ℝ) / n) atTop (nhds (1 / 4)) :=
  erdos_1005_of_bounds fVal_upper_bound fVal_lower_bound

#print axioms source_limit

end Erdos1005
