/- leanprover/lean4:v4.32.0  mathlib v4.32.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 204.
https://www.erdosproblems.com/forum/thread/204

Informal authors:
- Sarosh Adenwalla

Formal authors:
- Aristotle
- Wouter van Doorn

URLs:
- https://www.erdosproblems.com/forum/thread/204#post-4790
- https://github.com/Woett/Lean-files/blob/main/ErdosProblem204.lean
- https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/204.lean
-/
/-
We say that a positive integer $n$ is CD covering if for every divisor $d > 1$ of
$n$ there exists an integer $a_d$ such that the set of congruences
$\{a_d \pmod{d} \}$ is a covering system with the property that if $x$ is such
that $x \equiv a_d \pmod{d}$ and $x \equiv a_{d'} \pmod{d'}$, then
$\gcd(d, d') = 1$.

Sarosh Adenwalla solved Erdős Problem #204 (https://www.erdosproblems.com/204) by showing that no such $n$ exists.

S. Adenwalla, A Question of Erdős and Graham on Covering Systems. arXiv:2501.15170 (2025).

Below you can find a Lean formalization of the proof, which was obtained by Aristotle
from Harmonic (aristotle-harmonic@harmonic.fun).

At the very end of the file you can find the statement of Erdős Problem #204 taken
from the Formal Conjectures project by Google DeepMind, which we also prove.

https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/204.lean
-/

import Mathlib

namespace Erdos204

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.flexible false
set_option linter.unusedVariables false

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

attribute [local instance] Classical.propDecidable

noncomputable section

/-
We say a set of congruences (or a congruence set), $\{a_1\mod d_1,\ldots,a_t\mod d_t\}$, is \textit{coprime disjoint} (CD) if whenever two congruences in the set $a_i\mod d_i$ and $a_j\mod d_j$ overlap for $i\neq j$, we have $\gcd(d_i,d_j)=1$.
An integer, $x$, is \textit{covered} by $A$ if there exists $1\leq i\leq t$ such that $x\equiv a_i\mod d_i$.
Clearly $\delta(A)=1$ if and only if $A$ is a covering set.
-/
structure Congruence where
  a : ℤ
  d : ℕ
  d_pos : 0 < d

def Congruence.overlaps (c1 c2 : Congruence) : Prop :=
  ∃ x : ℤ, x ≡ c1.a [ZMOD c1.d] ∧ x ≡ c2.a [ZMOD c2.d]

def IsCD (S : Finset Congruence) : Prop :=
  ∀ c1 ∈ S, ∀ c2 ∈ S, c1 ≠ c2 → c1.overlaps c2 → c1.d.Coprime c2.d

def IsCovering (S : Finset Congruence) : Prop :=
  ∀ x : ℤ, ∃ c ∈ S, x ≡ c.a [ZMOD c.d]

/-
We define the set of congruences for a given $n$ and sequence $a_d$. We filter the divisors of $n$ to include only those greater than 1, and for each such divisor $d$, we create a congruence $a_d \pmod d$.
-/
instance : DecidableEq Congruence := fun c1 c2 =>
  match c1, c2 with
  | ⟨a1, d1, _⟩, ⟨a2, d2, _⟩ =>
    if h : a1 = a2 ∧ d1 = d2 then
      isTrue (by cases c1; cases c2; simp_all)
    else
      isFalse (by intro h_eq; cases c1; cases c2; simp_all)

def congruences (n : ℕ) (a : ℕ → ℤ) : Finset Congruence :=
  let divs := (Nat.divisors n).filter (fun d => 1 < d)
  let divs_list := divs.toList
  let cong_list := divs_list.attach.map (fun ⟨d, hd⟩ =>
    { a := a d,
      d := d,
      d_pos := by
        have : d ∈ divs := Finset.mem_toList.mp hd
        rw [Finset.mem_filter] at this
        exact lt_trans Nat.zero_lt_one this.2
    })
  cong_list.toFinset

/-
We say that $n$ is \textit{non-intersecting} if there exist integers $\{a_d \,:\, d|n,d>1\}$ such that $\{a_d\mod d\,:\, d|n, d>1\}$ is a CD congruence set.
-/
def IsNonIntersecting (n : ℕ) : Prop :=
  ∃ a : ℕ → ℤ, IsCD (congruences n a)

/-
We say $n$ is \textit{CD covering} if there exist integers $\{a_d \,:\, d|n,d>1\}$ such that $\{a_d\mod d\,:\, d|n, d>1\}$ is a CD distinct covering system.
-/
def IsCDCovering (n : ℕ) : Prop :=
  ∃ a : ℕ → ℤ, IsCD (congruences n a) ∧ IsCovering (congruences n a)

/-
Lemma P1: For any covering set, $A=\{a_1\mod d_1,\ldots,a_t\mod d_t\}$, we have $\sum_{i=1}^t \frac{1}{d_i}\geq 1$.
-/
noncomputable def sum_reciprocals (S : Finset Congruence) : ℚ :=
  S.sum (fun c => 1 / c.d)

theorem sum_reciprocals_ge_one (S : Finset Congruence) (h : IsCovering S) : sum_reciprocals S ≥ 1 := by
  unfold sum_reciprocals;
  -- Let $N$ be a large integer, then the number of integers in $[0, N)$ covered by $S$ is at least $N$.
  have h_covered : ∀ N : ℕ, N > 0 → ∑ c ∈ S, (N / (c.d : ℕ) + 1) ≥ N := by
    intro N hN_pos
    have h_covered_count : (∑ c ∈ S, (Finset.filter (fun x => x ≡ c.a [ZMOD c.d]) (Finset.Ico 0 N)).card) ≥ N := by
      have h_covered_count : (Finset.filter (fun x => ∃ c ∈ S, x ≡ c.a [ZMOD c.d]) (Finset.Ico 0 (N : ℤ))).card ≥ N := by
        rw [ Finset.filter_true_of_mem ] <;> aesop;
      refine le_trans h_covered_count ?_;
      exact le_trans ( Finset.card_le_card fun x hx => by aesop ) ( Finset.card_biUnion_le );
    refine le_trans h_covered_count <| Finset.sum_le_sum fun c hc => ?_;
    -- The number of integers in the interval $[0, N)$ that are congruent to $c.a$ modulo $c.d$ is at most $\frac{N}{c.d} + 1$.
    have h_card : Finset.card (Finset.filter (fun x => x ≡ c.a [ZMOD c.d]) (Finset.Ico 0 N)) ≤ Finset.card (Finset.image (fun x => x * c.d + (c.a % c.d)) (Finset.Ico 0 (N / c.d + 1))) := by
      refine Finset.card_mono ?_;
      intro x hx; simp_all +decide [ Int.ModEq ];
      exact ⟨ x / c.d,
        ⟨ Int.ediv_nonneg hx.1.1 ( Nat.cast_nonneg _ ),
          Int.ediv_le_ediv ( Nat.cast_pos.mpr c.d_pos ) hx.1.2.le ⟩,
        by
          linarith [ Int.emod_add_mul_ediv x c.d,
            Int.emod_nonneg x ( Nat.cast_ne_zero.mpr c.d_pos.ne' ) ] ⟩;
    exact h_card.trans ( Finset.card_image_le.trans ( by norm_num ) );
  -- Dividing both sides of the inequality by $N$, we get $\sum_{c \in S} \frac{1}{c.d} + \frac{|S|}{N} \geq 1$.
  have h_divided : ∀ N : ℕ, N > 0 → (∑ c ∈ S, (1 / (c.d : ℚ))) + (∑ c ∈ S, (1 : ℚ)) / N ≥ 1 := by
    intro N hN_pos
    have h_divided_step : (∑ c ∈ S, (N / (c.d : ℕ) + 1) : ℚ) ≥ N := by
      refine le_trans ?_ ( Finset.sum_le_sum fun x hx => add_le_add ( Nat.cast_div_le .. ) le_rfl ) ; norm_cast ; aesop;
    simp_all +decide [Finset.sum_add_distrib, div_eq_mul_inv];
    rw [ ← Finset.mul_sum _ _ _ ] at * ; nlinarith [ ( by norm_cast : ( 1 : ℚ ) ≤ N ), mul_inv_cancel₀ ( by positivity : ( N : ℚ ) ≠ 0 ) ];
  -- Taking the limit as $N$ approaches infinity, we get $\sum_{c \in S} \frac{1}{c.d} \geq 1$.
  have h_limit : Filter.Tendsto (fun N : ℕ => (∑ c ∈ S, (1 / (c.d : ℚ))) + (∑ c ∈ S, (1 : ℚ)) / (N : ℚ)) Filter.atTop (nhds ((∑ c ∈ S, (1 / (c.d : ℚ))) + 0)) := by
    exact le_trans ( tendsto_const_nhds.add <| tendsto_const_nhds.div_atTop <| tendsto_natCast_atTop_atTop ) <| by norm_num;
  simpa using le_of_tendsto_of_tendsto tendsto_const_nhds h_limit ( Filter.eventually_atTop.mpr ⟨ 1, fun N hN => h_divided N hN ⟩ )

/-
Proposition: $\sum_{d|n}\frac{1}{d}=\prod_{i=1}^s\sum_{j=0}^{\alpha_i}\frac{1}{p_i^j}$.
-/
noncomputable def sum_divisors_reciprocal (n : ℕ) : ℚ :=
  (Nat.divisors n).sum (fun d => 1 / (d : ℚ))

theorem sum_divisors_reciprocal_eq_prod_sum_prime_powers (n : ℕ) (hn : n ≠ 0) :
    sum_divisors_reciprocal n = ∏ p ∈ n.primeFactors, (∑ k ∈ Finset.range (n.factorization p + 1), 1 / ((p : ℚ) ^ k)) := by
      -- By definition of prime factorization, we can write n as a product of its prime factors.
      have h_factorization : n = ∏ p ∈ Nat.primeFactors n, p ^ (Nat.factorization n p) := by
        exact Eq.symm ( Nat.prod_factorization_pow_eq_self hn );
      unfold sum_divisors_reciprocal;
      -- Applying the multiplicativity of the sum of reciprocals of divisors function.
      have h_mul : ∀ m1 m2 : ℕ, Nat.gcd m1 m2 = 1 → (∑ d ∈ Nat.divisors (m1 * m2), (1 / (d : ℚ))) = (∑ d ∈ Nat.divisors m1, (1 / (d : ℚ))) * (∑ d ∈ Nat.divisors m2, (1 / (d : ℚ))) := by
        intros m1 m2 h_coprime
        have h_divisors : Nat.divisors (m1 * m2) = Finset.image (fun (d : ℕ × ℕ) => d.1 * d.2) (Nat.divisors m1 ×ˢ Nat.divisors m2) := by
          exact Nat.divisors_mul _ _;
        rw [ h_divisors, Finset.sum_image, Finset.sum_product ];
        · simp +decide [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul, mul_comm ];
        · intros x hx y hy; simp +contextual at hx hy ⊢;
          intro hxy
          have hx1 : x.1 = y.1 := by
            exact Nat.dvd_antisymm ( by exact ( Nat.Coprime.dvd_of_dvd_mul_right ( show Nat.Coprime ( x.1 ) ( y.2 ) from Nat.Coprime.coprime_dvd_left ( by tauto ) <| Nat.Coprime.coprime_dvd_right ( by tauto ) h_coprime ) ) <| hxy.symm ▸ dvd_mul_right _ _ ) ( by exact ( Nat.Coprime.dvd_of_dvd_mul_right ( show Nat.Coprime ( y.1 ) ( x.2 ) from Nat.Coprime.coprime_dvd_left ( by tauto ) <| Nat.Coprime.coprime_dvd_right ( by tauto ) h_coprime ) ) <| hxy.symm ▸ dvd_mul_right _ _ )
          have hx2 : x.2 = y.2 := by
            nlinarith [ Nat.pos_of_dvd_of_pos hx.1.1 ( Nat.pos_of_ne_zero hx.1.2 ), Nat.pos_of_dvd_of_pos hy.1.1 ( Nat.pos_of_ne_zero hy.1.2 ) ]
          exact Prod.ext hx1 hx2;
      -- Applying the multiplicativity of the sum of reciprocals of divisors function to rewrite the sum.
      have h_sum_mul : ∀ {S : Finset ℕ}, (∀ p ∈ S, Nat.Prime p) → (∑ d ∈ Nat.divisors (∏ p ∈ S, p ^ (Nat.factorization n p)), (1 / (d : ℚ))) = (∏ p ∈ S, (∑ k ∈ Finset.range (Nat.factorization n p + 1), (1 / (p ^ k : ℚ)))) := by
        intro S hS; induction S using Finset.induction <;> norm_num at *;
        rw [ Finset.prod_insert ‹_›, h_mul ];
        · rw [ Finset.prod_insert ‹_›, Nat.divisors_prime_pow hS.1 ] ; norm_num [ ‹ ( ∀ p ∈ _, Nat.Prime p ) → _› hS.2 ];
        · exact Nat.Coprime.prod_right fun p hp => Nat.coprime_pow_primes _ _ hS.1 ( hS.2 p hp ) <| by rintro rfl; exact ‹¬_› hp;
      rw [ ← h_sum_mul fun p hp => Nat.prime_of_mem_primeFactors hp, ← h_factorization ]

/-
Two congruences $x \equiv a \pmod m$ and $x \equiv b \pmod n$ overlap if and only if $a \equiv b \pmod{\gcd(m, n)}$.
-/
theorem overlaps_iff_modeq_gcd (a b : ℤ) (m n : ℕ) (_hm : m > 0) (_hn : n > 0) :
    (∃ x : ℤ, x ≡ a [ZMOD m] ∧ x ≡ b [ZMOD n]) ↔ a ≡ b [ZMOD (Nat.gcd m n)] := by
      constructor <;> intro h;
      · exact h.choose_spec.1.symm.of_dvd ( Int.natCast_dvd_natCast.mpr ( Nat.gcd_dvd_left _ _ ) ) |> Int.ModEq.trans <| h.choose_spec.2.of_dvd ( Int.natCast_dvd_natCast.mpr ( Nat.gcd_dvd_right _ _ ) );
      · -- By definition of congruence modulo gcd, there exists an integer k such that a ≡ b + k * gcd(m, n) (mod gcd(m, n)).
        obtain ⟨k, hk⟩ : ∃ k : ℤ, a = b + k * Nat.gcd m n := by
          exact h.symm.dvd.imp fun k hk => by linarith;
        -- By definition of gcd, there exist integers $u$ and $v$ such that $um + vn = \gcd(m, n)$.
        obtain ⟨u, v, huv⟩ : ∃ u v : ℤ, u * m + v * n = Nat.gcd m n := by
          exact Int.gcd_eq_gcd_ab m n ▸ ⟨ Int.gcdA m n, Int.gcdB m n, by ring ⟩;
        use b + k * v * n;
        exact ⟨ Int.modEq_iff_dvd.mpr ⟨ u * k, by push_cast [ hk ] ; linear_combination -huv * k ⟩, Int.modEq_iff_dvd.mpr ⟨ -k * v, by ring ⟩ ⟩

/-
Lemma 2.1: Let $n>1$ be non-intersecting. If $p$ is the smallest prime that divides $n$, then $\frac{n}{p}$ has less than $p$ distinct prime divisors.
-/
theorem non_intersecting_prime_divisors_bound (n : ℕ) (h_ni : IsNonIntersecting n) (h_n_gt_1 : n > 1) :
    (n / n.minFac).primeFactors.card < n.minFac := by
      by_contra h_contra;
      obtain ⟨a, ha⟩ := h_ni
      have h_prime_factors : (n.minFac : ℕ) ≤ ((n / n.minFac).primeFactors).card := by
        linarith
      obtain ⟨S, hS⟩ : ∃ S : Finset ℕ, S ⊆ (n / n.minFac).primeFactors ∧ S.card = n.minFac := by
        exact Finset.le_card_iff_exists_subset_card.mp h_prime_factors
      obtain ⟨q1, q2, hq1, hq2, hq_ne, hq_mod⟩ : ∃ q1 q2 : ℕ, q1 ∈ S ∧ q2 ∈ S ∧ q1 ≠ q2 ∧ a (n.minFac * q1) ≡ a (n.minFac * q2) [ZMOD n.minFac] := by
        have h_pigeonhole : Finset.card (Finset.image (fun q => a (n.minFac * q) % n.minFac) S) ≤ n.minFac - 1 := by
          have h_pigeonhole : Finset.image (fun q => a (n.minFac * q) % n.minFac) S ⊆ Finset.Ico 0 (n.minFac : ℤ) \ {a (n.minFac) % n.minFac} := by
            intro x hx
            obtain ⟨q, hqS, rfl⟩ := Finset.mem_image.mp hx
            have hq_div : n.minFac * q ∣ n := by
              exact Nat.mul_dvd_of_dvd_div ( Nat.minFac_dvd n ) ( Nat.dvd_of_mem_primeFactors ( hS.1 hqS ) )
            have hq_gt1 : 1 < n.minFac * q := by
              exact one_lt_mul_of_lt_of_le ( Nat.Prime.one_lt ( Nat.minFac_prime h_n_gt_1.ne' ) ) ( Nat.pos_of_mem_primeFactors ( hS.1 hqS ) |> Nat.one_le_of_lt )
            have hq_cong : ¬(a (n.minFac * q) ≡ a n.minFac [ZMOD n.minFac]) := by
              have := ha ⟨ a ( n.minFac * q ), n.minFac * q, by nlinarith ⟩ ?_ ⟨ a n.minFac, n.minFac, Nat.minFac_pos _ ⟩ ?_ ?_ <;> simp_all +decide [ Int.ModEq ];
              · simp_all +decide [Nat.coprime_mul_iff_left];
                exact fun h => by have := this ⟨ a ( n.minFac * q ), by simp +decide [ Int.ModEq ], by simp +decide [ Int.ModEq, h ] ⟩ ; linarith;
              · unfold congruences; aesop;
              · simp +decide [ congruences ];
                exact ⟨ ⟨ Nat.minFac_dvd n, by linarith ⟩, Nat.Prime.one_lt ( Nat.minFac_prime h_n_gt_1.ne' ) ⟩;
              · intro h H; simp_all +decide ;
                have := hS.1 hqS; simp_all +decide [ Nat.mem_primeFactors ] ;
            exact Finset.mem_sdiff.mpr ⟨Finset.mem_Ico.mpr ⟨Int.emod_nonneg _ (by
            exact Nat.cast_ne_zero.mpr ( Nat.ne_of_gt ( Nat.minFac_pos _ ) )), Int.emod_lt_of_pos _ (by
            exact Nat.cast_pos.mpr ( Nat.minFac_pos _ ))⟩, by
              simp_all +decide [ Int.ModEq ]⟩;
          refine le_trans ( Finset.card_le_card h_pigeonhole ) ?_ ; simp +decide [ Finset.card_sdiff, * ] ;
          rw [ Finset.inter_eq_left.mpr ] <;> norm_num [ Int.emod_nonneg _ ( Nat.cast_ne_zero.mpr <| Nat.ne_of_gt <| Nat.minFac_pos _ ), Int.emod_lt_of_pos _ ( Nat.cast_pos.mpr <| Nat.minFac_pos _ ) ] ; omega;
        by_cases h_eq : ∀ q1 q2 : ℕ, q1 ∈ S → q2 ∈ S → q1 ≠ q2 → a (n.minFac * q1) % n.minFac ≠ a (n.minFac * q2) % n.minFac;
        · exact absurd h_pigeonhole ( by rw [ Finset.card_image_of_injOn fun q1 hq1 q2 hq2 h => by specialize h_eq q1 q2 hq1 hq2; aesop ] ; exact not_le_of_gt ( Nat.sub_lt ( Nat.minFac_pos _ ) zero_lt_one |> lt_of_lt_of_le <| by linarith ) );
        · exact by push Not at h_eq; obtain ⟨ q1, q2, hq1, hq2, hne, heq ⟩ := h_eq; exact ⟨ q1, q2, hq1, hq2, hne, heq ⟩ ;
      have h_gcd : Nat.gcd (n.minFac * q1) (n.minFac * q2) = n.minFac := by
        simp_all +decide [ Nat.gcd_mul_left ];
        have := Nat.coprime_primes ( Nat.prime_of_mem_primeFactors ( hS.1 hq1 ) ) ( Nat.prime_of_mem_primeFactors ( hS.1 hq2 ) ) ; aesop;
      have h_overlaps : (Congruence.mk (a (n.minFac * q1)) (n.minFac * q1) (by
      exact Nat.mul_pos ( Nat.minFac_pos _ ) ( Nat.pos_of_mem_primeFactors ( hS.1 hq1 ) ))).overlaps (Congruence.mk (a (n.minFac * q2)) (n.minFac * q2) (by
      exact Nat.mul_pos ( Nat.minFac_pos _ ) ( Nat.pos_of_mem_primeFactors ( hS.1 hq2 ) ))) := by
        all_goals generalize_proofs at *;
        apply overlaps_iff_modeq_gcd _ _ _ _ (by
        (expose_names; exact pf)) (by
        positivity) |>.2
        generalize_proofs at *;
        aesop
      generalize_proofs at *;
      have := ha ⟨ a ( n.minFac * q1 ), n.minFac * q1, by linarith ⟩ ?_ ⟨ a ( n.minFac * q2 ), n.minFac * q2, by linarith ⟩ ?_ ?_ h_overlaps <;> simp_all +decide;
      · rw [ eq_comm ] at h_gcd ; aesop;
      · simp +decide [ congruences ];
        exact ⟨ ⟨ Nat.mul_dvd_of_dvd_div ( Nat.minFac_dvd n ) ( Nat.dvd_of_mem_primeFactors ( hS.1 hq1 ) ), by positivity ⟩, by nlinarith [ Nat.Prime.one_lt ( Nat.minFac_prime h_n_gt_1.ne' ), Nat.pos_of_mem_primeFactors ( hS.1 hq1 ) ] ⟩;
      · simp_all +decide [ congruences ];
        exact ⟨ ⟨ Nat.dvd_trans ( Nat.mul_dvd_mul_left _ ( Nat.dvd_of_mem_primeFactors ( hS.1 hq2 ) ) ) ( by rw [ Nat.mul_div_cancel' ( Nat.minFac_dvd n ) ] ), by positivity ⟩, by nlinarith [ Nat.minFac_pos n, Nat.Prime.one_lt ( Nat.minFac_prime h_n_gt_1.ne' ), Nat.pos_of_mem_primeFactors ( hS.1 hq2 ) ] ⟩;
      · exact fun _ => Nat.ne_of_gt ( Nat.minFac_pos _ )
/-
Definition: The sum of reciprocals of divisors of $n$ greater than 1.
Lemma: This sum is equal to the total sum of reciprocals of divisors minus 1.
-/
noncomputable def sum_divisors_gt_1_reciprocal (n : ℕ) : ℚ :=
  ((Nat.divisors n).filter (fun d => 1 < d)).sum (fun d => 1 / (d : ℚ))

theorem sum_divisors_gt_1_eq_total_sub_one (n : ℕ) (hn : n > 0) :
    sum_divisors_gt_1_reciprocal n = sum_divisors_reciprocal n - 1 := by
      unfold sum_divisors_gt_1_reciprocal sum_divisors_reciprocal;
      rw [ show ( Nat.divisors n |> Finset.filter fun x => 1 < x ) = ( Nat.divisors n ) \ { 1 } by ext x; rcases lt_trichotomy x 1 <;> aesop ] ; rw [ Finset.sum_eq_sum_sdiff_singleton_add <| Nat.mem_divisors.mpr <| ⟨ one_dvd _, by aesop ⟩ ] ; ring;

/-
Lemma: For a prime $p$ and any $m$, $\sum_{k=0}^m p^{-k} < \frac{p}{p-1}$.
-/
lemma geometric_series_prime_bound (p : ℕ) (hp : p.Prime) (m : ℕ) :
    ∑ k ∈ Finset.range (m + 1), (1 / (p : ℚ) ^ k) < p / (p - 1) := by
      -- We'll use the formula for the sum of a geometric series to prove this.
      have h_geo_series : ∑ k ∈ Finset.range (m + 1), (1 : ℚ) / p^k = (1 - (1 : ℚ) / p^(m + 1)) / (1 - (1 : ℚ) / p) := by
        rw [ eq_div_iff ];
        · exact Nat.recOn m ( by norm_num ) fun n ih => by norm_num [ pow_succ, Finset.sum_range_succ ] at * ; nlinarith;
        · exact sub_ne_zero_of_ne <| by norm_num; aesop;
      rw [ h_geo_series, div_lt_div_iff₀ ] <;> nlinarith [ show ( p : ℚ ) > 1 from Nat.one_lt_cast.mpr hp.one_lt, one_div_mul_cancel ( show ( p : ℚ ) ≠ 0 from Nat.cast_ne_zero.mpr hp.ne_zero ), one_div_pow ( p : ℚ ) ( m + 1 ), one_div_pos.mpr ( pow_pos ( show ( p : ℚ ) > 0 from Nat.cast_pos.mpr hp.pos ) ( m + 1 ) ) ]

/-
Definition: Case 1 is when $n$ is non-intersecting, $p^2 \nmid n$, and $n/p$ has fewer than $p$ prime factors.
Definition: Case 2 is when $n$ is non-intersecting, $p^2 \mid n$, and $n/p$ has fewer than $p$ prime factors.
Lemma: Any non-intersecting $n > 1$ falls into either Case 1 or Case 2.
-/
def IsCase1 (n : ℕ) : Prop :=
  let p := n.minFac
  n > 1 ∧ ¬(p^2 ∣ n) ∧ (n / p).primeFactors.card < p

def IsCase2 (n : ℕ) : Prop :=
  let p := n.minFac
  n > 1 ∧ p^2 ∣ n ∧ (n / p).primeFactors.card < p

theorem non_intersecting_cases (n : ℕ) (h_ni : IsNonIntersecting n) (h_n_gt_1 : n > 1) :
    IsCase1 n ∨ IsCase2 n := by
  let p := n.minFac
  have h_card := non_intersecting_prime_divisors_bound n h_ni h_n_gt_1
  by_cases hp2 : p^2 ∣ n
  · right
    exact ⟨h_n_gt_1, hp2, h_card⟩
  · left
    exact ⟨h_n_gt_1, hp2, h_card⟩

/-
Lemma: If $p \ge 3$ is prime and $q_0 < q_1 < \dots < q_{s-1}$ are primes greater than $p$, then $q_i \ge p + 2 + i$.
-/
lemma sorted_primes_bound_strong (p : ℕ) (s : ℕ) (q : ℕ → ℕ)
    (hp : p ≥ 3)
    (hp_prime : p.Prime)
    (hq_prime : ∀ i ∈ Finset.range s, (q i).Prime)
    (hq_gt : ∀ i ∈ Finset.range s, q i > p)
    (hq_sorted : ∀ i j, i ∈ Finset.range s → j ∈ Finset.range s → i < j → q i < q j) :
    ∀ i ∈ Finset.range s, q i ≥ p + 2 + i := by
      intro i hi
      induction i with
      | zero =>
        cases Nat.Prime.eq_two_or_odd hp_prime <;> cases Nat.Prime.eq_two_or_odd ( hq_prime 0 hi ) <;> simp_all +arith +decide
        · grind
        · exact Nat.succ_le_of_lt ( lt_of_le_of_ne ( hq_gt 0 hi ) ( Ne.symm <| by omega ) )
      | succ i ih =>
        grind

/-
Lemma: If $p \ge 3$ is prime and $q_0 < q_1 < \dots < q_{s-1}$ are primes greater than $p$, then $\prod_{i=0}^{s-1} \frac{q_i}{q_i-1} \le \frac{p+s+1}{p+1}$.
-/
lemma product_bound_primes_v2 (p : ℕ) (s : ℕ) (q : ℕ → ℕ)
    (hp : p ≥ 3)
    (hp_prime : p.Prime)
    (hq_prime : ∀ i ∈ Finset.range s, (q i).Prime)
    (hq_gt : ∀ i ∈ Finset.range s, q i > p)
    (hq_sorted : ∀ i j, i ∈ Finset.range s → j ∈ Finset.range s → i < j → q i < q j) :
    ∏ i ∈ Finset.range s, ((q i : ℚ) / (q i - 1)) ≤ (p + s + 1) / (p + 1) := by
      -- Applying the inequality $\frac{q_i}{q_i-1} \leq \frac{p+2+i}{p+1+i}$ for each $i$.
      have h_prod_bound : ∀ i ∈ Finset.range s, (q i : ℚ) / ((q i : ℚ) - 1) ≤ (p + 2 + i : ℚ) / (p + 1 + i) := by
        intros i hi; rw [ div_le_div_iff₀ ] <;> norm_cast <;> try linarith [ hq_gt i hi ] ;
        · -- Since $q_i$ is a prime greater than $p$, we have $q_i \geq p + 2 + i$.
          have h_q_ge : q i ≥ p + 2 + i := by
            exact sorted_primes_bound_strong p s q hp hp_prime hq_prime hq_gt hq_sorted i hi
          norm_num [ Int.subNatNat_eq_coe ] ; linarith [ hq_gt i hi ] ;
        · rw [ Int.subNatNat_eq_coe ] ; norm_num ; linarith [ hq_gt i hi ] ;
      refine le_trans ( Finset.prod_le_prod ?_ h_prod_bound ) ?_;
      · exact fun i hi => div_nonneg ( Nat.cast_nonneg _ ) ( sub_nonneg_of_le ( mod_cast Nat.one_le_iff_ne_zero.mpr ( Nat.Prime.ne_zero ( hq_prime i hi ) ) ) );
      · -- By induction on $s$, we can show that the product telescopes.
        induction s with
        | zero =>
          norm_num [ show ( p : ℚ ) + 1 ≠ 0 by positivity ]
        | succ s ih =>
          rw [ Finset.prod_range_succ, Nat.cast_succ ]
          exact le_trans ( mul_le_mul_of_nonneg_right ( ih ( fun i hi => hq_prime i ( Finset.mem_range.mpr ( Nat.lt_succ_of_lt ( Finset.mem_range.mp hi ) ) ) ) ( fun i hi => hq_gt i ( Finset.mem_range.mpr ( Nat.lt_succ_of_lt ( Finset.mem_range.mp hi ) ) ) ) ( fun i j hi hj hij => hq_sorted i j ( Finset.mem_range.mpr ( Nat.lt_succ_of_lt ( Finset.mem_range.mp hi ) ) ) ( Finset.mem_range.mpr ( Nat.lt_succ_of_lt ( Finset.mem_range.mp hj ) ) ) hij ) ( fun i hi => h_prod_bound i ( Finset.mem_range.mpr ( Nat.lt_succ_of_lt ( Finset.mem_range.mp hi ) ) ) ) ) ( by positivity ) ) ( by rw [ div_mul_div_comm, div_le_div_iff₀ ] <;> ring_nf <;> nlinarith )

/-
Lemma: For $n > 1$, $\sum_{d|n} \frac{1}{d} < \prod_{p|n} \frac{p}{p-1}$.
-/
lemma sum_divisors_reciprocal_lt_prod_geometric (n : ℕ) (hn : n > 1) :
    sum_divisors_reciprocal n < ∏ p ∈ n.primeFactors, ((p : ℚ) / (p - 1)) := by
      rw [ sum_divisors_reciprocal_eq_prod_sum_prime_powers ];
      · fapply Finset.prod_lt_prod;
        · exact fun p hp => Finset.sum_pos ( fun _ _ => one_div_pos.mpr ( pow_pos ( Nat.cast_pos.mpr ( Nat.pos_of_mem_primeFactors hp ) ) _ ) ) ( by norm_num );
        · intro p hp
          have h_geo_series : ∑ k ∈ Finset.range (Nat.factorization n p + 1), (1 / (p : ℚ) ^ k) < (p : ℚ) / (p - 1) := by
            convert geometric_series_prime_bound p ( Nat.prime_of_mem_primeFactors hp ) ( Nat.factorization n p ) using 1
          exact h_geo_series.le;
        · refine ⟨ n.minFac, ?_, ?_ ⟩;
          · exact Nat.mem_primeFactors.mpr ⟨ Nat.minFac_prime hn.ne', Nat.minFac_dvd n, by aesop ⟩;
          · convert geometric_series_prime_bound n.minFac ( Nat.minFac_prime hn.ne' ) ( n.factorization n.minFac ) using 1;
      · linarith

/-
Lemma: If $\gcd(m, n) = 1$, then $\sigma_{-1}(mn) = \sigma_{-1}(m)\sigma_{-1}(n)$.
-/
lemma sum_divisors_reciprocal_eq_mul_of_coprime {m n : ℕ} (h : m.Coprime n) :
    sum_divisors_reciprocal (m * n) = sum_divisors_reciprocal m * sum_divisors_reciprocal n := by
      -- By definition of divisors, we can write the divisors of $mn$ as $\{d \cdot d' \mid d \mid m, d' \mid n\}$.
      have h_divisors : Nat.divisors (m * n) = Finset.image (fun (p : ℕ × ℕ) => p.1 * p.2) (Nat.divisors m ×ˢ Nat.divisors n) := by
        exact Nat.divisors_mul _ _;
      unfold sum_divisors_reciprocal;
      rw [ h_divisors, Finset.sum_image, Finset.sum_product ];
      · simp +decide [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul, mul_comm ];
      · intros p hp q hq h_eq;
        -- Since $p$ and $q$ are divisors of $m$ and $n$ respectively, and $m$ and $n$ are coprime, it follows that $p.1 = q.1$ and $p.2 = q.2$.
        have h_eq1 : p.1 = q.1 := by
          simp +zetaDelta at *;
          exact Nat.dvd_antisymm ( by exact ( Nat.Coprime.dvd_of_dvd_mul_right ( Nat.Coprime.coprime_dvd_left hp.1.1 <| Nat.Coprime.coprime_dvd_right hq.2.1 h ) ) <| h_eq ▸ dvd_mul_right _ _ ) ( by exact ( Nat.Coprime.dvd_of_dvd_mul_right ( Nat.Coprime.coprime_dvd_left hq.1.1 <| Nat.Coprime.coprime_dvd_right hp.2.1 h ) ) <| h_eq.symm ▸ dvd_mul_right _ _ )
        have h_eq2 : p.2 = q.2 := by
          aesop
        aesop

/-
Lemma: If $m$ has $s$ prime factors all greater than $p \ge 3$, then $\prod_{q|m} \frac{q}{q-1} \le \frac{p+s+1}{p+1}$.
-/
lemma prod_prime_factors_geometric_bound (p : ℕ) (m : ℕ) (s : ℕ)
    (hp : p ≥ 3)
    (hp_prime : p.Prime)
    (hs : m.primeFactors.card = s)
    (hm_gt : ∀ q ∈ m.primeFactors, q > p) :
    ∏ q ∈ m.primeFactors, ((q : ℚ) / (q - 1)) ≤ (p + s + 1 : ℚ) / (p + 1) := by
      -- Let $q_k$ be the $k$-th prime greater than $p$. We need to show that $\prod_{k=0}^{s-1} \frac{q_k}{q_k-1} \le \frac{p+s+1}{p+1}$.
      have h_prod_bound : ∀ (s : ℕ) (q : ℕ → ℕ), (∀ i ∈ Finset.range s, q i > p) → (∀ i j, i ∈ Finset.range s → j ∈ Finset.range s → i < j → q i < q j) → (∀ i ∈ Finset.range s, Nat.Prime (q i)) → (∏ i ∈ Finset.range s, ((q i : ℚ) / (q i - 1))) ≤ (p + s + 1 : ℚ) / (p + 1) := by
        exact fun s q a a_1 a_2 => product_bound_primes_v2 p s q hp hp_prime a_2 a a_1;
      -- Let $q$ be a function that maps each index $i$ in the range $s$ to the $i$-th prime factor of $m$.
      obtain ⟨q, hq⟩ : ∃ q : ℕ → ℕ, (∀ i ∈ Finset.range s, q i > p) ∧ (∀ i j, i ∈ Finset.range s → j ∈ Finset.range s → i < j → q i < q j) ∧ (∀ i ∈ Finset.range s, Nat.Prime (q i)) ∧ m.primeFactors = Finset.image q (Finset.range s) := by
        -- Since $m$ has exactly $s$ prime factors greater than $p$, we can order them as $q_0 < q_1 < \dots < q_{s-1}$.
        obtain ⟨q_sorted, hq_sorted⟩ : ∃ q_sorted : Fin s → ℕ, (∀ i, Nat.Prime (q_sorted i)) ∧ (∀ i, q_sorted i > p) ∧ StrictMono q_sorted ∧ m.primeFactors = Finset.image q_sorted Finset.univ := by
          obtain ⟨q_sorted, hq_sorted⟩ : ∃ q_sorted : Fin s → ℕ, StrictMono q_sorted ∧ ∀ i, q_sorted i ∈ m.primeFactors := by
            exact ⟨ fun i => m.primeFactors.orderEmbOfFin ( by aesop ) i, by aesop_cat, fun i => by aesop ⟩;
          use q_sorted;
          exact ⟨ fun i => Nat.prime_of_mem_primeFactors ( hq_sorted.2 i ), fun i => hm_gt _ ( hq_sorted.2 i ), hq_sorted.1, by rw [ Finset.eq_of_subset_of_card_le ( Finset.image_subset_iff.mpr fun i _ => hq_sorted.2 i ) ( by rw [ Finset.card_image_of_injective _ hq_sorted.1.injective, Finset.card_fin, hs ] ) ] ⟩;
        use fun i => if hi : i < s then q_sorted ⟨ i, hi ⟩ else p + 1;
        simp_all +decide [ Finset.ext_iff ];
        exact ⟨ fun i j hi hj hij => hq_sorted.2.2.1 ( Nat.lt_of_le_of_lt ( Nat.le_refl _ ) hij ), fun a => ⟨ fun ⟨ i, hi ⟩ => ⟨ i, Fin.is_lt i, by aesop ⟩, fun ⟨ i, hi, hi' ⟩ => ⟨ ⟨ i, hi ⟩, by aesop ⟩ ⟩ ⟩;
      rw [ hq.2.2.2, Finset.prod_image ];
      · exact h_prod_bound s q hq.1 hq.2.1 hq.2.2.1;
      · exact fun i hi j hj hij => le_antisymm ( le_of_not_gt fun hi' => by linarith [ hq.2.1 _ _ hj hi hi' ] ) ( le_of_not_gt fun hj' => by linarith [ hq.2.1 _ _ hi hj hj' ] )

/-
Lemma: If $m$ has $s$ prime factors all greater than $p \ge 3$, then $\prod_{q|m} \frac{q}{q-1} \le \frac{p+s+1}{p+1}$.
-/
lemma prod_prime_factors_geometric_bound_v2 (p : ℕ) (m : ℕ) (s : ℕ)
    (hp : p ≥ 3)
    (hp_prime : p.Prime)
    (hs : m.primeFactors.card = s)
    (hm_gt : ∀ q ∈ m.primeFactors, q > p) :
    ∏ q ∈ m.primeFactors, ((q : ℚ) / (q - 1)) ≤ (p + s + 1 : ℚ) / (p + 1) := by
      convert prod_prime_factors_geometric_bound p m s hp hp_prime hs hm_gt using 1

/-
Lemma: If $n$ satisfies Case 1, then $\gcd(p, n/p) = 1$.
-/
lemma case1_coprime (n : ℕ) (h_case1 : IsCase1 n) :
    Nat.Coprime n.minFac (n / n.minFac) := by
  let p := n.minFac
  have hp : p.Prime := Nat.minFac_prime h_case1.1.ne'
  have h_not_dvd : ¬(p ∣ (n / p)) := by
    intro h
    have : p * p ∣ n := Nat.mul_dvd_of_dvd_div (Nat.minFac_dvd n) h
    have : p^2 ∣ n := by rwa [Nat.pow_two]
    exact h_case1.2.1 this
  exact (Nat.Prime.coprime_iff_not_dvd hp).mpr h_not_dvd

/-
Lemma: If $n > 1$ is odd, then its smallest prime factor is at least 3.
-/
lemma minFac_ge_3_of_odd (n : ℕ) (h_n_gt_1 : n > 1) (h_odd : Odd n) :
    n.minFac ≥ 3 := by
      contrapose! h_odd; interval_cases _ : Nat.minFac n <;> simp_all +decide [ ← even_iff_two_dvd, parity_simps ] ;
      exact absurd ‹_› ( Nat.ne_of_gt ( Nat.minFac_pos _ ) )

/-
Lemma: If $m > 1$ has $s$ prime factors all greater than $p \ge 3$, then $\sigma_{-1}(m) < \frac{p+s+1}{p+1}$.
-/
lemma sum_reciprocal_m_bound (p m s : ℕ) (hp : p ≥ 3) (hp_prime : p.Prime)
    (hs : m.primeFactors.card = s) (hm_gt : ∀ q ∈ m.primeFactors, q > p) (hm_gt_1 : m > 1) :
    sum_divisors_reciprocal m < (p + s + 1 : ℚ) / (p + 1) := by
  have h_lt_prod : sum_divisors_reciprocal m < ∏ q ∈ m.primeFactors, ((q : ℚ) / (q - 1)) :=
    sum_divisors_reciprocal_lt_prod_geometric m hm_gt_1
  have h_prod_le : ∏ q ∈ m.primeFactors, ((q : ℚ) / (q - 1)) ≤ (p + s + 1 : ℚ) / (p + 1) :=
    prod_prime_factors_geometric_bound_v2 p m s hp hp_prime hs hm_gt
  exact lt_of_lt_of_le h_lt_prod h_prod_le

/-
Lemma: If $n$ is odd, non-intersecting, and in Case 1, then $\sum_{d|n} \frac{1}{d} < 2$.
-/
lemma case_1a_sum_bound (n : ℕ) (h_n_gt_1 : n > 1)
    (h_case1 : IsCase1 n) (h_odd : Odd n) :
    sum_divisors_reciprocal n < 2 := by
      -- By Lemma~\ref{lem:minFac_ge_3_of_odd}, $p \ge 3$. By Lemma~\ref{lem:non_intersecting_prime_divisors_bound_final}, $s < p$.
      obtain ⟨p, hp_prime, hp_min, hp_ge_3⟩ : ∃ p, Nat.Prime p ∧ p = Nat.minFac n ∧ p ≥ 3 := by
        exact ⟨ _, Nat.minFac_prime h_n_gt_1.ne', rfl, minFac_ge_3_of_odd n h_n_gt_1 h_odd ⟩
      obtain ⟨s, hs⟩ : ∃ s, (n / p).primeFactors.card = s ∧ s < p := by
        exact ⟨ _, rfl, by simpa [ hp_min ] using h_case1.2.2 ⟩;
      -- Let $n/p = m$. By Lemma~\ref{lem:case1_coprime}, $m$ and $p$ are coprime. By Lemma~\ref{lem:sum_divisors_reciprocal_eq_mul_of_coprime}, $\sigma_{-1}(n) = \sigma_{-1}(p)\sigma_{-1}(m) = (1+1/p)\sigma_{-1}(m)$.
      have h_sigma_n : sum_divisors_reciprocal n = (1 + 1 / (p : ℚ)) * sum_divisors_reciprocal (n / p) := by
        have h_sigma_n : sum_divisors_reciprocal n = sum_divisors_reciprocal p * sum_divisors_reciprocal (n / p) := by
          have h_sigma_mul : Nat.Coprime p (n / p) := by
            convert case1_coprime n h_case1 using 1 ; aesop;
          rw [ ← sum_divisors_reciprocal_eq_mul_of_coprime h_sigma_mul, Nat.mul_div_cancel' ( hp_min ▸ Nat.minFac_dvd n ) ];
        rw [ h_sigma_n, show sum_divisors_reciprocal p = 1 + 1 / ( p : ℚ ) from ?_ ];
        unfold sum_divisors_reciprocal; rw [ hp_prime.sum_divisors ] ; norm_num; ring;
      -- If $n/p > 1$, then by Lemma~\ref{lem:sum_reciprocal_m_bound}, $\sigma_{-1}(n/p) < \frac{p+s+1}{p+1}$.
      by_cases h_np_gt_1 : n / p > 1;
      · have h_sigma_np : sum_divisors_reciprocal (n / p) < (p + s + 1 : ℚ) / (p + 1) := by
          apply sum_reciprocal_m_bound p (n / p) s hp_ge_3 hp_prime hs.left (by
          intro q hq; have := Nat.dvd_of_mem_primeFactors hq; simp_all +decide ;
          refine lt_of_le_of_ne ?_ ?_;
          · exact Nat.minFac_le_of_dvd hq.1.two_le ( dvd_trans hq.2.1 ( Nat.div_dvd_of_dvd ( Nat.minFac_dvd n ) ) );
          · rintro rfl; simp_all +decide [ Nat.dvd_div_iff_mul_dvd ( Nat.minFac_dvd n ) ] ;
            exact h_case1.2.1 ( by simpa only [ sq ] using hq.1 )) h_np_gt_1;
        refine h_sigma_n ▸ lt_of_lt_of_le ( mul_lt_mul_of_pos_left h_sigma_np ( by positivity ) ) ?_;
        rw [ one_add_div, div_mul_div_comm, div_le_iff₀ ] <;> nlinarith only [ show ( p : ℚ ) ≥ 3 by norm_cast, show ( s : ℚ ) + 1 ≤ p by norm_cast; linarith ];
      · interval_cases _ : n / p <;> simp_all +decide [ IsCase1 ];
        · exact absurd ( ‹n.minFac = s ∨ n < n.minFac›.resolve_left ( by linarith ) ) ( not_lt_of_ge ( Nat.minFac_le h_n_gt_1.le ) );
        · unfold sum_divisors_reciprocal; norm_num; nlinarith [ inv_mul_cancel₀ ( by positivity : ( n.minFac : ℚ ) ≠ 0 ), ( by norm_cast : ( 3 : ℚ ) ≤ n.minFac ) ] ;

/-
If $n$ is even and in Case 1, then $n=2$ or $n=2q^k$ for some odd prime $q$.
-/
lemma case_1b_structure (n : ℕ) (h_ni : IsNonIntersecting n) (h_n_gt_1 : n > 1)
    (h_case1 : IsCase1 n) (h_even : Even n) :
    n = 2 ∨ ∃ q k : ℕ, q.Prime ∧ q > 2 ∧ k ≥ 1 ∧ n = 2 * q ^ k := by
      -- Since $n$ is even and in Case 1, we have $n = 2 * (n / 2)$.
      obtain ⟨k, hk⟩ : ∃ k : ℕ, n = 2 * k := by
        exact even_iff_two_dvd.mp h_even
      obtain ⟨hk₁, hk₂⟩ := h_case1
      simp_all +decide;
      rcases k with ( _ | _ | k ) <;> simp_all +decide [Nat.minFac_eq];
      rcases hk₂ with ⟨ hk₂, hk₃ ⟩ ; interval_cases _ : Finset.card _ <;> simp_all +decide ;
      -- Since $k + 2$ has exactly one prime factor $q$, we can write $k + 2 = q^x$ for some $x \geq 1$.
      obtain ⟨q, x, hq_prime, hx_pos, hk2⟩ : ∃ q x : ℕ, Nat.Prime q ∧ x ≥ 1 ∧ k + 2 = q ^ x := by
        have := Finset.card_eq_one.mp ‹_›; obtain ⟨ q, hq ⟩ := this; simp_all +decide [ Finset.eq_singleton_iff_unique_mem ] ;
        exact ⟨ q, hq.1.1, Nat.primeFactorsList ( k + 2 ) |> List.count q, List.count_pos_iff.mpr ( by aesop ), by nth_rw 1 [ ← Nat.prod_primeFactorsList ( by linarith : k + 2 ≠ 0 ) ] ; rw [ List.prod_eq_pow_single q ] ; aesop ⟩;
      exact ⟨ q, hq_prime, lt_of_le_of_ne hq_prime.two_le ( Ne.symm <| by rintro rfl; exact hk₂ <| hk2.symm ▸ ⟨ 2 ^ ( x - 1 ), by cases x <;> simp_all +decide [ pow_succ' ] ; linarith ⟩ ), x, hx_pos, hk2 ⟩

/-
The density of a covering set is 1.
-/
def count_covered (S : Finset Congruence) (m : ℕ) : ℕ :=
  (Finset.range m).filter (fun x => ∃ c ∈ S, x ≡ c.a [ZMOD c.d]) |>.card

noncomputable def density (S : Finset Congruence) (m : ℕ) : ℚ :=
  (count_covered S m : ℚ) / m

theorem density_of_covering (S : Finset Congruence) (m : ℕ) (hm : m > 0)
    (h_cov : IsCovering S) : density S m = 1 := by
      unfold density;
      field_simp;
      norm_cast;
      convert Finset.card_range m;
      refine Finset.card_bij ( fun x hx => Int.toNat x ) ?_ ?_ ?_ <;> aesop

/-
If a subset of a CD congruence set is not pairwise coprime, its intersection is empty.
-/
def pairwise_coprime (I : Finset Congruence) : Prop :=
  ∀ c1 ∈ I, ∀ c2 ∈ I, c1 ≠ c2 → Nat.Coprime c1.d c2.d

noncomputable def density_formula (S : Finset Congruence) : ℚ :=
  ∑ I ∈ S.powerset.filter (fun I => I.Nonempty ∧ pairwise_coprime I),
    (-1 : ℚ) ^ (I.card - 1) * (1 / (∏ c ∈ I, (c.d : ℚ)))

noncomputable def density_val (S : Finset Congruence) : ℚ :=
  let D := S.lcm (fun c => c.d)
  if D = 0 then 0 else (count_covered S D : ℚ) / D

theorem pairwise_coprime_subset {S : Finset Congruence} {I : Finset Congruence} (h : I ⊆ S) (hS : IsCD S) :
    ¬ pairwise_coprime I → ∀ x : ℤ, ¬ (∀ c ∈ I, x ≡ c.a [ZMOD c.d]) := by
      intro h_not_pairwise_coprime x hx;
      contrapose! h_not_pairwise_coprime;
      refine fun a ha b hb hab => ?_;
      exact hS a ( h ha ) b ( h hb ) hab ( by exact ⟨ x, hx a ha, hx b hb ⟩ )

/-
The number of solutions to a pairwise coprime system of congruences in the range $[0, D)$ is $D / \prod d_i$.
-/
def intersection_count (I : Finset Congruence) (m : ℕ) : ℕ :=
  (Finset.range m).filter (fun x => ∀ c ∈ I, x ≡ c.a [ZMOD c.d]) |>.card

set_option maxHeartbeats 1000000 in
-- The CRT counting proof times out at the default heartbeat limit.
theorem intersection_count_pairwise_coprime (S : Finset Congruence) (I : Finset Congruence)
    (hI : I ⊆ S) (h_coprime : pairwise_coprime I) :
    let D := S.lcm (fun c => c.d)
    intersection_count I D = D / (∏ c ∈ I, c.d) := by
      apply le_antisymm;
      · -- Let $P = \prod_{c \in I} c.d$. Then $P$ divides $D$.
        set P := ∏ c ∈ I, c.d
        have hP_div_D : P ∣ S.lcm (fun c => c.d) := by
          have hP_div_D : P ∣ Finset.lcm I (fun c => c.d) := by
            have hP_div_D : ∀ c ∈ I, c.d ∣ Finset.lcm I (fun c => c.d) := by
              exact fun c hc => Finset.dvd_lcm hc;
            have hP_div_D : ∀ {T : Finset Congruence}, (∀ c ∈ T, c.d ∣ Finset.lcm I (fun c => c.d)) → (∀ c1 ∈ T, ∀ c2 ∈ T, c1 ≠ c2 → Nat.Coprime c1.d c2.d) → (∏ c ∈ T, c.d) ∣ Finset.lcm I (fun c => c.d) := by
              intros T hT_div hT_coprime
              induction T using Finset.induction with
              | empty =>
                simp
              | insert c T hcT ih =>
                rw [ Finset.prod_insert hcT ]
                exact Nat.Coprime.mul_dvd_of_dvd_of_dvd ( show Nat.Coprime ( c.d ) ( ∏ x ∈ T, x.d ) from Nat.Coprime.prod_right fun x hx => hT_coprime c ( Finset.mem_insert_self _ _ ) x ( Finset.mem_insert_of_mem hx ) <| by aesop ) ( hT_div c <| Finset.mem_insert_self _ _ ) ( ih ( fun x hx => hT_div x <| Finset.mem_insert_of_mem hx ) ( fun x hx y hy hxy => hT_coprime x ( Finset.mem_insert_of_mem hx ) y ( Finset.mem_insert_of_mem hy ) hxy ) );
            exact hP_div_D ‹_› h_coprime;
          exact dvd_trans hP_div_D ( Finset.lcm_dvd fun x hx => Finset.dvd_lcm ( hI hx ) );
        -- By the Chinese Remainder Theorem, there exists a unique solution modulo $P$ to the system of congruences.
        obtain ⟨x₀, hx₀⟩ : ∃ x₀ : ℤ, ∀ c ∈ I, x₀ ≡ c.a [ZMOD c.d] := by
          -- Applying the Chinese Remainder Theorem, we can find such an $x₀$.
          have h_crt : ∀ c ∈ I, ∃ x₀ : ℤ, x₀ ≡ c.a [ZMOD c.d] ∧ ∀ d ∈ I, d ≠ c → x₀ ≡ 0 [ZMOD d.d] := by
            -- For each $c \in I$, let $y_c$ be the multiplicative inverse of $\prod_{d \in I, d \neq c} d.d$ modulo $c.d$.
            intro c hc
            obtain ⟨y_c, hy_c⟩ : ∃ y_c : ℤ, y_c * (∏ d ∈ I.erase c, d.d) ≡ 1 [ZMOD c.d] := by
              have h_coprime_prod : Nat.Coprime (∏ d ∈ I.erase c, d.d) c.d := by
                exact Nat.Coprime.prod_left fun x hx => h_coprime x ( Finset.mem_of_mem_erase hx ) c hc ( by aesop );
              have := Nat.gcd_eq_gcd_ab ( ∏ d ∈ I.erase c, d.d ) c.d;
              exact ⟨ Nat.gcdA _ _, Int.modEq_iff_dvd.mpr ⟨ Nat.gcdB _ _, by push_cast at *; linarith ⟩ ⟩;
            use y_c * (∏ d ∈ I.erase c, d.d) * c.a;
            exact ⟨ by simpa using hy_c.mul_right _, fun d hd hcd => Int.modEq_zero_iff_dvd.mpr <| dvd_mul_of_dvd_left ( dvd_mul_of_dvd_right ( mod_cast Finset.dvd_prod_of_mem _ <| by aesop ) _ ) _ ⟩;
          choose! f hf₁ hf₂ using h_crt;
          use ∑ c ∈ I, f c;
          intro c hc; simp_all +decide [ ← ZMod.intCast_eq_intCast_iff ] ;
          rw [ Finset.sum_eq_single c ] <;> aesop;
        -- The solutions in $\{0, \dots, D-1\}$ are exactly those $x$ such that $x \equiv x_0 \pmod P$.
        have h_solutions : ∀ x : ℕ, x < S.lcm (fun c => c.d) → (∀ c ∈ I, (x : ℤ) ≡ c.a [ZMOD c.d]) → ∃ k : ℕ, k < (S.lcm (fun c => c.d)) / P ∧ x = Int.toNat (x₀ % P + k * P) := by
          intros x hx_lt hx_congr
          obtain ⟨k, hk⟩ : ∃ k : ℤ, x = x₀ % P + k * P := by
            have h_congr : x ≡ x₀ % P [ZMOD P] := by
              simp_all +decide [ Int.ModEq ];
              rw [ Int.emod_eq_emod_iff_emod_sub_eq_zero ];
              simp +zetaDelta at *;
              refine Finset.prod_dvd_of_coprime ?_ ?_;
              · intro c hc d hd hcd; specialize h_coprime c hc d hd hcd; aesop;
              · exact fun c hc => Int.dvd_of_emod_eq_zero ( by rw [ Int.sub_emod, hx_congr c hc, hx₀ c hc ] ; norm_num );
            exact h_congr.symm.dvd.imp fun k hk => by linarith;
          refine ⟨ Int.toNat k, ?_, ?_ ⟩;
          · have h_k_lt : k < (S.lcm (fun c => c.d)) / P := by
              nlinarith [ Int.emod_nonneg x₀ ( show ( P : ℤ ) ≠ 0 from mod_cast Finset.prod_ne_zero_iff.mpr fun c hc => Nat.ne_of_gt <| c.d_pos ), Int.emod_lt_of_pos x₀ ( show ( P : ℤ ) > 0 from mod_cast Finset.prod_pos fun c hc => c.d_pos ), Nat.div_mul_cancel hP_div_D ];
            nlinarith [ Int.toNat_of_nonneg ( show 0 ≤ k from by nlinarith [ Int.emod_nonneg x₀ ( show ( P : ℤ ) ≠ 0 from mod_cast Finset.prod_ne_zero_iff.mpr fun c hc => Nat.ne_of_gt ( c.d_pos ) ), Int.emod_lt_of_pos x₀ ( show ( P : ℤ ) > 0 from mod_cast Finset.prod_pos fun c hc => c.d_pos ) ] ), Nat.div_mul_le_self ( S.lcm fun c => c.d ) P ];
          · rw [ Int.toNat_of_nonneg ];
            · exact hk ▸ rfl;
            · nlinarith [ Int.emod_nonneg x₀ ( show ( P : ℤ ) ≠ 0 from mod_cast Finset.prod_ne_zero_iff.mpr fun c hc => Nat.cast_ne_zero.mpr <| Nat.ne_of_gt <| c.d_pos ), Int.emod_lt_of_pos x₀ ( show ( P : ℤ ) > 0 from mod_cast Finset.prod_pos fun c hc => Nat.cast_pos.mpr <| c.d_pos ) ];
        -- Therefore, the number of solutions is at most $(S.lcm (fun c => c.d)) / P$.
        have h_card_solutions : (Finset.filter (fun x : ℕ => ∀ c ∈ I, (x : ℤ) ≡ c.a [ZMOD c.d]) (Finset.range (S.lcm (fun c => c.d)))).card ≤ (S.lcm (fun c => c.d)) / P := by
          exact le_trans ( Finset.card_le_card fun x hx => show x ∈ Finset.image ( fun k : ℕ => Int.toNat ( x₀ % P + k * P ) ) ( Finset.range ( ( S.lcm fun c => c.d ) / P ) ) from by obtain ⟨ k, hk₁, rfl ⟩ := h_solutions x ( Finset.mem_range.mp ( Finset.mem_filter.mp hx |>.1 ) ) ( Finset.mem_filter.mp hx |>.2 ) ; exact Finset.mem_image.mpr ⟨ k, Finset.mem_range.mpr hk₁, rfl ⟩ ) ( Finset.card_image_le.trans ( by simp ) );
        refine (le_of_eq ?_).trans h_card_solutions;
        refine Finset.card_bij ( fun x hx => Int.toNat x ) ?_ ?_ ?_ <;> simp +decide;
        · tauto;
      · refine Nat.le_of_not_lt fun h => ?_;
        -- Since $I$ is pairwise coprime, there exists an integer $x_0$ such that $x_0 \equiv c.a \pmod{c.d}$ for all $c \in I$.
        obtain ⟨x₀, hx₀⟩ : ∃ x₀ : ℤ, ∀ c ∈ I, x₀ ≡ c.a [ZMOD c.d] := by
          -- Applying the Chinese Remainder Theorem.
          have h_crt : ∀ c ∈ I, ∃ x₀ : ℤ, x₀ ≡ c.a [ZMOD c.d] ∧ ∀ c' ∈ I, c' ≠ c → x₀ ≡ 0 [ZMOD c'.d] := by
            -- For each $c \in I$, let $y_c$ be the multiplicative inverse of $\prod_{c' \in I, c' \neq c} c'.d$ modulo $c.d$.
            intro c hc
            obtain ⟨y_c, hy_c⟩ : ∃ y_c : ℤ, y_c * (∏ c' ∈ I \ {c}, (c'.d : ℤ)) ≡ 1 [ZMOD (c.d : ℤ)] := by
              have h_coprime_prod : Nat.gcd (∏ c' ∈ I \ {c}, c'.d) c.d = 1 := by
                exact Nat.Coprime.prod_left fun x hx => h_coprime x ( by aesop ) c hc ( by aesop );
              have := Nat.gcd_eq_gcd_ab ( ∏ c' ∈ I \ { c }, c'.d ) c.d;
              exact ⟨ Nat.gcdA _ _, Int.modEq_iff_dvd.mpr ⟨ Nat.gcdB _ _, by push_cast at *; linarith ⟩ ⟩;
            use y_c * (∏ c' ∈ I \ {c}, (c'.d : ℤ)) * c.a;
            exact ⟨ by simpa using hy_c.mul_right _, fun c' hc' hc'' => Int.modEq_zero_iff_dvd.mpr <| dvd_mul_of_dvd_left ( dvd_mul_of_dvd_right ( Finset.dvd_prod_of_mem _ <| by aesop ) _ ) _ ⟩;
          choose! f hf₁ hf₂ using h_crt;
          use ∑ c ∈ I, f c;
          intro c hc; simp_all +decide only [Int.ModEq];
          rw [ Finset.sum_int_mod, Finset.sum_eq_single c ] <;> aesop;
        -- The solutions in $\{0, \dots, D-1\}$ are exactly those $x$ such that $x \equiv x_0 \pmod P$.
        have h_solutions : (Finset.range (S.lcm (fun c => c.d))).filter (fun x => ∀ c ∈ I, (x : ℤ) ≡ c.a [ZMOD c.d]) ⊇ Finset.image (fun m => Int.toNat (x₀ % (Finset.prod I (fun c => c.d)) + m * (Finset.prod I (fun c => c.d)))) (Finset.range ((S.lcm (fun c => c.d)) / (Finset.prod I (fun c => c.d)))) := by
          simp +decide [ Finset.subset_iff ];
          intro a ha; refine ⟨ ?_, ?_ ⟩;
          · refine ⟨ Int.toNat ( max ( x₀ % ∏ i ∈ I, ( i.d : ℤ ) + a * ∏ i ∈ I, ( i.d : ℤ ) ) 0 ), ?_, ?_ ⟩ <;> norm_num [ Int.toNat_of_nonneg ( le_max_right _ _ ) ];
            refine ⟨ ?_, Nat.pos_of_ne_zero ?_ ⟩;
            · have hP_pos_nat : 0 < ∏ c ∈ I, c.d := by
                exact Finset.prod_pos fun c _ => c.d_pos
              have hP_pos_int : 0 < ∏ c ∈ I, (c.d : ℤ) := by
                exact Finset.prod_pos fun c _ => Nat.cast_pos.mpr c.d_pos
              have ha_lt : a < (S.lcm fun c => c.d) / (∏ c ∈ I, c.d) :=
                ha
              have hmul_le_nat :
                  (a + 1) * (∏ c ∈ I, c.d) ≤ S.lcm (fun c => c.d) := by
                exact le_trans
                  (Nat.mul_le_mul_right _ (Nat.succ_le_of_lt ha_lt))
                  (Nat.div_mul_le_self _ _)
              have hmul_le_int :
                  ((a + 1) * (∏ c ∈ I, c.d) : ℤ) ≤ S.lcm (fun c => c.d) := by
                exact_mod_cast hmul_le_nat
              have hem_lt :
                  x₀ % (∏ c ∈ I, (c.d : ℤ)) < ∏ c ∈ I, (c.d : ℤ) :=
                Int.emod_lt_of_pos _ hP_pos_int
              nlinarith
            · intro H; simp_all +decide ;
          · intro c hc; rw [ max_eq_left ( by nlinarith [ Int.emod_nonneg x₀ ( show ( ∏ i ∈ I, ( i.d : ℤ ) ) ≠ 0 from Finset.prod_ne_zero_iff.mpr fun i hi => Nat.cast_ne_zero.mpr <| Nat.ne_of_gt <| i.d_pos ), show ( ∏ i ∈ I, ( i.d : ℤ ) ) > 0 from Finset.prod_pos fun i hi => Nat.cast_pos.mpr <| i.d_pos ] ) ] ; simp_all +decide [ Int.ModEq ] ;
            simp +decide [ ← hx₀ c hc, Int.add_emod, Int.mul_emod, Finset.prod_eq_prod_sdiff_singleton_mul hc ];
        refine h.not_ge ( le_trans ?_ ( Finset.card_mono h_solutions ) );
        rw [ Finset.card_image_of_injOn ];
        · norm_num [ Finset.card_image_of_injective, Function.Injective ];
        · intro m hm m' hm' h_eq; simp_all +decide ;
          rw [ max_eq_left, max_eq_left ] at h_eq;
          · exact mul_left_cancel₀ ( show ( ∏ i ∈ I, ( i.d : ℤ ) ) ≠ 0 from Finset.prod_ne_zero_iff.mpr fun i hi => Nat.cast_ne_zero.mpr <| Nat.ne_of_gt <| i.d_pos ) <| by linarith;
          · exact add_nonneg ( Int.emod_nonneg _ <| Finset.prod_ne_zero_iff.mpr fun i hi => Nat.cast_ne_zero.mpr <| ne_of_gt <| i.d_pos ) <| mul_nonneg ( by obtain ⟨ x, hx, rfl ⟩ := hm'; positivity ) <| Finset.prod_nonneg fun i hi => Nat.cast_nonneg _;
          · exact add_nonneg ( Int.emod_nonneg _ <| Finset.prod_ne_zero_iff.mpr fun i hi => Nat.cast_ne_zero.mpr <| ne_of_gt <| i.d_pos ) <| mul_nonneg ( by obtain ⟨ x, hx, rfl ⟩ := hm; positivity ) <| Finset.prod_nonneg fun i hi => Nat.cast_nonneg _

/-
Lemma 2.1 (Good): The density of a CD congruence set is given by the inclusion-exclusion formula over pairwise coprime subsets of moduli.
-/
set_option maxHeartbeats 1000000 in
-- The inclusion-exclusion proof times out at the default heartbeat limit.
theorem lemma_good (S : Finset Congruence) (h_cd : IsCD S) :
    density_val S = density_formula S := by
      -- Let $D = \text{lcm}_{c \in S} c.d$.
      set D := S.lcm (fun c => c.d) with hD_def;
      -- By the inclusion-exclusion principle, the number of covered integers in the range $[0, D)$ is given by the sum over all non-empty subsets $I$ of $S$ of $(-1)^{|I|+1}$ times the number of integers in the intersection of the congruences in $I$.
      have h_inclusion_exclusion : (count_covered S D : ℚ) = ∑ I ∈ S.powerset.filter (fun I => I.Nonempty), (-1 : ℚ) ^ (I.card + 1) * (intersection_count I D : ℚ) := by
        have h_inclusion_exclusion : ∀ (x : ℕ), x < D → (∑ I ∈ S.powerset.filter (fun I => I.Nonempty), (-1 : ℚ) ^ (I.card + 1) * (if ∀ c ∈ I, x ≡ c.a [ZMOD c.d] then 1 else 0)) = if ∃ c ∈ S, x ≡ c.a [ZMOD c.d] then 1 else 0 := by
          intro x hx
          have h_inclusion_exclusion_step : (∑ I ∈ S.powerset, (-1 : ℚ) ^ I.card * (if ∀ c ∈ I, x ≡ c.a [ZMOD c.d] then 1 else 0)) = if ∃ c ∈ S, x ≡ c.a [ZMOD c.d] then 0 else 1 := by
            have h_inclusion_exclusion_step : (∑ I ∈ S.powerset, (-1 : ℚ) ^ I.card * (if ∀ c ∈ I, x ≡ c.a [ZMOD c.d] then 1 else 0)) = (∏ c ∈ S, (1 - if x ≡ c.a [ZMOD c.d] then 1 else 0)) := by
              simp +decide [ sub_eq_neg_add, Finset.prod_add ];
              refine Finset.sum_congr rfl fun I hI => ?_;
              split_ifs <;> simp_all +decide;
              rw [ Finset.prod_eq_zero_iff.mpr ] ; aesop;
            split_ifs <;> simp_all +decide [ Finset.prod_eq_zero_iff ];
            grind +ring;
          simp_all +decide [Finset.sum_ite, pow_succ', mul_comm, Finset.filter_ne', Finset.nonempty_iff_ne_empty];
          split_ifs at * <;> simp_all +decide [ Finset.filter_erase];
        have h_inclusion_exclusion_sum : ∑ x ∈ Finset.range D, (∑ I ∈ S.powerset.filter (fun I => I.Nonempty), (-1 : ℚ) ^ (I.card + 1) * (if ∀ c ∈ I, x ≡ c.a [ZMOD c.d] then 1 else 0)) = ∑ I ∈ S.powerset.filter (fun I => I.Nonempty), (-1 : ℚ) ^ (I.card + 1) * (intersection_count I D : ℚ) := by
          rw [ Finset.sum_comm ];
          simp +decide [ Finset.sum_ite, intersection_count ];
          simp +decide [ mul_comm, Finset.filter_image ];
          refine Finset.sum_congr rfl fun I hI => ?_;
          congr 1
          let T : Finset ℕ := {a ∈ Finset.range D | ∀ c ∈ I, (a : ℤ) ≡ c.a [ZMOD c.d]}
          letI : DecidableEq ℤ := fun a b => Classical.propDecidable (a = b)
          have hcard :
              T.card = (@Finset.image ℕ ℤ (fun a b => Classical.propDecidable (a = b))
                Nat.cast T).card := by
            exact (Finset.card_image_of_injective T (Nat.cast_injective (R := ℤ))).symm
          simpa [T] using hcard;
        rw [ ← h_inclusion_exclusion_sum, Finset.sum_congr rfl fun x hx => h_inclusion_exclusion x ( Finset.mem_range.mp hx ) ];
        simp +decide [ count_covered ];
        rw [ Finset.card_filter, Finset.card_filter ];
        refine Finset.sum_bij ( fun x hx => Int.toNat x ) ?_ ?_ ?_ ?_ <;> simp +decide;
      -- By `intersection_count_pairwise_coprime`, if $I$ is pairwise coprime, then $intersection_count I D = D / \prod_{c \in I} c.d$.
      have h_inter_count : ∀ I ∈ S.powerset.filter (fun I => I.Nonempty), (intersection_count I D : ℚ) = if pairwise_coprime I then (D : ℚ) / (∏ c ∈ I, (c.d : ℚ)) else 0 := by
        intro I hI;
        split_ifs with hI_coprime;
        · rw [ intersection_count_pairwise_coprime S I ( Finset.mem_powerset.mp ( Finset.mem_filter.mp hI |>.1 ) ) hI_coprime ];
          rw [ Nat.cast_div_charZero ];
          · norm_num +zetaDelta at *;
          · have h_prod_div : ∀ c ∈ I, c.d ∣ D := by
              exact fun c hc => Finset.dvd_lcm ( Finset.mem_powerset.mp ( Finset.mem_filter.mp hI |>.1 ) hc );
            have h_prod_div : ∀ {T : Finset Congruence}, (∀ c ∈ T, c.d ∣ D) → (∀ c1 ∈ T, ∀ c2 ∈ T, c1 ≠ c2 → Nat.Coprime c1.d c2.d) → (∏ c ∈ T, c.d) ∣ D := by
              intros T hT_div hT_coprime
              induction T using Finset.induction with
              | empty =>
                simp
              | insert c T hcT ih =>
                rw [ Finset.prod_insert hcT ]
                exact Nat.Coprime.mul_dvd_of_dvd_of_dvd ( by exact Nat.Coprime.prod_right fun x hx => hT_coprime _ ( Finset.mem_insert_self _ _ ) _ ( Finset.mem_insert_of_mem hx ) <| by aesop ) ( hT_div _ <| Finset.mem_insert_self _ _ ) ( ih ( fun x hx => hT_div _ <| Finset.mem_insert_of_mem hx ) ( fun x hx y hy hxy => hT_coprime _ ( Finset.mem_insert_of_mem hx ) _ ( Finset.mem_insert_of_mem hy ) hxy ) );
            exact h_prod_div ‹_› hI_coprime;
        · simp +zetaDelta at *;
          exact Nat.eq_zero_of_not_pos fun h => pairwise_coprime_subset hI.1 h_cd hI_coprime ( Classical.choose ( Finset.card_pos.mp h ) ) ( Classical.choose_spec ( Finset.card_pos.mp h ) |> Finset.mem_filter.mp |>.2 );
      unfold density_val density_formula; simp_all +decide ;
      split_ifs <;> simp_all +decide [ pow_succ', div_eq_mul_inv ];
      · exact absurd ‹∃ x ∈ S, x.d = 0› ( by rintro ⟨ x, hx, hx' ⟩ ; exact absurd hx' ( ne_of_gt ( x.d_pos ) ) );
      · rw [ Finset.sum_congr rfl fun x hx => by rw [ h_inter_count x ( Finset.mem_powerset.mp ( Finset.mem_filter.mp hx |>.1 ) ) ( Finset.mem_filter.mp hx |>.2 ) ] ] ; simp +decide [ Finset.sum_ite, Finset.filter_and ] ; ring_nf;
        simp +decide [ Finset.sum_mul _ _ _, mul_comm, mul_left_comm ];
        rw [ ← Finset.sum_neg_distrib ] ; refine Finset.sum_congr ?_ ?_
        · aesop
        · intro x hx; rcases k : Finset.card x with ( _ | k ) <;> simp_all +decide [pow_succ',
          ne_of_gt] ;

/-
If $n=2q^k$ with $q$ an odd prime, the density of any CD congruence set on $n$ is strictly less than 1.
-/
set_option maxHeartbeats 1000000 in
-- The specialized density estimate times out at the default heartbeat limit.
theorem case_1b_density_lt_one (q k : ℕ) (hq : q.Prime) (hq_odd : Odd q) (hk : k ≥ 1)
    (a : ℕ → ℤ) (h_cd : IsCD (congruences (2 * q ^ k) a)) :
    density_val (congruences (2 * q ^ k) a) < 1 := by
      -- Using Lemma 2.1 (Good), the density is:
      have h_density : density_val (congruences (2 * q ^ k) a) = density_formula (congruences (2 * q ^ k) a) := by
        exact lemma_good (congruences (2 * q ^ k) a) h_cd;
      -- The divisors of $2q^k$ greater than 1 are $2, q, 2q, q^2, 2q^2, \dots, q^k, 2q^k$.
      have h_divisors : (Nat.divisors (2 * q ^ k)).filter (fun d => 1 < d) = {2} ∪ Finset.image (fun j => q ^ (j + 1)) (Finset.range k) ∪ Finset.image (fun j => 2 * q ^ (j + 1)) (Finset.range k) := by
        ext d
        simp [Nat.divisors_mul, Nat.divisors_prime_pow hq];
        constructor <;> intro hd <;> simp_all +decide [ Finset.mem_mul ];
        · rcases hd with ⟨ ⟨ y, hy, a, ha, rfl ⟩, hd ⟩ ; have := Nat.le_of_dvd ( by linarith ) hy ; interval_cases y <;> simp_all +decide ;
          · rcases a with ( _ | a ) <;> aesop;
          · rcases a <;> aesop;
        · rcases hd with ( rfl | ⟨ a, ha, rfl ⟩ | ⟨ a, ha, rfl ⟩ ) <;> [ exact ⟨ ⟨ 2, by norm_num, 0, by norm_num, by norm_num ⟩, by norm_num ⟩ ; exact ⟨ ⟨ 1, by norm_num, a + 1, by linarith, by norm_num ⟩, one_lt_pow₀ hq.one_lt ( by linarith ) ⟩ ; exact ⟨ ⟨ 2, by norm_num, a + 1, by linarith, by norm_num ⟩, by nlinarith [ pow_pos hq.pos ( a + 1 ) ] ⟩ ];
      -- The pairwise coprime subsets of these divisors are:
      -- 1. Singleton sets $\{d\}$ for any divisor $d > 1$.
      -- 2. Sets $\{2, q^j\}$ for $1 \le j \le k$.
      have h_subset : ∀ I ∈ Finset.powerset (congruences (2 * q ^ k) a), I.Nonempty → pairwise_coprime I → I.card ≤ 2 := by
        intros I hI hI_nonempty hI_coprime
        have h_subset : ∀ c ∈ I, c.d = 2 ∨ ∃ j ∈ Finset.range k, c.d = q ^ (j + 1) ∨ c.d = 2 * q ^ (j + 1) := by
          intros c hc
          have h_div : c.d ∈ (Nat.divisors (2 * q ^ k)).filter (fun d => 1 < d) := by
            have := Finset.mem_powerset.mp hI hc; unfold congruences at this; aesop;
          grind;
        -- If $I$ contains more than two elements, then there must be at least three elements in $I$ that are pairwise coprime.
        by_contra h_contra
        have h_three_elements : ∃ c1 c2 c3 : Congruence, c1 ∈ I ∧ c2 ∈ I ∧ c3 ∈ I ∧ c1 ≠ c2 ∧ c1 ≠ c3 ∧ c2 ≠ c3 ∧ Nat.Coprime c1.d c2.d ∧ Nat.Coprime c1.d c3.d ∧ Nat.Coprime c2.d c3.d := by
          obtain ⟨ s, hs ⟩ := Finset.two_lt_card.mp ( not_le.mp h_contra );
          obtain ⟨ hs₁, t, ht₁, u, hu₁, hst, hsu, htu ⟩ := hs; use s, t, u; aesop;
        obtain ⟨ c1, c2, c3, hc1, hc2, hc3, hne12, hne13, hne23, hcoprime12, hcoprime13, hcoprime23 ⟩ := h_three_elements;
        rcases h_subset c1 hc1 with ha | ⟨ j1, hj1, ha | ha ⟩ <;> rcases h_subset c2 hc2 with hb | ⟨ j2, hj2, hb | hb ⟩ <;> rcases h_subset c3 hc3 with hc | ⟨ j3, hj3, hc | hc ⟩ <;> simp_all +decide only [Nat.coprime_mul_iff_left,
                                                                                                                                                                                                                                          Nat.coprime_mul_iff_right];
        all_goals simp_all +decide [Nat.Coprime, Nat.gcd_mul_right, pow_add];
      -- Let's calculate the sum of the reciprocals of the pairwise coprime subsets.
      have h_sum_reciprocals : density_formula (congruences (2 * q ^ k) a) = (∑ c ∈ congruences (2 * q ^ k) a, (1 / (c.d : ℚ))) - (∑ I ∈ Finset.powersetCard 2 (congruences (2 * q ^ k) a), if pairwise_coprime I then (1 / (∏ c ∈ I, (c.d : ℚ))) else 0) := by
        unfold density_formula;
        rw [ show ( Finset.powerset ( congruences ( 2 * q ^ k ) a ) |> Finset.filter fun I => I.Nonempty ∧ pairwise_coprime I ) = Finset.image ( fun c => { c } ) ( congruences ( 2 * q ^ k ) a ) ∪ Finset.filter ( fun I => pairwise_coprime I ∧ I.card = 2 ) ( Finset.powersetCard 2 ( congruences ( 2 * q ^ k ) a ) ) from ?_, Finset.sum_union ];
        · rw [ Finset.sum_filter ] ; norm_num [ sub_eq_add_neg ];
          rw [ ← Finset.sum_neg_distrib ] ; refine Finset.sum_congr rfl fun x hx => ?_ ; aesop;
        · norm_num [ Finset.disjoint_left ];
        · ext I; simp [Finset.mem_union, Finset.mem_image];
          constructor <;> intro hI;
          · have := h_subset I ( Finset.mem_powerset.mpr hI.1 ) hI.2.1 hI.2.2; interval_cases _ : I.card <;> simp_all +decide ;
            rw [ Finset.card_eq_one ] at * ; aesop;
          · rcases hI with ( ⟨ x, hx, rfl ⟩ | ⟨ ⟨ hI₁, hI₂ ⟩, hI₃, hI₄ ⟩ ) <;> simp_all +decide [ Finset.subset_iff ];
            · exact fun y hy z hz hyz => by aesop;
            · exact Finset.card_pos.mp ( by linarith );
      -- Let's calculate the sum of the reciprocals of the pairwise coprime subsets of size 2.
      have h_sum_reciprocals_size2 : ∑ I ∈ Finset.powersetCard 2 (congruences (2 * q ^ k) a), (if pairwise_coprime I then (1 / (∏ c ∈ I, (c.d : ℚ))) else 0) ≥ ∑ j ∈ Finset.range k, (1 / (2 * q ^ (j + 1) : ℚ)) := by
        -- Each pair $\{2, q^j\}$ for $1 \le j \le k$ is a pairwise coprime subset of the divisors of $2q^k$.
        have h_pairs : ∀ j ∈ Finset.range k, ∃ c1 c2 : Congruence, c1 ∈ congruences (2 * q ^ k) a ∧ c2 ∈ congruences (2 * q ^ k) a ∧ c1 ≠ c2 ∧ c1.d = 2 ∧ c2.d = q ^ (j + 1) ∧ pairwise_coprime {c1, c2} := by
          intro j hj
          obtain ⟨c1, hc1⟩ : ∃ c1 : Congruence, c1 ∈ congruences (2 * q ^ k) a ∧ c1.d = 2 := by
            simp_all +decide [ Finset.ext_iff ];
            unfold congruences; aesop;
          obtain ⟨c2, hc2⟩ : ∃ c2 : Congruence, c2 ∈ congruences (2 * q ^ k) a ∧ c2.d = q ^ (j + 1) := by
            unfold congruences; simp_all +decide [ Finset.ext_iff ] ;
            exact Or.inr <| Or.inl ⟨ j, hj, rfl ⟩
          use c1, c2;
          simp_all +decide [ pairwise_coprime ];
          grind;
        choose! c1 c2 hc1 hc2 hne hd1 hd2 hcoprime using h_pairs;
        refine le_trans ?_
          ( Finset.sum_le_sum_of_subset_of_nonneg
            (s := Finset.image ( fun j : Finset.range k => { c1 j j.2, c2 j j.2 } ) Finset.univ)
            ?_ ?_ );
        · rw [ Finset.sum_image ];
          · rw [ ← Finset.sum_attach ];
            refine le_of_eq ?_;
            refine Finset.sum_congr rfl ?_;
            intro j hj;
            norm_num [ hne, hd1, hd2, hcoprime ];
          · intro j hj j' hj' hset;
            apply Subtype.ext;
            have hmem : c2 j j.2 ∈ ({ c1 j' j'.2, c2 j' j'.2 } : Finset Congruence) := by
              change c2 j j.2 ∈ (fun j : Finset.range k => { c1 j j.2, c2 j j.2 }) j';
              rw [ ← hset ];
              simp;
            simp at hmem;
            rcases hmem with hmem | hmem;
            · have hd := congr_arg Congruence.d hmem;
              rw [ hd2 j j.2, hd1 j' j'.2 ] at hd;
              have hq_ne_two : q ≠ 2 := by
                rintro rfl;
                norm_num at hq_odd;
              have hq_dvd_two : q ∣ 2 := by
                rw [ ← hd ];
                exact dvd_pow_self q (by omega);
              exact (hq_ne_two ((Nat.dvd_prime Nat.prime_two).mp hq_dvd_two |>.resolve_left hq.ne_one)).elim;
            · have hd := congr_arg Congruence.d hmem;
              rw [ hd2 j j.2, hd2 j' j'.2 ] at hd;
              have h_exp : (j : ℕ) + 1 = (j' : ℕ) + 1 :=
                Nat.pow_right_injective hq.one_lt hd;
              omega;
        · simp_all +decide [ Finset.subset_iff ];
          rintro x j hj rfl; exact ⟨ fun y hy => by aesop, by rw [ Finset.card_pair ( hne j hj ) ] ⟩ ;
        · intro i hi hi'; split_ifs <;> norm_num;
          exact Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _;
      -- Let's calculate the sum of the reciprocals of the divisors of $2q^k$ greater than 1.
      have h_sum_reciprocals_divisors : ∑ c ∈ congruences (2 * q ^ k) a, (1 / (c.d : ℚ)) = (1 / 2 : ℚ) + ∑ j ∈ Finset.range k, (1 / (q ^ (j + 1) : ℚ)) + ∑ j ∈ Finset.range k, (1 / (2 * q ^ (j + 1) : ℚ)) := by
        have h_sum_reciprocals_divisors : ∑ c ∈ congruences (2 * q ^ k) a, (1 / (c.d : ℚ)) = ∑ d ∈ (Nat.divisors (2 * q ^ k)).filter (fun d => 1 < d), (1 / (d : ℚ)) := by
            refine Finset.sum_bij ( fun c hc => c.d ) ?_ ?_ ?_ ?_ <;> simp +decide [ congruences ];
            · bound;
            · aesop;
        rw [ h_sum_reciprocals_divisors, h_divisors, Finset.sum_union, Finset.sum_union ] <;> norm_num;
        · ring_nf;
          rw [ Finset.sum_image, Finset.sum_image ] <;> norm_num [ hq.ne_zero ]
          · ring_nf
          · exact fun x hx y hy hxy => by simpa [ hq.ne_zero ] using StrictMono.injective ( show StrictMono fun j => q * q ^ j * 2 from fun i j hij => mul_lt_mul_of_pos_right ( mul_lt_mul_of_pos_left ( pow_lt_pow_right₀ hq.one_lt hij ) hq.pos ) zero_lt_two ) hxy;
          · exact fun x hx y hy hxy => Nat.pow_right_injective hq.one_lt <| mul_left_cancel₀ hq.ne_zero hxy;
        · intro x hx H; have := congr_arg Even H; norm_num [ hq_odd, parity_simps ] at this;
          exact absurd this ( by simpa using hq_odd );
        · norm_num [ Finset.disjoint_right ];
          refine ⟨ fun x hx => hq.ne_one, fun a ha x hx => ?_ ⟩;
          intro H; have := congr_arg ( ·.factorization ( 2 : ℕ ) ) H; norm_num [ hq.ne_zero, hq.ne_one, Nat.factorization_pow ] at this;
          rw [ Nat.factorization_eq_zero_of_not_dvd ] at this <;> simp_all +decide [ ← even_iff_two_dvd, parity_simps ];
      -- Let's calculate the sum of the reciprocals of the divisors of $2q^k$ greater than 1, excluding the term $\frac{1}{2}$.
      have h_sum_reciprocals_divisors_excluding_half : ∑ j ∈ Finset.range k, (1 / (q ^ (j + 1) : ℚ)) < 1 / (q - 1) := by
        ring_nf;
        rw [ ← Finset.mul_sum _ _ _, geom_sum_eq ];
        · rcases q with ( _ | _ | q ) <;> norm_num at *;
          field_simp;
          rw [ div_lt_iff_of_neg ] <;> nlinarith [ pow_le_pow_right₀ ( by linarith : 1 ≤ ( q : ℚ ) + 1 + 1 ) hk ];
        · exact inv_ne_one.mpr ( mod_cast hq.ne_one );
      rcases q with ( _ | _ | _ | q ) <;> norm_num at *;
      nlinarith [ inv_mul_cancel₀ ( by linarith : ( q : ℚ ) + 1 + 1 ≠ 0 ) ]

/-
If $n$ is in Case 2, the sum of reciprocals of its divisors is less than 2.
-/
theorem case_2_sum_bound (n : ℕ) (h_ni : IsNonIntersecting n) (h_n_gt_1 : n > 1)
    (h_case2 : IsCase2 n) :
    sum_divisors_reciprocal n < 2 := by
      -- By definition of Case 2, we have $p^2 \mid n$ and $k(p(n)) \le p(n) - 2$.
      obtain ⟨p, hp⟩ : ∃ p, Nat.Prime p ∧ p^2 ∣ n ∧ (n / p).primeFactors.card < p ∧ p = n.minFac := by
        unfold IsCase2 at h_case2; aesop;
      -- By definition of Case 2, we have $n = p^{\alpha} m$ with $m$ having at most $p-2$ prime factors all greater than $p$.
      obtain ⟨α, m, hm⟩ : ∃ α m, n = p^α * m ∧ α ≥ 2 ∧ (m.primeFactors.card ≤ p - 2) ∧ (∀ q ∈ m.primeFactors, q > p) := by
        obtain ⟨α, m, hm⟩ : ∃ α m, n = p^α * m ∧ α ≥ 2 ∧ ¬(p ∣ m) := by
          use Nat.factorization n p;
          refine ⟨ n / p ^ n.factorization p, Eq.symm ( Nat.mul_div_cancel' ( Nat.ordProj_dvd _ _ ) ), ?_, ?_ ⟩;
          · rw [ ← Nat.factorization_le_iff_dvd ] at hp <;> aesop;
          · rw [ Nat.dvd_div_iff_mul_dvd ( Nat.ordProj_dvd _ _ ) ];
            exact Nat.pow_succ_factorization_not_dvd h_n_gt_1.ne_bot hp.1;
        refine ⟨ α, m, hm.1, hm.2.1, ?_, ?_ ⟩;
        · -- Since $p$ is the smallest prime factor of $n$, we have $n / p = p^{\alpha - 1} * m$.
          have h_div : n / p = p^(α - 1) * m := by
            exact Nat.div_eq_of_eq_mul_left hp.1.pos ( by rw [ hm.1 ] ; rw [ ← mul_right_comm, ← pow_succ, Nat.sub_add_cancel ( by linarith ) ] );
          rw [ h_div, Nat.primeFactors_mul, Nat.primeFactors_pow ] at hp <;> norm_num at *;
          · rcases p with ( _ | _ | p ) <;> simp +arith +decide [ hp.1 ] at *;
            rw [ Finset.card_insert_of_notMem ] at hp <;> norm_num at *
            · linarith
            · tauto
          · omega;
          · exact fun h => absurd h hp.1.ne_zero;
          · rintro rfl; simp_all +singlePass;
        · simp +zetaDelta at *;
          exact fun q hq hq' hm' => lt_of_le_of_ne ( hp.2.2.2.symm ▸ Nat.minFac_le_of_dvd hq.two_le ( hm.1.symm ▸ dvd_mul_of_dvd_right hq' _ ) ) fun h => hm.2.2 ( h.symm ▸ hq' );
      -- Since $m$ has at most $p-2$ prime factors all greater than $p$, we have $\prod_{q \in m.primeFactors} \frac{q}{q-1} \le \frac{p + (p-2) + 1}{p + 1} = \frac{2p-1}{p+1}$.
      have h_prod_bound : ∏ q ∈ m.primeFactors, ((q : ℚ) / (q - 1)) ≤ (2 * p - 1 : ℚ) / (p + 1) := by
        have h_prod_bound : ∏ q ∈ m.primeFactors, ((q : ℚ) / (q - 1)) ≤ (p + (m.primeFactors.card) + 1 : ℚ) / (p + 1) := by
          by_cases hp_ge_3 : p ≥ 3;
          · convert prod_prime_factors_geometric_bound_v2 p m m.primeFactors.card hp_ge_3 hp.1 rfl hm.2.2.2 using 1;
          · interval_cases p <;> norm_num at *;
            rcases hm.2.2.1 with ( rfl | rfl ) <;> norm_num at *;
        refine le_trans h_prod_bound ?_;
        gcongr ; nlinarith only [ show ( m.primeFactors.card : ℚ ) ≤ p - 2 by exact le_tsub_of_add_le_left <| mod_cast by linarith [ Nat.sub_add_cancel hp.1.two_le ], show ( p : ℚ ) ≥ 2 by exact mod_cast hp.1.two_le ] ;
      -- Therefore, $\prod_{r|n} \frac{r}{r-1} \le \frac{p}{p-1} \cdot \frac{2p-1}{p+1}$.
      have h_prod_bound_total : ∏ q ∈ n.primeFactors, ((q : ℚ) / (q - 1)) ≤ (p : ℚ) / (p - 1) * (2 * p - 1 : ℚ) / (p + 1) := by
        have h_prod_bound_total : ∏ q ∈ n.primeFactors, ((q : ℚ) / (q - 1)) = (∏ q ∈ ({p} : Finset ℕ), ((q : ℚ) / (q - 1))) * (∏ q ∈ m.primeFactors, ((q : ℚ) / (q - 1))) := by
          rw [ ← Finset.prod_union ];
          · rw [ hm.1, Nat.primeFactors_mul ] <;> norm_num [ hp.1.ne_zero, hp.1.ne_one, Nat.primeFactors_pow ];
            · rw [ Nat.primeFactors_pow ] <;> norm_num [ hp.1 ];
              grind;
            · rintro rfl; simp_all +singlePass;
          · exact Finset.disjoint_singleton_left.mpr fun h => by linarith [ hm.2.2.2 p h ] ;
        simpa only [ h_prod_bound_total, Finset.prod_singleton, mul_div_assoc ] using mul_le_mul_of_nonneg_left h_prod_bound ( div_nonneg ( Nat.cast_nonneg _ ) ( sub_nonneg.mpr ( Nat.one_le_cast.mpr hp.1.pos ) ) );
      refine lt_of_lt_of_le ( sum_divisors_reciprocal_lt_prod_geometric n h_n_gt_1 ) ( h_prod_bound_total.trans ?_ );
      rw [ div_mul_eq_mul_div, div_div, div_le_iff₀ ] <;> nlinarith only [ show ( p : ℚ ) ≥ 2 by exact_mod_cast hp.1.two_le ]

/-
The sum of reciprocals of moduli in a congruence set for $n$ is the sum of reciprocals of divisors of $n$ greater than 1.
-/
theorem sum_reciprocals_eq_sum_divisors_gt_1 (n : ℕ) (a : ℕ → ℤ) :
    sum_reciprocals (congruences n a) = sum_divisors_gt_1_reciprocal n := by
      unfold sum_reciprocals sum_divisors_gt_1_reciprocal congruences;
      refine Finset.sum_bij ( fun x hx => x.d ) ?_ ?_ ?_ ?_ <;> aesop

/-
The density value of a covering set is 1.
-/
theorem density_val_eq_one_of_covering (S : Finset Congruence) (h_cov : IsCovering S) :
    density_val S = 1 := by
      -- By definition of density_val, we have density_val S = (count_covered S D : ℚ) / D.
      rw [density_val];
      split_ifs with hD
      · simp_all +decide [ Finset.lcm_eq_zero_iff ]
        obtain ⟨ x, hx, hx' ⟩ := ‹_›; have := x.d_pos; aesop;
      · simp_all +decide [ Finset.lcm_eq_zero_iff ]
        exact density_of_covering S _ (Nat.pos_of_ne_zero (by
          intro hzero
          rw [Finset.lcm_eq_zero_iff] at hzero
          obtain ⟨x, hx, hxd⟩ := hzero
          exact hD x hx hxd)) h_cov

/-
If $n$ is a CD covering number, then $n > 1$.
-/
theorem n_gt_1_of_cd_covering (n : ℕ) (h : IsCDCovering n) : n > 1 := by
  rcases n with ( _ | _ | n ) <;> simp_all +decide;
  · obtain ⟨ a, ha₁, ha₂ ⟩ := h;
    unfold congruences at ha₂; simp_all +decide [ IsCovering ] ;
  · obtain ⟨ a, ha ⟩ := h;
    have := ha.2 0; simp_all +decide [ congruences ] ;

/-
If $n$ is a CD covering number, then it is non-intersecting.
-/
theorem is_non_intersecting_of_cd_covering (n : ℕ) (h : IsCDCovering n) : IsNonIntersecting n := by
  exact ⟨ h.choose, h.choose_spec.1 ⟩

/-
There are no CD covering numbers.
-/
theorem T1 : ¬ ∃ n, IsCDCovering n := by
  rintro ⟨ n, hn ⟩ ;
  have h_n_gt_1 : n > 1 := n_gt_1_of_cd_covering n hn; have := is_non_intersecting_of_cd_covering n hn; ( obtain ⟨ a, ha ⟩ := hn; obtain ⟨ ha1, ha2 ⟩ := ha; rcases non_intersecting_cases n this ( by linarith ) with ( h|h ) <;> simp_all +decide [ IsCase1, IsCase2 ] ; );
  · -- If $n$ is in Case 1, then by `case_1a_sum_bound` or `case_1b_density_lt_one`, we have a contradiction.
    by_cases h_even : Even n;
    · -- If $n$ is even and in Case 1, then by `case_1b_structure`, $n=2$ or $n=2q^k$ for some odd prime $q$.
      obtain ⟨q, k, hq_prime, hq_odd, hk, hn_eq⟩ : ∃ q k : ℕ, q.Prime ∧ q > 2 ∧ k ≥ 1 ∧ n = 2 * q ^ k ∨ n = 2 := by
        have := case_1b_structure n this ‹_› ⟨ by linarith, by aesop ⟩ h_even; aesop;
      · -- If $n=2q^k$, then by `case_1b_density_lt_one`, the density is strictly less than 1.
        have h_density_lt_one : density_val (congruences (2 * q ^ k) a) < 1 := by
          apply case_1b_density_lt_one q k hq_prime (by
          exact hq_prime.odd_of_ne_two <| ne_of_gt hq_odd) hk a (by
          aesop)
        generalize_proofs at *; (
        exact h_density_lt_one.ne ( by rw [ ← hn_eq ] ; exact density_val_eq_one_of_covering _ ha2 ) ;);
      · contrapose! ha2; simp_all +decide [ IsCovering ] ;
        unfold congruences; norm_num;
        use a 2 + 1; intro c x hx hx' hc; subst hc; simp_all +decide [ Int.ModEq ] ;
        have := Nat.le_of_dvd ( by decide ) hx; interval_cases x ; norm_num at *; omega;
    · -- If $n$ is odd and in Case 1, then by `case_1a_sum_bound`, we have a contradiction.
      have h_contradiction : sum_divisors_reciprocal n < 2 := by
        apply case_1a_sum_bound n h_n_gt_1 ⟨by linarith, h⟩ (by grind)
      have h_covering : sum_reciprocals (congruences n a) ≥ 1 := by
        exact sum_reciprocals_ge_one (congruences n a) ha2
      have h_final : sum_divisors_gt_1_reciprocal n ≥ 1 := by
        exact h_covering.trans ( by rw [ sum_reciprocals_eq_sum_divisors_gt_1 ] ) |> le_trans <| le_rfl;
      have h_final_contradiction : sum_divisors_reciprocal n ≥ 2 := by
        rw [ sum_divisors_gt_1_eq_total_sub_one ] at h_final <;> linarith [ show 0 < n from pos_of_gt ‹_› ] ;
      linarith [h_contradiction, h_final_contradiction];
  · -- By `case_2_sum_bound`, $\sum_{d|n} \frac{1}{d} < 2$.
    have h_sum_bound : sum_divisors_gt_1_reciprocal n < 1 := by
      -- By `case_2_sum_bound`, $\sum_{d|n} \frac{1}{d} < 2$. Therefore, $\sum_{d|n, d>1} \frac{1}{d} = \sum_{d|n} \frac{1}{d} - 1 < 1$.
      have h_sum_bound : sum_divisors_reciprocal n < 2 := by
        apply case_2_sum_bound n this (by linarith) ⟨by linarith, h.left, h.right⟩
      generalize_proofs at *; (
      rw [ sum_divisors_gt_1_eq_total_sub_one ] <;> linarith [ show n > 0 by linarith ] ;)
    generalize_proofs at *; (
    exact h_sum_bound.not_ge ( by simpa [ sum_reciprocals_eq_sum_divisors_gt_1 ] using sum_reciprocals_ge_one _ ha2 ) ;)

/-
Statement taken from the Formal Conjectures project.
-/
theorem erdos_204 : ¬ ∃ (n : ℕ) (a : ℕ → ℤ),
    let D := {d : ℕ | d ∣ n ∧ d > 1}
    (∀ x : ℤ, ∃ d ∈ D, x ≡ a d [ZMOD d]) ∧
    (∀ d ∈ D, ∀ d' ∈ D, d ≠ d' → (∃ x : ℤ, x ≡ a d [ZMOD d] → x ≡ a d' [ZMOD d']) →
      Nat.gcd d d' = 1) := by
  rintro ⟨ n, a, ha₁, ha₂ ⟩;
  convert T1 using 1;
  constructor <;> intro h <;> simp_all +decide [ IsCDCovering ];
  refine h n a ?_ ?_ <;> simp_all +decide [ IsCD, IsCovering ];
  · unfold congruences; simp +decide [*] ;
    rintro c1 x hx hn hx' rfl c2 y hy hn hy' rfl hne h; specialize ha₂ x hx hx' y hy hy'; aesop;
  · intro x; obtain ⟨ d, hd₁, hd₂ ⟩ := ha₁ x; use ⟨ a d, d, by linarith ⟩ ; simp +decide [ hd₁, hd₂, congruences ] ;
    rintro rfl; simp_all +decide ;
    specialize ha₂ 2 ( by decide ) 4 ( by decide ) ; norm_num at ha₂;
    exact ha₂ ( a 4 ) |>.2 ( by norm_num )

end

end Erdos204

#print axioms Erdos204.T1
-- 'Erdos204.T1' depends on axioms: [propext, Classical.choice, Quot.sound]

#print axioms Erdos204.erdos_204
-- 'Erdos204.erdos_204' depends on axioms: [propext, Classical.choice, Quot.sound]
