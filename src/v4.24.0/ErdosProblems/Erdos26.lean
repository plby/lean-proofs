/-

This is a Lean formalization of a solution to Erdős Problem 26.
https://www.erdosproblems.com/forum/thread/26

The original proof was found by: Imre Ruzsa


Ruzsa's counterexample was auto-formalized by Aristotle (from
Harmonic).  The final theorem statement was available at the Formal
Conjectures project (organized by Google DeepMind).


The proof is verified by Lean.  The following version numbers were
used:

Lean Toolchain version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7 (v4.24.0)

-/


/-
We define the Ruzsa sequence $n_\ell$ using the Chinese Remainder Theorem to satisfy $n_\ell \equiv -(j-1) \pmod{p_j}$ for $1 \le j \le \ell$. We then define the set $A = \{n_\ell \mid \ell \ge 1\}$. We prove that for any $k \ge 1$, the set of multiples of $A+k$, denoted $\mathcal{M}(A, k)$, does not have density 1. Specifically, we construct an arithmetic progression $S_k$ which is disjoint from $\mathcal{M}(A, k)$ and has positive natural density $1/m_k$. This implies that the lower density of the complement $\mathbb{N} \setminus \mathcal{M}(A, k)$ is at least $1/m_k > 0$. This provides a counterexample to the conjecture that for any infinite set $A$, there exists $k$ such that almost all integers have a divisor of the form $a+k$ with $a \in A$.
-/

import Mathlib


open scoped Classical

set_option maxHeartbeats 0

variable {β : Type*} [Preorder β]

variable (S : Set β) (a b : β)

abbrev Set.interIio (S : Set β) (b : β) : Set β :=
  S ∩ Set.Iio b

noncomputable abbrev partialDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) (b : β) : ℝ :=
  (Set.interIio (S ∩ A) b).ncard / (Set.interIio A b).ncard

open scoped Topology

open Filter

def HasDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (α : ℝ) (A : Set β := Set.univ) : Prop :=
  Filter.Tendsto (fun (b : β) => partialDensity S A b) Filter.atTop (𝓝 α)

/--
Given a set `S` in an order `β`, where all intervals bounded above are finite, we define the upper
density of `S` (relative to a set `A`) to be the limsup of the partial densities of `S`
(relative to `A`) for `b → ∞`.
-/
noncomputable def upperDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) : ℝ :=
  atTop.limsup fun (b : β) ↦ partialDensity S A b

/--
Given a set `S` in an order `β`, where all intervals bounded above are finite, we define the lower
density of `S` (relative to a set `A`) to be the liminf of the partial densities of `S`
(relative to `A`) for `b → ∞`.
-/
noncomputable def lowerDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) : ℝ :=
  atTop.liminf fun (b : β) ↦ partialDensity S A b

noncomputable def myNaturalDensity (S : Set ℕ) : ℝ :=
  if upperDensity S = lowerDensity S then upperDensity S else 0

/-
Definition of the set of multiples of a shifted set A by k, and the property that almost all integers have a divisor of the form a+k with a in A.
-/
def multiplesOfShiftedSet (A : Set ℕ) (k : ℕ) : Set ℕ :=
  {n : ℕ | ∃ a ∈ A, (a + k) ∣ n}

/-
The number of integers $n \in \{1, \dots, N\}$ such that $n \equiv r \pmod m$ differs from $N/m$ by at most 1.
-/
lemma count_congruent_bound (N m : ℕ) (r : ℤ) (hm : m ≥ 1) :
    abs ((((Finset.Icc 1 N).filter (fun n => n ≡ r [ZMOD m])).card : ℝ) - (N : ℝ) / m) ≤ 1 := by
  -- Apply the Int.Ioc_filter_modEq_card theorem to get the cardinality equality.
  have h_card_eq' : (((Finset.filter (fun x => x ≡ r [ZMOD m]) (Finset.Ioc 0 N)).card : ℤ)) = Int.floor ((N - r) / (m : ℚ)) - Int.floor ((-r) / (m : ℚ)) := by
    convert Int.Ioc_filter_modEq_card ( a := 0 ) ( b := N ) ( v := r ) ( r := m ) using 1 ; norm_num [ Int.floor_div_natCast ];
    norm_num [ hm.trans_lt' ];
    rw [ max_eq_left ] ; norm_num [ Int.floor_neg ];
    exact Int.ediv_le_ediv ( by positivity ) ( by linarith );
  -- Let's simplify the expression using the fact that multiplication by a constant $k$ and taking the floor commute.
  have h_simplify : abs ((Int.floor ((N - r) / (m : ℚ)) - Int.floor ((-r) / (m : ℚ))) - (N : ℝ) / m) ≤ 1 := by
    rw [ abs_le ];
    ring_nf;
    constructor <;> push_cast [ ← @Rat.floor_cast ℝ ] <;> linarith [ Int.floor_le ( ( N : ℝ ) * ( m : ℝ ) ⁻¹ - ( r : ℝ ) * ( m : ℝ ) ⁻¹ ), Int.lt_floor_add_one ( ( N : ℝ ) * ( m : ℝ ) ⁻¹ - ( r : ℝ ) * ( m : ℝ ) ⁻¹ ), Int.floor_le ( - ( ( r : ℝ ) * ( m : ℝ ) ⁻¹ ) ), Int.lt_floor_add_one ( - ( ( r : ℝ ) * ( m : ℝ ) ⁻¹ ) ) ];
  convert h_simplify using 2;
  convert congr_arg ( fun x : ℤ => ( x : ℝ ) - ( N : ℝ ) / ( m : ℝ ) ) h_card_eq' using 1;
  · norm_cast;
    congr! 2;
    congr! 1;
    ext ( _ | n ) <;> aesop;
  · norm_num

/-
If a sequence f(n) is approximately linear with slope c (bounded error), then f(n)/n converges to c.
-/
lemma limit_of_quasi_linear (f : ℕ → ℝ) (c : ℝ) (C : ℝ) (h : ∀ n, abs (f n - c * n) ≤ C) :
    Filter.Tendsto (fun n => f n / n) Filter.atTop (𝓝 c) := by
      -- We can rewrite the limit expression using the fact that division is the same as multiplication by a reciprocal.
      suffices h_limit : Filter.Tendsto (fun n : ℕ => (f n - c * (n : ℝ)) / (n : ℝ)) Filter.atTop (nhds 0) by
        simpa using h_limit.add_const c |> Filter.Tendsto.congr' ( by filter_upwards [ Filter.eventually_ne_atTop 0 ] with n hn; simp +decide [ hn, sub_div ] );
      exact squeeze_zero_norm ( fun n => by simpa [ abs_div ] using div_le_div_of_nonneg_right ( h n ) ( Nat.cast_nonneg n ) ) ( tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop )

/-
If $m\ge 1$ and $r\in\mathbb{Z}$, then the set
\[
S_{m,r}:=\{n\in\mathbb{N}:\ n\equiv r \pmod m\}
\]
has natural density $d(S_{m,r})=\frac{1}{m}$.
-/
lemma arithmetic_progression_density (m : ℕ) (r : ℤ) (hm : m ≥ 1) :
    HasDensity {n : ℕ | n ≡ r [ZMOD m]} (1 / m) (@Set.univ ℕ) := by
  -- Let `f(n)` be the cardinality of `{k ∈ {1, ..., n} | k ≡ r [ZMOD m]}`.
  set f : ℕ → ℕ := fun n => (Finset.Icc 1 n).filter (fun k : ℕ => (k : ℤ) ≡ r [ZMOD m]) |>.card;
  -- By `count_congruent_bound`, we have `|f(n) - n/m| ≤ 1`.
  have h_bound : ∀ n : ℕ, abs ((f n : ℝ) - (n : ℝ) / m) ≤ 1 := by
    intro n; convert count_congruent_bound n m r hm using 1;
    convert rfl;
    refine' Finset.card_bij ( fun x hx => Int.toNat x ) _ _ _ <;> aesop;
  -- Applying `limit_of_quasi_linear` with `c = 1/m` and `C = 1`, we get that the limit of `partialDensity {n : ℕ | (n : ℤ) ≡ r [ZMOD m]} univ b` as `b → ∞` is `1/m`.
  have h_limit : Filter.Tendsto (fun b : ℕ => ((f (b - 1) + (if (0 : ℕ) ∈ {n : ℕ | (n : ℤ) ≡ r [ZMOD m]} then 1 else 0)) : ℝ) / b) Filter.atTop (𝓝 (1 / m)) := by
    -- We'll use the fact that if the denominator grows faster than the numerator, the limit will approach 0.
    have h_lim_zero : Filter.Tendsto (fun b : ℕ => ((f (b - 1) : ℝ) - (b - 1) / m) / b) Filter.atTop (𝓝 0) := by
      refine' squeeze_zero_norm' _ _;
      use fun n => 1 / ( n : ℝ );
      · filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn using by simpa [ abs_div, abs_of_nonneg ( by positivity : ( 0 : ℝ ) ≤ n ) ] using div_le_div_of_nonneg_right ( show |( f ( n - 1 ) : ℝ ) - ( n - 1 ) / m| ≤ 1 from by simpa [ hn ] using h_bound ( n - 1 ) ) ( by positivity ) ;
      · exact tendsto_one_div_atTop_nhds_zero_nat;
    convert h_lim_zero.add ( show Filter.Tendsto ( fun b : ℕ => ( ( b - 1 ) / m : ℝ ) / b + ( if 0 ∈ { n : ℕ | ( n : ℤ ) ≡ r [ZMOD m] } then 1 else 0 ) / b ) Filter.atTop ( 𝓝 ( 1 / m ) ) from ?_ ) using 2 <;> norm_num ; ring_nf;
    ring_nf;
    exact le_trans ( Filter.Tendsto.add ( Filter.Tendsto.sub ( tendsto_const_nhds.congr' ( by filter_upwards [ Filter.eventually_ne_atTop 0 ] with x hx; rw [ mul_right_comm, mul_inv_cancel₀ ( Nat.cast_ne_zero.mpr hx ), one_mul ] ) ) ( tendsto_const_nhds.mul tendsto_inverse_atTop_nhds_zero_nat ) ) ( tendsto_inverse_atTop_nhds_zero_nat.mul tendsto_const_nhds ) ) ( by norm_num );
  refine' h_limit.congr' _;
  filter_upwards [ Filter.eventually_gt_atTop 0 ] with b hb;
  unfold partialDensity;
  simp +decide [ Set.ncard_eq_toFinset_card' ];
  rw [ show ( Finset.Iio b : Finset ℕ ) = Finset.Icc 1 ( b - 1 ) ∪ { 0 } from ?_, Finset.filter_union, Finset.filter_singleton ] ; aesop;
  ext ( _ | i ) <;> cases b <;> aesop

/-
Given an integer $n$ that satisfies the first $l$ congruences (i.e., $p_{j-1} \mid n + j - 1$ for $1 \le j \le l$), there exists an integer $n' > n$ that satisfies the first $l+1$ congruences.
-/
def SatisfiesCongruences (n l : ℕ) : Prop :=
  ∀ j, 1 ≤ j ∧ j ≤ l → (Nat.nth Prime (j - 1)) ∣ (n + (j - 1))

lemma exists_next_congruence (l : ℕ) (n : ℕ) (h : SatisfiesCongruences n l) :
    ∃ n' > n, SatisfiesCongruences n' (l + 1) := by
      rw [ SatisfiesCongruences ] at *;
      -- By the Chinese Remainder Theorem, there exists an integer $n'$ such that $n' \equiv n \pmod{P}$ and $n' \equiv -l \pmod{p_l}$, where $P = \prod_{k=0}^{l-1} p_k$.
      obtain ⟨n', hn'⟩ : ∃ n', n' ≡ n [MOD ∏ k ∈ Finset.range l, Nat.nth Nat.Prime k] ∧ n' ≡ -l [ZMOD Nat.nth Nat.Prime l] ∧ n' > n := by
        -- By the Chinese Remainder Theorem, there exists an integer $x$ such that $x \equiv n \pmod{P}$ and $x \equiv -l \pmod{p_l}$.
        obtain ⟨x, hx⟩ : ∃ x, x ≡ n [MOD ∏ k ∈ Finset.range l, Nat.nth Nat.Prime k] ∧ x ≡ -l [ZMOD Nat.nth Nat.Prime l] := by
          have h_crt : Nat.gcd (∏ k ∈ Finset.range l, Nat.nth Nat.Prime k) (Nat.nth Nat.Prime l) = 1 := by
            refine' Nat.Coprime.prod_left fun i hi => _;
            have h_distinct : Nat.nth Nat.Prime i ≠ Nat.nth Nat.Prime l := by
              exact fun h => by have := Nat.nth_injective ( Nat.infinite_setOf_prime ) h; linarith [ Finset.mem_range.mp hi ] ;
            simpa [ h_distinct ] using Nat.coprime_primes ( Nat.prime_nth_prime i ) ( Nat.prime_nth_prime l );
          have := Nat.chineseRemainder h_crt;
          obtain ⟨ x, hx₁, hx₂ ⟩ := this n ( Int.toNat ( -l % ( Nat.nth Nat.Prime l ) ) ) ; use x; simp_all +decide [ ← Int.natCast_modEq_iff ] ;
          simp_all +decide [ Int.ModEq, Int.emod_nonneg _ ( Nat.cast_ne_zero.mpr <| Nat.Prime.ne_zero <| Nat.prime_nth_prime l ) ];
        refine' ⟨ x + ( ∏ k ∈ Finset.range l, Nat.nth Nat.Prime k ) * ( Nat.nth Nat.Prime l ) * ( n + 1 ), _, _, _ ⟩ <;> simp_all +decide [ ← ZMod.intCast_eq_intCast_iff ];
        · simp_all +decide [ ← ZMod.natCast_eq_natCast_iff ];
        · nlinarith [ show 0 < ( ∏ k ∈ Finset.range l, Nat.nth Nat.Prime k ) * Nat.nth Nat.Prime l by exact mul_pos ( Finset.prod_pos fun _ _ => Nat.Prime.pos ( by aesop ) ) ( Nat.Prime.pos ( by aesop ) ) ];
      refine' ⟨ n', hn'.2.2, _ ⟩;
      intro j hj; rcases hj with ⟨ hj₁, hj₂ ⟩ ; rcases hj₂.eq_or_lt with rfl|hj₂' <;> simp_all +decide [ Nat.ModEq ] ;
      · rw [ ← Int.natCast_dvd_natCast ] ; simp_all +decide [ Int.ModEq, Int.emod_eq_emod_iff_emod_sub_eq_zero ] ;
        convert hn'.2.1;
        exact funext fun x => by simp +decide [ ← Nat.prime_iff ] ;
      · -- Since $n' \equiv n \pmod{P}$, we have $n' + (j - 1) \equiv n + (j - 1) \pmod{P}$.
        have h_cong : n' + (j - 1) ≡ n + (j - 1) [MOD ∏ k ∈ Finset.range l, Nat.nth Nat.Prime k] := by
          exact Nat.ModEq.add_right _ hn'.1;
        refine' Nat.dvd_of_mod_eq_zero ( h_cong.of_dvd _ ▸ Nat.mod_eq_zero_of_dvd ( h j hj₁ ( Nat.le_of_lt_succ hj₂' ) ) );
        convert Finset.dvd_prod_of_mem _ ( Finset.mem_range.mpr ( show j - 1 < l from by omega ) ) using 1;
        congr! 2;
        ext; simp +decide [ ← Nat.prime_iff ] ;

/-
Let $p_1<p_2<\cdots$ be the primes. For each $\ell\ge 1$ there exists an integer $n_\ell$ such that
\[
n_\ell \equiv -(j-1)\pmod{p_j}\qquad\text{for all }1\le j\le \ell.
\]
Moreover, one may choose a strictly increasing sequence $n_1<n_2<\cdots$ with this property.
-/
theorem exists_congruence_construction :
    ∃ n : ℕ → ℕ, StrictMono n ∧
    ∀ l ≥ 1, ∀ j, 1 ≤ j ∧ j ≤ l → (Nat.nth Prime (j - 1)) ∣ (n l + (j - 1)) := by
  -- Using `exists_next_congruence`, for every $l$ and $n$ such that `SatisfiesCongruences n l`, there exists $n' > n$ such that `SatisfiesCongruences n' (l+1)`.
  -- We define $n(l+1) = \text{next\_val } l \ n(l) \ (\text{proof for } l)$.
  have h_seq : ∃ (n : ℕ → ℕ) (h : ∀ l, SatisfiesCongruences (n l) l), StrictMono n := by
    -- We define $n(0) = 0$.
    set n₀ : ℕ := 0;
    -- We define the sequence $n$ recursively.
    have h_seq : ∃ (n : ℕ → ℕ), n 0 = n₀ ∧ ∀ l, SatisfiesCongruences (n l) l ∧ n (l + 1) > n l := by
      have h_seq : ∀ l n, SatisfiesCongruences n l → ∃ n' > n, SatisfiesCongruences n' (l + 1) := by
        exact fun l n a => exists_next_congruence l n a;
      choose! f hf₁ hf₂ using h_seq;
      use fun l => Nat.recOn l n₀ fun l ih => f l ih;
      exact ⟨ rfl, fun l => ⟨ Nat.recOn l ( by unfold SatisfiesCongruences; aesop ) fun l ih => hf₂ _ _ ih, hf₁ _ _ ( Nat.recOn l ( by unfold SatisfiesCongruences; aesop ) fun l ih => hf₂ _ _ ih ) ⟩ ⟩;
    exact ⟨ h_seq.choose, fun l => h_seq.choose_spec.2 l |>.1, strictMono_nat_of_lt_succ fun l => h_seq.choose_spec.2 l |>.2 ⟩;
  aesop

/-
Definition of the Ruzsa sequence and set, and extraction of their properties from the existence theorem.
-/
noncomputable def ruzsa_sequence : ℕ → ℕ :=
  Classical.choose exists_congruence_construction

lemma ruzsa_sequence_strict_mono : StrictMono ruzsa_sequence :=
  (Classical.choose_spec exists_congruence_construction).1

lemma ruzsa_sequence_congruence (l : ℕ) (hl : l ≥ 1) (j : ℕ) (hj : 1 ≤ j ∧ j ≤ l) :
    (Nat.nth Prime (j - 1)) ∣ (ruzsa_sequence l + (j - 1)) :=
  (Classical.choose_spec exists_congruence_construction).2 l hl j hj

/-
The modulus $m_k$ is positive for $k \ge 1$.
-/
noncomputable def ruzsa_modulus (k : ℕ) : ℕ :=
  Nat.lcm (Nat.nth Prime k) (Finset.lcm (Finset.Icc 1 k) (fun l => ruzsa_sequence l + k))

def ruzsa_progression (k : ℕ) : Set ℕ :=
  {n : ℕ | n ≡ 1 [ZMOD ruzsa_modulus k]}

lemma ruzsa_modulus_pos (k : ℕ) (hk : k ≥ 1) : ruzsa_modulus k > 0 := by
  -- The least common multiple of any set of positive integers is positive.
  apply Nat.lcm_pos;
  · -- Since primes are positive integers, the nth prime must also be positive.
    apply Nat.Prime.pos; exact (by
    convert Nat.prime_nth_prime k;
    exact funext fun n => by rw [ ← Nat.prime_iff ] ;);
  · -- Since each term in the lcm is positive, their lcm is also positive.
    apply Nat.pos_of_ne_zero
    intro h_zero
    aesop

/-
If $n \in S_k$ and $1 \le \ell \le k$, then $(n_\ell + k) \nmid n$.
-/
lemma ruzsa_progression_subset_case1 (k : ℕ) (hk : k ≥ 1) (n : ℕ) (hn : n ∈ ruzsa_progression k) (l : ℕ) (hl : 1 ≤ l ∧ l ≤ k) :
    ¬ ((ruzsa_sequence l + k) ∣ n) := by
  intro h;
  -- If $(n_\ell + k) \mid n$, then $n \equiv 0 \pmod{n_\ell + k}$. However, since $n \equiv 1 \pmod{m_k}$, we have $1 \equiv 0 \pmod{n_\ell + k}$, which is a contradiction.
  have h_cong : n ≡ 1 [MOD ruzsa_modulus k] := by
    exact Int.natCast_modEq_iff.mp hn;
  -- Since $n \equiv 1 \pmod{m_k}$ and $n \equiv 0 \pmod{n_\ell + k}$, we have $1 \equiv 0 \pmod{n_\ell + k}$, which is a contradiction.
  have h_contra : 1 ≡ 0 [MOD (ruzsa_sequence l + k)] := by
    exact h_cong.symm.of_dvd ( Nat.dvd_trans ( Finset.dvd_lcm ( Finset.mem_Icc.mpr ⟨ by linarith, by linarith ⟩ ) ) ( Nat.dvd_lcm_right _ _ ) ) |> Nat.ModEq.trans <| Nat.modEq_zero_iff_dvd.mpr h;
  rw [ Nat.modEq_zero_iff_dvd ] at h_contra ; linarith [ Nat.le_of_dvd ( by linarith ) h_contra, show ruzsa_sequence l > 0 from Nat.pos_of_ne_zero fun h => by have := ruzsa_sequence_strict_mono ( show 0 < l from hl.1 ) ; aesop ]

/-
For $l \ge k+1$, $p_{k+1}$ divides $n_l + k$.
-/
lemma ruzsa_sequence_divisible_by_pk_plus_1 (k : ℕ) (l : ℕ) (hl : l ≥ k + 1) :
    (Nat.nth Prime k) ∣ (ruzsa_sequence l + k) := by
  convert ruzsa_sequence_congruence l ( by linarith ) ( k + 1 ) ⟨ by linarith, by linarith ⟩ using 1

/-
If $n \in S_k$ and $\ell \ge k+1$, then $(n_\ell + k) \nmid n$.
-/
lemma ruzsa_progression_subset_case2 (k : ℕ) (hk : k ≥ 1) (n : ℕ) (hn : n ∈ ruzsa_progression k) (l : ℕ) (hl : l ≥ k + 1) :
    ¬ ((ruzsa_sequence l + k) ∣ n) := by
  -- If $n \in S_k$ and $\ell \ge k+1$, then $p_{k+1}$ divides $n_\ell + k$.
  have h_div : (Nat.nth Prime k) ∣ (ruzsa_sequence l + k) := by
    exact ruzsa_sequence_divisible_by_pk_plus_1 k l hl;
  -- Since $n \in S_k$, we have $n \equiv 1 \pmod{p_{k+1}}$.
  have h_cong : n ≡ 1 [MOD (Nat.nth Prime k)] := by
    have h_cong : n ≡ 1 [ZMOD (ruzsa_modulus k)] := by
      exact hn;
    simpa [ ← Int.natCast_modEq_iff ] using h_cong.of_dvd <| Int.natCast_dvd_natCast.mpr <| Nat.dvd_lcm_left _ _;
  intro h; have := Nat.dvd_trans h_div h; simp_all +decide [ Nat.ModEq, Nat.dvd_iff_mod_eq_zero ] ;
  rw [ Nat.nth_eq_sInf ] at this;
  exact absurd ( this ▸ Nat.sInf_mem ( show { x : ℕ | Prime x ∧ ∀ k_1 < k, Nat.nth Prime k_1 < x }.Nonempty from Nat.nonempty_of_pos_sInf <| this.symm ▸ by decide ) |>.1.nat_prime.ne_one ) ( by norm_num )

/-
There exists an infinite set $A$ such that for all $k \ge 1$, the set of non-multiples of the shifted set $A+k$ has positive lower density.
-/
theorem ruzsa_counterexample :
    ∃ A : Set ℕ, A.Infinite ∧
    ∀ k ≥ 1, lowerDensity ({n : ℕ | n ∉ multiplesOfShiftedSet A k}) > 0 := by
  -- Define $$S_k := \{n \in \mathbb{N}:\ n \equiv 1 \pmod{m_k}\}.$$
  let S := fun k => {n : ℕ | n ≡ 1 [ZMOD ruzsa_modulus k]};
  -- Each $S_k$ has density $1/m_k$ and is a subset of $E_k$.
  have hS_density : ∀ k ≥ 1, lowerDensity (S k) = 1 / (ruzsa_modulus k : ℝ) := by
    intro k hk
    have hS_density : HasDensity (S k) (1 / (ruzsa_modulus k : ℝ)) := by
      convert arithmetic_progression_density ( ruzsa_modulus k ) 1 _;
      exact Nat.pos_of_ne_zero ( Nat.ne_of_gt ( ruzsa_modulus_pos k hk ) );
    convert hS_density.liminf_eq;
  -- Since $S_k \subset E_k$, we have $\underline{d}(E_k) \ge \underline{d}(S_k) = 1/m_k > 0$.
  have hE_density : ∀ k ≥ 1, lowerDensity {n : ℕ | n ∉ multiplesOfShiftedSet (ruzsa_sequence '' Set.Ici 1) k} ≥ lowerDensity (S k) := by
    intro k hk
    have h_subset : ∀ n ∈ S k, n ∉ multiplesOfShiftedSet (ruzsa_sequence '' Set.Ici 1) k := by
      intro n hn h; obtain ⟨ a, ha, ha' ⟩ := h; simp_all +decide [ Nat.dvd_iff_mod_eq_zero ] ;
      -- Since $a \in A$, we have $a = ruzsa_sequence x$ for some $x \ge 1$.
      obtain ⟨x, hx1, rfl⟩ := ha;
      have h_div : (ruzsa_sequence x + k) ∣ n := by
        exact Nat.dvd_of_mod_eq_zero ha';
      have h_not_div : ¬((ruzsa_sequence x + k) ∣ n) := by
        by_cases hx : x ≤ k;
        · apply ruzsa_progression_subset_case1 k hk n hn x ⟨hx1, hx⟩;
        · exact ruzsa_progression_subset_case2 k hk n hn x ( by linarith );
      contradiction;
    apply_rules [ Filter.liminf_le_liminf ];
    · field_simp;
      refine' Filter.Eventually.of_forall fun n => _;
      gcongr;
      · exact Set.finite_iff_bddAbove.mpr ⟨ n, fun x hx => le_of_lt hx.2 ⟩;
      · intro x hx; aesop;
    · refine' ⟨ 0, Filter.eventually_atTop.mpr ⟨ 1, fun n hn => _ ⟩ ⟩;
      simp +decide [ partialDensity ];
      positivity;
    · unfold partialDensity;
      norm_num [ Filter.IsCoboundedUnder ];
      norm_num [ Filter.IsCobounded ];
      exact ⟨ 1, fun a x hx => le_trans ( hx x le_rfl ) ( div_le_one_of_le₀ ( mod_cast by
        apply_rules [ Set.ncard_le_ncard ];
        · exact fun n hn => hn.2;
        · exact Set.finite_Iio x ) ( Nat.cast_nonneg _ ) ) ⟩;
  refine' ⟨ ruzsa_sequence '' Set.Ici 1, _, _ ⟩;
  · exact Set.Infinite.image ( fun n => by have := ruzsa_sequence_strict_mono.injective; aesop ) ( Set.Ici_infinite 1 );
  · exact fun k hk => lt_of_lt_of_le ( hS_density k hk ▸ one_div_pos.mpr ( Nat.cast_pos.mpr ( ruzsa_modulus_pos k hk ) ) ) ( hE_density k hk )

/-!
# Erdős Problem 26

*References:*
- [erdosproblems.com/26](https://www.erdosproblems.com/26)
- [Te19](https://arxiv.org/pdf/1908.00488) G. Tenenbaum,
  _Some of Erdős' unconventional problems in number theory, thirty-four years later_,
  arXiv:1908.00488 [math.NT] (2019)
-/

/-- A sequence of naturals $(a_i)$ is _thick_ if their sum of reciprocals diverges:
$$
  \sum_i \frac{1}{a_i} = \infty
$$-/
def IsThick {ι : Type*} (A : ι → ℕ) : Prop := ¬Summable (fun i ↦ (1 : ℝ) / A i)

/-- The set of multiples of a sequence $(a_i)$ is $\{na_i | n \in \mathbb{N}, i\}$. -/
def MultiplesOf {ι : Type*} (A : ι → ℕ) : Set ℕ := Set.range fun (n, i) ↦ n * A i

/-- A sequence of naturals $(a_i)$ is _Behrend_ if almost all integers are a multiple of
some $a_i$. In other words, if the set of multiples has natural density $1$. -/
def IsBehrend {ι : Type*} (A : ι → ℕ) : Prop := HasDensity (MultiplesOf A) 1

/-
Given a strictly increasing sequence $f$, there exists a strictly increasing subsequence $f \circ g$ (where $g$ maps to indices $\ge 1$) such that the sum of reciprocals of the subsequence converges.
-/
lemma exists_thin_subsequence {f : ℕ → ℕ} (hf : StrictMono f) :
    ∃ g : ℕ → ℕ, StrictMono g ∧ (∀ n, g n ≥ 1) ∧ Summable (fun n => (1 : ℝ) / f (g n)) := by
  use fun n => 2 ^ n;
  -- Since $f$ is strictly monotone, we have $f(2^n) \geq 2^n$ for all $n$.
  have h_f_ge_2n : ∀ n, f (2 ^ n) ≥ 2 ^ n := by
    exact fun n => hf.id_le _;
  exact ⟨ strictMono_nat_of_lt_succ fun n => by norm_num [ pow_succ' ], fun n => one_le_pow₀ ( by norm_num ), Summable.of_nonneg_of_le ( fun n => by positivity ) ( fun n => by simpa using inv_anti₀ ( by positivity ) ( show ( f ( 2 ^ n ) : ℝ ) ≥ 2 ^ n by exact_mod_cast h_f_ge_2n n ) ) ( by simpa using summable_geometric_two ) ⟩

/-
The number of positive multiples of A less than N is bounded by N * sum(1/A_i).
-/
lemma card_pos_multiples_bound {ι : Type*} (A : ι → ℕ) (h : Summable (fun i => 1 / (A i : ℝ))) (N : ℕ) :
    ((MultiplesOf A ∩ Set.Ioo 0 N).ncard : ℝ) ≤ N * (∑' i, 1 / (A i : ℝ)) := by
      rcases N.eq_zero_or_pos with hN | hN <;> simp_all +decide [ Set.ncard_eq_toFinset_card' ];
      refine' le_trans _ ( mul_le_mul_of_nonneg_left ( Summable.sum_le_tsum _ _ h ) <| Nat.cast_nonneg _ );
      rotate_left;
      exact Finset.filter ( fun i => A i ≠ 0 ) ( h.tendsto_cofinite_zero.eventually ( gt_mem_nhds <| show ( 0 : ℝ ) < 1 / N by positivity ) |> fun h => h.toFinset );
      · exact fun _ _ => by positivity;
      · -- Let's count the number of elements in the set of multiples of $A$ that are less than $N$.
        have h_count : (Finset.filter (fun n => ∃ i, A i ≠ 0 ∧ A i ∣ n) (Finset.Ioo 0 N)).card ≤ ∑ i ∈ Finset.filter (fun i => A i ≠ 0) (h.tendsto_cofinite_zero.eventually (gt_mem_nhds <| show (0 : ℝ) < 1 / N by positivity) |> fun h => h.toFinset), (N / A i : ℕ) := by
                                                                                                                                                                                              have h_count : (Finset.filter (fun n => ∃ i, A i ≠ 0 ∧ A i ∣ n) (Finset.Ioo 0 N)).card ≤ ∑ i ∈ Finset.filter (fun i => A i ≠ 0) (h.tendsto_cofinite_zero.eventually (gt_mem_nhds <| show (0 : ℝ) < 1 / N by positivity) |> fun h => h.toFinset), (Finset.filter (fun n => A i ∣ n) (Finset.Ioo 0 N)).card := by
                                                                                                                                                                                                                                                                                                                                                                                    have h_count : Finset.filter (fun n => ∃ i, A i ≠ 0 ∧ A i ∣ n) (Finset.Ioo 0 N) ⊆ Finset.biUnion (Finset.filter (fun i => A i ≠ 0) (h.tendsto_cofinite_zero.eventually (gt_mem_nhds <| show (0 : ℝ) < 1 / N by positivity) |> fun h => h.toFinset)) (fun i => Finset.filter (fun n => A i ∣ n) (Finset.Ioo 0 N)) := by
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            simp +contextual [ Finset.subset_iff ];
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            exact fun x hx₁ hx₂ i hi₁ hi₂ => ⟨ i, ⟨ inv_anti₀ ( Nat.cast_pos.mpr ( Nat.pos_of_ne_zero hi₁ ) ) ( mod_cast Nat.le_of_dvd hx₁ hi₂ |> le_trans <| Nat.le_of_lt hx₂ ), hi₁ ⟩, hi₂ ⟩;
                                                                                                                                                                                                                                                                                                                                                                                    exact le_trans ( Finset.card_le_card h_count ) ( Finset.card_biUnion_le );
                                                                                                                                                                                              refine' le_trans h_count ( Finset.sum_le_sum fun i hi => _ );
                                                                                                                                                                                              have h_count : Finset.filter (fun n => A i ∣ n) (Finset.Ioo 0 N) ⊆ Finset.image (fun n => A i * n) (Finset.Ico 1 (N / A i + 1)) := by
                                                                                                                                                                                                simp +decide [ Finset.subset_iff ];
                                                                                                                                                                                                exact fun x hx₁ hx₂ hx₃ => ⟨ x / A i, ⟨ Nat.div_pos ( Nat.le_of_dvd hx₁ hx₃ ) ( Nat.pos_of_ne_zero ( by aesop ) ), Nat.lt_succ_of_le ( Nat.div_le_div_right hx₂.le ) ⟩, Nat.mul_div_cancel' hx₃ ⟩;
                                                                                                                                                                                              exact le_trans ( Finset.card_le_card h_count ) ( Finset.card_image_le.trans ( by simp +decide ) );
        simp +zetaDelta at *;
        refine' le_trans ( Nat.cast_le.mpr ( le_trans ( Finset.card_mono _ ) h_count ) ) _;
        · simp +contextual [ Finset.subset_iff, MultiplesOf ];
          exact fun x hx₁ hx₂ y i hi => ⟨ i, by aesop_cat, hi ▸ dvd_mul_left _ _ ⟩;
        · norm_num [ Finset.mul_sum _ _ _ ];
          exact Finset.sum_le_sum fun i hi => by rw [ ← div_eq_mul_inv ] ; rw [ le_div_iff₀ ( Nat.cast_pos.mpr <| Nat.pos_of_ne_zero <| by aesop ) ] ; norm_cast; linarith [ Nat.div_mul_le_self N ( A i ) ] ;

lemma upperDensity_le_sum_inv {ι : Type*} {A : ι → ℕ} (h : Summable (fun i => 1 / (A i : ℝ))) :
    upperDensity (MultiplesOf A) ≤ tsum (fun i => 1 / (A i : ℝ)) := by
  -- We can bound the partial densities using the results from Lemma 23.
  have h_partial_density_bound : ∀ b : ℕ, b > 0 → (partialDensity (MultiplesOf A) (Set.univ : Set ℕ) b) ≤ (1 : ℝ) / b + (∑' i, 1 / (A i : ℝ)) := by
    intro b hb_pos
    have h_card : ((MultiplesOf A ∩ Set.Iio b).ncard : ℝ) ≤ 1 + b * (∑' i, 1 / (A i : ℝ)) := by
      have h_card : (MultiplesOf A ∩ Set.Iio b).ncard ≤ 1 + (MultiplesOf A ∩ Set.Ioo 0 b).ncard := by
        have h_card : (MultiplesOf A ∩ Set.Iio b) ⊆ {0} ∪ (MultiplesOf A ∩ Set.Ioo 0 b) := by
          grind;
        exact le_trans ( Set.ncard_le_ncard h_card ) ( Set.ncard_union_le _ _ ) |> le_trans <| by simp +decide ;
      refine' le_trans ( Nat.cast_le.mpr h_card ) _;
      simpa using card_pos_multiples_bound A h b;
    rw [ div_le_iff₀ ] <;> norm_num [ Set.ncard_eq_toFinset_card' ] at * <;> nlinarith [ inv_mul_cancel₀ ( by positivity : ( b : ℝ ) ≠ 0 ) ];
  have h_lim_partial_density_bound : Filter.Tendsto (fun b : ℕ => (1 : ℝ) / b + (∑' i, 1 / (A i : ℝ))) Filter.atTop (nhds ((∑' i, 1 / (A i : ℝ)))) := by
    simpa using tendsto_inverse_atTop_nhds_zero_nat.add tendsto_const_nhds;
  refine' le_of_tendsto_of_tendsto tendsto_const_nhds h_lim_partial_density_bound _;
  filter_upwards [ Filter.eventually_gt_atTop 0 ] with b hb;
  refine' csInf_le _ _;
  · exact ⟨ 0, fun x hx => by rcases Filter.eventually_atTop.mp hx with ⟨ N, hN ⟩ ; exact le_trans ( by positivity ) ( hN _ le_rfl ) ⟩;
  · filter_upwards [ Filter.eventually_gt_atTop b ] with n hn using le_trans ( h_partial_density_bound n ( pos_of_gt hn ) ) ( add_le_add ( one_div_le_one_div_of_le ( by positivity ) ( mod_cast hn.le ) ) le_rfl )

lemma upperDensity_lt_one_of_compl_myLowerDensity_pos {S : Set ℕ} (h : lowerDensity Sᶜ > 0) :
    upperDensity S < 1 := by
  unfold lowerDensity at h;
  -- Since the lower density of $S^c$ is positive, there exists some $\epsilon > 0$ such that for all sufficiently large $b$, the density of $S^c$ up to $b$ is at least $\epsilon$.
  obtain ⟨ε, hε_pos, hε⟩ : ∃ ε > 0, ∀ᶠ b in Filter.atTop, partialDensity Sᶜ Set.univ b ≥ ε := by
    rw [ Filter.liminf_eq ] at h;
    contrapose! h;
    simp +zetaDelta at *;
    exact csSup_le ⟨ 0, ⟨ 0, fun n hn => by exact div_nonneg ( Nat.cast_nonneg _ ) ( Nat.cast_nonneg _ ) ⟩ ⟩ fun x hx => by rcases hx with ⟨ n, hn ⟩ ; exact le_of_not_gt fun hx' => by obtain ⟨ m, hm₁, hm₂ ⟩ := h ( x / 2 ) ( half_pos hx' ) n; linarith [ hn m hm₁ ] ;
  -- Since the density of $S^c$ up to $b$ is at least $\epsilon$, the density of $S$ up to $b$ is at most $1 - \epsilon$.
  have h_density_S : ∀ᶠ b in Filter.atTop, partialDensity S Set.univ b ≤ 1 - ε := by
    -- Since the density of $S^c$ up to $b$ is at least $\epsilon$, the density of $S$ up to $b$ is at most $1 - \epsilon$ by the properties of densities.
    have h_density_S : ∀ᶠ b in Filter.atTop, partialDensity S Set.univ b + partialDensity Sᶜ Set.univ b ≤ 1 := by
      refine' Filter.eventually_atTop.mpr ⟨ 1, fun b hb => _ ⟩;
      field_simp;
      rw [ div_le_iff₀ ] <;> norm_cast <;> norm_num [ Set.ncard_eq_toFinset_card' ];
      · rw [ Finset.filter_card_add_filter_neg_card_eq_card ] ; aesop;
      · linarith;
    filter_upwards [ hε, h_density_S ] with b hb₁ hb₂ using by linarith;
  refine' lt_of_le_of_lt ( csInf_le _ _ ) _;
  exact 1 - ε;
  · exact ⟨ 0, fun x hx => by rcases Filter.eventually_atTop.mp hx with ⟨ b, hb ⟩ ; exact le_trans ( by exact div_nonneg ( Nat.cast_nonneg _ ) ( Nat.cast_nonneg _ ) ) ( hb _ le_rfl ) ⟩;
  · aesop;
  · linarith

lemma isBehrend_implies_upperDensity_eq_one {ι : Type*} {A : ι → ℕ} (h : IsBehrend A) :
    upperDensity (MultiplesOf A) = 1 := by
  -- By definition of IsBehrend, we have that the upper density of the multiples of A is 1.
  have h_upper : HasDensity (MultiplesOf A) 1 := by
    -- By definition of IsBehrend, we have that the upper density of the multiples of A is 1. Therefore, we can conclude the proof.
    convert h using 1;
  convert h_upper.limsup_eq

/-
If we allow for $\sum_{a\in A} \frac{1}{a} < \infty$ then Rusza has found a counter-example.
-/
theorem erdos_26.variants.rusza : ∃ A : ℕ → ℕ,
    StrictMono A ∧ ¬IsThick A ∧ ∀ k, ¬IsBehrend (A · + k) := by
  constructor;
  swap;
  exact fun n => 2 ^ ( 2 ^ n );
  constructor;
  · exact fun m n hmn => pow_lt_pow_right₀ ( by decide ) ( pow_lt_pow_right₀ ( by decide ) hmn );
  · constructor;
    · exact fun h => h <| by simpa using summable_geometric_two.comp_injective <| Nat.pow_right_injective <| by decide;
    · intro k;
      -- By definition of $A$, we know that the set of multiples of $A$ has upper density at most $\sum_{i=0}^{\infty} \frac{1}{2^{2^i} + k}$.
      have h_upper_density : upperDensity (MultiplesOf (fun x => 2 ^ (2 ^ x) + k)) ≤ ∑' i, (1 : ℝ) / (2 ^ (2 ^ i) + k) := by
        convert upperDensity_le_sum_inv _;
        · norm_cast;
        · exact Summable.of_nonneg_of_le ( fun _ => by positivity ) ( fun n => by simpa using inv_anti₀ ( by positivity ) ( show ( 2 ^ 2 ^ n + k : ℝ ) ≥ 2 ^ 2 ^ n by linarith ) ) ( by simpa using summable_geometric_two.comp_injective ( Nat.pow_right_injective ( by decide ) ) );
      -- Since $\sum_{i=0}^{\infty} \frac{1}{2^{2^i} + k}$ converges, its upper density is less than 1.
      have h_sum_lt_one : ∑' i, (1 : ℝ) / (2 ^ (2 ^ i) + k) < 1 := by
        -- We can bound the sum $\sum_{i=0}^{\infty} \frac{1}{2^{2^i} + k}$ above by $\sum_{i=0}^{\infty} \frac{1}{2^{2^i}}$.
        have h_sum_bound : ∑' i, (1 : ℝ) / (2 ^ (2 ^ i) + k) ≤ ∑' i, (1 : ℝ) / (2 ^ (2 ^ i)) := by
          refine' Summable.tsum_le_tsum _ _ _;
          · exact fun i => by gcongr ; norm_num;
          · exact Summable.of_nonneg_of_le ( fun _ => by positivity ) ( fun i => by simpa using inv_anti₀ ( by positivity ) ( show ( 2 ^ 2 ^ i + k : ℝ ) ≥ 2 ^ 2 ^ i by linarith ) ) ( by simpa using summable_geometric_two.comp_injective ( Nat.pow_right_injective ( by decide ) ) );
          · simpa using summable_geometric_two.comp_injective ( Nat.pow_right_injective ( by decide ) );
        refine lt_of_le_of_lt h_sum_bound ?_;
        field_simp;
        have h_sum_lt_one : ∑' i, (1 : ℝ) / (2 ^ (2 ^ i)) < ∑' i, (1 : ℝ) / (2 ^ (i + 1)) := by
          fapply Summable.tsum_lt_tsum;
          use 2;
          · intro n; rcases n with ( _ | _ | n ) <;> norm_num [ Nat.pow_succ', Nat.pow_mul ] ;
            exact inv_anti₀ ( by positivity ) ( pow_le_pow_right₀ ( by norm_num ) ( by induction' n with n ih <;> norm_num [ Nat.pow_succ', Nat.pow_mul ] at * ; linarith [ Nat.one_le_pow n 2 zero_lt_two ] ) );
          · norm_num;
          · simpa using summable_geometric_two.comp_injective ( Nat.pow_right_injective ( by decide ) );
          · simpa using summable_nat_add_iff 1 |>.2 <| summable_geometric_two;
        exact h_sum_lt_one.trans_le ( by ring_nf; rw [ tsum_mul_right, tsum_geometric_of_lt_one ] <;> norm_num );
      exact fun h => h_sum_lt_one.not_le <| h_upper_density.trans' <| by linarith [ isBehrend_implies_upperDensity_eq_one h ] ;

#print axioms erdos_26.variants.rusza 
-- 'erdos_26.variants.rusza' depends on axioms: [propext, Classical.choice, Quot.sound]
