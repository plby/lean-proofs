/-

This is a Lean formalization of a solution to Erdős Problem 34.
https://www.erdosproblems.com/forum/thread/34

The original proof was found by: Hegyvári

[He86] Hegyv\'ari, N., On consecutive sums in sequences. Acta
Math. Hungar. (1986), 193--200.


Instead, a different explicit construction by Konieczny was
auto-formalized by Aristotle (from Harmonic).

[Ko15] Konieczny, J., On consecutive sums in
permutations. arXiv:1504.07156 (2015).


The proof is verified by Lean.  The following version numbers were
used:

Lean Toolchain version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7 (v4.24.0)

-/


/-
Here was the full prompt used for this proof:

Arrange the numbers from 1 to n in the order 1, n, 2, n-1, 3, n-2, ...  That is, a_i = (i+1)/2 if i is odd and a_i = n+1 - i/2 if i is even.  Consider sums of consecutive subsequences of this ordering.  Show that consecutive sums with ODD length are all distinct.  As a result, deduce that the number of distinct consecutive sums is at least n^2/4.  And finally, explicitly state the trivial corollary that there exists a permutation of 1,...,n such that the number of distinct consecutive sums is NOT o(n^2).

-/

/-
We define a specific permutation of `1, ..., n` (represented as `construction` mapping indices to values) that alternates between small and large values. We prove that for this specific arrangement, all sums of consecutive subsequences of odd length are distinct (`distinct_odd_sums`). We then deduce that the number of distinct consecutive sums is at least `n^2/4` (`num_distinct_sums_ge`). Finally, we prove the corollary that there exists a permutation of `1, ..., n` such that the number of distinct consecutive sums is at least `c * n^2` for some constant `c > 0` (`exists_perm_not_small_o`).
-/

import Mathlib

namespace Erdos34

/-
The sequence $a_i$ is defined by $a_i = (i+1)/2$ if $i$ is odd, and $a_i = n+1 - i/2$ if $i$ is even.
-/
def construction (n : ℕ) (i : ℕ) : ℕ :=
  if i % 2 = 1 then (i + 1) / 2 else n + 1 - i / 2

/-
The sum of the subsequence from index $i$ to $j$.
-/
def segment_sum (n : ℕ) (i j : ℕ) : ℕ :=
  ∑ k ∈ Finset.Icc i j, construction n k

/-
The sum of $a_{2k+1}$ and $a_{2k+2}$ is $n+1$.
-/
lemma pair_sum_odd (n k : ℕ) (hk : 2 * k + 2 ≤ n) :
    construction n (2 * k + 1) + construction n (2 * k + 2) = n + 1 := by
  unfold construction; norm_num [ Nat.add_mod, Nat.mod_two_of_bodd ] ; omega;

/-
If a segment has odd length and starts at an odd index, its sum is $\frac{j-i}{2}(n+1) + a_j$.
-/
lemma sum_odd_length_odd_start (n i j : ℕ) (hij : i ≤ j) (hjn : j ≤ n)
    (h_odd_len : (j - i + 1) % 2 = 1) (h_i_odd : i % 2 = 1) :
    segment_sum n i j = (j - i) / 2 * (n + 1) + construction n j := by
  -- Let $i = 2k+1$ and $j = 2k+1+2m$. Then $m = (j-i)/2$.
  obtain ⟨k, m, hk, hm⟩ : ∃ k m, i = 2 * k + 1 ∧ j = 2 * k + 1 + 2 * m := by
    exact ⟨ i / 2, ( j - i ) / 2, by linarith [ Nat.mod_add_div i 2 ], by omega ⟩;
  -- The segment is $a_{2k+1}, a_{2k+2}, \dots, a_{2k+2m+1}$.
  -- Group into pairs $(a_{2k+1}, a_{2k+2}), \dots, (a_{2k+2m-1}, a_{2k+2m})$ and the last term $a_{2k+2m+1}$.
  -- There are $m$ pairs.
  have h_pair_sum : ∑ x ∈ Finset.Icc (2 * k + 1) (2 * k + 1 + 2 * m), construction n x = ∑ x ∈ Finset.range m, (construction n (2 * k + 1 + 2 * x) + construction n (2 * k + 2 + 2 * x)) + construction n (2 * k + 1 + 2 * m) := by
    erw [ Finset.sum_Ico_eq_sum_range ];
    rw [ show 2 * k + 1 + 2 * m + 1 - ( 2 * k + 1 ) = 2 * m + 1 by rw [ Nat.sub_eq_of_eq_add ] ; ring ] ; simp +arith +decide [ Finset.sum_add_distrib, Finset.sum_range_succ ] ;
    induction' m with m ih;
    · norm_num;
    · induction' m + 1 with m ih <;> simp +arith +decide [ Nat.mul_succ, Finset.sum_range_succ ] at * ; linarith;
  -- Each pair $(a_{2k+1+2x}, a_{2k+2+2x})$ sums to $n+1$ by `pair_sum_odd`.
  have h_pair_sum_value : ∀ x ∈ Finset.range m, construction n (2 * k + 1 + 2 * x) + construction n (2 * k + 2 + 2 * x) = n + 1 := by
    intros x hx; convert pair_sum_odd n ( k + x ) ( by linarith [ Finset.mem_range.mp hx ] ) using 1 ; ring_nf;
  simp_all +decide
  exact h_pair_sum

/-
If a segment has odd length and starts at an even index, its sum is $\frac{j-i}{2}(n+2) + a_j$.
-/
lemma sum_odd_length_even_start (n i j : ℕ) (hi : 1 ≤ i) (hij : i ≤ j) (hjn : j ≤ n)
    (h_odd_len : (j - i + 1) % 2 = 1) (h_i_even : i % 2 = 0) :
    segment_sum n i j = (j - i) / 2 * (n + 2) + construction n j := by
  -- Let $i = 2k$ and $j = 2k+2m$. Then $m = (j-i)/2$.
  obtain ⟨k, m, rfl, rfl⟩ : ∃ k m : ℕ, i = 2 * k ∧ j = 2 * k + 2 * m := by
    exact ⟨ i / 2, ( j - i ) / 2, by linarith [ Nat.mod_add_div i 2 ], by omega ⟩;
  -- By definition of $segment_sum$, we can write
  have h_segment_sum : segment_sum n (2 * k) (2 * k + 2 * m) = (∑ x ∈ Finset.range (2 * m + 1), construction n (2 * k + x)) := by
    apply Finset.sum_bij (fun x hx => x - 2 * k);
    · exact fun x hx => Finset.mem_range.mpr ( by rw [ tsub_lt_iff_left ] <;> linarith [ Finset.mem_Icc.mp hx ] );
    · intro a₁ ha₁ a₂ ha₂ h; rw [ tsub_left_inj ] at h <;> linarith [ Finset.mem_Icc.mp ha₁, Finset.mem_Icc.mp ha₂ ] ;
    · exact fun x hx => ⟨ 2 * k + x, Finset.mem_Icc.mpr ⟨ by linarith [ Finset.mem_range.mp hx ], by linarith [ Finset.mem_range.mp hx ] ⟩, by simp +decide ⟩;
    · exact fun x hx => by rw [ Nat.add_sub_of_le ( Finset.mem_Icc.mp hx |>.1 ) ] ;
  -- By definition of $construction$, we can split the sum into pairs and the last term.
  have h_split_sum : ∑ x ∈ Finset.range (2 * m + 1), construction n (2 * k + x) = ∑ x ∈ Finset.range m, (construction n (2 * k + 2 * x) + construction n (2 * k + 2 * x + 1)) + construction n (2 * k + 2 * m) := by
    induction' m with m ih;
    · norm_num;
    · induction' m + 1 with m ih <;> simp_all +arith +decide [ Nat.mul_succ, Finset.sum_range_succ ] ; linarith;
  -- By definition of $construction$, each pair $(a_{2k}, a_{2k+1})$ sums to $n+2$.
  have h_pair_sum : ∀ x ∈ Finset.range m, construction n (2 * k + 2 * x) + construction n (2 * k + 2 * x + 1) = n + 2 := by
    intros x hx; unfold construction; simp +arith +decide [ Nat.add_mod ] ;
    grind;
  simp_all +decide

set_option maxHeartbeats 0 in
/-
If two odd-length segments have the same sum, they must be the same segment.
-/
theorem distinct_odd_sums (n : ℕ) {i j k l : ℕ}
    (hi : 1 ≤ i) (hij : i ≤ j) (hjn : j ≤ n)
    (hk : 1 ≤ k) (hkl : k ≤ l) (hln : l ≤ n)
    (h_odd_1 : (j - i + 1) % 2 = 1)
    (h_odd_2 : (l - k + 1) % 2 = 1)
    (h_eq : segment_sum n i j = segment_sum n k l) :
    i = k ∧ j = l := by
  -- Let's consider the four cases based on the parity of $i$ and $k$.
  by_cases hi_odd : i % 2 = 1
  by_cases hk_odd : k % 2 = 1;
  · -- By Lemma 2, we have $(j - i) / 2 * (n + 1) + a_j = (l - k) / 2 * (n + 1) + a_l$.
    have h_eq_odd : (j - i) / 2 * (n + 1) + construction n j = (l - k) / 2 * (n + 1) + construction n l := by
      rw [ ← sum_odd_length_odd_start n i j hij hjn h_odd_1 hi_odd, ← sum_odd_length_odd_start n k l hkl hln h_odd_2 hk_odd ] ; aesop;
    -- Since $a_j = (j + 1) / 2$ and $a_l = (l + 1) / 2$, we have $(j - i) / 2 * (n + 1) + (j + 1) / 2 = (l - k) / 2 * (n + 1) + (l + 1) / 2$.
    have h_eq_odd_simplified : (j - i) / 2 = (l - k) / 2 ∧ construction n j = construction n l := by
      have h_eq_odd_simplified : construction n j < n + 1 ∧ construction n l < n + 1 := by
        exact ⟨ by unfold construction; split_ifs <;> omega, by unfold construction; split_ifs <;> omega ⟩;
      have h_eq_odd_simplified : (j - i) / 2 = (l - k) / 2 := by
        nlinarith only [ h_eq_odd, h_eq_odd_simplified ];
      aesop;
    unfold construction at h_eq_odd_simplified;
    grind;
  · -- By `sum_odd_length_odd_start`, the sums are $m_1(n+1) + a_j$ and $m_2(n+2) + a_l$.
    obtain ⟨m1, hm1⟩ : ∃ m1, j = i + 2 * m1 := by
      exact ⟨ ( j - i ) / 2, by omega ⟩
    obtain ⟨m2, hm2⟩ : ∃ m2, l = k + 2 * m2 := by
      exact ⟨ ( l - k ) / 2, by omega ⟩
    have h_sum1 : segment_sum n i j = m1 * (n + 1) + construction n j := by
      convert sum_odd_length_odd_start n i j hij hjn _ _ using 1 <;> aesop
    have h_sum2 : segment_sum n k l = m2 * (n + 2) + construction n l := by
      convert sum_odd_length_even_start n k l hk hkl hln _ _ using 1 <;> aesop;
    -- Since $j$ is odd and $l$ is even, we have $construction n j = (j + 1) / 2$ and $construction n l = n + 1 - l / 2$.
    have h_construction_j : construction n j = (j + 1) / 2 := by
      unfold construction; aesop
    have h_construction_l : construction n l = n + 1 - l / 2 := by
      unfold construction; aesop;
    -- Since $m1 \neq m2$, we have $m1 > m2$ or $m1 < m2$.
    by_cases h_cases : m1 > m2;
    · simp_all +decide [ Nat.add_div ];
      nlinarith only [ h_sum2, h_cases, Nat.sub_le ( n + 1 ) ( k / 2 + m2 ), Nat.div_mul_le_self i 2, Nat.div_mul_le_self k 2, Nat.div_add_mod i 2, Nat.div_add_mod k 2, hi_odd, hk_odd ];
    · cases lt_or_eq_of_le ( le_of_not_gt h_cases ) <;> simp_all +decide [ Nat.add_div ];
      · contrapose! h_sum2;
        exact ne_of_lt <| by nlinarith only [ Nat.div_mul_le_self i 2, Nat.div_mul_le_self k 2, Nat.sub_le ( n + 1 ) ( k / 2 + m2 ), ‹m1 < m2›, hjn, hln ] ;
      · grind +ring;
  · by_cases hk_odd : k % 2 = 1 <;> simp_all +decide
    · -- By `sum_odd_length_odd_start`, the sums are $m_1(n+2) + a_j$ and $m_2(n+1) + a_l$.
      obtain ⟨m1, hm1⟩ : ∃ m1, j = i + 2 * m1 := by
        exact ⟨ ( j - i ) / 2, by omega ⟩
      obtain ⟨m2, hm2⟩ : ∃ m2, l = k + 2 * m2 := by
        exact ⟨ ( l - k ) / 2, by omega ⟩
      have h_sum1 : segment_sum n i j = m1 * (n + 2) + construction n j := by
        convert sum_odd_length_even_start n i j hi hij hjn _ _ using 1 <;> aesop
      have h_sum2 : segment_sum n k l = m2 * (n + 1) + construction n l := by
        convert sum_odd_length_odd_start n k l hkl hln _ _ using 1 <;> aesop
      rw [h_sum1, h_sum2] at h_eq; (
      -- Since $j$ is even and $l$ is odd, we have $construction n j = n + 1 - j / 2$ and $construction n l = (l + 1) / 2$.
      have h_construction_j : construction n j = n + 1 - (i + 2 * m1) / 2 := by
        unfold construction; simp +arith +decide [ hm1, Nat.add_div ] ;
        aesop
      have h_construction_l : construction n l = (k + 2 * m2 + 1) / 2 := by
        unfold construction; simp +decide [ *, Nat.add_mod ] ;
      rw [h_construction_j, h_construction_l] at h_eq; (
      -- By simplifying, we can see that $m1 = m2$.
      have h_m_eq : m1 = m2 := by
        by_contra h_m_neq
        generalize_proofs at *; (
        cases lt_or_gt_of_ne h_m_neq <;> simp_all +decide [ Nat.add_div ];
        · nlinarith only [ Nat.div_mul_le_self i 2, Nat.div_mul_le_self k 2, Nat.div_add_mod i 2, Nat.div_add_mod k 2, hi_odd, hk_odd, h_eq, ‹m1 < m2›, Nat.sub_add_cancel ( show i / 2 + m1 ≤ n + 1 from by linarith [ Nat.div_mul_le_self i 2 ] ) ] ;
        · nlinarith only [ Nat.div_mul_le_self i 2, Nat.div_mul_le_self k 2, Nat.div_add_mod i 2, Nat.div_add_mod k 2, hi_odd, hk_odd, h_eq, hjn, hln, ‹_›, Nat.sub_add_cancel ( show i / 2 + m1 ≤ n + 1 from by linarith [ Nat.div_mul_le_self i 2 ] ) ] ;)
      subst h_m_eq; (
      grind +ring);));
    · -- By `sum_odd_length_even_start`, the sums are $m_1(n+2) + a_j$ and $m_2(n+2) + a_l$.
      obtain ⟨m1, hm1⟩ : ∃ m1, j = i + 2 * m1 := by
        exact ⟨ ( j - i ) / 2, by omega ⟩
      obtain ⟨m2, hm2⟩ : ∃ m2, l = k + 2 * m2 := by
        exact ⟨ ( l - k ) / 2, by omega ⟩
      have h_sum1 : segment_sum n i j = m1 * (n + 2) + construction n j := by
        convert sum_odd_length_even_start n i j hi hij hjn _ _ using 1 <;> aesop
      have h_sum2 : segment_sum n k l = m2 * (n + 2) + construction n l := by
        convert sum_odd_length_even_start n k l hk hkl hln _ _ using 1 <;> aesop;
      -- Since $a_j = n+1 - j/2$ and $a_l = n+1 - l/2$, we have $construction n j = n + 1 - (i + 2 * m1) / 2$ and $construction n l = n + 1 - (k + 2 * m2) / 2$.
      have h_construction_j : construction n j = n + 1 - (i + 2 * m1) / 2 := by
        unfold construction; aesop;
      have h_construction_l : construction n l = n + 1 - (k + 2 * m2) / 2 := by
        unfold construction; aesop;
      simp_all +decide [ Nat.add_div ];
      -- Since $m1 = m2$, we have $i + 2 * m1 = k + 2 * m2$.
      have h_eq_m : m1 = m2 := by
        nlinarith only [ h_sum2, Nat.sub_add_cancel ( show i / 2 + m1 ≤ n + 1 from by linarith [ Nat.div_mul_le_self i 2 ] ), Nat.sub_add_cancel ( show k / 2 + m2 ≤ n + 1 from by linarith [ Nat.div_mul_le_self k 2 ] ), Nat.div_mul_cancel ( show 2 ∣ i from Nat.dvd_of_mod_eq_zero hi_odd ), Nat.div_mul_cancel ( show 2 ∣ k from Nat.dvd_of_mod_eq_zero hk_odd ) ]
      simp_all +decide [ Nat.add_comm ];
      rw [ tsub_right_inj ] at h_sum2 <;> omega;

set_option maxHeartbeats 0 in
/-
The number of distinct consecutive sums is at least $n^2/4$.
-/
theorem num_distinct_sums_ge (n : ℕ) :
    (Finset.image (fun p : ℕ × ℕ => segment_sum n p.1 p.2)
      ((Finset.Icc 1 n).product (Finset.Icc 1 n) |>.filter (fun p => p.1 ≤ p.2))).card ≥ n^2 / 4 := by
  -- By `distinct_odd_sums`, the map `segment_sum` is injective on $S_{odd}$.
  have h_inj_odd : Finset.card (Finset.image (fun p => segment_sum n p.1 p.2) (Finset.filter (fun p => p.1 ≤ p.2 ∧ (p.2 - p.1 + 1) % 2 = 1) (Finset.product (Finset.Icc 1 n) (Finset.Icc 1 n)))) ≥ (n ^ 2) / 4 := by
    -- Let $S$ be the set of all valid intervals $[i, j]$ with $1 \le i \le j \le n$.
    set S := Finset.filter (fun p => p.1 ≤ p.2 ∧ (p.2 - p.1 + 1) % 2 = 1) (Finset.product (Finset.Icc 1 n) (Finset.Icc 1 n)) with hS_def

    -- By `distinct_odd_sums`, the map `segment_sum` is injective on $S$.
    have h_inj_odd : Finset.card (Finset.image (fun p => segment_sum n p.1 p.2) S) = Finset.card S := by
      apply Finset.card_image_of_injOn;
      intros p hp q hq h_eq;
      have := distinct_odd_sums n ( Finset.mem_Icc.mp ( Finset.mem_product.mp ( Finset.mem_filter.mp hp |>.1 ) |>.1 ) |>.1 ) ( Finset.mem_filter.mp hp |>.2.1 ) ( Finset.mem_Icc.mp ( Finset.mem_product.mp ( Finset.mem_filter.mp hp |>.1 ) |>.2 ) |>.2 ) ( Finset.mem_Icc.mp ( Finset.mem_product.mp ( Finset.mem_filter.mp hq |>.1 ) |>.1 ) |>.1 ) ( Finset.mem_filter.mp hq |>.2.1 ) ( Finset.mem_Icc.mp ( Finset.mem_product.mp ( Finset.mem_filter.mp hq |>.1 ) |>.2 ) |>.2 ) ( Finset.mem_filter.mp hp |>.2.2 ) ( Finset.mem_filter.mp hq |>.2.2 ) h_eq; aesop;
    rw [ h_inj_odd ];
    -- Let's count the number of pairs $(i, j)$ in $S$ by considering the parity of $i$ and $j$.
    have h_count : Finset.card S = Finset.sum (Finset.Icc 1 n) (fun i => Finset.card (Finset.filter (fun j => j ≥ i ∧ (j - i + 1) % 2 = 1) (Finset.Icc 1 n))) := by
      erw [ Finset.card_filter ];
      erw [ Finset.sum_product ] ; aesop;
    -- For each $i$, the number of $j$ such that $j \geq i$ and $(j - i + 1) \% 2 = 1$ is at least $\frac{n - i + 1}{2}$.
    have h_card_filter : ∀ i ∈ Finset.Icc 1 n, Finset.card (Finset.filter (fun j => j ≥ i ∧ (j - i + 1) % 2 = 1) (Finset.Icc 1 n)) ≥ (n - i + 1 + 1) / 2 := by
      intros i hi
      have h_filter : Finset.filter (fun j => j ≥ i ∧ (j - i + 1) % 2 = 1) (Finset.Icc 1 n) ⊇ Finset.image (fun k => i + 2 * k) (Finset.range ((n - i + 1 + 1) / 2)) := by
        simp +arith +decide [ Finset.subset_iff ];
        exact fun a ha => ⟨ by linarith [ Finset.mem_Icc.mp hi ], by linarith [ Nat.div_mul_le_self ( n - i ) 2, Nat.sub_add_cancel ( show i ≤ n from Finset.mem_Icc.mp hi |>.2 ) ] ⟩;
      exact le_trans ( by rw [ Finset.card_image_of_injective ] <;> aesop_cat ) ( Finset.card_mono h_filter );
    refine' le_trans _ ( h_count.symm ▸ Finset.sum_le_sum h_card_filter );
    erw [ Finset.sum_Ico_eq_sum_range ];
    rcases Nat.even_or_odd' n with ⟨ k, rfl | rfl ⟩ <;> norm_num [ Nat.add_div ];
    · rw [ show ( 2 * k ) ^ 2 / 4 = k ^ 2 by rw [ Nat.div_eq_of_eq_mul_left zero_lt_four ] ; ring ];
      rw [ show ( Finset.range ( 2 * k ) ) = Finset.image ( fun x => 2 * x ) ( Finset.range k ) ∪ Finset.image ( fun x => 2 * x + 1 ) ( Finset.range k ) from ?_, Finset.sum_union ] <;> norm_num [ Finset.sum_add_distrib, Finset.sum_image ];
      · rw [ show ( Finset.filter ( fun x => 2 ≤ ( 2 * k - ( 1 + x ) ) % 2 + 1 ) ( Finset.image ( fun x => 2 * x ) ( Finset.range k ) ) ) = Finset.image ( fun x => 2 * x ) ( Finset.range k ) from ?_, show ( Finset.filter ( fun x => 2 ≤ ( 2 * k - ( 1 + x ) + 1 ) % 2 + 1 ) ( Finset.image ( fun x => 2 * x ) ( Finset.range k ) ) ) = ∅ from ?_, show ( Finset.filter ( fun x => 2 ≤ ( 2 * k - ( 1 + x ) ) % 2 + 1 ) ( Finset.image ( fun x => 2 * x + 1 ) ( Finset.range k ) ) ) = ∅ from ?_, show ( Finset.filter ( fun x => 2 ≤ ( 2 * k - ( 1 + x ) + 1 ) % 2 + 1 ) ( Finset.image ( fun x => 2 * x + 1 ) ( Finset.range k ) ) ) = Finset.image ( fun x => 2 * x + 1 ) ( Finset.range k ) from ?_ ] <;> norm_num [ Finset.card_image_of_injective, Function.Injective ];
        · rw [ show ( Finset.range k ).sum ( fun x => ( 2 * k - ( 1 + 2 * x ) ) / 2 ) = ( Finset.range k ).sum ( fun x => k - x - 1 ) from Finset.sum_congr rfl fun x hx => ?_, show ( Finset.range k ).sum ( fun x => ( 2 * k - ( 1 + ( 2 * x + 1 ) ) ) / 2 ) = ( Finset.range k ).sum ( fun x => k - x - 1 ) from Finset.sum_congr rfl fun x hx => ?_ ];
          · exact Nat.recOn k ( by norm_num ) fun n ih => by cases n <;> simp +decide [ Finset.sum_range_succ' ] at * ; linarith;
          · omega;
          · grind;
        · intro a ha; omega;
        · intro a ha; omega;
        · intro a ha; omega;
        · intro a ha; omega;
      · norm_num [ Finset.disjoint_right ];
        intros; omega;
      · ext x
        simp [Finset.mem_range, Finset.mem_image];
        exact ⟨ fun h => by rcases Nat.even_or_odd' x with ⟨ c, rfl | rfl ⟩ <;> [ left; right ] <;> exact ⟨ c, by linarith, rfl ⟩, fun h => by rcases h with ( ⟨ c, hc, rfl ⟩ | ⟨ c, hc, rfl ⟩ ) <;> linarith ⟩;
    · rw [ show ( Finset.range ( 2 * k + 1 ) ) = Finset.image ( fun x => 2 * x ) ( Finset.range ( k + 1 ) ) ∪ Finset.image ( fun x => 2 * x + 1 ) ( Finset.range k ) from ?_, Finset.sum_union ] <;> norm_num [ Finset.sum_image, Nat.add_mod, Nat.mul_mod ];
      · norm_num [ add_comm 1, Nat.add_sub_add_left, ← Nat.div_div_eq_div_mul ];
        norm_num [ add_assoc, Nat.add_sub_add_right, Nat.mul_succ, Finset.sum_add_distrib ];
        norm_num [ ← mul_tsub, Nat.add_mod, Nat.mul_mod ];
        rw [ show ( ∑ x ∈ Finset.range ( k + 1 ), ( k - x ) ) = ( k + 1 ) * k / 2 from ?_, show ( ∑ x ∈ Finset.range k, ( 2 * k - ( 2 * x + 1 ) ) / 2 ) = k * ( k - 1 ) / 2 from ?_ ];
        · rcases k with ( _ | _ | k ) <;> simp +arith +decide [ Nat.add_mod ];
          ring_nf;
          cases Nat.mod_two_eq_zero_or_one k <;> simp +decide [ * ] <;> omega;
        · rw [ show ( ∑ x ∈ Finset.range k, ( 2 * k - ( 2 * x + 1 ) ) / 2 ) = ∑ x ∈ Finset.range k, ( k - x - 1 ) from Finset.sum_congr rfl fun x hx => by omega ];
          convert Finset.sum_range_id k using 1;
          conv_rhs => rw [ ← Finset.sum_range_reflect ] ;
          exact Finset.sum_congr rfl fun x hx => by rw [ Nat.sub_right_comm ] ;
        · convert Finset.sum_range_id ( k + 1 ) using 1;
          conv_rhs => rw [ ← Finset.sum_range_reflect ] ;
          rfl;
      · norm_num [ Finset.disjoint_right ];
        intros; omega;
      · ext x
        simp [Finset.mem_range, Finset.mem_image];
        exact ⟨ fun hx => by rcases Nat.even_or_odd' x with ⟨ c, rfl | rfl ⟩ <;> [ left; right ] <;> exact ⟨ c, by linarith, rfl ⟩, fun hx => by rcases hx with ( ⟨ c, hc, rfl ⟩ | ⟨ c, hc, rfl ⟩ ) <;> linarith ⟩;
  exact h_inj_odd.trans ( Finset.card_mono <| Finset.image_subset_image <| fun p hp => by aesop )

/-
The function `construction n` is a bijection from $\{1, \dots, n\}$ to itself.
-/
lemma construction_bij_on (n : ℕ) :
    { x | x ∈ Finset.Icc 1 n }.BijOn (construction n) { x | x ∈ Finset.Icc 1 n } := by
  -- To prove bijection, we show that construction n is both injective and surjective on the set {1, 2, ..., n}.
  have h_inj : ∀ i j : ℕ, 1 ≤ i → i ≤ n → 1 ≤ j → j ≤ n → construction n i = construction n j → i = j := by
    unfold construction;
    grind;
  -- Next, show that construction n is surjective on the set {1, 2, ..., n}.
  have h_surj : ∀ y : ℕ, 1 ≤ y → y ≤ n → ∃ x : ℕ, 1 ≤ x ∧ x ≤ n ∧ construction n x = y := by
    intro y hy₁ hy₂
    by_cases hy_even : y ≤ (n + 1) / 2;
    · use 2 * y - 1;
      exact ⟨ Nat.le_sub_one_of_lt ( by linarith ), Nat.sub_le_of_le_add ( by omega ), by unfold construction; split_ifs <;> omega ⟩;
    · use 2 * ( n + 1 - y );
      exact ⟨ by omega, by omega, by unfold construction; split_ifs <;> omega ⟩;
  simp +zetaDelta at *;
  refine' ⟨ fun x hx => _, fun x hx => _, fun x hx => _ ⟩;
  · unfold construction;
    grind;
  · exact fun y hy hxy => h_inj x y hx.1 hx.2 hy.1 hy.2 hxy;
  · grind

/-
The set of sums of consecutive subsequences of the permutation $p$, where the values are $p(k)+1$.
-/
def perm_consecutive_sums (n : ℕ) (p : Equiv.Perm (Fin n)) : Finset ℕ :=
  (Finset.univ.filter (fun x : Fin n × Fin n => x.1 ≤ x.2)).image
    (fun x => ∑ k ∈ Finset.Icc x.1 x.2, (p k + 1))

/-
There exists a permutation $p$ of $\{0, \dots, n-1\}$ such that $p(i) + 1 = a_{i+1}$ for all $i$.
-/
lemma exists_perm_eq_construction (n : ℕ) :
    ∃ p : Equiv.Perm (Fin n), ∀ i : Fin n, (p i : ℕ) + 1 = construction n (i + 1) := by
  -- Let $f : \text{Fin} n \to \text{Fin} n$ be defined by $f(i) = \text{construction}(n, i+1) - 1$.
  obtain ⟨f, hf⟩ : ∃ f : Fin n → Fin n, ∀ i, (f i : ℕ) + 1 = construction n (i + 1) := by
    have h_construction_bounds : ∀ i : Fin n, 1 ≤ construction n (i + 1) ∧ construction n (i + 1) ≤ n := by
      unfold construction;
      intro i; split_ifs <;> omega;
    exact ⟨ fun i => ⟨ construction n ( i + 1 ) - 1, by have := h_construction_bounds i; rw [ tsub_lt_iff_left ] <;> linarith ⟩, fun i => by simp +decide [ Nat.sub_add_cancel ( h_construction_bounds i |>.1 ) ] ⟩;
  -- Since $f$ is a bijection from $\text{Fin} n$ to $\text{Fin} n$, it is a permutation.
  have h_perm : Function.Bijective f := by
    -- By definition of $f$, we know that it is injective.
    have h_inj : Function.Injective f := by
      -- By definition of `construction`, we know that `construction n (i + 1)` is unique for each `i`.
      have h_unique : ∀ i j : Fin n, i ≠ j → construction n (i + 1) ≠ construction n (j + 1) := by
        have h_unique : Finset.image (fun i : Fin n => construction n (i + 1)) (Finset.univ : Finset (Fin n)) = Finset.Icc 1 n := by
          have h_construction_bij : Finset.image (fun i : ℕ => construction n (i + 1)) (Finset.range n) = Finset.Icc 1 n := by
            have h_construction_bij : Finset.image (fun i : ℕ => construction n i) (Finset.Icc 1 n) = Finset.Icc 1 n := by
              have := construction_bij_on n;
              simpa [ Finset.ext_iff, Set.ext_iff ] using this.image_eq;
            convert h_construction_bij using 1;
            ext; simp [Finset.mem_image];
            exact ⟨ fun ⟨ a, ha, ha' ⟩ => ⟨ a + 1, ⟨ by linarith, by linarith ⟩, ha' ⟩, fun ⟨ a, ⟨ ha₁, ha₂ ⟩, ha₃ ⟩ => ⟨ a - 1, by omega, by cases a <;> aesop ⟩ ⟩;
          convert h_construction_bij using 1;
          ext; simp [Finset.mem_image];
          exact ⟨ fun ⟨ a, ha ⟩ => ⟨ a, a.2, ha ⟩, fun ⟨ a, ha, ha' ⟩ => ⟨ ⟨ a, ha ⟩, ha' ⟩ ⟩;
        intro i j hij h_eq; have := Finset.card_image_iff.mp ( by rw [ h_unique ] ; simp +decide ) ; simp_all +decide ;
        exact hij ( this ( Set.mem_univ _ ) ( Set.mem_univ _ ) h_eq );
      exact fun i j hij => Classical.not_not.1 fun hi => h_unique i j hi <| by linarith [ hf i, hf j, show ( f i : ℕ ) = f j from congr_arg Fin.val hij ] ;
    exact ⟨ h_inj, Finite.injective_iff_surjective.mp h_inj ⟩;
  exact ⟨ Equiv.ofBijective f h_perm, hf ⟩

/-
If $p(i)+1 = a_{i+1}$, then the set of consecutive sums of $p$ is the same as the set of consecutive sums of the sequence $a$.
-/
lemma perm_sums_eq_construction_sums (n : ℕ) (p : Equiv.Perm (Fin n))
    (hp : ∀ i : Fin n, (p i : ℕ) + 1 = construction n (i + 1)) :
    perm_consecutive_sums n p =
    Finset.image (fun x : ℕ × ℕ => segment_sum n x.1 x.2)
      ((Finset.Icc 1 n).product (Finset.Icc 1 n) |>.filter (fun x => x.1 ≤ x.2)) := by
  ext; simp [perm_consecutive_sums];
  constructor;
  · rintro ⟨ a, b, hab, rfl ⟩ ; refine' ⟨ a + 1, b + 1, _, _ ⟩ <;> simp_all +decide [ segment_sum ] ;
    · exact ⟨ Nat.succ_le_of_lt a.2, Nat.succ_le_of_lt b.2 ⟩;
    · refine' Finset.sum_bij ( fun x hx => ⟨ x - 1, _ ⟩ ) _ _ _ _ <;> norm_num;
      any_goals intros; omega;
      exact lt_of_lt_of_le ( Nat.pred_lt ( ne_bot_of_gt ( Finset.mem_Icc.mp hx |>.1 ) ) ) ( Finset.mem_Icc.mp hx |>.2.trans ( Nat.succ_le_of_lt ( Fin.is_lt b ) ) );
      · exact fun x hx₁ hx₂ => ⟨ Nat.le_sub_one_of_lt hx₁, Nat.sub_le_of_le_add <| by linarith [ Fin.is_lt b ] ⟩;
      · exact fun i hi₁ hi₂ => ⟨ i + 1, ⟨ Nat.succ_le_succ hi₁, Nat.succ_le_succ hi₂ ⟩, by erw [ Fin.ext_iff ] ; simp +decide ⟩;
      · exact fun i hi₁ hi₂ => by rw [ Nat.sub_add_cancel ( by linarith ) ] ;
  · rintro ⟨ a, b, ⟨ ⟨ ⟨ ha₁, ha₂ ⟩, ⟨ hb₁, hb₂ ⟩ ⟩, hab ⟩, rfl ⟩;
    refine' ⟨ ⟨ a - 1, _ ⟩, ⟨ b - 1, _ ⟩, _, _ ⟩ <;> rcases a with ( _ | a ) <;> rcases b with ( _ | b ) <;> norm_num at *;
    any_goals omega;
    refine' Finset.sum_bij ( fun x hx => x + 1 ) _ _ _ _ <;> simp_all +decide [ Finset.mem_Icc ];
    · exact fun i hi₁ hi₂ => ⟨ hi₁, hi₂ ⟩;
    · exact fun i hi₁ hi₂ j hj₁ hj₂ h => Fin.ext h;
    · exact fun x hx₁ hx₂ => ⟨ ⟨ x - 1, by omega ⟩, ⟨ Nat.le_sub_one_of_lt hx₁, Nat.sub_le_of_le_add <| by omega ⟩, by cases x <;> aesop ⟩

/-
There exists a constant $c > 0$ (specifically $1/4$) such that for every $n$, there is a permutation of $\{1, \dots, n\}$ with at least $c n^2$ distinct consecutive sums.
-/
theorem exists_perm_not_small_o :
    ∃ (c : ℝ), c > 0 ∧ ∀ n, ∃ (p : Equiv.Perm (Fin n)),
      (perm_consecutive_sums n p).card ≥ c * n^2 := by
  use 1 / 16, by norm_num, ?_;
  field_simp;
  intro n
  by_cases hn : n ≤ 4;
  · interval_cases n <;> norm_cast;
  · -- By `exists_perm_eq_construction`, there exists a permutation $p$ such that $p(i)+1 = \text{construction}(n, i+1)$ for all $i$.
    obtain ⟨p, hp⟩ := exists_perm_eq_construction n;
    -- By `perm_sums_eq_construction_sums`, the set of consecutive sums of $p$ is equal to the set of consecutive sums of `construction`.
    have h_eq_sums : perm_consecutive_sums n p = Finset.image (fun x : ℕ × ℕ => segment_sum n x.1 x.2) ((Finset.Icc 1 n).product (Finset.Icc 1 n) |>.filter (fun x => x.1 ≤ x.2)) := by
      exact perm_sums_eq_construction_sums n p hp;
    -- By `num_distinct_sums_ge`, the cardinality of this image is at least $n^2/4$.
    have h_card_ge : (Finset.image (fun x : ℕ × ℕ => segment_sum n x.1 x.2) ((Finset.Icc 1 n).product (Finset.Icc 1 n) |>.filter (fun x => x.1 ≤ x.2))).card ≥ n^2 / 4 := by
      convert num_distinct_sums_ge n using 1;
    exact ⟨ p, by rw [ h_eq_sums ] ; exact_mod_cast by nlinarith [ Nat.div_add_mod ( n^2 ) 4, Nat.mod_lt ( n^2 ) zero_lt_four ] ⟩

def erdos_34 : Prop :=
  ∀ (c : ℝ), c > 0 → ∃ N, ∀ n ≥ N, ∀ (p : Equiv.Perm (Fin n)),
      (perm_consecutive_sums n p).card < c * n^2

theorem not_erdos_34 : ¬ erdos_34 := by
  intro h
  rcases exists_perm_not_small_o with ⟨c, hc_pos, hlarge⟩
  rcases h c hc_pos with ⟨N, hN⟩
  rcases hlarge N with ⟨p, hp_ge⟩
  have hp_lt : (perm_consecutive_sums N p).card < c * (N : ℝ)^2 := by
    exact hN N (le_rfl) p
  exact (not_lt_of_ge hp_ge) hp_lt

#print axioms not_erdos_34
-- 'not_erdos_34' depends on axioms: [propext, Classical.choice, Quot.sound]
