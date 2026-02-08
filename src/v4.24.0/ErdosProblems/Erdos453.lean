/-

This is a Lean formalization of a solution to Erdős Problem 453.
https://www.erdosproblems.com/forum/thread/453

The original proof was found by: Pomerance

[Po79] Pomerance, Carl, The prime number graph. Math. Comp. (1979),
399-408.


Pomerance's proof, as described on the page linked above, was
auto-formalized by Aristotle (from Harmonic).


The proof is verified by Lean.  The following version numbers were
used:

Lean Toolchain version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7 (v4.24.0)

-/


/-
We have proven that there are infinitely many $n$ such that $p_n^2 > p_{n-i}p_{n+i}$ for all $0 < i \le n$. This answers the user's question in the negative. The proof relies on the fact that the sequence $\log p_n$ is concave on the vertices of its upper convex hull, and that there are infinitely many such vertices because $\log p_n = o(n)$ and $\log p_n \to \infty$.
-/

import Mathlib

namespace Erdos453


open Asymptotics

/-
$a_n = \log p_n$. $n$ is a vertex of the upper convex hull of $\{(k, f(k))\}$ if there exists a line $y = mx+c$ passing through $(n, f(n))$ such that all points $(k, f(k))$ lie on or below this line.
-/
noncomputable def a (n : ℕ) : ℝ := Real.log (Nat.nth Nat.Prime n)

def is_vertex (f : ℕ → ℝ) (n : ℕ) : Prop :=
  ∃ m c, f n = m * n + c ∧ ∀ k, f k ≤ m * k + c

/-
If $n$ is a vertex of the upper convex hull of $\{(k, f(k))\}$, then $2f(n) \ge f(n-i) + f(n+i)$ for all $i \le n$.
-/
lemma is_vertex_implies_ge_neighbors {f : ℕ → ℝ} {n : ℕ} (h : is_vertex f n) (i : ℕ) (hi : i ≤ n) :
    2 * f n ≥ f (n - i) + f (n + i) := by
      rcases h with ⟨ m, c, hm, hc ⟩;
      have := hc ( n - i ) ; have := hc ( n + i ) ; push_cast [ Nat.cast_sub hi ] at *; linarith;

/-
For any $n$ and $0 < i \le n$, $p_n^2 \ne p_{n-i} p_{n+i}$.
-/
lemma prime_sq_ne_neighbors (n i : ℕ) (hi : 0 < i) (hin : i ≤ n) :
    (Nat.nth Nat.Prime n)^2 ≠ Nat.nth Nat.Prime (n - i) * Nat.nth Nat.Prime (n + i) := by
      -- By contradiction, assume $p_n^2 = p_{n-i} p_{n+i}$.
      by_contra h_eq
      have h_div : Nat.nth Nat.Prime (n - i) ∣ Nat.nth Nat.Prime n ^ 2 := by
        exact h_eq.symm ▸ dvd_mul_right _ _;
      have := Nat.Prime.dvd_of_dvd_pow ( Nat.prime_nth_prime ( n - i ) ) h_div; simp_all +decide [ Nat.prime_dvd_prime_iff_eq ] ;
      exact absurd this ( ne_of_lt ( Nat.nth_strictMono ( Nat.infinite_setOf_prime ) ( by omega ) ) )

/-
$p_n \le 2^{n+1}$.
-/
lemma nth_prime_le_pow_two (n : ℕ) : Nat.nth Nat.Prime n ≤ 2 ^ (n + 1) := by
  -- By induction, we know that $p_n \leq 2^{n+1}$.
  induction' n with n ih;
  · norm_num [ Nat.nth_zero ];
    exact Nat.sInf_le Nat.prime_two;
  · rw [ Nat.nth_eq_sInf ];
    -- By Bertrand's postulate, there exists a prime $p$ such that $2^{n+1} < p \leq 2^{n+2}$.
    obtain ⟨p, hp⟩ : ∃ p, Nat.Prime p ∧ 2^(n+1) < p ∧ p ≤ 2^(n+2) := by
      exact Nat.exists_prime_lt_and_le_two_mul ( 2 ^ ( n + 1 ) ) ( by norm_num ) |> fun ⟨ p, hp₁, hp₂ ⟩ => ⟨ p, hp₁, by linarith, by ring_nf at *; linarith ⟩;
    refine' le_trans ( Nat.sInf_le _ ) hp.2.2;
    exact ⟨ hp.1, fun k hk => lt_of_le_of_lt ( Nat.nth_monotone ( Nat.infinite_setOf_prime ) ( Nat.le_of_lt_succ hk ) ) ( lt_of_le_of_lt ih hp.2.1 ) ⟩

/-
$a_n \to \infty$.
-/
lemma a_tendsto_atTop : Filter.Tendsto a Filter.atTop Filter.atTop := by
  refine' Real.tendsto_log_atTop.comp _;
  refine' tendsto_natCast_atTop_atTop.comp ( Filter.tendsto_atTop_mono _ tendsto_natCast_atTop_atTop );
  intro n;
  refine' Nat.le_nth _;
  exact fun h => False.elim <| Nat.infinite_setOf_prime h

/-
If a sequence tends to 0 and has a positive value, it attains a maximum.
-/
lemma exists_max_of_tendsto_zero {g : ℕ → ℝ} (h_lim : Filter.Tendsto g Filter.atTop (nhds 0))
    (h_pos : ∃ k, g k > 0) : ∃ K, ∀ k, g k ≤ g K := by
      -- Since $g(n) \to 0$, there exists $M$ such that for all $n > M$, $g(n) < g(k_0)$ where $g(k_0) > 0$.
      obtain ⟨M, hM⟩ : ∃ M, ∀ n > M, g n < g (Classical.choose h_pos) := by
        exact Filter.eventually_atTop.mp ( h_lim.eventually ( gt_mem_nhds <| Classical.choose_spec h_pos ) ) |> fun ⟨ M, hM ⟩ ↦ ⟨ M, fun n hn ↦ hM n hn.le ⟩;
      -- The set $\{0, \dots, M\}$ is finite, so $g$ attains a maximum on it.
      obtain ⟨K, hK⟩ : ∃ K ∈ Finset.range (M + 1), ∀ k ∈ Finset.range (M + 1), g k ≤ g K := by
        exact Finset.exists_max_image _ _ ⟨ _, Finset.mem_range.mpr <| Nat.succ_pos _ ⟩;
      use if g K ≥ g (Classical.choose h_pos) then K else Classical.choose h_pos;
      intro k; split_ifs <;> [ exact if hk : k ≤ M then hK.2 k ( Finset.mem_range_succ_iff.mpr hk ) else le_of_lt ( hM k ( not_le.mp hk ) |> lt_of_lt_of_le <| by linarith ) ; exact if hk : k ≤ M then le_trans ( hK.2 k ( Finset.mem_range_succ_iff.mpr hk ) ) ( by linarith ) else le_of_lt ( hM k ( not_le.mp hk ) ) ] ;

/-
If $f(n) = o(n)$, then the slope $\frac{f(k) - f(N)}{k - N}$ tends to 0 as $k \to \infty$.
-/
noncomputable def slope_fun (f : ℕ → ℝ) (N k : ℕ) : ℝ := (f k - f N) / ((k : ℝ) - (N : ℝ))

lemma slope_tendsto_zero {f : ℕ → ℝ} {N : ℕ} (h_o : IsLittleO Filter.atTop f (fun n => (n : ℝ))) :
    Filter.Tendsto (fun k => slope_fun f N k) Filter.atTop (nhds 0) := by
      -- We can rewrite the slope function as $\frac{f(k)}{k} \cdot \frac{k}{k-N} - \frac{f(N)}{k-N}$.
      suffices h_slope_rewrite : Filter.Tendsto (fun k => (f k / (k : ℝ)) * (k / (k - N)) - (f N / (k - N))) Filter.atTop (nhds 0) by
        simp_all +decide [ slope_fun ];
        refine h_slope_rewrite.congr' ( by filter_upwards [ Filter.eventually_gt_atTop N ] with k hk using by rw [ div_mul_div_cancel₀ ( by norm_cast; linarith ) ] ; ring );
      -- Since $\frac{f(k)}{k} \to 0$ and $\frac{k}{k-N} \to 1$, their product tends to $0$.
      have h_prod : Filter.Tendsto (fun k => (f k) / (k : ℝ) * (k / (k - N))) Filter.atTop (nhds 0) := by
        -- Since $\frac{f(k)}{k} \to 0$, we have $\frac{f(k)}{k} \cdot \frac{k}{k-N} \to 0$.
        have h_frac1 : Filter.Tendsto (fun k => (f k) / (k : ℝ)) Filter.atTop (nhds 0) := by
          simpa [ Asymptotics.isLittleO_iff_tendsto ] using h_o.tendsto_div_nhds_zero;
        simpa using h_frac1.mul ( show Filter.Tendsto ( fun k : ℕ => ( k : ℝ ) / ( k - N ) ) Filter.atTop ( nhds 1 ) from by simpa using tendsto_natCast_div_add_atTop ( -N : ℝ ) );
      simpa using h_prod.sub ( tendsto_const_nhds.div_atTop ( Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop ) )

/-
If $N$ is a vertex and $K > N$ maximizes the slope from $N$, then $K$ is a vertex.
-/
lemma max_slope_is_vertex {f : ℕ → ℝ} {N K : ℕ} (hN : is_vertex f N) (hK_gt : K > N)
    (h_max : ∀ k > N, slope_fun f N k ≤ slope_fun f N K) : is_vertex f K := by
      -- By definition of $is_vertex$, there exists a line $L(x) = m(x - N) + f(N)$ such that $f(k) \le L(k)$ for all $k$.
      obtain ⟨m, c, hm⟩ : ∃ m c : ℝ, f N = m * N + c ∧ ∀ k, f k ≤ m * k + c := hN;
      -- Consider the line $L(x) = m(x - N) + f(N)$.
      use (f K - f N) / ((K : ℝ) - (N : ℝ)), f N - (f K - f N) / ((K : ℝ) - (N : ℝ)) * N;
      refine' ⟨ _, fun k => _ ⟩;
      · linarith [ div_mul_cancel₀ ( f K - f N ) ( sub_ne_zero_of_ne ( by norm_cast; linarith : ( K : ℝ ) ≠ N ) ) ];
      · by_cases hk : k > N;
        · have := h_max k hk;
          unfold slope_fun at this; rw [ div_le_iff₀ ] at this <;> nlinarith [ ( by norm_cast : ( N : ℝ ) < K ), ( by norm_cast : ( N : ℝ ) < k ) ] ;
        · have h_slope_le : (f K - f N) / ((K : ℝ) - (N : ℝ)) ≤ m := by
            have := hm.2 K; rw [ div_le_iff₀ ] <;> nlinarith [ show ( K : ℝ ) > N by norm_cast ] ;
          nlinarith [ hm.2 k, show ( k : ℝ ) ≤ N by norm_cast; linarith ]

/-
If $f(n) \to \infty$, then for any $N$, there exists $k > N$ such that $f(k) > f(N)$.
-/
lemma exists_gt_of_tendsto_atTop {f : ℕ → ℝ} (h_inf : Filter.Tendsto f Filter.atTop Filter.atTop) (N : ℕ) :
    ∃ k > N, f k > f N := by
      exact Filter.eventually_atTop.mp ( h_inf.eventually_gt_atTop ( f N ) ) |> fun ⟨ k, hk ⟩ ↦ ⟨ k + N + 1, by linarith, hk _ <| by linarith ⟩

/-
There exists $K > N$ that maximizes the slope from $N$ among all $k > N$.
-/
lemma exists_max_slope_gt_N {f : ℕ → ℝ} {N : ℕ}
    (h_o : IsLittleO Filter.atTop f (fun n => (n : ℝ)))
    (h_inf : Filter.Tendsto f Filter.atTop Filter.atTop) :
    ∃ K > N, ∀ k > N, slope_fun f N k ≤ slope_fun f N K := by
      -- By `exists_max_of_tendsto_zero`, $g$ attains a maximum at some $K$.
      obtain ⟨K, hK⟩ : ∃ K, ∀ k, slope_fun f N (k + N + 1) ≤ slope_fun f N (K + N + 1) := by
        -- By definition of $g$, we know that $g(k) = \text{slope\_fun } f N (k + N + 1)$ and $g(k) \to 0$ as $k \to \infty$.
        have h_g_tendsto_zero : Filter.Tendsto (fun k => slope_fun f N (k + N + 1)) Filter.atTop (nhds 0) := by
          have := @slope_tendsto_zero f N ; ring_nf;
          exact this h_o |> Filter.Tendsto.comp <| Filter.tendsto_atTop_mono ( fun k => by linarith ) tendsto_natCast_atTop_atTop;
        have h_g_exists_max : ∃ K, ∀ k, slope_fun f N (k + N + 1) ≤ slope_fun f N (K + N + 1) := by
          have h_g_pos : ∃ k, slope_fun f N (k + N + 1) > 0 := by
            have h_g_pos : ∃ k, f (k + N + 1) > f N := by
              exact Filter.eventually_atTop.mp ( h_inf.eventually_gt_atTop ( f N ) ) |> fun ⟨ k, hk ⟩ => ⟨ k, hk _ ( by linarith ) ⟩;
            exact h_g_pos.imp fun k hk => div_pos ( sub_pos.mpr hk ) ( by norm_num; linarith )
          exact exists_max_of_tendsto_zero h_g_tendsto_zero h_g_pos;
        exact h_g_exists_max;
      exact ⟨ K + N + 1, by linarith, fun k hk => by have := hK ( k - N - 1 ) ; rw [ show k = ( k - N - 1 ) + N + 1 by omega ] ; exact this ⟩

/-
If $f(n) = o(n)$ and $f(n) \to \infty$, then 0 is a vertex of the upper convex hull.
-/
lemma zero_is_vertex {f : ℕ → ℝ} (h_o : IsLittleO Filter.atTop f (fun n => (n : ℝ)))
    (h_inf : Filter.Tendsto f Filter.atTop Filter.atTop) : is_vertex f 0 := by
      -- By `exists_max_of_tendsto_zero`, there exists $K$ such that $s_k \le s_K$ for all $k$.
      obtain ⟨K, hK⟩ : ∃ K, ∀ k > 0, slope_fun f 0 k ≤ slope_fun f 0 K := by
        -- By `exists_max_of_tendsto_zero`, there exists $K > 0$ such that $s_k \le s_K$ for all $k > 0$.
        obtain ⟨K, hK⟩ : ∃ K > 0, ∀ k > 0, slope_fun f 0 k ≤ slope_fun f 0 K := by
          convert exists_max_slope_gt_N h_o h_inf;
        exact ⟨ K, hK.2 ⟩;
      use slope_fun f 0 K, f 0 - slope_fun f 0 K * 0;
      exact ⟨ by norm_num, fun k => if hk : k = 0 then by norm_num [ hk ] else by have := hK k ( Nat.pos_of_ne_zero hk ) ; unfold slope_fun at *; rw [ div_le_iff₀ ] at * <;> norm_num at * <;> cases lt_or_gt_of_ne hk <;> linarith ⟩

/-
If $f(n) = o(n)$ and $f(n) \to \infty$, then there are infinitely many vertices on the upper convex hull of $\{(n, f(n))\}$.
-/
lemma infinite_vertices {f : ℕ → ℝ} (h_o : IsLittleO Filter.atTop f (fun n => (n : ℝ)))
    (h_inf : Filter.Tendsto f Filter.atTop Filter.atTop) : Set.Infinite { n | is_vertex f n } := by
      -- Assume by contradiction that the set of vertices is finite.
      by_contra h_contra;
      -- Since the set of vertices is finite and nonempty (0 is a vertex by `zero_is_vertex`), it has a maximum element $N$.
      obtain ⟨N, hN⟩ : ∃ N, is_vertex f N ∧ ∀ n, is_vertex f n → n ≤ N := by
        exact ⟨ Finset.max' ( Set.Finite.toFinset ( Classical.not_not.mp h_contra ) ) ⟨ _, by simpa using zero_is_vertex h_o h_inf ⟩, by simpa using Finset.max'_mem ( Set.Finite.toFinset ( Classical.not_not.mp h_contra ) ) ⟨ _, by simpa using zero_is_vertex h_o h_inf ⟩, fun n hn => Finset.le_max' _ _ ( by simpa using hn ) ⟩;
      -- By `exists_max_slope_gt_N`, there exists $K > N$ such that for all $k > N$, the slope from $N$ to $k$ is at most the slope from $N$ to $K$.
      obtain ⟨K, hK_gt_N, hK_max⟩ : ∃ K > N, ∀ k > N, slope_fun f N k ≤ slope_fun f N K := by
        exact exists_max_slope_gt_N h_o h_inf;
      -- By `max_slope_is_vertex`, $K$ is a vertex.
      have hK_vertex : is_vertex f K := by
        apply max_slope_is_vertex hN.left hK_gt_N hK_max;
      linarith [ hN.2 K hK_vertex ]

/-
If $f(n) = o(n)$ and $f(n) \to \infty$, then there are infinitely many vertices on the upper convex hull.
-/
lemma infinite_vertices_of_little_o {f : ℕ → ℝ} (h_o : IsLittleO Filter.atTop f (fun n => (n : ℝ)))
    (h_inf : Filter.Tendsto f Filter.atTop Filter.atTop) : Set.Infinite { n | is_vertex f n } := by
      convert infinite_vertices _ _ using 1 ; aesop;
      assumption

/-
If $f(n) = o(n)$ and $f(n) \to \infty$, then there are infinitely many vertices on the upper convex hull.
-/
lemma infinite_vertices_thm {f : ℕ → ℝ} (h_o : IsLittleO Filter.atTop f (fun n => (n : ℝ)))
    (h_inf : Filter.Tendsto f Filter.atTop Filter.atTop) : Set.Infinite { n | is_vertex f n } := by
      exact infinite_vertices h_o h_inf

/-
If $f(n) = o(n)$ and $f(n) \to \infty$, then there are infinitely many vertices on the upper convex hull.
-/
lemma infinite_vertices_final {f : ℕ → ℝ} (h_o : IsLittleO Filter.atTop f (fun n => (n : ℝ)))
    (h_inf : Filter.Tendsto f Filter.atTop Filter.atTop) : Set.Infinite { n | is_vertex f n } := by
  by_contra h_finite
  let S := { n | is_vertex f n }
  have hS_finite : S.Finite := by simpa using h_finite
  have hS_nonempty : S.Nonempty := ⟨ 0, zero_is_vertex h_o h_inf ⟩
  let S_fin := hS_finite.toFinset
  have hS_fin_nonempty : S_fin.Nonempty := by
    rw [Set.Finite.toFinset_nonempty]
    exact hS_nonempty
  let N := S_fin.max' hS_fin_nonempty
  have hN_vertex : is_vertex f N := by
    have := S_fin.max'_mem hS_fin_nonempty
    simp [S_fin, S] at this
    exact this
  have hN_max : ∀ n, is_vertex f n → n ≤ N := by
    intro n hn
    have := S_fin.le_max' n (by simp [S_fin, S, hn])
    exact this
  obtain ⟨K, hK_gt, hK_max⟩ := exists_max_slope_gt_N (N := N) h_o h_inf
  have hK_vertex : is_vertex f K := max_slope_is_vertex hN_vertex hK_gt hK_max
  have hK_le_N : K ≤ N := hN_max K hK_vertex
  linarith

/-
If $f(n) = o(n)$ and $f(n) \to \infty$, then there are infinitely many vertices on the upper convex hull.
-/
lemma infinite_vertices_corrected {f : ℕ → ℝ} (h_o : IsLittleO Filter.atTop f (fun n => (n : ℝ)))
    (h_inf : Filter.Tendsto f Filter.atTop Filter.atTop) : Set.Infinite { n | is_vertex f n } := by
  by_contra h_finite
  let S := { n | is_vertex f n }
  have hS_finite : S.Finite := by simpa using h_finite
  have hS_nonempty : S.Nonempty := ⟨ 0, zero_is_vertex h_o h_inf ⟩
  let S_fin := hS_finite.toFinset
  have hS_fin_nonempty : S_fin.Nonempty := hS_finite.toFinset_nonempty.mpr hS_nonempty
  let N := S_fin.max' hS_fin_nonempty
  have hN_vertex : is_vertex f N := by
    have := S_fin.max'_mem hS_fin_nonempty
    simp [S_fin, S] at this
    exact this
  have hN_max : ∀ n, is_vertex f n → n ≤ N := by
    intro n hn
    have := S_fin.le_max' n (by simp [S_fin, S, hn])
    exact this
  obtain ⟨K, hK_gt, hK_max⟩ := exists_max_slope_gt_N (N := N) h_o h_inf
  have hK_vertex : is_vertex f K := max_slope_is_vertex hN_vertex hK_gt hK_max
  have hK_le_N : K ≤ N := hN_max K hK_vertex
  linarith

/-
If $n$ is a vertex of the upper convex hull of $a_n = \log p_n$, then $p_n^2 > p_{n-i} p_{n+i}$.
-/
lemma log_prime_vertex_implies_strict_ineq (n : ℕ) (h : is_vertex a n) :
    ∀ i, 0 < i → i ≤ n → 2 * a n > a (n - i) + a (n + i) := by
      intros i hi_pos hi_le_n
      have h_neq : a n * 2 ≠ a (n - i) + a (n + i) := by
        -- By definition of $a$, we know that $a n = \log p n$, $a (n - i) = \log p (n - i)$, and $a (n + i) = \log p (n + i)$.
        have h_log_eq : Real.log (Nat.nth Nat.Prime n ^ 2) ≠ Real.log (Nat.nth Nat.Prime (n - i) * Nat.nth Nat.Prime (n + i)) := by
          exact fun h => prime_sq_ne_neighbors n i hi_pos hi_le_n <| by rw [ ← @Nat.cast_inj ℝ ] ; push_cast; rw [ ← Real.exp_log ( pow_pos ( Nat.cast_pos.mpr <| Nat.Prime.pos <| Nat.prime_nth_prime n ) 2 ), ← Real.exp_log ( mul_pos ( Nat.cast_pos.mpr <| Nat.Prime.pos <| Nat.prime_nth_prime _ ) ( Nat.cast_pos.mpr <| Nat.Prime.pos <| Nat.prime_nth_prime _ ) ) ] ; aesop;
        convert h_log_eq using 1 <;> norm_num [ a ] ; ring;
        rw [ Real.log_mul ( Nat.cast_ne_zero.mpr <| Nat.Prime.ne_zero <| Nat.prime_nth_prime _ ) ( Nat.cast_ne_zero.mpr <| Nat.Prime.ne_zero <| Nat.prime_nth_prime _ ) ];
      exact lt_of_le_of_ne ( by linarith [ is_vertex_implies_ge_neighbors h i hi_le_n ] ) ( Ne.symm <| by simpa [ mul_comm ] using h_neq )

/-
If $f(n) = o(n)$ and $f(n) \to \infty$, then there are infinitely many vertices on the upper convex hull.
-/
lemma infinite_vertices_thm_v2 {f : ℕ → ℝ} (h_o : IsLittleO Filter.atTop f (fun n => (n : ℝ)))
    (h_inf : Filter.Tendsto f Filter.atTop Filter.atTop) : Set.Infinite { n | is_vertex f n } := by
  by_contra h_finite
  let S := { n | is_vertex f n }
  have hS_finite : S.Finite := by simpa using h_finite
  have hS_nonempty : S.Nonempty := ⟨ 0, zero_is_vertex h_o h_inf ⟩
  let S_fin := hS_finite.toFinset
  have hS_fin_nonempty : S_fin.Nonempty := hS_finite.toFinset_nonempty.mpr hS_nonempty
  let N := S_fin.max' hS_fin_nonempty
  have hN_vertex : is_vertex f N := by
    have := S_fin.max'_mem hS_fin_nonempty
    simp [S_fin, S] at this
    exact this
  have hN_max : ∀ n, is_vertex f n → n ≤ N := by
    intro n hn
    have := S_fin.le_max' n (by simp [S_fin, S, hn])
    exact this
  obtain ⟨K, hK_gt, hK_max⟩ := exists_max_slope_gt_N (N := N) h_o h_inf
  have hK_vertex : is_vertex f K := max_slope_is_vertex hN_vertex hK_gt hK_max
  have hK_le_N : K ≤ N := hN_max K hK_vertex
  linarith

/-
If $f(n) = o(n)$ and $f(n) \to \infty$, then there are infinitely many vertices on the upper convex hull.
-/
lemma infinite_vertices_thm_v3 {f : ℕ → ℝ} (h_o : IsLittleO Filter.atTop f (fun n => (n : ℝ)))
    (h_inf : Filter.Tendsto f Filter.atTop Filter.atTop) : Set.Infinite { n | is_vertex f n } := by
  by_contra h_finite
  let S := { n | is_vertex f n }
  have hS_finite : S.Finite := by simpa using h_finite
  have hS_nonempty : S.Nonempty := ⟨ 0, zero_is_vertex h_o h_inf ⟩
  let S_fin := hS_finite.toFinset
  have hS_fin_nonempty : S_fin.Nonempty := hS_finite.toFinset_nonempty.mpr hS_nonempty
  let N := S_fin.max' hS_fin_nonempty
  have hN_vertex : is_vertex f N := by
    have := S_fin.max'_mem hS_fin_nonempty
    simp [S_fin, S] at this
    exact this
  have hN_max : ∀ n, is_vertex f n → n ≤ N := by
    intro n hn
    have := S_fin.le_max' n (by simp [S_fin, S, hn])
    exact this
  obtain ⟨K, hK_gt, hK_max⟩ := exists_max_slope_gt_N (N := N) h_o h_inf
  have hK_vertex : is_vertex f K := max_slope_is_vertex hN_vertex hK_gt hK_max
  have hK_le_N : K ≤ N := hN_max K hK_vertex
  linarith

/-
$4^n \le (2n+1) \binom{2n}{n}$.
-/
lemma centralBinom_lower_bound (n : ℕ) : 4^n ≤ (2*n + 1) * (2*n).choose n := by
  -- We know that $\sum_{k=0}^{2n} \binom{2n}{k} = 4^n$ and the largest term is $\binom{2n}{n}$.
  have h_sum : ∑ k ∈ Finset.range (2 * n + 1), Nat.choose (2 * n) k = 4 ^ n := by
    rw [ show 4 ^ n = 2 ^ ( 2 * n ) by norm_num [ pow_mul ], Nat.sum_range_choose ];
  exact h_sum ▸ le_trans ( Finset.sum_le_sum fun _ _ => Nat.choose_le_middle _ _ ) ( by norm_num )

/-
$\binom{2n}{n} \le (2n)^{\pi(2n)}$.
-/
lemma choose_le_pow_primeCounting (n : ℕ) (h : 1 ≤ n) :
    (2 * n).choose n ≤ (2 * n) ^ Nat.primeCounting (2 * n) := by
      -- By definition of binomial coefficients, $\binom{2n}{n} = \prod_{p \leq 2n} p^{v_p}$, where $v_p$ is the exponent of $p$ in the prime factorization of $\binom{2n}{n}$.
      have h_binom_factorization : Nat.choose (2 * n) n = ∏ p ∈ Finset.filter Nat.Prime (Finset.range (2 * n + 1)), p ^ (Nat.factorization (Nat.choose (2 * n) n) p) := by
        conv_lhs => rw [ ← Nat.factorization_prod_pow_eq_self ( Nat.ne_of_gt ( Nat.choose_pos ( by linarith ) ) ) ] ;
        rw [ Finsupp.prod_of_support_subset ] <;> norm_num [ Finset.subset_iff ];
        exact fun p pp d _ => ⟨ Nat.lt_succ_of_le ( pp.dvd_factorial.mp ( d.trans ( Nat.choose_mul_factorial_mul_factorial ( show n ≤ 2 * n by linarith ) ▸ dvd_mul_of_dvd_left ( by norm_num ) _ ) ) ), pp ⟩;
      -- For each prime $p$, $p^{v_p} \leq 2n$.
      have h_prime_power_le : ∀ p ∈ Finset.filter Nat.Prime (Finset.range (2 * n + 1)), p ^ (Nat.factorization (Nat.choose (2 * n) n) p) ≤ 2 * n := by
        intro p hp; have := @Nat.factorization_choose_le_log p ( 2 * n ) ; norm_num at *;
        exact Nat.pow_le_of_le_log ( by linarith ) ( this );
      refine le_trans ( h_binom_factorization.le ) ?_;
      refine' le_trans ( Finset.prod_le_prod' h_prime_power_le ) _ ; norm_num [ Nat.primeCounting ];
      rw [ Nat.primeCounting', Nat.count_eq_card_filter_range ]

/-
$4^n \le (2n+1) (2n)^{\pi(2n)}$.
-/
lemma four_pow_le_mul_pow_pi (n : ℕ) (h : 1 ≤ n) :
    4 ^ n ≤ (2 * n + 1) * (2 * n) ^ Nat.primeCounting (2 * n) := by
      exact le_trans ( centralBinom_lower_bound n ) ( Nat.mul_le_mul_left _ ( choose_le_pow_primeCounting n h ) )

/-
$n \log 4 - \log(2n+1) \le \pi(2n) \log(2n)$.
-/
lemma pi_ge_bound (n : ℕ) (h : 1 ≤ n) :
    (n : ℝ) * Real.log 4 - Real.log (2 * n + 1) ≤ Nat.primeCounting (2 * n) * Real.log (2 * n) := by
      have := @four_pow_le_mul_pow_pi n h;
      have := Real.log_le_log ( by positivity ) ( show ( 4 : ℝ ) ^ n ≤ ( 2 * n + 1 ) * ( 2 * n ) ^ Nat.primeCounting ( 2 * n ) by exact_mod_cast this ) ; rw [ Real.log_mul ( by positivity ) ( by positivity ), Real.log_pow, Real.log_pow ] at this ; norm_num at * ; linarith;

/-
There exists a constant $c > 0$ such that for sufficiently large $n$, $\pi(n) \ge c n / \log n$.
-/
lemma pi_lower_bound_asymp : ∃ c > 0, ∀ᶠ n : ℕ in Filter.atTop, c * (n : ℝ) / Real.log n ≤ Nat.primeCounting n := by
  -- Set $c$ to be $\log 2 / 4$.
  use Real.log 2 / 4;
  -- From `pi_ge_bound`, we have $\pi(2k) \log(2k) \ge k \log 4 - \log(2k+1)$.
  have h_pi_ge_bound : ∀ k : ℕ, 1 ≤ k → Nat.primeCounting (2 * k) * Real.log (2 * k) ≥ k * Real.log 4 - Real.log (2 * k + 1) := by
    field_simp;
    intro k hk; have := pi_ge_bound k hk; norm_cast at *; ring_nf at *; aesop;
  -- This implies $\pi(2k) \ge \frac{2k \log 2 - \log(2k+1)}{\log(2k)}$.
  have h_pi_ge_bound_simplified : ∀ k : ℕ, 16 ≤ k → Nat.primeCounting (2 * k) ≥ (2 * k * Real.log 2 - Real.log (2 * k + 1)) / Real.log (2 * k) := by
    intro k hk; rw [ ge_iff_le, div_le_iff₀ ( Real.log_pos <| by norm_cast; linarith ) ] ; specialize h_pi_ge_bound k ( by linarith ) ; rw [ show ( 4 : ℝ ) = 2 ^ 2 by norm_num, Real.log_pow ] at h_pi_ge_bound ; ring_nf at * ; linarith;
  -- For large $k$, $2k \log 2 - \log(2k+1) \ge k \log 2$.
  have h_pi_ge_bound_final : ∀ k : ℕ, 16 ≤ k → Nat.primeCounting (2 * k) ≥ (k * Real.log 2) / Real.log (2 * k) := by
    intros k hk
    have h_log_bound : Real.log (2 * k + 1) ≤ k * Real.log 2 := by
      rw [ ← Real.log_rpow, Real.log_le_log_iff ] <;> norm_cast <;> induction hk <;> norm_num [ Nat.pow_succ ] at *;
      linarith;
    exact le_trans ( by rw [ div_le_div_iff_of_pos_right ( Real.log_pos <| by norm_cast; linarith ) ] ; linarith ) ( h_pi_ge_bound_simplified k hk );
  -- Therefore, for sufficiently large $n$, $\pi(n) \ge \frac{n \log 2}{4 \log n}$.
  have h_pi_ge_bound_final : ∀ᶠ n in Filter.atTop, Nat.primeCounting n ≥ (n * Real.log 2) / (4 * Real.log n) := by
    refine' Filter.eventually_atTop.mpr ⟨ 32, fun n hn => _ ⟩ ; rcases Nat.even_or_odd' n with ⟨ k, rfl | rfl ⟩ <;> norm_num at *;
    · have := h_pi_ge_bound_final k ( by linarith ) ; ring_nf at *; linarith;
    · refine' le_trans _ ( h_pi_ge_bound_final k ( by linarith ) ) |> le_trans <| Nat.cast_le.mpr <| Nat.monotone_primeCounting <| by linarith;
      rw [ div_le_div_iff₀ ];
      · -- We can divide both sides by $Real.log 2$ since it is positive.
        suffices h_div : (2 * k + 1) * Real.log (2 * k) ≤ k * (4 * Real.log (2 * k + 1)) by
          nlinarith [ Real.log_pos one_lt_two ];
        nlinarith [ show ( k : ℝ ) ≥ 16 by norm_cast; linarith, Real.log_nonneg ( show ( 2 * k : ℝ ) ≥ 1 by norm_cast; linarith ), Real.log_le_log ( by norm_cast; linarith ) ( show ( 2 * k + 1 : ℝ ) ≥ 2 * k by linarith ) ];
      · exact mul_pos zero_lt_four ( Real.log_pos ( by norm_cast; linarith ) );
      · exact Real.log_pos ( by norm_cast; linarith );
  exact ⟨ by positivity, h_pi_ge_bound_final.mono fun n hn => by convert hn.le using 1 ; ring ⟩

/-
$\pi(p_n) = n + 1$.
-/
lemma Nat.primeCounting_nth_eq (n : ℕ) : Nat.primeCounting (Nat.nth Nat.Prime n) = n + 1 := by
  -- By definition of $p_n$, we know that there are exactly $n$ primes less than or equal to $p_n$.
  have h_prime_counting : Nat.count Nat.Prime (Nat.nth Nat.Prime n) = n := by
    rw [ Nat.count_nth ]
    exact fun h => False.elim <| Nat.infinite_setOf_prime <| h.subset fun x hx => Nat.prime_iff.mp hx |> fun hx' => by simpa [ ← Nat.prime_iff ] using hx'
  rw [ Nat.primeCounting ]
  rw [ Nat.primeCounting', Nat.count_eq_card_filter_range ] at *
  rw [ Finset.range_add_one, Finset.filter_insert ]
  aesop

/-
There exists $c > 0$ such that for sufficiently large $n$, $p_n / \log p_n \le (n+1)/c$.
-/
lemma prime_div_log_le_linear : ∃ c > 0, ∀ᶠ n : ℕ in Filter.atTop, (Nat.nth Nat.Prime n : ℝ) / Real.log (Nat.nth Nat.Prime n) ≤ (n + 1) / c := by
  -- From `pi_lower_bound_asymp`, there exists $c > 0$ such that for large $k$, $\pi(k) \ge c k / \log k$.
  obtain ⟨c, hc_pos, hc⟩ : ∃ c > 0, ∀ᶠ k in Filter.atTop, Nat.primeCounting k ≥ c * (k : ℝ) / Real.log k := by
    convert pi_lower_bound_asymp using 1;
  -- Let $k = p_n$. Since $p_n \to \infty$, for large $n$, $\pi(p_n) \ge c p_n / \log p_n$.
  have h_prime_counting_bound : ∀ᶠ n in Filter.atTop, Nat.primeCounting (Nat.nth Nat.Prime n) ≥ c * (Nat.nth Nat.Prime n : ℝ) / Real.log (Nat.nth Nat.Prime n) := by
    simp +zetaDelta at *;
    exact ⟨ hc.choose, fun n hn => hc.choose_spec _ <| hn.trans <| Nat.le_of_lt <| Nat.recOn n ( Nat.Prime.pos <| by norm_num ) fun n ihn => Nat.lt_of_le_of_lt ihn <| Nat.nth_strictMono ( Nat.infinite_setOf_prime ) <| Nat.lt_succ_self _ ⟩;
  -- We know $\pi(p_n) = n+1$.
  have h_prime_counting_nth : ∀ n, Nat.primeCounting (Nat.nth Nat.Prime n) = n + 1 := by
    exact fun n => Nat.primeCounting_nth_eq n;
  simp_all +decide [ mul_div_assoc ];
  exact ⟨ c, hc_pos, h_prime_counting_bound.choose, fun n hn => by rw [ le_div_iff₀' hc_pos ] ; linarith [ h_prime_counting_bound.choose_spec n hn ] ⟩

/-
$\log p_n = o(n)$.
-/
lemma log_prime_isLittleO_id : (fun n => Real.log (Nat.nth Nat.Prime n)) =o[Filter.atTop] (fun n => (n : ℝ)) := by
  -- There exists $c > 0$ such that for sufficiently large $n$, $p_n / \log p_n \le (n+1)/c$.
  obtain ⟨c, hc₀, hc⟩ : ∃ c > 0, ∀ᶠ n in Filter.atTop, (Nat.nth Nat.Prime n : ℝ) / Real.log (Nat.nth Nat.Prime n) ≤ (n + 1) / c := by
    exact prime_div_log_le_linear;
  -- This implies $\frac{\log p_n}{n} \le \frac{n+1}{nc} \frac{(\log p_n)^2}{p_n}$.
  have h_bound : ∀ᶠ n in Filter.atTop, (Real.log (Nat.nth Nat.Prime n)) / (n : ℝ) ≤ ((n + 1) / (n * c)) * ((Real.log (Nat.nth Nat.Prime n))^2 / (Nat.nth Nat.Prime n)) := by
    filter_upwards [ hc, Filter.eventually_gt_atTop 0 ] with n hn hn';
    rw [ div_mul_div_comm, div_le_div_iff₀ ] at * <;> try positivity;
    · nlinarith [ show 0 < ( n : ℝ ) * Real.log ( Nat.nth Nat.Prime n ) by exact mul_pos ( Nat.cast_pos.mpr hn' ) ( Real.log_pos ( Nat.one_lt_cast.mpr ( Nat.Prime.one_lt ( Nat.prime_nth_prime n ) ) ) ) ];
    · exact Real.log_pos <| Nat.one_lt_cast.mpr <| Nat.Prime.one_lt <| Nat.prime_nth_prime n;
    · exact mul_pos ( mul_pos ( Nat.cast_pos.mpr hn' ) hc₀ ) ( Nat.cast_pos.mpr ( Nat.Prime.pos ( Nat.prime_nth_prime n ) ) );
  -- We know that $\frac{(\log x)^2}{x} \to 0$ as $x \to \infty$.
  have h_log_sq_div_x_zero : Filter.Tendsto (fun x : ℝ => (Real.log x)^2 / x) Filter.atTop (nhds 0) := by
    -- Let $y = \log x$, therefore the expression becomes $\frac{y^2}{e^y}$.
    suffices h_log_sq_div_exp_log : Filter.Tendsto (fun y : ℝ => y^2 / Real.exp y) Filter.atTop (nhds 0) by
      have := h_log_sq_div_exp_log.comp Real.tendsto_log_atTop;
      exact this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by rw [ Function.comp_apply, Real.exp_log hx ] );
    simpa [ Real.exp_neg ] using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2;
  -- Since $\frac{n+1}{nc} \to \frac{1}{c}$, we have $\frac{n+1}{nc} \frac{(\log p_n)^2}{p_n} \to 0$.
  have h_frac_zero : Filter.Tendsto (fun n : ℕ => ((n + 1) / (n * c)) * ((Real.log (Nat.nth Nat.Prime n))^2 / (Nat.nth Nat.Prime n))) Filter.atTop (nhds 0) := by
    -- We know that $\frac{n+1}{nc} \to \frac{1}{c}$ as $n \to \infty$.
    have h_frac_one_c : Filter.Tendsto (fun n : ℕ => (n + 1 : ℝ) / (n * c)) Filter.atTop (nhds (1 / c)) := by
      ring_nf;
      simpa using Filter.Tendsto.add ( tendsto_const_nhds.congr' ( by filter_upwards [ Filter.eventually_ne_atTop 0 ] with n hn; aesop ) ) ( tendsto_inverse_atTop_nhds_zero_nat.mul tendsto_const_nhds );
    simpa using h_frac_one_c.mul ( h_log_sq_div_x_zero.comp ( tendsto_natCast_atTop_atTop.comp ( Nat.nth_strictMono ( Nat.infinite_setOf_prime ) |> StrictMono.tendsto_atTop ) ) );
  rw [ Asymptotics.isLittleO_iff_tendsto' ];
  · exact squeeze_zero_norm' ( by filter_upwards [ h_bound ] with n hn; rw [ Real.norm_of_nonneg ( div_nonneg ( Real.log_nonneg <| mod_cast Nat.Prime.pos <| Nat.prime_nth_prime n ) <| Nat.cast_nonneg _ ) ] ; exact hn ) h_frac_zero;
  · filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn hn' using absurd hn' <| by positivity;

/-
There are infinitely many $n$ such that $p_n^2 > p_{n-i} p_{n+i}$ for all $0 < i \le n$.
-/
theorem infinitely_many_prime_sq_gt_neighbors : Set.Infinite { n | ∀ i, 0 < i → i ≤ n → (Nat.nth Nat.Prime n)^2 > Nat.nth Nat.Prime (n - i) * Nat.nth Nat.Prime (n + i) } := by
  -- We know that the set of vertices of the upper convex hull of $a_n = \log p_n$ is infinite (by `infinite_vertices`, using `log_prime_isLittleO_id` and `a_tendsto_atTop`).
  have h_vertices_infinite : Set.Infinite {n : ℕ | is_vertex (fun n => Real.log (Nat.nth Nat.Prime n)) n} := by
    apply_rules [ infinite_vertices_final, a_tendsto_atTop, log_prime_isLittleO_id ];
  refine h_vertices_infinite.mono ?_;
  intros n hn i hi_pos hi_le_n
  have h_log : 2 * Real.log (Nat.nth Nat.Prime n) > Real.log (Nat.nth Nat.Prime (n - i)) + Real.log (Nat.nth Nat.Prime (n + i)) := by
    convert log_prime_vertex_implies_strict_ineq n hn i hi_pos hi_le_n using 1;
  exact_mod_cast ( by rw [ ← Real.log_rpow, ← Real.log_mul, gt_iff_lt, Real.log_lt_log_iff ] at * <;> norm_cast at * <;> nlinarith [ Nat.Prime.two_le ( Nat.prime_nth_prime n ), Nat.Prime.two_le ( Nat.prime_nth_prime ( n - i ) ), Nat.Prime.two_le ( Nat.prime_nth_prime ( n + i ) ) ] : ( Nat.nth Nat.Prime n : ℝ ) ^ 2 > Nat.nth Nat.Prime ( n - i ) * Nat.nth Nat.Prime ( n + i ) )

/--
For all sufficiently large `n`, there exists some `i < n` such that
`(p_n)^2 < p_{n+i} * p_{n-i}`, where `p_k` is the `k`-th prime.

Here we use `Nat.nthPrime : ℕ → ℕ` for the `k`-th prime (with `k = 0` giving `2`).

Note that the indexing is off by one from the usual convention in mathematics,
but nonetheless the statement is exactly what is intended!
-/
def erdos_453 : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
    ∃ i : ℕ, i < n ∧
      (Nat.nth Nat.Prime n) ^ (2 : ℕ) <
        (Nat.nth Nat.Prime (n + i)) * (Nat.nth Nat.Prime (n - i))

theorem not_erdos_453 : ¬ erdos_453 := by
  -- By combining the results, we conclude that $p_n^2 > p_{n-i} p_{n+i}$ for infinitely many $n$.
  have h_inf : Set.Infinite {n | ∀ i, 0 < i → i ≤ n → (Nat.nth Nat.Prime n) ^ 2 > Nat.nth Nat.Prime (n - i) * Nat.nth Nat.Prime (n + i)} := by
    -- Apply the lemma that states there are infinitely many n such that for all i, 0 < i → i ≤ n → p_n^2 > p_{n-i} * p_{n+i}.
    apply infinitely_many_prime_sq_gt_neighbors;
  contrapose! h_inf;
  -- By definition of $erdos_453$, if it is true, then for all $n \geq N$, there exists an $i < n$ such that $p_n^2 < p_{n+i} * p_{n-i}$.
  obtain ⟨N, hN⟩ := h_inf;
  have h_finite : ∀ n ≥ N, ¬(∀ i, 0 < i → i ≤ n → (Nat.nth Nat.Prime n) ^ 2 > Nat.nth Nat.Prime (n - i) * Nat.nth Nat.Prime (n + i)) := by
    grind;
  exact Set.not_infinite.mpr ( Set.finite_iff_bddAbove.mpr ⟨ N, fun n hn => not_lt.1 fun contra => h_finite n contra.le hn ⟩ )

#print axioms not_erdos_453
-- 'not_erdos_453' depends on axioms: [propext, Classical.choice, Quot.sound]
