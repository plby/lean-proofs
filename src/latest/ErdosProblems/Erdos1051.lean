/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
/-
This is a Lean formalization of a solution to Erdős Problem 1051.
https://www.erdosproblems.com/forum/thread/1051

Informal authors:
- Gemini Deep Think
- Kevin Barreto
- J. Kang
- S. Kim
- V. Kovac
- S. Zhang

Formal authors:
- Kevin Barreto

URLs:
- https://www.erdosproblems.com/forum/thread/1051#post-3931
- https://arxiv.org/abs/2601.21442
-/
import Mathlib

namespace Erdos1051


noncomputable section

/-
Definitions of auxiliary sequences and summability lemma.
-/
noncomputable def P_n (a : ℕ → ℕ) (n : ℕ) : ℕ := ∏ k ∈ Finset.range n, a k

noncomputable def R_n (a : ℕ → ℕ) (n : ℕ) : ℝ :=
  ∑' k, if k < n then 0 else 1 / ((a k : ℝ) * (a (k + 1) : ℝ))

noncomputable def K_n (a : ℕ → ℕ) (q : ℕ) (n : ℕ) : ℝ :=
  (q : ℝ) * (P_n a n : ℝ) * (R_n a n)

lemma summable_of_ge_two (a : ℕ → ℕ) (h_mono : StrictMono a) (h_ge_two : ∀ n, 2 ≤ a n) :
  Summable (fun n ↦ 1 / ((a n : ℝ) * (a (n + 1) : ℝ))) := by
    -- Since $a_n \geq 2$ and strictly increasing, we have $a_n \geq n + 2$.
    have h_ge_n : ∀ n, a n ≥ n + 2 := by
      exact fun n => Nat.recOn n (by linarith [h_ge_two 0])
        fun n ih => by linarith [h_mono n.lt_succ_self]
    exact Summable.of_nonneg_of_le (fun n : ℕ => by positivity)
      (fun n : ℕ => by rw [div_le_div_iff₀] <;> norm_cast <;>
        nlinarith [h_ge_two n, h_ge_two (n + 1), h_ge_n n, h_ge_n (n + 1)])
      (summable_nat_add_iff 1 |>.2 <| Real.summable_one_div_nat_pow.2 one_lt_two)

/-
Lemma establishing lower bound for $K_n$.
-/
noncomputable def K_n_aux (a : ℕ → ℕ) (q : ℕ) (n : ℕ) : ℝ :=
  (q : ℝ) * (P_n a (n + 1) : ℝ) * (R_n a n)

lemma R_n_lower_bound
  (b : ℕ → ℕ)
  (h_mono : StrictMono b)
  (h_ge_two : ∀ n, 2 ≤ b n)
  (p q : ℕ)
  (hq : 0 < q)
  (h_sum : (∑' n, 1 / ((b n : ℝ) * (b (n + 1) : ℝ))) = p / q) :
  ∀ n, 1 ≤ K_n_aux b q n := by
    intro n
    have h_K_int : ∃ M : ℤ, M = K_n_aux b q n := by
      unfold K_n_aux
      generalize_proofs at *
      -- By definition of $K$, we know that
      -- $K_n = q P_n (p/q - \sum_{k=0}^{n-1} \frac{1}{b_k b_{k+1}})$.
      have h_K_def : R_n b n =
          (p / q) - ∑ k ∈ Finset.range n, (1 / ((b k : ℝ) * (b (k + 1) : ℝ))) := by
        unfold R_n
        rw [← h_sum, ← Summable.sum_add_tsum_nat_add n]
        · rw [eq_comm, ← Summable.sum_add_tsum_nat_add n]
          · rw [Finset.sum_congr rfl fun i hi => if_pos <| Finset.mem_range.mp hi]
            aesop
          · exact summable_of_ge_two b h_mono h_ge_two
        · refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
            (show Summable fun k => (1 : ℝ) / ((b k : ℝ) * (b (k + 1) : ℝ)) from ?_)
          · split_ifs <;> norm_num
            positivity
          · exact summable_of_ge_two b h_mono h_ge_two
      -- Substitute the definition of $K$ into the expression.
      use p * (∏ k ∈ Finset.range (n + 1), b k) -
        q * (∑ k ∈ Finset.range n, (∏ j ∈ Finset.range (n + 1), b j) / (b k * b (k + 1)))
      simp_all +decide [mul_sub, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _,
        div_eq_mul_inv]
      field_simp
      congr! 2
      · norm_cast
      · rw [Int.cast_div] <;> norm_num
        · unfold P_n
          push_cast
          ring
        · rw [Finset.prod_eq_mul_prod_diff_singleton_of_mem <|
              Finset.mem_range.mpr <| Nat.lt_succ_of_lt <| Finset.mem_range.mp ‹_›]
          exact mul_dvd_mul_left _ (Finset.dvd_prod_of_mem _ <| by aesop)
        · grind
    have h_K_pos : 0 < K_n_aux b q n := by
      refine mul_pos (mul_pos (Nat.cast_pos.mpr hq)
        (Nat.cast_pos.mpr (Finset.prod_pos fun _ _ => by linarith [h_ge_two ‹_›]))) ?_
      refine lt_of_lt_of_le ?_ (Summable.le_tsum ?_ (n + 1) ?_) <;> norm_num [h_ge_two]
      · exact mul_pos (inv_pos.mpr (Nat.cast_pos.mpr (by linarith [h_ge_two (n + 1 + 1)])))
          (inv_pos.mpr (Nat.cast_pos.mpr (by linarith [h_ge_two (n + 1)])))
      · have h_summable : Summable (fun k => (1 : ℝ) / ((b k) * (b (k + 1)))) := by
          exact summable_of_ge_two b h_mono h_ge_two
        exact Summable.of_nonneg_of_le (fun k => by split_ifs <;> positivity)
          (fun k => by split_ifs <;> first | positivity | simp [mul_comm]) h_summable
      · intro j hj
        split_ifs <;> positivity
    obtain ⟨M, hM⟩ := h_K_int
    have h_K_ge_one : 1 ≤ M := by
      exact_mod_cast hM.symm ▸ h_K_pos
    have h_K_ge_one' : 1 ≤ K_n_aux b q n := by
      exact hM ▸ mod_cast h_K_ge_one
    exact h_K_ge_one'

/-
Lemma establishing upper bound for $R_{n+1}$ and $K_{n+1}$.
-/
lemma R_n_upper_bound
  (b : ℕ → ℕ)
  (h_mono : StrictMono b)
  (h_ge_two : ∀ n, 2 ≤ b n)
  (q : ℕ) :
  ∀ n, R_n b (n + 1) ≤ 1 / (b (n + 1) : ℝ) ∧
       K_n_aux b q (n + 1) ≤ (q : ℝ) * (P_n b (n + 1) : ℝ) := by
         -- Applying the lemma:
         -- $\frac{1}{b_k b_{k+1}} \le \frac{1}{b_k} - \frac{1}{b_{k+1}}$.
         have h_lemma (n : ℕ) : R_n b (n + 1) ≤ 1 / ((b (n + 1)) : ℝ) := by
           have h_R_le_n1 : R_n b (n + 1) ≤
               ∑' k,
                 (if k ≥ n + 1 then
                   (1 / ((b k : ℝ)) - 1 / ((b (k + 1) : ℝ)))
                 else 0) := by
             refine Summable.tsum_le_tsum ?_ ?_ ?_
             · intro i
               split_ifs <;> norm_num
               · linarith
               · rw [inv_mul_le_iff₀] <;> nlinarith only [
                   show (b i : ℝ) ≥ 2 by exact_mod_cast h_ge_two i,
                   show (b (i + 1) : ℝ) ≥ b i + 1 by exact_mod_cast h_mono i.lt_succ_self,
                   inv_pos.mpr (show (b i : ℝ) > 0 by
                     exact_mod_cast by linarith [h_ge_two i]),
                   inv_pos.mpr (show (b (i + 1) : ℝ) > 0 by
                     exact_mod_cast by linarith [h_ge_two (i + 1)]),
                   mul_inv_cancel₀ (show (b i : ℝ) ≠ 0 by
                     exact_mod_cast by linarith [h_ge_two i]),
                   mul_inv_cancel₀ (show (b (i + 1) : ℝ) ≠ 0 by
                     exact_mod_cast by linarith [h_ge_two (i + 1)])]
               · linarith
             · have := summable_of_ge_two b h_mono h_ge_two
               exact Summable.of_nonneg_of_le (fun k => by positivity)
                 (fun k => by split_ifs <;> first | positivity | aesop) this
             · rw [← summable_nat_add_iff (n + 1)]
               refine (summable_iff_not_tendsto_nat_atTop_of_nonneg (fun _ => ?_)).2 ?_
               · split_ifs <;> first | positivity |
                   exact sub_nonneg_of_le <| one_div_le_one_div_of_le
                     (by
                       norm_cast
                       linarith [h_ge_two (‹_› + (n + 1)),
                        h_ge_two (‹_› + (n + 1) + 1)])
                     <| mod_cast h_mono.monotone <| by linarith
               · -- $\sum_{i=0}^{\infty} \left( \frac{1}{b(i+n+1)} - \frac{1}{b(i+n+2)} \right)$
                 -- is a telescoping series.
                  have h_telescoping : ∀ N, ∑ i ∈ Finset.range N,
                      (1 / (b (i + (n + 1)) : ℝ) - 1 / (b (i + (n + 1) + 1) : ℝ)) =
                      1 / (b (n + 1) : ℝ) - 1 / (b (N + (n + 1)) : ℝ) := by
                    exact fun N => by convert Finset.sum_range_sub' _ _ using 3 <;> ring_nf
                  simp_all +decide only [ge_iff_le, le_add_iff_nonneg_left, zero_le, ↓reduceIte,
                    one_div, Finset.sum_sub_distrib]
                  exact not_tendsto_atTop_of_tendsto_nhds (tendsto_const_nhds.sub <|
                    tendsto_inv_atTop_zero.comp <| tendsto_natCast_atTop_atTop.comp <|
                    h_mono.tendsto_atTop.comp <| Filter.tendsto_add_atTop_nat _)
           -- Notice that $\sum_{k=n+1}^{\infty} (1/b_k - 1/b_{k+1})$
           -- is a telescoping series.
           have h_telescoping : ∀ N ≥ n + 1,
               ∑ k ∈ Finset.range N,
                 (if k ≥ n + 1 then (1 / ((b k : ℝ)) - 1 / ((b (k + 1) : ℝ))) else 0) =
               (1 / ((b (n + 1)) : ℝ)) - (1 / ((b N : ℝ))) := by
             intro N hN
             induction hN <;> simp_all +decide [Finset.sum_range_succ]
             ring_nf
             exact Finset.sum_eq_zero fun x hx => if_neg (by linarith [Finset.mem_range.mp hx])
           -- Taking the limit of the telescoping series as $N \to \infty$,
           -- we get $\sum_{k=n+1}^{\infty} (1/b_k - 1/b_{k+1}) = 1/b_{n+1}$.
           have h_telescoping_limit : Filter.Tendsto
               (fun N => ∑ k ∈ Finset.range N,
                 (if k ≥ n + 1 then (1 / ((b k : ℝ)) - 1 / ((b (k + 1) : ℝ))) else 0))
               Filter.atTop (nhds (1 / ((b (n + 1)) : ℝ))) := by
             rw [Filter.tendsto_congr'
               (Filter.eventuallyEq_of_mem (Filter.Ici_mem_atTop (n + 1)) h_telescoping)]
             exact le_trans (tendsto_const_nhds.sub <| tendsto_const_nhds.div_atTop <|
               tendsto_natCast_atTop_atTop.comp <| h_mono.tendsto_atTop) <| by norm_num
           refine le_trans h_R_le_n1 <| le_of_tendsto_of_tendsto'
             (Summable.hasSum (show Summable _ from ?_) |> HasSum.tendsto_sum_nat)
             h_telescoping_limit fun N => ?_
           · exact (summable_iff_not_tendsto_nat_atTop_of_nonneg (fun _ => by
               split_ifs <;> first | positivity |
                 exact sub_nonneg_of_le <| one_div_le_one_div_of_le
                   (Nat.cast_pos.mpr <| by linarith [h_ge_two ‹_›]) <|
                   Nat.cast_le.mpr <| h_mono.monotone <| by linarith)).2
               fun h => not_tendsto_nhds_of_tendsto_atTop h _ h_telescoping_limit
           · norm_num
         unfold K_n_aux P_n
         norm_num [Finset.prod_range_succ, mul_assoc] at *
         exact fun n => ⟨h_lemma n, mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by
             have h_prod_pos : (0 : ℝ) < b n * b (n + 1) :=
               mul_pos (Nat.cast_pos.mpr (by linarith [h_ge_two n]))
                 (Nat.cast_pos.mpr (by linarith [h_ge_two (n + 1)]))
             nlinarith [h_lemma n, h_prod_pos,
               inv_mul_cancel₀ (by
                 norm_cast
                 linarith [h_ge_two (n + 1)] : (b (n + 1) : ℝ) ≠ 0)])
           (Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _)) (Nat.cast_nonneg _)⟩

/-
Recurrence relation for $P_n$.
-/
lemma P_n_recurrence
  (b : ℕ → ℕ)
  (h_mono : StrictMono b)
  (h_ge_two : ∀ n, 2 ≤ b n)
  (p q : ℕ)
  (hq : 0 < q)
  (h_sum : (∑' n, 1 / ((b n : ℝ) * (b (n + 1) : ℝ))) = p / q) :
  ∀ n, (P_n b (n + 2) : ℝ) ≤
      (1.5 * q) * (P_n b (n + 1) : ℝ) ^ 2 := by
    intro n
    have h_b_n_plus_one :
        b (n + 1) ≤ 1.5 * (q : ℝ) * (P_n b (n + 1) : ℝ) := by
      -- By Lemma 2 and $K_n \ge 1$, we have:
      -- $b_{n+1} \le b_{n+1} K_n = q P_n + K_{n+1} \le q P_n + q P_{n+1}$.
      have h_b_n_plus_one :
          b (n + 1) ≤
            (q : ℝ) * (P_n b n : ℝ) + (q : ℝ) * (P_n b (n + 1) : ℝ) := by
        have h_bound : (b (n + 1) : ℝ) * (K_n_aux b q n) =
            (q : ℝ) * (P_n b n) + (K_n_aux b q (n + 1)) := by
          unfold K_n_aux P_n
          ring_nf
          -- Using the definition of $R_n$ and $R_{n+1}$, we can rewrite the equation.
          have h_rewrite :
              R_n b n =
                1 / ((b n : ℝ) * (b (n + 1) : ℝ)) + R_n b (n + 1) := by
            unfold R_n
            rw [Summable.tsum_eq_add_tsum_ite]
            · congr! 1
              · exact if_neg (Nat.not_lt_of_ge (Nat.le_refl _))
              · grind
            · refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
                (show Summable fun k => (1 : ℝ) / (b k * b (k + 1)) from ?_)
              · split_ifs <;> norm_num
                positivity
              · exact summable_of_ge_two b h_mono h_ge_two
          rw [h_rewrite]
          norm_num [add_comm, add_left_comm, Finset.prod_range_succ]
          ring_nf
          norm_num [add_comm 1 n, add_comm 2 n, Finset.prod_range_succ, mul_assoc, mul_comm,
            mul_left_comm, ne_of_gt (zero_lt_two.trans_le (h_ge_two _))]
          ring
        -- Since $K_n \ge 1$, we have $b_{n+1} \le b_{n+1} K_n$.
        have h_b_n_plus_one_le :
            (b (n + 1) : ℝ) ≤ (b (n + 1) : ℝ) * (K_n_aux b q n) := by
          refine le_mul_of_one_le_right (Nat.cast_nonneg _) ?_
          apply R_n_lower_bound b h_mono h_ge_two p q hq h_sum
        have h_K_n_plus_one_le :
            K_n_aux b q (n + 1) ≤
              (q : ℝ) * (P_n b (n + 1) : ℝ) := by
          exact R_n_upper_bound b h_mono h_ge_two q _ |>.2
        linarith
      -- Since $b_n \ge 2$, $P_{n+1} = b_n P_n \ge 2 P_n$, so $P_n \le \frac{1}{2} P_{n+1}$.
      have h_P_n_le_half_P_n_plus_one :
          (P_n b n : ℝ) ≤ (1 / 2) * (P_n b (n + 1) : ℝ) := by
        unfold P_n
        norm_num [Finset.prod_range_succ]
        nlinarith only [show (b n : ℝ) ≥ 2 by exact_mod_cast h_ge_two n,
          show (∏ i ∈ Finset.range n, (b i : ℝ)) ≥ 0 by
            exact Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _]
      nlinarith
    unfold P_n at *
    norm_num [Finset.prod_range_succ] at *
    nlinarith [show 0 ≤ (∏ i ∈ Finset.range n, (b i : ℝ)) * b n by
      exact mul_nonneg (Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _) (Nat.cast_nonneg _)]

/-
Convergence of the sequence $u_n$.
-/
noncomputable def Erdos1051_u (b : ℕ → ℕ) (n : ℕ) : ℝ := Real.log (P_n b n : ℝ) / 2 ^ n

lemma Erdos1051_u_converges
  (b : ℕ → ℕ)
  (h_mono : StrictMono b)
  (h_ge_two : ∀ n, 2 ≤ b n)
  (p q : ℕ)
  (hq : 0 < q)
  (h_sum : (∑' n, 1 / ((b n : ℝ) * (b (n + 1) : ℝ))) = p / q) :
  ∃ Y, Filter.Tendsto (Erdos1051_u b) Filter.atTop (nhds Y) := by
    -- By definition of $u_n$, we have $u_{n+2} \leq u_{n+1} + \frac{\log C}{2^{n+2}}$.
    have h_bound : ∀ n,
        ((Real.log (P_n b (n + 2) : ℝ)) / (2 : ℝ) ^ (n + 2)) ≤
        ((Real.log (P_n b (n + 1) : ℝ)) / (2 : ℝ) ^ (n + 1)) +
        (Real.log (1.5 * q)) / (2 : ℝ) ^ (n + 2) := by
      -- From $P_{n+2} \le C P_{n+1}^2$, we have:
      -- $\log P_{n+2} \le \log C + 2 \log P_{n+1}$.
      have h_log_bound : ∀ n, Real.log (P_n b (n + 2) : ℝ) ≤
          Real.log (1.5 * q) + 2 * Real.log (P_n b (n + 1) : ℝ) := by
        -- Apply the logarithm to both sides of the recurrence relation.
        intros n
        have h_log : Real.log (P_n b (n + 2)) ≤
            Real.log ((1.5 * q) * (P_n b (n + 1))^2) := by
          have := P_n_recurrence b h_mono h_ge_two p q hq h_sum n
          norm_num at *
          gcongr
          exact Nat.cast_pos.mpr (Finset.prod_pos fun _ _ => zero_lt_two.trans_le (h_ge_two _))
        rwa [Real.log_mul (by positivity) (by
            exact ne_of_gt (sq_pos_of_pos (Nat.cast_pos.mpr (show 0 < P_n b (n + 1) from
              Finset.prod_pos fun _ _ => by linarith [h_ge_two ‹_›])))),
          Real.log_pow] at h_log
      intro n
      convert div_le_div_of_nonneg_right (h_log_bound n)
        (by positivity : (0 : ℝ) ≤ 2 ^ (n + 2)) using 1
      ring
    -- Let $v_n = u_n + \frac{\log C}{2^n}$. Then $v_{n+1} \le v_n$ for large enough $n$.
    set v : ℕ → ℝ := fun n =>
      ((Real.log (P_n b (n + 1) : ℝ)) / (2 : ℝ) ^ (n + 1)) +
      (Real.log (1.5 * q)) / (2 : ℝ) ^ (n + 1)
    have hv_decreasing : ∃ N, ∀ n ≥ N, v (n + 1) ≤ v n := by
      simp +zetaDelta only [ge_iff_le] at *
      use 1
      intros n hn
      specialize h_bound n
      ring_nf at *
      linarith
    -- Since $v_n$ is decreasing and bounded below, it converges.
    obtain ⟨N, hN⟩ := hv_decreasing
    have hv_converges : Filter.Tendsto v Filter.atTop (nhds (sInf {v n | n ≥ N})) := by
      have hv_bounded : BddBelow {v n | n ≥ N} := by
        use 0
        rintro x ⟨n, hn, rfl⟩
        exact add_nonneg
          (div_nonneg (Real.log_nonneg <| mod_cast Nat.one_le_iff_ne_zero.mpr <|
            ne_of_gt <| Finset.prod_pos fun _ _ => by linarith [h_ge_two ‹_›]) <|
              by positivity)
          (div_nonneg (Real.log_nonneg <|
            by
              norm_num
              linarith [show (q : ℝ) ≥ 1 by norm_cast])
            <| by positivity)
      have hv_monotone : Antitone (fun n => v (n + N)) := by
        exact antitone_nat_of_succ_le fun n => by
          simpa only [Nat.succ_add] using hN _ (Nat.le_add_left _ _)
      have hv_converges :
          Filter.Tendsto (fun n => v (n + N)) Filter.atTop (nhds (sInf {v (n + N) | n : ℕ})) := by
        exact tendsto_atTop_ciInf hv_monotone ⟨hv_bounded.choose, by
          rintro x ⟨n, rfl⟩
          exact hv_bounded.choose_spec ⟨n + N, by linarith, rfl⟩⟩
      rw [Filter.tendsto_add_atTop_iff_nat] at hv_converges
      convert hv_converges using 2
      exact congr_arg _ (by
        ext
        exact ⟨fun ⟨n, hn₁, hn₂⟩ =>
            ⟨n - N, by simpa [Nat.sub_add_cancel hn₁] using hn₂⟩,
          fun ⟨n, hn₂⟩ =>
            ⟨n + N, by linarith, by simpa [Nat.sub_add_cancel] using hn₂⟩⟩)
    -- Since log C / 2^n → 0, we have u_n → inf{v_n | n ≥ N}.
    have hu_converges : Filter.Tendsto
        (fun n => v n - (Real.log (1.5 * q)) / (2 : ℝ) ^ (n + 1))
        Filter.atTop (nhds (sInf {v n | n ≥ N})) := by
      simpa using hv_converges.sub (tendsto_const_nhds.div_atTop
        (tendsto_pow_atTop_atTop_of_one_lt one_lt_two |> Filter.Tendsto.comp <|
          Filter.tendsto_add_atTop_nat _))
    use sInf {v n | n ≥ N}
    rw [← Filter.tendsto_add_atTop_iff_nat 1]
    aesop

/-
Existence of limit L > 1.
-/
lemma Erdos1051_L_exists_gt_one
  (b : ℕ → ℕ)
  (h_mono : StrictMono b)
  (h_ge_two : ∀ n, 2 ≤ b n)
  (h_liminf : 1 < Filter.atTop.liminf (fun n ↦ (b n : ℝ) ^ ((1 : ℝ) / 2 ^ n)))
  (p q : ℕ) (hq : 0 < q)
  (h_sum : (∑' n, 1 / ((b n : ℝ) * (b (n + 1) : ℝ))) = p / q) :
  ∃ L, 1 < L ∧
    Filter.Tendsto (fun n ↦ (b n : ℝ) ^ ((1 : ℝ) / 2 ^ n)) Filter.atTop (nhds L) := by
    -- Let $Y = \lim u_n$.
    obtain ⟨Y, hY⟩ :
        ∃ Y, Filter.Tendsto (fun n => Real.log (b n) / 2 ^ n) Filter.atTop (nhds Y) := by
      have h_seq : Filter.Tendsto (fun n =>
          Real.log (P_n b n) / 2 ^ n) Filter.atTop
          (nhds (Classical.choose (Erdos1051_u_converges b h_mono h_ge_two p q hq h_sum))) := by
        exact Classical.choose_spec (Erdos1051_u_converges b h_mono h_ge_two p q hq h_sum)
      have h_seq : Filter.Tendsto (fun n =>
          (Real.log (P_n b (n + 1)) - Real.log (P_n b n)) / 2 ^ n) Filter.atTop
          (nhds (Classical.choose (Erdos1051_u_converges b h_mono h_ge_two p q hq h_sum))) := by
        have h_seq : Filter.Tendsto (fun n =>
            (Real.log (P_n b (n + 1)) / 2 ^ (n + 1)) * 2 -
            (Real.log (P_n b n) / 2 ^ n)) Filter.atTop
            (nhds (Classical.choose (Erdos1051_u_converges b h_mono h_ge_two p q hq h_sum))) := by
          convert Filter.Tendsto.sub
            (h_seq.comp (Filter.tendsto_add_atTop_nat 1) |> Filter.Tendsto.mul_const 2)
            h_seq using 2
          ring
        convert h_seq using 2
        ring
      have h_seq : Filter.Tendsto (fun n =>
          Real.log (b n) / 2 ^ n) Filter.atTop
          (nhds (Classical.choose (Erdos1051_u_converges b h_mono h_ge_two p q hq h_sum))) := by
        have h_eq : ∀ n, Real.log (P_n b (n + 1)) =
            Real.log (P_n b n) + Real.log (b n) := by
          intro n
          rw [← Real.log_mul
            (Nat.cast_ne_zero.mpr <| ne_of_gt <| show 0 < P_n b n from
              Finset.prod_pos fun _ _ => by linarith [h_ge_two ‹_›])
            (Nat.cast_ne_zero.mpr <| ne_of_gt <| show 0 < b n from by linarith [h_ge_two n])]
          push_cast [P_n]
          ring_nf
          rw [add_comm, Finset.prod_range_succ]
        aesop
      use Classical.choose (Erdos1051_u_converges b h_mono h_ge_two p q hq h_sum)
    have h_lim : Filter.Tendsto (fun n => (b n : ℝ) ^ (1 / 2 ^ n : ℝ)) Filter.atTop
        (nhds (Real.exp Y)) := by
      convert hY.exp using 2
      · rw [Real.rpow_def_of_pos (Nat.cast_pos.mpr <| pos_of_gt <| h_ge_two _)]
        ring_nf
        rw [Real.exp_eq_exp_ℝ]
      · rw [Real.exp_eq_exp_ℝ]
    rw [Filter.Tendsto.liminf_eq h_lim] at h_liminf
    aesop

/-
Upper bound for $R_n$ in terms of $D$.
-/
lemma R_n_upper_bound_D
  (b : ℕ → ℕ)
  (h_mono : StrictMono b)
  (h_ge_two : ∀ n, 2 ≤ b n)
  (L : ℝ)
  (h_lim : Filter.Tendsto (fun n ↦ (b n : ℝ) ^ ((1 : ℝ) / 2 ^ n)) Filter.atTop (nhds L))
  (D : ℝ)
  (hD_gt_one : 1 < D)
  (hD_lt_L : D < L) :
  ∃ N₀, ∀ n ≥ N₀, R_n b n ≤ 2 * D ^ (-3 * (2 : ℝ) ^ n) := by
    -- Since $b_n^{1/2^n} \to L > D$, eventually $b_n^{1/2^n} \ge D$, so $b_n \ge D^{2^n}$.
    obtain ⟨N₀, hN₀⟩ : ∃ N₀, ∀ n ≥ N₀, (b n : ℝ) ≥ D ^ (2 ^ n : ℝ) := by
      have := h_lim.eventually (lt_mem_nhds hD_lt_L)
      exact Filter.eventually_atTop.mp (this.mono fun n hn => by
        exact le_trans (Real.rpow_le_rpow (by positivity) hn.le (by positivity))
          (by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
            norm_num))
    -- Then $b_k b_{k+1} \ge D^{2^k} D^{2^{k+1}} = D^{3 \cdot 2^k}$.
    have h_prod_bound :
        ∀ n ≥ N₀, ∀ k ≥ n, (b k : ℝ) * (b (k + 1) : ℝ) ≥ D ^ (3 * 2 ^ k : ℝ) := by
      intros n hn k hk
      have h_prod_ge_step :
          (b k : ℝ) * (b (k + 1) : ℝ) ≥ D ^ (2 ^ k : ℝ) * D ^ (2 ^ (k + 1) : ℝ) := by
        exact mul_le_mul (hN₀ k (by linarith)) (hN₀ (k + 1) (by linarith))
          (by positivity) (by positivity)
      convert h_prod_ge_step using 1
      rw [← Real.rpow_add (by positivity)]
      ring_nf
    -- So $R_n \le \sum_{k=n}^\infty D^{-3 \cdot 2^k}$.
    have h_R_bound :
        ∀ n ≥ N₀, R_n b n ≤ ∑' k : ℕ, (D ^ (-3 * 2 ^ (n + k) : ℝ)) := by
      intros n hn
      have h_R_le_sum :
          R_n b n ≤
            ∑' k : ℕ, (1 / ((b (n + k) : ℝ) * (b (n + k + 1) : ℝ))) := by
        unfold R_n
        rw [← Summable.sum_add_tsum_nat_add n]
        · simp +decide [add_comm n, Finset.sum_ite]
          exact Finset.sum_nonpos fun x hx => by
            rw [Finset.mem_filter] at hx
            linarith [Finset.mem_range.mp hx.1]
        · have h_summable :
              Summable (fun k : ℕ => (1 / ((b k : ℝ) * (b (k + 1) : ℝ)))) := by
            exact summable_of_ge_two b h_mono h_ge_two
          exact Summable.of_nonneg_of_le (fun k => by split_ifs <;> positivity)
            (fun k => by split_ifs <;> first | positivity | aesop) h_summable
      refine le_trans h_R_le_sum <| Summable.tsum_le_tsum ?_ ?_ ?_
      · intro k
        specialize h_prod_bound n hn (n + k) (by linarith)
        norm_num [Real.rpow_neg (by positivity : 0 ≤ D)] at *
        simpa only [← mul_inv, mul_comm] using inv_anti₀ (by positivity) h_prod_bound
      · have h_summable :
            Summable (fun k : ℕ => (1 / ((b k : ℝ) * (b (k + 1) : ℝ)))) := by
          exact summable_of_ge_two b h_mono h_ge_two
        exact h_summable.comp_injective (add_right_injective n)
      · norm_num [Real.rpow_neg (by positivity : 0 ≤ D)]
        norm_cast
        norm_num [pow_mul']
        ring_nf
        exact Summable.comp_injective
          (summable_geometric_of_lt_one (by positivity)
            (inv_lt_one_of_one_lt₀ hD_gt_one))
          fun a b h => by simpa using h
    -- Let $t_k = D^{-3 \cdot 2^k}$. Then $t_{k+1} = t_k^2$.
    set t : ℕ → ℝ := fun k => D ^ (-3 * 2 ^ k : ℝ)
    have h_t_recurrence : ∀ k, t (k + 1) = t k ^ 2 := by
      intro k
      simp [t]
      ring_nf
      rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (by positivity)]
      ring_nf
    -- Since $D > 1$, $t_k \to 0$. Eventually $t_k \le 1/2$.
    obtain ⟨N₁, hN₁⟩ : ∃ N₁, ∀ k ≥ N₁, t k ≤ 1 / 2 := by
      have h_t_zero : Filter.Tendsto t Filter.atTop (nhds 0) := by
        norm_num +zetaDelta at *
        norm_num [Real.rpow_def_of_pos (zero_lt_one.trans hD_gt_one)]
        exact Filter.Tendsto.const_mul_atTop (Real.log_pos hD_gt_one)
          (Filter.Tendsto.const_mul_atTop (by norm_num)
            (tendsto_pow_atTop_atTop_of_one_lt one_lt_two))
      simpa using h_t_zero.eventually (ge_mem_nhds <| by norm_num)
    -- Then $\sum_{k=n}^\infty t_k \le 2 t_n$.
    have h_sum_bound : ∀ n ≥ N₁, ∑' k : ℕ, t (n + k) ≤ 2 * t n := by
      intros n hn
      have h_sum_bound_step : ∀ k, t (n + k) ≤ t n * (1 / 2) ^ k := by
        intro k
        induction k with
        | zero => simp
        | succ k ih =>
          rw [Nat.add_succ, h_t_recurrence]
          have h1 := hN₁ (n + k) (by linarith)
          have h2 : 0 < t (n + k) := by positivity
          calc t (n + k) ^ 2 ≤ t (n + k) * (1 / 2) := by nlinarith
            _ ≤ (t n * (1 / 2) ^ k) * (1 / 2) := by nlinarith
            _ = t n * (1 / 2) ^ (k + 1) := by ring
      refine le_trans (Summable.tsum_le_tsum h_sum_bound_step ?_ ?_) ?_
      · exact Summable.of_nonneg_of_le (fun _ => by positivity) (fun k => h_sum_bound_step k) <|
          Summable.mul_left _ <| summable_geometric_two
      · exact Summable.mul_left _ <| summable_geometric_two
      · rw [tsum_mul_left, tsum_geometric_two]
        ring_nf
        norm_num
    exact ⟨Max.max N₀ N₁, fun n hn =>
      le_trans (h_R_bound n (le_trans (le_max_left _ _) hn))
        (h_sum_bound n (le_trans (le_max_right _ _) hn))⟩
/-
If a sequence $b_n$ satisfies the growth conditions and its sum is rational,
we derive a contradiction.
-/
lemma erdos_1051_contradiction
  (b : ℕ → ℕ)
  (h_mono : StrictMono b)
  (h_ge_two : ∀ n, 2 ≤ b n)
  (h_liminf : 1 < Filter.atTop.liminf (fun n ↦ (b n : ℝ) ^ ((1 : ℝ) / 2 ^ n)))
  (h_rat : ∃ p q : ℕ, 0 < q ∧ (∑' n, 1 / ((b n : ℝ) * (b (n + 1) : ℝ))) = p / q) :
  False := by
    -- Let $D$ be a number such that $1 < D < L$.
    obtain ⟨L, hL_gt_one, hL⟩ : ∃ L, 1 < L ∧
        Filter.Tendsto (fun n ↦ (b n : ℝ) ^ ((1 : ℝ) / 2 ^ n)) Filter.atTop (nhds L) := by
      obtain ⟨p, q, hq, hpq⟩ := h_rat
      apply_rules [Erdos1051_L_exists_gt_one]
    obtain ⟨p, q, hq, h_sum⟩ := h_rat
    have h_P_lower_bound : ∀ D, 1 < D → D < L →
        ∃ N₀, ∀ n ≥ N₀,
          (P_n b (n + 1) : ℝ) ≥ 1 / (2 * q) * D ^ (3 * (2 : ℝ) ^ n) := by
      -- By Lemma 2, $R_n \ge \frac{1}{q P_{n+1}}$.
      have h_R_lower_bound : ∀ n, R_n b n ≥ 1 / (q * (P_n b (n + 1) : ℝ)) := by
        intro n
        have h_R_lower_bound : R_n b n ≥ 1 / (q * (P_n b (n + 1) : ℝ)) := by
          have h_K_lower_bound : K_n_aux b q n ≥ 1 := by
            apply R_n_lower_bound b h_mono h_ge_two p q hq h_sum
          field_simp
          rw [div_le_iff₀] <;> norm_cast
          · convert h_K_lower_bound.le using 1
            ring_nf!
            unfold K_n_aux
            ring_nf!
          · exact Finset.prod_pos fun _ _ => zero_lt_two.trans_le (h_ge_two _)
        exact h_R_lower_bound
      -- By Lemma 3, $R_n \le 2 D^{-3 \cdot 2^n}$ for large $n$.
      intros D hD_gt_one hD_lt_L
      obtain ⟨N₀, hN₀⟩ : ∃ N₀, ∀ n ≥ N₀,
          R_n b n ≤ 2 * D ^ (-3 * (2 : ℝ) ^ n) := by
        exact R_n_upper_bound_D b h_mono h_ge_two L hL D hD_gt_one hD_lt_L
      -- Combining the inequalities from Lemma 2 and Lemma 3, we get:
      -- $1 / (q * P_{n+1}) \le 2 * D ^ (-3 * 2^n)$.
      have h_combined :
          ∀ n ≥ N₀, 1 / (q * (P_n b (n + 1) : ℝ)) ≤
            2 * D ^ (-3 * (2 : ℝ) ^ n) := by
        exact fun n hn => le_trans (h_R_lower_bound n) (hN₀ n hn)
      use N₀
      intro n hn
      specialize h_combined n hn
      rw [div_le_iff₀] at h_combined <;>
        norm_num [Real.rpow_neg (by positivity : 0 ≤ D)] at *
      · field_simp at h_combined ⊢
        exact_mod_cast h_combined
      · exact mul_pos (Nat.cast_pos.mpr hq)
          (Nat.cast_pos.mpr (Finset.prod_pos fun _ _ => by linarith [h_ge_two ‹_›]))
    -- Taking the $2^{-n}$-th root of both sides of the inequality
    -- $P_{n+1} \ge \frac{1}{2q} D^{3 \cdot 2^n}$,
    -- we get $P_{n+1}^{1/2^n} \ge (\frac{1}{2q})^{1/2^n} D^3$.
    have h_P_root_lower_bound : ∀ D, 1 < D → D < L → ∃ N₀, ∀ n ≥ N₀,
        (P_n b (n + 1) : ℝ) ^ ((1 : ℝ) / 2 ^ n) ≥
        (1 / (2 * q)) ^ ((1 : ℝ) / 2 ^ n) * D ^ 3 := by
      intros D hD_gt_one hD_lt_L
      obtain ⟨N₀, hN₀⟩ := h_P_lower_bound D hD_gt_one hD_lt_L
      use N₀
      intro n hn
      have h_root : (P_n b (n + 1) : ℝ) ^ ((1 : ℝ) / 2 ^ n) ≥
          ((1 / (2 * q)) * D ^ (3 * (2 : ℝ) ^ n)) ^ ((1 : ℝ) / 2 ^ n) := by
        exact Real.rpow_le_rpow (by positivity) (hN₀ n hn) (by positivity)
      convert h_root using 1
      rw [Real.mul_rpow (by positivity) (by positivity)]
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      ring_nf
      norm_num [hq.ne']
    -- Taking the limit as $n \to \infty$, we get $L^2 \ge D^3$.
    have h_L_squared_ge_D_cubed : ∀ D, 1 < D → D < L → L^2 ≥ D^3 := by
      -- Taking the limit as $n \to \infty$, we get $L^2 \ge D^3$ by the properties of limits.
      intros D hD_gt_one hD_lt_L
      have h_lim_P_root : Filter.Tendsto
          (fun n => (P_n b (n + 1) : ℝ) ^ ((1 : ℝ) / 2 ^ n))
          Filter.atTop (nhds (L^2)) := by
        have h_P_root_limit : Filter.Tendsto
            (fun n => (P_n b n : ℝ) ^ ((1 : ℝ) / 2 ^ n))
            Filter.atTop (nhds L) := by
          have h_u_limit : Filter.Tendsto
              (fun n => Real.log (P_n b n : ℝ) / (2 ^ n : ℝ))
              Filter.atTop (nhds (Real.log L)) := by
            have := Erdos1051_u_converges b h_mono h_ge_two p q hq h_sum
            -- By definition of $u_n$, we know that $u_n = \frac{\log(P_n)}{2^n}$.
            obtain ⟨Y, hY⟩ := this
            have h_log_P : Filter.Tendsto
                (fun n => Real.log (b n : ℝ) / (2 ^ n : ℝ))
                Filter.atTop (nhds (Real.log L)) := by
              have := hL.log (by positivity)
              exact this.congr fun n => by
                rw [Real.log_rpow (by
                  norm_cast
                  linarith [h_ge_two n])]
                ring
            have h_log_P : Filter.Tendsto (fun n =>
                (Real.log (P_n b (n + 1) : ℝ) -
                  Real.log (P_n b n : ℝ)) / (2 ^ n : ℝ))
                Filter.atTop (nhds (Real.log L)) := by
              convert h_log_P using 2
              norm_num [P_n]
              rw [Finset.prod_range_succ, Real.log_mul
                (Finset.prod_ne_zero_iff.mpr fun _ _ =>
                  Nat.cast_ne_zero.mpr <| by linarith [h_ge_two ‹_›])
                (Nat.cast_ne_zero.mpr <| by linarith [h_ge_two ‹_›]), add_sub_cancel_left]
            have h_log_P : Filter.Tendsto (fun n =>
                (Real.log (P_n b (n + 1) : ℝ) / (2 ^ (n + 1) : ℝ)) -
                (Real.log (P_n b n : ℝ) / (2 ^ n : ℝ)) / 2)
                Filter.atTop (nhds (Real.log L / 2)) := by
              convert h_log_P.div_const 2 using 2
              ring
            have := h_log_P.sub (hY.comp (Filter.tendsto_add_atTop_nat 1) |>
              Filter.Tendsto.sub <| hY.div_const 2)
            norm_num at *
            unfold Erdos1051_u at *
            norm_num at *
            convert hY using 2
            linarith
          convert h_u_limit.exp using 2 <;>
            norm_num [Real.rpow_def_of_pos (show 0 < (P_n b _ : ℝ) from
              Nat.cast_pos.mpr <| Finset.prod_pos fun _ _ => by linarith [h_ge_two ‹_›])]
          · ring_nf
            rw [Real.exp_eq_exp_ℝ]
          · rw [← Real.exp_eq_exp_ℝ, Real.exp_log (by positivity)]
        have h_P_root_limit_shifted : Filter.Tendsto
            (fun n => (P_n b (n + 1) : ℝ) ^ ((1 : ℝ) / 2 ^ (n + 1)))
            Filter.atTop (nhds L) := by
          exact h_P_root_limit.comp (Filter.tendsto_add_atTop_nat 1)
        convert h_P_root_limit_shifted.pow 2 using 2
        ring_nf
        rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (Nat.cast_nonneg _)]
        ring_nf
      have h_lim_P_root_lower_bound : Filter.Tendsto
          (fun n => (1 / (2 * q) : ℝ) ^ ((1 : ℝ) / 2 ^ n) * D ^ 3)
          Filter.atTop (nhds (D ^ 3)) := by
        simpa using Filter.Tendsto.mul
          (tendsto_const_nhds.rpow
            (tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt one_lt_two))
            (by
              norm_num
              positivity))
          tendsto_const_nhds
      exact le_of_tendsto_of_tendsto h_lim_P_root_lower_bound h_lim_P_root
        (Filter.eventually_atTop.mpr <| h_P_root_lower_bound D hD_gt_one hD_lt_L)
    -- Since this holds for all $1 < D < L$, letting $D \to L$ gives
    -- $L^2 \ge L^3$, so $1 \ge L$, contradiction.
    have h_contradiction : L^2 ≥ L^3 := by
      have h_contradiction :
          Filter.Tendsto (fun D : ℝ => D^3) (nhdsWithin L (Set.Iio L)) (nhds (L^3)) := by
        exact Continuous.continuousWithinAt (by continuity)
      exact le_of_tendsto h_contradiction
        (Filter.eventually_of_mem (Ioo_mem_nhdsLT hL_gt_one)
          fun x hx => h_L_squared_ge_D_cubed x hx.1 hx.2)
    nlinarith [sq_pos_of_pos (sub_pos.mpr hL_gt_one)]

/-
Summability of the telescoping series $\sum \frac{1}{(n+1)(n+2)}$.
-/
lemma summable_telescoping_one_div_mul_succ :
    Summable (fun n : ℕ ↦ 1 / ((n + 1 : ℝ) * (n + 2 : ℝ))) := by
  -- We can compare our series with the convergent p-series $\sum_{n=1}^{\infty} \frac{1}{n^2}$.
  have h_comparison : ∀ n : ℕ, (1 / ((n + 1 : ℝ) * (n + 2))) ≤ (1 / (n + 1 : ℝ) ^ 2) := by
    exact fun n => by
      gcongr
      nlinarith
  exact Summable.of_nonneg_of_le (fun n => by positivity) h_comparison
    (by simpa using summable_nat_add_iff 1 |>.2 <| Real.summable_one_div_nat_pow.2 one_lt_two)

/-
Summability of the series.
-/
lemma erdos1051_summable
  (a : ℕ → ℕ)
  (h_mono : StrictMono a)
  (h_pos : ∀ n, 0 < a n) :
  Summable (fun n ↦ 1 / ((a n : ℝ) * (a (n + 1) : ℝ))) := by
    -- Since $a_n \ge n + 1$ and $a_n a_{n+1} \ge (n+1)(n+2)$, we can apply the comparison test.
    have h_comparison : ∀ n, (1 : ℝ) / ((a n) * (a (n + 1))) ≤ 1 / ((n + 1) * (n + 2)) := by
      intro n
      exact one_div_le_one_div_of_le (by positivity) (by
        norm_cast
        nlinarith [h_mono n.lt_succ_self,
          show a n ≥ n + 1 from Nat.recOn n (Nat.succ_le_of_lt (h_pos 0))
            fun n ih => by linarith [h_mono n.lt_succ_self]])
    exact Summable.of_nonneg_of_le (fun n => by positivity) h_comparison
      (by simpa using summable_telescoping_one_div_mul_succ)

/-
If liminf u_n > 1 and k >= 1, then liminf (u_n^k) > 1.
-/
set_option linter.flexible false in
-- The proof unfolds `liminf` and `bddAbove`, then works with the simplified goal.
lemma liminf_rpow_gt_one
  (u : ℕ → ℝ)
  (h_pos : ∀ n, 0 ≤ u n)
  (h_liminf : 1 < Filter.atTop.liminf u)
  (k : ℝ)
  (hk : 1 ≤ k) :
  1 < Filter.atTop.liminf (fun n ↦ (u n) ^ k) := by
    -- Since $\liminf u_n > 1$, there exists $c$ such that $1 < c < \liminf u_n$.
    obtain ⟨c, hc₁, hc₂⟩ : ∃ c, 1 < c ∧ c < Filter.liminf u Filter.atTop := by
      exact exists_between h_liminf
    -- Since $c < \liminf u_n$, there exists $N$ such that for all $n \geq N$, $u_n > c$.
    obtain ⟨N, hN⟩ : ∃ N, ∀ n ≥ N, u n > c := by
      rw [Filter.liminf_eq] at hc₂
      contrapose! hc₂
      exact csSup_le ⟨0, Filter.eventually_atTop.mpr ⟨0,
        fun n hn => by linarith [h_pos n]⟩⟩ fun x hx => by
        rcases Filter.eventually_atTop.mp hx with ⟨N, hN⟩
        rcases hc₂ N with ⟨n, hn₁, hn₂⟩
        linarith [hN n hn₁]
    -- Since $c < \liminf u_n$, we have $\liminf (u_n^k) \geq c^k$.
    have h_liminf_ge : Filter.liminf (fun n => u n ^ k) Filter.atTop ≥ c ^ k := by
      refine le_csSup ?_ ?_
      · by_contra h_contra
        simp_all +decide [Filter.liminf_eq, bddAbove_def]
        obtain ⟨M, hM₁, hM₂⟩ := h_contra
          (SupSet.sSup {a : ℝ | ∃ a_1 : ℕ, ∀ b : ℕ, a_1 ≤ b → a ≤ u b} ^ k + 1)
        obtain ⟨N, hN⟩ := hM₁
        have h_liminf_ge : ∀ b ≥ N, u b ≥ M ^ (1 / k) := fun n hn => by
          have := hN n hn
          have h_sSup_nonneg :
              0 ≤ SupSet.sSup
                {a : ℝ | ∃ a_1 : ℕ, ∀ b : ℕ, a_1 ≤ b → a ≤ u b} :=
            le_trans (by positivity) h_liminf.le
          exact le_trans (Real.rpow_le_rpow
            (by linarith [Real.rpow_nonneg h_sSup_nonneg k]) this (by positivity))
            (by rw [← Real.rpow_mul (h_pos n), mul_one_div_cancel (by positivity), Real.rpow_one])
        have h_liminf_ge' :
            M ^ (1 / k) ≤
              SupSet.sSup
                {a : ℝ | ∃ (a_1 : ℕ), ∀ (b : ℕ), a_1 ≤ b → a ≤ u b} := by
          refine le_csSup ?_ ?_
          · use SupSet.sSup {a : ℝ | ∃ a_1 : ℕ, ∀ b : ℕ, a_1 ≤ b → a ≤ u b}
            rintro x ⟨a_1, ha_1⟩
            refine le_csSup ?_ ⟨a_1, ha_1⟩
            by_contra h
            rw [Real.sSup_of_not_bddAbove h] at *
            linarith
          · exact ⟨N, h_liminf_ge⟩
        have h_liminf_ge'' :
            M ≤
              (SupSet.sSup
                {a : ℝ | ∃ (a_1 : ℕ), ∀ (b : ℕ), a_1 ≤ b → a ≤ u b}) ^ k := by
          have h_sSup_nonneg :
              0 ≤ SupSet.sSup
                {a : ℝ | ∃ a_1 : ℕ, ∀ b : ℕ, a_1 ≤ b → a ≤ u b} :=
            le_trans (by positivity) h_liminf.le
          have h_M_nonneg : 0 ≤ M := by linarith [Real.rpow_nonneg h_sSup_nonneg k]
          refine le_trans ?_ (Real.rpow_le_rpow (Real.rpow_nonneg h_M_nonneg _) h_liminf_ge'
            (by positivity))
          rw [← Real.rpow_mul h_M_nonneg, one_div_mul_cancel (by positivity), Real.rpow_one]
        linarith
      · exact Filter.eventually_atTop.mpr ⟨N, fun n hn => by
          simpa using Real.rpow_le_rpow (by positivity) (le_of_lt (hN n hn)) (by positivity)⟩
    exact lt_of_lt_of_le (Real.one_lt_rpow hc₁ (by positivity)) h_liminf_ge

/-
If liminf u_n > 1, then liminf (u_{n+N})^(2^N) > 1.
-/
lemma erdos_1051_liminf_shift_pow
  (u : ℕ → ℝ)
  (h_pos : ∀ n, 0 ≤ u n)
  (h_liminf : 1 < Filter.atTop.liminf u)
  (N : ℕ) :
  1 < Filter.atTop.liminf (fun n ↦ (u (n + N)) ^ (2 ^ N : ℝ)) := by
    convert liminf_rpow_gt_one _ _ ?_ _ ?_ using 1 <;> norm_num [h_liminf]
    · exact fun n => h_pos _
    · bound

/-
Main theorem: The series $\sum \frac{1}{a_n a_{n+1}}$ is irrational.
-/
theorem erdos_1051_irrational
  (a : ℕ → ℕ)
  (h_mono : StrictMono a)
  (h_pos : ∀ n, 0 < a n)
  (h_liminf : 1 < Filter.atTop.liminf (fun n ↦ (a n : ℝ) ^ ((1 : ℝ) / 2 ^ n))) :
  Irrational (∑' n, 1 / ((a n : ℝ) * (a (n + 1) : ℝ))) := by
    -- Let's choose any $N$ such that for all $n \geq N$, $a_n \geq 2$.
    obtain ⟨N₀, hN₀⟩ : ∃ N₀, ∀ n ≥ N₀, 2 ≤ a n := by
      exact ⟨1, fun n hn => Nat.succ_le_of_lt
        (lt_of_le_of_lt (Nat.succ_le_of_lt (h_pos 0)) (h_mono hn))⟩
    -- Let $b_n = a_{n+N₀}$. Then $b_n$ is strictly increasing and $b_n \geq 2$.
    set b : ℕ → ℕ := fun n => a (n + N₀)
    have h_b_mono : StrictMono b := by
      exact fun m n mn => h_mono <| by simpa using mn
    have h_b_ge_two : ∀ n, 2 ≤ b n := by
      exact fun n => hN₀ _ (Nat.le_add_left _ _)
    have h_b_liminf :
        1 < Filter.liminf (fun n => (b n : ℝ) ^ (1 / 2 ^ n : ℝ)) Filter.atTop := by
      -- Since $\liminf a_n^{1/2^n} > 1$, we have
      -- $\liminf (a_{n+N₀})^{1/2^{n+N₀}} > 1$.
      have h_liminf_shift :
          1 < Filter.liminf (fun n => (a (n + N₀) : ℝ) ^ (1 / 2 ^ (n + N₀) : ℝ))
            Filter.atTop := by
        convert h_liminf using 1
        norm_num [Filter.liminf_eq]
        congr! 3
        exact ⟨fun ⟨N, hN⟩ => ⟨N + N₀, fun n hn => by
            simpa using hN (n - N₀) (Nat.le_sub_of_add_le hn) |>
              le_trans <| by rw [Nat.sub_add_cancel <| by linarith]⟩,
          fun ⟨N, hN⟩ => ⟨N, fun n hn => by
            simpa using hN (n + N₀) (by linarith)⟩⟩
      -- Since $\liminf (a_{n+N₀})^{1/2^{n+N₀}} > 1$, we have
      -- $\liminf (a_{n+N₀})^{1/2^n} > 1$.
      have h_liminf_shift_pow : 1 < Filter.liminf
          (fun n => ((a (n + N₀) : ℝ) ^ (1 / 2 ^ (n + N₀) : ℝ)) ^ (2 ^ N₀ : ℝ))
          Filter.atTop := by
        convert liminf_rpow_gt_one _ _ h_liminf_shift _ _ using 1 <;> norm_num
        · exact fun n => Real.rpow_nonneg (Nat.cast_nonneg _) _
        · exact one_le_pow₀ (by norm_num)
      convert h_liminf_shift_pow using 3
      rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
      ring_nf
      simp +zetaDelta at *
    -- Apply `erdos_1051_contradiction` to $b_n$.
    have h_b_sum_irrational : Irrational (∑' n, 1 / ((b n) * (b (n + 1)) : ℝ)) := by
      exact fun ⟨p, hp⟩ => erdos_1051_contradiction b h_b_mono h_b_ge_two h_b_liminf
        ⟨p.num.natAbs, p.den, Nat.cast_pos.mpr p.pos, by
          simpa [abs_of_nonneg (Rat.num_nonneg.mpr
            (show 0 ≤ p by exact_mod_cast hp ▸ tsum_nonneg fun _ => by positivity)),
            Rat.cast_def] using hp.symm⟩
    have h_sum_split : ∑' n, 1 / ((a n) * (a (n + 1)) : ℝ) =
        (∑ n ∈ Finset.range N₀, 1 / ((a n) * (a (n + 1)) : ℝ)) +
        (∑' n, 1 / ((b n) * (b (n + 1)) : ℝ)) := by
      rw [← Summable.sum_add_tsum_nat_add]
      · congr! 2
        · grind
      · exact erdos1051_summable a h_mono h_pos
    exact h_sum_split ▸ by
      exact fun ⟨x, hx⟩ => h_b_sum_irrational
        ⟨x - ∑ n ∈ Finset.range N₀, 1 / ((a n : ℚ) * (a (n + 1))), by
          push_cast
          linarith⟩

/-
If the sum of the series is rational, then the sum of the shifted series is rational.
-/
lemma erdos_1051_sum_tail_rational
  (a : ℕ → ℕ)
  (h_mono : StrictMono a)
  (h_pos : ∀ n, 0 < a n)
  (h_rat : ∃ p q : ℕ, 0 < q ∧ (∑' n, 1 / ((a n : ℝ) * (a (n + 1) : ℝ))) = p / q)
  (N : ℕ) :
  ∃ p' q' : ℕ, 0 < q' ∧
    (∑' n, 1 / ((a (n + N) : ℝ) * (a (n + N + 1) : ℝ))) = p' / q' := by
    -- Denote the sum of the original series as S and the shifted series as S_shifted.
    obtain ⟨S, hS⟩ : ∃ S : ℚ, ∑' n, 1 / ((a n) * (a (n + 1)) : ℝ) = S := by
      exact ⟨h_rat.choose / h_rat.choose_spec.choose,
        by simpa using h_rat.choose_spec.choose_spec.2⟩
    obtain ⟨S_shifted, hS_shifted⟩ : ∃ S_shifted : ℚ,
        ∑' n, 1 / ((a (n + N)) * (a (n + N + 1)) : ℝ) = S_shifted := by
      have h_sum_eq : ∑' n, 1 / ((a (n + N)) * (a (n + N + 1)) : ℝ) =
          (∑' n, 1 / ((a n) * (a (n + 1)) : ℝ)) -
          (∑ n ∈ Finset.range N, 1 / ((a n) * (a (n + 1)) : ℝ)) := by
        rw [eq_comm, ← Summable.sum_add_tsum_nat_add N]
        · ring
        · exact erdos1051_summable a h_mono h_pos
      exact ⟨S - ∑ n ∈ Finset.range N, (a n * a (n + 1) : ℚ)⁻¹, by
        push_cast
        aesop⟩
    exact ⟨S_shifted.num.natAbs, S_shifted.den, Nat.cast_pos.mpr S_shifted.pos, by
      simpa [abs_of_nonneg (Rat.num_nonneg.mpr
        (show 0 ≤ S_shifted by exact_mod_cast hS_shifted ▸ tsum_nonneg fun _ => by positivity)),
        Rat.cast_def] using hS_shifted⟩

#print axioms erdos_1051_irrational
-- 'Erdos1051.erdos_1051_irrational' depends on axioms: [propext, Classical.choice, Quot.sound]

end

end Erdos1051
