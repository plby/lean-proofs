/- leanprover/lean4:v4.32.0  mathlib v4.32.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 1095.
https://www.erdosproblems.com/forum/thread/1095

Formalization status:
- Partial

Informal authors:
- E. F. Ecklund Jr.
- Paul Erdős
- J. L. Selfridge

Formal authors:
- Aristotle
- Boris Alexeev

URLs:
- https://www.erdosproblems.com/forum/thread/1095#post-2605
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos1095.md
- https://github.com/plby/lean-proofs/blob/main/src/v4.24.0/ErdosProblems/Erdos1095b.lean
- https://github.com/google-deepmind/formal-conjectures/blob/3d6dc14ba924f82ab5200288f6c6ee1be1326a2d/FormalConjectures/ErdosProblems/1095.lean
-/
import Mathlib

namespace Erdos1095b

open Filter Real

open scoped Asymptotics Topology

def Good (k n : ℕ) : Prop :=
  k + 1 < n ∧ k < Nat.minFac (Nat.choose n k)

open Classical in
noncomputable def g (k : ℕ) : ℕ :=
  if h : ∃ n : ℕ, Good k n then Nat.find h else 0

/-
For any $k \ge 2$, there exists $n$ such that $Good(k, n)$ and $n$ is bounded by $(k+1)!^3$.
-/
lemma exists_good_bound (k : ℕ) (hk : 2 ≤ k) : ∃ n, Good k n ∧ n ≤ (Nat.factorial (k + 1)) ^ 3 := by
  -- Let $M = \prod_{p \le k} p^{\lfloor \log_p k \rfloor + 1}$.
  set M := ∏ p ∈ Finset.filter Nat.Prime (Finset.Icc 2 k), p ^ ((Nat.log p k) + 1)
  -- We claim that $M \leq (k+1)!^2$.
  have hM_le : M ≤ (Nat.factorial (k + 1))^2 := by
    have h_prod_le :
        M ≤ (∏ p ∈ Finset.filter Nat.Prime (Finset.Icc 2 k), p ^ Nat.log p k) *
          (∏ p ∈ Finset.filter Nat.Prime (Finset.Icc 2 k), p) := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_le_prod' fun p hp => by
        ring_nf
        norm_num
    -- We'll use that $\prod_{p \le k} p^{\log_p k} \le k!$ and
    -- $\prod_{p \le k} p \le k!$.
    have h_prod_log_le_factorial :
        (∏ p ∈ Finset.filter Nat.Prime (Finset.Icc 2 k), p ^ Nat.log p k) ≤
          Nat.factorial k := by
      have h_prod_le_factorial :
          (∏ p ∈ Finset.filter Nat.Prime (Finset.Icc 2 k), p ^ Nat.log p k) ∣
            Nat.factorial k := by
        have h_prod_le_factorial :
            (∏ p ∈ Finset.filter Nat.Prime (Finset.Icc 2 k), p ^ Nat.log p k) ∣
              (∏ p ∈ Finset.Icc 2 k, p ^ Nat.factorization (Nat.factorial k) p) := by
          rw [← Finset.prod_subset
            (Finset.filter_subset (fun p => Nat.Prime p) (Finset.Icc 2 k))]
          · refine Finset.prod_dvd_prod_of_dvd _ _ fun p hp => pow_dvd_pow _ ?_
            have h_exp :
                Nat.factorization (Nat.factorial k) p =
                  ∑ i ∈ Finset.Ico 1 (Nat.log p k + 1), (k / p ^ i) := by
              rw [ Nat.factorization_def ]
              · haveI := Fact.mk (Finset.mem_filter.mp hp |>.2)
                rw [padicValNat_factorial]
                aesop
              · exact Finset.mem_filter.mp hp |>.2
            rw [ h_exp ]
            exact le_trans
              (by norm_num)
              (Finset.sum_le_sum fun i hi =>
                Nat.div_pos
                  (show k ≥ p ^ i from
                    Nat.pow_le_of_le_log
                      (by linarith)
                      (by linarith [Finset.mem_Ico.mp hi]))
                  (pow_pos (Nat.Prime.pos (Finset.mem_filter.mp hp |>.2)) _))
          · aesop
        refine dvd_trans h_prod_le_factorial ?_
        conv_rhs => rw [ ← Nat.prod_factorization_pow_eq_self ( Nat.factorial_ne_zero k ) ]
        rw [ Finsupp.prod_of_support_subset ] <;> norm_num
        exact fun p hp =>
          Finset.mem_Icc.mpr
            ⟨ Nat.Prime.two_le (Nat.prime_of_mem_primeFactors hp),
              Nat.le_of_not_lt fun h => by
                have := Nat.dvd_of_mem_primeFactors hp
                exact absurd (Nat.dvd_trans (Nat.dvd_refl _) this) (by
                  rw [Nat.Prime.dvd_factorial (Nat.prime_of_mem_primeFactors hp)]
                  linarith) ⟩
      exact Nat.le_of_dvd ( Nat.factorial_pos _ ) h_prod_le_factorial
    -- We'll use that $\prod_{p \le k} p \le k!$.
    have h_prod_le_factorial :
        (∏ p ∈ Finset.filter Nat.Prime (Finset.Icc 2 k), p) ≤ Nat.factorial k := by
      have h_prod_le_factorial :
          (∏ p ∈ Finset.filter Nat.Prime (Finset.Icc 2 k), p) ≤
            (∏ p ∈ Finset.Icc 2 k, p) := by
        exact Finset.prod_le_prod_of_subset_of_one_le' (Finset.filter_subset _ _) fun _ _ _ => by
          linarith [Finset.mem_Icc.mp ‹_›]
      convert h_prod_le_factorial using 1
      exact Nat.recOn k (by norm_num) fun n ih => by
        cases n <;>
          simp_all +decide [Nat.factorial_succ, Finset.prod_Ioc_succ_top,
            (Nat.succ_eq_succ ▸ Finset.Icc_succ_left_eq_Ioc)]
        linarith
    exact h_prod_le.trans (by
      rw [sq]
      exact Nat.mul_le_mul
        (h_prod_log_le_factorial.trans (Nat.factorial_le (Nat.le_succ _)))
        (h_prod_le_factorial.trans (Nat.factorial_le (Nat.le_succ _))))
  -- Let $n = M + k$. Since $k \ge 2$, $M \ge 2$, so $n > k+1$.
  use M + k
  -- We claim that for all $p \le k$, $p \nmid \binom{M+k}{k}$.
  have h_not_div :
      ∀ p ∈ Finset.filter Nat.Prime (Finset.Icc 2 k), ¬(p ∣ Nat.choose (M + k) k) := by
    -- For any $i \in \{1, \dots, k\}$, $v_p(M+i) = v_p(i)$ because
    -- $v_p(M) \ge \lfloor \log_p k \rfloor + 1 > \log_p k \ge v_p(k) \ge v_p(i)$.
    have h_vp :
        ∀ p ∈ Finset.filter Nat.Prime (Finset.Icc 2 k), ∀ i ∈ Finset.Icc 1 k,
          Nat.factorization (M + i) p = Nat.factorization i p := by
      intros p hp i hi
      have h_div : p ^ (Nat.factorization i p + 1) ∣ M := by
        refine dvd_trans ?_ ( Finset.dvd_prod_of_mem _ hp )
        exact pow_dvd_pow _ (Nat.succ_le_succ
          (Nat.le_log_of_pow_le
            (Nat.Prime.one_lt (Finset.mem_filter.mp hp |>.2))
            (Nat.le_trans
              (Nat.le_of_dvd
                (by linarith [Finset.mem_Icc.mp hi])
                (Nat.ordProj_dvd _ _))
              (by linarith [Finset.mem_Icc.mp hi]))))
      -- Since $p^{v_p(i) + 1} \mid M$, we have $v_p(M + i) = v_p(i)$.
      have h_vp_eq : Nat.factorization (M + i) p = Nat.factorization i p := by
        have h_div : p ^ (Nat.factorization i p) ∣ M + i := by
          exact dvd_add
            (dvd_trans (pow_dvd_pow _ (Nat.le_succ _)) h_div)
            (Nat.ordProj_dvd _ _)
        have h_not_div : ¬(p ^ (Nat.factorization i p + 1) ∣ M + i) := by
          rw [Nat.dvd_add_right ‹_›]
          exact Nat.pow_succ_factorization_not_dvd
            (by linarith [Finset.mem_Icc.mp hi]) (by aesop)
        exact le_antisymm
          (Nat.le_of_not_lt fun h =>
            h_not_div <| dvd_trans (pow_dvd_pow _ h) <| Nat.ordProj_dvd _ _)
          (Nat.le_of_not_lt fun h =>
            absurd
              (dvd_trans (pow_dvd_pow _ h) h_div)
              (Nat.pow_succ_factorization_not_dvd
                (by
                  linarith [Finset.mem_Icc.mp hi,
                    show M > 0 from
                      Finset.prod_pos fun x hx =>
                        pow_pos (Nat.Prime.pos <| Finset.mem_filter.mp hx |>.2) _])
                (Finset.mem_filter.mp hp |>.2)))
      exact h_vp_eq
    -- Thus $v_p(\prod (M+i)) = \sum v_p(i) = v_p(k!)$.
    have h_vp_prod :
        ∀ p ∈ Finset.filter Nat.Prime (Finset.Icc 2 k),
          Nat.factorization (∏ i ∈ Finset.Icc 1 k, (M + i)) p =
            Nat.factorization (Nat.factorial k) p := by
      intros p hp
      have h_vp_prod_step :
          Nat.factorization (∏ i ∈ Finset.Icc 1 k, (M + i)) p =
            ∑ i ∈ Finset.Icc 1 k, Nat.factorization (M + i) p := by
        rw [Nat.factorization_prod <| fun i hi => by
          exact ne_of_gt <| add_pos_of_nonneg_of_pos (Nat.zero_le _) <|
            Finset.mem_Icc.mp hi |>.1]
        rw [ Finset.sum_apply' ]
      rw [ h_vp_prod_step, Finset.sum_congr rfl fun i hi => h_vp p hp i hi ]
      have h_vp_prod_step :
          ∀ n : ℕ, ∑ i ∈ Finset.Icc 1 n, Nat.factorization i p =
            Nat.factorization (Nat.factorial n) p := by
        intro n
        induction n
        · simp
        · rw [Nat.factorial_succ, Nat.factorization_mul] <;>
            first
            | positivity
            | simp_all +decide [Finset.sum_Ioc_succ_top,
                (Nat.succ_eq_succ ▸ Finset.Icc_succ_left_eq_Ioc), add_comm]
      apply h_vp_prod_step
    -- Thus $v_p(\binom{M+k}{k}) = v_p(\prod (M+i)) - v_p(k!) = 0$.
    have h_vp_binom :
        ∀ p ∈ Finset.filter Nat.Prime (Finset.Icc 2 k),
          Nat.factorization (Nat.choose (M + k) k) p = 0 := by
      -- Using the identity
      -- $\binom{M+k}{k} = \frac{(M+k)(M+k-1)\cdots(M+1)}{k!}$,
      -- we can rewrite the factorization.
      have h_binom_identity :
          Nat.choose (M + k) k * Nat.factorial k =
            ∏ i ∈ Finset.Icc 1 k, (M + i) := by
        rw [ mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose ]
        erw [ Finset.prod_Ico_eq_prod_range, Nat.descFactorial_eq_prod_range ]
        rw [ ← Finset.prod_range_reflect ]
        exact Finset.prod_congr rfl fun x hx => by
          cases k <;> norm_num at *
          omega
      intro p hp
      replace h_binom_identity := congr_arg (fun x => x.factorization p) h_binom_identity
      simp_all only [Finset.mem_filter, Finset.mem_Icc, and_imp]
      rw [ Nat.factorization_mul ] at h_binom_identity
      · simp_all +decide
      · exact Nat.ne_of_gt <| Nat.choose_pos <| by
          linarith [show M > 0 from
            Finset.prod_pos fun p hp => pow_pos (Nat.Prime.pos <| by aesop) _]
      · exact Nat.factorial_ne_zero k
    exact fun p hp hp_dvd => by
      have hfactor_zero := h_vp_binom p hp
      rcases (Nat.factorization_eq_zero_iff (Nat.choose (M + k) k) p).mp hfactor_zero with
        hnot_prime | hnot_dvd | hchoose_zero
      · exact hnot_prime (Finset.mem_filter.mp hp |>.2)
      · exact hnot_dvd hp_dvd
      · exact (Nat.ne_of_gt (Nat.choose_pos (by
          linarith [show M > 0 from
            Finset.prod_pos fun p hp => pow_pos (Nat.Prime.pos (by aesop)) _]))) hchoose_zero
  -- Thus $\binom{n}{k}$ has no prime factors $\le k$.
  have h_min_fac : Nat.minFac (Nat.choose (M + k) k) > k := by
    refine lt_of_not_ge fun h => h_not_div ?_ ?_ ?_
    · exact Nat.minFac ( Nat.choose ( M + k ) k )
    · simp +zetaDelta only [Finset.mem_filter, Finset.mem_Icc, Nat.minFac_prime_iff, ne_eq] at *
      refine ⟨ ⟨ Nat.Prime.two_le ( Nat.minFac_prime ?_ ), h ⟩, ?_ ⟩
      · rcases k with ( _ | _ | k ) <;> simp_all +decide [ Nat.choose ]
        linarith [
          Nat.choose_pos (show k ≤
              (∏ p ∈ Finset.Icc 2 (k + 1 + 1) with Nat.Prime p,
                p ^ (Nat.log p (k + 1 + 1) + 1)) + k from by
            linarith [show
                (∏ p ∈ Finset.Icc 2 (k + 1 + 1) with Nat.Prime p,
                  p ^ (Nat.log p (k + 1 + 1) + 1)) ≥ 1 from
              Nat.one_le_iff_ne_zero.mpr <|
                Finset.prod_ne_zero_iff.mpr fun p hp =>
                  pow_ne_zero _ <| Nat.ne_of_gt <| Nat.Prime.pos <| by aesop]),
          Nat.choose_pos (show k + 1 ≤
              (∏ p ∈ Finset.Icc 2 (k + 1 + 1) with Nat.Prime p,
                p ^ (Nat.log p (k + 1 + 1) + 1)) + k from by
            linarith [show
                (∏ p ∈ Finset.Icc 2 (k + 1 + 1) with Nat.Prime p,
                  p ^ (Nat.log p (k + 1 + 1) + 1)) ≥ 1 from
              Nat.one_le_iff_ne_zero.mpr <|
                Finset.prod_ne_zero_iff.mpr fun p hp =>
                  pow_ne_zero _ <| Nat.ne_of_gt <| Nat.Prime.pos <| by aesop])]
      · rcases k with ( _ | _ | k ) <;> simp_all +arith +decide [ Nat.choose ]
        linarith [
          Nat.choose_pos (show k ≤
              k + (∏ x ∈ Finset.Icc 2 (k + 2) with Nat.Prime x,
                x ^ (Nat.log x (k + 2) + 1)) from
            Nat.le_add_right _ _),
          Nat.choose_pos (show k + 1 ≤
              k + (∏ x ∈ Finset.Icc 2 (k + 2) with Nat.Prime x,
                x ^ (Nat.log x (k + 2) + 1)) from
            Nat.succ_le_of_lt (Nat.lt_add_of_pos_right
              (Finset.prod_pos fun p hp => pow_pos (Nat.Prime.pos (by aesop)) _)))]
    · exact Nat.minFac_dvd _
  refine ⟨ ⟨ ?_, h_min_fac ⟩, ?_ ⟩
  · have hM_pos : 0 < M := by
      exact Finset.prod_pos fun p hp =>
        pow_pos (Nat.Prime.pos (Finset.mem_filter.mp hp |>.2)) _
    have htwo_mem : 2 ∈ Finset.filter Nat.Prime (Finset.Icc 2 k) := by
      exact Finset.mem_filter.mpr ⟨ Finset.mem_Icc.mpr ⟨ by norm_num, hk ⟩, Nat.prime_two ⟩
    have htwo_le_pow : 2 ≤ 2 ^ (Nat.log 2 k + 1) := by
      exact le_self_pow (by norm_num) (Nat.succ_ne_zero _)
    have hpow_le_M : 2 ^ (Nat.log 2 k + 1) ≤ M := by
      exact Nat.le_of_dvd hM_pos (Finset.dvd_prod_of_mem _ htwo_mem)
    omega
  · nlinarith [ Nat.self_le_factorial ( k + 1 ), pow_succ ( Nat.factorial ( k + 1 ) ) 2 ]

/-
https://www.erdosproblems.com/1095 used to say that Ecklund, Erdős,
and Selfridge conjectured $g(k)\leq \exp(k^{1+o(1)})$.

(But it seems they actually proved $g(k)\leq \exp(k*(1+o(1)))$.)

[EES74](https://mathscinet.ams.org/mathscinet/relay-station?mr=1199990)
-/
theorem erdos_1095_weaker_upper_bound :
    ∃ f : ℕ → ℝ, Tendsto f atTop (𝓝 0) ∧ ∀ k, 2 ≤ k → g k ≤ exp (k ^ (1 + f k)) := by
  refine ⟨ ?_, ?_, fun k hk => ?_ ⟩
  · refine fun k =>
      max 0 (Real.log (Real.log (g k)) / Real.log k - 1 + 3 / Real.log k)
  · -- We'll use the fact that $g(k) \leq (k+1)!^3$ to bound
    -- $\log \log g(k)$.
    have h_log_log_bound :
        ∀ k ≥ 2,
          Real.log (Real.log (g k)) ≤
            Real.log 3 + Real.log (k + 1) + Real.log (Real.log (k + 1)) := by
      -- Using the bound $g(k) \leq (k+1)!^3$, we get
      -- $\log g(k) \leq 3 \log ((k+1)!)$.
      have h_log_bound :
          ∀ k ≥ 2, Real.log (g k) ≤ 3 * Real.log (Nat.factorial (k + 1)) := by
        have h_log_bound : ∀ k ≥ 2, g k ≤ (Nat.factorial (k + 1)) ^ 3 := by
          intro k hk
          -- By definition of $g$, we know that $g(k) \leq (k+1)!^3$.
          obtain ⟨n, hn_good, hn_le⟩ :
              ∃ n, Good k n ∧ n ≤ (Nat.factorial (k + 1)) ^ 3 :=
            exists_good_bound k hk
          unfold g
          aesop
        intros k hk
        have h_log_bound : Real.log (g k) ≤ Real.log ((Nat.factorial (k + 1)) ^ 3) := by
          by_cases h : g k = 0
          · norm_num [ h ]
            positivity
          · exact Real.log_le_log ( by positivity ) ( mod_cast h_log_bound k hk )
        aesop
      -- Using the bound $3 \log ((k+1)!) \leq 3 (k+1) \log (k+1)$,
      -- we get $\log \log g(k) \leq \log (3 (k+1) \log (k+1))$.
      have h_log_log_bound :
          ∀ k ≥ 2,
            Real.log (Real.log (g k)) ≤
              Real.log (3 * (k + 1) * Real.log (k + 1)) := by
        intros k hk
        have h_log_log_bound :
            Real.log (Real.log (g k)) ≤
              Real.log (3 * Real.log (Nat.factorial (k + 1))) := by
          by_cases h : Real.log ( g k ) = 0
          · norm_num [ h ]
            exact Real.log_nonneg (by
              nlinarith [
                show (k : ℝ) ≥ 2 by norm_cast,
                Real.log_two_gt_d9,
                Real.log_le_log (by positivity) (show (k + 1 : ℝ) ≥ 2 by
                  norm_cast
                  linarith),
                Real.log_le_log (by positivity)
                  (show (k + 1 : ℝ) ≤ (k + 1).factorial by
                    exact mod_cast Nat.self_le_factorial _)])
          · exact Real.log_le_log
              (lt_of_le_of_ne
                (Real.log_nonneg <| mod_cast Nat.one_le_iff_ne_zero.mpr <| by aesop)
                (Ne.symm h))
              (h_log_bound k hk)
        refine le_trans h_log_log_bound <| Real.log_le_log ?_ ?_
        · exact mul_pos zero_lt_three
            (Real.log_pos <| mod_cast by linarith [Nat.self_le_factorial (k + 1)])
        · rw [ mul_assoc ]
          exact mul_le_mul_of_nonneg_left
            (by
              rw [← Real.log_rpow (by positivity)]
              exact Real.log_le_log (by positivity) (mod_cast
                Nat.recOn k (by norm_num) fun n ihn => by
                  rw [Nat.factorial_succ, pow_succ']
                  exact le_trans (Nat.mul_le_mul_left _ ihn) (by
                    gcongr
                    linarith)))
            zero_le_three
      exact fun k hk =>
        le_trans (h_log_log_bound k hk) (by
          rw [Real.log_mul (by positivity)
              (by exact ne_of_gt (Real.log_pos (by norm_cast; linarith))),
            Real.log_mul (by positivity) (by positivity)])
    -- Using the bound on $\log \log g(k)$, we can show that
    -- $\frac{\log \log g(k)}{\log k} - 1 + \frac{3}{\log k}$ tends to $0$.
    have h_frac_log_log_bound :
        Filter.Tendsto
          (fun k : ℕ =>
            (Real.log 3 + Real.log (k + 1) + Real.log (Real.log (k + 1))) /
              Real.log k - 1 + 3 / Real.log k)
          Filter.atTop (nhds 0) := by
      -- We'll use the fact that $\frac{\log (k + 1)}{\log k}$ tends to $1$
      -- as $k$ tends to infinity.
      have h_log_ratio :
          Filter.Tendsto (fun k : ℕ => Real.log (k + 1) / Real.log k)
            Filter.atTop (nhds 1) := by
        -- We can use the fact that
        -- $\log(k+1) = \log k + \log\left(1 + \frac{1}{k}\right)$
        -- to rewrite the limit expression.
        suffices h_log_rewrite :
            Filter.Tendsto
              (fun k : ℕ => (Real.log k + Real.log (1 + 1 / (k : ℝ))) / Real.log k)
              Filter.atTop (nhds 1) by
          refine h_log_rewrite.congr' (by
            filter_upwards [Filter.eventually_gt_atTop 0] with k hk using by
              rw [← Real.log_mul (by positivity) (by positivity), mul_add,
                mul_one_div_cancel (by positivity), mul_one])
        ring_nf
        exact le_trans
          (Filter.Tendsto.add
            (tendsto_const_nhds.congr' (by
              filter_upwards [Filter.eventually_gt_atTop 1] with x hx
              rw [mul_inv_cancel₀ (ne_of_gt (Real.log_pos (mod_cast hx)))]))
            (Filter.Tendsto.mul
              (Filter.Tendsto.log
                (tendsto_const_nhds.add tendsto_inv_atTop_nhds_zero_nat)
                (by norm_num))
              (tendsto_inv_atTop_zero.comp
                (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))))
          (by norm_num)
      -- We'll use the fact that $\frac{\log \log (k + 1)}{\log k}$ tends to $0$
      -- as $k$ tends to infinity.
      have h_log_log_ratio :
          Filter.Tendsto (fun k : ℕ => Real.log (Real.log (k + 1)) / Real.log k)
            Filter.atTop (nhds 0) := by
        -- We can use the fact that $\frac{\log \log (k + 1)}{\log k}$ tends
        -- to $0$ as $k$ tends to infinity.
        have h_log_log_ratio :
            Filter.Tendsto
              (fun k : ℕ => Real.log (Real.log (k + 1)) / Real.log (k + 1))
              Filter.atTop (nhds 0) := by
          have h_log_log_ratio :
              Filter.Tendsto (fun x : ℝ => Real.log x / x) Filter.atTop (nhds 0) := by
            -- Let $y = \frac{1}{x}$, so we can rewrite the limit as
            -- $\lim_{y \to 0^+} y \log(1/y)$.
            suffices h_log_recip :
                Filter.Tendsto (fun y : ℝ => y * Real.log (1 / y))
                  (Filter.map (fun x => 1 / x) Filter.atTop) (nhds 0) by
              exact h_log_recip.congr ( by simp +contextual [ div_eq_inv_mul ] )
            norm_num
            exact tendsto_nhdsWithin_of_tendsto_nhds
              (by
                have h := Real.continuous_mul_log.tendsto 0
                simpa using h.neg)
          exact h_log_log_ratio.comp
            (Real.tendsto_log_atTop.comp <|
              Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
        have := h_log_log_ratio.mul h_log_ratio
        simpa using this.congr' (by
          filter_upwards [Filter.eventually_gt_atTop 1] with x hx using by
            rw [div_mul_div_cancel₀ (ne_of_gt <| Real.log_pos <| by
              norm_cast
              linarith)])
      simpa +decide [ add_div ] using
        (Filter.Tendsto.add
          (Filter.Tendsto.sub
            (Filter.Tendsto.add
              (Filter.Tendsto.add
                ((tendsto_const_nhds (x := Real.log 3)).div_atTop <|
                  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
                h_log_ratio)
              h_log_log_ratio)
            (tendsto_const_nhds (x := (1 : ℝ))))
          ((tendsto_const_nhds (x := (3 : ℝ))).div_atTop <|
            Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))
    refine squeeze_zero_norm' ?_ h_frac_log_log_bound
    filter_upwards [ Filter.eventually_ge_atTop 2 ] with k hk
    rw [ Real.norm_of_nonneg ( by positivity ) ]
    exact max_le
      (by
        linarith [show
            0 ≤
              (Real.log 3 + Real.log (k + 1) + Real.log (Real.log (k + 1))) /
                  Real.log k - 1 + 3 / Real.log k from
          add_nonneg
            (sub_nonneg_of_le <| by
              rw [le_div_iff₀ <| Real.log_pos <| by norm_cast]
              nlinarith [
                Real.log_pos <| show (k : ℝ) > 1 by norm_cast,
                Real.log_le_log (by positivity) <| show (k : ℝ) + 1 ≥ k by
                  linarith,
                Real.log_pos <| show (3 : ℝ) > 1 by norm_num,
                Real.log_pos <| show (k + 1 : ℝ) > 1 by
                  norm_cast
                  linarith,
                Real.log_pos <| show Real.log (k + 1 : ℝ) > 1 by
                  rw [gt_iff_lt]
                  rw [Real.lt_log_iff_exp_lt <| by positivity]
                  exact Real.exp_one_lt_d9.trans_le <| by
                    norm_num
                    linarith [show (k : ℝ) ≥ 2 by norm_cast]])
            (by positivity)])
      (by
        linarith [
          h_log_log_bound k hk,
          show 0 < Real.log k from Real.log_pos <| by norm_cast,
          div_le_div_of_nonneg_right (h_log_log_bound k hk) <|
            Real.log_nonneg <| show (k : ℝ) ≥ 1 by
              norm_cast
              linarith])
  · -- Since $\limsup \frac{\log \log g(k)}{\log k} \leq 1$, we have
    -- $\frac{\log \log g(k)}{\log k} - 1 + \frac{3}{\log k} \leq \frac{3}{\log k}$.
    have h_log_log_gk :
        Real.log (g k) ≤
          (k : ℝ) ^
            (1 + (Real.log (Real.log (g k)) / Real.log k - 1 + 3 / Real.log k)) := by
      by_cases h : Real.log ( g k ) ≤ 0
      · exact le_trans h ( by positivity )
      · rw [ Real.rpow_def_of_pos ( by positivity ) ]
        rw [show
            Real.log (k : ℝ) *
                (1 + (Real.log (Real.log (g k)) / Real.log k - 1 + 3 / Real.log k)) =
              Real.log (Real.log (g k)) + 3 by
          have hk_gt_one : (1 : ℝ) < (k : ℝ) := by
            norm_cast
          have hklog_ne : Real.log (k : ℝ) ≠ 0 := by
            exact ne_of_gt (Real.log_pos hk_gt_one)
          field_simp [hklog_ne]
          ring ]
        rw [ Real.exp_add, Real.exp_log ( by linarith ) ]
        exact le_mul_of_one_le_right ( by linarith ) ( Real.one_le_exp ( by norm_num ) )
    refine le_trans ( Real.log_le_iff_le_exp ( Nat.cast_pos.mpr ?_ ) |>.1 h_log_log_gk ) ?_
    · unfold g
      split_ifs <;> simp_all +decide [ Good ]
      have := exists_good_bound k hk
      obtain ⟨ n, hn₁, hn₂ ⟩ := this
      have :=
        ‹∀ x : ℕ, k + 1 < x → Nat.minFac (Nat.choose x k) ≤ k› n
          (by linarith [hn₁.1])
      linarith [hn₁.2]
    · exact Real.exp_le_exp.mpr
        (Real.rpow_le_rpow_of_exponent_le (by norm_cast; linarith) (by norm_num))

end Erdos1095b

#print axioms Erdos1095b.erdos_1095_weaker_upper_bound
-- 'Erdos1095b.erdos_1095_weaker_upper_bound' depends on axioms: [propext, choice, Quot.sound]
