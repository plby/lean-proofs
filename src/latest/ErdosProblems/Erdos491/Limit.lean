/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib

open Filter Topology

namespace Erdos491LimitScratch

/-- A quantitative one-sided Cauchy estimate gives a limit, with the same
pointwise tail estimate.  This is the abstract limit step in Máté's
construction, with `C = 4 * M`. -/
theorem tendsto_of_ge_bound (A : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hA : ∀ k l : ℕ, k ≤ l → |A l - A k| ≤ C / (2 : ℝ) ^ k) :
    ∃ g : ℝ, Tendsto A atTop (𝓝 g) ∧
      ∀ k : ℕ, |A k - g| ≤ C / (2 : ℝ) ^ k := by
  have hzero : Tendsto (fun k : ℕ => C / (2 : ℝ) ^ k) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))
  have hCauchy : CauchySeq A := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    rcases Metric.tendsto_atTop.mp hzero ε hε with ⟨N, hN⟩
    refine ⟨N, fun m hm n hn => ?_⟩
    rcases le_total m n with hmn | hnm
    · rw [Real.dist_eq, abs_sub_comm]
      exact (hA m n hmn).trans_lt (by
        simpa [Real.dist_eq, abs_of_nonneg hC] using hN m hm)
    · rw [Real.dist_eq]
      exact (hA n m hnm).trans_lt (by
        simpa [Real.dist_eq, abs_of_nonneg hC] using hN n hn)
  rcases cauchySeq_tendsto_of_complete hCauchy with ⟨g, hg⟩
  refine ⟨g, hg, fun k => ?_⟩
  have hlim : Tendsto (fun l : ℕ => |A l - A k|) atTop (𝓝 |g - A k|) :=
    (hg.sub tendsto_const_nhds).abs
  rw [abs_sub_comm]
  exact le_of_tendsto hlim <|
    Filter.eventually_atTop.2 ⟨k, fun l hl => hA k l hl⟩

/-- Abstract form of the passage from the sparse exponent grids to all
exponents.  At scale `k`, `v k t` is the nearby admissible grid exponent.
The first hypothesis is the normalized local-oscillation estimate, while the
second is the uniform grid estimate. -/
theorem tendsto_of_approximation_grids (F : ℕ → ℝ) (g : ℝ)
    (v : ℕ → ℕ → ℕ) (e : ℕ → ℝ)
    (he0 : Tendsto e atTop (𝓝 0)) (he : ∀ k, 0 ≤ e k)
    (hlocal : ∀ k, Tendsto (fun t => |F t - F (v k t)|) atTop (𝓝 0))
    (hgrid : ∀ k t, |F (v k t) - g| ≤ e k) :
    Tendsto F atTop (𝓝 g) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  rcases Metric.tendsto_atTop.mp he0 (ε / 2) (by positivity) with ⟨K, hK⟩
  have heK : e K < ε / 2 := by
    simpa [Real.dist_eq, abs_of_nonneg (he K)] using hK K le_rfl
  rcases Metric.tendsto_atTop.mp (hlocal K) (ε / 2) (by positivity) with ⟨N, hN⟩
  refine ⟨N, fun t ht => ?_⟩
  rw [Real.dist_eq]
  calc
    |F t - g| ≤ |F t - F (v K t)| + |F (v K t) - g| := abs_sub_le _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add (by
      simpa [Real.dist_eq] using hN t ht) ((hgrid K t).trans_lt heK)
    _ = ε := by ring

/-- The dyadic limits of a coprime-additive function remain
coprime-additive. -/
theorem coprime_additive_of_dyadic_limits (f g : ℕ → ℝ)
    (hf : ∀ {a b : ℕ}, 0 < a → 0 < b → Nat.Coprime a b →
      f (a * b) = f a + f b)
    (hg : ∀ n : ℕ, 0 < n →
      Tendsto (fun k : ℕ => f (n ^ (2 ^ k)) / (2 : ℝ) ^ k) atTop (𝓝 (g n))) :
    ∀ {a b : ℕ}, 0 < a → 0 < b → Nat.Coprime a b →
      g (a * b) = g a + g b := by
  intro a b ha hb hab
  have hseq : ∀ k : ℕ,
      f ((a * b) ^ (2 ^ k)) / (2 : ℝ) ^ k =
        f (a ^ (2 ^ k)) / (2 : ℝ) ^ k +
          f (b ^ (2 ^ k)) / (2 : ℝ) ^ k := by
    intro k
    rw [mul_pow, hf (pow_pos ha _) (pow_pos hb _) (hab.pow _ _)]
    ring
  have hsum : Tendsto
      (fun k : ℕ => f (a ^ (2 ^ k)) / (2 : ℝ) ^ k +
        f (b ^ (2 ^ k)) / (2 : ℝ) ^ k) atTop (𝓝 (g a + g b)) :=
    (hg a ha).add (hg b hb)
  exact tendsto_nhds_unique (hg (a * b) (mul_pos ha hb))
    (hsum.congr' (Filter.Eventually.of_forall fun k => (hseq k).symm))

/-- If the normalized values along all positive exponents converge, their
limit is homogeneous under positive natural powers. -/
theorem power_homogeneous_of_all_exponent_limits (f g : ℕ → ℝ)
    (hg : ∀ n : ℕ, 0 < n →
      Tendsto (fun t : ℕ => f (n ^ t) / (t : ℝ)) atTop (𝓝 (g n))) :
    ∀ n r : ℕ, 0 < n → 0 < r → g (n ^ r) = (r : ℝ) * g n := by
  intro n r hn hr
  have hmul : Tendsto (fun t : ℕ => r * t) atTop atTop := by
    rw [Filter.tendsto_atTop_atTop]
    intro b
    refine ⟨b, fun a ha => ha.trans ?_⟩
    simpa only [one_mul] using
      Nat.mul_le_mul_right a (Nat.one_le_iff_ne_zero.2 hr.ne')
  have hsub : Tendsto
      (fun t : ℕ => f (n ^ (r * t)) / ((r * t : ℕ) : ℝ)) atTop (𝓝 (g n)) := by
    change Tendsto
      ((fun t : ℕ => f (n ^ t) / (t : ℝ)) ∘ fun t : ℕ => r * t) atTop (𝓝 (g n))
    exact (hg n hn).comp hmul
  have hscaled : Tendsto
      (fun t : ℕ => (r : ℝ) * (f (n ^ (r * t)) / ((r * t : ℕ) : ℝ)))
      atTop (𝓝 ((r : ℝ) * g n)) := tendsto_const_nhds.mul hsub
  have heq : ∀ᶠ t : ℕ in atTop,
      f ((n ^ r) ^ t) / (t : ℝ) =
        (r : ℝ) * (f (n ^ (r * t)) / ((r * t : ℕ) : ℝ)) := by
    filter_upwards [Filter.eventually_atTop.2 ⟨1, fun t ht => ht⟩] with t ht
    rw [pow_mul]
    push_cast
    field_simp [Nat.ne_of_gt ht, hr.ne']
  exact tendsto_nhds_unique (hg (n ^ r) (pow_pos hn r))
    (hscaled.congr' (heq.mono fun _ ht => ht.symm))

/-- Coprime additivity together with homogeneity on positive powers implies
complete additivity on the positive natural numbers. -/
theorem completely_additive_of_coprime_and_powers (g : ℕ → ℝ)
    (hcop : ∀ {a b : ℕ}, 0 < a → 0 < b → Nat.Coprime a b →
      g (a * b) = g a + g b)
    (hpow : ∀ n r : ℕ, 0 < n → 0 < r → g (n ^ r) = (r : ℝ) * g n) :
    ∀ {a b : ℕ}, 0 < a → 0 < b → g (a * b) = g a + g b := by
  have hg_one : g 1 = 0 := by
    have h := hcop (a := 1) (b := 1) (by norm_num) (by norm_num) (by norm_num)
    norm_num at h ⊢
    linarith
  have hprod : ∀ (s : Finset ℕ) (e : ℕ → ℕ),
      (∀ p ∈ s, Nat.Prime p) →
      g (∏ p ∈ s, p ^ e p) = ∑ p ∈ s, g (p ^ e p) := by
    intro s e hs
    induction s using Finset.induction_on with
    | empty => simp [hg_one]
    | @insert p s hp ih =>
        have hpp : Nat.Prime p := hs p (Finset.mem_insert_self p s)
        have hsp : ∀ q ∈ s, Nat.Prime q := fun q hq => hs q (Finset.mem_insert_of_mem hq)
        have hcop_prod : Nat.Coprime (p ^ e p) (∏ q ∈ s, q ^ e q) := by
          rw [Nat.coprime_prod_right_iff]
          intro q hq
          apply Nat.Coprime.pow
          exact (Nat.coprime_primes hpp (hsp q hq)).2 fun hpq => hp (hpq ▸ hq)
        rw [Finset.prod_insert hp, Finset.sum_insert hp,
          hcop (pow_pos hpp.pos _) (Finset.prod_pos fun q hq => pow_pos (hsp q hq).pos _)
            hcop_prod, ih hsp]
  have hformula : ∀ n : ℕ, 0 < n →
      g n = n.factorization.sum (fun p e => (e : ℝ) * g p) := by
    intro n hn
    have hexp : ∀ p ∈ n.primeFactors, 0 < n.factorization p := by
      intro p hp
      have hp' : p ∈ n.factorization.support := by
        simpa only [Nat.support_factorization] using hp
      exact Nat.pos_of_ne_zero (Finsupp.mem_support_iff.1 hp')
    calc
      g n = g (∏ p ∈ n.primeFactors, p ^ n.factorization p) :=
        congrArg g (Nat.prod_primeFactors_pow_factorization hn.ne')
      _ = ∑ p ∈ n.primeFactors, g (p ^ n.factorization p) :=
        hprod n.primeFactors n.factorization
          (fun p hp => Nat.prime_of_mem_primeFactors hp)
      _ = n.factorization.sum (fun p e => (e : ℝ) * g p) := by
        change (∑ p ∈ n.primeFactors, g (p ^ n.factorization p)) =
          ∑ p ∈ n.factorization.support, (n.factorization p : ℝ) * g p
        rw [Nat.support_factorization]
        exact Finset.sum_congr rfl fun p hp =>
          hpow p (n.factorization p) (Nat.prime_of_mem_primeFactors hp).pos (hexp p hp)
  intro a b ha hb
  rw [hformula (a * b) (mul_pos ha hb), hformula a ha, hformula b hb,
    Nat.factorization_mul ha.ne' hb.ne']
  exact Finsupp.sum_add_index' (fun _ => by norm_num) (fun _ _ _ => by push_cast; ring)

end Erdos491LimitScratch
