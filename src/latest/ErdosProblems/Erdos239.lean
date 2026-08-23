/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 239.
https://www.erdosproblems.com/forum/thread/239

Informal authors:
- Eduard Wirsing

Statement authors:
- Formal Conjectures authors

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos239.md
- https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/239.lean
-/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos239.External.Erdos67.MRRealPrefixCompleteStability
import ErdosProblems.Erdos239.External.Erdos69.HalaszMean

/-!
# Erdős Problem 239

Every real-valued multiplicative function taking only the values `-1` and `1`
has a Cesàro mean.  This is the Erdős--Wintner conjecture, proved by Wirsing
in 1967 and subsequently generalized by Halász.

The statement below intentionally agrees with the statement in the
`google-deepmind/formal-conjectures` repository.  In particular,
multiplicativity is required only for coprime arguments.
-/

open Filter
open scoped BigOperators Topology

namespace Erdos239

/-- The normalized summatory function occurring in Problem 239. -/
noncomputable def meanUpTo (f : ℕ → ℝ) (N : ℕ) : ℝ :=
  (∑ n ∈ Finset.Icc 1 N, f n) / N

/-- The hypotheses in Problem 239, packaged for use by the auxiliary lemmas. -/
def IsSignMultiplicative (f : ℕ → ℝ) : Prop :=
  (∀ n ≥ 1, f n = 1 ∨ f n = -1) ∧
  (∀ m n, m.Coprime n → f (m * n) = f m * f n) ∧
  f 1 = 1

lemma IsSignMultiplicative.sign {f : ℕ → ℝ} (hf : IsSignMultiplicative f)
    {n : ℕ} (hn : 1 ≤ n) : f n = 1 ∨ f n = -1 :=
  hf.1 n hn

lemma IsSignMultiplicative.abs_eq_one {f : ℕ → ℝ}
    (hf : IsSignMultiplicative f) {n : ℕ} (hn : 1 ≤ n) : |f n| = 1 := by
  rcases hf.sign hn with h | h <;> simp [h]

lemma IsSignMultiplicative.norm_eq_one {f : ℕ → ℝ}
    (hf : IsSignMultiplicative f) {n : ℕ} (hn : 1 ≤ n) : ‖f n‖ = 1 := by
  simpa [Real.norm_eq_abs] using hf.abs_eq_one hn

lemma IsSignMultiplicative.mem_Icc {f : ℕ → ℝ}
    (hf : IsSignMultiplicative f) {n : ℕ} (hn : 1 ≤ n) : f n ∈ Set.Icc (-1) 1 := by
  rcases hf.sign hn with h | h <;> simp [h]

lemma IsSignMultiplicative.mul {f : ℕ → ℝ} (hf : IsSignMultiplicative f)
    {m n : ℕ} (hmn : m.Coprime n) : f (m * n) = f m * f n :=
  hf.2.1 m n hmn

lemma IsSignMultiplicative.one {f : ℕ → ℝ} (hf : IsSignMultiplicative f) :
    f 1 = 1 :=
  hf.2.2

/-- Prime-factorization formula for a sign-valued multiplicative function. -/
lemma IsSignMultiplicative.eq_factorization_prod {f : ℕ → ℝ}
    (hf : IsSignMultiplicative f) {n : ℕ} (hn : n ≠ 0) :
    f n = n.factorization.prod fun p k => f (p ^ k) := by
  exact Nat.multiplicative_factorization f (fun m n hmn => hf.mul hmn) hf.one hn

/-! ## Reduction to complete multiplicativity

The value of a multiplicative function at a prime power need not be the
corresponding power of its value at the prime.  We first replace `f` by the
completely multiplicative function with the same prime values.  The
difference will later be recovered by an absolutely summable convolution
supported on squarefull integers.
-/

/-- The completely multiplicative function determined by the prime values
of `f`.  Its value at zero is immaterial and is set to zero. -/
noncomputable def completeCompanion (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else n.factorization.prod fun p e => f p ^ e

@[simp] lemma completeCompanion_zero (f : ℕ → ℝ) : completeCompanion f 0 = 0 := by
  simp [completeCompanion]

@[simp] lemma completeCompanion_one (f : ℕ → ℝ) : completeCompanion f 1 = 1 := by
  simp [completeCompanion]

lemma completeCompanion_mul (f : ℕ → ℝ) {m n : ℕ}
    (hm : m ≠ 0) (hn : n ≠ 0) :
    completeCompanion f (m * n) = completeCompanion f m * completeCompanion f n := by
  simp only [completeCompanion, mul_eq_zero, hm, hn, or_self, ↓reduceIte]
  rw [Nat.factorization_mul hm hn]
  exact Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)

@[simp] lemma completeCompanion_prime (f : ℕ → ℝ) {p : ℕ} (hp : p.Prime) :
    completeCompanion f p = f p := by
  simp [completeCompanion, hp.ne_zero, hp.factorization]

lemma completeCompanion_abs_eq_one {f : ℕ → ℝ}
    (hf : IsSignMultiplicative f) {n : ℕ} (hn : 0 < n) :
    |completeCompanion f n| = 1 := by
  rw [completeCompanion, if_neg hn.ne']
  rw [← Real.norm_eq_abs, Finsupp.prod, norm_prod]
  apply Finset.prod_eq_one
  intro p hp
  rw [norm_pow, hf.norm_eq_one]
  · simp
  · exact (Nat.prime_of_mem_primeFactors hp).one_le

lemma completeCompanion_isSignMultiplicative {f : ℕ → ℝ}
    (hf : IsSignMultiplicative f) : IsSignMultiplicative (completeCompanion f) := by
  refine ⟨?_, ?_, completeCompanion_one f⟩
  · intro n hn
    have habs := completeCompanion_abs_eq_one hf (by omega : 0 < n)
    rcases le_total 0 (completeCompanion f n) with hnonneg | hnonpos
    · left
      simpa [abs_of_nonneg hnonneg] using habs
    · right
      have := habs
      rw [abs_of_nonpos hnonpos] at this
      linarith
  · intro m n hmn
    by_cases hm : m = 0
    · subst m
      simp
    by_cases hn : n = 0
    · subst n
      simp
    exact completeCompanion_mul f hm hn

/-- The reciprocal mass of primes on which a sign function is negative. -/
noncomputable def badPrimeReciprocal (f : ℕ → ℝ) (p : ℕ) : ℝ :=
  if p.Prime ∧ f p = -1 then (p : ℝ)⁻¹ else 0

/-- Complex form consumed by the already formalized real-prefix stability
theorem. -/
noncomputable def companionComplex (f : ℕ → ℝ) (n : ℕ) : ℂ :=
  (completeCompanion f n : ℂ)

lemma companionComplex_isCompletelyMultiplicative {f : ℕ → ℝ} :
    Erdos67.IsCompletelyMultiplicativeOnPositive (companionComplex f) := by
  refine ⟨by simp [companionComplex], ?_⟩
  intro m n hm hn
  simp only [companionComplex, completeCompanion_mul f hm.ne' hn.ne', Complex.ofReal_mul]

lemma companionComplex_isMultiplicative {f : ℕ → ℝ} :
    Erdos67.IsMultiplicativeOnPositiveNat (companionComplex f) :=
  companionComplex_isCompletelyMultiplicative.isMultiplicativeOnPositiveNat

lemma companionComplex_real (f : ℕ → ℝ) (n : ℕ) (_hn : 0 < n) :
    (starRingEnd ℂ) (companionComplex f n) = companionComplex f n := by
  simp [companionComplex]

lemma companionComplex_norm_le_one {f : ℕ → ℝ}
    (hf : IsSignMultiplicative f) (n : ℕ) : ‖companionComplex f n‖ ≤ 1 := by
  by_cases hn : n = 0
  · subst n
    simp [companionComplex]
  · rw [companionComplex, Complex.norm_real, Real.norm_eq_abs,
      completeCompanion_abs_eq_one hf (Nat.pos_of_ne_zero hn)]

lemma positivePrefixMean_companionComplex (f : ℕ → ℝ) (N : ℕ) :
    Erdos67.positivePrefixMean (companionComplex f) N =
      (meanUpTo (completeCompanion f) N : ℂ) := by
  have hsum := Erdos67.sum_Ioc_eq_positivePrefixSum_sub
    (companionComplex f) (Nat.zero_le N)
  have hzero : Erdos67.positivePrefixSum (companionComplex f) 0 = 0 := by
    simp [Erdos67.positivePrefixSum]
  rw [hzero, sub_zero] at hsum
  rw [Erdos67.positivePrefixMean, ← hsum]
  have hsets : Finset.Ioc 0 N = Finset.Icc 1 N := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  rw [hsets]
  simp [meanUpTo, companionComplex]

/-- The quantitative local stability theorem already proved in the
Erdős--67 development, specialized to the real completely multiplicative
companion. -/
theorem eventually_completeCompanion_mean_local_stable {f : ℕ → ℝ}
    (hf : IsSignMultiplicative f) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ X : ℕ in atTop, ∀ Z : ℕ, X ≤ Z → Z ≤ 3 * X →
        |meanUpTo (completeCompanion f) Z -
            meanUpTo (completeCompanion f) X| ≤
          2 * C * (Real.log (X : ℝ)) ^ (-(1 / 1000 : ℝ)) := by
  obtain ⟨C, hC, hstable⟩ :=
    Erdos67.exists_eventually_uniform_real_complete_prefix_stable_one_thousandth
  refine ⟨C, hC, ?_⟩
  filter_upwards [hstable] with X hX
  intro Z hXZ hZX
  obtain ⟨mu, hmu⟩ := hX (companionComplex f)
    companionComplex_isMultiplicative
    companionComplex_isCompletelyMultiplicative
    (companionComplex_real f)
    (companionComplex_norm_le_one hf)
  have hZ := hmu Z hXZ hZX
  have hbase := hmu X le_rfl (by omega)
  have htriangle :
      ‖Erdos67.positivePrefixMean (companionComplex f) Z -
          Erdos67.positivePrefixMean (companionComplex f) X‖ ≤
        2 * C * (Real.log (X : ℝ)) ^ (-(1 / 1000 : ℝ)) := by
    calc
      _ = ‖(Erdos67.positivePrefixMean (companionComplex f) Z - mu) -
          (Erdos67.positivePrefixMean (companionComplex f) X - mu)‖ := by ring_nf
      _ ≤ ‖Erdos67.positivePrefixMean (companionComplex f) Z - mu‖ +
          ‖Erdos67.positivePrefixMean (companionComplex f) X - mu‖ :=
        norm_sub_le _ _
      _ ≤ C * (Real.log (X : ℝ)) ^ (-(1 / 1000 : ℝ)) +
          C * (Real.log (X : ℝ)) ^ (-(1 / 1000 : ℝ)) :=
        add_le_add hZ hbase
      _ = _ := by ring
  rw [positivePrefixMean_companionComplex,
    positivePrefixMean_companionComplex, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs] at htriangle
  exact htriangle

lemma tendsto_log_rpow_neg_one_thousandth_nat :
    Tendsto (fun N : ℕ =>
      (Real.log (N : ℝ)) ^ (-(1 / 1000 : ℝ))) atTop (𝓝 0) := by
  exact (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 1000)).comp
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

lemma tendsto_nat_const_mul_atTop (k : ℕ) (hk : 0 < k) :
    Tendsto (fun N : ℕ => k * N) atTop atTop := by
  rw [tendsto_atTop]
  intro b
  filter_upwards [eventually_ge_atTop b] with N hN
  exact hN.trans (Nat.le_mul_of_pos_left N hk)

/-- Local stability on `[X,3X]` implies that means at any two fixed
positive integer multiples of the same growing parameter become equal. -/
theorem tendsto_completeCompanion_mean_mul_sub_mul {f : ℕ → ℝ}
    (hf : IsSignMultiplicative f) {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun N : ℕ =>
      meanUpTo (completeCompanion f) (a * N) -
        meanUpTo (completeCompanion f) (b * N)) atTop (𝓝 0) := by
  obtain ⟨C, hC, hstable⟩ := eventually_completeCompanion_mean_local_stable hf
  have herr : Tendsto (fun X : ℕ =>
      2 * C * (Real.log (X : ℝ)) ^ (-(1 / 1000 : ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      tendsto_log_rpow_neg_one_thousandth_nat.const_mul (2 * C)
  have hadj : ∀ k : ℕ, 0 < k →
      Tendsto (fun N : ℕ =>
        meanUpTo (completeCompanion f) (k * N) -
          meanUpTo (completeCompanion f) ((k + 1) * N)) atTop (𝓝 0) := by
    intro k hk
    have hstable' := (tendsto_nat_const_mul_atTop k hk).eventually hstable
    have herr' := herr.comp (tendsto_nat_const_mul_atTop k hk)
    rw [Metric.tendsto_atTop] at herr' ⊢
    intro ε hε
    obtain ⟨N₀, hN₀⟩ := herr' ε hε
    obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 hstable'
    refine ⟨max N₀ N₁, fun N hN => ?_⟩
    have hs := hN₁ N (le_max_right _ _ |>.trans hN)
    have hle : k * N ≤ (k + 1) * N := by
      exact Nat.mul_le_mul_right N (Nat.le_succ k)
    have hthree : (k + 1) * N ≤ 3 * (k * N) := by
      simpa only [mul_assoc] using
        Nat.mul_le_mul_right N (show k + 1 ≤ 3 * k by omega)
    have hbound := hs ((k + 1) * N) hle hthree
    rw [Real.dist_eq, sub_zero]
    rw [abs_sub_comm]
    exact lt_of_le_of_lt hbound (by
      simpa only [Function.comp_apply, Real.dist_eq, sub_zero,
        abs_of_nonneg (by positivity :
          0 ≤ 2 * C * (Real.log ((k * N : ℕ) : ℝ)) ^ (-(1 / 1000 : ℝ)))]
        using hN₀ N (le_max_left _ _ |>.trans hN))
  have hordered : ∀ {u v : ℕ}, 0 < u → u ≤ v →
      Tendsto (fun N : ℕ =>
        meanUpTo (completeCompanion f) (u * N) -
          meanUpTo (completeCompanion f) (v * N)) atTop (𝓝 0) := by
    intro u v hu huv
    let d := v - u
    have htel : (fun N : ℕ =>
        meanUpTo (completeCompanion f) (u * N) -
          meanUpTo (completeCompanion f) (v * N)) =
        fun N : ℕ => ∑ j ∈ Finset.range d,
          (meanUpTo (completeCompanion f) ((u + j) * N) -
            meanUpTo (completeCompanion f) ((u + j + 1) * N)) := by
      funext N
      have hsum := Finset.sum_range_sub'
        (fun j : ℕ => meanUpTo (completeCompanion f) ((u + j) * N)) d
      dsimp only [d] at hsum ⊢
      rw [Nat.add_sub_of_le huv] at hsum
      exact hsum.symm
    rw [htel]
    have hsum := tendsto_finset_sum (Finset.range d) (fun j _hj =>
      hadj (u + j) (by omega))
    simpa using hsum
  rcases le_total a b with hab | hba
  · exact hordered ha hab
  · have h := hordered hb hba
    simpa [sub_eq_add_neg, add_comm] using h.neg

/-- The largest multiple of `Q` not exceeding `X`. -/
def floorMultiple (Q X : ℕ) : ℕ := Q * (X / Q)

lemma tendsto_floorMultiple_atTop {Q : ℕ} (hQ : 0 < Q) :
    Tendsto (floorMultiple Q) atTop atTop := by
  rw [tendsto_atTop]
  intro b
  filter_upwards [eventually_ge_atTop (Q * (b + 1))] with X hX
  have hdiv : b + 1 ≤ X / Q := by
    apply (Nat.le_div_iff_mul_le hQ).2
    simpa [Nat.mul_comm] using hX
  calc
    b ≤ X / Q := by omega
    _ ≤ Q * (X / Q) := Nat.le_mul_of_pos_left _ hQ

/-- Local stability also compares an arbitrary endpoint with the preceding
multiple of any fixed positive modulus. -/
theorem tendsto_completeCompanion_mean_sub_floorMultiple {f : ℕ → ℝ}
    (hf : IsSignMultiplicative f) {Q : ℕ} (hQ : 0 < Q) :
    Tendsto (fun X : ℕ =>
      meanUpTo (completeCompanion f) X -
        meanUpTo (completeCompanion f) (floorMultiple Q X))
      atTop (𝓝 0) := by
  obtain ⟨C, hC, hstable⟩ := eventually_completeCompanion_mean_local_stable hf
  have hfloor := tendsto_floorMultiple_atTop hQ
  have hstable' := hfloor.eventually hstable
  have herr : Tendsto (fun X : ℕ =>
      2 * C * (Real.log (floorMultiple Q X : ℝ)) ^ (-(1 / 1000 : ℝ)))
      atTop (𝓝 0) := by
    simpa only [Function.comp_apply, mul_zero] using
      (tendsto_log_rpow_neg_one_thousandth_nat.comp hfloor).const_mul (2 * C)
  rw [Metric.tendsto_atTop] at herr ⊢
  intro ε hε
  obtain ⟨X₀, hX₀⟩ := herr ε hε
  obtain ⟨X₁, hX₁⟩ := eventually_atTop.1 hstable'
  refine ⟨max (max X₀ X₁) Q, fun X hX => ?_⟩
  have hXQ : Q ≤ X := le_max_right _ _ |>.trans hX
  have hquot : 1 ≤ X / Q := (Nat.le_div_iff_mul_le hQ).2 (by simpa using hXQ)
  have hBpos : 0 < floorMultiple Q X := mul_pos hQ (by omega)
  have hBX : floorMultiple Q X ≤ X := by
    exact Nat.mul_div_le X Q
  have hXB3 : X ≤ 3 * floorMultiple Q X := by
    have hlt : X < floorMultiple Q X + Q := by
      have hmod := Nat.mod_add_div X Q
      have hmodlt := Nat.mod_lt X hQ
      dsimp [floorMultiple]
      omega
    have hQB : Q ≤ floorMultiple Q X := by
      dsimp [floorMultiple]
      nlinarith
    omega
  have hs := hX₁ X (le_max_right X₀ X₁ |>.trans
    (le_max_left (max X₀ X₁) Q |>.trans hX))
  have hbound := hs X hBX hXB3
  rw [Real.dist_eq, sub_zero]
  exact lt_of_le_of_lt hbound (by
    simpa only [Real.dist_eq, sub_zero,
      abs_of_nonneg (by positivity :
        0 ≤ 2 * C *
          (Real.log (floorMultiple Q X : ℝ)) ^ (-(1 / 1000 : ℝ)))]
      using hX₀ X (le_max_left X₀ X₁ |>.trans
        (le_max_left (max X₀ X₁) Q |>.trans hX)))

/-! ## Finite prime avoidance and the divergent branch

For a finite set `P` of negative primes, inclusion--exclusion is most
conveniently organized recursively.  Removing multiples of a new prime `p`
replaces an avoidance sum at `X` by the old sum at `X` minus `c(p)` times
the old sum at `X / p`.  At endpoints divisible by the product of `P`, this
recursion has no floor errors.
-/

def Avoids (P : Finset ℕ) (n : ℕ) : Prop :=
  ∀ p ∈ P, ¬p ∣ n

noncomputable def avoidanceFinset (P : Finset ℕ) (X : ℕ) : Finset ℕ :=
  by
    classical
    exact (Finset.Icc 1 X).filter (Avoids P)

noncomputable def avoidanceSum (c : ℕ → ℝ) (P : Finset ℕ) (X : ℕ) : ℝ :=
  ∑ n ∈ avoidanceFinset P X, c n

lemma avoids_empty (n : ℕ) : Avoids ∅ n := by
  simp [Avoids]

lemma avoids_insert {P : Finset ℕ} {p n : ℕ} :
    Avoids (insert p P) n ↔ ¬p ∣ n ∧ Avoids P n := by
  simp [Avoids, and_comm]

lemma avoids_prime_mul_iff {P : Finset ℕ} {p m : ℕ}
    (hp : p.Prime) (hP : ∀ q ∈ P, q.Prime) (hpP : p ∉ P) :
    Avoids P (p * m) ↔ Avoids P m := by
  constructor
  · intro h q hq hqm
    exact h q hq (dvd_mul_of_dvd_right hqm p)
  · intro h q hq hqpm
    rcases (hP q hq).dvd_mul.mp hqpm with hqp | hqm
    · exact hpP ((Nat.prime_dvd_prime_iff_eq (hP q hq) hp).mp hqp ▸ hq)
    · exact h q hq hqm

lemma sum_avoidance_multiples {c : ℕ → ℝ} {P : Finset ℕ} {p X : ℕ}
    (hp : p.Prime) (hP : ∀ q ∈ P, q.Prime) (hpP : p ∉ P) :
    (∑ n ∈ avoidanceFinset P X with p ∣ n, c n) =
      ∑ m ∈ avoidanceFinset P (X / p), c (p * m) := by
  classical
  symm
  apply Finset.sum_bij (fun m _hm => p * m)
  · intro m hm
    simp only [avoidanceFinset, Finset.mem_filter, Finset.mem_Icc] at hm ⊢
    refine ⟨⟨⟨by nlinarith [hp.pos], ?_⟩, ?_⟩, dvd_mul_right p m⟩
    · simpa [Nat.mul_comm] using
        (Nat.le_div_iff_mul_le hp.pos).mp hm.1.2
    · exact (avoids_prime_mul_iff hp hP hpP).2 hm.2
  · intro m₁ hm₁ m₂ hm₂ heq
    exact Nat.eq_of_mul_eq_mul_left hp.pos heq
  · intro n hn
    simp only [avoidanceFinset, Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨m, rfl⟩ := hn.2
    refine ⟨m, ?_, rfl⟩
    simp only [avoidanceFinset, Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨by nlinarith [hn.1.1.1, hp.pos], ?_⟩, ?_⟩
    · exact (Nat.le_div_iff_mul_le hp.pos).2 (by
        simpa [Nat.mul_comm] using hn.1.1.2)
    · exact (avoids_prime_mul_iff hp hP hpP).1 hn.1.2
  · intro m hm
    rfl

lemma avoidanceSum_insert {c : ℕ → ℝ} {P : Finset ℕ} {p X : ℕ}
    (hp : p.Prime) (hP : ∀ q ∈ P, q.Prime) (hpP : p ∉ P)
    (hcomp : ∀ m n : ℕ, 0 < m → 0 < n → c (m * n) = c m * c n) :
    avoidanceSum c (insert p P) X =
      avoidanceSum c P X - c p * avoidanceSum c P (X / p) := by
  classical
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (avoidanceFinset P X) (fun n => p ∣ n) c
  have hnot :
      (avoidanceFinset P X).filter (fun n => ¬p ∣ n) =
        avoidanceFinset (insert p P) X := by
    ext n
    simp [avoidanceFinset, avoids_insert, and_assoc, and_left_comm, and_comm]
  have hdvd := sum_avoidance_multiples (c := c) (X := X) hp hP hpP
  rw [hnot, hdvd] at hsplit
  have hmul : (∑ m ∈ avoidanceFinset P (X / p), c (p * m)) =
      c p * avoidanceSum c P (X / p) := by
    unfold avoidanceSum
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    rw [hcomp p m hp.pos]
    simp only [avoidanceFinset, Finset.mem_filter, Finset.mem_Icc] at hm
    exact hm.1.1
  rw [hmul] at hsplit
  unfold avoidanceSum at hsplit ⊢
  linarith

noncomputable def normalizedAvoidance
    (c : ℕ → ℝ) (P : Finset ℕ) (N : ℕ) : ℝ :=
  avoidanceSum c P ((∏ p ∈ P, p) * N) / (((∏ p ∈ P, p) * N : ℕ) : ℝ)

noncomputable def avoidanceEulerFactor
    (c : ℕ → ℝ) (P : Finset ℕ) : ℝ :=
  ∏ p ∈ P, (1 - c p / (p : ℝ))

lemma normalizedAvoidance_empty (c : ℕ → ℝ) (N : ℕ) :
    normalizedAvoidance c ∅ N = meanUpTo c N := by
  classical
  have hfin : avoidanceFinset ∅ N = Finset.Icc 1 N := by
    ext n
    simp [avoidanceFinset, Avoids]
  simp [normalizedAvoidance, avoidanceSum, hfin, meanUpTo]

lemma avoidanceEulerFactor_empty (c : ℕ → ℝ) :
    avoidanceEulerFactor c ∅ = 1 := by
  simp [avoidanceEulerFactor]

/-- The normalized avoidance sum is asymptotic to the ordinary mean times
the finite Euler factor.  This is where the fixed-dilation consequence of
real-prefix stability is used. -/
theorem tendsto_normalizedAvoidance_sub_mean_mul_euler {f : ℕ → ℝ}
    (hf : IsSignMultiplicative f) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) :
    Tendsto (fun N : ℕ =>
      normalizedAvoidance (completeCompanion f) P N -
        meanUpTo (completeCompanion f) ((∏ p ∈ P, p) * N) *
          avoidanceEulerFactor (completeCompanion f) P) atTop (𝓝 0) := by
  classical
  induction P using Finset.induction_on with
  | empty =>
      simp [normalizedAvoidance_empty, avoidanceEulerFactor_empty]
  | @insert p P hpP ih =>
      have hp : p.Prime := hP p (by simp)
      have hPrest : ∀ q ∈ P, q.Prime := fun q hq => hP q (by simp [hq])
      have hQpos : 0 < ∏ q ∈ P, q :=
        Finset.prod_pos fun q hq => (hPrest q hq).pos
      have hih := ih hPrest
      have hihp := hih.comp (tendsto_nat_const_mul_atTop p hp.pos)
      have hmean := tendsto_completeCompanion_mean_mul_sub_mul hf
        (a := ∏ q ∈ P, q) (b := p * ∏ q ∈ P, q)
          hQpos (mul_pos hp.pos hQpos)
      have hcomb :=
        (hihp.sub (hih.const_mul (completeCompanion f p / (p : ℝ)))).sub
          (hmean.const_mul
            ((completeCompanion f p / (p : ℝ)) *
              avoidanceEulerFactor (completeCompanion f) P))
      have hcongr : ∀ᶠ N : ℕ in atTop,
          (normalizedAvoidance (completeCompanion f) (insert p P) N -
              meanUpTo (completeCompanion f) ((∏ q ∈ insert p P, q) * N) *
                avoidanceEulerFactor (completeCompanion f) (insert p P)) =
            ((normalizedAvoidance (completeCompanion f) P (p * N) -
                meanUpTo (completeCompanion f) ((∏ q ∈ P, q) * (p * N)) *
                  avoidanceEulerFactor (completeCompanion f) P) -
              (completeCompanion f p / (p : ℝ)) *
                (normalizedAvoidance (completeCompanion f) P N -
                  meanUpTo (completeCompanion f) ((∏ q ∈ P, q) * N) *
                    avoidanceEulerFactor (completeCompanion f) P)) -
              ((completeCompanion f p / (p : ℝ)) *
                  avoidanceEulerFactor (completeCompanion f) P) *
                (meanUpTo (completeCompanion f) ((∏ q ∈ P, q) * N) -
                  meanUpTo (completeCompanion f)
                    ((p * ∏ q ∈ P, q) * N)) := by
        filter_upwards [eventually_ge_atTop 1] with N hN
        have hNpos : N ≠ 0 := by omega
        have hprod : (∏ q ∈ insert p P, q) = p * ∏ q ∈ P, q :=
          Finset.prod_insert hpP
        have hdiv : (p * (∏ q ∈ P, q) * N) / p = (∏ q ∈ P, q) * N := by
          simpa [mul_assoc] using
            (Nat.mul_div_cancel_left ((∏ q ∈ P, q) * N) hp.pos)
        have hrec := avoidanceSum_insert
          (c := completeCompanion f) hp hPrest hpP
          (fun m n hm hn => completeCompanion_mul f hm.ne' hn.ne')
          (X := p * (∏ q ∈ P, q) * N)
        rw [hdiv] at hrec
        simp only [normalizedAvoidance, avoidanceEulerFactor, hprod,
          Finset.prod_insert hpP]
        rw [hrec]
        have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
        have hQR : ((∏ q ∈ P, q : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hQpos.ne'
        have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hNpos
        push_cast
        field_simp [hpR, hQR, hNR]
        ring
      have hcomb0 : Tendsto (fun N : ℕ =>
          ((normalizedAvoidance (completeCompanion f) P (p * N) -
              meanUpTo (completeCompanion f) ((∏ q ∈ P, q) * (p * N)) *
                avoidanceEulerFactor (completeCompanion f) P) -
            (completeCompanion f p / (p : ℝ)) *
              (normalizedAvoidance (completeCompanion f) P N -
                meanUpTo (completeCompanion f) ((∏ q ∈ P, q) * N) *
                  avoidanceEulerFactor (completeCompanion f) P)) -
            ((completeCompanion f p / (p : ℝ)) *
                avoidanceEulerFactor (completeCompanion f) P) *
              (meanUpTo (completeCompanion f) ((∏ q ∈ P, q) * N) -
                meanUpTo (completeCompanion f)
                  ((p * ∏ q ∈ P, q) * N))) atTop (𝓝 0) := by
        simpa only [Function.comp_apply, mul_zero, sub_zero] using hcomb
      exact hcomb0.congr' (hcongr.mono fun _ h => h.symm)

lemma avoidanceFinset_card_eq_primeAvoidance_sum (P : Finset ℕ) (X : ℕ) :
    ((avoidanceFinset P X).card : ℝ) =
      ∑ n ∈ Finset.Ioc 0 X, Erdos69.HalaszMean.primeAvoidance P n := by
  classical
  have hsets : Finset.Icc 1 X = Finset.Ioc 0 X := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [avoidanceFinset, hsets]
  rw [Finset.card_filter]
  simp only [Nat.cast_sum, Erdos69.HalaszMean.primeAvoidance]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases havoid : Avoids P n
  · have hcond : ∀ p ∈ P, ¬p ∣ n := by simpa only [Avoids] using havoid
    simp only [if_pos havoid, if_pos hcond, Nat.cast_one]
  · have hcond : ¬∀ p ∈ P, ¬p ∣ n := by simpa only [Avoids] using havoid
    simp only [if_neg havoid, if_neg hcond, Nat.cast_zero]

lemma abs_avoidanceSum_completeCompanion_le_card {f : ℕ → ℝ}
    (hf : IsSignMultiplicative f) (P : Finset ℕ) (X : ℕ) :
    |avoidanceSum (completeCompanion f) P X| ≤
      (avoidanceFinset P X).card := by
  classical
  unfold avoidanceSum
  calc
    |∑ n ∈ avoidanceFinset P X, completeCompanion f n| ≤
        ∑ n ∈ avoidanceFinset P X, |completeCompanion f n| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ _n ∈ avoidanceFinset P X, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro n hn
      apply completeCompanion_abs_eq_one hf
      unfold avoidanceFinset at hn
      exact (Finset.mem_Icc.1 (Finset.mem_filter.1 hn).1).1
    _ = (avoidanceFinset P X).card := by simp

lemma avoidanceEulerFactor_completeCompanion_ge_one {f : ℕ → ℝ}
    (P : Finset ℕ) (hneg : ∀ p ∈ P, p.Prime ∧ f p = -1) :
    1 ≤ avoidanceEulerFactor (completeCompanion f) P := by
  classical
  unfold avoidanceEulerFactor
  apply Finset.one_le_prod
  intro p hp
  rw [completeCompanion_prime f (hneg p hp).1, (hneg p hp).2]
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (hneg p hp).1.pos
  have hdiv : (-1 : ℝ) / (p : ℝ) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by norm_num) hp0.le
  linarith

/-- Selberg's finite prime-avoidance estimate bounds the normalized signed
avoidance sum at the exact product endpoints used above. -/
lemma abs_normalizedAvoidance_le_halasz {f : ℕ → ℝ}
    (hf : IsSignMultiplicative f) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hne : P.Nonempty) {N : ℕ} (hN : 0 < N) :
    |normalizedAvoidance (completeCompanion f) P N| ≤
      1 / (1 + Erdos69.HalaszMean.reciprocalMass P) +
        (2 * P.card : ℝ) / (((∏ p ∈ P, p) * N : ℕ) : ℝ) := by
  let Q := ∏ p ∈ P, p
  have hQ : 0 < Q := Finset.prod_pos fun p hp => (hP p hp).pos
  have hX : 0 < Q * N := mul_pos hQ hN
  have hmass : 0 < Erdos69.HalaszMean.reciprocalMass P :=
    Erdos69.HalaszMean.reciprocalMass_pos_of_nonempty P hP hne
  have hcard := Erdos69.HalaszMean.primeAvoidance_sum_le P hP hmass (Q * N)
  rw [← avoidanceFinset_card_eq_primeAvoidance_sum] at hcard
  have habs := abs_avoidanceSum_completeCompanion_le_card hf P (Q * N)
  have hden : (0 : ℝ) < ((Q * N : ℕ) : ℝ) := by exact_mod_cast hX
  rw [normalizedAvoidance]
  rw [abs_div]
  change |avoidanceSum (completeCompanion f) P (Q * N)| /
      |(((Q * N : ℕ) : ℝ))| ≤
    1 / (1 + Erdos69.HalaszMean.reciprocalMass P) +
      (2 * P.card : ℝ) / (((Q * N : ℕ) : ℝ))
  rw [abs_of_pos hden]
  calc
    |avoidanceSum (completeCompanion f) P (Q * N)| /
        (((Q * N : ℕ) : ℝ)) ≤
        ((avoidanceFinset P (Q * N)).card : ℝ) /
          (((Q * N : ℕ) : ℝ)) :=
      div_le_div_of_nonneg_right habs hden.le
    _ ≤ (((Q * N : ℕ) : ℝ) /
          (1 + Erdos69.HalaszMean.reciprocalMass P) + 2 * P.card) /
          (((Q * N : ℕ) : ℝ)) := div_le_div_of_nonneg_right hcard hden.le
    _ = 1 / (1 + Erdos69.HalaszMean.reciprocalMass P) +
          (2 * P.card : ℝ) / (((Q * N : ℕ) : ℝ)) := by
      field_simp

theorem eventually_abs_completeCompanion_mean_mul_le {f : ℕ → ℝ}
    (hf : IsSignMultiplicative f) (P : Finset ℕ)
    (hneg : ∀ p ∈ P, p.Prime ∧ f p = -1) (hne : P.Nonempty) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      |meanUpTo (completeCompanion f) ((∏ p ∈ P, p) * N)| ≤
        1 / (1 + Erdos69.HalaszMean.reciprocalMass P) + ε := by
  let Q := ∏ p ∈ P, p
  have hP : ∀ p ∈ P, p.Prime := fun p hp => (hneg p hp).1
  have hQ : 0 < Q := Finset.prod_pos fun p hp => (hP p hp).pos
  have hEuler := avoidanceEulerFactor_completeCompanion_ge_one P hneg
  have hEuler0 : 0 ≤ avoidanceEulerFactor (completeCompanion f) P :=
    zero_le_one.trans hEuler
  have hT := tendsto_normalizedAvoidance_sub_mean_mul_euler hf P hP
  rw [Metric.tendsto_atTop] at hT
  obtain ⟨N₀, hN₀⟩ := hT (ε / 2) (by positivity)
  have hdenTop : Tendsto (fun N : ℕ => (((Q * N : ℕ) : ℝ))) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_nat_const_mul_atTop Q hQ)
  have hend : Tendsto (fun N : ℕ =>
      (2 * P.card : ℝ) / (((Q * N : ℕ) : ℝ))) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hdenTop
  rw [Metric.tendsto_atTop] at hend
  obtain ⟨N₁, hN₁⟩ := hend (ε / 2) (by positivity)
  filter_upwards [eventually_ge_atTop (max (max N₀ N₁) 1)] with N hN
  have hNpos : 0 < N := by omega
  have havoid := abs_normalizedAvoidance_le_halasz hf P hP hne hNpos
  have hTerr : |normalizedAvoidance (completeCompanion f) P N -
      meanUpTo (completeCompanion f) (Q * N) *
        avoidanceEulerFactor (completeCompanion f) P| < ε / 2 := by
    simpa only [Real.dist_eq, sub_zero, Q] using
      hN₀ N (le_max_left N₀ N₁ |>.trans
        (le_max_left (max N₀ N₁) 1 |>.trans hN))
  have henderr : (2 * P.card : ℝ) / (((Q * N : ℕ) : ℝ)) < ε / 2 := by
    have := hN₁ N (le_max_right N₀ N₁ |>.trans
      (le_max_left (max N₀ N₁) 1 |>.trans hN))
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at this
    exact this
  let M := meanUpTo (completeCompanion f) (Q * N)
  let U := normalizedAvoidance (completeCompanion f) P N
  let E := avoidanceEulerFactor (completeCompanion f) P
  have hME : |M| ≤ |M * E| := by
    rw [abs_mul, abs_of_nonneg hEuler0]
    nlinarith [abs_nonneg M]
  have htri : |M * E| ≤ |U| + |U - M * E| := by
    calc
      |M * E| = |U - (U - M * E)| := by congr 1 <;> ring
      _ ≤ |U| + |U - M * E| := abs_sub U (U - M * E)
  dsimp only [M, U, E] at hME htri
  exact (hME.trans htri).trans (by linarith)

lemma badPrimeReciprocal_nonneg (f : ℕ → ℝ) (p : ℕ) :
    0 ≤ badPrimeReciprocal f p := by
  unfold badPrimeReciprocal
  split_ifs <;> positivity

lemma badPrimeReciprocal_sum_range_eq_reciprocalMass (f : ℕ → ℝ) (K : ℕ) :
    (∑ p ∈ Finset.range K, badPrimeReciprocal f p) =
      Erdos69.HalaszMean.reciprocalMass
        ((Finset.range K).filter fun p => p.Prime ∧ f p = -1) := by
  classical
  rw [Erdos69.HalaszMean.reciprocalMass]
  simp only [badPrimeReciprocal, Finset.sum_filter]

lemma exists_badPrime_packet_large_mass {f : ℕ → ℝ}
    (hbad : ¬Summable (badPrimeReciprocal f)) (A : ℝ) :
    ∃ P : Finset ℕ,
      (∀ p ∈ P, p.Prime ∧ f p = -1) ∧
      A < Erdos69.HalaszMean.reciprocalMass P := by
  have hunbounded : ∃ K : ℕ,
      A < ∑ p ∈ Finset.range K, badPrimeReciprocal f p := by
    by_contra h
    push Not at h
    exact hbad (summable_of_sum_range_le
      (badPrimeReciprocal_nonneg f) fun K => h K)
  obtain ⟨K, hK⟩ := hunbounded
  refine ⟨(Finset.range K).filter fun p => p.Prime ∧ f p = -1, ?_, ?_⟩
  · intro p hp
    exact (Finset.mem_filter.1 hp).2
  · rwa [← badPrimeReciprocal_sum_range_eq_reciprocalMass]

/-- In the divergent negative-prime branch the completely multiplicative
companion has mean zero. -/
theorem tendsto_completeCompanion_mean_zero_of_not_summable_badPrimes
    {f : ℕ → ℝ} (hf : IsSignMultiplicative f)
    (hbad : ¬Summable (badPrimeReciprocal f)) :
    Tendsto (meanUpTo (completeCompanion f)) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨P, hneg, hmass⟩ :=
    exists_badPrime_packet_large_mass hbad (4 / ε)
  have hP : ∀ p ∈ P, p.Prime := fun p hp => (hneg p hp).1
  have hne : P.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty.mp h] at hmass
    simp [Erdos69.HalaszMean.reciprocalMass] at hmass
    have hfour : 0 < (4 : ℝ) / ε := div_pos (by norm_num) hε
    linarith
  let Q := ∏ p ∈ P, p
  have hQ : 0 < Q := Finset.prod_pos fun p hp => (hP p hp).pos
  have hmain := eventually_abs_completeCompanion_mean_mul_le hf P hneg hne
    (ε := ε / 4) (by positivity)
  have hfloor := tendsto_completeCompanion_mean_sub_floorMultiple hf hQ
  rw [Metric.tendsto_atTop] at hfloor
  obtain ⟨X₀, hX₀⟩ := hfloor (ε / 2) (by positivity)
  obtain ⟨X₁, hX₁⟩ := eventually_atTop.1 hmain
  refine ⟨max X₀ (Q * X₁), fun X hX => ?_⟩
  have hclose : |meanUpTo (completeCompanion f) X -
      meanUpTo (completeCompanion f) (floorMultiple Q X)| < ε / 2 := by
    simpa only [Real.dist_eq, sub_zero] using
      hX₀ X (le_max_left X₀ (Q * X₁) |>.trans hX)
  have hmultiple : |meanUpTo (completeCompanion f) (floorMultiple Q X)| ≤
      1 / (1 + Erdos69.HalaszMean.reciprocalMass P) + ε / 4 := by
    apply hX₁ (X / Q)
    apply (Nat.le_div_iff_mul_le hQ).2
    simpa only [Nat.mul_comm] using
      (le_max_right X₀ (Q * X₁) |>.trans hX)
  have hdecay : 1 / (1 + Erdos69.HalaszMean.reciprocalMass P) < ε / 4 := by
    have hmass0 : 0 < Erdos69.HalaszMean.reciprocalMass P :=
      Erdos69.HalaszMean.reciprocalMass_pos_of_nonempty P hP hne
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 1 +
      Erdos69.HalaszMean.reciprocalMass P)]
    have hprod := mul_lt_mul_of_pos_left hmass (show 0 < ε / 4 by positivity)
    field_simp at hprod
    nlinarith
  rw [Real.dist_eq, sub_zero]
  calc
    |meanUpTo (completeCompanion f) X| ≤
        |meanUpTo (completeCompanion f) X -
          meanUpTo (completeCompanion f) (floorMultiple Q X)| +
        |meanUpTo (completeCompanion f) (floorMultiple Q X)| := by
      simpa only [sub_add_cancel] using
        (abs_add_le (meanUpTo (completeCompanion f) X -
          meanUpTo (completeCompanion f) (floorMultiple Q X))
          (meanUpTo (completeCompanion f) (floorMultiple Q X)))
    _ < ε := by linarith

/-- The averages are uniformly bounded by one. -/
lemma abs_meanUpTo_le_one {f : ℕ → ℝ} (hf : IsSignMultiplicative f) (N : ℕ) :
    |meanUpTo f N| ≤ 1 := by
  by_cases hN : N = 0
  · simp [meanUpTo, hN]
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hterm : ∀ n ∈ Finset.Icc 1 N, |f n| ≤ 1 := by
    intro n hn
    rw [hf.abs_eq_one (Finset.mem_Icc.mp hn).1]
  calc
    |meanUpTo f N|
        = |∑ n ∈ Finset.Icc 1 N, f n| / (N : ℝ) := by
            simp [meanUpTo, abs_div, abs_of_pos hNpos]
    _ ≤ (∑ n ∈ Finset.Icc 1 N, |f n|) / (N : ℝ) := by
          gcongr
          exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ (∑ _n ∈ Finset.Icc 1 N, (1 : ℝ)) / (N : ℝ) := by
          exact div_le_div_of_nonneg_right (Finset.sum_le_sum hterm) hNpos.le
    _ = 1 := by
          simp [Nat.card_Icc, hNpos.ne']

/-! ## An elementary Euler-product summability criterion -/

/-- A nonnegative multiplicative function is summable if its positive
prime-power tails are summable locally and their sums are summable over the
primes.  This finite-Euler-product form is exactly what is needed for both
Möbius corrections below. -/
theorem summable_of_multiplicative_prime_tails (w : ℕ → ℝ)
    (hw0 : w 0 = 0) (hw1 : w 1 = 1)
    (hw_nonneg : ∀ n, 0 ≤ w n)
    (hw_mul : ∀ {m n : ℕ}, m.Coprime n → w (m * n) = w m * w n)
    (hlocal : ∀ {p : ℕ}, p.Prime →
      Summable (fun k : ℕ => w (p ^ (k + 1))))
    (hprime : Summable (fun p : ℕ =>
      if p.Prime then ∑' k : ℕ, w (p ^ (k + 1)) else 0)) :
    Summable w := by
  classical
  let tail : ℕ → ℝ := fun p =>
    if p.Prime then ∑' k : ℕ, w (p ^ (k + 1)) else 0
  change Summable tail at hprime
  have htail_nonneg : ∀ p, 0 ≤ tail p := by
    intro p
    by_cases hp : p.Prime
    · simp only [tail, if_pos hp]
      exact tsum_nonneg fun _ => hw_nonneg _
    · simp [tail, hp]
  have hlocal_full : ∀ {p : ℕ}, p.Prime →
      Summable (fun k : ℕ => ‖w (p ^ k)‖) := by
    intro p hp
    apply (summable_nat_add_iff 1).mp
    simpa only [Nat.add_comm] using
      (hlocal hp).congr (fun k => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hw_nonneg _)])
  have hlocal_tsum : ∀ {p : ℕ}, p.Prime →
      (∑' k : ℕ, w (p ^ k)) = 1 + tail p := by
    intro p hp
    have hs : Summable (fun k : ℕ => w (p ^ k)) :=
      (hlocal_full hp).of_norm
    rw [← hs.sum_add_tsum_nat_add 1]
    simp [tail, hp, hw1, Nat.add_comm]
  apply summable_of_sum_range_le hw_nonneg
    (c := Real.exp (∑' p : ℕ, tail p))
  intro N
  by_cases hN : N = 0
  · subst N
    simp only [Finset.range_zero, Finset.sum_empty]
    exact (Real.exp_pos _).le
  let emb : {n // n ∈ (Finset.range N).erase 0} →
      Nat.factoredNumbers (Finset.range N) := fun n =>
    ⟨n.1, (Nat.mem_factoredNumbers').2 fun p hp hpd =>
      Finset.mem_range.2 ((Nat.le_of_dvd (Nat.pos_of_ne_zero
        (Finset.ne_of_mem_erase n.2)) hpd).trans_lt
          (Finset.mem_range.1 (Finset.mem_of_mem_erase n.2)))⟩
  let t : Finset (Nat.factoredNumbers (Finset.range N)) :=
    ((Finset.range N).erase 0).attach.image emb
  have he := EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum
    hw1 (fun {_ _} hcop => hw_mul hcop) hlocal_full (Finset.range N)
  have hsubsum : Summable (fun m : Nat.factoredNumbers (Finset.range N) => w m) :=
    he.1.of_norm
  have hfinite : (∑ n ∈ Finset.range N, w n) = ∑ m ∈ t, w m := by
    have hzero : 0 ∈ Finset.range N := Finset.mem_range.2 (Nat.pos_of_ne_zero hN)
    calc
      (∑ n ∈ Finset.range N, w n) = ∑ n ∈ (Finset.range N).erase 0, w n := by
        exact (Finset.sum_erase (Finset.range N) hw0).symm
      _ = ∑ n ∈ ((Finset.range N).erase 0).attach, w n := by
        rw [Finset.sum_attach]
      _ = ∑ m ∈ t, w m := by
        symm
        apply Finset.sum_image
        intro a ha b hb hab
        apply Subtype.ext
        exact congrArg
          (fun x : Nat.factoredNumbers (Finset.range N) => (x : ℕ)) hab
  rw [hfinite]
  calc
    (∑ m ∈ t, w m) ≤ ∑' m : Nat.factoredNumbers (Finset.range N), w m :=
      hsubsum.sum_le_tsum t (fun _ _ => hw_nonneg _)
    _ = ∏ p ∈ Finset.range N with p.Prime, (1 + tail p) := by
      rw [he.2.tsum_eq]
      apply Finset.prod_congr rfl
      intro p hp
      exact hlocal_tsum (Finset.mem_filter.1 hp).2
    _ ≤ Real.exp (∑ p ∈ Finset.range N with p.Prime, tail p) := by
      exact Real.prod_one_add_le_exp_sum _ fun p => htail_nonneg p
    _ ≤ Real.exp (∑' p : ℕ, tail p) := by
      apply Real.exp_le_exp.mpr
      exact hprime.sum_le_tsum _ (fun p _ => htail_nonneg p)

/-! ## The Wintner summable-convolution lemma

This is the soft half of Wirsing's dichotomy.  If an arithmetic function is
the Dirichlet convolution of `g` with the constant-one arithmetic function,
and `∑ |g(n)| / n` converges, then its Cesàro mean is `∑ g(n) / n`.
-/

open scoped ArithmeticFunction.zeta

/-- For fixed positive `d`, the density of multiples of `d` in an initial
interval tends to `1 / d`. -/
lemma tendsto_natDiv_div (d : ℕ) (_hd : 0 < d) :
    Tendsto (fun N : ℕ => ((N / d : ℕ) : ℝ) / (N : ℝ)) atTop
      (𝓝 ((d : ℝ)⁻¹)) := by
  have h := tendsto_nat_floor_mul_div_atTop
    (R := ℝ) (a := (d : ℝ)⁻¹) (inv_nonneg.mpr (Nat.cast_nonneg d))
  have h' := h.comp tendsto_natCast_atTop_atTop
  refine h'.congr' (Eventually.of_forall fun N => ?_)
  simp only [Function.comp_apply]
  rw [show (d : ℝ)⁻¹ * (N : ℝ) = (N : ℝ) / (d : ℝ) by
    simp [div_eq_mul_inv, mul_comm]]
  rw [Nat.floor_div_eq_div]

/-- Wintner's averaging lemma, in the exact `Finset.Ioc 0 N` convention used
by Mathlib's summatory-convolution identity. -/
theorem tendsto_mean_dirichlet_mul_zeta (g : ArithmeticFunction ℝ)
    (hg : Summable fun n : ℕ => |g n| / (n : ℝ)) :
    Tendsto
      (fun N : ℕ => (∑ n ∈ Finset.Ioc 0 N, (g * ζ) n) / (N : ℝ))
      atTop (𝓝 (∑' n : ℕ, g n / (n : ℝ))) := by
  let a : ℕ → ℕ → ℝ := fun N n =>
    if n ∈ Finset.Ioc 0 N then
      g n * (((N / n : ℕ) : ℝ) / (N : ℝ))
    else 0
  have ha_lim : ∀ n : ℕ,
      Tendsto (fun N : ℕ => a N n) atTop (𝓝 (g n / (n : ℝ))) := by
    intro n
    by_cases hn : n = 0
    · subst n
      simp [a]
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      have hevent : ∀ᶠ N : ℕ in atTop, n ∈ Finset.Ioc 0 N :=
        eventually_atTop.2 ⟨n, fun N hN => Finset.mem_Ioc.mpr ⟨hnpos, hN⟩⟩
      change Tendsto (fun N : ℕ => a N n) atTop (𝓝 (g n * (n : ℝ)⁻¹))
      refine (tendsto_const_nhds.mul (tendsto_natDiv_div n hnpos)).congr' ?_
      filter_upwards [hevent] with N hN
      dsimp [a]
      rw [if_pos hN]
  have ha_bound : ∀ᶠ N : ℕ in atTop,
      ∀ n : ℕ, ‖a N n‖ ≤ |g n| / (n : ℝ) := by
    filter_upwards [eventually_atTop.2 ⟨1, fun _ h => h⟩] with N hN
    intro n
    by_cases hmem : n ∈ Finset.Ioc 0 N
    · have hnpos : 0 < n := (Finset.mem_Ioc.mp hmem).1
      have hNpos : 0 < (N : ℝ) := by exact_mod_cast hN
      have hratio_nonneg :
          0 ≤ ((N / n : ℕ) : ℝ) / (N : ℝ) := by positivity
      have hratio : ((N / n : ℕ) : ℝ) / (N : ℝ) ≤ (n : ℝ)⁻¹ := by
        calc
          ((N / n : ℕ) : ℝ) / (N : ℝ)
              ≤ ((N : ℝ) / (n : ℝ)) / (N : ℝ) := by
                exact div_le_div_of_nonneg_right Nat.cast_div_le hNpos.le
          _ = (n : ℝ)⁻¹ := by
                field_simp
      simp only [a, if_pos hmem, norm_mul, Real.norm_eq_abs,
        Real.norm_of_nonneg hratio_nonneg]
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left hratio (abs_nonneg _)
    · simp only [a, if_neg hmem, norm_zero]
      positivity
  have htannery := tendsto_tsum_of_dominated_convergence hg ha_lim ha_bound
  convert htannery using 1
  · ext N
    rw [ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum]
    rw [Finset.sum_div]
    simp only [a]
    rw [tsum_eq_sum (s := Finset.Ioc 0 N)]
    · apply Finset.sum_congr rfl
      intro n hn
      simp [hn, mul_div_assoc]
    · intro n hn
      simp [hn]

/-- The normalized summatory function of an arithmetic function. -/
noncomputable def arithmeticMean (c : ArithmeticFunction ℝ) (N : ℕ) : ℝ :=
  (∑ n ∈ Finset.Ioc 0 N, c n) / (N : ℝ)

lemma tendsto_nat_div_atTop (d : ℕ) (hd : 0 < d) :
    Tendsto (fun N : ℕ => N / d) atTop atTop := by
  rw [tendsto_atTop]
  intro b
  filter_upwards [eventually_ge_atTop (d * b)] with N hN
  exact (Nat.le_div_iff_mul_le hd).2 (by simpa [Nat.mul_comm] using hN)

/-- An absolutely summable Dirichlet convolution preserves an existing
bounded Cesàro mean.  This is the form of Wintner's argument needed to
transfer the zero mean of the completely multiplicative companion back to
the original multiplicative function. -/
theorem tendsto_mean_dirichlet_mul_of_mean
    (g c : ArithmeticFunction ℝ) (L : ℝ)
    (hc : Tendsto (arithmeticMean c) atTop (𝓝 L))
    (hc_bound : ∀ N : ℕ, |arithmeticMean c N| ≤ 1)
    (hg : Summable fun n : ℕ => |g n| / (n : ℝ)) :
    Tendsto (fun N : ℕ => arithmeticMean (g * c) N) atTop
      (𝓝 ((∑' n : ℕ, g n / (n : ℝ)) * L)) := by
  let a : ℕ → ℕ → ℝ := fun N n =>
    if n ∈ Finset.Ioc 0 N then
      g n * (((N / n : ℕ) : ℝ) / (N : ℝ)) * arithmeticMean c (N / n)
    else 0
  have ha_lim : ∀ n : ℕ,
      Tendsto (fun N : ℕ => a N n) atTop
        (𝓝 ((g n / (n : ℝ)) * L)) := by
    intro n
    by_cases hn : n = 0
    · subst n
      simp [a]
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      have hevent : ∀ᶠ N : ℕ in atTop, n ∈ Finset.Ioc 0 N :=
        eventually_atTop.2 ⟨n, fun N hN => Finset.mem_Ioc.mpr ⟨hnpos, hN⟩⟩
      have hmean := hc.comp (tendsto_nat_div_atTop n hnpos)
      have hprod : Tendsto (fun N : ℕ =>
          g n * (((N / n : ℕ) : ℝ) / (N : ℝ)) *
            arithmeticMean c (N / n)) atTop
          (𝓝 (g n * (n : ℝ)⁻¹ * L)) :=
        (tendsto_const_nhds.mul (tendsto_natDiv_div n hnpos)).mul hmean
      simpa only [div_eq_mul_inv] using
        hprod.congr' (hevent.mono fun N hN => by simp only [a, if_pos hN])
  have ha_bound : ∀ᶠ N : ℕ in atTop,
      ∀ n : ℕ, ‖a N n‖ ≤ |g n| / (n : ℝ) := by
    filter_upwards [eventually_atTop.2 ⟨1, fun _ h => h⟩] with N hN
    intro n
    by_cases hmem : n ∈ Finset.Ioc 0 N
    · have hNpos : 0 < (N : ℝ) := by exact_mod_cast hN
      have hratio_nonneg :
          0 ≤ ((N / n : ℕ) : ℝ) / (N : ℝ) := by positivity
      have hratio : ((N / n : ℕ) : ℝ) / (N : ℝ) ≤ (n : ℝ)⁻¹ := by
        calc
          ((N / n : ℕ) : ℝ) / (N : ℝ) ≤
              ((N : ℝ) / (n : ℝ)) / (N : ℝ) :=
            div_le_div_of_nonneg_right Nat.cast_div_le hNpos.le
          _ = (n : ℝ)⁻¹ := by field_simp
      simp only [a, if_pos hmem, norm_mul, Real.norm_eq_abs,
        Real.norm_of_nonneg hratio_nonneg]
      rw [div_eq_mul_inv]
      calc
        |g n| * (((N / n : ℕ) : ℝ) / (N : ℝ)) *
              |arithmeticMean c (N / n)| ≤
            |g n| * (((N / n : ℕ) : ℝ) / (N : ℝ)) * 1 :=
          mul_le_mul_of_nonneg_left (hc_bound _)
            (mul_nonneg (abs_nonneg _) hratio_nonneg)
        _ ≤ |g n| * (n : ℝ)⁻¹ := by
          simpa using mul_le_mul_of_nonneg_left hratio (abs_nonneg (g n))
    · simp only [a, if_neg hmem, norm_zero]
      positivity
  have htannery := tendsto_tsum_of_dominated_convergence hg ha_lim ha_bound
  convert htannery using 1
  · ext N
    rw [arithmeticMean, ArithmeticFunction.sum_Ioc_mul_eq_sum_sum]
    rw [Finset.sum_div]
    simp only [a, arithmeticMean]
    rw [tsum_eq_sum (s := Finset.Ioc 0 N)]
    · apply Finset.sum_congr rfl
      intro n hn
      have hnpos : 0 < n := (Finset.mem_Ioc.mp hn).1
      have hnN : n ≤ N := (Finset.mem_Ioc.mp hn).2
      have hNpos : 0 < N := hnpos.trans_le hnN
      have hdivpos : 0 < N / n := Nat.div_pos hnN hnpos
      simp only [hn, ↓reduceIte]
      field_simp [Nat.ne_of_gt hNpos, Nat.ne_of_gt hdivpos]
    · intro n hn
      simp [hn]
  · rw [tsum_mul_right]

/-- The arithmetic-function version of `f`, with the required value zero at
the natural number zero. -/
noncomputable def arithmeticFunction (f : ℕ → ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n = 0 then 0 else f n, by simp⟩

@[simp] lemma arithmeticFunction_zero (f : ℕ → ℝ) : arithmeticFunction f 0 = 0 := by
  simp [arithmeticFunction]

lemma arithmeticFunction_apply_of_pos (f : ℕ → ℝ) {n : ℕ} (hn : 0 < n) :
    arithmeticFunction f n = f n := by
  simp [arithmeticFunction, hn.ne']

lemma arithmeticFunction_isMultiplicative {f : ℕ → ℝ}
    (hf : IsSignMultiplicative f) :
    (arithmeticFunction f).IsMultiplicative := by
  refine ⟨by simp [arithmeticFunction, hf.one], ?_⟩
  intro m n hmn
  by_cases hm : m = 0
  · subst m
    simp
  by_cases hn : n = 0
  · subst n
    simp
  simp only [arithmeticFunction_apply_of_pos f (Nat.pos_of_ne_zero hm),
    arithmeticFunction_apply_of_pos f (Nat.pos_of_ne_zero hn),
    arithmeticFunction_apply_of_pos f (Nat.mul_pos
      (Nat.pos_of_ne_zero hm) (Nat.pos_of_ne_zero hn))]
  exact hf.mul hmn

/-- The complete companion as a zero-preserving monoid homomorphism. -/
noncomputable def completeCompanionHom (f : ℕ → ℝ) : ℕ →*₀ ℝ where
  toFun := completeCompanion f
  map_zero' := completeCompanion_zero f
  map_one' := completeCompanion_one f
  map_mul' m n := by
    by_cases hm : m = 0
    · subst m
      simp
    by_cases hn : n = 0
    · subst n
      simp
    exact completeCompanion_mul f hm hn

/-- Arithmetic-function form of the complete companion. -/
noncomputable def companionArithmetic (f : ℕ → ℝ) : ArithmeticFunction ℝ :=
  ⟨completeCompanionHom f, map_zero (completeCompanionHom f)⟩

@[simp] lemma companionArithmetic_apply (f : ℕ → ℝ) (n : ℕ) :
    companionArithmetic f n = completeCompanion f n := rfl

lemma companionArithmetic_isMultiplicative (f : ℕ → ℝ) :
    (companionArithmetic f).IsMultiplicative := by
  refine ⟨by simp [companionArithmetic], ?_⟩
  intro m n hmn
  simp only [companionArithmetic_apply]
  exact map_mul (completeCompanionHom f) m n

/-- Pointwise twisting by a completely multiplicative real function
intertwines Dirichlet convolution. -/
theorem companionArithmetic_pmul_mul (f : ℕ → ℝ)
    (g h : ArithmeticFunction ℝ) :
    ((companionArithmetic f).pmul g) * ((companionArithmetic f).pmul h) =
      (companionArithmetic f).pmul (g * h) := by
  ext n
  by_cases hn : n = 0
  · subst n
    simp
  · simp only [ArithmeticFunction.mul_apply, ArithmeticFunction.pmul_apply,
      companionArithmetic_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro xy hxy
    rcases Nat.mem_divisorsAntidiagonal.mp hxy with ⟨hprod, _hprod0⟩
    have hx : xy.1 ≠ 0 := by
      intro hx
      apply hn
      rw [← hprod, hx, zero_mul]
    have hy : xy.2 ≠ 0 := by
      intro hy
      apply hn
      rw [← hprod, hy, mul_zero]
    rw [← hprod, completeCompanion_mul f hx hy]
    ring

/-- Möbius correction `g = f * μ`; thus `f = g * 1`. -/
noncomputable def correction (f : ℕ → ℝ) : ArithmeticFunction ℝ :=
  arithmeticFunction f * (ArithmeticFunction.moebius : ArithmeticFunction ℝ)

lemma correction_isMultiplicative {f : ℕ → ℝ}
    (hf : IsSignMultiplicative f) : (correction f).IsMultiplicative :=
  (arithmeticFunction_isMultiplicative hf).mul
    ArithmeticFunction.isMultiplicative_moebius.intCast

lemma correction_mul_zeta (f : ℕ → ℝ) :
    correction f * ζ = arithmeticFunction f := by
  simp [correction, mul_assoc]

/-- On prime powers the Möbius correction is the first difference of the
local values of `f`. -/
lemma correction_prime_pow_succ (f : ℕ → ℝ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    correction f (p ^ (k + 1)) = f (p ^ (k + 1)) - f (p ^ k) := by
  have hsucc := congrArg (fun F : ArithmeticFunction ℝ => F (p ^ (k + 1)))
    (correction_mul_zeta f)
  have hbase := congrArg (fun F : ArithmeticFunction ℝ => F (p ^ k))
    (correction_mul_zeta f)
  rw [ArithmeticFunction.coe_mul_zeta_apply,
    Nat.sum_divisors_prime_pow hp, Finset.sum_range_succ] at hsucc hbase
  rw [Finset.sum_range_succ] at hsucc
  rw [arithmeticFunction_apply_of_pos f (pow_pos hp.pos _)] at hsucc hbase
  linarith

/-- The pointwise quotient of `f` by its sign-valued complete companion.
Since the companion is its own reciprocal, multiplication is enough. -/
noncomputable def relativeSign (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  f n * completeCompanion f n

lemma relativeSign_isSignMultiplicative {f : ℕ → ℝ}
    (hf : IsSignMultiplicative f) : IsSignMultiplicative (relativeSign f) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    rcases hf.sign hn with hfval | hfval <;>
      rcases (completeCompanion_isSignMultiplicative hf).sign hn with hcval | hcval <;>
      simp [relativeSign, hfval, hcval]
  · intro m n hmn
    by_cases hm : m = 0
    · subst m
      simp [relativeSign]
    by_cases hn : n = 0
    · subst n
      simp [relativeSign]
    simp only [relativeSign, hf.mul hmn, completeCompanion_mul f hm hn]
    ring
  · simp [relativeSign, hf.one]

lemma relativeSign_prime_eq_one {f : ℕ → ℝ}
    (hf : IsSignMultiplicative f) {p : ℕ} (hp : p.Prime) :
    relativeSign f p = 1 := by
  rcases hf.sign hp.one_le with h | h <;>
    simp [relativeSign, completeCompanion_prime f hp, h]

/-- The absolutely summable convolution factor changing the complete
companion back into the original multiplicative function. -/
noncomputable def companionTransfer (f : ℕ → ℝ) : ArithmeticFunction ℝ :=
  (companionArithmetic f).pmul (correction (relativeSign f))

lemma companionTransfer_isMultiplicative {f : ℕ → ℝ}
    (hf : IsSignMultiplicative f) :
    (companionTransfer f).IsMultiplicative :=
  (companionArithmetic_isMultiplicative f).pmul
    (correction_isMultiplicative (relativeSign_isSignMultiplicative hf))

lemma companionTransfer_mul_companion {f : ℕ → ℝ}
    (hf : IsSignMultiplicative f) :
    companionTransfer f * companionArithmetic f = arithmeticFunction f := by
  have hc : companionArithmetic f =
      (companionArithmetic f).pmul (ζ : ArithmeticFunction ℝ) :=
    (ArithmeticFunction.pmul_zeta (companionArithmetic f)).symm
  calc
    companionTransfer f * companionArithmetic f =
        ((companionArithmetic f).pmul (correction (relativeSign f))) *
          ((companionArithmetic f).pmul (ζ : ArithmeticFunction ℝ)) := by
      rw [companionTransfer]
      exact congrArg
        (fun x : ArithmeticFunction ℝ =>
          (companionArithmetic f).pmul (correction (relativeSign f)) * x) hc
    _ = (companionArithmetic f).pmul
        (correction (relativeSign f) * (ζ : ArithmeticFunction ℝ)) :=
      companionArithmetic_pmul_mul f _ _
    _ = (companionArithmetic f).pmul (arithmeticFunction (relativeSign f)) := by
      rw [correction_mul_zeta]
    _ = arithmeticFunction f := by
      ext n
      by_cases hn : n = 0
      · subst n
        simp [relativeSign]
      have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      rw [ArithmeticFunction.pmul_apply, companionArithmetic_apply,
        arithmeticFunction_apply_of_pos (relativeSign f) hnpos,
        arithmeticFunction_apply_of_pos f hnpos]
      rcases (completeCompanion_isSignMultiplicative hf).sign hnpos with hcval | hcval <;>
        simp [relativeSign, hcval]

/-- The absolute Dirichlet weight attached to an arithmetic function. -/
noncomputable def weightedAbs (g : ArithmeticFunction ℝ) (n : ℕ) : ℝ :=
  |g n| / (n : ℝ)

lemma weightedAbs_zero (g : ArithmeticFunction ℝ) : weightedAbs g 0 = 0 := by
  simp [weightedAbs]

lemma weightedAbs_nonneg (g : ArithmeticFunction ℝ) (n : ℕ) :
    0 ≤ weightedAbs g n := by
  exact div_nonneg (abs_nonneg _) (Nat.cast_nonneg _)

lemma weightedAbs_one {g : ArithmeticFunction ℝ} (hg : g.IsMultiplicative) :
    weightedAbs g 1 = 1 := by
  simp [weightedAbs, hg.map_one]

lemma weightedAbs_mul_of_coprime {g : ArithmeticFunction ℝ}
    (hg : g.IsMultiplicative) {m n : ℕ} (hmn : m.Coprime n) :
    weightedAbs g (m * n) = weightedAbs g m * weightedAbs g n := by
  unfold weightedAbs
  rw [hg.map_mul_of_coprime hmn, abs_mul]
  push_cast
  ring

lemma correction_weighted_prime_pow_le {f : ℕ → ℝ}
    (hf : IsSignMultiplicative f) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    weightedAbs (correction f) (p ^ (k + 1)) ≤
      2 * ((p : ℝ)⁻¹) ^ (k + 1) := by
  rw [weightedAbs, correction_prime_pow_succ f hp k]
  have hpcast : ((p ^ (k + 1) : ℕ) : ℝ) = (p : ℝ) ^ (k + 1) := by
    norm_cast
  rw [hpcast]
  have hnum : |f (p ^ (k + 1)) - f (p ^ k)| ≤ 2 := by
    calc
      |f (p ^ (k + 1)) - f (p ^ k)| ≤
          |f (p ^ (k + 1))| + |f (p ^ k)| := abs_sub _ _
      _ = 2 := by
        rw [hf.abs_eq_one (pow_pos hp.pos _),
          hf.abs_eq_one (pow_pos hp.pos _)]
        norm_num
  have hden : 0 ≤ (p : ℝ) ^ (k + 1) := by positivity
  calc
    |f (p ^ (k + 1)) - f (p ^ k)| / (p : ℝ) ^ (k + 1) ≤
        2 / (p : ℝ) ^ (k + 1) := div_le_div_of_nonneg_right hnum hden
    _ = 2 * ((p : ℝ)⁻¹) ^ (k + 1) := by rw [inv_pow]; ring

lemma correction_weighted_prime_eq_zero {f : ℕ → ℝ}
    (hf : IsSignMultiplicative f) {p : ℕ} (hp : p.Prime)
    (hprime : f p = 1) : weightedAbs (correction f) p = 0 := by
  convert congrArg (fun x : ℝ => |x| / (p : ℝ))
    (correction_prime_pow_succ f hp 0) using 1 <;>
    simp [weightedAbs, hprime, hf.one]

/-- A sign-valued multiplicative function which equals one at every prime
differs from the constant function by a correction supported at prime-power
exponent at least two; its weighted correction is therefore summable. -/
theorem summable_correction_weighted_of_prime_one {f : ℕ → ℝ}
    (hf : IsSignMultiplicative f)
    (hprime : ∀ {p : ℕ}, p.Prime → f p = 1) :
    Summable (weightedAbs (correction f)) := by
  let w := weightedAbs (correction f)
  have hmult := correction_isMultiplicative hf
  apply summable_of_multiplicative_prime_tails w
    (weightedAbs_zero _) (weightedAbs_one hmult)
    (weightedAbs_nonneg _)
    (fun hcop => weightedAbs_mul_of_coprime hmult hcop)
  · intro p hp
    have hpR : ‖(p : ℝ)⁻¹‖ < 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
    have hgeom : Summable (fun k : ℕ =>
        2 * ((p : ℝ)⁻¹) ^ (k + 1)) :=
      by
        simpa only [pow_succ, mul_assoc, mul_left_comm, mul_comm] using
          (summable_geometric_of_norm_lt_one hpR).mul_left (2 * (p : ℝ)⁻¹)
    exact Summable.of_nonneg_of_le (fun k => weightedAbs_nonneg _ _)
      (fun k => correction_weighted_prime_pow_le hf hp k) hgeom
  · have hglobal : Summable (fun p : ℕ => 4 * ((p : ℝ)⁻¹) ^ 2) := by
      simpa only [inv_pow] using
        (Real.summable_nat_pow_inv.mpr (by norm_num : 1 < 2)).mul_left 4
    apply Summable.of_nonneg_of_le
      (fun p => by
        split_ifs
        · exact tsum_nonneg fun _ => weightedAbs_nonneg _ _
        · exact le_rfl)
      ?_ hglobal
    intro p
    by_cases hp : p.Prime
    · rw [if_pos hp]
      let u : ℕ → ℝ := fun k => weightedAbs (correction f) (p ^ (k + 1))
      have hpR : ‖(p : ℝ)⁻¹‖ < 1 := by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
      have hu : Summable u := by
        have hgeom : Summable (fun k : ℕ =>
            2 * ((p : ℝ)⁻¹) ^ (k + 1)) :=
          by
            simpa only [pow_succ, mul_assoc, mul_left_comm, mul_comm] using
              (summable_geometric_of_norm_lt_one hpR).mul_left (2 * (p : ℝ)⁻¹)
        exact Summable.of_nonneg_of_le (fun k => weightedAbs_nonneg _ _)
          (fun k => correction_weighted_prime_pow_le hf hp k) hgeom
      have hu0 : u 0 = 0 := by
        simpa [u] using correction_weighted_prime_eq_zero hf hp (hprime hp)
      have hhalf : (p : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ := by
        exact (inv_le_inv₀ (by exact_mod_cast hp.pos) (by norm_num)).2
          (by exact_mod_cast hp.two_le)
      have hmajor : Summable (fun j : ℕ =>
          2 * ((p : ℝ)⁻¹) ^ 2 * ((2 : ℝ)⁻¹) ^ j) :=
        (summable_geometric_of_norm_lt_one (by norm_num : ‖(2 : ℝ)⁻¹‖ < 1)).mul_left
          (2 * ((p : ℝ)⁻¹) ^ 2)
      have hshift : Summable (fun j : ℕ => u (j + 1)) :=
        (summable_nat_add_iff 1).2 hu
      have htail := hshift.tsum_le_tsum (fun j => by
        calc
          u (j + 1) ≤ 2 * ((p : ℝ)⁻¹) ^ (j + 2) := by
            simpa [u, Nat.add_assoc] using
              correction_weighted_prime_pow_le hf hp (j + 1)
          _ = 2 * ((p : ℝ)⁻¹) ^ 2 * ((p : ℝ)⁻¹) ^ j := by
            rw [pow_add]
            ring
          _ ≤ 2 * ((p : ℝ)⁻¹) ^ 2 * ((2 : ℝ)⁻¹) ^ j := by
            gcongr) hmajor
      rw [show (∑' k : ℕ, u k) = ∑' j : ℕ, u (j + 1) by
        rw [← hu.sum_add_tsum_nat_add 1]
        simp [hu0]]
      calc
        (∑' j : ℕ, u (j + 1)) ≤
            ∑' j : ℕ, 2 * ((p : ℝ)⁻¹) ^ 2 * ((2 : ℝ)⁻¹) ^ j := htail
        _ = 4 * ((p : ℝ)⁻¹) ^ 2 := by
          rw [tsum_mul_left, tsum_geometric_inv_two]
          ring
    · rw [if_neg hp]
      simp

lemma companionTransfer_weighted_eq {f : ℕ → ℝ}
    (hf : IsSignMultiplicative f) (n : ℕ) :
    weightedAbs (companionTransfer f) n =
      weightedAbs (correction (relativeSign f)) n := by
  by_cases hn : n = 0
  · subst n
    simp [weightedAbs, companionTransfer]
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  unfold weightedAbs
  rw [companionTransfer, ArithmeticFunction.pmul_apply,
    companionArithmetic_apply, abs_mul, completeCompanion_abs_eq_one hf hnpos,
    one_mul]

theorem summable_companionTransfer_weighted {f : ℕ → ℝ}
    (hf : IsSignMultiplicative f) :
    Summable (weightedAbs (companionTransfer f)) := by
  apply (summable_correction_weighted_of_prime_one
    (relativeSign_isSignMultiplicative hf) fun hp =>
      relativeSign_prime_eq_one hf hp).congr
  intro n
  exact (companionTransfer_weighted_eq hf n).symm

lemma completeCompanion_prime_pow (f : ℕ → ℝ) {p k : ℕ} (hp : p.Prime) :
    completeCompanion f (p ^ k) = f p ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, completeCompanion_mul f (pow_ne_zero _ hp.ne_zero) hp.ne_zero,
        ih, completeCompanion_prime f hp]
      simp [pow_succ]

lemma completeCorrection_weighted_prime_pow_le {f : ℕ → ℝ}
    (hf : IsSignMultiplicative f) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    weightedAbs (correction (completeCompanion f)) (p ^ (k + 1)) ≤
      2 * ((p : ℝ)⁻¹) ^ (k + 1) := by
  rw [weightedAbs, correction_prime_pow_succ (completeCompanion f) hp k,
    completeCompanion_prime_pow f hp, completeCompanion_prime_pow f hp]
  have hpcast : ((p ^ (k + 1) : ℕ) : ℝ) = (p : ℝ) ^ (k + 1) := by norm_cast
  rw [hpcast]
  have hnum : |f p ^ (k + 1) - f p ^ k| ≤ 2 := by
    calc
      |f p ^ (k + 1) - f p ^ k| ≤ |f p ^ (k + 1)| + |f p ^ k| :=
        abs_sub _ _
      _ = 2 := by
        rw [abs_pow, abs_pow, hf.abs_eq_one hp.one_le]
        norm_num
  have hden : 0 ≤ (p : ℝ) ^ (k + 1) := by positivity
  calc
    |f p ^ (k + 1) - f p ^ k| / (p : ℝ) ^ (k + 1) ≤
        2 / (p : ℝ) ^ (k + 1) := div_le_div_of_nonneg_right hnum hden
    _ = 2 * ((p : ℝ)⁻¹) ^ (k + 1) := by
      rw [inv_pow]
      ring

lemma completeCorrection_weighted_prime_pow_eq_zero_of_pos {f : ℕ → ℝ}
    {p : ℕ} (hp : p.Prime) (hfp : f p = 1) (k : ℕ) :
    weightedAbs (correction (completeCompanion f)) (p ^ (k + 1)) = 0 := by
  rw [weightedAbs, correction_prime_pow_succ (completeCompanion f) hp k,
    completeCompanion_prime_pow f hp, completeCompanion_prime_pow f hp, hfp]
  simp

/-- If the reciprocal series over negative primes converges, the Wintner
correction of the completely multiplicative companion is absolutely
summable with weight `1/n`. -/
theorem summable_completeCorrection_weighted_of_badPrimes {f : ℕ → ℝ}
    (hf : IsSignMultiplicative f)
    (hbad : Summable (badPrimeReciprocal f)) :
    Summable (weightedAbs (correction (completeCompanion f))) := by
  let w := weightedAbs (correction (completeCompanion f))
  have hmult := correction_isMultiplicative (completeCompanion_isSignMultiplicative hf)
  apply summable_of_multiplicative_prime_tails w
    (weightedAbs_zero _) (weightedAbs_one hmult)
    (weightedAbs_nonneg _)
    (fun hcop => weightedAbs_mul_of_coprime hmult hcop)
  · intro p hp
    have hpR : ‖(p : ℝ)⁻¹‖ < 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
    have hgeom : Summable (fun k : ℕ =>
        2 * ((p : ℝ)⁻¹) ^ (k + 1)) :=
      by
        simpa only [pow_succ, mul_assoc, mul_left_comm, mul_comm] using
          (summable_geometric_of_norm_lt_one hpR).mul_left (2 * (p : ℝ)⁻¹)
    exact Summable.of_nonneg_of_le (fun k => weightedAbs_nonneg _ _)
      (fun k => completeCorrection_weighted_prime_pow_le hf hp k) hgeom
  · have hmajor : Summable (fun p : ℕ => 4 * badPrimeReciprocal f p) :=
      hbad.mul_left 4
    apply Summable.of_nonneg_of_le
      (fun p => by
        split_ifs
        · exact tsum_nonneg fun _ => weightedAbs_nonneg _ _
        · exact le_rfl)
      ?_ hmajor
    intro p
    by_cases hp : p.Prime
    · rw [if_pos hp]
      rcases hf.sign hp.one_le with hfp | hfp
      · have hzero : (fun k : ℕ =>
            weightedAbs (correction (completeCompanion f)) (p ^ (k + 1))) = 0 := by
          funext k
          exact completeCorrection_weighted_prime_pow_eq_zero_of_pos hp hfp k
        rw [hzero]
        change (∑' _k : ℕ, (0 : ℝ)) ≤ 4 * badPrimeReciprocal f p
        rw [tsum_zero]
        simp [badPrimeReciprocal, hp, hfp]
        norm_num
      · have hpR : ‖(p : ℝ)⁻¹‖ < 1 := by
          rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
          exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
        have hgeom : Summable (fun k : ℕ =>
            2 * ((p : ℝ)⁻¹) ^ (k + 1)) :=
          by
            simpa only [pow_succ, mul_assoc, mul_left_comm, mul_comm] using
              (summable_geometric_of_norm_lt_one hpR).mul_left (2 * (p : ℝ)⁻¹)
        have hlocal : Summable (fun k : ℕ =>
            weightedAbs (correction (completeCompanion f)) (p ^ (k + 1))) :=
          Summable.of_nonneg_of_le (fun k => weightedAbs_nonneg _ _)
            (fun k => completeCorrection_weighted_prime_pow_le hf hp k) hgeom
        have htsum := hlocal.tsum_le_tsum
          (fun k => completeCorrection_weighted_prime_pow_le hf hp k) hgeom
        rw [show (∑' k : ℕ, 2 * ((p : ℝ)⁻¹) ^ (k + 1)) =
            2 * (p : ℝ)⁻¹ * (1 - (p : ℝ)⁻¹)⁻¹ by
          calc
            (∑' k : ℕ, 2 * ((p : ℝ)⁻¹) ^ (k + 1)) =
                ∑' k : ℕ, (2 * (p : ℝ)⁻¹) * ((p : ℝ)⁻¹) ^ k := by
              apply tsum_congr
              intro k
              rw [pow_succ]
              ring
            _ = (2 * (p : ℝ)⁻¹) * ∑' k : ℕ, ((p : ℝ)⁻¹) ^ k :=
              tsum_mul_left
            _ = 2 * (p : ℝ)⁻¹ * (1 - (p : ℝ)⁻¹)⁻¹ := by
              rw [tsum_geometric_of_norm_lt_one hpR]] at htsum
        rw [badPrimeReciprocal, if_pos ⟨hp, hfp⟩]
        have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
        have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
        have hpm1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
        calc
          (∑' k : ℕ, weightedAbs (correction (completeCompanion f))
              (p ^ (k + 1))) ≤
              2 * (p : ℝ)⁻¹ * (1 - (p : ℝ)⁻¹)⁻¹ := htsum
          _ ≤ 4 * (p : ℝ)⁻¹ := by
            field_simp
            nlinarith
    · rw [if_neg hp]
      simp [badPrimeReciprocal, hp]

/-- The convergent branch of Wirsing's theorem, isolated with its exact
Möbius-correction summability hypothesis. -/
theorem tendsto_mean_of_correction_summable {f : ℕ → ℝ}
    (_hf : IsSignMultiplicative f)
    (hsum : Summable fun n : ℕ => |correction f n| / (n : ℝ)) :
    Tendsto (meanUpTo f) atTop
      (𝓝 (∑' n : ℕ, correction f n / (n : ℝ))) := by
  have h := tendsto_mean_dirichlet_mul_zeta (correction f) hsum
  rw [correction_mul_zeta] at h
  convert h using 1
  ext N
  have hsets : Finset.Ioc 0 N = Finset.Icc 1 N := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  rw [hsets]
  simp only [meanUpTo]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  exact (arithmeticFunction_apply_of_pos f (Finset.mem_Icc.mp hn).1).symm

lemma arithmeticMean_arithmeticFunction_eq_meanUpTo (f : ℕ → ℝ) (N : ℕ) :
    arithmeticMean (arithmeticFunction f) N = meanUpTo f N := by
  have hsets : Finset.Ioc 0 N = Finset.Icc 1 N := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  rw [arithmeticMean, meanUpTo, hsets]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  exact arithmeticFunction_apply_of_pos f (Finset.mem_Icc.mp hn).1

lemma companionArithmetic_eq_arithmeticFunction (f : ℕ → ℝ) :
    companionArithmetic f = arithmeticFunction (completeCompanion f) := by
  ext n
  by_cases hn : n = 0
  · subst n
    simp
  · rw [companionArithmetic_apply,
      arithmeticFunction_apply_of_pos _ (Nat.pos_of_ne_zero hn)]

lemma arithmeticMean_companion_eq_meanUpTo (f : ℕ → ℝ) (N : ℕ) :
    arithmeticMean (companionArithmetic f) N =
      meanUpTo (completeCompanion f) N := by
  rw [companionArithmetic_eq_arithmeticFunction,
    arithmeticMean_arithmeticFunction_eq_meanUpTo]

/-- Any Cesàro limit of the complete companion transfers to the original
multiplicative function through an absolutely summable convolution. -/
theorem tendsto_mean_of_companion_mean {f : ℕ → ℝ}
    (hf : IsSignMultiplicative f) {L : ℝ}
    (hc : Tendsto (meanUpTo (completeCompanion f)) atTop (𝓝 L)) :
    Tendsto (meanUpTo f) atTop
      (𝓝 ((∑' n : ℕ, companionTransfer f n / (n : ℝ)) * L)) := by
  have hcAF : Tendsto (arithmeticMean (companionArithmetic f)) atTop (𝓝 L) := by
    convert hc using 1
    ext N
    exact arithmeticMean_companion_eq_meanUpTo f N
  have hbound : ∀ N : ℕ, |arithmeticMean (companionArithmetic f) N| ≤ 1 := by
    intro N
    rw [arithmeticMean_companion_eq_meanUpTo]
    exact abs_meanUpTo_le_one (completeCompanion_isSignMultiplicative hf) N
  have hsum : Summable fun n : ℕ => |companionTransfer f n| / (n : ℝ) := by
    change Summable (weightedAbs (companionTransfer f))
    exact summable_companionTransfer_weighted hf
  have h := tendsto_mean_dirichlet_mul_of_mean
    (companionTransfer f) (companionArithmetic f) L hcAF hbound hsum
  rw [companionTransfer_mul_companion hf] at h
  convert h using 1
  ext N
  exact (arithmeticMean_arithmeticFunction_eq_meanUpTo f N).symm

/-- Erdős Problem 239: every multiplicative `{-1,1}`-valued function has a
Cesàro mean. -/
theorem erdos_239 :
    ∀ f : ℕ → ℝ,
    (∀ n ≥ 1, f n = 1 ∨ f n = -1) ∧
    (∀ m n, m.Coprime n → f (m * n) = f m * f n) ∧
    f 1 = 1 →
    ∃ L, Tendsto (fun N ↦ (∑ n ∈ Finset.Icc 1 N, f n) / N)
      atTop (𝓝 L) := by
  refine Iff.mp ?_ trivial
  simp only [true_iff]
  intro f hf
  change IsSignMultiplicative f at hf
  change ∃ L, Tendsto (meanUpTo f) atTop (𝓝 L)
  by_cases hbad : Summable (badPrimeReciprocal f)
  · have hsum := summable_completeCorrection_weighted_of_badPrimes hf hbad
    have hc := tendsto_mean_of_correction_summable
      (completeCompanion_isSignMultiplicative hf) (by
        change Summable (weightedAbs (correction (completeCompanion f)))
        exact hsum)
    refine ⟨(∑' n : ℕ, companionTransfer f n / (n : ℝ)) *
        (∑' n : ℕ, correction (completeCompanion f) n / (n : ℝ)), ?_⟩
    exact tendsto_mean_of_companion_mean hf hc
  · refine ⟨0, ?_⟩
    have hc := tendsto_completeCompanion_mean_zero_of_not_summable_badPrimes hf hbad
    simpa only [mul_zero] using tendsto_mean_of_companion_mean hf hc

end Erdos239
