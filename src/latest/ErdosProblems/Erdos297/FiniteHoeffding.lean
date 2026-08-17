/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos297.WeightedFourier
import ErdosProblems.Erdos297.GoodFactorization
import ErdosProblems.Erdos297.Parameters
import ErdosProblems.Erdos285.Proposition7Mass

/-!
# A finite Hoeffding inequality for Bernoulli subset sums

This file proves the concentration estimate needed in the lower-bound
argument for Erdős problem 297 without introducing a probability space.  A
product Bernoulli law is simply a nonnegative weight on `I.powerset`, and all
expectations are finite sums.

We use the slightly weaker (but especially convenient) subgaussian constant
`1`: a centered Bernoulli variable with range of length one satisfies

`E exp (z X) <= exp (z^2 / 2)`.

Consequently a weighted sum with coefficients `x i` has two-sided tail at
most `2 * exp (-t^2 / (2 * sum_i (x i)^2))`.  This is sufficient for the
Liu--Sawhney argument and gives the reciprocal specialization
`2 * exp (-M^2 / (2N))` for denominators in `[M,N]`.
-/

open Filter Finset
open scoped BigOperators

namespace Erdos297.FiniteHoeffding

noncomputable section

attribute [local instance] Classical.propDecidable

variable {ι : Type*} [DecidableEq ι]

/-- The centered additive statistic associated with a Bernoulli subset.
The value at coordinate `i` is `(1-p i) * x i` when selected and
`-p i * x i` when omitted. -/
def centeredSubsetSum (I : Finset ι) (p x : ι → ℝ) (B : Finset ι) : ℝ :=
  ∑ i ∈ I, if i ∈ B then (1 - p i) * x i else -p i * x i

/-- The uncentered subset statistic. -/
def subsetSum (B : Finset ι) (x : ι → ℝ) : ℝ :=
  ∑ i ∈ B, x i

/-- The mean of the uncentered subset statistic under the product weights. -/
def subsetMean (I : Finset ι) (p x : ι → ℝ) : ℝ :=
  ∑ i ∈ I, p i * x i

/-- The sum of squared coefficients, used as a variance proxy. -/
def squareSum (I : Finset ι) (x : ι → ℝ) : ℝ :=
  ∑ i ∈ I, (x i) ^ 2

/-- Weighted mass of an event on the finite powerset. -/
def eventMass (I : Finset ι) (p : ι → ℝ) (E : Finset ι → Prop) : ℝ :=
  ∑ B ∈ I.powerset, if E B then
    Erdos297.WeightedFourier.subsetWeight I p B else 0

/-- The centered and uncentered descriptions agree on subsets of `I`. -/
lemma centeredSubsetSum_eq_sub {I B : Finset ι} {p x : ι → ℝ}
    (hB : B ⊆ I) :
    centeredSubsetSum I p x B = subsetSum B x - subsetMean I p x := by
  rw [centeredSubsetSum, subsetSum, subsetMean, Finset.sum_ite]
  have hfilter : I.filter (fun i => i ∈ B) = B := by
    ext i
    simp [hB]
  have hfilterc : I.filter (fun i => ¬i ∈ B) = I \ B := by
    ext i
    simp
  rw [hfilter, hfilterc]
  have hsplit := Finset.sum_sdiff (s₁ := B) (s₂ := I)
    (f := fun i => p i * x i) hB
  have hselected :
      (∑ i ∈ B, (1 - p i) * x i) =
        (∑ i ∈ B, x i) - ∑ i ∈ B, p i * x i := by
    calc
      (∑ i ∈ B, (1 - p i) * x i) =
          ∑ i ∈ B, (x i - p i * x i) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = (∑ i ∈ B, x i) - ∑ i ∈ B, p i * x i :=
        by rw [Finset.sum_sub_distrib]
  have homitted :
      (∑ i ∈ I \ B, -p i * x i) =
        -(∑ i ∈ I \ B, p i * x i) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hselected, homitted, ← hsplit]
  ring

/-- Every centered one-coordinate Bernoulli exponential moment is bounded by
`exp (z^2 x^2 / 2)`.  This elementary lemma is the analytic heart of the
finite Hoeffding argument. -/
lemma bernoulli_centered_exp_le {p x z : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (1 - p) * Real.exp (z * (-p * x)) +
        p * Real.exp (z * ((1 - p) * x)) ≤
      Real.exp ((z * x) ^ 2 / 2) := by
  have hneg : |-p| ≤ (1 : ℝ) := by
    rw [abs_of_nonpos (neg_nonpos.mpr hp0)]
    linarith
  have hpos : |1 - p| ≤ (1 : ℝ) := by
    rw [abs_of_nonneg (sub_nonneg.mpr hp1)]
    linarith
  have h₀ := Real.exp_mul_le_cosh_add_mul_sinh hneg (z * x)
  have h₁ := Real.exp_mul_le_cosh_add_mul_sinh hpos (z * x)
  have hmul₀ := mul_le_mul_of_nonneg_left h₀ (sub_nonneg.mpr hp1)
  have hmul₁ := mul_le_mul_of_nonneg_left h₁ hp0
  calc
    (1 - p) * Real.exp (z * (-p * x)) +
          p * Real.exp (z * ((1 - p) * x)) =
        (1 - p) * Real.exp ((-p) * (z * x)) +
          p * Real.exp ((1 - p) * (z * x)) := by ring_nf
    _ ≤ (1 - p) * (Real.cosh (z * x) + (-p) * Real.sinh (z * x)) +
          p * (Real.cosh (z * x) + (1 - p) * Real.sinh (z * x)) :=
      add_le_add hmul₀ hmul₁
    _ = Real.cosh (z * x) := by ring
    _ ≤ Real.exp ((z * x) ^ 2 / 2) := Real.cosh_le_exp_half_sq _

/-- A product Bernoulli atom times the exponential of its centered statistic
factors coordinate by coordinate. -/
lemma subsetWeight_mul_exp_centered {I B : Finset ι} {p x : ι → ℝ}
    (hB : B ⊆ I) (z : ℝ) :
    Erdos297.WeightedFourier.subsetWeight I p B *
        Real.exp (z * centeredSubsetSum I p x B) =
      (∏ i ∈ B, p i * Real.exp (z * ((1 - p i) * x i))) *
        ∏ i ∈ I \ B, (1 - p i) * Real.exp (z * (-p i * x i)) := by
  rw [Erdos297.WeightedFourier.subsetWeight, centeredSubsetSum, Finset.sum_ite]
  have hfilter : I.filter (fun i => i ∈ B) = B := by
    ext i
    simp [hB]
  have hfilterc : I.filter (fun i => ¬i ∈ B) = I \ B := by
    ext i
    simp
  rw [hfilter, hfilterc, mul_add, Finset.mul_sum, Finset.mul_sum,
    Real.exp_add, Real.exp_sum, Real.exp_sum,
    Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  ring

/-- Exact finite moment-generating-function factorization. -/
lemma sum_weight_mul_exp_centered (I : Finset ι) (p x : ι → ℝ) (z : ℝ) :
    (∑ B ∈ I.powerset,
      Erdos297.WeightedFourier.subsetWeight I p B *
        Real.exp (z * centeredSubsetSum I p x B)) =
      ∏ i ∈ I,
        ((1 - p i) * Real.exp (z * (-p i * x i)) +
          p i * Real.exp (z * ((1 - p i) * x i))) := by
  calc
    (∑ B ∈ I.powerset,
        Erdos297.WeightedFourier.subsetWeight I p B *
          Real.exp (z * centeredSubsetSum I p x B)) =
        ∑ B ∈ I.powerset,
          (∏ i ∈ B, p i * Real.exp (z * ((1 - p i) * x i))) *
            ∏ i ∈ I \ B, (1 - p i) * Real.exp (z * (-p i * x i)) := by
      apply Finset.sum_congr rfl
      intro B hB
      exact subsetWeight_mul_exp_centered (Finset.mem_powerset.mp hB) z
    _ = ∏ i ∈ I,
        (p i * Real.exp (z * ((1 - p i) * x i)) +
          (1 - p i) * Real.exp (z * (-p i * x i))) := by
      exact (Finset.prod_add
        (fun i => p i * Real.exp (z * ((1 - p i) * x i)))
        (fun i => (1 - p i) * Real.exp (z * (-p i * x i))) I).symm
    _ = ∏ i ∈ I,
        ((1 - p i) * Real.exp (z * (-p i * x i)) +
          p i * Real.exp (z * ((1 - p i) * x i))) := by
      apply Finset.prod_congr rfl
      intro i hi
      ring

/-- Finite subgaussian MGF bound for an inhomogeneous Bernoulli subset sum. -/
theorem mgf_le (I : Finset ι) (p x : ι → ℝ)
    (hp0 : ∀ i ∈ I, 0 ≤ p i) (hp1 : ∀ i ∈ I, p i ≤ 1) (z : ℝ) :
    (∑ B ∈ I.powerset,
      Erdos297.WeightedFourier.subsetWeight I p B *
        Real.exp (z * centeredSubsetSum I p x B)) ≤
      Real.exp (z ^ 2 * squareSum I x / 2) := by
  rw [sum_weight_mul_exp_centered]
  calc
    (∏ i ∈ I,
        ((1 - p i) * Real.exp (z * (-p i * x i)) +
          p i * Real.exp (z * ((1 - p i) * x i)))) ≤
        ∏ i ∈ I, Real.exp ((z * x i) ^ 2 / 2) := by
      apply Finset.prod_le_prod
      · intro i hi
        exact add_nonneg
          (mul_nonneg (sub_nonneg.mpr (hp1 i hi)) (Real.exp_nonneg _))
          (mul_nonneg (hp0 i hi) (Real.exp_nonneg _))
      · intro i hi
        exact bernoulli_centered_exp_le (hp0 i hi) (hp1 i hi)
    _ = Real.exp (z ^ 2 * squareSum I x / 2) := by
      rw [← Real.exp_sum]
      congr 1
      rw [squareSum, Finset.mul_sum, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i hi
      ring

/-- Chernoff's bound at an arbitrary nonnegative exponential parameter. -/
theorem upperTail_le_exp (I : Finset ι) (p x : ι → ℝ)
    (hp0 : ∀ i ∈ I, 0 ≤ p i) (hp1 : ∀ i ∈ I, p i ≤ 1)
    {t z : ℝ} (hz : 0 ≤ z) :
    eventMass I p (fun B => t ≤ centeredSubsetSum I p x B) ≤
      Real.exp (-z * t + z ^ 2 * squareSum I x / 2) := by
  calc
    eventMass I p (fun B => t ≤ centeredSubsetSum I p x B) ≤
        Real.exp (-z * t) *
          ∑ B ∈ I.powerset,
            Erdos297.WeightedFourier.subsetWeight I p B *
              Real.exp (z * centeredSubsetSum I p x B) := by
      rw [eventMass, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro B hB
      have hw := Erdos297.WeightedFourier.subsetWeight_nonneg
        I p hp0 hp1 hB
      split_ifs with htail
      · have hw := Erdos297.WeightedFourier.subsetWeight_nonneg
          I p hp0 hp1 hB
        have hexp : 1 ≤ Real.exp (-z * t) *
            Real.exp (z * centeredSubsetSum I p x B) := by
          rw [← Real.exp_add, ← Real.exp_zero]
          apply Real.exp_le_exp.mpr
          nlinarith
        nlinarith [mul_le_mul_of_nonneg_left hexp hw]
      · exact mul_nonneg (Real.exp_nonneg _)
          (mul_nonneg hw (Real.exp_nonneg _))
    _ ≤ Real.exp (-z * t) *
          Real.exp (z ^ 2 * squareSum I x / 2) := by
      exact mul_le_mul_of_nonneg_left (mgf_le I p x hp0 hp1 z)
        (Real.exp_nonneg _)
    _ = Real.exp (-z * t + z ^ 2 * squareSum I x / 2) := by
      rw [Real.exp_add]

/-- The lower tail has the same Chernoff bound. -/
theorem lowerTail_le_exp (I : Finset ι) (p x : ι → ℝ)
    (hp0 : ∀ i ∈ I, 0 ≤ p i) (hp1 : ∀ i ∈ I, p i ≤ 1)
    {t z : ℝ} (hz : 0 ≤ z) :
    eventMass I p (fun B => centeredSubsetSum I p x B ≤ -t) ≤
      Real.exp (-z * t + z ^ 2 * squareSum I x / 2) := by
  have hcenter (B : Finset ι) :
      centeredSubsetSum I p (fun i => -x i) B =
        -centeredSubsetSum I p x B := by
    rw [centeredSubsetSum, centeredSubsetSum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    split_ifs <;> ring
  have hsquare : squareSum I (fun i => -x i) = squareSum I x := by
    apply Finset.sum_congr rfl
    intro i hi
    simp
  simpa only [hcenter, le_neg, hsquare] using
    (upperTail_le_exp I p (fun i => -x i) hp0 hp1 (t := t) hz)

/-- Two-sided Chernoff bound at an arbitrary nonnegative parameter. -/
theorem absTail_le_two_mul_exp (I : Finset ι) (p x : ι → ℝ)
    (hp0 : ∀ i ∈ I, 0 ≤ p i) (hp1 : ∀ i ∈ I, p i ≤ 1)
    {t z : ℝ} (_ht : 0 ≤ t) (hz : 0 ≤ z) :
    eventMass I p (fun B => t ≤ |centeredSubsetSum I p x B|) ≤
      2 * Real.exp (-z * t + z ^ 2 * squareSum I x / 2) := by
  calc
    eventMass I p (fun B => t ≤ |centeredSubsetSum I p x B|) ≤
        eventMass I p (fun B => t ≤ centeredSubsetSum I p x B) +
          eventMass I p (fun B => centeredSubsetSum I p x B ≤ -t) := by
      rw [eventMass, eventMass, eventMass, ← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro B hB
      have hw := Erdos297.WeightedFourier.subsetWeight_nonneg
        I p hp0 hp1 hB
      by_cases habs : t ≤ |centeredSubsetSum I p x B|
      · rcases le_abs.mp habs with hup | hlow
        · rw [if_pos habs, if_pos hup]
          exact le_add_of_nonneg_right (ite_nonneg hw le_rfl)
        · have hlow' : centeredSubsetSum I p x B ≤ -t := le_neg.mp hlow
          rw [if_pos habs, if_pos hlow']
          exact le_add_of_nonneg_left (ite_nonneg hw le_rfl)
      · rw [if_neg habs]
        exact add_nonneg (ite_nonneg hw le_rfl) (ite_nonneg hw le_rfl)
    _ ≤ Real.exp (-z * t + z ^ 2 * squareSum I x / 2) +
          Real.exp (-z * t + z ^ 2 * squareSum I x / 2) :=
      add_le_add (upperTail_le_exp I p x hp0 hp1 hz)
        (lowerTail_le_exp I p x hp0 hp1 hz)
    _ = 2 * Real.exp (-z * t + z ^ 2 * squareSum I x / 2) := by ring

/-- The optimized finite Hoeffding inequality.  The convention `0⁻¹ = 0`
makes the displayed right side equal to `2` when all coefficients vanish;
that degenerate case is handled separately in the proof. -/
theorem abs_centeredSubsetSum_tail (I : Finset ι) (p x : ι → ℝ)
    (hp0 : ∀ i ∈ I, 0 ≤ p i) (hp1 : ∀ i ∈ I, p i ≤ 1)
    {t : ℝ} (ht : 0 ≤ t) :
    eventMass I p (fun B => t ≤ |centeredSubsetSum I p x B|) ≤
      2 * Real.exp (-(t ^ 2) / (2 * squareSum I x)) := by
  have hsq0 : 0 ≤ squareSum I x := by
    exact Finset.sum_nonneg fun i hi => sq_nonneg (x i)
  rcases hsq0.eq_or_lt with hzero | hpos
  · have hmass : eventMass I p
        (fun B => t ≤ |centeredSubsetSum I p x B|) ≤ 1 := by
      calc
        eventMass I p (fun B => t ≤ |centeredSubsetSum I p x B|) ≤
            ∑ B ∈ I.powerset,
              Erdos297.WeightedFourier.subsetWeight I p B := by
          rw [eventMass]
          apply Finset.sum_le_sum
          intro B hB
          split_ifs
          · exact le_rfl
          · exact Erdos297.WeightedFourier.subsetWeight_nonneg
              I p hp0 hp1 hB
        _ = 1 := Erdos297.WeightedFourier.sum_subsetWeight I p
    rw [← hzero]
    norm_num
    exact hmass.trans (by norm_num)
  · have hchernoff := absTail_le_two_mul_exp I p x hp0 hp1 ht
      (z := t / squareSum I x) (div_nonneg ht hpos.le)
    convert hchernoff using 1
    congr 2
    field_simp [ne_of_gt hpos]
    ring

/-- Uncentered form of the optimized inequality. -/
theorem abs_subsetSum_sub_mean_tail (I : Finset ι) (p x : ι → ℝ)
    (hp0 : ∀ i ∈ I, 0 ≤ p i) (hp1 : ∀ i ∈ I, p i ≤ 1)
    {t : ℝ} (ht : 0 ≤ t) :
    eventMass I p (fun B =>
        t ≤ |subsetSum B x - subsetMean I p x|) ≤
      2 * Real.exp (-(t ^ 2) / (2 * squareSum I x)) := by
  have heq :
      eventMass I p (fun B => t ≤ |centeredSubsetSum I p x B|) =
        eventMass I p (fun B =>
          t ≤ |subsetSum B x - subsetMean I p x|) := by
    rw [eventMass, eventMass]
    apply Finset.sum_congr rfl
    intro B hB
    rw [centeredSubsetSum_eq_sub (Finset.mem_powerset.mp hB)]
  rw [← heq]
  exact abs_centeredSubsetSum_tail I p x hp0 hp1 ht

/-- Version centered at a named target, for applications where the Bernoulli
parameters were chosen so that their finite mean is exactly that target. -/
theorem abs_subsetSum_sub_target_tail (I : Finset ι) (p x : ι → ℝ)
    (hp0 : ∀ i ∈ I, 0 ≤ p i) (hp1 : ∀ i ∈ I, p i ≤ 1)
    {target t : ℝ} (hmean : subsetMean I p x = target) (ht : 0 ≤ t) :
    eventMass I p (fun B => t ≤ |subsetSum B x - target|) ≤
      2 * Real.exp (-(t ^ 2) / (2 * squareSum I x)) := by
  rw [← hmean]
  exact abs_subsetSum_sub_mean_tail I p x hp0 hp1 ht

/-! ## Reciprocal coefficients -/

/-- If every index lies in the integer interval `[M,N]` and `M` is positive,
then the sum of squared reciprocal coefficients is at most `N / M^2`. -/
lemma squareSum_reciprocal_le {I : Finset ℕ} {M N : ℕ}
    (hM : 0 < M) (hI : I ⊆ Finset.Icc M N) :
    squareSum I (fun n : ℕ => ((n : ℝ)⁻¹)) ≤
      (N : ℝ) / (M : ℝ) ^ 2 := by
  have hcardI : I.card ≤ N := by
    have hcard := Finset.card_le_card hI
    have hinterval : (Finset.Icc M N).card = N + 1 - M := by simp
    rw [hinterval] at hcard
    omega
  calc
    squareSum I (fun n : ℕ => ((n : ℝ)⁻¹)) ≤
        ∑ _n ∈ I, ((M : ℝ)⁻¹) ^ 2 := by
      rw [squareSum]
      apply Finset.sum_le_sum
      intro n hn
      have hMn : M ≤ n := (Finset.mem_Icc.mp (hI hn)).1
      have hMreal : 0 < (M : ℝ) := by exact_mod_cast hM
      have hinv : (n : ℝ)⁻¹ ≤ (M : ℝ)⁻¹ :=
        inv_anti₀ hMreal (by exact_mod_cast hMn)
      exact (sq_le_sq₀ (inv_nonneg.mpr (Nat.cast_nonneg n))
        (inv_nonneg.mpr (Nat.cast_nonneg M))).2 hinv
    _ = (I.card : ℝ) * ((M : ℝ)⁻¹) ^ 2 := by simp
    _ ≤ (N : ℝ) * ((M : ℝ)⁻¹) ^ 2 := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcardI) (sq_nonneg _)
    _ = (N : ℝ) / (M : ℝ) ^ 2 := by
      have hMreal : (M : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hM)
      field_simp

/-- Reciprocal specialization of finite Hoeffding.  For arbitrary Bernoulli
probabilities and denominators in `[M,N]`, the weighted mass on which the
centered reciprocal sum differs from zero by at least one is at most
`2 * exp (-M^2/(2N))`. -/
theorem abs_centered_reciprocal_tail {I : Finset ℕ} (p : ℕ → ℝ)
    {M N : ℕ} (hM : 0 < M) (hMN : M ≤ N)
    (hI : I ⊆ Finset.Icc M N)
    (hp0 : ∀ n ∈ I, 0 ≤ p n) (hp1 : ∀ n ∈ I, p n ≤ 1) :
    eventMass I p (fun B =>
        1 ≤ |centeredSubsetSum I p (fun n : ℕ => ((n : ℝ)⁻¹)) B|) ≤
      2 * Real.exp (-((M : ℝ) ^ 2) / (2 * (N : ℝ))) := by
  have hN : 0 < N := lt_of_lt_of_le hM hMN
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hMreal : 0 < (M : ℝ) := by exact_mod_cast hM
  let z : ℝ := (M : ℝ) ^ 2 / (N : ℝ)
  have hz : 0 ≤ z := by
    dsimp [z]
    positivity
  have htail := absTail_le_two_mul_exp I p
    (fun n : ℕ => ((n : ℝ)⁻¹)) hp0 hp1 (t := (1 : ℝ)) (z := z)
    (by norm_num) hz
  calc
    eventMass I p (fun B =>
        1 ≤ |centeredSubsetSum I p (fun n : ℕ => ((n : ℝ)⁻¹)) B|) ≤
        2 * Real.exp
          (-z * 1 + z ^ 2 *
            squareSum I (fun n : ℕ => ((n : ℝ)⁻¹)) / 2) := htail
    _ ≤ 2 * Real.exp (-((M : ℝ) ^ 2) / (2 * (N : ℝ))) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Real.exp_le_exp.mpr
      have hsquare := squareSum_reciprocal_le hM hI
      dsimp [z]
      have hzsq : 0 ≤ ((M : ℝ) ^ 2 / (N : ℝ)) ^ 2 := sq_nonneg _
      have hmul := mul_le_mul_of_nonneg_left hsquare hzsq
      field_simp [ne_of_gt hNreal, ne_of_gt hMreal] at hmul ⊢
      nlinarith [sq_nonneg (M : ℝ), sq_nonneg (N : ℝ)]

/-- The same reciprocal specialization written as deviation from the explicit
finite mean. -/
theorem abs_reciprocal_sum_sub_mean_tail {I : Finset ℕ} (p : ℕ → ℝ)
    {M N : ℕ} (hM : 0 < M) (hMN : M ≤ N)
    (hI : I ⊆ Finset.Icc M N)
    (hp0 : ∀ n ∈ I, 0 ≤ p n) (hp1 : ∀ n ∈ I, p n ≤ 1) :
    eventMass I p (fun B =>
        1 ≤ |subsetSum B (fun n : ℕ => ((n : ℝ)⁻¹)) -
          subsetMean I p (fun n : ℕ => ((n : ℝ)⁻¹))|) ≤
      2 * Real.exp (-((M : ℝ) ^ 2) / (2 * (N : ℝ))) := by
  have heq :
      eventMass I p (fun B =>
          1 ≤ |centeredSubsetSum I p (fun n : ℕ => ((n : ℝ)⁻¹)) B|) =
        eventMass I p (fun B =>
          1 ≤ |subsetSum B (fun n : ℕ => ((n : ℝ)⁻¹)) -
            subsetMean I p (fun n : ℕ => ((n : ℝ)⁻¹))|) := by
    rw [eventMass, eventMass]
    apply Finset.sum_congr rfl
    intro B hB
    rw [centeredSubsetSum_eq_sub (Finset.mem_powerset.mp hB)]
  rw [← heq]
  exact abs_centered_reciprocal_tail p hM hMN hI hp0 hp1

/-! ## The numerical off-lattice bound -/

/-- The common smooth denominator is eventually at most `exp (5S)`.  The
constant `5` leaves ample room beyond the explicit Chebyshev bound `2` proved
in the Erdős 285 development. -/
theorem eventually_smoothLcm_le_exp_five_mul :
    ∀ᶠ S : ℕ in atTop,
      (Erdos297.GoodFactorization.smoothLcm S : ℝ) ≤
        Real.exp (5 * (S : ℝ)) := by
  filter_upwards
    [Erdos285.Proposition7Mass.eventually_initialLcm_le_exp_two_mul]
      with S hS
  exact hS.trans (Real.exp_monotone (by
    have hS0 : (0 : ℝ) ≤ (S : ℝ) := Nat.cast_nonneg S
    nlinarith))

/-- The finite numerical comparison used to discard nonzero integral
translates.  The scale inequality with the concrete constant `24`, together
with `Q(S) ≤ exp (5S)`, makes the reciprocal Hoeffding tail at most
`1 / (4 Q(S))`. -/
theorem abs_reciprocal_sum_sub_mean_tail_le_inv_four_smoothLcm
    {I : Finset ℕ} (p : ℕ → ℝ) {M N S : ℕ}
    (hM : 0 < M) (hMN : M ≤ N) (hS : 1 ≤ S)
    (hI : I ⊆ Finset.Icc M N)
    (hp0 : ∀ n ∈ I, 0 ≤ p n) (hp1 : ∀ n ∈ I, p n ≤ 1)
    (hscale : (24 : ℝ) * (N : ℝ) * (S : ℝ) ≤ (M : ℝ) ^ 2)
    (hQ : (Erdos297.GoodFactorization.smoothLcm S : ℝ) ≤
      Real.exp (5 * (S : ℝ))) :
    eventMass I p (fun B =>
        1 ≤ |subsetSum B (fun n : ℕ => ((n : ℝ)⁻¹)) -
          subsetMean I p (fun n : ℕ => ((n : ℝ)⁻¹))|) ≤
      1 / (4 *
        (Erdos297.GoodFactorization.smoothLcm S : ℝ)) := by
  have hN : 0 < N := lt_of_lt_of_le hM hMN
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hSreal : (1 : ℝ) ≤ (S : ℝ) := by exact_mod_cast hS
  have hQpos : 0 <
      (Erdos297.GoodFactorization.smoothLcm S : ℝ) := by
    exact_mod_cast Nat.lcmUpto_pos S
  have hscaleDiv :
      12 * (S : ℝ) ≤ (M : ℝ) ^ 2 / (2 * (N : ℝ)) := by
    rw [le_div_iff₀ (mul_pos (by norm_num) hNreal)]
    nlinarith
  have hexpEight : (8 : ℝ) ≤ Real.exp (7 * (S : ℝ)) := by
    calc
      (8 : ℝ) = 7 + 1 := by norm_num
      _ ≤ Real.exp 7 := by simpa using Real.add_one_le_exp 7
      _ ≤ Real.exp (7 * (S : ℝ)) :=
        Real.exp_monotone (by nlinarith)
  calc
    eventMass I p (fun B =>
        1 ≤ |subsetSum B (fun n : ℕ => ((n : ℝ)⁻¹)) -
          subsetMean I p (fun n : ℕ => ((n : ℝ)⁻¹))|) ≤
        2 * Real.exp (-((M : ℝ) ^ 2) / (2 * (N : ℝ))) :=
      abs_reciprocal_sum_sub_mean_tail p hM hMN hI hp0 hp1
    _ ≤ 2 * Real.exp (-12 * (S : ℝ)) := by
      exact mul_le_mul_of_nonneg_left
        (Real.exp_monotone (by
          calc
            -((M : ℝ) ^ 2) / (2 * (N : ℝ)) =
                -((M : ℝ) ^ 2 / (2 * (N : ℝ))) := by ring
            _ ≤ -(12 * (S : ℝ)) := neg_le_neg hscaleDiv
            _ = -12 * (S : ℝ) := by ring)) (by norm_num)
    _ ≤ 1 / (4 *
        (Erdos297.GoodFactorization.smoothLcm S : ℝ)) := by
      rw [le_div_iff₀ (mul_pos (by norm_num) hQpos)]
      calc
        2 * Real.exp (-12 * (S : ℝ)) *
              (4 * (Erdos297.GoodFactorization.smoothLcm S : ℝ)) =
            8 * (Erdos297.GoodFactorization.smoothLcm S : ℝ) *
              Real.exp (-12 * (S : ℝ)) := by ring
        _ ≤ 8 * Real.exp (5 * (S : ℝ)) *
              Real.exp (-12 * (S : ℝ)) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hQ (by norm_num))
            (Real.exp_nonneg _)
        _ = 8 * Real.exp (-7 * (S : ℝ)) := by
          rw [mul_assoc, ← Real.exp_add]
          congr 1
          ring_nf
        _ ≤ Real.exp (7 * (S : ℝ)) *
              Real.exp (-7 * (S : ℝ)) :=
          mul_le_mul_of_nonneg_right hexpEight (Real.exp_nonneg _)
        _ = 1 := by rw [← Real.exp_add]; ring_nf; simp

/-- The rounded smoothness cutoff `S(N)` tends to infinity. -/
theorem tendsto_S_atTop : Tendsto Erdos297.S atTop atTop := by
  have hpow : Tendsto Erdos297.almostOnePower atTop atTop := by
    exact (tendsto_rpow_atTop
      (by norm_num : (0 : ℝ) < (9999 : ℝ) / 10000)).comp
        tendsto_natCast_atTop_atTop
  apply tendsto_atTop.mpr
  intro b
  filter_upwards
    [Erdos297.eventually_almostOnePower_le_natS,
      hpow.eventually_ge_atTop (b : ℝ)] with N hSN hb
  exact_mod_cast hb.trans hSN

/-- For the actual rounded Liu--Sawhney scales, the reciprocal off-lattice
Hoeffding estimate is at most `1/(4Q)` eventually, uniformly in the finite
index set and in all Bernoulli probabilities in `[0,1]`. -/
theorem eventually_abs_reciprocal_sum_sub_mean_tail_le_inv_four_smoothLcm :
    ∀ᶠ N : ℕ in atTop,
      ∀ (I : Finset ℕ) (p : ℕ → ℝ),
        I ⊆ Finset.Icc (Erdos297.M N) N →
        (∀ n ∈ I, 0 ≤ p n) → (∀ n ∈ I, p n ≤ 1) →
        eventMass I p (fun B =>
            1 ≤ |subsetSum B (fun n : ℕ => ((n : ℝ)⁻¹)) -
              subsetMean I p (fun n : ℕ => ((n : ℝ)⁻¹))|) ≤
          1 / (4 *
            (Erdos297.GoodFactorization.smoothLcm (Erdos297.S N) : ℝ)) := by
  have hQ := tendsto_S_atTop.eventually
    eventually_smoothLcm_le_exp_five_mul
  filter_upwards
    [Erdos297.eventually_real_scales_ge_two,
      Erdos297.eventually_nat_scale_chain,
      Erdos297.eventually_nat_S_le_M_term 24 (by norm_num), hQ]
      with N hlarge hchain hscaleDiv hQbound
  have hMcast : (1 : ℝ) ≤ (Erdos297.M N : ℝ) := by
    have hhalf : Erdos297.MReal N / 2 ≤ (Erdos297.M N : ℝ) := by
      simpa [Erdos297.M] using Erdos297.half_le_floor hlarge.2.2
    linarith [hlarge.2.2]
  have hScast : (1 : ℝ) ≤ (Erdos297.S N : ℝ) := by
    have hhalf : Erdos297.SReal N / 2 ≤ (Erdos297.S N : ℝ) := by
      simpa [Erdos297.S] using Erdos297.half_le_floor hlarge.1
    linarith [hlarge.1]
  have hMpos : 0 < Erdos297.M N := by exact_mod_cast hMcast
  have hSpos : 1 ≤ Erdos297.S N := by exact_mod_cast hScast
  have hMN : Erdos297.M N ≤ N := by
    have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    have hcast : (Erdos297.M N : ℝ) ≤ (N : ℝ) :=
      hchain.2.2.trans (by linarith)
    exact_mod_cast hcast
  have hNreal : 0 < (N : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le hMpos hMN)
  have hscale :
      (24 : ℝ) * (N : ℝ) * (Erdos297.S N : ℝ) ≤
        (Erdos297.M N : ℝ) ^ 2 := by
    have hmul := (le_div_iff₀
      (mul_pos (by norm_num : (0 : ℝ) < 24) hNreal)).mp hscaleDiv
    nlinarith
  intro I p hI hp0 hp1
  exact abs_reciprocal_sum_sub_mean_tail_le_inv_four_smoothLcm
    p hMpos hMN hSpos hI hp0 hp1 hscale hQbound

end

end Erdos297.FiniteHoeffding
