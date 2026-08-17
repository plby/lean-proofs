/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos586.FiniteProbability
import ErdosProblems.Erdos586.Smooth

/-!
# Moment expansions and Euler-product bounds for Erdős Problem 586

This file isolates the algebraic part of the moment calculation in the
Balister--Bollobás--Morris--Sahasrabudhe--Tiba distortion sieve.

* `weightedIndicatorSum` is the finite upper bound for a fibre density.
* `expectation_weightedIndicatorSum` and
  `expectation_sq_weightedIndicatorSum` are the exact first- and second-
  moment expansions.
* `firstMoment_le_indicator_sum` and `secondMoment_le_indicator_sum` turn a
  pointwise indicator bound into the estimates used by the sieve.
* `sum_pi_prod_le_prod` is the finite Euler-product principle.  It is stated
  for finite exponent boxes, so no infinite product is hidden in the proof.
* `smoothRoughSecondMoment_le_kappa` is the 5-smooth/rough factorization.
  Its only number-theoretic input is the sharp `17 / 10` smooth-energy bound.
-/

open scoped BigOperators

namespace Erdos586

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## Exact expansions of finite indicator sums -/

variable {Ω ι : Type*} [Fintype Ω]

/-- The real-valued indicator of a set. -/
def realIndicator (S : Set Ω) (ω : Ω) : ℝ := if ω ∈ S then 1 else 0

@[simp] lemma realIndicator_apply (S : Set Ω) (ω : Ω) :
    realIndicator S ω = if ω ∈ S then 1 else 0 := rfl

lemma realIndicator_nonneg (S : Set Ω) (ω : Ω) : 0 ≤ realIndicator S ω := by
  by_cases hS : ω ∈ S <;> simp [realIndicator, hS]

@[simp] lemma realIndicator_mul (S T : Set Ω) (ω : Ω) :
    realIndicator S ω * realIndicator T ω = realIndicator (S ∩ T) ω := by
  by_cases hS : ω ∈ S <;> by_cases hT : ω ∈ T <;> simp [realIndicator, hS, hT]

/-- A finite linear combination of event indicators. -/
def weightedIndicatorSum (I : Finset ι) (c : ι → ℝ) (E : ι → Set Ω) (ω : Ω) : ℝ :=
  ∑ i ∈ I, c i * realIndicator (E i) ω

lemma weightedIndicatorSum_nonneg (I : Finset ι) (c : ι → ℝ) (E : ι → Set Ω)
    (hc : ∀ i ∈ I, 0 ≤ c i) (ω : Ω) :
    0 ≤ weightedIndicatorSum I c E ω := by
  exact Finset.sum_nonneg fun i hi =>
    mul_nonneg (hc i hi) (realIndicator_nonneg (E i) ω)

lemma weightedIndicatorSum_sq (I : Finset ι) (c : ι → ℝ) (E : ι → Set Ω)
    (ω : Ω) :
    weightedIndicatorSum I c E ω ^ 2 =
      ∑ i ∈ I, ∑ j ∈ I, (c i * c j) * realIndicator (E i ∩ E j) ω := by
  classical
  simp only [weightedIndicatorSum, pow_two, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [← realIndicator_mul]
  ring

lemma FiniteProbability.expectation_weightedIndicatorSum
    (μ : FiniteProbability Ω) (I : Finset ι) (c : ι → ℝ) (E : ι → Set Ω) :
    μ.expectation (weightedIndicatorSum I c E) =
      ∑ i ∈ I, c i * μ.mass (E i) := by
  classical
  simp only [FiniteProbability.expectation, weightedIndicatorSum]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [FiniteProbability.mass, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω hω
  by_cases hE : ω ∈ E i <;> simp [realIndicator, hE]
  ring

lemma FiniteProbability.expectation_sq_weightedIndicatorSum
    (μ : FiniteProbability Ω) (I : Finset ι) (c : ι → ℝ) (E : ι → Set Ω) :
    μ.expectation (fun ω => weightedIndicatorSum I c E ω ^ 2) =
      ∑ i ∈ I, ∑ j ∈ I, (c i * c j) * μ.mass (E i ∩ E j) := by
  classical
  simp_rw [weightedIndicatorSum_sq]
  simp only [FiniteProbability.expectation]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [FiniteProbability.mass, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω hω
  by_cases hE : ω ∈ E i ∩ E j <;> simp [realIndicator, hE]
  ring

/-- First-moment domination obtained from a pointwise indicator-sum bound. -/
lemma firstMoment_le_indicator_sum
    (μ : FiniteProbability Ω) (I : Finset ι) (c : ι → ℝ) (E : ι → Set Ω)
    (α : Ω → ℝ) (hα : ∀ ω, α ω ≤ weightedIndicatorSum I c E ω) :
    μ.expectation α ≤ ∑ i ∈ I, c i * μ.mass (E i) := by
  rw [← μ.expectation_weightedIndicatorSum I c E]
  exact μ.expectation_mono hα

/-- Second-moment domination obtained from a nonnegative pointwise
indicator-sum bound. -/
lemma secondMoment_le_indicator_sum
    (μ : FiniteProbability Ω) (I : Finset ι) (c : ι → ℝ) (E : ι → Set Ω)
    (α : Ω → ℝ) (hα0 : ∀ ω, 0 ≤ α ω)
    (hc : ∀ i ∈ I, 0 ≤ c i)
    (hα : ∀ ω, α ω ≤ weightedIndicatorSum I c E ω) :
    μ.expectation (fun ω => α ω ^ 2) ≤
      ∑ i ∈ I, ∑ j ∈ I, (c i * c j) * μ.mass (E i ∩ E j) := by
  rw [← μ.expectation_sq_weightedIndicatorSum I c E]
  apply μ.expectation_mono
  intro ω
  exact (sq_le_sq₀ (hα0 ω) (weightedIndicatorSum_nonneg I c E hc ω)).mpr (hα ω)

/-- Short interface name used by the concrete prime-stage development. -/
lemma expect_le_indicator_sum
    (μ : FiniteProbability Ω) (I : Finset ι) (c : ι → ℝ) (E : ι → Set Ω)
    (α : Ω → ℝ) (hα : ∀ ω, α ω ≤ weightedIndicatorSum I c E ω) :
    μ.expectation α ≤ ∑ i ∈ I, c i * μ.mass (E i) :=
  firstMoment_le_indicator_sum μ I c E α hα

/-- Short interface name used by the concrete prime-stage development. -/
lemma expect_sq_le_indicator_sum
    (μ : FiniteProbability Ω) (I : Finset ι) (c : ι → ℝ) (E : ι → Set Ω)
    (α : Ω → ℝ) (hα0 : ∀ ω, 0 ≤ α ω)
    (hc : ∀ i ∈ I, 0 ≤ c i)
    (hα : ∀ ω, α ω ≤ weightedIndicatorSum I c E ω) :
    μ.expectation (fun ω => α ω ^ 2) ≤
      ∑ i ∈ I, ∑ j ∈ I, (c i * c j) * μ.mass (E i ∩ E j) :=
  secondMoment_le_indicator_sum μ I c E α hα0 hc hα

/-! ## Finite Euler products -/

/-- A finite positive-exponent geometric sum is bounded by the full tail.
This is the local factor used for the newly exposed prime. -/
lemma finite_geometric_tail_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (N : ℕ) :
    ∑ n ∈ Finset.Ico 1 (N + 1), x ^ n ≤ x / (1 - x) := by
  simpa using
    (geom_sum_Ico_le_of_lt_one (m := 1) (n := N + 1) hx0 hx1)

/-- The same bound written in the prime-variable form used by the sieve. -/
lemma finite_prime_power_sum_le {p : ℝ} (hp : 1 < p) (N : ℕ) :
    ∑ n ∈ Finset.Ico 1 (N + 1), (1 / p) ^ n ≤ 1 / (p - 1) := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hx0 : 0 ≤ (1 / p : ℝ) := one_div_nonneg.mpr hp0.le
  have hx1 : (1 / p : ℝ) < 1 := by
    simpa using one_div_lt_one_div_of_lt zero_lt_one hp
  calc
    ∑ n ∈ Finset.Ico 1 (N + 1), (1 / p) ^ n ≤
        (1 / p) / (1 - 1 / p) := finite_geometric_tail_le hx0 hx1 N
    _ = 1 / (p - 1) := by
      field_simp [ne_of_gt hp0, ne_of_gt (sub_pos.mpr hp)]
      <;> ring

/-- The independent pair of positive exponents at the new prime contributes
at most `(p - 1)⁻²`.  The two finite truncation lengths are allowed to differ.
-/
lemma finite_prime_power_pair_sum_le {p : ℝ} (hp : 1 < p) (M N : ℕ) :
    (∑ a ∈ Finset.Ico 1 (M + 1), (1 / p) ^ a) *
        (∑ b ∈ Finset.Ico 1 (N + 1), (1 / p) ^ b) ≤
      1 / (p - 1) ^ 2 := by
  have hM := finite_prime_power_sum_le hp M
  have hN := finite_prime_power_sum_le hp N
  have hp1 : 0 ≤ (1 / (p - 1) : ℝ) := one_div_nonneg.mpr (sub_pos.mpr hp).le
  have hsumN : 0 ≤ ∑ b ∈ Finset.Ico 1 (N + 1), (1 / p) ^ b := by positivity
  calc
    (∑ a ∈ Finset.Ico 1 (M + 1), (1 / p) ^ a) *
        (∑ b ∈ Finset.Ico 1 (N + 1), (1 / p) ^ b) ≤
        (1 / (p - 1)) * (1 / (p - 1)) :=
      mul_le_mul hM hN hsumN hp1
    _ = 1 / (p - 1) ^ 2 := by
      field_simp [ne_of_gt (sub_pos.mpr hp)]

/-- The finite local LCM tail.  There are `2e+1` ordered pairs of
nonnegative exponents with maximum `e`, and the full tail has the closed form
shown here. -/
lemma finite_max_exponent_tail_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1)
    (N : ℕ) :
    ∑ n ∈ Finset.range N,
        (2 * ((n + 1 : ℕ) : ℝ) + 1) * x ^ (n + 1) ≤
      x * (3 - x) / (1 - x) ^ 2 := by
  have hxnorm : ‖x‖ < 1 := by
    simpa [Real.norm_eq_abs, abs_of_nonneg hx0] using hx1
  have hnat : HasSum (fun n : ℕ => (n : ℝ) * x ^ n) (x / (1 - x) ^ 2) :=
    hasSum_coe_mul_geometric_of_norm_lt_one hxnorm
  have hgeom : HasSum (fun n : ℕ => x ^ n) (1 - x)⁻¹ :=
    hasSum_geometric_of_norm_lt_one hxnorm
  have hfull :
      HasSum (fun n : ℕ => (2 * (n : ℝ) + 1) * x ^ n)
        (2 * (x / (1 - x) ^ 2) + (1 - x)⁻¹) := by
    simpa [add_mul, mul_assoc] using (hnat.mul_left 2).add hgeom
  have htailSummable :
      Summable (fun n : ℕ =>
        (2 * ((n + 1 : ℕ) : ℝ) + 1) * x ^ (n + 1)) :=
    (summable_nat_add_iff 1).mpr hfull.summable
  have hsplit := hfull.summable.sum_add_tsum_nat_add 1
  rw [hfull.tsum_eq] at hsplit
  have hsplit' :
      1 + ∑' n : ℕ, (2 * ((n + 1 : ℕ) : ℝ) + 1) * x ^ (n + 1) =
        2 * (x / (1 - x) ^ 2) + (1 - x)⁻¹ := by
    simpa using hsplit
  have htailEq :
      (∑' n : ℕ, (2 * ((n + 1 : ℕ) : ℝ) + 1) * x ^ (n + 1)) =
        x * (3 - x) / (1 - x) ^ 2 := by
    calc
      (∑' n : ℕ, (2 * ((n + 1 : ℕ) : ℝ) + 1) * x ^ (n + 1)) =
          2 * (x / (1 - x) ^ 2) + (1 - x)⁻¹ - 1 := by linarith
      _ = x * (3 - x) / (1 - x) ^ 2 := by
        field_simp [ne_of_gt (sub_pos.mpr hx1)]
        <;> ring
  calc
    ∑ n ∈ Finset.range N,
        (2 * ((n + 1 : ℕ) : ℝ) + 1) * x ^ (n + 1) ≤
        ∑' n : ℕ, (2 * ((n + 1 : ℕ) : ℝ) + 1) * x ^ (n + 1) :=
      htailSummable.sum_le_tsum (Finset.range N) (fun _ _ => by positivity)
    _ = x * (3 - x) / (1 - x) ^ 2 := htailEq

/-- Prime-variable form of `finite_max_exponent_tail_le`, equal to the
numerator appearing in the BBMST Euler factor. -/
lemma finite_prime_max_exponent_tail_le {p : ℝ} (hp : 1 < p) (N : ℕ) :
    ∑ n ∈ Finset.range N,
        (2 * ((n + 1 : ℕ) : ℝ) + 1) * (1 / p) ^ (n + 1) ≤
      (3 * p - 1) / (p - 1) ^ 2 := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hx0 : 0 ≤ (1 / p : ℝ) := one_div_nonneg.mpr hp0.le
  have hx1 : (1 / p : ℝ) < 1 := by
    simpa using one_div_lt_one_div_of_lt zero_lt_one hp
  calc
    ∑ n ∈ Finset.range N,
        (2 * ((n + 1 : ℕ) : ℝ) + 1) * (1 / p) ^ (n + 1) ≤
        (1 / p) * (3 - 1 / p) / (1 - 1 / p) ^ 2 :=
      finite_max_exponent_tail_le hx0 hx1 N
    _ = (3 * p - 1) / (p - 1) ^ 2 := by
      field_simp [ne_of_gt hp0, ne_of_gt (sub_pos.mpr hp)]
      <;> ring

/-- A finite sum of coordinatewise products is bounded by the corresponding
product of local sum bounds.  The left side is the expansion over the finite
dependent box `s.pi t`.

This is the exact finitary substitute for the informal instruction "extend
the exponent sums and factor them into an Euler product".
-/
lemma sum_pi_prod_le_prod {κ : ι → Type*} [DecidableEq ι]
    (s : Finset ι) (t : ∀ i, Finset (κ i)) (f : ∀ i, κ i → ℝ) (B : ι → ℝ)
    (hf : ∀ i ∈ s, ∀ x ∈ t i, 0 ≤ f i x)
    (hB : ∀ i ∈ s, ∑ x ∈ t i, f i x ≤ B i) :
    (∑ x ∈ s.pi t, ∏ i ∈ s.attach, f i.1 (x i.1 i.2)) ≤ ∏ i ∈ s, B i := by
  rw [← Finset.prod_sum]
  apply Finset.prod_le_prod
  · intro i hi
    exact Finset.sum_nonneg fun x hx => hf i hi x hx
  · intro i hi
    exact hB i hi

/-- A version of `sum_pi_prod_le_prod` with a nonnegative outer summand
bounded by the coordinate product. -/
lemma sum_pi_le_prod {κ : ι → Type*} [DecidableEq ι]
    (s : Finset ι) (t : ∀ i, Finset (κ i)) (F : (∀ i ∈ s, κ i) → ℝ)
    (f : ∀ i, κ i → ℝ) (B : ι → ℝ)
    (hF : ∀ x ∈ s.pi t, F x ≤ ∏ i ∈ s.attach, f i.1 (x i.1 i.2))
    (hf : ∀ i ∈ s, ∀ x ∈ t i, 0 ≤ f i x)
    (hB : ∀ i ∈ s, ∑ x ∈ t i, f i x ≤ B i) :
    (∑ x ∈ s.pi t, F x) ≤ ∏ i ∈ s, B i := by
  calc
    (∑ x ∈ s.pi t, F x) ≤
        ∑ x ∈ s.pi t, ∏ i ∈ s.attach, f i.1 (x i.1 i.2) :=
      Finset.sum_le_sum fun x hx => hF x hx
    _ ≤ ∏ i ∈ s, B i := sum_pi_prod_le_prod s t f B hf hB

/-- Extend a finite sum through an injective encoding into a larger finite
box.  This is the subset step preceding `sum_pi_le_prod` in the rough Euler
product argument. -/
lemma sum_le_sum_over_injective_encoding {τ κ : Type*} [DecidableEq κ]
    (I : Finset τ) (T : Finset κ) (encode : τ → κ) (F : τ → ℝ) (G : κ → ℝ)
    (hinj : Set.InjOn encode (I : Set τ))
    (hmem : ∀ i ∈ I, encode i ∈ T)
    (hFG : ∀ i ∈ I, F i ≤ G (encode i))
    (hG0 : ∀ x ∈ T, 0 ≤ G x) :
    (∑ i ∈ I, F i) ≤ ∑ x ∈ T, G x := by
  calc
    (∑ i ∈ I, F i) ≤ ∑ i ∈ I, G (encode i) :=
      Finset.sum_le_sum fun i hi => hFG i hi
    _ = ∑ x ∈ I.image encode, G x := (Finset.sum_image hinj).symm
    _ ≤ ∑ x ∈ T, G x := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro x hx
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
        exact hmem i hi
      · intro x hxT hxI
        exact hG0 x hxT

/-! ### Reindexing by rough keys and smooth fibres -/

/-- The set of smooth values occurring above a fixed rough key. -/
def keyedFiber {τ ρ α : Type*} [DecidableEq ρ] [DecidableEq α]
    (I : Finset τ) (key : τ → ρ) (value : τ → α) (r : ρ) : Finset α :=
  (I.filter fun i => key i = r).image value

/-- Exact finite reindexing by a key and a value which is injective inside
each key fibre (equivalently, the combined `(key,value)` map is injective). -/
lemma sum_group_by_key_value {τ ρ α : Type*} [DecidableEq ρ] [DecidableEq α]
    (I : Finset τ) (key : τ → ρ) (value : τ → α)
    (hvalue : Set.InjOn (fun i => (key i, value i)) (I : Set τ))
    (F : ρ → α → ℝ) :
    (∑ i ∈ I, F (key i) (value i)) =
      ∑ r ∈ I.image key, ∑ a ∈ keyedFiber I key value r, F r a := by
  classical
  calc
    (∑ i ∈ I, F (key i) (value i)) =
        ∑ r ∈ I.image key, ∑ i ∈ I with key i = r, F (key i) (value i) :=
      (Finset.sum_fiberwise_of_maps_to
        (fun i hi => Finset.mem_image_of_mem key hi)
        (fun i => F (key i) (value i))).symm
    _ = ∑ r ∈ I.image key, ∑ a ∈ keyedFiber I key value r, F r a := by
      apply Finset.sum_congr rfl
      intro r hr
      have hinj : Set.InjOn value (↑(I.filter fun i => key i = r) : Set τ) := by
        intro i hi j hj hij
        apply hvalue (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hj).1
        exact Prod.ext
          ((Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm) hij
      rw [keyedFiber, Finset.sum_image hinj]
      apply Finset.sum_congr rfl
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]

/-- Two-dimensional version of `sum_group_by_key_value`. -/
lemma sum_pair_group_by_key_value {τ ρ α : Type*}
    [DecidableEq ρ] [DecidableEq α]
    (I : Finset τ) (key : τ → ρ) (value : τ → α)
    (hvalue : Set.InjOn (fun i => (key i, value i)) (I : Set τ))
    (F : ρ → ρ → α → α → ℝ) :
    (∑ i ∈ I, ∑ j ∈ I, F (key i) (key j) (value i) (value j)) =
      ∑ r ∈ I.image key, ∑ s ∈ I.image key,
        ∑ a ∈ keyedFiber I key value r,
          ∑ b ∈ keyedFiber I key value s, F r s a b := by
  calc
    (∑ i ∈ I, ∑ j ∈ I, F (key i) (key j) (value i) (value j)) =
        ∑ r ∈ I.image key, ∑ a ∈ keyedFiber I key value r,
          ∑ j ∈ I, F r (key j) a (value j) := by
      exact sum_group_by_key_value I key value hvalue
        (fun r a => ∑ j ∈ I, F r (key j) a (value j))
    _ = ∑ r ∈ I.image key, ∑ s ∈ I.image key,
        ∑ a ∈ keyedFiber I key value r,
          ∑ b ∈ keyedFiber I key value s, F r s a b := by
      apply Finset.sum_congr rfl
      intro r hr
      calc
        (∑ a ∈ keyedFiber I key value r,
            ∑ j ∈ I, F r (key j) a (value j)) =
            ∑ a ∈ keyedFiber I key value r,
              ∑ s ∈ I.image key,
                ∑ b ∈ keyedFiber I key value s, F r s a b := by
          apply Finset.sum_congr rfl
          intro a ha
          exact sum_group_by_key_value I key value hvalue (fun s b => F r s a b)
        _ = ∑ s ∈ I.image key,
              ∑ a ∈ keyedFiber I key value r,
                ∑ b ∈ keyedFiber I key value s, F r s a b := by
          rw [Finset.sum_comm]

/-- The local second-moment Euler factor at an earlier prime. -/
def secondMomentEulerFactor (p δ : ℝ) : ℝ :=
  1 + (3 * p - 1) / ((1 - δ) * (p - 1) ^ 2)

/-- Nested-division form of the Euler factor.  This is definitionally the
same expression as `Sieve.sieveFactor` after unfolding `Sieve.stageA`. -/
lemma secondMomentEulerFactor_eq_nested_div (p δ : ℝ) :
    secondMomentEulerFactor p δ =
      1 + ((3 * p - 1) / (p - 1) ^ 2) / (1 - δ) := by
  unfold secondMomentEulerFactor
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- A truncated earlier-prime exponent-pair sum is bounded by the exact
second-moment Euler factor.  The initial `1` is the pair `(0,0)`; all
positive maximum exponents receive the distortion multiplier
`(1 - δ)⁻¹`. -/
lemma finite_secondMomentEulerFactor_le {p δ : ℝ} (hp : 1 < p)
    (hδ : δ < 1) (N : ℕ) :
    1 + (1 / (1 - δ)) *
        (∑ n ∈ Finset.range N,
          (2 * ((n + 1 : ℕ) : ℝ) + 1) * (1 / p) ^ (n + 1)) ≤
      secondMomentEulerFactor p δ := by
  have hscale : 0 ≤ (1 / (1 - δ) : ℝ) :=
    one_div_nonneg.mpr (sub_pos.mpr hδ).le
  calc
    1 + (1 / (1 - δ)) *
        (∑ n ∈ Finset.range N,
          (2 * ((n + 1 : ℕ) : ℝ) + 1) * (1 / p) ^ (n + 1)) ≤
        1 + (1 / (1 - δ)) * ((3 * p - 1) / (p - 1) ^ 2) := by
      simpa [add_comm] using add_le_add_left
        (mul_le_mul_of_nonneg_left (finite_prime_max_exponent_tail_le hp N) hscale) 1
    _ = secondMomentEulerFactor p δ := by
      unfold secondMomentEulerFactor
      field_simp [ne_of_gt (sub_pos.mpr hp), ne_of_gt (sub_pos.mpr hδ)]
      <;> ring

/-- Adding the outer row and column to a square exponent box contributes
exactly `2k+1` pairs whose maximum exponent is `k`. -/
private lemma sum_pair_max_range_succ (g : ℕ → ℝ) (k : ℕ) :
    (∑ a ∈ Finset.range (k + 1), ∑ b ∈ Finset.range (k + 1), g (max a b)) =
      (∑ a ∈ Finset.range k, ∑ b ∈ Finset.range k, g (max a b)) +
        (2 * (k : ℝ) + 1) * g k := by
  have hrow :
      (∑ a ∈ Finset.range k, ∑ b ∈ Finset.range (k + 1), g (max a b)) =
        (∑ a ∈ Finset.range k, ∑ b ∈ Finset.range k, g (max a b)) +
          (k : ℝ) * g k := by
    calc
      (∑ a ∈ Finset.range k, ∑ b ∈ Finset.range (k + 1), g (max a b)) =
          ∑ a ∈ Finset.range k,
            ((∑ b ∈ Finset.range k, g (max a b)) + g (max a k)) := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [Finset.sum_range_succ]
      _ = (∑ a ∈ Finset.range k, ∑ b ∈ Finset.range k, g (max a b)) +
          ∑ a ∈ Finset.range k, g (max a k) := by
        rw [Finset.sum_add_distrib]
      _ = (∑ a ∈ Finset.range k, ∑ b ∈ Finset.range k, g (max a b)) +
          ∑ _a ∈ Finset.range k, g k := by
        congr 1
        apply Finset.sum_congr rfl
        intro a ha
        rw [Nat.max_eq_right (Nat.le_of_lt (Finset.mem_range.mp ha))]
      _ = (∑ a ∈ Finset.range k, ∑ b ∈ Finset.range k, g (max a b)) +
          (k : ℝ) * g k := by simp
  have hcol :
      (∑ b ∈ Finset.range (k + 1), g (max k b)) = ((k + 1 : ℕ) : ℝ) * g k := by
    calc
      (∑ b ∈ Finset.range (k + 1), g (max k b)) =
          ∑ _b ∈ Finset.range (k + 1), g k := by
        apply Finset.sum_congr rfl
        intro b hb
        have hblt : b < k + 1 := Finset.mem_range.mp hb
        have hbk : b ≤ k := by omega
        rw [Nat.max_eq_left hbk]
      _ = ((k + 1 : ℕ) : ℝ) * g k := by simp
  calc
    (∑ a ∈ Finset.range (k + 1), ∑ b ∈ Finset.range (k + 1), g (max a b)) =
        (∑ a ∈ Finset.range k, ∑ b ∈ Finset.range (k + 1), g (max a b)) +
          ∑ b ∈ Finset.range (k + 1), g (max k b) := by
      rw [Finset.sum_range_succ]
    _ = (∑ a ∈ Finset.range k, ∑ b ∈ Finset.range k, g (max a b)) +
        (2 * (k : ℝ) + 1) * g k := by
      rw [hrow, hcol]
      push_cast
      ring

/-- Count a finite square of exponent pairs by their maximum exponent. -/
private lemma finite_exponent_pair_factor_eq (c x : ℝ) (N : ℕ) :
    (∑ a ∈ Finset.range (N + 1), ∑ b ∈ Finset.range (N + 1),
        if max a b = 0 then 1 else c * x ^ max a b) =
      1 + c * ∑ n ∈ Finset.range N,
        (2 * ((n + 1 : ℕ) : ℝ) + 1) * x ^ (n + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
      calc
        (∑ a ∈ Finset.range (N + 1 + 1), ∑ b ∈ Finset.range (N + 1 + 1),
            if max a b = 0 then 1 else c * x ^ max a b) =
            (∑ a ∈ Finset.range (N + 1), ∑ b ∈ Finset.range (N + 1),
              if max a b = 0 then 1 else c * x ^ max a b) +
              (2 * ((N + 1 : ℕ) : ℝ) + 1) *
                (if N + 1 = 0 then 1 else c * x ^ (N + 1)) := by
          simpa using sum_pair_max_range_succ
            (fun e ↦ if e = 0 then 1 else c * x ^ e) (N + 1)
        _ = 1 + c * ∑ n ∈ Finset.range (N + 1),
            (2 * ((n + 1 : ℕ) : ℝ) + 1) * x ^ (n + 1) := by
          rw [ih, Finset.sum_range_succ]
          simp only [Nat.add_eq_zero, one_ne_zero, and_false, if_false]
          ring

/-- Concrete finite Euler-box estimate.  The `(a,b)=(0,0)` pair is
undistorted; all other pairs receive `(1-δ)⁻¹`, and grouping by
`max a b` gives the BBMST local factor. -/
lemma finite_exponent_pair_factor_le {p δ : ℝ} (hp : 1 < p)
    (hδ : δ < 1) (N : ℕ) :
    (∑ a ∈ Finset.range (N + 1), ∑ b ∈ Finset.range (N + 1),
        if max a b = 0 then 1
        else (1 / (1 - δ)) * (1 / p) ^ max a b) ≤
      secondMomentEulerFactor p δ := by
  rw [finite_exponent_pair_factor_eq]
  exact finite_secondMomentEulerFactor_le hp hδ N

/-- The BBMST refined second-moment expression, with a free smooth-energy
constant `κ`. -/
def refinedSecondMomentBound (κ p : ℝ) (stages : Finset ι)
    (prime distortion : ι → ℝ) : ℝ :=
  κ / (p - 1) ^ 2 * ∏ i ∈ stages, secondMomentEulerFactor (prime i) (distortion i)

/-! ## The 5-smooth/rough factorization -/

/-- The sharp smooth-energy constant of Lemma 9.4. -/
def fiveSmoothKappa : ℝ := 17 / 10

/-- The normalized starting value after the uniform `2,3,5` stages.  The
reciprocal smooth-antichain estimate supplies `μ₃ ≥ 2/3`; Lemma 9.4 supplies
`κ = 17/10`. -/
lemma fiveSmoothKappa_div_le_fifty_one_twentieth {μ : ℝ}
    (hμ : 2 / 3 ≤ μ) : fiveSmoothKappa / μ ≤ 51 / 20 := by
  have hμpos : 0 < μ := lt_of_lt_of_le (by norm_num) hμ
  rw [div_le_iff₀ hμpos]
  unfold fiveSmoothKappa
  nlinarith

/-- The rough part of the reindexed second-moment sum. -/
def roughSecondMoment {ρ : Type*} (R : Finset ρ) (w : ρ → ρ → ℝ) : ℝ :=
  ∑ r ∈ R, ∑ s ∈ R, w r s

/-- The complete reindexed second-moment sum.  The key `r` includes both a
rough integer and the positive exponent of the newly processed prime; `D r`
is its fibre of 5-smooth exponent triples. -/
def smoothRoughSecondMoment {ρ : Type*} (R : Finset ρ) (w : ρ → ρ → ℝ)
    (D : ρ → Finset Exp3) : ℝ :=
  ∑ r ∈ R, ∑ s ∈ R, w r s * tripleEnergy (D r) (D s)

/-- Generic hard-grouping lemma for the refined second moment.  A stage
index is split into a rough key and a 5-smooth exponent triple; the combined
pair of data is injective.
Any pairwise summand bounded by the corresponding rough weight times the
smooth LCM kernel is therefore bounded by `smoothRoughSecondMoment`.

The concrete stage assembly instantiates `key i` by `(roughPart i,
newPrimeExponent i)` and `value i` by the exponents of `2,3,5` in the old
part. -/
lemma pair_sum_le_smoothRough_of_reindex {τ ρ : Type*} [DecidableEq ρ]
    (I : Finset τ) (key : τ → ρ) (value : τ → Exp3)
    (hvalue : Set.InjOn (fun i => (key i, value i)) (I : Set τ))
    (F : τ → τ → ℝ) (w : ρ → ρ → ℝ)
    (hF : ∀ i ∈ I, ∀ j ∈ I,
      F i j ≤ w (key i) (key j) * tripleKernel (value i) (value j)) :
    (∑ i ∈ I, ∑ j ∈ I, F i j) ≤
      smoothRoughSecondMoment (I.image key) w (keyedFiber I key value) := by
  calc
    (∑ i ∈ I, ∑ j ∈ I, F i j) ≤
        ∑ i ∈ I, ∑ j ∈ I,
          w (key i) (key j) * tripleKernel (value i) (value j) := by
      exact Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => hF i hi j hj
    _ = ∑ r ∈ I.image key, ∑ s ∈ I.image key,
        ∑ a ∈ keyedFiber I key value r,
          ∑ b ∈ keyedFiber I key value s,
            w r s * tripleKernel a b :=
      sum_pair_group_by_key_value I key value hvalue
        (fun r s a b => w r s * tripleKernel a b)
    _ = smoothRoughSecondMoment (I.image key) w (keyedFiber I key value) := by
      unfold smoothRoughSecondMoment tripleEnergy
      simp_rw [Finset.mul_sum]

/-- Factoring off the 5-smooth coordinates costs at most `17 / 10`.

In the sieve application, `w r s` is
`p^(-(j_r+j_s)) * ν(lcm(rough_r,rough_s))/lcm(rough_r,rough_s)`.
All its factors are nonnegative.  Each `D r` is an antichain because the
original moduli form a divisibility antichain.
-/
lemma smoothRoughSecondMoment_le_kappa {ρ : Type*} (R : Finset ρ)
    (w : ρ → ρ → ℝ) (D : ρ → Finset Exp3)
    (hw : ∀ r ∈ R, ∀ s ∈ R, 0 ≤ w r s)
    (hD : ∀ r ∈ R, TripleAntichain (D r)) :
    smoothRoughSecondMoment R w D ≤ fiveSmoothKappa * roughSecondMoment R w := by
  unfold smoothRoughSecondMoment roughSecondMoment fiveSmoothKappa
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro r hr
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s hs
  calc
    w r s * tripleEnergy (D r) (D s) ≤ w r s * (17 / 10) := by
      exact mul_le_mul_of_nonneg_left (five_smooth_energy_le (D r) (D s) (hD r hr) (hD s hs))
        (hw r hr s hs)
    _ = (17 / 10) * w r s := by ring

/-- The factorized second moment followed by any finite Euler-product bound
for the rough part. -/
lemma smoothRoughSecondMoment_le_of_rough_le {ρ : Type*} (R : Finset ρ)
    (w : ρ → ρ → ℝ) (D : ρ → Finset Exp3) (B : ℝ)
    (hw : ∀ r ∈ R, ∀ s ∈ R, 0 ≤ w r s)
    (hD : ∀ r ∈ R, TripleAntichain (D r))
    (hrough : roughSecondMoment R w ≤ B) :
    smoothRoughSecondMoment R w D ≤ fiveSmoothKappa * B := by
  calc
    smoothRoughSecondMoment R w D ≤ fiveSmoothKappa * roughSecondMoment R w :=
      smoothRoughSecondMoment_le_kappa R w D hw hD
    _ ≤ fiveSmoothKappa * B := by
      exact mul_le_mul_of_nonneg_left hrough (by norm_num [fiveSmoothKappa])

/-- The form consumed by the sieve recurrence: after the rough-coordinate
sum has been bounded by the new-prime geometric factor times the finite
Euler product, the full second moment has the BBMST constant `17 / 10`.
-/
lemma smoothRoughSecondMoment_le_refined_bound {ρ σ : Type*}
    (R : Finset ρ) (w : ρ → ρ → ℝ) (D : ρ → Finset Exp3)
    (p : ℝ) (stages : Finset σ) (prime distortion : σ → ℝ)
    (hw : ∀ r ∈ R, ∀ s ∈ R, 0 ≤ w r s)
    (hD : ∀ r ∈ R, TripleAntichain (D r))
    (hrough : roughSecondMoment R w ≤
      1 / (p - 1) ^ 2 *
        ∏ i ∈ stages, secondMomentEulerFactor (prime i) (distortion i)) :
    smoothRoughSecondMoment R w D ≤
      refinedSecondMomentBound fiveSmoothKappa p stages prime distortion := by
  unfold refinedSecondMomentBound
  calc
    smoothRoughSecondMoment R w D ≤ fiveSmoothKappa * roughSecondMoment R w :=
      smoothRoughSecondMoment_le_kappa R w D hw hD
    _ ≤ fiveSmoothKappa *
        (1 / (p - 1) ^ 2 *
          ∏ i ∈ stages, secondMomentEulerFactor (prime i) (distortion i)) := by
      exact mul_le_mul_of_nonneg_left hrough (by norm_num [fiveSmoothKappa])
    _ = fiveSmoothKappa / (p - 1) ^ 2 *
        ∏ i ∈ stages, secondMomentEulerFactor (prime i) (distortion i) := by ring

/-- Reindex a finite pair sum into rough keys and 5-smooth fibres and apply
the complete refined bound in one step.  This is the endpoint used by the
concrete LCM-sum calculation: its `F` is the LCM summand, while `key` and
`value` are respectively the rough/new-prime data and the exponent triple
at `2,3,5`. -/
lemma pair_sum_le_refined_bound_of_reindex {τ ρ σ : Type*}
    [DecidableEq ρ]
    (I : Finset τ) (key : τ → ρ) (value : τ → Exp3)
    (hvalue : Set.InjOn (fun i ↦ (key i, value i)) (I : Set τ))
    (F : τ → τ → ℝ) (w : ρ → ρ → ℝ)
    (p : ℝ) (stages : Finset σ) (prime distortion : σ → ℝ)
    (hF : ∀ i ∈ I, ∀ j ∈ I,
      F i j ≤ w (key i) (key j) * tripleKernel (value i) (value j))
    (hw : ∀ r ∈ I.image key, ∀ s ∈ I.image key, 0 ≤ w r s)
    (hD : ∀ r ∈ I.image key, TripleAntichain (keyedFiber I key value r))
    (hrough : roughSecondMoment (I.image key) w ≤
      1 / (p - 1) ^ 2 *
        ∏ i ∈ stages, secondMomentEulerFactor (prime i) (distortion i)) :
    (∑ i ∈ I, ∑ j ∈ I, F i j) ≤
      refinedSecondMomentBound fiveSmoothKappa p stages prime distortion := by
  calc
    (∑ i ∈ I, ∑ j ∈ I, F i j) ≤
        smoothRoughSecondMoment (I.image key) w (keyedFiber I key value) :=
      pair_sum_le_smoothRough_of_reindex I key value hvalue F w hF
    _ ≤ refinedSecondMomentBound fiveSmoothKappa p stages prime distortion :=
      smoothRoughSecondMoment_le_refined_bound (I.image key) w
        (keyedFiber I key value) p stages prime distortion hw hD hrough

/-- A direct consumer form for a previously established finite pair-sum
upper bound.  It separates the probability/congruence-class expansion from
the smooth/rough reindexing without exposing an intermediate
`smoothRoughSecondMoment` premise. -/
lemma secondMoment_le_refined_bound_of_reindex {τ ρ σ : Type*}
    [DecidableEq ρ]
    (M₂ : ℝ) (I : Finset τ) (key : τ → ρ) (value : τ → Exp3)
    (hvalue : Set.InjOn (fun i ↦ (key i, value i)) (I : Set τ))
    (F : τ → τ → ℝ) (w : ρ → ρ → ℝ)
    (p : ℝ) (stages : Finset σ) (prime distortion : σ → ℝ)
    (hM₂ : M₂ ≤ ∑ i ∈ I, ∑ j ∈ I, F i j)
    (hF : ∀ i ∈ I, ∀ j ∈ I,
      F i j ≤ w (key i) (key j) * tripleKernel (value i) (value j))
    (hw : ∀ r ∈ I.image key, ∀ s ∈ I.image key, 0 ≤ w r s)
    (hD : ∀ r ∈ I.image key, TripleAntichain (keyedFiber I key value r))
    (hrough : roughSecondMoment (I.image key) w ≤
      1 / (p - 1) ^ 2 *
        ∏ i ∈ stages, secondMomentEulerFactor (prime i) (distortion i)) :
    M₂ ≤ refinedSecondMomentBound fiveSmoothKappa p stages prime distortion := by
  exact hM₂.trans (pair_sum_le_refined_bound_of_reindex I key value hvalue F w p stages
    prime distortion hF hw hD hrough)

/-- Complete second-moment pipeline.  The concrete arithmetic work is
concentrated in `hreindex` (the LCM congruence-mass estimate and the
5-smooth/rough reindexing) and `hrough` (the finite Euler-product bound).
Everything else is the exact indicator expansion and Lemma 9.4.
-/
lemma secondMoment_le_refined_bound {ρ σ : Type*}
    (μ : FiniteProbability Ω) (I : Finset ι) (c : ι → ℝ) (E : ι → Set Ω)
    (α : Ω → ℝ) (R : Finset ρ) (w : ρ → ρ → ℝ)
    (D : ρ → Finset Exp3) (p : ℝ) (stages : Finset σ)
    (prime distortion : σ → ℝ)
    (hα0 : ∀ ω, 0 ≤ α ω) (hc : ∀ i ∈ I, 0 ≤ c i)
    (hα : ∀ ω, α ω ≤ weightedIndicatorSum I c E ω)
    (hreindex :
      (∑ i ∈ I, ∑ j ∈ I, (c i * c j) * μ.mass (E i ∩ E j)) ≤
        smoothRoughSecondMoment R w D)
    (hw : ∀ r ∈ R, ∀ s ∈ R, 0 ≤ w r s)
    (hD : ∀ r ∈ R, TripleAntichain (D r))
    (hrough : roughSecondMoment R w ≤
      1 / (p - 1) ^ 2 *
        ∏ i ∈ stages, secondMomentEulerFactor (prime i) (distortion i)) :
    μ.expectation (fun ω => α ω ^ 2) ≤
      refinedSecondMomentBound fiveSmoothKappa p stages prime distortion := by
  calc
    μ.expectation (fun ω => α ω ^ 2) ≤
        ∑ i ∈ I, ∑ j ∈ I, (c i * c j) * μ.mass (E i ∩ E j) :=
      secondMoment_le_indicator_sum μ I c E α hα0 hc hα
    _ ≤ smoothRoughSecondMoment R w D := hreindex
    _ ≤ refinedSecondMomentBound fiveSmoothKappa p stages prime distortion :=
      smoothRoughSecondMoment_le_refined_bound R w D p stages prime distortion hw hD hrough

/-- Direct stage form of `secondMoment_le_refined_bound`.  Here `B` is the
newly covered subset of the old-by-new coordinate product, so the random
variable is exactly `fiberFraction B` and the conclusion is stated using
`FiniteProbability.secondMoment`.
-/
lemma stageSecondMoment_le_refined_bound {Y ρ σ : Type*}
    [Fintype Y] [Nonempty Y]
    (μ : FiniteProbability Ω) (B : Set (Ω × Y))
    (I : Finset ι) (c : ι → ℝ) (E : ι → Set Ω)
    (R : Finset ρ) (w : ρ → ρ → ℝ) (D : ρ → Finset Exp3)
    (p : ℝ) (stages : Finset σ) (prime distortion : σ → ℝ)
    (hc : ∀ i ∈ I, 0 ≤ c i)
    (hfiber : ∀ x, fiberFraction B x ≤ weightedIndicatorSum I c E x)
    (hreindex :
      (∑ i ∈ I, ∑ j ∈ I, (c i * c j) * μ.mass (E i ∩ E j)) ≤
        smoothRoughSecondMoment R w D)
    (hw : ∀ r ∈ R, ∀ s ∈ R, 0 ≤ w r s)
    (hD : ∀ r ∈ R, TripleAntichain (D r))
    (hrough : roughSecondMoment R w ≤
      1 / (p - 1) ^ 2 *
        ∏ i ∈ stages, secondMomentEulerFactor (prime i) (distortion i)) :
    secondMoment μ B ≤
      refinedSecondMomentBound fiveSmoothKappa p stages prime distortion := by
  unfold secondMoment
  exact secondMoment_le_refined_bound μ I c E (fiberFraction B) R w D p stages
    prime distortion (fiberFraction_nonneg B) hc hfiber hreindex hw hD hrough

end

end Erdos586
