/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 690.
https://www.erdosproblems.com/forum/thread/690

Informal authors:
- Stijn Cambie

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos690.md
-/
/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Mathlib
import Util.Density
import ErdosProblems.Erdos697.Erdos697CRTModel
import ErdosProblems.Erdos697.Erdos697Cover

/-!
# Erdős Problem 690

For a positive integer `n`, list its distinct prime factors increasingly.  This
file proves the exact natural-density formula for the event that a prime `p`
is in a specified position in this list.  It then formalizes Cambie's
resolution: the density is unimodal for positions one, two, and three, and is
not unimodal for every position from four through twenty.

The finite calculations below use only exact natural-number and rational
arithmetic.
-/

open Filter Set
open scoped Topology BigOperators

namespace Erdos690

/-! ## Exact coefficients and density -/

/-- Update the coefficient row when multiplying by `a + X`. -/
def coeffStep (a : ℕ) (row : List ℕ) : List ℕ :=
  (List.range (row.length + 1)).map fun r =>
    a * row.getD r 0 + if r = 0 then 0 else row.getD (r - 1) 0

/-- Coefficients of `∏_{q < p, q prime} (q - 1 + X)`. -/
def coeffRow (p : ℕ) : List ℕ :=
  (List.range p).foldl
    (fun row q => if q.Prime then coeffStep (q - 1) row else row) [1]

/-- The coefficient of `X^r` in
`∏_{q < p, q prime} (q - 1 + X)`. -/
def coeff (r p : ℕ) : ℕ := (coeffRow p).getD r 0

/-- The product of the primes strictly below `p`. -/
def primeModulus (p : ℕ) : ℕ :=
  (List.range p).foldl (fun n q => if q.Prime then n * q else n) 1

/-- The exact density attached to the one-based position `k` and prime `p`.
It is set to zero away from the intended domain. -/
def primeFactorDensity (k p : ℕ) : ℚ :=
  if 0 < k ∧ p.Prime then
    (coeff (k - 1) p : ℚ) / (p * primeModulus p : ℕ)
  else 0

theorem coeffStep_getD (a : ℕ) (row : List ℕ) (r : ℕ) :
    (coeffStep a row).getD r 0 =
      a * row.getD r 0 + if r = 0 then 0 else row.getD (r - 1) 0 := by
  by_cases h : r < row.length + 1
  · simp [coeffStep, List.getD, h]
  · have hr : row.length + 1 ≤ r := Nat.le_of_not_gt h
    have hr0 : ¬r < row.length := by omega
    have hr1 : r = 0 ∨ ¬r - 1 < row.length := by omega
    rcases hr1 with hr1 | hr1
    · omega
    · simp [coeffStep, List.getD, h, hr0, hr1]

theorem coeffRow_succ (p : ℕ) :
    coeffRow (p + 1) =
      if p.Prime then coeffStep (p - 1) (coeffRow p) else coeffRow p := by
  simp [coeffRow, List.range_succ, List.foldl_append]

theorem coeff_succ_of_prime (r p : ℕ) (hp : p.Prime) :
    coeff r (p + 1) = (p - 1) * coeff r p +
      if r = 0 then 0 else coeff (r - 1) p := by
  rw [coeff, coeffRow_succ, if_pos hp, coeffStep_getD]
  rfl

theorem coeff_succ_of_not_prime (r p : ℕ) (hp : ¬p.Prime) :
    coeff r (p + 1) = coeff r p := by
  simp [coeff, coeffRow_succ, hp]

theorem primeModulus_succ (p : ℕ) :
    primeModulus (p + 1) =
      if p.Prime then primeModulus p * p else primeModulus p := by
  simp [primeModulus, List.range_succ, List.foldl_append]

theorem primeModulus_pos (p : ℕ) : 0 < primeModulus p := by
  induction p with
  | zero => simp [primeModulus]
  | succ p ih =>
      rw [primeModulus_succ]
      split_ifs with hp
      · exact Nat.mul_pos ih hp.pos
      · exact ih

/-! ## The cutoff coefficient as a finite Bernoulli probability -/

/-- The primes strictly below a cutoff. -/
def primesBelow (p : ℕ) : Finset ℕ :=
  (Finset.range p).filter Nat.Prime

/-- The elementary-symmetric numerator over a finite set. -/
def finiteCoeffNumerator (a : ℕ → ℕ) (r : ℕ) (s : Finset ℕ) : ℕ :=
  ∑ S ∈ s.powersetCard r, ∏ q ∈ s \ S, a q

theorem finiteCoeffNumerator_zero (a : ℕ → ℕ) (s : Finset ℕ) :
    finiteCoeffNumerator a 0 s = ∏ q ∈ s, a q := by
  simp [finiteCoeffNumerator]

theorem finiteCoeffNumerator_succ_insert
    (a : ℕ → ℕ) (r x : ℕ) (s : Finset ℕ) (hx : x ∉ s) :
    finiteCoeffNumerator a (r + 1) (insert x s) =
      a x * finiteCoeffNumerator a (r + 1) s +
        finiteCoeffNumerator a r s := by
  classical
  rw [finiteCoeffNumerator, Finset.powersetCard_succ_insert hx]
  have hd : Disjoint (s.powersetCard (r + 1))
      ((s.powersetCard r).image (insert x)) := by
    rw [Finset.disjoint_left]
    intro T hT hTi
    have hxT : x ∉ T := fun h => hx ((Finset.mem_powersetCard.mp hT).1 h)
    obtain ⟨U, hU, hEq⟩ := Finset.mem_image.mp hTi
    exact hxT (hEq ▸ Finset.mem_insert_self x U)
  rw [Finset.sum_union hd]
  have hleft :
      ∑ T ∈ s.powersetCard (r + 1), ∏ q ∈ insert x s \ T, a q =
        a x * finiteCoeffNumerator a (r + 1) s := by
    unfold finiteCoeffNumerator
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro T hT
    have hTs : T ⊆ s := (Finset.mem_powersetCard.mp hT).1
    have hxT : x ∉ T := fun h => hx (hTs h)
    rw [show insert x s \ T = insert x (s \ T) by
      ext q
      simp only [Finset.mem_sdiff, Finset.mem_insert]
      aesop,
      Finset.prod_insert]
    simp [hx, hxT]
  rw [hleft]
  congr 1
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro U hU
    rw [show insert x s \ insert x U = s \ U by
      ext q
      simp only [Finset.mem_sdiff, Finset.mem_insert]
      aesop]
  · intro U₁ hU₁ U₂ hU₂ hEq
    have hU₁s : U₁ ⊆ s := (Finset.mem_powersetCard.mp hU₁).1
    have hU₂s : U₂ ⊆ s := (Finset.mem_powersetCard.mp hU₂).1
    have hxU₁ : x ∉ U₁ := fun h => hx (hU₁s h)
    have hxU₂ : x ∉ U₂ := fun h => hx (hU₂s h)
    calc
      U₁ = (insert x U₁).erase x := by simp [hxU₁]
      _ = (insert x U₂).erase x := by rw [hEq]
      _ = U₂ := by simp [hxU₂]

theorem finiteCoeffNumerator_insert
    (a : ℕ → ℕ) (r x : ℕ) (s : Finset ℕ) (hx : x ∉ s) :
    finiteCoeffNumerator a r (insert x s) =
      a x * finiteCoeffNumerator a r s +
        if r = 0 then 0 else finiteCoeffNumerator a (r - 1) s := by
  rcases r with _ | r
  · simp [finiteCoeffNumerator_zero, hx]
  · simpa using finiteCoeffNumerator_succ_insert a r x s hx

/-- The list-computed coefficient is the corresponding subset sum. -/
theorem coeff_eq_finiteCoeffNumerator (r p : ℕ) :
    coeff r p = finiteCoeffNumerator (fun q => q - 1) r (primesBelow p) := by
  induction p generalizing r with
  | zero =>
      rcases r with _ | r <;>
        simp [coeff, coeffRow, primesBelow, finiteCoeffNumerator,
          Finset.powersetCard]
  | succ p ih =>
      by_cases hp : p.Prime
      · rw [coeff_succ_of_prime r p hp]
        rw [show primesBelow (p + 1) = insert p (primesBelow p) by
          unfold primesBelow
          rw [Finset.range_add_one, Finset.filter_insert, if_pos hp]]
        rw [finiteCoeffNumerator_insert (fun q => q - 1) r p (primesBelow p)]
        · rw [ih]
          split_ifs
          · rfl
          · rw [ih]
        · simp [primesBelow]
      · rw [coeff_succ_of_not_prime r p hp]
        rw [show primesBelow (p + 1) = primesBelow p by
          unfold primesBelow
          rw [Finset.range_add_one, Finset.filter_insert, if_neg hp]]
        exact ih r

/-- The list-computed modulus is the product over the cutoff prime set. -/
theorem primeModulus_eq_prod_primesBelow (p : ℕ) :
    primeModulus p = ∏ q ∈ primesBelow p, q := by
  induction p with
  | zero => simp [primeModulus, primesBelow]
  | succ p ih =>
      rw [primeModulus_succ]
      by_cases hp : p.Prime
      · rw [if_pos hp]
        rw [show primesBelow (p + 1) = insert p (primesBelow p) by
          unfold primesBelow
          rw [Finset.range_add_one, Finset.filter_insert, if_pos hp]]
        simp [ih, primesBelow, mul_comm]
      · rw [if_neg hp]
        rw [show primesBelow (p + 1) = primesBelow p by
          unfold primesBelow
          rw [Finset.range_add_one, Finset.filter_insert, if_neg hp]]
        exact ih

/-- Exact-card mass in a finite independent divisibility model. -/
noncomputable def exactCardMass {I : Type*} [Fintype I] [DecidableEq I]
    (a : I → ℕ) (r : ℕ) : ℝ :=
  ∑ S ∈ (Finset.univ : Finset (Finset I)).filter (fun S => S.card = r),
    Erdos697.Bernoulli.weight Finset.univ
      (fun i => 1 / (a i : ℝ)) S

def exactCardNumerator {I : Type*} [Fintype I] [DecidableEq I]
    (a : I → ℕ) (r : ℕ) : ℕ :=
  ∑ S ∈ (Finset.univ : Finset (Finset I)).filter (fun S => S.card = r),
    ∏ i ∈ (Finset.univ : Finset I) \ S, (a i - 1)

theorem normalized_complement_product_eq_weight
    {I : Type*} [Fintype I] [DecidableEq I]
    (a : I → ℕ) (ha : ∀ i, 0 < a i) (S : Finset I) :
    (∏ i ∈ (Finset.univ : Finset I) \ S,
        ((a i - 1 : ℕ) : ℝ)) / (∏ i, (a i : ℝ)) =
      Erdos697.Bernoulli.weight (Finset.univ : Finset I)
        (fun i => 1 / (a i : ℝ)) S := by
  classical
  unfold Erdos697.Bernoulli.weight
  have hSsubset : S ⊆ (Finset.univ : Finset I) := fun _ _ => Finset.mem_univ _
  have hdisj : Disjoint S ((Finset.univ : Finset I) \ S) :=
    Finset.disjoint_sdiff
  have hunion : S ∪ ((Finset.univ : Finset I) \ S) = Finset.univ :=
    Finset.union_sdiff_of_subset hSsubset
  have hden_split :
      (∏ i, (a i : ℝ)) =
        (∏ i ∈ S, (a i : ℝ)) *
          ∏ i ∈ (Finset.univ : Finset I) \ S, (a i : ℝ) := by
    rw [← Finset.prod_union hdisj, hunion]
  have hfirst :
      (∏ i ∈ S, 1 / (a i : ℝ)) =
        1 / (∏ i ∈ S, (a i : ℝ)) := by
    simp only [one_div, Finset.prod_inv_distrib]
  have hsecond :
      (∏ i ∈ (Finset.univ : Finset I) \ S,
          (1 - 1 / (a i : ℝ))) =
        (∏ i ∈ (Finset.univ : Finset I) \ S,
          (((a i - 1 : ℕ) : ℝ))) /
          (∏ i ∈ (Finset.univ : Finset I) \ S, (a i : ℝ)) := by
    rw [← Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro i _
    have hai : (a i : ℝ) ≠ 0 := by exact_mod_cast (ha i).ne'
    rw [Nat.cast_sub (ha i)]
    norm_num
    field_simp
  rw [hfirst, hsecond, hden_split]
  have hAS : (∏ i ∈ S, (a i : ℝ)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    exact_mod_cast (ha i).ne'
  have hAC :
      (∏ i ∈ (Finset.univ : Finset I) \ S, (a i : ℝ)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    exact_mod_cast (ha i).ne'
  field_simp

theorem exactCardMass_eq_numerator_div
    {I : Type*} [Fintype I] [DecidableEq I]
    (a : I → ℕ) (ha : ∀ i, 0 < a i) (r : ℕ) :
    exactCardMass a r =
      (exactCardNumerator a r : ℝ) / ∏ i, (a i : ℝ) := by
  classical
  unfold exactCardMass exactCardNumerator
  push_cast
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro S _
  exact (normalized_complement_product_eq_weight a ha S).symm

def subtypePrimeNumerator (r p : ℕ) : ℕ :=
  exactCardNumerator (fun q : ↑(primesBelow p) => q.1) r

theorem subtypePrimeNumerator_eq_finiteCoeffNumerator (r p : ℕ) :
    subtypePrimeNumerator r p =
      finiteCoeffNumerator (fun q => q - 1) r (primesBelow p) := by
  classical
  unfold subtypePrimeNumerator exactCardNumerator finiteCoeffNumerator
  apply Finset.sum_bij
    (fun S (_ : S ∈ (Finset.univ : Finset (Finset ↑(primesBelow p))).filter
      (fun S => S.card = r)) => S.image Subtype.val)
  · intro S hS
    have hcard : S.card = r := (Finset.mem_filter.mp hS).2
    rw [Finset.mem_powersetCard]
    constructor
    · intro q hq
      obtain ⟨x, hxS, rfl⟩ := Finset.mem_image.mp hq
      exact x.2
    · have himage : (S.image Subtype.val).card = S.card := by
        apply Finset.card_image_iff.mpr
        intro a _ b _ hab
        exact Subtype.ext hab
      rw [himage, hcard]
  · intro S₁ hS₁ S₂ hS₂ hEq
    ext x
    have hx := Finset.ext_iff.mp hEq x.1
    simpa using hx
  · intro T hT
    have hTsub : T ⊆ primesBelow p := (Finset.mem_powersetCard.mp hT).1
    let S : Finset ↑(primesBelow p) :=
      (Finset.univ : Finset ↑(primesBelow p)).filter (fun q => q.1 ∈ T)
    refine ⟨S, ?_, ?_⟩
    · rw [Finset.mem_filter]
      constructor
      · exact Finset.mem_univ S
      · rw [show S.card = T.card by
          apply Finset.card_bij (fun q _ => q.1)
          · intro q hq
            exact (Finset.mem_filter.mp hq).2
          · intro q₁ hq₁ q₂ hq₂ heq
            exact Subtype.ext heq
          · intro q hq
            exact ⟨⟨q, hTsub hq⟩, by simp [S, hq], rfl⟩]
        exact (Finset.mem_powersetCard.mp hT).2
    · ext q
      simp only [Finset.mem_image]
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact (Finset.mem_filter.mp hx).2
      · intro hqT
        exact ⟨⟨q, hTsub hqT⟩, by simp [S, hqT], rfl⟩
  · intro S hS
    apply Finset.prod_bij (fun i _ => i.1)
    · intro i hi
      rw [Finset.mem_sdiff] at hi ⊢
      refine ⟨i.2, ?_⟩
      intro himage
      obtain ⟨j, hjS, hji⟩ := Finset.mem_image.mp himage
      apply hi.2
      have hji' : j = i := Subtype.ext hji
      simpa [hji'] using hjS
    · intro i₁ hi₁ i₂ hi₂ heq
      exact Subtype.ext heq
    · intro q hq
      rw [Finset.mem_sdiff] at hq
      let i : ↑(primesBelow p) := ⟨q, hq.1⟩
      refine ⟨i, ?_, rfl⟩
      rw [Finset.mem_sdiff]
      refine ⟨Finset.mem_univ i, ?_⟩
      intro hiS
      exact hq.2 (Finset.mem_image.mpr ⟨i, hiS, rfl⟩)
    · intro i hi
      rfl

/-- The exact-card Bernoulli probability is the fast cutoff coefficient ratio. -/
theorem subtype_exactCardMass_eq_coeff_div (r p : ℕ) :
    exactCardMass (fun q : ↑(primesBelow p) => q.1) r =
      (coeff r p : ℝ) / primeModulus p := by
  rw [exactCardMass_eq_numerator_div
    (fun q : ↑(primesBelow p) => q.1)
    (fun q => ((Finset.mem_filter.mp q.2).2).pos) r]
  change (subtypePrimeNumerator r p : ℝ) / _ = _
  rw [subtypePrimeNumerator_eq_finiteCoeffNumerator,
    ← coeff_eq_finiteCoeffNumerator]
  have hprod :
      (∏ q : ↑(primesBelow p), (q.1 : ℝ)) =
        ∏ q ∈ primesBelow p, (q : ℝ) := by
    symm
    simpa using (Finset.prod_subtype
      (p := fun q => q ∈ primesBelow p) (primesBelow p)
      (F := inferInstanceAs (Fintype ↑(primesBelow p)))
      (fun _ => Iff.rfl) (fun q : ℕ => (q : ℝ)))
  rw [hprod]
  have hden : (∏ q ∈ primesBelow p, (q : ℝ)) =
      (primeModulus p : ℝ) := by
    calc
      (∏ q ∈ primesBelow p, (q : ℝ)) =
          ((∏ q ∈ primesBelow p, q : ℕ) : ℝ) :=
            (Nat.cast_prod _ _).symm
      _ = (primeModulus p : ℝ) := by rw [primeModulus_eq_prod_primesBelow]
  rw [hden]

/-! ## Natural-density interpretation -/

private theorem hasDensity_of_counting_error
    (S : Set ℕ) (c C : ℝ)
    (h : ∀ n, |((S ∩ Set.Iio n).ncard : ℝ) - c * n| ≤ C) :
    S.HasDensity c := by
  rw [Set.HasDensity]
  have hzero : Tendsto
      (fun n : ℕ => (((S ∩ Set.Iio n).ncard : ℝ) - c * n) / n)
      atTop (𝓝 0) := by
    exact squeeze_zero_norm
      (fun n => by
        simpa [abs_div] using
          div_le_div_of_nonneg_right (h n) (Nat.cast_nonneg n))
      (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop)
  simpa only [zero_add] using (hzero.add_const c).congr' (by
    filter_upwards [eventually_gt_atTop 0] with n hn
    simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter]
    have hIio : (Set.Iio n).ncard = n := by simp
    rw [hIio]
    field_simp
    ring)

private theorem singleton_zero_hasDensity : ({0} : Set ℕ).HasDensity 0 := by
  apply hasDensity_of_counting_error _ _ 1
  intro n
  simp only [zero_mul, sub_zero, Nat.cast_nonneg, abs_of_nonneg]
  by_cases hn : n = 0
  · subst n
    simp
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have hset : ({0} : Set ℕ) ∩ Set.Iio n = {0} := by
      ext x
      simp [hnpos]
    rw [hset]
    simp

/-- Removing zero does not change natural density. -/
theorem HasDensity.diff_zero {S : Set ℕ} {d : ℝ}
    (hS : S.HasDensity d) :
    (S \ {0}).HasDensity d := by
  let U : Set ℕ := S ∩ {0}
  have hU : U.HasDensity 0 := by
    by_cases h0 : 0 ∈ S
    · have hUeq : U = {0} := by
        ext n
        simp only [U, Set.mem_inter_iff, Set.mem_singleton_iff]
        constructor
        · exact fun h => h.2
        · rintro rfl
          exact ⟨h0, rfl⟩
      rw [hUeq]
      exact singleton_zero_hasDensity
    · have hUeq : U = ∅ := by
        ext n
        simp only [U, Set.mem_inter_iff, Set.mem_singleton_iff,
          Set.mem_empty_iff_false, iff_false]
        rintro ⟨hnS, rfl⟩
        exact h0 hnS
      rw [hUeq]
      simp [Set.HasDensity, Set.partialDensity]
  rw [Set.HasDensity] at hS hU ⊢
  simpa only [sub_zero] using (hS.sub hU).congr' (by
    filter_upwards with n
    simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter]
    let T : Set ℕ := S \ {0}
    have hdisj : Disjoint T U := by
      rw [Set.disjoint_left]
      intro x hxT hxU
      exact hxT.2 hxU.2
    have hTU : T ∪ U = S := by
      ext x
      constructor
      · rintro (hx | hx)
        · exact hx.1
        · exact hx.1
      · intro hxS
        by_cases hx0 : x = 0
        · exact Or.inr ⟨hxS, by simpa using hx0⟩
        · exact Or.inl ⟨hxS, by simpa using hx0⟩
    have hdisj' : Disjoint (T ∩ Set.Iio n) (U ∩ Set.Iio n) :=
      hdisj.mono inter_subset_left inter_subset_left
    have hset : S ∩ Set.Iio n =
        (T ∩ Set.Iio n) ∪ (U ∩ Set.Iio n) := by
      rw [← Set.union_inter_distrib_right, hTU]
    rw [hset, Set.ncard_union_eq hdisj']
    push_cast
    change _ = ((T ∩ Set.Iio n).ncard : ℝ) / _
    ring)

/-- `p` is the one-based `k`th smallest distinct prime factor of `n`. -/
def IsKthSmallestPrimeFactor (k p n : ℕ) : Prop :=
  0 < k ∧ p ∈ n.primeFactors ∧
    (n.primeFactors.filter (fun q => q < p)).card = k - 1

/-- Positive integers whose one-based `k`th smallest distinct prime factor is `p`. -/
def kthPrimeFactorSet (k p : ℕ) : Set ℕ :=
  {n | IsKthSmallestPrimeFactor k p n}

theorem primeFactors_lt_eq_divisibility_filter
    {p n : ℕ} (hn0 : n ≠ 0) :
    n.primeFactors.filter (fun q => q < p) =
      (primesBelow p).filter (fun q => q ∣ n) := by
  ext q
  simp only [Finset.mem_filter, Nat.mem_primeFactors, primesBelow,
    Finset.mem_range]
  aesop

theorem selected_primesBelow_card (p n : ℕ) :
    (Erdos697.Cover.selected
      (fun q : ↑(primesBelow p) => q.1) n).card =
      ((primesBelow p).filter (fun q => q ∣ n)).card := by
  classical
  unfold Erdos697.Cover.selected
  apply Finset.card_bij (fun q _ => q.1)
  · intro q hq
    rw [Finset.mem_filter] at hq ⊢
    exact ⟨q.2, hq.2⟩
  · intro q₁ hq₁ q₂ hq₂ heq
    exact Subtype.ext heq
  · intro q hq
    rw [Finset.mem_filter] at hq
    exact ⟨⟨q, hq.1⟩, by simp [hq.2], rfl⟩

theorem kthPrimeFactorSet_eq_event
    {k p : ℕ} (hk : 0 < k) (hp : p.Prime) :
    kthPrimeFactorSet k p =
      Erdos697.Cover.eventSet p
        (fun q : ↑(primesBelow p) => q.1)
        (fun S => S.card = k - 1) \ {0} := by
  ext n
  simp only [kthPrimeFactorSet, IsKthSmallestPrimeFactor,
    Set.mem_setOf_eq, Set.mem_diff, Set.mem_singleton_iff,
    Erdos697.Cover.eventSet]
  constructor
  · rintro ⟨_, hpn, hcard⟩
    have hmem := Nat.mem_primeFactors.mp hpn
    have hn0 : n ≠ 0 := hmem.2.2
    rw [primeFactors_lt_eq_divisibility_filter hn0] at hcard
    rw [selected_primesBelow_card]
    exact ⟨⟨hmem.2.1, hcard⟩, hn0⟩
  · rintro ⟨⟨hpdvd, hcard⟩, hn0⟩
    rw [selected_primesBelow_card] at hcard
    rw [← primeFactors_lt_eq_divisibility_filter hn0] at hcard
    exact ⟨hk, Nat.mem_primeFactors.mpr ⟨hp, hpdvd, hn0⟩, hcard⟩

theorem subtype_primesBelow_pairwise_coprime (p : ℕ) :
    Pairwise (Function.onFun Nat.Coprime
      (fun q : ↑(primesBelow p) => q.1)) := by
  intro q r hqr
  change Nat.Coprime q.1 r.1
  have hqprime : q.1.Prime := (Finset.mem_filter.mp q.2).2
  have hrprime : r.1.Prime := (Finset.mem_filter.mp r.2).2
  rw [Nat.coprime_primes hqprime hrprime]
  intro heq
  exact hqr (Subtype.ext heq)

theorem target_coprime_primesBelow {p : ℕ} (hp : p.Prime)
    (q : ↑(primesBelow p)) : Nat.Coprime p q.1 := by
  have hqprime : q.1.Prime := (Finset.mem_filter.mp q.2).2
  have hqlt : q.1 < p := Finset.mem_range.mp
    (Finset.mem_filter.mp q.2).1
  rw [Nat.coprime_primes hp hqprime]
  exact ne_of_gt hqlt

/-- Exact density of the prime-factor-position event, in a direct real formula. -/
theorem kthPrimeFactorSet_hasDensity_formula
    {k p : ℕ} (hk : 0 < k) (hp : p.Prime) :
    (kthPrimeFactorSet k p).HasDensity
      ((1 : ℝ) / p * ((coeff (k - 1) p : ℝ) / primeModulus p)) := by
  have hperiodic := Erdos697.Cover.eventSet_hasDensity
    p hp.pos
    (fun q : ↑(primesBelow p) => q.1)
    (fun q => ((Finset.mem_filter.mp q.2).2).pos)
    (subtype_primesBelow_pairwise_coprime p)
    (target_coprime_primesBelow hp)
    (fun S : Finset ↑(primesBelow p) => S.card = k - 1)
  change (Erdos697.Cover.eventSet p
      (fun q : ↑(primesBelow p) => q.1)
      (fun S => S.card = k - 1)).HasDensity
    ((1 : ℝ) / p * exactCardMass
      (fun q : ↑(primesBelow p) => q.1) (k - 1)) at hperiodic
  rw [kthPrimeFactorSet_eq_event hk hp]
  apply HasDensity.diff_zero
  convert hperiodic using 1
  rw [subtype_exactCardMass_eq_coeff_div]

/-- The natural density is exactly the rational value used in the finite
unimodality computation. -/
theorem kthPrimeFactorSet_hasDensity
    {k p : ℕ} (hk : 0 < k) (hp : p.Prime) :
    (kthPrimeFactorSet k p).HasDensity
      ((primeFactorDensity k p : ℚ) : ℝ) := by
  convert kthPrimeFactorSet_hasDensity_formula hk hp using 1
  rw [primeFactorDensity, if_pos ⟨hk, hp⟩]
  push_cast
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hm0 : (primeModulus p : ℝ) ≠ 0 := by
    exact_mod_cast (primeModulus_pos p).ne'
  field_simp

/-! ## Unimodality along the primes -/

/-- A function is unimodal along the ordered primes if it is nondecreasing up
to a prime mode and nonincreasing thereafter. -/
def UnimodalOnPrimes {α : Type*} [Preorder α] (f : ℕ → α) : Prop :=
  ∃ m, m.Prime ∧
    (∀ p q, p.Prime → q.Prime → p ≤ q → q ≤ m → f p ≤ f q) ∧
    (∀ p q, p.Prime → q.Prime → m ≤ p → p ≤ q → f q ≤ f p)

def DensityUnimodal (k : ℕ) : Prop :=
  UnimodalOnPrimes (primeFactorDensity k)

/-- A strict valley at three ordered primes rules out unimodality. -/
theorem not_unimodal_of_valley {α : Type*} [Preorder α]
    (f : ℕ → α) (a b c : ℕ)
    (ha : a.Prime) (hb : b.Prime) (hc : c.Prime)
    (hab : a < b) (hbc : b < c)
    (hba : f b < f a) (hbcv : f b < f c) :
    ¬UnimodalOnPrimes f := by
  rintro ⟨m, hm, hinc, hdec⟩
  by_cases hmb : m ≤ b
  · exact (not_le_of_gt hbcv) (hdec b c hb hc hmb hbc.le)
  · have hbm : b ≤ m := Nat.le_of_lt (Nat.lt_of_not_ge hmb)
    exact (not_le_of_gt hba) (hinc a b ha hb hab.le hbm)

/-! ## Positive cases -/

/-- A recursion-friendly implementation of `coeff`, used to establish the
coefficient recurrence between arbitrary consecutive primes. -/
def coeffRec : ℕ → ℕ → ℕ
  | r, 0 => if r = 0 then 1 else 0
  | r, p + 1 =>
      if p.Prime then
        (p - 1) * coeffRec r p + if r = 0 then 0 else coeffRec (r - 1) p
      else coeffRec r p
termination_by _ p => p

theorem coeffRec_eq_coeff (r p : ℕ) : coeffRec r p = coeff r p := by
  induction p generalizing r with
  | zero =>
      rcases r with _ | r <;> simp [coeffRec, coeff, coeffRow, List.getD]
  | succ p ih =>
      by_cases hp : p.Prime
      · rw [coeffRec, if_pos hp, coeff_succ_of_prime r p hp]
        rw [ih]
        split_ifs
        · rfl
        · rw [ih]
      · rw [coeffRec, if_neg hp, coeff_succ_of_not_prime r p hp, ih]

theorem coeffRec_eq_of_no_prime (r a b : ℕ) (hab : a ≤ b)
    (hprime : ∀ n, a ≤ n → n < b → ¬n.Prime) :
    coeffRec r b = coeffRec r a := by
  induction b, hab using Nat.le_induction with
  | base => rfl
  | succ b hab ih =>
      rw [coeffRec, if_neg (hprime b hab (Nat.lt_succ_self b)), ih]
      intro n han hnb
      exact hprime n han (hnb.trans (Nat.lt_succ_self b))

/-- `p` and `q` are consecutive primes in the usual order. -/
def ConsecutivePrimes (p q : ℕ) : Prop :=
  p.Prime ∧ q.Prime ∧ p < q ∧
    ∀ r, r.Prime → p < r → r < q → False

theorem coeff_consecutive (r p q : ℕ) (hpq : ConsecutivePrimes p q) :
    coeff r q = (p - 1) * coeff r p +
      if r = 0 then 0 else coeff (r - 1) p := by
  rw [← coeffRec_eq_coeff]
  have heq : coeffRec r q = coeffRec r (p + 1) := by
    have hpqlt : p < q := hpq.2.2.1
    apply coeffRec_eq_of_no_prime r (p + 1) q
    · omega
    · intro n hpn hnq hnp
      exact hpq.2.2.2 n hnp (by omega) hnq
  rw [heq, coeffRec, if_pos hpq.1]
  rw [coeffRec_eq_coeff, coeffRec_eq_coeff]

/-- A recursion-friendly implementation of `primeModulus`. -/
def modulusRec : ℕ → ℕ
  | 0 => 1
  | p + 1 => if p.Prime then modulusRec p * p else modulusRec p

theorem modulusRec_eq (p : ℕ) : modulusRec p = primeModulus p := by
  induction p with
  | zero => rfl
  | succ p ih => rw [modulusRec, primeModulus_succ, ih]

theorem modulusRec_eq_of_no_prime (a b : ℕ) (hab : a ≤ b)
    (hprime : ∀ n, a ≤ n → n < b → ¬n.Prime) :
    modulusRec b = modulusRec a := by
  induction b, hab using Nat.le_induction with
  | base => rfl
  | succ b hab ih =>
      rw [modulusRec, if_neg (hprime b hab (Nat.lt_succ_self b)), ih]
      intro n han hnb
      exact hprime n han (hnb.trans (Nat.lt_succ_self b))

theorem primeModulus_consecutive (p q : ℕ) (hpq : ConsecutivePrimes p q) :
    primeModulus q = primeModulus p * p := by
  rw [← modulusRec_eq]
  have heq : modulusRec q = modulusRec (p + 1) := by
    have hpqlt : p < q := hpq.2.2.1
    apply modulusRec_eq_of_no_prime (p + 1) q
    · omega
    · intro n hpn hnq hnp
      exact hpq.2.2.2 n hnp (by omega) hnq
  rw [heq, modulusRec, if_pos hpq.1, modulusRec_eq]

/-- The first low-degree coefficient invariant used for `k = 2`. -/
theorem coeff_zero_le_three_coeff_one (p : ℕ) (hp : 3 ≤ p) :
    coeff 0 p ≤ 3 * coeff 1 p := by
  induction p, hp using Nat.le_induction with
  | base => decide
  | succ p hp ih =>
      by_cases hprime : p.Prime
      · rw [coeff_succ_of_prime 0 p hprime, coeff_succ_of_prime 1 p hprime]
        norm_num only
        calc
          (p - 1) * coeff 0 p ≤ (p - 1) * (3 * coeff 1 p) :=
            Nat.mul_le_mul_left (p - 1) ih
          _ = 3 * ((p - 1) * coeff 1 p) := by ring
          _ ≤ 3 * ((p - 1) * coeff 1 p + coeff 0 p) := by omega
      · simpa [coeff_succ_of_not_prime 0 p hprime,
          coeff_succ_of_not_prime 1 p hprime] using ih

/-- The second low-degree coefficient invariant used for `k = 3`. -/
theorem coeff_one_le_three_coeff_two (p : ℕ) (hp : 5 ≤ p) :
    coeff 1 p ≤ 3 * coeff 2 p := by
  induction p, hp using Nat.le_induction with
  | base => decide
  | succ p hp ih =>
      by_cases hprime : p.Prime
      · rw [coeff_succ_of_prime 1 p hprime, coeff_succ_of_prime 2 p hprime]
        norm_num only
        rw [Nat.mul_add]
        apply Nat.add_le_add
        · calc
            (p - 1) * coeff 1 p ≤ (p - 1) * (3 * coeff 2 p) :=
              Nat.mul_le_mul_left (p - 1) ih
            _ = 3 * ((p - 1) * coeff 2 p) := by ring
        · exact coeff_zero_le_three_coeff_one p (by omega)
      · simpa [coeff_succ_of_not_prime 1 p hprime,
          coeff_succ_of_not_prime 2 p hprime] using ih

/-- The coefficient threshold implies that the density cannot increase
across a pair of consecutive primes. -/
theorem density_next_le (k p q : ℕ) (hk : 2 ≤ k)
    (hpq : ConsecutivePrimes p q)
    (hthreshold : coeff (k - 2) p ≤ (q - p + 1) * coeff (k - 1) p) :
    primeFactorDensity k q ≤ primeFactorDensity k p := by
  have hkpos : 0 < k := by omega
  have hpqlt : p < q := hpq.2.2.1
  have hppos : 0 < p := hpq.1.pos
  rw [primeFactorDensity, if_pos ⟨hkpos, hpq.2.1⟩]
  rw [primeFactorDensity, if_pos ⟨hkpos, hpq.1⟩]
  have hkpred : k - 1 ≠ 0 := by omega
  have hcoeff : coeff (k - 1) q ≤ q * coeff (k - 1) p := by
    rw [coeff_consecutive (k - 1) p q hpq, if_neg hkpred]
    have hsub : (k - 1) - 1 = k - 2 := by omega
    rw [hsub]
    calc
      (p - 1) * coeff (k - 1) p + coeff (k - 2) p ≤
          (p - 1) * coeff (k - 1) p +
            (q - p + 1) * coeff (k - 1) p :=
        Nat.add_le_add_left hthreshold _
      _ = q * coeff (k - 1) p := by
        rw [← Nat.add_mul]
        congr 1
        omega
  rw [primeModulus_consecutive p q hpq]
  have hdenq : (0 : ℚ) < (q * (primeModulus p * p) : ℕ) := by
    exact_mod_cast Nat.mul_pos hpq.2.1.pos (Nat.mul_pos (primeModulus_pos p) hpq.1.pos)
  have hdenp : (0 : ℚ) < (p * primeModulus p : ℕ) := by
    exact_mod_cast Nat.mul_pos hpq.1.pos (primeModulus_pos p)
  apply (div_le_div_iff₀ hdenq hdenp).2
  have hcross :
      coeff (k - 1) q * (p * primeModulus p) ≤
        coeff (k - 1) p * (q * (primeModulus p * p)) := by
    calc
      coeff (k - 1) q * (p * primeModulus p) ≤
          (q * coeff (k - 1) p) * (p * primeModulus p) :=
        Nat.mul_le_mul_right _ hcoeff
      _ = coeff (k - 1) p * (q * (primeModulus p * p)) := by ring
  exact_mod_cast hcross

theorem density_next_lt_of_coeff_lt (k p q : ℕ) (hk : 2 ≤ k)
    (hpq : ConsecutivePrimes p q)
    (hthreshold : coeff (k - 2) p < (q - p + 1) * coeff (k - 1) p) :
    primeFactorDensity k q < primeFactorDensity k p := by
  have hkpos : 0 < k := by omega
  have hpqlt : p < q := hpq.2.2.1
  have hppos : 0 < p := hpq.1.pos
  rw [primeFactorDensity, if_pos ⟨hkpos, hpq.2.1⟩]
  rw [primeFactorDensity, if_pos ⟨hkpos, hpq.1⟩]
  have hkpred : k - 1 ≠ 0 := by omega
  have hcoeff : coeff (k - 1) q < q * coeff (k - 1) p := by
    rw [coeff_consecutive (k - 1) p q hpq, if_neg hkpred]
    have hsub : (k - 1) - 1 = k - 2 := by omega
    rw [hsub]
    calc
      (p - 1) * coeff (k - 1) p + coeff (k - 2) p <
          (p - 1) * coeff (k - 1) p +
            (q - p + 1) * coeff (k - 1) p :=
        Nat.add_lt_add_left hthreshold _
      _ = q * coeff (k - 1) p := by
        rw [← Nat.add_mul]
        congr 1
        omega
  rw [primeModulus_consecutive p q hpq]
  have hdenq : (0 : ℚ) < (q * (primeModulus p * p) : ℕ) := by
    exact_mod_cast Nat.mul_pos hpq.2.1.pos (Nat.mul_pos (primeModulus_pos p) hpq.1.pos)
  have hdenp : (0 : ℚ) < (p * primeModulus p : ℕ) := by
    exact_mod_cast Nat.mul_pos hpq.1.pos (primeModulus_pos p)
  apply (div_lt_div_iff₀ hdenq hdenp).2
  have hcross :
      coeff (k - 1) q * (p * primeModulus p) <
        coeff (k - 1) p * (q * (primeModulus p * p)) := by
    calc
      coeff (k - 1) q * (p * primeModulus p) <
          (q * coeff (k - 1) p) * (p * primeModulus p) :=
        Nat.mul_lt_mul_of_pos_right hcoeff (Nat.mul_pos hpq.1.pos (primeModulus_pos p))
      _ = coeff (k - 1) p * (q * (primeModulus p * p)) := by ring
  exact_mod_cast hcross

theorem density_lt_next_of_coeff_lt (k p q : ℕ) (hk : 2 ≤ k)
    (hpq : ConsecutivePrimes p q)
    (hthreshold : (q - p + 1) * coeff (k - 1) p < coeff (k - 2) p) :
    primeFactorDensity k p < primeFactorDensity k q := by
  have hkpos : 0 < k := by omega
  have hpqlt : p < q := hpq.2.2.1
  have hppos : 0 < p := hpq.1.pos
  rw [primeFactorDensity, if_pos ⟨hkpos, hpq.1⟩]
  rw [primeFactorDensity, if_pos ⟨hkpos, hpq.2.1⟩]
  have hkpred : k - 1 ≠ 0 := by omega
  have hcoeff : q * coeff (k - 1) p < coeff (k - 1) q := by
    rw [coeff_consecutive (k - 1) p q hpq, if_neg hkpred]
    have hsub : (k - 1) - 1 = k - 2 := by omega
    rw [hsub]
    calc
      q * coeff (k - 1) p =
          (p - 1) * coeff (k - 1) p +
            (q - p + 1) * coeff (k - 1) p := by
        rw [← Nat.add_mul]
        congr 1
        omega
      _ < (p - 1) * coeff (k - 1) p + coeff (k - 2) p :=
        Nat.add_lt_add_left hthreshold _
  rw [primeModulus_consecutive p q hpq]
  have hdenp : (0 : ℚ) < (p * primeModulus p : ℕ) := by
    exact_mod_cast Nat.mul_pos hpq.1.pos (primeModulus_pos p)
  have hdenq : (0 : ℚ) < (q * (primeModulus p * p) : ℕ) := by
    exact_mod_cast Nat.mul_pos hpq.2.1.pos (Nat.mul_pos (primeModulus_pos p) hpq.1.pos)
  apply (div_lt_div_iff₀ hdenp hdenq).2
  have hcross :
      coeff (k - 1) p * (q * (primeModulus p * p)) <
        coeff (k - 1) q * (p * primeModulus p) := by
    calc
      coeff (k - 1) p * (q * (primeModulus p * p)) =
          (q * coeff (k - 1) p) * (p * primeModulus p) := by ring
      _ < coeff (k - 1) q * (p * primeModulus p) :=
        Nat.mul_lt_mul_of_pos_right hcoeff (Nat.mul_pos hpq.1.pos (primeModulus_pos p))
  exact_mod_cast hcross

/-- Consecutive odd primes have gap at least two. -/
theorem consecutive_odd_prime_gap (p q : ℕ) (hpq : ConsecutivePrimes p q)
    (hp3 : 3 ≤ p) : 3 ≤ q - p + 1 := by
  have hpqlt : p < q := hpq.2.2.1
  have hpne : p ≠ 2 := by omega
  have hqne : q ≠ 2 := by omega
  obtain ⟨a, ha⟩ := hpq.1.odd_of_ne_two hpne
  obtain ⟨b, hb⟩ := hpq.2.1.odd_of_ne_two hqne
  omega

theorem density_two_next_le (p q : ℕ) (hpq : ConsecutivePrimes p q)
    (hp3 : 3 ≤ p) :
    primeFactorDensity 2 q ≤ primeFactorDensity 2 p := by
  apply density_next_le 2 p q (by omega) hpq
  norm_num only [Nat.reduceSubDiff]
  exact (coeff_zero_le_three_coeff_one p hp3).trans
    (Nat.mul_le_mul_right (coeff 1 p) (consecutive_odd_prime_gap p q hpq hp3))

theorem density_three_next_le (p q : ℕ) (hpq : ConsecutivePrimes p q)
    (hp5 : 5 ≤ p) :
    primeFactorDensity 3 q ≤ primeFactorDensity 3 p := by
  apply density_next_le 3 p q (by omega) hpq
  norm_num only [Nat.reduceSubDiff]
  exact (coeff_one_le_three_coeff_two p hp5).trans
    (Nat.mul_le_mul_right (coeff 2 p)
      (consecutive_odd_prime_gap p q hpq (by omega)))

theorem density_one_next_le (p q : ℕ) (hpq : ConsecutivePrimes p q) :
    primeFactorDensity 1 q ≤ primeFactorDensity 1 p := by
  rw [primeFactorDensity, if_pos ⟨by omega, hpq.2.1⟩]
  rw [primeFactorDensity, if_pos ⟨by omega, hpq.1⟩]
  norm_num only [Nat.reduceSubDiff]
  rw [coeff_consecutive 0 p q hpq]
  rw [primeModulus_consecutive p q hpq]
  have hpqlt : p < q := hpq.2.2.1
  have hcoeff : (p - 1) * coeff 0 p ≤ q * coeff 0 p := by
    exact Nat.mul_le_mul_right _ (by omega : p - 1 ≤ q)
  have hdenq : (0 : ℚ) < (q * (primeModulus p * p) : ℕ) := by
    exact_mod_cast Nat.mul_pos hpq.2.1.pos (Nat.mul_pos (primeModulus_pos p) hpq.1.pos)
  have hdenp : (0 : ℚ) < (p * primeModulus p : ℕ) := by
    exact_mod_cast Nat.mul_pos hpq.1.pos (primeModulus_pos p)
  apply (div_le_div_iff₀ hdenq hdenp).2
  exact_mod_cast (show
    ((p - 1) * coeff 0 p) * (p * primeModulus p) ≤
      coeff 0 p * (q * (primeModulus p * p)) by
        calc
          ((p - 1) * coeff 0 p) * (p * primeModulus p) ≤
              (q * coeff 0 p) * (p * primeModulus p) :=
            Nat.mul_le_mul_right _ hcoeff
          _ = coeff 0 p * (q * (primeModulus p * p)) := by ring)

/-- Lift a comparison across consecutive primes to arbitrary ordered primes. -/
theorem prime_le_of_consecutive_le_from {α : Type*} [Preorder α]
    (f : ℕ → α) (m : ℕ)
    (hstep : ∀ p q, m ≤ p → ConsecutivePrimes p q → f p ≤ f q)
    (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hmp : m ≤ p) (hpq : p ≤ q) :
    f p ≤ f q := by
  by_cases heq : p = q
  · subst q
    exact le_rfl
  · have hpqlt : p < q := lt_of_le_of_ne hpq heq
    by_cases hbetween : ∀ r, r.Prime → p < r → r < q → False
    · exact hstep p q hmp ⟨hp, hq, hpqlt, hbetween⟩
    · push Not at hbetween
      obtain ⟨r, hrp, hpr, hrq, _⟩ := hbetween
      exact (prime_le_of_consecutive_le_from f m hstep p r hp hrp hmp hpr.le).trans
        (prime_le_of_consecutive_le_from f m hstep r q hrp hq
          (hmp.trans hpr.le) hrq.le)
termination_by q - p
decreasing_by
  · omega
  · exact Nat.sub_lt_sub_left hpqlt hpr

theorem density_two_at_two : primeFactorDensity 2 2 = 0 := by
  rw [primeFactorDensity, if_pos ⟨by omega, Nat.prime_two⟩]
  rw [show coeff (2 - 1) 2 = 0 by rfl]
  simp

theorem density_two_at_three : primeFactorDensity 2 3 = 1 / 6 := by rfl

theorem density_three_at_two : primeFactorDensity 3 2 = 0 := by
  rw [primeFactorDensity, if_pos ⟨by omega, Nat.prime_two⟩]
  rw [show coeff (3 - 1) 2 = 0 by rfl]
  simp

theorem density_three_at_three : primeFactorDensity 3 3 = 0 := by
  rw [primeFactorDensity, if_pos ⟨by omega, Nat.prime_three⟩]
  rw [show coeff (3 - 1) 3 = 0 by rfl]
  simp

theorem density_three_at_five : primeFactorDensity 3 5 = 1 / 30 := by rfl

theorem density_one_unimodal : DensityUnimodal 1 := by
  refine ⟨2, Nat.prime_two, ?_, ?_⟩
  · intro p q hp hq hpq hq2
    have hp2 := hp.two_le
    have hq2' := hq.two_le
    have : p = q := by omega
    subst q
    exact le_rfl
  · intro p q hp hq h2p hpq
    exact prime_le_of_consecutive_le_from
      (fun n => OrderDual.toDual (primeFactorDensity 1 n)) 2
      (fun a b _ hab => density_one_next_le a b hab) p q hp hq h2p hpq

theorem density_two_unimodal : DensityUnimodal 2 := by
  refine ⟨3, Nat.prime_three, ?_, ?_⟩
  · intro p q hp hq hpq hq3
    have hp3 : p ≤ 3 := hpq.trans hq3
    have hpCases : p = 2 ∨ p = 3 := by
      have hp2 := hp.two_le
      omega
    have hqCases : q = 2 ∨ q = 3 := by
      have hq2 := hq.two_le
      omega
    rcases hpCases with hp2 | hp3 <;> rcases hqCases with hq2 | hq3
    · subst p; subst q; exact le_rfl
    · subst p; subst q
      rw [density_two_at_two, density_two_at_three]
      norm_num
    · omega
    · subst p; subst q; exact le_rfl
  · intro p q hp hq h3p hpq
    exact prime_le_of_consecutive_le_from
      (fun n => OrderDual.toDual (primeFactorDensity 2 n)) 3
      (fun a b ha hab => density_two_next_le a b hab ha) p q hp hq h3p hpq

theorem density_three_unimodal : DensityUnimodal 3 := by
  refine ⟨5, Nat.prime_five, ?_, ?_⟩
  · intro p q hp hq hpq hq5
    have hp5 : p ≤ 5 := hpq.trans hq5
    have classify (n : ℕ) (hn : n.Prime) (hn5 : n ≤ 5) :
        n = 2 ∨ n = 3 ∨ n = 5 := by
      have hn2 := hn.two_le
      interval_cases n <;> norm_num at hn <;> omega
    rcases classify p hp hp5 with hp2 | hp3 | hp5eq <;>
      rcases classify q hq hq5 with hq2 | hq3 | hq5eq
    · subst p; subst q; exact le_rfl
    · subst p; subst q; rw [density_three_at_two, density_three_at_three]
    · subst p; subst q
      rw [density_three_at_two, density_three_at_five]
      norm_num
    · omega
    · subst p; subst q; exact le_rfl
    · subst p; subst q
      rw [density_three_at_three, density_three_at_five]
      norm_num
    · omega
    · omega
    · subst p; subst q; exact le_rfl
  · intro p q hp hq h5p hpq
    exact prime_le_of_consecutive_le_from
      (fun n => OrderDual.toDual (primeFactorDensity 3 n)) 5
      (fun a b ha hab => density_three_next_le a b hab ha) p q hp hq h5p hpq

/-! ## Kernel-checked finite coefficient evaluator -/

/-- Interpret a coefficient list as a polynomial. -/
noncomputable def listPoly : List ℕ → Polynomial ℕ
  | [] => 0
  | a :: xs => Polynomial.C a + Polynomial.X * listPoly xs

@[simp] theorem listPoly_coeff (xs : List ℕ) (r : ℕ) :
    (listPoly xs).coeff r = xs.getD r 0 := by
  induction xs generalizing r with
  | nil => simp [listPoly, List.getD]
  | cons a xs ih =>
      rcases r with _ | r
      · simp [listPoly, List.getD]
      · simp [listPoly, ih, List.getD]

/-- Agreement of a truncated coefficient row with a polynomial. -/
def PolyAgree (d : ℕ) (xs : List ℕ) (P : Polynomial ℕ) : Prop :=
  ∀ r, r ≤ d → xs.getD r 0 = P.coeff r

/-- Truncated convolution, written with the same antidiagonal as
`Polynomial.coeff_mul`. -/
def convolveTo (d : ℕ) (xs ys : List ℕ) : List ℕ :=
  (List.range (d + 1)).map fun r =>
    ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal r,
      xs.getD ij.1 0 * ys.getD ij.2 0

theorem convolveTo_getD (d r : ℕ) (xs ys : List ℕ) (hr : r ≤ d) :
    (convolveTo d xs ys).getD r 0 =
      ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal r,
        xs.getD ij.1 0 * ys.getD ij.2 0 := by
  simp [convolveTo, List.getD, hr]

theorem PolyAgree.mul {d : ℕ} {xs ys : List ℕ}
    {P Q : Polynomial ℕ} (hx : PolyAgree d xs P) (hy : PolyAgree d ys Q) :
    PolyAgree d (convolveTo d xs ys) (P * Q) := by
  intro r hr
  rw [convolveTo_getD d r xs ys hr, Polynomial.coeff_mul]
  apply Finset.sum_congr rfl
  intro ij hij
  have hs : ij.1 + ij.2 = r :=
    Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  rw [hx ij.1 (by omega), hy ij.2 (by omega)]

def factorRow (p : ℕ) : List ℕ := [p - 1, 1]

noncomputable def factorPoly (p : ℕ) : Polynomial ℕ :=
  Polynomial.C (p - 1) + Polynomial.X

theorem factorRow_agree (d p : ℕ) :
    PolyAgree d (factorRow p) (factorPoly p) := by
  intro r hr
  rcases r with _ | r
  · simp [factorRow, factorPoly, List.getD]
  · rcases r with _ | r
    · simp [factorRow, factorPoly, List.getD, Polynomial.coeff_X]
    · simp [factorRow, factorPoly, List.getD, Polynomial.coeff_X]

theorem singleton_one_agree (d : ℕ) :
    PolyAgree d [1] (1 : Polynomial ℕ) := by
  intro r hr
  rcases r with _ | r <;> simp [List.getD, Polynomial.coeff_one]

def bucketRow (d : ℕ) : List ℕ → List ℕ
  | [] => [1]
  | p :: ps => convolveTo d (factorRow p) (bucketRow d ps)

/-- A sparse multiplication step, used for computation inside the explicit
prime chunks.  Unlike a generic convolution it exploits that a factor has
only the two coefficients `p - 1` and `1`. -/
def fastBucketRow : List ℕ → List ℕ
  | [] => [1]
  | p :: ps => coeffStep (p - 1) (fastBucketRow ps)

theorem coeffStep_agree {d a : ℕ} {row : List ℕ} {P : Polynomial ℕ}
    (h : PolyAgree d row P) :
    PolyAgree d (coeffStep a row) ((Polynomial.C a + Polynomial.X) * P) := by
  intro r hr
  rw [coeffStep_getD]
  rcases r with _ | r
  · rw [if_pos rfl, h 0 (Nat.zero_le d)]
    simp
  · simp only [Nat.succ_ne_zero, if_false, Nat.succ_sub_one, add_mul,
      Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_mul]
    rw [h (r + 1) hr, h r (by omega)]

noncomputable def primePoly : List ℕ → Polynomial ℕ
  | [] => 1
  | p :: ps => factorPoly p * primePoly ps

theorem fastBucketRow_agree (d : ℕ) (ps : List ℕ) :
    PolyAgree d (fastBucketRow ps) (primePoly ps) := by
  induction ps with
  | nil => exact singleton_one_agree d
  | cons p ps ih =>
      simpa [fastBucketRow, primePoly, factorPoly] using
        (coeffStep_agree (d := d) (a := p - 1) ih)

theorem bucketRow_agree (d : ℕ) (ps : List ℕ) :
    PolyAgree d (bucketRow d ps) (primePoly ps) := by
  induction ps with
  | nil => exact singleton_one_agree d
  | cons p ps ih => exact (factorRow_agree d p).mul ih

theorem primePoly_append (xs ys : List ℕ) :
    primePoly (xs ++ ys) = primePoly xs * primePoly ys := by
  induction xs with
  | nil => simp [primePoly]
  | cons x xs ih => simp [primePoly, ih, mul_assoc]

def primeChunk00 : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
def primeChunk01 : List ℕ := [37, 41, 43, 47, 53, 59, 61]
def primeChunk02 : List ℕ := [67, 71, 73, 79, 83, 89]
def primeChunk03 : List ℕ := [97, 101, 103, 107, 109, 113, 127]
def primeChunk04 : List ℕ := [131, 137, 139, 149, 151, 157]
def primeChunk05 : List ℕ := [163, 167, 173, 179, 181, 191]
def primeChunk06 : List ℕ := [193, 197, 199, 211, 223]
def primeChunk07 : List ℕ := [227, 229, 233, 239, 241, 251]
def primeChunk08 : List ℕ := [257, 263, 269, 271, 277, 281, 283]
def primeChunk09 : List ℕ := [293, 307, 311, 313, 317]
def primeChunk10 : List ℕ := [331, 337, 347, 349]
def primeChunk11 : List ℕ := [353, 359, 367, 373, 379, 383]
def primeChunk12 : List ℕ := [389, 397, 401, 409]
def primeChunk13 : List ℕ := [419, 421, 431, 433, 439, 443]
def primeChunk14 : List ℕ := [449, 457, 461, 463, 467, 479]
def primeChunk15 : List ℕ := [487, 491, 499, 503, 509]
def primeChunk16 : List ℕ := [521, 523, 541]
def primeChunk17 : List ℕ := [547, 557, 563, 569, 571]
def primeChunk18 : List ℕ := [577, 587, 593, 599, 601, 607]
def primeChunk19 : List ℕ := [613, 617, 619, 631]
def primeChunk20 : List ℕ := [641, 643, 647, 653, 659, 661]
def primeChunk21 : List ℕ := [673, 677, 683, 691, 701]
def primeChunk22 : List ℕ := [709, 719, 727, 733]
def primeChunk23 : List ℕ := [739, 743, 751, 757, 761]
def primeChunk24 : List ℕ := [769, 773, 787, 797]
def primeChunk25 : List ℕ := [809, 811, 821, 823, 827, 829]
def primeChunk26 : List ℕ := [839, 853, 857, 859, 863]
def primeChunk27 : List ℕ := [877, 881, 883, 887]
def primeChunk28 : List ℕ := [907, 911, 919]
def primeChunk29 : List ℕ := [929, 937, 941, 947, 953]
def primeChunk30 : List ℕ := [967, 971, 977, 983, 991]
def primeChunk31 : List ℕ := [997, 1009, 1013, 1019, 1021]
def primeChunk32 : List ℕ := [1031, 1033, 1039, 1049, 1051]
def primeChunk33 : List ℕ := [1061, 1063, 1069, 1087]
def primeChunk34 : List ℕ := [1091, 1093, 1097, 1103, 1109, 1117]
def primeChunk35 : List ℕ := [1123, 1129, 1151]
def primeChunk36 : List ℕ := []

def primes0 : List ℕ :=
  ((primeChunk00 ++ primeChunk01) ++ primeChunk02) ++ primeChunk03
def primes1 : List ℕ :=
  ((primeChunk04 ++ primeChunk05) ++ primeChunk06) ++ primeChunk07
def primes2 : List ℕ :=
  ((primeChunk08 ++ primeChunk09) ++ primeChunk10) ++ primeChunk11
def primes3 : List ℕ :=
  ((primeChunk12 ++ primeChunk13) ++ primeChunk14) ++ primeChunk15
def primes4 : List ℕ :=
  ((primeChunk16 ++ primeChunk17) ++ primeChunk18) ++ primeChunk19
def primes5 : List ℕ :=
  ((primeChunk20 ++ primeChunk21) ++ primeChunk22) ++ primeChunk23
def primes6 : List ℕ :=
  ((primeChunk24 ++ primeChunk25) ++ primeChunk26) ++ primeChunk27
def primes7 : List ℕ :=
  ((primeChunk28 ++ primeChunk29) ++ primeChunk30) ++ primeChunk31
def primes8 : List ℕ :=
  (((primeChunk32 ++ primeChunk33) ++ primeChunk34) ++ primeChunk35) ++
    primeChunk36

def primeSource (start : ℕ) : List ℕ :=
  if start = 0 then primes0
  else if start = 128 then primes1
  else if start = 256 then primes2
  else if start = 384 then primes3
  else if start = 512 then primes4
  else if start = 640 then primes5
  else if start = 768 then primes6
  else if start = 896 then primes7
  else primes8

def primeBlock (start _size p : ℕ) : List ℕ :=
  (primeSource start).filter (fun q => q < p)

def selectedPrimes (p : ℕ) : List ℕ :=
  ((((((((primeBlock 0 128 p ++ primeBlock 128 128 p) ++
      primeBlock 256 128 p) ++ primeBlock 384 128 p) ++
      primeBlock 512 128 p) ++ primeBlock 640 128 p) ++
      primeBlock 768 128 p) ++ primeBlock 896 128 p) ++
      primeBlock 1024 129 p)

noncomputable def blockPoly (start size p : ℕ) : Polynomial ℕ :=
  primePoly (primeBlock start size p)

noncomputable def leftBlockPoly (p : ℕ) : Polynomial ℕ :=
  blockPoly 0 128 p * blockPoly 128 128 p

noncomputable def middleBlockPoly (p : ℕ) : Polynomial ℕ :=
  (blockPoly 256 128 p * blockPoly 384 128 p) *
    (blockPoly 512 128 p * blockPoly 640 128 p)

noncomputable def tailBlockPoly (p : ℕ) : Polynomial ℕ :=
  (blockPoly 768 128 p * blockPoly 896 128 p) * blockPoly 1024 129 p

noncomputable def restBlockPoly (p : ℕ) : Polynomial ℕ :=
  middleBlockPoly p * tailBlockPoly p

noncomputable def balancedPoly (p : ℕ) : Polynomial ℕ :=
  leftBlockPoly p * restBlockPoly p

/-- The members of an explicit prime chunk which are below the cutoff. -/
def chunkBelow (ps : List ℕ) (p : ℕ) : List ℕ :=
  ps.filter (fun q => q < p)

/-- Each explicit chunk is itself split once, keeping the reduction depth of
the kernel evaluator independent of the longest prime chunk. -/
def splitChunkRow (d p : ℕ) (ps : List ℕ) : List ℕ :=
  fastBucketRow (chunkBelow ps p)

theorem splitChunkRow_agree (d p : ℕ) (ps : List ℕ) :
    PolyAgree d (splitChunkRow d p ps) (primePoly (chunkBelow ps p)) := by
  exact fastBucketRow_agree d (chunkBelow ps p)

/-- A balanced coefficient row for four consecutive explicit chunks. -/
def fourChunkRow (d p : ℕ) (a b c e : List ℕ) : List ℕ :=
  convolveTo d
    (convolveTo d (splitChunkRow d p a) (splitChunkRow d p b))
    (convolveTo d (splitChunkRow d p c) (splitChunkRow d p e))

theorem fourChunkRow_agree (d p : ℕ) (a b c e : List ℕ) :
    PolyAgree d (fourChunkRow d p a b c e)
      (primePoly (((chunkBelow a p ++ chunkBelow b p) ++
        chunkBelow c p) ++ chunkBelow e p)) := by
  intro r hr
  simp only [fourChunkRow]
  rw [(((splitChunkRow_agree d p a).mul (splitChunkRow_agree d p b)).mul
    ((splitChunkRow_agree d p c).mul (splitChunkRow_agree d p e))) r hr]
  simp only [primePoly_append]
  ring

/-- The final source interval has five (the last one singleton) chunks. -/
def fiveChunkRow (d p : ℕ) (a b c e f : List ℕ) : List ℕ :=
  convolveTo d (fourChunkRow d p a b c e)
    (splitChunkRow d p f)

theorem fiveChunkRow_agree (d p : ℕ) (a b c e f : List ℕ) :
    PolyAgree d (fiveChunkRow d p a b c e f)
      (primePoly ((((chunkBelow a p ++ chunkBelow b p) ++
        chunkBelow c p) ++ chunkBelow e p) ++ chunkBelow f p)) := by
  intro r hr
  simp only [fiveChunkRow]
  rw [((fourChunkRow_agree d p a b c e).mul
    (splitChunkRow_agree d p f)) r hr]
  rw [← primePoly_append]

def leftChunkRow (d p : ℕ) : List ℕ :=
  convolveTo d
    (fourChunkRow d p primeChunk00 primeChunk01 primeChunk02 primeChunk03)
    (fourChunkRow d p primeChunk04 primeChunk05 primeChunk06 primeChunk07)

def middleChunkRow (d p : ℕ) : List ℕ :=
  convolveTo d
    (convolveTo d
      (fourChunkRow d p primeChunk08 primeChunk09 primeChunk10 primeChunk11)
      (fourChunkRow d p primeChunk12 primeChunk13 primeChunk14 primeChunk15))
    (convolveTo d
      (fourChunkRow d p primeChunk16 primeChunk17 primeChunk18 primeChunk19)
      (fourChunkRow d p primeChunk20 primeChunk21 primeChunk22 primeChunk23))

def tailChunkRow (d p : ℕ) : List ℕ :=
  convolveTo d
    (convolveTo d
      (fourChunkRow d p primeChunk24 primeChunk25 primeChunk26 primeChunk27)
      (fourChunkRow d p primeChunk28 primeChunk29 primeChunk30 primeChunk31))
    (fiveChunkRow d p primeChunk32 primeChunk33 primeChunk34 primeChunk35
      primeChunk36)

def restChunkRow (d p : ℕ) : List ℕ :=
  convolveTo d (middleChunkRow d p) (tailChunkRow d p)

def balancedRow (d p : ℕ) : List ℕ :=
  convolveTo d (leftChunkRow d p) (restChunkRow d p)

theorem chunkBlock0_agree (d p : ℕ) : PolyAgree d
    (fourChunkRow d p primeChunk00 primeChunk01 primeChunk02 primeChunk03)
    (blockPoly 0 128 p) := by
  simpa [blockPoly, primeBlock, primeSource, primes0, chunkBelow,
    List.filter_append] using
    fourChunkRow_agree d p primeChunk00 primeChunk01 primeChunk02 primeChunk03

theorem chunkBlock1_agree (d p : ℕ) : PolyAgree d
    (fourChunkRow d p primeChunk04 primeChunk05 primeChunk06 primeChunk07)
    (blockPoly 128 128 p) := by
  simpa [blockPoly, primeBlock, primeSource, primes1, chunkBelow,
    List.filter_append] using
    fourChunkRow_agree d p primeChunk04 primeChunk05 primeChunk06 primeChunk07

theorem chunkBlock2_agree (d p : ℕ) : PolyAgree d
    (fourChunkRow d p primeChunk08 primeChunk09 primeChunk10 primeChunk11)
    (blockPoly 256 128 p) := by
  simpa [blockPoly, primeBlock, primeSource, primes2, chunkBelow,
    List.filter_append] using
    fourChunkRow_agree d p primeChunk08 primeChunk09 primeChunk10 primeChunk11

theorem chunkBlock3_agree (d p : ℕ) : PolyAgree d
    (fourChunkRow d p primeChunk12 primeChunk13 primeChunk14 primeChunk15)
    (blockPoly 384 128 p) := by
  simpa [blockPoly, primeBlock, primeSource, primes3, chunkBelow,
    List.filter_append] using
    fourChunkRow_agree d p primeChunk12 primeChunk13 primeChunk14 primeChunk15

theorem chunkBlock4_agree (d p : ℕ) : PolyAgree d
    (fourChunkRow d p primeChunk16 primeChunk17 primeChunk18 primeChunk19)
    (blockPoly 512 128 p) := by
  simpa [blockPoly, primeBlock, primeSource, primes4, chunkBelow,
    List.filter_append] using
    fourChunkRow_agree d p primeChunk16 primeChunk17 primeChunk18 primeChunk19

theorem chunkBlock5_agree (d p : ℕ) : PolyAgree d
    (fourChunkRow d p primeChunk20 primeChunk21 primeChunk22 primeChunk23)
    (blockPoly 640 128 p) := by
  simpa [blockPoly, primeBlock, primeSource, primes5, chunkBelow,
    List.filter_append] using
    fourChunkRow_agree d p primeChunk20 primeChunk21 primeChunk22 primeChunk23

theorem chunkBlock6_agree (d p : ℕ) : PolyAgree d
    (fourChunkRow d p primeChunk24 primeChunk25 primeChunk26 primeChunk27)
    (blockPoly 768 128 p) := by
  simpa [blockPoly, primeBlock, primeSource, primes6, chunkBelow,
    List.filter_append] using
    fourChunkRow_agree d p primeChunk24 primeChunk25 primeChunk26 primeChunk27

theorem chunkBlock7_agree (d p : ℕ) : PolyAgree d
    (fourChunkRow d p primeChunk28 primeChunk29 primeChunk30 primeChunk31)
    (blockPoly 896 128 p) := by
  simpa [blockPoly, primeBlock, primeSource, primes7, chunkBelow,
    List.filter_append] using
    fourChunkRow_agree d p primeChunk28 primeChunk29 primeChunk30 primeChunk31

theorem chunkBlock8_agree (d p : ℕ) : PolyAgree d
    (fiveChunkRow d p primeChunk32 primeChunk33 primeChunk34 primeChunk35
      primeChunk36)
    (blockPoly 1024 129 p) := by
  simpa [blockPoly, primeBlock, primeSource, primes8, chunkBelow,
    List.filter_append] using
    fiveChunkRow_agree d p primeChunk32 primeChunk33 primeChunk34 primeChunk35
      primeChunk36

theorem chunkPair01_agree (d p : ℕ) : PolyAgree d
    (convolveTo d
      (fourChunkRow d p primeChunk00 primeChunk01 primeChunk02 primeChunk03)
      (fourChunkRow d p primeChunk04 primeChunk05 primeChunk06 primeChunk07))
    (blockPoly 0 128 p * blockPoly 128 128 p) :=
  (chunkBlock0_agree d p).mul (chunkBlock1_agree d p)

theorem chunkPair23_agree (d p : ℕ) : PolyAgree d
    (convolveTo d
      (fourChunkRow d p primeChunk08 primeChunk09 primeChunk10 primeChunk11)
      (fourChunkRow d p primeChunk12 primeChunk13 primeChunk14 primeChunk15))
    (blockPoly 256 128 p * blockPoly 384 128 p) :=
  (chunkBlock2_agree d p).mul (chunkBlock3_agree d p)

theorem chunkPair45_agree (d p : ℕ) : PolyAgree d
    (convolveTo d
      (fourChunkRow d p primeChunk16 primeChunk17 primeChunk18 primeChunk19)
      (fourChunkRow d p primeChunk20 primeChunk21 primeChunk22 primeChunk23))
    (blockPoly 512 128 p * blockPoly 640 128 p) :=
  (chunkBlock4_agree d p).mul (chunkBlock5_agree d p)

theorem chunkPair67_agree (d p : ℕ) : PolyAgree d
    (convolveTo d
      (fourChunkRow d p primeChunk24 primeChunk25 primeChunk26 primeChunk27)
      (fourChunkRow d p primeChunk28 primeChunk29 primeChunk30 primeChunk31))
    (blockPoly 768 128 p * blockPoly 896 128 p) :=
  (chunkBlock6_agree d p).mul (chunkBlock7_agree d p)

theorem chunkMiddle_agree (d p : ℕ) : PolyAgree d
    (convolveTo d
      (convolveTo d
        (fourChunkRow d p primeChunk08 primeChunk09 primeChunk10 primeChunk11)
        (fourChunkRow d p primeChunk12 primeChunk13 primeChunk14 primeChunk15))
      (convolveTo d
        (fourChunkRow d p primeChunk16 primeChunk17 primeChunk18 primeChunk19)
        (fourChunkRow d p primeChunk20 primeChunk21 primeChunk22 primeChunk23)))
    ((blockPoly 256 128 p * blockPoly 384 128 p) *
      (blockPoly 512 128 p * blockPoly 640 128 p)) :=
  (chunkPair23_agree d p).mul (chunkPair45_agree d p)

theorem chunkTail_agree (d p : ℕ) : PolyAgree d
    (convolveTo d
      (convolveTo d
        (fourChunkRow d p primeChunk24 primeChunk25 primeChunk26 primeChunk27)
        (fourChunkRow d p primeChunk28 primeChunk29 primeChunk30 primeChunk31))
      (fiveChunkRow d p primeChunk32 primeChunk33 primeChunk34 primeChunk35
        primeChunk36))
    ((blockPoly 768 128 p * blockPoly 896 128 p) * blockPoly 1024 129 p) :=
  (chunkPair67_agree d p).mul (chunkBlock8_agree d p)

theorem chunkRest_agree (d p : ℕ) : PolyAgree d
    (convolveTo d
      (convolveTo d
        (convolveTo d
          (fourChunkRow d p primeChunk08 primeChunk09 primeChunk10 primeChunk11)
          (fourChunkRow d p primeChunk12 primeChunk13 primeChunk14 primeChunk15))
        (convolveTo d
          (fourChunkRow d p primeChunk16 primeChunk17 primeChunk18 primeChunk19)
          (fourChunkRow d p primeChunk20 primeChunk21 primeChunk22 primeChunk23)))
      (convolveTo d
        (convolveTo d
          (fourChunkRow d p primeChunk24 primeChunk25 primeChunk26 primeChunk27)
          (fourChunkRow d p primeChunk28 primeChunk29 primeChunk30 primeChunk31))
        (fiveChunkRow d p primeChunk32 primeChunk33 primeChunk34 primeChunk35
          primeChunk36)))
    (((blockPoly 256 128 p * blockPoly 384 128 p) *
        (blockPoly 512 128 p * blockPoly 640 128 p)) *
      ((blockPoly 768 128 p * blockPoly 896 128 p) * blockPoly 1024 129 p)) :=
  (chunkMiddle_agree d p).mul (chunkTail_agree d p)

theorem leftChunkRow_agree (d p : ℕ) :
    PolyAgree d (leftChunkRow d p) (leftBlockPoly p) := by
  simpa only [leftChunkRow, leftBlockPoly] using chunkPair01_agree d p

theorem middleChunkRow_agree (d p : ℕ) :
    PolyAgree d (middleChunkRow d p) (middleBlockPoly p) := by
  simpa only [middleChunkRow, middleBlockPoly] using chunkMiddle_agree d p

theorem tailChunkRow_agree (d p : ℕ) :
    PolyAgree d (tailChunkRow d p) (tailBlockPoly p) := by
  simpa only [tailChunkRow, tailBlockPoly] using chunkTail_agree d p

theorem restChunkRow_agree (d p : ℕ) :
    PolyAgree d (restChunkRow d p) (restBlockPoly p) := by
  exact (middleChunkRow_agree d p).mul (tailChunkRow_agree d p)

theorem balancedRow_agree (d p : ℕ) :
    PolyAgree d (balancedRow d p) (balancedPoly p) := by
  exact (leftChunkRow_agree d p).mul (restChunkRow_agree d p)

theorem balancedPoly_eq_primePoly_selected (p : ℕ) :
    balancedPoly p = primePoly (selectedPrimes p) := by
  simp only [balancedPoly, leftBlockPoly, restBlockPoly, middleBlockPoly,
    tailBlockPoly, selectedPrimes, blockPoly, primePoly_append]
  ring

def rawBlocks : List ℕ :=
  ((((((((List.range' 0 128 ++ List.range' 128 128) ++
      List.range' 256 128) ++ List.range' 384 128) ++
      List.range' 512 128) ++ List.range' 640 128) ++
      List.range' 768 128) ++ List.range' 896 128) ++
      List.range' 1024 129)

def allPrimes : List ℕ :=
  ((((((((primes0 ++ primes1) ++ primes2) ++ primes3) ++ primes4) ++
      primes5) ++ primes6) ++ primes7) ++ primes8)

theorem primeChunk00_exact :
    primeChunk00 = (List.range' 0 32).filter Nat.Prime := by
  norm_num [primeChunk00, List.range', List.filter]
theorem primeChunk01_exact :
    primeChunk01 = (List.range' 32 32).filter Nat.Prime := by
  norm_num [primeChunk01, List.range', List.filter]
theorem primeChunk02_exact :
    primeChunk02 = (List.range' 64 32).filter Nat.Prime := by
  norm_num [primeChunk02, List.range', List.filter]
theorem primeChunk03_exact :
    primeChunk03 = (List.range' 96 32).filter Nat.Prime := by
  norm_num [primeChunk03, List.range', List.filter]
theorem primeChunk04_exact :
    primeChunk04 = (List.range' 128 32).filter Nat.Prime := by
  norm_num [primeChunk04, List.range', List.filter]
theorem primeChunk05_exact :
    primeChunk05 = (List.range' 160 32).filter Nat.Prime := by
  norm_num [primeChunk05, List.range', List.filter]
theorem primeChunk06_exact :
    primeChunk06 = (List.range' 192 32).filter Nat.Prime := by
  norm_num [primeChunk06, List.range', List.filter]
theorem primeChunk07_exact :
    primeChunk07 = (List.range' 224 32).filter Nat.Prime := by
  norm_num [primeChunk07, List.range', List.filter]
theorem primeChunk08_exact :
    primeChunk08 = (List.range' 256 32).filter Nat.Prime := by
  norm_num [primeChunk08, List.range', List.filter]
theorem primeChunk09_exact :
    primeChunk09 = (List.range' 288 32).filter Nat.Prime := by
  norm_num [primeChunk09, List.range', List.filter]
theorem primeChunk10_exact :
    primeChunk10 = (List.range' 320 32).filter Nat.Prime := by
  norm_num [primeChunk10, List.range', List.filter]
theorem primeChunk11_exact :
    primeChunk11 = (List.range' 352 32).filter Nat.Prime := by
  norm_num [primeChunk11, List.range', List.filter]
theorem primeChunk12_exact :
    primeChunk12 = (List.range' 384 32).filter Nat.Prime := by
  norm_num [primeChunk12, List.range', List.filter]
theorem primeChunk13_exact :
    primeChunk13 = (List.range' 416 32).filter Nat.Prime := by
  norm_num [primeChunk13, List.range', List.filter]
theorem primeChunk14_exact :
    primeChunk14 = (List.range' 448 32).filter Nat.Prime := by
  norm_num [primeChunk14, List.range', List.filter]
theorem primeChunk15_exact :
    primeChunk15 = (List.range' 480 32).filter Nat.Prime := by
  norm_num [primeChunk15, List.range', List.filter]
theorem primeChunk16_exact :
    primeChunk16 = (List.range' 512 32).filter Nat.Prime := by
  norm_num [primeChunk16, List.range', List.filter]
theorem primeChunk17_exact :
    primeChunk17 = (List.range' 544 32).filter Nat.Prime := by
  norm_num [primeChunk17, List.range', List.filter]
theorem primeChunk18_exact :
    primeChunk18 = (List.range' 576 32).filter Nat.Prime := by
  norm_num [primeChunk18, List.range', List.filter]
theorem primeChunk19_exact :
    primeChunk19 = (List.range' 608 32).filter Nat.Prime := by
  norm_num [primeChunk19, List.range', List.filter]
theorem primeChunk20_exact :
    primeChunk20 = (List.range' 640 32).filter Nat.Prime := by
  norm_num [primeChunk20, List.range', List.filter]
theorem primeChunk21_exact :
    primeChunk21 = (List.range' 672 32).filter Nat.Prime := by
  norm_num [primeChunk21, List.range', List.filter]
theorem primeChunk22_exact :
    primeChunk22 = (List.range' 704 32).filter Nat.Prime := by
  norm_num [primeChunk22, List.range', List.filter]
theorem primeChunk23_exact :
    primeChunk23 = (List.range' 736 32).filter Nat.Prime := by
  norm_num [primeChunk23, List.range', List.filter]
theorem primeChunk24_exact :
    primeChunk24 = (List.range' 768 32).filter Nat.Prime := by
  norm_num [primeChunk24, List.range', List.filter]
theorem primeChunk25_exact :
    primeChunk25 = (List.range' 800 32).filter Nat.Prime := by
  norm_num [primeChunk25, List.range', List.filter]
theorem primeChunk26_exact :
    primeChunk26 = (List.range' 832 32).filter Nat.Prime := by
  norm_num [primeChunk26, List.range', List.filter]
theorem primeChunk27_exact :
    primeChunk27 = (List.range' 864 32).filter Nat.Prime := by
  norm_num [primeChunk27, List.range', List.filter]
theorem primeChunk28_exact :
    primeChunk28 = (List.range' 896 32).filter Nat.Prime := by
  norm_num [primeChunk28, List.range', List.filter]
theorem primeChunk29_exact :
    primeChunk29 = (List.range' 928 32).filter Nat.Prime := by
  norm_num [primeChunk29, List.range', List.filter]
theorem primeChunk30_exact :
    primeChunk30 = (List.range' 960 32).filter Nat.Prime := by
  norm_num [primeChunk30, List.range', List.filter]
theorem primeChunk31_exact :
    primeChunk31 = (List.range' 992 32).filter Nat.Prime := by
  norm_num [primeChunk31, List.range', List.filter]
theorem primeChunk32_exact :
    primeChunk32 = (List.range' 1024 32).filter Nat.Prime := by
  norm_num [primeChunk32, List.range', List.filter]
theorem primeChunk33_exact :
    primeChunk33 = (List.range' 1056 32).filter Nat.Prime := by
  norm_num [primeChunk33, List.range', List.filter]
theorem primeChunk34_exact :
    primeChunk34 = (List.range' 1088 32).filter Nat.Prime := by
  norm_num [primeChunk34, List.range', List.filter]
theorem primeChunk35_exact :
    primeChunk35 = (List.range' 1120 32).filter Nat.Prime := by
  norm_num [primeChunk35, List.range', List.filter]
theorem primeChunk36_exact :
    primeChunk36 = (List.range' 1152 1).filter Nat.Prime := by
  norm_num [primeChunk36, List.range', List.filter]

theorem primes0_exact : primes0 = (List.range' 0 128).filter Nat.Prime := by
  rw [primes0, primeChunk00_exact, primeChunk01_exact, primeChunk02_exact,
    primeChunk03_exact, ← List.filter_append, ← List.filter_append,
    ← List.filter_append, List.range'_append_1, List.range'_append_1,
    List.range'_append_1]
theorem primes1_exact : primes1 = (List.range' 128 128).filter Nat.Prime := by
  rw [primes1, primeChunk04_exact, primeChunk05_exact, primeChunk06_exact,
    primeChunk07_exact, ← List.filter_append, ← List.filter_append,
    ← List.filter_append, List.range'_append_1, List.range'_append_1,
    List.range'_append_1]
theorem primes2_exact : primes2 = (List.range' 256 128).filter Nat.Prime := by
  rw [primes2, primeChunk08_exact, primeChunk09_exact, primeChunk10_exact,
    primeChunk11_exact, ← List.filter_append, ← List.filter_append,
    ← List.filter_append, List.range'_append_1, List.range'_append_1,
    List.range'_append_1]
theorem primes3_exact : primes3 = (List.range' 384 128).filter Nat.Prime := by
  rw [primes3, primeChunk12_exact, primeChunk13_exact, primeChunk14_exact,
    primeChunk15_exact, ← List.filter_append, ← List.filter_append,
    ← List.filter_append, List.range'_append_1, List.range'_append_1,
    List.range'_append_1]
theorem primes4_exact : primes4 = (List.range' 512 128).filter Nat.Prime := by
  rw [primes4, primeChunk16_exact, primeChunk17_exact, primeChunk18_exact,
    primeChunk19_exact, ← List.filter_append, ← List.filter_append,
    ← List.filter_append, List.range'_append_1, List.range'_append_1,
    List.range'_append_1]
theorem primes5_exact : primes5 = (List.range' 640 128).filter Nat.Prime := by
  rw [primes5, primeChunk20_exact, primeChunk21_exact, primeChunk22_exact,
    primeChunk23_exact, ← List.filter_append, ← List.filter_append,
    ← List.filter_append, List.range'_append_1, List.range'_append_1,
    List.range'_append_1]
theorem primes6_exact : primes6 = (List.range' 768 128).filter Nat.Prime := by
  rw [primes6, primeChunk24_exact, primeChunk25_exact, primeChunk26_exact,
    primeChunk27_exact, ← List.filter_append, ← List.filter_append,
    ← List.filter_append, List.range'_append_1, List.range'_append_1,
    List.range'_append_1]
theorem primes7_exact : primes7 = (List.range' 896 128).filter Nat.Prime := by
  rw [primes7, primeChunk28_exact, primeChunk29_exact, primeChunk30_exact,
    primeChunk31_exact, ← List.filter_append, ← List.filter_append,
    ← List.filter_append, List.range'_append_1, List.range'_append_1,
    List.range'_append_1]
theorem primes8_exact : primes8 = (List.range' 1024 129).filter Nat.Prime := by
  rw [primes8, primeChunk32_exact, primeChunk33_exact, primeChunk34_exact,
    primeChunk35_exact, primeChunk36_exact, ← List.filter_append,
    ← List.filter_append, ← List.filter_append, ← List.filter_append,
    List.range'_append_1, List.range'_append_1, List.range'_append_1,
    List.range'_append_1]

theorem rawBlocks_eq_range : rawBlocks = List.range 1153 := by
  rw [List.range_eq_range']
  simp only [rawBlocks]
  rw [List.range'_append_1, List.range'_append_1, List.range'_append_1,
    List.range'_append_1, List.range'_append_1, List.range'_append_1,
    List.range'_append_1, List.range'_append_1]

theorem allPrimes_eq_filter_raw :
    allPrimes = rawBlocks.filter Nat.Prime := by
  simp only [allPrimes, rawBlocks, List.filter_append]
  rw [← primes0_exact, ← primes1_exact, ← primes2_exact,
    ← primes3_exact, ← primes4_exact, ← primes5_exact,
    ← primes6_exact, ← primes7_exact, ← primes8_exact]

theorem selectedPrimes_eq_filter_all (p : ℕ) :
    selectedPrimes p = allPrimes.filter (fun q => q < p) := by
  simp [selectedPrimes, allPrimes, primeBlock, primeSource,
    List.filter_append]

theorem filter_range_prime_lt (p N : ℕ) (hpN : p ≤ N) :
    (List.range N).filter (fun q => q.Prime ∧ q < p) =
      (List.range p).filter Nat.Prime := by
  have hrange : List.range N =
      List.range p ++ List.range' p (N - p) := by
    rw [List.range_eq_range', show N = p + (N - p) by omega,
      ← List.range'_append_1]
    simp [List.range_eq_range']
  rw [hrange, List.filter_append]
  have hfirst :
      (List.range p).filter (fun q => q.Prime ∧ q < p) =
        (List.range p).filter Nat.Prime := by
    apply List.filter_congr
    intro q hq
    have hqp : q < p := List.mem_range.mp hq
    simp [hqp]
  have hsecond :
      (List.range' p (N - p)).filter (fun q => q.Prime ∧ q < p) = [] := by
    rw [List.filter_eq_nil_iff]
    intro q hq
    have hpq : p ≤ q := by
      simp only [List.mem_range'] at hq
      obtain ⟨i, hi, rfl⟩ := hq
      omega
    simp [not_lt_of_ge hpq]
  rw [hfirst, hsecond, List.append_nil]

theorem selectedPrimes_eq_range_filter (p : ℕ) (hp : p ≤ 1153) :
    selectedPrimes p = (List.range p).filter Nat.Prime := by
  calc
    selectedPrimes p = allPrimes.filter (fun q => q < p) :=
      selectedPrimes_eq_filter_all p
    _ = (rawBlocks.filter Nat.Prime).filter (fun q => q < p) := by
      rw [allPrimes_eq_filter_raw]
    _ = ((List.range 1153).filter Nat.Prime).filter (fun q => q < p) := by
      rw [rawBlocks_eq_range]
    _ = (List.range 1153).filter (fun q => q.Prime ∧ q < p) := by
      rw [List.filter_filter]
      apply List.filter_congr
      intro q hq
      simp [and_comm]
    _ = (List.range p).filter Nat.Prime := filter_range_prime_lt p 1153 hp

theorem listPoly_coeffStep (a : ℕ) (row : List ℕ) :
    listPoly (coeffStep a row) =
      (Polynomial.C a + Polynomial.X) * listPoly row := by
  ext r
  rw [listPoly_coeff, coeffStep_getD]
  rcases r with _ | r
  · simp [listPoly_coeff]
  · simp only [add_mul, Polynomial.coeff_add, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_mul, listPoly_coeff]
    simp

theorem listPoly_coeffRow (p : ℕ) :
    listPoly (coeffRow p) =
      primePoly ((List.range p).filter Nat.Prime) := by
  induction p with
  | zero => simp [coeffRow, listPoly, primePoly]
  | succ p ih =>
      rw [coeffRow_succ, List.range_succ, List.filter_append]
      by_cases hp : p.Prime
      · rw [if_pos hp, listPoly_coeffStep, ih, primePoly_append]
        have hsingleton : [p].filter Nat.Prime = [p] := by simp [hp]
        rw [hsingleton]
        change factorPoly p * primePoly ((List.range p).filter Nat.Prime) =
          primePoly ((List.range p).filter Nat.Prime) * primePoly [p]
        simpa [primePoly] using
          (mul_comm (factorPoly p)
            (primePoly ((List.range p).filter Nat.Prime)))
      · rw [if_neg hp]
        have hsingleton : [p].filter Nat.Prime = [] := by simp [hp]
        rw [hsingleton, List.append_nil]
        exact ih

theorem coeff_eq_primePoly_coeff (r p : ℕ) :
    coeff r p = (primePoly ((List.range p).filter Nat.Prime)).coeff r := by
  rw [coeff, ← listPoly_coeff, listPoly_coeffRow]

/-- The evaluator used by the finite certificates.  It computes all degrees
through the requested degree by a balanced tree, avoiding a deep reduction term. -/
def coeffEB (r p : ℕ) : ℕ := (balancedRow r p).getD r 0

theorem coeffEB_eq_coeff (r p : ℕ) (hr : r ≤ 19) (hp : p ≤ 1153) :
    coeffEB r p = coeff r p := by
  rw [coeffEB, (balancedRow_agree r p) r le_rfl,
    balancedPoly_eq_primePoly_selected,
    selectedPrimes_eq_range_filter p hp,
    coeff_eq_primePoly_coeff]

theorem cert4 :
    coeff 2 13 < 5 * coeff 3 13 ∧
      3 * coeff 3 17 < coeff 2 17 := by
  rw [← coeffEB_eq_coeff 2 13 (by omega) (by omega),
    ← coeffEB_eq_coeff 3 13 (by omega) (by omega),
    ← coeffEB_eq_coeff 3 17 (by omega) (by omega),
    ← coeffEB_eq_coeff 2 17 (by omega) (by omega)]
  decide

theorem cert5 :
    coeff 3 23 < 7 * coeff 4 23 ∧
      3 * coeff 4 29 < coeff 3 29 := by
  rw [← coeffEB_eq_coeff 3 23 (by omega) (by omega),
    ← coeffEB_eq_coeff 4 23 (by omega) (by omega),
    ← coeffEB_eq_coeff 4 29 (by omega) (by omega),
    ← coeffEB_eq_coeff 3 29 (by omega) (by omega)]
  decide

theorem cert6 :
    coeff 4 31 < 7 * coeff 5 31 ∧
      5 * coeff 5 37 < coeff 4 37 := by
  rw [← coeffEB_eq_coeff 4 31 (by omega) (by omega),
    ← coeffEB_eq_coeff 5 31 (by omega) (by omega),
    ← coeffEB_eq_coeff 5 37 (by omega) (by omega),
    ← coeffEB_eq_coeff 4 37 (by omega) (by omega)]
  decide

theorem cert7 :
    coeff 5 73 < 7 * coeff 6 73 ∧
      5 * coeff 6 79 < coeff 5 79 := by
  rw [← coeffEB_eq_coeff 5 73 (by omega) (by omega),
    ← coeffEB_eq_coeff 6 73 (by omega) (by omega),
    ← coeffEB_eq_coeff 6 79 (by omega) (by omega),
    ← coeffEB_eq_coeff 5 79 (by omega) (by omega)]
  decide

theorem cert8 :
    coeff 6 89 < 9 * coeff 7 89 ∧
      5 * coeff 7 97 < coeff 6 97 := by
  rw [← coeffEB_eq_coeff 6 89 (by omega) (by omega),
    ← coeffEB_eq_coeff 7 89 (by omega) (by omega),
    ← coeffEB_eq_coeff 7 97 (by omega) (by omega),
    ← coeffEB_eq_coeff 6 97 (by omega) (by omega)]
  decide

theorem cert9 :
    coeff 7 113 < 15 * coeff 8 113 ∧
      5 * coeff 8 127 < coeff 7 127 := by
  rw [← coeffEB_eq_coeff 7 113 (by omega) (by omega),
    ← coeffEB_eq_coeff 8 113 (by omega) (by omega),
    ← coeffEB_eq_coeff 8 127 (by omega) (by omega),
    ← coeffEB_eq_coeff 7 127 (by omega) (by omega)]
  decide

theorem cert10 :
    coeff 8 113 < 15 * coeff 9 113 ∧
      5 * coeff 9 127 < coeff 8 127 := by
  rw [← coeffEB_eq_coeff 8 113 (by omega) (by omega),
    ← coeffEB_eq_coeff 9 113 (by omega) (by omega),
    ← coeffEB_eq_coeff 9 127 (by omega) (by omega),
    ← coeffEB_eq_coeff 8 127 (by omega) (by omega)]
  decide

theorem cert11 :
    coeff 9 113 < 15 * coeff 10 113 ∧
      5 * coeff 10 127 < coeff 9 127 := by
  rw [← coeffEB_eq_coeff 9 113 (by omega) (by omega),
    ← coeffEB_eq_coeff 10 113 (by omega) (by omega),
    ← coeffEB_eq_coeff 10 127 (by omega) (by omega),
    ← coeffEB_eq_coeff 9 127 (by omega) (by omega)]
  decide

theorem cert12 :
    coeff 10 293 < 15 * coeff 11 293 ∧
      5 * coeff 11 307 < coeff 10 307 := by
  rw [← coeffEB_eq_coeff 10 293 (by omega) (by omega),
    ← coeffEB_eq_coeff 11 293 (by omega) (by omega),
    ← coeffEB_eq_coeff 11 307 (by omega) (by omega),
    ← coeffEB_eq_coeff 10 307 (by omega) (by omega)]
  decide

theorem cert13 :
    coeff 11 293 < 15 * coeff 12 293 ∧
      5 * coeff 12 307 < coeff 11 307 := by
  rw [← coeffEB_eq_coeff 11 293 (by omega) (by omega),
    ← coeffEB_eq_coeff 12 293 (by omega) (by omega),
    ← coeffEB_eq_coeff 12 307 (by omega) (by omega),
    ← coeffEB_eq_coeff 11 307 (by omega) (by omega)]
  decide

theorem cert14 :
    coeff 12 523 < 19 * coeff 13 523 ∧
      7 * coeff 13 541 < coeff 12 541 := by
  rw [← coeffEB_eq_coeff 12 523 (by omega) (by omega),
    ← coeffEB_eq_coeff 13 523 (by omega) (by omega),
    ← coeffEB_eq_coeff 13 541 (by omega) (by omega),
    ← coeffEB_eq_coeff 12 541 (by omega) (by omega)]
  decide

theorem cert15 :
    coeff 13 523 < 19 * coeff 14 523 ∧
      7 * coeff 14 541 < coeff 13 541 := by
  rw [← coeffEB_eq_coeff 13 523 (by omega) (by omega),
    ← coeffEB_eq_coeff 14 523 (by omega) (by omega),
    ← coeffEB_eq_coeff 14 541 (by omega) (by omega),
    ← coeffEB_eq_coeff 13 541 (by omega) (by omega)]
  decide

theorem cert16 :
    coeff 14 523 < 19 * coeff 15 523 ∧
      7 * coeff 15 541 < coeff 14 541 := by
  rw [← coeffEB_eq_coeff 14 523 (by omega) (by omega),
    ← coeffEB_eq_coeff 15 523 (by omega) (by omega),
    ← coeffEB_eq_coeff 15 541 (by omega) (by omega),
    ← coeffEB_eq_coeff 14 541 (by omega) (by omega)]
  decide

theorem cert17 :
    coeff 15 887 < 21 * coeff 16 887 ∧
      5 * coeff 16 907 < coeff 15 907 := by
  rw [← coeffEB_eq_coeff 15 887 (by omega) (by omega),
    ← coeffEB_eq_coeff 16 887 (by omega) (by omega),
    ← coeffEB_eq_coeff 16 907 (by omega) (by omega),
    ← coeffEB_eq_coeff 15 907 (by omega) (by omega)]
  decide

theorem cert18 :
    coeff 16 887 < 21 * coeff 17 887 ∧
      5 * coeff 17 907 < coeff 16 907 := by
  rw [← coeffEB_eq_coeff 16 887 (by omega) (by omega),
    ← coeffEB_eq_coeff 17 887 (by omega) (by omega),
    ← coeffEB_eq_coeff 17 907 (by omega) (by omega),
    ← coeffEB_eq_coeff 16 907 (by omega) (by omega)]
  decide

theorem cert19 :
    coeff 17 887 < 21 * coeff 18 887 ∧
      5 * coeff 18 907 < coeff 17 907 := by
  rw [← coeffEB_eq_coeff 17 887 (by omega) (by omega),
    ← coeffEB_eq_coeff 18 887 (by omega) (by omega),
    ← coeffEB_eq_coeff 18 907 (by omega) (by omega),
    ← coeffEB_eq_coeff 17 907 (by omega) (by omega)]
  decide

theorem cert20 :
    coeff 18 1129 < 23 * coeff 19 1129 ∧
      3 * coeff 19 1151 < coeff 18 1151 := by
  rw [← coeffEB_eq_coeff 18 1129 (by omega) (by omega),
    ← coeffEB_eq_coeff 19 1129 (by omega) (by omega),
    ← coeffEB_eq_coeff 19 1151 (by omega) (by omega),
    ← coeffEB_eq_coeff 18 1151 (by omega) (by omega)]
  decide

/-! ## Exact strict-valley certificates -/

/-- Cambie's finite witnesses, grouped by the positions sharing a valley. -/
def valleyTriple (k : ℕ) : ℕ × ℕ × ℕ :=
  if k = 4 then (13, 17, 19)
  else if k = 5 then (23, 29, 31)
  else if k = 6 then (31, 37, 41)
  else if k = 7 then (73, 79, 83)
  else if k = 8 then (89, 97, 101)
  else if k ≤ 11 then (113, 127, 131)
  else if k ≤ 13 then (293, 307, 311)
  else if k ≤ 16 then (523, 541, 547)
  else if k ≤ 19 then (887, 907, 911)
  else (1129, 1151, 1153)

theorem consecutive_13_17 : ConsecutivePrimes 13 17 := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_⟩
  intro r hr h13 h17
  interval_cases r <;> norm_num at hr

theorem consecutive_17_19 : ConsecutivePrimes 17 19 := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_⟩
  intro r hr h17 h19
  interval_cases r <;> norm_num at hr

theorem consecutive_23_29 : ConsecutivePrimes 23 29 := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_⟩
  intro r hr h23 h29
  interval_cases r <;> norm_num at hr

theorem consecutive_29_31 : ConsecutivePrimes 29 31 := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_⟩
  intro r hr h29 h31
  interval_cases r <;> norm_num at hr

theorem consecutive_31_37 : ConsecutivePrimes 31 37 := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_⟩
  intro r hr h31 h37
  interval_cases r <;> norm_num at hr

theorem consecutive_37_41 : ConsecutivePrimes 37 41 := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_⟩
  intro r hr h37 h41
  interval_cases r <;> norm_num at hr

theorem consecutive_73_79 : ConsecutivePrimes 73 79 := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_⟩
  intro r hr h73 h79
  interval_cases r <;> norm_num at hr

theorem consecutive_79_83 : ConsecutivePrimes 79 83 := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_⟩
  intro r hr h79 h83
  interval_cases r <;> norm_num at hr

theorem consecutive_89_97 : ConsecutivePrimes 89 97 := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_⟩
  intro r hr h89 h97
  interval_cases r <;> norm_num at hr

theorem consecutive_97_101 : ConsecutivePrimes 97 101 := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_⟩
  intro r hr h97 h101
  interval_cases r <;> norm_num at hr

theorem consecutive_113_127 : ConsecutivePrimes 113 127 := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_⟩
  intro r hr h113 h127
  interval_cases r <;> norm_num at hr

theorem consecutive_127_131 : ConsecutivePrimes 127 131 := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_⟩
  intro r hr h127 h131
  interval_cases r <;> norm_num at hr

theorem consecutive_293_307 : ConsecutivePrimes 293 307 := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_⟩
  intro r hr h293 h307
  interval_cases r <;> norm_num at hr

theorem consecutive_307_311 : ConsecutivePrimes 307 311 := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_⟩
  intro r hr h307 h311
  interval_cases r <;> norm_num at hr

theorem consecutive_523_541 : ConsecutivePrimes 523 541 := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_⟩
  intro r hr h523 h541
  interval_cases r <;> norm_num at hr

theorem consecutive_541_547 : ConsecutivePrimes 541 547 := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_⟩
  intro r hr h541 h547
  interval_cases r <;> norm_num at hr

theorem consecutive_887_907 : ConsecutivePrimes 887 907 := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_⟩
  intro r hr h887 h907
  interval_cases r <;> norm_num at hr

theorem consecutive_907_911 : ConsecutivePrimes 907 911 := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_⟩
  intro r hr h907 h911
  interval_cases r <;> norm_num at hr

theorem consecutive_1129_1151 : ConsecutivePrimes 1129 1151 := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_⟩
  intro r hr h1129 h1151
  interval_cases r <;> norm_num at hr

theorem consecutive_1151_1153 : ConsecutivePrimes 1151 1153 := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_⟩
  intro r hr h1151 h1153
  interval_cases r <;> norm_num at hr

theorem valley_certificate_of_coeff (k a b c : ℕ) (hk : 2 ≤ k)
    (hab : ConsecutivePrimes a b) (hbc : ConsecutivePrimes b c)
    (hdown : coeff (k - 2) a < (b - a + 1) * coeff (k - 1) a)
    (hup : (c - b + 1) * coeff (k - 1) b < coeff (k - 2) b) :
    a.Prime ∧ b.Prime ∧ c.Prime ∧ a < b ∧ b < c ∧
      primeFactorDensity k b < primeFactorDensity k a ∧
      primeFactorDensity k b < primeFactorDensity k c := by
  exact ⟨hab.1, hab.2.1, hbc.2.1, hab.2.2.1, hbc.2.2.1,
    density_next_lt_of_coeff_lt k a b hk hab hdown,
    density_lt_next_of_coeff_lt k b c hk hbc hup⟩

/-- A presentation of `valley_certificate_of_coeff` in which the four small
natural-number indices are supplied in already-normalized form.  This keeps
the final finite case split from asking the elaborator to compare expressions
such as `coeff (k - 2) a` by unfolding the (computational) definition of
`coeff` at large concrete primes. -/
theorem valley_certificate_of_normalized_coeff
    (k a b c r s gapAB gapBC : ℕ) (hk : 2 ≤ k)
    (hab : ConsecutivePrimes a b) (hbc : ConsecutivePrimes b c)
    (hr : k - 2 = r) (hs : k - 1 = s)
    (hgapAB : b - a + 1 = gapAB) (hgapBC : c - b + 1 = gapBC)
    (hdown : coeff r a < gapAB * coeff s a)
    (hup : gapBC * coeff s b < coeff r b) :
    a.Prime ∧ b.Prime ∧ c.Prime ∧ a < b ∧ b < c ∧
      primeFactorDensity k b < primeFactorDensity k a ∧
      primeFactorDensity k b < primeFactorDensity k c := by
  apply valley_certificate_of_coeff k a b c hk hab hbc
  · simpa only [hr, hs, hgapAB] using hdown
  · simpa only [hr, hs, hgapBC] using hup

theorem valley_certificates (k : ℕ) (hk4 : 4 ≤ k) (hk20 : k ≤ 20) :
    let w := valleyTriple k
    w.1.Prime ∧ w.2.1.Prime ∧ w.2.2.Prime ∧
      w.1 < w.2.1 ∧ w.2.1 < w.2.2 ∧
      primeFactorDensity k w.2.1 < primeFactorDensity k w.1 ∧
      primeFactorDensity k w.2.1 < primeFactorDensity k w.2.2 := by
  interval_cases k
  · change Nat.Prime 13 ∧ Nat.Prime 17 ∧ Nat.Prime 19 ∧ 13 < 17 ∧ 17 < 19 ∧
      primeFactorDensity 4 17 < primeFactorDensity 4 13 ∧
      primeFactorDensity 4 17 < primeFactorDensity 4 19
    exact valley_certificate_of_coeff 4 13 17 19 (by omega)
      consecutive_13_17 consecutive_17_19 cert4.1 cert4.2
  · change Nat.Prime 23 ∧ Nat.Prime 29 ∧ Nat.Prime 31 ∧ 23 < 29 ∧ 29 < 31 ∧
      primeFactorDensity 5 29 < primeFactorDensity 5 23 ∧
      primeFactorDensity 5 29 < primeFactorDensity 5 31
    exact valley_certificate_of_coeff 5 23 29 31 (by omega)
      consecutive_23_29 consecutive_29_31 cert5.1 cert5.2
  · change Nat.Prime 31 ∧ Nat.Prime 37 ∧ Nat.Prime 41 ∧ 31 < 37 ∧ 37 < 41 ∧
      primeFactorDensity 6 37 < primeFactorDensity 6 31 ∧
      primeFactorDensity 6 37 < primeFactorDensity 6 41
    exact valley_certificate_of_coeff 6 31 37 41 (by omega)
      consecutive_31_37 consecutive_37_41 cert6.1 cert6.2
  · change Nat.Prime 73 ∧ Nat.Prime 79 ∧ Nat.Prime 83 ∧ 73 < 79 ∧ 79 < 83 ∧
      primeFactorDensity 7 79 < primeFactorDensity 7 73 ∧
      primeFactorDensity 7 79 < primeFactorDensity 7 83
    exact valley_certificate_of_coeff 7 73 79 83 (by omega)
      consecutive_73_79 consecutive_79_83 cert7.1 cert7.2
  · change Nat.Prime 89 ∧ Nat.Prime 97 ∧ Nat.Prime 101 ∧ 89 < 97 ∧ 97 < 101 ∧
      primeFactorDensity 8 97 < primeFactorDensity 8 89 ∧
      primeFactorDensity 8 97 < primeFactorDensity 8 101
    exact valley_certificate_of_coeff 8 89 97 101 (by omega)
      consecutive_89_97 consecutive_97_101 cert8.1 cert8.2
  · change Nat.Prime 113 ∧ Nat.Prime 127 ∧ Nat.Prime 131 ∧ 113 < 127 ∧ 127 < 131 ∧
      primeFactorDensity 9 127 < primeFactorDensity 9 113 ∧
      primeFactorDensity 9 127 < primeFactorDensity 9 131
    exact valley_certificate_of_normalized_coeff 9 113 127 131 7 8 15 5 (by omega)
      consecutive_113_127 consecutive_127_131 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) cert9.1 cert9.2
  · change Nat.Prime 113 ∧ Nat.Prime 127 ∧ Nat.Prime 131 ∧ 113 < 127 ∧ 127 < 131 ∧
      primeFactorDensity 10 127 < primeFactorDensity 10 113 ∧
      primeFactorDensity 10 127 < primeFactorDensity 10 131
    exact valley_certificate_of_normalized_coeff 10 113 127 131 8 9 15 5 (by omega)
      consecutive_113_127 consecutive_127_131 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) cert10.1 cert10.2
  · change Nat.Prime 113 ∧ Nat.Prime 127 ∧ Nat.Prime 131 ∧ 113 < 127 ∧ 127 < 131 ∧
      primeFactorDensity 11 127 < primeFactorDensity 11 113 ∧
      primeFactorDensity 11 127 < primeFactorDensity 11 131
    exact valley_certificate_of_normalized_coeff 11 113 127 131 9 10 15 5 (by omega)
      consecutive_113_127 consecutive_127_131 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) cert11.1 cert11.2
  · change Nat.Prime 293 ∧ Nat.Prime 307 ∧ Nat.Prime 311 ∧ 293 < 307 ∧ 307 < 311 ∧
      primeFactorDensity 12 307 < primeFactorDensity 12 293 ∧
      primeFactorDensity 12 307 < primeFactorDensity 12 311
    exact valley_certificate_of_normalized_coeff 12 293 307 311 10 11 15 5 (by omega)
      consecutive_293_307 consecutive_307_311 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) cert12.1 cert12.2
  · change Nat.Prime 293 ∧ Nat.Prime 307 ∧ Nat.Prime 311 ∧ 293 < 307 ∧ 307 < 311 ∧
      primeFactorDensity 13 307 < primeFactorDensity 13 293 ∧
      primeFactorDensity 13 307 < primeFactorDensity 13 311
    exact valley_certificate_of_normalized_coeff 13 293 307 311 11 12 15 5 (by omega)
      consecutive_293_307 consecutive_307_311 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) cert13.1 cert13.2
  · change Nat.Prime 523 ∧ Nat.Prime 541 ∧ Nat.Prime 547 ∧ 523 < 541 ∧ 541 < 547 ∧
      primeFactorDensity 14 541 < primeFactorDensity 14 523 ∧
      primeFactorDensity 14 541 < primeFactorDensity 14 547
    exact valley_certificate_of_normalized_coeff 14 523 541 547 12 13 19 7 (by omega)
      consecutive_523_541 consecutive_541_547 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) cert14.1 cert14.2
  · change Nat.Prime 523 ∧ Nat.Prime 541 ∧ Nat.Prime 547 ∧ 523 < 541 ∧ 541 < 547 ∧
      primeFactorDensity 15 541 < primeFactorDensity 15 523 ∧
      primeFactorDensity 15 541 < primeFactorDensity 15 547
    exact valley_certificate_of_normalized_coeff 15 523 541 547 13 14 19 7 (by omega)
      consecutive_523_541 consecutive_541_547 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) cert15.1 cert15.2
  · change Nat.Prime 523 ∧ Nat.Prime 541 ∧ Nat.Prime 547 ∧ 523 < 541 ∧ 541 < 547 ∧
      primeFactorDensity 16 541 < primeFactorDensity 16 523 ∧
      primeFactorDensity 16 541 < primeFactorDensity 16 547
    exact valley_certificate_of_normalized_coeff 16 523 541 547 14 15 19 7 (by omega)
      consecutive_523_541 consecutive_541_547 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) cert16.1 cert16.2
  · change Nat.Prime 887 ∧ Nat.Prime 907 ∧ Nat.Prime 911 ∧ 887 < 907 ∧ 907 < 911 ∧
      primeFactorDensity 17 907 < primeFactorDensity 17 887 ∧
      primeFactorDensity 17 907 < primeFactorDensity 17 911
    exact valley_certificate_of_normalized_coeff 17 887 907 911 15 16 21 5 (by omega)
      consecutive_887_907 consecutive_907_911 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) cert17.1 cert17.2
  · change Nat.Prime 887 ∧ Nat.Prime 907 ∧ Nat.Prime 911 ∧ 887 < 907 ∧ 907 < 911 ∧
      primeFactorDensity 18 907 < primeFactorDensity 18 887 ∧
      primeFactorDensity 18 907 < primeFactorDensity 18 911
    exact valley_certificate_of_normalized_coeff 18 887 907 911 16 17 21 5 (by omega)
      consecutive_887_907 consecutive_907_911 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) cert18.1 cert18.2
  · change Nat.Prime 887 ∧ Nat.Prime 907 ∧ Nat.Prime 911 ∧ 887 < 907 ∧ 907 < 911 ∧
      primeFactorDensity 19 907 < primeFactorDensity 19 887 ∧
      primeFactorDensity 19 907 < primeFactorDensity 19 911
    exact valley_certificate_of_normalized_coeff 19 887 907 911 17 18 21 5 (by omega)
      consecutive_887_907 consecutive_907_911 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) cert19.1 cert19.2
  · change Nat.Prime 1129 ∧ Nat.Prime 1151 ∧ Nat.Prime 1153 ∧ 1129 < 1151 ∧ 1151 < 1153 ∧
      primeFactorDensity 20 1151 < primeFactorDensity 20 1129 ∧
      primeFactorDensity 20 1151 < primeFactorDensity 20 1153
    exact valley_certificate_of_normalized_coeff 20 1129 1151 1153 18 19 23 3 (by omega)
      consecutive_1129_1151 consecutive_1151_1153 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) cert20.1 cert20.2

theorem density_not_unimodal_of_range (k : ℕ) (hk4 : 4 ≤ k) (hk20 : k ≤ 20) :
    ¬DensityUnimodal k := by
  obtain ⟨ha, hb, hc, hab, hbc, hba, hbcv⟩ := valley_certificates k hk4 hk20
  exact not_unimodal_of_valley (primeFactorDensity k)
    (valleyTriple k).1 (valleyTriple k).2.1 (valleyTriple k).2.2
    ha hb hc hab hbc hba hbcv

/-- Erdős Problem 690, including the existence and exact value of the stated
natural densities and Cambie's classification: unimodal for positions one
through three, and not unimodal for every position from four through twenty. -/
theorem erdos_690 :
    (∀ k p, 0 < k → p.Prime →
      (kthPrimeFactorSet k p).HasDensity
        ((primeFactorDensity k p : ℚ) : ℝ)) ∧
    (∀ k, 1 ≤ k → k ≤ 3 → DensityUnimodal k) ∧
    (∀ k, 4 ≤ k → k ≤ 20 → ¬DensityUnimodal k) := by
  refine ⟨?_, ?_, density_not_unimodal_of_range⟩
  · intro k p hk hp
    exact kthPrimeFactorSet_hasDensity hk hp
  · intro k hk1 hk3
    interval_cases k
    · exact density_one_unimodal
    · exact density_two_unimodal
    · exact density_three_unimodal

end Erdos690

#print axioms Erdos690.erdos_690
