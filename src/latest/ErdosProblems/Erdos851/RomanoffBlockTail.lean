/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Data.Nat.Log

/-!
# Geometric block tails for Romanoff's series

This file isolates the elementary real-variable step in Romanoff's
convergence argument.  A fifth-moment estimate for the mass of all indices
whose order is at most `X` implies a geometric estimate for the weighted
mass in the order block `[32^j, 32^(j+1))`.  The base `32 = 2^5` makes the
fifth-root calculation algebraic.

All statements are finite.  They can therefore be applied before passing to
an infinite sum, without any countability or local-finiteness assumptions.
-/

namespace Erdos851

open scoped BigOperators

namespace RomanoffBlockTail

/-- The mass in a finite set carried by indices of order at most `X`. -/
def prefixMass (f : ℕ → ℝ) (order : ℕ → ℕ) (S : Finset ℕ) (X : ℕ) : ℝ :=
  ∑ q ∈ S with order q ≤ X, f q

/-- The indices in `S` whose order lies in the half-open `32`-adic block
`[32^j, 32^(j+1))`. -/
def orderBlock (order : ℕ → ℕ) (S : Finset ℕ) (j : ℕ) : Finset ℕ :=
  S.filter fun q ↦ 32 ^ j ≤ order q ∧ order q < 32 ^ (j + 1)

/-- A `32`-adic block is contained in the prefix ending at the upper
endpoint of the block. -/
theorem sum_orderBlock_le_prefixMass
    {f : ℕ → ℝ} {order : ℕ → ℕ} (S : Finset ℕ) (j : ℕ)
    (hf : ∀ q, 0 ≤ f q) :
    ∑ q ∈ orderBlock order S j, f q ≤
      prefixMass f order S (32 ^ (j + 1)) := by
  classical
  unfold orderBlock prefixMass
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro q hq
    simp only [Finset.mem_filter] at hq ⊢
    exact ⟨hq.1, hq.2.2.le⟩
  · intro q hq hnot
    exact hf q

/-- Replacing each denominator in one order block by the lower endpoint can
only increase the weighted sum. -/
theorem weighted_orderBlock_le_mass_div
    {f : ℕ → ℝ} {order : ℕ → ℕ} (S : Finset ℕ) (j : ℕ)
    (hf : ∀ q, 0 ≤ f q) :
    ∑ q ∈ orderBlock order S j, f q / (order q : ℝ) ≤
      (∑ q ∈ orderBlock order S j, f q) / (32 : ℝ) ^ j := by
  classical
  rw [div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro q hq
  have hq' := (Finset.mem_filter.mp hq).2.1
  have hdenPos : (0 : ℝ) < order q := by
    exact_mod_cast (lt_of_lt_of_le (pow_pos (by norm_num : 0 < (32 : ℕ)) j) hq')
  have hbasePos : (0 : ℝ) < (32 : ℝ) ^ j := by positivity
  exact div_le_div_of_nonneg_left (hf q) hbasePos
    (by exact_mod_cast hq')

/-- The numerical fifth-power comparison used to avoid taking real fifth
roots. -/
theorem fifthMoment_numerical_bound (j : ℕ) :
    8 * ((32 : ℝ) ^ (j + 1)) ^ 4 ≤
      (32 * (16 : ℝ) ^ j) ^ 5 := by
  have hpowers : (((32 : ℝ) ^ j) ^ 4) = (((16 : ℝ) ^ j) ^ 5) := by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm j 4, Nat.mul_comm j 5,
      pow_mul, pow_mul]
    norm_num
  rw [pow_add, pow_one, mul_pow, mul_pow, hpowers]
  have hnonneg : 0 ≤ ((16 : ℝ) ^ j) ^ 5 := by positivity
  nlinarith

/-- A fifth-moment prefix bound implies the geometric weighted-block bound
`32 * 2^(-j)`.  The constant is deliberately not optimized. -/
theorem weighted_orderBlock_le_geometric
    {f : ℕ → ℝ} {order : ℕ → ℕ} (S : Finset ℕ) (j : ℕ)
    (hf : ∀ q, 0 ≤ f q)
    (hFifth :
      (prefixMass f order S (32 ^ (j + 1))) ^ 5 ≤
        8 * ((32 : ℝ) ^ (j + 1)) ^ 4) :
    ∑ q ∈ orderBlock order S j, f q / (order q : ℝ) ≤
      32 * (1 / 2 : ℝ) ^ j := by
  have hprefix : prefixMass f order S (32 ^ (j + 1)) ≤
      32 * (16 : ℝ) ^ j := by
    apply le_of_pow_le_pow_left₀ (by norm_num : 5 ≠ 0) (by positivity)
    exact hFifth.trans (fifthMoment_numerical_bound j)
  calc
    ∑ q ∈ orderBlock order S j, f q / (order q : ℝ) ≤
        (∑ q ∈ orderBlock order S j, f q) / (32 : ℝ) ^ j :=
      weighted_orderBlock_le_mass_div S j hf
    _ ≤ prefixMass f order S (32 ^ (j + 1)) / (32 : ℝ) ^ j := by
      gcongr
      exact sum_orderBlock_le_prefixMass S j hf
    _ ≤ (32 * (16 : ℝ) ^ j) / (32 : ℝ) ^ j := by
      gcongr
    _ = 32 * (1 / 2 : ℝ) ^ j := by
      rw [mul_div_assoc, ← div_pow]
      norm_num

/-- A uniform fifth-moment estimate supplies the geometric bound for every
`32`-adic order block. -/
theorem weighted_orderBlock_le_geometric_of_all_prefixes
    {f : ℕ → ℝ} {order : ℕ → ℕ} (S : Finset ℕ)
    (hf : ∀ q, 0 ≤ f q)
    (hFifth : ∀ X : ℕ,
      (prefixMass f order S X) ^ 5 ≤ 8 * (X : ℝ) ^ 4) (j : ℕ) :
    ∑ q ∈ orderBlock order S j, f q / (order q : ℝ) ≤
      32 * (1 / 2 : ℝ) ^ j := by
  apply weighted_orderBlock_le_geometric S j hf
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using hFifth (32 ^ (j + 1))

/-- The sum of any finite consecutive collection of weighted order blocks is
bounded by the corresponding geometric sum. -/
theorem sum_weighted_orderBlocks_le_geometric
    {f : ℕ → ℝ} {order : ℕ → ℕ} (S : Finset ℕ)
    (hf : ∀ q, 0 ≤ f q)
    (hFifth : ∀ X : ℕ,
      (prefixMass f order S X) ^ 5 ≤ 8 * (X : ℝ) ^ 4)
    (J N : ℕ) :
    ∑ j ∈ Finset.Ico J N,
        (∑ q ∈ orderBlock order S j, f q / (order q : ℝ)) ≤
      ∑ j ∈ Finset.Ico J N, 32 * (1 / 2 : ℝ) ^ j := by
  apply Finset.sum_le_sum
  intro j hj
  exact weighted_orderBlock_le_geometric_of_all_prefixes S hf hFifth j

/-- Quantitative finite tail bound.  Every finite union of order blocks with
indices in `[J,N)` has weighted mass at most `64 * 2^(-J)`. -/
theorem sum_weighted_orderBlocks_le_tail
    {f : ℕ → ℝ} {order : ℕ → ℕ} (S : Finset ℕ)
    (hf : ∀ q, 0 ≤ f q)
    (hFifth : ∀ X : ℕ,
      (prefixMass f order S X) ^ 5 ≤ 8 * (X : ℝ) ^ 4)
    (J N : ℕ) :
    ∑ j ∈ Finset.Ico J N,
        (∑ q ∈ orderBlock order S j, f q / (order q : ℝ)) ≤
      64 * (1 / 2 : ℝ) ^ J := by
  calc
    ∑ j ∈ Finset.Ico J N,
        (∑ q ∈ orderBlock order S j, f q / (order q : ℝ)) ≤
        ∑ j ∈ Finset.Ico J N, 32 * (1 / 2 : ℝ) ^ j :=
      sum_weighted_orderBlocks_le_geometric S hf hFifth J N
    _ ≤ ∑ i ∈ Finset.range (N - J),
        32 * (1 / 2 : ℝ) ^ (J + i) := by
      rw [Finset.sum_Ico_eq_sum_range]
    _ = 32 * (1 / 2 : ℝ) ^ J *
        ∑ i ∈ Finset.range (N - J), (1 / 2 : ℝ) ^ i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [pow_add]
      ring
    _ ≤ 32 * (1 / 2 : ℝ) ^ J * 2 := by
      gcongr
      exact sum_geometric_two_le (N - J)
    _ = 64 * (1 / 2 : ℝ) ^ J := by ring

/-- For a positive order, membership in the `j`th block is equivalent to
having base-`32` logarithm equal to `j`. -/
theorem mem_orderBlock_iff_log_eq
    {order : ℕ → ℕ} {S : Finset ℕ} {q j : ℕ} (hq : 0 < order q) :
    q ∈ orderBlock order S j ↔
      q ∈ S ∧ Nat.log 32 (order q) = j := by
  classical
  simp only [orderBlock, Finset.mem_filter]
  constructor
  · rintro ⟨hqS, hlo, hhi⟩
    exact ⟨hqS, Nat.log_eq_of_pow_le_of_lt_pow hlo hhi⟩
  · rintro ⟨hqS, hlog⟩
    subst j
    exact ⟨hqS, Nat.pow_log_le_self 32 hq.ne',
      Nat.lt_pow_succ_log_self (by norm_num) (order q)⟩

/-- The fifth-moment hypothesis gives a uniform bound for the weighted sum
over an arbitrary finite set.  Terms with zero mass are harmless; positivity
of `order` is needed only on the support of `f`. -/
theorem sum_weighted_le_64
    {f : ℕ → ℝ} {order : ℕ → ℕ}
    (hf : ∀ q, 0 ≤ f q)
    (horder : ∀ q, f q ≠ 0 → 0 < order q)
    (hFifth : ∀ (S : Finset ℕ) (X : ℕ),
      (prefixMass f order S X) ^ 5 ≤ 8 * (X : ℝ) ^ 4)
    (S : Finset ℕ) :
    ∑ q ∈ S, f q / (order q : ℝ) ≤ 64 := by
  classical
  let T := S.filter fun q ↦ f q ≠ 0
  let blockIndex := fun q ↦ Nat.log 32 (order q)
  have hsumT :
      ∑ q ∈ S, f q / (order q : ℝ) =
        ∑ q ∈ T, f q / (order q : ℝ) := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro q hqS hqT
    have hfq : f q = 0 := by
      by_contra hfq
      exact hqT (Finset.mem_filter.mpr ⟨hqS, hfq⟩)
    simp [hfq]
  have hmaps : ∀ q ∈ T, blockIndex q ∈ T.image blockIndex :=
    fun q hq ↦ Finset.mem_image_of_mem blockIndex hq
  have hfiber := Finset.sum_fiberwise_of_maps_to hmaps
    (fun q ↦ f q / (order q : ℝ))
  have hblock (j : ℕ) :
      T.filter (fun q ↦ blockIndex q = j) = orderBlock order T j := by
    ext q
    by_cases hqT : q ∈ T
    · have hfq : f q ≠ 0 := (Finset.mem_filter.mp hqT).2
      rw [mem_orderBlock_iff_log_eq (horder q hfq)]
      simp only [Finset.mem_filter, hqT, true_and]
      rfl
    · simp [orderBlock, hqT]
  have hgeomSummable : Summable (fun j : ℕ ↦ 32 * (1 / 2 : ℝ) ^ j) :=
    summable_geometric_two.mul_left 32
  calc
    ∑ q ∈ S, f q / (order q : ℝ) =
        ∑ q ∈ T, f q / (order q : ℝ) := hsumT
    _ = ∑ j ∈ T.image blockIndex,
        (∑ q ∈ orderBlock order T j, f q / (order q : ℝ)) := by
      rw [← hfiber]
      apply Finset.sum_congr rfl
      intro j hj
      rw [hblock]
    _ ≤ ∑ j ∈ T.image blockIndex, 32 * (1 / 2 : ℝ) ^ j := by
      apply Finset.sum_le_sum
      intro j hj
      exact weighted_orderBlock_le_geometric_of_all_prefixes T hf (hFifth T) j
    _ ≤ ∑' j : ℕ, 32 * (1 / 2 : ℝ) ^ j := by
      exact hgeomSummable.sum_le_tsum _ (fun j hj ↦ by positivity)
    _ = 64 := by
      rw [tsum_mul_left, tsum_geometric_two]
      norm_num

/-- Abstract Romanoff block summability criterion.  No finiteness assumption
on order fibers is needed: the moment bound is required uniformly for every
finite set, exactly as in `summable_of_sum_le`. -/
theorem summable_weighted_of_fifthMoment
    {f : ℕ → ℝ} {order : ℕ → ℕ}
    (hf : ∀ q, 0 ≤ f q)
    (horder : ∀ q, f q ≠ 0 → 0 < order q)
    (hFifth : ∀ (S : Finset ℕ) (X : ℕ),
      (prefixMass f order S X) ^ 5 ≤ 8 * (X : ℝ) ^ 4) :
    Summable (fun q ↦ f q / (order q : ℝ)) := by
  apply summable_of_sum_le (fun q ↦ div_nonneg (hf q) (by positivity))
  exact sum_weighted_le_64 hf horder hFifth

/-- Quantitative arbitrary-finite-set tail.  If every nonzero term has order
at least `32^J`, its total weighted mass is at most `64 * 2^(-J)`. -/
theorem sum_weighted_le_tail
    {f : ℕ → ℝ} {order : ℕ → ℕ}
    (hf : ∀ q, 0 ≤ f q)
    (horder : ∀ q, f q ≠ 0 → 0 < order q)
    (hFifth : ∀ (S : Finset ℕ) (X : ℕ),
      (prefixMass f order S X) ^ 5 ≤ 8 * (X : ℝ) ^ 4)
    (S : Finset ℕ) (J : ℕ)
    (hlarge : ∀ q ∈ S, f q ≠ 0 → 32 ^ J ≤ order q) :
    ∑ q ∈ S, f q / (order q : ℝ) ≤
      64 * (1 / 2 : ℝ) ^ J := by
  classical
  let T := S.filter fun q ↦ f q ≠ 0
  let blockIndex := fun q ↦ Nat.log 32 (order q)
  have hsumT :
      ∑ q ∈ S, f q / (order q : ℝ) =
        ∑ q ∈ T, f q / (order q : ℝ) := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro q hqS hqT
    have hfq : f q = 0 := by
      by_contra hfq
      exact hqT (Finset.mem_filter.mpr ⟨hqS, hfq⟩)
    simp [hfq]
  have hmaps : ∀ q ∈ T, blockIndex q ∈ T.image blockIndex :=
    fun q hq ↦ Finset.mem_image_of_mem blockIndex hq
  have hfiber := Finset.sum_fiberwise_of_maps_to hmaps
    (fun q ↦ f q / (order q : ℝ))
  have hblock (j : ℕ) :
      T.filter (fun q ↦ blockIndex q = j) = orderBlock order T j := by
    ext q
    by_cases hqT : q ∈ T
    · have hfq : f q ≠ 0 := (Finset.mem_filter.mp hqT).2
      rw [mem_orderBlock_iff_log_eq (horder q hfq)]
      simp only [Finset.mem_filter, hqT, true_and]
      rfl
    · simp [orderBlock, hqT]
  have hindexLarge : ∀ j ∈ T.image blockIndex, J ≤ j := by
    intro j hj
    obtain ⟨q, hqT, rfl⟩ := Finset.mem_image.mp hj
    have hqS : q ∈ S := (Finset.mem_filter.mp hqT).1
    have hfq : f q ≠ 0 := (Finset.mem_filter.mp hqT).2
    exact Nat.le_log_of_pow_le (by norm_num) (hlarge q hqS hfq)
  let tailMajorant := fun j : ℕ ↦
    if J ≤ j then 32 * (1 / 2 : ℝ) ^ j else 0
  have htailSummable : Summable tailMajorant := by
    apply Summable.of_nonneg_of_le
      (fun j ↦ by simp only [tailMajorant]; split_ifs <;> positivity)
      (fun j ↦ by simp only [tailMajorant]; split_ifs <;> simp)
      (summable_geometric_two.mul_left 32)
  calc
    ∑ q ∈ S, f q / (order q : ℝ) =
        ∑ q ∈ T, f q / (order q : ℝ) := hsumT
    _ = ∑ j ∈ T.image blockIndex,
        (∑ q ∈ orderBlock order T j, f q / (order q : ℝ)) := by
      rw [← hfiber]
      apply Finset.sum_congr rfl
      intro j hj
      rw [hblock]
    _ ≤ ∑ j ∈ T.image blockIndex, tailMajorant j := by
      apply Finset.sum_le_sum
      intro j hj
      simp only [tailMajorant, if_pos (hindexLarge j hj)]
      exact weighted_orderBlock_le_geometric_of_all_prefixes T hf (hFifth T) j
    _ ≤ ∑' j : ℕ, tailMajorant j := by
      exact htailSummable.sum_le_tsum _ (fun j hj ↦ by
        simp only [tailMajorant]
        split_ifs <;> positivity)
    _ = 64 * (1 / 2 : ℝ) ^ J := by
      simp only [tailMajorant]
      have htail :
          (∑' j : ℕ, if J ≤ j then (1 / 2 : ℝ) ^ j else 0) =
            2 * (1 / 2 : ℝ) ^ J := by
        simpa only [one_div] using tsum_geometric_inv_two_ge J
      calc
        (∑' j : ℕ, if J ≤ j then 32 * (1 / 2 : ℝ) ^ j else 0) =
            ∑' j : ℕ, 32 * (if J ≤ j then (1 / 2 : ℝ) ^ j else 0) := by
          apply tsum_congr
          intro j
          split_ifs <;> ring
        _ = 32 * ∑' j : ℕ, if J ≤ j then (1 / 2 : ℝ) ^ j else 0 := by
          rw [tsum_mul_left]
        _ = 64 * (1 / 2 : ℝ) ^ J := by rw [htail]; ring

end RomanoffBlockTail

end Erdos851
