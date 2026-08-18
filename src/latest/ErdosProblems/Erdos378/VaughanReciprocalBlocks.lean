/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos378.BilinearReciprocal
import BoundedGaps.BombieriVinogradov.Analytic.Dyadic
import BoundedGaps.BombieriVinogradov.Analytic.VaughanFourthTermMangoldtEnergy

/-!
# Dyadic Vaughan blocks for the reciprocal phase

The fourth Vaughan term is first padded to one fixed rectangle; its original
product interval is retained by an explicit zero-valued cutoff weight.  This
makes two independent dyadic decompositions available and lets the finite
bilinear estimate from `BilinearReciprocal` apply block by block.
-/

open scoped BigOperators ArithmeticFunction.vonMangoldt

namespace Erdos378
namespace VaughanReciprocalBlocks

open BoundedGaps.Maynard
open PrimeReciprocal
open BilinearReciprocal

noncomputable section

def cutoffMangoldtCoefficient (U : ℝ) (m : ℕ) : ℂ :=
  if U < (m : ℝ) then ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ) else 0

def cutoffFourthCoefficient (V : ℝ) (k : ℕ) : ℂ :=
  if V < (k : ℝ) then ((vaughanFourthCoefficient V k : ℝ) : ℂ) else 0

/-- The fixed rectangle representing Vaughan's fourth term. -/
def reciprocalVaughanFourthRectangle
    (X U V : ℝ) (x y : ℕ) : ℂ :=
  ∑ m ∈ Finset.Icc 2 y, cutoffMangoldtCoefficient U m *
    ∑ k ∈ Finset.Icc 2 y, cutoffFourthCoefficient V k *
      reciprocalCutoffWeight X x y m k

/-- Pad one variable-dependent inner interval to the fixed rectangle. -/
theorem nestedFourthInner_eq_rectangle
    (X : ℝ) {V : ℝ} (hV : 1 ≤ V) {x y m : ℕ} (hm : 0 < m) :
    (∑ k ∈ (Finset.Ioc (x / m) (y / m)).filter
        (fun k : ℕ ↦ V < (k : ℝ)),
      ((vaughanFourthCoefficient V k : ℝ) : ℂ) *
        reciprocalWeight X (m * k)) =
      ∑ k ∈ Finset.Icc 2 y, cutoffFourthCoefficient V k *
        reciprocalCutoffWeight X x y m k := by
  let P : ℕ → Prop := fun k ↦
    V < (k : ℝ) ∧ x < m * k ∧ m * k ≤ y
  let f : ℕ → ℂ := fun k ↦
    ((vaughanFourthCoefficient V k : ℝ) : ℂ) *
      reciprocalWeight X (m * k)
  have hset :
      (Finset.Ioc (x / m) (y / m)).filter
          (fun k : ℕ ↦ V < (k : ℝ)) =
        (Finset.Icc 2 y).filter P := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Icc, P]
    constructor
    · rintro ⟨⟨hxdiv, hydiv⟩, hkV⟩
      have hkTwo : 2 ≤ k := by
        have hkOneReal : (1 : ℝ) < k := hV.trans_lt hkV
        exact_mod_cast hkOneReal
      have hky : k ≤ y := hydiv.trans (Nat.div_le_self y m)
      exact ⟨⟨hkTwo, hky⟩, hkV,
        by simpa [Nat.mul_comm] using (Nat.div_lt_iff_lt_mul hm).mp hxdiv,
        by simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hm).mp hydiv⟩
    · rintro ⟨⟨hkTwo, hky⟩, hkV, hxprod, hyprod⟩
      exact ⟨⟨(Nat.div_lt_iff_lt_mul hm).mpr (by simpa [Nat.mul_comm] using hxprod),
        (Nat.le_div_iff_mul_le hm).mpr (by simpa [Nat.mul_comm] using hyprod)⟩, hkV⟩
  rw [hset]
  change (∑ k ∈ (Finset.Icc 2 y).filter P, f k) = _
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hkV : V < (k : ℝ)
  · by_cases hkprod : x < m * k ∧ m * k ≤ y
    · simp [P, f, cutoffFourthCoefficient, reciprocalCutoffWeight, hkV, hkprod]
    · simp [P, f, cutoffFourthCoefficient, reciprocalCutoffWeight, hkV, hkprod]
  · simp [P, f, cutoffFourthCoefficient, reciprocalCutoffWeight, hkV]

/-- Exact rectangular form of the reciprocal-twisted fourth Vaughan term. -/
theorem weightedVaughanIntervalFour_reciprocal_eq_rectangle
    (X : ℝ) {U V : ℝ} (hU : 1 ≤ U) (hV : 1 ≤ V) (x y : ℕ) :
    weightedVaughanIntervalFour (reciprocalWeight X) U V x y =
      -reciprocalVaughanFourthRectangle X U V x y := by
  rw [weightedVaughanIntervalFour_eq_nested (reciprocalWeight X) hU hV x y]
  apply congrArg Neg.neg
  unfold reciprocalVaughanFourthRectangle
  have houter :
      (Finset.Icc 1 y).filter (fun m : ℕ ↦ U < (m : ℝ)) =
        (Finset.Icc 2 y).filter (fun m : ℕ ↦ U < (m : ℝ)) := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hmOne, hmy⟩, hmU⟩
      have hmTwo : 2 ≤ m := by
        have hmOneReal : (1 : ℝ) < m := hU.trans_lt hmU
        exact_mod_cast hmOneReal
      exact ⟨⟨hmTwo, hmy⟩, hmU⟩
    · rintro ⟨⟨hmTwo, hmy⟩, hmU⟩
      exact ⟨⟨by omega, hmy⟩, hmU⟩
  rw [houter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro m hm
  by_cases hmU : U < (m : ℝ)
  · simp only [hmU, if_true, cutoffMangoldtCoefficient]
    have hmTwo := (Finset.mem_Icc.mp hm).1
    rw [nestedFourthInner_eq_rectangle X hV (by omega : 0 < m)]
  · simp [hmU, cutoffMangoldtCoefficient]

/-! ## Exact dyadic decomposition of the padded rectangle -/

/-- The actual upper endpoint of the `alpha`th dyadic block after truncating
at the ambient endpoint `y`. -/
def dyadicUpper (y alpha : ℕ) : ℕ :=
  min y (2 ^ (alpha + 1))

lemma filter_Icc_dyadicBlock_eq_Ioc (y alpha : ℕ) :
    (Finset.Icc 2 y).filter (fun t ↦ t ∈ dyadicBlock alpha) =
      Finset.Ioc (2 ^ alpha) (dyadicUpper y alpha) := by
  ext t
  simp only [Finset.mem_filter, Finset.mem_Icc, dyadicBlock,
    Finset.mem_Ioc, dyadicUpper, Nat.le_min]
  constructor
  · rintro ⟨⟨htwo, hty⟩, htlo, hthi⟩
    exact ⟨htlo, hty, hthi⟩
  · rintro ⟨htlo, hty, hthi⟩
    have hpow : 0 < 2 ^ alpha := pow_pos (by omega : 0 < 2) alpha
    exact ⟨⟨by omega, hty⟩, htlo, hthi⟩

/-- One independently dyadic block of the rectangular fourth Vaughan term. -/
def reciprocalVaughanFourthDyadicBlock
    (X U V : ℝ) (x y alpha beta : ℕ) : ℂ :=
  reciprocalBilinearBlock X x y
    (2 ^ alpha) (dyadicUpper y alpha)
    (2 ^ beta) (dyadicUpper y beta)
    (cutoffMangoldtCoefficient U) (cutoffFourthCoefficient V)

/-- The same block with both dyadic intervals filled out.  The product cutoff
makes all newly inserted terms vanish. -/
def reciprocalVaughanFourthFullDyadicBlock
    (X U V : ℝ) (x y alpha beta : ℕ) : ℂ :=
  reciprocalBilinearBlock X x y
    (2 ^ alpha) (2 ^ (alpha + 1))
    (2 ^ beta) (2 ^ (beta + 1))
    (cutoffMangoldtCoefficient U) (cutoffFourthCoefficient V)

lemma reciprocalVaughanFourthDyadicBlock_eq_full
    (X U V : ℝ) (x y alpha beta : ℕ) :
    reciprocalVaughanFourthDyadicBlock X U V x y alpha beta =
      reciprocalVaughanFourthFullDyadicBlock X U V x y alpha beta := by
  let M := 2 ^ alpha
  let M₁ := 2 ^ (alpha + 1)
  let K := 2 ^ beta
  let K₁ := 2 ^ (beta + 1)
  let a := cutoffMangoldtCoefficient U
  let b := cutoffFourthCoefficient V
  let w := reciprocalCutoffWeight X x y
  have hM : 0 < M := by dsimp only [M]; positivity
  have hK : 0 < K := by dsimp only [K]; positivity
  have hmSubset : Finset.Ioc M (dyadicUpper y alpha) ⊆ Finset.Ioc M M₁ := by
    intro m hm
    rcases Finset.mem_Ioc.mp hm with ⟨hMm, hmy⟩
    exact Finset.mem_Ioc.mpr ⟨hMm, hmy.trans (Nat.min_le_right _ _)⟩
  have hkSubset : Finset.Ioc K (dyadicUpper y beta) ⊆ Finset.Ioc K K₁ := by
    intro k hk
    rcases Finset.mem_Ioc.mp hk with ⟨hKk, hky⟩
    exact Finset.mem_Ioc.mpr ⟨hKk, hky.trans (Nat.min_le_right _ _)⟩
  have hinner (m : ℕ) (hm : m ∈ Finset.Ioc M M₁) :
      (∑ k ∈ Finset.Ioc K (dyadicUpper y beta), b k * w m k) =
        ∑ k ∈ Finset.Ioc K K₁, b k * w m k := by
    apply Finset.sum_subset hkSubset
    intro k hkFull hkNot
    have hkBounds := Finset.mem_Ioc.mp hkFull
    have hky : y < k := by
      by_contra hnot
      apply hkNot
      rw [Finset.mem_Ioc]
      exact ⟨hkBounds.1, le_min (Nat.le_of_not_gt hnot) hkBounds.2⟩
    have hmy : y < m * k := by
      have hmPos : 0 < m := hM.trans (Finset.mem_Ioc.mp hm).1
      nlinarith
    unfold w reciprocalCutoffWeight
    rw [if_neg (fun h : x < m * k ∧ m * k ≤ y ↦ (not_le_of_gt hmy) h.2)]
    simp
  change (∑ m ∈ Finset.Ioc M (dyadicUpper y alpha),
      a m * ∑ k ∈ Finset.Ioc K (dyadicUpper y beta), b k * w m k) =
    ∑ m ∈ Finset.Ioc M M₁, a m * ∑ k ∈ Finset.Ioc K K₁, b k * w m k
  calc
    (∑ m ∈ Finset.Ioc M (dyadicUpper y alpha),
      a m * ∑ k ∈ Finset.Ioc K (dyadicUpper y beta), b k * w m k) =
      ∑ m ∈ Finset.Ioc M (dyadicUpper y alpha),
        a m * ∑ k ∈ Finset.Ioc K K₁, b k * w m k := by
          apply Finset.sum_congr rfl
          intro m hm
          rw [hinner m (hmSubset hm)]
    _ = ∑ m ∈ Finset.Ioc M M₁,
        a m * ∑ k ∈ Finset.Ioc K K₁, b k * w m k := by
      apply Finset.sum_subset hmSubset
      intro m hmFull hmNot
      have hmBounds := Finset.mem_Ioc.mp hmFull
      have hmy : y < m := by
        by_contra hnot
        apply hmNot
        rw [Finset.mem_Ioc]
        exact ⟨hmBounds.1, le_min (Nat.le_of_not_gt hnot) hmBounds.2⟩
      apply mul_eq_zero_of_right
      apply Finset.sum_eq_zero
      intro k hk
      have hkPos : 0 < k := hK.trans (Finset.mem_Ioc.mp hk).1
      have hprod : y < m * k := by nlinarith
      unfold w reciprocalCutoffWeight
      rw [if_neg (fun h : x < m * k ∧ m * k ≤ y ↦ (not_le_of_gt hprod) h.2)]
      simp

private lemma sum_Icc_eq_sum_dyadicIoc
    {A : Type*} [AddCommMonoid A] (y : ℕ) (f : ℕ → A) :
    (∑ t ∈ Finset.Icc 2 y, f t) =
      ∑ alpha ∈ dyadicExponentRange y,
        ∑ t ∈ Finset.Ioc (2 ^ alpha) (dyadicUpper y alpha), f t := by
  rw [sum_eq_sum_dyadicBlocks (Finset.Icc 2 y) (by
    intro t ht
    simpa only [Finset.mem_Icc] using ht) f]
  apply Finset.sum_congr rfl
  intro alpha _halpha
  rw [filter_Icc_dyadicBlock_eq_Ioc]

/-- The padded fourth Vaughan rectangle is exactly the sum of its two-variable
dyadic blocks.  There is no boundary error: each variable is partitioned
independently and the original product cutoff remains inside the weight. -/
theorem reciprocalVaughanFourthRectangle_eq_sum_dyadicBlocks
    (X U V : ℝ) (x y : ℕ) :
    reciprocalVaughanFourthRectangle X U V x y =
      ∑ alpha ∈ dyadicExponentRange y,
        ∑ beta ∈ dyadicExponentRange y,
          reciprocalVaughanFourthDyadicBlock X U V x y alpha beta := by
  unfold reciprocalVaughanFourthRectangle
  rw [sum_Icc_eq_sum_dyadicIoc y]
  conv_lhs =>
    enter [2, alpha, 2, m]
    rw [sum_Icc_eq_sum_dyadicIoc y]
    rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro alpha _halpha
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro beta _hbeta
  simp only [reciprocalVaughanFourthDyadicBlock,
    reciprocalBilinearBlock]

/-- Exact dyadic expansion of the reciprocal-twisted fourth Vaughan term. -/
theorem weightedVaughanIntervalFour_reciprocal_eq_neg_sum_dyadicBlocks
    (X : ℝ) {U V : ℝ} (hU : 1 ≤ U) (hV : 1 ≤ V) (x y : ℕ) :
    weightedVaughanIntervalFour (reciprocalWeight X) U V x y =
      -∑ alpha ∈ dyadicExponentRange y,
        ∑ beta ∈ dyadicExponentRange y,
          reciprocalVaughanFourthDyadicBlock X U V x y alpha beta := by
  rw [weightedVaughanIntervalFour_reciprocal_eq_rectangle X hU hV x y,
    reciprocalVaughanFourthRectangle_eq_sum_dyadicBlocks]

end

end VaughanReciprocalBlocks
end Erdos378
