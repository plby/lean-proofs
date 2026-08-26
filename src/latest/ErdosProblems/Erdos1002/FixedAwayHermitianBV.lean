import ErdosProblems.Erdos1002.RamanujanBVMultiplier
import Mathlib.Order.Filter.AtTopBot.Interval

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Hermitian BV and Parseval bridge for the fixed-away range

This file supplies the all-integer form of the bounded-variation Abel
estimate used for distinct Ramanujan moduli.  It also accounts explicitly
for the two jumps created by deleting a closed integer interval, expands a
finite denominator block with the required complex conjugate, and separates
the exceptional modulus `p = 1`, diagonal pairs, and off-diagonal pairs.

The analytic decay estimates for the particular principal-value multiplier
are deliberately not assumed here: they enter later through the stated
summability, supremum, and total-variation hypotheses.
-/

open Filter Finset
open scoped ArithmeticFunction.sigma BigOperators ComplexConjugate Topology

namespace Erdos1002

noncomputable section

def hermitianRamanujanMultiplierTerm
    (w : ℤ → ℂ) (p p' : ℕ) (n : ℤ) : ℂ :=
  (ramanujanSum p n * conj (ramanujanSum p' n)) * w n

theorem summable_norm_hermitianRamanujanMultiplierTerm
    (w : ℤ → ℂ) (p p' : ℕ)
    (hw : Summable fun n : ℤ ↦ ‖w n‖) :
    Summable fun n : ℤ ↦
      ‖hermitianRamanujanMultiplierTerm w p p' n‖ := by
  have hmajor := hw.mul_left
    ((Nat.totient p : ℝ) * (Nat.totient p' : ℝ))
  apply hmajor.of_nonneg_of_le
  · intro n
    exact norm_nonneg _
  · intro n
    unfold hermitianRamanujanMultiplierTerm
    rw [norm_mul, norm_mul, Complex.norm_conj]
    have hp := norm_ramanujanSum_le_totient p n
    have hp' := norm_ramanujanSum_le_totient p' n
    exact mul_le_mul
      (mul_le_mul hp hp' (norm_nonneg _) (by positivity))
      le_rfl (norm_nonneg _) (by positivity)

theorem norm_tsum_hermitianRamanujanMultiplierTerm_le
    (w : ℤ → ℂ) {p p' : ℕ}
    (hp : p ≠ 0) (hp' : p' ≠ 0) (hpp' : p ≠ p')
    (hw : Summable fun n : ℤ ↦ ‖w n‖)
    (hvariation : Summable fun n : ℤ ↦ ‖w n - w (n + 1)‖)
    {B V : ℝ} (hSup : ∀ n : ℤ, ‖w n‖ ≤ B)
    (hVar : (∑' n : ℤ, ‖w n - w (n + 1)‖) ≤ V) :
    ‖∑' n : ℤ, hermitianRamanujanMultiplierTerm w p p' n‖ ≤
      (2 * ((ArithmeticFunction.sigma 1 p : ℝ) *
        (ArithmeticFunction.sigma 1 p' : ℝ))) * (B + V) := by
  have hterm := summable_norm_hermitianRamanujanMultiplierTerm
    w p p' hw
  have hlimit : Tendsto
      (fun K : ℕ ↦ ∑ n ∈ Icc (-(K : ℤ)) (K : ℤ),
        hermitianRamanujanMultiplierTerm w p p' n)
      atTop (nhds (∑' n : ℤ,
        hermitianRamanujanMultiplierTerm w p p' n)) :=
    hterm.of_norm.hasSum.comp (Finset.tendsto_Icc_neg (R := ℤ))
  apply le_of_tendsto hlimit.norm
  filter_upwards with K
  apply norm_weighted_ramanujan_product_int_le_sup_add_variation
    w (by omega) hp hp' hpp'
  · exact hSup (K : ℤ)
  · exact (hvariation.sum_le_tsum (Ico (-(K : ℤ)) (K : ℤ))
      (fun n _hn ↦ norm_nonneg _)).trans hVar

theorem norm_tsum_hermitianRamanujanMultiplierTerm_le_tsum
    (w : ℤ → ℂ) {p p' : ℕ}
    (hp : p ≠ 0) (hp' : p' ≠ 0) (hpp' : p ≠ p')
    (hw : Summable fun n : ℤ ↦ ‖w n‖)
    (hvariation : Summable fun n : ℤ ↦ ‖w n - w (n + 1)‖) :
    ‖∑' n : ℤ, hermitianRamanujanMultiplierTerm w p p' n‖ ≤
      (2 * ((ArithmeticFunction.sigma 1 p : ℝ) *
        (ArithmeticFunction.sigma 1 p' : ℝ))) *
        ((∑' n : ℤ, ‖w n‖) +
          ∑' n : ℤ, ‖w n - w (n + 1)‖) := by
  apply norm_tsum_hermitianRamanujanMultiplierTerm_le
    w hp hp' hpp' hw hvariation
  · intro n
    exact hw.le_tsum n (fun m _hm ↦ norm_nonneg (w m))
  · exact le_rfl

def integerIntervalComplementMultiplier
    (u v : ℤ) (w : ℤ → ℂ) (n : ℤ) : ℂ :=
  if u ≤ n ∧ n ≤ v then 0 else w n

theorem norm_integerIntervalComplementMultiplier_le
    (u v : ℤ) (w : ℤ → ℂ) (n : ℤ) :
    ‖integerIntervalComplementMultiplier u v w n‖ ≤ ‖w n‖ := by
  unfold integerIntervalComplementMultiplier
  split_ifs <;> simp

theorem summable_norm_integerIntervalComplementMultiplier
    (u v : ℤ) (w : ℤ → ℂ)
    (hw : Summable fun n : ℤ ↦ ‖w n‖) :
    Summable fun n : ℤ ↦
      ‖integerIntervalComplementMultiplier u v w n‖ := by
  exact hw.of_nonneg_of_le
    (fun n ↦ norm_nonneg _)
    (norm_integerIntervalComplementMultiplier_le u v w)

theorem norm_integerIntervalComplementMultiplier_sub_succ_le
    {u v : ℤ} (huv : u ≤ v) (w : ℤ → ℂ) (n : ℤ) :
    ‖integerIntervalComplementMultiplier u v w n -
        integerIntervalComplementMultiplier u v w (n + 1)‖ ≤
      ‖w n - w (n + 1)‖ +
        (if n + 1 = u then ‖w u‖ else 0) +
        (if n = v then ‖w v‖ else 0) := by
  by_cases hn : u ≤ n ∧ n ≤ v
  · by_cases hn1 : u ≤ n + 1 ∧ n + 1 ≤ v
    · simp [integerIntervalComplementMultiplier, hn, hn1]
      positivity
    · have hnv : n = v := by omega
      subst n
      have hv : u ≤ v ∧ v ≤ v := ⟨huv, le_rfl⟩
      have hv1 : ¬(u ≤ v + 1 ∧ v + 1 ≤ v) := by omega
      have hvune : v + 1 ≠ u := by omega
      simp only [integerIntervalComplementMultiplier, if_pos hv,
        if_neg hv1, zero_sub, norm_neg]
      simp only [hvune, if_false, if_true, add_zero]
      calc
        ‖w (v + 1)‖ = ‖w v - (w v - w (v + 1))‖ := by
          congr 1
          abel
        _ ≤ ‖w v‖ + ‖w v - w (v + 1)‖ := norm_sub_le _ _
        _ = ‖w v - w (v + 1)‖ + ‖w v‖ := add_comm _ _
  · by_cases hn1 : u ≤ n + 1 ∧ n + 1 ≤ v
    · have hnu : n + 1 = u := by omega
      have hnout : ¬(u ≤ n ∧ n ≤ v) := hn
      rw [hnu] at hn1
      simp only [integerIntervalComplementMultiplier, if_neg hnout,
        if_pos hn1, sub_zero, hnu]
      have hnv : n ≠ v := by omega
      rw [if_neg hnv]
      simp only [if_true, add_zero]
      calc
        ‖w n‖ = ‖(w n - w (n + 1)) + w u‖ := by
          rw [hnu]
          congr 1
          abel
        _ ≤ ‖w n - w (n + 1)‖ + ‖w u‖ := norm_add_le _ _
        _ = ‖w n - w u‖ + ‖w u‖ := by rw [hnu]
    · simp only [integerIntervalComplementMultiplier, if_neg hn, if_neg hn1]
      calc
        ‖w n - w (n + 1)‖ ≤
            ‖w n - w (n + 1)‖ +
              (if n + 1 = u then ‖w u‖ else 0) := by
          apply le_add_of_nonneg_right
          split_ifs <;> positivity
        _ ≤ (‖w n - w (n + 1)‖ +
              (if n + 1 = u then ‖w u‖ else 0)) +
                (if n = v then ‖w v‖ else 0) := by
          apply le_add_of_nonneg_right
          split_ifs <;> positivity

def leftIntervalBoundaryVariation (u : ℤ) (w : ℤ → ℂ) (n : ℤ) : ℝ :=
  if n + 1 = u then ‖w u‖ else 0

def rightIntervalBoundaryVariation (v : ℤ) (w : ℤ → ℂ) (n : ℤ) : ℝ :=
  if n = v then ‖w v‖ else 0

theorem summable_leftIntervalBoundaryVariation
    (u : ℤ) (w : ℤ → ℂ) :
    Summable (leftIntervalBoundaryVariation u w) := by
  apply summable_of_finite_support
  apply (Set.finite_singleton (u - 1)).subset
  intro n hn
  rw [Function.mem_support] at hn
  have heq : n + 1 = u := by
    by_contra hne
    simp [leftIntervalBoundaryVariation, hne] at hn
  simpa only [Set.mem_singleton_iff] using! (show n = u - 1 by omega)

theorem summable_rightIntervalBoundaryVariation
    (v : ℤ) (w : ℤ → ℂ) :
    Summable (rightIntervalBoundaryVariation v w) := by
  apply summable_of_finite_support
  apply (Set.finite_singleton v).subset
  intro n hn
  rw [Function.mem_support] at hn
  have heq : n = v := by
    by_contra hne
    simp [rightIntervalBoundaryVariation, hne] at hn
  simpa only [Set.mem_singleton_iff] using! heq

theorem tsum_leftIntervalBoundaryVariation
    (u : ℤ) (w : ℤ → ℂ) :
    (∑' n : ℤ, leftIntervalBoundaryVariation u w n) = ‖w u‖ := by
  calc
    (∑' n : ℤ, leftIntervalBoundaryVariation u w n) =
        ∑' n : ℤ, if n = u - 1 then ‖w u‖ else 0 := by
      apply tsum_congr
      intro n
      unfold leftIntervalBoundaryVariation
      by_cases h : n = u - 1
      · subst n
        simp
      · have hne : n + 1 ≠ u := by omega
        simp [h, hne]
    _ = ‖w u‖ := by rw [tsum_ite_eq]

theorem tsum_rightIntervalBoundaryVariation
    (v : ℤ) (w : ℤ → ℂ) :
    (∑' n : ℤ, rightIntervalBoundaryVariation v w n) = ‖w v‖ := by
  unfold rightIntervalBoundaryVariation
  rw [tsum_ite_eq]

theorem summable_variation_integerIntervalComplementMultiplier
    {u v : ℤ} (huv : u ≤ v) (w : ℤ → ℂ)
    (hvariation : Summable fun n : ℤ ↦ ‖w n - w (n + 1)‖) :
    Summable fun n : ℤ ↦
      ‖integerIntervalComplementMultiplier u v w n -
        integerIntervalComplementMultiplier u v w (n + 1)‖ := by
  have hleft := summable_leftIntervalBoundaryVariation u w
  have hright := summable_rightIntervalBoundaryVariation v w
  apply (hvariation.add (hleft.add hright)).of_nonneg_of_le
  · intro n
    exact norm_nonneg _
  · intro n
    simpa only [leftIntervalBoundaryVariation,
      rightIntervalBoundaryVariation, add_assoc] using!
        norm_integerIntervalComplementMultiplier_sub_succ_le huv w n

theorem tsum_variation_integerIntervalComplementMultiplier_le
    {u v : ℤ} (huv : u ≤ v) (w : ℤ → ℂ)
    (hvariation : Summable fun n : ℤ ↦ ‖w n - w (n + 1)‖) :
    (∑' n : ℤ,
      ‖integerIntervalComplementMultiplier u v w n -
        integerIntervalComplementMultiplier u v w (n + 1)‖) ≤
      (∑' n : ℤ, ‖w n - w (n + 1)‖) + ‖w u‖ + ‖w v‖ := by
  have hleft := summable_leftIntervalBoundaryVariation u w
  have hright := summable_rightIntervalBoundaryVariation v w
  have hmajor := hvariation.add (hleft.add hright)
  have hproj :=
    summable_variation_integerIntervalComplementMultiplier huv w hvariation
  calc
    (∑' n : ℤ,
        ‖integerIntervalComplementMultiplier u v w n -
          integerIntervalComplementMultiplier u v w (n + 1)‖) ≤
      ∑' n : ℤ,
        (‖w n - w (n + 1)‖ +
          (leftIntervalBoundaryVariation u w n +
            rightIntervalBoundaryVariation v w n)) := by
      apply hproj.tsum_le_tsum
      · intro n
        simpa only [leftIntervalBoundaryVariation,
          rightIntervalBoundaryVariation, add_assoc] using!
          norm_integerIntervalComplementMultiplier_sub_succ_le huv w n
      · exact hmajor
    _ = (∑' n : ℤ, ‖w n - w (n + 1)‖) +
        ((∑' n : ℤ, leftIntervalBoundaryVariation u w n) +
          ∑' n : ℤ, rightIntervalBoundaryVariation v w n) := by
      rw [hvariation.tsum_add (hleft.add hright), hleft.tsum_add hright]
    _ = (∑' n : ℤ, ‖w n - w (n + 1)‖) + ‖w u‖ + ‖w v‖ := by
      rw [tsum_leftIntervalBoundaryVariation,
        tsum_rightIntervalBoundaryVariation]
      ring

theorem norm_tsum_projected_hermitianRamanujanMultiplierTerm_le
    (w : ℤ → ℂ) {u v : ℤ} (huv : u ≤ v) {p p' : ℕ}
    (hp : p ≠ 0) (hp' : p' ≠ 0) (hpp' : p ≠ p')
    (hw : Summable fun n : ℤ ↦ ‖w n‖)
    (hvariation : Summable fun n : ℤ ↦ ‖w n - w (n + 1)‖) :
    ‖∑' n : ℤ,
        hermitianRamanujanMultiplierTerm
          (integerIntervalComplementMultiplier u v w) p p' n‖ ≤
      (2 * ((ArithmeticFunction.sigma 1 p : ℝ) *
        (ArithmeticFunction.sigma 1 p' : ℝ))) *
        ((∑' n : ℤ, ‖w n‖) +
          (∑' n : ℤ, ‖w n - w (n + 1)‖) + ‖w u‖ + ‖w v‖) := by
  have hprojNorm :=
    summable_norm_integerIntervalComplementMultiplier u v w hw
  have hprojVar :=
    summable_variation_integerIntervalComplementMultiplier
      huv w hvariation
  have hraw :=
    norm_tsum_hermitianRamanujanMultiplierTerm_le_tsum
      (integerIntervalComplementMultiplier u v w)
      hp hp' hpp' hprojNorm hprojVar
  calc
    ‖∑' n : ℤ,
        hermitianRamanujanMultiplierTerm
          (integerIntervalComplementMultiplier u v w) p p' n‖ ≤
      (2 * ((ArithmeticFunction.sigma 1 p : ℝ) *
        (ArithmeticFunction.sigma 1 p' : ℝ))) *
        ((∑' n : ℤ, ‖integerIntervalComplementMultiplier u v w n‖) +
          ∑' n : ℤ,
            ‖integerIntervalComplementMultiplier u v w n -
              integerIntervalComplementMultiplier u v w (n + 1)‖) := hraw
    _ ≤ (2 * ((ArithmeticFunction.sigma 1 p : ℝ) *
        (ArithmeticFunction.sigma 1 p' : ℝ))) *
        ((∑' n : ℤ, ‖w n‖) +
          (∑' n : ℤ, ‖w n - w (n + 1)‖) + ‖w u‖ + ‖w v‖) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hnormle := hprojNorm.tsum_le_tsum
        (norm_integerIntervalComplementMultiplier_le u v w) hw
      have hvarle :=
        tsum_variation_integerIntervalComplementMultiplier_le
          huv w hvariation
      linarith

def finiteHermitianBlockCoefficient
    (P : Finset ℕ) (a : ℕ → ℤ → ℂ) (n : ℤ) : ℂ :=
  ∑ p ∈ P, a p n

theorem finiteHermitianBlockCoefficient_norm_sq
    (P : Finset ℕ) (a : ℕ → ℤ → ℂ) (n : ℤ) :
    ((‖finiteHermitianBlockCoefficient P a n‖ ^ 2 : ℝ) : ℂ) =
      ∑ p ∈ P, ∑ p' ∈ P, a p n * conj (a p' n) := by
  unfold finiteHermitianBlockCoefficient
  rw [Complex.sq_norm, ← Complex.mul_conj, map_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.mul_sum]

theorem sum_finiteHermitianBlockCoefficient_norm_sq_Icc
    (P : Finset ℕ) (a : ℕ → ℤ → ℂ) (u v : ℤ) :
    (((∑ n ∈ Icc u v,
        ‖finiteHermitianBlockCoefficient P a n‖ ^ 2) : ℝ) : ℂ) =
      ∑ p ∈ P, ∑ p' ∈ P, ∑ n ∈ Icc u v,
        a p n * conj (a p' n) := by
  rw [Complex.ofReal_sum]
  calc
    (∑ n ∈ Icc u v,
        ((‖finiteHermitianBlockCoefficient P a n‖ ^ 2 : ℝ) : ℂ)) =
      ∑ n ∈ Icc u v, ∑ p ∈ P, ∑ p' ∈ P,
        a p n * conj (a p' n) := by
      apply Finset.sum_congr rfl
      intro n hn
      exact finiteHermitianBlockCoefficient_norm_sq P a n
    _ = ∑ p ∈ P, ∑ p' ∈ P, ∑ n ∈ Icc u v,
        a p n * conj (a p' n) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.sum_comm]

private theorem summable_finsetSum
    {ι α : Type*} [AddCommMonoid α] [TopologicalSpace α]
    [T2Space α] [ContinuousAdd α]
    (P : Finset ι) (f : ι → ℤ → α)
    (hf : ∀ p ∈ P, Summable (f p)) :
    Summable fun n : ℤ ↦ ∑ p ∈ P, f p n := by
  classical
  induction P using Finset.induction_on with
  | empty =>
      simpa using! (summable_zero : Summable fun _n : ℤ ↦ (0 : α))
  | @insert p P hp ih =>
      have hpSum : Summable (f p) := hf p (Finset.mem_insert_self p P)
      have hrest : Summable fun n : ℤ ↦ ∑ q ∈ P, f q n :=
        ih (fun q hq ↦ hf q (Finset.mem_insert_of_mem hq))
      simpa only [Finset.sum_insert hp] using! hpSum.add hrest

theorem tsum_finiteHermitianBlockCoefficient_norm_sq
    (P : Finset ℕ) (a : ℕ → ℤ → ℂ)
    (hpair : ∀ p ∈ P, ∀ p' ∈ P,
      Summable fun n : ℤ ↦ a p n * conj (a p' n)) :
    (((∑' n : ℤ,
        ‖finiteHermitianBlockCoefficient P a n‖ ^ 2) : ℝ) : ℂ) =
      ∑ p ∈ P, ∑ p' ∈ P, ∑' n : ℤ,
        a p n * conj (a p' n) := by
  have hsump : ∀ p ∈ P, Summable fun n : ℤ ↦
      ∑ p' ∈ P, a p n * conj (a p' n) := by
    intro p hp
    exact summable_finsetSum P
      (fun p' n ↦ a p n * conj (a p' n)) (hpair p hp)
  have houter : Summable fun n : ℤ ↦
      ∑ p ∈ P, ∑ p' ∈ P, a p n * conj (a p' n) :=
    summable_finsetSum P
      (fun p n ↦ ∑ p' ∈ P, a p n * conj (a p' n)) hsump
  rw [Complex.ofReal_tsum]
  calc
    (∑' n : ℤ,
        ((‖finiteHermitianBlockCoefficient P a n‖ ^ 2 : ℝ) : ℂ)) =
      ∑' n : ℤ, ∑ p ∈ P, ∑ p' ∈ P,
        a p n * conj (a p' n) := by
      apply tsum_congr
      intro n
      exact finiteHermitianBlockCoefficient_norm_sq P a n
    _ = ∑ p ∈ P, ∑' n : ℤ, ∑ p' ∈ P,
        a p n * conj (a p' n) :=
      Summable.tsum_finsetSum hsump
    _ = ∑ p ∈ P, ∑ p' ∈ P, ∑' n : ℤ,
        a p n * conj (a p' n) := by
      apply Finset.sum_congr rfl
      intro p hp
      exact Summable.tsum_finsetSum (hpair p hp)

/-- Absolute summability of the squared block norm.  This is the
summability fact used when a finite family of blocks is assembled by
Tonelli; it follows from the same pairwise Hermitian summability as the
exact Parseval identity above. -/
theorem summable_finiteHermitianBlockCoefficient_norm_sq
    (P : Finset ℕ) (a : ℕ → ℤ → ℂ)
    (hpair : ∀ p ∈ P, ∀ p' ∈ P,
      Summable fun n : ℤ ↦ a p n * conj (a p' n)) :
    Summable fun n : ℤ ↦ ‖finiteHermitianBlockCoefficient P a n‖ ^ 2 := by
  have hsump : ∀ p ∈ P, Summable fun n : ℤ ↦
      ∑ p' ∈ P, a p n * conj (a p' n) := by
    intro p hp
    exact summable_finsetSum P
      (fun p' n ↦ a p n * conj (a p' n)) (hpair p hp)
  have houter : Summable fun n : ℤ ↦
      ∑ p ∈ P, ∑ p' ∈ P, a p n * conj (a p' n) :=
    summable_finsetSum P
      (fun p n ↦ ∑ p' ∈ P, a p n * conj (a p' n)) hsump
  apply Complex.summable_ofReal.mp
  apply houter.congr
  intro n
  exact (finiteHermitianBlockCoefficient_norm_sq P a n).symm

def fixedAwayRamanujanProfileTerm
    (R : ℕ → ℤ → ℂ) (p : ℕ) (n : ℤ) : ℂ :=
  (((1 / (p : ℝ) ^ 2 : ℝ) : ℂ) * ramanujanSum p (-n)) * R p n

theorem fixedAwayRamanujanProfileTerm_mul_conj
    (R : ℕ → ℤ → ℂ) (p p' : ℕ) (n : ℤ) :
    fixedAwayRamanujanProfileTerm R p n *
        conj (fixedAwayRamanujanProfileTerm R p' n) =
      ((1 / ((p : ℝ) ^ 2 * (p' : ℝ) ^ 2) : ℝ) : ℂ) *
        (ramanujanSum p n * conj (ramanujanSum p' n)) *
          (R p n * conj (R p' n)) := by
  unfold fixedAwayRamanujanProfileTerm
  simp only [map_mul, Complex.conj_ofReal, conj_ramanujanSum,
    ramanujanSum_even]
  push_cast
  ring

def fixedAwayRamanujanProfileBlock
    (P : Finset ℕ) (R : ℕ → ℤ → ℂ) (n : ℤ) : ℂ :=
  ∑ p ∈ P, fixedAwayRamanujanProfileTerm R p n

def fixedAwayProfilePair
    (R : ℕ → ℤ → ℂ) (p p' : ℕ) (n : ℤ) : ℂ :=
  R p n * conj (R p' n)

/-- Squared-energy summability for a literal finite Ramanujan profile
block, with all scaling and conjugation factors included. -/
theorem summable_fixedAwayRamanujanProfileBlock_norm_sq
    (P : Finset ℕ) (R : ℕ → ℤ → ℂ)
    (hpair : ∀ p ∈ P, ∀ p' ∈ P,
      Summable fun n : ℤ ↦
        hermitianRamanujanMultiplierTerm
          (fixedAwayProfilePair R p p') p p' n) :
    Summable fun n : ℤ ↦ ‖fixedAwayRamanujanProfileBlock P R n‖ ^ 2 := by
  change Summable fun n : ℤ ↦
    ‖finiteHermitianBlockCoefficient P
      (fixedAwayRamanujanProfileTerm R) n‖ ^ 2
  apply summable_finiteHermitianBlockCoefficient_norm_sq
  intro p hp p' hp'
  have hscaled := (hpair p hp p' hp').mul_left
    (((1 / ((p : ℝ) ^ 2 * (p' : ℝ) ^ 2) : ℝ) : ℂ))
  apply hscaled.congr
  intro n
  simpa only [hermitianRamanujanMultiplierTerm,
    fixedAwayProfilePair, mul_assoc] using!
      (fixedAwayRamanujanProfileTerm_mul_conj R p p' n).symm

theorem sum_fixedAwayRamanujanProfileBlock_norm_sq_Icc
    (P : Finset ℕ) (R : ℕ → ℤ → ℂ) (u v : ℤ) :
    (((∑ n ∈ Icc u v,
        ‖fixedAwayRamanujanProfileBlock P R n‖ ^ 2) : ℝ) : ℂ) =
      ∑ p ∈ P, ∑ p' ∈ P,
        ((1 / ((p : ℝ) ^ 2 * (p' : ℝ) ^ 2) : ℝ) : ℂ) *
          ∑ n ∈ Icc u v,
            hermitianRamanujanMultiplierTerm
              (fixedAwayProfilePair R p p') p p' n := by
  change (((∑ n ∈ Icc u v,
      ‖finiteHermitianBlockCoefficient P
        (fixedAwayRamanujanProfileTerm R) n‖ ^ 2) : ℝ) : ℂ) = _
  rw [sum_finiteHermitianBlockCoefficient_norm_sq_Icc]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro p' hp'
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [fixedAwayRamanujanProfileTerm_mul_conj]
  unfold hermitianRamanujanMultiplierTerm fixedAwayProfilePair
  ring

theorem tsum_fixedAwayRamanujanProfileBlock_norm_sq
    (P : Finset ℕ) (R : ℕ → ℤ → ℂ)
    (hpair : ∀ p ∈ P, ∀ p' ∈ P,
      Summable fun n : ℤ ↦
        hermitianRamanujanMultiplierTerm
          (fixedAwayProfilePair R p p') p p' n) :
    (((∑' n : ℤ,
        ‖fixedAwayRamanujanProfileBlock P R n‖ ^ 2) : ℝ) : ℂ) =
      ∑ p ∈ P, ∑ p' ∈ P,
        ((1 / ((p : ℝ) ^ 2 * (p' : ℝ) ^ 2) : ℝ) : ℂ) *
          ∑' n : ℤ,
            hermitianRamanujanMultiplierTerm
              (fixedAwayProfilePair R p p') p p' n := by
  have hactual : ∀ p ∈ P, ∀ p' ∈ P,
      Summable fun n : ℤ ↦
        fixedAwayRamanujanProfileTerm R p n *
          conj (fixedAwayRamanujanProfileTerm R p' n) := by
    intro p hp p' hp'
    have hscaled := (hpair p hp p' hp').mul_left
      (((1 / ((p : ℝ) ^ 2 * (p' : ℝ) ^ 2) : ℝ) : ℂ))
    apply hscaled.congr
    intro n
    simpa only [hermitianRamanujanMultiplierTerm,
      fixedAwayProfilePair, mul_assoc] using!
        (fixedAwayRamanujanProfileTerm_mul_conj R p p' n).symm
  change (((∑' n : ℤ,
      ‖finiteHermitianBlockCoefficient P
        (fixedAwayRamanujanProfileTerm R) n‖ ^ 2) : ℝ) : ℂ) = _
  rw [tsum_finiteHermitianBlockCoefficient_norm_sq P
    (fixedAwayRamanujanProfileTerm R) hactual]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro p' hp'
  calc
    (∑' n : ℤ,
        fixedAwayRamanujanProfileTerm R p n *
          conj (fixedAwayRamanujanProfileTerm R p' n)) =
      ∑' n : ℤ,
        (((1 / ((p : ℝ) ^ 2 * (p' : ℝ) ^ 2) : ℝ) : ℂ) *
          hermitianRamanujanMultiplierTerm
            (fixedAwayProfilePair R p p') p p' n) := by
      apply tsum_congr
      intro n
      simpa only [hermitianRamanujanMultiplierTerm,
        fixedAwayProfilePair, mul_assoc] using!
          fixedAwayRamanujanProfileTerm_mul_conj R p p' n
    _ = ((1 / ((p : ℝ) ^ 2 * (p' : ℝ) ^ 2) : ℝ) : ℂ) *
          ∑' n : ℤ,
            hermitianRamanujanMultiplierTerm
              (fixedAwayProfilePair R p p') p p' n := tsum_mul_left

/-! ## Exact separation of the exceptional, diagonal, and off-diagonal parts -/

theorem sum_pair_eq_diagonal_add_offDiagonal
    {Rng ι : Type*} [AddCommMonoid Rng] [DecidableEq ι]
    (P : Finset ι) (f : ι → ι → Rng) :
    (∑ p ∈ P, ∑ p' ∈ P, f p p') =
      (∑ p ∈ P, f p p) +
        ∑ p ∈ P, ∑ p' ∈ P.erase p, f p p' := by
  classical
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  calc
    (∑ p' ∈ P, f p p') =
        (∑ p' ∈ P.erase p, f p p') + f p p :=
      (Finset.sum_erase_add P (f p) hp).symm
    _ = f p p + ∑ p' ∈ P.erase p, f p p' := add_comm _ _

def fixedAwayProfilePairTsum
    (R : ℕ → ℤ → ℂ) (p p' : ℕ) : ℂ :=
  (((1 / ((p : ℝ) ^ 2 * (p' : ℝ) ^ 2) : ℝ) : ℂ) *
    ∑' n : ℤ,
      hermitianRamanujanMultiplierTerm
        (fixedAwayProfilePair R p p') p p' n)

theorem tsum_fixedAwayRamanujanProfileBlock_norm_sq_diagonal_offDiagonal
    (P : Finset ℕ) (R : ℕ → ℤ → ℂ)
    (hpair : ∀ p ∈ P, ∀ p' ∈ P,
      Summable fun n : ℤ ↦
        hermitianRamanujanMultiplierTerm
          (fixedAwayProfilePair R p p') p p' n) :
    (((∑' n : ℤ,
        ‖fixedAwayRamanujanProfileBlock P R n‖ ^ 2) : ℝ) : ℂ) =
      (∑ p ∈ P, fixedAwayProfilePairTsum R p p) +
        ∑ p ∈ P, ∑ p' ∈ P.erase p,
          fixedAwayProfilePairTsum R p p' := by
  rw [tsum_fixedAwayRamanujanProfileBlock_norm_sq P R hpair]
  exact sum_pair_eq_diagonal_add_offDiagonal P
    (fixedAwayProfilePairTsum R)

theorem fixedAwayRamanujanProfileTerm_one
    (R : ℕ → ℤ → ℂ) (n : ℤ) :
    fixedAwayRamanujanProfileTerm R 1 n = R 1 n := by
  simp [fixedAwayRamanujanProfileTerm, ramanujanSum_one]

theorem fixedAwayRamanujanProfileBlock_singleton_one
    (R : ℕ → ℤ → ℂ) (n : ℤ) :
    fixedAwayRamanujanProfileBlock {1} R n = R 1 n := by
  simp [fixedAwayRamanujanProfileBlock,
    fixedAwayRamanujanProfileTerm_one]

theorem tsum_norm_fixedAwayRamanujanProfileBlock_singleton_one_sq
    (R : ℕ → ℤ → ℂ) :
    (∑' n : ℤ,
      ‖fixedAwayRamanujanProfileBlock {1} R n‖ ^ 2) =
        ∑' n : ℤ, ‖R 1 n‖ ^ 2 := by
  apply tsum_congr
  intro n
  rw [fixedAwayRamanujanProfileBlock_singleton_one]

/-- Integer translation of a profile, as in the exceptional shifted mode
`Rχ(n - ℓN)` for `p = 1`. -/
def integerTranslatedProfile (a : ℤ) (f : ℤ → ℂ) (n : ℤ) : ℂ :=
  f (n - a)

theorem summable_norm_integerTranslatedProfile_sq_iff
    (a : ℤ) (f : ℤ → ℂ) :
    (Summable fun n : ℤ ↦ ‖integerTranslatedProfile a f n‖ ^ 2) ↔
      Summable fun n : ℤ ↦ ‖f n‖ ^ 2 := by
  simpa only [integerTranslatedProfile, Function.comp_apply] using!
    ((Equiv.subRight a).summable_iff
      (f := fun n : ℤ ↦ ‖f n‖ ^ 2))

theorem tsum_norm_integerTranslatedProfile_sq
    (a : ℤ) (f : ℤ → ℂ) :
    (∑' n : ℤ, ‖integerTranslatedProfile a f n‖ ^ 2) =
      ∑' n : ℤ, ‖f n‖ ^ 2 := by
  simpa only [integerTranslatedProfile] using!
    (Equiv.subRight a).tsum_eq (fun n : ℤ ↦ ‖f n‖ ^ 2)

end

end Erdos1002
