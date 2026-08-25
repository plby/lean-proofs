import ErdosProblems.Erdos67.MRT
import ErdosProblems.Erdos67.MRTFourPrimeBound
import ErdosProblems.Erdos67.MRTVinogradov
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.Order.Chebyshev

/-!
# Finite minor-arc reductions for the MRT short-interval estimate

This file continues the corrected Ramaré expansion in `MRT.lean` through the
elementary finite part of Section 3 of Matomäki--Radziwiłł--Tao,
*An averaged form of Chowla's conjecture* (arXiv:1503.05121v3).

The proved results below cover four steps used there:

* an exact decomposition of a prime window into disjoint dyadic blocks;
* the finite Hölder reduction from an `ℓ¹` sum to a fourth moment;
* the exact expansion of that fourth moment into prime quadruples; and
* the geometric-progression bound for the remaining cofactor sum.

The remaining sections package the upper-bound-sieve and Vinogradov-lemma
estimate in equation (3.3) of the cited paper.
-/

open scoped BigOperators ComplexConjugate
open Finset

namespace Erdos67

noncomputable section

/-! ## Disjoint dyadic blocks -/

/-- The half-open dyadic block `(2^j L, 2^(j+1) L]`. -/
def dyadicNatBlock (L j : ℕ) : Finset ℕ :=
  Finset.Ioc (2 ^ j * L) (2 ^ (j + 1) * L)

/-- The union of the first `J` dyadic blocks above `L`. -/
def dyadicNatWindow (L J : ℕ) : Finset ℕ :=
  Finset.Ioc L (2 ^ J * L)

@[simp]
theorem mem_dyadicNatBlock {L j n : ℕ} :
    n ∈ dyadicNatBlock L j ↔ 2 ^ j * L < n ∧ n ≤ 2 ^ (j + 1) * L := by
  simp [dyadicNatBlock]

@[simp]
theorem mem_dyadicNatWindow {L J n : ℕ} :
    n ∈ dyadicNatWindow L J ↔ L < n ∧ n ≤ 2 ^ J * L := by
  simp [dyadicNatWindow]

/-- One more dyadic block extends the window by one dyadic scale. -/
theorem dyadicNatWindow_succ (L J : ℕ) :
    dyadicNatWindow L (J + 1) =
      dyadicNatWindow L J ∪ dyadicNatBlock L J := by
  ext n
  simp only [mem_dyadicNatWindow, Finset.mem_union, mem_dyadicNatBlock]
  constructor
  · intro hn
    by_cases h : n ≤ 2 ^ J * L
    · exact Or.inl ⟨hn.1, h⟩
    · exact Or.inr ⟨by omega, hn.2⟩
  · rintro (hn | hn)
    · refine ⟨hn.1, hn.2.trans ?_⟩
      calc
        2 ^ J * L ≤ 2 * (2 ^ J * L) := by omega
        _ = 2 ^ (J + 1) * L := by simp [pow_succ]; ring
    · have hscale : L ≤ 2 ^ J * L := by
        have hpow : 0 < 2 ^ J := pow_pos (by omega) J
        exact Nat.le_mul_of_pos_left L hpow
      exact ⟨lt_of_le_of_lt hscale hn.1, hn.2⟩

/-- The old window and the new block are disjoint. -/
theorem disjoint_dyadicNatWindow_dyadicNatBlock (L J : ℕ) :
    Disjoint (dyadicNatWindow L J) (dyadicNatBlock L J) := by
  rw [Finset.disjoint_left]
  intro n hnWindow hnBlock
  rw [mem_dyadicNatWindow] at hnWindow
  rw [mem_dyadicNatBlock] at hnBlock
  omega

/-- Exact telescoping decomposition of a sum over a dyadic window. -/
theorem sum_dyadicNatWindow_eq_sum_blocks
    {R : Type*} [AddCommMonoid R] (L J : ℕ) (f : ℕ → R) :
    (∑ n ∈ dyadicNatWindow L J, f n) =
      ∑ j ∈ Finset.range J, ∑ n ∈ dyadicNatBlock L j, f n := by
  induction J with
  | zero => simp [dyadicNatWindow]
  | succ J ih =>
      rw [show J + 1 = Nat.succ J by omega,
        dyadicNatWindow_succ,
        Finset.sum_union (disjoint_dyadicNatWindow_dyadicNatBlock L J),
        Finset.sum_range_succ, ih]

/-- The primes in one half-open dyadic block. -/
def dyadicPrimeBlock (L j : ℕ) : Finset ℕ :=
  (dyadicNatBlock L j).filter Nat.Prime

/-- The primes in the first `J` dyadic blocks above `L`. -/
def dyadicPrimeWindow (L J : ℕ) : Finset ℕ :=
  (dyadicNatWindow L J).filter Nat.Prime

@[simp]
theorem mem_dyadicPrimeBlock {L j p : ℕ} :
    p ∈ dyadicPrimeBlock L j ↔
      p.Prime ∧ 2 ^ j * L < p ∧ p ≤ 2 ^ (j + 1) * L := by
  simp [dyadicPrimeBlock, and_comm]

@[simp]
theorem mem_dyadicPrimeWindow {L J p : ℕ} :
    p ∈ dyadicPrimeWindow L J ↔
      p.Prime ∧ L < p ∧ p ≤ 2 ^ J * L := by
  simp [dyadicPrimeWindow, and_comm]

theorem dyadicPrimeWindow_succ (L J : ℕ) :
    dyadicPrimeWindow L (J + 1) =
      dyadicPrimeWindow L J ∪ dyadicPrimeBlock L J := by
  unfold dyadicPrimeWindow dyadicPrimeBlock
  rw [dyadicNatWindow_succ, Finset.filter_union]

theorem disjoint_dyadicPrimeWindow_dyadicPrimeBlock (L J : ℕ) :
    Disjoint (dyadicPrimeWindow L J) (dyadicPrimeBlock L J) := by
  exact (disjoint_dyadicNatWindow_dyadicNatBlock L J).mono
    (Finset.filter_subset _ _) (Finset.filter_subset _ _)

/-- The paper's first dyadic prime block is contained in the larger prime set
used by the sieve representation bound. -/
theorem dyadicPrimeBlock_zero_subset_primesLE_two_mul (P : ℕ) :
    dyadicPrimeBlock P 0 ⊆ Nat.primesLE (2 * P) := by
  intro p hp
  have hp' := mem_dyadicPrimeBlock.mp hp
  rw [Nat.mem_primesLE]
  norm_num at hp'
  exact ⟨hp'.2.2, hp'.1⟩

/-- Prime version of the exact dyadic block decomposition. -/
theorem sum_dyadicPrimeWindow_eq_sum_blocks
    {R : Type*} [AddCommMonoid R] (L J : ℕ) (f : ℕ → R) :
    (∑ p ∈ dyadicPrimeWindow L J, f p) =
      ∑ j ∈ Finset.range J, ∑ p ∈ dyadicPrimeBlock L j, f p := by
  induction J with
  | zero => simp [dyadicPrimeWindow, dyadicNatWindow]
  | succ J ih =>
      rw [show J + 1 = Nat.succ J by omega,
        dyadicPrimeWindow_succ,
        Finset.sum_union (disjoint_dyadicPrimeWindow_dyadicPrimeBlock L J),
        Finset.sum_range_succ, ih]

/-! ## Finite Hölder and fourth-moment reduction -/

/-- The fourth-power instance of finite Hölder:
`(∑ a_i)^4 ≤ |s|^3 ∑ a_i^4` for nonnegative real coefficients. -/
theorem sum_pow_four_le_card_cube_mul_sum_pow_four
    {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) :
    (∑ i ∈ s, a i) ^ 4 ≤
      (s.card : ℝ) ^ 3 * ∑ i ∈ s, a i ^ 4 := by
  simpa using (pow_sum_le_card_mul_sum_pow ha 3)

/-- The root-free Hölder step used after the dyadic Ramaré rearrangement. -/
theorem sum_norm_pow_four_le_card_cube_mul_fourthMoment
    {ι : Type*} (s : Finset ι) (A : ι → ℂ) :
    (∑ i ∈ s, ‖A i‖) ^ 4 ≤
      (s.card : ℝ) ^ 3 * ∑ i ∈ s, ‖A i‖ ^ 4 := by
  exact sum_pow_four_le_card_cube_mul_sum_pow_four s (fun i ↦ ‖A i‖)
    (fun _ _ ↦ norm_nonneg _)

/-- The ordered set of four prime variables used in the fourth-moment expansion. -/
def primeQuadrupleSet (P : Finset ℕ) : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  (P ×ˢ P) ×ˢ (P ×ˢ P)

/-- The coefficient contributed by one ordered quadruple. -/
def fourthMomentCoefficient (a : ℕ → ℂ)
    (x : (ℕ × ℕ) × (ℕ × ℕ)) : ℂ :=
  a x.2.2 * conj (a x.2.1) * a x.1.2 * conj (a x.1.1)

/-- Pointwise exact expansion of a fourth power into ordered quadruples. -/
theorem norm_four_finset_sum_eq_primeQuadruple_sum
    (P : Finset ℕ) (a : ℕ → ℂ) :
    (‖∑ p ∈ P, a p‖ : ℂ) ^ 4 =
      ∑ x ∈ primeQuadrupleSet P, fourthMomentCoefficient a x := by
  classical
  have hnorm (z : ℂ) : (‖z‖ : ℂ) ^ 4 = z * conj z * z * conj z := by
    have hsq : ((‖z‖ : ℂ) ^ 2) = conj z * z := by
      rw [← Complex.ofReal_pow, Complex.sq_norm,
        Complex.normSq_eq_conj_mul_self]
    rw [show (4 : ℕ) = 2 * 2 by omega, pow_mul, hsq]
    ring
  rw [hnorm]
  unfold primeQuadrupleSet
  simp only [map_sum, Finset.sum_mul, Finset.mul_sum]
  simp_rw [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro p₁ hp₁
  apply Finset.sum_congr rfl
  intro p₂ hp₂
  apply Finset.sum_congr rfl
  intro p₃ hp₃
  apply Finset.sum_congr rfl
  intro p₄ hp₄
  unfold fourthMomentCoefficient
  ring_nf

/-- Summing the pointwise expansion commutes the cofactor and prime-quadruple sums.
This is the finite algebraic content of the display following (3.3) in the
MRT minor-arc proof. -/
theorem fourthMoment_eq_sum_primeQuadruples
    (M P : Finset ℕ) (a : ℕ → ℕ → ℂ) :
    (((∑ m ∈ M, ‖∑ p ∈ P, a m p‖ ^ 4 : ℝ) : ℝ) : ℂ) =
      ∑ x ∈ primeQuadrupleSet P,
        ∑ m ∈ M, fourthMomentCoefficient (a m) x := by
  push_cast
  simp_rw [norm_four_finset_sum_eq_primeQuadruple_sum]
  rw [Finset.sum_comm]

/-! ## Geometric sums -/

theorem additivePhase_add (α : ℝ) (m n : ℕ) :
    additivePhase α (m + n) = additivePhase α m * additivePhase α n := by
  rw [additivePhase, additivePhase, additivePhase, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem conj_additivePhase (α : ℝ) (n : ℕ) :
    conj (additivePhase α n) = additivePhase (-α) n := by
  rw [additivePhase, additivePhase, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_natCast, map_ofNat, Complex.conj_ofReal,
    Complex.conj_I]
  push_cast
  ring_nf

theorem additivePhase_mul_swap (α : ℝ) (m n : ℕ) :
    additivePhase α (m * n) = additivePhase (α * n) m := by
  unfold additivePhase
  congr 1
  push_cast
  ring

theorem additivePhase_eq_pow (α : ℝ) (n : ℕ) :
    additivePhase α n = additivePhase α 1 ^ n := by
  induction n with
  | zero => simp [additivePhase]
  | succ n ih =>
      rw [pow_succ, ← ih, ← additivePhase_add]

/-- A geometric progression of additive phases on an interval of `N` consecutive integers. -/
def geometricPhaseSum (α : ℝ) (L N : ℕ) : ℂ :=
  ∑ j ∈ Finset.range N, additivePhase α (L + j)

theorem geometricPhaseSum_eq_mul_geom (α : ℝ) (L N : ℕ) :
    geometricPhaseSum α L N =
      additivePhase α L * ∑ j ∈ Finset.range N, additivePhase α 1 ^ j := by
  unfold geometricPhaseSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [additivePhase_add, additivePhase_eq_pow α j]

/-- Exact quotient formula for a nonconstant phase. -/
theorem geometricPhaseSum_eq_div (α : ℝ) (L N : ℕ)
    (hα : additivePhase α 1 ≠ 1) :
    geometricPhaseSum α L N =
      additivePhase α L *
        ((additivePhase α 1 ^ N - 1) / (additivePhase α 1 - 1)) := by
  rw [geometricPhaseSum_eq_mul_geom, geom_sum_eq hα]

/-- Trivial length bound for a consecutive geometric progression. -/
theorem norm_geometricPhaseSum_le_length (α : ℝ) (L N : ℕ) :
    ‖geometricPhaseSum α L N‖ ≤ N := by
  unfold geometricPhaseSum
  calc
    ‖∑ j ∈ Finset.range N, additivePhase α (L + j)‖ ≤
        ∑ j ∈ Finset.range N, ‖additivePhase α (L + j)‖ :=
      norm_sum_le _ _
    _ = N := by simp [norm_additivePhase]

/-- Cancellation bound obtained by summing the geometric progression exactly. -/
theorem norm_geometricPhaseSum_le_two_div
    (α : ℝ) (L N : ℕ) (hα : additivePhase α 1 ≠ 1) :
    ‖geometricPhaseSum α L N‖ ≤
      2 / ‖additivePhase α 1 - 1‖ := by
  rw [geometricPhaseSum_eq_div α L N hα, norm_mul, norm_additivePhase,
    one_mul, norm_div]
  have hden : 0 < ‖additivePhase α 1 - 1‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr hα)
  have hnum : ‖additivePhase α 1 ^ N - 1‖ ≤ 2 := by
    calc
      ‖additivePhase α 1 ^ N - 1‖ ≤
          ‖additivePhase α 1 ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, norm_additivePhase]; norm_num
  exact (div_le_div_iff_of_pos_right hden).2 hnum

/-- The usual `min(length, reciprocal phase separation)` geometric-sum bound. -/
theorem norm_geometricPhaseSum_le_min
    (α : ℝ) (L N : ℕ) (hα : additivePhase α 1 ≠ 1) :
    ‖geometricPhaseSum α L N‖ ≤
      min (N : ℝ) (2 / ‖additivePhase α 1 - 1‖) := by
  exact le_min (norm_geometricPhaseSum_le_length α L N)
    (norm_geometricPhaseSum_le_two_div α L N hα)

/-! ## The phase carried by one expanded prime quadruple -/

/-- The signed prime combination occurring after expansion of the fourth moment. -/
def primeQuadrupleDifference (x : (ℕ × ℕ) × (ℕ × ℕ)) : ℤ :=
  (x.1.2 : ℤ) + x.2.2 - x.1.1 - x.2.1

/-- The four additive phases in one expanded term collapse to the phase whose
frequency is the signed prime combination. -/
theorem primeQuadruple_phase_factorization
    (α : ℝ) (m : ℕ) (x : (ℕ × ℕ) × (ℕ × ℕ)) :
    additivePhase α (m * x.2.2) * conj (additivePhase α (m * x.2.1)) *
        additivePhase α (m * x.1.2) * conj (additivePhase α (m * x.1.1)) =
      additivePhase (α * (primeQuadrupleDifference x : ℝ)) m := by
  rw [conj_additivePhase, conj_additivePhase]
  unfold additivePhase primeQuadrupleDifference
  rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Paper-specific specialization of the generic fourth-moment coefficient:
the multiplicative coefficients separate from the cofactor geometric phase. -/
theorem fourthMomentCoefficient_phase_factorization
    (b : ℕ → ℂ) (α : ℝ) (m : ℕ)
    (x : (ℕ × ℕ) × (ℕ × ℕ)) :
    fourthMomentCoefficient
        (fun p ↦ b p * additivePhase α (m * p)) x =
      fourthMomentCoefficient b x *
        additivePhase (α * (primeQuadrupleDifference x : ℝ)) m := by
  calc
    fourthMomentCoefficient
          (fun p ↦ b p * additivePhase α (m * p)) x =
        fourthMomentCoefficient b x *
          (additivePhase α (m * x.2.2) *
            conj (additivePhase α (m * x.2.1)) *
            additivePhase α (m * x.1.2) *
            conj (additivePhase α (m * x.1.1))) := by
      unfold fourthMomentCoefficient
      simp only [map_mul]
      ring
    _ = _ := by rw [primeQuadruple_phase_factorization]

/-- After summing the cofactor through a consecutive interval, each prime
quadruple contributes one geometric progression. -/
theorem sum_fourthMomentCoefficient_phase_eq_geometricPhaseSum
    (b : ℕ → ℂ) (α : ℝ) (L N : ℕ)
    (x : (ℕ × ℕ) × (ℕ × ℕ)) :
    (∑ m ∈ Finset.range N,
        fourthMomentCoefficient
          (fun p ↦ b p * additivePhase α ((L + m) * p)) x) =
      fourthMomentCoefficient b x *
        geometricPhaseSum
          (α * (primeQuadrupleDifference x : ℝ)) L N := by
  rw [geometricPhaseSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  exact fourthMomentCoefficient_phase_factorization b α (L + m) x

/-- The complete exact fourth-moment expansion for a prime polynomial sampled
on a consecutive cofactor interval. -/
theorem fourthMoment_primePhase_eq_primeQuadruple_geometric
    (P : Finset ℕ) (b : ℕ → ℂ) (α : ℝ) (L N : ℕ) :
    (((∑ m ∈ Finset.range N,
        ‖∑ p ∈ P, b p * additivePhase α ((L + m) * p)‖ ^ 4 : ℝ) : ℝ) : ℂ) =
      ∑ x ∈ primeQuadrupleSet P,
        fourthMomentCoefficient b x *
          geometricPhaseSum
            (α * (primeQuadrupleDifference x : ℝ)) L N := by
  rw [fourthMoment_eq_sum_primeQuadruples]
  apply Finset.sum_congr rfl
  intro x hx
  exact sum_fourthMomentCoefficient_phase_eq_geometricPhaseSum b α L N x

/-- A total geometric majorant, including the integral-phase case. -/
def geometricPhaseMajorant (α : ℝ) (N : ℕ) : ℝ :=
  if additivePhase α 1 = 1 then N
  else min (N : ℝ) (2 / ‖additivePhase α 1 - 1‖)

theorem geometricPhaseMajorant_nonneg (α : ℝ) (N : ℕ) :
    0 ≤ geometricPhaseMajorant α N := by
  unfold geometricPhaseMajorant
  split_ifs
  · positivity
  · exact le_min (by positivity) (div_nonneg (by positivity) (norm_nonneg _))

theorem norm_geometricPhaseSum_le_majorant (α : ℝ) (L N : ℕ) :
    ‖geometricPhaseSum α L N‖ ≤ geometricPhaseMajorant α N := by
  unfold geometricPhaseMajorant
  split_ifs with hα
  · exact norm_geometricPhaseSum_le_length α L N
  · exact norm_geometricPhaseSum_le_min α L N hα

/-- Triangle inequality after the exact expansion: all remaining cancellation
is localized in the one-dimensional geometric majorants. -/
theorem fourthMoment_primePhase_le_primeQuadruple_majorants
    (P : Finset ℕ) (b : ℕ → ℂ) (α : ℝ) (L N : ℕ) :
    (∑ m ∈ Finset.range N,
        ‖∑ p ∈ P, b p * additivePhase α ((L + m) * p)‖ ^ 4 : ℝ) ≤
      ∑ x ∈ primeQuadrupleSet P,
        ‖fourthMomentCoefficient b x‖ *
          geometricPhaseMajorant
            (α * (primeQuadrupleDifference x : ℝ)) N := by
  let M : ℝ := ∑ m ∈ Finset.range N,
    ‖∑ p ∈ P, b p * additivePhase α ((L + m) * p)‖ ^ 4
  have hM : 0 ≤ M := Finset.sum_nonneg fun _ _ ↦ by positivity
  have hexact := fourthMoment_primePhase_eq_primeQuadruple_geometric P b α L N
  change M ≤ _
  calc
    M = ‖(M : ℂ)‖ := by simp [Real.norm_eq_abs, abs_of_nonneg hM]
    _ = ‖∑ x ∈ primeQuadrupleSet P,
        fourthMomentCoefficient b x *
          geometricPhaseSum
            (α * (primeQuadrupleDifference x : ℝ)) L N‖ := by rw [hexact]
    _ ≤ ∑ x ∈ primeQuadrupleSet P,
        ‖fourthMomentCoefficient b x *
          geometricPhaseSum
            (α * (primeQuadrupleDifference x : ℝ)) L N‖ :=
      norm_sum_le _ _
    _ = ∑ x ∈ primeQuadrupleSet P,
        ‖fourthMomentCoefficient b x‖ *
          ‖geometricPhaseSum
            (α * (primeQuadrupleDifference x : ℝ)) L N‖ := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [norm_mul]
    _ ≤ ∑ x ∈ primeQuadrupleSet P,
        ‖fourthMomentCoefficient b x‖ *
          geometricPhaseMajorant
            (α * (primeQuadrupleDifference x : ℝ)) N := by
      apply Finset.sum_le_sum
      intro x hx
      exact mul_le_mul_of_nonneg_left
        (norm_geometricPhaseSum_le_majorant
          (α * (primeQuadrupleDifference x : ℝ)) L N)
        (norm_nonneg _)

/-! ## The remaining analytic estimate -/

/-- Distance to the nearest integer. -/
def distanceToNearestInteger (x : ℝ) : ℝ :=
  Erdos69.MinorArc.nearestIntDist x

theorem distanceToNearestInteger_neg (x : ℝ) :
    distanceToNearestInteger (-x) = distanceToNearestInteger x := by
  unfold distanceToNearestInteger Erdos69.MinorArc.nearestIntDist
  rw [abs_sub_round_eq_min, abs_sub_round_eq_min]
  by_cases hx : Int.fract x = 0
  · have hnx : Int.fract (-x) = 0 := Int.fract_neg_eq_zero.mpr hx
    rw [hx, hnx]
  · rw [Int.fract_neg hx]
    ring_nf
    rw [min_comm]

/-- The geometric-series majorant in equation (3.3).  At an integral phase the
reciprocal term is interpreted as `+∞`, so the minimum equals the length cutoff. -/
def vinogradovWeight (H P : ℕ) (x : ℝ) : ℝ :=
  Erdos69.MinorArc.cappedInvDist ((H : ℝ) / P) x

theorem vinogradovWeight_neg (H P : ℕ) (x : ℝ) :
    vinogradovWeight H P (-x) = vinogradovWeight H P x := by
  unfold vinogradovWeight Erdos69.MinorArc.cappedInvDist
  rw [show Erdos69.MinorArc.nearestIntDist (-x) =
      Erdos69.MinorArc.nearestIntDist x by
    exact distanceToNearestInteger_neg x]

/-- The minor-arc weight of a signed frequency depends only on its natural
absolute value. -/
theorem vinogradovWeight_natAbs (H P : ℕ) (α : ℝ) (d : ℤ) :
    vinogradovWeight H P (((d.natAbs : ℕ) : ℝ) * α) =
      vinogradovWeight H P ((d : ℝ) * α) := by
  by_cases hd : 0 ≤ d
  · have hcast : (((d.natAbs : ℕ) : ℝ)) = (d : ℝ) := by
      rw [← Int.cast_natCast]
      exact_mod_cast Int.natAbs_of_nonneg hd
    rw [hcast]
  · have hneg : 0 ≤ -d := by omega
    have hcast : (((d.natAbs : ℕ) : ℝ)) = -(d : ℝ) := by
      have hi : ((d.natAbs : ℕ) : ℤ) = -d := by
        rw [← Int.natAbs_neg]
        exact Int.natAbs_of_nonneg hneg
      rw [← Int.cast_natCast]
      exact_mod_cast hi
    rw [hcast, neg_mul, vinogradovWeight_neg]

/-- The prime-quadruple sum on the left side of MRT equation (3.3). -/
def minorArcPrimeQuadrupleMass (H P : ℕ) (α : ℝ) : ℝ :=
  let primes := dyadicPrimeBlock P 0
  ∑ x ∈ primeQuadrupleSet primes,
    vinogradovWeight H P
      ((primeQuadrupleDifference x : ℝ) * α)

/-- A difference of two two-prime sums from `(P,2P]` has magnitude at most
`2P`. -/
theorem primeQuadrupleDifference_natAbs_le_two_mul
    {P : ℕ} {x : (ℕ × ℕ) × (ℕ × ℕ)}
    (hx : x ∈ primeQuadrupleSet (dyadicPrimeBlock P 0)) :
    (primeQuadrupleDifference x).natAbs ≤ 2 * P := by
  unfold primeQuadrupleSet at hx
  simp only [Finset.mem_product] at hx
  have h₁₁ := (mem_dyadicPrimeBlock.mp hx.1.1).2
  have h₁₂ := (mem_dyadicPrimeBlock.mp hx.1.2).2
  have h₂₁ := (mem_dyadicPrimeBlock.mp hx.2.1).2
  have h₂₂ := (mem_dyadicPrimeBlock.mp hx.2.2).2
  unfold primeQuadrupleDifference
  norm_num at h₁₁ h₁₂ h₂₁ h₂₂
  omega

/-- Prime quadruples in the dyadic block with a prescribed absolute
difference. -/
def primeQuadrupleAbsoluteDifferenceFiber (P n : ℕ) :
    Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  (primeQuadrupleSet (dyadicPrimeBlock P 0)).filter fun x ↦
    (primeQuadrupleDifference x).natAbs = n

/-- Prime quadruples in the dyadic block with a prescribed signed
difference. -/
def primeQuadrupleDifferenceFiber (P : ℕ) (d : ℤ) :
    Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  (primeQuadrupleSet (dyadicPrimeBlock P 0)).filter fun x ↦
    primeQuadrupleDifference x = d

/-- The same signed-difference fiber over an arbitrary finite prime set. -/
def primeQuadrupleDifferenceFiberOn (A : Finset ℕ) (d : ℤ) :
    Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  (primeQuadrupleSet A).filter fun x ↦ primeQuadrupleDifference x = d

theorem primeQuadrupleDifferenceFiber_eq_on (P : ℕ) (d : ℤ) :
    primeQuadrupleDifferenceFiber P d =
      primeQuadrupleDifferenceFiberOn (dyadicPrimeBlock P 0) d := rfl

theorem primeQuadrupleDifferenceFiberOn_eq_fourPrimeDifferenceFiber
    (A : Finset ℕ) (d : ℤ) :
    primeQuadrupleDifferenceFiberOn A d =
      fourPrimeDifferenceFiber A d := rfl

theorem primeQuadrupleDifferenceFiberOn_mono
    {A B : Finset ℕ} (hAB : A ⊆ B) (d : ℤ) :
    primeQuadrupleDifferenceFiberOn A d ⊆
      primeQuadrupleDifferenceFiberOn B d := by
  intro x hx
  simp only [primeQuadrupleDifferenceFiberOn, Finset.mem_filter,
    primeQuadrupleSet, Finset.mem_product] at hx ⊢
  exact ⟨⟨⟨hAB hx.1.1.1, hAB hx.1.1.2⟩,
    hAB hx.1.2.1, hAB hx.1.2.2⟩, hx.2⟩

/-- Consequently the broad `primesLE (2P)` sieve fiber dominates the actual
dyadic fiber occurring in the minor-arc mass. -/
theorem card_primeQuadrupleDifferenceFiber_le_primesLE
    (P : ℕ) (d : ℤ) :
    (primeQuadrupleDifferenceFiber P d).card ≤
      (primeQuadrupleDifferenceFiberOn (Nat.primesLE (2 * P)) d).card := by
  rw [primeQuadrupleDifferenceFiber_eq_on]
  exact Finset.card_le_card
    (primeQuadrupleDifferenceFiberOn_mono
      (dyadicPrimeBlock_zero_subset_primesLE_two_mul P) d)

/-- A crude bound used to absorb the finitely many scales preceding an
eventual sieve estimate. -/
theorem card_dyadicPrimeBlock_zero_le (P : ℕ) :
    (dyadicPrimeBlock P 0).card ≤ 2 * P + 1 := by
  calc
    (dyadicPrimeBlock P 0).card ≤ (Finset.range (2 * P + 1)).card := by
      apply Finset.card_le_card
      intro p hp
      rw [Finset.mem_range]
      have hp' := (mem_dyadicPrimeBlock.mp hp).2.2
      norm_num at hp'
      omega
    _ = 2 * P + 1 := by simp

theorem card_primeQuadrupleDifferenceFiber_le_crude
    (P : ℕ) (d : ℤ) :
    (primeQuadrupleDifferenceFiber P d).card ≤ (2 * P + 1) ^ 4 := by
  calc
    (primeQuadrupleDifferenceFiber P d).card ≤
        (primeQuadrupleSet (dyadicPrimeBlock P 0)).card :=
      Finset.card_filter_le _ _
    _ = (dyadicPrimeBlock P 0).card ^ 4 := by
      simp only [primeQuadrupleSet, Finset.card_product]
      ring
    _ ≤ (2 * P + 1) ^ 4 :=
      Nat.pow_le_pow_left (card_dyadicPrimeBlock_zero_le P) 4

theorem primeQuadrupleAbsoluteDifferenceFiber_subset_signed_union
    (P n : ℕ) :
    primeQuadrupleAbsoluteDifferenceFiber P n ⊆
      primeQuadrupleDifferenceFiber P (n : ℤ) ∪
        primeQuadrupleDifferenceFiber P (-(n : ℤ)) := by
  intro x hx
  simp only [primeQuadrupleAbsoluteDifferenceFiber,
    primeQuadrupleDifferenceFiber, Finset.mem_filter,
    Finset.mem_union] at hx ⊢
  have habs := hx.2
  by_cases hd : 0 ≤ primeQuadrupleDifference x
  · left
    refine ⟨hx.1, ?_⟩
    have hi := Int.natAbs_of_nonneg hd
    omega
  · right
    refine ⟨hx.1, ?_⟩
    have hneg : 0 ≤ -primeQuadrupleDifference x := by omega
    have hi : ((primeQuadrupleDifference x).natAbs : ℤ) =
        -primeQuadrupleDifference x := by
      rw [← Int.natAbs_neg]
      exact Int.natAbs_of_nonneg hneg
    omega

theorem card_primeQuadrupleAbsoluteDifferenceFiber_le_signed
    (P n : ℕ) :
    (primeQuadrupleAbsoluteDifferenceFiber P n).card ≤
      (primeQuadrupleDifferenceFiber P (n : ℤ)).card +
        (primeQuadrupleDifferenceFiber P (-(n : ℤ))).card := by
  exact (Finset.card_le_card
    (primeQuadrupleAbsoluteDifferenceFiber_subset_signed_union P n)).trans
      (Finset.card_union_le _ _)

theorem card_primeQuadrupleAbsoluteDifferenceFiber_le_two_mul
    (P n : ℕ) (R : ℝ)
    (hfiber : ∀ d : ℤ,
      ((primeQuadrupleDifferenceFiber P d).card : ℝ) ≤ R) :
    ((primeQuadrupleAbsoluteDifferenceFiber P n).card : ℝ) ≤ 2 * R := by
  have hcard := card_primeQuadrupleAbsoluteDifferenceFiber_le_signed P n
  have hcardR :
      ((primeQuadrupleAbsoluteDifferenceFiber P n).card : ℝ) ≤
        ((primeQuadrupleDifferenceFiber P (n : ℤ)).card : ℝ) +
          ((primeQuadrupleDifferenceFiber P (-(n : ℤ))).card : ℝ) := by
    exact_mod_cast hcard
  linarith [hfiber (n : ℤ), hfiber (-(n : ℤ))]

theorem vinogradovWeight_nonneg (H P : ℕ) (x : ℝ) :
    0 ≤ vinogradovWeight H P x := by
  exact Erdos69.MinorArc.cappedInvDist_nonneg (by positivity) x

/-- Exact regrouping of the quadruple mass by the natural absolute value of
the signed difference. -/
theorem minorArcPrimeQuadrupleMass_eq_sum_absoluteFibers
    (H P : ℕ) (α : ℝ) :
    minorArcPrimeQuadrupleMass H P α =
      ∑ n ∈ Finset.range (2 * P + 1),
        ((primeQuadrupleAbsoluteDifferenceFiber P n).card : ℝ) *
          vinogradovWeight H P ((n : ℝ) * α) := by
  classical
  let Q := primeQuadrupleSet (dyadicPrimeBlock P 0)
  let g : ((ℕ × ℕ) × (ℕ × ℕ)) → ℕ := fun x ↦
    (primeQuadrupleDifference x).natAbs
  have hmaps : ∀ x ∈ Q, g x ∈ Finset.range (2 * P + 1) := by
    intro x hx
    exact Finset.mem_range.mpr
      (Nat.lt_succ_of_le (primeQuadrupleDifference_natAbs_le_two_mul hx))
  calc
    minorArcPrimeQuadrupleMass H P α =
        ∑ x ∈ Q, vinogradovWeight H P ((g x : ℝ) * α) := by
      unfold minorArcPrimeQuadrupleMass
      apply Finset.sum_congr rfl
      intro x hx
      exact (vinogradovWeight_natAbs H P α
        (primeQuadrupleDifference x)).symm
    _ = ∑ n ∈ Finset.range (2 * P + 1),
        ∑ x ∈ Q with g x = n,
          vinogradovWeight H P ((n : ℝ) * α) := by
      exact (Finset.sum_fiberwise_of_maps_to' hmaps
        (fun n ↦ vinogradovWeight H P ((n : ℝ) * α))).symm
    _ = ∑ n ∈ Finset.range (2 * P + 1),
        ((primeQuadrupleAbsoluteDifferenceFiber P n).card : ℝ) *
          vinogradovWeight H P ((n : ℝ) * α) := by
      apply Finset.sum_congr rfl
      intro n hn
      simp only [Finset.sum_const, nsmul_eq_mul]
      congr 1

/-- A uniform estimate for the absolute-difference fibers converts directly
to the weighted prime-quadruple mass. -/
theorem minorArcPrimeQuadrupleMass_le_of_fiber_bound
    (H P : ℕ) (α R : ℝ) (_hR : 0 ≤ R)
    (hfiber : ∀ n ≤ 2 * P,
      ((primeQuadrupleAbsoluteDifferenceFiber P n).card : ℝ) ≤ R) :
    minorArcPrimeQuadrupleMass H P α ≤
      R * ∑ n ∈ Finset.range (2 * P + 1),
        vinogradovWeight H P ((n : ℝ) * α) := by
  rw [minorArcPrimeQuadrupleMass_eq_sum_absoluteFibers]
  calc
    (∑ n ∈ Finset.range (2 * P + 1),
        ((primeQuadrupleAbsoluteDifferenceFiber P n).card : ℝ) *
          vinogradovWeight H P ((n : ℝ) * α)) ≤
        ∑ n ∈ Finset.range (2 * P + 1),
          R * vinogradovWeight H P ((n : ℝ) * α) := by
      apply Finset.sum_le_sum
      intro n hn
      apply mul_le_mul_of_nonneg_right
      · exact hfiber n (Nat.le_of_lt_succ (Finset.mem_range.mp hn))
      · exact vinogradovWeight_nonneg H P _
    _ = R * ∑ n ∈ Finset.range (2 * P + 1),
        vinogradovWeight H P ((n : ℝ) * α) := by rw [Finset.mul_sum]

/-- Signed-numerator form of the finite Vinogradov lemma.  A negative
numerator is handled by replacing `α` with `-α`; the capped nearest-integer
weight is even. -/
theorem vinogradovWeight_two_mul_le_minor_arc_int
    (H W P q : ℕ) (a : ℤ) (α : ℝ)
    (hW : 2 ≤ W) (hWq : W ≤ q) (hqH : q ≤ H / W)
    (hPlo : W ^ 200 ≤ P) (hPhi : P ≤ H / W ^ 3)
    (ha : a.natAbs.Coprime q)
    (hα : |α - (a : ℝ) / q| ≤ (W : ℝ) / ((H : ℝ) * q)) :
    (∑ n ∈ Finset.range (2 * P + 1),
        vinogradovWeight H P ((n : ℝ) * α)) ≤
      100 * Real.log H * ((H : ℝ) / W) := by
  by_cases ha0 : 0 ≤ a
  · have hcast : ((a.natAbs : ℕ) : ℝ) = (a : ℝ) := by
      rw [← Int.cast_natCast]
      exact_mod_cast Int.natAbs_of_nonneg ha0
    have hv := MRTVinogradov.cappedInvDist_two_mul_le_minor_arc
      H W P q a.natAbs α hW hWq hqH hPlo hPhi ha
      (by simpa only [hcast] using hα)
    simpa only [vinogradovWeight, mul_comm] using hv
  · have hneg : 0 ≤ -a := by omega
    have hcast : ((a.natAbs : ℕ) : ℝ) = -(a : ℝ) := by
      have hi : ((a.natAbs : ℕ) : ℤ) = -a := by
        rw [← Int.natAbs_neg]
        exact Int.natAbs_of_nonneg hneg
      rw [← Int.cast_natCast]
      exact_mod_cast hi
    have hαneg : |-α - ((a.natAbs : ℕ) : ℝ) / q| ≤
        (W : ℝ) / ((H : ℝ) * q) := by
      rw [hcast]
      rw [show -α - (-(a : ℝ)) / (q : ℝ) =
          -(α - (a : ℝ) / (q : ℝ)) by ring, abs_neg]
      exact hα
    have hv := MRTVinogradov.cappedInvDist_two_mul_le_minor_arc
      H W P q a.natAbs (-α) hW hWq hqH hPlo hPhi ha hαneg
    calc
      (∑ n ∈ Finset.range (2 * P + 1),
          vinogradovWeight H P ((n : ℝ) * α)) =
          ∑ n ∈ Finset.range (2 * P + 1),
            vinogradovWeight H P ((n : ℝ) * (-α)) := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [show (n : ℝ) * (-α) = -((n : ℝ) * α) by ring,
          vinogradovWeight_neg]
      _ ≤ 100 * Real.log H * ((H : ℝ) / W) := by
        simpa only [vinogradovWeight, mul_comm] using hv

/-- Signed-numerator, floor-safe version with the exact Dirichlet endpoint
`q ≤ H / W + 1`. -/
theorem vinogradovWeight_two_mul_le_minor_arc_int_succ
    (H W P q : ℕ) (a : ℤ) (α : ℝ)
    (hW : 2 ≤ W) (hWq : W ≤ q) (hqH : q ≤ H / W + 1)
    (hPlo : W ^ 200 ≤ P) (hPhi : P ≤ H / W ^ 3)
    (ha : a.natAbs.Coprime q)
    (hα : |α - (a : ℝ) / q| ≤ (W : ℝ) / ((H : ℝ) * q)) :
    (∑ n ∈ Finset.range (2 * P + 1),
        vinogradovWeight H P ((n : ℝ) * α)) ≤
      100 * Real.log H * ((H : ℝ) / W) := by
  by_cases ha0 : 0 ≤ a
  · have hcast : ((a.natAbs : ℕ) : ℝ) = (a : ℝ) := by
      rw [← Int.cast_natCast]
      exact_mod_cast Int.natAbs_of_nonneg ha0
    have hv := MRTVinogradov.cappedInvDist_two_mul_le_minor_arc_succ
      H W P q a.natAbs α hW hWq hqH hPlo hPhi ha
      (by simpa only [hcast] using hα)
    simpa only [vinogradovWeight, mul_comm] using hv
  · have hneg : 0 ≤ -a := by omega
    have hcast : ((a.natAbs : ℕ) : ℝ) = -(a : ℝ) := by
      have hi : ((a.natAbs : ℕ) : ℤ) = -a := by
        rw [← Int.natAbs_neg]
        exact Int.natAbs_of_nonneg hneg
      rw [← Int.cast_natCast]
      exact_mod_cast hi
    have hαneg : |-α - ((a.natAbs : ℕ) : ℝ) / q| ≤
        (W : ℝ) / ((H : ℝ) * q) := by
      rw [hcast]
      rw [show -α - (-(a : ℝ)) / (q : ℝ) =
          -(α - (a : ℝ) / (q : ℝ)) by ring, abs_neg]
      exact hα
    have hv := MRTVinogradov.cappedInvDist_two_mul_le_minor_arc_succ
      H W P q a.natAbs (-α) hW hWq hqH hPlo hPhi ha hαneg
    calc
      (∑ n ∈ Finset.range (2 * P + 1),
          vinogradovWeight H P ((n : ℝ) * α)) =
          ∑ n ∈ Finset.range (2 * P + 1),
            vinogradovWeight H P ((n : ℝ) * (-α)) := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [show (n : ℝ) * (-α) = -((n : ℝ) * α) by ring,
          vinogradovWeight_neg]
      _ ≤ 100 * Real.log H * ((H : ℝ) / W) := by
        simpa only [vinogradovWeight, mul_comm] using hv

/-- Final equation-(3.3) assembly when the sieve estimate is stated directly
for absolute-difference fibers. -/
theorem minorArcPrimeQuadrupleMass_le_of_absoluteFiberEstimate_at
    (C : ℝ) (hC : 0 < C)
    (H W P q : ℕ)
    (hfiber : ∀ n : ℕ,
      ((primeQuadrupleAbsoluteDifferenceFiber P n).card : ℝ) ≤
        C * (P : ℝ) ^ 3 / Real.log P ^ 4)
    (a : ℤ) (α : ℝ)
    (hW : 2 ≤ W) (hWq : W ≤ q) (hqH : q ≤ H / W)
    (hPlo : W ^ 200 ≤ P) (hPhi : P ≤ H / W ^ 3)
    (ha : a.natAbs.Coprime q)
    (hα : |α - (a : ℝ) / q| ≤ (W : ℝ) / ((H : ℝ) * q)) :
    minorArcPrimeQuadrupleMass H P α ≤
      (100 * C) * Real.log H * (H : ℝ) * (P : ℝ) ^ 3 /
        ((W : ℝ) * Real.log P ^ 4) := by
  have hPtwo : 2 ≤ P := by
    have hpow : 2 ^ 200 ≤ W ^ 200 := Nat.pow_le_pow_left hW 200
    omega
  have hlogP : 0 < Real.log (P : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < P by omega))
  let R : ℝ := C * (P : ℝ) ^ 3 / Real.log P ^ 4
  have hR : 0 ≤ R := by
    dsimp [R]
    positivity
  have hmass := minorArcPrimeQuadrupleMass_le_of_fiber_bound
    H P α R hR (fun n hn ↦ hfiber n)
  have hvino := vinogradovWeight_two_mul_le_minor_arc_int
    H W P q a α hW hWq hqH hPlo hPhi ha hα
  calc
    minorArcPrimeQuadrupleMass H P α ≤
        R * ∑ n ∈ Finset.range (2 * P + 1),
          vinogradovWeight H P ((n : ℝ) * α) := hmass
    _ ≤ R * (100 * Real.log H * ((H : ℝ) / W)) :=
      mul_le_mul_of_nonneg_left hvino hR
    _ = (100 * C) * Real.log H * (H : ℝ) * (P : ℝ) ^ 3 /
        ((W : ℝ) * Real.log P ^ 4) := by
      dsimp [R]
      ring

/-- Floor-safe absolute-fiber assembly. -/
theorem minorArcPrimeQuadrupleMass_le_of_absoluteFiberEstimate_at_succ
    (C : ℝ) (hC : 0 < C)
    (H W P q : ℕ)
    (hfiber : ∀ n : ℕ,
      ((primeQuadrupleAbsoluteDifferenceFiber P n).card : ℝ) ≤
        C * (P : ℝ) ^ 3 / Real.log P ^ 4)
    (a : ℤ) (α : ℝ)
    (hW : 2 ≤ W) (hWq : W ≤ q) (hqH : q ≤ H / W + 1)
    (hPlo : W ^ 200 ≤ P) (hPhi : P ≤ H / W ^ 3)
    (ha : a.natAbs.Coprime q)
    (hα : |α - (a : ℝ) / q| ≤ (W : ℝ) / ((H : ℝ) * q)) :
    minorArcPrimeQuadrupleMass H P α ≤
      (100 * C) * Real.log H * (H : ℝ) * (P : ℝ) ^ 3 /
        ((W : ℝ) * Real.log P ^ 4) := by
  have hPtwo : 2 ≤ P := by
    have hpow : 2 ^ 200 ≤ W ^ 200 := Nat.pow_le_pow_left hW 200
    omega
  have hlogP : 0 < Real.log (P : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < P by omega))
  let R : ℝ := C * (P : ℝ) ^ 3 / Real.log P ^ 4
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hmass := minorArcPrimeQuadrupleMass_le_of_fiber_bound
    H P α R hR (fun n hn ↦ hfiber n)
  have hvino := vinogradovWeight_two_mul_le_minor_arc_int_succ
    H W P q a α hW hWq hqH hPlo hPhi ha hα
  calc
    minorArcPrimeQuadrupleMass H P α ≤
        R * ∑ n ∈ Finset.range (2 * P + 1),
          vinogradovWeight H P ((n : ℝ) * α) := hmass
    _ ≤ R * (100 * Real.log H * ((H : ℝ) / W)) :=
      mul_le_mul_of_nonneg_left hvino hR
    _ = (100 * C) * Real.log H * (H : ℝ) * (P : ℝ) ^ 3 /
        ((W : ℝ) * Real.log P ^ 4) := by
      dsimp [R]
      ring

/-- Global-fiber version of
`minorArcPrimeQuadrupleMass_le_of_absoluteFiberEstimate_at`. -/
theorem minorArcPrimeQuadrupleMass_le_of_absoluteFiberEstimate
    (C : ℝ) (hC : 0 < C)
    (hfiber : ∀ P n : ℕ,
      ((primeQuadrupleAbsoluteDifferenceFiber P n).card : ℝ) ≤
        C * (P : ℝ) ^ 3 / Real.log P ^ 4)
    (H W P q : ℕ) (a : ℤ) (α : ℝ)
    (hW : 2 ≤ W) (hWq : W ≤ q) (hqH : q ≤ H / W)
    (hPlo : W ^ 200 ≤ P) (hPhi : P ≤ H / W ^ 3)
    (ha : a.natAbs.Coprime q)
    (hα : |α - (a : ℝ) / q| ≤ (W : ℝ) / ((H : ℝ) * q)) :
    minorArcPrimeQuadrupleMass H P α ≤
      (100 * C) * Real.log H * (H : ℝ) * (P : ℝ) ^ 3 /
        ((W : ℝ) * Real.log P ^ 4) := by
  exact minorArcPrimeQuadrupleMass_le_of_absoluteFiberEstimate_at
    C hC H W P q (hfiber P) a α hW hWq hqH hPlo hPhi ha hα

/-- Assembly of the four-prime representation estimate and the finite
Vinogradov lemma.  The following theorem makes the remaining sieve input
explicit, while all rational-approximation and signed-frequency bookkeeping
is discharged here. -/
theorem minorArcPrimeQuadrupleMass_le_of_signedFiberEstimate_at
    (C : ℝ) (hC : 0 < C)
    (H W P q : ℕ)
    (hfiber : ∀ d : ℤ,
      ((primeQuadrupleDifferenceFiber P d).card : ℝ) ≤
        C * (P : ℝ) ^ 3 / Real.log P ^ 4)
    (a : ℤ) (α : ℝ)
    (hW : 2 ≤ W) (hWq : W ≤ q) (hqH : q ≤ H / W)
    (hPlo : W ^ 200 ≤ P) (hPhi : P ≤ H / W ^ 3)
    (ha : a.natAbs.Coprime q)
    (hα : |α - (a : ℝ) / q| ≤ (W : ℝ) / ((H : ℝ) * q)) :
    minorArcPrimeQuadrupleMass H P α ≤
      (200 * C) * Real.log H * (H : ℝ) * (P : ℝ) ^ 3 /
        ((W : ℝ) * Real.log P ^ 4) := by
  have hPtwo : 2 ≤ P := by
    have hpow : 2 ^ 200 ≤ W ^ 200 := Nat.pow_le_pow_left hW 200
    omega
  have hlogP : 0 < Real.log (P : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < P by omega))
  let R : ℝ := C * (P : ℝ) ^ 3 / Real.log P ^ 4
  have hR : 0 ≤ R := by
    dsimp [R]
    positivity
  have habs : ∀ n ≤ 2 * P,
      ((primeQuadrupleAbsoluteDifferenceFiber P n).card : ℝ) ≤ 2 * R := by
    intro n hn
    exact card_primeQuadrupleAbsoluteDifferenceFiber_le_two_mul P n R
      hfiber
  have hmass := minorArcPrimeQuadrupleMass_le_of_fiber_bound
    H P α (2 * R) (mul_nonneg (by norm_num) hR) habs
  have hvino :
      (∑ n ∈ Finset.range (2 * P + 1),
          vinogradovWeight H P ((n : ℝ) * α)) ≤
        100 * Real.log H * ((H : ℝ) / W) := by
    exact vinogradovWeight_two_mul_le_minor_arc_int
      H W P q a α hW hWq hqH hPlo hPhi ha hα
  calc
    minorArcPrimeQuadrupleMass H P α ≤
        (2 * R) * ∑ n ∈ Finset.range (2 * P + 1),
          vinogradovWeight H P ((n : ℝ) * α) := hmass
    _ ≤ (2 * R) * (100 * Real.log H * ((H : ℝ) / W)) := by
      exact mul_le_mul_of_nonneg_left hvino (mul_nonneg (by norm_num) hR)
    _ = (200 * C) * Real.log H * (H : ℝ) * (P : ℝ) ^ 3 /
        ((W : ℝ) * Real.log P ^ 4) := by
      dsimp [R]
      ring

/-- Floor-safe signed-fiber assembly. -/
theorem minorArcPrimeQuadrupleMass_le_of_signedFiberEstimate_at_succ
    (C : ℝ) (hC : 0 < C)
    (H W P q : ℕ)
    (hfiber : ∀ d : ℤ,
      ((primeQuadrupleDifferenceFiber P d).card : ℝ) ≤
        C * (P : ℝ) ^ 3 / Real.log P ^ 4)
    (a : ℤ) (α : ℝ)
    (hW : 2 ≤ W) (hWq : W ≤ q) (hqH : q ≤ H / W + 1)
    (hPlo : W ^ 200 ≤ P) (hPhi : P ≤ H / W ^ 3)
    (ha : a.natAbs.Coprime q)
    (hα : |α - (a : ℝ) / q| ≤ (W : ℝ) / ((H : ℝ) * q)) :
    minorArcPrimeQuadrupleMass H P α ≤
      (200 * C) * Real.log H * (H : ℝ) * (P : ℝ) ^ 3 /
        ((W : ℝ) * Real.log P ^ 4) := by
  have hPtwo : 2 ≤ P := by
    have hpow : 2 ^ 200 ≤ W ^ 200 := Nat.pow_le_pow_left hW 200
    omega
  have hlogP : 0 < Real.log (P : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < P by omega))
  let R : ℝ := C * (P : ℝ) ^ 3 / Real.log P ^ 4
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have habs : ∀ n ≤ 2 * P,
      ((primeQuadrupleAbsoluteDifferenceFiber P n).card : ℝ) ≤ 2 * R := by
    intro n hn
    exact card_primeQuadrupleAbsoluteDifferenceFiber_le_two_mul P n R hfiber
  have hmass := minorArcPrimeQuadrupleMass_le_of_fiber_bound
    H P α (2 * R) (mul_nonneg (by norm_num) hR) habs
  have hvino := vinogradovWeight_two_mul_le_minor_arc_int_succ
    H W P q a α hW hWq hqH hPlo hPhi ha hα
  calc
    minorArcPrimeQuadrupleMass H P α ≤
        (2 * R) * ∑ n ∈ Finset.range (2 * P + 1),
          vinogradovWeight H P ((n : ℝ) * α) := hmass
    _ ≤ (2 * R) * (100 * Real.log H * ((H : ℝ) / W)) :=
      mul_le_mul_of_nonneg_left hvino (mul_nonneg (by norm_num) hR)
    _ = (200 * C) * Real.log H * (H : ℝ) * (P : ℝ) ^ 3 /
        ((W : ℝ) * Real.log P ^ 4) := by
      dsimp [R]
      ring

/-- Global-fiber version of
`minorArcPrimeQuadrupleMass_le_of_signedFiberEstimate_at`. -/
theorem minorArcPrimeQuadrupleMass_le_of_signedFiberEstimate
    (C : ℝ) (hC : 0 < C)
    (hfiber : ∀ P : ℕ, ∀ d : ℤ,
      ((primeQuadrupleDifferenceFiber P d).card : ℝ) ≤
        C * (P : ℝ) ^ 3 / Real.log P ^ 4)
    (H W P q : ℕ) (a : ℤ) (α : ℝ)
    (hW : 2 ≤ W) (hWq : W ≤ q) (hqH : q ≤ H / W)
    (hPlo : W ^ 200 ≤ P) (hPhi : P ≤ H / W ^ 3)
    (ha : a.natAbs.Coprime q)
    (hα : |α - (a : ℝ) / q| ≤ (W : ℝ) / ((H : ℝ) * q)) :
    minorArcPrimeQuadrupleMass H P α ≤
      (200 * C) * Real.log H * (H : ℝ) * (P : ℝ) ^ 3 /
        ((W : ℝ) * Real.log P ^ 4) := by
  exact minorArcPrimeQuadrupleMass_le_of_signedFiberEstimate_at
    C hC H W P q (hfiber P) a α hW hWq hqH hPlo hPhi ha hα

/-- The still-deep minor-arc input after Ramaré, dyadic decomposition, Hölder,
fourth-moment expansion, and geometric summation.

This is the uniform finite form of equation (3.3) in arXiv:1503.05121v3.
Its proof combines an upper-bound sieve for representations by two primes with
the Vinogradov lemma for a rational approximation `a/q` to `α`.  It is a
`Prop` definition, not an assumption. -/
def MRTMinorArcQuadrupleEstimate : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ H W P q : ℕ, ∀ a : ℤ, ∀ α : ℝ,
      2 ≤ W → W ≤ q → q ≤ H / W + 1 → W ^ 200 ≤ P → P ≤ H / W ^ 3 →
      Nat.Coprime a.natAbs q →
      |α - (a : ℝ) / q| ≤ (W : ℝ) / ((H : ℝ) * q) →
      minorArcPrimeQuadrupleMass H P α ≤
        C * Real.log H * (H : ℝ) * (P : ℝ) ^ 3 /
          ((W : ℝ) * Real.log P ^ 4)

/-- A tail estimate for signed four-prime fibers proves the full minor-arc
estimate as soon as its threshold lies below the scale `2^200`.  Indeed, the
minor-arc hypotheses give `2^200 ≤ W^200 ≤ P`. -/
theorem MRTMinorArcQuadrupleEstimate_of_eventual_signedFiberEstimate
    (P₀ : ℕ) (hP₀ : P₀ ≤ 2 ^ 200)
    (C : ℝ) (hC : 0 < C)
    (hfiber : ∀ P : ℕ, P₀ ≤ P → ∀ d : ℤ,
      ((primeQuadrupleDifferenceFiber P d).card : ℝ) ≤
        C * (P : ℝ) ^ 3 / Real.log P ^ 4) :
    MRTMinorArcQuadrupleEstimate := by
  refine ⟨200 * C, mul_pos (by norm_num) hC, ?_⟩
  intro H W P q a α hW hWq hqH hPlo hPhi ha hα
  have hscale : 2 ^ 200 ≤ P :=
    (Nat.pow_le_pow_left hW 200).trans hPlo
  exact minorArcPrimeQuadrupleMass_le_of_signedFiberEstimate_at_succ
    C hC H W P q (hfiber P (hP₀.trans hscale)) a α
      hW hWq hqH hPlo hPhi ha hα

/-- Absolute-fiber counterpart of
`MRTMinorArcQuadrupleEstimate_of_eventual_signedFiberEstimate`, retaining the
sharper assembly constant `100`. -/
theorem MRTMinorArcQuadrupleEstimate_of_eventual_absoluteFiberEstimate
    (P₀ : ℕ) (hP₀ : P₀ ≤ 2 ^ 200)
    (C : ℝ) (hC : 0 < C)
    (hfiber : ∀ P : ℕ, P₀ ≤ P → ∀ n : ℕ,
      ((primeQuadrupleAbsoluteDifferenceFiber P n).card : ℝ) ≤
        C * (P : ℝ) ^ 3 / Real.log P ^ 4) :
    MRTMinorArcQuadrupleEstimate := by
  refine ⟨100 * C, mul_pos (by norm_num) hC, ?_⟩
  intro H W P q a α hW hWq hqH hPlo hPhi ha hα
  have hscale : 2 ^ 200 ≤ P :=
    (Nat.pow_le_pow_left hW 200).trans hPlo
  exact minorArcPrimeQuadrupleMass_le_of_absoluteFiberEstimate_at_succ
    C hC H W P q (hfiber P (hP₀.trans hscale)) a α
      hW hWq hqH hPlo hPhi ha hα

/-- An arbitrary eventual signed-fiber estimate suffices.  The finitely many
scales between `2^200` and its eventual threshold are absorbed into the
constant using the crude fourth-power cardinality bound above. -/
theorem MRTMinorArcQuadrupleEstimate_of_eventually_signedFiberEstimate
    (C : ℝ) (hC : 0 < C)
    (hfiber : ∀ᶠ P : ℕ in Filter.atTop, ∀ d : ℤ,
      ((primeQuadrupleDifferenceFiber P d).card : ℝ) ≤
        C * (P : ℝ) ^ 3 / Real.log P ^ 4) :
    MRTMinorArcQuadrupleEstimate := by
  obtain ⟨P₀, hP₀⟩ := Filter.eventually_atTop.1 hfiber
  let D : ℝ :=
    (((2 * P₀ + 1 : ℕ) : ℝ) ^ 4 * Real.log (P₀ : ℝ) ^ 4) + 1
  let C' : ℝ := C + D
  have hD : 0 < D := by
    dsimp [D]
    positivity
  have hC' : 0 < C' := by
    dsimp [C']
    linarith
  apply MRTMinorArcQuadrupleEstimate_of_eventual_signedFiberEstimate
    (2 ^ 200) le_rfl C' hC'
  intro P hscale d
  have hPtwo : 2 ≤ P := by
    exact (show 2 ≤ 2 ^ 200 by norm_num).trans hscale
  have hlogP : 0 < Real.log (P : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < P by omega))
  have hratio : 0 ≤ (P : ℝ) ^ 3 / Real.log (P : ℝ) ^ 4 := by
    positivity
  by_cases htail : P₀ ≤ P
  · calc
      ((primeQuadrupleDifferenceFiber P d).card : ℝ) ≤
          C * (P : ℝ) ^ 3 / Real.log P ^ 4 := hP₀ P htail d
      _ ≤ C' * (P : ℝ) ^ 3 / Real.log P ^ 4 := by
        rw [mul_div_assoc, mul_div_assoc]
        exact mul_le_mul_of_nonneg_right (by dsimp [C']; linarith) hratio
  · have hPP₀ : P ≤ P₀ := by omega
    have hP₀two : 2 ≤ P₀ := hPtwo.trans hPP₀
    have hlogP₀ : 0 < Real.log (P₀ : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < P₀ by omega))
    have hPR : (0 : ℝ) < P := by exact_mod_cast (show 0 < P by omega)
    have hP₀R : (0 : ℝ) < P₀ := by exact_mod_cast (show 0 < P₀ by omega)
    have hlog_le : Real.log (P : ℝ) ≤ Real.log (P₀ : ℝ) :=
      Real.strictMonoOn_log.monotoneOn
        (by simpa using hPR) (by simpa using hP₀R) (by exact_mod_cast hPP₀)
    have hlogpow : Real.log (P : ℝ) ^ 4 ≤ Real.log (P₀ : ℝ) ^ 4 := by
      gcongr
    let L : ℝ := ((2 * P₀ + 1 : ℕ) : ℝ) ^ 4
    have hcard :
        ((primeQuadrupleDifferenceFiber P d).card : ℝ) ≤ L := by
      have hc := card_primeQuadrupleDifferenceFiber_le_crude P d
      have hcR :
          ((primeQuadrupleDifferenceFiber P d).card : ℝ) ≤
            (((2 * P + 1 : ℕ) : ℝ) ^ 4) := by
        exact_mod_cast hc
      have hpoly :
          (((2 * P + 1 : ℕ) : ℝ) ^ 4) ≤
            (((2 * P₀ + 1 : ℕ) : ℝ) ^ 4) := by
        exact_mod_cast Nat.pow_le_pow_left (by omega : 2 * P + 1 ≤ 2 * P₀ + 1) 4
      exact hcR.trans (by simpa [L] using hpoly)
    have hPcube : (1 : ℝ) ≤ (P : ℝ) ^ 3 := by
      have hPone : (1 : ℝ) ≤ P := by exact_mod_cast (show 1 ≤ P by omega)
      nlinarith [sq_nonneg (P : ℝ)]
    have hLD : L * Real.log (P₀ : ℝ) ^ 4 ≤ D := by
      dsimp [L, D]
      linarith
    have hDto : D ≤ D * (P : ℝ) ^ 3 := by
      calc
        D = D * 1 := by ring
        _ ≤ D * (P : ℝ) ^ 3 :=
          mul_le_mul_of_nonneg_left hPcube hD.le
    have hLratio : L ≤ D * (P : ℝ) ^ 3 / Real.log (P : ℝ) ^ 4 := by
      rw [le_div_iff₀ (pow_pos hlogP 4)]
      calc
        L * Real.log (P : ℝ) ^ 4 ≤
            L * Real.log (P₀ : ℝ) ^ 4 := by
          exact mul_le_mul_of_nonneg_left hlogpow (by positivity)
        _ ≤ D := hLD
        _ ≤ D * (P : ℝ) ^ 3 := hDto
    calc
      ((primeQuadrupleDifferenceFiber P d).card : ℝ) ≤ L := hcard
      _ ≤ D * (P : ℝ) ^ 3 / Real.log P ^ 4 := hLratio
      _ ≤ C' * (P : ℝ) ^ 3 / Real.log P ^ 4 := by
        rw [mul_div_assoc, mul_div_assoc]
        exact mul_le_mul_of_nonneg_right (by dsimp [C']; linarith) hratio

/-- Unconditional proof of the MRT minor-arc prime-quadruple estimate. -/
theorem mrtMinorArcQuadrupleEstimate : MRTMinorArcQuadrupleEstimate := by
  obtain ⟨K, hK, henergy⟩ := exists_primesLE_additiveQuadruples_bound
  apply MRTMinorArcQuadrupleEstimate_of_eventually_signedFiberEstimate K hK
  filter_upwards [henergy] with P henergyP
  intro d
  have hsubset := card_primeQuadrupleDifferenceFiber_le_primesLE P d
  have hshift := card_fourPrimeDifferenceFiber_le_additiveQuadruples
    (Nat.primesLE (2 * P)) d
  have hsubsetR :
      ((primeQuadrupleDifferenceFiber P d).card : ℝ) ≤
        ((fourPrimeDifferenceFiber (Nat.primesLE (2 * P)) d).card : ℝ) := by
    exact_mod_cast (hsubset.trans_eq (by
      rw [primeQuadrupleDifferenceFiberOn_eq_fourPrimeDifferenceFiber]))
  have hshiftR :
      ((fourPrimeDifferenceFiber (Nat.primesLE (2 * P)) d).card : ℝ) ≤
        ((additiveQuadruples (Nat.primesLE (2 * P))).card : ℝ) := by
    exact_mod_cast hshift
  exact hsubsetR.trans (hshiftR.trans henergyP)

end

end Erdos67
