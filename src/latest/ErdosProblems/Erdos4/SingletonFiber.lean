/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4.FullDiscrepancy
import BoundedGaps.Maynard.ConcreteFractionalTupleBox
import BoundedGaps.Maynard.WirsingAllEndpoints

namespace Erdos4

open Filter MeasureTheory Set
open scoped ArithmeticFunction.Moebius BigOperators Interval
noncomputable section

noncomputable local instance (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-! ### The one-coordinate fibre

For the large-gap covering weight it is useful to isolate the degenerate
one-shift Maynard family.  In one coordinate every cross-coordinate
compatibility condition is vacuous.  Consequently its compatible quadratic
form and its pinned kernel reduce to the same scalar reciprocal-totient mean.
-/

/-- The zero singleton shift used to pin the separated weight directly at the
residual prime.  This avoids any endpoint condition relating that prime to the
auxiliary covering modulus. -/
def singletonShift : Finset ℕ := {0}

/-- The unique coordinate of `singletonShift`. -/
def singletonShiftOne : ↑singletonShift := ⟨0, by simp [singletonShift]⟩

/-- A scalar regarded as a tuple on the singleton shift set. -/
def singletonTuple (n : ℕ) : ↑singletonShift → ℕ := fun _ => n

@[simp] theorem singletonShiftOne_val : (singletonShiftOne : ℕ) = 0 := rfl

theorem singletonShift_subsingleton (a b : ↑singletonShift) : a = b := by
  apply Subtype.ext
  have ha : (a : ℕ) = 0 := by simpa [singletonShift] using a.property
  have hb : (b : ℕ) = 0 := by simpa [singletonShift] using b.property
  exact ha.trans hb.symm

@[simp] theorem singletonTuple_apply (n : ℕ) (h : ↑singletonShift) :
    singletonTuple n h = n := rfl

theorem singletonTuple_ext (r : ↑singletonShift → ℕ) :
    r = singletonTuple (r singletonShiftOne) := by
  funext h
  rw [singletonShift_subsingleton h singletonShiftOne]
  rfl

@[simp] theorem divisorTupleProduct_singletonTuple (n : ℕ) :
    BoundedGaps.Maynard.divisorTupleProduct singletonShift
        (singletonTuple n) = n := by
  have hcard : singletonShift.card = 1 := by simp [singletonShift]
  simp [BoundedGaps.Maynard.divisorTupleProduct, singletonTuple, hcard]

@[simp] theorem totientProduct_singletonTuple (n : ℕ) :
    (∏ h : ↑singletonShift, Nat.totient (singletonTuple n h)) =
      Nat.totient n := by
  have hcard : singletonShift.card = 1 := by simp [singletonShift]
  simp [singletonTuple, hcard]

theorem singleton_isCrossCoordinateCoprime
    (d e : ↑singletonShift → ℕ) :
    BoundedGaps.Maynard.IsCrossCoordinateCoprime singletonShift d e := by
  intro a b hab
  exact False.elim (hab (singletonShift_subsingleton a b))

theorem singletonTuple_injective : Function.Injective singletonTuple := by
  intro a b hab
  exact congrFun hab singletonShiftOne

theorem singletonTuple_mem_maynardSupport_iff
    {R W n : ℕ} :
    singletonTuple n ∈
        BoundedGaps.Maynard.maynardDivisorTupleSupport singletonShift R W ↔
      n ∈ BoundedGaps.Maynard.squarefreeCoprimeCoordinateSupport W (R - 1) := by
  rw [BoundedGaps.Maynard.mem_maynardDivisorTupleSupport_iff]
  rw [BoundedGaps.Maynard.mem_maynardDivisorTupleBox_iff]
  unfold BoundedGaps.Maynard.IsMaynardDivisorTuple
    BoundedGaps.Maynard.squarefreeCoprimeCoordinateSupport
  simp only [divisorTupleProduct_singletonTuple, Finset.mem_filter,
    Finset.mem_Icc]
  constructor
  · rintro ⟨hbox, hlt, hcop, hsq⟩
    exact ⟨⟨(hbox singletonShiftOne).1, by omega⟩, hsq, hcop⟩
  · rintro ⟨⟨hone, hle⟩, hsq, hcop⟩
    have hlt : n < R := by omega
    exact ⟨fun _ => ⟨by simpa [singletonTuple] using hone,
      by simpa [singletonTuple] using hlt⟩, hlt, hcop, hsq⟩

theorem maynardBox_singleton_eq_image (R : ℕ) :
    BoundedGaps.Maynard.maynardDivisorTupleBox singletonShift R =
      (Finset.Icc 1 (R - 1)).image singletonTuple := by
  ext r
  constructor
  · intro hr
    have hrEq : r = singletonTuple (r singletonShiftOne) := singletonTuple_ext r
    have hrData :=
      BoundedGaps.Maynard.mem_maynardDivisorTupleBox_iff.mp hr singletonShiftOne
    rw [hrEq] at hr ⊢
    exact Finset.mem_image.mpr ⟨r singletonShiftOne,
      Finset.mem_Icc.mpr ⟨hrData.1, by omega⟩, rfl⟩
  · intro hr
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hr
    apply BoundedGaps.Maynard.mem_maynardDivisorTupleBox_iff.mpr
    intro h
    have hnData := Finset.mem_Icc.mp hn
    exact ⟨by simpa [singletonTuple] using hnData.1,
      by simp only [singletonTuple]; omega⟩

theorem maynardSupport_singleton_eq_image (R W : ℕ) :
    BoundedGaps.Maynard.maynardDivisorTupleSupport singletonShift R W =
      (BoundedGaps.Maynard.squarefreeCoprimeCoordinateSupport W (R - 1)).image
        singletonTuple := by
  ext r
  constructor
  · intro hr
    have hrEq : r = singletonTuple (r singletonShiftOne) := singletonTuple_ext r
    rw [hrEq] at hr ⊢
    exact Finset.mem_image.mpr
      ⟨r singletonShiftOne, singletonTuple_mem_maynardSupport_iff.mp hr, rfl⟩
  · intro hr
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hr
    exact singletonTuple_mem_maynardSupport_iff.mpr hn

/-- With the constant test function, the one-coordinate `Y` diagonal is
exactly the scalar squarefree/coprime reciprocal-totient mean. -/
theorem singleton_maynardYDiagonal_eq_mean (R W : ℕ) :
    BoundedGaps.Maynard.maynardYDiagonalSum singletonShift R W
        (BoundedGaps.Maynard.maynardYValue singletonShift R W (fun _ => 1)) =
      BoundedGaps.Maynard.squarefreeCoprimeInvTotientMean W (R - 1) := by
  have hcard : singletonShift.card = 1 := by simp [singletonShift]
  rw [BoundedGaps.Maynard.maynardYDiagonalSum_maynardYValue_eq_explicit]
  rw [maynardSupport_singleton_eq_image]
  rw [Finset.sum_image (fun _ _ _ _ h => singletonTuple_injective h)]
  rw [← BoundedGaps.Maynard.squarefreeCoprimeCoordinateSupport_sum]
  apply Finset.sum_congr rfl
  intro n hn
  simp [hcard]

/-- The all-one coefficient of the singleton constant family is the same
scalar reciprocal-totient mean. -/
theorem singleton_maynardCoefficient_one_eq_mean
    (R W : ℕ) :
    BoundedGaps.Maynard.maynardCoefficient singletonShift R W (fun _ => 1)
        (singletonTuple 1) =
      BoundedGaps.Maynard.squarefreeCoprimeInvTotientMean W (R - 1) := by
  classical
  have hcard : singletonShift.card = 1 := by simp [singletonShift]
  unfold BoundedGaps.Maynard.maynardCoefficient
  rw [divisorTupleProduct_singletonTuple]
  rw [if_pos (Nat.coprime_one_left W)]
  rw [maynardBox_singleton_eq_image]
  rw [Finset.sum_image (fun _ _ _ _ h => singletonTuple_injective h)]
  rw [← BoundedGaps.Maynard.squarefreeCoprimeCoordinateSupport_sum]
  unfold BoundedGaps.Maynard.squarefreeCoprimeCoordinateSupport
  simp only [Finset.sum_filter]
  simp only [divisorTupleProduct_singletonTuple, singletonTuple_apply]
  simp only [Finset.univ_eq_attach, isUnit_iff_eq_one, IsUnit.squarefree,
    ArithmeticFunction.moebius_apply_of_squarefree, Int.reduceNeg, ArithmeticFunction.cardFactors_one, pow_zero,
    Int.cast_one, Nat.cast_one, mul_one, Finset.prod_const_one, IsUnit.dvd, implies_true, true_and, Finset.prod_const,
    Finset.card_attach, one_mul, one_div]
  apply Finset.sum_congr rfl
  intro n hn
  have hnData := Finset.mem_Icc.mp hn
  have hnlt : n < R := by omega
  by_cases hsq : Squarefree n
  · have hneg : ((-1 : ℝ) ^ ArithmeticFunction.cardFactors n) ^ 2 = 1 := by
      rcases neg_one_pow_eq_or ℝ (ArithmeticFunction.cardFactors n) with h | h <;>
        rw [h] <;> norm_num
    by_cases hcop : Nat.Coprime n W <;> simp [hnlt, hsq, hcop, hneg]
  · have hmu := ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq
    by_cases hcop : Nat.Coprime n W <;> simp [hnlt, hsq, hcop, hmu]

theorem singleton_incompatibleSum_eq_zero
    (D : Finset (↑singletonShift → ℕ))
    (a : (↑singletonShift → ℕ) → ℝ) :
    BoundedGaps.Maynard.incompatibleDivisorPairCommonDivisorTupleSum
        singletonShift D a = 0 := by
  classical
  unfold BoundedGaps.Maynard.incompatibleDivisorPairCommonDivisorTupleSum
  apply Finset.sum_eq_zero
  intro d hd
  have hfilter :
      D.filter (fun e =>
        ¬BoundedGaps.Maynard.IsCrossCoordinateCoprime singletonShift d e) = ∅ := by
    ext e
    simp [singleton_isCrossCoordinateCoprime]
  rw [hfilter]
  simp

/-- In one coordinate the compatible quadratic has no collision correction,
so it is exactly the scalar mean. -/
theorem singleton_compatibleQuadratic_eq_mean (R W : ℕ) :
    BoundedGaps.Maynard.compatibleDivisorPairTotientExpandedSum singletonShift
        (BoundedGaps.Maynard.maynardDivisorTupleSupport singletonShift R W)
        (BoundedGaps.Maynard.maynardCoefficient singletonShift R W (fun _ => 1)) =
      BoundedGaps.Maynard.squarefreeCoprimeInvTotientMean W (R - 1) := by
  rw [BoundedGaps.Maynard.compatibleDivisorPairTotientExpandedSum_eq_commonDivisorTupleSum]
  have hcoeff :
      BoundedGaps.Maynard.maynardCoefficient singletonShift R W (fun _ => 1) =
        BoundedGaps.Maynard.maynardCoefficientFromY singletonShift R W
          (BoundedGaps.Maynard.maynardYValue singletonShift R W (fun _ => 1)) := by
    funext d
    exact BoundedGaps.Maynard.maynardCoefficient_eq_fromYValue
      singletonShift R W (fun _ => 1) d
  rw [hcoeff]
  rw [BoundedGaps.Maynard.compatibleCommonDivisorTupleSum_eq_yDiagonal_sub_incompatible
    (BoundedGaps.Maynard.isSupportedMaynardY_maynardYValue
      singletonShift R W (fun _ => 1))]
  rw [singleton_incompatibleSum_eq_zero]
  simp [singleton_maynardYDiagonal_eq_mean]

theorem singletonTuple_eq_one_of_apply_eq_one
    (d : ↑singletonShift → ℕ) (hd : d singletonShiftOne = 1) :
    d = singletonTuple 1 := by
  rw [singletonTuple_ext d, hd]

theorem singletonOne_mem_maynardSupport
    {R W : ℕ} (hR : 2 ≤ R) :
    singletonTuple 1 ∈
      BoundedGaps.Maynard.maynardDivisorTupleSupport singletonShift R W := by
  rw [singletonTuple_mem_maynardSupport_iff]
  unfold BoundedGaps.Maynard.squarefreeCoprimeCoordinateSupport
  simp
  omega

/-- The raw one-coordinate pinned kernel is the square of the scalar mean.
The pinning equations force both divisor tuples to be the all-one tuple. -/
theorem singleton_rawPinnedPairTotientKernel_eq_mean_sq
    {R W : ℕ} (hR : 2 ≤ R) :
    rawPinnedPairTotientKernel
        (BoundedGaps.Maynard.maynardDivisorTupleSupport singletonShift R W)
        (BoundedGaps.Maynard.maynardCoefficient singletonShift R W (fun _ => 1))
        singletonShiftOne =
      (BoundedGaps.Maynard.squarefreeCoprimeInvTotientMean W (R - 1)) ^ 2 := by
  classical
  let D := BoundedGaps.Maynard.maynardDivisorTupleSupport singletonShift R W
  let a := BoundedGaps.Maynard.maynardCoefficient singletonShift R W (fun _ => 1)
  let one := singletonTuple 1
  have hone : one ∈ D := by
    exact singletonOne_mem_maynardSupport hR
  unfold rawPinnedPairTotientKernel
  rw [Finset.sum_eq_single one]
  · rw [Finset.sum_eq_single one]
    · dsimp [one, a]
      rw [singleton_maynardCoefficient_one_eq_mean]
      simp [singleton_isCrossCoordinateCoprime,
        BoundedGaps.Maynard.divisorTupleLcm]
      ring
    · intro d' hd' hd'ne
      have hd'val : d' singletonShiftOne ≠ 1 := by
        intro hv
        exact hd'ne (singletonTuple_eq_one_of_apply_eq_one d' hv)
      simp [one, hd'val]
    · intro hnot
      exact False.elim (hnot hone)
  · intro d hd hdne
    have hdval : d singletonShiftOne ≠ 1 := by
      intro hv
      exact hdne (singletonTuple_eq_one_of_apply_eq_one d hv)
    apply Finset.sum_eq_zero
    intro d' hd'
    simp [hdval]
  · intro hnot
    exact False.elim (hnot hone)

/-! ### Uniform scalar asymptotics

This is the exact lower-bound form of the all-endpoint Wirsing estimate used
for both singleton normalizations.  The hypothesis states explicitly that the
logarithmic endpoint dominates the uniform error term. -/

theorem exists_uniform_singletonMean_lower_bound :
    ∃ K : ℝ, 0 < K ∧
      ∀ {D P Q : ℕ}, 0 < P →
        Squarefree (primorial D * P) →
        20 * (K + Real.log D +
          BoundedGaps.Maynard.primeLogDivisorMass P + Real.log 2) ≤
            Real.log Q →
        BoundedGaps.Maynard.coprimeHarmonicDensity (primorial D * P) *
              Real.log Q / 2 ≤
          BoundedGaps.Maynard.squarefreeCoprimeInvTotientMean
            (primorial D * P) Q := by
  obtain ⟨K, hK, hbound⟩ :=
    BoundedGaps.Maynard.exists_uniform_abs_squarefreeCoprimeInvTotientMean_sub_density_log_le
  refine ⟨K, hK, ?_⟩
  intro D P Q hP hsq hlarge
  let δ := BoundedGaps.Maynard.coprimeHarmonicDensity (primorial D * P)
  let E := K + Real.log D +
    BoundedGaps.Maynard.primeLogDivisorMass P + Real.log 2
  let M := BoundedGaps.Maynard.squarefreeCoprimeInvTotientMean
    (primorial D * P) Q
  have hW : 0 < primorial D * P := Nat.mul_pos (primorial_pos D) hP
  have hδ : 0 < δ := by
    dsimp [δ, BoundedGaps.Maynard.coprimeHarmonicDensity]
    exact div_pos
      (by exact_mod_cast Nat.totient_pos.mpr hW)
      (by exact_mod_cast hW)
  have habs : |M - δ * Real.log Q| ≤ 10 * δ * E := by
    simpa [M, δ, E] using hbound hP hsq
  have hlower : -(10 * δ * E) ≤ M - δ * Real.log Q :=
    (abs_le.mp habs).1
  have hscaled : 20 * δ * E ≤ δ * Real.log Q := by
    have := mul_le_mul_of_nonneg_left hlarge hδ.le
    calc
      20 * δ * E = δ * (20 * E) := by ring
      _ ≤ δ * Real.log Q := by simpa [E] using this
  nlinarith

end

end Erdos4
