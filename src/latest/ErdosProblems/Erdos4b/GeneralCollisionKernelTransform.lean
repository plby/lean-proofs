/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralCollisionYTransform

/-!
# Coefficient-summed transform of the unpinned doubled kernel

This file composes the exact identities in `GeneralCollisionYTransform`.
The first step is pointwise: the genuine affine-compatible cross-gcd
summand is a finite signed sum over a coefficient-independent matrix box,
multiplied by the two ordinary compatible-pair kernels.  Subsequent lemmas
interchange only finite sums and apply the two-family Maynard `Y` transform.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators

noncomputable local instance generalCollisionKernelTransformDecidable
    (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- The summand of the ordinary compatible normalized Maynard quadratic. -/
noncomputable def ordinaryCompatiblePairKernel
    {H : Finset ℕ} (lambda : (H → ℕ) → ℝ)
    (d d' : H → ℕ) : ℝ :=
  if BoundedGaps.Maynard.IsCrossCoordinateCoprime H d d' then
    lambda d * lambda d' / (firstLcmProduct H d d' : ℝ)
  else 0

theorem ordinaryCompatiblePairKernel_eq_globalCrossCommonSum
    {H : Finset ℕ} {R W : ℕ} {d d' : H → ℕ}
    (hd : BoundedGaps.Maynard.IsMaynardDivisorTuple H R W d)
    (hd' : BoundedGaps.Maynard.IsMaynardDivisorTuple H R W d')
    (lambda : (H → ℕ) → ℝ) :
    ordinaryCompatiblePairKernel lambda d d' =
      ∑ s ∈ BoundedGaps.Maynard.crossMoebiusTupleBox H R,
        ∑ u ∈ BoundedGaps.Maynard.maynardDivisorTupleBox H R,
          if BoundedGaps.Maynard.LeftCrossDivides H u s d ∧
              BoundedGaps.Maynard.RightCrossDivides H u s d' then
            BoundedGaps.Maynard.crossMoebiusTupleTerm H s *
              (∏ h : H, (Nat.totient (u h) : ℝ)) *
              ((lambda d /
                  (BoundedGaps.Maynard.divisorTupleProduct H d : ℝ)) *
                (lambda d' /
                  (BoundedGaps.Maynard.divisorTupleProduct H d' : ℝ)))
          else 0 := by
  simpa [ordinaryCompatiblePairKernel, firstLcmProduct,
    BoundedGaps.Maynard.divisorTupleLcm, Nat.cast_prod] using
      compatiblePairKernel_eq_globalCrossCommonSum hd hd' lambda

/-- Two supported tuples satisfying the ordinary cross-coordinate predicate
have pairwise-coprime coordinate lcms. -/
theorem pairwise_lcm_of_maynard_cross
    {H : Finset ℕ} {R W : ℕ} {d d' : H → ℕ}
    (hd : BoundedGaps.Maynard.IsMaynardDivisorTuple H R W d)
    (hd' : BoundedGaps.Maynard.IsMaynardDivisorTuple H R W d')
    (hcross : BoundedGaps.Maynard.IsCrossCoordinateCoprime H d d') :
    ∀ {a b : H}, a ≠ b →
      (Nat.lcm (d a) (d' a)).Coprime (Nat.lcm (d b) (d' b)) := by
  intro a b hab
  exact BoundedGaps.Maynard.coprime_lcm_lcm_of_four
    (hd.coordinates_coprime hab) (hcross hab).1
    (hcross hab).2 (hd'.coordinates_coprime hab)

/-- Companion Maynard tuples with modulus `W*m` are coordinatewise coprime
to `m`, also after taking the lcm of two coordinates. -/
theorem m_coprime_companion_lcm
    {H : Finset ℕ} {R W m : ℕ} {e e' : H → ℕ}
    (he : BoundedGaps.Maynard.IsMaynardDivisorTuple H R (W * m) e)
    (he' : BoundedGaps.Maynard.IsMaynardDivisorTuple H R (W * m) e')
    (h : H) : m.Coprime (Nat.lcm (e h) (e' h)) := by
  have hmE : m.Coprime (BoundedGaps.Maynard.divisorTupleProduct H e) :=
    Nat.Coprime.of_dvd_left (dvd_mul_left m W) he.2.1.symm
  have hmE' : m.Coprime (BoundedGaps.Maynard.divisorTupleProduct H e') :=
    Nat.Coprime.of_dvd_left (dvd_mul_left m W) he'.2.1.symm
  have hme : m.Coprime (e h) := Nat.Coprime.of_dvd_right
    (BoundedGaps.Maynard.divisorTupleCoordinate_dvd_product e h) hmE
  have hme' : m.Coprime (e' h) := Nat.Coprime.of_dvd_right
    (BoundedGaps.Maynard.divisorTupleCoordinate_dvd_product e' h) hmE'
  apply Nat.Coprime.of_dvd_right (Nat.lcm_dvd_mul (e h) (e' h))
  exact hme.mul_right hme'

/-- Fixed-box form of the compatibility-weighted cross gcd on ordinary
Maynard supports, assuming the two ordinary within-family predicates. -/
theorem affineBoxSum_eq_compatibilityCrossGcd_of_cross
    {H : Finset ℕ} {RD RE W m q : ℕ} {d e d' e' : H → ℕ}
    (hd : BoundedGaps.Maynard.IsMaynardDivisorTuple H RD W d)
    (hd' : BoundedGaps.Maynard.IsMaynardDivisorTuple H RD W d')
    (he : BoundedGaps.Maynard.IsMaynardDivisorTuple H RE (W * m) e)
    (he' : BoundedGaps.Maynard.IsMaynardDivisorTuple H RE (W * m) e')
    (hcrossD : BoundedGaps.Maynard.IsCrossCoordinateCoprime H d d')
    (hcrossE : BoundedGaps.Maynard.IsCrossCoordinateCoprime H e e') :
    (∑ A ∈ crossAuxiliarySquarefreeValueMatrixBox H (RD * RD),
        crossAuxiliaryGcdIndicator A d e d' e' *
          crossAuxiliaryAffineMobiusWeight m q A) =
      if LargeGapCoordinateCrtCompatible H m q d e d' e' then
        (crossCoordinateGcdProduct H d e d' e' : ℝ)
      else 0 := by
  have hDpos : ∀ h : H, 0 < Nat.lcm (d h) (d' h) := fun h ↦
    Nat.lcm_pos (Nat.pos_of_ne_zero (hd.coordinate_squarefree h).ne_zero)
      (Nat.pos_of_ne_zero (hd'.coordinate_squarefree h).ne_zero)
  have hEpos : ∀ h : H, 0 < Nat.lcm (e h) (e' h) := fun h ↦
    Nat.lcm_pos (Nat.pos_of_ne_zero (he.coordinate_squarefree h).ne_zero)
      (Nat.pos_of_ne_zero (he'.coordinate_squarefree h).ne_zero)
  have hDD : ∀ {a b : H}, a ≠ b →
      (Nat.lcm (d a) (d' a)).Coprime (Nat.lcm (d b) (d' b)) :=
    pairwise_lcm_of_maynard_cross hd hd' hcrossD
  have hEE : ∀ {a b : H}, a ≠ b →
      (Nat.lcm (e a) (e' a)).Coprime (Nat.lcm (e b) (e' b)) :=
    pairwise_lcm_of_maynard_cross he he' hcrossE
  calc
    (∑ A ∈ crossAuxiliarySquarefreeValueMatrixBox H (RD * RD),
        crossAuxiliaryGcdIndicator A d e d' e' *
          crossAuxiliaryAffineMobiusWeight m q A) =
        ∑ a : CrossAuxiliaryDivisors H d e d' e',
          crossAuxiliaryAffineMobiusWeight m q
            (crossAuxiliaryValueMatrixOf a) :=
      (auxiliaryAffineMobiusSum_eq_squarefreeBox
        (fun ba ↦ localCrossGcd_pos_of_maynardTuples hd hd' he he' ba)
        (fun ba ↦ (localCrossGcd_lt_radius_sq hd hd' he he' ba).le)
        (fun ba ↦
          (BoundedGaps.Maynard.squarefree_lcm
            (hd.coordinate_squarefree ba.2)
            (hd'.coordinate_squarefree ba.2)).squarefree_of_dvd
              (Nat.gcd_dvd_left _ _))).symm
    _ = _ :=
      (compatibilityIndicator_mul_crossGcd_eq_auxiliaryMobiusSum
        hDpos hEpos (m_coprime_companion_lcm he he') hDD hEE).symm

/-- Pointwise bridge from the genuine doubled normalization summand to the
fixed matrix box times the two ordinary compatible-pair kernels. -/
theorem doubledCrossSummand_eq_pairKernels_mul_affineBox
    {H : Finset ℕ} {RD RE W m q : ℕ} {d e d' e' : H → ℕ}
    (hd : BoundedGaps.Maynard.IsMaynardDivisorTuple H RD W d)
    (hd' : BoundedGaps.Maynard.IsMaynardDivisorTuple H RD W d')
    (he : BoundedGaps.Maynard.IsMaynardDivisorTuple H RE (W * m) e)
    (he' : BoundedGaps.Maynard.IsMaynardDivisorTuple H RE (W * m) e')
    (hm : 0 < m) (hq : q.Prime) (hRDq : RD ≤ q) (hREq : RE ≤ q)
    (hcover : BoundedGaps.Maynard.CoversShiftDifferencePrimes H W)
    (lambdaD lambdaE : (H → ℕ) → ℝ) :
    (if LargeGapCoordinateCrtCompatible H m q d e d' e' then
        (lambdaD d * lambdaE e) * (lambdaD d' * lambdaE e') *
            crossCoordinateTotientSumProduct H d e d' e' /
          ((firstLcmProduct H d d' : ℝ) *
            companionLcmProduct H e e')
      else 0) =
      ordinaryCompatiblePairKernel lambdaD d d' *
        ordinaryCompatiblePairKernel lambdaE e e' *
        (∑ A ∈ crossAuxiliarySquarefreeValueMatrixBox H (RD * RD),
          crossAuxiliaryGcdIndicator A d e d' e' *
            crossAuxiliaryAffineMobiusWeight m q A) := by
  classical
  by_cases hc : LargeGapCoordinateCrtCompatible H m q d e d' e'
  · have hwithin :=
      withinFamilyCrossCoordinateCoprime_of_coordinateCompatible
        hm hq hRDq hREq hcover hd hd' he he' hc
    change BoundedGaps.Maynard.IsCrossCoordinateCoprime H d d' ∧
      BoundedGaps.Maynard.IsCrossCoordinateCoprime H e e' at hwithin
    obtain ⟨hcrossD, hcrossE⟩ := hwithin
    have hpairD : ordinaryCompatiblePairKernel lambdaD d d' =
        lambdaD d * lambdaD d' / (firstLcmProduct H d d' : ℝ) := by
      unfold ordinaryCompatiblePairKernel
      split
      · rfl
      · rename_i h
        exact (h hcrossD).elim
    have hpairE : ordinaryCompatiblePairKernel lambdaE e e' =
        lambdaE e * lambdaE e' / (firstLcmProduct H e e' : ℝ) := by
      unfold ordinaryCompatiblePairKernel
      split
      · rfl
      · rename_i h
        exact (h hcrossE).elim
    have hbox := affineBoxSum_eq_compatibilityCrossGcd_of_cross
      (q := q) hd hd' he he' hcrossD hcrossE
    rw [if_pos hc, hbox, if_pos hc,
      crossCoordinateTotientSumProduct_eq_crossGcd, hpairD, hpairE]
    unfold firstLcmProduct companionLcmProduct
    ring
  · rw [if_neg hc]
    by_cases hcrossD : BoundedGaps.Maynard.IsCrossCoordinateCoprime H d d'
    · by_cases hcrossE : BoundedGaps.Maynard.IsCrossCoordinateCoprime H e e'
      · have hbox := affineBoxSum_eq_compatibilityCrossGcd_of_cross
          (q := q) hd hd' he he' hcrossD hcrossE
        rw [hbox, if_neg hc]
        simp
      · simp [ordinaryCompatiblePairKernel, hcrossE]
    · simp [ordinaryCompatiblePairKernel, hcrossD]

/-- The finite fixed-box kernel obtained after the pointwise bridge. -/
noncomputable def doubledSelbergAffineBoxKernel
    (H : Finset ℕ) (RD : ℕ) (D E : Finset (H → ℕ))
    (lambdaD lambdaE : (H → ℕ) → ℝ) (m q : ℕ) : ℝ :=
  ∑ d ∈ D, ∑ e ∈ E, ∑ d' ∈ D, ∑ e' ∈ E,
    ordinaryCompatiblePairKernel lambdaD d d' *
      ordinaryCompatiblePairKernel lambdaE e e' *
      (∑ A ∈ crossAuxiliarySquarefreeValueMatrixBox H (RD * RD),
        crossAuxiliaryGcdIndicator A d e d' e' *
          crossAuxiliaryAffineMobiusWeight m q A)

/-- The genuine doubled cross-totient kernel equals its fixed-box form on
the two standard Maynard supports. -/
theorem doubledSelbergCrossTotientKernel_eq_affineBox_standard
    (H : Finset ℕ) (RD RE W m q : ℕ)
    (lambdaD lambdaE : (H → ℕ) → ℝ)
    (hm : 0 < m) (hq : q.Prime) (hRDq : RD ≤ q) (hREq : RE ≤ q)
    (hcover : BoundedGaps.Maynard.CoversShiftDifferencePrimes H W) :
    doubledSelbergCrossTotientKernel H
        (BoundedGaps.Maynard.maynardDivisorTupleSupport H RD W)
        (BoundedGaps.Maynard.maynardDivisorTupleSupport H RE (W * m))
        (fun d e ↦ lambdaD d * lambdaE e) m q =
      doubledSelbergAffineBoxKernel H RD
        (BoundedGaps.Maynard.maynardDivisorTupleSupport H RD W)
        (BoundedGaps.Maynard.maynardDivisorTupleSupport H RE (W * m))
        lambdaD lambdaE m q := by
  classical
  unfold doubledSelbergCrossTotientKernel doubledSelbergAffineBoxKernel
  apply Finset.sum_congr rfl
  intro d hdMem
  apply Finset.sum_congr rfl
  intro e heMem
  apply Finset.sum_congr rfl
  intro d' hd'Mem
  apply Finset.sum_congr rfl
  intro e' he'Mem
  exact doubledCrossSummand_eq_pairKernels_mul_affineBox
    (BoundedGaps.Maynard.isMaynardDivisorTuple_of_mem_support hdMem)
    (BoundedGaps.Maynard.isMaynardDivisorTuple_of_mem_support hd'Mem)
    (BoundedGaps.Maynard.isMaynardDivisorTuple_of_mem_support heMem)
    (BoundedGaps.Maynard.isMaynardDivisorTuple_of_mem_support he'Mem)
    hm hq hRDq hREq hcover lambdaD lambdaE

/-! ## Moving the fixed matrix box outside the coefficient sums -/

/-- Weight attached to one ordinary common tuple and one ordinary
cross-Möbius tuple. -/
noncomputable def crossCommonTupleWeight
    {H : Finset ℕ}
    (s : ∀ ab : H × H,
      ab ∈ BoundedGaps.Maynard.offDiagonalPairs H → ℕ)
    (u : H → ℕ) : ℝ :=
  BoundedGaps.Maynard.crossMoebiusTupleTerm H s *
    ∏ h : H, (Nat.totient (u h) : ℝ)

/-- Pointwise compatible-pair expansion in exactly the lower-restricted
coefficient form consumed by `crossAuxiliary_fixedMatrix_crossY_transform`. -/
theorem ordinaryCompatiblePairKernel_eq_lowerRestrictedSum
    {H : Finset ℕ} {R W : ℕ} {d d' : H → ℕ}
    (hd : BoundedGaps.Maynard.IsMaynardDivisorTuple H R W d)
    (hd' : BoundedGaps.Maynard.IsMaynardDivisorTuple H R W d')
    (y : (H → ℕ) → ℝ) :
    ordinaryCompatiblePairKernel
        (BoundedGaps.Maynard.maynardCoefficientFromY H R W y) d d' =
      ∑ s ∈ BoundedGaps.Maynard.crossMoebiusTupleBox H R,
        ∑ u ∈ BoundedGaps.Maynard.maynardDivisorTupleBox H R,
          crossCommonTupleWeight s u *
            (maynardLowerRestrictedCoefficient H R W y
                (BoundedGaps.Maynard.leftCrossLowerTuple H u s) d *
              maynardLowerRestrictedCoefficient H R W y
                (BoundedGaps.Maynard.rightCrossLowerTuple H u s) d') := by
  rw [ordinaryCompatiblePairKernel_eq_globalCrossCommonSum hd hd']
  apply Finset.sum_congr rfl
  intro s hs
  apply Finset.sum_congr rfl
  intro u hu
  unfold crossCommonTupleWeight maynardLowerRestrictedCoefficient
  by_cases hl : BoundedGaps.Maynard.LeftCrossDivides H u s d
  · have hl' := BoundedGaps.Maynard.leftCrossLowerTuple_dvd_iff.mpr hl
    by_cases hr : BoundedGaps.Maynard.RightCrossDivides H u s d'
    · have hr' := BoundedGaps.Maynard.rightCrossLowerTuple_dvd_iff.mpr hr
      rw [if_pos ⟨hl, hr⟩, if_pos hl', if_pos hr']
    · have hr' : ¬∀ h : H,
          BoundedGaps.Maynard.rightCrossLowerTuple H u s h ∣ d' h :=
        fun h ↦ hr (BoundedGaps.Maynard.rightCrossLowerTuple_dvd_iff.mp h)
      rw [if_neg (fun h ↦ hr h.2), if_neg hr']
      ring
  · have hl' : ¬∀ h : H,
        BoundedGaps.Maynard.leftCrossLowerTuple H u s h ∣ d h :=
      fun h ↦ hl (BoundedGaps.Maynard.leftCrossLowerTuple_dvd_iff.mp h)
    rw [if_neg (fun h ↦ hl h.1), if_neg hl']
    ring

/-- Reorder the five finite indices used below.  This lemma deliberately
keeps the coefficient families separate, avoiding any quotient or
convergence argument. -/
theorem sum_five_reorder
    {DType EType AType M : Type*}
    [DecidableEq DType] [DecidableEq EType] [DecidableEq AType]
    [AddCommMonoid M]
    (D : Finset DType) (E : Finset EType) (A : Finset AType)
    (F : DType → EType → DType → EType → AType → M) :
    (∑ d ∈ D, ∑ e ∈ E, ∑ d' ∈ D, ∑ e' ∈ E, ∑ a ∈ A,
        F d e d' e' a) =
      ∑ a ∈ A, ∑ d ∈ D, ∑ d' ∈ D, ∑ e ∈ E, ∑ e' ∈ E,
        F d e d' e' a := by
  calc
    (∑ d ∈ D, ∑ e ∈ E, ∑ d' ∈ D, ∑ e' ∈ E, ∑ a ∈ A,
        F d e d' e' a) =
        ∑ d ∈ D, ∑ e ∈ E, ∑ d' ∈ D, ∑ a ∈ A, ∑ e' ∈ E,
          F d e d' e' a := by
      apply Finset.sum_congr rfl
      intro d hd
      apply Finset.sum_congr rfl
      intro e he
      apply Finset.sum_congr rfl
      intro d' hd'
      rw [Finset.sum_comm]
    _ = ∑ d ∈ D, ∑ e ∈ E, ∑ a ∈ A, ∑ d' ∈ D, ∑ e' ∈ E,
          F d e d' e' a := by
      apply Finset.sum_congr rfl
      intro d hd
      apply Finset.sum_congr rfl
      intro e he
      rw [Finset.sum_comm]
    _ = ∑ d ∈ D, ∑ a ∈ A, ∑ e ∈ E, ∑ d' ∈ D, ∑ e' ∈ E,
          F d e d' e' a := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.sum_comm]
    _ = ∑ a ∈ A, ∑ d ∈ D, ∑ e ∈ E, ∑ d' ∈ D, ∑ e' ∈ E,
          F d e d' e' a := by
      rw [Finset.sum_comm]
    _ = ∑ a ∈ A, ∑ d ∈ D, ∑ d' ∈ D, ∑ e ∈ E, ∑ e' ∈ E,
          F d e d' e' a := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.sum_comm]

/-- Matrix-outer form of `doubledSelbergAffineBoxKernel`. -/
noncomputable def doubledSelbergAffineBoxOuterKernel
    (H : Finset ℕ) (RD : ℕ) (D E : Finset (H → ℕ))
    (lambdaD lambdaE : (H → ℕ) → ℝ) (m q : ℕ) : ℝ :=
  ∑ A ∈ crossAuxiliarySquarefreeValueMatrixBox H (RD * RD),
    crossAuxiliaryAffineMobiusWeight m q A *
      (∑ d ∈ D, ∑ d' ∈ D, ∑ e ∈ E, ∑ e' ∈ E,
        crossAuxiliaryGcdIndicator A d e d' e' *
          (ordinaryCompatiblePairKernel lambdaD d d' *
            ordinaryCompatiblePairKernel lambdaE e e'))

theorem doubledSelbergAffineBoxKernel_eq_outer
    (H : Finset ℕ) (RD : ℕ) (D E : Finset (H → ℕ))
    (lambdaD lambdaE : (H → ℕ) → ℝ) (m q : ℕ) :
    doubledSelbergAffineBoxKernel H RD D E lambdaD lambdaE m q =
      doubledSelbergAffineBoxOuterKernel H RD D E lambdaD lambdaE m q := by
  classical
  unfold doubledSelbergAffineBoxKernel doubledSelbergAffineBoxOuterKernel
  simp_rw [Finset.mul_sum]
  rw [sum_five_reorder]
  apply Finset.sum_congr rfl
  intro A hA
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro d' hd'
  apply Finset.sum_congr rfl
  intro e he
  apply Finset.sum_congr rfl
  intro e' he'
  ring

/-! ## The fixed-matrix ordinary-pair transform -/

theorem squarefree_finset_lcm
    {I : Type*} [DecidableEq I] (s : Finset I) (f : I → ℕ)
    (hf : ∀ i ∈ s, Squarefree (f i)) : Squarefree (s.lcm f) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.lcm_insert]
      exact BoundedGaps.Maynard.squarefree_lcm
        (hf a (Finset.mem_insert_self a s))
        (ih (fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)))

theorem crossAuxiliaryColumnLcm_squarefree_of_entries
    {H : Finset ℕ} {A : CrossAuxiliaryValueMatrix H}
    (hA : ∀ ba : H × H, Squarefree (A ba)) (j : H) :
    Squarefree (crossAuxiliaryColumnLcm A j) := by
  unfold crossAuxiliaryColumnLcm
  exact squarefree_finset_lcm H.attach (fun i ↦ A (i, j))
    (fun i hi ↦ hA (i, j))

theorem crossAuxiliaryRowLcm_squarefree_of_entries
    {H : Finset ℕ} {A : CrossAuxiliaryValueMatrix H}
    (hA : ∀ ba : H × H, Squarefree (A ba)) (i : H) :
    Squarefree (crossAuxiliaryRowLcm A i) := by
  unfold crossAuxiliaryRowLcm
  exact squarefree_finset_lcm H.attach (fun j ↦ A (i, j))
    (fun j hj ↦ hA (i, j))

theorem crossAuxiliaryColumnLcm_pos_of_entries
    {H : Finset ℕ} {A : CrossAuxiliaryValueMatrix H}
    (hA : ∀ ba : H × H, 0 < A ba) (j : H) :
    0 < crossAuxiliaryColumnLcm A j := by
  apply Nat.pos_of_ne_zero
  rw [crossAuxiliaryColumnLcm, ne_eq, Finset.lcm_eq_zero_iff]
  push Not
  intro i hi
  exact (hA (i, j)).ne'

theorem crossAuxiliaryRowLcm_pos_of_entries
    {H : Finset ℕ} {A : CrossAuxiliaryValueMatrix H}
    (hA : ∀ ba : H × H, 0 < A ba) (i : H) :
    0 < crossAuxiliaryRowLcm A i := by
  apply Nat.pos_of_ne_zero
  rw [crossAuxiliaryRowLcm, ne_eq, Finset.lcm_eq_zero_iff]
  push Not
  intro j hj
  exact (hA (i, j)).ne'

theorem sum_four_reorder
    {DType SType UType M : Type*}
    [DecidableEq DType] [DecidableEq SType] [DecidableEq UType]
    [AddCommMonoid M]
    (D : Finset DType) (S : Finset SType) (U : Finset UType)
    (F : DType → DType → SType → UType → M) :
    (∑ d ∈ D, ∑ d' ∈ D, ∑ s ∈ S, ∑ u ∈ U, F d d' s u) =
      ∑ s ∈ S, ∑ u ∈ U, ∑ d ∈ D, ∑ d' ∈ D, F d d' s u := by
  calc
    (∑ d ∈ D, ∑ d' ∈ D, ∑ s ∈ S, ∑ u ∈ U, F d d' s u) =
        ∑ d ∈ D, ∑ s ∈ S, ∑ d' ∈ D, ∑ u ∈ U, F d d' s u := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.sum_comm]
    _ = ∑ s ∈ S, ∑ d ∈ D, ∑ d' ∈ D, ∑ u ∈ U, F d d' s u := by
      rw [Finset.sum_comm]
    _ = ∑ s ∈ S, ∑ d ∈ D, ∑ u ∈ U, ∑ d' ∈ D, F d d' s u := by
      apply Finset.sum_congr rfl
      intro s hs
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.sum_comm]
    _ = ∑ s ∈ S, ∑ u ∈ U, ∑ d ∈ D, ∑ d' ∈ D, F d d' s u := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [Finset.sum_comm]

/-- Exact value of one ordinary compatible-pair sum after imposing the
column (or row) lcm constraints of a fixed squarefree matrix. -/
theorem fixedLcmCompatiblePairYTransform
    {H : Finset ℕ} {R W : ℕ} {A : H → ℕ}
    {y : (H → ℕ) → ℝ}
    (hy : BoundedGaps.Maynard.IsSupportedMaynardY H R W y)
    (hASq : ∀ h : H, Squarefree (A h))
    (hAPos : ∀ h : H, 0 < A h) :
    let D := BoundedGaps.Maynard.maynardDivisorTupleSupport H R W
    (∑ d ∈ D, ∑ d' ∈ D,
      (∏ h : H, if A h ∣ Nat.lcm (d h) (d' h) then (1 : ℝ) else 0) *
        ordinaryCompatiblePairKernel
          (BoundedGaps.Maynard.maynardCoefficientFromY H R W y) d d') =
      ∑ s ∈ BoundedGaps.Maynard.crossMoebiusTupleBox H R,
        ∑ u ∈ BoundedGaps.Maynard.maynardDivisorTupleBox H R,
          crossCommonTupleWeight s u *
            (∑ x : TupleLcmAllocation A,
              tupleLcmAllocationMobiusWeight x *
                tupleLcmAllocationCommonFirstYFactor y
                  (BoundedGaps.Maynard.leftCrossLowerTuple H u s) x *
                tupleLcmAllocationCommonSecondYFactor y
                  (BoundedGaps.Maynard.rightCrossLowerTuple H u s) x) := by
  classical
  dsimp only
  let D := BoundedGaps.Maynard.maynardDivisorTupleSupport H R W
  let S := BoundedGaps.Maynard.crossMoebiusTupleBox H R
  let U := BoundedGaps.Maynard.maynardDivisorTupleBox H R
  let I : (H → ℕ) → (H → ℕ) → ℝ := fun d d' ↦
    ∏ h : H, if A h ∣ Nat.lcm (d h) (d' h) then (1 : ℝ) else 0
  let L : (∀ ab : H × H,
      ab ∈ BoundedGaps.Maynard.offDiagonalPairs H → ℕ) →
      (H → ℕ) → (H → ℕ) → ℝ := fun s u d ↦
    maynardLowerRestrictedCoefficient H R W y
      (BoundedGaps.Maynard.leftCrossLowerTuple H u s) d
  let RR : (∀ ab : H × H,
      ab ∈ BoundedGaps.Maynard.offDiagonalPairs H → ℕ) →
      (H → ℕ) → (H → ℕ) → ℝ := fun s u d' ↦
    maynardLowerRestrictedCoefficient H R W y
      (BoundedGaps.Maynard.rightCrossLowerTuple H u s) d'
  change (∑ d ∈ D, ∑ d' ∈ D,
      I d d' * ordinaryCompatiblePairKernel
        (BoundedGaps.Maynard.maynardCoefficientFromY H R W y) d d') = _
  calc
    (∑ d ∈ D, ∑ d' ∈ D,
        I d d' * ordinaryCompatiblePairKernel
          (BoundedGaps.Maynard.maynardCoefficientFromY H R W y) d d') =
        ∑ d ∈ D, ∑ d' ∈ D, ∑ s ∈ S, ∑ u ∈ U,
          I d d' * (crossCommonTupleWeight s u * (L s u d * RR s u d')) := by
      apply Finset.sum_congr rfl
      intro d hdMem
      apply Finset.sum_congr rfl
      intro d' hd'Mem
      rw [ordinaryCompatiblePairKernel_eq_lowerRestrictedSum
        (BoundedGaps.Maynard.isMaynardDivisorTuple_of_mem_support hdMem)
        (BoundedGaps.Maynard.isMaynardDivisorTuple_of_mem_support hd'Mem)]
      simp_rw [Finset.mul_sum]
      rfl
    _ = ∑ s ∈ S, ∑ u ∈ U, ∑ d ∈ D, ∑ d' ∈ D,
          I d d' * (crossCommonTupleWeight s u * (L s u d * RR s u d')) := by
      exact sum_four_reorder D S U _
    _ = ∑ s ∈ S, ∑ u ∈ U,
          crossCommonTupleWeight s u *
            (∑ d ∈ D, ∑ d' ∈ D, I d d' * (L s u d * RR s u d')) := by
      apply Finset.sum_congr rfl
      intro s hs
      apply Finset.sum_congr rfl
      intro u hu
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      apply Finset.sum_congr rfl
      intro d' hd'
      ring
    _ = _ := by
      apply Finset.sum_congr rfl
      intro s hs
      apply Finset.sum_congr rfl
      intro u hu
      rw [maynardY_pair_lcmAllocation_of_cross_eq hy hASq hAPos hu hs]

/-! ## Exact coefficient-summed doubled transform -/

/-- Factor a fixed matrix indicator against arbitrary functions of the two
ordered coefficient pairs. -/
theorem crossAuxiliary_fourfold_pairSum_eq_pairProducts
    {H : Finset ℕ} (A : CrossAuxiliaryValueMatrix H)
    (DD DE : Finset (H → ℕ))
    (F G : (H → ℕ) → (H → ℕ) → ℝ) :
    (∑ d ∈ DD, ∑ d' ∈ DD, ∑ e ∈ DE, ∑ e' ∈ DE,
      crossAuxiliaryGcdIndicator A d e d' e' *
        (F d d' * G e e')) =
      (∑ d ∈ DD, ∑ d' ∈ DD,
        (∏ j : H,
          if crossAuxiliaryColumnLcm A j ∣ Nat.lcm (d j) (d' j) then
            (1 : ℝ) else 0) * F d d') *
      (∑ e ∈ DE, ∑ e' ∈ DE,
        (∏ i : H,
          if crossAuxiliaryRowLcm A i ∣ Nat.lcm (e i) (e' i) then
            (1 : ℝ) else 0) * G e e') := by
  classical
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d' hd'
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e' he'
  rw [crossAuxiliaryGcdIndicator_eq_columns_mul_rows]
  ring

/-- The finite Y-transform value attached to one coordinate-lcm tuple of a
fixed auxiliary matrix. -/
noncomputable def fixedLcmCompatiblePairYValue
    {H : Finset ℕ} (R : ℕ) (y : (H → ℕ) → ℝ) (A : H → ℕ) : ℝ :=
  ∑ s ∈ BoundedGaps.Maynard.crossMoebiusTupleBox H R,
    ∑ u ∈ BoundedGaps.Maynard.maynardDivisorTupleBox H R,
      crossCommonTupleWeight s u *
        (∑ x : TupleLcmAllocation A,
          tupleLcmAllocationMobiusWeight x *
            tupleLcmAllocationCommonFirstYFactor y
              (BoundedGaps.Maynard.leftCrossLowerTuple H u s) x *
            tupleLcmAllocationCommonSecondYFactor y
              (BoundedGaps.Maynard.rightCrossLowerTuple H u s) x)

/-- Complete finite two-family Y-transform of the unpinned doubled kernel. -/
noncomputable def doubledSelbergCrossYKernel
    (H : Finset ℕ) (RD RE : ℕ)
    (yD yE : (H → ℕ) → ℝ) (m q : ℕ) : ℝ :=
  ∑ A ∈ crossAuxiliarySquarefreeValueMatrixBox H (RD * RD),
    crossAuxiliaryAffineMobiusWeight m q A *
      (fixedLcmCompatiblePairYValue RD yD (crossAuxiliaryColumnLcm A) *
        fixedLcmCompatiblePairYValue RE yE (crossAuxiliaryRowLcm A))

/-! ## The all-one matrix term -/

/-- The distinguished value matrix with no cross-family collision prime. -/
def oneCrossAuxiliaryValueMatrix (H : Finset ℕ) :
    CrossAuxiliaryValueMatrix H :=
  fun _ ↦ 1

@[simp] theorem oneCrossAuxiliaryValueMatrix_apply
    {H : Finset ℕ} (ba : H × H) :
    oneCrossAuxiliaryValueMatrix H ba = 1 := by
  rfl

@[simp] theorem crossAuxiliaryColumnLcm_one
    {H : Finset ℕ} (j : H) :
    crossAuxiliaryColumnLcm (oneCrossAuxiliaryValueMatrix H) j = 1 := by
  unfold crossAuxiliaryColumnLcm
  change H.attach.lcm (fun _ ↦ 1) = 1
  induction H.attach using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.lcm_insert]
      simp [ih]

@[simp] theorem crossAuxiliaryRowLcm_one
    {H : Finset ℕ} (i : H) :
    crossAuxiliaryRowLcm (oneCrossAuxiliaryValueMatrix H) i = 1 := by
  unfold crossAuxiliaryRowLcm
  change H.attach.lcm (fun _ ↦ 1) = 1
  induction H.attach using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.lcm_insert]
      simp [ih]

@[simp] theorem affineCollisionWeight_one
    {H : Finset ℕ} (m q : ℕ) (ba : H × H) :
    affineCollisionWeight m q ba 1 = 1 := by
  unfold affineCollisionWeight affineCollisionWeightAF
  rw [ArithmeticFunction.mul_apply_one]
  have htarget : (affineCompatibilityTargetAF m q ba) 1 = 1 := by
    unfold affineCompatibilityTargetAF
    dsimp
    rw [if_pos (by
      change (m * (ba.2.1 * q) + 1) % 1 =
        (m * (ba.1.1 * q)) % 1
      omega)]
    norm_num
  rw [htarget]
  norm_num [ArithmeticFunction.moebius_apply_one]

@[simp] theorem affineCompatibilityTargetAF_apply
    {H : Finset ℕ} (m q : ℕ) (ba : H × H) (n : ℕ) :
    affineCompatibilityTargetAF m q ba n =
      if m * (ba.2.1 * q) + 1 ≡ m * (ba.1.1 * q) [MOD n] then
        (n : ℝ)
      else 0 := by
  unfold affineCompatibilityTargetAF
  rfl

/-- The local compatibility-weighted identity function is multiplicative in
the modulus. -/
theorem affineCompatibilityTargetAF_isMultiplicative
    {H : Finset ℕ} (m q : ℕ) (ba : H × H) :
    ArithmeticFunction.IsMultiplicative
      (affineCompatibilityTargetAF m q ba) := by
  constructor
  · rw [affineCompatibilityTargetAF_apply]
    rw [if_pos (by
      change (m * (ba.2.1 * q) + 1) % 1 =
        (m * (ba.1.1 * q)) % 1
      omega)]
    norm_num
  · intro a b hab
    simp only [affineCompatibilityTargetAF_apply]
    have hiff := Nat.modEq_and_modEq_iff_modEq_mul
      (a := m * (ba.2.1 * q) + 1) (b := m * (ba.1.1 * q))
      (m := a) (n := b) hab
    by_cases ha :
        m * (ba.2.1 * q) + 1 ≡ m * (ba.1.1 * q) [MOD a]
    · by_cases hb :
          m * (ba.2.1 * q) + 1 ≡ m * (ba.1.1 * q) [MOD b]
      · have habCollision := hiff.mp ⟨ha, hb⟩
        simp [ha, hb, habCollision]
      · have habCollision :
            ¬m * (ba.2.1 * q) + 1 ≡
              m * (ba.1.1 * q) [MOD a * b] :=
          fun h ↦ hb (hiff.mpr h).2
        simp [ha, hb, habCollision]
    · have habCollision :
          ¬m * (ba.2.1 * q) + 1 ≡
            m * (ba.1.1 * q) [MOD a * b] :=
        fun h ↦ ha (hiff.mpr h).1
      by_cases hb :
          m * (ba.2.1 * q) + 1 ≡ m * (ba.1.1 * q) [MOD b]
      · simp [ha, hb, habCollision]
      · simp [ha, hb, habCollision]

/-- Hence the M\"obius-inverted affine collision weight is itself
multiplicative. -/
theorem affineCollisionWeightAF_isMultiplicative
    {H : Finset ℕ} (m q : ℕ) (ba : H × H) :
    ArithmeticFunction.IsMultiplicative
      (affineCollisionWeightAF m q ba) := by
  exact ArithmeticFunction.isMultiplicative_moebius.intCast.mul
    (affineCompatibilityTargetAF_isMultiplicative m q ba)

/-- On a squarefree modulus the affine collision weight is the product of
its explicit prime-local weights. -/
theorem affineCollisionWeight_eq_prod_primeFactors
    {H : Finset ℕ} (m q : ℕ) (ba : H × H) {n : ℕ}
    (hn : Squarefree n) :
    affineCollisionWeight m q ba n =
      ∏ p ∈ n.primeFactors, affineCollisionWeight m q ba p := by
  unfold affineCollisionWeight
  exact (ArithmeticFunction.IsMultiplicative.prod_primeFactors
    (affineCollisionWeightAF_isMultiplicative m q ba) hn).symm

/-- At a prime, the signed affine M\"obius weight is `p - 1` on an
exceptional affine collision and `-1` otherwise.  This is the local
first-order/square-summable dichotomy used in the singular-factor bound. -/
theorem affineCollisionWeight_prime
    {H : Finset ℕ} (m q : ℕ) (ba : H × H) {p : ℕ}
    (hp : p.Prime) :
    affineCollisionWeight m q ba p =
      if m * (ba.2.1 * q) + 1 ≡ m * (ba.1.1 * q) [MOD p] then
        (p : ℝ) - 1
      else -1 := by
  have hsum := sum_affineCollisionWeight_divisors m q ba p
  rw [hp.divisors] at hsum
  have honeNotMem : 1 ∉ ({p} : Finset ℕ) := by
    simp only [Finset.mem_singleton]
    exact fun h ↦ hp.ne_one h.symm
  rw [Finset.sum_insert honeNotMem, Finset.sum_singleton,
    affineCollisionWeight_one] at hsum
  by_cases hcollision :
      m * (ba.2.1 * q) + 1 ≡ m * (ba.1.1 * q) [MOD p]
  · rw [if_pos hcollision] at hsum ⊢
    linarith
  · rw [if_neg hcollision] at hsum ⊢
    linarith

/-- The congruence in the prime-local affine weight is exactly divisibility
of the signed cross-affine difference used by the singular-series modules.
This lemma is the interface between the coefficient transform and the
already checked auxiliary-prime averaging estimates. -/
theorem affineCollisionWeight_prime_eq_crossAffineDifference
    {H : Finset ℕ} (m q : ℕ) (ba : H × H) {p : ℕ}
    (hp : p.Prime) :
    affineCollisionWeight m q ba p =
      if (p : ℤ) ∣ crossAffineDifference m q ba then
        (p : ℝ) - 1
      else -1 := by
  rw [affineCollisionWeight_prime m q ba hp]
  apply if_congr
  · simpa [crossAffineDifference] using
    (Nat.modEq_iff_dvd (n := p)
      (a := m * (ba.2.1 * q) + 1)
      (b := m * (ba.1.1 * q)))
  · rfl
  · rfl

/-- A diagonal matrix edge is never exceptional at a prime: its two affine
constants differ by one.  Hence every diagonal prime contributes the generic
local weight `-1`. -/
@[simp] theorem affineCollisionWeight_prime_diagonal
    {H : Finset ℕ} (m q : ℕ) (h : H) {p : ℕ}
    (hp : p.Prime) :
    affineCollisionWeight m q (h, h) p = -1 := by
  rw [affineCollisionWeight_prime_eq_crossAffineDifference m q (h, h) hp]
  rw [if_neg]
  intro hdiv
  have hpNegOne : (p : ℤ) ∣ (-1 : ℤ) := by
    simpa [crossAffineDifference] using hdiv
  have hpOne : (p : ℤ) ∣ (1 : ℤ) := by
    exact Int.dvd_neg.mp hpNegOne
  exact hp.not_dvd_one (Int.natCast_dvd_natCast.mp hpOne)

/-- Absolute prime-local weight: an exceptional affine collision costs
`p - 1`, while every generic prime has unit magnitude. -/
theorem abs_affineCollisionWeight_prime
    {H : Finset ℕ} (m q : ℕ) (ba : H × H) {p : ℕ}
    (hp : p.Prime) :
    |affineCollisionWeight m q ba p| =
      if (p : ℤ) ∣ crossAffineDifference m q ba then
        (p : ℝ) - 1
      else 1 := by
  rw [affineCollisionWeight_prime_eq_crossAffineDifference m q ba hp]
  by_cases hcollision : (p : ℤ) ∣ crossAffineDifference m q ba
  · rw [if_pos hcollision, if_pos hcollision, abs_of_nonneg]
    exact sub_nonneg.mpr (by exact_mod_cast hp.one_lt.le)
  · simp [hcollision]

@[simp] theorem crossAuxiliaryAffineMobiusWeight_one
    {H : Finset ℕ} (m q : ℕ) :
    crossAuxiliaryAffineMobiusWeight m q
        (oneCrossAuxiliaryValueMatrix H) = 1 := by
  simp [crossAuxiliaryAffineMobiusWeight]

theorem oneCrossAuxiliaryValueMatrix_mem_squarefreeBox
    {H : Finset ℕ} {Q : ℕ} (hQ : 0 < Q) :
    oneCrossAuxiliaryValueMatrix H ∈
      crossAuxiliarySquarefreeValueMatrixBox H Q := by
  rw [mem_crossAuxiliarySquarefreeValueMatrixBox_iff]
  exact ⟨fun _ ↦ ⟨by simp, hQ⟩, fun _ ↦ squarefree_one⟩

/-- Imposing the all-one lcm tuple does nothing, so its transformed value is
exactly the ordinary compatible Maynard quadratic. -/
theorem fixedLcmCompatiblePairYValue_one
    {H : Finset ℕ} {R W : ℕ} {y : (H → ℕ) → ℝ}
    (hy : BoundedGaps.Maynard.IsSupportedMaynardY H R W y) :
    fixedLcmCompatiblePairYValue R y (fun _ : H ↦ 1) =
      BoundedGaps.Maynard.compatibleDivisorPairNormalizedMainSum H
        (BoundedGaps.Maynard.maynardDivisorTupleSupport H R W)
        (BoundedGaps.Maynard.maynardCoefficientFromY H R W y) := by
  have htransform := fixedLcmCompatiblePairYTransform hy
    (A := fun _ : H ↦ 1) (fun _ ↦ squarefree_one) (fun _ ↦ by simp)
  rw [show fixedLcmCompatiblePairYValue R y (fun _ : H ↦ 1) =
      ∑ s ∈ BoundedGaps.Maynard.crossMoebiusTupleBox H R,
        ∑ u ∈ BoundedGaps.Maynard.maynardDivisorTupleBox H R,
          crossCommonTupleWeight s u *
            (∑ x : TupleLcmAllocation (fun _ : H ↦ 1),
              tupleLcmAllocationMobiusWeight x *
                tupleLcmAllocationCommonFirstYFactor y
                  (BoundedGaps.Maynard.leftCrossLowerTuple H u s) x *
                tupleLcmAllocationCommonSecondYFactor y
                  (BoundedGaps.Maynard.rightCrossLowerTuple H u s) x) by rfl]
  rw [← htransform]
  unfold BoundedGaps.Maynard.compatibleDivisorPairNormalizedMainSum
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d' hd'
  by_cases hcross : BoundedGaps.Maynard.IsCrossCoordinateCoprime H d d'
  · simp [ordinaryCompatiblePairKernel, hcross, firstLcmProduct,
      BoundedGaps.Maynard.divisorTupleLcm]
  · simp [ordinaryCompatiblePairKernel, hcross]

/-- A fixed lcm constraint that places a common prime in two distinct
coordinates is incompatible with every ordinary compatible Maynard pair.
Consequently its complete transformed value vanishes. -/
theorem fixedLcmCompatiblePairYValue_eq_zero_of_not_coprime
    {H : Finset ℕ} {R W : ℕ} {y : (H → ℕ) → ℝ}
    {A : H → ℕ} (hy : BoundedGaps.Maynard.IsSupportedMaynardY H R W y)
    (hASq : ∀ h : H, Squarefree (A h))
    (hAPos : ∀ h : H, 0 < A h)
    {a b : H} (hab : a ≠ b) (hnot : ¬(A a).Coprime (A b)) :
    fixedLcmCompatiblePairYValue R y A = 0 := by
  rw [show fixedLcmCompatiblePairYValue R y A =
      ∑ s ∈ BoundedGaps.Maynard.crossMoebiusTupleBox H R,
        ∑ u ∈ BoundedGaps.Maynard.maynardDivisorTupleBox H R,
          crossCommonTupleWeight s u *
            (∑ x : TupleLcmAllocation A,
              tupleLcmAllocationMobiusWeight x *
                tupleLcmAllocationCommonFirstYFactor y
                  (BoundedGaps.Maynard.leftCrossLowerTuple H u s) x *
                tupleLcmAllocationCommonSecondYFactor y
                  (BoundedGaps.Maynard.rightCrossLowerTuple H u s) x) by rfl]
  rw [← fixedLcmCompatiblePairYTransform hy hASq hAPos]
  apply Finset.sum_eq_zero
  intro d hd
  apply Finset.sum_eq_zero
  intro d' hd'
  have hdData := BoundedGaps.Maynard.isMaynardDivisorTuple_of_mem_support hd
  have hd'Data := BoundedGaps.Maynard.isMaynardDivisorTuple_of_mem_support hd'
  by_cases hcross : BoundedGaps.Maynard.IsCrossCoordinateCoprime H d d'
  · have hlcmCoprime := pairwise_lcm_of_maynard_cross
      hdData hd'Data hcross hab
    by_cases ha : A a ∣ Nat.lcm (d a) (d' a)
    · by_cases hb : A b ∣ Nat.lcm (d b) (d' b)
      · exact (hnot (Nat.Coprime.of_dvd ha hb hlcmCoprime)).elim
      · have hprod :
            (∏ h : H,
              if A h ∣ Nat.lcm (d h) (d' h) then (1 : ℝ) else 0) = 0 :=
          Finset.prod_eq_zero (Finset.mem_univ b) (by simp [hb])
        rw [hprod]
        ring
    · have hprod :
          (∏ h : H,
            if A h ∣ Nat.lcm (d h) (d' h) then (1 : ℝ) else 0) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ a) (by simp [ha])
      rw [hprod]
      ring
  · simp [ordinaryCompatiblePairKernel, hcross]

/-- A matrix has matching prime incidence when each prime occurs in at most
one column and at most one row.  These are exactly the matrices that can
survive the two ordinary within-family compatibility conditions. -/
def IsCrossAuxiliaryPrimeMatching
    {H : Finset ℕ} (A : CrossAuxiliaryValueMatrix H) : Prop :=
  (∀ a b : H, a ≠ b →
      (crossAuxiliaryColumnLcm A a).Coprime
        (crossAuxiliaryColumnLcm A b)) ∧
    ∀ a b : H, a ≠ b →
      (crossAuxiliaryRowLcm A a).Coprime
        (crossAuxiliaryRowLcm A b)

/-- On the matching locus, distinct matrix entries are coprime.  Indeed,
two distinct positions differ in their column or in their row, and each
entry divides the corresponding column or row lcm. -/
theorem crossAuxiliary_entries_coprime_of_matching
    {H : Finset ℕ} {A : CrossAuxiliaryValueMatrix H}
    (hmatch : IsCrossAuxiliaryPrimeMatching A)
    {ba bb : H × H} (hne : ba ≠ bb) :
    (A ba).Coprime (A bb) := by
  have hcolDvd (i j : H) :
      A (i, j) ∣ crossAuxiliaryColumnLcm A j := by
    unfold crossAuxiliaryColumnLcm
    exact Finset.dvd_lcm (Finset.mem_univ i)
  have hrowDvd (i j : H) :
      A (i, j) ∣ crossAuxiliaryRowLcm A i := by
    unfold crossAuxiliaryRowLcm
    exact Finset.dvd_lcm (Finset.mem_univ j)
  by_cases hcol : ba.2 = bb.2
  · have hrow : ba.1 ≠ bb.1 := by
      intro h
      apply hne
      exact Prod.ext h hcol
    exact Nat.Coprime.of_dvd
      (hrowDvd ba.1 ba.2) (hrowDvd bb.1 bb.2)
      (hmatch.2 ba.1 bb.1 hrow)
  · exact Nat.Coprime.of_dvd
      (hcolDvd ba.1 ba.2) (hcolDvd bb.1 bb.2)
      (hmatch.1 ba.2 bb.2 hcol)

/-- On the matching locus a prime determines at most one matrix edge. -/
theorem eq_of_prime_dvd_crossAuxiliary_entries_of_matching
    {H : Finset ℕ} {A : CrossAuxiliaryValueMatrix H}
    (hmatch : IsCrossAuxiliaryPrimeMatching A)
    {p : ℕ} (hp : p.Prime) {ba bb : H × H}
    (hpba : p ∣ A ba) (hpbb : p ∣ A bb) : ba = bb := by
  by_contra hne
  have hcop := crossAuxiliary_entries_coprime_of_matching hmatch hne
  exact hp.ne_one (Nat.eq_one_of_dvd_coprimes hcop hpba hpbb)

/-- A squarefree matching matrix has squarefree total entry product.  This
packages the fact that every rough prime belongs to a unique matrix edge. -/
theorem squarefree_crossAuxiliary_entryProduct_of_matching
    {H : Finset ℕ} {A : CrossAuxiliaryValueMatrix H}
    (hmatch : IsCrossAuxiliaryPrimeMatching A)
    (hsq : ∀ ba : H × H, Squarefree (A ba)) :
    Squarefree (∏ ba : H × H, A ba) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro ba hba bb hbb hne
    exact Nat.coprime_iff_isRelPrime.mp
      (crossAuxiliary_entries_coprime_of_matching hmatch hne)
  · intro ba hba
    exact hsq ba

/-- For a squarefree auxiliary matrix, the complete signed affine weight
is already an explicit product of its prime-local edge weights.  On the
matching locus the prime factors occurring in the different inner products
are disjoint, by `crossAuxiliary_entries_coprime_of_matching`; this is the
finite Euler-product form used by the quantitative tail estimate. -/
theorem crossAuxiliaryAffineMobiusWeight_eq_entryPrimeProducts
    {H : Finset ℕ} (m q : ℕ) {A : CrossAuxiliaryValueMatrix H}
    (hsq : ∀ ba : H × H, Squarefree (A ba)) :
    crossAuxiliaryAffineMobiusWeight m q A =
      ∏ ba : H × H,
        ∏ p ∈ (A ba).primeFactors, affineCollisionWeight m q ba p := by
  unfold crossAuxiliaryAffineMobiusWeight
  apply Finset.prod_congr rfl
  intro ba hba
  exact affineCollisionWeight_eq_prod_primeFactors m q ba (hsq ba)

/-- Absolute Euler-product form of the matrix weight.  This separates the
first-order exceptional factors from the unit generic factors without any
inequality or asymptotic argument. -/
theorem abs_crossAuxiliaryAffineMobiusWeight_eq_entryPrimeProducts
    {H : Finset ℕ} (m q : ℕ) {A : CrossAuxiliaryValueMatrix H}
    (hsq : ∀ ba : H × H, Squarefree (A ba)) :
    |crossAuxiliaryAffineMobiusWeight m q A| =
      ∏ ba : H × H,
        ∏ p ∈ (A ba).primeFactors,
          if (p : ℤ) ∣ crossAffineDifference m q ba then
            (p : ℝ) - 1
          else 1 := by
  rw [crossAuxiliaryAffineMobiusWeight_eq_entryPrimeProducts m q hsq,
    Finset.abs_prod]
  apply Finset.prod_congr rfl
  intro ba hba
  rw [Finset.abs_prod]
  apply Finset.prod_congr rfl
  intro p hpMem
  exact abs_affineCollisionWeight_prime m q ba
    (Nat.prime_of_mem_primeFactors hpMem)

/-- The coefficient-summed contribution of every nonmatching matrix is
zero, before taking any limit or absolute-value estimate. -/
theorem crossAuxiliaryYMatrixTerm_eq_zero_of_not_matching
    {H : Finset ℕ} {RD RE WD WE m q : ℕ}
    {yD yE : (H → ℕ) → ℝ}
    {A : CrossAuxiliaryValueMatrix H}
    (hA : A ∈ crossAuxiliarySquarefreeValueMatrixBox H (RD * RD))
    (hyD : BoundedGaps.Maynard.IsSupportedMaynardY H RD WD yD)
    (hyE : BoundedGaps.Maynard.IsSupportedMaynardY H RE WE yE)
    (hnot : ¬IsCrossAuxiliaryPrimeMatching A) :
    crossAuxiliaryAffineMobiusWeight m q A *
        (fixedLcmCompatiblePairYValue RD yD (crossAuxiliaryColumnLcm A) *
          fixedLcmCompatiblePairYValue RE yE (crossAuxiliaryRowLcm A)) = 0 := by
  have hAData := mem_crossAuxiliarySquarefreeValueMatrixBox_iff.mp hA
  have hentryPos : ∀ ba : H × H, 0 < A ba := fun ba ↦ (hAData.1 ba).1
  have hentrySq : ∀ ba : H × H, Squarefree (A ba) := hAData.2
  by_cases hcol : ∀ a b : H, a ≠ b →
      (crossAuxiliaryColumnLcm A a).Coprime
        (crossAuxiliaryColumnLcm A b)
  · have hrowNot : ¬∀ a b : H, a ≠ b →
        (crossAuxiliaryRowLcm A a).Coprime
          (crossAuxiliaryRowLcm A b) :=
      fun hrow ↦ hnot ⟨hcol, hrow⟩
    push Not at hrowNot
    obtain ⟨a, b, hab, hcop⟩ := hrowNot
    have hzero := fixedLcmCompatiblePairYValue_eq_zero_of_not_coprime
      hyE (crossAuxiliaryRowLcm_squarefree_of_entries hentrySq)
        (crossAuxiliaryRowLcm_pos_of_entries hentryPos) hab hcop
    rw [hzero]
    ring
  · push Not at hcol
    obtain ⟨a, b, hab, hcop⟩ := hcol
    have hzero := fixedLcmCompatiblePairYValue_eq_zero_of_not_coprime
      hyD (crossAuxiliaryColumnLcm_squarefree_of_entries hentrySq)
        (crossAuxiliaryColumnLcm_pos_of_entries hentryPos) hab hcop
    rw [hzero]
    ring

/-- The fixed squarefree matrix box restricted to the prime-matching locus. -/
def crossAuxiliaryMatchingValueMatrixBox
    (H : Finset ℕ) (Q : ℕ) : Finset (CrossAuxiliaryValueMatrix H) :=
  (crossAuxiliarySquarefreeValueMatrixBox H Q).filter
    IsCrossAuxiliaryPrimeMatching

/-- Nonmatching matrices may be deleted from the complete cross-`Y` kernel
without changing its value. -/
theorem doubledSelbergCrossYKernel_eq_matching_sum
    {H : Finset ℕ} {RD RE WD WE m q : ℕ}
    {yD yE : (H → ℕ) → ℝ}
    (hyD : BoundedGaps.Maynard.IsSupportedMaynardY H RD WD yD)
    (hyE : BoundedGaps.Maynard.IsSupportedMaynardY H RE WE yE) :
    doubledSelbergCrossYKernel H RD RE yD yE m q =
      ∑ A ∈ crossAuxiliaryMatchingValueMatrixBox H (RD * RD),
        crossAuxiliaryAffineMobiusWeight m q A *
          (fixedLcmCompatiblePairYValue RD yD
              (crossAuxiliaryColumnLcm A) *
            fixedLcmCompatiblePairYValue RE yE
              (crossAuxiliaryRowLcm A)) := by
  classical
  unfold doubledSelbergCrossYKernel crossAuxiliaryMatchingValueMatrixBox
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro A hA
  by_cases hmatch : IsCrossAuxiliaryPrimeMatching A
  · rw [if_pos hmatch]
  · rw [if_neg hmatch,
      crossAuxiliaryYMatrixTerm_eq_zero_of_not_matching hA hyD hyE hmatch]

/-- The part of the complete cross-`Y` kernel supported on matrices other
than the all-one matrix.  Its local factors are the genuine rough
cross-family collision corrections. -/
noncomputable def doubledSelbergCrossYTail
    (H : Finset ℕ) (RD RE : ℕ)
    (yD yE : (H → ℕ) → ℝ) (m q : ℕ) : ℝ :=
  ∑ A ∈ (crossAuxiliarySquarefreeValueMatrixBox H (RD * RD)).erase
      (oneCrossAuxiliaryValueMatrix H),
    crossAuxiliaryAffineMobiusWeight m q A *
      (fixedLcmCompatiblePairYValue RD yD (crossAuxiliaryColumnLcm A) *
        fixedLcmCompatiblePairYValue RE yE (crossAuxiliaryRowLcm A))

/-- Exact separation of the ordinary tensor main term from all nontrivial
cross-family collision matrices. -/
theorem doubledSelbergCrossYKernel_eq_quadratics_add_tail
    {H : Finset ℕ} {RD RE WD WE m q : ℕ}
    {yD yE : (H → ℕ) → ℝ}
    (hRD : 0 < RD)
    (hyD : BoundedGaps.Maynard.IsSupportedMaynardY H RD WD yD)
    (hyE : BoundedGaps.Maynard.IsSupportedMaynardY H RE WE yE) :
    doubledSelbergCrossYKernel H RD RE yD yE m q =
      BoundedGaps.Maynard.compatibleDivisorPairNormalizedMainSum H
          (BoundedGaps.Maynard.maynardDivisorTupleSupport H RD WD)
          (BoundedGaps.Maynard.maynardCoefficientFromY H RD WD yD) *
        BoundedGaps.Maynard.compatibleDivisorPairNormalizedMainSum H
          (BoundedGaps.Maynard.maynardDivisorTupleSupport H RE WE)
          (BoundedGaps.Maynard.maynardCoefficientFromY H RE WE yE) +
      doubledSelbergCrossYTail H RD RE yD yE m q := by
  classical
  let oneA := oneCrossAuxiliaryValueMatrix H
  let box := crossAuxiliarySquarefreeValueMatrixBox H (RD * RD)
  let term : CrossAuxiliaryValueMatrix H → ℝ := fun A ↦
    crossAuxiliaryAffineMobiusWeight m q A *
      (fixedLcmCompatiblePairYValue RD yD (crossAuxiliaryColumnLcm A) *
        fixedLcmCompatiblePairYValue RE yE (crossAuxiliaryRowLcm A))
  have hone : oneA ∈ box := by
    exact oneCrossAuxiliaryValueMatrix_mem_squarefreeBox
      (Nat.mul_pos hRD hRD)
  have hsplit := Finset.sum_erase_add (s := box) (f := term) hone
  have honeTerm : term oneA =
      BoundedGaps.Maynard.compatibleDivisorPairNormalizedMainSum H
          (BoundedGaps.Maynard.maynardDivisorTupleSupport H RD WD)
          (BoundedGaps.Maynard.maynardCoefficientFromY H RD WD yD) *
        BoundedGaps.Maynard.compatibleDivisorPairNormalizedMainSum H
          (BoundedGaps.Maynard.maynardDivisorTupleSupport H RE WE)
          (BoundedGaps.Maynard.maynardCoefficientFromY H RE WE yE) := by
    dsimp [term, oneA]
    rw [crossAuxiliaryAffineMobiusWeight_one]
    simp only [one_mul]
    have hcol : crossAuxiliaryColumnLcm
        (oneCrossAuxiliaryValueMatrix H) = fun _ : H ↦ 1 := by
      funext j
      exact crossAuxiliaryColumnLcm_one j
    have hrow : crossAuxiliaryRowLcm
        (oneCrossAuxiliaryValueMatrix H) = fun _ : H ↦ 1 := by
      funext i
      exact crossAuxiliaryRowLcm_one i
    rw [hcol, hrow, fixedLcmCompatiblePairYValue_one hyD,
      fixedLcmCompatiblePairYValue_one hyE]
  unfold doubledSelbergCrossYKernel doubledSelbergCrossYTail
  change (∑ A ∈ box, term A) = _
  change _ = _ + ∑ A ∈ box.erase oneA, term A
  rw [← honeTerm]
  linarith

theorem doubledSelbergAffineBoxOuterKernel_eq_crossY
    {H : Finset ℕ} {RD RE W m q : ℕ}
    {yD yE : (H → ℕ) → ℝ}
    (hyD : BoundedGaps.Maynard.IsSupportedMaynardY H RD W yD)
    (hyE : BoundedGaps.Maynard.IsSupportedMaynardY H RE (W * m) yE) :
    doubledSelbergAffineBoxOuterKernel H RD
        (BoundedGaps.Maynard.maynardDivisorTupleSupport H RD W)
        (BoundedGaps.Maynard.maynardDivisorTupleSupport H RE (W * m))
        (BoundedGaps.Maynard.maynardCoefficientFromY H RD W yD)
        (BoundedGaps.Maynard.maynardCoefficientFromY H RE (W * m) yE)
        m q =
      doubledSelbergCrossYKernel H RD RE yD yE m q := by
  classical
  unfold doubledSelbergAffineBoxOuterKernel doubledSelbergCrossYKernel
  apply Finset.sum_congr rfl
  intro A hA
  have hmem := mem_crossAuxiliarySquarefreeValueMatrixBox_iff.mp hA
  have hentryPos : ∀ ba : H × H, 0 < A ba := fun ba ↦ (hmem.1 ba).1
  have hentrySq : ∀ ba : H × H, Squarefree (A ba) := hmem.2
  rw [crossAuxiliary_fourfold_pairSum_eq_pairProducts]
  rw [fixedLcmCompatiblePairYTransform hyD
    (crossAuxiliaryColumnLcm_squarefree_of_entries hentrySq)
    (crossAuxiliaryColumnLcm_pos_of_entries hentryPos)]
  rw [fixedLcmCompatiblePairYTransform hyE
    (crossAuxiliaryRowLcm_squarefree_of_entries hentrySq)
    (crossAuxiliaryRowLcm_pos_of_entries hentryPos)]
  rfl

/-- Exact coefficient-summed two-family Y-transform for the genuine
affine-compatible doubled normalization kernel. -/
theorem doubledSelbergCrossTotientKernel_eq_crossY_standard
    (H : Finset ℕ) (RD RE W m q : ℕ)
    (yD yE : (H → ℕ) → ℝ)
    (hyD : BoundedGaps.Maynard.IsSupportedMaynardY H RD W yD)
    (hyE : BoundedGaps.Maynard.IsSupportedMaynardY H RE (W * m) yE)
    (hm : 0 < m) (hq : q.Prime) (hRDq : RD ≤ q) (hREq : RE ≤ q)
    (hcover : BoundedGaps.Maynard.CoversShiftDifferencePrimes H W) :
    doubledSelbergCrossTotientKernel H
        (BoundedGaps.Maynard.maynardDivisorTupleSupport H RD W)
        (BoundedGaps.Maynard.maynardDivisorTupleSupport H RE (W * m))
        (fun d e ↦
          BoundedGaps.Maynard.maynardCoefficientFromY H RD W yD d *
            BoundedGaps.Maynard.maynardCoefficientFromY H RE (W * m) yE e)
        m q =
      doubledSelbergCrossYKernel H RD RE yD yE m q := by
  rw [doubledSelbergCrossTotientKernel_eq_affineBox_standard
    H RD RE W m q
    (BoundedGaps.Maynard.maynardCoefficientFromY H RD W yD)
    (BoundedGaps.Maynard.maynardCoefficientFromY H RE (W * m) yE)
    hm hq hRDq hREq hcover]
  rw [doubledSelbergAffineBoxKernel_eq_outer]
  exact doubledSelbergAffineBoxOuterKernel_eq_crossY hyD hyE

end

end Erdos4b
