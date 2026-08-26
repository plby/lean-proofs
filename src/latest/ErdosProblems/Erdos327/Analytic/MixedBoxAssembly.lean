import ErdosProblems.Erdos327.Analytic.MixedOuterWeight
import ErdosProblems.Erdos327.Analytic.ThreeFormBoxSharp
import ErdosProblems.Erdos327.Analytic.ResidualMeanBridge

/-!
# Assembly of one finite mixed-coordinate box

This file stops before choosing asymptotic parameters or summing the
boxes.  It bounds the coordinates in one standard three-form box by the
product of the finite mixed sieve sum and the one-variable residual
moment, and then inserts their explicit analytic estimates.
-/

namespace Erdos327.Analytic

open Finset Real
open scoped ArithmeticFunction.Omega BigOperators

noncomputable section

/-- Mixed coordinates lying in one of the standard boxes consumed by
`finiteWeightBoxSum`: `X ≤ u < 2X` and `1 ≤ w ≤ 8X`. -/
noncomputable def mixedCoordinateBoxBlock
    (L N : ℕ) (Ab Kb Ao Ko : ℝ) (X : ℕ) : Finset MixedTriple :=
  (mixedCoordinateSet L N Ab Kb Ao Ko).filter fun q ↦
    mixedU q ∈ Ico X (2 * X) ∧ mixedW q ∈ Icc 1 (8 * X)

@[simp] theorem mem_mixedCoordinateBoxBlock
    {L N X : ℕ} {Ab Kb Ao Ko : ℝ} {q : MixedTriple} :
    q ∈ mixedCoordinateBoxBlock L N Ab Kb Ao Ko X ↔
      q ∈ mixedCoordinateSet L N Ab Kb Ao Ko ∧
        mixedU q ∈ Ico X (2 * X) ∧
        mixedW q ∈ Icc 1 (8 * X) := by
  simp [mixedCoordinateBoxBlock]

/-- The common linear form in a standard mixed block is between `X`
and `16X`.  The generous upper constant also follows directly from the
coordinate condition `2u+w ≤ 8u`. -/
theorem mixedLinear_mem_block_bounds
    {L N X : ℕ} {Ab Kb Ao Ko : ℝ} {q : MixedTriple}
    (hq : q ∈ mixedCoordinateBoxBlock L N Ab Kb Ao Ko X) :
    X ≤ mixedLinear q ∧ mixedLinear q ≤ 16 * X := by
  have hmem := mem_mixedCoordinateBoxBlock.mp hq
  have huBox := mem_Ico.mp hmem.2.1
  have hqData := hmem.1
  rw [mixedCoordinateSet, mem_filter] at hqData
  have hx8u := hqData.2.2.2.1
  constructor
  · dsimp [mixedLinear]
    omega
  · omega

/-- From `t u (2u+w) ≤ N` and `u,2u+w ≥ X`, the residual variable is
at most `N / X²`. -/
theorem mixedT_le_block_residualCutoff
    {L N X : ℕ} {Ab Kb Ao Ko : ℝ} {q : MixedTriple}
    (hq : q ∈ mixedCoordinateBoxBlock L N Ab Kb Ao Ko X) :
    mixedT q ≤ N / (X * X) := by
  have hmem := mem_mixedCoordinateBoxBlock.mp hq
  have huBox := mem_Ico.mp hmem.2.1
  have hX0 : 0 < X := by omega
  have hxLower := (mixedLinear_mem_block_bounds hq).1
  have hqData := hmem.1
  rw [mixedCoordinateSet, mem_filter] at hqData
  rcases hqData.2 with
    ⟨_hcop, _hw6u, _hx8u, _haHost, _hbLower, hbUpper,
      _htRough, _huRough, _hxRough, _htOdd, _huOdd, _hwOdd,
      _hxOdd, _hbRegular, _haRegular⟩
  change mixedT q * mixedU q * mixedLinear q ≤ N at hbUpper
  apply (Nat.le_div_iff_mul_le (Nat.mul_pos hX0 hX0)).2
  calc
    mixedT q * (X * X) ≤
        mixedT q * (mixedU q * mixedLinear q) := by
      exact Nat.mul_le_mul_left _
        (Nat.mul_le_mul huBox.1 hxLower)
    _ = mixedT q * mixedU q * mixedLinear q := by ring
    _ ≤ N := hbUpper

/-- The block-uniform logarithmic prefactor extracted from the joint
regularity indicator. -/
noncomputable def mixedBlockPrefactor
    (L X : ℕ) (Ab Kb Ao Ko qb qo : ℝ) : ℝ :=
  qb ^ Kb * qo ^ Ko *
    (log (16 * X) / log L) ^ (Ab * log qb + Ao * log qo)

/-- Product summand after separating `t` from the two outer variables. -/
noncomputable def mixedSeparatedSummand
    (L z X : ℕ) (qb qo : ℝ) (q : MixedTriple) : ℝ :=
  (if Rough L (mixedT q) then
      (1 / (qb * qo)) ^
        primeFactorCountBetween L X (mixedT q)
    else 0) *
    crossIntegerWeight (oddPrimesUpTo z)
      (mixedQU L (1 / qb)) (mixedQW L (1 / qo))
      (mixedQLinear L (1 / (qb * qo)))
      (mixedU q) (mixedW q)

/-- Nonnegativity of the finite mixed integer weight at the reciprocal
parameters used in the indicator. -/
theorem mixedCrossIntegerWeight_nonneg
    {L z u w : ℕ} {qb qo : ℝ}
    (hqb : 1 < qb) (hqo : 1 < qo) :
    0 ≤ crossIntegerWeight (oddPrimesUpTo z)
      (mixedQU L (1 / qb)) (mixedQW L (1 / qo))
      (mixedQLinear L (1 / (qb * qo))) u w := by
  have hqb0 : 0 < qb := zero_lt_one.trans hqb
  have hqo0 : 0 < qo := zero_lt_one.trans hqo
  unfold crossIntegerWeight
  apply prod_nonneg
  intro p hp
  by_cases hpL : p < L
  · simp only [mixedQU, mixedQW, mixedQLinear, if_pos hpL]
    split_ifs <;> norm_num
  · simp only [mixedQU, mixedQW, mixedQLinear, if_neg hpL]
    split_ifs <;> positivity

/-- The separated summand is nonnegative. -/
theorem mixedSeparatedSummand_nonneg
    {L z X : ℕ} {qb qo : ℝ} (hqb : 1 < qb) (hqo : 1 < qo)
    (q : MixedTriple) :
    0 ≤ mixedSeparatedSummand L z X qb qo q := by
  unfold mixedSeparatedSummand
  split_ifs
  · exact mul_nonneg (by positivity)
      (mixedCrossIntegerWeight_nonneg hqb hqo)
  · simp

/-- On a block, the pointwise mixed indicator is bounded by a uniform
logarithmic prefactor times the separated residual/sieve summand. -/
theorem mixedIndicatorMajorant_le_blockSeparated
    {L N z X : ℕ} {Ab Kb Ao Ko qb qo : ℝ} {q : MixedTriple}
    (hL : 3 ≤ L) (hX : 1 ≤ X) (hzX : z ≤ X)
    (hqb : 1 < qb) (hqo : 1 < qo)
    (hM : 0 ≤ Ab * log qb + Ao * log qo)
    (hq : q ∈ mixedCoordinateBoxBlock L N Ab Kb Ao Ko X) :
    mixedIndicatorMajorant L Ab Kb Ao Ko qb qo q ≤
      mixedBlockPrefactor L X Ab Kb Ao Ko qb qo *
        mixedSeparatedSummand L z X qb qo q := by
  have hmem := mem_mixedCoordinateBoxBlock.mp hq
  have hqCoord := hmem.1
  have hxBounds := mixedLinear_mem_block_bounds hq
  have hqData := hqCoord
  rw [mixedCoordinateSet, mem_filter] at hqData
  rcases hqData.2 with
    ⟨_hcop, _hw6u, _hx8u, _haHost, _hbLower, _hbUpper,
      htRough, _huRough, _hxRough, _htOdd, _huOdd, _hwOdd,
      _hxOdd, _hbRegular, _haRegular⟩
  have hqb0 : 0 < qb := zero_lt_one.trans hqb
  have hqo0 : 0 < qo := zero_lt_one.trans hqo
  have hprod0 : 0 < qb * qo := mul_pos hqb0 hqo0
  have hs0 : 0 ≤ (1 / (qb * qo) : ℝ) := by positivity
  have hprodOne : 1 ≤ qb * qo := by
    nlinarith [mul_pos (sub_pos.mpr hqb) (sub_pos.mpr hqo)]
  have hs1 : (1 / (qb * qo) : ℝ) ≤ 1 :=
    (div_le_one₀ hprod0).mpr hprodOne
  have hlogL : 0 < log (L : ℝ) :=
    log_pos (by exact_mod_cast (show 1 < L by omega))
  have hx0 : 0 < mixedLinear q := by omega
  have h16X0 : 0 < 16 * X := by omega
  have hu1 : 1 ≤ mixedU q :=
    hX.trans (mem_Ico.mp hmem.2.1).1
  have hw1 : 1 ≤ mixedW q :=
    (mem_Icc.mp hmem.2.2).1
  have hlogMono :
      log (mixedLinear q : ℝ) ≤ log (16 * X : ℕ) :=
    Real.strictMonoOn_log.monotoneOn
      (by simpa only [Set.mem_Ioi] using
        (show (0 : ℝ) < mixedLinear q by exact_mod_cast hx0))
      (by simpa only [Set.mem_Ioi] using
        (show (0 : ℝ) < (16 * X : ℕ) by exact_mod_cast h16X0))
      (by exact_mod_cast hxBounds.2)
  have hratio0 :
      0 ≤ log (mixedLinear q) / log L := by
    have : 0 < log (mixedLinear q : ℝ) :=
      log_pos (by
        exact_mod_cast (show 1 < mixedLinear q by
          dsimp [mixedLinear]
          omega))
    positivity
  have hratioLe :
      log (mixedLinear q) / log L ≤
        log (16 * X) / log L :=
    (div_le_div_iff_of_pos_right hlogL).2
      (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hlogMono)
  have hratioPow :
      (log (mixedLinear q) / log L) ^
          (Ab * log qb + Ao * log qo) ≤
        (log (16 * X) / log L) ^
          (Ab * log qb + Ao * log qo) :=
    Real.rpow_le_rpow hratio0 hratioLe hM
  have houter :=
    mixedOuterWeight_le_integerWeight
      hL hqb hqo (hzX.trans hxBounds.1) hqCoord
  have hresidual :
      (1 / (qb * qo)) ^
          primeFactorCountBetween L (mixedLinear q) (mixedT q) ≤
        (1 / (qb * qo)) ^
          primeFactorCountBetween L X (mixedT q) :=
    pow_le_pow_of_le_one hs0 hs1
      (primeFactorCountBetween_mono_right L (mixedT q) hxBounds.1)
  have hbasePrefactor :
      0 ≤ qb ^ Kb * qo ^ Ko := by
    exact mul_nonneg
      (Real.rpow_nonneg hqb0.le Kb)
      (Real.rpow_nonneg hqo0.le Ko)
  have hblockRatio :
      0 ≤ (log (16 * X) / log L) ^
        (Ab * log qb + Ao * log qo) :=
    Real.rpow_nonneg (hratio0.trans hratioLe) _
  have houter0 :
      0 ≤
        (1 / qb) ^ ArithmeticFunction.cardFactors (mixedU q) *
          (1 / qo) ^
            primeFactorCountBetween L (mixedLinear q) (mixedW q) *
          (1 / (qb * qo)) ^
            ArithmeticFunction.cardFactors (mixedLinear q) := by
    positivity
  have hcross0 :
      0 ≤ crossIntegerWeight (oddPrimesUpTo z)
        (mixedQU L (1 / qb)) (mixedQW L (1 / qo))
        (mixedQLinear L (1 / (qb * qo)))
        (mixedU q) (mixedW q) :=
    mixedCrossIntegerWeight_nonneg hqb hqo
  have hresidual0 :
      0 ≤ (1 / (qb * qo)) ^
        primeFactorCountBetween L (mixedLinear q) (mixedT q) := by
    positivity
  have htargetBefore0 :
      0 ≤
        (qb ^ Kb * qo ^ Ko *
            (log (16 * X) / log L) ^
              (Ab * log qb + Ao * log qo)) *
          crossIntegerWeight (oddPrimesUpTo z)
            (mixedQU L (1 / qb)) (mixedQW L (1 / qo))
            (mixedQLinear L (1 / (qb * qo)))
            (mixedU q) (mixedW q) := by
    positivity
  have hbefore :
      (qb ^ Kb * qo ^ Ko *
          (log (mixedLinear q) / log L) ^
            (Ab * log qb + Ao * log qo)) *
        ((1 / qb) ^ ArithmeticFunction.cardFactors (mixedU q) *
          (1 / qo) ^
            primeFactorCountBetween L (mixedLinear q) (mixedW q) *
          (1 / (qb * qo)) ^
            ArithmeticFunction.cardFactors (mixedLinear q)) ≤
      (qb ^ Kb * qo ^ Ko *
          (log (16 * X) / log L) ^
            (Ab * log qb + Ao * log qo)) *
        crossIntegerWeight (oddPrimesUpTo z)
          (mixedQU L (1 / qb)) (mixedQW L (1 / qo))
          (mixedQLinear L (1 / (qb * qo)))
          (mixedU q) (mixedW q) :=
    mul_le_mul
      (mul_le_mul_of_nonneg_left hratioPow hbasePrefactor)
      houter houter0
      (mul_nonneg hbasePrefactor hblockRatio)
  unfold mixedIndicatorMajorant mixedBlockPrefactor
  unfold mixedSeparatedSummand
  rw [if_pos htRough]
  calc
    qb ^ Kb * qo ^ Ko *
            (log (mixedLinear q) / log L) ^
              (Ab * log qb + Ao * log qo) *
          (1 / qb) ^
            ArithmeticFunction.cardFactors (mixedU q) *
          (1 / qo) ^
            primeFactorCountBetween L (mixedLinear q) (mixedW q) *
          (1 / (qb * qo)) ^
            ArithmeticFunction.cardFactors (mixedLinear q) *
          (1 / (qb * qo)) ^
            primeFactorCountBetween L (mixedLinear q) (mixedT q)
        =
          ((qb ^ Kb * qo ^ Ko *
              (log (mixedLinear q) / log L) ^
                (Ab * log qb + Ao * log qo)) *
            ((1 / qb) ^
                ArithmeticFunction.cardFactors (mixedU q) *
              (1 / qo) ^
                primeFactorCountBetween L
                  (mixedLinear q) (mixedW q) *
              (1 / (qb * qo)) ^
                ArithmeticFunction.cardFactors (mixedLinear q))) *
            (1 / (qb * qo)) ^
              primeFactorCountBetween L
                (mixedLinear q) (mixedT q) := by ring
    _ ≤
          (qb ^ Kb * qo ^ Ko *
              (log (16 * X) / log L) ^
                (Ab * log qb + Ao * log qo) *
            crossIntegerWeight (oddPrimesUpTo z)
              (mixedQU L (1 / qb)) (mixedQW L (1 / qo))
              (mixedQLinear L (1 / (qb * qo)))
              (mixedU q) (mixedW q)) *
            (1 / (qb * qo)) ^
              primeFactorCountBetween L X (mixedT q) := by
          exact mul_le_mul hbefore hresidual
            hresidual0 htargetBefore0
    _ = qb ^ Kb * qo ^ Ko *
          (log (16 * X) / log L) ^
            (Ab * log qb + Ao * log qo) *
          ((1 / (qb * qo)) ^
              primeFactorCountBetween L X (mixedT q) *
            crossIntegerWeight (oddPrimesUpTo z)
              (mixedQU L (1 / qb)) (mixedQW L (1 / qo))
              (mixedQLinear L (1 / (qb * qo)))
              (mixedU q) (mixedW q)) := by ring

/-- The rectangular ambient set used after discarding all coordinate
conditions except the three box ranges and `t ≤ N/X²`. -/
def mixedAmbientBox (N X : ℕ) : Finset MixedTriple :=
  ((Icc 1 (N / (X * X))) ×ˢ Ico X (2 * X)) ×ˢ
    Icc 1 (8 * X)

/-- Every coordinate in the standard block belongs to the rectangular
ambient box. -/
theorem mixedCoordinateBoxBlock_subset_ambient
    {L N X : ℕ} {Ab Kb Ao Ko : ℝ} :
    mixedCoordinateBoxBlock L N Ab Kb Ao Ko X ⊆
      mixedAmbientBox N X := by
  intro q hq
  have hmem := mem_mixedCoordinateBoxBlock.mp hq
  rw [mixedAmbientBox, mem_product]
  refine ⟨?_, hmem.2.2⟩
  rw [mem_product]
  have hqData := hmem.1
  rw [mixedCoordinateSet, mem_filter] at hqData
  rcases mem_product.mp hqData.1 with ⟨htuBox, _hwBox⟩
  have htLower := (mem_Icc.mp (mem_product.mp htuBox).1).1
  exact ⟨mem_Icc.mpr
    ⟨htLower, mixedT_le_block_residualCutoff hq⟩, hmem.2.1⟩

/-- Exact factorization of the separated sum on the rectangular ambient
box into the residual moment and the finite three-form box sum. -/
theorem sum_mixedSeparatedSummand_ambient_eq
    (L N z X : ℕ) (qb qo : ℝ) :
    (∑ q ∈ mixedAmbientBox N X,
        mixedSeparatedSummand L z X qb qo q) =
      (∑ t ∈ Icc 1 (N / (X * X)),
          if Rough L t then
            (1 / (qb * qo)) ^
              primeFactorCountBetween L X t
          else 0) *
        finiteWeightBoxSum
          (crossRetainedFamily (P := oddPrimesUpTo z)
            (mixedQU L (1 / qb)) (mixedQW L (1 / qo))
            (mixedQLinear L (1 / (qb * qo)))) X := by
  rw [finiteWeightBoxSum_cross_eq_integerWeight]
  unfold mixedAmbientBox mixedSeparatedSummand
  simp only [sum_product]
  rw [sum_mul]
  apply Finset.sum_congr rfl
  intro t ht
  rw [mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  rw [mul_sum]
  apply Finset.sum_congr rfl
  intro w hw
  rfl

/-- The block cardinality is bounded by the product of the uniform
regularity prefactor, the finite three-form box sum, and the residual
moment. -/
theorem card_mixedCoordinateBoxBlock_le_box_mul_residual
    {L N z X : ℕ} {Ab Kb Ao Ko qb qo : ℝ}
    (hL : 3 ≤ L) (hX : 1 ≤ X) (hzX : z ≤ X)
    (hqb : 1 < qb) (hqo : 1 < qo)
    (hM : 0 ≤ Ab * log qb + Ao * log qo) :
    ((mixedCoordinateBoxBlock
        L N Ab Kb Ao Ko X).card : ℝ) ≤
      mixedBlockPrefactor L X Ab Kb Ao Ko qb qo *
        finiteWeightBoxSum
          (crossRetainedFamily (P := oddPrimesUpTo z)
            (mixedQU L (1 / qb)) (mixedQW L (1 / qo))
            (mixedQLinear L (1 / (qb * qo)))) X *
        (∑ t ∈ Icc 1 (N / (X * X)),
          if Rough L t then
            (1 / (qb * qo)) ^
              primeFactorCountBetween L X t
          else 0) := by
  let B := mixedCoordinateBoxBlock L N Ab Kb Ao Ko X
  let C := mixedBlockPrefactor L X Ab Kb Ao Ko qb qo
  have hcard :
      (B.card : ℝ) ≤
        ∑ q ∈ B,
          mixedIndicatorMajorant L Ab Kb Ao Ko qb qo q := by
    calc
      (B.card : ℝ) = ∑ q ∈ B, (1 : ℝ) := by simp
      _ ≤ _ := by
        apply sum_le_sum
        intro q hq
        exact one_le_mixedIndicatorMajorant hL hqb hqo
          (mem_mixedCoordinateBoxBlock.mp (by simpa [B] using hq)).1
  have hmajor :
      (∑ q ∈ B,
          mixedIndicatorMajorant L Ab Kb Ao Ko qb qo q) ≤
        C * ∑ q ∈ B, mixedSeparatedSummand L z X qb qo q := by
    rw [mul_sum]
    apply sum_le_sum
    intro q hq
    exact mixedIndicatorMajorant_le_blockSeparated
      hL hX hzX hqb hqo hM hq
  have hsubset :
      B ⊆ mixedAmbientBox N X :=
    mixedCoordinateBoxBlock_subset_ambient
  have hseparated :
      (∑ q ∈ B, mixedSeparatedSummand L z X qb qo q) ≤
        ∑ q ∈ mixedAmbientBox N X,
          mixedSeparatedSummand L z X qb qo q :=
    sum_le_sum_of_subset_of_nonneg hsubset
      (fun q _ _ ↦ mixedSeparatedSummand_nonneg hqb hqo q)
  have hC0 : 0 ≤ C := by
    dsimp [C, mixedBlockPrefactor]
    have hqb0 : 0 < qb := zero_lt_one.trans hqb
    have hqo0 : 0 < qo := zero_lt_one.trans hqo
    have hlogL : 0 < log (L : ℝ) :=
      log_pos (by exact_mod_cast (show 1 < L by omega))
    have h16X : 1 < 16 * X := by omega
    exact mul_nonneg
      (mul_nonneg (Real.rpow_nonneg hqb0.le _)
        (Real.rpow_nonneg hqo0.le _))
      (Real.rpow_nonneg
        (div_nonneg
          (log_nonneg (by exact_mod_cast h16X.le)) hlogL.le) _)
  calc
    ((mixedCoordinateBoxBlock
        L N Ab Kb Ao Ko X).card : ℝ) =
        (B.card : ℝ) := rfl
    _ ≤ ∑ q ∈ B,
          mixedIndicatorMajorant L Ab Kb Ao Ko qb qo q :=
      hcard
    _ ≤ C * ∑ q ∈ B, mixedSeparatedSummand L z X qb qo q :=
      hmajor
    _ ≤ C * ∑ q ∈ mixedAmbientBox N X,
          mixedSeparatedSummand L z X qb qo q :=
      mul_le_mul_of_nonneg_left hseparated hC0
    _ = _ := by
      rw [sum_mixedSeparatedSummand_ambient_eq]
      dsimp [C]
      ring

/-- The explicit sharp three-form RHS used for a mixed block. -/
noncomputable def mixedSharpBoxBound
    (L z X R : ℕ) (qb qo : ℝ) : ℝ :=
  8 * (X : ℝ) ^ 2 *
      exp (mixedMertensEnvelope L z
        (1 / qb) (1 / qo) (1 / (qb * qo))) +
    8 * (X : ℝ) ^ 2 *
      ((3 * primeInvSum z) ^ (2 * R + 1) /
        ((2 * R + 1).factorial : ℝ)) +
    ((2 * R + 1 : ℕ) : ℝ) *
      (z : ℝ) ^ (2 * R) * (3 : ℝ) ^ (2 * R) *
      (9 * (X : ℝ) + (z : ℝ) ^ (2 * R))

/-- The explicit Mertens residual RHS with cutoff `X` and residual
range `Y = N/X²`. -/
noncomputable def mixedBlockResidualBound
    (L N X : ℕ) (qb qo : ℝ) : ℝ :=
  let Y := N / (X * X)
  2 * ((log 4 + 5) * Y / log Y) *
    exp
      ((1 / (qb * qo)) *
          primeInvTailUpper (L - 1) (min X Y) +
        primeInvTailUpper (min X Y) Y + 38)

/-- Nonnegativity of the extracted block prefactor. -/
theorem mixedBlockPrefactor_nonneg
    {L X : ℕ} {Ab Kb Ao Ko qb qo : ℝ}
    (hL : 3 ≤ L) (hX : 1 ≤ X)
    (hqb : 1 < qb) (hqo : 1 < qo) :
    0 ≤ mixedBlockPrefactor L X Ab Kb Ao Ko qb qo := by
  unfold mixedBlockPrefactor
  have hqb0 : 0 < qb := zero_lt_one.trans hqb
  have hqo0 : 0 < qo := zero_lt_one.trans hqo
  have hlogL : 0 < log (L : ℝ) :=
    log_pos (by exact_mod_cast (show 1 < L by omega))
  have h16X : 1 < 16 * X := by omega
  exact mul_nonneg
    (mul_nonneg (Real.rpow_nonneg hqb0.le _)
      (Real.rpow_nonneg hqo0.le _))
    (Real.rpow_nonneg
      (div_nonneg
        (log_nonneg (by exact_mod_cast h16X.le)) hlogL.le) _)

/-- Fully explicit finite bound for one standard mixed-coordinate box.
No asymptotic choice of `z,R,X` is made here. -/
theorem card_mixedCoordinateBoxBlock_le_explicit
    {L N z X R : ℕ} {Ab Kb Ao Ko qb qo : ℝ}
    (hL : 3 ≤ L) (hLX : L ≤ X)
    (hLz : L ≤ z) (hzX : z ≤ X)
    (hY : L ≤ N / (X * X))
    (hqb : 1 < qb) (hqo : 1 < qo)
    (hM : 0 ≤ Ab * log qb + Ao * log qo) :
    ((mixedCoordinateBoxBlock
        L N Ab Kb Ao Ko X).card : ℝ) ≤
      mixedBlockPrefactor L X Ab Kb Ao Ko qb qo *
        mixedSharpBoxBound L z X R qb qo *
        mixedBlockResidualBound L N X qb qo := by
  let alpha : ℝ := 1 / qb
  let beta : ℝ := 1 / qo
  let s : ℝ := 1 / (qb * qo)
  let Y : ℕ := N / (X * X)
  have hqb0 : 0 < qb := zero_lt_one.trans hqb
  have hqo0 : 0 < qo := zero_lt_one.trans hqo
  have hprod0 : 0 < qb * qo := mul_pos hqb0 hqo0
  have hprodOne : 1 ≤ qb * qo := by
    nlinarith [mul_pos (sub_pos.mpr hqb) (sub_pos.mpr hqo)]
  have ha0 : 0 ≤ alpha := by dsimp [alpha]; positivity
  have ha1 : alpha ≤ 1 := by
    dsimp [alpha]
    exact (div_le_one₀ hqb0).mpr hqb.le
  have hb0 : 0 ≤ beta := by dsimp [beta]; positivity
  have hb1 : beta ≤ 1 := by
    dsimp [beta]
    exact (div_le_one₀ hqo0).mpr hqo.le
  have hs0 : 0 ≤ s := by dsimp [s]; positivity
  have hs1 : s ≤ 1 := by
    dsimp [s]
    exact (div_le_one₀ hprod0).mpr hprodOne
  have hY2 : 2 ≤ Y := by
    dsimp [Y]
    omega
  have hbase :=
    card_mixedCoordinateBoxBlock_le_box_mul_residual
      (N := N) (Ab := Ab) (Kb := Kb) (Ao := Ao) (Ko := Ko)
      hL (by omega) hzX hqb hqo hM
  have hbox :
      finiteWeightBoxSum
          (crossRetainedFamily (P := oddPrimesUpTo z)
            (mixedQU L alpha) (mixedQW L beta)
            (mixedQLinear L s)) X ≤
        mixedSharpBoxBound L z X R qb qo := by
    dsimp [mixedSharpBoxBound, alpha, beta, s]
    exact mixed_threeFormBoxSum_le_sharp
      ha0 ha1 hb0 hb1 hs0 hs1 (by omega) hLz
  have hresidual :
      (∑ t ∈ Icc 1 Y,
          if Rough L t then
            s ^ primeFactorCountBetween L X t
          else 0) ≤
        mixedBlockResidualBound L N X qb qo := by
    dsimp [mixedBlockResidualBound, Y, s]
    exact roughResidualSubinterval_le_mertens
      hL hLX hY hY2 (by norm_num) hs0 hs1
  have hbox0 :
      0 ≤ finiteWeightBoxSum
        (crossRetainedFamily (P := oddPrimesUpTo z)
          (mixedQU L alpha) (mixedQW L beta)
          (mixedQLinear L s)) X := by
    rw [finiteWeightBoxSum_cross_eq_integerWeight]
    apply sum_nonneg
    intro p hp
    dsimp [alpha, beta, s]
    exact mixedCrossIntegerWeight_nonneg hqb hqo
  have hresidual0 :
      0 ≤ ∑ t ∈ Icc 1 Y,
        if Rough L t then
          s ^ primeFactorCountBetween L X t
        else 0 := by
    apply sum_nonneg
    intro t ht
    split_ifs <;> positivity
  have hprefactor0 :=
    mixedBlockPrefactor_nonneg
      (Ab := Ab) (Kb := Kb) (Ao := Ao) (Ko := Ko)
      hL ((show 1 ≤ L by omega).trans hLX) hqb hqo
  have hscaledBox :
      mixedBlockPrefactor L X Ab Kb Ao Ko qb qo *
          finiteWeightBoxSum
            (crossRetainedFamily (P := oddPrimesUpTo z)
              (mixedQU L alpha) (mixedQW L beta)
              (mixedQLinear L s)) X ≤
        mixedBlockPrefactor L X Ab Kb Ao Ko qb qo *
          mixedSharpBoxBound L z X R qb qo :=
    mul_le_mul_of_nonneg_left hbox hprefactor0
  have hscaledBox0 :
      0 ≤ mixedBlockPrefactor L X Ab Kb Ao Ko qb qo *
        mixedSharpBoxBound L z X R qb qo :=
    mul_nonneg hprefactor0 (hbox0.trans hbox)
  dsimp [alpha, beta, s, Y] at hbase hresidual0 hresidual
  exact hbase.trans <|
    (mul_le_mul_of_nonneg_right hscaledBox hresidual0).trans
      (mul_le_mul_of_nonneg_left hresidual hscaledBox0)

end

end Erdos327.Analytic
