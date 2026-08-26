import ErdosProblems.Erdos327.Analytic.SourceIndicator
import ErdosProblems.Erdos327.Analytic.SourceOuterWeight
import ErdosProblems.Erdos327.Analytic.ResidualMean
import ErdosProblems.Erdos327.Analytic.ThreeFormBoxSharp

/-!
# Finite dyadic assembly for bad source coordinates

This file packages the purely finite part of the centered-source estimate.
On a block `X ≤ u < 2X`, it turns the source-coordinate indicator into a
product of:

* one uniform regularity budget;
* the finite three-form squarefree weight in `(u,v)`;
* the one-variable residual moment in `d`.

No asymptotic parameter choice is made here.
-/

namespace Erdos327.Analytic

open Finset Real
open scoped ArithmeticFunction.Omega BigOperators

noncomputable section

/-- Source coordinates whose first coordinate lies in one dyadic block. -/
def sourceDyadicCoordinateSet
    (L N : ℕ) (A K : ℝ) (X : ℕ) : Finset SourceTriple :=
  (sourceCoordinateSet L N A K).filter fun q ↦
    X ≤ sourceU q ∧ sourceU q < 2 * X

/-- The uniform regularity budget on the enlarged box
`X ≤ u < 2X`, `1 ≤ v ≤ 8X`. -/
def sourceDyadicBudget
    (L X : ℕ) (A K : ℝ) : ℝ :=
  exp (log 4 *
    (A * log (log (8 * X) / log L) + K + 2))

/-- The residual moment left after lowering the variable cutoff `u+v`
to the dyadic cutoff `X`. -/
def sourceDyadicResidualMoment
    (L X Y : ℕ) : ℝ :=
  ∑ d ∈ Icc 1 Y,
    if OddRough L d then
      (1 / 4 : ℝ) ^ primeFactorCountBetween L X d
    else 0

/-- On a source dyadic block, the exact coordinate identity bounds the
residual coordinate by `2N / X²`. -/
theorem sourceD_le_two_mul_div_sq
    {L N : ℕ} {A K : ℝ} {X : ℕ} {q : SourceTriple}
    (hX : 0 < X)
    (hq : q ∈ sourceDyadicCoordinateSet L N A K X) :
    sourceD q ≤ 2 * N / X ^ 2 := by
  rw [sourceDyadicCoordinateSet, mem_filter] at hq
  rcases hq with ⟨hqSource, hXu, hu2X⟩
  have hqData := hqSource
  rw [sourceCoordinateSet, mem_filter] at hqData
  rcases hqData.2 with
    ⟨_hcop, _hv3u, _hscore, _hpair, hexact, _hLsum,
      _hbLower, hbUpper, _hoddU, _hoddSum, _hoddD,
      _hrough, _hregular⟩
  have hXsum : X ≤ sourceU q + sourceV q :=
    hXu.trans (Nat.le_add_right (sourceU q) (sourceV q))
  have hsq :
      X ^ 2 ≤ sourceU q * (sourceU q + sourceV q) := by
    simpa [pow_two] using Nat.mul_le_mul hXu hXsum
  have hmul :
      sourceD q * X ^ 2 ≤ 2 * N := by
    calc
      sourceD q * X ^ 2 ≤
          sourceD q *
            (sourceU q * (sourceU q + sourceV q)) :=
        Nat.mul_le_mul_left _ hsq
      _ = sourceU q * (sourceU q + sourceV q) * sourceD q := by
        ring
      _ = 2 * sourceVertex q := hexact.symm
      _ ≤ 2 * N := Nat.mul_le_mul_left 2 hbUpper
  exact (Nat.le_div_iff_mul_le (by positivity : 0 < X ^ 2)).2 hmul

/-- The `(u,v,d)` coordinates in a dyadic source block lie in the
rectangular product used by the finite sieve and residual mean. -/
theorem sourceDyadicCoordinateSet_subset_box
    {L N : ℕ} {A K : ℝ} {X : ℕ} (hX : 0 < X) :
    sourceDyadicCoordinateSet L N A K X ⊆
      (Ico X (2 * X) ×ˢ Icc 1 (8 * X)) ×ˢ
        Icc 1 (2 * N / X ^ 2) := by
  intro q hq
  have hqFilter := hq
  rw [sourceDyadicCoordinateSet, mem_filter] at hqFilter
  rcases hqFilter with ⟨hqSource, hXu, hu2X⟩
  have hqData := hqSource
  rw [sourceCoordinateSet, mem_filter] at hqData
  rcases hqData with ⟨hqOriginalBox, hconditions⟩
  rcases hconditions with
    ⟨_hcop, hv3u, _hscore, _hpair, _hexact, _hLsum,
      _hbLower, _hbUpper, _hoddU, _hoddSum, _hoddD,
      _hrough, _hregular⟩
  rcases mem_product.mp hqOriginalBox with ⟨huvBox, hdBox⟩
  rcases mem_product.mp huvBox with ⟨huBox, hvBox⟩
  have hvUpper : sourceV q ≤ 8 * X := by omega
  exact mem_product.mpr
    ⟨mem_product.mpr
      ⟨mem_Ico.mpr ⟨hXu, hu2X⟩,
        mem_Icc.mpr ⟨(mem_Icc.mp hvBox).1, hvUpper⟩⟩,
      mem_Icc.mpr
        ⟨(mem_Icc.mp hdBox).1,
          sourceD_le_two_mul_div_sq hX hq⟩⟩

/-- The variable regularity budget at `u+v` is bounded by the uniform
budget at the enlarged endpoint `8X`. -/
theorem source_budget_le_dyadicBudget
    {L N : ℕ} {A K : ℝ} {X : ℕ} {q : SourceTriple}
    (hL : 3 ≤ L) (hA : 0 ≤ A)
    (hq : q ∈ sourceDyadicCoordinateSet L N A K X) :
    exp (log 4 *
        (A * log
            (log (sourceU q + sourceV q) / log L) +
          K + 2)) ≤
      sourceDyadicBudget L X A K := by
  rw [sourceDyadicCoordinateSet, mem_filter] at hq
  rcases hq with ⟨hqSource, _hXu, hu2X⟩
  have hqData := hqSource
  rw [sourceCoordinateSet, mem_filter] at hqData
  rcases hqData.2 with
    ⟨_hcop, hv3u, _hscore, _hpair, _hexact, hLsum,
      _hbLower, _hbUpper, _hoddU, _hoddSum, _hoddD,
      _hrough, _hregular⟩
  have hsumUpper : sourceU q + sourceV q ≤ 8 * X := by
    omega
  have hLpos : (0 : ℝ) < L := by positivity
  have hsumPos : (0 : ℝ) < sourceU q + sourceV q := by
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < L) hLsum)
  have h8XPos : (0 : ℝ) < 8 * X := by
    have hX : 0 < X := by omega
    positivity
  have hlogL : 0 < log (L : ℝ) :=
    log_pos (by exact_mod_cast (show 1 < L by omega))
  have hlogSum : 0 < log (sourceU q + sourceV q : ℝ) :=
    log_pos (by exact_mod_cast
      (show 1 < sourceU q + sourceV q by omega))
  have hlog8X : 0 < log (8 * X : ℝ) :=
    log_pos (by exact_mod_cast (show 1 < 8 * X by omega))
  have hlogs :
      log (sourceU q + sourceV q : ℝ) ≤ log (8 * X : ℝ) :=
    Real.strictMonoOn_log.monotoneOn hsumPos h8XPos
      (by exact_mod_cast hsumUpper)
  have hratios :
      log (sourceU q + sourceV q : ℝ) / log L ≤
        log (8 * X : ℝ) / log L :=
    (div_le_div_iff_of_pos_right hlogL).2 hlogs
  have hlogRatios :
      log (log (sourceU q + sourceV q : ℝ) / log L) ≤
        log (log (8 * X : ℝ) / log L) :=
    Real.strictMonoOn_log.monotoneOn
      (div_pos hlogSum hlogL) (div_pos hlog8X hlogL) hratios
  unfold sourceDyadicBudget
  apply exp_le_exp.mpr
  have hlog4 : 0 ≤ log (4 : ℝ) :=
    (log_pos (by norm_num)).le
  exact mul_le_mul_of_nonneg_left
    (by
      have := mul_le_mul_of_nonneg_left hlogRatios hA
      linarith)
    hlog4

/-- Pointwise source-coordinate majorization on one dyadic block. -/
theorem sourceIndicatorMajorant_le_dyadicWeight
    {L N z : ℕ} {A K : ℝ} {X : ℕ} {q : SourceTriple}
    (hL : 3 ≤ L) (hA : 0 ≤ A)
    (hq : q ∈ sourceDyadicCoordinateSet L N A K X) :
    sourceIndicatorMajorant L A K q ≤
      sourceDyadicBudget L X A K *
        centeredIntegerWeight (oddPrimesUpTo z)
          (sourceQU L) (sourceQV L) (sourceQSum L)
          (sourceU q) (sourceV q) *
        (if OddRough L (sourceD q) then
          (1 / 4 : ℝ) ^
            primeFactorCountBetween L X (sourceD q)
        else 0) := by
  have hqFilter := hq
  rw [sourceDyadicCoordinateSet, mem_filter] at hqFilter
  rcases hqFilter with ⟨hqSource, hXu, _hu2X⟩
  have hqData := hqSource
  rw [sourceCoordinateSet, mem_filter] at hqData
  rcases hqData.2 with
    ⟨_hcop, _hv3u, _hscore, _hpair, _hexact, _hLsum,
      _hbLower, _hbUpper, _hoddU, _hoddSum, hoddD,
      _hrough, _hregular⟩
  have hXsum : X ≤ sourceU q + sourceV q :=
    hXu.trans (Nat.le_add_right _ _)
  have hcount :
      primeFactorCountBetween L X (sourceD q) ≤
        primeFactorCountBetween L (sourceU q + sourceV q)
          (sourceD q) :=
    primeFactorCountBetween_mono_right L (sourceD q) hXsum
  have hresidual :
      (1 / 4 : ℝ) ^
          primeFactorCountBetween L (sourceU q + sourceV q)
            (sourceD q) ≤
        (1 / 4 : ℝ) ^
          primeFactorCountBetween L X (sourceD q) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hcount
  rw [if_pos hoddD]
  unfold sourceIndicatorMajorant
  have hbudget :=
    source_budget_le_dyadicBudget hL hA hq
  have houter :=
    sourceOuterWeight_le_integerWeight (z := z) hqSource
  have houter0 :
      0 ≤
        (1 / 4 : ℝ) ^
            ArithmeticFunction.cardFactors (sourceU q) *
          (1 / 4 : ℝ) ^
            ArithmeticFunction.cardFactors
              (sourceU q + sourceV q) := by positivity
  have hweight0 :
      0 ≤ centeredIntegerWeight (oddPrimesUpTo z)
        (sourceQU L) (sourceQV L) (sourceQSum L)
        (sourceU q) (sourceV q) :=
    houter0.trans houter
  have hbudget0 :
      0 ≤ sourceDyadicBudget L X A K := by
    unfold sourceDyadicBudget
    positivity
  have hfirst :
      exp (log 4 *
          (A * log
              (log (sourceU q + sourceV q) / log L) +
            K + 2)) *
          ((1 / 4 : ℝ) ^
              ArithmeticFunction.cardFactors (sourceU q) *
            (1 / 4 : ℝ) ^
              ArithmeticFunction.cardFactors
                (sourceU q + sourceV q)) ≤
        sourceDyadicBudget L X A K *
          centeredIntegerWeight (oddPrimesUpTo z)
            (sourceQU L) (sourceQV L) (sourceQSum L)
            (sourceU q) (sourceV q) :=
    mul_le_mul hbudget houter houter0 hbudget0
  calc
    exp (log 4 *
          (A * log
              (log (sourceU q + sourceV q) / log L) +
            K + 2)) *
        (1 / 4 : ℝ) ^
          ArithmeticFunction.cardFactors (sourceU q) *
        (1 / 4 : ℝ) ^
          ArithmeticFunction.cardFactors
            (sourceU q + sourceV q) *
        (1 / 4 : ℝ) ^
          primeFactorCountBetween L
            (sourceU q + sourceV q) (sourceD q) =
      (exp (log 4 *
          (A * log
              (log (sourceU q + sourceV q) / log L) +
            K + 2)) *
        ((1 / 4 : ℝ) ^
            ArithmeticFunction.cardFactors (sourceU q) *
          (1 / 4 : ℝ) ^
            ArithmeticFunction.cardFactors
              (sourceU q + sourceV q))) *
        (1 / 4 : ℝ) ^
          primeFactorCountBetween L
            (sourceU q + sourceV q) (sourceD q) := by ring
    _ ≤ (sourceDyadicBudget L X A K *
          centeredIntegerWeight (oddPrimesUpTo z)
            (sourceQU L) (sourceQV L) (sourceQSum L)
            (sourceU q) (sourceV q)) *
        (1 / 4 : ℝ) ^
          primeFactorCountBetween L X (sourceD q) :=
      mul_le_mul hfirst hresidual (by positivity)
        (mul_nonneg hbudget0 hweight0)
    _ = _ := by ring

/-- The source squarefree weight is nonnegative on every integer pair. -/
theorem sourceIntegerWeight_nonneg
    (L z u v : ℕ) :
    0 ≤ centeredIntegerWeight (oddPrimesUpTo z)
      (sourceQU L) (sourceQV L) (sourceQSum L) u v := by
  unfold centeredIntegerWeight
  apply prod_nonneg
  intro p hp
  have hU :
      0 ≤ if p ∣ u then sourceQU L p else (1 : ℝ) := by
    split_ifs
    · exact (sourceQU_nonneg_le_one L p).1
    · norm_num
  have hV :
      0 ≤ if p ∣ v then sourceQV L p else (1 : ℝ) := by
    split_ifs
    · exact (sourceQV_nonneg_le_one L p).1
    · norm_num
  have hSum :
      0 ≤ if p ∣ u + v then sourceQSum L p else (1 : ℝ) := by
    split_ifs
    · exact (sourceQSum_nonneg_le_one L p).1
    · norm_num
  positivity

/-- The exact finite dyadic assembly: source coordinates are bounded by
the finite three-form box weight times the one-variable residual moment. -/
theorem card_sourceDyadicCoordinateSet_le_box_mul_residual
    {L N z X : ℕ} {A K : ℝ}
    (hL : 3 ≤ L) (hX : 0 < X) (hA : 0 ≤ A) :
    ((sourceDyadicCoordinateSet L N A K X).card : ℝ) ≤
      sourceDyadicBudget L X A K *
        finiteWeightBoxSum
          (centeredRetainedFamily (P := oddPrimesUpTo z)
            (sourceQU L) (sourceQV L) (sourceQSum L)) X *
        sourceDyadicResidualMoment L X (2 * N / X ^ 2) := by
  classical
  let S := sourceDyadicCoordinateSet L N A K X
  let pairBox := Ico X (2 * X) ×ˢ Icc 1 (8 * X)
  let residualBox := Icc 1 (2 * N / X ^ 2)
  let W : ℕ × ℕ → ℝ := fun x ↦
    centeredIntegerWeight (oddPrimesUpTo z)
      (sourceQU L) (sourceQV L) (sourceQSum L) x.1 x.2
  let r : ℕ → ℝ := fun d ↦
    if OddRough L d then
      (1 / 4 : ℝ) ^ primeFactorCountBetween L X d
    else 0
  let B := sourceDyadicBudget L X A K
  have hsubset : S ⊆ pairBox ×ˢ residualBox := by
    exact sourceDyadicCoordinateSet_subset_box hX
  have hcard :
      (S.card : ℝ) ≤
        ∑ q ∈ S, sourceIndicatorMajorant L A K q := by
    calc
      (S.card : ℝ) = ∑ _q ∈ S, (1 : ℝ) := by simp
      _ ≤ _ := by
        apply sum_le_sum
        intro q hq
        change q ∈ sourceDyadicCoordinateSet L N A K X at hq
        rw [sourceDyadicCoordinateSet, mem_filter] at hq
        exact one_le_sourceIndicatorMajorant hL hq.1
  have hpoint :
      ∀ q ∈ S,
        sourceIndicatorMajorant L A K q ≤
          B * W q.1 * r q.2 := by
    intro q hq
    exact sourceIndicatorMajorant_le_dyadicWeight hL hA hq
  have hnonneg :
      ∀ q ∈ pairBox ×ˢ residualBox, 0 ≤ B * W q.1 * r q.2 := by
    intro q hq
    have hB : 0 ≤ B := by
      dsimp [B, sourceDyadicBudget]
      positivity
    have hW : 0 ≤ W q.1 := by
      exact sourceIntegerWeight_nonneg L z q.1.1 q.1.2
    have hr : 0 ≤ r q.2 := by
      dsimp [r]
      split_ifs <;> positivity
    positivity
  have hsum :
      (∑ q ∈ S, sourceIndicatorMajorant L A K q) ≤
        ∑ q ∈ pairBox ×ˢ residualBox,
          B * W q.1 * r q.2 := by
    calc
      (∑ q ∈ S, sourceIndicatorMajorant L A K q) ≤
          ∑ q ∈ S, B * W q.1 * r q.2 :=
        sum_le_sum hpoint
      _ ≤ ∑ q ∈ pairBox ×ˢ residualBox,
          B * W q.1 * r q.2 :=
        sum_le_sum_of_subset_of_nonneg hsubset
          (fun q hq _hqS ↦ hnonneg q hq)
  calc
    ((sourceDyadicCoordinateSet L N A K X).card : ℝ) =
        (S.card : ℝ) := rfl
    _ ≤ ∑ q ∈ pairBox ×ˢ residualBox,
          B * W q.1 * r q.2 :=
      hcard.trans hsum
    _ = ∑ x ∈ pairBox, ∑ d ∈ residualBox,
          B * W x * r d := by
      rw [sum_product]
    _ = ∑ x ∈ pairBox,
          (B * W x) * (∑ d ∈ residualBox, r d) := by
      apply sum_congr rfl
      intro x hx
      rw [mul_sum]
    _ = (B * (∑ x ∈ pairBox, W x)) *
          (∑ d ∈ residualBox, r d) := by
      rw [← sum_mul, ← mul_sum]
    _ = sourceDyadicBudget L X A K *
          finiteWeightBoxSum
            (centeredRetainedFamily (P := oddPrimesUpTo z)
              (sourceQU L) (sourceQV L) (sourceQSum L)) X *
          sourceDyadicResidualMoment L X (2 * N / X ^ 2) := by
      dsimp [B, pairBox, residualBox, W, r,
        sourceDyadicResidualMoment]
      rw [← finiteWeightBoxSum_centered_eq_integerWeight]

/-- Explicit sharp sieve factor used in the dyadic source bound. -/
def sourceSharpSieveBound
    (L z X R : ℕ) : ℝ :=
  8 * (X : ℝ) ^ 2 * exp (sourceMertensEnvelope L z) +
    8 * (X : ℝ) ^ 2 *
      ((3 * primeInvSum z) ^ (2 * R + 1) /
        ((2 * R + 1).factorial : ℝ)) +
    ((2 * R + 1 : ℕ) : ℝ) *
      (z : ℝ) ^ (2 * R) * (3 : ℝ) ^ (2 * R) *
      (9 * (X : ℝ) + (z : ℝ) ^ (2 * R))

/-- Finite dyadic source-coordinate bound with explicit Mertens main term,
factorial Bonferroni tail, polynomial sieve boundary, and residual moment. -/
theorem card_sourceDyadicCoordinateSet_le_sharp_mul_residual
    {L N z X R : ℕ} {A K : ℝ}
    (hL : 3 ≤ L) (hX : 0 < X) (hLz : L ≤ z)
    (hA : 0 ≤ A) :
    ((sourceDyadicCoordinateSet L N A K X).card : ℝ) ≤
      sourceDyadicBudget L X A K *
        sourceSharpSieveBound L z X R *
        sourceDyadicResidualMoment L X (2 * N / X ^ 2) := by
  have hbase :=
    card_sourceDyadicCoordinateSet_le_box_mul_residual
      (N := N) (z := z) (K := K) hL hX hA
  have hsieve :=
    source_threeFormBoxSum_le_sharp
      (L := L) (z := z) (X := X) (R := R)
      (by omega : 2 ≤ L) hLz
  have hbudget :
      0 ≤ sourceDyadicBudget L X A K := by
    unfold sourceDyadicBudget
    positivity
  have hresidual :
      0 ≤ sourceDyadicResidualMoment L X (2 * N / X ^ 2) := by
    unfold sourceDyadicResidualMoment
    apply sum_nonneg
    intro d hd
    split_ifs <;> positivity
  refine hbase.trans ?_
  apply mul_le_mul_of_nonneg_right _ hresidual
  apply mul_le_mul_of_nonneg_left _ hbudget
  simpa [sourceSharpSieveBound] using hsieve

/-- Piecewise explicit residual envelope, valid on both sides of the
roughness cutoff. -/
def sourceDyadicResidualEnvelope
    (L X Y : ℕ) : ℝ :=
  if L ≤ Y then
    2 * ((log 4 + 5) * Y / log Y) *
      exp
        ((1 / 4 : ℝ) *
            primeInvTailUpper (L - 1) (min X Y) +
          primeInvTailUpper (min X Y) Y + 38)
  else
    2 * ((log 4 + 5) * Y / log Y) * exp 38

/-- The residual factor in the dyadic assembly satisfies the explicit
piecewise mean-value estimate. -/
theorem sourceDyadicResidualMoment_le_envelope
    {L X Y : ℕ}
    (hL : 3 ≤ L) (hLX : L ≤ X) (hY : 2 ≤ Y) :
    sourceDyadicResidualMoment L X Y ≤
      sourceDyadicResidualEnvelope L X Y := by
  unfold sourceDyadicResidualMoment sourceDyadicResidualEnvelope
  exact residualMoment_le_piecewise
    hL hLX hY (by norm_num) (by norm_num)

/-- Fully explicit finite dyadic bound after applying both the sharp
three-form estimate and the piecewise residual mean estimate. -/
theorem card_sourceDyadicCoordinateSet_le_explicit
    {L N z X R : ℕ} {A K : ℝ}
    (hL : 3 ≤ L) (hLX : L ≤ X) (hLz : L ≤ z)
    (hY : 2 ≤ 2 * N / X ^ 2) (hA : 0 ≤ A) :
    ((sourceDyadicCoordinateSet L N A K X).card : ℝ) ≤
      sourceDyadicBudget L X A K *
        sourceSharpSieveBound L z X R *
        sourceDyadicResidualEnvelope L X (2 * N / X ^ 2) := by
  have hXpos : 0 < X :=
    lt_of_lt_of_le (by omega : 0 < L) hLX
  have hbase :=
    card_sourceDyadicCoordinateSet_le_sharp_mul_residual
      (N := N) (R := R) (K := K)
      (hL := hL) (hX := hXpos) (hLz := hLz) (hA := hA)
  have hresidual :=
    sourceDyadicResidualMoment_le_envelope
      hL hLX hY
  have hbudget :
      0 ≤ sourceDyadicBudget L X A K := by
    unfold sourceDyadicBudget
    positivity
  have hsieve :
      0 ≤ sourceSharpSieveBound L z X R := by
    have hprimeInv : 0 ≤ primeInvSum z := by
      unfold primeInvSum
      positivity
    unfold sourceSharpSieveBound
    positivity
  exact hbase.trans
    (mul_le_mul_of_nonneg_left hresidual
      (mul_nonneg hbudget hsieve))

end

end Erdos327.Analytic
