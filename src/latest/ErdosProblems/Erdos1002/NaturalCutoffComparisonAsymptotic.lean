import ErdosProblems.Erdos1002.NaturalDenominatorCutoffAsymptotic
import Mathlib.Data.Nat.Log
import Mathlib.Analysis.SpecialFunctions.Log.Base

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Set Finset
open scoped BigOperators ComplexConjugate ENNReal Topology

namespace Erdos1002
noncomputable section

 theorem naturalDenominatorTailCoefficient_sub_eq_sum_Ioc
    (N P U n : ℕ) (hP : 0 < P) (hPU : P ≤ U) (hn : n ≠ 0) :
    naturalDenominatorTailCoefficient N P n -
        naturalDenominatorTailCoefficient N U n =
      ∑ p ∈ Ioc P U, naturalDenominatorCoefficientTerm N n p := by
  let pP : ℕ+ := ⟨P, hP⟩
  have hU : 0 < U := hP.trans_le hPU
  let pU : ℕ+ := ⟨U, hU⟩
  let fP : ℕ+ → ℝ := fun p ↦
    if P < (p : ℕ) then naturalDenominatorCoefficientTerm N n (p : ℕ) else 0
  let fU : ℕ+ → ℝ := fun p ↦
    if U < (p : ℕ) then naturalDenominatorCoefficientTerm N n (p : ℕ) else 0
  have hsP : Summable fP := by
    simpa only [fP] using! summable_naturalDenominatorTailCoefficient N P n hn
  have hsU : Summable fU := by
    simpa only [fU] using! summable_naturalDenominatorTailCoefficient N U n hn
  have hsub := hsP.tsum_sub hsU
  have hPsum : (∑' p : ℕ+, fP p) =
      naturalDenominatorTailCoefficient N P n := by rfl
  have hUsum : (∑' p : ℕ+, fU p) =
      naturalDenominatorTailCoefficient N U n := by rfl
  rw [hPsum, hUsum] at hsub
  calc
    naturalDenominatorTailCoefficient N P n -
        naturalDenominatorTailCoefficient N U n =
        ∑' p : ℕ+, (fP p - fU p) := hsub.symm
    _ = ∑ p ∈ Ioc pP pU, (fP p - fU p) := by
      apply tsum_eq_sum
      intro p hp
      have hout : ¬(P < (p : ℕ) ∧ (p : ℕ) ≤ U) := by
        have hout' : ¬(pP < p ∧ p ≤ pU) := by
          simpa only [Finset.mem_Ioc] using! hp
        intro h
        apply hout'
        constructor
        · exact_mod_cast h.1
        · exact_mod_cast h.2
      by_cases hlow : P < (p : ℕ)
      · have hhigh : U < (p : ℕ) := by omega
        simp [fP, fU, hlow, hhigh]
      · have hnotU : ¬U < (p : ℕ) := by omega
        simp [fP, fU, hlow, hnotU]
    _ = ∑ p ∈ Ioc pP pU,
        naturalDenominatorCoefficientTerm N n (p : ℕ) := by
      apply Finset.sum_congr rfl
      intro p hp
      have hmem := Finset.mem_Ioc.mp hp
      have hlow : P < (p : ℕ) := by simpa only [pP, PNat.mk_lt_mk] using! hmem.1
      have hnotHigh : ¬U < (p : ℕ) := by
        simpa only [pU, PNat.mk_le_mk, not_lt] using! hmem.2
      simp [fP, fU, hlow, hnotHigh]
    _ = ∑ p ∈ Ioc P U, naturalDenominatorCoefficientTerm N n p := by
      refine Finset.sum_bij
        (s := Ioc pP pU) (t := Ioc P U)
        (f := fun p : ℕ+ ↦ naturalDenominatorCoefficientTerm N n (p : ℕ))
        (g := fun p : ℕ ↦ naturalDenominatorCoefficientTerm N n p)
        (fun p _hp ↦ (p : ℕ)) ?_ ?_ ?_ ?_
      · intro p hp
        have hmem := Finset.mem_Ioc.mp hp
        apply Finset.mem_Ioc.mpr
        constructor
        · exact_mod_cast hmem.1
        · exact_mod_cast hmem.2
      · intro a ha b hb hab
        exact PNat.eq hab
      · intro p hp
        have hpMem := Finset.mem_Ioc.mp hp
        have hpPos : 0 < p := hP.trans hpMem.1
        refine ⟨⟨p, hpPos⟩, ?_, rfl⟩
        apply Finset.mem_Ioc.mpr
        constructor
        · exact_mod_cast hpMem.1
        · exact_mod_cast hpMem.2
      · intro p hp
        rfl

theorem crudeAllPTailCoefficient_sub_eq_dyadicBlockSum
    (N J n : ℕ) (hN : 0 < N) (hn : n ≠ 0) :
    crudeAllPTailCoefficient N N n -
        crudeAllPTailCoefficient N (2 ^ J * N) n =
      dyadicDenominatorBlockSumCoefficient N J n := by
  have hNU : N ≤ 2 ^ J * N :=
    Nat.le_mul_of_pos_left N (pow_pos (by omega) J)
  calc
    crudeAllPTailCoefficient N N n -
        crudeAllPTailCoefficient N (2 ^ J * N) n =
      naturalDenominatorTailCoefficient N N n -
        naturalDenominatorTailCoefficient N (2 ^ J * N) n := by
      rw [naturalDenominatorTailCoefficient_eq_crudeAllP N N n hn,
        naturalDenominatorTailCoefficient_eq_crudeAllP N (2 ^ J * N) n hn]
    _ = ∑ p ∈ Ioc N (2 ^ J * N),
        naturalDenominatorCoefficientTerm N n p :=
      naturalDenominatorTailCoefficient_sub_eq_sum_Ioc
        N N (2 ^ J * N) n hN hNU hn
    _ = dyadicDenominatorBlockSumCoefficient N J n :=
      (dyadicDenominatorBlockSumCoefficient_eq_interval N J n).symm

/-- Signed Fourier scalar of all denominator blocks between `N` and
`2^J N`. -/
def dyadicCutoffBridgeScalar (N J : ℕ) : ℕ ⊕ ℕ → ℂ := fun i ↦
  strictNaturalTailScalar N N i -
    strictNaturalTailScalar N (2 ^ J * N) i

theorem norm_sq_dyadicCutoffBridgeScalar_le
    (N J : ℕ) (hN : 0 < N) (i : ℕ ⊕ ℕ) :
    ‖dyadicCutoffBridgeScalar N J i‖ ^ 2 ≤
      dyadicDenominatorBlockSumCoefficient N J
        (Sum.elim id id i + 1) ^ 2 := by
  rcases i with n | n
  · simp only [dyadicCutoffBridgeScalar, strictNaturalTailScalar,
      Sum.elim_inl, id_eq]
    rw [← mul_sub]
    have hdiff := crudeAllPTailCoefficient_sub_eq_dyadicBlockSum
      N J (n + 1) hN (Nat.succ_ne_zero n)
    have hdiffC := congrArg (fun x : ℝ ↦ (x : ℂ)) hdiff
    push_cast at hdiffC
    rw [hdiffC]
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hK := norm_naturalCoefficientNormalization_le_one
    calc
      (‖naturalCoefficientNormalization‖ *
          |dyadicDenominatorBlockSumCoefficient N J (n + 1)|) ^ 2 ≤
          (1 * |dyadicDenominatorBlockSumCoefficient N J (n + 1)|) ^ 2 := by
        gcongr
      _ = dyadicDenominatorBlockSumCoefficient N J (n + 1) ^ 2 := by
        rw [one_mul, sq_abs]
  · simp only [dyadicCutoffBridgeScalar, strictNaturalTailScalar,
      Sum.elim_inr, id_eq]
    rw [← map_sub]
    rw [← mul_sub]
    have hdiff := crudeAllPTailCoefficient_sub_eq_dyadicBlockSum
      N J (n + 1) hN (Nat.succ_ne_zero n)
    have hdiffC := congrArg (fun x : ℝ ↦ (x : ℂ)) hdiff
    push_cast at hdiffC
    rw [hdiffC, Complex.norm_conj]
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hK := norm_naturalCoefficientNormalization_le_one
    calc
      (‖naturalCoefficientNormalization‖ *
          |dyadicDenominatorBlockSumCoefficient N J (n + 1)|) ^ 2 ≤
          (1 * |dyadicDenominatorBlockSumCoefficient N J (n + 1)|) ^ 2 := by
        gcongr
      _ = dyadicDenominatorBlockSumCoefficient N J (n + 1) ^ 2 := by
        rw [one_mul, sq_abs]

def dyadicCutoffBridgeSquareMajorant (N J : ℕ) : ℕ ⊕ ℕ → ℝ
  | Sum.inl n => dyadicDenominatorBlockSumCoefficient N J (n + 1) ^ 2
  | Sum.inr n => dyadicDenominatorBlockSumCoefficient N J (n + 1) ^ 2

theorem summable_dyadicCutoffBridgeSquareMajorant
    (N J : ℕ) (hN : 0 < N) :
    Summable (dyadicCutoffBridgeSquareMajorant N J) := by
  have hbase := summable_sq_dyadicDenominatorBlockSumCoefficient N J hN
  have hshift : Summable fun n : ℕ ↦
      dyadicDenominatorBlockSumCoefficient N J (n + 1) ^ 2 := by
    simpa only [Function.comp_apply] using!
      hbase.comp_injective Nat.succ_injective
  exact Summable.sum (dyadicCutoffBridgeSquareMajorant N J)
    (by simpa only [Function.comp_apply, dyadicCutoffBridgeSquareMajorant] using! hshift)
    (by simpa only [Function.comp_apply, dyadicCutoffBridgeSquareMajorant] using! hshift)

theorem summable_norm_sq_dyadicCutoffBridgeScalar
    (N J : ℕ) (hN : 0 < N) :
    Summable fun i : ℕ ⊕ ℕ ↦ ‖dyadicCutoffBridgeScalar N J i‖ ^ 2 := by
  apply Summable.of_nonneg_of_le
    (fun i ↦ sq_nonneg ‖dyadicCutoffBridgeScalar N J i‖)
    (fun i ↦ by
      rcases i with n | n
      · simpa only [dyadicCutoffBridgeSquareMajorant, Sum.elim_inl,
          id_eq] using!
          norm_sq_dyadicCutoffBridgeScalar_le N J hN (Sum.inl n)
      · simpa only [dyadicCutoffBridgeSquareMajorant, Sum.elim_inr,
          id_eq] using!
          norm_sq_dyadicCutoffBridgeScalar_le N J hN (Sum.inr n))
    (summable_dyadicCutoffBridgeSquareMajorant N J hN)

def dyadicCutoffBridgeFourierTerm (N J : ℕ) (i : ℕ ⊕ ℕ) :
    UnitCircleL2 :=
  dyadicCutoffBridgeScalar N J i • fourierLp 2 (signedNonzeroMode i)

theorem summable_dyadicCutoffBridgeFourierTerm
    (N J : ℕ) (hN : 0 < N) :
    Summable (dyadicCutoffBridgeFourierTerm N J) := by
  let V : ∀ _i : ℕ ⊕ ℕ, ℂ →ₗᵢ[ℂ] UnitCircleL2 :=
    fun i ↦ LinearIsometry.toSpanSingleton ℂ UnitCircleL2
      (orthonormal_signedNonzeroFourier.1 i)
  have hV : OrthogonalFamily ℂ (fun _ : ℕ ⊕ ℕ ↦ ℂ) V :=
    orthonormal_signedNonzeroFourier.orthogonalFamily
  have hs : Summable fun i ↦ V i (dyadicCutoffBridgeScalar N J i) :=
    (hV.summable_iff_norm_sq_summable (dyadicCutoffBridgeScalar N J)).mpr
      (summable_norm_sq_dyadicCutoffBridgeScalar N J hN)
  apply hs.congr
  intro i
  rw [show V i (dyadicCutoffBridgeScalar N J i) =
      dyadicCutoffBridgeScalar N J i •
        (fourierLp 2 (signedNonzeroMode i) : UnitCircleL2) by
      exact LinearIsometry.toSpanSingleton_apply _ _]
  rfl

def dyadicCutoffBridgeL2 (N J : ℕ) : UnitCircleL2 :=
  ∑' i : ℕ ⊕ ℕ, dyadicCutoffBridgeFourierTerm N J i

theorem strictNaturalTailL2_sub_eq_dyadicCutoffBridgeL2
    (N J : ℕ) (hN : 0 < N) :
    strictNaturalTailL2 N N - strictNaturalTailL2 N (2 ^ J * N) =
      dyadicCutoffBridgeL2 N J := by
  have hU : 0 < 2 ^ J * N := Nat.mul_pos (pow_pos (by omega) J) hN
  have hsN := summable_strictNaturalTailFourierTerm N N hN hN
  have hsU := summable_strictNaturalTailFourierTerm N (2 ^ J * N) hN hU
  rw [strictNaturalTailL2, strictNaturalTailL2, dyadicCutoffBridgeL2]
  rw [← hsN.tsum_sub hsU]
  apply tsum_congr
  intro i
  unfold strictNaturalTailFourierTerm dyadicCutoffBridgeFourierTerm
    dyadicCutoffBridgeScalar
  rw [sub_smul]

theorem naturalCutoffReconstructionL2_dyadic_sub_eq_bridge
    (N : ℕ+) (J : ℕ) :
    naturalCutoffReconstructionL2 N (2 ^ J * (N : ℕ)) -
        naturalCutoffReconstructionL2 N (N : ℕ) =
      dyadicCutoffBridgeL2 (N : ℕ) J := by
  rw [naturalCutoffReconstructionL2, naturalCutoffReconstructionL2]
  rw [← strictNaturalTailL2_sub_eq_dyadicCutoffBridgeL2
    (N : ℕ) J N.pos]
  abel

theorem norm_sq_dyadicCutoffBridgeL2_le
    (N J : ℕ) (hN : 0 < N) :
    ‖dyadicCutoffBridgeL2 N J‖ ^ 2 ≤
      2 * ((J : ℝ) ^ 2 * (80 + 64 * (Real.pi ^ 2 / 6) ^ 2)) := by
  let V : ∀ _i : ℕ ⊕ ℕ, ℂ →ₗᵢ[ℂ] UnitCircleL2 :=
    fun i ↦ LinearIsometry.toSpanSingleton ℂ UnitCircleL2
      (orthonormal_signedNonzeroFourier.1 i)
  have hV : OrthogonalFamily ℂ (fun _ : ℕ ⊕ ℕ ↦ ℂ) V :=
    orthonormal_signedNonzeroFourier.orthogonalFamily
  have hnorm := norm_sq_tsum_orthogonalFamily hV
    (dyadicCutoffBridgeScalar N J)
    (summable_norm_sq_dyadicCutoffBridgeScalar N J hN)
  have hterm : ∀ i : ℕ ⊕ ℕ,
      V i (dyadicCutoffBridgeScalar N J i) =
        dyadicCutoffBridgeFourierTerm N J i := by
    intro i
    rw [show V i (dyadicCutoffBridgeScalar N J i) =
        dyadicCutoffBridgeScalar N J i •
          (fourierLp 2 (signedNonzeroMode i) : UnitCircleL2) by
        exact LinearIsometry.toSpanSingleton_apply _ _]
    rfl
  have hnormEq : ‖dyadicCutoffBridgeL2 N J‖ ^ 2 =
      ∑' i : ℕ ⊕ ℕ, ‖dyadicCutoffBridgeScalar N J i‖ ^ 2 := by
    rw [dyadicCutoffBridgeL2, ← tsum_congr hterm]
    exact hnorm
  have hscalar := summable_norm_sq_dyadicCutoffBridgeScalar N J hN
  have hmajor := summable_dyadicCutoffBridgeSquareMajorant N J hN
  have hscalarMajor :
      (∑' i : ℕ ⊕ ℕ, ‖dyadicCutoffBridgeScalar N J i‖ ^ 2) ≤
        ∑' i : ℕ ⊕ ℕ, dyadicCutoffBridgeSquareMajorant N J i :=
    Summable.tsum_le_tsum
      (fun i ↦ by
        rcases i with n | n
        · simpa only [dyadicCutoffBridgeSquareMajorant, Sum.elim_inl, id_eq] using!
            norm_sq_dyadicCutoffBridgeScalar_le N J hN (Sum.inl n)
        · simpa only [dyadicCutoffBridgeSquareMajorant, Sum.elim_inr, id_eq] using!
            norm_sq_dyadicCutoffBridgeScalar_le N J hN (Sum.inr n))
      hscalar hmajor
  let T : ℝ := ∑' n : ℕ,
    dyadicDenominatorBlockSumCoefficient N J (n + 1) ^ 2
  have hbase := summable_sq_dyadicDenominatorBlockSumCoefficient N J hN
  have hshift : Summable fun n : ℕ ↦
      dyadicDenominatorBlockSumCoefficient N J (n + 1) ^ 2 := by
    simpa only [Function.comp_apply] using!
      hbase.comp_injective Nat.succ_injective
  have hmajorEq :
      (∑' i : ℕ ⊕ ℕ, dyadicCutoffBridgeSquareMajorant N J i) = T + T := by
    have hleft : HasSum
        (dyadicCutoffBridgeSquareMajorant N J ∘ Sum.inl) T := by
      simpa only [dyadicCutoffBridgeSquareMajorant, Function.comp_apply, T] using!
        hshift.hasSum
    have hright : HasSum
        (dyadicCutoffBridgeSquareMajorant N J ∘ Sum.inr) T := by
      simpa only [dyadicCutoffBridgeSquareMajorant, Function.comp_apply, T] using!
        hshift.hasSum
    exact (hleft.sum hright).tsum_eq
  have hshiftLe : T ≤ ∑' n : ℕ,
      dyadicDenominatorBlockSumCoefficient N J n ^ 2 := by
    simpa only [Function.comp_apply, T] using!
      tsum_comp_le_tsum_of_inj hbase (fun n ↦ sq_nonneg _)
        Nat.succ_injective
  rw [hmajorEq] at hscalarMajor
  calc
    ‖dyadicCutoffBridgeL2 N J‖ ^ 2 =
        ∑' i : ℕ ⊕ ℕ, ‖dyadicCutoffBridgeScalar N J i‖ ^ 2 := hnormEq
    _ ≤ T + T := hscalarMajor
    _ ≤ 2 * (∑' n : ℕ,
        dyadicDenominatorBlockSumCoefficient N J n ^ 2) := by linarith
    _ ≤ 2 * ((J : ℝ) ^ 2 * (80 + 64 * (Real.pi ^ 2 / 6) ^ 2)) := by
      gcongr
      exact tsum_sq_dyadicDenominatorBlockSumCoefficient_le N J hN

/-- Least dyadic exponent whose multiplier covers the manuscript ceiling. -/
def manuscriptDyadicExponent (N : ℕ) : ℕ :=
  Nat.clog 2 (manuscriptCeilScale N)

/-- Dyadic denominator endpoint covering the manuscript outer cutoff. -/
def manuscriptDyadicCutoff (N : ℕ) : ℕ :=
  2 ^ manuscriptDyadicExponent N * N

theorem manuscriptCeilScale_le_pow_dyadicExponent (N : ℕ) :
    manuscriptCeilScale N ≤ 2 ^ manuscriptDyadicExponent N := by
  exact Nat.le_pow_clog (by norm_num) (manuscriptCeilScale N)

theorem pow_dyadicExponent_le_two_mul_manuscriptCeilScale (N : ℕ) :
    2 ^ manuscriptDyadicExponent N ≤ 2 * manuscriptCeilScale N := by
  let C : ℕ := manuscriptCeilScale N
  let J : ℕ := manuscriptDyadicExponent N
  have hCpos : 0 < C := manuscriptCeilScale_pos N
  by_cases hC : C ≤ 1
  · have hCeq : C = 1 := Nat.le_antisymm hC hCpos
    simp [manuscriptDyadicExponent, C, hCeq]
  · have hCone : 1 < C := lt_of_not_ge hC
    have hJpos : 0 < J := by
      simpa only [J, manuscriptDyadicExponent, C] using!
        Nat.clog_pos (by norm_num : 1 < 2) hCone
    have hpred : 2 ^ J.pred < C := by
      simpa only [J, manuscriptDyadicExponent, C] using!
        Nat.pow_pred_clog_lt_self (by norm_num : 1 < 2) hCone
    calc
      2 ^ J = 2 ^ (J.pred + 1) := by
        rw [← Nat.succ_eq_add_one, Nat.succ_pred_eq_of_pos hJpos]
      _ = 2 * 2 ^ J.pred := by rw [pow_succ, Nat.mul_comm]
      _ ≤ 2 * C := Nat.mul_le_mul_left 2 hpred.le

theorem manuscriptOuterCutoff_le_dyadicCutoff (N : ℕ) :
    manuscriptOuterCutoff N ≤ manuscriptDyadicCutoff N := by
  unfold manuscriptOuterCutoff manuscriptDyadicCutoff
  simpa only [Nat.mul_comm] using!
    Nat.mul_le_mul_right N (manuscriptCeilScale_le_pow_dyadicExponent N)

theorem manuscriptDyadicCutoff_le_two_mul_outerCutoff (N : ℕ) :
    manuscriptDyadicCutoff N ≤ 2 * manuscriptOuterCutoff N := by
  unfold manuscriptDyadicCutoff manuscriptOuterCutoff
  have h := Nat.mul_le_mul_right N
    (pow_dyadicExponent_le_two_mul_manuscriptCeilScale N)
  simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using! h

theorem manuscriptDyadicExponent_cast_le (N : ℕ) :
    (manuscriptDyadicExponent N : ℝ) ≤
      2 + (10 / Real.log 2) * Real.log (manuscriptLogScale N) := by
  let L : ℝ := manuscriptLogScale N
  let C : ℕ := manuscriptCeilScale N
  let J : ℕ := manuscriptDyadicExponent N
  have hLpos : 0 < L := manuscriptLogScale_pos N
  have hCpos : (0 : ℝ) < (C : ℝ) := by
    exact_mod_cast manuscriptCeilScale_pos N
  have hCone : (1 : ℝ) ≤ (C : ℝ) := by
    exact_mod_cast (manuscriptCeilScale_pos N)
  have hlogC0 : 0 ≤ Real.log (C : ℝ) := Real.log_nonneg hCone
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogb0 : 0 ≤ Real.logb 2 (C : ℝ) := by
    unfold Real.logb
    exact div_nonneg hlogC0 hlogTwo.le
  have hceil := Nat.ceil_lt_add_one hlogb0
  have hceilEq : ⌈Real.logb (2 : ℝ) (C : ℝ)⌉₊ = Nat.clog 2 C :=
    Real.natCeil_logb_natCast 2 C
  rw [hceilEq] at hceil
  have hCup : (C : ℝ) ≤ 2 * L ^ 10 := by
    simpa only [C, L] using! manuscriptCeilScale_cast_le_two_mul_pow N
  have hlogCup : Real.log (C : ℝ) ≤ Real.log 2 + 10 * Real.log L := by
    have hmono := Real.log_le_log hCpos hCup
    rw [Real.log_mul (by norm_num) (pow_ne_zero 10 hLpos.ne'),
      Real.log_pow] at hmono
    norm_num at hmono
    exact hmono
  have hdiv : Real.log (C : ℝ) / Real.log 2 ≤
      (Real.log 2 + 10 * Real.log L) / Real.log 2 :=
    div_le_div_of_nonneg_right hlogCup hlogTwo.le
  dsimp only [J, manuscriptDyadicExponent, C, L] at hceil ⊢
  unfold Real.logb at hceil
  calc
    (Nat.clog 2 (manuscriptCeilScale N) : ℝ) ≤
        Real.log (manuscriptCeilScale N : ℝ) / Real.log 2 + 1 := hceil.le
    _ ≤ (Real.log 2 + 10 * Real.log (manuscriptLogScale N)) /
          Real.log 2 + 1 := by gcongr
    _ = 2 + (10 / Real.log 2) * Real.log (manuscriptLogScale N) := by
      field_simp [hlogTwo.ne']
      ring

theorem tendsto_manuscriptDyadicExponent_div_log :
    Tendsto
      (fun m : ℕ ↦
        (manuscriptDyadicExponent (m + 1) : ℝ) /
          Real.log (((m + 1 : ℕ) : ℝ)))
      atTop (nhds 0) := by
  let X : ℕ → ℝ := fun m ↦ Real.log (((m + 1 : ℕ) : ℝ))
  let L : ℕ → ℝ := fun m ↦ manuscriptLogScale (m + 1)
  let B : ℕ → ℝ := fun m ↦
    (2 + (10 / Real.log 2) * Real.log (L m)) / X m
  have hXtop : Tendsto X atTop atTop := by
    simpa only [X] using! Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop.comp (Filter.tendsto_add_atTop_nat 1))
  have hLtop : Tendsto L atTop atTop := by
    simpa only [L] using! tendsto_manuscriptLogScale_succ_atTop
  have hlogLdivL : Tendsto (fun m ↦ Real.log (L m) / L m)
      atTop (nhds 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hLtop
  have hOneDivX : Tendsto (fun m ↦ 1 / X m) atTop (nhds 0) :=
    hXtop.const_div_atTop 1
  have hLdivX : Tendsto (fun m ↦ L m / X m) atTop (nhds 1) := by
    have hsum := hOneDivX.add
      (tendsto_const_nhds : Tendsto (fun _m : ℕ ↦ (1 : ℝ)) atTop (nhds 1))
    have hsum' : Tendsto (fun m ↦ 1 / X m + 1) atTop (nhds 1) := by
      simpa using! hsum
    apply hsum'.congr'
    filter_upwards [hXtop.eventually_gt_atTop 0] with m hm
    rw [show L m = 1 + X m by rfl]
    field_simp [hm.ne']
  have hlogLdivX : Tendsto (fun m ↦ Real.log (L m) / X m)
      atTop (nhds 0) := by
    have hprod := hlogLdivL.mul hLdivX
    have hprod' : Tendsto
        (fun m ↦ (Real.log (L m) / L m) * (L m / X m))
        atTop (nhds 0) := by simpa using! hprod
    apply hprod'.congr'
    filter_upwards with m
    have hLm : L m ≠ 0 := by
      dsimp only [L]
      exact (manuscriptLogScale_pos (m + 1)).ne'
    calc
      Real.log (L m) / L m * (L m / X m) =
          Real.log (L m) * (L m)⁻¹ * L m * (X m)⁻¹ := by
        simp only [div_eq_mul_inv]
        ring
      _ = Real.log (L m) * ((L m)⁻¹ * L m) * (X m)⁻¹ := by ring
      _ = Real.log (L m) / X m := by
        rw [inv_mul_cancel₀ hLm]
        simp [div_eq_mul_inv]
  have hB : Tendsto B atTop (nhds 0) := by
    have hconst : Tendsto (fun m ↦ 2 / X m) atTop (nhds 0) :=
      hXtop.const_div_atTop 2
    have hlogPart : Tendsto
        (fun m ↦ (10 / Real.log 2) * (Real.log (L m) / X m))
        atTop (nhds 0) := by
      simpa using! hlogLdivX.const_mul (10 / Real.log 2)
    have hadd := hconst.add hlogPart
    have hadd' : Tendsto
        (fun m ↦ 2 / X m +
          (10 / Real.log 2) * (Real.log (L m) / X m))
        atTop (nhds 0) := by simpa using! hadd
    convert! hadd' using 1
    funext m
    dsimp only [B]
    ring
  apply squeeze_zero'
  · filter_upwards [hXtop.eventually_gt_atTop 0] with m hm
    exact div_nonneg (by positivity) hm.le
  · filter_upwards [hXtop.eventually_gt_atTop 0] with m hm
    exact div_le_div_of_nonneg_right
      (manuscriptDyadicExponent_cast_le (m + 1)) hm.le
  · exact hB

def dyadicCutoffBridgeNormConstant : ℝ :=
  Real.sqrt (2 * (80 + 64 * (Real.pi ^ 2 / 6) ^ 2))

theorem dyadicCutoffBridgeNormConstant_nonneg :
    0 ≤ dyadicCutoffBridgeNormConstant := Real.sqrt_nonneg _

theorem norm_dyadicCutoffBridgeL2_le
    (N J : ℕ) (hN : 0 < N) :
    ‖dyadicCutoffBridgeL2 N J‖ ≤
      dyadicCutoffBridgeNormConstant * (J : ℝ) := by
  have hC : 0 ≤ 2 * (80 + 64 * (Real.pi ^ 2 / 6) ^ 2) := by positivity
  have hsq := norm_sq_dyadicCutoffBridgeL2_le N J hN
  apply (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg dyadicCutoffBridgeNormConstant_nonneg (Nat.cast_nonneg J))).mp
  calc
    ‖dyadicCutoffBridgeL2 N J‖ ^ 2 ≤
        2 * ((J : ℝ) ^ 2 * (80 + 64 * (Real.pi ^ 2 / 6) ^ 2)) := hsq
    _ = (dyadicCutoffBridgeNormConstant * (J : ℝ)) ^ 2 := by
      unfold dyadicCutoffBridgeNormConstant
      rw [mul_pow, Real.sq_sqrt hC]
      ring

theorem tendsto_norm_dyadicNaturalCutoffComparison_div_log :
    Tendsto
      (fun m : ℕ ↦
        let N : ℕ+ := ⟨m + 1, Nat.succ_pos m⟩
        ‖naturalCutoffReconstructionL2 N (manuscriptDyadicCutoff (N : ℕ)) -
          naturalCutoffReconstructionL2 N (N : ℕ)‖ /
            Real.log (N : ℝ))
      atTop (nhds 0) := by
  let E : ℕ → ℝ := fun m ↦
    let N : ℕ+ := ⟨m + 1, Nat.succ_pos m⟩
    ‖naturalCutoffReconstructionL2 N (manuscriptDyadicCutoff (N : ℕ)) -
      naturalCutoffReconstructionL2 N (N : ℕ)‖ /
        Real.log (N : ℝ)
  let B : ℕ → ℝ := fun m ↦
    dyadicCutoffBridgeNormConstant *
      ((manuscriptDyadicExponent (m + 1) : ℝ) /
        Real.log (((m + 1 : ℕ) : ℝ)))
  have hB : Tendsto B atTop (nhds 0) := by
    simpa [B] using!
      tendsto_manuscriptDyadicExponent_div_log.const_mul
        dyadicCutoffBridgeNormConstant
  have hXtop : Tendsto
      (fun m : ℕ ↦ Real.log (((m + 1 : ℕ) : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop.comp (Filter.tendsto_add_atTop_nat 1))
  change Tendsto E atTop (nhds 0)
  apply squeeze_zero'
  · filter_upwards [hXtop.eventually_gt_atTop 0] with m hm
    dsimp only [E]
    exact div_nonneg (norm_nonneg _) hm.le
  · filter_upwards [hXtop.eventually_gt_atTop 0] with m hm
    let N : ℕ+ := ⟨m + 1, Nat.succ_pos m⟩
    have heq := naturalCutoffReconstructionL2_dyadic_sub_eq_bridge
      N (manuscriptDyadicExponent (N : ℕ))
    have hnorm := norm_dyadicCutoffBridgeL2_le
      (N : ℕ) (manuscriptDyadicExponent (N : ℕ)) N.pos
    have hcut : manuscriptDyadicCutoff (N : ℕ) =
        2 ^ manuscriptDyadicExponent (N : ℕ) * (N : ℕ) := rfl
    change
      ‖naturalCutoffReconstructionL2 N (manuscriptDyadicCutoff (N : ℕ)) -
          naturalCutoffReconstructionL2 N (N : ℕ)‖ / Real.log (N : ℝ) ≤
        dyadicCutoffBridgeNormConstant *
          ((manuscriptDyadicExponent (N : ℕ) : ℝ) / Real.log (N : ℝ))
    rw [hcut, heq]
    calc
      ‖dyadicCutoffBridgeL2 (N : ℕ) (manuscriptDyadicExponent (N : ℕ))‖ /
          Real.log (N : ℝ) ≤
          (dyadicCutoffBridgeNormConstant *
            (manuscriptDyadicExponent (N : ℕ) : ℝ)) /
              Real.log (N : ℝ) :=
        div_le_div_of_nonneg_right hnorm hm.le
      _ = dyadicCutoffBridgeNormConstant *
          ((manuscriptDyadicExponent (N : ℕ) : ℝ) /
            Real.log (N : ℝ)) := by ring
  · exact hB

theorem log_N_mul_manuscriptDyadicCutoff_le
    (N : ℕ) (hN : 0 < N) :
    Real.log (((N * manuscriptDyadicCutoff N : ℕ) : ℝ)) ≤
      14 * manuscriptLogScale N := by
  have hDpos : 0 < manuscriptDyadicCutoff N := by
    unfold manuscriptDyadicCutoff
    exact Nat.mul_pos (pow_pos (by omega) _) hN
  have hOuterPos : 0 < manuscriptOuterCutoff N := manuscriptOuterCutoff_pos hN
  have hNat : N * manuscriptDyadicCutoff N ≤
      2 * (N * manuscriptOuterCutoff N) := by
    calc
      N * manuscriptDyadicCutoff N ≤
          N * (2 * manuscriptOuterCutoff N) :=
        Nat.mul_le_mul_left N
          (manuscriptDyadicCutoff_le_two_mul_outerCutoff N)
      _ = 2 * (N * manuscriptOuterCutoff N) := by
        simp only [Nat.mul_assoc, Nat.mul_comm]
  have hleft : (0 : ℝ) < ((N * manuscriptDyadicCutoff N : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos hN hDpos
  have hright : (0 : ℝ) < (2 * ((N * manuscriptOuterCutoff N : ℕ) : ℝ)) := by
    positivity
  have hcast : (((N * manuscriptDyadicCutoff N : ℕ) : ℝ)) ≤
      2 * (((N * manuscriptOuterCutoff N : ℕ) : ℝ)) := by exact_mod_cast hNat
  have hmono := Real.log_le_log hleft hcast
  have hMne : ((((N * manuscriptOuterCutoff N : ℕ) : ℝ))) ≠ 0 := by
    positivity
  rw [Real.log_mul (by norm_num) hMne] at hmono
  have hlogTwo : Real.log 2 ≤ manuscriptLogScale N := by
    have htwo : Real.log 2 ≤ 1 := by
      nlinarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact htwo.trans (manuscriptLogScale_one_le N)
  linarith [log_N_mul_manuscriptOuterCutoff_le N hN]

theorem harmonic_N_mul_manuscriptDyadicCutoff_le
    (N : ℕ) (hN : 0 < N) :
    (harmonic (N * manuscriptDyadicCutoff N) : ℝ) ≤
      15 * manuscriptLogScale N := by
  have h := harmonic_le_one_add_log (N * manuscriptDyadicCutoff N)
  have hL := manuscriptLogScale_one_le N
  linarith [log_N_mul_manuscriptDyadicCutoff_le N hN]

theorem six_add_log_N_mul_manuscriptDyadicCutoff_le
    (N : ℕ) (hN : 0 < N) :
    6 + Real.log (((N * manuscriptDyadicCutoff N : ℕ) : ℝ)) ≤
      20 * manuscriptLogScale N := by
  have hL := manuscriptLogScale_one_le N
  linarith [log_N_mul_manuscriptDyadicCutoff_le N hN]

private theorem dyadicCutoffExplicitBound_eq (N : ℕ+) :
    let n : ℕ := N
    let D : ℕ := 2 ^ manuscriptDyadicExponent n
    let P : ℕ := manuscriptDyadicCutoff n
    2 *
        (((Real.pi ^ 2 / 6) * (2 / (P : ℝ))) ^ 2 *
            (((n * P : ℕ) : ℝ) * (harmonic (n * P) : ℝ) ^ 3) +
          32 * ((n : ℝ) ^ 2 / (((n : ℕ) * P : ℕ) : ℝ)) *
            (6 + Real.log ((((n : ℕ) * P : ℕ) : ℝ))) ^ 5 *
              dyadicFifthMoment) =
      2 *
        ((((Real.pi ^ 2 / 6) * 2) ^ 2 *
            (harmonic (n * P) : ℝ) ^ 3 / (D : ℝ)) +
          32 * (6 + Real.log (((n * P : ℕ) : ℝ))) ^ 5 *
            dyadicFifthMoment / (D : ℝ)) := by
  dsimp only
  have hn : (N : ℝ) ≠ 0 := by positivity
  have hD : ((2 ^ manuscriptDyadicExponent (N : ℕ) : ℕ) : ℝ) ≠ 0 := by
    positivity
  unfold manuscriptDyadicCutoff
  push_cast
  field_simp

def dyadicOuterTailBoundConstant : ℝ :=
  2 * (((Real.pi ^ 2 / 6 * 2) ^ 2 * 15 ^ 3) +
    32 * 20 ^ 5 * dyadicFifthMoment)

theorem dyadicOuterTailBoundConstant_nonneg :
    0 ≤ dyadicOuterTailBoundConstant := by
  unfold dyadicOuterTailBoundConstant
  exact mul_nonneg (by norm_num)
    (add_nonneg
      (mul_nonneg (sq_nonneg _) (by positivity))
      (mul_nonneg (by positivity) dyadicFifthMoment_nonneg))

theorem norm_sq_allDenominator_sub_manuscriptDyadicCutoff_le
    (N : ℕ+) :
    ‖allDenominatorReconstructionL2 N -
        naturalCutoffReconstructionL2 N (manuscriptDyadicCutoff (N : ℕ))‖ ^ 2 ≤
      dyadicOuterTailBoundConstant / manuscriptLogScale (N : ℕ) ^ 5 := by
  let n : ℕ := N
  let L : ℝ := manuscriptLogScale n
  let D : ℕ := 2 ^ manuscriptDyadicExponent n
  let P : ℕ := manuscriptDyadicCutoff n
  have hP : 0 < P := by
    dsimp only [P, manuscriptDyadicCutoff]
    exact Nat.mul_pos (pow_pos (by omega) _) N.pos
  have hraw := norm_sq_allDenominator_sub_naturalCutoffReconstructionL2_le
    N P hP
  have heq := dyadicCutoffExplicitBound_eq N
  have hDpos : (0 : ℝ) < (D : ℝ) := by positivity
  have hL : 1 ≤ L := manuscriptLogScale_one_le n
  have hLpos : 0 < L := manuscriptLogScale_pos n
  have hharm : (harmonic (n * P) : ℝ) ≤ 15 * L := by
    simpa only [n, P, L] using! harmonic_N_mul_manuscriptDyadicCutoff_le n N.pos
  have hlog : 6 + Real.log (((n * P : ℕ) : ℝ)) ≤ 20 * L := by
    simpa only [n, P, L] using!
      six_add_log_N_mul_manuscriptDyadicCutoff_le n N.pos
  have hharm0 : 0 ≤ (harmonic (n * P) : ℝ) := by
    have hq : (0 : ℚ) ≤ harmonic (n * P) :=
      (harmonic_pos (Nat.mul_ne_zero N.pos.ne' hP.ne')).le
    exact_mod_cast hq
  have hlog0 : 0 ≤ 6 + Real.log (((n * P : ℕ) : ℝ)) := by
    have hcast : (1 : ℝ) ≤ ((n * P : ℕ) : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr
        (Nat.mul_ne_zero N.pos.ne' hP.ne')
    positivity
  have hL3L5 : L ^ 3 ≤ L ^ 5 := by
    have hL2 : 1 ≤ L ^ 2 := one_le_pow₀ hL
    calc
      L ^ 3 = L ^ 3 * 1 := by ring
      _ ≤ L ^ 3 * L ^ 2 :=
        mul_le_mul_of_nonneg_left hL2 (pow_nonneg hLpos.le 3)
      _ = L ^ 5 := by ring
  have hharmPow : (harmonic (n * P) : ℝ) ^ 3 ≤ 15 ^ 3 * L ^ 5 := by
    calc
      (harmonic (n * P) : ℝ) ^ 3 ≤ (15 * L) ^ 3 :=
        pow_le_pow_left₀ hharm0 hharm 3
      _ = 15 ^ 3 * L ^ 3 := by ring
      _ ≤ 15 ^ 3 * L ^ 5 := by gcongr
  have hlogPow : (6 + Real.log (((n * P : ℕ) : ℝ))) ^ 5 ≤
      20 ^ 5 * L ^ 5 := by
    calc
      (6 + Real.log (((n * P : ℕ) : ℝ))) ^ 5 ≤ (20 * L) ^ 5 :=
        pow_le_pow_left₀ hlog0 hlog 5
      _ = 20 ^ 5 * L ^ 5 := by ring
  have hcoarse :
      2 *
          ((((Real.pi ^ 2 / 6) * 2) ^ 2 *
              (harmonic (n * P) : ℝ) ^ 3 / (D : ℝ)) +
            32 * (6 + Real.log (((n * P : ℕ) : ℝ))) ^ 5 *
              dyadicFifthMoment / (D : ℝ)) ≤
        dyadicOuterTailBoundConstant * L ^ 5 / (D : ℝ) := by
    have hinner :
      ((Real.pi ^ 2 / 6 * 2) ^ 2 * (harmonic (n * P) : ℝ) ^ 3 /
            (D : ℝ) +
          32 * (6 + Real.log (((n * P : ℕ) : ℝ))) ^ 5 *
            dyadicFifthMoment / (D : ℝ)) ≤
        (((Real.pi ^ 2 / 6 * 2) ^ 2 * 15 ^ 3 +
            32 * 20 ^ 5 * dyadicFifthMoment) * L ^ 5) / (D : ℝ) := by
      calc
        ((Real.pi ^ 2 / 6 * 2) ^ 2 * (harmonic (n * P) : ℝ) ^ 3 /
              (D : ℝ) +
            32 * (6 + Real.log (((n * P : ℕ) : ℝ))) ^ 5 *
              dyadicFifthMoment / (D : ℝ)) ≤
            ((Real.pi ^ 2 / 6 * 2) ^ 2 * (15 ^ 3 * L ^ 5) /
              (D : ℝ) +
              32 * (20 ^ 5 * L ^ 5) * dyadicFifthMoment / (D : ℝ)) := by
          apply add_le_add
          · exact div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_left hharmPow (sq_nonneg _)) hDpos.le
          · apply div_le_div_of_nonneg_right _ hDpos.le
            calc
              32 * (6 + Real.log (((n * P : ℕ) : ℝ))) ^ 5 *
                  dyadicFifthMoment =
                  32 * ((6 + Real.log (((n * P : ℕ) : ℝ))) ^ 5 *
                    dyadicFifthMoment) := by ring
              _ ≤ 32 * ((20 ^ 5 * L ^ 5) * dyadicFifthMoment) :=
                mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_right hlogPow dyadicFifthMoment_nonneg)
                  (by norm_num)
              _ = 32 * (20 ^ 5 * L ^ 5) * dyadicFifthMoment := by ring
        _ = (((Real.pi ^ 2 / 6 * 2) ^ 2 * 15 ^ 3 +
              32 * 20 ^ 5 * dyadicFifthMoment) * L ^ 5) / (D : ℝ) := by ring
    calc
      2 *
          (((Real.pi ^ 2 / 6 * 2) ^ 2 * (harmonic (n * P) : ℝ) ^ 3 /
              (D : ℝ)) +
            32 * (6 + Real.log (((n * P : ℕ) : ℝ))) ^ 5 *
              dyadicFifthMoment / (D : ℝ)) ≤
          2 * ((((Real.pi ^ 2 / 6 * 2) ^ 2 * 15 ^ 3 +
              32 * 20 ^ 5 * dyadicFifthMoment) * L ^ 5) / (D : ℝ)) :=
        mul_le_mul_of_nonneg_left hinner (by norm_num)
      _ = dyadicOuterTailBoundConstant * L ^ 5 / (D : ℝ) := by
        unfold dyadicOuterTailBoundConstant
        ring
  have hDLower : L ^ 10 ≤ (D : ℝ) := by
    calc
      L ^ 10 ≤ (manuscriptCeilScale n : ℝ) :=
        manuscriptLogScale_pow_le_ceil n
      _ ≤ (D : ℝ) := by
        exact_mod_cast manuscriptCeilScale_le_pow_dyadicExponent n
  have hinv : 1 / (D : ℝ) ≤ 1 / L ^ 10 :=
    one_div_le_one_div_of_le (pow_pos hLpos 10) hDLower
  have hratio : L ^ 5 / (D : ℝ) ≤ 1 / L ^ 5 := by
    calc
      L ^ 5 / (D : ℝ) = L ^ 5 * (1 / (D : ℝ)) := by ring
      _ ≤ L ^ 5 * (1 / L ^ 10) :=
        mul_le_mul_of_nonneg_left hinv (pow_nonneg hLpos.le 5)
      _ = 1 / L ^ 5 := by field_simp [hLpos.ne']
  calc
    ‖allDenominatorReconstructionL2 N - naturalCutoffReconstructionL2 N P‖ ^ 2 ≤
        2 *
          (((Real.pi ^ 2 / 6) * (2 / (P : ℝ))) ^ 2 *
              (((n * P : ℕ) : ℝ) * (harmonic (n * P) : ℝ) ^ 3) +
            32 * ((n : ℝ) ^ 2 / (((n : ℕ) * P : ℕ) : ℝ)) *
              (6 + Real.log ((((n : ℕ) * P : ℕ) : ℝ))) ^ 5 *
                dyadicFifthMoment) := by simpa only [n, P] using! hraw
    _ = 2 *
        ((((Real.pi ^ 2 / 6) * 2) ^ 2 *
            (harmonic (n * P) : ℝ) ^ 3 / (D : ℝ)) +
          32 * (6 + Real.log (((n * P : ℕ) : ℝ))) ^ 5 *
            dyadicFifthMoment / (D : ℝ)) := by
      simpa only [n, P, D] using! heq
    _ ≤ dyadicOuterTailBoundConstant * L ^ 5 / (D : ℝ) := hcoarse
    _ = dyadicOuterTailBoundConstant * (L ^ 5 / (D : ℝ)) := by ring
    _ ≤ dyadicOuterTailBoundConstant * (1 / L ^ 5) :=
      mul_le_mul_of_nonneg_left hratio dyadicOuterTailBoundConstant_nonneg
    _ = dyadicOuterTailBoundConstant / L ^ 5 := by ring

theorem tendsto_norm_allDenominator_sub_manuscriptDyadicCutoff :
    Tendsto
      (fun m : ℕ ↦
        let N : ℕ+ := ⟨m + 1, Nat.succ_pos m⟩
        ‖allDenominatorReconstructionL2 N -
          naturalCutoffReconstructionL2 N (manuscriptDyadicCutoff (N : ℕ))‖)
      atTop (nhds 0) := by
  let E : ℕ → ℝ := fun m ↦
    let N : ℕ+ := ⟨m + 1, Nat.succ_pos m⟩
    ‖allDenominatorReconstructionL2 N -
      naturalCutoffReconstructionL2 N (manuscriptDyadicCutoff (N : ℕ))‖
  let B : ℕ → ℝ := fun m ↦
    dyadicOuterTailBoundConstant / manuscriptLogScale (m + 1) ^ 5
  have hL5Top : Tendsto
      (fun m : ℕ ↦ manuscriptLogScale (m + 1) ^ 5) atTop atTop := by
    have hL2 := tendsto_manuscriptLogScale_succ_atTop.atTop_mul_atTop₀
      tendsto_manuscriptLogScale_succ_atTop
    have hL4 := hL2.atTop_mul_atTop₀ hL2
    have hL5 := hL4.atTop_mul_atTop₀ tendsto_manuscriptLogScale_succ_atTop
    convert! hL5 using 1
    funext m
    ring
  have hB : Tendsto B atTop (nhds 0) := by
    simpa only [B] using! hL5Top.const_div_atTop dyadicOuterTailBoundConstant
  have hsq : Tendsto (fun m ↦ E m ^ 2) atTop (nhds 0) := by
    apply squeeze_zero
    · exact fun m ↦ sq_nonneg (E m)
    · intro m
      simpa only [E, B] using!
        norm_sq_allDenominator_sub_manuscriptDyadicCutoff_le
          (⟨m + 1, Nat.succ_pos m⟩ : ℕ+)
    · exact hB
  have hsqrt := hsq.sqrt
  simpa only [E, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _),
    Real.sqrt_zero] using! hsqrt

theorem tendsto_norm_allDenominator_sub_manuscriptDyadicCutoff_div_log :
    Tendsto
      (fun m : ℕ ↦
        let N : ℕ+ := ⟨m + 1, Nat.succ_pos m⟩
        ‖allDenominatorReconstructionL2 N -
          naturalCutoffReconstructionL2 N (manuscriptDyadicCutoff (N : ℕ))‖ /
            Real.log (N : ℝ))
      atTop (nhds 0) := by
  have hlog : Tendsto
      (fun m : ℕ ↦ Real.log (((m + 1 : ℕ) : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop.comp (Filter.tendsto_add_atTop_nat 1))
  exact tendsto_norm_allDenominator_sub_manuscriptDyadicCutoff.div_atTop hlog

/-- The manuscript outer cutoff and the natural cutoff `P=N` differ by
`o(log N)` in the literal circle `L²` norm.  The final partial dyadic block
is handled by inserting the all-denominator reconstruction at both ends,
not by assuming that a partial block is dominated by a complete block. -/
theorem tendsto_norm_manuscriptOuterCutoff_sub_naturalCutoff_div_log :
    Tendsto
      (fun m : ℕ ↦
        let N : ℕ+ := ⟨m + 1, Nat.succ_pos m⟩
        ‖naturalCutoffReconstructionL2 N (manuscriptOuterCutoff (N : ℕ)) -
          naturalCutoffReconstructionL2 N (N : ℕ)‖ / Real.log (N : ℝ))
      atTop (nhds 0) := by
  let E : ℕ → ℝ := fun m ↦
    let N : ℕ+ := ⟨m + 1, Nat.succ_pos m⟩
    ‖naturalCutoffReconstructionL2 N (manuscriptOuterCutoff (N : ℕ)) -
      naturalCutoffReconstructionL2 N (N : ℕ)‖ / Real.log (N : ℝ)
  let B : ℕ → ℝ := fun m ↦
    let N : ℕ+ := ⟨m + 1, Nat.succ_pos m⟩
    ‖allDenominatorReconstructionL2 N -
        naturalCutoffReconstructionL2 N (manuscriptOuterCutoff (N : ℕ))‖ /
          Real.log (N : ℝ) +
      ‖allDenominatorReconstructionL2 N -
        naturalCutoffReconstructionL2 N (manuscriptDyadicCutoff (N : ℕ))‖ /
          Real.log (N : ℝ) +
      ‖naturalCutoffReconstructionL2 N (manuscriptDyadicCutoff (N : ℕ)) -
        naturalCutoffReconstructionL2 N (N : ℕ)‖ / Real.log (N : ℝ)
  have hB : Tendsto B atTop (nhds 0) := by
    have hsum :=
      tendsto_norm_allDenominator_sub_manuscriptOuterCutoff_div_log.add
        tendsto_norm_allDenominator_sub_manuscriptDyadicCutoff_div_log
    have hsum3 := hsum.add tendsto_norm_dyadicNaturalCutoffComparison_div_log
    simpa only [B, zero_add] using! hsum3
  have hXtop : Tendsto
      (fun m : ℕ ↦ Real.log (((m + 1 : ℕ) : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop.comp (Filter.tendsto_add_atTop_nat 1))
  change Tendsto E atTop (nhds 0)
  apply squeeze_zero'
  · filter_upwards [hXtop.eventually_gt_atTop 0] with m hm
    dsimp only [E]
    exact div_nonneg (norm_nonneg _) hm.le
  · filter_upwards [hXtop.eventually_gt_atTop 0] with m hm
    let N : ℕ+ := ⟨m + 1, Nat.succ_pos m⟩
    let Fouter : UnitCircleL2 :=
      naturalCutoffReconstructionL2 N (manuscriptOuterCutoff (N : ℕ))
    let Fall : UnitCircleL2 := allDenominatorReconstructionL2 N
    let Fdyadic : UnitCircleL2 :=
      naturalCutoffReconstructionL2 N (manuscriptDyadicCutoff (N : ℕ))
    let Fnatural : UnitCircleL2 := naturalCutoffReconstructionL2 N (N : ℕ)
    have hdecomp : Fouter - Fnatural =
        (Fouter - Fall) + (Fall - Fdyadic) + (Fdyadic - Fnatural) := by abel
    have htri : ‖Fouter - Fnatural‖ ≤
        ‖Fall - Fouter‖ + ‖Fall - Fdyadic‖ + ‖Fdyadic - Fnatural‖ := by
      rw [hdecomp]
      have hfirst : ‖Fouter - Fall‖ = ‖Fall - Fouter‖ := by
        rw [show Fouter - Fall = -(Fall - Fouter) by abel, norm_neg]
      calc
        ‖Fouter - Fall + (Fall - Fdyadic) + (Fdyadic - Fnatural)‖ ≤
            ‖Fouter - Fall‖ + ‖Fall - Fdyadic‖ + ‖Fdyadic - Fnatural‖ :=
          (norm_add_le _ _).trans <|
            add_le_add (norm_add_le _ _) (le_refl ‖Fdyadic - Fnatural‖)
        _ = ‖Fall - Fouter‖ + ‖Fall - Fdyadic‖ + ‖Fdyadic - Fnatural‖ := by
          rw [hfirst]
    change
      ‖Fouter - Fnatural‖ / Real.log (N : ℝ) ≤
        ‖Fall - Fouter‖ / Real.log (N : ℝ) +
          ‖Fall - Fdyadic‖ / Real.log (N : ℝ) +
            ‖Fdyadic - Fnatural‖ / Real.log (N : ℝ)
    calc
      ‖Fouter - Fnatural‖ / Real.log (N : ℝ) ≤
          (‖Fall - Fouter‖ + ‖Fall - Fdyadic‖ +
            ‖Fdyadic - Fnatural‖) / Real.log (N : ℝ) :=
        div_le_div_of_nonneg_right htri hm.le
      _ = ‖Fall - Fouter‖ / Real.log (N : ℝ) +
          ‖Fall - Fdyadic‖ / Real.log (N : ℝ) +
            ‖Fdyadic - Fnatural‖ / Real.log (N : ℝ) := by ring
  · exact hB

end
end Erdos1002
