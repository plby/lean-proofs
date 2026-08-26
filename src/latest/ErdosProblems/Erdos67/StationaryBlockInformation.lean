import ErdosProblems.Erdos67.StationaryCorrelation
import ErdosProblems.Erdos67.StationaryResidueIndependence
import ErdosProblems.Erdos67.StationaryPrimeBlock

/-!
# The correlation-error bound for a finite residue block

This applies the finite entropy estimate to the actual stationary process. Its
independence premise comes from CRT, and its mean premise comes from conditional
dilation and stationarity.
-/

open scoped BigOperators
open Finset MeasureTheory

namespace Erdos67.StationaryModel

open FiniteEntropy StationaryConcentration

/-- A finite sign block, beginning with coordinate one. -/
def signBlock (N : ℕ) (ω : Configuration) : Fin N → Bool :=
  fun j ↦ ω.1 ((j.val + 1 : ℕ) : ℤ)

theorem continuous_signBlock (N : ℕ) : Continuous (signBlock N) :=
  continuous_pi fun j ↦ (continuous_apply ((j.val + 1 : ℕ) : ℤ)).comp continuous_fst

variable {ι κ : Type*}

/-- Both positions in each pair lie in a block of length `(2h+1)L`. -/
def signBlockPairCoefficients (L h : ℕ) (p : ι → ℕ+)
    (hpL : ∀ i, (p i).val ≤ 2 * L)
    (x : Fin ((2 * h + 1) * L) → Bool) (i : ι) (j : Fin L) : ℝ :=
  signValue (x ⟨j.val, by have hj := j.isLt; nlinarith⟩) *
    signValue (x ⟨j.val + (p i).val * h, by
      have hj := j.isLt
      have hm := Nat.mul_le_mul_right h (hpL i)
      nlinarith⟩)

theorem abs_signBlockPairCoefficients (L h : ℕ) (p : ι → ℕ+)
    (hpL : ∀ i, (p i).val ≤ 2 * L)
    (x : Fin ((2 * h + 1) * L) → Bool) (i : ι) (j : Fin L) :
    |signBlockPairCoefficients L h p hpL x i j| = 1 := by
  simp only [signBlockPairCoefficients, abs_mul, abs_signValue, mul_one]

theorem signBlockPairCoefficients_apply (L h : ℕ) (p : ι → ℕ+)
    (hpL : ∀ i, (p i).val ≤ 2 * L) (ω : Configuration) (i : ι) (j : Fin L) :
    signBlockPairCoefficients L h p hpL (signBlock ((2 * h + 1) * L) ω) i j =
      coordinate ((j.val + 1 : ℕ) : ℤ) ω *
        coordinate (((j.val + 1 : ℕ) : ℤ) + ((p i).val : ℤ) * (h : ℤ)) ω := by
  simp only [signBlockPairCoefficients, signBlock, coordinate,
    Nat.cast_add, Nat.cast_mul, Nat.cast_one, add_assoc, add_comm, add_left_comm]

variable [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem signResidueTripleLaw_centered_pair
    (Q : ProbabilityMeasure Configuration)
    (hQ : Measure.map (shift 1) (Q : Measure Configuration) = (Q : Measure Configuration))
    (hCD : ∀ (d : ℕ+) (F : C((ℤ → Bool), ℝ)),
      (∫ ω, F ω.1 ∂(Q : Measure Configuration)) =
        (d.val : ℝ) * ∫ ω, conditionalDilationTest d F ω ∂(Q : Measure Configuration))
    (L h : ℕ) (p : ι → ℕ+) (q : κ → ℕ+) (hpL : ∀ i, (p i).val ≤ 2 * L)
    (i : ι) (j : Fin L) :
    (∑ z, signResidueTripleLaw Q (signBlock ((2 * h + 1) * L))
      (continuous_signBlock _).measurable p q z *
        (signBlockPairCoefficients L h p hpL z.1.1 i j *
          centeredResidueFactor (p i).val (z.1.2 i) j.val)) =
      correlation Q (h : ℤ) - correlation Q (((p i).val : ℤ) * (h : ℤ)) := by
  unfold signResidueTripleLaw
  rw [measureLaw_expectation]
  simp only [signBlockPairCoefficients_apply, centeredResidueFactor_succ, residueTuple]
  exact centered_pair_identity Q hQ hCD (p i) (j.val + 1) (h : ℤ)

/-- A block of coprime residue coordinates controls its squared correlation
errors by conditional mutual information, with all probabilistic inputs proved. -/
theorem correlation_errors_le_block_information
    (Q : ProbabilityMeasure Configuration)
    (hQ : Measure.map (shift 1) (Q : Measure Configuration) = (Q : Measure Configuration))
    (hCD : ∀ (d : ℕ+) (F : C((ℤ → Bool), ℝ)),
      (∫ ω, F ω.1 ∂(Q : Measure Configuration)) =
        (d.val : ℝ) * ∫ ω, conditionalDilationTest d F ω ∂(Q : Measure Configuration))
    (L h : ℕ) (hL : 0 < L) (p : ι → ℕ+) (q : κ → ℕ+)
    (hLp : ∀ i, L ≤ (p i).val) (hpL : ∀ i, (p i).val ≤ 2 * L)
    (hcoprime : Pairwise (Function.onFun Nat.Coprime
      (fun s : ι ⊕ κ ↦ (Sum.elim p q s).val))) :
    (∑ i, (correlation Q (h : ℤ) - correlation Q (((p i).val : ℤ) * (h : ℤ))) ^ 2) ≤
      18 * conditionalMutualInfo (signResidueTripleLaw Q (signBlock ((2 * h + 1) * L))
        (continuous_signBlock _).measurable p q) := by
  apply square_error_le_eighteen_information (fun i ↦ (p i).val)
    (signResidueTripleLaw Q (signBlock ((2 * h + 1) * L))
      (continuous_signBlock _).measurable p q) hL hLp hpL
    (signBlockPairCoefficients L h p hpL)
    (fun x i j ↦ (abs_signBlockPairCoefficients L h p hpL x i j).le)
    (fun i ↦ correlation Q (h : ℤ) - correlation Q (((p i).val : ℤ) * (h : ℤ)))
  · exact signResidueTripleLaw_independent_residues Q hQ _
      (continuous_signBlock _).measurable p q hcoprime
  · exact signResidueTripleLaw_centered_pair Q hQ hCD L h p q hpL

end Erdos67.StationaryModel
