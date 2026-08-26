import ErdosProblems.Erdos1002.PrimitiveShotCellFourier
import ErdosProblems.Erdos1002.NaturalCutoffShotFourierReduction

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Exact positive-frequency coefficient of the natural-cutoff shot error

This file performs the finite algebra that connects the literal circle
`L²` error to the analytic difference between the full principal-value
transform and the nearest-cell transform.  No Fourier series is rearranged:
the denominator set is finite, and the bounded positive-natural subtype in
the reconstruction coefficient is explicitly reindexed by `Finset.Icc`.
-/

open Filter MeasureTheory Set Finset
open scoped BigOperators

namespace Erdos1002

noncomputable section

/-- The subtype prefix used in the natural reconstruction is exactly the
ordinary finite sum over positive naturals at most `P`. -/
theorem naturalDenominatorPrefixCoefficient_eq_sum
    (N P n : ℕ) (hP : 0 < P) :
    naturalDenominatorPrefixCoefficient N P n =
      ∑ p ∈ Finset.Icc 1 P, naturalDenominatorCoefficientTerm N n p := by
  let Pp : ℕ+ := ⟨P, hP⟩
  let S : Finset ℕ+ := Finset.Icc 1 Pp
  have hS (p : ℕ+) : p ∈ S ↔ (p : ℕ) ≤ P := by
    simp only [S, Finset.mem_Icc]
    constructor
    · intro hp
      exact_mod_cast hp.2
    · intro hp
      constructor
      · exact PNat.one_le p
      · exact_mod_cast hp
  let e : {p : ℕ+ // (p : ℕ) ≤ P} ≃ {p : ℕ+ // p ∈ S} :=
    Equiv.subtypeEquivRight (fun p ↦ (hS p).symm)
  unfold naturalDenominatorPrefixCoefficient
  calc
    (∑' p : {p : ℕ+ // (p : ℕ) ≤ P},
        naturalDenominatorCoefficientTerm N n (p : ℕ+)) =
        ∑' p : {p : ℕ+ // p ∈ S},
          naturalDenominatorCoefficientTerm N n ((e.symm p : ℕ+) : ℕ) := by
      exact (e.symm.tsum_eq
        (fun p ↦ naturalDenominatorCoefficientTerm N n ((p : ℕ+) : ℕ))).symm
    _ = ∑ p ∈ S,
        naturalDenominatorCoefficientTerm N n (p : ℕ) := by
      have he (p : {p : ℕ+ // p ∈ S}) :
          ((e.symm p : ℕ+) : ℕ) = (p : ℕ+) := rfl
      simp_rw [he]
      exact Finset.tsum_subtype S
        (fun p : ℕ+ ↦ naturalDenominatorCoefficientTerm N n (p : ℕ))
    _ = ∑ p ∈ Finset.Icc 1 P,
        naturalDenominatorCoefficientTerm N n p := by
      apply Finset.sum_bij (s := S) (t := Finset.Icc 1 P)
        (fun p _hp ↦ (p : ℕ))
      · intro p hp
        have hpS : p ∈ S := by simpa using! hp
        exact Finset.mem_Icc.mpr ⟨p.property, (hS p).mp hpS⟩
      · intro p₁ _ p₂ _ h
        exact Subtype.ext h
      · intro p hp
        refine ⟨⟨p, (Finset.mem_Icc.mp hp).1⟩, ?_, rfl⟩
        simpa only [S, Finset.mem_Icc] using!
          (show (1 : ℕ+) ≤ ⟨p, (Finset.mem_Icc.mp hp).1⟩ ∧
              ⟨p, (Finset.mem_Icc.mp hp).1⟩ ≤ Pp by
            constructor
            · exact PNat.one_le _
            · exact_mod_cast (Finset.mem_Icc.mp hp).2)
      · intro p _hp
        rfl

/-- Difference between the exact full principal-value transform and its
nearest-cell truncation at the rational frequency `n / p`. -/
def nearestCellWindowTransform (N n p : ℕ) : ℂ :=
  naturalCoefficientNormalization * (hStarRatio n (p * N) : ℂ) -
    nearestCellTransform N n p

/-- Exact finite Ramanujan expansion of every positive Fourier coefficient
of the literal natural-cutoff shot error. -/
theorem naturalCutoffShotErrorCoefficient_nat
    (N : ℕ+) (n : ℕ) (hn : 0 < n) :
    naturalCutoffShotErrorCoefficient N (n : ℤ) =
      ∑ p ∈ Finset.Icc 1 (N : ℕ),
        ((1 / (p : ℝ) ^ 2 : ℝ) : ℂ) *
          ramanujanSum p (n : ℤ) *
            nearestCellWindowTransform (N : ℕ) n p := by
  unfold naturalCutoffShotErrorCoefficient
  rw [fourierCoeff_naturalCutoffReconstructionL2_pos_eq_finite
      N (N : ℕ) n N.pos hn,
    fourierCoeff_reconstructedShotL2_nat]
  unfold finiteNaturalDenominatorPositiveCoefficient
  rw [naturalDenominatorPrefixCoefficient_eq_sum
      (N : ℕ) (N : ℕ) n N.pos]
  rw [Complex.ofReal_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  have hpPos : 0 < p := (Finset.mem_Icc.mp hp).1
  unfold naturalDenominatorCoefficientTerm nearestCellWindowTransform
    naturalCoefficientNormalization
  push_cast
  rw [ofReal_re_ramanujanSum]
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hpPos.ne'
  field_simp [hpC, Real.pi_ne_zero]

end

end Erdos1002
