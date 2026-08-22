import ErdosProblems.Erdos1165.PrefixLevelTruncation
import ErdosProblems.Erdos1165.SpatialInsertionConditional

open scoped BigOperators

namespace Erdos1165.PrefixConditionalLaw

open LazyDecomposition PathInsertion SpatialInsertionFiber
open PrefixLevelTruncation ShiftedPrefixBridge

/-!
# The finite prefix form of the HLOZ (6.7) product law

The upper cutoff is kept as an explicit function of the spatial domino.  It
can therefore be instantiated with the corrected frozen local-time maxima of
`PrefixLevelTruncation`, including all finite-prefix boundary atoms.
-/

/-- Away-domino lazy totals, each living below its own supplied cutoff. -/
abbrev UpperTruncatedDominoTotals {o : Orientation} {i : ℕ} (x : Point)
    (r : Fin i → RetainedBlock o) (D : Finset Point)
    (upper : ExternalDomino x r → ℕ) :=
  (b : AwayDomino x r D) → Fin (upper b.1)

/-- Joint fixed-external-word mass of an upper-truncated total vector. -/
noncomputable def upperTotalsJointMass {o : Orientation} {i : ℕ} (x : Point)
    (r : Fin i → RetainedBlock o) (D : Finset Point)
    (upper : ExternalDomino x r → ℕ)
    (ℓ : UpperTruncatedDominoTotals x r D upper) : ℝ :=
  ∏ b : AwayDomino x r D,
    fixedExternalJointMass (dominoExternalMultiplicity x r b.1) (ℓ b)

/-- The one-domino truncated negative-binomial factor with an arbitrary
positive cutoff supplied by the frozen prefix data. -/
noncomputable def upperTruncatedDominoMass {o : Orientation} {i : ℕ}
    (x : Point) (r : Fin i → RetainedBlock o)
    (upper : ExternalDomino x r → ℕ) (b : ExternalDomino x r) (ℓ : ℕ) : ℝ :=
  if ℓ < upper b then
    NegativeBinomial.mass (15 / 16 : ℝ) (dominoExternalMultiplicity x r b) ℓ /
      ∑ j ∈ Finset.range (upper b),
        NegativeBinomial.mass (15 / 16 : ℝ) (dominoExternalMultiplicity x r b) j
  else 0

theorem oneDomino_upperConditionalMass {o : Orientation} {i : ℕ}
    (x : Point) (r : Fin i → RetainedBlock o)
    (upper : ExternalDomino x r → ℕ) (b : ExternalDomino x r)
    (ℓ : Fin (upper b)) :
    fixedExternalJointMass (dominoExternalMultiplicity x r b) ℓ /
        (∑ j ∈ Finset.range (upper b),
          fixedExternalJointMass (dominoExternalMultiplicity x r b) j) =
      upperTruncatedDominoMass x r upper b ℓ := by
  let a := dominoExternalMultiplicity x r b
  have ha : 0 < a := dominoExternalMultiplicity_pos x r b
  have hMarg : fixedExternalMarginalMass a ≠ 0 := by
    simp [fixedExternalMarginalMass]
  have hden :
      (∑ j ∈ Finset.range (upper b), fixedExternalJointMass a j) =
        fixedExternalMarginalMass a *
          ∑ j ∈ Finset.range (upper b),
            NegativeBinomial.mass (15 / 16 : ℝ) a j := by
    simp_rw [fixedExternalJointMass_factorization ha]
    rw [Finset.mul_sum]
  rw [fixedExternalJointMass_factorization ha, hden]
  rw [mul_div_mul_left _ _ hMarg]
  unfold upperTruncatedDominoMass
  rw [if_pos ℓ.isLt]

/-- Exact finite product disintegration with the literal per-domino cutoffs.
This is the algebraic content of HLOZ (6.7) on one fixed finite prefix fibre. -/
theorem upperTotals_conditional_factorization
    {o : Orientation} {i : ℕ} (x : Point)
    (r : Fin i → RetainedBlock o) (D : Finset Point)
    (upper : ExternalDomino x r → ℕ)
    (ℓ : UpperTruncatedDominoTotals x r D upper) :
    upperTotalsJointMass x r D upper ℓ /
        (∑ z : UpperTruncatedDominoTotals x r D upper,
          upperTotalsJointMass x r D upper z) =
      ∏ b : AwayDomino x r D,
        upperTruncatedDominoMass x r upper b.1 (ℓ b) := by
  classical
  unfold upperTotalsJointMass
  have hden := Finset.prod_univ_sum
    (fun b : AwayDomino x r D ↦ (Finset.univ : Finset (Fin (upper b.1))))
    (fun b j ↦ fixedExternalJointMass
      (dominoExternalMultiplicity x r b.1) (j : ℕ))
  rw [Fintype.piFinset_univ] at hden
  rw [hden.symm]
  rw [← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro b _
  simpa only [Fin.sum_univ_eq_sum_range] using
    oneDomino_upperConditionalMass x r upper b.1 (ℓ b)

/-! ## Literal finite-prefix specializations -/

abbrev EvenPrefixDominoTotals {i : ℕ} (ω : StepPath) (n : ℕ)
    (r : Fin i → RetainedBlock .even) (m : ℕ) (D : Finset Point) :=
  UpperTruncatedDominoTotals (0, 0) r D
    (fun b ↦ m - fixedEvenPrefixDominoMax ω n r b)

theorem evenPrefixTotals_conditional_factorization {i : ℕ}
    (ω : StepPath) (n : ℕ) (r : Fin i → RetainedBlock .even)
    (m : ℕ) (D : Finset Point) (ℓ : EvenPrefixDominoTotals ω n r m D) :
    upperTotalsJointMass (0, 0) r D
          (fun b ↦ m - fixedEvenPrefixDominoMax ω n r b) ℓ /
        (∑ z : EvenPrefixDominoTotals ω n r m D,
          upperTotalsJointMass (0, 0) r D
            (fun b ↦ m - fixedEvenPrefixDominoMax ω n r b) z) =
      ∏ b : AwayDomino (0, 0) r D,
        upperTruncatedDominoMass (0, 0) r
          (fun c ↦ m - fixedEvenPrefixDominoMax ω n r c) b.1 (ℓ b) := by
  exact upperTotals_conditional_factorization (0, 0) r D _ ℓ

abbrev ShiftedPrefixDominoTotals {i : ℕ} (ω : StepPath) (n : ℕ)
    (r : Fin i → RetainedBlock .shifted) (m : ℕ) (D : Finset Point) :=
  UpperTruncatedDominoTotals (trajectory ω 1) r D
    (fun b ↦ m - fixedShiftedPrefixDominoMax ω n r b)

theorem shiftedPrefixTotals_conditional_factorization {i : ℕ}
    (ω : StepPath) (n : ℕ) (r : Fin i → RetainedBlock .shifted)
    (m : ℕ) (D : Finset Point) (ℓ : ShiftedPrefixDominoTotals ω n r m D) :
    upperTotalsJointMass (trajectory ω 1) r D
          (fun b ↦ m - fixedShiftedPrefixDominoMax ω n r b) ℓ /
        (∑ z : ShiftedPrefixDominoTotals ω n r m D,
          upperTotalsJointMass (trajectory ω 1) r D
            (fun b ↦ m - fixedShiftedPrefixDominoMax ω n r b) z) =
      ∏ b : AwayDomino (trajectory ω 1) r D,
        upperTruncatedDominoMass (trajectory ω 1) r
          (fun c ↦ m - fixedShiftedPrefixDominoMax ω n r c) b.1 (ℓ b) := by
  exact upperTotals_conditional_factorization (trajectory ω 1) r D _ ℓ

end Erdos1165.PrefixConditionalLaw
