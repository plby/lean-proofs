/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos636.AugmentationScales

/-!
# Deterministic rounding bounds for the inner exposure

This temporary companion module isolates the four floor estimates used in
the final inner-exposure assembly.
-/

open Classical SimpleGraph Filter

namespace Erdos636
namespace AugmentationInnerScalesRoundingScratch

noncomputable section

open AsymptoticThresholds

def exposureSteps (mCoeff : ℝ) (nD : ℕ) : ℕ :=
  ⌊mCoeff * Real.sqrt nD⌋₊

def collisionBadBudget (badCollisionCoeff : ℝ) (nD : ℕ) : ℕ :=
  ⌊badCollisionCoeff * Real.sqrt nD⌋₊

def degreeBadBudget (badDegreeCoeff : ℝ) (nD : ℕ) : ℕ :=
  ⌊badDegreeCoeff * Real.sqrt nD⌋₊

def collisionEdgeBudget (energyCoeff : ℝ) (nD : ℕ) : ℕ :=
  ⌊energyCoeff * Real.sqrt nD⌋₊

def exposurePiece (pieceCoeff : ℝ) (nD : ℕ) : ℕ :=
  ⌊pieceCoeff * Real.sqrt nD⌋₊

def exposureOutput (outputCoeff : ℝ) (nD : ℕ) : ℕ :=
  ⌊outputCoeff * nD⌋₊

/-- The survivor, piece, output, and output-scale inequalities for the
explicit square-root and linear floors all hold after one threshold. -/
theorem exists_innerRoundedPackingBounds
    {a₀ mCoeff energyCoeff badGeomCoeff badCollisionCoeff badDegreeCoeff
      pieceCoeff outputCoeff a₂ deltaUpper : ℝ}
    (ha₀ : 0 < a₀) (hmCoeff : 0 < mCoeff)
    (henergyCoeff : 0 < energyCoeff)
    (hbadGeomCoeff : 0 < badGeomCoeff)
    (hbadCollisionCoeff : 0 < badCollisionCoeff)
    (hbadDegreeCoeff : 0 < badDegreeCoeff)
    (hpieceCoeff : 0 < pieceCoeff)
    (houtputCoeff : 0 < outputCoeff)
    (ha₂ : 0 ≤ a₂) (hdeltaUpper : 0 ≤ deltaUpper)
    (hsurvivor : badDegreeCoeff < a₀ / 16)
    (hpiece :
      pieceCoeff * (a₀ / 4 + 2 * energyCoeff) ≤
        (a₀ / 16 - badDegreeCoeff) ^ 2)
    (hgap : badGeomCoeff + badCollisionCoeff < mCoeff)
    (houtput :
      outputCoeff ≤
        (mCoeff - badGeomCoeff - badCollisionCoeff) * pieceCoeff / 2)
    (hscale : 2 * a₂ * deltaUpper ≤ outputCoeff) :
    ∃ N : ℕ, ∀ nD ≥ N, ∀ nZ : ℕ,
      (nZ : ℝ) ≤ deltaUpper * Real.sqrt nD →
      degreeBadBudget badDegreeCoeff nD <
          partialMatchingSize a₀ nD -
            AugmentationScales.partialBadBudget a₀ nD ∧
      exposurePiece pieceCoeff nD *
          (partialMatchingSize a₀ nD +
            2 * collisionEdgeBudget energyCoeff nD) ≤
        (partialMatchingSize a₀ nD -
            AugmentationScales.partialBadBudget a₀ nD -
            degreeBadBudget badDegreeCoeff nD) ^ 2 ∧
      exposureOutput outputCoeff nD ≤
        ((exposureSteps mCoeff nD + 1) -
            (AugmentationScales.geometricBadBudget badGeomCoeff nD +
              collisionBadBudget badCollisionCoeff nD)) *
          exposurePiece pieceCoeff nD ∧
      a₂ * nZ * Real.sqrt nD ≤ exposureOutput outputCoeff nD := by
  obtain ⟨Npartial, hpartial⟩ :=
    exists_eighth_mul_sqrt_le_quarter_floor a₀ ha₀
  obtain ⟨Npiece, hpieceFloor⟩ :=
    exists_half_mul_sqrt_le_floor pieceCoeff hpieceCoeff
  obtain ⟨Noutput, houtputLarge⟩ :=
    exists_nat_rpow_ge 1 (2 / outputCoeff) (by norm_num)
  let N := max 1 (max Npartial (max Npiece Noutput))
  refine ⟨N, ?_⟩
  intro nD hnD nZ hnZ
  have hnD1 : 1 ≤ nD := (le_max_left _ _).trans hnD
  have htail : max Npartial (max Npiece Noutput) ≤ nD :=
    (le_max_right _ _).trans hnD
  have hNpartial : Npartial ≤ nD := (le_max_left _ _).trans htail
  have htail' : max Npiece Noutput ≤ nD :=
    (le_max_right _ _).trans htail
  have hNpiece : Npiece ≤ nD := (le_max_left _ _).trans htail'
  have hNoutput : Noutput ≤ nD := (le_max_right _ _).trans htail'
  have hnDpos : 0 < nD := lt_of_lt_of_le Nat.zero_lt_one hnD1
  have hsqrtPos : 0 < Real.sqrt nD := Real.sqrt_pos.2 (by exact_mod_cast hnDpos)
  have hsqrtSq : (Real.sqrt nD) ^ 2 = (nD : ℝ) :=
    Real.sq_sqrt (Nat.cast_nonneg nD)
  let s₀ : ℕ := partialMatchingSize a₀ nD
  let badBudget : ℕ := AugmentationScales.partialBadBudget a₀ nD
  let badDegree : ℕ := degreeBadBudget badDegreeCoeff nD
  let edgeBudget : ℕ := collisionEdgeBudget energyCoeff nD
  let piece : ℕ := exposurePiece pieceCoeff nD
  let steps : ℕ := exposureSteps mCoeff nD
  let badGeom : ℕ :=
    AugmentationScales.geometricBadBudget badGeomCoeff nD
  let badCollision : ℕ := collisionBadBudget badCollisionCoeff nD
  let output : ℕ := exposureOutput outputCoeff nD
  have hs₀Lower : a₀ / 8 * Real.sqrt nD ≤ (s₀ : ℝ) := by
    simpa only [s₀, partialMatchingSize_eq] using hpartial nD hNpartial
  have hs₀Upper : (s₀ : ℝ) ≤ a₀ / 4 * Real.sqrt nD := by
    dsimp only [s₀, partialMatchingSize]
    have hfloor := Nat.floor_le
      (show 0 ≤ a₀ * Real.sqrt nD / 4 by positivity)
    simpa only [div_mul_eq_mul_div] using hfloor
  have hbadBudgetEq : badBudget = s₀ / 2 := by
    rfl
  have hbadDegreeUpper : (badDegree : ℝ) ≤
      badDegreeCoeff * Real.sqrt nD := by
    dsimp only [badDegree, degreeBadBudget]
    exact floor_mul_sqrt_le badDegreeCoeff hbadDegreeCoeff.le nD
  have htwiceBadDegree : 2 * badDegree < s₀ := by
    have hcoeff :
        2 * badDegreeCoeff * Real.sqrt nD <
          a₀ / 8 * Real.sqrt nD := by
      have := mul_lt_mul_of_pos_right hsurvivor hsqrtPos
      nlinarith
    have hreal : ((2 * badDegree : ℕ) : ℝ) < (s₀ : ℝ) := by
      push_cast
      calc
        2 * (badDegree : ℝ) ≤
            2 * (badDegreeCoeff * Real.sqrt nD) := by gcongr
        _ = 2 * badDegreeCoeff * Real.sqrt nD := by ring
        _ < a₀ / 8 * Real.sqrt nD := hcoeff
        _ ≤ (s₀ : ℝ) := hs₀Lower
    exact_mod_cast hreal
  have hcandidate : badDegree < s₀ - badBudget := by
    rw [hbadBudgetEq]
    omega
  have hedgeUpper : (edgeBudget : ℝ) ≤
      energyCoeff * Real.sqrt nD := by
    dsimp only [edgeBudget, collisionEdgeBudget]
    exact floor_mul_sqrt_le energyCoeff henergyCoeff.le nD
  have hpieceUpper : (piece : ℝ) ≤
      pieceCoeff * Real.sqrt nD := by
    dsimp only [piece, exposurePiece]
    exact floor_mul_sqrt_le pieceCoeff hpieceCoeff.le nD
  have hhalfSurvivor : (s₀ : ℝ) / 2 ≤ (s₀ - s₀ / 2 : ℕ) := by
    rw [Nat.cast_sub (Nat.div_le_self _ _)]
    nlinarith [show ((s₀ / 2 : ℕ) : ℝ) ≤ (s₀ : ℝ) / 2 from
      Nat.cast_div_le]
  have hremainingLower :
      (a₀ / 16 - badDegreeCoeff) * Real.sqrt nD ≤
        (s₀ - badBudget - badDegree : ℕ) := by
    have hcandidateHalf : badDegree ≤ s₀ - s₀ / 2 := by
      simpa only [hbadBudgetEq] using hcandidate.le
    rw [hbadBudgetEq, Nat.cast_sub hcandidateHalf]
    nlinarith
  have hremainingNonneg :
      0 ≤ (a₀ / 16 - badDegreeCoeff) * Real.sqrt nD := by
    exact mul_nonneg (sub_nonneg.mpr hsurvivor.le) hsqrtPos.le
  have hpieceReal :
      (piece * (s₀ + 2 * edgeBudget) : ℕ) ≤
        ((s₀ - badBudget - badDegree : ℕ) : ℝ) ^ 2 := by
    push_cast
    calc
      (piece : ℝ) * ((s₀ : ℝ) + 2 * edgeBudget)
          ≤ (pieceCoeff * Real.sqrt nD) *
              ((a₀ / 4 + 2 * energyCoeff) * Real.sqrt nD) := by
            apply mul_le_mul hpieceUpper
            · nlinarith
            · positivity
            · positivity
      _ = pieceCoeff * (a₀ / 4 + 2 * energyCoeff) *
            (nD : ℝ) := by
            calc
              (pieceCoeff * Real.sqrt nD) *
                    ((a₀ / 4 + 2 * energyCoeff) * Real.sqrt nD) =
                  pieceCoeff * (a₀ / 4 + 2 * energyCoeff) *
                    (Real.sqrt nD) ^ 2 := by ring
              _ = _ := by rw [hsqrtSq]
      _ ≤ (a₀ / 16 - badDegreeCoeff) ^ 2 * (nD : ℝ) := by
            exact mul_le_mul_of_nonneg_right hpiece (Nat.cast_nonneg nD)
      _ = ((a₀ / 16 - badDegreeCoeff) * Real.sqrt nD) ^ 2 := by
            calc
              (a₀ / 16 - badDegreeCoeff) ^ 2 * (nD : ℝ) =
                  (a₀ / 16 - badDegreeCoeff) ^ 2 *
                    (Real.sqrt nD) ^ 2 := by rw [hsqrtSq]
              _ = _ := by ring
      _ ≤ ((s₀ - badBudget - badDegree : ℕ) : ℝ) ^ 2 := by
            simpa only [pow_two] using
              mul_self_le_mul_self hremainingNonneg hremainingLower
  have hpieceNat :
      piece * (s₀ + 2 * edgeBudget) ≤
        (s₀ - badBudget - badDegree) ^ 2 := by
    exact_mod_cast hpieceReal
  have hpieceLower : pieceCoeff / 2 * Real.sqrt nD ≤ (piece : ℝ) := by
    simpa only [piece, exposurePiece] using hpieceFloor nD hNpiece
  have hstepsUpperLoss :
      mCoeff * Real.sqrt nD < (steps : ℝ) + 1 := by
    dsimp only [steps, exposureSteps]
    exact Nat.lt_floor_add_one _
  have hbadGeomUpper : (badGeom : ℝ) ≤
      badGeomCoeff * Real.sqrt nD := by
    dsimp only [badGeom, AugmentationScales.geometricBadBudget]
    exact floor_mul_sqrt_le badGeomCoeff hbadGeomCoeff.le nD
  have hbadCollisionUpper : (badCollision : ℝ) ≤
      badCollisionCoeff * Real.sqrt nD := by
    dsimp only [badCollision, collisionBadBudget]
    exact floor_mul_sqrt_le badCollisionCoeff hbadCollisionCoeff.le nD
  have hbadLtSteps : badGeom + badCollision < steps + 1 := by
    have hgapScaled :
        (badGeomCoeff + badCollisionCoeff) * Real.sqrt nD <
          mCoeff * Real.sqrt nD :=
      mul_lt_mul_of_pos_right hgap hsqrtPos
    have hreal : ((badGeom + badCollision : ℕ) : ℝ) <
        (steps + 1 : ℕ) := by
      push_cast
      nlinarith
    exact_mod_cast hreal
  have havailableLower :
      (mCoeff - badGeomCoeff - badCollisionCoeff) * Real.sqrt nD ≤
        (((steps + 1) - (badGeom + badCollision) : ℕ) : ℝ) := by
    rw [Nat.cast_sub hbadLtSteps.le]
    push_cast
    calc
      (mCoeff - badGeomCoeff - badCollisionCoeff) * Real.sqrt nD =
          mCoeff * Real.sqrt nD -
            (badGeomCoeff * Real.sqrt nD +
              badCollisionCoeff * Real.sqrt nD) := by ring
      _ ≤ ((steps : ℝ) + 1) -
            ((badGeom : ℝ) + badCollision) := by
          exact sub_le_sub hstepsUpperLoss.le
            (add_le_add hbadGeomUpper hbadCollisionUpper)
  have houtputUpper : (output : ℝ) ≤ outputCoeff * nD := by
    dsimp only [output, exposureOutput]
    exact Nat.floor_le (by positivity)
  have houtputReal : (output : ℝ) ≤
      (((steps + 1) - (badGeom + badCollision) : ℕ) : ℝ) * piece := by
    calc
      (output : ℝ) ≤ outputCoeff * nD := houtputUpper
      _ ≤ ((mCoeff - badGeomCoeff - badCollisionCoeff) *
            pieceCoeff / 2) * nD := by
          exact mul_le_mul_of_nonneg_right houtput (Nat.cast_nonneg nD)
      _ = ((mCoeff - badGeomCoeff - badCollisionCoeff) *
            Real.sqrt nD) * (pieceCoeff / 2 * Real.sqrt nD) := by
          calc
            ((mCoeff - badGeomCoeff - badCollisionCoeff) *
                  pieceCoeff / 2) * (nD : ℝ) =
                ((mCoeff - badGeomCoeff - badCollisionCoeff) *
                  pieceCoeff / 2) * (Real.sqrt nD) ^ 2 := by rw [hsqrtSq]
            _ = _ := by ring
      _ ≤ (((steps + 1) - (badGeom + badCollision) : ℕ) : ℝ) *
            piece := by
          exact mul_le_mul havailableLower hpieceLower
            (by positivity) (by positivity)
  have houtputNat : output ≤
      ((steps + 1) - (badGeom + badCollision)) * piece := by
    exact_mod_cast houtputReal
  have houtputRpow := houtputLarge nD hNoutput
  rw [Real.rpow_one] at houtputRpow
  have houtputArgLarge : 2 ≤ outputCoeff * nD := by
    have hscaled := mul_le_mul_of_nonneg_left houtputRpow houtputCoeff.le
    rw [mul_div_cancel₀ 2 houtputCoeff.ne'] at hscaled
    simpa [mul_comm] using hscaled
  have houtputLower : outputCoeff * nD / 2 ≤ (output : ℝ) := by
    dsimp only [output, exposureOutput]
    exact half_le_natFloor houtputArgLarge
  have hscaleReal : a₂ * nZ * Real.sqrt nD ≤ (output : ℝ) := by
    calc
      a₂ * nZ * Real.sqrt nD
          ≤ a₂ * (deltaUpper * Real.sqrt nD) * Real.sqrt nD := by
            gcongr
      _ = (a₂ * deltaUpper) * nD := by
            calc
              a₂ * (deltaUpper * Real.sqrt nD) * Real.sqrt nD =
                  (a₂ * deltaUpper) * (Real.sqrt nD) ^ 2 := by ring
              _ = _ := by rw [hsqrtSq]
      _ ≤ outputCoeff * nD / 2 := by
            have hscaleHalf : a₂ * deltaUpper ≤ outputCoeff / 2 := by
              linarith only [hscale]
            simpa only [div_mul_eq_mul_div] using
              mul_le_mul_of_nonneg_right hscaleHalf (Nat.cast_nonneg nD)
      _ ≤ (output : ℝ) := houtputLower
  simpa only [s₀, badBudget, badDegree, edgeBudget, piece, steps, badGeom,
    badCollision, output] using
    And.intro hcandidate (And.intro hpieceNat (And.intro houtputNat hscaleReal))

end

end AugmentationInnerScalesRoundingScratch
end Erdos636
