import ErdosProblems.Erdos1165.SpatialInsertionConditional

open scoped BigOperators ENNReal

namespace Erdos1165.SpatialInsertionFiber

open MeasureTheory
open LazyDecomposition PathInsertion

/-!
# Closing the terminal insertion gap

A deterministic finite prefix censors the final run of removable blocks, so
that run is not geometric.  The standard finite remedy is to expose one more
retained block.  The old terminal run is then an ordinary gap before that
auxiliary retained block.  This file records the resulting exact fair-walk
cylinder masses and transports the normalized capped density to those
cylinders.
-/

/-- Append one auxiliary retained block after the terminal insertion gap. -/
def closedGapWord {o : Orientation} {i : ℕ}
    (r : Fin i → RetainedBlock o) (q : Fin (i + 1) → ℕ)
    (a : RetainedBlock o) : List Block :=
  insertGapVector r q ++ [(a : Block)]

@[simp] theorem closedGapWord_length {o : Orientation} {i : ℕ}
    (r : Fin i → RetainedBlock o) (q : Fin (i + 1) → ℕ)
    (a : RetainedBlock o) :
    (closedGapWord r q a).length = i + 1 + ∑ k, q k := by
  rw [closedGapWord, List.length_append, insertGapVector_length]
  simp
  omega

/-- Direction coordinates of a finite block list. -/
def blockListDirections (w : List Block) : Fin (2 * w.length) → Direction :=
  flattenBlockVector fun k ↦ w.get k

/-- The exact fair-step cylinder spelling a closed insertion word. -/
def closedGapCylinder {o : Orientation} {i : ℕ}
    (r : Fin i → RetainedBlock o) (q : Fin (i + 1) → ℕ)
    (a : RetainedBlock o) : Set StepPath :=
  {ω | stepPrefix (2 * (closedGapWord r q a).length) ω =
    blockListDirections (closedGapWord r q a)}

/-- A closed insertion cylinder has exactly its uniform block-word mass. -/
theorem fairSteps_closedGapCylinder {o : Orientation} {i : ℕ}
    (r : Fin i → RetainedBlock o) (q : Fin (i + 1) → ℕ)
    (a : RetainedBlock o) :
    fairSteps (closedGapCylinder r q a) =
      ENNReal.ofReal (uniformBlockWordMass (closedGapWord r q a).length) := by
  rw [closedGapCylinder, Erdos1165.fairSteps_stepPrefix_singleton_mass]
  unfold uniformBlockWordMass
  rw [pow_mul]
  rw [ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 1 / 16)]
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 16)]
  congr 1
  simp only [ENNReal.ofReal_one, ENNReal.ofReal_ofNat, one_div]
  calc
    (4 : ℝ≥0∞)⁻¹ ^ 2 = ((4 : ℝ≥0∞) ^ 2)⁻¹ := ENNReal.inv_pow.symm
    _ = (16 : ℝ≥0∞)⁻¹ := by norm_num

/-- Real mass of one closed insertion cylinder. -/
noncomputable def closedGapMass {o : Orientation} {i : ℕ}
    (r : Fin i → RetainedBlock o) (q : Fin (i + 1) → ℕ)
    (a : RetainedBlock o) : ℝ :=
  uniformBlockWordMass (closedGapWord r q a).length

/-- For a fixed closed external word, fair-cylinder mass is a constant times
the product geometric insertion weight. -/
theorem closedGapMass_eq_const_mul_gapVectorMass {o : Orientation} {i : ℕ}
    (r : Fin i → RetainedBlock o) (q : Fin (i + 1) → ℕ)
    (a : RetainedBlock o) :
    closedGapMass r q a = (1 / 15 : ℝ) ^ (i + 1) * gapVectorMass q := by
  classical
  unfold closedGapMass uniformBlockWordMass gapVectorMass geometricGapMass
  rw [closedGapWord_length]
  rw [Finset.prod_mul_distrib, Finset.prod_const]
  simp only [Finset.card_univ, Fintype.card_fin]
  rw [Finset.prod_pow_eq_pow_sum]
  rw [pow_add]
  have hconst :
      (1 / 16 : ℝ) ^ (i + 1) =
        (1 / 15 : ℝ) ^ (i + 1) * (15 / 16 : ℝ) ^ (i + 1) := by
    rw [← mul_pow]
    norm_num
  rw [hconst]
  ring

/-- Closed-cylinder mass after imposing the level/favorite truncation. -/
noncomputable def closedConditionedMass {o : Orientation} {i : ℕ}
    (x : Point) (r : Fin i → RetainedBlock o) (m : ℕ) (D : Finset Point)
    (q : Fin (i + 1) → ℕ) (a : RetainedBlock o) : ℝ := by
  classical
  exact if DominoTruncation x r m D q then closedGapMass r q a else 0

theorem closedConditionedMass_eq_const_mul {o : Orientation} {i : ℕ}
    (x : Point) (r : Fin i → RetainedBlock o) (m : ℕ) (D : Finset Point)
    (q : Fin (i + 1) → ℕ) (a : RetainedBlock o) :
    closedConditionedMass x r m D q a =
      (1 / 15 : ℝ) ^ (i + 1) * conditionedGapVectorMass x r m D q := by
  classical
  by_cases hq : DominoTruncation x r m D q
  · rw [closedConditionedMass, if_pos hq, conditionedGapVectorMass, if_pos hq,
      closedGapMass_eq_const_mul_gapVectorMass]
  · rw [closedConditionedMass, if_neg hq, conditionedGapVectorMass, if_neg hq]
    ring

/-- Normalizing constant for the finite experiment of capped, closed
insertion cylinders. -/
noncomputable def closedCappedPartition {o : Orientation} {i : ℕ}
    (x : Point) (r : Fin i → RetainedBlock o) (m cap : ℕ)
    (D : Finset Point) (a : RetainedBlock o) : ℝ :=
  ∑ q : CappedCoordinates i cap,
    closedConditionedMass x r m D (fun k ↦ (q k : ℕ)) a

theorem closedCappedPartition_eq_const_mul {o : Orientation} {i : ℕ}
    (x : Point) (r : Fin i → RetainedBlock o) (m cap : ℕ)
    (D : Finset Point) (a : RetainedBlock o) :
    closedCappedPartition x r m cap D a =
      (1 / 15 : ℝ) ^ (i + 1) * cappedConditionedPartition x r m cap D := by
  classical
  unfold closedCappedPartition cappedConditionedPartition
  simp_rw [closedConditionedMass_eq_const_mul]
  rw [Finset.mul_sum]

/-- Normalized mass in the finite closed-cylinder experiment. -/
noncomputable def closedCappedDensity {o : Orientation} {i : ℕ}
    (x : Point) (r : Fin i → RetainedBlock o) (m cap : ℕ)
    (D : Finset Point) (a : RetainedBlock o) (q : CappedCoordinates i cap) : ℝ :=
  closedConditionedMass x r m D (fun k ↦ (q k : ℕ)) a /
    closedCappedPartition x r m cap D a

/-- Closing the censored terminal gap does not alter the normalized capped
law: it is exactly the already-factorized conditioned insertion density. -/
theorem closedCappedDensity_eq_cappedConditionedDensity
    {o : Orientation} {i : ℕ}
    (x : Point) (r : Fin i → RetainedBlock o) (m cap : ℕ)
    (D : Finset Point) (a : RetainedBlock o) (q : CappedCoordinates i cap) :
    closedCappedDensity x r m cap D a q =
      cappedConditionedDensity x r m cap D q := by
  unfold closedCappedDensity cappedConditionedDensity
  rw [closedConditionedMass_eq_const_mul, closedCappedPartition_eq_const_mul]
  apply mul_div_mul_left
  positivity

/-- Hence the actual closed-cylinder conditional density has the spatial
product form required in the finite capped analogue of HLOZ (6.7). -/
theorem closedCappedDensity_factorization
    {o : Orientation} {i : ℕ}
    (x : Point) (r : Fin i → RetainedBlock o) (m cap : ℕ)
    (D : Finset Point) (a : RetainedBlock o) (q : CappedCoordinates i cap) :
    closedCappedDensity x r m cap D a q =
      ∏ b : ExternalDomino x r,
        cappedDominoDensity x r m cap D b ((groupByDominoEquiv x r _ q) b) := by
  rw [closedCappedDensity_eq_cappedConditionedDensity]
  exact cappedConditionedDensity_factorization x r m cap D q

end Erdos1165.SpatialInsertionFiber
