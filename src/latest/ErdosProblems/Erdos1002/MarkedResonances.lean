import ErdosProblems.Erdos1002.FactorialMoments
import ErdosProblems.Erdos1002.ResonanceCellMeasure
import ErdosProblems.Erdos1002.Shots

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Marked resonance coordinates and finite counts

This file gives literal finite definitions for the marked point process used
in the manuscript.  It deliberately avoids an abstract point-process API:
all factorial moments reduce to measurable natural-valued finite counts.
-/

open MeasureTheory Set
open scoped BigOperators

namespace Erdos1002

noncomputable section

local instance markedResonancesPropDecidable (P : Prop) : Decidable P :=
  Classical.propDecidable P

/-- Logarithmic denominator coordinate. -/
def resonanceTimeCoordinate (N p : ℕ) : ℝ :=
  Real.log (p : ℝ) / Real.log (N : ℝ)

/-- The `[0,1)` representative of the torus mark `N δ_p mod 1`. -/
def resonanceTorusCoordinate (N p : ℕ) (α : ℝ) : ℝ :=
  Int.fract ((N : ℝ) * resonanceDelta p α)

/-- The three coordinates of one marked resonance. -/
def markedResonancePoint (N p : ℕ) (α : ℝ) : ℝ × ℝ × ℝ :=
  (resonanceTimeCoordinate N p,
    scaledResonanceCoordinate N p α,
    resonanceTorusCoordinate N p α)

theorem measurable_resonanceTorusCoordinate (N p : ℕ) :
    Measurable (resonanceTorusCoordinate N p) := by
  unfold resonanceTorusCoordinate
  exact (measurable_const.mul (measurable_resonanceDelta p)).fract

theorem measurable_markedResonancePoint (N p : ℕ) :
    Measurable (markedResonancePoint N p) := by
  exact Measurable.prodMk measurable_const
    (Measurable.prodMk (measurable_scaledResonanceCoordinate N p)
      (measurable_resonanceTorusCoordinate N p))

theorem resonanceTorusCoordinate_mem_Ico (N p : ℕ) (α : ℝ) :
    resonanceTorusCoordinate N p α ∈ Ico (0 : ℝ) 1 := by
  exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

/-- Periodicity makes the representative of the torus mark harmless in the
shot functional. -/
theorem bernoulliMark_resonanceTorusCoordinate (N p : ℕ) (α : ℝ) :
    bernoulliMark (resonanceTorusCoordinate N p α) =
      bernoulliMark ((N : ℝ) * resonanceDelta p α) := by
  let x : ℝ := (N : ℝ) * resonanceDelta p α
  have hx : Int.fract x + (⌊x⌋ : ℤ) = x := Int.fract_add_floor x
  calc
    bernoulliMark (resonanceTorusCoordinate N p α) =
        bernoulliMark (Int.fract x) := by rfl
    _ = bernoulliMark (Int.fract x + (⌊x⌋ : ℤ)) := by
      rw [bernoulliMark_add_intCast]
    _ = bernoulliMark x := by rw [hx]

/-- The number of primitive marked resonances with denominator in `[1,P]`
whose mark lies in `B`. -/
def markedResonanceCount (N P : ℕ) (B : Set (ℝ × ℝ × ℝ)) (α : ℝ) : ℕ :=
  by
    classical
    exact ∑ p ∈ Finset.Icc 1 P,
      if IsPrimitiveResonance p α ∧ markedResonancePoint N p α ∈ B then 1 else 0

theorem measurable_markedResonanceCount (N P : ℕ)
    {B : Set (ℝ × ℝ × ℝ)} (hB : MeasurableSet B) :
    Measurable (markedResonanceCount N P B) := by
  classical
  unfold markedResonanceCount
  apply Finset.measurable_fun_sum
  intro p _hp
  apply Measurable.ite
  · exact (measurableSet_isPrimitiveResonance p).inter
      (hB.preimage (measurable_markedResonancePoint N p))
  · exact measurable_const
  · exact measurable_const

/-- Rectangle form of the marked count. -/
def markedResonanceRectangleCount (N P : ℕ)
    (T X U : Set ℝ) (α : ℝ) : ℕ :=
  markedResonanceCount N P (T ×ˢ X ×ˢ U) α

theorem measurable_markedResonanceRectangleCount (N P : ℕ)
    {T X U : Set ℝ} (hT : MeasurableSet T) (hX : MeasurableSet X)
    (hU : MeasurableSet U) :
    Measurable (markedResonanceRectangleCount N P T X U) := by
  exact measurable_markedResonanceCount N P (hT.prod (hX.prod hU))

/-- Expanding the definition of a rectangle count introduces no hidden
point-process convention. -/
theorem markedResonanceRectangleCount_eq (N P : ℕ)
    (T X U : Set ℝ) (α : ℝ) :
    markedResonanceRectangleCount N P T X U α =
      ∑ p ∈ Finset.Icc 1 P,
        if IsPrimitiveResonance p α ∧
            resonanceTimeCoordinate N p ∈ T ∧
            scaledResonanceCoordinate N p α ∈ X ∧
            resonanceTorusCoordinate N p α ∈ U then 1 else 0 := by
  classical
  unfold markedResonanceRectangleCount markedResonanceCount markedResonancePoint
  apply Finset.sum_congr rfl
  intro p _hp
  simp only [mem_prod]

theorem markedResonanceCount_le (N P : ℕ)
    (B : Set (ℝ × ℝ × ℝ)) (α : ℝ) :
    markedResonanceCount N P B α ≤ P := by
  classical
  unfold markedResonanceCount
  calc
    (∑ p ∈ Finset.Icc 1 P,
        if IsPrimitiveResonance p α ∧ markedResonancePoint N p α ∈ B
          then 1 else 0) ≤
        ∑ _p ∈ Finset.Icc 1 P, 1 := by
      apply Finset.sum_le_sum
      intro p _hp
      split_ifs <;> omega
    _ = (Finset.Icc 1 P).card := by simp
    _ ≤ P := by
      rw [Nat.card_Icc]
      omega

/-- The falling factorial of a marked count is literally the number of
ordered distinct selections from the retained denominator set. -/
theorem markedResonanceCount_descFactorial_eq_card_embeddings
    (N P r : ℕ) (B : Set (ℝ × ℝ × ℝ)) (α : ℝ) :
    (markedResonanceCount N P B α).descFactorial r =
      Fintype.card
        (Fin r ↪
          (Finset.filter
            (fun p ↦ IsPrimitiveResonance p α ∧ markedResonancePoint N p α ∈ B)
            (Finset.Icc 1 P) : Finset ℕ)) := by
  classical
  let s : Finset ℕ := Finset.filter
    (fun p ↦ IsPrimitiveResonance p α ∧ markedResonancePoint N p α ∈ B)
    (Finset.Icc 1 P)
  have hcount : markedResonanceCount N P B α = s.card := by
    unfold markedResonanceCount s
    exact Finset.sum_boole _ _
  rw [hcount]
  exact (card_orderedDistinctTuples s r).symm

end

end Erdos1002
