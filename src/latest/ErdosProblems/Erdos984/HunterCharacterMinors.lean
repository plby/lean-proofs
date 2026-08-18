/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos984.HunterCharacters

/-!
# Nonsingular minors of integer-character matrices

A collection of integer characters is jointly onto the target torus as soon
as one square minor of its coefficient matrix has nonzero determinant.  This
is the algebraic bridge used in the exceptional-rotation union bound.
-/

open Set Function MeasureTheory
open scoped BigOperators

namespace Erdos984

noncomputable section

/-- The real square minor obtained by selecting one ambient coordinate for
each row of an integer-character matrix. -/
def integerCharacterMinorRealMatrix {D R : Type*}
    (ξ : R → D → ℤ) (σ : R → D) : Matrix R R ℝ :=
  fun r c ↦ (ξ r (σ c) : ℝ)

/-- A nonzero square minor makes the full real coefficient matrix
surjective. -/
lemma integerCharacterRealMatrix_surjective_of_minor
    {D R : Type*} [Fintype D] [Fintype R]
    [DecidableEq R]
    (ξ : R → D → ℤ) (σ : R → D)
    (hdet : (integerCharacterMinorRealMatrix ξ σ).det ≠ 0) :
    Surjective (integerCharacterRealMatrix ξ).mulVec := by
  classical
  let A : Matrix R R ℝ := integerCharacterMinorRealMatrix ξ σ
  have hAunit : IsUnit A := (Matrix.isUnit_iff_isUnit_det A).2
    (isUnit_iff_ne_zero.2 hdet)
  have hAsurj : Surjective A.mulVec :=
    Matrix.mulVec_surjective_iff_isUnit.2 hAunit
  intro y
  obtain ⟨v, hv⟩ := hAsurj y
  let u : D → ℝ := ∑ c, Pi.single (σ c) (v c)
  refine ⟨u, ?_⟩
  rw [← hv]
  have hsum :
      (integerCharacterRealMatrix ξ).mulVec u =
        ∑ c, (integerCharacterRealMatrix ξ).mulVec
          (Pi.single (σ c) (v c)) := by
    simpa [u] using
      (Matrix.mulVec_sum (integerCharacterRealMatrix ξ) Finset.univ
        (fun c ↦ Pi.single (σ c) (v c)))
  rw [hsum]
  ext r
  simp [Matrix.mulVec, dotProduct, A, integerCharacterMinorRealMatrix,
    integerCharacterRealMatrix, mul_comm]

/-- Consequently, a nonzero square minor makes the associated tuple of
integer characters surjective on finite unit tori. -/
lemma integerCharacterTuple_surjective_of_minor
    {D R : Type*} [Fintype D] [Fintype R]
    [DecidableEq R]
    (ξ : R → D → ℤ) (σ : R → D)
    (hdet : (integerCharacterMinorRealMatrix ξ σ).det ≠ 0) :
    Surjective (integerCharacterTuple ξ : UnitAddTorus D → UnitAddTorus R) :=
  integerCharacterTuple_surjective_of_real ξ
    (integerCharacterRealMatrix_surjective_of_minor ξ σ hdet)

/-- The simultaneous small-phase event attached to a nonzero minor has its
exact product-Haar volume. -/
lemma volume_small_nsmul_character_event_of_minor
    {D R : Type*} [Fintype D] [Fintype R]
    [DecidableEq R]
    (n : ℕ) (hn : 0 < n) (ξ : R → D → ℤ)
    (σ : R → D)
    (hdet : (integerCharacterMinorRealMatrix ξ σ).det ≠ 0)
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδhalf : δ ≤ (1 : ℝ) / 2) :
    volume (nsmulIntegerCharacterTuple n ξ ⁻¹'
      Metric.closedBall (0 : UnitAddTorus R) δ) =
      (ENNReal.ofReal (2 * δ)) ^ Fintype.card R :=
  volume_small_nsmul_character_event n hn ξ
    (integerCharacterRealMatrix_surjective_of_minor ξ σ hdet)
    hδ0 hδhalf

end

end Erdos984
