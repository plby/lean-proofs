import Mathlib.Tactic
import ErdosProblems.Erdos733.ST.PlanarRot90CoefficientUniqueness

open Classical
noncomputable section

-- [TABLET NODE: PlanarRot90AngleCoordinateDecomposition]
lemma PlanarRot90AngleCoordinateDecomposition (β α rb ra : ℝ) (hrb : rb ≠ 0) :
    let e : ℝ → EuclideanSpace ℝ (Fin 2) :=
      fun t => WithLp.toLp 2
        (fun k : Fin 2 => if k = 0 then Real.cos t else Real.sin t)
    let base : EuclideanSpace ℝ (Fin 2) := rb • e β
    let x : ℝ := (ra / rb) * Real.cos (α - β)
    let y : ℝ := (ra / rb) * Real.sin (α - β)
    ra • e α = x • base + y • PlanarRot90 base ∧
      ∀ {x' y' : ℝ},
        ra • e α = x' • base + y' • PlanarRot90 base →
          x' = x ∧ y' = y := by
-- BODY
  dsimp only
  let e : ℝ → EuclideanSpace ℝ (Fin 2) :=
    fun t => WithLp.toLp 2
      (fun k : Fin 2 => if k = 0 then Real.cos t else Real.sin t)
  let base : EuclideanSpace ℝ (Fin 2) := rb • e β
  let x : ℝ := (ra / rb) * Real.cos (α - β)
  let y : ℝ := (ra / rb) * Real.sin (α - β)
  have hdecomp : ra • e α = x • base + y • PlanarRot90 base := by
    dsimp [base, x, y, e]
    apply PiLp.ext
    intro k
    fin_cases k
    · simp [PlanarRot90, Real.cos_sub, Real.sin_sub]
      field_simp [hrb]
      ring_nf
      calc
        ra * Real.cos α =
            ra * Real.cos α * 1 := by ring
        _ = ra * Real.cos α * (Real.cos β ^ 2 + Real.sin β ^ 2) := by
          rw [Real.cos_sq_add_sin_sq]
        _ = ra * Real.cos α * Real.cos β ^ 2 +
              ra * Real.cos α * Real.sin β ^ 2 := by ring_nf
    · simp [PlanarRot90, Real.cos_sub, Real.sin_sub]
      field_simp [hrb]
      ring_nf
      calc
        ra * Real.sin α =
            ra * Real.sin α * 1 := by ring
        _ = ra * Real.sin α * (Real.sin β ^ 2 + Real.cos β ^ 2) := by
          rw [Real.sin_sq_add_cos_sq]
        _ = ra * Real.sin α * Real.sin β ^ 2 +
              ra * Real.sin α * Real.cos β ^ 2 := by ring_nf
  have hbase_ne : base ≠ 0 := by
    intro hz
    have hcoord0 := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 0) hz
    have hcoord1 := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 1) hz
    dsimp [base, e] at hcoord0 hcoord1
    simp at hcoord0 hcoord1
    rcases hcoord0 with hrb0 | hcos0
    · exact hrb hrb0
    · rcases hcoord1 with hrb0 | hsin0
      · exact hrb hrb0
      · nlinarith [Real.sin_sq_add_cos_sq β]
  refine ⟨hdecomp, ?_⟩
  intro x' y' hrep
  have hcoeff :=
    PlanarRot90CoefficientUniqueness (d := base) (v := ra • e α)
      hbase_ne hrep
  have hcoeff' :=
    PlanarRot90CoefficientUniqueness (d := base) (v := ra • e α)
      hbase_ne hdecomp
  constructor <;> linarith
