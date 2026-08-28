import Wikipedia.HopfProblem.ToricDoubleLocus

/-!
# Affine axis parametrizations of the double curves

For each edge direction, the lower reference triangle and the upper triangle
across that edge give two affine lines in the actual toric space. Their
transition is inversion on the punctured line.
-/

noncomputable section

open Set Topology
open scoped ContDiff Matrix

namespace Wikipedia.HopfProblem.ToricFan.Triangle

open ToricCharts

def axisPoint (s : Triangle) (i : Fin 3) (z : ℂ) : CoordinateSpace 3 :=
  Pi.single (s.axisIndex i) z

@[simp] theorem axisPoint_zero (s : Triangle) (i : Fin 3) : axisPoint s i 0 = 0 := by
  simp [axisPoint]

@[simp] theorem axisPoint_apply_axisIndex (s : Triangle) (i : Fin 3) (z : ℂ) :
    axisPoint s i z (s.axisIndex i) = z := by simp [axisPoint]

theorem axisPoint_apply_of_ne (s : Triangle) (i j : Fin 3) (z : ℂ) (hj : j ≠ s.axisIndex i) :
    axisPoint s i z j = 0 := by simp [axisPoint, hj]

theorem axisPoint_injective (s : Triangle) (i : Fin 3) : Function.Injective (axisPoint s i) := by
  intro z w h
  simpa only [axisPoint_apply_axisIndex] using congrFun h (s.axisIndex i)

theorem axisPoint_holomorphic (s : Triangle) (i : Fin 3) : ContDiff ℂ ω (axisPoint s i) := by
  apply contDiff_pi.mpr
  intro j
  by_cases hj : j = s.axisIndex i
  · subst j
    simp only [axisPoint_apply_axisIndex]
    exact contDiff_id
  · simpa only [axisPoint_apply_of_ne s i j _ hj] using
      (contDiff_const : ContDiff ℂ ω (fun _ : ℂ => (0 : ℂ)))

@[simp] theorem time_axisPoint (s : Triangle) (i : Fin 3) (z : ℂ) :
    time (axisPoint s i z) = 0 := by
  cases hs : s.upper <;> fin_cases i <;> simp [time, axisPoint, axisIndex, hs]

theorem eq_axisPoint_iff (s : Triangle) (i : Fin 3) (z : CoordinateSpace 3) :
    z = axisPoint s i (z (s.axisIndex i)) ↔ ∀ j, j ≠ s.axisIndex i → z j = 0 := by
  constructor
  · intro h j hj
    rw [h]
    exact axisPoint_apply_of_ne s i j _ hj
  · intro h
    ext j
    by_cases hj : j = s.axisIndex i
    · subst j
      simp
    · rw [axisPoint_apply_of_ne s i j _ hj, h j hj]

@[simp] theorem axisIndex_shift (s : Triangle) (v : Fin 2 → ℤ) (i : Fin 3) :
    (s.shift v).axisIndex i = s.axisIndex i := rfl

@[simp] theorem axisPoint_shift (s : Triangle) (v : Fin 2 → ℤ) (i : Fin 3) (z : ℂ) :
    axisPoint (s.shift v) i z = axisPoint s i z := rfl

/-- The upper triangle adjacent to the lower reference triangle along edge `i`. -/
def upperNeighbour (i : Fin 3) : Triangle :=
  ![⟨0, -1, true⟩, ⟨-1, 0, true⟩, ⟨0, 0, true⟩] i

@[simp] theorem upperNeighbour_upper (i : Fin 3) : (upperNeighbour i).upper = true := by
  fin_cases i <;> rfl

theorem axis_transition_source_iff (i : Fin 3) (z : ℂ) :
    axisPoint ToricSpace.referenceTriangle i z ∈
      (chartChange ToricSpace.referenceTriangle (upperNeighbour i)).source ↔ z ≠ 0 := by
  fin_cases i <;>
    simp [chartChange_source, domain, transition, dual, rays, upperNeighbour,
      ToricSpace.referenceTriangle, axisPoint, axisIndex, Matrix.mul_apply,
      Fin.sum_univ_succ, Fin.forall_fin_succ]

theorem axis_transition (i : Fin 3) (z : ℂ) :
    chartChange ToricSpace.referenceTriangle (upperNeighbour i)
      (axisPoint ToricSpace.referenceTriangle i z) = axisPoint (upperNeighbour i) i z⁻¹ := by
  ext j
  fin_cases i <;> fin_cases j <;>
    simp [chartChange, changeOfCoordinates, monomial, transition, dual, rays, upperNeighbour,
      ToricSpace.referenceTriangle, axisPoint, axisIndex, Fin.prod_univ_succ]

end Wikipedia.HopfProblem.ToricFan.Triangle

namespace Wikipedia.HopfProblem.ToricSpace

open ToricCharts ToricFan Triangle

theorem scale_axisPoint (s : Triangle) (u : ActingTorus) (i : Fin 3) (z : ℂ) :
    scale s u (axisPoint s i z) = axisPoint s i (factors s u (s.axisIndex i) * z) := by
  ext j
  by_cases hj : j = s.axisIndex i
  · subst j
    simp [scale]
  · simp [scale, axisPoint_apply_of_ne s i j _ hj]

theorem axis_inclusion_inversion (i : Fin 3) {z : ℂ} (hz : z ≠ 0) :
    inclusion referenceTriangle (axisPoint referenceTriangle i z) =
      inclusion (upperNeighbour i) (axisPoint (upperNeighbour i) i z⁻¹) :=
  (inclusion_eq_iff _ _ _ _).mpr ⟨(axis_transition_source_iff i z).mpr hz, axis_transition i z⟩

theorem twistedTranslate_axisPoint (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℤ) (s : Triangle) (i : Fin 3) (z : ℂ) :
    twistedTranslate C v (inclusion s (axisPoint s i z)) =
      inclusion (s.shift (cuspVector v))
        (axisPoint (s.shift (cuspVector v)) i
          (factors (s.shift (cuspVector v)) (fibreMultiplier (exponentialMultiplier C v 0))
            ((s.shift (cuspVector v)).axisIndex i) * z)) := by
  rw [twistedTranslate, translate_inclusion, variableMultiplier_inclusion, time_axisPoint]
  exact congrArg (inclusion _) (scale_axisPoint (s.shift (cuspVector v)) _ i z)

end Wikipedia.HopfProblem.ToricSpace
