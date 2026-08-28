import Wikipedia.HopfProblem.ThirdHurewiczFourSimplexBasic
import Wikipedia.HopfProblem.ThirdHurewiczFourSimplexLattice

/-!
# Two explicit piecewise-affine fillings of a labeled cube

For the first filling the eight cube vertices have labels
`000=001=0`, `100=1`, `010=110=2`, `011=3`, `101=111=4`.
The second map interpolates the labeling reflected in the first coordinate.
The six standard ordered chambers therefore contain respectively two and
three nondegenerate tetrahedra.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.ThirdHurewicz

open FirstHurewicz

/-- The first actual piecewise-affine cube filling in the four-simplex. -/
def fourSimplexFillA : C(Fin 3 → I, Simplex 4) where
  toFun u := ⟨![1 - max (u 0 : ℝ) (u 1 : ℝ),
    (u 0 : ℝ) - min (u 0 : ℝ) (max (u 1 : ℝ) (u 2 : ℝ)),
    (u 1 : ℝ) - min (u 1 : ℝ) (u 2 : ℝ),
    min (u 1 : ℝ) (u 2 : ℝ) - min (u 0 : ℝ) (min (u 1 : ℝ) (u 2 : ℝ)),
    min (u 0 : ℝ) (u 2 : ℝ)], by
      constructor
      · intro i
        fin_cases i
        · exact sub_nonneg.mpr (max_le (u 0).property.2 (u 1).property.2)
        · exact sub_nonneg.mpr (min_le_left _ _)
        · exact sub_nonneg.mpr (min_le_left _ _)
        · exact sub_nonneg.mpr (min_le_right _ _)
        · exact le_min (u 0).property.1 (u 2).property.1
      · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero,
          Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one]
        simpa only [add_assoc] using fourSimplex_coordinates_sum_A (u 0) (u 1) (u 2)⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    fin_cases i <;> dsimp <;> fun_prop

/-- The PL filling for the first-coordinate-reflected vertex labeling. -/
def fourSimplexFillB : C(Fin 3 → I, Simplex 4) where
  toFun u := ⟨![(u 0 : ℝ) - min (u 0 : ℝ) (u 1 : ℝ),
    1 - max (u 0 : ℝ) (max (u 1 : ℝ) (u 2 : ℝ)),
    (u 1 : ℝ) - min (u 1 : ℝ) (u 2 : ℝ),
    min (u 0 : ℝ) (min (u 1 : ℝ) (u 2 : ℝ)),
    (u 2 : ℝ) - min (u 0 : ℝ) (u 2 : ℝ)], by
      constructor
      · intro i
        fin_cases i
        · exact sub_nonneg.mpr (min_le_left _ _)
        · exact sub_nonneg.mpr
            (max_le (u 0).property.2 (max_le (u 1).property.2 (u 2).property.2))
        · exact sub_nonneg.mpr (min_le_left _ _)
        · exact le_min (u 0).property.1 (le_min (u 1).property.1 (u 2).property.1)
        · exact sub_nonneg.mpr (min_le_right _ _)
      · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero,
          Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one]
        simpa only [add_assoc] using fourSimplex_coordinates_sum_B (u 0) (u 1) (u 2)⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    fin_cases i <;> dsimp <;> fun_prop

@[simp] theorem fourSimplexFillA_zero (u : Fin 3 → I) :
    fourSimplexFillA u 0 = 1 - max (u 0 : ℝ) (u 1 : ℝ) := rfl

@[simp] theorem fourSimplexFillA_one (u : Fin 3 → I) :
    fourSimplexFillA u 1 = (u 0 : ℝ) - min (u 0 : ℝ) (max (u 1 : ℝ) (u 2 : ℝ)) := rfl

@[simp] theorem fourSimplexFillA_two (u : Fin 3 → I) :
    fourSimplexFillA u 2 = (u 1 : ℝ) - min (u 1 : ℝ) (u 2 : ℝ) := rfl

@[simp] theorem fourSimplexFillA_three (u : Fin 3 → I) :
    fourSimplexFillA u 3 = min (u 1 : ℝ) (u 2 : ℝ) -
      min (u 0 : ℝ) (min (u 1 : ℝ) (u 2 : ℝ)) := rfl

@[simp] theorem fourSimplexFillA_four (u : Fin 3 → I) :
    fourSimplexFillA u 4 = min (u 0 : ℝ) (u 2 : ℝ) := rfl

@[simp] theorem fourSimplexFillB_zero (u : Fin 3 → I) :
    fourSimplexFillB u 0 = (u 0 : ℝ) - min (u 0 : ℝ) (u 1 : ℝ) := rfl

@[simp] theorem fourSimplexFillB_one (u : Fin 3 → I) :
    fourSimplexFillB u 1 = 1 - max (u 0 : ℝ) (max (u 1 : ℝ) (u 2 : ℝ)) := rfl

@[simp] theorem fourSimplexFillB_two (u : Fin 3 → I) :
    fourSimplexFillB u 2 = (u 1 : ℝ) - min (u 1 : ℝ) (u 2 : ℝ) := rfl

@[simp] theorem fourSimplexFillB_three (u : Fin 3 → I) :
    fourSimplexFillB u 3 = min (u 0 : ℝ) (min (u 1 : ℝ) (u 2 : ℝ)) := rfl

@[simp] theorem fourSimplexFillB_four (u : Fin 3 → I) :
    fourSimplexFillB u 4 = (u 2 : ℝ) - min (u 0 : ℝ) (u 2 : ℝ) := rfl

/-- Reflection in the first coordinate of the original native cube. -/
def fourSimplexReflectFirst : C(Fin 3 → I, Fin 3 → I) where
  toFun u := ![σ (u 0), u 1, u 2]
  continuous_toFun := by
    apply continuous_pi
    intro i
    fin_cases i <;> dsimp <;> fun_prop

@[simp] theorem fourSimplexReflectFirst_apply (u : Fin 3 → I) :
    fourSimplexReflectFirst u = ![σ (u 0), u 1, u 2] := rfl

@[simp] theorem fourSimplexReflectFirst_involutive (u : Fin 3 → I) :
    fourSimplexReflectFirst (fourSimplexReflectFirst u) = u := by
  funext i
  fin_cases i <;> simp

theorem fourSimplexReflectFirst_boundary (u : Fin 3 → I)
    (hu : u ∈ Cube.boundary (Fin 3)) :
    fourSimplexReflectFirst u ∈ Cube.boundary (Fin 3) := by
  rcases hu with ⟨i, hi | hi⟩
  · fin_cases i
    · change u 0 = 0 at hi
      exact ⟨0, Or.inr (by simp [hi])⟩
    · exact ⟨1, Or.inl (by simpa using hi)⟩
    · exact ⟨2, Or.inl (by simpa using hi)⟩
  · fin_cases i
    · change u 0 = 1 at hi
      exact ⟨0, Or.inl (by simp [hi])⟩
    · exact ⟨1, Or.inr (by simpa using hi)⟩
    · exact ⟨2, Or.inr (by simpa using hi)⟩

end Wikipedia.HopfProblem.ThirdHurewicz
