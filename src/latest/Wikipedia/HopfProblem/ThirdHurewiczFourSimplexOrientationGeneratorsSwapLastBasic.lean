import Wikipedia.HopfProblem.ThirdHurewiczThreeSimplexBasic
import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedTetrahedronBasic

/-!
# The last-vertex swap and its cubical reflection

These are literal maps of the standard tetrahedron and native three-cube.
On every cube facet, the swapped simplex quotient and the reflected simplex
quotient have a common zero barycentric coordinate.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.ThirdHurewicz

open FirstHurewicz

/-- Exchange the last two barycentric coordinates of the actual tetrahedron. -/
def threeSimplexSwapLast : C(Simplex 3, Simplex 3) where
  toFun s := ⟨![s 0, s 1, s 3, s 2], by
    constructor
    · intro i
      fin_cases i <;> exact s.property.1 _
    · have hs := s.property.2
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero,
        Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one] at hs ⊢
      change s 0 + (s 1 + (s 2 + s 3)) = 1 at hs
      simpa only [add_comm (s 2) (s 3)] using hs⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    fin_cases i
    · change Continuous fun s : Simplex 3 => s 0
      exact (continuous_apply 0).comp continuous_subtype_val
    · change Continuous fun s : Simplex 3 => s 1
      exact (continuous_apply 1).comp continuous_subtype_val
    · change Continuous fun s : Simplex 3 => s 3
      exact (continuous_apply 3).comp continuous_subtype_val
    · change Continuous fun s : Simplex 3 => s 2
      exact (continuous_apply 2).comp continuous_subtype_val

@[simp] theorem threeSimplexSwapLast_zero (s : Simplex 3) :
    threeSimplexSwapLast s 0 = s 0 := rfl

@[simp] theorem threeSimplexSwapLast_one (s : Simplex 3) :
    threeSimplexSwapLast s 1 = s 1 := rfl

@[simp] theorem threeSimplexSwapLast_two (s : Simplex 3) :
    threeSimplexSwapLast s 2 = s 3 := rfl

@[simp] theorem threeSimplexSwapLast_three (s : Simplex 3) :
    threeSimplexSwapLast s 3 = s 2 := rfl

theorem threeSimplexSwapLast_boundary (s : Simplex 3)
    (hs : s ∈ threeSimplexBoundary) : threeSimplexSwapLast s ∈ threeSimplexBoundary := by
  obtain ⟨i, hi⟩ := hs
  fin_cases i
  · exact ⟨0, hi⟩
  · exact ⟨1, hi⟩
  · exact ⟨3, hi⟩
  · exact ⟨2, hi⟩

/-- Reversal of the last native cube coordinate. -/
def cubeThirdLastReverse : C(Fin 3 → I, Fin 3 → I) where
  toFun u := ![u 0, u 1, σ (u 2)]
  continuous_toFun := by
    apply continuous_pi
    intro i
    fin_cases i <;> dsimp <;> fun_prop

@[simp] theorem cubeThirdLastReverse_zero (u : Fin 3 → I) :
    cubeThirdLastReverse u 0 = u 0 := rfl

@[simp] theorem cubeThirdLastReverse_one (u : Fin 3 → I) :
    cubeThirdLastReverse u 1 = u 1 := rfl

@[simp] theorem cubeThirdLastReverse_two (u : Fin 3 → I) :
    cubeThirdLastReverse u 2 = σ (u 2) := rfl

/-- The affine simplex interpolation stays in a single boundary face on each
native cube facet. This uses the actual PL quotient, not an orientation axiom. -/
theorem threeSimplexSwapLast_commonZero (u : Fin 3 → I)
    (hu : u ∈ Cube.boundary (Fin 3)) :
    ∃ i : Fin 4, threeSimplexSwapLast (threeSimplexQuotient u) i = 0 ∧
      threeSimplexQuotient (cubeThirdLastReverse u) i = 0 := by
  rcases hu with ⟨j, hj | hj⟩
  · fin_cases j
    · change u 0 = 0 at hj
      refine ⟨1, ?_, ?_⟩
      · simp [hj, min_eq_left (u 1).property.1]
      · simp [hj, min_eq_left (u 1).property.1]
    · change u 1 = 0 at hj
      refine ⟨2, ?_, ?_⟩
      · simp [hj, min_eq_left (u 2).property.1, min_eq_right (u 0).property.1]
      · simp only [threeSimplexQuotient_two, cubeThirdLastReverse_zero,
          cubeThirdLastReverse_one, cubeThirdLastReverse_two, hj]
        change min (u 0 : ℝ) 0 - min (u 0 : ℝ) (min 0 (σ (u 2) : ℝ)) = 0
        rw [min_eq_right (u 0).property.1, min_eq_left (σ (u 2)).property.1,
          min_eq_right (u 0).property.1, sub_self]
    · change u 2 = 0 at hj
      refine ⟨2, ?_, ?_⟩
      · simp [hj, min_eq_right (u 1).property.1, min_eq_right (u 0).property.1]
      · simp [hj, min_eq_left (u 1).property.2]
  · fin_cases j
    · change u 0 = 1 at hj
      exact ⟨0, by simp [hj], by simp [hj]⟩
    · change u 1 = 1 at hj
      exact ⟨1, by simp [hj, min_eq_left (u 0).property.2],
        by simp [hj, min_eq_left (u 0).property.2]⟩
    · change u 2 = 1 at hj
      refine ⟨3, ?_, ?_⟩
      · simp [hj, min_eq_left (u 1).property.2]
      · simp [hj, min_eq_right (u 1).property.1, min_eq_right (u 0).property.1]

variable {X : Type} [TopologicalSpace X] {x : X}

/-- The original singular simplex with its last two vertices exchanged. -/
def basedThreeSimplexSwapLast (τ : BasedThreeSimplex x) : BasedThreeSimplex x :=
  ⟨τ.val.comp threeSimplexSwapLast,
    fun s hs => τ.property _ (threeSimplexSwapLast_boundary s hs)⟩

@[simp] theorem basedThreeSimplexSwapLast_apply (τ : BasedThreeSimplex x)
    (s : Simplex 3) :
    (basedThreeSimplexSwapLast τ).val s = τ.val (threeSimplexSwapLast s) := rfl

/-- The explicit cubical reflection is precisely Mathlib's loop reversal. -/
theorem symmAt_last_apply (p : GenLoop (Fin 3) X x) (u : Fin 3 → I) :
    GenLoop.symmAt (2 : Fin 3) p u = p (cubeThirdLastReverse u) := by
  change p (fun j => if j = (2 : Fin 3) then σ (u 2) else u j) = _
  congr 1
  funext j
  fin_cases j <;> rfl

end Wikipedia.HopfProblem.ThirdHurewicz
