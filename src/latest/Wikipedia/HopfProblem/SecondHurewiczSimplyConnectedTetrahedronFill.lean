import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedTetrahedronBasic

/-!
# Two triangles filling a boundary quadrilateral of the tetrahedron

The square is filled along its diagonal from vertex zero to vertex two.
Its lower triangle is face three, and its positively oriented upper triangle
is face one. A cyclic change of the four vertices supplies the other pair.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected

open FirstHurewicz

/-- The diagonal `02` filling, in actual tetrahedral barycentric coordinates. -/
def tetrahedronQuadrilateralA : C(Fin 2 → I, Simplex 3) where
  toFun u := ⟨![1 - max (u 0 : ℝ) (u 1 : ℝ),
    (u 0 : ℝ) - min (u 0 : ℝ) (u 1 : ℝ),
    min (u 0 : ℝ) (u 1 : ℝ),
    (u 1 : ℝ) - min (u 0 : ℝ) (u 1 : ℝ)], by
      constructor
      · intro i
        fin_cases i
        · exact sub_nonneg.mpr (max_le (u 0).property.2 (u 1).property.2)
        · exact sub_nonneg.mpr (min_le_left _ _)
        · exact le_min (u 0).property.1 (u 1).property.1
        · exact sub_nonneg.mpr (min_le_right _ _)
      · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero,
          Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one]
        rcases le_total (u 0 : ℝ) (u 1 : ℝ) with h | h
        · rw [min_eq_left h, max_eq_right h]
          ring
        · rw [min_eq_right h, max_eq_left h]
          ring⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    fin_cases i <;> dsimp <;> fun_prop

@[simp] theorem tetrahedronQuadrilateralA_zero (u : Fin 2 → I) :
    tetrahedronQuadrilateralA u 0 = 1 - max (u 0 : ℝ) (u 1 : ℝ) := rfl

@[simp] theorem tetrahedronQuadrilateralA_one (u : Fin 2 → I) :
    tetrahedronQuadrilateralA u 1 = (u 0 : ℝ) - min (u 0 : ℝ) (u 1 : ℝ) := rfl

@[simp] theorem tetrahedronQuadrilateralA_two (u : Fin 2 → I) :
    tetrahedronQuadrilateralA u 2 = min (u 0 : ℝ) (u 1 : ℝ) := rfl

@[simp] theorem tetrahedronQuadrilateralA_three (u : Fin 2 → I) :
    tetrahedronQuadrilateralA u 3 = (u 1 : ℝ) - min (u 0 : ℝ) (u 1 : ℝ) := rfl

theorem tetrahedronQuadrilateralA_boundary (u : Fin 2 → I)
    (hu : u ∈ Cube.boundary (Fin 2)) :
    tetrahedronQuadrilateralA u ∈ tetrahedronOneSkeleton := by
  rcases hu with ⟨i, hi | hi⟩
  · fin_cases i
    · change u 0 = 0 at hi
      refine ⟨1, 2, by decide, ?_, ?_⟩ <;>
        simp [hi, min_eq_left (u 1).property.1]
    · change u 1 = 0 at hi
      refine ⟨2, 3, by decide, ?_, ?_⟩ <;>
        simp [hi, min_eq_right (u 0).property.1]
  · fin_cases i
    · change u 0 = 1 at hi
      refine ⟨0, 3, by decide, ?_, ?_⟩ <;>
        simp [hi, min_eq_right (u 1).property.2, max_eq_left (u 1).property.2]
    · change u 1 = 1 at hi
      refine ⟨0, 1, by decide, ?_, ?_⟩ <;>
        simp [hi, min_eq_left (u 0).property.2, max_eq_right (u 0).property.2]

theorem tetrahedronQuadrilateralA_diagonal (t : I) :
    tetrahedronQuadrilateralA ![t, t] ∈ tetrahedronOneSkeleton := by
  refine ⟨1, 3, by decide, ?_, ?_⟩ <;> simp

/-- The cyclic permutation of the tetrahedron's four vertices. -/
def tetrahedronQuarterShift : C(Simplex 3, Simplex 3) where
  toFun s := ⟨![s 3, s 0, s 1, s 2], by
    constructor
    · intro i
      fin_cases i <;> exact stdSimplex.zero_le s _
    · have hs := stdSimplex.sum_eq_one s
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero,
        Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one] at hs ⊢
      change s 0 + (s 1 + (s 2 + s 3)) = 1 at hs
      linarith⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    fin_cases i
    · exact (continuous_apply 3).comp continuous_subtype_val
    · exact (continuous_apply 0).comp continuous_subtype_val
    · exact (continuous_apply 1).comp continuous_subtype_val
    · exact (continuous_apply 2).comp continuous_subtype_val

@[simp] theorem tetrahedronQuarterShift_zero (s : Simplex 3) :
    tetrahedronQuarterShift s 0 = s 3 := rfl

@[simp] theorem tetrahedronQuarterShift_one (s : Simplex 3) :
    tetrahedronQuarterShift s 1 = s 0 := rfl

@[simp] theorem tetrahedronQuarterShift_two (s : Simplex 3) :
    tetrahedronQuarterShift s 2 = s 1 := rfl

@[simp] theorem tetrahedronQuarterShift_three (s : Simplex 3) :
    tetrahedronQuarterShift s 3 = s 2 := rfl

def tetrahedronQuarterIndex : Fin 4 ≃ Fin 4 where
  toFun i := ![1, 2, 3, 0] i
  invFun i := ![3, 0, 1, 2] i
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

@[simp] theorem tetrahedronQuarterShift_index (s : Simplex 3) (i : Fin 4) :
    tetrahedronQuarterShift s (tetrahedronQuarterIndex i) = s i := by
  fin_cases i <;> rfl

theorem tetrahedronQuarterShift_oneSkeleton (s : Simplex 3)
    (hs : s ∈ tetrahedronOneSkeleton) :
    tetrahedronQuarterShift s ∈ tetrahedronOneSkeleton := by
  obtain ⟨i, j, hij, hi, hj⟩ := hs
  exact ⟨tetrahedronQuarterIndex i, tetrahedronQuarterIndex j,
    fun h => hij (tetrahedronQuarterIndex.injective h), by simpa, by simpa⟩

variable {X : Type} [TopologicalSpace X] {x : X}

/-- Composing the first geometric filling with the given tetrahedron. -/
def tetrahedronQuadrilateralLoop (τ : BasedTetrahedron x) : GenLoop (Fin 2) X x :=
  ⟨τ.val.comp tetrahedronQuadrilateralA,
    fun u hu => τ.property _ (tetrahedronQuadrilateralA_boundary u hu)⟩

@[simp] theorem tetrahedronQuadrilateralLoop_apply (τ : BasedTetrahedron x)
    (u : Fin 2 → I) :
    tetrahedronQuadrilateralLoop τ u = τ.val (tetrahedronQuadrilateralA u) := rfl

theorem tetrahedronQuadrilateralLoop_diagonal (τ : BasedTetrahedron x) (t : I) :
    tetrahedronQuadrilateralLoop τ ![t, t] = x :=
  τ.property _ (tetrahedronQuadrilateralA_diagonal t)

/-- The second pair of faces, before turning the square back by a quarter-turn. -/
def tetrahedronShiftedQuadrilateralLoop (τ : BasedTetrahedron x) :
    GenLoop (Fin 2) X x :=
  ⟨τ.val.comp (tetrahedronQuarterShift.comp tetrahedronQuadrilateralA),
    fun u hu => τ.property _
      (tetrahedronQuarterShift_oneSkeleton _ (tetrahedronQuadrilateralA_boundary u hu))⟩

@[simp] theorem tetrahedronShiftedQuadrilateralLoop_apply (τ : BasedTetrahedron x)
    (u : Fin 2 → I) :
    tetrahedronShiftedQuadrilateralLoop τ u =
      τ.val (tetrahedronQuarterShift (tetrahedronQuadrilateralA u)) := rfl

theorem tetrahedronShiftedQuadrilateralLoop_diagonal (τ : BasedTetrahedron x) (t : I) :
    tetrahedronShiftedQuadrilateralLoop τ ![t, t] = x :=
  τ.property _
    (tetrahedronQuarterShift_oneSkeleton _ (tetrahedronQuadrilateralA_diagonal t))

end Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected
