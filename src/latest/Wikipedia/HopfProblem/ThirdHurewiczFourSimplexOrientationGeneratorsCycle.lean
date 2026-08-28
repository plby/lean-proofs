import Wikipedia.HopfProblem.ThirdHurewiczFourSimplexOrientationCube
import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedTetrahedronBasic

/-!
# The odd four-cycle on an actual based three-simplex

The four-cycle of the barycentric coordinates is compared with a cyclic
permutation and reflection of the native three-cube. On each cube facet
the two simplex maps have a common zero coordinate, so their affine blend
gives an actual homotopy relative to the entire cube boundary.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.ThirdHurewicz

open FirstHurewicz SecondHurewicz.SimplyConnected

/-- The odd cyclic permutation of the four actual simplex coordinates. -/
def threeSimplexCycle : C(Simplex 3, Simplex 3) where
  toFun s := ⟨![s 1, s 2, s 3, s 0], by
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
    · exact (continuous_apply 1).comp continuous_subtype_val
    · exact (continuous_apply 2).comp continuous_subtype_val
    · exact (continuous_apply 3).comp continuous_subtype_val
    · exact (continuous_apply 0).comp continuous_subtype_val

@[simp] theorem threeSimplexCycle_zero (s : Simplex 3) :
    threeSimplexCycle s 0 = s 1 := rfl

@[simp] theorem threeSimplexCycle_one (s : Simplex 3) :
    threeSimplexCycle s 1 = s 2 := rfl

@[simp] theorem threeSimplexCycle_two (s : Simplex 3) :
    threeSimplexCycle s 2 = s 3 := rfl

@[simp] theorem threeSimplexCycle_three (s : Simplex 3) :
    threeSimplexCycle s 3 = s 0 := rfl

theorem threeSimplexCycle_boundary (s : Simplex 3)
    (hs : s ∈ threeSimplexBoundary) : threeSimplexCycle s ∈ threeSimplexBoundary := by
  obtain ⟨i, hi⟩ := hs
  fin_cases i
  · exact ⟨3, hi⟩
  · exact ⟨0, hi⟩
  · exact ⟨1, hi⟩
  · exact ⟨2, hi⟩

variable {X : Type} [TopologicalSpace X] {x : X}

/-- The original based singular simplex precomposed with the four-cycle. -/
def basedThreeSimplexVertexCycle (τ : BasedThreeSimplex x) : BasedThreeSimplex x :=
  ⟨τ.val.comp threeSimplexCycle,
    fun s hs => τ.property _ (threeSimplexCycle_boundary s hs)⟩

@[simp] theorem basedThreeSimplexVertexCycle_apply (τ : BasedThreeSimplex x) (s : Simplex 3) :
    (basedThreeSimplexVertexCycle τ).val s = τ.val (threeSimplexCycle s) := rfl

/-- On each cube facet the two parametrizations share an actual simplex face. -/
theorem threeSimplexCycle_quotient_commonZero (u : Fin 3 → I)
    (hu : u ∈ Cube.boundary (Fin 3)) :
    ∃ i : Fin 4, threeSimplexCycle (threeSimplexQuotient u) i = 0 ∧
      threeSimplexQuotient (cubeThirdCyclicReverse u) i = 0 := by
  rcases hu with ⟨i, hi | hi⟩
  · fin_cases i
    · change u 0 = 0 at hi
      refine ⟨2, ?_, ?_⟩
      · simp [hi, min_eq_left (le_min (u 1).property.1 (u 2).property.1)]
      · simp [hi, min_eq_left (u 2).property.2]
    · change u 1 = 0 at hi
      refine ⟨1, ?_, ?_⟩ <;>
        simp [hi, min_eq_left (u 2).property.1, min_eq_right (u 0).property.1]
    · change u 2 = 0 at hi
      refine ⟨2, ?_, ?_⟩ <;>
        simp [hi, min_eq_right (u 1).property.1, min_eq_right (u 0).property.1,
          min_eq_left (sub_nonneg.mpr (u 0).property.2)]
  · fin_cases i
    · change u 0 = 1 at hi
      refine ⟨3, ?_, ?_⟩ <;>
        simp [hi, min_eq_right (u 2).property.1, min_eq_right (u 1).property.1]
    · change u 1 = 1 at hi
      refine ⟨0, ?_, ?_⟩ <;> simp [hi, min_eq_left (u 0).property.2]
    · change u 2 = 1 at hi
      refine ⟨1, ?_, ?_⟩ <;> simp [hi, min_eq_left (u 1).property.2]

theorem threeSimplexCycle_quotient_blend_boundary (t : I) (u : Fin 3 → I)
    (hu : u ∈ Cube.boundary (Fin 3)) :
    tetrahedronSimplexBlend t (threeSimplexCycle (threeSimplexQuotient u))
      (threeSimplexQuotient (cubeThirdCyclicReverse u)) ∈ threeSimplexBoundary := by
  obtain ⟨i, hi, hj⟩ := threeSimplexCycle_quotient_commonZero u hu
  exact ⟨i, tetrahedronSimplexBlend_zero_coordinate t _ _ i hi hj⟩

/-- The literal relative homotopy retains the original singular simplex map. -/
def basedThreeSimplexVertexCycle_loopHomotopy (τ : BasedThreeSimplex x) :
    (basedThreeSimplexLoop (basedThreeSimplexVertexCycle τ)).val.HomotopyRel
      (cyclicReverseThreeLoop (basedThreeSimplexLoop τ)).val (Cube.boundary (Fin 3)) where
  toFun z := τ.val (tetrahedronSimplexBlend z.1
    (threeSimplexCycle (threeSimplexQuotient z.2))
    (threeSimplexQuotient (cubeThirdCyclicReverse z.2)))
  continuous_toFun := τ.val.continuous.comp
    (tetrahedronSimplexBlendMap (threeSimplexCycle.comp threeSimplexQuotient)
      (threeSimplexQuotient.comp cubeThirdCyclicReverse)).continuous
  map_zero_left u := by
    change τ.val (tetrahedronSimplexBlend 0 _ _) =
      τ.val (threeSimplexCycle (threeSimplexQuotient u))
    rw [tetrahedronSimplexBlend_zero]
  map_one_left u := by
    change τ.val (tetrahedronSimplexBlend 1 _ _) =
      τ.val (threeSimplexQuotient (cubeThirdCyclicReverse u))
    rw [tetrahedronSimplexBlend_one]
  prop' t u hu :=
    (τ.property _ (threeSimplexCycle_quotient_blend_boundary t u hu)).trans
      ((basedThreeSimplexLoop (basedThreeSimplexVertexCycle τ)).property u hu).symm

/-- The four-cycle negates the class in the original native third homotopy group. -/
@[simp] theorem basedThreeSimplexVertexCycle_class (τ : BasedThreeSimplex x) :
    basedThreeSimplexClass (basedThreeSimplexVertexCycle τ) = -basedThreeSimplexClass τ := by
  have h : GenLoop.Homotopic (basedThreeSimplexLoop (basedThreeSimplexVertexCycle τ))
      (cyclicReverseThreeLoop (basedThreeSimplexLoop τ)) :=
    ⟨basedThreeSimplexVertexCycle_loopHomotopy τ⟩
  have he : (⟦basedThreeSimplexLoop (basedThreeSimplexVertexCycle τ)⟧ : π_ 3 X x) =
      ⟦cyclicReverseThreeLoop (basedThreeSimplexLoop τ)⟧ := Quotient.sound h
  exact congrArg Additive.ofMul
    (he.trans (cyclicReverseThreeLoop_class (basedThreeSimplexLoop τ)))

end Wikipedia.HopfProblem.ThirdHurewicz
