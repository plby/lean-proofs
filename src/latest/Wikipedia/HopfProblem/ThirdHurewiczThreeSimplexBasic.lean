import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedTriangleBasic

/-!
# Boundary-based three-simplices in the native third homotopy group

The nested-minimum PL quotient maps the ordered chamber `u ≥ v ≥ w`
onto the actual standard three-simplex. Every other chamber and the whole
cube boundary map into its boundary. No homotopy or homology group is
replaced by a combinatorial presentation.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.ThirdHurewicz

open FirstHurewicz

/-- The entire geometric boundary of the actual standard three-simplex. -/
def threeSimplexBoundary : Set (Simplex 3) := {s | ∃ i, s i = 0}

/-- Actual singular three-simplices with the whole boundary at the base point.
This is stronger than the based-one-skeleton condition used in degree two. -/
def BasedThreeSimplex {X : Type} [TopologicalSpace X] (x : X) :=
  {τ : C(Simplex 3, X) // ∀ s ∈ threeSimplexBoundary, τ s = x}

/-- The explicit three-dimensional PL simplex quotient on the native cube. -/
def threeSimplexQuotient : C(Fin 3 → I, Simplex 3) where
  toFun u := ⟨![1 - (u 0 : ℝ),
    (u 0 : ℝ) - min (u 0 : ℝ) (u 1 : ℝ),
    min (u 0 : ℝ) (u 1 : ℝ) - min (u 0 : ℝ) (min (u 1 : ℝ) (u 2 : ℝ)),
    min (u 0 : ℝ) (min (u 1 : ℝ) (u 2 : ℝ))], by
      constructor
      · intro i
        fin_cases i
        · exact sub_nonneg.mpr (u 0).property.2
        · exact sub_nonneg.mpr (min_le_left _ _)
        · exact sub_nonneg.mpr (min_le_min_left _ (min_le_left _ _))
        · exact le_min (u 0).property.1 (le_min (u 1).property.1 (u 2).property.1)
      · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero,
          Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one]
        ring⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    fin_cases i <;> dsimp <;> fun_prop

@[simp] theorem threeSimplexQuotient_zero (u : Fin 3 → I) :
    threeSimplexQuotient u 0 = 1 - (u 0 : ℝ) := rfl

@[simp] theorem threeSimplexQuotient_one (u : Fin 3 → I) :
    threeSimplexQuotient u 1 = (u 0 : ℝ) - min (u 0 : ℝ) (u 1 : ℝ) := rfl

@[simp] theorem threeSimplexQuotient_two (u : Fin 3 → I) :
    threeSimplexQuotient u 2 = min (u 0 : ℝ) (u 1 : ℝ) -
      min (u 0 : ℝ) (min (u 1 : ℝ) (u 2 : ℝ)) := rfl

@[simp] theorem threeSimplexQuotient_three (u : Fin 3 → I) :
    threeSimplexQuotient u 3 = min (u 0 : ℝ) (min (u 1 : ℝ) (u 2 : ℝ)) := rfl

/-- The entire native cube boundary maps into the actual simplex boundary. -/
theorem threeSimplexQuotient_boundary (u : Fin 3 → I)
    (hu : u ∈ Cube.boundary (Fin 3)) : threeSimplexQuotient u ∈ threeSimplexBoundary := by
  rcases hu with ⟨i, hi | hi⟩
  · fin_cases i
    · change u 0 = 0 at hi
      refine ⟨3, ?_⟩
      rw [threeSimplexQuotient_three, hi]
      exact min_eq_left (le_min (u 1).property.1 (u 2).property.1)
    · change u 1 = 0 at hi
      refine ⟨3, ?_⟩
      rw [threeSimplexQuotient_three, hi]
      change min (u 0 : ℝ) (min (0 : ℝ) (u 2 : ℝ)) = 0
      rw [min_eq_left (u 2).property.1]
      exact min_eq_right (u 0).property.1
    · change u 2 = 0 at hi
      refine ⟨3, ?_⟩
      rw [threeSimplexQuotient_three, hi]
      change min (u 0 : ℝ) (min (u 1 : ℝ) (0 : ℝ)) = 0
      rw [min_eq_right (u 1).property.1]
      exact min_eq_right (u 0).property.1
  · fin_cases i
    · change u 0 = 1 at hi
      refine ⟨0, ?_⟩
      rw [threeSimplexQuotient_zero, hi]
      norm_num
    · change u 1 = 1 at hi
      refine ⟨1, ?_⟩
      rw [threeSimplexQuotient_one, hi]
      change (u 0 : ℝ) - min (u 0 : ℝ) (1 : ℝ) = 0
      rw [min_eq_left (u 0).property.2, sub_self]
    · change u 2 = 1 at hi
      refine ⟨2, ?_⟩
      rw [threeSimplexQuotient_two, hi]
      change min (u 0 : ℝ) (u 1 : ℝ) - min (u 0 : ℝ) (min (u 1 : ℝ) (1 : ℝ)) = 0
      rw [min_eq_left (u 1).property.2, sub_self]

theorem threeSimplexQuotient_boundary_of_first_le (u : Fin 3 → I)
    (h : (u 0 : ℝ) ≤ u 1) : threeSimplexQuotient u ∈ threeSimplexBoundary :=
  ⟨1, by rw [threeSimplexQuotient_one, min_eq_left h, sub_self]⟩

theorem threeSimplexQuotient_boundary_of_second_le (u : Fin 3 → I)
    (h : (u 1 : ℝ) ≤ u 2) : threeSimplexQuotient u ∈ threeSimplexBoundary :=
  ⟨2, by rw [threeSimplexQuotient_two, min_eq_left h, sub_self]⟩

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] {x : X}

/-- A whole-boundary-based three-simplex gives an actual native generalized loop. -/
def basedThreeSimplexLoop (τ : BasedThreeSimplex x) : GenLoop (Fin 3) X x :=
  ⟨τ.val.comp threeSimplexQuotient,
    fun u hu => τ.property _ (threeSimplexQuotient_boundary u hu)⟩

@[simp] theorem basedThreeSimplexLoop_apply (τ : BasedThreeSimplex x) (u : Fin 3 → I) :
    basedThreeSimplexLoop τ u = τ.val (threeSimplexQuotient u) := rfl

/-- Its class in Mathlib's original third homotopy group, in additive notation. -/
def basedThreeSimplexClass (τ : BasedThreeSimplex x) : Additive (π_ 3 X x) :=
  Additive.ofMul (⟦basedThreeSimplexLoop τ⟧ : π_ 3 X x)

/-- Every actual face is the constant singular two-simplex. -/
theorem basedThreeSimplex_face (τ : BasedThreeSimplex x) (i : Fin 4) :
    τ.val.comp (simplexFace 2 i) = ContinuousMap.const (Simplex 2) x := by
  apply ContinuousMap.ext
  intro s
  exact τ.property _ ⟨i, simplexFace_apply_self 2 i s⟩

def constantBasedThreeSimplex (x : X) : BasedThreeSimplex x :=
  ⟨ContinuousMap.const (Simplex 3) x, fun _ _ => rfl⟩

@[simp] theorem basedThreeSimplexLoop_constant (x : X) :
    basedThreeSimplexLoop (constantBasedThreeSimplex x) = GenLoop.const := rfl

@[simp] theorem basedThreeSimplexClass_constant (x : X) :
    basedThreeSimplexClass (constantBasedThreeSimplex x) = 0 := rfl

def mapBasedThreeSimplex (f : C(X, Y)) (τ : BasedThreeSimplex x) :
    BasedThreeSimplex (f x) :=
  ⟨f.comp τ.val, fun s hs => congrArg f (τ.property s hs)⟩

@[simp] theorem basedThreeSimplexLoop_map (f : C(X, Y)) (τ : BasedThreeSimplex x) :
    basedThreeSimplexLoop (mapBasedThreeSimplex f τ) =
      SecondHurewicz.mapGenLoop f x (basedThreeSimplexLoop τ) := rfl

/-- An actual relative simplex homotopy induces an actual relative cube homotopy. -/
def basedThreeSimplexLoopHomotopy {τ υ : BasedThreeSimplex x}
    (H : τ.val.HomotopyRel υ.val threeSimplexBoundary) :
    (basedThreeSimplexLoop τ).val.HomotopyRel (basedThreeSimplexLoop υ).val
      (Cube.boundary (Fin 3)) where
  toFun z := H (z.1, threeSimplexQuotient z.2)
  continuous_toFun := by fun_prop
  map_zero_left u := H.apply_zero _
  map_one_left u := H.apply_one _
  prop' r u hu := H.eq_fst r (threeSimplexQuotient_boundary u hu)

theorem basedThreeSimplexClass_homotopy {τ υ : BasedThreeSimplex x}
    (H : τ.val.HomotopyRel υ.val threeSimplexBoundary) :
    basedThreeSimplexClass τ = basedThreeSimplexClass υ :=
  congrArg Additive.ofMul (Quotient.sound ⟨basedThreeSimplexLoopHomotopy H⟩)

end Wikipedia.HopfProblem.ThirdHurewicz
