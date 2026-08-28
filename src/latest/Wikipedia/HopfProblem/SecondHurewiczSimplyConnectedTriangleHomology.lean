import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedTriangleSquareGeometry

/-!
# The Hurewicz image of an actual based triangle

The square quotient is the identity on its positive triangle and is
boundary-supported on its negative triangle. Thus its native Hurewicz
representative is exactly the singular triangle minus the constant triangle.
The latter correction is essential in the unnormalized singular complex.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected

open FirstHurewicz SingularMayerVietoris

theorem triangleQuotient_lowerProductTriangle :
    triangleQuotient.comp lowerProductTriangle = ContinuousMap.id (Simplex 2) := by
  apply ContinuousMap.ext
  intro s
  apply Subtype.ext
  funext i
  have hs := stdSimplex.sum_eq_one s
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hs
  change s 0 + (s 1 + s 2) = 1 at hs
  have hle : s 2 ≤ s 1 + s 2 := le_add_of_nonneg_left (stdSimplex.zero_le s 1)
  fin_cases i
  · change 1 - ((lowerProductTriangle s).1 : ℝ) = s 0
    rw [lowerProductTriangle_fst]
    linarith
  · change ((lowerProductTriangle s).1 : ℝ) -
      min ((lowerProductTriangle s).1 : ℝ) ((lowerProductTriangle s).2 : ℝ) = s 1
    rw [lowerProductTriangle_fst, lowerProductTriangle_snd, min_eq_right hle]
    ring
  · change min ((lowerProductTriangle s).1 : ℝ)
      ((lowerProductTriangle s).2 : ℝ) = s 2
    rw [lowerProductTriangle_fst, lowerProductTriangle_snd, min_eq_right hle]

theorem triangleQuotient_upperProductTriangle_boundary (s : Simplex 2) :
    triangleQuotient (upperProductTriangle s) ∈ triangleBoundary := by
  refine ⟨1, ?_⟩
  rw [triangleQuotient_one, upperProductTriangle_fst, upperProductTriangle_snd,
    min_eq_left (le_add_of_nonneg_left (stdSimplex.zero_le s 1)), sub_self]

variable {X : Type} [TopologicalSpace X] {x : X}

/-- The positive square triangle is literally the original singular triangle. -/
theorem basedTriangleLoop_lower (τ : BasedTriangle x) :
    (basedTriangleLoop τ).val.comp lowerSquareTriangle = τ.val := by
  change (squareMap (basedTriangleLoop τ)).comp lowerProductTriangle = _
  rw [squareMap_basedTriangleLoop, ContinuousMap.comp_assoc,
    triangleQuotient_lowerProductTriangle, ContinuousMap.comp_id]

/-- The negative square triangle is literally constant after the quotient. -/
theorem basedTriangleLoop_upper (τ : BasedTriangle x) :
    (basedTriangleLoop τ).val.comp upperSquareTriangle =
      ContinuousMap.const (Simplex 2) x := by
  change (squareMap (basedTriangleLoop τ)).comp upperProductTriangle = _
  rw [squareMap_basedTriangleLoop]
  ext s
  exact τ.property _ (triangleQuotient_upperProductTriangle_boundary s)

/-- Exact equality in Mathlib's actual unnormalized singular chains. -/
theorem squareChain_basedTriangleLoop (τ : BasedTriangle x) :
    squareChain (basedTriangleLoop τ) =
      simplexChain X 2 τ.val - simplexChain X 2 (ContinuousMap.const (Simplex 2) x) := by
  rw [squareChain_two_triangles, basedTriangleLoop_lower, basedTriangleLoop_upper]

/-- The corrected triangle is an actual singular two-cycle. -/
def basedTriangleCycle (τ : BasedTriangle x) : ModuleHomology.Cycle (singularComplex X) 2 :=
  ModuleHomology.mkCycle (singularComplex X) 2
    (simplexChain X 2 τ.val - simplexChain X 2 (ContinuousMap.const (Simplex 2) x)) (by
      rw [← squareChain_basedTriangleLoop]
      exact squareChain_boundary (basedTriangleLoop τ))

@[simp] theorem basedTriangleCycle_val (τ : BasedTriangle x) :
    (basedTriangleCycle τ).val =
      simplexChain X 2 τ.val - simplexChain X 2 (ContinuousMap.const (Simplex 2) x) := rfl

/-- The native Hurewicz map sends a based triangle to its corrected
original singular-cycle class. No injectivity or surjectivity is used. -/
theorem hurewicz_basedTriangleClass (τ : BasedTriangle x) :
    hurewiczMap x (basedTriangleClass τ) =
      ModuleHomology.cycleClass (singularComplex X) 2 (basedTriangleCycle τ) := by
  change ModuleHomology.cycleClass (singularComplex X) 2 (squareCycle (basedTriangleLoop τ)) = _
  congr 1
  apply Subtype.ext
  exact squareChain_basedTriangleLoop τ

/-- An actual homotopy of singular triangles relative to their entire
boundary gives an actual native generalized-loop homotopy. -/
def basedTriangleLoopHomotopy {τ υ : BasedTriangle x}
    (H : τ.val.HomotopyRel υ.val triangleBoundary) :
    (basedTriangleLoop τ).val.HomotopyRel (basedTriangleLoop υ).val
      (Cube.boundary (Fin 2)) where
  toFun z := H (z.1, triangleCubeQuotient z.2)
  continuous_toFun := by fun_prop
  map_zero_left t := H.apply_zero _
  map_one_left t := H.apply_one _
  prop' r t ht := H.eq_fst r (triangleCubeQuotient_boundary t ht)

theorem basedTriangleClass_homotopy {τ υ : BasedTriangle x}
    (H : τ.val.HomotopyRel υ.val triangleBoundary) :
    basedTriangleClass τ = basedTriangleClass υ :=
  congrArg Additive.ofMul (Quotient.sound ⟨basedTriangleLoopHomotopy H⟩)

end Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected
