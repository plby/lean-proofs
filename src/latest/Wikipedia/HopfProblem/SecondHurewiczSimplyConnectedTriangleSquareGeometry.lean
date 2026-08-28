import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedTriangleBasic
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCrossProductFormalPrism

/-!
# The literal four triangles of the square chain

The existing cross product is an unnormalized cone construction. Its two
nondegenerate triangles are accompanied by two boundary-supported triangles.
Their contributions cancel after any native generalized loop is applied.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected

open FirstHurewicz SingularMayerVietoris PeriodTorusHigherHomology

attribute [local instance] integerLinearMapModule integerTensorModule

/-- The actual square triangle with the specified ordered zero-one vertices. -/
def squareAffineTriangle (v : Fin 3 → Fin 2 × Fin 2) : C(Simplex 2, I × I) :=
  ((pathSimplex Path.id).prodMap (pathSimplex Path.id)).comp
    (productAffineSimplex (fun i => (stdVertices 1 (v i).1, stdVertices 1 (v i).2)))

theorem squareAffineTriangle_fst_coe (v : Fin 3 → Fin 2 × Fin 2) (s : Simplex 2) :
    ((squareAffineTriangle v s).1 : ℝ) =
      ∑ i, s i * stdVertices 1 (v i).1 1 := by
  change affineSimplex (fun i => stdVertices 1 (v i).1) s 1 = _
  exact affineSimplex_coordinate _ _ _

theorem squareAffineTriangle_snd_coe (v : Fin 3 → Fin 2 × Fin 2) (s : Simplex 2) :
    ((squareAffineTriangle v s).2 : ℝ) =
      ∑ i, s i * stdVertices 1 (v i).2 1 := by
  change affineSimplex (fun i => stdVertices 1 (v i).2) s 1 = _
  exact affineSimplex_coordinate _ _ _

/-- The positively oriented lower triangle, with vertices `00,10,11`. -/
def lowerProductTriangle : C(Simplex 2, I × I) :=
  squareAffineTriangle ![(0, 0), (1, 0), (1, 1)]

/-- The upper triangle with its original negative-chain orientation
`00,01,11`. -/
def upperProductTriangle : C(Simplex 2, I × I) :=
  squareAffineTriangle ![(0, 0), (0, 1), (1, 1)]

def leftProductDegenerate : C(Simplex 2, I × I) :=
  squareAffineTriangle ![(0, 0), (0, 0), (0, 1)]

def bottomProductDegenerate : C(Simplex 2, I × I) :=
  squareAffineTriangle ![(0, 0), (0, 0), (1, 0)]

@[simp] theorem lowerProductTriangle_fst (s : Simplex 2) :
    ((lowerProductTriangle s).1 : ℝ) = s 1 + s 2 := by
  simp [lowerProductTriangle, squareAffineTriangle_fst_coe, stdVertices,
    stdSimplex.vertex, Fin.sum_univ_succ, Pi.single_apply]

@[simp] theorem lowerProductTriangle_snd (s : Simplex 2) :
    ((lowerProductTriangle s).2 : ℝ) = s 2 := by
  simp [lowerProductTriangle, squareAffineTriangle_snd_coe, stdVertices,
    stdSimplex.vertex, Fin.sum_univ_succ, Pi.single_apply]

@[simp] theorem upperProductTriangle_fst (s : Simplex 2) :
    ((upperProductTriangle s).1 : ℝ) = s 2 := by
  simp [upperProductTriangle, squareAffineTriangle_fst_coe, stdVertices,
    stdSimplex.vertex, Fin.sum_univ_succ, Pi.single_apply]

@[simp] theorem upperProductTriangle_snd (s : Simplex 2) :
    ((upperProductTriangle s).2 : ℝ) = s 1 + s 2 := by
  simp [upperProductTriangle, squareAffineTriangle_snd_coe, stdVertices,
    stdSimplex.vertex, Fin.sum_univ_succ, Pi.single_apply]

@[simp] theorem leftProductDegenerate_fst (s : Simplex 2) :
    (leftProductDegenerate s).1 = 0 := by
  apply Subtype.ext
  simp [leftProductDegenerate, squareAffineTriangle_fst_coe, stdVertices,
    stdSimplex.vertex, Fin.sum_univ_succ, Pi.single_apply]

@[simp] theorem bottomProductDegenerate_snd (s : Simplex 2) :
    (bottomProductDegenerate s).2 = 0 := by
  apply Subtype.ext
  simp [bottomProductDegenerate, squareAffineTriangle_snd_coe, stdVertices,
    stdSimplex.vertex, Fin.sum_univ_succ, Pi.single_apply]

/-- The lower triangle takes values in Mathlib's original cube. -/
def lowerSquareTriangle : C(Simplex 2, Fin 2 → I) :=
  squareCoordinates.comp lowerProductTriangle

/-- The upper triangle, still with negative orientation in the square chain. -/
def upperSquareTriangle : C(Simplex 2, Fin 2 → I) :=
  squareCoordinates.comp upperProductTriangle

@[simp] theorem lowerSquareTriangle_zero (s : Simplex 2) :
    (lowerSquareTriangle s 0 : ℝ) = s 1 + s 2 := by
  simp [lowerSquareTriangle]

@[simp] theorem lowerSquareTriangle_one (s : Simplex 2) :
    (lowerSquareTriangle s 1 : ℝ) = s 2 := by
  simp [lowerSquareTriangle]

@[simp] theorem upperSquareTriangle_zero (s : Simplex 2) :
    (upperSquareTriangle s 0 : ℝ) = s 2 := by
  simp [upperSquareTriangle]

@[simp] theorem upperSquareTriangle_one (s : Simplex 2) :
    (upperSquareTriangle s 1 : ℝ) = s 1 + s 2 := by
  simp [upperSquareTriangle]

/-- Literal expansion of the actual cone-defined cross product. -/
theorem productSquareChain_four_triangles :
    productSquareChain = simplexChain (I × I) 2 lowerProductTriangle -
      simplexChain (I × I) 2 leftProductDegenerate -
      simplexChain (I × I) 2 upperProductTriangle +
      simplexChain (I × I) 2 bottomProductDegenerate := by
  rw [productSquareChain, intervalChain, pathChain, crossProductEdge_simplex,
    formalEdgeCrossProduct_simplex_succ, formalPointCrossProduct_edge_boundary,
    formalBoundary_edge_simplex]
  simp only [map_sub, formalEdgeCrossProduct_zero_simplex_right, formalMap_simplex,
    formalCone_simplex, productAffineChainMap_simplex, inducedChain_simplex]
  change (simplexChain (I × I) 2 lowerProductTriangle -
    simplexChain (I × I) 2 leftProductDegenerate) -
    (simplexChain (I × I) 2 upperProductTriangle -
      simplexChain (I × I) 2 bottomProductDegenerate) = _
  abel

variable {X : Type} [TopologicalSpace X] {x : X}

theorem squareMap_leftProductDegenerate (p : GenLoop (Fin 2) X x) :
    (squareMap p).comp leftProductDegenerate = ContinuousMap.const (Simplex 2) x := by
  ext s
  apply GenLoop.boundary p
  refine ⟨0, Or.inl ?_⟩
  rw [squareCoordinates_zero, leftProductDegenerate_fst]

theorem squareMap_bottomProductDegenerate (p : GenLoop (Fin 2) X x) :
    (squareMap p).comp bottomProductDegenerate = ContinuousMap.const (Simplex 2) x := by
  ext s
  apply GenLoop.boundary p
  refine ⟨1, Or.inl ?_⟩
  rw [squareCoordinates_one, bottomProductDegenerate_snd]

/-- For an actual generalized loop, the boundary-supported terms cancel.
This is equality in the original unnormalized singular chain group. -/
theorem squareChain_two_triangles (p : GenLoop (Fin 2) X x) :
    squareChain p = simplexChain X 2 (p.val.comp lowerSquareTriangle) -
      simplexChain X 2 (p.val.comp upperSquareTriangle) := by
  rw [squareChain, suspensionOne_toLoop, productSquareChain_four_triangles]
  simp only [map_add, map_sub, inducedChain_simplex,
    squareMap_leftProductDegenerate, squareMap_bottomProductDegenerate]
  change (simplexChain X 2 (p.val.comp lowerSquareTriangle) -
    simplexChain X 2 (ContinuousMap.const (Simplex 2) x)) -
    simplexChain X 2 (p.val.comp upperSquareTriangle) +
    simplexChain X 2 (ContinuousMap.const (Simplex 2) x) = _
  abel

end Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected
