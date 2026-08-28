import Wikipedia.HopfProblem.ThirdHurewiczCubeSubdivisionChainsSupport

/-!
# The common cone correction of the two diagonal square triangles

The two repeated-vertex tetrahedra along the square diagonal need not be
supported on the cube boundary. They occur identically for both square
triangles and cancel when those triangles are subtracted. All remaining
correction terms are evaluated using the actual cube-boundary condition.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.ThirdHurewicz.CubeSubdivision

open FirstHurewicz SingularMayerVietoris Geometry

theorem prismSimplex_endpoints_eq (b c : Fin 2 × Fin 2) (w : Fin 4 → Fin 2 × Fin 3)
    (h : ∀ j, (w j).2 = 0 ∨ (w j).2 = 2) :
    prismSimplex ![(0, 0), b, (1, 1)] w = prismSimplex ![(0, 0), c, (1, 1)] w := by
  apply congrArg cubeAffineSimplex
  funext j
  rcases h j with hj | hj <;> simp [hj]

variable {X : Type} [TopologicalSpace X] {x : X}

/-- The three nondegenerate terms of the indicated square-triangle prism. -/
def diagonalPrismPrincipal (p : GenLoop (Fin 3) X x) (b : Fin 2 × Fin 2) : Chains X 3 :=
  inducedChain p.val 3
      (prismSimplexChain ![(0, 0), b, (1, 1)] ![(0, 0), (1, 0), (1, 1), (1, 2)]) -
    inducedChain p.val 3
      (prismSimplexChain ![(0, 0), b, (1, 1)] ![(0, 0), (0, 1), (1, 1), (1, 2)]) +
    inducedChain p.val 3
      (prismSimplexChain ![(0, 0), b, (1, 1)] ![(0, 0), (0, 1), (0, 2), (1, 2)])

/-- The same literal diagonal correction for either square triangle. -/
def prismCommonCorrection (p : GenLoop (Fin 3) X x) : Chains X 3 :=
  inducedChain p.val 3
      (prismSimplexChain ![(0, 0), (0, 0), (1, 1)] ![(0, 0), (0, 0), (1, 0), (1, 2)]) -
    inducedChain p.val 3
      (prismSimplexChain ![(0, 0), (0, 0), (1, 1)] ![(0, 0), (0, 0), (0, 2), (1, 2)]) -
    simplexChain X 3 (ContinuousMap.const (Simplex 3) x)

/-- Exact decomposition of either oriented diagonal prism, in unnormalized chains. -/
theorem induced_diagonalPrism_eq_principal_add_correction
    (p : GenLoop (Fin 3) X x) (b : Fin 2 × Fin 2) (hb : b.1 = 0 ∨ b.2 = 0) :
    inducedChain p.val 3 (intervalTriangleChain ![(0, 0), b, (1, 1)]) =
      diagonalPrismPrincipal p b + prismCommonCorrection p := by
  have htime (w : Fin 4 → Fin 2 × Fin 3) (hw : ∀ j, (w j).1 = 0) :
      inducedChain p.val 3 (prismSimplexChain ![(0, 0), b, (1, 1)] w) =
        simplexChain X 3 (ContinuousMap.const (Simplex 3) x) := by
    apply induced_prismSimplexChain_of_coordinate p _ w 0
    left
    intro j
    simp [cubeBitVertex, stdVertices, hw j]
  have hside (w : Fin 4 → Fin 2 × Fin 3) (hw : ∀ j, (w j).2 = 0 ∨ (w j).2 = 1) :
      inducedChain p.val 3 (prismSimplexChain ![(0, 0), b, (1, 1)] w) =
        simplexChain X 3 (ContinuousMap.const (Simplex 3) x) := by
    rcases hb with hb | hb
    · apply induced_prismSimplexChain_of_coordinate p _ w 1
      left
      intro j
      rcases hw j with hj | hj <;> simp [cubeBitVertex, stdVertices, hj, hb]
    · apply induced_prismSimplexChain_of_coordinate p _ w 2
      left
      intro j
      rcases hw j with hj | hj <;> simp [cubeBitVertex, stdVertices, hj, hb]
  have hdiag (w : Fin 4 → Fin 2 × Fin 3) (hw : ∀ j, (w j).2 = 0 ∨ (w j).2 = 2) :
      inducedChain p.val 3 (prismSimplexChain ![(0, 0), b, (1, 1)] w) =
        inducedChain p.val 3 (prismSimplexChain ![(0, 0), (0, 0), (1, 1)] w) := by
    simp only [prismSimplexChain, prismSimplex_endpoints_eq b (0, 0) w hw]
  rw [intervalTriangleChain_twelve_tetrahedra]
  simp only [map_add, map_sub]
  rw [htime ![(0, 0), (0, 0), (0, 1), (0, 2)] (by intro j; fin_cases j <;> rfl),
    htime ![(0, 0), (0, 1), (0, 1), (0, 2)] (by intro j; fin_cases j <;> rfl),
    hside ![(0, 0), (0, 1), (0, 1), (1, 1)] (by intro j; fin_cases j <;> simp),
    hdiag ![(0, 0), (0, 0), (1, 0), (1, 2)] (by intro j; fin_cases j <;> simp),
    htime ![(0, 0), (0, 0), (0, 0), (0, 2)] (by intro j; fin_cases j <;> rfl),
    hdiag ![(0, 0), (0, 0), (0, 2), (1, 2)] (by intro j; fin_cases j <;> simp),
    hside ![(0, 0), (0, 0), (1, 0), (1, 1)] (by intro j; fin_cases j <;> simp),
    htime ![(0, 0), (0, 0), (0, 0), (0, 1)] (by intro j; fin_cases j <;> rfl),
    hside ![(0, 0), (0, 0), (0, 1), (1, 1)] (by intro j; fin_cases j <;> simp)]
  unfold diagonalPrismPrincipal prismCommonCorrection
  abel

/-- The shared interior correction cancels before any homology quotient is taken. -/
theorem induced_diagonalPrism_sub (p : GenLoop (Fin 3) X x) :
    inducedChain p.val 3 (intervalTriangleChain ![(0, 0), (1, 0), (1, 1)]) -
      inducedChain p.val 3 (intervalTriangleChain ![(0, 0), (0, 1), (1, 1)]) =
      diagonalPrismPrincipal p (1, 0) - diagonalPrismPrincipal p (0, 1) := by
  rw [induced_diagonalPrism_eq_principal_add_correction p (1, 0) (Or.inr rfl),
    induced_diagonalPrism_eq_principal_add_correction p (0, 1) (Or.inl rfl)]
  abel

end Wikipedia.HopfProblem.ThirdHurewicz.CubeSubdivision
