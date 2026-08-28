import Wikipedia.HopfProblem.ThirdHurewiczCubeSubdivisionChainsPrism

/-!
# Prism chains supported on a side of the native cube

A based native cube sends any simplex supported in one fixed boundary
coordinate to the actual constant simplex. If a square triangle lies on
a side of the square, this applies to every tetrahedron of its interval
prism. The twelve signed coefficients then cancel in the original chain
group, without discarding degenerate simplices.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.ThirdHurewicz.CubeSubdivision

open FirstHurewicz SingularMayerVietoris Geometry

variable {X : Type} [TopologicalSpace X] {x : X}

/-- A literal boundary-coordinate condition on the four prism vertices
forces its composite with the original native loop to be constant. -/
theorem loop_prismSimplex_of_coordinate (p : GenLoop (Fin 3) X x)
    (v : Fin 3 → Fin 2 × Fin 2) (w : Fin 4 → Fin 2 × Fin 3) (i : Fin 3)
    (h : (∀ j, cubeBitVertex ![(w j).1, (v (w j).2).1, (v (w j).2).2] i = 0) ∨
      (∀ j, cubeBitVertex ![(w j).1, (v (w j).2).1, (v (w j).2).2] i = 1)) :
    p.val.comp (prismSimplex v w) = ContinuousMap.const (Simplex 3) x :=
  loop_comp_cubeAffineSimplex_of_coordinate p _ i h

/-- The corresponding original singular chain is the constant simplex chain. -/
theorem induced_prismSimplexChain_of_coordinate (p : GenLoop (Fin 3) X x)
    (v : Fin 3 → Fin 2 × Fin 2) (w : Fin 4 → Fin 2 × Fin 3) (i : Fin 3)
    (h : (∀ j, cubeBitVertex ![(w j).1, (v (w j).2).1, (v (w j).2).2] i = 0) ∨
      (∀ j, cubeBitVertex ![(w j).1, (v (w j).2).1, (v (w j).2).2] i = 1)) :
    inducedChain p.val 3 (prismSimplexChain v w) =
      simplexChain X 3 (ContinuousMap.const (Simplex 3) x) := by
  rw [prismSimplexChain, inducedChain_simplex, loop_prismSimplex_of_coordinate p v w i h]

/-- A square triangle with its first bit fixed on a side gives only
boundary-supported prism simplices. -/
theorem loop_prismSimplex_of_fst (p : GenLoop (Fin 3) X x)
    (v : Fin 3 → Fin 2 × Fin 2) (w : Fin 4 → Fin 2 × Fin 3)
    (h : (∀ j, (v j).1 = 0) ∨ (∀ j, (v j).1 = 1)) :
    p.val.comp (prismSimplex v w) = ContinuousMap.const (Simplex 3) x := by
  apply loop_prismSimplex_of_coordinate p v w 1
  rcases h with h | h
  · exact Or.inl fun j => cubeBitVertex_zero _ (i := 1) (h (w j).2)
  · exact Or.inr fun j => cubeBitVertex_one _ (i := 1) (h (w j).2)

/-- The same conclusion for the second square bit. -/
theorem loop_prismSimplex_of_snd (p : GenLoop (Fin 3) X x)
    (v : Fin 3 → Fin 2 × Fin 2) (w : Fin 4 → Fin 2 × Fin 3)
    (h : (∀ j, (v j).2 = 0) ∨ (∀ j, (v j).2 = 1)) :
    p.val.comp (prismSimplex v w) = ContinuousMap.const (Simplex 3) x := by
  apply loop_prismSimplex_of_coordinate p v w 2
  rcases h with h | h
  · exact Or.inl fun j => cubeBitVertex_zero _ (i := 2) (h (w j).2)
  · exact Or.inr fun j => cubeBitVertex_one _ (i := 2) (h (w j).2)

private theorem induced_intervalTriangleChain_of_constant (p : GenLoop (Fin 3) X x)
    (v : Fin 3 → Fin 2 × Fin 2)
    (h : ∀ w, p.val.comp (prismSimplex v w) = ContinuousMap.const (Simplex 3) x) :
    inducedChain p.val 3 (intervalTriangleChain v) = 0 := by
  rw [intervalTriangleChain_twelve_tetrahedra]
  simp only [map_add, map_sub, prismSimplexChain, inducedChain_simplex, h]
  abel

/-- The complete native interval-triangle chain vanishes after applying
a based cube whenever the first square bit is fixed on a square side. -/
theorem induced_intervalTriangleChain_of_fst (p : GenLoop (Fin 3) X x)
    (v : Fin 3 → Fin 2 × Fin 2)
    (h : (∀ j, (v j).1 = 0) ∨ (∀ j, (v j).1 = 1)) :
    inducedChain p.val 3 (intervalTriangleChain v) = 0 :=
  induced_intervalTriangleChain_of_constant p v fun w => loop_prismSimplex_of_fst p v w h

/-- The complete native interval-triangle chain vanishes for a fixed
second square bit as well. -/
theorem induced_intervalTriangleChain_of_snd (p : GenLoop (Fin 3) X x)
    (v : Fin 3 → Fin 2 × Fin 2)
    (h : (∀ j, (v j).2 = 0) ∨ (∀ j, (v j).2 = 1)) :
    inducedChain p.val 3 (intervalTriangleChain v) = 0 :=
  induced_intervalTriangleChain_of_constant p v fun w => loop_prismSimplex_of_snd p v w h

end Wikipedia.HopfProblem.ThirdHurewicz.CubeSubdivision
