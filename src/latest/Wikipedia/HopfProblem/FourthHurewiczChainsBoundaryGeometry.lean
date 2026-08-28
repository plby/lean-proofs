import Wikipedia.HopfProblem.FourthHurewiczEvaluation

/-!
# The six boundary faces of the remaining fundamental three-cube

The boundary formula follows recursively from the actual interval cross
product and the frozen fundamental square. Two first-coordinate faces
have the native square as parameter space; the other four faces have the
ordinary product square as parameter space. Each opposite pair has the
same parameter chain and opposite signs.
-/

noncomputable section

open scoped unitInterval Topology

namespace Wikipedia.HopfProblem.FourthHurewicz

open FirstHurewicz SingularMayerVietoris PeriodTorusHigherHomology

attribute [local instance] integerLinearMapModule integerTensorModule

/-- Fixing the first coordinate in the remaining native three-cube. -/
def remainingCubeSideFirst (t : I) : C(Fin 2 → I, Fin 3 → I) :=
  ThirdHurewicz.cubeCoordinates.comp (crossInsertLeft t)

/-- A remaining three-cube side obtained from a side of its final square. -/
def remainingCubeSide (f : C(I, Fin 2 → I)) : C(I × I, Fin 3 → I) :=
  ThirdHurewicz.cubeCoordinates.comp ((ContinuousMap.id I).prodMap f)

theorem remainingCubeSideFirst_boundary (t : I) (ht : t = 0 ∨ t = 1)
    (u : Fin 2 → I) : remainingCubeSideFirst t u ∈ Cube.boundary (Fin 3) := by
  refine ⟨0, ?_⟩
  change ThirdHurewicz.cubeCoordinates (t, u) 0 = 0 ∨
    ThirdHurewicz.cubeCoordinates (t, u) 0 = 1
  simpa only [ThirdHurewicz.cubeCoordinates_zero] using ht

theorem remainingCubeSide_boundary (f : C(I, Fin 2 → I))
    (hf : ∀ t, f t ∈ Cube.boundary (Fin 2)) (z : I × I) :
    remainingCubeSide f z ∈ Cube.boundary (Fin 3) := by
  obtain ⟨i, hi⟩ := hf z.2
  refine ⟨i.succ, ?_⟩
  change ThirdHurewicz.cubeCoordinates (z.1, f z.2) i.succ = 0 ∨
    ThirdHurewicz.cubeCoordinates (z.1, f z.2) i.succ = 1
  simpa only [ThirdHurewicz.cubeCoordinates_succ] using hi

/-- The last-square side factor is exactly an induced ordinary product-square chain. -/
theorem remainingCubeSide_chain (f : C(I, Fin 2 → I)) :
    inducedChain ThirdHurewicz.cubeCoordinates 2
        (crossProductEdge I (Fin 2 → I) 1 SecondHurewicz.intervalChain
          (inducedChain f 1 SecondHurewicz.intervalChain)) =
      inducedChain (remainingCubeSide f) 2 SecondHurewicz.productSquareChain := by
  have h := crossProductEdge_natural (ContinuousMap.id I) f 1
    SecondHurewicz.intervalChain SecondHurewicz.intervalChain
  rw [inducedChain_id, LinearMap.id_apply] at h
  rw [← h]
  change ((inducedChain ThirdHurewicz.cubeCoordinates 2).comp
    (inducedChain ((ContinuousMap.id I).prodMap f) 2)) SecondHurewicz.productSquareChain = _
  rw [← inducedChain_comp]
  rfl

/-- The literal six oriented faces of the frozen fundamental three-cube,
obtained without expanding its singular simplices. -/
theorem remainingCubeChain_boundary :
    ((singularComplex (Fin 3 → I)).d 3 2).hom ThirdHurewicz.fundamentalCubeChain =
      inducedChain (remainingCubeSideFirst 1) 2 SecondHurewicz.fundamentalSquareChain -
        inducedChain (remainingCubeSideFirst 0) 2 SecondHurewicz.fundamentalSquareChain -
        (inducedChain (remainingCubeSide (ThirdHurewicz.squareSideLeft 1)) 2
            SecondHurewicz.productSquareChain -
          inducedChain (remainingCubeSide (ThirdHurewicz.squareSideLeft 0)) 2
            SecondHurewicz.productSquareChain -
          (inducedChain (remainingCubeSide (ThirdHurewicz.squareSideRight 1)) 2
              SecondHurewicz.productSquareChain -
            inducedChain (remainingCubeSide (ThirdHurewicz.squareSideRight 0)) 2
              SecondHurewicz.productSquareChain)) := by
  have hpoint (t : I) :
      crossProductZeroLeft I (Fin 2 → I) 2 (pointChain t)
          SecondHurewicz.fundamentalSquareChain =
        inducedChain (crossInsertLeft t) 2 SecondHurewicz.fundamentalSquareChain := by
    rw [pointChain, crossProductZeroLeft_simplex_left]
    rfl
  have hfirst (t : I) :
      inducedChain ThirdHurewicz.cubeCoordinates 2
          (inducedChain (crossInsertLeft t) 2 SecondHurewicz.fundamentalSquareChain) =
        inducedChain (remainingCubeSideFirst t) 2
          SecondHurewicz.fundamentalSquareChain := by
    rw [remainingCubeSideFirst, inducedChain_comp]
    rfl
  rw [ThirdHurewicz.fundamentalCubeChain, ← inducedChain_boundary]
  change inducedChain ThirdHurewicz.cubeCoordinates 2
    (((singularComplex (I × (Fin 2 → I))).d 3 2).hom
      (crossProductEdge I (Fin 2 → I) 2 SecondHurewicz.intervalChain
        SecondHurewicz.fundamentalSquareChain)) = _
  rw [crossProductEdge_boundary 1]
  change inducedChain ThirdHurewicz.cubeCoordinates 2
    (crossProductZeroLeft I (Fin 2 → I) 2
        (boundaryOne I SecondHurewicz.intervalChain) SecondHurewicz.fundamentalSquareChain -
      crossProductEdge I (Fin 2 → I) 1 SecondHurewicz.intervalChain
        (boundaryTwo (Fin 2 → I) SecondHurewicz.fundamentalSquareChain)) = _
  rw [SecondHurewicz.intervalChain_boundary, ThirdHurewicz.fundamentalSquareChain_boundary]
  simp only [map_sub, LinearMap.sub_apply, hpoint, hfirst, remainingCubeSide_chain]

end Wikipedia.HopfProblem.FourthHurewicz
