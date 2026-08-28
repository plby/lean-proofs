import Wikipedia.HopfProblem.FifthHurewiczEvaluation

/-!
# The eight paired faces of the remaining fundamental four-cube

The actual recursive interval cross product gives two first-coordinate
faces and the interval products of the six frozen three-cube faces.
Naturality identifies their parameter chains without expanding any
singular-simplex triangulation. Opposite faces retain the same parameter
chain and opposite signs.
-/

noncomputable section

open scoped unitInterval Topology

namespace Wikipedia.HopfProblem.FifthHurewicz

open FirstHurewicz SingularMayerVietoris PeriodTorusHigherHomology

attribute [local instance] integerLinearMapModule integerTensorModule

/-- Fix the first coordinate of the remaining native four-cube. -/
def remainingCubeSideFirst (t : I) : C(Fin 3 → I, Fin 4 → I) :=
  FourthHurewicz.cubeCoordinates.comp (crossInsertLeft t)

/-- Add a free first interval to any map into the remaining three-cube. -/
def remainingCubeSide {A : Type} [TopologicalSpace A] (f : C(A, Fin 3 → I)) :
    C(I × A, Fin 4 → I) :=
  FourthHurewicz.cubeCoordinates.comp ((ContinuousMap.id I).prodMap f)

theorem remainingCubeSideFirst_boundary (t : I) (ht : t = 0 ∨ t = 1)
    (u : Fin 3 → I) : remainingCubeSideFirst t u ∈ Cube.boundary (Fin 4) := by
  refine ⟨0, ?_⟩
  change FourthHurewicz.cubeCoordinates (t, u) 0 = 0 ∨
    FourthHurewicz.cubeCoordinates (t, u) 0 = 1
  simpa only [FourthHurewicz.cubeCoordinates_zero] using ht

theorem remainingCubeSide_boundary {A : Type} [TopologicalSpace A]
    (f : C(A, Fin 3 → I)) (hf : ∀ a, f a ∈ Cube.boundary (Fin 3)) (z : I × A) :
    remainingCubeSide f z ∈ Cube.boundary (Fin 4) := by
  obtain ⟨i, hi⟩ := hf z.2
  refine ⟨i.succ, ?_⟩
  change FourthHurewicz.cubeCoordinates (z.1, f z.2) i.succ = 0 ∨
    FourthHurewicz.cubeCoordinates (z.1, f z.2) i.succ = 1
  simpa only [FourthHurewicz.cubeCoordinates_succ] using hi

/-- Suspending a parametrized face is natural for chains of every degree. -/
theorem remainingCubeSide_chain {A : Type} [TopologicalSpace A]
    (k : ℕ) (f : C(A, Fin 3 → I)) (b : Chains A k) :
    inducedChain FourthHurewicz.cubeCoordinates (k + 1)
        (crossProductEdge I (Fin 3 → I) k SecondHurewicz.intervalChain
          (inducedChain f k b)) =
      inducedChain (remainingCubeSide f) (k + 1)
        (crossProductEdge I A k SecondHurewicz.intervalChain b) := by
  have h := crossProductEdge_natural (ContinuousMap.id I) f k SecondHurewicz.intervalChain b
  rw [inducedChain_id, LinearMap.id_apply] at h
  rw [← h]
  change ((inducedChain FourthHurewicz.cubeCoordinates (k + 1)).comp
    (inducedChain ((ContinuousMap.id I).prodMap f) (k + 1))) _ = _
  rw [← inducedChain_comp]
  rfl

/-- The fixed parameter chain on the ordinary product of three intervals. -/
def productThreeIntervalChain : Chains (I × (I × I)) 3 :=
  crossProductEdge I (I × I) 2 SecondHurewicz.intervalChain SecondHurewicz.productSquareChain

/-- The literal eight oriented faces of the frozen fundamental four-cube,
obtained recursively without enumerating its singular simplices. -/
theorem remainingCubeChain_boundary :
    ((singularComplex (Fin 4 → I)).d 4 3).hom FourthHurewicz.fundamentalCubeChain =
      inducedChain (remainingCubeSideFirst 1) 3 ThirdHurewicz.fundamentalCubeChain -
        inducedChain (remainingCubeSideFirst 0) 3 ThirdHurewicz.fundamentalCubeChain -
        (inducedChain (remainingCubeSide (FourthHurewicz.remainingCubeSideFirst 1)) 3
            ThirdHurewicz.productCubeChain -
          inducedChain (remainingCubeSide (FourthHurewicz.remainingCubeSideFirst 0)) 3
            ThirdHurewicz.productCubeChain -
          (inducedChain (remainingCubeSide
                (FourthHurewicz.remainingCubeSide (ThirdHurewicz.squareSideLeft 1))) 3
              productThreeIntervalChain -
            inducedChain (remainingCubeSide
                (FourthHurewicz.remainingCubeSide (ThirdHurewicz.squareSideLeft 0))) 3
              productThreeIntervalChain -
            (inducedChain (remainingCubeSide
                  (FourthHurewicz.remainingCubeSide (ThirdHurewicz.squareSideRight 1))) 3
                productThreeIntervalChain -
              inducedChain (remainingCubeSide
                  (FourthHurewicz.remainingCubeSide (ThirdHurewicz.squareSideRight 0))) 3
                productThreeIntervalChain))) := by
  have hpoint (t : I) :
      crossProductZeroLeft I (Fin 3 → I) 3 (pointChain t)
          ThirdHurewicz.fundamentalCubeChain =
        inducedChain (crossInsertLeft t) 3 ThirdHurewicz.fundamentalCubeChain := by
    rw [pointChain, crossProductZeroLeft_simplex_left]
    rfl
  have hfirst (t : I) :
      inducedChain FourthHurewicz.cubeCoordinates 3
          (inducedChain (crossInsertLeft t) 3 ThirdHurewicz.fundamentalCubeChain) =
        inducedChain (remainingCubeSideFirst t) 3 ThirdHurewicz.fundamentalCubeChain := by
    rw [remainingCubeSideFirst, inducedChain_comp]
    rfl
  rw [FourthHurewicz.fundamentalCubeChain, ← inducedChain_boundary]
  change inducedChain FourthHurewicz.cubeCoordinates 3
    (((singularComplex (I × (Fin 3 → I))).d 4 3).hom
      (crossProductEdge I (Fin 3 → I) 3 SecondHurewicz.intervalChain
        ThirdHurewicz.fundamentalCubeChain)) = _
  rw [crossProductEdge_boundary 2]
  change inducedChain FourthHurewicz.cubeCoordinates 3
    (crossProductZeroLeft I (Fin 3 → I) 3
        (boundaryOne I SecondHurewicz.intervalChain) ThirdHurewicz.fundamentalCubeChain -
      crossProductEdge I (Fin 3 → I) 2 SecondHurewicz.intervalChain
        (((singularComplex (Fin 3 → I)).d 3 2).hom ThirdHurewicz.fundamentalCubeChain)) = _
  rw [SecondHurewicz.intervalChain_boundary, FourthHurewicz.remainingCubeChain_boundary]
  simp only [map_sub, LinearMap.sub_apply, hpoint, hfirst, remainingCubeSide_chain]
  rfl

end Wikipedia.HopfProblem.FifthHurewicz
