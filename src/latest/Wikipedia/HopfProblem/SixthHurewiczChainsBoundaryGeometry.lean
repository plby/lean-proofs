import Wikipedia.HopfProblem.SixthHurewiczEvaluation

/-!
# The ten paired faces of the remaining fundamental five-cube

The recursive interval cross product gives two first-coordinate faces
and the interval products of the eight frozen four-cube faces.
Naturality identifies their parameter chains without expanding the
singular-simplex triangulation. Each opposite pair has the same
parameter chain and opposite signs.
-/

noncomputable section

open scoped unitInterval Topology

namespace Wikipedia.HopfProblem.SixthHurewicz

open FirstHurewicz SingularMayerVietoris PeriodTorusHigherHomology

attribute [local instance] integerLinearMapModule integerTensorModule

/-- Fix the first coordinate of the remaining native five-cube. -/
def remainingCubeSideFirst (t : I) : C(Fin 4 → I, Fin 5 → I) :=
  FifthHurewicz.cubeCoordinates.comp (crossInsertLeft t)

/-- Add a free first interval to any map into the remaining four-cube. -/
def remainingCubeSide {A : Type} [TopologicalSpace A] (f : C(A, Fin 4 → I)) :
    C(I × A, Fin 5 → I) :=
  FifthHurewicz.cubeCoordinates.comp ((ContinuousMap.id I).prodMap f)

theorem remainingCubeSideFirst_boundary (t : I) (ht : t = 0 ∨ t = 1)
    (u : Fin 4 → I) : remainingCubeSideFirst t u ∈ Cube.boundary (Fin 5) := by
  refine ⟨0, ?_⟩
  change FifthHurewicz.cubeCoordinates (t, u) 0 = 0 ∨
    FifthHurewicz.cubeCoordinates (t, u) 0 = 1
  simpa only [FifthHurewicz.cubeCoordinates_zero] using ht

theorem remainingCubeSide_boundary {A : Type} [TopologicalSpace A]
    (f : C(A, Fin 4 → I)) (hf : ∀ a, f a ∈ Cube.boundary (Fin 4)) (z : I × A) :
    remainingCubeSide f z ∈ Cube.boundary (Fin 5) := by
  obtain ⟨i, hi⟩ := hf z.2
  refine ⟨i.succ, ?_⟩
  change FifthHurewicz.cubeCoordinates (z.1, f z.2) i.succ = 0 ∨
    FifthHurewicz.cubeCoordinates (z.1, f z.2) i.succ = 1
  simpa only [FifthHurewicz.cubeCoordinates_succ] using hi

/-- Suspending a parametrized face is natural for chains of every degree. -/
theorem remainingCubeSide_chain {A : Type} [TopologicalSpace A]
    (k : ℕ) (f : C(A, Fin 4 → I)) (b : Chains A k) :
    inducedChain FifthHurewicz.cubeCoordinates (k + 1)
        (crossProductEdge I (Fin 4 → I) k SecondHurewicz.intervalChain
          (inducedChain f k b)) =
      inducedChain (remainingCubeSide f) (k + 1)
        (crossProductEdge I A k SecondHurewicz.intervalChain b) := by
  have h := crossProductEdge_natural (ContinuousMap.id I) f k SecondHurewicz.intervalChain b
  rw [inducedChain_id, LinearMap.id_apply] at h
  rw [← h]
  change ((inducedChain FifthHurewicz.cubeCoordinates (k + 1)).comp
    (inducedChain ((ContinuousMap.id I).prodMap f) (k + 1))) _ = _
  rw [← inducedChain_comp]
  rfl

/-- The fixed four-chain on two intervals times the native square. -/
def productTwoIntervalSquareChain : Chains (I × (I × (Fin 2 → I))) 4 :=
  crossProductEdge I (I × (Fin 2 → I)) 3 SecondHurewicz.intervalChain
    ThirdHurewicz.productCubeChain

/-- The fixed parameter chain on the ordinary product of four intervals. -/
def productFourIntervalChain : Chains (I × (I × (I × I))) 4 :=
  crossProductEdge I (I × (I × I)) 3 SecondHurewicz.intervalChain
    FifthHurewicz.productThreeIntervalChain

/-- The literal ten oriented faces of the frozen fundamental five-cube,
obtained recursively without enumerating its singular simplices. -/
theorem remainingCubeChain_boundary :
    ((singularComplex (Fin 5 → I)).d 5 4).hom FifthHurewicz.fundamentalCubeChain =
      inducedChain (remainingCubeSideFirst 1) 4 FourthHurewicz.fundamentalCubeChain -
        inducedChain (remainingCubeSideFirst 0) 4 FourthHurewicz.fundamentalCubeChain -
        (inducedChain (remainingCubeSide (FifthHurewicz.remainingCubeSideFirst 1)) 4
            FourthHurewicz.productCubeChain -
          inducedChain (remainingCubeSide (FifthHurewicz.remainingCubeSideFirst 0)) 4
            FourthHurewicz.productCubeChain -
          (inducedChain (remainingCubeSide
                (FifthHurewicz.remainingCubeSide (FourthHurewicz.remainingCubeSideFirst 1))) 4
              productTwoIntervalSquareChain -
            inducedChain (remainingCubeSide
                (FifthHurewicz.remainingCubeSide (FourthHurewicz.remainingCubeSideFirst 0))) 4
              productTwoIntervalSquareChain -
            (inducedChain (remainingCubeSide
                  (FifthHurewicz.remainingCubeSide
                    (FourthHurewicz.remainingCubeSide (ThirdHurewicz.squareSideLeft 1)))) 4
                productFourIntervalChain -
              inducedChain (remainingCubeSide
                  (FifthHurewicz.remainingCubeSide
                    (FourthHurewicz.remainingCubeSide (ThirdHurewicz.squareSideLeft 0)))) 4
                productFourIntervalChain -
              (inducedChain (remainingCubeSide
                    (FifthHurewicz.remainingCubeSide
                      (FourthHurewicz.remainingCubeSide (ThirdHurewicz.squareSideRight 1)))) 4
                  productFourIntervalChain -
                inducedChain (remainingCubeSide
                    (FifthHurewicz.remainingCubeSide
                      (FourthHurewicz.remainingCubeSide (ThirdHurewicz.squareSideRight 0)))) 4
                  productFourIntervalChain)))) := by
  have hpoint (t : I) :
      crossProductZeroLeft I (Fin 4 → I) 4 (pointChain t)
          FourthHurewicz.fundamentalCubeChain =
        inducedChain (crossInsertLeft t) 4 FourthHurewicz.fundamentalCubeChain := by
    rw [pointChain, crossProductZeroLeft_simplex_left]
    rfl
  have hfirst (t : I) :
      inducedChain FifthHurewicz.cubeCoordinates 4
          (inducedChain (crossInsertLeft t) 4 FourthHurewicz.fundamentalCubeChain) =
        inducedChain (remainingCubeSideFirst t) 4 FourthHurewicz.fundamentalCubeChain := by
    rw [remainingCubeSideFirst, inducedChain_comp]
    rfl
  rw [FifthHurewicz.fundamentalCubeChain, ← inducedChain_boundary]
  change inducedChain FifthHurewicz.cubeCoordinates 4
    (((singularComplex (I × (Fin 4 → I))).d 5 4).hom
      (crossProductEdge I (Fin 4 → I) 4 SecondHurewicz.intervalChain
        FourthHurewicz.fundamentalCubeChain)) = _
  rw [crossProductEdge_boundary 3]
  change inducedChain FifthHurewicz.cubeCoordinates 4
    (crossProductZeroLeft I (Fin 4 → I) 4
        (boundaryOne I SecondHurewicz.intervalChain) FourthHurewicz.fundamentalCubeChain -
      crossProductEdge I (Fin 4 → I) 3 SecondHurewicz.intervalChain
        (((singularComplex (Fin 4 → I)).d 4 3).hom FourthHurewicz.fundamentalCubeChain)) = _
  rw [SecondHurewicz.intervalChain_boundary, FifthHurewicz.remainingCubeChain_boundary]
  simp only [map_sub, LinearMap.sub_apply, hpoint, hfirst, remainingCubeSide_chain]
  rfl

end Wikipedia.HopfProblem.SixthHurewicz
