import Wikipedia.HomotopyGroupsOfSpheres.SeventhHurewicz.Evaluation

/-! # The twelve paired faces of the recursive fundamental six-cube -/

noncomputable section

open scoped unitInterval Topology

namespace Wikipedia.HomotopyGroupsOfSpheres.SeventhHurewicz

open Wikipedia.HopfProblem
open FirstHurewicz SingularMayerVietoris PeriodTorusHigherHomology

attribute [local instance] integerLinearMapModule integerTensorModule

def remainingCubeSideFirst (t : I) : C(Fin 5 → I, Fin 6 → I) :=
  SixthHurewicz.cubeCoordinates.comp (crossInsertLeft t)

def remainingCubeSide {A : Type} [TopologicalSpace A] (f : C(A, Fin 5 → I)) :
    C(I × A, Fin 6 → I) :=
  SixthHurewicz.cubeCoordinates.comp ((ContinuousMap.id I).prodMap f)

theorem remainingCubeSideFirst_boundary (t : I) (ht : t = 0 ∨ t = 1)
    (u : Fin 5 → I) : remainingCubeSideFirst t u ∈ Cube.boundary (Fin 6) := by
  refine ⟨0, ?_⟩
  change SixthHurewicz.cubeCoordinates (t, u) 0 = 0 ∨
    SixthHurewicz.cubeCoordinates (t, u) 0 = 1
  simpa only [SixthHurewicz.cubeCoordinates_zero] using ht

theorem remainingCubeSide_boundary {A : Type} [TopologicalSpace A]
    (f : C(A, Fin 5 → I)) (hf : ∀ a, f a ∈ Cube.boundary (Fin 5)) (z : I × A) :
    remainingCubeSide f z ∈ Cube.boundary (Fin 6) := by
  obtain ⟨i, hi⟩ := hf z.2
  refine ⟨i.succ, ?_⟩
  change SixthHurewicz.cubeCoordinates (z.1, f z.2) i.succ = 0 ∨
    SixthHurewicz.cubeCoordinates (z.1, f z.2) i.succ = 1
  simpa only [SixthHurewicz.cubeCoordinates_succ] using hi

theorem remainingCubeSide_chain {A : Type} [TopologicalSpace A]
    (k : ℕ) (f : C(A, Fin 5 → I)) (b : Chains A k) :
    inducedChain SixthHurewicz.cubeCoordinates (k + 1)
        (crossProductEdge I (Fin 5 → I) k SecondHurewicz.intervalChain
          (inducedChain f k b)) =
      inducedChain (remainingCubeSide f) (k + 1)
        (crossProductEdge I A k SecondHurewicz.intervalChain b) := by
  have h := crossProductEdge_natural (ContinuousMap.id I) f k SecondHurewicz.intervalChain b
  rw [inducedChain_id, LinearMap.id_apply] at h
  rw [← h]
  change ((inducedChain SixthHurewicz.cubeCoordinates (k + 1)).comp
    (inducedChain ((ContinuousMap.id I).prodMap f) (k + 1))) _ = _
  rw [← inducedChain_comp]
  rfl

def productTwoIntervalCubeChain : Chains (I × (I × (Fin 3 → I))) 5 :=
  crossProductEdge I (I × (Fin 3 → I)) 4 SecondHurewicz.intervalChain
    FourthHurewicz.productCubeChain

def productThreeIntervalSquareChain : Chains (I × (I × (I × (Fin 2 → I)))) 5 :=
  crossProductEdge I (I × (I × (Fin 2 → I))) 4 SecondHurewicz.intervalChain
    SixthHurewicz.productTwoIntervalSquareChain

def productFiveIntervalChain : Chains (I × (I × (I × (I × I)))) 5 :=
  crossProductEdge I (I × (I × (I × I))) 4 SecondHurewicz.intervalChain
    SixthHurewicz.productFourIntervalChain

def boundaryFace0 (t : I) : C(Fin 5 → I, Fin 6 → I) :=
  remainingCubeSideFirst t

theorem boundaryFace0_boundary (t : I) (ht : t = 0 ∨ t = 1)
    (u : Fin 5 → I) : boundaryFace0 t u ∈ Cube.boundary (Fin 6) :=
  remainingCubeSideFirst_boundary t ht u

def boundaryFace1 (t : I) : C(I × (Fin 4 → I), Fin 6 → I) :=
  remainingCubeSide (SixthHurewicz.remainingCubeSideFirst t)

theorem boundaryFace1_boundary (t : I) (ht : t = 0 ∨ t = 1)
    (u : I × (Fin 4 → I)) : boundaryFace1 t u ∈ Cube.boundary (Fin 6) :=
  remainingCubeSide_boundary _ (SixthHurewicz.remainingCubeSideFirst_boundary t ht) u

def boundaryFace2 (t : I) : C(I × (I × (Fin 3 → I)), Fin 6 → I) :=
  remainingCubeSide (SixthHurewicz.remainingCubeSide (FifthHurewicz.remainingCubeSideFirst t))

theorem boundaryFace2_boundary (t : I) (ht : t = 0 ∨ t = 1)
    (u : I × (I × (Fin 3 → I))) : boundaryFace2 t u ∈ Cube.boundary (Fin 6) :=
  remainingCubeSide_boundary _ (SixthHurewicz.remainingCubeSide_boundary _
    (FifthHurewicz.remainingCubeSideFirst_boundary t ht)) u

def boundaryFace3 (t : I) : C(I × (I × (I × (Fin 2 → I))), Fin 6 → I) :=
  remainingCubeSide (SixthHurewicz.remainingCubeSide
    (FifthHurewicz.remainingCubeSide (FourthHurewicz.remainingCubeSideFirst t)))

theorem boundaryFace3_boundary (t : I) (ht : t = 0 ∨ t = 1)
    (u : I × (I × (I × (Fin 2 → I)))) : boundaryFace3 t u ∈ Cube.boundary (Fin 6) :=
  remainingCubeSide_boundary _ (SixthHurewicz.remainingCubeSide_boundary _
    (FifthHurewicz.remainingCubeSide_boundary _
      (FourthHurewicz.remainingCubeSideFirst_boundary t ht))) u

def boundaryFace4 (t : I) : C(I × (I × (I × (I × I))), Fin 6 → I) :=
  remainingCubeSide (SixthHurewicz.remainingCubeSide (FifthHurewicz.remainingCubeSide
    (FourthHurewicz.remainingCubeSide (ThirdHurewicz.squareSideLeft t))))

theorem boundaryFace4_boundary (t : I) (ht : t = 0 ∨ t = 1)
    (u : I × (I × (I × (I × I)))) : boundaryFace4 t u ∈ Cube.boundary (Fin 6) :=
  remainingCubeSide_boundary _ (SixthHurewicz.remainingCubeSide_boundary _
    (FifthHurewicz.remainingCubeSide_boundary _ (FourthHurewicz.remainingCubeSide_boundary _
      (ThirdHurewicz.squareSideLeft_boundary t ht)))) u

def boundaryFace5 (t : I) : C(I × (I × (I × (I × I))), Fin 6 → I) :=
  remainingCubeSide (SixthHurewicz.remainingCubeSide (FifthHurewicz.remainingCubeSide
    (FourthHurewicz.remainingCubeSide (ThirdHurewicz.squareSideRight t))))

theorem boundaryFace5_boundary (t : I) (ht : t = 0 ∨ t = 1)
    (u : I × (I × (I × (I × I)))) : boundaryFace5 t u ∈ Cube.boundary (Fin 6) :=
  remainingCubeSide_boundary _ (SixthHurewicz.remainingCubeSide_boundary _
    (FifthHurewicz.remainingCubeSide_boundary _ (FourthHurewicz.remainingCubeSide_boundary _
      (ThirdHurewicz.squareSideRight_boundary t ht)))) u

/-- The actual chain boundary, retaining six opposite pairs of parametrized faces. -/
theorem remainingCubeChain_boundary :
    ((singularComplex (Fin 6 → I)).d 6 5).hom SixthHurewicz.fundamentalCubeChain =
      (inducedChain (boundaryFace0 1) 5 FifthHurewicz.fundamentalCubeChain -
        inducedChain (boundaryFace0 0) 5 FifthHurewicz.fundamentalCubeChain) -
      ((inducedChain (boundaryFace1 1) 5 FifthHurewicz.productCubeChain -
        inducedChain (boundaryFace1 0) 5 FifthHurewicz.productCubeChain) -
      ((inducedChain (boundaryFace2 1) 5 productTwoIntervalCubeChain -
        inducedChain (boundaryFace2 0) 5 productTwoIntervalCubeChain) -
      ((inducedChain (boundaryFace3 1) 5 productThreeIntervalSquareChain -
        inducedChain (boundaryFace3 0) 5 productThreeIntervalSquareChain) -
      ((inducedChain (boundaryFace4 1) 5 productFiveIntervalChain -
        inducedChain (boundaryFace4 0) 5 productFiveIntervalChain) -
      ((inducedChain (boundaryFace5 1) 5 productFiveIntervalChain -
        inducedChain (boundaryFace5 0) 5 productFiveIntervalChain)))))) := by
  have hpoint (t : I) :
      crossProductZeroLeft I (Fin 5 → I) 5 (pointChain t)
          FifthHurewicz.fundamentalCubeChain =
        inducedChain (crossInsertLeft t) 5 FifthHurewicz.fundamentalCubeChain := by
    rw [pointChain, crossProductZeroLeft_simplex_left]
    rfl
  have hfirst (t : I) :
      inducedChain SixthHurewicz.cubeCoordinates 5
          (inducedChain (crossInsertLeft t) 5 FifthHurewicz.fundamentalCubeChain) =
        inducedChain (remainingCubeSideFirst t) 5 FifthHurewicz.fundamentalCubeChain := by
    rw [remainingCubeSideFirst, inducedChain_comp]
    rfl
  rw [SixthHurewicz.fundamentalCubeChain, ← inducedChain_boundary]
  change inducedChain SixthHurewicz.cubeCoordinates 5
    (((singularComplex (I × (Fin 5 → I))).d 6 5).hom
      (crossProductEdge I (Fin 5 → I) 5 SecondHurewicz.intervalChain
        FifthHurewicz.fundamentalCubeChain)) = _
  rw [crossProductEdge_boundary 4]
  change inducedChain SixthHurewicz.cubeCoordinates 5
    (crossProductZeroLeft I (Fin 5 → I) 5
        (boundaryOne I SecondHurewicz.intervalChain) FifthHurewicz.fundamentalCubeChain -
      crossProductEdge I (Fin 5 → I) 4 SecondHurewicz.intervalChain
        (((singularComplex (Fin 5 → I)).d 5 4).hom FifthHurewicz.fundamentalCubeChain)) = _
  rw [SecondHurewicz.intervalChain_boundary, SixthHurewicz.remainingCubeChain_boundary]
  simp only [map_sub, LinearMap.sub_apply, hpoint, hfirst, remainingCubeSide_chain]
  rfl

end Wikipedia.HomotopyGroupsOfSpheres.SeventhHurewicz
