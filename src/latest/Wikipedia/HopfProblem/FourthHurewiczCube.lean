import Wikipedia.HopfProblem.FourthHurewiczPathCubes

/-!
# The genuine four-cube representative of the fourth Hurewicz map

The oriented four-chain is the actual cross product of the first interval
with the frozen fundamental three-cube in the remaining coordinates.
Applying the original native generalized loop gives exactly the evaluated
loop-space chain. Actual five-chains prove its homotopy and concatenation
laws before passing to the native homotopy quotient.
-/

noncomputable section

open scoped unitInterval Topology

namespace Wikipedia.HopfProblem.FourthHurewicz

open FirstHurewicz SingularMayerVietoris PeriodTorusHigherHomology

attribute [local instance] integerLinearMapModule integerTensorModule

/-- The genuine interval-times-three-cube singular four-chain. -/
def productCubeChain : Chains (I × (Fin 3 → I)) 4 :=
  crossProductEdge I (Fin 3 → I) 3 SecondHurewicz.intervalChain
    ThirdHurewicz.fundamentalCubeChain

/-- The fixed fundamental four-chain in Mathlib's literal native four-cube. -/
def fundamentalCubeChain : Chains (Fin 4 → I) 4 :=
  inducedChain cubeCoordinates 4 productCubeChain

variable {X : Type} [TopologicalSpace X] {x : X}

theorem suspensionOne_toLoop (p : GenLoop (Fin 4) X x) :
    suspensionOne x (pathChain (GenLoop.toLoop (0 : Fin 4) p)) =
      inducedChain (cubeMap p) 4 productCubeChain := by
  have h := crossProductEdge_natural (GenLoop.toLoop (0 : Fin 4) p).toContinuousMap
    (ContinuousMap.id (Fin 3 → I)) 3 SecondHurewicz.intervalChain
    ThirdHurewicz.fundamentalCubeChain
  rw [SecondHurewicz.induced_intervalChain, inducedChain_id, LinearMap.id_apply] at h
  rw [suspensionOne_apply, ← h]
  change ((inducedChain (evaluation x) 4).comp
    (inducedChain ((GenLoop.toLoop (0 : Fin 4) p).toContinuousMap.prodMap
      (ContinuousMap.id (Fin 3 → I))) 4)) productCubeChain = _
  rw [← inducedChain_comp, evaluation_comp_toLoop]

/-- The singular four-chain of the original native generalized loop. -/
def cubeChain (p : GenLoop (Fin 4) X x) : Chains X 4 :=
  suspensionOne x (pathChain (GenLoop.toLoop (0 : Fin 4) p))

/-- The representative applies the original cube map to the genuine
recursively constructed fundamental four-chain. -/
theorem cubeChain_eq_induced (p : GenLoop (Fin 4) X x) :
    cubeChain p = inducedChain p.val 4 fundamentalCubeChain := by
  rw [cubeChain, suspensionOne_toLoop]
  change inducedChain (p.val.comp cubeCoordinates) 4 productCubeChain =
    ((inducedChain p.val 4).comp (inducedChain cubeCoordinates 4)) productCubeChain
  rw [inducedChain_comp]

theorem cubeChain_boundary (p : GenLoop (Fin 4) X x) :
    ((singularComplex X).d 4 3).hom (cubeChain p) = 0 :=
  boundaryFour_suspensionOne_of_cycle x _ (boundaryOne_loop (GenLoop.toLoop 0 p))

/-- The actual integral singular four-cycle of the native based cube. -/
def cubeCycle (p : GenLoop (Fin 4) X x) : ModuleHomology.Cycle (singularComplex X) 4 :=
  pathCubeCycle x (GenLoop.toLoop (0 : Fin 4) p)

@[simp] theorem cubeCycle_val (p : GenLoop (Fin 4) X x) :
    (cubeCycle p).1 = cubeChain p := rfl

/-- The four-cube's class in genuine integral singular fourth homology. -/
def cubeHomologyClass (p : GenLoop (Fin 4) X x) : SingularHomology X 4 :=
  ModuleHomology.cycleClass (singularComplex X) 4 (cubeCycle p)

theorem cubeHomologyClass_eq_pathCubeClass (p : GenLoop (Fin 4) X x) :
    cubeHomologyClass p = pathCubeClass x (GenLoop.toLoop (0 : Fin 4) p) := rfl

/-- Actual homotopy relative to the whole native cube boundary preserves the class. -/
theorem cubeHomologyClass_homotopic {p q : GenLoop (Fin 4) X x}
    (h : GenLoop.Homotopic p q) : cubeHomologyClass p = cubeHomologyClass q :=
  pathCubeClass_homotopic x (GenLoop.homotopicTo (0 : Fin 4) h)

theorem toLoop_const :
    GenLoop.toLoop (0 : Fin 4) (GenLoop.const : GenLoop (Fin 4) X x) =
      Path.refl (GenLoop.const : BasedLoopSpace x) := by
  apply Path.ext
  funext t
  apply GenLoop.ext
  intro u
  rfl

@[simp] theorem cubeHomologyClass_const :
    cubeHomologyClass (GenLoop.const : GenLoop (Fin 4) X x) = 0 := by
  rw [cubeHomologyClass_eq_pathCubeClass, toLoop_const, pathCubeClass_refl]

theorem toLoop_transAt (p q : GenLoop (Fin 4) X x) :
    GenLoop.toLoop (0 : Fin 4) (GenLoop.transAt (0 : Fin 4) p q) =
      (GenLoop.toLoop (0 : Fin 4) p).trans (GenLoop.toLoop (0 : Fin 4) q) := by
  have h := congrArg (GenLoop.toLoop (0 : Fin 4))
    (GenLoop.fromLoop_trans_toLoop (i := (0 : Fin 4)) (p := p) (q := q))
  rw [GenLoop.to_from] at h
  exact h.symm

/-- Native concatenation in coordinate zero adds the genuine four-cube classes. -/
theorem cubeHomologyClass_transAt (p q : GenLoop (Fin 4) X x) :
    cubeHomologyClass (GenLoop.transAt (0 : Fin 4) p q) =
      cubeHomologyClass p + cubeHomologyClass q := by
  simp only [cubeHomologyClass_eq_pathCubeClass, toLoop_transAt, pathCubeClass_trans]

end Wikipedia.HopfProblem.FourthHurewicz
