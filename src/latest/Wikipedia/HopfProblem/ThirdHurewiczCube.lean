import Wikipedia.HopfProblem.ThirdHurewiczPathCubes

/-!
# The actual cubical representative of the third Hurewicz class

The fixed oriented three-chain is the genuine cross product of the first
interval with the frozen fundamental square in the remaining two
coordinates. Applying the original native generalized loop gives exactly
the evaluated loop-space chain. Its homotopy and concatenation laws use
explicit four-dimensional singular-chain primitives.
-/

noncomputable section

open scoped unitInterval Topology

namespace Wikipedia.HopfProblem.ThirdHurewicz

open FirstHurewicz SingularMayerVietoris PeriodTorusHigherHomology

attribute [local instance] integerLinearMapModule integerTensorModule

/-- The genuine oriented interval-times-square singular three-chain. -/
def productCubeChain : Chains (I × (Fin 2 → I)) 3 :=
  crossProductEdge I (Fin 2 → I) 2 SecondHurewicz.intervalChain
    SecondHurewicz.fundamentalSquareChain

/-- The fixed fundamental three-chain in Mathlib's literal native cube. -/
def fundamentalCubeChain : Chains (Fin 3 → I) 3 :=
  inducedChain cubeCoordinates 3 productCubeChain

variable {X : Type} [TopologicalSpace X] {x : X}

theorem suspensionOne_toLoop (p : GenLoop (Fin 3) X x) :
    suspensionOne x (pathChain (GenLoop.toLoop (0 : Fin 3) p)) =
      inducedChain (cubeMap p) 3 productCubeChain := by
  have h := crossProductEdge_natural (GenLoop.toLoop (0 : Fin 3) p).toContinuousMap
    (ContinuousMap.id (Fin 2 → I)) 2 SecondHurewicz.intervalChain
    SecondHurewicz.fundamentalSquareChain
  rw [SecondHurewicz.induced_intervalChain, inducedChain_id, LinearMap.id_apply] at h
  rw [suspensionOne_apply, ← h]
  change ((inducedChain (evaluation x) 3).comp
    (inducedChain ((GenLoop.toLoop (0 : Fin 3) p).toContinuousMap.prodMap
      (ContinuousMap.id (Fin 2 → I))) 3)) productCubeChain = _
  rw [← inducedChain_comp, evaluation_comp_toLoop]

/-- The singular three-chain associated with the original native generalized loop. -/
def cubeChain (p : GenLoop (Fin 3) X x) : Chains X 3 :=
  suspensionOne x (pathChain (GenLoop.toLoop (0 : Fin 3) p))

/-- The representative is the original map applied to the genuine oriented
fundamental chain of its actual three-dimensional cube. -/
theorem cubeChain_eq_induced (p : GenLoop (Fin 3) X x) :
    cubeChain p = inducedChain p.val 3 fundamentalCubeChain := by
  rw [cubeChain, suspensionOne_toLoop]
  change inducedChain (p.val.comp cubeCoordinates) 3 productCubeChain =
    ((inducedChain p.val 3).comp (inducedChain cubeCoordinates 3)) productCubeChain
  rw [inducedChain_comp]

theorem cubeChain_boundary (p : GenLoop (Fin 3) X x) :
    ((singularComplex X).d 3 2).hom (cubeChain p) = 0 :=
  boundaryThree_suspensionOne_of_cycle x _ (boundaryOne_loop (GenLoop.toLoop 0 p))

/-- The actual singular three-cycle of the native based cube. -/
def cubeCycle (p : GenLoop (Fin 3) X x) : ModuleHomology.Cycle (singularComplex X) 3 :=
  pathCubeCycle x (GenLoop.toLoop (0 : Fin 3) p)

@[simp] theorem cubeCycle_val (p : GenLoop (Fin 3) X x) :
    (cubeCycle p).1 = cubeChain p := rfl

/-- The cube's class in the actual integral singular third homology. -/
def cubeHomologyClass (p : GenLoop (Fin 3) X x) : SingularHomology X 3 :=
  ModuleHomology.cycleClass (singularComplex X) 3 (cubeCycle p)

theorem cubeHomologyClass_eq_pathCubeClass (p : GenLoop (Fin 3) X x) :
    cubeHomologyClass p = pathCubeClass x (GenLoop.toLoop (0 : Fin 3) p) := rfl

/-- Genuine homotopy relative to the entire cube boundary preserves the class. -/
theorem cubeHomologyClass_homotopic {p q : GenLoop (Fin 3) X x}
    (h : GenLoop.Homotopic p q) : cubeHomologyClass p = cubeHomologyClass q :=
  pathCubeClass_homotopic x (GenLoop.homotopicTo (0 : Fin 3) h)

theorem toLoop_const :
    GenLoop.toLoop (0 : Fin 3) (GenLoop.const : GenLoop (Fin 3) X x) =
      Path.refl (GenLoop.const : BasedLoopSpace x) := by
  apply Path.ext
  funext t
  apply GenLoop.ext
  intro u
  rfl

@[simp] theorem cubeHomologyClass_const :
    cubeHomologyClass (GenLoop.const : GenLoop (Fin 3) X x) = 0 := by
  rw [cubeHomologyClass_eq_pathCubeClass, toLoop_const, pathCubeClass_refl]

theorem toLoop_transAt (p q : GenLoop (Fin 3) X x) :
    GenLoop.toLoop (0 : Fin 3) (GenLoop.transAt (0 : Fin 3) p q) =
      (GenLoop.toLoop (0 : Fin 3) p).trans (GenLoop.toLoop (0 : Fin 3) q) := by
  have h := congrArg (GenLoop.toLoop (0 : Fin 3))
    (GenLoop.fromLoop_trans_toLoop (i := (0 : Fin 3)) (p := p) (q := q))
  rw [GenLoop.to_from] at h
  exact h.symm

/-- Native concatenation along coordinate zero adds the actual cubical classes. -/
theorem cubeHomologyClass_transAt (p q : GenLoop (Fin 3) X x) :
    cubeHomologyClass (GenLoop.transAt (0 : Fin 3) p q) =
      cubeHomologyClass p + cubeHomologyClass q := by
  simp only [cubeHomologyClass_eq_pathCubeClass, toLoop_transAt, pathCubeClass_trans]

end Wikipedia.HopfProblem.ThirdHurewicz
