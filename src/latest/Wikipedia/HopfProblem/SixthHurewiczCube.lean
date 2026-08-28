import Wikipedia.HopfProblem.SixthHurewiczPathCubes

/-!
# The genuine six-cube representative of the sixth Hurewicz map

The oriented six-chain is the actual cross product of the first interval
with the frozen fundamental five-cube in the remaining coordinates.
Applying the original native generalized loop gives the evaluated
loop-space chain. Actual seven-chains prove its homotopy and concatenation
laws before taking the native homotopy quotient.
-/

noncomputable section

open scoped unitInterval Topology

namespace Wikipedia.HopfProblem.SixthHurewicz

open FirstHurewicz SingularMayerVietoris PeriodTorusHigherHomology

attribute [local instance] integerLinearMapModule integerTensorModule

/-- The genuine interval-times-five-cube singular six-chain. -/
def productCubeChain : Chains (I × (Fin 5 → I)) 6 :=
  crossProductEdge I (Fin 5 → I) 5 SecondHurewicz.intervalChain
    FifthHurewicz.fundamentalCubeChain

/-- The fixed fundamental six-chain in Mathlib's literal native six-cube. -/
def fundamentalCubeChain : Chains (Fin 6 → I) 6 :=
  inducedChain cubeCoordinates 6 productCubeChain

variable {X : Type} [TopologicalSpace X] {x : X}

theorem suspensionOne_toLoop (p : GenLoop (Fin 6) X x) :
    suspensionOne x (pathChain (GenLoop.toLoop (0 : Fin 6) p)) =
      inducedChain (cubeMap p) 6 productCubeChain := by
  have h := crossProductEdge_natural (GenLoop.toLoop (0 : Fin 6) p).toContinuousMap
    (ContinuousMap.id (Fin 5 → I)) 5 SecondHurewicz.intervalChain
    FifthHurewicz.fundamentalCubeChain
  rw [SecondHurewicz.induced_intervalChain, inducedChain_id, LinearMap.id_apply] at h
  rw [suspensionOne_apply, ← h]
  change ((inducedChain (evaluation x) 6).comp
    (inducedChain ((GenLoop.toLoop (0 : Fin 6) p).toContinuousMap.prodMap
      (ContinuousMap.id (Fin 5 → I))) 6)) productCubeChain = _
  rw [← inducedChain_comp, evaluation_comp_toLoop]

/-- The actual singular six-chain of the original native generalized loop. -/
def cubeChain (p : GenLoop (Fin 6) X x) : Chains X 6 :=
  suspensionOne x (pathChain (GenLoop.toLoop (0 : Fin 6) p))

/-- The representative applies the original cube map to the genuine
recursively constructed fundamental six-chain. -/
theorem cubeChain_eq_induced (p : GenLoop (Fin 6) X x) :
    cubeChain p = inducedChain p.val 6 fundamentalCubeChain := by
  rw [cubeChain, suspensionOne_toLoop]
  change inducedChain (p.val.comp cubeCoordinates) 6 productCubeChain =
    ((inducedChain p.val 6).comp (inducedChain cubeCoordinates 6)) productCubeChain
  rw [inducedChain_comp]

theorem cubeChain_boundary (p : GenLoop (Fin 6) X x) :
    ((singularComplex X).d 6 5).hom (cubeChain p) = 0 :=
  boundarySix_suspensionOne_of_cycle x _ (boundaryOne_loop (GenLoop.toLoop 0 p))

/-- The genuine integral singular six-cycle of the native based cube. -/
def cubeCycle (p : GenLoop (Fin 6) X x) : ModuleHomology.Cycle (singularComplex X) 6 :=
  pathCubeCycle x (GenLoop.toLoop (0 : Fin 6) p)

@[simp] theorem cubeCycle_val (p : GenLoop (Fin 6) X x) :
    (cubeCycle p).1 = cubeChain p := rfl

/-- The six-cube's class in actual integral singular sixth homology. -/
def cubeHomologyClass (p : GenLoop (Fin 6) X x) : SingularHomology X 6 :=
  ModuleHomology.cycleClass (singularComplex X) 6 (cubeCycle p)

theorem cubeHomologyClass_eq_pathCubeClass (p : GenLoop (Fin 6) X x) :
    cubeHomologyClass p = pathCubeClass x (GenLoop.toLoop (0 : Fin 6) p) := rfl

/-- Actual homotopy relative to the whole cube boundary preserves the class. -/
theorem cubeHomologyClass_homotopic {p q : GenLoop (Fin 6) X x}
    (h : GenLoop.Homotopic p q) : cubeHomologyClass p = cubeHomologyClass q :=
  pathCubeClass_homotopic x (GenLoop.homotopicTo (0 : Fin 6) h)

theorem toLoop_const :
    GenLoop.toLoop (0 : Fin 6) (GenLoop.const : GenLoop (Fin 6) X x) =
      Path.refl (GenLoop.const : BasedLoopSpace x) := by
  apply Path.ext
  funext t
  apply GenLoop.ext
  intro u
  rfl

@[simp] theorem cubeHomologyClass_const :
    cubeHomologyClass (GenLoop.const : GenLoop (Fin 6) X x) = 0 := by
  rw [cubeHomologyClass_eq_pathCubeClass, toLoop_const, pathCubeClass_refl]

theorem toLoop_transAt (p q : GenLoop (Fin 6) X x) :
    GenLoop.toLoop (0 : Fin 6) (GenLoop.transAt (0 : Fin 6) p q) =
      (GenLoop.toLoop (0 : Fin 6) p).trans (GenLoop.toLoop (0 : Fin 6) q) := by
  have h := congrArg (GenLoop.toLoop (0 : Fin 6))
    (GenLoop.fromLoop_trans_toLoop (i := (0 : Fin 6)) (p := p) (q := q))
  rw [GenLoop.to_from] at h
  exact h.symm

/-- Native concatenation along coordinate zero adds the genuine six-cube classes. -/
theorem cubeHomologyClass_transAt (p q : GenLoop (Fin 6) X x) :
    cubeHomologyClass (GenLoop.transAt (0 : Fin 6) p q) =
      cubeHomologyClass p + cubeHomologyClass q := by
  simp only [cubeHomologyClass_eq_pathCubeClass, toLoop_transAt, pathCubeClass_trans]

end Wikipedia.HopfProblem.SixthHurewicz
