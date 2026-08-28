import Wikipedia.HomotopyGroupsOfSpheres.SeventhHurewicz.PathCubes

/-!
# The genuine seven-cube representative of the seventh Hurewicz map

The oriented seven-chain is the actual cross product of the first interval
with the frozen fundamental six-cube in the remaining coordinates.
Applying the original native generalized loop gives the evaluated
loop-space chain. Actual eight-chains prove its homotopy and concatenation
laws before taking the native homotopy quotient.
-/

noncomputable section

open scoped unitInterval Topology

namespace Wikipedia.HomotopyGroupsOfSpheres.SeventhHurewicz

open Wikipedia.HopfProblem

open FirstHurewicz SingularMayerVietoris PeriodTorusHigherHomology

attribute [local instance] integerLinearMapModule integerTensorModule

/-- The genuine interval-times-six-cube singular seven-chain. -/
def productCubeChain : Chains (I × (Fin 6 → I)) 7 :=
  crossProductEdge I (Fin 6 → I) 6 SecondHurewicz.intervalChain
    SixthHurewicz.fundamentalCubeChain

/-- The fixed fundamental seven-chain in Mathlib's literal native seven-cube. -/
def fundamentalCubeChain : Chains (Fin 7 → I) 7 :=
  inducedChain cubeCoordinates 7 productCubeChain

variable {X : Type} [TopologicalSpace X] {x : X}

theorem suspensionOne_toLoop (p : GenLoop (Fin 7) X x) :
    suspensionOne x (pathChain (GenLoop.toLoop (0 : Fin 7) p)) =
      inducedChain (cubeMap p) 7 productCubeChain := by
  have h := crossProductEdge_natural (GenLoop.toLoop (0 : Fin 7) p).toContinuousMap
    (ContinuousMap.id (Fin 6 → I)) 6 SecondHurewicz.intervalChain
    SixthHurewicz.fundamentalCubeChain
  rw [SecondHurewicz.induced_intervalChain, inducedChain_id, LinearMap.id_apply] at h
  rw [suspensionOne_apply, ← h]
  change ((inducedChain (evaluation x) 7).comp
    (inducedChain ((GenLoop.toLoop (0 : Fin 7) p).toContinuousMap.prodMap
      (ContinuousMap.id (Fin 6 → I))) 7)) productCubeChain = _
  rw [← inducedChain_comp, evaluation_comp_toLoop]

/-- The actual singular seven-chain of the original native generalized loop. -/
def cubeChain (p : GenLoop (Fin 7) X x) : Chains X 7 :=
  suspensionOne x (pathChain (GenLoop.toLoop (0 : Fin 7) p))

/-- The representative applies the original cube map to the genuine
recursively constructed fundamental seven-chain. -/
theorem cubeChain_eq_induced (p : GenLoop (Fin 7) X x) :
    cubeChain p = inducedChain p.val 7 fundamentalCubeChain := by
  rw [cubeChain, suspensionOne_toLoop]
  change inducedChain (p.val.comp cubeCoordinates) 7 productCubeChain =
    ((inducedChain p.val 7).comp (inducedChain cubeCoordinates 7)) productCubeChain
  rw [inducedChain_comp]

theorem cubeChain_boundary (p : GenLoop (Fin 7) X x) :
    ((singularComplex X).d 7 6).hom (cubeChain p) = 0 :=
  boundarySeven_suspensionOne_of_cycle x _ (boundaryOne_loop (GenLoop.toLoop 0 p))

/-- The genuine integral singular seven-cycle of the native based cube. -/
def cubeCycle (p : GenLoop (Fin 7) X x) : ModuleHomology.Cycle (singularComplex X) 7 :=
  pathCubeCycle x (GenLoop.toLoop (0 : Fin 7) p)

@[simp] theorem cubeCycle_val (p : GenLoop (Fin 7) X x) :
    (cubeCycle p).1 = cubeChain p := rfl

/-- The seven-cube's class in actual integral singular seventh homology. -/
def cubeHomologyClass (p : GenLoop (Fin 7) X x) : SingularHomology X 7 :=
  ModuleHomology.cycleClass (singularComplex X) 7 (cubeCycle p)

theorem cubeHomologyClass_eq_pathCubeClass (p : GenLoop (Fin 7) X x) :
    cubeHomologyClass p = pathCubeClass x (GenLoop.toLoop (0 : Fin 7) p) := rfl

/-- Actual homotopy relative to the whole cube boundary preserves the class. -/
theorem cubeHomologyClass_homotopic {p q : GenLoop (Fin 7) X x}
    (h : GenLoop.Homotopic p q) : cubeHomologyClass p = cubeHomologyClass q :=
  pathCubeClass_homotopic x (GenLoop.homotopicTo (0 : Fin 7) h)

theorem toLoop_const :
    GenLoop.toLoop (0 : Fin 7) (GenLoop.const : GenLoop (Fin 7) X x) =
      Path.refl (GenLoop.const : BasedLoopSpace x) := by
  apply Path.ext
  funext t
  apply GenLoop.ext
  intro u
  rfl

@[simp] theorem cubeHomologyClass_const :
    cubeHomologyClass (GenLoop.const : GenLoop (Fin 7) X x) = 0 := by
  rw [cubeHomologyClass_eq_pathCubeClass, toLoop_const, pathCubeClass_refl]

theorem toLoop_transAt (p q : GenLoop (Fin 7) X x) :
    GenLoop.toLoop (0 : Fin 7) (GenLoop.transAt (0 : Fin 7) p q) =
      (GenLoop.toLoop (0 : Fin 7) p).trans (GenLoop.toLoop (0 : Fin 7) q) := by
  have h := congrArg (GenLoop.toLoop (0 : Fin 7))
    (GenLoop.fromLoop_trans_toLoop (i := (0 : Fin 7)) (p := p) (q := q))
  rw [GenLoop.to_from] at h
  exact h.symm

/-- Native concatenation along coordinate zero adds the genuine seven-cube classes. -/
theorem cubeHomologyClass_transAt (p q : GenLoop (Fin 7) X x) :
    cubeHomologyClass (GenLoop.transAt (0 : Fin 7) p q) =
      cubeHomologyClass p + cubeHomologyClass q := by
  simp only [cubeHomologyClass_eq_pathCubeClass, toLoop_transAt, pathCubeClass_trans]

end Wikipedia.HomotopyGroupsOfSpheres.SeventhHurewicz
