import Wikipedia.HopfProblem.SecondHurewiczPathSquares

/-!
# The genuine square representative of the second Hurewicz class

The fixed square chain is the cross product of the two positively oriented
interval chains, transported to Mathlib's literal `Fin 2` cube. Applying
the actual generalized loop gives exactly the evaluated loop-space chain.
The relative homotopy and concatenation laws therefore concern native
two-dimensional generalized loops and their original square maps.
-/

noncomputable section

open scoped unitInterval Topology

namespace Wikipedia.HopfProblem.SecondHurewicz

open FirstHurewicz SingularMayerVietoris PeriodTorusHigherHomology

attribute [local instance] integerLinearMapModule integerTensorModule

/-- The standard oriented singular chain of the product square. -/
def productSquareChain : Chains (I × I) 2 :=
  crossProductEdge I I 1 intervalChain intervalChain

/-- Its four boundary edges, with the actual singular-chain orientation. -/
theorem productSquareChain_boundary :
    boundaryTwo (I × I) productSquareChain =
      inducedChain (crossInsertLeft (1 : I)) 1 intervalChain -
        inducedChain (crossInsertLeft (0 : I)) 1 intervalChain -
        (inducedChain (crossInsertRight (1 : I)) 1 intervalChain -
          inducedChain (crossInsertRight (0 : I)) 1 intervalChain) := by
  change ((singularComplex (I × I)).d 2 1).hom
    (crossProductEdge I I 1 intervalChain intervalChain) = _
  rw [crossProductEdge_boundary 0]
  change crossProductZeroLeft I I 1 (boundaryOne I intervalChain) intervalChain -
    crossProductEdge I I 0 intervalChain (boundaryOne I intervalChain) = _
  simp only [intervalChain_boundary, map_sub, LinearMap.sub_apply,
    crossProductEdge_point_right]
  simp only [pointChain, crossProductZeroLeft_simplex_left]
  rfl

/-- The same fixed square chain in the actual native two-dimensional cube. -/
def fundamentalSquareChain : Chains (Fin 2 → I) 2 :=
  inducedChain squareCoordinates 2 productSquareChain

variable {X : Type} [TopologicalSpace X] {x : X}

theorem induced_intervalChain {a b : X} (p : Path a b) :
    inducedChain p.toContinuousMap 1 intervalChain = pathChain p := by
  rw [intervalChain, pathChain, inducedChain_simplex]
  apply congrArg (simplexChain X 1)
  ext s
  rfl

theorem suspensionOne_toLoop (p : GenLoop (Fin 2) X x) :
    suspensionOne x (pathChain (GenLoop.toLoop (0 : Fin 2) p)) =
      inducedChain (squareMap p) 2 productSquareChain := by
  have h := crossProductEdge_natural (GenLoop.toLoop (0 : Fin 2) p).toContinuousMap
    (ContinuousMap.id I) 1 intervalChain intervalChain
  rw [induced_intervalChain, inducedChain_id, LinearMap.id_apply] at h
  rw [suspensionOne_apply, ← h]
  change ((inducedChain (evaluation x) 2).comp
    (inducedChain ((GenLoop.toLoop (0 : Fin 2) p).toContinuousMap.prodMap
      (ContinuousMap.id I)) 2)) productSquareChain = _
  rw [← inducedChain_comp, evaluation_comp_toLoop]

/-- The actual singular two-chain associated with the native generalized loop. -/
def squareChain (p : GenLoop (Fin 2) X x) : Chains X 2 :=
  suspensionOne x (pathChain (GenLoop.toLoop (0 : Fin 2) p))

/-- Its defining square is the original generalized loop, on the fixed
oriented chain of Mathlib's actual cube. -/
theorem squareChain_eq_induced (p : GenLoop (Fin 2) X x) :
    squareChain p = inducedChain p.val 2 fundamentalSquareChain := by
  rw [squareChain, suspensionOne_toLoop]
  change inducedChain (p.val.comp squareCoordinates) 2 productSquareChain =
    ((inducedChain p.val 2).comp (inducedChain squareCoordinates 2)) productSquareChain
  rw [inducedChain_comp]

theorem squareChain_boundary (p : GenLoop (Fin 2) X x) :
    boundaryTwo X (squareChain p) = 0 :=
  boundaryTwo_suspensionOne_of_cycle x _ (boundaryOne_loop (GenLoop.toLoop 0 p))

def squareCycle (p : GenLoop (Fin 2) X x) : ModuleHomology.Cycle (singularComplex X) 2 :=
  pathSquareCycle x (GenLoop.toLoop (0 : Fin 2) p)

@[simp] theorem squareCycle_val (p : GenLoop (Fin 2) X x) :
    (squareCycle p).1 = squareChain p := rfl

/-- The native square's actual integral singular homology class. -/
def squareHomologyClass (p : GenLoop (Fin 2) X x) : SingularHomology X 2 :=
  ModuleHomology.cycleClass (singularComplex X) 2 (squareCycle p)

theorem squareHomologyClass_eq_pathSquareClass (p : GenLoop (Fin 2) X x) :
    squareHomologyClass p = pathSquareClass x (GenLoop.toLoop (0 : Fin 2) p) := rfl

/-- Homotopy relative to the actual cube boundary preserves the class. -/
theorem squareHomologyClass_homotopic {p q : GenLoop (Fin 2) X x}
    (h : GenLoop.Homotopic p q) : squareHomologyClass p = squareHomologyClass q :=
  pathSquareClass_homotopic x (GenLoop.homotopicTo (0 : Fin 2) h)

theorem toLoop_const :
    GenLoop.toLoop (0 : Fin 2) (GenLoop.const : GenLoop (Fin 2) X x) =
      Path.refl (GenLoop.const : BasedLoopSpace x) := by
  apply Path.ext
  funext t
  apply GenLoop.ext
  intro u
  rfl

@[simp] theorem squareHomologyClass_const :
    squareHomologyClass (GenLoop.const : GenLoop (Fin 2) X x) = 0 := by
  rw [squareHomologyClass_eq_pathSquareClass, toLoop_const, pathSquareClass_refl]

theorem toLoop_transAt (p q : GenLoop (Fin 2) X x) :
    GenLoop.toLoop (0 : Fin 2) (GenLoop.transAt (0 : Fin 2) p q) =
      (GenLoop.toLoop (0 : Fin 2) p).trans (GenLoop.toLoop (0 : Fin 2) q) := by
  have h := congrArg (GenLoop.toLoop (0 : Fin 2))
    (GenLoop.fromLoop_trans_toLoop (i := (0 : Fin 2)) (p := p) (q := q))
  rw [GenLoop.to_from] at h
  exact h.symm

/-- Concatenating actual squares along coordinate zero adds their actual classes. -/
theorem squareHomologyClass_transAt (p q : GenLoop (Fin 2) X x) :
    squareHomologyClass (GenLoop.transAt (0 : Fin 2) p q) =
      squareHomologyClass p + squareHomologyClass q := by
  simp only [squareHomologyClass_eq_pathSquareClass, toLoop_transAt,
    pathSquareClass_trans]

end Wikipedia.HopfProblem.SecondHurewicz
