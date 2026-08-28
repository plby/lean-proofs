import Wikipedia.HopfProblem.ThirdHurewiczChains

/-!
# Evaluated two-loop-space paths in actual third singular homology

Evaluating a based path of native two-dimensional generalized loops on
the actual square chain gives a singular three-cycle. Homotopies and
concatenations are witnessed by explicit suspended four-chains before
passing to homology or taking any homotopy quotient.
-/

noncomputable section

namespace Wikipedia.HopfProblem.ThirdHurewicz

open FirstHurewicz SingularMayerVietoris

variable {X : Type} [TopologicalSpace X]

def pathCubeCycle (x : X)
    (p : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const) :
    ModuleHomology.Cycle (singularComplex X) 3 :=
  ModuleHomology.mkCycle (singularComplex X) 3 (suspensionOne x (pathChain p))
    (boundaryThree_suspensionOne_of_cycle x (pathChain p) (boundaryOne_loop p))

@[simp] theorem pathCubeCycle_val (x : X)
    (p : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const) :
    (pathCubeCycle x p).1 = suspensionOne x (pathChain p) := rfl

/-- The class belongs to Mathlib's actual integral singular `H₃`. -/
def pathCubeClass (x : X)
    (p : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const) : SingularHomology X 3 :=
  ModuleHomology.cycleClass (singularComplex X) 3 (pathCubeCycle x p)

/-- A path homotopy in the actual two-loop space supplies an explicit
singular four-boundary between the evaluated cubes. -/
theorem pathCube_homotopy_boundary (x : X)
    {p q : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const} (H : p.Homotopy q) :
    ((singularComplex X).d 4 3).hom (suspensionTwo x (homotopyChain H)) =
      (pathCubeCycle x p).1 - (pathCubeCycle x q).1 := by
  rw [boundaryFour_suspensionTwo, boundaryTwo_loopHomotopy, map_sub]
  rfl

theorem pathCubeClass_homotopy (x : X)
    {p q : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const} (H : p.Homotopy q) :
    pathCubeClass x p = pathCubeClass x q :=
  (ModuleHomology.cycleClass_eq_iff (singularComplex X) 3 _ _).mpr
    ⟨suspensionTwo x (homotopyChain H), pathCube_homotopy_boundary x H⟩

theorem pathCubeClass_homotopic (x : X)
    {p q : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const} (h : p.Homotopic q) :
    pathCubeClass x p = pathCubeClass x q := by
  obtain ⟨H⟩ := h
  exact pathCubeClass_homotopy x H

@[simp] theorem pathCubeClass_refl (x : X) :
    pathCubeClass x (Path.refl (GenLoop.const : BasedLoopSpace x)) = 0 := by
  apply (ModuleHomology.cycleClass_eq_zero_iff (singularComplex X) 3 _).mpr
  refine ⟨suspensionTwo x (constantTriangleChain (GenLoop.const : BasedLoopSpace x)), ?_⟩
  rw [boundaryFour_suspensionTwo, boundaryTwo_constantTriangleChain]
  rfl

/-- The suspended concatenation triangle is the actual degree-four
witness for additivity of the three-dimensional cube class. -/
theorem pathCube_concat_boundary (x : X)
    (p q : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const) :
    ((singularComplex X).d 4 3).hom (-suspensionTwo x (concatChain p q)) =
      (pathCubeCycle x (p.trans q)).1 -
        ((pathCubeCycle x p).1 + (pathCubeCycle x q).1) := by
  rw [map_neg, boundaryFour_suspensionTwo, boundaryTwo_concatChain, map_add, map_sub]
  simp only [pathCubeCycle_val]
  abel

theorem pathCubeClass_trans (x : X)
    (p q : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const) :
    pathCubeClass x (p.trans q) = pathCubeClass x p + pathCubeClass x q := by
  unfold pathCubeClass
  rw [← map_add]
  apply (ModuleHomology.cycleClass_eq_iff (singularComplex X) 3 _ _).mpr
  exact ⟨-suspensionTwo x (concatChain p q), pathCube_concat_boundary x p q⟩

end Wikipedia.HopfProblem.ThirdHurewicz
