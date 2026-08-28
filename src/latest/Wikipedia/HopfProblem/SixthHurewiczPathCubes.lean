import Wikipedia.HopfProblem.SixthHurewiczChains

/-!
# Evaluated five-loop-space paths in actual sixth singular homology

Evaluating a based path of native five-dimensional generalized loops on
the actual five-cube chain gives a singular six-cycle. Homotopies and
concatenations are witnessed by explicit suspended seven-chains before
passing to homology or taking any homotopy quotient.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SixthHurewicz

open FirstHurewicz SingularMayerVietoris

variable {X : Type} [TopologicalSpace X]

def pathCubeCycle (x : X)
    (p : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const) :
    ModuleHomology.Cycle (singularComplex X) 6 :=
  ModuleHomology.mkCycle (singularComplex X) 6 (suspensionOne x (pathChain p))
    (boundarySix_suspensionOne_of_cycle x (pathChain p) (boundaryOne_loop p))

@[simp] theorem pathCubeCycle_val (x : X)
    (p : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const) :
    (pathCubeCycle x p).1 = suspensionOne x (pathChain p) := rfl

/-- The class belongs to Mathlib's actual integral singular `H₆`. -/
def pathCubeClass (x : X)
    (p : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const) : SingularHomology X 6 :=
  ModuleHomology.cycleClass (singularComplex X) 6 (pathCubeCycle x p)

/-- A path homotopy in the actual five-loop space supplies an explicit
singular seven-boundary between the evaluated six-cubes. -/
theorem pathCube_homotopy_boundary (x : X)
    {p q : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const} (H : p.Homotopy q) :
    ((singularComplex X).d 7 6).hom (suspensionTwo x (homotopyChain H)) =
      (pathCubeCycle x p).1 - (pathCubeCycle x q).1 := by
  rw [boundarySeven_suspensionTwo, boundaryTwo_loopHomotopy, map_sub]
  rfl

theorem pathCubeClass_homotopy (x : X)
    {p q : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const} (H : p.Homotopy q) :
    pathCubeClass x p = pathCubeClass x q :=
  (ModuleHomology.cycleClass_eq_iff (singularComplex X) 6 _ _).mpr
    ⟨suspensionTwo x (homotopyChain H), pathCube_homotopy_boundary x H⟩

theorem pathCubeClass_homotopic (x : X)
    {p q : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const} (h : p.Homotopic q) :
    pathCubeClass x p = pathCubeClass x q := by
  obtain ⟨H⟩ := h
  exact pathCubeClass_homotopy x H

@[simp] theorem pathCubeClass_refl (x : X) :
    pathCubeClass x (Path.refl (GenLoop.const : BasedLoopSpace x)) = 0 := by
  apply (ModuleHomology.cycleClass_eq_zero_iff (singularComplex X) 6 _).mpr
  refine ⟨suspensionTwo x (constantTriangleChain (GenLoop.const : BasedLoopSpace x)), ?_⟩
  rw [boundarySeven_suspensionTwo, boundaryTwo_constantTriangleChain]
  rfl

/-- The suspended concatenation triangle is the actual degree-seven
witness for additivity of the six-dimensional cube class. -/
theorem pathCube_concat_boundary (x : X)
    (p q : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const) :
    ((singularComplex X).d 7 6).hom (-suspensionTwo x (concatChain p q)) =
      (pathCubeCycle x (p.trans q)).1 -
        ((pathCubeCycle x p).1 + (pathCubeCycle x q).1) := by
  rw [map_neg, boundarySeven_suspensionTwo, boundaryTwo_concatChain, map_add, map_sub]
  simp only [pathCubeCycle_val]
  abel

theorem pathCubeClass_trans (x : X)
    (p q : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const) :
    pathCubeClass x (p.trans q) = pathCubeClass x p + pathCubeClass x q := by
  unfold pathCubeClass
  rw [← map_add]
  apply (ModuleHomology.cycleClass_eq_iff (singularComplex X) 6 _ _).mpr
  exact ⟨-suspensionTwo x (concatChain p q), pathCube_concat_boundary x p q⟩

end Wikipedia.HopfProblem.SixthHurewicz
