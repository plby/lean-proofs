import Wikipedia.HomotopyGroupsOfSpheres.SeventhHurewicz.Chains

/-!
# Evaluated six-loop-space paths in actual seventh singular homology

Evaluating a based path of native six-dimensional generalized loops on
the actual six-cube chain gives a singular seven-cycle. Homotopies and
concatenations are witnessed by explicit suspended eight-chains before
passing to homology or taking any homotopy quotient.
-/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.SeventhHurewicz

open Wikipedia.HopfProblem

open FirstHurewicz SingularMayerVietoris

variable {X : Type} [TopologicalSpace X]

def pathCubeCycle (x : X)
    (p : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const) :
    ModuleHomology.Cycle (singularComplex X) 7 :=
  ModuleHomology.mkCycle (singularComplex X) 7 (suspensionOne x (pathChain p))
    (boundarySeven_suspensionOne_of_cycle x (pathChain p) (boundaryOne_loop p))

@[simp] theorem pathCubeCycle_val (x : X)
    (p : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const) :
    (pathCubeCycle x p).1 = suspensionOne x (pathChain p) := rfl

/-- The class belongs to Mathlib's actual integral singular `H₇`. -/
def pathCubeClass (x : X)
    (p : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const) : SingularHomology X 7 :=
  ModuleHomology.cycleClass (singularComplex X) 7 (pathCubeCycle x p)

/-- A path homotopy in the actual six-loop space supplies an explicit
singular eight-boundary between the evaluated seven-cubes. -/
theorem pathCube_homotopy_boundary (x : X)
    {p q : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const} (H : p.Homotopy q) :
    ((singularComplex X).d 8 7).hom (suspensionTwo x (homotopyChain H)) =
      (pathCubeCycle x p).1 - (pathCubeCycle x q).1 := by
  rw [boundaryEight_suspensionTwo, boundaryTwo_loopHomotopy, map_sub]
  rfl

theorem pathCubeClass_homotopy (x : X)
    {p q : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const} (H : p.Homotopy q) :
    pathCubeClass x p = pathCubeClass x q :=
  (ModuleHomology.cycleClass_eq_iff (singularComplex X) 7 _ _).mpr
    ⟨suspensionTwo x (homotopyChain H), pathCube_homotopy_boundary x H⟩

theorem pathCubeClass_homotopic (x : X)
    {p q : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const} (h : p.Homotopic q) :
    pathCubeClass x p = pathCubeClass x q := by
  obtain ⟨H⟩ := h
  exact pathCubeClass_homotopy x H

@[simp] theorem pathCubeClass_refl (x : X) :
    pathCubeClass x (Path.refl (GenLoop.const : BasedLoopSpace x)) = 0 := by
  apply (ModuleHomology.cycleClass_eq_zero_iff (singularComplex X) 7 _).mpr
  refine ⟨suspensionTwo x (constantTriangleChain (GenLoop.const : BasedLoopSpace x)), ?_⟩
  rw [boundaryEight_suspensionTwo, boundaryTwo_constantTriangleChain]
  rfl

/-- The suspended concatenation triangle is the actual degree-eight
witness for additivity of the seven-dimensional cube class. -/
theorem pathCube_concat_boundary (x : X)
    (p q : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const) :
    ((singularComplex X).d 8 7).hom (-suspensionTwo x (concatChain p q)) =
      (pathCubeCycle x (p.trans q)).1 -
        ((pathCubeCycle x p).1 + (pathCubeCycle x q).1) := by
  rw [map_neg, boundaryEight_suspensionTwo, boundaryTwo_concatChain, map_add, map_sub]
  simp only [pathCubeCycle_val]
  abel

theorem pathCubeClass_trans (x : X)
    (p q : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const) :
    pathCubeClass x (p.trans q) = pathCubeClass x p + pathCubeClass x q := by
  unfold pathCubeClass
  rw [← map_add]
  apply (ModuleHomology.cycleClass_eq_iff (singularComplex X) 7 _ _).mpr
  exact ⟨-suspensionTwo x (concatChain p q), pathCube_concat_boundary x p q⟩

end Wikipedia.HomotopyGroupsOfSpheres.SeventhHurewicz
