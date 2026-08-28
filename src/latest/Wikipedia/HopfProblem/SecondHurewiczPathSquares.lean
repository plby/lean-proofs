import Wikipedia.HopfProblem.SecondHurewiczChains

/-!
# Evaluated loop-space paths in actual second singular homology

The square associated with a based loop in the native loop space is an
actual singular two-cycle. Its homotopy and concatenation identities are
proved by the explicit suspended three-chains, before taking any homotopy
quotient.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SecondHurewicz

open FirstHurewicz SingularMayerVietoris

variable {X : Type} [TopologicalSpace X]

def pathSquareCycle (x : X)
    (p : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const) :
    ModuleHomology.Cycle (singularComplex X) 2 :=
  ModuleHomology.mkCycle (singularComplex X) 2 (suspensionOne x (pathChain p))
    (boundaryTwo_suspensionOne_of_cycle x (pathChain p) (boundaryOne_loop p))

@[simp] theorem pathSquareCycle_val (x : X)
    (p : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const) :
    (pathSquareCycle x p).1 = suspensionOne x (pathChain p) := rfl

/-- The class lives in Mathlib's integral singular `H₂`, not in a replacement quotient. -/
def pathSquareClass (x : X)
    (p : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const) : SingularHomology X 2 :=
  ModuleHomology.cycleClass (singularComplex X) 2 (pathSquareCycle x p)

/-- A path homotopy in the actual loop space supplies an explicit singular
three-boundary between the evaluated squares. -/
theorem pathSquare_homotopy_boundary (x : X)
    {p q : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const} (H : p.Homotopy q) :
    ((singularComplex X).d 3 2).hom (suspensionTwo x (homotopyChain H)) =
      (pathSquareCycle x p).1 - (pathSquareCycle x q).1 := by
  rw [boundaryThree_suspensionTwo, boundaryTwo_loopHomotopy, map_sub]
  rfl

theorem pathSquareClass_homotopy (x : X)
    {p q : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const} (H : p.Homotopy q) :
    pathSquareClass x p = pathSquareClass x q :=
  (ModuleHomology.cycleClass_eq_iff (singularComplex X) 2 _ _).mpr
    ⟨suspensionTwo x (homotopyChain H), pathSquare_homotopy_boundary x H⟩

theorem pathSquareClass_homotopic (x : X)
    {p q : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const} (h : p.Homotopic q) :
    pathSquareClass x p = pathSquareClass x q := by
  obtain ⟨H⟩ := h
  exact pathSquareClass_homotopy x H

@[simp] theorem pathSquareClass_refl (x : X) :
    pathSquareClass x (Path.refl (GenLoop.const : BasedLoopSpace x)) = 0 := by
  apply (ModuleHomology.cycleClass_eq_zero_iff (singularComplex X) 2 _).mpr
  refine ⟨suspensionTwo x (constantTriangleChain (GenLoop.const : BasedLoopSpace x)), ?_⟩
  rw [boundaryThree_suspensionTwo, boundaryTwo_constantTriangleChain]
  rfl

/-- The suspended concatenation triangle is the actual degree-three witness
for additivity of the two-dimensional square class. -/
theorem pathSquare_concat_boundary (x : X)
    (p q : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const) :
    ((singularComplex X).d 3 2).hom (-suspensionTwo x (concatChain p q)) =
      (pathSquareCycle x (p.trans q)).1 -
        ((pathSquareCycle x p).1 + (pathSquareCycle x q).1) := by
  rw [map_neg, boundaryThree_suspensionTwo, boundaryTwo_concatChain, map_add, map_sub]
  simp only [pathSquareCycle_val]
  abel

theorem pathSquareClass_trans (x : X)
    (p q : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const) :
    pathSquareClass x (p.trans q) = pathSquareClass x p + pathSquareClass x q := by
  unfold pathSquareClass
  rw [← map_add]
  apply (ModuleHomology.cycleClass_eq_iff (singularComplex X) 2 _ _).mpr
  exact ⟨-suspensionTwo x (concatChain p q), pathSquare_concat_boundary x p q⟩

end Wikipedia.HopfProblem.SecondHurewicz
