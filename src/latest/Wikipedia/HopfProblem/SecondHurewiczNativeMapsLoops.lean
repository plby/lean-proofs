import Mathlib.Topology.Homotopy.HomotopyGroup

/-!
# Continuous postcomposition of native generalized loops

These maps use Mathlib's actual generalized loops with their compact-open
subspace topology. They preserve the boundary condition, concatenation, and
homotopies relative to the boundary. Currying a generalized loop commutes
with postcomposition as an equality of actual paths in the lower loop space.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.SecondHurewicz

variable {N X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace Z]

/-- Continuous postcomposition on the actual space of generalized loops. -/
def mapGenLoop (f : C(X, Y)) (x : X) :
    C(GenLoop N X x, GenLoop N Y (f x)) where
  toFun p := ⟨f.comp p.val, fun t ht => congrArg f (p.property t ht)⟩
  continuous_toFun :=
    ((ContinuousMap.continuous_postcomp f).comp continuous_subtype_val).subtype_mk _

@[simp] theorem mapGenLoop_apply (f : C(X, Y)) (x : X)
    (p : GenLoop N X x) (t : N → I) :
    mapGenLoop f x p t = f (p t) := rfl

@[simp] theorem mapGenLoop_val (f : C(X, Y)) (x : X)
    (p : GenLoop N X x) :
    (mapGenLoop f x p).val = f.comp p.val := rfl

@[simp] theorem mapGenLoop_const (f : C(X, Y)) (x : X) :
    mapGenLoop (N := N) f x GenLoop.const = GenLoop.const := rfl

@[simp] theorem mapGenLoop_id (x : X) :
    mapGenLoop (N := N) (ContinuousMap.id X) x = ContinuousMap.id _ := by
  ext p t
  rfl

@[simp] theorem mapGenLoop_comp (f : C(X, Y)) (g : C(Y, Z)) (x : X) :
    mapGenLoop (N := N) (g.comp f) x =
      (mapGenLoop g (f x)).comp (mapGenLoop f x) := by
  ext p t
  rfl

@[simp] theorem mapGenLoop_constMap (x : X) (y : Y) :
    mapGenLoop (N := N) (ContinuousMap.const X y) x =
      ContinuousMap.const _ GenLoop.const := by
  ext p t
  rfl

/-- Postcomposition of an actual homotopy relative to the cube boundary. -/
def mapGenLoopHomotopy (f : C(X, Y)) (x : X) {p q : GenLoop N X x}
    (H : p.val.HomotopyRel q.val (Cube.boundary N)) :
    (mapGenLoop f x p).val.HomotopyRel
      (mapGenLoop f x q).val (Cube.boundary N) :=
  H.compContinuousMap f

@[simp] theorem mapGenLoopHomotopy_apply (f : C(X, Y)) (x : X)
    {p q : GenLoop N X x} (H : p.val.HomotopyRel q.val (Cube.boundary N))
    (t : I × (N → I)) :
    mapGenLoopHomotopy f x H t = f (H t) := rfl

/-- The native homotopy relation is preserved by postcomposition. -/
theorem mapGenLoop_homotopic (f : C(X, Y)) (x : X)
    {p q : GenLoop N X x} (h : GenLoop.Homotopic p q) :
    GenLoop.Homotopic (mapGenLoop f x p) (mapGenLoop f x q) :=
  h.comp_continuousMap f

section Coordinates

variable [DecidableEq N]

/-- Postcomposition commutes with concatenation along any cube coordinate. -/
@[simp] theorem mapGenLoop_transAt (f : C(X, Y)) (x : X) (i : N)
    (p q : GenLoop N X x) :
    mapGenLoop f x (GenLoop.transAt i p q) =
      GenLoop.transAt i (mapGenLoop f x p) (mapGenLoop f x q) := by
  apply GenLoop.ext
  intro t
  change f (if (t i : ℝ) ≤ 1 / 2 then _ else _) =
    if (t i : ℝ) ≤ 1 / 2 then _ else _
  split_ifs <;> rfl

/-- Postcomposition commutes with reversal along any cube coordinate. -/
@[simp] theorem mapGenLoop_symmAt (f : C(X, Y)) (x : X) (i : N)
    (p : GenLoop N X x) :
    mapGenLoop f x (GenLoop.symmAt i p) =
      GenLoop.symmAt i (mapGenLoop f x p) := by
  apply GenLoop.ext
  intro t
  rfl

/-- Currying commutes with actual postcomposition in the remaining loop space.
The endpoints agree definitionally, since a constant loop maps to a constant loop. -/
theorem mapGenLoop_toLoop (f : C(X, Y)) (x : X) (i : N)
    (p : GenLoop N X x) :
    GenLoop.toLoop i (mapGenLoop f x p) =
      (GenLoop.toLoop i p).map
        (mapGenLoop (N := {j : N // j ≠ i}) f x).continuous := by
  apply Path.ext
  funext t
  apply GenLoop.ext
  intro u
  rfl

end Coordinates

end Wikipedia.HopfProblem.SecondHurewicz
