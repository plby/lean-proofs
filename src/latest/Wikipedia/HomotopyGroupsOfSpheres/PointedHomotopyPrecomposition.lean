import Mathlib.Topology.Homotopy.Basic

/-! # Precomposition of a based homotopy by an actual pointed map -/

namespace Wikipedia.HomotopyGroupsOfSpheres

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

def pointedHomotopyPrecomp {f g : C(Y, Z)} {y : Y}
    (H : f.HomotopyRel g {y}) (p : C(X, Y)) (x : X) (hp : p x = y) :
    (f.comp p).HomotopyRel (g.comp p) {x} where
  toHomotopy := H.toHomotopy.compContinuousMap p
  prop' t z hz := by
    have he : z = x := Set.mem_singleton_iff.mp hz
    subst z
    change H (t, p x) = f (p x)
    rw [hp]
    exact H.eq_fst t (Set.mem_singleton y)

end Wikipedia.HomotopyGroupsOfSpheres
