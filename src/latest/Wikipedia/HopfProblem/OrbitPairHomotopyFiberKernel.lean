import Wikipedia.HopfProblem.OrbitPairHomotopyFiber
import Wikipedia.NoExoticSixSphere.InducedHomotopyMap

/-!
# Exactness at the source of a map, using its actual homotopy fibre

A native generalized loop maps to the constant class exactly when it comes
from the homotopy fibre. The forward construction curries its actual relative
nullhomotopy and fixes every cube face. Conversely the fibre's path coordinate
is the required relative nullhomotopy. No fibration exactness is assumed.
-/

noncomputable section

namespace Wikipedia.HopfProblem.OrbitPair.HomotopyFiber

open NoExoticSixSphere

variable {N X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

def liftGenLoop (f : C(X, Y)) (x : X) (p : GenLoop N X x)
    (H : (f.comp p.val).HomotopyRel (ContinuousMap.const _ (f x)) (Cube.boundary N)) :
    GenLoop N (Space f (f x)) (basepoint f x) :=
  ⟨lift f (f x) p.val H.toHomotopy, by
    intro z hz
    apply Subtype.ext
    apply Prod.ext
    · exact p.property z hz
    · apply ContinuousMap.ext
      intro t
      exact (H.eq_fst t hz).trans (congrArg f (p.property z hz))⟩

theorem projection_liftGenLoop (f : C(X, Y)) (x : X) (p : GenLoop N X x)
    (H : (f.comp p.val).HomotopyRel (ContinuousMap.const _ (f x)) (Cube.boundary N)) :
    HigherHomotopy.genLoopMap (projection f (f x)) rfl (liftGenLoop f x p H) = p := rfl

def projectedGenLoopNullhomotopy (f : C(X, Y)) (x : X)
    (q : GenLoop N (Space f (f x)) (basepoint f x)) :
    (f.comp ((projection f (f x)).comp q.val)).HomotopyRel
      (ContinuousMap.const _ (f x)) (Cube.boundary N) where
  toContinuousMap := (evaluation f (f x)).comp
    ⟨fun z ↦ (z.1, q.val z.2), continuous_fst.prodMk (q.val.continuous.comp continuous_snd)⟩
  map_zero_left z := (q.val z).property.1
  map_one_left z := (q.val z).property.2
  prop' t z hz := by
    change (q.val z).val.2 t = f ((q.val z).val.1)
    rw [q.property z hz]
    rfl

theorem map_eq_const_iff_exists_fiber_class (f : C(X, Y)) (x : X)
    (c : HomotopyGroup N X x) :
    HigherHomotopy.map f rfl c = (Quotient.mk' GenLoop.const : HomotopyGroup N Y (f x)) ↔
      ∃ q : HomotopyGroup N (Space f (f x)) (basepoint f x),
        HigherHomotopy.map (projection f (f x)) rfl q = c := by
  constructor
  · refine Quotient.inductionOn c ?_
    intro p hp
    obtain ⟨H⟩ := Quotient.exact hp
    refine ⟨Quotient.mk' (liftGenLoop f x p H), ?_⟩
    exact congrArg (fun r : GenLoop N X x ↦ (Quotient.mk' r : HomotopyGroup N X x))
      (projection_liftGenLoop f x p H)
  · rintro ⟨q, rfl⟩
    refine Quotient.inductionOn q ?_
    intro q
    exact Quotient.sound ⟨projectedGenLoopNullhomotopy f x q⟩

theorem projection_range_eq_ker [DecidableEq N] [Nonempty N] (f : C(X, Y)) (x : X) :
    (HigherHomotopy.mapMonoidHom (N := N) (projection f (f x))
      (projection_basepoint f x)).range =
        (HigherHomotopy.mapMonoidHom (N := N) f (y := x) rfl).ker := by
  ext c
  exact (map_eq_const_iff_exists_fiber_class f x c).symm

end Wikipedia.HopfProblem.OrbitPair.HomotopyFiber
