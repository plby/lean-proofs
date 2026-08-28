import Wikipedia.NoExoticSixSphere.PathFamilyCurrying

/-!
# The actual homotopy fibre of a continuous map

A fibre point consists of a point in the source and a continuous path from
its image to the chosen target point. The topology is the subspace topology
of the product with the native compact-open continuous-map space. A genuine
nullhomotopy gives a continuous lift to this fibre by currying.
-/

noncomputable section

open Set

namespace Wikipedia.HopfProblem.OrbitPair.HomotopyFiber

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

abbrev Space (f : C(X, Y)) (b : Y) :=
  {p : X × C(unitInterval, Y) // p.2 0 = f p.1 ∧ p.2 1 = b}

def projection (f : C(X, Y)) (b : Y) : C(Space f b, X) :=
  ⟨fun p ↦ p.val.1, continuous_fst.comp continuous_subtype_val⟩

def basepoint (f : C(X, Y)) (x : X) : Space f (f x) :=
  ⟨(x, ContinuousMap.const _ (f x)), rfl, rfl⟩

theorem projection_basepoint (f : C(X, Y)) (x : X) :
    projection f (f x) (basepoint f x) = x := rfl

def evaluation (f : C(X, Y)) (b : Y) : C(unitInterval × Space f b, Y) where
  toFun z := z.2.val.2 z.1
  continuous_toFun := continuous_eval.comp
    ((continuous_snd.comp (continuous_subtype_val.comp continuous_snd)).prodMk continuous_fst)

theorem evaluation_zero (f : C(X, Y)) (b : Y) (p : Space f b) :
    evaluation f b (0, p) = f (projection f b p) := p.property.1

theorem evaluation_one (f : C(X, Y)) (b : Y) (p : Space f b) :
    evaluation f b (1, p) = b := p.property.2

def projectionNullhomotopy (f : C(X, Y)) (x : X) :
    (f.comp (projection f (f x))).HomotopyRel
      (ContinuousMap.const _ (f x)) {basepoint f x} where
  toContinuousMap := evaluation f (f x)
  map_zero_left p := p.property.1
  map_one_left p := p.property.2
  prop' _ p hp := by
    have he : p = basepoint f x := hp
    subst p
    rfl

def lift (f : C(X, Y)) (b : Y) (p : C(Z, X))
    (H : (f.comp p).Homotopy (ContinuousMap.const _ b)) : C(Z, Space f b) := by
  let paths : C(Z, C(unitInterval, Y)) :=
    (H.toContinuousMap.comp ⟨Prod.swap, continuous_swap⟩).curry
  exact {
    toFun z := ⟨(p z, paths z), H.apply_zero z, H.apply_one z⟩
    continuous_toFun := (p.continuous.prodMk paths.continuous).subtype_mk _ }

theorem projection_lift (f : C(X, Y)) (b : Y) (p : C(Z, X))
    (H : (f.comp p).Homotopy (ContinuousMap.const _ b)) :
    (projection f b).comp (lift f b p H) = p := rfl

theorem lift_path_apply (f : C(X, Y)) (b : Y) (p : C(Z, X))
    (H : (f.comp p).Homotopy (ContinuousMap.const _ b)) (z : Z) (t : unitInterval) :
    (lift f b p H z).val.2 t = H (t, z) := rfl

end Wikipedia.HopfProblem.OrbitPair.HomotopyFiber
