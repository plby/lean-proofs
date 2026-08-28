import Wikipedia.NoExoticSixSphere.HomotopyFiberDeformationRetract

/-!
# Actual homotopy fibers of homotopic maps

Both endpoint slices are strong deformation retracts of the parameter
cylinder. Applying the explicit fiber transport equivalence to these
slices proves homotopy invariance. In particular a specified nullhomotopy
identifies the actual homotopy fiber with the source times native loops.
-/

noncomputable section

open scoped unitInterval ContinuousMap
open Wikipedia.HopfProblem.OrbitPair

namespace NoExoticSixSphere.HomotopyFiberHomotopyInvariance

open HomotopyFiber

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

def slice (X : Type*) [TopologicalSpace X] (t : I) : C(X, I × X) :=
  ⟨fun x ↦ (t, x), continuous_const.prodMk continuous_id⟩

def projection (X : Type*) [TopologicalSpace X] : C(I × X, X) :=
  ⟨Prod.snd, continuous_snd⟩

def sliceContraction (X : Type*) [TopologicalSpace X] (t : I) :
    (ContinuousMap.id (I × X)).HomotopyRel
      ((slice X t).comp (projection X)) (Set.range (slice X t)) where
  toFun p := (Set.Icc.convexComb p.2.1 t p.1, p.2.2)
  continuous_toFun :=
    (Set.Icc.continuous_convexComb_prod.comp
      ((continuous_fst.comp continuous_snd).prodMk
        (continuous_const.prodMk continuous_fst))).prodMk (continuous_snd.comp continuous_snd)
  map_zero_left p := Prod.ext (Set.Icc.convexComb_zero _ _) rfl
  map_one_left p := Prod.ext (Set.Icc.convexComb_one _ _) rfl
  prop' s p hp := by
    obtain ⟨x, rfl⟩ := hp
    exact Prod.ext (Set.Icc.convexComb_eq t s) rfl

def sliceFiberEquiv (G : C(I × X, Y)) (b : Y) (t : I) :
    Space (G.comp (slice X t)) b ≃ₕ Space G b :=
  HomotopyFiberDeformationRetract.equivalence G b (slice X t) (projection X)
    (hri := fun _ ↦ rfl) (H := sliceContraction X t)

def mapCongr {f g : C(X, Y)} (h : f = g) (b : Y) : Space f b ≃ₜ Space g b := by
  subst g
  exact Homeomorph.refl _

theorem zero_map {f g : C(X, Y)} (H : f.Homotopy g) :
    H.toContinuousMap.comp (slice X 0) = f := by
  apply ContinuousMap.ext
  exact H.map_zero_left

theorem one_map {f g : C(X, Y)} (H : f.Homotopy g) :
    H.toContinuousMap.comp (slice X 1) = g := by
  apply ContinuousMap.ext
  exact H.map_one_left

def equivalence {f g : C(X, Y)} (H : f.Homotopy g) (b : Y) : Space f b ≃ₕ Space g b :=
  ((mapCongr (zero_map H).symm b).toHomotopyEquiv.trans
    (sliceFiberEquiv H.toContinuousMap b 0)).trans
    ((sliceFiberEquiv H.toContinuousMap b 1).symm.trans
      (mapCongr (one_map H) b).toHomotopyEquiv)

def constantFiberHomeomorph (X : Type*) [TopologicalSpace X] (b : Y) :
    Space (ContinuousMap.const X b) b ≃ₜ X × Path b b where
  toFun p := (p.val.1,
    { toContinuousMap := p.val.2, source' := p.property.1, target' := p.property.2 })
  invFun p := ⟨(p.1, p.2.toContinuousMap), p.2.source, p.2.target⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    (continuous_fst.comp continuous_subtype_val).prodMk
      (continuous_induced_rng.mpr (continuous_snd.comp continuous_subtype_val))
  continuous_invFun :=
    (continuous_fst.prodMk (continuous_induced_dom.comp continuous_snd)).subtype_mk _

def nullhomotopyEquiv (f : C(X, Y)) (b : Y)
    (H : f.Homotopy (ContinuousMap.const X b)) : Space f b ≃ₕ X × Path b b :=
  (equivalence H b).trans (constantFiberHomeomorph X b).toHomotopyEquiv

end NoExoticSixSphere.HomotopyFiberHomotopyInvariance
