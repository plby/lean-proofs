import Wikipedia.NoExoticSixSphere.NativeEquivalenceDiskLifting

/-!
# An actual path-space diagonal for finite-domain homotopy reflection

A point records two source points and a path between their original
images. Lifting a map to this space through its diagonal up to homotopy
reflects an original target homotopy. Both endpoint maps are retained.
The native isomorphism property of this diagonal is not assumed to follow
from that of the original map here; that comparison remains separate.
-/

noncomputable section

open scoped Topology unitInterval
open Wikipedia.HopfProblem

namespace NoExoticSixSphere.HomotopyPullbackDiagonal

variable {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

abbrev Space (F : C(X, Y)) :=
  {p : (X × X) × C(I, Y) // p.2 0 = F p.1.1 ∧ p.2 1 = F p.1.2}

def left (F : C(X, Y)) : C(Space F, X) :=
  ⟨fun p ↦ p.val.1.1, continuous_fst.comp (continuous_fst.comp continuous_subtype_val)⟩

def right (F : C(X, Y)) : C(Space F, X) :=
  ⟨fun p ↦ p.val.1.2, continuous_snd.comp (continuous_fst.comp continuous_subtype_val)⟩

def diagonal (F : C(X, Y)) : C(X, Space F) where
  toFun x := ⟨((x, x), ContinuousMap.const I (F x)), rfl, rfl⟩
  continuous_toFun := ((continuous_id.prodMk continuous_id).prodMk
    (F.comp (ContinuousMap.fst : C(X × I, X))).curry.continuous).subtype_mk _

theorem left_diagonal (F : C(X, Y)) : (left F).comp (diagonal F) = ContinuousMap.id X := rfl

theorem right_diagonal (F : C(X, Y)) : (right F).comp (diagonal F) = ContinuousMap.id X := rfl

def evaluation (F : C(X, Y)) : C(I × Space F, Y) :=
  ⟨fun p ↦ p.2.val.2 p.1, continuous_eval.comp
    ((continuous_snd.comp (continuous_subtype_val.comp continuous_snd)).prodMk continuous_fst)⟩

theorem evaluation_zero (F : C(X, Y)) (p : Space F) :
    evaluation F (0, p) = F (left F p) := p.property.1

theorem evaluation_one (F : C(X, Y)) (p : Space F) :
    evaluation F (1, p) = F (right F p) := p.property.2

def ofHomotopy (F : C(X, Y)) (u v : C(Z, X)) (H : (F.comp u).Homotopy (F.comp v)) :
    C(Z, Space F) := by
  let paths : C(Z, C(I, Y)) :=
    (H.toContinuousMap.comp ⟨Prod.swap, continuous_swap⟩).curry
  exact ⟨fun z ↦ ⟨((u z, v z), paths z), H.apply_zero z, H.apply_one z⟩,
    ((u.continuous.prodMk v.continuous).prodMk paths.continuous).subtype_mk _⟩

theorem left_ofHomotopy (F : C(X, Y)) (u v : C(Z, X))
    (H : (F.comp u).Homotopy (F.comp v)) : (left F).comp (ofHomotopy F u v H) = u := rfl

theorem right_ofHomotopy (F : C(X, Y)) (u v : C(Z, X))
    (H : (F.comp u).Homotopy (F.comp v)) : (right F).comp (ofHomotopy F u v H) = v := rfl

theorem homotopic_reflect_of_diagonal_mapsLift (F : C(X, Y))
    (hF : DegreeCollapse.FiniteCells.MapsLift (diagonal F) Z) (u v : C(Z, X))
    (H : (F.comp u).Homotopic (F.comp v)) : u.Homotopic v := by
  obtain ⟨K⟩ := H
  obtain ⟨w, hw⟩ := hF (ofHomotopy F u v K)
  have hwu := (ContinuousMap.Homotopic.refl (left F)).comp hw
  have hwv := (ContinuousMap.Homotopic.refl (right F)).comp hw
  change w.Homotopic u at hwu
  change w.Homotopic v at hwv
  exact hwu.symm.trans hwv

theorem finiteCell_homotopic_reflect [PathConnectedSpace X] (F : C(X, Y))
    (hF : ∀ n (x : X), Function.Bijective
      (HigherHomotopy.map (N := Fin n) (diagonal F) (y := x) rfl))
    {d : ℕ} (hZ : DegreeCollapse.FiniteCells.Built d Z) (u v : C(Z, X))
    (H : (F.comp u).Homotopic (F.comp v)) : u.Homotopic v :=
  homotopic_reflect_of_diagonal_mapsLift F
    (RelativeDiskLifting.finiteCell_mapsLift_of_native_bijective (diagonal F) hF hZ) u v H

end NoExoticSixSphere.HomotopyPullbackDiagonal
