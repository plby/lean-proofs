import Wikipedia.HopfProblem.OrbitPairHomotopyFiberLoopInclusion
import Mathlib.Topology.Homotopy.Equiv

/-!
# The homotopy fiber over a strongly contracted source

The explicit transport construction lifts a contraction of the source.
At its final time the whole homotopy fiber lies over the contraction point.
The lifted family on that fiber supplies the other inverse homotopy, so
the actual loop inclusion is a homotopy equivalence.
-/

noncomputable section

open scoped unitInterval ContinuousMap
open Wikipedia.HopfProblem.OrbitPair

namespace NoExoticSixSphere.HomotopyFiberStrongContraction

open HomotopyFiber

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  (f : C(X, Y)) (x : X)
  (H : (ContinuousMap.id X).HomotopyRel (ContinuousMap.const X x) {x})

def family : C(I × Space f (f x), Space f (f x)) :=
  transport f (f x) (ContinuousMap.id _)
    (H.toContinuousMap.comp ⟨fun p ↦ (p.1, projection f (f x) p.2),
      continuous_fst.prodMk ((projection f (f x)).continuous.comp continuous_snd)⟩)
    (fun p ↦ H.map_zero_left (projection f (f x) p))

theorem family_projection (s : I) (p : Space f (f x)) :
    projection f (f x) (family f x H (s, p)) = H (s, projection f (f x) p) := rfl

theorem family_zero (p : Space f (f x)) : family f x H (0, p) = p :=
  transport_initial f (f x) (ContinuousMap.id _) _ _ p

def endpoint : C(Space f (f x), Space f (f x)) :=
  (family f x H).comp ⟨fun p ↦ (1, p), continuous_const.prodMk continuous_id⟩

theorem endpoint_projection (p : Space f (f x)) :
    projection f (f x) (endpoint f x H p) = x :=
  H.map_one_left (projection f (f x) p)

def retraction : C(Space f (f x), Path (f x) (f x)) :=
  loopFamily f x (endpoint f x H) (endpoint_projection f x H)

theorem inclusion_retraction : (loopInclusion f x).comp (retraction f x H) = endpoint f x H :=
  loopInclusion_loopFamily f x (endpoint f x H) (endpoint_projection f x H)

def retractionHomotopy : (ContinuousMap.id (Space f (f x))).Homotopy
    ((loopInclusion f x).comp (retraction f x H)) where
  toContinuousMap := family f x H
  map_zero_left := family_zero f x H
  map_one_left p := by
    change endpoint f x H p = _
    rw [inclusion_retraction]

def restrictedFamily : C(I × Path (f x) (f x), Path (f x) (f x)) :=
  loopFamily f x
    ((family f x H).comp ⟨fun p ↦ (p.1, loopInclusion f x p.2),
      continuous_fst.prodMk ((loopInclusion f x).continuous.comp continuous_snd)⟩)
    (fun p ↦ H.eq_fst p.1 (Set.mem_singleton x))

theorem restrictedFamily_zero (p : Path (f x) (f x)) : restrictedFamily f x H (0, p) = p := by
  apply Path.ext
  funext t
  change (family f x H (0, loopInclusion f x p)).val.2 t = p t
  rw [family_zero]
  rfl

theorem restrictedFamily_one (p : Path (f x) (f x)) :
    restrictedFamily f x H (1, p) = retraction f x H (loopInclusion f x p) := rfl

def restrictedHomotopy : (ContinuousMap.id (Path (f x) (f x))).Homotopy
    ((retraction f x H).comp (loopInclusion f x)) where
  toContinuousMap := restrictedFamily f x H
  map_zero_left := restrictedFamily_zero f x H
  map_one_left := restrictedFamily_one f x H

def equivalence : Space f (f x) ≃ₕ Path (f x) (f x) where
  toFun := retraction f x H
  invFun := loopInclusion f x
  left_inv := ⟨(retractionHomotopy f x H).symm⟩
  right_inv := ⟨(restrictedHomotopy f x H).symm⟩

theorem equivalence_symm_apply (p : Path (f x) (f x)) :
    (equivalence f x H).symm p = loopInclusion f x p := rfl

end NoExoticSixSphere.HomotopyFiberStrongContraction
