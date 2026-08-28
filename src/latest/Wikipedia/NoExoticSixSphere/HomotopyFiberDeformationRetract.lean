import Wikipedia.HopfProblem.OrbitPairHomotopyFiberLiftedFamily
import Mathlib.Topology.Homotopy.Equiv

/-!
# Homotopy fibers over a genuine deformation retract of the source

Transport along the given deformation constructs the inverse on actual
compact-open homotopy fibers. Both inverse homotopies are extracted from
that same lifted family, including its restriction over the retract.
-/

noncomputable section

open scoped unitInterval ContinuousMap
open Wikipedia.HopfProblem.OrbitPair

namespace NoExoticSixSphere.HomotopyFiberDeformationRetract

open HomotopyFiber

variable {A X Y : Type*} [TopologicalSpace A] [TopologicalSpace X] [TopologicalSpace Y]
  (f : C(X, Y)) (b : Y) (i : C(A, X)) (r : C(X, A))
  (hri : ∀ a, r (i a) = a)
  (H : (ContinuousMap.id X).HomotopyRel (i.comp r) (Set.range i))

def inclusionMap : C(Space (f.comp i) b, Space f b) where
  toFun p := ⟨(i p.val.1, p.val.2), p.property⟩
  continuous_toFun :=
    ((i.continuous.comp (continuous_fst.comp continuous_subtype_val)).prodMk
      (continuous_snd.comp continuous_subtype_val)).subtype_mk _

def family : C(I × Space f b, Space f b) :=
  transport f b (ContinuousMap.id _)
    (H.toContinuousMap.comp ⟨fun p ↦ (p.1, projection f b p.2),
      continuous_fst.prodMk ((projection f b).continuous.comp continuous_snd)⟩)
    (fun p ↦ H.map_zero_left (projection f b p))

theorem family_projection (s : I) (p : Space f b) :
    projection f b (family f b i r H (s, p)) = H (s, projection f b p) := rfl

theorem family_zero (p : Space f b) : family f b i r H (0, p) = p :=
  transport_initial f b (ContinuousMap.id _) _ _ p

def retractionMap : C(Space f b, Space (f.comp i) b) where
  toFun p := ⟨(r (projection f b p), (family f b i r H (1, p)).val.2),
    (family f b i r H (1, p)).property.1.trans
      (congrArg f (H.map_one_left (projection f b p))),
    (family f b i r H (1, p)).property.2⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (r.continuous.comp (projection f b).continuous).prodMk
      (continuous_snd.comp (continuous_subtype_val.comp
        ((family f b i r H).continuous.comp (continuous_const.prodMk continuous_id))))

theorem inclusion_retraction (p : Space f b) :
    inclusionMap f b i (retractionMap f b i r H p) = family f b i r H (1, p) := by
  apply Subtype.ext
  apply Prod.ext
  · exact (H.map_one_left (projection f b p)).symm
  · rfl

def retractionHomotopy : (ContinuousMap.id (Space f b)).Homotopy
    ((inclusionMap f b i).comp (retractionMap f b i r H)) where
  toContinuousMap := family f b i r H
  map_zero_left := family_zero f b i r H
  map_one_left p := (inclusion_retraction f b i r H p).symm

def restrictedFamily : C(I × Space (f.comp i) b, Space (f.comp i) b) where
  toFun p := ⟨(p.2.val.1, (family f b i r H (p.1, inclusionMap f b i p.2)).val.2),
    (family f b i r H (p.1, inclusionMap f b i p.2)).property.1.trans
      (congrArg f (H.eq_fst p.1 ⟨p.2.val.1, rfl⟩)),
    (family f b i r H (p.1, inclusionMap f b i p.2)).property.2⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (continuous_fst.comp (continuous_subtype_val.comp continuous_snd)).prodMk
      (continuous_snd.comp (continuous_subtype_val.comp
        ((family f b i r H).continuous.comp
          (continuous_fst.prodMk ((inclusionMap f b i).continuous.comp continuous_snd)))))

theorem restrictedFamily_zero (p : Space (f.comp i) b) :
    restrictedFamily f b i r H (0, p) = p := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change (family f b i r H (0, inclusionMap f b i p)).val.2 = p.val.2
    rw [family_zero]
    rfl

include hri in
theorem restrictedFamily_one (p : Space (f.comp i) b) :
    restrictedFamily f b i r H (1, p) =
      retractionMap f b i r H (inclusionMap f b i p) := by
  apply Subtype.ext
  exact Prod.ext (hri p.val.1).symm rfl

def restrictedHomotopy : (ContinuousMap.id (Space (f.comp i) b)).Homotopy
    ((retractionMap f b i r H).comp (inclusionMap f b i)) where
  toContinuousMap := restrictedFamily f b i r H
  map_zero_left := restrictedFamily_zero f b i r H
  map_one_left := restrictedFamily_one f b i r (hri := hri) (H := H)

def equivalence : Space (f.comp i) b ≃ₕ Space f b where
  toFun := inclusionMap f b i
  invFun := retractionMap f b i r H
  left_inv := ⟨(restrictedHomotopy f b i r (hri := hri) (H := H)).symm⟩
  right_inv := ⟨(retractionHomotopy f b i r H).symm⟩

end NoExoticSixSphere.HomotopyFiberDeformationRetract
