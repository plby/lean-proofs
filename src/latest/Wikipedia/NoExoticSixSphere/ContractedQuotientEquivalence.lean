import Mathlib.Topology.Homotopy.Equiv
import Mathlib.Topology.ContinuousMap.Basic

/-!
# A homotopy inverse from an actual fiber-preserving contraction

Suppose a continuous quotient identifies precisely one subset, leaving all
other points distinct. A homotopy of the source which preserves that subset
and ends by mapping it to one point gives an actual homotopy inverse.
The endpoint and the time-dependent comparison both descend through the
original quotient maps. No abstract replacement quotient is introduced.
-/

noncomputable section

open Set Function Topology
open scoped unitInterval

namespace NoExoticSixSphere.ContractedQuotient

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  (q : C(X, Y)) (hq : IsQuotientMap q) (S : Set X)
  (hfiber : ∀ x y, q x = q y ↔ x = y ∨ x ∈ S ∧ y ∈ S)
  {g : C(X, X)} (a : X) (hg : ∀ x ∈ S, g x = a)

include hfiber hg in
theorem endpoint_respects (x y : X) (h : q x = q y) : g x = g y := by
  rcases (hfiber x y).mp h with rfl | ⟨hx, hy⟩
  · rfl
  · exact (hg x hx).trans (hg y hy).symm

def inverse : C(Y, X) := IsQuotientMap.lift hq g (endpoint_respects q S hfiber a hg)

theorem inverse_comp : (inverse q hq S hfiber a hg).comp q = g :=
  IsQuotientMap.lift_comp hq g (endpoint_respects q S hfiber a hg)

theorem inverse_apply (x : X) : inverse q hq S hfiber a hg (q x) = g x :=
  ContinuousMap.congr_fun (inverse_comp q hq S hfiber a hg) x

def timeQuotient : C(I × X, I × Y) := (ContinuousMap.id I).prodMap q

variable [CompactSpace X] [T2Space Y]

include hq in
theorem isQuotientMap_timeQuotient : IsQuotientMap (timeQuotient q) := by
  apply IsQuotientMap.of_surjective_continuous ?_ (timeQuotient q).continuous
  rintro ⟨t, y⟩
  obtain ⟨x, hx⟩ := hq.surjective y
  exact ⟨(t, x), Prod.ext rfl hx⟩

variable (H : (ContinuousMap.id X).Homotopy g)
  (hH : ∀ (t : I) (x : X), x ∈ S → H (t, x) ∈ S)

def homotopyImage : C(I × X, Y) := q.comp H.toContinuousMap

omit [CompactSpace X] [T2Space Y] in
include hfiber hH in
theorem homotopyImage_respects (p r : I × X) (h : timeQuotient q p = timeQuotient q r) :
    homotopyImage q H p = homotopyImage q H r := by
  rcases p with ⟨t, x⟩
  rcases r with ⟨s, y⟩
  have ht : t = s := congrArg Prod.fst h
  have hxy : q x = q y := congrArg Prod.snd h
  subst s
  rcases (hfiber x y).mp hxy with rfl | ⟨hx, hy⟩
  · rfl
  · exact (hfiber _ _).mpr (Or.inr ⟨hH t x hx, hH t y hy⟩)

def descendedMap : C(I × Y, Y) :=
  IsQuotientMap.lift (f := timeQuotient q) (isQuotientMap_timeQuotient q hq)
    (homotopyImage q H) (homotopyImage_respects q S hfiber H hH)

theorem descendedMap_apply (t : I) (x : X) :
    descendedMap q hq S hfiber H hH (t, q x) = q (H (t, x)) :=
  ContinuousMap.congr_fun
    (IsQuotientMap.lift_comp (f := timeQuotient q) (isQuotientMap_timeQuotient q hq)
      (homotopyImage q H) (homotopyImage_respects q S hfiber H hH)) (t, x)

def rightHomotopy : (ContinuousMap.id Y).Homotopy (q.comp (inverse q hq S hfiber a hg)) where
  toContinuousMap := descendedMap q hq S hfiber H hH
  map_zero_left y := by
    obtain ⟨x, rfl⟩ := hq.surjective y
    change descendedMap q hq S hfiber H hH (0, q x) = q x
    rw [descendedMap_apply, H.apply_zero]
    rfl
  map_one_left y := by
    obtain ⟨x, rfl⟩ := hq.surjective y
    change descendedMap q hq S hfiber H hH (1, q x) = q (inverse q hq S hfiber a hg (q x))
    rw [descendedMap_apply, H.apply_one, inverse_apply]

/-- The forward map of the constructed homotopy equivalence is the supplied quotient itself. -/
def homotopyEquiv : ContinuousMap.HomotopyEquiv X Y where
  toFun := q
  invFun := inverse q hq S hfiber a hg
  left_inv := by
    rw [inverse_comp]
    exact ⟨H.symm⟩
  right_inv := ⟨(rightHomotopy q hq S hfiber a hg H hH).symm⟩

theorem homotopyEquiv_toFun : (homotopyEquiv q hq S hfiber a hg H hH).toFun = q := rfl

end NoExoticSixSphere.ContractedQuotient
