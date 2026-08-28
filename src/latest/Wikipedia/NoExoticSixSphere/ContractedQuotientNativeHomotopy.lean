import Wikipedia.NoExoticSixSphere.ContractedQuotientEquivalence
import Wikipedia.NoExoticSixSphere.InducedHomotopyMap

/-!
# Native homotopy maps of a based contracted quotient

When the extended contraction fixes its selected point, both inverse
homotopies of the actual quotient fix their respective basepoints.
They therefore give inverse maps on the original native cube classes,
without introducing basepoint-change maps or an abstract replacement.
-/

noncomputable section

open Set Topology
open scoped unitInterval

namespace NoExoticSixSphere.HigherHomotopy

variable {N X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  (f : C(X, Y)) (r : C(Y, X)) {x : X} {y : Y} (hf : f x = y) (hr : r y = x)

theorem map_leftInverse_of_based_homotopy
    (H : (r.comp f).HomotopyRel (ContinuousMap.id X) {x}) :
    Function.LeftInverse (map (N := N) r hr) (map (N := N) f hf) := by
  intro c
  refine Quotient.inductionOn c fun p ↦ ?_
  apply Quotient.sound
  refine ⟨{ toHomotopy := H.toHomotopy.compContinuousMap p.val, prop' := ?_ }⟩
  intro t z hz
  exact H.eq_fst t (show p.val z ∈ ({x} : Set X) from p.property z hz)

include hr in
theorem map_bijective_of_based_inverse
    (H : (r.comp f).HomotopyRel (ContinuousMap.id X) {x})
    (K : (f.comp r).HomotopyRel (ContinuousMap.id Y) {y}) :
    Function.Bijective (map (N := N) f hf) := by
  have hleft := map_leftInverse_of_based_homotopy (N := N) f r hf hr H
  have hright := map_leftInverse_of_based_homotopy (N := N) r f hr hf K
  exact ⟨hleft.injective, fun c ↦ ⟨map r hr c, hright c⟩⟩

end NoExoticSixSphere.HigherHomotopy

namespace NoExoticSixSphere.ContractedQuotient

variable {N X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [CompactSpace X] [T2Space Y]

theorem map_bijective_of_fixed_contraction
    (q : C(X, Y)) (hq : IsQuotientMap q) (S : Set X)
    (hfiber : ∀ x y, q x = q y ↔ x = y ∨ x ∈ S ∧ y ∈ S)
    {g : C(X, X)} (a : X) (ha : a ∈ S) (hg : ∀ x ∈ S, g x = a)
    (H : (ContinuousMap.id X).HomotopyRel g {a})
    (hH : ∀ (t : I) (x : X), x ∈ S → H (t, x) ∈ S) :
    Function.Bijective (HigherHomotopy.map (N := N) q (y := a) rfl) := by
  let r := inverse q hq S hfiber a hg
  have hr : r (q a) = a := (inverse_apply q hq S hfiber a hg a).trans (hg a ha)
  let L : (ContinuousMap.id X).HomotopyRel (r.comp q) {a} :=
    H.cast rfl (inverse_comp q hq S hfiber a hg).symm
  let R : (ContinuousMap.id Y).HomotopyRel (q.comp r) {q a} := {
    toHomotopy := rightHomotopy q hq S hfiber a hg H.toHomotopy hH
    prop' := by
      rintro t z (rfl : z = q a)
      change descendedMap q hq S hfiber H.toHomotopy hH (t, q a) = q a
      rw [descendedMap_apply]
      exact (hfiber _ _).mpr (Or.inr ⟨hH t a ha, ha⟩) }
  exact HigherHomotopy.map_bijective_of_based_inverse q r rfl hr L.symm R.symm

end NoExoticSixSphere.ContractedQuotient
