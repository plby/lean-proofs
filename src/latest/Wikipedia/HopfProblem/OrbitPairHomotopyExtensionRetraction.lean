import Wikipedia.HopfProblem.OrbitPairHomotopyExtensionPushout
import Mathlib.Topology.Homotopy.Equiv

/-!
# Exact retractions from homotopy extension

For a map with homotopy extension, a chosen homotopy inverse can be
adjusted to an exact retraction. The other inverse identity remains a
homotopy. This does not yet assert a strong deformation retraction:
stationarity of that second homotopy is a separate requirement.
-/

noncomputable section

universe u

open CategoryTheory unitInterval

namespace Wikipedia.HopfProblem.OrbitPair.HomotopyExtension

theorem extend_homotopy {A B Z : TopCat.{u}} (i : A ⟶ B)
    (hi : HasHomotopyExtension i) (f : C(B, Z)) {g : C(A, Z)}
    (H : (f.comp i.hom).Homotopy g) :
    ∃ f' : C(B, Z), ∃ K : f.Homotopy f', ∀ t a, K (t, i a) = H (t, a) := by
  obtain ⟨L, hL0, hLi⟩ := hi Z f H.toContinuousMap H.map_zero_left
  let f' := L.comp ⟨fun b ↦ (1, b), continuous_const.prodMk continuous_id⟩
  exact ⟨f', ⟨L, hL0, fun _ ↦ rfl⟩, hLi⟩

theorem exists_retraction {A B : TopCat.{u}} (i : A ⟶ B)
    (hi : HasHomotopyExtension i) (e : ContinuousMap.HomotopyEquiv A B)
    (he : e.toFun = i.hom) :
    ∃ r : C(B, A), r.comp i.hom = ContinuousMap.id A ∧
      (i.hom.comp r).Homotopic (ContinuousMap.id B) := by
  have hleft : (e.invFun.comp i.hom).Homotopic (ContinuousMap.id A) := by
    rw [← he]
    exact e.left_inv
  obtain ⟨H⟩ := hleft
  obtain ⟨r, K, hKi⟩ := extend_homotopy i hi e.invFun H
  refine ⟨r, ?_, ?_⟩
  · apply ContinuousMap.ext
    intro a
    exact (K.map_one_left (i a)).symm.trans ((hKi 1 a).trans (H.map_one_left a))
  · have hr : (i.hom.comp e.invFun).Homotopic (ContinuousMap.id B) := by
      rw [← he]
      exact e.right_inv
    exact (ContinuousMap.Homotopic.comp (.refl i.hom) ⟨K.symm⟩).trans hr

end Wikipedia.HopfProblem.OrbitPair.HomotopyExtension
