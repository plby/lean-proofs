import Wikipedia.HopfProblem.OrbitPairNeighborhoodCylinderRetraction
import Wikipedia.HopfProblem.OrbitPairHomotopyExtensionProductGluing

/-!
# Neighborhood deformation data and homotopy extension

A cylinder retraction gives homotopy extension by closed-cover pasting.
Combining the two explicit constructions proves the equivalence between
homotopy extension and neighborhood deformation data for a closed
embedding. The reverse implication needs only embedding: the data itself
proves that the range is closed.
-/

noncomputable section

universe u

open CategoryTheory unitInterval Topology

namespace Wikipedia.HopfProblem.OrbitPair.HomotopyExtension

theorem of_cylinder_retraction {A B : TopCat.{u}} (i : A ⟶ B) (hc : IsClosedEmbedding i)
    (R : C(I × B, ↥(cylinderBase i)))
    (hR0 : ∀ b, R (0, b) = cylinderBottom i b)
    (hRi : ∀ t a, R (t, i a) = cylinderSide i (t, a)) : HasHomotopyExtension i := by
  intro Z F G h0
  let U : TopCat.{u} := TopCat.of PUnit.{u + 1}
  let FP : C(B × U, Z) := F.comp ContinuousMap.fst
  let GP : C(I × (A × U), Z) :=
    G.comp ⟨fun p ↦ (p.1, p.2.1), continuous_fst.prodMk continuous_snd.fst⟩
  have h0' : ∀ a k, GP (0, (a, k)) = FP (i a, k) := fun a _ ↦ h0 a
  let H := (cylinderProductMap i hc FP GP h0').comp
    ⟨fun p ↦ (R p, PUnit.unit), R.continuous.prodMk continuous_const⟩
  refine ⟨H, ?_, ?_⟩
  · intro b
    change cylinderProductMap i hc FP GP h0' (R (0, b), PUnit.unit) = F b
    rw [hR0, cylinderProductMap_bottom]
    rfl
  · intro t a
    change cylinderProductMap i hc FP GP h0' (R (t, i a), PUnit.unit) = G (t, a)
    rw [hRi, cylinderProductMap_side]
    rfl

end Wikipedia.HopfProblem.OrbitPair.HomotopyExtension

namespace Wikipedia.HopfProblem.OrbitPair.NeighborhoodDeformation

theorem hasHomotopyExtension {A B : TopCat.{u}} {i : A ⟶ B} (D : Data i)
    (hi : IsEmbedding i) : HomotopyExtension.HasHomotopyExtension i :=
  HomotopyExtension.of_cylinder_retraction i ⟨hi, range_isClosed D⟩ (cylinderRetraction D)
    (cylinderRetraction_bottom D) (cylinderRetraction_side D)

theorem hasHomotopyExtension_iff {A B : TopCat.{u}} (i : A ⟶ B) (hc : IsClosedEmbedding i) :
    HomotopyExtension.HasHomotopyExtension i ↔ Nonempty (Data i) :=
  ⟨fun h ↦ exists_data i h hc, fun ⟨D⟩ ↦ hasHomotopyExtension D hc.isEmbedding⟩

end Wikipedia.HopfProblem.OrbitPair.NeighborhoodDeformation
