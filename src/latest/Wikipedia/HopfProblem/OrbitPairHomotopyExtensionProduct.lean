import Wikipedia.HopfProblem.OrbitPairHomotopyExtensionProductGluing
import Wikipedia.HopfProblem.OrbitPairNativeSkeletalHomotopyExtension

/-!
# Homotopy extension for products of closed inclusions

Multiply the universal cylinder retraction by the parameter space and
compose with the checked closed-cover pasting map. The parameter space
need not be locally compact. The native finite-dimensional realization
theorem then supplies an unconditional application to simplicial
monomorphisms and their products with any space.
-/

noncomputable section

universe u

open CategoryTheory unitInterval Topology

namespace Wikipedia.HopfProblem.OrbitPair.HomotopyExtension

theorem prod_right {A B : TopCat.{u}} (i : A ⟶ B)
    (hi : HasHomotopyExtension i) (hc : IsClosedEmbedding i) (K : TopCat.{u}) :
    HasHomotopyExtension (TopCat.ofHom (i.hom.prodMap (ContinuousMap.id K))) := by
  intro Z F G h0
  obtain ⟨R, hR0, hRi⟩ := exists_cylinder_retraction i hi
  have h0' : ∀ a k, G (0, (a, k)) = F (i a, k) := fun a k ↦ h0 (a, k)
  let M : C(I × (B × K), ↥(cylinderBase i) × K) :=
    ⟨fun p ↦ (R (p.1, p.2.1), p.2.2),
      (R.continuous.comp (continuous_fst.prodMk continuous_snd.fst)).prodMk continuous_snd.snd⟩
  let H := (cylinderProductMap i hc F G h0').comp M
  refine ⟨H, ?_, ?_⟩
  · rintro ⟨b, k⟩
    change cylinderProductMap i hc F G h0' (R (0, b), k) = F (b, k)
    rw [hR0]
    exact cylinderProductMap_bottom i hc F G h0' b k
  · rintro t ⟨a, k⟩
    change cylinderProductMap i hc F G h0' (R (t, i a), k) = G (t, (a, k))
    rw [hRi]
    exact cylinderProductMap_side i hc F G h0' t a k

theorem realized_mono_product_of_dimension {X Y : SSet.{u}} (i : X ⟶ Y) [Mono i]
    (d : ℕ) [Y.HasDimensionLT d] (K : TopCat.{u}) :
    HasHomotopyExtension
      (TopCat.ofHom ((SSet.toTop.map i).hom.prodMap (ContinuousMap.id K))) :=
  prod_right (SSet.toTop.map i) (realized_mono_of_dimension i d)
    (RealizationSimplex.realizedMono_isClosedEmbedding i) K

theorem realized_mono_product_of_finite {X Y : SSet.{u}} (i : X ⟶ Y) [Mono i]
    [Y.Finite] (K : TopCat.{u}) :
    HasHomotopyExtension
      (TopCat.ofHom ((SSet.toTop.map i).hom.prodMap (ContinuousMap.id K))) :=
  prod_right (SSet.toTop.map i) (realized_mono_of_finite i)
    (RealizationSimplex.realizedMono_isClosedEmbedding i) K

end Wikipedia.HopfProblem.OrbitPair.HomotopyExtension
