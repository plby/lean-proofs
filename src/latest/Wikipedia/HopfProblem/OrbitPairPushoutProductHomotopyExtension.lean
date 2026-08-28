import Wikipedia.HopfProblem.OrbitPairProductBoundaryPushout

/-!
# Homotopy extension for the actual categorical pushout-product map

The actual pushout is isomorphic to the checked literal product-boundary
union. Under that isomorphism its canonical map is exactly the union
inclusion. Closed embedding and homotopy extension therefore transfer
to the original categorical map.
-/

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits Topology

namespace Wikipedia.HopfProblem.OrbitPair.NeighborhoodProduct

variable {A X : TopCat.{u}} {B Y : TopCat.{v}} (i : A ⟶ X) (j : B ⟶ Y)

theorem canonicalMap_compatible :
    cornerLeft (A := A) j ≫ TopCat.ofHom (i.hom.prodMap (ContinuousMap.id Y)) =
      cornerRight (B := B) i ≫ TopCat.ofHom ((ContinuousMap.id X).prodMap j.hom) := rfl

def canonicalMap : pushout (cornerLeft (A := A) j) (cornerRight (B := B) i) ⟶
    TopCat.of (X × Y) :=
  pushout.desc (TopCat.ofHom (i.hom.prodMap (ContinuousMap.id Y)))
    (TopCat.ofHom ((ContinuousMap.id X).prodMap j.hom)) (canonicalMap_compatible i j)

theorem canonicalMap_inl :
    pushout.inl (cornerLeft (A := A) j) (cornerRight (B := B) i) ≫ canonicalMap i j =
      TopCat.ofHom (i.hom.prodMap (ContinuousMap.id Y)) :=
  pushout.inl_desc _ _ (canonicalMap_compatible i j)

theorem canonicalMap_inr :
    pushout.inr (cornerLeft (A := A) j) (cornerRight (B := B) i) ≫ canonicalMap i j =
      TopCat.ofHom ((ContinuousMap.id X).prodMap j.hom) :=
  pushout.inr_desc _ _ (canonicalMap_compatible i j)

def pushoutIso (hi : IsClosedEmbedding i) (hj : IsClosedEmbedding j) :
    pushout (cornerLeft (A := A) j) (cornerRight (B := B) i) ≅ TopCat.of ↥(boundary i j) :=
  (IsPushout.of_hasPushout (cornerLeft (A := A) j) (cornerRight (B := B) i)).isoIsPushout
    _ _ (isPushout i j hi hj)

theorem pushoutIso_inl (hi : IsClosedEmbedding i) (hj : IsClosedEmbedding j) :
    pushout.inl (cornerLeft (A := A) j) (cornerRight (B := B) i) ≫ (pushoutIso i j hi hj).hom =
      leftFace i j :=
  (IsPushout.of_hasPushout (cornerLeft (A := A) j) (cornerRight (B := B) i)).inl_isoIsPushout_hom
    _ _ (isPushout i j hi hj)

theorem pushoutIso_inr (hi : IsClosedEmbedding i) (hj : IsClosedEmbedding j) :
    pushout.inr (cornerLeft (A := A) j) (cornerRight (B := B) i) ≫ (pushoutIso i j hi hj).hom =
      rightFace i j :=
  (IsPushout.of_hasPushout (cornerLeft (A := A) j) (cornerRight (B := B) i)).inr_isoIsPushout_hom
    _ _ (isPushout i j hi hj)

theorem pushoutIso_inclusion (hi : IsClosedEmbedding i) (hj : IsClosedEmbedding j) :
    (pushoutIso i j hi hj).hom ≫ inclusion i j = canonicalMap i j := by
  apply pushout.hom_ext
  · rw [← Category.assoc, pushoutIso_inl, canonicalMap_inl]
    rfl
  · rw [← Category.assoc, pushoutIso_inr, canonicalMap_inr]
    rfl

theorem canonicalMap_isClosedEmbedding (hi : IsClosedEmbedding i) (hj : IsClosedEmbedding j) :
    IsClosedEmbedding (canonicalMap i j) := by
  rw [← pushoutIso_inclusion i j hi hj]
  exact (inclusion_isClosedEmbedding i j hi hj).comp
    (TopCat.homeoOfIso (pushoutIso i j hi hj)).isClosedEmbedding

theorem canonicalMap_hasHomotopyExtension
    (hi : HomotopyExtension.HasHomotopyExtension i) (hj : HomotopyExtension.HasHomotopyExtension j)
    (hci : IsClosedEmbedding i) (hcj : IsClosedEmbedding j) :
    HomotopyExtension.HasHomotopyExtension (canonicalMap i j) := by
  rw [← pushoutIso_inclusion i j hci hcj]
  exact HomotopyExtension.comp _ _ (HomotopyExtension.of_isIso _)
    (of_closed_homotopyExtension hi hj hci hcj)

end Wikipedia.HopfProblem.OrbitPair.NeighborhoodProduct
