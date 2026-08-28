import Wikipedia.NoExoticSixSphere.JamesSphereConeStageContractible
import Wikipedia.NoExoticSixSphere.CompactAdjunctionPushout
import Wikipedia.NoExoticSixSphere.DoubleMappingCylinderEquivalence
import Wikipedia.HopfProblem.OrbitPairHomotopyExtensionProduct

/-!
# A contractible double mapping cylinder for the actual James attaching maps

The cone-boundary product map has the proved homotopy-extension property.
The actual adjunction square is a native topological pushout. Therefore
the literal double-cylinder collapse is a homotopy equivalence, and its
source is contractible because the original auxiliary cone stage is.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Topology
open Wikipedia.HopfProblem.OrbitPair

namespace NoExoticSixSphere.JamesSphere.ConeStage

def attachingLeft (n k : ℕ) : TopCat.of (Sphere n × James.stage (spherePole n) k) ⟶
    TopCat.of (ReducedCone.Space n × James.stage (spherePole n) k) :=
  TopCat.ofHom (data n k).embedding

def attachingRight (n k : ℕ) : TopCat.of (Sphere n × James.stage (spherePole n) k) ⟶
    TopCat.of (James.stage (spherePole n) (k + 1)) :=
  TopCat.ofHom (stageAction n k)

theorem attachingLeft_hasHomotopyExtension (n k : ℕ) :
    HomotopyExtension.HasHomotopyExtension (attachingLeft n k) :=
  HomotopyExtension.prod_right (ReducedCone.boundaryMorphism n)
    (ReducedCone.boundary_hasHomotopyExtension n) (ReducedCone.boundary_isClosedEmbedding n)
    (TopCat.of (James.stage (spherePole n) k))

theorem attachingSquare (n k : ℕ) : IsPushout (attachingLeft n k) (attachingRight n k)
    (TopCat.ofHom (quotientMap n k)) (TopCat.ofHom (words n k)) :=
  CompactAdjunction.isPushout (data n k)

def doubleSpace (n k : ℕ) : TopCat :=
  DoubleMappingCylinder.space (attachingLeft n k) (attachingRight n k)

def doubleCollapse (n k : ℕ) : doubleSpace n k ⟶ TopCat.of (Space n k) :=
  DoubleMappingCylinder.collapse (attachingLeft n k) (attachingRight n k) (attachingSquare n k)

theorem exists_double_equiv (n k : ℕ) :
    ∃ E : ContinuousMap.HomotopyEquiv (doubleSpace n k) (Space n k),
      E.toFun = (doubleCollapse n k).hom :=
  DoubleMappingCylinder.exists_collapse_equiv (attachingLeft n k) (attachingRight n k)
    (attachingSquare n k) (attachingLeft_hasHomotopyExtension n k)

instance (n k : ℕ) : ContractibleSpace (doubleSpace n k) := by
  obtain ⟨E, _⟩ := exists_double_equiv n k
  exact E.contractibleSpace

theorem doubleCollapse_left (n k : ℕ) :
    DoubleMappingCylinder.left (attachingLeft n k) (attachingRight n k) ≫ doubleCollapse n k =
      TopCat.ofHom (quotientMap n k) :=
  DoubleMappingCylinder.left_collapse (attachingLeft n k) (attachingRight n k) (attachingSquare n k)

theorem doubleCollapse_right (n k : ℕ) :
    DoubleMappingCylinder.right (attachingLeft n k) (attachingRight n k) ≫ doubleCollapse n k =
      TopCat.ofHom (words n k) :=
  DoubleMappingCylinder.right_collapse (attachingLeft n k) (attachingRight n k)
    (attachingSquare n k)

end NoExoticSixSphere.JamesSphere.ConeStage
