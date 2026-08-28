import Wikipedia.NoExoticSixSphere.JamesSphereConeContraction
import Wikipedia.NoExoticSixSphere.QuotientAttachment
import Wikipedia.NoExoticSixSphere.SpherePointCofibration
import Wikipedia.NoExoticSixSphere.SubspaceCofibration
import Wikipedia.HopfProblem.OrbitPairIntervalBoundaryDeformation

/-!
# The actual reduced-cone boundary is a closed cofibration

The boundary pulls back under the cone presentation to the two interval
end faces together with the basepoint line. This is a product-boundary
cofibration. Its quotient attachment is the original cone-boundary
inclusion, so homotopy extension descends to that actual map.
-/

noncomputable section

open CategoryTheory Set Topology unitInterval
open Wikipedia.HopfProblem.OrbitPair

namespace NoExoticSixSphere.JamesSphere.ReducedCone

def faces (n : ℕ) : Set (Sphere n × I) :=
  {p | p.1 = spherePole n ∨ p.2 = 0 ∨ p.2 = 1}

theorem presentation_mem_boundary_iff (n : ℕ) (p : Sphere n × I) :
    presentation n p ∈ Set.range (boundary n) ↔ p ∈ faces n := by
  constructor
  · rintro ⟨x, hx⟩
    have he : prefixCurve n (x, 1) = prefixCurve n p := congrArg Subtype.val hx
    rcases (prefix_eq_iff n (x, 1) p).mp he with hp | ⟨_, hp⟩
    · exact Or.inr (Or.inr (congrArg Prod.snd hp).symm)
    · exact hp.elim Or.inl (fun hs ↦ Or.inr (Or.inl hs))
  · rintro (hx | hs | hs)
    · exact ⟨spherePole n, (boundary_pole n).trans
        ((presentation_eq_base_iff n p).mpr (Or.inl hx)).symm⟩
    · exact ⟨spherePole n, (boundary_pole n).trans
        ((presentation_eq_base_iff n p).mpr (Or.inr hs)).symm⟩
    · exact ⟨p.1, congrArg (presentation n) (Prod.ext rfl hs.symm)⟩

theorem presentation_preimage_boundary (n : ℕ) :
    presentation n ⁻¹' Set.range (boundary n) = faces n := by
  ext p
  exact presentation_mem_boundary_iff n p

theorem faces_eq_productBoundary (n : ℕ) : faces n =
    NeighborhoodProduct.boundary (MetricPointCofibration.inclusion (spherePole n))
      IntervalBoundary.inclusion := by
  ext p
  change (p.1 = spherePole n ∨ p.2 = 0 ∨ p.2 = 1) ↔
    p.1 ∈ Set.range (SubspaceCofibration.inclusion ({spherePole n} : Set (Sphere n))) ∨
      p.2 ∈ Set.range (SubspaceCofibration.inclusion IntervalBoundary.endpoints)
  rw [SubspaceCofibration.mem_range, SubspaceCofibration.mem_range]
  rfl

def facesData (n : ℕ) : NeighborhoodDeformation.Data (SubspaceCofibration.inclusion (faces n)) := by
  rw [faces_eq_productBoundary]
  exact NeighborhoodProduct.data (SpherePointCofibration.data (spherePole n)) IntervalBoundary.data

def presentationMorphism (n : ℕ) : TopCat.of (Sphere n × I) ⟶ TopCat.of (Space n) :=
  TopCat.ofHom (presentation n)

theorem presentation_fiber_condition (n : ℕ) (p q : Sphere n × I)
    (h : presentation n p = presentation n q) :
    presentation n p ∈ Set.range (boundary n) ∨ p = q := by
  rcases (prefix_eq_iff n p q).mp (congrArg Subtype.val h) with he | ⟨hp, _⟩
  · exact Or.inr he
  · left
    exact (presentation_mem_boundary_iff n p).mpr
      (hp.elim Or.inl (fun hs ↦ Or.inr (Or.inl hs)))

def boundaryRangeInclusion (n : ℕ) :
    TopCat.of (Set.range (boundary n)) ⟶ TopCat.of (Space n) :=
  QuotientAttachment.inclusion (Q := TopCat.of (Space n)) (Set.range (boundary n))

theorem boundaryRange_hasHomotopyExtension (n : ℕ) :
    HomotopyExtension.HasHomotopyExtension (boundaryRangeInclusion n) := by
  apply QuotientAttachment.hasHomotopyExtension (presentationMorphism n)
    (Set.range (boundary n)) (presentation_isQuotientMap n) (presentation_fiber_condition n)
  change HomotopyExtension.HasHomotopyExtension
    (SubspaceCofibration.inclusion (presentation n ⁻¹' Set.range (boundary n)))
  rw [presentation_preimage_boundary]
  exact SubspaceCofibration.hasHomotopyExtension (facesData n)

def boundaryHomeomorph (n : ℕ) : Sphere n ≃ₜ Set.range (boundary n) :=
  (boundary_isClosedEmbedding n).isEmbedding.toHomeomorph

def boundaryMorphism (n : ℕ) : TopCat.of (Sphere n) ⟶ TopCat.of (Space n) :=
  TopCat.ofHom (boundary n)

theorem boundary_factor (n : ℕ) : boundaryMorphism n =
    (TopCat.isoOfHomeo (boundaryHomeomorph n)).hom ≫ boundaryRangeInclusion n := rfl

theorem boundary_hasHomotopyExtension (n : ℕ) :
    HomotopyExtension.HasHomotopyExtension (boundaryMorphism n) := by
  rw [boundary_factor]
  exact HomotopyExtension.comp _ _ (HomotopyExtension.of_isIso _)
    (boundaryRange_hasHomotopyExtension n)

end NoExoticSixSphere.JamesSphere.ReducedCone
