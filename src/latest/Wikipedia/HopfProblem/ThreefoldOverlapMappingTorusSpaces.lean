import Wikipedia.HopfProblem.ThreefoldOverlapMappingTorusEllipticSpecial
import Wikipedia.HopfProblem.ThreefoldOverlapMappingTorusCuspSpecial

/-!
# Mapping-torus models of all three literal global overlaps

The equivalences below apply to the actual intersections in the glued
threefold.  The maps to the regular family and original fillings are the
literal maps from the global Mayer--Vietoris cover, composed with the
constructed boundary inclusions.  The inverse comparisons retain these
maps up to the displayed genuine homotopies.
-/

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace Wikipedia.HopfProblem.ThreefoldOverlapMappingTorus

open SpecialPeriods SpecialPeriods.Threefold SpecialPeriods.Threefold.Homology

/-- The actual boundary homeomorphisms, including both elliptic affine twists. -/
def monodromy : Puncture → (RealTorus₄ ≃ₜ RealTorus₄)
  | none => Cusp.monodromy
  | some j => Wikipedia.HopfProblem.Elliptic.flatTorusAffine j j.twist

/-- Each boundary is the literal integer-orbit mapping torus of its real-period fibre. -/
abbrev Boundary (i : Puncture) := MappingTorus.Torus (monodromy i)

/-- The actual original punctured pieces have their proved boundary models. -/
def pieceMappingTorusHomotopyEquiv (i : Puncture) : PuncturedPiece i ≃ₕ Boundary i := by
  cases i with
  | none => exact Cusp.specialMappingTorusHomotopyEquiv
  | some j => exact Elliptic.specialMappingTorusHomotopyEquiv j

/-- All three actual global regular/filling intersections are homotopy equivalent
to their original rank-four affine mapping tori. -/
def overlapMappingTorusHomotopyEquiv (i : Puncture) : RegularOverlap i ≃ₕ Boundary i :=
  (overlapPieceHomeomorph i).toHomotopyEquiv.trans (pieceMappingTorusHomotopyEquiv i)

/-- The actual boundary inclusion in the literal global intersection. -/
def boundaryToOverlap (i : Puncture) : C(Boundary i, RegularOverlap i) :=
  ⟨(overlapMappingTorusHomotopyEquiv i).symm,
    (overlapMappingTorusHomotopyEquiv i).symm.continuous⟩

/-- The genuine regular-family coefficient map used in the attachment sequence. -/
def boundaryToRegularFamily (i : Puncture) : C(Boundary i, SpecialRegularFamily) :=
  (overlapToRegularFamily i).comp (boundaryToOverlap i)

/-- The genuine filling coefficient map used in the attachment sequence. -/
def boundaryToFilling (i : Puncture) : C(Boundary i, localPiece (some i)) :=
  (overlapToFilling i).comp (boundaryToOverlap i)

theorem boundaryToRegularFamily_ambient (i : Puncture) (x : Boundary i) :
    inclusion none (boundaryToRegularFamily i x) = (boundaryToOverlap i x).val :=
  inclusion_overlapToRegularFamily i (boundaryToOverlap i x)

theorem boundaryToFilling_ambient (i : Puncture) (x : Boundary i) :
    inclusion (some i) (boundaryToFilling i x) = (boundaryToOverlap i x).val :=
  inclusion_overlapToFilling i (boundaryToOverlap i x)

/-- Both boundary maps are identified by the original gluing, on every point. -/
theorem boundary_maps_agree (i : Puncture) :
    originalRegularInclusion.comp (boundaryToRegularFamily i) =
      (originalPieceInclusion (some i)).comp (boundaryToFilling i) := by
  apply ContinuousMap.ext
  intro x
  exact (boundaryToRegularFamily_ambient i x).trans (boundaryToFilling_ambient i x).symm

@[simp] theorem boundaryToOverlap_cusp_piece (x : Boundary none) :
    overlapPieceHomeomorph none (boundaryToOverlap none x) =
      Cusp.specialBoundaryInclusion x :=
  (overlapPieceHomeomorph none).apply_symm_apply _

@[simp] theorem boundaryToOverlap_elliptic_piece (j : Wikipedia.HopfProblem.Elliptic.Kind)
    (x : Boundary (some j)) :
    overlapPieceHomeomorph (some j) (boundaryToOverlap (some j) x) =
      Elliptic.specialBoundaryInclusion j x :=
  (overlapPieceHomeomorph (some j)).apply_symm_apply _

/-- The cusp coefficient is exactly the previously constructed original cusp map. -/
theorem boundaryToFilling_cusp : boundaryToFilling none = Cusp.specialBoundaryToPiece := by
  apply ContinuousMap.ext
  intro x
  exact congrArg Subtype.val (boundaryToOverlap_cusp_piece x)

/-- The elliptic coefficients are exactly the original affine filling maps. -/
theorem boundaryToFilling_elliptic (j : Wikipedia.HopfProblem.Elliptic.Kind) :
    boundaryToFilling (some j) = Elliptic.specialBoundaryToPiece j := by
  apply ContinuousMap.ext
  intro x
  exact congrArg Subtype.val (boundaryToOverlap_elliptic_piece j x)

/-- The actual overlap retraction, retaining its original source. -/
def overlapRetraction (i : Puncture) : C(RegularOverlap i, Boundary i) :=
  ⟨overlapMappingTorusHomotopyEquiv i, (overlapMappingTorusHomotopyEquiv i).continuous⟩

theorem boundary_overlap_retraction_homotopic (i : Puncture) :
    ((boundaryToOverlap i).comp (overlapRetraction i)).Homotopic (ContinuousMap.id _) :=
  (overlapMappingTorusHomotopyEquiv i).left_inv

/-- Replacing the full overlap by its boundary preserves the actual regular map
up to the constructed radial homotopy. -/
theorem boundary_regular_retraction_homotopic (i : Puncture) :
    ((boundaryToRegularFamily i).comp (overlapRetraction i)).Homotopic
      (overlapToRegularFamily i) := by
  simpa only [boundaryToRegularFamily, ContinuousMap.comp_assoc, ContinuousMap.comp_id] using
    (ContinuousMap.Homotopic.refl (overlapToRegularFamily i)).comp
      (boundary_overlap_retraction_homotopic i)

/-- The same radial homotopy preserves the original filling coefficient. -/
theorem boundary_filling_retraction_homotopic (i : Puncture) :
    ((boundaryToFilling i).comp (overlapRetraction i)).Homotopic
      (overlapToFilling i) := by
  simpa only [boundaryToFilling, ContinuousMap.comp_assoc, ContinuousMap.comp_id] using
    (ContinuousMap.Homotopic.refl (overlapToFilling i)).comp
      (boundary_overlap_retraction_homotopic i)

/-- The rank-four boundary fibre, with its actual original regular-family map. -/
def fibreToRegularFamily (i : Puncture) : C(RealTorus₄, SpecialRegularFamily) :=
  (boundaryToRegularFamily i).comp (MappingTorus.HomologyCover.fibreInclusion (monodromy i))

/-- The same actual fibre with values in the original filling piece. -/
def fibreToFilling (i : Puncture) : C(RealTorus₄, localPiece (some i)) :=
  (boundaryToFilling i).comp (MappingTorus.HomologyCover.fibreInclusion (monodromy i))

end Wikipedia.HopfProblem.ThreefoldOverlapMappingTorus
