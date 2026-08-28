import Wikipedia.HopfProblem.DegreeCollapseTimeCollarComplementPair
import Wikipedia.HopfProblem.DegreeCollapseIntegralNonnegativePair

/-!
# The original relative exterior inclusion for a collared surgery pair

The whole attaching core is positive and compact. The actual half-to-ambient
core-complement map is therefore a relative homology isomorphism. The two
original radial exterior deformations transfer this to the literal closed
exterior ranges. Neither homology nor simple connectivity is assumed.
-/

noncomputable section

open Function Set ContinuousMap

namespace Wikipedia.HopfProblem.DegreeCollapse.TimeCollar

open NoExoticSixSphere SingularMayerVietoris Wikipedia.SmoothSixDPoincare
open RelativeSingularHomology NonnegativeSurgeryPair

variable {M B E F R Y : Type} [TopologicalSpace M] [T2Space M] [TopologicalSpace B]
  [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace R] [TopologicalSpace Y] [CompactSpace (PuncturedHandle.UnitSphere E)]
  {t : M → ℝ} (C : TimeCollar t B) (P : SurgeryBoundaryPair E F R M Y) (ty : Y → ℝ)
  (hold : ∀ p, 0 ≤ t (P.oldPiece p)) (hnew : ∀ p, 0 ≤ ty (P.newPiece p))
  (hext : ∀ r, 0 ≤ t (P.oldExterior r) ↔ 0 ≤ ty (P.newExterior r))
  (hcore : ∀ s, 0 < t (P.attachingSphere s))

include C hcore in
theorem halfCoreComplement_relative_bijective (k : ℕ) :
    Bijective (RelativeSingularHomology.map (subtypeInclusion {x : M | 0 ≤ t x})
      (complement_inclusion_mapsTo P t ty C.continuous_time hold hnew hext) k) := by
  have hK : ∀ p ∈ range P.attachingSphere, 0 < t p := by
    rintro p ⟨s, rfl⟩
    exact hcore s
  have hclosed : IsClosed (range P.attachingSphere) :=
    (isCompact_range P.attachingSphere.continuous).isClosed
  have hh := C.halfInclusion_relative_bijective (range P.attachingSphere) hK hclosed k
  have transfer (Q : Set (NonnegativeHalf t))
      (hQ : Q = C.halfComplement (range P.attachingSphere))
      (hf : MapsTo (halfInclusion t) Q P.OldComplement) :
      Bijective (RelativeSingularHomology.map (halfInclusion t) hf k) := by
    subst Q
    exact hh
  exact transfer _ (complement_eq_preimage P t ty C.continuous_time hold hnew hext) _

include C hcore in
theorem halfExterior_relative_bijective (k : ℕ) :
    Bijective (relativeExteriorInclusion P t ty C.continuous_time hold hnew hext k) :=
  relativeExteriorInclusion_bijective_of_complement P t ty C.continuous_time hold hnew hext k
    (C.halfCoreComplement_relative_bijective P ty hold hnew hext hcore k)

end Wikipedia.HopfProblem.DegreeCollapse.TimeCollar
