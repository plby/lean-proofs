import Wikipedia.HopfProblem.DegreeCollapseIntegralSurgeryComplementPair
import Wikipedia.HopfProblem.DegreeCollapseNonnegativeSurgeryPair

/-!
# Original relative maps for a surgery and its nonnegative half

The half exterior and half core are the actual restrictions of the original
maps. Their relative maps commute with enlargement to the core complements.
Consequently an isomorphism for the original core-complement pairs gives an
isomorphism for the original closed-exterior pairs, without changing maps.
-/

noncomputable section

open Function Set ContinuousMap

namespace Wikipedia.HopfProblem.DegreeCollapse.NonnegativeSurgeryPair

open Wikipedia.SmoothSixDPoincare NoExoticSixSphere.RelativeSingularHomology
open SingularMayerVietoris SurgeryExteriorRetraction

variable {E F R X Y : Type} [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [TopologicalSpace R] [TopologicalSpace X] [TopologicalSpace Y]
  (d : SurgeryBoundaryPair E F R X Y) (tx : X → ℝ) (ty : Y → ℝ)
  (hx : Continuous tx) (hold : ∀ p, 0 ≤ tx (d.oldPiece p))
  (hnew : ∀ p, 0 ≤ ty (d.newPiece p))
  (hext : ∀ r, 0 ≤ tx (d.oldExterior r) ↔ 0 ≤ ty (d.newExterior r))

omit [NormedSpace ℝ F] in
theorem exterior_inclusion_mapsTo :
    MapsTo (subtypeInclusion {x : X | 0 ≤ tx x})
      (range (pair d tx ty hx hold hnew hext).oldExterior) (range d.oldExterior) := by
  rintro x ⟨r, rfl⟩
  exact ⟨r.val, rfl⟩

omit [NormedSpace ℝ F] in
theorem complement_eq_preimage :
    (pair d tx ty hx hold hnew hext).OldComplement =
      Subtype.val ⁻¹' d.OldComplement := by
  ext x
  change (¬ ∃ s, (pair d tx ty hx hold hnew hext).attachingSphere s = x) ↔
    ¬ ∃ s, d.attachingSphere s = x.val
  apply not_congr
  constructor
  · rintro ⟨s, hs⟩
    exact ⟨s, congrArg (fun x : {x : X // 0 ≤ tx x} ↦ x.val) hs⟩
  · rintro ⟨s, hs⟩
    exact ⟨s, Subtype.ext hs⟩

omit [NormedSpace ℝ F] in
theorem complement_inclusion_mapsTo :
    MapsTo (subtypeInclusion {x : X | 0 ≤ tx x})
      (pair d tx ty hx hold hnew hext).OldComplement d.OldComplement := by
  intro x hx'
  exact (Set.ext_iff.mp (complement_eq_preimage d tx ty hx hold hnew hext) x).mp hx'

abbrev relativeExteriorInclusion (k : ℕ) :
    Homology (range (pair d tx ty hx hold hnew hext).oldExterior) k →ₗ[ℤ]
      Homology (range d.oldExterior) k :=
  map (subtypeInclusion {x : X | 0 ≤ tx x})
    (exterior_inclusion_mapsTo d tx ty hx hold hnew hext) k

omit [NormedSpace ℝ F] in
theorem relativeExteriorInclusion_square (k : ℕ) :
    (exteriorToComplement d k).comp (relativeExteriorInclusion d tx ty hx hold hnew hext k) =
      (map (subtypeInclusion {x : X | 0 ≤ tx x})
        (complement_inclusion_mapsTo d tx ty hx hold hnew hext) k).comp
          (exteriorToComplement (pair d tx ty hx hold hnew hext) k) := by
  exact (map_comp (subtypeInclusion {x : X | 0 ≤ tx x})
    (exterior_inclusion_mapsTo d tx ty hx hold hnew hext)
    (ContinuousMap.id X) (exteriorRange_subset_complement d) k).symm.trans
      (map_comp (ContinuousMap.id {x : X | 0 ≤ tx x})
        (exteriorRange_subset_complement (pair d tx ty hx hold hnew hext))
        (subtypeInclusion {x : X | 0 ≤ tx x})
        (complement_inclusion_mapsTo d tx ty hx hold hnew hext) k)

theorem relativeExteriorInclusion_bijective_of_complement (k : ℕ)
    (hc : Bijective (map (subtypeInclusion {x : X | 0 ≤ tx x})
      (complement_inclusion_mapsTo d tx ty hx hold hnew hext) k)) :
    Bijective (relativeExteriorInclusion d tx ty hx hold hnew hext k) := by
  have hg := exteriorToComplement_bijective d k
  have hcomp : Bijective ((exteriorToComplement d k).comp
      (relativeExteriorInclusion d tx ty hx hold hnew hext k)) := by
    rw [relativeExteriorInclusion_square]
    exact hc.comp (exteriorToComplement_bijective (pair d tx ty hx hold hnew hext) k)
  constructor
  · intro x y hxy
    exact hcomp.1 (congrArg (exteriorToComplement d k) hxy)
  · intro y
    obtain ⟨x, hx'⟩ := hcomp.2 (exteriorToComplement d k y)
    exact ⟨x, hg.1 hx'⟩

end Wikipedia.HopfProblem.DegreeCollapse.NonnegativeSurgeryPair
