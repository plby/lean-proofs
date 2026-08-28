import Wikipedia.NoExoticSixSphere.MinimumPolygonRetraction
import Wikipedia.NoExoticSixSphere.CompactEnergyBand
import Wikipedia.NoExoticSixSphere.OrthogonalSupportedBandDeformation

/-!
# A near-minimum energy sublevel admits the actual retraction

Compactness puts a whole small sublevel in the retraction's open domain. This
gives a continuous map to the exact minimum locus fixing that locus. A homotopy
from the inclusion to this map is a separate requirement, not asserted here.
-/

open Set

namespace NoExoticSixSphere.OrthogonalPolygon

open GLOrthonormalization CayleyTransform OrthogonalExponential OrthogonalVertexSpace
  FiniteControlledLowering

variable {n m : ℕ}
variable (a b : OrthogonalOperators n) (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (hanti : (a⁻¹ * b).1.1 = -(1 : Vector n →L[ℝ] Vector n))
    (hsmall : ∀ J : OrthogonalComplexStructures.Space n, ∀ i : Fin (m + 1),
      (τ i.succ - τ i.castSucc) • (Real.pi • J.1) ∈ (logarithmChart n).target)
    (cap : ℝ) (hcap : (n : ℝ) * Real.pi ^ 2 < cap)
    (hcompact : IsCompact (energySublevel a b τ cap))

include hτ hzero hone hanti hsmall hcap hcompact

omit hsmall in
theorem exists_near_minimum_sublevel_in_open (U : Set (Space n m))
    (hU : IsOpen U) (hminU : minimumSet a b τ ⊆ U) :
    ∃ δ > 0, (n : ℝ) * Real.pi ^ 2 + δ < cap ∧
      energySublevel a b τ ((n : ℝ) * Real.pi ^ 2 + δ) ⊆ U := by
  obtain ⟨d, hd, hband⟩ := exists_energy_band_in_open (energy a b τ)
    (energySublevel a b τ cap) hcompact
    ((contMDiffOn_energy a b τ).continuousOn.mono (fun _ hv ↦ hv.1))
    ((n : ℝ) * Real.pi ^ 2) U hU (fun _ hv he ↦ hminU ⟨hv.1, he⟩)
  let δ := min (d / 2) ((cap - (n : ℝ) * Real.pi ^ 2) / 2)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδd : δ ≤ d / 2 := min_le_left _ _
  have hδcap : δ ≤ (cap - (n : ℝ) * Real.pi ^ 2) / 2 := min_le_right _ _
  have htop : (n : ℝ) * Real.pi ^ 2 + δ < cap := by linarith
  refine ⟨δ, hδ, htop, ?_⟩
  intro v hv
  have hvcap : v ∈ energySublevel a b τ cap := ⟨hv.1, hv.2.trans htop.le⟩
  have hlow := antipodal_energy_ge_of_compact_sublevel a b τ hτ hzero hone cap
    hcompact hanti v hvcap
  apply hband v hvcap
  rw [abs_of_nonneg (sub_nonneg.mpr hlow)]
  have := hv.2
  linarith

theorem exists_sublevel_in_minimumRetractionDomain :
    ∃ δ > 0, (n : ℝ) * Real.pi ^ 2 + δ < cap ∧
      energySublevel a b τ ((n : ℝ) * Real.pi ^ 2 + δ) ⊆ minimumRetractionDomain a b τ :=
  exists_near_minimum_sublevel_in_open a b τ hτ hzero hone hanti cap hcap hcompact
    (minimumRetractionDomain a b τ) (isOpen_minimumRetractionDomain a b τ)
    (minimumSet_subset_retractionDomain a b τ hτ hzero hone hanti hsmall
      (isCompact_energySublevel_of_le a b τ hcap.le hcompact))

theorem exists_near_minimum_retraction :
    ∃ δ > 0, (n : ℝ) * Real.pi ^ 2 + δ < cap ∧
      ∃ r : C(energySublevel a b τ ((n : ℝ) * Real.pi ^ 2 + δ), minimumSet a b τ),
        ∀ v : minimumSet a b τ, ∀ hv : v.1 ∈ energySublevel a b τ ((n : ℝ) * Real.pi ^ 2 + δ),
          r ⟨v.1, hv⟩ = v := by
  obtain ⟨δ, hδ, htop, hsub⟩ := exists_sublevel_in_minimumRetractionDomain
    a b τ hτ hzero hone hanti hsmall cap hcap hcompact
  let incl : C(energySublevel a b τ ((n : ℝ) * Real.pi ^ 2 + δ),
      minimumRetractionDomain a b τ) :=
    ⟨fun v ↦ ⟨v.1, hsub v.2⟩, continuous_subtype_val.subtype_mk _⟩
  refine ⟨δ, hδ, htop,
    (minimumNeighborhoodRetraction a b τ hτ hzero hone hanti hsmall).comp incl, ?_⟩
  intro v hv
  exact minimumNeighborhoodRetraction_eq_self a b τ hτ hzero hone hanti hsmall
    (isCompact_energySublevel_of_le a b τ hcap.le hcompact) v

end NoExoticSixSphere.OrthogonalPolygon
