import Wikipedia.NoExoticSixSphere.ComplexStructureRetraction
import Wikipedia.NoExoticSixSphere.OrthogonalMinimumPolygonSpace

/-!
# Retraction from a neighborhood onto the actual minimum polygon locus

The initial logarithmic generator recovers a complex structure on a minimum
polygon. Normalizing that generator and resampling the associated exponential
extends this recovery continuously to an open neighborhood of the minimum set.
-/

open Set

namespace NoExoticSixSphere.OrthogonalPolygon

open GLOrthonormalization CayleyTransform OrthogonalExponential OrthogonalVertexSpace

variable {n m : ℕ}

noncomputable def initialComplexCoordinate (a b : OrthogonalOperators n)
    (τ : Fin (m + 2) → ℝ) (v : Space n m) : SkewOperators n :=
  (((τ (0 : Fin (m + 1)).succ - τ (0 : Fin (m + 1)).castSucc) * Real.pi)⁻¹ : ℝ) •
    generator a b v 0

theorem continuousOn_initialComplexCoordinate (a b : OrthogonalOperators n)
    (τ : Fin (m + 2) → ℝ) :
    ContinuousOn (initialComplexCoordinate a b τ) (admissible a b m) := by
  unfold initialComplexCoordinate
  exact (contMDiffOn_generator a b (0 : Fin (m + 1))).continuousOn.const_smul
    (((τ (0 : Fin (m + 1)).succ - τ (0 : Fin (m + 1)).castSucc) * Real.pi)⁻¹ : ℝ)

def minimumRetractionDomain (a b : OrthogonalOperators n) (τ : Fin (m + 2) → ℝ) :
    Set (Space n m) :=
  admissible a b m ∩ initialComplexCoordinate a b τ ⁻¹'
    OrthogonalComplexStructures.normalizationDomain n

theorem isOpen_minimumRetractionDomain (a b : OrthogonalOperators n)
    (τ : Fin (m + 2) → ℝ) : IsOpen (minimumRetractionDomain a b τ) :=
  (continuousOn_initialComplexCoordinate a b τ).isOpen_inter_preimage
    (isOpen_admissible a b m) (OrthogonalComplexStructures.isOpen_normalizationDomain n)

noncomputable def nearbyComplexStructure (a b : OrthogonalOperators n)
    (τ : Fin (m + 2) → ℝ) :
    C(minimumRetractionDomain a b τ, OrthogonalComplexStructures.Space n) :=
  (OrthogonalComplexStructures.neighborhoodRetraction n).comp
    { toFun v := ⟨initialComplexCoordinate a b τ v.1, v.2.2⟩
      continuous_toFun := by
        exact ((continuousOn_initialComplexCoordinate a b τ).mono
          inter_subset_left).domRestrict.subtype_mk _ }

variable (a b : OrthogonalOperators n) (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (hanti : (a⁻¹ * b).1.1 = -(1 : Vector n →L[ℝ] Vector n))
    (hsmall : ∀ J : OrthogonalComplexStructures.Space n, ∀ i : Fin (m + 1),
      (τ i.succ - τ i.castSucc) • (Real.pi • J.1) ∈ (logarithmChart n).target)

include hτ hzero hone hanti hsmall

theorem initialComplexCoordinate_exponential (J : OrthogonalComplexStructures.Space n) :
    initialComplexCoordinate a b τ (exponentialVertices a τ (Real.pi • J.1)) = J.1 := by
  have hδ : τ (0 : Fin (m + 1)).succ - τ (0 : Fin (m + 1)).castSucc ≠ 0 :=
    sub_ne_zero.mpr (hτ (show (0 : Fin (m + 1)).castSucc < (0 : Fin (m + 1)).succ by simp)).ne'
  rw [initialComplexCoordinate, generator_exponentialVertices a b τ hzero hone _
    (complexStructure_endpoint a b hanti J) (hsmall J)]
  simp only [smul_smul, inv_mul_cancel₀ (mul_ne_zero hδ Real.pi_ne_zero), one_smul]

theorem exponential_mem_minimumRetractionDomain (J : OrthogonalComplexStructures.Space n) :
    exponentialVertices a τ (Real.pi • J.1) ∈ minimumRetractionDomain a b τ := by
  refine ⟨(exponentialVertices_mem_minimumSet a b τ hτ hzero hone hanti hsmall J).1, ?_⟩
  change initialComplexCoordinate a b τ (exponentialVertices a τ (Real.pi • J.1)) ∈
    OrthogonalComplexStructures.normalizationDomain n
  rw [initialComplexCoordinate_exponential a b τ hτ hzero hone hanti hsmall]
  exact OrthogonalComplexStructures.mem_normalizationDomain J

theorem nearbyComplexStructure_exponential (J : OrthogonalComplexStructures.Space n) :
    nearbyComplexStructure a b τ ⟨exponentialVertices a τ (Real.pi • J.1),
      exponential_mem_minimumRetractionDomain a b τ hτ hzero hone hanti hsmall J⟩ = J := by
  apply Subtype.ext
  apply Subtype.ext
  change OrthogonalComplexStructures.normalizationOperator
    (initialComplexCoordinate a b τ (exponentialVertices a τ (Real.pi • J.1))) = _
  rw [initialComplexCoordinate_exponential a b τ hτ hzero hone hanti hsmall]
  exact OrthogonalComplexStructures.normalizationOperator_of_complexStructure J

noncomputable def minimumNeighborhoodRetraction :
    C(minimumRetractionDomain a b τ, minimumSet a b τ) :=
  (minimumParametrization a b τ hτ hzero hone hanti hsmall).comp (nearbyComplexStructure a b τ)

variable (hcompact : IsCompact (energySublevel a b τ ((n : ℝ) * Real.pi ^ 2)))

include hcompact

theorem minimumSet_subset_retractionDomain : minimumSet a b τ ⊆ minimumRetractionDomain a b τ := by
  intro v hv
  obtain ⟨J, hJ⟩ := minimumParametrization_surjective
    a b τ hτ hzero hone hanti hsmall hcompact ⟨v, hv⟩
  have he : exponentialVertices a τ (Real.pi • J.1) = v := congrArg Subtype.val hJ
  rw [← he]
  exact exponential_mem_minimumRetractionDomain a b τ hτ hzero hone hanti hsmall J

theorem minimumNeighborhoodRetraction_eq_self (v : minimumSet a b τ) :
    minimumNeighborhoodRetraction a b τ hτ hzero hone hanti hsmall
      ⟨v.1, minimumSet_subset_retractionDomain
        a b τ hτ hzero hone hanti hsmall hcompact v.2⟩ = v := by
  obtain ⟨J, rfl⟩ := minimumParametrization_surjective a b τ hτ hzero hone hanti hsmall hcompact v
  change minimumParametrization a b τ hτ hzero hone hanti hsmall
    (nearbyComplexStructure a b τ ⟨exponentialVertices a τ (Real.pi • J.1), _⟩) = _
  rw [nearbyComplexStructure_exponential a b τ hτ hzero hone hanti hsmall]

end NoExoticSixSphere.OrthogonalPolygon
