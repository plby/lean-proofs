import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSecondMinimumPolygonSpace
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicAnticommutingRetraction

/-!
# A neighborhood retraction onto minimum complex-structure polygons

The first edge logarithm, scaled by its time length and `π`, is an
anticommuting direction at the starting structure. Polar normalization
recovers its unit generator; multiplication by the starting structure gives
the original midpoint parameter. Resampling gives an actual retraction.
-/

noncomputable section

open Set

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.ComplexStructurePolygon

open NoExoticSixSphere.GLOrthonormalization ComplexStructures ComplexStructureVertices

variable {n m : ℕ}

def initialCoordinate (a b : ComplexStructures.Space n) (τ : Fin (m + 2) → ℝ)
    (v : ComplexStructureVertices.Space n m) : SkewSpace n :=
  (((τ (0 : Fin (m + 1)).succ - τ 0) * Real.pi)⁻¹ : ℝ) • generator a b v 0

theorem continuousOn_initialCoordinate (a b : ComplexStructures.Space n) (τ : Fin (m + 2) → ℝ) :
    ContinuousOn (initialCoordinate a b τ) (admissible a b m) := by
  have h : ContinuousOn (fun v : ComplexStructureVertices.Space n m ↦
      Polygon.generator (toSymplectic a) (toSymplectic b) (forget v) (0 : Fin (m + 1)))
      (admissible a b m) :=
    (Polygon.contMDiffOn_generator (toSymplectic a) (toSymplectic b)
      (0 : Fin (m + 1))).continuousOn.comp
      (continuous_forget (n := n) (m := m)).continuousOn (fun _ hv ↦ admissible_forget a b hv)
  have hg : ContinuousOn (fun v : ComplexStructureVertices.Space n m ↦ generator a b v 0)
      (admissible a b m) := h.congr (fun v _ ↦ (generator_forget a b v 0).symm)
  exact hg.const_smul ((((τ (0 : Fin (m + 1)).succ - τ 0) * Real.pi)⁻¹) : ℝ)

theorem initialCoordinate_mem_anti (a b : ComplexStructures.Space n) (τ : Fin (m + 2) → ℝ)
    {v : ComplexStructureVertices.Space n m} (hv : v ∈ admissible a b m) :
    (initialCoordinate a b τ v).val ∈ antiSkewSubmodule a := by
  have hg : (generator a b v 0).val ∈ antiSkewSubmodule a :=
    ⟨(generator a b v 0).property, ShortLog.generator_anticommute (hv 0)⟩
  rw [initialCoordinate, Submodule.coe_smul]
  exact (antiSkewSubmodule a).smul_mem _ hg

def minimumRetractionDomain (a b : ComplexStructures.Space n) (τ : Fin (m + 2) → ℝ) :
    Set (ComplexStructureVertices.Space n m) :=
  admissible a b m ∩ initialCoordinate a b τ ⁻¹' ComplexStructures.normalizationDomain n

theorem isOpen_minimumRetractionDomain (a b : ComplexStructures.Space n) (τ : Fin (m + 2) → ℝ) :
    IsOpen (minimumRetractionDomain a b τ) :=
  (continuousOn_initialCoordinate a b τ).isOpen_inter_preimage
    (isOpen_admissible a b m) (ComplexStructures.isOpen_normalizationDomain n)

def nearbyGenerator (a b : ComplexStructures.Space n) (τ : Fin (m + 2) → ℝ) :
    C(minimumRetractionDomain a b τ, AnticommutingStructures.Space a) :=
  (AnticommutingStructures.neighborhoodRetraction a).comp {
    toFun v := ⟨⟨(initialCoordinate a b τ v.val).val,
      initialCoordinate_mem_anti a b τ v.property.1⟩, v.property.2⟩
    continuous_toFun := by
      have hc : Continuous (fun v : minimumRetractionDomain a b τ ↦
          initialCoordinate a b τ v.val) :=
        ((continuousOn_initialCoordinate a b τ).mono inter_subset_left).domRestrict
      have hop : Continuous (fun v : minimumRetractionDomain a b τ ↦
          (initialCoordinate a b τ v.val).val) := continuous_subtype_val.comp hc
      exact (hop.subtype_mk _).subtype_mk _ }

def nearbyParameter (a b : ComplexStructures.Space n) (τ : Fin (m + 2) → ℝ) :
    C(minimumRetractionDomain a b τ, AnticommutingStructures.Space a) :=
  ⟨fun v ↦ AnticommutingStructures.midpointParameter (nearbyGenerator a b τ v),
    AnticommutingStructures.continuous_midpointParameter.comp (nearbyGenerator a b τ).continuous⟩

variable (a b : ComplexStructures.Space n) (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (hanti : (Cayley.relative a b).val.val.val =
      -(1 : Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)))
    (hsmall : ∀ P : AnticommutingStructures.Space a, ∀ i : Fin (m + 1),
      ‖(τ i.succ - τ i.castSucc) •
        (Real.pi • (AnticommutingStructures.generatorParameter P).val.val)‖ < ShortLog.radius n)

include hτ hzero hone hanti hsmall

theorem initialCoordinate_rotation (P : AnticommutingStructures.Space a) :
    initialCoordinate a b τ (rotationVertices τ P) =
      (AnticommutingStructures.generatorParameter P).val.val := by
  have hδ : τ (0 : Fin (m + 1)).succ - τ (0 : Fin (m + 1)).castSucc ≠ 0 :=
    sub_ne_zero.mpr
      (hτ (show (0 : Fin (m + 1)).castSucc < (0 : Fin (m + 1)).succ by simp)).ne'
  rw [initialCoordinate, generator_rotationVertices a b τ hzero hone hanti P (hsmall P)]
  change (((τ (0 : Fin (m + 1)).succ - τ (0 : Fin (m + 1)).castSucc) * Real.pi)⁻¹ : ℝ) •
    ((τ (0 : Fin (m + 1)).succ - τ (0 : Fin (m + 1)).castSucc) •
      (Real.pi • (AnticommutingStructures.generatorParameter P).val.val)) = _
  simp only [smul_smul, inv_mul_cancel₀ (mul_ne_zero hδ Real.pi_ne_zero), one_smul]

theorem rotation_mem_minimumRetractionDomain (P : AnticommutingStructures.Space a) :
    rotationVertices τ P ∈ minimumRetractionDomain a b τ := by
  refine ⟨rotationVertices_admissible a b τ hzero hone hanti P (hsmall P), ?_⟩
  change initialCoordinate a b τ (rotationVertices τ P) ∈ ComplexStructures.normalizationDomain n
  rw [initialCoordinate_rotation a b τ hτ hzero hone hanti hsmall]
  exact ComplexStructures.mem_normalizationDomain (AnticommutingStructures.generatorParameter P).val

theorem nearbyGenerator_rotation (P : AnticommutingStructures.Space a) :
    nearbyGenerator a b τ ⟨rotationVertices τ P,
      rotation_mem_minimumRetractionDomain a b τ hτ hzero hone hanti hsmall P⟩ =
        AnticommutingStructures.generatorParameter P := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  change ComplexStructures.normalizationOperator
    (initialCoordinate a b τ (rotationVertices τ P)) = _
  rw [initialCoordinate_rotation a b τ hτ hzero hone hanti hsmall]
  exact ComplexStructures.normalizationOperator_of_complexStructure
    (AnticommutingStructures.generatorParameter P).val

theorem nearbyParameter_rotation (P : AnticommutingStructures.Space a) :
    nearbyParameter a b τ ⟨rotationVertices τ P,
      rotation_mem_minimumRetractionDomain a b τ hτ hzero hone hanti hsmall P⟩ = P := by
  change AnticommutingStructures.midpointParameter (nearbyGenerator a b τ _) = P
  rw [nearbyGenerator_rotation a b τ hτ hzero hone hanti hsmall P,
    AnticommutingStructures.midpoint_generator]

def minimumNeighborhoodRetraction : C(minimumRetractionDomain a b τ, minimumSet a b τ) :=
  (minimumParametrization a b τ hτ hzero hone hanti hsmall).comp (nearbyParameter a b τ)

variable (hcompact : IsCompact (energySublevel a b τ (((4 * n + 4 : ℕ) : ℝ) * Real.pi ^ 2)))

include hcompact

theorem minimumSet_subset_retractionDomain : minimumSet a b τ ⊆ minimumRetractionDomain a b τ := by
  intro v hv
  obtain ⟨P, hP⟩ := minimumParametrization_surjective
    a b τ hτ hzero hone hanti hsmall hcompact ⟨v, hv⟩
  have he : rotationVertices τ P = v := congrArg Subtype.val hP
  rw [← he]
  exact rotation_mem_minimumRetractionDomain a b τ hτ hzero hone hanti hsmall P

theorem minimumNeighborhoodRetraction_eq_self (v : minimumSet a b τ) :
    minimumNeighborhoodRetraction a b τ hτ hzero hone hanti hsmall
      ⟨v.val, minimumSet_subset_retractionDomain
        a b τ hτ hzero hone hanti hsmall hcompact v.property⟩ =
        v := by
  obtain ⟨P, rfl⟩ := minimumParametrization_surjective a b τ hτ hzero hone hanti hsmall hcompact v
  change minimumParametrization a b τ hτ hzero hone hanti hsmall
    (nearbyParameter a b τ ⟨rotationVertices τ P, _⟩) = _
  rw [nearbyParameter_rotation a b τ hτ hzero hone hanti hsmall P]

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.ComplexStructurePolygon
