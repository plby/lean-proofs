import Wikipedia.HomotopyGroupsOfSpheres.BalancedMinimumPolygonSpace
import Wikipedia.HomotopyGroupsOfSpheres.BalancedRealRetraction

/-!
# An actual neighborhood retraction onto minimum constrained polygons

The first edge logarithm, divided by its time length and by π, recovers a
real symmetric matrix. On the open normalization domain its polar part is
a balanced involution. Resampling this involution fixes every minimum
polygon exactly.
-/

noncomputable section

open scoped Matrix.Norms.Frobenius
open Set

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices.Polygon

open VertexSpace BalancedRealInvolutions ComplexSkewMatrices

variable {m : ℕ}

def initialCoordinate (n : ℕ) (τ : Fin (m + 2) → ℝ)
    (v : VertexSpace.Space (Index n) m) : Matrix (Index n) (Index n) ℝ :=
  (((τ (0 : Fin (m + 1)).succ - τ 0) * Real.pi)⁻¹ : ℝ) •
    LocalLogarithm.imaginaryPart (generator specialIdentity (antipode n) v 0).val

theorem continuousOn_initialCoordinate (n : ℕ) (τ : Fin (m + 2) → ℝ) :
    ContinuousOn (initialCoordinate n τ) (admissible specialIdentity (antipode n) m) := by
  have hg : ContinuousOn (fun v : VertexSpace.Space (Index n) m ↦
      generator specialIdentity (antipode n) v 0) (admissible specialIdentity (antipode n) m) :=
    continuousOn_iff_continuous_domRestrict.mpr
      (continuous_generator specialIdentity (antipode n) 0)
  have him : Continuous (LocalLogarithm.imaginaryPart (N := Index n)) :=
    (finiteLinearMap_contDiff (LocalLogarithm.imaginaryPart (N := Index n))).continuous
  exact (him.comp_continuousOn (continuous_subtype_val.comp_continuousOn hg)).const_smul
    ((((τ (0 : Fin (m + 1)).succ - τ 0) * Real.pi)⁻¹) : ℝ)

theorem initialCoordinate_symmetric (n : ℕ) (τ : Fin (m + 2) → ℝ)
    {v : VertexSpace.Space (Index n) m} (hv : v ∈ admissible specialIdentity (antipode n) m) :
    (initialCoordinate n τ v).transpose = initialCoordinate n τ v := by
  have hs := ShortLog.generator_reversible (hv 0)
  change (generator specialIdentity (antipode n) v 0).val.transpose * 1 =
    1 * (generator specialIdentity (antipode n) v 0).val at hs
  simp only [mul_one, one_mul] at hs
  rw [initialCoordinate, Matrix.transpose_smul]
  exact congrArg (fun A : Matrix (Index n) (Index n) ℝ ↦
    (((τ (0 : Fin (m + 1)).succ - τ 0) * Real.pi)⁻¹ : ℝ) • A)
      (ImaginarySymmetricMatrices.map_im_transpose _ hs)

def minimumRetractionDomain (n : ℕ) (τ : Fin (m + 2) → ℝ) :
    Set (VertexSpace.Space (Index n) m) :=
  admissible specialIdentity (antipode n) m ∩
    initialCoordinate n τ ⁻¹' BalancedRealInvolutions.normalizationDomain n

theorem isOpen_minimumRetractionDomain (n : ℕ) (τ : Fin (m + 2) → ℝ) :
    IsOpen (minimumRetractionDomain n τ) :=
  (continuousOn_initialCoordinate n τ).isOpen_inter_preimage
    (isOpen_admissible specialIdentity (antipode n) m)
    (BalancedRealInvolutions.isOpen_normalizationDomain n)

def nearbyParameter (n : ℕ) (τ : Fin (m + 2) → ℝ) :
    C(minimumRetractionDomain n τ, BalancedRealInvolutions.Space n) :=
  (BalancedRealInvolutions.neighborhoodRetraction n).comp {
    toFun v := ⟨initialCoordinate n τ v.val, initialCoordinate_symmetric n τ v.property.1,
      v.property.2⟩
    continuous_toFun :=
      ((continuousOn_initialCoordinate n τ).mono inter_subset_left).domRestrict.subtype_mk _ }

variable (n : ℕ) (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ)
    (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (hsmall : ∀ J : BalancedRealInvolutions.Space n, ∀ i : Fin (m + 1),
      ‖(τ i.succ - τ i.castSucc) • imaginaryDirection (minimumGenerator J)‖ <
        CompatibleLog.radius (Index n))

include hτ hzero hone hsmall

theorem initialCoordinate_rotation (J : BalancedRealInvolutions.Space n) :
    initialCoordinate n τ (rotationVertices τ J) = J.val := by
  have hδ : τ (0 : Fin (m + 1)).succ - τ (0 : Fin (m + 1)).castSucc ≠ 0 :=
    sub_ne_zero.mpr
      (hτ (show (0 : Fin (m + 1)).castSucc < (0 : Fin (m + 1)).succ by simp)).ne'
  rw [initialCoordinate, generator_rotationVertices τ hzero hone J (hsmall J)]
  change (((τ (0 : Fin (m + 1)).succ - τ (0 : Fin (m + 1)).castSucc) * Real.pi)⁻¹ : ℝ) •
    LocalLogarithm.imaginaryPart ((τ (0 : Fin (m + 1)).succ - τ (0 : Fin (m + 1)).castSucc) •
      ImaginarySymmetricMatrices.imaginary (minimumGenerator J).val) = J.val
  rw [map_smul, LocalLogarithm.imaginaryPart_imaginary]
  change (((τ (0 : Fin (m + 1)).succ - τ (0 : Fin (m + 1)).castSucc) * Real.pi)⁻¹ : ℝ) •
    ((τ (0 : Fin (m + 1)).succ - τ (0 : Fin (m + 1)).castSucc) • (Real.pi • J.val)) = J.val
  simp only [smul_smul, inv_mul_cancel₀ (mul_ne_zero hδ Real.pi_ne_zero), one_smul]

theorem rotation_mem_minimumRetractionDomain (J : BalancedRealInvolutions.Space n) :
    rotationVertices τ J ∈ minimumRetractionDomain n τ := by
  refine ⟨rotationVertices_admissible τ hzero hone J (hsmall J), ?_⟩
  change initialCoordinate n τ (rotationVertices τ J) ∈
    BalancedRealInvolutions.normalizationDomain n
  rw [initialCoordinate_rotation n τ hτ hzero hone hsmall]
  exact BalancedRealInvolutions.mem_normalizationDomain J

theorem nearbyParameter_rotation (J : BalancedRealInvolutions.Space n) :
    nearbyParameter n τ ⟨rotationVertices τ J,
      rotation_mem_minimumRetractionDomain n τ hτ hzero hone hsmall J⟩ = J := by
  apply Subtype.ext
  change normalizationMatrix (initialCoordinate n τ (rotationVertices τ J)) = J.val
  rw [initialCoordinate_rotation n τ hτ hzero hone hsmall]
  exact normalizationMatrix_of_involution J

def minimumNeighborhoodRetraction : C(minimumRetractionDomain n τ, minimumSet n τ) :=
  (minimumParametrization n τ hτ hzero hone hsmall).comp (nearbyParameter n τ)

variable (hcompact : IsCompact
  (energySublevel specialIdentity (antipode n) τ ((4 * n : ℝ) * Real.pi ^ 2)))

include hcompact

theorem minimumSet_subset_retractionDomain : minimumSet n τ ⊆ minimumRetractionDomain n τ := by
  intro v hv
  obtain ⟨J, hJ⟩ := minimumParametrization_surjective n τ hτ hzero hone hsmall hcompact ⟨v, hv⟩
  have he : rotationVertices τ J = v := congrArg Subtype.val hJ
  rw [← he]
  exact rotation_mem_minimumRetractionDomain n τ hτ hzero hone hsmall J

theorem minimumNeighborhoodRetraction_eq_self (v : minimumSet n τ) :
    minimumNeighborhoodRetraction n τ hτ hzero hone hsmall
      ⟨v.val, minimumSet_subset_retractionDomain n τ hτ hzero hone hsmall hcompact v.property⟩ =
        v := by
  obtain ⟨J, rfl⟩ := minimumParametrization_surjective n τ hτ hzero hone hsmall hcompact v
  change minimumParametrization n τ hτ hzero hone hsmall
    (nearbyParameter n τ ⟨rotationVertices τ J, _⟩) = _
  rw [nearbyParameter_rotation n τ hτ hzero hone hsmall J]

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices.Polygon
