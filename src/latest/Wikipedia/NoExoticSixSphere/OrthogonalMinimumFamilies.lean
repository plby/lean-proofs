import Wikipedia.NoExoticSixSphere.OrthogonalMinimumDeformation

/-!
# Deformation to a continuous family of minimum exponential polygons

The endpoint is expressed using a genuine continuous family of orthogonal
complex structures, via the proved minimum-locus homeomorphism.
-/

open Set Module
open scoped ContDiff Manifold Topology

namespace NoExoticSixSphere.OrthogonalPolygon

open GLOrthonormalization CayleyTransform OrthogonalExponential OrthogonalVertexSpace

variable {M : Type*} [TopologicalSpace M] {n m : ℕ}

noncomputable def complexStructureFamilyVertices (a : OrthogonalOperators n)
    (τ : Fin (m + 2) → ℝ) (J : C(M, OrthogonalComplexStructures.Space n)) : C(M, Space n m) :=
  ⟨fun x ↦ exponentialVertices a τ (Real.pi • (J x).1),
    (continuous_exponentialVertices a τ).comp
      ((continuous_subtype_val.comp J.continuous).const_smul Real.pi)⟩

variable {B H : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [FiniteDimensional ℝ B] [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
  [I.Boundaryless] [ChartedSpace H M] [IsManifold I ∞ M] [CompactSpace M] [T2Space M]

include I

theorem exists_homotopy_to_complexStructure_family (a b : OrthogonalOperators n)
    (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ)
    (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (hanti : (a⁻¹ * b).1.1 = -(1 : Vector n →L[ℝ] Vector n))
    (hsmall : ∀ J : OrthogonalComplexStructures.Space n, ∀ i : Fin (m + 1),
      (τ i.succ - τ i.castSucc) • (Real.pi • J.1) ∈ (logarithmChart n).target)
    (cap : ℝ) (hcap : (n : ℝ) * Real.pi ^ 2 < cap)
    (hcompact : IsCompact (energySublevel a b τ cap))
    (hshort : energySublevel a b τ cap ⊆ shortDomain a b m)
    (hd : finrank ℝ B + 2 < n)
    (p : C(M, Space n m)) (hp : ∀ x, p x ∈ admissible a b m)
    (start : ℝ) (hstart : start < cap) (hpstart : ∀ x, energy a b τ (p x) ≤ start) :
    ∃ J : C(M, OrthogonalComplexStructures.Space n),
      ∃ G : ContinuousMap.HomotopyRel p (complexStructureFamilyVertices a τ J)
          (p ⁻¹' minimumSet a b τ),
        ∀ t x, G (t, x) ∈ energySublevel a b τ cap := by
  obtain ⟨q, hq, G, hG⟩ := exists_homotopy_into_minimum (I := I)
    a b τ hτ hzero hone hanti hsmall cap hcap hcompact hshort hd p hp start hstart hpstart
  let qm : C(M, minimumSet a b τ) := ⟨fun x ↦ ⟨q x, hq x⟩, q.continuous.subtype_mk _⟩
  let e := complexStructureMinimumHomeomorph a b τ hτ hzero hone hanti hsmall
    (isCompact_energySublevel_of_le a b τ hcap.le hcompact)
  let J : C(M, OrthogonalComplexStructures.Space n) :=
    ⟨fun x ↦ e.symm (qm x), e.symm.continuous.comp qm.continuous⟩
  have hend : complexStructureFamilyVertices a τ J = q := by
    apply ContinuousMap.ext
    intro x
    exact congrArg Subtype.val (e.apply_symm_apply (qm x))
  exact ⟨J, G.cast rfl hend.symm, hG⟩

end NoExoticSixSphere.OrthogonalPolygon
