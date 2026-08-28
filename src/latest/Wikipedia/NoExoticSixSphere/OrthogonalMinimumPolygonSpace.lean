import Wikipedia.NoExoticSixSphere.OrthogonalExponentialPolygon
import Wikipedia.NoExoticSixSphere.OrthogonalPolygonMinimumPaths

/-!
# The actual minimum polygon locus and orthogonal complex structures

Sampling the minimum exponential paths gives a continuous bijection onto
the minimum-energy polygon locus. Local logarithmic uniqueness gives
injectivity, and the proved energy equality case gives surjectivity.
Compactness of the complex-structure space makes this a homeomorphism.
-/

open Set

namespace NoExoticSixSphere.OrthogonalPolygon

open GLOrthonormalization CayleyTransform OrthogonalExponential OrthogonalVertexSpace

variable {n m : ℕ}

def minimumSet (a b : OrthogonalOperators n) (τ : Fin (m + 2) → ℝ) : Set (Space n m) :=
  {v | v ∈ admissible a b m ∧ energy a b τ v = (n : ℝ) * Real.pi ^ 2}

theorem complexStructure_endpoint (a b : OrthogonalOperators n)
    (hanti : (a⁻¹ * b).1.1 = -(1 : Vector n →L[ℝ] Vector n))
    (J : OrthogonalComplexStructures.Space n) : a * exp (Real.pi • J.1) = b := by
  have he : exp (Real.pi • J.1) = a⁻¹ * b :=
    Subtype.ext (Subtype.ext ((OrthogonalComplexStructures.exp_pi J).trans hanti.symm))
  rw [he, mul_inv_cancel_left]

variable (a b : OrthogonalOperators n) (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (hanti : (a⁻¹ * b).1.1 = -(1 : Vector n →L[ℝ] Vector n))
    (hsmall : ∀ J : OrthogonalComplexStructures.Space n, ∀ i : Fin (m + 1),
      (τ i.succ - τ i.castSucc) • (Real.pi • J.1) ∈ (logarithmChart n).target)

include hτ hzero hone hanti hsmall

theorem exponentialVertices_mem_minimumSet (J : OrthogonalComplexStructures.Space n) :
    exponentialVertices a τ (Real.pi • J.1) ∈ minimumSet a b τ := by
  have hend := complexStructure_endpoint a b hanti J
  refine ⟨exponentialVertices_admissible a b τ hzero hone _ hend (hsmall J), ?_⟩
  rw [energy_exponentialVertices a b τ hτ hzero hone _ hend (hsmall J)]
  apply SkewAntipodalSpectrum.squareNorm_of_gram_scalar
  rw [SkewSpectralPlane.gram_smul, OrthogonalComplexStructures.gram_eq_one]

noncomputable def minimumParametrization :
    C(OrthogonalComplexStructures.Space n, minimumSet a b τ) where
  toFun J := ⟨exponentialVertices a τ (Real.pi • J.1),
    exponentialVertices_mem_minimumSet a b τ hτ hzero hone hanti hsmall J⟩
  continuous_toFun := ((continuous_exponentialVertices a τ).comp
    (continuous_subtype_val.const_smul Real.pi)).subtype_mk _

theorem minimumParametrization_injective :
    Function.Injective (minimumParametrization a b τ hτ hzero hone hanti hsmall) := by
  intro J L he
  have hv : exponentialVertices a τ (Real.pi • J.1) = exponentialVertices a τ (Real.pi • L.1) :=
    congrArg Subtype.val he
  have hg := congrArg (fun v ↦ generator a b v (0 : Fin (m + 1))) hv
  rw [generator_exponentialVertices a b τ hzero hone _ (complexStructure_endpoint a b hanti J)
      (hsmall J),
    generator_exponentialVertices a b τ hzero hone _ (complexStructure_endpoint a b hanti L)
      (hsmall L)] at hg
  have hδ : τ (0 : Fin (m + 1)).succ - τ (0 : Fin (m + 1)).castSucc ≠ 0 :=
    sub_ne_zero.mpr (hτ (show (0 : Fin (m + 1)).castSucc < (0 : Fin (m + 1)).succ by simp)).ne'
  apply Subtype.ext
  exact smul_right_injective (M := SkewOperators n) Real.pi_ne_zero
    (smul_right_injective (M := SkewOperators n) hδ hg)

variable (hcompact : IsCompact (energySublevel a b τ ((n : ℝ) * Real.pi ^ 2)))

include hcompact

theorem minimumParametrization_surjective :
    Function.Surjective (minimumParametrization a b τ hτ hzero hone hanti hsmall) := by
  intro v
  have hv : v.1 ∈ energySublevel a b τ ((n : ℝ) * Real.pi ^ 2) := ⟨v.2.1, v.2.2.le⟩
  obtain ⟨J, hJ⟩ := (energy_eq_min_iff_complexStructure a b τ hτ hzero hone _ hcompact
    hanti v.1 hv).mp v.2.2
  refine ⟨J, Subtype.ext ?_⟩
  funext i
  have ht : τ i.castSucc.succ ∈ Icc (0 : ℝ) 1 := by
    constructor
    · rw [← hzero]
      exact hτ.monotone (Fin.zero_le _)
    · rw [← hone]
      exact hτ.monotone (Fin.le_last _)
  have he := (path_vertex a b τ hτ v.2.1 i.castSucc.succ).symm.trans (hJ _ ht)
  change a * exp (τ i.castSucc.succ • (Real.pi • J.1)) = v.1 i
  simpa only [vertices_interior] using he.symm

noncomputable def complexStructureMinimumHomeomorph :
    OrthogonalComplexStructures.Space n ≃ₜ minimumSet a b τ :=
  IsHomeomorph.homeomorph (minimumParametrization a b τ hτ hzero hone hanti hsmall)
    (isHomeomorph_iff_continuous_bijective.mpr
      ⟨(minimumParametrization a b τ hτ hzero hone hanti hsmall).continuous,
        minimumParametrization_injective a b τ hτ hzero hone hanti hsmall,
        minimumParametrization_surjective a b τ hτ hzero hone hanti hsmall hcompact⟩)

theorem complexStructureMinimumHomeomorph_apply (J : OrthogonalComplexStructures.Space n) :
    (complexStructureMinimumHomeomorph a b τ hτ hzero hone hanti hsmall hcompact J).1 =
      exponentialVertices a τ (Real.pi • J.1) := rfl

end NoExoticSixSphere.OrthogonalPolygon
