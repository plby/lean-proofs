import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicComplexStructureIndexField
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicComplexStructureVertexVariation
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicComplexStructurePolygonRealization
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicPolygonIndex

/-!
# Sampling negative anticommuting fields into actual complex-structure polygons

The sampled field belongs to each vertex's anticommuting model. Its actual
vertex variation therefore stays in the complex-structure space. The
verified energy-contact comparison transfers strict negativity to the
finite polygon energy; negativity also proves independence after sampling.
-/

noncomputable section

open Set
open scoped ContDiff

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.ComplexStructurePolygon

open NoExoticSixSphere.GLOrthonormalization NoExoticSixSphere.SkewSpectralPlane
open ComplexStructures ComplexStructureVertices Exponential IndexTestField

variable {n m : ℕ}

theorem exists_negative_vertexFamily_of_exponential (a b : ComplexStructures.Space n)
    (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ)
    (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (v : ComplexStructureVertices.Space n m) (hv : v ∈ admissible a b m) (K : AntiSkewSpace a)
    (hpath : ∀ t ∈ Icc (0 : ℝ) 1, path a b τ hτ v hv t = exponentialCurve a K t)
    (hexp : (exp (antiSkewToSkew a K)).val.val.val =
      -(1 : Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)))
    (hnot : gram (toOrthogonalSkew n (antiSkewToSkew a K)) ≠
      Real.pi ^ 2 • (1 : Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4))) :
    ∃ R : (Fin n → ℝ) →ₗ[ℝ] Model v, Function.Injective R ∧ ∀ c, c ≠ 0 →
      deriv (deriv (fun s ↦ energy a b τ (vertexVariation v (R c) s))) 0 < 0 := by
  let L := antiSkewToSkew a K
  let γ : ℝ → symplecticSubgroup n := fun t ↦ toSymplectic a * exp (t • L)
  have hγ : ContDiff ℝ ∞ (fun t ↦ (γ t).val.val.val) :=
    contDiff_const.clm_comp
      (NoExoticSixSphere.SkewConjugation.contDiff_exp_smul_operator (toOrthogonalSkew n L))
  have htime (j : Fin (m + 2)) : τ j ∈ Icc (0 : ℝ) 1 := by
    constructor
    · rw [← hzero]
      exact hτ.monotone (Fin.zero_le j)
    · rw [← hone]
      exact hτ.monotone (Fin.le_last j)
  have hmatchCS (j : Fin (m + 2)) : exponentialCurve a K (τ j) = vertices a b v j :=
    (hpath _ (htime j)).symm.trans (path_vertex a b τ hτ v hv j)
  have hmatch (j : Fin (m + 2)) :
      γ (τ j) = Polygon.vertices (toSymplectic a) (toSymplectic b) (forget v) j := by
    rw [← vertices_forget, ← hmatchCS, exponentialCurve_toSymplectic]
  have hpathOp (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      Polygon.path (toSymplectic a) (toSymplectic b) τ (forget v) t = γ t := by
    rw [← path_toSymplectic a b τ hτ v hv, hpath t ht, exponentialCurve_toSymplectic]
  have hcontact : Polygon.energy (toSymplectic a) (toSymplectic b) τ (forget v) =
      NoExoticSixSphere.OrthogonalPathEnergy.energy
        (fun t ↦ (γ t).val.val.val) (τ 0) (τ (Fin.last (m + 1))) := by
    rw [← Polygon.path_energy_eq _ _ τ hτ (admissible_forget a b hv), hzero, hone]
    apply NoExoticSixSphere.OrthogonalPathEnergy.energy_congr_Icc zero_le_one
    intro t ht
    exact congrArg (fun q : symplecticSubgroup n ↦ q.val.val.val) (hpathOp t ht)
  obtain ⟨T, _, hneg⟩ := exists_anticommuting_negativeFamily a L K.property.2 hexp hnot
  let F : (Fin n → ℝ) →ₗ[ℝ] (ℝ → SkewSpace n) :=
    (fieldLinear L).comp ((antiSkewToSkew a).comp T)
  let R₀ : (Fin n → ℝ) →ₗ[ℝ] VertexSpace.Model n m := (Polygon.sampleFieldLinear τ).comp F
  have hmem (c : Fin n → ℝ) (j : Fin m) : (R₀ c j).val ∈ antiSkewSubmodule (v j) := by
    have h := indexField_mem_antiSkew a K (T c) (τ j.castSucc.succ)
    rw [hmatchCS, vertices_interior] at h
    exact h
  let R : (Fin n → ℝ) →ₗ[ℝ] Model v := {
    toFun c j := ⟨(R₀ c j).val, hmem c j⟩
    map_add' c d := by
      funext j
      apply Subtype.ext
      exact congrArg (fun W : VertexSpace.Model n m ↦ (W j).val) (R₀.map_add c d)
    map_smul' r c := by
      funext j
      apply Subtype.ext
      exact congrArg (fun W : VertexSpace.Model n m ↦ (W j).val) (R₀.map_smul r c) }
  have hR (c : Fin n → ℝ) : modelInclusion v (R c) = R₀ c := by
    funext j
    apply Subtype.ext
    rfl
  have hRneg (c : Fin n → ℝ) (hc : c ≠ 0) :
      deriv (deriv (fun s ↦ Polygon.energy (toSymplectic a) (toSymplectic b) τ
        (Polygon.vertexVariation (forget v) (R₀ c) s))) 0 < 0 := by
    have hle := Polygon.secondDerivative_le_of_energy_contact (toSymplectic a) (toSymplectic b)
      τ hτ (forget v) (shortDomain_forget a b hv) hγ (contDiff_field L (antiSkewToSkew a (T c)))
      hmatch (by rw [hzero]; exact field_zero L (antiSkewToSkew a (T c)))
      (by rw [hone]; exact field_one L (antiSkewToSkew a (T c))) hcontact
    rw [hzero, hone] at hle
    exact lt_of_le_of_lt hle
      (NegativeVariation.negative_secondDerivative (toSymplectic a) L
        (antiSkewToSkew a (T c)) (hneg c hc))
  have hR₀inj := Polygon.linear_injective_of_negative_variations (toSymplectic a)
    (toSymplectic b) τ (forget v) R₀ hRneg
  refine ⟨R, ?_, ?_⟩
  · intro c d h
    apply hR₀inj
    rw [← hR, ← hR]
    exact congrArg (modelInclusion v) h
  · intro c hc
    simpa only [energy, forget_vertexVariation, hR] using hRneg c hc

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.ComplexStructurePolygon
