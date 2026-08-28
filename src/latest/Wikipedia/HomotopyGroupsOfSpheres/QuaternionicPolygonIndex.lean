import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicPolygonRealization
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicNegativeVariation
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicVertexVariation
import Wikipedia.NoExoticSixSphere.OrthogonalPolygonVariationComparison

/-!
# Sampling negative symplectic fields into finite polygon directions

For a strictly short polygon realizing a nonminimal antipodal exponential,
the negative smooth variations give negative variations of the actual finite
polygon energy. Their negativity proves that vertex sampling preserves
linear independence. Classification of critical polygons is a separate step.
-/

noncomputable section

open scoped ContDiff Manifold
open Set

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.Polygon

open NoExoticSixSphere.GLOrthonormalization NoExoticSixSphere.SkewSpectralPlane
open VertexSpace Exponential IndexTestField

variable {n m : ℕ}

def sampleFieldLinear (τ : Fin (m + 2) → ℝ) : (ℝ → SkewSpace n) →ₗ[ℝ] Model n m :=
  LinearMap.pi (fun j => LinearMap.proj (τ j.castSucc.succ))

theorem sampleFieldLinear_toOrthogonal (τ : Fin (m + 2) → ℝ) (W : ℝ → SkewSpace n) :
    (fun i => toOrthogonalSkew n (sampleFieldLinear τ W i)) =
      NoExoticSixSphere.OrthogonalPolygon.sampledField τ (fun t => toOrthogonalSkew n (W t)) := rfl

theorem secondDerivative_le_of_energy_contact (a b : symplecticSubgroup n)
    (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ) (v : Space n m)
    (hv : v ∈ shortDomain a b m) {γ : ℝ → symplecticSubgroup n} {W : ℝ → SkewSpace n}
    (hγ : ContDiff ℝ ∞ (fun t => (γ t).val.val.val)) (hW : ContDiff ℝ ∞ W)
    (hmatch : ∀ j, γ (τ j) = vertices a b v j)
    (hl : W (τ 0) = 0) (hu : W (τ (Fin.last (m + 1))) = 0)
    (hcontact : energy a b τ v = NoExoticSixSphere.OrthogonalPathEnergy.energy
      (fun t => (γ t).val.val.val) (τ 0) (τ (Fin.last (m + 1)))) :
    deriv (deriv (fun s => energy a b τ (vertexVariation v (sampleFieldLinear τ W) s))) 0 ≤
      deriv (deriv (fun s => NoExoticSixSphere.OrthogonalPathEnergy.energy
        (fun t => (NegativeVariation.family γ W (s, t)).val.val.val)
          (τ 0) (τ (Fin.last (m + 1))))) 0 := by
  have hL : ContDiff ℝ ∞ (toOrthogonalSkew n) :=
    finiteLinearMap_contDiff (E := SkewSpace n)
      (F := NoExoticSixSphere.CayleyTransform.SkewOperators (4 * n + 4)) (toOrthogonalSkew n)
  have hWO : ContDiff ℝ ∞ (fun t => toOrthogonalSkew n (W t)) := hL.comp hW
  have hmatchO (j) : (γ (τ j)).val =
      NoExoticSixSphere.OrthogonalPolygon.vertices a.val b.val (forget v) j := by
    rw [hmatch, vertices_forget]
  have hlO : toOrthogonalSkew n (W (τ 0)) = 0 := by rw [hl, map_zero]
  have huO : toOrthogonalSkew n (W (τ (Fin.last (m + 1)))) = 0 := by rw [hu, map_zero]
  have h := NoExoticSixSphere.OrthogonalPolygon.secondDerivative_le_of_energy_contact
    a.val b.val τ hτ (forget v) (shortDomain_forget a b hv)
    (γ := fun t => (γ t).val) hγ hWO hmatchO hlO huO hcontact
  simpa only [energy, forget_vertexVariation, sampleFieldLinear_toOrthogonal,
    NegativeVariation.family_orthogonal] using h

theorem linear_injective_of_negative_variations (a b : symplecticSubgroup n)
    (τ : Fin (m + 2) → ℝ) (v : Space n m) {d : ℕ}
    (R : (Fin d → ℝ) →ₗ[ℝ] Model n m)
    (hneg : ∀ c, c ≠ 0 →
      deriv (deriv (fun s => energy a b τ (vertexVariation v (R c) s))) 0 < 0) :
    Function.Injective R := by
  apply (injective_iff_map_eq_zero R).mpr
  intro c hc
  by_contra hne
  have hn := hneg c hne
  rw [hc] at hn
  simp only [vertexVariation_zero_field, deriv_const', deriv_const] at hn
  exact (lt_irrefl 0) hn

theorem exists_negative_vertexFamily (a b : symplecticSubgroup n)
    (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ)
    (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (v : Space n m) (hv : v ∈ shortDomain a b m) (K : SkewSpace n)
    (hpath : ∀ t ∈ Icc (0 : ℝ) 1, path a b τ v t = a * exp (t • K))
    (hexp : (exp K).val.val.val = -(1 : Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)))
    (hnot : gram (toOrthogonalSkew n K) ≠
      Real.pi ^ 2 • (1 : Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4))) :
    ∃ R : (Fin n → ℝ) →ₗ[ℝ] Model n m, Function.Injective R ∧ ∀ c, c ≠ 0 →
      deriv (deriv (fun s => energy a b τ (vertexVariation v (R c) s))) 0 < 0 := by
  let γ : ℝ → symplecticSubgroup n := fun t => a * exp (t • K)
  have hγ : ContDiff ℝ ∞ (fun t => (γ t).val.val.val) :=
    contDiff_const.clm_comp
      (NoExoticSixSphere.SkewConjugation.contDiff_exp_smul_operator (toOrthogonalSkew n K))
  have htime (j : Fin (m + 2)) : τ j ∈ Icc (0 : ℝ) 1 := by
    constructor
    · rw [← hzero]
      exact hτ.monotone (Fin.zero_le j)
    · rw [← hone]
      exact hτ.monotone (Fin.le_last j)
  have hmatch (j : Fin (m + 2)) : γ (τ j) = vertices a b v j :=
    (hpath _ (htime j)).symm.trans (path_vertex a b τ hτ hv.1 j)
  have hcontact : energy a b τ v = NoExoticSixSphere.OrthogonalPathEnergy.energy
      (fun t => (γ t).val.val.val) (τ 0) (τ (Fin.last (m + 1))) := by
    rw [← path_energy_eq a b τ hτ hv.1, hzero, hone]
    apply NoExoticSixSphere.OrthogonalPathEnergy.energy_congr_Icc zero_le_one
    intro t ht
    exact congrArg (fun q : symplecticSubgroup n => q.val.val.val) (hpath t ht)
  obtain ⟨T, _, hneg⟩ := exists_negativeFamily K hexp hnot
  let R : (Fin n → ℝ) →ₗ[ℝ] Model n m := (sampleFieldLinear τ).comp ((fieldLinear K).comp T)
  have hRneg (c : Fin n → ℝ) (hc : c ≠ 0) :
      deriv (deriv (fun s => energy a b τ (vertexVariation v (R c) s))) 0 < 0 := by
    have hle := secondDerivative_le_of_energy_contact a b τ hτ v hv hγ
      (contDiff_field K (T c)) hmatch
      (by rw [hzero]; exact field_zero K (T c))
      (by rw [hone]; exact field_one K (T c)) hcontact
    rw [hzero, hone] at hle
    exact lt_of_le_of_lt hle (NegativeVariation.negative_secondDerivative a K (T c) (hneg c hc))
  exact ⟨R, linear_injective_of_negative_variations a b τ v R hRneg, hRneg⟩

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.Polygon
