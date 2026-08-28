import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicPolygonIndex
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicStationaryPolygon
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicVertexTangent
import Wikipedia.NoExoticSixSphere.SkewAntipodalMinimum

/-!
# Independent negative directions at actual symplectic critical polygons

In `Sp(n+1)`, every antipodal critical polygon above minimum energy has
an `n`-dimensional family of negative variations with independent actual
chart tangents. This rank-growing lower bound is not asserted to be sharp.
-/

noncomputable section

open scoped Manifold ContDiff
open Set

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.Polygon

open NoExoticSixSphere.GLOrthonormalization NoExoticSixSphere.HilbertSchmidt
open VertexSpace Exponential

variable {n m : ℕ}

theorem exists_negative_vertexFamily_of_critical (a b : symplecticSubgroup n)
    (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ)
    (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (v : Space n m) (hv : v ∈ shortDomain a b m)
    (hcrit : mfderiv 𝓘(ℝ, Model n m) 𝓘(ℝ, ℝ) (energy a b τ) v = 0)
    (hanti : (a⁻¹ * b).val.val.val = -(1 : Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)))
    (habove : ((4 * n + 4 : ℕ) : ℝ) * Real.pi ^ 2 < energy a b τ v) :
    ∃ R : (Fin n → ℝ) →ₗ[ℝ] Model n m, Function.Injective R ∧ ∀ c, c ≠ 0 →
      deriv (deriv (fun s => energy a b τ (vertexVariation v (R c) s))) 0 < 0 := by
  obtain ⟨K, hend, hpath⟩ := critical_is_exponential a b τ hτ v hv.1 hcrit
  simp only [hzero, hone, sub_zero, one_smul] at hend hpath
  have hexpeq : exp K = a⁻¹ * b := by rw [← hend, inv_mul_cancel_left]
  have hexp : (exp K).val.val.val =
      -(1 : Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)) := by rwa [hexpeq]
  apply exists_negative_vertexFamily a b τ hτ hzero hone v hv K hpath hexp
  intro hgram
  have he := path_energy_eq a b τ hτ hv.1
  rw [hzero, hone] at he
  have hcompare : NoExoticSixSphere.OrthogonalPathEnergy.energy
      (fun t => (path a b τ v t).val.val.val) 0 1 =
      NoExoticSixSphere.OrthogonalPathEnergy.energy
        (fun t => (a * exp (t • K)).val.val.val) 0 1 :=
    NoExoticSixSphere.OrthogonalPathEnergy.energy_congr_Icc zero_le_one
      (fun t ht => congrArg (fun q : symplecticSubgroup n => q.val.val.val) (hpath t ht))
  have hs : energy a b τ v = squareNorm K.val := by
    change NoExoticSixSphere.OrthogonalPathEnergy.energy
      (fun t => (path a b τ v t).val.val.val) 0 1 =
      NoExoticSixSphere.OrthogonalPathEnergy.energy
        (fun t => (a.val * NoExoticSixSphere.OrthogonalExponential.exp
          (t • toOrthogonalSkew n K)).val.val) 0 1 at hcompare
    rw [NoExoticSixSphere.OrthogonalPathEnergy.energy_left_exp] at hcompare
    simpa only [sub_zero, one_mul, toOrthogonalSkew, LinearMap.coe_mk, AddHom.coe_mk]
      using he.symm.trans hcompare
  exact habove.ne' (hs.trans
    (NoExoticSixSphere.SkewAntipodalSpectrum.squareNorm_of_gram_scalar
      (toOrthogonalSkew n K) _ hgram))

theorem exists_negative_tangentFamily_of_critical (a b : symplecticSubgroup n)
    (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ)
    (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (v : Space n m) (hv : v ∈ shortDomain a b m)
    (hcrit : mfderiv 𝓘(ℝ, Model n m) 𝓘(ℝ, ℝ) (energy a b τ) v = 0)
    (hanti : (a⁻¹ * b).val.val.val = -(1 : Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)))
    (habove : ((4 * n + 4 : ℕ) : ℝ) * Real.pi ^ 2 < energy a b τ v) :
    ∃ R : (Fin n → ℝ) →ₗ[ℝ] Model n m,
      Function.Injective (fun c => deriv (fun s => atVertices v (vertexVariation v (R c) s)) 0) ∧
      ∀ c, c ≠ 0 →
        deriv (deriv (fun s => energy a b τ (vertexVariation v (R c) s))) 0 < 0 := by
  obtain ⟨R, hR, hneg⟩ :=
    exists_negative_vertexFamily_of_critical a b τ hτ hzero hone v hv hcrit hanti habove
  exact ⟨R, independent_chart_tangents v R hR, hneg⟩

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.Polygon
