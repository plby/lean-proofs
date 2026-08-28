import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicComplexStructurePolygonIndex
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicComplexStructureStationaryPolygon
import Wikipedia.NoExoticSixSphere.SkewAntipodalMinimum

/-! # A rank-growing negative family at every nonminimal complex-structure critical polygon -/

noncomputable section

open Set

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.ComplexStructurePolygon

open NoExoticSixSphere.GLOrthonormalization NoExoticSixSphere.HilbertSchmidt
open NoExoticSixSphere.SkewSpectralPlane ComplexStructures ComplexStructureVertices Exponential

variable {n m : ℕ}

theorem energy_eq_squareNorm_of_exponential (a b : ComplexStructures.Space n)
    (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ)
    (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (v : ComplexStructureVertices.Space n m) (hv : v ∈ admissible a b m) (K : AntiSkewSpace a)
    (hpath : ∀ t ∈ Icc (0 : ℝ) 1, path a b τ hτ v hv t = exponentialCurve a K t) :
    energy a b τ v = squareNorm K.val := by
  let L := antiSkewToSkew a K
  have he := path_energy_eq a b τ hτ v hv
  rw [hzero, hone] at he
  have hcompare : NoExoticSixSphere.OrthogonalPathEnergy.energy
      (fun t ↦ (path a b τ hτ v hv t).val.val) 0 1 =
      NoExoticSixSphere.OrthogonalPathEnergy.energy
        (fun t ↦ (toSymplectic a * exp (t • L)).val.val.val) 0 1 := by
    apply NoExoticSixSphere.OrthogonalPathEnergy.energy_congr_Icc zero_le_one
    intro t ht
    exact (congrArg (fun Q : ComplexStructures.Space n ↦ Q.val.val) (hpath t ht)).trans
      (congrArg (fun q : symplecticSubgroup n ↦ q.val.val.val)
        (exponentialCurve_toSymplectic a K t))
  change NoExoticSixSphere.OrthogonalPathEnergy.energy
    (fun t ↦ (path a b τ hτ v hv t).val.val) 0 1 =
    NoExoticSixSphere.OrthogonalPathEnergy.energy
      (fun t ↦ ((toSymplectic a).val * NoExoticSixSphere.OrthogonalExponential.exp
        (t • toOrthogonalSkew n L)).val.val) 0 1 at hcompare
  rw [NoExoticSixSphere.OrthogonalPathEnergy.energy_left_exp] at hcompare
  have hn : squareNorm (toOrthogonalSkew n L).val = squareNorm K.val := rfl
  have he' : energy a b τ v = squareNorm (toOrthogonalSkew n L).val := by
    simpa only [sub_zero, one_mul] using he.symm.trans hcompare
  exact he'.trans hn

theorem exists_negative_vertexFamily_of_critical (a b : ComplexStructures.Space n)
    (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ)
    (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (v : ComplexStructureVertices.Space n m) (hv : v ∈ admissible a b m)
    (hcrit : fderiv ℝ (localEnergy a b τ v) 0 = 0)
    (hanti : (Cayley.relative a b).val.val.val =
      -(1 : Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)))
    (habove : ((4 * n + 4 : ℕ) : ℝ) * Real.pi ^ 2 < energy a b τ v) :
    ∃ R : (Fin n → ℝ) →ₗ[ℝ] Model v, Function.Injective R ∧ ∀ c, c ≠ 0 →
      deriv (deriv (fun s ↦ energy a b τ (vertexVariation v (R c) s))) 0 < 0 := by
  obtain ⟨K, hend, hpath⟩ := critical_is_exponential a b τ hτ v hv hcrit
  simp only [hzero, hone, sub_zero] at hend hpath
  have hgroup := congrArg toSymplectic hend
  rw [exponentialCurve_toSymplectic, one_smul] at hgroup
  have hexpeq : exp (antiSkewToSkew a K) = Cayley.relative a b := by
    rw [Cayley.relative, ← hgroup, inv_mul_cancel_left]
  have hexp : (exp (antiSkewToSkew a K)).val.val.val =
      -(1 : Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)) := by rwa [hexpeq]
  apply exists_negative_vertexFamily_of_exponential a b τ hτ hzero hone v hv K hpath hexp
  intro hgram
  have he := energy_eq_squareNorm_of_exponential a b τ hτ hzero hone v hv K hpath
  exact habove.ne' (he.trans
    (NoExoticSixSphere.SkewAntipodalSpectrum.squareNorm_of_gram_scalar
      (toOrthogonalSkew n (antiSkewToSkew a K)) _ hgram))

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.ComplexStructurePolygon
