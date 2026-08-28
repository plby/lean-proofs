import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSecondMinimumEnergy
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicComplexStructurePolygonMinimum
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicComplexStructurePolygonCriticalIndex

/-! # Minimum complex-structure polygons are exactly the original anticommuting rotations -/

open Set

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.ComplexStructurePolygon

open NoExoticSixSphere.GLOrthonormalization NoExoticSixSphere.HilbertSchmidt
open ComplexStructures ComplexStructureVertices Exponential

variable {n m : ℕ}

theorem energy_eq_min_iff_rotation (a b : ComplexStructures.Space n)
    (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ)
    (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1) (E : ℝ)
    (hcompact : IsCompact (energySublevel a b τ E))
    (hanti : (Cayley.relative a b).val.val.val =
      -(1 : Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)))
    (v : ComplexStructureVertices.Space n m) (hv : v ∈ energySublevel a b τ E) :
    energy a b τ v = ((4 * n + 4 : ℕ) : ℝ) * Real.pi ^ 2 ↔
      ∃ P : AnticommutingStructures.Space a, ∀ t ∈ Icc (0 : ℝ) 1,
        path a b τ hτ v hv.1 t = AnticommutingStructures.rotation P (t * Real.pi) := by
  have hpenergy := path_energy_eq a b τ hτ v hv.1
  rw [hzero, hone] at hpenergy
  constructor
  · intro he
    have hcrit := critical_of_minimum_energy a b τ hτ hzero hone E hcompact hanti v hv he
    obtain ⟨K, hend, hpath⟩ := critical_is_exponential a b τ hτ v hv.1 hcrit
    simp only [hzero, hone, sub_zero] at hend hpath
    have hgroup := congrArg toSymplectic hend
    rw [exponentialCurve_toSymplectic, one_smul] at hgroup
    have hexpeq : exp (antiSkewToSkew a K) = Cayley.relative a b := by
      rw [Cayley.relative, ← hgroup, inv_mul_cancel_left]
    have hexp : (exp (antiSkewToSkew a K)).val.val.val =
        -(1 : Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)) := by rwa [hexpeq]
    have hsq : squareNorm K.val = ((4 * n + 4 : ℕ) : ℝ) * Real.pi ^ 2 :=
      (energy_eq_squareNorm_of_exponential a b τ hτ hzero hone v hv.1 K hpath).symm.trans he
    obtain ⟨P, hP⟩ := (AnticommutingStructures.squareNorm_eq_iff_minimumSpeed K hexp).mp hsq
    refine ⟨P, fun t ht ↦ (hpath t ht).trans ?_⟩
    rw [← hP, AnticommutingStructures.exponentialCurve_speed]
  · rintro ⟨P, hP⟩
    rw [← hpenergy, NoExoticSixSphere.OrthogonalPathEnergy.energy_congr_Icc zero_le_one
      (fun t ht ↦ congrArg (fun Q : ComplexStructures.Space n ↦ Q.val.val) (hP t ht))]
    exact AnticommutingStructures.energy_rotation P

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.ComplexStructurePolygon
