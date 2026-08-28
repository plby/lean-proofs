import Wikipedia.HopfProblem.SpecialPeriodsLinearIndependence
import Wikipedia.HopfProblem.SpecialPeriodsTriangleRegularElliptic
import Wikipedia.HopfProblem.SpecialPeriodsTriangleQuotientDensity
import Wikipedia.HopfProblem.PeriodTorusQuasiperiodicPeriods

/-!
# Arithmetic of a common vertical period of the actual special family

For a single integral source vector, equality with a fixed vertical
translation on the regular locus extends to all source points. The proved
linear independence of the actual special periods then kills its first
three integral coordinates. Conversely, every integral multiple of the
second standard complex vector is an actual period in every fibre.
-/

noncomputable section

open Set Topology UpperHalfPlane
open scoped Matrix

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalActionKernel

theorem specialPeriodMatrix_first (z : ℍ) (v : Lattice) :
    ((specialPeriodMap.point z).val.matrix *ᵥ (fun i => (v i : ℂ))) 0 =
      6 * specialMu z * (v 0 : ℂ) + specialTau z * (v 1 : ℂ) + (v 2 : ℂ) := by
  simp [PeriodPoint.matrix, Matrix.mulVec, dotProduct, Fin.sum_univ_four, specialMu, specialTau]

theorem specialPeriodMatrix_second (z : ℍ) (v : Lattice) :
    ((specialPeriodMap.point z).val.matrix *ᵥ (fun i => (v i : ℂ))) 1 =
      specialBeta z * (v 0 : ℂ) + specialMu z * (v 1 : ℂ) + (v 3 : ℂ) := by
  simp [PeriodPoint.matrix, Matrix.mulVec, dotProduct, Fin.sum_univ_four, specialMu, specialBeta]

/-- A fixed integral vector representing a vertical period on every
regular fibre has only its final integral coordinate left. -/
theorem common_integer_period_vertical (ς : ℂ) (v : Lattice)
    (hv : ∀ z : TriangleRegularPoint,
      (specialPeriodMap.point z.val).val.matrix *ᵥ (fun i => (v i : ℂ)) =
        ς • (![0, 1] : ComplexPlane₂)) :
    v 0 = 0 ∧ v 1 = 0 ∧ v 2 = 0 ∧ ς = (v 3 : ℂ) := by
  have hfirst : ∀ z : TriangleRegularPoint,
      (v 2 : ℂ) + (v 1 : ℂ) * specialTau z.val +
        (6 * (v 0 : ℂ)) * specialMu z.val = 0 := by
    intro z
    have h := congrFun (hv z) 0
    rw [specialPeriodMatrix_first] at h
    change 6 * specialMu z.val * (v 0 : ℂ) + specialTau z.val * (v 1 : ℂ) +
      (v 2 : ℂ) = ς * 0 at h
    linear_combination h
  have hc : Continuous (fun z : ℍ =>
      (v 2 : ℂ) + (v 1 : ℂ) * specialTau z + (6 * (v 0 : ℂ)) * specialMu z) :=
    (continuous_const.add (continuous_const.mul specialTau_holomorphic.continuous)).add
      (continuous_const.mul specialMu_holomorphic.continuous)
  have hfull : ∀ z : ℍ,
      (v 2 : ℂ) + (v 1 : ℂ) * specialTau z + (6 * (v 0 : ℂ)) * specialMu z = 0 := by
    have hclosed : IsClosed {z : ℍ | (v 2 : ℂ) + (v 1 : ℂ) * specialTau z +
        (6 * (v 0 : ℂ)) * specialMu z = 0} := isClosed_eq hc continuous_const
    have hsubset : triangleRegularLocus ⊆
        {z : ℍ | (v 2 : ℂ) + (v 1 : ℂ) * specialTau z +
          (6 * (v 0 : ℂ)) * specialMu z = 0} := fun z hz => hfirst ⟨z, hz⟩
    have hclosure := closure_minimal hsubset hclosed
    rw [triangleRegularLocus_dense.closure_eq] at hclosure
    exact fun z => hclosure (mem_univ z)
  have hrel : ∀ z : ℍ,
      (v 2 : ℂ) + (v 1 : ℂ) * specialTau z + (6 * (v 0 : ℂ)) * specialMu z +
        0 * specialBeta z + 0 * (6 * specialMu z ^ 2 - specialTau z * specialBeta z) = 0 := by
    intro z
    simpa only [zero_mul, add_zero] using hfull z
  obtain ⟨hc₂, hc₁, hc₀, _, _⟩ :=
    specialPeriodFunctions_relation (v 2 : ℂ) (v 1 : ℂ) (6 * (v 0 : ℂ)) 0 0 hrel
  have hv₀ : v 0 = 0 := by
    have hz : (v 0 : ℂ) = 0 :=
      (mul_eq_zero.mp hc₀).resolve_left (by norm_num : (6 : ℂ) ≠ 0)
    exact_mod_cast hz
  have hv₁ : v 1 = 0 := by exact_mod_cast hc₁
  have hv₂ : v 2 = 0 := by exact_mod_cast hc₂
  refine ⟨hv₀, hv₁, hv₂, ?_⟩
  let z : TriangleRegularPoint := Classical.ofNonempty
  have hsecond := congrFun (hv z) 1
  rw [specialPeriodMatrix_second, hv₀, hv₁] at hsecond
  simpa using hsecond.symm

/-- Every integral vertical translation is a period of any actual
period-domain lattice, since the last period column is the second unit vector. -/
theorem integer_vertical_mem_lattice (p : PeriodDomain) (n : ℤ) :
    (n : ℂ) • (![0, 1] : ComplexPlane₂) ∈ p.lattice := by
  have h := PeriodTorusQuasiperiodic.integer_period_mem_lattice p (![0, 0, 0, n] : Lattice)
  have he : p.val.matrix *ᵥ (fun i => ((![0, 0, 0, n] : Lattice) i : ℂ)) =
      (n : ℂ) • (![0, 1] : ComplexPlane₂) := by
    ext i
    fin_cases i <;>
      simp [PeriodPoint.matrix, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  exact he ▸ h

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalActionKernel
