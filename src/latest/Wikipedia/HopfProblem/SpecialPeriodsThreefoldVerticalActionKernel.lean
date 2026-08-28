import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionKernelArithmetic
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionKernelCoordinates

/-!
# Common vertical periods of the actual special family

A fixed vertical translation is a period of every actual regular fibre
if and only if its scalar is an integer. Continuity, connectedness, and
discreteness first supply a single integral period vector. The proved
linear independence of the actual special periods then identifies that
vector with an integral multiple of the last source basis vector.

This is the geometric period-kernel calculation in Proposition 9.23.
No global flow, gluing, or automorphism-group conclusion is assumed here.
-/

noncomputable section

open Set UpperHalfPlane
open scoped Matrix

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalActionKernel

/-- A scalar that is a vertical period on every actual regular fibre is an integer. -/
theorem vertical_common_period_integer (ς : ℂ)
    (hς : ∀ z : TriangleRegularPoint,
      ς • (![0, 1] : ComplexPlane₂) ∈ (specialPeriodMap.point z.val).lattice) :
    ∃ n : ℤ, ς = (n : ℂ) := by
  obtain ⟨v, hv⟩ := exists_common_integer_period (ς • (![0, 1] : ComplexPlane₂)) hς
  exact ⟨v 3, (common_integer_period_vertical ς v hv).2.2.2⟩

/-- The common vertical periods of the genuine regular fibres are exactly the integers. -/
theorem vertical_mem_all_regular_lattices_iff (ς : ℂ) :
    (∀ z : TriangleRegularPoint,
      ς • (![0, 1] : ComplexPlane₂) ∈ (specialPeriodMap.point z.val).lattice) ↔
      ∃ n : ℤ, ς = (n : ℂ) := by
  constructor
  · exact vertical_common_period_integer ς
  · rintro ⟨n, rfl⟩ z
    exact integer_vertical_mem_lattice (specialPeriodMap.point z.val) n

/-- The equivalent statement in the literal ordered integer column coordinates. -/
theorem vertical_integer_periods_iff (ς : ℂ) :
    (∀ z : TriangleRegularPoint, ∃ v : Lattice,
      (specialPeriodMap.point z.val).val.matrix *ᵥ (fun i => (v i : ℂ)) =
        ς • (![0, 1] : ComplexPlane₂)) ↔ ∃ n : ℤ, ς = (n : ℂ) := by
  rw [← vertical_mem_all_regular_lattices_iff]
  apply forall_congr'
  intro z
  exact ((specialPeriodMap.point z.val).mem_lattice_iff _).symm

/-- The same characterization holds when periods are tested over all source points. -/
theorem vertical_mem_all_lattices_iff (ς : ℂ) :
    (∀ z : ℍ, ς • (![0, 1] : ComplexPlane₂) ∈ (specialPeriodMap.point z).lattice) ↔
      ∃ n : ℤ, ς = (n : ℂ) := by
  constructor
  · intro hς
    exact vertical_common_period_integer ς (fun z => hς z.val)
  · rintro ⟨n, rfl⟩ z
    exact integer_vertical_mem_lattice (specialPeriodMap.point z) n

/-- As a subset of the actual complex parameter line, the common period
kernel is the literal image of the integer embedding. -/
theorem vertical_common_periods_eq_range_intCast :
    {ς : ℂ | ∀ z : TriangleRegularPoint,
      ς • (![0, 1] : ComplexPlane₂) ∈ (specialPeriodMap.point z.val).lattice} =
      Set.range (fun n : ℤ => (n : ℂ)) := by
  ext ς
  constructor
  · intro hς
    obtain ⟨n, hn⟩ := vertical_common_period_integer ς hς
    exact ⟨n, hn.symm⟩
  · rintro ⟨n, rfl⟩
    exact (vertical_mem_all_regular_lattices_iff (n : ℂ)).mpr ⟨n, rfl⟩

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalActionKernel
