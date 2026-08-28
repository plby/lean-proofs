import Wikipedia.HopfProblem.PeriodTori
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# An actual compact cutoff meeting every period-lattice orbit

Rounding down the coordinates in the genuine period basis gives an
element of the genuine period lattice.  Subtracting it lands in the
basis parallelepiped, which is compact.  A smooth bump function equal
to one on that compact set therefore meets every orbit positively.
No fundamental-domain coverage or cutoff existence is assumed.
-/

noncomputable section

open Set Metric
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationLatticeCochain

/-- Coordinatewise integer floor, as an element of the actual period lattice. -/
def latticeFloor (p : PeriodDomain) (z : ComplexPlane₂) : p.lattice :=
  ⟨ZSpan.floor p.basis z, by
    rw [p.lattice_eq_span_basis]
    exact (ZSpan.floor p.basis z).property⟩

@[simp] theorem latticeFloor_coe (p : PeriodDomain) (z : ComplexPlane₂) :
    (latticeFloor p z : ComplexPlane₂) = ZSpan.floor p.basis z := rfl

/-- The representative obtained by subtracting the actual lattice floor
lies in the actual compact period parallelepiped. -/
theorem sub_latticeFloor_mem_parallelepiped (p : PeriodDomain) (z : ComplexPlane₂) :
    z - (latticeFloor p z : ComplexPlane₂) ∈ (p.basis.parallelepiped : Set ComplexPlane₂) := by
  change ZSpan.fract p.basis z ∈ _root_.parallelepiped p.basis
  exact ZSpan.fundamentalDomain_subset_parallelepiped p.basis
    (ZSpan.fract_mem_fundamentalDomain p.basis z)

theorem exists_lattice_translate_mem_parallelepiped (p : PeriodDomain) (z : ComplexPlane₂) :
    ∃ l : p.lattice, z + (l : ComplexPlane₂) ∈ (p.basis.parallelepiped : Set ComplexPlane₂) := by
  refine ⟨-latticeFloor p z, ?_⟩
  simpa only [Submodule.coe_neg, ← sub_eq_add_neg] using
    sub_latticeFloor_mem_parallelepiped p z

/-- A genuine compact set meets every lattice orbit by positive translation. -/
theorem exists_compact_lattice_cover (p : PeriodDomain) :
    ∃ K : Set ComplexPlane₂, IsCompact K ∧
      ∀ z, ∃ l : p.lattice, z + (l : ComplexPlane₂) ∈ K :=
  ⟨p.basis.parallelepiped, p.basis.parallelepiped.isCompact,
    exists_lattice_translate_mem_parallelepiped p⟩

/-- An actual compactly supported nonnegative smooth cutoff equals one
at some lattice translate of every point. -/
theorem exists_smooth_lattice_cutoff (p : PeriodDomain) :
    ∃ χ : ComplexPlane₂ → ℝ, ContDiff ℝ ∞ χ ∧ (∀ z, 0 ≤ χ z) ∧
      HasCompactSupport χ ∧ ∀ z, ∃ l : p.lattice, χ (z + l) = 1 := by
  obtain ⟨K, hK, hcover⟩ := exists_compact_lattice_cover p
  obtain ⟨r, hr, hbound⟩ := hK.isBounded.subset_closedBall_lt 0 (0 : ComplexPlane₂)
  let b : ContDiffBump (0 : ComplexPlane₂) := {
    rIn := r
    rOut := r + 1
    rIn_pos := hr
    rIn_lt_rOut := lt_add_one r }
  refine ⟨b, b.contDiff, fun _ => b.nonneg, b.hasCompactSupport, ?_⟩
  intro z
  obtain ⟨l, hl⟩ := hcover z
  exact ⟨l, b.one_of_mem_closedBall (hbound hl)⟩

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationLatticeCochain
