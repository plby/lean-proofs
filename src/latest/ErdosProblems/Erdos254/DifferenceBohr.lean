/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos254.SymbolicSpace

namespace Erdos254

open Filter MeasureTheory Set
open scoped BigOperators Topology

/-- Positive upper density along initial intervals, expressed for a binary
configuration without an auxiliary density limit. -/
def PositiveBinaryDensity (c : BinarySequence) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∃ᶠ N : ℕ in atTop,
    δ ≤ (N + 1 : ℝ)⁻¹ * ∑ k ∈ Finset.range (N + 1), ((c k).toNat : ℝ)

def configurationDifferences (c : BinarySequence) : Set ℕ :=
  {n | ∃ k : ℤ, c k = true ∧ c (k + n) = true}

/-- The correspondence measure of a configuration of positive upper density. -/
theorem positive_binary_density_measure (c : BinarySequence) (hc : PositiveBinaryDensity c) :
    ∃ μ : ProbabilityMeasure (binaryOrbitClosure c),
      MeasurePreserving (orbitShift c) (μ : Measure (binaryOrbitClosure c)) μ ∧
      0 < (μ : Measure (binaryOrbitClosure c)).real (orbitCylinder c) := by
  obtain ⟨δ, hδ, hdensity⟩ := hc
  have havg (N : ℕ) :
      birkhoffAverage ℝ (orbitShift c) (orbitObservable c) (N + 1) (binaryBase c) =
        (N + 1 : ℝ)⁻¹ * ∑ k ∈ Finset.range (N + 1), ((c k).toNat : ℝ) := by
    simp only [birkhoffAverage, birkhoffSum, orbitObservable, ContinuousMap.coe_mk,
      orbitShift_iterate_apply, binaryBase, zero_add, smul_eq_mul, Nat.cast_add, Nat.cast_one]
  obtain ⟨μ, hpres, hlower⟩ := exists_invariant_probability (orbitShift c)
    (orbitShift c).continuous (binaryBase c) (orbitObservable c) δ
      (by simpa only [havg] using hdensity)
  have hpos : 0 < (μ : Measure (binaryOrbitClosure c)).real (orbitCylinder c) := by
    rw [integral_orbitObservable] at hlower
    exact hδ.trans_le hlower
  exact ⟨μ, hpres, hpos⟩

/-- Følner's difference-set theorem in the form needed for the sumset argument:
positive upper density yields a piecewise Bohr set of nonnegative differences. -/
theorem configuration_differences_piecewiseBohr (c : BinarySequence)
    (hc : PositiveBinaryDensity c) : ContainsPiecewiseBohr (configurationDifferences c) := by
  obtain ⟨μ, hpres, hpos⟩ := positive_binary_density_measure c hc
  have hreturns := return_times_piecewiseBohr (μ : Measure (binaryOrbitClosure c))
    (orbitShift c).toMeasurableEquiv hpres (orbitCylinder_measurable c) hpos
  apply hreturns.mono
  intro n hn
  obtain ⟨x, hx⟩ := nonempty_of_measure_ne_zero hn
  have hx0 : x.val 0 = true := hx.1
  have hxn : x.val (n : ℤ) = true := by
    have ht : ((orbitShift c)^[n] x).val 0 = true := hx.2
    simpa only [orbitShift_iterate_apply, zero_add] using ht
  obtain ⟨k, hk⟩ := orbitClosure_finite_pattern x.property ({0, (n : ℤ)} : Finset ℤ)
  refine ⟨k, ?_, ?_⟩
  · have h := hk 0 (by simp)
    simpa only [zero_add, hx0] using h.symm
  · have h := hk (n : ℤ) (by simp)
    simpa only [hxn, add_comm] using h.symm

end Erdos254
