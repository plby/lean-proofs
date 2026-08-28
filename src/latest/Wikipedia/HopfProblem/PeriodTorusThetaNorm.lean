import Wikipedia.HopfProblem.PeriodTorusThetaBasic
import Mathlib.Topology.Order.Compact

/-!
# A genuine global norm bound from Appell--Humbert automorphy

The weighted norm is proved periodic from the transformation law and
Hermitian symmetry.  Its range is compact by the actual period lattice,
which produces the global exponential bound without an assumed compact
fundamental domain or an assumed periodicity statement.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusTheta

/-- Taking norms of the actual automorphy factor removes only the norm-one
multiplier; no multiplicativity of that multiplier is used. -/
theorem appellHumbert_norm (p : PeriodDomain) (H : HermitianForm)
    (α : p.lattice → ℂ) (hα : ∀ l, ‖α l‖ = 1)
    (θ : ComplexPlane₂ → ℂ) (hAuto : AppellHumbertAutomorphy p H α θ)
    (l : p.lattice) (z : ComplexPlane₂) :
    ‖θ (z + l)‖ =
      Real.exp (Real.pi * (H z l).re + (Real.pi / 2) * (H l l).re) * ‖θ z‖ := by
  rw [hAuto l z, norm_mul, norm_mul, hα l, one_mul, Complex.norm_exp]
  simp [Complex.mul_re]

/-- The weighted norm is unchanged under each genuine lattice translation. -/
theorem weightedNorm_translate (p : PeriodDomain) (H : HermitianForm) (hH : IsHermitian H)
    (α : p.lattice → ℂ) (hα : ∀ l, ‖α l‖ = 1)
    (θ : ComplexPlane₂ → ℂ) (hAuto : AppellHumbertAutomorphy p H α θ)
    (l : p.lattice) (z : ComplexPlane₂) :
    weightedNorm H θ (z + l) = weightedNorm H θ z := by
  unfold weightedNorm
  rw [appellHumbert_norm p H α hα θ hAuto l z, IsHermitian.diagonal_add_re H hH]
  rw [mul_comm (Real.exp _) ‖θ z‖, mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- Periodicity expressed on the actual lattice subset, for the lattice
compactness theorem. -/
theorem weightedNorm_periodic (p : PeriodDomain) (H : HermitianForm) (hH : IsHermitian H)
    (α : p.lattice → ℂ) (hα : ∀ l, ‖α l‖ = 1)
    (θ : ComplexPlane₂ → ℂ) (hAuto : AppellHumbertAutomorphy p H α θ) :
    ∀ z w, w ∈ p.lattice → weightedNorm H θ (z + w) = weightedNorm H θ z := by
  intro z w hw
  exact weightedNorm_translate p H hH α hα θ hAuto ⟨w, hw⟩ z

/-- Continuity and the full genuine period lattice make the weighted-norm
range compact. -/
theorem weightedNorm_range_isCompact (p : PeriodDomain) (H : HermitianForm)
    (hH : IsHermitian H) (α : p.lattice → ℂ) (hα : ∀ l, ‖α l‖ = 1)
    (θ : ComplexPlane₂ → ℂ) (hθ : Continuous θ)
    (hAuto : AppellHumbertAutomorphy p H α θ) :
    IsCompact (Set.range (weightedNorm H θ)) :=
  IsZLattice.isCompact_range_of_periodic p.lattice (weightedNorm H θ)
    (weightedNorm_continuous H θ hθ) (weightedNorm_periodic p H hH α hα θ hAuto)

/-- A global positive exponential bound follows from actual automorphy. -/
theorem theta_norm_bound (p : PeriodDomain) (H : HermitianForm) (hH : IsHermitian H)
    (α : p.lattice → ℂ) (hα : ∀ l, ‖α l‖ = 1)
    (θ : ComplexPlane₂ → ℂ) (hθ : Continuous θ)
    (hAuto : AppellHumbertAutomorphy p H α θ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z,
      ‖θ z‖ ≤ C * Real.exp ((Real.pi / 2) * (H z z).re) := by
  obtain ⟨M, hM⟩ := (weightedNorm_range_isCompact p H hH α hα θ hθ hAuto).bddAbove
  refine ⟨max M 0 + 1, ?_, ?_⟩
  · have hmax : 0 ≤ max M 0 := le_max_right M 0
    linarith
  · intro z
    have hbound : weightedNorm H θ z ≤ max M 0 + 1 := by
      have hz : weightedNorm H θ z ≤ M := hM (Set.mem_range_self z)
      have hm : M ≤ max M 0 := le_max_left M 0
      linarith
    have hz := mul_le_mul_of_nonneg_right hbound
      (Real.exp_pos ((Real.pi / 2) * (H z z).re)).le
    simpa only [weightedNorm, mul_assoc, ← Real.exp_add, neg_mul,
      neg_add_cancel, Real.exp_zero, mul_one] using hz

end Wikipedia.HopfProblem.PeriodTorusTheta
