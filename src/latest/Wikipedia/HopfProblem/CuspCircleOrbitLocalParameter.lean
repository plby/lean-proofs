import Wikipedia.HopfProblem.ThreefoldHomologyDeltaSweepAction

/-!
# The exact unit-circle range of the original delta parameter

The existing period-one parameter is precisely the norm-one subgroup of
the nonzero complex scalars. These lemmas retain its original normalized
exponential, so local opposite-weight orbits can be compared with the
unchanged global circle action without introducing another parameter.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.FixedCoordinates.CircleOrbit

open Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology

local notation "Circle" => AddCircle (1 : ℝ)

/-- The original normalized exponential has norm one at every real time. -/
theorem normalizedExponential_real_norm (t : ℝ) :
    ‖(Exponential.normalizedExponential (t : ℂ) : ℂ)‖ = 1 := by
  simp [Exponential.normalizedExponential_coe, CuspUniformization.exponential,
    Complex.norm_exp, Complex.mul_re, Complex.mul_im]

/-- Every parameter of the actual delta-circle action is a unit scalar. -/
@[simp] theorem circleParameter_norm (t : Circle) :
    ‖(DeltaSweep.circleParameter t : ℂ)‖ = 1 := by
  refine QuotientAddGroup.induction_on t fun s => ?_
  rw [DeltaSweep.circleParameter_real]
  exact normalizedExponential_real_norm s

/-- Every norm-one scalar occurs with the original period-one normalization. -/
theorem exists_circleParameter_of_norm_eq_one (u : ℂˣ) (hu : ‖(u : ℂ)‖ = 1) :
    ∃ t : Circle, DeltaSweep.circleParameter t = u := by
  obtain ⟨s, rfl⟩ := Exponential.normalizedExponential_surjective u
  change ‖CuspUniformization.exponential s‖ = 1 at hu
  have hlog := CuspUniformization.log_norm_exponential s
  rw [hu, Real.log_one] at hlog
  have him : s.im = 0 :=
    (mul_eq_zero.mp hlog.symm).resolve_left
      (mul_ne_zero (by norm_num) Real.pi_ne_zero)
  have hs : (s.re : ℂ) = s := Complex.ext rfl him.symm
  refine ⟨(s.re : Circle), ?_⟩
  rw [DeltaSweep.circleParameter_real, hs]

/-- The exact range of the existing parameter, inside the original complex units. -/
theorem mem_range_circleParameter_iff (u : ℂˣ) :
    u ∈ Set.range DeltaSweep.circleParameter ↔ ‖(u : ℂ)‖ = 1 := by
  constructor
  · rintro ⟨t, rfl⟩
    exact circleParameter_norm t
  · exact exists_circleParameter_of_norm_eq_one u

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.FixedCoordinates.CircleOrbit
