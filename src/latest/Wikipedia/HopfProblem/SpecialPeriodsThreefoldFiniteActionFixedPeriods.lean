import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionPeriodBasic
import Wikipedia.HopfProblem.EllipticFlatTorus

/-!
# Real vertical times in the actual period lattices

The original last real period coordinate is the primitive integral
column `δ`. Hence a real translation in that complex direction is a
period of even one fibre exactly when its time is an integer. This
pointwise assertion is stronger than the common-period kernel and does
not use variation or connectedness of the base.
-/

noncomputable section

open scoped Matrix ContDiff

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.FiniteActionFixed.Period

variable {V B : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace B] [ChartedSpace V B] (P : HolomorphicPeriodMap V B)

/-- The inverse period coordinates of a real vertical translation are
literally that real multiple of the last standard basis vector. -/
theorem inverse_vector_real (b : B) (s : ℝ) :
    (P.periodEquiv b).symm (VerticalAction.Period.vector (s : ℂ)) =
      s • Pi.basisFun ℝ (Fin 4) 3 := by
  apply (P.periodEquiv b).injective
  rw [LinearEquiv.apply_symm_apply, map_smul, VerticalAction.Period.periodEquiv_delta]
  ext i
  fin_cases i <;> simp [VerticalAction.Period.vector]

/-- No nonintegral real vertical time belongs to any actual period
lattice. The proof uses its full real basis, not just nonzero `e₂`. -/
theorem real_vector_mem_lattice_iff (b : B) (s : ℝ) :
    VerticalAction.Period.vector (s : ℂ) ∈ (P.point b).lattice ↔
      ∃ n : ℤ, s = (n : ℝ) := by
  constructor
  · intro hs
    have hm := (VerticalAction.Period.vector_mem_lattice_iff P (s : ℂ) b).mp hs
    rw [inverse_vector_real] at hm
    obtain ⟨v, hv⟩ := (Elliptic.standardLattice_mem_iff _).mp hm
    refine ⟨v 3, ?_⟩
    simpa only [Pi.smul_apply, Pi.basisFun_apply, Pi.single_eq_same,
      smul_eq_mul, mul_one, Elliptic.realCast] using congrFun hv 3
  · rintro ⟨n, rfl⟩
    apply (VerticalAction.Period.vector_mem_lattice_iff P _ b).mpr
    simpa only [Complex.ofReal_intCast] using
      VerticalAction.Period.inverse_vector_int_mem P b n

/-- The actual translation on each original family fibre fixes a point
at real time `s` if and only if `s` is integral. -/
theorem real_flow_eq_self_iff (s : ℝ) (x : P.TotalSpace) :
    VerticalAction.Period.flow P (s : ℂ) x = x ↔ ∃ n : ℤ, s = (n : ℝ) :=
  (VerticalAction.Period.flow_eq_self_iff P (s : ℂ) x).trans
    (real_vector_mem_lattice_iff P x.1 s)

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.FiniteActionFixed.Period
