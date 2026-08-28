import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationUniquenessData
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# The semicharacter law forces integral imaginary lattice pairings

The two orders of addition in the actual lattice give equal phase factors.
Hermitian symmetry changes the sign of the imaginary pairing, and the exact
kernel of the complex exponential then makes that pairing an integer.
No integrality assumption is added to `UnitaryDatum`.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationUniqueness
namespace UnitaryDatum

variable {p : PeriodDomain} (D : UnitaryDatum p)

/-- The imaginary part of the actual Hermitian form is integral on every
pair of actual period-lattice vectors. -/
theorem imaginary_pairing_integral (l m : p.lattice) :
    ∃ n : ℤ, (D.form l m).im = (n : ℝ) := by
  have hskew : (D.form m l).im = -(D.form l m).im := by
    rw [D.hermitian l m]
    simp only [Complex.star_def, Complex.conj_im]
  have hphase :
      Complex.exp (-((Real.pi : ℂ) * Complex.I * ((D.form l m).im : ℂ))) =
        Complex.exp ((Real.pi : ℂ) * Complex.I * ((D.form l m).im : ℂ)) := by
    apply mul_left_cancel₀ (mul_ne_zero (D.multiplier_ne_zero l) (D.multiplier_ne_zero m))
    calc
      _ = D.multiplier (l + m) := (D.multiplier_add l m).symm
      _ = D.multiplier (m + l) := congrArg D.multiplier (add_comm l m)
      _ = D.multiplier m * D.multiplier l *
          Complex.exp (-((Real.pi : ℂ) * Complex.I * ((D.form m l).im : ℂ))) :=
        D.multiplier_add m l
      _ = _ := by
        rw [hskew, Complex.ofReal_neg, mul_neg, neg_neg,
          mul_comm (D.multiplier m) (D.multiplier l)]
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hphase.symm
  refine ⟨n, ?_⟩
  have hi := congrArg Complex.im hn
  simp [Complex.mul_re, Complex.mul_im] at hi
  apply mul_left_cancel₀ Real.pi_ne_zero
  nlinarith only [hi]

/-- The same integrality statement with membership in the original lattice,
without replacing it by a coordinate model. -/
theorem imaginary_pairing_integral_of_mem (x y : ComplexPlane₂)
    (hx : x ∈ p.lattice) (hy : y ∈ p.lattice) :
    ∃ n : ℤ, (D.form x y).im = (n : ℝ) :=
  D.imaginary_pairing_integral ⟨x, hx⟩ ⟨y, hy⟩

end UnitaryDatum
end Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationUniqueness
