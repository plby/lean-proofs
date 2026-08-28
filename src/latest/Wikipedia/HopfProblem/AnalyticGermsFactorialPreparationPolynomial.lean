import Wikipedia.HopfProblem.AnalyticGermsFactorialPolynomialCoefficients
import Wikipedia.HopfProblem.AnalyticGermsFactorialRootMultiset
import Wikipedia.HopfProblem.AnalyticGermsFactorialMoments
import Wikipedia.HopfProblem.AnalyticGermsFactorialArgumentPrinciple

/-!
# The genuine analytic preparation polynomial

The degree is the actual central-slice zero count. The coefficients are
Newton polynomials in actual contour moments. At every nearby parameter,
the resulting monic polynomial is proved equal to the product over all
actual zeros, with their analytic multiplicities. Thus the analytic slice
factorizations used below are conclusions, not preparation hypotheses.
-/

noncomputable section

open Set Metric Filter Topology Polynomial

namespace Wikipedia.HopfProblem.AnalyticGermsFactorial.PreparationPolynomial

/-- Actual zero count of the central slice inside the chosen circle. -/
def degree (f : ℂ × ℂ → ℂ) (R : ℝ) : ℕ :=
  ∑ᶠ w ∈ ball (0 : ℂ) R, analyticOrderNatAt (fun t => f (0, t)) w

/-- The coefficients are finite algebraic expressions in actual moments. -/
def coefficient (f : ℂ × ℂ → ℂ) (R : ℝ) (j : ℕ) (z : ℂ) : ℂ :=
  (-1) ^ j * Newton.elementary (fun k => Moments.moment f R k z) j

/-- The monic polynomial attached to a slice by contour reconstruction. -/
def slicePolynomial (f : ℂ × ℂ → ℂ) (R : ℝ) (z : ℂ) : ℂ[X] :=
  Newton.polynomial (fun k => Moments.moment f R k z) (degree f R)

/-- Evaluate the preparation polynomial in the second coordinate. -/
def function (f : ℂ × ℂ → ℂ) (R : ℝ) (p : ℂ × ℂ) : ℂ :=
  (slicePolynomial f R p.1).eval p.2

@[simp] theorem coefficient_zero (f : ℂ × ℂ → ℂ) (R : ℝ) (z : ℂ) :
    coefficient f R 0 z = 1 := by simp [coefficient]

theorem slicePolynomial_eq_descending (f : ℂ × ℂ → ℂ) (R : ℝ) (z : ℂ) :
    slicePolynomial f R z =
      Newton.descendingPolynomial (fun j => coefficient f R j z) (degree f R) :=
  Newton.polynomial_eq_descendingPolynomial _ _

theorem slicePolynomial_monic (f : ℂ × ℂ → ℂ) (R : ℝ) (z : ℂ) :
    (slicePolynomial f R z).Monic := Newton.polynomial_monic _ _

theorem slicePolynomial_natDegree (f : ℂ × ℂ → ℂ) (R : ℝ) (z : ℂ) :
    (slicePolynomial f R z).natDegree = degree f R := Newton.polynomial_natDegree _ _

variable {f : ℂ × ℂ → ℂ} {r R : ℝ}

theorem coefficient_analyticOnNhd (hr : 0 < r) (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 r ×ˢ closedBall 0 R))
    (hf0 : ∀ p ∈ closedBall 0 r ×ˢ sphere 0 R, f p ≠ 0) (j : ℕ) :
    AnalyticOnNhd ℂ (coefficient f R j) (ball 0 r) := by
  exact analyticOnNhd_const.mul
    (Newton.elementary_analyticOnNhd (Moments.moment f R)
      (fun k => Moments.moment_analyticOnNhd hr hR hf hf0 k) j)

theorem function_analyticOnNhd (hr : 0 < r) (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 r ×ˢ closedBall 0 R))
    (hf0 : ∀ p ∈ closedBall 0 r ×ˢ sphere 0 R, f p ≠ 0) :
    AnalyticOnNhd ℂ (function f R) (ball (0 : ℂ) r ×ˢ (Set.univ : Set ℂ)) := by
  intro p hp
  exact Newton.polynomial_eval_analyticAt (Moments.moment f R) (degree f R)
    (fun k => Moments.moment_analyticOnNhd hr hR hf hf0 k p.1 hp.1)

/-- Every nearby slice has a genuine analytic nonvanishing factor after
division by the single analytically reconstructed polynomial family. -/
theorem exists_slice_factor (hr : 0 < r) (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 r ×ˢ closedBall 0 R))
    (hf0 : ∀ p ∈ closedBall 0 r ×ˢ sphere 0 R, f p ≠ 0)
    {z : ℂ} (hz : z ∈ ball 0 r) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (closedBall 0 R) ∧
      (∀ w ∈ closedBall 0 R, g w ≠ 0) ∧
      (∀ w : ℂ, f (z, w) = function f R (z, w) * g w) := by
  have hslice : AnalyticOnNhd ℂ (fun w => f (z, w)) (closedBall 0 R) := by
    intro w hw
    exact (hf (z, w) ⟨ball_subset_closedBall hz, hw⟩).comp
      (analyticAt_const.prod analyticAt_id)
  obtain ⟨t, ht, hm, g, hg, hfg, hg0, hmoment⟩ :=
    ArgumentPrinciple.exists_finset_factorization_weightedMoment hslice
      (fun w hw => hf0 (z, w) ⟨ball_subset_closedBall hz, hw⟩) hR
  have hM (k : ℕ) : Moments.moment f R k z =
      ∑ a ∈ t, (analyticOrderNatAt (fun w => f (z, w)) a : ℂ) * a ^ k := by
    rw [Moments.moment_eq_logDeriv]
    exact hmoment k
  have hd : degree f R = ∑ a ∈ t, analyticOrderNatAt (fun w => f (z, w)) a := by
    apply Nat.cast_injective (R := ℂ)
    calc
      (degree f R : ℂ) = Moments.moment f R 0 0 :=
        (Moments.moment_zero_eq_finsum hR hf hf0 (mem_closedBall_self hr.le)).symm
      _ = Moments.moment f R 0 z :=
        (Moments.moment_zero_eq_zero_slice hr hR hf hf0 hz).symm
      _ = _ := by simpa using hM 0
  have hP : slicePolynomial f R z =
      ∏ a ∈ t, (X - C a) ^ analyticOrderNatAt (fun w => f (z, w)) a := by
    unfold slicePolynomial
    simp_rw [hM]
    rw [hd]
    exact rootMultiset_polynomial _ _
  refine ⟨g, hg, hg0, ?_⟩
  intro w
  calc
    f (z, w) = (∏ a ∈ t, (w - a) ^ analyticOrderNatAt (fun w => f (z, w)) a) * g w :=
      congrFun hfg w
    _ = function f R (z, w) * g w := by
      simp only [function, hP, eval_prod, eval_pow, eval_sub, eval_X, eval_C]

/-- The analytically reconstructed polynomial has no zeros on the same
boundary cylinder. -/
theorem function_boundary_ne_zero (hr : 0 < r) (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 r ×ˢ closedBall 0 R))
    (hf0 : ∀ p ∈ closedBall 0 r ×ˢ sphere 0 R, f p ≠ 0)
    {z w : ℂ} (hz : z ∈ ball 0 r) (hw : w ∈ sphere 0 R) :
    function f R (z, w) ≠ 0 := by
  obtain ⟨g, hg, hg0, hfg⟩ := exists_slice_factor hr hR hf hf0 hz
  intro hP
  exact hf0 (z, w) ⟨ball_subset_closedBall hz, hw⟩ (by rw [hfg w, hP, zero_mul])

end Wikipedia.HopfProblem.AnalyticGermsFactorial.PreparationPolynomial
