import Wikipedia.HopfProblem.SpecialPeriodsTriangleCusp
import Mathlib.Analysis.Analytic.Constructions

/-!
# Cusp regularity and division by the simple mu pole

Cusp regularity means agreement, sufficiently high in the actual cusp,
with an analytic germ in the normalized exponential coordinate.  It is
preserved by subtraction.  If a cusp-regular function factors through a
function of the form `q⁻¹ v(q)`, with `v` an analytic unit, its other
factor has an analytic cusp germ whose value at the cusp is zero.

The factor statement is local at the cusp and needs no global
holomorphy or triangle-invariance assumption on the factor.
-/

noncomputable section

open Filter UpperHalfPlane
open scoped Topology

namespace Wikipedia.HopfProblem.SpecialPeriods.MuTorsor

/-- A function is regular at the actual triangle cusp when it agrees
there with an analytic germ in the normalized exponential coordinate. -/
def CuspRegular (f : ℍ → ℂ) : Prop :=
  ∃ M : ℂ → ℂ, AnalyticAt ℂ M 0 ∧
    ∀ᶠ z in UpperHalfPlane.atImInfty, f z = M (Triangle.cuspQ z)

/-- Constants have constant analytic cusp germs. -/
theorem CuspRegular.const (c : ℂ) : CuspRegular (fun _ : ℍ => c) :=
  ⟨fun _ => c, analyticAt_const, Filter.Eventually.of_forall fun _ => rfl⟩

/-- The zero function is regular at the actual cusp. -/
theorem CuspRegular.zero : CuspRegular (0 : ℍ → ℂ) := CuspRegular.const 0

/-- Subtracting cusp-regular functions subtracts their analytic cusp
germs on a common sufficiently high cusp neighbourhood. -/
theorem CuspRegular.sub {f g : ℍ → ℂ}
    (hf : CuspRegular f) (hg : CuspRegular g) : CuspRegular (f - g) := by
  obtain ⟨M, hM, hfM⟩ := hf
  obtain ⟨N, hN, hgN⟩ := hg
  refine ⟨M - N, hM.sub hN, ?_⟩
  filter_upwards [hfM, hgN] with z hfz hgz
  simp only [Pi.sub_apply, hfz, hgz]

/-- Dividing a cusp-regular numerator by an actual simple cusp pole
produces an analytic cusp germ vanishing at zero. -/
theorem factor_cusp_germ {ν F H : ℍ → ℂ} {v : ℂ → ℂ}
    (hνc : CuspRegular ν) (hv : AnalyticAt ℂ v 0) (hv0 : v 0 ≠ 0)
    (hF : ∀ᶠ z in UpperHalfPlane.atImInfty,
      F z = (Triangle.cuspQ z)⁻¹ * v (Triangle.cuspQ z))
    (hfac : ∀ z : ℍ, ν z = F z * H z) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧ g 0 = 0 ∧
      ∀ᶠ z in UpperHalfPlane.atImInfty, H z = g (Triangle.cuspQ z) := by
  obtain ⟨M, hM, hνM⟩ := hνc
  refine ⟨fun q => q * M q / v q, (analyticAt_id.mul hM).div hv hv0, by simp, ?_⟩
  have hvne : ∀ᶠ z in UpperHalfPlane.atImInfty, v (Triangle.cuspQ z) ≠ 0 :=
    (Triangle.cuspQ_tendsto_atImInfty.mono_right nhdsWithin_le_nhds).eventually
      (hv.continuousAt.eventually_ne hv0)
  filter_upwards [hνM, hF, hvne] with z hνz hFz hvz
  apply (eq_div_iff hvz).mpr
  have he := hfac z
  rw [hνz, hFz] at he
  calc
    H z * v (Triangle.cuspQ z) = v (Triangle.cuspQ z) * H z := mul_comm _ _
    _ = (Triangle.cuspQ z * (Triangle.cuspQ z)⁻¹) *
        (v (Triangle.cuspQ z) * H z) := by
      rw [mul_inv_cancel₀ (Triangle.cuspQ_ne_zero z), one_mul]
    _ = Triangle.cuspQ z * ((Triangle.cuspQ z)⁻¹ * v (Triangle.cuspQ z) * H z) := by
      ring
    _ = Triangle.cuspQ z * M (Triangle.cuspQ z) := by rw [← he]

end Wikipedia.HopfProblem.SpecialPeriods.MuTorsor
