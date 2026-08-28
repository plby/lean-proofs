import Wikipedia.SmoothSixDPoincare.MorseCriticalPoints
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Pow

/-!
# The cubic model for a cancelling pair of Morse critical points

The parameter crosses the unique degenerate critical point of a cubic
plus a nondegenerate transverse quadratic form. The actual differential
is computed, and the critical set is identified exactly. Localization of
the parameter change is separate; no global cancellation is asserted here.
-/

noncomputable section

open Set
open scoped ContDiff BigOperators

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

abbrev Model (m : ℕ) := ℝ × (Fin m → ℝ)

variable {m : ℕ} (σ : Fin m → ℝ)

def cubic (t : ℝ) (p : Model m) : ℝ :=
  p.1 ^ 3 / 3 + t * p.1 + ∑ i, σ i * (p.2 i) ^ 2

def differential (t : ℝ) (p : Model m) : Model m →L[ℝ] ℝ :=
  (p.1 ^ 2 + t) • ContinuousLinearMap.fst ℝ ℝ (Fin m → ℝ) +
    ∑ i, (2 * σ i * p.2 i) •
      ((ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℝ ℝ (Fin m → ℝ)))

theorem differential_apply (t : ℝ) (p v : Model m) :
    differential σ t p v =
      (p.1 ^ 2 + t) * v.1 + ∑ i, 2 * σ i * p.2 i * v.2 i := by
  simp [differential]

theorem contDiff_cubic_family :
    ContDiff ℝ ∞ (fun p : ℝ × Model m => cubic σ p.1 p.2) := by
  unfold cubic
  fun_prop

theorem contDiff_cubic (t : ℝ) : ContDiff ℝ ∞ (cubic σ t) :=
  (contDiff_cubic_family σ).comp (contDiff_const.prodMk contDiff_id)

theorem hasFDerivAt_cubic (t : ℝ) (p : Model m) :
    HasFDerivAt (cubic σ t) (differential σ t p) p := by
  have hx := (ContinuousLinearMap.fst ℝ ℝ (Fin m → ℝ)).hasFDerivAt (x := p)
  have hy (i : Fin m) :=
    ((ContinuousLinearMap.proj i).comp
      (ContinuousLinearMap.snd ℝ ℝ (Fin m → ℝ))).hasFDerivAt (x := p)
  have hq := HasFDerivAt.fun_sum (u := Finset.univ)
    (fun i _ => ((hy i).pow 2).const_mul (σ i))
  convert! (((hx.pow 3).mul_const (1 / 3)).add (hx.const_mul t)).add hq using 1
  · funext q
    simp [cubic, div_eq_mul_inv]
  · apply ContinuousLinearMap.ext
    intro v
    simp [differential]
    ring_nf

theorem fderiv_cubic (t : ℝ) (p : Model m) :
    fderiv ℝ (cubic σ t) p = differential σ t p :=
  (hasFDerivAt_cubic σ t p).fderiv

/-- No hidden critical points occur off the scalar axis. -/
theorem critical_iff (hσ : ∀ i, σ i ≠ 0) (t : ℝ) (p : Model m) :
    fderiv ℝ (cubic σ t) p = 0 ↔ p.1 ^ 2 + t = 0 ∧ p.2 = 0 := by
  rw [fderiv_cubic]
  constructor
  · intro h
    have hx := congrArg (fun L : Model m →L[ℝ] ℝ => L (1, 0)) h
    have hx' : p.1 ^ 2 + t = 0 := by simpa [differential_apply] using hx
    refine ⟨hx', ?_⟩
    funext i
    have hy := congrArg (fun L : Model m →L[ℝ] ℝ => L (0, Pi.single i 1)) h
    have hy' : 2 * σ i * p.2 i = 0 := by
      simpa [differential_apply, Pi.single_apply] using hy
    exact (mul_eq_zero.mp hy').resolve_left (mul_ne_zero (by norm_num) (hσ i))
  · rintro ⟨hx, hy⟩
    apply ContinuousLinearMap.ext
    intro v
    simp [differential_apply, hx, hy]

theorem cubic_zero_unique_critical (hσ : ∀ i, σ i ≠ 0) (p : Model m) :
    fderiv ℝ (cubic σ 0) p = 0 ↔ p = 0 := by
  rw [critical_iff σ hσ]
  constructor
  · rintro ⟨hx, hy⟩
    have hx' : p.1 = 0 := by nlinarith [sq_nonneg p.1]
    exact Prod.ext hx' hy
  · rintro rfl
    simp

theorem positive_parameter_no_critical (hσ : ∀ i, σ i ≠ 0) {t : ℝ}
    (ht : 0 < t) (p : Model m) : fderiv ℝ (cubic σ t) p ≠ 0 := by
  intro h
  have hx := ((critical_iff σ hσ t p).mp h).1
  nlinarith [sq_nonneg p.1]

/-- A negative parameter gives exactly the two critical points, with no others. -/
theorem negative_parameter_critical_iff (hσ : ∀ i, σ i ≠ 0) (a : ℝ) (p : Model m) :
    fderiv ℝ (cubic σ (-(a ^ 2))) p = 0 ↔ p = (a, 0) ∨ p = (-a, 0) := by
  rw [critical_iff σ hσ]
  constructor
  · rintro ⟨hx, hy⟩
    have hs : p.1 = a ∨ p.1 = -a := by
      have he : (p.1 - a) * (p.1 + a) = 0 := by nlinarith
      rcases mul_eq_zero.mp he with h | h
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    exact hs.elim (fun h => Or.inl (Prod.ext h hy))
      (fun h => Or.inr (Prod.ext h hy))
  · rintro (rfl | rfl) <;> simp

theorem cubic_critical_values (a : ℝ) :
    cubic σ (-(a ^ 2)) (a, 0) = -(2 * a ^ 3 / 3) ∧
      cubic σ (-(a ^ 2)) (-a, 0) = 2 * a ^ 3 / 3 := by
  constructor <;> simp [cubic] <;> ring

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
