import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Averaging over the original period-one real action

The average is the ordinary Bochner interval integral over `[0,1]`.
Continuity and integrability concern the given action and the given map;
no topology, atlas, or action is replaced.  The addition and period-one
laws are explicit inputs, rather than an assumed invariance of the average.
-/

noncomputable section

open MeasureTheory Set

namespace Wikipedia.HopfProblem.SmoothCircleAverage

variable {M F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The literal average over one period of the given real action. -/
def average (act : ℝ → M → M) (g : M → F) (x : M) : F :=
  ∫ t in (0 : ℝ)..1, g (act t x)

@[simp] theorem average_apply (act : ℝ → M → M) (g : M → F) (x : M) :
    average act g x = ∫ t in (0 : ℝ)..1, g (act t x) := rfl

section Continuity

omit [NormedSpace ℝ F]

variable [TopologicalSpace M] {g : M → F}

theorem continuous_integrand (act : ℝ → M → M)
    (hact : Continuous (fun p : ℝ × M => act p.1 p.2)) (hg : Continuous g) :
    Continuous (fun p : ℝ × M => g (act p.1 p.2)) := hg.comp hact

theorem continuous_parametric_integrand (act : ℝ → M → M)
    (hact : Continuous (fun p : ℝ × M => act p.1 p.2)) (hg : Continuous g) :
    Continuous (fun p : M × ℝ => g (act p.2 p.1)) :=
  (continuous_integrand act hact hg).comp (continuous_snd.prodMk continuous_fst)

/-- Each original time orbit gives a continuous vector-valued integrand. -/
theorem orbit_continuous (act : ℝ → M → M)
    (hact : Continuous (fun p : ℝ × M => act p.1 p.2)) (hg : Continuous g) (x : M) :
    Continuous (fun t : ℝ => g (act t x)) :=
  (continuous_integrand act hact hg).comp (continuous_id.prodMk continuous_const)

/-- Strong measurability follows from the original continuous time orbit. -/
theorem orbit_stronglyMeasurable (act : ℝ → M → M)
    (hact : Continuous (fun p : ℝ × M => act p.1 p.2)) (hg : Continuous g) (x : M) :
    StronglyMeasurable (fun t : ℝ => g (act t x)) :=
  (orbit_continuous act hact hg x).stronglyMeasurable

theorem orbit_aestronglyMeasurable (act : ℝ → M → M)
    (hact : Continuous (fun p : ℝ × M => act p.1 p.2)) (hg : Continuous g)
    (x : M) (μ : Measure ℝ) : AEStronglyMeasurable (fun t : ℝ => g (act t x)) μ :=
  (orbit_stronglyMeasurable act hact hg x).aestronglyMeasurable

/-- All finite time intervals are genuinely Bochner-integrable. -/
theorem orbit_intervalIntegrable (act : ℝ → M → M)
    (hact : Continuous (fun p : ℝ × M => act p.1 p.2)) (hg : Continuous g)
    (x : M) (a b : ℝ) : IntervalIntegrable (fun t : ℝ => g (act t x)) volume a b :=
  (orbit_continuous act hact hg x).intervalIntegrable a b

end Continuity

omit [NormedAddCommGroup F] [NormedSpace ℝ F] in
theorem orbit_periodic (act : ℝ → M → M)
    (hperiod : ∀ (t : ℝ) (x : M), act (t + 1) x = act t x)
    (g : M → F) (x : M) : Function.Periodic (fun t => g (act t x)) 1 :=
  fun t => congrArg g (hperiod t x)

/-- Translation through one whole original period proves invariance of the average. -/
theorem average_invariant (act : ℝ → M → M)
    (hadd : ∀ (t s : ℝ) (x : M), act (t + s) x = act t (act s x))
    (hperiod : ∀ (t : ℝ) (x : M), act (t + 1) x = act t x)
    (g : M → F) (s : ℝ) (x : M) : average act g (act s x) = average act g x := by
  have hfun : (fun t : ℝ => g (act t (act s x))) = fun t => g (act (t + s) x) :=
    funext (fun t => congrArg g (hadd t s x).symm)
  unfold average
  rw [hfun, intervalIntegral.integral_comp_add_right (fun t => g (act t x)) s,
    zero_add, add_comm (1 : ℝ) s]
  simpa only [zero_add] using (orbit_periodic act hperiod g x).intervalIntegral_add_eq s 0

theorem average_congr_orbit (act : ℝ → M → M) (g h : M → F) (x : M)
    (heq : ∀ t : ℝ, g (act t x) = h (act t x)) : average act g x = average act h x := by
  unfold average
  apply intervalIntegral.integral_congr
  intro t _
  exact heq t

section Complete

variable [CompleteSpace F]

@[simp] theorem average_const (act : ℝ → M → M) (c : F) (x : M) :
    average act (fun _ => c) x = c := by
  simp only [average, intervalIntegral.integral_const, sub_zero, one_smul]

theorem average_eq_of_orbit_const (act : ℝ → M → M) (g : M → F) (x : M) (c : F)
    (heq : ∀ t : ℝ, g (act t x) = c) : average act g x = c :=
  (average_congr_orbit act g (fun _ => c) x heq).trans (average_const act c x)

theorem average_eq_of_invariant (act : ℝ → M → M) (f : M → F)
    (hf : ∀ (t : ℝ) (x : M), f (act t x) = f x) (x : M) : average act f x = f x :=
  average_eq_of_orbit_const act f x (f x) (fun t => hf t x)

/-- The original prescribed values are preserved on every action-invariant relative set. -/
theorem average_eqOn_of_invariant (act : ℝ → M → M) (g f : M → F) {S : Set M}
    (hS : ∀ t : ℝ, MapsTo (act t) S S) (heq : EqOn g f S)
    (hf : ∀ (t : ℝ) (x : M), f (act t x) = f x) : EqOn (average act g) f S := by
  intro x hx
  apply average_eq_of_orbit_const act g x (f x)
  intro t
  exact (heq (hS t hx)).trans (hf t x)

/-- Applying the same period average twice does not change it. -/
theorem average_idempotent (act : ℝ → M → M)
    (hadd : ∀ (t s : ℝ) (x : M), act (t + s) x = act t (act s x))
    (hperiod : ∀ (t : ℝ) (x : M), act (t + 1) x = act t x)
    (g : M → F) (x : M) : average act (average act g) x = average act g x :=
  average_eq_of_invariant act (average act g) (average_invariant act hadd hperiod g) x

end Complete

end Wikipedia.HopfProblem.SmoothCircleAverage
