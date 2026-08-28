import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Topology.Homotopy.Lifting

/-!
# Actual winding through the exponential covering

The winding number of a based loop in the punctured complex plane is the
endpoint of its unique logarithmic lift beginning at zero, divided by
`2πi`. The lift is supplied by the actual exponential covering map.
Explicit logarithmic paths compute this invariant; they do not define it.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusLineBundle.Chern

open Topology unitInterval

/-- The actual punctured complex plane, with its subspace topology. -/
abbrev PuncturedPlane := {z : ℂ // z ≠ 0}

/-- The basepoint used for winding. -/
def puncturedOne : PuncturedPlane := ⟨1, one_ne_zero⟩

/-- Genuine continuous based loops in the punctured plane. -/
abbrev BasedLoop := Path puncturedOne puncturedOne

@[simp] theorem puncturedOne_coe : (puncturedOne : ℂ) = 1 := rfl

/-- The logarithmic lift obtained from the actual exponential covering. -/
def normalizedLoopLog (γ : BasedLoop) : C(I, ℂ) :=
  Complex.isCoveringMap_exp.liftPath γ 0 (by
    exact γ.source.trans (Subtype.ext Complex.exp_zero.symm))

@[simp] theorem normalizedLoopLog_zero (γ : BasedLoop) : normalizedLoopLog γ 0 = 0 :=
  Complex.isCoveringMap_exp.liftPath_zero ..

theorem normalizedLoopLog_exp (γ : BasedLoop) (t : I) :
    Complex.exp (normalizedLoopLog γ t) = (γ t : ℂ) := by
  exact congrArg Subtype.val
    (congrFun (Complex.isCoveringMap_exp.liftPath_lifts γ 0 (by
      exact γ.source.trans (Subtype.ext Complex.exp_zero.symm))) t)

theorem normalizedLoopLog_exp_one (γ : BasedLoop) :
    Complex.exp (normalizedLoopLog γ 1) = 1 := by
  rw [normalizedLoopLog_exp, γ.target]
  rfl

/-- The integer represented by an exponential period is unique. -/
theorem int_mul_two_pi_I_injective :
    Function.Injective (fun n : ℤ => (n : ℂ) * (2 * Real.pi * Complex.I)) := by
  intro m n h
  have hmn : (m : ℂ) = n := mul_right_cancel₀ Complex.two_pi_I_ne_zero h
  exact_mod_cast hmn

/-- The endpoint of a based logarithmic lift is one unique exponential period. -/
theorem existsUnique_normalizedLoopLog_endpoint (γ : BasedLoop) :
    ∃! n : ℤ, normalizedLoopLog γ 1 = (n : ℂ) * (2 * Real.pi * Complex.I) := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp (normalizedLoopLog_exp_one γ)
  refine ⟨n, hn, ?_⟩
  intro m hm
  exact int_mul_two_pi_I_injective (hm.symm.trans hn)

/-- Genuine integer winding, defined by lifting the loop through `exp`. -/
def windingNumber (γ : BasedLoop) : ℤ :=
  (existsUnique_normalizedLoopLog_endpoint γ).choose

theorem normalizedLoopLog_endpoint (γ : BasedLoop) :
    normalizedLoopLog γ 1 = (windingNumber γ : ℂ) * (2 * Real.pi * Complex.I) :=
  (existsUnique_normalizedLoopLog_endpoint γ).choose_spec.1

/-- Uniqueness of the logarithmic lift on the interval. -/
theorem logPath_eq_normalizedLoopLog (γ : BasedLoop) (b : I → ℂ)
    (hb : Continuous b) (hb0 : b 0 = 0)
    (hexp : ∀ t, Complex.exp (b t) = (γ t : ℂ)) :
    b = normalizedLoopLog γ := by
  apply Complex.isCoveringMap_exp.eq_of_comp_eq hb (normalizedLoopLog γ).continuous
    ?_ 0 (hb0.trans (normalizedLoopLog_zero γ).symm)
  funext t
  exact Subtype.ext ((hexp t).trans (normalizedLoopLog_exp γ t).symm)

/-- Any supplied logarithmic path computes the winding of the actual loop. -/
theorem windingNumber_eq_iff_of_logPath (γ : BasedLoop) (b : I → ℂ)
    (hb : Continuous b) (hb0 : b 0 = 0)
    (hexp : ∀ t, Complex.exp (b t) = (γ t : ℂ)) (n : ℤ) :
    windingNumber γ = n ↔ b 1 = (n : ℂ) * (2 * Real.pi * Complex.I) := by
  rw [logPath_eq_normalizedLoopLog γ b hb hb0 hexp, normalizedLoopLog_endpoint]
  exact ⟨fun h => congrArg (fun m : ℤ => (m : ℂ) * (2 * Real.pi * Complex.I)) h,
    fun h => int_mul_two_pi_I_injective h⟩

/-- Endpoint form of the computation theorem. -/
theorem windingNumber_of_logPath (γ : BasedLoop) (b : I → ℂ)
    (hb : Continuous b) (hb0 : b 0 = 0)
    (hexp : ∀ t, Complex.exp (b t) = (γ t : ℂ)) (n : ℤ)
    (hb1 : b 1 = (n : ℂ) * (2 * Real.pi * Complex.I)) : windingNumber γ = n :=
  (windingNumber_eq_iff_of_logPath γ b hb hb0 hexp n).mpr hb1

/-- A logarithmic path with any initial value computes winding by its endpoint difference. -/
theorem windingNumber_eq_iff_of_logPath_difference (γ : BasedLoop) (b : I → ℂ)
    (hb : Continuous b) (hexp : ∀ t, Complex.exp (b t) = (γ t : ℂ)) (n : ℤ) :
    windingNumber γ = n ↔ b 1 - b 0 = (n : ℂ) * (2 * Real.pi * Complex.I) := by
  have he0 : Complex.exp (b 0) = 1 :=
    (hexp 0).trans (congrArg Subtype.val γ.source)
  apply windingNumber_eq_iff_of_logPath γ (fun t => b t - b 0)
    (hb.sub continuous_const) (sub_self _)
  intro t
  rw [Complex.exp_sub, hexp t, he0, div_one]

/-- Winding is invariant under genuine endpoint-preserving path homotopies. -/
theorem windingNumber_homotopic {γ δ : BasedLoop} (h : γ.Homotopic δ) :
    windingNumber γ = windingNumber δ := by
  apply int_mul_two_pi_I_injective
  change (windingNumber γ : ℂ) * (2 * Real.pi * Complex.I) =
    (windingNumber δ : ℂ) * (2 * Real.pi * Complex.I)
  rw [← normalizedLoopLog_endpoint, ← normalizedLoopLog_endpoint]
  exact Complex.isCoveringMap_exp.liftPath_apply_one_eq_of_homotopicRel h 0 _ _

/-- The counterclockwise exponential loop, traversed `n` times. -/
def exponentialLoop (n : ℤ) : BasedLoop where
  toFun t := ⟨Complex.exp ((t : ℝ) * ((n : ℂ) * (2 * Real.pi * Complex.I))),
    Complex.exp_ne_zero _⟩
  continuous_toFun := by fun_prop
  source' := by apply Subtype.ext; simp [puncturedOne]
  target' := by
    apply Subtype.ext
    simp [puncturedOne]

@[simp] theorem windingNumber_exponentialLoop (n : ℤ) :
    windingNumber (exponentialLoop n) = n := by
  apply windingNumber_of_logPath (exponentialLoop n)
    (fun t : I => (t : ℝ) * ((n : ℂ) * (2 * Real.pi * Complex.I)))
    (by fun_prop) (by simp) (fun _ => rfl) n
  simp

/-- The positive `exp(2πit)` generator has winding `+1`. -/
theorem windingNumber_positive_generator : windingNumber (exponentialLoop 1) = 1 :=
  windingNumber_exponentialLoop 1

@[simp] theorem windingNumber_refl : windingNumber (Path.refl puncturedOne) = 0 := by
  apply windingNumber_of_logPath (Path.refl puncturedOne) (fun _ => 0)
    continuous_const rfl (fun _ => Complex.exp_zero) 0
  simp

end Wikipedia.HopfProblem.PeriodTorusLineBundle.Chern
