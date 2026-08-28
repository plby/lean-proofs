import Wikipedia.HopfProblem.CuspExponentials
import Wikipedia.HopfProblem.ToricReduction
import Mathlib.Topology.Algebra.Group.Units

/-!
# Continuous torus actions for cusp straightening

The action is jointly continuous on the actual glued toric space,
including its boundary.  Exponential fibre multipliers preserve the
cusp parameter and change logarithmic position by their real drift.
-/

noncomputable section

open Set Topology
open scoped Matrix

namespace Wikipedia.HopfProblem.ToricSpace

open ToricCharts ToricFan

theorem factors_continuous (s : Triangle) : Continuous (factors s) := by
  apply continuous_pi
  intro i
  change Continuous (fun u : ActingTorus => ∏ j, (u j : ℂ) ^ s.dual i j)
  exact continuous_finsetProd _ (fun j _ =>
    (Units.continuous_val.comp (continuous_apply j)).zpow₀ _
      (fun u => Or.inl (u j).ne_zero))

/-- Joint continuity, not only continuity for each fixed torus element. -/
theorem torusAction_joint_continuous :
    Continuous (fun p : ActingTorus × Space => torusAction p.1 p.2) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨u, x⟩
  obtain ⟨s, z, rfl⟩ := inclusion_jointly_surjective x
  have hlocal : Continuous (fun p : ActingTorus × CoordinateSpace 3 =>
      inclusion s (scale s p.1 p.2)) :=
    (inclusion_openEmbedding s).continuous.comp
      (((factors_continuous s).comp continuous_fst).mul continuous_snd)
  apply (((IsOpenEmbedding.id (X := ActingTorus)).prodMap
    (inclusion_openEmbedding s)).continuousAt_iff
      (g := fun p : ActingTorus × Space => torusAction p.1 p.2) (x := (u, z))).mp
  change ContinuousAt
    (fun p : ActingTorus × CoordinateSpace 3 => torusAction p.1 (inclusion s p.2)) (u, z)
  simpa only [torusAction_inclusion] using hlocal.continuousAt (x := (u, z))

theorem fibreMultiplier_continuous : Continuous fibreMultiplier := by
  apply continuous_pi
  intro i
  fin_cases i
  · exact continuous_apply 0
  · exact continuous_apply 1
  · exact continuous_const

end Wikipedia.HopfProblem.ToricSpace

namespace Wikipedia.HopfProblem.CuspRetraction

open ToricCharts ToricFan ToricSpace CuspUniformization

/-- Real vectors embedded coordinatewise in the complex fibre space. -/
def realToComplex : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℂ) where
  toFun v i := (v i : ℂ)
  map_add' v w := by ext i; simp
  map_smul' a v := by ext i; simp [Complex.real_smul]

@[simp] theorem realToComplex_apply (v : Fin 2 → ℝ) (i : Fin 2) :
    realToComplex v i = (v i : ℂ) := rfl

theorem realToComplex_continuous : Continuous realToComplex := by
  apply continuous_pi
  intro i
  exact Complex.continuous_ofReal.comp (continuous_apply i)

@[simp] theorem norm_realToComplex (v : Fin 2 → ℝ) : ‖realToComplex v‖ = ‖v‖ := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro i
    simpa only [realToComplex_apply, Complex.norm_real] using norm_le_pi_norm v i
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro i
    simpa only [realToComplex_apply, Complex.norm_real] using
      norm_le_pi_norm (realToComplex v) i

def expFibreUnits (a : Fin 2 → ℂ) : Fin 2 → ℂˣ :=
  fun i => Units.mk0 (exponential (a i)) (exponential_ne_zero _)

@[simp] theorem expFibreUnits_coe (a : Fin 2 → ℂ) (i : Fin 2) :
    (expFibreUnits a i : ℂ) = exponential (a i) := rfl

@[simp] theorem expFibreUnits_zero : expFibreUnits 0 = 1 := by
  ext i
  simp [expFibreUnits]

theorem expFibreUnits_add (a b : Fin 2 → ℂ) :
    expFibreUnits (a + b) = expFibreUnits a * expFibreUnits b := by
  ext i
  simp [expFibreUnits, exponential_add]

theorem expFibreUnits_continuous : Continuous expFibreUnits := by
  apply continuous_pi
  intro i
  apply Units.continuous_iff.mpr
  have h : Continuous (fun a : Fin 2 → ℂ => exponential (a i)) :=
    exponential_holomorphic.continuous.comp (continuous_apply i)
  exact ⟨h, h.inv₀ (fun a => exponential_ne_zero (a i))⟩

def expFibreAction (a : Fin 2 → ℂ) (x : Space) : Space :=
  torusAction (fibreMultiplier (expFibreUnits a)) x

@[simp] theorem expFibreAction_zero (x : Space) : expFibreAction 0 x = x := by
  simp [expFibreAction]

theorem expFibreAction_add (a b : Fin 2 → ℂ) (x : Space) :
    expFibreAction a (expFibreAction b x) = expFibreAction (a + b) x := by
  simp only [expFibreAction, torusAction_mul, expFibreUnits_add, fibreMultiplier_mul]

@[simp] theorem time_expFibreAction (a : Fin 2 → ℂ) (x : Space) :
    time (expFibreAction a x) = time x := time_fibreMultiplier _ _

theorem expFibreAction_continuous :
    Continuous (fun p : (Fin 2 → ℂ) × Space => expFibreAction p.1 p.2) := by
  have h : Continuous (fun p : (Fin 2 → ℂ) × Space =>
      (fibreMultiplier (expFibreUnits p.1), p.2)) :=
    ((fibreMultiplier_continuous.comp expFibreUnits_continuous).comp
      continuous_fst).prodMk continuous_snd
  change Continuous ((fun p : ActingTorus × Space => torusAction p.1 p.2) ∘
    (fun p : (Fin 2 → ℂ) × Space => (fibreMultiplier (expFibreUnits p.1), p.2)))
  exact Continuous.comp torusAction_joint_continuous h

theorem expFibreAction_translate (a : Fin 2 → ℂ) (v : Fin 2 → ℤ) (x : Space) :
    expFibreAction a (translate v x) = translate v (expFibreAction a x) :=
  fibreMultiplier_translate _ _ _

theorem torusCoordinates_expFibreAction (a : Fin 2 → ℂ) {x : Space}
    (hx : x ∈ openTorus) (i : Fin 2) :
    torusCoordinates (expFibreAction a x) i.castSucc =
      exponential (a i) * torusCoordinates x i.castSucc := by
  rw [expFibreAction, torusCoordinates_action _ hx]
  fin_cases i <;> rfl

theorem position_expFibreAction (a : Fin 2 → ℂ) {x : Space} (hx : x ∈ openTorus) :
    position (expFibreAction a x) = position x +
      (Real.log ‖time x‖)⁻¹ • (fun i => -2 * Real.pi * (a i).im) := by
  ext i
  simp only [position, time_expFibreAction, logCoordinates, logNorm,
    torusCoordinates_expFibreAction a hx, norm_mul, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]
  rw [Real.log_mul (norm_ne_zero_iff.mpr (exponential_ne_zero _))
    (norm_ne_zero_iff.mpr (torusCoordinates_nonzero hx _)), log_norm_exponential]
  ring

theorem twistedTranslate_eq_expFibreAction
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℤ) (x : Space) :
    twistedTranslate C v x =
      expFibreAction (C (time x) *ᵥ (fun i => (v i : ℂ))) (translate (cuspVector v) x) := by
  unfold twistedTranslate variableMultiplier
  rw [time_translate]
  rfl

@[simp] theorem position_of_time_zero {x : Space} (hx : time x = 0) : position x = 0 := by
  ext i
  simp [position, hx]

end Wikipedia.HopfProblem.CuspRetraction
