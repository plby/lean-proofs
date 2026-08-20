module
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import ErdosProblems.Erdos515.External.Ray.Misc.Complex

/-!
## Snap a complex number to `Circle`
-/

open Classical
open Complex (arg I)
open Set
open scoped ContDiff Real Topology ComplexConjugate
noncomputable section

variable {X : Type} [TopologicalSpace X]

/-- `z / abs z : Circle` -/
public def snap (z : ℂ) : Circle :=
  if n : z = 0 then 1 else ⟨z / ‖z‖, by simp [n, Submonoid.unitSphere, div_self]⟩

public lemma coe_snap {z : ℂ} (z0 : z ≠ 0) : (snap z).val = z / ‖z‖ := by
  simp only [snap, z0, ↓reduceDIte, div_eq_mul_inv]

@[simp] public lemma norm_snap {z : ℂ} : ‖(snap z).val‖ = 1 :=
  Circle.norm_coe _

@[simp] public lemma arg_snap {z : ℂ} (z0 : z ≠ 0) : arg (snap z) = arg z := by
  simp only [snap, z0, ↓reduceDIte, div_eq_mul_inv]
  have e0 : arg ((‖z‖ : ℂ))⁻¹ = 0 := by
    simp only [← Complex.ofReal_inv]
    apply Complex.arg_ofReal_of_nonneg
    bound
  rw [Complex.arg_mul z0]
  · simp only [add_eq_left, e0]
  · simpa only [ne_eq, inv_eq_zero, Complex.ofReal_eq_zero, norm_eq_zero]
  · simp only [e0, add_zero, Complex.arg_mem_Ioc]

public lemma snap_eq_snap_iff {z w : ℂ} (z0 : z ≠ 0) (w0 : w ≠ 0) :
    snap z = snap w ↔ arg z = arg w := by
  simp only [Circle.ext_iff, Complex.ext_norm_arg_iff, norm_snap, arg_snap z0, arg_snap w0,
    true_and]

@[simp] public lemma snap_mul {z w : ℂ} (z0 : z ≠ 0) (w0 : w ≠ 0) :
    snap (z * w) = snap z * snap w := by
  apply Circle.ext
  simp only [Circle.coe_mul, coe_snap z0, coe_snap w0, coe_snap (mul_ne_zero z0 w0),
    Complex.norm_mul, Complex.ofReal_mul]
  rw [div_mul_div_comm]

@[simp] public lemma snap_div {z w : ℂ} (z0 : z ≠ 0) (w0 : w ≠ 0) :
    snap (z / w) = snap z / snap w := by
  apply Circle.ext
  simp only [Circle.coe_div, coe_snap z0, coe_snap w0, coe_snap (div_ne_zero z0 w0),
    Complex.norm_div, Complex.ofReal_div]
  rw [div_div_div_comm]

@[simp] public lemma snap_zero : snap 0 = 1 := by
  simp only [snap, ↓reduceDIte]

@[simp] public lemma snap_of_pos {t : ℝ} (t0 : 0 < t) : snap (t : ℂ) = 1 := by
  apply Circle.ext
  have n : (t : ℂ) ≠ 0 := by exact_mod_cast t0.ne'
  simp only [coe_snap n, Complex.norm_real, Real.norm_eq_abs, abs_of_pos t0, Circle.coe_one]
  rw [div_self n]

@[simp] public lemma snap_mul_of_pos {t : ℝ} (t0 : 0 < t) {z : ℂ} : snap (t * z) = snap z := by
  rcases eq_or_ne z 0 with rfl | z0
  · simp only [mul_zero]
  · have n : (t : ℂ) ≠ 0 := by exact_mod_cast t0.ne'
    apply Circle.ext
    simp only [coe_snap (mul_ne_zero n z0), coe_snap z0, Complex.norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos t0, Complex.ofReal_mul, div_mul_eq_div_div, ne_eq,
      not_false_eq_true, mul_div_cancel_left₀, n]

@[simp] public lemma snap_circle (z : Circle) : snap z.val = z := by
  apply Circle.ext
  simp only [coe_snap z.coe_ne_zero, Circle.norm_coe, Complex.ofReal_one, div_one]

@[simp] public lemma norm_mul_snap {z : ℂ} (z0 : z ≠ 0) : ‖z‖ * (snap z).val = z := by
  have n : (‖z‖ : ℂ) ≠ 0 := by simpa
  simp only [snap, z0, ↓reduceDIte, mul_div_cancel₀ _ n]

/-- Alternative definition using `Set.codRestrict` -/
lemma snap_eq_restrict :
    snap = codRestrict (fun z : ℂ ↦ if z = 0 then 1 else z / ‖z‖) (Submonoid.unitSphere ℂ)
      (by intro z; split_ifs with h; all_goals simp [h]) := by
  ext z
  by_cases z0 : z = 0
  all_goals simp [z0, coe_snap]

public lemma continuousAt_snap {z : ℂ} (z0 : z ≠ 0) : ContinuousAt snap z := by
  have i : Topology.IsInducing ((↑) : Circle → ℂ) := Topology.IsInducing.subtypeVal
  refine i.continuousAt_iff.mpr ?_
  have e : (fun w : ℂ ↦ (snap w).val) =ᶠ[𝓝 z] fun w ↦ w / ‖w‖ := by
    filter_upwards [eventually_ne_nhds z0] with w w0
    exact coe_snap w0
  refine ContinuousAt.congr_of_eventuallyEq ?_ e
  exact continuousAt_id.div (Complex.continuous_ofReal.comp continuous_norm).continuousAt
    (by simpa only [ne_eq, Complex.ofReal_eq_zero, norm_eq_zero])

@[fun_prop] public lemma ContinuousAt.snap_units {f : X → ℂˣ} {x : X} (fc : ContinuousAt f x) :
    ContinuousAt (fun x ↦ snap (f x)) x := by
  refine (continuousAt_snap ?_).comp ?_
  · apply Units.ne_zero
  · exact Units.continuous_val.continuousAt.comp fc

@[fun_prop] public lemma Continuous.snap_units {f : X → ℂˣ} (fc : Continuous f) :
    Continuous (fun x ↦ snap (f x)) := by
  rw [continuous_iff_continuousAt]
  fun_prop

public lemma snap_unit (z : ℂˣ) : snap z = ⟨z / ‖z.val‖, by simp [Submonoid.unitSphere]⟩ := by
  simp only [snap, Units.ne_zero, ↓reduceDIte]
  rfl

@[simp] public lemma snap_exp_mul_I {t : ℝ} : snap (Complex.exp (t * I)) = Circle.exp t := by
  simp [Circle.ext_iff, coe_snap]

@[simp] lemma snap_one : snap 1 = 1 := by
  simp only [snap, one_ne_zero, ↓reduceDIte, norm_one, Complex.ofReal_one, div_one]
  rfl

/-!
### Snap calculus
-/

public lemma analyticAt_snap {z : ℂ} (z0 : z ≠ 0) : AnalyticAt ℝ (fun z ↦ (snap z).val) z := by
  have e : ∀ᶠ w : ℂ in 𝓝 z, (snap w).val = w / ‖w‖ := by
    filter_upwards [eventually_ne_nhds z0]
    aesop (add safe apply [coe_snap])
  refine AnalyticAt.congr ?_ (Filter.EventuallyEq.symm e)
  exact analyticAt_id.div (Complex.analyticAt_norm z0).ofReal (by simpa)

public lemma AnalyticAt.snap {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℂ} {x : E}
    (a : AnalyticAt ℝ f x) (f0 : f x ≠ 0) : AnalyticAt ℝ (fun x ↦ (snap (f x)).val) x :=
  (analyticAt_snap f0).comp a

/-!
### Snap to a unit
-/

section Units

variable {α : Type} [GroupWithZero α]

/-- `Units.mk0` with a default to 1 -/
public def Units.mk1 (x : α) : αˣ :=
  if h : x ≠ 0 then Units.mk0 x h else 1

@[simp] public lemma Units.mk1_zero : Units.mk1 (0 : α) = 1 := by
  simp only [mk1, ne_eq, not_true_eq_false, ↓reduceDIte]

@[simp] public lemma Units.val_mk1 {x : α} (x0 : x ≠ 0) : (Units.mk1 x).val = x := by
  simp only [mk1, ne_eq, x0, not_false_eq_true, ↓reduceDIte, val_mk0]

public lemma Units.continuousAt_mk1 [TopologicalSpace α] [T1Space α] [ContinuousInv₀ α]
    {x : α} (x0 : x ≠ 0) : ContinuousAt (fun x ↦ Units.mk1 x) x := by
  simp only [isInducing_embedProduct.continuousAt_iff, Function.comp_def, embedProduct_apply,
    val_inv_eq_inv_val, MulOpposite.op_inv]
  rw [continuousAt_congr (g := fun x : α ↦ (x, (MulOpposite.op x)⁻¹))]
  · apply continuousAt_id.prodMk
    simp only [← MulOpposite.op_inv]
    exact MulOpposite.continuous_op.continuousAt.comp (continuousAt_inv₀ x0)
  · filter_upwards [eventually_ne_nhds x0]
    aesop

@[simp] public lemma Units.snap_mk1 {x : ℂ} : snap (Units.mk1 x).val = snap x := by
  simp only [snap, mk1, ne_eq, dite_not, ne_zero, ↓reduceDIte]
  aesop

@[simp] public lemma Units.mk1_inj {x y : α} (x0 : x ≠ 0) (y0 : y ≠ 0) :
    Units.mk1 x = Units.mk1 y ↔ x = y := by
  simp only [Units.ext_iff, ne_eq, x0, not_false_eq_true, val_mk1, y0]
