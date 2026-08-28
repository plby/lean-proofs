import Wikipedia.NoExoticSixSphere.SphereNormalization
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# Radial extension of norm-preserving sphere actions

The action may vary over an arbitrary parameter space. Multiplying by
the radius makes its extension jointly continuous even where the direction
is undefined. This is the analytic input for an actual Hopf construction
on an orthogonal family; no stable homotopy comparison is asserted here.
-/

noncomputable section

open scoped Topology
open Set Filter NoExoticSixSphere

namespace Wikipedia.HopfProblem.DegreeCollapse.RadialSphereAction

variable {P E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def direction (a : E) (ha : a ≠ 0) : UnitSphere E :=
  ⟨NormedSpace.normalize a, by
    simpa only [mem_sphere_zero_iff_norm] using NormedSpace.norm_normalize ha⟩

def value (A : P → UnitSphere E → F → F) (p : P) (a : E) (b : F) : F := by
  classical
  exact if ha : a = 0 then 0 else ‖a‖ • A p (direction a ha) b

theorem value_zero (A : P → UnitSphere E → F → F) (p : P) (b : F) :
    value A p 0 b = 0 := by
  simp [value]

theorem value_of_ne_zero (A : P → UnitSphere E → F → F)
    (p : P) (a : E) (b : F) (ha : a ≠ 0) :
    value A p a b = ‖a‖ • A p (direction a ha) b := by
  simp only [value, dif_neg ha]

theorem value_norm (A : P → UnitSphere E → F → F)
    (hA : ∀ p a b, ‖A p a b‖ = ‖b‖) (p : P) (a : E) (b : F) :
    ‖value A p a b‖ = ‖a‖ * ‖b‖ := by
  by_cases ha : a = 0
  · subst a
    simp only [value_zero, norm_zero, zero_mul]
  · rw [value_of_ne_zero A p a b ha, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg a), hA]

theorem value_zero_right (A : P → UnitSphere E → F → F)
    (hA : ∀ p a b, ‖A p a b‖ = ‖b‖) (p : P) (a : E) :
    value A p a 0 = 0 := by
  apply norm_eq_zero.mp
  rw [value_norm A hA, norm_zero, mul_zero]

theorem continuous_value [TopologicalSpace P] (A : P → UnitSphere E → F → F)
    (hA : ∀ p a b, ‖A p a b‖ = ‖b‖)
    (hc : Continuous (fun z : P × (UnitSphere E × F) ↦ A z.1 z.2.1 z.2.2)) :
    Continuous (fun z : P × (E × F) ↦ value A z.1 z.2.1 z.2.2) := by
  let U : Set (P × (E × F)) := {z | z.2.1 ≠ 0}
  have hU : IsOpen U :=
    (isClosed_eq (continuous_fst.comp continuous_snd) continuous_const).isOpen_compl
  have haway : ContinuousOn (fun z : P × (E × F) ↦ value A z.1 z.2.1 z.2.2) U := by
    rw [continuousOn_iff_continuous_domRestrict]
    let d : U → UnitSphere E := fun z ↦ direction z.val.2.1 z.property
    have ha : Continuous (fun z : U ↦ z.val.2.1) := continuous_subtype_val.snd.fst
    have hd : Continuous d := by
      apply Continuous.subtype_mk
      exact (ha.norm.inv₀ (fun z ↦ norm_ne_zero_iff.mpr z.property)).smul ha
    have hb : Continuous (fun z : U ↦ A z.val.1 (d z) z.val.2.2) :=
      hc.comp (continuous_subtype_val.fst.prodMk (hd.prodMk continuous_subtype_val.snd.snd))
    convert ha.norm.smul hb using 1
    funext z
    exact value_of_ne_zero A z.val.1 z.val.2.1 z.val.2.2 z.property
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hz : z.2.1 = 0
  · change Tendsto _ (𝓝 z) (𝓝 (value A z.1 z.2.1 z.2.2))
    rw [hz, value_zero]
    apply squeeze_zero_norm
      (fun w : P × (E × F) ↦ (value_norm A hA w.1 w.2.1 w.2.2).le)
    have ht := ((continuous_snd.fst.norm).mul (continuous_snd.snd.norm)).continuousAt
      (x := z)
    change Tendsto (fun w : P × (E × F) ↦ ‖w.2.1‖ * ‖w.2.2‖)
      (𝓝 z) (𝓝 (‖z.2.1‖ * ‖z.2.2‖)) at ht
    simpa only [hz, norm_zero, zero_mul] using ht
  · exact haway.continuousAt (hU.mem_nhds hz)

theorem value_const (B : F → F) (p : P) (a : E) (b : F) :
    value (fun (_ : P) (_ : UnitSphere E) ↦ B) p a b = ‖a‖ • B b := by
  by_cases ha : a = 0
  · subst a
    simp only [value_zero, norm_zero, zero_smul]
  · exact value_of_ne_zero _ p a b ha

end Wikipedia.HopfProblem.DegreeCollapse.RadialSphereAction
