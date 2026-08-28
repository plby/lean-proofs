import Wikipedia.HopfProblem.DegreeCollapseCubicTimeChart
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# The full transverse cubic flow cylinder

The explicit longitudinal time chart and exponential transverse solutions
give a genuine smooth cylinder on the entire open strip between the cubic
critical points. Its time curves solve the exact cubic field, including
all transverse coordinates.
-/

noncomputable section

open Set Function
open scoped Topology ContDiff Manifold

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {m : ℕ}

def cubicFlowCylinder (σ : Fin m → ℝ) (a : ℝ) (p : (Fin m → ℝ) × ℝ) : Model m :=
  (cubicAxisParameter a p.2, fun i => Real.exp (-σ i * p.2) * p.1 i)

def cubicFlowCylinderInverse (σ : Fin m → ℝ) (a : ℝ) (p : Model m) : (Fin m → ℝ) × ℝ :=
  (fun i => Real.exp (σ i * cubicAxisClock a p.1) * p.2 i, cubicAxisClock a p.1)

theorem cubicFlowCylinder_left_inv (σ : Fin m → ℝ) {a : ℝ} (ha : 0 < a)
    (p : (Fin m → ℝ) × ℝ) :
    cubicFlowCylinderInverse σ a (cubicFlowCylinder σ a p) = p := by
  apply Prod.ext
  · funext i
    change Real.exp (σ i * cubicAxisClock a (cubicAxisParameter a p.2)) *
      (Real.exp (-σ i * p.2) * p.1 i) = p.1 i
    rw [cubicAxisClock_parameter ha, ← mul_assoc, ← Real.exp_add, neg_mul,
      add_neg_cancel, Real.exp_zero, one_mul]
  · exact cubicAxisClock_parameter ha p.2

theorem cubicFlowCylinder_right_inv (σ : Fin m → ℝ) {a : ℝ} (ha : 0 < a)
    {p : Model m} (hp : p.1 ∈ Ioo (-a) a) :
    cubicFlowCylinder σ a (cubicFlowCylinderInverse σ a p) = p := by
  apply Prod.ext
  · exact cubicAxisParameter_clock ha hp
  · funext i
    change Real.exp (-σ i * cubicAxisClock a p.1) *
      (Real.exp (σ i * cubicAxisClock a p.1) * p.2 i) = p.2 i
    rw [← mul_assoc, ← Real.exp_add, neg_mul, neg_add_cancel, Real.exp_zero, one_mul]

theorem contDiff_cubicFlowCylinder (σ : Fin m → ℝ) (a : ℝ) :
    ContDiff ℝ ∞ (cubicFlowCylinder σ a) := by
  apply ((contDiff_cubicAxisParameter a).comp contDiff_snd).prodMk
  apply contDiff_pi.mpr
  intro i
  fun_prop

theorem contDiffOn_cubicFlowCylinderInverse (σ : Fin m → ℝ) {a : ℝ} (ha : 0 < a) :
    ContDiffOn ℝ ∞ (cubicFlowCylinderInverse σ a) (Ioo (-a) a ×ˢ univ) := by
  have ht : ContDiffOn ℝ ∞ (fun p : Model m => cubicAxisClock a p.1) (Ioo (-a) a ×ˢ univ) :=
    (contDiffOn_cubicAxisClock ha).comp contDiffOn_fst (fun _ hp => hp.1)
  apply ContDiffOn.prodMk ?_ ht
  apply contDiffOn_pi.mpr
  intro i
  exact (Real.contDiff_exp.comp_contDiffOn (contDiffOn_const.mul ht)).mul
    (((contDiff_apply ℝ ℝ i).comp contDiff_snd).contDiffOn)

/-- Complete cubic time and transverse coordinates form an actual open-strip diffeomorphism. -/
def cubicFlowCylinderChart (σ : Fin m → ℝ) {a : ℝ} (ha : 0 < a) :
    PartialDiffeomorph 𝓘(ℝ, (Fin m → ℝ) × ℝ) 𝓘(ℝ, Model m)
      ((Fin m → ℝ) × ℝ) (Model m) ∞ where
  toFun := cubicFlowCylinder σ a
  invFun := cubicFlowCylinderInverse σ a
  source := univ
  target := Ioo (-a) a ×ˢ univ
  map_source' p _ := ⟨cubicAxisParameter_mem ha p.2, mem_univ _⟩
  map_target' _ _ := mem_univ _
  left_inv' p _ := cubicFlowCylinder_left_inv σ ha p
  right_inv' _ hp := cubicFlowCylinder_right_inv σ ha hp.1
  open_source := isOpen_univ
  open_target := isOpen_Ioo.prod isOpen_univ
  contMDiffOn_toFun := (contDiff_cubicFlowCylinder σ a).contMDiff.contMDiffOn
  contMDiffOn_invFun := (contDiffOn_cubicFlowCylinderInverse σ ha).contMDiffOn

/-- Every time line in the full cylinder solves the actual cubic field. -/
theorem hasDerivAt_cubicFlowCylinder (σ : Fin m → ℝ) (a : ℝ) (z : Fin m → ℝ) (t : ℝ) :
    HasDerivAt (fun s => cubicFlowCylinder σ a (z, s))
      (cubicDescent σ (-(a ^ 2)) (cubicFlowCylinder σ a (z, t))) t := by
  have hz : HasDerivAt (fun s => fun i => Real.exp (-σ i * s) * z i)
      (fun i => -σ i * (Real.exp (-σ i * t) * z i)) t := by
    apply hasDerivAt_pi.mpr
    intro i
    have hd := ((Real.hasDerivAt_exp (-σ i * t)).comp t
      ((hasDerivAt_id t).const_mul (-σ i))).mul_const (z i)
    convert! hd using 1
    first | rfl | ring
  have hd := (hasDerivAt_cubicAxisParameter a t).prodMk hz
  have he : cubicDescent σ (-(a ^ 2)) (cubicFlowCylinder σ a (z, t)) =
      (a ^ 2 - cubicAxisParameter a t ^ 2, fun i => -σ i * (Real.exp (-σ i * t) * z i)) := by
    apply Prod.ext
    · change -(cubicAxisParameter a t ^ 2 + -(a ^ 2)) = a ^ 2 - cubicAxisParameter a t ^ 2
      ring
    · rfl
  rw [he]
  exact hd

theorem cubicFlowCylinder_axis (σ : Fin m → ℝ) (a t : ℝ) :
    cubicFlowCylinder σ a (0, t) = cubicModelOrbit a t := by
  simp only [cubicFlowCylinder, cubicModelOrbit, Pi.zero_apply, mul_zero]
  rfl

theorem cubicFlowCylinder_zero_time (σ : Fin m → ℝ) (a : ℝ) (z : Fin m → ℝ) :
    cubicFlowCylinder σ a (z, 0) = (0, z) := by
  simp only [cubicFlowCylinder, cubicAxisParameter, mul_zero, Real.tanh_zero,
    Real.exp_zero, one_mul]

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
