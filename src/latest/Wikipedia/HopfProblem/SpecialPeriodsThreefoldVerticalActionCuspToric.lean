import Wikipedia.HopfProblem.ToricTwists

/-!
# The vertical holomorphic flow on the genuine toric cusp model

Multiplication in the second torus coordinate extends over every toric
boundary stratum. Its exponential parameter gives a jointly holomorphic
additive flow, preserves the cusp time, and has every integer as a period.
All holomorphicity statements use the existing toric atlas.
-/

noncomputable section

open Set Topology
open scoped ContDiff Matrix

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.Cusp

open ToricCharts ToricFan ToricSpace

local notation "IT" => modelWithCornersSelf ℂ (CoordinateSpace 3)
local notation "I₁" => modelWithCornersSelf ℂ ℂ

/-- The exponential multiplier of the second fibre-torus coordinate. -/
def multiplier (s : ℂ) : ActingTorus :=
  fibreMultiplier ![1, Units.mk0 (Complex.exp (2 * Real.pi * Complex.I * s))
    (Complex.exp_ne_zero _)]

@[simp] theorem multiplier_zero : multiplier 0 = 1 := by
  ext i
  fin_cases i <;> simp [multiplier, fibreMultiplier]

theorem multiplier_add (s t : ℂ) : multiplier (s + t) = multiplier s * multiplier t := by
  ext i
  fin_cases i <;> simp [multiplier, fibreMultiplier, mul_add, Complex.exp_add]

@[simp] theorem multiplier_int_cast (n : ℤ) : multiplier (n : ℂ) = 1 := by
  have he : Complex.exp (2 * Real.pi * Complex.I * (n : ℂ)) = 1 := by
    simpa only [mul_comm] using Complex.exp_int_mul_two_pi_mul_I n
  ext i
  fin_cases i <;> simp [multiplier, fibreMultiplier, he]

/-- The actual extended torus action, including the toric boundary. -/
def toricFlow (s : ℂ) : Space → Space := torusAction (multiplier s)

@[simp] theorem toricFlow_zero (x : Space) : toricFlow 0 x = x := by
  simp [toricFlow]

theorem toricFlow_add (s t : ℂ) (x : Space) :
    toricFlow (s + t) x = toricFlow s (toricFlow t x) := by
  simp only [toricFlow, multiplier_add, torusAction_mul]

@[simp] theorem toricFlow_int_cast (n : ℤ) (x : Space) : toricFlow (n : ℂ) x = x := by
  simp [toricFlow]

@[simp] theorem toricFlow_time (s : ℂ) (x : Space) : time (toricFlow s x) = time x := by
  exact time_fibreMultiplier _ x

@[simp] theorem toricFlow_inclusion (s : ℂ) (a : Triangle) (z : CoordinateSpace 3) :
    toricFlow s (inclusion a z) = inclusion a (scale a (multiplier s) z) :=
  torusAction_inclusion _ _ _

theorem multiplier_holomorphic :
    ContDiff ℂ ω (fun s : ℂ => fun i => (multiplier s i : ℂ)) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact contDiff_const
  · exact (contDiff_const.mul contDiff_id).cexp
  · exact contDiff_const

theorem multiplier_factors_holomorphic (a : Triangle) :
    ContDiff ℂ ω (fun s => factors a (multiplier s)) := by
  apply contDiffOn_univ.mp
  exact (monomial_contDiffOn a.dual ω).comp multiplier_holomorphic.contDiffOn
    (fun s _ => torus_subset_domain _ (fun i => (multiplier s i).ne_zero))

/-- Joint holomorphicity of the literal scaling in each affine toric chart. -/
theorem toricFlow_scale_joint_holomorphic (a : Triangle) :
    ContDiff ℂ ω (fun p : ℂ × CoordinateSpace 3 => scale a (multiplier p.1) p.2) :=
  ((multiplier_factors_holomorphic a).comp contDiff_fst).mul contDiff_snd

private theorem toricFlow_scale_joint_contMDiff (a : Triangle) :
    ContMDiff (modelWithCornersSelf ℂ (ℂ × CoordinateSpace 3)) IT ω
      (fun q : ℂ × CoordinateSpace 3 => scale a (multiplier q.1) q.2) :=
  (toricFlow_scale_joint_holomorphic a).contMDiff

private theorem toricChartInverse_holomorphic (a : Triangle) (x : Space)
    (hx : x ∈ (parametrization a).target) :
    ContMDiffAt IT IT ω (parametrization a).symm x := by
  have he : (parametrization a).symm ∈ IsManifold.maximalAtlas IT ω Space :=
    IsManifold.subset_maximalAtlas (mem_range_self a)
  exact contMDiffAt_of_mem_maximalAtlas he hx

private theorem toricFlow_local_coordinates_holomorphic (a : Triangle) (p : ℂ × Space)
    (hp : p.2 ∈ (parametrization a).target) :
    ContMDiffAt ((I₁).prod IT) (modelWithCornersSelf ℂ (ℂ × CoordinateSpace 3)) ω
      (fun q : ℂ × Space => (q.1, (parametrization a).symm q.2)) p := by
  have hinv := toricChartInverse_holomorphic a p.2 hp
  have hfirst : ContMDiffAt ((I₁).prod IT) I₁ ω (Prod.fst : ℂ × Space → ℂ) p :=
    contMDiffAt_fst
  have hsecond : ContMDiffAt ((I₁).prod IT) IT ω
      (fun q : ℂ × Space => (parametrization a).symm q.2) p :=
    hinv.comp p contMDiffAt_snd
  exact hfirst.prodMk_space hsecond

private theorem toricFlow_local_scaled_holomorphic (a : Triangle) (p : ℂ × Space)
    (hp : p.2 ∈ (parametrization a).target) :
    ContMDiffAt ((I₁).prod IT) IT ω
      (fun q : ℂ × Space => scale a (multiplier q.1) ((parametrization a).symm q.2)) p := by
  exact ContMDiffAt.comp
    (I := (I₁).prod IT) (I' := modelWithCornersSelf ℂ (ℂ × CoordinateSpace 3)) (I'' := IT)
    (f := fun q : ℂ × Space => (q.1, (parametrization a).symm q.2))
    (g := fun q : ℂ × CoordinateSpace 3 => scale a (multiplier q.1) q.2) p
    (toricFlow_scale_joint_contMDiff a (p.1, (parametrization a).symm p.2))
    (toricFlow_local_coordinates_holomorphic a p hp)

private theorem toricFlow_local_holomorphic (a : Triangle) (p : ℂ × Space)
    (hp : p.2 ∈ (parametrization a).target) :
    ContMDiffAt ((I₁).prod IT) IT ω
      (fun q : ℂ × Space =>
        inclusion a (scale a (multiplier q.1) ((parametrization a).symm q.2))) p :=
  (inclusion_holomorphic a).contMDiffAt.comp p
    (toricFlow_local_scaled_holomorphic a p hp)

/-- The exponential torus action is holomorphic jointly in time and the
point of the original toric space, including every boundary stratum. -/
theorem toricFlow_joint_holomorphic :
    ContMDiff ((I₁).prod IT) IT ω (fun p : ℂ × Space => toricFlow p.1 p.2) := by
  intro p
  let a := preferredTriangle p.2
  have hp : p.2 ∈ (parametrization a).target := by
    rw [parametrization_target]
    exact preferred_mem p.2
  apply (toricFlow_local_holomorphic a p hp).congr_of_eventuallyEq
  filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds
    ((parametrization a).open_target.mem_nhds hp)] with q hq
  calc
    toricFlow q.1 q.2 =
        toricFlow q.1 (inclusion a ((parametrization a).symm q.2)) :=
      congrArg (toricFlow q.1) ((parametrization a).right_inv hq).symm
    _ = _ := toricFlow_inclusion q.1 a _

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.Cusp
