import Wikipedia.HopfProblem.ToricTranslations

/-!
# The complex torus acting on the cusp model

The coordinatewise torus action extends across every boundary stratum of the
glued space. The first two torus factors preserve the cusp parameter. These
are the multipliers used in the twisted action of Lemma 4.3.
-/

noncomputable section

open Set Topology
open scoped ContDiff Matrix

namespace Wikipedia.HopfProblem.ToricSpace

open ToricCharts ToricFan Triangle

abbrev ActingTorus := Fin 3 → ℂˣ

def factors (s : Triangle) (u : ActingTorus) : CoordinateSpace 3 :=
  monomial s.dual (fun j => (u j : ℂ))

theorem factors_nonzero (s : Triangle) (u : ActingTorus) (j : Fin 3) : factors s u j ≠ 0 :=
  monomial_mapsTo_torus _ (fun i => (u i).ne_zero) j

def scale (s : Triangle) (u : ActingTorus) (z : CoordinateSpace 3) : CoordinateSpace 3 :=
  factors s u * z

theorem scale_holomorphic (s : Triangle) (u : ActingTorus) : ContDiff ℂ ω (scale s u) := by
  apply contDiff_pi.mpr
  intro j
  exact contDiff_const.mul (contDiff_apply ℂ ℂ j)

theorem scale_mem_source (s t : Triangle) (u : ActingTorus) (z : CoordinateSpace 3) :
    scale s u z ∈ (chartChange s t).source ↔ z ∈ (chartChange s t).source := by
  simp [chartChange_source, domain, scale, factors_nonzero]

theorem transition_factors (s t : Triangle) (u : ActingTorus) :
    monomial (transition s t) (factors s u) = factors t u := by
  have he : transition s t * s.dual = t.dual := by
    rw [transition, Matrix.mul_assoc, rays_dual, Matrix.mul_one]
  change monomial (transition s t) (monomial s.dual (fun j => (u j : ℂ))) = _
  rw [monomial_mul_on_torus _ _ (fun j => (u j).ne_zero), he]
  rfl

theorem scale_transition (s t : Triangle) (u : ActingTorus) (z : CoordinateSpace 3) :
    chartChange s t (scale s u z) = scale t u (chartChange s t z) := by
  change monomial (transition s t) (factors s u * z) =
    factors t u * monomial (transition s t) z
  rw [monomial_mul, transition_factors]

theorem action_compatible (u : ActingTorus) (s t : Triangle) (z : CoordinateSpace 3)
    (hz : z ∈ (chartChange s t).source) :
    inclusion t (scale t u (chartChange s t z)) = inclusion s (scale s u z) := by
  exact ((inclusion_eq_iff s t _ _).mpr
    ⟨(scale_mem_source s t u z).mpr hz, scale_transition s t u z⟩).symm

def torusAction (u : ActingTorus) : Space → Space :=
  descend (fun s z => inclusion s (scale s u z))

@[simp] theorem torusAction_inclusion (u : ActingTorus) (s : Triangle)
    (z : CoordinateSpace 3) : torusAction u (inclusion s z) = inclusion s (scale s u z) :=
  descend_inclusion _ (action_compatible u) s z

theorem torusAction_holomorphic (u : ActingTorus) :
    ContMDiff (modelWithCornersSelf ℂ (CoordinateSpace 3))
      (modelWithCornersSelf ℂ (CoordinateSpace 3)) ω (torusAction u) :=
  descend_holomorphic _ _ (action_compatible u)
    (fun s => (inclusion_holomorphic s).comp (scale_holomorphic s u).contMDiff)

@[simp] theorem factors_one (s : Triangle) : factors s 1 = 1 := by
  change monomial s.dual 1 = 1
  exact monomial_ones _

theorem factors_mul (s : Triangle) (u v : ActingTorus) :
    factors s (u * v) = factors s u * factors s v := by
  change monomial s.dual ((fun j => (u j : ℂ)) * (fun j => (v j : ℂ))) = _
  exact monomial_mul _ _ _

@[simp] theorem scale_one (s : Triangle) (z : CoordinateSpace 3) : scale s 1 z = z := by
  simp [scale]

theorem scale_mul (s : Triangle) (u v : ActingTorus) (z : CoordinateSpace 3) :
    scale s u (scale s v z) = scale s (u * v) z := by
  simp [scale, factors_mul, mul_assoc]

@[simp] theorem torusAction_one (x : Space) : torusAction 1 x = x := by
  obtain ⟨s, z, rfl⟩ := inclusion_jointly_surjective x
  simp

theorem torusAction_mul (u v : ActingTorus) (x : Space) :
    torusAction u (torusAction v x) = torusAction (u * v) x := by
  obtain ⟨s, z, rfl⟩ := inclusion_jointly_surjective x
  simp [scale_mul]

instance actingTorusMulAction : MulAction ActingTorus Space where
  smul := torusAction
  one_smul := torusAction_one
  mul_smul u v x := (torusAction_mul u v x).symm

def torusHomeomorph (u : ActingTorus) : Space ≃ₜ Space where
  toFun := torusAction u
  invFun := torusAction u⁻¹
  left_inv x := by rw [torusAction_mul]; simp
  right_inv x := by rw [torusAction_mul]; simp
  continuous_toFun := (torusAction_holomorphic u).continuous
  continuous_invFun := (torusAction_holomorphic u⁻¹).continuous

theorem time_factors (s : Triangle) (u : ActingTorus) : Triangle.time (factors s u) = u 2 := by
  have he := congrFun (monomial_mul_on_torus s.rays s.dual (fun j => (u j).ne_zero)) 2
  simpa only [factors, rays_dual, monomial_one, monomial_rays_height] using he

theorem time_scale (s : Triangle) (u : ActingTorus) (z : CoordinateSpace 3) :
    Triangle.time (scale s u z) = (u 2 : ℂ) * Triangle.time z := by
  rw [← time_factors s u]
  simp [Triangle.time, scale]
  ring

theorem time_torusAction (u : ActingTorus) (x : Space) :
    time (torusAction u x) = (u 2 : ℂ) * time x := by
  obtain ⟨s, z, rfl⟩ := inclusion_jointly_surjective x
  simp [time_scale]

def fibreMultiplier (u : Fin 2 → ℂˣ) : ActingTorus := ![u 0, u 1, 1]

@[simp] theorem time_fibreMultiplier (u : Fin 2 → ℂˣ) (x : Space) :
    time (torusAction (fibreMultiplier u) x) = time x := by
  simp [time_torusAction, fibreMultiplier]

theorem shear_fibreMultiplier (v : Fin 2 → ℤ) (u : Fin 2 → ℂˣ) :
    monomial (shear v) (fun j => (fibreMultiplier u j : ℂ)) =
      (fun j => (fibreMultiplier u j : ℂ)) := by
  ext i
  fin_cases i <;> simp [monomial, shear, fibreMultiplier, Fin.prod_univ_succ]

theorem factors_shift_fibreMultiplier (s : Triangle) (v : Fin 2 → ℤ) (u : Fin 2 → ℂˣ) :
    factors (s.shift v) (fibreMultiplier u) = factors s (fibreMultiplier u) := by
  unfold factors
  rw [dual_shift, ← monomial_mul_on_torus s.dual (shear (-v))
    (fun j => (fibreMultiplier u j).ne_zero), shear_fibreMultiplier]

theorem fibreMultiplier_translate (v : Fin 2 → ℤ) (u : Fin 2 → ℂˣ) (x : Space) :
    torusAction (fibreMultiplier u) (translate v x) =
      translate v (torusAction (fibreMultiplier u) x) := by
  obtain ⟨s, z, rfl⟩ := inclusion_jointly_surjective x
  simp [scale, factors_shift_fibreMultiplier]

end Wikipedia.HopfProblem.ToricSpace
