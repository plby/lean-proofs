import Wikipedia.SmoothSixDPoincare.RadialExtension
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Homotopy.Basic

/-!
# Continuous disk extensions of nullhomotopic sphere maps

The explicit cone parametrization of the actual closed normed disk is a
quotient map. A nullhomotopy descends through its fibers and gives a continuous
extension with exactly the original sphere values. No smoothness is asserted.
-/

noncomputable section

open Set Function Metric Topology

namespace Wikipedia.SmoothSixDPoincare.DiskCone

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]

def point (p : unitInterval × sphere (0 : E) 1) : closedBall (0 : E) 1 :=
  ⟨(1 - (p.1 : ℝ)) • (p.2 : E), by
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr p.1.2.2), mem_sphere_zero_iff_norm.mp p.2.property, mul_one]
    linarith [p.1.2.1]⟩

theorem norm_point (p : unitInterval × sphere (0 : E) 1) :
    ‖(point p : E)‖ = 1 - (p.1 : ℝ) := by
  change ‖(1 - (p.1 : ℝ)) • (p.2 : E)‖ = _
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr p.1.2.2),
    mem_sphere_zero_iff_norm.mp p.2.property, mul_one]

theorem continuous_point : Continuous (point (E := E)) := by
  apply Continuous.subtype_mk
  exact (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
    (continuous_subtype_val.comp continuous_snd)

theorem point_fibers {p q : unitInterval × sphere (0 : E) 1} (hpq : point p = point q) :
    p = q ∨ (p.1 = 1 ∧ q.1 = 1) := by
  have hnorm := congrArg (fun x : closedBall (0 : E) 1 => ‖(x : E)‖) hpq
  rw [norm_point, norm_point] at hnorm
  have ht : p.1 = q.1 := Subtype.ext (by linarith)
  rcases p with ⟨t, x⟩
  rcases q with ⟨s, y⟩
  dsimp only at ht
  subst s
  by_cases htop : t = 1
  · exact Or.inr ⟨htop, htop⟩
  · have htval : (t : ℝ) ≠ 1 := fun heq => htop (Subtype.ext heq)
    have hnonzero : 1 - (t : ℝ) ≠ 0 := sub_ne_zero.mpr (Ne.symm htval)
    have hvec : (1 - (t : ℝ)) • (x : E) = (1 - (t : ℝ)) • (y : E) :=
      congrArg Subtype.val hpq
    have hxy : x = y := Subtype.ext ((smul_right_injective E hnonzero) hvec)
    exact Or.inl (congrArg (fun z => (t, z)) hxy)

variable [Nonempty (sphere (0 : E) 1)]

theorem surjective_point : Surjective (point (E := E)) := by
  intro x
  by_cases hx : (x : E) = 0
  · refine ⟨(1, Classical.choice inferInstance), ?_⟩
    apply Subtype.ext
    change (1 - (1 : ℝ)) • _ = (x : E)
    rw [sub_self, zero_smul, hx]
  · have hxnorm : ‖(x : E)‖ ≤ 1 := mem_closedBall_zero_iff.mp x.property
    let t : unitInterval :=
      ⟨1 - ‖(x : E)‖, sub_nonneg.mpr hxnorm, by linarith [norm_nonneg (x : E)]⟩
    refine ⟨(t, RadialExtension.direction (x : E) hx), ?_⟩
    apply Subtype.ext
    change (1 - (1 - ‖(x : E)‖)) • (‖(x : E)‖⁻¹ • (x : E)) = (x : E)
    rw [sub_sub_cancel, smul_inv_smul₀ (norm_ne_zero_iff.mpr hx)]

theorem isQuotientMap_point [FiniteDimensional ℝ E] : IsQuotientMap (point (E := E)) := by
  let : CompactSpace (sphere (0 : E) 1) := isCompact_iff_compactSpace.mp (isCompact_sphere _ _)
  exact .of_surjective_continuous surjective_point continuous_point

variable (f : C(sphere (0 : E) 1, M)) (c : M) (H : f.Homotopy (ContinuousMap.const _ c))

omit [Nonempty (sphere (0 : E) 1)] in
theorem homotopy_eq_of_point_eq {p q : unitInterval × sphere (0 : E) 1}
    (hpq : point p = point q) : H p = H q := by
  rcases point_fibers hpq with h | ⟨hp, hq⟩
  · exact congrArg H h
  · have hp' : p = (1, p.2) := Prod.ext hp rfl
    have hq' : q = (1, q.2) := Prod.ext hq rfl
    rw [hp', hq', H.apply_one, H.apply_one]
    rfl

def extensionFun (x : closedBall (0 : E) 1) : M := H (surjInv surjective_point x)

theorem extensionFun_point (p : unitInterval × sphere (0 : E) 1) :
    extensionFun f c H (point p) = H p :=
  homotopy_eq_of_point_eq f c H (surjInv_eq surjective_point (point p))

def extension [FiniteDimensional ℝ E] : C(closedBall (0 : E) 1, M) where
  toFun := extensionFun f c H
  continuous_toFun := by
    apply isQuotientMap_point.continuous_iff.mpr
    have heq : extensionFun f c H ∘ point = H := funext (extensionFun_point f c H)
    rw [heq]
    exact H.continuous

theorem extension_boundary [FiniteDimensional ℝ E] (x : sphere (0 : E) 1) :
    extension f c H ⟨x, sphere_subset_closedBall x.property⟩ = f x := by
  have heq : (⟨(x : E), sphere_subset_closedBall x.property⟩ : closedBall (0 : E) 1) =
      point (0, x) := by
    apply Subtype.ext
    change (x : E) = (1 - (0 : ℝ)) • (x : E)
    rw [sub_zero, one_smul]
  change extensionFun f c H _ = f x
  rw [heq, extensionFun_point, H.apply_zero]

theorem extension_zero [FiniteDimensional ℝ E] :
    extension f c H ⟨0, mem_closedBall_self zero_le_one⟩ = c := by
  let x : sphere (0 : E) 1 := Classical.choice inferInstance
  have heq : (⟨0, mem_closedBall_self zero_le_one⟩ : closedBall (0 : E) 1) = point (1, x) := by
    apply Subtype.ext
    change (0 : E) = (1 - (1 : ℝ)) • (x : E)
    rw [sub_self, zero_smul]
  change extensionFun f c H _ = c
  rw [heq, extensionFun_point, H.apply_one]
  rfl

end Wikipedia.SmoothSixDPoincare.DiskCone
