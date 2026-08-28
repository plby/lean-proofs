import Wikipedia.NoExoticSixSphere.SphereCylinderPoles

/-!
# A genuine circle clock for doubling a two-ended cylinder

The first coordinate gives a smooth clock, equal to zero and one at
the two actual coordinate poles. Away from those poles its differential
is surjective. The proof uses the actual sphere tangent space and the
rotation tangent vector, without replacing the circle's smooth atlas.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.CircleCylinder

abbrev V := EuclideanSpace ℝ (Fin 2)

local instance : Fact (Module.finrank ℝ V = 1 + 1) := ⟨finrank_euclideanSpace_fin⟩

def head : V →L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ (EuclideanSpace ℝ (Fin 1))).comp
    (SphereCylinder.join 0).symm.toContinuousLinearMap

theorem head_apply (v : V) : head v = v 0 := rfl

def clockLinear : V →L[ℝ] ℝ := (-1 / 2 : ℝ) • head

def ambientClock (v : V) : ℝ := 1 / 2 + clockLinear v

def clock (c : Sphere 1) : ℝ := ambientClock c.val

theorem clock_apply (c : Sphere 1) : clock c = (1 - c.val 0) / 2 := by
  change (1 : ℝ) / 2 + (-1 / 2) * c.val 0 = _
  ring

theorem contMDiff_clock : ContMDiff (𝓡 1) 𝓘(ℝ, ℝ) ∞ clock := by
  have hc : ContMDiff (𝓡 1) 𝓘(ℝ, V) ∞ (Subtype.val : Sphere 1 → V) :=
    contMDiff_coe_sphere
  exact contMDiff_const.add (clockLinear.contDiff.contMDiff.comp hc)

def clockMap : C(Sphere 1, ℝ) := ⟨clock, contMDiff_clock.continuous⟩

theorem clock_left : clock (SphereCylinder.endPole 0 true) = 0 := by
  rw [clock_apply, SphereCylinder.endPole_head]
  norm_num

theorem clock_right : clock (SphereCylinder.endPole 0 false) = 1 := by
  rw [clock_apply, SphereCylinder.endPole_head]
  norm_num

def tangent (c : Sphere 1) : V := WithLp.toLp 2 (Fin.cons (-c.val 1) (fun _ : Fin 1 ↦ c.val 0))

theorem tangent_orthogonal (c : Sphere 1) : tangent c ∈ (ℝ ∙ c.val)ᗮ := by
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
  simp [tangent, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_succ,
    mul_comm]

theorem inclusion_range (c : Sphere 1) :
    (mfderiv (𝓡 1) 𝓘(ℝ, V) (Subtype.val : Sphere 1 → V) c).range = (ℝ ∙ c.val)ᗮ := by
  convert! range_mvfderiv_subtypeVal (n := 1) c

theorem mfderiv_clock (c : Sphere 1) :
    mfderiv (𝓡 1) 𝓘(ℝ, ℝ) clock c =
      clockLinear.comp (mfderiv (𝓡 1) 𝓘(ℝ, V) (Subtype.val : Sphere 1 → V) c) := by
  have hA : HasFDerivAt ambientClock clockLinear c.val :=
    clockLinear.hasFDerivAt.const_add (1 / 2)
  have hc : ContMDiff (𝓡 1) 𝓘(ℝ, V) ∞ (Subtype.val : Sphere 1 → V) :=
    contMDiff_coe_sphere
  change mfderiv (𝓡 1) 𝓘(ℝ, ℝ) (ambientClock ∘ Subtype.val) c = _
  rw [mfderiv_comp c hA.differentiableAt.mdifferentiableAt (hc.mdifferentiableAt (by simp)),
    mfderiv_eq_fderiv, hA.fderiv]
  rfl

theorem surjective_mfderiv_clock (c : Sphere 1) (hc : c ∈ SphereCylinder.band 0) :
    Surjective (mfderiv (𝓡 1) 𝓘(ℝ, ℝ) clock c) := by
  let D : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ := mfderiv (𝓡 1) 𝓘(ℝ, ℝ) clock c
  let A : EuclideanSpace ℝ (Fin 1) →L[ℝ] V :=
    mfderiv (𝓡 1) 𝓘(ℝ, V) (Subtype.val : Sphere 1 → V) c
  have hD : D = clockLinear.comp A := mfderiv_clock c
  have hA : A.range = (ℝ ∙ c.val)ᗮ := inclusion_range c
  change Surjective D
  have htail : c.val 1 ≠ 0 := by
    intro h
    apply hc
    ext i
    fin_cases i
    exact h
  have hv := tangent_orthogonal c
  rw [← hA] at hv
  obtain ⟨u, hu⟩ := hv
  change A u = tangent c at hu
  have hd : D u = c.val 1 / 2 := by
    rw [hD, ContinuousLinearMap.comp_apply, hu]
    change (-1 / 2 : ℝ) * (-c.val 1) = c.val 1 / 2
    ring
  intro z
  refine ⟨(z / (c.val 1 / 2)) • u, ?_⟩
  rw [map_smul, hd]
  change (z / (c.val 1 / 2)) * (c.val 1 / 2) = z
  exact div_mul_cancel₀ z (div_ne_zero htail (by norm_num))

end NoExoticSixSphere.CircleCylinder
