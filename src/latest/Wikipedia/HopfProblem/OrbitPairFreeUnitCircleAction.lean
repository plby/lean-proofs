import Wikipedia.HopfProblem.OrbitPairUnitCircleAction

/-! # Restricting the original native unit-circle action to its actual free locus -/

noncomputable section

open Set Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.OrbitPair

open SpecialPeriods SpecialPeriods.Threefold

attribute [local instance] unitCircleMulAction unitCircleAction_continuous
  Threefold.chartedSpace Threefold.space_isSmoothRealManifold

theorem freeLocus_smul_mem (u : Circle) (x : freeLocus) : u • x.val ∈ freeLocus := by
  change u • x.val ∉ VerticalAction.D₀
  rw [← CircleOrbitSpace.quotientMap_preimage_fixedCurveRange]
  change CircleOrbitSpace.quotientMap (u • x.val) ∉ range CircleOrbitSpace.fixedCurveMap
  rw [quotientMap_unitCircle_smul]
  exact (freeOrbitProjection x).property

@[instance_reducible] def freeLocusUnitCircleAction : MulAction Circle freeLocus where
  smul u x := ⟨u • x.val, freeLocus_smul_mem u x⟩
  one_smul x := Subtype.ext (one_smul Circle x.val)
  mul_smul u v x := Subtype.ext (mul_smul u v x.val)

attribute [local instance] freeLocusUnitCircleAction

@[simp] theorem freeLocus_smul_coe (u : Circle) (x : freeLocus) :
    (u • x).val = u • x.val := rfl

theorem freeLocusUnitCircleAction_continuous : ContinuousSMul Circle freeLocus :=
  ⟨(continuous_fst.smul (continuous_subtype_val.comp continuous_snd)).subtype_mk _⟩

local notation "IX" => 𝓘(ℝ, ℂ × ComplexPlane₂)

theorem freeLocusUnitCircleAction_smooth :
    ContMDiff ((𝓡 1).prod IX) IX ∞ (fun z : Circle × freeLocus => z.1 • z.2) := by
  apply (ContMDiff.subtypeVal_comp_iff freeLocus _).mp
  exact unitCircleAction_smooth.comp
    (contMDiff_fst.prodMk (contMDiff_subtype_val.comp contMDiff_snd))

theorem freeOrbitProjection_unitCircle_smul (u : Circle) (x : freeLocus) :
    freeOrbitProjection (u • x) = freeOrbitProjection x :=
  Subtype.ext (quotientMap_unitCircle_smul u x.val)

theorem freeLocus_unitCircle_smul_injective (x : freeLocus) :
    Function.Injective (fun u : Circle => u • x) := by
  obtain ⟨F, _, he, hFx⟩ := exists_unitCircle_equivariant_smooth_function_at_free_point
    x.val x.property
  intro u v h
  apply Circle.ext
  have hh := congrArg F (congrArg (fun y : freeLocus => y.val) h)
  change F (u • x.val) = F (v • x.val) at hh
  rw [he, he] at hh
  exact mul_right_cancel₀ hFx hh

theorem freeOrbitProjection_eq_iff_unitCircle (x y : freeLocus) :
    freeOrbitProjection x = freeOrbitProjection y ↔ ∃ u : Circle, u • y = x := by
  constructor
  · intro h
    obtain ⟨u, hu⟩ := (quotientMap_eq_iff_unitCircle x.val y.val).mp
      (congrArg (fun z : freeOrbitLocus => z.val) h)
    exact ⟨u, Subtype.ext hu⟩
  · rintro ⟨u, rfl⟩
    exact freeOrbitProjection_unitCircle_smul u y

end Wikipedia.HopfProblem.OrbitPair
