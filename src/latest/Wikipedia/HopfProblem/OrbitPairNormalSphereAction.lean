import Wikipedia.HopfProblem.OrbitPairFreeUnitCircleAction
import Wikipedia.HopfProblem.OrbitPairMeridian

/-!
# The actual normal-sphere circle action and the Hopf pullback

Equal scalar weights in the original global normal framing become the
original opposite weights in the Euclidean Hopf coordinates. The
normal-sphere inclusion in the threefold is equivariant for these
literal actions, and the Hopf map is invariant.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.OrbitPair

open SpecialPeriods SpecialPeriods.Threefold CuspCircleNormalTrivialization

attribute [local instance] unitCircleMulAction freeLocusUnitCircleAction

def normalUnitAction (u : Circle) (v : Normal) : Normal :=
  scalarCoordinates ((u : ℂ) • scalarCoordinates.symm v)

theorem normalUnitAction_eq_opposite (u : Circle) (v : Normal) :
    normalUnitAction u v = oppositeAction (Circle.toUnits u) v := by
  change scalarCoordinates ((Circle.toUnits u : ℂ) • scalarCoordinates.symm v) = _
  rw [scalarCoordinates_smul (Circle.toUnits u) (Circle.norm_coe u),
    scalarCoordinates.apply_symm_apply]

theorem radialHopfMap_normalUnitAction (u : Circle) (v : Normal) :
    radialHopfMap (normalUnitAction u v) = radialHopfMap v := by
  symm
  apply (radialHopfMap_eq_iff v (normalUnitAction u v)).mpr
  refine ⟨Circle.toUnits u, Circle.norm_coe u, ?_⟩
  rw [normalUnitAction_eq_opposite]
  rfl

theorem norm_normalUnitAction (u : Circle) (v : Normal) : ‖normalUnitAction u v‖ = ‖v‖ := by
  rw [← norm_radialHopfMap, radialHopfMap_normalUnitAction, norm_radialHopfMap]

@[instance_reducible] def normalUnitCircleAction : MulAction Circle Normal where
  smul := normalUnitAction
  one_smul v := by
    change scalarCoordinates (((1 : Circle) : ℂ) • scalarCoordinates.symm v) = v
    rw [Circle.coe_one, one_smul, scalarCoordinates.apply_symm_apply]
  mul_smul u w v := by
    change scalarCoordinates (((u * w : Circle) : ℂ) • scalarCoordinates.symm v) =
      scalarCoordinates ((u : ℂ) •
        scalarCoordinates.symm (scalarCoordinates ((w : ℂ) • scalarCoordinates.symm v)))
    rw [scalarCoordinates.symm_apply_apply, Circle.coe_mul, mul_smul]

attribute [local instance] normalUnitCircleAction

theorem normalUnitAction_continuous : Continuous (fun z : Circle × Normal => normalUnitAction z.1 z.2) :=
  scalarCoordinates.continuous.comp
    ((continuous_subtype_val.comp continuous_fst).smul
      (scalarCoordinates.symm.continuous.comp continuous_snd))

instance normalSphere_mulAction (r : ℝ) : MulAction Circle (NormalSphere r) where
  smul u v := ⟨normalUnitAction u v, by
    simpa only [Metric.mem_sphere, dist_zero_right, norm_normalUnitAction] using v.property⟩
  one_smul v := Subtype.ext (one_smul Circle v.val)
  mul_smul u w v := Subtype.ext (mul_smul u w v.val)

instance normalSphere_continuousSMul (r : ℝ) : ContinuousSMul Circle (NormalSphere r) :=
  ⟨(normalUnitAction_continuous.comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _⟩

theorem sphereHopfMap_smul (r : ℝ) (u : Circle) (v : NormalSphere r) :
    sphereHopfMap r (u • v) = sphereHopfMap r v :=
  Subtype.ext (radialHopfMap_normalUnitAction u v.val)

theorem normalSphereMap_smul (b : RiemannSphere) (r : ℝ)
    (hr₀ : 0 < r) (hr : r < injectiveRadius) (u : Circle) (v : NormalSphere r) :
    normalSphereMap b r hr₀ hr (u • v) = u • normalSphereMap b r hr₀ hr v := by
  change roundProductMap (normalSphereTubePoint b r hr₀ hr (u • v)) =
    VerticalAction.actionBiholomorph (Circle.toUnits u)
      (roundProductMap (normalSphereTubePoint b r hr₀ hr v))
  rw [roundProductMap_normalAction (Circle.toUnits u) (Circle.norm_coe u)]
  apply congrArg roundProductMap
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change scalarCoordinates.symm (scalarCoordinates ((u : ℂ) • scalarCoordinates.symm v.val)) =
      (u : ℂ) • scalarCoordinates.symm v.val
    exact scalarCoordinates.symm_apply_apply _

theorem freeNormalSphereMap_smul (b : RiemannSphere) (r : ℝ)
    (hr₀ : 0 < r) (hr : r < injectiveRadius) (u : Circle) (v : NormalSphere r) :
    freeNormalSphereMap b r hr₀ hr (u • v) = u • freeNormalSphereMap b r hr₀ hr v :=
  Subtype.ext (normalSphereMap_smul b r hr₀ hr u v)

end Wikipedia.HopfProblem.OrbitPair
