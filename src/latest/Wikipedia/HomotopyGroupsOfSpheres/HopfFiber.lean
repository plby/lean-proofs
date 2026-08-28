import Wikipedia.HopfProblem.OrbitPairNormalSphereAction

/-! # The actual fibers of the Hopf sphere map are circles -/

noncomputable section

open scoped Topology

namespace Wikipedia.HomotopyGroupsOfSpheres

open HopfProblem HopfProblem.OrbitPair
open HopfProblem.SpecialPeriods HopfProblem.SpecialPeriods.Threefold
open HopfProblem.CuspCircleNormalTrivialization

attribute [local instance] freeLocusUnitCircleAction

variable (b : RiemannSphere) (r : ℝ) (hr₀ : 0 < r) (hr : r < injectiveRadius)

include b hr₀ hr in
/-- The circle acts freely on a positive-radius normal sphere. -/
theorem hopf_smul_injective (v : NormalSphere r) :
    Function.Injective (fun u : Circle => u • v) := by
  intro u w h
  apply freeLocus_unitCircle_smul_injective (freeNormalSphereMap b r hr₀ hr v)
  simpa only [freeNormalSphereMap_smul] using congrArg (freeNormalSphereMap b r hr₀ hr) h

include b hr₀ hr in
/-- Equal Hopf images are precisely points in a common circle orbit. -/
theorem hopf_eq_iff (v w : NormalSphere r) :
    sphereHopfMap r v = sphereHopfMap r w ↔ ∃ u : Circle, u • w = v := by
  constructor
  · intro h
    have h' : freeOrbitProjection (freeNormalSphereMap b r hr₀ hr v) =
        freeOrbitProjection (freeNormalSphereMap b r hr₀ hr w) := by
      rw [freeOrbitProjection_freeNormalSphereMap, freeOrbitProjection_freeNormalSphereMap, h]
    obtain ⟨u, hu⟩ := (freeOrbitProjection_eq_iff_unitCircle _ _).mp h'
    refine ⟨u, ?_⟩
    apply normalSphereMap_injective b r hr₀ hr
    exact congrArg (fun z : freeLocus => z.val)
      ((freeNormalSphereMap_smul b r hr₀ hr u w).trans hu)
  · rintro ⟨u, rfl⟩
    exact sphereHopfMap_smul r u w

/-- The orbit map as a continuous map into the literal fiber. -/
def hopfFiberMap (v : NormalSphere r) :
    C(Circle, {w : NormalSphere r // sphereHopfMap r w = sphereHopfMap r v}) where
  toFun u := ⟨u • v, sphereHopfMap_smul r u v⟩
  continuous_toFun := (continuous_id.smul continuous_const).subtype_mk _

/-- Compactness identifies the fiber's inherited topology with the ordinary circle. -/
def hopfFiberHomeomorph (v : NormalSphere r) :
    Circle ≃ₜ {w : NormalSphere r // sphereHopfMap r w = sphereHopfMap r v} :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective (hopfFiberMap r v) (by
      constructor
      · intro u w h
        exact hopf_smul_injective b r hr₀ hr v (congrArg Subtype.val h)
      · intro w
        obtain ⟨u, hu⟩ := (hopf_eq_iff b r hr₀ hr w.val v).mp w.property
        exact ⟨u, Subtype.ext hu⟩))
    (hopfFiberMap r v).continuous

@[simp] theorem hopfFiberHomeomorph_apply (v : NormalSphere r) (u : Circle) :
    (hopfFiberHomeomorph b r hr₀ hr v u).val = u • v := rfl

@[simp] theorem hopfFiberHomeomorph_one (v : NormalSphere r) :
    hopfFiberHomeomorph b r hr₀ hr v 1 = ⟨v, rfl⟩ := by
  apply Subtype.ext
  exact one_smul Circle v

end Wikipedia.HomotopyGroupsOfSpheres
