import Wikipedia.NoExoticSixSphere.RankSixHemisphereSpinor
import Wikipedia.NoExoticSixSphere.RankSixSpinorPhase
import Wikipedia.NoExoticSixSphere.CircleFamilyNullhomotopy
import Wikipedia.NoExoticSixSphere.HemisphereExtension
import Wikipedia.NoExoticSixSphere.HemisphereMapGluing
import Wikipedia.NoExoticSixSphere.EquatorDimension

/-!
# Lifting four-sphere complex-structure families to unit spinors

Hemisphere sections differ by an actual circle-valued transition map.
Its nullhomotopy extends across the southern hemisphere, correcting that
section to agree exactly with the northern one. The corrected sections glue.
-/

namespace NoExoticSixSphere.RankSixComplexProjection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_unitSection_of_circleNullhomotopy
    (J : C(UnitSphere E, OrthogonalComplexStructures.Space 6)) (v : UnitSphere E)
    [Nonempty (Equator v)]
    (hcircle : ∀ f : C(Equator v, Circle), f.Homotopic (ContinuousMap.const _ 1)) :
    ∃ q : C(UnitSphere E, UnitSpinor),
      ∀ x, projection (J x) (q x) = (q x : Spinor) := by
  obtain ⟨qN, hN⟩ := exists_hemisphere_unitSection J v
  obtain ⟨qS, hS⟩ := exists_hemisphere_unitSection J (antipode v)
  let a : C(Equator v, UnitSpinor) :=
    qN.comp ⟨equatorNorth v, continuous_equatorNorth v⟩
  let b : C(Equator v, UnitSpinor) :=
    qS.comp ⟨equatorSouth v, continuous_equatorSouth v⟩
  have ha (x : Equator v) : projection (J x.1) (a x) = (a x : Spinor) :=
    hN (equatorNorth v x)
  have hb (x : Equator v) : projection (J x.1) (b x) = (b x : Spinor) :=
    hS (equatorSouth v x)
  let f : C(Equator v, Circle) := phaseMap (fun x : Equator v ↦ J x.1) a b ha hb
  have hf : ∀ x, phaseSmul (f x) (b x) = a x :=
    phaseMap_smul (fun x : Equator v ↦ J x.1) a b ha hb
  obtain ⟨H⟩ := hcircle f
  obtain ⟨g, hg⟩ := exists_southernExtension_of_nullhomotopy v f 1 H
  let qS' : C(ClosedHemisphere (antipode v), UnitSpinor) :=
    ⟨fun x ↦ phaseSmul (g x) (qS x),
      continuous_phaseSmul.comp (g.continuous.prodMk qS.continuous)⟩
  have hagree (x : Equator v) : qN (equatorNorth v x) = qS' (equatorSouth v x) := by
    change a x = phaseSmul (g (equatorSouth v x)) (b x)
    rw [hg]
    exact (hf x).symm
  obtain ⟨q, hqN, hqS⟩ := exists_glued_hemisphereMap v qN qS' hagree
  refine ⟨q, fun x ↦ ?_⟩
  have hm : x ∈ closedHemisphere v ∪ closedHemisphere (antipode v) := by
    rw [hemispheres_cover]
    exact Set.mem_univ x
  rcases hm with hx | hx
  · rw [hqN ⟨x, hx⟩]
    exact hN ⟨x, hx⟩
  · rw [hqS ⟨x, hx⟩]
    exact phaseSmul_fixed (J x) (qS ⟨x, hx⟩) (hS ⟨x, hx⟩) (g ⟨x, hx⟩)

theorem fourthSphere_equator_circle_nullhomotopic (v : Sphere 4)
    (f : C(Equator v, Circle)) : f.Homotopic (ContinuousMap.const _ 1) := by
  let e : Equator v ≃ₜ Sphere 3 :=
    equatorEuclideanHomeomorph v (n := 4) finrank_euclideanSpace_fin
  let : SimplyConnectedSpace (Sphere 3) := EuclideanSphere.simplyConnectedSpace 1
  let : LocallyPathConnectedSpace (Sphere 3) :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 3)) (Sphere 3)
  let f' : C(Sphere 3, Circle) := f.comp ⟨e.symm, e.symm.continuous⟩
  obtain ⟨H⟩ := circleMap_nullhomotopic f'
  refine ⟨{
    toFun := fun p ↦ H (p.1, e p.2)
    continuous_toFun := H.continuous.comp
      (continuous_fst.prodMk (e.continuous.comp continuous_snd))
    map_zero_left := ?_
    map_one_left := ?_ }⟩
  · intro x
    change H (0, e x) = f x
    rw [H.apply_zero]
    exact congrArg f (e.symm_apply_apply x)
  · intro x
    exact H.apply_one (e x)

theorem exists_fourthSphere_unitSection
    (J : C(Sphere 4, OrthogonalComplexStructures.Space 6)) :
    ∃ q : C(Sphere 4, UnitSpinor), ∀ x, projection (J x) (q x) = (q x : Spinor) := by
  classical
  let : Nonempty (Sphere 4) := NormedSpace.sphere_nonempty_rclike ℝ zero_le_one
  let v : Sphere 4 := Classical.choice inferInstance
  let e : Equator v ≃ₜ Sphere 3 :=
    equatorEuclideanHomeomorph v (n := 4) finrank_euclideanSpace_fin
  let : Nonempty (Sphere 3) := NormedSpace.sphere_nonempty_rclike ℝ zero_le_one
  let : Nonempty (Equator v) := e.toEquiv.nonempty
  exact exists_unitSection_of_circleNullhomotopy J v
    (fourthSphere_equator_circle_nullhomotopic v)

end NoExoticSixSphere.RankSixComplexProjection
