import Wikipedia.HomotopyGroupsOfSpheres.CliffordBoundarySpinorFiber

/-! # Every circle loop is the actual spinor boundary of a two-sphere cube -/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.CliffordBoundaryBott

open NoExoticSixSphere NoExoticSixSphere.CubeFirstCoordinate
open NoExoticSixSphere.RankSixComplexProjection

theorem exists_connecting_sphere (q : GenLoop (Fin 1) Circle 1) :
    ∃ p : GenLoop (Fin 2) (Sphere 2) structurePole,
      SpinorFibration.connecting poleSpinor 1
        (pointedMap structureMap structurePole (fromSpinor poleSpinor) structureMap_pole
          (⟦p⟧ : π_ 2 (Sphere 2) structurePole)) = (⟦q⟧ : π_ 1 Circle 1) := by
  obtain ⟨H⟩ := pairFiberLoop_nullhomotopic q
  let F := H.symm
  let p : GenLoop (Fin 2) (Sphere 2) structurePole :=
    ⟨hopfMap.comp (F.toContinuousMap.comp (split 1)), by
      intro u hu
      change hopfMap (F (split 1 u)) = structurePole
      rcases (boundary_split_iff 1 u).mp hu with h₀ | h₁ | hb
      · change hopfMap (F ((split 1 u).1, (split 1 u).2)) = structurePole
        rw [h₀]
        exact (congrArg hopfMap (F.map_zero_left _)).trans hopfMap_pairPole
      · change hopfMap (F ((split 1 u).1, (split 1 u).2)) = structurePole
        rw [h₁]
        exact (congrArg hopfMap (F.map_one_left _)).trans
          (hopfMap_pairFiber (q (split 1 u).2))
      · exact (congrArg hopfMap (F.eq_fst (split 1 u).1 hb)).trans hopfMap_pairPole⟩
  let p' := pointedMapGenLoop structureMap structurePole (fromSpinor poleSpinor) structureMap_pole p
  let L : SpinorFibration.CubeLift poleSpinor p' := {
    map := spinorPlaneMap.comp F.toContinuousMap
    initial := fun u ↦ (congrArg spinorPlaneMap (F.map_zero_left u)).trans poleSpinor_eq.symm
    project := fun t u ↦ by
      change fromSpinor (spinorPlaneMap (F (t, u))) =
        structureMap (hopfMap (F (split 1 (join 1 (t, u)))))
      rw [split_join]
      exact fromSpinor_plane (F (t, u))
    boundary := fun t u hu ↦
      (congrArg spinorPlaneMap (F.eq_fst t hu)).trans poleSpinor_eq.symm }
  have he : L.endpoint = q := by
    apply GenLoop.ext
    intro u
    change SpinorFibration.coordinate poleSpinor (spinorPlaneMap (F (1, u)))
      (L.endpoint_project u).symm = q u
    have hF : F (1, u) = pairFiber (q u) := F.map_one_left u
    have hv : spinorPlaneMap (F (1, u)) = phaseSmul (q u) poleSpinor :=
      (congrArg spinorPlaneMap hF).trans ((spinorPlaneMap_pairFiber (q u)).trans
        (congrArg (phaseSmul (q u)) poleSpinor_eq.symm))
    simp only [hv, SpinorFibration.coordinate_phaseSmul]
  refine ⟨p, ?_⟩
  rw [pointedMap_mk]
  exact (SpinorFibration.connecting_eq_endpoint poleSpinor p' L).trans
    (congrArg Quotient.mk' he)

end Wikipedia.HomotopyGroupsOfSpheres.CliffordBoundaryBott
