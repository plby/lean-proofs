import Wikipedia.NoExoticSixSphere.QuaternionicHopfConnectingHom

/-! # Exactness at the actual unit-quaternion Hopf fiber -/

noncomputable section

open scoped unitInterval

namespace NoExoticSixSphere.QuaternionicHopf

open CubeFirstCoordinate HigherHomotopy

variable {n : ℕ}

def inclusionMap (n : ℕ) [NeZero n] :
    HomotopyGroup (Fin n) FiberGroup 1 →* HomotopyGroup (Fin n) (Sphere 7) (spherePole 7) :=
  mapMonoidHom unitFiberPoint unitFiberPoint_one

theorem endpoint_inclusion_nullhomotopic
    {p : GenLoop (Fin (n + 1)) (Sphere 4) (spherePole 4)} (L : CubeLift p) :
    GenLoop.Homotopic (genLoopMap unitFiberPoint unitFiberPoint_one L.endpoint) GenLoop.const := by
  let H : (GenLoop.const : GenLoop (Fin n) (Sphere 7) (spherePole 7)).val.HomotopyRel
      (genLoopMap unitFiberPoint unitFiberPoint_one L.endpoint).val (Cube.boundary (Fin n)) := {
    toContinuousMap := L.map
    map_zero_left := L.initial
    map_one_left := fun u ↦ (L.endpoint_point u).symm
    prop' := fun t u hu ↦ L.boundary t u hu }
  exact ⟨H.symm⟩

theorem inclusionMap_connecting [NeZero n]
    (a : HomotopyGroup (Fin (n + 1)) (Sphere 4) (spherePole 4)) :
    inclusionMap n (connecting n a) = 1 := by
  refine Quotient.inductionOn a fun p ↦ ?_
  exact Quotient.sound (endpoint_inclusion_nullhomotopic (chosenLift p))

theorem exists_connecting_of_nullhomotopic (q : GenLoop (Fin n) FiberGroup 1)
    (hq : GenLoop.Homotopic (genLoopMap unitFiberPoint unitFiberPoint_one q) GenLoop.const) :
    ∃ p : GenLoop (Fin (n + 1)) (Sphere 4) (spherePole 4),
      connecting n (⟦p⟧ : HomotopyGroup (Fin (n + 1)) (Sphere 4) (spherePole 4)) =
        (⟦q⟧ : HomotopyGroup (Fin n) FiberGroup 1) := by
  obtain ⟨H⟩ := hq
  let F := H.symm
  let p : GenLoop (Fin (n + 1)) (Sphere 4) (spherePole 4) :=
    ⟨sphereMap.comp (F.toContinuousMap.comp (split n)), by
      intro u hu
      change sphereMap (F (split n u)) = spherePole 4
      rcases (boundary_split_iff n u).mp hu with h₀ | h₁ | hb
      · change sphereMap (F ((split n u).1, (split n u).2)) = spherePole 4
        rw [h₀]
        exact (congrArg sphereMap (F.map_zero_left _)).trans sphereMap_pole
      · change sphereMap (F ((split n u).1, (split n u).2)) = spherePole 4
        rw [h₁]
        exact (congrArg sphereMap (F.map_one_left _)).trans (sphereMap_unitFiberPoint _)
      · rw [show F (split n u) = spherePole 7 from F.eq_fst (split n u).1 hb]
        exact sphereMap_pole⟩
  let L : CubeLift p := {
    map := F.toContinuousMap
    initial := F.map_zero_left
    project := fun t u ↦ by
      change sphereMap (F (t, u)) = sphereMap (F (split n (join n (t, u))))
      rw [split_join]
    boundary := fun t u hu ↦ F.eq_fst t hu }
  have he : L.endpoint = q := by
    apply GenLoop.ext
    intro u
    apply unitFiberPoint_injective
    rw [L.endpoint_point]
    exact F.map_one_left u
  exact ⟨p, (connecting_eq_endpoint p L).trans (congrArg Quotient.mk' he)⟩

theorem connecting_range_eq_kernel [NeZero n] (a : HomotopyGroup (Fin n) FiberGroup 1) :
    (∃ b : HomotopyGroup (Fin (n + 1)) (Sphere 4) (spherePole 4), connecting n b = a) ↔
      inclusionMap n a = 1 := by
  constructor
  · rintro ⟨b, rfl⟩
    exact inclusionMap_connecting b
  · refine Quotient.inductionOn a fun q hq ↦ ?_
    obtain ⟨p, hp⟩ := exists_connecting_of_nullhomotopic q (Quotient.exact hq)
    exact ⟨⟦p⟧, hp⟩

end NoExoticSixSphere.QuaternionicHopf
