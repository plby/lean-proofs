import Wikipedia.HomotopyGroupsOfSpheres.RankSixSpinorConnectingHom
import Wikipedia.HomotopyGroupsOfSpheres.Basic

/-!
# Exactness constructions for the spinor circle fibration

A total-space null-homotopy gives a preimage of a circle class. Conversely,
a null-homotopy of the last-face circle coordinate closes a spinor lift by
an inverse phase, without changing its complex-structure projection.
-/

noncomputable section

open scoped unitInterval

namespace NoExoticSixSphere.RankSixComplexProjection.SpinorFibration

open NoExoticSixSphere.CubeFirstCoordinate Wikipedia.HopfProblem.SecondHurewicz

variable {d : ℕ} (A : UnitSpinor)

def fiberInclusion : C(Circle, UnitSpinor) :=
  ⟨fun z ↦ phaseSmul z A, continuous_phaseSmul.comp (continuous_id.prodMk continuous_const)⟩

def fiberLoop (q : GenLoop (Fin d) Circle 1) : GenLoop (Fin d) UnitSpinor A :=
  ⟨(fiberInclusion A).comp q.val, fun u hu ↦ by
    change phaseSmul (q u) A = A
    have hq : q u = 1 := q.property u hu
    rw [hq, phaseSmul_one]⟩

theorem exists_connecting_of_nullhomotopic (q : GenLoop (Fin d) Circle 1)
    (hq : GenLoop.Homotopic (fiberLoop A q) GenLoop.const) :
    ∃ p : GenLoop (Fin (d + 1)) (OrthogonalComplexStructures.Space 6) (fromSpinor A),
      connecting A d (⟦p⟧ : HomotopyGroup (Fin (d + 1))
        (OrthogonalComplexStructures.Space 6) (fromSpinor A)) =
        (⟦q⟧ : HomotopyGroup (Fin d) Circle 1) := by
  obtain ⟨H⟩ := hq
  let F := H.symm
  let p : GenLoop (Fin (d + 1)) (OrthogonalComplexStructures.Space 6) (fromSpinor A) :=
    ⟨map.comp (F.toContinuousMap.comp (split d)), by
      intro u hu
      change fromSpinor (F (split d u)) = fromSpinor A
      rcases (boundary_split_iff d u).mp hu with h₀ | h₁ | hb
      · change fromSpinor (F ((split d u).1, (split d u).2)) = fromSpinor A
        rw [h₀]
        exact congrArg fromSpinor (F.map_zero_left _)
      · change fromSpinor (F ((split d u).1, (split d u).2)) = fromSpinor A
        rw [h₁]
        exact (congrArg fromSpinor (F.map_one_left _)).trans (fromSpinor_phaseSmul _ A)
      · exact congrArg fromSpinor (F.eq_fst (split d u).1 hb)⟩
  let L : CubeLift A p := {
    map := F.toContinuousMap
    initial := F.map_zero_left
    project := fun t u ↦ by
      change fromSpinor (F (t, u)) = fromSpinor (F (split d (join d (t, u))))
      rw [split_join]
    boundary := fun t u hu ↦ F.eq_fst t hu }
  have he : L.endpoint = q := by
    apply GenLoop.ext
    intro u
    change coordinate A (F (1, u)) (L.endpoint_project u).symm = q u
    have hF : F (1, u) = phaseSmul (q u) A := F.map_one_left u
    simp only [hF, coordinate_phaseSmul]
  exact ⟨p, (connecting_eq_endpoint A p L).trans (congrArg Quotient.mk' he)⟩

theorem exists_closed_lift
    {p : GenLoop (Fin (d + 1)) (OrthogonalComplexStructures.Space 6) (fromSpinor A)}
    (L : CubeLift A p) (h : GenLoop.Homotopic L.endpoint GenLoop.const) :
    ∃ q : GenLoop (Fin (d + 1)) UnitSpinor A, mapGenLoop map A q = p := by
  obtain ⟨H⟩ := h
  let F := H.symm
  let M : C(I × (Fin d → I), UnitSpinor) :=
    ⟨fun z ↦ phaseSmul (F z)⁻¹ (L.map z),
      continuous_phaseSmul.comp (F.continuous.inv.prodMk L.map.continuous)⟩
  have hM₀ (u : Fin d → I) : M (0, u) = A := by
    have hF : F (0, u) = (1 : Circle) := F.map_zero_left u
    change phaseSmul (F (0, u))⁻¹ (L.map (0, u)) = A
    rw [L.initial, hF, inv_one, phaseSmul_one]
  have hM₁ (u : Fin d → I) : M (1, u) = A := by
    have hF : F (1, u) = L.endpoint u := F.map_one_left u
    have hL : phaseSmul (L.endpoint u) A = L.map (1, u) :=
      phaseSmul_coordinate A _ (L.endpoint_project u).symm
    change phaseSmul (F (1, u))⁻¹ (L.map (1, u)) = A
    rw [hF, ← hL, ← phaseSmul_mul, inv_mul_cancel, phaseSmul_one]
  have hMb (t : I) (u : Fin d → I) (hu : u ∈ Cube.boundary (Fin d)) : M (t, u) = A := by
    have hF : F (t, u) = (1 : Circle) := F.eq_fst t hu
    change phaseSmul (F (t, u))⁻¹ (L.map (t, u)) = A
    rw [L.boundary t u hu, hF, inv_one, phaseSmul_one]
  have hMp (t : I) (u : Fin d → I) : fromSpinor (M (t, u)) = p (join d (t, u)) :=
    (fromSpinor_phaseSmul (F (t, u))⁻¹ (L.map (t, u))).trans (L.project t u)
  let q : GenLoop (Fin (d + 1)) UnitSpinor A :=
    ⟨M.comp (split d), by
      intro u hu
      change M (split d u) = A
      rcases (boundary_split_iff d u).mp hu with h₀ | h₁ | hb
      · change M ((split d u).1, (split d u).2) = A
        rw [h₀]
        exact hM₀ _
      · change M ((split d u).1, (split d u).2) = A
        rw [h₁]
        exact hM₁ _
      · exact hMb _ _ hb⟩
  refine ⟨q, ?_⟩
  apply GenLoop.ext
  intro u
  exact (hMp (split d u).1 (split d u).2).trans (congrArg p (join_split d u))

end NoExoticSixSphere.RankSixComplexProjection.SpinorFibration
