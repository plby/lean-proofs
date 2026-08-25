import StackExchange.Puzzling139335.N4Midline.OrderedGeometry
import StackExchange.Puzzling139335.N4Midline.EndpointMass

/-!
# The ordered repeated-midline case

The center cannot belong to either member of the reflected pair or to
the middle ordered corner placement. If it belongs to the last placement,
the geometry forces an endpoint configuration excluded by weighted mass.
-/

open Set

namespace Puzzling139335.N4Midline

open ThreeCorners

noncomputable section

theorem ordered_not_protected (d : SquareDissection)
    (hmirror : midlineReflection '' d.piece 0 = d.piece 1)
    (hzero : (0 : Plane) ∈ d.piece 0) (hleft : d.piece 0 ⊆ leftHalfSquare)
    (b c : Fin 4) (hindices : (b = 2 ∧ c = 3) ∨ (b = 3 ∧ c = 2))
    (B C : Plane) (θ φ : ℝ)
    (eB eC : Plane ≃ᵃⁱ[ℝ] Plane)
    (himageB : eB '' d.piece 0 = d.piece b)
    (himageC : eC '' d.piece 0 = d.piece c)
    (hcornerB : eB B = corner b) (hcornerC : eC C = corner c)
    (hfullB : UnitPairs.IsFullSquareCorner (d.piece 0) B)
    (hfullC : UnitPairs.IsFullSquareCorner (d.piece 0) C)
    (hB : SupportCorner (d.piece 0) B) (hC : SupportCorner (d.piece 0) C)
    (hbisectorB : hB.bisector = outwardBisector θ)
    (hbisectorC : hC.bisector = outwardBisector φ)
    (hconeB : d.piece 0 ⊆ supportCone B θ)
    (hconeC : d.piece 0 ⊆ supportCone C φ)
    (hθ : θ ∈ Icc (Real.pi / 2) Real.pi)
    (hφ : φ ∈ Icc (θ + Real.pi / 2) (3 * Real.pi / 2)) :
    ¬ d.HasProtectedCenter := by
  intro hprotected
  have hdis : Disjoint (interior (d.piece 0))
      (interior (midlineReflection '' d.piece 0)) := by
    rw [hmirror]
    exact d.disjoint_interiors (by decide : (0 : Fin 4) ≠ 1)
  have hpairNot := squareCenter_not_mem_reflected_pair hdis
  rw [hmirror] at hpairNot
  have hsubB : eB '' d.piece 0 ⊆ unitSquare := by
    rw [himageB]
    exact d.piece_subset b
  have hcenterB := frameCenter_maps_to_squareCenter hfullB hB hbisectorB
    eB b hsubB hcornerB
  have hmiddleNot := middle_placement_center_not_interior hleft hB.mem hθ
    eB himageB hcenterB
  have hlast : squareCenter ∈ interior (d.piece c) := by
    obtain ⟨i, hi⟩ := hprotected
    have henum : i = 0 ∨ i = 1 ∨ i = b ∨ i = c := by
      rcases hindices with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> fin_cases i <;> simp
    rcases henum with rfl | rfl | rfl | rfl
    · exact (hpairNot.1 hi).elim
    · exact (hpairNot.2 hi).elim
    · exact (hmiddleNot hi).elim
    · exact hi
  obtain ⟨hθendpoint, hBendpoint⟩ := ordered_midpoint_forced d hmirror hzero hleft
    b c hindices B C θ φ eB eC himageB himageC hcornerB hcornerC hfullB hfullC
    hB hC hbisectorB hbisectorC hconeB hconeC hθ hφ hlast
  have hbtop : b = 2 ∨ b = 3 := hindices.elim
    (fun h => Or.inl h.1) (fun h => Or.inr h.1)
  have hctop : c = 2 ∨ c = 3 := hindices.elim
    (fun h => Or.inr h.2) (fun h => Or.inl h.2)
  have hcb : c ≠ b := by
    rcases hindices with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  apply d.false_of_upper_endpoint_reflected_pair hmirror hleft hbtop hctop hcb
    eB himageB
  · simpa only [hBendpoint] using hcornerB
  · simpa only [frameCenter, hθendpoint, hBendpoint] using hcenterB
  · exact hlast

end

end Puzzling139335.N4Midline
