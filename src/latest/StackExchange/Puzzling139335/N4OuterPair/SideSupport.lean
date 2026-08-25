import StackExchange.Puzzling139335.N4OuterPair.AxisNonzero
import StackExchange.Puzzling139335.PlaneIsometries.Matrix
import StackExchange.Puzzling139335.SourceFaceBridge.SupportingFaces

/-!
# A middle piece cannot have two contacts on both vertical sides

Pulling square-side contacts back through an actual congruence gives source
supporting points for opposite normals.  Both normal components are nonzero
by the actual axis exclusions.  The lower source contains its base endpoints,
so the opposite-support obstruction applies without any positive-length
face, interval, or interface hypothesis.
-/

open Set

namespace Puzzling139335.N4OuterPair

open PlaneIsometries SourceFaceBridge

private theorem affine_x_coordinates (e : Plane ≃ᵃⁱ[ℝ] Plane) (p : Plane) :
    (e p) 0 = linearMatrix e 0 0 * p 0 + linearMatrix e 0 1 * p 1 + (e 0) 0 :=
  congrArg (fun q : Plane => q 0) (affine_apply_eq_matrix_coordinates e p)

private theorem source_support_of_right_side {P Q : Set Plane}
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' P = Q) (hQ : Q ⊆ unitSquare)
    {p : Plane} (hp : p ∈ P) (hpx : (e p) 0 = 1) :
    SupportsAt P (linearMatrix e 0 0) (linearMatrix e 0 1) p := by
  refine ⟨hp, ?_⟩
  intro q hq
  have hqQ : e q ∈ Q := he ▸ mem_image_of_mem e hq
  have hqx : (e q) 0 ≤ 1 := (hQ hqQ).1.2
  have hep := affine_x_coordinates e p
  have heq := affine_x_coordinates e q
  linarith only [hqx, hpx, hep, heq]

private theorem source_opposite_support_of_left_side {P Q : Set Plane}
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' P = Q) (hQ : Q ⊆ unitSquare)
    {p : Plane} (hp : p ∈ P) (hpx : (e p) 0 = 0) :
    SupportsAt P (-linearMatrix e 0 0) (-linearMatrix e 0 1) p := by
  refine ⟨hp, ?_⟩
  intro q hq
  have hqQ : e q ∈ Q := he ▸ mem_image_of_mem e hq
  have hqx : 0 ≤ (e q) 0 := (hQ hqQ).1.1
  have hep := affine_x_coordinates e p
  have heq := affine_x_coordinates e q
  nlinarith only [hqx, hpx, hep, heq]

namespace Configuration

variable {d : SquareDissection}

/-- With an explicit actual congruence from the bottom piece, neither
middle piece can have two distinct contacts on each vertical square side. -/
theorem middle_vertical_contacts_not_both_nontrivial_of_isometry
    (h : Configuration d) (hc : d.HasProtectedCenter) {i : Fin 4}
    (hi : i = 2 ∨ i = 3) (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (he : e '' d.piece 0 = d.piece i) :
    ¬ ((d.piece i ∩ {p : Plane | p 0 = 0}).Nontrivial ∧
      (d.piece i ∩ {p : Plane | p 0 = 1}).Nontrivial) := by
  intro hboth
  have hn := h.middle_normal_nonaxis hc hi e he
  have hsource : d.piece 0 ⊆ lowerHalfSquare := by
    intro p hp
    exact ⟨(d.piece_subset 0 hp).1, (d.piece_subset 0 hp).2.1,
      (h.outer_halves.1 hp).2.2⟩
  have hA : point 0 0 ∈ d.piece 0 := by
    simpa only [point, Schoenflies.Plane.mk] using h.bottom_left_mk
  have hB : point 1 0 ∈ d.piece 0 := by
    simpa only [point, Schoenflies.Plane.mk] using h.bottom_right_mk
  apply SourceFaceBridge.no_opposite_nonaxis_supports hsource hA hB hn.1 hn.2
  constructor
  · obtain ⟨p, hp, q, hq, hpq⟩ := hboth.2
    obtain ⟨p₀, hp₀, rfl⟩ : p ∈ e '' d.piece 0 := by
      rw [he]
      exact hp.1
    obtain ⟨q₀, hq₀, rfl⟩ : q ∈ e '' d.piece 0 := by
      rw [he]
      exact hq.1
    refine ⟨p₀, q₀, (fun heq => hpq (congrArg e heq)), ?_, ?_⟩
    · exact source_support_of_right_side e he (d.piece_subset i) hp₀ hp.2
    · exact source_support_of_right_side e he (d.piece_subset i) hq₀ hq.2
  · obtain ⟨p, hp, q, hq, hpq⟩ := hboth.1
    obtain ⟨p₀, hp₀, rfl⟩ : p ∈ e '' d.piece 0 := by
      rw [he]
      exact hp.1
    obtain ⟨q₀, hq₀, rfl⟩ : q ∈ e '' d.piece 0 := by
      rw [he]
      exact hq.1
    refine ⟨p₀, q₀, (fun heq => hpq (congrArg e heq)), ?_, ?_⟩
    · exact source_opposite_support_of_left_side e he (d.piece_subset i) hp₀ hp.2
    · exact source_opposite_support_of_left_side e he (d.piece_subset i) hq₀ hq.2

/-- The actual congruence supplied by the dissection gives the opposite-side
contact obstruction without selecting an isometry in the statement. -/
theorem middle_vertical_contacts_not_both_nontrivial
    (h : Configuration d) (hc : d.HasProtectedCenter) {i : Fin 4}
    (hi : i = 2 ∨ i = 3) :
    ¬ ((d.piece i ∩ {p : Plane | p 0 = 0}).Nontrivial ∧
      (d.piece i ∩ {p : Plane | p 0 = 1}).Nontrivial) := by
  obtain ⟨e, he⟩ := d.congruent 0 i
  exact h.middle_vertical_contacts_not_both_nontrivial_of_isometry hc hi e he

/-- A middle piece cannot have two distinct actual contacts on each of the
two vertical square sides. -/
theorem middle_not_two_vertical_contacts
    (h : Configuration d) (hc : d.HasProtectedCenter) {i : Fin 4}
    (hi : i = 2 ∨ i = 3) :
    ¬ ((d.piece i ∩ {p : Plane | p 0 = 0}).Nontrivial ∧
      (d.piece i ∩ {p : Plane | p 0 = 1}).Nontrivial) :=
  h.middle_vertical_contacts_not_both_nontrivial hc hi

/-- At least one vertical square side meets a middle piece in at most one point. -/
theorem middle_vertical_contact_subsingleton
    (h : Configuration d) (hc : d.HasProtectedCenter) {i : Fin 4}
    (hi : i = 2 ∨ i = 3) :
    (d.piece i ∩ {p : Plane | p 0 = 0}).Subsingleton ∨
      (d.piece i ∩ {p : Plane | p 0 = 1}).Subsingleton := by
  rcases (d.piece i ∩ {p : Plane | p 0 = 0}).subsingleton_or_nontrivial with hleft | hleft
  · exact Or.inl hleft
  · apply Or.inr
    apply Set.not_nontrivial_iff.mp
    intro hright
    exact h.middle_vertical_contacts_not_both_nontrivial hc hi ⟨hleft, hright⟩

end Configuration

end Puzzling139335.N4OuterPair
