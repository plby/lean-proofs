import StackExchange.Puzzling139335.N4OuterPair.AxisNonzero
import StackExchange.Puzzling139335.PlaneIsometries.Matrix
import StackExchange.Puzzling139335.SourceFaceBridge.SupportingFaces

/-!
# Actual vertical-side contacts determine upward source normals

Two right-side contacts pull back to two maximizers of the first matrix
row, while two left-side contacts pull back to two maximizers of its
negative.  A downward nonvertical normal has only one source maximizer.
The actual axis exclusions therefore force the relevant source normal
strictly into the upper half-plane.
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

/-- Distinct actual right-side contacts give distinct source support points
for the first row of the congruence matrix. -/
theorem right_contacts_have_two_source_supports {P Q : Set Plane}
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' P = Q) (hQ : Q ⊆ unitSquare)
    (hcontact : (Q ∩ {p : Plane | p 0 = 1}).Nontrivial) :
    HasTwoSupportPoints P (linearMatrix e 0 0) (linearMatrix e 0 1) := by
  obtain ⟨p, hp, q, hq, hpq⟩ := hcontact
  obtain ⟨p₀, hp₀, rfl⟩ : p ∈ e '' P := by
    rw [he]
    exact hp.1
  obtain ⟨q₀, hq₀, rfl⟩ : q ∈ e '' P := by
    rw [he]
    exact hq.1
  refine ⟨p₀, q₀, (fun heq => hpq (congrArg e heq)), ?_, ?_⟩
  · exact source_support_of_right_side e he hQ hp₀ hp.2
  · exact source_support_of_right_side e he hQ hq₀ hq.2

/-- Distinct actual left-side contacts give distinct source support points
for the negative first row of the congruence matrix. -/
theorem left_contacts_have_two_source_supports {P Q : Set Plane}
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' P = Q) (hQ : Q ⊆ unitSquare)
    (hcontact : (Q ∩ {p : Plane | p 0 = 0}).Nontrivial) :
    HasTwoSupportPoints P (-linearMatrix e 0 0) (-linearMatrix e 0 1) := by
  obtain ⟨p, hp, q, hq, hpq⟩ := hcontact
  obtain ⟨p₀, hp₀, rfl⟩ : p ∈ e '' P := by
    rw [he]
    exact hp.1
  obtain ⟨q₀, hq₀, rfl⟩ : q ∈ e '' P := by
    rw [he]
    exact hq.1
  refine ⟨p₀, q₀, (fun heq => hpq (congrArg e heq)), ?_, ?_⟩
  · exact source_opposite_support_of_left_side e he hQ hp₀ hp.2
  · exact source_opposite_support_of_left_side e he hQ hq₀ hq.2

namespace Configuration

variable {d : SquareDissection}

private theorem lower_source_support_assumptions (h : Configuration d) :
    d.piece 0 ⊆ lowerHalfSquare ∧ point 0 0 ∈ d.piece 0 ∧ point 1 0 ∈ d.piece 0 := by
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    exact ⟨(d.piece_subset 0 hp).1, (d.piece_subset 0 hp).2.1,
      (h.outer_halves.1 hp).2.2⟩
  · simpa only [point, Schoenflies.Plane.mk] using h.bottom_left_mk
  · simpa only [point, Schoenflies.Plane.mk] using h.bottom_right_mk

/-- A nontrivial right-side contact forces the first-row source normal upward. -/
theorem right_contact_normal_up (h : Configuration d) (hc : d.HasProtectedCenter)
    {i : Fin 4} (hi : i = 2 ∨ i = 3) (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (he : e '' d.piece 0 = d.piece i)
    (hRnontriv : (d.piece i ∩ {p : Plane | p 0 = 1}).Nontrivial) :
    0 < linearMatrix e 0 1 := by
  have hn := h.middle_normal_nonaxis hc hi e he
  obtain ⟨hsource, hA, hB⟩ := lower_source_support_assumptions h
  by_contra hnot
  have hdown : linearMatrix e 0 1 < 0 :=
    lt_of_le_of_ne (le_of_not_gt hnot) hn.2
  exact SourceFaceBridge.not_hasTwoSupportPoints_of_downward hsource hA hB hn.1 hdown
    (right_contacts_have_two_source_supports e he (d.piece_subset i) hRnontriv)

/-- At the left side the outward source normal is the negative first row,
so its positive vertical component means the row's vertical entry is negative. -/
theorem left_contact_normal_up (h : Configuration d) (hc : d.HasProtectedCenter)
    {i : Fin 4} (hi : i = 2 ∨ i = 3) (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (he : e '' d.piece 0 = d.piece i)
    (hLnontriv : (d.piece i ∩ {p : Plane | p 0 = 0}).Nontrivial) :
    linearMatrix e 0 1 < 0 := by
  have hn := h.middle_normal_nonaxis hc hi e he
  obtain ⟨hsource, hA, hB⟩ := lower_source_support_assumptions h
  by_contra hnot
  have hrow : 0 < linearMatrix e 0 1 :=
    lt_of_le_of_ne (le_of_not_gt hnot) (Ne.symm hn.2)
  exact SourceFaceBridge.not_hasTwoSupportPoints_of_downward hsource hA hB
    (neg_ne_zero.mpr hn.1) (neg_lt_zero.mpr hrow)
    (left_contacts_have_two_source_supports e he (d.piece_subset i) hLnontriv)

end Configuration

end Puzzling139335.N4OuterPair
