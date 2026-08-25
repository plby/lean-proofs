import StackExchange.Puzzling139335.N6.TripleOppositeParity.TopVertex
import StackExchange.Puzzling139335.N6.TripleOppositeParity.SupportArms
import StackExchange.Puzzling139335.N6.TripleOppositeParity.PullbackArms
import StackExchange.Puzzling139335.N6.TripleOppositeParity.SideIntervals
import StackExchange.Puzzling139335.N6.TripleOppositeParity.SideIntervals.Exceptional

/-!
# The normalized opposite-parity triple-corner case is impossible

The three pieces incident to the lower-left corner are the source region,
its thirty-degree rotation, and its diagonal reflection.  The remaining
piece sends another full source corner to the top-right corner.  The proof
uses actual Jordan contacts and explicit support frames throughout.
-/

open Set

namespace Puzzling139335.N6.TripleOppositeParity

open TripleCornerBounds (triangle R30)
open ReflectionSeparation (diagonal)

noncomputable section

theorem rotateThirty_eq_R30 : (TripleSectors.rotateThirty : Plane → Plane) = R30 := by
  funext p
  ext i
  fin_cases i <;> simp [R30, N7Geometry.c]

/-- A normalized opposite-parity triple-corner cover cannot exist.  All
hypotheses describe actual pieces, their affine placement, and their full
corner germ; no arm-length or supporting-direction conclusion is assumed. -/
theorem normalized_impossible {P : Set Plane} (hP : IsJordanRegion P)
    (htriangle : P ⊆ triangle) (h0 : (0 : Plane) ∈ P) (hB : corner 1 ∈ P)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (heS : e '' P ⊆ unitSquare)
    {C : Plane} (hC : UnitPairs.IsFullSquareCorner P C)
    (heC : e C = corner 2) (hCB : C ≠ corner 1)
    (hdisP : Disjoint (interior P) (interior (e '' P)))
    (hdisQ : Disjoint (interior (diagonal '' P)) (interior (e '' P)))
    (hcover : unitSquare ⊆
      P ∪ TripleSectors.rotateThirty '' P ∪ diagonal '' P ∪ e '' P) : False := by
  have hC0 : C ≠ 0 := by
    intro hzero
    exact SupportArms.not_full_origin htriangle (hzero ▸ hC)
  have hD : IsJordanRegion (e '' P) := hP.image_homeomorph e.toHomeomorph
  have hPS : P ⊆ unitSquare := htriangle.trans SupportArms.triangle_subset_square
  have hTR : corner 2 ∈ e '' P := heC ▸ mem_image_of_mem e hC.mem
  have hB' : (!₂[1, 0] : Plane) ∈ P := by simpa [corner] using hB
  have hCB' : C ≠ (!₂[1, 0] : Plane) := by simpa [corner] using hCB
  have hmiddle : ∀ t ∈ Icc (0 : ℝ) 1,
      Schoenflies.Plane.mk t 1 ∉ R30 '' P := by
    intro t _
    exact not_mem_rotated_image_of_y_eq_one htriangle h0 hB' hC hC0 hCB' rfl
  have hcover' : unitSquare ⊆ P ∪ R30 '' P ∪ diagonal '' P ∪ e '' P := by
    simpa only [rotateThirty_eq_R30] using hcover
  obtain ⟨r, hr, hrightP, _, hrightD, htopD⟩ := side_intervals_of_triangle_cover
    hP hD htriangle heS hdisP
    (by simpa [corner, Schoenflies.Plane.mk] using hB)
    (by simpa [corner, Schoenflies.Plane.mk] using hTR) hcover' hmiddle
  have hheight_le_one : 1 / Real.sqrt (3 : ℝ) ≤ 1 := by
    apply (div_le_iff₀ TripleSectors.sqrt_three_pos).mpr
    simpa only [one_mul] using TripleSectors.one_lt_sqrt_three.le
  have hr1 : r ≤ 1 := hr.2.trans hheight_le_one
  have hE : (!₂[1, r] : Plane) ∈ P := by
    simpa [Schoenflies.Plane.mk] using (hrightP r).mpr ⟨hr.1, le_rfl⟩
  have hrightEndpoint : (!₂[1, r] : Plane) ∈ e '' P := by
    simpa [Schoenflies.Plane.mk] using hrightD r ⟨le_rfl, hr1⟩
  have htopEndpoint : (!₂[r, 1] : Plane) ∈ e '' P := by
    simpa [Schoenflies.Plane.mk] using htopD r ⟨le_rfl, hr1⟩
  obtain ⟨hframe⟩ := hC.isSupportCorner
  let k := SupportArms.coordinateCorner hframe
  have harms := full_corner_arms_mem hC k e heS heC htopEndpoint hrightEndpoint
  have hs : SupportArms.sine hframe = 0 :=
    SupportArms.sine_eq_zero_of_long_arm htriangle h0 hB hframe hC0 hCB
      ⟨hr.1, hr1⟩ hE harms.1
  obtain ⟨hc, hCx, hCy0, hCy1⟩ :=
    SupportArms.corner_on_right_of_zero_turn htriangle h0 hB hframe hC0 hCB hE hs
  have hCcoords : C = !₂[1, C 1] := by
    ext i
    fin_cases i
    · exact hCx
    · rfl
  have hnfirst : k.firstNormal = !₂[0, 1] := by
    simp [k, SupportArms.coordinateCorner, hs, hc]
  have hnsecond : k.secondNormal = !₂[1, 0] := by
    simp [k, SupportArms.coordinateCorner, hs, hc]
  rcases full_corner_placement_eq_straight_or_swapped
    hC k e heS heC hCcoords hnfirst hnsecond with he | he
  · have hQ : IsJordanRegion (diagonal '' P) :=
      hP.image_homeomorph diagonal.toHomeomorph
    have hQS : diagonal '' P ⊆ unitSquare := by
      rintro _ ⟨p, hp, rfl⟩
      exact ReflectionSeparation.diagonal_mem_unitSquare.mpr (hPS hp)
    apply SideIntervals.straightPlacement_impossible hQ hD hQS heS hdisQ hCy0 hCy1 rfl
    · rw [he]
    · exact h0
    · exact hB
    · exact hTR
  · apply SideIntervals.swappedPlacement_impossible hP hD hPS heS hdisP hCy0 hCy1
    · rw [he]
    · exact h0
    · exact hB
    · exact hTR

/-- Reflecting the whole square interchanges the two outer pieces and
changes the reflected middle placement to the proper thirty-degree rotation. -/
theorem normalized_reflected_middle_impossible {P : Set Plane} (hP : IsJordanRegion P)
    (htriangle : P ⊆ triangle) (h0 : (0 : Plane) ∈ P) (hB : corner 1 ∈ P)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (heS : e '' P ⊆ unitSquare)
    {C : Plane} (hC : UnitPairs.IsFullSquareCorner P C)
    (heC : e C = corner 2) (hCB : C ≠ corner 1)
    (hdisP : Disjoint (interior P) (interior (e '' P)))
    (hdisQ : Disjoint (interior (diagonal '' P)) (interior (e '' P)))
    (hcover : unitSquare ⊆
      P ∪ TripleSectors.reflectThirty '' P ∪ diagonal '' P ∪ e '' P) : False := by
  let f := e.trans diagonal
  have hfS : f '' P ⊆ unitSquare := by
    rintro _ ⟨p, hp, rfl⟩
    exact ReflectionSeparation.diagonal_mem_unitSquare.mpr (heS (mem_image_of_mem e hp))
  have hfC : f C = corner 2 := by
    change diagonal (e C) = corner 2
    rw [heC]
    ext i
    fin_cases i <;> simp [corner]
  have hQQ : diagonal '' (diagonal '' P) = P := by
    simp only [image_image, ReflectionSeparation.diagonal_involutive,
      image_id']
  have hDimage : diagonal '' (e '' P) = f '' P := by
    rw [image_image]
    rfl
  have hdisP' : Disjoint (interior P) (interior (f '' P)) := by
    have hd := RectangularHull.disjoint_interiors_image_homeomorph hdisQ diagonal.toHomeomorph
    change Disjoint (interior (diagonal '' (diagonal '' P)))
      (interior (diagonal '' (e '' P))) at hd
    simpa only [hQQ, hDimage] using hd
  have hdisQ' : Disjoint (interior (diagonal '' P)) (interior (f '' P)) := by
    have hd := RectangularHull.disjoint_interiors_image_homeomorph hdisP diagonal.toHomeomorph
    change Disjoint (interior (diagonal '' P)) (interior (diagonal '' (e '' P))) at hd
    simpa only [hDimage] using hd
  have hcover' : unitSquare ⊆
      P ∪ TripleSectors.rotateThirty '' P ∪ diagonal '' P ∪ f '' P := by
    intro x hx
    have hdx := hcover (ReflectionSeparation.diagonal_mem_unitSquare.mpr hx)
    rcases hdx with ((hfirst | hmiddle) | hlast) | hremaining
    · exact Or.inl (Or.inr ⟨diagonal x, hfirst, ReflectionSeparation.diagonal_involutive x⟩)
    · obtain ⟨p, hp, heq⟩ := hmiddle
      change diagonal (TripleSectors.rotateThirty p) = diagonal x at heq
      exact Or.inl (Or.inl (Or.inr ⟨p, hp, diagonal.injective heq⟩))
    · obtain ⟨p, hp, heq⟩ := hlast
      exact Or.inl (Or.inl (Or.inl (diagonal.injective heq ▸ hp)))
    · obtain ⟨p, hp, heq⟩ := hremaining
      refine Or.inr ⟨p, hp, ?_⟩
      change diagonal (e p) = x
      rw [heq, ReflectionSeparation.diagonal_involutive]
  exact normalized_impossible hP htriangle h0 hB f hfS hC hfC hCB
    hdisP' hdisQ' hcover'

/-- Both possible orientation parities of the middle sector are excluded. -/
theorem normalized_middle_parity_impossible {P M : Set Plane} (hP : IsJordanRegion P)
    (htriangle : P ⊆ triangle) (h0 : (0 : Plane) ∈ P) (hB : corner 1 ∈ P)
    (hM : M = TripleSectors.rotateThirty '' P ∨ M = TripleSectors.reflectThirty '' P)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (heS : e '' P ⊆ unitSquare)
    {C : Plane} (hC : UnitPairs.IsFullSquareCorner P C)
    (heC : e C = corner 2) (hCB : C ≠ corner 1)
    (hdisP : Disjoint (interior P) (interior (e '' P)))
    (hdisQ : Disjoint (interior (diagonal '' P)) (interior (e '' P)))
    (hcover : unitSquare ⊆ P ∪ M ∪ diagonal '' P ∪ e '' P) : False := by
  rcases hM with rfl | rfl
  · exact normalized_impossible hP htriangle h0 hB e heS hC heC hCB hdisP hdisQ hcover
  · exact normalized_reflected_middle_impossible
      hP htriangle h0 hB e heS hC heC hCB hdisP hdisQ hcover

end

end Puzzling139335.N6.TripleOppositeParity
