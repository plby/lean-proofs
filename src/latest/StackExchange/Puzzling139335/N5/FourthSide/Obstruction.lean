import StackExchange.Puzzling139335.N5.FourthSide.Contacts
import StackExchange.Puzzling139335.N5.FourthSide.Reflection
import StackExchange.Puzzling139335.N5.StrictFrame

/-!
# At least one fourth-piece side contact is a singleton

The strict source frame is obtained from the actual normalized dissection.
Two nontrivial contact sets on the top and right sides would place an actual
source point at the uniquely owned top-right square corner.
-/

open Set

namespace Puzzling139335.N5

theorem Normalized.fourth_right_or_top_subsingleton_of_corner_frame
    {d : SquareDissection} (h : Normalized d) {C : Plane} {c s : ℝ}
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' d.piece 0 = d.piece 2)
    (hC : C ∈ d.piece 0) (hcs : c ^ 2 + s ^ 2 = 1)
    (hs : 0 < s) (hsc : s < c) (hform : CornerPlacementForm e C c s) :
    (d.piece 3 ∩ {p : Plane | p 0 = 1}).Subsingleton ∨
      (d.piece 3 ∩ {p : Plane | p 1 = 1}).Subsingleton := by
  by_contra hnone
  have hR := Set.not_subsingleton_iff.mp (fun hr => hnone (Or.inl hr))
  have hT := Set.not_subsingleton_iff.mp (fun ht => hnone (Or.inr ht))
  obtain ⟨g, hg⟩ := d.congruent 0 3
  have hefit : e '' d.piece 0 ⊆ unitSquare := by
    rw [he]
    exact d.piece_subset 2
  have hgfit : g '' d.piece 0 ⊆ unitSquare := by
    rw [hg]
    exact d.piece_subset 3
  have hR' : (g '' d.piece 0 ∩ {p : Plane | p 0 = 1}).Nontrivial := by
    simpa only [hg] using hR
  have hT' : (g '' d.piece 0 ∩ {p : Plane | p 1 = 1}).Nontrivial := by
    simpa only [hg] using hT
  have himages := FourthSide.two_side_contacts_place_B_or_C
    (d.piece_subset 0) h.below_diagonal h.bottom_left h.bottom_right hC
    hcs hs hsc e hefit hform g hgfit hR' hT'
  apply h.unique_top_right 3 (by decide)
  rw [← hg]
  rcases himages with hB | hCimage
  · exact ⟨corner 1, h.bottom_right, hB⟩
  · exact ⟨C, hC, hCimage⟩

/-- The actual fourth piece has at most one point on its right side or at
most one point on its top side. No frame, normal, or contact certificate is
an input to this theorem. -/
theorem Normalized.fourth_right_or_top_subsingleton {d : SquareDissection}
    (h : Normalized d) (hc : d.HasProtectedCenter) :
    (d.piece 3 ∩ {p : Plane | p 0 = 1}).Subsingleton ∨
      (d.piece 3 ∩ {p : Plane | p 1 = 1}).Subsingleton := by
  obtain ⟨e, he⟩ := d.congruent 0 2
  obtain ⟨c, s, hunit, hs, hsc, _hk, _hkh, _hhc, _hc1, _hz, _hd, hform⟩ :=
    h.exists_strict_corner_frame hc e he
  exact h.fourth_right_or_top_subsingleton_of_corner_frame e he
    (h.third_corner_preimage e he).1 hunit hs hsc hform

/-- A common diagonal reflection and interchange of the first two labels
puts the singleton contact on the right, while leaving the source set
exactly unchanged. -/
theorem Normalized.exists_fourth_right_normalization {d : SquareDissection}
    (h : Normalized d) (hc : d.HasProtectedCenter) :
    ∃ d' : SquareDissection, Normalized d' ∧ d'.piece 0 = d.piece 0 ∧
      (d'.HasProtectedCenter ↔ d.HasProtectedCenter) ∧
      (d'.piece 3 ∩ {p : Plane | p 0 = 1}).Subsingleton :=
  FourthSide.exists_right_subsingleton h (h.fourth_right_or_top_subsingleton hc)

end Puzzling139335.N5
