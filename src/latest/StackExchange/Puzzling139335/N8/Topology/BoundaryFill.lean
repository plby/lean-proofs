import StackExchange.Puzzling139335.JordanCurveRigidity

/-!
# A Jordan subregion containing the ambient frontier

The exterior of a closed Jordan region is the unbounded complementary
region of its frontier.  A Jordan subregion which contains the whole ambient
frontier must therefore be the ambient region itself.  These statements use
only Jordan topology and require no boundary-length or area assumptions.
-/

open Set Schoenflies

namespace Puzzling139335.N8

/-- The unbounded region of a Jordan frontier is the complement of the filled
Jordan region. -/
theorem outside_frontier_eq_compl {P : Set Plane} (hP : IsJordanRegion P) :
    outside (frontier P) = Pᶜ := by
  obtain ⟨C, hC, rfl⟩ := hP
  have hsep := jordan_curve_theorem hC
  rw [frontier_closure_inside hsep, (IsRegionOf.inside C).closure_eq hsep]
  ext x
  constructor
  · intro hx
    rintro (hin | hcurve)
    · exact Set.disjoint_left.mp disjoint_inside_outside hin hx
    · exact hx.1 hcurve
  · intro hx
    have hxc : x ∈ Cᶜ := fun hcurve => hx (Or.inr hcurve)
    have hor : x ∈ inside C ∪ outside C := by
      rwa [inside_union_outside]
    exact hor.resolve_left (fun hin => hx (Or.inl hin))

/-- A Jordan subregion containing the entire frontier of its ambient Jordan
region equals that region. -/
theorem eq_of_subset_of_frontier_subset {P S : Set Plane}
    (hP : IsJordanRegion P) (hS : IsJordanRegion S)
    (hPS : P ⊆ S) (hfront : frontier S ⊆ P) : P = S := by
  apply (hS.eq_of_frontier_subset hP ?_).symm
  intro x hx
  refine ⟨subset_closure (hfront hx), ?_⟩
  exact fun hxP => hx.2 (interior_mono hPS hxP)

end Puzzling139335.N8
