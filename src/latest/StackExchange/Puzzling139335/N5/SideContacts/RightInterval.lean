import StackExchange.Puzzling139335.N5.SideContacts.RightInterval.Downward
import StackExchange.Puzzling139335.N5.SideContacts.RightInterval.CompactInitial

/-!
# The exact initial interval on the right side

Two disjoint Jordan interiors cannot alternate along the right boundary.
Consequently the lower piece's right contacts are downward closed.  Closedness
and the square bounds give a greatest contact, and the endpoint hypotheses
put it strictly between zero and one.
-/

open Set

namespace Puzzling139335.N5.SideContacts

/-- The right-side contacts of the lower piece form exactly one nontrivial
initial interval.  Only the actual Jordan regions, their side coverage, and
their stated endpoint memberships are inputs. -/
theorem right_side_initial_interval {P Q : Set Plane}
    (hP : IsJordanRegion P) (hQ : IsJordanRegion Q)
    (hPS : P ⊆ unitSquare) (hQS : Q ⊆ unitSquare)
    (hdis : Disjoint (interior P) (interior Q))
    (hBR : Schoenflies.Plane.mk 1 0 ∈ P) (hTR : Schoenflies.Plane.mk 1 1 ∈ Q)
    (hTRnotP : Schoenflies.Plane.mk 1 1 ∉ P)
    (hcover : ∀ y ∈ Icc (0 : ℝ) 1,
      Schoenflies.Plane.mk 1 y ∈ P ∨ Schoenflies.Plane.mk 1 y ∈ Q)
    (hpositive : ∃ y > 0, Schoenflies.Plane.mk 1 y ∈ P) :
    ∃ b : ℝ, 0 < b ∧ b < 1 ∧
      ∀ y : ℝ, Schoenflies.Plane.mk 1 y ∈ P ↔ 0 ≤ y ∧ y ≤ b := by
  let T : Set ℝ := {y | Schoenflies.Plane.mk 1 y ∈ P}
  have hclosed : IsClosed T := hP.isClosed.preimage (by fun_prop)
  have hsub : T ⊆ Icc (0 : ℝ) 1 := fun y hy => (hPS hy).2
  have hpos : ∃ y ∈ T, 0 < y := by
    obtain ⟨y, hy0, hyP⟩ := hpositive
    exact ⟨y, hyP, hy0⟩
  have hdown : ∀ {c : ℝ}, c ∈ T → ∀ b ∈ Icc (0 : ℝ) c, b ∈ T := by
    intro c hc b hb
    exact right_side_contacts_downward hP hQ hPS hQS hdis hBR hTR hTRnotP hcover hc b hb
  exact exists_positive_initial_interval hclosed hsub hBR hTRnotP hpos hdown

/-- The same result with coverage stated as an inclusion of the actual right
side segment. -/
theorem right_side_initial_interval_of_segment_cover {P Q : Set Plane}
    (hP : IsJordanRegion P) (hQ : IsJordanRegion Q)
    (hPS : P ⊆ unitSquare) (hQS : Q ⊆ unitSquare)
    (hdis : Disjoint (interior P) (interior Q))
    (hBR : Schoenflies.Plane.mk 1 0 ∈ P) (hTR : Schoenflies.Plane.mk 1 1 ∈ Q)
    (hTRnotP : Schoenflies.Plane.mk 1 1 ∉ P)
    (hcover : segment ℝ (Schoenflies.Plane.mk 1 0) (Schoenflies.Plane.mk 1 1) ⊆ P ∪ Q)
    (hpositive : ∃ y > 0, Schoenflies.Plane.mk 1 y ∈ P) :
    ∃ b : ℝ, 0 < b ∧ b < 1 ∧
      ∀ y : ℝ, Schoenflies.Plane.mk 1 y ∈ P ↔ 0 ≤ y ∧ y ≤ b := by
  apply right_side_initial_interval hP hQ hPS hQS hdis hBR hTR hTRnotP ?_ hpositive
  intro y hy
  apply hcover
  rw [Schoenflies.mem_segment_vert, segment_eq_Icc (show (0 : ℝ) ≤ 1 by norm_num)]
  exact ⟨rfl, hy⟩

end Puzzling139335.N5.SideContacts
