import StackExchange.Puzzling139335.N4OuterPair.SideSupport
import StackExchange.Puzzling139335.N4OuterPair.IntervalOwnership
import StackExchange.Puzzling139335.N4OuterPair.SideGaps

/-!
# Each nondegenerate vertical gap has one middle owner

A middle copy cannot have two points on both vertical sides.  A positive
interval covered by the two closed middle contacts therefore has a unique
possible nonsingleton owner, and closedness fills its whole gap.  Strictly
positive gap lengths are explicit inputs here, not a final certificate.
-/

open Set

namespace Puzzling139335.N4OuterPair

def sideContact (d : SquareDissection) (i : Fin 4) (x : ℝ) : Set ℝ :=
  {y | Schoenflies.Plane.mk x y ∈ d.piece i}

theorem sideContact_isClosed (d : SquareDissection) (i : Fin 4) (x : ℝ) :
    IsClosed (sideContact d i x) := by
  apply (d.jordan i).isClosed.preimage
  fun_prop

theorem sideContact_nontrivial_to_plane {d : SquareDissection} {i : Fin 4} {x : ℝ}
    (h : (sideContact d i x).Nontrivial) :
    (d.piece i ∩ {p : Plane | p 0 = x}).Nontrivial := by
  obtain ⟨a, ha, b, hb, hab⟩ := h
  refine ⟨Schoenflies.Plane.mk x a, ⟨ha, rfl⟩,
    Schoenflies.Plane.mk x b, ⟨hb, rfl⟩, ?_⟩
  intro heq
  exact hab (congrArg (fun p : Plane => p 1) heq)

private theorem nontrivial_of_interval_subset {A : Set ℝ} {a b : ℝ}
    (h : Icc a b ⊆ A) (hab : a < b) : A.Nontrivial :=
  ⟨a, h ⟨le_rfl, hab.le⟩, b, h ⟨hab.le, le_rfl⟩, hab.ne⟩

private theorem nontrivial_of_inter {A I : Set ℝ} (h : (A ∩ I).Nontrivial) :
    A.Nontrivial := by
  obtain ⟨a, ha, b, hb, hab⟩ := h
  exact ⟨a, ha.1, b, hb.1, hab⟩

namespace Configuration

variable {d : SquareDissection}

theorem right_contact_subsingleton_of_left (h : Configuration d) (hc : d.HasProtectedCenter)
    {i : Fin 4} (hi : i = 2 ∨ i = 3) (hleft : (sideContact d i 0).Nontrivial) :
    (sideContact d i 1).Subsingleton := by
  intro a ha b hb
  by_contra hab
  exact h.middle_not_two_vertical_contacts hc hi
    ⟨sideContact_nontrivial_to_plane hleft,
      sideContact_nontrivial_to_plane ⟨a, ha, b, hb, hab⟩⟩

theorem left_contact_subsingleton_of_right (h : Configuration d) (hc : d.HasProtectedCenter)
    {i : Fin 4} (hi : i = 2 ∨ i = 3) (hright : (sideContact d i 1).Nontrivial) :
    (sideContact d i 0).Subsingleton := by
  intro a ha b hb
  by_contra hab
  exact h.middle_not_two_vertical_contacts hc hi
    ⟨sideContact_nontrivial_to_plane ⟨a, ha, b, hb, hab⟩,
      sideContact_nontrivial_to_plane hright⟩

/-- The two positive gaps are wholly owned by different middle pieces.
The result includes their endpoints and allows singleton extra contacts. -/
theorem side_gap_owners (h : Configuration d) (hc : d.HasProtectedCenter)
    {a b : ℝ} (ha0 : 0 ≤ a) (ha : a < 1 / 2) (hb0 : 0 ≤ b) (hb : b < 1 / 2)
    (hleft : ∀ y : ℝ, Schoenflies.Plane.mk 0 y ∈ d.piece 0 ↔ y ∈ Icc (0 : ℝ) a)
    (hright : ∀ y : ℝ, Schoenflies.Plane.mk 1 y ∈ d.piece 0 ↔ y ∈ Icc (0 : ℝ) b) :
    (Icc a (1 - a) ⊆ sideContact d 2 0 ∧ Icc b (1 - b) ⊆ sideContact d 3 1) ∨
      (Icc a (1 - a) ⊆ sideContact d 3 0 ∧ Icc b (1 - b) ⊆ sideContact d 2 1) := by
  have ha' : a < 1 - a := by linarith only [ha]
  have hb' : b < 1 - b := by linarith only [hb]
  have hcoverL : Icc a (1 - a) ⊆ sideContact d 2 0 ∪ sideContact d 3 0 :=
    h.closed_side_gap_covered (Or.inl rfl) ha0 ha hleft
  have hcoverR : Icc b (1 - b) ⊆ sideContact d 2 1 ∪ sideContact d 3 1 :=
    h.closed_side_gap_covered (Or.inr rfl) hb0 hb hright
  rcases nontrivial_contacts_of_interval_cover hcoverL ha' with hL2 | hL3
  · have hR2sub := h.right_contact_subsingleton_of_left hc (Or.inl rfl)
      (nontrivial_of_inter hL2)
    have hR3 : Icc b (1 - b) ⊆ sideContact d 3 1 :=
      closed_interval_subset_of_subsingleton_other (sideContact_isClosed d 3 1)
        (by simpa only [union_comm] using hcoverR)
        (fun _ hx _ hy => hR2sub hx.1 hy.1) hb'
    have hL3sub := h.left_contact_subsingleton_of_right hc (Or.inr rfl)
      (nontrivial_of_interval_subset hR3 hb')
    have hL2 : Icc a (1 - a) ⊆ sideContact d 2 0 :=
      closed_interval_subset_of_subsingleton_other (sideContact_isClosed d 2 0) hcoverL
        (fun _ hx _ hy => hL3sub hx.1 hy.1) ha'
    exact Or.inl ⟨hL2, hR3⟩
  · have hR3sub := h.right_contact_subsingleton_of_left hc (Or.inr rfl)
      (nontrivial_of_inter hL3)
    have hR2 : Icc b (1 - b) ⊆ sideContact d 2 1 :=
      closed_interval_subset_of_subsingleton_other (sideContact_isClosed d 2 1) hcoverR
        (fun _ hx _ hy => hR3sub hx.1 hy.1) hb'
    have hL2sub := h.left_contact_subsingleton_of_right hc (Or.inl rfl)
      (nontrivial_of_interval_subset hR2 hb')
    have hL3 : Icc a (1 - a) ⊆ sideContact d 3 0 :=
      closed_interval_subset_of_subsingleton_other (sideContact_isClosed d 3 0)
        (by simpa only [union_comm] using hcoverL)
        (fun _ hx _ hy => hL2sub hx.1 hy.1) ha'
    exact Or.inr ⟨hL3, hR2⟩

end Configuration

end Puzzling139335.N4OuterPair
