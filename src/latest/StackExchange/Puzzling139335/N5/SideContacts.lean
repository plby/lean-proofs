import StackExchange.Puzzling139335.N5.SideContacts.OuterTopology
import StackExchange.Puzzling139335.N5.SideContacts.RightInterval
import StackExchange.Puzzling139335.N5.SideContacts.DiagonalInterval

/-!
# Exact right-side and diagonal contacts in the five-incidence case

Both intervals are derived from the actual normalized dissection.  The
right-side interval follows from Jordan interlacing with the connected
middle remainder.  The diagonal interval follows from connectedness of
the whole common set of the reflected pair.  Positive endpoint bounds
come from actual relative corner neighborhoods, and the protected center
puts the diagonal endpoint strictly below one half.
-/

open Set

namespace Puzzling139335.N5

variable {d : SquareDissection}

/-- The above-diagonal piece has no contact at all with the right side:
its only possible point would be the uniquely owned top-right corner. -/
theorem Normalized.right_side_not_mem_one (h : Normalized d) (y : ℝ) :
    Schoenflies.Plane.mk 1 y ∉ d.piece 1 := by
  intro hy
  have hfit := d.piece_subset 1 hy
  have habove := h.above_diagonal hy
  have hy1 : y = 1 := le_antisymm hfit.2.2 habove
  subst y
  apply h.unique_top_right 1 (by decide)
  simpa [corner, Fin.ext_iff, Schoenflies.Plane.mk] using hy

/-- On the fixed diagonal, membership in the first piece is exactly
membership in both pieces of the reflected pair. -/
theorem Normalized.diagonal_mem_outer_inter_iff (h : Normalized d) (t : ℝ) :
    Schoenflies.Plane.mk t t ∈ d.piece 0 ∩ d.piece 1 ↔
      Schoenflies.Plane.mk t t ∈ d.piece 0 := by
  constructor
  · exact fun ht => ht.1
  · intro ht
    refine ⟨ht, ?_⟩
    rw [← h.diagonal_image]
    exact ⟨Schoenflies.Plane.mk t t, ht, ReflectionSeparation.diagonal_fixed rfl⟩

/-- The right-side contact is exactly one closed interval starting at the
bottom-right corner, with strictly positive length less than one. -/
theorem Normalized.exists_right_contact_interval (h : Normalized d)
    (hc : d.HasProtectedCenter) :
    ∃ b : ℝ, 0 < b ∧ b < 1 ∧
      ∀ y : ℝ, Schoenflies.Plane.mk 1 y ∈ d.piece 0 ↔ 0 ≤ y ∧ y ≤ b := by
  have hdis : Disjoint (interior (d.piece 0)) (interior (d.piece 2 ∪ d.piece 3)) :=
    (disjoint_union_right.mpr
      ⟨d.disjoint_interior_piece (by decide : (0 : Fin 4) ≠ 2),
       d.disjoint_interior_piece (by decide : (0 : Fin 4) ≠ 3)⟩).mono_right interior_subset
  have hBR : Schoenflies.Plane.mk 1 0 ∈ d.piece 0 := by
    simpa [corner, Fin.ext_iff, Schoenflies.Plane.mk] using h.bottom_right
  have hTR : Schoenflies.Plane.mk 1 1 ∈ d.piece 2 ∪ d.piece 3 := by
    left
    simpa [corner, Fin.ext_iff, Schoenflies.Plane.mk] using h.top_right
  have hTRnot : Schoenflies.Plane.mk 1 1 ∉ d.piece 0 := by
    simpa [corner, Fin.ext_iff, Schoenflies.Plane.mk] using
      h.unique_top_right 0 (by decide)
  have hcover : ∀ y ∈ Icc (0 : ℝ) 1,
      Schoenflies.Plane.mk 1 y ∈ d.piece 0 ∨
        Schoenflies.Plane.mk 1 y ∈ d.piece 2 ∪ d.piece 3 := by
    intro y hy
    have hsq : Schoenflies.Plane.mk 1 y ∈ unitSquare := ⟨by norm_num, hy⟩
    obtain ⟨i, hi⟩ := d.exists_piece_mem hsq
    fin_cases i
    · exact Or.inl hi
    · exact (h.right_side_not_mem_one y hi).elim
    · exact Or.inr (Or.inl hi)
    · exact Or.inr (Or.inr hi)
  exact SideContacts.right_side_initial_interval
    (d.jordan 0) (h.remainder_jordan hc) (d.piece_subset 0)
    (union_subset (d.piece_subset 2) (d.piece_subset 3))
    hdis hBR hTR hTRnot hcover h.exists_positive_right_contact

/-- The whole diagonal contact is exactly one closed interval starting at
the split corner, with endpoint strictly between zero and the center. -/
theorem Normalized.exists_diagonal_contact_interval (h : Normalized d)
    (hc : d.HasProtectedCenter) :
    ∃ a : ℝ, 0 < a ∧ a < 1 / 2 ∧
      ∀ t : ℝ, Schoenflies.Plane.mk t t ∈ d.piece 0 ↔ 0 ≤ t ∧ t ≤ a := by
  have hzero : Schoenflies.Plane.mk 0 0 ∈ d.piece 0 ∩ d.piece 1 := by
    simpa [corner, Fin.ext_iff, Schoenflies.Plane.mk] using
      And.intro h.bottom_left h.left_bottom
  have hpositive : ∃ p ∈ d.piece 0 ∩ d.piece 1, 0 < p 0 := by
    obtain ⟨a, ha0, _, _, ha⟩ := h.exists_common_diagonal_interior
    exact ⟨Schoenflies.Plane.mk a a, ha, ha0⟩
  have hcenter : squareCenter ∉ d.piece 0 ∩ d.piece 1 := by
    intro hp
    exact h.center_not_mem_outer_pair hc (Or.inl hp.1)
  obtain ⟨a, ha0, ha1, hmem⟩ := exists_diagonal_interval_of_compact_preconnected
    ((d.jordan 0).isCompact.inter (d.jordan 1).isCompact)
    (h.outer_inter_isConnected hc).isPreconnected
    (fun p hp => d.piece_subset 0 hp.1) h.outer_inter_diagonal hzero hpositive hcenter
  refine ⟨a, ha0, ha1, ?_⟩
  intro t
  exact (h.diagonal_mem_outer_inter_iff t).symm.trans (hmem t)

/-- A common choice of the two actual interval parameters, including the
endpoint memberships needed by subsequent supporting-line calculations. -/
theorem Normalized.exists_side_contact_parameters (h : Normalized d)
    (hc : d.HasProtectedCenter) :
    ∃ a b : ℝ, 0 < a ∧ a < 1 / 2 ∧ 0 < b ∧ b < 1 ∧
      Schoenflies.Plane.mk a a ∈ d.piece 0 ∧
      Schoenflies.Plane.mk 1 b ∈ d.piece 0 ∧
      (∀ t : ℝ, Schoenflies.Plane.mk t t ∈ d.piece 0 ↔ 0 ≤ t ∧ t ≤ a) ∧
      (∀ y : ℝ, Schoenflies.Plane.mk 1 y ∈ d.piece 0 ↔ 0 ≤ y ∧ y ≤ b) := by
  obtain ⟨a, ha0, ha1, ha⟩ := h.exists_diagonal_contact_interval hc
  obtain ⟨b, hb0, hb1, hb⟩ := h.exists_right_contact_interval hc
  exact ⟨a, b, ha0, ha1, hb0, hb1,
    (ha a).mpr ⟨ha0.le, le_rfl⟩, (hb b).mpr ⟨hb0.le, le_rfl⟩, ha, hb⟩

/-- Set-equality form of both exact physical contacts. -/
theorem Normalized.exists_exact_side_contact_sets (h : Normalized d)
    (hc : d.HasProtectedCenter) :
    ∃ a b : ℝ, 0 < a ∧ a < 1 / 2 ∧ 0 < b ∧ b < 1 ∧
      d.piece 0 ∩ {p : Plane | p 0 = p 1} =
        (fun t : ℝ => Schoenflies.Plane.mk t t) '' Icc 0 a ∧
      d.piece 0 ∩ {p : Plane | p 0 = 1} =
        (fun y : ℝ => Schoenflies.Plane.mk 1 y) '' Icc 0 b := by
  obtain ⟨a, b, ha0, ha1, hb0, hb1, _, _, ha, hb⟩ := h.exists_side_contact_parameters hc
  refine ⟨a, b, ha0, ha1, hb0, hb1, ?_, ?_⟩
  · apply Set.Subset.antisymm
    · rintro p ⟨hp, hdiag⟩
      have heq : Schoenflies.Plane.mk (p 0) (p 0) = p := by
        apply PlaneIsometries.plane_ext
        · rfl
        · exact hdiag
      exact ⟨p 0, (ha (p 0)).mp (heq.symm ▸ hp), heq⟩
    · rintro p ⟨t, ht, rfl⟩
      exact ⟨(ha t).mpr ht, rfl⟩
  · apply Set.Subset.antisymm
    · rintro p ⟨hp, hright⟩
      have heq : Schoenflies.Plane.mk 1 (p 1) = p := by
        apply PlaneIsometries.plane_ext
        · exact hright.symm
        · rfl
      exact ⟨p 1, (hb (p 1)).mp (heq.symm ▸ hp), heq⟩
    · rintro p ⟨y, hy, rfl⟩
      exact ⟨(hb y).mpr hy, rfl⟩

end Puzzling139335.N5
