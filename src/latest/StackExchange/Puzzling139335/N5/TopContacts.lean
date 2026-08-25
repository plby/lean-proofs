import StackExchange.Puzzling139335.N5.TopContacts.Bounds
import StackExchange.Puzzling139335.N5.TopContacts.FinalInterval
import StackExchange.Puzzling139335.N5.TopContacts.MiddleInterval

/-!
# Exact top contacts from the actual surviving placement

The support calculation gives a strict gap before the singleton piece.
The actual Jordan interlacing argument fills its final top interval, and
coverage and supporting-side uniqueness give the fourth piece's middle
interval.
-/

open Set

namespace Puzzling139335.N5

/-- The actual surviving frame determines exact terminal and middle top
intervals.  No top contact or supporting-face completeness is assumed. -/
theorem Normalized.exists_top_contact_partition_of_swapped_form
    {d : SquareDissection} (h : Normalized d)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' d.piece 0 = d.piece 2)
    {C : Plane} {c s b : ℝ}
    (hunit : c ^ 2 + s ^ 2 = 1)
    (hc : 0 < c) (hs : 0 < s) (hc₁ : c < 1)
    (hb₀ : 0 < b) (hb₁ : b < 1) (hk : C 1 < c)
    (hform : ∀ p, e p =
      !₂[1 + s * C 0 - c * C 1 - s * p 0 + c * p 1,
         1 - c * C 0 - s * C 1 + c * p 0 + s * p 1])
    (hright : ∀ y : ℝ,
      Schoenflies.Plane.mk 1 y ∈ d.piece 0 ↔ 0 ≤ y ∧ y ≤ b) :
    ∃ m : ℝ, b < m ∧ m < 1 ∧
      (∀ x : ℝ, Schoenflies.Plane.mk x 1 ∈ d.piece 2 ↔ m ≤ x ∧ x ≤ 1) ∧
      (∀ x : ℝ, Schoenflies.Plane.mk x 1 ∈ d.piece 3 ↔ b ≤ x ∧ x ≤ m) := by
  have hE : Schoenflies.Plane.mk 1 b ∈ d.piece 0 :=
    (hright b).mpr ⟨hb₀.le, le_rfl⟩
  have hOne := h.top_contact_one_iff_of_right_interval hright
  have hafter : ∀ x : ℝ, Schoenflies.Plane.mk x 1 ∈ d.piece 2 → b < x := by
    intro x hx
    exact h.singleton_top_contact_gt_base_height e he hunit hc hs hc₁ hb₀ hk hform hE hx
  have hTR : Schoenflies.Plane.mk 1 1 ∈ d.piece 2 := by
    simpa [corner, Fin.ext_iff, Schoenflies.Plane.mk] using h.top_right
  have hcover : ∀ x ∈ Ioo b 1,
      Schoenflies.Plane.mk x 1 ∈ d.piece 2 ∨
        Schoenflies.Plane.mk x 1 ∈ d.piece 3 := by
    intro x hx
    have hXS : Schoenflies.Plane.mk x 1 ∈ unitSquare :=
      ⟨⟨(hb₀.trans hx.1).le, hx.2.le⟩, by norm_num⟩
    obtain ⟨i, hi⟩ := d.exists_piece_mem hXS
    fin_cases i
    · exact (h.top_side_not_mem_zero x hi).elim
    · exact (not_le_of_gt hx.1 ((hOne x).mp hi).2).elim
    · exact Or.inl hi
    · exact Or.inr hi
  obtain ⟨m, hbm, hm₁, hTwo⟩ := TopContacts.top_side_final_interval
    (d.jordan 2) (d.jordan 3) (d.piece_subset 2) (d.piece_subset 3)
    (d.disjoint_interiors (by decide : (2 : Fin 4) ≠ 3)) hTR ⟨hb₀, hb₁⟩
    hafter h.exists_singleton_top_contact_lt_one hcover
  exact ⟨m, hbm, hm₁, hTwo,
    h.top_side_mem_three_iff_of_neighbor_intervals hb₀ hbm hm₁ hOne hTwo⟩

end Puzzling139335.N5
