import StackExchange.Puzzling139335.N4MiddleInvolutions.BoundaryBalance.ExteriorArcs
import StackExchange.Puzzling139335.N4MiddleInvolutions.BoundaryBalance.GapVariation
import StackExchange.Puzzling139335.N4MiddleInvolutions.BoundaryBalance.OuterVariation
import StackExchange.Puzzling139335.N4MiddleInvolutions.BoundaryBalance.SegmentBounds.PairArcSum
import StackExchange.Puzzling139335.N4OuterPair.Contacts

/-!
# An actual length obstruction for the middle interface

The exact boundary family is constructed from the dissection. Shared mixed
interfaces cancel at every positive resolution. The remaining actual exterior
arcs give a lower bound on every segment containing the middle interface,
without a rectifiability or boundary-measure assumption.
-/

open Set

namespace Puzzling139335.N4MiddleInvolutions.BoundaryBalance

/-- The middle interface cannot fit in a segment shorter than twice the sum
of the actual lower outer side-contact heights. -/
theorem two_contact_sum_le_segment_length {d : SquareDissection}
    (h : N4OuterPair.Configuration d) (hc : d.HasProtectedCenter)
    {l r : ℝ} (hl : l ∈ Ioc (0 : ℝ) (1 / 2)) (hr : r ∈ Ioc (0 : ℝ) (1 / 2))
    (hleft : ∀ y : ℝ,
      Schoenflies.Plane.mk 0 y ∈ d.piece 0 ↔ y ∈ Icc (0 : ℝ) l)
    (hright : ∀ y : ℝ,
      Schoenflies.Plane.mk 1 y ∈ d.piece 0 ↔ y ∈ Icc (0 : ℝ) r)
    {a b : Plane} (hcut : d.piece 2 ∩ d.piece 3 ⊆ segment ℝ a b) :
    2 * (l + r) ≤ dist a b := by
  obtain ⟨F, _, hparams⟩ := d.exists_exact_boundary_arc_family
  obtain ⟨k0, hp0, hA0⟩ := exists_lower_exterior_arc h hc hl hr hleft hright F
  obtain ⟨k1, hp1, hA1⟩ := exists_upper_exterior_arc h hc hl hr hleft hright F
  let K : ℝ := (F.n (Sum.inl 0) : ℝ) + (F.n (Sum.inl 1) : ℝ) +
    (F.n (Sum.inl 2) : ℝ) + (F.n (Sum.inl 3) : ℝ) + 6
  have hK : 0 < K := by dsimp [K]; positivity
  have hbound (ε : ℝ) (hε : 0 < ε) :
      4 * (l + r) ≤ 2 * dist a b + K * ε := by
    have hout := outer_pairArcSum_lower_of_occurrences F hl.1 hr.1 hε
      k0 k1 hp0 hp1 hA0 hA1
    have hgap := middle_exterior_pairArcSum_le h hc hl.2 hr.2 hleft hright F hε
    have hbalance := (abs_le.mp (pairArcSum_balance_abs_le F hparams hε)).1
    have hnonneg := pairArcSum_nonneg F hε (Sum.inl 0) (Sum.inl 1)
    have hcutBound := pairArcSum_le_dist_of_inter_subset_segment F hε
      (Sum.inl 2) (Sum.inl 3) hcut
    dsimp [K]
    nlinarith only [hout, hgap, hbalance, hnonneg, hcutBound]
  by_contra hnot
  have hdelta : 0 < 2 * (l + r) - dist a b := sub_pos.mpr (lt_of_not_ge hnot)
  let ε : ℝ := (2 * (l + r) - dist a b) / K
  have hε : 0 < ε := div_pos hdelta hK
  have hcancel : K * ε = 2 * (l + r) - dist a b := by
    dsimp [ε]
    rw [mul_div_cancel₀ _ (ne_of_gt hK)]
  have hsmall := hbound ε hε
  rw [hcancel] at hsmall
  linarith only [hsmall, hdelta]

/-- A complete left half-arm, together with the actual positive right contact,
forces the middle interface out of every segment of length at most one. -/
theorem middle_interface_not_subset_segment_of_full_left_arm {d : SquareDissection}
    (h : N4OuterPair.Configuration d) (hc : d.HasProtectedCenter)
    (harm : segment ℝ (Schoenflies.Plane.mk 0 0)
      (Schoenflies.Plane.mk 0 (1 / 2)) ⊆ d.piece 0)
    {a b : Plane} (hab : dist a b ≤ 1) :
    ¬ d.piece 2 ∩ d.piece 3 ⊆ segment ℝ a b := by
  intro hcut
  obtain ⟨r, hr, hright⟩ := h.positive_side_contact_interval hc
    (x := (1 : ℝ)) (Or.inr rfl)
  have hleft : ∀ y : ℝ,
      Schoenflies.Plane.mk 0 y ∈ d.piece 0 ↔ y ∈ Icc (0 : ℝ) (1 / 2) := by
    intro y
    constructor
    · intro hy
      exact (h.outer_halves.1 hy).2
    · intro hy
      apply harm
      rw [Schoenflies.mem_segment_vert,
        segment_eq_Icc (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      exact ⟨rfl, hy⟩
  have hbound := two_contact_sum_le_segment_length h hc
    (by norm_num : (1 / 2 : ℝ) ∈ Ioc (0 : ℝ) (1 / 2)) hr hleft hright hcut
  linarith only [hbound, hr.1, hab]

/-- The symmetric right-half-arm version needs no relabeling or change of
the actual middle pieces. -/
theorem middle_interface_not_subset_segment_of_full_right_arm {d : SquareDissection}
    (h : N4OuterPair.Configuration d) (hc : d.HasProtectedCenter)
    (harm : segment ℝ (Schoenflies.Plane.mk 1 0)
      (Schoenflies.Plane.mk 1 (1 / 2)) ⊆ d.piece 0)
    {a b : Plane} (hab : dist a b ≤ 1) :
    ¬ d.piece 2 ∩ d.piece 3 ⊆ segment ℝ a b := by
  intro hcut
  obtain ⟨l, hl, hleft⟩ := h.positive_side_contact_interval hc
    (x := (0 : ℝ)) (Or.inl rfl)
  have hright : ∀ y : ℝ,
      Schoenflies.Plane.mk 1 y ∈ d.piece 0 ↔ y ∈ Icc (0 : ℝ) (1 / 2) := by
    intro y
    constructor
    · intro hy
      exact (h.outer_halves.1 hy).2
    · intro hy
      apply harm
      rw [Schoenflies.mem_segment_vert,
        segment_eq_Icc (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      exact ⟨rfl, hy⟩
  have hbound := two_contact_sum_le_segment_length h hc hl
    (by norm_num : (1 / 2 : ℝ) ∈ Ioc (0 : ℝ) (1 / 2)) hleft hright hcut
  linarith only [hbound, hl.1, hab]

end Puzzling139335.N4MiddleInvolutions.BoundaryBalance
