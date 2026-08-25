import StackExchange.Puzzling139335.N8.Pairs.Local
import StackExchange.Puzzling139335.N7.RepeatedSide
import StackExchange.Puzzling139335.SymmetryOrbit.Classification
import StackExchange.Puzzling139335.QuarterTurnPair

/-!
# Shared corners of adjacent repeated side pairs

An actual repeated intrinsic pair gives a square symmetry between its
two placements. The quarter-turn obstruction leaves an involution. Such
an involution exchanges the two physical side endpoint sets and fixes
their singleton intersection, so the shared corner has the same intrinsic
type in the two pieces.
-/

open Set

namespace Puzzling139335.N7

private theorem common_side_index_unique :
    ∀ s t j a : Fin 4, s ≠ t →
      (j = s ∨ j = s + 1) → (j = t ∨ j = t + 1) →
      (a = s ∨ a = s + 1) → (a = t ∨ a = t + 1) → a = j := by
  decide

/-- Distinct sides sharing a square corner have no other common endpoint. -/
theorem common_side_endpoint_unique {s t j : Fin 4} (hst : s ≠ t)
    (hjs : j = s ∨ j = s + 1) (hjt : j = t ∨ j = t + 1) {p : Plane}
    (hps : p ∈ ({corner s, corner (s + 1)} : Set Plane))
    (hpt : p ∈ ({corner t, corner (t + 1)} : Set Plane)) : p = corner j := by
  rcases hps with hps | hps
  · have hst' : s = t ∨ s = t + 1 := by
      simpa only [hps, mem_insert_iff, mem_singleton_iff, corner_injective.eq_iff]
        using hpt
    exact hps.trans (congrArg corner
      (common_side_index_unique s t j s hst hjs hjt (Or.inl rfl) hst'))
  · have hps : p = corner (s + 1) := mem_singleton_iff.mp hps
    have hst' : s + 1 = t ∨ s + 1 = t + 1 := by
      simpa only [hps, mem_insert_iff, mem_singleton_iff, corner_injective.eq_iff]
        using hpt
    exact hps.trans (congrArg corner
      (common_side_index_unique s t j (s + 1) hst hjs hjt (Or.inr rfl) hst'))

/-- An involution exchanging two distinct side endpoint sets fixes their
shared corner. -/
theorem shared_corner_fixed_of_involutive (e : Plane → Plane)
    (hinv : Function.Involutive e) {s t j : Fin 4} (hst : s ≠ t)
    (hjs : j = s ∨ j = s + 1) (hjt : j = t ∨ j = t + 1)
    (hends : e '' {corner s, corner (s + 1)} = {corner t, corner (t + 1)}) :
    e (corner j) = corner j := by
  have hjs' : corner j ∈ ({corner s, corner (s + 1)} : Set Plane) := by
    rcases hjs with rfl | rfl <;> simp
  have hjt' : corner j ∈ ({corner t, corner (t + 1)} : Set Plane) := by
    rcases hjt with rfl | rfl <;> simp
  have hejt : e (corner j) ∈ ({corner t, corner (t + 1)} : Set Plane) := by
    rw [← hends]
    exact mem_image_of_mem e hjs'
  have hejs : e (corner j) ∈ ({corner s, corner (s + 1)} : Set Plane) := by
    rw [← hends] at hjt'
    obtain ⟨p, hp, hpj⟩ := hjt'
    rw [← hpj, hinv]
    exact hp
  exact common_side_endpoint_unique hst hjs hjt hejs hejt

/-- Distinct pieces carrying the same intrinsic pair cannot occupy the
same physical side. This does not require a protected center. -/
theorem local_sides_ne_of_intrinsicPair_eq (d : SquareDissection)
    {i k s t : Fin 4} (hik : i ≠ k)
    (hsi : N8.IsLocalSide d i s) (htk : N8.IsLocalSide d k t)
    (hpair : N8.intrinsicPair d i = N8.intrinsicPair d k) : s ≠ t := by
  rintro rfl
  exact no_side_stabilizing_pair d hik s (d.relativePlacement i k)
    (d.relativePlacement_image i k)
    (N8.local_relativePlacement_side_endpoints_of_pair_eq d hsi htk hpair)
    ((hsi s).mpr (Or.inl rfl)) ((hsi (s + 1)).mpr (Or.inr rfl))

/-- The actual relative placement of adjacent repeated pairs fixes their
shared physical corner in a protected-center dissection. -/
theorem relativePlacement_fixes_shared_corner_of_repeated_pair
    (d : SquareDissection) (hc : d.HasProtectedCenter)
    {i k s t j : Fin 4} (hik : i ≠ k)
    (hsi : N8.IsLocalSide d i s) (htk : N8.IsLocalSide d k t) (hst : s ≠ t)
    (hji : corner j ∈ d.piece i) (hjk : corner j ∈ d.piece k)
    (hpair : N8.intrinsicPair d i = N8.intrinsicPair d k) :
    d.relativePlacement i k (corner j) = corner j := by
  have hS := N8.local_relativePlacement_preserves_square_of_pair_eq d hsi htk hpair
  rcases SymmetryOrbit.square_symmetry_classification
      (d.relativePlacement i k) hS.subset with hquarter | hinv
  · exact (d.not_hasProtectedCenter_of_quarterTurn_pair hik (d.relativePlacement i k)
      hquarter hS.subset (d.relativePlacement_image i k) hc).elim
  · exact shared_corner_fixed_of_involutive (d.relativePlacement i k) hinv
      hst ((hsi j).mp hji) ((htk j).mp hjk)
      (N8.local_relativePlacement_side_endpoints_of_pair_eq d hsi htk hpair)

/-- Adjacent occurrences of one repeated intrinsic side pair agree on the
intrinsic type at their shared physical corner. -/
theorem intrinsicCorner_eq_of_adjacent_repeated_pair
    (d : SquareDissection) (hc : d.HasProtectedCenter)
    {i k s t j : Fin 4} (hik : i ≠ k)
    (hsi : N8.IsLocalSide d i s) (htk : N8.IsLocalSide d k t) (hst : s ≠ t)
    (hji : corner j ∈ d.piece i) (hjk : corner j ∈ d.piece k)
    (hpair : N8.intrinsicPair d i = N8.intrinsicPair d k) :
    d.intrinsicCorner i j = d.intrinsicCorner k j := by
  apply (d.placement k).injective
  change d.relativePlacement i k (corner j) = d.placement k (d.intrinsicCorner k j)
  rw [d.placement_intrinsicCorner]
  exact relativePlacement_fixes_shared_corner_of_repeated_pair d hc hik hsi htk
    hst hji hjk hpair

end Puzzling139335.N7
