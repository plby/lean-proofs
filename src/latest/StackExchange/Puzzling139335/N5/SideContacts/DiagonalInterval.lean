import StackExchange.Puzzling139335.Definitions
import Mathlib

/-!
# A compact connected initial interval on the diagonal

This is a generic set theorem. Compactness supplies a largest first
coordinate, and preconnectedness supplies every intermediate coordinate.
The diagonal condition turns each coordinate witness into the required
actual point of the set. Avoidance of the center bounds the endpoint.
-/

open Set

namespace Puzzling139335.N5

theorem exists_diagonal_interval_of_compact_preconnected {S : Set Plane}
    (hcompact : IsCompact S) (hconn : IsPreconnected S) (hsub : S ⊆ unitSquare)
    (hdiag : ∀ p ∈ S, p 0 = p 1) (hzero : Schoenflies.Plane.mk 0 0 ∈ S)
    (hpositive : ∃ p ∈ S, 0 < p 0) (hcenter : squareCenter ∉ S) :
    ∃ a : ℝ, 0 < a ∧ a < 1 / 2 ∧
      ∀ t : ℝ, Schoenflies.Plane.mk t t ∈ S ↔ 0 ≤ t ∧ t ≤ a := by
  have hcoord : Continuous (fun p : Plane => p 0) :=
    PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0
  obtain ⟨q, hq, hmax⟩ := hcompact.exists_isMaxOn ⟨_, hzero⟩ hcoord.continuousOn
  have hmax' : ∀ p ∈ S, p 0 ≤ q 0 := hmax
  have hfill (t : ℝ) (ht0 : 0 ≤ t) (htq : t ≤ q 0) :
      Schoenflies.Plane.mk t t ∈ S := by
    have himage : t ∈ (fun p : Plane => p 0) '' S :=
      hconn.intermediate_value hzero hq hcoord.continuousOn ⟨ht0, htq⟩
    obtain ⟨p, hp, hpt⟩ := himage
    have hpeq : p = Schoenflies.Plane.mk t t := by
      ext i
      fin_cases i
      · change p 0 = t
        exact hpt
      · change p 1 = t
        exact (hdiag p hp).symm.trans hpt
    exact hpeq ▸ hp
  have hqpos : 0 < q 0 := by
    obtain ⟨p, hp, hp0⟩ := hpositive
    exact hp0.trans_le (hmax' p hp)
  have hqlt : q 0 < 1 / 2 := by
    by_contra hnot
    exact hcenter (hfill (1 / 2) (by norm_num) (le_of_not_gt hnot))
  refine ⟨q 0, hqpos, hqlt, ?_⟩
  intro t
  constructor
  · intro ht
    exact ⟨(hsub ht).1.1, hmax' _ ht⟩
  · rintro ⟨ht0, htq⟩
    exact hfill t ht0 htq

/-- Set equality form of the same diagonal-interval conclusion. -/
theorem exists_diagonal_interval_eq_of_compact_preconnected {S : Set Plane}
    (hcompact : IsCompact S) (hconn : IsPreconnected S) (hsub : S ⊆ unitSquare)
    (hdiag : ∀ p ∈ S, p 0 = p 1) (hzero : Schoenflies.Plane.mk 0 0 ∈ S)
    (hpositive : ∃ p ∈ S, 0 < p 0) (hcenter : squareCenter ∉ S) :
    ∃ a : ℝ, 0 < a ∧ a < 1 / 2 ∧
      S = (fun t : ℝ => Schoenflies.Plane.mk t t) '' Icc 0 a := by
  obtain ⟨a, ha0, ha1, hmem⟩ := exists_diagonal_interval_of_compact_preconnected
    hcompact hconn hsub hdiag hzero hpositive hcenter
  refine ⟨a, ha0, ha1, Set.Subset.antisymm ?_ ?_⟩
  · intro p hp
    have hpeq : Schoenflies.Plane.mk (p 0) (p 0) = p := by
      ext i
      fin_cases i
      · rfl
      · exact hdiag p hp
    refine ⟨p 0, ?_, hpeq⟩
    apply (hmem (p 0)).mp
    exact hpeq.symm ▸ hp
  · rintro p ⟨t, ht, rfl⟩
    exact (hmem t).mpr ht

end Puzzling139335.N5
