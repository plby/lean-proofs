import StackExchange.Puzzling139335.StraightBranchCount.Defs
import StackExchange.Puzzling139335.JordanArcGerms
import StackExchange.Puzzling139335.JordanSubarc

/-!
# The intrinsic number of straight Jordan-boundary branches

Local branch matching makes the count independent of the chosen cut.  Two
incident arcs that meet only at their endpoints give the same count, even
when they are only short parts of the two boundary branches.
-/

open Set

namespace Puzzling139335

namespace HasStraightBranchCount

/-- The straight-branch count is independent of the chosen second cut point
and of the naming of the two branches. -/
theorem unique {C : Set Plane} {v : Plane} {m n : ℕ}
    (hm : HasStraightBranchCount C v m) (hn : HasStraightBranchCount C v n) : m = n := by
  obtain ⟨p, A, B, hcut, rfl⟩ := hm
  obtain ⟨q, D, E, hcut', rfl⟩ := hn
  rcases hcut.sameBoundaryGerm_pair hcut' with ⟨hAD, hBE⟩ | ⟨hAE, hBD⟩
  · rw [hAD.straightGermIndicator_eq, hBE.straightGermIndicator_eq]
  · rw [hAE.straightGermIndicator_eq, hBD.straightGermIndicator_eq, Nat.add_comm]

end HasStraightBranchCount

/-- Any two different incident endpoint branches display the intrinsic
straight-branch count.  They need not cover the whole Jordan curve. -/
theorem hasStraightBranchCount_of_two_endpoint_arcs
    {C A B : Set Plane} {v a b : Plane}
    (hC : Schoenflies.IsJordanCurve C)
    (hA : Schoenflies.IsArcBetween A v a) (hB : Schoenflies.IsArcBetween B v b)
    (hAC : A ⊆ C) (hBC : B ⊆ C)
    (hinter : A ∩ B ⊆ ({v, a} : Set Plane)) :
    HasStraightBranchCount C v (straightGermIndicator A v + straightGermIndicator B v) := by
  obtain ⟨D, hcut⟩ := hC.exists_cutPair_of_subset_arc hA hAC
  have hBD : SameBoundaryGerm B D v := by
    rcases hcut.endpoint_arc_germ_eq_or hB hBC with hBA | hBD
    · exact False.elim (hA.not_sameBoundaryGerm_of_inter_subset_endpoints hinter hBA.symm)
    · exact hBD
  exact ⟨a, A, D, hcut, by rw [hBD.straightGermIndicator_eq]⟩

theorem HasStraightBranchCount.eq_two_endpoint_arcs
    {C A B : Set Plane} {v a b : Plane} {n : ℕ}
    (h : HasStraightBranchCount C v n) (hC : Schoenflies.IsJordanCurve C)
    (hA : Schoenflies.IsArcBetween A v a) (hB : Schoenflies.IsArcBetween B v b)
    (hAC : A ⊆ C) (hBC : B ⊆ C)
    (hinter : A ∩ B ⊆ ({v, a} : Set Plane)) :
    n = straightGermIndicator A v + straightGermIndicator B v :=
  h.unique (hasStraightBranchCount_of_two_endpoint_arcs hC hA hB hAC hBC hinter)

/-- In the two-straight-branch case, every endpoint arc following that
Jordan boundary starts with a genuine straight segment. -/
theorem HasStraightBranchCount.two_implies_endpoint_arc_straight
    {C A : Set Plane} {v a : Plane} (h : HasStraightBranchCount C v 2)
    (hA : Schoenflies.IsArcBetween A v a) (hAC : A ⊆ C) : IsStraightAt A v := by
  obtain ⟨q, D, E, hcut, hn⟩ := h
  have hD : straightGermIndicator D v = 1 := by
    have hDle := straightGermIndicator_le_one D v
    have hEle := straightGermIndicator_le_one E v
    omega
  have hE : straightGermIndicator E v = 1 := by
    have hDle := straightGermIndicator_le_one D v
    have hEle := straightGermIndicator_le_one E v
    omega
  rcases hcut.endpoint_arc_germ_eq_or hA hAC with hAD | hAE
  · exact ((straightGermIndicator_eq_one_iff D v).mp hD).of_sameBoundaryGerm hAD.symm
  · exact ((straightGermIndicator_eq_one_iff E v).mp hE).of_sameBoundaryGerm hAE.symm

end Puzzling139335
