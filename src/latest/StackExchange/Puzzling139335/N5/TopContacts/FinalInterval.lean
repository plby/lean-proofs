import StackExchange.Puzzling139335.N5.TopContacts.FinalInterval.Gap
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# The final interval of top contacts

The least top contact exists by compactness.  Coverage supplies a contact
of the other piece just before that least point; Jordan interlacing then
excludes every later gap before the top-right corner.
-/

open Set

namespace Puzzling139335.N5.TopContacts

/-- Actual top contacts of the corner piece form a nontrivial closed final
interval, strictly after the given lower bound. -/
theorem top_side_final_interval {R D : Set Plane} {b : ℝ}
    (hR : IsJordanRegion R) (hD : IsJordanRegion D)
    (hRS : R ⊆ unitSquare) (hDS : D ⊆ unitSquare)
    (hdis : Disjoint (interior R) (interior D))
    (hTR : Schoenflies.Plane.mk 1 1 ∈ R) (hb : b ∈ Ioo (0 : ℝ) 1)
    (hafter : ∀ x : ℝ, Schoenflies.Plane.mk x 1 ∈ R → b < x)
    (hbefore : ∃ x < 1, Schoenflies.Plane.mk x 1 ∈ R)
    (hcover : ∀ x ∈ Ioo b 1,
      Schoenflies.Plane.mk x 1 ∈ R ∨ Schoenflies.Plane.mk x 1 ∈ D) :
    ∃ m : ℝ, b < m ∧ m < 1 ∧
      ∀ x : ℝ, Schoenflies.Plane.mk x 1 ∈ R ↔ m ≤ x ∧ x ≤ 1 := by
  let T : Set ℝ := {x | Schoenflies.Plane.mk x 1 ∈ R}
  have hclosed : IsClosed T := hR.isClosed.preimage (by fun_prop)
  have hsub : T ⊆ Icc (0 : ℝ) 1 := fun x hx => (hRS hx).1
  have hcompact : IsCompact T := isCompact_Icc.of_isClosed_subset hclosed hsub
  obtain ⟨m, hm⟩ := hcompact.exists_isLeast ⟨1, hTR⟩
  have hmR : Schoenflies.Plane.mk m 1 ∈ R := hm.1
  have hbm : b < m := hafter m hmR
  obtain ⟨a, ha1, haR⟩ := hbefore
  have hm1 : m < 1 := lt_of_le_of_lt (hm.2 haR) ha1
  let y : ℝ := (b + m) / 2
  have hyb : b < y := by dsimp [y]; linarith
  have hym : y < m := by dsimp [y]; linarith
  have hy1 : y < 1 := hym.trans hm1
  have hyD : Schoenflies.Plane.mk y 1 ∈ D := by
    apply (hcover y ⟨hyb, hy1⟩).resolve_left
    intro hyR
    exact (not_le_of_gt hym) (hm.2 hyR)
  refine ⟨m, hbm, hm1, ?_⟩
  intro x
  constructor
  · intro hxR
    exact ⟨hm.2 hxR, (hRS hxR).1.2⟩
  · rintro ⟨hmx, hx1⟩
    rcases eq_or_lt_of_le hmx with hmx | hmx
    · exact hmx ▸ hmR
    rcases eq_or_lt_of_le hx1 with hx1 | hx1
    · exact hx1.symm ▸ hTR
    by_contra hxR
    have hxD : Schoenflies.Plane.mk x 1 ∈ D :=
      (hcover x ⟨hbm.trans hmx, hx1⟩).resolve_left hxR
    exact top_side_gap_impossible hR hD hRS hDS hdis hmR hTR hxD hyD
      (hb.1.le.trans hyb.le) hym hmx hx1

end Puzzling139335.N5.TopContacts
