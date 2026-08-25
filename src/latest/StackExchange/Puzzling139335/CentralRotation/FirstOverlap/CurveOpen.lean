import StackExchange.Puzzling139335.CentralRotation.FirstOverlap.SubarcOpen
import StackExchange.Puzzling139335.JordanSubarc

/-!
# Endpoint exclusion for subarcs of a Jordan curve

An actual arc contained in a Jordan curve has a complementary closed arc.
The complement of that closed arc exhibits the relative openness of the first
arc without its endpoints.  Closure then promotes disjointness of arc interiors
to disjointness of a whole arc from the other arc's interior.
-/

open Set Schoenflies

namespace Puzzling139335.CentralRotation.FirstOverlap

/-- An arc with its endpoints removed is relatively open in every Jordan curve
that contains it. -/
theorem subarc_diff_isRelOpen_of_isJordanCurve
    {C Γ : Set Schoenflies.Plane} {p q : Schoenflies.Plane}
    (hC : IsJordanCurve C) (hΓ : IsArcBetween Γ p q) (hΓC : Γ ⊆ C) :
    ∃ V : Set Schoenflies.Plane, IsOpen V ∧ Γ \ {p, q} = V ∩ C := by
  obtain ⟨B, hcut⟩ := hC.exists_cutPair_of_subset_arc hΓ hΓC
  refine ⟨Bᶜ, hcut.snd.isArc.isClosed.isOpen_compl, ?_⟩
  ext x
  constructor
  · rintro ⟨hxΓ, hxends⟩
    refine ⟨?_, hΓC hxΓ⟩
    intro hxB
    apply hxends
    rw [← hcut.inter_eq]
    exact ⟨hxΓ, hxB⟩
  · rintro ⟨hxB, hxC⟩
    have hxΓ : x ∈ Γ := by
      rw [← hcut.union_eq] at hxC
      exact hxC.resolve_right hxB
    refine ⟨hxΓ, ?_⟩
    intro hxends
    rw [← hcut.inter_eq] at hxends
    exact hxB hxends.2

/-- For two actual subarcs of a Jordan curve, disjointness after removing both
pairs of endpoints already excludes the whole first arc from the interior of
the second. -/
theorem disjoint_of_disjoint_arc_interiors_of_isJordanCurve
    {C I Γ : Set Schoenflies.Plane} {u v p q : Schoenflies.Plane}
    (hC : IsJordanCurve C) (hI : IsArcBetween I u v)
    (hΓ : IsArcBetween Γ p q) (hIC : I ⊆ C) (hΓC : Γ ⊆ C)
    (hdisj : Disjoint (I \ {u, v}) (Γ \ {p, q})) :
    Disjoint I (Γ \ {p, q}) := by
  obtain ⟨V, hVopen, hV⟩ := subarc_diff_isRelOpen_of_isJordanCurve hC hΓ hΓC
  have hIV : Disjoint (I \ {u, v}) V := by
    refine disjoint_left.mpr ?_
    intro x hxI hxV
    apply disjoint_left.mp hdisj hxI
    rw [hV]
    exact ⟨hxV, hIC hxI.1⟩
  have hclosure := hIV.closure_left hVopen
  rw [arc_closure_diff_endpoints hI] at hclosure
  apply hclosure.mono_right
  rw [hV]
  exact inter_subset_left

/-- If the curve is covered by `Γ` and `M`, and `M` contains both endpoints of
`Γ`, any subarc with interior disjoint from the interior of `Γ` lies in `M`. -/
theorem subset_complement_of_disjoint_arc_interiors_of_isJordanCurve
    {C I Γ M : Set Schoenflies.Plane} {u v p q : Schoenflies.Plane}
    (hC : IsJordanCurve C) (hI : IsArcBetween I u v)
    (hΓ : IsArcBetween Γ p q) (hIC : I ⊆ C) (hΓC : Γ ⊆ C)
    (hcover : C = Γ ∪ M) (hp : p ∈ M) (hq : q ∈ M)
    (hdisj : Disjoint (I \ {u, v}) (Γ \ {p, q})) : I ⊆ M := by
  have hwhole := disjoint_of_disjoint_arc_interiors_of_isJordanCurve
    hC hI hΓ hIC hΓC hdisj
  intro x hxI
  have hxC := hIC hxI
  rw [hcover] at hxC
  rcases hxC with hxΓ | hxM
  · by_contra hxM
    apply disjoint_left.mp hwhole hxI
    refine ⟨hxΓ, ?_⟩
    rintro (rfl | rfl)
    · exact hxM hp
    · exact hxM hq
  · exact hxM

end Puzzling139335.CentralRotation.FirstOverlap
