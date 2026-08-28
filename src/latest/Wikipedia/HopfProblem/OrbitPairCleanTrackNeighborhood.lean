import Wikipedia.HopfProblem.OrbitPairNativeFamilyTrack
import Wikipedia.HopfProblem.OrbitPairFamilyDoublePoints
import Mathlib.Order.Interval.Set.Infinite

/-!
# Excluding all other branches near an embedded track point

A finite collision locus leaves an injective slice in every nonempty time
interval. At a point of such a slice, compactness of the spatial source
allows a target neighborhood whose entire track preimage lies in any
prescribed source neighborhood. The compactness argument uses a bounded
time band; no properness of the full noncompact track is assumed.
-/

noncomputable section

open Set Function

namespace Wikipedia.HopfProblem.OrbitPair.NativeFamily

variable {M N : Type*}

theorem exists_injective_slice_of_finite_doublePoints (F : ℝ × M → N)
    (hfinite : (FamilyDoublePoints.doublePoints F).Finite)
    {a b : ℝ} (hab : a < b) :
    ∃ t ∈ Ioo a b, Injective (fun x => F (t, x)) := by
  obtain ⟨t, ht, hnot⟩ := ((Ioo_infinite hab).sdiff (hfinite.image Prod.fst)).nonempty
  refine ⟨t, ht, ?_⟩
  intro x y hxy
  by_contra hne
  exact hnot ⟨(t, (x, y)), ⟨hne, hxy⟩, rfl⟩

variable [TopologicalSpace M] [CompactSpace M]
  [TopologicalSpace N] [T2Space N]

theorem exists_open_clean_track_neighborhood {F : ℝ × M → N}
    (hF : Continuous F) (q : ℝ × M)
    (hi : Injective (fun x => F (q.1, x)))
    {V : Set (ℝ × M)} (hV : IsOpen V) (hqV : q ∈ V)
    {a b : ℝ} (ha : a < q.1) (hb : q.1 < b) :
    ∃ O : Set (ℝ × N), IsOpen O ∧ track F q ∈ O ∧
      O ⊆ Ioo a b ×ˢ univ ∧ track F ⁻¹' O ⊆ V := by
  let K : Set (ℝ × M) := (Icc a b ×ˢ univ) \ V
  have hK : IsCompact K := (isCompact_Icc.prod isCompact_univ).diff hV
  have htrack : Continuous (track F) := continuous_fst.prodMk hF
  have hclosed : IsClosed (track F '' K) := (hK.image htrack).isClosed
  have hnot : track F q ∉ track F '' K := by
    rintro ⟨p, hp, heq⟩
    have hp1 : p.1 = q.1 := congrArg (fun y : ℝ × N => y.1) heq
    have hp2 : F (q.1, p.2) = F (q.1, q.2) := by
      have hh : F p = F q := congrArg Prod.snd heq
      change F (p.1, p.2) = F (q.1, q.2) at hh
      rwa [hp1] at hh
    have hpq : p = q := Prod.ext hp1 (hi hp2)
    exact hp.2 (hpq.symm ▸ hqV)
  let O : Set (ℝ × N) := (Ioo a b ×ˢ univ) ∩ (track F '' K)ᶜ
  refine ⟨O, (isOpen_Ioo.prod isOpen_univ).inter hclosed.isOpen_compl,
    ⟨⟨⟨ha, hb⟩, mem_univ _⟩, hnot⟩, inter_subset_left, ?_⟩
  intro p hp
  by_contra hpV
  have hpK : p ∈ K := ⟨⟨⟨hp.1.1.1.le, hp.1.1.2.le⟩, mem_univ _⟩, hpV⟩
  exact hp.2 ⟨p, hpK, rfl⟩

end Wikipedia.HopfProblem.OrbitPair.NativeFamily
