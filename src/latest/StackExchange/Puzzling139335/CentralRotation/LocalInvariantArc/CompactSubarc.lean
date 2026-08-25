import Wikipedia.SchoenfliesTheorem.MatchedArc
import Mathlib.Topology.Order.Compact

/-!
# Compact connected subsets of an arc

A compact connected subset of an injective interval image pulls back to a closed
parameter interval.  If that subset contains a relative neighborhood of a point
which is not an endpoint of the ambient arc, its parameter interval has the
chosen point strictly between its endpoints.
-/

open Set unitInterval
open scoped Topology

namespace Schoenflies

/-- A compact connected subset of a simple interval image is exactly the image
of a closed parameter interval.  A singleton subset is allowed here. -/
theorem compact_connected_subset_arc_parameters {f : ℝ → Plane}
    (hf : ContinuousOn f I) (hi : InjOn f I)
    {E : Set Plane} (hE : IsCompact E) (hc : IsConnected E)
    (hsub : E ⊆ f '' I) :
    ∃ a b : ℝ, a ∈ I ∧ b ∈ I ∧ a ≤ b ∧
      I ∩ f ⁻¹' E = Icc a b ∧ f '' Icc a b = E := by
  let g : Plane → ℝ := Function.invFunOn f I
  have hg : ContinuousOn g (f '' I) :=
    continuousOn_invFunOn_image' isCompact_I hf hi
  have hparameters : g '' E = I ∩ f ⁻¹' E := by
    ext t
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨s, hs, rfl⟩ := hsub hx
      simpa only [g, hi.leftInvOn_invFunOn hs, mem_inter_iff, mem_preimage] using
        (show s ∈ I ∧ f s ∈ E from ⟨hs, hx⟩)
    · rintro ⟨ht, hft⟩
      exact ⟨f t, hft, hi.leftInvOn_invFunOn ht⟩
  have hK : IsCompact (I ∩ f ⁻¹' E) := by
    rw [← hparameters]
    exact hE.image_of_continuousOn (hg.mono hsub)
  have hC : IsConnected (I ∩ f ⁻¹' E) := by
    rw [← hparameters]
    exact hc.image g (hg.mono hsub)
  let a : ℝ := sInf (I ∩ f ⁻¹' E)
  let b : ℝ := sSup (I ∩ f ⁻¹' E)
  have ha : a ∈ I ∩ f ⁻¹' E := hK.sInf_mem hC.nonempty
  have hb : b ∈ I ∩ f ⁻¹' E := hK.sSup_mem hC.nonempty
  have hinterval : I ∩ f ⁻¹' E = Icc a b := eq_Icc_of_connected_compact hC hK
  have hab : a ≤ b := (hinterval ▸ ha).2
  refine ⟨a, b, ha.1, hb.1, hab, hinterval, ?_⟩
  rw [← hinterval]
  apply Set.Subset.antisymm
  · rintro _ ⟨t, ht, rfl⟩
    exact ht.2
  · intro x hx
    obtain ⟨t, ht, rfl⟩ := hsub hx
    exact ⟨t, ⟨ht, hx⟩, rfl⟩

/-- A compact connected subset containing a relative neighborhood of an interior
point of an arc is itself a nondegenerate arc, and the chosen point is not one
of its endpoints. -/
theorem IsArcBetween.exists_isArcBetween_compact_connected_neighborhood
    {A E : Set Plane} {p q z : Plane} (hA : IsArcBetween A p q)
    (hE : IsCompact E) (hc : IsConnected E) (hsub : E ⊆ A)
    (hz : z ∈ A \ {p, q})
    (hnbhd : ∃ r > 0, Metric.ball z r ∩ A ⊆ E) :
    ∃ a b : Plane, IsArcBetween E a b ∧ z ∈ E \ {a, b} := by
  obtain ⟨f, hf, hi, hfA, hfp, hfq⟩ := hA
  have hsub' : E ⊆ f '' I := by simpa only [hfA] using hsub
  obtain ⟨a, b, ha, hb, hab, hinterval, himage⟩ :=
    compact_connected_subset_arc_parameters hf hi hE hc hsub'
  obtain ⟨t, ht, hft⟩ := (show z ∈ f '' I by simpa only [hfA] using hz.1)
  have hzero : t ≠ 0 := by
    intro ht0
    apply hz.2
    exact Or.inl (hft.symm.trans (ht0 ▸ hfp))
  have hone : t ≠ 1 := by
    intro ht1
    apply hz.2
    exact Or.inr (hft.symm.trans (ht1 ▸ hfq))
  have htInterior : 0 < t ∧ t < 1 :=
    ⟨lt_of_le_of_ne ht.1 hzero.symm, lt_of_le_of_ne ht.2 hone⟩
  have hI : I ∈ 𝓝 t := Icc_mem_nhds htInterior.1 htInterior.2
  obtain ⟨r, hr, hball⟩ := hnbhd
  have hpreimage : f ⁻¹' Metric.ball z r ∈ 𝓝 t := by
    apply ((hf t ht).continuousAt hI).preimage_mem_nhds
    rw [hft]
    exact Metric.ball_mem_nhds z hr
  have hEparams : I ∩ f ⁻¹' E ∈ 𝓝 t := by
    apply Filter.mem_of_superset (Filter.inter_mem hI hpreimage)
    intro s hs
    exact ⟨hs.1, hball ⟨hs.2, hfA ▸ mem_image_of_mem f hs.1⟩⟩
  rw [hinterval] at hEparams
  have hstrict : a < t ∧ t < b := Icc_mem_nhds_iff.mp hEparams
  have hab_ne : a ≠ b := (hstrict.1.trans hstrict.2).ne
  have hEarc : IsArcBetween E (f a) (f b) := by
    simpa only [uIcc_of_le hab, himage] using
      isArcBetween_subarc_of_injOn_I hf hi ha hb hab_ne
  refine ⟨f a, f b, hEarc, hball ⟨Metric.mem_ball_self hr, hz.1⟩, ?_⟩
  simp only [mem_insert_iff, mem_singleton_iff, not_or]
  constructor
  · intro heq
    exact hstrict.1.ne' (hi ht ha (hft.trans heq))
  · intro heq
    exact hstrict.2.ne (hi ht hb (hft.trans heq))

end Schoenflies
