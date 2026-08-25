import StackExchange.Puzzling139335.JordanTransport
import Wikipedia.SchoenfliesTheorem.Subarc
import Wikipedia.SchoenfliesTheorem.SimpleArc
import Mathlib.Topology.Order.Compact

/-!
# A symmetric Jordan curve in an arc and its involutive image

An arc joining two points exchanged by a fixed-point-free involution need
not be disjoint from its image.  Among all pairs of exchanged parameters,
choose one with least parameter separation.  The intervening subarc meets
its image only at its endpoints, so the two form a Jordan curve.
-/

open Set unitInterval

namespace Schoenflies.IsArcBetween

/-- An arc joining a point to its image under an involution contains a
subarc whose union with its image is an invariant Jordan curve, provided
the involution fixes no point on the original arc. -/
theorem exists_invariant_jordanCurve {A : Set Plane} {p : Plane}
    (e : Plane ≃ₜ Plane) (hinv : Function.Involutive e)
    (hA : IsArcBetween A p (e p))
    (hfree : ∀ x ∈ A, e x ≠ x) :
    ∃ C ⊆ A ∪ e '' A, IsJordanCurve C ∧ e '' C = C := by
  obtain ⟨f, hf, hfinj, hfA, hf0, hf1⟩ := hA
  let F : I → Plane := fun t => f t
  have hF : Continuous F := hf.domRestrict
  let K : Set (I × I) := {z | (z.1 : ℝ) ≤ z.2 ∧ F z.1 = e (F z.2)}
  have hKclosed : IsClosed K := by
    exact (isClosed_le (continuous_subtype_val.comp continuous_fst)
      (continuous_subtype_val.comp continuous_snd)).inter
      (isClosed_eq (hF.comp continuous_fst)
        (e.continuous.comp (hF.comp continuous_snd)))
  have hKnonempty : K.Nonempty := by
    refine ⟨(0, 1), ?_⟩
    change (0 : ℝ) ≤ 1 ∧ f 0 = e (f 1)
    exact ⟨zero_le_one, by rw [hf0, hf1, hinv]⟩
  let gap : I × I → ℝ := fun z => (z.2 : ℝ) - z.1
  have hgap : Continuous gap :=
    (continuous_subtype_val.comp continuous_snd).sub
      (continuous_subtype_val.comp continuous_fst)
  obtain ⟨z, hz, hmin⟩ := hKclosed.isCompact.exists_isMinOn hKnonempty hgap.continuousOn
  let a : ℝ := z.1
  let b : ℝ := z.2
  have ha : a ∈ I := z.1.property
  have hb : b ∈ I := z.2.property
  have hab : a ≤ b := hz.1
  have hpair : f a = e (f b) := hz.2
  have hepair : e (f a) = f b := by rw [hpair, hinv]
  have habne : a ≠ b := by
    intro heq
    have hfaA : f a ∈ A := hfA ▸ mem_image_of_mem f ha
    exact hfree (f a) hfaA (by simpa only [heq] using hepair)
  let B : Set Plane := f '' uIcc a b
  have hB : IsArcBetween B (f a) (f b) :=
    isArcBetween_subarc_of_injOn_I hf hfinj ha hb habne
  have hBA : B ⊆ A := by
    rw [← hfA]
    exact image_mono (uIcc_subset_I ha hb)
  have hEB : IsArcBetween (e '' B) (f b) (f a) := by
    simpa only [hepair, ← hpair] using hB.image_homeomorph e
  have hmeet : ∀ x ∈ B, x ∈ e '' B → x = f a ∨ x = f b := by
    rintro x ⟨s, hs, rfl⟩ ⟨y, ⟨t, ht, rfl⟩, hts⟩
    have hsI : s ∈ I := uIcc_subset_I ha hb hs
    have htI : t ∈ I := uIcc_subset_I ha hb ht
    have hsab : a ≤ s ∧ s ≤ b := by simpa only [uIcc_of_le hab, mem_Icc] using hs
    have htab : a ≤ t ∧ t ≤ b := by simpa only [uIcc_of_le hab, mem_Icc] using ht
    rcases le_total s t with hst | hts'
    · have hKst : (⟨s, hsI⟩, ⟨t, htI⟩) ∈ K := ⟨hst, hts.symm⟩
      have hbound : b - a ≤ t - s := hmin hKst
      have hsa : s = a := by linarith [hsab.1, htab.2]
      exact Or.inl (congrArg f hsa)
    · have hKts : (⟨t, htI⟩, ⟨s, hsI⟩) ∈ K := by
        refine ⟨hts', ?_⟩
        change f t = e (f s)
        rw [← hts, hinv]
      have hbound : b - a ≤ s - t := hmin hKts
      have hsb : s = b := by linarith [hsab.2, htab.1]
      exact Or.inr (congrArg f hsb)
  refine ⟨B ∪ e '' B, union_subset_union hBA (image_mono hBA),
    IsJordanCurve.of_two_arcs hB hEB hmeet, ?_⟩
  have hee : e '' (e '' B) = B := by
    rw [← image_comp]
    have hid : (e ∘ e : Plane → Plane) = id := funext hinv
    rw [hid, image_id]
  rw [image_union, hee, union_comm]

end Schoenflies.IsArcBetween
