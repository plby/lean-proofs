import Wikipedia.SchoenfliesTheorem.Concatenate
import Wikipedia.SchoenfliesTheorem.GeneralCrosscut

/-!
# A loop parametrization adapted to a Jordan cut pair

Traverse the first arc from `p` to `q`, then the second in the reverse direction.
The two arcs occupy the closed lower and upper parameter halves.  This uses only
continuous injective arc parametrizations, with no length assumption.
-/

open Set unitInterval

namespace Schoenflies

/-- The lower half of a concatenation covers precisely the first arc. -/
theorem image_concatenate_lowerHalf (f g : ℝ → Plane) :
    concatenate f g '' lowerHalf = f '' I := by
  apply Subset.antisymm
  · rintro _ ⟨t, ht, rfl⟩
    exact ⟨2 * t, double_mem_I ht, (concatenate_of_le ht.2).symm⟩
  · rintro _ ⟨t, ht, rfl⟩
    refine ⟨t / 2, ⟨by linarith [ht.1], by linarith [ht.2]⟩, ?_⟩
    rw [concatenate_of_le (by linarith [ht.2])]
    congr 1
    ring

/-- When the joining endpoints agree, the closed upper half covers precisely
the second arc, including its starting point at the seam. -/
theorem image_concatenate_upperHalf {f g : ℝ → Plane} (hmid : f 1 = g 0) :
    concatenate f g '' upperHalf = g '' I := by
  apply Subset.antisymm
  · rintro _ ⟨t, ht, rfl⟩
    exact ⟨2 * t - 1, doubleBack_mem_I ht, (concatenate_upperHalf hmid ht).symm⟩
  · rintro _ ⟨t, ht, rfl⟩
    refine ⟨(t + 1) / 2, ⟨by linarith [ht.1], by linarith [ht.2]⟩, ?_⟩
    rw [concatenate_upperHalf hmid ⟨by linarith [ht.1], by linarith [ht.2]⟩]
    congr 1
    ring

/-- A named Jordan cut pair admits one loop parametrization that places its
first and second arcs on the two closed parameter halves. -/
theorem IsCutPair.exists_loop_parametrization {C A B : Set Plane} {p q : Plane}
    (hcut : IsCutPair C p q A B) :
    ∃ f : ℝ → Plane, IsLoop f ∧ f '' I = C ∧
      f '' Icc 0 (1 / 2 : ℝ) = A ∧ f '' Icc (1 / 2 : ℝ) 1 = B := by
  obtain ⟨f, hfc, hfi, hfim, hf0, hf1⟩ := hcut.fst
  obtain ⟨g, hgc, hgi, hgim, hg0, hg1⟩ := hcut.snd.reverse
  have hmid : f 1 = g 0 := hf1.trans hg0.symm
  have hloop : IsLoop (concatenate f g) := by
    refine IsLoop.concatenate hfc hfi hgc hgi hmid (hg1.trans hf0.symm) ?_
    intro z hz hz'
    have hzAB : z ∈ A ∩ B := ⟨hfim ▸ hz, hgim ▸ hz'⟩
    rw [hcut.inter_eq] at hzAB
    simpa only [mem_insert_iff, mem_singleton_iff, hf0, hf1] using hzAB
  refine ⟨concatenate f g, hloop, ?_, ?_, ?_⟩
  · rw [image_concatenate hmid, hfim, hgim, hcut.union_eq]
  · exact (image_concatenate_lowerHalf f g).trans hfim
  · exact (image_concatenate_upperHalf hmid).trans hgim

end Schoenflies
