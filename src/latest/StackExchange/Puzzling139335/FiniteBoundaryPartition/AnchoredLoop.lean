import Wikipedia.SchoenfliesTheorem.GeneralCrosscut

/-!
# A Jordan loop with two prescribed parameter values

Traverse the first arc of a cut pair during the first half of the parameter
interval and the second arc in reverse during the second half.  The common
endpoints occur at parameters `0` and `1/2`.
-/

open Set unitInterval Schoenflies

namespace Puzzling139335

/-- A cut pair has a loop parametrization starting at its first endpoint and
reaching its second endpoint at time `1/2`. -/
theorem cutPair_exists_anchored_loop {C A B : Set Plane} {p q : Plane}
    (hcut : IsCutPair C p q A B) :
    ∃ f : ℝ → Plane, IsLoop f ∧ f '' Icc 0 1 = C ∧ f 0 = p ∧ f (1 / 2) = q := by
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
  · change concatenate f g '' I = C
    rw [image_concatenate hmid, hfim, hgim, hcut.union_eq]
  · rw [concatenate_zero, hf0]
  · rw [concatenate_of_le le_rfl]
    norm_num [hf1]

/-- Two distinct points of a Jordan curve can be assigned parameters `0` and
`1/2` in a loop parametrization of the curve. -/
theorem jordanCurve_exists_anchored_loop {C : Set Plane} {p q : Plane}
    (hC : IsJordanCurve C) (hp : p ∈ C) (hq : q ∈ C) (hpq : p ≠ q) :
    ∃ f : ℝ → Plane, IsLoop f ∧ f '' Icc 0 1 = C ∧ f 0 = p ∧ f (1 / 2) = q := by
  obtain ⟨A, B, hcut⟩ := exists_isCutPair hC hp hq hpq
  exact cutPair_exists_anchored_loop hcut

end Puzzling139335
