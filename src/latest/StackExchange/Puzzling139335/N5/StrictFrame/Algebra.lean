import StackExchange.Puzzling139335.N5.CornerFrame.Angle

/-!
# Strict scalar bounds for the actual five-incidence corner frame

The quantities `c * h + s * k` and `c * k - s * h` are the two
coordinates of the source point in the corner frame.  The lemmas here
derive strict parameter bounds from the explicit support inequalities;
their geometric hypotheses are supplied by the actual source placements.
-/

namespace Puzzling139335.N5.StrictFrame

/-- A strict upper bound on the first frame coordinate excludes zero sine. -/
theorem sin_pos_of_strict_offset {c s h k : ℝ}
    (hcs : c ^ 2 + s ^ 2 = 1) (hc : 0 < c) (hs : 0 ≤ s)
    (hB : c * (1 - h) ≤ s * k) (hd : c * h + s * k < 1) :
    0 < s := by
  by_contra hspos
  have hs0 : s = 0 := le_antisymm (le_of_not_gt hspos) hs
  have hc1 : c = 1 := by nlinarith only [hcs, hc, hs0]
  rw [hs0, hc1] at hB hd
  norm_num at hB hd
  linarith

/-- Inverting the orthogonal frame recovers the first source coordinate. -/
theorem source_height_identity {c s h k : ℝ} (hcs : c ^ 2 + s ^ 2 = 1) :
    h = c * (c * h + s * k) - s * (c * k - s * h) := by
  calc
    h = (c ^ 2 + s ^ 2) * h := by rw [hcs, one_mul]
    _ = c * (c * h + s * k) - s * (c * k - s * h) := by ring

/-- Strictness of both relevant frame coordinates gives `h < c < 1`. -/
theorem height_lt_cos_of_strict_offsets {c s h k : ℝ}
    (hcs : c ^ 2 + s ^ 2 = 1) (hc : 0 < c) (hs : 0 < s)
    (hd : c * h + s * k < 1) (hz : 0 < c * k - s * h) :
    h < c ∧ c < 1 := by
  have hid := source_height_identity (h := h) (k := k) hcs
  have hcd := mul_lt_mul_of_pos_left hd hc
  have hsz := mul_pos hs hz
  constructor
  · linarith only [hid, hcd, hsz]
  · nlinarith only [hcs, sq_pos_of_pos hs]

/-- The two support inequalities rule out the diagonal equality case;
the same strict source ordering then rules out equal sine and cosine. -/
theorem strict_order_of_diagonal_bound {c s h k : ℝ}
    (hc : 0 < c) (_hs : 0 ≤ s) (hsc : s ≤ c) (hkh : k ≤ h)
    (hA : s * h ≤ c * k) (hB : c * (1 - h) ≤ s * k)
    (hdiag : h = k → h < 1 / 2) : k < h ∧ s < c := by
  have hkh' : k < h := by
    refine lt_of_le_of_ne hkh ?_
    intro hEq
    have hh := hdiag hEq.symm
    have hA' : s * h ≤ c * h := by simpa only [hEq] using hA
    have hB' : c * (1 - h) ≤ s * h := by simpa only [hEq] using hB
    have hpositive : 0 < c * (1 - 2 * h) :=
      mul_pos hc (by linarith only [hh])
    nlinarith only [hA', hB', hpositive]
  refine ⟨hkh', lt_of_le_of_ne hsc ?_⟩
  intro hEq
  have hhk : h ≤ k := by
    apply (mul_le_mul_iff_right₀ hc).mp
    simpa only [hEq] using hA
  exact (not_lt_of_ge hhk) hkh'

/-- A positive supported leg gives a strictly positive transverse offset. -/
theorem transverse_offset_pos_of_leg {c s h k a : ℝ}
    (ha : 0 < a) (hsc : s < c)
    (hleg : (c - s) * a ≤ c * k - s * h) :
    0 < c * k - s * h :=
  (mul_pos (sub_pos.mpr hsc) ha).trans_le hleg

/-- Strictly ordered positive frame parameters correspond to a strict
angle between zero and one eighth of a turn. -/
theorem exists_angle_of_strict_frame {c s : ℝ}
    (hcs : c ^ 2 + s ^ 2 = 1) (hs : 0 < s) (hsc : s < c) :
    ∃ θ : ℝ, θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 4) ∧
      Real.cos θ = c ∧ Real.sin θ = s := by
  obtain ⟨θ, hθ, hcos, hsin⟩ := exists_angle_of_ordered_frame hcs hs.le hsc.le
  have hθpos : 0 < θ := by
    by_contra hnot
    have hθ0 : θ = 0 := le_antisymm (le_of_not_gt hnot) hθ.1
    have hs0 : s = 0 := by simpa only [hθ0, Real.sin_zero] using hsin.symm
    exact hs.ne' hs0
  have hθlt : θ < Real.pi / 4 := by
    by_contra hnot
    have hθ4 : θ = Real.pi / 4 := le_antisymm hθ.2 (le_of_not_gt hnot)
    have heq : c = s := by
      rw [← hcos, ← hsin, hθ4, Real.cos_pi_div_four, Real.sin_pi_div_four]
    exact hsc.ne heq.symm
  exact ⟨θ, ⟨hθpos, hθlt⟩, hcos, hsin⟩

end Puzzling139335.N5.StrictFrame
