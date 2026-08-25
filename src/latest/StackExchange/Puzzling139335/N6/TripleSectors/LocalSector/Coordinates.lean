import StackExchange.Puzzling139335.SegmentCrossing.Overlap

/-!
# Coordinates for a sector between two first-quadrant segments

Nonzero segments from the origin in the closed first quadrant cannot have
zero determinant if their intersection consists only of the origin.  The
determinant functionals then give the two sides of the resulting sector.
-/

open Set

namespace Puzzling139335.N6.TripleSectors.LocalSector

noncomputable section

/-- Signed planar determinant, shared with the segment-crossing API. -/
abbrev det := SegmentCrossing.det

/-- The functional positive to the left of the directed line through `a`. -/
abbrev leftForm (a : Plane) : Plane →L[ℝ] ℝ := SegmentCrossing.detForm a

/-- The functional positive to the right of the directed line through `b`. -/
def rightForm (b : Plane) : Plane →L[ℝ] ℝ := -SegmentCrossing.detForm b

/-- The sum of the two Euclidean coordinates. -/
def coordSum : Plane →L[ℝ] ℝ := EuclideanSpace.proj 0 + EuclideanSpace.proj 1

@[simp] theorem leftForm_apply (a x : Plane) : leftForm a x = det a x := rfl

@[simp] theorem rightForm_apply (b x : Plane) : rightForm b x = det x b := by
  change -det b x = det x b
  exact (SegmentCrossing.det_swap b x).symm

@[simp] theorem coordSum_apply (x : Plane) : coordSum x = x 0 + x 1 := rfl

theorem coordSum_pos {a : Plane} (ha : a ≠ 0)
    (ha0 : 0 ≤ a 0) (ha1 : 0 ≤ a 1) : 0 < coordSum a := by
  rw [coordSum_apply]
  by_contra h
  have h0 : a 0 = 0 := by linarith
  have h1 : a 1 = 0 := by linarith
  apply ha
  ext i
  fin_cases i <;> simp_all

theorem smul_mem_segment_zero (a : Plane) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    t • a ∈ segment ℝ 0 a := by
  rw [segment_eq_image]
  exact ⟨t, ht, by simp⟩

/-- Collinear first-quadrant vectors have proportional coordinate sums. -/
theorem sum_smul_eq_of_det_eq_zero {a b : Plane} (h : det a b = 0) :
    coordSum b • a = coordSum a • b := by
  change a 0 * b 1 - a 1 * b 0 = 0 at h
  ext i
  fin_cases i
  · change (b 0 + b 1) * a 0 = (a 0 + a 1) * b 0
    nlinarith only [h]
  · change (b 0 + b 1) * a 1 = (a 0 + a 1) * b 1
    nlinarith only [h]

/-- Two nonzero first-quadrant segments meeting only at the origin are
linearly independent. -/
theorem det_ne_zero_of_segments_inter_singleton {a b : Plane}
    (ha : a ≠ 0) (hb : b ≠ 0)
    (ha0 : 0 ≤ a 0) (ha1 : 0 ≤ a 1)
    (hb0 : 0 ≤ b 0) (hb1 : 0 ≤ b 1)
    (hinter : segment ℝ 0 a ∩ segment ℝ 0 b = {0}) : det a b ≠ 0 := by
  intro hdet
  have hA := coordSum_pos ha ha0 ha1
  have hB := coordSum_pos hb hb0 hb1
  have hsum : 0 < coordSum a + coordSum b := add_pos hA hB
  have hab := sum_smul_eq_of_det_eq_zero hdet
  have hcommon :
      (coordSum b / (coordSum a + coordSum b)) • a =
        (coordSum a / (coordSum a + coordSum b)) • b := by
    have h := congrArg (fun x : Plane => (coordSum a + coordSum b)⁻¹ • x) hab
    simpa only [smul_smul, ← div_eq_inv_mul] using h
  have hleft : (coordSum b / (coordSum a + coordSum b)) • a ∈ segment ℝ 0 a :=
    smul_mem_segment_zero a
      ⟨(div_pos hB hsum).le, (div_le_one hsum).mpr (by linarith)⟩
  have hright : (coordSum b / (coordSum a + coordSum b)) • a ∈ segment ℝ 0 b := by
    rw [hcommon]
    exact smul_mem_segment_zero b
      ⟨(div_pos hA hsum).le, (div_le_one hsum).mpr (by linarith)⟩
  have hz : (coordSum b / (coordSum a + coordSum b)) • a = 0 := by
    have hmem : (coordSum b / (coordSum a + coordSum b)) • a ∈
        segment ℝ 0 a ∩ segment ℝ 0 b := ⟨hleft, hright⟩
    rwa [hinter, mem_singleton_iff] at hmem
  exact (smul_ne_zero (ne_of_gt (div_pos hB hsum)) ha) hz

/-- The two signed side functionals can be prescribed independently. -/
theorem exists_forms_eq {a b : Plane} (hdet : det a b ≠ 0) (s t : ℝ) :
    ∃ x : Plane, leftForm a x = s ∧ rightForm b x = t := by
  obtain ⟨x, hs, ht⟩ := SegmentCrossing.exists_detForm_eq_pair hdet s (-t)
  refine ⟨x, hs, ?_⟩
  change -SegmentCrossing.detForm b x = t
  rw [ht, neg_neg]

theorem leftForm_surjective {a b : Plane} (hdet : det a b ≠ 0) :
    Function.Surjective (leftForm a) :=
  SegmentCrossing.detForm_surjective_of_det_ne_zero hdet

theorem rightForm_surjective {a b : Plane} (hdet : det a b ≠ 0) :
    Function.Surjective (rightForm b) := by
  intro t
  obtain ⟨x, _, hx⟩ := exists_forms_eq hdet 0 t
  exact ⟨x, hx⟩

@[simp] theorem leftForm_self (a : Plane) : leftForm a a = 0 :=
  SegmentCrossing.det_self a

@[simp] theorem rightForm_self (b : Plane) : rightForm b b = 0 := by
  exact (rightForm_apply b b).trans (SegmentCrossing.det_self b)

/-- The actual two segments lie in the nonnegative sector boundary. -/
theorem forms_of_mem_segment_union {a b x : Plane} (hdet : 0 ≤ det a b)
    (hx : x ∈ segment ℝ 0 a ∪ segment ℝ 0 b) :
    0 ≤ leftForm a x ∧ 0 ≤ rightForm b x ∧
      (leftForm a x = 0 ∨ rightForm b x = 0) := by
  rcases hx with hx | hx
  · rw [segment_eq_image] at hx
    rcases hx with ⟨t, ht, rfl⟩
    have hf : leftForm a ((1 - t) • 0 + t • a) = 0 := by
      rw [smul_zero, zero_add, map_smul, leftForm_self, smul_zero]
    refine ⟨hf.ge, ?_, Or.inl hf⟩
    change 0 ≤ rightForm b ((1 - t) • 0 + t • a)
    rw [smul_zero, zero_add, map_smul, smul_eq_mul, rightForm_apply]
    exact mul_nonneg ht.1 hdet
  · rw [segment_eq_image] at hx
    rcases hx with ⟨t, ht, rfl⟩
    have hg : rightForm b ((1 - t) • 0 + t • b) = 0 := by
      rw [smul_zero, zero_add, map_smul, rightForm_self, smul_zero]
    refine ⟨?_, hg.ge, Or.inr hg⟩
    change 0 ≤ leftForm a ((1 - t) • 0 + t • b)
    rw [smul_zero, zero_add, map_smul, smul_eq_mul, leftForm_apply]
    exact mul_nonneg ht.1 hdet

@[simp] theorem leftForm_neg_sub (a b : Plane) :
    leftForm a (-a - b) = -det a b := by
  rw [map_sub, map_neg, leftForm_self, leftForm_apply, neg_zero, zero_sub]

@[simp] theorem rightForm_neg_sub (a b : Plane) :
    rightForm b (-a - b) = -det a b := by
  rw [map_sub, map_neg, rightForm_self, sub_zero, rightForm_apply]

theorem negative_direction {a b : Plane} (hdet : 0 < det a b)
    (ha : a ≠ 0) (hb : b ≠ 0)
    (ha0 : 0 ≤ a 0) (ha1 : 0 ≤ a 1)
    (hb0 : 0 ≤ b 0) (hb1 : 0 ≤ b 1) :
    leftForm a (-a - b) < 0 ∧ rightForm b (-a - b) < 0 ∧
      coordSum (-a - b) < 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [leftForm_neg_sub]
    linarith
  · rw [rightForm_neg_sub]
    linarith
  · rw [map_sub, map_neg]
    linarith [coordSum_pos ha ha0 ha1, coordSum_pos hb hb0 hb1]

/-- Coordinate version of the two-functional decomposition. -/
theorem forms_decomposition (a b x : Plane) :
    rightForm b x • a + leftForm a x • b = det a b • x := by
  ext i
  fin_cases i <;> simp [det, SegmentCrossing.det] <;> ring

/-- A sector between first-quadrant vectors remains in that quadrant. -/
theorem coords_nonneg_of_forms_nonneg {a b x : Plane}
    (hdet : 0 < det a b) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (hleft : 0 ≤ leftForm a x) (hright : 0 ≤ rightForm b x) :
    ∀ i, 0 ≤ x i := by
  intro i
  have h := congrArg (fun y : Plane => y i) (forms_decomposition a b x)
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at h
  have hnonneg : 0 ≤ det a b * x i := by
    rw [← h]
    exact add_nonneg (mul_nonneg hright (ha i)) (mul_nonneg hleft (hb i))
  exact nonneg_of_mul_nonneg_right hnonneg hdet

end

end Puzzling139335.N6.TripleSectors.LocalSector
