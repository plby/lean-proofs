import ErdosProblems.Erdos633b.TrapezoidLayers

/-! Translation and exact vertical stacking of closed sixty-degree trapezoids. -/

namespace Erdos633b.Sixty

theorem point_eq_latticeShift (d : ℝ) (hd : 0 < d) (s t : ℝ) :
    point d s t = (frame d hd).latticeShift s t := by
  have h0 : (frame d hd).points 0 = 0 := point_zero d
  have hP := point_linear d s t
  change point d s t = s • ((frame d hd).points 1 - (frame d hd).points 0) +
    t • ((frame d hd).points 2 - (frame d hd).points 0)
  rw [h0, sub_zero, sub_zero]
  exact hP

theorem coords_add_point (d : ℝ) (hd : 0 < d) (s t : ℝ) (p : Plane) :
    (frame d hd).coord 1 (point d s t + p) = s + (frame d hd).coord 1 p ∧
      (frame d hd).coord 2 (point d s t + p) = t + (frame d hd).coord 2 p := by
  rw [point_eq_latticeShift d hd, Triangle.coord_shift_one, Triangle.coord_shift_two]
  exact ⟨rfl, rfl⟩

theorem coords_sub_point (d : ℝ) (hd : 0 < d) (s t : ℝ) (p : Plane) :
    (frame d hd).coord 1 (p - point d s t) = (frame d hd).coord 1 p - s ∧
      (frame d hd).coord 2 (p - point d s t) = (frame d hd).coord 2 p - t := by
  have h := coords_add_point d hd s t (p - point d s t)
  rw [show point d s t + (p - point d s t) = p by abel] at h
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

noncomputable def cap (d : ℝ) (hd : 0 < d) (x y r : ℝ) : Set Plane :=
  {p | 0 ≤ (frame d hd).coord 1 p ∧ r ≤ (frame d hd).coord 2 p ∧
    (frame d hd).coord 2 p ≤ r + y ∧
    (frame d hd).coord 1 p + (frame d hd).coord 2 p ≤ x + y + r}

theorem translated_trapezoid (d : ℝ) (hd : 0 < d) (x y r : ℝ) :
    (AffineIsometryEquiv.constVAdd ℝ Plane (point d 0 r)) ''
      TrapezoidPartition.trapezoidSet (frame d hd) x y = cap d hd x y r := by
  ext p
  constructor
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨hs, ht, hty, hsum⟩ := hv
    change 0 ≤ (frame d hd).coord 1 (point d 0 r + v) ∧
      r ≤ (frame d hd).coord 2 (point d 0 r + v) ∧
      (frame d hd).coord 2 (point d 0 r + v) ≤ r + y ∧
      (frame d hd).coord 1 (point d 0 r + v) +
        (frame d hd).coord 2 (point d 0 r + v) ≤ x + y + r
    rw [(coords_add_point d hd 0 r v).1, (coords_add_point d hd 0 r v).2, zero_add]
    exact ⟨hs, by linarith, by linarith, by linarith⟩
  · rintro ⟨hs, ht, hty, hsum⟩
    refine ⟨p - point d 0 r, ?_, ?_⟩
    · change 0 ≤ (frame d hd).coord 1 (p - point d 0 r) ∧
        0 ≤ (frame d hd).coord 2 (p - point d 0 r) ∧
        (frame d hd).coord 2 (p - point d 0 r) ≤ y ∧
        (frame d hd).coord 1 (p - point d 0 r) +
          (frame d hd).coord 2 (p - point d 0 r) ≤ x + y
      rw [(coords_sub_point d hd 0 r p).1, (coords_sub_point d hd 0 r p).2, sub_zero]
      exact ⟨hs, by linarith, by linarith, by linarith⟩
    · change point d 0 r + (p - point d 0 r) = p
      abel

theorem stack_union (d : ℝ) (hd : 0 < d) (x y r : ℝ) (hy : 0 ≤ y) (hr : 0 ≤ r) :
    TrapezoidPartition.trapezoidSet (frame d hd) (x + y) r ∪ cap d hd x y r =
      TrapezoidPartition.trapezoidSet (frame d hd) x (r + y) := by
  ext p
  simp only [Set.mem_union, TrapezoidPartition.trapezoidSet, TrapezoidPartition.trapezoid,
    cap, Set.mem_ofPred_eq]
  constructor
  · rintro (⟨hs, ht, htr, hsum⟩ | ⟨hs, ht, htr, hsum⟩)
    · exact ⟨hs, ht, by linarith, by linarith⟩
    · exact ⟨hs, by linarith, htr, by linarith⟩
  · rintro ⟨hs, ht, htr, hsum⟩
    by_cases h : (frame d hd).coord 2 p ≤ r
    · exact Or.inl ⟨hs, ht, h, by linarith⟩
    · exact Or.inr ⟨hs, le_of_not_ge h, htr, by linarith⟩

theorem stack_disjoint_interiors (d : ℝ) (hd : 0 < d) (x y r : ℝ) :
    Disjoint (interior (TrapezoidPartition.trapezoidSet (frame d hd) (x + y) r))
      (interior (cap d hd x y r)) := by
  apply disjoint_interiors_of_separator (frame d hd) _ _ 0 1 r (Or.inr one_ne_zero)
  · intro p hp
    change (frame d hd).coordForm 0 1 p ≤ r
    simpa only [Triangle.coordForm_apply, zero_mul, one_mul, zero_add] using hp.2.2.1
  · intro p hp
    change r ≤ (frame d hd).coordForm 0 1 p
    simpa only [Triangle.coordForm_apply, zero_mul, one_mul, zero_add] using hp.2.1

noncomputable def stack_patch_step (d : ℝ) (hd : 0 < d) (R : Triangle) (x y r : ℝ)
    (hy : 0 ≤ y) (hr : 0 ≤ r) (n m : ℕ)
    (lower : Patch R (TrapezoidPartition.trapezoidSet (frame d hd) (x + y) r) n)
    (upper : Patch R (TrapezoidPartition.trapezoidSet (frame d hd) x y) m) :
    Patch R (TrapezoidPartition.trapezoidSet (frame d hd) x (r + y)) (n + m) := by
  have top := upper.move (AffineIsometryEquiv.constVAdd ℝ Plane (point d 0 r))
  rw [translated_trapezoid d hd x y r] at top
  have result := lower.glueTwo top (stack_disjoint_interiors d hd x y r)
  rwa [stack_union d hd x y r hy hr] at result

end Erdos633b.Sixty
