import ErdosProblems.Erdos633b.SixtyArrays

/-! Exact strip gluing and enlarged group-2 trapezoid layers. -/

namespace Erdos633b.Sixty

theorem disjoint_interiors_of_separator (T : Triangle) (S U : Set Plane) (a b c : ℝ)
    (hab : a ≠ 0 ∨ b ≠ 0) (hS : S ⊆ {p | T.coordForm a b p ≤ c})
    (hU : U ⊆ {p | c ≤ T.coordForm a b p}) : Disjoint (interior S) (interior U) := by
  have hSi := interior_mono hS
  have hUi := interior_mono hU
  rw [T.interior_coordForm_le a b c hab] at hSi
  rw [T.interior_coordForm_ge a b c hab] at hUi
  apply Set.disjoint_left.mpr
  intro p hp hq
  have hleft := hSi hp
  have hright := hUi hq
  change T.coordForm a b p < c at hleft
  change c < T.coordForm a b p at hright
  exact lt_asymm hleft hright

theorem strip_union (d : ℝ) (hd : 0 < d) (z x w y : ℝ) (hx : 0 ≤ x) (hw : 0 ≤ w) :
    strip d hd z x y ∪ strip d hd (z + x) w y = strip d hd z (x + w) y := by
  ext p
  simp only [Set.mem_union, strip, Set.mem_ofPred_eq]
  constructor
  · rintro (⟨ht, hty, hlo, hhi⟩ | ⟨ht, hty, hlo, hhi⟩)
    · exact ⟨ht, hty, hlo, by linarith⟩
    · exact ⟨ht, hty, by linarith, by linarith⟩
  · rintro ⟨ht, hty, hlo, hhi⟩
    by_cases h : (frame d hd).coord 1 p + (frame d hd).coord 2 p ≤ z + x
    · exact Or.inl ⟨ht, hty, hlo, h⟩
    · exact Or.inr ⟨ht, hty, le_of_not_ge h, by linarith⟩

theorem strips_disjoint_interiors (d : ℝ) (hd : 0 < d) (z x w y : ℝ) :
    Disjoint (interior (strip d hd z x y)) (interior (strip d hd (z + x) w y)) := by
  apply disjoint_interiors_of_separator (frame d hd) _ _ 1 1 (z + x) (Or.inl one_ne_zero)
  · intro p hp
    change (frame d hd).coordForm 1 1 p ≤ z + x
    simpa only [Triangle.coordForm_apply, one_mul] using hp.2.2.2
  · intro p hp
    change z + x ≤ (frame d hd).coordForm 1 1 p
    simpa only [Triangle.coordForm_apply, one_mul] using hp.2.2.1

theorem trapezoid_strip_union (d : ℝ) (hd : 0 < d) (x y z : ℝ) (hx : 0 ≤ x) (hz : 0 ≤ z) :
    TrapezoidPartition.trapezoidSet (frame d hd) x y ∪ strip d hd (x + y) z y =
      TrapezoidPartition.trapezoidSet (frame d hd) (x + z) y := by
  ext p
  simp only [Set.mem_union, TrapezoidPartition.trapezoidSet,
    TrapezoidPartition.trapezoid, strip, Set.mem_ofPred_eq]
  constructor
  · rintro (⟨hs, ht, hty, hsum⟩ | ⟨ht, hty, hlo, hhi⟩)
    · exact ⟨hs, ht, hty, by linarith⟩
    · exact ⟨by linarith, ht, hty, by linarith⟩
  · rintro ⟨hs, ht, hty, hsum⟩
    by_cases h : (frame d hd).coord 1 p + (frame d hd).coord 2 p ≤ x + y
    · exact Or.inl ⟨hs, ht, hty, h⟩
    · exact Or.inr ⟨ht, hty, le_of_not_ge h, by linarith⟩

theorem trapezoid_strip_disjoint_interiors (d : ℝ) (hd : 0 < d) (x y z : ℝ) :
    Disjoint (interior (TrapezoidPartition.trapezoidSet (frame d hd) x y))
      (interior (strip d hd (x + y) z y)) := by
  apply disjoint_interiors_of_separator (frame d hd) _ _ 1 1 (x + y) (Or.inl one_ne_zero)
  · intro p hp
    change (frame d hd).coordForm 1 1 p ≤ x + y
    simpa only [Triangle.coordForm_apply, one_mul] using hp.2.2.2
  · intro p hp
    change x + y ≤ (frame d hd).coordForm 1 1 p
    simpa only [Triangle.coordForm_apply, one_mul] using hp.2.2.1

noncomputable def extend_trapezoid_patch (d : ℝ) (hd : 0 < d) (R : Triangle) (x y u v : ℝ)
    (hx : 0 ≤ x) (hu : 0 ≤ u) (hv : 0 ≤ v) (n₀ n₁ n₂ : ℕ)
    (base : Patch R (TrapezoidPartition.trapezoidSet (frame d hd) x y) n₀)
    (first : Patch R (strip d hd (x + y) u y) n₁)
    (second : Patch R (strip d hd (x + y + u) v y) n₂) :
    Patch R (TrapezoidPartition.trapezoidSet (frame d hd) (x + (u + v)) y) (n₀ + (n₁ + n₂)) := by
  have strips := first.glueTwo second (strips_disjoint_interiors d hd (x + y) u v y)
  rw [strip_union d hd (x + y) u v y hu hv] at strips
  have result := base.glueTwo strips (trapezoid_strip_disjoint_interiors d hd x y (u + v))
  rwa [trapezoid_strip_union d hd x y (u + v) hx (add_nonneg hu hv)] at result

noncomputable def wide_layer_patch (d : ℝ) (hd : 0 < d) (he : d ^ 2 = 3)
    (a b c u v : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hu : 0 < u) (hv : 0 < v)
    (hrel : (c : ℝ) ^ 2 = (a : ℝ) ^ 2 + (a : ℝ) * b + (b : ℝ) ^ 2) :
    Patch (groupTwoReference d hd a b (by exact_mod_cast ha) (by exact_mod_cast hb))
      (TrapezoidPartition.trapezoidSet (frame d hd)
        ((a : ℝ) ^ 2 + (b : ℝ) ^ 2 + ((u : ℝ) * a + (v : ℝ) * b)) ((a : ℝ) * b))
      ((a ^ 2 + b ^ 2 + c ^ 2) + (2 * a * u + 2 * v * b)) := by
  have har : (0 : ℝ) < a := by exact_mod_cast ha
  have hbr : (0 : ℝ) < b := by exact_mod_cast hb
  have hur : (0 : ℝ) < u := by exact_mod_cast hu
  have hvr : (0 : ℝ) < v := by exact_mod_cast hv
  let R := groupTwoReference d hd a b har hbr
  let x := (a : ℝ) ^ 2 + (b : ℝ) ^ 2
  let y := (a : ℝ) * b
  have base := basic_trapezoid_patch d hd he a b c ha hb hc hrel
  have first := swapped_array_patch d hd he a b (x + y) har hbr a u ha hu
  have second : Patch R (strip d hd (x + y + (u : ℝ) * a) ((v : ℝ) * b) y) (2 * v * b) := by
    have result := aligned_array_patch d hd a b (x + y + (u : ℝ) * a) har hbr v b hv hb
    simpa only [mul_comm (b : ℝ) (a : ℝ)] using result
  exact extend_trapezoid_patch d hd R x y ((u : ℝ) * a) ((v : ℝ) * b)
    (add_nonneg (sq_nonneg _) (sq_nonneg _)) (mul_pos hur har).le (mul_pos hvr hbr).le
    _ _ _ base first second

end Erdos633b.Sixty
