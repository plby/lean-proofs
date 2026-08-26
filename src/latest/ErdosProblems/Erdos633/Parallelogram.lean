import ErdosProblems.Erdos633.RegionTiling

/-!
# Parallelogram grids of congruent triangles

A rectangle has two triangular pieces in every unit cell. Affine transport
gives a parallelogram grid of copies of an arbitrary triangle.
-/

namespace Erdos633

def closedRectangle (m n : ℕ) : Set ℂ :=
  {z | 0 ≤ z.re ∧ z.re ≤ m ∧ 0 ≤ z.im ∧ z.im ≤ n}

def rectangleGridTile (m n : ℕ) (p : (Fin m × Fin n) × Bool) : Triangle :=
  if p.2 then unitUpper p.1.1.val p.1.2.val else unitLower p.1.1.val p.1.2.val

theorem rectangleGridTile_subset (m n : ℕ) (p : (Fin m × Fin n) × Bool) :
    (rectangleGridTile m n p).carrier ⊆ closedRectangle m n := by
  intro z hz
  have hi0 : (0 : ℝ) ≤ p.1.1 := by positivity
  have hj0 : (0 : ℝ) ≤ p.1.2 := by positivity
  have hi : (p.1.1 : ℝ) + 1 ≤ m := by exact_mod_cast Nat.add_one_le_iff.mpr p.1.1.isLt
  have hj : (p.1.2 : ℝ) + 1 ≤ n := by exact_mod_cast Nat.add_one_le_iff.mpr p.1.2.isLt
  change 0 ≤ z.re ∧ z.re ≤ m ∧ 0 ≤ z.im ∧ z.im ≤ n
  by_cases hp : p.2 = true
  · rw [rectangleGridTile, if_pos hp] at hz
    rw [unitUpper_mem_iff] at hz
    push_cast at hz
    exact ⟨by linarith [hz.2.1, hz.2.2], by linarith [hz.1],
      by linarith [hz.1, hz.2.2], by linarith [hz.2.1]⟩
  · rw [rectangleGridTile, if_neg hp] at hz
    rw [unitLower_mem_iff] at hz
    push_cast at hz
    exact ⟨by linarith [hz.1], by linarith [hz.2.1, hz.2.2],
      by linarith [hz.2.1], by linarith [hz.1, hz.2.2]⟩

theorem rectangleGrid_covers (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    (⋃ p : (Fin m × Fin n) × Bool, (rectangleGridTile m n p).carrier) =
      closedRectangle m n := by
  apply Set.Subset.antisymm
  · exact Set.iUnion_subset fun p => rectangleGridTile_subset m n p
  · intro z hz
    obtain ⟨i, hi, hi1, _⟩ := exists_unit_interval_index m hm z.re hz.1 hz.2.1
    obtain ⟨j, hj, hj1, _⟩ := exists_unit_interval_index n hn z.im hz.2.2.1 hz.2.2.2
    by_cases hdiag : z.re + z.im ≤ (i : ℝ) + j + 1
    · refine Set.mem_iUnion.mpr ⟨((i, j), false), ?_⟩
      change z ∈ (unitLower i.val j.val).carrier
      rw [unitLower_mem_iff]
      exact ⟨hi, hj, hdiag⟩
    · refine Set.mem_iUnion.mpr ⟨((i, j), true), ?_⟩
      change z ∈ (unitUpper i.val j.val).carrier
      rw [unitUpper_mem_iff]
      exact ⟨hi1, hj1, le_of_lt (lt_of_not_ge hdiag)⟩

theorem rectangleGrid_disjoint (m n : ℕ) :
    Pairwise fun p q : (Fin m × Fin n) × Bool =>
      Disjoint (interior (rectangleGridTile m n p).carrier)
        (interior (rectangleGridTile m n q).carrier) := by
  rintro ⟨⟨i, j⟩, b⟩ ⟨⟨k, l⟩, c⟩ hne
  have hcells (hbc : b = c) : ((i.val : ℤ), (j.val : ℤ)) ≠ ((k.val : ℤ), (l.val : ℤ)) := by
    intro h
    have hi := congrArg Prod.fst h
    have hj := congrArg Prod.snd h
    dsimp at hi hj
    have hik : i = k := Fin.ext (by exact_mod_cast hi)
    have hjl : j = l := Fin.ext (by exact_mod_cast hj)
    subst k
    subst l
    subst c
    exact hne rfl
  cases b <;> cases c
  · exact unitLower_disjoint (hcells rfl)
  · exact unitLower_upper_disjoint _ _ _ _
  · exact (unitLower_upper_disjoint _ _ _ _).symm
  · exact unitUpper_disjoint (hcells rfl)

noncomputable def parallelogramGrid (e : ℂ ≃ᵃ[ℝ] ℂ) (m n : ℕ)
    (hm : 0 < m) (hn : 0 < n) :
    RegionTiling (e '' closedRectangle m n) (standardTriangle.mapAffineEquiv e)
      ((Fin m × Fin n) × Bool) where
  tile p := (rectangleGridTile m n p).mapAffineEquiv e
  congruent := by
    intro p
    by_cases hp : p.2 = true
    · rw [rectangleGridTile, if_pos hp]
      exact affine_image_halfTurn_congruent standardTriangle e _
    · rw [rectangleGridTile, if_neg hp]
      exact affine_image_translate_congruent standardTriangle e _
  covers := by
    simp only [Triangle.mapAffineEquiv_carrier]
    rw [← Set.image_iUnion, rectangleGrid_covers m n hm hn]
  disjoint := by
    intro p q hpq
    simp only [Triangle.mapAffineEquiv_interior]
    exact Set.disjoint_image_of_injective e.injective (rectangleGrid_disjoint m n hpq)

end Erdos633
