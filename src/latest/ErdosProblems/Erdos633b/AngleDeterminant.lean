import ErdosProblems.Erdos633b.SmallAngleRelations

/-! Exact integral elimination of a local relation and the actual
corner-column angle equation. -/

namespace Erdos633b

def cornerLocalDeterminant (P Q R : ℕ) (t : ℤ × ℤ × ℤ) : ℤ :=
  ((P : ℤ) - R) * t.2.1 - ((Q : ℤ) - R) * t.1

def cornerLocalAlphaNumerator (_P Q R : ℕ) (t : ℤ × ℤ × ℤ) : ℤ :=
  (1 - (R : ℤ)) * t.2.1 - ((Q : ℤ) - R) * t.2.2

def cornerLocalBetaNumerator (P _Q R : ℕ) (t : ℤ × ℤ × ℤ) : ℤ :=
  ((P : ℤ) - R) * t.2.2 - (1 - (R : ℤ)) * t.1

theorem corner_local_elimination (α β γ : ℝ) (hs : α + β + γ = Real.pi)
    (P Q R : ℕ) (hc : (P : ℝ) * α + Q * β + R * γ = Real.pi)
    (t : ℤ × ℤ × ℤ)
    (he : (t.1 : ℝ) * α + (t.2.1 : ℝ) * β = (t.2.2 : ℝ) * Real.pi) :
    (cornerLocalDeterminant P Q R t : ℝ) * α =
      cornerLocalAlphaNumerator P Q R t * Real.pi ∧
    (cornerLocalDeterminant P Q R t : ℝ) * β =
      cornerLocalBetaNumerator P Q R t * Real.pi := by
  have hc' : ((P : ℝ) - R) * α + ((Q : ℝ) - R) * β = (1 - (R : ℝ)) * Real.pi := by
    linear_combination hc - (R : ℝ) * hs
  dsimp only [cornerLocalDeterminant, cornerLocalAlphaNumerator, cornerLocalBetaNumerator]
  push_cast
  constructor
  · linear_combination (t.2.1 : ℝ) * hc' - ((Q : ℝ) - R) * he
  · linear_combination ((P : ℝ) - R) * he - (t.1 : ℝ) * hc'

theorem corner_local_zero_numerators (α β γ : ℝ) (hs : α + β + γ = Real.pi)
    (P Q R : ℕ) (hc : (P : ℝ) * α + Q * β + R * γ = Real.pi)
    (t : ℤ × ℤ × ℤ)
    (he : (t.1 : ℝ) * α + (t.2.1 : ℝ) * β = (t.2.2 : ℝ) * Real.pi)
    (hd : cornerLocalDeterminant P Q R t = 0) :
    cornerLocalAlphaNumerator P Q R t = 0 ∧ cornerLocalBetaNumerator P Q R t = 0 := by
  obtain ⟨ha, hb⟩ := corner_local_elimination α β γ hs P Q R hc t he
  rw [hd, Int.cast_zero, zero_mul] at ha hb
  constructor
  · exact_mod_cast (mul_eq_zero.mp ha.symm).resolve_right Real.pi_ne_zero
  · exact_mod_cast (mul_eq_zero.mp hb.symm).resolve_right Real.pi_ne_zero

theorem ordered_relation_coefficient_bounds (t : ℤ × ℤ × ℤ)
    (ht : t ∈ orderedNonrightRelationTriples) : |t.1| ≤ 5 ∧ |t.2.1| ≤ 11 := by
  have ht := (Finset.mem_erase.mp ht).2
  simp only [orderedRelationTriples, Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl <;> norm_num

theorem corner_local_determinant_bound (P Q R : ℕ) (hP : P ≤ 21) (hQ : Q ≤ 5)
    (hR : R ≤ 1) (t : ℤ × ℤ × ℤ) (ht : t ∈ orderedNonrightRelationTriples) :
    |cornerLocalDeterminant P Q R t| ≤ 256 := by
  obtain ⟨hA, hB⟩ := ordered_relation_coefficient_bounds t ht
  have hPR : |(P : ℤ) - R| ≤ 21 := abs_le.mpr ⟨by omega, by omega⟩
  have hQR : |(Q : ℤ) - R| ≤ 5 := abs_le.mpr ⟨by omega, by omega⟩
  calc
    |cornerLocalDeterminant P Q R t| ≤ |(P : ℤ) - R| * |t.2.1| +
        |(Q : ℤ) - R| * |t.1| := by
      simpa only [cornerLocalDeterminant, sub_eq_add_neg, abs_mul, abs_neg] using
        abs_add_le (((P : ℤ) - R) * t.2.1) (-(((Q : ℤ) - R) * t.1))
    _ ≤ 21 * 11 + 5 * 5 := add_le_add
      (mul_le_mul hPR hB (abs_nonneg _) (by decide))
      (mul_le_mul hQR hA (abs_nonneg _) (by decide))
    _ = 256 := by norm_num

end Erdos633b
