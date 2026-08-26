import ErdosProblems.Erdos394.ZonotopeCover
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Measure bounds for two-dimensional zonotopes
-/

open Set MeasureTheory Module
open scoped Pointwise ENNReal Matrix

namespace Erdos394

lemma para_eq_parallelepiped (a b : Fin 2 → ℝ) :
    para a b = parallelepiped ![a, b] := by
  ext p
  rw [mem_parallelepiped_iff]
  constructor
  · rintro ⟨x, y, hx, hy, rfl⟩
    refine ⟨![x, y], ?_, ?_⟩
    · constructor <;> intro i <;> fin_cases i <;>
        simp [hx.1, hx.2, hy.1, hy.2]
    · simp [Fin.sum_univ_two]
  · rintro ⟨t, ht, rfl⟩
    refine ⟨t 0, t 1, ?_, ?_, ?_⟩
    · exact ⟨ht.1 0, ht.2 0⟩
    · exact ⟨ht.1 1, ht.2 1⟩
    · simp [Fin.sum_univ_two]

lemma basisFun_addHaar_eq_volume_fin2 :
    (Pi.basisFun ℝ (Fin 2)).addHaar = volume := by
  rw [Basis.addHaar_def, Basis.parallelepiped_basisFun,
    addHaarMeasure_eq_volume_pi]

/-- Exact measure of a two-generator parallelogram. -/
theorem volume_para (a b : Fin 2 → ℝ) :
    volume (para a b) =
      ENNReal.ofReal |(Pi.basisFun ℝ (Fin 2)).det ![a, b]| := by
  rw [para_eq_parallelepiped, ← basisFun_addHaar_eq_volume_fin2]
  exact Measure.addHaar_parallelepiped (Pi.basisFun ℝ (Fin 2)) ![a, b]

lemma measure_five_union_le (μ : Measure (Fin 2 → ℝ))
    (A B C D E : Set (Fin 2 → ℝ)) :
    μ (A ∪ (B ∪ (C ∪ (D ∪ E)))) ≤
      μ A + μ B + μ C + μ D + μ E := by
  calc
    μ (A ∪ (B ∪ (C ∪ (D ∪ E)))) ≤ μ A + μ (B ∪ (C ∪ (D ∪ E))) :=
      measure_union_le _ _
    _ ≤ μ A + (μ B + μ (C ∪ (D ∪ E))) := by gcongr; exact measure_union_le _ _
    _ ≤ μ A + (μ B + (μ C + μ (D ∪ E))) := by gcongr; exact measure_union_le _ _
    _ ≤ μ A + (μ B + (μ C + (μ D + μ E))) := by gcongr; exact measure_union_le _ _
    _ = μ A + μ B + μ C + μ D + μ E := by ac_rfl

/-- Measure bound for a three-generator zonotope, retaining its designated
base parallelogram with coefficient one. -/
theorem volume_zono3_le {a b c : Fin 2 → ℝ} {α β : ℝ}
    (hc : c = α • a + β • b) :
    volume (zono3 a b c) ≤
      volume (para a b) + 2 * volume (para b c) + 2 * volume (para a c) := by
  calc
    volume (zono3 a b c) ≤ volume
        (para a b ∪ (para b c ∪ ((a +ᵥ para b c) ∪
          (para a c ∪ (b +ᵥ para a c))))) :=
      measure_mono (zono3_subset_five_para hc)
    _ ≤ volume (para a b) + volume (para b c) + volume (a +ᵥ para b c) +
          volume (para a c) + volume (b +ᵥ para a c) :=
      measure_five_union_le volume _ _ _ _ _
    _ = volume (para a b) + 2 * volume (para b c) +
          2 * volume (para a c) := by
      rw [measure_vadd, measure_vadd]
      ring

/-- Cyclic reordering does not change a three-generator zonotope. -/
lemma zono3_cycle (a b c : Fin 2 → ℝ) : zono3 a b c = zono3 b c a := by
  ext p
  constructor
  · rintro ⟨x, y, z, hx, hy, hz, rfl⟩
    exact ⟨y, z, x, hy, hz, hx, by module⟩
  · rintro ⟨x, y, z, hx, hy, hz, rfl⟩
    exact ⟨z, x, y, hz, hx, hy, by module⟩

lemma para_comm (a b : Fin 2 → ℝ) : para a b = para b a := by
  ext p
  constructor
  · rintro ⟨x, y, hx, hy, rfl⟩
    exact ⟨y, x, hy, hx, by module⟩
  · rintro ⟨x, y, hx, hy, rfl⟩
    exact ⟨y, x, hy, hx, by module⟩

/-- Four-generator zonotope bound.  The first two generators form the unique
leading parallelogram; all other pair areas have only absolute coefficients. -/
theorem volume_zono4_le
    {a b c d : Fin 2 → ℝ} {α β γ δ η θ κ ξ : ℝ}
    (hdab : d = α • a + β • b) (hcab : c = γ • a + δ • b)
    (hbcd : b = η • c + θ • d) (hacd : a = κ • c + ξ • d) :
    volume (zono4 a b c d) ≤
      volume (para a b) + 6 * volume (para a c) +
        6 * volume (para b c) + 4 * volume (para a d) +
        4 * volume (para b d) + 4 * volume (para c d) := by
  have hcover := zono4_subset_five_zono3 (c := c) hdab
  have hraw : volume (zono4 a b c d) ≤
      volume (zono3 a b c) + 2 * volume (zono3 b c d) +
        2 * volume (zono3 a c d) := by
    calc
      volume (zono4 a b c d) ≤ volume
          (zono3 a b c ∪ (zono3 b c d ∪ ((a +ᵥ zono3 b c d) ∪
            (zono3 a c d ∪ (b +ᵥ zono3 a c d))))) := measure_mono hcover
      _ ≤ volume (zono3 a b c) + volume (zono3 b c d) +
            volume (a +ᵥ zono3 b c d) + volume (zono3 a c d) +
            volume (b +ᵥ zono3 a c d) := measure_five_union_le volume _ _ _ _ _
      _ = volume (zono3 a b c) + 2 * volume (zono3 b c d) +
            2 * volume (zono3 a c d) := by
        rw [measure_vadd, measure_vadd]
        ring
  have habc := volume_zono3_le hcab
  have hbcdBound : volume (zono3 b c d) ≤
      volume (para c d) + 2 * volume (para d b) + 2 * volume (para c b) := by
    rw [zono3_cycle]
    exact volume_zono3_le hbcd
  have hacdBound : volume (zono3 a c d) ≤
      volume (para c d) + 2 * volume (para d a) + 2 * volume (para c a) := by
    rw [zono3_cycle]
    exact volume_zono3_le hacd
  calc
    volume (zono4 a b c d) ≤
        volume (zono3 a b c) + 2 * volume (zono3 b c d) +
          2 * volume (zono3 a c d) := hraw
    _ ≤ (volume (para a b) + 2 * volume (para b c) + 2 * volume (para a c)) +
        2 * (volume (para c d) + 2 * volume (para d b) + 2 * volume (para c b)) +
        2 * (volume (para c d) + 2 * volume (para d a) + 2 * volume (para c a)) := by
      gcongr
    _ = volume (para a b) + 6 * volume (para a c) +
        6 * volume (para b c) + 4 * volume (para a d) +
        4 * volume (para b d) + 4 * volume (para c d) := by
      rw [para_comm d b, para_comm c b, para_comm d a, para_comm c a]
      ring

end Erdos394
