import Util.IncidenceGeometry.RichLinesBound
import Util.IncidenceGeometry.SzemerediTrotter
import ErdosProblems.Erdos652.Circles

open scoped Real
noncomputable section

namespace Erdos652

open Classical in
/-- The total number of incidences between a planar point set and all lines
containing at least two of its points is `O(m²)`.  We retain the actual finite
line family because it will receive the perpendicular bisectors of bad arcs. -/
lemma twoRichLineIncidences :
    ∃ C : ℝ, 0 < C ∧
      ∀ P : Finset Point, 4 ≤ P.card →
        ∃ L : Finset {ℓ : AffineSubspace ℝ Point // IsAffineLine ℓ},
          (∀ ℓ, ℓ ∈ L ↔
            2 ≤ (P.filter (fun p => p ∈ (ℓ.1 : AffineSubspace ℝ Point))).card) ∧
          (LineIncidences P L : ℝ) ≤ C * ((P.card : ℝ) ^ 2 + (P.card : ℝ)) := by
  obtain ⟨CR, hCR, hrich⟩ := RichLinesBound
  obtain ⟨CS, hCS, hST⟩ := SzemerediTrotter
  let R : ℝ := max 1 CR
  let C : ℝ := CS * (R + R + 1)
  have hR1 : (1 : ℝ) ≤ R := le_max_left _ _
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR1
  have hCRR : CR ≤ R := le_max_right _ _
  have hCpos : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hCpos, ?_⟩
  intro P hm4
  have hmnonneg : 0 ≤ (P.card : ℝ) := by positivity
  have hsqrt4 : (2 : ℝ) ≤ Real.sqrt (P.card : ℝ) := by
    rw [show (2 : ℝ) = Real.sqrt 4 by norm_num]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hm4)
  obtain ⟨L, hLmem, hLcard0⟩ := hrich P 2 (by omega) (by norm_num at hsqrt4 ⊢; exact hsqrt4)
  refine ⟨L, hLmem, ?_⟩
  have hLcard : (L.card : ℝ) ≤ R * (P.card : ℝ) ^ 2 := by
    calc
      (L.card : ℝ) ≤ CR * (P.card : ℝ) ^ 2 / (2 : ℝ) ^ 3 := hLcard0
      _ ≤ CR * (P.card : ℝ) ^ 2 := by
        have hnonneg : 0 ≤ CR * (P.card : ℝ) ^ 2 :=
          mul_nonneg hCR.le (sq_nonneg _)
        norm_num
        linarith
      _ ≤ R * (P.card : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right hCRR (sq_nonneg _)
  let M : ℝ := (((P.card : ℝ) * (L.card : ℝ)) ^ ((2 : ℝ) / 3))
  have hMLnonneg : 0 ≤ (P.card : ℝ) * (L.card : ℝ) := by positivity
  have hmul : (P.card : ℝ) * (L.card : ℝ) ≤
      R * (P.card : ℝ) ^ 3 := by
    calc
      (P.card : ℝ) * (L.card : ℝ) ≤
          (P.card : ℝ) * (R * (P.card : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hLcard hmnonneg
      _ = R * (P.card : ℝ) ^ 3 := by ring
  have hM : M ≤ R * (P.card : ℝ) ^ 2 := by
    have hrpow := Real.rpow_le_rpow (by positivity : 0 ≤ (P.card : ℝ) * (L.card : ℝ))
      hmul (by norm_num : (0 : ℝ) ≤ (2 : ℝ) / 3)
    have hrewrite :
        (R * (P.card : ℝ) ^ 3) ^ ((2 : ℝ) / 3) =
          R ^ ((2 : ℝ) / 3) * (P.card : ℝ) ^ 2 := by
      rw [Real.mul_rpow hRpos.le (by positivity)]
      rw [← Real.rpow_natCast_mul hmnonneg 3 ((2 : ℝ) / 3)]
      norm_num
    have hRpow : R ^ ((2 : ℝ) / 3) ≤ R :=
      Real.rpow_le_self_of_one_le hR1 (by norm_num)
    calc
      M ≤ (R * (P.card : ℝ) ^ 3) ^ ((2 : ℝ) / 3) := hrpow
      _ = R ^ ((2 : ℝ) / 3) * (P.card : ℝ) ^ 2 := hrewrite
      _ ≤ R * (P.card : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right hRpow (sq_nonneg _)
  have hLlinear : (L.card : ℝ) ≤
      R * ((P.card : ℝ) ^ 2 + (P.card : ℝ)) := by
    calc
      (L.card : ℝ) ≤ R * (P.card : ℝ) ^ 2 := hLcard
      _ ≤ R * ((P.card : ℝ) ^ 2 + (P.card : ℝ)) := by
        exact mul_le_mul_of_nonneg_left (by linarith) hRpos.le
  have hmlinear : (P.card : ℝ) ≤
      (P.card : ℝ) ^ 2 + (P.card : ℝ) := by
    nlinarith [sq_nonneg (P.card : ℝ)]
  have hMlinear : M ≤
      R * ((P.card : ℝ) ^ 2 + (P.card : ℝ)) :=
    hM.trans (mul_le_mul_of_nonneg_left (by
      linarith) hRpos.le)
  calc
    (LineIncidences P L : ℝ) ≤
        CS * (M + (P.card : ℝ) + (L.card : ℝ)) := hST P L
    _ ≤ CS * ((R + R + 1) *
        ((P.card : ℝ) ^ 2 + (P.card : ℝ))) := by
      gcongr
      nlinarith [hMlinear, hLlinear, hmlinear]
    _ = C * ((P.card : ℝ) ^ 2 + (P.card : ℝ)) := by
      simp [C]
      ring

end Erdos652
