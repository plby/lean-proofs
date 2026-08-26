import ErdosProblems.Erdos633b.GeneralSineArea
import ErdosProblems.Erdos633b.RightTileQuartics

/-! Polynomial root transfer turns the actual sine-product area identity
into a necessary sign agreement. All representation, irreducibility, root,
and nonvanishing premises are explicit. -/

namespace Erdos633b
open Polynomial

theorem sign_agreement_of_square_identity (n P Q F G : ℝ) (hn : 0 < n)
    (hP : P ≠ 0) (hF : F ≠ 0) (he : n * P * F ^ 2 = G ^ 2 * Q) : 0 < P * Q := by
  have hs : 0 < F ^ 2 := sq_pos_of_ne_zero hF
  rcases lt_or_gt_of_ne hP with hp | hp
  · have hl : n * P * F ^ 2 < 0 :=
      mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hn hp) hs
    have hq : Q < 0 := by
      by_contra h
      have hh : 0 ≤ G ^ 2 * Q := mul_nonneg (sq_nonneg _) (le_of_not_gt h)
      rw [← he] at hh
      linarith
    exact mul_pos_of_neg_of_neg hp hq
  · have hl : 0 < n * P * F ^ 2 := mul_pos (mul_pos hn hp) hs
    have hq : 0 < Q := by
      by_contra h
      have hh : G ^ 2 * Q ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (le_of_not_gt h)
      rw [← he] at hh
      linarith
    exact mul_pos hp hq

theorem polynomial_conjugate_sign_agreement (f P Q F G : ℚ[X]) (t t' : ℝ)
    (hf : Irreducible f) (hm : f.Monic) (ht : aeval t f = 0) (ht' : aeval t' f = 0)
    (n : ℕ) (hn : 0 < n)
    (he : (n : ℝ) * aeval t P * (aeval t F) ^ 2 = (aeval t G) ^ 2 * aeval t Q)
    (hP : aeval t' P ≠ 0) (hF : aeval t' F ≠ 0) :
    0 < aeval t' P * aeval t' Q := by
  let g : ℚ[X] := C (n : ℚ) * P * F ^ 2 - G ^ 2 * Q
  have hg : aeval t g = 0 := by simpa [g] using sub_eq_zero.mpr he
  have hg' := rational_polynomial_root_transfer f g t t' hf hm ht ht' hg
  have he' : (n : ℝ) * aeval t' P * (aeval t' F) ^ 2 = (aeval t' G) ^ 2 * aeval t' Q := by
    simpa [g, sub_eq_zero] using hg'
  exact sign_agreement_of_square_identity _ _ _ _ _ (by exact_mod_cast hn) hP hF he'

namespace Tiling

theorem conjugate_sine_product_positive {T : Triangle} {n : ℕ} (d : Tiling T n)
    (u : ℝ) (hu : u ≠ 0) (f P Q F G : ℚ[X]) (t t' : ℝ)
    (hf : Irreducible f) (hm : f.Monic) (ht : aeval t f = 0) (ht' : aeval t' f = 0)
    (hP : aeval t P = (Real.sin (d.tile.angle 0) / u) *
      (Real.sin (d.tile.angle 1) / u) * (Real.sin (d.tile.angle 2) / u))
    (hQ : aeval t Q = (Real.sin (T.angle 0) / u) *
      (Real.sin (T.angle 1) / u) * (Real.sin (T.angle 2) / u))
    (hF : aeval t F = Real.sin (T.angle 0) / u)
    (hG : aeval t G = (d.boundarySideCount 0 0 : ℝ) * (Real.sin (d.tile.angle 0) / u) +
      d.boundarySideCount 0 1 * (Real.sin (d.tile.angle 1) / u) +
      d.boundarySideCount 0 2 * (Real.sin (d.tile.angle 2) / u))
    (hP' : aeval t' P ≠ 0) (hF' : aeval t' F ≠ 0) :
    0 < aeval t' P * aeval t' Q := by
  apply polynomial_conjugate_sign_agreement f P Q F G t t' hf hm ht ht' n d.positive _ hP' hF'
  rw [hP, hQ, hF, hG]
  exact d.scaled_sine_product_area_identity u hu

end Tiling
end Erdos633b
