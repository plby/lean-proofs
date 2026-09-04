import Util.IncidenceGeometry.IsAffineLine
import Util.IncidenceGeometry.LineIncidences
import Util.IncidenceGeometry.CrossingLemma
import Util.IncidenceGeometry.PolygonalReplacementForGeometricArcs
import Util.IncidenceGeometry.PointLineConsecutivePairDrawing

open scoped Real

theorem SzemerediTrotter :
    ∃ C : ℝ, 0 < C ∧
      ∀ (P : Finset (EuclideanSpace ℝ (Fin 2)))
        (L : Finset {ℓ : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)) // IsAffineLine ℓ}),
        (LineIncidences P L : ℝ) ≤
          C * (((P.card : ℝ) * (L.card : ℝ)) ^ ((2 : ℝ) / 3) +
            (P.card : ℝ) + (L.card : ℝ)) := by
  refine ⟨5 + (100 : ℝ) ^ ((1 : ℝ) / 3), by positivity, ?_⟩
  intro P L
  by_cases hP0 : P.card = 0
  · have hPempty : P = ∅ := Finset.card_eq_zero.mp hP0
    simp only [one_div, ge_iff_le]
    exact mul_nonneg
      (add_nonneg (by norm_num) (Real.rpow_nonneg (by norm_num) _)) (by positivity)
  by_cases hL0 : L.card = 0
  · have hLempty : L = ∅ := Finset.card_eq_zero.mp hL0
    simp only [one_div, ge_iff_le]
    exact mul_nonneg
      (add_nonneg (by norm_num) (Real.rpow_nonneg (by norm_num) _)) (by positivity)
  have hn_nat : 1 ≤ P.card := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hP0)
  have hl_nat : 1 ≤ L.card := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hL0)
  have hn_nonneg : 0 ≤ (P.card : ℝ) := by positivity
  have hl_nonneg : 0 ≤ (L.card : ℝ) := by positivity
  let mainTerm : ℝ :=
    ((P.card : ℝ) * (L.card : ℝ)) ^ ((2 : ℝ) / 3)
  have hmain_nonneg : 0 ≤ mainTerm := by
    dsimp [mainTerm]
    exact Real.rpow_nonneg (mul_nonneg hn_nonneg hl_nonneg) _
  have hroot_nonneg : 0 ≤ (100 : ℝ) ^ ((1 : ℝ) / 3) :=
    Real.rpow_nonneg (by norm_num) _
  have hsum_nonneg :
      0 ≤ mainTerm + (P.card : ℝ) + (L.card : ℝ) := by positivity
  rcases PointLineConsecutivePairDrawing P L with
    ⟨G, hGfin, D, ell, hell, hinc, hlocal⟩
  let : Fintype G.edgeSet := hGfin
  obtain ⟨_Dpoly, _hpolyCrossings, hcross_upper_nat⟩ :=
    PolygonalReplacementForGeometricArcs G D
  let e : ℝ := (G.edgeFinset.card : ℝ)
  have hell_real : (ell : ℝ) ≤ (L.card : ℝ) := by exact_mod_cast hell
  have hinc_real :
      (LineIncidences P L : ℝ) = e + (ell : ℝ) := by
    dsimp [e]
    exact_mod_cast hinc
  have hcross_upper : (CrossingNumber G : ℝ) ≤ (L.card : ℝ) ^ 2 := by
    have h₁ : (CrossingNumber G : ℝ) ≤ (D.localPairCount : ℝ) := by
      exact_mod_cast hcross_upper_nat
    have h₂ : (D.localPairCount : ℝ) ≤ (ell : ℝ) ^ 2 := by
      exact_mod_cast hlocal
    have h₃ : (ell : ℝ) ^ 2 ≤ (L.card : ℝ) ^ 2 := by
      nlinarith [sq_nonneg ((L.card : ℝ) - (ell : ℝ))]
    exact h₁.trans (h₂.trans h₃)
  by_cases hsmall : G.edgeFinset.card < 4 * P.card
  · have hsmall_real : e < 4 * (P.card : ℝ) := by
      dsimp [e]
      exact_mod_cast hsmall
    have hI_lt :
        (LineIncidences P L : ℝ) < 4 * (P.card : ℝ) + (L.card : ℝ) := by
      rw [hinc_real]
      linarith
    have hsmall_bound :
        (LineIncidences P L : ℝ) ≤
          5 * (mainTerm + (P.card : ℝ) + (L.card : ℝ)) := by
      nlinarith
    have hcoefficient :
        (5 : ℝ) ≤ 5 + (100 : ℝ) ^ ((1 : ℝ) / 3) := by linarith
    exact hsmall_bound.trans
      (mul_le_mul_of_nonneg_right hcoefficient hsum_nonneg)
  · have hlarge_nat : 4 * P.card ≤ G.edgeFinset.card := le_of_not_gt hsmall
    have hnV : 1 ≤ Fintype.card P := by
      simpa [Fintype.card_coe] using hn_nat
    have hlargeV : 4 * Fintype.card P ≤ G.edgeFinset.card := by
      simpa [Fintype.card_coe] using hlarge_nat
    have hcross_lower := CrossingLemma G hnV hlargeV
    have hcross_lower' :
        e ^ 3 / (100 * (P.card : ℝ) ^ 2) ≤ (CrossingNumber G : ℝ) := by
      dsimp [e]
      simpa [Fintype.card_coe] using hcross_lower
    have hdiv_bound :
        e ^ 3 / (100 * (P.card : ℝ) ^ 2) ≤ (L.card : ℝ) ^ 2 :=
      hcross_lower'.trans hcross_upper
    have hden_pos : 0 < 100 * (P.card : ℝ) ^ 2 := by positivity
    have hcube_le :
        e ^ 3 ≤ 100 * (P.card : ℝ) ^ 2 * (L.card : ℝ) ^ 2 := by
      have hmul := (div_le_iff₀ hden_pos).mp hdiv_bound
      nlinarith
    have he_nonneg : 0 ≤ e := by
      dsimp [e]
      positivity
    have htarget_nonneg :
        0 ≤ 100 * (P.card : ℝ) ^ 2 * (L.card : ℝ) ^ 2 := by positivity
    have he_root_inv :
        e ≤ (100 * (P.card : ℝ) ^ 2 * (L.card : ℝ) ^ 2) ^
          ((3 : ℝ)⁻¹) := by
      rw [Real.le_rpow_inv_iff_of_pos he_nonneg htarget_nonneg
        (by norm_num : (0 : ℝ) < 3)]
      simpa [Real.rpow_natCast] using hcube_le
    have hroot_factor :
        (100 * (P.card : ℝ) ^ 2 * (L.card : ℝ) ^ 2) ^
            ((1 : ℝ) / 3) =
          (100 : ℝ) ^ ((1 : ℝ) / 3) * mainTerm := by
      rw [show 100 * (P.card : ℝ) ^ 2 * (L.card : ℝ) ^ 2 =
          100 * ((P.card : ℝ) * (L.card : ℝ)) ^ 2 by ring]
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 100)
        (sq_nonneg ((P.card : ℝ) * (L.card : ℝ)))]
      rw [← Real.rpow_natCast_mul
        (mul_nonneg hn_nonneg hl_nonneg) 2 ((1 : ℝ) / 3)]
      dsimp [mainTerm]
      congr 1
      norm_num
    have hroot_factor_inv :
        (100 * (P.card : ℝ) ^ 2 * (L.card : ℝ) ^ 2) ^
            ((3 : ℝ)⁻¹) =
          (100 : ℝ) ^ ((1 : ℝ) / 3) * mainTerm := by
      simpa [one_div] using hroot_factor
    have he_le :
        e ≤ (100 : ℝ) ^ ((1 : ℝ) / 3) * mainTerm :=
      he_root_inv.trans_eq hroot_factor_inv
    have hI_le :
        (LineIncidences P L : ℝ) ≤
          (100 : ℝ) ^ ((1 : ℝ) / 3) * mainTerm + (L.card : ℝ) := by
      rw [hinc_real]
      linarith
    have hmain_le_sum :
        mainTerm ≤ mainTerm + (P.card : ℝ) + (L.card : ℝ) := by
      linarith
    have hroot_part :
        (100 : ℝ) ^ ((1 : ℝ) / 3) * mainTerm ≤
          (100 : ℝ) ^ ((1 : ℝ) / 3) *
            (mainTerm + (P.card : ℝ) + (L.card : ℝ)) :=
      mul_le_mul_of_nonneg_left hmain_le_sum hroot_nonneg
    have hline_part :
        (L.card : ℝ) ≤
          5 * (mainTerm + (P.card : ℝ) + (L.card : ℝ)) := by
      nlinarith
    calc
      (LineIncidences P L : ℝ) ≤
          (100 : ℝ) ^ ((1 : ℝ) / 3) * mainTerm + (L.card : ℝ) := hI_le
      _ ≤ (5 + (100 : ℝ) ^ ((1 : ℝ) / 3)) *
          (mainTerm + (P.card : ℝ) + (L.card : ℝ)) := by
        nlinarith
