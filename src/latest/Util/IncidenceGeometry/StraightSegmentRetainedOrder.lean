import Mathlib.Tactic
import Util.IncidenceGeometry.Basic

open Classical
noncomputable section

lemma StraightSegmentRetainedOrder
    (A B p g c : EuclideanSpace ℝ (Fin 2))
    (hAB : A ≠ B)
    (hp : p ∈ openSegment ℝ A B)
    (hg : g ∈ openSegment ℝ p B)
    (hc : c ∈ openSegment ℝ A B)
    (hpC : p ∈ segment ℝ A c)
    (hgC : g ∈ segment ℝ A c)
    (hpc : p ≠ c) (hgc : g ≠ c) :
    p ∈ openSegment ℝ A c ∧ g ∈ openSegment ℝ p c := by
  rw [openSegment_eq_image_lineMap] at hp hg hc
  rw [segment_eq_image_lineMap] at hpC hgC
  rcases hp with ⟨t, ht, htp⟩
  rcases hg with ⟨v, hv, hvg⟩
  rcases hc with ⟨s, hs, hsc⟩
  rcases hpC with ⟨u, hu, hucp⟩
  rcases hgC with ⟨q, hq, hqcg⟩
  have hlineInj := AffineMap.lineMap_injective ℝ hAB
  have htus : t = u * s := by
    apply hlineInj
    calc
      AffineMap.lineMap A B t = p := htp
      _ = AffineMap.lineMap A c u := hucp.symm
      _ = AffineMap.lineMap A (AffineMap.lineMap A B s) u := by rw [hsc]
      _ = AffineMap.lineMap A B (u * s) :=
        AffineMap.lineMap_lineMap_right A B s u
  let w := 1 - (1 - v) * (1 - t)
  have hwg : AffineMap.lineMap A B w = g := by
    calc
      AffineMap.lineMap A B w =
          AffineMap.lineMap (AffineMap.lineMap A B t) B v := by
        dsimp [w]
        exact (AffineMap.lineMap_lineMap_left A B t v).symm
      _ = AffineMap.lineMap p B v := by rw [htp]
      _ = g := hvg
  have hwqs : w = q * s := by
    apply hlineInj
    calc
      AffineMap.lineMap A B w = g := hwg
      _ = AffineMap.lineMap A c q := hqcg.symm
      _ = AffineMap.lineMap A (AffineMap.lineMap A B s) q := by rw [hsc]
      _ = AffineMap.lineMap A B (q * s) :=
        AffineMap.lineMap_lineMap_right A B s q
  have huLt : u < 1 := by
    have huNe : u ≠ 1 := by
      intro hu1
      have hpeq : p = c := by
        rw [← hucp, hu1]
        simp
      exact hpc hpeq
    exact lt_of_le_of_ne hu.2 huNe
  have hqLt : q < 1 := by
    have hqNe : q ≠ 1 := by
      intro hq1
      have hgeq : g = c := by
        rw [← hqcg, hq1]
        simp
      exact hgc hgeq
    exact lt_of_le_of_ne hq.2 hqNe
  have hts : t < s := by
    rw [htus]
    nlinarith [mul_pos (sub_pos.mpr huLt) hs.1]
  have htw : t < w := by
    dsimp [w]
    nlinarith [mul_pos hv.1 (sub_pos.mpr ht.2)]
  have hws : w < s := by
    rw [hwqs]
    nlinarith [mul_pos (sub_pos.mpr hqLt) hs.1]
  constructor
  · rw [openSegment_eq_image_lineMap]
    refine ⟨t / s, ⟨div_pos ht.1 hs.1, (div_lt_one hs.1).mpr hts⟩, ?_⟩
    calc
      AffineMap.lineMap A c (t / s) =
          AffineMap.lineMap A (AffineMap.lineMap A B s) (t / s) := by rw [hsc]
      _ = AffineMap.lineMap A B ((t / s) * s) :=
        AffineMap.lineMap_lineMap_right A B s (t / s)
      _ = AffineMap.lineMap A B t := by rw [div_mul_cancel₀ t hs.1.ne']
      _ = p := htp
  · rw [openSegment_eq_image_lineMap]
    let lam := (w - t) / (s - t)
    refine ⟨lam, ⟨?_, ?_⟩, ?_⟩
    · exact div_pos (sub_pos.mpr htw) (sub_pos.mpr hts)
    · rw [div_lt_one (sub_pos.mpr hts)]
      linarith
    · rw [← hwg, ← htp, ← hsc]
      apply PiLp.ext
      intro k
      simp [lam, AffineMap.lineMap_apply_module]
      have hst : s - t ≠ 0 := sub_ne_zero.mpr hts.ne'
      field_simp [hst]
      ring
