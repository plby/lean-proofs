import Mathlib.Tactic
import ErdosProblems.Erdos733.ST.PlanarRot90AngleCoordinateDecomposition
import ErdosProblems.Erdos733.ST.PlanarRot90ClockwiseWedgeSignCriterion
import ErdosProblems.Erdos733.ST.PlanarRot90ClockwiseWedgeTauTrig

open Classical
noncomputable section

-- [TABLET NODE: PlanarRot90ClockwiseWedgeAngleCriterion]
lemma PlanarRot90ClockwiseWedgeAngleCriterion
    (β ν α rb rn ra c s x y : ℝ)
    (hβ0 : 0 ≤ β) (hβ2 : β < 2 * Real.pi)
    (hν0 : 0 ≤ ν) (hν2 : ν < 2 * Real.pi)
    (hα0 : 0 ≤ α) (hα2 : α < 2 * Real.pi)
    (hrb : 0 < rb) (hrn : 0 < rn) (hra : 0 < ra)
    (hαν : α ≠ β) (hνβ : ν ≠ β)
    (hpoint :
      let e : ℝ → EuclideanSpace ℝ (Fin 2) :=
        fun t => WithLp.toLp 2
          (fun k : Fin 2 => if k = 0 then Real.cos t else Real.sin t)
      let base : EuclideanSpace ℝ (Fin 2) := rb • e β
      ra • e α = x • base + y • PlanarRot90 base)
    (hother :
      let e : ℝ → EuclideanSpace ℝ (Fin 2) :=
        fun t => WithLp.toLp 2
          (fun k : Fin 2 => if k = 0 then Real.cos t else Real.sin t)
      let base : EuclideanSpace ℝ (Fin 2) := rb • e β
      rn • e ν = c • base - s • PlanarRot90 base) :
    let τ : ℝ → ℝ :=
      fun t => if t = β then 2 * Real.pi
        else if t < β then β - t
        else β - t + 2 * Real.pi
    (if 0 < s then
        y < 0 ∧ 0 < c * y + s * x
      else if s < 0 then
        y < 0 ∨ 0 < c * y + s * x
      else
        y < 0) ↔ τ α < τ ν := by
-- BODY
  dsimp only at hpoint hother
  dsimp only
  let e : ℝ → EuclideanSpace ℝ (Fin 2) :=
    fun t => WithLp.toLp 2
      (fun k : Fin 2 => if k = 0 then Real.cos t else Real.sin t)
  let base : EuclideanSpace ℝ (Fin 2) := rb • e β
  let τ : ℝ → ℝ :=
    fun t => if t = β then 2 * Real.pi
      else if t < β then β - t
      else β - t + 2 * Real.pi
  let A : ℝ := τ α
  let N : ℝ := τ ν
  have hτ_bounds {t : ℝ} (ht0 : 0 ≤ t) (ht2 : t < 2 * Real.pi)
      (htne : t ≠ β) : 0 < τ t ∧ τ t < 2 * Real.pi := by
    dsimp [τ]
    rw [if_neg htne]
    by_cases hlt : t < β
    · simp [hlt]
      linarith
    · simp [hlt]
      have hβlt : β < t := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm htne)
      constructor <;> linarith
  have hA_bounds : 0 < A ∧ A < 2 * Real.pi := hτ_bounds hα0 hα2 hαν
  have hN_bounds : 0 < N ∧ N < 2 * Real.pi := hτ_bounds hν0 hν2 hνβ
  have hcoord_point :=
    PlanarRot90AngleCoordinateDecomposition β α rb ra (ne_of_gt hrb)
  have hpoint_rep :
      ra • e α = x • base + y • PlanarRot90 base := by
    simpa [e, base] using hpoint
  have hxy := hcoord_point.2 hpoint_rep
  have hcoord_other :=
    PlanarRot90AngleCoordinateDecomposition β ν rb rn (ne_of_gt hrb)
  have hother_rep :
      rn • e ν = c • base + (-s) • PlanarRot90 base := by
    simpa [e, base, sub_eq_add_neg, neg_smul] using hother
  have hcs := hcoord_other.2 hother_rep
  have htrig := PlanarRot90ClockwiseWedgeTauTrig β ν α hαν hνβ
  have htrigN := PlanarRot90ClockwiseWedgeTauTrig β ν ν hνβ hνβ
  have hsinA : Real.sin (α - β) = -Real.sin A := by
    simpa [τ, A] using htrig.1
  have hcosA : Real.cos (α - β) = Real.cos A := by
    simpa [τ, A] using htrig.2.1
  have hsinNA : Real.sin (α - ν) = Real.sin (N - A) := by
    simpa [τ, A, N] using htrig.2.2
  have hsinN : Real.sin (ν - β) = -Real.sin N := by
    simpa [τ, N] using htrigN.1
  have hcosN : Real.cos (ν - β) = Real.cos N := by
    simpa [τ, N] using htrigN.2.1
  have hfactorA_pos : 0 < ra / rb := div_pos hra hrb
  have hfactorN_pos : 0 < rn / rb := div_pos hrn hrb
  have hy_eq : y = -(ra / rb) * Real.sin A := by
    calc
      y = (ra / rb) * Real.sin (α - β) := hxy.2
      _ = (ra / rb) * (-Real.sin A) := by rw [hsinA]
      _ = -(ra / rb) * Real.sin A := by ring
  have hc_eq : c = (rn / rb) * Real.cos N := by
    calc
      c = (rn / rb) * Real.cos (ν - β) := hcs.1
      _ = (rn / rb) * Real.cos N := by rw [hcosN]
  have hs_eq : s = (rn / rb) * Real.sin N := by
    have hsneg : -s = (rn / rb) * Real.sin (ν - β) := hcs.2
    calc
      s = -((rn / rb) * Real.sin (ν - β)) := by linarith
      _ = -((rn / rb) * (-Real.sin N)) := by rw [hsinN]
      _ = (rn / rb) * Real.sin N := by ring
  have hx_eq : x = (ra / rb) * Real.cos (α - β) := hxy.1
  have hline_eq :
      c * y + s * x =
        (rn / rb) * (ra / rb) * Real.sin (N - A) := by
    calc
      c * y + s * x =
          ((rn / rb) * Real.cos (ν - β)) *
              ((ra / rb) * Real.sin (α - β)) +
            (-(rn / rb) * Real.sin (ν - β)) *
              ((ra / rb) * Real.cos (α - β)) := by
            have hs_alt : s = -(rn / rb) * Real.sin (ν - β) := by
              calc
                s = -((rn / rb) * Real.sin (ν - β)) := by linarith
                _ = -(rn / rb) * Real.sin (ν - β) := by ring
            rw [hcs.1, hxy.2, hs_alt, hxy.1]
      _ = (rn / rb) * (ra / rb) *
            (Real.sin (α - β) * Real.cos (ν - β) -
              Real.cos (α - β) * Real.sin (ν - β)) := by
            ring
      _ = (rn / rb) * (ra / rb) * Real.sin (α - ν) := by
            have hdet :
                Real.sin (α - β) * Real.cos (ν - β) -
                    Real.cos (α - β) * Real.sin (ν - β) =
                  Real.sin (α - ν) := by
              have harg : (α - β) - (ν - β) = α - ν := by ring
              rw [← harg]
              symm
              rw [Real.sin_sub]
            rw [hdet]
      _ = (rn / rb) * (ra / rb) * Real.sin (N - A) := by rw [hsinNA]
  have hsin_pos_iff {x : ℝ} (hx0 : 0 < x) (hx2 : x < 2 * Real.pi) :
      0 < Real.sin x ↔ x < Real.pi := by
    constructor
    · intro hsin
      by_contra hnot
      have hpi_le : Real.pi ≤ x := le_of_not_gt hnot
      rcases eq_or_lt_of_le hpi_le with hpi | hpi_lt
      · rw [← hpi, Real.sin_pi] at hsin
        linarith
      · have hxsub_neg : x - 2 * Real.pi < 0 := by linarith
        have hxsub_gt : -Real.pi < x - 2 * Real.pi := by linarith
        have hneg : Real.sin (x - 2 * Real.pi) < 0 :=
          Real.sin_neg_of_neg_of_neg_pi_lt hxsub_neg hxsub_gt
        rw [Real.sin_sub_two_pi] at hneg
        linarith
    · intro hxpi
      exact Real.sin_pos_of_pos_of_lt_pi hx0 hxpi
  have hy_iff : y < 0 ↔ A < Real.pi := by
    rw [hy_eq]
    have : (-(ra / rb) * Real.sin A < 0) ↔ 0 < Real.sin A := by
      constructor
      · intro h
        by_contra hnot
        have hsin_nonpos : Real.sin A ≤ 0 := le_of_not_gt hnot
        have hnegfac_nonpos : -(ra / rb) ≤ 0 := by linarith
        have hprod_nonneg : 0 ≤ -(ra / rb) * Real.sin A :=
          mul_nonneg_of_nonpos_of_nonpos hnegfac_nonpos hsin_nonpos
        linarith
      · intro hsin
        exact mul_neg_of_neg_of_pos (neg_neg_of_pos hfactorA_pos) hsin
    exact this.trans (hsin_pos_iff hA_bounds.1 hA_bounds.2)
  have hline_iff : 0 < c * y + s * x ↔ 0 < Real.sin (N - A) := by
    rw [hline_eq]
    have hfac_pos : 0 < (rn / rb) * (ra / rb) :=
      mul_pos hfactorN_pos hfactorA_pos
    constructor
    · intro h
      exact (pos_iff_pos_of_mul_pos h).mp hfac_pos
    · intro h
      exact mul_pos hfac_pos h
  have hspos_iff : 0 < s ↔ 0 < Real.sin N := by
    rw [hs_eq]
    constructor
    · intro h
      exact (pos_iff_pos_of_mul_pos h).mp hfactorN_pos
    · intro h
      exact mul_pos hfactorN_pos h
  have hsneg_iff : s < 0 ↔ Real.sin N < 0 := by
    rw [hs_eq]
    constructor
    · intro h
      by_contra hnot
      have hsin_nonneg : 0 ≤ Real.sin N := le_of_not_gt hnot
      have hprod_nonneg : 0 ≤ (rn / rb) * Real.sin N :=
        mul_nonneg (le_of_lt hfactorN_pos) hsin_nonneg
      linarith
    · intro h
      exact mul_neg_of_pos_of_neg hfactorN_pos h
  have hcrit :=
    PlanarRot90ClockwiseWedgeSignCriterion A N
      hA_bounds.1 hA_bounds.2 hN_bounds.1 hN_bounds.2
  by_cases hspos : 0 < s
  · have hsinNpos : 0 < Real.sin N := hspos_iff.mp hspos
    simpa [hspos, hsinNpos, hy_iff, hline_iff] using hcrit
  · by_cases hsneg : s < 0
    · have hsinNneg : Real.sin N < 0 := hsneg_iff.mp hsneg
      have hsinNnotpos : ¬ 0 < Real.sin N := by linarith
      simpa [hspos, hsneg, hsinNnotpos, hsinNneg, hy_iff, hline_iff] using hcrit
    · have hsinNnotpos : ¬ 0 < Real.sin N := by
        intro h
        exact hspos (hspos_iff.mpr h)
      have hsinNnotneg : ¬ Real.sin N < 0 := by
        intro h
        exact hsneg (hsneg_iff.mpr h)
      simpa [hspos, hsneg, hsinNnotpos, hsinNnotneg, hy_iff, hline_iff] using hcrit
