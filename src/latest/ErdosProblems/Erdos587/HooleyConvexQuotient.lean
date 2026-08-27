import ErdosProblems.Erdos587.NVDevelopment

/-! # Exact lattice lifting from a shrunken primitive convex quotient -/

namespace Erdos587.GeneralizedAP

theorem delta_exists_lattice_lift_of_shrunken_quotient (X : ConvexProgression)
    {n : ℕ} (u a : Fin X.rank → ℤ) (hua : dotLinear a u = 1)
    (b : Module.Basis (Fin n) ℤ (LinearMap.ker (dotLinear a))) (hn : n + 1 = X.rank)
    {η : ℝ} (hη : 0 ≤ η) (hη1 : η ≤ 1)
    (hu : intCastVec u ∈ bodyDilate η X.body)
    (y : Fin n → ℤ)
    (hy : intCastVec y ∈ bodyDilate (1 - η)
      (intLinearMapRealExtension (primitiveQuotientProjection u a hua b) '' X.body)) :
    ∃ v : Fin X.rank → ℤ, intCastVec v ∈ X.body ∧
      primitiveQuotientProjection u a hua b v = y := by
  let q := primitiveQuotientProjection u a hua b
  let qR := intLinearMapRealExtension q
  obtain ⟨p, ⟨x, hx, rfl⟩, hscaled⟩ := hy
  obtain ⟨v₀, hv₀⟩ := primitiveQuotientProjection_surjective u a hua b y
  have hv₀R : qR (intCastVec v₀) = intCastVec y := by
    rw [intLinearMapRealExtension_intCastVec, hv₀]
  have hxR : qR ((1 - η) • x) = intCastVec y := by
    rw [map_smul]
    exact hscaled
  have hkernel : qR (intCastVec v₀ - (1 - η) • x) = 0 := by
    rw [map_sub, hv₀R, hxR, sub_self]
  obtain ⟨r, hr⟩ := ConvexProgression.exists_eq_smul_direction_of_real_quotient_eq_zero
    u a hua b hn (intCastVec v₀ - (1 - η) • x) hkernel
  let k : ℤ := -round r
  let v := v₀ + k • u
  have hlift : intCastVec v₀ = (1 - η) • x + r • intCastVec u := by
    calc
      _ = (intCastVec v₀ - (1 - η) • x) + (1 - η) • x := by abel
      _ = r • intCastVec u + (1 - η) • x := by rw [hr]
      _ = _ := add_comm _ _
  have hcast : intCastVec v = (1 - η) • x + (r + (k : ℝ)) • intCastVec u := by
    dsimp only [v]
    rw [ConvexProgression.intCastVec_add, ConvexProgression.intCastVec_zsmul, hlift, add_smul]
    abel
  have hround : |r + (k : ℝ)| ≤ (1 / 2 : ℝ) := by
    simpa only [k, Int.cast_neg, ← sub_eq_add_neg] using abs_sub_round r
  have huGauge : gauge X.body (intCastVec u) ≤ η := gauge_le_of_mem hη hu
  have hscaledGauge : gauge X.body ((1 - η) • x) ≤ 1 - η := by
    rw [gauge_smul_of_nonneg (sub_nonneg.mpr hη1), smul_eq_mul]
    exact mul_le_of_le_one_right (sub_nonneg.mpr hη1) (gauge_le_one_of_mem hx)
  have hroundGauge : gauge X.body ((r + (k : ℝ)) • intCastVec u) ≤ η / 2 := by
    rw [gauge_smul X.body_balanced, Real.norm_eq_abs]
    calc
      _ ≤ (1 / 2 : ℝ) * η :=
        mul_le_mul hround huGauge (gauge_nonneg _) (by norm_num)
      _ = _ := by ring
  have hvGauge : gauge X.body (intCastVec v) ≤ 1 := by
    rw [hcast]
    calc
      _ ≤ gauge X.body ((1 - η) • x) +
          gauge X.body ((r + (k : ℝ)) • intCastVec u) :=
        gauge_add_le X.body_convex X.body_absorbent _ _
      _ ≤ (1 - η) + η / 2 := add_le_add hscaledGauge hroundGauge
      _ ≤ 1 := by linarith
  have hvBody : intCastVec v ∈ X.body := by
    obtain ⟨z, hz, heq⟩ := MahlerBoxData.mem_bodyDilate_of_gauge_le
      (show (0 : ℝ) < 1 by norm_num) hvGauge
    have hzv : z = intCastVec v := by simpa only [one_smul] using heq
    exact hzv ▸ hz
  have hqu : q u = 0 :=
    (primitiveQuotientProjection_eq_zero_iff u a hua b u).2 (by simp [hua])
  refine ⟨v, hvBody, ?_⟩
  change q (v₀ + k • u) = y
  rw [map_add, map_zsmul, hqu, smul_zero, add_zero]
  exact hv₀

theorem delta_shrunken_quotient_eval_subset (X : ConvexProgression)
    {n : ℕ} (u a : Fin X.rank → ℤ) (hua : dotLinear a u = 1)
    (b : Module.Basis (Fin n) ℤ (LinearMap.ker (dotLinear a))) (hn : n + 1 = X.rank)
    {η : ℝ} (hη : 0 ≤ η) (hη1 : η ≤ 1)
    (hu : intCastVec u ∈ bodyDilate η X.body) (heval : X.eval u = 0) :
    (fun y : Fin n → ℤ => X.base + primitiveQuotientEval X.eval b y) ''
      {y | intCastVec y ∈ bodyDilate (1 - η)
        (intLinearMapRealExtension (primitiveQuotientProjection u a hua b) '' X.body)} ⊆
      X.carrier := by
  rintro z ⟨y, hy, rfl⟩
  obtain ⟨v, hv, hqv⟩ :=
    delta_exists_lattice_lift_of_shrunken_quotient X u a hua b hn hη hη1 hu y hy
  refine ⟨v, hv, ?_⟩
  change X.base + X.eval v = X.base + primitiveQuotientEval X.eval b y
  rw [← hqv, primitiveQuotientEval_projection X.eval u a hua heval b v]

lemma delta_injOn_half_body_of_no_short_kernel (X : ConvexProgression) (η : ℝ)
    (hkernel : ∀ v : Fin X.rank → ℤ, X.eval v = 0 →
      intCastVec v ∈ bodyDilate η X.body → v = 0) :
    Set.InjOn X.eval {v : Fin X.rank → ℤ | intCastVec v ∈ bodyDilate (η / 2) X.body} := by
  intro x hx y hy heval
  have hsub : intCastVec (x - y) ∈ bodyDilate η X.body := by
    rw [intCastVec_sub]
    simpa only [show 2 * (η / 2) = η by ring] using
      sub_mem_bodyDilate_two_mul X.body_convex X.body_neg hx hy
  have heval0 : X.eval (x - y) = 0 := by rw [map_sub, heval, sub_self]
  exact sub_eq_zero.mp (hkernel (x - y) heval0 hsub)

end Erdos587.GeneralizedAP
