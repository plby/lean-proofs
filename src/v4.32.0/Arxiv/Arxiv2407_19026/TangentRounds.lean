import Arxiv.Arxiv2407_19026.Unconditional

/-!
# Tangent-envelope optimization rounds

The paper's coarse region boost loses information needed for a symmetric
Ramsey region.  Here each later round instead uses a supporting tangent of
the full exponent proved in the preceding round.
-/

noncomputable section

namespace Arxiv2407_19026

def tangentRoundBookMargin (β z X Y : ℝ) : ℝ :=
  optimizedRamseyExponent β z +
    (Real.log X + z * Real.log (optimizationM z) +
      z * Real.log Y) / 2

/-- Logarithmic interpolation between a certified point `(A, B)` and its
swap.  The interpolating arc is the hyperbola `X * Y = A * B`. -/
lemma ExponentRegionCertificate.plateau
    {F : ℝ → ℝ} {A B X : ℝ}
    (C : ExponentRegionCertificate F A B)
    (hA0 : 0 < A) (hB0 : 0 < B) (hX0 : 0 < X)
    (hBX : B ≤ X) (hXA : X ≤ A) :
    ExponentRegionCertificate F X (A * B / X) := by
  have hlogBX : Real.log B ≤ Real.log X :=
    Real.log_le_log hB0 hBX
  have hlogXA : Real.log X ≤ Real.log A :=
    Real.log_le_log hX0 hXA
  have hlogY :
      Real.log (A * B / X) =
        Real.log A + Real.log B - Real.log X := by
    rw [Real.log_div (mul_ne_zero hA0.ne' hB0.ne') hX0.ne',
      Real.log_mul hA0.ne' hB0.ne']
  constructor
  · intro r hr
    have hbase := C.forward r hr
    rw [hlogY]
    have hnonneg :
        0 ≤ (1 - r) * (Real.log A - Real.log X) :=
      mul_nonneg (by linarith [hr.2])
        (sub_nonneg.mpr hlogXA)
    nlinarith
  · intro r hr
    have hbase := C.swap.backward r hr
    rw [hlogY]
    have hnonneg :
        0 ≤ (1 - r) * (Real.log X - Real.log B) :=
      mul_nonneg (by linarith [hr.2])
        (sub_nonneg.mpr hlogBX)
    nlinarith

/-- Pointwise numerical data for passing from exponent `β₀` to exponent
`β₁` using the tangent envelope of the already-proved `β₀` profile. -/
structure TangentRoundCertificate (β₀ β₁ : ℝ) : Prop where
  pointwise :
    ∀ z ∈ Set.Ioc (0 : ℝ) 1,
      ∃ t ∈ Set.Ioc (0 : ℝ) 1,
        let A :=
          tangentRegionX (optimizedRamseyExponent β₀)
            (optimizedRamseySlope β₀) t
        let B := tangentRegionY (optimizedRamseySlope β₀) t
        let X := optimizationX β₁ z
        (X ≤ A ∧ 0 < tangentRoundBookMargin β₁ z X B) ∨
          (X ≤ B ∧ 0 < tangentRoundBookMargin β₁ z X A) ∨
          (B ≤ X ∧ X ≤ A ∧
            0 < tangentRoundBookMargin β₁ z X (A * B / X))

lemma optimizedTangentPoint_swap_mem_ramseyRegion
    {β t : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 2 / 25)
    (ht : t ∈ Set.Ioc (0 : ℝ) 1)
    (hExp : HasRamseyExponent (optimizedRamseyExponent β)) :
    (tangentRegionY (optimizedRamseySlope β) t,
      tangentRegionX (optimizedRamseyExponent β)
        (optimizedRamseySlope β) t) ∈ ramseyRegion := by
  let A :=
    tangentRegionX (optimizedRamseyExponent β)
      (optimizedRamseySlope β) t
  let B := tangentRegionY (optimizedRamseySlope β) t
  have hA0 : 0 < A := Real.exp_pos _
  have hB0 : 0 < B := Real.exp_pos _
  have hA1 : A < 1 :=
    tangentRegionX_lt_one hβ0 hβ1 ht.1 ht.2
  have hB1 : B < 1 := by
    dsimp [B, tangentRegionY]
    rw [Real.exp_lt_one_iff]
    linarith [optimizedRamseySlope_pos hβ0 ht.1 ht.2]
  apply exponentRegionCertificate_mem_ramseyRegion
    hB0 hB1 hA0 hA1
  · exact (tangent_exponentRegionCertificate
      (fun r hr ↦ optimizedRamseyExponent_tangent_upper
        hβ0 hβ1 ht hr)
      (tangentRegionY_le_tangentRegionX hβ0 ht)).swap
  · exact hExp

lemma optimizedTangentPlateau_mem_ramseyRegion
    {β t X : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 2 / 25)
    (ht : t ∈ Set.Ioc (0 : ℝ) 1)
    (hX0 : 0 < X)
    (hBX :
      tangentRegionY (optimizedRamseySlope β) t ≤ X)
    (hXA :
      X ≤ tangentRegionX (optimizedRamseyExponent β)
        (optimizedRamseySlope β) t)
    (hExp : HasRamseyExponent (optimizedRamseyExponent β)) :
    (X,
      tangentRegionX (optimizedRamseyExponent β)
          (optimizedRamseySlope β) t *
        tangentRegionY (optimizedRamseySlope β) t / X) ∈
      ramseyRegion := by
  let A :=
    tangentRegionX (optimizedRamseyExponent β)
      (optimizedRamseySlope β) t
  let B := tangentRegionY (optimizedRamseySlope β) t
  have hA0 : 0 < A := Real.exp_pos _
  have hB0 : 0 < B := Real.exp_pos _
  have hA1 : A < 1 :=
    tangentRegionX_lt_one hβ0 hβ1 ht.1 ht.2
  have hY0 : 0 < A * B / X :=
    div_pos (mul_pos hA0 hB0) hX0
  have hYleA : A * B / X ≤ A := by
    rw [div_le_iff₀ hX0]
    exact mul_le_mul_of_nonneg_left hBX hA0.le
  have hY1 : A * B / X < 1 := hYleA.trans_lt hA1
  apply exponentRegionCertificate_mem_ramseyRegion
    hX0 (hXA.trans_lt hA1) hY0 hY1
  · exact (tangent_exponentRegionCertificate
      (fun r hr ↦ optimizedRamseyExponent_tangent_upper
        hβ0 hβ1 ht hr)
      (tangentRegionY_le_tangentRegionX hβ0 ht)).plateau
        hA0 hB0 hX0 hBX hXA
  · exact hExp

lemma pointwiseBookProfile_of_tangentRoundCertificate
    {β₀ β₁ : ℝ}
    (hβ₀0 : 0 ≤ β₀) (hβ₀1 : β₀ ≤ 2 / 25)
    (hβ₁ : 0 ≤ β₁)
    (hprev : HasRamseyExponent (optimizedRamseyExponent β₀))
    (C : TangentRoundCertificate β₀ β₁) :
    PointwiseBookProfile
      (optimizedRamseyExponent β₁)
      (optimizedRamseySlope β₁) := by
  constructor
  · intro z hz
    exact optimizedRamseyExponent_nonneg_of_nonneg hβ₁ hz
  · intro z hz
    exact hasDerivAt_optimizedRamseyExponent β₁ hz
  · intro z hz
    unfold optimizedRamseySlope
    have hz0 : z ≠ 0 := ne_of_gt hz
    have hzp : z + 1 ≠ 0 := by linarith
    fun_prop
  · intro z hz
    obtain ⟨t, ht, hchoice⟩ := C.pointwise z hz
    let A :=
      tangentRegionX (optimizedRamseyExponent β₀)
        (optimizedRamseySlope β₀) t
    let B := tangentRegionY (optimizedRamseySlope β₀) t
    let μ := optimizationM z
    let p₀ := optimizationP β₁ z
    let X := optimizationX β₁ z
    have hμ : 0 < μ := by
      dsimp [μ, optimizationM]
      exact mul_pos hz.1 (Real.exp_pos _)
    have hμ1 : μ < 1 := by
      have he0 : 0 < Real.exp (-z) := Real.exp_pos _
      have he1 : Real.exp (-z) < 1 :=
        Real.exp_lt_one_iff.mpr (by linarith [hz.1])
      dsimp [μ, optimizationM]
      exact mul_lt_one_of_nonneg_of_lt_one_right hz.2 he0.le he1
    have hs : 0 < optimizedRamseySlope β₁ z :=
      optimizedRamseySlope_pos hβ₁ hz.1 hz.2
    have hp₀ : 0 < p₀ := by
      dsimp [p₀, optimizationP]
      exact sub_pos.mpr
        (Real.exp_lt_one_iff.mpr (by linarith))
    have hp₀1 : p₀ < 1 := by
      dsimp [p₀, optimizationP]
      linarith [Real.exp_pos (-optimizedRamseySlope β₁ z)]
    have hAμ : 0 < 1 - μ := sub_pos.mpr hμ1
    have hXeq :
        X = p₀ ^ ((1 : ℝ) / (1 - μ)) * (1 - μ) := by
      rfl
    have hX0 : 0 < X := by
      rw [hXeq]
      exact mul_pos (Real.rpow_pos_of_pos hp₀ _) hAμ
    have hX1 : X < 1 := by
      have hr : 0 < (1 : ℝ) / (1 - μ) := one_div_pos.mpr hAμ
      have hrpow : p₀ ^ ((1 : ℝ) / (1 - μ)) < 1 :=
        Real.rpow_lt_one hp₀.le hp₀1 hr
      have hAμ1 : 1 - μ < 1 := by linarith
      rw [hXeq]
      exact mul_lt_one_of_nonneg_of_lt_one_left
        (Real.rpow_nonneg hp₀.le _)
        hrpow hAμ1.le
    have hA0 : 0 < A := Real.exp_pos _
    have hB0 : 0 < B := Real.exp_pos _
    have hA1 : A < 1 :=
      tangentRegionX_lt_one hβ₀0 hβ₀1 ht.1 ht.2
    have hB1 : B < 1 := by
      dsimp [B, tangentRegionY]
      rw [Real.exp_lt_one_iff]
      linarith [optimizedRamseySlope_pos hβ₀0 ht.1 ht.2]
    rcases hchoice with hforward | hbackward | hplateau
    · have hregionAB : (A, B) ∈ ramseyRegion := by
        simpa [A, B] using
          optimizedTangentPoint_mem_ramseyRegion
            hβ₀0 hβ₀1 ht hprev
      have hregionXB : (X, B) ∈ ramseyRegion :=
        ramseyRegion_mono hregionAB hX0 hforward.1 hB0 le_rfl
      have hbook :
          -(Real.log X + z * Real.log μ +
              z * Real.log B) / 2 <
            optimizedRamseyExponent β₁ z := by
        unfold tangentRoundBookMargin at hforward
        dsimp [X, μ] at *
        linarith
      exact exists_admissibleBookCellData_of_region
        hμ hμ1 hp₀ hp₀1 hXeq hX0 hX1 hB0 hB1
        hregionXB hbook (by
          dsimp [p₀, optimizationP]
          ring)
    · have hregionBA : (B, A) ∈ ramseyRegion := by
        simpa [A, B] using
          optimizedTangentPoint_swap_mem_ramseyRegion
            hβ₀0 hβ₀1 ht hprev
      have hregionXA : (X, A) ∈ ramseyRegion :=
        ramseyRegion_mono hregionBA hX0 hbackward.1 hA0 le_rfl
      have hbook :
          -(Real.log X + z * Real.log μ +
              z * Real.log A) / 2 <
            optimizedRamseyExponent β₁ z := by
        unfold tangentRoundBookMargin at hbackward
        dsimp [X, μ] at *
        linarith
      exact exists_admissibleBookCellData_of_region
        hμ hμ1 hp₀ hp₀1 hXeq hX0 hX1 hA0 hA1
        hregionXA hbook (by
          dsimp [p₀, optimizationP]
          ring)
    · let Y := A * B / X
      have hY0 : 0 < Y := by
        dsimp [Y]
        exact div_pos (mul_pos hA0 hB0) hX0
      have hYleA : Y ≤ A := by
        dsimp [Y]
        rw [div_le_iff₀ hX0]
        exact mul_le_mul_of_nonneg_left hplateau.1 hA0.le
      have hY1 : Y < 1 := hYleA.trans_lt hA1
      have hregionXY : (X, Y) ∈ ramseyRegion := by
        simpa [A, B, Y, X] using
          optimizedTangentPlateau_mem_ramseyRegion
            hβ₀0 hβ₀1 ht hX0 hplateau.1 hplateau.2.1 hprev
      have hbook :
          -(Real.log X + z * Real.log μ +
              z * Real.log Y) / 2 <
            optimizedRamseyExponent β₁ z := by
        unfold tangentRoundBookMargin at hplateau
        dsimp [X, μ, Y] at *
        linarith
      exact exists_admissibleBookCellData_of_region
        hμ hμ1 hp₀ hp₀1 hXeq hX0 hX1 hY0 hY1
        hregionXY hbook (by
          dsimp [p₀, optimizationP]
          ring)

theorem hasRamseyExponent_of_tangentRoundCertificate
    {β₀ β₁ : ℝ}
    (hβ₀0 : 0 ≤ β₀) (hβ₀1 : β₀ ≤ 2 / 25)
    (hβ₁ : 0 ≤ β₁)
    (hprev : HasRamseyExponent (optimizedRamseyExponent β₀))
    (C : TangentRoundCertificate β₀ β₁) :
    HasRamseyExponent (optimizedRamseyExponent β₁) :=
  hasRamseyExponent_of_pointwiseBookProfile
    (pointwiseBookProfile_of_tangentRoundCertificate
      hβ₀0 hβ₀1 hβ₁ hprev C)
    (hasSmallRatioBase_optimizedRamseyExponent hβ₁)

end Arxiv2407_19026
