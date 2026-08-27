import Arxiv.Arxiv2411_18291.PaperIntegralGeneratorExistence

/-! # Uniform numerical bounds for the complete generator palette -/

open Finset

noncomputable section

namespace Arxiv2411_18291

def paperPaletteUpperBound (q r h : ℕ) : ℕ :=
  3 * (paperColourTrialCount q r (2 * q) * h + 1)

def paperGeneratorCoefficientUpperBound (q r h : ℕ) : ℕ :=
  ((2 * q.choose r + 1) * paperPaletteUpperBound q r h +
    paperColourTrialCount q r (2 * q) * h + 1) * 2 ^ q

def integralGeneratorThreshold (q r : ℕ) : ℕ :=
  max (paperSizeThreshold q (r + 1))
    ((paperGeneratorCoefficientUpperBound q (r + 1)
      (3 * (2 * q) ^ (r + 1) * (q.choose (r + 1)) ^ 2)) ^
        (20 * paperInverseAlpha q (r + 1)))

theorem paperColourTrialCount_mono (q r : ℕ) {f g : ℕ} (hfg : f ≤ g) :
    paperColourTrialCount q r f ≤ paperColourTrialCount q r g := by
  unfold paperColourTrialCount
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.add_le_add_right hfg 1))

theorem paperGeneratorCoefficientUpperBound_pos (q r h : ℕ) :
    0 < paperGeneratorCoefficientUpperBound q r h := by
  unfold paperGeneratorCoefficientUpperBound
  positivity

variable {W : Type*} [Fintype W] [DecidableEq W] {q r h : ℕ}

theorem paperExtensionPaletteSize_le (hqr : r + 1 < q)
    (S : ExchangeSystem W q (r + 1)) (P : Block W q)
    (hqh : q.choose (r + 1) ≤ h) (hSh : S.graph.card ≤ h) :
    paperExtensionPaletteSize S P ≤ paperPaletteUpperBound q (r + 1) h := by
  let L := paperColourTrialCount q (r + 1) (2 * q)
  have hroot : (S.base.val ∪ P.val).card ≤ 2 * q := by
    have hh := card_union_le S.base.val P.val
    rw [S.base.property, P.property] at hh
    omega
  have hnew (F : Finset W) : (newEdges F S.graph).card ≤ h :=
    (card_filter_le _ _).trans hSh
  have h₁ : paperColourTrialCount q (r + 1) (r + 1) * (q.choose (r + 1) - 1) ≤ L * h :=
    Nat.mul_le_mul (paperColourTrialCount_mono q (r + 1) (by omega))
      ((Nat.sub_le _ _).trans hqh)
  have h₂ : paperColourTrialCount q (r + 1) q * (newEdges S.base.val S.graph).card ≤ L * h :=
    Nat.mul_le_mul (paperColourTrialCount_mono q (r + 1) (by omega)) (hnew _)
  have h₃ : paperColourTrialCount q (r + 1) (S.base.val ∪ P.val).card *
      (newEdges (S.base.val ∪ P.val) S.graph).card ≤ L * h :=
    Nat.mul_le_mul (paperColourTrialCount_mono q (r + 1) hroot) (hnew _)
  unfold paperExtensionPaletteSize paperPaletteUpperBound
  change _ ≤ 3 * (L * h + 1)
  omega

theorem paperIntegralGeneratorCoefficient_le (hqr : r + 1 < q)
    (S : ExchangeSystem W q (r + 1)) (P : Block W q)
    (hqh : q.choose (r + 1) ≤ h) (hSh : S.graph.card ≤ h) :
    paperIntegralGeneratorCoefficient S P ≤ paperGeneratorCoefficientUpperBound q (r + 1) h := by
  have hK2 : 2 ≤ q.choose (r + 1) := (show 2 ≤ q by omega).trans (q_le_choose_succ hqr)
  have hfar : S.farCliques.card ≤ h := by
    have hmul := Nat.mul_le_mul_right S.farCliques.card hK2
    have hb := S.far_card_mul_le
    omega
  have hL : paperColourTrialCount q (r + 1) S.base.val.card ≤
      paperColourTrialCount q (r + 1) (2 * q) := by
    rw [S.base.property]
    exact paperColourTrialCount_mono q (r + 1) (by omega)
  have hcoef := Nat.add_le_add_right
    (Nat.add_le_add
      (Nat.mul_le_mul_left (2 * q.choose (r + 1) + 1)
        (paperExtensionPaletteSize_le hqr S P hqh hSh))
      (Nat.mul_le_mul hL hfar)) 1
  unfold paperIntegralGeneratorCoefficient paperGeneratorCoefficientUpperBound
  exact_mod_cast Nat.mul_le_mul_right (2 ^ q) hcoef

theorem generator_assembly_threshold_le_uniform (hqr : r + 1 < q)
    (S : ExchangeSystem W q (r + 1)) (P : Block W q)
    (hqh : q.choose (r + 1) ≤ S.graph.card)
    (hS : S.graph.card ≤ 3 * (2 * q) ^ (r + 1) * (q.choose (r + 1)) ^ 2) :
    finiteGeneratorAssemblyThreshold q r (paperIntegralGeneratorCoefficient S P) ≤
      integralGeneratorThreshold q r := by
  have hc := paperIntegralGeneratorCoefficient_le hqr S P (hqh.trans hS) hS
  have hpos := paperGeneratorCoefficientUpperBound_pos q (r + 1)
    (3 * (2 * q) ^ (r + 1) * (q.choose (r + 1)) ^ 2)
  have hceil : ⌈max 1 (paperIntegralGeneratorCoefficient S P)⌉₊ ≤
      paperGeneratorCoefficientUpperBound q (r + 1)
        (3 * (2 * q) ^ (r + 1) * (q.choose (r + 1)) ^ 2) := by
    apply Nat.ceil_le.mpr
    exact max_le (by exact_mod_cast hpos) hc
  exact max_le_max le_rfl (Nat.pow_le_pow_left hceil _)

end Arxiv2411_18291
