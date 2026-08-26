/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierLocalMultiplicity
import ErdosProblems.Erdos4b.GeneralFourierSingularProduct

/-!
# The single auxiliary-prime correction

The simplified Fourier graph has no edge at the auxiliary prime, but
the literal residue families can collapse there. Their local-factor
ratio is retained explicitly and differs from one by `O(K/q)`.
-/

namespace Erdos4b

noncomputable section

open Filter
open scoped BigOperators Topology

theorem abs_one_sub_div_ratio_sub_one_le {p n x y : ℝ}
    (hp : 0 < p) (hn : 0 ≤ n) (hpn : 2 * n ≤ p)
    (hx0 : 0 ≤ x) (hxn : x ≤ n) (hy0 : 0 ≤ y) (hyn : y ≤ n) :
    |(1 - y / p) / (1 - x / p) - 1| ≤ 2 * n / p := by
  have hpx : 0 < p - x := by linarith
  have hden : 1 - x / p ≠ 0 := by
    apply ne_of_gt
    rw [sub_pos, div_lt_one hp]
    linarith
  have hid : (1 - y / p) / (1 - x / p) - 1 = (x - y) / (p - x) := by
    field_simp
    ring
  have hdiff : |x - y| ≤ n := abs_le.mpr ⟨by linarith, by linarith⟩
  rw [hid, abs_div, abs_of_pos hpx]
  calc
    _ ≤ n / (p / 2) := div_le_div₀ hn hdiff (by positivity) (by linarith)
    _ = _ := by ring

theorem norm_ratio_zeroExponent_realFactors_sub_one_le
    (n : ℕ) {p x y : ℝ} (hp : 2 ≤ p) (hpn : 2 * (n : ℝ) ≤ p)
    (hx0 : 0 ≤ x) (hxn : x ≤ n) (hy0 : 0 ≤ y) (hyn : y ≤ n) :
    ‖(((1 - y / p) / (1 - 1 / p) ^ n : ℝ) : ℂ) /
      (((1 - x / p) / (1 - 1 / p) ^ n : ℝ) : ℂ) - 1‖ ≤ 2 * (n : ℝ) / p := by
  have hp0 : 0 < p := by linarith
  have hbase : 1 - 1 / p ≠ 0 := by
    apply ne_of_gt
    rw [sub_pos, div_lt_one hp0]
    linarith
  have heq :
      (((1 - y / p) / (1 - 1 / p) ^ n : ℝ) : ℂ) /
        (((1 - x / p) / (1 - 1 / p) ^ n : ℝ) : ℂ) - 1 =
      ((((1 - y / p) / (1 - 1 / p) ^ n) /
        ((1 - x / p) / (1 - 1 / p) ^ n) - 1 : ℝ) : ℂ) := by
    simp only [Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_one]
  rw [heq, Complex.norm_real, Real.norm_eq_abs,
    div_div_div_cancel_right₀ (pow_ne_zero n hbase)]
  exact abs_one_sub_div_ratio_sub_one_le hp0 (Nat.cast_nonneg _) hpn hx0 hxn hy0 hyn

def affineAuxiliaryPrimeCorrection (H : Finset ℕ) (m q : ℕ) : ℂ :=
  (largeGapLocalFactor H m q q : ℂ) /
    doubledFourierSingularFactor (affineFourierCollisionEdges H m q)
      (affineFourierCompanionSwitch m) q

theorem norm_affineAuxiliaryPrimeCorrection_sub_one_le
    (H : Finset ℕ) {m q : ℕ} (hq : q.Prime) (hcard : 4 * (H.card : ℝ) ≤ q) :
    ‖affineAuxiliaryPrimeCorrection H m q - 1‖ ≤ 4 * (H.card : ℝ) / q := by
  let D := doubledFourierExceptionalCount (Finset.univ : Finset H)
    (affineFourierCollisionEdges H m q q) (affineFourierCompanionSwitch m q)
  have hDle : D ≤ 2 * H.card := by
    dsimp [D]
    rw [affineFourierCollisionEdges_eq_empty_of_dvd_q H hq (dvd_refl q)]
    unfold doubledFourierExceptionalCount
    cases affineFourierCompanionSwitch m q <;> simp
    omega
  have hDreal : (D : ℝ) ≤ (2 * H.card : ℕ) := by exact_mod_cast hDle
  have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg _
  have hωreal : (largeGapLocalMultiplicity H m q q : ℝ) ≤ (2 * H.card : ℕ) := by
    exact_mod_cast largeGapLocalMultiplicity_le_two_mul_card H m q q
  have hS : doubledFourierSingularFactor (affineFourierCollisionEdges H m q)
      (affineFourierCompanionSwitch m) q =
      (((1 - (((2 * H.card : ℕ) : ℝ) - D) / q) /
        (1 - 1 / (q : ℝ)) ^ (2 * H.card) : ℝ) : ℂ) := by
    rw [doubledFourierSingularFactor_eq_ofReal]
    simp only [Fintype.card_sum, Fintype.card_coe, ← two_mul]
    rfl
  have hF : largeGapLocalFactor H m q q =
      (1 - (largeGapLocalMultiplicity H m q q : ℝ) / q) /
        (1 - 1 / (q : ℝ)) ^ (2 * H.card) := by
    simp only [largeGapLocalFactor, div_eq_mul_inv, inv_pow]
  rw [affineAuxiliaryPrimeCorrection, hS, hF]
  have hbound := norm_ratio_zeroExponent_realFactors_sub_one_le (2 * H.card)
    (p := (q : ℝ)) (x := ((2 * H.card : ℕ) : ℝ) - D)
    (y := (largeGapLocalMultiplicity H m q q : ℝ))
    (by exact_mod_cast hq.two_le) (by push_cast; linarith)
    (sub_nonneg.mpr hDreal) (sub_le_self _ hD0) (Nat.cast_nonneg _) hωreal
  convert hbound using 1
  push_cast
  ring

theorem tendsto_affineAuxiliaryPrimeCorrection_one
    {α : Type*} {l : Filter α} (K : ℕ) (H : α → Finset ℕ) (m q : α → ℕ)
    (hcard : ∀ a, (H a).card = K) (hq : ∀ᶠ a in l, (q a).Prime)
    (hqTop : Tendsto q l atTop) :
    Tendsto (fun a ↦ affineAuxiliaryPrimeCorrection (H a) (m a) (q a)) l (𝓝 1) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hqR : Tendsto (fun a ↦ (q a : ℝ)) l atTop := tendsto_natCast_atTop_atTop.comp hqTop
  apply squeeze_zero' (Eventually.of_forall fun a ↦ norm_nonneg _)
    (g := fun a ↦ 4 * (K : ℝ) / (q a : ℝ))
  · filter_upwards [hq, hqR.eventually_ge_atTop (4 * (K : ℝ))] with a hqa hlarge
    simpa only [hcard a] using norm_affineAuxiliaryPrimeCorrection_sub_one_le
      (H a) hqa (by simpa only [hcard a] using hlarge)
  · exact tendsto_const_nhds.div_atTop hqR

end

end Erdos4b
