/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourcePartThreeResidualNumerics

/-!
# Rounded Appendix-A.2 input from the actual residual inequalities

The component count follows from nontriviality, both live sets retain the
gamma reserve, and nonextreme density supplies the integer root reserves.
No Appendix orientation or graph embedding is assumed here.
-/

open scoped BigOperators
noncomputable section

namespace Erdos547b.ZhaoSourcePartThreeAppendixData

open Finset Erdos547b.RegularPair Erdos547b.ZhaoLemma58GroupedSmallForest
open Erdos547b.ZhaoLemma54AppendixA Erdos547b.ZhaoSourcePartThreeResidualNumerics

/-- The source budget and occupied-side trichotomy construct every integer
field needed to invoke the existing Appendix-A.2 orientation theorem. -/
theorem appendixData_of_residual {b : ℕ} (F : OrderedRootedForest b)
    (N gamma epsilon lambda dx dy : ℝ) (X Y P Q small : ℕ)
    (herror : 2 ≤ epsilon * N) (hreserve : 0 ≤ gamma * N)
    (hlambda : 0 ≤ lambda) (hlambdaHalf : lambda ≤ 1 / 2)
    (hdxlo : lambda ≤ dx) (hdxhi : dx ≤ 1 - lambda)
    (hdylo : lambda ≤ dy) (hdyhi : dy ≤ 1 - lambda)
    (hgate : 8 * (epsilon * N) ≤ lambda * (gamma * N))
    (hXN : (X : ℝ) ≤ N) (hYN : (Y : ℝ) ≤ N) (hXY : X ≤ Y)
    (hPX : P ≤ X) (hQY : Q ≤ Y)
    (hP : dx * X - 2 * (epsilon * N) ≤ P)
    (hQ : dy * Y - 2 * (epsilon * N) ≤ Q)
    (hinv : ResidualInvariant dx dy N (epsilon * N) (N - X) (N - Y))
    (hbudget : (N - X) + (N - Y) + F.order ≤
      (dx + dy + lambda) * N - 2 * (gamma * N) - 24 * (epsilon * N))
    (hlower : ∀ i, 2 ≤ F.size i) (hupper : ∀ i, F.size i ≤ small)
    (hsmall : (small : ℝ) ≤ epsilon * N / 2) :
    AppendixA2NumericData F small ⌈3 * (epsilon * N)⌉₊ ⌈(gamma + 3 * epsilon) * N⌉₊
      X Y P Q gamma epsilon N := by
  let error := epsilon * N
  let reserve := gamma * N
  let R : ℕ := ⌈3 * error⌉₊
  let S : ℕ := ⌈(gamma + 3 * epsilon) * N⌉₊
  have he : 0 ≤ error := by dsimp only [error]; linarith only [herror]
  have hN : 0 ≤ N := (Nat.cast_nonneg X).trans hXN
  have hx : 0 ≤ N - X := sub_nonneg.mpr hXN
  have hy : 0 ≤ N - Y := sub_nonneg.mpr hYN
  have hxN : N - X ≤ N := sub_le_self N (Nat.cast_nonneg X)
  have hyN : N - Y ≤ N := sub_le_self N (Nat.cast_nonneg Y)
  have hP' : dx * (N - (N - X)) - 2 * error ≤ P := by
    simpa only [sub_sub_cancel] using hP
  have hQ' : dy * (N - (N - Y)) - 2 * error ≤ Q := by
    simpa only [sub_sub_cancel] using hQ
  have hroot := root_slots_real N lambda dx dy error reserve (N - X) (N - Y) F.order P Q
    hN hlambda hlambdaHalf hdxlo hdxhi hdylo hdyhi hx hxN hy hyN hreserve hP' hQ' hbudget
  have hside := side_slots_real N lambda dx dy error reserve (N - X) (N - Y) F.order P Q
    hN hlambda he hdxlo hdxhi hdylo hdyhi hx hxN hy hyN hinv hP' hQ' hbudget
  simp only [sub_sub_cancel] at hside
  have horder : (0 : ℝ) ≤ F.order := Nat.cast_nonneg _
  have hminX : min (P : ℝ) Q ≤ X := (min_le_left _ _).trans (by exact_mod_cast hPX)
  have hminY : min (P : ℝ) Q ≤ Y := (min_le_right _ _).trans (by exact_mod_cast hQY)
  have hXreserve : reserve ≤ X := by
    have h := min_le_left (X : ℝ) (Y : ℝ)
    linarith only [hside, hminX, h, horder, he]
  have hYreserve : reserve ≤ Y := by
    have h := min_le_right (X : ℝ) (Y : ℝ)
    linarith only [hside, hminY, h, horder, he]
  have hR : (R : ℝ) ≤ 4 * error := by
    have hc := Nat.ceil_lt_add_one (show 0 ≤ 3 * error by positivity)
    change (⌈3 * error⌉₊ : ℝ) ≤ 4 * error
    linarith only [hc, herror]
  have hS : (S : ℝ) ≤ reserve + 7 / 2 * error := by
    have harg : (gamma + 3 * epsilon) * N = reserve + 3 * error := by dsimp [reserve, error]; ring
    have hc := Nat.ceil_lt_add_one (show 0 ≤ reserve + 3 * error by positivity)
    change (⌈(gamma + 3 * epsilon) * N⌉₊ : ℝ) ≤ reserve + 7 / 2 * error
    rw [harg]
    linarith only [hc, herror]
  have hRP : R ≤ P := by
    have hdx : 0 ≤ dx := hlambda.trans hdxlo
    have hm1 := mul_le_mul_of_nonneg_left hXreserve hdx
    have hm2 := mul_le_mul_of_nonneg_right hdxlo hreserve
    have hcast : (R : ℝ) ≤ P := by linarith only [hm1, hm2, hgate, hP, hR, he]
    exact_mod_cast hcast
  have hRQ : R ≤ Q := by
    have hdy : 0 ≤ dy := hlambda.trans hdylo
    have hm1 := mul_le_mul_of_nonneg_left hYreserve hdy
    have hm2 := mul_le_mul_of_nonneg_right hdylo hreserve
    have hcast : (R : ℝ) ≤ Q := by linarith only [hm1, hm2, hgate, hQ, hR, he]
    exact_mod_cast hcast
  have hb : 2 * b ≤ F.order := by
    calc
      2 * b = ∑ _i : Fin b, 2 := by simp [Nat.mul_comm]
      _ ≤ ∑ i, F.size i := Finset.sum_le_sum (fun i _ => hlower i)
  have hbReal : 2 * (b : ℝ) ≤ F.order := by exact_mod_cast hb
  refine {
    component_lower := hlower
    component_upper := hupper
    X_le_Y := hXY
    P_le_X := hPX
    rootReserve_le_P := hRP
    rootReserve_le_Q := hRQ
    rootReserve_le_sideReserve := ?_
    root_slots := ?_
    side_slots := ?_
    root_rounding := ?_
    side_rounding := Nat.le_ceil _
  }
  · apply Nat.ceil_mono
    nlinarith only [hreserve]
  · have hcast : (b : ℝ) + 2 * R ≤ P + Q := by linarith only [hroot, hbReal, hR]
    exact_mod_cast hcast
  · have hXYreal : (X : ℝ) ≤ Y := by exact_mod_cast hXY
    rw [min_eq_left hXYreal] at hside
    have hcast : (F.order : ℝ) + 2 * S + small ≤ min (P : ℝ) Q + X := by
      linarith only [hside, hS, hsmall, he]
    exact_mod_cast hcast
  · simpa only [mul_assoc] using Nat.le_ceil (3 * (epsilon * N))

end Erdos547b.ZhaoSourcePartThreeAppendixData

#print axioms Erdos547b.ZhaoSourcePartThreeAppendixData.appendixData_of_residual
