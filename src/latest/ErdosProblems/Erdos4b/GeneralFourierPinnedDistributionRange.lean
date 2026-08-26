/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierPinnedSourceDistribution
import ErdosProblems.Erdos4b.GeneralFourierMassGrowth

/-!
# The source modulus radius lies below a fixed prime-distribution level

The first simplex width is `1/10`. The companion logarithm condition
`K * LE ≤ V / 40` makes the logarithm of the squared product radius at
most `4 + V / 4`. An endpoint with logarithm at least `3V/4` then
admits the fixed level `2/5` once `V ≥ 80`.
-/

namespace Erdos4b

noncomputable section

def pinnedSourceProductRadius (K : ℕ) (V LE : ℝ) : ℕ :=
  (⌈Real.exp ((1 / 10 : ℝ) * V)⌉₊ * ⌈Real.exp ((K : ℝ) * LE)⌉₊) ^ 2

theorem pinnedSourceProductRadius_pos (K : ℕ) (V LE : ℝ) :
    0 < pinnedSourceProductRadius K V LE := by
  unfold pinnedSourceProductRadius
  exact pow_pos (Nat.mul_pos (Nat.ceil_pos.mpr (Real.exp_pos _))
    (Nat.ceil_pos.mpr (Real.exp_pos _))) 2

theorem log_pinnedSourceProductRadius_le
    (K : ℕ) {V LE : ℝ} (hV : 0 ≤ V) (hLE : 0 ≤ LE) (hsmall : (K : ℝ) * LE ≤ V / 40) :
    Real.log (pinnedSourceProductRadius K V LE) ≤ 4 + V / 4 := by
  have hDpos : (0 : ℝ) < ⌈Real.exp ((1 / 10 : ℝ) * V)⌉₊ := by
    exact_mod_cast Nat.ceil_pos.mpr (Real.exp_pos ((1 / 10 : ℝ) * V))
  have hEpos : (0 : ℝ) < ⌈Real.exp ((K : ℝ) * LE)⌉₊ := by
    exact_mod_cast Nat.ceil_pos.mpr (Real.exp_pos ((K : ℝ) * LE))
  have hD := log_ceil_exp_le_add_one (by positivity : 0 ≤ (1 / 10 : ℝ) * V)
  have hE := log_ceil_exp_le_add_one (by positivity : 0 ≤ (K : ℝ) * LE)
  simp only [pinnedSourceProductRadius, Nat.cast_pow, Nat.cast_mul, Real.log_pow,
    Real.log_mul hDpos.ne' hEpos.ne', Nat.cast_ofNat]
  linarith

theorem pinnedSourceProductRadius_le_twoFifthsCutoff
    (K : ℕ) {V LE : ℝ} {x : ℕ} (hV : 80 ≤ V) (hLE : 0 ≤ LE)
    (hsmall : (K : ℝ) * LE ≤ V / 40) (hx : 0 < x) (hlog : 3 * V / 4 ≤ Real.log x) :
    pinnedSourceProductRadius K V LE ≤ BoundedGaps.Maynard.modulusCutoff (2 / 5) x := by
  have hxR : (0 : ℝ) < x := by exact_mod_cast hx
  have hRpos : (0 : ℝ) < pinnedSourceProductRadius K V LE := by
    exact_mod_cast pinnedSourceProductRadius_pos K V LE
  have hRlog := log_pinnedSourceProductRadius_le K (by linarith) hLE hsmall
  apply (Nat.le_floor_iff (Real.rpow_nonneg (Nat.cast_nonneg x) (2 / 5))).mpr
  rw [Real.rpow_def_of_pos hxR]
  apply (Real.log_le_iff_le_exp hRpos).mp
  linarith

theorem pinnedSourceProductRadius_le_endpoint
    (K : ℕ) {V LE : ℝ} {x : ℕ} (hV : 80 ≤ V) (hLE : 0 ≤ LE)
    (hsmall : (K : ℝ) * LE ≤ V / 40) (hx : 0 < x) (hlog : 3 * V / 4 ≤ Real.log x) :
    pinnedSourceProductRadius K V LE ≤ x := by
  apply (pinnedSourceProductRadius_le_twoFifthsCutoff K hV hLE hsmall hx hlog).trans
  have hfloor : (BoundedGaps.Maynard.modulusCutoff (2 / 5) x : ℝ) ≤
      Real.rpow (x : ℝ) (2 / 5 : ℝ) := Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg x) _)
  exact_mod_cast hfloor.trans
    (Real.rpow_le_self_of_one_le (by exact_mod_cast hx) (by norm_num : (2 / 5 : ℝ) ≤ 1))

theorem primeLevelWitness_pinnedSourceEndpointErrorBound_le_twoFifths
    {K : ℕ} {J : Type*} (S : Finset J) (F : J → Fin K → ℝ → ℝ) (G : ℝ → ℝ)
    (h : Fin K) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {V LE C₀ exponent C : ℝ} {X₀ x : ℕ} (hV : 80 ≤ V) (hLE : 0 < LE)
    (hsmall : (K : ℝ) * LE ≤ V / 40) (hxpos : 0 < x) (hlog : 3 * V / 4 ≤ Real.log x)
    (hFsupport : ∀ j ∈ S, ∀ u : Fin K → ℝ,
      (∀ i, 0 ≤ u i) → (∀ i, F j i (u i) ≠ 0) → (∑ i, u i) ≤ (1 : ℝ) / 10)
    (hGsupport : ∀ t, 0 ≤ t → G t ≠ 0 → t ≤ 1) (hC₀ : 0 ≤ C₀)
    (hcoef : ∀ v, ‖pinnedSourceFlatCoefficient S F G h V LE v‖ ≤ C₀)
    (hw : BoundedGaps.Maynard.PrimeLevelWitness (2 / 5) exponent C X₀) (hx : X₀ ≤ x) :
    pinnedSourceEndpointErrorBound S F G h P x V LE ≤
      C₀ ^ 2 * pinnedFlatTauDiscrepancyBound K C exponent x (pinnedSourceProductRadius K V LE) := by
  apply primeLevelWitness_pinnedSourceEndpointErrorBound_le S F G h P hP
    (by linarith : 0 < V) hLE hFsupport hGsupport hC₀ hcoef hw hx
  · exact (pinnedSourceProductRadius_le_endpoint K hV hLE.le hsmall hxpos hlog).trans
      (Nat.le_succ x)
  · exact pinnedSourceProductRadius_le_twoFifthsCutoff K hV hLE.le hsmall hxpos hlog

end

end Erdos4b
