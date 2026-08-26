/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierPinnedForcedModulusFibers
import ErdosProblems.Erdos4b.GeneralFourierPinnedDistributionRange

/-!
# The enlarged source modulus remains below the fixed prime-distribution level

One forced prime at most `Y` adds at most `log Y` to the logarithmic
radius. With the source scales, the radius is below the two-fifths
endpoint cutoff once the ambient logarithm is at least 160.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators

def pinnedSourceForcedProductRadius (K : ℕ) (V : ℝ) (Y : ℕ) : ℕ :=
  pinnedSourceProductRadius K V (Real.log Y) * Y

theorem pinnedSourceForcedProductRadius_pos (K : ℕ) (V : ℝ) {Y : ℕ} (hY : 0 < Y) :
    0 < pinnedSourceForcedProductRadius K V Y :=
  Nat.mul_pos (pinnedSourceProductRadius_pos K V (Real.log Y)) hY

theorem log_pinnedSourceForcedProductRadius_le
    {K : ℕ} (hK : 0 < K) {V : ℝ} {Y : ℕ} (hV : 0 ≤ V) (hY : 0 < Y)
    (hsmall : (K : ℝ) * Real.log Y ≤ V / 40) :
    Real.log (pinnedSourceForcedProductRadius K V Y) ≤ 4 + 11 * V / 40 := by
  have hY0 : (0 : ℝ) < Y := by exact_mod_cast hY
  have hLE : 0 ≤ Real.log Y := Real.log_nonneg (by exact_mod_cast hY)
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hLEK : Real.log Y ≤ (K : ℝ) * Real.log Y := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hK1 hLE
  have hLEsmall : Real.log Y ≤ V / 40 := hLEK.trans hsmall
  have hRpos : (0 : ℝ) < pinnedSourceProductRadius K V (Real.log Y) := by
    exact_mod_cast pinnedSourceProductRadius_pos K V (Real.log Y)
  rw [pinnedSourceForcedProductRadius, Nat.cast_mul, Real.log_mul hRpos.ne' hY0.ne']
  have hRlog := log_pinnedSourceProductRadius_le K hV hLE hsmall
  linarith

theorem pinnedSourceForcedProductRadius_le_twoFifthsCutoff
    {K : ℕ} (hK : 0 < K) {V : ℝ} {Y x : ℕ} (hV : 160 ≤ V) (hY : 0 < Y)
    (hsmall : (K : ℝ) * Real.log Y ≤ V / 40) (hx : 0 < x)
    (hlog : 3 * V / 4 ≤ Real.log x) :
    pinnedSourceForcedProductRadius K V Y ≤ BoundedGaps.Maynard.modulusCutoff (2 / 5) x := by
  have hxR : (0 : ℝ) < x := by exact_mod_cast hx
  have hRpos : (0 : ℝ) < pinnedSourceForcedProductRadius K V Y := by
    exact_mod_cast pinnedSourceForcedProductRadius_pos K V hY
  have hRlog := log_pinnedSourceForcedProductRadius_le hK (by linarith) hY hsmall
  apply (Nat.le_floor_iff (Real.rpow_nonneg (Nat.cast_nonneg x) (2 / 5))).mpr
  rw [Real.rpow_def_of_pos hxR]
  apply (Real.log_le_iff_le_exp hRpos).mp
  linarith

theorem pinnedSourceForcedProductRadius_le_endpoint
    {K : ℕ} (hK : 0 < K) {V : ℝ} {Y x : ℕ} (hV : 160 ≤ V) (hY : 0 < Y)
    (hsmall : (K : ℝ) * Real.log Y ≤ V / 40) (hx : 0 < x)
    (hlog : 3 * V / 4 ≤ Real.log x) : pinnedSourceForcedProductRadius K V Y ≤ x := by
  apply (pinnedSourceForcedProductRadius_le_twoFifthsCutoff hK hV hY hsmall hx hlog).trans
  have hfloor : (BoundedGaps.Maynard.modulusCutoff (2 / 5) x : ℝ) ≤
      Real.rpow (x : ℝ) (2 / 5 : ℝ) := Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg x) _)
  exact_mod_cast hfloor.trans
    (Real.rpow_le_self_of_one_le (by exact_mod_cast hx) (by norm_num : (2 / 5 : ℝ) ≤ 1))

theorem pinnedForcedDivisorModulus_le_source_radius
    {K : ℕ} {J : Type*} (S : Finset J) (F : J → Fin K → ℝ → ℝ) (G : ℝ → ℝ)
    (h : Fin K) (P : Finset ℕ) (hP : ∀ r ∈ P, r.Prime)
    {V : ℝ} {Y p : ℕ} (hV : 0 < V) (hY : 1 < Y) (hp : p.Prime) (hpy : p ≤ Y)
    (hFsupport : ∀ j ∈ S, ∀ u : Fin K → ℝ,
      (∀ i, 0 ≤ u i) → (∀ i, F j i (u i) ≠ 0) → (∑ i, u i) ≤ (1 : ℝ) / 10)
    (hGsupport : ∀ t, 0 ≤ t → G t ≠ 0 → t ≤ 1)
    (d : (PinnedShiftIndex h ⊕ PinnedShiftIndex h) → Bool → ℕ)
    (hd : d ∈ rawDoubledCutoffDivisorTuples (PinnedShiftIndex h) P)
    (hne : pinnedSourceFlatCoefficient S F G h V (Real.log Y) (fun i ↦ d i false) *
      pinnedSourceFlatCoefficient S F G h V (Real.log Y) (fun i ↦ d i true) ≠ 0) :
    pinnedForcedDivisorModulus h (p, d) ≤ pinnedSourceForcedProductRadius K V Y := by
  have hQpos := (pinnedFlatDivisorModulus_squarefree h P hP d
    ((mem_rawDoubledCutoffDivisorTuples P hP d).mp hd)).ne_zero.bot_lt
  have hQ := pinnedFlatDivisorModulus_le_source_product_radii S F G h hV
    (Real.log_pos (by exact_mod_cast hY)) hFsupport hGsupport d hne
  exact (Nat.le_of_dvd (Nat.mul_pos hQpos hp.pos)
    (Nat.lcm_dvd_mul (pinnedFlatDivisorModulus h d) p)).trans (Nat.mul_le_mul hQ hpy)

end

end Erdos4b
