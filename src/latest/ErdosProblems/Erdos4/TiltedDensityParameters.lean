import ErdosProblems.Erdos4.TiltedCutoffParameters
import ErdosProblems.Erdos4.TiltedDensity
import ErdosProblems.Erdos4.FGKMTOuterParameters

/-! The actual tilted density is bounded by a constant times `t log₂ x / log x`. -/

namespace Erdos4.Tilted

open Filter FGKMT

noncomputable def tiltTruncation (x : ℕ) : ℕ := ⌊Real.exp (outerScale x)⌋₊

noncomputable def primeDensity (x : ℕ) : ℝ :=
  primeSurvival (coordinateValue (smallCutoff x) (sieveCutoff x)) (tiltExponent x)

theorem primeDensity_pos (x : ℕ) : 0 < primeDensity x :=
  primeSurvival_pos _ _

theorem eventually_tiltTruncation_bounds :
    ∀ᶠ x : ℕ in atTop,
      2 ≤ smallCutoff x ∧ smallCutoff x ≤ tiltTruncation x ∧ tiltTruncation x ≤ sieveCutoff x ∧
      outerScale x / 2 ≤ Real.log (tiltTruncation x : ℝ) ∧
      Real.log (tiltTruncation x : ℝ) ≤ outerScale x ∧
      tiltExponent x * Real.log (tiltTruncation x : ℝ) ≤ 1 := by
  filter_upwards [eventually_outerScale_bounds, eventually_smallCutoff_bounds,
    tiltScale_tendsto.eventually (eventually_ge_atTop 2),
    log_tendsto.eventually (eventually_ge_atTop (2 * Real.log 64)),
    eventually_iterated_log_power_le 1 200 (by norm_num : (0 : ℝ) < 1 / 2),
    eventually_ge_atTop 1] with x hb hw ht hL64 hdom hx
  let L := Real.log (x : ℝ)
  let l := Real.log L
  let s := outerScale x
  have hLpos : 0 < L := by have hh := hb.1; change 16 ≤ L at hh; linarith
  have htpos : 0 < tiltScale x := by linarith
  have hxpos : (0 : ℝ) < x := by exact_mod_cast hx
  have hroot : 4 ≤ Real.sqrt L := by
    have hh := Real.sq_sqrt hLpos.le
    have h0 := Real.sqrt_nonneg L
    have hhL := hb.1
    change 16 ≤ L at hhL
    nlinarith
  have hs2 : 2 ≤ s := by have hh := hb.2.2.2.2.1; change Real.sqrt L ≤ s at hh; linarith
  have hZ := floor_exp_log_bounds hs2
  change 2 ≤ tiltTruncation x ∧ s / 2 ≤ Real.log (tiltTruncation x : ℝ) ∧
    Real.log (tiltTruncation x : ℝ) ≤ s at hZ
  have hWpos : (0 : ℝ) < smallCutoff x := by exact_mod_cast (show 0 < smallCutoff x by omega)
  have hZpos : (0 : ℝ) < tiltTruncation x := by exact_mod_cast (show 0 < tiltTruncation x by omega)
  have hdom' : 200 * l ≤ s := by
    have hh : 200 * l ≤ Real.sqrt L := by simpa only [pow_one, Real.sqrt_eq_rpow] using hdom
    exact hh.trans hb.2.2.2.2.1
  have hWZ : smallCutoff x ≤ tiltTruncation x := by
    have hlogW := hw.2.2.2.2.2.2.1
    change Real.log (smallCutoff x : ℝ) ≤ 100 * l at hlogW
    have hlogs : Real.log (smallCutoff x : ℝ) ≤ Real.log (tiltTruncation x : ℝ) := by linarith [hZ.2.1]
    exact_mod_cast (Real.log_le_log_iff hWpos hZpos).mp hlogs
  have hsHalf : s ≤ L / 2 := by
    change L / tiltScale x ≤ L / 2
    exact div_le_div_of_nonneg_left hLpos.le (by norm_num) ht
  have hZupper : (tiltTruncation x : ℝ) ≤ (x : ℝ) / 64 := by
    calc
      _ ≤ Real.exp s := Nat.floor_le (Real.exp_pos s).le
      _ ≤ Real.exp (L - Real.log 64) := by
        apply Real.exp_le_exp.mpr
        change 2 * Real.log 64 ≤ L at hL64
        linarith
      _ = _ := by rw [Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 64), Real.exp_log hxpos]
  have hZB : tiltTruncation x ≤ sieveCutoff x := by
    have hh : (64 : ℝ) * tiltTruncation x ≤ x := by linarith
    have hhN : 64 * tiltTruncation x ≤ x := by exact_mod_cast hh
    unfold sieveCutoff
    omega
  have hτs : tiltExponent x * s = 1 := by
    change tiltScale x / L * (L / tiltScale x) = 1
    field_simp [hLpos.ne', htpos.ne']
  have hcut : tiltExponent x * Real.log (tiltTruncation x : ℝ) ≤ 1 := by
    exact (mul_le_mul_of_nonneg_left hZ.2.2 hb.2.2.2.2.2.2.1.le).trans_eq hτs
  exact ⟨hw.1, hWZ, hZB, hZ.2.1, hZ.2.2, hcut⟩

theorem exists_primeDensity_bounds :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ x : ℕ in atTop,
      c * Real.log (Real.log (x : ℝ)) / Real.log (x : ℝ) ≤ primeDensity x ∧
      primeDensity x ≤ C * tiltScale x * Real.log (Real.log (x : ℝ)) / Real.log (x : ℝ) := by
  obtain ⟨c, C, hc, hC, hbound⟩ := exists_tilted_density_bounds
  refine ⟨c, 200 * C, hc, by positivity, ?_⟩
  filter_upwards [eventually_tiltTruncation_bounds, eventually_smallCutoff_bounds,
    eventually_outerScale_bounds] with x hZ hw hb
  let L := Real.log (x : ℝ)
  let l := Real.log L
  let s := outerScale x
  have hLpos : 0 < L := by have hh := hb.1; change 16 ≤ L at hh; linarith
  have hlpos : 0 < l := by have hh := hb.2.1; change 1 ≤ l at hh; linarith
  have htpos : 0 < tiltScale x := by linarith [hb.2.2.1]
  have hspos : 0 < s := div_pos hLpos htpos
  have hτ := hb.2.2.2.2.2.2.1.le
  have hd := hbound (smallCutoff x) (tiltTruncation x) (sieveCutoff x) hZ.1 hZ.2.1 hZ.2.2.1
    (tiltExponent x) hτ hZ.2.2.2.2.2
  have hB2 : 2 ≤ sieveCutoff x := hw.1.trans hw.2.1
  have hlogB : 0 < Real.log (sieveCutoff x : ℝ) := Real.log_pos (by exact_mod_cast hB2)
  have hlogW : 0 < Real.log (smallCutoff x : ℝ) := Real.log_pos (by exact_mod_cast hw.1)
  have hlogZ : 0 < Real.log (tiltTruncation x : ℝ) :=
    Real.log_pos (by exact_mod_cast (hZ.1.trans hZ.2.1))
  have hBL : Real.log (sieveCutoff x : ℝ) ≤ L := Real.log_le_log
    (by exact_mod_cast (show 0 < sieveCutoff x by omega))
    (by exact_mod_cast Nat.div_le_self x 64)
  constructor
  · calc
      _ ≤ c * Real.log (smallCutoff x : ℝ) / L :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hw.2.2.2.2.2.1 hc.le) hLpos.le
      _ ≤ c * Real.log (smallCutoff x : ℝ) / Real.log (sieveCutoff x : ℝ) :=
        div_le_div_of_nonneg_left (mul_nonneg hc.le hlogW.le) hlogB hBL
      _ ≤ _ := hd.1
  · calc
      _ ≤ C * Real.log (smallCutoff x : ℝ) / Real.log (tiltTruncation x : ℝ) := hd.2
      _ ≤ C * (100 * l) / Real.log (tiltTruncation x : ℝ) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hw.2.2.2.2.2.2.1 hC.le) hlogZ.le
      _ ≤ C * (100 * l) / (s / 2) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hZ.2.2.2.1
      _ = _ := by dsimp [s, outerScale, l, L]; field_simp; ring

end Erdos4.Tilted
