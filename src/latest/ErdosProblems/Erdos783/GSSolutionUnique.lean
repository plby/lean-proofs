import ErdosProblems.Erdos783.GSSolution

open MeasureTheory Set

namespace Erdos783

noncomputable section

/-- The normalized Volterra solution is unique on the nonnegative axis.
The proof applies the same unit-interval maximum argument to the absolute
difference of two solutions. -/
theorem gs_solution_unique
    {chi sigma tau : ℝ → ℝ} (hchi : IsGSKernel chi)
    (hsigma : IsGSSolution chi sigma) (htau : IsGSSolution chi tau) :
    ∀ u : ℝ, 0 ≤ u → sigma u = tau u := by
  let d : ℝ → ℝ := fun u ↦ sigma u - tau u
  have hdcont : ContinuousOn d (Ici (0 : ℝ)) := hsigma.1.sub htau.1
  have hdeq : ∀ u : ℝ, 1 ≤ u →
      u * d u = ∫ t : ℝ in 0..u, chi t * d (u - t) := by
    intro u hu
    have hs := hsigma.2.2 u hu
    have ht := htau.2.2 u hu
    have hsub : ContinuousOn (fun t : ℝ ↦ u - t) (Icc 0 u) :=
      continuousOn_const.sub continuousOn_id
    have hmap : MapsTo (fun t : ℝ ↦ u - t) (Icc 0 u) (Icc 0 u) := by
      intro t hmem
      exact ⟨sub_nonneg.mpr hmem.2, sub_le_self _ hmem.1⟩
    have hsigInt : IntervalIntegrable
        (fun t : ℝ ↦ chi t * sigma (u - t)) volume 0 u := by
      exact (hchi.1 0 u).mul_continuousOn (by
        rw [uIcc_of_le (zero_le_one.trans hu)]
        exact hsigma.1.comp hsub (fun _t ht ↦ (hmap ht).1))
    have htauInt : IntervalIntegrable
        (fun t : ℝ ↦ chi t * tau (u - t)) volume 0 u := by
      exact (hchi.1 0 u).mul_continuousOn (by
        rw [uIcc_of_le (zero_le_one.trans hu)]
        exact htau.1.comp hsub (fun _t ht ↦ (hmap ht).1))
    dsimp only [d]
    rw [show (fun t : ℝ ↦ chi t * (sigma (u - t) - tau (u - t))) =
        fun t ↦ chi t * sigma (u - t) - chi t * tau (u - t) by
      funext t; ring,
      intervalIntegral.integral_sub hsigInt htauInt]
    linarith
  have hstep : ∀ n : ℕ, 1 ≤ n →
      ∀ u : ℝ, 0 ≤ u → u ≤ n → d u = 0 := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base =>
        intro u hu0 hu1
        dsimp only [d]
        rw [hsigma.2.1 u hu0 (by simpa using hu1),
          htau.2.1 u hu0 (by simpa using hu1)]
        ring
    | succ n hn ih =>
        intro u hu0 huSucc
        by_cases hun : u ≤ n
        · exact ih u hu0 hun
        · have hnu : (n : ℝ) < u := lt_of_not_ge hun
          have hnu' : (n : ℝ) ≤ u := hnu.le
          have hn0 : (0 : ℝ) ≤ n := by positivity
          have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
          have hcontAbs : ContinuousOn (fun v ↦ |d v|) (Icc (n : ℝ) u) :=
            (hdcont.mono (fun x hx ↦ hn0.trans hx.1)).abs
          obtain ⟨v, hv, hmax⟩ := isCompact_Icc.exists_isMaxOn
            (nonempty_Icc.mpr hnu') hcontAbs
          have huMem : u ∈ Icc (n : ℝ) u := ⟨hnu', le_rfl⟩
          have hdu : |d u| ≤ |d v| := hmax huMem
          have hv0 : 0 ≤ v := hn0.trans hv.1
          let a : ℝ := v - n
          have ha0 : 0 ≤ a := sub_nonneg.mpr hv.1
          have hav : a ≤ v := by dsimp only [a]; linarith
          have ha1 : a ≤ 1 := by
            have hvle : v ≤ (n : ℝ) + 1 := by
              exact hv.2.trans (by exact_mod_cast huSucc)
            dsimp only [a]
            linarith
          have hsub : ContinuousOn (fun t : ℝ ↦ v - t) (Icc 0 v) :=
            continuousOn_const.sub continuousOn_id
          have hmap : MapsTo (fun t : ℝ ↦ v - t) (Icc 0 v) (Icc 0 u) := by
            intro t ht
            exact ⟨sub_nonneg.mpr ht.2, (sub_le_self _ ht.1).trans hv.2⟩
          have hdsub : ContinuousOn (fun t : ℝ ↦ d (v - t)) (uIcc 0 v) := by
            rw [uIcc_of_le hv0]
            exact hdcont.comp hsub (fun _t ht ↦ (hmap ht).1)
          have hfull : IntervalIntegrable
              (fun t : ℝ ↦ chi t * d (v - t)) volume 0 v :=
            (hchi.1 0 v).mul_continuousOn hdsub
          have hleft : IntervalIntegrable
              (fun t : ℝ ↦ chi t * d (v - t)) volume 0 a := by
            apply hfull.mono_set
            rw [uIcc_of_le hv0, uIcc_of_le ha0]
            exact Icc_subset_Icc le_rfl hav
          have hright : IntervalIntegrable
              (fun t : ℝ ↦ chi t * d (v - t)) volume a v := by
            apply hfull.mono_set
            rw [uIcc_of_le hv0, uIcc_of_le hav]
            exact Icc_subset_Icc ha0 le_rfl
          have hrightZero :
              (∫ t : ℝ in a..v, chi t * d (v - t)) = 0 := by
            rw [show (∫ t : ℝ in a..v, chi t * d (v - t)) =
                ∫ _t : ℝ in a..v, (0 : ℝ) by
              apply intervalIntegral.integral_congr
              intro t ht
              rw [uIcc_of_le hav] at ht
              have harg0 : 0 ≤ v - t := sub_nonneg.mpr ht.2
              have hargn : v - t ≤ n := by
                dsimp only [a] at ht
                linarith [ht.1]
              change chi t * d (v - t) = 0
              rw [ih (v - t) harg0 hargn, mul_zero]]
            simp
          have hleftNorm :
              |(∫ t : ℝ in 0..a, chi t * d (v - t))| ≤ a * |d v| := by
            have h := intervalIntegral.norm_integral_le_of_norm_le_const
              (C := |d v|) (f := fun t : ℝ ↦ chi t * d (v - t)) (by
                intro t ht
                rw [uIoc_of_le ha0] at ht
                have ht' : t ∈ Icc (0 : ℝ) a := ⟨ht.1.le, ht.2⟩
                have hchiOne : chi t = 1 :=
                  hchi.2.2.2 t ht'.1 (ht'.2.trans ha1)
                have harg : v - t ∈ Icc (n : ℝ) u := by
                  constructor
                  · dsimp only [a] at ht'
                    linarith [ht'.2]
                  · exact (sub_le_self _ ht'.1).trans hv.2
                rw [hchiOne, one_mul, Real.norm_eq_abs]
                exact hmax harg)
            simpa [abs_of_nonneg ha0, mul_comm] using h
          have hsplit := intervalIntegral.integral_add_adjacent_intervals
            hleft hright
          have heq := hdeq v (hn1.trans hv.1)
          have hmain : v * |d v| ≤ a * |d v| := by
            calc
              v * |d v| = |v * d v| := by
                rw [abs_mul, abs_of_nonneg hv0]
              _ = |(∫ t : ℝ in 0..v, chi t * d (v - t))| := by
                rw [heq]
              _ = |(∫ t : ℝ in 0..a, chi t * d (v - t))| := by
                rw [← hsplit, hrightZero, add_zero]
              _ ≤ a * |d v| := hleftNorm
          have hdv : d v = 0 := by
            have hnpos : (0 : ℝ) < n := zero_lt_one.trans_le hn1
            have habs : |d v| = 0 := by
              dsimp only [a] at hmain
              nlinarith [abs_nonneg (d v)]
            exact abs_eq_zero.mp habs
          exact abs_eq_zero.mp (le_antisymm (hdu.trans_eq (by rw [hdv, abs_zero]))
            (abs_nonneg _))
  intro u hu0
  let n : ℕ := max 1 ⌈u⌉₊
  have hn1 : 1 ≤ n := le_max_left _ _
  have hun : u ≤ n := (Nat.le_ceil u).trans (by
    exact_mod_cast (le_max_right 1 ⌈u⌉₊))
  have := hstep n hn1 u hu0 hun
  dsimp only [d] at this
  linarith

end

end Erdos783
