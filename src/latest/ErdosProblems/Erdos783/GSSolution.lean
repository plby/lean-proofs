import ErdosProblems.Erdos783.GSKernel

open MeasureTheory Set

namespace Erdos783

noncomputable section

def IsGSSolution (chi sigma : ℝ → ℝ) : Prop :=
  ContinuousOn sigma (Ici (0 : ℝ)) ∧
  (∀ u : ℝ, 0 ≤ u → u ≤ 1 → sigma u = 1) ∧
  (∀ u : ℝ, 1 ≤ u →
    u * sigma u = ∫ t : ℝ in 0..u, chi t * sigma (u - t))

/-- Every nonnegative Granville--Soundararajan kernel has its normalized
Volterra solution in `[0,1]`.  The proof is a unit-interval induction: on
the new interval `[n,n+1]`, compact extrema and the identity `chi = 1` on
`[0,1]` leave a positive factor `n` against any putative excursion. -/
theorem gs_solution_mem_Icc
    {chi sigma : ℝ → ℝ} (hchi : IsGSKernel chi)
    (hsigma : IsGSSolution chi sigma) :
    ∀ u : ℝ, 0 ≤ u → sigma u ∈ Icc (0 : ℝ) 1 := by
  have hstep : ∀ n : ℕ, 1 ≤ n →
      ∀ u : ℝ, 0 ≤ u → u ≤ n → sigma u ∈ Icc (0 : ℝ) 1 := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base =>
        intro u hu0 hu1
        rw [hsigma.2.1 u hu0 (by simpa using hu1)]
        exact ⟨zero_le_one, le_rfl⟩
    | succ n hn ih =>
        intro u hu0 huSucc
        by_cases hun : u ≤ n
        · exact ih u hu0 hun
        · have hnu : (n : ℝ) < u := lt_of_not_ge hun
          have hnu' : (n : ℝ) ≤ u := hnu.le
          have hn0 : (0 : ℝ) ≤ n := by positivity
          have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
          have hu1 : 1 ≤ u := hn1.trans hnu'
          have hcont : ContinuousOn sigma (Icc (n : ℝ) u) :=
            hsigma.1.mono (fun x hx ↦ hn0.trans hx.1)
          have hnonempty : (Icc (n : ℝ) u).Nonempty :=
            nonempty_Icc.mpr hnu'
          obtain ⟨vmin, hvmin, hmin⟩ :=
            isCompact_Icc.exists_isMinOn hnonempty hcont
          obtain ⟨vmax, hvmax, hmax⟩ :=
            isCompact_Icc.exists_isMaxOn hnonempty hcont
          have hfullInt (v : ℝ) (hv : v ∈ Icc (n : ℝ) u) :
              IntervalIntegrable (fun t : ℝ ↦ chi t * sigma (v - t))
                volume 0 v := by
            have hv0 : 0 ≤ v := hn0.trans hv.1
            have hsub : ContinuousOn (fun t : ℝ ↦ v - t) (Icc 0 v) :=
              continuousOn_const.sub continuousOn_id
            have hmap : MapsTo (fun t : ℝ ↦ v - t) (Icc 0 v) (Icc 0 u) := by
              intro t ht
              exact ⟨sub_nonneg.mpr ht.2,
                (sub_le_self _ ht.1).trans hv.2⟩
            have hs : ContinuousOn (fun t : ℝ ↦ sigma (v - t)) (uIcc 0 v) := by
              rw [uIcc_of_le hv0]
              exact (hsigma.1.mono Icc_subset_Ici_self).comp hsub hmap
            exact (hchi.1 0 v).mul_continuousOn hs
          have hlower : 0 ≤ sigma u := by
            by_contra hnot
            have hsuNeg : sigma u < 0 := lt_of_not_ge hnot
            have huMem : u ∈ Icc (n : ℝ) u := ⟨hnu', le_rfl⟩
            have hmNeg : sigma vmin < 0 := (hmin huMem).trans_lt hsuNeg
            let a : ℝ := vmin - n
            have hvmin0 : 0 ≤ vmin := hn0.trans hvmin.1
            have ha0 : 0 ≤ a := sub_nonneg.mpr hvmin.1
            have ha1 : a ≤ 1 := by
              dsimp only [a]
              have hvle : vmin ≤ (n : ℝ) + 1 := by
                exact hvmin.2.trans (by exact_mod_cast huSucc)
              exact sub_le_iff_le_add.mpr (by linarith)
            have hav : a ≤ vmin := by dsimp only [a]; linarith
            have hfull := hfullInt vmin hvmin
            have hleft : IntervalIntegrable
                (fun t : ℝ ↦ chi t * sigma (vmin - t)) volume 0 a := by
              apply hfull.mono_set
              rw [uIcc_of_le hvmin0, uIcc_of_le ha0]
              exact Icc_subset_Icc le_rfl hav
            have hright : IntervalIntegrable
                (fun t : ℝ ↦ chi t * sigma (vmin - t)) volume a vmin := by
              apply hfull.mono_set
              rw [uIcc_of_le hvmin0, uIcc_of_le hav]
              exact Icc_subset_Icc ha0 le_rfl
            have hleftLower :
                a * sigma vmin ≤
                  ∫ t : ℝ in 0..a, chi t * sigma (vmin - t) := by
              calc
                a * sigma vmin =
                    ∫ _t : ℝ in 0..a, sigma vmin := by simp
                _ ≤ ∫ t : ℝ in 0..a,
                    chi t * sigma (vmin - t) := by
                  apply intervalIntegral.integral_mono_on ha0
                    intervalIntegrable_const hleft
                  intro t ht
                  have hchiOne : chi t = 1 :=
                    hchi.2.2.2 t ht.1 (ht.2.trans ha1)
                  have harg : vmin - t ∈ Icc (n : ℝ) u := by
                    constructor
                    · dsimp only [a] at ht
                      linarith [ht.2]
                    · exact (sub_le_self _ ht.1).trans hvmin.2
                  rw [hchiOne, one_mul]
                  exact hmin harg
            have hrightLower :
                0 ≤ ∫ t : ℝ in a..vmin,
                  chi t * sigma (vmin - t) := by
              apply intervalIntegral.integral_nonneg hav
              intro t ht
              have harg0 : 0 ≤ vmin - t := sub_nonneg.mpr ht.2
              have hargn : vmin - t ≤ n := by
                dsimp only [a] at ht
                linarith [ht.1]
              exact mul_nonneg (hchi.2.1 t (ha0.trans ht.1))
                (ih (vmin - t) harg0 hargn).1
            have hsplit := intervalIntegral.integral_add_adjacent_intervals
              hleft hright
            have heq := hsigma.2.2 vmin (hn1.trans hvmin.1)
            have hmain : a * sigma vmin ≤ vmin * sigma vmin := by
              rw [heq, ← hsplit]
              linarith
            dsimp only [a] at hmain
            nlinarith
          have hupper : sigma u ≤ 1 := by
            by_contra hnot
            have hsuLarge : 1 < sigma u := lt_of_not_ge hnot
            have huMem : u ∈ Icc (n : ℝ) u := ⟨hnu', le_rfl⟩
            have hMLarge : 1 < sigma vmax := hsuLarge.trans_le (hmax huMem)
            let a : ℝ := vmax - n
            have hvmax0 : 0 ≤ vmax := hn0.trans hvmax.1
            have ha0 : 0 ≤ a := sub_nonneg.mpr hvmax.1
            have ha1 : a ≤ 1 := by
              dsimp only [a]
              have hvle : vmax ≤ (n : ℝ) + 1 := by
                exact hvmax.2.trans (by exact_mod_cast huSucc)
              exact sub_le_iff_le_add.mpr (by linarith)
            have hav : a ≤ vmax := by dsimp only [a]; linarith
            have hfull := hfullInt vmax hvmax
            have hleft : IntervalIntegrable
                (fun t : ℝ ↦ chi t * sigma (vmax - t)) volume 0 a := by
              apply hfull.mono_set
              rw [uIcc_of_le hvmax0, uIcc_of_le ha0]
              exact Icc_subset_Icc le_rfl hav
            have hright : IntervalIntegrable
                (fun t : ℝ ↦ chi t * sigma (vmax - t)) volume a vmax := by
              apply hfull.mono_set
              rw [uIcc_of_le hvmax0, uIcc_of_le hav]
              exact Icc_subset_Icc ha0 le_rfl
            have hleftUpper :
                (∫ t : ℝ in 0..a, chi t * sigma (vmax - t)) ≤
                  a * sigma vmax := by
              calc
                (∫ t : ℝ in 0..a,
                    chi t * sigma (vmax - t)) ≤
                    ∫ _t : ℝ in 0..a, sigma vmax := by
                  apply intervalIntegral.integral_mono_on ha0 hleft
                    intervalIntegrable_const
                  intro t ht
                  have hchiOne : chi t = 1 :=
                    hchi.2.2.2 t ht.1 (ht.2.trans ha1)
                  have harg : vmax - t ∈ Icc (n : ℝ) u := by
                    constructor
                    · dsimp only [a] at ht
                      linarith [ht.2]
                    · exact (sub_le_self _ ht.1).trans hvmax.2
                  rw [hchiOne, one_mul]
                  exact hmax harg
                _ = a * sigma vmax := by simp
            have hrightUpper :
                (∫ t : ℝ in a..vmax,
                  chi t * sigma (vmax - t)) ≤ n := by
              rw [show (n : ℝ) = ∫ _t : ℝ in a..vmax, (1 : ℝ) by
                simp [a]]
              apply intervalIntegral.integral_mono_on hav hright
                intervalIntegrable_const
              intro t ht
              have harg0 : 0 ≤ vmax - t := sub_nonneg.mpr ht.2
              have hargn : vmax - t ≤ n := by
                dsimp only [a] at ht
                linarith [ht.1]
              have hsarg := ih (vmax - t) harg0 hargn
              exact mul_le_one₀ (hchi.2.2.1 t (ha0.trans ht.1))
                hsarg.1 hsarg.2
            have hsplit := intervalIntegral.integral_add_adjacent_intervals
              hleft hright
            have heq := hsigma.2.2 vmax (hn1.trans hvmax.1)
            have hmain : vmax * sigma vmax ≤ a * sigma vmax + n := by
              rw [heq, ← hsplit]
              linarith
            dsimp only [a] at hmain
            nlinarith
          exact ⟨hlower, hupper⟩
  intro u hu0
  let n : ℕ := max 1 ⌈u⌉₊
  have hn1 : 1 ≤ n := le_max_left _ _
  have hun : u ≤ n := by
    exact (Nat.le_ceil u).trans (by
      exact_mod_cast (le_max_right 1 ⌈u⌉₊))
  exact hstep n hn1 u hu0 hun

end

end Erdos783
