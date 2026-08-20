import ErdosProblems.Erdos783.GSSection7
import ErdosProblems.Erdos783.GSMoments
import ErdosProblems.Erdos783.GSSection6
import ErdosProblems.Erdos783.GSSolution

open MeasureTheory Set

namespace Erdos783

noncomputable section

lemma continuousOn_gsDefect
    {chi sigma : ℝ → ℝ} (hchi : IsGSKernel chi)
    (hsigma : IsGSSolution chi sigma)
    {u : ℝ} (hu1 : 1 ≤ u) :
    ContinuousOn
      (fun v ↦ sigma v - dickmanRho (gsScale chi v))
      (Icc 0 u) := by
  have hs : ContinuousOn sigma (Icc 0 u) :=
    hsigma.1.mono (Icc_subset_Ici_self)
  have hE := continuousOn_gsScale_Icc_zero hchi hu1
  have hrho : ContinuousOn (fun v ↦ dickmanRho (gsScale chi v))
      (Icc 0 u) :=
    continuousOn_dickmanRho_Ici_zero.comp hE
      (fun v _hv ↦ (gsScale_pos chi v).le)
  exact hs.sub hrho

lemma gs_champion_principle
    {chi sigma : ℝ → ℝ} (hchi : IsGSKernel chi)
    (hsigma : IsGSSolution chi sigma)
    {u : ℝ} (hu1 : 1 ≤ u)
    (hchamp : ∀ v ∈ Icc (0 : ℝ) u,
      sigma u - dickmanRho (gsScale chi u) ≤
        sigma v - dickmanRho (gsScale chi v))
    (hBlt : gsB chi u < u)
    (hconv : u * dickmanRho (gsScale chi u) ≤
      ∫ t : ℝ in 0..u,
        chi t * dickmanRho (gsScale chi (u - t))) :
    dickmanRho (gsScale chi u) ≤ sigma u := by
  let D : ℝ → ℝ := fun v ↦ sigma v - dickmanRho (gsScale chi v)
  have hu0 : 0 ≤ u := zero_le_one.trans hu1
  have hDcont : ContinuousOn D (Icc 0 u) := by
    exact continuousOn_gsDefect hchi hsigma hu1
  have hsub : ContinuousOn (fun t : ℝ ↦ u - t) (Icc 0 u) :=
    continuousOn_const.sub continuousOn_id
  have hsubMap : MapsTo (fun t : ℝ ↦ u - t) (Icc 0 u) (Icc 0 u) := by
    intro t ht
    exact ⟨sub_nonneg.mpr ht.2, sub_le_self _ ht.1⟩
  have hDsub : ContinuousOn (fun t ↦ D (u - t)) (Icc 0 u) :=
    hDcont.comp hsub hsubMap
  have hDsub' : ContinuousOn (fun t ↦ D (u - t)) (uIcc 0 u) := by
    rw [uIcc_of_le hu0]
    exact hDsub
  have hintRight : IntervalIntegrable (fun t ↦ chi t * D (u - t))
      volume 0 u := (hchi.1 0 u).mul_continuousOn hDsub'
  have hintLeft : IntervalIntegrable (fun t ↦ chi t * D u)
      volume 0 u := (hchi.1 0 u).mul_const (D u)
  have hpoint : ∀ t ∈ Icc (0 : ℝ) u,
      chi t * D u ≤ chi t * D (u - t) := by
    intro t ht
    apply mul_le_mul_of_nonneg_left
    · exact hchamp (u - t) ⟨sub_nonneg.mpr ht.2, sub_le_self _ ht.1⟩
    · exact hchi.2.1 t ht.1
  have hmono :
      (∫ t : ℝ in 0..u, chi t * D u) ≤
        ∫ t : ℝ in 0..u, chi t * D (u - t) :=
    intervalIntegral.integral_mono_on hu0 hintLeft hintRight hpoint
  have hleft : (∫ t : ℝ in 0..u, chi t * D u) = gsB chi u * D u := by
    rw [intervalIntegral.integral_mul_const]
    rfl
  have hsigmaEq := hsigma.2.2 u hu1
  have hrhoInt := intervalIntegrable_gsWeightedDickmanSub hchi hu1
    (by norm_num : (0 : ℝ) ≤ 0) hu0 le_rfl
  have hsigmaSub : ContinuousOn (fun t ↦ sigma (u - t)) (Icc 0 u) :=
    (hsigma.1.mono Icc_subset_Ici_self).comp hsub hsubMap
  have hsigmaSub' : ContinuousOn (fun t ↦ sigma (u - t)) (uIcc 0 u) := by
    rw [uIcc_of_le hu0]
    exact hsigmaSub
  have hsigmaInt : IntervalIntegrable (fun t ↦ chi t * sigma (u - t))
      volume 0 u := (hchi.1 0 u).mul_continuousOn hsigmaSub'
  have hright :
      (∫ t : ℝ in 0..u, chi t * D (u - t)) =
        u * sigma u -
          ∫ t : ℝ in 0..u,
            chi t * dickmanRho (gsScale chi (u - t)) := by
    rw [show (fun t : ℝ ↦ chi t * D (u - t)) =
        (fun t ↦ chi t * sigma (u - t) -
          chi t * dickmanRho (gsScale chi (u - t))) by
      funext t
      dsimp only [D]
      ring]
    rw [intervalIntegral.integral_sub hsigmaInt hrhoInt, ← hsigmaEq]
  rw [hleft, hright] at hmono
  have hupper :
      u * sigma u -
          (∫ t : ℝ in 0..u,
            chi t * dickmanRho (gsScale chi (u - t))) ≤
        u * D u := by
    dsimp only [D]
    linarith
  have hchain := hmono.trans hupper
  dsimp only [D] at hchain ⊢
  nlinarith

/-- The two elementary cases which precede the champion argument in
Granville--Soundararajan, isolated with exactly the disjunction needed by
the final compact-minimum proof. -/
def GSPreliminaryBound (chi sigma : ℝ → ℝ) : Prop :=
  ∀ u : ℝ, 1 ≤ u →
    (gsScale chi u < 13 / 5 ∨
      gsScale chi u - 1 < gsScale chi (u / gsScale chi u)) →
    dickmanRho (gsScale chi u) ≤ sigma u

/-- The first (odd) Bonferroni truncation of the locally finite
Granville--Soundararajan expansion. -/
def GSFirstBonferroni (chi sigma : ℝ → ℝ) : Prop :=
  ∀ u : ℝ, 1 ≤ u → 1 - gsLogScale chi u ≤ sigma u

lemma gs_firstBonferroni_of_odd
    {chi sigma : ℝ → ℝ} (hodd : GSOddBonferroni chi sigma) :
    GSFirstBonferroni chi sigma := by
  intro u hu
  have h := hodd u (zero_le_one.trans hu) 0
  have hs : gsAlternatingMomentSum chi 1 u =
      1 - gsLogScale chi u := by
    rw [gsAlternatingMomentSum]
    simp [Finset.sum_range_succ, gsMoment_one chi hu]
    ring
  norm_num at h
  rw [hs] at h
  exact h

lemma gs_small_scale_bound
    {chi sigma : ℝ → ℝ} (hchi : IsGSKernel chi)
    (hfirst : GSFirstBonferroni chi sigma)
    {u : ℝ} (hu : 1 ≤ u) (hE : gsScale chi u ≤ 2) :
    dickmanRho (gsScale chi u) ≤ sigma u := by
  have hEone : 1 ≤ gsScale chi u := gsScale_ge_one hchi hu
  rw [dickmanRho_eq_one_sub_log hEone hE]
  have hlog : Real.log (gsScale chi u) = gsLogScale chi u := by
    simp [gsScale]
  rw [hlog]
  exact hfirst u hu

lemma gs_small_scale_refined
    {chi sigma : ℝ → ℝ} (hchi : IsGSKernel chi)
    (hodd : GSOddBonferroni chi sigma)
    {u : ℝ} (hu : 1 ≤ u) (hE : gsScale chi u ≤ 2) :
    dickmanRho (gsScale chi u) +
        (1 - gsLogScale chi u / 3) / 2 * gsMoment chi 2 u ≤ sigma u := by
  have hEone : 1 ≤ gsScale chi u := gsScale_ge_one hchi hu
  have hI3 := gsMoment_three_le_logScale_mul_two hchi hu
  have hlower := gs_lower_three_of_odd hodd hu
    (xi := gsLogScale chi u / 3) (by
      convert hI3 using 1 <;> ring)
  rw [dickmanRho_eq_one_sub_log hEone hE]
  have hlog : Real.log (gsScale chi u) = gsLogScale chi u := by
    simp [gsScale]
  rw [hlog]
  nlinarith

lemma gsLogScale_lt_three_of_scale_le_two
    {chi : ℝ → ℝ} {u : ℝ} (hE : gsScale chi u ≤ 2) :
    gsLogScale chi u < 3 := by
  have hlogle := Real.strictMonoOn_log.monotoneOn
    (gsScale_pos chi u) (by norm_num : (0 : ℝ) < 2) hE
  have hlog : Real.log (gsScale chi u) = gsLogScale chi u := by
    simp [gsScale]
  rw [hlog] at hlogle
  exact hlogle.trans_lt (Real.log_two_lt_d9.trans (by norm_num))

lemma gsMoment_two_eq_zero_of_small_scale_of_upper
    {chi sigma : ℝ → ℝ} (hchi : IsGSKernel chi)
    (hodd : GSOddBonferroni chi sigma)
    {u : ℝ} (hu : 1 ≤ u) (hE : gsScale chi u ≤ 2)
    (hupper : sigma u ≤ dickmanRho (gsScale chi u)) :
    gsMoment chi 2 u = 0 := by
  have hrefined := gs_small_scale_refined hchi hodd hu hE
  have hcoef : 0 < (1 - gsLogScale chi u / 3) / 2 := by
    have hM3 := gsLogScale_lt_three_of_scale_le_two hE
    have hdiv : gsLogScale chi u / 3 < 1 := by linarith
    exact div_pos (sub_pos.mpr hdiv) (by norm_num)
  have hmoment : 0 ≤ gsMoment chi 2 u :=
    gsMoment_nonneg hchi 2 (zero_le_one.trans hu)
  nlinarith

/-- Granville--Soundararajan Proposition 6.1 in the non-strict form used
by the final proof. -/
def GSProposition61 (chi sigma : ℝ → ℝ) : Prop :=
  ∀ u : ℝ, 1 ≤ u → 2 < gsScale chi u →
    gsScale chi u - 1 < gsScale chi (u / gsScale chi u) →
    dickmanRho (gsScale chi u) ≤ sigma u

/-- Granville--Soundararajan Proposition 6.2.  The endpoint `13/5` is
written exactly, so the complement feeds the Section 7 certificate. -/
def GSProposition62 (chi sigma : ℝ → ℝ) : Prop :=
  ∀ u : ℝ, 1 ≤ u → 2 < gsScale chi u →
    gsScale chi u < 13 / 5 →
    dickmanRho (gsScale chi u) ≤ sigma u

theorem gs_preliminaryBound_of_section6
    {chi sigma : ℝ → ℝ} (hchi : IsGSKernel chi)
    (hfirst : GSFirstBonferroni chi sigma)
    (h61 : GSProposition61 chi sigma)
    (h62 : GSProposition62 chi sigma) :
    GSPreliminaryBound chi sigma := by
  intro u hu hcase
  by_cases hE2 : gsScale chi u ≤ 2
  · exact gs_small_scale_bound hchi hfirst hu hE2
  · have hE2' : 2 < gsScale chi u := lt_of_not_ge hE2
    rcases hcase with hsmall | hlarge
    · exact h62 u hu hE2' hsmall
    · exact h61 u hu hE2' hlarge

theorem gs_continuous_extremal_of_preliminary
    {chi sigma : ℝ → ℝ} (hchi : IsGSKernel chi)
    (hsigma : IsGSSolution chi sigma)
    (hpre : GSPreliminaryBound chi sigma) :
    ∀ u : ℝ, 0 ≤ u → dickmanRho (gsScale chi u) ≤ sigma u := by
  intro u hu
  by_contra hbad
  have hbad' : sigma u - dickmanRho (gsScale chi u) < 0 := by
    exact sub_neg.mpr (lt_of_not_ge hbad)
  let D : ℝ → ℝ := fun v ↦ sigma v - dickmanRho (gsScale chi v)
  have hu1 : 1 ≤ max 1 u := le_max_left _ _
  have huMax : u ≤ max 1 u := le_max_right _ _
  have hDcont : ContinuousOn D (Icc 0 (max 1 u)) :=
    continuousOn_gsDefect hchi hsigma hu1
  obtain ⟨v, hv, hvmin⟩ := isCompact_Icc.exists_isMinOn
    (nonempty_Icc.mpr (by positivity : (0 : ℝ) ≤ max 1 u)) hDcont
  have huMem : u ∈ Icc (0 : ℝ) (max 1 u) := ⟨hu, huMax⟩
  have hvneg : D v < 0 := (hvmin huMem).trans_lt (by simpa [D] using hbad')
  have hv0 : 0 ≤ v := hv.1
  have hv1 : 1 < v := by
    by_contra hvnot
    have hvle : v ≤ 1 := le_of_not_gt hvnot
    have hsOne : sigma v = 1 := hsigma.2.1 v hv0 hvle
    have hEOne : gsScale chi v = 1 := gsScale_eq_one hchi hv0 hvle
    have hrhoOne : dickmanRho (1 : ℝ) = 1 :=
      dickmanRho_profile.2.1 1 (by norm_num) (by norm_num)
    simp only [D, hsOne, hEOne, hrhoOne, sub_self] at hvneg
    exact lt_irrefl 0 hvneg
  have hv1le : 1 ≤ v := hv1.le
  have hvchamp : ∀ w ∈ Icc (0 : ℝ) v, D v ≤ D w := by
    intro w hw
    apply hvmin
    exact ⟨hw.1, hw.2.trans hv.2⟩
  by_cases hpreCase : gsScale chi v < 13 / 5 ∨
      gsScale chi v - 1 < gsScale chi (v / gsScale chi v)
  · have hbound := hpre v hv1le hpreCase
    exact (not_lt_of_ge hbound) (by simpa [D] using hvneg)
  · have heLarge : (13 / 5 : ℝ) ≤ gsScale chi v :=
      le_of_not_gt (fun h ↦ hpreCase (Or.inl h))
    have hsmall : gsScale chi (v / gsScale chi v) ≤
        gsScale chi v - 1 :=
      le_of_not_gt (fun h ↦ hpreCase (Or.inr h))
    have hconv := gs_champion_integral_inequality hchi hv1le heLarge hsmall
    have hBupper := (gs_scale_bounds hchi (t := (1 : ℝ)) (y := v)
      (by norm_num) hv1le).2
    have hBlt : gsB chi v < v := by
      rw [gsB_one hchi, gsScale_one] at hBupper
      norm_num at hBupper
      nlinarith
    have hbound := gs_champion_principle hchi hsigma hv1le
      (by simpa only [D] using hvchamp) hBlt hconv
    exact (not_lt_of_ge hbound) (by simpa [D] using hvneg)

/-- Assembly of the continuous argument from the genuine odd Bonferroni
inequalities and the two Section 6 estimates. -/
theorem gs_continuous_extremal_of_section6
    {chi sigma : ℝ → ℝ} (hchi : IsGSKernel chi)
    (hsigma : IsGSSolution chi sigma)
    (hodd : GSOddBonferroni chi sigma)
    (h61 : GSProposition61 chi sigma)
    (h62 : GSProposition62 chi sigma) :
    ∀ u : ℝ, 0 ≤ u → dickmanRho (gsScale chi u) ≤ sigma u := by
  exact gs_continuous_extremal_of_preliminary hchi hsigma
    (gs_preliminaryBound_of_section6 hchi
      (gs_firstBonferroni_of_odd hodd) h61 h62)

lemma gs_proposition62_ge_three
    {chi sigma : ℝ → ℝ} (hchi : IsGSKernel chi)
    (hodd : GSOddBonferroni chi sigma)
    {u : ℝ} (hu3 : 3 ≤ u) (he2 : 2 < gsScale chi u)
    (heUpper : gsScale chi u < 13 / 5)
    (hcut : gsScale chi (u / gsScale chi u) ≤ gsScale chi u - 1) :
    dickmanRho (gsScale chi u) ≤ sigma u := by
  let e : ℝ := gsScale chi u
  let ey : ℝ := gsScale chi (u / 3)
  let xi : ℝ := gsLogScale chi (u / 3)
  let S : ℝ :=
    Real.log (2 * e / (3 * (e - 1))) +
      Real.log (e * (1 - 1 / (3 * ey)) / (e - 1))
  have hu : 1 ≤ u := by linarith
  have hy : 1 ≤ u / 3 := by linarith
  have heLe : e ≤ 13 / 5 := by dsimp only [e]; exact heUpper.le
  have heThree : e ≤ 3 := by
    dsimp only [e] at heUpper ⊢
    norm_num at heUpper ⊢
    linarith
  have heOne : 1 ≤ e := by
    dsimp only [e]
    exact gsScale_ge_one hchi hu
  have heyOne : 1 ≤ ey := by
    dsimp only [ey]
    exact gsScale_ge_one hchi hy
  have hePos : 0 < e := zero_lt_one.trans_le heOne
  have heu : e ≤ u := by
    dsimp only [e]
    exact gsScale_le_self hchi hu
  have hyCutArg : u / 3 ≤ u / e := by
    apply (div_le_div_iff_of_pos_left (zero_lt_one.trans_le hu)
      (by norm_num) hePos).mpr
    exact heThree
  have huDivE : 1 ≤ u / e := by
    exact (le_div_iff₀ hePos).mpr (by simpa only [one_mul] using heu)
  have heyCut : ey ≤ e - 1 := by
    calc
      ey ≤ gsScale chi (u / e) := by
        dsimp only [ey]
        exact gsScale_mono hchi hy huDivE hyCutArg
      _ ≤ e - 1 := by simpa only [e] using hcut
  have hxi : Real.log ey = xi := by
    dsimp only [ey, xi, gsScale]
    rw [Real.log_exp]
  have hxi0 : 0 ≤ xi := by
    rw [← hxi]
    exact Real.log_nonneg heyOne
  have hxiOne : xi ≤ 1 := by
    have heyEight : ey ≤ 8 / 5 := by
      dsimp only [e] at heLe
      linarith
    have hlogmono := Real.log_le_log (gsScale_pos chi (u / 3)) heyEight
    have hnum := log_eight_fifths_bounds.2
    rw [hxi] at hlogmono
    norm_num at hnum ⊢
    linarith
  have hI3 := gsMoment_three_le_three_logScale_third hchi hu3
  change gsMoment chi 3 u ≤ 3 * xi * gsMoment chi 2 u at hI3
  have hlower := gs_lower_three_of_odd hodd hu hI3
  have hI2 := gsMoment_two_lower_explicit hchi hu3 he2 heUpper.le hcut
  change gsGamma e + xi * S ≤ gsMoment chi 2 u at hI2
  have hscalar := section62_scalar
    (e := e) (ey := ey) (by simpa only [e] using he2)
      heLe heyOne heyCut
  rw [hxi] at hscalar
  change gsGamma e ≤ (1 - xi) * S at hscalar
  have hcoef : 0 ≤ 1 - xi := sub_nonneg.mpr hxiOne
  have hI2scaled : (1 - xi) * (gsGamma e + xi * S) ≤
      (1 - xi) * gsMoment chi 2 u :=
    mul_le_mul_of_nonneg_left hI2 hcoef
  have hgammaScaled : gsGamma e ≤
      (1 - xi) * (gsGamma e + xi * S) := by
    have hbonus : 0 ≤ xi * ((1 - xi) * S - gsGamma e) :=
      mul_nonneg hxi0 (sub_nonneg.mpr hscalar)
    nlinarith
  have hgammaI2 : gsGamma e ≤ (1 - xi) * gsMoment chi 2 u :=
    hgammaScaled.trans hI2scaled
  have hrho := dickmanRho_eq_gamma he2.le heThree
  have hlog : Real.log e = gsLogScale chi u := by
    dsimp only [e, gsScale]
    rw [Real.log_exp]
  rw [hlog] at hrho
  change 1 - gsLogScale chi u + (1 - xi) / 2 * gsMoment chi 2 u ≤ sigma u at hlower
  rw [hrho]
  nlinarith

lemma gsMoment_two_ge_gamma_of_lt_three
    {chi : ℝ → ℝ} (hchi : IsGSKernel chi)
    {u : ℝ} (hu : 1 ≤ u) (hu3 : u < 3)
    (he2 : 2 < gsScale chi u) :
    gsGamma (gsScale chi u) ≤ gsMoment chi 2 u := by
  let e : ℝ := gsScale chi u
  let a : ℝ := u / e
  let u₁ : ℝ := u * (1 - 1 / e)
  have hu0 : 0 < u := zero_lt_one.trans_le hu
  have hePos : 0 < e := by dsimp only [e]; exact gsScale_pos chi u
  have heu : e ≤ u := by dsimp only [e]; exact gsScale_le_self hchi hu
  have huDivE : 1 ≤ u / e :=
    (le_div_iff₀ hePos).mpr (by simpa only [one_mul] using heu)
  have haPos : 0 < a := by dsimp only [a]; positivity
  have hau : a ≤ u := by
    dsimp only [a]
    apply (div_le_iff₀ hePos).mpr
    nlinarith
  have hau₁ : a ≤ u₁ := by
    dsimp only [a, u₁]
    rw [show u * (1 - 1 / e) = u * (e - 1) / e by
      field_simp [hePos.ne']]
    exact div_le_div_of_nonneg_right
      (by simpa only [mul_one] using
        mul_le_mul_of_nonneg_left (by linarith : 1 ≤ e - 1) hu0.le) hePos.le
  have hu₁u : u₁ < u := by
    have hgap : u - u₁ = u / e := by
      dsimp only [u₁]
      field_simp [hePos.ne']
      ring
    have : 0 < u / e := div_pos hu0 hePos
    linarith
  have hraw := gsMoment_two_rearranged hchi hu
    (y := (1 : ℝ)) (by norm_num) hu
  rw [gsScale_one] at hraw
  norm_num at hraw
  change (∫ t : ℝ in a..u, gsMoment chi 1 (u - t) / t) ≤
    gsMoment chi 2 u at hraw
  have hmodel := intervalIntegrable_inv_mul_moment_one hchi haPos hau le_rfl
  have hmodel₁ : IntervalIntegrable
      (fun t : ℝ => (1 / t) * gsMoment chi 1 (u - t)) volume a u₁ := by
    apply hmodel.mono_set
    rw [uIcc_of_le hau₁, uIcc_of_le hau]
    exact Icc_subset_Icc le_rfl hu₁u.le
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioc a u)]
      (fun t : ℝ => (1 / t) * gsMoment chi 1 (u - t)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact mul_nonneg (one_div_nonneg.mpr (haPos.le.trans ht.1.le))
      (gsMoment_nonneg hchi 1 (sub_nonneg.mpr ht.2))
  have hrestrict :
      (∫ t : ℝ in a..u₁, (1 / t) * gsMoment chi 1 (u - t)) ≤
        ∫ t : ℝ in a..u, (1 / t) * gsMoment chi 1 (u - t) :=
    intervalIntegral.integral_mono_interval le_rfl hau₁ hu₁u.le hnonneg hmodel
  have hlog := intervalIntegrable_log_complement_div hu0 hePos
    haPos hau₁ hu₁u
  have hlogLower :
      (∫ t : ℝ in a..u₁, Real.log (e * (u - t) / u) / t) ≤
        ∫ t : ℝ in a..u₁, (1 / t) * gsMoment chi 1 (u - t) := by
    apply intervalIntegral.integral_mono_on hau₁ hlog hmodel₁
    intro t ht
    have ht1 : 1 ≤ u - t := by
      have htu₁ : t ≤ u₁ := ht.2
      dsimp only [u₁] at htu₁
      have heNe : e ≠ 0 := hePos.ne'
      field_simp [heNe] at htu₁
      nlinarith [huDivE]
    have htU : u - t ≤ u := by linarith [haPos.le.trans ht.1]
    have hpoint := gsMoment_one_ge_log_scale_ratio hchi ht1 htU
    change Real.log (e * (u - t) / u) ≤ gsMoment chi 1 (u - t) at hpoint
    have ht0 : 0 ≤ t := haPos.le.trans ht.1
    simpa [div_eq_mul_inv, mul_comm] using
      mul_le_mul_of_nonneg_left hpoint (inv_nonneg.mpr ht0)
  have hgamma := scaled_gamma_integral (u := u) (e := e) hu0 hePos
  change (∫ t : ℝ in a..u₁, Real.log (e * (u - t) / u) / t) =
    gsGamma e at hgamma
  have hchain := hlogLower.trans hrestrict
  have hconv : (∫ t : ℝ in a..u, (1 / t) * gsMoment chi 1 (u - t)) =
      ∫ t : ℝ in a..u, gsMoment chi 1 (u - t) / t := by
    apply intervalIntegral.integral_congr
    intro t _ht
    ring
  rw [hgamma, hconv] at hchain
  exact hchain.trans hraw

lemma gs_proposition62_lt_three
    {chi sigma : ℝ → ℝ} (hchi : IsGSKernel chi)
    (hodd : GSOddBonferroni chi sigma)
    {u : ℝ} (hu : 1 ≤ u) (hu3 : u < 3)
    (he2 : 2 < gsScale chi u) :
    dickmanRho (gsScale chi u) ≤ sigma u := by
  let e : ℝ := gsScale chi u
  have heLe : e ≤ 3 := by
    dsimp only [e]
    exact (gsScale_le_self hchi hu).trans hu3.le
  have hI3zero : gsMoment chi 3 u = 0 := by
    exact gsMoment_eq_zero_of_lt (by linarith : 0 ≤ u) hu3
  have hI3 : gsMoment chi 3 u ≤ 3 * (0 : ℝ) * gsMoment chi 2 u := by
    rw [hI3zero]
    norm_num
  have hlower := gs_lower_three_of_odd hodd hu hI3
  norm_num at hlower
  have hgamma := gsMoment_two_ge_gamma_of_lt_three hchi hu hu3 he2
  change gsGamma e ≤ gsMoment chi 2 u at hgamma
  have hrho := dickmanRho_eq_gamma he2.le heLe
  have hlog : Real.log e = gsLogScale chi u := by
    dsimp only [e, gsScale]
    rw [Real.log_exp]
  rw [hlog] at hrho
  rw [hrho]
  nlinarith

theorem gs_proposition62
    {chi sigma : ℝ → ℝ} (hchi : IsGSKernel chi)
    (hodd : GSOddBonferroni chi sigma)
    (h61 : GSProposition61 chi sigma) :
    GSProposition62 chi sigma := by
  intro u hu he2 heUpper
  by_cases hu3 : 3 ≤ u
  · by_cases hcut : gsScale chi (u / gsScale chi u) ≤ gsScale chi u - 1
    · exact gs_proposition62_ge_three hchi hodd hu3 he2 heUpper hcut
    · exact h61 u hu he2 (lt_of_not_ge hcut)
  · exact gs_proposition62_lt_three hchi hodd hu (lt_of_not_ge hu3) he2


theorem gs_continuous_extremal_of_section61
    {chi sigma : ℝ → ℝ} (hchi : IsGSKernel chi)
    (hsigma : IsGSSolution chi sigma)
    (hodd : GSOddBonferroni chi sigma)
    (h61 : GSProposition61 chi sigma) :
    ∀ u : ℝ, 0 ≤ u → dickmanRho (gsScale chi u) ≤ sigma u := by
  exact gs_continuous_extremal_of_section6 hchi hsigma hodd h61
    (gs_proposition62 hchi hodd h61)

end

end Erdos783
