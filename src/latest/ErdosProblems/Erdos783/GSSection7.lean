import ErdosProblems.Erdos783.GSChampion

open MeasureTheory Set

namespace Erdos783

noncomputable section

lemma monotoneOn_dickmanRho_gsScale_sub
    {chi : ℝ → ℝ} (hchi : IsGSKernel chi)
    {u a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ u - 1) :
    MonotoneOn (fun t ↦ dickmanRho (gsScale chi (u - t))) (Icc a b) := by
  intro s hs t ht hst
  have hus0 : 0 ≤ u - s := by linarith [hs.2, hb]
  have hut0 : 0 ≤ u - t := by linarith [ht.2, hb]
  have harg : u - t ≤ u - s := by linarith
  have hE := gsScale_mono_Ici_zero hchi hut0 hus0 harg
  have hEt0 : 0 ≤ gsScale chi (u - t) := (gsScale_pos _ _).le
  have hEs0 : 0 ≤ gsScale chi (u - s) := (gsScale_pos _ _).le
  exact antitoneOn_dickmanRho_Ici_zero hEt0 hEs0 hE

lemma continuousOn_dickmanRho_gsScale_sub
    {chi : ℝ → ℝ} (hchi : IsGSKernel chi)
    {u a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ u - 1) :
    ContinuousOn (fun t ↦ dickmanRho (gsScale chi (u - t))) (Icc a b) := by
  have hu : 1 ≤ u := by linarith
  have hsub : ContinuousOn (fun t : ℝ ↦ u - t) (Icc a b) :=
    continuousOn_const.sub continuousOn_id
  have hsubMap : MapsTo (fun t : ℝ ↦ u - t) (Icc a b) (Icc 1 u) := by
    intro t ht
    constructor
    · linarith [ht.2, hb]
    · linarith [ht.1, ha]
  have hE : ContinuousOn (fun t ↦ gsScale chi (u - t)) (Icc a b) :=
    (continuousOn_gsScale_Icc hchi hu).comp hsub hsubMap
  exact continuousOn_dickmanRho_Ici_zero.comp hE
    (fun t _ht ↦ (gsScale_pos chi (u - t)).le)

/-- Equation (7.2), prior to evaluating the final Dickman integral. -/
lemma gs_champion_I3_preliminary
    {chi : ℝ → ℝ} (hchi : IsGSKernel chi)
    {u u₀ V : ℝ}
    (hu₀ : 0 ≤ u₀) (hu₀le : u₀ ≤ u - 1)
    (hV : V = u - gsB chi u₀) :
    (∫ t : ℝ in 0..u₀,
        chi t * dickmanRho (gsScale chi (u - t))) ≥
      ∫ t : ℝ in V..u, dickmanRho (gsScale chi t) := by
  let g : ℝ → ℝ := fun t ↦ dickmanRho (gsScale chi (u - t))
  have hB0 : 0 ≤ gsB chi u₀ := gsB_nonneg hchi hu₀
  have hBle : gsB chi u₀ ≤ u₀ := gsB_le hchi hu₀
  have hgmono : MonotoneOn g (Icc 0 u₀) := by
    exact monotoneOn_dickmanRho_gsScale_sub hchi (by norm_num) hu₀ hu₀le
  have hgcont : ContinuousOn g (Icc 0 u₀) := by
    exact continuousOn_dickmanRho_gsScale_sub hchi (by norm_num) hu₀ hu₀le
  have hg : IntervalIntegrable g volume 0 u₀ := by
    have : ContinuousOn g (uIcc 0 u₀) := by
      simpa [uIcc_of_le hu₀] using hgcont
    exact this.intervalIntegrable
  have hchig : IntervalIntegrable (fun t ↦ chi t * g t) volume 0 u₀ :=
    (hchi.1 0 u₀).mul_continuousOn (by simpa [uIcc_of_le hu₀] using hgcont)
  have hbathtub := gs_rearrangement_lower_integrable hu₀ hB0
    (by linarith) (hchi.1 0 u₀) hg hchig
    (fun t ht ↦ hchi.2.1 t ht.1)
    (fun t ht ↦ hchi.2.2.1 t ht.1)
    hgmono (by rfl : (∫ t : ℝ in 0..u₀, chi t) = gsB chi u₀)
  have hchange :
      (∫ t : ℝ in 0..gsB chi u₀, g t) =
        ∫ t : ℝ in V..u, dickmanRho (gsScale chi t) := by
    dsimp only [g]
    have hsub := intervalIntegral.integral_comp_sub_left
      (f := fun s : ℝ ↦ dickmanRho (gsScale chi s))
      (a := (0 : ℝ)) (b := gsB chi u₀) u
    rw [hsub]
    rw [hV]
    congr 1 <;> ring
  simpa [g, hchange] using hbathtub

lemma gs_champion_dickman_integral_lower
    {chi : ℝ → ℝ} (hchi : IsGSKernel chi)
    {u V : ℝ} (hV1 : 1 ≤ V) (hVu : V ≤ u)
    (hVu1 : u - u / gsScale chi u ≤ V) :
    u * dickmanRho (gsScale chi u) -
        V / gsScale chi V *
          (∫ t : ℝ in (gsScale chi u - 1)..gsScale chi V,
            dickmanRho t) ≤
      ∫ t : ℝ in V..u, dickmanRho (gsScale chi t) := by
  let e := gsScale chi u
  let eV := gsScale chi V
  let W := V * e / eV
  have hu1 : 1 ≤ u := hV1.trans hVu
  have hePos : 0 < e := gsScale_pos chi u
  have heVPos : 0 < eV := gsScale_pos chi V
  have hEVle : eV ≤ e := gsScale_mono hchi hV1 hu1 hVu
  have hratio : e / u ≤ eV / V := gsScale_div_antitone hchi hV1 hVu
  have huPos : 0 < u := zero_lt_one.trans_le hu1
  have hVPos : 0 < V := zero_lt_one.trans_le hV1
  have heVlower : e - 1 ≤ eV := by
    have hfromV' : u * (e - 1) ≤ V * e := by
      have hVu1' : u - u / e ≤ V := by
        simpa only [e] using hVu1
      calc
        u * (e - 1) = e * (u - u / e) := by
          field_simp [hePos.ne']
          <;> ring
        _ ≤ e * V := mul_le_mul_of_nonneg_left hVu1' hePos.le
        _ = V * e := by ring
    have hmul' : V * e ≤ u * eV := by
      have := (div_le_div_iff₀ huPos hVPos).mp hratio
      nlinarith
    have : u * (e - 1) ≤ u * eV := hfromV'.trans hmul'
    exact le_of_mul_le_mul_left this huPos
  have hVW : V ≤ W := by
    dsimp only [W]
    rw [le_div_iff₀ heVPos]
    nlinarith
  have hWu : W ≤ u := by
    dsimp only [W]
    rw [div_le_iff₀ heVPos]
    have h := hratio
    field_simp [huPos.ne', hVPos.ne'] at h ⊢
    nlinarith
  have hcontE : ContinuousOn (gsScale chi) (Icc V u) :=
    (continuousOn_gsScale_Icc hchi hu1).mono
      (Icc_subset_Icc hV1 le_rfl)
  have hcontRhoE : ContinuousOn (fun t ↦ dickmanRho (gsScale chi t))
      (Icc V u) :=
    continuousOn_dickmanRho_Ici_zero.comp hcontE
      (fun t _ht ↦ (gsScale_pos chi t).le)
  have hintRhoE : IntervalIntegrable
      (fun t ↦ dickmanRho (gsScale chi t)) volume V u := by
    have : ContinuousOn (fun t ↦ dickmanRho (gsScale chi t)) (uIcc V u) := by
      simpa [uIcc_of_le hVu] using hcontRhoE
    exact this.intervalIntegrable
  have hintLeft : IntervalIntegrable
      (fun t ↦ dickmanRho (gsScale chi t)) volume V W :=
    hintRhoE.mono_set (by
      rw [uIcc_of_le hVW, uIcc_of_le hVu]
      exact Icc_subset_Icc le_rfl hWu)
  have hintRight : IntervalIntegrable
      (fun t ↦ dickmanRho (gsScale chi t)) volume W u :=
    hintRhoE.mono_set (by
      rw [uIcc_of_le hWu, uIcc_of_le hVu]
      exact Icc_subset_Icc hVW le_rfl)
  have hleftPoint : ∀ t ∈ Icc V W,
      dickmanRho (eV / V * t) ≤ dickmanRho (gsScale chi t) := by
    intro t ht
    have ht1 : 1 ≤ t := hV1.trans ht.1
    have hratioT := gsScale_div_antitone hchi hV1 ht.1
    have htPos : 0 < t := zero_lt_one.trans_le ht1
    have hscale : gsScale chi t ≤ eV / V * t := by
      dsimp only [eV] at hratioT ⊢
      field_simp [hVPos.ne', htPos.ne'] at hratioT ⊢
      nlinarith
    exact antitoneOn_dickmanRho_Ici_zero (gsScale_pos chi t).le
      (mul_nonneg (div_nonneg heVPos.le hVPos.le) htPos.le) hscale
  have hrightPoint : ∀ t ∈ Icc W u,
      dickmanRho e ≤ dickmanRho (gsScale chi t) := by
    intro t ht
    have ht1 : 1 ≤ t := hV1.trans (hVW.trans ht.1)
    have hscale := gsScale_mono hchi ht1 hu1 ht.2
    exact antitoneOn_dickmanRho_Ici_zero (gsScale_pos chi t).le
      hePos.le hscale
  have hleftModel : IntervalIntegrable
      (fun t ↦ dickmanRho (eV / V * t)) volume V W := by
    have hc : 0 < eV / V := div_pos heVPos hVPos
    have hcont : ContinuousOn (fun t ↦ dickmanRho (eV / V * t))
        (Icc V W) := by
      apply continuousOn_dickmanRho_Ici_zero.comp
        (continuousOn_const.mul continuousOn_id)
      intro t ht
      exact mul_nonneg (div_nonneg heVPos.le hVPos.le)
        (hVPos.le.trans ht.1)
    have : ContinuousOn (fun t ↦ dickmanRho (eV / V * t)) (uIcc V W) := by
      simpa [uIcc_of_le hVW] using hcont
    exact this.intervalIntegrable
  have hrightModel : IntervalIntegrable (fun _t : ℝ ↦ dickmanRho e)
      volume W u := intervalIntegrable_const
  have hleftLower :
      (∫ t : ℝ in V..W, dickmanRho (eV / V * t)) ≤
        ∫ t : ℝ in V..W, dickmanRho (gsScale chi t) := by
    exact intervalIntegral.integral_mono_on hVW hleftModel hintLeft hleftPoint
  have hrightLower :
      (∫ _t : ℝ in W..u, dickmanRho e) ≤
        ∫ t : ℝ in W..u, dickmanRho (gsScale chi t) := by
    exact intervalIntegral.integral_mono_on hWu hrightModel hintRight hrightPoint
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hintLeft hintRight
  have hmodel :
      (u - W) * dickmanRho e +
          V / eV * (∫ t : ℝ in eV..e, dickmanRho t) ≤
        ∫ t : ℝ in V..u, dickmanRho (gsScale chi t) := by
    have hchange := intervalIntegral.integral_comp_mul_left
      (f := dickmanRho) (a := V) (b := W)
      (show eV / V ≠ 0 by positivity)
    have hconst : (∫ _t : ℝ in W..u, dickmanRho e) =
        (u - W) * dickmanRho e := by simp [mul_comm]
    have hchange' :
        (∫ t : ℝ in V..W, dickmanRho (eV / V * t)) =
          V / eV * (∫ t : ℝ in eV..e, dickmanRho t) := by
      rw [hchange]
      have hca : eV / V * V = eV := by
        field_simp [hVPos.ne']
      have hcb : eV / V * W = e := by
        dsimp only [W]
        field_simp [hVPos.ne', heVPos.ne']
      rw [hca, hcb]
      rw [show (eV / V)⁻¹ = V / eV by
        field_simp [hVPos.ne', heVPos.ne']]
      simp only [smul_eq_mul]
    rw [← hsplit, ← hchange', ← hconst]
    linarith
  have he1 : 1 ≤ e := gsScale_ge_one hchi hu1
  have hintRho : IntervalIntegrable dickmanRho volume (e - 1) e :=
    intervalIntegrable_dickmanRho_of_nonneg (by linarith) hePos.le
  have hintBefore : IntervalIntegrable dickmanRho volume (e - 1) eV :=
    hintRho.mono_set (by
      rw [uIcc_of_le heVlower, uIcc_of_le (by linarith : e - 1 ≤ e)]
      exact Icc_subset_Icc le_rfl hEVle)
  have hintAfter : IntervalIntegrable dickmanRho volume eV e :=
    hintRho.mono_set (by
      rw [uIcc_of_le hEVle, uIcc_of_le (by linarith : e - 1 ≤ e)]
      exact Icc_subset_Icc heVlower le_rfl)
  have hsplitRho := intervalIntegral.integral_add_adjacent_intervals
    hintBefore hintAfter
  have hdelay := dickmanRho_profile.2.2.2.2 e he1
  have htotal :
      (∫ t : ℝ in (e - 1)..eV, dickmanRho t) +
          (∫ t : ℝ in eV..e, dickmanRho t) = e * dickmanRho e := by
    calc
      _ = ∫ t : ℝ in (e - 1)..e, dickmanRho t := hsplitRho
      _ = e * dickmanRho e := hdelay
  have hid :
      u * dickmanRho e -
          V / eV * (∫ t : ℝ in (e - 1)..eV, dickmanRho t) =
        (u - W) * dickmanRho e +
          V / eV * (∫ t : ℝ in eV..e, dickmanRho t) := by
    dsimp only [W]
    field_simp [heVPos.ne']
    nlinarith
  rw [hid]
  exact hmodel

lemma gs_weighted_interval_lower
    {chi g : ℝ → ℝ} (hchi : IsGSKernel chi)
    {lo hi k : ℝ} (hlo0 : 0 ≤ lo) (hlohi : lo ≤ hi)
    (htarget : IntervalIntegrable (fun t ↦ chi t * g t) volume lo hi)
    (hk : ∀ t ∈ Icc lo hi, k ≤ g t) :
    k * (gsB chi hi - gsB chi lo) ≤
      ∫ t : ℝ in lo..hi, chi t * g t := by
  have hmodel : IntervalIntegrable (fun t ↦ chi t * k) volume lo hi :=
    (hchi.1 lo hi).mul_const k
  have hmono :
      (∫ t : ℝ in lo..hi, chi t * k) ≤
        ∫ t : ℝ in lo..hi, chi t * g t := by
    apply intervalIntegral.integral_mono_on hlohi hmodel htarget
    intro t ht
    exact mul_le_mul_of_nonneg_left (hk t ht)
      (hchi.2.1 t (hlo0.trans ht.1))
  calc
    k * (gsB chi hi - gsB chi lo) =
        ∫ t : ℝ in lo..hi, chi t * k := by
      rw [gsB_sub hchi hlo0 hlohi,
        intervalIntegral.integral_mul_const]
      ring
    _ ≤ _ := hmono

lemma scaled_dickman_interval_upper
    {base lo hi alpha mass : ℝ}
    (hbase0 : 0 ≤ base) (hbaseLo : base ≤ lo) (hlohi : lo ≤ hi)
    (halpha : 0 ≤ alpha) (hlen : alpha * (hi - lo) = mass) :
    alpha * (∫ t : ℝ in lo..hi, dickmanRho t) ≤
      dickmanRho base * mass := by
  have hint : IntervalIntegrable dickmanRho volume lo hi :=
    intervalIntegrable_dickmanRho_of_nonneg
      (hbase0.trans hbaseLo) (hbase0.trans (hbaseLo.trans hlohi))
  have hupper :
      (∫ t : ℝ in lo..hi, dickmanRho t) ≤
        ∫ _t : ℝ in lo..hi, dickmanRho base := by
    apply intervalIntegral.integral_mono_on hlohi hint intervalIntegrable_const
    intro t ht
    exact antitoneOn_dickmanRho_Ici_zero hbase0
      (hbase0.trans (hbaseLo.trans ht.1)) (hbaseLo.trans ht.1)
  have hscaled := mul_le_mul_of_nonneg_left hupper halpha
  rw [show (∫ _t : ℝ in lo..hi, dickmanRho base) =
      (hi - lo) * dickmanRho base by simp] at hscaled
  calc
    alpha * (∫ t : ℝ in lo..hi, dickmanRho t) ≤
        alpha * ((hi - lo) * dickmanRho base) := hscaled
    _ = dickmanRho base * mass := by
      rw [← mul_assoc, hlen]
      ring

lemma intervalIntegrable_gsWeightedDickmanSub
    {chi : ℝ → ℝ} (hchi : IsGSKernel chi)
    {u lo hi : ℝ} (hu1 : 1 ≤ u) (hlo0 : 0 ≤ lo)
    (hlohi : lo ≤ hi) (hhiu : hi ≤ u) :
    IntervalIntegrable
      (fun t ↦ chi t * dickmanRho (gsScale chi (u - t)))
      volume lo hi := by
  have hsub : ContinuousOn (fun t : ℝ ↦ u - t) (Icc lo hi) :=
    continuousOn_const.sub continuousOn_id
  have hsubMap : MapsTo (fun t : ℝ ↦ u - t) (Icc lo hi) (Icc 0 u) := by
    intro t ht
    change 0 ≤ u - t ∧ u - t ≤ u
    exact ⟨sub_nonneg.mpr (ht.2.trans hhiu), sub_le_self _ (hlo0.trans ht.1)⟩
  have hE := (continuousOn_gsScale_Icc_zero hchi hu1).comp hsub hsubMap
  have hg : ContinuousOn (fun t ↦ dickmanRho (gsScale chi (u - t)))
      (Icc lo hi) :=
    continuousOn_dickmanRho_Ici_zero.comp hE
      (fun t _ht ↦ (gsScale_pos chi (u - t)).le)
  have hg' : ContinuousOn (fun t ↦ dickmanRho (gsScale chi (u - t)))
      (uIcc lo hi) := by
    rw [uIcc_of_le hlohi]
    exact hg
  exact (hchi.1 lo hi).mul_continuousOn hg'

structure GSChampionCertificate
    (chi : ℝ → ℝ) (u e u₀ u₁ V a a₁ EV c tau tau' : ℝ) : Prop where
  huPos : 0 < u
  hu₀Pos : 0 < u₀
  hu₀u₁ : u₀ ≤ u₁
  hu₁1 : 1 ≤ u₁
  hu₁Pos : 0 < u₁
  hu₁u : u₁ ≤ u
  hV1 : 1 ≤ V
  hVPos : 0 < V
  hVu : V ≤ u
  haPos : 0 < a
  ha₁Pos : 0 < a₁
  hEVPos : 0 < EV
  hRhoDenPos : 0 < dickmanRho (e - 1)
  heMinusNonneg : 0 ≤ e - 1
  htau0 : 0 ≤ tau
  hloMid : e - 1 ≤ a₁ + tau
  hmidEnd : a₁ + tau ≤ a₁ + tau + tau'
  hEVEnd : EV ≤ a₁ + tau + tau'
  heVlower : e - 1 ≤ EV
  htauEq : tau + a₁ - e + 1 =
    EV / V * c * (gsB chi u - gsB chi u₁)
  htau'Eq : tau' = EV / V * (gsB chi u₁ - gsB chi u₀)
  hI3Condition : u - u / e ≤ V

lemma gs_champion_certificate
    {chi : ℝ → ℝ} (hchi : IsGSKernel chi)
    {u : ℝ} (hu1 : 1 ≤ u)
    (heLarge : (13 / 5 : ℝ) ≤ gsScale chi u)
    (hsmall : gsScale chi (u / gsScale chi u) ≤ gsScale chi u - 1) :
    let e := gsScale chi u
    let u₀ := u / e
    let u₁ := u - u₀
    let V := u - gsB chi u₀
    let a := gsScale chi u₀
    let a₁ := gsScale chi u₁
    let EV := gsScale chi V
    let c := dickmanRho a / dickmanRho (e - 1)
    let eta := u₀ * EV / V
    let tau := EV / V * c * (gsB chi u - gsB chi u₁) - a₁ + e - 1
    let tau' := EV / V * (gsB chi u₁ - gsB chi u₀)
    GSChampionCertificate chi u e u₀ u₁ V a a₁ EV c tau tau' := by
  let e := gsScale chi u
  let u₀ := u / e
  let u₁ := u - u₀
  let V := u - gsB chi u₀
  let a := gsScale chi u₀
  let a₁ := gsScale chi u₁
  let EV := gsScale chi V
  let c := dickmanRho a / dickmanRho (e - 1)
  let eta := u₀ * EV / V
  let tau := EV / V * c * (gsB chi u - gsB chi u₁) - a₁ + e - 1
  let tau' := EV / V * (gsB chi u₁ - gsB chi u₀)
  change GSChampionCertificate chi u e u₀ u₁ V a a₁ EV c tau tau'
  have hePos : 0 < e := gsScale_pos chi u
  have he : (13 / 5 : ℝ) ≤ e := by simpa only [e] using heLarge
  have he1 : 1 ≤ e := by linarith
  have huPos : 0 < u := zero_lt_one.trans_le hu1
  have heu : e ≤ u := by
    dsimp only [e]
    exact gsScale_le_self hchi hu1
  have hu₀1 : 1 ≤ u₀ := by
    dsimp only [u₀]
    exact (le_div_iff₀ hePos).mpr (by simpa using heu)
  have hu₀Pos : 0 < u₀ := zero_lt_one.trans_le hu₀1
  have huEq : u = e * u₀ := by
    dsimp only [u₀]
    field_simp [hePos.ne']
  have hu₁Eq : u₁ = (e - 1) * u₀ := by
    dsimp only [u₁]
    rw [huEq]
    ring
  have hu₀u₁ : u₀ ≤ u₁ := by
    rw [hu₁Eq]
    nlinarith
  have hu₁1 : 1 ≤ u₁ := hu₀1.trans hu₀u₁
  have hu₁Pos : 0 < u₁ := zero_lt_one.trans_le hu₁1
  have hu₁u : u₁ ≤ u := by
    dsimp only [u₁]
    linarith
  have hB₀nonneg : 0 ≤ gsB chi u₀ := gsB_nonneg hchi hu₀Pos.le
  have hB₀le : gsB chi u₀ ≤ u₀ := gsB_le hchi hu₀Pos.le
  have hVu : V ≤ u := by
    dsimp only [V]
    linarith
  have hu₁V : u₁ ≤ V := by
    dsimp only [V, u₁]
    linarith
  have hV1 : 1 ≤ V := hu₁1.trans hu₁V
  have hVPos : 0 < V := zero_lt_one.trans_le hV1
  have hu₀V : u₀ ≤ V := hu₀u₁.trans hu₁V
  have haPos : 0 < a := gsScale_pos chi u₀
  have ha1 : 1 ≤ a := by
    dsimp only [a]
    exact gsScale_ge_one hchi hu₀1
  have haSmall : a ≤ e - 1 := by
    simpa only [a, e, u₀] using hsmall
  have ha₁Pos : 0 < a₁ := gsScale_pos chi u₁
  have hEVPos : 0 < EV := gsScale_pos chi V
  have ha₁leEV : a₁ ≤ EV := by
    dsimp only [a₁, EV]
    exact gsScale_mono hchi hu₁1 hV1 hu₁V
  have hB₀lower : u₀ / a ≤ gsB chi u₀ := by
    dsimp only [a]
    exact gsB_ge_div_scale hchi hu₀1
  have hVupper : V ≤ u₀ * (e - a⁻¹) := by
    dsimp only [V]
    rw [huEq]
    field_simp [haPos.ne'] at hB₀lower ⊢
    nlinarith
  have hratioVu : e / u ≤ EV / V := by
    dsimp only [e, EV]
    exact gsScale_div_antitone hchi hV1 hVu
  have heta1 : 1 ≤ eta := by
    dsimp only [eta]
    have hscaled := mul_le_mul_of_nonneg_left hratioVu hu₀Pos.le
    rw [huEq] at hscaled
    field_simp [hePos.ne', hVPos.ne'] at hscaled ⊢
    nlinarith
  have hEVlambda : EV ≤ eta * (e - a⁻¹) := by
    dsimp only [eta]
    have hmul := mul_le_mul_of_nonneg_left hVupper
      (div_nonneg hEVPos.le hVPos.le)
    calc
      EV = EV / V * V := by field_simp [hVPos.ne']
      _ ≤ EV / V * (u₀ * (e - a⁻¹)) := hmul
      _ = u₀ * EV / V * (e - a⁻¹) := by ring
  have hetaA : eta ≤ a := by
    have hratio : EV / V ≤ a / u₀ := by
      dsimp only [EV, a]
      exact gsScale_div_antitone hchi hu₀1 hu₀V
    have hmul := mul_le_mul_of_nonneg_left hratio hu₀Pos.le
    dsimp only [eta]
    field_simp [hu₀Pos.ne', hVPos.ne'] at hmul ⊢
    nlinarith
  have ha₁lower : e - 1 ≤ a₁ := by
    have hratio : e / u ≤ a₁ / u₁ := by
      dsimp only [e, a₁]
      exact gsScale_div_antitone hchi hu₁1 hu₁u
    have hcross := (div_le_div_iff₀ huPos hu₁Pos).mp hratio
    rw [huEq, hu₁Eq] at hcross
    have hfactor : 0 < e * u₀ := mul_pos hePos hu₀Pos
    apply le_of_mul_le_mul_left (a := e * u₀) _ hfactor
    nlinarith
  have heMinusNonneg : 0 ≤ e - 1 := by linarith [he1]
  have hRhoDenPos : 0 < dickmanRho (e - 1) :=
    dickmanRho_profile.2.2.1 _ heMinusNonneg
  have hc1 : 1 ≤ c := by
    dsimp only [c]
    rw [one_le_div hRhoDenPos]
    exact antitoneOn_dickmanRho_Ici_zero haPos.le heMinusNonneg haSmall
  have hB₁leBV : gsB chi u₁ ≤ gsB chi V :=
    gsB_mono hchi hu₁Pos.le hVPos.le hu₁V
  have hupperGap : u * EV / e - V ≤ gsB chi u - gsB chi V := by
    simpa only [e, EV] using (gs_scale_bounds hchi hV1 hVu).1
  have hlowerGap : V * a / EV - u₀ ≤ gsB chi V - gsB chi u₀ := by
    simpa only [a, EV] using (gs_scale_bounds hchi hu₀1 hu₀V).1
  have hscalar := dickmanChampionScalar he ha1 haSmall heta1
  have htauEq : tau + a₁ - e + 1 =
      EV / V * c * (gsB chi u - gsB chi u₁) := by
    dsimp only [tau]
    ring
  have htau'Eq : tau' = EV / V * (gsB chi u₁ - gsB chi u₀) := rfl
  have htauCover : EV - a₁ ≤ tau + tau' := by
    exact gsChampionTauCondition he1 hu₀Pos hVPos hEVPos huEq rfl
      hetaA hEVlambda hscalar hc1 hB₁leBV hupperGap hlowerGap
      htauEq htau'Eq
  have hB₁nonneg : 0 ≤ gsB chi u₁ - gsB chi u₀ :=
    sub_nonneg.mpr (gsB_mono hchi hu₀Pos.le hu₁Pos.le hu₀u₁)
  have htau'0 : 0 ≤ tau' := by
    rw [htau'Eq]
    exact mul_nonneg (div_nonneg hEVPos.le hVPos.le) hB₁nonneg
  have hBtailLower :
      V / EV * (a₁ - e + 1) ≤ gsB chi u - gsB chi u₁ := by
    have hscale := (gs_scale_bounds hchi hu₁1 hu₁u).1
    have hVoverEV : V / EV ≤ u / e := by
      exact (div_le_div_iff₀ hEVPos hePos).mpr (by
        have h := hratioVu
        field_simp [huPos.ne', hVPos.ne'] at h ⊢
        nlinarith)
    have hterm0 : 0 ≤ a₁ - e + 1 := by linarith
    have hmul := mul_le_mul_of_nonneg_right hVoverEV hterm0
    change u * a₁ / e - u₁ ≤ gsB chi u - gsB chi u₁ at hscale
    calc
      V / EV * (a₁ - e + 1) ≤ u / e * (a₁ - e + 1) := hmul
      _ = u * a₁ / e - u₁ := by
        rw [huEq, hu₁Eq]
        field_simp [hePos.ne']
        <;> ring
      _ ≤ gsB chi u - gsB chi u₁ := hscale
  have htau0 : 0 ≤ tau := by
    have hscaled := mul_le_mul_of_nonneg_left hBtailLower
      (div_nonneg hEVPos.le hVPos.le)
    have hEVV : EV / V * (V / EV) = 1 := by
      field_simp [hEVPos.ne', hVPos.ne']
    have hmass0 : 0 ≤ gsB chi u - gsB chi u₁ :=
      sub_nonneg.mpr (gsB_mono hchi hu₁Pos.le huPos.le hu₁u)
    have hboost := mul_le_mul_of_nonneg_right hc1 hmass0
    have hmain : a₁ - e + 1 ≤
        EV / V * c * (gsB chi u - gsB chi u₁) := by
      calc
        a₁ - e + 1 = EV / V * (V / EV * (a₁ - e + 1)) := by
          field_simp [hVPos.ne', hEVPos.ne']
        _ ≤ EV / V * (gsB chi u - gsB chi u₁) := hscaled
        _ ≤ EV / V * (c * (gsB chi u - gsB chi u₁)) := by
          exact mul_le_mul_of_nonneg_left (by simpa using hboost)
            (div_nonneg hEVPos.le hVPos.le)
        _ = EV / V * c * (gsB chi u - gsB chi u₁) := by ring
    rw [show tau = EV / V * c * (gsB chi u - gsB chi u₁) -
        (a₁ - e + 1) by linear_combination htauEq]
    exact sub_nonneg.mpr hmain
  have hloMid : e - 1 ≤ a₁ + tau :=
    ha₁lower.trans (le_add_of_nonneg_right htau0)
  have hmidEnd : a₁ + tau ≤ a₁ + tau + tau' :=
    le_add_of_nonneg_right htau'0
  have hEVEnd : EV ≤ a₁ + tau + tau' := by
    linarith only [htauCover]
  have heVlower : e - 1 ≤ EV := ha₁lower.trans ha₁leEV
  have hI3Condition : u - u / e ≤ V := by
    have huDiv : u / e = u₀ := by rfl
    rw [huDiv]
    dsimp only [V]
    linarith
  exact ⟨huPos, hu₀Pos, hu₀u₁, hu₁1, hu₁Pos, hu₁u, hV1,
    hVPos, hVu, haPos, ha₁Pos, hEVPos, hRhoDenPos,
    heMinusNonneg, htau0, hloMid, hmidEnd, hEVEnd, heVlower,
    htauEq, htau'Eq, hI3Condition⟩

/-- The integral inequality (7.1) in the final, champion case. -/
theorem gs_champion_integral_inequality
    {chi : ℝ → ℝ} (hchi : IsGSKernel chi)
    {u : ℝ} (hu1 : 1 ≤ u)
    (heLarge : (13 / 5 : ℝ) ≤ gsScale chi u)
    (hsmall : gsScale chi (u / gsScale chi u) ≤ gsScale chi u - 1) :
    u * dickmanRho (gsScale chi u) ≤
      ∫ t : ℝ in 0..u, chi t * dickmanRho (gsScale chi (u - t)) := by
  let e := gsScale chi u
  let u₀ := u / e
  let u₁ := u - u₀
  let V := u - gsB chi u₀
  let a := gsScale chi u₀
  let a₁ := gsScale chi u₁
  let EV := gsScale chi V
  let c := dickmanRho a / dickmanRho (e - 1)
  let eta := u₀ * EV / V
  let tau := EV / V * c * (gsB chi u - gsB chi u₁) - a₁ + e - 1
  let tau' := EV / V * (gsB chi u₁ - gsB chi u₀)
  have hcert0 := gs_champion_certificate hchi hu1 heLarge hsmall
  change GSChampionCertificate chi u e u₀ u₁ V a a₁ EV c tau tau' at hcert0
  rcases hcert0 with
    ⟨huPos, hu₀Pos, hu₀u₁, hu₁1, hu₁Pos, hu₁u, hV1, hVPos,
      hVu, haPos, ha₁Pos, hEVPos, hRhoDenPos, heMinusNonneg, htau0,
      hloMid, hmidEnd, hEVEnd, heVlower, htauEq, htau'Eq,
      hI3Condition⟩
  have hfullInt : IntervalIntegrable
      (fun t ↦ chi t * dickmanRho (gsScale chi (u - t))) volume 0 u :=
    intervalIntegrable_gsWeightedDickmanSub hchi hu1 (by norm_num)
      huPos.le le_rfl
  have hI₁Int : IntervalIntegrable
      (fun t ↦ chi t * dickmanRho (gsScale chi (u - t))) volume u₁ u :=
    intervalIntegrable_gsWeightedDickmanSub hchi hu1 hu₁Pos.le hu₁u le_rfl
  have hI₂Int : IntervalIntegrable
      (fun t ↦ chi t * dickmanRho (gsScale chi (u - t))) volume u₀ u₁ :=
    intervalIntegrable_gsWeightedDickmanSub hchi hu1 hu₀Pos.le hu₀u₁ hu₁u
  have hI₃Int : IntervalIntegrable
      (fun t ↦ chi t * dickmanRho (gsScale chi (u - t))) volume 0 u₀ :=
    intervalIntegrable_gsWeightedDickmanSub hchi hu1 (by norm_num)
      hu₀Pos.le (hu₀u₁.trans hu₁u)
  have hI₁constant :
      dickmanRho a * (gsB chi u - gsB chi u₁) ≤
        ∫ t : ℝ in u₁..u,
          chi t * dickmanRho (gsScale chi (u - t)) := by
    apply gs_weighted_interval_lower hchi hu₁Pos.le hu₁u hI₁Int
    intro t ht
    rcases ht with ⟨htl, htr⟩
    have hs0 : 0 ≤ u - t := sub_nonneg.mpr htr
    have hsu₀ : u - t ≤ u₀ := by
      dsimp only [u₁] at htl
      linarith
    have hscale := gsScale_mono_Ici_zero hchi hs0 hu₀Pos.le hsu₀
    exact antitoneOn_dickmanRho_Ici_zero (gsScale_pos chi (u - t)).le
      haPos.le hscale
  have hI₂constant :
      dickmanRho a₁ * (gsB chi u₁ - gsB chi u₀) ≤
        ∫ t : ℝ in u₀..u₁,
          chi t * dickmanRho (gsScale chi (u - t)) := by
    apply gs_weighted_interval_lower hchi hu₀Pos.le hu₀u₁ hI₂Int
    intro t ht
    rcases ht with ⟨htl, htr⟩
    have hs0 : 0 ≤ u - t := sub_nonneg.mpr (htr.trans hu₁u)
    have hsu₁ : u - t ≤ u₁ := by
      dsimp only [u₁]
      linarith
    have hscale := gsScale_mono_Ici_zero hchi hs0 hu₁Pos.le hsu₁
    exact antitoneOn_dickmanRho_Ici_zero (gsScale_pos chi (u - t)).le
      ha₁Pos.le hscale
  have hI₁length :
      V / EV * ((a₁ + tau) - (e - 1)) =
        c * (gsB chi u - gsB chi u₁) := by
    rw [show (a₁ + tau) - (e - 1) =
        EV / V * c * (gsB chi u - gsB chi u₁) by
      linarith [htauEq]]
    field_simp [hVPos.ne', hEVPos.ne']
  have hI₁scaled :
      V / EV * (∫ t : ℝ in (e - 1)..(a₁ + tau), dickmanRho t) ≤
        dickmanRho a * (gsB chi u - gsB chi u₁) := by
    have hbound := scaled_dickman_interval_upper
      (base := e - 1) (lo := e - 1) (hi := a₁ + tau)
      (alpha := V / EV) (mass := c * (gsB chi u - gsB chi u₁))
      (by linarith) le_rfl hloMid (div_nonneg hVPos.le hEVPos.le) hI₁length
    have hcIdentity :
        dickmanRho (e - 1) * (c * (gsB chi u - gsB chi u₁)) =
          dickmanRho a * (gsB chi u - gsB chi u₁) := by
      dsimp only [c]
      field_simp [hRhoDenPos.ne']
    simpa only [hcIdentity] using hbound
  have hI₂length :
      V / EV * ((a₁ + tau + tau') - (a₁ + tau)) =
        gsB chi u₁ - gsB chi u₀ := by
    rw [htau'Eq]
    field_simp [hVPos.ne', hEVPos.ne']
    ring
  have hI₂scaled :
      V / EV * (∫ t : ℝ in (a₁ + tau)..(a₁ + tau + tau'),
        dickmanRho t) ≤
        dickmanRho a₁ * (gsB chi u₁ - gsB chi u₀) := by
    exact scaled_dickman_interval_upper
      (base := a₁) (lo := a₁ + tau) (hi := a₁ + tau + tau')
      (alpha := V / EV) (mass := gsB chi u₁ - gsB chi u₀)
      ha₁Pos.le (le_add_of_nonneg_right htau0) hmidEnd
      (div_nonneg hVPos.le hEVPos.le)
      hI₂length
  have hI₁ :
      V / EV * (∫ t : ℝ in (e - 1)..(a₁ + tau), dickmanRho t) ≤
        ∫ t : ℝ in u₁..u,
          chi t * dickmanRho (gsScale chi (u - t)) :=
    hI₁scaled.trans hI₁constant
  have hI₂ :
      V / EV * (∫ t : ℝ in (a₁ + tau)..(a₁ + tau + tau'),
          dickmanRho t) ≤
        ∫ t : ℝ in u₀..u₁,
          chi t * dickmanRho (gsScale chi (u - t)) :=
    hI₂scaled.trans hI₂constant
  have hI₃pre := gs_champion_I3_preliminary hchi hu₀Pos.le
    (by linarith [hu₁1] : u₀ ≤ u - 1) (by rfl : V = u - gsB chi u₀)
  have hI₃dick := gs_champion_dickman_integral_lower hchi hV1 hVu
    (by simpa only [e] using hI3Condition)
  have hI₃ :
      u * dickmanRho e -
          V / EV * (∫ t : ℝ in (e - 1)..EV, dickmanRho t) ≤
        ∫ t : ℝ in 0..u₀,
          chi t * dickmanRho (gsScale chi (u - t)) := by
    have hI₃dick' :
        u * dickmanRho e -
            V / EV * (∫ t : ℝ in (e - 1)..EV, dickmanRho t) ≤
          ∫ t : ℝ in V..u, dickmanRho (gsScale chi t) := by
      simpa only [e, EV] using hI₃dick
    exact hI₃dick'.trans hI₃pre
  have hrhoInt : IntervalIntegrable dickmanRho volume (e - 1)
      (a₁ + tau + tau') :=
    intervalIntegrable_dickmanRho_of_nonneg (by linarith)
      (by linarith [hEVPos] : 0 ≤ a₁ + tau + tau')
  have hp := gsChampionIntegralPieces
    (rho := dickmanRho) (lo := e - 1) (mid := a₁ + tau)
    (EV := EV) (endpoint := a₁ + tau + tau')
    (I₁ := ∫ t : ℝ in u₁..u,
      chi t * dickmanRho (gsScale chi (u - t)))
    (I₂ := ∫ t : ℝ in u₀..u₁,
      chi t * dickmanRho (gsScale chi (u - t)))
    (I₃ := ∫ t : ℝ in 0..u₀,
      chi t * dickmanRho (gsScale chi (u - t)))
    (u := u) (rhoe := dickmanRho e) (alpha := V / EV)
    hloMid hmidEnd heVlower hEVEnd hrhoInt
    (fun t ht ↦ dickmanRho_nonneg (by linarith [ht.1]))
    (div_nonneg hVPos.le hEVPos.le) hI₃ hI₁ hI₂
  have hsplit₀₁ := intervalIntegral.integral_add_adjacent_intervals hI₃Int hI₂Int
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hI₃Int.trans hI₂Int) hI₁Int
  dsimp only [e] at hp ⊢
  linarith

end

end Erdos783
