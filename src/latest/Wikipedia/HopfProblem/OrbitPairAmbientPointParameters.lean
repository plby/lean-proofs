import Wikipedia.HopfProblem.OrbitPairSupportedAmbientClock
import Wikipedia.SmoothSixDPoincare.ManifoldImageDimension

/-!
# Ambient clock parameters controlling a selected projected value

For one prescribed source point, a new coincidence with any other source
point having a different clock weight determines the translation parameter.
The bad-parameter map has the dimension of the whole family source, not
twice that dimension. Good parameters leave only old coincidences with
equal clock weights. The map being perturbed is the actual supported
ambient clock family, so sufficiently small parameters are slice-wise
ambient diffeomorphisms.
-/

noncomputable section

open Set Function Filter
open scoped ContDiff Manifold Topology

namespace Wikipedia.HopfProblem.OrbitPair.AmbientPointParameters

open Wikipedia.SmoothSixDPoincare ClockVelocity

variable {V E G H K M N : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace H] [TopologicalSpace K]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ G K}
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace K N] [T2Space N]
  (Φ : PartialDiffeomorph 𝓘(ℝ, V) J V N ∞)
  (F : ℝ × M → N) (β : V → ℝ) (κ : ℝ → ℝ)

def weight (p : ℝ × M) : ℝ := β (Φ.symm (F p)) * κ p.1

def family (a : V) : ℝ × M → N :=
  NativeFamily.ambientFamily F (clockAmbient Φ β κ a)

def badDomain (q : ℝ × M) : Set (ℝ × M) :=
  {p | F p ∈ Φ.target ∧ weight Φ F β κ q - weight Φ F β κ p ≠ 0}

def badParameter (q p : ℝ × M) : V :=
  (weight Φ F β κ q - weight Φ F β κ p)⁻¹ • (Φ.symm (F p) - Φ.symm (F q))

theorem family_fixed_of_not_mem (a : V) {p : ℝ × M} (hp : F p ∉ Φ.target) :
    family Φ F β κ a p = F p := by
  change SupportedDiffeomorph.extendMap Φ
    (fun z => z + β z • (κ p.1 • a)) (F p) = F p
  exact SupportedDiffeomorph.extendMap_of_notMem Φ _ hp

theorem coincidence_imp_old_of_not_mem {a : V}
    (hmap : ∀ t : ℝ, MapsTo (fun z => z + β z • (κ t • a)) Φ.source Φ.source)
    {q : ℝ × M} (hq : F q ∉ Φ.target) (p : ℝ × M)
    (hqp : family Φ F β κ a q = family Φ F β κ a p) : F q = F p := by
  have hqfixed := family_fixed_of_not_mem Φ F β κ a hq
  by_cases hp : F p ∈ Φ.target
  · have hpnew : family Φ F β κ a p ∈ Φ.target :=
      SupportedDiffeomorph.bumpFamily_mem_target Φ β (κ p.1 • a) (hmap p.1) hp
    rw [← hqp, hqfixed] at hpnew
    exact False.elim (hq hpnew)
  · exact hqfixed.symm.trans (hqp.trans (family_fixed_of_not_mem Φ F β κ a hp))

theorem smooth_weight (hF : ContMDiff (𝓘(ℝ, ℝ).prod I) J ∞ F)
    (hβ : ContDiff ℝ ∞ β) (hκ : ContDiff ℝ ∞ κ) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (weight Φ F β κ) (F ⁻¹' Φ.target) := by
  have hc : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, V) ∞
      (fun p : ℝ × M => Φ.symm (F p)) (F ⁻¹' Φ.target) :=
    Φ.contMDiffOn_invFun.comp hF.contMDiffOn (fun _ hp => hp)
  have hb := hβ.contMDiff.comp_contMDiffOn hc
  have hk : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => κ p.1) (F ⁻¹' Φ.target) :=
    (hκ.contMDiff.comp contMDiff_fst).contMDiffOn
  exact hb.smul hk

theorem badDomain_isOpen (hF : ContMDiff (𝓘(ℝ, ℝ).prod I) J ∞ F)
    (hβ : ContDiff ℝ ∞ β) (hκ : ContDiff ℝ ∞ κ) (q : ℝ × M) :
    IsOpen (badDomain Φ F β κ q) := by
  have hU := Φ.open_target.preimage hF.continuous
  have hw := smooth_weight Φ F β κ hF hβ hκ
  exact (continuousOn_const.sub hw.continuousOn).isOpen_inter_preimage hU
    (isOpen_ne_fun continuous_id continuous_const)

theorem smooth_badParameter (hF : ContMDiff (𝓘(ℝ, ℝ).prod I) J ∞ F)
    (hβ : ContDiff ℝ ∞ β) (hκ : ContDiff ℝ ∞ κ) (q : ℝ × M) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, V) ∞
      (badParameter Φ F β κ q) (badDomain Φ F β κ q) := by
  intro p hp
  have hU := Φ.open_target.preimage hF.continuous
  have hw := (smooth_weight Φ F β κ hF hβ hκ).contMDiffAt (hU.mem_nhds hp.1)
  have hc := (Φ.contMDiffOn_invFun.contMDiffAt (Φ.open_target.mem_nhds hp.1)).comp p
    hF.contMDiffAt
  exact (((contMDiffAt_const.sub hw).inv₀ hp.2).smul
    (hc.sub contMDiffAt_const)).contMDiffWithinAt

theorem coincidence_imp_old_and_equal_weight {a : V}
    (hmap : ∀ t : ℝ, MapsTo (fun z => z + β z • (κ t • a)) Φ.source Φ.source)
    {q : ℝ × M} (hq : F q ∈ Φ.target)
    (hgood : a ∉ badParameter Φ F β κ q '' badDomain Φ F β κ q)
    (p : ℝ × M) (hqp : family Φ F β κ a q = family Φ F β κ a p) :
    F q = F p ∧ weight Φ F β κ q = weight Φ F β κ p := by
  have hqnew : family Φ F β κ a q ∈ Φ.target :=
    SupportedDiffeomorph.bumpFamily_mem_target Φ β (κ q.1 • a) (hmap q.1) hq
  have hpnew : family Φ F β κ a p ∈ Φ.target := hqp ▸ hqnew
  have hp : F p ∈ Φ.target := by
    by_contra hp
    have heq := family_fixed_of_not_mem Φ F β κ a hp
    rw [heq] at hpnew
    exact hp hpnew
  have hqcoord := SupportedDiffeomorph.bumpFamily_coordinates Φ β (κ q.1 • a) (hmap q.1) hq
  have hpcoord := SupportedDiffeomorph.bumpFamily_coordinates Φ β (κ p.1 • a) (hmap p.1) hp
  have hcoord : Φ.symm (F q) + weight Φ F β κ q • a =
      Φ.symm (F p) + weight Φ F β κ p • a := by
    simpa only [weight, mul_smul] using
      hqcoord.symm.trans ((congrArg Φ.symm hqp).trans hpcoord)
  by_cases hw : weight Φ F β κ q = weight Φ F β κ p
  · rw [hw] at hcoord
    exact ⟨Φ.symm.toPartialEquiv.injOn hq hp (add_right_cancel hcoord), hw⟩
  · exfalso
    apply hgood
    have hd : weight Φ F β κ q - weight Φ F β κ p ≠ 0 := sub_ne_zero.mpr hw
    refine ⟨p, ⟨hp, hd⟩, ?_⟩
    have hs : (weight Φ F β κ q - weight Φ F β κ p) • a =
        Φ.symm (F p) - Φ.symm (F q) := by
      rw [sub_smul]
      exact sub_eq_sub_iff_add_eq_add.mpr (by simpa only [add_comm] using hcoord)
    change (weight Φ F β κ q - weight Φ F β κ p)⁻¹ •
      (Φ.symm (F p) - Φ.symm (F q)) = a
    rw [← hs, inv_smul_smul₀ hd]

variable [FiniteDimensional ℝ E] [IsManifold I ∞ M] [LindelofSpace (ℝ × M)]

theorem exists_small_clock_no_new_point_coincidences
    (hF : ContMDiff (𝓘(ℝ, ℝ).prod I) J ∞ F)
    (hβ : ContDiff ℝ ∞ β) (hcompact : HasCompactSupport β)
    (hsupport : tsupport β ⊆ Φ.source)
    (hκ : ContDiff ℝ ∞ κ) (hbound : ∀ t, ‖κ t‖ ≤ 1)
    (q : ℝ × M) (hq : F q ∈ Φ.target)
    (hdim : Module.finrank ℝ (ℝ × E) < Module.finrank ℝ V)
    {R : V → Prop} (hR : ∀ᶠ a in 𝓝 (0 : V), R a) {ε : ℝ} (hε : 0 < ε) :
    ∃ a : V, ‖a‖ < ε ∧ R a ∧
      ∀ p : ℝ × M, family Φ F β κ a q = family Φ F β κ a p →
        F q = F p ∧ weight Φ F β κ q = weight Φ F β κ p := by
  have hdense := GeneralPosition.dense_compl_manifold_image
    (badDomain_isOpen Φ F β κ hF hβ hκ q)
    (smooth_badParameter Φ F β κ hF hβ hκ q) hdim
  obtain ⟨η, hη, -, -, hmap⟩ :=
    SupportedDiffeomorph.exists_radius_ambient_bumpFamily Φ hβ hcompact hsupport
  obtain ⟨δ, hδ, hδR⟩ := Metric.eventually_nhds_iff.mp hR
  obtain ⟨a, hgood, hnorm⟩ := hdense.exists_dist_lt 0 (lt_min hε (lt_min hη hδ))
  have ha : ‖a‖ < min ε (min η δ) := by simpa only [dist_zero_left] using hnorm
  have haη : ‖a‖ < η := ha.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have haδ : ‖a‖ < δ := ha.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hm : ∀ t : ℝ, MapsTo (fun z => z + β z • (κ t • a)) Φ.source Φ.source := by
    intro t
    apply hmap (κ t • a)
    calc
      ‖κ t • a‖ = ‖κ t‖ * ‖a‖ := norm_smul _ _
      _ ≤ 1 * ‖a‖ := mul_le_mul_of_nonneg_right (hbound t) (norm_nonneg a)
      _ = ‖a‖ := one_mul _
      _ < η := haη
  refine ⟨a, ha.trans_le (min_le_left _ _), ?_, ?_⟩
  · exact hδR (by simpa only [dist_zero_right] using haδ)
  · exact fun p hp => coincidence_imp_old_and_equal_weight Φ F β κ hm hq hgood p hp

theorem exists_small_clock_no_new_finite_point_coincidences
    (hF : ContMDiff (𝓘(ℝ, ℝ).prod I) J ∞ F)
    (hβ : ContDiff ℝ ∞ β) (hcompact : HasCompactSupport β)
    (hsupport : tsupport β ⊆ Φ.source)
    (hκ : ContDiff ℝ ∞ κ) (hbound : ∀ t, ‖κ t‖ ≤ 1)
    {S : Set (ℝ × M)} (hS : S.Finite)
    (hdim : Module.finrank ℝ (ℝ × E) < Module.finrank ℝ V)
    {R : V → Prop} (hR : ∀ᶠ a in 𝓝 (0 : V), R a) {ε : ℝ} (hε : 0 < ε) :
    ∃ a : V, ‖a‖ < ε ∧ R a ∧
      ∀ q ∈ S, ∀ p : ℝ × M, family Φ F β κ a q = family Φ F β κ a p →
        F q = F p ∧ (F q ∈ Φ.target → weight Φ F β κ q = weight Φ F β κ p) := by
  let B : Set V := ⋃ q ∈ S, badParameter Φ F β κ q '' badDomain Φ F β κ q
  have hBdim : dimH B ≤ (Module.finrank ℝ (ℝ × E) : ENNReal) := by
    rw [show B = ⋃ q ∈ S, badParameter Φ F β κ q '' badDomain Φ F β κ q from rfl,
      dimH_bUnion hS.countable]
    exact iSup₂_le (fun q _ => GeneralPosition.dimH_image_manifold_le
      (badDomain_isOpen Φ F β κ hF hβ hκ q) (smooth_badParameter Φ F β κ hF hβ hκ q))
  have hdense : Dense Bᶜ :=
    dense_compl_of_dimH_lt_finrank (hBdim.trans_lt (Nat.cast_lt.mpr hdim))
  obtain ⟨η, hη, -, -, hmap⟩ :=
    SupportedDiffeomorph.exists_radius_ambient_bumpFamily Φ hβ hcompact hsupport
  obtain ⟨δ, hδ, hδR⟩ := Metric.eventually_nhds_iff.mp hR
  obtain ⟨a, hgood, hnorm⟩ := hdense.exists_dist_lt 0 (lt_min hε (lt_min hη hδ))
  have ha : ‖a‖ < min ε (min η δ) := by simpa only [dist_zero_left] using hnorm
  have haη : ‖a‖ < η := ha.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have haδ : ‖a‖ < δ := ha.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hm : ∀ t : ℝ, MapsTo (fun z => z + β z • (κ t • a)) Φ.source Φ.source := by
    intro t
    apply hmap (κ t • a)
    calc
      ‖κ t • a‖ = ‖κ t‖ * ‖a‖ := norm_smul _ _
      _ ≤ 1 * ‖a‖ := mul_le_mul_of_nonneg_right (hbound t) (norm_nonneg a)
      _ = ‖a‖ := one_mul _
      _ < η := haη
  refine ⟨a, ha.trans_le (min_le_left _ _), ?_, ?_⟩
  · exact hδR (by simpa only [dist_zero_right] using haδ)
  · intro q hq p hqp
    by_cases hqt : F q ∈ Φ.target
    · have hqgood : a ∉ badParameter Φ F β κ q '' badDomain Φ F β κ q :=
        fun h => hgood (mem_iUnion₂.mpr ⟨q, hq, h⟩)
      have hh := coincidence_imp_old_and_equal_weight Φ F β κ hm hqt hqgood p hqp
      exact ⟨hh.1, fun _ => hh.2⟩
    · exact ⟨coincidence_imp_old_of_not_mem Φ F β κ hm hqt p hqp,
        fun h => False.elim (hqt h)⟩

end Wikipedia.HopfProblem.OrbitPair.AmbientPointParameters
