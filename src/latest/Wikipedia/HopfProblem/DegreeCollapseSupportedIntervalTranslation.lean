import Wikipedia.SmoothSixDPoincare.BumpTranslationDiffeomorph
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Supported scalar diffeomorphisms with a prescribed translation germ

Small bump translations give actual smooth diffeomorphisms with full
translation germs. Composition, inverse germs, and connectedness of the
open interval extend this to any two interior heights, fixing every
exterior height. These are the scalar profiles for native rearrangement.
-/

noncomputable section

open Set Function Filter Metric
open scoped ContDiff Manifold Topology
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseRearrangement

def IntervalTranslation (a b x y : ℝ) : Prop :=
  ∃ D : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞,
    (∀ z, z ∉ Ioo a b → D z = z) ∧ D =ᶠ[𝓝 x] fun z => z + (y - x)

theorem translation_germ_apply
    (D : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞) {x y : ℝ}
    (hD : D =ᶠ[𝓝 x] fun z => z + (y - x)) : D x = y := by
  have h := hD.self_of_nhds
  linarith

theorem intervalTranslation_refl (a b x : ℝ) : IntervalTranslation a b x x := by
  refine ⟨Diffeomorph.refl 𝓘(ℝ, ℝ) ℝ ∞, fun _ _ => rfl, Eventually.of_forall ?_⟩
  intro z
  change z = z + (x - x)
  ring

theorem intervalTranslation_symm {a b x y : ℝ} (h : IntervalTranslation a b x y) :
    IntervalTranslation a b y x := by
  obtain ⟨D, hfix, hgerm⟩ := h
  have hxy := translation_germ_apply D hgerm
  have hback : D.symm y = x := by rw [← hxy, D.symm_apply_apply]
  have ht : Tendsto D.symm (𝓝 y) (𝓝 x) := hback ▸ D.symm.continuous.continuousAt.tendsto
  refine ⟨D.symm, ?_, ?_⟩
  · intro z hz
    have hh := D.symm_apply_apply z
    rwa [hfix z hz] at hh
  · filter_upwards [hgerm.comp_tendsto ht] with z hz
    change D (D.symm z) = D.symm z + (y - x) at hz
    rw [D.apply_symm_apply] at hz
    linarith

theorem intervalTranslation_trans {a b x y z : ℝ}
    (hxy : IntervalTranslation a b x y) (hyz : IntervalTranslation a b y z) :
    IntervalTranslation a b x z := by
  obtain ⟨D, hDfix, hD⟩ := hxy
  obtain ⟨G, hGfix, hG⟩ := hyz
  have hxy := translation_germ_apply D hD
  have ht : Tendsto D (𝓝 x) (𝓝 y) := hxy ▸ D.continuous.continuousAt.tendsto
  refine ⟨D.trans G, ?_, ?_⟩
  · intro w hw
    change G (D w) = w
    rw [hDfix w hw, hGfix w hw]
  · filter_upwards [hD, hG.comp_tendsto ht] with w hwD hwG
    change G (D w) = w + (z - x)
    change G (D w) = D w + (z - y) at hwG
    rw [hwG, hwD]
    ring

theorem exists_local_interval_translation {a b x : ℝ} (hx : x ∈ Ioo a b) :
    ∃ ε, 0 < ε ∧ ∀ y, dist y x < ε → IntervalTranslation a b x y := by
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp (isOpen_Ioo.mem_nhds hx)
  let β : ContDiffBump x := ⟨r / 4, r / 2, by positivity, by linarith⟩
  have hsupp : tsupport (fun z : ℝ => β z) ⊆ Ioo a b := by
    rw [β.tsupport_eq]
    intro z hz
    apply hsub
    have hh : dist z x ≤ r / 2 := hz
    change dist z x < r
    linarith
  have hcompact : HasCompactSupport (fun z : ℝ => β z) := by
    change IsCompact (tsupport (fun z : ℝ => β z))
    rw [β.tsupport_eq]
    exact isCompact_closedBall _ _
  obtain ⟨ε, hε, hmove⟩ := SmallPerturbation.exists_radius_bumpTranslation β.contDiff hcompact
  refine ⟨ε, hε, ?_⟩
  intro y hy
  have hnorm : ‖y - x‖ < ε := by simpa only [dist_eq_norm] using hy
  obtain ⟨D, hD, hfix⟩ := hmove (y - x) hnorm
  refine ⟨D, fun z hz => hfix z (fun h => hz (hsupp h)), ?_⟩
  filter_upwards [ball_mem_nhds x β.rIn_pos] with z hz
  rw [hD, β.one_of_mem_closedBall (ball_subset_closedBall hz), one_smul]

theorem exists_supported_interval_translation {a b x y : ℝ}
    (hx : x ∈ Ioo a b) (hy : y ∈ Ioo a b) : IntervalTranslation a b x y := by
  let U := Ioo a b
  let P : U → Prop := fun z => IntervalTranslation a b x z
  have hlocal : IsLocallyConstant P := by
    apply (IsLocallyConstant.iff_eventually_eq P).mpr
    intro z
    obtain ⟨ε, hε, hmove⟩ := exists_local_interval_translation z.property
    filter_upwards [Metric.ball_mem_nhds z hε] with w hw
    have hzw : IntervalTranslation a b z w := hmove w hw
    apply propext
    exact ⟨fun hw => intervalTranslation_trans hw (intervalTranslation_symm hzw),
      fun hz => intervalTranslation_trans hz hzw⟩
  let _ : PreconnectedSpace U := isPreconnected_iff_preconnectedSpace.mp isPreconnected_Ioo
  have heq : P ⟨x, hx⟩ = P ⟨y, hy⟩ := hlocal.apply_eq_of_preconnectedSpace ⟨x, hx⟩ ⟨y, hy⟩
  have hstart : P ⟨x, hx⟩ := intervalTranslation_refl a b x
  have hfinish : P ⟨y, hy⟩ := heq ▸ hstart
  exact hfinish

theorem strictMono_of_fixed_exterior
    (D : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞) {a b : ℝ}
    (hfix : ∀ z, z ∉ Ioo a b → D z = z) : StrictMono D := by
  rcases D.continuous.strictMono_of_inj D.injective with hm | ha
  · exact hm
  · have hanti := ha (show b < b + 1 by linarith)
    rw [hfix b (fun h => (lt_irrefl b) h.2), hfix (b + 1) (fun h => by linarith [h.2])] at hanti
    linarith

theorem deriv_pos_of_strictMono_diffeomorph
    (D : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞) (hm : StrictMono D) (x : ℝ) :
    0 < deriv D x := by
  have hd := (D.mdifferentiable (by simp) x).differentiableAt.hasDerivAt
  have hi := (D.symm.mdifferentiable (by simp) (D x)).differentiableAt.hasDerivAt
  have hc := hi.comp x hd
  have heq : D.symm ∘ D = id := funext D.symm_apply_apply
  rw [heq] at hc
  have hh := hc.unique (hasDerivAt_id x)
  have hn : deriv D x ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hh
    norm_num at hh
  exact lt_of_le_of_ne hm.monotone.deriv_nonneg (Ne.symm hn)

theorem exists_increasing_interval_translation {a b x y : ℝ}
    (hx : x ∈ Ioo a b) (hy : y ∈ Ioo a b) :
    ∃ D : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞,
      (∀ z, z ∉ Ioo a b → D z = z) ∧ (D =ᶠ[𝓝 x] fun z => z + (y - x)) ∧
      D x = y ∧ StrictMono D ∧ ∀ z, 0 < deriv D z := by
  obtain ⟨D, hfix, hgerm⟩ := exists_supported_interval_translation hx hy
  have hm := strictMono_of_fixed_exterior D hfix
  exact ⟨D, hfix, hgerm, translation_germ_apply D hgerm, hm,
    deriv_pos_of_strictMono_diffeomorph D hm⟩

theorem exists_increasing_interval_translation_with_exterior_germs {a b x y : ℝ}
    (hx : x ∈ Ioo a b) (hy : y ∈ Ioo a b) :
    ∃ D : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞,
      (∀ z, z ∉ Ioo a b → D z = z) ∧ (D =ᶠ[𝓝 x] fun z => z + (y - x)) ∧
      D x = y ∧ StrictMono D ∧ (∀ z, 0 < deriv D z) ∧
      ∀ z, z ∉ Ioo a b → D =ᶠ[𝓝 z] id := by
  obtain ⟨a', haa', ha'⟩ := exists_between (lt_min hx.1 hy.1)
  obtain ⟨b', hb', hb'b⟩ := exists_between (max_lt hx.2 hy.2)
  have hx' : x ∈ Ioo a' b' :=
    ⟨ha'.trans_le (min_le_left _ _), (le_max_left _ _).trans_lt hb'⟩
  have hy' : y ∈ Ioo a' b' :=
    ⟨ha'.trans_le (min_le_right _ _), (le_max_right _ _).trans_lt hb'⟩
  obtain ⟨D, hfix, hgerm, hpoint, hmono, hderiv⟩ := exists_increasing_interval_translation hx' hy'
  have hsub : Icc a' b' ⊆ Ioo a b := fun z hz => ⟨haa'.trans_le hz.1, hz.2.trans_lt hb'b⟩
  have hout (z : ℝ) (hz : z ∉ Ioo a b) : D =ᶠ[𝓝 z] id := by
    have hz' : z ∈ (Icc a' b')ᶜ := fun h => hz (hsub h)
    filter_upwards [isClosed_Icc.isOpen_compl.mem_nhds hz'] with w hw
    exact hfix w (fun h => hw ⟨h.1.le, h.2.le⟩)
  exact ⟨D, fun z hz => (hout z hz).self_of_nhds, hgerm, hpoint, hmono, hderiv, hout⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseRearrangement
