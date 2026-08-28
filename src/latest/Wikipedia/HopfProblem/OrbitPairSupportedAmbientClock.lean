import Wikipedia.HopfProblem.OrbitPairAmbientFamily
import Wikipedia.SmoothSixDPoincare.AmbientBumpTranslations

/-!
# Supported native ambient clock perturbations

A bounded smooth clock drives an actual ambient bump diffeomorphism. The
construction is jointly smooth, is the identity where the clock vanishes
or outside the target cutoff, and has the exact weighted translation
formula in the original chart. When applied to a native surface family,
it retains all synchronized collisions, spatial immersion, and regularity.

The separate task of choosing this clock and chart to prepare an immersive
projected corridor is not assumed to have been completed here.
-/

noncomputable section

open Set Function
open scoped ContDiff Manifold Topology

namespace Wikipedia.HopfProblem.OrbitPair.ClockVelocity

open Wikipedia.SmoothSixDPoincare

variable {V G K N : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace K]
  {J : ModelWithCorners ℝ G K}
  [TopologicalSpace N] [ChartedSpace K N] [T2Space N]
  (Φ : PartialDiffeomorph 𝓘(ℝ, V) J V N ∞)

def clockAmbient (β : V → ℝ) (κ : ℝ → ℝ) (a : V) (p : ℝ × N) : N :=
  SupportedDiffeomorph.bumpFamily Φ β (κ p.1 • a, p.2)

theorem exists_radius_clockAmbient {β : V → ℝ} {κ : ℝ → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hcompact : HasCompactSupport β)
    (hsupport : tsupport β ⊆ Φ.source)
    (hκ : ContDiff ℝ ∞ κ) (hbound : ∀ t, ‖κ t‖ ≤ 1) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ a : V, ‖a‖ < ε →
      ContMDiff (𝓘(ℝ, ℝ).prod J) J ∞ (clockAmbient Φ β κ a) ∧
      (∀ t, ∃ D : Diffeomorph J J N N ∞,
        ∀ y, D y = clockAmbient Φ β κ a (t, y)) ∧
      (∀ t y, κ t = 0 ∨ y ∉ Φ '' tsupport β →
        clockAmbient Φ β κ a (t, y) = y) ∧
      (∀ t y, y ∈ Φ.target →
        Φ.symm (clockAmbient Φ β κ a (t, y)) =
          Φ.symm y + β (Φ.symm y) • (κ t • a)) := by
  obtain ⟨ε, hε, hdiff, hsmooth, hmap⟩ :=
    SupportedDiffeomorph.exists_radius_ambient_bumpFamily Φ hβ hcompact hsupport
  refine ⟨ε, hε, ?_⟩
  intro a ha
  have hsmall (t : ℝ) : ‖κ t • a‖ < ε := by
    calc
      ‖κ t • a‖ = ‖κ t‖ * ‖a‖ := norm_smul _ _
      _ ≤ 1 * ‖a‖ := mul_le_mul_of_nonneg_right (hbound t) (norm_nonneg a)
      _ = ‖a‖ := one_mul _
      _ < ε := ha
  have hin : ContMDiff (𝓘(ℝ, ℝ).prod J) (𝓘(ℝ, V).prod J) ∞
      (fun p : ℝ × N => (κ p.1 • a, p.2)) :=
    ((hκ.contMDiff.comp contMDiff_fst).smul contMDiff_const).prodMk contMDiff_snd
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p
    exact (hsmooth (κ p.1 • a, p.2) (hsmall p.1)).comp p (hin p)
  · intro t
    exact hdiff (κ t • a) (hsmall t)
  · intro t y hy
    rcases hy with hzero | hout
    · change SupportedDiffeomorph.bumpFamily Φ β (κ t • a, y) = y
      rw [hzero, zero_smul]
      exact SupportedDiffeomorph.bumpFamily_zero Φ β y
    · exact SupportedDiffeomorph.bumpFamily_fixed_outside Φ β (κ t • a) hout
  · intro t y hy
    exact SupportedDiffeomorph.bumpFamily_coordinates Φ β (κ t • a)
      (hmap _ (hsmall t)) hy

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]

theorem exists_radius_clock_changed_family {β : V → ℝ} {κ : ℝ → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hcompact : HasCompactSupport β)
    (hsupport : tsupport β ⊆ Φ.source)
    (hκ : ContDiff ℝ ∞ κ) (hbound : ∀ t, ‖κ t‖ ≤ 1)
    {F : ℝ × M → N} (hF : ContMDiff (𝓘(ℝ, ℝ).prod I) J ∞ F)
    (hiF : ∀ t x, Injective (mfderiv I J (fun y => F (t, y)) x))
    {S : Set (ℝ × (M × M))} (hrF : SynchronizedPairs.RegularOn (I := I) (J := J) F S) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ a : V, ‖a‖ < ε →
      let F' := NativeFamily.ambientFamily F (clockAmbient Φ β κ a)
      ContMDiff (𝓘(ℝ, ℝ).prod I) J ∞ F' ∧
      FamilyDoublePoints.doublePoints F' = FamilyDoublePoints.doublePoints F ∧
      (∀ t x, Injective (mfderiv I J (fun y => F' (t, y)) x)) ∧
      SynchronizedPairs.RegularOn (I := I) (J := J) F' S ∧
      (∀ t x, κ t = 0 ∨ F (t, x) ∉ Φ '' tsupport β → F' (t, x) = F (t, x)) := by
  obtain ⟨ε, hε, hall⟩ := exists_radius_clockAmbient Φ hβ hcompact hsupport hκ hbound
  refine ⟨ε, hε, ?_⟩
  intro a ha
  obtain ⟨hA, hD, hfixed, -⟩ := hall a ha
  have hinj : ∀ t, Injective (fun y => clockAmbient Φ β κ a (t, y)) := by
    intro t
    obtain ⟨D, hd⟩ := hD t
    have he : (fun y => clockAmbient Φ β κ a (t, y)) = D :=
      funext (fun y => (hd y).symm)
    rw [he]
    exact D.injective
  have hbij := NativeFamily.ambient_slice_bijective_mfderiv hD
  refine ⟨NativeFamily.ambientFamily_smooth hF hA,
    NativeFamily.doublePoints_ambientFamily F _ hinj,
    NativeFamily.ambientFamily_injective_spatial hF hA hiF (fun t y => (hbij t y).injective),
    (NativeFamily.ambientFamily_regularOn_iff hF hA hinj hbij S).mpr hrF, ?_⟩
  intro t x hx
  exact hfixed t (F (t, x)) hx

end Wikipedia.HopfProblem.OrbitPair.ClockVelocity
