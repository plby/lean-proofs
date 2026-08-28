import Wikipedia.HopfProblem.DegreeCollapseTubeSupportBox
import Wikipedia.HopfProblem.DegreeCollapseLongitudinalDiffeomorph
import Wikipedia.HopfProblem.DegreeCollapseConvexHeightProfiles

/-!
# Supported longitudinal interpolation through genuine diffeomorphisms

Interpolate an increasing scalar profile with the identity, using a
transverse cutoff and a bounded smooth time parameter. Positivity of the
longitudinal derivative survives every blend. Compact support and the
triangular inverse theorem give a global diffeomorphism for every real time.
-/

noncomputable section

open Set Function Metric Manifold
open scoped Topology ContDiff
open Wikipedia.HopfProblem.DegreeCollapse.RegularHeightCoordinates

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

def longitudinalBlendDisplacement (D : ℝ → ℝ) (β : V → ℝ) (η : ℝ → ℝ)
    (t : ℝ) (p : ℝ × V) : ℝ := η t * β p.2 * (D p.1 - p.1)

def longitudinalBlend (D : ℝ → ℝ) (β : V → ℝ) (η : ℝ → ℝ)
    (p : ℝ × (ℝ × V)) : ℝ × V :=
  (p.2.1 + longitudinalBlendDisplacement D β η p.1 p.2, p.2.2)

theorem longitudinalBlendDisplacement_smooth {D : ℝ → ℝ} {β : V → ℝ} (η : ℝ → ℝ)
    (hD : ContDiff ℝ ∞ D) (hβ : ContDiff ℝ ∞ β) (t : ℝ) :
    ContDiff ℝ ∞ (longitudinalBlendDisplacement D β η t) :=
  (contDiff_const.mul (hβ.comp contDiff_snd)).mul ((hD.comp contDiff_fst).sub contDiff_fst)

theorem longitudinalBlend_smooth {D : ℝ → ℝ} {β : V → ℝ} {η : ℝ → ℝ}
    (hD : ContDiff ℝ ∞ D) (hβ : ContDiff ℝ ∞ β) (hη : ContDiff ℝ ∞ η) :
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ × V)) 𝓘(ℝ, ℝ × V) ∞
      (longitudinalBlend D β η) := by
  have hs : ContMDiff 𝓘(ℝ, ℝ × V) 𝓘(ℝ, ℝ) ∞ Prod.fst := contDiff_fst.contMDiff
  have hz : ContMDiff 𝓘(ℝ, ℝ × V) 𝓘(ℝ, V) ∞ Prod.snd := contDiff_snd.contMDiff
  have hs' : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ × V)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × (ℝ × V) => p.2.1) := hs.comp contMDiff_snd
  have hz' : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ × V)) 𝓘(ℝ, V) ∞
      (fun p : ℝ × (ℝ × V) => p.2.2) := hz.comp contMDiff_snd
  exact (hs'.add (((hη.contMDiff.comp contMDiff_fst).mul
    (hβ.contMDiff.comp hz')).mul ((hD.contMDiff.comp hs').sub hs'))).prodMk_space hz'

theorem longitudinalBlend_zero {D : ℝ → ℝ} {β : V → ℝ} {η : ℝ → ℝ}
    (hη : η 0 = 0) (p : ℝ × V) : longitudinalBlend D β η (0, p) = p := by
  simp only [longitudinalBlend, longitudinalBlendDisplacement, hη, zero_mul, add_zero]

theorem longitudinalBlendDisplacement_zero_outside {D : ℝ → ℝ} {β : V → ℝ}
    (η : ℝ → ℝ) {l u : ℝ} (hfix : ∀ s ∉ Ioo l u, D s = s)
    (t : ℝ) (p : ℝ × V) (hp : p ∉ Icc l u ×ˢ tsupport β) :
    longitudinalBlendDisplacement D β η t p = 0 := by
  by_cases hs : p.1 ∈ Icc l u
  · have hb : β p.2 = 0 := image_eq_zero_of_notMem_tsupport (fun h => hp ⟨hs, h⟩)
    simp only [longitudinalBlendDisplacement, hb, mul_zero, zero_mul]
  · have hd := hfix p.1 (fun h => hs ⟨h.1.le, h.2.le⟩)
    simp only [longitudinalBlendDisplacement, hd, sub_self, mul_zero]

theorem longitudinalBlend_fixed_outside {D : ℝ → ℝ} {β : V → ℝ}
    (η : ℝ → ℝ) {l u : ℝ} (hfix : ∀ s ∉ Ioo l u, D s = s)
    (t : ℝ) (p : ℝ × V) (hp : p ∉ Icc l u ×ˢ tsupport β) :
    longitudinalBlend D β η (t, p) = p := by
  rw [longitudinalBlend, longitudinalBlendDisplacement_zero_outside η hfix t p hp, add_zero]

theorem longitudinalBlend_derivative_positive {D : ℝ → ℝ} {β : V → ℝ} {η : ℝ → ℝ}
    (hD : ContDiff ℝ ∞ D) (hβ : ContDiff ℝ ∞ β)
    (hDpos : ∀ s, 0 < deriv D s) (hβrange : ∀ z, β z ∈ Icc (0 : ℝ) 1)
    (hηrange : ∀ t, η t ∈ Icc (0 : ℝ) 1) (t : ℝ) (p : ℝ × V) :
    0 < fderiv ℝ (displacedHeight (longitudinalBlendDisplacement D β η t)) p (1, 0) := by
  have hu := longitudinalBlendDisplacement_smooth η hD hβ t
  have hscalar := scalar_derivative (contDiff_displacedHeight hu) p.1 p.2
  have hd := (hasDerivAt_id p.1).add
    (((hD.differentiable (by simp) p.1).hasDerivAt.sub (hasDerivAt_id p.1)).const_mul
      (η t * β p.2))
  have hrate : fderiv ℝ (displacedHeight (longitudinalBlendDisplacement D β η t)) p (1, 0) =
      1 + (η t * β p.2) * (deriv D p.1 - 1) := hscalar.deriv.symm.trans hd.deriv
  rw [hrate]
  have hweight : η t * β p.2 ∈ Icc (0 : ℝ) 1 :=
    ⟨mul_nonneg (hηrange t).1 (hβrange p.2).1,
      mul_le_one₀ (hηrange t).2 (hβrange p.2).1 (hβrange p.2).2⟩
  have hpos := MorseRearrangement.positive_blended_slope hweight (hDpos p.1) zero_lt_one
  nlinarith

variable [FiniteDimensional ℝ V]

theorem longitudinalBlend_slices {D : ℝ → ℝ} {β : V → ℝ} {η : ℝ → ℝ} {l u : ℝ}
    (hD : ContDiff ℝ ∞ D) (hβ : ContDiff ℝ ∞ β) (hc : HasCompactSupport β)
    (hDpos : ∀ s, 0 < deriv D s) (hfix : ∀ s ∉ Ioo l u, D s = s)
    (hβrange : ∀ z, β z ∈ Icc (0 : ℝ) 1) (hηrange : ∀ t, η t ∈ Icc (0 : ℝ) 1)
    (t : ℝ) : ∃ d : Diffeomorph 𝓘(ℝ, ℝ × V) 𝓘(ℝ, ℝ × V) (ℝ × V) (ℝ × V) ∞,
      ∀ p, d p = longitudinalBlend D β η (t, p) := by
  have hu := longitudinalBlendDisplacement_smooth η hD hβ t
  have hcompact : HasCompactSupport (longitudinalBlendDisplacement D β η t) :=
    HasCompactSupport.intro (isCompact_Icc.prod hc.isCompact)
      (longitudinalBlendDisplacement_zero_outside η hfix t)
  exact ⟨longitudinalDiffeomorph hu hcompact
    (longitudinalBlend_derivative_positive hD hβ hDpos hβrange hηrange t), fun _ => rfl⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
