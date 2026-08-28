import Wikipedia.HopfProblem.SpecialPeriodsRotations
import Mathlib.Analysis.Analytic.Order
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

/-!
# Exact disc vanishing orders in the actual ambient chart

A holomorphic function on the original open disc has an analytic ambient
germ through the inverse of its actual chart at zero.  Multiplication by
the `n`th power of the disc coordinate has exact vanishing order `n` when
the remaining holomorphic factor is nonzero at the centre.
-/

noncomputable section

open Set Filter Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.SectionsUnit

/-- Ambient extension through the actual inverse chart of the open disc. -/
def discExtension (f : Disc → ℂ) : ℂ → ℂ :=
  f ∘ (chartAt ℂ discZero).symm

@[simp] theorem discChart_apply (s : Disc) :
    chartAt ℂ discZero s = (s : ℂ) := rfl

theorem zero_mem_discChart_target : (0 : ℂ) ∈ (chartAt ℂ discZero).target :=
  (chartAt ℂ discZero).map_source (mem_chart_source ℂ discZero)

@[simp] theorem discChart_symm_zero : (chartAt ℂ discZero).symm 0 = discZero :=
  (chartAt ℂ discZero).left_inv (mem_chart_source ℂ discZero)

theorem discChart_symm_coe {z : ℂ} (hz : z ∈ (chartAt ℂ discZero).target) :
    ((chartAt ℂ discZero).symm z : ℂ) = z :=
  (chartAt ℂ discZero).right_inv hz

@[simp] theorem discExtension_zero (f : Disc → ℂ) :
    discExtension f 0 = f discZero := by
  simp only [discExtension, Function.comp_apply, discChart_symm_zero]

/-- The extension is analytic at zero for the original open-disc atlas. -/
theorem discExtension_analyticAt {u : Disc → ℂ}
    (hu : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω u) : AnalyticAt ℂ (discExtension u) 0 := by
  have hc : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (chartAt ℂ discZero).symm 0 :=
    contMDiffOn_chart_symm.contMDiffAt
      ((chartAt ℂ discZero).open_target.mem_nhds zero_mem_discChart_target)
  exact ((hu _).comp 0 hc).contDiffAt.analyticAt

/-- In a neighbourhood of the actual chart centre, extension commutes
with multiplying by the ambient coordinate power. -/
theorem discExtension_power_mul_eventually (u : Disc → ℂ) (n : ℕ) :
    discExtension (fun s : Disc => (s : ℂ) ^ n * u s) =ᶠ[𝓝 (0 : ℂ)]
      (fun z : ℂ => z ^ n * discExtension u z) := by
  filter_upwards [(chartAt ℂ discZero).open_target.mem_nhds zero_mem_discChart_target]
    with z hz
  change ((chartAt ℂ discZero).symm z : ℂ) ^ n * u ((chartAt ℂ discZero).symm z) =
    z ^ n * u ((chartAt ℂ discZero).symm z)
  rw [discChart_symm_coe hz]

theorem discExtension_power_mul_analyticAt {u : Disc → ℂ}
    (hu : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω u) (n : ℕ) :
    AnalyticAt ℂ (discExtension (fun s : Disc => (s : ℂ) ^ n * u s)) 0 := by
  have hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun s : Disc => (s : ℂ) ^ n * u s) :=
    (contMDiff_subtype_val.pow n).mul hu
  exact discExtension_analyticAt hF

/-- A holomorphic unit at the disc centre contributes zero to the order. -/
theorem analyticOrderAt_discExtension_of_ne_zero {u : Disc → ℂ}
    (hu : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω u) (hunit : u discZero ≠ 0) :
    analyticOrderAt (discExtension u) 0 = 0 :=
  (discExtension_analyticAt hu).analyticOrderAt_eq_zero.mpr
    (by simpa only [discExtension_zero] using hunit)

/-- Exact ambient vanishing order of `s^n u(s)`, with the ambient germ
defined by the actual inverse chart of the original disc. -/
theorem analyticOrderAt_discExtension_power_mul {u : Disc → ℂ}
    (hu : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω u) (hunit : u discZero ≠ 0) (n : ℕ) :
    analyticOrderAt (discExtension (fun s : Disc => (s : ℂ) ^ n * u s)) 0 = (n : ℕ∞) := by
  rw [analyticOrderAt_congr (discExtension_power_mul_eventually u n)]
  change analyticOrderAt (((id : ℂ → ℂ) ^ n) * discExtension u) 0 = (n : ℕ∞)
  rw [analyticOrderAt_mul (analyticAt_id.pow n) (discExtension_analyticAt hu),
    analyticOrderAt_pow analyticAt_id, analyticOrderAt_id,
    analyticOrderAt_discExtension_of_ne_zero hu hunit]
  simp

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.SectionsUnit
