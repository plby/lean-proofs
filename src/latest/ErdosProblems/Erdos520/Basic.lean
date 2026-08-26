import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Filter MeasureTheory
open scoped Topology

namespace Erdos
namespace Problem520

/-- The iterated logarithm used in Erdős #520, evaluated on natural inputs. -/
noncomputable def log₂ (N : ℕ) : ℝ :=
  Real.log (Real.log (N : ℝ))

/-- The critical almost-sure upper-bound scale used in the proof. -/
noncomputable def criticalScale (η : ℝ) (N : ℕ) : ℝ :=
  Real.sqrt N * log₂ N ^ (1 / 4 + η)

/-- The classical law-of-the-iterated-logarithm scale, written exactly as in
Erdős #520. -/
noncomputable def lilScale (N : ℕ) : ℝ :=
  Real.sqrt ((N : ℝ) * log₂ N)

/-- Almost-sure `1/4 + η` upper bounds for every positive `η`.

The constant may depend on the sample and on `η`. This is the direct Lean
form of the quantitative theorem proved by the development.
-/
def CriticalUpperBound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (M : Ω → ℕ → ℝ) : Prop :=
  ∀ η : ℝ, 0 < η →
    ∀ᵐ omega ∂μ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ N : ℕ in atTop,
        |M omega N| ≤ C * criticalScale η N

/-- The zero-LIL conclusion that disproves a positive constant in #520. -/
def ZeroLIL {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (M : Ω → ℕ → ℝ) : Prop :=
  ∀ᵐ omega ∂μ,
    Tendsto (fun N : ℕ => |M omega N| / lilScale N) atTop (𝓝 0)

/-- Signed zero-LIL convergence. -/
def SignedZeroLIL {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (M : Ω → ℕ → ℝ) : Prop :=
  ∀ᵐ omega ∂μ,
    Tendsto (fun N : ℕ => M omega N / lilScale N) atTop (𝓝 0)

/-- There is almost surely no positive **limsup** constant at the classical
LIL normalization.  This is the direct negation of the positive-constant
formulation of Erdős #520. -/
def NoPositiveLILConstant {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (M : Ω → ℕ → ℝ) : Prop :=
  ∀ᵐ omega ∂μ, ∀ c : ℝ, 0 < c →
    limsup (fun N : ℕ => M omega N / lilScale N) atTop ≠ c

theorem tendsto_log₂_atTop :
    Tendsto log₂ atTop atTop := by
  exact Real.tendsto_log_atTop.comp
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

theorem eventually_log₂_pos :
    ∀ᶠ N : ℕ in atTop, 0 < log₂ N :=
  tendsto_log₂_atTop.eventually (eventually_gt_atTop 0)

theorem eventually_lilScale_pos :
    ∀ᶠ N : ℕ in atTop, 0 < lilScale N := by
  filter_upwards [eventually_gt_atTop (0 : ℕ), eventually_log₂_pos] with N hN hlog
  exact Real.sqrt_pos.2 (mul_pos (by exact_mod_cast hN) hlog)

/-- At `η = 1/8`, the quotient of the critical scale by the LIL scale is
exactly the decaying power `(log₂ N)^(-1/8)` for all sufficiently large `N`.
-/
theorem criticalScale_div_lilScale_eventually :
    ∀ᶠ N : ℕ in atTop,
      criticalScale (1 / 8 : ℝ) N / lilScale N = log₂ N ^ (-1 / 8 : ℝ) := by
  filter_upwards [eventually_gt_atTop (0 : ℕ), eventually_log₂_pos] with N hN hlog
  have hsqrt : 0 < Real.sqrt N := Real.sqrt_pos.2 (by exact_mod_cast hN)
  rw [criticalScale, lilScale, Real.sqrt_mul (by positivity),
    Real.sqrt_eq_rpow (log₂ N)]
  field_simp
  rw [← Real.rpow_add hlog]
  congr 1
  norm_num

theorem tendsto_log₂_rpow_neg_one_eighth :
    Tendsto (fun N : ℕ => log₂ N ^ (-1 / 8 : ℝ)) atTop (𝓝 0) := by
  have hexp : (-1 / 8 : ℝ) = -(1 / 8) := by ring
  rw [hexp]
  have hpow := tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 8)
  exact hpow.comp tendsto_log₂_atTop

/-- The strengthened `1/4 + η` almost-sure upper bound implies the zero-LIL
conclusion. No probabilistic axiom is used here; this is the deterministic
endpoint of the quantitative estimate.
-/
theorem zeroLIL_of_criticalUpperBound {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {M : Ω → ℕ → ℝ}
    (h : CriticalUpperBound μ M) :
    ZeroLIL μ M := by
  have hη := h (1 / 8 : ℝ) (by norm_num)
  filter_upwards [hη] with omega homega
  rcases homega with ⟨C, hC, hbound⟩
  have hmajorant :
      Tendsto (fun N : ℕ => C * log₂ N ^ (-1 / 8 : ℝ)) atTop (𝓝 0) := by
    simpa using! tendsto_log₂_rpow_neg_one_eighth.const_mul C
  apply squeeze_zero'
  · filter_upwards [eventually_lilScale_pos] with N hscale
    exact div_nonneg (abs_nonneg _) hscale.le
  · filter_upwards [hbound, eventually_lilScale_pos,
      criticalScale_div_lilScale_eventually] with N hMN hscale hscale_eq
    calc
      |M omega N| / lilScale N
          ≤ (C * criticalScale (1 / 8 : ℝ) N) / lilScale N :=
            div_le_div_of_nonneg_right hMN hscale.le
      _ = C * (criticalScale (1 / 8 : ℝ) N / lilScale N) := by ring
      _ = C * log₂ N ^ (-1 / 8 : ℝ) := by rw [hscale_eq]
  · exact hmajorant

theorem signedZeroLIL_of_zeroLIL {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {M : Ω → ℕ → ℝ}
    (h : ZeroLIL μ M) :
    SignedZeroLIL μ M := by
  filter_upwards [h] with omega homega
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply homega.congr'
  filter_upwards [eventually_lilScale_pos] with N hscale
  simp [Real.norm_eq_abs, abs_of_pos hscale]

theorem noPositiveLILConstant_of_zeroLIL {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {M : Ω → ℕ → ℝ}
    (h : ZeroLIL μ M) :
    NoPositiveLILConstant μ M := by
  have hsigned := signedZeroLIL_of_zeroLIL h
  filter_upwards [hsigned] with omega homega
  intro c hc hlimsup
  have hzero :
      limsup (fun N : ℕ => M omega N / lilScale N) atTop = 0 :=
    homega.limsup_eq
  rw [hzero] at hlimsup
  linarith

end Problem520
end Erdos
