import Arxiv.Arxiv2411_18291.VarianceExponentialBound
import Arxiv.Arxiv2411_18291.ConditionalExponential

/-!
# Conditional exponential bounds using second moments

Signed bounded increments are integrable, as are their squares and
exponentials. Taking conditional expectations of the quadratic scalar
bound gives exponential compensation by the conditional second moment
whenever the conditional mean is nonpositive.
-/

open MeasureTheory ProbabilityTheory

noncomputable section

namespace Arxiv2411_18291

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {P : Measure Ω}
variable [IsProbabilityMeasure P] {X : Ω → ℝ} {b t : ℝ}

theorem integrable_sq_of_abs_bound (hX : StronglyMeasurable X)
    (hXb : ∀ᵐ ω ∂P, |X ω| ≤ b) : Integrable (fun ω => (X ω) ^ 2) P := by
  apply Integrable.of_bound (hX.pow 2).aestronglyMeasurable (b ^ 2)
  filter_upwards [hXb] with ω hω
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact sq_le_sq.mpr (hω.trans (le_abs_self b))

theorem condExp_exp_mul_le_quadratic (hm : m ≤ mΩ) (hb : 0 ≤ b)
    (hX : StronglyMeasurable X) (hXb : ∀ᵐ ω ∂P, |X ω| ≤ b)
    (ht : 0 ≤ t) (htb : t * b < 2) :
    P[fun ω => Real.exp (t * X ω) | m] ≤ᵐ[P]
      fun ω => 1 + t * P[X | m] ω +
        (t ^ 2 / (2 - t * b)) * P[fun ω => (X ω) ^ 2 | m] ω := by
  let g := t ^ 2 / (2 - t * b)
  have hXi : Integrable X P := Integrable.of_bound hX.aestronglyMeasurable b hXb
  have hX2 := integrable_sq_of_abs_bound hX hXb
  have hexp := integrable_exp_mul_of_abs_bound hX.measurable hXb t
  have hlin : Integrable (fun ω => 1 + t * X ω + g * (X ω) ^ 2) P :=
    ((integrable_const 1).add (hXi.const_mul t)).add (hX2.const_mul g)
  have hpoint : (fun ω => Real.exp (t * X ω)) ≤ᵐ[P]
      fun ω => 1 + t * X ω + g * (X ω) ^ 2 := by
    filter_upwards [hXb] with ω hω
    exact exp_mul_le_quadratic_of_upper_bound hb ((le_abs_self _).trans hω) ht htb
  have hfirst := condExp_add (μ := P) (integrable_const (1 : ℝ)) (hXi.const_mul t) m
  have hsecond := condExp_add (μ := P)
    ((integrable_const (1 : ℝ)).add (hXi.const_mul t)) (hX2.const_mul g) m
  have hmul := condExp_smul (μ := P) t X m
  have hmul2 := condExp_smul (μ := P) g (fun ω => (X ω) ^ 2) m
  filter_upwards [condExp_mono (m := m) hexp hlin hpoint, hfirst, hsecond, hmul, hmul2]
    with ω hω hf hs ht' hg'
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, condExp_const hm] at hf hs ht' hg'
  change P[fun ω => 1 + t * X ω | m] ω =
    1 + P[fun ω => t * X ω | m] ω at hf
  change P[fun ω => 1 + t * X ω + g * (X ω) ^ 2 | m] ω =
    P[fun ω => 1 + t * X ω | m] ω + P[fun ω => g * (X ω) ^ 2 | m] ω at hs
  change P[fun ω => t * X ω | m] ω = t * P[X | m] ω at ht'
  change P[fun ω => g * (X ω) ^ 2 | m] ω =
    g * P[fun ω => (X ω) ^ 2 | m] ω at hg'
  apply hω.trans
  change P[fun ω => 1 + t * X ω + g * (X ω) ^ 2 | m] ω ≤
    1 + t * P[X | m] ω + g * P[fun ω => (X ω) ^ 2 | m] ω
  rw [hs, hf, ht', hg']

theorem condExp_exp_mul_le_exp_secondMoment (hm : m ≤ mΩ) (hb : 0 ≤ b)
    (hX : StronglyMeasurable X) (hXb : ∀ᵐ ω ∂P, |X ω| ≤ b)
    (hmean : P[X | m] ≤ᵐ[P] 0) (ht : 0 ≤ t) (htb : t * b < 2) :
    P[fun ω => Real.exp (t * X ω) | m] ≤ᵐ[P]
      fun ω => Real.exp ((t ^ 2 / (2 - t * b)) * P[fun ω => (X ω) ^ 2 | m] ω) := by
  filter_upwards [condExp_exp_mul_le_quadratic hm hb hX hXb ht htb, hmean] with ω hω hμ
  have htμ : t * P[X | m] ω ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht hμ
  have he := Real.add_one_le_exp
    ((t ^ 2 / (2 - t * b)) * P[fun ω => (X ω) ^ 2 | m] ω)
  exact hω.trans (by linarith only [htμ, he])

end Arxiv2411_18291
