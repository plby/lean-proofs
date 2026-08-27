import Arxiv.Arxiv2411_18291.FrozenEdgeControlledMoments
import Arxiv.Arxiv2411_18291.EdgeCriticalDrift

/-! # Critical-interval drift for the constructed frozen edge process -/

open Finset MeasureTheory ProbabilityTheory

noncomputable section

namespace Arxiv2411_18291.CliqueRemovalProcess

variable {V : Type*} [Fintype V] [DecidableEq V] {q r : ℕ}

theorem edgeIncrement_nonpos_of_upper_critical (hqr : r < q)
    (H : Finset (Block V q)) (e : Block V r) (c : ℕ → ℝ) (i : ℕ)
    {m u w t h₀ v : ℝ} (hm : 0 ≤ m) (hu : 0 ≤ u) (ht : 0 ≤ t) (hwt : w ≤ t)
    (hum : u ≤ m) (hu2 : u ^ 2 ≤ t * m) (hh₀ : 0 < h₀) (hv : v ≤ h₀ / 2)
    (hvm : v * m ≤ t * h₀)
    (hC : ((q.choose r : ℝ) ^ 2 + q.choose r) * (Fintype.card V : ℝ) ^ (q - r - 1) ≤ t)
    (hδ : c (i + 1) - c i ≤ 0)
    (hstep : -(((q.choose r - 1 : ℕ) : ℝ) * m ^ 2 / h₀) +
      (6 * ((q.choose r - 1 : ℕ) : ℝ) + 4) * t * m / h₀ ≤ c (i + 1) - c i) :
    ∀ᵐ ω ∂probability r H,
      let R := remainingCliques r H (trajectoryCliques ω i)
      let x := ((R.filter fun Q => e.val ⊆ Q.val).card : ℝ)
      e ∉ cliqueSupport r (trajectoryCliques ω i) → R.Nonempty →
      (∀ f : Block V r, (R.filter fun Q => f.val ⊆ Q.val).Nonempty →
        m - u ≤ ((R.filter fun Q => f.val ⊆ Q.val).card : ℝ) ∧
          ((R.filter fun Q => f.val ⊆ Q.val).card : ℝ) ≤ m + u) →
      |(R.card : ℝ) - h₀| ≤ v → m + u - w ≤ x → x ≤ m + u →
      (probability r H)[edgeIncrement H e c i | Filtration.piLE i] ω ≤ 0 := by
  filter_upwards [edgeIncrement_condExp_bounds hqr H e c i (m - u) (m + u)] with ω hω
  dsimp only
  intro he hR hd hh hxlo hxhi
  have htrend := frozen_edge_upper_drift_nonpos
    (Nat.cast_nonneg (q.choose r - 1)) (Nat.cast_nonneg _) hm hu ht
    (by positivity) hC hwt hum hu2 hxlo hxhi hh₀ hh hv hvm hδ hstep
  exact (hω he hR hd).2.trans htrend

theorem edgeIncrement_nonneg_of_lower_critical (hqr : r < q)
    (H : Finset (Block V q)) (e : Block V r) (c : ℕ → ℝ) (i : ℕ)
    {m u w t h₀ v B : ℝ} (hm : 0 ≤ m) (hu : 0 ≤ u) (ht : 0 ≤ t) (hwt : w ≤ t)
    (htm : t ≤ m) (hum : u ≤ m) (hu2 : u ^ 2 ≤ t * m) (hh₀ : 0 < h₀)
    (hv : v ≤ h₀ / 2) (hvm : v * m ≤ t * h₀) (hB : 0 ≤ B)
    (hδB : -(c (i + 1) - c i) ≤ B)
    (hstep : c (i + 1) - c i ≤ -(((q.choose r - 1 : ℕ) : ℝ) * m ^ 2 / h₀) -
      6 * ((q.choose r - 1 : ℕ) : ℝ) * t * m / h₀ - 4 * m * B / h₀) :
    ∀ᵐ ω ∂probability r H,
      let R := remainingCliques r H (trajectoryCliques ω i)
      let x := ((R.filter fun Q => e.val ⊆ Q.val).card : ℝ)
      e ∉ cliqueSupport r (trajectoryCliques ω i) → R.Nonempty →
      (∀ f : Block V r, (R.filter fun Q => f.val ⊆ Q.val).Nonempty →
        m - u ≤ ((R.filter fun Q => f.val ⊆ Q.val).card : ℝ) ∧
          ((R.filter fun Q => f.val ⊆ Q.val).card : ℝ) ≤ m + u) →
      |(R.card : ℝ) - h₀| ≤ v → m - u ≤ x → x ≤ m - u + w →
      0 ≤ (probability r H)[edgeIncrement H e c i | Filtration.piLE i] ω := by
  filter_upwards [edgeIncrement_condExp_bounds hqr H e c i (m - u) (m + u)] with ω hω
  dsimp only
  intro he hR hd hh hxlo hxhi
  have htrend := frozen_edge_lower_drift_nonneg (Nat.cast_nonneg (q.choose r - 1))
    hm hu ht hwt htm hum hu2 hxlo hxhi hh₀ hh hv hvm hB hδB hstep
  apply le_trans _ (hω he hR hd).1
  simpa only [div_mul_eq_mul_div] using htrend

end Arxiv2411_18291.CliqueRemovalProcess
