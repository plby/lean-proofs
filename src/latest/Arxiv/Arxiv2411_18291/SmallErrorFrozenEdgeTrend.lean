import Arxiv.Arxiv2411_18291.FrozenEdgeControlledMoments
import Arxiv.Arxiv2411_18291.SmallErrorEdgeDrift

/-! # Sharper conditional drift of the actual frozen edge process -/

open Finset MeasureTheory ProbabilityTheory

noncomputable section

namespace Arxiv2411_18291.CliqueRemovalProcess

variable {V : Type*} [Fintype V] [DecidableEq V] {q r : ℕ}

theorem edgeIncrement_nonpos_of_small_error (hqr : r < q) (hk : q.choose r ≤ 5)
    (H : Finset (Block V q)) (e : Block V r) (c : ℕ → ℝ) (i : ℕ)
    {m u w h₀ v : ℝ} (hm : 0 ≤ m) (hu : 0 ≤ u) (hw : 0 ≤ w)
    (hum : u ≤ m / 8) (hu2 : u ^ 2 ≤ w * m / 8) (hh₀ : 0 < h₀)
    (hv : v ≤ h₀ / 64) (hvm : v * m ≤ 5 / 2 * w * h₀)
    (hC : ((q.choose r : ℝ) ^ 2 + q.choose r) * (Fintype.card V : ℝ) ^ (q - r - 1) ≤
      w / 100)
    (hδ : c (i + 1) - c i ≤ 0)
    (hstep : -(((q.choose r - 1 : ℕ) : ℝ) * m ^ 2 / h₀) +
      (3 * ((q.choose r - 1 : ℕ) : ℝ) + 23 / 8) * w * m / h₀ ≤ c (i + 1) - c i) :
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
  have hk4 : (((q.choose r - 1 : ℕ) : ℝ)) ≤ 4 := by exact_mod_cast (by omega :
    q.choose r - 1 ≤ 4)
  have htrend := frozen_edge_upper_drift_of_small_error
    (Nat.cast_nonneg (q.choose r - 1)) hk4 (Nat.cast_nonneg _) hm hu hw
    (by positivity) hC hum hu2 hxlo hxhi hh₀ hh hv hvm hδ hstep
  exact (hω he hR hd).2.trans htrend

theorem edgeIncrement_nonneg_of_small_error (hqr : r < q) (hk : q.choose r ≤ 5)
    (H : Finset (Block V q)) (e : Block V r) (c : ℕ → ℝ) (i : ℕ)
    {m u w h₀ v B : ℝ} (hm : 0 ≤ m) (hu : 0 ≤ u) (hw : 0 ≤ w)
    (hwu : w ≤ u) (hum : u ≤ m / 8) (hu2 : u ^ 2 ≤ w * m / 8) (hh₀ : 0 < h₀)
    (hv : v ≤ h₀ / 64) (hvm : v * m ≤ 5 / 2 * w * h₀)
    (hB : 0 ≤ B) (hBw : B ≤ w / 100) (hδB : -(c (i + 1) - c i) ≤ B)
    (hstep : c (i + 1) - c i ≤ -(((q.choose r - 1 : ℕ) : ℝ) * m ^ 2 / h₀) -
      (3 * ((q.choose r - 1 : ℕ) : ℝ) + 23 / 8) * w * m / h₀) :
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
  have hk4 : (((q.choose r - 1 : ℕ) : ℝ)) ≤ 4 := by exact_mod_cast (by omega :
    q.choose r - 1 ≤ 4)
  have htrend := frozen_edge_lower_drift_of_small_error (Nat.cast_nonneg (q.choose r - 1))
    hk4 hm hu hw hwu hum hu2 hxlo hxhi hh₀ hh hv hvm hB hBw hδB hstep
  apply le_trans _ (hω he hR hd).1
  simpa only [div_mul_eq_mul_div] using htrend

end Arxiv2411_18291.CliqueRemovalProcess
