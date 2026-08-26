import Mathlib

/- Ported from Lean 4.31.0 to 4.33.0; imports and elaboration options adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos489

open Filter
open scoped Topology

/-- A sequence which is eventually uniformly approximable, to arbitrary
accuracy, by convergent sequences is itself convergent in `ℝ`. -/
theorem exists_tendsto_of_uniform_eventual_approx
    (f : ℕ → ℝ) (approx : ℕ → ℕ → ℝ)
    (hclose : ∀ ε : ℝ, 0 < ε → ∃ H : ℕ,
      ∀ᶠ x : ℕ in atTop, |f x - approx H x| < ε)
    (hconv : ∀ H : ℕ, ∃ L : ℝ, Tendsto (approx H) atTop (𝓝 L)) :
    ∃ L : ℝ, Tendsto f atTop (𝓝 L) := by
  have hcauchy : CauchySeq f := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨H, hH⟩ := hclose (ε / 4) (by positivity)
    obtain ⟨L, hL⟩ := hconv H
    have hLmetric := (Metric.tendsto_atTop.1 hL) (ε / 4) (by positivity)
    obtain ⟨Nclose, hNclose⟩ := Filter.eventually_atTop.mp hH
    obtain ⟨Nlim, hNlim⟩ := hLmetric
    refine ⟨max Nclose Nlim, ?_⟩
    intro m hm n hn
    have hmclose := hNclose m (le_trans (le_max_left _ _) hm)
    have hnclose := hNclose n (le_trans (le_max_left _ _) hn)
    have hmlim := hNlim m (le_trans (le_max_right _ _) hm)
    have hnlim := hNlim n (le_trans (le_max_right _ _) hn)
    rw [Real.dist_eq] at hmlim hnlim ⊢
    have htri1 : |f m - f n| ≤
        |f m - approx H m| + |approx H m - L| + |L - f n| := by
      simpa only [Real.dist_eq] using
        dist_triangle4 (f m) (approx H m) L (f n)
    have htri2 : |L - f n| ≤
        |L - approx H n| + |approx H n - f n| := by
      simpa only [Real.dist_eq] using dist_triangle L (approx H n) (f n)
    have hmclose' : |f m - approx H m| < ε / 4 := hmclose
    have hnclose' : |approx H n - f n| < ε / 4 := by
      simpa [abs_sub_comm] using hnclose
    have hnlim' : |L - approx H n| < ε / 4 := by
      simpa [abs_sub_comm] using hnlim
    nlinarith
  exact cauchySeq_tendsto_of_complete hcauchy

end Erdos489
