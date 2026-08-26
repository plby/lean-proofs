import Mathlib
import ErdosProblems.Erdos550.ReducedIndependence
import ErdosProblems.Erdos550.OffTuranParams

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# `α(Q) < ηℓ`: a heavy cluster set spans a dense regular pair

This theorem combines the three preceding ingredients into the full `α(Q)` edge-step
of the direct off-Turán embedding:

* `turan_gap_lower` (`OffTuranParams`) — `C(p,2) − t_q(p) ≥ p²/(4q)`;
* `turan_lt_induce_of_few_irregular` (`ReducedIndependence`) — few irregular
  pairs ⟹ the Turán threshold is exceeded;
* `exists_dense_regular_pair_in_family` (`ReducedIndependence`) — the F-freeness
  contradiction giving a dense regular pair.

The result: for an `F`-free red host, any cluster family `𝒜` of size `≥ 4q²`
with fewer than `|𝒜|²/(4q)` irregular pairs (and large, disjoint, `ε₀`-uniform
clusters) contains a pair that is `ε₀`-regular **and** of blue density `≥ d` — an
edge of the reduced graph `Q`.  In the application `|𝒜| ≥ ηℓ` and the irregular
count is `< ε ℓ² < η²ℓ²/(4q) ≤ |𝒜|²/(4q)`, so the hypotheses hold.
-/

open SimpleGraph Finset

namespace Erdos550

/-- **`α(Q) < ηℓ` (edge form).**  For an `F`-free red host there are `ε₀ > 0`,
`m₀` such that every cluster family `𝒜` with `|𝒜| ≥ 4q²`, at most `B` irregular
pairs inside it (`B < |𝒜|²/(4q)`), clusters of size `≥ m₀`, pairwise disjoint and
pairwise-`ε₀`-uniform, contains an `ε₀`-regular pair of blue density `≥ d`. -/
lemma alphaQ_dense_regular_pair {W : Type} [Fintype W] (F : SimpleGraph W)
    (q : ℕ) (hcol : F.Colorable (q + 1)) (hq : 1 ≤ q) (d : ℝ) (hd1 : d < 1) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ m₀ : ℕ, ∀ {V : Type} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj], ¬ (F ⊑ Gᶜ) →
      ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (C : ι → Finset V)
        (Rg : SimpleGraph ι) [DecidableRel Rg.Adj] (𝒜 : Finset ι) (B : ℕ),
        4 * q ^ 2 ≤ 𝒜.card →
        ((Rg.induce (↑𝒜 : Set ι))ᶜ).edgeFinset.card ≤ B →
        (B : ℝ) < (𝒜.card : ℝ) ^ 2 / (4 * q) →
        (∀ i ∈ 𝒜, m₀ ≤ (C i).card) →
        (∀ i ∈ 𝒜, ∀ j ∈ 𝒜, i ≠ j → Disjoint (C i) (C j)) →
        (∀ i j, Rg.Adj i j → G.IsUniform ε₀ (C i) (C j)) →
        ∃ i ∈ 𝒜, ∃ j ∈ 𝒜, Rg.Adj i j ∧ (d : ℝ) ≤ (G.edgeDensity (C i) (C j) : ℝ) := by
  classical
  obtain ⟨ε₀, hε₀, m₀, hmain⟩ := exists_dense_regular_pair_in_family F q hcol d hd1
  refine ⟨ε₀, hε₀, m₀, ?_⟩
  intro V _ _ G _ hFfree ι _ _ C Rg _ 𝒜 B hbig hbad hBlt hC hdisj hreg
  have hgap := turan_gap_lower q 𝒜.card hq hbig
  have hturan : (turanEdges q 𝒜.card : ℕ) < (Rg.induce (↑𝒜 : Set ι)).edgeFinset.card := by
    refine turan_lt_induce_of_few_irregular Rg 𝒜 q B hbad ?_
    have hreal : (turanEdges q 𝒜.card : ℝ) + (B : ℝ) < (𝒜.card.choose 2 : ℝ) := by
      linarith [hgap, hBlt]
    exact_mod_cast hreal
  exact hmain G hFfree C Rg 𝒜 hturan hC hdisj hreg

end Erdos550
