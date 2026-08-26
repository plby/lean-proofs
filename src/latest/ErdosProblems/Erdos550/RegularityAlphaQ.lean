import Mathlib
import ErdosProblems.Erdos550.ReducedAlphaQ
import ErdosProblems.Erdos550.RegularityNonuniform

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# `α(Q) < ηℓ` directly from a Szemerédi partition

This assembles the abstract `α(Q)` theorem (`alphaQ_dense_regular_pair`) with the
graph-side irregular-pair bound (`induce_compl_edges_le_nonUniforms`) and
`Finpartition.IsUniform`, giving the off-Turán `α(Q)` step in the form actually
produced by Szemerédi's regularity lemma: for an `F`-free red host and an
`ε`-uniform partition `P`, any cluster set `𝒜` with `|𝒜| ≥ 4q²` and
`ℓ²·ε < |𝒜|²/(4q)` (with clusters large enough) contains two distinct parts that
form an `ε`-uniform pair of **blue** density `≥ d` — i.e. an edge of the reduced
graph `Q`.
-/

open SimpleGraph Finset Classical

namespace Erdos550

/-- **`α(Q) < ηℓ` from a Szemerédi partition.** -/
theorem regularity_dense_regular_pair {W : Type} [Fintype W] (F : SimpleGraph W)
    (q : ℕ) (hcol : F.Colorable (q + 1)) (hq : 1 ≤ q) (d : ℝ) (hd1 : d < 1) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ m₀ : ℕ, ∀ {V : Type} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj], ¬ (F ⊑ Gᶜ) →
      ∀ (ε : ℝ), 0 ≤ ε → ε ≤ ε₀ →
      ∀ (P : Finpartition (univ : Finset V)), P.IsUniform G ε →
      ∀ (𝒜 : Finset {x // x ∈ P.parts}),
        4 * q ^ 2 ≤ 𝒜.card →
        ((P.parts.card : ℝ) ^ 2 * ε < (𝒜.card : ℝ) ^ 2 / (4 * q)) →
        (∀ U ∈ 𝒜, m₀ ≤ U.val.card) →
        ∃ U ∈ 𝒜, ∃ W' ∈ 𝒜, U ≠ W' ∧ G.IsUniform ε U.val W'.val ∧
          (d : ℝ) ≤ (G.edgeDensity U.val W'.val : ℝ) := by
  classical
  obtain ⟨ε₀, hε₀, m₀, hcap⟩ := alphaQ_dense_regular_pair F q hcol hq d hd1
  refine ⟨ε₀, hε₀, m₀, ?_⟩
  intro V _ _ G _ hFfree ε hε0 hεε₀ P hPunif 𝒜 hbig hthr hsize
  -- the regular-pairs graph on the parts
  set Rg : SimpleGraph {x // x ∈ P.parts} :=
    { Adj := fun U W => U ≠ W ∧ G.IsUniform ε U.val W.val
      symm := ⟨fun U W h => ⟨(h.1).symm, h.2.symm⟩⟩
      loopless := ⟨fun U h => h.1 rfl⟩ } with hRgdef
  -- clusters are just the parts' underlying finsets
  set C : {x // x ∈ P.parts} → Finset V := fun U => U.val with hCdef
  -- irregular-pair bound
  have hbad : ((Rg.induce (↑𝒜 : Set {x // x ∈ P.parts}))ᶜ).edgeFinset.card
      ≤ (P.nonUniforms G ε).card :=
    induce_compl_edges_le_nonUniforms G ε P Rg
      (fun U W hUW => by simp only [hRgdef]; exact ⟨fun h => h.2, fun h => ⟨hUW, h⟩⟩) 𝒜
  -- non-uniform count is small
  have hnu : ((P.nonUniforms G ε).card : ℝ) < (𝒜.card : ℝ) ^ 2 / (4 * q) := by
    have h1 : ((P.nonUniforms G ε).card : ℝ)
        ≤ (↑(P.parts.card * (P.parts.card - 1))) * ε := hPunif
    have h2 : (↑(P.parts.card * (P.parts.card - 1)) : ℝ)
        ≤ (P.parts.card : ℝ) ^ 2 := by
      have := Nat.mul_le_mul_left P.parts.card (Nat.sub_le P.parts.card 1)
      calc (↑(P.parts.card * (P.parts.card - 1)) : ℝ)
          ≤ (↑(P.parts.card * P.parts.card) : ℝ) := by exact_mod_cast this
        _ = (P.parts.card : ℝ) ^ 2 := by push_cast; ring
    have h3 : (↑(P.parts.card * (P.parts.card - 1)) : ℝ) * ε
        ≤ (P.parts.card : ℝ) ^ 2 * ε := by
      exact mul_le_mul_of_nonneg_right h2 hε0
    linarith
  -- Apply the abstract theorem with B := #(nonUniforms).
  have := hcap G hFfree C Rg 𝒜 (P.nonUniforms G ε).card hbig hbad hnu hsize
    (fun U hU W hW hUW => P.disjoint U.2 W.2 (fun h => hUW (Subtype.ext h)))
    (fun U W hUW => (hUW.2).mono hεε₀)
  obtain ⟨U, hU, W', hW', hadj, hdens⟩ := this
  exact ⟨U, hU, W', hW', hadj.1, hadj.2, hdens⟩

end Erdos550
