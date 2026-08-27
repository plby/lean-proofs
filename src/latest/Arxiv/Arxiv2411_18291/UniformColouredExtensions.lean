import Arxiv.Arxiv2411_18291.AsymptoticColouredExtensions
import Arxiv.Arxiv2411_18291.IndependentTrials
import Arxiv.Arxiv2411_18291.AmplificationNumerics

/-!
# One finite colour family for all root maps

Repeating the colour experiment independently makes every root map succeed
in some colour group. The groups are fixed in advance and shared by all
roots; the number of groups is independent of the ambient vertex count.
-/

open Finset Filter MeasureTheory
open scoped Topology

noncomputable section

namespace Arxiv2411_18291

variable {I W : Type*} [Fintype W] [DecidableEq W] {q : ℕ}

theorem eventually_uniform_coloured_extensions (F : Finset W) (s : Finset I)
    (Q : I → Block W q) (r L : ℕ) (hroot : ∀ i ∈ s, ((Q i).val ∩ F).card < r)
    {b c a β γ κ : ℝ} (hb : 0 < b) (hc : 0 < c) (hκ : 0 < κ) (hκγ : κ < γ)
    (hgap : a + 2 * β * s.card + κ < 1) (hL : (F.card : ℝ) < κ * L) :
    ∀ᶠ n : ℕ in atTop,
      ∀ [MeasurableSpace (Equiv.Perm (Fin n))] [MeasurableSingletonClass (Equiv.Perm (Fin n))],
      ∀ T : (φ : F ↪ Fin n) → Finset (EmbeddingExtension φ),
      ∀ D : Finset (Block (Fin n) q), ∀ d : ℝ, 0 ≤ d →
      (∀ φ, (c * (n : ℝ) ^ (-a)) * (n : ℝ) ^ (Fintype.card W - F.card) ≤ (T φ).card) →
      b * (n : ℝ) ^ (-β) ≤ density D →
      (1 - (n : ℝ) ^ (-γ)) * d ≤ density D →
      (∀ j < r, ∀ P : IntersectingBlockPair (Fin n) q q j,
        (PMF.uniformOfFintype (Equiv.Perm (Fin n))).toMeasure.real
          {σ | P.val.1 ∈ mapGraph σ.toEmbedding D ∧ P.val.2 ∈ mapGraph σ.toEmbedding D} ≤
          (1 + (n : ℝ) ^ (-γ)) * d ^ 2) →
      ∃ ω : Fin L → RandomPermutation.Sample I (Fin n), ∀ φ : F ↪ Fin n, ∃ j,
        ((T φ).card : ℝ) * density D ^ s.card / 2 < extensionColourCount φ s Q (T φ) D (ω j) := by
  classical
  filter_upwards [eventually_coloured_extensions F s Q r hroot hb hc hκ hκγ hgap,
    eventually_trial_union_bound 8 κ F.card L hL] with n hsingle hsmall
  intro _ _ T D d hd hT hp hpd hpair
  let B (φ : F ↪ Fin n) : Set (RandomPermutation.Sample I (Fin n)) :=
    {ω | extensionColourCount φ s Q (T φ) D ω ≤ ((T φ).card : ℝ) * density D ^ s.card / 2}
  have hB (φ : F ↪ Fin n) : MeasurableSet (B φ) :=
    measurableSet_le (RandomPermutation.eventCount_measurable s (T φ)
      (fun f i => extensionColourEvent (Q i) f D)) measurable_const
  have hprob (φ : F ↪ Fin n) :
      (RandomPermutation.probability I (Fin n)).real (B φ) ≤ 8 * (n : ℝ) ^ (-κ) :=
    (hsingle φ (T φ) D d hd (hT φ) hp hpd hpair).1
  have hcard : ((univ : Finset (F ↪ Fin n)).card : ℝ) ≤ (n : ℝ) ^ F.card := by
    have hn : (univ : Finset (F ↪ Fin n)).card ≤ n ^ F.card := by
      simpa only [card_univ, Fintype.card_embedding_eq, Fintype.card_fin,
        Fintype.card_coe] using Nat.descFactorial_le_pow n F.card
    exact_mod_cast hn
  have hbudget : ((univ : Finset (F ↪ Fin n)).card : ℝ) *
      (8 * (n : ℝ) ^ (-κ)) ^ L < 1 :=
    (mul_le_mul_of_nonneg_right hcard (by positivity)).trans_lt hsmall
  obtain ⟨ω, hω⟩ := IndependentTrials.exists_trials_avoiding_each
    (RandomPermutation.probability I (Fin n)) L univ B (fun φ _ => hB φ)
      (fun φ _ => hprob φ) hbudget
  refine ⟨ω, fun φ => ?_⟩
  obtain ⟨j, hj⟩ := hω φ (mem_univ φ)
  exact ⟨j, lt_of_not_ge hj⟩

end Arxiv2411_18291
