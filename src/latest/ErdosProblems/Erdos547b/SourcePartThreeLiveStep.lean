/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourcePartThreeAppendixData
import ErdosProblems.Erdos547b.SourcePartThreeResidualInvariant
import ErdosProblems.Erdos547b.SourceDynamicUsedCard
import ErdosProblems.Erdos547b.Lemma58PartThreeEmbedding

/-!
# One actual Part-3 owner batch preserving the live-state invariant

Appendix numeric data are constructed from the scalar source budget and
live typicality. The resulting graph images are counted exactly, so the
output invariant is about the actual remaining endpoint sets.
-/

open scoped SimpleGraph Classical
noncomputable section

namespace Erdos547b.ZhaoSourcePartThreeLiveStep

open Finset SimpleGraph Erdos547b.RegularPair
open Erdos547b.ZhaoLemma58GroupedSmallForest Erdos547b.ZhaoLemma58PartThreeEmbedding
open Erdos547b.ZhaoSourcePartThreeResidualNumerics Erdos547b.ZhaoSourcePartThreeAppendixData

/-- The local Part-3 step constructs its actual graph copy and proves the
residual trichotomy on its actual unused sets. Only the current root is given. -/
theorem exists_partThree_live_step
    {b : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    (F : OrderedRootedForest b) (H : SimpleGraph V) [DecidableRel H.Adj]
    (z : V) (whole live : Fin 2 → Finset V) (N small : ℕ)
    (gamma epsilon rho density lambda dx dy : ℝ)
    (herror : 2 ≤ epsilon * N) (hgamma : 0 ≤ gamma)
    (hlambda : 0 ≤ lambda) (hlambdaHalf : lambda ≤ 1 / 2)
    (hdxlo : lambda ≤ dx) (hdxhi : dx ≤ 1 - lambda)
    (hdylo : lambda ≤ dy) (hdyhi : dy ≤ 1 - lambda)
    (hgate : 8 * epsilon ≤ lambda * gamma)
    (hwhole : ∀ c, (whole c).card = N) (hlive : ∀ c, live c ⊆ whole c)
    (hXY : (live 0).card ≤ (live 1).card)
    (hP : dx * (live 0).card - 2 * (epsilon * N) ≤ (#((live 0).filter (H.Adj z)) : ℝ))
    (hQ : dy * (live 1).card - 2 * (epsilon * N) ≤ (#((live 1).filter (H.Adj z)) : ℝ))
    (hinv : ResidualInvariant dx dy N (epsilon * N) (N - (live 0).card) (N - (live 1).card))
    (hbudget : ((N : ℝ) - (live 0).card) + (N - (live 1).card) + F.order ≤
      (dx + dy + lambda) * N - 2 * (gamma * N) - 24 * (epsilon * N))
    (hlower : ∀ i, 2 ≤ F.size i) (hupper : ∀ i, F.size i ≤ small)
    (hsmall : (small : ℝ) ≤ epsilon * N / 2)
    (huniform : H.IsUniform rho (whole 0) (whole 1))
    (hdisjoint : Disjoint (whole 0) (whole 1))
    (hdensity : density ≤ H.edgeDensity (whole 0) (whole 1))
    (hfactor : 0 ≤ density - rho)
    (hregularRoot : rho * N < 3 * epsilon * N)
    (hregularInterior : rho * N ≤ gamma * N)
    (hcomponent : ∀ i, (F.size i : ℝ) + rho * N ≤ (density - rho) * (gamma * N)) :
    ∃ orient : Fin b → Fin 2 ≃ Fin 2,
      ∃ E : DynamicAttachedForestEmbedding F H (fun _ => z) orient live,
        ResidualInvariant dx dy N (epsilon * N)
          ((N : ℝ) - (live 0 \ E.used 0).card) ((N : ℝ) - (live 1 \ E.used 1).card) := by
  let rootPool : Fin 2 → Finset V := fun c => (live c).filter (H.Adj z)
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hreserve : 0 ≤ gamma * (N : ℝ) := mul_nonneg hgamma hN
  have he : 0 ≤ epsilon * (N : ℝ) := by linarith only [herror]
  have hliveN (c : Fin 2) : ((live c).card : ℝ) ≤ N := by
    exact_mod_cast (Finset.card_le_card (hlive c)).trans_eq (hwhole c)
  have hgateN : 8 * (epsilon * (N : ℝ)) ≤ lambda * (gamma * N) := by
    nlinarith only [mul_le_mul_of_nonneg_right hgate hN]
  let D := appendixData_of_residual F N gamma epsilon lambda dx dy
    (live 0).card (live 1).card (rootPool 0).card (rootPool 1).card small
    herror hreserve hlambda hlambdaHalf hdxlo hdxhi hdylo hdyhi hgateN
    (hliveN 0) (hliveN 1) hXY (Finset.card_filter_le _ _) (Finset.card_filter_le _ _)
    hP hQ hinv hbudget hlower hupper hsmall
  obtain ⟨E⟩ := exists_partThreeDynamicGroupEmbedding F small ⌈3 * (epsilon * N)⌉₊
    ⌈(gamma + 3 * epsilon) * N⌉₊ H z whole live rootPool rho density gamma epsilon N D
    huniform hlive (fun c => Finset.filter_subset _ _) hdisjoint hdensity hfactor he
    (fun c => by simpa only [hwhole c] using hregularRoot)
    (fun c => by simpa only [hwhole c] using hregularInterior)
    (fun i c => by simpa only [hwhole c] using hcomponent i)
    (fun _ _ hw => (Finset.mem_filter.mp hw).2)
  have hload (c : Fin 2) : sideLoad F E.orient c ≤ (live c).card := by
    rw [← E.embedding.card_used c]
    exact Finset.card_le_card (E.embedding.used_subset c)
  have htri := appendix_trichotomy_real F E.orient (live 0).card (live 1).card
    (rootPool 0).card (rootPool 1).card ⌈3 * (epsilon * N)⌉₊ small
    (hload 0) (hload 1) E.trichotomy
  have hR : (⌈3 * (epsilon * (N : ℝ))⌉₊ : ℝ) ≤ 4 * (epsilon * N) := by
    have hc := Nat.ceil_lt_add_one (show 0 ≤ 3 * (epsilon * (N : ℝ)) by positivity)
    linarith only [hc, herror]
  have hnew := ResidualInvariant.advance dx dy N (epsilon * N)
    (N - (live 0).card) (N - (live 1).card) (sideLoad F E.orient 0) (sideLoad F E.orient 1)
    (rootPool 0).card (rootPool 1).card ⌈3 * (epsilon * N)⌉₊ small
    (hlambda.trans hdxlo) (by linarith only [hdxhi, hlambda])
    (hlambda.trans hdylo) (by linarith only [hdyhi, hlambda])
    (sub_nonneg.mpr (hliveN 0)) (sub_nonneg.mpr (hliveN 1))
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) he hR (by linarith only [hsmall, he])
    (by simpa only [sub_sub_cancel] using hP) (by simpa only [sub_sub_cancel] using hQ)
    hinv (by simpa only [sub_sub_cancel] using htri)
  have hnewCount (c : Fin 2) :
      ((N : ℝ) - (live c).card) + sideLoad F E.orient c =
        (N : ℝ) - (live c \ E.embedding.used c).card := by
    rw [E.embedding.card_residual c, Nat.cast_sub (hload c)]
    ring
  rw [hnewCount 0, hnewCount 1] at hnew
  exact ⟨E.orient, E.embedding, hnew⟩

end Erdos547b.ZhaoSourcePartThreeLiveStep

#print axioms Erdos547b.ZhaoSourcePartThreeLiveStep.exists_partThree_live_step
