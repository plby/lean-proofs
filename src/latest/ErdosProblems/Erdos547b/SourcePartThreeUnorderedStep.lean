/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourcePartThreeLiveStep
import ErdosProblems.Erdos547b.SourceDynamicSideRelabel

/-!
# Part-3 live step without a permanent endpoint ordering

Order the two current live sets only for the local Appendix call, then
restore their physical labels without changing the graph-copy maps.
-/

open scoped SimpleGraph Classical
noncomputable section

namespace Erdos547b.ZhaoSourcePartThreeLiveStep

open Finset SimpleGraph Erdos547b.RegularPair
open Erdos547b.ZhaoLemma58GroupedSmallForest Erdos547b.ZhaoSourcePartThreeResidualNumerics

theorem exists_partThree_live_step_unordered
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
  by_cases hXY : (live 0).card ≤ (live 1).card
  · exact exists_partThree_live_step F H z whole live N small gamma epsilon rho density lambda dx dy
      herror hgamma hlambda hlambdaHalf hdxlo hdxhi hdylo hdyhi hgate hwhole hlive hXY hP hQ
      hinv hbudget hlower hupper hsmall huniform hdisjoint hdensity hfactor hregularRoot
      hregularInterior hcomponent
  · let side : Fin 2 ≃ Fin 2 := Equiv.swap 0 1
    have hs0 : side 0 = 1 := Equiv.swap_apply_left _ _
    have hs1 : side 1 = 0 := Equiv.swap_apply_right _ _
    have hbudget' : ((N : ℝ) - (live (side 0)).card) + (N - (live (side 1)).card) + F.order ≤
        (dy + dx + lambda) * N - 2 * (gamma * N) - 24 * (epsilon * N) := by
      rw [hs0, hs1]
      nlinarith only [hbudget]
    obtain ⟨orient, E, hnew⟩ := exists_partThree_live_step F H z
      (fun c => whole (side c)) (fun c => live (side c)) N small
      gamma epsilon rho density lambda dy dx herror hgamma hlambda hlambdaHalf
      hdylo hdyhi hdxlo hdxhi hgate (fun c => hwhole (side c)) (fun c => hlive (side c))
      (by simpa only [hs0, hs1] using le_of_not_ge hXY)
      (by simpa only [hs0] using hQ) (by simpa only [hs1] using hP)
      (by simpa only [hs0, hs1] using hinv.swap) hbudget' hlower hupper hsmall
      (by simpa only [hs0, hs1] using huniform.symm)
      (by simpa only [hs0, hs1] using hdisjoint.symm)
      (by simpa only [hs0, hs1, H.edgeDensity_comm] using hdensity)
      hfactor hregularRoot hregularInterior hcomponent
    let E' := E.relabelSides side
    have hu0 : E'.used 0 = E.used 1 := by
      simpa only [hs1] using E.used_relabelSides side 1
    have hu1 : E'.used 1 = E.used 0 := by
      simpa only [hs0] using E.used_relabelSides side 0
    refine ⟨fun i => (orient i).trans side, E', ?_⟩
    rw [hu0, hu1]
    simpa only [hs0, hs1] using hnew.swap

end Erdos547b.ZhaoSourcePartThreeLiveStep

#print axioms Erdos547b.ZhaoSourcePartThreeLiveStep.exists_partThree_live_step_unordered
