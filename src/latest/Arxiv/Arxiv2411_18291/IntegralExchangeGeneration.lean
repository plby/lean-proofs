import Arxiv.Arxiv2411_18291.ExchangeElimination
import Arxiv.Arxiv2411_18291.IntegralSpan

/-!
# Integer generation through replacement and elimination exchanges

The actual signed exchange vectors witness generation over the integers,
not merely modulo the decoder modulus. Their support statements persist
after embedding into the ambient vertex set and enlarging the clique family.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {W V : Type*} [Fintype W] [DecidableEq W] [Fintype V] [DecidableEq V]
variable {q r : ℕ}

omit [Fintype W] [DecidableEq W] in
theorem generatedBy_clique {D : Finset (Block V q)} {Q : Block V q} (hQ : Q ∈ D) :
    GeneratedBy D (indicator (cliqueEdges r Q)) := by
  refine ⟨indicator {Q}, boundary_indicator_singleton Q, fun P hP => ?_⟩
  apply indicator_apply_of_notMem
  intro h
  exact hP ((mem_singleton.mp h) ▸ hQ)

omit [Fintype V] [DecidableEq V] in
theorem ExchangeSystem.generatedBy_replacement (S : ExchangeSystem W q r) :
    GeneratedBy S.replacementCliques (indicator (cliqueEdges r S.base)) :=
  ⟨S.replacementVector, S.boundary_replacement, S.replacementVector_support⟩

theorem ExchangeSystem.generatedBy_image_replacement (S : ExchangeSystem W q r)
    (f : W ↪ V) (D : Finset (Block V q))
    (hD : ∀ Q ∈ S.replacementCliques, mapBlock f Q ∈ D) :
    GeneratedBy D (indicator (cliqueEdges r (mapBlock f S.base))) := by
  apply (S.map f).generatedBy_replacement.mono
  intro Q hQ
  rw [S.replacementCliques_map f] at hQ
  obtain ⟨P, hP, rfl⟩ := (mem_mapGraph _ _ _).mp hQ
  exact hD P hP

omit [Fintype V] [DecidableEq V] in
theorem ExchangeSystem.generatedBy_elimination (S : ExchangeSystem W q r)
    {N : Block W q} (hN : N ∈ S.negative) :
    GeneratedBy (S.eliminationCliques N)
      (indicator (cliqueEdges r S.base) - indicator (cliqueEdges r N)) := by
  refine ⟨S.eliminationVector N, S.boundary_elimination hN, fun Q hQ => ?_⟩
  have hp : Q ∉ S.eliminationPositive N := fun h => hQ (mem_union_left _ h)
  have hn : Q ∉ S.eliminationNegative := fun h => hQ (mem_union_right _ h)
  simp only [eliminationVector, Pi.sub_apply, indicator_apply_of_notMem hp,
    indicator_apply_of_notMem hn, sub_self]

theorem ExchangeSystem.eliminationCliques_map (S : ExchangeSystem W q r)
    (f : W ↪ V) (N : Block W q) :
    (S.map f).eliminationCliques (mapBlock f N) = mapGraph f (S.eliminationCliques N) := by
  change (mapGraph f S.negative).erase (mapBlock f N) ∪
    (mapGraph f S.positive).erase (mapBlock f S.base) =
      mapGraph f (S.negative.erase N ∪ S.positive.erase S.base)
  rw [mapGraph_union, mapGraph_erase, mapGraph_erase]

theorem ExchangeSystem.generatedBy_image_elimination (S : ExchangeSystem W q r)
    {N : Block W q} (hN : N ∈ S.negative) (f : W ↪ V) (D : Finset (Block V q))
    (hD : ∀ Q ∈ S.eliminationCliques N, mapBlock f Q ∈ D) :
    GeneratedBy D (indicator (cliqueEdges r (mapBlock f S.base)) -
      indicator (cliqueEdges r (mapBlock f N))) := by
  have hN' : mapBlock f N ∈ (S.map f).negative :=
    (mem_mapGraph f S.negative _).mpr ⟨N, hN, rfl⟩
  apply ((S.map f).generatedBy_elimination hN').mono
  intro Q hQ
  rw [S.eliminationCliques_map f N] at hQ
  obtain ⟨P, hP, rfl⟩ := (mem_mapGraph _ _ _).mp hQ
  exact hD P hP

end Arxiv2411_18291
