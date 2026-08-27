import Arxiv.Arxiv2411_18291.ModularIntegralLift

/-!
# Support of modular clique combinations

Every modular combination vanishes outside the supporting clique family.
For a nontrivial coefficient ring, a generated clique therefore has all
its edges in that support.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [Fintype V] [DecidableEq V] {q r N : ℕ}

theorem modular_generated_zero_outside_support (D : Finset (Block V q))
    {J : Block V r → ZMod N} (hJ : J ∈ generatedSubgroup (modularCliqueVector N r) D)
    (e : Block V r) (he : e ∉ cliqueSupport r D) : J e = 0 := by
  obtain ⟨K, hK, rfl⟩ := exists_integral_boundary_of_modular_generated N D hJ
  obtain ⟨Φ, rfl, hsΦ⟩ := hK
  have hz := boundary_zero_outside_support D (cliqueSupport r D) Φ hsΦ Subset.rfl e he
  change ((boundary r Φ e : ℤ) : ZMod N) = 0
  rw [hz, Int.cast_zero]

theorem cliqueEdges_subset_support_of_modular_generated [Nontrivial (ZMod N)]
    (D : Finset (Block V q)) (Q : Block V q)
    (hQ : modularCliqueVector N r Q ∈ generatedSubgroup (modularCliqueVector N r) D) :
    cliqueEdges r Q ⊆ cliqueSupport r D := by
  intro e heQ
  by_contra he
  have hz := modular_generated_zero_outside_support D hQ e he
  have hsub := (mem_cliqueEdges _ _).mp heQ
  simp only [modularCliqueVector, if_pos hsub, one_ne_zero] at hz

end Arxiv2411_18291
