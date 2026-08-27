import Arxiv.Arxiv2411_18291.ExchangeReplacement
import Arxiv.Arxiv2411_18291.ModularCliqueGenerators

/-!
# Modular generation through an exchange

If every replacement clique is generated, the base clique is generated.
This is the algebraic conclusion needed after constructing monochromatic
near and far cliques, and it remains valid after any vertex embedding.
-/

open Finset
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

variable {W V : Type*} [Fintype W] [Fintype V] [DecidableEq W] [DecidableEq V]
variable {q r : ℕ}

omit [Fintype W] [DecidableEq W] in
theorem sum_modularCliqueVector (N : ℕ) (D : Finset (Block V q)) :
    ∑ Q ∈ D, modularCliqueVector N r Q =
      fun e => ((boundary r (indicator D) e : ℤ) : ZMod N) := by
  funext e
  rw [Finset.sum_apply, boundary_indicator]
  simp only [modularCliqueVector, ← sum_filter, sum_const, nsmul_eq_mul, mul_one,
    Int.cast_natCast]

omit [Fintype V] [DecidableEq V] in
theorem ExchangeSystem.modular_decompositions (S : ExchangeSystem W q r) (N : ℕ) :
    ∑ Q ∈ S.positive, modularCliqueVector N r Q =
      ∑ Q ∈ S.negative, modularCliqueVector N r Q := by
  rw [sum_modularCliqueVector, sum_modularCliqueVector,
    S.positive_decomposition, S.negative_decomposition]

omit [Fintype V] [DecidableEq V] in
theorem ExchangeSystem.modular_replacement (S : ExchangeSystem W q r) (N : ℕ) :
    modularCliqueVector N r S.base = (∑ Q ∈ S.negative, modularCliqueVector N r Q) -
      ∑ Q ∈ S.positive.erase S.base, modularCliqueVector N r Q := by
  rw [← S.modular_decompositions N]
  have hp := sum_erase_add S.positive (modularCliqueVector N r) S.base_mem
  rw [← hp]
  abel

omit [Fintype V] [DecidableEq V] in
theorem ExchangeSystem.modular_base_mem (S : ExchangeSystem W q r) (N : ℕ)
    (A : AddSubgroup (Block W r → ZMod N))
    (hrep : ∀ Q ∈ S.replacementCliques, modularCliqueVector N r Q ∈ A) :
    modularCliqueVector N r S.base ∈ A := by
  rw [S.modular_replacement N]
  apply A.sub_mem
  · exact A.sum_mem (fun Q hQ => hrep Q (mem_union_left _ hQ))
  · exact A.sum_mem (fun Q hQ => hrep Q (mem_union_right _ hQ))

omit [Fintype V] in
theorem ExchangeSystem.modular_image_base_mem [Finite V] (S : ExchangeSystem W q r) (N : ℕ)
    (f : W ↪ V) (A : AddSubgroup (Block V r → ZMod N))
    (hrep : ∀ Q ∈ S.replacementCliques, modularCliqueVector N r (mapBlock f Q) ∈ A) :
    modularCliqueVector N r (mapBlock f S.base) ∈ A := by
  let _ := Fintype.ofFinite V
  apply (S.map f).modular_base_mem N A
  intro Q hQ
  rw [S.replacementCliques_map f] at hQ
  obtain ⟨P, hP, hPQ⟩ := (mem_mapGraph _ _ _).mp hQ
  rw [← hPQ]
  exact hrep P hP

end Arxiv2411_18291
