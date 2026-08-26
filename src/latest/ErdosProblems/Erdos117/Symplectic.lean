import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.FieldTheory.Finiteness
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Linear algebra for the clique bounds and central-factor recursion
-/

namespace Erdos117

open Finset Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

/-- A constant nonzero off-diagonal pairing forces affine independence.
This is the Gram-matrix estimate used for the extraspecial 2-groups. -/
theorem card_le_finrank_add_one_of_pairing
    (B : LinearMap.BilinForm K V) (halt : B.IsAlt) (s : Finset V)
    (hs : (s : Set V).Pairwise (fun x y => B x y = 1)) :
    s.card ≤ finrank K V + 1 := by
  classical
  by_contra h
  obtain ⟨f, hv, hf, x, hx, hfx⟩ :=
    Module.exists_nontrivial_relation_sum_zero_of_finrank_succ_lt_card
      (R := K) (lt_of_not_ge h)
  have hp : ∑ y ∈ s, f y * B x y = 0 := by
    simpa only [map_sum, map_smul, smul_eq_mul, map_zero] using
      congrArg (B x) hv
  have he : ∑ y ∈ s.erase x, f y = 0 := by
    rw [← sum_erase_add _ _ hx, halt x, mul_zero, add_zero] at hp
    convert hp using 1
    apply sum_congr rfl
    intro y hy
    rw [hs hx (mem_erase.mp hy).2 (mem_erase.mp hy).1.symm, mul_one]
  rw [← sum_erase_add _ _ hx, he, zero_add] at hf
  exact hfx hf

/-- A totally isotropic subspace of a nondegenerate bilinear space has at
most half the dimension of the ambient space. -/
theorem twice_finrank_le_of_isotropic
    (B : LinearMap.BilinForm K V) (hB : B.Nondegenerate)
    (W : Submodule K V) (hW : ∀ x ∈ W, ∀ y ∈ W, B x y = 0) :
    2 * finrank K W ≤ finrank K V := by
  have hle : W ≤ B.orthogonal W := by
    intro y hy x hx
    exact hW x hx y hy
  have hdim := Submodule.finrank_mono hle
  rw [B.finrank_orthogonal hB] at hdim
  have hamb := Submodule.finrank_le W
  omega

/-- Restricting a nondegenerate reflexive form to a subspace of codimension `q`
loses at most `2*q` from the rank. The statement uses natural dimensions and
therefore also covers restrictions whose resulting form is zero. -/
theorem finrank_le_restrict_rank_add_twice_codim
    (B : LinearMap.BilinForm K V) (hB : B.Nondegenerate) (hrefl : B.IsRefl)
    (W : Submodule K V) :
    finrank K V ≤ finrank K (LinearMap.range (B.restrict W)) +
      2 * (finrank K V - finrank K W) := by
  have hle : (LinearMap.ker (B.restrict W)).map W.subtype ≤ B.orthogonal W := by
    intro x hx
    obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hx
    intro w hw
    apply hrefl v w
    exact LinearMap.congr_fun (LinearMap.mem_ker.mp hv) ⟨w, hw⟩
  have hdim := Submodule.finrank_mono hle
  rw [Submodule.finrank_map_subtype_eq, B.finrank_orthogonal hB] at hdim
  have hrank := (B.restrict W).finrank_range_add_finrank_ker
  have hW := Submodule.finrank_le W
  omega

end Erdos117
