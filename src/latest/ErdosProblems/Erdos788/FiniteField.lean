import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Finite-field interfaces for the upper construction

These lemmas isolate the two algebraic facts used later: distinct affine
graphs meet in at most one point, and a surjective map
`𝔽_p^(2r) → 𝔽_p^r` has a kernel of size `p^r`.
-/

open scoped BigOperators

namespace Erdos788

theorem affine_graph_eq_unique {K : Type*} [Field K]
    {a b c d x y : K} (hcoeff : (a, b) ≠ (c, d))
    (hx : a * x + b = c * x + d)
    (hy : a * y + b = c * y + d) : x = y := by
  have hprod : (a - c) * (x - y) = 0 := by
    linear_combination hx - hy
  rcases mul_eq_zero.mp hprod with hac | hxy
  · have ha : a = c := sub_eq_zero.mp hac
    have hb : b = d := by
      rw [ha] at hx
      exact add_left_cancel hx
    exact (hcoeff (Prod.ext ha hb)).elim
  · exact sub_eq_zero.mp hxy

section Kernel

variable (p r : ℕ) [Fact p.Prime]

theorem kernel_card_of_surjective
    (F : (Fin (2 * r) → ZMod p) →ₗ[ZMod p] (Fin r → ZMod p))
    (hF : Function.Surjective F) :
    Nat.card F.ker = p ^ r := by
  have hrange : F.range = ⊤ := LinearMap.range_eq_top.mpr hF
  have hfrange : Module.finrank (ZMod p) F.range = r := by
    rw [hrange, finrank_top, Module.finrank_fintype_fun_eq_card]
    simp
  have hfdomain :
      Module.finrank (ZMod p) (Fin (2 * r) → ZMod p) = 2 * r := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp
  have hfker : Module.finrank (ZMod p) F.ker = r := by
    have h := F.finrank_range_add_finrank_ker
    rw [hfrange, hfdomain] at h
    omega
  rw [Module.natCard_eq_pow_finrank (K := ZMod p) (V := F.ker),
    Nat.card_zmod, hfker]

/-- The kernel represented as a finset of the ambient vector space. -/
def kernelFinset
    (F : (Fin (2 * r) → ZMod p) →ₗ[ZMod p] (Fin r → ZMod p)) :
    Finset (Fin (2 * r) → ZMod p) :=
  {x | F x = 0}.toFinset

theorem kernelFinset_card_of_surjective
    (F : (Fin (2 * r) → ZMod p) →ₗ[ZMod p] (Fin r → ZMod p))
    (hF : Function.Surjective F) :
    (kernelFinset p r F).card = p ^ r := by
  rw [kernelFinset, Set.toFinset_card, ← Nat.card_eq_fintype_card]
  exact kernel_card_of_surjective p r F hF

/-- The union of `|Y|` surjective kernels has size at most `|Y| p^r`. -/
theorem kernel_palette_card_le {ι : Type*} [DecidableEq ι]
    (Y : Finset ι)
    (F : ι → (Fin (2 * r) → ZMod p) →ₗ[ZMod p] (Fin r → ZMod p))
    (hF : ∀ y ∈ Y, Function.Surjective (F y)) :
    (Y.biUnion (kernelFinset p r ∘ F)).card ≤ Y.card * p ^ r := by
  calc
    (Y.biUnion (kernelFinset p r ∘ F)).card
        ≤ ∑ y ∈ Y, (kernelFinset p r (F y)).card := Finset.card_biUnion_le
    _ = ∑ _y ∈ Y, p ^ r := by
      apply Finset.sum_congr rfl
      intro y hy
      exact kernelFinset_card_of_surjective p r (F y) (hF y hy)
    _ = Y.card * p ^ r := by simp

end Kernel

end Erdos788
