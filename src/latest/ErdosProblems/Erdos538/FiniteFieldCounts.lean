import Mathlib

/- Ported from Lean 4.31.0 to 4.33.0; imports, namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos538.IsotropicKernel

open LinearMap Module

/-- The dot-product functional associated to a nonzero finite vector is a
nonzero, hence surjective, linear functional. -/
theorem dotProductEquiv_ne_zero
    {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    {v : ι → K} (hv : v ≠ 0) :
    (dotProductEquiv K ι) v ≠ 0 := by
  exact (dotProductEquiv K ι).map_ne_zero_iff.mpr hv

/-- The kernel of a nonzero functional on a finite vector space has
`q^(finrank-1)` elements. -/
theorem natCard_ker_functional
    {K W : Type*} [Field K] [Fintype K] [AddCommGroup W] [Module K W]
    [Fintype W] (f : W →ₗ[K] K) (hf : f ≠ 0) :
    Nat.card (LinearMap.ker f) =
      Nat.card K ^ (Module.finrank K W - 1) := by
  have hsurj : Function.Surjective f := LinearMap.surjective hf
  have hrange : LinearMap.range f = ⊤ := LinearMap.range_eq_top.mpr hsurj
  have hrank := LinearMap.finrank_range_add_finrank_ker f
  have hcod : Module.finrank K K = 1 := Module.finrank_self K
  have hker : Module.finrank K (LinearMap.ker f) = Module.finrank K W - 1 := by
    rw [hrange, finrank_top, hcod] at hrank
    omega
  have hcardker : Nat.card (LinearMap.ker f) =
      Nat.card K ^ Module.finrank K (LinearMap.ker f) :=
    Module.natCard_eq_pow_finrank (K := K) (V := LinearMap.ker f)
  rw [hcardker, hker]

/-- Over a finite field, the kernel of one nonzero linear equation in `n`
variables has exactly `q^(n-1)` elements. -/
theorem natCard_ker_dotProduct
    {K ι : Type*} [Field K] [Fintype K] [Fintype ι] [DecidableEq ι]
    [Nonempty ι] {v : ι → K} (hv : v ≠ 0) :
    Nat.card (LinearMap.ker ((dotProductEquiv K ι) v)) =
      Nat.card K ^ (Fintype.card ι - 1) := by
  let f : (ι → K) →ₗ[K] K := (dotProductEquiv K ι) v
  have hf : f ≠ 0 := dotProductEquiv_ne_zero hv
  have h := natCard_ker_functional f hf
  rw [Module.finrank_fintype_fun_eq_card K] at h
  exact h

/-- A finite type with a decidable zero has one fewer nonzero elements than
total elements. -/
theorem natCard_ne_zero {X : Type*} [Finite X] [Zero X] [DecidableEq X] :
    Nat.card {x : X // x ≠ 0} = Nat.card X - 1 := by
  change Nat.card (Set.Elem {x : X | x ≠ 0}) = Nat.card X - 1
  rw [Nat.card_coe_set_eq]
  have h := Set.ncard_diff_singleton_of_mem
    (s := (Set.univ : Set X)) (a := (0 : X)) (Set.mem_univ 0)
  have heq : (Set.univ : Set X) \ {0} = {x : X | x ≠ 0} := by
    ext x
    simp
  rw [heq, Set.ncard_univ] at h
  exact h

/-- Excluding the single zero vector from the kernel count leaves
`q^(n-1)-1`; the subtraction form avoids choosing a particular finite-type
instance on the kernel subtype. -/
theorem natCard_ker_dotProduct_sub_one
    {K ι : Type*} [Field K] [Fintype K]
    [Fintype ι] [DecidableEq ι] [Nonempty ι] {v : ι → K} (hv : v ≠ 0) :
    Nat.card (LinearMap.ker ((dotProductEquiv K ι) v)) - 1 =
      Nat.card K ^ (Fintype.card ι - 1) - 1 := by
  rw [natCard_ker_dotProduct hv]

/-- Pairs satisfying a nonzero linear equation in the first coordinate and a
uniquely determined second coordinate are parametrized by the kernel. -/
def badPairEquivKer
    {K W : Type*} [Field K] [AddCommGroup W] [Module K W]
    (f : W →ₗ[K] K) (g : W → K) :
    {p : W × K // f p.1 = 0 ∧ p.2 = g p.1} ≃ LinearMap.ker f where
  toFun p := ⟨p.1.1, p.2.1⟩
  invFun x := ⟨(x.1, g x.1), x.2, rfl⟩
  left_inv p := by
    apply Subtype.ext
    exact Prod.ext rfl p.2.2.symm
  right_inv x := rfl

/-- Exact count underlying the `1/q²` one-extension danger estimate: among
`W × K`, imposing one nonzero linear equation on `W` and then determining the
`K` coordinate leaves `q^(finrank W-1)` pairs. -/
theorem natCard_bad_pairs
    {K W : Type*} [Field K] [Fintype K] [AddCommGroup W] [Module K W]
    [Fintype W] (f : W →ₗ[K] K) (hf : f ≠ 0) (g : W → K) :
    Nat.card {p : W × K // f p.1 = 0 ∧ p.2 = g p.1} =
      Nat.card K ^ (Module.finrank K W - 1) := by
  rw [Nat.card_congr (badPairEquivKer f g)]
  exact natCard_ker_functional f hf

end Erdos538.IsotropicKernel
