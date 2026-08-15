/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.RationalArtinPolynomial
import Mathlib.Algebra.Polynomial.Splits

/-!
# The logarithmic-derivative phase as a sum over polynomial roots

For a split monic polynomial `F`, the usual logarithmic-derivative identity

`F'(r) / F(r) = sum_alpha 1 / (r - alpha)`

identifies the base-field polynomial phase with the sum of the simple-pole
phase over all roots of `F`, counted with multiplicity.  This is the bridge
from the multiplicative polynomial Euler weight to extension-field point
sums.
-/

namespace Erdos387

open Polynomial
open scoped BigOperators

namespace RationalWeil

/-- The base-field simple-pole phase evaluated in an extension field. -/
noncomputable def mappedSimplePolePhase
    {p : ℕ} [NeZero p] {E : Type*} [Field E] [Algebra (ZMod p) E]
    (coeff : ZMod p → ZMod p) (x : E) : E :=
  ∑ r ∈ InverseRational.poleSupport coeff,
    algebraMap (ZMod p) E (coeff r) *
      (x - algebraMap (ZMod p) E r)⁻¹

/-- The finite rearrangement and sign change used in the root-sum formula. -/
theorem neg_sum_mul_rootRecip_eq_sum_mappedSimplePolePhase
    {p : ℕ} [NeZero p] {E : Type*} [Field E] [Algebra (ZMod p) E]
    (coeff : ZMod p → ZMod p) (roots : Multiset E) :
    -(∑ r ∈ InverseRational.poleSupport coeff,
        algebraMap (ZMod p) E (coeff r) *
          (roots.map fun x =>
            (algebraMap (ZMod p) E r - x)⁻¹).sum) =
      (roots.map (mappedSimplePolePhase coeff)).sum := by
  classical
  induction roots using Multiset.induction_on with
  | empty => simp
  | @cons x roots ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons,
        mappedSimplePolePhase, mul_add, Finset.sum_add_distrib]
      rw [neg_add, ih]
      congr 1
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro r hr
      rw [show algebraMap (ZMod p) E r - x =
          -(x - algebraMap (ZMod p) E r) by ring,
        inv_neg]
      ring

/-- After mapping to a splitting field, the logarithmic-derivative phase is
the sum of the mapped point phase over all roots, with multiplicity. -/
theorem map_logarithmicDerivativePhase_eq_sum_roots
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {E : Type*} [Field E] [Algebra (ZMod p) E]
    (coeff : ZMod p → ZMod p) {F : (ZMod p)[X]}
    (hF : AvoidsPoleSupport coeff F)
    (hSplit : (F.map (algebraMap (ZMod p) E)).Splits) :
    algebraMap (ZMod p) E (logarithmicDerivativePhase coeff F) =
      (((F.map (algebraMap (ZMod p) E)).roots.map
        (mappedSimplePolePhase coeff)).sum) := by
  classical
  let f : (ZMod p)[X] →+* E[X] := mapRingHom (algebraMap (ZMod p) E)
  have hratio (r : ZMod p)
      (hr : r ∈ InverseRational.poleSupport coeff) :
      algebraMap (ZMod p) E
          (eval r F.derivative * (eval r F)⁻¹) =
        (((F.map (algebraMap (ZMod p) E)).roots.map fun x =>
          (algebraMap (ZMod p) E r - x)⁻¹).sum) := by
    have hden :
        eval (algebraMap (ZMod p) E r)
            (F.map (algebraMap (ZMod p) E)) ≠ 0 := by
      rw [eval_map_apply]
      intro hzero
      apply hF r hr
      apply (algebraMap (ZMod p) E).injective
      simpa using hzero
    calc
      algebraMap (ZMod p) E
          (eval r F.derivative * (eval r F)⁻¹) =
          eval (algebraMap (ZMod p) E r)
              (F.map (algebraMap (ZMod p) E)).derivative /
            eval (algebraMap (ZMod p) E r)
              (F.map (algebraMap (ZMod p) E)) := by
        simp only [map_mul, map_inv₀, div_eq_mul_inv,
          derivative_map, eval_map_apply]
      _ = _ := by
        simpa only [one_div] using
          hSplit.eval_derivative_div_eval_of_ne_zero hden
  rw [logarithmicDerivativePhase, map_neg, map_sum]
  simp only [map_mul]
  calc
    -(∑ r ∈ InverseRational.poleSupport coeff,
        algebraMap (ZMod p) E (coeff r) *
          algebraMap (ZMod p) E (eval r F.derivative) *
            algebraMap (ZMod p) E (eval r F)⁻¹) =
        -(∑ r ∈ InverseRational.poleSupport coeff,
          algebraMap (ZMod p) E (coeff r) *
            (((F.map (algebraMap (ZMod p) E)).roots.map fun x =>
              (algebraMap (ZMod p) E r - x)⁻¹).sum)) := by
      congr 1
      apply Finset.sum_congr rfl
      intro r hr
      calc
        algebraMap (ZMod p) E (coeff r) *
            algebraMap (ZMod p) E (eval r F.derivative) *
              algebraMap (ZMod p) E (eval r F)⁻¹ =
            algebraMap (ZMod p) E (coeff r) *
              algebraMap (ZMod p) E
                (eval r F.derivative * (eval r F)⁻¹) := by
          rw [map_mul]
          ring
        _ = _ := by rw [hratio r hr]
    _ = _ :=
      neg_sum_mul_rootRecip_eq_sum_mappedSimplePolePhase coeff _

end RationalWeil

end Erdos387
