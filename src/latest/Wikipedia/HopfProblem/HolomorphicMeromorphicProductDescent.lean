import Wikipedia.HopfProblem.HolomorphicMeromorphicProductDescentBasic
import Wikipedia.HopfProblem.HolomorphicMeromorphicIdentity

/-!
# Genuine meromorphic descent on a connected product box

An actual local numerator and denominator satisfying all fibrewise
cross-products descend to the base. One chooses a fibre point where the
denominator has a nonzero value somewhere. The native holomorphic
identity principle makes its slice a valid denominator at every base
point. The original cross-products then give equality of actual
holomorphic stalk cross-products, hence equality in the genuine
meromorphic fraction fields everywhere on the product box.
-/

noncomputable section

open TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicMeromorphic.ProductDescent

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

local notation "I₁" => modelWithCornersSelf ℂ ℂ
local notation "IP" => modelWithCornersSelf ℂ (ℂ × E)

/-- A genuine product denominator has a fixed-fibre slice with nonzero
native holomorphic germ at every point of the preconnected base. -/
theorem exists_slice_nonzero_germs (U : Opens ℂ) (V : Opens E)
    [Nonempty U] [PreconnectedSpace U] [Nonempty V]
    (q : HolomorphicFunctionSheaf.Section IP (ℂ × E) (box U V))
    (hq : ∀ x : box U V, holomorphicGerm IP (ℂ × E) (box U V) x q ≠ 0) :
    ∃ w : V, ∀ z : U, holomorphicGerm I₁ ℂ U z (sliceHolomorphic U V w q) ≠ 0 := by
  classical
  let x₀ : box U V := boxPoint U V (Classical.choice ‹Nonempty U›)
    (Classical.choice ‹Nonempty V›)
  have hex : ∃ x : box U V, q x ≠ 0 := by
    by_contra! hzero
    have he : q = 0 := ContMDiffMap.ext hzero
    exact hq x₀ ((congrArg (holomorphicGerm IP (ℂ × E) (box U V) x₀) he).trans
      (map_zero _))
  obtain ⟨x, hx⟩ := hex
  refine ⟨fibrePoint U V x, ?_⟩
  intro z hz
  have he : sliceHolomorphic U V (fibrePoint U V x) q = 0 :=
    HolomorphicFunctionSheaf.section_eq_of_germ_eq I₁ U
      (sliceHolomorphic U V (fibrePoint U V x) q) 0 z
      (hz.trans (map_zero (holomorphicGerm I₁ ℂ U z)).symm)
  exact hx (congrArg (fun a : HolomorphicFunctionSheaf.Section I₁ ℂ U =>
    a (basePoint U V x)) he)

/-- Any valid fixed-fibre slice is the actual base fraction whose ambient
projection pullback agrees with the original product fraction. -/
theorem fixed_slice_descends (U : Opens ℂ) (V : Opens E)
    (p q : HolomorphicFunctionSheaf.Section IP (ℂ × E) (box U V))
    (hq : ∀ x : box U V, holomorphicGerm IP (ℂ × E) (box U V) x q ≠ 0)
    (hcross : ∀ (z : U) (v w : V),
      p (boxPoint U V z v) * q (boxPoint U V z w) =
        p (boxPoint U V z w) * q (boxPoint U V z v))
    (w : V) (hw : ∀ z : U, holomorphicGerm I₁ ℂ U z (sliceHolomorphic U V w q) ≠ 0) :
    pullbackToBox U V
        (ofFraction I₁ ℂ U (sliceHolomorphic U V w p) (sliceHolomorphic U V w q) hw) =
      ofFraction IP (ℂ × E) (box U V) p q hq := by
  have he : liftHolomorphic U V (sliceHolomorphic U V w p) * q =
      p * liftHolomorphic U V (sliceHolomorphic U V w q) :=
    ContMDiffMap.ext fun x => (hcross (basePoint U V x) (fibrePoint U V x) w).symm
  apply section_ext
  intro x
  exact (pullbackToBox_ofFraction_apply U V (sliceHolomorphic U V w p)
    (sliceHolomorphic U V w q) hw x).trans
      ((fraction_eq_iff IP (ℂ × E) (box U V)
        (liftHolomorphic U V (sliceHolomorphic U V w p))
        (liftHolomorphic U V (sliceHolomorphic U V w q)) p q x
        (liftHolomorphic_nonzero_germs U V (sliceHolomorphic U V w q) hw x) (hq x)).mpr
          (congrArg (holomorphicGerm IP (ℂ × E) (box U V) x) he))

/-- Fibrewise cross-products produce an actual meromorphic section on
the original base open set, with exact projection-pullback equality. -/
theorem exists_descended_section (U : Opens ℂ) (V : Opens E)
    [Nonempty U] [PreconnectedSpace U] [Nonempty V]
    (p q : HolomorphicFunctionSheaf.Section IP (ℂ × E) (box U V))
    (hq : ∀ x : box U V, holomorphicGerm IP (ℂ × E) (box U V) x q ≠ 0)
    (hcross : ∀ (z : U) (v w : V),
      p (boxPoint U V z v) * q (boxPoint U V z w) =
        p (boxPoint U V z w) * q (boxPoint U V z v)) :
    ∃ s : Section I₁ ℂ U,
      pullbackToBox U V s = ofFraction IP (ℂ × E) (box U V) p q hq := by
  obtain ⟨w, hw⟩ := exists_slice_nonzero_germs U V q hq
  exact ⟨ofFraction I₁ ℂ U (sliceHolomorphic U V w p) (sliceHolomorphic U V w q) hw,
    fixed_slice_descends U V p q hq hcross w hw⟩

/-- The descended section agrees at every product point as an actual
fraction-stalk identity under the genuine ambient first-projection map. -/
theorem exists_descended_section_germs (U : Opens ℂ) (V : Opens E)
    [Nonempty U] [PreconnectedSpace U] [Nonempty V]
    (p q : HolomorphicFunctionSheaf.Section IP (ℂ × E) (box U V))
    (hq : ∀ x : box U V, holomorphicGerm IP (ℂ × E) (box U V) x q ≠ 0)
    (hcross : ∀ (z : U) (v w : V),
      p (boxPoint U V z v) * q (boxPoint U V z w) =
        p (boxPoint U V z w) * q (boxPoint U V z v)) :
    ∃ s : Section I₁ ℂ U, ∀ x : box U V,
      germPullback IP I₁ fstMap fstMap_isOpenMap x.val (s (basePoint U V x)) =
        fraction IP (ℂ × E) (box U V) p q x := by
  obtain ⟨s, hs⟩ := exists_descended_section U V p q hq hcross
  exact ⟨s, fun x => congrArg (fun a : Section IP (ℂ × E) (box U V) => a x) hs⟩

end Wikipedia.HopfProblem.HolomorphicMeromorphic.ProductDescent
