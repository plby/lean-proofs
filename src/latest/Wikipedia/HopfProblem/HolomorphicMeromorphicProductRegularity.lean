import Wikipedia.HopfProblem.HolomorphicMeromorphicProductDescentBasic
import Wikipedia.HopfProblem.HolomorphicMeromorphicPullbackRegular
import Wikipedia.HopfProblem.HolomorphicMeromorphicScalarBasic

/-!
# Product projection reflects native meromorphic regularity

The actual holomorphic slice through a product point is a left inverse
to projection on the original holomorphic stalks. Applying this left
inverse to a cleared-denominator identity reflects regularity of an
arbitrary meromorphic germ. The slice is not asserted to pull back
arbitrary meromorphic functions.
-/

noncomputable section

open TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicMeromorphic.ProductDescent

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

local notation "I₁" => modelWithCornersSelf ℂ ℂ
local notation "IP" => modelWithCornersSelf ℂ (ℂ × E)

/-- The actual holomorphic slice retracts the native holomorphic stalk
pullback of the ambient projection. -/
theorem holomorphicPullbackStalk_slice_fst (z : ℂ) (v : E)
    (a : HolomorphicStalk I₁ ℂ z) :
    holomorphicPullbackStalk I₁ IP (sliceMap v) z
      (holomorphicPullbackStalk IP I₁ fstMap (z, v) a) = a :=
  (RingHom.congr_fun (holomorphicPullbackStalk_comp I₁ IP I₁ (sliceMap v) fstMap z) a).trans
    (RingHom.congr_fun (holomorphicPullbackStalk_id I₁ z) a)

/-- A meromorphic base germ whose projection pullback is regular is
itself regular. Only holomorphic stalk pullback along the slice is used. -/
theorem regularAt_of_fst_pullback {U : Opens ℂ} (s : Section I₁ ℂ U)
    (x : pullbackOpen IP I₁ fstMap U)
    (hx : RegularAt IP (ℂ × E) (pullbackSection IP I₁ fstMap fstMap_isOpenMap U s) x) :
    RegularAt I₁ ℂ s (pullbackPoint IP I₁ fstMap U x) := by
  obtain ⟨p, hp⟩ := hx
  let φ : HolomorphicStalk I₁ ℂ x.val.1 →+* HolomorphicStalk IP (ℂ × E) x.val :=
    holomorphicPullbackStalk IP I₁ fstMap x.val
  let ψ : HolomorphicStalk IP (ℂ × E) x.val →+* HolomorphicStalk I₁ ℂ x.val.1 :=
    holomorphicPullbackStalk I₁ IP (sliceMap x.val.2) x.val.1
  have hret : ∀ a, ψ (φ a) = a :=
    holomorphicPullbackStalk_slice_fst x.val.1 x.val.2
  let c : Germ I₁ ℂ x.val.1 := s (pullbackPoint IP I₁ fstMap U x)
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective
    (HolomorphicStalk I₁ ℂ x.val.1) c
  have hb' : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
  have hbA : ofHolomorphicGerm I₁ ℂ x.val.1 b ≠ 0 :=
    (ofHolomorphicGerm_eq_zero_iff I₁ ℂ x.val.1 b).not.mpr hb'
  have hφb : φ b ≠ 0 :=
    (map_eq_zero_iff φ (holomorphicPullbackStalk_injective IP I₁ fstMap
      fstMap_isOpenMap x.val)).not.mpr hb'
  have hbB : ofHolomorphicGerm IP (ℂ × E) x.val (φ b) ≠ 0 :=
    (ofHolomorphicGerm_eq_zero_iff IP (ℂ × E) x.val (φ b)).not.mpr hφb
  have hpb : ofHolomorphicGerm IP (ℂ × E) x.val p =
      ofHolomorphicGerm IP (ℂ × E) x.val (φ a) /
        ofHolomorphicGerm IP (ℂ × E) x.val (φ b) := by
    refine hp.trans ((congrArg (germPullback IP I₁ fstMap fstMap_isOpenMap x.val)
      hab.symm).trans ?_)
    exact (map_div₀ _ _ _).trans (congrArg₂ (fun u v : Germ IP (ℂ × E) x.val => u / v)
      (germPullback_ofHolomorphicGerm IP I₁ fstMap fstMap_isOpenMap x.val a)
      (germPullback_ofHolomorphicGerm IP I₁ fstMap fstMap_isOpenMap x.val b))
  have hO : p * φ b = φ a :=
    ofHolomorphicGerm_injective IP (ℂ × E) x.val
      ((map_mul (ofHolomorphicGerm IP (ℂ × E) x.val) p (φ b)).trans
        ((eq_div_iff hbB).mp hpb))
  have hA : ψ p * b = a := by
    simpa only [map_mul, hret] using congrArg ψ hO
  refine ⟨ψ p, ?_⟩
  exact ((eq_div_iff hbA).mpr
    ((map_mul (ofHolomorphicGerm I₁ ℂ x.val.1) (ψ p) b).symm.trans
      (congrArg (ofHolomorphicGerm I₁ ℂ x.val.1) hA))).trans hab

/-- The ambient product projection preserves and reflects native
meromorphic regularity at every product point. -/
theorem regularAt_fst_pullback_iff {U : Opens ℂ} (s : Section I₁ ℂ U)
    (x : pullbackOpen IP I₁ fstMap U) :
    RegularAt IP (ℂ × E) (pullbackSection IP I₁ fstMap fstMap_isOpenMap U s) x ↔
      RegularAt I₁ ℂ s (pullbackPoint IP I₁ fstMap U x) :=
  ⟨regularAt_of_fst_pullback s x, regularAt_pullbackSection IP I₁ fstMap fstMap_isOpenMap s x⟩

/-- Canonical values commute with actual product projection pullback,
including at poles, without a regularity hypothesis. -/
theorem value_fst_pullback {U : Opens ℂ} (s : Section I₁ ℂ U)
    (x : pullbackOpen IP I₁ fstMap U) :
    value IP (ℂ × E) (pullbackSection IP I₁ fstMap fstMap_isOpenMap U s) x =
      value I₁ ℂ s (pullbackPoint IP I₁ fstMap U x) := by
  classical
  by_cases ht : RegularAt I₁ ℂ s (pullbackPoint IP I₁ fstMap U x)
  · exact value_pullbackSection_of_regularAt IP I₁ fstMap fstMap_isOpenMap s x ht
  · have hs : ¬ RegularAt IP (ℂ × E)
        (pullbackSection IP I₁ fstMap fstMap_isOpenMap U s) x := fun h =>
      ht (regularAt_of_fst_pullback s x h)
    simp only [value, dif_neg hs, dif_neg ht]

/-- Literal restriction to a product box retains the regularity equivalence. -/
theorem regularAt_pullbackToBox_iff (U : Opens ℂ) (V : Opens E)
    (s : Section I₁ ℂ U) (x : box U V) :
    RegularAt IP (ℂ × E) (pullbackToBox U V s) x ↔
      RegularAt I₁ ℂ s (basePoint U V x) :=
  regularAt_fst_pullback_iff s (Set.inclusion (box_le_fst_preimage U V) x)

/-- Actual box pullback has the exact canonical value of the base section. -/
theorem value_pullbackToBox (U : Opens ℂ) (V : Opens E)
    (s : Section I₁ ℂ U) (x : box U V) :
    value IP (ℂ × E) (pullbackToBox U V s) x = value I₁ ℂ s (basePoint U V x) :=
  value_fst_pullback s (Set.inclusion (box_le_fst_preimage U V) x)

theorem value_pullbackToBox_eq_scalarValue (U : Opens ℂ) (V : Opens E)
    (s : Section I₁ ℂ U) (x : box U V) :
    value IP (ℂ × E) (pullbackToBox U V s) x = scalarValue s x.val.1 :=
  (value_pullbackToBox U V s x).trans (scalarValue_apply s x.val.1 x.property.1).symm

end Wikipedia.HopfProblem.HolomorphicMeromorphic.ProductDescent
