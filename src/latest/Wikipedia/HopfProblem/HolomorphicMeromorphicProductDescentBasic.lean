import Wikipedia.HopfProblem.HolomorphicMeromorphicPullbackFunctor

/-!
# Native holomorphic slices and projection pullback on product boxes

Every map uses the original self-model atlas on the ambient normed
spaces. The product box is the literal product open set. Holomorphic
slices are obtained by actual composition and restriction; the slice
map is not assumed to pull back arbitrary meromorphic germs.
-/

noncomputable section

open TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicMeromorphic.ProductDescent

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

local notation "I₁" => modelWithCornersSelf ℂ ℂ
local notation "IP" => modelWithCornersSelf ℂ (ℂ × E)

/-- The literal product open set in the original ambient product space. -/
def box (U : Opens ℂ) (V : Opens E) : Opens (ℂ × E) :=
  ⟨(U : Set ℂ) ×ˢ (V : Set E), U.isOpen.prod V.isOpen⟩

def boxPoint (U : Opens ℂ) (V : Opens E) (z : U) (v : V) : box U V :=
  ⟨(z.val, v.val), ⟨z.property, v.property⟩⟩

def basePoint (U : Opens ℂ) (V : Opens E) (x : box U V) : U :=
  ⟨x.val.1, x.property.1⟩

def fibrePoint (U : Opens ℂ) (V : Opens E) (x : box U V) : V :=
  ⟨x.val.2, x.property.2⟩

/-- The actual ambient first projection in its native self-model atlas. -/
def fstMap : ContMDiffMap IP I₁ (ℂ × E) ℂ ω :=
  ⟨Prod.fst, contDiff_fst.contMDiff⟩

theorem fstMap_isOpenMap : IsOpenMap (fstMap (E := E)) := isOpenMap_fst

/-- The actual fixed-fibre holomorphic map; no openness is asserted. -/
def sliceMap (w : E) : ContMDiffMap I₁ IP ℂ (ℂ × E) ω :=
  ⟨fun z => (z, w), (contDiff_id.prodMk contDiff_const).contMDiff⟩

theorem box_le_fst_preimage (U : Opens ℂ) (V : Opens E) :
    box U V ≤ pullbackOpen IP I₁ fstMap U := fun _ hx => hx.1

theorem sliceSource_le (U : Opens ℂ) (V : Opens E) (w : V) :
    U ≤ pullbackOpen I₁ IP (sliceMap w.val) (box U V) :=
  fun _ hz => ⟨hz, w.property⟩

/-- Restriction of a genuine holomorphic product function to one fixed fibre point. -/
def sliceHolomorphic (U : Opens ℂ) (V : Opens E) (w : V) :
    HolomorphicFunctionSheaf.Section IP (ℂ × E) (box U V) →+*
      HolomorphicFunctionSheaf.Section I₁ ℂ U :=
  (HolomorphicFunctionSheaf.restrictionAlgHom I₁ ℂ (sliceSource_le U V w)).toRingHom.comp
    (holomorphicPullback I₁ IP (sliceMap w.val) (box U V))

@[simp] theorem sliceHolomorphic_apply (U : Opens ℂ) (V : Opens E) (w : V)
    (p : HolomorphicFunctionSheaf.Section IP (ℂ × E) (box U V)) (z : U) :
    sliceHolomorphic U V w p z = p (boxPoint U V z w) := rfl

/-- A base holomorphic function, pulled back by the ambient projection and
then literally restricted to the product box. -/
def liftHolomorphic (U : Opens ℂ) (V : Opens E) :
    HolomorphicFunctionSheaf.Section I₁ ℂ U →+*
      HolomorphicFunctionSheaf.Section IP (ℂ × E) (box U V) :=
  (HolomorphicFunctionSheaf.restrictionAlgHom IP (ℂ × E)
    (box_le_fst_preimage U V)).toRingHom.comp (holomorphicPullback IP I₁ fstMap U)

@[simp] theorem liftHolomorphic_apply (U : Opens ℂ) (V : Opens E)
    (p : HolomorphicFunctionSheaf.Section I₁ ℂ U) (x : box U V) :
    liftHolomorphic U V p x = p (basePoint U V x) := rfl

/-- The actual meromorphic first-projection pullback restricted to the literal box. -/
def pullbackToBox (U : Opens ℂ) (V : Opens E) :
    Section I₁ ℂ U →+* Section IP (ℂ × E) (box U V) :=
  (restrictionRingHom IP (ℂ × E) (box_le_fst_preimage U V)).comp
    (pullbackRingHom IP I₁ fstMap fstMap_isOpenMap U)

@[simp] theorem pullbackToBox_apply (U : Opens ℂ) (V : Opens E)
    (s : Section I₁ ℂ U) (x : box U V) :
    pullbackToBox U V s x =
      germPullback IP I₁ fstMap fstMap_isOpenMap x.val (s (basePoint U V x)) := rfl

/-- A valid base denominator stays valid on the box, by the actual injective
stalk pullback for the open ambient projection and literal restriction. -/
theorem liftHolomorphic_nonzero_germs (U : Opens ℂ) (V : Opens E)
    (q : HolomorphicFunctionSheaf.Section I₁ ℂ U)
    (hq : ∀ z : U, holomorphicGerm I₁ ℂ U z q ≠ 0) :
    ∀ x : box U V, holomorphicGerm IP (ℂ × E) (box U V) x (liftHolomorphic U V q) ≠ 0 := by
  intro x hx
  apply holomorphicPullback_nonzero_germs IP I₁ fstMap fstMap_isOpenMap U q hq
    (Set.inclusion (box_le_fst_preimage U V) x)
  exact (holomorphicGerm_restrict IP (ℂ × E) (box_le_fst_preimage U V) x
    (holomorphicPullback IP I₁ fstMap U q)).symm.trans hx

/-- Pullback of a genuine base fraction is the expected fraction of the
actual lifted holomorphic numerator and denominator on the box. -/
theorem pullbackToBox_ofFraction_apply (U : Opens ℂ) (V : Opens E)
    (p q : HolomorphicFunctionSheaf.Section I₁ ℂ U)
    (hq : ∀ z : U, holomorphicGerm I₁ ℂ U z q ≠ 0) (x : box U V) :
    pullbackToBox U V (ofFraction I₁ ℂ U p q hq) x =
      fraction IP (ℂ × E) (box U V) (liftHolomorphic U V p) (liftHolomorphic U V q) x :=
  (germPullback_fraction IP I₁ fstMap fstMap_isOpenMap U p q
    (Set.inclusion (box_le_fst_preimage U V) x)).trans
      (fraction_restrict IP (ℂ × E) (box_le_fst_preimage U V)
        (holomorphicPullback IP I₁ fstMap U p) (holomorphicPullback IP I₁ fstMap U q) x).symm

end Wikipedia.HopfProblem.HolomorphicMeromorphic.ProductDescent
