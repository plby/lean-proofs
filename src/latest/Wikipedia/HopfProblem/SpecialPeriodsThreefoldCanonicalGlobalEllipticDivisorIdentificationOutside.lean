import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalEllipticDivisorOrders
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPullbackTrivializationGeneral

/-!
# The genuine divisor-bundle trivialization off the elliptic support

The full inverse image of the open complement carries the original open
submanifold atlas of the independently clutched divisor bundle.  Its
trivialization is the restriction of that bundle's actual chart at index
`none`, and its inverse is the restriction of the actual chart inverse.
Both maps are proved holomorphic in these original atlases.
-/

noncomputable section

open Bundle Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalEllipticDivisor

open TrianglePeriodFamily.Canonical

local notation "IF" => modelWithCornersSelf ℂ Model
local notation "I₁" => modelWithCornersSelf ℂ ℂ
local notation "Iκ" => ModelWithCorners.prod
  (modelWithCornersSelf ℂ Model) (modelWithCornersSelf ℂ ℂ)

attribute [local instance] Threefold.chartedSpace

local instance outsideIdentificationManifold : IsManifold IF ω Threefold.Space :=
  Threefold.space_isManifold

local instance outsideIdentificationHolomorphic :
    ContMDiffVectorBundle ω ℂ divisorBundle.Fiber IF := divisorBundle_holomorphic

/-- The actual full inverse image of the open complement in the original bundle total space. -/
def outsideTotal : TopologicalSpace.Opens divisorBundle.TotalSpace :=
  ⟨(Bundle.TotalSpace.proj : divisorBundle.TotalSpace → Threefold.Space) ⁻¹'
      (outside : Set Threefold.Space), outside.isOpen.preimage divisorBundle.continuous_proj⟩

/-- The original atlas trivialization used by the outside clutching piece. -/
abbrev outsideTrivialization := transitions.core.localTriv (none : Index)

@[simp] theorem outsideTrivialization_baseSet :
    outsideTrivialization.baseSet = (outside : Set Threefold.Space) := rfl

@[simp] theorem outsideTrivialization_source :
    outsideTrivialization.source = (outsideTotal : Set divisorBundle.TotalSpace) := rfl

/-- The base projection, retaining membership of the literal open complement. -/
def outsideProjection (p : outsideTotal) : outside := ⟨p.val.proj, p.property⟩

@[simp] theorem outsideProjection_val (p : outsideTotal) :
    (outsideProjection p).val = p.val.proj := rfl

theorem outsideProjection_holomorphic : ContMDiff Iκ IF ω outsideProjection := by
  have hp : ContMDiff Iκ IF ω (fun p : outsideTotal => p.val.proj) :=
    (Bundle.contMDiff_proj divisorBundle.Fiber).comp contMDiff_subtype_val
  intro p
  have he : ContMDiffAt Iκ IF ω (Subtype.val ∘ outsideProjection) p ↔
      ContMDiffAt Iκ IF ω outsideProjection p :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  exact he.mp (hp p)

/-- The forward map reads the coefficient in the actual original bundle chart. -/
def outsideForward (p : outsideTotal) : outside × ℂ :=
  (outsideProjection p, (outsideTrivialization p.val).2)

@[simp] theorem outsideForward_fst (p : outsideTotal) :
    (outsideForward p).1 = outsideProjection p := rfl

@[simp] theorem outsideForward_snd (p : outsideTotal) :
    (outsideForward p).2 = (transitions.core.localTriv none p.val).2 := rfl

theorem outsideForward_holomorphic : ContMDiff Iκ Iκ ω outsideForward := by
  have ht : ContMDiff Iκ Iκ ω (fun p : outsideTotal => outsideTrivialization p.val) :=
    (Pullback.trivializationPartialDiffeomorph (I := IF) outsideTrivialization).contMDiffOn
      |>.comp_contMDiff contMDiff_subtype_val
        (fun p => outsideTrivialization.mem_source.mpr p.property)
  exact outsideProjection_holomorphic.prodMk ht.snd

/-- The inverse is the original bundle-chart inverse, with its natural open codomain. -/
def outsideBackward (q : outside × ℂ) : outsideTotal :=
  ⟨outsideTrivialization.toOpenPartialHomeomorph.symm (q.1.val, q.2), q.1.property⟩

@[simp] theorem outsideBackward_val (q : outside × ℂ) :
    (outsideBackward q).val =
      (transitions.core.localTriv none).toOpenPartialHomeomorph.symm (q.1.val, q.2) := rfl

@[simp] theorem outsideBackward_projection (q : outside × ℂ) :
    outsideProjection (outsideBackward q) = q.1 := Subtype.ext rfl

theorem outsideBackward_holomorphic : ContMDiff Iκ Iκ ω outsideBackward := by
  have hi : ContMDiff Iκ Iκ ω (fun q : outside × ℂ => (q.1.val, q.2)) :=
    (contMDiff_subtype_val.comp contMDiff_fst).prodMk contMDiff_snd
  have ht : ContMDiff Iκ Iκ ω
      (fun q : outside × ℂ => outsideTrivialization.toOpenPartialHomeomorph.symm
        (q.1.val, q.2)) :=
    (Pullback.trivializationPartialDiffeomorph (I := IF) outsideTrivialization).contMDiffOn_invFun
      |>.comp_contMDiff hi (fun q => outsideTrivialization.mem_target.mpr q.1.property)
  intro q
  have he : ContMDiffAt Iκ Iκ ω (Subtype.val ∘ outsideBackward) q ↔
      ContMDiffAt Iκ Iκ ω outsideBackward q :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  exact he.mp (ht q)

@[simp] theorem outsideBackward_forward (p : outsideTotal) :
    outsideBackward (outsideForward p) = p := by
  apply Subtype.ext
  exact outsideTrivialization.symm_apply_mk_proj
    (outsideTrivialization.mem_source.mpr p.property)

@[simp] theorem outsideForward_backward (q : outside × ℂ) :
    outsideForward (outsideBackward q) = q := by
  apply Prod.ext
  · exact outsideBackward_projection q
  · have he : outsideTrivialization
        (outsideTrivialization.toOpenPartialHomeomorph.symm (q.1.val, q.2)) =
        (q.1.val, q.2) := outsideTrivialization.apply_symm_apply' q.1.property
    exact congrArg (fun p : Threefold.Space × ℂ => p.2) he

/-- A genuine biholomorphism of the original bundle restriction with the
product over the actual open complement. -/
def outsideBundleBiholomorph : Diffeomorph Iκ Iκ outsideTotal (outside × ℂ) ω where
  toFun := outsideForward
  invFun := outsideBackward
  left_inv := outsideBackward_forward
  right_inv := outsideForward_backward
  contMDiff_toFun := outsideForward_holomorphic
  contMDiff_invFun := outsideBackward_holomorphic

@[simp] theorem outsideBundleBiholomorph_apply (p : outsideTotal) :
    outsideBundleBiholomorph p =
      (outsideProjection p, (transitions.core.localTriv none p.val).2) := rfl

@[simp] theorem outsideBundleBiholomorph_projection (p : outsideTotal) :
    (outsideBundleBiholomorph p).1 = outsideProjection p := rfl

@[simp] theorem outsideBundleBiholomorph_symm_val (q : outside × ℂ) :
    (outsideBundleBiholomorph.symm q).val =
      (transitions.core.localTriv none).toOpenPartialHomeomorph.symm (q.1.val, q.2) := rfl

@[simp] theorem outsideBundleBiholomorph_symm_projection (q : outside × ℂ) :
    outsideProjection (outsideBundleBiholomorph.symm q) = q.1 :=
  outsideBackward_projection q

/-- A vector in a specified original fibre, regarded as a point of the actual restriction. -/
def outsideFiberPoint (x : outside) (v : divisorBundle.Fiber x.val) : outsideTotal :=
  ⟨⟨x.val, v⟩, x.property⟩

@[simp] theorem outsideFiberPoint_val (x : outside) (v : divisorBundle.Fiber x.val) :
    (outsideFiberPoint x v).val = (⟨x.val, v⟩ : divisorBundle.TotalSpace) := rfl

/-- The genuine fibrewise continuous linear equivalence supplied by the original chart. -/
def outsideFiberEquiv (x : outside) : divisorBundle.Fiber x.val ≃L[ℂ] ℂ :=
  outsideTrivialization.continuousLinearEquivAt ℂ x.val x.property

@[simp] theorem outsideFiberEquiv_apply (x : outside) (v : divisorBundle.Fiber x.val) :
    outsideFiberEquiv x v = (transitions.core.localTriv none ⟨x.val, v⟩).2 := rfl

/-- The total-space biholomorphism has the original linear chart map on every fibre. -/
theorem outsideBundleBiholomorph_fiber_apply (x : outside) (v : divisorBundle.Fiber x.val) :
    outsideBundleBiholomorph (outsideFiberPoint x v) = (x, outsideFiberEquiv x v) :=
  Prod.ext (Subtype.ext rfl) rfl

theorem outsideBundleBiholomorph_snd_add (x : outside) (v w : divisorBundle.Fiber x.val) :
    (outsideBundleBiholomorph (outsideFiberPoint x (v + w))).2 =
      (outsideBundleBiholomorph (outsideFiberPoint x v)).2 +
        (outsideBundleBiholomorph (outsideFiberPoint x w)).2 := by
  change outsideFiberEquiv x (v + w) = outsideFiberEquiv x v + outsideFiberEquiv x w
  exact map_add (outsideFiberEquiv x) v w

theorem outsideBundleBiholomorph_snd_smul (x : outside) (c : ℂ)
    (v : divisorBundle.Fiber x.val) :
    (outsideBundleBiholomorph (outsideFiberPoint x (c • v))).2 =
      c • (outsideBundleBiholomorph (outsideFiberPoint x v)).2 := by
  change outsideFiberEquiv x (c • v) = c • outsideFiberEquiv x v
  exact map_smul (outsideFiberEquiv x) c v

/-- The inverse biholomorphism is also exactly the original inverse fibre equivalence. -/
theorem outsideBundleBiholomorph_symm_fiber (x : outside) (c : ℂ) :
    (outsideBundleBiholomorph.symm (x, c)).val =
      (⟨x.val, (outsideFiberEquiv x).symm c⟩ : divisorBundle.TotalSpace) :=
  outsideTrivialization.symm_apply_eq_mk_continuousLinearEquivAt_symm
    (R := ℂ) x.val x.property c

/-- The actual canonical section restricted to the original open complement. -/
def outsideCanonicalSectionMap (x : outside) : outsideTotal :=
  outsideFiberPoint x (canonicalSection x.val)

@[simp] theorem outsideCanonicalSectionMap_val (x : outside) :
    (outsideCanonicalSectionMap x).val = canonicalSectionMap x.val := rfl

/-- The divisor's canonical section has coefficient one in the actual outside chart. -/
theorem outsideFiberEquiv_canonicalSection (x : outside) :
    outsideFiberEquiv x (canonicalSection x.val) = 1 :=
  canonicalSection_localCoefficient none x.property

theorem outsideBundleBiholomorph_canonicalSection (x : outside) :
    outsideBundleBiholomorph (outsideCanonicalSectionMap x) = (x, 1) := by
  change outsideBundleBiholomorph (outsideFiberPoint x (canonicalSection x.val)) = _
  rw [outsideBundleBiholomorph_fiber_apply, outsideFiberEquiv_canonicalSection]

theorem outsideBundleBiholomorph_smul_canonicalSection (x : outside) (c : ℂ) :
    outsideBundleBiholomorph (outsideFiberPoint x (c • canonicalSection x.val)) = (x, c) := by
  rw [outsideBundleBiholomorph_fiber_apply, map_smul,
    outsideFiberEquiv_canonicalSection, smul_eq_mul, mul_one]

/-- The actual inverse sends a scalar to that scalar times the actual canonical section. -/
theorem outsideBundleBiholomorph_symm_eq_smul_canonicalSection (x : outside) (c : ℂ) :
    (outsideBundleBiholomorph.symm (x, c)).val =
      (⟨x.val, c • canonicalSection x.val⟩ : divisorBundle.TotalSpace) := by
  have he : outsideBundleBiholomorph.symm (x, c) =
      outsideFiberPoint x (c • canonicalSection x.val) := by
    apply outsideBundleBiholomorph.injective
    change outsideBundleBiholomorph (outsideBundleBiholomorph.symm (x, c)) =
      outsideBundleBiholomorph (outsideFiberPoint x (c • canonicalSection x.val))
    rw [outsideBundleBiholomorph.apply_symm_apply,
      outsideBundleBiholomorph_smul_canonicalSection]
  exact congrArg Subtype.val he

/-- Holomorphicity of the actual section map into the original restricted total space. -/
theorem outsideCanonicalSectionMap_holomorphic :
    ContMDiff IF Iκ ω outsideCanonicalSectionMap := by
  have he : outsideCanonicalSectionMap =
      (fun x : outside => outsideBundleBiholomorph.symm (x, 1)) := by
    funext x
    apply outsideBundleBiholomorph.injective
    change outsideBundleBiholomorph (outsideCanonicalSectionMap x) =
      outsideBundleBiholomorph (outsideBundleBiholomorph.symm (x, 1))
    rw [outsideBundleBiholomorph_canonicalSection, outsideBundleBiholomorph.apply_symm_apply]
  rw [he]
  exact outsideBundleBiholomorph.symm.contMDiff.comp
    (contMDiff_id.prodMk contMDiff_const)

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalEllipticDivisor
