import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalEllipticDivisorIdentificationBasic

/-!
# Holomorphic identification with the native canonical bundle on the elliptic patch

The independently clutched divisor bundle and the original canonical bundle
have identical coefficients in their matched local trivializations throughout
the full order-four elliptic patch.  This proves both directions of the
comparison holomorphic for their original total-space atlases.  The resulting
biholomorphism uses the explicit fibre maps already constructed, including at
the central surface where the distinguished sections vanish.
-/

noncomputable section

open Set Topology Bundle
open scoped ContDiff

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalEllipticDivisor

open TrianglePeriodFamily.Canonical

local notation "I" => modelWithCornersSelf ℂ Model
local notation "I₁" => modelWithCornersSelf ℂ ℂ
local notation "Iκ" => ModelWithCorners.prod
  (modelWithCornersSelf ℂ Model) (modelWithCornersSelf ℂ ℂ)

attribute [local instance] Threefold.chartedSpace

local instance identificationHolomorphicManifold : IsManifold I ω Threefold.Space :=
  Threefold.space_isManifold

/-- Holomorphicity into the unchanged native canonical total space,
proved from the identity coefficient in each matched bundle chart. -/
theorem patchForward_val_holomorphic :
    ContMDiff Iκ Iκ ω
      (fun p : patchTotal => (patchForward p).val) := by
  intro p
  let i := achart Model p.val.proj
  have hp : p.val.proj ∈ i.val.source := mem_chart_source Model p.val.proj
  have htarget : (patchForward p).val ∈
      (Threefold.Canonical.bundle.localTriv i).source := hp
  apply ((Threefold.Canonical.bundle.localTriv i).contMDiffAt_iff
    (f := fun q : patchTotal => (patchForward q).val) (x₀ := p) htarget).mpr
  have hπ : ContMDiffAt Iκ I ω (fun q : patchTotal => q.val.proj) p :=
    (Bundle.contMDiffAt_proj divisorBundle.Fiber).comp p
      contMDiff_subtype_val.contMDiffAt
  refine ⟨?_, ?_⟩
  · simpa only [patchForward_proj] using hπ
  · have hsource : p.val ∈ (divisorBundle.localTriv (some i)).source :=
      ⟨p.property, hp⟩
    have he : ContMDiffAt Iκ Iκ ω (divisorBundle.localTriv (some i)) p.val :=
      (divisorBundle.localTriv (some i)).contMDiffOn.contMDiffAt
        ((divisorBundle.localTriv (some i)).open_source.mem_nhds hsource)
    have hcoef : ContMDiffAt Iκ I₁ ω
        (fun q : patchTotal => (divisorBundle.localTriv (some i) q.val).2) p :=
      (he.comp p contMDiff_subtype_val.contMDiffAt).snd
    apply hcoef.congr_of_eventuallyEq
    filter_upwards [hπ.continuousAt (i.val.open_source.mem_nhds hp)] with q hq
    exact patchForward_localTriv i q hq

/-- The explicit inverse is holomorphic into the independently constructed
divisor total space, using its own original local trivializations. -/
theorem patchBackward_val_holomorphic :
    ContMDiff Iκ Iκ ω
      (fun p : nativePatchTotal => (patchBackward p).val) := by
  intro p
  let i := achart Model p.val.proj
  have hp : p.val.proj ∈ i.val.source := mem_chart_source Model p.val.proj
  have htarget : (patchBackward p).val ∈
      (divisorBundle.localTriv (some i)).source := ⟨p.property, hp⟩
  apply ((divisorBundle.localTriv (some i)).contMDiffAt_iff
    (f := fun q : nativePatchTotal => (patchBackward q).val) (x₀ := p) htarget).mpr
  have hπ : ContMDiffAt Iκ I ω (fun q : nativePatchTotal => q.val.proj) p :=
    (Bundle.contMDiffAt_proj Threefold.Canonical.bundle.Fiber).comp p
      contMDiff_subtype_val.contMDiffAt
  refine ⟨?_, ?_⟩
  · simpa only [patchBackward_proj] using hπ
  · have hsource : p.val ∈ (Threefold.Canonical.bundle.localTriv i).source := hp
    have he : ContMDiffAt Iκ Iκ ω (Threefold.Canonical.bundle.localTriv i) p.val :=
      (Threefold.Canonical.bundle.localTriv i).contMDiffOn.contMDiffAt
        ((Threefold.Canonical.bundle.localTriv i).open_source.mem_nhds hsource)
    have hcoef : ContMDiffAt Iκ I₁ ω
        (fun q : nativePatchTotal =>
          (Threefold.Canonical.bundle.localTriv i q.val).2) p :=
      (he.comp p contMDiff_subtype_val.contMDiffAt).snd
    apply hcoef.congr_of_eventuallyEq
    filter_upwards [hπ.continuousAt (i.val.open_source.mem_nhds hp)] with q hq
    exact patchBackward_localTriv i q hq

/-- Holomorphicity between the actual natural open total-space restrictions. -/
theorem patchForward_holomorphic : ContMDiff Iκ Iκ ω patchForward := by
  intro p
  have h : ContMDiffAt Iκ Iκ ω
      (fun q : patchTotal => (patchForward q).val) p ↔
      ContMDiffAt Iκ Iκ ω patchForward p :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  exact h.mp (patchForward_val_holomorphic p)

theorem patchBackward_holomorphic : ContMDiff Iκ Iκ ω patchBackward := by
  intro p
  have h : ContMDiffAt Iκ Iκ ω
      (fun q : nativePatchTotal => (patchBackward q).val) p ↔
      ContMDiffAt Iκ Iκ ω patchBackward p :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  exact h.mp (patchBackward_val_holomorphic p)

/-- The actual divisor bundle is biholomorphic, fibrewise complex-linearly
over the identity, to the full elliptic-patch restriction of the native
canonical bundle.  No topology or manifold atlas is transported. -/
def patchBundleBiholomorph :
    Diffeomorph Iκ Iκ patchTotal nativePatchTotal ω where
  toFun := patchForward
  invFun := patchBackward
  left_inv := patchBackward_patchForward
  right_inv := patchForward_patchBackward
  contMDiff_toFun := patchForward_holomorphic
  contMDiff_invFun := patchBackward_holomorphic

@[simp] theorem patchBundleBiholomorph_apply (p : patchTotal) :
    patchBundleBiholomorph p = patchForward p := rfl

@[simp] theorem patchBundleBiholomorph_symm_apply (p : nativePatchTotal) :
    patchBundleBiholomorph.symm p = patchBackward p := rfl

@[simp] theorem patchBundleBiholomorph_proj (p : patchTotal) :
    (patchBundleBiholomorph p).val.proj = p.val.proj := rfl

@[simp] theorem patchBundleBiholomorph_symm_proj (p : nativePatchTotal) :
    (patchBundleBiholomorph.symm p).val.proj = p.val.proj := rfl

theorem patchBundleBiholomorph_projection (p : patchTotal) :
    nativePatchTotalProjection (patchBundleBiholomorph p) =
      patchTotalProjection p := rfl

theorem patchBundleBiholomorph_symm_projection (p : nativePatchTotal) :
    patchTotalProjection (patchBundleBiholomorph.symm p) =
      nativePatchTotalProjection p := rfl

/-- The biholomorphism uses exactly the original fibre equivalence. -/
@[simp] theorem patchBundleBiholomorph_mk (x : patch) (v : divisorBundle.Fiber x.val) :
    (patchBundleBiholomorph ⟨⟨x.val, v⟩, x.property⟩).val =
      ⟨x.val, patchFiberEquiv x.val v⟩ := rfl

@[simp] theorem patchBundleBiholomorph_symm_mk (x : patch)
    (v : Threefold.Canonical.bundle.Fiber x.val) :
    (patchBundleBiholomorph.symm ⟨⟨x.val, v⟩, x.property⟩).val =
      ⟨x.val, (patchFiberEquiv x.val).symm v⟩ := rfl

theorem patchBundleBiholomorph_add (x : patch) (v w : divisorBundle.Fiber x.val) :
    id (α := ℂ) (patchBundleBiholomorph ⟨⟨x.val, v + w⟩, x.property⟩).val.2 =
      id (α := ℂ) (patchBundleBiholomorph ⟨⟨x.val, v⟩, x.property⟩).val.2 +
        id (α := ℂ) (patchBundleBiholomorph ⟨⟨x.val, w⟩, x.property⟩).val.2 :=
  (patchFiberEquiv x.val).map_add v w

theorem patchBundleBiholomorph_smul (x : patch) (c : ℂ) (v : divisorBundle.Fiber x.val) :
    id (α := ℂ) (patchBundleBiholomorph ⟨⟨x.val, c • v⟩, x.property⟩).val.2 =
      c • id (α := ℂ) (patchBundleBiholomorph ⟨⟨x.val, v⟩, x.property⟩).val.2 :=
  (patchFiberEquiv x.val).map_smul c v

/-- The actual distinguished divisor section is carried to the original
order-four canonical section, including its central zeros. -/
theorem patchBundleBiholomorph_canonicalSection (x : patch) :
    patchBundleBiholomorph (canonicalSectionOnPatch x) = nativeSectionOnPatch x :=
  patchForward_canonicalSection x

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalEllipticDivisor
