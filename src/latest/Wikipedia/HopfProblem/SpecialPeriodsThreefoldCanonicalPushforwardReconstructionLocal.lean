import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPushforwardSectionsNative
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPushforwardSectionsLinear
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPushforwardIdealCoordinate
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPushforwardCuspGeometry
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalMeromorphicSection

/-!
# Reconstructing native canonical sections from actual ideal sections

On the finite base chart the section is the literal product `h Ω`, including
the second elliptic fibre where Ω vanishes. On the full cusp neighborhood it
is the literal product `(h/T) κ`, with actual holomorphic division in the
vanishing ideal and the genuine nowhere-zero native frame `κ = T Ω`.
The two native holomorphic sections agree on their entire overlap.
-/

noncomputable section

open Set Topology TopologicalSpace
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Pushforward.Reconstruction

open HolomorphicFunctionSheaf.SphereH1

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold

local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)

/-- The part of the original base open away from infinity. -/
def finiteBase (U : Opens RiemannSphere) : Opens RiemannSphere :=
  U ⊓ NegativeOneFrames.finiteChart

theorem finiteBase_le (U : Opens RiemannSphere) : finiteBase U ≤ U := inf_le_left

theorem finite_preimage_mem_outside (U : Opens RiemannSphere)
    (x : Threefold.basePreimage (finiteBase U)) : x.val ∈ GlobalCusp.outside :=
  (GlobalCusp.mem_outside x.val).mpr
    ((NegativeOneFrames.mem_finiteChart _).mp x.property.2)

/-- The actual meromorphic form is holomorphic over the whole finite
base chart, including the central elliptic zero surface. -/
def finiteForm (U : Opens RiemannSphere) : PreimageSection (finiteBase U) where
  toFun x := GlobalMeromorphicSection.rawSection x.val
  contMDiff_toFun := by
    intro x
    exact (GlobalMeromorphicSection.rawSectionMap_holomorphicOn_outside_cusp.contMDiffAt
      (GlobalCusp.outside.isOpen.mem_nhds (finite_preimage_mem_outside U x))).comp x
        contMDiff_subtype_val.contMDiffAt

@[simp] theorem finiteForm_apply (U : Opens RiemannSphere)
    (x : Threefold.basePreimage (finiteBase U)) :
    finiteForm U x = GlobalMeromorphicSection.rawSection x.val := rfl

/-- The original cusp frame on the full preimage of the cusp base open. -/
def cuspForm (U : Opens RiemannSphere) : PreimageSection (Cusp.localBase U) where
  toFun x := GlobalCuspExtension.canonicalSection (Cusp.cuspPoint U x)
  contMDiff_toFun := GlobalCuspExtension.canonicalSectionMap_holomorphic.comp
    (Cusp.cuspPoint_holomorphic U)

@[simp] theorem cuspForm_apply (U : Opens RiemannSphere)
    (x : Threefold.basePreimage (Cusp.localBase U)) :
    cuspForm U x = GlobalCuspExtension.canonicalSection (Cusp.cuspPoint U x) := rfl

theorem cuspBase_le_infinityChart (U : Opens RiemannSphere) :
    Cusp.localBase U ≤ NegativeOneFrames.infinityChart := by
  intro p hp
  exact (NegativeOneFrames.mem_infinityChart p).mpr (Cusp.basePatch_ne_zero hp.2)

/-- The actual holomorphic quotient by the reciprocal sphere coordinate
on the full cusp base open, including its point at infinity. -/
def cuspQuotient (U : Opens RiemannSphere) (h : NegativeOneSection U) :
    Threefold.BaseSection (Cusp.localBase U) :=
  IdealCoordinate.divide (Cusp.localBase U) (cuspBase_le_infinityChart U)
    (negativeOneRestriction inf_le_left h)

theorem cuspQuotient_mul_reciprocal (U : Opens RiemannSphere)
    (h : NegativeOneSection U) (p : Cusp.localBase U) :
    cuspQuotient U h p * GlobalCusp.reciprocalCoordinate p.val =
      h.val ⟨p.val, p.property.1⟩ :=
  IdealCoordinate.divide_mul_reciprocal (Cusp.localBase U)
    (cuspBase_le_infinityChart U) (negativeOneRestriction inf_le_left h) p

/-- Actual native canonical reconstruction on the full finite preimage. -/
def finiteSection (U : Opens RiemannSphere) (h : NegativeOneSection U) :
    PreimageSection (finiteBase U) :=
  Threefold.pullbackSection (finiteBase U)
      (HolomorphicFunctionSheaf.restrictionAlgHom 𝓘(ℂ) RiemannSphere inf_le_left h.val) •
    finiteForm U

@[simp] theorem finiteSection_apply (U : Opens RiemannSphere) (h : NegativeOneSection U)
    (x : Threefold.basePreimage (finiteBase U)) :
    finiteSection U h x = h.val ⟨Threefold.projectionSphere x.val, x.property.1⟩ •
      GlobalMeromorphicSection.rawSection x.val := rfl

/-- Actual native canonical reconstruction on the full cusp preimage. -/
def cuspSection (U : Opens RiemannSphere) (h : NegativeOneSection U) :
    PreimageSection (Cusp.localBase U) :=
  Threefold.pullbackSection (Cusp.localBase U) (cuspQuotient U h) • cuspForm U

@[simp] theorem cuspSection_apply (U : Opens RiemannSphere) (h : NegativeOneSection U)
    (x : Threefold.basePreimage (Cusp.localBase U)) :
    cuspSection U h x = cuspQuotient U h (Threefold.baseProjection (Cusp.localBase U) x) •
      GlobalCuspExtension.canonicalSection (Cusp.cuspPoint U x) := rfl

/-- Every point of the finite/cusp overlap lies in the actual regular family. -/
theorem overlap_mem_regular (U : Opens RiemannSphere)
    (x : Threefold.basePreimage (finiteBase U ⊓ Cusp.localBase U)) :
    x.val ∈ Threefold.regularLocus := by
  apply (Threefold.mem_regularLocus_iff_sphere x.val).mpr
  apply (Threefold.mem_sphereRegularPatch _).mpr
  exact ⟨(NegativeOneFrames.mem_finiteChart _).mp x.property.1.2,
    Cusp.basePatch_ne_zero x.property.2.2, Cusp.basePatch_ne_one x.property.2.2⟩

/-- Literal equality in the original canonical fibre on the whole overlap. -/
theorem finiteSection_eq_cuspSection (U : Opens RiemannSphere)
    (h : NegativeOneSection U)
    (x : Threefold.basePreimage (finiteBase U ⊓ Cusp.localBase U)) :
    finiteSection U h ⟨x.val, x.property.1⟩ =
      cuspSection U h ⟨x.val, x.property.2⟩ := by
  rw [finiteSection_apply, cuspSection_apply,
    GlobalCuspExtension.canonicalSection_overlap _ (overlap_mem_regular U x),
    GlobalMeromorphicSection.rawSection_eq_regular (overlap_mem_regular U x),
    ← mul_smul]
  have he := cuspQuotient_mul_reciprocal U h
    (Threefold.baseProjection (Cusp.localBase U) ⟨x.val, x.property.2⟩)
  exact congrArg (fun c : ℂ => c • GlobalRegular.globalSection
    ⟨x.val, overlap_mem_regular U x⟩) he.symm

/-- The finite chart and the original full cusp base neighborhood cover
every base open, without shrinking its domain. -/
theorem finiteBase_sup_cuspBase (U : Opens RiemannSphere) :
    finiteBase U ⊔ Cusp.localBase U = U := by
  apply le_antisymm (sup_le inf_le_left inf_le_left)
  intro p hp
  by_cases hInf : p = (∞ : RiemannSphere)
  · exact Or.inr ⟨hp, hInf ▸ Cusp.infty_mem_basePatch⟩
  · exact Or.inl ⟨hp, (NegativeOneFrames.mem_finiteChart p).mpr hInf⟩

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Pushforward.Reconstruction
