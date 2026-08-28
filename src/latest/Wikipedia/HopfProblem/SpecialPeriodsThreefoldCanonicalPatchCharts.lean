import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalBundle

/-!
# Canonical coordinates on the actual full gluing patches

The inclusion of each genuine local piece is locally biholomorphic.  In
the matching local and glued charts its derivative is the identity.
Across the actual overlaps its derivatives obey the chain rule, giving
the exact gluing rule for arbitrary top covectors.
-/

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical

open TrianglePeriodFamily.Canonical

local notation "IF" => modelWithCornersSelf ℂ Model

attribute [local instance] Threefold.chartedSpace localPieceChartedSpace
  localPiece_nonempty localPiece_isManifold

local instance patchChartsGlobalManifold : IsManifold IF ω Threefold.Space :=
  Threefold.space_isManifold

/-- Every full piece inclusion is a genuine local biholomorphism. -/
theorem inclusion_isLocalDiffeomorph (i : Index) :
    IsLocalDiffeomorph IF IF ω (Threefold.inclusion i) := by
  intro x
  exact ((Threefold.patchBiholomorph i).isLocalDiffeomorph x).comp
    (K := IF) (P := Threefold.Space)
    (isLocalDiffeomorph_subtypeVal IF (Threefold.liftedPatch i)
      (Threefold.patchBiholomorph i x))

/-- The actual piece chart, as an index of the actual global atlas. -/
def patchChart (i : Index) (a : localPiece i) : atlas Model Threefold.Space :=
  ⟨gluingData.gluedChart i a, gluingData.gluedChart_mem_atlas i a⟩

@[simp] theorem patchChart_inclusion (i : Index) (a x : localPiece i) :
    (patchChart i a).val (Threefold.inclusion i x) = chartAt Model a x :=
  gluingData.gluedChart_inclusion i a x

theorem inclusion_mem_patchChart_source (i : Index) (a x : localPiece i)
    (hx : x ∈ (chartAt Model a).source) :
    Threefold.inclusion i x ∈ (patchChart i a).val.source := by
  change Threefold.inclusion i x ∈ (gluingData.parametrization i).target ∧
    (gluingData.parametrization i).symm (Threefold.inclusion i x) ∈ (chartAt Model a).source
  rw [gluingData.parametrization_symm_inclusion, gluingData.parametrization_target]
  exact ⟨mem_range_self x, hx⟩

theorem patchChart_inclusionCoordinate_eventually (i : Index) (a : localPiece i)
    {u : Model} (hu : u ∈ (chartAt Model a).target) :
    ((patchChart i a).val ∘ Threefold.inclusion i ∘ (chartAt Model a).symm) =ᶠ[𝓝 u] id := by
  filter_upwards [(chartAt Model a).open_target.mem_nhds hu] with w hw
  change (patchChart i a).val (Threefold.inclusion i ((chartAt Model a).symm w)) = w
  rw [patchChart_inclusion]
  exact (chartAt Model a).right_inv hw

/-- The matching-chart derivative includes the actual piece inclusion. -/
theorem patchChart_inclusion_fderiv (i : Index) (a : localPiece i)
    {u : Model} (hu : u ∈ (chartAt Model a).target) :
    fderiv ℂ ((patchChart i a).val ∘ Threefold.inclusion i ∘ (chartAt Model a).symm) u =
      ContinuousLinearMap.id ℂ Model := by
  rw [(patchChart_inclusionCoordinate_eventually i a hu).fderiv_eq]
  exact (hasFDerivAt_id u).fderiv

theorem patchChart_inclusion_det (i : Index) (a : localPiece i)
    {u : Model} (hu : u ∈ (chartAt Model a).target) :
    LinearMap.det
      (fderiv ℂ ((patchChart i a).val ∘ Threefold.inclusion i ∘ (chartAt Model a).symm)
        u).toLinearMap = 1 := by
  rw [patchChart_inclusion_fderiv i a hu]
  exact LinearMap.det_id

theorem patchChart_volume_pullback (i : Index) (a : localPiece i)
    {u : Model} (hu : u ∈ (chartAt Model a).target) :
    volume.compContinuousLinearMap
      (fderiv ℂ ((patchChart i a).val ∘ Threefold.inclusion i ∘ (chartAt Model a).symm) u) =
        volume := by
  rw [volume_pullback, patchChart_inclusion_det i a hu, one_smul]

/-- A genuine vector of the global canonical bundle, selected in the
global chart inherited from this actual local piece. -/
def patchLocalFrame (i : Index) (a x : localPiece i) (hx : x ∈ (chartAt Model a).source) :
    bundle.Fiber (Threefold.inclusion i x) :=
  Atlas.localFrame Threefold.Space (patchChart i a)
    ⟨Threefold.inclusion i x, inclusion_mem_patchChart_source i a x hx⟩

theorem patchLocalFrame_ne_zero (i : Index) (a x : localPiece i)
    (hx : x ∈ (chartAt Model a).source) : patchLocalFrame i a x hx ≠ 0 :=
  Atlas.localFrame_ne_zero Threefold.Space (patchChart i a)
    ⟨Threefold.inclusion i x, inclusion_mem_patchChart_source i a x hx⟩

/-- Pullback of that genuine global local frame is exactly the native
local volume, with no unspecified scalar factor. -/
theorem patchLocalFrame_pullback (i : Index) (a x : localPiece i)
    (hx : x ∈ (chartAt Model a).source) :
    (inCoordinates (patchChart i a) (Threefold.inclusion i x)
      (patchLocalFrame i a x hx)).compContinuousLinearMap
        (fderiv ℂ ((patchChart i a).val ∘ Threefold.inclusion i ∘ (chartAt Model a).symm)
          (chartAt Model a x)) = volume := by
  have hf : inCoordinates (patchChart i a) (Threefold.inclusion i x)
      (patchLocalFrame i a x hx) = volume :=
    Atlas.localFrame_inCoordinates Threefold.Space (patchChart i a)
      ⟨Threefold.inclusion i x, inclusion_mem_patchChart_source i a x hx⟩
  rw [hf]
  exact patchChart_volume_pullback i a ((chartAt Model a).map_source hx)

/-- The two piece inclusions give literally the same global point on
every actual overlap. -/
theorem inclusion_transition (i j : Index) (x : localPiece i)
    (hx : x ∈ (gluingData.transition i j).source) :
    Threefold.inclusion j (gluingData.transition i j x) = Threefold.inclusion i x :=
  ((gluingData.inclusion_eq_iff i j x (gluingData.transition i j x)).mpr ⟨hx, rfl⟩).symm

theorem inclusion_transition_eventually (i j : Index) (x : localPiece i)
    (hx : x ∈ (gluingData.transition i j).source) :
    (Threefold.inclusion j ∘ gluingData.transition i j) =ᶠ[𝓝 x] Threefold.inclusion i := by
  filter_upwards [(gluingData.transition i j).open_source.mem_nhds hx] with y hy
  exact inclusion_transition i j y hy

/-- Actual tangent derivatives satisfy the gluing chain rule throughout
the full overlap, not just on the central fibres. -/
theorem inclusion_mfderiv_gluing (i j : Index) (x : localPiece i)
    (hx : x ∈ (gluingData.transition i j).source) :
    mfderiv IF IF (Threefold.inclusion i) x =
      (mfderiv IF IF (Threefold.inclusion j) (gluingData.transition i j x)).comp
        (mfderiv IF IF (gluingData.transition i j) x) := by
  have he := (inclusion_transition_eventually i j x hx).mfderiv_eq (I := IF) (I' := IF)
  have hj := (Threefold.inclusion_holomorphic j).mdifferentiable (by simp)
  have ht := ((gluingData_transition_holomorphic i j).contMDiffAt
    ((gluingData.transition i j).open_source.mem_nhds hx)).mdifferentiableAt (by simp)
  rw [mfderiv_comp x (hj _) ht] at he
  exact he.symm

/-- The exact full-overlap gluing rule for arbitrary genuine top
covectors is pullback by the actual overlap derivative. -/
theorem topCovector_gluing (i j : Index) (x : localPiece i)
    (hx : x ∈ (gluingData.transition i j).source) (α : TopCovector) :
    α.compContinuousLinearMap (mfderiv IF IF (Threefold.inclusion i) x) =
      (α.compContinuousLinearMap
        (mfderiv IF IF (Threefold.inclusion j)
          (gluingData.transition i j x))).compContinuousLinearMap
          (mfderiv IF IF (gluingData.transition i j) x) := by
  rw [inclusion_mfderiv_gluing i j x hx]
  rfl

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical
