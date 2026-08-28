import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPullbackLocal
import Mathlib.Geometry.Manifold.Algebra.Structures

/-!
# Holomorphic canonical bundle maps over local biholomorphisms

Inverse pullback sends a canonical vector at `x` to the corresponding vector
at `f x`.  This map is holomorphic for the original total-space manifold
structures: its local fibre coefficient is the inverse of the actual
holomorphic, nonzero chart Jacobian of `f`.
-/

noncomputable section

open Bundle Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Canonical.Pullback

local notation "I" => modelWithCornersSelf ℂ Model
local notation "I₁" => modelWithCornersSelf ℂ ℂ

variable {M N : Type*}
  [TopologicalSpace M] [ChartedSpace Model M] [IsManifold I ω M]
  [TopologicalSpace N] [ChartedSpace Model N] [IsManifold I ω N]

/-- The actual fibrewise-linear canonical bundle map over `f`, inverse to
derivative pullback on each fibre. -/
def forwardMap {f : M → N} (hf : IsLocalDiffeomorph I I ω f)
    (p : (Atlas.core M).TotalSpace) : (Atlas.core N).TotalSpace :=
  ⟨f p.proj, (pullbackEquiv hf p.proj).symm p.2⟩

@[simp] theorem forwardMap_proj {f : M → N} (hf : IsLocalDiffeomorph I I ω f)
    (p : (Atlas.core M).TotalSpace) : (forwardMap hf p).proj = f p.proj := rfl

@[simp] theorem forwardMap_mk {f : M → N} (hf : IsLocalDiffeomorph I I ω f)
    (x : M) (v : (Atlas.core M).Fiber x) :
    forwardMap hf ⟨x, v⟩ = ⟨f x, (pullbackEquiv hf x).symm v⟩ := rfl

theorem forwardMap_localCoefficient {f : M → N} (hf : IsLocalDiffeomorph I I ω f)
    (i : atlas Model M) (j : atlas Model N) (p : (Atlas.core M).TotalSpace)
    (hi : p.proj ∈ i.val.source) (hj : f p.proj ∈ j.val.source) :
    ((Atlas.core N).localTriv j (forwardMap hf p)).2 =
      (chartDeterminant f i j p.proj)⁻¹ * ((Atlas.core M).localTriv i p).2 :=
  pullbackEquiv_symm_localCoefficient hf i j hi hj p.2

/-- In actual bundle trivializations this is the base map together with
multiplication by its inverse chart Jacobian. -/
theorem forwardMap_localTriv {f : M → N} (hf : IsLocalDiffeomorph I I ω f)
    (i : atlas Model M) (j : atlas Model N) (p : (Atlas.core M).TotalSpace)
    (hi : p.proj ∈ i.val.source) (hj : f p.proj ∈ j.val.source) :
    (Atlas.core N).localTriv j (forwardMap hf p) =
      (f p.proj, (chartDeterminant f i j p.proj)⁻¹ * ((Atlas.core M).localTriv i p).2) := by
  apply Prod.ext
  · rfl
  · exact forwardMap_localCoefficient hf i j p hi hj

/-- Inverse-pullback transport is holomorphic in the native canonical
bundle atlases, not only a fibrewise continuous linear equivalence. -/
theorem forwardMap_holomorphic {f : M → N} (hf : IsLocalDiffeomorph I I ω f) :
    ContMDiff ((I).prod I₁) ((I).prod I₁) ω (forwardMap hf) := by
  intro p
  let i : atlas Model M := achart Model p.proj
  let j : atlas Model N := achart Model (f p.proj)
  have hi : p.proj ∈ i.val.source := mem_chart_source Model p.proj
  have hj : f p.proj ∈ j.val.source := mem_chart_source Model (f p.proj)
  have hp : p ∈ ((Atlas.core M).localTriv i).source := hi
  have hfp : forwardMap hf p ∈ ((Atlas.core N).localTriv j).source := hj
  have hproj : ContMDiffAt ((I).prod I₁) I ω
      (Bundle.TotalSpace.proj : (Atlas.core M).TotalSpace → M) p :=
    Bundle.contMDiffAt_proj (Atlas.core M).Fiber
  apply (((Atlas.core N).localTriv j).contMDiffAt_iff hfp).mpr
  refine ⟨(hf.contMDiff.contMDiffAt).comp p hproj, ?_⟩
  have hU : i.val.source ∩ f ⁻¹' j.val.source ∈ 𝓝 p.proj :=
    (i.val.open_source.inter (j.val.open_source.preimage hf.contMDiff.continuous)).mem_nhds
      ⟨hi, hj⟩
  have hdet : ContMDiffAt I I₁ ω (chartDeterminant f i j) p.proj :=
    (chartDeterminant_holomorphicOn f i j hf.contMDiff).contMDiffAt hU
  have hinv : ContMDiffAt ((I).prod I₁) I₁ ω
      (fun q : (Atlas.core M).TotalSpace => (chartDeterminant f i j q.proj)⁻¹) p :=
    (hdet.inv₀ (chartDeterminant_ne_zero f i j hi hj (hf p.proj))).comp p hproj
  have hcoef : ContMDiffAt ((I).prod I₁) I₁ ω
      (fun q : (Atlas.core M).TotalSpace => ((Atlas.core M).localTriv i q).2) p :=
    (((Atlas.core M).localTriv i).contMDiffOn.contMDiffAt
      (((Atlas.core M).localTriv i).open_source.mem_nhds hp)).snd
  apply (hinv.mul hcoef).congr_of_eventuallyEq
  filter_upwards [hproj.continuousAt.preimage_mem_nhds hU] with q hq
  exact forwardMap_localCoefficient hf i j q hq.1 hq.2

theorem forwardMap_add {f : M → N} (hf : IsLocalDiffeomorph I I ω f)
    (x : M) (v w : (Atlas.core M).Fiber x) :
    id (α := (Atlas.core N).Fiber (f x)) (forwardMap hf ⟨x, v + w⟩).2 =
      id (α := (Atlas.core N).Fiber (f x)) (forwardMap hf ⟨x, v⟩).2 +
        id (α := (Atlas.core N).Fiber (f x)) (forwardMap hf ⟨x, w⟩).2 :=
  (pullbackEquiv hf x).symm.map_add v w

theorem forwardMap_smul {f : M → N} (hf : IsLocalDiffeomorph I I ω f)
    (x : M) (c : ℂ) (v : (Atlas.core M).Fiber x) :
    (forwardMap hf ⟨x, c • v⟩).2 = c • (forwardMap hf ⟨x, v⟩).2 :=
  (pullbackEquiv hf x).symm.map_smul c v

end Wikipedia.HopfProblem.TrianglePeriodFamily.Canonical.Pullback
