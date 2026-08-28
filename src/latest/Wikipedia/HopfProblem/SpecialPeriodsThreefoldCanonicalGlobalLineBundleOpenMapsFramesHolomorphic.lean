import Wikipedia.HopfProblem.HolomorphicCharacterBundleCoreSections
import Mathlib.Geometry.Manifold.Algebra.Structures

/-!
# Holomorphicity of native bundle maps from local frame ratios

Two actual holomorphic nonvanishing frames determine holomorphic local
ratios in the original bundle charts. A native scalar map with those
local expressions is holomorphic over the given open set. No continuity
of its preferred-coordinate multiplier is assumed: preferred charts
may change discontinuously while the actual bundle map is holomorphic.
-/

noncomputable section

open Bundle Set Topology TopologicalSpace
open scoped ContDiff

namespace Wikipedia.HopfProblem.CanonicalGlobalLineBundle.OpenMaps

open HolomorphicCharacterBundle

variable {M ι η : Type*} [TopologicalSpace M]
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [TopologicalSpace H]
  [ChartedSpace H M] (I : ModelWithCorners ℂ E H)

local notation "I₁" => modelWithCornersSelf ℂ ℂ

/-- Actual frame holomorphicity gives holomorphicity of each valid
native local coefficient at every point of the chosen open set. -/
theorem localCoefficient_contMDiffAt_of_frame
    (A : TransitionData M ι) [A.IsHolomorphic I]
    (U : Opens M) (s : ∀ x, A.core.Fiber x)
    (hs : ContMDiffOn I (I.prod I₁) ω
      (fun x => (⟨x, s x⟩ : A.core.TotalSpace)) (U : Set M))
    (i : ι) {x : M} (hx : x ∈ U) (hi : x ∈ A.baseSet i) :
    ContMDiffAt I I₁ ω (A.localCoefficient s i) x :=
  (((A.core.localTriv i).contMDiffAt_iff
    (f := fun y => (⟨y, s y⟩ : A.core.TotalSpace))
    (show (⟨x, s x⟩ : A.core.TotalSpace) ∈ (A.core.localTriv i).source from hi)).mp
      (hs.contMDiffAt (U.isOpen.mem_nhds hx))).2

/-- Nonvanishing of the actual fibre vector implies nonvanishing of
its native scalar coefficient. -/
theorem localCoefficient_ne_zero_of_frame
    (A : TransitionData M ι) (s : ∀ x, A.core.Fiber x)
    (i : ι) {x : M} (hs : s x ≠ 0) : A.localCoefficient s i x ≠ 0 :=
  mul_ne_zero (A.transition_ne_zero _ _ _) hs

/-- Native local frame-ratio expressions imply holomorphicity of the
actual scalar map on the total-space preimage of the open set. -/
theorem nativeScalarMap_holomorphicOn_of_frame_ratios
    (A : TransitionData M ι) (B : TransitionData M η)
    [A.IsHolomorphic I] [B.IsHolomorphic I]
    (U : Opens M) (h : M → ℂˣ)
    (s : ∀ x, A.core.Fiber x) (t : ∀ x, B.core.Fiber x)
    (hs : ∀ x ∈ U, s x ≠ 0)
    (hsHol : ContMDiffOn I (I.prod I₁) ω
      (fun x => (⟨x, s x⟩ : A.core.TotalSpace)) (U : Set M))
    (htHol : ContMDiffOn I (I.prod I₁) ω
      (fun x => (⟨x, t x⟩ : B.core.TotalSpace)) (U : Set M))
    (hcoef : ∀ (i : ι) (j : η) (p : A.core.TotalSpace), p.proj ∈ U →
      (B.core.localTriv j ⟨p.proj, (h p.proj : ℂ) * id (α := ℂ) p.2⟩).2 =
        (B.localCoefficient t j p.proj / A.localCoefficient s i p.proj) *
          (A.core.localTriv i p).2) :
    ContMDiffOn (I.prod I₁) (I.prod I₁) ω
      (fun p : A.core.TotalSpace =>
        (⟨p.proj, (h p.proj : ℂ) * id (α := ℂ) p.2⟩ : B.core.TotalSpace))
      ((fun p : A.core.TotalSpace => p.proj) ⁻¹' (U : Set M)) := by
  intro p hp
  have hpU : p.proj ∈ U := hp
  have hAt : ContMDiffAt (I.prod I₁) (I.prod I₁) ω
      (fun q : A.core.TotalSpace =>
        (⟨q.proj, (h q.proj : ℂ) * id (α := ℂ) q.2⟩ : B.core.TotalSpace)) p := by
    let i := A.indexAt p.proj
    let j := B.indexAt p.proj
    have hpi : p.proj ∈ A.baseSet i := A.mem_baseSet_at p.proj
    have hpj : p.proj ∈ B.baseSet j := B.mem_baseSet_at p.proj
    apply ((B.core.localTriv j).contMDiffAt_iff
      (f := fun q : A.core.TotalSpace =>
        (⟨q.proj, (h q.proj : ℂ) * id (α := ℂ) q.2⟩ : B.core.TotalSpace))
      (show (⟨p.proj, (h p.proj : ℂ) * id (α := ℂ) p.2⟩ : B.core.TotalSpace) ∈
        (B.core.localTriv j).source from hpj)).mpr
    have hπ : ContMDiffAt (I.prod I₁) I ω
        (fun q : A.core.TotalSpace => q.proj) p := Bundle.contMDiffAt_proj A.core.Fiber
    refine ⟨hπ, ?_⟩
    have hsc := localCoefficient_contMDiffAt_of_frame I A U s hsHol i hpU hpi
    have htc := localCoefficient_contMDiffAt_of_frame I B U t htHol j hpU hpj
    have hsc0 := localCoefficient_ne_zero_of_frame A s i (hs p.proj hpU)
    have hratio : ContMDiffAt I I₁ ω
        (fun x => B.localCoefficient t j x / A.localCoefficient s i x) p.proj :=
      htc.div₀ hsc hsc0
    have he : ContMDiffAt (I.prod I₁) (I.prod I₁) ω (A.core.localTriv i) p :=
      (A.core.localTriv i).contMDiffOn.contMDiffAt
        ((A.core.localTriv i).open_source.mem_nhds hpi)
    apply ((hratio.comp p hπ).mul he.snd).congr_of_eventuallyEq
    filter_upwards [hπ.continuousAt (U.isOpen.mem_nhds hpU)] with q hq
    exact hcoef i j q hq
  exact hAt.contMDiffWithinAt

end Wikipedia.HopfProblem.CanonicalGlobalLineBundle.OpenMaps
