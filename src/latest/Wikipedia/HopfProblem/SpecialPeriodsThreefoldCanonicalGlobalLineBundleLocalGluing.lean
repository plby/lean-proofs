import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalLineBundleRefinementGauge

/-!
# Gluing cross-cover gauges from an actual open coarse cover

Holomorphic gauge units given on an open coarse cover assemble to a
global `CrossGauge` when their local values agree and their cocycle
identities hold on the appropriate overlaps. Holomorphicity of the
selected global value follows from local eventual equality; no
continuity of the chart selector is assumed. The resulting bundle
isomorphism is the existing `CrossGauge.diffeomorph`.
-/

noncomputable section

open Bundle Set Topology TopologicalSpace
open scoped ContDiff

namespace Wikipedia.HopfProblem.CanonicalGlobalLineBundle

open HolomorphicCharacterBundle

variable {M ι η : Type*} [TopologicalSpace M]
    {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [TopologicalSpace H]
    [ChartedSpace H M] (I : ModelWithCorners ℂ E H)

local notation "I₁" => modelWithCornersSelf ℂ ℂ

/-- Local gauge units on a genuine open coarse cover. Agreement is only
required where both coarse patches and the fixed original chart pair
are valid. Compatibility is the original cross-gauge identity within
each coarse patch. -/
structure LocalCrossGauge (A : TransitionData M ι) (B : TransitionData M η)
    (κ : Type*) where
  cover : κ → Opens M
  indexAt : M → κ
  mem_cover : ∀ x, x ∈ cover (indexAt x)
  value : κ → (ι × η) → M → ℂˣ
  holomorphicOn : ∀ k i,
    ContMDiffOn I I₁ ω (fun x => (value k i x : ℂ))
      ((A.baseSet i.1 ∩ B.baseSet i.2) ∩ cover k)
  agreement : ∀ k l i x, x ∈ A.baseSet i.1 ∩ B.baseSet i.2 →
    x ∈ cover k → x ∈ cover l → value k i x = value l i x
  compatible : ∀ k (i j : ι × η) x,
    x ∈ (A.baseSet i.1 ∩ B.baseSet i.2) ∩ (A.baseSet j.1 ∩ B.baseSet j.2) →
    x ∈ cover k →
      B.transition i.2 j.2 x * value k i x = value k j x * A.transition i.1 j.1 x

namespace LocalCrossGauge

variable {I} {κ : Type*} {A : TransitionData M ι} {B : TransitionData M η}
    (G : LocalCrossGauge I A B κ)

/-- Choose the value on a coarse patch containing the base point. -/
def globalValue (i : ι × η) (x : M) : ℂˣ := G.value (G.indexAt x) i x

/-- On any valid coarse patch, the selected value is its prescribed local value. -/
theorem globalValue_eq_of_mem (k : κ) (i : ι × η) {x : M}
    (hi : x ∈ A.baseSet i.1 ∩ B.baseSet i.2) (hk : x ∈ G.cover k) :
    G.globalValue i x = G.value k i x :=
  G.agreement (G.indexAt x) k i x hi (G.mem_cover x) hk

/-- The selected value is holomorphic on each original chart-pair
intersection because it agrees locally with one fixed holomorphic value. -/
theorem globalValue_holomorphicOn (i : ι × η) :
    ContMDiffOn I I₁ ω (fun x => (G.globalValue i x : ℂ))
      (A.baseSet i.1 ∩ B.baseSet i.2) := by
  intro x hx
  let k := G.indexAt x
  have hU : ((A.baseSet i.1 ∩ B.baseSet i.2) ∩ (G.cover k : Set M)) ∈ 𝓝 x :=
    (((A.isOpen_baseSet i.1).inter (B.isOpen_baseSet i.2)).inter
      (G.cover k).isOpen).mem_nhds ⟨hx, G.mem_cover x⟩
  have hloc := (G.holomorphicOn k i).contMDiffAt hU
  apply (hloc.congr_of_eventuallyEq ?_).contMDiffWithinAt
  filter_upwards [hU] with y hy
  exact congrArg (fun u : ℂˣ => (u : ℂ)) (G.globalValue_eq_of_mem k i hy.1 hy.2)

/-- The local units assemble to the existing global cross-cover gauge. -/
def toCrossGauge : CrossGauge I A B where
  value := G.globalValue
  compatible i j x hx := G.compatible (G.indexAt x) i j x hx (G.mem_cover x)
  holomorphicOn := G.globalValue_holomorphicOn

@[simp] theorem toCrossGauge_value (i : ι × η) (x : M) :
    G.toCrossGauge.value i x = G.value (G.indexAt x) i x := rfl

theorem toCrossGauge_value_of_mem (k : κ) (i : ι × η) {x : M}
    (hi : x ∈ A.baseSet i.1 ∩ B.baseSet i.2) (hk : x ∈ G.cover k) :
    G.toCrossGauge.value i x = G.value k i x := G.globalValue_eq_of_mem k i hi hk

variable [A.IsHolomorphic I] [B.IsHolomorphic I]

/-- The existing native bundle biholomorphism has the prescribed local
coefficient on every coarse patch. No new isomorphism is assumed or defined. -/
theorem toCrossGauge_diffeomorph_localCoefficient (k : κ) (i : ι) (j : η)
    (p : A.core.TotalSpace) (hp : p.proj ∈ A.baseSet i ∩ B.baseSet j)
    (hk : p.proj ∈ G.cover k) :
    (B.core.localTriv j (G.toCrossGauge.diffeomorph p)).2 =
      (G.value k (i, j) p.proj : ℂ) * (A.core.localTriv i p).2 := by
  calc
    _ = (G.toCrossGauge.value (i, j) p.proj : ℂ) * (A.core.localTriv i p).2 :=
      G.toCrossGauge.diffeomorph_localCoefficient i j p hp
    _ = _ := congrArg (fun u : ℂˣ => (u : ℂ) * (A.core.localTriv i p).2)
      (G.toCrossGauge_value_of_mem k (i, j) hp hk)

/-- The inverse biholomorphism has the reciprocal of the same local
coefficient on every coarse patch. -/
theorem toCrossGauge_diffeomorph_symm_localCoefficient (k : κ) (i : ι) (j : η)
    (p : B.core.TotalSpace) (hp : p.proj ∈ A.baseSet i ∩ B.baseSet j)
    (hk : p.proj ∈ G.cover k) :
    (A.core.localTriv i (G.toCrossGauge.diffeomorph.symm p)).2 =
      (G.value k (i, j) p.proj : ℂ)⁻¹ * (B.core.localTriv j p).2 := by
  calc
    _ = (G.toCrossGauge.value (i, j) p.proj : ℂ)⁻¹ * (B.core.localTriv j p).2 :=
      G.toCrossGauge.diffeomorph_symm_localCoefficient i j p hp
    _ = _ := congrArg (fun u : ℂˣ => (u : ℂ)⁻¹ * (B.core.localTriv j p).2)
      (G.toCrossGauge_value_of_mem k (i, j) hp hk)

end LocalCrossGauge

end Wikipedia.HopfProblem.CanonicalGlobalLineBundle
