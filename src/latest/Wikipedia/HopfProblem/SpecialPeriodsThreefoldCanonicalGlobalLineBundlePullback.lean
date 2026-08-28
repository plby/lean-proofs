import Wikipedia.HopfProblem.HolomorphicCharacterBundleCore

/-!
# Pullback of the existing holomorphic cocycle line bundles

Pulling the open cover and its variable transition functions back along a
continuous map gives another `TransitionData`, hence another native line
bundle. For a holomorphic base map its transition functions are
holomorphic, and the natural map of native total spaces is holomorphic.
Its fibre maps and actual local-coordinate formula are explicit.
-/

noncomputable section

open Set Topology Bundle
open scoped ContDiff

namespace Wikipedia.HopfProblem.CanonicalGlobalLineBundle

open HolomorphicCharacterBundle

variable {M N ι : Type*} [TopologicalSpace M] [TopologicalSpace N]
    (A : TransitionData N ι) (f : M → N) (hf : Continuous f)

/-- The inverse-image open cover, with the original transition functions
composed with the base map. The core is the existing native bundle core. -/
def pullback : TransitionData M ι where
  baseSet i := f ⁻¹' A.baseSet i
  isOpen_baseSet i := (A.isOpen_baseSet i).preimage hf
  indexAt x := A.indexAt (f x)
  mem_baseSet_at x := A.mem_baseSet_at (f x)
  transition i j x := A.transition i j (f x)
  transition_self i x hx := A.transition_self i (f x) hx
  transition_comp i j k x hx := A.transition_comp i j k (f x) hx
  continuousOn_transition i j :=
    (A.continuousOn_transition i j).comp hf.continuousOn (fun _ hx => hx)

@[simp] theorem pullback_baseSet (i : ι) :
    (pullback A f hf).baseSet i = f ⁻¹' A.baseSet i := rfl

@[simp] theorem pullback_indexAt (x : M) :
    (pullback A f hf).indexAt x = A.indexAt (f x) := rfl

@[simp] theorem pullback_transition (i j : ι) (x : M) :
    (pullback A f hf).transition i j x = A.transition i j (f x) := rfl

theorem pullback_core_coordChange (i j : ι) (x : M) :
    (pullback A f hf).core.coordChange i j x = A.core.coordChange i j (f x) := rfl

/-- The pullback fibre is continuously and complex-linearly identified
with the original fibre over the image point. -/
def pullbackFiberEquiv (x : M) : (pullback A f hf).core.Fiber x ≃L[ℂ] A.core.Fiber (f x) :=
  ContinuousLinearEquiv.refl ℂ ℂ

@[simp] theorem pullbackFiberEquiv_apply (x : M) (v : (pullback A f hf).core.Fiber x) :
    pullbackFiberEquiv A f hf x v = id (α := ℂ) v := rfl

/-- The native total-space map covering the given base map. -/
def pullbackTotalMap (p : (pullback A f hf).core.TotalSpace) : A.core.TotalSpace :=
  ⟨f p.proj, pullbackFiberEquiv A f hf p.proj p.2⟩

@[simp] theorem pullbackTotalMap_proj (p : (pullback A f hf).core.TotalSpace) :
    (pullbackTotalMap A f hf p).proj = f p.proj := rfl

@[simp] theorem pullbackTotalMap_mk (x : M) (v : (pullback A f hf).core.Fiber x) :
    pullbackTotalMap A f hf ⟨x, v⟩ = ⟨f x, pullbackFiberEquiv A f hf x v⟩ := rfl

/-- In the actual pulled-back and original bundle charts, the total-space
map changes only the base coordinate and preserves the fibre coefficient. -/
theorem pullbackTotalMap_localTriv (i : ι) (p : (pullback A f hf).core.TotalSpace) :
    A.core.localTriv i (pullbackTotalMap A f hf p) =
      (f p.proj, ((pullback A f hf).core.localTriv i p).2) := rfl

@[simp] theorem pullback_id : pullback A id continuous_id = A := by
  cases A
  rfl

theorem pullback_comp {P : Type*} [TopologicalSpace P]
    (g : P → M) (hg : Continuous g) :
    pullback (pullback A f hf) g hg = pullback A (f ∘ g) (hf.comp hg) := rfl

variable {E H E' H' : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [TopologicalSpace H]
    [NormedAddCommGroup E'] [NormedSpace ℂ E'] [TopologicalSpace H']
    [ChartedSpace H M] [ChartedSpace H' N]
    (I : ModelWithCorners ℂ E H) (J : ModelWithCorners ℂ E' H')

local notation "I₁" => modelWithCornersSelf ℂ ℂ

theorem pullback_isHolomorphic [A.IsHolomorphic J] (hhol : ContMDiff I J ω f) :
    (pullback A f hf).IsHolomorphic I where
  contMDiffOn_transition i j :=
    (A.transition_holomorphic J i j).comp hhol.contMDiffOn (fun _ hx => hx)

theorem pullback_contMDiffVectorBundle [A.IsHolomorphic J] (hhol : ContMDiff I J ω f) :
    ContMDiffVectorBundle ω ℂ (pullback A f hf).core.Fiber I := by
  let : (pullback A f hf).IsHolomorphic I := pullback_isHolomorphic A f hf I J hhol
  infer_instance

/-- Holomorphicity of the total-space pullback map is checked in the two
original bundle atlases, using the exact common fibre coefficient. -/
theorem pullbackTotalMap_holomorphic [A.IsHolomorphic J] (hhol : ContMDiff I J ω f) :
    ContMDiff (I.prod I₁) (J.prod I₁) ω (pullbackTotalMap A f hf) := by
  let : (pullback A f hf).IsHolomorphic I := pullback_isHolomorphic A f hf I J hhol
  intro p
  let i := A.indexAt (f p.proj)
  have hp : pullbackTotalMap A f hf p ∈ (A.core.localTriv i).source :=
    A.mem_baseSet_at (f p.proj)
  apply ((A.core.localTriv i).contMDiffAt_iff hp).mpr
  refine ⟨(hhol p.proj).comp p (Bundle.contMDiffAt_proj (pullback A f hf).core.Fiber), ?_⟩
  let e := (pullback A f hf).core.localTriv i
  have hp' : p ∈ e.source := A.mem_baseSet_at (f p.proj)
  have he : ContMDiffAt (I.prod I₁) (I.prod I₁) ω e p :=
    e.contMDiffOn.contMDiffAt (e.open_source.mem_nhds hp')
  have hcoeff : (fun q : (pullback A f hf).core.TotalSpace =>
      (A.core.localTriv i (pullbackTotalMap A f hf q)).2) = fun q => (e q).2 := by
    funext q
    exact congrArg Prod.snd (pullbackTotalMap_localTriv A f hf i q)
  rw [hcoeff]
  exact he.snd

end Wikipedia.HopfProblem.CanonicalGlobalLineBundle
