import Wikipedia.HopfProblem.HolomorphicMeromorphicPolarBundleCore
import Wikipedia.HopfProblem.HolomorphicMeromorphicPolarBundleSections

/-!
# Holomorphic scalar cocycles and their native line-bundle sections

The scalar cocycle constructs the bundle, including its topology and atlas.
Compatible holomorphic scalar functions then glue to a genuine native
`ContMDiffSection`. The local coordinate and zero-locus identities below
retain the exact functions supplied on the cover.
-/

open Set Topology Bundle
open scoped ContDiff

namespace Wikipedia.HopfProblem.HolomorphicMeromorphic.PolarBundle.ScalarCocycle

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [TopologicalSpace H]
  {I : ModelWithCorners ℂ E H} {M ι : Type*}
  [TopologicalSpace M] [ChartedSpace H M]
  (A : ScalarCocycle I M ι) (f : ι → M → ℂ)

local notation "I₁" => modelWithCornersSelf ℂ ℂ

/-- Over a complex manifold, the native total-space atlas is itself analytic. -/
theorem totalSpace_isManifold [IsManifold I ω M] :
    IsManifold (I.prod I₁) ω A.core.TotalSpace := inferInstance

/-- A genuine native holomorphic section of the line bundle constructed from
the cocycle, with the supplied compatible local scalar coordinates. -/
noncomputable def sectionOfCompatible
    (hhol : ∀ i, ContMDiffOn I I₁ ω (f i) (A.baseSet i))
    (hf : ∀ i j x, x ∈ A.baseSet i ∩ A.baseSet j →
      A.transition i j x * f i x = f j x) :
    ContMDiffSection I ℂ ω A.core.Fiber :=
  gluedSection A.core f I hhol hf

@[simp] theorem sectionOfCompatible_apply
    (hhol : ∀ i, ContMDiffOn I I₁ ω (f i) (A.baseSet i))
    (hf : ∀ i j x, x ∈ A.baseSet i ∩ A.baseSet j →
      A.transition i j x * f i x = f j x) (x : M) :
    A.sectionOfCompatible f hhol hf x = f (A.indexAt x) x := rfl

/-- The full native-chart expression of the section on each cover member. -/
theorem sectionOfCompatible_localTriv
    (hhol : ∀ i, ContMDiffOn I I₁ ω (f i) (A.baseSet i))
    (hf : ∀ i j x, x ∈ A.baseSet i ∩ A.baseSet j →
      A.transition i j x * f i x = f j x)
    (i : ι) {x : M} (hx : x ∈ A.baseSet i) :
    A.core.localTriv i ⟨x, A.sectionOfCompatible f hhol hf x⟩ = (x, f i x) :=
  sectionValue_localTriv_eq A.core f hf i hx

/-- The section's zero locus is exactly the local scalar zero locus. -/
theorem sectionOfCompatible_eq_zero_iff
    (hhol : ∀ i, ContMDiffOn I I₁ ω (f i) (A.baseSet i))
    (hf : ∀ i j x, x ∈ A.baseSet i ∩ A.baseSet j →
      A.transition i j x * f i x = f j x)
    (i : ι) {x : M} (hx : x ∈ A.baseSet i) :
    A.sectionOfCompatible f hhol hf x = 0 ↔ f i x = 0 :=
  sectionValue_eq_zero_iff A.core f hf i hx

theorem sectionOfCompatible_ne_zero_iff
    (hhol : ∀ i, ContMDiffOn I I₁ ω (f i) (A.baseSet i))
    (hf : ∀ i j x, x ∈ A.baseSet i ∩ A.baseSet j →
      A.transition i j x * f i x = f j x)
    (i : ι) {x : M} (hx : x ∈ A.baseSet i) :
    A.sectionOfCompatible f hhol hf x ≠ 0 ↔ f i x ≠ 0 :=
  not_congr (A.sectionOfCompatible_eq_zero_iff f hhol hf i hx)

/-- No other native holomorphic section has these local coordinates. -/
theorem sectionOfCompatible_unique
    (hhol : ∀ i, ContMDiffOn I I₁ ω (f i) (A.baseSet i))
    (hf : ∀ i j x, x ∈ A.baseSet i ∩ A.baseSet j →
      A.transition i j x * f i x = f j x)
    (s : ContMDiffSection I ℂ ω A.core.Fiber)
    (hs : ∀ i x, x ∈ A.baseSet i → (A.core.localTriv i ⟨x, s x⟩).2 = f i x) :
    s = A.sectionOfCompatible f hhol hf :=
  gluedSection_unique A.core f I hhol hf s hs

/-- A cover-compatible family determines a unique native holomorphic section
of the line bundle built from its transition cocycle. -/
theorem existsUnique_section
    (hhol : ∀ i, ContMDiffOn I I₁ ω (f i) (A.baseSet i))
    (hf : ∀ i j x, x ∈ A.baseSet i ∩ A.baseSet j →
      A.transition i j x * f i x = f j x) :
    ∃! s : ContMDiffSection I ℂ ω A.core.Fiber,
      ∀ i x, x ∈ A.baseSet i → (A.core.localTriv i ⟨x, s x⟩).2 = f i x := by
  refine ⟨A.sectionOfCompatible f hhol hf, ?_, ?_⟩
  · intro i x hx
    exact congrArg Prod.snd (A.sectionOfCompatible_localTriv f hhol hf i hx)
  · intro s hs
    exact A.sectionOfCompatible_unique f hhol hf s hs

end Wikipedia.HopfProblem.HolomorphicMeromorphic.PolarBundle.ScalarCocycle
