import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Analysis.Complex.Basic

/-!
# Gluing holomorphic sections of a complex line bundle

Compatible holomorphic scalar functions in the charts of an actual
`VectorBundleCore` define a genuine `ContMDiffSection` of the bundle it
constructs.  The coordinate formulas hold on every chart of the given
cover, and determine the section uniquely.
-/

noncomputable section

open Set Topology Bundle
open scoped ContDiff

namespace Wikipedia.HopfProblem.HolomorphicMeromorphic.PolarBundle

variable {M ι : Type*} [TopologicalSpace M]
    (Z : VectorBundleCore ℂ M ℂ ι) (f : ι → M → ℂ)

/-- The fibre value selected from compatible local scalar coordinates. -/
def sectionValue (x : M) : Z.Fiber x := f (Z.indexAt x) x

/-- The glued fibre value has exactly the prescribed coordinate in every chart. -/
theorem sectionValue_localTriv
    (hf : ∀ i j x, x ∈ Z.baseSet i ∩ Z.baseSet j →
      Z.coordChange i j x (f i x) = f j x)
    (i : ι) {x : M} (hx : x ∈ Z.baseSet i) :
    (Z.localTriv i ⟨x, sectionValue Z f x⟩).2 = f i x := by
  exact hf (Z.indexAt x) i x ⟨Z.mem_baseSet_at x, hx⟩

/-- The full chart expression of the glued section, including the base point. -/
theorem sectionValue_localTriv_eq
    (hf : ∀ i j x, x ∈ Z.baseSet i ∩ Z.baseSet j →
      Z.coordChange i j x (f i x) = f j x)
    (i : ι) {x : M} (hx : x ∈ Z.baseSet i) :
    Z.localTriv i ⟨x, sectionValue Z f x⟩ = (x, f i x) := by
  exact Prod.ext rfl (sectionValue_localTriv Z f hf i hx)

/-- Vanishing of the section is equivalent to vanishing of its scalar coordinate. -/
theorem sectionValue_eq_zero_iff
    (hf : ∀ i j x, x ∈ Z.baseSet i ∩ Z.baseSet j →
      Z.coordChange i j x (f i x) = f j x)
    (i : ι) {x : M} (hx : x ∈ Z.baseSet i) :
    sectionValue Z f x = 0 ↔ f i x = 0 := by
  constructor
  · intro h
    have h' : f (Z.indexAt x) x = 0 := h
    rw [← hf (Z.indexAt x) i x ⟨Z.mem_baseSet_at x, hx⟩, h', map_zero]
  · intro h
    change f (Z.indexAt x) x = 0
    rw [← hf i (Z.indexAt x) x ⟨hx, Z.mem_baseSet_at x⟩, h, map_zero]

/-- Nonvanishing can likewise be checked in any local chart. -/
theorem sectionValue_ne_zero_iff
    (hf : ∀ i j x, x ∈ Z.baseSet i ∩ Z.baseSet j →
      Z.coordChange i j x (f i x) = f j x)
    (i : ι) {x : M} (hx : x ∈ Z.baseSet i) :
    sectionValue Z f x ≠ 0 ↔ f i x ≠ 0 :=
  not_congr (sectionValue_eq_zero_iff Z f hf i hx)

/-- Local coordinates uniquely determine the underlying section. -/
theorem sectionValue_unique (s : ∀ x, Z.Fiber x)
    (hs : ∀ i x, x ∈ Z.baseSet i → (Z.localTriv i ⟨x, s x⟩).2 = f i x) :
    s = sectionValue Z f := by
  funext x
  have h := hs (Z.indexAt x) x (Z.mem_baseSet_at x)
  change Z.coordChange (Z.indexAt x) (Z.indexAt x) x (id (α := ℂ) (s x)) =
    f (Z.indexAt x) x at h
  rw [Z.coordChange_self _ x (Z.mem_baseSet_at x)] at h
  exact h

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace H] [ChartedSpace H M] (I : ModelWithCorners ℂ E H)

local notation "I₁" => modelWithCornersSelf ℂ ℂ

/-- The glued section is holomorphic for the native bundle manifold structure. -/
theorem sectionValue_holomorphic
    (hhol : ∀ i, ContMDiffOn I I₁ ω (f i) (Z.baseSet i))
    (hf : ∀ i j x, x ∈ Z.baseSet i ∩ Z.baseSet j →
      Z.coordChange i j x (f i x) = f j x) :
    ContMDiff I (I.prod I₁) ω
      (fun x ↦ (⟨x, sectionValue Z f x⟩ : Z.TotalSpace)) := by
  intro x
  apply Bundle.contMDiffAt_section x |>.mpr
  have h := (hhol (Z.indexAt x)).contMDiffAt
    ((Z.isOpen_baseSet (Z.indexAt x)).mem_nhds (Z.mem_baseSet_at x))
  apply h.congr_of_eventuallyEq
  filter_upwards [(Z.isOpen_baseSet (Z.indexAt x)).mem_nhds (Z.mem_baseSet_at x)] with y hy
  exact sectionValue_localTriv Z f hf (Z.indexAt x) hy

/-- The genuine bundled holomorphic section obtained by gluing local coordinates. -/
def gluedSection
    (hhol : ∀ i, ContMDiffOn I I₁ ω (f i) (Z.baseSet i))
    (hf : ∀ i j x, x ∈ Z.baseSet i ∩ Z.baseSet j →
      Z.coordChange i j x (f i x) = f j x) :
    ContMDiffSection I ℂ ω Z.Fiber where
  toFun := sectionValue Z f
  contMDiff_toFun := sectionValue_holomorphic Z f I hhol hf

@[simp] theorem gluedSection_apply
    (hhol : ∀ i, ContMDiffOn I I₁ ω (f i) (Z.baseSet i))
    (hf : ∀ i j x, x ∈ Z.baseSet i ∩ Z.baseSet j →
      Z.coordChange i j x (f i x) = f j x) (x : M) :
    gluedSection Z f I hhol hf x = sectionValue Z f x := rfl

/-- The bundled section retains the exact prescribed local coordinates. -/
theorem gluedSection_localTriv
    (hhol : ∀ i, ContMDiffOn I I₁ ω (f i) (Z.baseSet i))
    (hf : ∀ i j x, x ∈ Z.baseSet i ∩ Z.baseSet j →
      Z.coordChange i j x (f i x) = f j x)
    (i : ι) {x : M} (hx : x ∈ Z.baseSet i) :
    (Z.localTriv i ⟨x, gluedSection Z f I hhol hf x⟩).2 = f i x :=
  sectionValue_localTriv Z f hf i hx

/-- A holomorphic section with these local coordinates is the glued section. -/
theorem gluedSection_unique
    (hhol : ∀ i, ContMDiffOn I I₁ ω (f i) (Z.baseSet i))
    (hf : ∀ i j x, x ∈ Z.baseSet i ∩ Z.baseSet j →
      Z.coordChange i j x (f i x) = f j x)
    (s : ContMDiffSection I ℂ ω Z.Fiber)
    (hs : ∀ i x, x ∈ Z.baseSet i → (Z.localTriv i ⟨x, s x⟩).2 = f i x) :
    s = gluedSection Z f I hhol hf := by
  exact ContMDiffSection.coe_injective (sectionValue_unique Z f s hs)

end Wikipedia.HopfProblem.HolomorphicMeromorphic.PolarBundle
