import Wikipedia.HopfProblem.HolomorphicCharacterBundleCore
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection

/-!
# Gluing holomorphic sections of a character line bundle

Compatible holomorphic scalar functions in the bundle charts define an
actual holomorphic section. Conversely every section has compatible local
coefficients, and its holomorphicity is detected in those independently
constructed local trivializations.
-/

noncomputable section

open Set Topology Bundle
open scoped ContDiff

namespace Wikipedia.HopfProblem.HolomorphicCharacterBundle.TransitionData

variable {M ι : Type*} [TopologicalSpace M] (A : TransitionData M ι)

def IsCompatible (f : ι → M → ℂ) : Prop :=
  ∀ i j x, x ∈ A.baseSet i ∩ A.baseSet j →
    (A.transition i j x : ℂ) * f i x = f j x

/-- Local coefficients are read in the bundle's actual linear trivializations. -/
def localCoefficient (s : ∀ x, A.core.Fiber x) (i : ι) (x : M) : ℂ :=
  (A.core.localTriv i ⟨x, s x⟩).2

@[simp] theorem localCoefficient_eq (s : ∀ x, A.core.Fiber x) (i : ι) (x : M) :
    A.localCoefficient s i x =
      (A.transition (A.indexAt x) i x : ℂ) * id (α := ℂ) (s x) := rfl

theorem localCoefficient_indexAt (s : ∀ x, A.core.Fiber x) (x : M) :
    A.localCoefficient s (A.indexAt x) x = id (α := ℂ) (s x) := by
  rw [localCoefficient_eq, A.transition_self _ _ (A.mem_baseSet_at x)]
  simp

theorem localCoefficient_compatible (s : ∀ x, A.core.Fiber x) :
    A.IsCompatible (A.localCoefficient s) := by
  intro i j x hx
  have hc := congrArg (fun u : ℂˣ => (u : ℂ))
    (A.transition_comp (A.indexAt x) i j x ⟨⟨A.mem_baseSet_at x, hx.1⟩, hx.2⟩)
  change (A.transition i j x : ℂ) * (A.transition (A.indexAt x) i x : ℂ) =
    (A.transition (A.indexAt x) j x : ℂ) at hc
  simp only [localCoefficient_eq]
  rw [← mul_assoc, hc]

theorem localCoefficient_ne_zero (s : ∀ x, A.core.Fiber x) (hs : ∀ x, s x ≠ 0)
    (i : ι) (x : M) : A.localCoefficient s i x ≠ 0 :=
  mul_ne_zero (A.transition_ne_zero _ _ _) (hs x)

/-- The selected local coefficient describes the value in the selected bundle fibre. -/
def sectionFromLocal (f : ι → M → ℂ) (x : M) : A.core.Fiber x := f (A.indexAt x) x

theorem localCoefficient_sectionFromLocal (f : ι → M → ℂ) (hf : A.IsCompatible f)
    (i : ι) {x : M} (hx : x ∈ A.baseSet i) :
    A.localCoefficient (A.sectionFromLocal f) i x = f i x :=
  hf (A.indexAt x) i x ⟨A.mem_baseSet_at x, hx⟩

theorem sectionFromLocal_localCoefficient (s : ∀ x, A.core.Fiber x) :
    A.sectionFromLocal (A.localCoefficient s) = s := by
  funext x
  exact A.localCoefficient_indexAt s x

theorem sectionFromLocal_ne_zero (f : ι → M → ℂ)
    (hf : ∀ i x, x ∈ A.baseSet i → f i x ≠ 0) (x : M) :
    A.sectionFromLocal f x ≠ 0 := hf (A.indexAt x) x (A.mem_baseSet_at x)

theorem section_eq_of_localCoefficient_eq (s t : ∀ x, A.core.Fiber x)
    (h : ∀ i x, x ∈ A.baseSet i → A.localCoefficient s i x = A.localCoefficient t i x) :
    s = t := by
  funext x
  have hx := h (A.indexAt x) x (A.mem_baseSet_at x)
  rw [localCoefficient_indexAt, localCoefficient_indexAt] at hx
  exact hx

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [TopologicalSpace H]
    [ChartedSpace H M] (I : ModelWithCorners ℂ E H) [A.IsHolomorphic I]

local notation "I₁" => modelWithCornersSelf ℂ ℂ

theorem localCoefficient_holomorphic (s : ∀ x, A.core.Fiber x)
    (hs : ContMDiff I (I.prod I₁) ω (fun x => (⟨x, s x⟩ : A.core.TotalSpace))) (i : ι) :
    ContMDiffOn I I₁ ω (A.localCoefficient s i) (A.baseSet i) :=
  (A.core.localTriv i).contMDiffOn_section_baseSet_iff.mp hs.contMDiffOn

omit [A.IsHolomorphic I] in
theorem sectionFromLocal_holomorphic (f : ι → M → ℂ) (hf : A.IsCompatible f)
    (hhol : ∀ i, ContMDiffOn I I₁ ω (f i) (A.baseSet i)) :
    ContMDiff I (I.prod I₁) ω (fun x => (⟨x, A.sectionFromLocal f x⟩ : A.core.TotalSpace)) := by
  intro x
  rw [Bundle.contMDiffAt_section]
  have hnhds : A.baseSet (A.indexAt x) ∈ 𝓝 x :=
    (A.isOpen_baseSet (A.indexAt x)).mem_nhds (A.mem_baseSet_at x)
  have h := (hhol (A.indexAt x)).contMDiffAt hnhds
  apply h.congr_of_eventuallyEq
  filter_upwards [hnhds] with y hy
  exact A.localCoefficient_sectionFromLocal f hf (A.indexAt x) hy

def holomorphicSectionFromLocal (f : ι → M → ℂ) (hf : A.IsCompatible f)
    (hhol : ∀ i, ContMDiffOn I I₁ ω (f i) (A.baseSet i)) :
    ContMDiffSection I ℂ ω A.core.Fiber where
  toFun := A.sectionFromLocal f
  contMDiff_toFun := A.sectionFromLocal_holomorphic I f hf hhol

omit [A.IsHolomorphic I] in
@[simp] theorem holomorphicSectionFromLocal_apply (f : ι → M → ℂ) (hf : A.IsCompatible f)
    (hhol : ∀ i, ContMDiffOn I I₁ ω (f i) (A.baseSet i)) (x : M) :
    A.holomorphicSectionFromLocal I f hf hhol x = f (A.indexAt x) x := rfl

theorem section_holomorphic_iff_localCoefficients (s : ∀ x, A.core.Fiber x) :
    ContMDiff I (I.prod I₁) ω (fun x => (⟨x, s x⟩ : A.core.TotalSpace)) ↔
      ∀ i, ContMDiffOn I I₁ ω (A.localCoefficient s i) (A.baseSet i) := by
  constructor
  · exact A.localCoefficient_holomorphic I s
  · intro hs
    have h := A.sectionFromLocal_holomorphic I (A.localCoefficient s)
      (A.localCoefficient_compatible s) hs
    simpa only [sectionFromLocal_localCoefficient] using h

end Wikipedia.HopfProblem.HolomorphicCharacterBundle.TransitionData
