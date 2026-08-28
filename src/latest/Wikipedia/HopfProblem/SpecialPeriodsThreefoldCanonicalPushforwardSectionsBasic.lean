import Wikipedia.HopfProblem.HolomorphicFunctionSheafBasic
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection

/-!
# Holomorphic sections in the original native line-bundle fibres

Sections on an open set take values in the fibres of a given original
`VectorBundleCore`. Their holomorphicity is that of the resulting map
to that core's original total space. Restriction is literal restriction
of the dependent fibre-valued function, with no replacement cocycle or
change of total-space atlas.
-/

noncomputable section

open Bundle Set Topology TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.NativeBundleSections

variable {M : Type} {ι : Type*} [TopologicalSpace M]
  (C : VectorBundleCore ℂ M ℂ ι)
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] [ChartedSpace H M] (I : ModelWithCorners ℂ E H)

local notation "I₁" => modelWithCornersSelf ℂ ℂ

/-- A section valued in the original fibres and holomorphic into the
original native bundle total space. -/
structure Section (U : Opens M) where
  toFun : ∀ x : U, C.Fiber (x : M)
  contMDiff_toFun : ContMDiff I (I.prod I₁) ω
    (fun x : U => (⟨(x : M), toFun x⟩ : C.TotalSpace))

instance localTriv_memTrivializationAtlas (i : ι) :
    MemTrivializationAtlas (C.localTriv i) where
  out := ⟨i, rfl⟩

namespace Section

instance {U : Opens M} : CoeFun (Section C I U)
    (fun _ => ∀ x : U, C.Fiber (x : M)) where
  coe := Section.toFun

@[ext] theorem ext {U : Opens M} {s t : Section C I U}
    (h : ∀ x, s x = t x) : s = t := by
  cases s
  cases t
  congr
  exact funext h

theorem coe_injective (U : Opens M) :
    Function.Injective (fun s : Section C I U => s.toFun) := by
  intro s t h
  exact Section.ext C I (congrFun h)

/-- The actual map to the original native total space. -/
def totalSpace {U : Opens M} (s : Section C I U) (x : U) : C.TotalSpace :=
  ⟨(x : M), s x⟩

@[simp] theorem totalSpace_proj {U : Opens M} (s : Section C I U) (x : U) :
    (s.totalSpace C I x).proj = (x : M) := rfl

theorem holomorphic {U : Opens M} (s : Section C I U) :
    ContMDiff I (I.prod I₁) ω (s.totalSpace C I) := s.contMDiff_toFun

/-- Literal restriction to an original smaller base open set. -/
def restrict {U V : Opens M} (h : U ≤ V) (s : Section C I V) : Section C I U where
  toFun x := s ⟨(x : M), h x.property⟩
  contMDiff_toFun := s.contMDiff_toFun.comp (contMDiff_inclusion h)

@[simp] theorem restrict_apply {U V : Opens M} (h : U ≤ V)
    (s : Section C I V) (x : U) :
    restrict C I h s x = s ⟨(x : M), h x.property⟩ := rfl

@[simp] theorem restrict_refl {U : Opens M} (s : Section C I U) :
    restrict C I le_rfl s = s := by
  ext x
  rfl

@[simp] theorem restrict_restrict {U V W : Opens M} (hUV : U ≤ V) (hVW : V ≤ W)
    (s : Section C I W) :
    restrict C I hUV (restrict C I hVW s) = restrict C I (hUV.trans hVW) s := by
  ext x
  rfl

/-- Native local trivializations detect holomorphicity of actual sections. -/
theorem holomorphicAt_iff [C.IsContMDiff I ω] {U : Opens M}
    (s : ∀ y : U, C.Fiber (y : M)) (x : U) (i : ι) (hx : (x : M) ∈ C.baseSet i) :
    ContMDiffAt I (I.prod I₁) ω (fun y : U => (⟨(y : M), s y⟩ : C.TotalSpace)) x ↔
      ContMDiffAt I I₁ ω (fun y : U => (C.localTriv i ⟨(y : M), s y⟩).2) x := by
  rw [(C.localTriv i).contMDiffAt_iff
    (f := fun y : U => (⟨(y : M), s y⟩ : C.TotalSpace))
    (show (⟨(x : M), s x⟩ : C.TotalSpace) ∈ (C.localTriv i).source from hx)]
  exact and_iff_right (contMDiff_subtype_val x)

end Section

end Wikipedia.HopfProblem.NativeBundleSections
