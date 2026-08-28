import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPushforwardSectionsBasic

/-!
# Equality of native holomorphic sections from a dense set

Continuity in an actual local bundle trivialization extends equality
from a dense set. No Hausdorff assumption on the entire total space or
continuity of a preferred scalar coordinate is required.
-/

noncomputable section

open Bundle Set Filter Topology TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.NativeBundleSections.Section

variable {M : Type} {ι : Type*} [TopologicalSpace M]
  (C : VectorBundleCore ℂ M ℂ ι)
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] [ChartedSpace H M] (I : ModelWithCorners ℂ E H)
  [C.IsContMDiff I ω]

/-- Actual native holomorphic sections agreeing on a dense subset of
their open domain agree in every original fibre. -/
theorem ext_of_dense {U : Opens M} {D : Set U} (hD : Dense D)
    {s t : NativeBundleSections.Section C I U}
    (he : ∀ x ∈ D, s x = t x) : s = t := by
  apply NativeBundleSections.Section.ext C I
  intro x
  by_contra hx
  let i := C.indexAt (x : M)
  have hi : (x : M) ∈ C.baseSet i := C.mem_baseSet_at x
  have hs := (holomorphicAt_iff C I s x i hi).mp (s.contMDiff_toFun x)
  have ht := (holomorphicAt_iff C I t x i hi).mp (t.contMDiff_toFun x)
  have hc : (C.localTriv i ⟨(x : M), s x⟩).2 ≠
      (C.localTriv i ⟨(x : M), t x⟩).2 := by
    intro h
    exact hx (((C.localTriv i).linearEquivAt ℂ (x : M) hi).injective h)
  have hN : {y : U | (C.localTriv i ⟨(y : M), s y⟩).2 -
      (C.localTriv i ⟨(y : M), t y⟩).2 ≠ 0} ∈ 𝓝 x :=
    (hs.sub ht).continuousAt.eventually_ne (sub_ne_zero.mpr hc)
  obtain ⟨y, hy, hyD⟩ := (mem_closure_iff_nhds.mp (hD x)) _ hN
  exact hy (sub_eq_zero.mpr (congrArg
    (fun v : C.Fiber (y : M) => (C.localTriv i ⟨(y : M), v⟩).2) (he y hyD)))

/-- A dense subset of the base remains sufficient after restricting to
an arbitrary open domain of the original native bundle. -/
theorem ext_of_dense_base {U : Opens M} {D : Set M} (hD : Dense D)
    {s t : NativeBundleSections.Section C I U}
    (he : ∀ x : U, (x : M) ∈ D → s x = t x) : s = t := by
  apply ext_of_dense C I (hD.preimage U.isOpen.isOpenMap_subtype_val)
  exact he

end Wikipedia.HopfProblem.NativeBundleSections.Section
