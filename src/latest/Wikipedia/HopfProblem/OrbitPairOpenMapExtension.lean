import Wikipedia.HopfProblem.OrbitPairOpenSmoothExtension
import Wikipedia.SmoothSixDPoincare.OpenHomotopyExtension

/-!
# Smooth extension of a local modification by the original map

A smooth map on an open region extends by a given smooth ambient map when
their discrepancy lies in a closed subset of the open region. The formulas
are exact on the region and off the support, with eventual equality to the
original map at every point outside that support.
-/

noncomputable section

open Set Topology Filter TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.OrbitPair.OpenMapExtension

open Wikipedia.SmoothSixDPoincare.OpenHomotopyExtension

variable {V H M W K N : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [TopologicalSpace H]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [TopologicalSpace K]
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace K N]
  (I : ModelWithCorners ℝ V H) (J : ModelWithCorners ℝ W K)

theorem smoothAt_on (U : Opens M) (f : M → N) (g : U → N)
    (hg : ContMDiff I J ∞ g) {x : M} (hx : x ∈ U) :
    ContMDiffAt I J ∞ (extendFunction U f g) x := by
  apply (contMDiffAt_subtype_iff (U := U) (x := ⟨x, hx⟩)).mp
  have he : (fun z : U => extendFunction U f g z.val) = g :=
    funext (extendFunction_of_mem U f g)
  rw [he]
  exact hg ⟨x, hx⟩

omit I J [ChartedSpace H M] [ChartedSpace K N] in
theorem eq_off (U : Opens M) (f : M → N) (g : U → N)
    {S : Set M} (hfixed : ∀ x : U, x.val ∉ S → g x = f x.val)
    {x : M} (hx : x ∉ S) : extendFunction U f g x = f x := by
  by_cases hxU : x ∈ U
  · exact (extendFunction_of_mem U f g ⟨x, hxU⟩).trans (hfixed ⟨x, hxU⟩ hx)
  · exact extendFunction_of_not_mem U f g hxU

omit I J [ChartedSpace H M] [ChartedSpace K N] in
theorem eventuallyEq_off (U : Opens M) (f : M → N) (g : U → N)
    {S : Set M} (hS : IsClosed S) (hfixed : ∀ x : U, x.val ∉ S → g x = f x.val)
    {x : M} (hx : x ∉ S) : extendFunction U f g =ᶠ[𝓝 x] f := by
  filter_upwards [hS.isOpen_compl.mem_nhds hx] with y hy
  exact eq_off U f g hfixed hy

theorem smooth (U : Opens M) (f : M → N) (g : U → N)
    (hf : ContMDiff I J ∞ f) (hg : ContMDiff I J ∞ g)
    {S : Set M} (hS : IsClosed S) (hSU : S ⊆ U)
    (hfixed : ∀ x : U, x.val ∉ S → g x = f x.val) :
    ContMDiff I J ∞ (extendFunction U f g) := by
  intro x
  by_cases hx : x ∈ U
  · exact smoothAt_on I J U f g hg hx
  · exact hf.contMDiffAt.congr_of_eventuallyEq
      (eventuallyEq_off U f g hS hfixed (fun h => hx (hSU h)))

end Wikipedia.HopfProblem.OrbitPair.OpenMapExtension
