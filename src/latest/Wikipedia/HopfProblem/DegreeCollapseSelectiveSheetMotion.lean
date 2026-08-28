import Wikipedia.SmoothSixDPoincare.AmbientIsotopy
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Topology.Homotopy.Basic

/-!
# Applying an ambient motion to only one source sheet

For an immersion, applying an ambient diffeomorphism to its whole image
cannot remove self-intersections. Here the motion is applied only on an
open source patch. A closed inner support keeps the patch boundary fixed,
so the family is jointly smooth and all slices remain immersive.
-/

noncomputable section

open Set Function Filter Manifold Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SelectiveSheet

variable {X Y : Type*}

def family (f : X → Y) (A : ℝ × Y → Y) (U : Set X) (z : ℝ × X) : Y := by
  classical
  exact if z.2 ∈ U then A (z.1, f z.2) else f z.2

theorem family_on (f : X → Y) (A : ℝ × Y → Y) (U : Set X)
    (t : ℝ) {x : X} (hx : x ∈ U) : family f A U (t, x) = A (t, f x) := by
  simp only [family, hx, if_pos]

theorem family_off (f : X → Y) (A : ℝ × Y → Y) (U : Set X)
    (t : ℝ) {x : X} (hx : x ∉ U) : family f A U (t, x) = f x := by
  simp only [family, hx, if_false]

theorem family_fixed {f : X → Y} {A : ℝ × Y → Y} {U K : Set X}
    (hfix : ∀ t x, x ∈ U → x ∉ K → A (t, f x) = f x)
    (t : ℝ) {x : X} (hx : x ∉ K) : family f A U (t, x) = f x := by
  by_cases hU : x ∈ U
  · exact (family_on f A U t hU).trans (hfix t x hU hx)
  · exact family_off f A U t hU

theorem family_zero {f : X → Y} {A : ℝ × Y → Y} {U : Set X}
    (hA0 : ∀ y, A (0, y) = y) (x : X) : family f A U (0, x) = f x := by
  by_cases hx : x ∈ U
  · exact (family_on f A U 0 hx).trans (hA0 (f x))
  · exact family_off f A U 0 hx

variable {E V H H' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ V H'}
  [TopologicalSpace X] [ChartedSpace H X] [TopologicalSpace Y] [ChartedSpace H' Y]

theorem contMDiff_family {f : X → Y} {A : ℝ × Y → Y} {U K : Set X}
    (hU : IsOpen U) (hK : IsClosed K) (hKU : K ⊆ U)
    (hf : ContMDiff I J ∞ f) (hA : ContMDiff (𝓘(ℝ, ℝ).prod J) J ∞ A)
    (hfix : ∀ t x, x ∈ U → x ∉ K → A (t, f x) = f x) :
    ContMDiff (𝓘(ℝ, ℝ).prod I) J ∞ (family f A U) := by
  intro z
  by_cases hz : z.2 ∈ U
  · have hs := (hA.comp (contMDiff_fst.prodMk (hf.comp contMDiff_snd))).contMDiffAt (x := z)
    apply hs.congr_of_eventuallyEq
    filter_upwards [(hU.preimage continuous_snd).mem_nhds hz] with w hw
    exact family_on f A U w.1 hw
  · have hzK : z.2 ∉ K := fun hh => hz (hKU hh)
    apply (hf.comp contMDiff_snd).contMDiffAt.congr_of_eventuallyEq
    filter_upwards [(hK.isOpen_compl.preimage continuous_snd).mem_nhds hzK] with w hw
    exact family_fixed hfix w.1 hw

theorem injective_mfderiv_family_slice {f : X → Y} {A : ℝ × Y → Y} {U K : Set X}
    (hU : IsOpen U) (hK : IsClosed K) (hKU : K ⊆ U)
    (hf : ContMDiff I J ∞ f) (hdf : ∀ x, Injective (mfderiv I J f x))
    (hslice : ∀ t, ∃ D : Diffeomorph J J Y Y ∞, ∀ y, A (t, y) = D y)
    (hfix : ∀ t x, x ∈ U → x ∉ K → A (t, f x) = f x)
    (t : ℝ) (x : X) : Injective (mfderiv I J (fun y => family f A U (t, y)) x) := by
  by_cases hx : x ∈ U
  · obtain ⟨D, hD⟩ := hslice t
    have heq : (fun y => family f A U (t, y)) =ᶠ[𝓝 x] (D ∘ f) := by
      filter_upwards [hU.mem_nhds hx] with y hy
      exact (family_on f A U t hy).trans (hD (f y))
    rw [heq.mfderiv_eq, mfderiv_comp x
      (D.contMDiff.mdifferentiable (by simp) (f x)) (hf.mdifferentiable (by simp) x)]
    exact (D.mfderivToContinuousLinearEquiv (by simp) (f x)).injective.comp (hdf x)
  · have hxK : x ∉ K := fun hh => hx (hKU hh)
    have heq : (fun y => family f A U (t, y)) =ᶠ[𝓝 x] f := by
      filter_upwards [hK.isOpen_compl.mem_nhds hxK] with y hy
      exact family_fixed hfix t hy
    rw [heq.mfderiv_eq]
    exact hdf x

theorem exists_immersed_endpoint_homotopic (f : C(X, Y)) {A : ℝ × Y → Y} {U K : Set X}
    (hU : IsOpen U) (hK : IsClosed K) (hKU : K ⊆ U)
    (hf : ContMDiff I J ∞ f) (hdf : ∀ x, Injective (mfderiv I J f x))
    (hA : ContMDiff (𝓘(ℝ, ℝ).prod J) J ∞ A) (hA0 : ∀ y, A (0, y) = y)
    (hslice : ∀ t, ∃ D : Diffeomorph J J Y Y ∞, ∀ y, A (t, y) = D y)
    (hfix : ∀ t x, x ∈ U → x ∉ K → A (t, f x) = f x) :
    ∃ g : C(X, Y), ContMDiff I J ∞ g ∧ f.Homotopic g ∧
      (∀ x, Injective (mfderiv I J g x)) ∧
      (∀ x, g x = family f A U (1, x)) ∧ (∀ x ∉ K, g x = f x) := by
  have hF := contMDiff_family hU hK hKU hf hA hfix
  have hlast : ContMDiff I J ∞ (fun x => family f A U (1, x)) :=
    hF.comp (contMDiff_const.prodMk contMDiff_id)
  let g : C(X, Y) := ⟨fun x => family f A U (1, x), hlast.continuous⟩
  refine ⟨g, hlast, ?_, injective_mfderiv_family_slice hU hK hKU hf hdf hslice hfix 1,
    fun _ => rfl, fun x hx => family_fixed hfix 1 hx⟩
  exact ⟨{
    toFun := fun z => family f A U ((z.1 : ℝ), z.2)
    continuous_toFun := hF.continuous.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
    map_zero_left := family_zero hA0
    map_one_left := fun _ => rfl }⟩

end Wikipedia.HopfProblem.DegreeCollapse.SelectiveSheet
