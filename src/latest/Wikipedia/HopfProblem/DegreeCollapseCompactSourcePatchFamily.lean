import Wikipedia.HopfProblem.DegreeCollapseSelectiveSheetMotion

/-!
# Gluing an actual source-patch family across a closed inner support

The local family acts on source points and need not be an ambient
diffeomorphism. Smoothness at a prescribed interval of times suffices.
Agreement with the original map off a closed inner support gives the global
native smooth endpoint, its actual homotopy, and injective native derivatives.
-/

noncomputable section

open Set Function Filter Manifold Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SourcePatch

variable {X Y : Type*}

def family (f : X → Y) (H : ℝ × X → Y) (U : Set X) (z : ℝ × X) : Y := by
  classical
  exact if z.2 ∈ U then H z else f z.2

theorem family_on (f : X → Y) (H : ℝ × X → Y) (U : Set X)
    (t : ℝ) {x : X} (hx : x ∈ U) : family f H U (t, x) = H (t, x) := by
  simp only [family, hx, if_pos]

theorem family_off (f : X → Y) (H : ℝ × X → Y) (U : Set X)
    (t : ℝ) {x : X} (hx : x ∉ U) : family f H U (t, x) = f x := by
  simp only [family, hx, if_false]

theorem family_fixed {f : X → Y} {H : ℝ × X → Y} {U K : Set X}
    (hfix : ∀ t x, x ∈ U → x ∉ K → H (t, x) = f x)
    (t : ℝ) {x : X} (hx : x ∉ K) : family f H U (t, x) = f x := by
  by_cases hU : x ∈ U
  · exact (family_on f H U t hU).trans (hfix t x hU hx)
  · exact family_off f H U t hU

theorem family_start {f : X → Y} {H : ℝ × X → Y} {U : Set X}
    (hstart : ∀ x ∈ U, H (-1, x) = f x) (x : X) : family f H U (-1, x) = f x := by
  by_cases hx : x ∈ U
  · exact (family_on f H U (-1) hx).trans (hstart x hx)
  · exact family_off f H U (-1) hx

variable {E V H H' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ V H'}
  [TopologicalSpace X] [ChartedSpace H X] [TopologicalSpace Y] [ChartedSpace H' Y]

theorem contMDiffAt_family {f : X → Y} {A : ℝ × X → Y} {U K : Set X} {T : Set ℝ}
    (hU : IsOpen U) (hK : IsClosed K) (hKU : K ⊆ U)
    (hf : ContMDiff I J ∞ f)
    (hA : ∀ t ∈ T, ∀ x ∈ U, ContMDiffAt (𝓘(ℝ, ℝ).prod I) J ∞ A (t, x))
    (hfix : ∀ t x, x ∈ U → x ∉ K → A (t, x) = f x)
    {t : ℝ} (ht : t ∈ T) (x : X) :
    ContMDiffAt (𝓘(ℝ, ℝ).prod I) J ∞ (family f A U) (t, x) := by
  by_cases hx : x ∈ U
  · apply (hA t ht x hx).congr_of_eventuallyEq
    filter_upwards [(hU.preimage continuous_snd).mem_nhds hx] with z hz
    exact family_on f A U z.1 hz
  · have hxK : x ∉ K := fun h ↦ hx (hKU h)
    apply (hf.comp contMDiff_snd).contMDiffAt.congr_of_eventuallyEq
    filter_upwards [(hK.isOpen_compl.preimage continuous_snd).mem_nhds hxK] with z hz
    exact family_fixed hfix z.1 hz

theorem injective_mfderiv_family_endpoint {f : X → Y} {A : ℝ × X → Y} {U K : Set X}
    (hU : IsOpen U) (hK : IsClosed K) (hKU : K ⊆ U)
    (hdf : ∀ x, Injective (mfderiv I J f x))
    (hA : ∀ x ∈ U, Injective (mfderiv I J (fun y ↦ A (1, y)) x))
    (hfix : ∀ t x, x ∈ U → x ∉ K → A (t, x) = f x)
    (x : X) : Injective (mfderiv I J (fun y ↦ family f A U (1, y)) x) := by
  by_cases hx : x ∈ U
  · have he : (fun y ↦ family f A U (1, y)) =ᶠ[𝓝 x] (fun y ↦ A (1, y)) := by
      filter_upwards [hU.mem_nhds hx] with y hy
      exact family_on f A U 1 hy
    rw [he.mfderiv_eq]
    exact hA x hx
  · have hxK : x ∉ K := fun h ↦ hx (hKU h)
    have he : (fun y ↦ family f A U (1, y)) =ᶠ[𝓝 x] f := by
      filter_upwards [hK.isOpen_compl.mem_nhds hxK] with y hy
      exact family_fixed hfix 1 hy
    rw [he.mfderiv_eq]
    exact hdf x

theorem exists_immersed_endpoint_homotopic (f : C(X, Y)) {A : ℝ × X → Y} {U K : Set X}
    (hU : IsOpen U) (hK : IsClosed K) (hKU : K ⊆ U)
    (hf : ContMDiff I J ∞ f) (hdf : ∀ x, Injective (mfderiv I J f x))
    (hA : ∀ t ∈ Icc (-1 : ℝ) 1, ∀ x ∈ U,
      ContMDiffAt (𝓘(ℝ, ℝ).prod I) J ∞ A (t, x))
    (hAi : ∀ x ∈ U, Injective (mfderiv I J (fun y ↦ A (1, y)) x))
    (hstart : ∀ x ∈ U, A (-1, x) = f x)
    (hfix : ∀ t x, x ∈ U → x ∉ K → A (t, x) = f x) :
    ∃ g : C(X, Y), ContMDiff I J ∞ g ∧ f.Homotopic g ∧
      (∀ x, Injective (mfderiv I J g x)) ∧
      (∀ x, g x = family f A U (1, x)) ∧ (∀ x ∉ K, g x = f x) := by
  have hF (t : ℝ) (ht : t ∈ Icc (-1 : ℝ) 1) (x : X) :=
    contMDiffAt_family hU hK hKU hf hA hfix ht x
  have hlast : ContMDiff I J ∞ (fun x ↦ family f A U (1, x)) := by
    intro x
    exact (hF 1 (by norm_num : (1 : ℝ) ∈ Icc (-1 : ℝ) 1) x).comp x
      (contMDiffAt_const.prodMk contMDiffAt_id)
  let g : C(X, Y) := ⟨fun x ↦ family f A U (1, x), hlast.continuous⟩
  refine ⟨g, hlast, ?_, injective_mfderiv_family_endpoint hU hK hKU hdf hAi hfix,
    (fun _ ↦ rfl), (fun x hx ↦ family_fixed hfix 1 hx)⟩
  have hcont : ContinuousOn (family f A U) (Icc (-1 : ℝ) 1 ×ˢ univ) :=
    fun z hz ↦ (hF z.1 hz.1 z.2).continuousAt.continuousWithinAt
  refine ⟨{
    toFun := fun z ↦ family f A U (2 * (z.1 : ℝ) - 1, z.2)
    continuous_toFun := hcont.comp_continuous (by fun_prop) ?_
    map_zero_left := ?_
    map_one_left := ?_ }⟩
  · intro z
    refine ⟨?_, mem_univ _⟩
    have hz := z.1.property
    constructor <;> linarith [hz.1, hz.2]
  · intro x
    change family f A U (2 * (0 : ℝ) - 1, x) = f x
    norm_num
    exact family_start hstart x
  · intro x
    change family f A U (2 * (1 : ℝ) - 1, x) = family f A U (1, x)
    norm_num

end Wikipedia.HopfProblem.DegreeCollapse.SourcePatch
