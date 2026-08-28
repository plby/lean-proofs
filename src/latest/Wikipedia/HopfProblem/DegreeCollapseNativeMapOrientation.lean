import Wikipedia.HopfProblem.OrbitPairNativeChartOrientation

/-!
# Coherent orientation signs for native coordinate maps

A smooth coordinate map from an oriented manifold to a vector space need
not be globally injective. Wherever its actual native derivative is
invertible, its orientation sign is continuous. Source tangent-chart
changes cancel against the original orientation section. Thus the sign
is constant along a connected source arc in that region.
-/

noncomputable section

open Set Function Filter Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.DegreeCollapse.NativeMapOrientation

open OrbitPair.DeterminantSignCover

variable {D E H M : Type*}
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  (o : Orientation (tangentBundleCore I M)) (g : M → D) (J : D ≃L[ℝ] E)

def nativeFrame (x : M) : E →L[ℝ] E :=
  J.toContinuousLinearMap.comp (mfderiv I 𝓘(ℝ, D) g x)

omit [IsManifold I ∞ M] in
theorem nativeFrame_det_ne_zero {x : M}
    (hx : Bijective (mfderiv I 𝓘(ℝ, D) g x)) : (nativeFrame (I := I) g J x).det ≠ 0 := by
  intro hzero
  exact (LinearMap.det_eq_zero_iff_ker_ne_bot.mp hzero)
    (LinearMap.ker_eq_bot.mpr (J.injective.comp hx.1))

def fixedFrame (x₀ x : M) : E →L[ℝ] E :=
  J.toContinuousLinearMap.comp
    (inTangentCoordinates I 𝓘(ℝ, D) id g (fun x => mfderiv I 𝓘(ℝ, D) g x) x₀ x)

omit [FiniteDimensional ℝ E] in
theorem fixedFrame_eq {x₀ x : M} (hx : x ∈ (chartAt H x₀).source) :
    fixedFrame (I := I) g J x₀ x = (nativeFrame (I := I) g J x).comp
      ((tangentBundleCore I M).coordChange (achart H x₀) (achart H x) x) := by
  unfold fixedFrame
  rw [inTangentCoordinates_eq (I := I) (I' := 𝓘(ℝ, D)) id g
    (fun x => mfderiv I 𝓘(ℝ, D) g x) hx (show g x ∈ (chartAt D (g x₀)).source from mem_univ _)]
  simp only [tangentBundleCore_coordChange_model_space, ContinuousLinearMap.id_comp]
  rfl

omit [FiniteDimensional ℝ E] in
theorem continuousAt_fixedFrame {x₀ : M} (hg : ContMDiffAt I 𝓘(ℝ, D) ∞ g x₀) :
    ContinuousAt (fixedFrame (I := I) g J x₀) x₀ :=
  continuousAt_const.clm_comp (hg.mfderiv_const (m := 0) (by simp)).continuousAt

def sign (x : M) : Bool := action (nativeFrame (I := I) g J x).det (o.rawSign x)

theorem sign_eq_fixedFrame {x₀ x : M} (hx : x ∈ (chartAt H x₀).source)
    (hdet : (nativeFrame (I := I) g J x).det ≠ 0) :
    sign o g J x = action (fixedFrame (I := I) g J x₀ x).det
      (o.localSign (achart H x₀) x) := by
  have hself : o.localSign (achart H x) x = o.rawSign x := by
    rw [o.localSign_eq_action_rawSign]
    change action ((tangentBundleCore I M).coordChange (achart H x) (achart H x) x).det
      (o.rawSign x) = o.rawSign x
    rw [coordChange_self_eq (tangentBundleCore I M) (achart H x) (mem_chart_source H x)]
    change action (LinearMap.id : E →ₗ[ℝ] E).det (o.rawSign x) = o.rawSign x
    rw [LinearMap.det_id]
    exact action_one _
  have hlocal := o.localSign_coordChange (achart H x₀) (achart H x)
    ⟨hx, mem_chart_source H x⟩
  rw [hself] at hlocal
  rw [fixedFrame_eq g J hx]
  have hcomp : ((nativeFrame (I := I) g J x).comp
      ((tangentBundleCore I M).coordChange (achart H x₀) (achart H x) x)).det =
      (nativeFrame (I := I) g J x).det *
        ((tangentBundleCore I M).coordChange (achart H x₀) (achart H x) x).det :=
    LinearMap.det_comp _ _
  rw [hcomp, action_mul _ _ hdet
    (coordChange_det_ne_zero (tangentBundleCore I M) _ _ ⟨hx, mem_chart_source H x⟩), hlocal]
  rfl

theorem continuousAt_sign {x₀ : M} (hg : ContMDiffAt I 𝓘(ℝ, D) ∞ g x₀)
    (hdet : ∀ᶠ x in 𝓝 x₀, (nativeFrame (I := I) g J x).det ≠ 0) :
    ContinuousAt (sign o g J) x₀ := by
  have hchart₀ : x₀ ∈ (chartAt H x₀).source := mem_chart_source H x₀
  have hlocal : ContinuousAt (o.localSign (achart H x₀)) x₀ :=
    (o.continuousOn_localSign (achart H x₀)).continuousAt
      ((chartAt H x₀).open_source.mem_nhds hchart₀)
  have hfixed : (fixedFrame (I := I) g J x₀ x₀).det ≠ 0 := by
    rw [fixedFrame_eq g J hchart₀,
      coordChange_self_eq (tangentBundleCore I M) (achart H x₀) hchart₀,
      ContinuousLinearMap.comp_id]
    exact hdet.self_of_nhds
  have hs : ContinuousAt (fun x => action (fixedFrame (I := I) g J x₀ x).det
      (o.localSign (achart H x₀) x)) x₀ := by
    have hp : ContinuousAt (fun x => ((fixedFrame (I := I) g J x₀ x).det,
        o.localSign (achart H x₀) x)) x₀ :=
      (ContinuousLinearMap.continuous_det.continuousAt.comp
        (continuousAt_fixedFrame (I := I) g J hg)).prodMk hlocal
    exact (continuousAt_action hfixed _).comp_of_eq hp rfl
  apply hs.congr_of_eventuallyEq
  filter_upwards [(chartAt H x₀).open_source.mem_nhds hchart₀, hdet] with x hx hd
  exact sign_eq_fixedFrame o g J hx hd

theorem continuousOn_sign {U : Set M} (hU : IsOpen U)
    (hg : ContMDiffOn I 𝓘(ℝ, D) ∞ g U)
    (hbij : ∀ x ∈ U, Bijective (mfderiv I 𝓘(ℝ, D) g x)) :
    ContinuousOn (sign o g J) U := by
  intro x hx
  apply (continuousAt_sign o g J (hg.contMDiffAt (hU.mem_nhds hx)) ?_).continuousWithinAt
  filter_upwards [hU.mem_nhds hx] with y hy
  exact nativeFrame_det_ne_zero g J (hbij y hy)

theorem sign_eq_on_preconnected {U : Set M} (hU : IsOpen U)
    (hg : ContMDiffOn I 𝓘(ℝ, D) ∞ g U)
    (hbij : ∀ x ∈ U, Bijective (mfderiv I 𝓘(ℝ, D) g x))
    {A : Type*} [TopologicalSpace A] {a : A → M} {s : Set A}
    (hs : IsPreconnected s) (ha : ContinuousOn a s) (himage : MapsTo a s U)
    {x y : A} (hx : x ∈ s) (hy : y ∈ s) :
    sign o g J (a x) = sign o g J (a y) :=
  hs.constant ((continuousOn_sign o g J hU hg hbij).comp ha himage) hx hy

end Wikipedia.HopfProblem.DegreeCollapse.NativeMapOrientation
