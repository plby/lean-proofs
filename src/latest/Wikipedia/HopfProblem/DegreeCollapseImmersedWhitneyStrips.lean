import Wikipedia.HopfProblem.DegreeCollapseImmersedWhitneyCorners
import Wikipedia.HopfProblem.DegreeCollapsePatchCornerDerivative
import Wikipedia.HopfProblem.DegreeCollapseStripFromPatchArcChart

/-!
# Clean joining strips for the actual immersed-sphere branches

The ambient chart, transverse corner derivatives, and complete shared corner
germs construct an actual strip along the original source arc. Its contact
with the first full patch is exactly its center, and its contact with the
second full patch is exactly its endpoint axes. The normal data are retained
for the subsequent Whitney framing construction.
-/

noncomputable section

open Set Function Filter Module Topology
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.ImmersedSource

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization
open Wikipedia.SmoothSixDPoincare

variable {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (Vector 6) M] [IsManifold (𝓡 6) ∞ M]
  {f : Sphere 3 → M}

theorem CleanJoiningArc.exists_strip_with_shared_corners
    (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f)
    (hi : ∀ x, Injective (mfderiv (𝓡 3) (𝓡 6) f x))
    (ht : ∀ x y, x ≠ y → f x = f y → Surjective
      ((mfderiv (𝓡 3) (𝓡 6) f x).coprod (mfderiv (𝓡 3) (𝓡 6) f y)))
    {x₀ x₁ y₀ y₁ : Sphere 3} {u₀ u₁ v₀ v₁ : Vector 3}
    (a : CleanJoiningArc f x₀ x₁ u₀ u₁)
    (hc₀ : f x₀ = f y₀) (hc₁ : f x₁ = f y₁) (hv₀ : v₀ ≠ 0) (hv₁ : v₁ ≠ 0)
    {U V : Set (Sphere 3)} (hU : IsOpen U)
    (hAU : a.map '' Icc (0 : ℝ) 1 ⊆ U) (hy₀ : y₀ ∈ V) (hy₁ : y₁ ∈ V)
    (hUV : Disjoint (closure U) (closure V)) (hVc : IsCompact (closure V))
    (heU : IsClosedEmbedding (fun x : closure U => f x))
    (c₀ : CleanCornerPatch (E := Vector 6) (f '' closure U) (f '' closure V)
      (fun t => f (NativeParametrization.centered (D := Vector 3) x₀ (t • u₀)))
      (fun t => f (NativeParametrization.centered (D := Vector 3) y₀ (t • v₀))))
    (c₁ : CleanCornerPatch (E := Vector 6) (f '' closure U) (f '' closure V)
      (fun t => f (NativeParametrization.centered (D := Vector 3) x₁ (t • u₁)))
      (fun t => f (NativeParametrization.centered (D := Vector 3) y₁ (t • v₁))))
    {O : Set M} (hO : IsOpen O) (hAO : MapsTo (f ∘ a.map) (Icc (0 : ℝ) 1) O) :
    ∃ k : CleanStripPatch (E := Vector 6) (f '' closure U) (f '' closure V)
        (f ∘ a.map) c₀.map c₁.map,
      Nonempty (StripNormalData (Vector 2) (Vector 3) (E := Vector 6) (f '' closure U) k.map) ∧
      MapsTo k.map k.domain O := by
  obtain ⟨Φ, hline, htarget, hzero, hclean⟩ := a.exists_ambient_patch_chart hf hi hU hAU heU hO hAO
  have hx₀ : x₀ ∈ U := hAU ⟨0, by simp, a.start⟩
  have hx₁ : x₁ ∈ U := hAU ⟨1, by simp, a.finish⟩
  have hK₀ : closure U ∈ 𝓝 x₀ := mem_of_superset (hU.mem_nhds hx₀) subset_closure
  have hK₁ : closure U ∈ 𝓝 x₁ := mem_of_superset (hU.mem_nhds hx₁) subset_closure
  have hne₀ : x₀ ≠ y₀ := fun he => (Set.disjoint_left.mp hUV)
    (subset_closure hx₀) (by rw [he]; exact subset_closure hy₀)
  have hne₁ : x₁ ≠ y₁ := fun he => (Set.disjoint_left.mp hUV)
    (subset_closure hx₁) (by rw [he]; exact subset_closure hy₁)
  have hx₀Φ : f x₀ ∈ Φ.target := by
    have hs := hline (by simp : (0 : ℝ) ∈ Icc 0 1)
    have hh := Φ.map_source' hs
    rwa [hzero 0 hs, a.start] at hh
  have hx₁Φ : f x₁ ∈ Φ.target := by
    have hs := hline (by simp : (1 : ℝ) ∈ Icc 0 1)
    have hh := Φ.map_source' hs
    rwa [hzero 1 hs, a.finish] at hh
  let d₀ := NativeParametrization.centered (D := Vector 3) y₀
  let d₁ := NativeParametrization.centered (D := Vector 3) y₁
  have hd₀ : (0 : Vector 3) ∈ d₀.source := NativeParametrization.zero_mem_centered_source y₀
  have hd₁ : (0 : Vector 3) ∈ d₁.source := NativeParametrization.zero_mem_centered_source y₁
  have hdy₀ : d₀ 0 = y₀ := NativeParametrization.centered_zero y₀
  have hdy₁ : d₁ 0 = y₁ := NativeParametrization.centered_zero y₁
  have hn₀ := (patch_corner_normalDerivative_ne_zero Φ hf hf hclean d₀ hd₀ hK₀ hx₀Φ
    (by rw [hdy₀]; exact hc₀.symm)
    (by rw [hdy₀]; exact ht x₀ y₀ hne₀ hc₀) (by simp)
    c₀.smooth c₀.open_domain c₀.contains_zero hv₀ c₀.axis_second).1
  have hn₁ := (patch_corner_normalDerivative_ne_zero Φ hf hf hclean d₁ hd₁ hK₁ hx₁Φ
    (by rw [hdy₁]; exact hc₁.symm)
    (by rw [hdy₁]; exact ht x₁ y₁ hne₁ hc₁) (by simp)
    c₁.smooth c₁.open_domain c₁.contains_zero hv₁ c₁.axis_second).1
  have haxis₀ : (fun t : ℝ => c₀.map (t, 0)) =ᶠ[𝓝 0] (f ∘ a.map) := by
    have haxis := (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds
      (c₀.open_domain.mem_nhds c₀.contains_zero)
    filter_upwards [haxis, a.start_germ] with t htA he
    change c₀.map (t, 0) = f (a.map t)
    rw [c₀.axis_first t htA, he]
  have hrev : Tendsto (fun t : ℝ => 1-t) (𝓝 0) (𝓝 1) := by
    have he : Tendsto (fun t : ℝ => 1-t) (𝓝 0) (𝓝 (1-0)) :=
      (show Continuous (fun t : ℝ => 1-t) by fun_prop).continuousAt
    simpa only [sub_zero] using he
  have haxis₁ : (fun t : ℝ => c₁.map (t, 0)) =ᶠ[𝓝 0] fun t => (f ∘ a.map) (1-t) := by
    have haxis := (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds
      (c₁.open_domain.mem_nhds c₁.contains_zero)
    filter_upwards [haxis, a.finish_germ.comp_tendsto hrev] with t htA he
    change a.map (1-t) = NativeParametrization.centered (D := Vector 3) x₁ ((1-(1-t)) • u₁) at he
    change c₁.map (t, 0) = f (a.map (1-t))
    rw [c₁.axis_first t htA, he]
    have ht' : 1-(1-t) = t := by ring
    rw [ht']
  have havoid : ∀ t ∈ Ioo (0 : ℝ) 1, (f ∘ a.map) t ∉ f '' closure V := by
    intro t htI hh
    obtain ⟨z, hz, he⟩ := hh
    have htz : a.map t = z := eq_of_not_mem_doubleSources (a.avoids_doubleSources t htI) he.symm
    exact (Set.disjoint_left.mp hUV)
      (subset_closure (hAU ⟨t, ⟨htI.1.le, htI.2.le⟩, rfl⟩)) (by rw [htz]; exact hz)
  obtain ⟨k, hn, hmap⟩ := exists_strip_from_patch_arc_chart Φ hline hzero hclean
    (hVc.image hf.continuous).isClosed havoid c₀ c₁ haxis₀ haxis₁ hn₀ hn₁ (by simp)
  exact ⟨k, hn, fun p hp => htarget (hmap hp)⟩

theorem exists_native_branch_strip_pair
    (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f)
    (hi : ∀ x, Injective (mfderiv (𝓡 3) (𝓡 6) f x))
    (ht : ∀ x y, x ≠ y → f x = f y → Surjective
      ((mfderiv (𝓡 3) (𝓡 6) f x).coprod (mfderiv (𝓡 3) (𝓡 6) f y)))
    {x₀ x₁ y₀ y₁ : Sphere 3} {u₀ u₁ v₀ v₁ : Vector 3}
    (a : CleanJoiningArc f x₀ x₁ u₀ u₁) (b : CleanJoiningArc f y₀ y₁ v₀ v₁)
    (hc₀ : f x₀ = f y₀) (hc₁ : f x₁ = f y₁)
    (hu₀ : u₀ ≠ 0) (hu₁ : u₁ ≠ 0) (hv₀ : v₀ ≠ 0) (hv₁ : v₁ ≠ 0)
    {U V : Set (Sphere 3)} (hU : IsOpen U) (hV : IsOpen V)
    (hAU : a.map '' Icc (0 : ℝ) 1 ⊆ U) (hBV : b.map '' Icc (0 : ℝ) 1 ⊆ V)
    (hUV : Disjoint (closure U) (closure V))
    (hUc : IsCompact (closure U)) (hVc : IsCompact (closure V))
    (heU : IsClosedEmbedding (fun x : closure U => f x))
    (heV : IsClosedEmbedding (fun x : closure V => f x))
    {O : Set M} (hO : IsOpen O)
    (hAO : MapsTo (f ∘ a.map) (Icc (0 : ℝ) 1) O)
    (hBO : MapsTo (f ∘ b.map) (Icc (0 : ℝ) 1) O) :
    ∃ c₀ : CleanCornerPatch (E := Vector 6) (f '' closure U) (f '' closure V)
        (fun t => f (NativeParametrization.centered (D := Vector 3) x₀ (t • u₀)))
        (fun t => f (NativeParametrization.centered (D := Vector 3) y₀ (t • v₀))),
      ∃ c₁ : CleanCornerPatch (E := Vector 6) (f '' closure U) (f '' closure V)
          (fun t => f (NativeParametrization.centered (D := Vector 3) x₁ (t • u₁)))
          (fun t => f (NativeParametrization.centered (D := Vector 3) y₁ (t • v₁))),
        ∃ k : CleanStripPatch (E := Vector 6) (f '' closure U) (f '' closure V)
            (f ∘ a.map) c₀.map c₁.map,
          ∃ l : CleanStripPatch (E := Vector 6) (f '' closure V) (f '' closure U)
              (f ∘ b.map) c₀.swap.map c₁.swap.map,
            Nonempty (StripNormalData (Vector 2) (Vector 3) (E := Vector 6)
              (f '' closure U) k.map) ∧
            Nonempty (StripNormalData (Vector 2) (Vector 3) (E := Vector 6)
              (f '' closure V) l.map) ∧ MapsTo k.map k.domain O ∧ MapsTo l.map l.domain O := by
  obtain ⟨c₀, c₁, _, _⟩ := exists_native_branch_corner_pair hf ht a b hc₀ hc₁
    hu₀ hu₁ hv₀ hv₁ hU hV hAU hBV hUV heU heV hO hAO
  obtain ⟨k, hkN, hkO⟩ := a.exists_strip_with_shared_corners hf hi ht hc₀ hc₁ hv₀ hv₁
    hU hAU (hBV ⟨0, by simp, b.start⟩) (hBV ⟨1, by simp, b.finish⟩)
    hUV hVc heU c₀ c₁ hO hAO
  obtain ⟨l, hlN, hlO⟩ := b.exists_strip_with_shared_corners hf hi ht hc₀.symm hc₁.symm hu₀ hu₁
    hV hBV (hAU ⟨0, by simp, a.start⟩) (hAU ⟨1, by simp, a.finish⟩)
    hUV.symm hUc heV c₀.swap c₁.swap hO hBO
  exact ⟨c₀, c₁, k, l, hkN, hlN, hkO, hlO⟩

end Wikipedia.HopfProblem.DegreeCollapse.ImmersedSource
