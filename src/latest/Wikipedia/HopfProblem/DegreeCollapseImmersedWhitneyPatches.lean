import Wikipedia.HopfProblem.DegreeCollapseImmersedWhitneyArcs
import Wikipedia.HopfProblem.DegreeCollapseSelectiveSupport

/-!
# Clean source patches and an ambient branch-isolating neighborhood

Thicken the constructed disjoint source arcs to disjoint compact embedded
patch closures. Their images have exactly the two selected intersections.
When each selected value has exactly its two specified source preimages,
an ambient neighborhood of the whole arc pair sees only these patches.
The two-preimage condition is explicit: self-transversality alone does not
exclude a third branch at the same target value.
-/

noncomputable section

open Set Function Filter Topology
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.ImmersedSource

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization

variable {M : Type*} [TopologicalSpace M] {f : Sphere 3 → M}

omit [TopologicalSpace M] in
theorem CleanJoiningArc.doubleSources_on_image {x y : Sphere 3} {u v : Vector 3}
    (a : CleanJoiningArc f x y u v) {z : Sphere 3}
    (hz : z ∈ a.map '' Icc (0 : ℝ) 1) (hD : z ∈ doubleSources f) : z = x ∨ z = y := by
  obtain ⟨t, ht, rfl⟩ := hz
  by_cases ht0 : t = 0
  · exact Or.inl (by rw [ht0, a.start])
  by_cases ht1 : t = 1
  · exact Or.inr (by rw [ht1, a.finish])
  exact (a.avoids_doubleSources t
    ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩ hD).elim

omit [TopologicalSpace M] in
theorem CleanJoiningArc.preimage_image_subset {x y : Sphere 3} {u v : Vector 3}
    (a : CleanJoiningArc f x y u v) {W : Set (Sphere 3)}
    (hW : a.map '' Icc (0 : ℝ) 1 ⊆ W)
    (h0 : ∀ z, f z = f x → z ∈ W) (h1 : ∀ z, f z = f y → z ∈ W) :
    f ⁻¹' (f '' (a.map '' Icc (0 : ℝ) 1)) ⊆ W := by
  intro z hz
  obtain ⟨_, ⟨t, ht, rfl⟩, he⟩ := hz
  by_cases ht0 : t = 0
  · apply h0 z
    simpa only [ht0, a.start] using he.symm
  by_cases ht1 : t = 1
  · apply h1 z
    simpa only [ht1, a.finish] using he.symm
  have hez : a.map t = z := eq_of_not_mem_doubleSources
    (a.avoids_doubleSources t
      ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩) he
  exact hW ⟨t, ht, hez⟩

variable [T2Space M] [ChartedSpace (Vector 6) M] [IsManifold (𝓡 6) ∞ M]

theorem exists_clean_source_patches
    (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f)
    (hi : ∀ x, Injective (mfderiv (𝓡 3) (𝓡 6) f x))
    (hfinite : (SphereSelfIntersections.pairs f).Finite)
    {x₀ x₁ y₀ y₁ : Sphere 3} {u₀ u₁ v₀ v₁ : Vector 3}
    (a : CleanJoiningArc f x₀ x₁ u₀ u₁) (b : CleanJoiningArc f y₀ y₁ v₀ v₁)
    (hab : Disjoint (a.map '' Icc (0 : ℝ) 1) (b.map '' Icc (0 : ℝ) 1))
    (hc₀ : f x₀ = f y₀) (hc₁ : f x₁ = f y₁)
    (hfib₀ : ∀ z, f z = f x₀ → z = x₀ ∨ z = y₀)
    (hfib₁ : ∀ z, f z = f x₁ → z = x₁ ∨ z = y₁) :
    ∃ U V : Set (Sphere 3), ∃ O : Set M,
      IsOpen U ∧ IsOpen V ∧ IsOpen O ∧
      a.map '' Icc (0 : ℝ) 1 ⊆ U ∧ b.map '' Icc (0 : ℝ) 1 ⊆ V ∧
      IsCompact (closure U) ∧ IsCompact (closure V) ∧
      Disjoint (closure U) (closure V) ∧
      InjOn f (closure U) ∧ InjOn f (closure V) ∧
      IsClosedEmbedding (fun x : closure U => f x) ∧
      IsClosedEmbedding (fun x : closure V => f x) ∧
      (f '' (a.map '' Icc (0 : ℝ) 1 ∪ b.map '' Icc (0 : ℝ) 1)) ⊆ O ∧
      f ⁻¹' O ⊆ U ∪ V ∧
      (f '' closure U) ∩ (f '' closure V) = {f x₀, f x₁} := by
  let K : Set (Sphere 3) := a.map '' Icc (0 : ℝ) 1
  let L : Set (Sphere 3) := b.map '' Icc (0 : ℝ) 1
  have hK : IsCompact K := isCompact_Icc.image a.map.continuous
  have hL : IsCompact L := isCompact_Icc.image b.map.continuous
  have hD : (doubleSources f).Finite := hfinite.image _
  have hbadA : (doubleSources f \ {x₀, x₁}).Finite := hD.sdiff
  have hbadB : (doubleSources f \ {y₀, y₁}).Finite := hD.sdiff
  let W : Set (Sphere 3) := (doubleSources f \ {x₀, x₁})ᶜ ∩ Lᶜ
  have hW : IsOpen W := hbadA.isClosed.isOpen_compl.inter hL.isClosed.isOpen_compl
  have hKW : K ⊆ W := by
    intro z hz
    refine ⟨?_, fun hzL => (Set.disjoint_left.mp hab) hz hzL⟩
    intro hzbad
    exact hzbad.2 (a.doubleSources_on_image hz hzbad.1)
  obtain ⟨U, hU, hKU, hUW, hUc, hiU, heU⟩ :=
    exists_sphere_source_neighborhood hf hi hK a.image_injective hW hKW
  let Z : Set (Sphere 3) := (closure U)ᶜ ∩ (doubleSources f \ {y₀, y₁})ᶜ
  have hZ : IsOpen Z := isClosed_closure.isOpen_compl.inter hbadB.isClosed.isOpen_compl
  have hLZ : L ⊆ Z := by
    intro z hz
    refine ⟨fun hzU => (hUW hzU).2 hz, ?_⟩
    intro hzbad
    exact hzbad.2 (b.doubleSources_on_image hz hzbad.1)
  obtain ⟨V, hV, hLV, hVZ, hVc, hiV, heV⟩ :=
    exists_sphere_source_neighborhood hf hi hL b.image_injective hZ hLZ
  have hUV : Disjoint (closure U) (closure V) := Set.disjoint_left.mpr
    (fun _ hx hy => (hVZ hy).1 hx)
  have hx₀ : x₀ ∈ K := ⟨0, by simp, a.start⟩
  have hx₁ : x₁ ∈ K := ⟨1, by simp, a.finish⟩
  have hy₀ : y₀ ∈ L := ⟨0, by simp, b.start⟩
  have hy₁ : y₁ ∈ L := ⟨1, by simp, b.finish⟩
  have hfib0W : ∀ z, f z = f x₀ → z ∈ U ∪ V := by
    intro z hz
    rcases hfib₀ z hz with rfl | rfl
    · exact Or.inl (hKU hx₀)
    · exact Or.inr (hLV hy₀)
  have hfib1W : ∀ z, f z = f x₁ → z ∈ U ∪ V := by
    intro z hz
    rcases hfib₁ z hz with rfl | rfl
    · exact Or.inl (hKU hx₁)
    · exact Or.inr (hLV hy₁)
  have hpre : f ⁻¹' (f '' (K ∪ L)) ⊆ U ∪ V := by
    intro z hz
    obtain ⟨w, hw, hwz⟩ := hz
    rcases hw with hwK | hwL
    · exact a.preimage_image_subset (fun _ hh => Or.inl (hKU hh)) hfib0W hfib1W
        ⟨w, hwK, hwz⟩
    · exact b.preimage_image_subset (fun _ hh => Or.inr (hLV hh))
        (fun z hz => hfib0W z (hz.trans hc₀.symm))
        (fun z hz => hfib1W z (hz.trans hc₁.symm)) ⟨w, hwL, hwz⟩
  obtain ⟨O, hO, hBO, hpreO⟩ := SelectiveSheet.exists_target_neighborhood_of_preimage_subset
    hf.continuous (hU.union hV) hpre
  refine ⟨U, V, O, hU, hV, hO, hKU, hLV, hUc, hVc, hUV, hiU, hiV,
    heU, heV, hBO, hpreO, ?_⟩
  ext z
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, ⟨y, hy, he⟩⟩
    have hne : x ≠ y := fun heq => (Set.disjoint_left.mp hUV) hx (by rwa [heq])
    have hxD : x ∈ doubleSources f := ⟨(x, y), ⟨hne, he.symm⟩, rfl⟩
    have hxend : x ∈ ({x₀, x₁} : Set (Sphere 3)) := by
      by_contra hn
      exact (hUW hx).1 ⟨hxD, hn⟩
    rcases hxend with hxe | hxe
    · exact Or.inl (congrArg f hxe)
    · exact Or.inr (congrArg f (show x = x₁ from hxe))
  · rintro (rfl | hz)
    · exact ⟨⟨x₀, subset_closure (hKU hx₀), rfl⟩,
        ⟨y₀, subset_closure (hLV hy₀), hc₀.symm⟩⟩
    · have hz' : z = f x₁ := hz
      subst z
      exact ⟨⟨x₁, subset_closure (hKU hx₁), rfl⟩,
        ⟨y₁, subset_closure (hLV hy₁), hc₁.symm⟩⟩

end Wikipedia.HopfProblem.DegreeCollapse.ImmersedSource
