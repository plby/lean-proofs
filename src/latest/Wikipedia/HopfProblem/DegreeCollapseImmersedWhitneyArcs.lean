import Wikipedia.HopfProblem.DegreeCollapseImmersedSourceArc
import Wikipedia.HopfProblem.DegreeCollapseArcAvoidanceInOpen

/-!
# Two disjoint source arcs for actual self-intersection branches

Both arcs are constructed in the original source sphere. Their interiors
avoid every double-point preimage, their endpoint germs are prescribed,
and their ambient images meet exactly at the two selected values. No
global embedding of the source immersion is assumed.
-/

noncomputable section

open Set Function Filter Topology
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.ImmersedSource

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization
open Wikipedia.SmoothSixDPoincare

variable {M : Type*} [TopologicalSpace M]

structure CleanJoiningArc (f : Sphere 3 → M) (x y : Sphere 3) (u v : Vector 3) where
  map : C(ℝ, Sphere 3)
  smooth : ContMDiff 𝓘(ℝ, ℝ) (𝓡 3) ∞ map
  start : map 0 = x
  finish : map 1 = y
  start_germ : map =ᶠ[𝓝 (0 : ℝ)]
    fun t => NativeParametrization.centered (D := Vector 3) x (t • u)
  finish_germ : map =ᶠ[𝓝 (1 : ℝ)]
    fun t => NativeParametrization.centered (D := Vector 3) y ((1-t) • v)
  embedded : IsClosedEmbedding (fun t : unitInterval => map t)
  immersed : ∀ t ∈ Icc (0 : ℝ) 1, Injective (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) map t)
  avoids_doubleSources : ∀ t ∈ Ioo (0 : ℝ) 1, map t ∉ doubleSources f
  image_injective : InjOn f (map '' Icc (0 : ℝ) 1)

omit [TopologicalSpace M] in
theorem CleanJoiningArc.ambient_intersection_eq {f : Sphere 3 → M}
    {x₀ x₁ y₀ y₁ : Sphere 3} {u₀ u₁ v₀ v₁ : Vector 3}
    (a : CleanJoiningArc f x₀ x₁ u₀ u₁) (b : CleanJoiningArc f y₀ y₁ v₀ v₁)
    (hab : Disjoint (a.map '' Icc (0 : ℝ) 1) (b.map '' Icc (0 : ℝ) 1))
    (hc₀ : f x₀ = f y₀) (hc₁ : f x₁ = f y₁) :
    (f '' (a.map '' Icc (0 : ℝ) 1)) ∩ (f '' (b.map '' Icc (0 : ℝ) 1)) =
      {f x₀, f x₁} := by
  ext z
  constructor
  · rintro ⟨⟨_, ⟨t, ht, rfl⟩, rfl⟩, ⟨_, ⟨s, hs, rfl⟩, he⟩⟩
    by_cases ht0 : t = 0
    · rw [ht0, a.start]
      exact mem_insert _ _
    by_cases ht1 : t = 1
    · rw [ht1, a.finish]
      exact mem_insert_of_mem _ (mem_singleton _)
    have hne : a.map t ≠ b.map s := fun h =>
      (Set.disjoint_left.mp hab) ⟨t, ht, rfl⟩ ⟨s, hs, h.symm⟩
    exact (a.avoids_doubleSources t
      ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩
        ⟨(a.map t, b.map s), ⟨hne, he.symm⟩, rfl⟩).elim
  · rintro (rfl | hz)
    · exact ⟨⟨x₀, ⟨0, by simp, a.start⟩, rfl⟩,
        ⟨y₀, ⟨0, by simp, b.start⟩, hc₀.symm⟩⟩
    · have hz' : z = f x₁ := hz
      subst z
      exact ⟨⟨x₁, ⟨1, by simp, a.finish⟩, rfl⟩,
        ⟨y₁, ⟨1, by simp, b.finish⟩, hc₁.symm⟩⟩

variable [T2Space M] [ChartedSpace (Vector 6) M] [IsManifold (𝓡 6) ∞ M]

theorem exists_disjoint_clean_joining_arcs {f : Sphere 3 → M}
    (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f)
    (hi : ∀ x, Injective (mfderiv (𝓡 3) (𝓡 6) f x))
    (ht : ∀ x y, x ≠ y → f x = f y → Surjective
      ((mfderiv (𝓡 3) (𝓡 6) f x).coprod (mfderiv (𝓡 3) (𝓡 6) f y)))
    {x₀ x₁ y₀ y₁ : Sphere 3} (h₀ : x₀ ≠ y₀) (h₁ : x₁ ≠ y₁)
    (hc₀ : f x₀ = f y₀) (hc₁ : f x₁ = f y₁) (hvalues : f x₀ ≠ f x₁)
    (γ : Path x₀ x₁) (δ : Path y₀ y₁)
    {u₀ u₁ v₀ v₁ : Vector 3} (hu₀ : u₀ ≠ 0) (hu₁ : u₁ ≠ 0)
    (hv₀ : v₀ ≠ 0) (hv₁ : v₁ ≠ 0) :
    ∃ a : CleanJoiningArc f x₀ x₁ u₀ u₁,
    ∃ b : CleanJoiningArc f y₀ y₁ v₀ v₁,
      Disjoint (a.map '' Icc (0 : ℝ) 1) (b.map '' Icc (0 : ℝ) 1) ∧
      (f '' (a.map '' Icc (0 : ℝ) 1)) ∩ (f '' (b.map '' Icc (0 : ℝ) 1)) =
        {f x₀, f x₁} := by
  obtain ⟨a, ha, ha0, ha1, hag0, hag1, hea, hia, hava, hifa, -, -, -⟩ :=
    exists_clean_source_arc hf hi ht hvalues γ hu₀ hu₁
  have hvalues' : f y₀ ≠ f y₁ := by rwa [← hc₀, ← hc₁]
  obtain ⟨b, hb, hb0, hb1, hbg0, hbg1, heb, hib, havb, -, -, -, -⟩ :=
    exists_clean_source_arc hf hi ht hvalues' δ hv₀ hv₁
  have hb0off : b 0 ∉ a '' Icc (0 : ℝ) 1 := by
    rw [hb0]
    intro hy
    exact h₀ (hifa ⟨0, by simp, ha0⟩ hy hc₀)
  have hb1off : b 1 ∉ a '' Icc (0 : ℝ) 1 := by
    rw [hb1]
    intro hy
    exact h₁ (hifa ⟨1, by simp, ha1⟩ hy hc₁)
  let O : Set (Sphere 3) := (doubleSources f \ {y₀, y₁})ᶜ
  have hD : (doubleSources f).Finite := (SphereSelfIntersections.finite_pairs hf ht hi).image _
  have hbad : (doubleSources f \ {y₀, y₁}).Finite := hD.sdiff
  have hO : IsOpen O := hbad.isClosed.isOpen_compl
  have hmaps : MapsTo b (Icc (0 : ℝ) 1) O := by
    intro t htI htbad
    by_cases ht0 : t = 0
    · exact htbad.2 (Or.inl (by rw [ht0, hb0]))
    by_cases ht1 : t = 1
    · exact htbad.2 (Or.inr (show b t = y₁ by rw [ht1, hb1]))
    exact havb t ⟨lt_of_le_of_ne htI.1 (Ne.symm ht0),
      lt_of_le_of_ne htI.2 ht1⟩ htbad.1
  obtain ⟨c, hc, hcb0, hcb1, hec, hic, hmaps', hca⟩ :=
    exists_arc_disjoint_in_open a b ha hb
      (by simp : 3 ≤ Module.finrank ℝ (Vector 3)) heb hib hb0off hb1off hO hmaps
  have hc0 : c 0 = y₀ := hcb0.eq_of_nhds.trans hb0
  have hc1 : c 1 = y₁ := hcb1.eq_of_nhds.trans hb1
  have havc : ∀ t ∈ Ioo (0 : ℝ) 1, c t ∉ doubleSources f := by
    intro t htI htD
    have htC : t ∈ Icc (0 : ℝ) 1 := ⟨htI.1.le, htI.2.le⟩
    have hcend : c t ∈ ({y₀, y₁} : Set (Sphere 3)) := by
      by_contra hn
      exact hmaps' htC ⟨htD, hn⟩
    rcases hcend with hce | hce
    · have hte : (⟨t, htC⟩ : unitInterval) = 0 := hec.injective (by
        change c t = c 0
        rw [hc0]
        exact hce)
      exact htI.1.ne' (congrArg Subtype.val hte)
    · have hte : (⟨t, htC⟩ : unitInterval) = 1 := hec.injective (by
        change c t = c 1
        rw [hc1]
        exact hce)
      exact htI.2.ne (congrArg Subtype.val hte)
  have hifc : InjOn f (c '' Icc (0 : ℝ) 1) :=
    injOn_arc_image (by rwa [hc0, hc1]) havc
  let A : CleanJoiningArc f x₀ x₁ u₀ u₁ :=
    ⟨a, ha, ha0, ha1, hag0, hag1, hea, hia, hava, hifa⟩
  let B : CleanJoiningArc f y₀ y₁ v₀ v₁ :=
    ⟨c, hc, hc0, hc1, hcb0.trans hbg0, hcb1.trans hbg1, hec, hic, havc, hifc⟩
  exact ⟨A, B, hca.symm, A.ambient_intersection_eq B hca.symm hc₀ hc₁⟩

end Wikipedia.HopfProblem.DegreeCollapse.ImmersedSource
