import Wikipedia.HopfProblem.DegreeCollapseImmersedSourceNeighborhood
import Wikipedia.NoExoticSixSphere.SphereDoublePointParity
import Wikipedia.SmoothSixDPoincare.NativeArcEndpointGerms

/-!
# A clean joining arc in the source of a self-transverse immersion

Avoid the finite set of genuine double-point preimages in the open arc.
Every interior image point then has exactly one preimage in the entire
source sphere. Distinct endpoint images make the whole ambient arc
embedded; the original immersion supplies its injective native derivative.
-/

noncomputable section

open Set Function Filter Topology
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.ImmersedSource

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization
open Wikipedia.SmoothSixDPoincare

variable {M : Type*}

def doubleSources (f : Sphere 3 → M) : Set (Sphere 3) :=
  Prod.fst '' SphereSelfIntersections.pairs f

theorem eq_of_not_mem_doubleSources {f : Sphere 3 → M} {x y : Sphere 3}
    (hx : x ∉ doubleSources f) (he : f x = f y) : x = y := by
  by_contra hne
  exact hx ⟨(x, y), ⟨hne, he⟩, rfl⟩

theorem injOn_arc_image {f : Sphere 3 → M} {a : ℝ → Sphere 3}
    (hends : f (a 0) ≠ f (a 1))
    (havoid : ∀ t ∈ Ioo (0 : ℝ) 1, a t ∉ doubleSources f) :
    InjOn f (a '' Icc (0 : ℝ) 1) := by
  rintro x ⟨t, ht, rfl⟩ y ⟨s, hs, rfl⟩ he
  by_contra hne
  have htD : a t ∈ doubleSources f := ⟨(a t, a s), ⟨hne, he⟩, rfl⟩
  have hsD : a s ∈ doubleSources f := ⟨(a s, a t), ⟨fun h => hne h.symm, he.symm⟩, rfl⟩
  have htend : t = 0 ∨ t = 1 := by
    by_contra hn
    have hn' := not_or.mp hn
    exact havoid t ⟨lt_of_le_of_ne ht.1 (Ne.symm hn'.1),
      lt_of_le_of_ne ht.2 hn'.2⟩ htD
  have hsend : s = 0 ∨ s = 1 := by
    by_contra hn
    have hn' := not_or.mp hn
    exact havoid s ⟨lt_of_le_of_ne hs.1 (Ne.symm hn'.1),
      lt_of_le_of_ne hs.2 hn'.2⟩ hsD
  rcases htend with rfl | rfl <;> rcases hsend with rfl | rfl
  · exact hne rfl
  · exact hends he
  · exact hends he.symm
  · exact hne rfl

variable [TopologicalSpace M] [T2Space M]
  [ChartedSpace (Vector 6) M] [IsManifold (𝓡 6) ∞ M]

theorem exists_clean_source_arc {f : Sphere 3 → M}
    (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f)
    (hi : ∀ x, Injective (mfderiv (𝓡 3) (𝓡 6) f x))
    (ht : ∀ x y, x ≠ y → f x = f y → Surjective
      ((mfderiv (𝓡 3) (𝓡 6) f x).coprod (mfderiv (𝓡 3) (𝓡 6) f y)))
    {x y : Sphere 3} (hxy : f x ≠ f y) (γ : Path x y)
    {u v : Vector 3} (hu : u ≠ 0) (hv : v ≠ 0) :
    ∃ a : C(ℝ, Sphere 3), ContMDiff 𝓘(ℝ, ℝ) (𝓡 3) ∞ a ∧
      a 0 = x ∧ a 1 = y ∧
      (a =ᶠ[𝓝 (0 : ℝ)] fun t => NativeParametrization.centered (D := Vector 3) x (t • u)) ∧
      (a =ᶠ[𝓝 (1 : ℝ)] fun t => NativeParametrization.centered (D := Vector 3) y ((1-t) • v)) ∧
      IsClosedEmbedding (fun t : unitInterval => a t) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, Injective (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) a t)) ∧
      (∀ t ∈ Ioo (0 : ℝ) 1, a t ∉ doubleSources f) ∧
      InjOn f (a '' Icc (0 : ℝ) 1) ∧
      IsClosedEmbedding (fun t : unitInterval => f (a t)) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, Injective (mfderiv 𝓘(ℝ, ℝ) (𝓡 6) (f ∘ a) t)) ∧
      ∀ t ∈ Ioo (0 : ℝ) 1, ∀ z, f z = f (a t) → z = a t := by
  have hD : (doubleSources f).Finite := (SphereSelfIntersections.finite_pairs hf ht hi).image _
  have hne : x ≠ y := fun he => hxy (congrArg f he)
  obtain ⟨a, ha, ha0, ha1, hg0, hg1, hemb, hia, havoid⟩ :=
    exists_embedded_arc_with_native_endpoint_germs γ hne
      (by simp : 3 ≤ Module.finrank ℝ (Vector 3)) hu hv hD
  have hends : f (a 0) ≠ f (a 1) := by rwa [ha0, ha1]
  have hiarc := injOn_arc_image hends havoid
  refine ⟨a, ha, ha0, ha1, hg0, hg1, hemb, hia, havoid, hiarc, ?_, ?_, ?_⟩
  · apply (hf.continuous.comp (a.continuous.comp continuous_subtype_val)).isClosedEmbedding
    intro t s he
    exact hemb.injective (hiarc ⟨t, t.property, rfl⟩ ⟨s, s.property, rfl⟩ he)
  · intro t htI
    rw [mfderiv_comp t (hf.mdifferentiable (by simp) (a t))
      (ha.mdifferentiable (by simp) t)]
    exact (hi (a t)).comp (hia t htI)
  · intro t htI z he
    exact (eq_of_not_mem_doubleSources (havoid t htI) he.symm).symm

end Wikipedia.HopfProblem.DegreeCollapse.ImmersedSource
