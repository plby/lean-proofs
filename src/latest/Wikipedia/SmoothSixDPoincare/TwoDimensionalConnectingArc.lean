import Wikipedia.SmoothSixDPoincare.ShortEmbeddedArc
import Wikipedia.SmoothSixDPoincare.FinitePointPathAvoidance

/-!
# Embedded connecting arcs in dimension at least two

Start with a short embedded arc and move its far endpoint by an actual
global diffeomorphism fixing the starting point and the other finite
obstacles. Its image remains embedded and immersive. This avoids the
dimension-three restriction of generic removal of curve self-intersections.
-/

noncomputable section

open Set Function ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare

variable {G H N : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  [FiniteDimensional ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H}
  [J.Boundaryless] [TopologicalSpace N] [ChartedSpace H N]
  [IsManifold J ∞ N] [T2Space N]

/-- Embedded immersive connecting arcs with finite interior avoidance exist in dimension two. -/
theorem exists_embedded_connecting_arc_avoiding_finite_dim_two {x y : N}
    (γ : Path x y) (hxy : x ≠ y) (hdim : 2 ≤ Module.finrank ℝ G)
    {S : Set N} (hS : S.Finite) :
    ∃ f : C(ℝ, N), ContMDiff 𝓘(ℝ, ℝ) J ∞ f ∧ f 0 = x ∧ f 1 = y ∧
      Topology.IsClosedEmbedding (fun t : unitInterval => f t) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, Injective (mfderiv 𝓘(ℝ, ℝ) J f t)) ∧
      ∀ t ∈ Ioo (0 : ℝ) 1, f t ∉ S := by
  have hSx : (S \ {x}).Finite := hS.subset sdiff_subset
  obtain ⟨g, hg, hg0, hg1, hemb, hi, havoid⟩ :=
    exists_short_embedded_arc (J := J) hSx.isClosed.isOpen_compl
      (show x ∈ (S \ {x})ᶜ from by simp) hdim
  have hginj : InjOn g (Icc (0 : ℝ) 1) := by
    intro s hs t ht hst
    exact congrArg Subtype.val (hemb.injective (a₁ := ⟨s, hs⟩) (a₂ := ⟨t, ht⟩) hst)
  have hg1S : g 1 ∉ S := by
    intro hs
    exact havoid 1 (by simp) ⟨hs, hg1⟩
  let C : Set N := (insert x S) \ {y}
  have hC : C.Finite := (hS.insert x).subset sdiff_subset
  have hxC : x ∈ C := ⟨mem_insert x S, hxy⟩
  have hg1C : g 1 ∉ C := by
    rintro ⟨hr, _⟩
    rcases hr with hr | hr
    · exact hg1 hr
    · exact hg1S hr
  have hyC : y ∉ C := fun hy => hy.2 rfl
  let α : Path x (g 1) := {
    toFun := fun t => g t
    continuous_toFun := g.continuous.comp continuous_subtype_val
    source' := hg0
    target' := rfl }
  obtain ⟨d, hd, hfix⟩ := exists_pointMoving_fixing_finite (J := J)
    (α.symm.trans γ) hdim hC hg1C hyC
  let f : C(ℝ, N) := ⟨d ∘ g, d.continuous.comp g.continuous⟩
  have hf : ContMDiff 𝓘(ℝ, ℝ) J ∞ f := d.contMDiff.comp hg
  refine ⟨f, hf, ?_, hd, ?_, ?_, ?_⟩
  · change d (g 0) = x
    rw [hg0]
    exact hfix x hxC
  · apply (f.continuous.comp continuous_subtype_val).isClosedEmbedding
    intro s t hst
    exact hemb.injective (d.injective hst)
  · intro t ht
    change Injective (mfderiv 𝓘(ℝ, ℝ) J (d ∘ g) t)
    rw [mfderiv_comp t (d.contMDiff.mdifferentiableAt (by simp))
      (hg.mdifferentiableAt (by simp))]
    exact (PartialChart.bijective_mfderiv d.toPartialDiffeomorph (mem_univ (g t))).1.comp (hi t ht)
  · intro t ht hftS
    have htI : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
    by_cases hfty : f t = y
    · have hgt : g t = g 1 := d.injective (hfty.trans hd.symm)
      exact ht.2.ne (hginj htI (by simp) hgt)
    · have hftC : f t ∈ C := ⟨Or.inr hftS, hfty⟩
      have hgt : g t = f t := d.injective (hfix (f t) hftC).symm
      have hgtS : g t ∈ S := hgt.symm ▸ hftS
      have hgtx : g t ≠ x := by
        intro he
        exact ht.1.ne' (hginj htI (by simp) (he.trans hg0.symm))
      exact havoid t htI ⟨hgtS, hgtx⟩

end Wikipedia.SmoothSixDPoincare
