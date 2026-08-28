import Wikipedia.HopfProblem.OrbitPairSourceArcsFiniteAvoidance
import Wikipedia.HopfProblem.OrbitPairCollisionArcFibers

/-!
# Constructed clean boundary arcs for a pair of collision events

Two distinct collision values in one time slice have four distinct source
points. Construct disjoint embedded source arcs with interiors avoiding
all collision sources. Their projected arcs are embedded and immersive;
their intersections have exactly the two prescribed endpoint parameter
pairs. The full fixed-time source fiber of every arc value is recorded.

This constructs the boundary arcs. A smooth corner neighborhood, a clean
disk filling, its adapted framing, and the Whitney move remain separate.
-/

noncomputable section

open Set Function ContinuousMap
open scoped ContDiff Manifold Topology

namespace Wikipedia.HopfProblem.OrbitPair.NativeFamily

open FamilyDoublePoints

variable {E G H K M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace H] [TopologicalSpace K]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {J : ModelWithCorners ℝ G K}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [PathConnectedSpace M]
  [TopologicalSpace N] [ChartedSpace K N] [T2Space N]

structure CollisionArcPair (F : ℝ × M → N) (t : ℝ) (x₀ x₁ y₀ y₁ : M) where
  firstArc : C(ℝ, M)
  secondArc : C(ℝ, M)
  smoothFirst : ContMDiff 𝓘(ℝ, ℝ) I ∞ firstArc
  smoothSecond : ContMDiff 𝓘(ℝ, ℝ) I ∞ secondArc
  first_zero : firstArc 0 = x₀
  first_one : firstArc 1 = x₁
  second_zero : secondArc 0 = y₀
  second_one : secondArc 1 = y₁
  source_first_embedding : Topology.IsClosedEmbedding (fun s : unitInterval => firstArc s)
  source_second_embedding : Topology.IsClosedEmbedding (fun s : unitInterval => secondArc s)
  first_derivative : ∀ s ∈ Icc (0 : ℝ) 1, Injective (mfderiv 𝓘(ℝ, ℝ) I firstArc s)
  second_derivative : ∀ s ∈ Icc (0 : ℝ) 1, Injective (mfderiv 𝓘(ℝ, ℝ) I secondArc s)
  source_disjoint : Disjoint (range (fun s : unitInterval => firstArc s))
    (range (fun s : unitInterval => secondArc s))
  first_interior_avoids : ∀ s ∈ Ioo (0 : ℝ) 1,
    firstArc s ∉ Prod.snd '' collisionSources F
  second_interior_avoids : ∀ s ∈ Ioo (0 : ℝ) 1,
    secondArc s ∉ Prod.snd '' collisionSources F
  target_first_smooth : ContMDiff 𝓘(ℝ, ℝ) J ∞ (fun s => F (t, firstArc s))
  target_second_smooth : ContMDiff 𝓘(ℝ, ℝ) J ∞ (fun s => F (t, secondArc s))
  target_first_embedding : Topology.IsClosedEmbedding (fun s : unitInterval => F (t, firstArc s))
  target_second_embedding : Topology.IsClosedEmbedding (fun s : unitInterval => F (t, secondArc s))
  target_first_derivative : ∀ s ∈ Icc (0 : ℝ) 1,
    Injective (mfderiv 𝓘(ℝ, ℝ) J (fun u => F (t, firstArc u)) s)
  target_second_derivative : ∀ s ∈ Icc (0 : ℝ) 1,
    Injective (mfderiv 𝓘(ℝ, ℝ) J (fun u => F (t, secondArc u)) s)
  first_fiber : ∀ s ∈ Icc (0 : ℝ) 1, ∀ z : M,
    F (t, z) = F (t, firstArc s) ↔
      z = firstArc s ∨ (s = 0 ∧ z = y₀) ∨ (s = 1 ∧ z = y₁)
  second_fiber : ∀ s ∈ Icc (0 : ℝ) 1, ∀ z : M,
    F (t, z) = F (t, secondArc s) ↔
      z = secondArc s ∨ (s = 0 ∧ z = x₀) ∨ (s = 1 ∧ z = x₁)
  crossing_parameters : ∀ s ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
    F (t, firstArc s) = F (t, secondArc u) ↔ (s = 0 ∧ u = 0) ∨ (s = 1 ∧ u = 1)

theorem nonempty_collisionArcPair {F : ℝ × M → N}
    (hF : ContMDiff (𝓘(ℝ, ℝ).prod I) J ∞ F)
    (hi : ∀ t x, Injective (mfderiv I J (fun z => F (t, z)) x))
    (hfinite : (doublePoints F).Finite)
    (hglobal : ∀ p ∈ doublePoints F, HasGlobalProjectedCollisionFiber F p)
    (hdim : 2 ≤ Module.finrank ℝ E)
    {t : ℝ} {x₀ x₁ y₀ y₁ : M}
    (hp₀ : (t, (x₀, y₀)) ∈ doublePoints F)
    (hp₁ : (t, (x₁, y₁)) ∈ doublePoints F)
    (hvalue : F (t, x₀) ≠ F (t, x₁)) :
    Nonempty (CollisionArcPair (I := I) (J := J) F t x₀ x₁ y₀ y₁) := by
  obtain ⟨hxx, hyy, hcross⟩ := collision_pair_source_endpoints_distinct hp₀ hp₁ hvalue
  obtain ⟨f, g, hf, hg, hf0, hf1, hg0, hg1, hembf, hembg, hif, hig,
      hdisj, havoidf, havoidg⟩ := SourceArcs.exists_disjoint_embedded_arc_pair_avoiding_finite
    (I := I) hdim hxx hyy hcross ((finite_collisionSources hfinite).image Prod.snd)
  have hfiber := collision_arc_slice_fiber_formula hp₀ hp₁
    (hglobal _ hp₀) (hglobal _ hp₁) hf0 hf1 havoidf
  have hp₀swap : (t, (y₀, x₀)) ∈ doublePoints F := ⟨hp₀.1.symm, hp₀.2.symm⟩
  have hp₁swap : (t, (y₁, x₁)) ∈ doublePoints F := ⟨hp₁.1.symm, hp₁.2.symm⟩
  have gfiber := collision_arc_slice_fiber_formula hp₀swap hp₁swap
    (hglobal _ hp₀swap) (hglobal _ hp₁swap) hg0 hg1 havoidg
  have hslice : ContMDiff I J ∞ (fun x => F (t, x)) :=
    hF.comp (contMDiff_const.prodMk contMDiff_id)
  have hfs : ContMDiff 𝓘(ℝ, ℝ) J ∞ (fun s => F (t, f s)) := hslice.comp hf
  have hgs : ContMDiff 𝓘(ℝ, ℝ) J ∞ (fun s => F (t, g s)) := hslice.comp hg
  refine ⟨{
    firstArc := f
    secondArc := g
    smoothFirst := hf
    smoothSecond := hg
    first_zero := hf0
    first_one := hf1
    second_zero := hg0
    second_one := hg1
    source_first_embedding := hembf
    source_second_embedding := hembg
    first_derivative := hif
    second_derivative := hig
    source_disjoint := hdisj
    first_interior_avoids := havoidf
    second_interior_avoids := havoidg
    target_first_smooth := hfs
    target_second_smooth := hgs
    target_first_embedding := (hfs.continuous.comp continuous_subtype_val).isClosedEmbedding
      (collision_arc_projection_injective hembf.injective hdisj hg0 hg1 hfiber)
    target_second_embedding := (hgs.continuous.comp continuous_subtype_val).isClosedEmbedding
      (collision_arc_projection_injective hembg.injective hdisj.symm hf0 hf1 gfiber)
    target_first_derivative := ?_
    target_second_derivative := ?_
    first_fiber := hfiber
    second_fiber := gfiber
    crossing_parameters := collision_arc_crossing_parameters hp₀ hp₁ hf0 hf1 hg0 hg1
      hembg.injective hdisj hfiber }⟩
  · intro s hs
    change Injective (mfderiv 𝓘(ℝ, ℝ) J ((fun x => F (t, x)) ∘ f) s)
    rw [mfderiv_comp s (hslice.mdifferentiableAt (by simp)) (hf.mdifferentiableAt (by simp))]
    exact (hi t (f s)).comp (hif s hs)
  · intro s hs
    change Injective (mfderiv 𝓘(ℝ, ℝ) J ((fun x => F (t, x)) ∘ g) s)
    rw [mfderiv_comp s (hslice.mdifferentiableAt (by simp)) (hg.mdifferentiableAt (by simp))]
    exact (hi t (g s)).comp (hig s hs)

theorem nonempty_collisionArcPair_of_unordered_events {F : ℝ × M → N}
    (hF : ContMDiff (𝓘(ℝ, ℝ).prod I) J ∞ F)
    (hi : ∀ t x, Injective (mfderiv I J (fun z => F (t, z)) x))
    (hfinite : (doublePoints F).Finite)
    (hglobal : ∀ p ∈ doublePoints F, HasGlobalProjectedCollisionFiber F p)
    (hdim : 2 ≤ Module.finrank ℝ E)
    {t : ℝ} {u v : unorderedDoublePoints F}
    (hu : u.val.1 = t) (hv : v.val.1 = t) (hne : u ≠ v) :
    ∃ x₀ x₁ y₀ y₁ : M,
      u.val = (t, s(x₀, y₀)) ∧ v.val = (t, s(x₁, y₁)) ∧
      Nonempty (CollisionArcPair (I := I) (J := J) F t x₀ x₁ y₀ y₁) := by
  obtain ⟨⟨r, x₀, y₀⟩, hp, hpu⟩ := u.property
  obtain ⟨⟨s, x₁, y₁⟩, hq, hqv⟩ := v.property
  have hrt : r = t := (congrArg (fun z : ℝ × Sym2 M => z.1) hpu).trans hu
  have hst : s = t := (congrArg (fun z : ℝ × Sym2 M => z.1) hqv).trans hv
  subst r
  subst s
  have hvalue : F (t, x₀) ≠ F (t, x₁) := by
    intro heq
    have hproj := unorderedProjection_eq_of_projected_value_eq hglobal hp hq heq.symm
    exact hne (Subtype.ext (hpu.symm.trans (hproj.symm.trans hqv)))
  exact ⟨x₀, x₁, y₀, y₁, hpu.symm, hqv.symm,
    nonempty_collisionArcPair hF hi hfinite hglobal hdim hp hq hvalue⟩

end Wikipedia.HopfProblem.OrbitPair.NativeFamily
