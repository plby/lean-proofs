import Wikipedia.HopfProblem.OrbitPairClosedImmersionRetraction
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

/-!
# Local native field extension from a closed embedded immersion

Recover source points smoothly near the embedded image, express the
prescribed tangent vectors in one actual tangent-bundle trivialization,
and use those coordinates in the ambient fibers. The resulting field
matches the prescribed vector at every source point mapping into the
target neighborhood, not merely on one chosen source patch.
-/

noncomputable section

open Set Function Bundle
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.OrbitPair.NativeImmersion

variable {E G H K X N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [TopologicalSpace H] [TopologicalSpace K]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {J : ModelWithCorners ℝ G K} [J.Boundaryless]
  [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X]
  [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N]

theorem exists_local_field_extension {f : X → N}
    (hf : ContMDiff I J ∞ f) (hemb : Topology.IsClosedEmbedding f)
    {u : (x : X) → TangentSpace J (f x)}
    (hu : ContMDiff I J.tangent ∞ (fun x => (⟨f x, u x⟩ : TangentBundle J N)))
    (x : X) (hi : Injective (mfderiv I J f x)) :
    ∃ O : Set N, IsOpen O ∧ f x ∈ O ∧ ∃ v : (y : N) → TangentSpace J y,
      ContMDiffOn J J.tangent ∞ (fun y => (⟨y, v y⟩ : TangentBundle J N)) O ∧
      ∀ z : X, f z ∈ O → v (f z) = u z := by
  obtain ⟨O₀, hO₀, hxO₀, r, hr, hrecover⟩ :=
    exists_recovery_of_closed_immersion hf hemb x hi
  let e := trivializationAt G (TangentSpace J) (f x)
  have hxe : f x ∈ e.baseSet :=
    FiberBundle.mem_baseSet_trivializationAt G (TangentSpace J) (f x)
  have hfr : ContMDiffOn J J ∞ (f ∘ r) O₀ := hf.comp_contMDiffOn hr
  let O : Set N := (O₀ ∩ (f ∘ r) ⁻¹' e.baseSet) ∩ e.baseSet
  have hO : IsOpen O :=
    (hfr.continuousOn.isOpen_inter_preimage hO₀ e.open_baseSet).inter e.open_baseSet
  have hxO : f x ∈ O := by
    refine ⟨⟨hxO₀, ?_⟩, hxe⟩
    change f (r (f x)) ∈ e.baseSet
    rw [hrecover x hxO₀]
    exact hxe
  let coords : N → G := fun y => (e (⟨f (r y), u (r y)⟩ : TangentBundle J N)).2
  have hsection : ContMDiffOn J J.tangent ∞
      (fun y => (⟨f (r y), u (r y)⟩ : TangentBundle J N)) O :=
    hu.comp_contMDiffOn (hr.mono (fun _ hy => hy.1.1))
  have hcoords : ContMDiffOn J 𝓘(ℝ, G) ∞ coords O := by
    have he : ContMDiffOn J.tangent (J.prod 𝓘(ℝ, G)) ∞ e e.source := e.contMDiffOn
    exact contMDiff_snd.comp_contMDiffOn
      (he.comp hsection (fun y hy => e.mem_source.mpr hy.1.2))
  let v : (y : N) → TangentSpace J y := fun y => e.symm y (coords y)
  have hv : ContMDiffOn J J.tangent ∞ (fun y => (⟨y, v y⟩ : TangentBundle J N)) O := by
    apply (e.contMDiffOn_section_iff hO (fun _ hy => hy.2)).mpr
    apply hcoords.congr
    intro y hy
    have hcoord := congrArg (fun p : N × G => p.2) (e.apply_mk_symm hy.2 (coords y))
    exact hcoord
  refine ⟨O, hO, hxO, v, hv, ?_⟩
  intro z hz
  change e.symm (f z) (e (⟨f (r (f z)), u (r (f z))⟩ : TangentBundle J N)).2 = u z
  rw [hrecover z hz.1.1]
  exact e.symm_apply_apply_mk hz.2 (u z)

end Wikipedia.HopfProblem.OrbitPair.NativeImmersion
