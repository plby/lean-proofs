import Wikipedia.HopfProblem.OrbitPairLocalFieldExtension
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Native smooth field extension along a closed embedded immersion

Local field extensions glue by the proved smooth-section partition theorem.
The condition of agreeing with every prescribed vector above a given image
point is affine in its actual tangent fiber. Off the closed image the zero
section is a local admissible extension. The resulting field is globally
smooth in the original tangent bundle and agrees exactly along the whole
embedded image.
-/

noncomputable section

open Set Function Bundle Filter
open scoped ContDiff Manifold Topology

namespace Wikipedia.HopfProblem.OrbitPair.NativeImmersion

variable {E G H K X N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [TopologicalSpace H] [TopologicalSpace K]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {J : ModelWithCorners ℝ G K} [J.Boundaryless]
  [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X]
  [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N]
  [T2Space N] [SigmaCompactSpace N]

theorem exists_field_extension {f : X → N}
    (hf : ContMDiff I J ∞ f) (hemb : Topology.IsClosedEmbedding f)
    (hi : ∀ x, Injective (mfderiv I J f x))
    {u : (x : X) → TangentSpace J (f x)}
    (hu : ContMDiff I J.tangent ∞ (fun x => (⟨f x, u x⟩ : TangentBundle J N))) :
    ∃ v : (y : N) → TangentSpace J y,
      ContMDiff J J.tangent ∞ (fun y => (⟨y, v y⟩ : TangentBundle J N)) ∧
      ∀ x : X, v (f x) = u x := by
  let C : (y : N) → Set (TangentSpace J y) := fun y => {w | ∀ x : X, f x = y → w = u x}
  have hC : ∀ y, Convex ℝ (C y) := by
    intro y v hv w hw a b _ _ hab x hx
    subst y
    change a • v + b • w = u x
    rw [hv x rfl, hw x rfl, ← add_smul, hab, one_smul]
  have hlocal : ∀ y : N, ∃ O ∈ 𝓝 y, ∃ v : (z : N) → TangentSpace J z,
      ContMDiffOn J J.tangent ∞ (fun z => (⟨z, v z⟩ : TangentBundle J N)) O ∧
      ∀ z ∈ O, v z ∈ C z := by
    intro y
    by_cases hy : y ∈ range f
    · obtain ⟨x, rfl⟩ := hy
      obtain ⟨O, hO, hxO, v, hv, hmatch⟩ := exists_local_field_extension hf hemb hu x (hi x)
      refine ⟨O, hO.mem_nhds hxO, v, hv, ?_⟩
      intro z hz q hq
      subst z
      exact hmatch q hz
    · refine ⟨(range f)ᶜ, hemb.isClosed_range.isOpen_compl.mem_nhds hy,
        (fun _ => 0), (Bundle.contMDiff_zeroSection ℝ (TangentSpace J)).contMDiffOn, ?_⟩
      intro z hz x hx
      exact False.elim (hz ⟨x, hx⟩)
  obtain ⟨v, hv⟩ := exists_contMDiffSection_forall_mem_convex_of_local
    (n := ⊤) J (TangentSpace J (M := N)) C hC hlocal
  exact ⟨v, v.contMDiff, fun x => hv (f x) x rfl⟩

end Wikipedia.HopfProblem.OrbitPair.NativeImmersion
