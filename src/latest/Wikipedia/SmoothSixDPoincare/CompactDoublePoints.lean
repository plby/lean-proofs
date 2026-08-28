import Wikipedia.SmoothSixDPoincare.ImmersionLocalInjectivity

/-!
# Compactness of the off-diagonal self-intersection set

For a locally injective map, a union of products of injective neighborhoods
separates every diagonal point from the distinct collision pairs. The latter
therefore form a closed subset of the compact source square. In particular
this applies to maps with injective native derivatives on a compact set.
-/

noncomputable section

open Set
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ManifoldImmersion

section Topological

variable {X N : Type*} [TopologicalSpace X] [TopologicalSpace N] [T2Space N]

def doublePoints (f : X → N) (K : Set X) : Set (X × X) :=
  {q | q.1 ∈ K ∧ q.2 ∈ K ∧ q.1 ≠ q.2 ∧ f q.1 = f q.2}

/-- Off-diagonal collision pairs in a compact locally injective source region form a compact set. -/
theorem isCompact_doublePoints_of_locally_injective {f : X → N} (hf : Continuous f)
    {K : Set X} (hK : IsCompact K)
    (hlocal : ∀ x ∈ K, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ InjOn f U) :
    IsCompact (doublePoints f K) := by
  classical
  choose U hU hmem hinj using (fun x : K => hlocal x x.property)
  let V : Set (X × X) := ⋃ x : K, (U x) ×ˢ (U x)
  have hV : IsOpen V := isOpen_iUnion (fun x => (hU x).prod (hU x))
  have hclosed : IsClosed {q : X × X | f q.1 = f q.2} :=
    isClosed_eq (hf.comp continuous_fst) (hf.comp continuous_snd)
  have heq : doublePoints f K = ((K ×ˢ K) ∩ {q : X × X | f q.1 = f q.2}) ∩ Vᶜ := by
    ext q
    constructor
    · rintro ⟨hx, hy, hne, hcoll⟩
      refine ⟨⟨⟨hx, hy⟩, hcoll⟩, ?_⟩
      intro hv
      obtain ⟨x, hxU, hyU⟩ := mem_iUnion.mp hv
      exact hne (hinj x hxU hyU hcoll)
    · rintro ⟨⟨⟨hx, hy⟩, hcoll⟩, hv⟩
      refine ⟨hx, hy, ?_, hcoll⟩
      intro hxy
      apply hv
      apply mem_iUnion.mpr
      refine ⟨⟨q.1, hx⟩, hmem ⟨q.1, hx⟩, ?_⟩
      rw [← hxy]
      exact hmem ⟨q.1, hx⟩
  rw [heq]
  exact ((hK.prod hK).inter_right hclosed).inter_right hV.isClosed_compl

end Topological

variable {E G H N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [J.Boundaryless]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] [T2Space N]

/-- The actual distinct collision pairs of a compact immersive region form a compact set. -/
theorem isCompact_doublePoints_of_injective_nativeDerivative {f : E → N}
    (hf : ContMDiff 𝓘(ℝ, E) J ∞ f) {K : Set E} (hK : IsCompact K)
    (hinj : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f x)) :
    IsCompact (doublePoints f K) :=
  isCompact_doublePoints_of_locally_injective hf.continuous hK
    (fun _ hx => exists_open_injOn_of_injective_nativeDerivative hf (hinj _ hx))

end Wikipedia.SmoothSixDPoincare.ManifoldImmersion
