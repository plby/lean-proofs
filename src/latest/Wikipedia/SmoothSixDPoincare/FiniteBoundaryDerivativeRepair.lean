import Wikipedia.SmoothSixDPoincare.BoundaryDerivativeRepairStep

/-!
# Finite repair of boundary derivatives with boundary values fixed

The old compact immersive region and the tangent common-kernel condition
survive every patch. Hence the finite procedure can make the whole prescribed
compact boundary locus immersive without moving any of its points.
-/

noncomputable section

open Set ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ManifoldImmersion

open ManifoldSmoothing (MapSmoothingPatch)

variable {B E G H H' X N : Type*}
  [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ B H} {J : ModelWithCorners ℝ G H'} [J.Boundaryless]
  [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X] [LindelofSpace (X × E)]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]

/-- Repair finitely many boundary patches while retaining the common-kernel condition and
all previously injective derivatives. -/
theorem exists_finite_boundary_derivative_repair {ι : Type*} [Finite ι]
    (p : ι → MapSmoothingPatch 𝓘(ℝ, E) J (X := E) (N := N))
    (L : ι → Set E) (hL : ∀ i, IsCompact (L i)) (hLsub : ∀ i, L i ⊆ (p i).plateau)
    (f : C(E, N)) (hf : ContMDiff 𝓘(ℝ, E) J ∞ f) (hcompatible : ∀ i, (p i).Compatible f)
    {b : X → E} (hb : ContMDiff I 𝓘(ℝ, E) ∞ b) (hLrange : ∀ i, L i ⊆ range b)
    {ρ : E → ℝ} (hρ : ContDiff ℝ ∞ ρ) (hzero : ∀ x, ρ (b x) = 0)
    (hdim : Module.finrank ℝ B + Module.finrank ℝ E < Module.finrank ℝ G)
    {K : Set E} (hK : IsCompact K)
    (hinj : ∀ y ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f y))
    (hcommon : ∀ y, ρ y = 0 → ∀ v, mfderiv 𝓘(ℝ, E) J f y v = 0 →
      fderiv ℝ ρ y v = 0 → v = 0) (s : Finset ι) :
    ∃ g : C(E, N), ContMDiff 𝓘(ℝ, E) J ∞ g ∧ (∀ i, (p i).Compatible g) ∧
      f.HomotopicRel g {y | ρ y = 0} ∧
      (∀ y, ρ y = 0 → ∀ v, mfderiv 𝓘(ℝ, E) J g y v = 0 →
        fderiv ℝ ρ y v = 0 → v = 0) ∧
      ∀ y ∈ K ∪ ⋃ i ∈ s, L i, Function.Injective (mfderiv 𝓘(ℝ, E) J g y) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨f, hf, hcompatible, HomotopicRel.refl f, hcommon, ?_⟩
    simpa only [Finset.notMem_empty, iUnion_of_empty, iUnion_empty, union_empty] using hinj
  | @insert i s _ ih =>
    obtain ⟨g₁, hg₁, hc₁, hhom₁, hcommon₁, hinj₁⟩ := ih
    have hKold : IsCompact (K ∪ ⋃ j ∈ s, L j) :=
      hK.union (s.isCompact_biUnion (fun j _ => hL j))
    obtain ⟨g₂, hg₂, hc₂, hhom₂, hcommon₂, hinj₂⟩ :=
      exists_boundary_derivative_repair_step p i g₁ hg₁ hc₁ hb hρ hzero hdim
        hKold hinj₁ (hLsub i) (hLrange i) hcommon₁
    refine ⟨g₂, hg₂, hc₂, hhom₁.trans hhom₂, hcommon₂, ?_⟩
    intro y hy
    apply hinj₂ y
    rcases hy with hy | hy
    · exact Or.inl (Or.inl hy)
    · obtain ⟨j, hj, hyj⟩ := mem_iUnion₂.mp hy
      rcases Finset.mem_insert.mp hj with rfl | hjs
      · exact Or.inr hyj
      · exact Or.inl (Or.inr (mem_iUnion₂.mpr ⟨j, hjs, hyj⟩))

end Wikipedia.SmoothSixDPoincare.ManifoldImmersion
