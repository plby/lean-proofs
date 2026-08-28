import Wikipedia.HopfProblem.DegreeCollapseIntegralSupportChartTransport

/-!
# Integral fundamental classes on compact supports in the original charts

The image of a compact support under an actual chart has the constructed
Euclidean integral class. Transport it through the original excision and
source-target homeomorphism maps. Its local values are precisely the
primitive integral classes defined by this chart, with their signs.
No compatibility between different chart orientations is assumed here.
-/

noncomputable section

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralChartOrientation

open NoExoticSixSphere SupportedRelativeHomology

variable {E M : Type} [NormedAddCommGroup E] [TopologicalSpace M]

theorem image_compact (e : OpenPartialHomeomorph M E) (K : Set M)
    (hK : IsCompact K) (hKs : K ⊆ e.source) : IsCompact (e '' K) :=
  hK.image_of_continuousOn (e.continuousOn.mono hKs)

theorem image_subset_target (e : OpenPartialHomeomorph M E) (K : Set M)
    (hKs : K ⊆ e.source) : e '' K ⊆ e.target := by
  rintro y ⟨x, hx, rfl⟩
  exact e.map_source (hKs hx)

theorem image_membership (e : OpenPartialHomeomorph M E) (K : Set M)
    (hKs : K ⊆ e.source) (x : M) (hx : x ∈ e.source) : x ∈ K ↔ e x ∈ e '' K := by
  constructor
  · intro h
    exact ⟨x, h, rfl⟩
  · rintro ⟨y, hy, he⟩
    exact (e.injOn (hKs hy) hx he) ▸ hy

variable [T2Space M] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  (n : ℕ) [Fact (Module.finrank ℝ E = (n + 1) + 1)]

/-- The actual integral homology equivalence of the support with its chart image. -/
def supportEquiv (e : OpenPartialHomeomorph M E) (K : Set M)
    (hK : IsCompact K) (hKs : K ⊆ e.source) :
    Homology (ModuleCat.of ℤ ℤ) K (n + 2) ≃ₗ[ℤ]
      Homology (ModuleCat.of ℤ ℤ) (e '' K) (n + 2) :=
  IntegralSupportTransport.partialHomeomorphEquiv e hK.isClosed
    (image_compact e K hK hKs).isClosed hKs (image_subset_target e K hKs)
    (image_membership e K hKs) (n + 2)

/-- This class is constructed from the actual compact chart image, not supplied. -/
def fundamentalClass (e : OpenPartialHomeomorph M E) (K : Set M)
    (hK : IsCompact K) (hKs : K ⊆ e.source) : Homology (ModuleCat.of ℤ ℤ) K (n + 2) :=
  (supportEquiv n e K hK hKs).symm
    (IntegralEuclideanOrientation.fundamentalClass E n (e '' K)
      (image_compact e K hK hKs).isBounded)

/-- Every localization is exactly the original chart's primitive signed integral class. -/
theorem fundamentalClass_evaluate (e : OpenPartialHomeomorph M E) (K : Set M)
    (hK : IsCompact K) (hKs : K ⊆ e.source) (x : M) (hx : x ∈ K) :
    evaluate (ModuleCat.of ℤ ℤ) K x hx (n + 2) (fundamentalClass n e K hK hKs) =
      RelativeSingularHomology.chartLocalTopClass n e x (hKs hx) := by
  let c : RelativeSingularHomology.LocalHomology x (n + 2) :=
    evaluate (ModuleCat.of ℤ ℤ) K x hx (n + 2) (fundamentalClass n e K hK hKs)
  have hlocal : RelativeSingularHomology.partialHomeomorphEquiv e x (hKs hx) (n + 2) c =
      IntegralBallOrientation.pointClass E n (e x) := by
    have he := IntegralSupportTransport.evaluate_partialHomeomorphEquiv e hK.isClosed
      (image_compact e K hK hKs).isClosed hKs (image_subset_target e K hKs)
      (image_membership e K hKs) x hx (n + 2) (fundamentalClass n e K hK hKs)
    refine he.symm.trans ?_
    exact (congrArg (evaluate (ModuleCat.of ℤ ℤ) (e '' K) (e x)
      ((image_membership e K hKs x (hKs hx)).mp hx) (n + 2))
      ((supportEquiv n e K hK hKs).apply_symm_apply _)).trans
        (IntegralEuclideanOrientation.fundamentalClass_evaluate E n (e '' K)
          (image_compact e K hK hKs).isBounded (e x)
          ((image_membership e K hKs x (hKs hx)).mp hx))
  change c = RelativeSingularHomology.chartLocalTopClass n e x (hKs hx)
  apply (RelativeSingularHomology.chartLocalTopEquiv n e x (hKs hx)).injective
  rw [RelativeSingularHomology.chartLocalTopEquiv_class]
  change RelativeSingularHomology.localTopEquiv E n
    (RelativeSingularHomology.translateLocalEquiv E (e x) (n + 2)
      (RelativeSingularHomology.partialHomeomorphEquiv e x (hKs hx) (n + 2) c)) = 1
  rw [hlocal, IntegralBallOrientation.translate_pointClass,
    RelativeSingularHomology.localTopEquiv_class]

theorem exists_fundamentalClass (e : OpenPartialHomeomorph M E) (K : Set M)
    (hK : IsCompact K) (hKs : K ⊆ e.source) :
    ∃ a : Homology (ModuleCat.of ℤ ℤ) K (n + 2), ∀ (x : M) (hx : x ∈ K),
      evaluate (ModuleCat.of ℤ ℤ) K x hx (n + 2) a =
        RelativeSingularHomology.chartLocalTopClass n e x (hKs hx) :=
  ⟨fundamentalClass n e K hK hKs, fundamentalClass_evaluate n e K hK hKs⟩

end Wikipedia.HopfProblem.DegreeCollapse.IntegralChartOrientation
