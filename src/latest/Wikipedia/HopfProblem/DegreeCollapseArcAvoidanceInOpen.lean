import Wikipedia.SmoothSixDPoincare.CleanNeighborhoodAvoidance
import Wikipedia.SmoothSixDPoincare.NativeArcEndpointGerms

/-!
# Disjoining two source arcs while preserving a prescribed open region

The second arc is perturbed away from the entire compact first arc, not
merely from finitely many sampled points. Its endpoint germs and an open
image constraint are preserved. The latter retains avoidance of all other
double-point preimages when used on an immersed sphere.
-/

noncomputable section

open Set Function Filter Metric Topology
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.ImmersedSource

open Wikipedia.SmoothSixDPoincare

variable {E H N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [TopologicalSpace N] [ChartedSpace H N]
  [IsManifold I ∞ N] [T2Space N]

theorem exists_arc_disjoint_in_open (a b : C(ℝ, N))
    (ha : ContMDiff 𝓘(ℝ, ℝ) I ∞ a) (hb : ContMDiff 𝓘(ℝ, ℝ) I ∞ b)
    (hdim : 3 ≤ Module.finrank ℝ E)
    (hemb : IsClosedEmbedding (fun t : unitInterval => b t))
    (hi : ∀ t ∈ Icc (0 : ℝ) 1, Injective (mfderiv 𝓘(ℝ, ℝ) I b t))
    (h0 : b 0 ∉ a '' Icc (0 : ℝ) 1) (h1 : b 1 ∉ a '' Icc (0 : ℝ) 1)
    {O : Set N} (hO : IsOpen O) (hmaps : MapsTo b (Icc (0 : ℝ) 1) O) :
    ∃ c : C(ℝ, N), ContMDiff 𝓘(ℝ, ℝ) I ∞ c ∧
      (c =ᶠ[𝓝 (0 : ℝ)] b) ∧ (c =ᶠ[𝓝 (1 : ℝ)] b) ∧
      IsClosedEmbedding (fun t : unitInterval => c t) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, Injective (mfderiv 𝓘(ℝ, ℝ) I c t)) ∧
      MapsTo c (Icc (0 : ℝ) 1) O ∧
      Disjoint (c '' Icc (0 : ℝ) 1) (a '' Icc (0 : ℝ) 1) := by
  have hclosed : IsClosed (a '' Icc (0 : ℝ) 1) := (isCompact_Icc.image a.continuous).isClosed
  have hnear0 : ∀ᶠ t in 𝓝 (0 : ℝ), b t ∉ a '' Icc (0 : ℝ) 1 :=
    (hclosed.isOpen_compl.preimage b.continuous).mem_nhds h0
  have hnear1 : ∀ᶠ t in 𝓝 (1 : ℝ), b t ∉ a '' Icc (0 : ℝ) 1 :=
    (hclosed.isOpen_compl.preimage b.continuous).mem_nhds h1
  obtain ⟨r, hr, hball0⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hnear0
  obtain ⟨s, hs, hball1⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hnear1
  let C : Set ℝ := closedBall 0 r ∪ closedBall 1 s
  have hC : IsClosed C := isClosed_closedBall.union isClosed_closedBall
  have h0C : C ∈ 𝓝 (0 : ℝ) := mem_of_superset (ball_mem_nhds 0 hr)
    (fun _ ht => Or.inl (ball_subset_closedBall ht))
  have h1C : C ∈ 𝓝 (1 : ℝ) := mem_of_superset (ball_mem_nhds 1 hs)
    (fun _ ht => Or.inr (ball_subset_closedBall ht))
  have hinj : InjOn b (Icc (0 : ℝ) 1) := by
    intro x hx y hy he
    exact congrArg Subtype.val (hemb.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) he)
  have hclean : ∀ t ∈ Icc (0 : ℝ) 1 ∩ C, t ∉ (∅ : Set ℝ) →
      b t ∉ a '' Icc (0 : ℝ) 1 := by
    intro t ht _
    rcases ht.2 with ht0 | ht1
    · exact hball0 ht0
    · exact hball1 ht1
  have hdim' : 2 * Module.finrank ℝ ℝ < Module.finrank ℝ E := by
    simp only [Module.finrank_self]
    omega
  have hob : Module.finrank ℝ ℝ + Module.finrank ℝ ℝ < Module.finrank ℝ E := by
    simp only [Module.finrank_self]
    omega
  obtain ⟨c, hc, H, hec, hic, hmaps', havoid⟩ :=
    ManifoldImmersion.exists_embedded_image_avoidance_relative_neighborhood b a (Icc (0 : ℝ) 1)
      hb ha hclosed hdim' hob isCompact_Icc hC (empty_subset _) hinj hi hclean hO hmaps
  refine ⟨c, hc, ?_, ?_, hec, hic, hmaps', ?_⟩
  · filter_upwards [h0C] with t ht
    exact (H.fst_eq_snd ht).symm
  · filter_upwards [h1C] with t ht
    exact (H.fst_eq_snd ht).symm
  · rw [Set.disjoint_left]
    rintro z ⟨t, ht, rfl⟩ hz
    exact havoid t ⟨ht, notMem_empty t⟩ hz

end Wikipedia.HopfProblem.DegreeCollapse.ImmersedSource
