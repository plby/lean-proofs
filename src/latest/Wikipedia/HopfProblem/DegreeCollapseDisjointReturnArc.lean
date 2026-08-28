import Wikipedia.HopfProblem.DegreeCollapseReturnArcCleanEndpoints
import Wikipedia.SmoothSixDPoincare.OpenComplementAvoidance

/-!
# An embedded return arc disjoint from the original arc interior

Relative general position is applied inside the prescribed open target.
The obstacle is the full closed short arc, parametrized by its native open
interval of definition. Clean endpoint neighborhoods are fixed pointwise,
so both smooth continuation germs survive the perturbation.
-/

noncomputable section

open Set Function Filter ContinuousMap TopologicalSpace
open scoped ContDiff Manifold Topology
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {G H N : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  [FiniteDimensional ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H}
  [J.Boundaryless] [TopologicalSpace N] [ChartedSpace H N]
  [IsManifold J ∞ N] [T2Space N]

theorem exists_disjoint_embedded_return_arc (S : Opens N)
    {α : ℝ → N} {R r : ℝ} (hr : 0 < r) (hrR : r < R)
    (hα : ContMDiffOn 𝓘(ℝ, ℝ) J ∞ α (Ioo (-R) R))
    (hinj : InjOn α (Icc (-R) R))
    (hderiv : ∀ s ∈ Ioo (-R) R, Injective (mfderiv 𝓘(ℝ, ℝ) J α s))
    (hplus : α r ∈ S) (hminus : α (-r) ∈ S)
    (γ : Path (⟨α r, hplus⟩ : S) (⟨α (-r), hminus⟩ : S))
    (hdim : 3 ≤ Module.finrank ℝ G) :
    ∃ g : C(ℝ, S), ContMDiff 𝓘(ℝ, ℝ) J ∞ g ∧
      ((Subtype.val ∘ g) =ᶠ[𝓝 (0 : ℝ)] (fun t => α (t + r))) ∧
      ((Subtype.val ∘ g) =ᶠ[𝓝 (1 : ℝ)] (fun t => α (t + (-1 - r)))) ∧
      Topology.IsClosedEmbedding (fun t : unitInterval => g t) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, Injective (mfderiv 𝓘(ℝ, ℝ) J g t)) ∧
      ∀ t ∈ Ioo (0 : ℝ) 1, (g t : N) ∉ α '' Icc (-r) r := by
  obtain ⟨β, hβ, hβ0, hβ1, hemb, hβd⟩ :=
    exists_embedded_return_arc_inside_open S hr hrR hα hinj hderiv hplus hminus γ hdim
  obtain ⟨C, hC, hBC, hclean⟩ :=
    exists_clean_return_endpoint_neighborhood hr hrR hinj hβ0 hβ1
  let Q : Opens ℝ := ⟨Ioo (-R) R, isOpen_Ioo⟩
  let q : C(Q, N) := ⟨fun s => α s, continuous_iff_continuousAt.mpr (fun s =>
    (hα.continuousOn.continuousAt (isOpen_Ioo.mem_nhds s.property)).comp
      continuous_subtype_val.continuousAt)⟩
  have hq : ContMDiff 𝓘(ℝ, ℝ) J ∞ q := by
    intro s
    exact (hα.contMDiffAt (isOpen_Ioo.mem_nhds s.property)).comp s
      (contMDiff_subtype_val (n := ∞)).contMDiffAt
  let A : Set Q := {s | (s : ℝ) ∈ Icc (-r) r}
  have hsub : Icc (-r) r ⊆ Ioo (-R) R := fun s hs =>
    ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have himage : q '' A = α '' Icc (-r) r := by
    ext x
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨s, hs, rfl⟩
    · rintro ⟨s, hs, rfl⟩
      exact ⟨⟨s, hsub hs⟩, hs, rfl⟩
  have hclosed : IsClosed (q '' A) := by
    rw [himage]
    exact (isCompact_Icc.image_of_continuousOn (hα.continuousOn.mono hsub)).isClosed
  have hself : 2 * Module.finrank ℝ ℝ < Module.finrank ℝ G := by
    simp only [Module.finrank_self]
    omega
  have hobstacle : Module.finrank ℝ ℝ + Module.finrank ℝ ℝ < Module.finrank ℝ G := by
    simp only [Module.finrank_self]
    omega
  have hβinj : InjOn β (Icc (0 : ℝ) 1) := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (hemb.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hxy)
  have hclean' : ∀ t ∈ Icc (0 : ℝ) 1 ∩ C, t ∉ ({0, 1} : Set ℝ) →
      (β t : N) ∉ q '' A := by
    intro t ht htB
    rw [himage]
    exact hclean t ht htB
  obtain ⟨g, hg, hhom, hembg, hdg, -, havoid⟩ :=
    ManifoldImmersion.exists_embedded_image_avoidance_relative_neighborhood_in_open
      S β q A hβ hq hclosed hself hobstacle isCompact_Icc hC hBC hβinj hβd hclean'
      isOpen_univ (fun _ _ => mem_univ _)
  have h0C : C ∈ 𝓝 (0 : ℝ) := mem_interior_iff_mem_nhds.mp (hBC (Or.inl rfl))
  have h1C : C ∈ 𝓝 (1 : ℝ) := mem_interior_iff_mem_nhds.mp (hBC (Or.inr rfl))
  refine ⟨g, hg, ?_, ?_, hembg, hdg, ?_⟩
  · filter_upwards [h0C, hβ0] with t ht ht0
    exact (congrArg Subtype.val (hhom.fst_eq_snd ht)).symm.trans ht0
  · filter_upwards [h1C, hβ1] with t ht ht1
    exact (congrArg Subtype.val (hhom.fst_eq_snd ht)).symm.trans ht1
  · intro t ht hmem
    have htB : t ∉ ({0, 1} : Set ℝ) := by
      simp only [mem_insert_iff, mem_singleton_iff, not_or]
      exact ⟨ne_of_gt ht.1, ne_of_lt ht.2⟩
    exact havoid t ⟨⟨ht.1.le, ht.2.le⟩, htB⟩ (himage.symm ▸ hmem)

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
