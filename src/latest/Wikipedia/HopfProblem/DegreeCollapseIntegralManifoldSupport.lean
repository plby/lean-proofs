import Wikipedia.HopfProblem.DegreeCollapseIntegralCompactSupport
import Wikipedia.HopfProblem.DegreeCollapseIntegralChartFundamentalClass
import Wikipedia.NoExoticSixSphere.LocalFundamentalNeighborhood

/-!
# Integral local detection on arbitrary compact manifold supports

The actual chart equivalence transports the proved Euclidean detection
and dimension bounds. A finite cover by compact chart neighborhoods and
the integral closed-union sequence prove these properties on every compact
subset of the original manifold. No orientability assumption is needed
for detection or above-dimensional vanishing; no global fundamental class
is concluded from these properties alone.
-/

noncomputable section

open Set Filter
open scoped Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralCompactSupport

open NoExoticSixSphere SupportedRelativeHomology

variable {M N : Type} [TopologicalSpace M] [TopologicalSpace N] [T2Space M] [T2Space N]

theorem Properties.of_partialHomeomorph (d : ℕ) (e : OpenPartialHomeomorph M N)
    {K : Set M} {L : Set N} (hK : IsCompact K)
    (hKs : K ⊆ e.source) (hLt : L ⊆ e.target)
    (hKL : ∀ x ∈ e.source, x ∈ K ↔ e x ∈ L) (hL : Properties d L) : Properties d K where
  compact := hK
  above k hk := by
    let := hL.above k hk
    exact (IntegralSupportTransport.partialHomeomorphEquiv e hK.isClosed hL.compact.isClosed
      hKs hLt hKL k).injective.subsingleton
  detected a b hab := by
    apply (IntegralSupportTransport.partialHomeomorphEquiv e hK.isClosed hL.compact.isClosed
      hKs hLt hKL d).injective
    apply hL.detected
    intro y hy
    have hpre : ∃ x : M, x ∈ K ∧ e x = y := by
      refine ⟨e.symm y, ?_, e.right_inv (hLt hy)⟩
      apply (hKL (e.symm y) (e.map_target (hLt hy))).mpr
      exact (e.right_inv (hLt hy)).symm ▸ hy
    obtain ⟨x, hx, rfl⟩ := hpre
    have ha := IntegralSupportTransport.evaluate_partialHomeomorphEquiv e
      hK.isClosed hL.compact.isClosed hKs hLt hKL x hx d a
    have hb := IntegralSupportTransport.evaluate_partialHomeomorphEquiv e
      hK.isClosed hL.compact.isClosed hKs hLt hKL x hx d b
    exact ha.trans ((congrArg (RelativeSingularHomology.partialHomeomorphEquiv e x (hKs hx) d)
      (hab x hx)).trans hb.symm)

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (n : ℕ) [Fact (Module.finrank ℝ E = (n + 1) + 1)]

theorem compact_chart_properties (e : OpenPartialHomeomorph M E)
    (K : Set M) (hK : IsCompact K) (hKs : K ⊆ e.source) : Properties (n + 2) K :=
  Properties.of_partialHomeomorph (n + 2) e hK hKs
    (IntegralChartOrientation.image_subset_target e K hKs)
    (IntegralChartOrientation.image_membership e K hKs)
    (compactEuclidean_properties n (e '' K) (IntegralChartOrientation.image_compact e K hK hKs))

theorem finiteUnion_compactChart {ι : Type*} (s : Finset ι)
    (e : ι → OpenPartialHomeomorph M E) (K : ι → Set M)
    (hK : ∀ i ∈ s, IsCompact (K i)) (hS : ∀ i ∈ s, K i ⊆ (e i).source) :
    Properties (n + 2) (⋃ i ∈ s, K i) := by
  classical
  induction s using Finset.induction_on generalizing K with
  | empty => simpa using (Properties.empty (M := M) (n + 2))
  | @insert i s hi ih =>
    have hKi := hK i (Finset.mem_insert_self i s)
    have hSi := hS i (Finset.mem_insert_self i s)
    have hsmallK : ∀ j ∈ s, IsCompact (K j) := fun j hj => hK j (Finset.mem_insert_of_mem hj)
    have hsmallS : ∀ j ∈ s, K j ⊆ (e j).source := fun j hj => hS j (Finset.mem_insert_of_mem hj)
    have hleft := compact_chart_properties n (e i) (K i) hKi hSi
    have hright := ih K hsmallK hsmallS
    have hinter := ih (fun j => K i ∩ K j)
      (fun j hj => hKi.inter_right (hsmallK j hj).isClosed)
      (fun j hj => Set.inter_subset_right.trans (hsmallS j hj))
    have hinter' : Properties (n + 2) (K i ∩ (⋃ j ∈ s, K j)) := by
      simpa only [Set.inter_iUnion] using hinter
    simpa only [Finset.mem_insert, Set.iUnion_iUnion_eq_or_left] using
      (Properties.union (n + 2) hleft hright hinter')

variable [ChartedSpace E M]

include E in
/-- Actual integral detection and dimension bounds hold on every original compact support. -/
theorem compactManifold_properties (K : Set M) (hK : IsCompact K) : Properties (n + 2) K := by
  classical
  let e (x : K) := chartAt E (x : M)
  have hballs : ∀ x : K, ∃ B : Set M,
      IsCompact B ∧ (x : M) ∈ interior B ∧ B ⊆ (e x).source := by
    intro x
    have hx : (x : M) ∈ (e x).source := mem_chart_source E (x : M)
    obtain ⟨R, hR, hB, _⟩ := ChartClosedBall.exists_support_subset (e x) x hx univ univ_mem
    refine ⟨ChartClosedBall.support (e x) (e x x) R,
      ChartClosedBall.support_isCompact (e x) (e x x) R hB, ?_,
      ChartClosedBall.support_subset_source (e x) (e x x) R hB⟩
    exact mem_interior_iff_mem_nhds.mpr (ChartClosedBall.support_mem_nhds (e x) x hx R hR hB)
  choose B hB hxB hBS using hballs
  have hcover : K ⊆ ⋃ x : K, interior (B x) := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, hxB ⟨x, hx⟩⟩
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover (fun x : K => interior (B x))
    (fun _ => isOpen_interior) hcover
  have h := finiteUnion_compactChart n s e (fun x => K ∩ B x)
    (fun x _ => hK.inter_right (hB x).isClosed)
    (fun x _ => inter_subset_right.trans (hBS x))
  have he : (⋃ x ∈ s, K ∩ B x) = K := by
    apply Subset.antisymm
    · intro y hy
      obtain ⟨x, _, hx⟩ := mem_iUnion₂.mp hy
      exact hx.1
    · intro y hy
      obtain ⟨x, hx, hyB⟩ := mem_iUnion₂.mp (hs hy)
      exact mem_iUnion₂.mpr ⟨x, hx, hy, interior_subset hyB⟩
  simpa only [he] using h

include E in
theorem compactManifold_above_subsingleton (K : Set M) (hK : IsCompact K)
    (k : ℕ) (hk : n + 2 < k) : Subsingleton (Homology (ModuleCat.of ℤ ℤ) K k) :=
  (compactManifold_properties (E := E) n K hK).above k hk

include E in
theorem compactManifold_detected (K : Set M) (hK : IsCompact K)
    (a b : Homology (ModuleCat.of ℤ ℤ) K (n + 2))
    (hab : ∀ (x : M) (hx : x ∈ K), evaluate (ModuleCat.of ℤ ℤ) K x hx (n + 2) a =
      evaluate (ModuleCat.of ℤ ℤ) K x hx (n + 2) b) : a = b :=
  (compactManifold_properties (E := E) n K hK).detected a b hab

end Wikipedia.HopfProblem.DegreeCollapse.IntegralCompactSupport
