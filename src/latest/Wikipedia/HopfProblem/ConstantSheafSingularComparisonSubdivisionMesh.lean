import Wikipedia.HopfProblem.SingularMayerVietorisMeshSubdivision

/-!
# Actual barycentric subdivision for arbitrary open covers

An arbitrary open cover of the image of a singular simplex has a positive
Lebesgue number after pullback to the compact standard simplex.  The
previously proved geometric mesh estimate therefore makes every term of
every sufficiently iterated formal subdivision subordinate to the cover.
The cover is not required to be finite.  Only the family of input singular
simplices is finite in the uniform version.
-/

noncomputable section

open Set

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison

open FirstHurewicz SingularMayerVietoris

section CompactSource

variable {K X : Type*} {ι : Sort*}
variable [PseudoMetricSpace K] [CompactSpace K] [Nonempty K] [TopologicalSpace X]
variable (U : ι → Set X) (σ : C(K, X))

/-- A Lebesgue number for an arbitrary open cover of the image of an actual
continuous map from a nonempty compact metric space.  Nonemptiness of the
source also supplies a cover member when the tested subset is empty. -/
theorem exists_lebesgue_number_pairwise (hU : ∀ i, IsOpen (U i))
    (hcover : range σ ⊆ ⋃ i, U i) :
    ∃ δ > 0, ∀ s : Set K, (∀ x ∈ s, ∀ y ∈ s, dist x y ≤ δ) →
      ∃ i, σ '' s ⊆ U i := by
  let W : ι → Set K := fun i => σ ⁻¹' U i
  have hW : ∀ i, IsOpen (W i) := fun i => (hU i).preimage σ.continuous
  have hWcover : (univ : Set K) ⊆ ⋃ i, W i := by
    intro x _
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover (mem_range_self x))
    exact mem_iUnion.mpr ⟨i, hi⟩
  obtain ⟨ε, hε, hball⟩ := lebesgue_number_lemma_of_metric isCompact_univ hW hWcover
  refine ⟨ε / 2, half_pos hε, ?_⟩
  intro s hdist
  by_cases hs : s.Nonempty
  · obtain ⟨x, hx⟩ := hs
    obtain ⟨i, hi⟩ := hball x (mem_univ x)
    refine ⟨i, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact hi ((hdist y hy x hx).trans_lt (half_lt_self hε))
  · obtain ⟨x⟩ := ‹Nonempty K›
    obtain ⟨i, _⟩ := hball x (mem_univ x)
    refine ⟨i, ?_⟩
    rw [not_nonempty_iff_eq_empty.mp hs, image_empty]
    exact empty_subset _

/-- The arbitrary-cover Lebesgue criterion in terms of the diameter of
the full subset, using boundedness of every subset of the compact source. -/
theorem exists_lebesgue_number (hU : ∀ i, IsOpen (U i))
    (hcover : range σ ⊆ ⋃ i, U i) :
    ∃ δ > 0, ∀ s : Set K, Metric.diam s ≤ δ → ∃ i, σ '' s ⊆ U i := by
  obtain ⟨δ, hδ, hsmall⟩ := exists_lebesgue_number_pairwise U σ hU hcover
  refine ⟨δ, hδ, fun s hs => hsmall s ?_⟩
  intro x hx y hy
  exact (Metric.dist_le_diam_of_mem Metric.isBounded_of_compactSpace hx hy).trans hs

end CompactSource

section Simplex

variable {X : Type*} {ι : Sort*} [TopologicalSpace X] {p : ℕ}
variable (U : ι → Set X)

/-- One positive diameter bound works for every continuous subsimplex,
in every dimension, of a given actual singular simplex. -/
theorem simplex_lebesgue_number_subsimplices (σ : C(Simplex p, X))
    (hU : ∀ i, IsOpen (U i)) (hcover : range σ ⊆ ⋃ i, U i) :
    ∃ δ > 0, ∀ (m : ℕ) (f : C(Simplex m, Simplex p)),
      Metric.diam (range f) ≤ δ → ∃ i, range (σ.comp f) ⊆ U i := by
  obtain ⟨δ, hδ, hsmall⟩ := exists_lebesgue_number U σ hU hcover
  refine ⟨δ, hδ, ?_⟩
  intro m f hf
  simpa only [ContinuousMap.coe_comp, range_comp] using hsmall (range f) hf

/-- Geometric contraction eventually makes every subsimplex subordinate
to an arbitrary open cover, with no assumed Lebesgue number. -/
theorem simplex_eventually_small_of_diameter (σ : C(Simplex p, X))
    (hU : ∀ i, IsOpen (U i)) (hcover : range σ ⊆ ⋃ i, U i) (D : ℝ) :
    ∃ N : ℕ, ∀ k ≥ N, ∀ (m : ℕ) (f : C(Simplex m, Simplex p)),
      Metric.diam (range f) ≤ meshFactor p ^ k * D →
        ∃ i, range (σ.comp f) ⊆ U i := by
  obtain ⟨δ, hδ, hsmall⟩ := simplex_lebesgue_number_subsimplices U σ hU hcover
  obtain ⟨N, hN⟩ := eventually_meshFactor_pow_mul_lt p D hδ
  refine ⟨N, ?_⟩
  intro k hk m f hf
  exact hsmall m f (hf.trans (hN k hk).le)

/-- Every nonzero term of every sufficiently iterated actual formal
subdivision lies over one member of the arbitrary open cover.  The stage
is uniform over all formal chains in this standard simplex. -/
theorem simplex_formalSubdivision_eventually_small (σ : C(Simplex p, X))
    (hU : ∀ i, IsOpen (U i)) (hcover : range σ ⊆ ⋃ i, U i) :
    ∃ N : ℕ, ∀ k ≥ N, ∀ c : FormalChains (Simplex p) (p + 1),
      ∀ w ∈ ((formalSubdivision (fun _ v => simplexBarycenter v) (p + 1))^[k] c).support,
        ∃ i, range (σ.comp (affineSimplex w)) ⊆ U i := by
  obtain ⟨N, hN⟩ := simplex_eventually_small_of_diameter U σ hU hcover 1
  refine ⟨N, ?_⟩
  intro k hk c w hw
  apply hN k hk p (affineSimplex w)
  simpa only [mul_one] using simplex_formalSubdivision_iterate_diam k c w hw

/-- A finite family of actual singular simplices admits one subdivision
stage, valid at every later stage, for an arbitrary open cover. -/
theorem finite_family_formalSubdivision_eventually_small (s : Finset C(Simplex p, X))
    (hU : ∀ i, IsOpen (U i)) (hcover : ∀ σ ∈ s, range σ ⊆ ⋃ i, U i) :
    ∃ N : ℕ, ∀ k ≥ N, ∀ σ ∈ s, ∀ c : FormalChains (Simplex p) (p + 1),
      ∀ w ∈ ((formalSubdivision (fun _ v => simplexBarycenter v) (p + 1))^[k] c).support,
        ∃ i, range (σ.comp (affineSimplex w)) ⊆ U i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact ⟨0, fun _ _ _ hσ => False.elim (Finset.notMem_empty _ hσ)⟩
  | @insert σ s hσ ih =>
    obtain ⟨Nσ, hNσ⟩ := simplex_formalSubdivision_eventually_small U σ hU
      (hcover σ (Finset.mem_insert_self σ s))
    obtain ⟨Ns, hNs⟩ := ih (fun τ hτ => hcover τ (Finset.mem_insert_of_mem hτ))
    refine ⟨max Nσ Ns, ?_⟩
    intro k hk τ hτ c w hw
    rcases Finset.mem_insert.mp hτ with rfl | hτ
    · exact hNσ k ((le_max_left _ _).trans hk) c w hw
    · exact hNs k ((le_max_right _ _).trans hk) τ hτ c w hw

end Simplex

end Wikipedia.HopfProblem.ConstantSheafSingularComparison
