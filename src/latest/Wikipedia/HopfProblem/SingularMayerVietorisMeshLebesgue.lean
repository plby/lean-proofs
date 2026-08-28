import Wikipedia.HopfProblem.FirstHurewiczSimplex
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Lebesgue numbers and eventual smallness for actual singular simplices

An open two-set cover of the image of an actual singular simplex pulls
back to an open cover of the compact standard simplex. The metric
Lebesgue number lemma gives a positive, uniform bound on the diameters
of all subsets lying over a single member of the cover.

The barycentric mesh factor `n/(n+1)` tends geometrically to zero under
iteration. Consequently every sufficiently small subsimplex lies over
one member of the cover. The bound is uniform over a finite family of
singular simplices, as needed for a finitely supported singular chain.
-/

noncomputable section

open Set Filter Topology

namespace Wikipedia.HopfProblem.SingularMayerVietoris

open FirstHurewicz

section CompactSource

variable {K X : Type*} [PseudoMetricSpace K] [CompactSpace K] [TopologicalSpace X]
variable (σ : C(K, X)) {U V : Set X}

/-- A genuine Lebesgue number for a continuous map from a compact metric
space, stated as a bound on every pair of points of an arbitrary subset. -/
theorem exists_lebesgue_number_two_pairwise (hU : IsOpen U) (hV : IsOpen V)
    (hcover : range σ ⊆ U ∪ V) :
    ∃ δ > 0, ∀ s : Set K, (∀ x ∈ s, ∀ y ∈ s, dist x y ≤ δ) →
      σ '' s ⊆ U ∨ σ '' s ⊆ V := by
  let W : Bool → Set K := fun b => if b then σ ⁻¹' U else σ ⁻¹' V
  have hW : ∀ b, IsOpen (W b) := by
    intro b
    cases b
    · exact hV.preimage σ.continuous
    · exact hU.preimage σ.continuous
  have hWcover : (univ : Set K) ⊆ ⋃ b, W b := by
    intro x _
    rcases hcover ⟨x, rfl⟩ with hx | hx
    · exact mem_iUnion.mpr ⟨true, hx⟩
    · exact mem_iUnion.mpr ⟨false, hx⟩
  obtain ⟨ε, hε, hball⟩ := lebesgue_number_lemma_of_metric isCompact_univ hW hWcover
  refine ⟨ε / 2, half_pos hε, ?_⟩
  intro s hdist
  by_cases hs : s.Nonempty
  · obtain ⟨x, hx⟩ := hs
    obtain ⟨b, hb⟩ := hball x (mem_univ x)
    have hsub : s ⊆ Metric.ball x ε := by
      intro y hy
      exact (hdist y hy x hx).trans_lt (half_lt_self hε)
    cases b
    · right
      rintro _ ⟨y, hy, rfl⟩
      exact hb (hsub hy)
    · left
      rintro _ ⟨y, hy, rfl⟩
      exact hb (hsub hy)
  · left
    rw [not_nonempty_iff_eq_empty.mp hs, image_empty]
    exact empty_subset _

/-- The same actual Lebesgue number criterion in terms of set diameter.
All subsets of the compact source are bounded, so the real diameter
controls every pairwise distance, including nonclosed subsets. -/
theorem exists_lebesgue_number_two (hU : IsOpen U) (hV : IsOpen V)
    (hcover : range σ ⊆ U ∪ V) :
    ∃ δ > 0, ∀ s : Set K, Metric.diam s ≤ δ → σ '' s ⊆ U ∨ σ '' s ⊆ V := by
  obtain ⟨δ, hδ, hsmall⟩ := exists_lebesgue_number_two_pairwise σ hU hV hcover
  refine ⟨δ, hδ, fun s hs => hsmall s ?_⟩
  intro x hx y hy
  exact (Metric.dist_le_diam_of_mem Metric.isBounded_of_compactSpace hx hy).trans hs

end CompactSource

/-- The exact geometric contraction factor for an `n`-simplex. -/
def meshFactor (n : ℕ) : ℝ := (n : ℝ) / ((n : ℝ) + 1)

theorem meshFactor_nonneg (n : ℕ) : 0 ≤ meshFactor n := by
  exact div_nonneg (Nat.cast_nonneg n) (by positivity)

theorem meshFactor_lt_one (n : ℕ) : meshFactor n < 1 := by
  apply (div_lt_one (by positivity : (0 : ℝ) < (n : ℝ) + 1)).mpr
  linarith

theorem meshFactor_le_one (n : ℕ) : meshFactor n ≤ 1 := (meshFactor_lt_one n).le

/-- Faces have no worse contraction factor than their containing simplex. -/
theorem meshFactor_mono : Monotone meshFactor := by
  intro n m hnm
  dsimp [meshFactor]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have hnm' : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
  nlinarith

theorem meshFactor_pow_tendsto (n : ℕ) :
    Tendsto (fun k : ℕ => meshFactor n ^ k) atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (meshFactor_nonneg n) (meshFactor_lt_one n)

theorem meshFactor_pow_mul_tendsto (n : ℕ) (D : ℝ) :
    Tendsto (fun k : ℕ => meshFactor n ^ k * D) atTop (𝓝 0) := by
  simpa only [zero_mul] using (meshFactor_pow_tendsto n).mul_const D

/-- Every fixed initial diameter eventually contracts below a prescribed
positive bound, and stays below it at every later subdivision stage. -/
theorem eventually_meshFactor_pow_mul_lt (n : ℕ) (D : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ k ≥ N, meshFactor n ^ k * D < δ := by
  apply eventually_atTop.mp
  exact (meshFactor_pow_mul_tendsto n D).eventually (eventually_lt_nhds hδ)

section Simplex

variable {X : Type*} [TopologicalSpace X] {U V : Set X} {n : ℕ}

/-- The Lebesgue number exists for the actual compact topological simplex. -/
theorem simplex_lebesgue_number_two (σ : C(Simplex n, X))
    (hU : IsOpen U) (hV : IsOpen V) (hcover : range σ ⊆ U ∪ V) :
    ∃ δ > 0, ∀ s : Set (Simplex n), Metric.diam s ≤ δ →
      σ '' s ⊆ U ∨ σ '' s ⊆ V :=
  exists_lebesgue_number_two σ hU hV hcover

/-- A single positive number works simultaneously for the images of all
continuous subsimplices, in every dimension. -/
theorem simplex_lebesgue_number_subsimplices (σ : C(Simplex n, X))
    (hU : IsOpen U) (hV : IsOpen V) (hcover : range σ ⊆ U ∪ V) :
    ∃ δ > 0, ∀ (m : ℕ) (f : C(Simplex m, Simplex n)), Metric.diam (range f) ≤ δ →
      range (σ.comp f) ⊆ U ∨ range (σ.comp f) ⊆ V := by
  obtain ⟨δ, hδ, hsmall⟩ := simplex_lebesgue_number_two σ hU hV hcover
  refine ⟨δ, hδ, ?_⟩
  intro m f hf
  simpa only [ContinuousMap.coe_comp, range_comp] using hsmall (range f) hf

/-- Genuine eventual smallness from the proven geometric contraction
bound. No Lebesgue number or smallness conclusion is assumed. -/
theorem simplex_eventually_small_of_diameter (σ : C(Simplex n, X))
    (hU : IsOpen U) (hV : IsOpen V) (hcover : range σ ⊆ U ∪ V) (D : ℝ) :
    ∃ N : ℕ, ∀ k ≥ N, ∀ (m : ℕ) (f : C(Simplex m, Simplex n)),
      Metric.diam (range f) ≤ meshFactor n ^ k * D →
        range (σ.comp f) ⊆ U ∨ range (σ.comp f) ⊆ V := by
  obtain ⟨δ, hδ, hsmall⟩ := simplex_lebesgue_number_subsimplices σ hU hV hcover
  obtain ⟨N, hN⟩ := eventually_meshFactor_pow_mul_lt n D hδ
  refine ⟨N, ?_⟩
  intro k hk m f hf
  exact hsmall m f (hf.trans (hN k hk).le)

/-- One stage works for every singular simplex in a finite support, and
for every later stage. This is the uniform version needed for actual chains. -/
theorem finite_family_eventually_small_of_diameter (s : Finset C(Simplex n, X))
    (hU : IsOpen U) (hV : IsOpen V) (hcover : ∀ σ ∈ s, range σ ⊆ U ∪ V) (D : ℝ) :
    ∃ N : ℕ, ∀ k ≥ N, ∀ σ ∈ s, ∀ (m : ℕ) (f : C(Simplex m, Simplex n)),
      Metric.diam (range f) ≤ meshFactor n ^ k * D →
        range (σ.comp f) ⊆ U ∨ range (σ.comp f) ⊆ V := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact ⟨0, fun _ _ _ hσ => False.elim (Finset.notMem_empty _ hσ)⟩
  | @insert σ s hσ ih =>
    obtain ⟨Nσ, hNσ⟩ := simplex_eventually_small_of_diameter σ hU hV
      (hcover σ (Finset.mem_insert_self σ s)) D
    obtain ⟨Ns, hNs⟩ := ih (fun τ hτ => hcover τ (Finset.mem_insert_of_mem hτ))
    refine ⟨max Nσ Ns, ?_⟩
    intro k hk τ hτ m f hf
    rcases Finset.mem_insert.mp hτ with rfl | hτ
    · exact hNσ k ((le_max_left _ _).trans hk) m f hf
    · exact hNs k ((le_max_right _ _).trans hk) τ hτ m f hf

end Simplex

end Wikipedia.HopfProblem.SingularMayerVietoris
