import Wikipedia.HopfProblem.RiemannMappingNormalFamily
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Sequences

/-!
# Compact convergence for bounded holomorphic families

This is the finite-dimensional normal-family compactness argument for
coordinate maps of genuine holomorphic automorphisms. The topology is
uniform convergence on compact subsets of the actual open domain.
Arzelà–Ascoli applies because the complex Schwarz estimate proves local
equicontinuity and bounded subsets of the target have compact closure.
-/

noncomputable section

open Set Metric Function Filter Complex
open scoped Topology Uniformity UniformConvergence

namespace Wikipedia.HopfProblem.HolomorphicAutomorphismNormalFamily

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]

/-- Compact subsets of the open coordinate domain. -/
def compactSubsets (U : Set E) : Set (Set E) := {K | K ⊆ U ∧ IsCompact K}

/-- Functions with the topology of uniform convergence on compact subsets. -/
abbrev FunctionSpace (U : Set E) (F : Type*) [UniformSpace F] :=
  E →ᵤ[compactSubsets U] F

/-- The underlying function of a point in the compact-convergence space. -/
def evaluation {U : Set E} (f : FunctionSpace U F) : E → F :=
  UniformOnFun.toFun (compactSubsets U) f

@[simp] theorem evaluation_ofFun {U : Set E} (f : E → F) :
    evaluation (UniformOnFun.ofFun (compactSubsets U) f) = f := rfl

variable [NormedSpace ℂ E]

/-- Compact convergence on a finite-dimensional open domain is first countable
at the level of its uniformity, including domains that are not relatively compact. -/
theorem uniformity_isCountablyGenerated [FiniteDimensional ℂ E]
    {U : Set E} (hU : IsOpen U) :
    (𝓤 (FunctionSpace U F)).IsCountablyGenerated := by
  have := hU.locallyCompactSpace
  have : SigmaCompactSpace U := sigmaCompactSpace_of_locallyCompact_secondCountable
  let φ : CompactExhaustion U := default
  apply UniformOnFun.isCountablyGenerated_uniformity (t := fun n => (↑) '' φ n)
  · intro n
    exact ⟨image_val_subset, (φ.isCompact n).image continuous_subtype_val⟩
  · exact monotone_image.comp φ.subset
  · rintro K ⟨hKU, hKc⟩
    lift K to Set U using hKU
    rw [← Subtype.isCompact_iff] at hKc
    exact (φ.exists_superset_of_isCompact hKc).imp fun n hn => by gcongr

/-- Convergence in this function space is exactly locally uniform convergence
on the coordinate domain. -/
theorem tendsto_iff_tendstoLocallyUniformlyOn [FiniteDimensional ℂ E]
    {U : Set E} (hU : IsOpen U) {ι : Type*} {φ : Filter ι}
    {f : ι → FunctionSpace U F} {g : FunctionSpace U F} :
    Tendsto f φ (𝓝 g) ↔
      TendstoLocallyUniformlyOn (fun i => evaluation (f i)) (evaluation g) φ U := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hU,
    UniformOnFun.tendsto_iff_tendstoUniformlyOn]
  constructor
  · intro h K hKU hKc
    exact h K ⟨hKU, hKc⟩
  · intro h K hK
    exact h K hK.1 hK.2

/-- Approaching a point through a family means locally uniform convergence
of the corresponding functions, including a general closure-point filter. -/
theorem evaluation_tendstoLocallyUniformlyOn [FiniteDimensional ℂ E]
    {U : Set E} (hU : IsOpen U)
    {f : FunctionSpace U F} {s : Set (FunctionSpace U F)} :
    TendstoLocallyUniformlyOn evaluation (evaluation f) (𝓝[s] f) U := by
  exact (tendsto_iff_tendstoLocallyUniformlyOn hU).mp
    (tendsto_id'.mpr nhdsWithin_le_nhds)

variable [NormedSpace ℂ F]

/-- The actual closure of a bounded holomorphic family is compact. -/
theorem isCompact_closure_of_bounded_holomorphic [FiniteDimensional ℂ F]
    {U : Set E} (hU : IsOpen U) {s : Set (FunctionSpace U F)}
    (hsd : ∀ f ∈ s, DifferentiableOn ℂ (evaluation f) U)
    (hsb : ∃ C : ℝ, ∀ f ∈ s, ∀ z ∈ U, ‖evaluation f z‖ ≤ C) :
    IsCompact (closure s) := by
  obtain ⟨C, hC⟩ := hsb
  apply ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
    (𝔖 := compactSubsets U) (fun K hK => hK.2) (F := evaluation) .id
  · rintro K ⟨hKU, _⟩ z hz
    exact (RiemannMapping.equicontinuousAt_of_forall_norm_le (hU.mem_nhds (hKU hz))
      (fun f : s => hsd f.val f.property)
      ⟨C, fun f z hz => hC f.val f.property z hz⟩).equicontinuousWithinAt K
  · intro K hK x hx
    exact ⟨closedBall 0 C, isCompact_closedBall _ _, fun f hf => by
      simpa only [mem_closedBall_zero_iff] using hC f hf x (hK.1 hx)⟩

omit [NormedSpace ℂ F] in
/-- A uniform bound on the domain is preserved at every compact-convergence
closure point, without any restriction on values outside the domain. -/
theorem norm_le_of_mem_closure [FiniteDimensional ℂ E]
    {U : Set E} (hU : IsOpen U) {s : Set (FunctionSpace U F)} {C : ℝ}
    (hs : ∀ f ∈ s, ∀ z ∈ U, ‖evaluation f z‖ ≤ C)
    {f : FunctionSpace U F} (hf : f ∈ closure s) :
    ∀ z ∈ U, ‖evaluation f z‖ ≤ C := by
  let : (𝓝[s] f).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hf
  intro z hz
  exact le_of_tendsto ((evaluation_tendstoLocallyUniformlyOn hU).tendsto_at hz).norm
    (eventually_mem_nhdsWithin.mono fun g hg => hs g hg z hz)

/-- Every bounded holomorphic sequence has a strictly increasing subsequence
converging locally uniformly to an actual function. Holomorphicity of this
limit is proved in the accompanying multivariable limit theorem. -/
theorem exists_subseq_compact_convergence [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]
    {U : Set E} (hU : IsOpen U) (f : ℕ → E → F)
    (hfd : ∀ n, DifferentiableOn ℂ (f n) U) {C : ℝ}
    (hfb : ∀ n, ∀ z ∈ U, ‖f n z‖ ≤ C) :
    ∃ (g : E → F) (φ : ℕ → ℕ), StrictMono φ ∧
      TendstoLocallyUniformlyOn (fun n => f (φ n)) g atTop U ∧
      ∀ z ∈ U, ‖g z‖ ≤ C := by
  let := uniformity_isCountablyGenerated (F := F) hU
  let f' : ℕ → FunctionSpace U F := fun n =>
    UniformOnFun.ofFun (compactSubsets U) (f n)
  have hd : ∀ g ∈ range f', DifferentiableOn ℂ (evaluation g) U := by
    rintro _ ⟨n, rfl⟩
    exact hfd n
  have hb : ∀ g ∈ range f', ∀ z ∈ U, ‖evaluation g z‖ ≤ C := by
    rintro _ ⟨n, rfl⟩ z hz
    exact hfb n z hz
  have hc := isCompact_closure_of_bounded_holomorphic hU hd ⟨C, hb⟩
  obtain ⟨g, hg, φ, hφ, hconv⟩ := hc.tendsto_subseq
    (fun n => subset_closure (mem_range_self n))
  refine ⟨evaluation g, φ, hφ, ?_, norm_le_of_mem_closure hU hb hg⟩
  exact (tendsto_iff_tendstoLocallyUniformlyOn hU).mp hconv

end Wikipedia.HopfProblem.HolomorphicAutomorphismNormalFamily
