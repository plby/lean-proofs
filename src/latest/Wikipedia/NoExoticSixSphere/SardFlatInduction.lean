import Wikipedia.NoExoticSixSphere.SardFlatStratumSlice
import Wikipedia.NoExoticSixSphere.SardFlatNull

/-!
# The finite vanishing strata under dimension induction

Second countability turns local null-image statements into a global one.
Applying this to the constructed hypersurface slices proves the finite
vanishing-stratum step from the explicitly stated lower-dimensional Sard
induction hypothesis. The induction itself is not asserted here.
-/

open scoped ContDiff Topology
open Set Filter Module MeasureTheory MeasureTheory.Measure TopologicalSpace

namespace NoExoticSixSphere.Sard

theorem measure_image_eq_zero_of_local {X Y : Type*} [TopologicalSpace X]
    [SecondCountableTopology X] [MeasurableSpace Y] (μ : Measure Y) (f : X → Y) (s : Set X)
    (h : ∀ x ∈ s, ∃ t ∈ 𝓝[s] x, μ (f '' t) = 0) : μ (f '' s) = 0 := by
  choose! t ht hzero using h
  obtain ⟨a, has, hac, hcover⟩ := countable_cover_nhdsWithin ht
  apply measure_mono_null (image_mono hcover)
  rw [image_iUnion₂]
  exact (measure_biUnion_null_iff hac).mpr (fun x hx ↦ hzero x (has hx))

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [Nontrivial F] [MeasurableSpace F]

theorem measure_image_flat_difference_of_lowerDimension (μ : Measure F)
    (hSard : ∀ (g : EuclideanSpace ℝ (Fin (finrank ℝ E - 1)) → F)
      (V : Set (EuclideanSpace ℝ (Fin (finrank ℝ E - 1)))),
      IsOpen V → ContDiffOn ℝ ∞ g V →
        μ (g '' {z | z ∈ V ∧ ¬ Function.Surjective (fderiv ℝ g z)}) = 0)
    {f : E → F} {U : Set E} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    {k : ℕ} (hk : 1 ≤ k) :
    μ (f '' ((U ∩ flatPoints f k) \ flatPoints f (k + 1))) = 0 := by
  let s := (U ∩ flatPoints f k) \ flatPoints f (k + 1)
  apply measure_image_eq_zero_of_local μ f s
  intro x hx
  obtain ⟨W, hW, hxW, _, V, g, hV, hg, himage⟩ :=
    exists_flatStratumSlice hU hf hk hx.1.1 hx.1.2 hx.2
  refine ⟨s ∩ W, inter_mem self_mem_nhdsWithin
    (mem_nhdsWithin_of_mem_nhds (hW.mem_nhds hxW)), ?_⟩
  apply measure_mono_null _ (hSard g V hV hg)
  apply Subset.trans _ himage
  exact image_mono (fun _ hy ↦ ⟨hy.2, hy.1.1.2⟩)

theorem measure_image_zero_derivative_of_lowerDimension [FiniteDimensional ℝ F] [BorelSpace F]
    (μ : Measure F) [IsAddHaarMeasure μ]
    (hSard : ∀ (g : EuclideanSpace ℝ (Fin (finrank ℝ E - 1)) → F)
      (V : Set (EuclideanSpace ℝ (Fin (finrank ℝ E - 1)))),
      IsOpen V → ContDiffOn ℝ ∞ g V →
        μ (g '' {z | z ∈ V ∧ ¬ Function.Surjective (fderiv ℝ g z)}) = 0)
    {f : E → F} {U : Set E} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) :
    μ (f '' {x | x ∈ U ∧ fderiv ℝ f x = 0}) = 0 := by
  change μ (f '' (U ∩ {x | fderiv ℝ f x = 0})) = 0
  rw [← flatPoints_one]
  have hstep : ∀ k : ℕ, 1 ≤ k → μ (f '' (U ∩ flatPoints f (k + 1))) = 0 →
      μ (f '' (U ∩ flatPoints f k)) = 0 := by
    intro k hk hn
    have hd := measure_image_flat_difference_of_lowerDimension μ hSard hU hf hk
    apply measure_mono_null _ (measure_union_null hd hn)
    rintro _ ⟨x, hx, rfl⟩
    by_cases hx' : x ∈ flatPoints f (k + 1)
    · exact Or.inr ⟨x, ⟨hx.1, hx'⟩, rfl⟩
    · exact Or.inl ⟨x, ⟨hx, hx'⟩, rfl⟩
  have hdown : ∀ j : ℕ, μ (f '' (U ∩ flatPoints f (j + 1))) = 0 →
      μ (f '' (U ∩ flatPoints f 1)) = 0 := by
    intro j
    induction j with
    | zero => exact id
    | succ j ih => exact fun h ↦ ih (hstep (j + 1) (by omega) h)
  apply hdown (finrank ℝ E)
  apply measure_image_flatPoints_eq_zero μ hU hf (finrank ℝ E + 1)
  have hpos : 0 < finrank ℝ F := Module.finrank_pos
  have hp : finrank ℝ E + 2 ≤ (finrank ℝ E + 2) * finrank ℝ F := by
    simpa using Nat.mul_le_mul_left (finrank ℝ E + 2) (Nat.succ_le_of_lt hpos)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using
    (lt_of_lt_of_le (by omega : finrank ℝ E < finrank ℝ E + 2) hp)

end NoExoticSixSphere.Sard
