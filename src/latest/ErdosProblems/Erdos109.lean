/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 109.
https://www.erdosproblems.com/forum/thread/109

Informal authors:
- Joel Moreira
- Florian K. Richter
- Donald Robertson

Statement authors:
- Formal Conjectures authors

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos109.md
- https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/109.lean
-/
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Integral
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unitary
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.MeanErgodic
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.RCLike.ContinuousMap
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Combinatorics.Hindman
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Dynamics.Ergodic.Extreme
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.Intersectivity
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Topology.Compactification.StoneCech
import Mathlib.Topology.Clopen
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.MetricSpace.IsometricSMul
import Mathlib.Topology.MetricSpace.UniformConvergence
import Util.Density

/-!
# Erdős Problem 109

Every set of natural numbers of positive upper density contains `B + C` for
two infinite sets `B` and `C`.

The proof follows Moreira--Richter--Robertson.  The first part of this file
isolates their purely combinatorial rectangle extraction.  The analytic
correlation theorem is developed below it.
-/

open CompactlySupported Filter Function Set
open scoped BoundedContinuousFunction ENNReal NNReal Pointwise Topology
open MeasureTheory ProbabilityTheory

namespace Erdos109

/-! ## Realizing upper density on growing prefixes -/

/-- A bounded sequence of prefix densities has a subsequence converging to
its limsup, and the selected prefix lengths tend to infinity.  We discard a
finite initial segment so that every selected prefix is nonempty. -/
theorem exists_prefix_realizing_upperDensity (A : Set ℕ) :
    ∃ N : ℕ → ℕ,
      Tendsto (fun k => A.partialDensity Set.univ (N k)) atTop
        (𝓝 A.upperDensity) ∧
      Tendsto N atTop atTop ∧ ∀ k, 0 < N k := by
  have hlow : IsCoboundedUnder (· ≤ ·) atTop
      (fun n : ℕ => A.partialDensity Set.univ n) :=
    isCoboundedUnder_le_of_le atTop fun n => by positivity
  have hupp : IsBoundedUnder (· ≤ ·) atTop
      (fun n : ℕ => A.partialDensity Set.univ n) :=
    isBoundedUnder_of ⟨(1 : ℝ), fun (n : ℕ) =>
      Set.partialDensity_le_one A Set.univ n⟩
  obtain ⟨N, hNlim, hNtop⟩ := exists_seq_tendsto_limsup hlow hupp
  have hNpos : ∀ᶠ k in atTop, 0 < N k := by
    exact hNtop (eventually_gt_atTop 0)
  rw [eventually_atTop] at hNpos
  obtain ⟨K, hK⟩ := hNpos
  refine ⟨fun k => N (k + K), ?_, ?_, ?_⟩
  · simpa [Set.upperDensity, Function.comp_def] using
      hNlim.comp (tendsto_add_atTop_nat K)
  · exact hNtop.comp (tendsto_add_atTop_nat K)
  · intro k
    exact hK (k + K) (Nat.le_add_left K k)

/-! ## Diagonal compactness for the analytic argument -/

/-- A countable array of real numbers with one common bound has a
subsequence on which every column converges.  MRR repeatedly pass to one
subsequence on which countably many finite correlations exist; packaging the
argument as convergence in a compact countable product avoids a nested
diagonal construction. -/
theorem exists_subseq_tendsto_bounded_array
    (a : ℕ → ℕ → ℝ) (C : ℝ)
    (ha : ∀ k j, a k j ∈ Set.Icc (-C) C) :
    ∃ φ : ℕ → ℕ, ∃ l : ℕ → ℝ, StrictMono φ ∧
      (∀ j, Tendsto (fun k => a (φ k) j) atTop (𝓝 (l j))) ∧
      ∀ j, l j ∈ Set.Icc (-C) C := by
  let x : ℕ → ℕ → Set.Icc (-C) C := fun k j => ⟨a k j, ha k j⟩
  obtain ⟨y, φ, hφ, hy⟩ := CompactSpace.tendsto_subseq x
  refine ⟨φ, fun j => y j, hφ, ?_, fun j => (y j).property⟩
  intro j
  have hj := (continuous_subtype_val.tendsto (y j)).comp (hy.apply_nhds j)
  change Tendsto (fun k => a (φ k) j) atTop (𝓝 ((y j : Set.Icc (-C) C) : ℝ)) at hj
  exact hj

/-- The normalized proportion of a set inside a finite sampling set. -/
noncomputable def finsetDensity (F : Finset ℕ) (E : Set ℕ) : ℝ :=
  ((((F : Set ℕ) ∩ E).ncard : ℕ) : ℝ) / F.card

/-- Convergence of densities along a sequence of finite sampling sets. -/
def HasDensityAlong (F : ℕ → Finset ℕ) (E : Set ℕ) (d : ℝ) : Prop :=
  Tendsto (fun k => finsetDensity (F k) E) atTop (𝓝 d)

theorem finsetDensity_nonneg (F : Finset ℕ) (E : Set ℕ) :
    0 ≤ finsetDensity F E := by
  simp only [finsetDensity]
  positivity

theorem finsetDensity_mono {F : Finset ℕ} {E D : Set ℕ} (hED : E ⊆ D) :
    finsetDensity F E ≤ finsetDensity F D := by
  unfold finsetDensity
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast Set.ncard_le_ncard (inter_subset_inter_right (F : Set ℕ) hED)
    (F.finite_toSet.inter_of_left D)

theorem finsetDensity_union_le (F : Finset ℕ) (E D : Set ℕ) :
    finsetDensity F (E ∪ D) ≤ finsetDensity F E + finsetDensity F D := by
  unfold finsetDensity
  rw [← add_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  norm_cast
  rw [show (F : Set ℕ) ∩ (E ∪ D) =
      ((F : Set ℕ) ∩ E) ∪ ((F : Set ℕ) ∩ D) by
    ext n
    simp only [mem_inter_iff, Finset.mem_coe, mem_union]
    tauto]
  exact Set.ncard_union_le _ _

theorem hasDensityAlong_zero_mono {F : ℕ → Finset ℕ} {E D : Set ℕ}
    (hED : E ⊆ D) (hD : HasDensityAlong F D 0) :
    HasDensityAlong F E 0 := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hD
  · exact fun _ => finsetDensity_nonneg _ _
  · exact fun _ => finsetDensity_mono hED

theorem hasDensityAlong_zero_union {F : ℕ → Finset ℕ} {E D : Set ℕ}
    (hE : HasDensityAlong F E 0) (hD : HasDensityAlong F D 0) :
    HasDensityAlong F (E ∪ D) 0 := by
  have hsum : Tendsto
      (fun k => finsetDensity (F k) E + finsetDensity (F k) D) atTop (𝓝 0) := by
    simpa only [zero_add] using hE.add hD
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
  · exact fun _ => finsetDensity_nonneg _ _
  · exact fun k => finsetDensity_union_le (F k) E D

/-- The filter of sets whose complements have density zero along `F`. -/
def densityOneFilter (F : ℕ → Finset ℕ) : Filter ℕ where
  sets := {E | HasDensityAlong F Eᶜ 0}
  univ_sets := by
    simpa [HasDensityAlong, finsetDensity] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  sets_of_superset := by
    intro E D hE hED
    exact hasDensityAlong_zero_mono (compl_subset_compl.mpr hED) hE
  inter_sets := by
    intro E D hE hD
    change HasDensityAlong F (E ∩ D)ᶜ 0
    rw [compl_inter]
    exact hasDensityAlong_zero_union hE hD

theorem finsetDensity_univ (F : Finset ℕ) (hF : F.Nonempty) :
    finsetDensity F Set.univ = 1 := by
  simp [finsetDensity, Finset.card_ne_zero.mpr hF]

theorem densityOneFilter_neBot (F : ℕ → Finset ℕ) (hF : ∀ k, (F k).Nonempty) :
    (densityOneFilter F).NeBot := by
  rw [Filter.neBot_iff]
  intro hbot
  have hzero : HasDensityAlong F Set.univ 0 := by
    have : (∅ : Set ℕ) ∈ densityOneFilter F := by simp [hbot]
    change HasDensityAlong F (∅ : Set ℕ)ᶜ 0 at this
    simpa using this
  have hone : HasDensityAlong F Set.univ 1 := by
    simpa only [HasDensityAlong, finsetDensity_univ _ (hF _)] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
  exact zero_ne_one (tendsto_nhds_unique hzero hone)

theorem hasDensityAlong_zero_of_finite
    (F : ℕ → Finset ℕ) (hcard : Tendsto (fun k => (F k).card) atTop atTop)
    {E : Set ℕ} (hE : E.Finite) : HasDensityAlong F E 0 := by
  classical
  have hbound (k : ℕ) :
      finsetDensity (F k) E ≤ (E.ncard : ℝ) / (F k).card := by
    unfold finsetDensity
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    norm_cast
    exact Set.ncard_le_ncard inter_subset_right hE
  have hupp : Tendsto (fun k => (E.ncard : ℝ) / (F k).card)
      atTop (𝓝 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat (E.ncard : ℝ)).comp hcard
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupp
  · exact fun _ => finsetDensity_nonneg _ _
  · exact hbound

theorem densityOneFilter_le_cofinite
    (F : ℕ → Finset ℕ) (hcard : Tendsto (fun k => (F k).card) atTop atTop) :
    densityOneFilter F ≤ (cofinite : Filter ℕ) := by
  intro E hE
  change HasDensityAlong F Eᶜ 0
  exact hasDensityAlong_zero_of_finite F hcard (by
    simpa only [mem_cofinite] using hE)

/-- The density-one filter extends to a free ultrafilter.  In particular,
every set of density zero is rejected by this ultrafilter. -/
theorem exists_ultrafilter_avoiding_density_zero
    (F : ℕ → Finset ℕ) (hF : ∀ k, (F k).Nonempty)
    (hcard : Tendsto (fun k => (F k).card) atTop atTop) :
    ∃ p : Ultrafilter ℕ,
      (p : Filter ℕ) ≤ densityOneFilter F ∧ (p : Filter ℕ) ≤ cofinite := by
  let : (densityOneFilter F).NeBot := densityOneFilter_neBot F hF
  obtain ⟨p, hp⟩ := Ultrafilter.exists_le (densityOneFilter F)
  exact ⟨p, hp, hp.trans (densityOneFilter_le_cofinite F hcard)⟩

theorem density_zero_not_mem_ultrafilter
    {F : ℕ → Finset ℕ} {p : Ultrafilter ℕ}
    (hp : (p : Filter ℕ) ≤ densityOneFilter F) {E : Set ℕ}
    (hE : HasDensityAlong F E 0) : E ∉ (p : Filter ℕ) := by
  intro hEp
  have hcomp : Eᶜ ∈ (p : Filter ℕ) := by
    apply hp
    change HasDensityAlong F (Eᶜ)ᶜ 0
    simpa using hE
  have hempty : (∅ : Set ℕ) ∈ (p : Filter ℕ) := by
    simpa only [inter_compl_self] using inter_mem hEp hcomp
  simpa using hempty

/-- A uniform eventual lower bound for the density of `E` along `F`. -/
def HasPositiveLowerDensityAlong (F : ℕ → Finset ℕ) (E : Set ℕ) : Prop :=
  ∃ r : ℝ, 0 < r ∧ ∀ᶠ k in atTop, r ≤ finsetDensity (F k) E

theorem not_subset_of_positiveLowerDensity_of_density_zero
    {F : ℕ → Finset ℕ} {B E : Set ℕ}
    (hB : HasPositiveLowerDensityAlong F B)
    (hE : HasDensityAlong F E 0) : ¬B ⊆ E := by
  rintro hBE
  obtain ⟨r, hr, hBr⟩ := hB
  have hEr : ∀ᶠ k in atTop, finsetDensity (F k) E < r :=
    hE.eventually (eventually_lt_nhds hr)
  obtain ⟨k, hBk, hEk⟩ := (hBr.and hEr).exists
  exact (not_lt_of_ge (hBk.trans (finsetDensity_mono hBE))) hEk

theorem densityOneFilter_inf_principal_neBot
    {F : ℕ → Finset ℕ} {B : Set ℕ}
    (hB : HasPositiveLowerDensityAlong F B) :
    (densityOneFilter F ⊓ 𝓟 B).NeBot := by
  rw [Filter.inf_principal_neBot_iff]
  intro U hU
  change HasDensityAlong F Uᶜ 0 at hU
  by_contra hnon
  have hsub : B ⊆ Uᶜ := by
    intro b hb
    simp only [mem_compl_iff, Classical.not_not]
    intro hbU
    exact hnon ⟨b, hbU, hb⟩
  exact not_subset_of_positiveLowerDensity_of_density_zero hB hU hsub

/-- An eventually positive-density set can be placed in an ultrafilter that
rejects every density-zero set.  When the sample sizes grow, this
ultrafilter is free.  This is the exact `U1` mechanism in MRR. -/
theorem exists_ultrafilter_containing_positiveLowerDensity
    (F : ℕ → Finset ℕ) (hcard : Tendsto (fun k => (F k).card) atTop atTop)
    {B : Set ℕ} (hB : HasPositiveLowerDensityAlong F B) :
    ∃ p : Ultrafilter ℕ, B ∈ (p : Filter ℕ) ∧
      (p : Filter ℕ) ≤ densityOneFilter F ∧ (p : Filter ℕ) ≤ cofinite := by
  let : (densityOneFilter F ⊓ 𝓟 B).NeBot :=
    densityOneFilter_inf_principal_neBot hB
  obtain ⟨p, hp⟩ := Ultrafilter.exists_le (densityOneFilter F ⊓ 𝓟 B)
  have hpDensity : (p : Filter ℕ) ≤ densityOneFilter F :=
    hp.trans inf_le_left
  have hpB : (p : Filter ℕ) ≤ 𝓟 B := hp.trans inf_le_right
  exact ⟨p, (le_principal_iff.mp hpB), hpDensity,
    hpDensity.trans (densityOneFilter_le_cofinite F hcard)⟩

/-! ## Syndetic return times of a compact orbit -/

/-- A set of natural numbers is syndetic if every interval of one fixed
finite length meets it.  The offset formulation is convenient for both
orbit-return arguments and cardinality estimates. -/
def Syndetic (S : Set ℕ) : Prop :=
  ∃ K : ℕ, ∀ n : ℕ, ∃ k ≤ K, n + k ∈ S

/-- A totally bounded forward orbit of an isometry returns uniformly often
to every neighbourhood of its initial point.  This is the compact-recurrence
part of MRR's Lemma 4.9, stated without any Hilbert-space structure. -/
theorem syndetic_returnTimes_of_totallyBounded
    {X : Type*} [PseudoMetricSpace X] (T : X → X) (hT : Isometry T)
    (x : X) (horbit : TotallyBounded (Set.range fun n : ℕ ↦ T^[n] x))
    {r : ℝ} (hr : 0 < r) :
    Syndetic {n : ℕ | dist (T^[n] x) x < r} := by
  obtain ⟨centres, hcentres_subset, hcentres_finite, hcover⟩ :=
    Metric.finite_approx_of_totallyBounded horbit r hr
  have hchoose : ∀ y ∈ Set.range (fun n : ℕ ↦ T^[n] x),
      ∃ z ∈ centres, y ∈ Metric.ball z r := by
    intro y hy
    rcases Set.mem_iUnion.mp (hcover hy) with ⟨z, hz⟩
    rcases Set.mem_iUnion.mp hz with ⟨hzcentres, hyz⟩
    exact ⟨z, hzcentres, hyz⟩
  have hcentres_nonempty : centres.Nonempty := by
    obtain ⟨z, hz, -⟩ := hchoose x ⟨0, by simp⟩
    exact ⟨z, hz⟩
  let : Fintype centres := hcentres_finite.fintype
  let index : centres → ℕ := fun z ↦ Classical.choose (hcentres_subset z.property)
  have hindex (z : centres) : T^[index z] x = z :=
    Classical.choose_spec (hcentres_subset z.property)
  let K : ℕ := Finset.univ.sup index
  refine ⟨K, fun n ↦ ?_⟩
  obtain ⟨z, hz, hnz⟩ := hchoose (T^[n + K] x) ⟨n + K, rfl⟩
  let z' : centres := ⟨z, hz⟩
  let i := index z'
  have hiK : i ≤ K := by
    dsimp [K]
    exact Finset.le_sup (f := index) (Finset.mem_univ z')
  refine ⟨K - i, Nat.sub_le K i, ?_⟩
  change dist (T^[n + (K - i)] x) x < r
  have hsum : i + (n + (K - i)) = n + K := by omega
  have hiso_dist (j : ℕ) (a b : X) : dist (T^[j] a) (T^[j] b) = dist a b := by
    induction j with
    | zero => simp
    | succ j ih =>
        have ha : T^[j + 1] a = T (T^[j] a) := by
          simpa only [Nat.succ_eq_add_one] using Function.iterate_succ_apply' T j a
        have hb : T^[j + 1] b = T (T^[j] b) := by
          simpa only [Nat.succ_eq_add_one] using Function.iterate_succ_apply' T j b
        rw [ha, hb, hT.dist_eq, ih]
  rw [← hiso_dist i]
  rw [← Function.iterate_add_apply, hsum]
  rw [hindex z']
  exact hnz

/-- A syndetic set occupies at least one point in each of a linearly growing
family of disjoint blocks.  This cardinality version is the arithmetic core
of the positive-lower-density estimate below. -/
theorem ncard_inter_range_lower_of_syndetic {S : Set ℕ} (hS : Syndetic S) :
    ∃ d : ℕ, 0 < d ∧ ∀ N : ℕ,
      N / d ≤ ((Finset.range N : Set ℕ) ∩ S).ncard := by
  classical
  obtain ⟨K, hK⟩ := hS
  let d := K + 1
  let offset : ℕ → ℕ := fun j ↦ Classical.choose (hK (j * d))
  have hoffset_le (j : ℕ) : offset j ≤ K :=
    (Classical.choose_spec (hK (j * d))).1
  have hoffset_mem (j : ℕ) : j * d + offset j ∈ S :=
    (Classical.choose_spec (hK (j * d))).2
  let point : ℕ → ℕ := fun j ↦ j * d + offset j
  have hpoint_block (j : ℕ) : point j < (j + 1) * d := by
    calc
      point j = j * d + offset j := rfl
      _ ≤ j * d + K := Nat.add_le_add_left (hoffset_le j) _
      _ < j * d + d := Nat.add_lt_add_left (by dsimp [d]; omega) _
      _ = (j + 1) * d := by simp [Nat.add_mul]
  have hpoint_lt (N j : ℕ) (hj : j < N / d) : point j < N := by
    have hmul : (j + 1) * d ≤ N := by
      exact (Nat.le_div_iff_mul_le (by omega : 0 < d)).mp (Nat.succ_le_of_lt hj)
    exact (hpoint_block j).trans_le hmul
  have hpoint_inj : Injective point := by
    intro i j hij
    rcases lt_trichotomy i j with hijlt | rfl | hjilt
    · have hleft := hpoint_block i
      have hright : (i + 1) * d ≤ point j := by
        dsimp [point]
        exact le_add_right ((Nat.mul_le_mul_right d (Nat.succ_le_of_lt hijlt)))
      exact ((hleft.trans_le hright).ne hij).elim
    · rfl
    · have hleft := hpoint_block j
      have hright : (j + 1) * d ≤ point i := by
        dsimp [point]
        exact le_add_right ((Nat.mul_le_mul_right d (Nat.succ_le_of_lt hjilt)))
      exact ((hleft.trans_le hright).ne hij.symm).elim
  refine ⟨d, by dsimp [d]; omega, fun N ↦ ?_⟩
  let image := (Finset.range (N / d)).image point
  have himage_subset : (image : Set ℕ) ⊆ (Finset.range N : Set ℕ) ∩ S := by
    intro y hy
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
    have hj' : j < N / d := Finset.mem_range.mp hj
    exact ⟨Finset.mem_range.mpr (hpoint_lt N j hj'), hoffset_mem j⟩
  have hcard : image.card ≤ ((Finset.range N : Set ℕ) ∩ S).ncard := by
    rw [← Set.ncard_coe_finset image]
    exact Set.ncard_le_ncard himage_subset
      ((Finset.range N).finite_toSet.inter_of_left S)
  simpa [image, Finset.card_image_iff.mpr hpoint_inj.injOn] using hcard

/-- Every syndetic set has a uniform positive lower density on any sequence
of initial intervals whose lengths tend to infinity. -/
theorem positiveLowerDensity_range_of_syndetic {S : Set ℕ} (hS : Syndetic S)
    {N : ℕ → ℕ} (hN : Tendsto N atTop atTop) :
    HasPositiveLowerDensityAlong (fun k ↦ Finset.range (N k)) S := by
  obtain ⟨d, hd, hcard⟩ := ncard_inter_range_lower_of_syndetic hS
  refine ⟨1 / (2 * d : ℝ), by positivity, ?_⟩
  filter_upwards [hN (eventually_ge_atTop (2 * d))] with k hk
  change 2 * d ≤ N k at hk
  have hNpos : 0 < N k := lt_of_lt_of_le (by omega : 0 < 2 * d) hk
  have hdivpos : 0 < N k / d := by
    exact Nat.div_pos (by omega) hd
  have harith : N k ≤ 2 * (N k / d) * d := by
    have hlt : N k < d * (N k / d + 1) := Nat.lt_mul_div_succ (N k) hd
    have hsucc : N k / d + 1 ≤ 2 * (N k / d) := by omega
    nlinarith
  have hratio : (1 : ℝ) / (2 * d) ≤ ((N k / d : ℕ) : ℝ) / N k := by
    rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 * d) (by exact_mod_cast hNpos)]
    norm_num only [one_mul]
    exact_mod_cast (show N k ≤ (N k / d) * (2 * d) by
      simpa [mul_assoc, mul_left_comm, mul_comm] using harith)
  exact hratio.trans (by
    unfold finsetDensity
    rw [Finset.card_range]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hcard (N k)) (Nat.cast_nonneg _))

/-- Compact recurrence can be imposed on a free ultrafilter while retaining
the property that every density-zero exceptional set is rejected.  This is
the exact combination of MRR's conditions U1 and U2. -/
theorem exists_essential_ultrafilter_containing_compact_returns
    {X : Type*} [PseudoMetricSpace X] (T : X → X) (hT : Isometry T)
    (x : X) (horbit : TotallyBounded (Set.range fun n : ℕ ↦ T^[n] x))
    {r : ℝ} (hr : 0 < r) {N : ℕ → ℕ} (hN : Tendsto N atTop atTop) :
    ∃ p : Ultrafilter ℕ,
      {n : ℕ | dist (T^[n] x) x < r} ∈ (p : Filter ℕ) ∧
      (p : Filter ℕ) ≤ densityOneFilter (fun k ↦ Finset.range (N k)) ∧
      (p : Filter ℕ) ≤ cofinite := by
  let returns : Set ℕ := {n : ℕ | dist (T^[n] x) x < r}
  have hreturns : Syndetic returns :=
    syndetic_returnTimes_of_totallyBounded T hT x horbit hr
  have hdensity : HasPositiveLowerDensityAlong
      (fun k ↦ Finset.range (N k)) returns :=
    positiveLowerDensity_range_of_syndetic hreturns hN
  have hcard : Tendsto (fun k ↦ (Finset.range (N k)).card) atTop atTop := by
    simpa only [Finset.card_range] using hN
  simpa only [returns] using
    exists_ultrafilter_containing_positiveLowerDensity
      (fun k ↦ Finset.range (N k)) hcard hdensity

/-! ## Finite Bohr return sets -/

/-- Simultaneous approximate return times for a finite family of characters
of `ℕ`.  An element `z : Circle` represents the character `n ↦ z ^ n`. -/
def bohrReturn (Z : List Circle) (r : ℝ) : Set ℕ :=
  {n | ∀ z ∈ Z, dist (z ^ n) 1 < r}

/-- A finite Bohr return set is syndetic.  We realize all characters at once
as a rotation of the compact finite product of circles and invoke compact
recurrence. -/
theorem bohrReturn_syndetic (Z : List Circle) {r : ℝ} (hr : 0 < r) :
    Syndetic (bohrReturn Z r) := by
  classical
  let I := Fin Z.length
  let phase : I → Circle := fun i ↦ Z.get i
  let T : (I → Circle) → (I → Circle) := fun w ↦ phase * w
  have hT : Isometry T := by
    exact Isometry.piMap (fun i (w : Circle) ↦ phase i * w)
      (fun i ↦ by
        rw [isometry_iff_dist_eq]
        intro x y
        rw [show dist (phase i * x) (phase i * y) =
            dist ((phase i * x : Circle) : ℂ) ((phase i * y : Circle) : ℂ) from rfl]
        rw [show dist x y = dist (x : ℂ) (y : ℂ) from rfl]
        simp only [Complex.dist_eq, Circle.coe_mul]
        rw [← mul_sub, norm_mul, Circle.norm_coe, one_mul])
  have horbit : TotallyBounded
      (Set.range fun n : ℕ ↦ T^[n] (1 : I → Circle)) :=
    TotallyBounded.subset (Set.subset_univ _) isCompact_univ.totallyBounded
  have hiterate (n : ℕ) : T^[n] (1 : I → Circle) = fun i ↦ phase i ^ n := by
    induction n with
    | zero => ext z; simp
    | succ n ih =>
        have hs : T^[n + 1] (1 : I → Circle) = T (T^[n] 1) := by
          simpa only [Nat.succ_eq_add_one] using Function.iterate_succ_apply' T n 1
        rw [hs, ih]
        ext z
        simp [T, phase, pow_succ']
  have hreturn := syndetic_returnTimes_of_totallyBounded T hT
    (1 : I → Circle) horbit hr
  convert hreturn using 1
  ext n
  simp only [bohrReturn, Set.mem_ofPred_eq, hiterate]
  rw [dist_pi_lt_iff hr]
  constructor
  · intro h i
    exact h (Z.get i) (List.get_mem Z i)
  · intro h z hz
    obtain ⟨i, rfl⟩ := List.get_of_mem hz
    exact h i

/-- Intersecting finitely many finite-character return constraints amounts
to taking their union and the smaller radius. -/
theorem bohrReturn_append_subset_inter (Z W : List Circle) {r s : ℝ}
    (hr : 0 < r) (hs : 0 < s) :
    bohrReturn (Z ++ W) (min r s) ⊆ bohrReturn Z r ∩ bohrReturn W s := by
  intro n hn
  constructor
  · intro z hz
    exact (hn z (by simp [hz])).trans_le (min_le_left _ _)
  · intro z hz
    exact (hn z (by simp [hz])).trans_le (min_le_right _ _)

/-- The common return constraint for two finite character families has a
uniform positive lower density on every growing sequence of prefixes. -/
theorem positiveLowerDensity_bohrReturn_append
    (Z W : List Circle) {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    {N : ℕ → ℕ} (hN : Tendsto N atTop atTop) :
    HasPositiveLowerDensityAlong (fun k ↦ Finset.range (N k))
      (bohrReturn (Z ++ W) (min r s)) := by
  apply positiveLowerDensity_range_of_syndetic
  · exact bohrReturn_syndetic (Z ++ W) (lt_min hr hs)
  · exact hN

/-- Two finite Bohr-return requirements can be imposed on one free
ultrafilter which still rejects every set of zero density along the chosen
prefixes.  This is the finite-character form of MRR's conditions `U1` and
`U3`. -/
theorem exists_essential_ultrafilter_containing_bohrReturns
    (Z W : List Circle) {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    {N : ℕ → ℕ} (hN : Tendsto N atTop atTop) :
    ∃ p : Ultrafilter ℕ,
      bohrReturn Z r ∈ (p : Filter ℕ) ∧
      bohrReturn W s ∈ (p : Filter ℕ) ∧
      (p : Filter ℕ) ≤ densityOneFilter (fun k ↦ Finset.range (N k)) ∧
      (p : Filter ℕ) ≤ cofinite := by
  let D := bohrReturn (Z ++ W) (min r s)
  have hD : HasPositiveLowerDensityAlong (fun k ↦ Finset.range (N k)) D :=
    positiveLowerDensity_bohrReturn_append Z W hr hs hN
  have hcard : Tendsto (fun k ↦ (Finset.range (N k)).card) atTop atTop := by
    simpa only [Finset.card_range] using hN
  obtain ⟨p, hDp, hpDensity, hpfree⟩ :=
    exists_ultrafilter_containing_positiveLowerDensity
      (fun k ↦ Finset.range (N k)) hcard hD
  have hsub := bohrReturn_append_subset_inter Z W hr hs
  refine ⟨p, ?_, ?_, hpDensity, hpfree⟩
  · exact mem_of_superset hDp (hsub.trans inter_subset_left)
  · exact mem_of_superset hDp (hsub.trans inter_subset_right)

/-! ## Finite trigonometric polynomials -/

/-- A finite trigonometric polynomial on `ℕ`; a circle element `z`
denotes the character `n ↦ z ^ n`.  Lists allow repeated phases without
requiring decidable equality on the circle. -/
noncomputable def trigPoly (terms : List (ℂ × Circle)) (n : ℕ) : ℂ :=
  ∑ i : Fin terms.length, (terms.get i).1 * ((terms.get i).2 : ℂ) ^ n

/-- The phases occurring in a trigonometric polynomial, with multiplicity. -/
def trigPhases (terms : List (ℂ × Circle)) : List Circle :=
  terms.map Prod.snd

/-- The `ℓ¹` norm of the coefficients.  It is the uniform Lipschitz
constant used to turn simultaneous phase returns into polynomial returns. -/
noncomputable def trigCoeffNormSum (terms : List (ℂ × Circle)) : ℝ :=
  ∑ i : Fin terms.length, ‖(terms.get i).1‖

theorem trigCoeffNormSum_nonneg (terms : List (ℂ × Circle)) :
    0 ≤ trigCoeffNormSum terms := by
  exact Finset.sum_nonneg fun _ _ ↦ norm_nonneg _

/-- A simultaneous phase return moves a finite trigonometric polynomial by
at most the return radius times the coefficient `ℓ¹` norm, uniformly in
the base point. -/
theorem norm_trigPoly_add_sub_le
    (terms : List (ℂ × Circle)) {m : ℕ} {r : ℝ}
    (hm : m ∈ bohrReturn (trigPhases terms) r) (n : ℕ) :
    ‖trigPoly terms (n + m) - trigPoly terms n‖ ≤
      trigCoeffNormSum terms * r := by
  classical
  rw [trigPoly, trigPoly, ← Finset.sum_sub_distrib]
  calc
    ‖∑ i : Fin terms.length,
        ((terms.get i).1 * ((terms.get i).2 : ℂ) ^ (n + m) -
          (terms.get i).1 * ((terms.get i).2 : ℂ) ^ n)‖
        ≤ ∑ i : Fin terms.length,
            ‖(terms.get i).1 * ((terms.get i).2 : ℂ) ^ (n + m) -
              (terms.get i).1 * ((terms.get i).2 : ℂ) ^ n‖ :=
          norm_sum_le _ _
    _ ≤ ∑ i : Fin terms.length, ‖(terms.get i).1‖ * r := by
      apply Finset.sum_le_sum
      intro i hi
      let z : Circle := (terms.get i).2
      have hzmem : z ∈ trigPhases terms := by
        exact List.mem_map.mpr ⟨terms.get i, List.get_mem terms i, rfl⟩
      have hz := hm z hzmem
      have hz' : ‖(z : ℂ) ^ m - 1‖ < r := by
        rw [← Complex.dist_eq]
        exact_mod_cast hz
      calc
        ‖(terms.get i).1 * ((z : ℂ) ^ (n + m)) -
            (terms.get i).1 * ((z : ℂ) ^ n)‖ =
            ‖(terms.get i).1 * (z : ℂ) ^ n * ((z : ℂ) ^ m - 1)‖ := by
              congr 1
              rw [pow_add]
              ring
        _ = ‖(terms.get i).1‖ * ‖(z : ℂ) ^ n‖ *
              ‖(z : ℂ) ^ m - 1‖ := by rw [norm_mul, norm_mul]
        _ = ‖(terms.get i).1‖ * ‖(z : ℂ) ^ m - 1‖ := by
              rw [norm_pow, Circle.norm_coe, one_pow, mul_one]
        _ ≤ ‖(terms.get i).1‖ * r :=
              mul_le_mul_of_nonneg_left hz'.le (norm_nonneg _)
    _ = trigCoeffNormSum terms * r := by
      rw [trigCoeffNormSum, Finset.sum_mul]

/-! ## Finite means and correlations

The MRR analytic argument is ultimately used only for indicator functions.
The following elementary layer records the exact translation between its
finite Hilbert-space notation and the cardinality densities used by the
combinatorial extraction below.  Keeping this interface over `ℝ` avoids any
loss through `ℝ≥0∞` coercions in the analytic part. -/

/-- The real indicator of a set of natural numbers. -/
noncomputable def realIndicator (E : Set ℕ) : ℕ → ℝ :=
  by
    classical
    exact fun n ↦ if n ∈ E then 1 else 0

@[simp] theorem realIndicator_apply_mem {E : Set ℕ} {n : ℕ} (hn : n ∈ E) :
    realIndicator E n = 1 := by
  simp [realIndicator, hn]

@[simp] theorem realIndicator_apply_notMem {E : Set ℕ} {n : ℕ} (hn : n ∉ E) :
    realIndicator E n = 0 := by
  simp [realIndicator, hn]

/-- The normalized mean of a real function over a finite set. -/
noncomputable def realFinsetMean (F : Finset ℕ) (f : ℕ → ℝ) : ℝ :=
  (∑ n ∈ F, f n) / F.card

/-- The finite real correlation used throughout the specialized MRR
argument. -/
noncomputable def realFinsetCorrelation
    (F : Finset ℕ) (f g : ℕ → ℝ) : ℝ :=
  realFinsetMean F (fun n ↦ f n * g n)

theorem sum_realIndicator (F : Finset ℕ) (E : Set ℕ) :
    ∑ n ∈ F, realIndicator E n =
      (((F : Set ℕ) ∩ E).ncard : ℝ) := by
  classical
  rw [Set.ncard_eq_toFinset_card _ (F.finite_toSet.inter_of_left E)]
  simp [realIndicator, Set.Finite.mem_toFinset]

theorem realFinsetMean_indicator (F : Finset ℕ) (E : Set ℕ) :
    realFinsetMean F (realIndicator E) = finsetDensity F E := by
  rw [realFinsetMean, finsetDensity, sum_realIndicator]

@[simp] theorem realIndicator_inter (E D : Set ℕ) (n : ℕ) :
    realIndicator (E ∩ D) n = realIndicator E n * realIndicator D n := by
  classical
  by_cases hnE : n ∈ E <;> by_cases hnD : n ∈ D <;>
    simp [realIndicator, hnE, hnD]

theorem realFinsetCorrelation_indicator (F : Finset ℕ) (E D : Set ℕ) :
    realFinsetCorrelation F (realIndicator E) (realIndicator D) =
      finsetDensity F (E ∩ D) := by
  rw [realFinsetCorrelation]
  simp_rw [← realIndicator_inter]
  exact realFinsetMean_indicator F (E ∩ D)

theorem finsetDensity_le_one (F : Finset ℕ) (E : Set ℕ) :
    finsetDensity F E ≤ 1 := by
  by_cases hF : F.Nonempty
  · calc
      finsetDensity F E ≤ finsetDensity F Set.univ :=
        finsetDensity_mono (Set.subset_univ E)
      _ = 1 := finsetDensity_univ F hF
  · have : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hF
    simp [this, finsetDensity]

/-- On an initial interval, the finite-set normalization is definitionally
the partial density used in `Set.upperDensity`. -/
theorem finsetDensity_range_eq_partialDensity (A : Set ℕ) (N : ℕ) :
    finsetDensity (Finset.range N) A = A.partialDensity Set.univ N := by
  simp [finsetDensity, Set.partialDensity, Set.ncard_eq_toFinset_card, inter_comm]

/-- Countably many set densities can be made simultaneously convergent by
one increasing reindexing.  This is the indicator-valued instance of MRR's
repeated correlation diagonalization. -/
theorem exists_subseq_hasDensityAlong_countable
    (F : ℕ → Finset ℕ) (s : ℕ → Set ℕ) :
    ∃ φ : ℕ → ℕ, ∃ d : ℕ → ℝ, StrictMono φ ∧
      (∀ i, HasDensityAlong (fun k ↦ F (φ k)) (s i) (d i)) ∧
      ∀ i, d i ∈ Set.Icc (0 : ℝ) 1 := by
  have hbounds (k i : ℕ) :
      finsetDensity (F k) (s i) ∈ Set.Icc (-(1 : ℝ)) 1 :=
    ⟨(by linarith [finsetDensity_nonneg (F k) (s i)]),
      finsetDensity_le_one (F k) (s i)⟩
  obtain ⟨φ, d, hφ, hd, hdIcc⟩ :=
    exists_subseq_tendsto_bounded_array
      (fun k i ↦ finsetDensity (F k) (s i)) 1 hbounds
  refine ⟨φ, d, hφ, hd, fun i ↦ ⟨?_, (hdIcc i).2⟩⟩
  exact ge_of_tendsto (hd i)
    (Filter.Eventually.of_forall fun k ↦ finsetDensity_nonneg (F (φ k)) (s i))

/-! ## A density form of Bergelson's lemma -/

/-- Membership patterns for a countable family of subsets of `ℕ`. -/
abbrev DensityPattern := ℕ → Bool

/-- The coordinate cylinder in Cantor space. -/
def patternEvent (i : ℕ) : Set DensityPattern := {p | p i = true}

theorem patternEvent_isClopen (i : ℕ) : IsClopen (patternEvent i) := by
  exact (isClopen_discrete {true}).preimage (continuous_apply i)

/-- The membership pattern of one natural number in a countable family of sets. -/
noncomputable def membershipPattern (s : ℕ → Set ℕ) (x : ℕ) : DensityPattern := by
  classical
  exact fun i => decide (x ∈ s i)

@[simp] theorem membershipPattern_apply (s : ℕ → Set ℕ) (x i : ℕ) :
    membershipPattern s x i = true ↔ x ∈ s i := by
  classical
  simp [membershipPattern]

/-- The one-sided shift on the Cantor space of Boolean sequences. -/
def patternShift (x : DensityPattern) : DensityPattern :=
  fun i ↦ x (i + 1)

theorem continuous_patternShift : Continuous patternShift := by
  apply continuous_pi
  intro i
  exact continuous_apply (i + 1)

@[simp] theorem patternShift_apply (x : DensityPattern) (i : ℕ) :
    patternShift x i = x (i + 1) := rfl

theorem patternShift_preimage_event (i : ℕ) :
    patternShift ⁻¹' patternEvent i = patternEvent (i + 1) := rfl

/-- The orbit name of `A`: its `i`-th coordinate records membership of
`n+i` in `A`. -/
noncomputable def orbitPattern (A : Set ℕ) (n : ℕ) : DensityPattern :=
  membershipPattern (fun i ↦ {x : ℕ | x + i ∈ A}) n

@[simp] theorem orbitPattern_apply (A : Set ℕ) (n i : ℕ) :
    orbitPattern A n i = true ↔ n + i ∈ A := by
  simp [orbitPattern]

theorem patternShift_orbitPattern (A : Set ℕ) (n : ℕ) :
    patternShift (orbitPattern A n) = orbitPattern A (n + 1) := by
  ext i
  apply Bool.eq_iff_iff.mpr
  simp only [patternShift_apply, orbitPattern_apply]
  rw [show n + (i + 1) = n + 1 + i by omega]

theorem iterate_patternShift_orbitPattern (A : Set ℕ) (m n : ℕ) :
    patternShift^[m] (orbitPattern A n) = orbitPattern A (n + m) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Function.iterate_succ_apply', ih, patternShift_orbitPattern]
      rw [show n + m + 1 = n + (m + 1) by omega]

/-- The uniform empirical law of membership patterns on a nonempty finite set. -/
noncomputable def empiricalPatternMeasure (s : ℕ → Set ℕ) (F : Finset ℕ)
    (hF : F.Nonempty) : ProbabilityMeasure DensityPattern :=
  ⟨((PMF.uniformOfFinset F hF).map (membershipPattern s)).toMeasure, inferInstance⟩

theorem empiricalPatternMeasure_apply (s : ℕ → Set ℕ) (F : Finset ℕ)
    (hF : F.Nonempty) {E : Set DensityPattern} (hE : MeasurableSet E) :
    ((empiricalPatternMeasure s F hF : ProbabilityMeasure DensityPattern) :
        Measure DensityPattern) E =
      ((((F : Set ℕ) ∩ membershipPattern s ⁻¹' E).ncard : ℕ) : ℝ≥0∞) / F.card := by
  classical
  change ((PMF.uniformOfFinset F hF).map (membershipPattern s)).toMeasure E = _
  rw [PMF.toMeasure_map_apply (membershipPattern s) _ E (measurable_of_countable _) hE]
  rw [PMF.toMeasure_uniformOfFinset_apply hF _
    (membershipPattern s ⁻¹' E).to_countable.measurableSet]
  congr 2
  rw [Set.ncard_eq_toFinset_card _ (F.finite_toSet.inter_of_left _)]
  simp

theorem empiricalPatternMeasure_event (s : ℕ → Set ℕ) (F : Finset ℕ)
    (hF : F.Nonempty) (i : ℕ) :
    ((empiricalPatternMeasure s F hF : ProbabilityMeasure DensityPattern) :
        Measure DensityPattern) (patternEvent i) =
      ((((F : Set ℕ) ∩ s i).ncard : ℕ) : ℝ≥0∞) / F.card := by
  classical
  change ((PMF.uniformOfFinset F hF).map (membershipPattern s)).toMeasure
    (patternEvent i) = _
  rw [PMF.toMeasure_map_apply (membershipPattern s) _ _ (measurable_of_countable _)
    (patternEvent_isClopen i).2.measurableSet]
  have hpre : membershipPattern s ⁻¹' patternEvent i = s i := by
    ext x
    simp [patternEvent]
  rw [hpre, PMF.toMeasure_uniformOfFinset_apply hF (s i) (s i).to_countable.measurableSet]
  congr 2
  rw [Set.ncard_eq_toFinset_card _ (F.finite_toSet.inter_of_left (s i))]
  simp

/-- The `i`-th translate recorded by the orbit name of `A`. -/
def orbitSet (A : Set ℕ) (i : ℕ) : Set ℕ := {n | n + i ∈ A}

theorem orbitPattern_eq_membershipPattern (A : Set ℕ) (n : ℕ) :
    orbitPattern A n = membershipPattern (orbitSet A) n := rfl

/-- The empirical distribution of the first `N` orbit names of `A`. -/
noncomputable def empiricalOrbitMeasure (A : Set ℕ) (N : ℕ) (hN : 0 < N) :
    ProbabilityMeasure DensityPattern :=
  empiricalPatternMeasure (orbitSet A) (Finset.range N)
    (by simpa using (Nat.ne_of_gt hN))

theorem empiricalOrbitMeasure_event (A : Set ℕ) (N : ℕ) (hN : 0 < N)
    (i : ℕ) :
    ((empiricalOrbitMeasure A N hN : ProbabilityMeasure DensityPattern) :
        Measure DensityPattern) (patternEvent i) =
      ((((Finset.range N : Set ℕ) ∩ orbitSet A i).ncard : ℕ) : ℝ≥0∞) / N := by
  simpa [empiricalOrbitMeasure] using
    empiricalPatternMeasure_event (orbitSet A) (Finset.range N)
      (by simpa using (Nat.ne_of_gt hN)) i

/-- Integrating a bounded continuous function against a finite empirical
orbit measure is the corresponding normalized orbit sum. -/
theorem integral_empiricalOrbitMeasure (A : Set ℕ) (N : ℕ) (hN : 0 < N)
    (f : DensityPattern →ᵇ ℝ) :
    ∫ x, f x ∂((empiricalOrbitMeasure A N hN : ProbabilityMeasure DensityPattern) :
        Measure DensityPattern) =
      (∑ n ∈ Finset.range N, f (orbitPattern A n)) / N := by
  classical
  let p := PMF.uniformOfFinset (Finset.range N)
    (by simpa using (Nat.ne_of_gt hN))
  let g : ℕ → DensityPattern := orbitPattern A
  have hg : Measurable g := measurable_of_countable _
  have hfg : Integrable (fun n ↦ f (g n)) p.toMeasure := by
    let fg : ℕ →ᵇ ℝ := f.compContinuous ⟨g, continuous_of_discreteTopology⟩
    exact BoundedContinuousFunction.integrable p.toMeasure fg
  change ∫ x, f x ∂((p.map g).toMeasure) = _
  rw [← PMF.toMeasure_map (f := g) p hg]
  rw [MeasureTheory.integral_map hg.aemeasurable
    (f.continuous.aestronglyMeasurable)]
  rw [PMF.integral_eq_tsum p (fun n ↦ f (g n)) hfg]
  rw [tsum_eq_sum (s := Finset.range N)]
  · calc
      (∑ x ∈ Finset.range N, (p x).toReal • f (g x)) =
          ((N : ℝ≥0∞)⁻¹).toReal *
            ∑ x ∈ Finset.range N, f (g x) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x hx
        rw [show p x = (N : ℝ≥0∞)⁻¹ by simp [p, hx]]
        rfl
      _ = (∑ n ∈ Finset.range N, f (orbitPattern A n)) / N := by
        simp only [ENNReal.toReal_inv, ENNReal.toReal_natCast, g]
        rw [div_eq_mul_inv]
        ring
  · intro n hn
    simp [p, PMF.uniformOfFinset_apply, hn]

/-- Shifting a finite interval sum changes it only by its two endpoints. -/
theorem sum_range_succ_shift (u : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range N, u (n + 1)) =
      (∑ n ∈ Finset.range N, u n) + u N - u 0 := by
  have h := Finset.sum_range_succ' u N
  rw [Finset.sum_range_succ] at h
  linarith

/-- A uniformly bounded endpoint error divided by prefix lengths tending to
infinity vanishes. -/
theorem tendsto_orbit_endpoint_error
    {ι : Type*} {L : Filter ι} (A : Set ℕ) (N : ι → ℕ)
    (hN : Tendsto N L atTop) (f : DensityPattern →ᵇ ℝ) :
    Tendsto (fun k ↦
      (f (orbitPattern A (N k)) - f (orbitPattern A 0)) / (N k : ℝ))
      L (𝓝 0) := by
  apply tendsto_bdd_div_atTop_nhds_zero
      (b := -2 * ‖f‖) (B := 2 * ‖f‖)
  · exact Eventually.of_forall fun k ↦ by
      have h₁ := f.norm_coe_le_norm (orbitPattern A (N k))
      have h₂ := f.norm_coe_le_norm (orbitPattern A 0)
      simp only [Real.norm_eq_abs] at h₁ h₂
      rcases abs_le.mp h₁ with ⟨h₁l, h₁u⟩
      rcases abs_le.mp h₂ with ⟨h₂l, h₂u⟩
      linarith
  · exact Eventually.of_forall fun k ↦ by
      have h₁ := f.norm_coe_le_norm (orbitPattern A (N k))
      have h₂ := f.norm_coe_le_norm (orbitPattern A 0)
      simp only [Real.norm_eq_abs] at h₁ h₂
      rcases abs_le.mp h₁ with ⟨h₁l, h₁u⟩
      rcases abs_le.mp h₂ with ⟨h₂l, h₂u⟩
      linarith
  · exact (tendsto_natCast_atTop_atTop (R := ℝ)).comp hN

/-- The shifted empirical integral equals the original empirical integral
plus its normalized endpoint error. -/
theorem integral_map_empiricalOrbitMeasure (A : Set ℕ) (N : ℕ) (hN : 0 < N)
    (f : DensityPattern →ᵇ ℝ) :
    ∫ x, f x ∂(((empiricalOrbitMeasure A N hN).map
        continuous_patternShift.measurable.aemeasurable :
          ProbabilityMeasure DensityPattern) : Measure DensityPattern) =
      (∫ x, f x ∂((empiricalOrbitMeasure A N hN :
        ProbabilityMeasure DensityPattern) : Measure DensityPattern)) +
      (f (orbitPattern A N) - f (orbitPattern A 0)) / N := by
  rw [ProbabilityMeasure.toMeasure_map]
  rw [MeasureTheory.integral_map
    continuous_patternShift.measurable.aemeasurable
    f.continuous.aestronglyMeasurable]
  let sf : DensityPattern →ᵇ ℝ :=
    f.compContinuous ⟨patternShift, continuous_patternShift⟩
  change (∫ x, sf x ∂((empiricalOrbitMeasure A N hN :
      ProbabilityMeasure DensityPattern) : Measure DensityPattern)) = _
  rw [integral_empiricalOrbitMeasure A N hN sf,
    integral_empiricalOrbitMeasure A N hN f]
  have hsum := sum_range_succ_shift (fun n ↦ f (orbitPattern A n)) N
  change (∑ n ∈ Finset.range N, f (patternShift (orbitPattern A n))) / N = _
  simp_rw [patternShift_orbitPattern]
  rw [hsum]
  ring

/-- Every weak limit of empirical laws along prefixes tending to infinity is
invariant under the one-sided shift. -/
theorem measurePreserving_patternShift_of_tendsto_empiricalOrbitMeasure
    {ι : Type*} {L : Filter ι} [NeBot L]
    (A : Set ℕ) (N : ι → ℕ) (hNpos : ∀ k, 0 < N k)
    (hNtop : Tendsto N L atTop) (μ : ProbabilityMeasure DensityPattern)
    (hμ : Tendsto (fun k ↦ empiricalOrbitMeasure A (N k) (hNpos k))
      L (𝓝 μ)) :
    MeasurePreserving patternShift (μ : Measure DensityPattern) μ := by
  let μs : ι → ProbabilityMeasure DensityPattern :=
    fun k ↦ empiricalOrbitMeasure A (N k) (hNpos k)
  have hμs : Tendsto μs L (𝓝 μ) := hμ
  have hmap :
      Tendsto (fun k ↦ (μs k).map
          continuous_patternShift.measurable.aemeasurable)
        L (𝓝 (μ.map continuous_patternShift.measurable.aemeasurable)) :=
    ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
      μs μ hμs continuous_patternShift
  have hsame :
      Tendsto (fun k ↦ (μs k).map
          continuous_patternShift.measurable.aemeasurable)
        L (𝓝 μ) := by
    rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
    intro f
    have horig :=
      (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hμs) f
    have herr := tendsto_orbit_endpoint_error A N hNtop f
    have hsum := horig.add herr
    convert hsum using 1
    · funext k
      exact integral_map_empiricalOrbitMeasure A (N k) (hNpos k) f
    · simp
  have heq : μ.map continuous_patternShift.measurable.aemeasurable = μ :=
    tendsto_nhds_unique hmap hsame
  refine ⟨continuous_patternShift.measurable, ?_⟩
  exact congrArg ProbabilityMeasure.toMeasure heq

/-- Compactness of probability measures on Cantor space supplies a limiting
orbit law along one strict subsequence.  The second conclusion records all
coordinate-cylinder masses explicitly. -/
theorem exists_empiricalOrbitMeasure_subseq
    (A : Set ℕ) (N : ℕ → ℕ) (hN : ∀ k, 0 < N k) :
    ∃ μ : ProbabilityMeasure DensityPattern, ∃ φ : ℕ → ℕ,
      StrictMono φ ∧
      Tendsto (fun k ↦ empiricalOrbitMeasure A (N (φ k)) (hN (φ k)))
        atTop (𝓝 μ) ∧
      ∀ i, Tendsto
        (fun k ↦ ((((Finset.range (N (φ k)) : Set ℕ) ∩
          orbitSet A i).ncard : ℕ) : ℝ≥0∞) / N (φ k))
        atTop
        (𝓝 (((μ : ProbabilityMeasure DensityPattern) : Measure DensityPattern)
          (patternEvent i))) := by
  let μs : ℕ → ProbabilityMeasure DensityPattern :=
    fun k ↦ empiricalOrbitMeasure A (N k) (hN k)
  obtain ⟨μ, φ, hφ, hμ⟩ := CompactSpace.tendsto_subseq μs
  refine ⟨μ, φ, hφ, hμ, fun i ↦ ?_⟩
  have hi := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hμ
    (by rw [(patternEvent_isClopen i).frontier_eq]; simp)
  convert hi using 1
  funext k
  dsimp [μs]
  rw [empiricalOrbitMeasure_event]

/-- The correspondence principle needed below, specialized to the exact
prefixes defining upper density.  It produces a shift-invariant probability
law on Cantor space whose zero-coordinate cylinder has mass precisely the
original upper density, while retaining the actual convergent empirical
subsequence that realizes the law. -/
theorem exists_invariant_orbitMeasure_realizing_upperDensity (A : Set ℕ) :
    ∃ N : ℕ → ℕ, ∃ hNpos : ∀ k, 0 < N k,
      ∃ μ : ProbabilityMeasure DensityPattern, ∃ φ : ℕ → ℕ,
        Tendsto N atTop atTop ∧ StrictMono φ ∧
        Tendsto (fun k ↦ empiricalOrbitMeasure A (N (φ k)) (hNpos (φ k)))
          atTop (𝓝 μ) ∧
        MeasurePreserving patternShift (μ : Measure DensityPattern) μ ∧
        (((μ : ProbabilityMeasure DensityPattern) : Measure DensityPattern)
          (patternEvent 0)).toReal = A.upperDensity := by
  obtain ⟨N, hNdensity, hNtop, hNpos⟩ := exists_prefix_realizing_upperDensity A
  obtain ⟨μ, φ, hφ, hμ, hcoord⟩ :=
    exists_empiricalOrbitMeasure_subseq A N hNpos
  have hNφtop : Tendsto (fun k ↦ N (φ k)) atTop atTop :=
    hNtop.comp hφ.injective.nat_tendsto_atTop
  have hinvariant :
      MeasurePreserving patternShift (μ : Measure DensityPattern) μ :=
    measurePreserving_patternShift_of_tendsto_empiricalOrbitMeasure
      A (fun k ↦ N (φ k)) (fun k ↦ hNpos (φ k)) hNφtop μ hμ
  have hcoordReal :
      Tendsto
        (fun k ↦ ENNReal.toReal
          (((((Finset.range (N (φ k)) : Set ℕ) ∩ orbitSet A 0).ncard : ℕ) : ℝ≥0∞) /
            (N (φ k) : ℝ≥0∞)))
        atTop
        (𝓝 ((((μ : ProbabilityMeasure DensityPattern) : Measure DensityPattern)
          (patternEvent 0)).toReal)) := by
    simpa only [Function.comp_def] using
      ((ENNReal.tendsto_toReal
        (measure_ne_top ((μ : ProbabilityMeasure DensityPattern) :
          Measure DensityPattern) (patternEvent 0))).comp (hcoord 0))
  have hdensitySubseq :
      Tendsto (fun k ↦ A.partialDensity Set.univ (N (φ k))) atTop
        (𝓝 A.upperDensity) :=
    hNdensity.comp hφ.injective.nat_tendsto_atTop
  have hrealEq :
      (fun k ↦ ENNReal.toReal
        (((((Finset.range (N (φ k)) : Set ℕ) ∩ orbitSet A 0).ncard : ℕ) : ℝ≥0∞) /
          (N (φ k) : ℝ≥0∞))) =
        (fun k ↦ A.partialDensity Set.univ (N (φ k))) := by
    funext k
    rw [show orbitSet A 0 = A by ext n; simp [orbitSet]]
    rw [ENNReal.toReal_div]
    · simp only [ENNReal.toReal_natCast]
      rw [← finsetDensity_range_eq_partialDensity]
      simp [finsetDensity]
  refine ⟨N, hNpos, μ, φ, hNtop, hφ, hμ, hinvariant, ?_⟩
  apply tendsto_nhds_unique hcoordReal
  rw [hrealEq]
  exact hdensitySubseq

/-- Bergelson's intersectivity lemma in the density form used by MRR.  A
uniform positive lower bound for each member of a countable family, measured
on finite sets whose cardinalities tend to infinity, yields an infinite
subfamily all of whose finite intersections are infinite. -/
theorem bergelson_finset
    (s : ℕ → Set ℕ) (F : ℕ → Finset ℕ) (hF : ∀ n, (F n).Nonempty)
    (r : ℝ≥0∞) (hr0 : r ≠ 0)
    (hr : ∀ i, ∀ᶠ n in atTop,
      r ≤ ((((F n : Set ℕ) ∩ s i).ncard : ℕ) : ℝ≥0∞) / (F n).card)
    (hcard : Tendsto (fun n => (F n).card) atTop atTop) :
    ∃ t : Set ℕ, t.Infinite ∧ ∀ ⦃u : Set ℕ⦄, u ⊆ t → u.Finite →
      (⋂ i ∈ u, s i).Infinite := by
  let μs : ℕ → ProbabilityMeasure DensityPattern :=
    fun n => empiricalPatternMeasure s (F n) (hF n)
  obtain ⟨μ, φ, hφ, hμ⟩ := CompactSpace.tendsto_subseq μs
  have hφtop : Tendsto φ atTop atTop := hφ.tendsto_atTop
  have hevent (i : ℕ) :
      Tendsto (fun n => ((μs (φ n) : ProbabilityMeasure DensityPattern) :
          Measure DensityPattern) (patternEvent i)) atTop
        (𝓝 (((μ : ProbabilityMeasure DensityPattern) : Measure DensityPattern)
          (patternEvent i))) := by
    exact ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hμ
      (by simp [patternEvent_isClopen i])
  have hrevent (i : ℕ) :
      r ≤ ((μ : ProbabilityMeasure DensityPattern) : Measure DensityPattern)
        (patternEvent i) := by
    apply ge_of_tendsto (hevent i)
    filter_upwards [hφtop (hr i)] with n hn
    simpa [μs, empiricalPatternMeasure_event] using hn
  obtain ⟨t, ht, hinter⟩ := bergelson
    (μ := ((μ : ProbabilityMeasure DensityPattern) : Measure DensityPattern))
    (s := patternEvent) (r := r)
    (fun i => (patternEvent_isClopen i).2.measurableSet) hr0 hrevent
  refine ⟨t, ht, ?_⟩
  intro u hut hu
  have hEU : IsClopen (⋂ i ∈ u, patternEvent i) :=
    hu.isClopen_biInter fun i _ => patternEvent_isClopen i
  have hpos : 0 < ((μ : ProbabilityMeasure DensityPattern) : Measure DensityPattern)
      (⋂ i ∈ u, patternEvent i) := hinter hut hu
  intro hD
  have hpre : membershipPattern s ⁻¹' (⋂ i ∈ u, patternEvent i) = ⋂ i ∈ u, s i := by
    ext x
    simp [patternEvent]
  have hmass :
      Tendsto
        (fun n => ((μs (φ n) : ProbabilityMeasure DensityPattern) :
          Measure DensityPattern) (⋂ i ∈ u, patternEvent i)) atTop
        (𝓝 (((μ : ProbabilityMeasure DensityPattern) : Measure DensityPattern)
          (⋂ i ∈ u, patternEvent i))) := by
    exact ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hμ
      (by simp [hEU])
  have hbound : ∀ n,
      ((μs (φ n) : ProbabilityMeasure DensityPattern) : Measure DensityPattern)
          (⋂ i ∈ u, patternEvent i) ≤
        ((⋂ i ∈ u, s i).ncard : ℝ≥0∞) / (F (φ n)).card := by
    intro n
    rw [show μs (φ n) = empiricalPatternMeasure s (F (φ n)) (hF (φ n)) by rfl,
      empiricalPatternMeasure_apply _ _ _ hEU.2.measurableSet, hpre]
    exact ENNReal.div_le_div_right (by
      exact_mod_cast Set.ncard_le_ncard inter_subset_right hD) _
  have hzero : Tendsto
      (fun n => ((μs (φ n) : ProbabilityMeasure DensityPattern) :
        Measure DensityPattern) (⋂ i ∈ u, patternEvent i)) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (show Tendsto (fun n => ((⋂ i ∈ u, s i).ncard : ℝ≥0∞) / (F (φ n)).card)
        atTop (𝓝 0) by
        simpa [div_eq_mul_inv, mul_comm] using
          ENNReal.Tendsto.mul_const
            (ENNReal.tendsto_inv_nat_nhds_zero.comp (hcard.comp hφtop))
            (.inr (ENNReal.natCast_ne_top (⋂ i ∈ u, s i).ncard)))
    · exact fun _ => bot_le
    · exact hbound
  have hz := tendsto_nhds_unique hmass hzero
  exact hpos.ne' hz

/-- The right translate `A - m`, written without truncated subtraction. -/
def shift (A : Set ℕ) (m : ℕ) : Set ℕ := {n | n + m ∈ A}

@[simp] theorem mem_shift {A : Set ℕ} {m n : ℕ} : n ∈ shift A m ↔ n + m ∈ A := Iff.rfl

@[simp] theorem shift_zero (A : Set ℕ) : shift A 0 = A := by
  ext n
  simp [shift]

theorem shift_add (A : Set ℕ) (m n : ℕ) : shift (shift A m) n = shift A (m + n) := by
  ext k
  simp [shift, add_assoc, add_comm m n]

/-- A finite rectangular approximation to the desired sumset.  `indices`
records indices in the candidate sequence `m`; `columns` records elements of
`L`. -/
structure RectangleStage (A L : Set ℕ) (m : ℕ → ℕ) where
  indices : Finset ℕ
  columns : Finset ℕ
  columns_mem : (columns : Set ℕ) ⊆ L
  cross_mem : ∀ i ∈ indices, ∀ c ∈ columns, m i + c ∈ A

namespace RectangleStage

variable {A L : Set ℕ} {m : ℕ → ℕ}

def empty : RectangleStage A L m where
  indices := ∅
  columns := ∅
  columns_mem := by simp
  cross_mem := by simp

/-- The two hypotheses used in the elementary rectangle construction.

* `leftRich` says that every finite family of rows has infinitely many
  common columns in `L`.
* `rightRich` says that every finite family of columns has a fresh row.

The analytic part of the MRR proof supplies exactly these two statements. -/
def LeftRich (A L : Set ℕ) (m : ℕ → ℕ) : Prop :=
  ∀ I : Finset ℕ, (L ∩ ⋂ i ∈ I, shift A (m i)).Infinite

def RightRich (A L : Set ℕ) (m : ℕ → ℕ) : Prop :=
  ∀ C : Finset ℕ, (C : Set ℕ) ⊆ L → ∀ I : Finset ℕ,
    ∃ i ∉ I, ∀ c ∈ C, m i + c ∈ A

theorem exists_extension (hleft : LeftRich A L m) (hright : RightRich A L m)
    (s : RectangleStage A L m) :
    ∃ t : RectangleStage A L m,
      s.indices ⊆ t.indices ∧ s.columns ⊆ t.columns ∧
      t.indices.card = s.indices.card + 1 ∧
      t.columns.card = s.columns.card + 1 := by
  classical
  have hinf := hleft s.indices
  have hfcols : (s.columns : Set ℕ).Finite := s.columns.finite_toSet
  obtain ⟨c, hc, hcn⟩ := (hinf.sdiff hfcols).nonempty
  have hcL : c ∈ L := hc.1
  have hcn' : c ∉ s.columns := by simpa using hcn
  obtain ⟨i, hin, hiA⟩ := hright (insert c s.columns) (by
    intro x hx
    simp only [Finset.coe_insert, Set.mem_insert_iff] at hx
    rcases hx with hxc | hx
    · exact hxc ▸ hcL
    · exact s.columns_mem (by simpa using hx)) s.indices
  refine ⟨{
    indices := insert i s.indices
    columns := insert c s.columns
    columns_mem := ?_
    cross_mem := ?_
  }, by simp, by simp, by simp [hin], by simp [hcn']⟩
  · intro x hx
    simp only [Finset.coe_insert, Set.mem_insert_iff] at hx
    rcases hx with hxc | hx
    · exact hxc ▸ hcL
    · exact s.columns_mem (by simpa using hx)
  · intro j hj x hx
    simp only [Finset.mem_insert] at hj hx
    rcases hj with rfl | hj
    · exact hiA x (by simpa using hx)
    · rcases hx with hxc | hx
      · subst x
        have hshift : c ∈ shift A (m j) := by
          exact (Set.mem_iInter₂.mp hc.2) j hj
        simpa [shift, add_comm] using hshift
      · exact s.cross_mem j hj x hx

noncomputable def next (hleft : LeftRich A L m) (hright : RightRich A L m)
    (s : RectangleStage A L m) : RectangleStage A L m :=
  Classical.choose (exists_extension hleft hright s)

theorem next_spec (hleft : LeftRich A L m) (hright : RightRich A L m)
    (s : RectangleStage A L m) :
    s.indices ⊆ (next hleft hright s).indices ∧
      s.columns ⊆ (next hleft hright s).columns ∧
      (next hleft hright s).indices.card = s.indices.card + 1 ∧
      (next hleft hright s).columns.card = s.columns.card + 1 :=
  Classical.choose_spec (exists_extension hleft hright s)

noncomputable def stages (hleft : LeftRich A L m) (hright : RightRich A L m) :
    ℕ → RectangleStage A L m
  | 0 => empty
  | n + 1 => next hleft hright (stages hleft hright n)

@[simp] theorem stages_zero (hleft : LeftRich A L m) (hright : RightRich A L m) :
    stages hleft hright 0 = empty := rfl

@[simp] theorem stages_succ (hleft : LeftRich A L m) (hright : RightRich A L m)
    (n : ℕ) : stages hleft hright (n + 1) =
      next hleft hright (stages hleft hright n) := rfl

theorem indices_card_stages (hleft : LeftRich A L m) (hright : RightRich A L m) :
    ∀ n, (stages hleft hright n).indices.card = n := by
  intro n
  induction n with
  | zero => simp [empty]
  | succ n ih =>
      rw [stages_succ, (next_spec hleft hright _).2.2.1, ih]

theorem columns_card_stages (hleft : LeftRich A L m) (hright : RightRich A L m) :
    ∀ n, (stages hleft hright n).columns.card = n := by
  intro n
  induction n with
  | zero => simp [empty]
  | succ n ih =>
      rw [stages_succ, (next_spec hleft hright _).2.2.2, ih]

theorem indices_mono_succ (hleft : LeftRich A L m) (hright : RightRich A L m)
    (n : ℕ) : (stages hleft hright n).indices ⊆
      (stages hleft hright (n + 1)).indices := by
  rw [stages_succ]
  exact (next_spec hleft hright _).1

theorem columns_mono_succ (hleft : LeftRich A L m) (hright : RightRich A L m)
    (n : ℕ) : (stages hleft hright n).columns ⊆
      (stages hleft hright (n + 1)).columns := by
  rw [stages_succ]
  exact (next_spec hleft hright _).2.1

theorem indices_mono (hleft : LeftRich A L m) (hright : RightRich A L m)
    {a b : ℕ} (hab : a ≤ b) : (stages hleft hright a).indices ⊆
      (stages hleft hright b).indices := by
  induction b, hab using Nat.le_induction with
  | base => exact Finset.Subset.rfl
  | succ b _ ih => exact ih.trans (indices_mono_succ hleft hright b)

theorem columns_mono (hleft : LeftRich A L m) (hright : RightRich A L m)
    {a b : ℕ} (hab : a ≤ b) : (stages hleft hright a).columns ⊆
      (stages hleft hright b).columns := by
  induction b, hab using Nat.le_induction with
  | base => exact Finset.Subset.rfl
  | succ b _ ih => exact ih.trans (columns_mono_succ hleft hright b)

end RectangleStage

open RectangleStage

/-- The elementary extraction used at the end of MRR (and of Host's proof):
two compatible one-sided richness statements produce an infinite complete
rectangle in the sum graph of `A`. -/
theorem exists_infinite_add_subset_of_rich
    {A L : Set ℕ} {m : ℕ → ℕ} (hm : Injective m)
    (hleft : LeftRich A L m) (hright : RightRich A L m) :
    ∃ B C : Set ℕ, B.Infinite ∧ C.Infinite ∧ B + C ⊆ A := by
  classical
  let S : ℕ → RectangleStage A L m := stages hleft hright
  let B : Set ℕ := {b | ∃ n i, i ∈ (S n).indices ∧ b = m i}
  let C : Set ℕ := {c | ∃ n, c ∈ (S n).columns}
  have hBinf : B.Infinite := by
    intro hBfin
    let n := hBfin.toFinset.card + 1
    have hsub : (S n).indices.image m ⊆ hBfin.toFinset := by
      intro b hb
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hb
      exact hBfin.mem_toFinset.mpr ⟨n, i, hi, rfl⟩
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_image_iff.mpr hm.injOn, show (S n).indices.card = n from
      indices_card_stages hleft hright n] at hcard
    omega
  have hCinf : C.Infinite := by
    intro hCfin
    let n := hCfin.toFinset.card + 1
    have hsub : (S n).columns ⊆ hCfin.toFinset := by
      intro c hc
      exact hCfin.mem_toFinset.mpr ⟨n, hc⟩
    have hcard := Finset.card_le_card hsub
    rw [show (S n).columns.card = n from columns_card_stages hleft hright n] at hcard
    omega
  refine ⟨B, C, hBinf, hCinf, ?_⟩
  intro x hx
  obtain ⟨b, hb, c, hc, rfl⟩ := Set.mem_add.mp hx
  obtain ⟨nb, i, hi, rfl⟩ := hb
  obtain ⟨nc, hc⟩ := hc
  let n := max nb nc
  have hi' : i ∈ (S n).indices :=
    indices_mono hleft hright (Nat.le_max_left _ _) hi
  have hc' : c ∈ (S n).columns :=
    columns_mono hleft hright (Nat.le_max_right _ _) hc
  exact (S n).cross_mem i hi' c hc'

/-- The complete combinatorial/density reduction.  It packages the use of
`bergelson_finset`: uniform positive densities supply `LeftRich`, while an
eventual row condition supplies `RightRich`, and the rectangle construction
then gives the two infinite summands. -/
theorem exists_infinite_add_subset_of_density
    {A L : Set ℕ} {m : ℕ → ℕ} (hm : Injective m)
    (F : ℕ → Finset ℕ) (hF : ∀ n, (F n).Nonempty)
    (hcard : Tendsto (fun n => (F n).card) atTop atTop)
    (r : ℝ≥0∞) (hr0 : r ≠ 0)
    (hleft : ∀ i, ∀ᶠ n in atTop,
      r ≤ ((((F n : Set ℕ) ∩ (L ∩ shift A (m i))).ncard : ℕ) : ℝ≥0∞) /
        (F n).card)
    (hright : ∀ C : Finset ℕ, (C : Set ℕ) ⊆ L →
      ∀ᶠ i in atTop, ∀ c ∈ C, m i + c ∈ A) :
    ∃ B C : Set ℕ, B.Infinite ∧ C.Infinite ∧ B + C ⊆ A := by
  classical
  obtain ⟨t, ht, htinter⟩ := bergelson_finset
    (fun i => L ∩ shift A (m i)) F hF r hr0 hleft hcard
  let : Infinite t := ht.to_subtype
  let e : ℕ → ℕ := fun n => (Infinite.natEmbedding t n : ℕ)
  have he : Injective e := Subtype.val_injective.comp (Infinite.natEmbedding t).injective
  have het (n : ℕ) : e n ∈ t := (Infinite.natEmbedding t n).property
  let m' : ℕ → ℕ := m ∘ e
  have hm' : Injective m' := hm.comp he
  have hleft' : LeftRich A L m' := by
    intro I
    let u : Set ℕ := e '' ((I : Set ℕ) ∪ {0})
    have hu_t : u ⊆ t := by
      rintro _ ⟨i, -, rfl⟩
      exact het i
    have hu_fin : u.Finite :=
      ((I.finite_toSet.union (finite_singleton 0)).image e)
    have hu_inf := htinter hu_t hu_fin
    apply hu_inf.mono
    intro x hx
    have hxall := Set.mem_iInter₂.mp hx
    constructor
    · exact (hxall (e 0) ⟨0, by simp⟩).1
    · apply Set.mem_iInter₂.mpr
      intro i hi
      exact (hxall (e i) ⟨i, by simp [hi]⟩).2
  have hright' : RightRich A L m' := by
    intro C hCL I
    have hev : ∀ᶠ i in atTop, ∀ c ∈ C, m' i + c ∈ A := by
      exact he.nat_tendsto_atTop (hright C hCL)
    rw [eventually_atTop] at hev
    obtain ⟨N, hN⟩ := hev
    by_cases hI : I.Nonempty
    · let i := max N (I.max' hI + 1)
      have hiN : N ≤ i := Nat.le_max_left _ _
      have hiI : i ∉ I := by
        intro hi
        have himax : i ≤ I.max' hI := Finset.le_max' I i hi
        dsimp [i] at himax
        omega
      exact ⟨i, hiI, hN i hiN⟩
    · have hIempty : I = ∅ := Finset.not_nonempty_iff_eq_empty.mp hI
      exact ⟨N, by simp [hIempty], hN N le_rfl⟩
  exact exists_infinite_add_subset_of_rich hm' hleft' hright'

/-! ## An invariant regular law on the Stone–Čech compactification -/

local instance : Add (Ultrafilter ℕ) := Ultrafilter.add
local instance : AddSemigroup (Ultrafilter ℕ) := Ultrafilter.addSemigroup
local instance : MeasurableSpace (Ultrafilter ℕ) := borel (Ultrafilter ℕ)
local instance : BorelSpace (Ultrafilter ℕ) := ⟨rfl⟩

abbrev BetaNat := Ultrafilter ℕ

def betaShift (p : BetaNat) : BetaNat := p + pure 1

theorem continuous_betaShift : Continuous betaShift := by
  exact Ultrafilter.continuous_add_left (pure 1)

theorem betaShift_pure (n : ℕ) : betaShift (pure n) = pure (n + 1) := by
  rfl

noncomputable def betaMembership (A : Set ℕ) : C(BetaNat, Bool) := by
  classical
  exact ⟨Ultrafilter.extend (fun n ↦ decide (n ∈ A)),
    continuous_ultrafilter_extend _⟩

noncomputable def betaIndicator (A : Set ℕ) : C(BetaNat, ℝ) :=
  ⟨fun p ↦ if betaMembership A p then 1 else 0,
    (show Continuous (fun b : Bool ↦ if b then (1 : ℝ) else 0) from
      continuous_of_discreteTopology).comp (betaMembership A).continuous⟩

@[simp] theorem betaMembership_eq_true_iff (A : Set ℕ) (p : BetaNat) :
    betaMembership A p = true ↔ A ∈ (p : Filter ℕ) := by
  classical
  unfold betaMembership
  change Ultrafilter.extend (fun n ↦ decide (n ∈ A)) p = true ↔ A ∈ (p : Filter ℕ)
  rw [ultrafilter_extend_eq_iff, nhds_discrete, Filter.le_pure_iff]
  have hpre : (fun n ↦ decide (n ∈ A)) ⁻¹' ({true} : Set Bool) = A := by
    ext n
    simp
  change (fun n ↦ decide (n ∈ A)) ⁻¹' ({true} : Set Bool) ∈ (p : Filter ℕ) ↔
    A ∈ (p : Filter ℕ)
  rw [hpre]

@[simp] theorem betaIndicator_apply_of_mem (A : Set ℕ) (p : BetaNat)
    (hA : A ∈ (p : Filter ℕ)) : betaIndicator A p = 1 := by
  simp [betaIndicator, hA]

@[simp] theorem betaIndicator_apply_of_not_mem (A : Set ℕ) (p : BetaNat)
    (hA : A ∉ (p : Filter ℕ)) : betaIndicator A p = 0 := by
  simp [betaIndicator, hA]

noncomputable def natIndicator (A : Set ℕ) (n : ℕ) : ℝ := by
  classical
  exact if n ∈ A then 1 else 0

@[simp] theorem natIndicator_eq_realIndicator (A : Set ℕ) (n : ℕ) :
    natIndicator A n = realIndicator A n := by
  rfl

@[simp] theorem betaIndicator_pure (A : Set ℕ) (n : ℕ) :
    betaIndicator A (pure n) = natIndicator A n := by
  classical
  simp [betaIndicator, betaMembership, natIndicator]

noncomputable def betaEmpirical (N : ℕ) (hN : 0 < N) : ProbabilityMeasure BetaNat :=
  ⟨((PMF.uniformOfFinset (Finset.range N) (by simpa using hN.ne')).map pure).toMeasure,
    inferInstance⟩

theorem integral_betaEmpirical (N : ℕ) (hN : 0 < N) (f : C(BetaNat, ℝ)) :
    ∫ x, f x ∂((betaEmpirical N hN : ProbabilityMeasure BetaNat) : Measure BetaNat) =
      (∑ n ∈ Finset.range N, f (pure n)) / N := by
  classical
  let p := PMF.uniformOfFinset (Finset.range N) (by simpa using hN.ne')
  have hp : Integrable (fun n ↦ f (pure n)) p.toMeasure := by
    let fp : BoundedContinuousFunction ℕ ℝ :=
      (BoundedContinuousFunction.mkOfCompact f).compContinuous
      ⟨pure, continuous_of_discreteTopology⟩
    exact BoundedContinuousFunction.integrable p.toMeasure fp
  change ∫ x, f x ∂((p.map pure).toMeasure) = _
  rw [← PMF.toMeasure_map (f := pure) p (measurable_of_countable _)]
  rw [MeasureTheory.integral_map (measurable_of_countable _).aemeasurable
    f.continuous.aestronglyMeasurable]
  rw [PMF.integral_eq_tsum p (fun n ↦ f (pure n)) hp]
  rw [tsum_eq_sum (s := Finset.range N)]
  · calc
      (∑ x ∈ Finset.range N, (p x).toReal • f (pure x)) =
          ((N : ℝ≥0∞)⁻¹).toReal * ∑ x ∈ Finset.range N, f (pure x) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x hx
        rw [show p x = (N : ℝ≥0∞)⁻¹ by simp [p, hx]]
        rfl
      _ = (∑ n ∈ Finset.range N, f (pure n)) / N := by
        simp only [ENNReal.toReal_inv, ENNReal.toReal_natCast]
        rw [div_eq_mul_inv]
        ring
  · intro n hn
    simp [p, PMF.uniformOfFinset_apply, hn]

theorem sum_range_shift_beta (N : ℕ) (f : C(BetaNat, ℝ)) :
    (∑ n ∈ Finset.range N, f (betaShift (pure n))) =
      (∑ n ∈ Finset.range N, f (pure n)) + f (pure N) - f (pure 0) := by
  simpa [betaShift_pure] using
    (by
      have h := Finset.sum_range_succ' (fun n ↦ f (pure n)) N
      rw [Finset.sum_range_succ] at h
      linarith)

theorem tendsto_beta_endpoint_error
    {L : Filter ℕ} [NeBot L] (N : ℕ → ℕ) (hN : Tendsto N L atTop)
    (f : BetaNat →ᵇ ℝ) :
    Tendsto (fun k ↦ (f (pure (N k)) - f (pure 0)) / (N k : ℝ)) L (𝓝 0) := by
  apply tendsto_bdd_div_atTop_nhds_zero (b := -2 * ‖f‖) (B := 2 * ‖f‖)
  · exact Eventually.of_forall fun k ↦ by
      have h₁ := f.norm_coe_le_norm (pure (N k))
      have h₂ := f.norm_coe_le_norm (pure 0)
      simp only [Real.norm_eq_abs] at h₁ h₂
      rcases abs_le.mp h₁ with ⟨h₁l, h₁u⟩
      rcases abs_le.mp h₂ with ⟨h₂l, h₂u⟩
      linarith
  · exact Eventually.of_forall fun k ↦ by
      have h₁ := f.norm_coe_le_norm (pure (N k))
      have h₂ := f.norm_coe_le_norm (pure 0)
      simp only [Real.norm_eq_abs] at h₁ h₂
      rcases abs_le.mp h₁ with ⟨h₁l, h₁u⟩
      rcases abs_le.mp h₂ with ⟨h₂l, h₂u⟩
      linarith
  · exact (tendsto_natCast_atTop_atTop (R := ℝ)).comp hN

theorem integral_map_betaEmpirical (N : ℕ) (hN : 0 < N)
    (f : BetaNat →ᵇ ℝ) :
    ∫ x, f x ∂(((betaEmpirical N hN).map
        continuous_betaShift.measurable.aemeasurable : ProbabilityMeasure BetaNat) : Measure BetaNat) =
      (∫ x, f x ∂((betaEmpirical N hN : ProbabilityMeasure BetaNat) : Measure BetaNat)) +
        (f (pure N) - f (pure 0)) / N := by
  rw [ProbabilityMeasure.toMeasure_map]
  rw [MeasureTheory.integral_map continuous_betaShift.measurable.aemeasurable
    f.continuous.aestronglyMeasurable]
  let sf : C(BetaNat, ℝ) := f.toContinuousMap.comp ⟨betaShift, continuous_betaShift⟩
  change (∫ x, sf x ∂((betaEmpirical N hN : ProbabilityMeasure BetaNat) : Measure BetaNat)) = _
  have hf :
      (∫ x, f x ∂((betaEmpirical N hN : ProbabilityMeasure BetaNat) : Measure BetaNat)) =
        (∑ n ∈ Finset.range N, f (pure n)) / N := by
    simpa using integral_betaEmpirical N hN f.toContinuousMap
  rw [integral_betaEmpirical N hN sf, hf]
  change ((∑ n ∈ Finset.range N, f (betaShift (pure n))) / N) = _
  have hs := sum_range_shift_beta N f.toContinuousMap
  change (∑ n ∈ Finset.range N, f (betaShift (pure n))) = _ at hs
  rw [hs]
  change
    ((∑ n ∈ Finset.range N, f.toContinuousMap (pure n)) +
        f.toContinuousMap (pure N) - f.toContinuousMap (pure 0)) / (N : ℝ) =
      (∑ n ∈ Finset.range N, f.toContinuousMap (pure n)) / (N : ℝ) +
        (f.toContinuousMap (pure N) - f.toContinuousMap (pure 0)) / (N : ℝ)
  ring

noncomputable def regularizeBetaMeasure (μ : ProbabilityMeasure BetaNat) : Measure BetaNat :=
  RealRMK.rieszMeasure
    (CompactlySupportedContinuousMap.integralPositiveLinearMap (μ : Measure BetaNat))

theorem regular_regularizeBetaMeasure (μ : ProbabilityMeasure BetaNat) :
    (regularizeBetaMeasure μ).Regular := by
  unfold regularizeBetaMeasure
  infer_instance

theorem integral_regularizeBetaMeasure (μ : ProbabilityMeasure BetaNat)
    (f : C(BetaNat, ℝ)) :
    ∫ x, f x ∂regularizeBetaMeasure μ = ∫ x, f x ∂(μ : Measure BetaNat) := by
  let fc : C_c(BetaNat, ℝ) :=
    { toFun := f
      hasCompactSupport' := HasCompactSupport.of_compactSpace f }
  simpa [regularizeBetaMeasure, fc] using
    (RealRMK.integral_rieszMeasure
      (CompactlySupportedContinuousMap.integralPositiveLinearMap (μ : Measure BetaNat)) fc)

theorem regularizeBetaMeasure_univ (μ : ProbabilityMeasure BetaNat) :
    regularizeBetaMeasure μ univ = 1 := by
  let : (regularizeBetaMeasure μ).Regular := regular_regularizeBetaMeasure μ
  let one : C(BetaNat, ℝ) := 1
  have h := integral_regularizeBetaMeasure μ one
  rw [show (∫ x, one x ∂regularizeBetaMeasure μ) =
      (regularizeBetaMeasure μ univ).toReal by simp [one, integral_const, measureReal_def]] at h
  have hright : (∫ x, one x ∂(μ : Measure BetaNat)) = 1 := by
    simp [one, integral_const]
  rw [hright] at h
  exact (ENNReal.toReal_eq_one_iff _).mp h

noncomputable def regularizeBetaProbability
    (μ : ProbabilityMeasure BetaNat) : ProbabilityMeasure BetaNat :=
  ⟨regularizeBetaMeasure μ, ⟨regularizeBetaMeasure_univ μ⟩⟩

theorem regular_regularizeBetaProbability (μ : ProbabilityMeasure BetaNat) :
    ((regularizeBetaProbability μ : ProbabilityMeasure BetaNat) : Measure BetaNat).Regular := by
  exact regular_regularizeBetaMeasure μ

theorem integral_regularizeBetaProbability (μ : ProbabilityMeasure BetaNat)
    (f : C(BetaNat, ℝ)) :
    ∫ x, f x ∂((regularizeBetaProbability μ : ProbabilityMeasure BetaNat) : Measure BetaNat) =
      ∫ x, f x ∂(μ : Measure BetaNat) := by
  exact integral_regularizeBetaMeasure μ f

theorem exists_invariant_betaLimit
    (N : ℕ → ℕ) (hNpos : ∀ k, 0 < N k) (hNtop : Tendsto N atTop atTop) :
    ∃ q : Ultrafilter ℕ, (q : Filter ℕ) ≤ atTop ∧
      ∃ μ : ProbabilityMeasure BetaNat,
        ((μ : Measure BetaNat).Regular) ∧
        Tendsto (fun k ↦ betaEmpirical (N k) (hNpos k)) (q : Filter ℕ) (𝓝 μ) ∧
        MeasurePreserving betaShift (μ : Measure BetaNat) μ := by
  let : (atTop : Filter ℕ).NeBot := inferInstance
  obtain ⟨q, hq⟩ := Ultrafilter.exists_le (atTop : Filter ℕ)
  let μs : ℕ → ProbabilityMeasure BetaNat :=
    fun k ↦ betaEmpirical (N k) (hNpos k)
  let Q : Ultrafilter (ProbabilityMeasure BetaNat) := q.map μs
  obtain ⟨μ₀, -, hμ₀⟩ := isCompact_univ.ultrafilter_le_nhds Q (by simp)
  have hμs₀ : Tendsto μs (q : Filter ℕ) (𝓝 μ₀) := by
    change map μs (q : Filter ℕ) ≤ 𝓝 μ₀
    simpa [Q] using hμ₀
  let μ : ProbabilityMeasure BetaNat := regularizeBetaProbability μ₀
  have hμreg : (μ : Measure BetaNat).Regular := by
    exact regular_regularizeBetaProbability μ₀
  have hμs : Tendsto μs (q : Filter ℕ) (𝓝 μ) := by
    rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
    intro f
    have h :=
      (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hμs₀) f
    convert h using 1
    simpa [μ] using (integral_regularizeBetaProbability μ₀ f.toContinuousMap)
  refine ⟨q, hq, μ, hμreg, hμs, ?_⟩
  have hNq : Tendsto N (q : Filter ℕ) atTop := hNtop.mono_left hq
  have hmap :
    Tendsto (fun k ↦ (μs k).map continuous_betaShift.measurable.aemeasurable)
        (q : Filter ℕ) (𝓝 (μ.map continuous_betaShift.measurable.aemeasurable)) :=
    ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
      μs μ hμs continuous_betaShift
  have hsame :
    Tendsto (fun k ↦ (μs k).map continuous_betaShift.measurable.aemeasurable)
        (q : Filter ℕ) (𝓝 μ) := by
    rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
    intro f
    have horig :=
      (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hμs) f
    have herr := tendsto_beta_endpoint_error N hNq f
    have hsum := horig.add herr
    convert hsum using 1
    · funext k
      exact integral_map_betaEmpirical (N k) (hNpos k) f
    · simp
  let : (μ : Measure BetaNat).Regular := hμreg
  let : (Measure.map betaShift (μ : Measure BetaNat)).InnerRegular :=
    Measure.InnerRegular.map_of_continuous continuous_betaShift
  let : IsProbabilityMeasure (Measure.map betaShift (μ : Measure BetaNat)) :=
    Measure.isProbabilityMeasure_map continuous_betaShift.measurable.aemeasurable
  have heq : Measure.map betaShift (μ : Measure BetaNat) = (μ : Measure BetaNat) := by
    apply Measure.ext_of_integral_eq_on_compactlySupported
    intro f
    let fb : BetaNat →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact f.toContinuousMap
    have hmapf :=
      (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hmap) fb
    have hsamef :=
      (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hsame) fb
    have hf := tendsto_nhds_unique hmapf hsamef
    simpa [ProbabilityMeasure.toMeasure_map, fb] using hf
  refine ⟨continuous_betaShift.measurable, ?_⟩
  exact heq

abbrev BetaTest := C(BetaNat, ℝ)
abbrev BetaFunctional := WeakDual ℝ BetaTest

local instance : LocallyConvexSpace ℝ BetaFunctional :=
  (WeakDual.withSeminorms ℝ BetaTest).toLocallyConvexSpace
noncomputable def betaIntegralFunctional (μ : Measure BetaNat) [IsProbabilityMeasure μ] :
    StrongDual ℝ BetaTest :=
  LinearMap.mkContinuous
    { toFun := fun f ↦ ∫ x, f x ∂μ
      map_add' := fun f g ↦ by
        let fb : BetaNat →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact f
        let gb : BetaNat →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact g
        simpa [fb, gb] using integral_add (fb.integrable μ) (gb.integrable μ)
      map_smul' := fun c f ↦ by simpa using integral_smul c f }
    1 (fun f ↦ by
      let fb : BetaNat →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact f
      simpa [fb] using fb.norm_integral_le_norm μ)

@[simp] theorem betaIntegralFunctional_apply (μ : Measure BetaNat)
    [IsProbabilityMeasure μ] (f : BetaTest) :
    betaIntegralFunctional μ f = ∫ x, f x ∂μ := rfl

noncomputable def betaIntegralWeakFunctional (μ : Measure BetaNat) [IsProbabilityMeasure μ] :
    BetaFunctional := StrongDual.toWeakDual (betaIntegralFunctional μ)

@[simp] theorem betaIntegralWeakFunctional_apply (μ : Measure BetaNat)
    [IsProbabilityMeasure μ] (f : BetaTest) :
    betaIntegralWeakFunctional μ f = ∫ x, f x ∂μ := rfl

noncomputable def betaShiftTest (f : BetaTest) : BetaTest :=
  f.comp ⟨betaShift, continuous_betaShift⟩

@[simp] theorem betaShiftTest_apply (f : BetaTest) (p : BetaNat) :
    betaShiftTest f p = f (betaShift p) := rfl

def betaInvariantStates : Set BetaFunctional :=
  {Λ | Λ 1 = 1 ∧
    (∀ f : BetaTest, (∀ x, 0 ≤ f x) → 0 ≤ Λ f) ∧
    ∀ f : BetaTest, Λ (betaShiftTest f) = Λ f}

theorem betaInvariantStates_norm_le_one {Λ : BetaFunctional}
    (hΛ : Λ ∈ betaInvariantStates) : ‖WeakDual.toStrongDual Λ‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound (WeakDual.toStrongDual Λ) zero_le_one
  intro f
  have hupper_nonneg : ∀ x, 0 ≤ (‖f‖ : ℝ) • (1 : BetaTest) x - f x := by
    intro x
    have hx : |f x| ≤ ‖f‖ := by
      simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm x
    simpa only [ContinuousMap.one_apply, smul_eq_mul, mul_one] using
      sub_nonneg.mpr ((le_abs_self (f x)).trans hx)
  have hlower_nonneg : ∀ x, 0 ≤ (‖f‖ : ℝ) • (1 : BetaTest) x + f x := by
    intro x
    have hx : |f x| ≤ ‖f‖ := by
      simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm x
    have hsum : 0 ≤ ‖f‖ + f x := by linarith [neg_le_of_abs_le hx]
    simpa only [ContinuousMap.one_apply, smul_eq_mul, mul_one] using hsum
  have hupper := hΛ.2.1 ((‖f‖ : ℝ) • (1 : BetaTest) - f) hupper_nonneg
  have hlower := hΛ.2.1 ((‖f‖ : ℝ) • (1 : BetaTest) + f) hlower_nonneg
  have hΛone : Λ (1 : BetaTest) = 1 := hΛ.1
  simp only [map_sub, map_smul, hΛone, smul_eq_mul, mul_one, map_add] at hupper hlower
  rw [WeakDual.toStrongDual_apply, one_mul, Real.norm_eq_abs]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem betaInvariantStates_isBounded : Bornology.IsBounded betaInvariantStates := by
  change Bornology.IsBounded
    (WeakDual.toStrongDual ⁻¹' {Λ : StrongDual ℝ BetaTest |
      StrongDual.toWeakDual Λ ∈ betaInvariantStates})
  rw [WeakDual.isBounded_toStrongDual_preimage_iff_isBounded,
    isBounded_iff_forall_norm_le]
  exact ⟨1, fun Λ hΛ ↦ betaInvariantStates_norm_le_one hΛ⟩

theorem betaInvariantStates_isClosed : IsClosed betaInvariantStates := by
  have hnorm : IsClosed {Λ : BetaFunctional | Λ (1 : BetaTest) = 1} :=
    isClosed_eq (WeakDual.eval_continuous _) continuous_const
  have hpos : IsClosed {Λ : BetaFunctional |
      ∀ f : BetaTest, (∀ x, 0 ≤ f x) → 0 ≤ Λ f} := by
    classical
    rw [show {Λ : BetaFunctional |
        ∀ f : BetaTest, (∀ x, 0 ≤ f x) → 0 ≤ Λ f} =
        ⋂ f : BetaTest, if ∀ x, 0 ≤ f x then {Λ : BetaFunctional | 0 ≤ Λ f} else univ by
      ext Λ
      simp]
    apply isClosed_iInter
    intro f
    by_cases hf : ∀ x, 0 ≤ f x
    · rw [if_pos hf]
      change IsClosed ((fun Λ : BetaFunctional ↦ Λ f) ⁻¹' Ici 0)
      exact isClosed_Ici.preimage (WeakDual.eval_continuous f)
    · rw [if_neg hf]
      exact isClosed_univ
  have hinv : IsClosed {Λ : BetaFunctional |
      ∀ f : BetaTest, Λ (betaShiftTest f) = Λ f} := by
    simp only [setOf_forall]
    exact isClosed_iInter fun f ↦
      isClosed_eq (WeakDual.eval_continuous _) (WeakDual.eval_continuous _)
  rw [show betaInvariantStates = ({Λ : BetaFunctional | Λ (1 : BetaTest) = 1} ∩
    ({Λ : BetaFunctional | ∀ f : BetaTest, (∀ x, 0 ≤ f x) → 0 ≤ Λ f} ∩
    {Λ : BetaFunctional | ∀ f : BetaTest, Λ (betaShiftTest f) = Λ f})) by
      ext Λ; simp [betaInvariantStates]]
  exact hnorm.inter (hpos.inter hinv)

theorem betaInvariantStates_isCompact : IsCompact betaInvariantStates :=
  WeakDual.isCompact_of_bounded_of_closed betaInvariantStates_isBounded
    betaInvariantStates_isClosed

theorem betaIntegralWeakFunctional_mem (μ : Measure BetaNat)
    [IsProbabilityMeasure μ] (hμ : MeasurePreserving betaShift μ μ) :
    betaIntegralWeakFunctional μ ∈ betaInvariantStates := by
  refine ⟨?_, ?_, ?_⟩
  · simp [betaIntegralWeakFunctional_apply, integral_const]
  · intro f hf
    exact integral_nonneg_of_ae (Eventually.of_forall hf)
  · intro f
    rw [betaIntegralWeakFunctional_apply, betaIntegralWeakFunctional_apply]
    change (∫ x, f (betaShift x) ∂μ) = ∫ x, f x ∂μ
    rw [← MeasureTheory.integral_map continuous_betaShift.measurable.aemeasurable
      f.continuous.aestronglyMeasurable, hμ.map_eq]

theorem betaInvariantStates_convex : Convex ℝ betaInvariantStates := by
  intro Λ hΛ Γ hΓ a b ha hb hab
  change Λ (1 : BetaTest) = 1 ∧ _ ∧ _ at hΛ
  change Γ (1 : BetaTest) = 1 ∧ _ ∧ _ at hΓ
  change (a • Λ + b • Γ) (1 : BetaTest) = 1 ∧ _ ∧ _
  refine ⟨?_, ?_, ?_⟩
  · change a * Λ (1 : BetaTest) + b * Γ (1 : BetaTest) = 1
    rw [hΛ.1, hΓ.1]
    linarith
  · intro f hf
    change 0 ≤ a * Λ f + b * Γ f
    exact add_nonneg (mul_nonneg ha (hΛ.2.1 f hf)) (mul_nonneg hb (hΓ.2.1 f hf))
  · intro f
    change a * Λ (betaShiftTest f) + b * Γ (betaShiftTest f) =
      a * Λ f + b * Γ f
    rw [hΛ.2.2 f, hΓ.2.2 f]

noncomputable def betaEvalFunctional (f : BetaTest) : StrongDual ℝ BetaFunctional where
  toFun Λ := Λ f
  map_add' Λ Γ := by rfl
  map_smul' c Λ := by rfl
  cont := WeakDual.eval_continuous f

@[simp] theorem betaEvalFunctional_apply (f : BetaTest) (Λ : BetaFunctional) :
    betaEvalFunctional f Λ = Λ f := rfl

noncomputable def betaMaxFace (f : BetaTest) : Set BetaFunctional :=
  (betaEvalFunctional f).toExposed betaInvariantStates

theorem betaMaxFace_isExposed (f : BetaTest) :
    IsExposed ℝ betaInvariantStates (betaMaxFace f) :=
  ContinuousLinearMap.toExposed.isExposed

theorem betaMaxFace_nonempty (f : BetaTest) (hstates : betaInvariantStates.Nonempty) :
    (betaMaxFace f).Nonempty := by
  obtain ⟨Λ, hΛ, hmax⟩ := betaInvariantStates_isCompact.exists_isMaxOn hstates
    (betaEvalFunctional f).continuous.continuousOn
  exact ⟨Λ, hΛ, hmax⟩

theorem exists_extreme_betaInvariantState_ge (f : BetaTest)
    {Λ₀ : BetaFunctional} (hΛ₀ : Λ₀ ∈ betaInvariantStates) :
    ∃ Λ : BetaFunctional,
      Λ ∈ extremePoints ℝ betaInvariantStates ∧ Λ₀ f ≤ Λ f := by
  have hstates : betaInvariantStates.Nonempty := ⟨Λ₀, hΛ₀⟩
  have hface : (betaMaxFace f).Nonempty := betaMaxFace_nonempty f hstates
  have hface_compact : IsCompact (betaMaxFace f) :=
    (betaMaxFace_isExposed f).isCompact betaInvariantStates_isCompact
  obtain ⟨Λ, hΛext⟩ := hface_compact.extremePoints_nonempty hface
  have hΛext_states : Λ ∈ extremePoints ℝ betaInvariantStates :=
    (betaMaxFace_isExposed f).isExtreme.extremePoints_subset_extremePoints hΛext
  refine ⟨Λ, hΛext_states, ?_⟩
  exact hΛext.1.2 Λ₀ hΛ₀

noncomputable def betaStatePositiveFunctional (Λ : BetaFunctional)
    (hΛ : Λ ∈ betaInvariantStates) : C_c(BetaNat, ℝ) →ₚ[ℝ] ℝ where
  toFun f := Λ f.toContinuousMap
  map_add' f g := by
    change Λ ((f + g).toContinuousMap) = Λ f.toContinuousMap + Λ g.toContinuousMap
    rw [show (f + g).toContinuousMap = f.toContinuousMap + g.toContinuousMap by
      ext x
      rfl]
    exact map_add Λ f.toContinuousMap g.toContinuousMap
  map_smul' c f := by
    change Λ ((c • f).toContinuousMap) = c • Λ f.toContinuousMap
    rw [show (c • f).toContinuousMap = c • f.toContinuousMap by
      ext x
      rfl]
    exact map_smul Λ c f.toContinuousMap
  monotone' f g hfg := by
    have hnonneg : ∀ x, 0 ≤ (g.toContinuousMap - f.toContinuousMap) x := by
      intro x
      exact sub_nonneg.mpr (hfg x)
    have h := hΛ.2.1 (g.toContinuousMap - f.toContinuousMap) hnonneg
    simpa only [map_sub, sub_nonneg] using h

noncomputable def betaStateMeasure (Λ : BetaFunctional)
    (hΛ : Λ ∈ betaInvariantStates) : Measure BetaNat :=
  RealRMK.rieszMeasure (betaStatePositiveFunctional Λ hΛ)

theorem regular_betaStateMeasure (Λ : BetaFunctional)
    (hΛ : Λ ∈ betaInvariantStates) : (betaStateMeasure Λ hΛ).Regular := by
  unfold betaStateMeasure
  infer_instance

theorem integral_betaStateMeasure (Λ : BetaFunctional)
    (hΛ : Λ ∈ betaInvariantStates) (f : BetaTest) :
    ∫ x, f x ∂betaStateMeasure Λ hΛ = Λ f := by
  let fc : C_c(BetaNat, ℝ) :=
    { toFun := f
      hasCompactSupport' := HasCompactSupport.of_compactSpace f }
  calc
    (∫ x, f x ∂betaStateMeasure Λ hΛ) =
        ∫ x, fc x ∂(RealRMK.rieszMeasure (betaStatePositiveFunctional Λ hΛ)) := by
          congr with x
    _ = betaStatePositiveFunctional Λ hΛ fc :=
      RealRMK.integral_rieszMeasure (betaStatePositiveFunctional Λ hΛ) fc
    _ = Λ f := by
      change Λ fc.toContinuousMap = Λ f
      congr 1

theorem betaStateMeasure_univ (Λ : BetaFunctional)
    (hΛ : Λ ∈ betaInvariantStates) : betaStateMeasure Λ hΛ univ = 1 := by
  let : (betaStateMeasure Λ hΛ).Regular := regular_betaStateMeasure Λ hΛ
  let one : BetaTest := 1
  have h := integral_betaStateMeasure Λ hΛ one
  rw [show (∫ x, one x ∂betaStateMeasure Λ hΛ) =
      (betaStateMeasure Λ hΛ univ).toReal by
        simp [one, integral_const, measureReal_def]] at h
  rw [show Λ one = 1 by exact hΛ.1] at h
  exact (ENNReal.toReal_eq_one_iff _).mp h

noncomputable def betaStateProbability (Λ : BetaFunctional)
    (hΛ : Λ ∈ betaInvariantStates) : ProbabilityMeasure BetaNat :=
  ⟨betaStateMeasure Λ hΛ, ⟨betaStateMeasure_univ Λ hΛ⟩⟩

theorem regular_betaStateProbability (Λ : BetaFunctional)
    (hΛ : Λ ∈ betaInvariantStates) :
    ((betaStateProbability Λ hΛ : ProbabilityMeasure BetaNat) : Measure BetaNat).Regular :=
  regular_betaStateMeasure Λ hΛ

theorem measurePreserving_betaStateProbability (Λ : BetaFunctional)
    (hΛ : Λ ∈ betaInvariantStates) :
    MeasurePreserving betaShift
      ((betaStateProbability Λ hΛ : ProbabilityMeasure BetaNat) : Measure BetaNat)
      (betaStateProbability Λ hΛ : ProbabilityMeasure BetaNat) := by
  let μ : Measure BetaNat := betaStateMeasure Λ hΛ
  have hμreg : μ.Regular := regular_betaStateMeasure Λ hΛ
  let : μ.Regular := hμreg
  let : (Measure.map betaShift μ).InnerRegular :=
    Measure.InnerRegular.map_of_continuous continuous_betaShift
  let : IsProbabilityMeasure μ := ⟨betaStateMeasure_univ Λ hΛ⟩
  let : IsProbabilityMeasure (Measure.map betaShift μ) :=
    Measure.isProbabilityMeasure_map continuous_betaShift.measurable.aemeasurable
  refine ⟨continuous_betaShift.measurable, ?_⟩
  change Measure.map betaShift μ = μ
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  change (∫ x, f.toContinuousMap x ∂Measure.map betaShift μ) =
    ∫ x, f.toContinuousMap x ∂μ
  rw [MeasureTheory.integral_map continuous_betaShift.measurable.aemeasurable
    f.continuous.aestronglyMeasurable]
  let fc : BetaTest := f.toContinuousMap
  have hinv := hΛ.2.2 fc
  calc
    (∫ x, f.toContinuousMap (betaShift x) ∂μ) =
        ∫ x, betaShiftTest fc x ∂betaStateMeasure Λ hΛ := by rfl
    _ = Λ (betaShiftTest fc) := integral_betaStateMeasure Λ hΛ _
    _ = Λ fc := hinv
    _ = ∫ x, fc x ∂betaStateMeasure Λ hΛ :=
      (integral_betaStateMeasure Λ hΛ _).symm
    _ = ∫ x, f.toContinuousMap x ∂μ := by rfl

theorem regular_cond_of_regular (μ : Measure BetaNat) [μ.Regular]
    {s : Set BetaNat} (hs : μ s ≠ 0) : μ[|s].Regular := by
  unfold ProbabilityTheory.cond
  have hrestr : (μ.restrict s).Regular :=
    Measure.Regular.restrict_of_measure_ne_top (measure_ne_top μ s)
  let : (μ.restrict s).Regular := hrestr
  exact Measure.Regular.smul (ENNReal.inv_ne_top.mpr hs)

theorem measurePreserving_cond_of_invariant_set {μ : Measure BetaNat}
    (hμ : MeasurePreserving betaShift μ μ) {s : Set BetaNat}
    (hsm : MeasurableSet s) (hfs : betaShift ⁻¹' s = s) :
    MeasurePreserving betaShift μ[|s] μ[|s] := by
  apply MeasurePreserving.smul_measure
  convert hμ.restrict_preimage hsm using 1
  exact congrArg μ.restrict hfs.symm

theorem betaIntegralWeakFunctional_cond_decomposition (μ : Measure BetaNat)
    [IsProbabilityMeasure μ] {s : Set BetaNat} (hsm : MeasurableSet s)
    (hs : μ s ≠ 0) (hsc : μ sᶜ ≠ 0) :
    betaIntegralWeakFunctional μ =
      μ.real s • (@betaIntegralWeakFunctional μ[|s] (cond_isProbabilityMeasure hs)) +
        μ.real sᶜ •
          (@betaIntegralWeakFunctional μ[|sᶜ] (cond_isProbabilityMeasure hsc)) := by
  let : IsProbabilityMeasure μ[|s] := cond_isProbabilityMeasure hs
  let : IsProbabilityMeasure μ[|sᶜ] := cond_isProbabilityMeasure hsc
  apply ContinuousLinearMap.ext
  intro f
  change (∫ x, f x ∂μ) =
    μ.real s * (∫ x, f x ∂μ[|s]) + μ.real sᶜ * (∫ x, f x ∂μ[|sᶜ])
  have hsavg : μ.real s * (∫ x, f x ∂μ[|s]) = ∫ x, f x ∂μ.restrict s := by
    simpa only [setAverage_eq', ProbabilityTheory.cond, smul_eq_mul] using
      measure_smul_setAverage (μ := μ) f (s := s) (measure_ne_top μ s)
  have hcavg : μ.real sᶜ * (∫ x, f x ∂μ[|sᶜ]) = ∫ x, f x ∂μ.restrict sᶜ := by
    simpa only [setAverage_eq', ProbabilityTheory.cond, smul_eq_mul] using
      measure_smul_setAverage (μ := μ) f (s := sᶜ) (measure_ne_top μ sᶜ)
  rw [hsavg, hcavg, ← integral_add_measure]
  · rw [Measure.restrict_add_restrict_compl hsm]
  · exact (BoundedContinuousFunction.mkOfCompact f).integrable _
  · exact (BoundedContinuousFunction.mkOfCompact f).integrable _

theorem ergodic_betaStateProbability_of_extreme (Λ : BetaFunctional)
    (hΛext : Λ ∈ extremePoints ℝ betaInvariantStates) :
    Ergodic betaShift
      ((betaStateProbability Λ hΛext.1 : ProbabilityMeasure BetaNat) : Measure BetaNat) := by
  let μ : Measure BetaNat := betaStateMeasure Λ hΛext.1
  have hμprob : IsProbabilityMeasure μ := ⟨betaStateMeasure_univ Λ hΛext.1⟩
  let : IsProbabilityMeasure μ := hμprob
  have hμreg : μ.Regular := regular_betaStateMeasure Λ hΛext.1
  let : μ.Regular := hμreg
  have hμpres : MeasurePreserving betaShift μ μ :=
    measurePreserving_betaStateProbability Λ hΛext.1
  have hstate : betaIntegralWeakFunctional μ = Λ := by
    apply ContinuousLinearMap.ext
    intro f
    exact integral_betaStateMeasure Λ hΛext.1 f
  refine ⟨hμpres, ⟨?_⟩⟩
  intro s hsm hfs
  by_contra H
  obtain ⟨hs, hsc⟩ : μ s ≠ 0 ∧ μ sᶜ ≠ 0 := by
    simpa [eventuallyConst_set, ae_iff, and_comm] using! H
  let hps : IsProbabilityMeasure μ[|s] := cond_isProbabilityMeasure hs
  let hpcs : IsProbabilityMeasure μ[|sᶜ] := cond_isProbabilityMeasure hsc
  let Λs : BetaFunctional := betaIntegralWeakFunctional μ[|s]
  let Λc : BetaFunctional := betaIntegralWeakFunctional μ[|sᶜ]
  have hpres_s : MeasurePreserving betaShift μ[|s] μ[|s] :=
    measurePreserving_cond_of_invariant_set hμpres hsm hfs
  have hpres_c : MeasurePreserving betaShift μ[|sᶜ] μ[|sᶜ] :=
    measurePreserving_cond_of_invariant_set hμpres hsm.compl (by
      rw [preimage_compl, hfs])
  have hΛs : Λs ∈ betaInvariantStates :=
    betaIntegralWeakFunctional_mem μ[|s] hpres_s
  have hΛc : Λc ∈ betaInvariantStates :=
    betaIntegralWeakFunctional_mem μ[|sᶜ] hpres_c
  have ha : 0 < μ.real s := ENNReal.toReal_pos hs (measure_ne_top μ s)
  have hb : 0 < μ.real sᶜ := ENNReal.toReal_pos hsc (measure_ne_top μ sᶜ)
  have hab : μ.real s + μ.real sᶜ = 1 := probReal_add_probReal_compl hsm
  have hdecomp : betaIntegralWeakFunctional μ =
      μ.real s • Λs + μ.real sᶜ • Λc := by
    exact betaIntegralWeakFunctional_cond_decomposition μ hsm hs hsc
  have hopen : Λ ∈ openSegment ℝ Λs Λc := by
    refine ⟨μ.real s, μ.real sᶜ, ha, hb, hab, ?_⟩
    rw [← hstate]
    exact hdecomp.symm
  have hΛs_eq : Λs = Λ := hΛext.2 hΛs hΛc hopen
  have hcondreg : μ[|s].Regular := regular_cond_of_regular μ hs
  let : μ[|s].Regular := hcondreg
  have hcond_eq : μ[|s] = μ := by
    apply Measure.ext_of_integral_eq_on_compactlySupported
    intro f
    let fc : BetaTest := f.toContinuousMap
    have heval := congrArg (fun Ψ : BetaFunctional ↦ Ψ fc) hΛs_eq
    have hmain := integral_betaStateMeasure Λ hΛext.1 fc
    change (∫ x, fc x ∂μ[|s]) = Λ fc at heval
    change (∫ x, fc x ∂μ) = Λ fc at hmain
    calc
      (∫ x, f x ∂μ[|s]) = ∫ x, fc x ∂μ[|s] := by rfl
      _ = Λ fc := heval
      _ = ∫ x, fc x ∂μ := hmain.symm
      _ = ∫ x, f x ∂μ := by rfl
  rw [← hcond_eq] at hsc
  simp [ProbabilityTheory.cond_apply, hsm] at hsc

theorem exists_regular_ergodic_betaMeasure_realizing_upperDensity (A : Set ℕ) :
    ∃ μ : ProbabilityMeasure BetaNat,
      ((μ : Measure BetaNat).Regular) ∧
      MeasurePreserving betaShift (μ : Measure BetaNat) μ ∧
      Ergodic betaShift (μ : Measure BetaNat) ∧
      A.upperDensity ≤
        ∫ x, betaIndicator A x ∂(μ : Measure BetaNat) := by
  obtain ⟨N, hNdensity, hNtop, hNpos⟩ :=
    exists_prefix_realizing_upperDensity A
  obtain ⟨q, hq, μ₀, hμ₀reg, hμ₀tend, hμ₀pres⟩ :=
    exists_invariant_betaLimit N hNpos hNtop
  let f : C(BetaNat, ℝ) := betaIndicator A
  have hIntTend :
      Tendsto
        (fun k ↦ ∫ x, f x ∂
          ((betaEmpirical (N k) (hNpos k) : ProbabilityMeasure BetaNat) :
            Measure BetaNat))
        (q : Filter ℕ) (𝓝 (∫ x, f x ∂(μ₀ : Measure BetaNat))) := by
    simpa using
      (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hμ₀tend)
        (BoundedContinuousFunction.mkOfCompact f)
  have hFinite (k : ℕ) :
      (∫ x, f x ∂
          ((betaEmpirical (N k) (hNpos k) : ProbabilityMeasure BetaNat) :
            Measure BetaNat)) =
        A.partialDensity Set.univ (N k) := by
    rw [integral_betaEmpirical]
    simp_rw [f, betaIndicator_pure, natIndicator_eq_realIndicator]
    calc
      (∑ n ∈ Finset.range (N k), realIndicator A n) / (N k : ℝ) =
          realFinsetMean (Finset.range (N k))
            (realIndicator A) := by
        simp [realFinsetMean]
      _ = finsetDensity (Finset.range (N k)) A :=
        realFinsetMean_indicator _ _
      _ = A.partialDensity Set.univ (N k) :=
        finsetDensity_range_eq_partialDensity A (N k)
  have hDensityTend :
      Tendsto (fun k ↦ A.partialDensity Set.univ (N k))
        (q : Filter ℕ) (𝓝 A.upperDensity) :=
    hNdensity.mono_left hq
  have hIntEq : (∫ x, f x ∂(μ₀ : Measure BetaNat)) = A.upperDensity := by
    apply tendsto_nhds_unique hIntTend
    convert hDensityTend using 1
    funext k
    exact hFinite k
  let Λ₀ : BetaFunctional := betaIntegralWeakFunctional (μ₀ : Measure BetaNat)
  have hΛ₀ : Λ₀ ∈ betaInvariantStates := by
    exact betaIntegralWeakFunctional_mem (μ₀ : Measure BetaNat) hμ₀pres
  obtain ⟨Λ, hΛext, hΛge⟩ :=
    exists_extreme_betaInvariantState_ge f hΛ₀
  let μ : ProbabilityMeasure BetaNat := betaStateProbability Λ hΛext.1
  refine ⟨μ, regular_betaStateProbability Λ hΛext.1,
    measurePreserving_betaStateProbability Λ hΛext.1,
    ergodic_betaStateProbability_of_extreme Λ hΛext, ?_⟩
  calc
    A.upperDensity = Λ₀ f := by
      rw [← hIntEq]
      rfl
    _ ≤ Λ f := hΛge
    _ = ∫ x, f x ∂(μ : Measure BetaNat) := by
      exact (integral_betaStateMeasure Λ hΛext.1 f).symm

/-- Translating an arithmetic set agrees with composing its clopen
indicator on `βℕ` with right addition by the corresponding principal
ultrafilter. -/
theorem betaIndicator_shift (A : Set ℕ) (m : ℕ) :
    betaIndicator (shift A m) =
      (betaIndicator A).comp
        ⟨fun p : BetaNat ↦ p + pure m, Ultrafilter.continuous_add_left (pure m)⟩ := by
  apply ContinuousMap.ext
  intro p
  apply congrFun ((denseRange_pure : DenseRange (pure : ℕ → BetaNat)).equalizer
    (betaIndicator (shift A m)).continuous
    ((betaIndicator A).continuous.comp (Ultrafilter.continuous_add_left (pure m))) ?_) p
  funext n
  have hpure : (pure n : BetaNat) + pure m = pure (n + m) := by
    apply Ultrafilter.coe_inj.mp
    ext s
    change (∀ᶠ x in (pure n : Ultrafilter ℕ),
      ∀ᶠ y in (pure m : Ultrafilter ℕ), x + y ∈ s) ↔ n + m ∈ s
    simp
  simp only [Function.comp_apply]
  rw [hpure, betaIndicator_pure]
  rw [betaIndicator_pure]
  rfl

/-! ## The free-ultrafilter extraction criterion -/

/-- The shift of `A` selected by an ultrafilter: `c` belongs precisely when
the set of rows compatible with the column `c` is ultrafilter-large. -/
def ultraShift (A : Set ℕ) (p : Ultrafilter ℕ) : Set ℕ :=
  {c | shift A c ∈ (p : Filter ℕ)}

@[simp] theorem mem_ultraShift {A : Set ℕ} {p : Ultrafilter ℕ} {c : ℕ} :
    c ∈ ultraShift A p ↔ shift A c ∈ (p : Filter ℕ) := Iff.rfl

/-- The ultrafilter shift is represented on `βℕ` by right addition of
the ultrafilter.  This is the pointwise-limit side of the MRR argument. -/
theorem betaIndicator_ultraShift (A : Set ℕ) (p : Ultrafilter ℕ) :
    betaIndicator (ultraShift A p) =
      (betaIndicator A).comp
        ⟨fun q : BetaNat ↦ q + p, Ultrafilter.continuous_add_left p⟩ := by
  apply ContinuousMap.ext
  intro q
  apply congrFun ((denseRange_pure : DenseRange (pure : ℕ → BetaNat)).equalizer
    (betaIndicator (ultraShift A p)).continuous
    ((betaIndicator A).continuous.comp (Ultrafilter.continuous_add_left p)) ?_) q
  funext n
  simp only [Function.comp_apply, betaIndicator_pure]
  have hmem : A ∈ ((pure n : BetaNat) + p : Ultrafilter ℕ) ↔
      shift A n ∈ (p : Filter ℕ) := by
    change (∀ᶠ x in (pure n : Ultrafilter ℕ),
      ∀ᶠ y in p, x + y ∈ A) ↔ shift A n ∈ (p : Filter ℕ)
    change {y : ℕ | n + y ∈ A} ∈ (p : Filter ℕ) ↔
      {y : ℕ | y + n ∈ A} ∈ (p : Filter ℕ)
    have hsets : {y : ℕ | n + y ∈ A} = {y : ℕ | y + n ∈ A} := by
      ext y
      simp [add_comm]
    rw [hsets]
  by_cases h : shift A n ∈ (p : Filter ℕ)
  · rw [betaIndicator_apply_of_mem A ((pure n : BetaNat) + p) (hmem.mpr h)]
    simp [natIndicator, ultraShift, h]
  · rw [betaIndicator_apply_of_not_mem A ((pure n : BetaNat) + p)
      (fun hA ↦ h (hmem.mp hA))]
    simp [natIndicator, ultraShift, h]

@[simp] theorem realIndicator_shift (A : Set ℕ) (m n : ℕ) :
    realIndicator (shift A m) n = realIndicator A (n + m) := by
  classical
  simp only [realIndicator, mem_shift]

theorem realFinsetCorrelation_shift_ultraShift
    (F : Finset ℕ) (A : Set ℕ) (p : Ultrafilter ℕ) (m : ℕ) :
    realFinsetCorrelation F (realIndicator (shift A m))
        (realIndicator (ultraShift A p)) =
      finsetDensity F (ultraShift A p ∩ shift A m) := by
  rw [realFinsetCorrelation_indicator, inter_comm]

/-- The finite correlations used in the combinatorial endpoint are exactly
integrals of products of clopen indicators against the empirical laws on
`βℕ`. -/
theorem integral_betaEmpirical_indicator_correlation
    (N : ℕ) (hN : 0 < N) (A : Set ℕ) (p : Ultrafilter ℕ) (m : ℕ) :
    ∫ x, betaIndicator (shift A m) x * betaIndicator (ultraShift A p) x
        ∂((betaEmpirical N hN : ProbabilityMeasure BetaNat) : Measure BetaNat) =
      finsetDensity (Finset.range N) (ultraShift A p ∩ shift A m) := by
  let f : C(BetaNat, ℝ) :=
    betaIndicator (shift A m) * betaIndicator (ultraShift A p)
  have hf := integral_betaEmpirical N hN f
  rw [show (∫ x, betaIndicator (shift A m) x * betaIndicator (ultraShift A p) x
      ∂((betaEmpirical N hN : ProbabilityMeasure BetaNat) : Measure BetaNat)) =
      ∫ x, f x ∂((betaEmpirical N hN : ProbabilityMeasure BetaNat) : Measure BetaNat) by rfl,
    hf]
  dsimp [f]
  simp_rw [betaIndicator_pure, natIndicator_eq_realIndicator]
  simpa [realFinsetCorrelation, realFinsetMean] using
    realFinsetCorrelation_shift_ultraShift (Finset.range N) A p m

/-- The first `n + 1` column constraints imposed by an ultrafilter shift. -/
noncomputable def ultraRowsThrough (A : Set ℕ) (p : Ultrafilter ℕ) (n : ℕ) : Set ℕ := by
  classical
  exact ⋂ c ∈ Finset.range (n + 1),
    if c ∈ ultraShift A p then shift A c else Set.univ

theorem ultraRowsThrough_mem (A : Set ℕ) (p : Ultrafilter ℕ) (n : ℕ) :
    ultraRowsThrough A p n ∈ (p : Filter ℕ) := by
  classical
  rw [ultraRowsThrough, Filter.biInter_finset_mem]
  intro c hc
  by_cases hcp : c ∈ ultraShift A p
  · rw [if_pos hcp]
    exact hcp
  · simp [hcp]

/-- Candidate rows at stage `n`: they lie in `G`, satisfy every selected
column constraint up to `n`, and are larger than the previous row. -/
def ultraRowCandidates (A G : Set ℕ) (p : Ultrafilter ℕ) (n previous : ℕ) : Set ℕ :=
  G ∩ ultraRowsThrough A p n ∩ Set.Ioi previous

theorem ultraRowCandidates_mem (A G : Set ℕ) (p : Ultrafilter ℕ)
    (hp : (p : Filter ℕ) ≤ cofinite) (hG : G ∈ (p : Filter ℕ))
    (n previous : ℕ) : ultraRowCandidates A G p n previous ∈ (p : Filter ℕ) := by
  apply inter_mem (inter_mem hG (ultraRowsThrough_mem A p n))
  apply hp
  rw [mem_cofinite]
  simpa only [compl_Ioi] using Set.finite_Iic previous

/-- Recursively choose increasingly large rows from the ultrafilter. -/
noncomputable def ultraRows (A G : Set ℕ) (p : Ultrafilter ℕ)
    (hp : (p : Filter ℕ) ≤ cofinite) (hG : G ∈ (p : Filter ℕ)) : ℕ → ℕ
  | 0 => Classical.choose (Ultrafilter.nonempty_of_mem
      (ultraRowCandidates_mem A G p hp hG 0 0))
  | n + 1 => Classical.choose (Ultrafilter.nonempty_of_mem
      (ultraRowCandidates_mem A G p hp hG (n + 1) (ultraRows A G p hp hG n)))

theorem ultraRows_mem_candidates (A G : Set ℕ) (p : Ultrafilter ℕ)
    (hp : (p : Filter ℕ) ≤ cofinite) (hG : G ∈ (p : Filter ℕ)) (n : ℕ) :
    ultraRows A G p hp hG n ∈
      ultraRowCandidates A G p n (if n = 0 then 0 else ultraRows A G p hp hG (n - 1)) := by
  cases n with
  | zero =>
      exact Classical.choose_spec (Ultrafilter.nonempty_of_mem
        (ultraRowCandidates_mem A G p hp hG 0 0))
  | succ n =>
      rw [ultraRows]
      exact Classical.choose_spec (Ultrafilter.nonempty_of_mem
        (ultraRowCandidates_mem A G p hp hG (n + 1) (ultraRows A G p hp hG n)))

theorem ultraRows_strictMono (A G : Set ℕ) (p : Ultrafilter ℕ)
    (hp : (p : Filter ℕ) ≤ cofinite) (hG : G ∈ (p : Filter ℕ)) :
    StrictMono (ultraRows A G p hp hG) := by
  apply strictMono_nat_of_lt_succ
  intro n
  simpa using (ultraRows_mem_candidates A G p hp hG (n + 1)).2

theorem ultraRows_mem_good (A G : Set ℕ) (p : Ultrafilter ℕ)
    (hp : (p : Filter ℕ) ≤ cofinite) (hG : G ∈ (p : Filter ℕ)) (n : ℕ) :
    ultraRows A G p hp hG n ∈ G :=
  (ultraRows_mem_candidates A G p hp hG n).1.1

theorem ultraRows_eventually_compatible (A G : Set ℕ) (p : Ultrafilter ℕ)
    (hp : (p : Filter ℕ) ≤ cofinite) (hG : G ∈ (p : Filter ℕ))
    (C : Finset ℕ) (hC : (C : Set ℕ) ⊆ ultraShift A p) :
    ∀ᶠ n in atTop, ∀ c ∈ C, ultraRows A G p hp hG n + c ∈ A := by
  classical
  let N := C.sup id
  filter_upwards [eventually_ge_atTop N] with n hn c hc
  have hcN : c ≤ N := by
    dsimp [N]
    exact Finset.le_sup (α := ℕ) (f := id) hc
  have hcrange : c ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
  have hrows := (ultraRows_mem_candidates A G p hp hG n).1.2
  have hcshift : ultraRows A G p hp hG n ∈ shift A c := by
    have hx :
      ultraRows A G p hp hG n ∈
        if c ∈ ultraShift A p then shift A c else Set.univ :=
      Set.mem_iInter₂.mp hrows c hcrange
    rw [if_pos (hC (by simpa using hc))] at hx
    exact hx
  simpa [shift, add_comm] using hcshift

/-- A free ultrafilter packages the entire `RightRich` side of the MRR
criterion.  It remains only to provide one uniformly dense ultrafilter-large
set of rows. -/
theorem exists_infinite_add_subset_of_ultrafilter_density
    {A G : Set ℕ} (p : Ultrafilter ℕ)
    (hp : (p : Filter ℕ) ≤ cofinite) (hG : G ∈ (p : Filter ℕ))
    (F : ℕ → Finset ℕ) (hF : ∀ n, (F n).Nonempty)
    (hcard : Tendsto (fun n => (F n).card) atTop atTop)
    (r : ℝ≥0∞) (hr0 : r ≠ 0)
    (hleft : ∀ m ∈ G, ∀ᶠ n in atTop,
      r ≤ ((((F n : Set ℕ) ∩ (ultraShift A p ∩ shift A m)).ncard : ℕ) : ℝ≥0∞) /
        (F n).card) :
    ∃ B C : Set ℕ, B.Infinite ∧ C.Infinite ∧ B + C ⊆ A := by
  let m := ultraRows A G p hp hG
  apply exists_infinite_add_subset_of_density
    (ultraRows_strictMono A G p hp hG).injective F hF hcard r hr0
  · intro i
    exact hleft (m i) (ultraRows_mem_good A G p hp hG i)
  · exact ultraRows_eventually_compatible A G p hp hG

/-! ## The exact analytic-to-combinatorial interface -/

/-- Rows whose correlation with the ultrafilter shift has one fixed positive
eventual lower bound along the selected prefixes. -/
def correlationGoodRows (A : Set ℕ) (p : Ultrafilter ℕ) (N : ℕ → ℕ)
    (r : ℝ≥0∞) : Set ℕ :=
  {m | ∀ᶠ k in atTop,
    r ≤ ((((Finset.range (N k) : Set ℕ) ∩
      (ultraShift A p ∩ shift A m)).ncard : ℕ) : ℝ≥0∞) /
        (Finset.range (N k)).card}

/-- Once the MRR correlation-selection theorem supplies an
ultrafilter-large set of uniformly positive rows, all remaining work is the
already verified Bergelson/rectangle extraction. -/
theorem erdos109_of_correlationGoodRows
    {A : Set ℕ} {N : ℕ → ℕ} (hN : Tendsto N atTop atTop)
    (p : Ultrafilter ℕ) (hp : (p : Filter ℕ) ≤ cofinite)
    (r : ℝ≥0∞) (hr : r ≠ 0)
    (hgood : correlationGoodRows A p N r ∈ (p : Filter ℕ)) :
    ∃ B C : Set ℕ, B.Infinite ∧ C.Infinite ∧ B + C ⊆ A := by
  have hNpos : ∀ᶠ k in atTop, 0 < N k := hN (eventually_gt_atTop 0)
  rw [eventually_atTop] at hNpos
  obtain ⟨K, hK⟩ := hNpos
  let N' : ℕ → ℕ := fun k ↦ N (k + K)
  have hN'top : Tendsto N' atTop atTop :=
    hN.comp (tendsto_add_atTop_nat K)
  have hN'pos (k : ℕ) : 0 < N' k := hK (k + K) (Nat.le_add_left K k)
  let G := correlationGoodRows A p N r
  have hG : G ∈ (p : Filter ℕ) := hgood
  apply exists_infinite_add_subset_of_ultrafilter_density p hp hG
    (fun k ↦ Finset.range (N' k))
    (fun k ↦ by simpa using (Nat.ne_of_gt (hN'pos k)))
    (by simpa only [Finset.card_range] using hN'top) r hr
  intro m hm
  have hm' : ∀ᶠ k in atTop,
      r ≤ ((((Finset.range (N k) : Set ℕ) ∩
        (ultraShift A p ∩ shift A m)).ncard : ℕ) : ℝ≥0∞) /
          (Finset.range (N k)).card := hm
  exact (tendsto_add_atTop_nat K) hm'

end Erdos109

open CompactlySupported Filter Function MeasureTheory Set
open scoped ComplexConjugate ComplexOrder ENNReal NNReal Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

noncomputable def unitaryOperator (U : H ≃ₗᵢ[ℂ] H) : H →L[ℂ] H := U

theorem unitaryOperator_mem (U : H ≃ₗᵢ[ℂ] H) :
    unitaryOperator U ∈ unitary (H →L[ℂ] H) := by
  exact (Unitary.linearIsometryEquiv.symm U).property

abbrev UnitarySpectrum (U : H ≃ₗᵢ[ℂ] H) := spectrum ℂ (unitaryOperator U)

noncomputable def realToComplexContinuous {X : Type*} [TopologicalSpace X]
    (f : C(X, ℝ)) : C(X, ℂ) :=
  f.realToRCLike ℂ

@[simp] theorem realToComplexContinuous_apply {X : Type*} [TopologicalSpace X]
    (f : C(X, ℝ)) (x : X) : realToComplexContinuous f x = f x := rfl

noncomputable def spectralQuadratic (U : H ≃ₗᵢ[ℂ] H) (x : H)
    (f : C(UnitarySpectrum U, ℝ)) : ℝ :=
  Complex.re (inner ℂ
    (cfcHom (isStarNormal_of_mem_unitary (unitaryOperator_mem U))
      (realToComplexContinuous f) x) x)

theorem spectralQuadratic_add (U : H ≃ₗᵢ[ℂ] H) (x : H)
    (f g : C(UnitarySpectrum U, ℝ)) :
    spectralQuadratic U x (f + g) =
      spectralQuadratic U x f + spectralQuadratic U x g := by
  let Φ := cfcHom (R := ℂ)
    (isStarNormal_of_mem_unitary (unitaryOperator_mem U))
  have hreal : realToComplexContinuous (f + g) =
      realToComplexContinuous f + realToComplexContinuous g := by
    exact map_add (ContinuousMap.realToRCLikeStarAlgHom _ ℂ) f g
  unfold spectralQuadratic
  rw [hreal, map_add Φ]
  simp only [ContinuousLinearMap.add_apply, inner_add_left, map_add,
    Complex.add_re]
  rfl

theorem spectralQuadratic_smul (U : H ≃ₗᵢ[ℂ] H) (x : H)
    (c : ℝ) (f : C(UnitarySpectrum U, ℝ)) :
    spectralQuadratic U x (c • f) = c • spectralQuadratic U x f := by
  let Φ := cfcHom (R := ℂ)
    (isStarNormal_of_mem_unitary (unitaryOperator_mem U))
  have hreal : realToComplexContinuous (c • f) =
      (c : ℂ) • realToComplexContinuous f := by
    exact map_smul (ContinuousMap.realToRCLikeStarAlgHom _ ℂ) c f
  unfold spectralQuadratic
  rw [hreal, map_smul Φ]
  simp only [ContinuousLinearMap.smul_apply, inner_smul_left,
    Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, smul_eq_mul]
  simp [Φ]

noncomputable def continuousSqrt {X : Type*} [TopologicalSpace X]
    (f : C(X, ℝ)) : C(X, ℝ) where
  toFun x := Real.sqrt (f x)
  continuous_toFun := Real.continuous_sqrt.comp f.continuous

@[simp] theorem continuousSqrt_apply {X : Type*} [TopologicalSpace X]
    (f : C(X, ℝ)) (x : X) : continuousSqrt f x = Real.sqrt (f x) := rfl

theorem spectralQuadratic_nonneg (U : H ≃ₗᵢ[ℂ] H) (x : H)
    (f : C(UnitarySpectrum U, ℝ)) (hf : 0 ≤ f) :
    0 ≤ spectralQuadratic U x f := by
  let s : C(UnitarySpectrum U, ℝ) := continuousSqrt f
  have hfsq : f = s * s := by
    ext z
    change f z = Real.sqrt (f z) * Real.sqrt (f z)
    rw [← sq]
    exact (Real.sq_sqrt (hf z)).symm
  rw [hfsq]
  let Φ := cfcHom (R := ℂ)
    (isStarNormal_of_mem_unitary (unitaryOperator_mem U))
  let a : H →L[ℂ] H := cfcHom
    (isStarNormal_of_mem_unitary (unitaryOperator_mem U))
      (realToComplexContinuous s)
  have hrealstar : star (realToComplexContinuous s) =
      realToComplexContinuous s := by
    exact (ContinuousMap.isSelfAdjoint_realToRCLike ℂ).star_eq
  have hop : Φ (realToComplexContinuous (s * s)) = star a * a := by
    rw [show realToComplexContinuous (s * s) =
        realToComplexContinuous s * realToComplexContinuous s by
      exact map_mul (ContinuousMap.realToRCLikeStarAlgHom _ ℂ) s s]
    calc
      Φ (realToComplexContinuous s * realToComplexContinuous s) =
          Φ (star (realToComplexContinuous s) * realToComplexContinuous s) := by
            rw [hrealstar]
      _ = star (Φ (realToComplexContinuous s)) *
          Φ (realToComplexContinuous s) := by rw [map_mul Φ, map_star Φ]
      _ = star a * a := by rfl
  unfold spectralQuadratic
  rw [hop]
  change 0 ≤ Complex.re (inner ℂ ((star a * a) x) x)
  rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_left]
  exact inner_self_nonneg (𝕜 := ℂ) (x := a x)

noncomputable def spectralPositiveFunctional (U : H ≃ₗᵢ[ℂ] H) (x : H) :
    C_c(UnitarySpectrum U, ℝ) →ₚ[ℝ] ℝ where
  toFun f := spectralQuadratic U x f.toContinuousMap
  map_add' f g := by
    change spectralQuadratic U x ((f + g).toContinuousMap) =
      spectralQuadratic U x f.toContinuousMap +
        spectralQuadratic U x g.toContinuousMap
    rw [show (f + g).toContinuousMap =
        f.toContinuousMap + g.toContinuousMap by ext; rfl]
    exact spectralQuadratic_add U x _ _
  map_smul' c f := by
    change spectralQuadratic U x ((c • f).toContinuousMap) =
      c • spectralQuadratic U x f.toContinuousMap
    rw [show (c • f).toContinuousMap = c • f.toContinuousMap by ext; rfl]
    exact spectralQuadratic_smul U x c _
  monotone' f g hfg := by
    have hnonneg : 0 ≤ g.toContinuousMap - f.toContinuousMap := by
      intro z
      exact sub_nonneg.mpr (hfg z)
    have h := spectralQuadratic_nonneg U x
      (g.toContinuousMap - f.toContinuousMap) hnonneg
    have hsub : spectralQuadratic U x
        (g.toContinuousMap - f.toContinuousMap) =
        spectralQuadratic U x g.toContinuousMap -
          spectralQuadratic U x f.toContinuousMap := by
      rw [sub_eq_add_neg, spectralQuadratic_add]
      have hneg := spectralQuadratic_smul U x (-1) f.toContinuousMap
      rw [show -f.toContinuousMap = (-1 : ℝ) • f.toContinuousMap by simp,
        hneg]
      rw [sub_eq_add_neg]
      simp
    rw [hsub, sub_nonneg] at h
    exact h

noncomputable def spectralMeasure (U : H ≃ₗᵢ[ℂ] H) (x : H) :
    Measure (UnitarySpectrum U) :=
  RealRMK.rieszMeasure (spectralPositiveFunctional U x)

theorem integral_spectralMeasure_real (U : H ≃ₗᵢ[ℂ] H) (x : H)
    (f : C(UnitarySpectrum U, ℝ)) :
    ∫ z, f z ∂spectralMeasure U x = spectralQuadratic U x f := by
  let fc : C_c(UnitarySpectrum U, ℝ) :=
    ⟨f, HasCompactSupport.of_compactSpace f⟩
  calc
    ∫ z, f z ∂(spectralMeasure U x) =
        ∫ z, fc z ∂(RealRMK.rieszMeasure (spectralPositiveFunctional U x)) := by rfl
    _ = spectralPositiveFunctional U x fc :=
      RealRMK.integral_rieszMeasure (spectralPositiveFunctional U x) fc
    _ = spectralQuadratic U x f := by rfl

theorem spectralQuadratic_complex_of_real (U : H ≃ₗᵢ[ℂ] H) (x : H)
    (f : C(UnitarySpectrum U, ℝ)) :
    inner ℂ x
      (cfcHom (R := ℂ)
        (isStarNormal_of_mem_unitary (unitaryOperator_mem U))
        (realToComplexContinuous f) x) =
      (spectralQuadratic U x f : ℂ) := by
  let a : H →L[ℂ] H := cfcHom (R := ℂ)
    (isStarNormal_of_mem_unitary (unitaryOperator_mem U))
      (realToComplexContinuous f)
  have hfself : IsSelfAdjoint (realToComplexContinuous f) :=
    ContinuousMap.isSelfAdjoint_realToRCLike ℂ
  have haself : IsSelfAdjoint a := by
    rw [isSelfAdjoint_iff]
    change star
      (cfcHom (R := ℂ)
        (isStarNormal_of_mem_unitary (unitaryOperator_mem U))
        (realToComplexContinuous f)) = _
    rw [← map_star]
    exact congrArg
      (cfcHom (R := ℂ)
        (isStarNormal_of_mem_unitary (unitaryOperator_mem U)))
      hfself.star_eq
  have hinner : inner ℂ (a x) x = inner ℂ x (a x) :=
    haself.isSymmetric x x
  unfold spectralQuadratic
  change inner ℂ x (a x) = (Complex.re (inner ℂ (a x) x) : ℂ)
  rw [← hinner]
  apply Complex.ext
  · rfl
  · exact haself.isSymmetric.im_inner_apply_self x

noncomputable def complexReContinuous {X : Type*} [TopologicalSpace X]
    (f : C(X, ℂ)) : C(X, ℝ) where
  toFun z := Complex.re (f z)
  continuous_toFun := Complex.continuous_re.comp f.continuous

noncomputable def complexImContinuous {X : Type*} [TopologicalSpace X]
    (f : C(X, ℂ)) : C(X, ℝ) where
  toFun z := Complex.im (f z)
  continuous_toFun := Complex.continuous_im.comp f.continuous

theorem integral_spectralMeasure_complex (U : H ≃ₗᵢ[ℂ] H) (x : H)
    (f : C(UnitarySpectrum U, ℂ)) :
    ∫ z, f z ∂spectralMeasure U x =
      inner ℂ x
        (cfcHom (R := ℂ)
          (isStarNormal_of_mem_unitary (unitaryOperator_mem U)) f x) := by
  let : IsFiniteMeasure (spectralMeasure U x) := by
    unfold spectralMeasure
    infer_instance
  let fr : C(UnitarySpectrum U, ℝ) := complexReContinuous f
  let fi : C(UnitarySpectrum U, ℝ) := complexImContinuous f
  have hfdecomp : f = realToComplexContinuous fr +
      Complex.I • realToComplexContinuous fi := by
    ext z
    simpa [fr, fi, complexReContinuous, complexImContinuous,
      realToComplexContinuous, mul_comm] using
        (Complex.re_add_im (f z)).symm
  have hfr : Integrable (fun z ↦ (realToComplexContinuous fr) z)
      (spectralMeasure U x) := by
    simpa only [integrableOn_univ] using
      (realToComplexContinuous fr).continuous.continuousOn.integrableOn_compact
        (μ := spectralMeasure U x) isCompact_univ
  have hfi : Integrable (fun z ↦
      (Complex.I • realToComplexContinuous fi) z) (spectralMeasure U x) := by
    have hc : Continuous (fun z ↦
        (Complex.I • realToComplexContinuous fi) z) :=
      continuous_const.mul (realToComplexContinuous fi).continuous
    simpa only [integrableOn_univ] using
      hc.continuousOn.integrableOn_compact
        (μ := spectralMeasure U x) isCompact_univ
  have hfrint : (∫ z, (realToComplexContinuous fr) z
      ∂spectralMeasure U x) = (spectralQuadratic U x fr : ℂ) := by
    calc
      (∫ z, (realToComplexContinuous fr) z ∂spectralMeasure U x) =
          ((∫ z, fr z ∂spectralMeasure U x : ℝ) : ℂ) := by
            exact integral_complex_ofReal
      _ = (spectralQuadratic U x fr : ℂ) := by
        rw [integral_spectralMeasure_real]
  have hfiint : (∫ z, (realToComplexContinuous fi) z
      ∂spectralMeasure U x) = (spectralQuadratic U x fi : ℂ) := by
    calc
      (∫ z, (realToComplexContinuous fi) z ∂spectralMeasure U x) =
          ((∫ z, fi z ∂spectralMeasure U x : ℝ) : ℂ) := by
            exact integral_complex_ofReal
      _ = (spectralQuadratic U x fi : ℂ) := by
        rw [integral_spectralMeasure_real]
  rw [hfdecomp]
  change (∫ z, (realToComplexContinuous fr) z +
      (Complex.I • realToComplexContinuous fi) z ∂spectralMeasure U x) = _
  rw [integral_add hfr hfi]
  rw [show (∫ z, (Complex.I • realToComplexContinuous fi) z
      ∂spectralMeasure U x) =
      Complex.I * ∫ z, (realToComplexContinuous fi) z
        ∂spectralMeasure U x by
    change (∫ z, Complex.I * (realToComplexContinuous fi) z
      ∂spectralMeasure U x) = _
    exact integral_const_mul _ _]
  rw [hfrint, hfiint]
  rw [map_add, map_smul]
  rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    inner_add_right, inner_smul_right]
  rw [spectralQuadratic_complex_of_real,
    spectralQuadratic_complex_of_real]

open Filter Finset MeasureTheory Set
open scoped ComplexConjugate ENNReal Topology

noncomputable local instance : MeasurableSpace Circle := borel Circle
local instance : BorelSpace Circle := ⟨rfl⟩
noncomputable local instance : DecidableEq Circle := Classical.decEq Circle

noncomputable def circleCesaroKernel (N : ℕ) (z w : Circle) : ℂ :=
  (N : ℂ)⁻¹ * ∑ n ∈ range N, ((z / w : Circle) : ℂ) ^ n

theorem norm_circleCesaroKernel_le_one (N : ℕ) (z w : Circle) :
    ‖circleCesaroKernel N z w‖ ≤ 1 := by
  by_cases hN : N = 0
  · simp [circleCesaroKernel, hN]
  rw [circleCesaroKernel, norm_mul, norm_inv, Complex.norm_natCast]
  calc
    (N : ℝ)⁻¹ * ‖∑ n ∈ range N, (((z / w : Circle) : ℂ) ^ n)‖ ≤
        (N : ℝ)⁻¹ * ∑ _n ∈ range N, 1 := by
          gcongr
          calc
            ‖∑ n ∈ range N, (((z / w : Circle) : ℂ) ^ n)‖ ≤
                ∑ n ∈ range N, ‖(((z / w : Circle) : ℂ) ^ n)‖ :=
              norm_sum_le _ _
            _ = ∑ _n ∈ range N, 1 := by simp [Circle.norm_coe]
    _ = 1 := by
      simp [hN]

theorem tendsto_circleCesaroKernel (z w : Circle) :
    Tendsto (fun N ↦ circleCesaroKernel N z w) atTop
      (nhds (if z = w then 1 else 0)) := by
  classical
  by_cases hzw : z = w
  · subst w
    have hev : ∀ᶠ N in atTop, N ≠ 0 :=
      (eventually_gt_atTop 0).mono fun N hN ↦ hN.ne'
    have heq : ∀ᶠ N in atTop, circleCesaroKernel N z z = 1 := by
      filter_upwards [hev] with N hN
      simp [circleCesaroKernel, hN]
    simpa using (tendsto_const_nhds (x := (1 : ℂ))).congr'
      (Filter.EventuallyEq.symm heq)
  · simp only [if_neg hzw]
    have ht : (((z / w : Circle) : ℂ)) ≠ 1 := by
      intro h
      have hcircle : z / w = (1 : Circle) := Circle.coe_injective h
      exact hzw (div_eq_one.mp hcircle)
    have hbound : IsBoundedUnder (· ≤ ·) atTop
        (norm ∘ fun N : ℕ ↦
          ((((z / w : Circle) : ℂ) ^ N - 1) /
            (((z / w : Circle) : ℂ) - 1))) := by
      apply isBoundedUnder_of_eventually_le
        (a := 2 / ‖(((z / w : Circle) : ℂ) - 1)‖)
      exact Eventually.of_forall fun N ↦ by
        rw [Function.comp_apply, norm_div]
        gcongr
        calc
          ‖((z / w : Circle) : ℂ) ^ N - 1‖ ≤
              ‖((z / w : Circle) : ℂ) ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
          _ = 2 := by simp [Circle.norm_coe]; norm_num
    have hzero := NormedField.tendsto_zero_smul_of_tendsto_zero_of_bounded
      (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℂ)) hbound
    apply hzero.congr'
    filter_upwards with N
    rw [circleCesaroKernel, geom_sum_eq ht]
    rfl

theorem tendsto_integral_circleCesaroKernel_zero
    (μ : Measure Circle) [IsFiniteMeasure μ] [NullSingletonClass μ] :
    Tendsto
      (fun N ↦ ∫ zw, circleCesaroKernel N zw.1 zw.2 ∂(μ.prod μ))
      atTop (nhds 0) := by
  have hdiag : μ.prod μ {zw : Circle × Circle | zw.1 = zw.2} = 0 := by
    apply Measure.measure_prod_null_of_ae_null isClosed_diagonal.measurableSet
    exact Eventually.of_forall fun z ↦ by
      change μ (Prod.mk z ⁻¹' diagonal Circle) = 0
      rw [show Prod.mk z ⁻¹' diagonal Circle = {z} by
        ext w
        simp [eq_comm]]
      exact measure_singleton z
  have hne : ∀ᵐ zw ∂(μ.prod μ), zw.1 ≠ zw.2 := by
    rw [ae_iff]
    simpa only [not_not] using hdiag
  have hmeas : ∀ N, AEStronglyMeasurable
      (fun zw : Circle × Circle ↦ circleCesaroKernel N zw.1 zw.2)
        (μ.prod μ) := by
    intro N
    apply Continuous.aestronglyMeasurable
    unfold circleCesaroKernel
    have hdiv : Continuous
        (fun zw : Circle × Circle ↦ (zw.1 / zw.2 : Circle)) :=
      by
        convert (continuous_fst.mul continuous_snd.inv :
          Continuous (fun zw : Circle × Circle ↦ zw.1 * zw.2⁻¹)) using 1
        ext zw
        simp [div_eq_mul_inv]
    have hbase : Continuous
        (fun zw : Circle × Circle ↦ (((zw.1 / zw.2 : Circle) : ℂ))) :=
      continuous_subtype_val.comp hdiv
    exact continuous_const.mul
      (continuous_finsetSum (range N) fun n _hn ↦ hbase.pow n)
  have hbound : ∀ N, ∀ zw : Circle × Circle,
      ‖circleCesaroKernel N zw.1 zw.2‖ ≤ (1 : ℝ) :=
    fun N zw ↦ norm_circleCesaroKernel_le_one N zw.1 zw.2
  have hlim : ∀ᵐ zw ∂(μ.prod μ),
      Tendsto (fun N ↦ circleCesaroKernel N zw.1 zw.2)
        atTop (nhds 0) := by
    filter_upwards [hne] with zw hzw
    simpa [hzw] using tendsto_circleCesaroKernel zw.1 zw.2
  have h := tendsto_integral_filter_of_dominated_convergence
    (μ := μ.prod μ) (F := fun N zw ↦ circleCesaroKernel N zw.1 zw.2)
    (f := fun _ ↦ (0 : ℂ)) (fun _ ↦ (1 : ℝ))
    (Eventually.of_forall hmeas)
    (Eventually.of_forall fun N ↦ Eventually.of_forall (hbound N))
    (integrable_const (1 : ℝ)) hlim
  simpa using h

noncomputable def circleFourierCoeff (μ : Measure Circle) (n : ℕ) : ℂ :=
  ∫ z, (z : ℂ) ^ n ∂μ

theorem integral_circle_div_pow_prod (μ : Measure Circle) [IsFiniteMeasure μ]
    (n : ℕ) :
    (∫ zw, (((zw.1 / zw.2 : Circle) : ℂ) ^ n) ∂(μ.prod μ)) =
      circleFourierCoeff μ n * conj (circleFourierCoeff μ n) := by
  calc
    (∫ zw, (((zw.1 / zw.2 : Circle) : ℂ) ^ n) ∂(μ.prod μ)) =
        ∫ zw, ((zw.1 : ℂ) ^ n) * (((zw.2⁻¹ : Circle) : ℂ) ^ n)
          ∂(μ.prod μ) := by
            apply integral_congr_ae
            exact Eventually.of_forall fun zw ↦ by
              simp [div_eq_mul_inv, mul_pow]
    _ = (∫ z, (z : ℂ) ^ n ∂μ) *
        ∫ w, (((w⁻¹ : Circle) : ℂ) ^ n) ∂μ := by
          exact integral_prod_mul (μ := μ) (ν := μ)
            (fun z : Circle ↦ (z : ℂ) ^ n)
            (fun w : Circle ↦ (((w⁻¹ : Circle) : ℂ) ^ n))
    _ = circleFourierCoeff μ n * conj (circleFourierCoeff μ n) := by
      unfold circleFourierCoeff
      rw [← integral_conj]
      congr 2
      funext w
      rw [Circle.coe_inv_eq_conj]
      exact (map_pow (starRingEnd ℂ) (w : ℂ) n).symm

theorem integral_circleCesaroKernel_eq (μ : Measure Circle) [IsFiniteMeasure μ]
    (N : ℕ) :
    (∫ zw, circleCesaroKernel N zw.1 zw.2 ∂(μ.prod μ)) =
      (N : ℂ)⁻¹ * ∑ n ∈ range N,
        circleFourierCoeff μ n * conj (circleFourierCoeff μ n) := by
  have hterm (n : ℕ) : Integrable
      (fun zw : Circle × Circle ↦ (((zw.1 / zw.2 : Circle) : ℂ) ^ n))
        (μ.prod μ) := by
    have hdiv : Continuous
        (fun zw : Circle × Circle ↦ (zw.1 / zw.2 : Circle)) := by
      convert (continuous_fst.mul continuous_snd.inv :
        Continuous (fun zw : Circle × Circle ↦ zw.1 * zw.2⁻¹)) using 1
      ext zw
      simp [div_eq_mul_inv]
    have hcont : Continuous
        (fun zw : Circle × Circle ↦ (((zw.1 / zw.2 : Circle) : ℂ) ^ n)) :=
      (continuous_subtype_val.comp hdiv).pow n
    simpa only [integrableOn_univ] using
      hcont.continuousOn.integrableOn_of_subset_isCompact
        isCompact_univ MeasurableSet.univ Subset.rfl
          (measure_ne_top (μ.prod μ) Set.univ)
  unfold circleCesaroKernel
  rw [integral_const_mul, integral_finsetSum (range N)
    (fun n _hn ↦ hterm n)]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  exact integral_circle_div_pow_prod μ n

theorem tendsto_wiener_average_sq_zero
    (μ : Measure Circle) [IsFiniteMeasure μ] [NullSingletonClass μ] :
    Tendsto
      (fun N : ℕ ↦ (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N,
        ‖circleFourierCoeff μ n‖ ^ 2)
      atTop (nhds 0) := by
  have hcomplex := tendsto_integral_circleCesaroKernel_zero μ
  have hre := Complex.continuous_re.continuousAt.tendsto.comp hcomplex
  apply hre.congr'
  filter_upwards with N
  change Complex.re
    (∫ zw, circleCesaroKernel N zw.1 zw.2 ∂(μ.prod μ)) = _
  rw [integral_circleCesaroKernel_eq μ N]
  simp only [map_mul, map_inv₀, map_natCast, map_sum, Complex.ofReal_inv,
    Complex.mul_conj', Complex.ofReal_pow, Complex.ofReal_sum,
    Complex.ofReal_mul]
  simp only [Complex.mul_re, Complex.inv_re, Complex.natCast_re, Complex.normSq_natCast, div_self_mul_self',
    Complex.re_sum, Complex.inv_im, Complex.natCast_im, neg_zero, zero_div, Complex.im_sum, zero_mul, sub_zero,
    mul_eq_mul_left_iff, inv_eq_zero, Nat.cast_eq_zero]
  left
  apply Finset.sum_congr rfl
  intro i hi
  norm_num [pow_two, Complex.mul_re]

open Filter Finset Function MeasureTheory Set
open scoped ComplexConjugate ENNReal NNReal Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

noncomputable local instance : MeasurableSpace Circle := borel Circle
local instance : BorelSpace Circle := ⟨rfl⟩
noncomputable local instance : DecidableEq Circle := Classical.decEq Circle

/-- The spectrum of a unitary operator, regarded as a subspace of the unit circle. -/
noncomputable def spectrumToCircle (U : H ≃ₗᵢ[ℂ] H) : UnitarySpectrum U → Circle :=
  fun z ↦ ⟨z.1, by
    change dist z.1 0 = 1
    rw [dist_zero_right]
    exact spectrum.norm_eq_one_of_unitary (unitaryOperator_mem U) z.2⟩

theorem spectrumToCircle_injective (U : H ≃ₗᵢ[ℂ] H) :
    Injective (spectrumToCircle U) := by
  intro z w h
  apply Subtype.ext
  exact congrArg (fun q : Circle ↦ (q : ℂ)) h

theorem continuous_spectrumToCircle (U : H ≃ₗᵢ[ℂ] H) :
    Continuous (spectrumToCircle U) := by
  unfold spectrumToCircle
  exact Continuous.subtype_mk continuous_subtype_val _

noncomputable def circleSpectralMeasure (U : H ≃ₗᵢ[ℂ] H) (x : H) :
    Measure Circle :=
  Measure.map (spectrumToCircle U) (spectralMeasure U x)

noncomputable def spectralPow (U : H ≃ₗᵢ[ℂ] H) (n : ℕ) :
    C(UnitarySpectrum U, ℂ) :=
  (ContinuousMap.restrict (spectrum ℂ (unitaryOperator U))
    (ContinuousMap.id ℂ)) ^ n

@[simp] theorem spectralPow_apply (U : H ≃ₗᵢ[ℂ] H) (n : ℕ)
    (z : UnitarySpectrum U) : spectralPow U n z = (z.1 : ℂ) ^ n := rfl

theorem cfcHom_spectralPow (U : H ≃ₗᵢ[ℂ] H) (n : ℕ) :
    cfcHom (isStarNormal_of_mem_unitary (unitaryOperator_mem U))
        (spectralPow U n) =
      (unitaryOperator U) ^ n := by
  rw [spectralPow, map_pow, cfcHom_id]

theorem circleFourierCoeff_circleSpectralMeasure
    (U : H ≃ₗᵢ[ℂ] H) (x : H) (n : ℕ) :
    circleFourierCoeff (circleSpectralMeasure U x) n =
      inner ℂ x (((unitaryOperator U) ^ n) x) := by
  unfold circleFourierCoeff circleSpectralMeasure
  have hc : Continuous (fun z : Circle ↦ (z : ℂ) ^ n) :=
    (show Continuous (fun z : Circle ↦ (z : ℂ)) from continuous_subtype_val).pow n
  rw [MeasureTheory.integral_map
    (continuous_spectrumToCircle U).measurable.aemeasurable
    hc.aestronglyMeasurable]
  change (∫ z, spectralPow U n z ∂spectralMeasure U x) = _
  rw [integral_spectralMeasure_complex, cfcHom_spectralPow]

/-- The algebraic span of all unit-circle eigenvectors. -/
noncomputable def unitaryEigenSpan (U : H ≃ₗᵢ[ℂ] H) : Submodule ℂ H :=
  Submodule.span ℂ {y | ∃ z : Circle, U y = (z : ℂ) • y}

/-- The closed Kronecker subspace generated by all eigenvectors. -/
noncomputable def unitaryKronecker (U : H ≃ₗᵢ[ℂ] H) : ClosedSubmodule ℂ H :=
  (unitaryEigenSpan U).closure

theorem unitaryEigenSpan_le_kronecker (U : H ≃ₗᵢ[ℂ] H) :
    unitaryEigenSpan U ≤ (unitaryKronecker U).toSubmodule :=
  (unitaryEigenSpan U).le_topologicalClosure

theorem eigenvector_mem_kronecker (U : H ≃ₗᵢ[ℂ] H) {y : H} {z : Circle}
    (hy : U y = (z : ℂ) • y) : y ∈ unitaryKronecker U := by
  apply unitaryEigenSpan_le_kronecker U
  exact Submodule.subset_span ⟨z, hy⟩

noncomputable def unitaryCompactPart (U : H ≃ₗᵢ[ℂ] H) (x : H) : H :=
  ((unitaryKronecker U).toSubmodule).orthogonalProjectionOnto x

noncomputable def unitaryWeakPart (U : H ≃ₗᵢ[ℂ] H) (x : H) : H :=
  x - unitaryCompactPart U x

theorem unitaryWeakPart_mem_orthogonal (U : H ≃ₗᵢ[ℂ] H) (x : H) :
    unitaryWeakPart U x ∈ ((unitaryKronecker U).toSubmodule)ᗮ := by
  change x - ((unitaryKronecker U).toSubmodule).starProjection x ∈
    ((unitaryKronecker U).toSubmodule)ᗮ
  exact ((unitaryKronecker U).toSubmodule).sub_starProjection_mem_orthogonal x

theorem inner_unitaryWeakPart_eigenvector (U : H ≃ₗᵢ[ℂ] H) (x : H)
    {y : H} {z : Circle} (hy : U y = (z : ℂ) • y) :
    inner ℂ (unitaryWeakPart U x) y = 0 := by
  exact Submodule.inner_left_of_mem_orthogonal
    (eigenvector_mem_kronecker U hy) (unitaryWeakPart_mem_orthogonal U x)

/-- Twist a unitary by the inverse of a unit-circle scalar. Its fixed vectors
are precisely the eigenvectors with the given eigenvalue. -/
noncomputable def twistedUnitary (U : H ≃ₗᵢ[ℂ] H) (z : Circle) : H →L[ℂ] H :=
  (z : ℂ)⁻¹ • unitaryOperator U

theorem twistedUnitary_norm_le_one (U : H ≃ₗᵢ[ℂ] H) (z : Circle) :
    ‖twistedUnitary U z‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro y
  change ‖(z : ℂ)⁻¹ • U y‖ ≤ 1 * ‖y‖
  rw [norm_smul, norm_inv, Circle.norm_coe, inv_one, U.norm_map, one_mul]

theorem mem_eqLocus_twistedUnitary_iff (U : H ≃ₗᵢ[ℂ] H) (z : Circle)
    (y : H) :
    y ∈ (twistedUnitary U z).eqLocus (1 : H →L[ℂ] H) ↔
      U y = (z : ℂ) • y := by
  change (z : ℂ)⁻¹ • U y = y ↔ _
  constructor
  · intro h
    calc
      U y = (z : ℂ) • ((z : ℂ)⁻¹ • U y) := by
        rw [smul_smul, mul_inv_cancel₀ (Circle.coe_ne_zero z), one_smul]
      _ = (z : ℂ) • y := by rw [h]
  · intro h
    rw [h, smul_smul, inv_mul_cancel₀ (Circle.coe_ne_zero z), one_smul]

theorem unitaryWeakPart_mem_twisted_fixed_orthogonal
    (U : H ≃ₗᵢ[ℂ] H) (x : H) (z : Circle) :
    unitaryWeakPart U x ∈
      ((twistedUnitary U z).eqLocus (1 : H →L[ℂ] H))ᗮ := by
  rw [Submodule.mem_orthogonal]
  intro y hy
  exact inner_eq_zero_symm.mp <| inner_unitaryWeakPart_eigenvector U x
    ((mem_eqLocus_twistedUnitary_iff U z y).mp hy)

theorem tendsto_twisted_birkhoffAverage_weakPart
    (U : H ≃ₗᵢ[ℂ] H) (x : H) (z : Circle) :
    Tendsto
      (fun N ↦ birkhoffAverage ℂ (twistedUnitary U z) _root_.id N
        (unitaryWeakPart U x))
      atTop (nhds 0) := by
  have hmean := (twistedUnitary U z).tendsto_birkhoffAverage_orthogonalProjection
    (twistedUnitary_norm_le_one U z) (unitaryWeakPart U x)
  have hzero :
      ((twistedUnitary U z).eqLocus (1 : H →L[ℂ] H)).orthogonalProjectionOnto
        (unitaryWeakPart U x) = 0 :=
    Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal
      (unitaryWeakPart_mem_twisted_fixed_orthogonal U x z)
  have hzero_coe :
      (((((twistedUnitary U z).eqLocus (1 : H →L[ℂ] H)).orthogonalProjectionOnto
        (unitaryWeakPart U x)) :
          (twistedUnitary U z).eqLocus (1 : H →L[ℂ] H)) : H) = 0 :=
    congrArg Subtype.val hzero
  simpa only [hzero_coe] using hmean

theorem tendsto_integral_circleCesaroKernel_right
    (μ : Measure Circle) [IsFiniteMeasure μ] (w : Circle) :
    Tendsto (fun N ↦ ∫ z, circleCesaroKernel N z w ∂μ) atTop
      (nhds (μ.real {w} : ℂ)) := by
  have hmeas : ∀ N, AEStronglyMeasurable
      (fun z : Circle ↦ circleCesaroKernel N z w) μ := by
    intro N
    apply Continuous.aestronglyMeasurable
    unfold circleCesaroKernel
    have hdiv : Continuous (fun z : Circle ↦ (z / w : Circle)) :=
      continuous_id.mul continuous_const.inv
    have hbase : Continuous (fun z : Circle ↦ (((z / w : Circle) : ℂ))) :=
      continuous_subtype_val.comp hdiv
    exact continuous_const.mul
      (continuous_finsetSum (range N) fun n _hn ↦ hbase.pow n)
  have hbound : ∀ N, ∀ z : Circle,
      ‖circleCesaroKernel N z w‖ ≤ (1 : ℝ) :=
    fun N z ↦ norm_circleCesaroKernel_le_one N z w
  have hlim : ∀ᵐ z ∂μ,
      Tendsto (fun N ↦ circleCesaroKernel N z w) atTop
        (nhds (if z = w then 1 else 0)) :=
    Eventually.of_forall fun z ↦ tendsto_circleCesaroKernel z w
  have h := tendsto_integral_filter_of_dominated_convergence
    (μ := μ) (F := fun N z ↦ circleCesaroKernel N z w)
    (f := fun z ↦ if z = w then (1 : ℂ) else 0)
    (fun _ ↦ (1 : ℝ))
    (Eventually.of_forall hmeas)
    (Eventually.of_forall fun N ↦ Eventually.of_forall (hbound N))
    (integrable_const (1 : ℝ)) hlim
  convert h using 1
  rw [show (fun z : Circle ↦ if z = w then (1 : ℂ) else 0) =
      Set.indicator ({w} : Set Circle) (fun _ ↦ (1 : ℂ)) by
    funext z
    by_cases hzw : z = w <;> simp [hzw]]
  have hwmeas : MeasurableSet ({w} : Set Circle) := measurableSet_singleton w
  rw [integral_indicator_const (μ := μ) (s := ({w} : Set Circle)) (1 : ℂ) hwmeas]
  simp

theorem integral_circle_div_pow_right (μ : Measure Circle) [IsFiniteMeasure μ]
    (w : Circle) (n : ℕ) :
    (∫ z, (((z / w : Circle) : ℂ) ^ n) ∂μ) =
      ((w : ℂ)⁻¹ ^ n) * circleFourierCoeff μ n := by
  calc
    (∫ z, (((z / w : Circle) : ℂ) ^ n) ∂μ) =
        ∫ z, ((w : ℂ)⁻¹ ^ n) * ((z : ℂ) ^ n) ∂μ := by
          apply integral_congr_ae
          exact Eventually.of_forall fun z ↦ by
            change ((z : ℂ) / (w : ℂ)) ^ n = _
            rw [div_pow]
            ring
    _ = ((w : ℂ)⁻¹ ^ n) * ∫ z, ((z : ℂ) ^ n) ∂μ :=
      integral_const_mul _ _
    _ = ((w : ℂ)⁻¹ ^ n) * circleFourierCoeff μ n := rfl

theorem integral_circleCesaroKernel_right_eq (μ : Measure Circle)
    [IsFiniteMeasure μ] (w : Circle) (N : ℕ) :
    (∫ z, circleCesaroKernel N z w ∂μ) =
      (N : ℂ)⁻¹ * ∑ n ∈ range N,
        ((w : ℂ)⁻¹ ^ n) * circleFourierCoeff μ n := by
  have hterm (n : ℕ) : Integrable
      (fun z : Circle ↦ (((z / w : Circle) : ℂ) ^ n)) μ := by
    have hdiv : Continuous (fun z : Circle ↦ (z / w : Circle)) :=
      continuous_id.mul continuous_const.inv
    have hcont : Continuous (fun z : Circle ↦ (((z / w : Circle) : ℂ) ^ n)) :=
      (continuous_subtype_val.comp hdiv).pow n
    simpa only [integrableOn_univ] using
      hcont.continuousOn.integrableOn_compact (μ := μ) isCompact_univ
  unfold circleCesaroKernel
  rw [integral_const_mul, integral_finsetSum (range N)
    (fun n _hn ↦ hterm n)]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  exact integral_circle_div_pow_right μ w n

theorem iterate_twistedUnitary_apply (U : H ≃ₗᵢ[ℂ] H)
    (w : Circle) (n : ℕ) (x : H) :
    (twistedUnitary U w)^[n] x =
      ((w : ℂ)⁻¹ ^ n) • (((unitaryOperator U) ^ n) x) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      change (w : ℂ)⁻¹ • U
        (((w : ℂ)⁻¹ ^ n) • (((unitaryOperator U) ^ n) x)) = _
      rw [U.map_smul, smul_smul]
      change ((w : ℂ)⁻¹ * (w : ℂ)⁻¹ ^ n) •
          (U (((unitaryOperator U) ^ n) x)) = _
      rw [show (w : ℂ)⁻¹ * (w : ℂ)⁻¹ ^ n = (w : ℂ)⁻¹ ^ (n + 1) by
        rw [pow_succ']]
      congr 1
      rw [pow_succ']
      rfl

theorem integral_circleCesaroKernel_circleSpectralMeasure_eq
    (U : H ≃ₗᵢ[ℂ] H) (x : H) (w : Circle) (N : ℕ) :
    (∫ z, circleCesaroKernel N z w ∂circleSpectralMeasure U x) =
      inner ℂ x
        (birkhoffAverage ℂ (twistedUnitary U w) _root_.id N x) := by
  let : IsFiniteMeasure (spectralMeasure U x) := by
    unfold spectralMeasure
    infer_instance
  let : IsFiniteMeasure (circleSpectralMeasure U x) := by
    unfold circleSpectralMeasure
    exact Measure.isFiniteMeasure_map (spectralMeasure U x) (spectrumToCircle U)
  rw [integral_circleCesaroKernel_right_eq]
  simp_rw [circleFourierCoeff_circleSpectralMeasure]
  unfold birkhoffAverage birkhoffSum
  rw [inner_smul_right, inner_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  rw [iterate_twistedUnitary_apply, id_eq]
  exact (inner_smul_right x (((unitaryOperator U) ^ n) x)
    ((w : ℂ)⁻¹ ^ n)).symm

theorem circleSpectralMeasure_weakPart_singleton
    (U : H ≃ₗᵢ[ℂ] H) (x : H) (w : Circle) :
    circleSpectralMeasure U (unitaryWeakPart U x) {w} = 0 := by
  let xw := unitaryWeakPart U x
  let μ := circleSpectralMeasure U xw
  let : IsFiniteMeasure (spectralMeasure U xw) := by
    unfold spectralMeasure
    infer_instance
  let : IsFiniteMeasure μ := by
    dsimp [μ, circleSpectralMeasure]
    exact Measure.isFiniteMeasure_map (spectralMeasure U xw) (spectrumToCircle U)
  have hmass : Tendsto (fun N ↦ ∫ z, circleCesaroKernel N z w ∂μ)
      atTop (nhds (μ.real {w} : ℂ)) :=
    tendsto_integral_circleCesaroKernel_right μ w
  have hmean : Tendsto
      (fun N ↦ birkhoffAverage ℂ (twistedUnitary U w) _root_.id N xw)
      atTop (nhds 0) := by
    simpa only [xw] using tendsto_twisted_birkhoffAverage_weakPart U x w
  have hinner : Tendsto
      (fun N ↦ inner ℂ xw
        (birkhoffAverage ℂ (twistedUnitary U w) _root_.id N xw))
      atTop (nhds 0) := by
    have hmap : Tendsto (innerSL ℂ xw) (nhds 0) (nhds 0) := by
      simpa only [map_zero] using (innerSL ℂ xw).continuous.tendsto (0 : H)
    have hh := hmap.comp hmean
    apply hh.congr'
    exact Eventually.of_forall fun N ↦
      innerSL_apply_apply (𝕜 := ℂ) xw
        (birkhoffAverage ℂ (twistedUnitary U w) _root_.id N xw)
  have hintegral : Tendsto (fun N ↦ ∫ z, circleCesaroKernel N z w ∂μ)
      atTop (nhds 0) := by
    apply hinner.congr'
    exact Eventually.of_forall fun N ↦ by
      symm
      exact integral_circleCesaroKernel_circleSpectralMeasure_eq U xw w N
  have hrealComplex : (μ.real {w} : ℂ) = 0 :=
    tendsto_nhds_unique hmass hintegral
  have hreal : μ.real {w} = 0 := by
    exact_mod_cast hrealComplex
  exact (measureReal_eq_zero_iff (μ := μ) (s := ({w} : Set Circle))).mp hreal

theorem tendsto_unitaryWeakPart_selfCorrelation_sq_average
    (U : H ≃ₗᵢ[ℂ] H) (x : H) :
    Tendsto
      (fun N : ℕ ↦ (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N,
        ‖inner ℂ (unitaryWeakPart U x)
          (((unitaryOperator U) ^ n) (unitaryWeakPart U x))‖ ^ 2)
      atTop (nhds 0) := by
  let xw := unitaryWeakPart U x
  let μ := circleSpectralMeasure U xw
  let : IsFiniteMeasure (spectralMeasure U xw) := by
    unfold spectralMeasure
    infer_instance
  let : IsFiniteMeasure μ := by
    dsimp [μ, circleSpectralMeasure]
    exact Measure.isFiniteMeasure_map (spectralMeasure U xw) (spectrumToCircle U)
  let : NullSingletonClass μ :=
    ⟨fun w ↦ circleSpectralMeasure_weakPart_singleton U x w⟩
  simpa only [μ, xw, circleFourierCoeff_circleSpectralMeasure] using
    tendsto_wiener_average_sq_zero μ

theorem tendsto_unitaryWeakPart_selfCorrelation_average
    (U : H ≃ₗᵢ[ℂ] H) (x : H) :
    Tendsto
      (fun N : ℕ ↦ (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N,
        ‖inner ℂ (unitaryWeakPart U x)
          (((unitaryOperator U) ^ n) (unitaryWeakPart U x))‖)
      atTop (nhds 0) := by
  let a : ℕ → ℝ := fun n ↦
    ‖inner ℂ (unitaryWeakPart U x)
      (((unitaryOperator U) ^ n) (unitaryWeakPart U x))‖
  let q : ℕ → ℝ := fun N ↦
    (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, a n ^ 2
  have hq : Tendsto q atTop (nhds 0) := by
    simpa only [q, a] using tendsto_unitaryWeakPart_selfCorrelation_sq_average U x
  have hsqrt : Tendsto (fun N ↦ Real.sqrt (q N)) atTop (nhds 0) := by
    simpa [Function.comp_def] using
      Real.continuous_sqrt.continuousAt.tendsto.comp hq
  change Tendsto
    (fun N : ℕ ↦ (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, a n)
    atTop (nhds 0)
  refine squeeze_zero
    (f := fun N : ℕ ↦ (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, a n)
    (g := fun N : ℕ ↦ Real.sqrt (q N)) ?_ ?_ hsqrt
  · intro N
    exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg N))
      (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)
  · intro N
    by_cases hN : N = 0
    · subst N
      simp [q]
    · have hNpos : (0 : ℝ) < N := by exact_mod_cast (Nat.pos_of_ne_zero hN)
      have hcs := sum_mul_sq_le_sq_mul_sq (Finset.range N)
        (fun _ : ℕ ↦ (1 : ℝ)) a
      simp only [one_mul, one_pow, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul, mul_one] at hcs
      apply Real.le_sqrt_of_sq_le
      calc
        ((N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, a n) ^ 2 =
            (N : ℝ)⁻¹ ^ 2 * (∑ n ∈ Finset.range N, a n) ^ 2 := by ring
        _ ≤ (N : ℝ)⁻¹ ^ 2 *
            ((N : ℝ) * ∑ n ∈ Finset.range N, a n ^ 2) :=
          mul_le_mul_of_nonneg_left hcs (sq_nonneg _)
        _ = q N := by
          dsimp [q]
          field_simp

noncomputable def unitaryCorrelationAverage (U : H ≃ₗᵢ[ℂ] H)
    (x y : H) (N : ℕ) : ℝ :=
  (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N,
    ‖inner ℂ y (((unitaryOperator U) ^ n) x)‖

theorem unitaryOperator_pow_apply (U : H ≃ₗᵢ[ℂ] H) (n : ℕ) (x : H) :
    ((unitaryOperator U) ^ n) x = (U ^ n) x := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', pow_succ', ContinuousLinearMap.mul_apply, ih]
      rfl

theorem inner_unitary_pow_left_right (U : H ≃ₗᵢ[ℂ] H)
    (x : H) (k m : ℕ) :
    inner ℂ ((U ^ k) x) ((U ^ (k + m)) x) =
      inner ℂ x ((U ^ m) x) := by
  rw [pow_add]
  exact (U ^ k).inner_map_map x ((U ^ m) x)

theorem unitaryCorrelationAverage_self (U : H ≃ₗᵢ[ℂ] H) (x : H) (N : ℕ) :
    unitaryCorrelationAverage U x x N =
      (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N,
        ‖inner ℂ x (((unitaryOperator U) ^ n) x)‖ := rfl

theorem tendsto_unitaryCorrelationAverage_orbit_weakPart
    (U : H ≃ₗᵢ[ℂ] H) (x : H) (k : ℕ) :
    Tendsto
      (fun N ↦ unitaryCorrelationAverage U (unitaryWeakPart U x)
        ((U ^ k) (unitaryWeakPart U x)) N)
      atTop (nhds 0) := by
  let xw := unitaryWeakPart U x
  let b : ℕ → ℝ := fun n ↦
    ‖inner ℂ xw (((unitaryOperator U) ^ n) xw)‖
  let c : ℝ := ∑ n ∈ Finset.range k,
    ‖inner ℂ ((U ^ k) xw) (((unitaryOperator U) ^ n) xw)‖
  have hself : Tendsto
      (fun N : ℕ ↦ (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, b n)
      atTop (nhds 0) := by
    simpa only [b, xw] using tendsto_unitaryWeakPart_selfCorrelation_average U x
  have hprefix : Tendsto (fun N : ℕ ↦ (N : ℝ)⁻¹ * c) atTop (nhds 0) := by
    simpa only [Function.comp_apply, zero_mul] using
      (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).mul_const c
  change Tendsto
    (fun N ↦ unitaryCorrelationAverage U xw ((U ^ k) xw) N)
    atTop (nhds 0)
  refine squeeze_zero
    (f := fun N ↦ unitaryCorrelationAverage U xw ((U ^ k) xw) N)
    (g := fun N ↦ (N : ℝ)⁻¹ * c +
      (N : ℝ)⁻¹ * ∑ m ∈ Finset.range N, b m) ?_ ?_ ?_
  · intro N
    exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg N))
      (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)
  · intro N
    by_cases hkN : k ≤ N
    · have hsplit := Finset.sum_range_add_sum_Ico
          (fun n ↦ ‖inner ℂ ((U ^ k) xw)
            (((unitaryOperator U) ^ n) xw)‖) hkN
      have htail :
          (∑ n ∈ Finset.Ico k N,
              ‖inner ℂ ((U ^ k) xw)
                (((unitaryOperator U) ^ n) xw)‖) =
            ∑ m ∈ Finset.range (N - k), b m := by
        rw [Finset.sum_Ico_eq_sum_range]
        apply Finset.sum_congr rfl
        intro m hm
        dsimp [b]
        rw [unitaryOperator_pow_apply, unitaryOperator_pow_apply]
        rw [inner_unitary_pow_left_right]
      have hsubset : Finset.range (N - k) ⊆ Finset.range N :=
        Finset.range_subset_range.mpr (Nat.sub_le N k)
      have htail_le :
          (∑ m ∈ Finset.range (N - k), b m) ≤
            ∑ m ∈ Finset.range N, b m :=
        Finset.sum_le_sum_of_subset_of_nonneg hsubset
          (fun i hi hni ↦ norm_nonneg _)
      have htotal :
          (∑ n ∈ Finset.range N,
              ‖inner ℂ ((U ^ k) xw)
                (((unitaryOperator U) ^ n) xw)‖) =
            (∑ n ∈ Finset.range k,
              ‖inner ℂ ((U ^ k) xw)
                (((unitaryOperator U) ^ n) xw)‖) +
              ∑ m ∈ Finset.range (N - k), b m := by
        rw [← htail]
        exact hsplit.symm
      calc
        unitaryCorrelationAverage U xw ((U ^ k) xw) N =
            (N : ℝ)⁻¹ *
            ((∑ n ∈ Finset.range k,
                ‖inner ℂ ((U ^ k) xw)
                  (((unitaryOperator U) ^ n) xw)‖) +
              ∑ m ∈ Finset.range (N - k), b m) := by
          rw [unitaryCorrelationAverage, htotal]
        _ ≤
            (N : ℝ)⁻¹ *
              ((∑ n ∈ Finset.range k,
                  ‖inner ℂ ((U ^ k) xw)
                    (((unitaryOperator U) ^ n) xw)‖) +
                ∑ m ∈ Finset.range N, b m) :=
          mul_le_mul_of_nonneg_left (add_le_add (le_refl _) htail_le)
            (inv_nonneg.mpr (Nat.cast_nonneg N))
        _ = (N : ℝ)⁻¹ * c +
            (N : ℝ)⁻¹ * ∑ m ∈ Finset.range N, b m := by
          dsimp [c]
          ring
    · have hNk : N ≤ k := Nat.le_of_not_ge hkN
      have hsum_le :
          (∑ n ∈ Finset.range N,
              ‖inner ℂ ((U ^ k) xw)
                (((unitaryOperator U) ^ n) xw)‖) ≤ c := by
        dsimp [c]
        apply Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_subset_range.mpr hNk)
        intro i hi hni
        exact norm_nonneg _
      calc
        unitaryCorrelationAverage U xw ((U ^ k) xw) N =
            (N : ℝ)⁻¹ *
            ∑ n ∈ Finset.range N,
              ‖inner ℂ ((U ^ k) xw)
                (((unitaryOperator U) ^ n) xw)‖ := rfl
        _ ≤
            (N : ℝ)⁻¹ * c :=
          mul_le_mul_of_nonneg_left hsum_le
            (inv_nonneg.mpr (Nat.cast_nonneg N))
        _ ≤ (N : ℝ)⁻¹ * c +
            (N : ℝ)⁻¹ * ∑ m ∈ Finset.range N, b m :=
          le_add_of_nonneg_right <| mul_nonneg
            (inv_nonneg.mpr (Nat.cast_nonneg N))
            (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)
  · simpa only [Pi.add_apply, zero_add] using hprefix.add hself

theorem unitaryCorrelationAverage_lipschitz (U : H ≃ₗᵢ[ℂ] H) (x : H) (N : ℕ) :
    LipschitzWith ‖x‖₊ (fun y ↦ unitaryCorrelationAverage U x y N) := by
  apply LipschitzWith.of_dist_le_mul
  intro y z
  by_cases hN : N = 0
  · subst N
    simp only [unitaryCorrelationAverage, Nat.cast_zero, inv_zero,
      Finset.range_zero, Finset.sum_empty, mul_zero, dist_self, coe_nnnorm]
    exact mul_nonneg (norm_nonneg _) dist_nonneg
  · have hNpos : (0 : ℝ) < N := by exact_mod_cast (Nat.pos_of_ne_zero hN)
    have hsum :
        |(∑ n ∈ Finset.range N,
              ‖inner ℂ y (((unitaryOperator U) ^ n) x)‖) -
            ∑ n ∈ Finset.range N,
              ‖inner ℂ z (((unitaryOperator U) ^ n) x)‖| ≤
          ∑ _n ∈ Finset.range N, ‖y - z‖ * ‖x‖ := by
      rw [← Finset.sum_sub_distrib]
      calc
        |∑ n ∈ Finset.range N,
            (‖inner ℂ y (((unitaryOperator U) ^ n) x)‖ -
              ‖inner ℂ z (((unitaryOperator U) ^ n) x)‖)| ≤
            ∑ n ∈ Finset.range N,
              |‖inner ℂ y (((unitaryOperator U) ^ n) x)‖ -
                ‖inner ℂ z (((unitaryOperator U) ^ n) x)‖| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _n ∈ Finset.range N, ‖y - z‖ * ‖x‖ := by
          apply Finset.sum_le_sum
          intro n hn
          calc
            |‖inner ℂ y (((unitaryOperator U) ^ n) x)‖ -
                ‖inner ℂ z (((unitaryOperator U) ^ n) x)‖| ≤
                ‖inner ℂ y (((unitaryOperator U) ^ n) x) -
                  inner ℂ z (((unitaryOperator U) ^ n) x)‖ :=
              abs_norm_sub_norm_le _ _
            _ = ‖inner ℂ (y - z) (((unitaryOperator U) ^ n) x)‖ := by
              rw [inner_sub_left]
            _ ≤ ‖y - z‖ * ‖((unitaryOperator U) ^ n) x‖ :=
              norm_inner_le_norm _ _
            _ = ‖y - z‖ * ‖x‖ := by
              rw [unitaryOperator_pow_apply, (U ^ n).norm_map]
    rw [Real.dist_eq]
    change
      |(N : ℝ)⁻¹ *
          (∑ n ∈ Finset.range N,
            ‖inner ℂ y (((unitaryOperator U) ^ n) x)‖) -
        (N : ℝ)⁻¹ *
          (∑ n ∈ Finset.range N,
            ‖inner ℂ z (((unitaryOperator U) ^ n) x)‖)| ≤
        (‖x‖₊ : ℝ) * dist y z
    rw [← mul_sub, abs_mul, abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg N))]
    calc
      (N : ℝ)⁻¹ *
          |(∑ n ∈ Finset.range N,
                ‖inner ℂ y (((unitaryOperator U) ^ n) x)‖) -
            ∑ n ∈ Finset.range N,
                ‖inner ℂ z (((unitaryOperator U) ^ n) x)‖| ≤
          (N : ℝ)⁻¹ *
            ∑ _n ∈ Finset.range N, ‖y - z‖ * ‖x‖ :=
        mul_le_mul_of_nonneg_left hsum
          (inv_nonneg.mpr (Nat.cast_nonneg N))
      _ = ‖x‖ * ‖y - z‖ := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        field_simp
      _ = (‖x‖₊ : ℝ) * dist y z := by
        rw [dist_eq_norm, coe_nnnorm]

theorem unitaryCorrelationAverage_nonneg (U : H ≃ₗᵢ[ℂ] H)
    (x y : H) (N : ℕ) :
    0 ≤ unitaryCorrelationAverage U x y N :=
  mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg N))
    (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)

theorem unitaryCorrelationAverage_add_le (U : H ≃ₗᵢ[ℂ] H)
    (x y z : H) (N : ℕ) :
    unitaryCorrelationAverage U x (y + z) N ≤
      unitaryCorrelationAverage U x y N + unitaryCorrelationAverage U x z N := by
  unfold unitaryCorrelationAverage
  rw [← mul_add, ← Finset.sum_add_distrib]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg N))
  apply Finset.sum_le_sum
  intro n hn
  rw [inner_add_left]
  exact norm_add_le _ _

theorem unitaryCorrelationAverage_smul (U : H ≃ₗᵢ[ℂ] H)
    (x y : H) (c : ℂ) (N : ℕ) :
    unitaryCorrelationAverage U x (c • y) N =
      ‖c‖ * unitaryCorrelationAverage U x y N := by
  have hinner (n : ℕ) :
      inner ℂ (c • y) (((unitaryOperator U) ^ n) x) =
        star c * inner ℂ y (((unitaryOperator U) ^ n) x) :=
    inner_smul_left y _ c
  unfold unitaryCorrelationAverage
  simp_rw [hinner, norm_mul, norm_star]
  rw [← Finset.mul_sum]
  ring

theorem tendsto_unitaryCorrelationAverage_zero (U : H ≃ₗᵢ[ℂ] H) (x : H) :
    Tendsto (fun N ↦ unitaryCorrelationAverage U x 0 N) atTop (nhds 0) := by
  simp [unitaryCorrelationAverage]

theorem tendsto_unitaryCorrelationAverage_add (U : H ≃ₗᵢ[ℂ] H)
    (x y z : H)
    (hy : Tendsto (fun N ↦ unitaryCorrelationAverage U x y N) atTop (nhds 0))
    (hz : Tendsto (fun N ↦ unitaryCorrelationAverage U x z N) atTop (nhds 0)) :
    Tendsto (fun N ↦ unitaryCorrelationAverage U x (y + z) N)
      atTop (nhds 0) := by
  refine squeeze_zero
    (fun N ↦ unitaryCorrelationAverage_nonneg U x (y + z) N)
    (fun N ↦ unitaryCorrelationAverage_add_le U x y z N) ?_
  simpa only [Pi.add_apply, zero_add] using hy.add hz

theorem tendsto_unitaryCorrelationAverage_smul (U : H ≃ₗᵢ[ℂ] H)
    (x y : H) (c : ℂ)
    (hy : Tendsto (fun N ↦ unitaryCorrelationAverage U x y N) atTop (nhds 0)) :
    Tendsto (fun N ↦ unitaryCorrelationAverage U x (c • y) N)
      atTop (nhds 0) := by
  simpa only [unitaryCorrelationAverage_smul, mul_zero] using hy.const_mul ‖c‖

noncomputable def unitaryForwardCyclic (U : H ≃ₗᵢ[ℂ] H) (x : H) :
    Submodule ℂ H :=
  (Submodule.span ℂ (Set.range fun n : ℕ ↦ (U ^ n) x)).topologicalClosure

theorem tendsto_unitaryCorrelationAverage_mem_forwardCyclic_weakPart
    (U : H ≃ₗᵢ[ℂ] H) (x y : H)
    (hy : y ∈ unitaryForwardCyclic U (unitaryWeakPart U x)) :
    Tendsto
      (fun N ↦ unitaryCorrelationAverage U (unitaryWeakPart U x) y N)
      atTop (nhds 0) := by
  let xw := unitaryWeakPart U x
  let S : Set H := {z | Tendsto
    (fun N ↦ unitaryCorrelationAverage U xw z N) atTop (nhds 0)}
  let M : Submodule ℂ H :=
    { carrier := S
      zero_mem' := tendsto_unitaryCorrelationAverage_zero U xw
      add_mem' := fun {y z} hy hz ↦
        tendsto_unitaryCorrelationAverage_add U xw y z hy hz
      smul_mem' := fun c {y} hy ↦
        tendsto_unitaryCorrelationAverage_smul U xw y c hy }
  have hclosed : IsClosed S := by
    have hequi : Equicontinuous
        (fun N : ℕ ↦ fun z : H ↦ unitaryCorrelationAverage U xw z N) :=
      (LipschitzWith.uniformEquicontinuous
        (fun N : ℕ ↦ fun z : H ↦ unitaryCorrelationAverage U xw z N)
        ‖xw‖₊ (fun N ↦ unitaryCorrelationAverage_lipschitz U xw N)).equicontinuous
    exact hequi.isClosed_setOfPred_tendsto continuous_const
  have hMclosed : IsClosed (M : Set H) := by
    change IsClosed S
    exact hclosed
  have hgen : Set.range (fun n : ℕ ↦ (U ^ n) xw) ⊆ (M : Set H) := by
    intro z hz
    obtain ⟨n, rfl⟩ := hz
    exact tendsto_unitaryCorrelationAverage_orbit_weakPart U x n
  have hspan : Submodule.span ℂ (Set.range fun n : ℕ ↦ (U ^ n) xw) ≤ M :=
    Submodule.span_le.mpr hgen
  have hclosure :
      (Submodule.span ℂ (Set.range fun n : ℕ ↦ (U ^ n) xw)).topologicalClosure ≤ M :=
    Submodule.topologicalClosure_minimal _ hspan hMclosed
  exact hclosure (by simpa only [unitaryForwardCyclic, xw] using hy)

theorem unitary_pow_mem_forwardCyclic (U : H ≃ₗᵢ[ℂ] H)
    (x : H) (n : ℕ) :
    (U ^ n) x ∈ unitaryForwardCyclic U x := by
  unfold unitaryForwardCyclic
  apply Submodule.le_topologicalClosure
  exact Submodule.subset_span (Set.mem_range_self n)

theorem tendsto_unitaryWeakPart_correlation_average
    (U : H ≃ₗᵢ[ℂ] H) (x y : H) :
    Tendsto
      (fun N ↦ unitaryCorrelationAverage U (unitaryWeakPart U x) y N)
      atTop (nhds 0) := by
  let xw := unitaryWeakPart U x
  let K := unitaryForwardCyclic U xw
  let : K.HasOrthogonalProjection := by
    dsimp [K, unitaryForwardCyclic]
    infer_instance
  let yp : H := K.starProjection y
  have hyp : yp ∈ K := K.starProjection_apply_mem y
  have hlim : Tendsto
      (fun N ↦ unitaryCorrelationAverage U xw yp N)
      atTop (nhds 0) := by
    exact tendsto_unitaryCorrelationAverage_mem_forwardCyclic_weakPart U x yp hyp
  change Tendsto (fun N ↦ unitaryCorrelationAverage U xw y N) atTop (nhds 0)
  apply hlim.congr'
  exact Eventually.of_forall fun N ↦ by
    change unitaryCorrelationAverage U xw yp N =
      unitaryCorrelationAverage U xw y N
    unfold unitaryCorrelationAverage
    congr 1
    apply Finset.sum_congr rfl
    intro n hn
    congr 1
    rw [unitaryOperator_pow_apply]
    let v : K := ⟨(U ^ n) xw, unitary_pow_mem_forwardCyclic U xw n⟩
    change inner ℂ yp (v : H) = inner ℂ y (v : H)
    exact K.inner_orthogonalProjectionOnto_eq_of_mem_right v y

open Filter Finset Function Set
open scoped ComplexConjugate Pointwise Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem unitary_pow_eigenvector (U : H ≃ₗᵢ[ℂ] H)
    {x : H} {z : Circle} (hx : U x = (z : ℂ) • x) (n : ℕ) :
    (U ^ n) x = (z : ℂ) ^ n • x := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        (U ^ (n + 1)) x = U ((U ^ n) x) := by rw [pow_succ']; rfl
        _ = U ((z : ℂ) ^ n • x) := by rw [ih]
        _ = (z : ℂ) ^ n • U x := by rw [U.map_smul]
        _ = (z : ℂ) ^ n • ((z : ℂ) • x) := by rw [hx]
        _ = (z : ℂ) ^ (n + 1) • x := by rw [smul_smul, pow_succ]

theorem totallyBounded_unitaryOrbit_eigenvector (U : H ≃ₗᵢ[ℂ] H)
    {x : H} {z : Circle} (hx : U x = (z : ℂ) • x) :
    TotallyBounded (Set.range fun n : ℕ ↦ (U ^ n) x) := by
  let f : Circle → H := fun w ↦ (w : ℂ) • x
  have hf : Continuous f :=
    continuous_subtype_val.smul continuous_const
  have hcompact : IsCompact (Set.range f) := by
    rw [← image_univ]
    exact isCompact_univ.image hf
  apply hcompact.totallyBounded.subset
  intro y hy
  obtain ⟨n, rfl⟩ := hy
  refine ⟨z ^ n, ?_⟩
  exact (unitary_pow_eigenvector U hx n).symm

theorem totallyBounded_unitaryOrbit_zero (U : H ≃ₗᵢ[ℂ] H) :
    TotallyBounded (Set.range fun n : ℕ ↦ (U ^ n) (0 : H)) := by
  convert totallyBounded_singleton (0 : H) using 1
  ext y
  simp

theorem totallyBounded_unitaryOrbit_add (U : H ≃ₗᵢ[ℂ] H) (x y : H)
    (hx : TotallyBounded (Set.range fun n : ℕ ↦ (U ^ n) x))
    (hy : TotallyBounded (Set.range fun n : ℕ ↦ (U ^ n) y)) :
    TotallyBounded (Set.range fun n : ℕ ↦ (U ^ n) (x + y)) := by
  let Kx := closure (Set.range fun n : ℕ ↦ (U ^ n) x)
  let Ky := closure (Set.range fun n : ℕ ↦ (U ^ n) y)
  have hKx : IsCompact Kx := hx.closure.isCompact_of_isClosed isClosed_closure
  have hKy : IsCompact Ky := hy.closure.isCompact_of_isClosed isClosed_closure
  have hsum : IsCompact (Kx + Ky) := hKx.add hKy
  apply hsum.totallyBounded.subset
  intro v hv
  obtain ⟨n, rfl⟩ := hv
  change (U ^ n) (x + y) ∈ Kx + Ky
  rw [(U ^ n).map_add]
  exact Set.add_mem_add
    (subset_closure (Set.mem_range_self n))
    (subset_closure (Set.mem_range_self n))

theorem totallyBounded_unitaryOrbit_smul (U : H ≃ₗᵢ[ℂ] H)
    (c : ℂ) (x : H)
    (hx : TotallyBounded (Set.range fun n : ℕ ↦ (U ^ n) x)) :
    TotallyBounded (Set.range fun n : ℕ ↦ (U ^ n) (c • x)) := by
  let K := closure (Set.range fun n : ℕ ↦ (U ^ n) x)
  have hK : IsCompact K := hx.closure.isCompact_of_isClosed isClosed_closure
  have hcK : IsCompact (c • K) := hK.smul c
  apply hcK.totallyBounded.subset
  intro v hv
  obtain ⟨n, rfl⟩ := hv
  change (U ^ n) (c • x) ∈ c • K
  rw [(U ^ n).map_smul]
  exact Set.smul_mem_smul_set (subset_closure (Set.mem_range_self n))

def unitaryAlmostPeriodic (U : H ≃ₗᵢ[ℂ] H) : Set H :=
  {x | TotallyBounded (Set.range fun n : ℕ ↦ (U ^ n) x)}

theorem isClosed_unitaryAlmostPeriodic (U : H ≃ₗᵢ[ℂ] H) :
    IsClosed (unitaryAlmostPeriodic U) := by
  apply closure_subset_iff_isClosed.mp
  intro x hx
  change TotallyBounded (Set.range fun n : ℕ ↦ (U ^ n) x)
  rw [Metric.totallyBounded_iff]
  intro ε hε
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.mp hx (ε / 3) (by linarith)
  change TotallyBounded (Set.range fun n : ℕ ↦ (U ^ n) y) at hy
  obtain ⟨t, htfin, htcover⟩ :=
    (Metric.totallyBounded_iff.mp hy) (ε / 3) (by linarith)
  refine ⟨t, htfin, ?_⟩
  intro v hv
  obtain ⟨n, rfl⟩ := hv
  have hycover := htcover (Set.mem_range_self n)
  simp only [Set.mem_iUnion] at hycover ⊢
  obtain ⟨a, ha, hball⟩ := hycover
  refine ⟨a, ha, ?_⟩
  rw [Metric.mem_ball] at hball ⊢
  calc
    dist ((U ^ n) x) a ≤
        dist ((U ^ n) x) ((U ^ n) y) + dist ((U ^ n) y) a :=
      dist_triangle _ _ _
    _ = dist x y + dist ((U ^ n) y) a := by
      rw [(U ^ n).dist_map]
    _ < ε := by linarith

noncomputable def unitaryAlmostPeriodicSubmodule (U : H ≃ₗᵢ[ℂ] H) :
    Submodule ℂ H where
  carrier := unitaryAlmostPeriodic U
  zero_mem' := totallyBounded_unitaryOrbit_zero U
  add_mem' := fun {x y} hx hy ↦ totallyBounded_unitaryOrbit_add U x y hx hy
  smul_mem' := fun c {x} hx ↦ totallyBounded_unitaryOrbit_smul U c x hx

theorem unitaryEigenSpan_le_almostPeriodic (U : H ≃ₗᵢ[ℂ] H) :
    unitaryEigenSpan U ≤ unitaryAlmostPeriodicSubmodule U := by
  apply Submodule.span_le.mpr
  intro x hx
  obtain ⟨z, hz⟩ := hx
  exact totallyBounded_unitaryOrbit_eigenvector U hz

theorem unitaryKronecker_le_almostPeriodic (U : H ≃ₗᵢ[ℂ] H) :
    (unitaryKronecker U).toSubmodule ≤ unitaryAlmostPeriodicSubmodule U := by
  change (unitaryEigenSpan U).topologicalClosure ≤ unitaryAlmostPeriodicSubmodule U
  exact Submodule.topologicalClosure_minimal _
    (unitaryEigenSpan_le_almostPeriodic U)
    (by
      change IsClosed (unitaryAlmostPeriodic U)
      exact isClosed_unitaryAlmostPeriodic U)

theorem unitaryCompactPart_mem_kronecker (U : H ≃ₗᵢ[ℂ] H) (x : H) :
    unitaryCompactPart U x ∈ unitaryKronecker U := by
  exact ((unitaryKronecker U).toSubmodule.orthogonalProjectionOnto x).property

theorem totallyBounded_unitaryCompactPart_orbit (U : H ≃ₗᵢ[ℂ] H) (x : H) :
    TotallyBounded
      (Set.range fun n : ℕ ↦ (U ^ n) (unitaryCompactPart U x)) :=
  unitaryKronecker_le_almostPeriodic U (unitaryCompactPart_mem_kronecker U x)

open Filter Finset Function Set
open scoped ComplexConjugate Pointwise Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem lower_inner_on_unitary_return (U : H ≃ₗᵢ[ℂ] H) (w : H)
    {n : ℕ} (hn : dist ((U ^ n) w) w < ‖w‖ / 2) :
    ‖w‖ ^ 2 / 2 < ‖inner ℂ w ((U ^ n) w)‖ := by
  have hdiff :
      ‖inner ℂ w ((U ^ n) w) - inner ℂ w w‖ < ‖w‖ ^ 2 / 2 := by
    rw [← inner_sub_right]
    calc
      ‖inner ℂ w ((U ^ n) w - w)‖ ≤ ‖w‖ * ‖(U ^ n) w - w‖ :=
        norm_inner_le_norm _ _
      _ = ‖w‖ * dist ((U ^ n) w) w := by rw [dist_eq_norm]
      _ < ‖w‖ * (‖w‖ / 2) := by
        exact mul_lt_mul_of_pos_left hn (norm_pos_iff.mpr (by
          intro hw
          subst w
          simp at hn))
      _ = ‖w‖ ^ 2 / 2 := by ring
  have htri : ‖inner ℂ w w‖ ≤
      ‖inner ℂ w ((U ^ n) w)‖ +
        ‖inner ℂ w ((U ^ n) w) - inner ℂ w w‖ := by
    simpa [add_comm] using
      (norm_le_norm_add_norm_sub
        (inner ℂ w ((U ^ n) w)) (inner ℂ w w))
  simp only [inner_self_eq_norm_sq_to_K, norm_pow,
    RCLike.norm_ofReal, abs_norm] at htri
  simp only [inner_self_eq_norm_sq_to_K] at hdiff
  nlinarith [sq_nonneg ‖w‖]

theorem unitaryCorrelationAverage_lower_of_syndetic_returns
    (U : H ≃ₗᵢ[ℂ] H) (w : H) (hw : w ≠ 0)
    (S : Set ℕ)
    (hS : S = {n : ℕ | dist ((U ^ n) w) w < ‖w‖ / 2})
    (hSsyn : Erdos109.Syndetic S) :
    ∃ r : ℝ, 0 < r ∧ ∀ᶠ N in atTop,
      r ≤ unitaryCorrelationAverage U w w N := by
  classical
  obtain ⟨d, hd, hden⟩ :=
    Erdos109.positiveLowerDensity_range_of_syndetic hSsyn
      (tendsto_id : Tendsto (fun n : ℕ ↦ n) atTop atTop)
  let c : ℝ := ‖w‖ ^ 2 / 2
  refine ⟨c * d, mul_pos (by positivity) hd, ?_⟩
  filter_upwards [hden] with N hN
  have hsum : c * (((Finset.range N : Set ℕ) ∩ S).ncard : ℝ) ≤
      ∑ n ∈ Finset.range N, ‖inner ℂ w (((unitaryOperator U) ^ n) w)‖ := by
    let T := (Finset.range N).filter (fun n ↦ n ∈ S)
    have hterm : ∀ n ∈ T, c ≤
        ‖inner ℂ w (((unitaryOperator U) ^ n) w)‖ := by
      intro n hn
      have hnS : n ∈ S := (Finset.mem_filter.mp hn).2
      rw [hS] at hnS
      rw [unitaryOperator_pow_apply]
      exact (lower_inner_on_unitary_return U w hnS).le
    have hsub : T ⊆ Finset.range N := fun n hn ↦ (Finset.mem_filter.mp hn).1
    have hTset : (↑T : Set ℕ) = (Finset.range N : Set ℕ) ∩ S := by
      ext n
      simp [T]
    have hraw : ∑ _n ∈ T, c ≤
        ∑ n ∈ Finset.range N, ‖inner ℂ w (((unitaryOperator U) ^ n) w)‖ := by
      calc
        ∑ _n ∈ T, c ≤
            ∑ n ∈ T, ‖inner ℂ w (((unitaryOperator U) ^ n) w)‖ :=
          Finset.sum_le_sum fun n hn ↦ hterm n hn
        _ ≤ ∑ n ∈ Finset.range N,
            ‖inner ℂ w (((unitaryOperator U) ^ n) w)‖ :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun i hi hnot ↦ norm_nonneg _)
    calc
      c * (((Finset.range N : Set ℕ) ∩ S).ncard : ℝ) = ∑ _n ∈ T, c := by
        rw [← hTset, Set.ncard_coe_finset]
        simp only [sum_const, nsmul_eq_mul]
        rw [mul_comm]
      _ ≤ ∑ n ∈ Finset.range N,
          ‖inner ℂ w (((unitaryOperator U) ^ n) w)‖ := hraw
  calc
    c * d ≤ c * Erdos109.finsetDensity (Finset.range N) S :=
      mul_le_mul_of_nonneg_left hN (by positivity)
    _ = (N : ℝ)⁻¹ *
        (c * (((Finset.range N : Set ℕ) ∩ S).ncard : ℝ)) := by
      simp only [Erdos109.finsetDensity, Finset.card_range]
      ring
    _ ≤ (N : ℝ)⁻¹ *
        ∑ n ∈ Finset.range N,
          ‖inner ℂ w (((unitaryOperator U) ^ n) w)‖ :=
      mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr (Nat.cast_nonneg N))
    _ = unitaryCorrelationAverage U w w N := rfl

theorem eq_zero_of_totallyBounded_unitaryOrbit_of_correlationAverage
    (U : H ≃ₗᵢ[ℂ] H) (w : H)
    (horbit : TotallyBounded (Set.range fun n : ℕ ↦ (U ^ n) w))
    (hlim : Tendsto (fun N ↦ unitaryCorrelationAverage U w w N)
      atTop (nhds 0)) : w = 0 := by
  by_contra hw
  have hr : 0 < ‖w‖ / 2 := by positivity
  have hiter (n : ℕ) : (U : H → H)^[n] w = (U ^ n) w := by
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Function.iterate_succ_apply', ih, pow_succ',
          LinearIsometryEquiv.coe_mul]
        rfl
  have horbit' : TotallyBounded (Set.range fun n : ℕ ↦ (U : H → H)^[n] w) := by
    simpa only [hiter] using horbit
  have hSsyn := Erdos109.syndetic_returnTimes_of_totallyBounded
    (U : H → H) U.isometry w horbit' hr
  let S : Set ℕ := {n : ℕ | dist ((U ^ n) w) w < ‖w‖ / 2}
  have hS : S = {n : ℕ | dist ((U ^ n) w) w < ‖w‖ / 2} := rfl
  have hSsyn' : Erdos109.Syndetic S := by
    simpa only [S, hiter] using hSsyn
  obtain ⟨r, hrpos, hravg⟩ :=
    unitaryCorrelationAverage_lower_of_syndetic_returns U w hw S hS hSsyn'
  have hsmall : ∀ᶠ N in atTop, unitaryCorrelationAverage U w w N < r :=
    hlim.eventually (eventually_lt_nhds hrpos)
  obtain ⟨N, hlower, hupper⟩ := (hravg.and hsmall).exists
  exact (not_lt_of_ge hlower) hupper

theorem unitaryAlmostPeriodic_le_kronecker (U : H ≃ₗᵢ[ℂ] H) :
    unitaryAlmostPeriodicSubmodule U ≤ (unitaryKronecker U).toSubmodule := by
  intro y hy
  let w := unitaryWeakPart U y
  have hcompact : TotallyBounded
      (Set.range fun n : ℕ ↦ (U ^ n) (unitaryCompactPart U y)) :=
    totallyBounded_unitaryCompactPart_orbit U y
  have hneg : TotallyBounded
      (Set.range fun n : ℕ ↦ (U ^ n) (-unitaryCompactPart U y)) := by
    simpa only [neg_one_smul] using
      totallyBounded_unitaryOrbit_smul U (-1 : ℂ) (unitaryCompactPart U y) hcompact
  have hworbit : TotallyBounded (Set.range fun n : ℕ ↦ (U ^ n) w) := by
    simpa only [w, unitaryWeakPart, sub_eq_add_neg] using
      totallyBounded_unitaryOrbit_add U y (-unitaryCompactPart U y) hy hneg
  have hwlim : Tendsto
      (fun N ↦ unitaryCorrelationAverage U w w N) atTop (nhds 0) := by
    simpa only [w] using
      tendsto_unitaryWeakPart_correlation_average U y w
  have hwzero : w = 0 :=
    eq_zero_of_totallyBounded_unitaryOrbit_of_correlationAverage
      U w hworbit hwlim
  have hy_eq : y = unitaryCompactPart U y := by
    exact sub_eq_zero.mp hwzero
  rw [hy_eq]
  exact unitaryCompactPart_mem_kronecker U y

theorem unitaryAlmostPeriodic_eq_kronecker (U : H ≃ₗᵢ[ℂ] H) :
    unitaryAlmostPeriodicSubmodule U = (unitaryKronecker U).toSubmodule := by
  apply le_antisymm
  · exact unitaryAlmostPeriodic_le_kronecker U
  · exact unitaryKronecker_le_almostPeriodic U

open CompactlySupported Filter Function Set
open scoped BoundedContinuousFunction ComplexConjugate ENNReal NNReal Pointwise Topology
open MeasureTheory ProbabilityTheory

namespace Erdos109

noncomputable section

noncomputable local instance : MeasurableSpace BetaNat := borel BetaNat
local instance : BorelSpace BetaNat := ⟨rfl⟩

noncomputable def betaPred : BetaNat → BetaNat :=
  Ultrafilter.extend (fun n : ℕ ↦ pure n.pred)

theorem continuous_betaPred : Continuous betaPred :=
  continuous_ultrafilter_extend _

@[simp] theorem betaPred_pure (n : ℕ) : betaPred (pure n) = pure n.pred := by
  simp [betaPred]

theorem betaPred_betaShift (p : BetaNat) : betaPred (betaShift p) = p := by
  apply congrFun ((denseRange_pure : DenseRange (pure : ℕ → BetaNat)).equalizer
    (continuous_betaPred.comp continuous_betaShift) continuous_id ?_) p
  funext n
  simp only [Function.comp_apply, betaShift_pure, betaPred_pure, Nat.pred_succ]
  rfl

theorem betaPred_eq_map (p : BetaNat) :
    betaPred p = p.map Nat.pred := by
  rw [betaPred, ultrafilter_extend_eq_iff]
  rw [show p.map (fun n : ℕ ↦ pure n.pred) =
      (p.map Nat.pred).map pure by
    rw [Ultrafilter.map_map]
    rfl]
  exact ultrafilter_converges_iff.mpr (bind_pure (p.map Nat.pred)).symm

theorem betaShift_eq_map (p : BetaNat) :
    betaShift p = p.map Nat.succ := by
  apply Ultrafilter.coe_injective
  ext s
  change (∀ᶠ x in p, ∀ᶠ y in pure 1, x + y ∈ s) ↔
    {x | Nat.succ x ∈ s} ∈ (p : Filter ℕ)
  simp only [Filter.eventually_pure]
  rfl

theorem betaShift_betaPred_of_ne (p : BetaNat) (hp : p ≠ pure 0) :
    betaShift (betaPred p) = p := by
  have hzero : ({0} : Set ℕ) ∉ (p : Filter ℕ) := by
    intro h
    apply hp
    exact Ultrafilter.coe_injective (p.neBot'.eq_pure_iff.mpr h)
  have hevent : (fun n : ℕ ↦ Nat.succ n.pred) =ᶠ[p] id := by
    have hcompl : ({0} : Set ℕ)ᶜ ∈ (p : Filter ℕ) :=
      (Ultrafilter.compl_mem_iff_notMem (f := p)).mpr hzero
    filter_upwards [hcompl] with n hn
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hn
    change Nat.succ n.pred = n
    exact Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero hn)
  rw [betaShift_eq_map, betaPred_eq_map, Ultrafilter.map_map]
  apply Ultrafilter.coe_injective
  exact (Filter.map_congr hevent).trans Filter.map_id

theorem betaShift_ne_pure_zero (p : BetaNat) : betaShift p ≠ pure 0 := by
  intro hp
  have hp0 : p = pure 0 := by
    calc
      p = betaPred (betaShift p) := (betaPred_betaShift p).symm
      _ = betaPred (pure 0) := congrArg betaPred hp
      _ = pure 0 := by simp
  subst p
  have h10 : pure 1 = (pure 0 : BetaNat) := by
    simpa only [betaShift_pure, zero_add] using hp
  exact Nat.one_ne_zero (Ultrafilter.pure_injective h10)

theorem betaShift_preimage_pure_zero :
    betaShift ⁻¹' ({pure 0} : Set BetaNat) = ∅ := by
  ext p
  simp [betaShift_ne_pure_zero]

theorem measure_pure_zero_eq_zero {μ : Measure BetaNat}
    (hμ : MeasurePreserving betaShift μ μ) :
    μ ({pure 0} : Set BetaNat) = 0 := by
  have hmap := congrArg (fun ν : Measure BetaNat ↦ ν ({pure 0} : Set BetaNat)) hμ.map_eq
  rw [Measure.map_apply (μ := μ) continuous_betaShift.measurable
      (measurableSet_singleton (pure 0 : BetaNat)),
    betaShift_preimage_pure_zero, measure_empty] at hmap
  exact hmap.symm

theorem betaShift_betaPred_ae {μ : Measure BetaNat}
    (hμ : MeasurePreserving betaShift μ μ) :
    betaShift ∘ betaPred =ᵐ[μ] id := by
  have hne : ∀ᵐ p ∂μ, p ≠ pure 0 := by
    simpa only [Set.mem_singleton_iff] using
      (measure_eq_zero_iff_ae_notMem.mp (measure_pure_zero_eq_zero hμ))
  filter_upwards [hne] with p hp
  exact betaShift_betaPred_of_ne p hp

theorem measurePreserving_betaPred {μ : Measure BetaNat}
    (hμ : MeasurePreserving betaShift μ μ) :
    MeasurePreserving betaPred μ μ := by
  refine ⟨continuous_betaPred.measurable, ?_⟩
  calc
    Measure.map betaPred μ = Measure.map betaPred (Measure.map betaShift μ) := by
      rw [hμ.map_eq]
    _ = Measure.map (betaPred ∘ betaShift) μ := by
      rw [Measure.map_map]
      · exact continuous_betaPred.measurable
      · exact continuous_betaShift.measurable
    _ = μ := by
      rw [show betaPred ∘ betaShift = id by
        funext p
        exact betaPred_betaShift p]
      exact Measure.map_id

abbrev BetaL2 (μ : Measure BetaNat) := Lp ℂ 2 μ

noncomputable def betaKoopmanForward {μ : Measure BetaNat}
    (hμ : MeasurePreserving betaShift μ μ) :
    BetaL2 μ →ₗᵢ[ℂ] BetaL2 μ :=
  Lp.compMeasurePreservingₗᵢ ℂ betaShift hμ

noncomputable def betaKoopmanBackward {μ : Measure BetaNat}
    (hμ : MeasurePreserving betaShift μ μ) :
    BetaL2 μ →ₗᵢ[ℂ] BetaL2 μ :=
  Lp.compMeasurePreservingₗᵢ ℂ betaPred (measurePreserving_betaPred hμ)

theorem betaKoopmanForward_backward_apply {μ : Measure BetaNat}
    (hμ : MeasurePreserving betaShift μ μ) (g : BetaL2 μ) :
    betaKoopmanForward hμ (betaKoopmanBackward hμ g) = g := by
  let hp := measurePreserving_betaPred hμ
  change Lp.compMeasurePreserving betaShift hμ
      (Lp.compMeasurePreserving betaPred hp g) = g
  rw [← Lp.compMeasurePreserving_comp_apply g hp hμ]
  apply Lp.ext
  have hcoe := Lp.coeFn_compMeasurePreserving g (hp.comp hμ)
  filter_upwards [hcoe] with p hcoe
  rw [hcoe]
  simp only [Function.comp_apply]
  rw [betaPred_betaShift]

theorem betaKoopmanBackward_forward_apply {μ : Measure BetaNat}
    (hμ : MeasurePreserving betaShift μ μ) (g : BetaL2 μ) :
    betaKoopmanBackward hμ (betaKoopmanForward hμ g) = g := by
  let hp := measurePreserving_betaPred hμ
  change Lp.compMeasurePreserving betaPred hp
      (Lp.compMeasurePreserving betaShift hμ g) = g
  rw [← Lp.compMeasurePreserving_comp_apply g hμ hp]
  apply Lp.ext
  have hcoe := Lp.coeFn_compMeasurePreserving g (hμ.comp hp)
  filter_upwards [hcoe, betaShift_betaPred_ae hμ] with p hcoe hinv
  rw [hcoe]
  simp only [Function.comp_apply]
  exact congrArg (fun q ↦ (g : BetaNat → ℂ) q) hinv

noncomputable def betaKoopman {μ : Measure BetaNat}
    (hμ : MeasurePreserving betaShift μ μ) :
    BetaL2 μ ≃ₗᵢ[ℂ] BetaL2 μ :=
  LinearIsometryEquiv.ofLinearIsometry
    (betaKoopmanForward hμ)
    (betaKoopmanBackward hμ).toLinearMap
    (by
      apply LinearMap.ext
      exact betaKoopmanForward_backward_apply hμ)
    (by
      apply LinearMap.ext
      exact betaKoopmanBackward_forward_apply hμ)

@[simp] theorem betaKoopman_apply {μ : Measure BetaNat}
    (hμ : MeasurePreserving betaShift μ μ) (g : BetaL2 μ) :
    betaKoopman hμ g = Lp.compMeasurePreserving betaShift hμ g := rfl

noncomputable def betaIndicatorComplex (A : Set ℕ) : C(BetaNat, ℂ) :=
  ⟨fun p ↦ (betaIndicator A p : ℂ),
    Complex.continuous_ofReal.comp (betaIndicator A).continuous⟩

@[simp] theorem betaIndicatorComplex_apply (A : Set ℕ) (p : BetaNat) :
    betaIndicatorComplex A p = (betaIndicator A p : ℂ) := rfl

noncomputable def betaIndicatorL2 (μ : Measure BetaNat) [IsFiniteMeasure μ]
    (A : Set ℕ) : BetaL2 μ :=
  ContinuousMap.toLp 2 μ ℂ (betaIndicatorComplex A)

theorem betaKoopman_indicator {μ : Measure BetaNat} [IsFiniteMeasure μ]
    (hμ : MeasurePreserving betaShift μ μ) (A : Set ℕ) :
    betaKoopman hμ (betaIndicatorL2 μ A) = betaIndicatorL2 μ (shift A 1) := by
  change Lp.compMeasurePreserving betaShift hμ (betaIndicatorL2 μ A) = _
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving (betaIndicatorL2 μ A) hμ,
    hμ.quasiMeasurePreserving.ae_eq_comp
      (ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) μ (betaIndicatorComplex A)),
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) μ
      (betaIndicatorComplex (shift A 1))] with
      p hcomp hAcomp hshift
  rw [hcomp]
  change
    (((ContinuousMap.toLp 2 μ ℂ (betaIndicatorComplex A) : BetaL2 μ) :
        BetaNat → ℂ) ∘ betaShift) p =
      ((ContinuousMap.toLp 2 μ ℂ (betaIndicatorComplex (shift A 1)) :
        BetaL2 μ) : BetaNat → ℂ) p
  rw [hAcomp, hshift]
  change (betaIndicator A (betaShift p) : ℂ) =
    (betaIndicator (shift A 1) p : ℂ)
  exact congrArg (fun r : ℝ ↦ (r : ℂ))
    (congrArg (fun f : C(BetaNat, ℝ) ↦ f p) (betaIndicator_shift A 1)).symm

theorem betaKoopman_pow_indicator {μ : Measure BetaNat} [IsFiniteMeasure μ]
    (hμ : MeasurePreserving betaShift μ μ) (A : Set ℕ) (n : ℕ) :
    (betaKoopman hμ ^ n) (betaIndicatorL2 μ A) =
      betaIndicatorL2 μ (shift A n) := by
  induction n with
  | zero => simp
  | succ n hn =>
      rw [pow_succ']
      change betaKoopman hμ ((betaKoopman hμ ^ n) (betaIndicatorL2 μ A)) = _
      rw [hn, betaKoopman_indicator hμ, shift_add]

theorem inner_betaIndicatorL2_koopman_pow {μ : Measure BetaNat}
    [IsFiniteMeasure μ] (hμ : MeasurePreserving betaShift μ μ)
    (A D : Set ℕ) (m : ℕ) :
    inner ℂ (betaIndicatorL2 μ D)
        ((betaKoopman hμ ^ m) (betaIndicatorL2 μ A)) =
      ((∫ x, betaIndicator (shift A m) x * betaIndicator D x ∂μ : ℝ) : ℂ) := by
  rw [betaKoopman_pow_indicator hμ]
  change inner ℂ (ContinuousMap.toLp 2 μ ℂ (betaIndicatorComplex D))
      (ContinuousMap.toLp 2 μ ℂ (betaIndicatorComplex (shift A m))) = _
  rw [ContinuousMap.inner_toLp]
  calc
    (∫ x, betaIndicatorComplex (shift A m) x *
        conj (betaIndicatorComplex D x) ∂μ) =
        ∫ x, ((betaIndicator (shift A m) x * betaIndicator D x : ℝ) : ℂ) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp [betaIndicatorComplex]
    _ = ((∫ x, betaIndicator (shift A m) x * betaIndicator D x ∂μ : ℝ) : ℂ) :=
      integral_ofReal

theorem tendsto_finsetDensity_ultraShift_correlation
    (N : ℕ → ℕ) (hNpos : ∀ k, 0 < N k) (q : Ultrafilter ℕ)
    (μ : ProbabilityMeasure BetaNat)
    (hμtend : Tendsto (fun k ↦ betaEmpirical (N k) (hNpos k))
      (q : Filter ℕ) (𝓝 μ)) (A : Set ℕ) (p : Ultrafilter ℕ) (m : ℕ) :
    Tendsto
      (fun k ↦ finsetDensity (Finset.range (N k))
        (ultraShift A p ∩ shift A m))
      (q : Filter ℕ)
      (𝓝 (∫ x, betaIndicator (shift A m) x *
        betaIndicator (ultraShift A p) x ∂(μ : Measure BetaNat))) := by
  let f : C(BetaNat, ℝ) :=
    betaIndicator (shift A m) * betaIndicator (ultraShift A p)
  have ht :=
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hμtend)
      (BoundedContinuousFunction.mkOfCompact f)
  convert ht using 1
  · funext k
    simpa [f] using
      (integral_betaEmpirical_indicator_correlation (N k) (hNpos k) A p m).symm
  · rfl

end

end Erdos109

open Filter MeasureTheory Set
open scoped BoundedContinuousFunction ENNReal ProbabilityTheory Topology

variable {α : Type*} [MeasurableSpace α]

open Erdos109

local instance : MeasurableSpace (Ultrafilter ℕ) := borel (Ultrafilter ℕ)
local instance : BorelSpace (Ultrafilter ℕ) := ⟨rfl⟩

noncomputable def betaExtendBounded (f : ℕ → ℝ) (C : ℝ)
    (hf : ∀ n, |f n| ≤ C) : C(BetaNat, ℝ) := by
  let fs : ℕ → Set.Icc (-C) C := fun n ↦
    ⟨f n, (abs_le.mp (hf n)).1, (abs_le.mp (hf n)).2⟩
  letI : CompactSpace (Set.Icc (-C) C) :=
    isCompact_iff_compactSpace.mp isCompact_Icc
  exact ⟨fun p ↦ (Ultrafilter.extend fs p : Set.Icc (-C) C),
    continuous_subtype_val.comp (continuous_ultrafilter_extend fs)⟩

@[simp] theorem betaExtendBounded_pure (f : ℕ → ℝ) (C : ℝ)
    (hf : ∀ n, |f n| ≤ C) (n : ℕ) :
    betaExtendBounded f C hf (pure n) = f n := by
  simp [betaExtendBounded]

theorem abs_betaExtendBounded_le (f : ℕ → ℝ) (C : ℝ)
    (hf : ∀ n, |f n| ≤ C) (p : BetaNat) :
    |betaExtendBounded f C hf p| ≤ C := by
  let fs : ℕ → Set.Icc (-C) C := fun n ↦
    ⟨f n, (abs_le.mp (hf n)).1, (abs_le.mp (hf n)).2⟩
  let : CompactSpace (Set.Icc (-C) C) :=
    isCompact_iff_compactSpace.mp isCompact_Icc
  change |(Ultrafilter.extend fs p : Set.Icc (-C) C).1| ≤ C
  exact abs_le.mpr (Ultrafilter.extend fs p).2

noncomputable def betaRightTranslate (f : ℕ → ℝ) (C : ℝ)
    (hf : ∀ n, |f n| ≤ C) (n : ℕ) : C(BetaNat, ℝ) :=
  betaExtendBounded (fun m ↦ f (n + m)) C (fun m ↦ hf (n + m))

@[simp] theorem betaRightTranslate_pure (f : ℕ → ℝ) (C : ℝ)
    (hf : ∀ n, |f n| ≤ C) (n m : ℕ) :
    betaRightTranslate f C hf n (pure m) = f (n + m) := by
  simp [betaRightTranslate]

theorem abs_betaRightTranslate_le (f : ℕ → ℝ) (C : ℝ)
    (hf : ∀ n, |f n| ≤ C) (n : ℕ) (p : BetaNat) :
    |betaRightTranslate f C hf n p| ≤ C := by
  exact abs_betaExtendBounded_le (fun m ↦ f (n + m)) C (fun m ↦ hf (n + m)) p

theorem integral_betaEmpirical_indicator_rightTranslate
    (N : ℕ) (hN : 0 < N) (B : Set ℕ)
    (f : ℕ → ℝ) (C : ℝ) (hf : ∀ n, |f n| ≤ C) (n : ℕ) :
    ∫ p, betaIndicator B p * betaRightTranslate f C hf n p
        ∂((betaEmpirical N hN : ProbabilityMeasure BetaNat) : Measure BetaNat) =
      realFinsetMean (Finset.range N)
        (fun m ↦ realIndicator B m * f (n + m)) := by
  let g : C(BetaNat, ℝ) := betaIndicator B * betaRightTranslate f C hf n
  rw [show (∫ p, betaIndicator B p * betaRightTranslate f C hf n p
      ∂((betaEmpirical N hN : ProbabilityMeasure BetaNat) : Measure BetaNat)) =
      ∫ p, g p ∂((betaEmpirical N hN : ProbabilityMeasure BetaNat) : Measure BetaNat) by rfl]
  rw [integral_betaEmpirical N hN g]
  simp only [g, ContinuousMap.mul_apply, betaIndicator_pure,
    betaRightTranslate_pure, natIndicator_eq_realIndicator]
  simp [realFinsetMean]

theorem integral_betaEmpirical_indicator (N : ℕ) (hN : 0 < N) (B : Set ℕ) :
    ∫ p, betaIndicator B p
        ∂((betaEmpirical N hN : ProbabilityMeasure BetaNat) : Measure BetaNat) =
      finsetDensity (Finset.range N) B := by
  rw [integral_betaEmpirical N hN (betaIndicator B)]
  simp_rw [betaIndicator_pure, natIndicator_eq_realIndicator]
  rw [← realFinsetMean_indicator]
  simp [realFinsetMean]

def betaEvent (B : Set ℕ) : Set BetaNat :=
  betaMembership B ⁻¹' {true}

theorem betaEvent_isClopen (B : Set ℕ) : IsClopen (betaEvent B) := by
  exact (isClopen_discrete {true}).preimage (betaMembership B).continuous

@[simp] theorem pure_mem_betaEvent_iff (B : Set ℕ) (n : ℕ) :
    pure n ∈ betaEvent B ↔ n ∈ B := by
  classical
  simp [betaEvent, betaMembership]

theorem betaIndicator_eq_indicator_betaEvent (B : Set ℕ) :
    (fun p ↦ betaIndicator B p) = (betaEvent B).indicator (fun _ ↦ (1 : ℝ)) := by
  funext p
  by_cases hp : betaMembership B p = true
  · simp [betaIndicator, betaEvent, hp]
  · simp [betaIndicator, betaEvent, hp]

noncomputable def betaCrossAverage (N : ℕ) (h f : ℕ → ℝ)
    (C : ℝ) (hf : ∀ n, |f n| ≤ C) : C(BetaNat, ℝ) :=
  (N : ℝ)⁻¹ •
    ∑ n ∈ Finset.range N, (h n) • betaRightTranslate f C hf n

theorem betaCrossAverage_apply (N : ℕ) (h f : ℕ → ℝ)
    (C : ℝ) (hf : ∀ n, |f n| ≤ C) (p : BetaNat) :
    betaCrossAverage N h f C hf p =
      realFinsetMean (Finset.range N)
        (fun n ↦ h n * betaRightTranslate f C hf n p) := by
  simp [betaCrossAverage, realFinsetMean, div_eq_mul_inv,
    Finset.sum_apply, smul_eq_mul]
  ring

theorem abs_betaCrossAverage_le (N : ℕ) (hN : 0 < N)
    (h f : ℕ → ℝ) (H C : ℝ) (hH : ∀ n, |h n| ≤ H)
    (hf : ∀ n, |f n| ≤ C) (p : BetaNat) :
    |betaCrossAverage N h f C hf p| ≤ H * C := by
  rw [betaCrossAverage_apply, realFinsetMean, abs_div]
  have hden : (0 : ℝ) < N := by exact_mod_cast hN
  have hHnonneg : 0 ≤ H := (abs_nonneg (h 0)).trans (hH 0)
  rw [Finset.card_range, abs_of_pos hden]
  apply (div_le_iff₀ hden).2
  calc
    |∑ n ∈ Finset.range N, h n * betaRightTranslate f C hf n p| ≤
        ∑ n ∈ Finset.range N, |h n * betaRightTranslate f C hf n p| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _n ∈ Finset.range N, H * C := by
      apply Finset.sum_le_sum
      intro n hn
      rw [abs_mul]
      exact mul_le_mul (hH n) (abs_betaRightTranslate_le f C hf n p)
        (abs_nonneg _) hHnonneg
    _ = (N : ℝ) * (H * C) := by simp
    _ = H * C * (N : ℝ) := by ring

theorem integral_betaIndicator_mul_betaRightTranslate_eq_zero
    (N : ℕ → ℕ) (hNpos : ∀ k, 0 < N k)
    (q : Ultrafilter ℕ) (hq : (q : Filter ℕ) ≤ atTop)
    (μ : ProbabilityMeasure BetaNat)
    (hμ : Tendsto (fun k ↦ betaEmpirical (N k) (hNpos k))
      (q : Filter ℕ) (𝓝 μ))
    (B : Set ℕ) (f : ℕ → ℝ) (C : ℝ) (hf : ∀ n, |f n| ≤ C)
    (hanti : ∀ n, Tendsto
      (fun k ↦ realFinsetMean (Finset.range (N k))
        (fun m ↦ realIndicator B m * f (n + m))) atTop (𝓝 0))
    (n : ℕ) :
    ∫ p, betaIndicator B p * betaRightTranslate f C hf n p
        ∂(μ : Measure BetaNat) = 0 := by
  let g : C(BetaNat, ℝ) := betaIndicator B * betaRightTranslate f C hf n
  let gb : BetaNat →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact g
  have hμg := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hμ) gb
  have hantig : Tendsto
      (fun k ↦ ∫ p, betaIndicator B p * betaRightTranslate f C hf n p
        ∂((betaEmpirical (N k) (hNpos k) : ProbabilityMeasure BetaNat) : Measure BetaNat))
      (q : Filter ℕ) (𝓝 0) := by
    have ht := (hanti n).mono_left hq
    exact ht.congr' (Eventually.of_forall fun k ↦
      (integral_betaEmpirical_indicator_rightTranslate
        (N k) (hNpos k) B f C hf n).symm)
  apply tendsto_nhds_unique hμg hantig

theorem integral_betaIndicator_mul_betaCrossAverage_eq_zero
    (Nseq : ℕ → ℕ) (hNpos : ∀ k, 0 < Nseq k)
    (q : Ultrafilter ℕ) (hq : (q : Filter ℕ) ≤ atTop)
    (μ : ProbabilityMeasure BetaNat)
    (hμ : Tendsto (fun k ↦ betaEmpirical (Nseq k) (hNpos k))
      (q : Filter ℕ) (𝓝 μ))
    (B : Set ℕ) (f h : ℕ → ℝ) (C : ℝ) (hf : ∀ n, |f n| ≤ C)
    (hanti : ∀ n, Tendsto
      (fun k ↦ realFinsetMean (Finset.range (Nseq k))
        (fun m ↦ realIndicator B m * f (n + m))) atTop (𝓝 0))
    (K : ℕ) :
    ∫ p, betaIndicator B p * betaCrossAverage (Nseq K) h f C hf p
        ∂(μ : Measure BetaNat) = 0 := by
  let lhs : C(BetaNat, ℝ) :=
    betaIndicator B * betaCrossAverage (Nseq K) h f C hf
  let rhs : C(BetaNat, ℝ) :=
    (Nseq K : ℝ)⁻¹ •
      ∑ n ∈ Finset.range (Nseq K),
        (h n) • (betaIndicator B * betaRightTranslate f C hf n)
  have hlr : lhs = rhs := by
    ext p
    simp [lhs, rhs, betaCrossAverage, Finset.sum_apply, smul_eq_mul]
    field_simp [Nat.ne_of_gt (hNpos K)]
    left
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    ring
  change betaIntegralFunctional (μ : Measure BetaNat) lhs = 0
  rw [hlr]
  dsimp only [rhs]
  rw [map_smul, map_sum]
  simp_rw [map_smul, betaIntegralFunctional_apply]
  simp_rw [ContinuousMap.mul_apply]
  simp_rw [integral_betaIndicator_mul_betaRightTranslate_eq_zero
    Nseq hNpos q hq μ hμ B f C hf hanti]
  simp

theorem betaEvent_measure_ne_zero_of_lower_density
    (N : ℕ → ℕ) (hNpos : ∀ k, 0 < N k)
    (q : Ultrafilter ℕ) (hq : (q : Filter ℕ) ≤ atTop)
    (μ : ProbabilityMeasure BetaNat)
    (hμ : Tendsto (fun k ↦ betaEmpirical (N k) (hNpos k))
      (q : Filter ℕ) (𝓝 μ))
    (B : Set ℕ) (d : ℝ) (hd : 0 < d)
    (hBd : ∀ᶠ k in atTop, d ≤ finsetDensity (Finset.range (N k)) B) :
    (μ : Measure BetaNat) (betaEvent B) ≠ 0 := by
  let b : BetaNat →ᵇ ℝ :=
    BoundedContinuousFunction.mkOfCompact (betaIndicator B)
  have hμb := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hμ) b
  have hfinite : ∀ k,
      (∫ p, b p
        ∂((betaEmpirical (N k) (hNpos k) : ProbabilityMeasure BetaNat) : Measure BetaNat)) =
        finsetDensity (Finset.range (N k)) B := by
    intro k
    exact integral_betaEmpirical_indicator (N k) (hNpos k) B
  have hμlower : d ≤ ∫ p, b p ∂(μ : Measure BetaNat) := by
    apply ge_of_tendsto hμb
    filter_upwards [hq hBd] with k hk
    simpa only [hfinite] using hk
  have hevent : (∫ p, b p ∂(μ : Measure BetaNat)) =
      (μ : Measure BetaNat).real (betaEvent B) := by
    change (∫ p, betaIndicator B p ∂(μ : Measure BetaNat)) = _
    rw [betaIndicator_eq_indicator_betaEvent B,
      integral_indicator_const (1 : ℝ) (betaEvent_isClopen B).2.measurableSet]
    simp
  rw [hevent] at hμlower
  have hrealpos : 0 < (μ : Measure BetaNat).real (betaEvent B) :=
    hd.trans_le hμlower
  rw [Measure.real, ENNReal.toReal_pos_iff] at hrealpos
  exact hrealpos.1.ne'

/-- A first-moment consequence of reverse Fatou for uniformly `[0,1]`-valued
functions.  This is the measure-theoretic core of the selection argument in
MRR, Theorem 4.11. -/
theorem exists_le_limsup_of_tendsto_lintegral
    (μ : Measure α) [IsProbabilityMeasure μ]
    (F : ℕ → α → ℝ≥0∞) (r : ℝ≥0∞)
    (hFmeas : ∀ n, Measurable (F n))
    (hFle : ∀ n x, F n x ≤ 1)
    (hlim : Tendsto (fun n ↦ ∫⁻ x, F n x ∂μ) atTop (𝓝 r)) :
    ∃ x, r ≤ limsup (fun n ↦ F n x) atTop := by
  have hlimsup_le_one : ∀ x, limsup (fun n ↦ F n x) atTop ≤ 1 := by
    intro x
    exact limsup_le_of_le (by isBoundedDefault)
      (Eventually.of_forall fun n ↦ hFle n x)
  have hint_le_one : (∫⁻ x, limsup (fun n ↦ F n x) atTop ∂μ) ≤ 1 := by
    calc
      (∫⁻ x, limsup (fun n ↦ F n x) atTop ∂μ) ≤ ∫⁻ _x, (1 : ℝ≥0∞) ∂μ :=
        lintegral_mono fun x ↦ hlimsup_le_one x
      _ = 1 := by simp
  obtain ⟨x, hx⟩ := exists_lintegral_le
    (ne_top_of_le_ne_top ENNReal.one_ne_top hint_le_one)
  refine ⟨x, ?_⟩
  calc
    r = limsup (fun n ↦ ∫⁻ x, F n x ∂μ) atTop := hlim.limsup_eq.symm
    _ ≤ ∫⁻ x, limsup (fun n ↦ F n x) atTop ∂μ :=
      limsup_lintegral_le 1 hFmeas
        (fun n ↦ ae_of_all _ fun x ↦ hFle n x) (by simp)
    _ ≤ limsup (fun n ↦ F n x) atTop := hx

/-- The same first-moment argument while avoiding any prescribed null set. -/
theorem exists_notMem_null_le_limsup_of_tendsto_lintegral
    (μ : Measure α) [IsProbabilityMeasure μ]
    (F : ℕ → α → ℝ≥0∞) (r : ℝ≥0∞)
    (hFmeas : ∀ n, Measurable (F n))
    (hFle : ∀ n x, F n x ≤ 1)
    (hlim : Tendsto (fun n ↦ ∫⁻ x, F n x ∂μ) atTop (𝓝 r))
    (Z : Set α) (hZ : μ Z = 0) :
    ∃ x ∉ Z, r ≤ limsup (fun n ↦ F n x) atTop := by
  have hlimsup_le_one : ∀ x, limsup (fun n ↦ F n x) atTop ≤ 1 := by
    intro x
    exact limsup_le_of_le (by isBoundedDefault)
      (Eventually.of_forall fun n ↦ hFle n x)
  have hint_le_one : (∫⁻ x, limsup (fun n ↦ F n x) atTop ∂μ) ≤ 1 := by
    calc
      (∫⁻ x, limsup (fun n ↦ F n x) atTop ∂μ) ≤ ∫⁻ _x, (1 : ℝ≥0∞) ∂μ :=
        lintegral_mono fun x ↦ hlimsup_le_one x
      _ = 1 := by simp
  obtain ⟨x, hxZ, hx⟩ := exists_notMem_null_lintegral_le
    (ne_top_of_le_ne_top ENNReal.one_ne_top hint_le_one) hZ
  refine ⟨x, hxZ, ?_⟩
  calc
    r = limsup (fun n ↦ ∫⁻ x, F n x ∂μ) atTop := hlim.limsup_eq.symm
    _ ≤ ∫⁻ x, limsup (fun n ↦ F n x) atTop ∂μ :=
      limsup_lintegral_le 1 hFmeas
        (fun n ↦ ae_of_all _ fun x ↦ hFle n x) (by simp)
    _ ≤ limsup (fun n ↦ F n x) atTop := hx

/-- Reverse Fatou in the signed, uniformly bounded form needed by the MRR
ultrafilter selection argument. -/
theorem exists_nonneg_limsup_of_tendsto_integral_zero
    (μ : Measure α) [IsProbabilityMeasure μ]
    (F : ℕ → α → ℝ) (C : ℝ) (hC : 0 < C)
    (hFmeas : ∀ n, Measurable (F n))
    (hFlower : ∀ n x, -C ≤ F n x)
    (hFupper : ∀ n x, F n x ≤ C)
    (hlim : Tendsto (fun n ↦ ∫ x, F n x ∂μ) atTop (𝓝 0)) :
    ∃ x, 0 ≤ limsup (fun n ↦ F n x) atTop := by
  let G : ℕ → α → ℝ := fun n x ↦ (F n x + C) / (2 * C)
  let Ge : ℕ → α → ℝ≥0∞ := fun n x ↦ ENNReal.ofReal (G n x)
  have hGmeas (n : ℕ) : Measurable (G n) := by
    dsimp [G]
    fun_prop
  have hGeMeas (n : ℕ) : Measurable (Ge n) :=
    (hGmeas n).ennreal_ofReal
  have hGnonneg (n : ℕ) (x : α) : 0 ≤ G n x := by
    dsimp [G]
    exact div_nonneg (by linarith [hFlower n x]) (by positivity)
  have hGle (n : ℕ) (x : α) : G n x ≤ 1 := by
    dsimp [G]
    apply (div_le_one (by positivity)).2
    linarith [hFupper n x]
  have hGint (n : ℕ) : Integrable (G n) μ := by
    refine ⟨(hGmeas n).aestronglyMeasurable,
      HasFiniteIntegral.of_bounded (C := 1) ?_⟩
    exact ae_of_all _ fun x ↦ (abs_le.mpr ⟨by linarith [hGnonneg n x], hGle n x⟩)
  have hG_integral (n : ℕ) :
      (∫ x, G n x ∂μ) = ((∫ x, F n x ∂μ) + C) / (2 * C) := by
    simp only [G]
    rw [integral_div, integral_add (by
      refine ⟨(hFmeas n).aestronglyMeasurable,
        HasFiniteIntegral.of_bounded (C := C) ?_⟩
      exact ae_of_all _ fun x ↦ abs_le.mpr ⟨hFlower n x, hFupper n x⟩)
      (integrable_const C)]
    simp
  have hGlim : Tendsto (fun n ↦ ∫ x, G n x ∂μ) atTop (𝓝 (1 / 2 : ℝ)) := by
    have hmap : ContinuousAt (fun t : ℝ ↦ (t + C) / (2 * C)) 0 := by
      fun_prop
    have ht := hmap.tendsto.comp hlim
    rw [show (0 + C) / (2 * C) = (1 / 2 : ℝ) by
      rw [zero_add]
      field_simp] at ht
    exact ht.congr' (Eventually.of_forall fun n ↦ (hG_integral n).symm)
  have hGe_integral (n : ℕ) :
      (∫⁻ x, Ge n x ∂μ) = ENNReal.ofReal (∫ x, G n x ∂μ) := by
    symm
    exact ofReal_integral_eq_lintegral_ofReal (hGint n)
      (ae_of_all _ fun x ↦ hGnonneg n x)
  have hGelim : Tendsto (fun n ↦ ∫⁻ x, Ge n x ∂μ) atTop
      (𝓝 (ENNReal.ofReal (1 / 2 : ℝ))) := by
    have hoflim := (ENNReal.continuous_ofReal.tendsto (1 / 2 : ℝ)).comp hGlim
    exact hoflim.congr' (Eventually.of_forall fun n ↦ (hGe_integral n).symm)
  have hGele (n : ℕ) (x : α) : Ge n x ≤ 1 := by
    exact ENNReal.ofReal_le_one.mpr (hGle n x)
  obtain ⟨x, hx⟩ := exists_le_limsup_of_tendsto_lintegral
    μ Ge (ENNReal.ofReal (1 / 2 : ℝ)) hGeMeas hGele hGelim
  refine ⟨x, ?_⟩
  have hFbddAbove : IsBoundedUnder (· ≤ ·) atTop (fun n ↦ F n x) :=
    isBoundedUnder_of_eventually_le (a := C)
      (Eventually.of_forall fun n ↦ hFupper n x)
  have hFcobdd : IsCoboundedUnder (· ≤ ·) atTop (fun n ↦ F n x) :=
    IsCoboundedUnder.of_frequently_ge (a := -C)
      (Frequently.of_forall fun n ↦ hFlower n x)
  let phi : ℝ → ℝ := fun t ↦ (t + C) / (2 * C)
  have hphiMono : Monotone phi := by
    intro a b hab
    dsimp [phi]
    apply div_le_div_of_nonneg_right _ (by positivity)
    linarith
  have hphiCont : Continuous phi := by fun_prop
  have hlimsupG :
      limsup (fun n ↦ G n x) atTop = phi (limsup (fun n ↦ F n x) atTop) := by
    symm
    simpa only [G, phi, Function.comp_def] using
      hphiMono.map_limsup_of_continuousAt (fun n ↦ F n x)
        hphiCont.continuousAt hFbddAbove hFcobdd
  have hGbounded : IsBoundedUnder (· ≤ ·) atTop (fun n ↦ G n x) :=
    isBoundedUnder_of_eventually_le (a := 1)
      (Eventually.of_forall fun n ↦ hGle n x)
  have hGcobdd : IsCoboundedUnder (· ≤ ·) atTop (fun n ↦ G n x) :=
    IsCoboundedUnder.of_frequently_ge (a := 0)
      (Frequently.of_forall fun n ↦ hGnonneg n x)
  have hofReal : ENNReal.ofReal (limsup (fun n ↦ G n x) atTop) =
      limsup (fun n ↦ Ge n x) atTop := by
    simpa only [Ge] using ENNReal.ofReal_limsup hGcobdd hGbounded
  have hlimsupGnonneg : 0 ≤ limsup (fun n ↦ G n x) atTop :=
    le_limsup_of_frequently_le
      (Frequently.of_forall fun n ↦ hGnonneg n x) hGbounded
  have hxReal : (1 / 2 : ℝ) ≤ limsup (fun n ↦ G n x) atTop := by
    rw [← hofReal] at hx
    exact (ENNReal.ofReal_le_ofReal_iff hlimsupGnonneg).mp hx
  rw [hlimsupG] at hxReal
  dsimp [phi] at hxReal
  rw [le_div_iff₀ (by positivity : 0 < 2 * C)] at hxReal
  linarith

/-- Signed reverse Fatou with a null exceptional set. -/
theorem exists_notMem_null_nonneg_limsup_of_tendsto_integral_zero
    (μ : Measure α) [IsProbabilityMeasure μ]
    (F : ℕ → α → ℝ) (C : ℝ) (hC : 0 < C)
    (hFmeas : ∀ n, Measurable (F n))
    (hFlower : ∀ n x, -C ≤ F n x)
    (hFupper : ∀ n x, F n x ≤ C)
    (hlim : Tendsto (fun n ↦ ∫ x, F n x ∂μ) atTop (𝓝 0))
    (Z : Set α) (hZ : μ Z = 0) :
    ∃ x ∉ Z, 0 ≤ limsup (fun n ↦ F n x) atTop := by
  let G : ℕ → α → ℝ := fun n x ↦ (F n x + C) / (2 * C)
  let Ge : ℕ → α → ℝ≥0∞ := fun n x ↦ ENNReal.ofReal (G n x)
  have hGmeas (n : ℕ) : Measurable (G n) := by
    dsimp [G]
    fun_prop
  have hGeMeas (n : ℕ) : Measurable (Ge n) := (hGmeas n).ennreal_ofReal
  have hGnonneg (n : ℕ) (x : α) : 0 ≤ G n x := by
    dsimp [G]
    exact div_nonneg (by linarith [hFlower n x]) (by positivity)
  have hGle (n : ℕ) (x : α) : G n x ≤ 1 := by
    dsimp [G]
    apply (div_le_one (by positivity)).2
    linarith [hFupper n x]
  have hGint (n : ℕ) : Integrable (G n) μ := by
    refine ⟨(hGmeas n).aestronglyMeasurable,
      HasFiniteIntegral.of_bounded (C := 1) ?_⟩
    exact ae_of_all _ fun x ↦ abs_le.mpr ⟨by linarith [hGnonneg n x], hGle n x⟩
  have hG_integral (n : ℕ) :
      (∫ x, G n x ∂μ) = ((∫ x, F n x ∂μ) + C) / (2 * C) := by
    simp only [G]
    rw [integral_div, integral_add (by
      refine ⟨(hFmeas n).aestronglyMeasurable,
        HasFiniteIntegral.of_bounded (C := C) ?_⟩
      exact ae_of_all _ fun x ↦ abs_le.mpr ⟨hFlower n x, hFupper n x⟩)
      (integrable_const C)]
    simp
  have hGlim : Tendsto (fun n ↦ ∫ x, G n x ∂μ) atTop (𝓝 (1 / 2 : ℝ)) := by
    have hmap : ContinuousAt (fun t : ℝ ↦ (t + C) / (2 * C)) 0 := by fun_prop
    have ht := hmap.tendsto.comp hlim
    rw [show (0 + C) / (2 * C) = (1 / 2 : ℝ) by
      rw [zero_add]
      field_simp] at ht
    exact ht.congr' (Eventually.of_forall fun n ↦ (hG_integral n).symm)
  have hGe_integral (n : ℕ) :
      (∫⁻ x, Ge n x ∂μ) = ENNReal.ofReal (∫ x, G n x ∂μ) := by
    symm
    exact ofReal_integral_eq_lintegral_ofReal (hGint n)
      (ae_of_all _ fun x ↦ hGnonneg n x)
  have hGelim : Tendsto (fun n ↦ ∫⁻ x, Ge n x ∂μ) atTop
      (𝓝 (ENNReal.ofReal (1 / 2 : ℝ))) := by
    have hoflim := (ENNReal.continuous_ofReal.tendsto (1 / 2 : ℝ)).comp hGlim
    exact hoflim.congr' (Eventually.of_forall fun n ↦ (hGe_integral n).symm)
  have hGele (n : ℕ) (x : α) : Ge n x ≤ 1 :=
    ENNReal.ofReal_le_one.mpr (hGle n x)
  obtain ⟨x, hxZ, hx⟩ := exists_notMem_null_le_limsup_of_tendsto_lintegral
    μ Ge (ENNReal.ofReal (1 / 2 : ℝ)) hGeMeas hGele hGelim Z hZ
  refine ⟨x, hxZ, ?_⟩
  have hFbddAbove : IsBoundedUnder (· ≤ ·) atTop (fun n ↦ F n x) :=
    isBoundedUnder_of_eventually_le (a := C)
      (Eventually.of_forall fun n ↦ hFupper n x)
  have hFcobdd : IsCoboundedUnder (· ≤ ·) atTop (fun n ↦ F n x) :=
    IsCoboundedUnder.of_frequently_ge (a := -C)
      (Frequently.of_forall fun n ↦ hFlower n x)
  let phi : ℝ → ℝ := fun t ↦ (t + C) / (2 * C)
  have hphiMono : Monotone phi := by
    intro a b hab
    dsimp [phi]
    apply div_le_div_of_nonneg_right _ (by positivity)
    linarith
  have hphiCont : Continuous phi := by fun_prop
  have hlimsupG :
      limsup (fun n ↦ G n x) atTop = phi (limsup (fun n ↦ F n x) atTop) := by
    symm
    simpa only [G, phi, Function.comp_def] using
      hphiMono.map_limsup_of_continuousAt (fun n ↦ F n x)
        hphiCont.continuousAt hFbddAbove hFcobdd
  have hGbounded : IsBoundedUnder (· ≤ ·) atTop (fun n ↦ G n x) :=
    isBoundedUnder_of_eventually_le (a := 1)
      (Eventually.of_forall fun n ↦ hGle n x)
  have hGcobdd : IsCoboundedUnder (· ≤ ·) atTop (fun n ↦ G n x) :=
    IsCoboundedUnder.of_frequently_ge (a := 0)
      (Frequently.of_forall fun n ↦ hGnonneg n x)
  have hofReal : ENNReal.ofReal (limsup (fun n ↦ G n x) atTop) =
      limsup (fun n ↦ Ge n x) atTop := by
    simpa only [Ge] using ENNReal.ofReal_limsup hGcobdd hGbounded
  have hlimsupGnonneg : 0 ≤ limsup (fun n ↦ G n x) atTop :=
    le_limsup_of_frequently_le
      (Frequently.of_forall fun n ↦ hGnonneg n x) hGbounded
  have hxReal : (1 / 2 : ℝ) ≤ limsup (fun n ↦ G n x) atTop := by
    rw [← hofReal] at hx
    exact (ENNReal.ofReal_le_ofReal_iff hlimsupGnonneg).mp hx
  rw [hlimsupG] at hxReal
  dsimp [phi] at hxReal
  rw [le_div_iff₀ (by positivity : 0 < 2 * C)] at hxReal
  linarith

/-- The ultrafilter selection theorem underlying MRR, Theorem 4.11,
specialized to interval Følner sets. -/
theorem exists_betaEvent_limsup_betaCrossAverage_nonneg
    (N : ℕ → ℕ) (hNpos : ∀ k, 0 < N k)
    (q : Ultrafilter ℕ) (hq : (q : Filter ℕ) ≤ atTop)
    (μ : ProbabilityMeasure BetaNat)
    (hμ : Tendsto (fun k ↦ betaEmpirical (N k) (hNpos k))
      (q : Filter ℕ) (𝓝 μ))
    (B : Set ℕ) (d : ℝ) (hd : 0 < d)
    (hBd : ∀ᶠ k in atTop, d ≤ finsetDensity (Finset.range (N k)) B)
    (f h : ℕ → ℝ) (C H : ℝ) (hC : 0 < C) (hH : 0 < H)
    (hf : ∀ n, |f n| ≤ C) (hh : ∀ n, |h n| ≤ H)
    (hanti : ∀ n, Tendsto
      (fun k ↦ realFinsetMean (Finset.range (N k))
        (fun m ↦ realIndicator B m * f (n + m))) atTop (𝓝 0)) :
    ∃ p ∈ betaEvent B,
      0 ≤ limsup (fun k ↦ betaCrossAverage (N k) h f C hf p) atTop := by
  let S : Set BetaNat := betaEvent B
  have hSmeas : MeasurableSet S := (betaEvent_isClopen B).2.measurableSet
  have hSne : (μ : Measure BetaNat) S ≠ 0 :=
    betaEvent_measure_ne_zero_of_lower_density N hNpos q hq μ hμ B d hd hBd
  let ν : Measure BetaNat := (μ : Measure BetaNat)[|S]
  let : IsProbabilityMeasure ν := ProbabilityTheory.cond_isProbabilityMeasure hSne
  have hνcompl : ν Sᶜ = 0 := by
    dsimp only [ν]
    rw [ProbabilityTheory.cond_apply hSmeas]
    simp
  have hInt (K : ℕ) :
      ∫ p, betaCrossAverage (N K) h f C hf p ∂ν = 0 := by
    have hprod := integral_betaIndicator_mul_betaCrossAverage_eq_zero
      N hNpos q hq μ hμ B f h C hf hanti K
    have hind :
        (fun p ↦ betaIndicator B p * betaCrossAverage (N K) h f C hf p) =
          S.indicator (fun p ↦ betaCrossAverage (N K) h f C hf p) := by
      funext p
      change betaIndicator B p * betaCrossAverage (N K) h f C hf p =
        (betaEvent B).indicator (fun p ↦ betaCrossAverage (N K) h f C hf p) p
      rw [congrFun (betaIndicator_eq_indicator_betaEvent B) p]
      by_cases hp : p ∈ S <;> simp [S] at hp ⊢ <;> simp [hp]
    rw [hind, integral_indicator hSmeas] at hprod
    dsimp only [ν, ProbabilityTheory.cond]
    rw [integral_smul_measure, hprod]
    simp
  have hIntTend : Tendsto
      (fun K ↦ ∫ p, betaCrossAverage (N K) h f C hf p ∂ν)
      atTop (𝓝 0) := by
    simpa only [hInt] using tendsto_const_nhds
  have hbound (K : ℕ) (p : BetaNat) :
      |betaCrossAverage (N K) h f C hf p| ≤ H * C :=
    abs_betaCrossAverage_le (N K) (hNpos K) h f H C hh hf p
  obtain ⟨p, hpcompl, hp⟩ :=
    exists_notMem_null_nonneg_limsup_of_tendsto_integral_zero
      ν (fun K p ↦ betaCrossAverage (N K) h f C hf p)
      (H * C) (mul_pos hH hC)
      (fun K ↦ (betaCrossAverage (N K) h f C hf).continuous.measurable)
      (fun K p ↦ (abs_le.mp (hbound K p)).1)
      (fun K p ↦ (abs_le.mp (hbound K p)).2)
      hIntTend Sᶜ hνcompl
  exact ⟨p, by simpa [S] using hpcompl, hp⟩

open CompactlySupported Filter Function MeasureTheory Set
open scoped BoundedContinuousFunction ComplexConjugate ENNReal NNReal Pointwise Topology

namespace Erdos109

noncomputable section

noncomputable local instance : MeasurableSpace BetaNat := borel BetaNat
local instance : BorelSpace BetaNat := ⟨rfl⟩

/-- Stone--Čech extension of a bounded complex sequence. -/
noncomputable def betaExtendComplex (f : ℕ → ℂ) (C : ℝ)
    (hf : ∀ n, ‖f n‖ ≤ C) : C(BetaNat, ℂ) := by
  let fs : ℕ → Metric.closedBall (0 : ℂ) C := fun n ↦ ⟨f n, by simpa using hf n⟩
  letI : CompactSpace (Metric.closedBall (0 : ℂ) C) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : ℂ) C)
  exact ⟨fun p ↦ (Ultrafilter.extend fs p : Metric.closedBall (0 : ℂ) C),
    continuous_subtype_val.comp (continuous_ultrafilter_extend fs)⟩

@[simp] theorem betaExtendComplex_pure (f : ℕ → ℂ) (C : ℝ)
    (hf : ∀ n, ‖f n‖ ≤ C) (n : ℕ) :
    betaExtendComplex f C hf (pure n) = f n := by
  simp [betaExtendComplex]

theorem norm_betaExtendComplex_le (f : ℕ → ℂ) (C : ℝ)
    (hf : ∀ n, ‖f n‖ ≤ C) (p : BetaNat) :
    ‖betaExtendComplex f C hf p‖ ≤ C := by
  let fs : ℕ → Metric.closedBall (0 : ℂ) C := fun n ↦ ⟨f n, by simpa using hf n⟩
  let : CompactSpace (Metric.closedBall (0 : ℂ) C) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : ℂ) C)
  have hp := (Ultrafilter.extend fs p).property
  change dist ((Ultrafilter.extend fs p : Metric.closedBall (0 : ℂ) C).1) 0 ≤ C at hp
  change ‖(Ultrafilter.extend fs p : Metric.closedBall (0 : ℂ) C).1‖ ≤ C
  simpa [dist_zero_right] using hp

noncomputable def betaRightTranslateComplex (f : ℕ → ℂ) (C : ℝ)
    (hf : ∀ n, ‖f n‖ ≤ C) (n : ℕ) : C(BetaNat, ℂ) :=
  betaExtendComplex (fun m ↦ f (n + m)) C (fun m ↦ hf (n + m))

@[simp] theorem betaRightTranslateComplex_pure (f : ℕ → ℂ) (C : ℝ)
    (hf : ∀ n, ‖f n‖ ≤ C) (n m : ℕ) :
    betaRightTranslateComplex f C hf n (pure m) = f (n + m) := by
  simp [betaRightTranslateComplex]

theorem norm_betaRightTranslateComplex_le (f : ℕ → ℂ) (C : ℝ)
    (hf : ∀ n, ‖f n‖ ≤ C) (n : ℕ) (p : BetaNat) :
    ‖betaRightTranslateComplex f C hf n p‖ ≤ C :=
  norm_betaExtendComplex_le (fun m ↦ f (n + m)) C (fun m ↦ hf (n + m)) p

theorem betaRightTranslateComplex_of_continuous (F : C(BetaNat, ℂ))
    (C : ℝ) (hF : ∀ p, ‖F p‖ ≤ C) (n : ℕ) :
    betaRightTranslateComplex (fun m ↦ F (pure m)) C
        (fun m ↦ hF (pure m)) n =
      F.comp ⟨betaShift^[n], continuous_betaShift.iterate n⟩ := by
  apply ContinuousMap.ext
  have heq :
      (betaRightTranslateComplex (fun m ↦ F (pure m)) C
          (fun m ↦ hF (pure m)) n : BetaNat → ℂ) =
        (F.comp ⟨betaShift^[n], continuous_betaShift.iterate n⟩ : BetaNat → ℂ) := by
    apply (denseRange_pure : DenseRange (pure : ℕ → BetaNat)).equalizer
    · exact (betaRightTranslateComplex _ C _ n).continuous
    · exact (F.comp ⟨betaShift^[n], continuous_betaShift.iterate n⟩).continuous
    funext m
    simp only [Function.comp_apply, ContinuousMap.comp_apply,
      betaRightTranslateComplex_pure]
    have hit : betaShift^[n] (pure m) = pure (m + n) := by
      induction n with
      | zero => simp
      | succ n ih =>
          rw [Function.iterate_succ_apply', ih, betaShift_pure]
          congr 1
    change F (pure (n + m)) = F (betaShift^[n] (pure m))
    rw [hit, add_comm]
  exact congrFun heq

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The compact closure of the forward orbit of an almost-periodic vector. -/
def compactOrbit (U : H ≃ₗᵢ[ℂ] H) (c : H) : Set H :=
  closure (Set.range fun n : ℕ ↦ (U ^ n) c)

theorem isCompact_compactOrbit (U : H ≃ₗᵢ[ℂ] H) (c : H)
    (hc : TotallyBounded (Set.range fun n : ℕ ↦ (U ^ n) c)) :
    IsCompact (compactOrbit U c) := by
  exact hc.closure.isCompact_of_isClosed isClosed_closure

def compactOrbitPoint (U : H ≃ₗᵢ[ℂ] H) (c : H) (n : ℕ) :
    compactOrbit U c :=
  ⟨(U ^ n) c, subset_closure (Set.mem_range_self n)⟩

@[simp] theorem compactOrbitPoint_val (U : H ≃ₗᵢ[ℂ] H) (c : H) (n : ℕ) :
    (compactOrbitPoint U c n : H) = (U ^ n) c := rfl

/-- A scalar observable sampled along a compact unitary orbit. -/
noncomputable def compactOrbitCode (U : H ≃ₗᵢ[ℂ] H) (c : H)
    (ψ : compactOrbit U c →ᵇ ℂ) (n : ℕ) : ℂ :=
  ψ (compactOrbitPoint U c n)

theorem norm_compactOrbitCode_le (U : H ≃ₗᵢ[ℂ] H) (c : H)
    (hc : TotallyBounded (Set.range fun n : ℕ ↦ (U ^ n) c))
    (ψ : compactOrbit U c →ᵇ ℂ) (n : ℕ) :
    ‖compactOrbitCode U c ψ n‖ ≤ ‖ψ‖ :=
  ψ.norm_coe_le_norm _

/-- The Stone--Čech continuous extension of a compact-orbit code. -/
noncomputable def compactOrbitExtension (U : H ≃ₗᵢ[ℂ] H) (c : H)
    (hc : TotallyBounded (Set.range fun n : ℕ ↦ (U ^ n) c))
    (ψ : compactOrbit U c →ᵇ ℂ) : C(BetaNat, ℂ) :=
  betaExtendComplex (compactOrbitCode U c ψ) ‖ψ‖
    (norm_compactOrbitCode_le U c hc ψ)

@[simp] theorem compactOrbitExtension_pure (U : H ≃ₗᵢ[ℂ] H) (c : H)
    (hc : TotallyBounded (Set.range fun n : ℕ ↦ (U ^ n) c))
    (ψ : compactOrbit U c →ᵇ ℂ) (n : ℕ) : compactOrbitExtension U c hc ψ (pure n) =
      compactOrbitCode U c ψ n := by
  simp [compactOrbitExtension]

theorem norm_compactOrbitExtension_le (U : H ≃ₗᵢ[ℂ] H) (c : H)
    (hc : TotallyBounded (Set.range fun n : ℕ ↦ (U ^ n) c))
    (ψ : compactOrbit U c →ᵇ ℂ) (p : BetaNat) :
    ‖compactOrbitExtension U c hc ψ p‖ ≤ ‖ψ‖ :=
  norm_betaExtendComplex_le _ _ _ p

@[simp] theorem compactOrbitExtension_zero (U : H ≃ₗᵢ[ℂ] H) (c : H)
    (hc : TotallyBounded (Set.range fun n : ℕ ↦ (U ^ n) c)) :
    compactOrbitExtension U c hc (0 : compactOrbit U c →ᵇ ℂ) = 0 := by
  apply ContinuousMap.ext
  have heq :
      (compactOrbitExtension U c hc (0 : compactOrbit U c →ᵇ ℂ) : BetaNat → ℂ) =
        (0 : BetaNat → ℂ) := by
    apply (denseRange_pure : DenseRange (pure : ℕ → BetaNat)).equalizer
    · exact (compactOrbitExtension U c hc 0).continuous
    · fun_prop
    funext n
    simp [compactOrbitCode]
  exact congrFun heq

theorem compactOrbitExtension_add (U : H ≃ₗᵢ[ℂ] H) (c : H)
    (hc : TotallyBounded (Set.range fun n : ℕ ↦ (U ^ n) c))
    (ψ φ : compactOrbit U c →ᵇ ℂ) :
    compactOrbitExtension U c hc (ψ + φ) =
      compactOrbitExtension U c hc ψ + compactOrbitExtension U c hc φ := by
  apply ContinuousMap.ext
  have heq :
      (compactOrbitExtension U c hc (ψ + φ) : BetaNat → ℂ) =
        (compactOrbitExtension U c hc ψ +
          compactOrbitExtension U c hc φ : C(BetaNat, ℂ)) := by
    apply (denseRange_pure : DenseRange (pure : ℕ → BetaNat)).equalizer
    · exact (compactOrbitExtension U c hc (ψ + φ)).continuous
    · exact (compactOrbitExtension U c hc ψ +
        compactOrbitExtension U c hc φ).continuous
    funext n
    simp [compactOrbitCode]
  exact congrFun heq

theorem compactOrbitExtension_smul (U : H ≃ₗᵢ[ℂ] H) (c : H)
    (hc : TotallyBounded (Set.range fun n : ℕ ↦ (U ^ n) c))
    (a : ℂ) (ψ : compactOrbit U c →ᵇ ℂ) :
    compactOrbitExtension U c hc (a • ψ) =
      a • compactOrbitExtension U c hc ψ := by
  apply ContinuousMap.ext
  have heq :
      (compactOrbitExtension U c hc (a • ψ) : BetaNat → ℂ) =
        (a • compactOrbitExtension U c hc ψ : C(BetaNat, ℂ)) := by
    apply (denseRange_pure : DenseRange (pure : ℕ → BetaNat)).equalizer
    · exact (compactOrbitExtension U c hc (a • ψ)).continuous
    · exact (a • compactOrbitExtension U c hc ψ).continuous
    funext n
    simp [compactOrbitCode]
  exact congrFun heq

section BetaFactor

variable {μ : Measure BetaNat} [IsFiniteMeasure μ]

noncomputable def compactOrbitFactorL2 (U : BetaL2 μ ≃ₗᵢ[ℂ] BetaL2 μ)
    (c : BetaL2 μ)
    (hc : TotallyBounded (Set.range fun n : ℕ ↦ (U ^ n) c))
    (ψ : compactOrbit U c →ᵇ ℂ) : BetaL2 μ :=
  ContinuousMap.toLp 2 μ ℂ (compactOrbitExtension U c hc ψ)

@[simp] theorem compactOrbitFactorL2_zero
    (U : BetaL2 μ ≃ₗᵢ[ℂ] BetaL2 μ) (c : BetaL2 μ)
    (hc : TotallyBounded (Set.range fun n : ℕ ↦ (U ^ n) c)) :
    compactOrbitFactorL2 U c hc 0 = 0 := by
  simp [compactOrbitFactorL2]

theorem compactOrbitFactorL2_add
    (U : BetaL2 μ ≃ₗᵢ[ℂ] BetaL2 μ) (c : BetaL2 μ)
    (hc : TotallyBounded (Set.range fun n : ℕ ↦ (U ^ n) c))
    (ψ φ : compactOrbit U c →ᵇ ℂ) :
    compactOrbitFactorL2 U c hc (ψ + φ) =
      compactOrbitFactorL2 U c hc ψ + compactOrbitFactorL2 U c hc φ := by
  simp only [compactOrbitFactorL2, compactOrbitExtension_add, map_add]

theorem compactOrbitFactorL2_smul
    (U : BetaL2 μ ≃ₗᵢ[ℂ] BetaL2 μ) (c : BetaL2 μ)
    (hc : TotallyBounded (Set.range fun n : ℕ ↦ (U ^ n) c))
    (a : ℂ) (ψ : compactOrbit U c →ᵇ ℂ) :
    compactOrbitFactorL2 U c hc (a • ψ) =
      a • compactOrbitFactorL2 U c hc ψ := by
  simp only [compactOrbitFactorL2, compactOrbitExtension_smul, map_smul]

noncomputable def compactOrbitFactorSubmodule
    (U : BetaL2 μ ≃ₗᵢ[ℂ] BetaL2 μ) (c : BetaL2 μ)
    (hc : TotallyBounded (Set.range fun n : ℕ ↦ (U ^ n) c)) :
    Submodule ℂ (BetaL2 μ) where
  carrier := Set.range (compactOrbitFactorL2 U c hc)
  zero_mem' := ⟨0, compactOrbitFactorL2_zero U c hc⟩
  add_mem' := by
    rintro _ _ ⟨ψ, rfl⟩ ⟨φ, rfl⟩
    exact ⟨ψ + φ, compactOrbitFactorL2_add U c hc ψ φ⟩
  smul_mem' := by
    rintro a _ ⟨ψ, rfl⟩
    exact ⟨a • ψ, compactOrbitFactorL2_smul U c hc a ψ⟩

noncomputable def compactOrbitFactorClosed
    (U : BetaL2 μ ≃ₗᵢ[ℂ] BetaL2 μ) (c : BetaL2 μ)
    (hc : TotallyBounded (Set.range fun n : ℕ ↦ (U ^ n) c)) :
    ClosedSubmodule ℂ (BetaL2 μ) :=
  (compactOrbitFactorSubmodule U c hc).closure

noncomputable def betaShiftComplex (F : C(BetaNat, ℂ)) : C(BetaNat, ℂ) :=
  F.comp ⟨betaShift, continuous_betaShift⟩

@[simp] theorem betaShiftComplex_apply (F : C(BetaNat, ℂ)) (p : BetaNat) :
    betaShiftComplex F p = F (betaShift p) := rfl

theorem iterate_betaShiftComplex_apply (F : C(BetaNat, ℂ)) (n : ℕ) (p : BetaNat) :
    betaShiftComplex^[n] F p = F (betaShift^[n] p) := by
  induction n generalizing p with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', betaShiftComplex_apply, ih]
      congr 1

theorem betaKoopman_continuousMap {μ : Measure BetaNat} [IsFiniteMeasure μ]
    (hμ : MeasurePreserving betaShift μ μ) (F : C(BetaNat, ℂ)) :
    betaKoopman hμ (ContinuousMap.toLp 2 μ ℂ F) =
      ContinuousMap.toLp 2 μ ℂ (betaShiftComplex F) := by
  change Lp.compMeasurePreserving betaShift hμ (ContinuousMap.toLp 2 μ ℂ F) = _
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving (ContinuousMap.toLp 2 μ ℂ F) hμ,
    hμ.quasiMeasurePreserving.ae_eq_comp
      (ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) μ F),
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) μ (betaShiftComplex F)] with
      p hcomp hFcomp hshift
  rw [hcomp]
  change (((ContinuousMap.toLp 2 μ ℂ F : BetaL2 μ) : BetaNat → ℂ) ∘ betaShift) p =
    ((ContinuousMap.toLp 2 μ ℂ (betaShiftComplex F) : BetaL2 μ) : BetaNat → ℂ) p
  rw [hFcomp, hshift]
  rfl

theorem betaKoopman_pow_continuousMap {μ : Measure BetaNat} [IsFiniteMeasure μ]
    (hμ : MeasurePreserving betaShift μ μ) (F : C(BetaNat, ℂ)) (n : ℕ) :
    (betaKoopman hμ ^ n) (ContinuousMap.toLp 2 μ ℂ F) =
      ContinuousMap.toLp 2 μ ℂ (betaShiftComplex^[n] F) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ']
      change betaKoopman hμ ((betaKoopman hμ ^ n)
        (ContinuousMap.toLp 2 μ ℂ F)) = _
      rw [ih, betaKoopman_continuousMap]
      rw [Function.iterate_succ_apply']

theorem dist_compactOrbitPoint_add (U : BetaL2 μ ≃ₗᵢ[ℂ] BetaL2 μ)
    (c : BetaL2 μ) (k n m : ℕ) :
    dist (compactOrbitPoint U c (k + n)) (compactOrbitPoint U c (k + m)) =
      dist (compactOrbitPoint U c n) (compactOrbitPoint U c m) := by
  change dist ((U ^ (k + n)) c) ((U ^ (k + m)) c) =
    dist ((U ^ n) c) ((U ^ m) c)
  rw [pow_add, pow_add]
  change dist ((U ^ k) ((U ^ n) c)) ((U ^ k) ((U ^ m) c)) = _
  rw [(U ^ k).dist_map]

theorem compactOrbitExtension_shift_pure
    (U : BetaL2 μ ≃ₗᵢ[ℂ] BetaL2 μ) (c : BetaL2 μ)
    (hc : TotallyBounded (Set.range fun n : ℕ ↦ (U ^ n) c))
    (ψ : compactOrbit U c →ᵇ ℂ) (n k : ℕ) :
    (betaShiftComplex^[n] (compactOrbitExtension U c hc ψ)) (pure k) =
      ψ (compactOrbitPoint U c (k + n)) := by
  rw [iterate_betaShiftComplex_apply]
  have hit : betaShift^[n] (pure k) = pure (k + n) := by
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Function.iterate_succ_apply', ih, betaShift_pure]
        congr 1
  rw [hit, compactOrbitExtension_pure]
  rfl

theorem norm_toLp_sub_le_of_forall {μ : Measure BetaNat}
    [IsProbabilityMeasure μ] (F G : C(BetaNat, ℂ)) (r : ℝ)
    (h : ∀ p, ‖F p - G p‖ ≤ r) :
    ‖ContinuousMap.toLp 2 μ ℂ F - ContinuousMap.toLp 2 μ ℂ G‖ ≤ r := by
  rw [← map_sub]
  have hr : 0 ≤ r := le_trans (norm_nonneg _) (h (pure 0))
  have hb := Lp.norm_le_of_ae_bound (f := ContinuousMap.toLp 2 μ ℂ (F - G))
    hr (by
      filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) μ (F - G)] with p hp
      rw [hp]
      exact h p)
  simpa [measureUnivNNReal, measure_univ] using hb

theorem norm_compactOrbitFactor_shift_sub_le
    {μ : Measure BetaNat} [IsProbabilityMeasure μ]
    (hμ : MeasurePreserving betaShift μ μ)
    (U : BetaL2 μ ≃ₗᵢ[ℂ] BetaL2 μ) (c : BetaL2 μ)
    (hc : TotallyBounded (Set.range fun n : ℕ ↦ (U ^ n) c))
    (ψ : compactOrbit U c →ᵇ ℂ) (n m : ℕ) (r : ℝ)
    (hr : ∀ k, ‖ψ (compactOrbitPoint U c (k + n)) -
        ψ (compactOrbitPoint U c (k + m))‖ ≤ r) :
    ‖(betaKoopman hμ ^ n) (compactOrbitFactorL2 U c hc ψ) -
        (betaKoopman hμ ^ m) (compactOrbitFactorL2 U c hc ψ)‖ ≤ r := by
  rw [compactOrbitFactorL2, betaKoopman_pow_continuousMap,
    betaKoopman_pow_continuousMap]
  apply norm_toLp_sub_le_of_forall _ _ r
  intro p
  have hpure : ∀ k,
      ‖(betaShiftComplex^[n] (compactOrbitExtension U c hc ψ)) (pure k) -
        (betaShiftComplex^[m] (compactOrbitExtension U c hc ψ)) (pure k)‖ ≤ r := by
    intro k
    simpa only [compactOrbitExtension_shift_pure] using hr k
  let D : C(BetaNat, ℝ) :=
    ⟨fun p ↦ ‖(betaShiftComplex^[n] (compactOrbitExtension U c hc ψ)) p -
        (betaShiftComplex^[m] (compactOrbitExtension U c hc ψ)) p‖,
      ((betaShiftComplex^[n] (compactOrbitExtension U c hc ψ)).continuous.sub
        (betaShiftComplex^[m] (compactOrbitExtension U c hc ψ)).continuous).norm⟩
  have hD : ∀ p, D p ≤ r := by
    have hclosed : IsClosed {p : BetaNat | D p ≤ r} :=
      isClosed_Iic.preimage D.continuous
    have hrange : Set.range (pure : ℕ → BetaNat) ⊆ {p : BetaNat | D p ≤ r} := by
      rintro _ ⟨k, rfl⟩
      exact hpure k
    have hclosure : closure (Set.range (pure : ℕ → BetaNat)) ⊆
        {p : BetaNat | D p ≤ r} := closure_minimal hrange hclosed
    have hdense : closure (Set.range (pure : ℕ → BetaNat)) = Set.univ :=
      (denseRange_pure : DenseRange (pure : ℕ → BetaNat)).closure_range
    intro p
    exact hclosure (by rw [hdense]; exact Set.mem_univ p)
  exact hD p

theorem totallyBounded_compactOrbitFactorL2_orbit
    {μ : Measure BetaNat} [IsProbabilityMeasure μ]
    (hμ : MeasurePreserving betaShift μ μ)
    (U : BetaL2 μ ≃ₗᵢ[ℂ] BetaL2 μ) (c : BetaL2 μ)
    (hc : TotallyBounded (Set.range fun n : ℕ ↦ (U ^ n) c))
    (ψ : compactOrbit U c →ᵇ ℂ) :
    TotallyBounded (Set.range fun n : ℕ ↦
      (betaKoopman hμ ^ n) (compactOrbitFactorL2 U c hc ψ)) := by
  rw [Metric.totallyBounded_iff]
  intro ε hε
  let : CompactSpace (compactOrbit U c) :=
    isCompact_iff_compactSpace.mp (isCompact_compactOrbit U c hc)
  have hψuc : UniformContinuous ψ :=
    CompactSpace.uniformContinuous_of_continuous ψ.continuous
  obtain ⟨δ, hδ, hψ⟩ := (Metric.uniformContinuous_iff.mp hψuc)
    (ε / 2) (by positivity)
  obtain ⟨centres, hcentres_subset, hcentres_finite, hcover⟩ :=
    Metric.finite_approx_of_totallyBounded hc δ hδ
  let index : centres → ℕ := fun z ↦
    Classical.choose (hcentres_subset z.2)
  have hindex (z : centres) : (U ^ index z) c = z.1 :=
    Classical.choose_spec (hcentres_subset z.2)
  let : Fintype centres := hcentres_finite.fintype
  let t : Set (BetaL2 μ) := Set.range fun z : centres ↦
    (betaKoopman hμ ^ index z) (compactOrbitFactorL2 U c hc ψ)
  have htfin : t.Finite := by
    exact Set.finite_range _
  refine ⟨t, htfin, ?_⟩
  intro v hv
  obtain ⟨n, rfl⟩ := hv
  have hncover := hcover (Set.mem_range_self n)
  rcases Set.mem_iUnion.mp hncover with ⟨z, hz⟩
  rcases Set.mem_iUnion.mp hz with ⟨hzcentres, hnz⟩
  let z' : centres := ⟨z, hzcentres⟩
  refine Set.mem_iUnion₂.mpr ⟨
    (betaKoopman hμ ^ index z') (compactOrbitFactorL2 U c hc ψ),
    Set.mem_range_self z', ?_⟩
  rw [Metric.mem_ball]
  rw [dist_eq_norm]
  calc
    ‖(betaKoopman hμ ^ n) (compactOrbitFactorL2 U c hc ψ) -
        (betaKoopman hμ ^ index z') (compactOrbitFactorL2 U c hc ψ)‖ ≤ ε / 2 := by
      apply norm_compactOrbitFactor_shift_sub_le hμ U c hc ψ n (index z') (ε / 2)
      intro k
      have hbase : dist (compactOrbitPoint U c n)
          (compactOrbitPoint U c (index z')) < δ := by
        change dist ((U ^ n) c) ((U ^ index z') c) < δ
        rw [hindex z']
        exact hnz
      have hshift : dist (compactOrbitPoint U c (k + n))
          (compactOrbitPoint U c (k + index z')) < δ := by
        rw [dist_compactOrbitPoint_add]
        exact hbase
      simpa only [dist_eq_norm] using hψ hshift |>.le
    _ < ε := by linarith

theorem compactOrbitFactorSubmodule_le_almostPeriodic
    {μ : Measure BetaNat} [IsProbabilityMeasure μ]
    (hμ : MeasurePreserving betaShift μ μ)
    (c : BetaL2 μ)
    (hc : TotallyBounded
      (Set.range fun n : ℕ ↦ (betaKoopman hμ ^ n) c)) :
    compactOrbitFactorSubmodule (betaKoopman hμ) c hc ≤
      unitaryAlmostPeriodicSubmodule (betaKoopman hμ) := by
  rintro _ ⟨ψ, rfl⟩
  exact totallyBounded_compactOrbitFactorL2_orbit hμ (betaKoopman hμ) c hc ψ

theorem compactOrbitFactorClosed_le_kronecker
    {μ : Measure BetaNat} [IsProbabilityMeasure μ]
    (hμ : MeasurePreserving betaShift μ μ)
    (c : BetaL2 μ)
    (hc : TotallyBounded
      (Set.range fun n : ℕ ↦ (betaKoopman hμ ^ n) c)) :
    (compactOrbitFactorClosed (betaKoopman hμ) c hc).toSubmodule ≤
      (unitaryKronecker (betaKoopman hμ)).toSubmodule := by
  rw [← unitaryAlmostPeriodic_eq_kronecker]
  exact Submodule.topologicalClosure_minimal _
    (compactOrbitFactorSubmodule_le_almostPeriodic hμ c hc)
    (by
      change IsClosed (unitaryAlmostPeriodic (betaKoopman hμ))
      exact isClosed_unitaryAlmostPeriodic (betaKoopman hμ))

theorem compactOrbitExtension_one
    (U : BetaL2 μ ≃ₗᵢ[ℂ] BetaL2 μ) (c : BetaL2 μ)
    (hc : TotallyBounded (Set.range fun n : ℕ ↦ (U ^ n) c)) :
    compactOrbitExtension U c hc (1 : compactOrbit U c →ᵇ ℂ) = 1 := by
  apply ContinuousMap.ext
  have heq :
      (compactOrbitExtension U c hc (1 : compactOrbit U c →ᵇ ℂ) :
          BetaNat → ℂ) = (1 : BetaNat → ℂ) := by
    apply (denseRange_pure : DenseRange (pure : ℕ → BetaNat)).equalizer
    · exact (compactOrbitExtension U c hc 1).continuous
    · fun_prop
    funext n
    simp [compactOrbitCode]
  exact congrFun heq

theorem compactOrbitFactorL2_one
    (U : BetaL2 μ ≃ₗᵢ[ℂ] BetaL2 μ) (c : BetaL2 μ)
    (hc : TotallyBounded (Set.range fun n : ℕ ↦ (U ^ n) c)) :
    compactOrbitFactorL2 U c hc (1 : compactOrbit U c →ᵇ ℂ) =
      ContinuousMap.toLp 2 μ ℂ (1 : C(BetaNat, ℂ)) := by
  simp only [compactOrbitFactorL2, compactOrbitExtension_one]

theorem continuous_one_mem_compactOrbitFactorClosed
    (U : BetaL2 μ ≃ₗᵢ[ℂ] BetaL2 μ) (c : BetaL2 μ)
    (hc : TotallyBounded (Set.range fun n : ℕ ↦ (U ^ n) c)) :
    ContinuousMap.toLp 2 μ ℂ (1 : C(BetaNat, ℂ)) ∈
      compactOrbitFactorClosed U c hc := by
  apply (compactOrbitFactorSubmodule U c hc).le_topologicalClosure
  exact ⟨1, compactOrbitFactorL2_one U c hc⟩

end BetaFactor

end

end Erdos109

open CompactlySupported Filter Function MeasureTheory Set
open scoped BoundedContinuousFunction ComplexConjugate ENNReal NNReal Pointwise Topology

namespace Erdos109

noncomputable section

noncomputable local instance : MeasurableSpace BetaNat := borel BetaNat
local instance : BorelSpace BetaNat := ⟨rfl⟩

/-- Extract an ordinary subsequence realizing any prescribed countable family
of continuous test integrals from an empirical ultralimit. -/
theorem exists_subseq_integrals_tendsto_of_ultrafilter
    (N : ℕ → ℕ) (hNpos : ∀ k, 0 < N k)
    (q : Ultrafilter ℕ) (hq : (q : Filter ℕ) ≤ atTop)
    (μ : ProbabilityMeasure BetaNat)
    (hμ : Tendsto (fun k ↦ betaEmpirical (N k) (hNpos k))
      (q : Filter ℕ) (𝓝 μ))
    (g : ℕ → C(BetaNat, ℝ)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ j,
      Tendsto
        (fun k ↦ ∫ p, g j p
          ∂((betaEmpirical (N (φ k)) (hNpos (φ k)) :
            ProbabilityMeasure BetaNat) : Measure BetaNat))
        atTop (𝓝 (∫ p, g j p ∂(μ : Measure BetaNat))) := by
  let x : ℕ → (ℕ → ℝ) := fun k j ↦
    ∫ p, g j p
      ∂((betaEmpirical (N k) (hNpos k) : ProbabilityMeasure BetaNat) :
        Measure BetaNat)
  let y : ℕ → ℝ := fun j ↦ ∫ p, g j p ∂(μ : Measure BetaNat)
  have hxy : Tendsto x (q : Filter ℕ) (𝓝 y) := by
    rw [tendsto_pi_nhds]
    intro j
    let gb : BetaNat →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact (g j)
    simpa [x, y, gb] using
      (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hμ) gb
  have hcluster : NeBot ((𝓝 y) ⊓ map x atTop) := by
    exact (inferInstance : NeBot (map x (q : Filter ℕ))).mono
      (le_inf hxy (map_mono hq))
  obtain ⟨φ, hφ, hφlim⟩ := subseq_tendsto_of_neBot hcluster
  refine ⟨φ, hφ, fun j ↦ ?_⟩
  have hj := (tendsto_pi_nhds.mp hφlim) j
  simpa only [Function.comp_apply, x, y] using hj

/-- Signed reverse Fatou at an arbitrary limiting first moment, while
avoiding a prescribed null set. -/
theorem exists_notMem_null_limsup_ge_of_tendsto_integral
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (F : ℕ → α → ℝ) (C : ℝ) (hC : 0 < C)
    (hFmeas : ∀ n, Measurable (F n))
    (hFlower : ∀ n x, -C ≤ F n x)
    (hFupper : ∀ n x, F n x ≤ C)
    (r : ℝ)
    (hlim : Tendsto (fun n ↦ ∫ x, F n x ∂μ) atTop (𝓝 r))
    (Z : Set α) (hZ : μ Z = 0) :
    ∃ x ∉ Z, r ≤ limsup (fun n ↦ F n x) atTop := by
  let D : ℝ := C + |r|
  have hD : 0 < D := by dsimp [D]; positivity
  have hFint (n : ℕ) : Integrable (F n) μ := by
    refine ⟨(hFmeas n).aestronglyMeasurable,
      HasFiniteIntegral.of_bounded (C := C) ?_⟩
    exact ae_of_all _ fun x ↦ abs_le.mpr ⟨hFlower n x, hFupper n x⟩
  have hshiftlim : Tendsto
      (fun n ↦ ∫ x, F n x - r ∂μ) atTop (𝓝 0) := by
    have hi : (fun n ↦ ∫ x, F n x - r ∂μ) =
        fun n ↦ (∫ x, F n x ∂μ) - r := by
      funext n
      rw [integral_sub (hFint n) (integrable_const r)]
      simp
    rw [hi]
    have hc : Tendsto (fun _ : ℕ ↦ r) atTop (𝓝 r) := tendsto_const_nhds
    simpa only [sub_self] using hlim.sub hc
  obtain ⟨x, hxZ, hx⟩ :=
    exists_notMem_null_nonneg_limsup_of_tendsto_integral_zero
      μ (fun n x ↦ F n x - r) D hD
      (fun n ↦ (hFmeas n).sub measurable_const)
      (fun n x ↦ by
        dsimp [D]
        have hr : r ≤ |r| := le_abs_self r
        linarith [hFlower n x])
      (fun n x ↦ by
        dsimp [D]
        have hr : -r ≤ |r| := neg_le_abs r
        linarith [hFupper n x])
      hshiftlim Z hZ
  refine ⟨x, hxZ, ?_⟩
  have hFbddAbove : IsBoundedUnder (· ≤ ·) atTop (fun n ↦ F n x) :=
    isBoundedUnder_of_eventually_le (a := C)
      (Eventually.of_forall fun n ↦ hFupper n x)
  have hFcobdd : IsCoboundedUnder (· ≤ ·) atTop (fun n ↦ F n x) :=
    IsCoboundedUnder.of_frequently_ge (a := -C)
      (Frequently.of_forall fun n ↦ hFlower n x)
  let phi : ℝ → ℝ := fun t ↦ t - r
  have hphiMono : Monotone phi := fun _ _ hab ↦ sub_le_sub_right hab r
  have hphiCont : Continuous phi := by fun_prop
  have hls :
      limsup (fun n ↦ F n x - r) atTop =
        limsup (fun n ↦ F n x) atTop - r := by
    symm
    simpa only [phi, Function.comp_def] using
      hphiMono.map_limsup_of_continuousAt (fun n ↦ F n x)
        hphiCont.continuousAt hFbddAbove hFcobdd
  rw [hls] at hx
  linarith

end

end Erdos109

open CompactlySupported Filter Function MeasureTheory Set
open scoped BoundedContinuousFunction ComplexConjugate ENNReal NNReal Pointwise Topology

namespace Erdos109

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

noncomputable def weakOrbitDual (U : H ≃ₗᵢ[ℂ] H) (x : H) (n : ℕ) :
    WeakDual ℂ H :=
  StrongDual.toWeakDual (InnerProductSpace.toDual ℂ H ((U ^ n) x))

theorem weakOrbitDual_mem_closedBall (U : H ≃ₗᵢ[ℂ] H) (x : H) (n : ℕ) :
    weakOrbitDual U x n ∈
      WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℂ H) ‖x‖ := by
  change dist (InnerProductSpace.toDual ℂ H ((U ^ n) x)) 0 ≤ ‖x‖
  simp

noncomputable def weakOrbitExtensionDual (U : H ≃ₗᵢ[ℂ] H) (x : H) :
    BetaNat →
      (WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℂ H) ‖x‖) := by
  letI : CompactSpace
      (WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℂ H) ‖x‖) :=
    isCompact_iff_compactSpace.mp (WeakDual.isCompact_closedBall (0 : StrongDual ℂ H) ‖x‖)
  exact Ultrafilter.extend (fun n ↦ ⟨weakOrbitDual U x n,
    weakOrbitDual_mem_closedBall U x n⟩)

theorem continuous_weakOrbitExtensionDual (U : H ≃ₗᵢ[ℂ] H) (x : H) :
    Continuous (weakOrbitExtensionDual U x) := by
  let : CompactSpace
      (WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℂ H) ‖x‖) :=
    isCompact_iff_compactSpace.mp (WeakDual.isCompact_closedBall (0 : StrongDual ℂ H) ‖x‖)
  unfold weakOrbitExtensionDual
  exact continuous_ultrafilter_extend _

@[simp] theorem weakOrbitExtensionDual_pure (U : H ≃ₗᵢ[ℂ] H) (x : H) (n : ℕ) :
    weakOrbitExtensionDual U x (pure n) =
      ⟨weakOrbitDual U x n, weakOrbitDual_mem_closedBall U x n⟩ := by
  simp [weakOrbitExtensionDual]

noncomputable def weakOrbitExtension (U : H ≃ₗᵢ[ℂ] H) (x : H) (p : BetaNat) : H :=
  (InnerProductSpace.toDual ℂ H).symm
    (WeakDual.toStrongDual (weakOrbitExtensionDual U x p).1)

theorem norm_weakOrbitExtension_le (U : H ≃ₗᵢ[ℂ] H) (x : H) (p : BetaNat) :
    ‖weakOrbitExtension U x p‖ ≤ ‖x‖ := by
  change ‖(InnerProductSpace.toDual ℂ H).symm
    (WeakDual.toStrongDual (weakOrbitExtensionDual U x p).1)‖ ≤ ‖x‖
  rw [(InnerProductSpace.toDual ℂ H).symm.norm_map]
  have hp := (weakOrbitExtensionDual U x p).2
  change dist (WeakDual.toStrongDual (weakOrbitExtensionDual U x p).1) 0 ≤ ‖x‖ at hp
  simpa only [dist_zero_right] using hp

@[simp] theorem weakOrbitExtension_pure (U : H ≃ₗᵢ[ℂ] H) (x : H) (n : ℕ) :
    weakOrbitExtension U x (pure n) = (U ^ n) x := by
  apply (InnerProductSpace.toDual ℂ H).injective
  change InnerProductSpace.toDual ℂ H
      ((InnerProductSpace.toDual ℂ H).symm
        (WeakDual.toStrongDual (weakOrbitExtensionDual U x (pure n)).1)) =
    InnerProductSpace.toDual ℂ H ((U ^ n) x)
  rw [(InnerProductSpace.toDual ℂ H).apply_symm_apply]
  simp [weakOrbitDual]

theorem continuous_inner_weakOrbitExtension (U : H ≃ₗᵢ[ℂ] H) (x y : H) :
    Continuous (fun p : BetaNat ↦ inner ℂ (weakOrbitExtension U x p) y) := by
  have heq : (fun p : BetaNat ↦ inner ℂ (weakOrbitExtension U x p) y) =
      fun p : BetaNat ↦
        (WeakDual.toStrongDual (weakOrbitExtensionDual U x p).1) y := by
    funext p
    exact InnerProductSpace.toDual_symm_apply
  rw [heq]
  exact (WeakDual.eval_continuous y).comp
    (continuous_subtype_val.comp (continuous_weakOrbitExtensionDual U x))

end

end Erdos109

open CompactlySupported Filter Function MeasureTheory Set
open scoped BoundedContinuousFunction ComplexConjugate ENNReal NNReal Pointwise Topology

namespace Erdos109

noncomputable section

noncomputable local instance : MeasurableSpace BetaNat := borel BetaNat
local instance : BorelSpace BetaNat := ⟨rfl⟩

/-- Metric projection of a complex number onto the real interval `[0,1]`. -/
noncomputable def clipComplex01 (z : ℂ) : ℂ :=
  ((min 1 (max 0 z.re) : ℝ) : ℂ)

theorem continuous_clipComplex01 : Continuous clipComplex01 := by
  unfold clipComplex01
  fun_prop

theorem norm_sub_clipComplex01_le_of_eq_zero_or_one
    {x : ℂ} (hx : x = 0 ∨ x = 1) (z : ℂ) :
    ‖x - clipComplex01 z‖ ≤ ‖x - z‖ := by
  rcases hx with rfl | rfl
  · simp only [zero_sub, norm_neg, clipComplex01, Complex.norm_real]
    rw [Real.norm_eq_abs]
    have hre : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
    by_cases hz : z.re ≤ 0
    · simp [max_eq_left hz, abs_zero]
    · have hz0 : 0 ≤ z.re := le_of_not_ge hz
      by_cases hz1 : z.re ≤ 1
      · rw [max_eq_right hz0, min_eq_right hz1, abs_of_nonneg hz0]
        simpa only [abs_of_nonneg hz0] using hre
      · have h1 : 1 ≤ z.re := le_of_not_ge hz1
        rw [max_eq_right hz0, min_eq_left h1, abs_of_nonneg (by positivity)]
        exact le_trans h1 (by simpa [abs_of_nonneg hz0] using hre)
  · rw [show (1 : ℂ) - clipComplex01 z =
        ((1 - min 1 (max 0 z.re) : ℝ) : ℂ) by
          simp [clipComplex01],
      Complex.norm_real, Real.norm_eq_abs]
    have hre : |1 - z.re| ≤ ‖(1 : ℂ) - z‖ := by
      have h := Complex.abs_re_le_norm ((1 : ℂ) - z)
      simpa using h
    by_cases hz : z.re ≤ 0
    · rw [max_eq_left hz]
      norm_num
      exact le_trans (by rw [abs_of_nonneg (by linarith)]; linarith) hre
    · have hz0 : 0 ≤ z.re := le_of_not_ge hz
      by_cases hz1 : z.re ≤ 1
      · rw [max_eq_right hz0, min_eq_right hz1]
        exact hre
      · have h1 : 1 ≤ z.re := le_of_not_ge hz1
        rw [max_eq_right hz0, min_eq_left h1]
        simp

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

noncomputable def clipCompactOrbitObservable
    (U : H ≃ₗᵢ[ℂ] H) (c : H)
    (hc : TotallyBounded (Set.range fun n : ℕ ↦ (U ^ n) c))
    (psi : compactOrbit U c →ᵇ ℂ) : compactOrbit U c →ᵇ ℂ := by
  letI : CompactSpace (compactOrbit U c) :=
    isCompact_iff_compactSpace.mp (isCompact_compactOrbit U c hc)
  exact BoundedContinuousFunction.mkOfCompact
    ⟨clipComplex01 ∘ psi, continuous_clipComplex01.comp psi.continuous⟩

theorem compactOrbitExtension_clip
    (U : H ≃ₗᵢ[ℂ] H) (c : H)
    (hc : TotallyBounded (Set.range fun n : ℕ ↦ (U ^ n) c))
    (psi : compactOrbit U c →ᵇ ℂ) :
    compactOrbitExtension U c hc (clipCompactOrbitObservable U c hc psi) =
      ⟨fun p ↦ clipComplex01 (compactOrbitExtension U c hc psi p),
        continuous_clipComplex01.comp
          (compactOrbitExtension U c hc psi).continuous⟩ := by
  apply ContinuousMap.ext
  apply congrFun
  apply (denseRange_pure : DenseRange (pure : ℕ → BetaNat)).equalizer
  · exact (compactOrbitExtension U c hc
      (clipCompactOrbitObservable U c hc psi)).continuous
  · exact continuous_clipComplex01.comp
      (compactOrbitExtension U c hc psi).continuous
  funext n
  simp [clipCompactOrbitObservable, clipComplex01, compactOrbitCode]

section Beta

variable {mu : Measure BetaNat} [IsProbabilityMeasure mu]

theorem betaIndicatorComplex_eq_zero_or_one (A : Set ℕ) (p : BetaNat) :
    betaIndicatorComplex A p = 0 ∨ betaIndicatorComplex A p = 1 := by
  change (betaIndicator A p : ℂ) = 0 ∨ (betaIndicator A p : ℂ) = 1
  change ((if betaMembership A p = true then (1 : ℝ) else 0 : ℝ) : ℂ) = 0 ∨
    ((if betaMembership A p = true then (1 : ℝ) else 0 : ℝ) : ℂ) = 1
  by_cases h : betaMembership A p = true <;> simp [h]

theorem norm_indicator_sub_clip_factor_le
    (A : Set ℕ)
    (U : BetaL2 mu ≃ₗᵢ[ℂ] BetaL2 mu) (c : BetaL2 mu)
    (hc : TotallyBounded (Set.range fun n : ℕ ↦ (U ^ n) c))
    (psi : compactOrbit U c →ᵇ ℂ) :
    ‖betaIndicatorL2 mu A -
        compactOrbitFactorL2 U c hc (clipCompactOrbitObservable U c hc psi)‖ ≤
      ‖betaIndicatorL2 mu A - compactOrbitFactorL2 U c hc psi‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [Lp.coeFn_sub (betaIndicatorL2 mu A)
      (compactOrbitFactorL2 U c hc (clipCompactOrbitObservable U c hc psi)),
    Lp.coeFn_sub (betaIndicatorL2 mu A) (compactOrbitFactorL2 U c hc psi),
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) mu
      (betaIndicatorComplex A),
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) mu
      (compactOrbitExtension U c hc (clipCompactOrbitObservable U c hc psi)),
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) mu
      (compactOrbitExtension U c hc psi)] with p hsubclip hsub hA hclip hpsi
  rw [hsubclip, hsub]
  simp only [betaIndicatorL2, compactOrbitFactorL2]
  simp only [Pi.sub_apply]
  rw [hA, hclip, hpsi, compactOrbitExtension_clip]
  exact norm_sub_clipComplex01_le_of_eq_zero_or_one
    (betaIndicatorComplex_eq_zero_or_one A p) _

end Beta

end

end Erdos109

open CompactlySupported Filter Function MeasureTheory Set
open scoped BoundedContinuousFunction ComplexConjugate ENNReal NNReal Pointwise Topology

namespace Erdos109

noncomputable section

noncomputable local instance : MeasurableSpace BetaNat := borel BetaNat
local instance : BorelSpace BetaNat := ⟨rfl⟩

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A quantitative Pythagorean estimate around an orthogonal projection. -/
theorem norm_sub_starProjection_sq_le
    (S : Submodule ℂ H) [S.HasOrthogonalProjection]
    (F y yc : H) (hyc : yc ∈ S)
    (hcontract : ‖F - yc‖ ≤ ‖F - y‖) :
    ‖S.starProjection F - yc‖ ^ 2 ≤
      2 * ‖F - S.starProjection F‖ * ‖S.starProjection F - y‖ +
        ‖S.starProjection F - y‖ ^ 2 := by
  have hmem : S.starProjection F - yc ∈ S :=
    S.sub_mem (S.starProjection_apply_mem F) hyc
  have horth : inner ℂ (F - S.starProjection F) (S.starProjection F - yc) = 0 :=
    S.starProjection_inner_eq_zero F _ hmem
  have hdecomp : F - yc =
      (F - S.starProjection F) + (S.starProjection F - yc) := by
    abel
  have hpyth : ‖F - yc‖ ^ 2 = ‖F - S.starProjection F‖ ^ 2 +
      ‖S.starProjection F - yc‖ ^ 2 := by
    rw [hdecomp]
    simpa [pow_two] using
      norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth
  have htriangle : ‖F - y‖ ≤
      ‖F - S.starProjection F‖ + ‖S.starProjection F - y‖ := by
    rw [show F - y = (F - S.starProjection F) +
      (S.starProjection F - y) by abel]
    exact norm_add_le _ _
  have hsquare : ‖F - yc‖ ^ 2 ≤
      (‖F - S.starProjection F‖ + ‖S.starProjection F - y‖) ^ 2 := by
    exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).2
      (hcontract.trans htriangle)
  rw [hpyth] at hsquare
  nlinarith [sq_nonneg ‖F - S.starProjection F‖,
    sq_nonneg ‖S.starProjection F - y‖]

section Beta

variable {mu : Measure BetaNat} [IsProbabilityMeasure mu]

/-- The projection of an indicator onto the compact-orbit factor admits
uniformly `[0,1]`-valued continuous factor approximants. -/
theorem exists_clipped_factor_close_starProjection
    (A : Set ℕ)
    (U : BetaL2 mu ≃ₗᵢ[ℂ] BetaL2 mu) (c : BetaL2 mu)
    (hc : TotallyBounded (Set.range fun n : ℕ ↦ (U ^ n) c))
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ psi : compactOrbit U c →ᵇ ℂ,
      ‖(compactOrbitFactorClosed U c hc).toSubmodule.starProjection
          (betaIndicatorL2 mu A) -
        compactOrbitFactorL2 U c hc
          (clipCompactOrbitObservable U c hc psi)‖ < epsilon := by
  let S : Submodule ℂ (BetaL2 mu) :=
    (compactOrbitFactorClosed U c hc).toSubmodule
  let F : BetaL2 mu := betaIndicatorL2 mu A
  let b : BetaL2 mu := S.starProjection F
  let M : ℝ := ‖F - b‖
  let delta : ℝ := min 1 (epsilon ^ 2 / (4 * (M + 1)))
  have hM : 0 ≤ M := norm_nonneg _
  have hden : 0 < 4 * (M + 1) := by positivity
  have hdelta : 0 < delta := by
    dsimp [delta]
    positivity
  have hdelta_one : delta ≤ 1 := min_le_left _ _
  have hdelta_quot : delta ≤ epsilon ^ 2 / (4 * (M + 1)) :=
    min_le_right _ _
  have hbS : b ∈ S := S.starProjection_apply_mem F
  have hbclosure : b ∈ closure
      ((compactOrbitFactorSubmodule U c hc : Submodule ℂ (BetaL2 mu)) :
        Set (BetaL2 mu)) := by
    change b ∈ (compactOrbitFactorSubmodule U c hc).topologicalClosure at hbS
    rwa [← SetLike.mem_coe, Submodule.topologicalClosure_coe] at hbS
  obtain ⟨y, hy, hby⟩ := Metric.mem_closure_iff.mp hbclosure delta hdelta
  rcases hy with ⟨psi, rfl⟩
  refine ⟨psi, ?_⟩
  let y : BetaL2 mu := compactOrbitFactorL2 U c hc psi
  let yc : BetaL2 mu := compactOrbitFactorL2 U c hc
    (clipCompactOrbitObservable U c hc psi)
  have hdb : ‖b - y‖ < delta := by
    simpa only [b, y, dist_eq_norm] using hby
  have hycS : yc ∈ S := by
    apply (compactOrbitFactorSubmodule U c hc).le_topologicalClosure
    exact ⟨clipCompactOrbitObservable U c hc psi, rfl⟩
  have hcontract : ‖F - yc‖ ≤ ‖F - y‖ := by
    exact norm_indicator_sub_clip_factor_le A U c hc psi
  have hquant := norm_sub_starProjection_sq_le S F y yc hycS hcontract
  have hqbound : ‖b - yc‖ ^ 2 ≤ 2 * M * ‖b - y‖ + ‖b - y‖ ^ 2 := by
    simpa only [b, M] using hquant
  have hsmall : 2 * M * ‖b - y‖ + ‖b - y‖ ^ 2 <
      (2 * M + 1) * delta := by
    have hdb0 : 0 ≤ ‖b - y‖ := norm_nonneg _
    have hdelta0 : 0 ≤ delta := hdelta.le
    nlinarith
  have hratio : (2 * M + 1) *
      (epsilon ^ 2 / (4 * (M + 1))) < epsilon ^ 2 := by
    calc
      (2 * M + 1) * (epsilon ^ 2 / (4 * (M + 1))) =
          ((2 * M + 1) * epsilon ^ 2) / (4 * (M + 1)) := by ring
      _ < epsilon ^ 2 := (div_lt_iff₀ hden).2 (by
        have hepsq : 0 < epsilon ^ 2 := sq_pos_of_pos hepsilon
        nlinarith)
  have hdeltaRatio : (2 * M + 1) * delta < epsilon ^ 2 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left hdelta_quot (by positivity)) hratio
  have hsq : ‖b - yc‖ ^ 2 < epsilon ^ 2 :=
    lt_of_le_of_lt hqbound (hsmall.trans hdeltaRatio)
  change ‖b - yc‖ < epsilon
  exact (sq_lt_sq₀ (norm_nonneg _) hepsilon.le).mp hsq

end Beta

end

end Erdos109

open CompactlySupported Filter Function MeasureTheory Set
open scoped BoundedContinuousFunction ComplexConjugate ENNReal NNReal Pointwise Topology

namespace Erdos109

noncomputable section

noncomputable local instance : MeasurableSpace BetaNat := borel BetaNat
local instance : BorelSpace BetaNat := ⟨rfl⟩

/-- Clipping to the real interval `[0,1]` is a contraction on `ℂ`. -/
theorem lipschitzWith_clipComplex01 : LipschitzWith 1 clipComplex01 := by
  have hr : LipschitzWith 1 (fun x : ℝ ↦ min 1 (max 0 x)) :=
    (LipschitzWith.id.const_max 0).const_min 1
  apply LipschitzWith.of_dist_le_mul
  intro z w
  simp only [NNReal.coe_one, one_mul]
  rw [dist_eq_norm, dist_eq_norm]
  calc
    ‖clipComplex01 z - clipComplex01 w‖ =
        ‖min 1 (max 0 z.re) - min 1 (max 0 w.re)‖ := by
          rw [clipComplex01, clipComplex01, ← Complex.ofReal_sub,
            Complex.norm_real]
    _ = dist (min 1 (max 0 z.re)) (min 1 (max 0 w.re)) := by
          rw [dist_eq_norm]
    _ ≤ dist z.re w.re := by simpa using hr.dist_le_mul z.re w.re
    _ = |(z - w).re| := by simp [Real.dist_eq]
    _ ≤ ‖z - w‖ := Complex.abs_re_le_norm (z - w)

@[simp] theorem clipComplex01_zero : clipComplex01 0 = 0 := by
  simp [clipComplex01]

/-- Pointwise clipping, defined intrinsically on an `L²` class. -/
noncomputable def clipComplexLp {mu : Measure BetaNat} [IsFiniteMeasure mu]
    (f : BetaL2 mu) : BetaL2 mu :=
  lipschitzWith_clipComplex01.compLp clipComplex01_zero f

theorem coeFn_clipComplexLp {mu : Measure BetaNat} [IsFiniteMeasure mu]
    (f : BetaL2 mu) :
    (clipComplexLp f : BetaNat → ℂ) =ᵐ[mu] fun p ↦ clipComplex01 (f p) := by
  filter_upwards
    [lipschitzWith_clipComplex01.coeFn_compLp clipComplex01_zero f] with p hp
  simpa only [clipComplexLp, Function.comp_apply] using hp

/-- Clipping commutes with the Koopman shift. -/
theorem betaKoopman_clipComplexLp {mu : Measure BetaNat} [IsFiniteMeasure mu]
    (hmu : MeasurePreserving betaShift mu mu) (f : BetaL2 mu) :
    betaKoopman hmu (clipComplexLp f) = clipComplexLp (betaKoopman hmu f) := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving (clipComplexLp f) hmu,
    hmu.quasiMeasurePreserving.ae_eq_comp (coeFn_clipComplexLp f),
    coeFn_clipComplexLp (betaKoopman hmu f),
    Lp.coeFn_compMeasurePreserving f hmu] with p hleft hclipcomp hright hfcomp
  rw [betaKoopman_apply, hleft, hclipcomp, hright, betaKoopman_apply, hfcomp]
  rfl

theorem betaKoopman_pow_clipComplexLp {mu : Measure BetaNat} [IsFiniteMeasure mu]
    (hmu : MeasurePreserving betaShift mu mu) (f : BetaL2 mu) (n : ℕ) :
    (betaKoopman hmu ^ n) (clipComplexLp f) =
      clipComplexLp ((betaKoopman hmu ^ n) f) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ']
      change betaKoopman hmu ((betaKoopman hmu ^ n) (clipComplexLp f)) = _
      rw [ih, betaKoopman_clipComplexLp]
      congr 1

/-- A Lipschitz pointwise transform preserves a totally bounded Koopman orbit. -/
theorem totallyBounded_clipComplexLp_orbit
    {mu : Measure BetaNat} [IsProbabilityMeasure mu]
    (hmu : MeasurePreserving betaShift mu mu) (f : BetaL2 mu)
    (hf : TotallyBounded (Set.range fun n : ℕ ↦ (betaKoopman hmu ^ n) f)) :
    TotallyBounded
      (Set.range fun n : ℕ ↦ (betaKoopman hmu ^ n) (clipComplexLp f)) := by
  have himage := hf.image
    (lipschitzWith_clipComplex01.lipschitzWith_compLp clipComplex01_zero).uniformContinuous
  apply himage.subset
  rintro y ⟨n, rfl⟩
  refine ⟨(betaKoopman hmu ^ n) f, Set.mem_range_self n, ?_⟩
  exact (betaKoopman_pow_clipComplexLp hmu f n).symm

section Projection

variable {mu : Measure BetaNat} [IsProbabilityMeasure mu]

/-- Clipping the indicator's compact component does not increase the error. -/
theorem norm_indicator_sub_clipComplexLp_le
    (A : Set ℕ) (v : BetaL2 mu) :
    ‖betaIndicatorL2 mu A - clipComplexLp v‖ ≤
      ‖betaIndicatorL2 mu A - v‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [Lp.coeFn_sub (betaIndicatorL2 mu A) (clipComplexLp v),
    Lp.coeFn_sub (betaIndicatorL2 mu A) v,
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) mu (betaIndicatorComplex A),
    coeFn_clipComplexLp v] with p hleft hright hA hclip
  rw [hleft, hright]
  change ‖(betaIndicatorL2 mu A : BetaNat → ℂ) p - (clipComplexLp v : BetaNat → ℂ) p‖ ≤
    ‖(betaIndicatorL2 mu A : BetaNat → ℂ) p - (v : BetaNat → ℂ) p‖
  rw [betaIndicatorL2, hA, hclip]
  exact norm_sub_clipComplex01_le_of_eq_zero_or_one
    (betaIndicatorComplex_eq_zero_or_one A p) _

/-- The compact component of a Boolean indicator is itself `[0,1]`-valued. -/
theorem clipComplexLp_unitaryCompactPart_indicator
    (hmu : MeasurePreserving betaShift mu mu) (A : Set ℕ) :
    clipComplexLp (unitaryCompactPart (betaKoopman hmu) (betaIndicatorL2 mu A)) =
      unitaryCompactPart (betaKoopman hmu) (betaIndicatorL2 mu A) := by
  let U := betaKoopman hmu
  let F := betaIndicatorL2 mu A
  let S := (unitaryKronecker U).toSubmodule
  let a := unitaryCompactPart U F
  let : S.HasOrthogonalProjection := by
    infer_instance
  have haAP : a ∈ unitaryAlmostPeriodicSubmodule U := by
    change TotallyBounded (Set.range fun n : ℕ ↦ (U ^ n) a)
    exact totallyBounded_unitaryCompactPart_orbit U F
  have hacAP : clipComplexLp a ∈ unitaryAlmostPeriodicSubmodule U := by
    change TotallyBounded (Set.range fun n : ℕ ↦ (U ^ n) (clipComplexLp a))
    exact totallyBounded_clipComplexLp_orbit hmu a haAP
  have hacS : clipComplexLp a ∈ S := by
    change clipComplexLp a ∈ unitaryKronecker U
    rw [unitaryAlmostPeriodic_eq_kronecker] at hacAP
    exact hacAP
  have hcontract : ‖F - clipComplexLp a‖ ≤ ‖F - a‖ := by
    exact norm_indicator_sub_clipComplexLp_le A a
  have hproj : S.starProjection F = a := by
    change ((unitaryKronecker U).toSubmodule).starProjection F =
      unitaryCompactPart U F
    rfl
  have hquant := norm_sub_starProjection_sq_le S F a (clipComplexLp a) hacS hcontract
  rw [hproj] at hquant
  have hzero : ‖a - clipComplexLp a‖ = 0 := by
    have hnonneg : 0 ≤ ‖a - clipComplexLp a‖ ^ 2 := sq_nonneg _
    have : ‖a - clipComplexLp a‖ ^ 2 ≤ 0 := by simpa using hquant
    nlinarith
  change clipComplexLp a = a
  exact (sub_eq_zero.mp (norm_eq_zero.mp hzero)).symm

end Projection

end

end Erdos109

open CompactlySupported Filter Function MeasureTheory Set
open scoped BoundedContinuousFunction ComplexConjugate ENNReal NNReal Pointwise Topology

namespace Erdos109

noncomputable section

noncomputable local instance : MeasurableSpace BetaNat := borel BetaNat
local instance : BorelSpace BetaNat := ⟨rfl⟩

/-- A zero-density arithmetic set has a null clopen event in every empirical
ultralimit along the same prefixes. -/
theorem measure_betaEvent_eq_zero_of_density_zero
    (N : ℕ → ℕ) (hNpos : ∀ k, 0 < N k)
    (q : Ultrafilter ℕ) (hq : (q : Filter ℕ) ≤ atTop)
    (mu : ProbabilityMeasure BetaNat)
    (hmu : Tendsto (fun k ↦ betaEmpirical (N k) (hNpos k))
      (q : Filter ℕ) (𝓝 mu))
    (E : Set ℕ)
    (hE : HasDensityAlong (fun k ↦ Finset.range (N k)) E 0) :
    (mu : Measure BetaNat) (betaEvent E) = 0 := by
  let b : BetaNat →ᵇ ℝ :=
    BoundedContinuousFunction.mkOfCompact (betaIndicator E)
  have hmu_b :=
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hmu) b
  have hemp : Tendsto
      (fun k ↦ ∫ p, b p
        ∂((betaEmpirical (N k) (hNpos k) : ProbabilityMeasure BetaNat) :
          Measure BetaNat))
      (q : Filter ℕ) (𝓝 0) := by
    have hEq (k : ℕ) :
        (∫ p, b p
          ∂((betaEmpirical (N k) (hNpos k) : ProbabilityMeasure BetaNat) :
            Measure BetaNat)) =
          finsetDensity (Finset.range (N k)) E := by
      exact integral_betaEmpirical_indicator (N k) (hNpos k) E
    exact (hE.mono_left hq).congr'
      (Eventually.of_forall fun k ↦ (hEq k).symm)
  have hint : (∫ p, b p ∂(mu : Measure BetaNat)) = 0 :=
    tendsto_nhds_unique hmu_b hemp
  have hevent : (∫ p, b p ∂(mu : Measure BetaNat)) =
      (mu : Measure BetaNat).real (betaEvent E) := by
    change (∫ p, betaIndicator E p ∂(mu : Measure BetaNat)) = _
    rw [betaIndicator_eq_indicator_betaEvent E,
      integral_indicator_const (1 : ℝ) (betaEvent_isClopen E).2.measurableSet]
    simp
  rw [hevent] at hint
  exact (measureReal_eq_zero_iff
    (μ := (mu : Measure BetaNat)) (s := betaEvent E)).mp hint

/-- Every point in the support of an empirical prefix limit is essential:
it contains every density-one set along those prefixes. -/
theorem support_point_le_densityOneFilter
    (N : ℕ → ℕ) (hNpos : ∀ k, 0 < N k)
    (q : Ultrafilter ℕ) (hq : (q : Filter ℕ) ≤ atTop)
    (mu : ProbabilityMeasure BetaNat)
    (hmu : Tendsto (fun k ↦ betaEmpirical (N k) (hNpos k))
      (q : Filter ℕ) (𝓝 mu))
    (p : BetaNat) (hp : p ∈ (mu : Measure BetaNat).support) :
    (p : Filter ℕ) ≤ densityOneFilter (fun k ↦ Finset.range (N k)) := by
  intro E hE
  change HasDensityAlong (fun k ↦ Finset.range (N k)) Eᶜ 0 at hE
  by_contra hpE
  have hpEc : Eᶜ ∈ (p : Filter ℕ) :=
    (Ultrafilter.compl_mem_iff_notMem (f := p)).mpr hpE
  have hpEvent : p ∈ betaEvent Eᶜ := by
    change betaMembership Eᶜ p = true
    exact (betaMembership_eq_true_iff Eᶜ p).mpr hpEc
  have hnull : (mu : Measure BetaNat) (betaEvent Eᶜ) = 0 :=
    measure_betaEvent_eq_zero_of_density_zero N hNpos q hq mu hmu Eᶜ hE
  have hopen : IsOpen (betaEvent Eᶜ) := (betaEvent_isClopen Eᶜ).2
  have hpos : 0 < (mu : Measure BetaNat) (betaEvent Eᶜ) :=
    (Measure.mem_support_iff_forall p).mp hp _ (hopen.mem_nhds hpEvent)
  exact hpos.ne' hnull

end

end Erdos109

open CompactlySupported Filter Function MeasureTheory Set
open scoped BoundedContinuousFunction ComplexConjugate ENNReal NNReal Pointwise Topology

namespace Erdos109

noncomputable section

/-- Reverse Fatou for a nonzero finite measure, expressed using the
normalized average of that measure. -/
theorem exists_notMem_null_limsup_ge_of_tendsto_average
    {alpha : Type*} [MeasurableSpace alpha] [Nonempty alpha]
    (mu : Measure alpha) [IsFiniteMeasure mu] [NeZero mu]
    (F : ℕ → alpha → ℝ) (C : ℝ) (hC : 0 < C)
    (hFmeas : ∀ n, Measurable (F n))
    (hFlower : ∀ n x, -C ≤ F n x)
    (hFupper : ∀ n x, F n x ≤ C)
    (r : ℝ)
    (hlim : Tendsto (fun n ↦ ⨍ x, F n x ∂mu) atTop (𝓝 r))
    (Z : Set alpha) (hZ : mu Z = 0) :
    ∃ x ∉ Z, r ≤ limsup (fun n ↦ F n x) atTop := by
  let muf : FiniteMeasure alpha := ⟨mu, inferInstance⟩
  let nu : ProbabilityMeasure alpha := muf.normalize
  have hmuf_ne : muf ≠ 0 := by
    intro hzero
    have : mu = 0 := congrArg FiniteMeasure.toMeasure hzero
    exact (NeZero.ne mu) this
  have hnuZ : (nu : Measure alpha) Z = 0 := by
    rw [muf.toMeasure_normalize_eq_of_nonzero hmuf_ne]
    simp only [Measure.coe_smul, Pi.smul_apply]
    have hmufZ : (muf : Measure alpha) Z = 0 := by
      simpa only [muf, FiniteMeasure.toMeasure_mk] using hZ
    rw [hmufZ, smul_zero]
  have hlim' : Tendsto
      (fun n ↦ ∫ x, F n x ∂(nu : Measure alpha)) atTop (𝓝 r) := by
    exact hlim.congr' (Eventually.of_forall fun n ↦ by
      have hav := muf.average_eq_integral_normalize hmuf_ne (F n)
      change average mu (F n) = ∫ x, F n x ∂(nu : Measure alpha)
      simpa only [show (muf : Measure alpha) = mu from rfl,
        show muf.normalize = nu from rfl] using hav)
  exact exists_notMem_null_limsup_ge_of_tendsto_integral
    (nu : Measure alpha) F C hC hFmeas hFlower hFupper r hlim' Z hnuZ

/-- A bounded family with uniformly lower-bounded averages has, after one
strict subsequence, a pointwise limsup with the same lower bound.  A null
exceptional set can be avoided. -/
theorem exists_subseq_notMem_null_limsup_ge_of_average_lower
    {alpha : Type*} [MeasurableSpace alpha] [Nonempty alpha]
    (mu : Measure alpha) [IsFiniteMeasure mu] [NeZero mu]
    (F : ℕ → alpha → ℝ) (C : ℝ) (hC : 0 < C)
    (hFmeas : ∀ n, Measurable (F n))
    (hFlower : ∀ n x, -C ≤ F n x)
    (hFupper : ∀ n x, F n x ≤ C)
    (r : ℝ) (hlower : ∀ n, r ≤ ⨍ x, F n x ∂mu)
    (Z : Set alpha) (hZ : mu Z = 0) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧
      ∃ x ∉ Z, r ≤ limsup (fun n ↦ F (phi n) x) atTop := by
  let a : ℕ → ℝ := fun n ↦ ⨍ x, F n x ∂mu
  have haIcc (n : ℕ) : a n ∈ Set.Icc (-C) C := by
    let muf : FiniteMeasure alpha := ⟨mu, inferInstance⟩
    let nu : ProbabilityMeasure alpha := muf.normalize
    have hmuf_ne : muf ≠ 0 := by
      intro hzero
      have : mu = 0 := congrArg FiniteMeasure.toMeasure hzero
      exact (NeZero.ne mu) this
    have hav : a n = ∫ x, F n x ∂(nu : Measure alpha) := by
      exact muf.average_eq_integral_normalize hmuf_ne (F n)
    rw [hav]
    have hFn : Integrable (F n) (nu : Measure alpha) := by
      refine ⟨(hFmeas n).aestronglyMeasurable,
        HasFiniteIntegral.of_bounded (C := C) ?_⟩
      exact ae_of_all _ fun x ↦ abs_le.mpr ⟨hFlower n x, hFupper n x⟩
    constructor
    · simpa using integral_mono_ae (integrable_const (-C)) hFn
        (ae_of_all _ fun x ↦ hFlower n x)
    · simpa using integral_mono_ae hFn (integrable_const C)
        (ae_of_all _ fun x ↦ hFupper n x)
  obtain ⟨s, hs, phi, hphi, hlim⟩ :=
    tendsto_subseq_of_bounded
      ((isCompact_Icc : IsCompact (Set.Icc (-C) C)).isBounded) haIcc
  have hrs : r ≤ s := ge_of_tendsto hlim
    (Eventually.of_forall fun n ↦ hlower (phi n))
  obtain ⟨x, hxZ, hx⟩ :=
    exists_notMem_null_limsup_ge_of_tendsto_average mu
      (fun n x ↦ F (phi n) x) C hC
      (fun n ↦ hFmeas (phi n))
      (fun n x ↦ hFlower (phi n) x)
      (fun n x ↦ hFupper (phi n) x)
      s (by simpa only [a, Function.comp_def] using hlim) Z hZ
  exact ⟨phi, hphi, x, hxZ, hrs.trans hx⟩

end

end Erdos109

open CompactlySupported Filter Function MeasureTheory Set
open scoped BoundedContinuousFunction ComplexConjugate ENNReal NNReal Pointwise Topology

namespace Erdos109

noncomputable section

noncomputable local instance : MeasurableSpace BetaNat := borel BetaNat
local instance : BorelSpace BetaNat := ⟨rfl⟩

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A continuous tent function supported on the ball of radius `r`. -/
noncomputable def compactReturnBump (r d : ℝ) : ℝ :=
  max 0 (1 - d / r)

theorem continuous_compactReturnBump (r : ℝ) :
    Continuous (compactReturnBump r) := by
  unfold compactReturnBump
  fun_prop

theorem compactReturnBump_nonneg (r d : ℝ) :
    0 ≤ compactReturnBump r d := le_max_left _ _

theorem compactReturnBump_le_one {r d : ℝ} (hr : 0 < r) (hd : 0 ≤ d) :
    compactReturnBump r d ≤ 1 := by
  rw [compactReturnBump, max_le_iff]
  constructor
  · norm_num
  · have : 0 ≤ d / r := div_nonneg hd hr.le
    linarith

theorem compactReturnBump_eq_zero_of_le {r d : ℝ} (hr : 0 < r) (h : r ≤ d) :
    compactReturnBump r d = 0 := by
  rw [compactReturnBump, max_eq_left]
  rw [sub_nonpos, le_div_iff₀ hr]
  simpa using h

theorem compactReturnBump_pos_iff {r d : ℝ} (hr : 0 < r) :
    0 < compactReturnBump r d ↔ d < r := by
  rw [compactReturnBump, lt_max_iff]
  simp only [lt_self_iff_false, false_or]
  rw [sub_pos, div_lt_one hr]

theorem one_half_le_compactReturnBump {r d : ℝ} (hr : 0 < r)
    (hd : d ≤ r / 2) :
    (1 / 2 : ℝ) ≤ compactReturnBump r d := by
  rw [compactReturnBump]
  apply le_max_of_le_right
  rw [le_sub_iff_add_le]
  have hdiv : d / r ≤ (1 / 2 : ℝ) := by
    rw [div_le_iff₀ hr]
    nlinarith
  linarith

/-- The smooth compact-return weight sampled along a unitary orbit. -/
noncomputable def compactReturnWeightCode
    (U : H ≃ₗᵢ[ℂ] H) (c : H) (r : ℝ) (n : ℕ) : ℝ :=
  compactReturnBump r (dist ((U ^ n) c) c)

theorem compactReturnWeightCode_nonneg
    (U : H ≃ₗᵢ[ℂ] H) (c : H) (r : ℝ) (n : ℕ) :
    0 ≤ compactReturnWeightCode U c r n :=
  compactReturnBump_nonneg _ _

theorem compactReturnWeightCode_le_one
    (U : H ≃ₗᵢ[ℂ] H) (c : H) {r : ℝ} (hr : 0 < r) (n : ℕ) :
    compactReturnWeightCode U c r n ≤ 1 :=
  compactReturnBump_le_one hr dist_nonneg

theorem abs_compactReturnWeightCode_le_one
    (U : H ≃ₗᵢ[ℂ] H) (c : H) {r : ℝ} (hr : 0 < r) (n : ℕ) :
    |compactReturnWeightCode U c r n| ≤ 1 := by
  rw [abs_of_nonneg (compactReturnWeightCode_nonneg U c r n)]
  exact compactReturnWeightCode_le_one U c hr n

/-- Stone--Čech extension of the smooth return weight. -/
noncomputable def compactReturnWeight
    (U : H ≃ₗᵢ[ℂ] H) (c : H) (r : ℝ) (hr : 0 < r) : C(BetaNat, ℝ) :=
  betaExtendBounded (compactReturnWeightCode U c r) 1
    (abs_compactReturnWeightCode_le_one U c hr)

@[simp] theorem compactReturnWeight_pure
    (U : H ≃ₗᵢ[ℂ] H) (c : H) (r : ℝ) (hr : 0 < r) (n : ℕ) :
    compactReturnWeight U c r hr (pure n) = compactReturnWeightCode U c r n := by
  simp [compactReturnWeight]

theorem compactReturnWeight_nonneg
    (U : H ≃ₗᵢ[ℂ] H) (c : H) (r : ℝ) (hr : 0 < r) (p : BetaNat) :
    0 ≤ compactReturnWeight U c r hr p := by
  let W := compactReturnWeight U c r hr
  have hclosed : IsClosed {p : BetaNat | 0 ≤ W p} :=
    isClosed_Ici.preimage W.continuous
  have hsub : Set.range (pure : ℕ → BetaNat) ⊆ {p | 0 ≤ W p} := by
    rintro _ ⟨n, rfl⟩
    simpa [W] using compactReturnWeightCode_nonneg U c r n
  apply closure_minimal hsub hclosed
  rw [(denseRange_pure : DenseRange (pure : ℕ → BetaNat)).closure_range]
  exact Set.mem_univ p

theorem compactReturnWeight_le_one
    (U : H ≃ₗᵢ[ℂ] H) (c : H) (r : ℝ) (hr : 0 < r) (p : BetaNat) :
    compactReturnWeight U c r hr p ≤ 1 := by
  exact (abs_le.mp (abs_betaExtendBounded_le
    (compactReturnWeightCode U c r) 1
    (abs_compactReturnWeightCode_le_one U c hr) p)).2

theorem compactReturnWeight_pos_implies_return_mem
    (U : H ≃ₗᵢ[ℂ] H) (c : H) (r : ℝ) (hr : 0 < r) (p : BetaNat)
    (hp : 0 < compactReturnWeight U c r hr p) :
    {n : ℕ | dist ((U ^ n) c) c < r} ∈ (p : Filter ℕ) := by
  let R : Set ℕ := {n : ℕ | dist ((U ^ n) c) c < r}
  by_contra hR
  have hRc : Rᶜ ∈ (p : Filter ℕ) :=
    (Ultrafilter.compl_mem_iff_notMem (f := p)).mpr hR
  have hzero : compactReturnWeight U c r hr p = 0 := by
    let z : Set.Icc (-(1 : ℝ)) 1 := ⟨0, by norm_num⟩
    let fs : ℕ → Set.Icc (-(1 : ℝ)) 1 := fun n ↦
      ⟨compactReturnWeightCode U c r n,
        (abs_le.mp (abs_compactReturnWeightCode_le_one U c hr n))⟩
    have hfs : fs =ᶠ[p] fun _ ↦ z := by
      filter_upwards [hRc] with n hn
      apply Subtype.ext
      have hnnot : ¬ dist ((U ^ n) c) c < r := by
        simpa only [R, Set.mem_compl_iff, Set.mem_setOf_eq] using hn
      exact compactReturnBump_eq_zero_of_le hr (le_of_not_gt hnnot)
    have hext : Ultrafilter.extend fs p = z := by
      rw [ultrafilter_extend_eq_iff]
      exact tendsto_const_nhds.congr' hfs.symm
    change (Ultrafilter.extend fs p : Set.Icc (-(1 : ℝ)) 1).1 = 0
    exact congrArg Subtype.val hext
  linarith

/-- The same return bump as a bounded continuous observable on the compact
orbit closure. -/
noncomputable def compactReturnObservable
    (U : H ≃ₗᵢ[ℂ] H) (c : H)
    (hc : TotallyBounded (Set.range fun n : ℕ ↦ (U ^ n) c))
    (r : ℝ) (hr : 0 < r) : compactOrbit U c →ᵇ ℂ := by
  letI : CompactSpace (compactOrbit U c) :=
    isCompact_iff_compactSpace.mp (isCompact_compactOrbit U c hc)
  exact BoundedContinuousFunction.mkOfCompact
    ⟨fun z ↦ ((compactReturnBump r (dist (z : H) c) : ℝ) : ℂ), by
      exact Complex.continuous_ofReal.comp
        ((continuous_compactReturnBump r).comp
          (continuous_subtype_val.dist continuous_const))⟩

@[simp] theorem compactReturnObservable_orbitPoint
    (U : H ≃ₗᵢ[ℂ] H) (c : H)
    (hc : TotallyBounded (Set.range fun n : ℕ ↦ (U ^ n) c))
    (r : ℝ) (hr : 0 < r) (n : ℕ) :
    compactReturnObservable U c hc r hr (compactOrbitPoint U c n) =
      (compactReturnWeightCode U c r n : ℂ) := rfl

/-- The real Stone--Čech return weight agrees with the complex compact-orbit
factor extension. -/
theorem compactOrbitExtension_returnObservable
    (U : H ≃ₗᵢ[ℂ] H) (c : H)
    (hc : TotallyBounded (Set.range fun n : ℕ ↦ (U ^ n) c))
    (r : ℝ) (hr : 0 < r) :
    compactOrbitExtension U c hc (compactReturnObservable U c hc r hr) =
      ⟨fun p ↦ (compactReturnWeight U c r hr p : ℂ),
        Complex.continuous_ofReal.comp (compactReturnWeight U c r hr).continuous⟩ := by
  apply ContinuousMap.ext
  apply congrFun
  apply (denseRange_pure : DenseRange (pure : ℕ → BetaNat)).equalizer
  · exact (compactOrbitExtension U c hc
      (compactReturnObservable U c hc r hr)).continuous
  · exact Complex.continuous_ofReal.comp (compactReturnWeight U c r hr).continuous
  funext n
  simp [compactOrbitCode]

section Beta

variable {mu : Measure BetaNat} [IsProbabilityMeasure mu]

/-- The `L²` vector represented by the smooth return weight belongs to the
compact-orbit factor. -/
theorem returnWeightL2_mem_compactOrbitFactor
    (U : BetaL2 mu ≃ₗᵢ[ℂ] BetaL2 mu) (c : BetaL2 mu)
    (hc : TotallyBounded (Set.range fun n : ℕ ↦ (U ^ n) c))
    (r : ℝ) (hr : 0 < r) :
    ContinuousMap.toLp 2 mu ℂ
        ⟨fun p ↦ (compactReturnWeight U c r hr p : ℂ),
          Complex.continuous_ofReal.comp (compactReturnWeight U c r hr).continuous⟩ ∈
      compactOrbitFactorSubmodule U c hc := by
  refine ⟨compactReturnObservable U c hc r hr, ?_⟩
  simp only [compactOrbitFactorL2, compactOrbitExtension_returnObservable]

/-- For a Koopman compact orbit, the smooth return weight lies in the
Kronecker subspace. -/
theorem returnWeightL2_mem_kronecker
    (hmu : MeasurePreserving betaShift mu mu)
    (c : BetaL2 mu)
    (hc : TotallyBounded
      (Set.range fun n : ℕ ↦ (betaKoopman hmu ^ n) c))
    (r : ℝ) (hr : 0 < r) :
    ContinuousMap.toLp 2 mu ℂ
        ⟨fun p ↦ (compactReturnWeight (betaKoopman hmu) c r hr p : ℂ),
          Complex.continuous_ofReal.comp
            (compactReturnWeight (betaKoopman hmu) c r hr).continuous⟩ ∈
      unitaryKronecker (betaKoopman hmu) := by
  apply compactOrbitFactorClosed_le_kronecker hmu c hc
  apply (compactOrbitFactorSubmodule (betaKoopman hmu) c hc).le_topologicalClosure
  exact returnWeightL2_mem_compactOrbitFactor
    (betaKoopman hmu) c hc r hr

end Beta

end

end Erdos109

open CompactlySupported Filter Function MeasureTheory Set
open scoped BoundedContinuousFunction ComplexConjugate ENNReal NNReal Pointwise Topology

namespace Erdos109

noncomputable section

noncomputable local instance : MeasurableSpace BetaNat := borel BetaNat
local instance : BorelSpace BetaNat := ⟨rfl⟩

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem iterate_linearIsometryEquiv_apply
    (U : H ≃ₗᵢ[ℂ] H) (n : ℕ) (x : H) :
    (fun y : H ↦ U y)^[n] x = (U ^ n) x := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, pow_succ']
      rfl

/-- Smooth compact return weights have positive lower mean along every
growing sequence of prefixes. -/
theorem positiveLowerMean_compactReturnWeightCode
    (U : H ≃ₗᵢ[ℂ] H) (c : H)
    (hc : TotallyBounded (Set.range fun n : ℕ ↦ (U ^ n) c))
    (r : ℝ) (hr : 0 < r)
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) :
    ∃ d : ℝ, 0 < d ∧ ∀ᶠ k in atTop,
      d ≤ realFinsetMean (Finset.range (N k))
        (compactReturnWeightCode U c r) := by
  let R : Set ℕ := {n | dist ((U ^ n) c) c < r / 2}
  have hRsynd : Syndetic R := by
    have hs := syndetic_returnTimes_of_totallyBounded
      (fun y : H ↦ U y) U.isometry c (by
        simpa only [iterate_linearIsometryEquiv_apply] using hc)
      (by positivity : 0 < r / 2)
    simpa only [R, iterate_linearIsometryEquiv_apply] using hs
  obtain ⟨d, hd, hRd⟩ :=
    positiveLowerDensity_range_of_syndetic hRsynd hN
  refine ⟨d / 2, by positivity, ?_⟩
  filter_upwards [hRd] with k hk
  have hpoint (n : ℕ) :
      (1 / 2 : ℝ) * realIndicator R n ≤
        compactReturnWeightCode U c r n := by
    by_cases hn : n ∈ R
    · rw [realIndicator_apply_mem hn, mul_one]
      exact one_half_le_compactReturnBump hr (le_of_lt hn)
    · rw [realIndicator_apply_notMem hn, mul_zero]
      exact compactReturnWeightCode_nonneg U c r n
  have hmean : realFinsetMean (Finset.range (N k))
      (fun n ↦ (1 / 2 : ℝ) * realIndicator R n) ≤
      realFinsetMean (Finset.range (N k))
        (compactReturnWeightCode U c r) := by
    unfold realFinsetMean
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    exact Finset.sum_le_sum fun n _ ↦ hpoint n
  calc
    d / 2 = (1 / 2 : ℝ) * d := by ring
    _ ≤ (1 / 2 : ℝ) * finsetDensity (Finset.range (N k)) R := by
      gcongr
    _ = realFinsetMean (Finset.range (N k))
        (fun n ↦ (1 / 2 : ℝ) * realIndicator R n) := by
      rw [realFinsetMean, ← Finset.mul_sum, sum_realIndicator,
        finsetDensity]
      ring
    _ ≤ _ := hmean

/-- The smooth return weight has strictly positive integral in an empirical
prefix ultralimit. -/
theorem integral_compactReturnWeight_pos
    (N : ℕ → ℕ) (hNpos : ∀ k, 0 < N k) (hNtop : Tendsto N atTop atTop)
    (q : Ultrafilter ℕ) (hq : (q : Filter ℕ) ≤ atTop)
    (mu : ProbabilityMeasure BetaNat)
    (hmu : Tendsto (fun k ↦ betaEmpirical (N k) (hNpos k))
      (q : Filter ℕ) (𝓝 mu))
    (U : H ≃ₗᵢ[ℂ] H) (c : H)
    (hc : TotallyBounded (Set.range fun n : ℕ ↦ (U ^ n) c))
    (r : ℝ) (hr : 0 < r) :
    0 < ∫ p, compactReturnWeight U c r hr p ∂(mu : Measure BetaNat) := by
  obtain ⟨d, hd, hdmean⟩ :=
    positiveLowerMean_compactReturnWeightCode U c hc r hr N hNtop
  let W : BetaNat →ᵇ ℝ :=
    BoundedContinuousFunction.mkOfCompact (compactReturnWeight U c r hr)
  have hmuW :=
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hmu) W
  have hfinite (k : ℕ) :
      (∫ p, W p
        ∂((betaEmpirical (N k) (hNpos k) : ProbabilityMeasure BetaNat) :
          Measure BetaNat)) =
        realFinsetMean (Finset.range (N k))
          (compactReturnWeightCode U c r) := by
    change (∫ p, compactReturnWeight U c r hr p
      ∂((betaEmpirical (N k) (hNpos k) : ProbabilityMeasure BetaNat) :
        Measure BetaNat)) = _
    rw [integral_betaEmpirical (N k) (hNpos k)
      (compactReturnWeight U c r hr)]
    simp only [
      compactReturnWeight_pure, realFinsetMean, Finset.card_range]
  have hlower : d ≤ ∫ p, W p ∂(mu : Measure BetaNat) := by
    apply ge_of_tendsto hmuW
    filter_upwards [hq hdmean] with k hk
    simpa only [hfinite] using hk
  exact hd.trans_le hlower

end

end Erdos109

open CompactlySupported Filter Function MeasureTheory Set
open scoped BoundedContinuousFunction ComplexConjugate ENNReal NNReal Pointwise Topology

namespace Erdos109

noncomputable section

noncomputable local instance : MeasurableSpace BetaNat := borel BetaNat
local instance : BorelSpace BetaNat := ⟨rfl⟩

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The empirical limit measure tilted by a smooth compact-return weight. -/
noncomputable def compactReturnWeightedMeasure
    (mu : Measure BetaNat)
    (U : H ≃ₗᵢ[ℂ] H) (c : H) (r : ℝ) (hr : 0 < r) : Measure BetaNat :=
  mu.withDensity fun p ↦ ENNReal.ofReal (compactReturnWeight U c r hr p)

theorem compactReturnWeightedMeasure_isFinite
    (mu : Measure BetaNat) [IsProbabilityMeasure mu]
    (U : H ≃ₗᵢ[ℂ] H) (c : H) (r : ℝ) (hr : 0 < r) :
    IsFiniteMeasure (compactReturnWeightedMeasure mu U c r hr) := by
  unfold compactReturnWeightedMeasure
  apply isFiniteMeasure_withDensity
  apply ne_top_of_le_ne_top ENNReal.one_ne_top
  calc
    (∫⁻ p, ENNReal.ofReal (compactReturnWeight U c r hr p) ∂mu) ≤
        ∫⁻ _p, (1 : ℝ≥0∞) ∂mu := by
      apply lintegral_mono
      intro p
      exact ENNReal.ofReal_le_one.mpr
        (compactReturnWeight_le_one U c r hr p)
    _ = 1 := by simp

theorem compactReturnWeightedMeasure_neZero
    (mu : Measure BetaNat) [IsProbabilityMeasure mu]
    (U : H ≃ₗᵢ[ℂ] H) (c : H) (r : ℝ) (hr : 0 < r)
    (hpos : 0 < ∫ p, compactReturnWeight U c r hr p ∂mu) :
    NeZero (compactReturnWeightedMeasure mu U c r hr) := by
  refine ⟨fun hzero ↦ ?_⟩
  have hmeas : Measurable (fun p ↦ compactReturnWeight U c r hr p) :=
    (compactReturnWeight U c r hr).continuous.measurable
  have hnonneg : 0 ≤ᵐ[mu] fun p ↦ compactReturnWeight U c r hr p :=
    ae_of_all _ (compactReturnWeight_nonneg U c r hr)
  have hlin :
      (∫⁻ p, ENNReal.ofReal (compactReturnWeight U c r hr p) ∂mu) = 0 := by
    have huniv := congrArg (fun nu : Measure BetaNat ↦ nu Set.univ) hzero
    simpa only [compactReturnWeightedMeasure, withDensity_apply _ MeasurableSet.univ,
      Measure.restrict_univ, Measure.coe_zero, Pi.zero_apply] using huniv
  have hint : Integrable (fun p ↦ compactReturnWeight U c r hr p) mu := by
    refine ⟨hmeas.aestronglyMeasurable,
      HasFiniteIntegral.of_bounded (C := 1) (ae_of_all _ fun p ↦ ?_)⟩
    rw [Real.norm_eq_abs,
      abs_of_nonneg (compactReturnWeight_nonneg U c r hr p)]
    exact compactReturnWeight_le_one U c r hr p
  have hof : ENNReal.ofReal (∫ p, compactReturnWeight U c r hr p ∂mu) = 0 := by
    rw [ofReal_integral_eq_lintegral_ofReal hint hnonneg, hlin]
  exact (ENNReal.ofReal_pos.mpr hpos).ne' hof

/-- The weighted measure gives mass zero both to the complement of the
original support and to points where the return weight vanishes. -/
theorem compactReturnWeightedMeasure_badSet_zero
    (mu : Measure BetaNat) [IsProbabilityMeasure mu] [mu.Regular]
    (U : H ≃ₗᵢ[ℂ] H) (c : H) (r : ℝ) (hr : 0 < r) :
    compactReturnWeightedMeasure mu U c r hr
      (mu.supportᶜ ∪ {p | compactReturnWeight U c r hr p = 0}) = 0 := by
  apply measure_union_null
  · exact (withDensity_absolutelyContinuous mu _)
      (Measure.measure_compl_support_of_regular (μ := mu))
  · let Z : Set BetaNat := {p | compactReturnWeight U c r hr p = 0}
    have hZ : MeasurableSet Z :=
      isClosed_singleton.preimage (compactReturnWeight U c r hr).continuous |>.measurableSet
    unfold compactReturnWeightedMeasure
    rw [withDensity_apply _ hZ]
    exact setLIntegral_eq_zero hZ (fun p hp ↦ by
      have hp0 : compactReturnWeight U c r hr p = 0 := hp
      simp [hp0])

end

end Erdos109

open CompactlySupported Filter Function MeasureTheory Set
open scoped BoundedContinuousFunction ComplexConjugate ENNReal NNReal Pointwise Topology

namespace Erdos109

noncomputable section

noncomputable local instance : MeasurableSpace BetaNat := borel BetaNat
local instance : BorelSpace BetaNat := ⟨rfl⟩

/-! ## The deterministic character factor on `βℕ` -/

/-- The Stone--Čech extension of the character `n ↦ z^n`. -/
noncomputable def betaCharacter (z : Circle) : C(BetaNat, ℂ) :=
  betaExtendComplex (fun n ↦ (z : ℂ) ^ n) 1 (fun n ↦ by
    rw [norm_pow, Circle.norm_coe, one_pow])

@[simp] theorem betaCharacter_pure (z : Circle) (n : ℕ) :
    betaCharacter z (pure n) = (z : ℂ) ^ n := by
  simp [betaCharacter]

theorem betaCharacter_one : betaCharacter (1 : Circle) = 1 := by
  apply ContinuousMap.ext
  apply congrFun
  apply (denseRange_pure : DenseRange (pure : ℕ → BetaNat)).equalizer
  · exact (betaCharacter 1).continuous
  · fun_prop
  funext n
  simp

theorem betaCharacter_mul (z w : Circle) :
    betaCharacter (z * w) = betaCharacter z * betaCharacter w := by
  apply ContinuousMap.ext
  apply congrFun
  apply (denseRange_pure : DenseRange (pure : ℕ → BetaNat)).equalizer
  · exact (betaCharacter (z * w)).continuous
  · exact (betaCharacter z * betaCharacter w).continuous
  funext n
  simp [mul_pow]

theorem betaCharacter_inv (z : Circle) :
    betaCharacter z⁻¹ = star (betaCharacter z) := by
  apply ContinuousMap.ext
  apply congrFun
  apply (denseRange_pure : DenseRange (pure : ℕ → BetaNat)).equalizer
  · exact (betaCharacter z⁻¹).continuous
  · exact (star (betaCharacter z)).continuous
  funext n
  simp only [Function.comp_apply]
  rw [betaCharacter_pure, ContinuousMap.star_apply, betaCharacter_pure]
  rw [Circle.coe_inv_eq_conj]
  exact (map_pow (starRingEnd ℂ) (z : ℂ) n).symm

theorem betaCharacter_shift (z : Circle) :
    (betaCharacter z).comp ⟨betaShift, continuous_betaShift⟩ =
      (z : ℂ) • betaCharacter z := by
  apply ContinuousMap.ext
  apply congrFun
  apply (denseRange_pure : DenseRange (pure : ℕ → BetaNat)).equalizer
  · exact ((betaCharacter z).comp ⟨betaShift, continuous_betaShift⟩).continuous
  · exact ((z : ℂ) • betaCharacter z).continuous
  funext n
  simp only [Function.comp_apply, ContinuousMap.comp_apply,
    ContinuousMap.smul_apply, smul_eq_mul]
  have hshift : (⟨betaShift, continuous_betaShift⟩ : C(BetaNat, BetaNat)) (pure n) =
      pure (n + 1) := betaShift_pure n
  rw [hshift, betaCharacter_pure, betaCharacter_pure]
  rw [pow_succ']

variable {mu : Measure BetaNat} [IsProbabilityMeasure mu]

/-- A character, regarded as an `L²` vector. -/
noncomputable def betaCharacterL2 (z : Circle) : BetaL2 mu :=
  ContinuousMap.toLp 2 mu ℂ (betaCharacter z)

theorem betaKoopman_character
    (hmu : MeasurePreserving betaShift mu mu) (z : Circle) :
    betaKoopman hmu (betaCharacterL2 (mu := mu) z) =
      (z : ℂ) • betaCharacterL2 (mu := mu) z := by
  rw [betaCharacterL2, betaKoopman_continuousMap]
  change ContinuousMap.toLp 2 mu ℂ
      ((betaCharacter z).comp ⟨betaShift, continuous_betaShift⟩) = _
  rw [betaCharacter_shift]
  exact (ContinuousMap.toLp 2 mu ℂ).map_smul (z : ℂ) (betaCharacter z)

/-- Algebraic and closed Besicovitch character spaces in the empirical
Koopman Hilbert space. -/
noncomputable def betaBesSpan : Submodule ℂ (BetaL2 mu) :=
  Submodule.span ℂ (Set.range (betaCharacterL2 (mu := mu)))

noncomputable def betaBesClosed : ClosedSubmodule ℂ (BetaL2 mu) :=
  (betaBesSpan (mu := mu)).closure

theorem betaBesSpan_le_kronecker
    (hmu : MeasurePreserving betaShift mu mu) :
    betaBesSpan (mu := mu) ≤
      (unitaryKronecker (betaKoopman hmu)).toSubmodule := by
  rw [betaBesSpan, Submodule.span_le]
  rintro _ ⟨z, rfl⟩
  exact eigenvector_mem_kronecker (betaKoopman hmu)
    (betaKoopman_character hmu z)

theorem betaBesClosed_le_kronecker
    (hmu : MeasurePreserving betaShift mu mu) :
    (betaBesClosed (mu := mu)).toSubmodule ≤
      (unitaryKronecker (betaKoopman hmu)).toSubmodule := by
  change (betaBesSpan (mu := mu)).topologicalClosure ≤ _
  exact Submodule.topologicalClosure_minimal (betaBesSpan (mu := mu))
    (betaBesSpan_le_kronecker hmu)
    (unitaryKronecker (betaKoopman hmu)).isClosed'

theorem betaCharacterL2_one :
    betaCharacterL2 (mu := mu) (1 : Circle) =
      ContinuousMap.toLp 2 mu ℂ (1 : C(BetaNat, ℂ)) := by
  rw [betaCharacterL2, betaCharacter_one]

theorem one_mem_betaBesSpan :
    ContinuousMap.toLp 2 mu ℂ (1 : C(BetaNat, ℂ)) ∈
      betaBesSpan (mu := mu) := by
  rw [← betaCharacterL2_one (mu := mu)]
  exact Submodule.subset_span (Set.mem_range_self (1 : Circle))

/-! ## Continuous character polynomials -/

noncomputable def betaCharacterSpanC : Submodule ℂ C(BetaNat, ℂ) :=
  Submodule.span ℂ (Set.range betaCharacter)

theorem betaCharacterSpanC_one :
    (1 : C(BetaNat, ℂ)) ∈ betaCharacterSpanC := by
  rw [← betaCharacter_one]
  exact Submodule.subset_span (Set.mem_range_self (1 : Circle))

theorem betaCharacterSpanC_mul_mem {f g : C(BetaNat, ℂ)}
    (hf : f ∈ betaCharacterSpanC) (hg : g ∈ betaCharacterSpanC) :
    f * g ∈ betaCharacterSpanC := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
      rcases hf with ⟨z, rfl⟩
      induction hg using Submodule.span_induction with
      | mem g hg =>
          rcases hg with ⟨w, rfl⟩
          rw [← betaCharacter_mul]
          exact Submodule.subset_span (Set.mem_range_self (z * w))
      | zero => simp
      | add x y _ _ hx hy => simpa [mul_add] using
          (betaCharacterSpanC.add_mem hx hy)
      | smul a x _ hx => simpa [mul_smul_comm] using
          (betaCharacterSpanC.smul_mem a hx)
  | zero => simp
  | add x y _ _ hx hy => simpa [add_mul] using betaCharacterSpanC.add_mem hx hy
  | smul a x _ hx => simpa [smul_mul_assoc] using betaCharacterSpanC.smul_mem a hx

theorem betaCharacterSpanC_star_mem {f : C(BetaNat, ℂ)}
    (hf : f ∈ betaCharacterSpanC) : star f ∈ betaCharacterSpanC := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
      rcases hf with ⟨z, rfl⟩
      rw [← betaCharacter_inv]
      exact Submodule.subset_span (Set.mem_range_self z⁻¹)
  | zero => simp
  | add x y _ _ hx hy => simpa [map_add] using betaCharacterSpanC.add_mem hx hy
  | smul a x _ hx => simpa [star_smul] using betaCharacterSpanC.smul_mem (star a) hx

noncomputable def betaTrigAlgebra : StarSubalgebra ℂ C(BetaNat, ℂ) where
  carrier := betaCharacterSpanC
  zero_mem' := betaCharacterSpanC.zero_mem
  add_mem' := betaCharacterSpanC.add_mem
  one_mem' := betaCharacterSpanC_one
  mul_mem' := betaCharacterSpanC_mul_mem
  algebraMap_mem' := fun a ↦ by
    rw [show algebraMap ℂ C(BetaNat, ℂ) a = a • 1 by ext; simp]
    exact betaCharacterSpanC.smul_mem a betaCharacterSpanC_one
  star_mem' := betaCharacterSpanC_star_mem

theorem betaTrigAlgebra_toLp_mem_span {F : C(BetaNat, ℂ)}
    (hF : F ∈ betaTrigAlgebra) :
    ContinuousMap.toLp 2 mu ℂ F ∈ betaBesSpan (mu := mu) := by
  change F ∈ betaCharacterSpanC at hF
  induction hF using Submodule.span_induction with
  | mem F hF =>
      rcases hF with ⟨z, rfl⟩
      exact Submodule.subset_span (Set.mem_range_self z)
  | zero => simp
  | add x y _ _ hx hy => simpa using (betaBesSpan (mu := mu)).add_mem hx hy
  | smul a x _ hx => simpa using (betaBesSpan (mu := mu)).smul_mem a hx

/-! ## Finite phase tori -/

variable {I : Type*} [Fintype I]

noncomputable def phasePoint (z : I → Circle) (n : ℕ) : I → Circle :=
  fun i ↦ z i ^ n

noncomputable def torusCoordinate (i : I) : C((I → Circle), ℂ) :=
  ⟨fun x ↦ (x i : ℂ), continuous_subtype_val.comp (continuous_apply i)⟩

noncomputable def torusTrigAlgebra : StarSubalgebra ℂ C((I → Circle), ℂ) :=
  StarAlgebra.adjoin ℂ (Set.range torusCoordinate)

theorem torusTrigAlgebra_separatesPoints :
    (torusTrigAlgebra (I := I)).SeparatesPoints := by
  intro x y hxy
  have : ∃ i, x i ≠ y i := by
    by_contra h
    push_neg at h
    exact hxy (funext h)
  obtain ⟨i, hi⟩ := this
  refine ⟨(torusCoordinate i : (I → Circle) → ℂ), ?_, ?_⟩
  · refine ⟨torusCoordinate i, ?_, rfl⟩
    exact StarAlgebra.subset_adjoin ℂ _ (Set.mem_range_self i)
  · intro heq
    exact hi (Subtype.ext heq)

theorem torusTrigAlgebra_dense :
    (torusTrigAlgebra (I := I)).topologicalClosure = ⊤ :=
  ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints
    (torusTrigAlgebra (I := I)) torusTrigAlgebra_separatesPoints

/-- Extend a continuous observable sampled along one finite phase orbit to
the Stone--Čech compactification. -/
noncomputable def torusSampleExtension (z : I → Circle)
    (psi : C((I → Circle), ℂ)) : C(BetaNat, ℂ) :=
  betaExtendComplex (fun n ↦ psi (phasePoint z n)) ‖psi‖
    (fun n ↦ psi.norm_coe_le_norm (phasePoint z n))

@[simp] theorem torusSampleExtension_pure (z : I → Circle)
    (psi : C((I → Circle), ℂ)) (n : ℕ) :
    torusSampleExtension z psi (pure n) = psi (phasePoint z n) := by
  simp [torusSampleExtension]

theorem norm_torusSampleExtension_le (z : I → Circle)
    (psi : C((I → Circle), ℂ)) :
    ‖torusSampleExtension z psi‖ ≤ ‖psi‖ := by
  rw [ContinuousMap.norm_le _ (norm_nonneg psi)]
  exact norm_betaExtendComplex_le _ _ _

theorem torusSampleExtension_coordinate (z : I → Circle) (i : I) :
    torusSampleExtension z (torusCoordinate i) = betaCharacter (z i) := by
  apply ContinuousMap.ext
  apply congrFun
  apply (denseRange_pure : DenseRange (pure : ℕ → BetaNat)).equalizer
  · exact (torusSampleExtension z (torusCoordinate i)).continuous
  · exact (betaCharacter (z i)).continuous
  funext n
  simp [torusCoordinate, phasePoint]

theorem torusSampleExtension_algebraMap (z : I → Circle) (a : ℂ) :
    torusSampleExtension z (algebraMap ℂ C((I → Circle), ℂ) a) =
      algebraMap ℂ C(BetaNat, ℂ) a := by
  apply ContinuousMap.ext
  apply congrFun
  apply (denseRange_pure : DenseRange (pure : ℕ → BetaNat)).equalizer
  · exact (torusSampleExtension z
      (algebraMap ℂ C((I → Circle), ℂ) a)).continuous
  · fun_prop
  funext n
  simp

theorem torusSampleExtension_add (z : I → Circle)
    (psi phi : C((I → Circle), ℂ)) :
    torusSampleExtension z (psi + phi) =
      torusSampleExtension z psi + torusSampleExtension z phi := by
  apply ContinuousMap.ext
  apply congrFun
  apply (denseRange_pure : DenseRange (pure : ℕ → BetaNat)).equalizer
  · exact (torusSampleExtension z (psi + phi)).continuous
  · exact (torusSampleExtension z psi + torusSampleExtension z phi).continuous
  funext n
  simp

theorem torusSampleExtension_mul (z : I → Circle)
    (psi phi : C((I → Circle), ℂ)) :
    torusSampleExtension z (psi * phi) =
      torusSampleExtension z psi * torusSampleExtension z phi := by
  apply ContinuousMap.ext
  apply congrFun
  apply (denseRange_pure : DenseRange (pure : ℕ → BetaNat)).equalizer
  · exact (torusSampleExtension z (psi * phi)).continuous
  · exact (torusSampleExtension z psi * torusSampleExtension z phi).continuous
  funext n
  simp

theorem torusSampleExtension_smul (z : I → Circle) (a : ℂ)
    (psi : C((I → Circle), ℂ)) :
    torusSampleExtension z (a • psi) = a • torusSampleExtension z psi := by
  apply ContinuousMap.ext
  apply congrFun
  apply (denseRange_pure : DenseRange (pure : ℕ → BetaNat)).equalizer
  · exact (torusSampleExtension z (a • psi)).continuous
  · exact (a • torusSampleExtension z psi).continuous
  funext n
  simp

theorem torusSampleExtension_sub (z : I → Circle)
    (psi phi : C((I → Circle), ℂ)) :
    torusSampleExtension z (psi - phi) =
      torusSampleExtension z psi - torusSampleExtension z phi := by
  apply ContinuousMap.ext
  apply congrFun
  apply (denseRange_pure : DenseRange (pure : ℕ → BetaNat)).equalizer
  · exact (torusSampleExtension z (psi - phi)).continuous
  · exact (torusSampleExtension z psi - torusSampleExtension z phi).continuous
  funext n
  simp

theorem torusSampleExtension_star (z : I → Circle)
    (psi : C((I → Circle), ℂ)) :
    torusSampleExtension z (star psi) = star (torusSampleExtension z psi) := by
  apply ContinuousMap.ext
  apply congrFun
  apply (denseRange_pure : DenseRange (pure : ℕ → BetaNat)).equalizer
  · exact (torusSampleExtension z (star psi)).continuous
  · exact (star (torusSampleExtension z psi)).continuous
  funext n
  simp

theorem torusSampleExtension_mem_betaTrigAlgebra (z : I → Circle)
    {psi : C((I → Circle), ℂ)} (hpsi : psi ∈ torusTrigAlgebra) :
    torusSampleExtension z psi ∈ betaTrigAlgebra := by
  induction hpsi using StarAlgebra.adjoin_induction with
  | mem psi hpsi =>
      rcases hpsi with ⟨i, rfl⟩
      rw [torusSampleExtension_coordinate]
      change betaCharacter (z i) ∈ betaCharacterSpanC
      exact Submodule.subset_span (Set.mem_range_self (z i))
  | algebraMap a =>
      rw [torusSampleExtension_algebraMap]
      exact (betaTrigAlgebra).algebraMap_mem a
  | add psi phi _ _ hpsi hphi =>
      rw [torusSampleExtension_add]
      exact (betaTrigAlgebra).add_mem hpsi hphi
  | mul psi phi _ _ hpsi hphi =>
      rw [torusSampleExtension_mul]
      exact (betaTrigAlgebra).mul_mem hpsi hphi
  | star psi _ hpsi =>
      rw [torusSampleExtension_star]
      exact star_mem hpsi

theorem norm_toLp_continuousMap_le (F : C(BetaNat, ℂ)) :
    ‖ContinuousMap.toLp 2 mu ℂ F‖ ≤ ‖F‖ := by
  calc
    ‖ContinuousMap.toLp 2 mu ℂ F‖ ≤
        ‖(ContinuousMap.toLp 2 mu ℂ : C(BetaNat, ℂ) →L[ℂ] BetaL2 mu)‖ * ‖F‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖F‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg F)
      have hmass : measureUnivNNReal mu = 1 := by
        change (mu Set.univ).toNNReal = 1
        rw [measure_univ]
        rfl
      exact (ContinuousMap.toLp_norm_le
        (p := (2 : ℝ≥0∞)) (μ := mu) (E := ℂ) (𝕜 := ℂ)).trans_eq (by
          rw [hmass]
          simp)
    _ = ‖F‖ := one_mul _

/-- Any continuous observable on a finite phase torus, sampled along a
rotation orbit, gives a vector in the closed Besicovitch character space. -/
theorem torusSampleExtension_toLp_mem_betaBesClosed (z : I → Circle)
    (psi : C((I → Circle), ℂ)) :
    ContinuousMap.toLp 2 mu ℂ (torusSampleExtension z psi) ∈
      betaBesClosed (mu := mu) := by
  change ContinuousMap.toLp 2 mu ℂ (torusSampleExtension z psi) ∈
    (betaBesSpan (mu := mu)).topologicalClosure
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe,
    Metric.mem_closure_iff]
  intro epsilon hepsilon
  have hmem : psi ∈ (torusTrigAlgebra (I := I)).topologicalClosure := by
    rw [torusTrigAlgebra_dense]
    exact StarSubalgebra.mem_top
  change psi ∈ closure
    ((torusTrigAlgebra (I := I) : StarSubalgebra ℂ C((I → Circle), ℂ)) :
      Set C((I → Circle), ℂ)) at hmem
  obtain ⟨phi, hphi, hdist⟩ :=
    Metric.mem_closure_iff.mp hmem epsilon hepsilon
  refine ⟨ContinuousMap.toLp 2 mu ℂ (torusSampleExtension z phi), ?_, ?_⟩
  · apply betaTrigAlgebra_toLp_mem_span
    exact torusSampleExtension_mem_betaTrigAlgebra z hphi
  · rw [dist_eq_norm, ← map_sub]
    calc
      ‖ContinuousMap.toLp 2 mu ℂ
          (torusSampleExtension z psi - torusSampleExtension z phi)‖ ≤
          ‖torusSampleExtension z psi - torusSampleExtension z phi‖ :=
        norm_toLp_continuousMap_le _
      _ = ‖torusSampleExtension z (psi - phi)‖ := by
        rw [torusSampleExtension_sub]
      _ ≤ ‖psi - phi‖ := norm_torusSampleExtension_le z (psi - phi)
      _ < epsilon := by simpa only [dist_eq_norm] using hdist

end

end Erdos109

open CompactlySupported Filter Function MeasureTheory Set
open scoped BoundedContinuousFunction ComplexConjugate ENNReal NNReal Pointwise Topology

namespace Erdos109

noncomputable section

noncomputable local instance : MeasurableSpace BetaNat := borel BetaNat
local instance : BorelSpace BetaNat := ⟨rfl⟩

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Bundled eigenvectors of a unitary. -/
def UnitaryEigenvector (U : H ≃ₗᵢ[ℂ] H) :=
  {x : H // ∃ z : Circle, U x = (z : ℂ) • x}

noncomputable def unitaryEigenPhase (U : H ≃ₗᵢ[ℂ] H)
    (x : UnitaryEigenvector U) : Circle :=
  Classical.choose x.property

theorem unitaryEigenPhase_spec (U : H ≃ₗᵢ[ℂ] H)
    (x : UnitaryEigenvector U) :
    U x.1 = (unitaryEigenPhase U x : ℂ) • x.1 :=
  Classical.choose_spec x.property

theorem unitaryEigen_generator_eq_range (U : H ≃ₗᵢ[ℂ] H) :
    {x : H | ∃ z : Circle, U x = (z : ℂ) • x} =
      Set.range (fun x : UnitaryEigenvector U ↦ x.1) := by
  ext x
  simp [UnitaryEigenvector]

/-- A finite eigenvector expansion of an element of the algebraic eigen-span. -/
noncomputable def unitaryEigenCoeffs (U : H ≃ₗᵢ[ℂ] H) (c : H)
    (hc : c ∈ unitaryEigenSpan U) : UnitaryEigenvector U →₀ ℂ := by
  rw [unitaryEigenSpan, unitaryEigen_generator_eq_range,
    Finsupp.mem_span_range_iff_exists_finsupp] at hc
  exact Classical.choose hc

theorem unitaryEigenCoeffs_sum (U : H ≃ₗᵢ[ℂ] H) (c : H)
    (hc : c ∈ unitaryEigenSpan U) :
    (unitaryEigenCoeffs U c hc).sum (fun x a ↦ a • x.1) = c := by
  rw [unitaryEigenCoeffs]
  exact Classical.choose_spec (by
    rw [unitaryEigenSpan, unitaryEigen_generator_eq_range,
      Finsupp.mem_span_range_iff_exists_finsupp] at hc
    exact hc)

variable (U : H ≃ₗᵢ[ℂ] H) (c : H) (hc : c ∈ unitaryEigenSpan U)

abbrev EigenSupport := (unitaryEigenCoeffs U c hc).support

noncomputable def eigenSupportPhase (i : EigenSupport U c hc) : Circle :=
  unitaryEigenPhase U i.1

/-- Reconstruct the finite eigenvector expansion from arbitrary phases on
its finite support. -/
noncomputable def eigenModelPoint (x : EigenSupport U c hc → Circle) : H :=
  ∑ i : EigenSupport U c hc,
    ((unitaryEigenCoeffs U c hc) i.1 * (x i : ℂ)) • i.1.1

theorem continuous_eigenModelPoint :
    Continuous (eigenModelPoint U c hc) := by
  unfold eigenModelPoint
  fun_prop

theorem eigenModelPoint_phasePoint (n : ℕ) :
    eigenModelPoint U c hc (phasePoint (eigenSupportPhase U c hc) n) =
      (U ^ n) c := by
  classical
  let d := unitaryEigenCoeffs U c hc
  calc
    eigenModelPoint U c hc (phasePoint (eigenSupportPhase U c hc) n) =
        d.sum (fun x a ↦ (a * (unitaryEigenPhase U x : ℂ) ^ n) • x.1) := by
      simp only [eigenModelPoint, phasePoint, eigenSupportPhase, d]
      rw [Finsupp.sum]
      exact (Finset.sum_subtype (unitaryEigenCoeffs U c hc).support
        (fun _ ↦ Iff.rfl)
        (fun x ↦ ((unitaryEigenCoeffs U c hc) x *
          (unitaryEigenPhase U x : ℂ) ^ n) • x.1)).symm
    _ = d.sum (fun x a ↦ a • (U ^ n) x.1) := by
      apply Finsupp.sum_congr
      intro x hx
      rw [unitary_pow_eigenvector U (unitaryEigenPhase_spec U x) n,
        smul_smul]
    _ = (U ^ n) (d.sum (fun x a ↦ a • x.1)) := by
      rw [map_finsuppSum]
      simp
    _ = (U ^ n) c := by
      rw [unitaryEigenCoeffs_sum U c hc]

/-- The tent return observable on the finite phase model. -/
noncomputable def eigenReturnTorusObservable (r : ℝ) :
    C((EigenSupport U c hc → Circle), ℂ) :=
  ⟨fun x ↦ ((compactReturnBump r (dist (eigenModelPoint U c hc x) c) : ℝ) : ℂ),
    Complex.continuous_ofReal.comp
      ((continuous_compactReturnBump r).comp
        ((continuous_eigenModelPoint U c hc).dist continuous_const))⟩

theorem eigenReturnTorusObservable_phasePoint (r : ℝ) (n : ℕ) :
    eigenReturnTorusObservable U c hc r
        (phasePoint (eigenSupportPhase U c hc) n) =
      (compactReturnWeightCode U c r n : ℂ) := by
  simp only [eigenReturnTorusObservable, ContinuousMap.coe_mk]
  rw [eigenModelPoint_phasePoint]
  rfl

theorem torusSampleExtension_eigenReturn (r : ℝ) (hr : 0 < r) :
    torusSampleExtension (eigenSupportPhase U c hc)
        (eigenReturnTorusObservable U c hc r) =
      ⟨fun p ↦ (compactReturnWeight U c r hr p : ℂ),
        Complex.continuous_ofReal.comp (compactReturnWeight U c r hr).continuous⟩ := by
  apply ContinuousMap.ext
  apply congrFun
  apply (denseRange_pure : DenseRange (pure : ℕ → BetaNat)).equalizer
  · exact (torusSampleExtension (eigenSupportPhase U c hc)
      (eigenReturnTorusObservable U c hc r)).continuous
  · exact Complex.continuous_ofReal.comp (compactReturnWeight U c r hr).continuous
  funext n
  simp only [Function.comp_apply, torusSampleExtension_pure,
    eigenReturnTorusObservable_phasePoint]
  change (compactReturnWeightCode U c r n : ℂ) =
    (compactReturnWeight U c r hr (pure n) : ℂ)
  rw [compactReturnWeight_pure]

variable {mu : Measure BetaNat} [IsProbabilityMeasure mu]

/-- A smooth return weight for an algebraic finite-eigenvector combination
is a deterministic Besicovitch vector, even when the eigenvectors themselves
come from a larger Koopman Kronecker factor. -/
theorem returnWeightL2_mem_betaBesClosed_of_mem_eigenSpan
    (hc : c ∈ unitaryEigenSpan U) (r : ℝ) (hr : 0 < r) :
    ContinuousMap.toLp 2 mu ℂ
        ⟨fun p ↦ (compactReturnWeight U c r hr p : ℂ),
          Complex.continuous_ofReal.comp
            (compactReturnWeight U c r hr).continuous⟩ ∈
      betaBesClosed (mu := mu) := by
  rw [← torusSampleExtension_eigenReturn U c hc r hr]
  exact torusSampleExtension_toLp_mem_betaBesClosed
    (eigenSupportPhase U c hc) (eigenReturnTorusObservable U c hc r)

end

end Erdos109

open CompactlySupported Filter Function MeasureTheory Set
open scoped BoundedContinuousFunction ComplexConjugate ENNReal NNReal Pointwise Topology

namespace Erdos109

noncomputable section

noncomputable local instance : MeasurableSpace BetaNat := borel BetaNat
local instance : BorelSpace BetaNat := ⟨rfl⟩

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The diagonal action of a unitary on the Hilbert direct sum of two copies. -/
noncomputable def unitaryL2Prod (U : H ≃ₗᵢ[ℂ] H) :
    WithLp 2 (H × H) ≃ₗᵢ[ℂ] WithLp 2 (H × H) :=
  LinearIsometryEquiv.withLpProdCongr (p := 2) U U

@[simp] theorem unitaryL2Prod_apply (U : H ≃ₗᵢ[ℂ] H) (x y : H) :
    unitaryL2Prod U (WithLp.toLp 2 (x, y)) =
      WithLp.toLp 2 (U x, U y) := rfl

@[simp] theorem unitaryL2Prod_pow_apply (U : H ≃ₗᵢ[ℂ] H) (x y : H) (n : ℕ) :
    (unitaryL2Prod U ^ n) (WithLp.toLp 2 (x, y)) =
      WithLp.toLp 2 ((U ^ n) x, (U ^ n) y) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ']
      change unitaryL2Prod U ((unitaryL2Prod U ^ n) (WithLp.toLp 2 (x, y))) = _
      rw [ih, unitaryL2Prod_apply]
      apply congrArg (WithLp.toLp 2)
      apply Prod.ext
      · change U ((U ^ n) x) = (U ^ (n + 1)) x
        symm
        rw [pow_succ']
        rfl
      · change U ((U ^ n) y) = (U ^ (n + 1)) y
        symm
        rw [pow_succ']
        rfl

theorem unitaryL2Prod_eigen_left (U : H ≃ₗᵢ[ℂ] H)
    {x : H} {z : Circle} (hx : U x = (z : ℂ) • x) :
    unitaryL2Prod U (WithLp.toLp 2 (x, 0)) =
      (z : ℂ) • WithLp.toLp 2 (x, 0) := by
  rw [unitaryL2Prod_apply, hx, U.map_zero]
  simpa only [← WithLp.toLp_smul, Prod.smul_mk, smul_zero]

theorem unitaryL2Prod_eigen_right (U : H ≃ₗᵢ[ℂ] H)
    {y : H} {z : Circle} (hy : U y = (z : ℂ) • y) :
    unitaryL2Prod U (WithLp.toLp 2 (0, y)) =
      (z : ℂ) • WithLp.toLp 2 (0, y) := by
  rw [unitaryL2Prod_apply, hy, U.map_zero]
  simpa only [← WithLp.toLp_smul, Prod.smul_mk, smul_zero]

theorem unitaryEigenSpan_toLp_left (U : H ≃ₗᵢ[ℂ] H)
    {x : H} (hx : x ∈ unitaryEigenSpan U) :
    WithLp.toLp 2 (x, 0) ∈ unitaryEigenSpan (unitaryL2Prod U) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      rcases hx with ⟨z, hz⟩
      exact Submodule.subset_span ⟨z, unitaryL2Prod_eigen_left U hz⟩
  | zero =>
      change WithLp.toLp 2 (0 : H × H) ∈ _
      rw [WithLp.toLp_zero]
      exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
      simpa only [← WithLp.toLp_add, Prod.mk_add_mk, add_zero] using
        (unitaryEigenSpan (unitaryL2Prod U)).add_mem hx hy
  | smul a x _ hx =>
      simpa only [← WithLp.toLp_smul, Prod.smul_mk, smul_zero] using
        (unitaryEigenSpan (unitaryL2Prod U)).smul_mem a hx

theorem unitaryEigenSpan_toLp_right (U : H ≃ₗᵢ[ℂ] H)
    {y : H} (hy : y ∈ unitaryEigenSpan U) :
    WithLp.toLp 2 (0, y) ∈ unitaryEigenSpan (unitaryL2Prod U) := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
      rcases hy with ⟨z, hz⟩
      exact Submodule.subset_span ⟨z, unitaryL2Prod_eigen_right U hz⟩
  | zero =>
      change WithLp.toLp 2 (0 : H × H) ∈ _
      rw [WithLp.toLp_zero]
      exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
      simpa only [← WithLp.toLp_add, Prod.mk_add_mk, zero_add] using
        (unitaryEigenSpan (unitaryL2Prod U)).add_mem hx hy
  | smul a x _ hx =>
      simpa only [← WithLp.toLp_smul, Prod.smul_mk, smul_zero] using
        (unitaryEigenSpan (unitaryL2Prod U)).smul_mem a hx

/-- Two algebraic eigenvectors may be synchronized by putting them in the
Hilbert direct sum and using its diagonal unitary. -/
theorem unitaryEigenSpan_toLp_pair (U : H ≃ₗᵢ[ℂ] H)
    {x y : H} (hx : x ∈ unitaryEigenSpan U) (hy : y ∈ unitaryEigenSpan U) :
    WithLp.toLp 2 (x, y) ∈ unitaryEigenSpan (unitaryL2Prod U) := by
  have hsum := (unitaryEigenSpan (unitaryL2Prod U)).add_mem
    (unitaryEigenSpan_toLp_left U hx) (unitaryEigenSpan_toLp_right U hy)
  simpa only [← WithLp.toLp_add, Prod.mk_add_mk, add_zero, zero_add] using hsum

theorem compactReturnWeightL2_pair_mem_betaBesClosed
    {mu : Measure BetaNat} [IsProbabilityMeasure mu]
    (U : H ≃ₗᵢ[ℂ] H) {x y : H}
    (hx : x ∈ unitaryEigenSpan U) (hy : y ∈ unitaryEigenSpan U)
    (r : ℝ) (hr : 0 < r) :
    ContinuousMap.toLp 2 mu ℂ
        ⟨fun p ↦ (compactReturnWeight (unitaryL2Prod U)
            (WithLp.toLp 2 (x, y)) r hr p : ℂ),
          Complex.continuous_ofReal.comp
            (compactReturnWeight (unitaryL2Prod U)
              (WithLp.toLp 2 (x, y)) r hr).continuous⟩ ∈
      betaBesClosed (mu := mu) :=
  returnWeightL2_mem_betaBesClosed_of_mem_eigenSpan
    (unitaryL2Prod U) (WithLp.toLp 2 (x, y))
      (unitaryEigenSpan_toLp_pair U hx hy) r hr

/-- Positivity of the synchronized return weight forces simultaneous return
of both coordinates. -/
theorem compactReturnWeight_pair_pos_implies
    (U : H ≃ₗᵢ[ℂ] H) (x y : H) (r : ℝ) (hr : 0 < r)
    {p : BetaNat}
    (hp : 0 < compactReturnWeight (unitaryL2Prod U)
      (WithLp.toLp 2 (x, y)) r hr p) :
    {n | dist ((U ^ n) x) x < r} ∈ (p : Filter ℕ) ∧
      {n | dist ((U ^ n) y) y < r} ∈ (p : Filter ℕ) := by
  have hpair := compactReturnWeight_pos_implies_return_mem
    (unitaryL2Prod U) (WithLp.toLp 2 (x, y)) r hr p hp
  constructor
  · filter_upwards [hpair] with n hn
    rw [unitaryL2Prod_pow_apply] at hn
    have hcoord := WithLp.dist_fst_le
      ((unitaryL2Prod U ^ n) (WithLp.toLp 2 (x, y)))
      (WithLp.toLp 2 (x, y))
    rw [unitaryL2Prod_pow_apply] at hcoord
    exact lt_of_le_of_lt hcoord hn
  · filter_upwards [hpair] with n hn
    rw [unitaryL2Prod_pow_apply] at hn
    have hcoord := WithLp.dist_snd_le
      ((unitaryL2Prod U ^ n) (WithLp.toLp 2 (x, y)))
      (WithLp.toLp 2 (x, y))
    rw [unitaryL2Prod_pow_apply] at hcoord
    exact lt_of_le_of_lt hcoord hn

end

end Erdos109

open Filter Function Set

namespace Erdos109

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem exists_vector_representing_family_functional
    (v : ℕ → H) (c : ℕ → ℂ)
    (hc : ∀ d : ℕ →₀ ℂ,
      ‖Finsupp.linearCombination ℂ v d‖ ≥
        ‖Finsupp.linearCombination ℂ c d‖) :
    ∃ y : H, ‖y‖ ≤ 1 ∧ ∀ n : ℕ, inner ℂ y (v n) = c n := by
  let T : (ℕ →₀ ℂ) →ₗ[ℂ] H := Finsupp.linearCombination ℂ v
  let L : (ℕ →₀ ℂ) →ₗ[ℂ] ℂ := Finsupp.linearCombination ℂ c
  have hker : LinearMap.ker T ≤ LinearMap.ker L := by
    intro d hd
    rw [LinearMap.mem_ker] at hd ⊢
    have hnorm : ‖L d‖ = 0 := by
      apply le_antisymm
      · simpa only [T, L, hd, norm_zero] using hc d
      · exact norm_nonneg _
    exact norm_eq_zero.mp hnorm
  let Lq := (LinearMap.ker T).liftQ L hker
  let LR : LinearMap.range T →ₗ[ℂ] ℂ :=
    Lq.comp T.quotKerEquivRange.symm.toLinearMap
  have hLR_image (d : ℕ →₀ ℂ) :
      LR ⟨T d, LinearMap.mem_range_self T d⟩ = L d := by
    simp [LR, Lq]
  have hLR_bound (x : LinearMap.range T) : ‖LR x‖ ≤ 1 * ‖x‖ := by
    rcases x.property with ⟨d, hd⟩
    have hx : x = ⟨T d, LinearMap.mem_range_self T d⟩ := Subtype.ext hd.symm
    rw [hx, hLR_image]
    simpa only [one_mul, Submodule.coe_norm] using hc d
  let LRc : StrongDual ℂ (LinearMap.range T) := LR.mkContinuous 1 hLR_bound
  have hLRc_norm : ‖LRc‖ ≤ 1 :=
    LinearMap.mkContinuous_norm_le LR zero_le_one hLR_bound
  obtain ⟨g, hgext, hgnorm⟩ :=
    exists_extension_norm_eq (LinearMap.range T) LRc
  let y : H := (InnerProductSpace.toDual ℂ H).symm g
  refine ⟨y, ?_, ?_⟩
  · rw [show ‖y‖ = ‖g‖ by
      change ‖(InnerProductSpace.toDual ℂ H).symm g‖ = ‖g‖
      exact (InnerProductSpace.toDual ℂ H).symm.norm_map g]
    rw [hgnorm]
    exact hLRc_norm
  · intro n
    rw [InnerProductSpace.toDual_symm_apply]
    have hmem : v n ∈ LinearMap.range T := by
      refine ⟨Finsupp.single n 1, ?_⟩
      simp [T]
    calc
      g (v n) = g (⟨v n, hmem⟩ : LinearMap.range T) := rfl
      _ = LRc ⟨v n, hmem⟩ := hgext _
      _ = LR ⟨v n, hmem⟩ := rfl
      _ = L (Finsupp.single n 1) := by
        rw [← hLR_image]
        congr 1
        simp [T]
      _ = c n := by simp [L]

/-- A convenient limit interface for the preceding Hahn--Banach lemma.
The finite functionals `L k` may live on changing empirical spaces; it is
enough that their values and their Cauchy--Schwarz majorants converge. -/
theorem exists_vector_representing_limit_family_functional
    (v : ℕ → H) (c : ℕ → ℂ)
    (L : ℕ → (ℕ →₀ ℂ) → ℂ) (Q : ℕ → (ℕ →₀ ℂ) → ℝ)
    (hL : ∀ d, Tendsto (fun k ↦ L k d) atTop
      (nhds (Finsupp.linearCombination ℂ c d)))
    (hQ : ∀ d, Tendsto (fun k ↦ Q k d) atTop
      (nhds ‖Finsupp.linearCombination ℂ v d‖))
    (hbound : ∀ k d, ‖L k d‖ ≤ Q k d) :
    ∃ y : H, ‖y‖ ≤ 1 ∧ ∀ n : ℕ, inner ℂ y (v n) = c n := by
  apply exists_vector_representing_family_functional v c
  intro d
  exact le_of_tendsto_of_tendsto (hL d).norm (hQ d)
    (Eventually.of_forall fun k ↦ hbound k d)

theorem exists_vector_representing_orbit_functional
    (U : H ≃ₗᵢ[ℂ] H) (F : H) (c : ℕ → ℂ)
    (hc : ∀ d : ℕ →₀ ℂ,
      ‖Finsupp.linearCombination ℂ (fun n ↦ (U ^ n) F) d‖ ≥
        ‖Finsupp.linearCombination ℂ c d‖) :
    ∃ y : H, ‖y‖ ≤ 1 ∧ ∀ n : ℕ, inner ℂ y ((U ^ n) F) = c n :=
  exists_vector_representing_family_functional
    (fun n ↦ (U ^ n) F) c hc

end

end Erdos109

open CompactlySupported Filter Function MeasureTheory Set
open scoped BoundedContinuousFunction ComplexConjugate ENNReal NNReal Pointwise Topology

namespace Erdos109

noncomputable section

noncomputable local instance : MeasurableSpace BetaNat := borel BetaNat
local instance : BorelSpace BetaNat := ⟨rfl⟩

variable {mu : Measure BetaNat} [IsProbabilityMeasure mu]

/-- Every algebraic Besicovitch vector has a continuous character-polynomial
representative. -/
theorem betaBesSpan_exists_characterPolynomial
    {v : BetaL2 mu} (hv : v ∈ betaBesSpan (mu := mu)) :
    ∃ Y : C(BetaNat, ℂ), Y ∈ betaCharacterSpanC ∧
      ContinuousMap.toLp 2 mu ℂ Y = v := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
      rcases hv with ⟨z, rfl⟩
      exact ⟨betaCharacter z, Submodule.subset_span (Set.mem_range_self z), rfl⟩
  | zero =>
      exact ⟨0, (betaCharacterSpanC).zero_mem, by simp⟩
  | add x y _ _ hx hy =>
      rcases hx with ⟨X, hX, rfl⟩
      rcases hy with ⟨Y, hY, rfl⟩
      exact ⟨X + Y, (betaCharacterSpanC).add_mem hX hY, by simp⟩
  | smul a x _ hx =>
      rcases hx with ⟨X, hX, rfl⟩
      exact ⟨a • X, (betaCharacterSpanC).smul_mem a hX, by simp⟩

theorem betaBesSpan_le_unitaryEigenSpan
    (hmu : MeasurePreserving betaShift mu mu) :
    betaBesSpan (mu := mu) ≤ unitaryEigenSpan (betaKoopman hmu) := by
  rw [betaBesSpan, Submodule.span_le]
  rintro _ ⟨z, rfl⟩
  exact Submodule.subset_span ⟨z, betaKoopman_character hmu z⟩

/-- Approximation inside the closed Besicovitch space by a continuous finite
character polynomial, retaining algebraic eigenvector membership. -/
theorem exists_characterPolynomial_close_betaBesClosed
    (hmu : MeasurePreserving betaShift mu mu)
    {b : BetaL2 mu} (hb : b ∈ betaBesClosed (mu := mu))
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ Y : C(BetaNat, ℂ),
      Y ∈ betaCharacterSpanC ∧
      ContinuousMap.toLp 2 mu ℂ Y ∈ unitaryEigenSpan (betaKoopman hmu) ∧
      ‖b - ContinuousMap.toLp 2 mu ℂ Y‖ < epsilon := by
  change b ∈ (betaBesSpan (mu := mu)).topologicalClosure at hb
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe,
    Metric.mem_closure_iff] at hb
  obtain ⟨v, hv, hvclose⟩ := hb epsilon hepsilon
  rcases betaBesSpan_exists_characterPolynomial hv with ⟨Y, hY, rfl⟩
  refine ⟨Y, hY, betaBesSpan_le_unitaryEigenSpan hmu hv, ?_⟩
  simpa only [dist_eq_norm] using hvclose

theorem clipComplexLp_toLp (Z : C(BetaNat, ℂ)) :
    clipComplexLp (ContinuousMap.toLp 2 mu ℂ Z) =
      ContinuousMap.toLp 2 mu ℂ
        ⟨fun p ↦ clipComplex01 (Z p),
          continuous_clipComplex01.comp Z.continuous⟩ := by
  apply Lp.ext
  filter_upwards [coeFn_clipComplexLp
      (ContinuousMap.toLp 2 mu ℂ Z),
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) mu Z,
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) mu
      ⟨fun p ↦ clipComplex01 (Z p),
        continuous_clipComplex01.comp Z.continuous⟩] with p hclip hZ hright
  rw [hclip, hZ, hright]
  rfl

/-- A clipped `L²` vector admits continuous `[0,1]`-valued approximants. -/
theorem exists_continuous_clip_close
    [mu.Regular]
    {a : BetaL2 mu} (ha : clipComplexLp a = a)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ Hc : C(BetaNat, ℂ),
      (∀ p, Hc p = ((Hc p).re : ℂ) ∧ 0 ≤ (Hc p).re ∧ (Hc p).re ≤ 1) ∧
      ‖a - ContinuousMap.toLp 2 mu ℂ Hc‖ < epsilon := by
  have hdense := ContinuousMap.toLp_denseRange ℂ mu ℂ
    (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
  obtain ⟨Z, hZ⟩ := hdense.exists_dist_lt a hepsilon
  let Hc : C(BetaNat, ℂ) :=
    ⟨fun p ↦ clipComplex01 (Z p),
      continuous_clipComplex01.comp Z.continuous⟩
  refine ⟨Hc, ?_, ?_⟩
  · intro p
    dsimp only [Hc]
    constructor
    · simp [clipComplex01]
    · constructor <;> simp [clipComplex01]
  · have hcontract := lipschitzWith_clipComplex01.norm_compLp_sub_le
        clipComplex01_zero a (ContinuousMap.toLp 2 mu ℂ Z)
    change ‖clipComplexLp a -
        clipComplexLp (ContinuousMap.toLp 2 mu ℂ Z)‖ ≤
      1 * ‖a - ContinuousMap.toLp 2 mu ℂ Z‖ at hcontract
    rw [ha, clipComplexLp_toLp Z] at hcontract
    change ‖a - ContinuousMap.toLp 2 mu ℂ Hc‖ < epsilon
    calc
      ‖a - ContinuousMap.toLp 2 mu ℂ Hc‖ ≤
          1 * ‖a - ContinuousMap.toLp 2 mu ℂ Z‖ := hcontract
      _ < epsilon := by simpa only [one_mul, dist_eq_norm] using hZ

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Algebraic eigenvectors are dense in the Kronecker subspace by definition. -/
theorem exists_unitaryEigenSpan_close
    (U : H ≃ₗᵢ[ℂ] H) {a : H} (ha : a ∈ unitaryKronecker U)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ g : H, g ∈ unitaryEigenSpan U ∧ ‖a - g‖ < epsilon := by
  change a ∈ (unitaryEigenSpan U).topologicalClosure at ha
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe,
    Metric.mem_closure_iff] at ha
  obtain ⟨g, hg, hag⟩ := ha epsilon hepsilon
  exact ⟨g, hg, by simpa only [dist_eq_norm] using hag⟩

end

end Erdos109

open CompactlySupported Filter Function MeasureTheory Set
open scoped BoundedContinuousFunction ComplexConjugate ENNReal NNReal Pointwise Topology

namespace Erdos109

noncomputable section

noncomputable local instance : MeasurableSpace BetaNat := borel BetaNat
local instance : BorelSpace BetaNat := ⟨rfl⟩

variable {mu : Measure BetaNat} [IsProbabilityMeasure mu]

theorem inner_compactPart_besProjection
    (hmu : MeasurePreserving betaShift mu mu) (F : BetaL2 mu) :
    inner ℂ (unitaryCompactPart (betaKoopman hmu) F)
        ((betaBesClosed (mu := mu)).toSubmodule.starProjection F) =
      inner ℂ ((betaBesClosed (mu := mu)).toSubmodule.starProjection F)
        ((betaBesClosed (mu := mu)).toSubmodule.starProjection F) := by
  let U := betaKoopman hmu
  let S := (betaBesClosed (mu := mu)).toSubmodule
  let K := (unitaryKronecker U).toSubmodule
  let a := unitaryCompactPart U F
  let b := S.starProjection F
  have hbS : b ∈ S := S.starProjection_apply_mem F
  have hbK : b ∈ K := betaBesClosed_le_kronecker hmu hbS
  have hFa : inner ℂ (F - a) b = 0 := by
    exact K.starProjection_inner_eq_zero F b hbK
  have hFb : inner ℂ (F - b) b = 0 := by
    exact S.starProjection_inner_eq_zero F b hbS
  have hab : inner ℂ a b = inner ℂ F b := by
    rw [inner_sub_left, sub_eq_zero] at hFa
    exact hFa.symm
  have hbb : inner ℂ b b = inner ℂ F b := by
    rw [inner_sub_left, sub_eq_zero] at hFb
    exact hFb.symm
  simpa only [U, S, K, a, b] using hab.trans hbb.symm

theorem norm_one_betaL2 :
    ‖ContinuousMap.toLp 2 mu ℂ (1 : C(BetaNat, ℂ))‖ = 1 := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (by positivity : (0 : ℝ) ≤ 1)]
  rw [← @inner_self_eq_norm_sq ℂ _ _ _ _]
  rw [ContinuousMap.inner_toLp]
  simp

theorem integral_indicator_le_norm_besProjection
    (A : Set ℕ) :
    ∫ p, betaIndicator A p ∂mu ≤
      ‖(betaBesClosed (mu := mu)).toSubmodule.starProjection
        (betaIndicatorL2 mu A)‖ := by
  let F := betaIndicatorL2 mu A
  let S := (betaBesClosed (mu := mu)).toSubmodule
  let e : BetaL2 mu := ContinuousMap.toLp 2 mu ℂ (1 : C(BetaNat, ℂ))
  let b := S.starProjection F
  have heS : e ∈ S := by
    apply (betaBesSpan (mu := mu)).le_topologicalClosure
    exact one_mem_betaBesSpan
  have hproj : inner ℂ (F - b) e = 0 := S.starProjection_inner_eq_zero F e heS
  have hinner : inner ℂ b e = ((∫ p, betaIndicator A p ∂mu : ℝ) : ℂ) := by
    have hFe : inner ℂ F e = ((∫ p, betaIndicator A p ∂mu : ℝ) : ℂ) := by
      dsimp only [F, e, betaIndicatorL2]
      rw [ContinuousMap.inner_toLp]
      simpa [betaIndicatorComplex] using
        (integral_ofReal (X := BetaNat) (μ := mu) (𝕜 := ℂ)
          (f := fun p : BetaNat ↦ betaIndicator A p))
    rw [inner_sub_left, sub_eq_zero] at hproj
    exact hproj.symm.trans hFe
  have hcs := norm_inner_le_norm (𝕜 := ℂ) b e
  rw [hinner, Complex.norm_real, Real.norm_eq_abs, norm_one_betaL2] at hcs
  have hintnonneg : 0 ≤ ∫ p, betaIndicator A p ∂mu := by
    apply integral_nonneg
    intro p
    by_cases hp : betaMembership A p = true <;> simp [betaIndicator, hp]
  simpa only [abs_of_nonneg hintnonneg, mul_one, S, b] using hcs

theorem sq_integral_indicator_le_re_inner_compact_bes
    (hmu : MeasurePreserving betaShift mu mu) (A : Set ℕ) :
    (∫ p, betaIndicator A p ∂mu) ^ 2 ≤
      (inner ℂ
        (unitaryCompactPart (betaKoopman hmu) (betaIndicatorL2 mu A))
        ((betaBesClosed (mu := mu)).toSubmodule.starProjection
          (betaIndicatorL2 mu A))).re := by
  rw [inner_compactPart_besProjection hmu]
  have hbself :
      (inner ℂ
        ((betaBesClosed (mu := mu)).toSubmodule.starProjection
          (betaIndicatorL2 mu A))
        ((betaBesClosed (mu := mu)).toSubmodule.starProjection
          (betaIndicatorL2 mu A))).re =
        ‖(betaBesClosed (mu := mu)).toSubmodule.starProjection
          (betaIndicatorL2 mu A)‖ ^ 2 := by
    exact inner_self_eq_norm_sq (𝕜 := ℂ) _
  rw [hbself]
  have hnonneg : 0 ≤ ∫ p, betaIndicator A p ∂mu := by
    apply integral_nonneg
    intro p
    by_cases hp : betaMembership A p = true <;> simp [betaIndicator, hp]
  exact (sq_le_sq₀ hnonneg (norm_nonneg _)).2
    (integral_indicator_le_norm_besProjection A)

end

end Erdos109

open CompactlySupported Filter Function MeasureTheory Set
open scoped BoundedContinuousFunction ComplexConjugate ENNReal NNReal Pointwise Topology

namespace Erdos109

noncomputable section

noncomputable local instance : MeasurableSpace BetaNat := borel BetaNat
local instance : BorelSpace BetaNat := ⟨rfl⟩

variable {mu : Measure BetaNat} [IsProbabilityMeasure mu]

theorem betaKoopman_symm_character
    (hmu : MeasurePreserving betaShift mu mu) (z : Circle) :
    (betaKoopman hmu).symm (betaCharacterL2 (mu := mu) z) =
      ((z : ℂ)⁻¹) • betaCharacterL2 (mu := mu) z := by
  apply (betaKoopman hmu).injective
  rw [(betaKoopman hmu).apply_symm_apply, map_smul,
    betaKoopman_character hmu, smul_smul,
    inv_mul_cancel₀ (Circle.coe_ne_zero z), one_smul]

theorem betaBesClosed_symm_invariant
    (hmu : MeasurePreserving betaShift mu mu)
    {v : BetaL2 mu} (hv : v ∈ betaBesClosed (mu := mu)) :
    (betaKoopman hmu).symm v ∈ betaBesClosed (mu := mu) := by
  let S := (betaBesClosed (mu := mu)).toSubmodule
  let M : Submodule ℂ (BetaL2 mu) :=
    S.comap (betaKoopman hmu).symm.toLinearMap
  have hMclosed : IsClosed (M : Set (BetaL2 mu)) := by
    exact (betaBesClosed (mu := mu)).isClosed'.preimage
      (betaKoopman hmu).symm.continuous
  have hgen : Set.range (betaCharacterL2 (mu := mu)) ⊆ M := by
    rintro _ ⟨z, rfl⟩
    change (betaKoopman hmu).symm (betaCharacterL2 (mu := mu) z) ∈ S
    rw [betaKoopman_symm_character]
    exact S.smul_mem _ ((betaBesSpan (mu := mu)).le_topologicalClosure
      (Submodule.subset_span (Set.mem_range_self z)))
  have hspan : betaBesSpan (mu := mu) ≤ M := by
    rw [betaBesSpan, Submodule.span_le]
    exact hgen
  have hclosure : (betaBesSpan (mu := mu)).topologicalClosure ≤ M :=
    Submodule.topologicalClosure_minimal _ hspan hMclosed
  exact hclosure hv

theorem betaBesClosed_symm_pow_invariant
    (hmu : MeasurePreserving betaShift mu mu)
    {v : BetaL2 mu} (hv : v ∈ betaBesClosed (mu := mu)) (n : ℕ) :
    ((betaKoopman hmu).symm ^ n) v ∈ betaBesClosed (mu := mu) := by
  induction n with
  | zero => simpa using hv
  | succ n ih =>
      rw [pow_succ']
      exact betaBesClosed_symm_invariant hmu ih

theorem inner_bes_koopman_pow_sub_projection_eq_zero
    (hmu : MeasurePreserving betaShift mu mu)
    (F : BetaL2 mu) {W : BetaL2 mu}
    (hW : W ∈ betaBesClosed (mu := mu)) (n : ℕ) :
    inner ℂ W ((betaKoopman hmu ^ n)
      (F - (betaBesClosed (mu := mu)).toSubmodule.starProjection F)) = 0 := by
  let U := betaKoopman hmu
  let S := (betaBesClosed (mu := mu)).toSubmodule
  let v := F - S.starProjection F
  have hWs : (U.symm ^ n) W ∈ S :=
    betaBesClosed_symm_pow_invariant hmu hW n
  have horth : inner ℂ v ((U.symm ^ n) W) = 0 :=
    S.starProjection_inner_eq_zero F _ hWs
  have hmove : inner ℂ W ((U ^ n) v) =
      inner ℂ ((U.symm ^ n) W) v := by
    calc
      inner ℂ W ((U ^ n) v) = inner ℂ (((U ^ n).symm) W) v :=
        ((U ^ n).symm.inner_map_eq_flip W v).symm
      _ = inner ℂ ((U.symm ^ n) W) v := by
        have heq : (U ^ n).symm = U.symm ^ n := by
          change (U ^ n)⁻¹ = U⁻¹ ^ n
          exact (inv_pow U n).symm
        rw [heq]
  rw [hmove]
  exact inner_eq_zero_symm.mpr horth

end

end Erdos109

open CompactlySupported Filter Function MeasureTheory Set
open scoped BoundedContinuousFunction ComplexConjugate ENNReal NNReal Pointwise Topology

namespace Erdos109

noncomputable section

noncomputable local instance : MeasurableSpace BetaNat := borel BetaNat
local instance : BorelSpace BetaNat := ⟨rfl⟩

noncomputable def continuousRealPart (Y : C(BetaNat, ℂ)) : C(BetaNat, ℝ) :=
  ⟨fun p ↦ (Y p).re, Complex.continuous_re.comp Y.continuous⟩

noncomputable def continuousAntiPart (A : Set ℕ) (Y : C(BetaNat, ℂ)) :
    C(BetaNat, ℝ) := betaIndicator A - continuousRealPart Y

theorem continuousAntiPart_pure (A : Set ℕ) (Y : C(BetaNat, ℂ)) (n : ℕ) :
    continuousAntiPart A Y (pure n) =
      realIndicator A n - (Y (pure n)).re := by
  simp [continuousAntiPart, continuousRealPart]

theorem abs_continuousAntiPart_pure_le (A : Set ℕ)
    (Y : C(BetaNat, ℂ)) (n : ℕ) :
    |continuousAntiPart A Y (pure n)| ≤ 1 + ‖Y‖ := by
  rw [continuousAntiPart_pure]
  calc
    |realIndicator A n - (Y (pure n)).re| ≤
        |realIndicator A n| + |(Y (pure n)).re| := abs_sub _ _
    _ ≤ 1 + ‖Y‖ := by
      gcongr
      · by_cases hn : n ∈ A <;> simp [realIndicator, hn]
      · exact (Complex.abs_re_le_norm _).trans (Y.norm_coe_le_norm _)

theorem iterate_betaShift_pure (n m : ℕ) :
    betaShift^[n] (pure m) = pure (m + n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, betaShift_pure]
      congr 1

theorem betaIndicator_iterate_shift (A : Set ℕ) (n : ℕ) :
    (betaIndicator A).comp
        ⟨betaShift^[n], continuous_betaShift.iterate n⟩ =
      betaIndicator (shift A n) := by
  apply ContinuousMap.ext
  apply congrFun
  apply (denseRange_pure : DenseRange (pure : ℕ → BetaNat)).equalizer
  · exact ((betaIndicator A).comp
      ⟨betaShift^[n], continuous_betaShift.iterate n⟩).continuous
  · exact (betaIndicator (shift A n)).continuous
  funext m
  simp only [Function.comp_apply, ContinuousMap.comp_apply]
  change betaIndicator A (betaShift^[n] (pure m)) =
    betaIndicator (shift A n) (pure m)
  rw [iterate_betaShift_pure]
  simp only [betaIndicator_pure, natIndicator_eq_realIndicator,
    realIndicator_shift, add_comm]

theorem betaRightTranslate_of_continuous (G : C(BetaNat, ℝ))
    (C : ℝ) (hG : ∀ p, |G p| ≤ C) (n : ℕ) :
    betaRightTranslate (fun m ↦ G (pure m)) C (fun m ↦ hG (pure m)) n =
      G.comp ⟨betaShift^[n], continuous_betaShift.iterate n⟩ := by
  apply ContinuousMap.ext
  apply congrFun
  apply (denseRange_pure : DenseRange (pure : ℕ → BetaNat)).equalizer
  · exact (betaRightTranslate _ C _ n).continuous
  · exact (G.comp ⟨betaShift^[n], continuous_betaShift.iterate n⟩).continuous
  funext m
  simp only [Function.comp_apply, ContinuousMap.comp_apply,
    betaRightTranslate_pure]
  change G (pure (n + m)) = G (betaShift^[n] (pure m))
  rw [iterate_betaShift_pure, add_comm]

variable {mu : Measure BetaNat} [IsProbabilityMeasure mu]

theorem norm_toLp_returnWeight_le_one
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (V : K ≃ₗᵢ[ℂ] K) (c : K) (r : ℝ) (hr : 0 < r) :
    ‖ContinuousMap.toLp 2 mu ℂ
      ⟨fun p ↦ (compactReturnWeight V c r hr p : ℂ),
        Complex.continuous_ofReal.comp
          (compactReturnWeight V c r hr).continuous⟩‖ ≤ 1 := by
  apply (norm_toLp_continuousMap_le _).trans
  rw [ContinuousMap.norm_le _ (by positivity)]
  intro p
  change ‖(compactReturnWeight V c r hr p : ℂ)‖ ≤ 1
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (compactReturnWeight_nonneg V c r hr p)]
  exact compactReturnWeight_le_one V c r hr p

/-- The weighted anti-structured correlations are uniformly small when the
continuous trigonometric representative is close to the Besicovitch
projection. -/
theorem abs_integral_returnWeight_mul_rightTranslate_anti_le
    (hmu : MeasurePreserving betaShift mu mu)
    (A : Set ℕ) (Y : C(BetaNat, ℂ))
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (V : K ≃ₗᵢ[ℂ] K) (c : K) (r : ℝ) (hr : 0 < r)
    (hWbes : ContinuousMap.toLp 2 mu ℂ
        ⟨fun p ↦ (compactReturnWeight V c r hr p : ℂ),
          Complex.continuous_ofReal.comp
            (compactReturnWeight V c r hr).continuous⟩ ∈
      betaBesClosed (mu := mu))
    (n : ℕ) :
    |∫ p, compactReturnWeight V c r hr p *
        betaRightTranslate
          (fun m ↦ continuousAntiPart A Y (pure m)) (1 + ‖Y‖)
          (abs_continuousAntiPart_pure_le A Y) n p ∂mu| ≤
      ‖(betaBesClosed (mu := mu)).toSubmodule.starProjection
          (betaIndicatorL2 mu A) - ContinuousMap.toLp 2 mu ℂ Y‖ := by
  let U := betaKoopman hmu
  let F := betaIndicatorL2 mu A
  let b := (betaBesClosed (mu := mu)).toSubmodule.starProjection F
  let y := ContinuousMap.toLp 2 mu ℂ Y
  let Wc : C(BetaNat, ℂ) :=
    ⟨fun p ↦ (compactReturnWeight V c r hr p : ℂ),
      Complex.continuous_ofReal.comp (compactReturnWeight V c r hr).continuous⟩
  let W := ContinuousMap.toLp 2 mu ℂ Wc
  have hright := betaRightTranslate_of_continuous (continuousAntiPart A Y)
    (1 + ‖Y‖) (fun p ↦ by
      have hA : |betaIndicator A p| ≤ 1 := by
        by_cases hp : betaMembership A p = true <;> simp [betaIndicator, hp]
      calc
        |continuousAntiPart A Y p| ≤
            |betaIndicator A p| + |(Y p).re| := by
              simpa [continuousAntiPart, continuousRealPart] using
                abs_sub (betaIndicator A p) (Y p).re
        _ ≤ 1 + ‖Y‖ := by
          gcongr
          exact (Complex.abs_re_le_norm _).trans (Y.norm_coe_le_norm _)) n
  rw [hright]
  have hinter :
      (∫ p, compactReturnWeight V c r hr p *
          (continuousAntiPart A Y).comp
            ⟨betaShift^[n], continuous_betaShift.iterate n⟩ p ∂mu : ℝ) =
        (inner ℂ W ((U ^ n) (F - y))).re := by
    dsimp only [U, F, y]
    rw [map_sub, betaKoopman_pow_indicator,
      betaKoopman_pow_continuousMap]
    dsimp only [W, Wc, betaIndicatorL2]
    rw [← map_sub, ContinuousMap.inner_toLp]
    let Q : C(BetaNat, ℂ) :=
      (betaIndicatorComplex (shift A n) - betaShiftComplex^[n] Y) * Wc
    have hQint : Integrable (fun p ↦ Q p) mu :=
      (BoundedContinuousFunction.mkOfCompact Q).integrable mu
    have hcomplex :
        (∫ p, (betaIndicatorComplex (shift A n) - betaShiftComplex^[n] Y) p *
          conj (Wc p) ∂mu) = ∫ p, Q p ∂mu := by
      apply integral_congr_ae
      filter_upwards [] with p
      simp [Q, Wc]
    rw [hcomplex]
    have hre : (∫ p, (Q p).re ∂mu) = (∫ p, Q p ∂mu).re := by
      simpa only [RCLike.re_eq_complex_re] using integral_re hQint
    rw [← hre]
    apply integral_congr_ae
    filter_upwards [] with p
    have hshift := congrArg (fun G : C(BetaNat, ℝ) ↦ G p)
      (betaIndicator_iterate_shift A n)
    simp only [ContinuousMap.comp_apply] at hshift
    change compactReturnWeight V c r hr p *
        (continuousAntiPart A Y).comp
          ⟨betaShift^[n], continuous_betaShift.iterate n⟩ p = (Q p).re
    simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk]
    have hshift' : betaIndicator A (betaShift^[n] p) =
        betaIndicator (shift A n) p := hshift
    change compactReturnWeight V c r hr p *
        (betaIndicator A (betaShift^[n] p) - (Y (betaShift^[n] p)).re) =
      (Q p).re
    rw [hshift']
    simp [Q, Wc, iterate_betaShiftComplex_apply]
    ring
  have hzero : inner ℂ W ((U ^ n) (F - b)) = 0 := by
    exact inner_bes_koopman_pow_sub_projection_eq_zero hmu F hWbes n
  have hdecomp : F - y = (F - b) + (b - y) := by abel
  have heq : inner ℂ W ((U ^ n) (F - y)) =
      inner ℂ W ((U ^ n) (b - y)) := by
    rw [hdecomp, map_add, inner_add_right, hzero, zero_add]
  have hbound := norm_inner_le_norm (𝕜 := ℂ) W ((U ^ n) (b - y))
  rw [(U ^ n).norm_map] at hbound
  have hWnorm : ‖W‖ ≤ 1 := norm_toLp_returnWeight_le_one V c r hr
  have hinnerbound : ‖inner ℂ W ((U ^ n) (F - y))‖ ≤ ‖b - y‖ := by
    rw [heq]
    exact hbound.trans (by nlinarith [norm_nonneg (b - y)])
  calc
    |∫ p, compactReturnWeight V c r hr p *
        (continuousAntiPart A Y).comp
          ⟨betaShift^[n], continuous_betaShift.iterate n⟩ p ∂mu| =
        |(inner ℂ W ((U ^ n) (F - y))).re| := congrArg abs hinter
    _ ≤ ‖inner ℂ W ((U ^ n) (F - y))‖ :=
      Complex.abs_re_le_norm _
    _ ≤ ‖b - y‖ := hinnerbound
    _ = ‖(betaBesClosed (mu := mu)).toSubmodule.starProjection
          (betaIndicatorL2 mu A) - ContinuousMap.toLp 2 mu ℂ Y‖ := rfl

end

end Erdos109

open CompactlySupported Filter Function MeasureTheory Set
open scoped BoundedContinuousFunction ComplexConjugate ENNReal NNReal Pointwise Topology

namespace Erdos109

noncomputable section

noncomputable local instance : MeasurableSpace BetaNat := borel BetaNat
local instance : BorelSpace BetaNat := ⟨rfl⟩

variable {mu : Measure BetaNat} [IsProbabilityMeasure mu]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem integral_compactReturnWeightedMeasure
    (V : K ≃ₗᵢ[ℂ] K) (c : K) (r : ℝ) (hr : 0 < r)
    (g : BetaNat → ℝ) :
    ∫ p, g p ∂compactReturnWeightedMeasure mu V c r hr =
      ∫ p, compactReturnWeight V c r hr p * g p ∂mu := by
  unfold compactReturnWeightedMeasure
  rw [integral_withDensity_eq_integral_toReal_smul]
  · apply integral_congr_ae
    filter_upwards [] with p
    rw [ENNReal.toReal_ofReal (compactReturnWeight_nonneg V c r hr p)]
    rfl
  · exact (ENNReal.measurable_ofReal.comp
      (compactReturnWeight V c r hr).continuous.measurable)
  · exact ae_of_all _ fun p ↦ ENNReal.ofReal_lt_top

theorem compactReturnWeightedMeasure_real_univ
    (V : K ≃ₗᵢ[ℂ] K) (c : K) (r : ℝ) (hr : 0 < r) :
    (compactReturnWeightedMeasure mu V c r hr).real Set.univ =
      ∫ p, compactReturnWeight V c r hr p ∂mu := by
  have hone := integral_compactReturnWeightedMeasure
    (mu := mu) V c r hr (fun _ ↦ (1 : ℝ))
  simpa only [integral_const, smul_eq_mul, mul_one, one_mul] using hone

/-- A finite weighted cross-average inherits the same normalized lower bound
from uniform bounds on each weighted translate. -/
theorem compactReturnWeighted_average_betaCrossAverage_lower
    (V : K ≃ₗᵢ[ℂ] K) (c : K) (r : ℝ) (hr : 0 < r)
    (d : ℝ) (hd : d = ∫ p, compactReturnWeight V c r hr p ∂mu)
    (hdpos : 0 < d)
    (N : ℕ) (hN : 0 < N)
    (h f : ℕ → ℝ) (H C e : ℝ)
    (hH : 0 ≤ H) (he : 0 ≤ e)
    (hh : ∀ n, |h n| ≤ H) (hf : ∀ n, |f n| ≤ C)
    (hsmall : ∀ n,
      |∫ p, compactReturnWeight V c r hr p *
        betaRightTranslate f C hf n p ∂mu| ≤ e) :
    -(H * e / d) ≤
      ⨍ p, betaCrossAverage N h f C hf p
        ∂compactReturnWeightedMeasure mu V c r hr := by
  let nu := compactReturnWeightedMeasure mu V c r hr
  have hmass : nu.real Set.univ = d := by
    rw [compactReturnWeightedMeasure_real_univ, ← hd]
  rw [average_eq, hmass]
  change -(H * e / d) ≤ d⁻¹ *
    ∫ p, betaCrossAverage N h f C hf p ∂nu
  rw [integral_compactReturnWeightedMeasure]
  have hinter :
      (∫ p, compactReturnWeight V c r hr p *
          betaCrossAverage N h f C hf p ∂mu) =
        realFinsetMean (Finset.range N) (fun n ↦ h n *
          ∫ p, compactReturnWeight V c r hr p *
            betaRightTranslate f C hf n p ∂mu) := by
    rw [realFinsetMean, Finset.card_range]
    have htermInt (n : ℕ) : Integrable (fun p : BetaNat ↦
        h n * (compactReturnWeight V c r hr p *
          betaRightTranslate f C hf n p)) mu :=
      (BoundedContinuousFunction.mkOfCompact
        ((h n) • ((compactReturnWeight V c r hr) *
          betaRightTranslate f C hf n))).integrable mu
    calc
      (∫ p, compactReturnWeight V c r hr p *
          betaCrossAverage N h f C hf p ∂mu) =
          ∫ p, (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N,
            h n * (compactReturnWeight V c r hr p *
              betaRightTranslate f C hf n p) ∂mu := by
        apply integral_congr_ae
        filter_upwards [] with p
        rw [betaCrossAverage_apply, realFinsetMean, Finset.card_range,
          div_eq_mul_inv]
        simp only [Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro n hn
        ring
      _ = (N : ℝ)⁻¹ * ∫ p, ∑ n ∈ Finset.range N,
            h n * (compactReturnWeight V c r hr p *
              betaRightTranslate f C hf n p) ∂mu :=
        integral_const_mul _ _
      _ = (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N,
            h n * ∫ p, compactReturnWeight V c r hr p *
              betaRightTranslate f C hf n p ∂mu := by
        rw [integral_finsetSum (Finset.range N)
          (fun n _hn ↦ htermInt n)]
        congr 1
        apply Finset.sum_congr rfl
        intro n hn
        exact integral_const_mul _ _
      _ = (∑ n ∈ Finset.range N, h n *
            ∫ p, compactReturnWeight V c r hr p *
              betaRightTranslate f C hf n p ∂mu) / (N : ℝ) := by ring
  rw [hinter, realFinsetMean, Finset.card_range]
  have hterm (n : ℕ) :
      -(H * e) ≤ h n *
        ∫ p, compactReturnWeight V c r hr p *
          betaRightTranslate f C hf n p ∂mu := by
    have hh' := hh n
    have hs' := hsmall n
    rcases abs_le.mp hh' with ⟨hhlo, hhhi⟩
    rcases abs_le.mp hs' with ⟨hslo, hshi⟩
    nlinarith
  have hsum : (-(H * e)) * (N : ℝ) ≤
      ∑ n ∈ Finset.range N, h n *
        ∫ p, compactReturnWeight V c r hr p *
          betaRightTranslate f C hf n p ∂mu := by
    calc
      (-(H * e)) * (N : ℝ) =
          ∑ _n ∈ Finset.range N, (-(H * e)) := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring
      _ ≤ ∑ n ∈ Finset.range N, h n *
          ∫ p, compactReturnWeight V c r hr p *
            betaRightTranslate f C hf n p ∂mu :=
        Finset.sum_le_sum fun n hn ↦ hterm n
  have hmean : -(H * e) ≤
      (∑ n ∈ Finset.range N, h n *
        ∫ p, compactReturnWeight V c r hr p *
          betaRightTranslate f C hf n p ∂mu) / (N : ℝ) := by
    rw [le_div_iff₀ (by exact_mod_cast hN)]
    simpa only [neg_mul] using hsum
  have hdinv : 0 < d⁻¹ := inv_pos.mpr hdpos
  calc
    -(H * e / d) = d⁻¹ * (-(H * e)) := by field_simp
    _ ≤ d⁻¹ * ((∑ n ∈ Finset.range N, h n *
        ∫ p, compactReturnWeight V c r hr p *
          betaRightTranslate f C hf n p ∂mu) / (N : ℝ)) :=
      mul_le_mul_of_nonneg_left hmean hdinv.le

end

end Erdos109

open Filter Function MeasureTheory ProbabilityTheory Set
open scoped ComplexConjugate

namespace Erdos109

noncomputable section

noncomputable local instance : MeasurableSpace BetaNat := borel BetaNat
local instance : BorelSpace BetaNat := ⟨rfl⟩

/-- The normalized complex mean over an initial interval. -/
noncomputable def complexPrefixMean (N : ℕ) (f : ℕ → ℂ) : ℂ :=
  (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, f n

/-- Finite Cauchy--Schwarz in the exact normalization used by the empirical
GNS construction. -/
theorem norm_complexPrefixMean_mul_le_sqrt
    (N : ℕ) (hN : 0 < N) (u : ℕ → ℂ) (z : ℕ → ℂ)
    (hu : ∀ n, ‖u n‖ ≤ 1) :
    ‖complexPrefixMean N (fun n ↦ u n * z n)‖ ≤
      Real.sqrt ((∑ n ∈ Finset.range N, ‖z n‖ ^ 2) / (N : ℝ)) := by
  let a : ℝ := ∑ n ∈ Finset.range N, ‖z n‖
  let b : ℝ := ∑ n ∈ Finset.range N, ‖z n‖ ^ 2
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hsum : ‖∑ n ∈ Finset.range N, u n * z n‖ ≤ a := by
    calc
      ‖∑ n ∈ Finset.range N, u n * z n‖ ≤
          ∑ n ∈ Finset.range N, ‖u n * z n‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ Finset.range N, ‖z n‖ := by
        apply Finset.sum_le_sum
        intro n hn
        rw [norm_mul]
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right (hu n) (norm_nonneg (z n))
      _ = a := rfl
  have hcs : a ^ 2 ≤ (N : ℝ) * b := by
    have hc := Finset.sum_mul_sq_le_sq_mul_sq
      (Finset.range N) (fun _n ↦ (1 : ℝ)) (fun n ↦ ‖z n‖)
    simpa only [one_mul, one_pow, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, mul_one, a, b] using hc
  have hab : 0 ≤ a := Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  have hb : 0 ≤ b := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have hdiv : a / (N : ℝ) ≤ Real.sqrt (b / (N : ℝ)) := by
    rw [Real.le_sqrt (div_nonneg hab hNreal.le) (div_nonneg hb hNreal.le)]
    rw [div_pow]
    rw [div_le_div_iff₀ (sq_pos_of_pos hNreal) hNreal]
    nlinarith
  calc
    ‖complexPrefixMean N (fun n ↦ u n * z n)‖ =
        (N : ℝ)⁻¹ * ‖∑ n ∈ Finset.range N, u n * z n‖ := by
      rw [complexPrefixMean, norm_mul, norm_inv, Complex.norm_natCast]
    _ ≤ (N : ℝ)⁻¹ * a :=
      mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hNreal.le)
    _ = a / (N : ℝ) := by rw [div_eq_mul_inv]; ring
    _ ≤ Real.sqrt (b / (N : ℝ)) := hdiv

noncomputable def continuousImagPart (Y : C(BetaNat, ℂ)) : C(BetaNat, ℝ) :=
  ⟨fun p ↦ (Y p).im, Complex.continuous_im.comp Y.continuous⟩

@[simp] theorem continuousRealPart_apply (Y : C(BetaNat, ℂ)) (p : BetaNat) :
    continuousRealPart Y p = (Y p).re := rfl

@[simp] theorem continuousImagPart_apply (Y : C(BetaNat, ℂ)) (p : BetaNat) :
    continuousImagPart Y p = (Y p).im := rfl

noncomputable def gramProduct (Z : ℕ → C(BetaNat, ℂ)) (i j : ℕ) :
    C(BetaNat, ℂ) := Z i * star (Z j)

noncomputable def gramTest (Z : ℕ → C(BetaNat, ℂ)) (n : ℕ) :
    C(BetaNat, ℝ) :=
  let tagged := Nat.unpair n
  let ij := Nat.unpair tagged.2
  if tagged.1 = 0 then continuousRealPart (gramProduct Z ij.1 ij.2)
  else continuousImagPart (gramProduct Z ij.1 ij.2)

@[simp] theorem gramTest_real (Z : ℕ → C(BetaNat, ℂ)) (i j : ℕ) :
    gramTest Z (Nat.pair 0 (Nat.pair i j)) =
      continuousRealPart (gramProduct Z i j) := by
  simp [gramTest]

@[simp] theorem gramTest_imag (Z : ℕ → C(BetaNat, ℂ)) (i j : ℕ) :
    gramTest Z (Nat.pair 1 (Nat.pair i j)) =
      continuousImagPart (gramProduct Z i j) := by
  simp [gramTest]

theorem integral_betaEmpirical_complex
    (N : ℕ) (hN : 0 < N) (P : C(BetaNat, ℂ)) :
    (∫ p, P p
        ∂((betaEmpirical N hN : ProbabilityMeasure BetaNat) : Measure BetaNat)) =
      complexPrefixMean N (fun n ↦ P (pure n)) := by
  let Pr := continuousRealPart P
  let Pi := continuousImagPart P
  have hPint : Integrable (fun p ↦ P p)
      ((betaEmpirical N hN : ProbabilityMeasure BetaNat) : Measure BetaNat) :=
    (BoundedContinuousFunction.mkOfCompact P).integrable _
  have hre := integral_betaEmpirical N hN Pr
  have him := integral_betaEmpirical N hN Pi
  have hsum :
      (∑ n ∈ Finset.range N, P (pure n)) =
        ((∑ n ∈ Finset.range N, (P (pure n)).re : ℝ) : ℂ) +
          ((∑ n ∈ Finset.range N, (P (pure n)).im : ℝ) : ℂ) * Complex.I := by
    calc
      (∑ n ∈ Finset.range N, P (pure n)) =
          ∑ n ∈ Finset.range N,
            (((P (pure n)).re : ℂ) + ((P (pure n)).im : ℂ) * Complex.I) := by
        apply Finset.sum_congr rfl
        intro n hn
        exact (Complex.re_add_im _).symm
      _ = (∑ n ∈ Finset.range N, ((P (pure n)).re : ℂ)) +
          ∑ n ∈ Finset.range N, ((P (pure n)).im : ℂ) * Complex.I := by
        rw [Finset.sum_add_distrib]
      _ = ((∑ n ∈ Finset.range N, (P (pure n)).re : ℝ) : ℂ) +
          ((∑ n ∈ Finset.range N, (P (pure n)).im : ℝ) : ℂ) * Complex.I := by
        push_cast
        rw [Finset.sum_mul]
  calc
    (∫ p, P p
        ∂((betaEmpirical N hN : ProbabilityMeasure BetaNat) : Measure BetaNat)) =
        ((∫ p, Pr p
          ∂((betaEmpirical N hN : ProbabilityMeasure BetaNat) : Measure BetaNat) : ℝ) : ℂ) +
        ((∫ p, Pi p
          ∂((betaEmpirical N hN : ProbabilityMeasure BetaNat) : Measure BetaNat) : ℝ) : ℂ) *
          Complex.I := by
      symm
      have hh := integral_re_add_im hPint
      change ((∫ p, Pr p
          ∂((betaEmpirical N hN : ProbabilityMeasure BetaNat) : Measure BetaNat) : ℝ) : ℂ) +
        ((∫ p, Pi p
          ∂((betaEmpirical N hN : ProbabilityMeasure BetaNat) : Measure BetaNat) : ℝ) : ℂ) *
          Complex.I = ∫ p, P p
            ∂((betaEmpirical N hN : ProbabilityMeasure BetaNat) : Measure BetaNat) at hh
      exact hh
    _ = ((realFinsetMean (Finset.range N) (fun n ↦ (P (pure n)).re) : ℝ) : ℂ) +
        ((realFinsetMean (Finset.range N) (fun n ↦ (P (pure n)).im) : ℝ) : ℂ) *
          Complex.I := by
      rw [hre, him]
      simp only [Pr, Pi, continuousRealPart_apply, continuousImagPart_apply,
        realFinsetMean, Finset.card_range]
    _ = complexPrefixMean N (fun n ↦ P (pure n)) := by
      rw [realFinsetMean, realFinsetMean, Finset.card_range,
        complexPrefixMean, hsum]
      push_cast
      ring

/-- One ordinary subsequence realizes the whole Gram matrix of a countable
family of continuous observables. -/
theorem exists_subseq_gram_tendsto_of_ultrafilter
    (N : ℕ → ℕ) (hNpos : ∀ k, 0 < N k)
    (q : Ultrafilter ℕ) (hq : (q : Filter ℕ) ≤ atTop)
    (mu : ProbabilityMeasure BetaNat)
    (hmu : Tendsto (fun k ↦ betaEmpirical (N k) (hNpos k))
      (q : Filter ℕ) (nhds mu))
    (Z : ℕ → C(BetaNat, ℂ)) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧ ∀ i j,
      Tendsto
        (fun k ↦ complexPrefixMean (N (phi k))
          (fun n ↦ Z i (pure n) * conj (Z j (pure n))))
        atTop
        (nhds (∫ p, gramProduct Z i j p ∂(mu : Measure BetaNat))) := by
  obtain ⟨phi, hphi, htests⟩ :=
    exists_subseq_integrals_tendsto_of_ultrafilter
      N hNpos q hq mu hmu (gramTest Z)
  refine ⟨phi, hphi, fun i j ↦ ?_⟩
  let P := gramProduct Z i j
  have hPint : Integrable (fun p ↦ P p) (mu : Measure BetaNat) := by
    change Integrable P (mu : Measure BetaNat)
    exact (BoundedContinuousFunction.mkOfCompact P).integrable _
  have hRe := htests (Nat.pair 0 (Nat.pair i j))
  have hIm := htests (Nat.pair 1 (Nat.pair i j))
  rw [gramTest_real] at hRe
  rw [gramTest_imag] at hIm
  have hcomplex := hRe.ofReal.add (hIm.ofReal.mul_const Complex.I)
  have hfun (k : ℕ) :
      complexPrefixMean (N (phi k))
          (fun n ↦ Z i (pure n) * conj (Z j (pure n))) =
        ((∫ p, continuousRealPart P p
          ∂((betaEmpirical (N (phi k)) (hNpos (phi k)) :
            ProbabilityMeasure BetaNat) : Measure BetaNat) : ℝ) : ℂ) +
        ((∫ p, continuousImagPart P p
          ∂((betaEmpirical (N (phi k)) (hNpos (phi k)) :
            ProbabilityMeasure BetaNat) : Measure BetaNat) : ℝ) : ℂ) *
          Complex.I := by
    calc
      complexPrefixMean (N (phi k))
          (fun n ↦ Z i (pure n) * conj (Z j (pure n))) =
          ∫ p, P p
            ∂((betaEmpirical (N (phi k)) (hNpos (phi k)) :
              ProbabilityMeasure BetaNat) : Measure BetaNat) := by
        rw [integral_betaEmpirical_complex]
        rfl
      _ = _ := by
        symm
        apply integral_re_add_im
        change Integrable P _
        exact (BoundedContinuousFunction.mkOfCompact P).integrable _
  have hlim :
      ((∫ p, continuousRealPart P p ∂(mu : Measure BetaNat) : ℝ) : ℂ) +
        ((∫ p, continuousImagPart P p ∂(mu : Measure BetaNat) : ℝ) : ℂ) *
          Complex.I = ∫ p, P p ∂(mu : Measure BetaNat) := by
    exact integral_re_add_im hPint
  rw [← hlim]
  exact hcomplex.congr' (Eventually.of_forall fun k ↦ by
    simpa only [P] using (hfun k).symm)

noncomputable def continuousFinsuppCombination
    (Z : ℕ → C(BetaNat, ℂ)) (d : ℕ →₀ ℂ) : C(BetaNat, ℂ) :=
  ∑ i ∈ d.support, (d i) • Z i

@[simp] theorem continuousFinsuppCombination_apply
    (Z : ℕ → C(BetaNat, ℂ)) (d : ℕ →₀ ℂ) (p : BetaNat) :
    continuousFinsuppCombination Z d p =
      ∑ i ∈ d.support, d i * Z i p := by
  simp [continuousFinsuppCombination, smul_eq_mul]

theorem continuousFinsuppCombination_toLp
    (mu : Measure BetaNat) [IsFiniteMeasure mu]
    (Z : ℕ → C(BetaNat, ℂ)) (d : ℕ →₀ ℂ) :
    ContinuousMap.toLp 2 mu ℂ (continuousFinsuppCombination Z d) =
      Finsupp.linearCombination ℂ
        (fun i ↦ ContinuousMap.toLp 2 mu ℂ (Z i)) d := by
  rw [Finsupp.linearCombination_apply]
  simp only [continuousFinsuppCombination, map_sum, map_smul]
  rfl

theorem gram_combination_apply
    (Z : ℕ → C(BetaNat, ℂ)) (d e : ℕ →₀ ℂ) (p : BetaNat) :
    continuousFinsuppCombination Z d p *
        conj (continuousFinsuppCombination Z e p) =
      ∑ i ∈ d.support, ∑ j ∈ e.support,
        (d i * conj (e j)) * (Z i p * conj (Z j p)) := by
  simp only [continuousFinsuppCombination_apply, map_sum, map_mul,
    starRingEnd_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem complexPrefixMean_gram_combination
    (N : ℕ) (Z : ℕ → C(BetaNat, ℂ)) (d e : ℕ →₀ ℂ) :
    complexPrefixMean N (fun n ↦
        continuousFinsuppCombination Z d (pure n) *
          conj (continuousFinsuppCombination Z e (pure n))) =
      ∑ i ∈ d.support, ∑ j ∈ e.support,
        (d i * conj (e j)) *
          complexPrefixMean N (fun n ↦ Z i (pure n) * conj (Z j (pure n))) := by
  unfold complexPrefixMean
  simp_rw [gram_combination_apply]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro n hn
  ring

theorem integral_gram_combination
    (mu : Measure BetaNat) [IsFiniteMeasure mu]
    (Z : ℕ → C(BetaNat, ℂ)) (d e : ℕ →₀ ℂ) :
    (∫ p, continuousFinsuppCombination Z d p *
        conj (continuousFinsuppCombination Z e p) ∂mu) =
      ∑ i ∈ d.support, ∑ j ∈ e.support,
        (d i * conj (e j)) * ∫ p, Z i p * conj (Z j p) ∂mu := by
  have hint (i j : ℕ) : Integrable (fun p ↦ Z i p * conj (Z j p)) mu :=
    (BoundedContinuousFunction.mkOfCompact (gramProduct Z i j)).integrable _
  apply Eq.trans (integral_congr_ae (ae_of_all _ fun p ↦
    gram_combination_apply Z d e p))
  rw [integral_finsetSum d.support (fun i _hi ↦
    integrable_finset_sum e.support fun j _hj ↦
      (hint i j).const_mul (d i * conj (e j)))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_finsetSum e.support (fun j _hj ↦
    (hint i j).const_mul (d i * conj (e j)))]
  apply Finset.sum_congr rfl
  intro j hj
  exact integral_const_mul _ _

theorem tendsto_complexPrefixMean_gram_combination
    {N : ℕ → ℕ} {mu : Measure BetaNat} [IsFiniteMeasure mu]
    (Z : ℕ → C(BetaNat, ℂ))
    (hgram : ∀ i j, Tendsto
      (fun k ↦ complexPrefixMean (N k)
        (fun n ↦ Z i (pure n) * conj (Z j (pure n))))
      atTop (nhds (∫ p, gramProduct Z i j p ∂mu)))
    (d e : ℕ →₀ ℂ) :
    Tendsto
      (fun k ↦ complexPrefixMean (N k) (fun n ↦
        continuousFinsuppCombination Z d (pure n) *
          conj (continuousFinsuppCombination Z e (pure n))))
      atTop
      (nhds (∫ p, continuousFinsuppCombination Z d p *
        conj (continuousFinsuppCombination Z e p) ∂mu)) := by
  have hsum := tendsto_finsetSum d.support fun i hi ↦
    tendsto_finsetSum e.support fun j hj ↦
      (hgram i j).const_mul (d i * conj (e j))
  rw [integral_gram_combination]
  exact hsum.congr' (Eventually.of_forall fun k ↦
    (complexPrefixMean_gram_combination (N k) Z d e).symm)

noncomputable def empiricalCombinationNorm
    (N : ℕ) (Z : ℕ → C(BetaNat, ℂ)) (d : ℕ →₀ ℂ) : ℝ :=
  Real.sqrt ((∑ n ∈ Finset.range N,
    ‖continuousFinsuppCombination Z d (pure n)‖ ^ 2) / (N : ℝ))

theorem complexPrefixMean_self_eq_secondMoment
    (N : ℕ) (hN : 0 < N) (G : C(BetaNat, ℂ)) :
    complexPrefixMean N (fun n ↦ G (pure n) * conj (G (pure n))) =
      (((∑ n ∈ Finset.range N, ‖G (pure n)‖ ^ 2) / (N : ℝ) : ℝ) : ℂ) := by
  unfold complexPrefixMean
  simp_rw [Complex.mul_conj]
  simp_rw [← Complex.sq_norm]
  push_cast
  rw [div_eq_mul_inv]
  ring

theorem integral_self_eq_norm_toLp_sq
    (mu : Measure BetaNat) [IsFiniteMeasure mu] (G : C(BetaNat, ℂ)) :
    (∫ p, G p * conj (G p) ∂mu) =
      ((‖ContinuousMap.toLp 2 mu ℂ G‖ ^ 2 : ℝ) : ℂ) := by
  rw [← ContinuousMap.inner_toLp]
  rw [inner_self_eq_norm_sq_to_K]
  norm_cast

theorem tendsto_empiricalCombinationNorm
    {N : ℕ → ℕ} (hNpos : ∀ k, 0 < N k)
    {mu : Measure BetaNat} [IsFiniteMeasure mu]
    (Z : ℕ → C(BetaNat, ℂ))
    (hgram : ∀ i j, Tendsto
      (fun k ↦ complexPrefixMean (N k)
        (fun n ↦ Z i (pure n) * conj (Z j (pure n))))
      atTop (nhds (∫ p, gramProduct Z i j p ∂mu)))
    (d : ℕ →₀ ℂ) :
    Tendsto (fun k ↦ empiricalCombinationNorm (N k) Z d) atTop
      (nhds ‖Finsupp.linearCombination ℂ
        (fun i ↦ ContinuousMap.toLp 2 mu ℂ (Z i)) d‖) := by
  let G := continuousFinsuppCombination Z d
  have hc := tendsto_complexPrefixMean_gram_combination Z hgram d d
  have hre := (Complex.continuous_re.tendsto _).comp hc
  change Tendsto
    (fun k ↦ (complexPrefixMean (N k) (fun n ↦
      G (pure n) * conj (G (pure n)))).re)
    atTop
    (nhds (∫ p, G p * conj (G p) ∂mu).re) at hre
  have hsecond : Tendsto
      (fun k ↦ (∑ n ∈ Finset.range (N k), ‖G (pure n)‖ ^ 2) / (N k : ℝ))
      atTop (nhds (‖ContinuousMap.toLp 2 mu ℂ G‖ ^ 2)) := by
    convert hre using 1
    · funext k
      rw [complexPrefixMean_self_eq_secondMoment (N k) (hNpos k) G]
      norm_cast
    · rw [integral_self_eq_norm_toLp_sq]
      norm_cast
  have hsqrt := (Real.continuous_sqrt.tendsto _).comp hsecond
  simpa [Function.comp_def, empiricalCombinationNorm, G,
    Real.sqrt_sq_eq_abs,
    abs_of_nonneg (norm_nonneg _), continuousFinsuppCombination_toLp] using hsqrt

theorem norm_complexPrefixMean_le
    (N : ℕ) (hN : 0 < N) (f : ℕ → ℂ) (C : ℝ)
    (hf : ∀ n, ‖f n‖ ≤ C) :
    ‖complexPrefixMean N f‖ ≤ C := by
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  calc
    ‖complexPrefixMean N f‖ =
        (N : ℝ)⁻¹ * ‖∑ n ∈ Finset.range N, f n‖ := by
      rw [complexPrefixMean, norm_mul, norm_inv, Complex.norm_natCast]
    _ ≤ (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, ‖f n‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _)
        (inv_nonneg.mpr hNreal.le)
    _ ≤ (N : ℝ)⁻¹ * ∑ _n ∈ Finset.range N, C := by
      apply mul_le_mul_of_nonneg_left
      · exact Finset.sum_le_sum fun n hn ↦ hf n
      · exact inv_nonneg.mpr hNreal.le
    _ = C := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp

theorem exists_subseq_tendsto_bounded_complex_array
    (a : ℕ → ℕ → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ k j, ‖a k j‖ ≤ C) :
    ∃ phi : ℕ → ℕ, ∃ l : ℕ → ℂ, StrictMono phi ∧
      (∀ j, Tendsto (fun k ↦ a (phi k) j) atTop (nhds (l j))) ∧
      ∀ j, ‖l j‖ ≤ C := by
  let x : ℕ → ℕ → Metric.closedBall (0 : ℂ) C := fun k j ↦
    ⟨a k j, by simpa only [mem_closedBall_zero_iff] using ha k j⟩
  let : CompactSpace (Metric.closedBall (0 : ℂ) C) :=
    isCompact_iff_compactSpace.mp (ProperSpace.isCompact_closedBall 0 C)
  obtain ⟨y, phi, hphi, hy⟩ := CompactSpace.tendsto_subseq x
  refine ⟨phi, fun j ↦ y j, hphi, ?_, fun j ↦ ?_⟩
  · intro j
    have hj := (continuous_subtype_val.tendsto (y j)).comp
      (hy.apply_nhds j)
    change Tendsto (fun k ↦ a (phi k) j) atTop
      (nhds ((y j : Metric.closedBall (0 : ℂ) C) : ℂ)) at hj
    exact hj
  · simpa only [mem_closedBall_zero_iff] using (y j).property

theorem complexPrefixMean_mul_combination
    (N : ℕ) (u : ℕ → ℂ) (Z : ℕ → C(BetaNat, ℂ)) (d : ℕ →₀ ℂ) :
    complexPrefixMean N (fun n ↦
        u n * continuousFinsuppCombination Z d (pure n)) =
      Finsupp.linearCombination ℂ
        (fun i ↦ complexPrefixMean N (fun n ↦ u n * Z i (pure n))) d := by
  rw [Finsupp.linearCombination_apply]
  unfold complexPrefixMean
  simp_rw [continuousFinsuppCombination_apply]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  change (∑ n ∈ Finset.range N, (N : ℂ)⁻¹ *
      (u n * (d i * Z i (pure n)))) =
    d i * ∑ n ∈ Finset.range N, (N : ℂ)⁻¹ * (u n * Z i (pure n))
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  ring

/-- Diagonal empirical correlations against a pointwise unit-bounded left
sequence define a genuine norm-one vector in the limiting `L²` space. -/
theorem exists_subseq_vector_representing_empirical_left
    (N : ℕ → ℕ) (hNpos : ∀ k, 0 < N k)
    (mu : Measure BetaNat) [IsFiniteMeasure mu]
    (Z : ℕ → C(BetaNat, ℂ))
    (hZ : ∀ i p, ‖Z i p‖ ≤ 1)
    (hgram : ∀ i j, Tendsto
      (fun k ↦ complexPrefixMean (N k)
        (fun n ↦ Z i (pure n) * conj (Z j (pure n))))
      atTop (nhds (∫ p, gramProduct Z i j p ∂mu)))
    (u : ℕ → ℂ) (hu : ∀ n, ‖u n‖ ≤ 1) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧ ∃ c : ℕ → ℂ, ∃ y : BetaL2 mu,
      ‖y‖ ≤ 1 ∧
      (∀ i, Tendsto
        (fun k ↦ complexPrefixMean (N (phi k))
          (fun n ↦ u n * Z i (pure n)))
        atTop (nhds (c i))) ∧
      ∀ i, inner ℂ y (ContinuousMap.toLp 2 mu ℂ (Z i)) = c i := by
  let a : ℕ → ℕ → ℂ := fun k i ↦
    complexPrefixMean (N k) (fun n ↦ u n * Z i (pure n))
  have ha (k i : ℕ) : ‖a k i‖ ≤ 1 := by
    apply norm_complexPrefixMean_le (N k) (hNpos k) _ 1
    intro n
    rw [norm_mul]
    calc
      ‖u n‖ * ‖Z i (pure n)‖ ≤ 1 * 1 :=
        mul_le_mul (hu n) (hZ i (pure n)) (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  obtain ⟨phi, c, hphi, hc, hcBound⟩ :=
    exists_subseq_tendsto_bounded_complex_array a 1 zero_le_one ha
  refine ⟨phi, hphi, c, ?_⟩
  let v : ℕ → BetaL2 mu := fun i ↦ ContinuousMap.toLp 2 mu ℂ (Z i)
  let L : ℕ → (ℕ →₀ ℂ) → ℂ := fun k d ↦
    complexPrefixMean (N (phi k)) (fun n ↦
      u n * continuousFinsuppCombination Z d (pure n))
  let Q : ℕ → (ℕ →₀ ℂ) → ℝ := fun k d ↦
    empiricalCombinationNorm (N (phi k)) Z d
  have hL (d : ℕ →₀ ℂ) : Tendsto (fun k ↦ L k d) atTop
      (nhds (Finsupp.linearCombination ℂ c d)) := by
    have hs := tendsto_finsetSum d.support fun i hi ↦
      (hc i).const_mul (d i)
    have hs' : Tendsto
        (fun k ↦ Finsupp.linearCombination ℂ
          (fun i ↦ complexPrefixMean (N (phi k))
            (fun n ↦ u n * Z i (pure n))) d)
        atTop (nhds (Finsupp.linearCombination ℂ c d)) := by
      change Tendsto
        (fun k ↦ ∑ i ∈ d.support, d i *
          complexPrefixMean (N (phi k)) (fun n ↦ u n * Z i (pure n)))
        atTop (nhds (∑ i ∈ d.support, d i * c i))
      exact hs
    exact hs'.congr' (Eventually.of_forall fun k ↦ by
      simpa only [L] using
        (complexPrefixMean_mul_combination (N (phi k)) u Z d).symm)
  have hQ (d : ℕ →₀ ℂ) : Tendsto (fun k ↦ Q k d) atTop
      (nhds ‖Finsupp.linearCombination ℂ v d‖) := by
    have hg : ∀ i j, Tendsto
        (fun k ↦ complexPrefixMean (N (phi k))
          (fun n ↦ Z i (pure n) * conj (Z j (pure n))))
        atTop (nhds (∫ p, gramProduct Z i j p ∂mu)) :=
      fun i j ↦ (hgram i j).comp hphi.tendsto_atTop
    simpa only [Q, v] using
      tendsto_empiricalCombinationNorm (fun k ↦ hNpos (phi k)) Z hg d
  have hbound (k : ℕ) (d : ℕ →₀ ℂ) : ‖L k d‖ ≤ Q k d := by
    exact norm_complexPrefixMean_mul_le_sqrt (N (phi k)) (hNpos (phi k))
      u (fun n ↦ continuousFinsuppCombination Z d (pure n)) hu
  obtain ⟨y, hy, hyc⟩ := exists_vector_representing_limit_family_functional
    v c L Q hL hQ hbound
  exact ⟨y, hy, hc, by simpa only [v] using hyc⟩

end

end Erdos109

open CompactlySupported Filter Function MeasureTheory Set
open scoped BoundedContinuousFunction ComplexConjugate ENNReal NNReal Pointwise Topology

namespace Erdos109

noncomputable section

noncomputable local instance : MeasurableSpace BetaNat := borel BetaNat
local instance : BorelSpace BetaNat := ⟨rfl⟩

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Strong ultrafilter limit of a totally bounded unitary orbit. -/
noncomputable def compactOrbitLimit
    (U : H ≃ₗᵢ[ℂ] H) (c : H)
    (hc : TotallyBounded (Set.range fun n : ℕ ↦ (U ^ n) c))
    (p : BetaNat) : H := by
  letI : CompactSpace (compactOrbit U c) :=
    isCompact_iff_compactSpace.mp (isCompact_compactOrbit U c hc)
  exact (Ultrafilter.extend (compactOrbitPoint U c) p : compactOrbit U c).1

theorem continuous_compactOrbitLimit
    (U : H ≃ₗᵢ[ℂ] H) (c : H)
    (hc : TotallyBounded (Set.range fun n : ℕ ↦ (U ^ n) c)) :
    Continuous (compactOrbitLimit U c hc) := by
  let : CompactSpace (compactOrbit U c) :=
    isCompact_iff_compactSpace.mp (isCompact_compactOrbit U c hc)
  change Continuous (fun p ↦
    (Ultrafilter.extend (compactOrbitPoint U c) p : compactOrbit U c).1)
  exact continuous_subtype_val.comp (continuous_ultrafilter_extend _)

@[simp] theorem compactOrbitLimit_pure
    (U : H ≃ₗᵢ[ℂ] H) (c : H)
    (hc : TotallyBounded (Set.range fun n : ℕ ↦ (U ^ n) c)) (n : ℕ) :
    compactOrbitLimit U c hc (pure n) = (U ^ n) c := by
  let : CompactSpace (compactOrbit U c) :=
    isCompact_iff_compactSpace.mp (isCompact_compactOrbit U c hc)
  simp [compactOrbitLimit]

theorem norm_compactOrbitLimit
    (U : H ≃ₗᵢ[ℂ] H) (c : H)
    (hc : TotallyBounded (Set.range fun n : ℕ ↦ (U ^ n) c)) (p : BetaNat) :
    ‖compactOrbitLimit U c hc p‖ = ‖c‖ := by
  let D : C(BetaNat, ℝ) :=
    ⟨fun p ↦ ‖compactOrbitLimit U c hc p‖,
      (continuous_compactOrbitLimit U c hc).norm⟩
  let K : C(BetaNat, ℝ) := ⟨fun _ ↦ ‖c‖, continuous_const⟩
  have heq : D = K := by
    apply ContinuousMap.ext
    apply congrFun
    apply (denseRange_pure : DenseRange (pure : ℕ → BetaNat)).equalizer
    · exact D.continuous
    · fun_prop
    funext n
    change ‖compactOrbitLimit U c hc (pure n)‖ = ‖c‖
    rw [compactOrbitLimit_pure, (U ^ n).norm_map]
  have hp := congrArg (fun f : C(BetaNat, ℝ) ↦ f p) heq
  change ‖compactOrbitLimit U c hc p‖ = ‖c‖ at hp
  exact hp

theorem closure_pure_image (E : Set ℕ) :
    closure (pure '' E : Set BetaNat) = betaEvent E := by
  apply Set.Subset.antisymm
  · apply closure_minimal
    · rintro _ ⟨n, hn, rfl⟩
      exact (pure_mem_betaEvent_iff E n).2 hn
    · exact (betaEvent_isClopen E).1
  · intro p hp
    rw [mem_closure_iff]
    intro O hO hpO
    have hnonempty : (O ∩ betaEvent E).Nonempty := ⟨p, hpO, hp⟩
    have hdense : Dense (Set.range (pure : ℕ → BetaNat)) := denseRange_pure
    obtain ⟨q, hqrange, hqopen⟩ :=
      hdense.exists_mem_open (hO.inter (betaEvent_isClopen E).2) hnonempty
    rcases hqrange with ⟨n, rfl⟩
    refine ⟨pure n, hqopen.1, ?_⟩
    exact ⟨n, (pure_mem_betaEvent_iff E n).1 hqopen.2, rfl⟩

theorem dist_compactOrbitLimit_le_of_mem
    (U : H ≃ₗᵢ[ℂ] H) (c : H)
    (hc : TotallyBounded (Set.range fun n : ℕ ↦ (U ^ n) c))
    (p : BetaNat) (r : ℝ)
    (hp : {n : ℕ | dist ((U ^ n) c) c < r} ∈ (p : Filter ℕ)) :
    dist (compactOrbitLimit U c hc p) c ≤ r := by
  let E : Set ℕ := {n : ℕ | dist ((U ^ n) c) c < r}
  have hpE : p ∈ betaEvent E := by
    change betaMembership E p = true
    exact (betaMembership_eq_true_iff E p).2 hp
  have hpclosure : p ∈ closure (pure '' E : Set BetaNat) := by
    rw [closure_pure_image]
    exact hpE
  have hclosed : IsClosed {q : BetaNat |
      dist (compactOrbitLimit U c hc q) c ≤ r} :=
    isClosed_Iic.preimage ((continuous_compactOrbitLimit U c hc).dist continuous_const)
  apply closure_minimal _ hclosed hpclosure
  rintro _ ⟨n, hn, rfl⟩
  have hn' : dist ((U ^ n) c) c < r := hn
  change dist (compactOrbitLimit U c hc (pure n)) c ≤ r
  rw [compactOrbitLimit_pure]
  exact le_of_lt hn'

/-! The arithmetic right-ultrafilter shift of a continuous observable. -/

noncomputable def betaOrbitAt (Y : C(BetaNat, ℂ)) (p : BetaNat) :
    C(BetaNat, ℂ) :=
  betaExtendComplex (fun n ↦ Y (betaShift^[n] p)) ‖Y‖
    (fun n ↦ Y.norm_coe_le_norm _)

@[simp] theorem betaOrbitAt_pure_apply
    (Y : C(BetaNat, ℂ)) (p : BetaNat) (n : ℕ) :
    betaOrbitAt Y p (pure n) = Y (betaShift^[n] p) := by
  simp [betaOrbitAt]

theorem betaOrbitAt_zero (p : BetaNat) : betaOrbitAt 0 p = 0 := by
  apply ContinuousMap.ext
  apply congrFun
  apply (denseRange_pure : DenseRange (pure : ℕ → BetaNat)).equalizer
  · exact (betaOrbitAt 0 p).continuous
  · fun_prop
  funext n
  simp

theorem betaOrbitAt_add (Y Z : C(BetaNat, ℂ)) (p : BetaNat) :
    betaOrbitAt (Y + Z) p = betaOrbitAt Y p + betaOrbitAt Z p := by
  apply ContinuousMap.ext
  apply congrFun
  apply (denseRange_pure : DenseRange (pure : ℕ → BetaNat)).equalizer
  · exact (betaOrbitAt (Y + Z) p).continuous
  · exact (betaOrbitAt Y p + betaOrbitAt Z p).continuous
  funext n
  simp

theorem betaOrbitAt_smul (a : ℂ) (Y : C(BetaNat, ℂ)) (p : BetaNat) :
    betaOrbitAt (a • Y) p = a • betaOrbitAt Y p := by
  apply ContinuousMap.ext
  apply congrFun
  apply (denseRange_pure : DenseRange (pure : ℕ → BetaNat)).equalizer
  · exact (betaOrbitAt (a • Y) p).continuous
  · exact (a • betaOrbitAt Y p).continuous
  funext n
  simp

theorem betaCharacter_iterate_shift_apply (z : Circle) (n : ℕ) (p : BetaNat) :
    betaCharacter z (betaShift^[n] p) =
      ((z : ℂ) ^ n) * betaCharacter z p := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      have hs : betaCharacter z (betaShift (betaShift^[n] p)) =
          (z : ℂ) * betaCharacter z (betaShift^[n] p) := by
        have hs0 := congrArg (fun Y : C(BetaNat, ℂ) ↦ Y (betaShift^[n] p))
          (betaCharacter_shift z)
        change betaCharacter z (betaShift (betaShift^[n] p)) =
          (z : ℂ) * betaCharacter z (betaShift^[n] p) at hs0
        exact hs0
      rw [hs, ih, pow_succ']
      ring

theorem betaCharacter_iterate_shift (z : Circle) (n : ℕ) :
    betaShiftComplex^[n] (betaCharacter z) =
      ((z : ℂ) ^ n) • betaCharacter z := by
  apply ContinuousMap.ext
  intro p
  rw [iterate_betaShiftComplex_apply, betaCharacter_iterate_shift_apply]
  rfl

theorem betaOrbitAt_character (z : Circle) (p : BetaNat) :
    betaOrbitAt (betaCharacter z) p =
      betaCharacter z p • betaCharacter z := by
  apply ContinuousMap.ext
  apply congrFun
  apply (denseRange_pure : DenseRange (pure : ℕ → BetaNat)).equalizer
  · exact (betaOrbitAt (betaCharacter z) p).continuous
  · exact (betaCharacter z p • betaCharacter z).continuous
  funext n
  change betaOrbitAt (betaCharacter z) p (pure n) =
    (betaCharacter z p • betaCharacter z) (pure n)
  rw [betaOrbitAt_pure_apply]
  have hs := congrArg (fun Y : C(BetaNat, ℂ) ↦ Y p)
    (betaCharacter_iterate_shift z n)
  rw [iterate_betaShiftComplex_apply] at hs
  simpa only [ContinuousMap.smul_apply, betaCharacter_pure, smul_eq_mul,
    mul_comm] using hs

theorem norm_betaCharacter (z : Circle) (p : BetaNat) :
    ‖betaCharacter z p‖ = 1 := by
  let D : C(BetaNat, ℝ) :=
    ⟨fun q ↦ ‖betaCharacter z q‖, (betaCharacter z).continuous.norm⟩
  have hD : D = (1 : C(BetaNat, ℝ)) := by
    apply ContinuousMap.ext
    apply congrFun
    apply (denseRange_pure : DenseRange (pure : ℕ → BetaNat)).equalizer
    · exact D.continuous
    · fun_prop
    funext n
    change ‖betaCharacter z (pure n)‖ = 1
    rw [betaCharacter_pure, norm_pow, Circle.norm_coe, one_pow]
  exact congrArg (fun F : C(BetaNat, ℝ) ↦ F p) hD

theorem continuous_betaOrbitAt_toLp
    {mu : Measure BetaNat} [IsFiniteMeasure mu]
    {Y : C(BetaNat, ℂ)} (hY : Y ∈ betaCharacterSpanC) :
    Continuous (fun p ↦ ContinuousMap.toLp 2 mu ℂ (betaOrbitAt Y p)) := by
  induction hY using Submodule.span_induction with
  | mem Y hY =>
      rcases hY with ⟨z, rfl⟩
      simp_rw [betaOrbitAt_character]
      simp_rw [map_smul]
      exact (betaCharacter z).continuous.smul
        (continuous_const : Continuous fun _ : BetaNat ↦
          ContinuousMap.toLp 2 mu ℂ (betaCharacter z))
  | zero =>
      simp_rw [betaOrbitAt_zero, map_zero]
      exact continuous_const
  | add Y Z _ _ hY hZ =>
      simp_rw [betaOrbitAt_add, map_add]
      exact hY.add hZ
  | smul a Y _ hY =>
      simp_rw [betaOrbitAt_smul, map_smul]
      exact (continuous_const : Continuous fun _ : BetaNat ↦ a).smul hY

theorem betaOrbitAt_mem_characterSpan
    {Y : C(BetaNat, ℂ)} (hY : Y ∈ betaCharacterSpanC) (p : BetaNat) :
    betaOrbitAt Y p ∈ betaCharacterSpanC := by
  induction hY using Submodule.span_induction with
  | mem Y hY =>
      rcases hY with ⟨z, rfl⟩
      rw [betaOrbitAt_character]
      exact (betaCharacterSpanC).smul_mem _
        (Submodule.subset_span (Set.mem_range_self z))
  | zero => simpa only [betaOrbitAt_zero] using (betaCharacterSpanC).zero_mem
  | add Y Z _ _ hY hZ =>
      rw [betaOrbitAt_add]
      exact (betaCharacterSpanC).add_mem hY hZ
  | smul a Y _ hY =>
      rw [betaOrbitAt_smul]
      exact (betaCharacterSpanC).smul_mem a hY

theorem betaOrbitAt_pure
    (Y : C(BetaNat, ℂ)) (m : ℕ) :
    betaOrbitAt Y (pure m) = betaShiftComplex^[m] Y := by
  apply ContinuousMap.ext
  apply congrFun
  apply (denseRange_pure : DenseRange (pure : ℕ → BetaNat)).equalizer
  · exact (betaOrbitAt Y (pure m)).continuous
  · exact (betaShiftComplex^[m] Y).continuous
  funext n
  change betaOrbitAt Y (pure m) (pure n) = (betaShiftComplex^[m] Y) (pure n)
  rw [betaOrbitAt_pure_apply, iterate_betaShiftComplex_apply]
  rw [iterate_betaShift_pure, iterate_betaShift_pure]
  congr 2
  omega

theorem characterSpan_toLp_mem_eigenSpan
    {mu : Measure BetaNat} [IsProbabilityMeasure mu]
    (hmu : MeasurePreserving betaShift mu mu)
    {Y : C(BetaNat, ℂ)} (hY : Y ∈ betaCharacterSpanC) :
    ContinuousMap.toLp 2 mu ℂ Y ∈ unitaryEigenSpan (betaKoopman hmu) := by
  induction hY using Submodule.span_induction with
  | mem Y hY =>
      rcases hY with ⟨z, rfl⟩
      exact Submodule.subset_span ⟨z, betaKoopman_character hmu z⟩
  | zero => simp
  | add Y Z _ _ hY hZ => simpa using (unitaryEigenSpan _).add_mem hY hZ
  | smul a Y _ hY => simpa using (unitaryEigenSpan _).smul_mem a hY

theorem characterSpan_orbit_totallyBounded
    {mu : Measure BetaNat} [IsProbabilityMeasure mu]
    (hmu : MeasurePreserving betaShift mu mu)
    {Y : C(BetaNat, ℂ)} (hY : Y ∈ betaCharacterSpanC) :
    TotallyBounded (Set.range fun n : ℕ ↦
      (betaKoopman hmu ^ n) (ContinuousMap.toLp 2 mu ℂ Y)) := by
  change ContinuousMap.toLp 2 mu ℂ Y ∈
    unitaryAlmostPeriodicSubmodule (betaKoopman hmu)
  exact unitaryEigenSpan_le_almostPeriodic _
    (characterSpan_toLp_mem_eigenSpan hmu hY)

theorem toLp_betaOrbitAt_eq_compactOrbitLimit
    {mu : Measure BetaNat} [IsProbabilityMeasure mu]
    (hmu : MeasurePreserving betaShift mu mu)
    {Y : C(BetaNat, ℂ)} (hY : Y ∈ betaCharacterSpanC) (p : BetaNat) :
    ContinuousMap.toLp 2 mu ℂ (betaOrbitAt Y p) =
      compactOrbitLimit (betaKoopman hmu) (ContinuousMap.toLp 2 mu ℂ Y)
        (characterSpan_orbit_totallyBounded hmu hY) p := by
  let left : BetaNat → BetaL2 mu := fun q ↦
    ContinuousMap.toLp 2 mu ℂ (betaOrbitAt Y q)
  let right : BetaNat → BetaL2 mu :=
    compactOrbitLimit (betaKoopman hmu) (ContinuousMap.toLp 2 mu ℂ Y)
      (characterSpan_orbit_totallyBounded hmu hY)
  have heq : left = right := by
    apply (denseRange_pure : DenseRange (pure : ℕ → BetaNat)).equalizer
    · exact continuous_betaOrbitAt_toLp hY
    · exact continuous_compactOrbitLimit _ _ _
    funext n
    change ContinuousMap.toLp 2 mu ℂ (betaOrbitAt Y (pure n)) =
      compactOrbitLimit (betaKoopman hmu) (ContinuousMap.toLp 2 mu ℂ Y)
        (characterSpan_orbit_totallyBounded hmu hY) (pure n)
    rw [betaOrbitAt_pure, compactOrbitLimit_pure]
    exact (betaKoopman_pow_continuousMap hmu Y n).symm
  exact congrFun heq p

/-- Gram convergence extends from a countable generating family to an
ultrafilter-shifted character polynomial as soon as that polynomial has
been expressed in the same algebraic span. -/
theorem tendsto_prefixMean_generator_mul_betaOrbitAt
    {N : ℕ → ℕ} {mu : Measure BetaNat} [IsFiniteMeasure mu]
    (Z : ℕ → C(BetaNat, ℂ))
    (hgram : ∀ i j, Tendsto
      (fun k ↦ complexPrefixMean (N k)
        (fun n ↦ Z i (pure n) * conj (Z j (pure n))))
      atTop (nhds (∫ p, gramProduct Z i j p ∂mu)))
    (i : ℕ) (Y : C(BetaNat, ℂ)) (p : BetaNat)
    (hspan : betaOrbitAt Y p ∈ Submodule.span ℂ (Set.range Z)) :
    Tendsto
      (fun k ↦ complexPrefixMean (N k) (fun n ↦
        Z i (pure n) * conj (betaOrbitAt Y p (pure n))))
      atTop
      (nhds (∫ q, Z i q * conj (betaOrbitAt Y p q) ∂mu)) := by
  obtain ⟨d, hd⟩ :=
    Finsupp.mem_span_range_iff_exists_finsupp.mp hspan
  have hcombo : continuousFinsuppCombination Z d = betaOrbitAt Y p := by
    change (∑ i ∈ d.support, d i • Z i) = betaOrbitAt Y p
    change (d.sum fun i a ↦ a • Z i) = betaOrbitAt Y p at hd
    exact hd
  let e : ℕ →₀ ℂ := Finsupp.single i 1
  have he : continuousFinsuppCombination Z e = Z i := by
    simp [e, continuousFinsuppCombination]
  have ht := tendsto_complexPrefixMean_gram_combination Z hgram e d
  rw [he, hcombo] at ht
  exact ht

end

end Erdos109

open CompactlySupported Filter Function MeasureTheory Set
open scoped BoundedContinuousFunction ComplexConjugate ENNReal NNReal Pointwise Topology

namespace Erdos109

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem finsetDensity_large_inner_le_correlationAverage
    (U : H ≃ₗᵢ[ℂ] H) (x y : H) (M : ℕ) (hM : 0 < M)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    finsetDensity (Finset.range M)
        {n | epsilon ≤ ‖inner ℂ y ((U ^ n) x)‖} ≤
      epsilon⁻¹ * unitaryCorrelationAverage U x y M := by
  rw [← realFinsetMean_indicator]
  unfold realFinsetMean unitaryCorrelationAverage
  rw [Finset.card_range]
  have hpoint (n : ℕ) :
      realIndicator {m | epsilon ≤ ‖inner ℂ y ((U ^ m) x)‖} n ≤
        epsilon⁻¹ * ‖inner ℂ y ((unitaryOperator U ^ n) x)‖ := by
    rw [unitaryOperator_pow_apply]
    by_cases hn : epsilon ≤ ‖inner ℂ y ((U ^ n) x)‖
    · rw [realIndicator_apply_mem hn]
      rw [one_le_inv_mul₀ hepsilon]
      exact hn
    · rw [realIndicator_apply_notMem hn]
      positivity
  calc
    (∑ n ∈ Finset.range M,
        realIndicator {m | epsilon ≤ ‖inner ℂ y ((U ^ m) x)‖} n) / (M : ℝ) ≤
        (∑ n ∈ Finset.range M,
          epsilon⁻¹ * ‖inner ℂ y ((unitaryOperator U ^ n) x)‖) / (M : ℝ) := by
      apply div_le_div_of_nonneg_right
      · exact Finset.sum_le_sum fun n hn ↦ hpoint n
      · positivity
    _ = epsilon⁻¹ * ((M : ℝ)⁻¹ *
        ∑ n ∈ Finset.range M,
          ‖inner ℂ y ((unitaryOperator U ^ n) x)‖) := by
      rw [← Finset.mul_sum]
      field_simp

theorem hasDensityAlong_large_weak_correlation_zero
    (U : H ≃ₗᵢ[ℂ] H) (F y : H)
    (N : ℕ → ℕ) (hNpos : ∀ k, 0 < N k)
    (hNtop : Tendsto N atTop atTop)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    HasDensityAlong (fun k ↦ Finset.range (N k))
      {n | epsilon ≤ ‖inner ℂ y ((U ^ n) (unitaryWeakPart U F))‖} 0 := by
  have hcorr := (tendsto_unitaryWeakPart_correlation_average U F y).comp hNtop
  have hupper : Tendsto
      (fun k ↦ epsilon⁻¹ *
        unitaryCorrelationAverage U (unitaryWeakPart U F) y (N k))
      atTop (nhds 0) := by
    simpa only [Function.comp_apply, mul_zero] using hcorr.const_mul epsilon⁻¹
  apply squeeze_zero
  · exact fun k ↦ finsetDensity_nonneg _ _
  · exact fun k ↦ finsetDensity_large_inner_le_correlationAverage
      U (unitaryWeakPart U F) y (N k) (hNpos k) epsilon hepsilon
  · exact hupper

theorem essential_mem_small_weak_correlation
    (U : H ≃ₗᵢ[ℂ] H) (F y : H)
    (N : ℕ → ℕ) (hNpos : ∀ k, 0 < N k)
    (hNtop : Tendsto N atTop atTop)
    (p : Ultrafilter ℕ)
    (hp : (p : Filter ℕ) ≤ densityOneFilter (fun k ↦ Finset.range (N k)))
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    {n | ‖inner ℂ y ((U ^ n) (unitaryWeakPart U F))‖ < epsilon} ∈
      (p : Filter ℕ) := by
  apply hp
  change HasDensityAlong (fun k ↦ Finset.range (N k))
    {n | ‖inner ℂ y ((U ^ n) (unitaryWeakPart U F))‖ < epsilon}ᶜ 0
  convert hasDensityAlong_large_weak_correlation_zero
    U F y N hNpos hNtop epsilon hepsilon using 1
  ext n
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt]

end

end Erdos109

open CompactlySupported Filter Function MeasureTheory Set
open scoped BoundedContinuousFunction ComplexConjugate ENNReal NNReal Pointwise Topology

namespace Erdos109

noncomputable section

noncomputable local instance : MeasurableSpace BetaNat := borel BetaNat
local instance : BorelSpace BetaNat := ⟨rfl⟩
noncomputable local instance : DecidableEq C(BetaNat, ℂ) := Classical.decEq _

theorem exists_common_finite_character_generators
    {Y G : C(BetaNat, ℂ)}
    (hY : Y ∈ betaCharacterSpanC) (hG : G ∈ betaCharacterSpanC) :
    ∃ W : Finset C(BetaNat, ℂ),
      (W : Set C(BetaNat, ℂ)) ⊆ Set.range betaCharacter ∧
      Y ∈ Submodule.span ℂ (W : Set C(BetaNat, ℂ)) ∧
      G ∈ Submodule.span ℂ (W : Set C(BetaNat, ℂ)) := by
  change Y ∈ Submodule.span ℂ (Set.range betaCharacter) at hY
  change G ∈ Submodule.span ℂ (Set.range betaCharacter) at hG
  obtain ⟨WY, hWYsub, hYWY⟩ := Submodule.mem_span_finite_of_mem_span hY
  obtain ⟨WG, hWGsub, hGWG⟩ := Submodule.mem_span_finite_of_mem_span hG
  refine ⟨WY ∪ WG, ?_, ?_, ?_⟩
  · intro w hw
    rcases Finset.mem_union.mp hw with hw | hw
    · exact hWYsub hw
    · exact hWGsub hw
  · exact (Submodule.span_mono (by
      intro w hw
      exact Finset.mem_union_left WG hw)) hYWY
  · exact (Submodule.span_mono (by
      intro w hw
      exact Finset.mem_union_right WY hw)) hGWG

/-- Countable family containing a clipped compact observable, every shift of
the indicator, and a prescribed finite set of characters. -/
noncomputable def mrrGeneratorFamily
    (A : Set ℕ) (Hc : C(BetaNat, ℂ))
    (W : Finset C(BetaNat, ℂ)) : ℕ → C(BetaNat, ℂ)
  | 0 => Hc
  | n + 1 =>
      let tagged := Nat.unpair n
      if tagged.1 = 0 then betaIndicatorComplex (shift A tagged.2)
      else W.toList.getD tagged.2 0

@[simp] theorem mrrGeneratorFamily_zero
    (A : Set ℕ) (Hc : C(BetaNat, ℂ)) (W : Finset C(BetaNat, ℂ)) :
    mrrGeneratorFamily A Hc W 0 = Hc := rfl

@[simp] theorem mrrGeneratorFamily_row
    (A : Set ℕ) (Hc : C(BetaNat, ℂ))
    (W : Finset C(BetaNat, ℂ)) (m : ℕ) :
    mrrGeneratorFamily A Hc W (Nat.pair 0 m + 1) =
      betaIndicatorComplex (shift A m) := by
  simp [mrrGeneratorFamily]

theorem list_getD_mem_or_zero
    {alpha : Type*} [DecidableEq alpha] [Zero alpha]
    (L : List alpha) (n : ℕ) : L.getD n 0 ∈ L ∨ L.getD n 0 = 0 := by
  by_cases hn : n < L.length
  · left
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn]
    simp only [Option.getD_some]
    exact List.getElem_mem hn
  · right
    rw [List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (Nat.le_of_not_gt hn)]
    rfl

theorem mrrGeneratorFamily_norm_le_one
    (A : Set ℕ) (Hc : C(BetaNat, ℂ))
    (hHc : ∀ p, ‖Hc p‖ ≤ 1)
    (W : Finset C(BetaNat, ℂ))
    (hW : (W : Set C(BetaNat, ℂ)) ⊆ Set.range betaCharacter) :
    ∀ i p, ‖mrrGeneratorFamily A Hc W i p‖ ≤ 1 := by
  intro i p
  cases i with
  | zero => exact hHc p
  | succ n =>
      rw [mrrGeneratorFamily]
      split_ifs
      · change ‖(betaIndicator (shift A (Nat.unpair n).2) p : ℂ)‖ ≤ 1
        by_cases hp : betaMembership (shift A (Nat.unpair n).2) p = true <;>
          simp [betaIndicator, hp]
      · rcases list_getD_mem_or_zero W.toList (Nat.unpair n).2 with hw | hw
        · have hwW : W.toList.getD (Nat.unpair n).2 0 ∈ W :=
            (Finset.mem_toList).1 hw
          rcases hW hwW with ⟨z, hz⟩
          rw [← hz, norm_betaCharacter]
        · rw [hw]
          simp

theorem finiteCharacters_le_generatorSpan
    (A : Set ℕ) (Hc : C(BetaNat, ℂ))
    (W : Finset C(BetaNat, ℂ)) :
    Submodule.span ℂ (W : Set C(BetaNat, ℂ)) ≤
      Submodule.span ℂ (Set.range (mrrGeneratorFamily A Hc W)) := by
  apply Submodule.span_mono
  intro w hw
  have hwL : w ∈ W.toList := (Finset.mem_toList).2 hw
  rw [List.mem_iff_getElem] at hwL
  obtain ⟨n, hn, hwn⟩ := hwL
  refine ⟨Nat.pair 1 n + 1, ?_⟩
  simp only [mrrGeneratorFamily, Nat.unpair_pair, ne_eq, one_ne_zero,
    ↓reduceIte]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn]
  simpa only [Option.getD_some] using hwn

theorem betaOrbitAt_mem_generatorSpan
    (A : Set ℕ) (Hc : C(BetaNat, ℂ))
    (W : Finset C(BetaNat, ℂ))
    {Y : C(BetaNat, ℂ)}
    (hYW : Y ∈ Submodule.span ℂ (W : Set C(BetaNat, ℂ)))
    (hW : (W : Set C(BetaNat, ℂ)) ⊆ Set.range betaCharacter)
    (p : BetaNat) :
    betaOrbitAt Y p ∈
      Submodule.span ℂ (Set.range (mrrGeneratorFamily A Hc W)) := by
  have hOrbitW : betaOrbitAt Y p ∈
      Submodule.span ℂ (W : Set C(BetaNat, ℂ)) := by
    induction hYW using Submodule.span_induction with
    | mem w hw =>
        rcases hW hw with ⟨z, rfl⟩
        rw [betaOrbitAt_character]
        exact (Submodule.span ℂ (W : Set C(BetaNat, ℂ))).smul_mem _
          (Submodule.subset_span hw)
    | zero => simpa only [betaOrbitAt_zero] using
        (Submodule.span ℂ (W : Set C(BetaNat, ℂ))).zero_mem
    | add Y Z _ _ hY hZ =>
        rw [betaOrbitAt_add]
        exact (Submodule.span ℂ (W : Set C(BetaNat, ℂ))).add_mem hY hZ
    | smul a Y _ hY =>
        rw [betaOrbitAt_smul]
        exact (Submodule.span ℂ (W : Set C(BetaNat, ℂ))).smul_mem a hY
  exact finiteCharacters_le_generatorSpan A Hc W hOrbitW

end

end Erdos109

open CompactlySupported Filter Function MeasureTheory Set
open scoped BoundedContinuousFunction ComplexConjugate ENNReal NNReal Pointwise Topology

namespace Erdos109

noncomputable section

noncomputable local instance : MeasurableSpace BetaNat := borel BetaNat
local instance : BorelSpace BetaNat := ⟨rfl⟩
local instance : Add (Ultrafilter ℕ) := Ultrafilter.add
local instance : AddSemigroup (Ultrafilter ℕ) := Ultrafilter.addSemigroup

theorem betaShift_iterate_eq_add_pure (p : BetaNat) (n : ℕ) :
    betaShift^[n] p = p + (pure n : BetaNat) := by
  induction n with
  | zero =>
      apply Ultrafilter.coe_inj.mp
      ext E
      change E ∈ (p : Filter ℕ) ↔
        ∀ᶠ x in p, ∀ᶠ y in pure 0, x + y ∈ E
      simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      apply Ultrafilter.coe_inj.mp
      ext E
      change (∀ᶠ x in p, ∀ᶠ y in pure n,
        ∀ᶠ z in pure 1, x + y + z ∈ E) ↔
        ∀ᶠ x in p, ∀ᶠ y in pure (n + 1), x + y ∈ E
      simp [add_assoc]

theorem ultrafilter_add_pure_comm (p : BetaNat) (n : ℕ) :
    p + (pure n : BetaNat) = (pure n : BetaNat) + p := by
  apply Ultrafilter.coe_inj.mp
  ext E
  change (∀ᶠ x in p, ∀ᶠ y in pure n, x + y ∈ E) ↔
    ∀ᶠ x in pure n, ∀ᶠ y in p, x + y ∈ E
  change {x : ℕ | x + n ∈ E} ∈ (p : Filter ℕ) ↔
    {y : ℕ | n + y ∈ E} ∈ (p : Filter ℕ)
  have hset : {x : ℕ | x + n ∈ E} = {y : ℕ | n + y ∈ E} := by
    ext x
    change x + n ∈ E ↔ n + x ∈ E
    rw [add_comm]
  rw [hset]

theorem betaIndicator_iterate_at_eq_ultraShift
    (A : Set ℕ) (p : BetaNat) (n : ℕ) :
    betaIndicator A (betaShift^[n] p) =
      betaIndicator (ultraShift A p) (pure n) := by
  rw [betaIndicator_ultraShift]
  change betaIndicator A (betaShift^[n] p) =
    betaIndicator A ((pure n : BetaNat) + p)
  rw [betaShift_iterate_eq_add_pure, ultrafilter_add_pure_comm]

theorem rightTranslate_continuousAnti_eq
    (A : Set ℕ) (Y : C(BetaNat, ℂ)) (p : BetaNat) (n : ℕ) :
    betaRightTranslate
        (fun m ↦ continuousAntiPart A Y (pure m)) (1 + ‖Y‖)
        (abs_continuousAntiPart_pure_le A Y) n p =
      betaIndicator (ultraShift A p) (pure n) -
        (betaOrbitAt Y p (pure n)).re := by
  rw [betaRightTranslate_of_continuous (continuousAntiPart A Y)]
  · simp only [ContinuousMap.comp_apply, continuousAntiPart,
      ContinuousMap.sub_apply, continuousRealPart_apply,
      betaOrbitAt_pure_apply]
    change betaIndicator A (betaShift^[n] p) -
        (Y (betaShift^[n] p)).re = _
    rw [betaIndicator_iterate_at_eq_ultraShift]
  · intro q
    have hA : |betaIndicator A q| ≤ 1 := by
      by_cases hq : betaMembership A q = true <;> simp [betaIndicator, hq]
    calc
      |continuousAntiPart A Y q| ≤
          |betaIndicator A q| + |(Y q).re| := by
        simpa [continuousAntiPart, continuousRealPart] using
          abs_sub (betaIndicator A q) (Y q).re
      _ ≤ 1 + ‖Y‖ := by
        gcongr
        exact (Complex.abs_re_le_norm _).trans (Y.norm_coe_le_norm _)

theorem betaCrossAverage_anti_eq
    (A : Set ℕ) (Y Hc : C(BetaNat, ℂ))
    (hHreal : ∀ p, Hc p = ((Hc p).re : ℂ))
    (N : ℕ) (p : BetaNat) :
    betaCrossAverage N (fun n ↦ (Hc (pure n)).re)
        (fun m ↦ continuousAntiPart A Y (pure m)) (1 + ‖Y‖)
        (abs_continuousAntiPart_pure_le A Y) p =
      realFinsetMean (Finset.range N) (fun n ↦
        (Hc (pure n)).re *
          (betaIndicator (ultraShift A p) (pure n) -
            (betaOrbitAt Y p (pure n)).re)) := by
  rw [betaCrossAverage_apply]
  apply congrArg (realFinsetMean (Finset.range N))
  funext n
  rw [rightTranslate_continuousAnti_eq]

theorem integral_betaIndicator_eq_of_upperDensity_limit
    (A : Set ℕ) (N : ℕ → ℕ) (hNpos : ∀ k, 0 < N k)
    (q : Ultrafilter ℕ) (hq : (q : Filter ℕ) ≤ atTop)
    (mu : ProbabilityMeasure BetaNat)
    (hmu : Tendsto (fun k ↦ betaEmpirical (N k) (hNpos k))
      (q : Filter ℕ) (nhds mu))
    (hdens : Tendsto (fun k ↦ finsetDensity (Finset.range (N k)) A)
      atTop (nhds A.upperDensity)) :
    ∫ p, betaIndicator A p ∂(mu : Measure BetaNat) = A.upperDensity := by
  let b : BetaNat →ᵇ ℝ :=
    BoundedContinuousFunction.mkOfCompact (betaIndicator A)
  have hmuA :=
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hmu) b
  change Tendsto (fun k ↦
      ∫ p, betaIndicator A p
        ∂((betaEmpirical (N k) (hNpos k) : ProbabilityMeasure BetaNat) :
          Measure BetaNat)) (q : Filter ℕ)
      (nhds (∫ p, betaIndicator A p ∂(mu : Measure BetaNat))) at hmuA
  have hdensq := hdens.mono_left hq
  apply tendsto_nhds_unique hmuA
  exact hdensq.congr' (Eventually.of_forall fun k ↦
    (integral_betaEmpirical_indicator (N k) (hNpos k) A).symm)

end

end Erdos109

open CompactlySupported Filter Function MeasureTheory Set
open scoped BoundedContinuousFunction ComplexConjugate ENNReal NNReal Pointwise Topology

namespace Erdos109

noncomputable section

noncomputable local instance : MeasurableSpace BetaNat := borel BetaNat
local instance : BorelSpace BetaNat := ⟨rfl⟩

variable {mu : Measure BetaNat} [IsProbabilityMeasure mu]

theorem betaOrbitAt_neg (Y : C(BetaNat, ℂ)) (p : BetaNat) :
    betaOrbitAt (-Y) p = -betaOrbitAt Y p := by
  rw [show -Y = (-1 : ℂ) • Y by simp, betaOrbitAt_smul]
  simp

theorem betaOrbitAt_sub (Y Z : C(BetaNat, ℂ)) (p : BetaNat) :
    betaOrbitAt (Y - Z) p = betaOrbitAt Y p - betaOrbitAt Z p := by
  rw [sub_eq_add_neg, betaOrbitAt_add, betaOrbitAt_neg]
  rfl

theorem norm_toLp_betaOrbitAt_eq
    (hmu : MeasurePreserving betaShift mu mu)
    {Y : C(BetaNat, ℂ)} (hY : Y ∈ betaCharacterSpanC) (p : BetaNat) :
    ‖ContinuousMap.toLp 2 mu ℂ (betaOrbitAt Y p)‖ =
      ‖ContinuousMap.toLp 2 mu ℂ Y‖ := by
  rw [toLp_betaOrbitAt_eq_compactOrbitLimit hmu hY p,
    norm_compactOrbitLimit]

theorem norm_betaIndicatorL2_le_one (A : Set ℕ) :
    ‖betaIndicatorL2 mu A‖ ≤ 1 := by
  apply (norm_toLp_continuousMap_le (betaIndicatorComplex A)).trans
  rw [ContinuousMap.norm_le _ (by positivity)]
  intro p
  change ‖(betaIndicator A p : ℂ)‖ ≤ 1
  by_cases hp : betaMembership A p = true <;> simp [betaIndicator, hp]

theorem norm_unitaryCompactPart_le_one
    (hmu : MeasurePreserving betaShift mu mu) (A : Set ℕ) :
    ‖unitaryCompactPart (betaKoopman hmu) (betaIndicatorL2 mu A)‖ ≤ 1 := by
  exact ((unitaryKronecker (betaKoopman hmu)).toSubmodule
    |>.norm_starProjection_apply_le (betaIndicatorL2 mu A)).trans
      (norm_betaIndicatorL2_le_one A)

theorem norm_besProjection_le_one (A : Set ℕ) :
    ‖(betaBesClosed (mu := mu)).toSubmodule.starProjection
        (betaIndicatorL2 mu A)‖ ≤ 1 := by
  exact ((betaBesClosed (mu := mu)).toSubmodule
    |>.norm_starProjection_apply_le (betaIndicatorL2 mu A)).trans
      (norm_betaIndicatorL2_le_one A)

theorem dist_toLp_betaOrbitAt_le
    (hmu : MeasurePreserving betaShift mu mu)
    {Y Z : C(BetaNat, ℂ)}
    (hY : Y ∈ betaCharacterSpanC) (hZ : Z ∈ betaCharacterSpanC)
    (p : BetaNat) :
    dist (ContinuousMap.toLp 2 mu ℂ (betaOrbitAt Y p))
        (ContinuousMap.toLp 2 mu ℂ (betaOrbitAt Z p)) =
      ‖ContinuousMap.toLp 2 mu ℂ (Y - Z)‖ := by
  rw [dist_eq_norm, ← map_sub, ← betaOrbitAt_sub,
    norm_toLp_betaOrbitAt_eq hmu ((betaCharacterSpanC).sub_mem hY hZ) p]

theorem inner_re_lower_of_close
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (a b x y : H)
    (hab : (inner ℂ a b).re ≥ 0)
    (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1)
    (hxa : ‖x - a‖ ≤ ε) (hyb : ‖y - b‖ ≤ η) :
    (inner ℂ x y).re ≥ (inner ℂ a b).re - ε * (1 + η) - η := by
  have heps : 0 ≤ ε := (norm_nonneg (x - a)).trans hxa
  have heta : 0 ≤ η := (norm_nonneg (y - b)).trans hyb
  have h1 := Complex.abs_re_le_norm (inner ℂ (x - a) y)
  have h2 := norm_inner_le_norm (𝕜 := ℂ) (x - a) y
  have h3 := Complex.abs_re_le_norm (inner ℂ a (y - b))
  have h4 := norm_inner_le_norm (𝕜 := ℂ) a (y - b)
  have hy : ‖y‖ ≤ 1 + η := by
    calc
      ‖y‖ ≤ ‖y - b‖ + ‖b‖ := by
        simpa only [sub_add_cancel] using norm_add_le (y - b) b
      _ ≤ η + 1 := add_le_add hyb hb
      _ = 1 + η := by ring
  have herr1 : |(inner ℂ (x - a) y).re| ≤ ε * (1 + η) :=
    h1.trans (h2.trans (mul_le_mul hxa hy (norm_nonneg _) heps))
  have herr2 : |(inner ℂ a (y - b)).re| ≤ η := by
    calc
      |(inner ℂ a (y - b)).re| ≤ ‖inner ℂ a (y - b)‖ := h3
      _ ≤ ‖a‖ * ‖y - b‖ := h4
      _ ≤ 1 * η := mul_le_mul ha hyb (norm_nonneg _) zero_le_one
      _ = η := one_mul _
  have heq : (inner ℂ x y).re =
      (inner ℂ a b).re + (inner ℂ a (y - b)).re +
        (inner ℂ (x - a) y).re := by
    conv_lhs =>
      rw [show x = a + (x - a) by abel, inner_add_left,
        show y = b + (y - b) by abel, inner_add_right]
    simp only [Complex.add_re]
    rw [show b + (y - b) = y by abel]
  have he1 := (abs_le.mp herr1).1
  have he2 := (abs_le.mp herr2).1
  rw [heq]
  linarith

theorem complexPrefixMean_ofReal (N : ℕ) (f : ℕ → ℝ) :
    complexPrefixMean N (fun n ↦ (f n : ℂ)) =
      (realFinsetMean (Finset.range N) f : ℂ) := by
  unfold complexPrefixMean realFinsetMean
  rw [Finset.card_range, div_eq_mul_inv]
  push_cast
  ring

theorem complexPrefixMean_re (N : ℕ) (f : ℕ → ℂ) :
    (complexPrefixMean N f).re =
      realFinsetMean (Finset.range N) (fun n ↦ (f n).re) := by
  unfold complexPrefixMean realFinsetMean
  rw [Finset.card_range, ← Complex.ofReal_natCast, ← Complex.ofReal_inv,
    Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [Complex.re_sum]
  ring

theorem complexPrefixMean_betaIndicators_eq_finsetDensity
    (A D : Set ℕ) (N : ℕ) :
    complexPrefixMean N (fun n ↦
        (betaIndicator A (pure n) : ℂ) *
          betaIndicatorComplex D (pure n)) =
      (finsetDensity (Finset.range N) (A ∩ D) : ℂ) := by
  calc
    complexPrefixMean N (fun n ↦
        (betaIndicator A (pure n) : ℂ) * betaIndicatorComplex D (pure n)) =
        complexPrefixMean N (fun n ↦
          (realIndicator A n * realIndicator D n : ℝ)) := by
      apply congrArg (complexPrefixMean N)
      funext n
      simp [betaIndicatorComplex, betaIndicator_pure,
        natIndicator_eq_realIndicator]
    _ = (realFinsetCorrelation (Finset.range N)
          (realIndicator A) (realIndicator D) : ℂ) := by
      rw [complexPrefixMean_ofReal]
      rfl
    _ = (finsetDensity (Finset.range N) (A ∩ D) : ℂ) := by
      rw [realFinsetCorrelation_indicator]

theorem betaCrossAverage_anti_eq_complex_sub
    (A : Set ℕ) (Y Hc : C(BetaNat, ℂ))
    (hHreal : ∀ p, Hc p = ((Hc p).re : ℂ))
    (N : ℕ) (p : BetaNat) :
    betaCrossAverage N (fun n ↦ (Hc (pure n)).re)
        (fun m ↦ continuousAntiPart A Y (pure m)) (1 + ‖Y‖)
        (abs_continuousAntiPart_pure_le A Y) p =
      (complexPrefixMean N (fun n ↦
        (betaIndicator (ultraShift A p) (pure n) : ℂ) *
          Hc (pure n))).re -
      (complexPrefixMean N (fun n ↦
        Hc (pure n) * conj (betaOrbitAt Y p (pure n)))).re := by
  rw [betaCrossAverage_anti_eq A Y Hc hHreal N p]
  rw [complexPrefixMean_re, complexPrefixMean_re]
  have hterm (n : ℕ) :
      ((betaIndicator (ultraShift A p) (pure n) : ℂ) * Hc (pure n)).re =
        (Hc (pure n)).re * betaIndicator (ultraShift A p) (pure n) := by
    rw [hHreal]
    simp [mul_comm]
  have htermY (n : ℕ) :
      (Hc (pure n) * conj (betaOrbitAt Y p (pure n))).re =
        (Hc (pure n)).re * (betaOrbitAt Y p (pure n)).re := by
    rw [hHreal]
    simp
  simp_rw [hterm, htermY]
  unfold realFinsetMean
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  ring

theorem mrr_corr_zero_numeric
    {delta eps epsY c : ℝ}
    (hdelta : 0 < delta)
    (heps : eps = delta ^ 2 / 100)
    (hepsY0 : 0 ≤ epsY)
    (hepsYLe : epsY ≤ eps)
    (hepsLe : eps ≤ 1 / 100)
    (hc : delta ^ 2 - eps * (1 + (epsY + 3 * eps)) -
        (epsY + 3 * eps) - delta ^ 2 / 100 ≤ c) :
    (3 / 4 : ℝ) * delta ^ 2 ≤ c := by
  have heps0 : 0 ≤ eps := by rw [heps]; positivity
  have heta0 : 0 ≤ epsY + 3 * eps := by
    positivity
  have heta : epsY + 3 * eps ≤ 4 * eps := by linarith
  have hfactor : 1 + (epsY + 3 * eps) ≤ 104 / 100 := by
    nlinarith
  have hmul : eps * (1 + (epsY + 3 * eps)) ≤ eps * (104 / 100) :=
    mul_le_mul_of_nonneg_left hfactor heps0
  rw [heps] at hmul heta hc
  nlinarith [sq_pos_of_pos hdelta]

theorem mrr_transfer_to_compact_numeric
    {delta eps corr compact error : ℝ}
    (hdelta : 0 < delta)
    (hcorr : (3 / 4 : ℝ) * delta ^ 2 ≤ corr)
    (heps : eps ≤ (1 / 100 : ℝ) * delta ^ 2)
    (heq : corr = compact + error)
    (herror : error ≤ eps) :
    (2 / 3 : ℝ) * delta ^ 2 ≤ compact := by
  nlinarith [sq_pos_of_pos hdelta]

theorem norm_unitary_iterate_sub_le_three
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (U : H ≃ₗᵢ[ℂ] H) (a g : H) (n : ℕ) (eps : ℝ)
    (hag : ‖a - g‖ ≤ eps) (hret : dist ((U ^ n) g) g < eps) :
    ‖(U ^ n) a - a‖ ≤ 3 * eps := by
  have hdecomp : (U ^ n) a - a =
      (U ^ n) (a - g) + ((U ^ n) g - g) + (g - a) := by
    rw [(U ^ n).map_sub]
    abel
  rw [hdecomp]
  calc
    ‖(U ^ n) (a - g) + ((U ^ n) g - g) + (g - a)‖ ≤
        ‖(U ^ n) (a - g)‖ + ‖(U ^ n) g - g‖ + ‖g - a‖ := by
      exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ = ‖a - g‖ + dist ((U ^ n) g) g + ‖a - g‖ := by
      rw [(U ^ n).norm_map, dist_eq_norm, norm_sub_rev g a]
    _ ≤ eps + eps + eps := by
      exact add_le_add (add_le_add hag (le_of_lt hret)) hag
    _ = 3 * eps := by ring

theorem mrr_row_numeric
    {s eps compact weak total : ℝ}
    (hs : 0 ≤ s)
    (hy : (2 / 3 : ℝ) * s ≤ compact)
    (heps : eps = s / 100)
    (hcompact : compact - 3 * eps ≤ total - weak)
    (hweak : -(s / 10) ≤ weak) :
    (1 / 2 : ℝ) * s ≤ total := by
  rw [heps] at hcompact
  norm_num at hy hcompact hweak ⊢
  linarith

theorem ennreal_density_eq_ofReal
    (F : Finset ℕ) (hF : F.Nonempty) (E : Set ℕ) :
    (((((F : Set ℕ) ∩ E).ncard : ℕ) : ℝ≥0∞) / F.card) =
      ENNReal.ofReal (finsetDensity F E) := by
  rw [finsetDensity, ENNReal.ofReal_div_of_pos
    (by exact_mod_cast Finset.card_pos.mpr hF)]
  simp

end

end Erdos109

open CompactlySupported Filter Function MeasureTheory Set
open scoped BoundedContinuousFunction ComplexConjugate ENNReal NNReal Pointwise Topology

namespace Erdos109

noncomputable section

noncomputable local instance : MeasurableSpace BetaNat := borel BetaNat
local instance : BorelSpace BetaNat := ⟨rfl⟩

theorem erdos_109 (A : Set ℕ) (hA : A.upperDensity > 0) :
    ∃ B C : Set ℕ, B.Infinite ∧ C.Infinite ∧ B + C ⊆ A := by
  obtain ⟨N, hNdensity, hNtop, hNpos⟩ :=
    exists_prefix_realizing_upperDensity A
  have hNdensity' : Tendsto
      (fun k ↦ finsetDensity (Finset.range (N k)) A)
      atTop (nhds A.upperDensity) := by
    simpa only [finsetDensity_range_eq_partialDensity] using hNdensity
  obtain ⟨q, hq, mu, hmureg, hmu, hpres⟩ :=
    exists_invariant_betaLimit N hNpos hNtop
  let : (mu : Measure BetaNat).Regular := hmureg
  let U := betaKoopman hpres
  let F : BetaL2 (mu : Measure BetaNat) := betaIndicatorL2 mu A
  let a : BetaL2 (mu : Measure BetaNat) := unitaryCompactPart U F
  let b : BetaL2 (mu : Measure BetaNat) :=
    (betaBesClosed (mu := (mu : Measure BetaNat))).toSubmodule.starProjection F
  let delta : ℝ := A.upperDensity
  let eps : ℝ := delta ^ 2 / 100
  have hdelta : 0 < delta := hA
  have heps : 0 < eps := by positivity
  have hdeltaInt : ∫ p, betaIndicator A p ∂(mu : Measure BetaNat) = delta := by
    exact integral_betaIndicator_eq_of_upperDensity_limit
      A N hNpos q hq mu hmu hNdensity'
  have hinner : delta ^ 2 ≤ (inner ℂ a b).re := by
    simpa only [a, b, F, U, delta, hdeltaInt] using
      (sq_integral_indicator_le_re_inner_compact_bes hpres A)
  have haK : a ∈ unitaryKronecker U := by
    exact unitaryCompactPart_mem_kronecker U F
  obtain ⟨ga, hgaEig, hgaClose⟩ :=
    exists_unitaryEigenSpan_close U haK eps heps
  have hbBes : b ∈ betaBesClosed (mu := (mu : Measure BetaNat)) := by
    exact (betaBesClosed (mu := (mu : Measure BetaNat))).toSubmodule
      |>.starProjection_apply_mem F
  obtain ⟨G, hGchar, hGEig, hGClose⟩ :=
    exists_characterPolynomial_close_betaBesClosed hpres hbBes eps heps
  let g : BetaL2 (mu : Measure BetaNat) := ContinuousMap.toLp 2 mu ℂ G
  let V := unitaryL2Prod U
  let c := WithLp.toLp 2 (ga, g)
  have hcEig : c ∈ unitaryEigenSpan V := by
    exact unitaryEigenSpan_toLp_pair U hgaEig (by simpa only [g, U] using hGEig)
  have hcAP : TotallyBounded (Set.range fun n : ℕ ↦ (V ^ n) c) := by
    exact unitaryEigenSpan_le_almostPeriodic V hcEig
  let d : ℝ := ∫ p, compactReturnWeight V c eps heps p ∂(mu : Measure BetaNat)
  have hdpos : 0 < d := by
    exact integral_compactReturnWeight_pos N hNpos hNtop q hq mu hmu
      V c hcAP eps heps
  let epsY : ℝ := d * delta ^ 2 / 100
  have hepsY : 0 < epsY := by positivity
  obtain ⟨Y, hYchar, hYEig, hYClose⟩ :=
    exists_characterPolynomial_close_betaBesClosed hpres hbBes epsY hepsY
  obtain ⟨Hc, hHc, hHcClose⟩ := exists_continuous_clip_close
    (mu := (mu : Measure BetaNat))
    (clipComplexLp_unitaryCompactPart_indicator hpres A) eps heps
  have hHreal : ∀ p, Hc p = ((Hc p).re : ℂ) := fun p ↦ (hHc p).1
  have hHnorm : ∀ p, ‖Hc p‖ ≤ 1 := by
    intro p
    rw [(hHc p).1, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hHc p).2.1]
    exact (hHc p).2.2
  obtain ⟨W, hWchar, hYW, hGW⟩ :=
    exists_common_finite_character_generators hYchar hGchar
  let Z : ℕ → C(BetaNat, ℂ) := mrrGeneratorFamily A Hc W
  have hZnorm : ∀ i p, ‖Z i p‖ ≤ 1 := by
    exact mrrGeneratorFamily_norm_le_one A Hc hHnorm W hWchar
  obtain ⟨phi₀, hphi₀, hgram₀⟩ :=
    exists_subseq_gram_tendsto_of_ultrafilter N hNpos q hq mu hmu Z
  have hWbes : ContinuousMap.toLp 2 (mu : Measure BetaNat) ℂ
        ⟨fun p ↦ (compactReturnWeight V c eps heps p : ℂ),
          Complex.continuous_ofReal.comp
            (compactReturnWeight V c eps heps).continuous⟩ ∈
      betaBesClosed (mu := (mu : Measure BetaNat)) := by
    simpa only [V, c, g, U] using
      (compactReturnWeightL2_pair_mem_betaBesClosed U hgaEig hGEig eps heps)
  have hantiSmall (n : ℕ) :
      |∫ p, compactReturnWeight V c eps heps p *
        betaRightTranslate
          (fun m ↦ continuousAntiPart A Y (pure m)) (1 + ‖Y‖)
          (abs_continuousAntiPart_pure_le A Y) n p
          ∂(mu : Measure BetaNat)| ≤ epsY := by
    exact (abs_integral_returnWeight_mul_rightTranslate_anti_le
      hpres A Y V c eps heps hWbes n).trans (le_of_lt hYClose)
  let nu : Measure BetaNat := compactReturnWeightedMeasure
    (mu : Measure BetaNat) V c eps heps
  let : IsFiniteMeasure nu := compactReturnWeightedMeasure_isFinite
    (mu : Measure BetaNat) V c eps heps
  let : NeZero nu := compactReturnWeightedMeasure_neZero
    (mu : Measure BetaNat) V c eps heps hdpos
  let cross (k : ℕ) : BetaNat → ℝ := fun p ↦
    betaCrossAverage (N (phi₀ k)) (fun n ↦ (Hc (pure n)).re)
      (fun m ↦ continuousAntiPart A Y (pure m)) (1 + ‖Y‖)
      (abs_continuousAntiPart_pure_le A Y) p
  have hcrossLower (k : ℕ) :
      -(epsY / d) ≤ ⨍ p, cross k p ∂nu := by
    have h := compactReturnWeighted_average_betaCrossAverage_lower
      (mu := (mu : Measure BetaNat)) V c eps heps d rfl hdpos
      (N (phi₀ k)) (hNpos (phi₀ k))
      (fun n ↦ (Hc (pure n)).re)
      (fun m ↦ continuousAntiPart A Y (pure m))
      1 (1 + ‖Y‖) epsY zero_le_one hepsY.le
      (fun n ↦ by
        rw [abs_of_nonneg (hHc (pure n)).2.1]
        exact (hHc (pure n)).2.2)
      (abs_continuousAntiPart_pure_le A Y) hantiSmall
    simpa only [one_mul, cross, nu] using h
  let Bad : Set BetaNat :=
    (mu : Measure BetaNat).supportᶜ ∪
      {p | compactReturnWeight V c eps heps p = 0}
  have hBad : nu Bad = 0 := by
    exact compactReturnWeightedMeasure_badSet_zero
      (mu : Measure BetaNat) V c eps heps
  have hCpos : 0 < 1 + ‖Y‖ := by positivity
  obtain ⟨phi₁, hphi₁, p, hpBad, hpLimsup⟩ :=
    exists_subseq_notMem_null_limsup_ge_of_average_lower
      nu cross (1 + ‖Y‖) hCpos
      (fun k ↦ (betaCrossAverage _ _ _ _ _).continuous.measurable)
      (fun k p ↦ (abs_le.mp (abs_betaCrossAverage_le
        (N (phi₀ k)) (hNpos (phi₀ k))
        (fun n ↦ (Hc (pure n)).re)
        (fun m ↦ continuousAntiPart A Y (pure m))
        1 (1 + ‖Y‖)
        (fun n ↦ by
          rw [abs_of_nonneg (hHc (pure n)).2.1]
          exact (hHc (pure n)).2.2)
        (abs_continuousAntiPart_pure_le A Y) p)).1 |> (by
          simpa only [one_mul, cross] using ·))
      (fun k p ↦ (abs_le.mp (abs_betaCrossAverage_le
        (N (phi₀ k)) (hNpos (phi₀ k))
        (fun n ↦ (Hc (pure n)).re)
        (fun m ↦ continuousAntiPart A Y (pure m))
        1 (1 + ‖Y‖)
        (fun n ↦ by
          rw [abs_of_nonneg (hHc (pure n)).2.1]
          exact (hHc (pure n)).2.2)
        (abs_continuousAntiPart_pure_le A Y) p)).2 |> (by
          simpa only [one_mul, cross] using ·))
      (-(epsY / d)) hcrossLower Bad hBad
  have hpSupport : p ∈ (mu : Measure BetaNat).support := by
    by_contra hp
    exact hpBad (Or.inl hp)
  have hpWeight : 0 < compactReturnWeight V c eps heps p := by
    have hnz : compactReturnWeight V c eps heps p ≠ 0 := by
      intro hz
      exact hpBad (Or.inr hz)
    exact lt_of_le_of_ne (compactReturnWeight_nonneg V c eps heps p) hnz.symm
  have hpReturns := compactReturnWeight_pair_pos_implies
    U ga g eps heps (by simpa only [V, c] using hpWeight)

  -- The next diagonal subsequence realizes the pointwise limsup and then
  -- represents every required correlation by one vector in the limiting L² space.
  let antiSeq : ℕ → ℝ := fun k ↦ cross (phi₁ k) p
  have hantiBounded : IsBoundedUnder (· ≤ ·) atTop antiSeq := by
    refine isBoundedUnder_of ⟨1 + ‖Y‖, fun k ↦ ?_⟩
    have hk := (abs_le.mp (abs_betaCrossAverage_le
      (N (phi₀ (phi₁ k))) (hNpos (phi₀ (phi₁ k)))
      (fun n ↦ (Hc (pure n)).re)
      (fun m ↦ continuousAntiPart A Y (pure m))
      1 (1 + ‖Y‖)
      (fun n ↦ by
        rw [abs_of_nonneg (hHc (pure n)).2.1]
        exact (hHc (pure n)).2.2)
      (abs_continuousAntiPart_pure_le A Y) p)).2
    simpa only [one_mul, antiSeq, cross] using hk
  have hantiCobounded : IsCoboundedUnder (· ≤ ·) atTop antiSeq := by
    refine isCoboundedUnder_le_of_le atTop
      (x := -(1 + ‖Y‖)) (fun k ↦ ?_)
    have hk := (abs_le.mp (abs_betaCrossAverage_le
      (N (phi₀ (phi₁ k))) (hNpos (phi₀ (phi₁ k)))
      (fun n ↦ (Hc (pure n)).re)
      (fun m ↦ continuousAntiPart A Y (pure m))
      1 (1 + ‖Y‖)
      (fun n ↦ by
        rw [abs_of_nonneg (hHc (pure n)).2.1]
        exact (hHc (pure n)).2.2)
      (abs_continuousAntiPart_pure_le A Y) p)).1
    simpa only [one_mul, antiSeq, cross] using hk
  obtain ⟨theta, hantiLim, htheta⟩ :=
    exists_seq_tendsto_limsup hantiCobounded hantiBounded
  let M : ℕ → ℕ := fun k ↦ N (phi₀ (phi₁ (theta k)))
  have hMpos : ∀ k, 0 < M k := fun k ↦ hNpos _
  have hgram : ∀ i j, Tendsto
      (fun k ↦ complexPrefixMean (M k)
        (fun n ↦ Z i (pure n) * conj (Z j (pure n))))
      atTop
      (nhds (∫ p, gramProduct Z i j p ∂(mu : Measure BetaNat))) := by
    intro i j
    simpa [M, Function.comp_def] using (hgram₀ i j).comp
      (hphi₁.tendsto_atTop.comp htheta)
  let u : ℕ → ℂ := fun n ↦
    (betaIndicator (ultraShift A p) (pure n) : ℂ)
  have hu : ∀ n, ‖u n‖ ≤ 1 := by
    intro n
    change ‖(betaIndicator (ultraShift A p) (pure n) : ℂ)‖ ≤ 1
    by_cases hn : betaMembership (ultraShift A p) (pure n) = true <;>
      simp [betaIndicator, hn]
  obtain ⟨phi₂, hphi₂, corr, y, hyNorm, hcorrLim, hcorrInner⟩ :=
    exists_subseq_vector_representing_empirical_left
      M hMpos (mu : Measure BetaNat) Z hZnorm hgram u hu
  let L : ℕ → ℕ := fun k ↦ M (phi₂ k)
  have hLpos : ∀ k, 0 < L k := fun k ↦ hMpos _
  have hLtop : Tendsto L atTop atTop := by
    exact hNtop.comp (hphi₀.tendsto_atTop.comp
      (hphi₁.tendsto_atTop.comp
        (htheta.comp hphi₂.tendsto_atTop)))

  have hantiLower : -(epsY / d) ≤ limsup antiSeq atTop := by
    simpa only [antiSeq] using hpLimsup
  have hantiLim' : Tendsto
      (fun k ↦ antiSeq (theta (phi₂ k))) atTop
      (nhds (limsup antiSeq atTop)) := by
    simpa [Function.comp_def] using hantiLim.comp hphi₂.tendsto_atTop
  have hYspan : betaOrbitAt Y p ∈ Submodule.span ℂ (Set.range Z) := by
    exact betaOrbitAt_mem_generatorSpan A Hc W hYW hWchar p
  have hstruct₀ := tendsto_prefixMean_generator_mul_betaOrbitAt
    Z hgram 0 Y p hYspan
  have hstruct : Tendsto
      (fun k ↦ complexPrefixMean (L k) (fun n ↦
        Z 0 (pure n) * conj (betaOrbitAt Y p (pure n))))
      atTop
      (nhds (∫ x, Z 0 x * conj (betaOrbitAt Y p x)
        ∂(mu : Measure BetaNat))) := by
    simpa [L, Function.comp_def] using
      hstruct₀.comp hphi₂.tendsto_atTop
  have hcorr₀ : Tendsto
      (fun k ↦ complexPrefixMean (L k)
        (fun n ↦ u n * Z 0 (pure n)))
      atTop (nhds (corr 0)) := by
    simpa only [L] using hcorrLim 0
  have hsplit : Tendsto
      (fun k ↦ antiSeq (theta (phi₂ k))) atTop
      (nhds ((corr 0).re -
        (∫ x, Z 0 x * conj (betaOrbitAt Y p x)
          ∂(mu : Measure BetaNat)).re)) := by
    have hcorrRe := (Complex.continuous_re.tendsto (corr 0)).comp hcorr₀
    have hstructRe := (Complex.continuous_re.tendsto
      (∫ x, Z 0 x * conj (betaOrbitAt Y p x)
        ∂(mu : Measure BetaNat))).comp hstruct
    have ht := hcorrRe.sub hstructRe
    apply ht.congr'
    filter_upwards [] with k
    change
      (complexPrefixMean (L k) (fun n ↦
        (betaIndicator (ultraShift A p) (pure n) : ℂ) * Hc (pure n))).re -
        (complexPrefixMean (L k) (fun n ↦
          Hc (pure n) * conj (betaOrbitAt Y p (pure n)))).re =
      betaCrossAverage (L k) (fun n ↦ (Hc (pure n)).re)
        (fun m ↦ continuousAntiPart A Y (pure m)) (1 + ‖Y‖)
        (abs_continuousAntiPart_pure_le A Y) p
    rw [betaCrossAverage_anti_eq_complex_sub A Y Hc hHreal]
  have hlimsupEq : limsup antiSeq atTop =
      (corr 0).re -
        (∫ x, Z 0 x * conj (betaOrbitAt Y p x)
          ∂(mu : Measure BetaNat)).re :=
    tendsto_nhds_unique hantiLim' hsplit
  let avec : BetaL2 (mu : Measure BetaNat) :=
    ContinuousMap.toLp 2 mu ℂ Hc
  let yp : BetaL2 (mu : Measure BetaNat) :=
    ContinuousMap.toLp 2 mu ℂ (betaOrbitAt Y p)
  let gp : BetaL2 (mu : Measure BetaNat) :=
    ContinuousMap.toLp 2 mu ℂ (betaOrbitAt G p)
  have hstructInner :
      (∫ x, Z 0 x * conj (betaOrbitAt Y p x)
        ∂(mu : Measure BetaNat)) = inner ℂ yp avec := by
    change (∫ x, Hc x * conj (betaOrbitAt Y p x)
      ∂(mu : Measure BetaNat)) = inner ℂ yp avec
    rw [ContinuousMap.inner_toLp]
  have hYG : ‖ContinuousMap.toLp 2 mu ℂ Y - g‖ ≤ epsY + eps := by
    have hYc : ‖ContinuousMap.toLp 2 mu ℂ Y - b‖ ≤ epsY := by
      rw [norm_sub_rev]
      exact le_of_lt hYClose
    have hGc : ‖b - g‖ ≤ eps := by
      change ‖b - ContinuousMap.toLp 2 mu ℂ G‖ ≤ eps
      exact le_of_lt hGClose
    calc
      ‖ContinuousMap.toLp 2 mu ℂ Y - g‖ ≤
          ‖ContinuousMap.toLp 2 mu ℂ Y - b‖ + ‖b - g‖ := by
        rw [show ContinuousMap.toLp 2 mu ℂ Y - g =
          (ContinuousMap.toLp 2 mu ℂ Y - b) + (b - g) by abel]
        exact norm_add_le _ _
      _ ≤ epsY + eps := add_le_add hYc hGc
  have hYpGp : dist yp gp ≤ epsY + eps := by
    rw [show yp = ContinuousMap.toLp 2 mu ℂ (betaOrbitAt Y p) from rfl,
      show gp = ContinuousMap.toLp 2 mu ℂ (betaOrbitAt G p) from rfl,
      dist_toLp_betaOrbitAt_le hpres hYchar hGchar p]
    rw [map_sub]
    change ‖ContinuousMap.toLp 2 mu ℂ Y - g‖ ≤ epsY + eps
    exact hYG
  have hGorbit : TotallyBounded (Set.range fun n : ℕ ↦ (U ^ n) g) := by
    simpa only [g, U] using characterSpan_orbit_totallyBounded hpres hGchar
  have hGpG : dist gp g ≤ eps := by
    rw [show gp = ContinuousMap.toLp 2 mu ℂ (betaOrbitAt G p) from rfl,
      toLp_betaOrbitAt_eq_compactOrbitLimit hpres hGchar p]
    exact dist_compactOrbitLimit_le_of_mem U g hGorbit p eps hpReturns.2
  have hYpB : ‖yp - b‖ ≤ epsY + 3 * eps := by
    rw [← dist_eq_norm]
    calc
      dist yp b ≤ dist yp gp + dist gp g + dist g b := dist_triangle4 _ _ _ _
      _ ≤ (epsY + eps) + eps + eps := by
        apply add_le_add
        · exact add_le_add hYpGp hGpG
        · change dist g b ≤ eps
          rw [dist_eq_norm, norm_sub_rev]
          change ‖b - ContinuousMap.toLp 2 mu ℂ G‖ ≤ eps
          exact le_of_lt hGClose
      _ = epsY + 3 * eps := by ring
  have haNorm : ‖a‖ ≤ 1 := by
    simpa only [a, U, F] using
      (norm_unitaryCompactPart_le_one (mu := (mu : Measure BetaNat)) hpres A)
  have hbNorm : ‖b‖ ≤ 1 := by
    simpa only [b, F] using
      (norm_besProjection_le_one (mu := (mu : Measure BetaNat)) A)
  have havecA : ‖avec - a‖ ≤ eps := by
    simpa only [avec, a, U, F, norm_sub_rev] using le_of_lt hHcClose
  have hstructLower :
      (inner ℂ yp avec).re ≥
        (inner ℂ a b).re -
          eps * (1 + (epsY + 3 * eps)) - (epsY + 3 * eps) := by
    have htmp := inner_re_lower_of_close a b avec yp
      ((sq_nonneg delta).trans hinner) haNorm hbNorm havecA hYpB
    have hre : (inner ℂ avec yp).re = (inner ℂ yp avec).re := by
      exact inner_re_symm (𝕜 := ℂ) avec yp
    rwa [← hre]
  have hcorrZeroLower :
      (corr 0).re ≥
        delta ^ 2 - eps * (1 + (epsY + 3 * eps)) -
          (epsY + 3 * eps) - epsY / d := by
    rw [hlimsupEq, hstructInner] at hantiLower
    linarith
  have hdeltaLe : delta ≤ 1 := by
    exact le_of_tendsto hNdensity
      (Eventually.of_forall fun n ↦ Set.partialDensity_le_one A Set.univ (N n))
  have hdLe : d ≤ 1 := by
    calc
      d ≤ ∫ _p : BetaNat, (1 : ℝ) ∂(mu : Measure BetaNat) := by
        dsimp only [d]
        apply integral_mono
        · exact (BoundedContinuousFunction.mkOfCompact
            (compactReturnWeight V c eps heps)).integrable _
        · exact integrable_const 1
        · intro p
          exact compactReturnWeight_le_one V c eps heps p
      _ = 1 := by simp
  have hepsYLe : epsY ≤ eps := by
    have hm := mul_le_mul_of_nonneg_right hdLe (sq_nonneg delta)
    dsimp only [epsY, eps]
    exact div_le_div_of_nonneg_right (by simpa only [one_mul] using hm) (by positivity)
  have hepsLe : eps ≤ 1 / 100 := by
    have hs : delta ^ 2 ≤ (1 : ℝ) ^ 2 :=
      (sq_le_sq₀ hdelta.le zero_le_one).2 hdeltaLe
    dsimp only [eps]
    exact div_le_div_of_nonneg_right (by simpa using hs) (by positivity)
  have hdiv : epsY / d = delta ^ 2 / 100 := by
    dsimp only [epsY]
    field_simp [hdpos.ne']
  have hcorrZeroStrong : (3 / 4 : ℝ) * delta ^ 2 ≤ (corr 0).re := by
    rw [hdiv] at hcorrZeroLower
    exact mrr_corr_zero_numeric hdelta rfl hepsY.le
      hepsYLe hepsLe hcorrZeroLower
  have hyA : (2 / 3 : ℝ) * delta ^ 2 ≤ (inner ℂ y a).re := by
    have hc0 : inner ℂ y avec = corr 0 := by
      simpa only [avec, Z, mrrGeneratorFamily_zero] using hcorrInner 0
    have herr := Complex.abs_re_le_norm (inner ℂ y (avec - a))
    have herrNorm := norm_inner_le_norm (𝕜 := ℂ) y (avec - a)
    have habserr : |(inner ℂ y (avec - a)).re| ≤ eps := by
      exact herr.trans (herrNorm.trans
        (mul_le_mul hyNorm havecA (norm_nonneg _) zero_le_one |>.trans_eq (one_mul eps)))
    have hlo := (abs_le.mp habserr).1
    have hhi := (abs_le.mp habserr).2
    have heq : (inner ℂ y avec).re =
        (inner ℂ y a).re + (inner ℂ y (avec - a)).re := by
      have havec : avec = a + (avec - a) := by abel
      calc
        (inner ℂ y avec).re = (inner ℂ y (a + (avec - a))).re :=
          congrArg (fun v ↦ (inner ℂ y v).re) havec
        _ = (inner ℂ y a).re + (inner ℂ y (avec - a)).re := by
          rw [inner_add_right, Complex.add_re]
    rw [hc0] at heq
    have hepsSmall : eps ≤ (1 / 100 : ℝ) * delta ^ 2 := by
      have heqeps : eps = (1 / 100 : ℝ) * delta ^ 2 := by
        dsimp only [eps]
        ring
      exact heqeps.le
    exact mrr_transfer_to_compact_numeric hdelta hcorrZeroStrong
      hepsSmall heq hhi

  -- Every return time for the algebraic approximation of the compact part
  -- now has a uniformly positive limiting row correlation.
  have hpEssential : (p : Filter ℕ) ≤
      densityOneFilter (fun k ↦ Finset.range (N k)) :=
    support_point_le_densityOneFilter N hNpos q hq mu hmu p hpSupport
  have hweakMem :
      {m | ‖inner ℂ y ((U ^ m) (unitaryWeakPart U F))‖ <
        delta ^ 2 / 10} ∈ (p : Filter ℕ) := by
    exact essential_mem_small_weak_correlation U F y N hNpos hNtop
      p hpEssential (delta ^ 2 / 10) (by positivity)
  let GoodBase : Set ℕ :=
    {m | dist ((U ^ m) ga) ga < eps} ∩
      {m | ‖inner ℂ y ((U ^ m) (unitaryWeakPart U F))‖ <
        delta ^ 2 / 10}
  have hGoodBase : GoodBase ∈ (p : Filter ℕ) :=
    inter_mem hpReturns.1 hweakMem
  have hrowLower (m : ℕ) (hm : m ∈ GoodBase) :
      (1 / 2 : ℝ) * delta ^ 2 ≤ (corr (Nat.pair 0 m + 1)).re := by
    have hUa : ‖(U ^ m) a - a‖ ≤ 3 * eps := by
      exact norm_unitary_iterate_sub_le_three U a ga m eps
        (le_of_lt hgaClose) hm.1
    have hcompactErr :
        |(inner ℂ y ((U ^ m) a - a)).re| ≤ 3 * eps := by
      calc
        |(inner ℂ y ((U ^ m) a - a)).re| ≤
            ‖inner ℂ y ((U ^ m) a - a)‖ := Complex.abs_re_le_norm _
        _ ≤ ‖y‖ * ‖(U ^ m) a - a‖ :=
          norm_inner_le_norm (𝕜 := ℂ) _ _
        _ ≤ 1 * (3 * eps) :=
          mul_le_mul hyNorm hUa (norm_nonneg _) zero_le_one
        _ = 3 * eps := one_mul _
    have hcompactLower :
        (inner ℂ y a).re - 3 * eps ≤
          (inner ℂ y ((U ^ m) a)).re := by
      have herrLo := (abs_le.mp hcompactErr).1
      have heq : (inner ℂ y ((U ^ m) a)).re =
          (inner ℂ y a).re +
            (inner ℂ y ((U ^ m) a - a)).re := by
        have hv : (U ^ m) a = a + ((U ^ m) a - a) := by abel
        calc
          (inner ℂ y ((U ^ m) a)).re =
              (inner ℂ y (a + ((U ^ m) a - a))).re :=
            congrArg (fun v ↦ (inner ℂ y v).re) hv
          _ = _ := by rw [inner_add_right, Complex.add_re]
      rw [heq]
      linarith
    have hweakLower : -(delta ^ 2 / 10) ≤
        (inner ℂ y ((U ^ m) (unitaryWeakPart U F))).re := by
      have habs := Complex.abs_re_le_norm
        (inner ℂ y ((U ^ m) (unitaryWeakPart U F)))
      have hlt := hm.2
      have hlo := (abs_lt.mp (lt_of_le_of_lt habs hlt)).1
      exact le_of_lt hlo
    have hrowEq : inner ℂ y ((U ^ m) F) = corr (Nat.pair 0 m + 1) := by
      have hi := hcorrInner (Nat.pair 0 m + 1)
      change inner ℂ y (ContinuousMap.toLp 2 mu ℂ
        (mrrGeneratorFamily A Hc W (Nat.pair 0 m + 1))) =
          corr (Nat.pair 0 m + 1) at hi
      rw [mrrGeneratorFamily_row] at hi
      change inner ℂ y (betaIndicatorL2 (mu : Measure BetaNat) (shift A m)) =
        corr (Nat.pair 0 m + 1) at hi
      rw [← betaKoopman_pow_indicator hpres A m] at hi
      exact hi
    have hparts : (corr (Nat.pair 0 m + 1)).re =
        (inner ℂ y ((U ^ m) (unitaryWeakPart U F))).re +
          (inner ℂ y ((U ^ m) a)).re := by
      have hFa : F = unitaryWeakPart U F + a := by
        dsimp only [unitaryWeakPart, a]
        abel
      have hmap := congrArg (fun v ↦ inner ℂ y ((U ^ m) v)) hFa
      rw [(U ^ m).map_add, inner_add_right] at hmap
      calc
        (corr (Nat.pair 0 m + 1)).re = (inner ℂ y ((U ^ m) F)).re :=
          congrArg Complex.re hrowEq.symm
        _ = (inner ℂ y ((U ^ m) (unitaryWeakPart U F)) +
            inner ℂ y ((U ^ m) a)).re := congrArg Complex.re hmap
        _ = _ := by rw [Complex.add_re]
    apply mrr_row_numeric (sq_nonneg delta) hyA rfl
    · have heqCW : (corr (Nat.pair 0 m + 1)).re -
          (inner ℂ y ((U ^ m) (unitaryWeakPart U F))).re =
          (inner ℂ y ((U ^ m) a)).re := by
        rw [hparts]
        ring
      rw [heqCW]
      exact hcompactLower
    · exact hweakLower
  have hrowDensity (m : ℕ) : Tendsto
      (fun k ↦ finsetDensity (Finset.range (L k))
        (ultraShift A p ∩ shift A m)) atTop
      (nhds (corr (Nat.pair 0 m + 1)).re) := by
    have hfinite (k : ℕ) :
        complexPrefixMean (L k) (fun n ↦
          u n * Z (Nat.pair 0 m + 1) (pure n)) =
        (finsetDensity (Finset.range (L k))
          (ultraShift A p ∩ shift A m) : ℂ) := by
      rw [show Z (Nat.pair 0 m + 1) = betaIndicatorComplex (shift A m) by
        exact mrrGeneratorFamily_row A Hc W m]
      change complexPrefixMean (L k) (fun n ↦
          (betaIndicator (ultraShift A p) (pure n) : ℂ) *
            betaIndicatorComplex (shift A m) (pure n)) = _
      exact complexPrefixMean_betaIndicators_eq_finsetDensity
        (ultraShift A p) (shift A m) (L k)
    have hc : Tendsto
        (fun k ↦ (finsetDensity (Finset.range (L k))
          (ultraShift A p ∩ shift A m) : ℂ)) atTop
        (nhds (corr (Nat.pair 0 m + 1))) := by
      have hcL : Tendsto
          (fun k ↦ complexPrefixMean (L k)
            (fun n ↦ u n * Z (Nat.pair 0 m + 1) (pure n))) atTop
          (nhds (corr (Nat.pair 0 m + 1))) := by
        exact hcorrLim (Nat.pair 0 m + 1)
      exact hcL.congr' (Eventually.of_forall fun k ↦ hfinite k)
    have hre := (Complex.continuous_re.tendsto
      (corr (Nat.pair 0 m + 1))).comp hc
    change Tendsto
      (fun k ↦ (finsetDensity (Finset.range (L k))
        (ultraShift A p ∩ shift A m) : ℂ).re) atTop
      (nhds (corr (Nat.pair 0 m + 1)).re) at hre
    simpa only [Complex.ofReal_re] using hre
  let threshold : ℝ := delta ^ 2 / 3
  have hgood : correlationGoodRows A p L (ENNReal.ofReal threshold) ∈
      (p : Filter ℕ) := by
    filter_upwards [hGoodBase] with m hm
    have hlt : threshold < (corr (Nat.pair 0 m + 1)).re := by
      have hr := hrowLower m hm
      dsimp only [threshold]
      nlinarith only [hr, sq_pos_of_pos hdelta]
    have hev := (tendsto_order.mp (hrowDensity m)).1 threshold hlt
    change ∀ᶠ k in atTop,
      ENNReal.ofReal threshold ≤
        (((((Finset.range (L k) : Set ℕ) ∩
          (ultraShift A p ∩ shift A m)).ncard : ℕ) : ℝ≥0∞) /
            (Finset.range (L k)).card)
    filter_upwards [hev] with k hk
    rw [ennreal_density_eq_ofReal (Finset.range (L k))
      (Finset.nonempty_range_iff.mpr (Nat.ne_of_gt (hLpos k)))
      (ultraShift A p ∩ shift A m)]
    exact ENNReal.ofReal_le_ofReal (le_of_lt hk)
  have hpCofinite : (p : Filter ℕ) ≤ cofinite := by
    exact hpEssential.trans (densityOneFilter_le_cofinite
      (fun k ↦ Finset.range (N k)) (by
        simpa only [Finset.card_range] using hNtop))
  apply erdos109_of_correlationGoodRows hLtop p hpCofinite
    (ENNReal.ofReal threshold)
  · exact (ENNReal.ofReal_pos.mpr (by
      dsimp only [threshold]
      positivity)).ne'
  · exact hgood

end

end Erdos109

#print axioms Erdos109.erdos_109
