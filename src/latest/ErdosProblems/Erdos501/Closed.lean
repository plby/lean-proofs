/-
Copyright (c) 2026 Elliot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot, Claude
-/
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Topology.Bases

/-!
# Infinite free sets for set mappings with closed values of small measure

This file formalizes the theorem of Newelski, Pawlikowski and Seredyński
(*Infinite free set for small measure set mappings*, Proc. Amer. Math. Soc. 100 (1987), 335–339)
which answers positively the second question of Erdős problem #501
(Erdős–Hajnal problem 38(B)):

> If, for every `x ∈ ℝ`, `A x ⊆ ℝ` is a closed set of Lebesgue measure `< 1`, must there be an
> independent set of size `3`, i.e. `x, y, z` distinct with none of them in the `A`-set of another?

Newelski–Pawlikowski–Seredyński proved much more: there is an *infinite* independent (free) set.

## Main results

* `Erdos501.exists_infinite_isFreeSet`: the general form (Theorem (b)(i) of the paper).
  Let `α` be a second countable topological space with a σ-finite Borel measure `μ` of infinite
  total mass, and let `F : α → Set α` have closed values with `μ (F x) ≤ C < ∞` for all `x`.
  Then there is an infinite free set for `F`, i.e. an infinite `X ⊆ α` with `x ∉ F y` for all
  distinct `x, y ∈ X`.
* `Erdos501.erdos501`: the Lebesgue-measure case on `ℝ` with `volume (A x) < 1`
  (Corollary 1 of the paper, the resolution of the second question of Erdős #501).
* `Erdos501.erdos501_three`: in particular there is an independent set of size `3`.
* `Erdos501.erdos501_pairwise`, `Erdos501.erdos501_ncard_three`: the same two statements in the
  exact form used by `google-deepmind/formal-conjectures`
  (`erdos_501.variants.newelski_pawlikowski_seredynski` and `erdos_501.variants.closed_size3`).

## Proof sketch

Write `Y ⊇ compat F Y x := {y ∈ Y | y ∉ F x ∧ x ∉ F y ∧ y ≠ x}` for the points of `Y` that are
compatible with `x`. It suffices (`exists_infinite_isFreeSet_of_step`) to prove the *key lemma*:
if `μ Y = ∞` (outer measure) then there is `x ∈ Y` with `μ (compat F Y x) = ∞`; then one picks
`x₀, x₁, …` recursively and `{xₙ}` is an infinite free set.

The key lemma is proved by contradiction (`exists_mem_measure_compat_eq_top`).
If it fails, then for every `x ∈ Y` the set `{t ∈ Y | x ∉ F t}` has finite outer measure, so
by continuity from below there is `N` and a set `Y' ⊆ Y` with `C < μ Y' < ∞` such that
`μ {t ∈ Y | x ∉ F t} ≤ N` for all `x ∈ Y'`. Fix `η > 0` with `C + 2η = μ Y'`.
For every `t` the closed set `F t` is approximated from outside by the complement of a finite
union `U t` of basic open sets, with `μ (Y' \ U t) ≤ C + η`. Since there are only countably many
finite families of basic open sets, there is a finite collection `𝒮` of them such that
`Z = {t ∈ Y | U t ∈ 𝒮}` has outer measure `> μ Y' * N / η`. Let `𝒥` be the finite set of basic
open sets appearing in `𝒮`, and for a point `y` let `τ y ⊆ 𝒥` be its "type" (the members of `𝒥`
containing `y`); the sets `τ ⁻¹' {σ}` (`σ ⊆ 𝒥`) are measurable and partition the space.
Two finite additivity computations (`sum_measure_fiber_inter`) give:

* for `t ∈ Z`, the total weight `μ (τ ⁻¹' {σ} ∩ Y')` of the types `σ` disjoint from `U t`
  is `μ (Y' \ U t) ≤ C + η`;
* for a type `σ` of positive weight, containing some `x ∈ Y'`, the set of `t ∈ Z` whose `U t`
  meets `σ` is contained in `{t ∈ Y | x ∉ F t}` and so has outer measure `≤ N`.

Taking measurable hulls `K σ` of these sets and applying Markov's inequality to
`g = ∑ σ, μ (τ ⁻¹' {σ} ∩ Y') • 𝟙 (K σ)` (whose integral is `≤ μ Y' * N`) produces a point
`t ∈ Z` with `g t < η`; the total weight `μ Y'` then splits as (types disjoint from `U t`)
`+` (types meeting `U t`) `< (C + η) + η = μ Y'`, a contradiction.

## References

* L. Newelski, J. Pawlikowski, W. Seredyński, *Infinite free set for small measure set mappings*,
  Proc. Amer. Math. Soc. 100 (1987), 335–339.
* P. Erdős, A. Hajnal, *Some remarks on set theory. VIII*, Michigan Math. J. 7 (1960), 187–191.
* https://www.erdosproblems.com/501
-/

open MeasureTheory Set TopologicalSpace
open scoped ENNReal

noncomputable section

namespace Erdos501

variable {α : Type*}

/-! ### Free sets and the abstract recursion -/

/-- A set `X` is *free* (or *independent*) for the set mapping `F : α → Set α` if `x ∉ F y`
for all distinct `x, y ∈ X`. -/
def IsFreeSet (F : α → Set α) (X : Set α) : Prop :=
  ∀ x ∈ X, ∀ y ∈ X, x ≠ y → x ∉ F y

/-- The points of `Y` which are *compatible* with `x`: those `y ∈ Y` with `y ≠ x`, `y ∉ F x` and
`x ∉ F y`. -/
def compat (F : α → Set α) (Y : Set α) (x : α) : Set α :=
  {y ∈ Y | y ∉ F x ∧ x ∉ F y ∧ y ≠ x}

theorem compat_subset (F : α → Set α) (Y : Set α) (x : α) : compat F Y x ⊆ Y :=
  fun _ hy => hy.1

/-- Abstract recursion: if a property `P` of sets holds for `univ`, and every set `Y` with `P Y`
contains a point `x` such that `P (compat F Y x)`, then there is an infinite free set for `F`. -/
theorem exists_infinite_isFreeSet_of_step (F : α → Set α) (P : Set α → Prop) (h0 : P univ)
    (hstep : ∀ Y, P Y → ∃ x ∈ Y, P (compat F Y x)) :
    ∃ X : Set α, X.Infinite ∧ IsFreeSet F X := by
  obtain ⟨x₀, -, -⟩ := hstep univ h0
  have : Nonempty α := ⟨x₀⟩
  choose! pt hpt using hstep
  -- `Ys (n + 1) = compat F (Ys n) (pt (Ys n))`, `Ys 0 = univ`
  set next : Set α → Set α := fun Y => compat F Y (pt Y) with hnext
  set Ys : ℕ → Set α := fun n => next^[n] univ with hYs
  have hYs_succ : ∀ n, Ys (n + 1) = compat F (Ys n) (pt (Ys n)) := fun n =>
    Function.iterate_succ_apply' next n univ
  have hP : ∀ n, P (Ys n) := by
    intro n
    induction n with
    | zero => simpa [hYs] using h0
    | succ n ih => rw [hYs_succ]; exact (hpt _ ih).2
  have hanti : Antitone Ys := antitone_nat_of_succ_le fun n => by
    rw [hYs_succ]; exact compat_subset _ _ _
  set xs : ℕ → α := fun n => pt (Ys n) with hxs
  have hmem : ∀ n, xs n ∈ Ys n := fun n => (hpt _ (hP n)).1
  have key : ∀ m n, m < n → xs n ∈ compat F (Ys m) (xs m) := by
    intro m n hmn
    have h : xs n ∈ Ys (m + 1) := hanti (Nat.succ_le_of_lt hmn) (hmem n)
    rwa [hYs_succ] at h
  have hinj : Function.Injective xs := by
    intro m n hmn
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact (key m n h).2.2.2 hmn.symm
    · exact (key n m h).2.2.2 hmn
  refine ⟨range xs, infinite_range_of_injective hinj, ?_⟩
  rintro _ ⟨m, rfl⟩ _ ⟨n, rfl⟩ hne
  have hmn : m ≠ n := fun h => hne (congrArg xs h)
  rcases lt_or_gt_of_ne hmn with h | h
  · exact (key m n h).2.2.1
  · exact (key n m h).2.1

/-! ### Measure-theoretic tools -/

/-- Finite additivity of the outer measure `μ (· ∩ Y')` along the fibres of a map `τ` into a
finite set `S`. -/
theorem sum_measure_fiber_inter {β ι : Type*} [MeasurableSpace β] (μ : Measure β)
    (τ : β → ι) (S : Finset ι) (hτ : ∀ i, MeasurableSet (τ ⁻¹' {i})) (hS : ∀ y, τ y ∈ S)
    (Y' : Set β) (Q : ι → Prop) [DecidablePred Q] :
    ∑ i ∈ S with Q i, μ (τ ⁻¹' {i} ∩ Y') = μ ({y | Q (τ y)} ∩ Y') := by
  have hdisj : Set.PairwiseDisjoint (↑(S.filter Q) : Set ι) (fun i => τ ⁻¹' {i}) :=
    fun i _ j _ hij => Set.disjoint_left.2 fun y hyi hyj =>
      hij ((show τ y = i from hyi).symm.trans (show τ y = j from hyj))
  have hU : ({y | Q (τ y)} : Set β) = ⋃ i ∈ S.filter Q, τ ⁻¹' {i} := by
    ext y
    constructor
    · intro h
      exact mem_iUnion₂.2 ⟨τ y, Finset.mem_filter.2 ⟨hS y, h⟩, rfl⟩
    · intro h
      obtain ⟨i, hi, hyi⟩ := mem_iUnion₂.1 h
      have hyi' : τ y = i := hyi
      rw [mem_ofPred_eq, hyi']
      exact (Finset.mem_filter.1 hi).2
  have hmeas : MeasurableSet (⋃ i ∈ S.filter Q, τ ⁻¹' {i}) :=
    Finset.measurableSet_biUnion _ fun i _ => hτ i
  calc ∑ i ∈ S with Q i, μ (τ ⁻¹' {i} ∩ Y')
      = ∑ i ∈ S with Q i, μ.restrict Y' (τ ⁻¹' {i}) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Measure.restrict_apply (hτ i)]
    _ = μ.restrict Y' (⋃ i ∈ S.filter Q, τ ⁻¹' {i}) :=
        (measure_biUnion_finset hdisj fun i _ => hτ i).symm
    _ = μ ({y | Q (τ y)} ∩ Y') := by rw [Measure.restrict_apply hmeas, hU]

/-- The unfiltered version of `sum_measure_fiber_inter`. -/
theorem sum_measure_fiber_inter_eq {β ι : Type*} [MeasurableSpace β] (μ : Measure β)
    (τ : β → ι) (S : Finset ι) (hτ : ∀ i, MeasurableSet (τ ⁻¹' {i})) (hS : ∀ y, τ y ∈ S)
    (Y' : Set β) : ∑ i ∈ S, μ (τ ⁻¹' {i} ∩ Y') = μ Y' := by
  have hdisj : Set.PairwiseDisjoint (↑S : Set ι) (fun i => τ ⁻¹' {i}) :=
    fun i _ j _ hij => Set.disjoint_left.2 fun y hyi hyj =>
      hij ((show τ y = i from hyi).symm.trans (show τ y = j from hyj))
  have hU : (⋃ i ∈ S, τ ⁻¹' {i}) = univ := by
    refine eq_univ_of_forall fun y => ?_
    exact mem_iUnion₂.2 ⟨τ y, hS y, rfl⟩
  have hmeas : MeasurableSet (⋃ i ∈ S, τ ⁻¹' {i}) :=
    Finset.measurableSet_biUnion _ fun i _ => hτ i
  calc ∑ i ∈ S, μ (τ ⁻¹' {i} ∩ Y')
      = ∑ i ∈ S, μ.restrict Y' (τ ⁻¹' {i}) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Measure.restrict_apply (hτ i)]
    _ = μ.restrict Y' (⋃ i ∈ S, τ ⁻¹' {i}) :=
        (measure_biUnion_finset hdisj fun i _ => hτ i).symm
    _ = μ Y' := by rw [Measure.restrict_apply hmeas, hU, univ_inter]

section Topological

variable [TopologicalSpace α] [SecondCountableTopology α]

/-- The union of a finite family of sets from the countable basis `countableBasis α`. -/
def Ubasis (s : Finset ↥(countableBasis α)) : Set α :=
  ⋃ u ∈ s, (u : Set α)

theorem mem_Ubasis {s : Finset ↥(countableBasis α)} {y : α} :
    y ∈ Ubasis s ↔ ∃ u ∈ s, y ∈ (u : Set α) := by
  simp [Ubasis]

theorem Ubasis_mono {s t : Finset ↥(countableBasis α)} (h : s ⊆ t) : Ubasis s ⊆ Ubasis t := by
  intro y hy
  rw [mem_Ubasis] at hy ⊢
  obtain ⟨u, hu, hyu⟩ := hy
  exact ⟨u, h hu, hyu⟩

variable [MeasurableSpace α] [OpensMeasurableSpace α]

theorem measurableSet_Ubasis (s : Finset ↥(countableBasis α)) : MeasurableSet (Ubasis s) :=
  Finset.measurableSet_biUnion _ fun u _ => (isOpen_of_mem_countableBasis u.2).measurableSet

variable {μ : Measure α}

/-- Approximating a closed set `K` from the outside by the complement of a finite union of basic
open sets, up to `ε`, relative to a set `Y'` of finite outer measure. -/
theorem exists_Ubasis_approx {Y' K : Set α} (hY' : μ Y' ≠ ∞) (hK : IsClosed K) {ε : ℝ≥0∞}
    (hε : ε ≠ 0) :
    ∃ s : Finset ↥(countableBasis α), Ubasis s ⊆ Kᶜ ∧ μ (Y' \ Ubasis s) ≤ μ K + ε := by
  classical
  have : Countable ↥(countableBasis α) := (countable_countableBasis α).to_subtype
  -- the directed family of `Y' ∩ Ubasis s` over those `s` with `Ubasis s ⊆ Kᶜ`
  have hdir : Directed (· ⊆ ·)
      (fun s : {s : Finset ↥(countableBasis α) // Ubasis s ⊆ Kᶜ} => Y' ∩ Ubasis s.1) := by
    rintro ⟨s₁, hs₁⟩ ⟨s₂, hs₂⟩
    refine ⟨⟨s₁ ∪ s₂, ?_⟩, ?_, ?_⟩
    · intro y hy
      rw [mem_Ubasis] at hy
      obtain ⟨u, hu, hyu⟩ := hy
      rcases Finset.mem_union.1 hu with hu | hu
      · exact hs₁ (mem_Ubasis.2 ⟨u, hu, hyu⟩)
      · exact hs₂ (mem_Ubasis.2 ⟨u, hu, hyu⟩)
    · exact inter_subset_inter_right _ (Ubasis_mono Finset.subset_union_left)
    · exact inter_subset_inter_right _ (Ubasis_mono Finset.subset_union_right)
  have hunion :
      ⋃ s : {s : Finset ↥(countableBasis α) // Ubasis s ⊆ Kᶜ}, (Y' ∩ Ubasis s.1) = Y' \ K := by
    ext y
    simp only [mem_iUnion, mem_inter_iff, mem_sdiff]
    constructor
    · rintro ⟨s, hyY, hyU⟩
      exact ⟨hyY, fun hyK => s.2 hyU hyK⟩
    · rintro ⟨hyY, hyK⟩
      obtain ⟨u, hu, hyu, huK⟩ :=
        (isBasis_countableBasis α).exists_subset_of_mem_open (show y ∈ Kᶜ from hyK)
          hK.isOpen_compl
      refine ⟨⟨{⟨u, hu⟩}, ?_⟩, hyY, ?_⟩
      · intro z hz
        rw [mem_Ubasis] at hz
        obtain ⟨v, hv, hzv⟩ := hz
        rw [Finset.mem_singleton] at hv
        subst hv
        exact huK hzv
      · exact mem_Ubasis.2 ⟨⟨u, hu⟩, Finset.mem_singleton_self _, hyu⟩
  have hsup : μ (Y' \ K) =
      ⨆ s : {s : Finset ↥(countableBasis α) // Ubasis s ⊆ Kᶜ}, μ (Y' ∩ Ubasis s.1) := by
    rw [← hunion, hdir.measure_iUnion]
  -- choose `s` with `μ (Y' \ K) ≤ μ (Y' ∩ Ubasis s) + ε`
  obtain ⟨s, hs⟩ : ∃ s : {s : Finset ↥(countableBasis α) // Ubasis s ⊆ Kᶜ},
      μ (Y' \ K) ≤ μ (Y' ∩ Ubasis s.1) + ε := by
    by_cases h0 : μ (Y' \ K) = 0
    · refine ⟨⟨∅, ?_⟩, by rw [h0]; exact zero_le⟩
      intro y hy
      rw [mem_Ubasis] at hy
      obtain ⟨u, hu, -⟩ := hy
      exact absurd hu (Finset.notMem_empty u)
    · have hfin : μ (Y' \ K) ≠ ∞ := ne_top_of_le_ne_top hY' (measure_mono sdiff_subset)
      have hlt : μ (Y' \ K) - ε <
          ⨆ s : {s : Finset ↥(countableBasis α) // Ubasis s ⊆ Kᶜ}, μ (Y' ∩ Ubasis s.1) :=
        (ENNReal.sub_lt_self hfin h0 hε).trans_eq hsup
      obtain ⟨s, hs⟩ := lt_iSup_iff.1 hlt
      exact ⟨s, tsub_le_iff_right.1 hs.le⟩
  refine ⟨s.1, s.2, ?_⟩
  have hmeasU : MeasurableSet (Ubasis s.1) := measurableSet_Ubasis s.1
  have h1 : μ ((Y' \ K) ∩ Ubasis s.1) + μ ((Y' \ K) \ Ubasis s.1) = μ (Y' \ K) :=
    measure_inter_add_sdiff _ hmeasU
  have h2 : (Y' \ K) ∩ Ubasis s.1 = Y' ∩ Ubasis s.1 := by
    ext y
    simp only [mem_inter_iff, mem_sdiff]
    constructor
    · rintro ⟨⟨h, _⟩, h'⟩
      exact ⟨h, h'⟩
    · rintro ⟨h, h'⟩
      exact ⟨⟨h, fun hK' => s.2 h' hK'⟩, h'⟩
  rw [h2] at h1
  have h3 : μ ((Y' \ K) \ Ubasis s.1) ≤ ε := by
    have hfin : μ (Y' ∩ Ubasis s.1) ≠ ∞ :=
      ne_top_of_le_ne_top hY' (measure_mono inter_subset_left)
    exact ENNReal.le_of_add_le_add_left hfin (h1.le.trans hs)
  calc μ (Y' \ Ubasis s.1) ≤ μ ((Y' ∩ K) ∪ ((Y' \ K) \ Ubasis s.1)) := by
        apply measure_mono
        intro y hy
        by_cases hyK : y ∈ K
        · exact Or.inl ⟨hy.1, hyK⟩
        · exact Or.inr ⟨⟨hy.1, hyK⟩, hy.2⟩
    _ ≤ μ (Y' ∩ K) + μ ((Y' \ K) \ Ubasis s.1) := measure_union_le _ _
    _ ≤ μ K + ε := add_le_add (measure_mono inter_subset_right) h3

/-! ### The key lemma -/

/-- **Key lemma.** Let `μ` be a σ-finite Borel measure on a second countable space, and let
`F : α → Set α` have closed values with `μ (F x) ≤ C < ∞`. If `μ Y = ∞` (outer measure), then
there is `x ∈ Y` such that the set `compat F Y x` of points of `Y` compatible with `x` still has
infinite outer measure. -/
theorem exists_mem_measure_compat_eq_top [SigmaFinite μ] {F : α → Set α}
    (hF : ∀ x, IsClosed (F x)) {C : ℝ≥0∞} (hC : C ≠ ∞) (hFC : ∀ x, μ (F x) ≤ C) {Y : Set α}
    (hY : μ Y = ∞) : ∃ x ∈ Y, μ (compat F Y x) = ∞ := by
  classical
  have : Countable ↥(countableBasis α) := (countable_countableBasis α).to_subtype
  by_contra hcon'
  have hcon : ∀ x ∈ Y, μ (compat F Y x) ≠ ∞ := fun x hx h => hcon' ⟨x, hx, h⟩
  -- Step 1: for `x ∈ Y`, the set `{t ∈ Y | x ∉ F t}` has finite outer measure.
  have hsingle : ∀ x : α, μ {x} ≠ ∞ := by
    intro x
    obtain ⟨n, hn⟩ : ∃ n, x ∈ spanningSets μ n := by
      have : x ∈ ⋃ n, spanningSets μ n := by rw [iUnion_spanningSets]; exact mem_univ x
      exact mem_iUnion.1 this
    exact ne_top_of_le_ne_top (measure_spanningSets_lt_top μ n).ne
      (measure_mono (singleton_subset_iff.2 hn))
  have h1 : ∀ x ∈ Y, μ {t ∈ Y | x ∉ F t} ≠ ∞ := by
    intro x hx
    have hsub : {t ∈ Y | x ∉ F t} ⊆ compat F Y x ∪ F x ∪ {x} := by
      intro t ht
      by_cases htF : t ∈ F x
      · exact Or.inl (Or.inr htF)
      by_cases htx : t = x
      · exact Or.inr htx
      · exact Or.inl (Or.inl ⟨ht.1, htF, ht.2, htx⟩)
    refine ne_top_of_le_ne_top ?_ (measure_mono hsub)
    refine ne_top_of_le_ne_top ?_
      ((measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl))
    exact ENNReal.add_ne_top.2
      ⟨ENNReal.add_ne_top.2 ⟨hcon x hx, ne_top_of_le_ne_top hC (hFC x)⟩, hsingle x⟩
  -- Step 2: choose `N` with `C < μ {x ∈ Y | μ {t ∈ Y | x ∉ F t} ≤ N}`.
  have hYN_mono : Monotone (fun N : ℕ => {x ∈ Y | μ {t ∈ Y | x ∉ F t} ≤ N}) := by
    intro N M hNM x hx
    exact ⟨hx.1, hx.2.trans (by exact_mod_cast hNM)⟩
  have hYN_union : ⋃ N : ℕ, {x ∈ Y | μ {t ∈ Y | x ∉ F t} ≤ N} = Y := by
    apply Subset.antisymm
    · exact iUnion_subset fun N x hx => hx.1
    · intro x hx
      obtain ⟨N, hN⟩ := ENNReal.exists_nat_gt (h1 x hx)
      exact mem_iUnion.2 ⟨N, hx, hN.le⟩
  obtain ⟨N, hN⟩ : ∃ N : ℕ, C < μ {x ∈ Y | μ {t ∈ Y | x ∉ F t} ≤ N} := by
    have hsup : ⨆ N : ℕ, μ {x ∈ Y | μ {t ∈ Y | x ∉ F t} ≤ N} = ∞ := by
      rw [← hYN_mono.measure_iUnion, hYN_union, hY]
    exact lt_iSup_iff.1 (by rw [hsup]; exact hC.lt_top)
  -- Step 3: cut down to a set `Y'` of finite outer measure with `C < μ Y'`.
  obtain ⟨n, hn⟩ : ∃ n : ℕ,
      C < μ ({x ∈ Y | μ {t ∈ Y | x ∉ F t} ≤ N} ∩ spanningSets μ n) := by
    have hmono : Monotone
        (fun n : ℕ => {x ∈ Y | μ {t ∈ Y | x ∉ F t} ≤ N} ∩ spanningSets μ n) :=
      fun n m hnm => inter_subset_inter_right _ (monotone_spanningSets μ hnm)
    have hsup : ⨆ n : ℕ, μ ({x ∈ Y | μ {t ∈ Y | x ∉ F t} ≤ N} ∩ spanningSets μ n)
        = μ {x ∈ Y | μ {t ∈ Y | x ∉ F t} ≤ N} := by
      rw [← hmono.measure_iUnion, ← inter_iUnion, iUnion_spanningSets, inter_univ]
    exact lt_iSup_iff.1 (by rw [hsup]; exact hN)
  have hY'Y : {x ∈ Y | μ {t ∈ Y | x ∉ F t} ≤ N} ∩ spanningSets μ n ⊆ Y :=
    fun x hx => hx.1.1
  have hY'N : ∀ x ∈ {x ∈ Y | μ {t ∈ Y | x ∉ F t} ≤ N} ∩ spanningSets μ n,
      μ {t ∈ Y | x ∉ F t} ≤ N :=
    fun x hx => hx.1.2
  have hY'fin : μ ({x ∈ Y | μ {t ∈ Y | x ∉ F t} ≤ N} ∩ spanningSets μ n) ≠ ∞ :=
    ne_top_of_le_ne_top (measure_spanningSets_lt_top μ n).ne (measure_mono inter_subset_right)
  set Y' : Set α := {x ∈ Y | μ {t ∈ Y | x ∉ F t} ≤ N} ∩ spanningSets μ n with hY'def
  clear_value Y'
  have hCc : C < μ Y' := hn
  -- Step 4: `η > 0` with `C + η + η = μ Y'`.
  obtain ⟨η, hη0, hηsum⟩ : ∃ η : ℝ≥0∞, η ≠ 0 ∧ C + η + η = μ Y' := by
    refine ⟨(μ Y' - C) / 2, ?_, ?_⟩
    · exact (ENNReal.div_pos_iff.2 ⟨(tsub_pos_iff_lt.2 hCc).ne', ENNReal.ofNat_ne_top⟩).ne'
    · rw [add_assoc, ENNReal.add_halves, add_tsub_cancel_of_le hCc.le]
  have hηfin : η ≠ ∞ := ne_top_of_le_ne_top hY'fin (by rw [← hηsum]; exact le_add_self)
  -- Step 5: approximate each closed set `F t` from outside by the complement of a finite union
  -- of basic open sets `Ubasis (st t)`, with error `η` relative to `Y'`.
  have hB1 : ∀ t : α, ∃ s : Finset ↥(countableBasis α),
      Ubasis s ⊆ (F t)ᶜ ∧ μ (Y' \ Ubasis s) ≤ C + η := fun t => by
    obtain ⟨s, hs1, hs2⟩ := exists_Ubasis_approx (μ := μ) hY'fin (hF t) hη0
    exact ⟨s, hs1, hs2.trans (add_le_add (hFC t) le_rfl)⟩
  choose st hst1 hst2 using hB1
  -- Step 6: a finite family `𝒮` of "types" such that `Z = {t ∈ Y | st t ∈ 𝒮}` is large.
  set L : ℝ≥0∞ := μ Y' * N / η with hL
  have hLfin : L < ∞ :=
    ENNReal.div_lt_top (ENNReal.mul_ne_top hY'fin (ENNReal.natCast_ne_top N)) hη0
  obtain ⟨𝒮, h𝒮⟩ : ∃ 𝒮 : Finset (Finset ↥(countableBasis α)), L < μ {t ∈ Y | st t ∈ 𝒮} := by
    have hdir : Directed (· ⊆ ·)
        (fun 𝒮 : Finset (Finset ↥(countableBasis α)) => {t ∈ Y | st t ∈ 𝒮}) := by
      intro 𝒮₁ 𝒮₂
      exact ⟨𝒮₁ ∪ 𝒮₂, fun t ht => ⟨ht.1, Finset.mem_union_left _ ht.2⟩,
        fun t ht => ⟨ht.1, Finset.mem_union_right _ ht.2⟩⟩
    have hunion : ⋃ 𝒮 : Finset (Finset ↥(countableBasis α)), {t ∈ Y | st t ∈ 𝒮} = Y := by
      apply Subset.antisymm (iUnion_subset fun 𝒮 t ht => ht.1)
      intro t ht
      exact mem_iUnion.2 ⟨{st t}, ht, Finset.mem_singleton_self _⟩
    have hsup : ⨆ 𝒮 : Finset (Finset ↥(countableBasis α)), μ {t ∈ Y | st t ∈ 𝒮} = ∞ := by
      rw [← hdir.measure_iUnion, hunion, hY]
    exact lt_iSup_iff.1 (by rw [hsup]; exact hLfin)
  have hZY : {t ∈ Y | st t ∈ 𝒮} ⊆ Y := fun t ht => ht.1
  have hZ𝒮 : ∀ t ∈ {t ∈ Y | st t ∈ 𝒮}, st t ∈ 𝒮 := fun t ht => ht.2
  set Z : Set α := {t ∈ Y | st t ∈ 𝒮} with hZdef
  clear_value Z
  -- Step 7: the finite set `𝒥` of basic open sets involved, and the "type" `τ y ⊆ 𝒥` of a point.
  set 𝒥 : Finset ↥(countableBasis α) := 𝒮.sup id with h𝒥
  have hst𝒥 : ∀ t ∈ Z, st t ⊆ 𝒥 := fun t ht => Finset.le_sup (f := id) (hZ𝒮 t ht)
  obtain ⟨τ, hτdef⟩ : ∃ τ : α → Finset ↥(countableBasis α),
      τ = fun y => 𝒥.filter (fun u : ↥(countableBasis α) => y ∈ (u : Set α)) := ⟨_, rfl⟩
  have hτ𝒥 : ∀ y, τ y ⊆ 𝒥 := fun y => by
    rw [hτdef]; exact Finset.filter_subset _ _
  have hτmem : ∀ y (u : ↥(countableBasis α)), u ∈ τ y ↔ u ∈ 𝒥 ∧ y ∈ (u : Set α) :=
    fun y u => by rw [hτdef]; exact Finset.mem_filter
  -- membership in `Ubasis s` for `s ⊆ 𝒥` only depends on the type
  have hkey : ∀ s : Finset ↥(countableBasis α), s ⊆ 𝒥 → ∀ y,
      (y ∉ Ubasis s ↔ Disjoint s (τ y)) := by
    intro s hs y
    rw [Finset.disjoint_left]
    constructor
    · intro hy u hus huτ
      exact hy (mem_Ubasis.2 ⟨u, hus, ((hτmem y u).1 huτ).2⟩)
    · intro h hy
      obtain ⟨u, hus, hyu⟩ := mem_Ubasis.1 hy
      exact h hus ((hτmem y u).2 ⟨hs hus, hyu⟩)
  -- the fibres of `τ` are measurable
  have hτmeas : ∀ σ : Finset ↥(countableBasis α), MeasurableSet (τ ⁻¹' {σ}) := by
    intro σ
    by_cases hσ : σ ⊆ 𝒥
    · have hpre : τ ⁻¹' {σ} = ⋂ u ∈ 𝒥, {y | y ∈ (u : Set α) ↔ u ∈ σ} := by
        ext y
        simp only [mem_preimage, mem_singleton_iff, mem_iInter, mem_ofPred_eq]
        constructor
        · intro h u hu
          rw [← h, hτmem]
          exact ⟨fun hyu => ⟨hu, hyu⟩, fun h' => h'.2⟩
        · intro h
          ext u
          rw [hτmem]
          constructor
          · rintro ⟨hu, hyu⟩
            exact (h u hu).1 hyu
          · intro huσ
            exact ⟨hσ huσ, (h u (hσ huσ)).2 huσ⟩
      rw [hpre]
      refine Finset.measurableSet_biInter _ fun u _ => ?_
      have hu : MeasurableSet (u : Set α) := (isOpen_of_mem_countableBasis u.2).measurableSet
      by_cases huσ : u ∈ σ
      · have : {y | y ∈ (u : Set α) ↔ u ∈ σ} = (u : Set α) := by ext y; simp [huσ]
        rw [this]; exact hu
      · have : {y | y ∈ (u : Set α) ↔ u ∈ σ} = (u : Set α)ᶜ := by ext y; simp [huσ]
        rw [this]; exact hu.compl
    · have hpre : τ ⁻¹' {σ} = ∅ := by
        ext y
        simp only [mem_preimage, mem_singleton_iff, mem_empty_iff_false, iff_false]
        intro h
        exact hσ (h ▸ hτ𝒥 y)
      rw [hpre]
      exact MeasurableSet.empty
  have hτpow : ∀ y, τ y ∈ 𝒥.powerset := fun y => Finset.mem_powerset.2 (hτ𝒥 y)
  -- the weights `μ (τ ⁻¹' {σ} ∩ Y')`, `σ ⊆ 𝒥`, add up to `μ Y'`
  have hsum_all : ∑ σ ∈ 𝒥.powerset, μ (τ ⁻¹' {σ} ∩ Y') = μ Y' :=
    sum_measure_fiber_inter_eq μ τ 𝒥.powerset hτmeas hτpow Y'
  -- (I): for `t ∈ Z`, the weight of the types disjoint from `st t` is at most `C + η`
  have hI : ∀ t ∈ Z, ∑ σ ∈ 𝒥.powerset with Disjoint (st t) σ, μ (τ ⁻¹' {σ} ∩ Y') ≤ C + η := by
    intro t ht
    rw [sum_measure_fiber_inter μ τ 𝒥.powerset hτmeas hτpow Y' (fun σ => Disjoint (st t) σ)]
    have : {y | Disjoint (st t) (τ y)} ∩ Y' = Y' \ Ubasis (st t) := by
      ext y
      simp only [mem_inter_iff, mem_ofPred_eq, mem_sdiff]
      rw [← hkey (st t) (hst𝒥 t ht) y]
      exact and_comm
    rw [this]
    exact hst2 t
  -- (II): for a type `σ` of positive weight, the set of `t ∈ Z` with `st t` meeting `σ` has
  -- outer measure at most `N`
  have hII : ∀ σ, μ (τ ⁻¹' {σ} ∩ Y') ≠ 0 → μ (Z \ {t | Disjoint (st t) σ}) ≤ N := by
    intro σ hσ
    obtain ⟨x, hxτ, hxY'⟩ := nonempty_of_measure_ne_zero hσ
    have hxσ : τ x = σ := hxτ
    refine (measure_mono ?_).trans (hY'N x hxY')
    intro t ht
    have htZ : t ∈ Z := ht.1
    have hnd : ¬ Disjoint (st t) σ := ht.2
    refine ⟨hZY htZ, fun hxF => ?_⟩
    rw [← hxσ, ← hkey (st t) (hst𝒥 t htZ) x, not_not] at hnd
    exact hst1 t hnd hxF
  -- Step 8: measurable hulls `K σ ⊇ Z \ {t | Disjoint (st t) σ}` and Markov's inequality.
  obtain ⟨K, hKmeas, hKsub, hKμ⟩ : ∃ K : Finset ↥(countableBasis α) → Set α,
      (∀ σ, MeasurableSet (K σ)) ∧ (∀ σ, Z \ {t | Disjoint (st t) σ} ⊆ K σ) ∧
      (∀ σ, μ (K σ) = μ (Z \ {t | Disjoint (st t) σ})) :=
    ⟨fun σ => toMeasurable μ (Z \ {t | Disjoint (st t) σ}),
      fun σ => measurableSet_toMeasurable _ _, fun σ => subset_toMeasurable _ _,
      fun σ => measure_toMeasurable _⟩
  set g : α → ℝ≥0∞ := fun t => ∑ σ ∈ 𝒥.powerset, μ (τ ⁻¹' {σ} ∩ Y') * (K σ).indicator 1 t
    with hg
  have hgmeas : Measurable g := by
    show Measurable fun t => ∑ σ ∈ 𝒥.powerset, μ (τ ⁻¹' {σ} ∩ Y') * (K σ).indicator 1 t
    exact Finset.measurable_sum _ fun σ _ =>
      (measurable_one.indicator (hKmeas σ)).const_mul (μ (τ ⁻¹' {σ} ∩ Y'))
  have hgint : ∫⁻ t, g t ∂μ ≤ μ Y' * N := by
    calc ∫⁻ t, g t ∂μ
        = ∑ σ ∈ 𝒥.powerset, μ (τ ⁻¹' {σ} ∩ Y') * μ (K σ) := by
          show ∫⁻ t, ∑ σ ∈ 𝒥.powerset, μ (τ ⁻¹' {σ} ∩ Y') * (K σ).indicator 1 t ∂μ = _
          rw [lintegral_finsetSum _ fun σ _ =>
            (measurable_one.indicator (hKmeas σ)).const_mul (μ (τ ⁻¹' {σ} ∩ Y'))]
          refine Finset.sum_congr rfl fun σ _ => ?_
          rw [lintegral_const_mul _ (measurable_one.indicator (hKmeas σ)),
            lintegral_indicator_one (hKmeas σ)]
      _ ≤ ∑ σ ∈ 𝒥.powerset, μ (τ ⁻¹' {σ} ∩ Y') * N := by
          refine Finset.sum_le_sum fun σ _ => ?_
          by_cases h0 : μ (τ ⁻¹' {σ} ∩ Y') = 0
          · simp [h0]
          · rw [hKμ σ]
            exact mul_le_mul' le_rfl (hII σ h0)
      _ = μ Y' * N := by rw [← Finset.sum_mul, hsum_all]
  have hE : μ {t | η ≤ g t} ≤ L := by
    have h : η * μ {t | η ≤ g t} ≤ ∫⁻ t, g t ∂μ :=
      mul_meas_ge_le_lintegral₀ hgmeas.aemeasurable η
    have h' : μ {t | η ≤ g t} * η ≤ μ Y' * N := by
      rw [mul_comm]; exact h.trans hgint
    rw [hL, ENNReal.le_div_iff_mul_le (Or.inl hη0)
      (Or.inr (ENNReal.mul_ne_top hY'fin (ENNReal.natCast_ne_top N)))]
    exact h'
  -- Step 9: pick `t ∈ Z` with `g t < η` and derive the contradiction.
  obtain ⟨t, htZ, htE⟩ : (Z \ {t | η ≤ g t}).Nonempty := by
    rw [nonempty_iff_ne_empty]
    intro hempty
    rw [sdiff_eq_empty] at hempty
    exact absurd ((measure_mono hempty).trans hE) (not_le.2 h𝒮)
  have htE' : ¬ η ≤ g t := htE
  have htg : g t < η := not_le.1 htE'
  have hnotR : ∑ σ ∈ 𝒥.powerset with ¬ Disjoint (st t) σ, μ (τ ⁻¹' {σ} ∩ Y') ≤ g t := by
    show _ ≤ ∑ σ ∈ 𝒥.powerset, μ (τ ⁻¹' {σ} ∩ Y') * (K σ).indicator 1 t
    calc ∑ σ ∈ 𝒥.powerset with ¬ Disjoint (st t) σ, μ (τ ⁻¹' {σ} ∩ Y')
        = ∑ σ ∈ 𝒥.powerset with ¬ Disjoint (st t) σ,
            μ (τ ⁻¹' {σ} ∩ Y') * (K σ).indicator 1 t := by
          refine Finset.sum_congr rfl fun σ hσ => ?_
          have htK : t ∈ K σ := hKsub σ ⟨htZ, (Finset.mem_filter.1 hσ).2⟩
          rw [indicator_of_mem htK, Pi.one_apply, mul_one]
      _ ≤ ∑ σ ∈ 𝒥.powerset, μ (τ ⁻¹' {σ} ∩ Y') * (K σ).indicator 1 t :=
          Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  have htotal : μ Y' = (∑ σ ∈ 𝒥.powerset with Disjoint (st t) σ, μ (τ ⁻¹' {σ} ∩ Y'))
      + ∑ σ ∈ 𝒥.powerset with ¬ Disjoint (st t) σ, μ (τ ⁻¹' {σ} ∩ Y') := by
    rw [Finset.sum_filter_add_sum_filter_not, hsum_all]
  have hlt : μ Y' < C + η + η := by
    rw [htotal]
    exact ENNReal.add_lt_add_of_le_of_lt
      (ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hC, hηfin⟩) (hI t htZ)) (hI t htZ)
      (hnotR.trans_lt htg)
  rw [hηsum] at hlt
  exact lt_irrefl _ hlt

/-! ### The main theorem and the resolution of Erdős problem 501 (second question) -/

/-- **Newelski–Pawlikowski–Seredyński (1987), Theorem (b)(i).**
Let `μ` be a σ-finite Borel measure on a second countable topological space `α` with
`μ univ = ∞`, and let `F : α → Set α` have closed values with `μ (F x) ≤ C < ∞` for all `x`.
Then there is an infinite free set for `F`: an infinite set `X` with `x ∉ F y` for all distinct
`x, y ∈ X`. -/
theorem exists_infinite_isFreeSet [SigmaFinite μ] (hμ : μ univ = ∞) {F : α → Set α}
    (hF : ∀ x, IsClosed (F x)) {C : ℝ≥0∞} (hC : C ≠ ∞) (hFC : ∀ x, μ (F x) ≤ C) :
    ∃ X : Set α, X.Infinite ∧ IsFreeSet F X :=
  exists_infinite_isFreeSet_of_step F (fun Y => μ Y = ∞) hμ
    fun _ hY => exists_mem_measure_compat_eq_top hF hC hFC hY

end Topological

/-- **Erdős problem #501, second question** (answered positively by
Newelski–Pawlikowski–Seredyński, Corollary 1): if `A x ⊆ ℝ` is a closed set of Lebesgue measure
`< 1` for every `x ∈ ℝ`, then there is an infinite independent set, i.e. an infinite `X ⊆ ℝ`
such that `x ∉ A y` for all distinct `x, y ∈ X`. -/
theorem erdos501 (A : ℝ → Set ℝ) (hA : ∀ x, IsClosed (A x)) (hA1 : ∀ x, volume (A x) < 1) :
    ∃ X : Set ℝ, X.Infinite ∧ ∀ x ∈ X, ∀ y ∈ X, x ≠ y → x ∉ A y :=
  exists_infinite_isFreeSet Real.volume_univ hA ENNReal.one_ne_top fun x => (hA1 x).le

/-- In particular (the literal second question of Erdős #501): under the same hypotheses there
is an independent set of size `3`. -/
theorem erdos501_three (A : ℝ → Set ℝ) (hA : ∀ x, IsClosed (A x))
    (hA1 : ∀ x, volume (A x) < 1) :
    ∃ T : Finset ℝ, T.card = 3 ∧ ∀ x ∈ T, ∀ y ∈ T, x ≠ y → x ∉ A y := by
  obtain ⟨X, hXinf, hXfree⟩ := erdos501 A hA hA1
  obtain ⟨T, hTX, hT⟩ := hXinf.exists_subset_card_eq 3
  exact ⟨T, hT, fun x hx y hy hxy => hXfree x (hTX hx) y (hTX hy) hxy⟩

/-! ### The statements used in `google-deepmind/formal-conjectures`

`FormalConjectures/ErdosProblems/501.lean` in the formal-conjectures repository states the
second question of Erdős #501 as `erdos_501.variants.closed_size3` and the NPS87 theorem as
`erdos_501.variants.newelski_pawlikowski_seredynski`, both with independence expressed as
`X.Pairwise (fun x y => x ∉ A y)`; the following two theorems are exactly the right-hand sides
of those `answer(True) ↔ …` statements. -/

/-- The right-hand side of `erdos_501.variants.newelski_pawlikowski_seredynski`
in formal-conjectures. -/
theorem erdos501_pairwise (A : ℝ → Set ℝ) (hA : ∀ x, IsClosed (A x))
    (hA1 : ∀ x, volume (A x) < 1) :
    ∃ X : Set ℝ, X.Infinite ∧ X.Pairwise (fun x y => x ∉ A y) := by
  obtain ⟨X, hX, hfree⟩ := erdos501 A hA hA1
  exact ⟨X, hX, fun x hx y hy hxy => hfree x hx y hy hxy⟩

/-- The right-hand side of `erdos_501.variants.closed_size3` in formal-conjectures
(the literal second question of Erdős #501). -/
theorem erdos501_ncard_three (A : ℝ → Set ℝ) (hA : ∀ x, IsClosed (A x))
    (hA1 : ∀ x, volume (A x) < 1) :
    ∃ X : Set ℝ, 3 ≤ X.ncard ∧ X.Pairwise (fun x y => x ∉ A y) := by
  obtain ⟨T, hT, hfree⟩ := erdos501_three A hA hA1
  refine ⟨(T : Set ℝ), ?_, fun x hx y hy hxy => hfree x hx y hy hxy⟩
  rw [Set.ncard_coe_finset, hT]

end Erdos501

end
