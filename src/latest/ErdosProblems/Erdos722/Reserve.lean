/-
Copyright 2026 The Lean-Proofs Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import ErdosProblems.Erdos722.Typicality
import Mathlib

/-!
# The reserve construction for Erdős 722

This file turns simultaneous common-neighbourhood typicality into the two
deterministic properties of the sparse reserve.  The first layer below is a
finite bipartite double count and the level-by-level extension tree.
-/

namespace Erdos722.Reserve

open Finset
open Erdos722.Typicality

/-- A finite bipartite relation with left degree at least `a` and right
degree at most `b` satisfies the corresponding edge-count inequality. -/
theorem card_mul_le_card_mul_of_relation
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (left : Finset α) (right : Finset β) (rel : α → β → Prop)
    [DecidableRel rel] (a b : ℕ)
    (hleft : ∀ x ∈ left, a ≤ (right.filter (rel x)).card)
    (hright : ∀ y ∈ right, (left.filter fun x ↦ rel x y).card ≤ b) :
    left.card * a ≤ right.card * b := by
  calc
    left.card * a = ∑ _x ∈ left, a := by simp
    _ ≤ ∑ x ∈ left, (right.filter (rel x)).card := by
      apply Finset.sum_le_sum
      exact hleft
    _ = ∑ y ∈ right, (left.filter fun x ↦ rel x y).card := by
      simp only [Finset.card_filter]
      rw [Finset.sum_comm]
    _ ≤ ∑ _y ∈ right, b := by
      apply Finset.sum_le_sum
      exact hright
    _ = right.card * b := by simp

/-- `r`-edges supported on a finite vertex set. -/
def cliqueEdges (S : Finset (Fin n)) (r : ℕ) : Finset (Finset (Fin n)) :=
  S.powersetCard r

def localDegree (host : Finset (Finset (Fin n))) (I : Finset (Fin n)) : ℕ :=
  (host.filter fun A ↦ I ⊆ A).card

/-- A one-face common neighbourhood counts exactly the sampled edges
through that face. -/
lemma localDegree_sampledEdges_eq_commonNeighbors
    {n r : ℕ} (hr : 0 < r) (I : Finset (Fin n)) (hI : I.card = r - 1)
    (ω : {a // a ∈ uniformEdges n r} → Bool) :
    localDegree (sampledEdges n r ω) I =
      (commonNeighbors n r {I} hr (by simpa using hI) ω).card := by
  classical
  symm
  let source := commonNeighbors n r {I} hr (by simpa using hI) ω
  let target := (sampledEdges n r ω).filter fun A ↦ I ⊆ A
  change source.card = target.card
  apply Finset.card_bij (s := source) (t := target)
      (fun x _hx ↦ insert (x : Fin n) I)
  · intro x hx
    have hxgood := (Finset.mem_filter.mp hx).2
    have hxI : (x : Fin n) ∉ I := by
      have hc := x.property
      simpa [cleanVertices] using hc
    have hcard : (insert (x : Fin n) I).card = r := by
      rw [Finset.card_insert_of_notMem hxI, hI]
      omega
    apply Finset.mem_filter.mpr
    constructor
    · apply mem_sampledEdges.mpr
      let he : insert (x : Fin n) I ∈ uniformEdges n r :=
        mem_uniformEdges.mpr hcard
      refine ⟨he, ?_⟩
      have hroot : ⟨I, Finset.mem_singleton_self I⟩ =
          (⟨I, Finset.mem_singleton_self I⟩ : {f // f ∈ ({I} : Finset (Finset (Fin n)))}) := rfl
      have hω := hxgood ⟨I, Finset.mem_singleton_self I⟩
      simpa [commonEdgeCoord] using hω
    · exact Finset.subset_insert _ _
  · intro x hx y hy hxy
    apply Subtype.ext
    have hxI : (x : Fin n) ∉ I := by simpa [cleanVertices] using x.property
    have hxmem : (x : Fin n) ∈ insert (y : Fin n) I := by
      change insert (x : Fin n) I = insert (y : Fin n) I at hxy
      rw [← hxy]
      exact Finset.mem_insert_self _ _
    rcases Finset.mem_insert.mp hxmem with h | h
    · exact h
    · exact (hxI h).elim
  · intro A hA
    have hAtarget := Finset.mem_filter.mp hA
    have hAuniform : A.card = r :=
      mem_uniformEdges.mp (sampledEdges_subset ω hAtarget.1)
    have hdiffcard : (A \ I).card = 1 := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hAtarget.2,
        hAuniform, hI]
      omega
    obtain ⟨x, hdiff⟩ := Finset.card_eq_one.mp hdiffcard
    have hxA : x ∈ A := by
      have : x ∈ A \ I := by simp [hdiff]
      exact (Finset.mem_sdiff.mp this).1
    have hxI : x ∉ I := by
      have : x ∈ A \ I := by simp [hdiff]
      exact (Finset.mem_sdiff.mp this).2
    have hAI : A = insert x I := by
      apply Finset.Subset.antisymm
      · intro y hy
        by_cases hyI : y ∈ I
        · exact Finset.mem_insert_of_mem hyI
        · have hyDiff : y ∈ A \ I := Finset.mem_sdiff.mpr ⟨hy, hyI⟩
          have : y = x := by simpa [hdiff] using hyDiff
          simpa [this]
      · exact Finset.insert_subset hxA hAtarget.2
    let xclean : cleanVertices n ({I} : Finset (Finset (Fin n))) :=
      ⟨x, by simpa [cleanVertices] using hxI⟩
    refine ⟨xclean, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      intro f
      have hf : (f : Finset (Fin n)) = I := Finset.mem_singleton.mp f.property
      obtain ⟨hAu, hsample⟩ := mem_sampledEdges.mp hAtarget.1
      have hcoord : commonEdgeCoord n r {I} hr (by simpa using hI)
          ⟨xclean, f⟩ = ⟨A, hAu⟩ := by
        apply Subtype.ext
        change insert x (f : Finset (Fin n)) = A
        rw [hf, ← hAI]
      simpa [hcoord] using hsample
    · exact hAI.symm

/-- The upper typicality estimate for one root face is the maximum
`(r-1)`-degree estimate for the sampled reserve. -/
theorem typical_localDegree_upper
    {n q r : ℕ} (hr : 0 < r) (hrq : r ≤ q)
    (p : Set.Icc (0 : ℝ) 1)
    (ω : {a // a ∈ uniformEdges n r} → Bool)
    (htyp : ∀ roots, ∀ hroots :
      roots ∈ rootFamilies n r (Nat.choose q r),
      commonMean n roots p / 2 <
        Probability.finiteRandomSum
          (fun x ↦ commonNeighborIndicator n r roots hr
            (root_card_of_mem_rootFamilies hroots) x) ω ∧
      Probability.finiteRandomSum
          (fun x ↦ commonNeighborIndicator n r roots hr
            (root_card_of_mem_rootFamilies hroots) x) ω <
        2 * commonMean n roots p) :
    ∀ I, I.card = r - 1 →
      (localDegree (sampledEdges n r ω) I : ℝ) < 2 * n * (p : ℝ) := by
  intro I hI
  have hroots : ({I} : Finset (Finset (Fin n))) ∈
      rootFamilies n r (Nat.choose q r) := by
    rw [mem_rootFamilies]
    constructor
    · intro f hf
      have : f = I := Finset.mem_singleton.mp hf
      subst f
      exact mem_uniformEdges.mpr hI
    · simp only [Finset.card_singleton]
      have hc := Nat.choose_pos hrq
      omega
  have hupp := (htyp {I} hroots).2
  rw [← card_commonNeighbors n r {I} hr
    (root_card_of_mem_rootFamilies hroots) ω] at hupp
  rw [localDegree_sampledEdges_eq_commonNeighbors hr I hI ω]
  calc
    ((commonNeighbors n r {I} hr
        (root_card_of_mem_rootFamilies hroots) ω).card : ℝ) <
        2 * commonMean n {I} p := hupp
    _ ≤ 2 * n * (p : ℝ) := by
      unfold commonMean
      simp only [Finset.card_singleton, pow_one]
      have hc : ((cleanVertices n {I}).card : ℝ) ≤ n := by
        have hcNat : (cleanVertices n {I}).card ≤ n := by
          simpa using Finset.card_le_univ (cleanVertices n {I})
        exact_mod_cast hcNat
      nlinarith [p.property.1]

/-- Reserve density `n^{-1/D}`, written as a real `D`th root of `1/n`. -/
noncomputable def reserveProbability (n D : ℕ) : ℝ :=
  ((n : ℝ)⁻¹) ^ ((D : ℝ)⁻¹)

lemma reserveProbability_pos (hn : 0 < n) (D : ℕ) :
    0 < reserveProbability n D := by
  unfold reserveProbability
  exact Real.rpow_pos_of_pos (inv_pos.mpr (by exact_mod_cast hn)) _

lemma reserveProbability_le_one (hn : 0 < n) (D : ℕ) :
    reserveProbability n D ≤ 1 := by
  unfold reserveProbability
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnOne : (1 : ℝ) ≤ n := by
    exact_mod_cast (show 1 ≤ n from hn)
  calc
    ((n : ℝ)⁻¹) ^ ((D : ℝ)⁻¹) ≤
        (1 : ℝ) ^ ((D : ℝ)⁻¹) := by
      apply Real.rpow_le_rpow (inv_nonneg.mpr (by positivity))
      · exact (inv_le_one₀ hnR).2 hnOne
      · positivity
    _ = 1 := Real.one_rpow _

noncomputable def reserveProbabilityIcc (n D : ℕ) (hn : 0 < n) :
    Set.Icc (0 : ℝ) 1 :=
  ⟨reserveProbability n D,
    (reserveProbability_pos hn D).le, reserveProbability_le_one hn D⟩

lemma reserveProbability_pow (hn : 0 < n) (hD : 0 < D) :
    (reserveProbability n D) ^ D = ((n : ℝ)⁻¹) := by
  unfold reserveProbability
  exact Real.rpow_inv_natCast_pow (inv_nonneg.mpr (by positivity)) hD.ne'

lemma reserveProbability_pow_nat (hn : 0 < n) (hD : 0 < D) (s : ℕ) :
    (reserveProbability n D) ^ s =
      (n : ℝ) ^ (-((s : ℝ) / (D : ℝ))) := by
  have hbase : 0 ≤ ((n : ℝ)⁻¹) := inv_nonneg.mpr (by positivity)
  unfold reserveProbability
  rw [← Real.rpow_natCast, ← Real.rpow_mul hbase,
    Real.rpow_neg_eq_inv_rpow]
  congr 1
  field_simp

/-- At density `n^{-1/D}`, the upper typicality estimate is exactly the
power-cleared local-degree bound used by the reserve lemma. -/
theorem typical_localDegree_power_bound
    {n q r D : ℕ} (hn : 0 < n) (hD : 0 < D)
    (hr : 0 < r) (hrq : r ≤ q)
    (ω : {a // a ∈ uniformEdges n r} → Bool)
    (htyp : ∀ roots, ∀ hroots :
      roots ∈ rootFamilies n r (Nat.choose q r),
      commonMean n roots (reserveProbabilityIcc n D hn) / 2 <
        Probability.finiteRandomSum
          (fun x ↦ commonNeighborIndicator n r roots hr
            (root_card_of_mem_rootFamilies hroots) x) ω ∧
      Probability.finiteRandomSum
          (fun x ↦ commonNeighborIndicator n r roots hr
            (root_card_of_mem_rootFamilies hroots) x) ω <
        2 * commonMean n roots (reserveProbabilityIcc n D hn)) :
    ∀ I, I.card = r - 1 →
      (localDegree (sampledEdges n r ω) I) ^ D ≤
        2 ^ D * n ^ (D - 1) := by
  intro I hI
  have hdeg := typical_localDegree_upper hr hrq
    (reserveProbabilityIcc n D hn) ω htyp I hI
  have hpow : ((localDegree (sampledEdges n r ω) I : ℕ) : ℝ) ^ D ≤
      (2 * n * reserveProbability n D) ^ D := by
    exact pow_le_pow_left₀ (by positivity) hdeg.le D
  have hnreal : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hident : (2 * (n : ℝ) * reserveProbability n D) ^ D =
      ((2 ^ D * n ^ (D - 1) : ℕ) : ℝ) := by
    have hnPow : (n : ℝ) ^ D * (n : ℝ)⁻¹ = (n : ℝ) ^ (D - 1) := by
      have hDs : D = (D - 1) + 1 := by omega
      nth_rw 1 [hDs]
      rw [pow_succ]
      field_simp
    rw [mul_pow, mul_pow, reserveProbability_pow hn hD]
    push_cast
    rw [mul_assoc, hnPow]
  rw [hident] at hpow
  exact_mod_cast hpow

/-- Valid partial extensions of a root edge by `i` new vertices. -/
def extensionLevel (n q r : ℕ) (reserve : Finset (Finset (Fin n)))
    (e : Finset (Fin n)) (i : ℕ) : Finset (Finset (Fin n)) :=
  (uniformEdges n (r + i)).filter fun S ↦
    e ⊆ S ∧ cliqueEdges S r \ {e} ⊆ reserve

/-- The `(r-1)`-faces which a new vertex must complete at partial set `S`. -/
def extensionRoots (S : Finset (Fin n)) (r : ℕ) :
    Finset (Finset (Fin n)) :=
  S.powersetCard (r - 1)

lemma mem_extensionRoots {f S : Finset (Fin n)} :
    f ∈ extensionRoots S r ↔ f ⊆ S ∧ f.card = r - 1 := by
  simp [extensionRoots, Finset.mem_powersetCard]

lemma card_extensionRoots (S : Finset (Fin n)) :
    (extensionRoots S r).card = Nat.choose S.card (r - 1) := by
  simp [extensionRoots]

lemma cleanVertices_eq_sdiff_biUnion
    (roots : Finset (Finset (Fin n))) :
    cleanVertices n roots =
      (Finset.univ : Finset (Fin n)) \ roots.biUnion id := by
  classical
  ext x
  simp [cleanVertices]

/-- Removing at most `h` root faces, each of size `r-1`, leaves at least
`n-h(r-1)` clean vertices. -/
lemma cleanVertices_card_lower
    {roots : Finset (Finset (Fin n))}
    (hroot : ∀ f ∈ roots, f.card = r - 1)
    (hroots : roots.card ≤ h) :
    n - h * (r - 1) ≤ (cleanVertices n roots).card := by
  classical
  have hunion : (roots.biUnion id).card ≤ roots.card * (r - 1) := by
    calc
      (roots.biUnion id).card ≤ ∑ f ∈ roots, f.card :=
        Finset.card_biUnion_le
      _ = roots.card * (r - 1) := by
        apply Finset.sum_const_nat hroot
  have hunion' : (roots.biUnion id).card ≤ h * (r - 1) :=
    hunion.trans (Nat.mul_le_mul_right (r - 1) hroots)
  rw [cleanVertices_eq_sdiff_biUnion,
    Finset.card_sdiff_of_subset (Finset.subset_univ _)]
  simpa using Nat.sub_le_sub_left hunion' n

/-- There are only polynomially many root families when the permitted
family size is fixed. -/
lemma card_rootFamilies_le (n r h : ℕ) :
    (rootFamilies n r h).card ≤
      (h + 1) * ((uniformEdges n (r - 1)).card + 1) ^ h := by
  classical
  let U := uniformEdges n (r - 1)
  have hsub : rootFamilies n r h ⊆
      (Finset.range (h + 1)).biUnion fun i ↦ U.powersetCard i := by
    intro roots hroots
    have hm := mem_rootFamilies.mp hroots
    apply Finset.mem_biUnion.mpr
    refine ⟨roots.card, Finset.mem_range.mpr (by omega), ?_⟩
    exact Finset.mem_powersetCard.mpr ⟨hm.1, rfl⟩
  calc
    (rootFamilies n r h).card ≤
        ((Finset.range (h + 1)).biUnion fun i ↦ U.powersetCard i).card :=
      Finset.card_le_card hsub
    _ ≤ ∑ i ∈ Finset.range (h + 1), (U.powersetCard i).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ Finset.range (h + 1), (U.card + 1) ^ h := by
      apply Finset.sum_le_sum
      intro i hi
      rw [Finset.card_powersetCard]
      have hih : i ≤ h := by simpa using Finset.mem_range.mp hi
      calc
        Nat.choose U.card i ≤ U.card ^ i := Nat.choose_le_pow _ _
        _ ≤ (U.card + 1) ^ i := Nat.pow_le_pow_left (Nat.le_succ _) _
        _ ≤ (U.card + 1) ^ h :=
          Nat.pow_le_pow_right (by omega) hih
    _ = (h + 1) * (U.card + 1) ^ h := by simp

lemma commonMean_lower_of_mem_rootFamilies
    {n r h : ℕ} (p : Set.Icc (0 : ℝ) 1)
    {roots : Finset (Finset (Fin n))}
    (hroots : roots ∈ rootFamilies n r h) :
    ((n - h * (r - 1) : ℕ) : ℝ) * (p : ℝ) ^ h ≤
      commonMean n roots p := by
  have hroot := root_card_of_mem_rootFamilies hroots
  have hcleanNat := cleanVertices_card_lower hroot (mem_rootFamilies.mp hroots).2
  have hclean : ((n - h * (r - 1) : ℕ) : ℝ) ≤
      (cleanVertices n roots).card := by exact_mod_cast hcleanNat
  have hpow : (p : ℝ) ^ h ≤ (p : ℝ) ^ roots.card :=
    pow_le_pow_of_le_one p.property.1 p.property.2 (mem_rootFamilies.mp hroots).2
  unfold commonMean
  exact mul_le_mul hclean hpow (pow_nonneg p.property.1 _) (by positivity)

/-- A single explicit scalar inequality discharges the simultaneous finite
union bound. -/
theorem tail_sum_lt_one_of_scalar_bound
    (n r h : ℕ) (p : Set.Icc (0 : ℝ) 1)
    (hscalar :
      ((rootFamilies n r h).card : ℝ) * 2 *
          Real.exp (-(((n - h * (r - 1) : ℕ) : ℝ) *
            (p : ℝ) ^ h) / 10) < 1) :
    ∑ roots ∈ rootFamilies n r h,
      (Real.exp (-(commonMean n roots p) / 10) +
        Real.exp (-(commonMean n roots p) / 5)) < 1 := by
  let M : ℝ := ((n - h * (r - 1) : ℕ) : ℝ) * (p : ℝ) ^ h
  have hM : 0 ≤ M := mul_nonneg (by positivity) (pow_nonneg p.property.1 _)
  calc
    (∑ roots ∈ rootFamilies n r h,
        (Real.exp (-(commonMean n roots p) / 10) +
          Real.exp (-(commonMean n roots p) / 5))) ≤
        ∑ _roots ∈ rootFamilies n r h,
          (2 * Real.exp (-M / 10)) := by
      apply Finset.sum_le_sum
      intro roots hroots
      have hm := commonMean_lower_of_mem_rootFamilies p hroots
      have hfirst : Real.exp (-(commonMean n roots p) / 10) ≤
          Real.exp (-M / 10) := by
        apply Real.exp_le_exp.mpr
        linarith
      have hsecond : Real.exp (-(commonMean n roots p) / 5) ≤
          Real.exp (-M / 10) := by
        apply Real.exp_le_exp.mpr
        linarith
      linarith
    _ = ((rootFamilies n r h).card : ℝ) * 2 *
        Real.exp (-M / 10) := by simp; ring
    _ < 1 := by simpa [M] using hscalar

/-- Exponential decay in a positive real power dominates every fixed
polynomial. -/
lemma tendsto_pow_mul_exp_neg_rpow_atTop
    (P : ℕ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Filter.Tendsto
      (fun x : ℝ ↦ x ^ P * Real.exp (-b * x ^ a)) Filter.atTop (nhds 0) := by
  have hbase := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
    ((P : ℝ) / a) b hb
  have hcomp := hbase.comp (tendsto_rpow_atTop ha)
  apply Filter.Tendsto.congr' _ hcomp
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
  have hxa : 0 ≤ x := hx.le
  have ha0 : a ≠ 0 := ha.ne'
  change (x ^ a) ^ ((P : ℝ) / a) * Real.exp (-b * x ^ a) =
    x ^ P * Real.exp (-b * x ^ a)
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul hxa]
  congr 3
  field_simp

/-- For fixed design parameters, the scalar union-bound estimate holds for
all sufficiently large ground-set sizes. -/
theorem eventually_reserve_scalar_bound
    (q r : ℕ) (hr : 0 < r) (hrq : r ≤ q) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ((rootFamilies n r (Nat.choose q r)).card : ℝ) * 2 *
          Real.exp (-(((n - Nat.choose q r * (r - 1) : ℕ) : ℝ) *
            reserveProbability n ((6 * Nat.choose q r) ^ 2) ^ Nat.choose q r) / 10) < 1 := by
  let K := Nat.choose q r
  let D := (6 * K) ^ 2
  let P := r * K
  let a : ℝ := 1 - (K : ℝ) / (D : ℝ)
  let C₀ : ℝ := 2 * (K + 1) * 2 ^ K
  have hK : 0 < K := Nat.choose_pos hrq
  have hD : 0 < D := by
    dsimp [D]
    positivity
  have hKD : K < D := by
    dsimp [D]
    nlinarith
  have ha : 0 < a := by
    dsimp [a]
    have hDr : (0 : ℝ) < D := by exact_mod_cast hD
    have hKDr : (K : ℝ) < D := by exact_mod_cast hKD
    apply sub_pos.mpr
    exact (div_lt_one hDr).mpr hKDr
  have hdecay := tendsto_pow_mul_exp_neg_rpow_atTop P ha (by norm_num : (0 : ℝ) < 1 / 20)
  have hconst : Filter.Tendsto
      (fun x : ℝ ↦ C₀ * (x ^ P * Real.exp (-(1 / 20 : ℝ) * x ^ a)))
      Filter.atTop (nhds 0) := by
    have hC₀ : Filter.Tendsto (fun _ : ℝ ↦ C₀)
        Filter.atTop (nhds C₀) := tendsto_const_nhds
    simpa only [mul_zero] using hC₀.mul hdecay
  have hnat := hconst.comp tendsto_natCast_atTop_atTop
  have hsmall : ∀ᶠ n : ℕ in Filter.atTop,
      C₀ * (((n : ℝ) ^ P) *
        Real.exp (-(1 / 20 : ℝ) * (n : ℝ) ^ a)) < 1 :=
    (tendsto_order.1 hnat).2 _ (by norm_num)
  filter_upwards [hsmall,
    Filter.eventually_ge_atTop (max 1 (2 * (K * (r - 1))))] with n hnsmall hnlarge
  have hn : 0 < n := lt_of_lt_of_le (by omega : 0 < 1) (le_trans (le_max_left _ _) hnlarge)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnOne : 1 ≤ n := hn
  have hface : (uniformEdges n (r - 1)).card ≤ n ^ r := by
    rw [show (uniformEdges n (r - 1)).card = Nat.choose n (r - 1) by
      simp [uniformEdges]]
    calc
      Nat.choose n (r - 1) ≤ n ^ (r - 1) := Nat.choose_le_pow _ _
      _ ≤ n ^ r := Nat.pow_le_pow_right hn (by omega)
  have hrootNat : (rootFamilies n r K).card ≤
      (K + 1) * (2 ^ K * n ^ P) := by
    calc
      (rootFamilies n r K).card ≤
          (K + 1) * ((uniformEdges n (r - 1)).card + 1) ^ K :=
        card_rootFamilies_le n r K
      _ ≤ (K + 1) * (2 * n ^ r) ^ K := by
        apply Nat.mul_le_mul_left
        apply Nat.pow_le_pow_left
        have hone : 1 ≤ n ^ r := one_le_pow₀ hnOne
        omega
      _ = (K + 1) * (2 ^ K * n ^ P) := by
        rw [mul_pow, ← pow_mul]
  have hroot : ((rootFamilies n r K).card : ℝ) * 2 ≤
      C₀ * (n : ℝ) ^ P := by
    have hrootCast : ((rootFamilies n r K).card : ℝ) ≤
        (((K + 1) * (2 ^ K * n ^ P) : ℕ) : ℝ) := by
      exact_mod_cast hrootNat
    calc
      ((rootFamilies n r K).card : ℝ) * 2 ≤
          (((K + 1) * (2 ^ K * n ^ P) : ℕ) : ℝ) * 2 :=
        mul_le_mul_of_nonneg_right hrootCast (by norm_num)
      _ = C₀ * (n : ℝ) ^ P := by
        push_cast
        dsimp [C₀]
        ring
  have hbaseNat : 2 * (K * (r - 1)) ≤ n :=
    (le_max_right 1 (2 * (K * (r - 1)))).trans hnlarge
  have hbase : (n : ℝ) / 2 ≤
      ((n - K * (r - 1) : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : K * (r - 1) ≤ n)]
    have hbaseCast : (2 : ℝ) * ((K * (r - 1) : ℕ) : ℝ) ≤ n := by
      exact_mod_cast hbaseNat
    linarith
  have hpK : reserveProbability n D ^ K =
      (n : ℝ) ^ (-((K : ℝ) / (D : ℝ))) :=
    reserveProbability_pow_nat hn hD K
  have hrpow : (n : ℝ) *
      (n : ℝ) ^ (-((K : ℝ) / (D : ℝ))) = (n : ℝ) ^ a := by
    calc
      (n : ℝ) * (n : ℝ) ^ (-((K : ℝ) / (D : ℝ))) =
          (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (-((K : ℝ) / (D : ℝ))) := by
        rw [Real.rpow_one]
      _ = (n : ℝ) ^ ((1 : ℝ) + -((K : ℝ) / (D : ℝ))) :=
        (Real.rpow_add hnR _ _).symm
      _ = (n : ℝ) ^ a := by
        congr 1
  have hmean : (1 / 2 : ℝ) * (n : ℝ) ^ a ≤
      ((n - K * (r - 1) : ℕ) : ℝ) * reserveProbability n D ^ K := by
    rw [hpK]
    calc
      (1 / 2 : ℝ) * (n : ℝ) ^ a =
          ((n : ℝ) / 2) * (n : ℝ) ^ (-((K : ℝ) / (D : ℝ))) := by
        rw [← hrpow]
        ring
      _ ≤ ((n - K * (r - 1) : ℕ) : ℝ) *
          (n : ℝ) ^ (-((K : ℝ) / (D : ℝ))) := by
        apply mul_le_mul_of_nonneg_right hbase
        exact Real.rpow_nonneg (le_of_lt hnR) _
  have hexp : Real.exp (-(((n - K * (r - 1) : ℕ) : ℝ) *
        reserveProbability n D ^ K) / 10) ≤
      Real.exp (-(1 / 20 : ℝ) * (n : ℝ) ^ a) := by
    apply Real.exp_le_exp.mpr
    linarith
  calc
    ((rootFamilies n r K).card : ℝ) * 2 *
        Real.exp (-(((n - K * (r - 1) : ℕ) : ℝ) *
          reserveProbability n D ^ K) / 10) ≤
        (C₀ * (n : ℝ) ^ P) *
          Real.exp (-(1 / 20 : ℝ) * (n : ℝ) ^ a) :=
      mul_le_mul hroot hexp (Real.exp_nonneg _) (by positivity)
    _ = C₀ * ((n : ℝ) ^ P *
        Real.exp (-(1 / 20 : ℝ) * (n : ℝ) ^ a)) := by ring
    _ < 1 := hnsmall

/-- Once the scalar estimate holds, a single deterministic sample has all
common-neighbourhood estimates and the required power-cleared maximum
`(r-1)`-degree bound. -/
theorem exists_typical_sampled_reserve
    {n q r : ℕ} (hn : 0 < n) (hr : 0 < r) (hrq : r ≤ q)
    (hscalar :
      ((rootFamilies n r (Nat.choose q r)).card : ℝ) * 2 *
          Real.exp (-(((n - Nat.choose q r * (r - 1) : ℕ) : ℝ) *
            reserveProbability n ((6 * Nat.choose q r) ^ 2) ^ Nat.choose q r) / 10) < 1) :
    ∃ ω : {e // e ∈ uniformEdges n r} → Bool,
      (∀ roots, ∀ hroots : roots ∈ rootFamilies n r (Nat.choose q r),
        commonMean n roots
              (reserveProbabilityIcc n ((6 * Nat.choose q r) ^ 2) hn) / 2 <
            Probability.finiteRandomSum
              (fun x ↦ commonNeighborIndicator n r roots hr
                (root_card_of_mem_rootFamilies hroots) x) ω ∧
        Probability.finiteRandomSum
              (fun x ↦ commonNeighborIndicator n r roots hr
                (root_card_of_mem_rootFamilies hroots) x) ω <
            2 * commonMean n roots
              (reserveProbabilityIcc n ((6 * Nat.choose q r) ^ 2) hn)) ∧
      sampledEdges n r ω ⊆ uniformEdges n r ∧
      (∀ I, I.card = r - 1 →
        (localDegree (sampledEdges n r ω) I) ^ ((6 * Nat.choose q r) ^ 2) ≤
          2 ^ ((6 * Nat.choose q r) ^ 2) *
            n ^ (((6 * Nat.choose q r) ^ 2) - 1)) := by
  let D := (6 * Nat.choose q r) ^ 2
  have hD : 0 < D := by
    have hK : 0 < Nat.choose q r := Nat.choose_pos hrq
    dsimp [D]
    positivity
  let p := reserveProbabilityIcc n D hn
  have htail :
      ∑ roots ∈ rootFamilies n r (Nat.choose q r),
        (Real.exp (-(commonMean n roots p) / 10) +
          Real.exp (-(commonMean n roots p) / 5)) < 1 := by
    apply tail_sum_lt_one_of_scalar_bound
    simpa [p, D, reserveProbabilityIcc] using hscalar
  obtain ⟨ω, htyp⟩ := exists_simultaneously_typical
    n r (Nat.choose q r) hr p htail
  refine ⟨ω, ?_, sampledEdges_subset ω, ?_⟩
  · simpa [p, D] using htyp
  · exact typical_localDegree_power_bound hn hD hr hrq ω (by
      simpa [p, D] using htyp)

/-- The common-neighbour root counts along a `q`-vertex extension tree
telescope to `choose q r - 1`. -/
lemma sum_extension_root_counts (r m : ℕ) (hr : 0 < r) :
    ∑ i ∈ Finset.range m, Nat.choose (r + i) (r - 1) =
      Nat.choose (r + m) r - 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      have hpascal : Nat.choose (r + m + 1) r =
          Nat.choose (r + m) (r - 1) + Nat.choose (r + m) r := by
        have h := Nat.choose_succ_succ' (r + m) (r - 1)
        simpa [show r - 1 + 1 = r by omega, Nat.add_assoc,
          Nat.add_comm, Nat.add_left_comm] using h
      rw [show r + (m + 1) = r + m + 1 by omega, hpascal]
      have hchoose : 0 < Nat.choose (r + m) r :=
        Nat.choose_pos (by omega)
      omega

/-- The real lower bound from which the integer branching factor at level
`i` is obtained. -/
noncomputable def reserveBranchingReal (n q r i : ℕ) : ℝ :=
  ((n - Nat.choose q r * (r - 1) : ℕ) : ℝ) *
      reserveProbability n ((6 * Nat.choose q r) ^ 2) ^
        Nat.choose (r + i) (r - 1) / 2

/-- Integer branching factor used in the extension-tree double count. -/
noncomputable def reserveBranching (n q r i : ℕ) : ℕ :=
  ⌊reserveBranchingReal n q r i⌋₊

lemma reserveBranching_cast_le (n q r i : ℕ) :
    (reserveBranching n q r i : ℝ) ≤ reserveBranchingReal n q r i := by
  apply Nat.floor_le
  unfold reserveBranchingReal reserveProbability
  positivity

/-- Above two, taking the natural floor loses at most a factor two. -/
lemma half_le_natFloor {x : ℝ} (hx : 2 ≤ x) :
    x / 2 ≤ (Nat.floor x : ℝ) := by
  have hlt := Nat.lt_floor_add_one x
  have hone : (1 : ℝ) ≤ x / 2 := by linarith
  exact le_of_lt (by linarith)

lemma extension_root_count_le
    {q r i : ℕ} (hr : 0 < r) (hi : i < q - r) :
    Nat.choose (r + i) (r - 1) ≤ Nat.choose q r := by
  have hri : r + i ≤ q - 1 := by omega
  calc
    Nat.choose (r + i) (r - 1) ≤
        Nat.choose (q - 1) (r - 1) := Nat.choose_le_choose _ hri
    _ ≤ Nat.choose q r := by
      have hpascal : Nat.choose q r =
          Nat.choose (q - 1) (r - 1) + Nat.choose (q - 1) r := by
        calc
          Nat.choose q r =
              Nat.choose (Nat.succ (q - 1)) (Nat.succ (r - 1)) := by
            congr <;> omega
          _ = _ := by
            have h := Nat.choose_succ_succ' (q - 1) (r - 1)
            simpa [show r - 1 + 1 = r by omega] using h
      rw [hpascal]
      omega

/-- For fixed `q,r`, every integer branching factor is eventually taken
from a real quantity at least two, uniformly over the finitely many
extension levels. -/
theorem eventually_two_le_reserveBranchingReal
    (q r : ℕ) (hr : 0 < r) (hrq : r < q) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ i < q - r,
      2 ≤ reserveBranchingReal n q r i := by
  let K := Nat.choose q r
  let D := (6 * K) ^ 2
  let a : ℝ := 1 - (K : ℝ) / (D : ℝ)
  have hK : 0 < K := Nat.choose_pos hrq.le
  have hD : 0 < D := by
    dsimp [D]
    positivity
  have hKD : K < D := by
    dsimp [D]
    nlinarith
  have ha : 0 < a := by
    dsimp [a]
    have hDr : (0 : ℝ) < D := by exact_mod_cast hD
    have hKDr : (K : ℝ) < D := by exact_mod_cast hKD
    exact sub_pos.mpr ((div_lt_one hDr).mpr hKDr)
  have hgrow : Filter.Tendsto (fun x : ℝ ↦ x ^ a)
      Filter.atTop Filter.atTop := tendsto_rpow_atTop ha
  have hnat := hgrow.comp tendsto_natCast_atTop_atTop
  have hevent : ∀ᶠ n : ℕ in Filter.atTop, (8 : ℝ) ≤ (n : ℝ) ^ a :=
    hnat.eventually (Filter.eventually_ge_atTop 8)
  filter_upwards [hevent,
    Filter.eventually_ge_atTop (max 1 (2 * (K * (r - 1))))] with n hnGrow hnLarge
  intro i hi
  have hn : 0 < n := lt_of_lt_of_le (by omega : 0 < 1)
    ((le_max_left 1 (2 * (K * (r - 1)))).trans hnLarge)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnOneR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hbaseNat : 2 * (K * (r - 1)) ≤ n :=
    (le_max_right 1 (2 * (K * (r - 1)))).trans hnLarge
  have hbase : (n : ℝ) / 2 ≤
      ((n - K * (r - 1) : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : K * (r - 1) ≤ n)]
    have hbaseCast : (2 : ℝ) * ((K * (r - 1) : ℕ) : ℝ) ≤ n := by
      exact_mod_cast hbaseNat
    linarith
  let s := Nat.choose (r + i) (r - 1)
  have hs : s ≤ K := extension_root_count_le hr hi
  have hexponent : -((K : ℝ) / (D : ℝ)) ≤
      -((s : ℝ) / (D : ℝ)) := by
    have hsR : (s : ℝ) ≤ K := by exact_mod_cast hs
    have hDr : (0 : ℝ) < D := by exact_mod_cast hD
    exact neg_le_neg (div_le_div_of_nonneg_right hsR hDr.le)
  have hpLower : (n : ℝ) ^ (-((K : ℝ) / (D : ℝ))) ≤
      (n : ℝ) ^ (-((s : ℝ) / (D : ℝ))) :=
    Real.rpow_le_rpow_of_exponent_le hnOneR hexponent
  have hpS : reserveProbability n D ^ s =
      (n : ℝ) ^ (-((s : ℝ) / (D : ℝ))) :=
    reserveProbability_pow_nat hn hD s
  have hrpow : (n : ℝ) *
      (n : ℝ) ^ (-((K : ℝ) / (D : ℝ))) = (n : ℝ) ^ a := by
    calc
      (n : ℝ) * (n : ℝ) ^ (-((K : ℝ) / (D : ℝ))) =
          (n : ℝ) ^ (1 : ℝ) *
            (n : ℝ) ^ (-((K : ℝ) / (D : ℝ))) := by rw [Real.rpow_one]
      _ = (n : ℝ) ^ ((1 : ℝ) + -((K : ℝ) / (D : ℝ))) :=
        (Real.rpow_add hnR _ _).symm
      _ = (n : ℝ) ^ a := by congr 1
  have hmul : ((n : ℝ) / 2) *
        (n : ℝ) ^ (-((K : ℝ) / (D : ℝ))) ≤
      ((n - K * (r - 1) : ℕ) : ℝ) *
        (n : ℝ) ^ (-((s : ℝ) / (D : ℝ))) := by
    exact mul_le_mul hbase hpLower (Real.rpow_nonneg (le_of_lt hnR) _)
      (by positivity)
  have htwo : (2 : ℝ) ≤
      ((n - K * (r - 1) : ℕ) : ℝ) *
        (n : ℝ) ^ (-((s : ℝ) / (D : ℝ))) / 2 := by
    calc
      (2 : ℝ) ≤ (n : ℝ) ^ a / 4 := by linarith
      _ = (((n : ℝ) / 2) *
          (n : ℝ) ^ (-((K : ℝ) / (D : ℝ)))) / 2 := by
        rw [← hrpow]
        ring
      _ ≤ _ := div_le_div_of_nonneg_right hmul (by norm_num)
  simpa [reserveBranchingReal, K, D, s, hpS] using htwo

/-- Exact product of the real half-branching lower bounds.  The exponent
identity is the hockey-stick sum above. -/
lemma prod_half_reserveBranchingReal
    (n q r : ℕ) (hr : 0 < r) (hrq : r ≤ q) :
    ∏ i ∈ Finset.range (q - r), (reserveBranchingReal n q r i / 2) =
      (((n - Nat.choose q r * (r - 1) : ℕ) : ℝ) ^ (q - r) *
        reserveProbability n ((6 * Nat.choose q r) ^ 2) ^
          (Nat.choose q r - 1)) / (4 : ℝ) ^ (q - r) := by
  let base : ℝ := ((n - Nat.choose q r * (r - 1) : ℕ) : ℝ)
  let p : ℝ := reserveProbability n ((6 * Nat.choose q r) ^ 2)
  let m := q - r
  have hsum : ∑ i ∈ Finset.range m, Nat.choose (r + i) (r - 1) =
      Nat.choose q r - 1 := by
    have h := sum_extension_root_counts r m hr
    simpa [m, Nat.add_sub_of_le hrq] using h
  calc
    ∏ i ∈ Finset.range (q - r), (reserveBranchingReal n q r i / 2) =
        ∏ i ∈ Finset.range m,
          (base * p ^ Nat.choose (r + i) (r - 1) / 4) := by
      apply Finset.prod_congr rfl
      intro i hi
      simp only [reserveBranchingReal, base, p, m]
      ring
    _ = (base ^ m * p ^ (Nat.choose q r - 1)) / (4 : ℝ) ^ m := by
      simp_rw [div_eq_mul_inv]
      rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
      rw [Finset.prod_const, Finset.card_range]
      rw [Finset.prod_pow_eq_pow_sum, hsum]
      simp [m, div_eq_mul_inv, mul_assoc]
    _ = _ := by simp [base, p, m]

/-- After clearing the fixed predecessor multiplicity and the fractional
reserve exponent, the product of the integer branching factors has the
exact power strength required by `HasReserveProperty`. -/
theorem eventually_branching_product_power_lower
    (q r : ℕ) (hr : 0 < r) (hrq : r < q) :
    ∀ᶠ n : ℕ in Filter.atTop,
      n ^ (((6 * Nat.choose q r) ^ 2) * (q - r) - Nat.choose q r) *
          (((2 ^ q) ^ (q - r)) ^ ((6 * Nat.choose q r) ^ 2)) ≤
        (∏ i ∈ Finset.range (q - r), reserveBranching n q r i) ^
          ((6 * Nat.choose q r) ^ 2) := by
  let K := Nat.choose q r
  let D := (6 * K) ^ 2
  let m := q - r
  let C := (2 ^ q) ^ m
  let E := D * m - K
  have hK : 0 < K := Nat.choose_pos hrq.le
  have hD : 0 < D := by
    dsimp [D]
    positivity
  have hm : 0 < m := by dsimp [m]; omega
  have hKD : K < D := by
    dsimp [D]
    nlinarith
  have hED : K ≤ D * m := by nlinarith
  have htwo := eventually_two_le_reserveBranchingReal q r hr hrq
  filter_upwards [htwo,
    Filter.eventually_ge_atTop
      (max (max 1 (2 * (K * (r - 1)))) ((8 ^ m * C) ^ D))] with
      n hnTwo hnLarge
  have hn : 0 < n := lt_of_lt_of_le (by omega : 0 < 1)
    ((le_max_left 1 (2 * (K * (r - 1)))).trans
      ((le_max_left (max 1 (2 * (K * (r - 1)))) ((8 ^ m * C) ^ D)).trans hnLarge))
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hbaseNat : 2 * (K * (r - 1)) ≤ n :=
    (le_max_right 1 (2 * (K * (r - 1)))).trans
      ((le_max_left (max 1 (2 * (K * (r - 1)))) ((8 ^ m * C) ^ D)).trans hnLarge)
  have hbase : (n : ℝ) / 2 ≤
      ((n - K * (r - 1) : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : K * (r - 1) ≤ n)]
    have hbaseCast : (2 : ℝ) * ((K * (r - 1) : ℕ) : ℝ) ≤ n := by
      exact_mod_cast hbaseNat
    linarith
  have hthresholdNat : (8 ^ m * C) ^ D ≤ n :=
    (le_max_right (max 1 (2 * (K * (r - 1)))) ((8 ^ m * C) ^ D)).trans hnLarge
  have hthreshold : (((8 : ℝ) ^ m * C) ^ D) ≤ n := by
    exact_mod_cast hthresholdNat
  let p : ℝ := reserveProbability n D
  have hpD : p ^ D = (n : ℝ)⁻¹ := by
    exact reserveProbability_pow hn hD
  have hfloor :
      (∏ i ∈ Finset.range m, reserveBranchingReal n q r i / 2) ≤
        ((∏ i ∈ Finset.range m, reserveBranching n q r i : ℕ) : ℝ) := by
    push_cast
    apply Finset.prod_le_prod
    · intro i hi
      exact div_nonneg (le_trans (by norm_num)
        (hnTwo i (by simpa [m] using hi))) (by norm_num)
    · intro i hi
      exact half_le_natFloor (hnTwo i (by simpa [m] using hi))
  have hformula :
      ∏ i ∈ Finset.range m, reserveBranchingReal n q r i / 2 =
        (((n - K * (r - 1) : ℕ) : ℝ) ^ m * p ^ (K - 1)) /
          (4 : ℝ) ^ m := by
    simpa [K, D, m, p] using prod_half_reserveBranchingReal n q r hr hrq.le
  have hbasePow : ((n : ℝ) / 2) ^ m ≤
      ((n - K * (r - 1) : ℕ) : ℝ) ^ m :=
    pow_le_pow_left₀ (by positivity) hbase m
  have hrealLower :
      (((n : ℝ) / 8) ^ m * p ^ (K - 1)) ≤
        ∏ i ∈ Finset.range m, reserveBranchingReal n q r i / 2 := by
    rw [hformula]
    have hpNonneg : 0 ≤ p := by
      exact (reserveProbability_pos hn D).le
    have hpPowNonneg : 0 ≤ p ^ (K - 1) := pow_nonneg hpNonneg _
    have hmul : ((n : ℝ) / 2) ^ m * p ^ (K - 1) ≤
        ((n - K * (r - 1) : ℕ) : ℝ) ^ m * p ^ (K - 1) :=
      mul_le_mul_of_nonneg_right hbasePow hpPowNonneg
    have hdiv := div_le_div_of_nonneg_right hmul (by positivity : 0 ≤ (4 : ℝ) ^ m)
    calc
      ((n : ℝ) / 8) ^ m * p ^ (K - 1) =
          (((n : ℝ) / 2) ^ m * p ^ (K - 1)) / (4 : ℝ) ^ m := by
        rw [div_pow, div_pow]
        field_simp
        have h84 : (2 : ℝ) ^ m * (4 : ℝ) ^ m = (8 : ℝ) ^ m := by
          rw [← mul_pow]
          norm_num
        rw [← h84]
        ring
      _ ≤ _ := hdiv
  have hsmallPower :
      ((((n : ℝ) / 8) ^ m * p ^ (K - 1)) ^ D) ≤
        ((∏ i ∈ Finset.range m, reserveBranching n q r i : ℕ) : ℝ) ^ D := by
    have hpNonneg : 0 ≤ p := (reserveProbability_pos hn D).le
    have hsmallNonneg : 0 ≤ ((n : ℝ) / 8) ^ m * p ^ (K - 1) :=
      mul_nonneg (pow_nonneg (by positivity) _) (pow_nonneg hpNonneg _)
    exact pow_le_pow_left₀ hsmallNonneg (hrealLower.trans hfloor) D
  have hpowIndex : m * D = E + (K - 1) + 1 := by
    have hE : E + K = D * m := Nat.sub_add_cancel hED
    calc
      m * D = D * m := Nat.mul_comm _ _
      _ = E + K := hE.symm
      _ = E + (K - 1) + 1 := by omega
  have hsmallIdentity :
      (((n : ℝ) / 8) ^ m * p ^ (K - 1)) ^ D =
        (n : ℝ) ^ E * (n : ℝ) / (((8 : ℝ) ^ m) ^ D) := by
    have hpComm : (p ^ (K - 1)) ^ D = (p ^ D) ^ (K - 1) := by
      rw [← pow_mul, ← pow_mul]
      congr 1
      exact Nat.mul_comm _ _
    calc
      (((n : ℝ) / 8) ^ m * p ^ (K - 1)) ^ D =
          ((n : ℝ) / 8) ^ (m * D) * (p ^ D) ^ (K - 1) := by
        rw [mul_pow, hpComm, pow_mul]
      _ = ((n : ℝ) ^ (m * D) / (8 : ℝ) ^ (m * D)) *
          (((n : ℝ) ^ (K - 1))⁻¹) := by
        rw [hpD, inv_pow, div_pow]
      _ = (n : ℝ) ^ E * (n : ℝ) / (((8 : ℝ) ^ m) ^ D) := by
        rw [← pow_mul]
        rw [hpowIndex, pow_add, pow_succ]
        field_simp
        ring
  have hC : (C : ℝ) ^ D ≤
      (n : ℝ) / (((8 : ℝ) ^ m) ^ D) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < ((8 : ℝ) ^ m) ^ D)).2
    rw [← mul_pow]
    simpa [mul_assoc, mul_left_comm, mul_comm] using hthreshold
  have htargetSmall :
      (n : ℝ) ^ E * (C : ℝ) ^ D ≤
        (((n : ℝ) / 8) ^ m * p ^ (K - 1)) ^ D := by
    rw [hsmallIdentity]
    calc
      (n : ℝ) ^ E * (C : ℝ) ^ D ≤
          (n : ℝ) ^ E *
            ((n : ℝ) / (((8 : ℝ) ^ m) ^ D)) :=
        mul_le_mul_of_nonneg_left hC (by positivity)
      _ = (n : ℝ) ^ E * (n : ℝ) /
          (((8 : ℝ) ^ m) ^ D) := by ring
  have htargetReal :
      ((n ^ E * C ^ D : ℕ) : ℝ) ≤
        (((∏ i ∈ Finset.range m, reserveBranching n q r i) ^ D : ℕ) : ℝ) := by
    norm_num only [Nat.cast_mul, Nat.cast_pow]
    exact htargetSmall.trans hsmallPower
  have htargetNat : n ^ E * C ^ D ≤
      (∏ i ∈ Finset.range m, reserveBranching n q r i) ^ D := by
    exact_mod_cast htargetReal
  simpa [K, D, m, C, E] using htargetNat

/-- For `r ≥ 2` and a set of size at least `r`, avoiding every
`(r-1)`-face of `S` is exactly avoiding `S`. -/
lemma mem_cleanVertices_extensionRoots
    (hr : 1 < r) (hcard : r ≤ S.card) (x : Fin n) :
    x ∈ cleanVertices n (extensionRoots S r) ↔ x ∉ S := by
  constructor
  · intro hx hxS
    have herase : (S.erase x).card = S.card - 1 := by
      rw [Finset.card_erase_of_mem hxS]
    have hsmall : r - 2 ≤ (S.erase x).card := by omega
    obtain ⟨t, ht⟩ := Finset.powersetCard_nonempty.mpr hsmall
    have htsub : t ⊆ S.erase x := (Finset.mem_powersetCard.mp ht).1
    have htcard : t.card = r - 2 := (Finset.mem_powersetCard.mp ht).2
    let f := insert x t
    have hxt : x ∉ t := fun h ↦ Finset.notMem_erase x S (htsub h)
    have hfsub : f ⊆ S := by
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact hxS
      · exact Finset.erase_subset x S (htsub hy)
    have hfcard : f.card = r - 1 := by
      change (insert x t).card = r - 1
      rw [Finset.card_insert_of_notMem hxt, htcard]
      omega
    exact (mem_cleanVertices.mp hx f
      (mem_extensionRoots.mpr ⟨hfsub, hfcard⟩)) (Finset.mem_insert_self x t)
  · intro hx
    apply mem_cleanVertices.mpr
    intro f hf hxf
    exact hx ((mem_extensionRoots.mp hf).1 hxf)

lemma extensionRoots_mem_rootFamilies
    {S : Finset (Fin n)} (hSq : S.card < q) :
    extensionRoots S r ∈ rootFamilies n r (Nat.choose q r) := by
  rw [mem_rootFamilies]
  constructor
  · intro f hf
    exact mem_uniformEdges.mpr (mem_extensionRoots.mp hf).2
  · rw [card_extensionRoots]
    calc
      Nat.choose S.card (r - 1) ≤ Nat.choose (q - 1) (r - 1) := by
        exact Nat.choose_le_choose _ (by omega)
      _ ≤ Nat.choose q r := by
        by_cases hr0 : r = 0
        · simp [hr0]
        · have heq : Nat.choose q r =
              Nat.choose (q - 1) (r - 1) + Nat.choose (q - 1) r := by
            calc
              Nat.choose q r =
                  Nat.choose (Nat.succ (q - 1)) (Nat.succ (r - 1)) := by
                congr <;> omega
              _ = _ := by
                have hp := Nat.choose_succ_succ' (q - 1) (r - 1)
                rw [show r - 1 + 1 = r by omega] at hp
                simpa [Nat.succ_eq_add_one, show r - 1 + 1 = r by omega] using hp
          rw [heq]
          omega

/-- The one-vertex extension relation between consecutive levels. -/
def ExtendsByOne (S T : Finset (Fin n)) : Prop :=
  S ⊆ T ∧ T.card = S.card + 1

instance instDecidableExtendsByOne (n : ℕ) :
    DecidableRel (@ExtendsByOne n) := fun S T ↦ by
  unfold ExtendsByOne
  infer_instance

lemma incoming_extensions_le
    (right left : Finset (Finset (Fin n))) (T : Finset (Fin n))
    (hTq : T.card ≤ q) :
    (left.filter fun S ↦ ExtendsByOne S T).card ≤ 2 ^ q := by
  classical
  calc
    (left.filter fun S ↦ ExtendsByOne S T).card ≤ T.powerset.card := by
      apply Finset.card_le_card
      intro S hS
      exact Finset.mem_powerset.mpr (Finset.mem_filter.mp hS).2.1
    _ = 2 ^ T.card := Finset.card_powerset T
    _ ≤ 2 ^ q := Nat.pow_le_pow_right (by omega) hTq

lemma mem_extensionLevel_data
    {reserve : Finset (Finset (Fin n))} {e S : Finset (Fin n)}
    (hS : S ∈ extensionLevel n q r reserve e i) :
    S.card = r + i ∧ e ⊆ S ∧ cliqueEdges S r \ {e} ⊆ reserve := by
  have hm := Finset.mem_filter.mp hS
  exact ⟨mem_uniformEdges.mp hm.1, hm.2.1, hm.2.2⟩

/-- Every clean common neighbour of a valid partial extension gives a
distinct valid set on the next level. -/
lemma commonNeighbors_le_successors
    {n q r i : ℕ} (hr : 1 < r) (hi : i < q - r)
    (e S : Finset (Fin n))
    (ω : {a // a ∈ uniformEdges n r} → Bool)
    (hS : S ∈ extensionLevel n q r (sampledEdges n r ω) e i) :
    (commonNeighbors n r (extensionRoots S r) (by omega)
        (fun f hf ↦ (mem_extensionRoots.mp hf).2) ω).card ≤
      ((extensionLevel n q r (sampledEdges n r ω) e (i + 1)).filter
        (ExtendsByOne S)).card := by
  classical
  let roots := extensionRoots S r
  let hroot : ∀ f ∈ roots, f.card = r - 1 :=
    fun f hf ↦ (mem_extensionRoots.mp hf).2
  let source := commonNeighbors n r roots (by omega) hroot ω
  let target := (extensionLevel n q r (sampledEdges n r ω) e (i + 1)).filter
    (ExtendsByOne S)
  apply Finset.card_le_card_of_injOn
      (fun x : cleanVertices n roots ↦ insert (x : Fin n) S)
      (s := source) (t := target)
  · intro x hx
    have hxgood : ∀ f : {f // f ∈ roots},
        ω (commonEdgeCoord n r roots (by omega) hroot ⟨x, f⟩) = true :=
      (Finset.mem_filter.mp hx).2
    have hSdata := mem_extensionLevel_data hS
    have hSr : r ≤ S.card := by omega
    have hxS : (x : Fin n) ∉ S := by
      apply (mem_cleanVertices_extensionRoots hr hSr x).mp
      simpa [roots] using x.property
    have hcard : (insert (x : Fin n) S).card = r + (i + 1) := by
      rw [Finset.card_insert_of_notMem hxS, hSdata.1]
      omega
    have heS : e ⊆ insert (x : Fin n) S :=
      hSdata.2.1.trans (Finset.subset_insert _ _)
    have hedge : cliqueEdges (insert (x : Fin n) S) r \ {e} ⊆
        sampledEdges n r ω := by
      intro A hA
      have hAclique := (Finset.mem_sdiff.mp hA).1
      have hAne : A ≠ e := by simpa using (Finset.mem_sdiff.mp hA).2
      have hAsub : A ⊆ insert (x : Fin n) S :=
        (Finset.mem_powersetCard.mp hAclique).1
      have hAcard : A.card = r := (Finset.mem_powersetCard.mp hAclique).2
      by_cases hxA : (x : Fin n) ∈ A
      · let f := A.erase x
        have hfsub : f ⊆ S := by
          intro y hy
          have hyA : y ∈ A := Finset.mem_of_mem_erase hy
          rcases Finset.mem_insert.mp (hAsub hyA) with hyx | hyS
          · subst y
            exact (Finset.notMem_erase (x : Fin n) A hy).elim
          · exact hyS
        have hfcard : f.card = r - 1 := by
          change (A.erase (x : Fin n)).card = r - 1
          rw [Finset.card_erase_of_mem hxA, hAcard]
        have hfroot : f ∈ roots :=
          mem_extensionRoots.mpr ⟨hfsub, hfcard⟩
        have hω := hxgood ⟨f, hfroot⟩
        apply mem_sampledEdges.mpr
        let hAuniform : A ∈ uniformEdges n r := mem_uniformEdges.mpr hAcard
        refine ⟨hAuniform, ?_⟩
        have hAf : A = insert (x : Fin n) f := (Finset.insert_erase hxA).symm
        have hcoord : commonEdgeCoord n r roots (by omega) hroot ⟨x, ⟨f, hfroot⟩⟩ =
            ⟨A, hAuniform⟩ := by
          apply Subtype.ext
          exact hAf.symm
        simpa [hcoord] using hω
      · have hAS : A ⊆ S := by
          intro y hy
          rcases Finset.mem_insert.mp (hAsub hy) with hyx | hyS
          · exact (hxA (hyx ▸ hy)).elim
          · exact hyS
        exact hSdata.2.2 (Finset.mem_sdiff.mpr
          ⟨Finset.mem_powersetCard.mpr ⟨hAS, hAcard⟩, by simpa⟩)
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_filter.mpr
      exact ⟨mem_uniformEdges.mpr hcard, heS, hedge⟩
    · exact ⟨Finset.subset_insert _ _, by
        rw [Finset.card_insert_of_notMem hxS]⟩
  · intro x hx y hy hxy
    have hSdata := mem_extensionLevel_data hS
    have hSr : r ≤ S.card := by omega
    have hxS : (x : Fin n) ∉ S :=
      (mem_cleanVertices_extensionRoots hr hSr x).mp (by
        simpa [roots] using x.property)
    have hyS : (y : Fin n) ∉ S :=
      (mem_cleanVertices_extensionRoots hr hSr y).mp (by
        simpa [roots] using y.property)
    apply Subtype.ext
    change insert (x : Fin n) S = insert (y : Fin n) S at hxy
    have hxmem : (x : Fin n) ∈ insert (y : Fin n) S := by
      rw [← hxy]
      exact Finset.mem_insert_self _ _
    rcases Finset.mem_insert.mp hxmem with h | h
    · exact h
    · exact (hxS h).elim

/-- Conversely, every valid one-vertex successor arises from one clean
common neighbour.  Together with `commonNeighbors_le_successors`, this is
the exact branching identity for the extension tree. -/
lemma successors_le_commonNeighbors
    {n q r i : ℕ} (hr : 1 < r) (hi : i < q - r)
    (e S : Finset (Fin n))
    (ω : {a // a ∈ uniformEdges n r} → Bool)
    (hS : S ∈ extensionLevel n q r (sampledEdges n r ω) e i) :
    ((extensionLevel n q r (sampledEdges n r ω) e (i + 1)).filter
        (ExtendsByOne S)).card ≤
      (commonNeighbors n r (extensionRoots S r) (by omega)
        (fun f hf ↦ (mem_extensionRoots.mp hf).2) ω).card := by
  classical
  let roots := extensionRoots S r
  let hroot : ∀ f ∈ roots, f.card = r - 1 :=
    fun f hf ↦ (mem_extensionRoots.mp hf).2
  let source := commonNeighbors n r roots (by omega) hroot ω
  let target := (extensionLevel n q r (sampledEdges n r ω) e (i + 1)).filter
    (ExtendsByOne S)
  have hdiff (T : ↑target) : (T.1 \ S).card = 1 := by
    have hrel := (Finset.mem_filter.mp T.2).2
    rw [Finset.card_sdiff_of_subset hrel.1, hrel.2]
    omega
  let added (T : ↑target) : Fin n :=
    Classical.choose (Finset.card_eq_one.mp (hdiff T))
  have hadded (T : ↑target) : T.1 \ S = {added T} :=
    Classical.choose_spec (Finset.card_eq_one.mp (hdiff T))
  have hadded_mem (T : ↑target) : added T ∈ T.1 \ S := by
    rw [hadded]
    simp
  have hT_eq (T : ↑target) : T.1 = insert (added T) S := by
    apply Finset.Subset.antisymm
    · intro x hx
      by_cases hxS : x ∈ S
      · exact Finset.mem_insert_of_mem hxS
      · have : x ∈ T.1 \ S := Finset.mem_sdiff.mpr ⟨hx, hxS⟩
        rw [hadded] at this
        exact Finset.mem_insert.mpr (Or.inl (Finset.mem_singleton.mp this))
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hxS
      · exact (Finset.mem_sdiff.mp (hadded_mem T)).1
      · exact (Finset.mem_filter.mp T.2).2.1 hxS
  have hadded_clean (T : ↑target) :
      added T ∈ cleanVertices n roots := by
    have hxNotS : added T ∉ S :=
      (Finset.mem_sdiff.mp (hadded_mem T)).2
    apply (mem_cleanVertices_extensionRoots hr (by
      have hSdata := mem_extensionLevel_data hS
      omega) (added T)).mpr
    exact hxNotS
  have hadded_source (T : ↑target) :
      (⟨added T, hadded_clean T⟩ : ↑(cleanVertices n roots)) ∈ source := by
    have hTlevel := (Finset.mem_filter.mp T.2).1
    have hTdata := mem_extensionLevel_data hTlevel
    have hxNotS : added T ∉ S :=
      (Finset.mem_sdiff.mp (hadded_mem T)).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro f
    have hfroot : f.1 ∈ roots := f.2
    have hfdata := mem_extensionRoots.mp hfroot
    let A := insert (added T) f.1
    have hxNotF : added T ∉ f.1 := fun h ↦ hxNotS (hfdata.1 h)
    have hAcard : A.card = r := by
      rw [Finset.card_insert_of_notMem hxNotF, hfdata.2]
      omega
    have hAsub : A ⊆ T.1 := by
      rw [hT_eq T]
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (hfdata.1 hy)
    have hAne : A ≠ e := by
      intro hAe
      have hxE : added T ∈ e := by
        rw [← hAe]
        exact Finset.mem_insert_self _ _
      have heS : e ⊆ S := (mem_extensionLevel_data hS).2.1
      exact hxNotS (heS hxE)
    have hAreserve : A ∈ sampledEdges n r ω := by
      apply hTdata.2.2
      exact Finset.mem_sdiff.mpr
        ⟨Finset.mem_powersetCard.mpr ⟨hAsub, hAcard⟩, by simpa⟩
    have hcoord : commonEdgeCoord n r roots (by omega) hroot
        ⟨⟨added T, hadded_clean T⟩, f⟩ =
        ⟨A, mem_uniformEdges.mpr hAcard⟩ := by
      apply Subtype.ext
      rfl
    have hω := (mem_sampledEdges.mp hAreserve).2
    simpa [hcoord] using hω
  let φ : ↑target → ↑source := fun T ↦
    ⟨⟨added T, hadded_clean T⟩, hadded_source T⟩
  have hφinj : Function.Injective φ := by
    intro T U h
    apply Subtype.ext
    rw [hT_eq T, hT_eq U]
    have : added T = added U :=
      congrArg (fun z : ↑source ↦ (z.1.1 : Fin n)) h
    rw [this]
  calc
    target.card = Fintype.card ↑target := (Fintype.card_coe target).symm
    _ ≤ Fintype.card ↑source := Fintype.card_le_of_injective φ hφinj
    _ = source.card := Fintype.card_coe source

theorem card_successors_eq_commonNeighbors
    {n q r i : ℕ} (hr : 1 < r) (hi : i < q - r)
    (e S : Finset (Fin n))
    (ω : {a // a ∈ uniformEdges n r} → Bool)
    (hS : S ∈ extensionLevel n q r (sampledEdges n r ω) e i) :
    ((extensionLevel n q r (sampledEdges n r ω) e (i + 1)).filter
        (ExtendsByOne S)).card =
      (commonNeighbors n r (extensionRoots S r) (by omega)
        (fun f hf ↦ (mem_extensionRoots.mp hf).2) ω).card := by
  exact Nat.le_antisymm
    (successors_le_commonNeighbors hr hi e S ω hS)
    (commonNeighbors_le_successors hr hi e S ω hS)

private lemma extensionLevel_predecessor_nonempty
    {n q r i : ℕ} {reserve : Finset (Finset (Fin n))}
    {e T : Finset (Fin n)} (hecard : e.card = r)
    (hT : T ∈ extensionLevel n q r reserve e (i + 1)) :
    ((extensionLevel n q r reserve e i).filter fun S ↦
      ExtendsByOne S T).Nonempty := by
  classical
  have hTdata := mem_extensionLevel_data hT
  have heT : e ⊆ T := hTdata.2.1
  have hdiffCard : (T \ e).card = i + 1 := by
    rw [Finset.card_sdiff_of_subset heT, hTdata.1, hecard]
    omega
  have hdiff : (T \ e).Nonempty := Finset.card_pos.mp (by omega)
  let x := hdiff.choose
  have hxDiff : x ∈ T \ e := hdiff.choose_spec
  have hxT : x ∈ T := (Finset.mem_sdiff.mp hxDiff).1
  have hxNotE : x ∉ e := (Finset.mem_sdiff.mp hxDiff).2
  let S := T.erase x
  have hScard : S.card = r + i := by
    change (T.erase x).card = r + i
    rw [Finset.card_erase_of_mem hxT, hTdata.1]
    omega
  have heS : e ⊆ S := by
    intro y hy
    apply Finset.mem_erase.mpr
    exact ⟨fun hyx ↦ hxNotE (hyx ▸ hy), heT hy⟩
  have hhost : cliqueEdges S r \ {e} ⊆ reserve := by
    intro A hA
    apply hTdata.2.2
    have hm := Finset.mem_sdiff.mp hA
    apply Finset.mem_sdiff.mpr
    exact ⟨Finset.mem_powersetCard.mpr
      ⟨(Finset.mem_powersetCard.mp hm.1).1.trans (Finset.erase_subset _ _),
        (Finset.mem_powersetCard.mp hm.1).2⟩, hm.2⟩
  refine ⟨S, Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
  · exact Finset.mem_filter.mpr
      ⟨mem_uniformEdges.mpr hScard, heS, hhost⟩
  · constructor
    · exact Finset.erase_subset _ _
    · rw [hScard, hTdata.1]
      omega

/-- Upper branching bound for one extension level. -/
theorem extensionLevel_step_upper
    {n q r i U : ℕ} (hr : 1 < r) (hi : i < q - r)
    {e : Finset (Fin n)} (hecard : e.card = r)
    (ω : {a // a ∈ uniformEdges n r} → Bool)
    (hupper : ∀ S ∈ extensionLevel n q r (sampledEdges n r ω) e i,
      (commonNeighbors n r (extensionRoots S r) (by omega)
        (fun f hf ↦ (mem_extensionRoots.mp hf).2) ω).card ≤ U) :
    (extensionLevel n q r (sampledEdges n r ω) e (i + 1)).card ≤
      (extensionLevel n q r (sampledEdges n r ω) e i).card * U := by
  have hrel := card_mul_le_card_mul_of_relation
    (extensionLevel n q r (sampledEdges n r ω) e (i + 1))
    (extensionLevel n q r (sampledEdges n r ω) e i)
    (fun T S ↦ ExtendsByOne S T) 1 U
    (by
      intro T hT
      exact Finset.card_pos.mpr
        (extensionLevel_predecessor_nonempty hecard hT))
    (by
      intro S hS
      rw [card_successors_eq_commonNeighbors hr hi e S ω hS]
      exact hupper S hS)
  simpa using hrel

/-- Product upper bound with a level-dependent branching cap. -/
theorem extensionLevel_iterate_upper
    {n q r m : ℕ} (hr : 1 < r) (hm : m ≤ q - r)
    {e : Finset (Fin n)} (hecard : e.card = r)
    (ω : {a // a ∈ uniformEdges n r} → Bool) (U : ℕ → ℕ)
    (hupper : ∀ i < m, ∀ S ∈
      extensionLevel n q r (sampledEdges n r ω) e i,
      (commonNeighbors n r (extensionRoots S r) (by omega)
        (fun f hf ↦ (mem_extensionRoots.mp hf).2) ω).card ≤ U i) :
    (extensionLevel n q r (sampledEdges n r ω) e m).card ≤
      (extensionLevel n q r (sampledEdges n r ω) e 0).card *
        ∏ i ∈ Finset.range m, U i := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hmle : m ≤ q - r := by omega
      have hmLt : m < q - r := by omega
      have hprev := ih hmle (fun i hi ↦ hupper i (by omega))
      have hstep := extensionLevel_step_upper hr hmLt hecard ω
        (hupper m (by omega))
      rw [Finset.prod_range_succ]
      exact hstep.trans (by
        simpa [Nat.mul_assoc] using Nat.mul_le_mul_right (U m) hprev)

/-- One level of the extension tree grows by the common-neighbour lower
bound, up to the uniform `2^q` predecessor multiplicity. -/
theorem extensionLevel_step
    {n q r i ell : ℕ} (hr : 1 < r) (hi : i < q - r)
    (e : Finset (Fin n))
    (ω : {a // a ∈ uniformEdges n r} → Bool)
    (hlower : ∀ S ∈ extensionLevel n q r (sampledEdges n r ω) e i,
      ell ≤ (commonNeighbors n r (extensionRoots S r) (by omega)
        (fun f hf ↦ (mem_extensionRoots.mp hf).2) ω).card) :
    (extensionLevel n q r (sampledEdges n r ω) e i).card * ell ≤
      (extensionLevel n q r (sampledEdges n r ω) e (i + 1)).card * 2 ^ q := by
  apply card_mul_le_card_mul_of_relation
    (extensionLevel n q r (sampledEdges n r ω) e i)
    (extensionLevel n q r (sampledEdges n r ω) e (i + 1))
    ExtendsByOne ell (2 ^ q)
  · intro S hS
    exact (hlower S hS).trans (commonNeighbors_le_successors hr hi e S ω hS)
  · intro T hT
    have hTcard : T.card = r + (i + 1) := (mem_extensionLevel_data hT).1
    have hrq : r ≤ q := by
      by_contra hnot
      have : q - r = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_not_ge hnot)
      omega
    have hi' : i + 1 ≤ q - r := by omega
    have hTq : T.card ≤ q := by
      calc
      T.card = r + (i + 1) := hTcard
      _ ≤ r + (q - r) := Nat.add_le_add_left hi' r
      _ = q := Nat.add_sub_of_le hrq
    exact incoming_extensions_le
      (extensionLevel n q r (sampledEdges n r ω) e (i + 1))
      (extensionLevel n q r (sampledEdges n r ω) e i) T hTq

/-- Iterating the bipartite count through `m` extension levels. -/
theorem extensionLevel_iterate
    {n q r m ell : ℕ} (hr : 1 < r) (hm : m ≤ q - r)
    (e : Finset (Fin n))
    (ω : {a // a ∈ uniformEdges n r} → Bool)
    (hlower : ∀ i < m, ∀ S ∈
      extensionLevel n q r (sampledEdges n r ω) e i,
      ell ≤ (commonNeighbors n r (extensionRoots S r) (by omega)
        (fun f hf ↦ (mem_extensionRoots.mp hf).2) ω).card) :
    (extensionLevel n q r (sampledEdges n r ω) e 0).card * ell ^ m ≤
      (extensionLevel n q r (sampledEdges n r ω) e m).card * (2 ^ q) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hmq : m < q - r := by omega
      have hprev := ih (by omega) (fun i hi ↦ hlower i (by omega))
      have hstep := extensionLevel_step hr hmq e ω (hlower m (by omega))
      calc
        (extensionLevel n q r (sampledEdges n r ω) e 0).card * ell ^ (m + 1) =
            ((extensionLevel n q r (sampledEdges n r ω) e 0).card * ell ^ m) * ell := by
          ring
        _ ≤ ((extensionLevel n q r (sampledEdges n r ω) e m).card *
            (2 ^ q) ^ m) * ell := Nat.mul_le_mul_right ell hprev
        _ = ((extensionLevel n q r (sampledEdges n r ω) e m).card * ell) *
            (2 ^ q) ^ m := by ring
        _ ≤ ((extensionLevel n q r (sampledEdges n r ω) e (m + 1)).card *
            2 ^ q) * (2 ^ q) ^ m := Nat.mul_le_mul_right ((2 ^ q) ^ m) hstep
        _ = (extensionLevel n q r (sampledEdges n r ω) e (m + 1)).card *
            (2 ^ q) ^ (m + 1) := by ring

/-- Variable branching factors; this retains the telescoping reserve
density exponent instead of replacing every level by the worst one. -/
theorem extensionLevel_iterate_variable
    {n q r m : ℕ} (hr : 1 < r) (hm : m ≤ q - r)
    (ell : ℕ → ℕ) (e : Finset (Fin n))
    (ω : {a // a ∈ uniformEdges n r} → Bool)
    (hlower : ∀ i < m, ∀ S ∈
      extensionLevel n q r (sampledEdges n r ω) e i,
      ell i ≤ (commonNeighbors n r (extensionRoots S r) (by omega)
        (fun f hf ↦ (mem_extensionRoots.mp hf).2) ω).card) :
    (extensionLevel n q r (sampledEdges n r ω) e 0).card *
        ∏ i ∈ Finset.range m, ell i ≤
      (extensionLevel n q r (sampledEdges n r ω) e m).card * (2 ^ q) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hmq : m < q - r := by omega
      have hprev := ih (by omega) (fun i hi ↦ hlower i (by omega))
      have hstep := extensionLevel_step hr hmq e ω (hlower m (by omega))
      rw [Finset.prod_range_succ]
      calc
        (extensionLevel n q r (sampledEdges n r ω) e 0).card *
            ((∏ i ∈ Finset.range m, ell i) * ell m) =
            ((extensionLevel n q r (sampledEdges n r ω) e 0).card *
              ∏ i ∈ Finset.range m, ell i) * ell m := by ring
        _ ≤ ((extensionLevel n q r (sampledEdges n r ω) e m).card *
            (2 ^ q) ^ m) * ell m := Nat.mul_le_mul_right (ell m) hprev
        _ = ((extensionLevel n q r (sampledEdges n r ω) e m).card * ell m) *
            (2 ^ q) ^ m := by ring
        _ ≤ ((extensionLevel n q r (sampledEdges n r ω) e (m + 1)).card *
            2 ^ q) * (2 ^ q) ^ m := Nat.mul_le_mul_right ((2 ^ q) ^ m) hstep
        _ = (extensionLevel n q r (sampledEdges n r ω) e (m + 1)).card *
            (2 ^ q) ^ (m + 1) := by ring

lemma extensionLevel_zero
    {reserve : Finset (Finset (Fin n))} {e : Finset (Fin n)}
    (he : e.card = r) :
    extensionLevel n q r reserve e 0 = {e} := by
  classical
  ext S
  constructor
  · intro hS
    have hdata := mem_extensionLevel_data hS
    have hSe : S = e :=
      (Finset.eq_of_subset_of_card_le hdata.2.1 (by omega)).symm
    simpa [hSe]
  · intro hS
    have hSe : S = e := Finset.mem_singleton.mp hS
    subst S
    apply Finset.mem_filter.mpr
    constructor
    · exact mem_uniformEdges.mpr (by simpa using he)
    · constructor
      · exact Finset.Subset.rfl
      · intro A hA
        have hAclique := (Finset.mem_sdiff.mp hA).1
        have hAcard := (Finset.mem_powersetCard.mp hAclique).2
        have hAsub := (Finset.mem_powersetCard.mp hAclique).1
        have hAe : A = e := Finset.eq_of_subset_of_card_le hAsub (by omega)
        exact ((Finset.mem_sdiff.mp hA).2 (by simpa [hAe])).elim

/-- Final partial extensions are precisely the reserve candidates through
the root edge. -/
def reserveCandidates (n q r : ℕ) (reserve : Finset (Finset (Fin n)))
    (e : Finset (Fin n)) : Finset (Finset (Fin n)) :=
  (uniformEdges n q).filter fun B ↦
    e ⊆ B ∧ cliqueEdges B r \ {e} ⊆ reserve

lemma extensionLevel_final (hrq : r ≤ q)
    (reserve : Finset (Finset (Fin n))) (e : Finset (Fin n)) :
    extensionLevel n q r reserve e (q - r) =
      reserveCandidates n q r reserve e := by
  have : r + (q - r) = q := Nat.add_sub_of_le hrq
  simp only [extensionLevel, reserveCandidates, this]

/-- The level count at the final stage is the promised lower bound on
reserve-supported clique extensions. -/
theorem reserveCandidates_mul_lower
    {n q r ell : ℕ} (hr : 1 < r) (hrq : r ≤ q)
    (e : Finset (Fin n)) (he : e.card = r)
    (ω : {a // a ∈ uniformEdges n r} → Bool)
    (hlower : ∀ i < q - r, ∀ S ∈
      extensionLevel n q r (sampledEdges n r ω) e i,
      ell ≤ (commonNeighbors n r (extensionRoots S r) (by omega)
        (fun f hf ↦ (mem_extensionRoots.mp hf).2) ω).card) :
    ell ^ (q - r) ≤
      (reserveCandidates n q r (sampledEdges n r ω) e).card *
        (2 ^ q) ^ (q - r) := by
  have hiter := extensionLevel_iterate hr (le_refl (q - r)) e ω hlower
  rw [extensionLevel_zero he, Finset.card_singleton, one_mul,
    extensionLevel_final hrq] at hiter
  exact hiter

theorem reserveCandidates_prod_lower
    {n q r : ℕ} (hr : 1 < r) (hrq : r ≤ q)
    (ell : ℕ → ℕ) (e : Finset (Fin n)) (he : e.card = r)
    (ω : {a // a ∈ uniformEdges n r} → Bool)
    (hlower : ∀ i < q - r, ∀ S ∈
      extensionLevel n q r (sampledEdges n r ω) e i,
      ell i ≤ (commonNeighbors n r (extensionRoots S r) (by omega)
        (fun f hf ↦ (mem_extensionRoots.mp hf).2) ω).card) :
    (∏ i ∈ Finset.range (q - r), ell i) ≤
      (reserveCandidates n q r (sampledEdges n r ω) e).card *
        (2 ^ q) ^ (q - r) := by
  have hiter := extensionLevel_iterate_variable hr (le_refl (q - r)) ell e ω hlower
  rw [extensionLevel_zero he, Finset.card_singleton, one_mul,
    extensionLevel_final hrq] at hiter
  exact hiter

/-- Simultaneous typicality supplies the uniform integer branching factor
needed by the extension-tree count. -/
theorem typical_extension_lower
    {n q r ell : ℕ} (hr : 1 < r) (hrq : r < q)
    (p : Set.Icc (0 : ℝ) 1)
    (ω : {a // a ∈ uniformEdges n r} → Bool)
    (e : Finset (Fin n))
    (htyp : ∀ roots, ∀ hroots :
      roots ∈ rootFamilies n r (Nat.choose q r),
      commonMean n roots p / 2 <
        Probability.finiteRandomSum
          (fun x ↦ commonNeighborIndicator n r roots (by omega)
            (root_card_of_mem_rootFamilies hroots) x) ω ∧
      Probability.finiteRandomSum
          (fun x ↦ commonNeighborIndicator n r roots (by omega)
            (root_card_of_mem_rootFamilies hroots) x) ω <
        2 * commonMean n roots p)
    (hell : (ell : ℝ) ≤
      ((n - Nat.choose q r * (r - 1) : ℕ) : ℝ) *
        (p : ℝ) ^ Nat.choose q r / 2) :
    ∀ i < q - r, ∀ S ∈
      extensionLevel n q r (sampledEdges n r ω) e i,
      ell ≤ (commonNeighbors n r (extensionRoots S r) (by omega)
        (fun f hf ↦ (mem_extensionRoots.mp hf).2) ω).card := by
  intro i hi S hS
  have hSdata := mem_extensionLevel_data hS
  have hSq : S.card < q := by omega
  let roots := extensionRoots S r
  have hroots : roots ∈ rootFamilies n r (Nat.choose q r) :=
    extensionRoots_mem_rootFamilies hSq
  let hroot : ∀ f ∈ roots, f.card = r - 1 :=
    root_card_of_mem_rootFamilies hroots
  have hcleanNat : n - Nat.choose q r * (r - 1) ≤
      (cleanVertices n roots).card :=
    cleanVertices_card_lower hroot (mem_rootFamilies.mp hroots).2
  have hclean : ((n - Nat.choose q r * (r - 1) : ℕ) : ℝ) ≤
      (cleanVertices n roots).card := by exact_mod_cast hcleanNat
  have hpow : (p : ℝ) ^ Nat.choose q r ≤ (p : ℝ) ^ roots.card :=
    pow_le_pow_of_le_one p.property.1 p.property.2 (mem_rootFamilies.mp hroots).2
  have hmean :
      ((n - Nat.choose q r * (r - 1) : ℕ) : ℝ) *
          (p : ℝ) ^ Nat.choose q r ≤ commonMean n roots p := by
    unfold commonMean
    exact mul_le_mul hclean hpow (pow_nonneg p.property.1 _)
      (by positivity)
  have htypical := (htyp roots hroots).1
  rw [← card_commonNeighbors n r roots (by omega) hroot ω] at htypical
  have hell' : (ell : ℝ) <
      ((commonNeighbors n r roots (by omega) hroot ω).card : ℝ) :=
    hell.trans_lt ((div_le_div_of_nonneg_right hmean (by norm_num)).trans_lt htypical)
  exact_mod_cast hell'.le

theorem typical_extension_lower_variable
    {n q r : ℕ} (hr : 1 < r) (hrq : r < q)
    (p : Set.Icc (0 : ℝ) 1)
    (ω : {a // a ∈ uniformEdges n r} → Bool)
    (e : Finset (Fin n)) (ell : ℕ → ℕ)
    (htyp : ∀ roots, ∀ hroots :
      roots ∈ rootFamilies n r (Nat.choose q r),
      commonMean n roots p / 2 <
        Probability.finiteRandomSum
          (fun x ↦ commonNeighborIndicator n r roots (by omega)
            (root_card_of_mem_rootFamilies hroots) x) ω ∧
      Probability.finiteRandomSum
          (fun x ↦ commonNeighborIndicator n r roots (by omega)
            (root_card_of_mem_rootFamilies hroots) x) ω <
        2 * commonMean n roots p)
    (hell : ∀ i < q - r, (ell i : ℝ) ≤
      ((n - Nat.choose q r * (r - 1) : ℕ) : ℝ) *
        (p : ℝ) ^ Nat.choose (r + i) (r - 1) / 2) :
    ∀ i < q - r, ∀ S ∈
      extensionLevel n q r (sampledEdges n r ω) e i,
      ell i ≤ (commonNeighbors n r (extensionRoots S r) (by omega)
        (fun f hf ↦ (mem_extensionRoots.mp hf).2) ω).card := by
  intro i hi S hS
  have hSdata := mem_extensionLevel_data hS
  have hSq : S.card < q := by omega
  let roots := extensionRoots S r
  have hroots : roots ∈ rootFamilies n r (Nat.choose q r) :=
    extensionRoots_mem_rootFamilies hSq
  let hroot : ∀ f ∈ roots, f.card = r - 1 :=
    root_card_of_mem_rootFamilies hroots
  have hrootsCard : roots.card = Nat.choose (r + i) (r - 1) := by
    change (extensionRoots S r).card = _
    rw [card_extensionRoots, hSdata.1]
  have hcleanNat : n - Nat.choose q r * (r - 1) ≤
      (cleanVertices n roots).card :=
    cleanVertices_card_lower hroot (mem_rootFamilies.mp hroots).2
  have hclean : ((n - Nat.choose q r * (r - 1) : ℕ) : ℝ) ≤
      (cleanVertices n roots).card := by exact_mod_cast hcleanNat
  have hmean :
      ((n - Nat.choose q r * (r - 1) : ℕ) : ℝ) *
          (p : ℝ) ^ Nat.choose (r + i) (r - 1) ≤ commonMean n roots p := by
    unfold commonMean
    rw [hrootsCard]
    exact mul_le_mul_of_nonneg_right hclean (pow_nonneg p.property.1 _)
  have htypical := (htyp roots hroots).1
  rw [← card_commonNeighbors n r roots (by omega) hroot ω] at htypical
  have hell' : (ell i : ℝ) <
      ((commonNeighbors n r roots (by omega) hroot ω).card : ℝ) :=
    (hell i hi).trans_lt
      ((div_le_div_of_nonneg_right hmean (by norm_num)).trans_lt htypical)
  exact_mod_cast hell'.le

/-- The completed sparse-reserve lemma in the finite-set language of this
file.  It is an eventual statement because only the two explicit scalar
estimates above require `n` to be large. -/
theorem eventually_exists_reserve
    (q r : ℕ) (hr : 1 < r) (hrq : r < q) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∃ reserve : Finset (Finset (Fin n)),
        reserve ⊆ uniformEdges n r ∧
        (∀ I, I.card = r - 1 →
          (localDegree reserve I) ^ ((6 * Nat.choose q r) ^ 2) ≤
            2 ^ ((6 * Nat.choose q r) ^ 2) *
              n ^ (((6 * Nat.choose q r) ^ 2) - 1)) ∧
        ∀ e ∈ uniformEdges n r \ reserve,
          n ^ (((6 * Nat.choose q r) ^ 2) * (q - r) - Nat.choose q r) ≤
            (reserveCandidates n q r reserve e).card ^
              ((6 * Nat.choose q r) ^ 2) := by
  have hscalar := eventually_reserve_scalar_bound q r (by omega) hrq.le
  have hproduct := eventually_branching_product_power_lower q r (by omega) hrq
  filter_upwards [hscalar, hproduct, Filter.eventually_ge_atTop 1] with
      n hnScalar hnProduct hnOne
  have hn : 0 < n := hnOne
  obtain ⟨ω, htyp, hsub, hdegree⟩ :=
    exists_typical_sampled_reserve hn (by omega) hrq.le hnScalar
  let reserve := sampledEdges n r ω
  refine ⟨reserve, hsub, ?_, ?_⟩
  · intro I hI
    exact hdegree I hI
  · intro e he
    have hecard : e.card = r := mem_uniformEdges.mp (Finset.mem_sdiff.mp he).1
    let ell : ℕ → ℕ := reserveBranching n q r
    let p := reserveProbabilityIcc n ((6 * Nat.choose q r) ^ 2) hn
    have hell : ∀ i < q - r, (ell i : ℝ) ≤
        ((n - Nat.choose q r * (r - 1) : ℕ) : ℝ) *
          (p : ℝ) ^ Nat.choose (r + i) (r - 1) / 2 := by
      intro i hi
      simpa [ell, p, reserveBranchingReal, reserveProbabilityIcc] using
        reserveBranching_cast_le n q r i
    have hlower := typical_extension_lower_variable hr hrq p ω e ell htyp hell
    have htree := reserveCandidates_prod_lower hr hrq.le ell e hecard ω hlower
    let D := (6 * Nat.choose q r) ^ 2
    let C := (2 ^ q) ^ (q - r)
    let target := n ^ (D * (q - r) - Nat.choose q r)
    have htreePow :
        (∏ i ∈ Finset.range (q - r), ell i) ^ D ≤
          ((reserveCandidates n q r reserve e).card * C) ^ D :=
      Nat.pow_le_pow_left htree D
    have hmul : target * C ^ D ≤
        (reserveCandidates n q r reserve e).card ^ D * C ^ D := by
      calc
        target * C ^ D ≤
            (∏ i ∈ Finset.range (q - r), ell i) ^ D := by
          simpa [target, C, D, ell] using hnProduct
        _ ≤ ((reserveCandidates n q r reserve e).card * C) ^ D := htreePow
        _ = (reserveCandidates n q r reserve e).card ^ D * C ^ D := by
          rw [mul_pow]
    have hCpos : 0 < C ^ D := by
      dsimp [C]
      positivity
    have hcancel : target ≤ (reserveCandidates n q r reserve e).card ^ D :=
      Nat.le_of_mul_le_mul_right hmul hCpos
    simpa [target, D] using hcancel

end Erdos722.Reserve
