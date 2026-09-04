/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos171.IncrementArithmetic
import ErdosProblems.Erdos171.Iteration
import ErdosProblems.Erdos171.Tiling
import ErdosProblems.Erdos171.DensityBridges
import ErdosProblems.Erdos171.Correlation
import ErdosProblems.Erdos171.RestrictedMDHJ
import ErdosProblems.Erdos171.UniformWordFibres
import ErdosProblems.Erdos171.StructuredCorrelation
import ErdosProblems.Erdos171.FaceDensity
import ErdosProblems.Erdos171.UniformCorrelation
import ErdosProblems.Erdos171.InsensitiveTiling
import ErdosProblems.Erdos171.AlphabetInduction

/-!
# The final density-increment integration for Erdős 171

This file combines the two quantitative outputs of the Dodos--Kanellopoulos--
Tyros argument.  A structured set `D` is positively correlated with the
ambient family `A`, and a tiling covers all but a quadratically small part of
`D`.  The correlation therefore survives on the covered part.  Since the
tiles are pairwise disjoint, one tile has increased pullback density.

The constants in this lemma are deliberately abstract.  Later in the file
they are instantiated by the frozen constants supplied by the correlation
and insensitive-tiling modules.
-/

namespace Erdos171

open Combinatorics

attribute [local instance] Classical.dec

/-- At a density threshold above one the increment statement is vacuous,
because every finite-set density is at most one. -/
def vacuousDensityIncrementStep {t : ℕ} {delta : ℝ} (hdelta : 1 < delta) :
    DensityIncrementStep t delta where
  increment := 1
  increment_pos := zero_lt_one
  threshold := fun _ ↦ 0
  force _ A hA := by
    exfalso
    exact (not_lt_of_ge (hA.trans (density_le_one A))) hdelta

/-- The qualitative intersection-tiling theorem specialized to the `k`
insensitive factors produced by structured correlation. -/
theorem exists_k_intersection_tiling
    {k : ℕ} (hk : 0 < k) {beta : ℝ} (hbeta : 0 < beta)
    (hone : ∀ d, ∃ n, OneInsensitiveTilingAt k d n beta) :
    ∀ d, ∃ n, InsensitiveIntersectionTilingAt k k d n beta := by
  intro d
  obtain ⟨n, hn⟩ :=
    exists_insensitiveIntersectionTilingAt hbeta hone (k - 1) d
  have hpred : k - 1 + 1 = k := Nat.sub_add_cancel hk
  have hn' : InsensitiveIntersectionTilingAt k k d n beta := by
    simpa only [hpred] using hn
  exact ⟨n, hn'⟩

/-- The preceding specialization while preserving a prescribed lower bound
on the ambient tiling dimension. -/
theorem exists_k_intersection_tiling_ge
    {k : ℕ} (hk : 0 < k) {beta : ℝ} (hbeta : 0 < beta)
    (hone : ∀ d N, ∃ n, N ≤ n ∧ OneInsensitiveTilingAt k d n beta) :
    ∀ d N, ∃ n, N ≤ n ∧
      InsensitiveIntersectionTilingAt k k d n beta := by
  intro d N
  obtain ⟨n, hNn, hn⟩ :=
    exists_insensitiveIntersectionTilingAt_ge hbeta hone (k - 1) d N
  have hpred : k - 1 + 1 = k := Nat.sub_add_cancel hk
  have hn' : InsensitiveIntersectionTilingAt k k d n beta := by
    simpa only [hpred] using hn
  exact ⟨n, hNn, hn'⟩

/-- Choose the frozen small cube and all numerical parameters used by the
DKT increment argument.  The small cube is chosen at density `delta / 4`
and then enlarged, if necessary, to have positive dimension. -/
theorem exists_frozen_DKT_parameters
    {k : ℕ} (hk : 2 ≤ k) (hDHJfinite : FiniteDensityHJ k)
    {delta : ℝ} (hdelta : 0 < delta) (hdelta_one : delta ≤ 1) :
    ∃ m0 : ℕ, 0 < m0 ∧
      (∀ B : Finset (Word k m0), delta / 4 ≤ density B →
        ContainsLine (B : Set (Word k m0))) ∧
      let theta := IncrementArithmetic.theta delta
        (Fintype.card (Line (Fin k) (Fin m0)))
      let eta := IncrementArithmetic.eta delta theta
      let gamma := IncrementArithmetic.gamma delta eta k
      0 < theta ∧ theta ≤ 1 ∧ eta ^ 2 / 2 ≤ delta / 2 ∧
        0 < eta ∧ 0 < gamma ∧ gamma < 2 := by
  have hkpos : 0 < k := lt_of_lt_of_le (by omega) hk
  obtain ⟨m0raw, hm0raw⟩ :=
    hDHJfinite.eventual hkpos (delta / 4) (by positivity)
  let m0 := max m0raw 1
  have hm0raw_le : m0raw ≤ m0 := Nat.le_max_left _ _
  have hm0pos : 0 < m0 :=
    lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_right _ _)
  let : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp hkpos
  have hsmall : ∀ B : Finset (Word k m0), delta / 4 ≤ density B →
      ContainsLine (B : Set (Word k m0)) := hm0raw m0 hm0raw_le
  have huniv : delta / 4 ≤
      density (Finset.univ : Finset (Word k m0)) := by
    rw [density_univ]
    linarith
  obtain ⟨l0, hl0⟩ := hsmall Finset.univ huniv
  let : Nonempty (Line (Fin k) (Fin m0)) := ⟨l0⟩
  have hqpos : (0 : ℝ) < Fintype.card (Line (Fin k) (Fin m0)) := by
    positivity
  have hqone : (1 : ℝ) ≤ Fintype.card (Line (Fin k) (Fin m0)) := by
    exact_mod_cast Fintype.card_pos
  let theta := IncrementArithmetic.theta delta
    (Fintype.card (Line (Fin k) (Fin m0)))
  let eta := IncrementArithmetic.eta delta theta
  let gamma := IncrementArithmetic.gamma delta eta k
  have htheta : 0 < theta :=
    IncrementArithmetic.theta_pos hdelta hqpos
  have htheta_delta : theta ≤ delta / 4 :=
    IncrementArithmetic.theta_le_delta_div_four hdelta.le hqone
  have htheta_one : theta ≤ 1 := by linarith
  have hbounds := IncrementArithmetic.fixed_parameter_bounds
    hdelta hdelta_one htheta htheta_one
      (show (2 : ℝ) ≤ (k : ℝ) by exact_mod_cast hk)
  have heta_one : eta < 1 := by
    have h3eta : 3 * eta < delta := hbounds.2.2.1
    linarith
  have heta_sq_lt : eta ^ 2 < delta := by
    have heta : 0 < eta := hbounds.1
    have heta_sq_lt_eta : eta ^ 2 < eta := by
      nlinarith [mul_pos heta (sub_pos.mpr heta_one)]
    have h3eta : 3 * eta < delta := hbounds.2.2.1
    linarith
  refine ⟨m0, hm0pos, hsmall, ?_⟩
  dsimp only
  exact ⟨htheta, htheta_one, by linarith, hbounds.1,
    hbounds.2.2.2.1, hbounds.2.2.2.2.2.2.2.2⟩

namespace BlockCoord

/-- Finiteness of a nested block-coordinate type, transported from its
ordinary finite index type. -/
noncomputable instance instFintype (M s r : ℕ) :
    Fintype (BlockCoord M s r) :=
  Fintype.ofEquiv (Fin (r * M + s)) (equivFin M s r).symm

end BlockCoord

namespace UniformFibres.FrozenPrefix

open BlockTower

/-- A frozen prefix leaves one distinguished word block and the whole
remaining suffix free.  This subspace exposes those two pieces as one sum
parameter cube. -/
def freeBlockTailNested {t M s q : ℕ} : ∀ {r : ℕ},
    FrozenPrefix (Word t M) r (q + 1) →
      Subspace (Fin M ⊕ BlockCoord M s q) (Fin t) (BlockCoord M s r)
  | _, .nil _ => default
  | _, .cons z p => fixedLeft z (freeBlockTailNested p)

@[simp] theorem freeBlockTailNested_apply {t M s q : ℕ} : ∀ {r : ℕ}
    (p : FrozenPrefix (Word t M) r (q + 1))
    (x : Word t M) (y : BlockCoord M s q → Fin t),
    freeBlockTailNested (s := s) p (Subspace.sumWord x y) =
      BlockTower.functionEquiv t M s r
        (p.prepend (x, (BlockTower.functionEquiv t M s q).symm y))
  | _, .nil _, x, y => by
      change Sum.elim x y =
        BlockTower.functionEquiv t M s (q + 1)
          (x, (BlockTower.functionEquiv t M s q).symm y)
      rw [BlockTower.functionEquiv_succ_apply]
      simp
  | _, .cons z p, x, y => by
      rw [freeBlockTailNested, fixedLeft_apply,
        BlockTower.functionEquiv_succ_apply]
      exact congrArg (Sum.elim z)
        (freeBlockTailNested_apply (s := s) p x y)

/-- Flatten `freeBlockTailNested` back to the ordinary `Fin`-indexed ambient
cube. -/
def freeBlockTail {t M s q r : ℕ}
    (p : FrozenPrefix (Word t M) r (q + 1)) :
    Subspace (Fin M ⊕ BlockCoord M s q) (Fin t) (Fin (r * M + s)) :=
  (freeBlockTailNested (s := s) p).reindex (Equiv.refl _) (Equiv.refl _)
    (BlockCoord.equivFin M s r)

@[simp] theorem freeBlockTail_apply_sumWord {t M s q r : ℕ}
    (p : FrozenPrefix (Word t M) r (q + 1))
    (x : Word t M) (y : BlockCoord M s q → Fin t) :
    freeBlockTail p (Subspace.sumWord x y) =
      BlockTower.coordinateWordEquiv t M s r
        (p.prepend (x, (BlockTower.functionEquiv t M s q).symm y)) := by
  funext i
  simp [freeBlockTail, BlockTower.coordinateWordEquiv_apply,
    Subspace.reindex_apply]

end UniformFibres.FrozenPrefix

@[simp] theorem defaultSubspace_apply {α ι : Type*}
    (x : ι → α) : (default : Subspace ι α ι) x = x := rfl

/-- Change from the block flattening used by `UniformWordFibres` to the
explicit nested-coordinate flattening used by `freeBlockTail`. -/
noncomputable def uniformCoordinatePullback (t M s r : ℕ)
    (A : Finset (Word t (r * M + s))) :
    Finset (Word t (r * M + s)) :=
  A.map (((BlockTower.wordEquiv t M s r).symm.trans
    (BlockTower.coordinateWordEquiv t M s r)).symm.toEmbedding)

@[simp] theorem density_uniformCoordinatePullback (t M s r : ℕ)
    (A : Finset (Word t (r * M + s))) :
    density (uniformCoordinatePullback t M s r A) = density A := by
  rw [uniformCoordinatePullback, density_map_equiv]

@[simp] theorem wordEquiv_mem_uniformCoordinatePullback
    (t M s r : ℕ) (A : Finset (Word t (r * M + s)))
    (z : BlockTower (Word t M) (Word t s) r) :
    BlockTower.wordEquiv t M s r z ∈ uniformCoordinatePullback t M s r A ↔
      BlockTower.coordinateWordEquiv t M s r z ∈ A := by
  simp only [uniformCoordinatePullback, Finset.mem_map,
    Equiv.toEmbedding_apply]
  constructor
  · rintro ⟨a, ha, h⟩
    have hz : (BlockTower.coordinateWordEquiv t M s r).symm a = z := by
      apply (BlockTower.wordEquiv t M s r).injective
      exact h
    have haeq : a = BlockTower.coordinateWordEquiv t M s r z := by
      apply (BlockTower.coordinateWordEquiv t M s r).symm.injective
      simpa using hz
    exact haeq ▸ ha
  · intro hz
    exact ⟨BlockTower.coordinateWordEquiv t M s r z, hz, by simp⟩

/-- The tails in the pullback through `freeBlockTail` are precisely the word
fibres selected by the uniform-fibres lemma, up to the canonical coordinate
equivalence on the tail. -/
theorem density_sectionTails_freeBlockTail_eq_wordFibre
    {k M s q r : ℕ}
    (A : Finset (Word (k + 1) (r * M + s)))
    (p : UniformFibres.FrozenPrefix (Word (k + 1) M) r (q + 1))
    (x : Word (k + 1) M) :
    density (sectionTails
      (default : Subspace (Fin M) (Fin (k + 1)) (Fin M))
      (pullbackFinset p.freeBlockTail A) x) =
      density (UniformWordFibres.wordFibre
        (uniformCoordinatePullback (k + 1) M s r A) p x) := by
  classical
  let e : (BlockCoord M s q → Fin (k + 1)) ≃ Word (k + 1) (q * M + s) :=
    (BlockTower.functionEquiv (k + 1) M s q).symm.trans
      (BlockTower.wordEquiv (k + 1) M s q)
  have hset :
      sectionTails (default : Subspace (Fin M) (Fin (k + 1)) (Fin M))
          (pullbackFinset p.freeBlockTail A) x =
        (UniformWordFibres.wordFibre
          (uniformCoordinatePullback (k + 1) M s r A) p x).map
            e.symm.toEmbedding := by
    ext y
    simp only [mem_sectionTails, mem_pullbackFinset, Finset.mem_map,
      Equiv.toEmbedding_apply, UniformWordFibres.mem_wordFibre,
      wordEquiv_mem_uniformCoordinatePullback, defaultSubspace_apply]
    change p.freeBlockTail (Subspace.sumWord x y) ∈ A ↔ _
    rw [UniformFibres.FrozenPrefix.freeBlockTail_apply_sumWord p x y]
    constructor
    · intro hy
      refine ⟨e y, ?_, ?_⟩
      · simpa [e] using hy
      · exact e.symm_apply_apply y
    · rintro ⟨a, ha, hay⟩
      have haeq : a = e y := by
        apply e.symm.injective
        simpa using hay
      subst a
      simpa [e] using ha
  rw [hset]
  exact density_map_equiv e.symm _

/-- Pulling back through a composite subspace is the same as performing the
two pullbacks successively. -/
@[simp] theorem iterationPullback_comp
    {e d t n : ℕ} (U : Subspace (Fin d) (Fin t) (Fin n))
    (V : Subspace (Fin e) (Fin t) (Fin d))
    (A : Finset (Word t n)) :
    iterationPullback (U.comp V) A =
      iterationPullback V (iterationPullback U A) := by
  simp only [iterationPullback_eq_pullbackFinset, pullbackFinset_comp]

/-- A line in a pullback over an arbitrary finite coordinate type maps to a
line in the original family. -/
theorem not_containsLineOn_pullbackFinset
    {alpha eta iota : Type*} [Fintype (eta → alpha)]
    (U : Subspace eta alpha iota) (A : Finset (iota → alpha))
    (hA : ¬ContainsLineOn (A : Set (iota → alpha))) :
    ¬ContainsLineOn (pullbackFinset U A : Set (eta → alpha)) := by
  intro h
  apply hA
  obtain ⟨l, hl⟩ := h
  refine ⟨U.lineMap l, ?_⟩
  rintro _ ⟨a, rfl⟩
  rw [Subspace.lineMap_apply]
  exact (mem_pullbackFinset U A (l a)).1 (hl ⟨a, rfl⟩)

/-- Removing the part of `D` not covered by a tiling loses at most its whole
density from the correlation with `A`. -/
theorem correlated_density_on_covered
    {X : Type*} [Fintype X] [DecidableEq X]
    (A D E : Finset X) {rho gamma : ℝ}
    (hcorr : (rho + gamma) * density D < density (A ∩ D)) :
    (rho + gamma) * density D - density (D \ E) < density (A ∩ E) := by
  have hsub : A ∩ D ⊆ (A ∩ E) ∪ (D \ E) := by
    intro x hx
    by_cases hxE : x ∈ E
    · exact Finset.mem_union.mpr <|
        Or.inl (Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hx).1, hxE⟩)
    · exact Finset.mem_union.mpr <|
        Or.inr (Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hx).2, hxE⟩)
  have hmono : density (A ∩ D) ≤ density ((A ∩ E) ∪ (D \ E)) :=
    density_mono hsub
  have hunion : density ((A ∩ E) ∪ (D \ E)) ≤
      density (A ∩ E) + density (D \ E) :=
    density_union_le_add _ _
  linarith

/-- A structured correlation which is tiled up to error `gamma²/2` forces
one tile to have density strictly larger than `rho + gamma/2`.

This is the last averaging step of the DKT density-increment proof.  Notice
that `rho` is the actual density, whereas `gamma` may have been frozen at a
smaller baseline density. -/
theorem exists_increment_tile_of_structured_tiling
    {k d n : ℕ} {rho gamma : ℝ}
    (A D : Finset (Word (k + 1) n))
    (T : SubspaceTiling (Fin d) (Fin (k + 1)) (Fin n))
    (hrho : 0 ≤ rho) (hgamma : 0 < gamma)
    (hD : gamma < density D)
    (hcorr : (rho + gamma) * density D < density (A ∩ D))
    (hcontained : T.IsContainedIn D)
    (hloss : density (D \ T.covered) < gamma ^ 2 / 2) :
    ∃ U ∈ T.tiles,
      rho + gamma / 2 < density (iterationPullback U A) := by
  let : Nonempty (Fin (k + 1)) := ⟨⟨0, by omega⟩⟩
  let : Nonempty (Word (k + 1) d) := Pi.instNonempty
  have hcover : T.covered ⊆ D := (T.covered_subset_iff D).2 hcontained
  have hcoverDensity : density T.covered ≤ density D := density_mono hcover
  have hcoveredCorrelation :
      (rho + gamma) * density D - density (D \ T.covered) <
        density (A ∩ T.covered) :=
    correlated_density_on_covered A D T.covered hcorr
  have hcoveredIncrement :
      (rho + gamma / 2) * density T.covered <
        density (A ∩ T.covered) := by
    apply IncrementArithmetic.uncovered_mass_density_increment
      hrho hgamma hD hloss hcoverDensity
    exact hcoveredCorrelation.le
  by_contra! hall
  let q : Subspace (Fin d) (Fin (k + 1)) (Fin n) →
      Finset (Word (k + 1) n) := fun U ↦ subspacePoints U ∩ A
  have hqsub : ∀ U ∈ T.tiles, q U ⊆ subspacePoints U := by
    intro U _
    exact Finset.inter_subset_left
  have hqlocal : ∀ U ∈ T.tiles,
      density (q U) ≤
        (rho + gamma / 2) * density (subspacePoints U) := by
    intro U hU
    have hpull : density (subspacePullback U A) ≤ rho + gamma / 2 := by
      simpa only [iterationPullback_eq_subspacePullback] using hall U hU
    rw [show q U = subspacePoints U ∩ A by rfl,
      density_inter_subspacePoints]
    have htileNonneg : 0 ≤ density (subspacePoints U) := density_nonneg _
    have hmul := mul_le_mul_of_nonneg_left hpull htileNonneg
    nlinarith
  have hsum := density_biUnion_le_mul_density_biUnion
    T.pairwiseDisjoint hqsub hqlocal
  have hpUnion : T.tiles.biUnion subspacePoints = T.covered := rfl
  have hqUnion : T.tiles.biUnion q = T.covered ∩ A := by
    ext x
    simp only [q, Finset.mem_biUnion, Finset.mem_inter]
    constructor
    · rintro ⟨U, hU, hxU, hxA⟩
      exact ⟨T.mem_covered x |>.2 ⟨U, hU, hxU⟩, hxA⟩
    · rintro ⟨hxT, hxA⟩
      obtain ⟨U, hU, hxU⟩ := (T.mem_covered x).1 hxT
      exact ⟨U, hU, hxU, hxA⟩
  rw [hqUnion, hpUnion] at hsum
  have hcomm : T.covered ∩ A = A ∩ T.covered := Finset.inter_comm _ _
  rw [hcomm] at hsum
  exact (not_le_of_gt hcoveredIncrement) hsum

/-- Weak-inequality interface expected by `DensityIncrementStep.force`. -/
theorem exists_increment_subspace_of_structured_tiling
    {k d n : ℕ} {rho gamma : ℝ}
    (A D : Finset (Word (k + 1) n))
    (T : SubspaceTiling (Fin d) (Fin (k + 1)) (Fin n))
    (hrho : 0 ≤ rho) (hgamma : 0 < gamma)
    (hD : gamma < density D)
    (hcorr : (rho + gamma) * density D < density (A ∩ D))
    (hcontained : T.IsContainedIn D)
    (hloss : density (D \ T.covered) < gamma ^ 2 / 2) :
    ∃ U : Subspace (Fin d) (Fin (k + 1)) (Fin n),
      rho + gamma / 2 ≤ density (iterationPullback U A) := by
  obtain ⟨U, _hU, hinc⟩ := exists_increment_tile_of_structured_tiling
    A D T hrho hgamma hD hcorr hcontained hloss
  exact ⟨U, hinc.le⟩

/-- Combine one structured-correlation output with an exact-dimension
intersection tiling.  This is the target-dimension instance from which the
`force` field of the final density-increment step is assembled.

The disjunctive hypothesis is exactly the useful conclusion of the
structured-correlation module: either the original family already has a
line, or its pullback to `W` correlates with an intersection of `k`
insensitive sets. -/
theorem force_of_structured_correlation_and_tiling
    {k d m n : ℕ} (hk : 2 ≤ k)
    {gamma : ℝ} (hgamma : 0 < gamma) (hgamma_two : gamma < 2)
    (A : Finset (Word (k + 1) n))
    (hstructured :
      ContainsLine (A : Set (Word (k + 1) n)) ∨
        ∃ W : Subspace (Fin m) (Fin (k + 1)) (Fin n),
        ∃ D : Fin k → Finset (Word (k + 1) m),
          (∀ i, IsLastInsensitive i (D i : Set (Word (k + 1) m))) ∧
          gamma < density (familyInter D) ∧
          (density A + gamma) * density (familyInter D) <
            density (iterationPullback W A ∩ familyInter D))
    (htiling : InsensitiveIntersectionTilingAt k k d m
      (gamma ^ 2 / (4 * (k : ℝ)))) :
    ContainsLine (A : Set (Word (k + 1) n)) ∨
      ∃ U : Subspace (Fin d) (Fin (k + 1)) (Fin n),
        density A + gamma / 2 ≤ density (iterationPullback U A) := by
  rcases hstructured with hline | ⟨W, D, hDins, hDdense, hDcorr⟩
  · exact Or.inl hline
  · right
    have hkR : (k : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le (by omega : 0 < 2) hk))
    have herror :
        2 * (k : ℝ) * (gamma ^ 2 / (4 * (k : ℝ))) = gamma ^ 2 / 2 :=
      IncrementArithmetic.tiling_error_identity hkR
    have hthreshold :
        2 * (k : ℝ) * (gamma ^ 2 / (4 * (k : ℝ))) <
          density (familyInter D) := by
      rw [herror]
      exact (IncrementArithmetic.tiling_error_lt_gamma hgamma hgamma_two).trans
        hDdense
    obtain ⟨T, hTcontained, hTloss⟩ :=
      htiling (fun i : Fin k ↦ i) D hDins hthreshold
    have hrho : 0 ≤ density A := density_nonneg A
    obtain ⟨V, hV⟩ := exists_increment_subspace_of_structured_tiling
      (iterationPullback W A) (familyInter D) T hrho hgamma hDdense hDcorr
        hTcontained (by simpa only [herror] using hTloss)
    refine ⟨W.comp V, ?_⟩
    simpa only [iterationPullback_comp] using hV

/-- Package target-dependent structured-correlation and tiling dimensions as
a `DensityIncrementStep`.  The middle dimension may depend on the requested
tile dimension, and the ambient threshold may in turn depend on that middle
dimension; no monotonicity of either choice is required. -/
noncomputable def densityIncrementStep_of_structured_tilings
    {k : ℕ} (hk : 2 ≤ k) {delta gamma : ℝ}
    (hgamma : 0 < gamma) (hgamma_two : gamma < 2)
    (middle threshold : ℕ → ℕ)
    (hstructured : ∀ d : ℕ,
      ∀ A : Finset (Word (k + 1) (threshold d)),
        delta ≤ density A →
          ContainsLine (A : Set (Word (k + 1) (threshold d))) ∨
            ∃ W : Subspace (Fin (middle d)) (Fin (k + 1))
                (Fin (threshold d)),
            ∃ D : Fin k → Finset (Word (k + 1) (middle d)),
              (∀ i, IsLastInsensitive i
                (D i : Set (Word (k + 1) (middle d)))) ∧
              gamma < density (familyInter D) ∧
              (density A + gamma) * density (familyInter D) <
                density (iterationPullback W A ∩ familyInter D))
    (htiling : ∀ d : ℕ,
      InsensitiveIntersectionTilingAt k k d (middle d)
        (gamma ^ 2 / (4 * (k : ℝ)))) :
    DensityIncrementStep (k + 1) delta where
  increment := gamma / 2
  increment_pos := half_pos hgamma
  threshold := threshold
  force d A hA :=
    force_of_structured_correlation_and_tiling hk hgamma hgamma_two A
      (hstructured d A hA) (htiling d)

/-- A structured-correlation conclusion at fixed middle and ambient
dimensions.  Naming this interface keeps the dimension-selection layer
independent of how the uniform-fibres argument constructs its witness. -/
def StructuredIncrementAt (k m n : ℕ) (delta gamma : ℝ) : Prop :=
  ∀ A : Finset (Word (k + 1) n), delta ≤ density A →
    ContainsLine (A : Set (Word (k + 1) n)) ∨
      ∃ W : Subspace (Fin m) (Fin (k + 1)) (Fin n),
      ∃ D : Fin k → Finset (Word (k + 1) m),
        (∀ i, IsLastInsensitive i (D i : Set (Word (k + 1) m))) ∧
        gamma < density (familyInter D) ∧
        (density A + gamma) * density (familyInter D) <
          density (iterationPullback W A ∩ familyInter D)

/-- Abstract interface of the uniform-fibres/correlation half of DKT. -/
def UniformStructuredCorrelationPrinciple : Prop :=
  ∀ (k m0 m : ℕ), 2 ≤ k → 0 < m0 → m0 ≤ m →
    ∀ delta0 : ℝ, 0 < delta0 → delta0 ≤ 1 →
    0 < IncrementArithmetic.theta delta0
      (Fintype.card (Line (Fin k) (Fin m0))) →
    IncrementArithmetic.theta delta0
      (Fintype.card (Line (Fin k) (Fin m0))) ≤ 1 →
    (IncrementArithmetic.eta delta0
      (IncrementArithmetic.theta delta0
        (Fintype.card (Line (Fin k) (Fin m0))))) ^ 2 / 2 ≤ delta0 / 2 →
    density (liftFinset (Finset.univ : Finset (Word k m))) <
      IncrementArithmetic.eta delta0
        (IncrementArithmetic.theta delta0
          (Fintype.card (Line (Fin k) (Fin m0)))) →
    (∀ B : Finset (Word k m0), delta0 / 4 ≤ density B →
      ContainsLine (B : Set (Word k m0))) →
    ∃ n : ℕ, ∀ A : Finset (Word (k + 1) n),
      delta0 ≤ density A →
      ¬ContainsLine (A : Set (Word (k + 1) n)) →
      ∃ W : Subspace (Fin m) (Fin (k + 1)) (Fin n),
      ∃ D : Fin k → Finset (Word (k + 1) m),
        (∀ i, IsLastInsensitive i (D i : Set (Word (k + 1) m))) ∧
        IncrementArithmetic.gamma delta0
            (IncrementArithmetic.eta delta0
              (IncrementArithmetic.theta delta0
                (Fintype.card (Line (Fin k) (Fin m0))))) k <
          density (familyInter D) ∧
        (density A + IncrementArithmetic.gamma delta0
            (IncrementArithmetic.eta delta0
              (IncrementArithmetic.theta delta0
                (Fintype.card (Line (Fin k) (Fin m0))))) k) *
            density (familyInter D) <
          density (pullbackFinset W A ∩ familyInter D)

/-- Abstract lower-bound-preserving interface of DKT Lemma 12. -/
def EventualOneInsensitiveTilingPrinciple : Prop :=
  ∀ (k : ℕ), 0 < k → FiniteDensityHJ k →
    ∀ beta : ℝ, 0 < beta →
    ∀ d N : ℕ, ∃ n, N ≤ n ∧ OneInsensitiveTilingAt k d n beta

/-- The uniform-correlation development supplies its abstract interface. -/
theorem uniformStructuredCorrelationPrinciple :
    UniformStructuredCorrelationPrinciple := by
  intro k m0 m hk hm0 hm0m delta0 hdelta0 hdelta0_one htheta
    htheta_one herror hface hDHJ
  exact UniformCorrelation.exists_structured_correlation_at
    k m0 m hk hm0 hm0m delta0 hdelta0 hdelta0_one htheta htheta_one
      herror hface hDHJ

/-- The greedy insensitive-tiling development supplies its abstract
lower-bound-preserving interface. -/
theorem eventualOneInsensitiveTilingPrinciple :
    EventualOneInsensitiveTilingPrinciple := by
  intro k hk hDHJ beta hbeta d N
  exact (hDHJ.finiteRestrictedMDHJ hk d).exists_oneInsensitiveTilingAt_ge
    hbeta N

/-- Choose the middle tiling dimension separately for every requested target
dimension, subject to a common lower bound, and only then choose the ambient
correlation dimension.  This is the quantifier order needed to combine face
decay with insensitive tiling. -/
noncomputable def densityIncrementStep_of_eventual_structured_tilings
    {k : ℕ} (hk : 2 ≤ k) {delta gamma : ℝ}
    (hgamma : 0 < gamma) (hgamma_two : gamma < 2) (base : ℕ)
    (htilingExists : ∀ d N, ∃ m, N ≤ m ∧
      InsensitiveIntersectionTilingAt k k d m
        (gamma ^ 2 / (4 * (k : ℝ))))
    (hstructuredExists : ∀ m, base ≤ m →
      ∃ n, StructuredIncrementAt k m n delta gamma) :
    DensityIncrementStep (k + 1) delta := by
  let middle : ℕ → ℕ := fun d ↦ (htilingExists d base).choose
  have hmiddle (d : ℕ) : base ≤ middle d :=
    (htilingExists d base).choose_spec.1
  have htiling (d : ℕ) :
      InsensitiveIntersectionTilingAt k k d (middle d)
        (gamma ^ 2 / (4 * (k : ℝ))) :=
    (htilingExists d base).choose_spec.2
  let threshold : ℕ → ℕ := fun d ↦
    (hstructuredExists (middle d) (hmiddle d)).choose
  have hstructured (d : ℕ) :
      StructuredIncrementAt k (middle d) (threshold d) delta gamma :=
    (hstructuredExists (middle d) (hmiddle d)).choose_spec
  exact densityIncrementStep_of_structured_tilings hk hgamma hgamma_two
    middle threshold (fun d ↦ hstructured d) htiling

/-- Complete parameter and dimension assembly from the two concrete DKT
principles.  All constants are frozen at the input lower density `delta`. -/
noncomputable def densityIncrementStep_of_DKT_principles
    (huniform : UniformStructuredCorrelationPrinciple)
    (hone : EventualOneInsensitiveTilingPrinciple)
    {k : ℕ} (hk : 2 ≤ k) (hDHJfinite : FiniteDensityHJ k)
    (delta : ℝ) (hdelta : 0 < delta) :
    DensityIncrementStep (k + 1) delta := by
  by_cases hlarge : 1 < delta
  · exact vacuousDensityIncrementStep hlarge
  have hdelta_one : delta ≤ 1 := le_of_not_gt hlarge
  let m0 :=
    (exists_frozen_DKT_parameters hk hDHJfinite hdelta hdelta_one).choose
  have hparameters :=
    (exists_frozen_DKT_parameters hk hDHJfinite hdelta hdelta_one).choose_spec
  have hm0 : 0 < m0 := hparameters.1
  have hDHJ0 : ∀ B : Finset (Word k m0), delta / 4 ≤ density B →
      ContainsLine (B : Set (Word k m0)) := hparameters.2.1
  let theta := IncrementArithmetic.theta delta
    (Fintype.card (Line (Fin k) (Fin m0)))
  let eta := IncrementArithmetic.eta delta theta
  let gamma := IncrementArithmetic.gamma delta eta k
  have htheta : 0 < theta := hparameters.2.2.1
  have htheta_one : theta ≤ 1 := hparameters.2.2.2.1
  have herror : eta ^ 2 / 2 ≤ delta / 2 := hparameters.2.2.2.2.1
  have heta : 0 < eta := hparameters.2.2.2.2.2.1
  have hgamma : 0 < gamma := hparameters.2.2.2.2.2.2.1
  have hgamma_two : gamma < 2 := hparameters.2.2.2.2.2.2.2
  let Mface := (eventually_density_liftFinset_univ_lt k heta).choose
  have hMface := (eventually_density_liftFinset_univ_lt k heta).choose_spec
  let base := max m0 Mface
  have hm0base : m0 ≤ base := Nat.le_max_left _ _
  have hMfacebase : Mface ≤ base := Nat.le_max_right _ _
  have hkpos : 0 < k := lt_of_lt_of_le (by omega) hk
  let beta : ℝ := gamma ^ 2 / (4 * (k : ℝ))
  have hbeta : 0 < beta := by
    dsimp only [beta]
    positivity
  have hone' : ∀ d N, ∃ n, N ≤ n ∧
      OneInsensitiveTilingAt k d n beta :=
    hone k hkpos hDHJfinite beta hbeta
  have htilingExists : ∀ d N, ∃ m, N ≤ m ∧
      InsensitiveIntersectionTilingAt k k d m beta :=
    exists_k_intersection_tiling_ge hkpos hbeta hone'
  have hstructuredExists : ∀ m, base ≤ m →
      ∃ n, StructuredIncrementAt k m n delta gamma := by
    intro m hbasem
    have hm0m : m0 ≤ m := hm0base.trans hbasem
    have hfacem : density
        (liftFinset (Finset.univ : Finset (Word k m))) < eta :=
      hMface m (hMfacebase.trans hbasem)
    let n := (huniform k m0 m hk hm0 hm0m delta hdelta hdelta_one
      htheta htheta_one herror hfacem hDHJ0).choose
    have hn := (huniform k m0 m hk hm0 hm0m delta hdelta hdelta_one
      htheta htheta_one herror hfacem hDHJ0).choose_spec
    refine ⟨n, ?_⟩
    intro A hA
    by_cases hline : ContainsLine (A : Set (Word (k + 1) n))
    · exact Or.inl hline
    · right
      obtain ⟨W, D, hDins, hDdense, hDcorr⟩ := hn A hA hline
      exact ⟨W, D, hDins, hDdense, by
        simpa only [iterationPullback_eq_pullbackFinset] using hDcorr⟩
  exact densityIncrementStep_of_eventual_structured_tilings hk hgamma
    hgamma_two base (by simpa only [beta] using htilingExists)
      hstructuredExists

/-- The unconditional DKT density-increment step from density
Hales--Jewett on the preceding alphabet. -/
noncomputable def densityIncrementStep_succ
    {k : ℕ} (hk : 2 ≤ k) (hDHJfinite : FiniteDensityHJ k)
    (delta : ℝ) (hdelta : 0 < delta) :
    DensityIncrementStep (k + 1) delta :=
  densityIncrementStep_of_DKT_principles
    uniformStructuredCorrelationPrinciple
    eventualOneInsensitiveTilingPrinciple hk hDHJfinite delta hdelta

/-- The density-increment hypothesis required by alphabet induction. -/
noncomputable def alphabetDensityIncrement :
    AlphabetDensityIncrementHypothesis :=
  fun k hk hDHJfinite delta hdelta ↦
    densityIncrementStep_succ hk hDHJfinite delta hdelta

end Erdos171
