/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos651.PohoataZakharovBridge
import ErdosProblems.Erdos651.ConvexCore
import ErdosProblems.Erdos651.FinalEstimates
import ErdosProblems.Erdos651.BinomialEnvelope
import ErdosProblems.Erdos651.CapAssembly
import ErdosProblems.Erdos651.CapRamsey
import ErdosProblems.Erdos651.FiniteRamsey
import ErdosProblems.Erdos651.PositiveFraction
import ErdosProblems.Erdos651.TwoSeparation
import ErdosProblems.Erdos651.HamSandwich
import ErdosProblems.Erdos651.AboveBelow
import ErdosProblems.Erdos651.TrihedralGadget

/-!
# The Pohoata--Zakharov assembly

This file assembles the geometric and numerical ingredients of the proof of
Pohoata--Zakharov, Theorem 1.1.  In particular, it keeps the cap-union step
and the conversion of the source's final envelope into the literal point-set
epsilon statement explicit.
-/

namespace Erdos651

open Filter Finset Set
open scoped BigOperators Topology

noncomputable section

/-! ## Lifting the planar positive-fraction configuration -/

/-- A Pór--Valtr configuration in a generic planar projection of `X`.
The actual spatial cells are the points of `X` whose images lie in the
corresponding planar cells. -/
structure LiftedPositiveFractionConfiguration
    (k : ℕ) (X : Finset (Point 3)) where
  projection : Point 3 →ᵃ[ℝ] Point 2
  projection_inj : Set.InjOn projection X
  planar : OrderedStrongPositiveFractionConfiguration k (X.image projection)

def LiftedPositiveFractionConfiguration.cell
    {k : ℕ} {X : Finset (Point 3)}
    (C : LiftedPositiveFractionConfiguration k X) (i : Fin k) :
    Finset (Point 3) :=
  X.filter fun x ↦ C.projection x ∈ C.planar.cell i

theorem LiftedPositiveFractionConfiguration.cell_subset
    {k : ℕ} {X : Finset (Point 3)}
    (C : LiftedPositiveFractionConfiguration k X) (i : Fin k) :
    C.cell i ⊆ X := by
  exact Finset.filter_subset _ _

theorem LiftedPositiveFractionConfiguration.image_cell
    {k : ℕ} {X : Finset (Point 3)}
    (C : LiftedPositiveFractionConfiguration k X) (i : Fin k) :
    (C.cell i).image C.projection = C.planar.cell i := by
  classical
  ext y
  constructor
  · intro hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact (Finset.mem_filter.mp hx).2
  · intro hy
    have hyambient := C.planar.cell_subset i hy
    obtain ⟨x, hxX, hxy⟩ := Finset.mem_image.mp hyambient
    subst y
    exact Finset.mem_image.2 ⟨x, Finset.mem_filter.2 ⟨hxX, hy⟩, rfl⟩

theorem LiftedPositiveFractionConfiguration.cell_card
    {k : ℕ} {X : Finset (Point 3)}
    (C : LiftedPositiveFractionConfiguration k X) (i : Fin k) :
    (C.cell i).card = (C.planar.cell i).card := by
  rw [← C.image_cell i, Finset.card_image_of_injOn]
  exact C.projection_inj.mono (C.cell_subset i)

theorem LiftedPositiveFractionConfiguration.cell_disjoint
    {k : ℕ} {X : Finset (Point 3)}
    (C : LiftedPositiveFractionConfiguration k X) :
    PairwiseDisjointClusters C.cell := by
  intro i j hij
  rw [Finset.disjoint_left]
  intro x hxi hxj
  have hpi : C.projection x ∈ C.planar.cell i :=
    (Finset.mem_filter.mp hxi).2
  have hpj : C.projection x ∈ C.planar.cell j :=
    (Finset.mem_filter.mp hxj).2
  exact Finset.disjoint_left.mp (C.planar.cell_disjoint hij) hpi hpj

theorem LiftedPositiveFractionConfiguration.cell_density
    {k : ℕ} {X : Finset (Point 3)}
    (C : LiftedPositiveFractionConfiguration k X) (i : Fin k) :
    X.card ≤ 2 ^ (40 * k) * (C.cell i).card := by
  have hambient : (X.image C.projection).card = X.card :=
    Finset.card_image_of_injOn C.projection_inj
  simpa [HasPositiveFractionDensity, hambient, C.cell_card i] using
    C.planar.cell_dense i

theorem LiftedPositiveFractionConfiguration.allCells_subset
    {k : ℕ} {X : Finset (Point 3)}
    (C : LiftedPositiveFractionConfiguration k X) :
    allClusters C.cell ⊆ X := by
  intro x hx
  rw [mem_allClusters_iff] at hx
  exact C.cell_subset hx.choose hx.choose_spec

/-- Every spatial transversal is convex because its injective affine image
is one of the robust planar transversals. -/
theorem LiftedPositiveFractionConfiguration.transversal_convex
    {k : ℕ} {X : Finset (Point 3)}
    (C : LiftedPositiveFractionConfiguration k X)
    (p : Fin k → Point 3) (hp : IsClusterTransversal C.cell p) :
    InConvexPosition (Finset.univ.image p) := by
  let q : Fin k → Point 2 := fun i ↦ C.projection (p i)
  have hq : ∀ i, q i ∈ C.planar.cell i := by
    intro i
    exact (Finset.mem_filter.mp (hp i)).2
  have hqconv := C.planar.transversal_convex q hq
  have hsub : Finset.univ.image p ⊆ X := by
    intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    exact C.cell_subset i (hp i)
  have himage : (Finset.univ.image p).image C.projection =
      Finset.univ.image q := by
    ext y
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨p i, ⟨i, rfl⟩, rfl⟩
  apply InConvexPosition.of_image_affineMap C.projection
    (C.projection_inj.mono hsub)
  simpa only [himage] using hqconv

theorem LiftedPositiveFractionConfiguration.image_clusterUnion
    {k : ℕ} {X : Finset (Point 3)}
    (C : LiftedPositiveFractionConfiguration k X) (I : Finset (Fin k)) :
    (clusterUnion C.cell I).image C.projection =
      planarClusterUnion C.planar.cell I := by
  classical
  ext y
  simp only [clusterUnion, planarClusterUnion, Finset.mem_image,
    Finset.mem_biUnion]
  constructor
  · rintro ⟨x, ⟨i, hiI, hxi⟩, rfl⟩
    exact ⟨i, hiI, by
      rw [← C.image_cell i]
      exact Finset.mem_image_of_mem C.projection hxi⟩
  · rintro ⟨i, hiI, hyi⟩
    rw [← C.image_cell i] at hyi
    obtain ⟨x, hxi, rfl⟩ := Finset.mem_image.mp hyi
    exact ⟨x, ⟨i, hiI, hxi⟩, rfl⟩

/-- Whole-cell strong convex position also lifts through the generic affine
projection. -/
theorem LiftedPositiveFractionConfiguration.strong_convex :
    {k : ℕ} → {X : Finset (Point 3)} →
    (C : LiftedPositiveFractionConfiguration k X) →
    StrongConvexPositionClusters C.cell := by
  intro k X C i
  rw [Set.disjoint_left]
  intro z hzi hzother
  have hzpi : C.projection z ∈
      convexHull ℝ ((C.planar.cell i : Finset (Point 2)) : Set (Point 2)) := by
    rw [← C.image_cell i, Finset.coe_image, ← C.projection.image_convexHull]
    exact ⟨z, hzi, rfl⟩
  have hzpother : C.projection z ∈
      convexHull ℝ
        ((planarClusterUnion C.planar.cell (Finset.univ.erase i) :
          Finset (Point 2)) : Set (Point 2)) := by
    rw [← C.image_clusterUnion (Finset.univ.erase i), Finset.coe_image,
      ← C.projection.image_convexHull]
    exact ⟨z, hzother, rfl⟩
  exact Set.disjoint_left.1 (C.planar.strong_convex i) hzpi hzpother

theorem exists_liftedPositiveFractionConfiguration
    {k : ℕ} (hk : 4 ≤ k) {X : Finset (Point 3)}
    (hproj : Set.InjOn verticalProjection X)
    (hcard : 2 ^ (40 * k) ≤ X.card)
    (hgp : InGeneralPosition 2 (X.image verticalProjection)) :
    Nonempty (LiftedPositiveFractionConfiguration k X) := by
  have himagecard : (X.image verticalProjection).card = X.card :=
    Finset.card_image_of_injOn hproj
  obtain ⟨C⟩ := exists_orderedStrongPositiveFractionConfiguration k hk
    (X.image verticalProjection) (by simpa only [himagecard] using hcard) hgp
  exact ⟨⟨verticalProjection, hproj, C⟩⟩

/-- The output after Proposition 2.5, retaining the source-correct strong
convexity and the exact combined density loss. -/
structure SeparatedPositiveFractionClusters
    (k : ℕ) (X : Finset (Point 3)) where
  source : LiftedPositiveFractionConfiguration k X
  cluster : Fin k → Finset (Point 3)
  cluster_subset_source : ∀ i, cluster i ⊆ source.cell i
  twoSeparated : TwoSeparatedClusters cluster
  strongConvex : StrongConvexPositionClusters cluster
  density : ∀ i,
    X.card ≤ 2 ^ (40 * k + k ^ 3) * (cluster i).card
  nonempty : ∀ i, (cluster i).Nonempty

theorem exists_separatedPositiveFractionClusters
    {k : ℕ} {X : Finset (Point 3)}
    (C : LiftedPositiveFractionConfiguration k X)
    (hgp : InGeneralPosition 3 X)
    (hlarge : 2 ^ (40 * k + k ^ 3) ≤ X.card) :
    Nonempty (SeparatedPositiveFractionClusters k X) := by
  have hcell : ∀ i, 2 ^ (k ^ 3) ≤ (C.cell i).card := by
    intro i
    have hmul : 2 ^ (40 * k) * 2 ^ (k ^ 3) ≤
        2 ^ (40 * k) * (C.cell i).card := by
      calc
        2 ^ (40 * k) * 2 ^ (k ^ 3) = 2 ^ (40 * k + k ^ 3) :=
          (pow_add 2 _ _).symm
        _ ≤ X.card := hlarge
        _ ≤ 2 ^ (40 * k) * (C.cell i).card := C.cell_density i
    exact Nat.le_of_mul_le_mul_left hmul (by positivity)
  have hallgp : InGeneralPosition 3 (allClusters C.cell) :=
    hgp.mono C.allCells_subset
  obtain ⟨Y, hYC, hYtwo, hYloss⟩ :=
    exists_twoSeparated_subclusters C.cell C.cell_disjoint hcell hallgp
  have hYstrong : StrongConvexPositionClusters Y :=
    C.strong_convex.mono hYC
  have hYdensity : ∀ i,
      X.card ≤ 2 ^ (40 * k + k ^ 3) * (Y i).card := by
    intro i
    calc
      X.card ≤ 2 ^ (40 * k) * (C.cell i).card := C.cell_density i
      _ ≤ 2 ^ (40 * k) * (2 ^ (k ^ 3) * (Y i).card) :=
        Nat.mul_le_mul_left _ (hYloss i)
      _ = 2 ^ (40 * k + k ^ 3) * (Y i).card := by
        rw [pow_add]
        ring
  have hYne : ∀ i, (Y i).Nonempty := by
    intro i
    rw [Finset.nonempty_iff_ne_empty]
    intro hi
    have hd := hYdensity i
    rw [hi] at hd
    simp at hd
    have : 0 < X.card := lt_of_lt_of_le (by positivity) hlarge
    omega
  exact ⟨{
    source := C
    cluster := Y
    cluster_subset_source := hYC
    twoSeparated := hYtwo
    strongConvex := hYstrong
    density := hYdensity
    nonempty := hYne }⟩

def SeparatedPositiveFractionClusters.representative
    {k : ℕ} {X : Finset (Point 3)}
    (C : SeparatedPositiveFractionClusters k X) (i : Fin k) : Point 3 :=
  (C.cluster i).choose (C.nonempty i)

theorem SeparatedPositiveFractionClusters.representative_mem
    {k : ℕ} {X : Finset (Point 3)}
    (C : SeparatedPositiveFractionClusters k X) :
    IsClusterTransversal C.cluster C.representative := by
  intro i
  exact (C.cluster i).choose_spec (C.nonempty i)

theorem SeparatedPositiveFractionClusters.representative_projection_mem
    {k : ℕ} {X : Finset (Point 3)}
    (C : SeparatedPositiveFractionClusters k X) (i : Fin k) :
    verticalProjection (C.representative i) ∈ C.source.planar.cell i := by
  exact (Finset.mem_filter.mp
    (C.cluster_subset_source i (C.representative_mem i))).2

theorem SeparatedPositiveFractionClusters.representative_injective
    {k : ℕ} {X : Finset (Point 3)}
    (C : SeparatedPositiveFractionClusters k X) :
    Function.Injective C.representative := by
  intro i j hij
  by_contra hne
  have hdisj := C.strongConvex.pairwiseDisjoint hne
  exact Finset.disjoint_left.mp hdisj (C.representative_mem i)
    (hij ▸ C.representative_mem j)

/-- A convenient general-position consequence for an explicitly indexed
four-tuple. -/
theorem affineIndependent_fin_four_of_generalPosition
    {U : Finset (Point 3)} (hUcard : 4 ≤ U.card)
    (hgp : InGeneralPosition 3 U) (p : Fin 4 → Point 3)
    (hpU : ∀ i, p i ∈ U) (hpinj : Function.Injective p) :
    AffineIndependent ℝ p := by
  classical
  let A := Finset.univ.image p
  have hAU : A ⊆ U := by
    intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    exact hpU i
  have hAcard : A.card ≤ 4 := by
    simpa [A] using Finset.card_image_le (s := (Finset.univ : Finset (Fin 4))) p
  have hAind : AffineIndependent ℝ (fun x : A ↦ (x : Point 3)) :=
    affineIndependent_of_subset_of_card_le_four hUcard hgp hAU hAcard
  let e : Fin 4 ↪ A :=
    ⟨fun i ↦ ⟨p i, Finset.mem_image.2 ⟨i, Finset.mem_univ i, rfl⟩⟩,
      fun i j hij ↦ hpinj (congrArg Subtype.val hij)⟩
  convert hAind.comp_embedding e using 1
  funext i
  rfl

theorem SeparatedPositiveFractionClusters.representative_four_independent
    {k : ℕ} {X : Finset (Point 3)}
    (C : SeparatedPositiveFractionClusters k X)
    (hXcard : 4 ≤ X.card) (hgp : InGeneralPosition 3 X)
    (i₀ i₁ i₂ i₃ : Fin k)
    (h₀₁ : i₀ < i₁) (h₁₂ : i₁ < i₂) (h₂₃ : i₂ < i₃) :
    AffineIndependent ℝ ![C.representative i₀, C.representative i₁,
      C.representative i₂, C.representative i₃] := by
  let f : Fin 4 → Fin k := ![i₀, i₁, i₂, i₃]
  have hfinj : Function.Injective f := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [f] <;> omega
  apply affineIndependent_fin_four_of_generalPosition hXcard hgp
  · intro i
    exact C.source.cell_subset (f i)
      (C.cluster_subset_source (f i) (C.representative_mem (f i)))
  · exact C.representative_injective.comp hfinj

/-! ## Reindexing a selected ordered subfamily -/

def reindexClusters {k m : ℕ} (X : Fin k → Finset (Point 3))
    (e : Fin m ↪ Fin k) : Fin m → Finset (Point 3) :=
  fun i ↦ X (e i)

theorem TwoSeparatedClusters.reindex {k m : ℕ}
    {X : Fin k → Finset (Point 3)} (hX : TwoSeparatedClusters X)
    (e : Fin m ↪ Fin k) : TwoSeparatedClusters (reindexClusters X e) := by
  intro i j i' j' hij hi'j' hpairs
  apply hX (e.injective.ne hij) (e.injective.ne hi'j')
  simpa using (Finset.disjoint_map e).mpr hpairs

theorem StrongConvexPositionClusters.reindex {k m : ℕ}
    {X : Fin k → Finset (Point 3)} (hX : StrongConvexPositionClusters X)
    (e : Fin m ↪ Fin k) :
    StrongConvexPositionClusters (reindexClusters X e) := by
  classical
  intro i
  apply (hX (e i)).mono_right
  apply convexHull_mono
  intro x hx
  simp only [clusterUnion, Finset.mem_coe, Finset.mem_biUnion] at hx ⊢
  obtain ⟨j, hj, hxj⟩ := hx
  refine ⟨e j, ?_, hxj⟩
  simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hj ⊢
  exact e.injective.ne hj

theorem IsProjectedConvexChain.reindex_univ {k m : ℕ}
    {x : Fin k → Point 3} (hchain : IsProjectedConvexChain x Finset.univ)
    (e : Fin m ↪o Fin k) :
    IsProjectedConvexChain (fun i ↦ x (e i)) Finset.univ := by
  intro i₀ _ i₁ _ i₂ _ i₃ _ h₀₁ h₁₂ h₂₃
  exact hchain (e i₀) (Finset.mem_univ _) (e i₁) (Finset.mem_univ _)
    (e i₂) (Finset.mem_univ _) (e i₃) (Finset.mem_univ _)
    (e.lt_iff_lt.mpr h₀₁) (e.lt_iff_lt.mpr h₁₂) (e.lt_iff_lt.mpr h₂₃)

theorem UniformAboveBelowOn.reindex_orderEmbOfFin
    {k m : ℕ} {x : Fin k → Point 3} {H : Finset (Fin k)}
    (huniform : UniformAboveBelowOn x H) (hHcard : H.card = m) :
    UniformAboveBelowOn
      (fun i ↦ x (H.orderEmbOfFin hHcard i)) Finset.univ := by
  let e : Fin m ↪o Fin k := H.orderEmbOfFin hHcard
  rcases huniform with habove | hbelow
  · left
    intro i₀ _ i₁ _ i₂ _ i₃ _ h₀₁ h₁₂ h₂₃
    exact habove (e i₀) (H.orderEmbOfFin_mem hHcard i₀)
      (e i₁) (H.orderEmbOfFin_mem hHcard i₁)
      (e i₂) (H.orderEmbOfFin_mem hHcard i₂)
      (e i₃) (H.orderEmbOfFin_mem hHcard i₃)
      (e.lt_iff_lt.mpr h₀₁) (e.lt_iff_lt.mpr h₁₂) (e.lt_iff_lt.mpr h₂₃)
  · right
    intro i₀ _ i₁ _ i₂ _ i₃ _ h₀₁ h₁₂ h₂₃
    exact hbelow (e i₀) (H.orderEmbOfFin_mem hHcard i₀)
      (e i₁) (H.orderEmbOfFin_mem hHcard i₁)
      (e i₂) (H.orderEmbOfFin_mem hHcard i₂)
      (e i₃) (H.orderEmbOfFin_mem hHcard i₃)
      (e.lt_iff_lt.mpr h₀₁) (e.lt_iff_lt.mpr h₁₂) (e.lt_iff_lt.mpr h₂₃)

/-- The positive-fraction clusters after the four-uniform Ramsey selection,
reindexed in their inherited order. -/
structure UniformSeparatedClusters
    (k m : ℕ) (X : Finset (Point 3)) where
  cluster : Fin m → Finset (Point 3)
  representative : Fin m → Point 3
  cluster_subset : ∀ i, cluster i ⊆ X
  representative_mem : IsClusterTransversal cluster representative
  nonempty : ∀ i, (cluster i).Nonempty
  twoSeparated : TwoSeparatedClusters cluster
  strongConvex : StrongConvexPositionClusters cluster
  density : ∀ i,
    X.card ≤ 2 ^ (40 * k + k ^ 3) * (cluster i).card
  projectedChain : IsProjectedConvexChain representative Finset.univ
  uniformAboveBelow : UniformAboveBelowOn representative Finset.univ

/-- Select and order a uniform above/below subfamily.  The density exponent
is kept as the original positive-fraction parameter `k`; the later assembly
will instantiate `k = pzQuarterRoot n`. -/
def SeparatedPositiveFractionClusters.selectUniform
    {k m : ℕ} {X : Finset (Point 3)}
    (C : SeparatedPositiveFractionClusters k X)
    (H : Finset (Fin k)) (hHcard : H.card = m)
    (hchain : IsProjectedConvexChain C.representative Finset.univ)
    (huniform : UniformAboveBelowOn C.representative H) :
    UniformSeparatedClusters k m X where
  cluster := reindexClusters C.cluster (H.orderEmbOfFin hHcard).toEmbedding
  representative := fun i ↦ C.representative (H.orderEmbOfFin hHcard i)
  cluster_subset := fun i ↦
    (C.cluster_subset_source _).trans (C.source.cell_subset _)
  representative_mem := fun i ↦ C.representative_mem _
  nonempty := fun i ↦ C.nonempty _
  twoSeparated := C.twoSeparated.reindex _
  strongConvex := C.strongConvex.reindex _
  density := fun i ↦ by
    simpa only using C.density (H.orderEmbOfFin hHcard i)
  projectedChain := hchain.reindex_univ (H.orderEmbOfFin hHcard)
  uniformAboveBelow := huniform.reindex_orderEmbOfFin hHcard

def finCastSuccOrderEmb (k : ℕ) : Fin k ↪o Fin (k + 1) where
  toFun := Fin.castSucc
  inj' := Fin.castSucc_injective
  map_rel_iff' := by simp

def extendFinPoint {k : ℕ} (x : Fin k → Point 3) : Fin (k + 1) → Point 3 :=
  fun i ↦ if hi : i.1 < k then x ⟨i.1, hi⟩ else 0

@[simp] theorem extendFinPoint_castSucc {k : ℕ} (x : Fin k → Point 3)
    (i : Fin k) : extendFinPoint x (Fin.castSucc i) = x i := by
  simp [extendFinPoint]

/-- Corollary 2.4 in the exact half-open convention used by Proposition
3.1.  Passing from `Fin k` to `Fin (k+1)` supplies the cut immediately after
`j₃`, including when `j₃` is the final index. -/
theorem trihedral_representative_hulls_disjoint
    {k : ℕ} (x : Fin k → Point 3) (hcard : 5 ≤ k)
    (hchain : IsProjectedConvexChain x Finset.univ)
    (huniform : UniformAboveBelowOn x Finset.univ)
    (j₁ j₂ j₃ : Fin k) (h₁₂ : j₁ < j₂) (h₂₃ : j₂ < j₃) :
    Disjoint
      (convexHull ℝ
        ((firstTrihedralIndices j₁ j₂ j₃).image x : Set (Point 3)))
      (convexHull ℝ
        (((secondTrihedralIndices j₁ j₂ j₃ ∪ {j₂}).image x) :
          Set (Point 3))) ∧
    Disjoint
      (convexHull ℝ
        (((firstTrihedralIndices j₁ j₂ j₃ ∪ {j₂}).image x) :
          Set (Point 3)))
      (convexHull ℝ
        ((secondTrihedralIndices j₁ j₂ j₃).image x : Set (Point 3))) := by
  classical
  let e : Fin k ↪o Fin (k + 1) := finCastSuccOrderEmb k
  let S : Finset (Fin (k + 1)) := Finset.univ.map e.toEmbedding
  let x' : Fin (k + 1) → Point 3 := extendFinPoint x
  have hx' (i : Fin k) : x' (e i) = x i := by
    simp [x', e, finCastSuccOrderEmb]
  have hScard : S.card = k := by simp [S]
  have hchain' : IsProjectedConvexChain x' S := by
    intro i₀ hi₀ i₁ hi₁ i₂ hi₂ i₃ hi₃ h₀₁ h₁₂' h₂₃'
    obtain ⟨q₀, -, rfl⟩ := Finset.mem_map.mp hi₀
    obtain ⟨q₁, -, rfl⟩ := Finset.mem_map.mp hi₁
    obtain ⟨q₂, -, rfl⟩ := Finset.mem_map.mp hi₂
    obtain ⟨q₃, -, rfl⟩ := Finset.mem_map.mp hi₃
    simpa only [hx'] using hchain q₀ (Finset.mem_univ _) q₁ (Finset.mem_univ _)
      q₂ (Finset.mem_univ _) q₃ (Finset.mem_univ _)
      (e.lt_iff_lt.mp h₀₁) (e.lt_iff_lt.mp h₁₂') (e.lt_iff_lt.mp h₂₃')
  have huniform' : UniformAboveBelowOn x' S := by
    rcases huniform with habove | hbelow
    · left
      intro i₀ hi₀ i₁ hi₁ i₂ hi₂ i₃ hi₃ h₀₁ h₁₂' h₂₃'
      obtain ⟨q₀, -, rfl⟩ := Finset.mem_map.mp hi₀
      obtain ⟨q₁, -, rfl⟩ := Finset.mem_map.mp hi₁
      obtain ⟨q₂, -, rfl⟩ := Finset.mem_map.mp hi₂
      obtain ⟨q₃, -, rfl⟩ := Finset.mem_map.mp hi₃
      simpa only [hx'] using habove q₀ (Finset.mem_univ _) q₁ (Finset.mem_univ _)
        q₂ (Finset.mem_univ _) q₃ (Finset.mem_univ _)
        (e.lt_iff_lt.mp h₀₁) (e.lt_iff_lt.mp h₁₂') (e.lt_iff_lt.mp h₂₃')
    · right
      intro i₀ hi₀ i₁ hi₁ i₂ hi₂ i₃ hi₃ h₀₁ h₁₂' h₂₃'
      obtain ⟨q₀, -, rfl⟩ := Finset.mem_map.mp hi₀
      obtain ⟨q₁, -, rfl⟩ := Finset.mem_map.mp hi₁
      obtain ⟨q₂, -, rfl⟩ := Finset.mem_map.mp hi₂
      obtain ⟨q₃, -, rfl⟩ := Finset.mem_map.mp hi₃
      simpa only [hx'] using hbelow q₀ (Finset.mem_univ _) q₁ (Finset.mem_univ _)
        q₂ (Finset.mem_univ _) q₃ (Finset.mem_univ _)
        (e.lt_iff_lt.mp h₀₁) (e.lt_iff_lt.mp h₁₂') (e.lt_iff_lt.mp h₂₃')
  have blockImage (P : Fin k → Prop) [DecidablePred P]
      (P' : Fin (k + 1) → Prop)
      (hP : ∀ i : Fin k, P' (e i) ↔ P i) :
      (S.filter P').image x' = (Finset.univ.filter P).image x := by
    ext y
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_map,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨_, ⟨i, -, rfl⟩, hi, rfl⟩
      exact ⟨i, (hP i).mp hi, hx' i⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨e i, ⟨i, trivial, rfl⟩, (hP i).mpr hi, hx' i⟩
  have hfirst₁ :
      (firstAlternatingBlock S (e j₁) (Fin.succ j₂) (Fin.succ j₃)).image x' =
        (firstTrihedralIndices j₁ j₂ j₃).image x := by
    apply blockImage
    intro i
    simp only [e, finCastSuccOrderEmb, Fin.castSucc_mk, Fin.succ_mk]
    simp only [mem_firstTrihedralIndices]
    change (i.1 < j₁.1 ∨ (j₂.1 + 1 ≤ i.1 ∧ i.1 < j₃.1 + 1)) ↔
      (i.1 < j₁.1 ∨ (j₂.1 < i.1 ∧ i.1 ≤ j₃.1))
    omega
  have hsecond₁ :
      (secondAlternatingBlock S (e j₁) (Fin.succ j₂) (Fin.succ j₃)).image x' =
        (secondTrihedralIndices j₁ j₂ j₃ ∪ {j₂}).image x := by
    apply blockImage
    intro i
    simp only [e, finCastSuccOrderEmb, Fin.castSucc_mk, Fin.succ_mk]
    simp only [Finset.mem_union, mem_secondTrihedralIndices,
      Finset.mem_singleton]
    change ((j₁.1 ≤ i.1 ∧ i.1 < j₂.1 + 1) ∨ j₃.1 + 1 ≤ i.1) ↔
      (((j₁.1 ≤ i.1 ∧ i.1 < j₂.1) ∨ j₃.1 < i.1) ∨ i = j₂)
    constructor
    · intro hi
      rcases hi with hi | hi
      · by_cases hij : i = j₂
        · exact Or.inr hij
        · left; left; omega
      · left; right; omega
    · intro hi
      rcases hi with (hi | hi) | rfl
      · left; omega
      · right; omega
      · left; omega
  have hfirst₂ :
      (firstAlternatingBlock S (e j₁) (e j₂) (Fin.succ j₃)).image x' =
        (firstTrihedralIndices j₁ j₂ j₃ ∪ {j₂}).image x := by
    apply blockImage
    intro i
    simp only [e, finCastSuccOrderEmb, Fin.castSucc_mk, Fin.succ_mk]
    simp only [Finset.mem_union, mem_firstTrihedralIndices,
      Finset.mem_singleton]
    change (i.1 < j₁.1 ∨ (j₂.1 ≤ i.1 ∧ i.1 < j₃.1 + 1)) ↔
      ((i.1 < j₁.1 ∨ (j₂.1 < i.1 ∧ i.1 ≤ j₃.1)) ∨ i = j₂)
    constructor
    · intro hi
      rcases hi with hi | hi
      · exact Or.inl (Or.inl hi)
      · by_cases hij : i = j₂
        · exact Or.inr hij
        · left; right; omega
    · intro hi
      rcases hi with (hi | hi) | rfl
      · exact Or.inl hi
      · right; omega
      · right; omega
  have hsecond₂ :
      (secondAlternatingBlock S (e j₁) (e j₂) (Fin.succ j₃)).image x' =
        (secondTrihedralIndices j₁ j₂ j₃).image x := by
    apply blockImage
    intro i
    simp only [e, finCastSuccOrderEmb, Fin.castSucc_mk, Fin.succ_mk]
    simp only [mem_secondTrihedralIndices]
    change ((j₁.1 ≤ i.1 ∧ i.1 < j₂.1) ∨ j₃.1 + 1 ≤ i.1) ↔
      ((j₁.1 ≤ i.1 ∧ i.1 < j₂.1) ∨ j₃.1 < i.1)
    omega
  constructor
  · have h := alternatingBlock_hulls_disjoint x' S (e j₁) (Fin.succ j₂)
      (Fin.succ j₃) (by simpa only [hScard] using hcard)
      (by change j₁.1 ≤ j₂.1 + 1; omega) (by change j₂.1 + 1 ≤ j₃.1 + 1; omega)
      hchain' huniform'
    simpa only [hfirst₁, hsecond₁] using h
  · have h := alternatingBlock_hulls_disjoint x' S (e j₁) (e j₂)
      (Fin.succ j₃) (by simpa only [hScard] using hcard)
      (e.le_iff_le.mpr h₁₂.le) (by change j₂.1 ≤ j₃.1 + 1; omega)
      hchain' huniform'
    simpa only [hfirst₂, hsecond₂] using h

/-- Proposition 2.7 turns a strict separation of representative blocks into
the same separation for the unions of their full clusters. -/
theorem UniformSeparatedClusters.fullCluster_hulls_disjoint
    {k m : ℕ} {X : Finset (Point 3)}
    (C : UniformSeparatedClusters k m X)
    (A B : Finset (Fin m)) (hAB : A ∪ B = Finset.univ)
    (hAne : A.Nonempty) (hBne : B.Nonempty)
    (hrep : Disjoint
      (convexHull ℝ (A.image C.representative : Set (Point 3)))
      (convexHull ℝ (B.image C.representative : Set (Point 3)))) :
    Disjoint
      (convexHull ℝ (clusterUnion C.cluster A : Set (Point 3)))
      (convexHull ℝ (clusterUnion C.cluster B : Set (Point 3))) := by
  classical
  obtain ⟨f, c, hAneg, hBpos⟩ :=
    finite_sets_strictly_separated_point3
      (A.image C.representative) (B.image C.representative) hrep
  have hf : f ≠ 0 := by
    intro hf
    obtain ⟨i, hiA⟩ := hAne
    obtain ⟨j, hjB⟩ := hBne
    have hi := hAneg (C.representative i)
      (Finset.mem_image_of_mem C.representative hiA)
    have hj := hBpos (C.representative j)
      (Finset.mem_image_of_mem C.representative hjB)
    simp only [hf, map_zero] at hi hj
    linarith
  have hpattern : HasRepresentativePlanePattern C.representative f c := by
    refine ⟨hf, ?_⟩
    intro i
    have hi : i ∈ A ∪ B := by rw [hAB]; simp
    rcases Finset.mem_union.mp hi with hiA | hiB
    · have hlt := hAneg (C.representative i)
        (Finset.mem_image_of_mem C.representative hiA)
      dsimp [planeValue]
      linarith
    · have hgt := hBpos (C.representative i)
        (Finset.mem_image_of_mem C.representative hiB)
      dsimp [planeValue]
      linarith
  obtain ⟨g, d, hg, hlift⟩ :=
    liftsRepresentativePlanePattern_of_twoSeparated_of_strong
      C.twoSeparated C.strongConvex C.representative_mem hpattern
  have hAgen : (↑(clusterUnion C.cluster A) : Set (Point 3)) ⊆
      {y | g y < d} := by
    intro y hy
    simp only [clusterUnion, Finset.mem_coe, Finset.mem_biUnion] at hy
    obtain ⟨i, hiA, hyi⟩ := hy
    have hirep := hAneg (C.representative i)
      (Finset.mem_image_of_mem C.representative hiA)
    have := (hlift i y hyi).2 (by
      dsimp [planeValue]
      linarith)
    simpa [planeValue] using this
  have hBgen : (↑(clusterUnion C.cluster B) : Set (Point 3)) ⊆
      {y | d < g y} := by
    intro y hy
    simp only [clusterUnion, Finset.mem_coe, Finset.mem_biUnion] at hy
    obtain ⟨i, hiB, hyi⟩ := hy
    have hirep := hBpos (C.representative i)
      (Finset.mem_image_of_mem C.representative hiB)
    have := (hlift i y hyi).1 (by
      dsimp [planeValue]
      linarith)
    simpa [planeValue] using this
  rw [Set.disjoint_left]
  intro y hyA hyB
  have hyneg : g y < d :=
    convexHull_min hAgen (convex_halfSpace_lt g.isLinear d) hyA
  have hypos : d < g y :=
    convexHull_min hBgen (convex_halfSpace_gt g.isLinear d) hyB
  linarith

/-! ## Aligning a generic projection with the vertical coordinates -/

/-- The evident coordinate identification `(ℝ² × ℝ) ≃ₗ ℝ³`. -/
def pointTwoProdRealEquivPointThree :
    (Point 2 × ℝ) ≃ₗ[ℝ] Point 3 where
  toFun yz := WithLp.toLp 2 ![yz.1 0, yz.1 1, yz.2]
  invFun x := (WithLp.toLp 2 ![x 0, x 1], x 2)
  left_inv yz := by
    rcases yz with ⟨y, z⟩
    apply Prod.ext
    · apply PiLp.ext
      intro i
      fin_cases i <;> simp
    · simp
  right_inv x := by
    apply PiLp.ext
    intro i
    fin_cases i <;> simp
  map_add' x y := by
    apply PiLp.ext
    intro i
    fin_cases i <;> simp
  map_smul' c x := by
    apply PiLp.ext
    intro i
    fin_cases i <;> simp

@[simp] theorem verticalProjection_pointTwoProdRealEquivPointThree
    (y : Point 2 × ℝ) :
    verticalProjection (pointTwoProdRealEquivPointThree y) = y.1 := by
  apply PiLp.ext
  intro i
  fin_cases i <;> simp [verticalProjection, pointTwoProdRealEquivPointThree]

/-- Every surjective affine projection to the plane can be completed by one
linear coordinate to an affine coordinate system on `ℝ³`.  After this
change of coordinates it is literally `verticalProjection`, so all the
hard-coded above/below lemmas apply without changing their geometry. -/
theorem exists_affineEquiv_verticalProjection_eq_of_surjective
    (π : Point 3 →ᵃ[ℝ] Point 2) (hπ : Function.Surjective π.linear) :
    ∃ e : Point 3 ≃ᵃ[ℝ] Point 3,
      ∀ x, verticalProjection (e x) = π x := by
  classical
  let L : Point 3 →ₗ[ℝ] Point 2 := π.linear
  obtain ⟨g, hg⟩ :=
    L.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hπ)
  have hg' : Function.RightInverse g L := LinearMap.ext_iff.mp hg
  have hkerfin : Module.finrank ℝ (LinearMap.ker L) = 1 := by
    have hrank := L.finrank_range_add_finrank_ker
    have hrange : LinearMap.range L = ⊤ := LinearMap.range_eq_top.mpr hπ
    rw [hrange] at hrank
    have hdom : Module.finrank ℝ (Point 3) = 3 := by simp [Point]
    have hcod : Module.finrank ℝ (Point 2) = 2 := by simp [Point]
    rw [Submodule.finrank_top, hcod, hdom] at hrank
    omega
  let eK : LinearMap.ker L ≃ₗ[ℝ] ℝ := LinearEquiv.ofFinrankEq (by
    rw [hkerfin]
    simp)
  let D : Point 3 ≃ₗ[ℝ] (Point 2 × ℝ) :=
    { toFun := fun x ↦
        (L x, eK ⟨x - g (L x), by
          change L (x - g (L x)) = 0
          rw [map_sub, hg' (L x), sub_self]⟩)
      invFun := fun yz ↦ g yz.1 + (eK.symm yz.2).1
      left_inv := by
        intro x
        have heK : (eK.symm (eK ⟨x - g (L x), by
            change L (x - g (L x)) = 0
            rw [map_sub, hg' (L x), sub_self]⟩ : LinearMap.ker L)).1 =
            x - g (L x) := by
          exact congrArg Subtype.val (eK.symm_apply_apply _)
        simp only [heK]
        abel
      right_inv := by
        intro yz
        apply Prod.ext
        · simp only [map_add, hg', Submodule.coe_mem, map_zero, add_zero]
        · apply eK.symm.injective
          apply Subtype.ext
          simp only [map_add, hg', Submodule.coe_mem, map_zero, add_zero,
            eK.symm_apply_apply]
          abel
      map_add' := by
        intro x y
        apply Prod.ext
        · simp
        · apply eK.symm.injective
          apply Subtype.ext
          simp
          abel
      map_smul' := by
        intro c x
        apply Prod.ext
        · simp
        · apply eK.symm.injective
          apply Subtype.ext
          simp }
  let E : Point 3 ≃ₗ[ℝ] Point 3 :=
    D.trans pointTwoProdRealEquivPointThree
  let shift : Point 3 := pointTwoProdRealEquivPointThree (π 0, 0)
  let e : Point 3 ≃ᵃ[ℝ] Point 3 :=
    E.toAffineEquiv.trans (AffineEquiv.constVAdd ℝ (Point 3) shift)
  refine ⟨e, ?_⟩
  intro x
  apply PiLp.ext
  intro i
  have hlinear := congrArg (fun y : Point 2 ↦ y i)
    (π.linearMap_vsub x 0)
  fin_cases i
  · simpa [e, E, shift, D, L, verticalProjection,
      pointTwoProdRealEquivPointThree, vsub_eq_sub] using hlinear
  · simpa [e, E, shift, D, L, verticalProjection,
      pointTwoProdRealEquivPointThree, vsub_eq_sub] using hlinear

/-- Three noncollinear values force the linear part of a planar affine map
to be onto. -/
theorem affineProjection_linear_surjective_of_image_generalPosition
    {X : Finset (Point 3)} (π : Point 3 →ᵃ[ℝ] Point 2)
    (hπinj : Set.InjOn π X) (hXcard : 3 ≤ X.card)
    (hgp : InGeneralPosition 2 (X.image π)) :
    Function.Surjective π.linear := by
  classical
  have himagecard : (X.image π).card = X.card :=
    Finset.card_image_of_injOn hπinj
  obtain ⟨T, hTsub, hTcard⟩ :=
    Finset.exists_subset_card_eq (show 3 ≤ (X.image π).card by
      simpa [himagecard] using hXcard)
  have hAI : AffineIndependent ℝ (fun y : T ↦ (y : Point 2)) := by
    apply hgp T hTsub
    simpa using hTcard
  have hspan :
      vectorSpan ℝ (Set.range fun y : T ↦ (y : Point 2)) = ⊤ := by
    apply hAI.vectorSpan_eq_top_of_card_eq_finrank_add_one
    simp [Point, hTcard]
  have hTne : T.Nonempty := by rw [← Finset.card_pos, hTcard]; norm_num
  let a : T := ⟨T.choose hTne, T.choose_spec hTne⟩
  have hle : vectorSpan ℝ (Set.range fun y : T ↦ (y : Point 2)) ≤
      LinearMap.range π.linear := by
    rw [vectorSpan_eq_span_vsub_set_right ℝ (Set.mem_range_self a),
      Submodule.span_le]
    rintro v ⟨_, ⟨b, rfl⟩, rfl⟩
    have hbimage := hTsub b.property
    have haimage := hTsub a.property
    obtain ⟨xb, hxbX, hxbeq⟩ := Finset.mem_image.mp hbimage
    obtain ⟨xa, hxaX, hxaeq⟩ := Finset.mem_image.mp haimage
    refine ⟨xb - xa, ?_⟩
    have hv := π.linearMap_vsub xb xa
    simpa [vsub_eq_sub, hxbeq, hxaeq] using hv
  apply LinearMap.range_eq_top.mp
  apply top_unique
  rw [← hspan]
  exact hle

theorem inGeneralPosition_image_affineEquiv
    {d : ℕ} {X : Finset (Point d)} (hX : InGeneralPosition d X)
    (e : Point d ≃ᵃ[ℝ] Point d) :
    InGeneralPosition d (X.image e) := by
  apply InGeneralPosition.of_image_affineMap e.symm.toAffineMap
    e.symm.injective.injOn
  have hback : (X.image e).image e.symm = X := by
    ext x
    simp
  simpa only [hback] using hX

/-- Generic projection in the coordinate form needed by `AboveBelow`.
The affine equivalence is returned explicitly so the eventual convex subset
can be transported back to the original point set. -/
theorem exists_vertical_generic_affineEquiv
    {X : Finset (Point 3)} (hgp : InGeneralPosition 3 X)
    (hXcard : 4 ≤ X.card) :
    ∃ e : Point 3 ≃ᵃ[ℝ] Point 3,
      InGeneralPosition 3 (X.image e) ∧
      Set.InjOn verticalProjection (X.image e) ∧
      InGeneralPosition 2 ((X.image e).image verticalProjection) := by
  obtain ⟨π, hπinj, hπgp⟩ := exists_generic_plane_projection hgp hXcard
  have hπsurj : Function.Surjective π.linear :=
    affineProjection_linear_surjective_of_image_generalPosition π hπinj
      (by omega) hπgp
  obtain ⟨e, he⟩ :=
    exists_affineEquiv_verticalProjection_eq_of_surjective π hπsurj
  have himage : (X.image e).image verticalProjection = X.image π := by
    ext y
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨_, ⟨x, hxX, rfl⟩, rfl⟩
      exact ⟨x, hxX, (he x).symm⟩
    · rintro ⟨x, hxX, rfl⟩
      exact ⟨e x, ⟨x, hxX, rfl⟩, he x⟩
  refine ⟨e, inGeneralPosition_image_affineEquiv hgp e, ?_, ?_⟩

  · intro ex hex ey hey hxy
    obtain ⟨x, hxX, rfl⟩ := Finset.mem_image.mp hex
    obtain ⟨y, hyX, rfl⟩ := Finset.mem_image.mp hey
    apply congrArg e
    exact hπinj hxX hyX (by simpa only [he] using hxy)
  · simpa only [himage] using hπgp

/-! ## The exact rounding used for the alternating cap union -/

/-- There are `ceil(t/2)` alternating indices, and caps of cardinality
`ceil(2n/t)` therefore contribute at least `n` points. -/
theorem target_le_alternating_cap_count (n t : ℕ) (ht : 0 < t) :
    n ≤ ((t + 1) / 2) * ⌈(2 : ℝ) * n / t⌉₊ := by
  let a : ℕ := ⌈(2 : ℝ) * n / t⌉₊
  have htR : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  have hdiv : (2 : ℝ) * n / t ≤ (a : ℝ) := by
    exact Nat.le_ceil _
  have hmulR : (2 : ℝ) * n ≤ t * a := by
    simpa [mul_comm] using (div_le_iff₀ htR).mp hdiv
  have hmul : 2 * n ≤ t * a := by exact_mod_cast hmulR
  have htceil : t ≤ 2 * ((t + 1) / 2) := by omega
  have htwice : 2 * n ≤ 2 * (((t + 1) / 2) * a) := by
    calc
      2 * n ≤ t * a := hmul
      _ ≤ (2 * ((t + 1) / 2)) * a := Nat.mul_le_mul_right a htceil
      _ = 2 * (((t + 1) / 2) * a) := by ac_rfl
  change n ≤ ((t + 1) / 2) * a
  exact Nat.le_of_mul_le_mul_left htwice (by norm_num)

/-- Exact source-level cap assembly: `ceil(t/2)` disjoint caps, each of
size `ceil(2n/t)`, contain a convex `n`-set in the ambient set. -/
theorem containsConvexSubset_of_alternating_pCaps
    {n t : ℕ} (ht : 0 < t)
    (X : Finset (Point 3))
    (P : Fin ((t + 1) / 2) → Set (Point 3))
    (K : Fin ((t + 1) / 2) → Finset (Point 3))
    (hKX : ∀ i, K i ⊆ X)
    (hdisj : ((Finset.univ : Finset (Fin ((t + 1) / 2))) :
      Set (Fin ((t + 1) / 2))).PairwiseDisjoint K)
    (hcap : ∀ i, PCap (P i) (K i))
    (hothers : ∀ i j, i ≠ j → (↑(K j) : Set (Point 3)) ⊆ P i)
    (hKcard : ∀ i, (K i).card = ⌈(2 : ℝ) * n / t⌉₊) :
    ContainsConvexSubset 3 n X := by
  let U := (Finset.univ : Finset (Fin ((t + 1) / 2))).biUnion K
  have hUcard : U.card = ((t + 1) / 2) * ⌈(2 : ℝ) * n / t⌉₊ := by
    rw [show U.card = ∑ i : Fin ((t + 1) / 2), (K i).card by
      exact Finset.card_biUnion hdisj]
    simp only [hKcard, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    rfl
  have hconv : ContainsConvexSubset 3 n U := by
    apply containsConvexSubset_of_biUnion_pCaps P K hcap hothers
    rw [hUcard]
    exact target_le_alternating_cap_count n t ht
  obtain ⟨Y, hYU, hYcard, hYconv⟩ := hconv
  refine ⟨Y, ?_, hYcard, hYconv⟩
  intro y hy
  have hyU := hYU hy
  obtain ⟨i, -, hyi⟩ := Finset.mem_biUnion.mp hyU
  exact hKX i hyi

/-! ## Elementary binomial estimates -/

/-- The cube of the cups--caps binomial coefficient is bounded by the
corresponding power. -/
theorem choose_cube_le_pow (N a : ℕ) :
    (N.choose a) ^ 3 ≤ N ^ (3 * a) := by
  calc
    (N.choose a) ^ 3 ≤ (N ^ a) ^ 3 :=
      Nat.pow_le_pow_left (Nat.choose_le_pow N a) 3
    _ = N ^ (a * 3) := (pow_mul N a 3).symm
    _ = N ^ (3 * a) := by rw [mul_comm]

/-- If the upper argument of the binomial coefficient is itself bounded by
a power of a scale `t`, then the binomial cube has the required scale-power
form. -/
theorem choose_cube_le_scale_pow {N a t b : ℕ} (hN : N ≤ t ^ b) :
    (N.choose a) ^ 3 ≤ t ^ (b * (3 * a)) := by
  calc
    (N.choose a) ^ 3 ≤ N ^ (3 * a) := choose_cube_le_pow N a
    _ ≤ (t ^ b) ^ (3 * a) := Nat.pow_le_pow_left hN _
    _ = t ^ (b * (3 * a)) := (pow_mul t b (3 * a)).symm

/-- The rounded cups--caps coefficient is dominated by the cleaner
`choose (n+a) a` coefficient used in `BinomialEnvelope`. -/
theorem choose_cap_threshold_le_choose_add (n a : ℕ) (ha : 2 ≤ a) :
    Nat.choose (a + n - 4) (a - 2) ≤ Nat.choose (n + a) a := by
  let N := a + n - 4
  let b := a - 2
  have hstep₁ : Nat.choose N b ≤ Nat.choose (N + 1) (b + 1) := by
    rw [Nat.choose_succ_succ']
    omega
  have hstep₂ : Nat.choose (N + 1) (b + 1) ≤
      Nat.choose (N + 2) (b + 2) := by
    rw [show N + 2 = (N + 1) + 1 by omega,
      show b + 2 = (b + 1) + 1 by omega, Nat.choose_succ_succ']
    omega
  calc
    Nat.choose (a + n - 4) (a - 2) = Nat.choose N b := rfl
    _ ≤ Nat.choose (N + 1) (b + 1) := hstep₁
    _ ≤ Nat.choose (N + 2) (b + 2) := hstep₂
    _ = Nat.choose (N + 2) a := by congr 1 <;> omega
    _ ≤ Nat.choose (n + a) a := by
      apply Nat.choose_le_choose
      dsimp [N]
      omega

/-- The sixth power of the exact coefficient appearing in Proposition 2.1
is bounded by the explicit binomial envelope. -/
theorem choose_cap_threshold_pow_six_le_envelope
    (n t : ℕ) (hn : 0 < n) (ht : 3 ≤ t) (htn : t ≤ n)
    (ha : 2 ≤ pzCapSize n t) :
    ((Nat.choose (pzCapSize n t + n - 4) (pzCapSize n t - 2) : ℕ) : ℝ) ^ 6 ≤
      (t : ℝ) ^ ((36 : ℝ) * n / t) := by
  have hchoose := choose_cap_threshold_le_choose_add n (pzCapSize n t) ha
  calc
    ((Nat.choose (pzCapSize n t + n - 4) (pzCapSize n t - 2) : ℕ) : ℝ) ^ 6
        ≤ ((Nat.choose (n + pzCapSize n t) (pzCapSize n t) : ℕ) : ℝ) ^ 6 := by
          exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast hchoose) 6
    _ ≤ (t : ℝ) ^ ((36 : ℝ) * n / t) :=
      choose_add_pzCapSize_pow_six_le_envelope n t hn ht htn

/-! ## A concrete unbounded Ramsey-clique scale -/

/-- The largest clique size whose explicit `r`-uniform Ramsey bound fits
below `k`.  The `m = 0` disjunct makes the defining finite set nonempty. -/
def pzRamseyCliqueSizeFor (r k : ℕ) : ℕ :=
  ((Finset.range (k + 1)).filter fun m =>
    m = 0 ∨ uniformRamseySequence r m ≤ k).sup id

/-- The inverse triple-Ramsey scale. -/
def pzRamseyCliqueSize (k : ℕ) : ℕ :=
  pzRamseyCliqueSizeFor 3 k

theorem pzRamseyCliqueSizeFor_le (r k : ℕ) :
    pzRamseyCliqueSizeFor r k ≤ k := by
  apply Finset.sup_le
  intro m hm
  exact Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_filter.mp hm).1)

theorem pzRamseyCliqueSize_le (k : ℕ) : pzRamseyCliqueSize k ≤ k :=
  pzRamseyCliqueSizeFor_le 3 k

/-- A positive value of the inverse scale genuinely satisfies the explicit
Ramsey threshold (rather than coming from the adjoined zero). -/
theorem uniformRamseySequence_le_of_pzRamseyCliqueSizeFor_pos
    {r k : ℕ} (hk : 0 < pzRamseyCliqueSizeFor r k) :
    uniformRamseySequence r (pzRamseyCliqueSizeFor r k) ≤ k := by
  let S := (Finset.range (k + 1)).filter fun m =>
    m = 0 ∨ uniformRamseySequence r m ≤ k
  have hS : S.Nonempty := by
    refine ⟨0, ?_⟩
    simp [S]
  obtain ⟨m, hmS, hm⟩ := Finset.sup_mem_of_nonempty (f := id) hS
  have heq : m = pzRamseyCliqueSizeFor r k := by
    simpa [S, pzRamseyCliqueSizeFor] using hm
  have hmprop := (Finset.mem_filter.mp hmS).2
  rcases hmprop with rfl | hmle
  · simp [pzRamseyCliqueSizeFor] at hk
  · simpa only [heq] using hmle

theorem uniformRamseySequence_le_of_pzRamseyCliqueSize_pos
    {k : ℕ} (hk : 0 < pzRamseyCliqueSize k) :
    uniformRamseySequence 3 (pzRamseyCliqueSize k) ≤ k :=
  uniformRamseySequence_le_of_pzRamseyCliqueSizeFor_pos hk

/-- Every fixed clique size is eventually admitted by the inverse Ramsey
scale. -/
theorem eventually_le_pzRamseyCliqueSizeFor (r m : ℕ) :
    ∀ᶠ k : ℕ in atTop, m ≤ pzRamseyCliqueSizeFor r k := by
  filter_upwards [eventually_ge_atTop (max m (uniformRamseySequence r m))]
    with k hk
  apply Finset.le_sup (f := id)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨Nat.lt_succ_of_le ((le_max_left _ _).trans hk),
    Or.inr ((le_max_right _ _).trans hk)⟩

theorem eventually_le_pzRamseyCliqueSize (m : ℕ) :
    ∀ᶠ k : ℕ in atTop, m ≤ pzRamseyCliqueSize k :=
  eventually_le_pzRamseyCliqueSizeFor 3 m

/-- The inverse triple-Ramsey scale tends to infinity. -/
theorem pzRamseyCliqueSizeFor_tendsto_atTop (r : ℕ) :
    Tendsto (pzRamseyCliqueSizeFor r) atTop atTop := by
  rw [tendsto_atTop]
  exact eventually_le_pzRamseyCliqueSizeFor r

theorem pzRamseyCliqueSize_tendsto_atTop :
    Tendsto pzRamseyCliqueSize atTop atTop :=
  pzRamseyCliqueSizeFor_tendsto_atTop 3

/-- The size retained after the four-uniform above/below Ramsey step. -/
def pzAboveBelowScale (n : ℕ) : ℕ :=
  pzRamseyCliqueSizeFor 4 (pzQuarterRoot n)

theorem pzAboveBelowScale_tendsto_atTop :
    Tendsto pzAboveBelowScale atTop atTop :=
  (pzRamseyCliqueSizeFor_tendsto_atTop 4).comp pzQuarterRoot_tendsto_atTop

theorem pzAboveBelowScale_le_quarterRoot (n : ℕ) :
    pzAboveBelowScale n ≤ pzQuarterRoot n :=
  pzRamseyCliqueSizeFor_le 4 _

/-- The size of the clique retained after the final triple-Ramsey step. -/
def pzSourceCliqueSize (n : ℕ) : ℕ :=
  pzRamseyCliqueSize (pzAboveBelowScale n)

theorem pzSourceCliqueSize_tendsto_atTop :
    Tendsto pzSourceCliqueSize atTop atTop :=
  pzRamseyCliqueSize_tendsto_atTop.comp pzAboveBelowScale_tendsto_atTop

/-- The slowly growing scale used in the source envelope.  If the final
triple-Ramsey clique has size `m`, we retain its largest odd initial segment
`2q+1` and put `t=2q`.  Thus there are exactly
`q = (t+1)/2` alternating middle clusters, with no parity loss in the cap
count. -/
def pzSourceScale (n : ℕ) : ℕ :=
  2 * ((pzSourceCliqueSize n - 1) / 2)

theorem pzSourceScale_tendsto_atTop :
    Tendsto pzSourceScale atTop atTop := by
  rw [tendsto_atTop]
  intro b
  filter_upwards [pzSourceCliqueSize_tendsto_atTop.eventually_ge_atTop (b + 2)]
    with n hn
  dsimp [pzSourceScale]
  omega

theorem pzSourceScale_add_one_le_cliqueSize (n : ℕ) :
    pzSourceScale n + 1 ≤ pzSourceCliqueSize n := by
  dsimp [pzSourceScale]
  omega

theorem pzSourceScale_even (n : ℕ) : Even (pzSourceScale n) := by
  exact ⟨(pzSourceCliqueSize n - 1) / 2, by
    simp only [pzSourceScale]
    omega⟩

theorem pzSourceScale_le_quarterRoot (n : ℕ) :
    pzSourceScale n ≤ pzQuarterRoot n :=
  (Nat.le_of_lt_succ (pzSourceScale_add_one_le_cliqueSize n)).trans
    ((pzRamseyCliqueSize_le _).trans (pzAboveBelowScale_le_quarterRoot n))

/-- The integer fourth root has fourth power at most its argument. -/
theorem pzQuarterRoot_pow_four_le (n : ℕ) :
    pzQuarterRoot n ^ 4 ≤ n := by
  have hfloor : (pzQuarterRoot n : ℝ) ≤ (n : ℝ) ^ (1 / 4 : ℝ) := by
    exact Nat.floor_le (by positivity)
  have hpow : (pzQuarterRoot n : ℝ) ^ 4 ≤
      ((n : ℝ) ^ (1 / 4 : ℝ)) ^ 4 :=
    pow_le_pow_left₀ (by positivity) hfloor 4
  have hrpow : ((n : ℝ) ^ (1 / 4 : ℝ)) ^ 4 = (n : ℝ) := by
    convert Real.rpow_inv_natCast_pow (x := (n : ℝ)) (n := 4)
      (by positivity) (by norm_num) using 1 <;> norm_num
  exact_mod_cast hpow.trans_eq hrpow

/-- The positive-fraction and repeated-halving loss is absorbed by a
`t^(41 n/t)` factor.  This is the exact elementary comparison used in the
source: `t ≤ k₀`, `k₀⁴ ≤ n`, and eventually `2 ≤ t`. -/
theorem positiveFractionLoss_le_sourceEnvelope
    (n : ℕ) (ht : 2 ≤ pzSourceScale n) :
    ((2 ^ (40 * pzQuarterRoot n + pzQuarterRoot n ^ 3) : ℕ) : ℝ) ≤
      (pzSourceScale n : ℝ) ^
        ((41 : ℝ) * (n : ℝ) / (pzSourceScale n : ℝ)) := by
  let k := pzQuarterRoot n
  let t := pzSourceScale n
  have ht0 : 0 < t := by omega
  have htk : t ≤ k := pzSourceScale_le_quarterRoot n
  have hk0 : 0 < k := lt_of_lt_of_le (by omega) htk
  have hk4 : k ^ 4 ≤ n := pzQuarterRoot_pow_four_le n
  have htk3 : t * k ^ 3 ≤ n := by
    calc
      t * k ^ 3 ≤ k * k ^ 3 := Nat.mul_le_mul_right _ htk
      _ = k ^ 4 := by ring
      _ ≤ n := hk4
  have hk_le_k3 : k ≤ k ^ 3 := by
    simpa using Nat.pow_le_pow_right (show 1 ≤ k by omega)
      (show 1 ≤ 3 by omega)
  have hbasepow :
      (2 ^ (40 * k + k ^ 3) : ℕ) ≤ t ^ (40 * k + k ^ 3) :=
    Nat.pow_le_pow_left ht _
  have hexpR : ((40 * k + k ^ 3 : ℕ) : ℝ) ≤
      (41 : ℝ) * (n : ℝ) / (t : ℝ) := by
    have htR : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht0
    have hk3R : ((k ^ 3 : ℕ) : ℝ) ≤ (n : ℝ) / (t : ℝ) := by
      apply (le_div_iff₀ htR).2
      exact_mod_cast htk3
    have hkR : (k : ℝ) ≤ (k ^ 3 : ℕ) := by exact_mod_cast hk_le_k3
    push_cast
    nlinarith
  calc
    ((2 ^ (40 * pzQuarterRoot n + pzQuarterRoot n ^ 3) : ℕ) : ℝ)
        = ((2 ^ (40 * k + k ^ 3) : ℕ) : ℝ) := rfl
    _ ≤ ((t ^ (40 * k + k ^ 3) : ℕ) : ℝ) := by exact_mod_cast hbasepow
    _ = (t : ℝ) ^ ((40 * k + k ^ 3 : ℕ) : ℝ) := by
      rw [Real.rpow_natCast]
      norm_cast
    _ ≤ (t : ℝ) ^ ((41 : ℝ) * (n : ℝ) / (t : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast ht) hexpR

theorem two_le_pzCapSize {n t : ℕ} (ht : 0 < t) (htn : t ≤ n) :
    2 ≤ pzCapSize n t := by
  have htR : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  have htwo : (2 : ℝ) ≤ (2 : ℝ) * n / t := by
    rw [le_div_iff₀ htR]
    exact_mod_cast Nat.mul_le_mul_left 2 htn
  exact_mod_cast htwo.trans (pzCapSize_lower (n := n) ht)

/-- After the positive-fraction and `2`-separation losses and the two
square-root losses, the exact cap threshold is still bounded by a PZ
envelope.  The explicit constant is `41 + 36 = 77`. -/
theorem loss_mul_choose_cap_threshold_pow_six_le_sourceEnvelope
    (n : ℕ) (hn : 0 < n) (ht : 3 ≤ pzSourceScale n)
    (htn : pzSourceScale n ≤ n) :
    (((2 ^ (40 * pzQuarterRoot n + pzQuarterRoot n ^ 3)) *
        Nat.choose
          (pzCapSize n (pzSourceScale n) + n - 4)
          (pzCapSize n (pzSourceScale n) - 2) ^ 6 : ℕ) : ℝ) ≤
      (pzSourceScale n : ℝ) ^
        ((77 : ℝ) * (n : ℝ) / (pzSourceScale n : ℝ)) := by
  let t := pzSourceScale n
  have ht0 : 0 < t := by omega
  have hcap : 2 ≤ pzCapSize n t := two_le_pzCapSize ht0 htn
  have hloss := positiveFractionLoss_le_sourceEnvelope n (show 2 ≤ t by omega)
  have hchoose := choose_cap_threshold_pow_six_le_envelope n t hn ht htn hcap
  have htR : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht0
  calc
    (((2 ^ (40 * pzQuarterRoot n + pzQuarterRoot n ^ 3)) *
        Nat.choose (pzCapSize n (pzSourceScale n) + n - 4)
          (pzCapSize n (pzSourceScale n) - 2) ^ 6 : ℕ) : ℝ)
        = ((2 ^ (40 * pzQuarterRoot n + pzQuarterRoot n ^ 3) : ℕ) : ℝ) *
          ((Nat.choose (pzCapSize n t + n - 4)
            (pzCapSize n t - 2) : ℕ) : ℝ) ^ 6 := by
              simp only [Nat.cast_mul, Nat.cast_pow]
    _ ≤ t ^ ((41 : ℝ) * (n : ℝ) / t) *
          t ^ ((36 : ℝ) * (n : ℝ) / t) :=
      mul_le_mul hloss hchoose (by positivity) (by positivity)
    _ = t ^ ((77 : ℝ) * (n : ℝ) / t) := by
      rw [← Real.rpow_add htR]
      congr 1
      ring

theorem eventually_loss_mul_choose_cap_threshold_pow_six_le_sourceEnvelope :
    ∀ᶠ n : ℕ in atTop,
      (((2 ^ (40 * pzQuarterRoot n + pzQuarterRoot n ^ 3)) *
          Nat.choose
            (pzCapSize n (pzSourceScale n) + n - 4)
            (pzCapSize n (pzSourceScale n) - 2) ^ 6 : ℕ) : ℝ) ≤
        (pzSourceScale n : ℝ) ^
          ((77 : ℝ) * (n : ℝ) / (pzSourceScale n : ℝ)) := by
  filter_upwards [pzSourceScale_tendsto_atTop.eventually_ge_atTop 3]
    with n ht
  have hn : 0 < n := by
    have htk : pzSourceScale n ≤ pzQuarterRoot n :=
      pzSourceScale_le_quarterRoot n
    have hk4 := pzQuarterRoot_pow_four_le n
    omega
  have htn : pzSourceScale n ≤ n := by
    have htk : pzSourceScale n ≤ pzQuarterRoot n :=
      pzSourceScale_le_quarterRoot n
    have hk4 := pzQuarterRoot_pow_four_le n
    have hkpos : 0 < pzQuarterRoot n := lt_of_lt_of_le (by omega) htk
    have hk_le_four : pzQuarterRoot n ≤ pzQuarterRoot n ^ 4 := by
      simpa using Nat.pow_le_pow_right (show 1 ≤ pzQuarterRoot n by omega)
        (show 1 ≤ 4 by omega)
    exact htk.trans (hk_le_four.trans hk4)
  exact loss_mul_choose_cap_threshold_pow_six_le_sourceEnvelope n hn ht htn

/-! ## Eliminating the two square-root losses exactly -/

/-- Once the geometric construction has produced its alternating free
family, the density bound and the exact quadratic Dilworth bound turn the
strict source threshold into caps (or a direct convex set). -/
theorem AlternatingFreeFamily.containsConvexSubset_of_sourceThreshold
    {n t : ℕ} {X : Finset (Point 3)}
    (F : AlternatingFreeFamily ((t + 1) / 2) X)
    (hn : 2 ≤ n) (ht : 3 ≤ t) (htn : t ≤ n)
    (hdensity : ∀ i,
      X.card ≤ 2 ^ (40 * pzQuarterRoot n + pzQuarterRoot n ^ 3) *
        (F.middle i).card)
    (hthreshold :
      2 ^ (40 * pzQuarterRoot n + pzQuarterRoot n ^ 3) *
          Nat.choose (pzCapSize n t + n - 4) (pzCapSize n t - 2) ^ 6 <
        X.card) :
    ContainsConvexSubset 3 n X := by
  let a := pzCapSize n t
  let loss := 2 ^ (40 * pzQuarterRoot n + pzQuarterRoot n ^ 3)
  let B := Nat.choose (a + n - 4) (a - 2) ^ 3
  have ht0 : 0 < t := by omega
  have ha : 2 ≤ a := by
    exact two_le_pzCapSize ht0 htn
  apply F.containsConvexSubset ha hn (by
    simpa [a, pzCapSize] using target_le_alternating_cap_count n t ht0)
  intro i
  have hloss : 0 < loss := by simp [loss]
  have hthreshold' : loss * (B * B) < X.card := by
    have hpow : B * B =
        Nat.choose (a + n - 4) (a - 2) ^ 6 := by
      dsimp [B]
      rw [← pow_add]
    rw [hpow]
    simpa [loss, a] using hthreshold
  have hBBmiddle : B * B < (F.middle i).card := by
    apply Nat.lt_of_mul_lt_mul_left
    calc
      loss * (B * B) < X.card := hthreshold'
      _ ≤ loss * (F.middle i).card := by simpa [loss] using hdensity i
  by_contra hnot
  have hfreeB : (F.freeSet i).card ≤ B := Nat.le_of_not_gt hnot
  have hmiddleBB : (F.middle i).card ≤ B * B :=
    (F.middle_card_le_free_square i).trans
      (Nat.mul_le_mul hfreeB hfreeB)
  exact (Nat.not_lt_of_ge hmiddleBB) hBBmiddle

theorem AlternatingFreeFamily.containsConvexSubset_of_sourceEnvelope
    {n : ℕ} {X : Finset (Point 3)}
    (F : AlternatingFreeFamily ((pzSourceScale n + 1) / 2) X)
    (hn : 2 ≤ n) (ht : 3 ≤ pzSourceScale n)
    (htn : pzSourceScale n ≤ n)
    (hdensity : ∀ i,
      X.card ≤ 2 ^ (40 * pzQuarterRoot n + pzQuarterRoot n ^ 3) *
        (F.middle i).card)
    (hlarge :
      (pzSourceScale n : ℝ) ^
          ((77 : ℝ) * (n : ℝ) / (pzSourceScale n : ℝ)) <
        (X.card : ℝ)) :
    ContainsConvexSubset 3 n X := by
  have hbound := loss_mul_choose_cap_threshold_pow_six_le_sourceEnvelope
    n (by omega) ht htn
  have hthreshold :
      2 ^ (40 * pzQuarterRoot n + pzQuarterRoot n ^ 3) *
          Nat.choose
            (pzCapSize n (pzSourceScale n) + n - 4)
            (pzCapSize n (pzSourceScale n) - 2) ^ 6 < X.card := by
    exact_mod_cast hbound.trans_lt hlarge
  exact F.containsConvexSubset_of_sourceThreshold hn ht htn hdensity hthreshold

theorem eventually_uniformRamseySequence_aboveBelowScale_le_quarterRoot :
    ∀ᶠ n : ℕ in atTop,
      uniformRamseySequence 4 (pzAboveBelowScale n) ≤ pzQuarterRoot n := by
  filter_upwards [pzAboveBelowScale_tendsto_atTop.eventually_gt_atTop 0]
    with n hn
  exact uniformRamseySequence_le_of_pzRamseyCliqueSizeFor_pos hn

theorem eventually_uniformRamseySequence_sourceCliqueSize_le_quarterRoot :
    ∀ᶠ n : ℕ in atTop,
      uniformRamseySequence 3 (pzSourceCliqueSize n) ≤ pzQuarterRoot n := by
  filter_upwards [pzSourceCliqueSize_tendsto_atTop.eventually_gt_atTop 0]
    with n hn
  exact (uniformRamseySequence_le_of_pzRamseyCliqueSize_pos hn).trans
    (pzAboveBelowScale_le_quarterRoot n)

theorem eventually_uniformRamseySequence_sourceCliqueSize_le_aboveBelowScale :
    ∀ᶠ n : ℕ in atTop,
      uniformRamseySequence 3 (pzSourceCliqueSize n) ≤ pzAboveBelowScale n := by
  filter_upwards [pzSourceCliqueSize_tendsto_atTop.eventually_gt_atTop 0]
    with n hn
  exact uniformRamseySequence_le_of_pzRamseyCliqueSize_pos hn

/-- Triple Ramsey selection at the exact slowly growing source scale.  The
returned clique has the odd cardinality `t+1`; consequently its alternating
middle indices are indexed by `Fin ((t+1)/2)`. -/
theorem pzSourceScale_tripleRamsey
    {α : Type*} [DecidableEq α] (n : ℕ) (A : Finset α)
    (hscale : 0 < pzSourceScale n)
    (hcard : pzAboveBelowScale n ≤ A.card)
    (color : Finset α → Bool) :
    ∃ H : Finset α, H ⊆ A ∧ H.card = pzSourceScale n + 1 ∧
      MonochromaticOn 3 color H := by
  have hclique : 0 < pzSourceCliqueSize n := by
    have := pzSourceScale_add_one_le_cliqueSize n
    omega
  obtain ⟨H₀, hH₀A, hH₀card, hH₀mono⟩ :=
    uniformRamseySequence_spec 3 (pzSourceCliqueSize n) A
      ((uniformRamseySequence_le_of_pzRamseyCliqueSize_pos hclique).trans hcard)
      color
  have htarget : pzSourceScale n + 1 ≤ H₀.card := by
    rw [hH₀card]
    exact pzSourceScale_add_one_le_cliqueSize n
  obtain ⟨H, hHH₀, hHcard⟩ := Finset.exists_subset_card_eq htarget
  refine ⟨H, hHH₀.trans hH₀A, hHcard, ?_⟩
  rcases hH₀mono with ⟨b, hb⟩
  exact ⟨b, fun J hJ hJcard ↦ hb J (hJ.trans hHH₀) hJcard⟩

/-! ## The final source envelope -/

/-- The output of the cap-producing branch of the source argument. -/
structure AlternatingPCapFamily (n t : ℕ) (X : Finset (Point 3)) where
  background : Fin ((t + 1) / 2) → Set (Point 3)
  cap : Fin ((t + 1) / 2) → Finset (Point 3)
  cap_subset : ∀ i, cap i ⊆ X
  cap_disjoint : ((Finset.univ : Finset (Fin ((t + 1) / 2))) :
    Set (Fin ((t + 1) / 2))).PairwiseDisjoint cap
  isPCap : ∀ i, PCap (background i) (cap i)
  other_caps_subset : ∀ i j, i ≠ j →
    (↑(cap j) : Set (Point 3)) ⊆ background i
  cap_card : ∀ i, (cap i).card = ⌈(2 : ℝ) * n / t⌉₊

theorem AlternatingPCapFamily.containsConvexSubset
    {n t : ℕ} {X : Finset (Point 3)}
    (F : AlternatingPCapFamily n t X) (ht : 0 < t) :
    ContainsConvexSubset 3 n X :=
  containsConvexSubset_of_alternating_pCaps ht X F.background F.cap
    F.cap_subset F.cap_disjoint F.isPCap F.other_caps_subset F.cap_card

/-- The exact output expected from the finite geometric/combinatorial part
of the source proof.  Its scale is the size of the final monochromatic
triple clique. -/
private structure PohoataZakharovEnvelopeCertificate where
  scale : ℕ → ℕ
  constant : ℝ
  scale_tendsto : Tendsto scale atTop atTop
  forces_eventually : ∀ᶠ n : ℕ in atTop,
    ∀ X : Finset (Point 3), InGeneralPosition 3 X →
      (scale n : ℝ) ^ (constant * (n : ℝ) / (scale n : ℝ)) < (X.card : ℝ) →
      ContainsConvexSubset 3 n X

/-- Concrete constructor for the final envelope certificate.  Its premise is
kept local to the assembly: the two alternatives are exactly the direct
convex branch of Proposition 2.1 and the alternating cap family which is
discharged by `containsConvexSubset_of_alternating_pCaps`. -/
private theorem envelopeCertificate_of_capExtraction
    (C : ℝ)
    (hextract : ∀ᶠ n : ℕ in atTop,
      0 < pzSourceScale n ∧
      ∀ X : Finset (Point 3), InGeneralPosition 3 X →
        (pzSourceScale n : ℝ) ^
            (C * (n : ℝ) / (pzSourceScale n : ℝ)) < (X.card : ℝ) →
        ContainsConvexSubset 3 n X ∨
          Nonempty (AlternatingPCapFamily n (pzSourceScale n) X)) :
    PohoataZakharovEnvelopeCertificate := by
  exact {
    scale := pzSourceScale
    constant := C
    scale_tendsto := pzSourceScale_tendsto_atTop
    forces_eventually := by
      filter_upwards [hextract] with n hn
      intro X hgp hlarge
      rcases hn.2 X hgp hlarge with hconv | hcaps
      · exact hconv
      · exact hcaps.some.containsConvexSubset hn.1 }

/-- An envelope certificate implies the literal point-set epsilon statement
of Theorem 1.1. -/
private theorem PohoataZakharovEnvelopeCertificate.theoremOneOne
    (cert : PohoataZakharovEnvelopeCertificate) :
    PohoataZakharovTheoremOneOne := by
  intro ε hε
  have henv := eventually_pzEnvelope_lt_two_rpow
    cert.constant cert.scale_tendsto hε
  have hforce := cert.forces_eventually
  rw [eventually_atTop] at henv hforce
  obtain ⟨N₁, hN₁⟩ := hforce
  obtain ⟨N₂, hN₂⟩ := henv
  refine ⟨max N₁ N₂, fun n hn X hcard hgp ↦ ?_⟩
  exact hN₁ n ((le_max_left _ _).trans hn) X hgp
    ((hN₂ n ((le_max_right _ _).trans hn)).trans_le hcard)

/-! ## Existence of the numerical Erdős--Szekeres function -/

/-- The literal PZ theorem also proves that the forcing set defining
`erdosSzekeresNumber 3 n` is nonempty for every `n`. -/
private theorem hasErdosSzekeresNumber_three_of_theoremOneOne
    (hPZ : PohoataZakharovTheoremOneOne) :
    ∀ n : ℕ, HasErdosSzekeresNumber 3 n := by
  intro n
  obtain ⟨n₀, hn₀⟩ := hPZ 1 (by norm_num)
  let m := max n n₀
  let N : ℕ := ⌈(2 : ℝ) ^ (m : ℝ)⌉₊
  refine ⟨N, ?_⟩
  intro X hNX hgp
  have hmconv : ContainsConvexSubset 3 m X := by
    apply hn₀ m (le_max_right n n₀) X _ hgp
    have hceil : (2 : ℝ) ^ (m : ℝ) ≤ (N : ℝ) := Nat.le_ceil _
    have hNX' : (N : ℝ) ≤ (X.card : ℝ) := by exact_mod_cast hNX
    simpa only [one_mul] using hceil.trans hNX'
  obtain ⟨Y, hYX, hYcard, hYconv⟩ := hmconv
  have hnY : n ≤ Y.card := by simpa only [hYcard] using le_max_left n n₀
  obtain ⟨Z, hZY, hZcard⟩ := Finset.exists_subset_card_eq hnY
  refine ⟨Z, hZY.trans hYX, hZcard, ?_⟩
  intro x hxZ hxHull
  apply hYconv x (hZY hxZ)
  exact convexHull_mono (by
    intro y hy
    exact Finset.erase_subset_erase x hZY hy) hxHull

end

end Erdos651
