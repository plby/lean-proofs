/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.Section9KernelAffineReduction
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.Visible

/-!
# Freiman's dimension lemma

This is the rank estimate used before the Section 9 product body is built.
For a finite set `K` in a real vector space, its affine rank is the dimension
of the direction of its affine span.  Freiman's lemma gives

`|K + K| >= (r + 1)|K| - r(r + 1)/2`.

The proof follows Bilu, Lemma 4.3.  The geometric step removes a vertex of
the convex hull.  If the affine rank drops, three full layers of the sumset
are disjoint.  Otherwise a visible facet of the remaining convex hull gives
`r` additional sums.  The induction is recorded over the integers, avoiding
all artefacts from truncated natural subtraction.
-/

namespace Erdos186.CFP.Bilu.Section43FreimanDimension

open Set Module Submodule
open scoped Pointwise
open Section7FreimanMap

noncomputable section

set_option autoImplicit false

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [DecidableEq V]

/-- The affine dimension of a finite set. -/
def affineRank (K : Finset V) : ℕ :=
  finrank ℝ (affineSpan ℝ (K : Set V)).direction

/-- The exact right-hand side of Freiman's dimension lemma, in `ℚ` so that
the triangular correction is honest subtraction and division by two. -/
def freimanDimensionLowerBound (K : Finset V) : ℚ :=
  ((affineRank K + 1 : ℕ) : ℚ) * K.card -
    ((affineRank K : ℕ) : ℚ) * (affineRank K + 1) / 2

/-- The one-point peeling alternative in Bilu's proof of Lemma 4.3.

`rank_drop` is the case where deleting the exposed vertex lowers affine
dimension by one.  Its sumset contributes all of `x + K'` and `2x` beyond
`K' + K'`.  In the other case a visible facet supplies `r` sums beyond the
old double sumset, together with `2x`. -/
structure FreimanPeelingCertificate (K : Finset V) where
  point : V
  point_mem : point ∈ K
  rank_erase_le : affineRank (K.erase point) ≤ affineRank K
  rank_le_erase_add_one : affineRank K ≤ affineRank (K.erase point) + 1
  growth_drop : affineRank (K.erase point) < affineRank K →
    (pairSumset (K.erase point)).card + K.card ≤ (pairSumset K).card
  growth_same : affineRank (K.erase point) = affineRank K →
    (pairSumset (K.erase point)).card + affineRank K + 1 ≤
      (pairSumset K).card

/-- Affine rank is monotone under inclusion. -/
theorem affineRank_mono {K L : Finset V} (hKL : K ⊆ L) :
    affineRank K ≤ affineRank L := by
  apply Submodule.finrank_mono
  apply AffineSubspace.direction_le
  apply affineSpan_mono ℝ
  exact_mod_cast hKL

/-- Adjoining one point increases affine rank by at most one. -/
theorem affineRank_le_erase_add_one (K : Finset V) {x : V} (hx : x ∈ K) :
    affineRank K ≤ affineRank (K.erase x) + 1 := by
  rw [affineRank, affineRank, direction_affineSpan, direction_affineSpan]
  have hset : (K : Set V) = insert x (K.erase x : Set V) := by
    ext y
    simp only [Finset.coe_sort_coe, Finset.mem_coe, Finset.mem_erase,
      Set.mem_insert_iff]
    constructor
    · intro hy
      by_cases hxy : y = x
      · exact Or.inl hxy
      · exact Or.inr ⟨hxy, hy⟩
    · rintro (rfl | ⟨_h, hy⟩)
      · exact hx
      · exact hy
  rw [hset]
  exact finrank_vectorSpan_insert_le_set ℝ (K.erase x : Set V) x

/-- A point whose deletion lowers affine rank is not in the affine span of
the remaining points. -/
theorem not_mem_affineSpan_erase_of_rank_lt (K : Finset V) {x : V}
    (hx : x ∈ K) (hrank : affineRank (K.erase x) < affineRank K) :
    x ∉ affineSpan ℝ (K.erase x : Set V) := by
  intro hxspan
  have hset : (K : Set V) = insert x (K.erase x : Set V) := by
    ext y
    simp only [Finset.mem_coe, Finset.mem_erase, Set.mem_insert_iff]
    constructor
    · intro hy
      by_cases hxy : y = x
      · exact Or.inl hxy
      · exact Or.inr ⟨hxy, hy⟩
    · rintro (rfl | ⟨_h, hy⟩)
      · exact hx
      · exact hy
  have hspan : vectorSpan ℝ (K : Set V) =
      vectorSpan ℝ (K.erase x : Set V) := by
    rw [hset, vectorSpan_insert_eq_vectorSpan hxspan]
  rw [affineRank, affineRank, direction_affineSpan,
    direction_affineSpan, hspan] at hrank
  exact (Nat.lt_irrefl _ hrank)

/-- The translate of a finite set by a fixed point. -/
def pointTranslate (x : V) (K : Finset V) : Finset V :=
  K.image fun y ↦ x + y

@[simp] theorem card_pointTranslate (x : V) (K : Finset V) :
    (pointTranslate x K).card = K.card := by
  rw [pointTranslate, Finset.card_image_of_injective]
  intro y z hyz
  exact add_left_cancel hyz

@[simp] theorem mem_pointTranslate (x : V) (K : Finset V) (z : V) :
    z ∈ pointTranslate x K ↔ ∃ y ∈ K, x + y = z := by
  rw [pointTranslate, Finset.mem_image]

/-- If `x` is outside the affine span of `K`, then the layer `x + K`
does not meet `K + K`. -/
theorem disjoint_pairSumset_pointTranslate_of_not_mem_affineSpan
    (K : Finset V) {x : V} (hx : x ∉ affineSpan ℝ (K : Set V)) :
    Disjoint (pairSumset K) (pointTranslate x K) := by
  rw [Finset.disjoint_left]
  intro z hzsum hztranslate
  obtain ⟨u, hu, v, hv, huv⟩ := (mem_pairSumset K z).mp hzsum
  obtain ⟨y, hy, hxy⟩ := (mem_pointTranslate x K z).mp hztranslate
  apply hx
  let S := affineSpan ℝ (K : Set V)
  have hyS : y ∈ S := subset_affineSpan ℝ (K : Set V) hy
  have huS : u ∈ S := subset_affineSpan ℝ (K : Set V) hu
  have hvS : v ∈ S := subset_affineSpan ℝ (K : Set V) hv
  apply (AffineSubspace.vsub_right_mem_direction_iff_mem hyS x).mp
  have huy : u - y ∈ S.direction :=
    AffineSubspace.vsub_mem_direction huS hyS
  have hvy : v - y ∈ S.direction :=
    AffineSubspace.vsub_mem_direction hvS hyS
  have hrel : x + y = u + v := hxy.trans huv.symm
  have heq : x - y = (u - y) + (v - y) := by
    calc
      x - y = (x + y) - y - y := by abel
      _ = (u + v) - y - y := by rw [hrel]
      _ = (u - y) + (v - y) := by abel
  change x - y ∈ S.direction
  rw [heq]
  exact S.direction.add_mem huy hvy

/-- The exceptional sum `x+x` is outside both lower layers whenever `x`
is outside the affine span of `K`. -/
theorem point_self_not_mem_lower_layers_of_not_mem_affineSpan
    (K : Finset V) {x : V} (hx : x ∉ affineSpan ℝ (K : Set V)) :
    x + x ∉ pairSumset K ∪ pointTranslate x K := by
  intro hmem
  rw [Finset.mem_union] at hmem
  rcases hmem with hsum | htranslate
  · obtain ⟨u, hu, v, hv, huv⟩ := (mem_pairSumset K (x + x)).mp hsum
    apply hx
    let S := affineSpan ℝ (K : Set V)
    have huS : u ∈ S := subset_affineSpan ℝ (K : Set V) hu
    have hvS : v ∈ S := subset_affineSpan ℝ (K : Set V) hv
    have hmid : (2 : ℝ)⁻¹ • u + (2 : ℝ)⁻¹ • v ∈ S := by
      have hline := AffineMap.lineMap_mem (Q := S) (1 / 2 : ℝ) huS hvS
      rw [AffineMap.lineMap_apply_module] at hline
      norm_num at hline ⊢
      exact hline
    have heq : (2 : ℝ)⁻¹ • u + (2 : ℝ)⁻¹ • v = x := by
      calc
        (2 : ℝ)⁻¹ • u + (2 : ℝ)⁻¹ • v =
            (2 : ℝ)⁻¹ • (u + v) := by rw [smul_add]
        _ = (2 : ℝ)⁻¹ • (x + x) := by rw [huv]
        _ = x := by module
    rw [← heq]
    exact hmid
  · obtain ⟨y, hy, hxy⟩ := (mem_pointTranslate x K (x + x)).mp htranslate
    have : y = x := by
      exact add_left_cancel hxy
    have hxK : x ∈ K := by simpa [this] using hy
    exact hx (subset_affineSpan ℝ (K : Set V) hxK)

/-- Cardinal bookkeeping for three disjoint layers inside one finite set. -/
theorem card_add_card_add_one_le_of_three_layers
    {A B T : Finset V} {z : V} (hAB : Disjoint A B)
    (hz : z ∉ A ∪ B) (hsub : A ∪ B ∪ {z} ⊆ T) :
    A.card + B.card + 1 ≤ T.card := by
  have hsingle : Disjoint (A ∪ B) ({z} : Finset V) :=
    Finset.disjoint_singleton_right.mpr hz
  calc
    A.card + B.card + 1 = (A ∪ B ∪ {z}).card := by
      rw [Finset.card_union_of_disjoint hsingle,
        Finset.card_union_of_disjoint hAB, Finset.card_singleton]
    _ ≤ T.card := Finset.card_le_card hsub

/-- The rank-drop branch in the peeling certificate. -/
theorem pairSumset_growth_of_rank_drop (K : Finset V) {x : V}
    (hx : x ∈ K) (hrank : affineRank (K.erase x) < affineRank K) :
    (pairSumset (K.erase x)).card + K.card ≤ (pairSumset K).card := by
  let K' := K.erase x
  have hxspan : x ∉ affineSpan ℝ (K' : Set V) := by
    simpa [K'] using not_mem_affineSpan_erase_of_rank_lt K hx hrank
  have hdisj : Disjoint (pairSumset K') (pointTranslate x K') :=
    disjoint_pairSumset_pointTranslate_of_not_mem_affineSpan K' hxspan
  have hself : x + x ∉ pairSumset K' ∪ pointTranslate x K' :=
    point_self_not_mem_lower_layers_of_not_mem_affineSpan K' hxspan
  have hsub : pairSumset K' ∪ pointTranslate x K' ∪ {x + x} ⊆
      pairSumset K := by
    intro z hz
    simp only [Finset.mem_union, Finset.mem_singleton] at hz
    rcases hz with (hz | hz) | rfl
    · obtain ⟨u, hu, v, hv, rfl⟩ := (mem_pairSumset K' z).mp hz
      exact (mem_pairSumset K _).mpr
        ⟨u, Finset.mem_of_mem_erase hu, v, Finset.mem_of_mem_erase hv, rfl⟩
    · obtain ⟨y, hy, rfl⟩ := (mem_pointTranslate x K' z).mp hz
      exact (mem_pairSumset K _).mpr
        ⟨x, hx, y, Finset.mem_of_mem_erase hy, rfl⟩
    · exact (mem_pairSumset K _).mpr ⟨x, hx, x, hx, rfl⟩
  have hcard := card_add_card_add_one_le_of_three_layers hdisj hself hsub
  rw [card_pointTranslate] at hcard
  have hKcard : K'.card + 1 = K.card := by
    simpa [K'] using Finset.card_erase_add_one hx
  calc
    (pairSumset (K.erase x)).card + K.card =
        (pairSumset K').card + (K'.card + 1) := by
          change (pairSumset K').card + K.card = _
          rw [← hKcard]
    _ = (pairSumset K').card + K'.card + 1 := by omega
    _ ≤ (pairSumset K).card := hcard

/-- A visible facet of the set remaining after an exposed point is
deleted.  The separating functional is stated only on the finite set,
which is exactly what the sumset layer argument uses. -/
structure VisibleFacetCertificate (K : Finset V) (x : V) where
  face : Finset V
  face_subset : face ⊆ K
  face_card : affineRank (insert x K) ≤ face.card
  functional : V →ₗ[ℝ] ℝ
  level : ℝ
  face_level : ∀ y ∈ face, functional y = level
  set_le : ∀ y ∈ K, functional y ≤ level
  point_gt : level < functional x

/-- A visible facet contributes its translate as a new layer beyond the
old double sumset. -/
theorem VisibleFacetCertificate.disjoint_pairSumset_pointTranslate
    {K : Finset V} {x : V} (F : VisibleFacetCertificate K x) :
    Disjoint (pairSumset K) (pointTranslate x F.face) := by
  rw [Finset.disjoint_left]
  intro z hzsum hzface
  obtain ⟨u, hu, v, hv, huv⟩ := (mem_pairSumset K z).mp hzsum
  obtain ⟨y, hy, hxy⟩ := (mem_pointTranslate x F.face z).mp hzface
  have hold : F.functional z ≤ F.level + F.level := by
    rw [← huv, map_add]
    exact add_le_add (F.set_le u hu) (F.set_le v hv)
  have hnew : F.functional x + F.level ≤ F.functional z := by
    rw [← hxy, map_add, F.face_level y hy]
  linarith [F.point_gt]

/-- The exposed point doubled is beyond both the old and facet layers. -/
theorem VisibleFacetCertificate.point_self_not_mem_layers
    {K : Finset V} {x : V} (F : VisibleFacetCertificate K x) :
    x + x ∉ pairSumset K ∪ pointTranslate x F.face := by
  intro hmem
  rw [Finset.mem_union] at hmem
  rcases hmem with hsum | hface
  · obtain ⟨u, hu, v, hv, huv⟩ :=
      (mem_pairSumset K (x + x)).mp hsum
    have hold : F.functional (x + x) ≤ F.level + F.level := by
      rw [← huv, map_add]
      exact add_le_add (F.set_le u hu) (F.set_le v hv)
    rw [map_add] at hold
    linarith [F.point_gt]
  · obtain ⟨y, hy, hxy⟩ :=
      (mem_pointTranslate x F.face (x + x)).mp hface
    have heq := congrArg F.functional hxy
    simp only [map_add, F.face_level y hy] at heq
    linarith [F.point_gt]

/-- The same-rank branch of the peeling argument, assuming its visible
facet certificate. -/
theorem pairSumset_growth_of_visibleFacet (K : Finset V) {x : V}
    (hx : x ∈ K) (F : VisibleFacetCertificate (K.erase x) x) :
    (pairSumset (K.erase x)).card + affineRank K + 1 ≤
      (pairSumset K).card := by
  let K' := K.erase x
  have hdisj : Disjoint (pairSumset K') (pointTranslate x F.face) := by
    simpa [K'] using F.disjoint_pairSumset_pointTranslate
  have hself : x + x ∉ pairSumset K' ∪ pointTranslate x F.face := by
    simpa [K'] using F.point_self_not_mem_layers
  have hsub : pairSumset K' ∪ pointTranslate x F.face ∪ {x + x} ⊆
      pairSumset K := by
    intro z hz
    simp only [Finset.mem_union, Finset.mem_singleton] at hz
    rcases hz with (hz | hz) | rfl
    · obtain ⟨u, hu, v, hv, rfl⟩ := (mem_pairSumset K' z).mp hz
      exact (mem_pairSumset K _).mpr
        ⟨u, Finset.mem_of_mem_erase hu, v, Finset.mem_of_mem_erase hv, rfl⟩
    · obtain ⟨y, hy, rfl⟩ := (mem_pointTranslate x F.face z).mp hz
      exact (mem_pairSumset K _).mpr
        ⟨x, hx, y, Finset.mem_of_mem_erase (F.face_subset hy), rfl⟩
    · exact (mem_pairSumset K _).mpr ⟨x, hx, x, hx, rfl⟩
  have hcard := card_add_card_add_one_le_of_three_layers hdisj hself hsub
  rw [card_pointTranslate] at hcard
  have hrankInsert : affineRank (insert x K') = affineRank K := by
    have hinsert : insert x K' = K := by
      change insert x (K.erase x) = K
      exact Finset.insert_erase hx
    rw [hinsert]
  have hface : affineRank K ≤ F.face.card := by
    rw [← hrankInsert]
    exact F.face_card
  change (pairSumset K').card + affineRank K + 1 ≤
    (pairSumset K).card
  omega

/-- Points of `K` visible from `x` through its convex hull. -/
def visibleFinset (K : Finset V) (x : V) : Finset V :=
  by
    classical
    exact K.filter fun y ↦ IsVisible ℝ (convexHull ℝ (K : Set V)) x y

@[simp] theorem mem_visibleFinset (K : Finset V) (x y : V) :
    y ∈ visibleFinset K x ↔
      y ∈ K ∧ IsVisible ℝ (convexHull ℝ (K : Set V)) x y := by
  classical
  simp [visibleFinset]

/-- The visible-point theorem in finite-dimensional/natural-rank form. -/
theorem affineRank_insert_le_card_visibleFinset (K : Finset V) {x : V}
    (hx : x ∉ convexHull ℝ (K : Set V)) :
    affineRank (insert x K) ≤ (visibleFinset K x).card := by
  classical
  have hclosed : IsClosed (convexHull ℝ (K : Set V)) :=
    K.finite_toSet.isClosed_convexHull ℝ
  have hrank := rank_le_card_isVisible hclosed hx
  have hvisibleSet :
      {y ∈ (K : Set V) |
        IsVisible ℝ (convexHull ℝ (K : Set V)) x y} =
        (visibleFinset K x : Set V) := by
    ext y
    simp [visibleFinset]
  rw [hvisibleSet, ← Submodule.finrank_eq_rank,
    Cardinal.mk_fintype] at hrank
  have hvisibleCard :
      Fintype.card (visibleFinset K x : Set V) =
        (visibleFinset K x).card := by
    change Fintype.card ↥(visibleFinset K x) = (visibleFinset K x).card
    exact Fintype.card_coe (visibleFinset K x)
  rw [hvisibleCard] at hrank
  have hrankNat :
      finrank ℝ (span ℝ (-x +ᵥ (K : Set V))) ≤
        (visibleFinset K x).card := by
    exact_mod_cast hrank
  rw [affineRank, direction_affineSpan]
  have hspan : vectorSpan ℝ ((insert x K : Finset V) : Set V) =
      span ℝ (-x +ᵥ (K : Set V)) := by
    rw [vectorSpan_eq_span_vsub_finset_right_ne ℝ
      (Finset.mem_insert_self x K)]
    have hxK : x ∉ K := by
      intro hxK
      exact hx (subset_convexHull ℝ (K : Set V) hxK)
    rw [Finset.erase_insert hxK]
    congr 1
    ext v
    simp only [Finset.coe_image, Set.mem_image]
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y, hy, ?_⟩
      simp [vadd_eq_add, sub_eq_add_neg, add_comm]
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y, hy, ?_⟩
      simp [vadd_eq_add, sub_eq_add_neg, add_comm]
  rw [hspan]
  exact hrankNat

/-- The translates by points visible from `x` do not meet the old double
sumset: a collision would put the midpoint of `x` and the visible point in
the old convex hull. -/
theorem disjoint_pairSumset_pointTranslate_visibleFinset
    (K : Finset V) {x : V} (hx : x ∉ convexHull ℝ (K : Set V)) :
    Disjoint (pairSumset K) (pointTranslate x (visibleFinset K x)) := by
  rw [Finset.disjoint_left]
  intro z hzsum hzvisible
  obtain ⟨u, hu, v, hv, huv⟩ := (mem_pairSumset K z).mp hzsum
  obtain ⟨y, hyvisible, hxy⟩ :=
    (mem_pointTranslate x (visibleFinset K x) z).mp hzvisible
  have hydata := (mem_visibleFinset K x y).mp hyvisible
  have hxyne : x ≠ y := by
    intro hxyEq
    apply hx
    rw [hxyEq]
    exact subset_convexHull ℝ (K : Set V) hydata.1
  have hrel : x + y = u + v := hxy.trans huv.symm
  have hmidEq :
      AffineMap.lineMap x y (1 / 2 : ℝ) =
        AffineMap.lineMap u v (1 / 2 : ℝ) := by
    simp only [AffineMap.lineMap_apply_module]
    norm_num
    rw [← smul_add, ← smul_add, hrel]
  have huHull : u ∈ convexHull ℝ (K : Set V) :=
    subset_convexHull ℝ (K : Set V) hu
  have hvHull : v ∈ convexHull ℝ (K : Set V) :=
    subset_convexHull ℝ (K : Set V) hv
  have hmidHull : AffineMap.lineMap x y (1 / 2 : ℝ) ∈
      convexHull ℝ (K : Set V) := by
    rw [hmidEq]
    exact (convex_convexHull ℝ (K : Set V)).lineMap_mem
      huHull hvHull (by norm_num)
  exact (hydata.2 hmidHull)
    (sbtw_lineMap_iff.mpr ⟨hxyne, by norm_num⟩)

/-- The doubled exposed point is outside both old and visible-translate
layers. -/
theorem point_self_not_mem_visible_layers
    (K : Finset V) {x : V} (hx : x ∉ convexHull ℝ (K : Set V)) :
    x + x ∉ pairSumset K ∪ pointTranslate x (visibleFinset K x) := by
  intro hmem
  rw [Finset.mem_union] at hmem
  rcases hmem with hsum | hvisible
  · obtain ⟨u, hu, v, hv, huv⟩ :=
      (mem_pairSumset K (x + x)).mp hsum
    apply hx
    have huHull : u ∈ convexHull ℝ (K : Set V) :=
      subset_convexHull ℝ (K : Set V) hu
    have hvHull : v ∈ convexHull ℝ (K : Set V) :=
      subset_convexHull ℝ (K : Set V) hv
    have hmid := (convex_convexHull ℝ (K : Set V)).lineMap_mem
      huHull hvHull (show (1 / 2 : ℝ) ∈ Set.Icc 0 1 by norm_num)
    have hline : AffineMap.lineMap u v (1 / 2 : ℝ) = x := by
      simp only [AffineMap.lineMap_apply_module]
      norm_num
      rw [← smul_add, huv]
      module
    rwa [hline] at hmid
  · obtain ⟨y, hy, hxy⟩ :=
      (mem_pointTranslate x (visibleFinset K x) (x + x)).mp hvisible
    have hyEq : y = x := add_left_cancel hxy
    have hyK := (mem_visibleFinset K x y).mp hy
    apply hx
    rw [← hyEq]
    exact subset_convexHull ℝ (K : Set V) hyK.1

/-- The same-rank peeling growth supplied by the visible-point theorem. -/
theorem pairSumset_growth_of_visibleFinset (K : Finset V) {x : V}
    (hxK : x ∈ K) (hx : x ∉ convexHull ℝ (K.erase x : Set V)) :
    (pairSumset (K.erase x)).card + affineRank K + 1 ≤
      (pairSumset K).card := by
  let K' := K.erase x
  have hdisj : Disjoint (pairSumset K')
      (pointTranslate x (visibleFinset K' x)) :=
    disjoint_pairSumset_pointTranslate_visibleFinset K' hx
  have hself : x + x ∉ pairSumset K' ∪
      pointTranslate x (visibleFinset K' x) :=
    point_self_not_mem_visible_layers K' hx
  have hsub : pairSumset K' ∪ pointTranslate x (visibleFinset K' x) ∪
      {x + x} ⊆ pairSumset K := by
    intro z hz
    simp only [Finset.mem_union, Finset.mem_singleton] at hz
    rcases hz with (hz | hz) | rfl
    · obtain ⟨u, hu, v, hv, rfl⟩ := (mem_pairSumset K' z).mp hz
      exact (mem_pairSumset K _).mpr
        ⟨u, Finset.mem_of_mem_erase hu, v, Finset.mem_of_mem_erase hv, rfl⟩
    · obtain ⟨y, hy, rfl⟩ :=
        (mem_pointTranslate x (visibleFinset K' x) z).mp hz
      have hyK' := (mem_visibleFinset K' x y).mp hy |>.1
      exact (mem_pairSumset K _).mpr
        ⟨x, hxK, y, Finset.mem_of_mem_erase hyK', rfl⟩
    · exact (mem_pairSumset K _).mpr ⟨x, hxK, x, hxK, rfl⟩
  have hcard := card_add_card_add_one_le_of_three_layers hdisj hself hsub
  rw [card_pointTranslate] at hcard
  have hrankInsert : affineRank (insert x K') = affineRank K := by
    have hinsert : insert x K' = K := by
      change insert x (K.erase x) = K
      exact Finset.insert_erase hxK
    rw [hinsert]
  have hvisCard : affineRank K ≤ (visibleFinset K' x).card := by
    rw [← hrankInsert]
    exact affineRank_insert_le_card_visibleFinset K' hx
  change (pairSumset K').card + affineRank K + 1 ≤
    (pairSumset K).card
  omega

/-- Every finite set with at least two points has the one-point peeling
certificate used in Freiman's induction.  The point is an extreme point of
the finite convex hull; visible points supply the same-rank layer. -/
theorem exists_freimanPeelingCertificate (K : Finset V) (hK : 1 < K.card) :
    Nonempty (FreimanPeelingCertificate K) := by
  classical
  have hKnonempty : K.Nonempty := Finset.card_pos.mp (by omega)
  have hKset : (K : Set V).Nonempty := by
    simpa only [Finset.coe_nonempty] using hKnonempty
  have hHullNonempty : (convexHull ℝ (K : Set V)).Nonempty :=
    hKset.convexHull
  obtain ⟨x, hxExtreme⟩ :=
    (K.finite_toSet.isCompact_convexHull ℝ).extremePoints_nonempty
      hHullNonempty
  have hxK : x ∈ K := by
    exact (extremePoints_convexHull_subset (𝕜 := ℝ)) hxExtreme
  have hxBigNot :
      x ∉ convexHull ℝ (convexHull ℝ (K : Set V) \ {x}) := by
    have hiff := Convex.mem_extremePoints_iff_mem_sdiff_convexHull_sdiff
      (x := x) (convex_convexHull ℝ (K : Set V))
    exact (hiff.mp hxExtreme).2
  have hxErase : x ∉ convexHull ℝ (K.erase x : Set V) := by
    intro hxSmall
    apply hxBigNot
    apply (convexHull_mono ?_) hxSmall
    intro y hy
    have hyK : y ∈ K := Finset.mem_of_mem_erase hy
    have hyne : y ≠ x := (Finset.mem_erase.mp hy).1
    exact ⟨subset_convexHull ℝ (K : Set V) hyK, by simpa using hyne⟩
  refine ⟨{
    point := x
    point_mem := hxK
    rank_erase_le := affineRank_mono (Finset.erase_subset x K)
    rank_le_erase_add_one := affineRank_le_erase_add_one K hxK
    growth_drop := fun hrank ↦ pairSumset_growth_of_rank_drop K hxK hrank
    growth_same := fun _hrank ↦ pairSumset_growth_of_visibleFinset K hxK hxErase
  }⟩

/-- A nonempty finite set contains at least one more point than its affine
dimension. -/
theorem affineRank_add_one_le_card (K : Finset V) (hK : K.Nonempty) :
    affineRank K + 1 ≤ K.card := by
  letI : Nonempty {x // x ∈ K} := hK.to_subtype
  have hrange :
      Set.range (fun x : {x // x ∈ K} ↦ (x : V)) = (K : Set V) := by
    ext x
    simp
  have hdim := finrank_vectorSpan_range_add_one_le ℝ
    (fun x : {x // x ∈ K} ↦ (x : V))
  rw [hrange, Fintype.card_coe] at hdim
  rw [affineRank, direction_affineSpan]
  exact hdim

/-- Arithmetic induction once the exposed-vertex/visible-facet peeling
certificate is available for every non-singleton finite set. -/
theorem freiman_dimension_lower_bound_of_peeling
    (peel : ∀ (K : Finset V), 1 < K.card →
      Nonempty (FreimanPeelingCertificate K)) :
    ∀ K : Finset V,
      freimanDimensionLowerBound K ≤ ((pairSumset K).card : ℚ) := by
  classical
  intro K
  induction K using Finset.strongInductionOn with
  | _ K ih =>
      by_cases hK0 : K.card = 0
      · have hK : K = ∅ := Finset.card_eq_zero.mp hK0
        subst K
        unfold freimanDimensionLowerBound
        simp only [Finset.card_empty, Nat.cast_zero, mul_zero, zero_sub,
          pairSumset, Finset.image_empty, Finset.card_empty]
        exact neg_nonpos.mpr (by positivity)
      by_cases hK1 : K.card = 1
      · obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp hK1
        have hrank : affineRank ({x} : Finset V) = 0 := by
          have hdim := affineRank_add_one_le_card ({x} : Finset V) (by simp)
          simp only [Finset.card_singleton] at hdim
          omega
        simp [freimanDimensionLowerBound, pairSumset, hrank]
      have hKtwo : 1 < K.card := by omega
      obtain ⟨P⟩ := peel K hKtwo
      let K' := K.erase P.point
      have hK'sub : K' ⊂ K := by
        exact Finset.erase_ssubset P.point_mem
      have hIH := ih K' hK'sub
      have hcard : K'.card + 1 = K.card := by
        simpa [K'] using Finset.card_erase_add_one P.point_mem
      by_cases hrank : affineRank K' = affineRank K
      · have hrankErase : affineRank (K.erase P.point) = affineRank K := by
          simpa [K'] using hrank
        have hgrowthNat :
            (pairSumset K').card + affineRank K + 1 ≤
              (pairSumset K).card := by
          simpa [K'] using P.growth_same hrankErase
        have hgrowth :
            ((pairSumset K').card : ℚ) + affineRank K + 1 ≤
              ((pairSumset K).card : ℚ) := by
          exact_mod_cast hgrowthNat
        simp only [freimanDimensionLowerBound] at hIH ⊢
        rw [hrank] at hIH
        push_cast at hIH hgrowth ⊢
        have hcardZ : (K.card : ℚ) = (K'.card : ℚ) + 1 := by
          exact_mod_cast hcard.symm
        rw [hcardZ]
        nlinarith
      · have hranklt : affineRank K' < affineRank K :=
          lt_of_le_of_ne P.rank_erase_le hrank

        have hrankeq : affineRank K' + 1 = affineRank K := by
          have hle : affineRank K ≤ affineRank K' + 1 := by
            simpa [K'] using P.rank_le_erase_add_one
          have := hle
          omega
        have hrankErase : affineRank (K.erase P.point) < affineRank K := by
          simpa [K'] using hranklt
        have hgrowthNat :
            (pairSumset K').card + K.card ≤ (pairSumset K).card := by
          simpa [K'] using P.growth_drop hrankErase
        have hgrowth :
            ((pairSumset K').card : ℚ) + K.card ≤
              ((pairSumset K).card : ℚ) := by
          exact_mod_cast hgrowthNat
        simp only [freimanDimensionLowerBound] at hIH ⊢
        rw [← hrankeq]
        push_cast at hIH hgrowth ⊢
        have hcardZ : (K.card : ℚ) = (K'.card : ℚ) + 1 := by
          exact_mod_cast hcard.symm
        rw [hcardZ]
        nlinarith

/-- Freiman's dimension lemma in its exact finite form. -/
theorem freiman_dimension_lower_bound (K : Finset V) :
    freimanDimensionLowerBound K ≤ ((pairSumset K).card : ℚ) :=
  freiman_dimension_lower_bound_of_peeling
    (fun L hL ↦ exists_freimanPeelingCertificate L hL) K

/-- The fixed rank consequence needed in Section 9: small doubling bounds
the homogenized affine rank solely in terms of the doubling constant. -/
theorem affineRank_add_one_le_two_mul_of_dimension_bound
    (K : Finset V) (hK : K.Nonempty) (sigma : ℕ)
    (hfreiman : freimanDimensionLowerBound K ≤
      ((pairSumset K).card : ℚ))
    (hdouble : (pairSumset K).card ≤ sigma * K.card) :
    affineRank K + 1 ≤ 2 * sigma := by
  have hcard := affineRank_add_one_le_card K hK
  have hcardPos : (0 : ℚ) < K.card := by exact_mod_cast hK.card_pos
  have hdoubleZ : ((pairSumset K).card : ℚ) ≤
      (sigma : ℚ) * K.card := by exact_mod_cast hdouble
  have hrankNonneg : (0 : ℚ) ≤ affineRank K := by positivity
  have htri :
      ((affineRank K : ℚ) * (affineRank K + 1)) ≤
        (affineRank K : ℚ) * K.card := by
    gcongr
    exact_mod_cast hcard
  have hraw :
      ((affineRank K + 1 : ℕ) : ℚ) * K.card -
          ((affineRank K : ℕ) : ℚ) * (affineRank K + 1) / 2 ≤
        (sigma : ℚ) * K.card := by
    exact hfreiman.trans hdoubleZ
  push_cast at hraw
  have htwice :
      ((affineRank K : ℚ) + 2) * K.card ≤
        (2 * sigma : ℚ) * K.card := by
    nlinarith
  have : (affineRank K : ℚ) + 2 ≤ 2 * sigma := by
    apply (mul_le_mul_iff_of_pos_right hcardPos).mp
    simpa [mul_comm, mul_left_comm, mul_assoc] using htwice
  exact_mod_cast (show (affineRank K : ℚ) + 1 ≤ 2 * sigma by linarith)

/-- Source-facing small-doubling rank bound, with Freiman's dimension
inequality discharged internally. -/
theorem affineRank_add_one_le_two_mul (K : Finset V) (hK : K.Nonempty)
    (sigma : ℕ) (hdouble : (pairSumset K).card ≤ sigma * K.card) :
    affineRank K + 1 ≤ 2 * sigma :=
  affineRank_add_one_le_two_mul_of_dimension_bound K hK sigma
    (freiman_dimension_lower_bound K) hdouble

end

end Erdos186.CFP.Bilu.Section43FreimanDimension

#print axioms
  Erdos186.CFP.Bilu.Section43FreimanDimension.freiman_dimension_lower_bound_of_peeling
#print axioms
  Erdos186.CFP.Bilu.Section43FreimanDimension.freiman_dimension_lower_bound
#print axioms
  Erdos186.CFP.Bilu.Section43FreimanDimension.affineRank_add_one_le_two_mul_of_dimension_bound
#print axioms
  Erdos186.CFP.Bilu.Section43FreimanDimension.affineRank_add_one_le_two_mul
