/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos223.SphericalEuler
import Mathlib.Algebra.Module.Submodule.Union

/-!
# The global spherical drawing of the diameter double cover

This module joins the canonical local radial fans from `SphericalEuler` into
red-to-blue paths for the bipartite double cover.  The final three theorems
give the exact intersection pattern of distinct drawing paths: they meet only
at the base representing a common graph endpoint.
-/

open Metric Set
open scoped BigOperators EuclideanGeometry RealInnerProductSpace SimpleGraph

namespace Erdos223.SphericalEuler.GlobalDoubleCover

noncomputable section

open DiameterRadialFan

variable {d : ℕ} {A : Finset (Point d)}

def leftIndex {x y : {z // z ∈ A}} (hxy : (diameterGraph A).Adj x y) :
    NeighborIndex A x := ⟨y, hxy⟩

def rightIndex {x y : {z // z ∈ A}} (hxy : (diameterGraph A).Adj x y) :
    NeighborIndex A y := ⟨x, hxy.symm⟩

def redBase (A : Finset (Point d)) (x : {z // z ∈ A}) : Point d :=
  NormedSpace.normalize (base A x)

def blueBase (A : Finset (Point d)) (x : {z // z ∈ A}) : Point d :=
  -NormedSpace.normalize (base A x)

def edgeDirection (x y : {z // z ∈ A}) : Point d :=
  (y : Point d) - (x : Point d)

@[simp]
lemma direction_leftIndex {x y : {z // z ∈ A}}
    (hxy : (diameterGraph A).Adj x y) :
    direction (leftIndex hxy) = edgeDirection x y := rfl

@[simp]
lemma neg_direction_rightIndex {x y : {z // z ∈ A}}
    (hxy : (diameterGraph A).Adj x y) :
    -direction (rightIndex hxy) = edgeDirection x y := by
  simp [direction, rightIndex, edgeDirection]

/-- The red half-edge, with its target written using the edge's global
orientation rather than the definitionally equal local direction. -/
def redHalfPath
    (hA : IsDiameterOne A)
    (hmin : ∀ v : {z // z ∈ A}, 2 ≤ (diameterGraph A).degree v)
    {x y : {z // z ∈ A}} (hxy : (diameterGraph A).Adj x y) :
    Path (redBase A x) (edgeDirection x y) :=
  (path hA hmin (leftIndex hxy)).cast rfl (direction_leftIndex hxy).symm

/-- The blue half-edge, directed from the common diameter direction to the
negative of the base at the blue endpoint. -/
def blueHalfPath
    (hA : IsDiameterOne A)
    (hmin : ∀ v : {z // z ∈ A}, 2 ≤ (diameterGraph A).degree v)
    {x y : {z // z ∈ A}} (hxy : (diameterGraph A).Adj x y) :
    Path (edgeDirection x y) (blueBase A y) :=
  (((path hA hmin (rightIndex hxy)).map
    (by fun_prop : Continuous fun z : Point d ↦ -z)).symm).cast
      (neg_direction_rightIndex hxy).symm rfl

/-- Global red-to-blue drawing path for an oriented diameter edge. -/
def redBluePath
    (hA : IsDiameterOne A)
    (hmin : ∀ v : {z // z ∈ A}, 2 ≤ (diameterGraph A).degree v)
    {x y : {z // z ∈ A}} (hxy : (diameterGraph A).Adj x y) :
    Path (redBase A x) (blueBase A y) :=
  (redHalfPath hA hmin hxy).trans (blueHalfPath hA hmin hxy)

lemma range_redHalfPath
    (hA : IsDiameterOne A)
    (hmin : ∀ v : {z // z ∈ A}, 2 ≤ (diameterGraph A).degree v)
    {x y : {z // z ∈ A}} (hxy : (diameterGraph A).Adj x y) :
    Set.range (redHalfPath hA hmin hxy) =
      Set.range (path hA hmin (leftIndex hxy)) := by
  apply congrArg Set.range
  exact Path.cast_coe _ _ _

lemma range_blueHalfPath
    (hA : IsDiameterOne A)
    (hmin : ∀ v : {z // z ∈ A}, 2 ≤ (diameterGraph A).degree v)
    {x y : {z // z ∈ A}} (hxy : (diameterGraph A).Adj x y) :
    Set.range (blueHalfPath hA hmin hxy) =
      -(Set.range (path hA hmin (rightIndex hxy))) := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    rw [Set.mem_neg]
    exact ⟨⟨1 - t, by constructor <;> linarith [t.prop.1, t.prop.2]⟩, by
      change (path hA hmin (rightIndex hxy))
          ⟨1 - (t : ℝ), by constructor <;> linarith [t.prop.1, t.prop.2]⟩ =
        -(-(path hA hmin (rightIndex hxy))
          ⟨1 - (t : ℝ), by constructor <;> linarith [t.prop.1, t.prop.2]⟩)
      simp⟩
  · rw [Set.mem_neg]
    rintro ⟨t, ht⟩
    refine ⟨unitInterval.symm t, ?_⟩
    calc
      (blueHalfPath hA hmin hxy) (unitInterval.symm t) =
          -(path hA hmin (rightIndex hxy)) (unitInterval.symm (unitInterval.symm t)) := rfl
      _ = -(path hA hmin (rightIndex hxy)) t := by rw [unitInterval.symm_symm]
      _ = z := by simpa using congrArg Neg.neg ht

lemma range_redBluePath
    (hA : IsDiameterOne A)
    (hmin : ∀ v : {z // z ∈ A}, 2 ≤ (diameterGraph A).degree v)
    {x y : {z // z ∈ A}} (hxy : (diameterGraph A).Adj x y) :
    Set.range (redBluePath hA hmin hxy) =
      Set.range (path hA hmin (leftIndex hxy)) ∪
        -(Set.range (path hA hmin (rightIndex hxy))) := by
  rw [redBluePath, Path.trans_range, range_redHalfPath, range_blueHalfPath]

lemma diameter_norm_bound (hA : IsDiameterOne A) :
    ∀ p ∈ (↑A : Set (Point d)), ∀ q ∈ (↑A : Set (Point d)), ‖p - q‖ ≤ 1 := by
  intro p hp q hq
  simpa [dist_eq_norm] using hA.dist_le hp hq

lemma direction_ne_redBase
    (hA : IsDiameterOne A)
    (hmin : ∀ v : {z // z ∈ A}, 2 ≤ (diameterGraph A).degree v)
    {x : {z // z ∈ A}} (i : NeighborIndex A x) :
    direction i ≠ redBase A x := by
  intro hi
  have honezero : (1 : ℝ) = 0 := (arc_injective hA hmin i) (by
    rw [arc_one hA hmin i, arc_zero]
    exact hi)
  norm_num at honezero

/-- A local endpoint cannot lie on a different local radial arc. -/
lemma direction_not_mem_other_path
    (hA : IsDiameterOne A)
    (hmin : ∀ v : {z // z ∈ A}, 2 ≤ (diameterGraph A).degree v)
    {x : {z // z ∈ A}} {i j : NeighborIndex A x} (hij : i ≠ j) :
    direction j ∉ Set.range (path hA hmin i) := by
  intro hj
  have hinter : direction j ∈
      Set.range (path hA hmin i) ∩ Set.range (path hA hmin j) :=
    ⟨hj, Path.target_mem_range (path hA hmin j)⟩
  rw [path_ranges_inter_eq_singleton hA hmin hij, Set.mem_singleton_iff] at hinter
  exact direction_ne_redBase hA hmin j hinter

lemma leftRange_subset_region
    (hA : IsDiameterOne A)
    (hmin : ∀ v : {z // z ∈ A}, 2 ≤ (diameterGraph A).degree v)
    {x y : {z // z ∈ A}} (hxy : (diameterGraph A).Adj x y) :
    Set.range (path hA hmin (leftIndex hxy)) ⊆
      diameterConeRegion (↑A : Set (Point d)) (x : Point d) :=
  path_range_subset_region hA hmin (leftIndex hxy)

lemma neg_mem_rightRange_of_mem_blueRange
    (hA : IsDiameterOne A)
    (hmin : ∀ v : {z // z ∈ A}, 2 ≤ (diameterGraph A).degree v)
    {x y : {z // z ∈ A}} {p : Point d} (hxy : (diameterGraph A).Adj x y)
    (hp : p ∈ -(Set.range (path hA hmin (rightIndex hxy)))) :
    -p ∈ Set.range (path hA hmin (rightIndex hxy)) := by
  simpa only [Set.mem_neg, neg_neg] using hp

lemma blueRange_subset_neg_region
    (hA : IsDiameterOne A)
    (hmin : ∀ v : {z // z ∈ A}, 2 ≤ (diameterGraph A).degree v)
    {x y : {z // z ∈ A}} (hxy : (diameterGraph A).Adj x y) :
    -(Set.range (path hA hmin (rightIndex hxy))) ⊆
      -(diameterConeRegion (↑A : Set (Point d)) (y : Point d)) := by
  intro p hp
  rw [Set.mem_neg]
  exact path_range_subset_region hA hmin (rightIndex hxy)
    (neg_mem_rightRange_of_mem_blueRange hA hmin hxy hp)

lemma leftRanges_disjoint
    (hA : IsDiameterOne A)
    (hmin : ∀ v : {z // z ∈ A}, 2 ≤ (diameterGraph A).degree v)
    {x y z w : {u // u ∈ A}}
    (hxy : (diameterGraph A).Adj x y)
    (hzw : (diameterGraph A).Adj z w) (hxz : x ≠ z) :
    Disjoint (Set.range (path hA hmin (leftIndex hxy)))
      (Set.range (path hA hmin (leftIndex hzw))) := by
  rw [Set.disjoint_left]
  intro p hpx hpz
  apply hxz
  apply Subtype.ext
  exact eq_of_mem_two_diameterConeRegions x.prop z.prop (diameter_norm_bound hA)
    (leftRange_subset_region hA hmin hxy hpx)
    (leftRange_subset_region hA hmin hzw hpz)

lemma blueRanges_disjoint
    (hA : IsDiameterOne A)
    (hmin : ∀ v : {z // z ∈ A}, 2 ≤ (diameterGraph A).degree v)
    {x y z w : {u // u ∈ A}}
    (hxy : (diameterGraph A).Adj x y)
    (hzw : (diameterGraph A).Adj z w) (hyw : y ≠ w) :
    Disjoint (-(Set.range (path hA hmin (rightIndex hxy))))
      (-(Set.range (path hA hmin (rightIndex hzw)))) := by
  rw [Set.disjoint_left]
  intro p hpy hpw
  apply hyw
  apply Subtype.ext
  exact eq_of_mem_two_diameterConeRegions y.prop w.prop (diameter_norm_bound hA)
    (path_range_subset_region hA hmin (rightIndex hxy)
      (neg_mem_rightRange_of_mem_blueRange hA hmin hxy hpy))
    (path_range_subset_region hA hmin (rightIndex hzw)
      (neg_mem_rightRange_of_mem_blueRange hA hmin hzw hpw))

/-- A red half for `x → y` and a blue half ending at `w` are disjoint when
`y ≠ w`. -/
lemma leftBlueRanges_disjoint
    (hA : IsDiameterOne A)
    (hmin : ∀ v : {z // z ∈ A}, 2 ≤ (diameterGraph A).degree v)
    {x y z w : {u // u ∈ A}}
    (hxy : (diameterGraph A).Adj x y)
    (hzw : (diameterGraph A).Adj z w) (hyw : y ≠ w) :
    Disjoint (Set.range (path hA hmin (leftIndex hxy)))
      (-(Set.range (path hA hmin (rightIndex hzw)))) := by
  rw [Set.disjoint_left]
  intro p hleft hblue
  have hnegRight := neg_mem_rightRange_of_mem_blueRange hA hmin hzw hblue
  have hpX := leftRange_subset_region hA hmin hxy hleft
  have hnegpW := path_range_subset_region hA hmin (rightIndex hzw) hnegRight
  obtain ⟨hp, hnorm⟩ := eq_direction_of_mem_region_and_neg_mem_region
    x.prop w.prop (diameter_norm_bound hA) hpX hnegpW
  have hxw : (diameterGraph A).Adj x w := (diameterGraph_adj A x w).2 (by
    simpa [dist_eq_norm] using hnorm)
  have hindices : leftIndex hxy ≠ leftIndex hxw := by
    intro hind
    apply hyw
    exact congrArg (fun i : NeighborIndex A x ↦ (i.1 : {u // u ∈ A})) hind
  apply direction_not_mem_other_path hA hmin hindices
  simpa only [direction_leftIndex, edgeDirection, hp] using hleft

/-- The mixed halves of two edges with the same blue endpoint are disjoint
when their red endpoints differ. -/
lemma leftBlueRanges_disjoint_same_target
    (hA : IsDiameterOne A)
    (hmin : ∀ v : {z // z ∈ A}, 2 ≤ (diameterGraph A).degree v)
    {x y z : {u // u ∈ A}}
    (hxy : (diameterGraph A).Adj x y)
    (hzy : (diameterGraph A).Adj z y) (hxz : x ≠ z) :
    Disjoint (Set.range (path hA hmin (leftIndex hxy)))
      (-(Set.range (path hA hmin (rightIndex hzy)))) := by
  rw [Set.disjoint_left]
  intro p hleft hblue
  have hnegRight := neg_mem_rightRange_of_mem_blueRange hA hmin hzy hblue
  have hpX := leftRange_subset_region hA hmin hxy hleft
  have hnegpY := path_range_subset_region hA hmin (rightIndex hzy) hnegRight
  have hp := (eq_direction_of_mem_region_and_neg_mem_region
    x.prop y.prop (diameter_norm_bound hA) hpX hnegpY).1
  have hindices : rightIndex hzy ≠ rightIndex hxy := by
    intro hind
    apply hxz
    exact congrArg (fun i : NeighborIndex A y ↦ (i.1 : {u // u ∈ A})) hind.symm
  apply direction_not_mem_other_path hA hmin hindices
  have hneg : -p = (x : Point d) - (y : Point d) := by
    rw [hp]
    exact neg_sub (y : Point d) (x : Point d)
  simpa only [direction, rightIndex, hneg] using hnegRight

/-- Distinct oriented edges with a common red endpoint meet exactly at that
red base. -/
theorem redBluePath_ranges_inter_eq_redBase
    (hA : IsDiameterOne A)
    (hmin : ∀ v : {z // z ∈ A}, 2 ≤ (diameterGraph A).degree v)
    {x y w : {u // u ∈ A}}
    (hxy : (diameterGraph A).Adj x y)
    (hxw : (diameterGraph A).Adj x w) (hyw : y ≠ w) :
    Set.range (redBluePath hA hmin hxy) ∩
        Set.range (redBluePath hA hmin hxw) = {redBase A x} := by
  have hindices : leftIndex hxy ≠ leftIndex hxw := by
    intro hind
    apply hyw
    exact congrArg (fun i : NeighborIndex A x ↦ (i.1 : {u // u ∈ A})) hind
  apply Set.Subset.antisymm
  · intro p hp
    rw [range_redBluePath hA hmin hxy] at hp
    rw [range_redBluePath hA hmin hxw] at hp
    rcases hp with ⟨hleft | hblue, hleft' | hblue'⟩
    · have hinter : p ∈ Set.range (path hA hmin (leftIndex hxy)) ∩
          Set.range (path hA hmin (leftIndex hxw)) := ⟨hleft, hleft'⟩
      rw [path_ranges_inter_eq_singleton hA hmin hindices] at hinter
      exact hinter
    · exact False.elim
        (Set.disjoint_left.mp (leftBlueRanges_disjoint hA hmin hxy hxw hyw)
          hleft hblue')
    · exact False.elim
        (Set.disjoint_left.mp (leftBlueRanges_disjoint hA hmin hxw hxy hyw.symm)
          hleft' hblue)
    · exact False.elim
        (Set.disjoint_left.mp (blueRanges_disjoint hA hmin hxy hxw hyw)
          hblue hblue')
  · intro p hp
    rw [Set.mem_singleton_iff] at hp
    subst p
    exact ⟨Path.source_mem_range (redBluePath hA hmin hxy),
      Path.source_mem_range (redBluePath hA hmin hxw)⟩

/-- Distinct oriented edges with a common blue endpoint meet exactly at that
blue base. -/
theorem redBluePath_ranges_inter_eq_blueBase
    (hA : IsDiameterOne A)
    (hmin : ∀ v : {z // z ∈ A}, 2 ≤ (diameterGraph A).degree v)
    {x y z : {u // u ∈ A}}
    (hxy : (diameterGraph A).Adj x y)
    (hzy : (diameterGraph A).Adj z y) (hxz : x ≠ z) :
    Set.range (redBluePath hA hmin hxy) ∩
        Set.range (redBluePath hA hmin hzy) = {blueBase A y} := by
  have hindices : rightIndex hxy ≠ rightIndex hzy := by
    intro hind
    apply hxz
    exact congrArg (fun i : NeighborIndex A y ↦ (i.1 : {u // u ∈ A})) hind
  apply Set.Subset.antisymm
  · intro p hp
    rw [range_redBluePath hA hmin hxy] at hp
    rw [range_redBluePath hA hmin hzy] at hp
    rcases hp with ⟨hleft | hblue, hleft' | hblue'⟩
    · exact False.elim
        (Set.disjoint_left.mp (leftRanges_disjoint hA hmin hxy hzy hxz)
          hleft hleft')
    · exact False.elim
        (Set.disjoint_left.mp
          (leftBlueRanges_disjoint_same_target hA hmin hxy hzy hxz)
          hleft hblue')
    · exact False.elim
        (Set.disjoint_left.mp
          (leftBlueRanges_disjoint_same_target hA hmin hzy hxy hxz.symm)
          hleft' hblue)
    · have hneg : -p ∈ Set.range (path hA hmin (rightIndex hxy)) ∩
          Set.range (path hA hmin (rightIndex hzy)) :=
        ⟨neg_mem_rightRange_of_mem_blueRange hA hmin hxy hblue,
          neg_mem_rightRange_of_mem_blueRange hA hmin hzy hblue'⟩
      rw [path_ranges_inter_eq_singleton hA hmin hindices,
        Set.mem_singleton_iff] at hneg
      rw [Set.mem_singleton_iff]
      calc
        p = -(-p) := by simp
        _ = -redBase A y := congrArg Neg.neg hneg
        _ = blueBase A y := rfl
  · intro p hp
    rw [Set.mem_singleton_iff] at hp
    subst p
    exact ⟨Path.target_mem_range (redBluePath hA hmin hxy),
      Path.target_mem_range (redBluePath hA hmin hzy)⟩

/-- If two oriented edges have neither their red nor their blue endpoint in
common, their global drawing paths are disjoint. -/
theorem redBluePath_ranges_inter_eq_empty
    (hA : IsDiameterOne A)
    (hmin : ∀ v : {z // z ∈ A}, 2 ≤ (diameterGraph A).degree v)
    {x y z w : {u // u ∈ A}}
    (hxy : (diameterGraph A).Adj x y)
    (hzw : (diameterGraph A).Adj z w) (hxz : x ≠ z) (hyw : y ≠ w) :
    Set.range (redBluePath hA hmin hxy) ∩
        Set.range (redBluePath hA hmin hzw) = ∅ := by
  apply Set.Subset.antisymm
  · intro p hp
    rw [range_redBluePath hA hmin hxy] at hp
    rw [range_redBluePath hA hmin hzw] at hp
    rcases hp with ⟨hleft | hblue, hleft' | hblue'⟩
    · exact False.elim
        (Set.disjoint_left.mp (leftRanges_disjoint hA hmin hxy hzw hxz)
          hleft hleft')
    · exact False.elim
        (Set.disjoint_left.mp (leftBlueRanges_disjoint hA hmin hxy hzw hyw)
          hleft hblue')
    · exact False.elim
        (Set.disjoint_left.mp (leftBlueRanges_disjoint hA hmin hzw hxy hyw.symm)
          hleft' hblue)
    · exact False.elim
        (Set.disjoint_left.mp (blueRanges_disjoint hA hmin hxy hzw hyw)
          hblue hblue')
  · exact Set.empty_subset _

/-! ## A puncture outside the finite drawing -/

lemma span_pair_ne_top (a b : Point 3) :
    Submodule.span ℝ ({a, b} : Set (Point 3)) ≠ ⊤ := by
  exact (span_lt_top_of_card_lt_finrank (R := ℝ)
    (s := ({a, b} : Set (Point 3))) (by
      classical
      simp only [Set.toFinset_insert, Set.toFinset_singleton]
      have hcard : ({a, b} : Finset (Point 3)).card ≤ 2 := Finset.card_insert_le _ _
      norm_num [Point]
      omega)).ne

lemma arc_mem_span_base_direction {A : Finset (Point 3)}
    (x : {z // z ∈ A}) (i : NeighborIndex A x) (t : ℝ) :
    arc A x i t ∈
      Submodule.span ℝ ({base A x, direction i} : Set (Point 3)) := by
  let S := Submodule.span ℝ ({base A x, direction i} : Set (Point 3))
  have hb : base A x ∈ S := Submodule.subset_span (by simp [S])
  have hd : direction i ∈ S := Submodule.subset_span (by simp [S])
  change NormedSpace.normalize
      ((1 - t) • base A x +
        t • positiveSectionPoint (directionFunctional A x) (direction i)) ∈ S
  rw [NormedSpace.normalize]
  apply S.smul_mem
  apply S.add_mem
  · exact S.smul_mem _ hb
  · exact S.smul_mem _ (S.smul_mem _ hd)

def halfSpan {A : Finset (Point 3)}
    (i : (diameterGraph A).Dart × Bool) : Submodule ℝ (Point 3) :=
  if i.2 then
    Submodule.span ℝ
      ({base A i.1.snd, edgeDirection i.1.snd i.1.fst} : Set (Point 3))
  else
    Submodule.span ℝ
      ({base A i.1.fst, edgeDirection i.1.fst i.1.snd} : Set (Point 3))

lemma halfSpan_ne_top {A : Finset (Point 3)}
    (i : (diameterGraph A).Dart × Bool) : halfSpan i ≠ ⊤ := by
  simp only [halfSpan]
  split <;> apply span_pair_ne_top

lemma normalize_not_mem_of_not_mem {S : Submodule ℝ (Point 3)} {z : Point 3}
    (hz : z ∉ S) : NormedSpace.normalize z ∉ S := by
  intro hn
  apply hz
  rw [← NormedSpace.norm_smul_normalize z]
  exact S.smul_mem _ hn

/-- A unit point outside every great-circle plane supporting the finite
double-cover drawing. -/
theorem exists_unit_avoiding_all_halfSpans (A : Finset (Point 3)) :
    ∃ z : Point 3, ‖z‖ = 1 ∧
      ∀ i : (diameterGraph A).Dart × Bool, z ∉ halfSpan i := by
  let p : Option ((diameterGraph A).Dart × Bool) → Submodule ℝ (Point 3)
    | none => ⊥
    | some i => halfSpan i
  have hp : ∀ i, p i ≠ ⊤ := by
    intro i
    cases i with
    | none => exact bot_ne_top
    | some i => exact halfSpan_ne_top i
  obtain ⟨z, hz⟩ := Submodule.exists_forall_notMem_of_forall_ne_top p hp
  have hz0 : z ≠ 0 := by
    intro hzero
    subst z
    exact hz none (by simp [p])
  refine ⟨NormedSpace.normalize z, NormedSpace.norm_normalize hz0, ?_⟩
  intro i
  exact normalize_not_mem_of_not_mem (hz (some i))

lemma red_path_range_subset_halfSpan
    {A : Finset (Point 3)} (hA : IsDiameterOne A)
    (hmin : ∀ v, 2 ≤ (diameterGraph A).degree v)
    {x y : {z // z ∈ A}} (hxy : (diameterGraph A).Adj x y) :
    Set.range (path hA hmin (leftIndex hxy)) ⊆
      halfSpan (⟨(x, y), hxy⟩, false) := by
  rintro z ⟨t, rfl⟩
  change arc A x (leftIndex hxy) (t : ℝ) ∈ _
  simpa [halfSpan, edgeDirection] using
    arc_mem_span_base_direction x (leftIndex hxy) (t : ℝ)

lemma blue_path_range_subset_halfSpan
    {A : Finset (Point 3)} (hA : IsDiameterOne A)
    (hmin : ∀ v, 2 ≤ (diameterGraph A).degree v)
    {x y : {z // z ∈ A}} (hxy : (diameterGraph A).Adj x y) :
    -(Set.range (path hA hmin (rightIndex hxy))) ⊆
      halfSpan (⟨(x, y), hxy⟩, true) := by
  intro z hz
  rw [Set.mem_neg] at hz
  obtain ⟨t, ht⟩ := hz
  have hmem := arc_mem_span_base_direction y (rightIndex hxy) (t : ℝ)
  have htneg := congrArg Neg.neg ht
  simp only [neg_neg] at htneg
  rw [← htneg]
  change -(arc A y (rightIndex hxy) (t : ℝ)) ∈
    Submodule.span ℝ ({base A y, direction (rightIndex hxy)} : Set (Point 3))
  exact Submodule.neg_mem _ hmem

/-- There is a unit point outside every edge path of the spherical drawing. -/
theorem exists_unit_not_mem_redBluePath_ranges
    {A : Finset (Point 3)} (hA : IsDiameterOne A)
    (hmin : ∀ v, 2 ≤ (diameterGraph A).degree v) :
    ∃ z : Point 3, ‖z‖ = 1 ∧
      ∀ {x y : {z // z ∈ A}} (hxy : (diameterGraph A).Adj x y),
        z ∉ Set.range (redBluePath hA hmin hxy) := by
  obtain ⟨z, hzunit, hzspan⟩ := exists_unit_avoiding_all_halfSpans A
  refine ⟨z, hzunit, ?_⟩
  intro x y hxy hz
  rw [range_redBluePath hA hmin hxy] at hz
  rcases hz with hz | hz
  · exact hzspan (⟨(x, y), hxy⟩, false)
      (red_path_range_subset_halfSpan hA hmin hxy hz)
  · exact hzspan (⟨(x, y), hxy⟩, true)
      (blue_path_range_subset_halfSpan hA hmin hxy hz)

end

end Erdos223.SphericalEuler.GlobalDoubleCover

open Metric Set
open scoped BigOperators EuclideanGeometry RealInnerProductSpace SimpleGraph

namespace Erdos223.SphericalEuler.GlobalDoubleCover

noncomputable section

open DiameterRadialFan

variable {A : Finset (Point 3)}

lemma redBase_mem_region
    (hA : IsDiameterOne A)
    (hmin : ∀ v : {z // z ∈ A}, 2 ≤ (diameterGraph A).degree v)
    (x : {z // z ∈ A}) :
    redBase A x ∈ diameterConeRegion (↑A : Set (Point 3)) (x : Point 3) := by
  have hcard : 0 < Fintype.card (DiameterRadialFan.NeighborIndex A x) := by
    rw [(diameterGraph A).card_neighborSet_eq_degree]
    exact lt_of_lt_of_le (by norm_num) (hmin x)
  let i : DiameterRadialFan.NeighborIndex A x :=
    @Classical.choice _ (Fintype.card_pos_iff.mp hcard)
  exact DiameterRadialFan.path_range_subset_region hA hmin i
    (Path.source_mem_range (DiameterRadialFan.path hA hmin i))

lemma norm_redBase_of_minDegree
    (hA : IsDiameterOne A)
    (hmin : ∀ v : {z // z ∈ A}, 2 ≤ (diameterGraph A).degree v)
    (x : {z // z ∈ A}) : ‖redBase A x‖ = 1 :=
  (redBase_mem_region hA hmin x).1

lemma norm_blueBase_of_minDegree
    (hA : IsDiameterOne A)
    (hmin : ∀ v : {z // z ∈ A}, 2 ≤ (diameterGraph A).degree v)
    (x : {z // z ∈ A}) : ‖blueBase A x‖ = 1 := by
  rw [blueBase, norm_neg]
  exact norm_redBase_of_minDegree hA hmin x

def spherePos
    (hA : IsDiameterOne A)
    (hmin : ∀ v : {z // z ∈ A}, 2 ≤ (diameterGraph A).degree v) :
    ({z // z ∈ A} ⊕ {z // z ∈ A}) → sphere (0 : Point 3) 1
  | .inl x => ⟨redBase A x, mem_sphere_zero_iff_norm.2
      (norm_redBase_of_minDegree hA hmin x)⟩
  | .inr x => ⟨blueBase A x, mem_sphere_zero_iff_norm.2
      (norm_blueBase_of_minDegree hA hmin x)⟩

lemma redBase_injective
    (hA : IsDiameterOne A)
    (hmin : ∀ v : {z // z ∈ A}, 2 ≤ (diameterGraph A).degree v) :
    Function.Injective (redBase A) := by
  intro x y hxy
  apply Subtype.ext
  exact eq_of_mem_two_diameterConeRegions x.prop y.prop (diameter_norm_bound hA)
    (redBase_mem_region hA hmin x) (hxy ▸ redBase_mem_region hA hmin y)

lemma blueBase_injective
    (hA : IsDiameterOne A)
    (hmin : ∀ v : {z // z ∈ A}, 2 ≤ (diameterGraph A).degree v) :
    Function.Injective (blueBase A) := by
  intro x y hxy
  apply redBase_injective hA hmin
  change -redBase A x = -redBase A y at hxy
  exact neg_injective hxy

lemma redBase_ne_blueBase
    (hA : IsDiameterOne A)
    (hmin : ∀ v : {z // z ∈ A}, 2 ≤ (diameterGraph A).degree v)
    (x y : {z // z ∈ A}) : redBase A x ≠ blueBase A y := by
  intro hEq
  have hneg : -redBase A x = redBase A y := by
    change redBase A x = -redBase A y at hEq
    rw [hEq, neg_neg]
  obtain ⟨hdir, hnorm⟩ := eq_direction_of_mem_region_and_neg_mem_region
    x.prop y.prop (diameter_norm_bound hA) (redBase_mem_region hA hmin x)
    (hneg ▸ redBase_mem_region hA hmin y)
  have hxy : (diameterGraph A).Adj x y := (diameterGraph_adj A x y).2 (by
    simpa [dist_eq_norm] using hnorm)
  apply direction_ne_redBase hA hmin (leftIndex hxy)
  simpa [direction, leftIndex, edgeDirection] using hdir.symm

lemma spherePos_injective
    (hA : IsDiameterOne A)
    (hmin : ∀ v : {z // z ∈ A}, 2 ≤ (diameterGraph A).degree v) :
    Function.Injective (spherePos hA hmin) := by
  intro u v huv
  cases u with
  | inl x =>
      cases v with
      | inl y =>
          exact congrArg Sum.inl (redBase_injective hA hmin (congrArg Subtype.val huv))
      | inr y =>
          exact False.elim (redBase_ne_blueBase hA hmin x y (congrArg Subtype.val huv))
  | inr x =>
      cases v with
      | inl y =>
          exact False.elim (redBase_ne_blueBase hA hmin y x (congrArg Subtype.val huv).symm)
      | inr y =>
          exact congrArg Sum.inr (blueBase_injective hA hmin (congrArg Subtype.val huv))

end

end Erdos223.SphericalEuler.GlobalDoubleCover




namespace Path

variable {X : Type*} [TopologicalSpace X] {a b c : X}

theorem trans_injective_of_injective_of_range_inter_eq_singleton
    (p : Path a b) (q : Path b c)
    (hp : Function.Injective p) (hq : Function.Injective q)
    (hpq : Set.range p ∩ Set.range q = {b}) :
    Function.Injective (p.trans q) := by
  intro t s hts
  by_cases ht : (t : ℝ) ≤ 1 / 2
  · by_cases hs : (s : ℝ) ≤ 1 / 2
    · rw [Path.trans_apply, dif_pos ht, Path.trans_apply, dif_pos hs] at hts
      have huv := hp hts
      apply Subtype.ext
      have := congrArg Subtype.val huv
      dsimp at this ⊢
      linarith
    · rw [Path.trans_apply, dif_pos ht, Path.trans_apply, dif_neg hs] at hts
      let u : unitInterval := ⟨2 * (t : ℝ), by constructor <;> linarith [t.2.1, ht]⟩
      let v : unitInterval := ⟨2 * (s : ℝ) - 1,
        by constructor <;> linarith [s.2.2, not_le.1 hs]⟩
      have hinter : p u ∈ Set.range p ∩ Set.range q :=
        ⟨⟨u, rfl⟩, ⟨v, hts.symm⟩⟩
      rw [hpq, Set.mem_singleton_iff] at hinter
      have hu : u = (1 : unitInterval) := hp (by simpa using hinter)
      have huv : (u : ℝ) = 1 := congrArg Subtype.val hu
      have htval : (t : ℝ) = 1 / 2 := by
        dsimp [u] at huv
        linarith
      have hslt : 1 / 2 < (s : ℝ) := lt_of_not_ge hs
      have hqv : q v = q 0 := by
        rw [← hts, hinter]
        exact (Path.source q).symm
      have hv : v = (0 : unitInterval) := hq hqv
      have hvval : (v : ℝ) = 0 := congrArg Subtype.val hv
      dsimp [v] at hvval
      exfalso
      linarith
  · by_cases hs : (s : ℝ) ≤ 1 / 2
    · rw [Path.trans_apply, dif_neg ht, Path.trans_apply, dif_pos hs] at hts
      let u : unitInterval := ⟨2 * (t : ℝ) - 1,
        by constructor <;> linarith [t.2.2, not_le.1 ht]⟩
      let v : unitInterval := ⟨2 * (s : ℝ), by constructor <;> linarith [s.2.1, hs]⟩
      have hinter : p v ∈ Set.range p ∩ Set.range q :=
        ⟨⟨v, rfl⟩, ⟨u, hts⟩⟩
      rw [hpq, Set.mem_singleton_iff] at hinter
      have hv : v = (1 : unitInterval) := hp (by simpa using hinter)
      have hvval : (v : ℝ) = 1 := congrArg Subtype.val hv
      have hsval : (s : ℝ) = 1 / 2 := by
        dsimp [v] at hvval
        linarith
      have htlt : 1 / 2 < (t : ℝ) := lt_of_not_ge ht
      have hqu : q u = q 0 := by
        rw [hts, hinter]
        exact (Path.source q).symm
      have hu : u = (0 : unitInterval) := hq hqu
      have huval : (u : ℝ) = 0 := congrArg Subtype.val hu
      dsimp [u] at huval
      exfalso
      linarith
    · rw [Path.trans_apply, dif_neg ht, Path.trans_apply, dif_neg hs] at hts
      have huv := hq hts
      apply Subtype.ext
      have := congrArg Subtype.val huv
      dsimp at this ⊢
      linarith

end Path

open Metric
open scoped EuclideanGeometry RealInnerProductSpace SimpleGraph

namespace Erdos223.SphericalEuler.GlobalDoubleCover

noncomputable section

open DiameterRadialFan

variable {d : ℕ} {A : Finset (Point d)}

lemma redHalfPath_injective
    (hA : IsDiameterOne A)
    (hmin : ∀ v : {z // z ∈ A}, 2 ≤ (diameterGraph A).degree v)
    {x y : {z // z ∈ A}} (hxy : (diameterGraph A).Adj x y) :
    Function.Injective (redHalfPath hA hmin hxy) := by
  intro t s hts
  apply Subtype.ext
  apply arc_injective hA hmin (leftIndex hxy)
  rw [show (redHalfPath hA hmin hxy : unitInterval → Point d) =
      path hA hmin (leftIndex hxy) from Path.cast_coe _ _ _] at hts
  exact hts

lemma blueHalfPath_injective
    (hA : IsDiameterOne A)
    (hmin : ∀ v : {z // z ∈ A}, 2 ≤ (diameterGraph A).degree v)
    {x y : {z // z ∈ A}} (hxy : (diameterGraph A).Adj x y) :
    Function.Injective (blueHalfPath hA hmin hxy) := by
  intro t s hts
  have hcoe : (blueHalfPath hA hmin hxy : unitInterval → Point d) =
      fun u ↦ -(path hA hmin (rightIndex hxy)) (unitInterval.symm u) := by
    funext u
    rw [show (blueHalfPath hA hmin hxy : unitInterval → Point d) =
      (((path hA hmin (rightIndex hxy)).map
        (by fun_prop : Continuous fun z : Point d ↦ -z)).symm) from
          Path.cast_coe _ _ _]
    rfl
  rw [hcoe] at hts
  have harc :
      arc A y (rightIndex hxy) (1 - (t : ℝ)) =
        arc A y (rightIndex hxy) (1 - (s : ℝ)) := by
    simpa [path] using congrArg Neg.neg hts
  have hparam := arc_injective hA hmin (rightIndex hxy) harc
  apply Subtype.ext
  linarith

lemma redHalfPath_range_inter_blueHalfPath_range
    (hA : IsDiameterOne A)
    (hmin : ∀ v : {z // z ∈ A}, 2 ≤ (diameterGraph A).degree v)
    {x y : {z // z ∈ A}} (hxy : (diameterGraph A).Adj x y) :
    Set.range (redHalfPath hA hmin hxy) ∩
        Set.range (blueHalfPath hA hmin hxy) = {edgeDirection x y} := by
  rw [range_redHalfPath hA hmin hxy, range_blueHalfPath hA hmin hxy]
  apply Set.Subset.antisymm
  · intro p hp
    rw [Set.mem_singleton_iff]
    obtain ⟨hleft, hblue⟩ := hp
    have hnegRight := neg_mem_rightRange_of_mem_blueRange hA hmin hxy hblue
    have hpX := leftRange_subset_region hA hmin hxy hleft
    have hnegpY := path_range_subset_region hA hmin (rightIndex hxy) hnegRight
    exact (eq_direction_of_mem_region_and_neg_mem_region
      x.prop y.prop (diameter_norm_bound hA) hpX hnegpY).1
  · intro p hp
    rw [Set.mem_singleton_iff] at hp
    subst p
    constructor
    · exact Path.target_mem_range _
    · rw [Set.mem_neg]
      simpa [direction, rightIndex, edgeDirection] using
        Path.target_mem_range (path hA hmin (rightIndex hxy))

theorem redBluePath_injective
    (hA : IsDiameterOne A)
    (hmin : ∀ v : {z // z ∈ A}, 2 ≤ (diameterGraph A).degree v)
    {x y : {z // z ∈ A}} (hxy : (diameterGraph A).Adj x y) :
    Function.Injective (redBluePath hA hmin hxy) := by
  exact Path.trans_injective_of_injective_of_range_inter_eq_singleton
    (redHalfPath hA hmin hxy) (blueHalfPath hA hmin hxy)
    (redHalfPath_injective hA hmin hxy) (blueHalfPath_injective hA hmin hxy)
    (redHalfPath_range_inter_blueHalfPath_range hA hmin hxy)

end

end Erdos223.SphericalEuler.GlobalDoubleCover

open Metric Set
open scoped EuclideanGeometry RealInnerProductSpace SimpleGraph

namespace Erdos223.SphericalEuler.GlobalDoubleCover

noncomputable section

open DiameterRadialFan

variable {A : Finset (Point 3)}

local instance pointThreeFinrankFact : Fact (Module.finrank ℝ (Point 3) = 2 + 1) :=
  ⟨by norm_num [Point]⟩

lemma norm_redBluePath
    (hA : IsDiameterOne A)
    (hmin : ∀ v : {z // z ∈ A}, 2 ≤ (diameterGraph A).degree v)
    {x y : {z // z ∈ A}} (hxy : (diameterGraph A).Adj x y)
    (t : unitInterval) :
    ‖(redBluePath hA hmin hxy) t‖ = 1 := by
  have ht : (redBluePath hA hmin hxy) t ∈
      Set.range (redBluePath hA hmin hxy) := ⟨t, rfl⟩
  rw [range_redBluePath hA hmin hxy] at ht
  rcases ht with ht | ht
  · exact (leftRange_subset_region hA hmin hxy ht).1
  · have hb := blueRange_subset_neg_region hA hmin hxy ht
    rw [Set.mem_neg] at hb
    simpa using hb.1

lemma norm_redBase
    (hA : IsDiameterOne A)
    (hmin : ∀ v : {z // z ∈ A}, 2 ≤ (diameterGraph A).degree v)
    {x y : {z // z ∈ A}} (hxy : (diameterGraph A).Adj x y) :
    ‖redBase A x‖ = 1 := by
  rw [← Path.source (redBluePath hA hmin hxy)]
  exact norm_redBluePath hA hmin hxy 0

lemma norm_blueBase
    (hA : IsDiameterOne A)
    (hmin : ∀ v : {z // z ∈ A}, 2 ≤ (diameterGraph A).degree v)
    {x y : {z // z ∈ A}} (hxy : (diameterGraph A).Adj x y) :
    ‖blueBase A y‖ = 1 := by
  rw [← Path.target (redBluePath hA hmin hxy)]
  exact norm_redBluePath hA hmin hxy 1

def sphereRedBluePath
    (hA : IsDiameterOne A)
    (hmin : ∀ v : {z // z ∈ A}, 2 ≤ (diameterGraph A).degree v)
    {x y : {z // z ∈ A}} (hxy : (diameterGraph A).Adj x y) :
    Path
      (⟨redBase A x, mem_sphere_zero_iff_norm.2 (norm_redBase hA hmin hxy)⟩ :
        sphere (0 : Point 3) 1)
      (⟨blueBase A y, mem_sphere_zero_iff_norm.2 (norm_blueBase hA hmin hxy)⟩ :
        sphere (0 : Point 3) 1) where
  toFun t := ⟨(redBluePath hA hmin hxy) t,
    mem_sphere_zero_iff_norm.2 (norm_redBluePath hA hmin hxy t)⟩
  continuous_toFun := (redBluePath hA hmin hxy).continuous.subtype_mk _
  source' := Subtype.ext (Path.source (redBluePath hA hmin hxy))
  target' := Subtype.ext (Path.target (redBluePath hA hmin hxy))

@[simp]
lemma sphereRedBluePath_coe
    (hA : IsDiameterOne A)
    (hmin : ∀ v : {z // z ∈ A}, 2 ≤ (diameterGraph A).degree v)
    {x y : {z // z ∈ A}} (hxy : (diameterGraph A).Adj x y) (t : unitInterval) :
    ((sphereRedBluePath hA hmin hxy t : sphere (0 : Point 3) 1) : Point 3) =
      redBluePath hA hmin hxy t := rfl

lemma sphereRedBluePath_injective
    (hA : IsDiameterOne A)
    (hmin : ∀ v : {z // z ∈ A}, 2 ≤ (diameterGraph A).degree v)
    {x y : {z // z ∈ A}} (hxy : (diameterGraph A).Adj x y) :
    Function.Injective (sphereRedBluePath hA hmin hxy) := by
  intro t s hts
  apply redBluePath_injective hA hmin hxy
  exact congrArg Subtype.val hts

lemma sphereRedBluePath_range_subset_stereographic_source
    (hA : IsDiameterOne A)
    (hmin : ∀ v : {z // z ∈ A}, 2 ≤ (diameterGraph A).degree v)
    {z : Point 3} (hz : ‖z‖ = 1)
    (havoid : ∀ {x y : {z // z ∈ A}} (hxy : (diameterGraph A).Adj x y),
      z ∉ Set.range (redBluePath hA hmin hxy))
    {x y : {z // z ∈ A}} (hxy : (diameterGraph A).Adj x y) :
    Set.range (sphereRedBluePath hA hmin hxy) ⊆
      (stereographic' 2
        (⟨z, mem_sphere_zero_iff_norm.2 hz⟩ : sphere (0 : Point 3) 1)).source := by
  rw [stereographic'_source]
  intro p hp hpole
  rw [Set.mem_singleton_iff] at hpole
  obtain ⟨t, rfl⟩ := hp
  apply havoid hxy
  refine ⟨t, ?_⟩
  exact congrArg Subtype.val hpole

def stereoRedBluePath
    (hA : IsDiameterOne A)
    (hmin : ∀ v : {z // z ∈ A}, 2 ≤ (diameterGraph A).degree v)
    {z : Point 3} (hz : ‖z‖ = 1)
    (havoid : ∀ {x y : {z // z ∈ A}} (hxy : (diameterGraph A).Adj x y),
      z ∉ Set.range (redBluePath hA hmin hxy))
    {x y : {z // z ∈ A}} (hxy : (diameterGraph A).Adj x y) :
    Path
      (stereographic' 2 ⟨z, mem_sphere_zero_iff_norm.2 hz⟩
        ⟨redBase A x, mem_sphere_zero_iff_norm.2 (norm_redBase hA hmin hxy)⟩)
      (stereographic' 2 ⟨z, mem_sphere_zero_iff_norm.2 hz⟩
        ⟨blueBase A y, mem_sphere_zero_iff_norm.2 (norm_blueBase hA hmin hxy)⟩) :=
  (sphereRedBluePath hA hmin hxy).map'
    ((stereographic' 2
      (⟨z, mem_sphere_zero_iff_norm.2 hz⟩ : sphere (0 : Point 3) 1)).continuousOn.mono
        (sphereRedBluePath_range_subset_stereographic_source hA hmin hz havoid hxy))

lemma stereoRedBluePath_injective
    (hA : IsDiameterOne A)
    (hmin : ∀ v : {z // z ∈ A}, 2 ≤ (diameterGraph A).degree v)
    {z : Point 3} (hz : ‖z‖ = 1)
    (havoid : ∀ {x y : {z // z ∈ A}} (hxy : (diameterGraph A).Adj x y),
      z ∉ Set.range (redBluePath hA hmin hxy))
    {x y : {z // z ∈ A}} (hxy : (diameterGraph A).Adj x y) :
    Function.Injective (stereoRedBluePath hA hmin hz havoid hxy) := by
  intro t s hts
  apply sphereRedBluePath_injective hA hmin hxy
  apply (stereographic' 2
    (⟨z, mem_sphere_zero_iff_norm.2 hz⟩ : sphere (0 : Point 3) 1)).injOn
  · apply sphereRedBluePath_range_subset_stereographic_source hA hmin hz havoid hxy
    exact ⟨t, rfl⟩
  · apply sphereRedBluePath_range_subset_stereographic_source hA hmin hz havoid hxy
    exact ⟨s, rfl⟩
  · exact hts

end

end Erdos223.SphericalEuler.GlobalDoubleCover
