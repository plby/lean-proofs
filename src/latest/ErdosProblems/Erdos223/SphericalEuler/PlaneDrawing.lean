import ErdosProblems.Erdos223.SphericalEuler.GlobalPaths
import Wikipedia.SchoenfliesTheorem.Graph.Redrawing
import Wikipedia.SchoenfliesTheorem.FaceCyclesLand
import Mathlib.Combinatorics.Graph.Simple
import Mathlib.Combinatorics.Graph.Maps

open Metric Set
open scoped BigOperators EuclideanGeometry RealInnerProductSpace SimpleGraph Graph

namespace Erdos223.SphericalEuler.GlobalDoubleCover

noncomputable section

open DiameterRadialFan

variable {A : Finset (Point 3)}

local instance pointThreeFinrankFactBridge : Fact (Module.finrank ℝ (Point 3) = 2 + 1) :=
  ⟨by norm_num [Point]⟩

def planePos
    (hA : IsDiameterOne A)
    (hmin : ∀ v : {z // z ∈ A}, 2 ≤ (diameterGraph A).degree v)
    (z : Point 3) (hz : ‖z‖ = 1) :
    ({z // z ∈ A} ⊕ {z // z ∈ A}) → Schoenflies.Plane :=
  fun v ↦ stereographic' 2
    (⟨z, mem_sphere_zero_iff_norm.2 hz⟩ : sphere (0 : Point 3) 1) (spherePos hA hmin v)

lemma spherePos_mem_stereographic_source
    (hA : IsDiameterOne A)
    (hmin : ∀ v : {z // z ∈ A}, 2 ≤ (diameterGraph A).degree v)
    {z : Point 3} (hz : ‖z‖ = 1)
    (havoid : ∀ {x y : {z // z ∈ A}} (hxy : (diameterGraph A).Adj x y),
      z ∉ Set.range (redBluePath hA hmin hxy))
    (v : {z // z ∈ A} ⊕ {z // z ∈ A}) :
    spherePos hA hmin v ∈
      (stereographic' 2
        (⟨z, mem_sphere_zero_iff_norm.2 hz⟩ : sphere (0 : Point 3) 1)).source := by
  rw [stereographic'_source]
  intro hv
  rw [Set.mem_singleton_iff] at hv
  cases v with
  | inl x =>
      have hcard : 0 < Fintype.card ((diameterGraph A).neighborSet x) := by
        rw [(diameterGraph A).card_neighborSet_eq_degree]
        exact lt_of_lt_of_le (by norm_num) (hmin x)
      let yi : (diameterGraph A).neighborSet x :=
        @Classical.choice _ (Fintype.card_pos_iff.mp hcard)
      let y : {z // z ∈ A} := yi.1
      have hxy : (diameterGraph A).Adj x y := yi.2
      apply havoid hxy
      refine ⟨0, ?_⟩
      have hval := congrArg Subtype.val hv
      simpa [spherePos] using hval
  | inr y =>
      have hcard : 0 < Fintype.card ((diameterGraph A).neighborSet y) := by
        rw [(diameterGraph A).card_neighborSet_eq_degree]
        exact lt_of_lt_of_le (by norm_num) (hmin y)
      let xi : (diameterGraph A).neighborSet y :=
        @Classical.choice _ (Fintype.card_pos_iff.mp hcard)
      let x : {z // z ∈ A} := xi.1
      have hyx : (diameterGraph A).Adj y x := xi.2
      apply havoid hyx.symm
      refine ⟨1, ?_⟩
      have hval := congrArg Subtype.val hv
      simpa [spherePos] using hval

lemma planePos_injective
    (hA : IsDiameterOne A)
    (hmin : ∀ v : {z // z ∈ A}, 2 ≤ (diameterGraph A).degree v)
    {z : Point 3} (hz : ‖z‖ = 1)
    (havoid : ∀ {x y : {z // z ∈ A}} (hxy : (diameterGraph A).Adj x y),
      z ∉ Set.range (redBluePath hA hmin hxy)) :
    Function.Injective (planePos hA hmin z hz) := by
  intro u v huv
  apply spherePos_injective hA hmin
  apply (stereographic' 2
    (⟨z, mem_sphere_zero_iff_norm.2 hz⟩ : sphere (0 : Point 3) 1)).injOn
  · exact spherePos_mem_stereographic_source hA hmin hz havoid u
  · exact spherePos_mem_stereographic_source hA hmin hz havoid v
  · exact huv

lemma exists_orientedDart_of_mem_doubleCover_edgeSet
    (e : Sym2 ({z // z ∈ A} ⊕ {z // z ∈ A}))
    (he : e ∈ (diameterGraph A).bipartiteDoubleCover.edgeSet) :
    ∃ d : (diameterGraph A).Dart,
      e = s(Sum.inl d.fst, Sum.inr d.snd) := by
  induction e using Sym2.inductionOn with
  | _ u v =>
      rw [SimpleGraph.mem_edgeSet] at he
      cases u with
      | inl x =>
          cases v with
          | inl y => simp at he
          | inr y => exact ⟨⟨(x, y), he⟩, rfl⟩
      | inr x =>
          cases v with
          | inl y => exact ⟨⟨(y, x), he.symm⟩, Sym2.eq_swap⟩
          | inr y => simp at he

noncomputable def orientedDart
    (e : Sym2 ({z // z ∈ A} ⊕ {z // z ∈ A}))
    (he : e ∈ (diameterGraph A).bipartiteDoubleCover.edgeSet) :
    (diameterGraph A).Dart :=
  Classical.choose (exists_orientedDart_of_mem_doubleCover_edgeSet e he)

lemma orientedDart_edge_eq
    (e : Sym2 ({z // z ∈ A} ⊕ {z // z ∈ A}))
    (he : e ∈ (diameterGraph A).bipartiteDoubleCover.edgeSet) :
    e = s(Sum.inl (orientedDart e he).fst, Sum.inr (orientedDart e he).snd) :=
  Classical.choose_spec (exists_orientedDart_of_mem_doubleCover_edgeSet e he)

def planeDoubleCoverGraph
    (hA : IsDiameterOne A)
    (hmin : ∀ v : {z // z ∈ A}, 2 ≤ (diameterGraph A).degree v)
    (z : Point 3) (hz : ‖z‖ = 1) :
    Graph Schoenflies.Plane (Sym2 ({z // z ∈ A} ⊕ {z // z ∈ A})) :=
  (Graph.ofSimpleGraph (diameterGraph A).bipartiteDoubleCover).map
    (planePos hA hmin z hz)

def planeEdgeDrawing
    (hA : IsDiameterOne A)
    (hmin : ∀ v : {z // z ∈ A}, 2 ≤ (diameterGraph A).degree v)
    {z : Point 3} (hz : ‖z‖ = 1)
    (havoid : ∀ {x y : {z // z ∈ A}} (hxy : (diameterGraph A).Adj x y),
      z ∉ Set.range (redBluePath hA hmin hxy)) :
    Sym2 ({z // z ∈ A} ⊕ {z // z ∈ A}) → ℝ → Schoenflies.Plane :=
  fun e ↦ if he : e ∈ (diameterGraph A).bipartiteDoubleCover.edgeSet then
    (stereoRedBluePath hA hmin hz havoid (orientedDart e he).adj).extend
  else fun _ ↦ 0

lemma planeEdgeDrawing_of_mem
    (hA : IsDiameterOne A)
    (hmin : ∀ v : {z // z ∈ A}, 2 ≤ (diameterGraph A).degree v)
    {z : Point 3} (hz : ‖z‖ = 1)
    (havoid : ∀ {x y : {z // z ∈ A}} (hxy : (diameterGraph A).Adj x y),
      z ∉ Set.range (redBluePath hA hmin hxy))
    (e : Sym2 ({z // z ∈ A} ⊕ {z // z ∈ A}))
    (he : e ∈ (diameterGraph A).bipartiteDoubleCover.edgeSet) :
    planeEdgeDrawing hA hmin hz havoid e =
      (stereoRedBluePath hA hmin hz havoid (orientedDart e he).adj).extend := by
  funext t
  simp only [planeEdgeDrawing]
  rw [dif_pos he]

lemma planeEdgeDrawing_zero
    (hA : IsDiameterOne A)
    (hmin : ∀ v : {z // z ∈ A}, 2 ≤ (diameterGraph A).degree v)
    {z : Point 3} (hz : ‖z‖ = 1)
    (havoid : ∀ {x y : {z // z ∈ A}} (hxy : (diameterGraph A).Adj x y),
      z ∉ Set.range (redBluePath hA hmin hxy))
    (e : Sym2 ({z // z ∈ A} ⊕ {z // z ∈ A}))
    (he : e ∈ (diameterGraph A).bipartiteDoubleCover.edgeSet) :
    planeEdgeDrawing hA hmin hz havoid e 0 =
      planePos hA hmin z hz (Sum.inl (orientedDart e he).fst) := by
  rw [planeEdgeDrawing_of_mem hA hmin hz havoid e he, Path.extend_zero]
  rfl

lemma planeEdgeDrawing_one
    (hA : IsDiameterOne A)
    (hmin : ∀ v : {z // z ∈ A}, 2 ≤ (diameterGraph A).degree v)
    {z : Point 3} (hz : ‖z‖ = 1)
    (havoid : ∀ {x y : {z // z ∈ A}} (hxy : (diameterGraph A).Adj x y),
      z ∉ Set.range (redBluePath hA hmin hxy))
    (e : Sym2 ({z // z ∈ A} ⊕ {z // z ∈ A}))
    (he : e ∈ (diameterGraph A).bipartiteDoubleCover.edgeSet) :
    planeEdgeDrawing hA hmin hz havoid e 1 =
      planePos hA hmin z hz (Sum.inr (orientedDart e he).snd) := by
  rw [planeEdgeDrawing_of_mem hA hmin hz havoid e he, Path.extend_one]
  rfl

lemma planeEdge_isLink
    (hA : IsDiameterOne A)
    (hmin : ∀ v : {z // z ∈ A}, 2 ≤ (diameterGraph A).degree v)
    {z : Point 3} (hz : ‖z‖ = 1)
    (havoid : ∀ {x y : {z // z ∈ A}} (hxy : (diameterGraph A).Adj x y),
      z ∉ Set.range (redBluePath hA hmin hxy))
    (e : Sym2 ({z // z ∈ A} ⊕ {z // z ∈ A}))
    (he : e ∈ (diameterGraph A).bipartiteDoubleCover.edgeSet) :
    (planeDoubleCoverGraph hA hmin z hz).IsLink e
      (planeEdgeDrawing hA hmin hz havoid e 0)
      (planeEdgeDrawing hA hmin hz havoid e 1) := by
  rw [planeEdgeDrawing_zero hA hmin hz havoid e he,
    planeEdgeDrawing_one hA hmin hz havoid e he]
  apply Graph.IsLink.map
  rw [Graph.ofSimpleGraph_isLink]
  exact ⟨orientedDart_edge_eq e he, he⟩

lemma planeEdge_param
    (hA : IsDiameterOne A)
    (hmin : ∀ v : {z // z ∈ A}, 2 ≤ (diameterGraph A).degree v)
    {z : Point 3} (hz : ‖z‖ = 1)
    (havoid : ∀ {x y : {z // z ∈ A}} (hxy : (diameterGraph A).Adj x y),
      z ∉ Set.range (redBluePath hA hmin hxy))
    (e : Sym2 ({z // z ∈ A} ⊕ {z // z ∈ A}))
    (he : e ∈ (diameterGraph A).bipartiteDoubleCover.edgeSet) :
    ContinuousOn (planeEdgeDrawing hA hmin hz havoid e) unitInterval ∧
      Set.InjOn (planeEdgeDrawing hA hmin hz havoid e) unitInterval ∧
      (planeDoubleCoverGraph hA hmin z hz).IsLink e
        (planeEdgeDrawing hA hmin hz havoid e 0)
        (planeEdgeDrawing hA hmin hz havoid e 1) := by
  rw [planeEdgeDrawing_of_mem hA hmin hz havoid e he]
  refine ⟨(Path.continuous_extend _).continuousOn, ?_, ?_⟩
  · intro a ha b hb hab
    have hab' :
        stereoRedBluePath hA hmin hz havoid (orientedDart e he).adj ⟨a, ha⟩ =
          stereoRedBluePath hA hmin hz havoid (orientedDart e he).adj ⟨b, hb⟩ := by
      rw [Path.extend_apply _ ha, Path.extend_apply _ hb] at hab
      exact hab
    have huv := stereoRedBluePath_injective hA hmin hz havoid
      (orientedDart e he).adj hab'
    exact congrArg Subtype.val huv
  · have hlink := planeEdge_isLink hA hmin hz havoid e he
    rw [planeEdgeDrawing_of_mem hA hmin hz havoid e he] at hlink
    exact hlink

lemma redBase_mem_range_redBluePath_iff
    (hA : IsDiameterOne A)
    (hmin : ∀ v : {z // z ∈ A}, 2 ≤ (diameterGraph A).degree v)
    (v : {z // z ∈ A}) {x y : {z // z ∈ A}}
    (hxy : (diameterGraph A).Adj x y) :
    redBase A v ∈ Set.range (redBluePath hA hmin hxy) ↔ v = x := by
  rw [range_redBluePath hA hmin hxy]
  constructor
  · rintro (hleft | hblue)
    · apply Subtype.ext
      exact eq_of_mem_two_diameterConeRegions v.prop x.prop (diameter_norm_bound hA)
        (redBase_mem_region hA hmin v) (leftRange_subset_region hA hmin hxy hleft)
    · have hnegRight := neg_mem_rightRange_of_mem_blueRange hA hmin hxy hblue
      have hnegY := path_range_subset_region hA hmin (rightIndex hxy) hnegRight
      obtain ⟨hdir, hnorm⟩ := eq_direction_of_mem_region_and_neg_mem_region
        v.prop y.prop (diameter_norm_bound hA) (redBase_mem_region hA hmin v) hnegY
      have hvy : (diameterGraph A).Adj v y := (diameterGraph_adj A v y).2 (by
        simpa [dist_eq_norm] using hnorm)
      exfalso
      apply direction_ne_redBase hA hmin (leftIndex hvy)
      simpa [direction, leftIndex, edgeDirection] using hdir.symm
  · rintro rfl
    exact Or.inl (Path.source_mem_range (path hA hmin (leftIndex hxy)))

lemma blueBase_mem_range_redBluePath_iff
    (hA : IsDiameterOne A)
    (hmin : ∀ v : {z // z ∈ A}, 2 ≤ (diameterGraph A).degree v)
    (v : {z // z ∈ A}) {x y : {z // z ∈ A}}
    (hxy : (diameterGraph A).Adj x y) :
    blueBase A v ∈ Set.range (redBluePath hA hmin hxy) ↔ v = y := by
  rw [range_redBluePath hA hmin hxy]
  constructor
  · rintro (hleft | hblue)
    · have hpX := leftRange_subset_region hA hmin hxy hleft
      have hneg : -blueBase A v = redBase A v := by simp [blueBase, redBase]
      obtain ⟨hdir, hnorm⟩ := eq_direction_of_mem_region_and_neg_mem_region
        x.prop v.prop (diameter_norm_bound hA) hpX
          (hneg ▸ redBase_mem_region hA hmin v)
      have hxv : (diameterGraph A).Adj x v := (diameterGraph_adj A x v).2 (by
        simpa [dist_eq_norm] using hnorm)
      exfalso
      apply direction_ne_redBase hA hmin (rightIndex hxv)
      have hdir' : (x : Point 3) - (v : Point 3) = redBase A v := by
        rw [← hneg, hdir]
        simp
      simpa [direction, rightIndex] using hdir'
    · have hnegRight := neg_mem_rightRange_of_mem_blueRange hA hmin hxy hblue
      rw [show -blueBase A v = redBase A v by simp [blueBase, redBase]] at hnegRight
      apply Subtype.ext
      exact eq_of_mem_two_diameterConeRegions v.prop y.prop (diameter_norm_bound hA)
        (redBase_mem_region hA hmin v)
        (path_range_subset_region hA hmin (rightIndex hxy) hnegRight)
  · rintro rfl
    exact Or.inr (by
      rw [Set.mem_neg]
      simpa [blueBase] using Path.source_mem_range (path hA hmin (rightIndex hxy)))

lemma planePos_mem_range_stereoRedBluePath_iff
    (hA : IsDiameterOne A)
    (hmin : ∀ v : {z // z ∈ A}, 2 ≤ (diameterGraph A).degree v)
    {z : Point 3} (hz : ‖z‖ = 1)
    (havoid : ∀ {x y : {z // z ∈ A}} (hxy : (diameterGraph A).Adj x y),
      z ∉ Set.range (redBluePath hA hmin hxy))
    (v : {z // z ∈ A} ⊕ {z // z ∈ A})
    {x y : {z // z ∈ A}} (hxy : (diameterGraph A).Adj x y) :
    planePos hA hmin z hz v ∈ Set.range (stereoRedBluePath hA hmin hz havoid hxy) ↔
      v = Sum.inl x ∨ v = Sum.inr y := by
  constructor
  · rintro ⟨t, ht⟩
    have hsphere : spherePos hA hmin v = sphereRedBluePath hA hmin hxy t := by
      apply (stereographic' 2
        (⟨z, mem_sphere_zero_iff_norm.2 hz⟩ : sphere (0 : Point 3) 1)).injOn
      · exact spherePos_mem_stereographic_source hA hmin hz havoid v
      · apply sphereRedBluePath_range_subset_stereographic_source hA hmin hz havoid hxy
        exact ⟨t, rfl⟩
      · exact ht.symm
    have hval := congrArg Subtype.val hsphere
    cases v with
    | inl v =>
        left
        apply congrArg Sum.inl
        apply (redBase_mem_range_redBluePath_iff hA hmin v hxy).1
        exact ⟨t, by simpa [spherePos] using hval.symm⟩
    | inr v =>
        right
        apply congrArg Sum.inr
        apply (blueBase_mem_range_redBluePath_iff hA hmin v hxy).1
        exact ⟨t, by simpa [spherePos] using hval.symm⟩
  · rintro (rfl | rfl)
    · exact Path.source_mem_range _
    · exact Path.target_mem_range _

lemma planePos_mem_edgeArc_iff
    (hA : IsDiameterOne A)
    (hmin : ∀ v : {z // z ∈ A}, 2 ≤ (diameterGraph A).degree v)
    {z : Point 3} (hz : ‖z‖ = 1)
    (havoid : ∀ {x y : {z // z ∈ A}} (hxy : (diameterGraph A).Adj x y),
      z ∉ Set.range (redBluePath hA hmin hxy))
    (v : {z // z ∈ A} ⊕ {z // z ∈ A})
    (e : Sym2 ({z // z ∈ A} ⊕ {z // z ∈ A}))
    (he : e ∈ (diameterGraph A).bipartiteDoubleCover.edgeSet) :
    planePos hA hmin z hz v ∈ Graph.edgeArc (planeEdgeDrawing hA hmin hz havoid) e ↔
      v = Sum.inl (orientedDart e he).fst ∨
        v = Sum.inr (orientedDart e he).snd := by
  rw [Graph.edgeArc]
  constructor
  · rintro ⟨t, ht, htv⟩
    have hrange : planePos hA hmin z hz v ∈
        Set.range (stereoRedBluePath hA hmin hz havoid (orientedDart e he).adj) := by
      refine ⟨⟨t, ht⟩, ?_⟩
      rw [← htv, planeEdgeDrawing_of_mem hA hmin hz havoid e he,
        Path.extend_apply _ ht]
    exact (planePos_mem_range_stereoRedBluePath_iff hA hmin hz havoid v
      (orientedDart e he).adj).1 hrange
  · rintro (rfl | rfl)
    · refine ⟨0, by simp, ?_⟩
      exact planeEdgeDrawing_zero hA hmin hz havoid e he
    · refine ⟨1, by simp, ?_⟩
      exact planeEdgeDrawing_one hA hmin hz havoid e he

lemma planeDoubleCoverGraph_vertexSet
    (hA : IsDiameterOne A)
    (hmin : ∀ v : {z // z ∈ A}, 2 ≤ (diameterGraph A).degree v)
    (z : Point 3) (hz : ‖z‖ = 1) :
    V(planeDoubleCoverGraph hA hmin z hz) = Set.range (planePos hA hmin z hz) := by
  ext p
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v, rfl⟩
  · rintro ⟨v, rfl⟩
    exact ⟨v, by simp, rfl⟩

lemma planeDrawing_vertex_mem_edgeArc
    (hA : IsDiameterOne A)
    (hmin : ∀ v : {z // z ∈ A}, 2 ≤ (diameterGraph A).degree v)
    {z : Point 3} (hz : ‖z‖ = 1)
    (havoid : ∀ {x y : {z // z ∈ A}} (hxy : (diameterGraph A).Adj x y),
      z ∉ Set.range (redBluePath hA hmin hxy))
    {e : Sym2 ({z // z ∈ A} ⊕ {z // z ∈ A})}
    {p q v : Schoenflies.Plane}
    (hl : (planeDoubleCoverGraph hA hmin z hz).IsLink e p q)
    (hv : v ∈ V(planeDoubleCoverGraph hA hmin z hz))
    (hve : v ∈ Graph.edgeArc (planeEdgeDrawing hA hmin hz havoid) e) :
    v = p ∨ v = q := by
  have he : e ∈ (diameterGraph A).bipartiteDoubleCover.edgeSet := hl.edge_mem
  rw [planeDoubleCoverGraph_vertexSet hA hmin z hz] at hv
  obtain ⟨u, rfl⟩ := hv
  have hu := (planePos_mem_edgeArc_iff hA hmin hz havoid u e he).1 hve
  have hcanonical := planeEdge_isLink hA hmin hz havoid e he
  rcases hl.eq_and_eq_or_eq_and_eq hcanonical with h | h
  · rcases h with ⟨rfl, rfl⟩
    rcases hu with rfl | rfl
    · exact Or.inl (planeEdgeDrawing_zero hA hmin hz havoid e he).symm
    · exact Or.inr (planeEdgeDrawing_one hA hmin hz havoid e he).symm
  · rcases h with ⟨rfl, rfl⟩
    rcases hu with rfl | rfl
    · exact Or.inr (planeEdgeDrawing_zero hA hmin hz havoid e he).symm
    · exact Or.inl (planeEdgeDrawing_one hA hmin hz havoid e he).symm

lemma planeDrawing_edge_inter
    (hA : IsDiameterOne A)
    (hmin : ∀ v : {z // z ∈ A}, 2 ≤ (diameterGraph A).degree v)
    {z : Point 3} (hz : ‖z‖ = 1)
    (havoid : ∀ {x y : {z // z ∈ A}} (hxy : (diameterGraph A).Adj x y),
      z ∉ Set.range (redBluePath hA hmin hxy))
    {e f : Sym2 ({z // z ∈ A} ⊕ {z // z ∈ A})}
    (he : e ∈ E(planeDoubleCoverGraph hA hmin z hz))
    (hf : f ∈ E(planeDoubleCoverGraph hA hmin z hz)) (hef : e ≠ f)
    {p : Schoenflies.Plane}
    (hpe : p ∈ Graph.edgeArc (planeEdgeDrawing hA hmin hz havoid) e)
    (hpf : p ∈ Graph.edgeArc (planeEdgeDrawing hA hmin hz havoid) f) :
    p ∈ V(planeDoubleCoverGraph hA hmin z hz) ∧
      (planeDoubleCoverGraph hA hmin z hz).Inc e p ∧
      (planeDoubleCoverGraph hA hmin z hz).Inc f p := by
  have he' : e ∈ (diameterGraph A).bipartiteDoubleCover.edgeSet := he
  have hf' : f ∈ (diameterGraph A).bipartiteDoubleCover.edgeSet := hf
  let de := orientedDart e he'
  let df := orientedDart f hf'
  obtain ⟨t, htI, htp⟩ := hpe
  obtain ⟨s, hsI, hsp⟩ := hpf
  have hstereo :
      stereoRedBluePath hA hmin hz havoid de.adj ⟨t, htI⟩ =
        stereoRedBluePath hA hmin hz havoid df.adj ⟨s, hsI⟩ := by
    rw [← Path.extend_apply _ htI, ← Path.extend_apply _ hsI]
    rw [← planeEdgeDrawing_of_mem hA hmin hz havoid e he',
      ← planeEdgeDrawing_of_mem hA hmin hz havoid f hf']
    exact htp.trans hsp.symm
  have hsphere :
      sphereRedBluePath hA hmin de.adj ⟨t, htI⟩ =
        sphereRedBluePath hA hmin df.adj ⟨s, hsI⟩ := by
    apply (stereographic' 2
      (⟨z, mem_sphere_zero_iff_norm.2 hz⟩ : sphere (0 : Point 3) 1)).injOn
    · apply sphereRedBluePath_range_subset_stereographic_source hA hmin hz havoid de.adj
      exact ⟨⟨t, htI⟩, rfl⟩
    · apply sphereRedBluePath_range_subset_stereographic_source hA hmin hz havoid df.adj
      exact ⟨⟨s, hsI⟩, rfl⟩
    · exact hstereo
  have hraw :
      redBluePath hA hmin de.adj ⟨t, htI⟩ =
        redBluePath hA hmin df.adj ⟨s, hsI⟩ :=
    congrArg Subtype.val hsphere
  by_cases hred : de.fst = df.fst
  · have hblue : de.snd ≠ df.snd := by
      intro hblue
      apply hef
      rw [orientedDart_edge_eq e he', orientedDart_edge_eq f hf', hred, hblue]
    have hadjg : (diameterGraph A).Adj de.fst df.snd := by
      rw [hred]
      exact df.adj
    let dg : (diameterGraph A).Dart := ⟨(de.fst, df.snd), hadjg⟩
    have hdg : dg = df := by
      exact SimpleGraph.Dart.ext dg df (Prod.ext hred rfl)
    have hinter : redBluePath hA hmin de.adj ⟨t, htI⟩ ∈
        Set.range (redBluePath hA hmin de.adj) ∩
          Set.range (redBluePath hA hmin df.adj) :=
      ⟨⟨⟨t, htI⟩, rfl⟩, ⟨⟨s, hsI⟩, hraw.symm⟩⟩
    rw [← hdg] at hinter
    rw [redBluePath_ranges_inter_eq_redBase hA hmin de.adj
      dg.adj hblue, Set.mem_singleton_iff] at hinter
    have ht0 : (⟨t, htI⟩ : unitInterval) = 0 :=
      redBluePath_injective hA hmin de.adj (by
        rw [hinter]
        exact (Path.source _).symm)
    have hpPos : p = planePos hA hmin z hz (Sum.inl de.fst) := by
      have htval : t = 0 := congrArg Subtype.val ht0
      calc
        p = planeEdgeDrawing hA hmin hz havoid e t := htp.symm
        _ = planeEdgeDrawing hA hmin hz havoid e 0 := by rw [htval]
        _ = planePos hA hmin z hz (Sum.inl de.fst) :=
          planeEdgeDrawing_zero hA hmin hz havoid e he'
    have hlinke := planeEdge_isLink hA hmin hz havoid e he'
    have hlinkf := planeEdge_isLink hA hmin hz havoid f hf'
    have hince := hlinke.inc_left
    have hincf := hlinkf.inc_left
    rw [planeEdgeDrawing_zero hA hmin hz havoid e he'] at hince
    rw [planeEdgeDrawing_zero hA hmin hz havoid f hf', ← hred] at hincf
    rw [hpPos]
    refine ⟨?_, hince, hincf⟩
    rw [planeDoubleCoverGraph_vertexSet hA hmin z hz]
    exact ⟨Sum.inl de.fst, rfl⟩
  · by_cases hblue : de.snd = df.snd
    · have hadjg : (diameterGraph A).Adj df.fst de.snd := by
        rw [hblue]
        exact df.adj
      let dg : (diameterGraph A).Dart := ⟨(df.fst, de.snd), hadjg⟩
      have hdg : dg = df := by
        exact SimpleGraph.Dart.ext dg df (Prod.ext rfl hblue)
      have hinter : redBluePath hA hmin de.adj ⟨t, htI⟩ ∈
          Set.range (redBluePath hA hmin de.adj) ∩
            Set.range (redBluePath hA hmin df.adj) :=
        ⟨⟨⟨t, htI⟩, rfl⟩, ⟨⟨s, hsI⟩, hraw.symm⟩⟩
      rw [← hdg] at hinter
      rw [redBluePath_ranges_inter_eq_blueBase hA hmin de.adj
        dg.adj hred, Set.mem_singleton_iff] at hinter
      have ht1 : (⟨t, htI⟩ : unitInterval) = 1 :=
        redBluePath_injective hA hmin de.adj (by
          rw [hinter]
          exact (Path.target _).symm)
      have hpPos : p = planePos hA hmin z hz (Sum.inr de.snd) := by
        have htval : t = 1 := congrArg Subtype.val ht1
        calc
          p = planeEdgeDrawing hA hmin hz havoid e t := htp.symm
          _ = planeEdgeDrawing hA hmin hz havoid e 1 := by rw [htval]
          _ = planePos hA hmin z hz (Sum.inr de.snd) :=
            planeEdgeDrawing_one hA hmin hz havoid e he'
      have hlinke := planeEdge_isLink hA hmin hz havoid e he'
      have hlinkf := planeEdge_isLink hA hmin hz havoid f hf'
      have hince := hlinke.inc_right
      have hincf := hlinkf.inc_right
      rw [planeEdgeDrawing_one hA hmin hz havoid e he'] at hince
      rw [planeEdgeDrawing_one hA hmin hz havoid f hf', ← hblue] at hincf
      rw [hpPos]
      refine ⟨?_, hince, hincf⟩
      rw [planeDoubleCoverGraph_vertexSet hA hmin z hz]
      exact ⟨Sum.inr de.snd, rfl⟩
    · have hinter : redBluePath hA hmin de.adj ⟨t, htI⟩ ∈
          Set.range (redBluePath hA hmin de.adj) ∩
            Set.range (redBluePath hA hmin df.adj) :=
        ⟨⟨⟨t, htI⟩, rfl⟩, ⟨⟨s, hsI⟩, hraw.symm⟩⟩
      rw [redBluePath_ranges_inter_eq_empty hA hmin de.adj df.adj hred hblue] at hinter
      exact False.elim hinter

theorem isDrawing_planeDoubleCoverGraph
    (hA : IsDiameterOne A)
    (hmin : ∀ v : {z // z ∈ A}, 2 ≤ (diameterGraph A).degree v)
    {z : Point 3} (hz : ‖z‖ = 1)
    (havoid : ∀ {x y : {z // z ∈ A}} (hxy : (diameterGraph A).Adj x y),
      z ∉ Set.range (redBluePath hA hmin hxy)) :
    Graph.IsDrawing (planeDoubleCoverGraph hA hmin z hz)
      (planeEdgeDrawing hA hmin hz havoid) where
  edge_param e he := planeEdge_param hA hmin hz havoid e he
  vertex_mem_edgeArc _ _ _ _ hl hv hve :=
    planeDrawing_vertex_mem_edgeArc hA hmin hz havoid hl hv hve
  edge_inter e f he hf hef p hpe hpf :=
    planeDrawing_edge_inter hA hmin hz havoid he hf hef hpe hpf

end


end Erdos223.SphericalEuler.GlobalDoubleCover

