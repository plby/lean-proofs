import ErdosProblems.Erdos547.GEAlternatingReachability

/-!
# Reachable singleton sets and their separator neighbourhoods
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

omit [DecidableEq V] in
theorem FractionalMatching.adj_of_weight_pos (μ : FractionalMatching G) {u v : V}
    (h : 0 < μ.weight u v) : G.Adj u v := by
  by_contra hn
  rw [μ.supported u v hn] at h
  exact (lt_irrefl 0) h

omit [DecidableEq V] in
theorem FractionalMatching.load_pos_of_weight_pos (μ : FractionalMatching G) {u v : V}
    (h : 0 < μ.weight u v) : 0 < μ.load u :=
  h.trans_le (Finset.single_le_sum (fun x _ ↦ μ.nonnegative u x) (Finset.mem_univ v))

namespace GallaiEdmondsPartition

open scoped Classical in
def reachableVertices (D : GallaiEdmondsPartition G) (w : EdgeWeights G) (c : V)
    (μ : FractionalMatching G) : Finset V := Finset.univ.filter fun u ↦
  ∃ x ∈ D.singletonVertices, μ.load x < w.weight c x ∧
    Relation.ReflTransGen (AlternatingStep μ) x u

open scoped Classical in
def reachableNeighbours (D : GallaiEdmondsPartition G) (w : EdgeWeights G) (c : V)
    (μ : FractionalMatching G) : Finset V := Finset.univ.filter fun y ↦
  ∃ x ∈ D.reachableVertices w c μ, G.Adj x y

theorem IsMaxSaturation.reachable_singleton {D : GallaiEdmondsPartition G}
    {w : EdgeWeights G} {c : V} {μ : FractionalMatching G}
    (h : D.IsMaxSaturation w c μ) {u : V} (hu : u ∈ D.reachableVertices w c μ) :
    u ∈ D.singletonVertices := by
  classical
  obtain ⟨x, hx, hdef, hr⟩ := (Finset.mem_filter.mp hu).2
  exact (h.alternating_properties hx hdef hr).1

theorem IsMaxSaturation.reachable_load_le {D : GallaiEdmondsPartition G}
    {w : EdgeWeights G} {c : V} {μ : FractionalMatching G}
    (h : D.IsMaxSaturation w c μ) {u : V} (hu : u ∈ D.reachableVertices w c μ) :
    μ.load u ≤ w.weight c u := by
  classical
  obtain ⟨x, hx, hdef, hr⟩ := (Finset.mem_filter.mp hu).2
  cases hr with
  | refl => exact hdef.le
  | @tail v u hr hs =>
    obtain ⟨y, hvy, hyp⟩ := hs
    exact ((h.alternating_properties hx hdef hr).2 y hvy).2 u hyp |>.2

theorem IsMaxSaturation.reachable_weight_pos {D : GallaiEdmondsPartition G}
    {w : EdgeWeights G} {c : V} {μ : FractionalMatching G}
    (h : D.IsMaxSaturation w c μ) {u : V} (hu : u ∈ D.reachableVertices w c μ) :
    0 < w.weight c u := by
  classical
  have hle := h.reachable_load_le hu
  obtain ⟨x, hx, hdef, hr⟩ := (Finset.mem_filter.mp hu).2
  cases hr with
  | refl => exact (μ.load_nonneg _).trans_lt hdef
  | tail _ hs =>
    obtain ⟨y, _, hyp⟩ := hs
    have hp : 0 < μ.weight u y := by rw [μ.symmetric u y]; exact hyp
    exact (μ.load_pos_of_weight_pos hp).trans_le hle

theorem IsMaxSaturation.reachable_neighbour_separator {D : GallaiEdmondsPartition G}
    {w : EdgeWeights G} {c : V} {μ : FractionalMatching G}
    (h : D.IsMaxSaturation w c μ) {u : V} (hu : u ∈ D.reachableNeighbours w c μ) :
    u ∈ D.separator := by
  classical
  obtain ⟨x, hx, hxu⟩ := (Finset.mem_filter.mp hu).2
  exact D.neighbour_of_singleton_mem_separator (h.reachable_singleton hx) hxu

theorem reachable_partner_mem (D : GallaiEdmondsPartition G) (w : EdgeWeights G)
    (c : V) (μ : FractionalMatching G) {y z : V} (hy : y ∈ D.reachableNeighbours w c μ)
    (hyz : 0 < μ.weight y z) : z ∈ D.reachableVertices w c μ := by
  classical
  obtain ⟨u, hu, huy⟩ := (Finset.mem_filter.mp hy).2
  obtain ⟨x, hx, hdef, hr⟩ := (Finset.mem_filter.mp hu).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, x, hx, hdef, hr.tail ⟨y, huy, hyz⟩⟩

theorem reachable_neighbour_mem (D : GallaiEdmondsPartition G) (w : EdgeWeights G)
    (c : V) (μ : FractionalMatching G) {x y : V} (hx : x ∈ D.reachableVertices w c μ)
    (hxy : 0 < μ.weight x y) : y ∈ D.reachableNeighbours w c μ := by
  classical
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, x, hx, μ.adj_of_weight_pos hxy⟩

theorem reachable_load_sum_eq (D : GallaiEdmondsPartition G) (w : EdgeWeights G)
    (c : V) (μ : FractionalMatching G) :
    (∑ x ∈ D.reachableVertices w c μ, μ.load x) =
      ∑ y ∈ D.reachableNeighbours w c μ, μ.load y := by
  classical
  let R := D.reachableVertices w c μ
  let S := D.reachableNeighbours w c μ
  have hrow (x : V) (hx : x ∈ R) : μ.load x = ∑ y ∈ S, μ.weight x y := by
    symm
    apply Finset.sum_subset (Finset.subset_univ S)
    intro y _ hy
    apply le_antisymm _ (μ.nonnegative x y)
    exact le_of_not_gt (fun hp ↦ hy (D.reachable_neighbour_mem w c μ hx hp))
  have hcol (y : V) (hy : y ∈ S) : μ.load y = ∑ x ∈ R, μ.weight y x := by
    symm
    apply Finset.sum_subset (Finset.subset_univ R)
    intro x _ hx
    apply le_antisymm _ (μ.nonnegative y x)
    exact le_of_not_gt (fun hp ↦ hx (D.reachable_partner_mem w c μ hy hp))
  change (∑ x ∈ R, μ.load x) = ∑ y ∈ S, μ.load y
  calc
    _ = ∑ x ∈ R, ∑ y ∈ S, μ.weight x y := Finset.sum_congr rfl hrow
    _ = ∑ y ∈ S, ∑ x ∈ R, μ.weight x y := Finset.sum_comm
    _ = ∑ y ∈ S, ∑ x ∈ R, μ.weight y x := by
      apply Finset.sum_congr rfl
      intro y _
      exact Finset.sum_congr rfl fun x _ ↦ μ.symmetric x y
    _ = _ := Finset.sum_congr rfl fun y hy ↦ (hcol y hy).symm

theorem IsMaxSaturation.reachable_card_bound {D : GallaiEdmondsPartition G}
    {w : EdgeWeights G} {c : V} {μ : FractionalMatching G}
    (h : D.IsMaxSaturation w c μ) :
    (D.reachableNeighbours w c μ).card ≤ (D.reachableVertices w c μ).card := by
  have hsum := D.reachable_load_sum_eq w c μ
  have hS : (∑ y ∈ D.reachableNeighbours w c μ, μ.load y) =
      ((D.reachableNeighbours w c μ).card : ℝ) := by
    calc
      _ = ∑ _y ∈ D.reachableNeighbours w c μ, (1 : ℝ) :=
        Finset.sum_congr rfl fun y hy ↦ h.1.load_separator (h.reachable_neighbour_separator hy)
      _ = _ := by simp
  have hR : (∑ x ∈ D.reachableVertices w c μ, μ.load x) ≤
      ((D.reachableVertices w c μ).card : ℝ) := by
    calc
      _ ≤ ∑ _x ∈ D.reachableVertices w c μ, (1 : ℝ) :=
        Finset.sum_le_sum fun x _ ↦ μ.load_le_one x
      _ = _ := by simp
  rw [hsum, hS] at hR
  exact_mod_cast hR

end GallaiEdmondsPartition

end Erdos547.DPRS

#print axioms Erdos547.DPRS.GallaiEdmondsPartition.IsMaxSaturation.reachable_card_bound
