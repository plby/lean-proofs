import ErdosProblems.Erdos547.GEAvoidingDeficit
import ErdosProblems.Erdos547.GEAvoidingSupply
import ErdosProblems.Erdos547.AvoidingVertex
import ErdosProblems.Erdos547.AvoidingNumbers

/-!
# Constructing the second allocation in the general avoiding case
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

namespace GallaiEdmondsPartition

open scoped Classical in
theorem IsOptimalGEPair.exists_avoiding_allocation {D : GallaiEdmondsPartition G}
    {w : EdgeWeights G} {c e : V} {μ ν : FractionalMatching G}
    (A b₁ b₂ γ : ℝ) (hA : 0 < A) (hb₁ : 0 < b₁) (hb₂ : b₁ < b₂) (hγ : 0 ≤ γ)
    {σ : SkewMatching G (b₂ / b₁)}
    (h : D.IsOptimalGEPair w c μ σ ν) (hm : D.IsMaxSaturation w c μ)
    (he : e ∈ D.reachableVertices w c μ)
    (hdef : σ.load e + ν.load e < w.weight c e)
    (hσ : σ.total ≤ b₁ + b₂) (hhigh : A + b₁ + b₂ ≤ w.degree c)
    (hdeg : ∀ z, (A + b₁ + b₂) / 2 ≤ w.degree z)
    (hsmall : ((D.reachableVertices w c μ ∪ D.fullFlabellumExtra w c μ e b₁).card : ℝ) < b₂)
    (ρ : SkewMatching G (b₂ / b₁))
    (hρ : ρ.DominatedByFractional (ν.touching (Finset.univ.filter (G.Adj e) : Set V)))
    (htρ : ρ.total = (1 + b₂ / b₁) / (b₂ / b₁) *
      (ν.touching (Finset.univ.filter (G.Adj e) : Set V)).total)
    (hc : ∀ u, σ.load u + ρ.load u ≤ 1) (hbudget : σ.total + ρ.total < b₁ + b₂) :
    ∃ d : V, ∃ α : SkewMatching G γ, G.Adj c d ∧ α.total = A ∧
      α.Fits (w.truncate (σ.add ρ hc).load (σ.add ρ hc).load_nonneg) d ∧
      (∀ u, α.load u + (σ.add ρ hc).load u ≤ 1) ∧
      ∀ u ∉ D.avoidingFreeSet w c μ σ ν (Finset.univ.filter (G.Adj e)), α.load u = 0 := by
  classical
  let R := D.reachableVertices w c μ
  let X := D.fullFlabellumExtra w c μ e b₁
  let C := Finset.univ.filter (G.Adj e)
  let U := D.avoidingFreeSet w c μ σ ν C
  let β := σ.add ρ hc
  let good := D.singletonVertices \ (R ∪ X)
  let D₀ := (R.card : ℝ) + X.card - (∑ u ∈ R, σ.load u) - (ν.touching (C : Set V)).total
  have hratio : 1 < b₂ / b₁ := (one_lt_div hb₁).mpr hb₂
  have hpos : 0 < b₂ / b₁ := zero_lt_one.trans hratio
  have hC : C ⊆ D.reachableNeighbours w c μ := fun u hu ↦
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, e, he, (Finset.mem_filter.mp hu).2⟩
  have hCeq (u : V) (hu : u ∈ C) : w.weight c u = σ.outLoad u :=
    (IsOptimalGEPair.separation_one hm h hratio he hdef (Finset.mem_filter.mp hu).2).symm
  have hhead : σ.total / (1 + b₂ / b₁) ≤ b₁ := by
    apply (div_le_div_of_nonneg_right hσ σ.denominator_pos.le).trans_eq
    exact (skew_parts_of_sum b₁ b₂ hb₁ (hb₁.le.trans hb₂.le)).1
  have hroom : ((R ∪ X).card : ℝ) + σ.total / (1 + b₂ / b₁) < w.degree c := by
    change ((R ∪ X).card : ℝ) < b₂ at hsmall
    linarith
  obtain ⟨d, hd, hslack, _⟩ := exists_maximal_avoiding_vertex w c σ (R ∪ X) C hCeq hroom
  have hdR : d ∉ R := fun hu ↦ hd (Finset.mem_union_left _ (Finset.mem_union_left _ hu))
  have hdX : d ∉ X := fun hu ↦ hd (Finset.mem_union_left _ (Finset.mem_union_right _ hu))
  have hdC : ¬ G.Adj e d := fun hu ↦ hd
    (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu⟩))
  have hcd : G.Adj c d := by
    by_contra hn
    rw [w.supported c d hn] at hslack
    exact (not_lt_of_ge (σ.outLoad_nonneg d)) hslack
  have hN := h.no_covered_neighbour_of_slack hm hratio he hdef C
    (fun _ hu ↦ (Finset.mem_filter.mp hu).2) hslack
  have hsupply := h.1.avoiding_degree_supply b₁ b₂ (A + b₁ + b₂) hb₁ hb₂.le
    (by linarith) hm he (hdeg e) (hdeg d) hdR hdC hdX hN ρ hρ htρ hc
  have hgood (z : V) (hz : z ∈ good) : A ≤ w.degreeOn U z - ∑ u ∈ U, β.load u := by
    have hzs := (Finset.mem_sdiff.mp hz).1
    have hzRX := (Finset.mem_sdiff.mp hz).2
    have hzR : z ∉ R := fun hh ↦ hzRX (Finset.mem_union_left _ hh)
    have hzX : z ∉ X := fun hh ↦ hzRX (Finset.mem_union_right _ hh)
    have hzC : ¬ G.Adj e z := fun hez ↦ D.singleton_not_separator hzs
      (D.neighbour_of_singleton_mem_separator (hm.reachable_singleton he) hez)
    have hh := h.1.avoiding_degree_supply b₁ b₂ (A + b₁ + b₂) hb₁ hb₂.le
      (by linarith) hm he (hdeg e) (hdeg z) hzR hzC hzX
      (hm.no_covered_neighbour_of_singleton C hzs) ρ hρ htρ hc
    change A + b₁ + b₂ - (σ.total + ρ.total) ≤ w.degreeOn U z - ∑ u ∈ U, β.load u at hh
    linarith
  have hRX : Disjoint R X := Finset.disjoint_left.mpr fun z hz hx ↦
    (Finset.mem_filter.mp hx).2.1 hz
  have hcards : (R.card : ℝ) + X.card < b₂ := by
    change ((R ∪ X).card : ℝ) < b₂ at hsmall
    rwa [Finset.card_union_of_disjoint hRX, Nat.cast_add] at hsmall
  have htail : (∑ u ∈ R, σ.load u) + (ν.touching (C : Set V)).total =
      (b₂ / b₁) * (σ.total + ρ.total) / (1 + b₂ / b₁) := by
    rw [h.1.reachable_skew_load hm]
    exact reverse_tail_identity _ _ _ _ hpos htρ
  have hD : D₀ < b₁ + b₂ - (σ.total + ρ.total) := by
    have hh := deficit_lt_remaining (b₂ / b₁) (b₁ + b₂) (σ.total + ρ.total)
      ((R.card : ℝ) + X.card) hpos.le hbudget
      (by rwa [mul_div_assoc, (skew_parts_of_sum b₁ b₂ hb₁ (hb₁.le.trans hb₂.le)).2])
    dsimp [D₀]
    rw [sub_sub, htail]
    exact hh
  obtain ⟨μ₀, hbase, hbad⟩ := h.1.exists_avoiding_baseline hm C X hC ρ hρ hc d
  have hsize : A + D₀ ≤ w.degreeOn U d - ∑ u ∈ U, β.load u := by
    change A + b₁ + b₂ - (σ.total + ρ.total) ≤ w.degreeOn U d - ∑ u ∈ U, β.load u at hsupply
    linarith
  obtain ⟨α, ht, hfit, hcap, hz⟩ := exists_skew_on_free_set_of_deficit_bound w d β U good
    A D₀ γ hA.le hγ μ₀ hbase hgood hbad hsize
  exact ⟨d, α, hcd, ht, hfit, hcap, hz⟩

end GallaiEdmondsPartition

end Erdos547.DPRS

#print axioms Erdos547.DPRS.GallaiEdmondsPartition.IsOptimalGEPair.exists_avoiding_allocation
