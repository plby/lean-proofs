/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos110.Construction

/-!
# The finite-subgraph estimate

For a fixed stage `k`, high-label edges map to the `k`th Specker relation.
A spanning-forest argument makes that finite tail bipartite.  The remaining
`k` label layers already have their recursive two-colorings, and their
product uses `2^(k+1)` colors.
-/

noncomputable section

open Set

namespace Erdos110
namespace FiniteEstimate

open Blocks Construction GraphLemmas

variable (C : (a : Height.S) → Ordinal.Club a.1)
variable (q : ℕ → ℕ)

/-- The symmetric Specker graph used by block `k`. -/
def speckerGraph (k : ℕ) :
    SimpleGraph (Specker.IncSeq (blockWidth q k) (Set.Iio Height.lambda.ord)) :=
  SimpleGraph.fromRel fun a b ↦ Specker.Up (scale q k) a b

/-- High-label edges of a finite subgraph. -/
def tail (H : (graph C q).Subgraph) (k : ℕ) : SimpleGraph H.verts :=
  SimpleGraph.fromRel fun x y ↦
    H.coe.Adj x y ∧ ∃ j, k ≤ j ∧ Directed C q j x.1 y.1

private theorem blockWidth_large (k : ℕ) :
    scale q k + 1 < blockWidth q k := by
  simp [scale, blockWidth, Specker.width]

private theorem specker_adj_of_up {k : ℕ}
    {a b : Specker.IncSeq (blockWidth q k) (Set.Iio Height.lambda.ord)}
    (h : Specker.Up (scale q k) a b) : (speckerGraph q k).Adj a b := by
  rw [speckerGraph, SimpleGraph.fromRel_adj]
  refine ⟨?_, Or.inl h⟩
  intro hab
  subst b
  exact Specker.not_adj_self (blockWidth_large q k) (Or.inl h)

/-- The block map is a graph homomorphism from the high-label tail. -/
def tailHom (H : (graph C q).Subgraph) (k : ℕ) :
    tail C q H k →g speckerGraph q k where
  toFun x := tuple C q x.1.height k
  map_rel' := by
    intro x y hxy
    rw [tail, SimpleGraph.fromRel_adj] at hxy
    rcases hxy.2 with hxy | hyx
    · obtain ⟨_, j, hkj, hj⟩ := hxy
      apply specker_adj_of_up q
      exact (chosen_compatible C q hj) k hkj
    · obtain ⟨_, j, hkj, hj⟩ := hyx
      exact (specker_adj_of_up q ((chosen_compatible C q hj) k hkj)).symm

private theorem speckerGraph_no_short_odd_walk (k : ℕ)
    (u : Specker.IncSeq (blockWidth q k) (Set.Iio Height.lambda.ord))
    (p : (speckerGraph q k).Walk u u)
    (hodd : Odd p.length) (hlen : p.length ≤ q k) : False := by
  let v : ℕ → Specker.IncSeq (blockWidth q k) (Set.Iio Height.lambda.ord) :=
    fun i ↦ p.getVert i
  have hedge : ∀ j < p.length,
      Specker.Adj (scale q k) (v j) (v (j + 1)) := by
    intro j hj
    have ha := p.adj_getVert_succ hj
    change (SimpleGraph.fromRel (fun a b :
      Specker.IncSeq (blockWidth q k) (Set.Iio Height.lambda.ord) ↦
        Specker.Up (scale q k) a b)).Adj (v j) (v (j + 1)) at ha
    rw [SimpleGraph.fromRel_adj] at ha
    exact ha.2
  have hclosed : v p.length = v 0 := by
    simp [v, SimpleGraph.Walk.getVert_length]
  have hell : p.length ≤ 2 * scale q k + 1 := by
    dsimp [scale]
    omega
  exact Specker.no_short_odd_closed_walk (scale q k) p.length (by
      simp [scale]) hell (by
      simpa [blockWidth] using Specker.width_bound (scale q k) p.length hell)
    hodd v hedge hclosed

/-- The high-label part of every subgraph with at most `q k` vertices is
two-colorable. -/
theorem tail_colorable_two (H : (graph C q).Subgraph) (k : ℕ)
    [Fintype H.verts] (hcard : Fintype.card H.verts ≤ q k) :
    (tail C q H k).Colorable 2 := by
  apply colorable_two_of_hom_no_short_odd_walk
    (tail C q H k) (speckerGraph q k) (tailHom C q H k)
  intro u p hodd hlen
  exact speckerGraph_no_short_odd_walk q k u p hodd (hlen.trans hcard)

/-- Small subgraphs have the required exponential coloring bound. -/
theorem chromaticNumber_le (H : (graph C q).Subgraph) (k : ℕ)
    (hfin : H.verts.Finite) (hcard : H.verts.ncard ≤ q k) :
    H.coe.chromaticNumber ≤ (2 ^ (k + 1) : ℕ) := by
  classical
  let : Fintype H.verts := hfin.fintype
  have hcard' : Fintype.card H.verts ≤ q k := by
    rwa [Set.fintypeCard_eq_ncard]
  obtain ⟨ct⟩ := tail_colorable_two C q H k hcard'
  let ctBool : (tail C q H k).Coloring Bool :=
    (tail C q H k).recolorOfEquiv finTwoEquiv ct
  let color : H.coe.Coloring (Fin (k + 1) → Bool) :=
    SimpleGraph.Coloring.mk (fun x i ↦
      if hi : i.1 = 0 then ctBool x
      else layerColor C q (i.1 - 1) x.1) (by
        intro x y hxy
        have hglobal : (graph C q).Adj x.1 y.1 := H.coe_adj_sub x y hxy
        obtain ⟨j, hj | hj⟩ := adj_has_label C q hglobal
        · by_cases hkj : k ≤ j
          · have htail : (tail C q H k).Adj x y := by
              rw [tail, SimpleGraph.fromRel_adj]
              exact ⟨hxy.ne, Or.inl ⟨hxy, j, hkj, hj⟩⟩
            intro heq
            have := congrFun heq ⟨0, by omega⟩
            simp only [dif_pos rfl] at this
            exact ctBool.valid htail this
          · have hjk : j < k := by omega
            intro heq
            have := congrFun heq ⟨j + 1, by omega⟩
            simp only [dif_neg (by omega), Nat.add_sub_cancel] at this
            exact layerColor_ne C q hj this
        · by_cases hkj : k ≤ j
          · have htail : (tail C q H k).Adj x y := by
              rw [tail, SimpleGraph.fromRel_adj]
              exact ⟨hxy.ne, Or.inr ⟨hxy.symm, j, hkj, hj⟩⟩
            intro heq
            have := congrFun heq ⟨0, by omega⟩
            simp only [dif_pos rfl] at this
            exact ctBool.valid htail this
          · have hjk : j < k := by omega
            intro heq
            have := congrFun heq ⟨j + 1, by omega⟩
            simp only [dif_neg (by omega), Nat.add_sub_cancel] at this
            exact layerColor_ne C q hj this.symm)
  have hc := color.colorable
  simpa using hc.chromaticNumber_le

end FiniteEstimate
end Erdos110
