import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Data.Set.Card

/-!
# Evenness from a finite incidence count

For a finite relation, suppose each edge meets two vertices, while a specified
subset of vertices has degree one and all other vertices have degree two.
Double counting the actual relation then proves that the specified subset has
even cardinality. Distinct edges are retained even if their endpoint sets agree.
-/

open Set Function
open scoped BigOperators

namespace NoExoticSixSphere.CurveDecomposition

theorem even_ncard_of_incidence {V E : Type*} (vertices : Set V) (edges : Set E)
    (hvfin : vertices.Finite) (hefin : edges.Finite) (B : Set V) (hBV : B ⊆ vertices)
    (r : V → E → Prop)
    (hboundary : ∀ v ∈ B, {e ∈ edges | r v e}.ncard = 1)
    (hinterior : ∀ v ∈ vertices, v ∉ B → {e ∈ edges | r v e}.ncard = 2)
    (hedges : ∀ e ∈ edges, {v ∈ vertices | r v e}.ncard = 2) : Even B.ncard := by
  classical
  let vs := hvfin.toFinset
  let es := hefin.toFinset
  have hrow (v : V) (hv : v ∈ vs) :
      (es.bipartiteAbove r v).card = if v ∈ B then 1 else 2 := by
    have he : (es.bipartiteAbove r v : Set E) = {e ∈ edges | r v e} := by
      ext e
      simp [Finset.bipartiteAbove, es]
    rw [← ncard_coe_finset, he]
    by_cases hvB : v ∈ B
    · rw [if_pos hvB]
      exact hboundary v hvB
    · rw [if_neg hvB]
      exact hinterior v (by simpa [vs] using hv) hvB
  have hcol (e : E) (he : e ∈ es) : (vs.bipartiteBelow r e).card = 2 := by
    have hv : (vs.bipartiteBelow r e : Set V) = {v ∈ vertices | r v e} := by
      ext v
      simp [Finset.bipartiteBelow, vs]
    rw [← ncard_coe_finset, hv]
    exact hedges e (by simpa [es] using he)
  have hsum : (∑ v ∈ vs, if v ∈ B then 1 else 2) = es.card * 2 := by
    calc
      _ = ∑ v ∈ vs, (es.bipartiteAbove r v).card :=
        Finset.sum_congr rfl (fun v hv ↦ (hrow v hv).symm)
      _ = ∑ e ∈ es, (vs.bipartiteBelow r e).card :=
        Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow r
      _ = ∑ _e ∈ es, 2 := Finset.sum_congr rfl hcol
      _ = es.card * 2 := by simp
  have hsplit : (∑ v ∈ vs, if v ∈ B then 1 else 2) =
      (vs.filter (· ∈ B)).card + 2 * (vs.filter (· ∉ B)).card := by
    rw [Finset.sum_ite]
    simp [mul_comm]
  rw [hsplit] at hsum
  have hbset : (vs.filter (· ∈ B) : Set V) = B := by
    ext v
    simp only [Finset.mem_coe, Finset.mem_filter]
    constructor
    · exact fun h ↦ h.2
    · intro hvB
      exact ⟨by simpa [vs] using hBV hvB, hvB⟩
  have hbcard : B.ncard = (vs.filter (· ∈ B)).card := by
    rw [← ncard_coe_finset, hbset]
  rw [hbcard]
  refine ⟨es.card - (vs.filter (· ∉ B)).card, ?_⟩
  omega

end NoExoticSixSphere.CurveDecomposition
