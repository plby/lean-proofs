import ErdosProblems.Erdos73.SameSideCrossingAssembly
import ErdosProblems.Erdos73.ThroughCrossingSelection

/-! Complete finite crossing/noncrossing handle extraction using the checked wall routes. -/

namespace Erdos73
noncomputable section
open scoped Classical

open SimpleGraph Finset

def crossingHandleIntermediateSize (k : ℕ) : ℕ :=
  k - 1 + pureEndpointPairBound k + 2 * twoColorRamseyBound k k

def crossingHandleSelectionBound (k : ℕ) : ℕ :=
  8 * (4 * crossingHandleIntermediateSize k - 1) + 1

namespace ColumnHandleFamily

variable {V I : Type*} [Fintype V] {G : SimpleGraph V} {c r : ℕ}
variable {S : GraphSubdivisionModel (elementaryWall c r) G}
variable {col : BipartiteColoringOn G S.vertexSet}

theorem oddPacking_or_crossing_handles (F : ColumnHandleFamily S col I)
    (k : ℕ) (hc : k + 2 ≤ c) (s : Finset I)
    (hsize : crossingHandleSelectionBound k ≤ s.card) :
    HasOddCyclePacking k G ∨
      HasSameSideCrossingHandles (S := S) (col := col) true k ∨
      HasSameSideCrossingHandles (S := S) (col := col) false k ∨
      HasThroughCrossingHandles (S := S) (col := col) k := by
  let m := crossingHandleIntermediateSize k
  obtain ⟨E, hdis, ⟨sourceSide, targetSide⟩, hsides⟩ :=
    F.exists_homogeneous_row_disjoint_subfamily (by omega) s m
      (by dsimp only [crossingHandleSelectionBound] at hsize; omega)
  have hsl (i : Fin m) : decide ((E.sourceNail i).val.2.val ≤ 1) = sourceSide :=
    congrArg Prod.fst (hsides i)
  have htl (i : Fin m) : decide ((E.targetNail i).val.2.val ≤ 1) = targetSide :=
    congrArg Prod.snd (hsides i)
  have hsameSize : k - 1 + pureEndpointPairBound k ≤ (univ : Finset (Fin m)).card := by
    simp only [card_univ, Fintype.card_fin]
    dsimp only [m, crossingHandleIntermediateSize]
    omega
  have hthroughSize : 2 * twoColorRamseyBound k k ≤ (univ : Finset (Fin m)).card := by
    simp only [card_univ, Fintype.card_fin]
    dsimp only [m, crossingHandleIntermediateSize]
    omega
  cases sourceSide with
  | false =>
    have hsr (i : Fin m) : 2 * (c - 1) ≤ (E.sourceNail i).val.2.val :=
      (E.source_boundary i).resolve_left (by
        simpa only [decide_eq_false_iff_not] using hsl i)
    cases targetSide with
    | false =>
      have htr (i : Fin m) : 2 * (c - 1) ≤ (E.targetNail i).val.2.val :=
        (E.target_boundary i).resolve_left (by
          simpa only [decide_eq_false_iff_not] using htl i)
      obtain hp | hx := E.oddPacking_or_sameSide_crossing_any_rows false k hc hdis
        hsr htr univ hsameSize
      · exact Or.inl hp
      · exact Or.inr (Or.inr (Or.inl hx))
    | true =>
      have htleft (i : Fin m) : (E.targetNail i).val.2.val ≤ 1 := of_decide_eq_true (htl i)
      let D := E.reverseWhere (fun _ => true)
      have hDdis : Pairwise (fun i j => Disjoint (D.rows i) (D.rows j)) := by
        intro i j hij
        simpa only [D, reverseWhere_rows] using hdis hij
      obtain hp | hx := D.oddPacking_or_through_crossing k hc hDdis htleft hsr univ hthroughSize
      · exact Or.inl hp
      · exact Or.inr (Or.inr (Or.inr hx))
  | true =>
    have hsleft (i : Fin m) : (E.sourceNail i).val.2.val ≤ 1 := of_decide_eq_true (hsl i)
    cases targetSide with
    | false =>
      have htr (i : Fin m) : 2 * (c - 1) ≤ (E.targetNail i).val.2.val :=
        (E.target_boundary i).resolve_left (by
          simpa only [decide_eq_false_iff_not] using htl i)
      obtain hp | hx := E.oddPacking_or_through_crossing k hc hdis hsleft htr univ hthroughSize
      · exact Or.inl hp
      · exact Or.inr (Or.inr (Or.inr hx))
    | true =>
      have htleft (i : Fin m) : (E.targetNail i).val.2.val ≤ 1 := of_decide_eq_true (htl i)
      obtain hp | hx := E.oddPacking_or_sameSide_crossing_any_rows true k hc hdis
        hsleft htleft univ hsameSize
      · exact Or.inl hp
      · exact Or.inr (Or.inl hx)

end ColumnHandleFamily
end
end Erdos73
