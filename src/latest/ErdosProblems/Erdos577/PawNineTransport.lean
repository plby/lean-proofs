import ErdosProblems.Erdos577.PawNineModel
import ErdosProblems.Erdos577.PawEleven
import ErdosProblems.Erdos577.UniversalReplacement
import ErdosProblems.Erdos577.DiagonalDegrees

/-! Transfer actual universal replacements into the necessary finite row conditions. -/

namespace Erdos577.PawNine

open Finset
open scoped BigOperators

lemma count_split (m : ℕ) : PathExchange.crossCount m =
    DenseOutside.terminalCount m + DenseOutside.triangleCount m := by
  simp [PathExchange.crossCount, DenseOutside.terminalCount, DenseOutside.triangleCount,
    List.range_succ, Nat.add_assoc]

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma rowCount_encoded (p : Paw G) (q : Quadrilateral G) (i : Fin 4) :
    rowCount (PawEncoding.encoded p q).val i = degreeIn G (p.vertices i) q.support := by
  have hq : Function.Injective (q : Fin 4 → V) := q.injective
  rw [rowCount, Quadrilateral.support, degreeIn_image G _ _ _ hq]
  apply sum_congr rfl
  intro j _
  rw [PawEncoding.encoded_bit]
  by_cases he : G.Adj (p.vertices i) (q j) <;> simp [he]

lemma triangleCount_encoded (p : Paw G) (q : Quadrilateral G) :
    DenseOutside.triangleCount (PawEncoding.encoded p q).val = contacts G p.triangle q.support := by
  have h := count_split (PawEncoding.encoded p q).val
  rw [PawEncoding.crossCount_encoded, PawEncoding.terminalCount_encoded, p.contacts_support] at h
  omega

lemma goodRow_of_universal_replacement (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (i : Fin 3)
    (hr : ∀ v ∈ q.support,
      QuadOn G (insert (p.vertices (Fin.natAdd 1 i)) (q.support.erase v))) :
    GoodRow (Unattached.diagonal q) (PawEncoding.encoded p q).val i := by
  have hz : p.vertices (Fin.natAdd 1 i) ∉ q.support := by
    intro h
    exact (disjoint_left.mp hd)
      ((mem_tupleSupport p.vertices _).mpr ⟨Fin.natAdd 1 i, rfl⟩) h
  have hs : QuadOn G q.support := ⟨q, rfl⟩
  constructor
  · rw [rowCount_encoded]
    exact hs.universal_replace_degree hz hr
  · intro j hj
    have he := universal_replace_adjacent_to_degree_two hz hr
      ((q.mem_support _).mpr ⟨j, rfl⟩) (q.degreeIn_eq_two_of_diagonal_false j hj)
    have hb := PawEncoding.encoded_bit p q (Fin.natAdd 1 i) j
    have hindex : 4 * (Fin.natAdd 1 i).val + j.val = 4 * (i.val + 1) + j.val := by
      simp only [Fin.val_natAdd, Nat.add_comm 1 i.val]
    rw [hindex] at hb
    exact hb.trans (decide_eq_true he)

lemma hasGoodRow_of_universal_replacement (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support)
    (hr : ∃ v ∈ p.triangle, ∀ w ∈ q.support, QuadOn G (insert v (q.support.erase w))) :
    HasGoodRow (Unattached.diagonal q) (PawEncoding.encoded p q).val := by
  obtain ⟨v, hv, hr⟩ := hr
  simp only [Paw.triangle, mem_insert, mem_singleton] at hv
  rcases hv with rfl | rfl | rfl
  · exact ⟨0, goodRow_of_universal_replacement p q hd 0 hr⟩
  · exact ⟨1, goodRow_of_universal_replacement p q hd 1 hr⟩
  · exact ⟨2, goodRow_of_universal_replacement p q hd 2 hr⟩

end Erdos577.PawNine
