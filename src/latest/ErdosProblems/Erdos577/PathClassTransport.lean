import ErdosProblems.Erdos577.PathClassModel
import ErdosProblems.Erdos577.PathLossTransport
import ErdosProblems.Erdos577.CommonReplacement

/-! Transport exact normalized path rows and positive outcomes to the original graph. -/

namespace Erdos577.PathClass

open Finset Function
open scoped BigOperators

lemma rowCount_remove_add (m : ℕ) (reverse : Bool) (cols : Fin 4 ↪ Fin 4) (i u : Fin 4) :
    (∑ v : Fin 4, if v ≠ u then (bit m reverse cols i v).toNat else 0) +
      (bit m reverse cols i u).toNat = rowCount m reverse cols i := by
  have he : (∑ v : Fin 4, if v = u then (bit m reverse cols i v).toNat else 0) =
      (bit m reverse cols i u).toNat := by simp
  rw [← he, ← sum_add_distrib]
  apply sum_congr rfl
  intro v _
  by_cases hv : v = u <;> simp [hv]

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

def normalizedPath (p : FourPath G) (reverse : Bool) : FourPath G :=
  if reverse then p.reverse else p

lemma normalizedPath_support (p : FourPath G) (reverse : Bool) :
    (normalizedPath p reverse).support = p.support := by
  cases reverse <;> simp [normalizedPath, FourPath.reverse_support]

variable [DecidableRel G.Adj]

lemma diagonal_eq_three (q : Quadrilateral G) (hq : G.IsNClique 4 q.support) :
    Unattached.diagonal q = 3 := by
  have hinj : Injective (q : Fin 4 → V) := q.injective
  have h02 : G.Adj (q 0) (q 2) := hq.isClique ((q.mem_support _).mpr ⟨0, rfl⟩)
    ((q.mem_support _).mpr ⟨2, rfl⟩) (hinj.ne (by decide))
  have h13 : G.Adj (q 1) (q 3) := hq.isClique ((q.mem_support _).mpr ⟨1, rfl⟩)
    ((q.mem_support _).mpr ⟨3, rfl⟩) (hinj.ne (by decide))
  simp [Unattached.diagonal, h02, h13]

lemma Positive.transport (p : FourPath G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (hq : G.IsNClique 4 q.support)
    (h : Positive (PathExchange.encoded p q).val) :
    ScoredExchange G (p.support ∪ q.support) 6 := by
  have hmodel : ScoredExchange
      (PathLoss.graph (Unattached.diagonal q) (PathExchange.encoded p q).val) univ 6 := by
    rw [diagonal_eq_three q hq]
    exact h
  have hg := hmodel.image (PathLoss.modelCopy p q hd)
  rw [PathLoss.modelCopy_image] at hg
  exact hg

lemma bit_encoded (p : FourPath G) (q : Quadrilateral G) (hq : G.IsNClique 4 q.support)
    (reverse : Bool) (cols : Fin 4 ↪ Fin 4) (i j : Fin 4) :
    bit (PathExchange.encoded p q).val reverse cols i j =
      decide (G.Adj ((normalizedPath p reverse).vertices i) (q.relabelOfClique hq cols j)) := by
  rw [bit, PathExchange.encoded_bit]
  cases reverse <;> rfl

lemma rowCount_encoded (p : FourPath G) (q : Quadrilateral G) (hq : G.IsNClique 4 q.support)
    (reverse : Bool) (cols : Fin 4 ↪ Fin 4) (i : Fin 4) :
    rowCount (PathExchange.encoded p q).val reverse cols i =
      degreeIn G ((normalizedPath p reverse).vertices i) q.support := by
  let q' := q.relabelOfClique hq cols
  have hinj : Injective (q' : Fin 4 → V) := q'.injective
  have he := degreeIn_image G ((normalizedPath p reverse).vertices i) univ q' hinj
  change degreeIn G ((normalizedPath p reverse).vertices i) q'.support = _ at he
  have hcount : rowCount (PathExchange.encoded p q).val reverse cols i =
      degreeIn G ((normalizedPath p reverse).vertices i) q'.support := by
    rw [he, rowCount]
    apply sum_congr rfl
    intro j _
    rw [bit_encoded p q hq]
    change (decide (G.Adj ((normalizedPath p reverse).vertices i) (q' j))).toNat =
      if G.Adj ((normalizedPath p reverse).vertices i) (q' j) then 1 else 0
    by_cases h : G.Adj ((normalizedPath p reverse).vertices i) (q' j) <;>
      simp only [h, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false, if_true, if_false]
  simpa only [q', Quadrilateral.relabelOfClique_support] using hcount

lemma Replacement.transport (p : FourPath G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (hq : G.IsNClique 4 q.support)
    (reverse : Bool) (cols : Fin 4 ↪ Fin 4) (i j l : Fin 4)
    (h : Replacement (PathExchange.encoded p q).val reverse cols i j l) :
    CommonReplacement G ((normalizedPath p reverse).vertices j)
      ((normalizedPath p reverse).vertices l)
      ((normalizedPath p reverse).vertices i) q.support := by
  obtain ⟨u, hju, hlu, htwo⟩ := h
  let p' := normalizedPath p reverse
  let q' := q.relabelOfClique hq cols
  have hu : q' u ∈ q.support := by
    rw [← q.relabelOfClique_support hq cols]
    exact (q'.mem_support _).mpr ⟨u, rfl⟩
  have hi : p'.vertices i ∈ p.support := by
    rw [← normalizedPath_support p reverse]
    exact mem_image.mpr ⟨i, mem_univ _, rfl⟩
  have hqi : p'.vertices i ∉ q.support := fun h ↦ disjoint_left.mp hd hi h
  rw [bit_encoded p q hq] at hju hlu
  refine ⟨q' u, hu, of_decide_eq_true hju, of_decide_eq_true hlu, ?_⟩
  apply (clique_replace_iff_two_contacts hq hqi hu).mpr
  have he := degreeIn_erase_add G (p'.vertices i) (q' u) hu
  have hsum := rowCount_remove_add (PathExchange.encoded p q).val reverse cols i u
  rw [rowCount_encoded p q hq, bit_encoded p q hq] at hsum
  change _ + (decide (G.Adj (p'.vertices i) (q' u))).toNat =
    degreeIn G (p'.vertices i) q.support at hsum
  by_cases hadj : G.Adj (p'.vertices i) (q' u)
  · simp only [hadj, decide_true, Bool.toNat_true, if_true] at he hsum
    omega
  · simp only [hadj, decide_false, Bool.toNat_false, if_false] at he hsum
    omega

end Erdos577.PathClass
