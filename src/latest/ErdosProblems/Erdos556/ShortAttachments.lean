import ErdosProblems.Erdos556.DeletionPaths
import ErdosProblems.Erdos556.PathOperations

/-!
# Disjoint short attachments to a vertex set

Connectivity after deletion of a short first path gives a second attachment.
Taking the first entry into the target set makes both interiors avoid it.
-/

namespace Erdos556

open SimpleGraph Finset

theorem exists_disjoint_short_attachments {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b d D : ℕ)
    (hconn : ConnectedAfterDeleting G b) (hd : 0 < d)
    (hdeg : ∀ w, d + b ≤ G.degree w) (hN : Fintype.card V ≤ D * d)
    (S : Finset V) (hbudget : S.card + 3 * D + 1 ≤ b)
    (C : Set V) (hC : C.Nontrivial) (hCS : ∀ z ∈ C, z ∉ S)
    (u v : V) (hu : u ∉ S) (hv : v ∉ S) (huv : u ≠ v) :
    ∃ x ∈ C, ∃ y ∈ C, ∃ (p : G.Walk u x) (q : G.Walk v y),
      p.IsPath ∧ q.IsPath ∧ p.length < 3 * D ∧ q.length < 3 * D ∧ x ≠ y ∧
      (∀ z ∈ p.support, z ∈ C → z = x) ∧
      (∀ z ∈ q.support, z ∈ C → z = y) ∧
      (∀ z ∈ p.support, z ∉ q.support) ∧
      (∀ z ∈ p.support, z ∉ S) ∧ (∀ z ∈ q.support, z ∉ S) := by
  classical
  obtain ⟨w, hwC, hwv⟩ := hC.exists_ne v
  have hfirst : (insert v S).card ≤ b := (card_insert_le v S).trans (by omega)
  obtain ⟨p', hp', hplen, hpavoid⟩ := exists_short_path_avoiding G b d hconn hd hdeg
    (insert v S) hfirst u w (by simpa using And.intro huv hu)
    (by simpa using And.intro hwv (hCS w hwC))
  obtain ⟨x, hxC, p, hp, hpp', hpsub, hpC⟩ := exists_path_first_meeting_set p' hp' C hwC
  have hpbound : p.length < 3 * D := by nlinarith
  have hpav (z : V) (hz : z ∈ p.support) : z ∉ insert v S :=
    hpavoid z (hpsub hz)
  have hpcard : p.support.toFinset.card ≤ 3 * D := by
    have hcard := List.toFinset_card_le p.support
    rw [p.length_support] at hcard
    omega
  let T := S ∪ p.support.toFinset
  have hT : T.card ≤ b := (card_union_le S p.support.toFinset).trans (by omega)
  obtain ⟨z, hzC, hzx⟩ := hC.exists_ne x
  have hzT : z ∉ T := by
    simp only [T, mem_union, List.mem_toFinset, not_or]
    exact ⟨hCS z hzC, fun h => hzx (hpC z h hzC)⟩
  have hvT : v ∉ T := by
    simp only [T, mem_union, List.mem_toFinset, not_or]
    exact ⟨hv, fun h => hpav v h (mem_insert_self v S)⟩
  obtain ⟨q', hq', hqlen, hqavoid⟩ := exists_short_path_avoiding G b d hconn hd hdeg
    T hT v z hvT hzT
  obtain ⟨y, hyC, q, hq, hqq', hqsub, hqC⟩ := exists_path_first_meeting_set q' hq' C hzC
  have hqbound : q.length < 3 * D := by nlinarith
  have hqav (z : V) (hz : z ∈ q.support) : z ∉ T := hqavoid z (hqsub hz)
  have hpq (z : V) (hzp : z ∈ p.support) (hzq : z ∈ q.support) : False :=
    hqav z hzq (mem_union_right S (List.mem_toFinset.mpr hzp))
  have hxy : x ≠ y := by
    intro h
    exact hpq x p.end_mem_support (h ▸ q.end_mem_support)
  refine ⟨x, hxC, y, hyC, p, q, hp, hq, hpbound, hqbound, hxy, hpC, hqC, hpq, ?_, ?_⟩
  · intro z hz hzS
    exact hpav z hz (mem_insert_of_mem hzS)
  · intro z hz hzS
    exact hqav z hz (mem_union_left _ hzS)

#print axioms exists_disjoint_short_attachments

end Erdos556
