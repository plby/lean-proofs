import ErdosProblems.Erdos547.LabelledEmbedding

/-!
# Three-pool embedding for a small absorption seed
-/

namespace Erdos547

open Finset SimpleGraph
open scoped SimpleGraph

variable {U V : Type*} [Fintype U]

open scoped Classical in
/-- Embed a tree so that the selected vertices `I` use `Q`, their neighbours
use `P`, and all other vertices use `A`. -/
theorem exists_copy_three_pools (T : SimpleGraph U) (G : SimpleGraph V)
    [DecidableRel G.Adj] (hT : T.IsTree) (I J : Finset U)
    (hIJ : Disjoint I J) (hneighbors : ∀ u ∈ I, ∀ v, T.Adj u v → v ∈ J)
    (P Q A : Finset V) (hPQ : Disjoint P Q) (hPA : Disjoint P A) (hQA : Disjoint Q A)
    (hP : P.Nonempty) (hQ : Q.Nonempty) (hA : A.Nonempty)
    (hQP : ∀ z ∈ Q, J.card ≤ degreeIn G P z)
    (hPQdeg : ∀ z ∈ P, I.card ≤ degreeIn G Q z)
    (hrestP : ∀ z ∈ P ∪ A, J.card ≤ degreeIn G P z)
    (hrestA : ∀ z ∈ P ∪ A, Fintype.card U ≤ degreeIn G A z) :
    ∃ f : T.Copy G,
      (∀ u ∈ I, f u ∈ Q) ∧ (∀ u ∈ J, f u ∈ P) ∧
      (∀ u, u ∉ I → u ∉ J → f u ∈ A) := by
  classical
  let label (u : U) : Fin 3 := if u ∈ I then 0 else if u ∈ J then 1 else 2
  let pool (i : Fin 3) : Finset V := if i = 0 then Q else if i = 1 then P else A
  have hdis : ∀ i j, i ≠ j → Disjoint (pool i) (pool j) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [pool, disjoint_comm]
  have hnotI {u : U} (hu : u ∈ J) : u ∉ I :=
    fun h ↦ Finset.disjoint_left.mp hIJ h hu
  have hclass0 : ((Finset.univ : Finset U).filter fun x ↦ label x = 0) = I := by
    ext x
    by_cases hxI : x ∈ I <;> by_cases hxJ : x ∈ J <;> simp [label, hxI, hxJ]
  have hclass1 : ((Finset.univ : Finset U).filter fun x ↦ label x = 1) = J := by
    ext x
    by_cases hxI : x ∈ I
    · have hxJ : x ∉ J := fun h ↦ Finset.disjoint_left.mp hIJ hxI h
      simp [label, hxI, hxJ]
    · simp [label, hxI]
  have hclass2 : ((Finset.univ : Finset U).filter fun x ↦ label x = 2).card ≤
      Fintype.card U := by
    simpa using Finset.card_filter_le (Finset.univ : Finset U) (fun x ↦ label x = 2)
  have hdegree : ∀ u v, T.Adj u v → ∀ z ∈ pool (label u),
      ((Finset.univ : Finset U).filter fun x ↦ label x = label v).card ≤
        degreeIn G (pool (label v)) z := by
    intro u v huv z hz
    by_cases huI : u ∈ I
    · have hvJ := hneighbors u huI v huv
      have hvI := hnotI hvJ
      have hu : label u = 0 := by simp [label, huI]
      have hv : label v = 1 := by simp [label, hvI, hvJ]
      rw [hu] at hz
      rw [hv, hclass1]
      exact hQP z (by simpa [pool] using hz)
    · by_cases huJ : u ∈ J
      · have hu : label u = 1 := by simp [label, huI, huJ]
        have hzP : z ∈ P := by simpa [hu, pool] using hz
        by_cases hvI : v ∈ I
        · have hv : label v = 0 := by simp [label, hvI]
          rw [hv, hclass0]
          exact hPQdeg z hzP
        · by_cases hvJ : v ∈ J
          · have hv : label v = 1 := by simp [label, hvI, hvJ]
            rw [hv, hclass1]
            exact hrestP z (Finset.mem_union_left _ hzP)
          · have hv : label v = 2 := by simp [label, hvI, hvJ]
            rw [hv]
            exact hclass2.trans (hrestA z (Finset.mem_union_left _ hzP))
      · have hu : label u = 2 := by simp [label, huI, huJ]
        have hzA : z ∈ A := by simpa [hu, pool] using hz
        have hvI : v ∉ I := fun h ↦ huJ (hneighbors v h u huv.symm)
        by_cases hvJ : v ∈ J
        · have hv : label v = 1 := by simp [label, hvI, hvJ]
          rw [hv, hclass1]
          exact hrestP z (Finset.mem_union_right _ hzA)
        · have hv : label v = 2 := by simp [label, hvI, hvJ]
          rw [hv]
          exact hclass2.trans (hrestA z (Finset.mem_union_right _ hzA))
  obtain ⟨r⟩ := hT.connected.nonempty
  have hpool : (pool (label r)).Nonempty := by
    by_cases hrI : r ∈ I
    · simpa [pool, label, hrI] using hQ
    · by_cases hrJ : r ∈ J
      · simpa [pool, label, hrI, hrJ] using hP
      · simpa [pool, label, hrI, hrJ] using hA
  obtain ⟨z, hz⟩ := hpool
  obtain ⟨f, _, hf⟩ := exists_copy_of_labelled_degree T G hT label pool hdis (by
    intro u v huv z hz
    convert hdegree u v huv z hz using 1
    congr 2) r z hz
  refine ⟨f, ?_, ?_, ?_⟩
  · intro u hu
    simpa [label, pool, hu] using hf u
  · intro u hu
    simpa [label, pool, hu, hnotI hu] using hf u
  · intro u huI huJ
    simpa [label, pool, huI, huJ] using hf u

end Erdos547

#print axioms Erdos547.exists_copy_three_pools
