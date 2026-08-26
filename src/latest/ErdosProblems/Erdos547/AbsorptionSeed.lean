import ErdosProblems.Erdos547.ThreePools

/-!
# Embedding the small seed for absorption into a near-clique
-/

namespace Erdos547

open Finset SimpleGraph
open scoped SimpleGraph BigOperators

variable {U V : Type*} [Fintype U]

open scoped Classical in
theorem exists_absorption_seed_copy (T : SimpleGraph U) (G : SimpleGraph V)
    [DecidableRel T.Adj] [DecidableRel G.Adj] (hT : T.IsTree)
    (d m : ℕ) (hd : 0 < d) (hm : 20 * d ≤ m)
    (hsmall : Fintype.card U ≤ 8 * d - 1)
    (I : Finset U) (hIcard : I.card = d)
    (hIdeg : ∀ u ∈ I, T.degree u ≤ 2)
    (hIind : ∀ u ∈ I, ∀ v ∈ I, ¬ T.Adj u v)
    (A P Q : Finset V) (hPA : P ⊆ A) (hQA : Disjoint Q A) (hQ : Q.Nonempty)
    (hAsize : A.card ≤ m) (hPsize : 2 * P.card ≤ m)
    (hAdeg : ∀ z ∈ A, m ≤ degreeIn G A z + d)
    (hPQ : ∀ z ∈ P, 4 * d ≤ degreeIn G Q z)
    (hQP : ∀ z ∈ Q, 4 * d ≤ degreeIn G P z) :
    ∃ f : T.Copy G, (∀ u ∈ I, f u ∈ Q) ∧ (∀ u ∉ I, f u ∈ A) := by
  classical
  let J := I.biUnion (fun u ↦ T.neighborFinset u)
  have hJcard : J.card ≤ 2 * d := by
    calc
      _ ≤ ∑ u ∈ I, (T.neighborFinset u).card := Finset.card_biUnion_le
      _ ≤ ∑ _u ∈ I, 2 := by
        apply Finset.sum_le_sum
        intro u hu
        simpa using hIdeg u hu
      _ = _ := by simp [hIcard, Nat.mul_comm]
  have hIJ : Disjoint I J := by
    apply Finset.disjoint_left.mpr
    intro u huI huJ
    obtain ⟨v, hvI, hvu⟩ := Finset.mem_biUnion.mp huJ
    exact hIind v hvI u huI ((T.mem_neighborFinset v u).mp hvu)
  have hneighbors : ∀ u ∈ I, ∀ v, T.Adj u v → v ∈ J := by
    intro u hu v huv
    exact Finset.mem_biUnion.mpr ⟨u, hu, (T.mem_neighborFinset u v).mpr huv⟩
  obtain ⟨q, hq⟩ := hQ
  have hPlo : 4 * d ≤ P.card := (hQP q hq).trans (degreeIn_le_card G P q)
  have hP : P.Nonempty := Finset.card_pos.mp (by omega)
  let B := A \ P
  have hPB : Disjoint P B := by
    apply Finset.disjoint_left.mpr
    intro z hzP hzB
    exact (Finset.mem_sdiff.mp hzB).2 hzP
  have hQB : Disjoint Q B := hQA.mono_right Finset.sdiff_subset
  have hPQdis : Disjoint P Q := (hQA.mono_right hPA).symm
  have hcover : P ∪ B = A := Finset.union_sdiff_of_subset hPA
  have hBsize : B.card + P.card = A.card := by
    change (A \ P).card + P.card = A.card
    rw [Finset.card_sdiff_of_subset hPA]
    have hle := Finset.card_le_card hPA
    omega
  have hAP : A \ P = B := rfl
  have hAB : A \ B = P := by
    ext z
    simp only [B, Finset.mem_sdiff]
    constructor
    · rintro ⟨hzA, hz⟩
      by_contra hzP
      exact hz ⟨hzA, hzP⟩
    · intro hzP
      exact ⟨hPA hzP, fun h ↦ h.2 hzP⟩
  have hdegP : ∀ z ∈ A, J.card ≤ degreeIn G P z := by
    intro z hz
    have hdeg := hAdeg z hz
    have hloss := degreeIn_le_add_removed G A P z
    rw [hAP] at hloss
    omega
  have hdegB : ∀ z ∈ A, Fintype.card U ≤ degreeIn G B z := by
    intro z hz
    have hdeg := hAdeg z hz
    have hloss := degreeIn_le_add_removed G A B z
    rw [hAB] at hloss
    omega
  have hB : B.Nonempty := by
    obtain ⟨p, hp⟩ := hP
    have hdeg := hdegB p (hPA hp)
    have hle := degreeIn_le_card G B p
    let : Nonempty U := hT.connected.nonempty
    have hn := Fintype.card_pos (α := U)
    exact Finset.card_pos.mp (by omega)
  obtain ⟨f, hfI, hfJ, hfB⟩ := exists_copy_three_pools T G hT I J hIJ hneighbors
    P Q B hPQdis hPB hQB hP ⟨q, hq⟩ hB
    (fun z hz ↦ hJcard.trans (by have h := hQP z hz; omega))
    (fun z hz ↦ by rw [hIcard]; have h := hPQ z hz; omega)
    (by rw [hcover]; exact hdegP) (by rw [hcover]; exact hdegB)
  refine ⟨f, hfI, ?_⟩
  intro u hu
  by_cases huJ : u ∈ J
  · exact hPA (hfJ u huJ)
  · exact Finset.sdiff_subset (hfB u hu huJ)

end Erdos547

#print axioms Erdos547.exists_absorption_seed_copy
