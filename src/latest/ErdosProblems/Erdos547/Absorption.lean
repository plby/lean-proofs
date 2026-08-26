import ErdosProblems.Erdos547.AbsorptionSeed
import ErdosProblems.Erdos547.PendantPackage

/-!
# Absorbing a bounded pendant package across a dense bipartite pair
-/

namespace Erdos547

open Finset SimpleGraph
open scoped SimpleGraph

variable {U V : Type*} [Fintype U]

open scoped Classical in
/-- A dense pair between a small part of a near-clique and an outside set
provides the absorption needed to embed an arbitrary tree of order `m+1`. -/
theorem isContained_of_absorbing_pair (T : SimpleGraph U) (G : SimpleGraph V)
    [DecidableRel G.Adj] (hT : T.IsTree)
    (d m : ℕ) (hd : 0 < d) (hm : 20 * d ≤ m) (horder : Fintype.card U = m + 1)
    (A P Q : Finset V) (hPA : P ⊆ A) (hQA : Disjoint Q A) (hQ : Q.Nonempty)
    (hAsize : A.card ≤ m) (hPsize : 2 * P.card ≤ m)
    (hAdeg : ∀ z ∈ A, m ≤ degreeIn G A z + d)
    (hPQ : ∀ z ∈ P, 4 * d ≤ degreeIn G Q z)
    (hQP : ∀ z ∈ Q, 4 * d ≤ degreeIn G P z) : T ⊑ G := by
  classical
  obtain ⟨S, r, I, _, hSsmall, hpiece, hIS, hIcard, hIdeg, hIind, hIclosed⟩ :=
    exists_pendant_package T hT d hd (by omega)
  have hST : (T.induce (S : Set U)).IsTree := ⟨hpiece.connected, hT.isAcyclic.induce _⟩
  have hScard : Fintype.card (S : Set U) = S.card := Fintype.card_coe S
  let J := (Finset.univ : Finset (S : Set U)).filter fun u ↦ u.val ∈ I
  have hJval : J.image (fun u : (S : Set U) ↦ u.val) = I := by
    ext v
    constructor
    · intro hv
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
      exact (Finset.mem_filter.mp hu).2
    · intro hv
      refine Finset.mem_image.mpr ⟨⟨v, hIS hv⟩, ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩
  have hJcard : J.card = d := by
    rw [← Finset.card_image_of_injective J Subtype.coe_injective, hJval, hIcard]
  have hJdeg : ∀ u ∈ J, (T.induce (S : Set U)).degree u ≤ 2 := by
    intro u hu
    have hI := (Finset.mem_filter.mp hu).2
    rw [← degreeIn_eq_induce_degree T S u]
    have hle := degreeIn_mono T (Finset.subset_univ S) u.val
    rw [degreeIn_univ] at hle
    exact hle.trans (hIdeg u.val hI).2
  have hJind : ∀ u ∈ J, ∀ v ∈ J, ¬ (T.induce (S : Set U)).Adj u v := by
    intro u hu v hv
    exact hIind u.val (Finset.mem_filter.mp hu).2 v.val (Finset.mem_filter.mp hv).2
  obtain ⟨e, heJ, heA⟩ := exists_absorption_seed_copy (T.induce (S : Set U)) G hST
    d m hd hm (by omega) J hJcard hJdeg hJind A P Q hPA hQA hQ hAsize hPsize
    hAdeg hPQ hQP
  have houtside : J.image e ⊆ (Finset.univ.image e) \ A := by
    intro z hz
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hz
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_image.mpr ⟨u, Finset.mem_univ _, rfl⟩, ?_⟩
    exact fun h ↦ Finset.disjoint_left.mp hQA (heJ u hu) h
  have houtcard : d ≤ ((Finset.univ.image e) \ A).card := by
    have hcard := Finset.card_le_card houtside
    rwa [Finset.card_image_of_injective J
      (show Function.Injective (fun u ↦ e u) from e.injective), hJcard] at hcard
  have hclosed : ∀ p : (S : Set U), e p ∉ A → ∀ v, T.Adj p.val v → v ∈ S := by
    intro p hp v hpv
    have hpJ : p ∈ J := by
      by_contra h
      exact hp (heA p h)
    exact hIclosed p.val (Finset.mem_filter.mp hpJ).2 v hpv
  obtain ⟨f, _, _⟩ := extend_connected_copy_in hT S hpiece.connected e A hclosed (by
    intro z hz
    have hdeg := hAdeg z hz
    rw [horder]
    omega)
  exact ⟨f⟩

end Erdos547

#print axioms Erdos547.isContained_of_absorbing_pair
