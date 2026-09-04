import ErdosProblems.Erdos556.EvenCycleChords

/-! The two equally large parity cliques on a minimal even cycle. -/

namespace Erdos556

open SimpleGraph Finset

def parityHalfIndex (t : ℕ) (b : Fin 2) (i : Fin t) : Fin (2 * t) :=
  ⟨2 * i.val + b.val, by have hi := i.isLt; have hb := b.isLt; omega⟩

theorem parityHalfIndex_injective (t : ℕ) (b : Fin 2) :
    Function.Injective (parityHalfIndex t b) := by
  intro i j h
  have hv := congrArg Fin.val h
  change 2 * i.val + b.val = 2 * j.val + b.val at hv
  apply Fin.ext
  omega

noncomputable def parityHalf {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {t : ℕ} (f : (cycleGraph (2 * t)).Copy G) (b : Fin 2) : Finset V :=
  univ.image (fun i : Fin t => f (parityHalfIndex t b i))

theorem parityHalf_card {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {t : ℕ} (f : (cycleGraph (2 * t)).Copy G) (b : Fin 2) : (parityHalf f b).card = t := by
  classical
  have hinj : Function.Injective (fun i : Fin t => f (parityHalfIndex t b i)) :=
    f.injective.comp (parityHalfIndex_injective t b)
  rw [parityHalf, card_image_of_injective _ hinj,
    card_univ, Fintype.card_fin]

theorem parityHalf_disjoint {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {t : ℕ} (f : (cycleGraph (2 * t)).Copy G) : Disjoint (parityHalf f 0) (parityHalf f 1) := by
  classical
  apply Finset.disjoint_left.mpr
  intro v hv0 hv1
  obtain ⟨i, _, hi⟩ := mem_image.mp hv0
  obtain ⟨j, _, hj⟩ := mem_image.mp hv1
  have h := congrArg Fin.val (f.injective (hi.trans hj.symm))
  change 2 * i.val + 0 = 2 * j.val + 1 at h
  omega

theorem parityHalf_isClique {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {t : ℕ} [NeZero (2 * t)] (ht : 4 ≤ t) (f : (cycleGraph (2 * t)).Copy G)
    (hno : ¬ cycleGraph (2 * t - 1) ⊑ G) (hnoc : ¬ cycleGraph (2 * t - 1) ⊑ Gᶜ)
    (b : Fin 2) : Gᶜ.IsClique ((parityHalf f b : Finset V) : Set V) := by
  classical
  intro u hu v hv huv
  obtain ⟨i, _, hi⟩ := mem_image.mp hu
  obtain ⟨j, _, hj⟩ := mem_image.mp hv
  rw [← hi, ← hj]
  apply complement_adj_of_same_parity t ht f hno hnoc
  · intro h
    exact huv (hi.symm.trans ((congrArg f h).trans hj))
  · change (2 * i.val + b.val) % 2 = (2 * j.val + b.val) % 2
    omega

theorem exists_two_parity_cliques {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (t : ℕ) (ht : 4 ≤ t) (hc : cycleGraph (2 * t) ⊑ G)
    (hno : ¬ cycleGraph (2 * t - 1) ⊑ G) (hnoc : ¬ cycleGraph (2 * t - 1) ⊑ Gᶜ) :
    ∃ A B : Finset V, Disjoint A B ∧ A.card = t ∧ B.card = t ∧
      Gᶜ.IsClique (A : Set V) ∧ Gᶜ.IsClique (B : Set V) := by
  classical
  let : NeZero (2 * t) := ⟨by omega⟩
  obtain ⟨f⟩ := hc
  exact ⟨parityHalf f 0, parityHalf f 1, parityHalf_disjoint f,
    parityHalf_card f 0, parityHalf_card f 1,
    parityHalf_isClique ht f hno hnoc 0, parityHalf_isClique ht f hno hnoc 1⟩

#print axioms exists_two_parity_cliques

end Erdos556
