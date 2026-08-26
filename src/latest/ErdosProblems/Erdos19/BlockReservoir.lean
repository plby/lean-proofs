import ErdosProblems.Erdos19.EventualBalancedPartition
import ErdosProblems.Erdos19.GraphDegreeAccounting

/-! # Reserving all graph edges inside a balanced partition -/

namespace Erdos19

open Finset
open _root_.SimpleGraph

attribute [local instance] Classical.propDecidable

variable {V K : Type*}

def insideBlocks (G : _root_.SimpleGraph V) (z : V → K) : _root_.SimpleGraph V where
  Adj u v := G.Adj u v ∧ z u = z v
  symm := ⟨fun _ _ h ↦ ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h ↦ h.1.ne rfl⟩

theorem insideBlocks_le (G : _root_.SimpleGraph V) (z : V → K) : insideBlocks G z ≤ G :=
  fun _ _ h ↦ h.1

noncomputable def blockVertices [Fintype V] (z : V → K) (a : K) : Finset V := by
  classical
  exact univ.filter fun v ↦ z v = a

theorem blockVertices_pairwise_disjoint [Fintype V] (z : V → K) :
    Pairwise fun a b ↦ Disjoint (blockVertices z a) (blockVertices z b) := by
  classical
  intro a b hab
  apply Finset.disjoint_left.mpr
  intro v hva hvb
  exact hab ((mem_filter.mp hva).2.symm.trans (mem_filter.mp hvb).2)

theorem filtered_blocks_pairwise_disjoint [Fintype V] (z : V → K) (Y : Finset V) :
    Pairwise fun a b ↦ Disjoint (Y.filter fun v ↦ z v = a) (Y.filter fun v ↦ z v = b) := by
  classical
  intro a b hab
  apply Finset.disjoint_left.mpr
  intro v hva hvb
  exact hab ((mem_filter.mp hva).2.symm.trans (mem_filter.mp hvb).2)

theorem insideBlocks_neighbor_ncard [Fintype V] (G : _root_.SimpleGraph V)
    (z : V → K) (v : V) :
    ((insideBlocks G z).neighborSet v).ncard =
      ((G.neighborSet v).toFinset.filter fun w ↦ z w = z v).card := by
  classical
  rw [Set.ncard_eq_toFinset_card']
  congr 1
  ext w
  constructor
  · intro hw
    have hm : w ∈ (insideBlocks G z).neighborSet v := Set.mem_toFinset.mp hw
    have h : (insideBlocks G z).Adj v w := hm
    exact mem_filter.mpr ⟨Set.mem_toFinset.mpr h.1, h.2.symm⟩
  · intro hw
    obtain ⟨hG, hz⟩ := mem_filter.mp hw
    have hG' : w ∈ G.neighborSet v := Set.mem_toFinset.mp hG
    apply Set.mem_toFinset.mpr
    exact ⟨hG', hz.symm⟩

theorem insideBlocks_missing_on_block (G : _root_.SimpleGraph V) (z : V → K)
    (a : K) (X : Set V) (hX : ∀ v ∈ X, z v = a) (u : V) (hu : z u = a) :
    X \ (insideBlocks G z).neighborSet u = X \ G.neighborSet u := by
  ext v
  constructor
  · rintro ⟨hv, hnot⟩
    exact ⟨hv, fun h ↦ hnot ⟨h, hu.trans (hX v hv).symm⟩⟩
  · rintro ⟨hv, hnot⟩
    exact ⟨hv, fun h ↦ hnot h.1⟩

theorem eventually_exists_balanced_block_reservoir (k : ℕ) (hk : 0 < k)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ G : _root_.SimpleGraph (Fin n),
      ∀ Y : Finset (Fin n), ∃ z : Fin n → Fin k,
        (∀ a, |((blockVertices z a).card : ℝ) - (n : ℝ) / k| < eta * n) ∧
        (∀ v, |(((insideBlocks G z).neighborSet v).ncard : ℝ) -
          (G.neighborSet v).ncard / k| < eta * n) ∧
        (∀ a, |((Y.filter fun v ↦ z v = a).card : ℝ) - (Y.card : ℝ) / k| < eta * n) := by
  classical
  obtain ⟨N, hN⟩ := eventually_exists_balanced_partition k 3 1 hk eta heta
  refine ⟨max N 1, ?_⟩
  intro n hn G Y
  have hnpos : 1 ≤ n := (le_max_right _ _).trans hn
  let S : Fin n ⊕ Bool → Finset (Fin n) := fun i ↦
    match i with
    | Sum.inl v => (G.neighborSet v).toFinset
    | Sum.inr b => if b then Y else univ
  have hI : Fintype.card (Fin n ⊕ Bool) ≤ 3 * n ^ 1 := by
    simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_bool, pow_one]
    omega
  obtain ⟨z, hz⟩ := hN n ((le_max_left _ _).trans hn) (Fin n ⊕ Bool) hI S
  refine ⟨z, ?_, ?_, ?_⟩
  · intro a
    have hblock : (S (Sum.inr false)).filter (fun v ↦ z v = a) = blockVertices z a := by
      ext v
      simp [S, blockVertices]
    have hsize : (S (Sum.inr false)).card = n := by simp [S]
    have h := hz (Sum.inr false) a
    rw [hblock, hsize] at h
    exact h
  · intro v
    have hS : S (Sum.inl v) = (G.neighborSet v).toFinset := by
      dsimp only [S]
    have hsize : (S (Sum.inl v)).card = (G.neighborSet v).ncard :=
      (Set.ncard_eq_toFinset_card' _).symm
    have hcount : ((insideBlocks G z).neighborSet v).ncard =
        ((S (Sum.inl v)).filter fun w ↦ z w = z v).card := by
      rw [hS]
      convert! insideBlocks_neighbor_ncard G z v using 1
      congr 1
      ext w
      simp only [mem_filter, Set.mem_toFinset]
    have h := hz (Sum.inl v) (z v)
    rw [← hcount, hsize] at h
    exact h
  · intro a
    simpa only [S, ↓reduceIte] using hz (Sum.inr true) a

#print axioms eventually_exists_balanced_block_reservoir

end Erdos19
