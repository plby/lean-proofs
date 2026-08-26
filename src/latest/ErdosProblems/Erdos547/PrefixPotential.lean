import ErdosProblems.Erdos547.PairedEmbedding
import ErdosProblems.Erdos547.PairDecay
import ErdosProblems.Erdos547.ExposedSeed

/-!
# Iterating the paired-prefix contraction
-/

namespace Erdos547

open Finset SimpleGraph
open scoped SimpleGraph

variable {U V : Type*} [Fintype V]
    {T : SimpleGraph U} {G : SimpleGraph V} [DecidableRel G.Adj]

open scoped Classical in
/-- A paired prefix can be embedded with exponentially decreasing exposure
potential whenever the escape condition holds throughout the host. -/
theorem exists_paired_prefix_copy_low_potential [Nonempty V]
    (hT : T.IsAcyclic) (indices : Finset V) (k : ℕ) (hk : k ≤ Fintype.card V)
    (hescape : ∀ x ∈ indices, ∀ a, k ≤ ((G.neighborFinset a).filter
      fun z ↦ k ≤ (G.neighborFinset z \ G.neighborFinset x).card).card)
    {r : ℕ} {S : Finset U} (hprefix : PairedPrefix T r S)
    (hmin : 2 * r ≤ G.minDegree) (hsmall : 4 * r ≤ k) :
    ∃ e : (T.induce (S : Set U)).Copy G,
      exposurePotential indices (fun x ↦ ((Finset.univ.image e).filter fun w ↦ ¬ G.Adj x w).card) ≤
        pairDecay (Fintype.card V) k ^ (r - 1) * indices.card := by
  classical
  have hN : 0 < Fintype.card V := Fintype.card_pos
  have hdecay := pairDecay_nonneg hN hk
  revert hmin hsmall
  induction hprefix with
  | edge u v huv =>
    intro hmin hsmall
    have hp : PairedPrefix T 1 {u, v} := PairedPrefix.edge u v huv
    have hST : (T.induce (↑({u, v} : Finset U) : Set U)).IsTree :=
      ⟨hp.connected, hT.induce _⟩
    have hcard : Fintype.card (↑({u, v} : Finset U) : Set U) = 2 := by simp [huv.ne]
    obtain ⟨e⟩ := isContained_of_isTree_of_minDegree (G := G) hST (by rw [hcard]; omega)
    refine ⟨e, ?_⟩
    simpa only [Nat.sub_self, pow_zero, one_mul] using exposurePotential_le_card indices
      (fun x ↦ ((Finset.univ.image e).filter fun w ↦ ¬ G.Adj x w).card)
  | @step r S hprefix p hp u hu v hv hpu huv ih =>
    intro hmin hsmall
    obtain ⟨e, he⟩ := ih (by omega) (by omega)
    let used : Finset V := Finset.univ.image e
    have hused : used.card = 2 * r := by
      have hcard : used.card = S.card := by
        simpa [used] using Finset.card_image_of_injective
          (Finset.univ : Finset (S : Set U)) e.injective
      exact hcard.trans hprefix.card
    have hmin' : used.card + 1 ≤ G.minDegree := by omega
    obtain ⟨q, hq, hcontract⟩ := exists_pair_exposure_contraction G used (e ⟨p, hp⟩)
      (by simp [used]) hmin' indices k (fun x hx ↦ hescape x hx (e ⟨p, hp⟩))
    have hspec := (mem_pairChoices G used (e ⟨p, hp⟩) q.1 q.2).mp hq
    obtain ⟨e', hnewimage⟩ := extend_copy_pair_finset hT S hprefix.connected e ⟨p, hp⟩
      u v hu hv hpu huv q.1 q.2 hspec.1 hspec.2.2.1 hspec.2.1 hspec.2.2.2
    have hfactor := pair_factor_le_pairDecay (N := Fintype.card V) hN
      (show 2 * used.card ≤ k by omega)
    have hnonneg := exposurePotential_nonneg indices
      (fun x ↦ (used.filter fun w ↦ ¬ G.Adj x w).card)
    have hcontract' : exposurePotential indices
        (fun x ↦ ((insert q.2 (insert q.1 used)).filter fun w ↦ ¬ G.Adj x w).card) ≤
          pairDecay (Fintype.card V) k *
            exposurePotential indices (fun x ↦ (used.filter fun w ↦ ¬ G.Adj x w).card) :=
      hcontract.trans (mul_le_mul_of_nonneg_right hfactor hnonneg)
    have he' : exposurePotential indices (fun x ↦ (used.filter fun w ↦ ¬ G.Adj x w).card) ≤
        pairDecay (Fintype.card V) k ^ (r - 1) * indices.card := by
      convert he using 1
    have hprod := mul_le_mul_of_nonneg_left he' hdecay
    refine ⟨e', ?_⟩
    have hpot : exposurePotential indices
        (fun x ↦ ((Finset.univ.image e').filter fun w ↦ ¬ G.Adj x w).card) =
          exposurePotential indices
            (fun x ↦ ((insert q.2 (insert q.1 used)).filter fun w ↦ ¬ G.Adj x w).card) := by
      rw [hnewimage]
    rw [hpot]
    have hrpos := hprefix.pos
    have hr : r - 1 + 1 = r := by omega
    have hpower : pairDecay (Fintype.card V) k *
        (pairDecay (Fintype.card V) k ^ (r - 1) * indices.card) =
          pairDecay (Fintype.card V) k ^ (r + 1 - 1) * indices.card := by
      calc
        _ = pairDecay (Fintype.card V) k ^ (r - 1 + 1) * indices.card := by
          rw [pow_succ]
          ring
        _ = _ := by rw [hr, Nat.add_sub_cancel]
    exact hcontract'.trans (hpower ▸ hprod)

open scoped Classical in
/-- The many-nonleaves embedding case under the explicit escape condition.
The numerical threshold is the only asymptotic inequality used in this step. -/
theorem isContained_of_escape_many_nonleaves [Fintype U] [Nonempty V]
    (hT : T.IsTree) (m d r k : ℕ) (horder : Fintype.card U = m + 1)
    (hr : 0 < r) (hcore : 2 * r ≤ Fintype.card (treeCore T))
    (hk : k ≤ Fintype.card V) (hsmall : 4 * r ≤ k) (hmin : 2 * r ≤ G.minDegree)
    (hdegree : ∀ z, m ≤ G.degree z + d)
    (hescape : ∀ x, G.degree x ≤ m → ∀ a, k ≤ ((G.neighborFinset a).filter
      fun z ↦ k ≤ (G.neighborFinset z \ G.neighborFinset x).card).card)
    (hthreshold : pairDecay (Fintype.card V) k ^ (r - 1) * Fintype.card V < (1 / 2 : ℝ) ^ d) :
    T ⊑ G := by
  classical
  obtain ⟨S, hS⟩ := exists_paired_prefix T hT r hr hcore
  let indices := Finset.univ.filter fun x ↦ G.degree x ≤ m
  obtain ⟨e, hpotential⟩ := exists_paired_prefix_copy_low_potential hT.isAcyclic indices k hk
    (fun x hx a ↦ hescape x (Finset.mem_filter.mp hx).2 a) hS hmin hsmall
  have hindices : (indices.card : ℝ) ≤ Fintype.card V := by
    exact_mod_cast Finset.card_le_univ indices
  have hpow : 0 ≤ pairDecay (Fintype.card V) k ^ (r - 1) :=
    pow_nonneg (pairDecay_nonneg Fintype.card_pos hk) _
  have hprod := mul_le_mul_of_nonneg_left hindices hpow
  have hpotential' : exposurePotential indices
      (fun x ↦ ((Finset.univ.image e).filter fun w ↦ ¬ G.Adj x w).card) < (1 / 2 : ℝ) ^ d :=
    (hpotential.trans hprod).trans_lt hthreshold
  obtain ⟨f, _⟩ := extend_of_small_exposurePotential T G hT m d horder hdegree S hS.connected e
    hpotential'
  exact ⟨f⟩

end Erdos547

#print axioms Erdos547.exists_paired_prefix_copy_low_potential
#print axioms Erdos547.isContained_of_escape_many_nonleaves
