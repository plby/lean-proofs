import Mathlib
import ErdosProblems.Erdos550.AvoidingClusterEmbedding
import ErdosProblems.Erdos550.RegularPairTools

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Skeleton embedding with small `Bad` (adaptive typicality)

The adaptive shrub embedding (`AdaptiveMatchingShrub.lean`) needs each seed image
to be typical toward *most* matching clusters, i.e. atypical toward only a small
set `Bad`.  This file constructs such a skeleton embedding.

The construction forbids the *high-`Bad`* vertices—those atypical toward more
than `thr` target clusters.  By a Markov/double-counting bound the high-`Bad` set
has size at most
`(∑_{m∈Tset} |atyp i m|)/thr`, which the capacity absorbs.  The surviving images
are then atypical toward at most `thr` clusters — exactly a small `Bad`.
-/

open SimpleGraph Finset

namespace Erdos550

open Classical in
/-- The number of `Tset`-clusters toward which a vertex `v` is atypical (sees fewer
than a `(dcap m - ε)`-fraction of `C m`). -/
noncomputable def badCount {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {ι : Type*} (C : ι → Finset V) (dcap : ι → ℝ)
    (ε : ℝ) (Tset : Finset ι) (v : V) : ℕ :=
  (Tset.filter (fun m => (((C m).filter (fun x => G.Adj v x)).card : ℝ)
      < (dcap m - ε) * ((C m).card : ℝ))).card

open Classical in
set_option maxHeartbeats 1000000 in
/-- **Low-`Bad` skeleton embedding.**  Embed the skeleton forest into the head
clusters so that every image is atypical toward at most `thr` target clusters. -/
theorem skeleton_lowbad_embedding
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    {ι : Type*} [DecidableEq ι] (C : ι → Finset V) (R : SimpleGraph ι) (dcap : ι → ℝ)
    (hdcap1 : ∀ i, dcap i ≤ 1)
    (hne : ∀ i, (C i).Nonempty)
    (hdisj : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (huni : ∀ i j, R.Adj i j → G.IsUniform ε (C i) (C j))
    (hdens : ∀ i j, R.Adj i j → dcap j ≤ (G.edgeDensity (C i) (C j) : ℝ))
    {α : Type*} [Fintype α] [DecidableEq α]
    (parentA : α → Option α) (rankA : α → ℕ)
    (hrankA : ∀ a b, parentA a = some b → rankA b < rankA a)
    (cluA : α → ι)
    (hhomA : ∀ a b, parentA a = some b → R.Adj (cluA a) (cluA b))
    (BB : ℕ)
    (hB : ∀ a, ((univ.filter (fun x => parentA x = some a)).image cluA).card ≤ BB)
    (Hset Tset : Finset ι)
    (hcluA_H : ∀ a, cluA a ∈ Hset)
    (thr : ℝ) (hthr : 0 < thr)
    (Bnd : ℝ)
    (hatyp : ∀ i ∈ Hset,
        (∑ m ∈ Tset, (((C i).filter (fun v =>
            (((C m).filter (fun x => G.Adj v x)).card : ℝ)
              < (dcap m - ε) * ((C m).card : ℝ))).card) : ℝ) ≤ Bnd)
    (hcapSk : ∀ i, ((univ.filter (fun a => cluA a = i)).card : ℝ)
              + Bnd / thr
              + (BB : ℝ) * (ε * ((C i).card : ℝ)) < (dcap i - ε) * ((C i).card : ℝ)) :
    ∃ f : α → V, Function.Injective f ∧
      (∀ a, f a ∈ C (cluA a)) ∧
      (∀ a b, parentA a = some b → G.Adj (f a) (f b)) ∧
      (∀ a, (badCount G C dcap ε Tset (f a) : ℝ) ≤ thr) := by
  by_contra! h_contra;
  -- Apply the regularClusters_forest_embedding_weighted_avoiding theorem with the given parameters.
  have := @regularClusters_forest_embedding_weighted_avoiding V _ _ G _ ε hε0 hε1 ι _ C R dcap hdcap1 hne hdisj huni hdens α _ _ parentA rankA hrankA cluA hhomA BB hB (fun i => if i ∈ Hset then (C i).filter (fun v => (badCount G C dcap ε Tset v : ℝ) > thr) else ∅) (by
  intro i;
  by_cases hi : i ∈ Hset <;> simp +decide [ hi ];
  · refine' lt_of_le_of_lt _ ( hcapSk i );
    have h_markov : (Finset.card (Finset.filter (fun v => (badCount G C dcap ε Tset v : ℝ) > thr) (C i))) * thr ≤ ∑ v ∈ C i, (badCount G C dcap ε Tset v : ℝ) := by
      have h_markov : ∀ v ∈ Finset.filter (fun v => (badCount G C dcap ε Tset v : ℝ) > thr) (C i), (badCount G C dcap ε Tset v : ℝ) ≥ thr := by
        exact fun v hv => le_of_lt <| Finset.mem_filter.mp hv |>.2;
      exact le_trans ( by simp +decide [ mul_comm ] ) ( Finset.sum_le_sum h_markov ) |> le_trans <| Finset.sum_le_sum_of_subset_of_nonneg ( Finset.filter_subset _ _ ) fun _ _ _ => Nat.cast_nonneg _;
    have h_sum_badCount : ∑ v ∈ C i, (badCount G C dcap ε Tset v : ℝ) = ∑ m ∈ Tset, ((C i).filter (fun v => ((C m).filter (fun x => G.Adj v x)).card < (dcap m - ε) * ((C m).card : ℝ))).card := by
      simp +decide [ badCount ];
      simp +decide only [card_filter];
      exact mod_cast Finset.sum_comm;
    simp_all +decide;
    rw [ le_div_iff₀ hthr ] ; linarith [ hatyp i hi ];
  · refine' lt_of_le_of_lt _ ( hcapSk i );
    simp +decide at hi ⊢;
    by_cases hα : Nonempty α;
    · exact div_nonneg ( le_trans ( Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _ ) ( hatyp _ ( hcluA_H hα.some ) ) ) hthr.le;
    · simp_all +decide [ Function.Injective ]);
  obtain ⟨ f, hf₁, hf₂, hf₃, hf₄ ⟩ := this; specialize h_contra f hf₁ hf₂ hf₄; simp_all +decide ;
  exact h_contra.choose_spec.not_ge ( hf₃ _ )

end Erdos550
