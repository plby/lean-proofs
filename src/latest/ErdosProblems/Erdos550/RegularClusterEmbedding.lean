import Mathlib
import ErdosProblems.Erdos550.RegularPairEmbedding
import ErdosProblems.Erdos550.RegularPairTools

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Multi-cluster candidate-set tree/forest embedding (local engine of the tree Key Lemma)

This file generalises the single-regular-pair candidate-set engine
`Erdos550.regularPair_forest_embedding` to a **multi-cluster** setting.  It uses
an indexed family of pairwise-disjoint clusters `C : ι → Finset V` and a reduced
graph `R` on the index set, where every `R`-edge `(i,j)` is an
`ε`-uniform pair `(C i, C j)` of density `≥ d`.

Given a rooted forest on `α` (encoded by `parent`/`rank`) together with a
cluster-assignment `clu : α → ι` that is a homomorphism into `R` along parent
links, and provided each cluster's *load* plus a `B·ε`-slack fits inside its
`(d−ε)`-capacity (where `B` bounds the number of distinct child-clusters of any
single forest vertex), there is an injective embedding sending each vertex into
its prescribed cluster and every forest edge to an edge of `G`.

The single analytic ingredient beyond the elementary pair lemmas is
`Erdos550.good_fresh_neighbor_clusters`: a fresh neighbour of an already-placed
good vertex that is *simultaneously* good toward every cluster in a given finite
set `J` (a union bound over `J` of the per-pair "few low-degree vertices" fact
`Erdos550.isUniform_few_low_degree`).
-/

open SimpleGraph Finset

namespace Erdos550

/-
**Multi-cluster candidate-set extension step.**

Let `C : ι → Finset V` be clusters and `i : ι`, `p : V` with `p` *good toward*
`C i` (at least `(d−ε)·|C i|` neighbours in `C i`).  Let `J : Finset ι` be a set
of clusters, each of which forms an `ε`-uniform pair `(C i, C j)` of density
`≥ d` with `C i`.  If the used set `U` is small enough that
`|U| + |J|·ε·|C i| < (d−ε)·|C i|`, then there is a vertex `w ∈ C i` adjacent to
`p`, avoiding `U`, that is itself good toward every cluster `C j` (`j ∈ J`).
-/
lemma good_fresh_neighbor_clusters
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {ε d : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    {ι : Type*} [DecidableEq ι] {C : ι → Finset V}
    {i : ι} {p : V} {U : Finset V} {J : Finset ι}
    (hi : (C i).Nonempty)
    (hneJ : ∀ j ∈ J, (C j).Nonempty)
    (huniJ : ∀ j ∈ J, G.IsUniform ε (C i) (C j))
    (hdensJ : ∀ j ∈ J, d ≤ (G.edgeDensity (C i) (C j) : ℝ))
    (hpdeg : (d - ε) * ((C i).card : ℝ)
        ≤ (((C i).filter (fun b => G.Adj p b)).card : ℝ))
    (hU : (U.card : ℝ) + (J.card : ℝ) * (ε * ((C i).card : ℝ))
        < (d - ε) * ((C i).card : ℝ)) :
    ∃ w ∈ C i, G.Adj p w ∧ w ∉ U ∧
      ∀ j ∈ J, (d - ε) * ((C j).card : ℝ)
        ≤ (((C j).filter (fun b => G.Adj w b)).card : ℝ) := by
  obtain ⟨w, hw⟩ : ∃ w ∈ C i, G.Adj p w ∧ w ∉ U ∧ ∀ j ∈ J, w ∉ (C i).filter (fun w => ((C j).filter (fun b => G.Adj w b)).card < ((G.edgeDensity (C i) (C j) : ℝ) - ε) * (C j).card) := by
    contrapose! hU;
    refine' le_trans hpdeg ( le_trans ( Nat.cast_le.mpr <| show _ ≤ _ from _ ) _ );
    exact ( U ∩ C i ).card + ( Finset.biUnion J fun j => Finset.filter ( fun w => ( Finset.card ( Finset.filter ( fun b => G.Adj w b ) ( C j ) ) : ℝ ) < ( G.edgeDensity ( C i ) ( C j ) - ε ) * ( Finset.card ( C j ) : ℝ ) ) ( C i ) ).card;
    · refine' le_trans _ ( Finset.card_union_le _ _ );
      exact Finset.card_le_card fun x hx => by by_cases hx' : x ∈ U <;> aesop;
    · refine' le_trans ( Nat.cast_le.mpr ( add_le_add ( Finset.card_le_card ( Finset.inter_subset_left ) ) ( Finset.card_biUnion_le ) ) ) _ ; norm_num;
      refine' le_trans ( Finset.sum_le_sum fun j hj => Nat.cast_le.mpr <| show _ ≤ _ from _ ) _;
      use fun j => Nat.floor ( ε * ( C i |> Finset.card ) );
      · have := isUniform_few_low_degree G hε0 hε1 hi ( hneJ j hj ) ( huniJ j hj ) ; norm_num at * ; exact Nat.le_floor <| mod_cast this.le;
      · exact le_trans ( Finset.sum_le_sum fun _ _ => Nat.floor_le ( by positivity ) ) ( by simp +decide );
  refine' ⟨ w, hw.1, hw.2.1, hw.2.2.1, fun j hj => _ ⟩;
  simp_all +decide [ Finset.mem_filter ];
  exact le_trans ( mul_le_mul_of_nonneg_right ( sub_le_sub_right ( hdensJ j hj ) _ ) ( Nat.cast_nonneg _ ) ) ( hw.2.2.2 j hj hw.1 )

/-
**Multi-cluster root-placement step.**

A good, unused vertex of cluster `C i` that is good toward every cluster in `J`.
-/
lemma exists_good_unused_clusters
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {ε d : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    {ι : Type*} [DecidableEq ι] {C : ι → Finset V}
    {i : ι} {U : Finset V} {J : Finset ι}
    (hi : (C i).Nonempty)
    (hneJ : ∀ j ∈ J, (C j).Nonempty)
    (huniJ : ∀ j ∈ J, G.IsUniform ε (C i) (C j))
    (hdensJ : ∀ j ∈ J, d ≤ (G.edgeDensity (C i) (C j) : ℝ))
    (hU : (U.card : ℝ) + (J.card : ℝ) * (ε * ((C i).card : ℝ))
        < ((C i).card : ℝ)) :
    ∃ w ∈ C i, w ∉ U ∧
      ∀ j ∈ J, (d - ε) * ((C j).card : ℝ)
        ≤ (((C j).filter (fun b => G.Adj w b)).card : ℝ) := by
  -- By definition of $B$, we know that $|B| < |C i|$.
  have hB_card : (U ∪ Finset.biUnion J (fun j => (C i).filter (fun w => ((C j).filter (fun b => G.Adj w b)).card < (d - ε) * (C j).card))).card < (C i).card := by
    have h_card_biUnion : (J.biUnion (fun j => (C i).filter (fun w => ((C j).filter (fun b => G.Adj w b)).card < (d - ε) * ((C j).card : ℝ)))).card ≤ J.card * ε * (C i).card := by
      have h_card_biUnion : ∀ j ∈ J, (Finset.filter (fun w => ((C j).filter (fun b => G.Adj w b)).card < (d - ε) * ((C j).card : ℝ)) (C i)).card < ε * (C i).card := by
        intro j hj
        have h_card_lt : ((C i).filter (fun w => ((C j).filter (fun b => G.Adj w b)).card < (d - ε) * ((C j).card : ℝ))).card ≤ ((C i).filter (fun w => ((C j).filter (fun b => G.Adj w b)).card < ((G.edgeDensity (C i) (C j) : ℝ) - ε) * ((C j).card : ℝ))).card := by
          exact Finset.card_mono fun x hx => Finset.mem_filter.mpr ⟨ Finset.mem_filter.mp hx |>.1, lt_of_lt_of_le ( Finset.mem_filter.mp hx |>.2 ) ( mul_le_mul_of_nonneg_right ( sub_le_sub_right ( hdensJ j hj ) _ ) ( Nat.cast_nonneg _ ) ) ⟩;
        exact lt_of_le_of_lt ( Nat.cast_le.mpr h_card_lt ) ( by simpa using! isUniform_few_low_degree G hε0 hε1 hi ( hneJ j hj ) ( huniJ j hj ) );
      refine' le_trans ( Nat.cast_le.mpr ( Finset.card_biUnion_le ) ) _;
      simpa [ mul_assoc ] using! Finset.sum_le_sum fun j hj => le_of_lt ( h_card_biUnion j hj );
    exact_mod_cast ( by nlinarith [ show ( Finset.card ( U ∪ Finset.biUnion J fun j => Finset.filter ( fun w => ( Finset.card ( Finset.filter ( fun b => G.Adj w b ) ( C j ) ) : ℝ ) < ( d - ε ) * Finset.card ( C j ) ) ( C i ) ) : ℝ ) ≤ Finset.card U + Finset.card ( Finset.biUnion J fun j => Finset.filter ( fun w => ( Finset.card ( Finset.filter ( fun b => G.Adj w b ) ( C j ) ) : ℝ ) < ( d - ε ) * Finset.card ( C j ) ) ( C i ) ) by exact_mod_cast Finset.card_union_le _ _ ] : ( Finset.card ( U ∪ Finset.biUnion J fun j => Finset.filter ( fun w => ( Finset.card ( Finset.filter ( fun b => G.Adj w b ) ( C j ) ) : ℝ ) < ( d - ε ) * Finset.card ( C j ) ) ( C i ) ) : ℝ ) < Finset.card ( C i ) );
  obtain ⟨ w, hw ⟩ := Finset.not_subset.mp ( fun h => hB_card.not_ge <| Finset.card_le_card h ) ; use w; aesop;

/-
**Multi-cluster rooted-forest embedding (candidate-set engine).**

Let `C : ι → Finset V` be pairwise-disjoint nonempty clusters and `R` a graph on
`ι` such that every `R`-edge `(i,j)` is an `ε`-uniform pair `(C i, C j)` of
density `≥ d`.  Let a rooted forest on `α` be given by `parent`/`rank` together
with a cluster-assignment `clu : α → ι` that is a homomorphism into `R` along
parent links.  Let `BB` bound the number of distinct child-clusters of any single
forest vertex.  If for every cluster `i` the load `#{a : clu a = i}` plus the
slack `BB·ε·|C i|` is `< (d−ε)·|C i|`, then there is an injective `f : α → V`
sending each vertex into its cluster and every forest edge to an edge of `G`.

This is the multi-cluster generalisation of `regularPair_forest_embedding`: it is
the local embedding engine of the tree "Key Lemma" of the regularity proof of the
Erdős–Sós theorem, embedding a rooted forest across the regular pairs of a reduced
graph via a load-balanced homomorphism.
-/
set_option maxHeartbeats 1000000 in
theorem regularClusters_forest_embedding
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {ε d : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hd1 : d ≤ 1)
    {ι : Type*} [DecidableEq ι] (C : ι → Finset V) (R : SimpleGraph ι)
    (hne : ∀ i, (C i).Nonempty)
    (hdisj : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (huni : ∀ i j, R.Adj i j → G.IsUniform ε (C i) (C j))
    (hdens : ∀ i j, R.Adj i j → d ≤ (G.edgeDensity (C i) (C j) : ℝ))
    {α : Type*} [Fintype α] [DecidableEq α]
    (parent : α → Option α) (rank : α → ℕ)
    (hrank : ∀ a b, parent a = some b → rank b < rank a)
    (clu : α → ι)
    (hhom : ∀ a b, parent a = some b → R.Adj (clu a) (clu b))
    (BB : ℕ)
    (hB : ∀ a, ((univ.filter (fun x => parent x = some a)).image clu).card ≤ BB)
    (hcap : ∀ i, ((univ.filter (fun a => clu a = i)).card : ℝ)
              + (BB : ℝ) * (ε * ((C i).card : ℝ)) < (d - ε) * ((C i).card : ℝ)) :
    ∃ f : α → V, Function.Injective f ∧
      (∀ a, f a ∈ C (clu a)) ∧
      (∀ a b, parent a = some b → G.Adj (f a) (f b)) := by
  have hkey : ∀ S : Finset α, (∀ a ∈ S, ∀ b, parent a = some b → b ∈ S) →
    ∃ f : α → V, Set.InjOn f S ∧
      (∀ a ∈ S, f a ∈ C (clu a)) ∧
      (∀ a ∈ S, ∀ j ∈ (univ.filter (fun x => parent x = some a)).image clu, (d - ε) * ((C j).card : ℝ) ≤ (((C j).filter (fun b => G.Adj (f a) b)).card : ℝ)) ∧
      (∀ a ∈ S, ∀ b, parent a = some b → G.Adj (f a) (f b)) := by
        intro S hS
        induction' S using Finset.strongInduction with S ih S ih;
        by_cases hS_empty : S = ∅;
        · simp [hS_empty];
          contrapose! hcap;
          exact False.elim ( hcap.2.elim ( Classical.choose ( hne ( clu hcap.1.some ) ) ) );
        · obtain ⟨a, haS, ha_max⟩ : ∃ a ∈ S, ∀ b ∈ S, rank b ≤ rank a := by
            exact Finset.exists_max_image _ _ ( Finset.nonempty_of_ne_empty hS_empty );
          obtain ⟨f', hf'⟩ := ih (S.erase a) (by
          exact Finset.erase_ssubset haS) (by
          grind);
          by_cases ha_root : parent a = none;
          · obtain ⟨w, hw⟩ : ∃ w ∈ C (clu a), w ∉ (S.erase a).image f' ∧ ∀ j ∈ (univ.filter (fun x => parent x = some a)).image clu, (d - ε) * ((C j).card : ℝ) ≤ (((C j).filter (fun b => G.Adj w b)).card : ℝ) := by
              have hU : (Finset.card (Finset.image f' (S.erase a) ∩ C (clu a)) : ℝ) + (Finset.card (Finset.image clu {x | parent x = some a}) : ℝ) * (ε * ((C (clu a)).card : ℝ)) < ((C (clu a)).card : ℝ) := by
                have hU_root : (Finset.card (Finset.image f' (S.erase a) ∩ C (clu a)) : ℝ) ≤ (Finset.card (Finset.filter (fun x => clu x = clu a) S) - 1 : ℝ) := by
                  have hU_root : Finset.image f' (S.erase a) ∩ C (clu a) ⊆ Finset.image f' (Finset.filter (fun x => clu x = clu a) (S.erase a)) := by
                    simp +decide [ Finset.subset_iff ];
                    intro x b hb hbS hx hx';
                    use b;
                    simp [hb, hbS, hx];
                    exact Classical.not_not.1 fun h => Finset.disjoint_left.1 ( hdisj _ _ h ) ( hf'.2.1 b ( Finset.mem_erase_of_ne_of_mem hb hbS ) ) ( hx ▸ hx' );
                  refine' le_trans ( Nat.cast_le.mpr ( Finset.card_le_card hU_root ) ) _;
                  rw [ Finset.card_image_of_injOn ];
                  · rw [ show ( Finset.filter ( fun x => clu x = clu a ) S ) = Finset.filter ( fun x => clu x = clu a ) ( S.erase a ) ∪ { a } from ?_, Finset.card_union ] <;> simp +decide [ haS ];
                    grind;
                  · exact hf'.1.mono ( by aesop_cat );
                have := hcap ( clu a );
                refine' lt_of_le_of_lt ( add_le_add hU_root ( mul_le_mul_of_nonneg_right ( Nat.cast_le.mpr ( hB a ) ) ( mul_nonneg hε0.le ( Nat.cast_nonneg _ ) ) ) ) _;
                refine' lt_of_le_of_lt _ ( lt_of_lt_of_le this _ );
                · exact add_le_add ( sub_le_self _ zero_le_one |> le_trans <| mod_cast Finset.card_mono <| Finset.filter_subset_filter _ <| Finset.subset_univ _ ) le_rfl;
                · exact mul_le_of_le_one_left ( Nat.cast_nonneg _ ) ( by linarith );
              convert! exists_good_unused_clusters G hε0 hε1 ( hne ( clu a ) ) _ _ _ hU using 1;
              any_goals intro j hj; rw [ SimpleGraph.edgeDensity_comm ] ; exact hdens _ _ ( by
                grind );
              · grind;
              · exact fun j hj => hne j;
              · simp +decide [  ];
                exact fun b hb => huni _ _ ( hhom _ _ hb |> SimpleGraph.Adj.symm );
            refine' ⟨ fun x => if x = a then w else f' x, _, _, _, _ ⟩ <;> simp +decide [ Set.InjOn, * ];
            · intro x₁ hx₁ x₂ hx₂ h; by_cases hx₁a : x₁ = a <;> by_cases hx₂a : x₂ = a <;> simp +decide [ hx₁a, hx₂a ] at h ⊢;
              · exact False.elim ( hw.2.1 ( h.symm ▸ Finset.mem_image_of_mem _ ( Finset.mem_erase_of_ne_of_mem hx₂a hx₂ ) ) );
              · exact hw.2.1 ( h ▸ Finset.mem_image_of_mem _ ( Finset.mem_erase_of_ne_of_mem hx₁a hx₁ ) );
              · exact hf'.1 ( Finset.mem_erase_of_ne_of_mem hx₁a hx₁ ) ( Finset.mem_erase_of_ne_of_mem hx₂a hx₂ ) h;
            · grind;
            · grind;
            · grind;
          · obtain ⟨b, hb⟩ : ∃ b, parent a = some b := by
              exact Option.ne_none_iff_exists'.mp ha_root;
            obtain ⟨w, hw⟩ : ∃ w ∈ C (clu a), G.Adj (f' b) w ∧ w ∉ ((S.erase a).image f') ∩ C (clu a) ∧ ∀ j ∈ (univ.filter (fun x => parent x = some a)).image clu, (d - ε) * ((C j).card : ℝ) ≤ (((C j).filter (fun b => G.Adj w b)).card : ℝ) := by
              have hU : ((Finset.image f' (S.erase a) ∩ C (clu a)).card : ℝ) + (Finset.card (Finset.image clu (Finset.filter (fun x => parent x = some a) Finset.univ)) : ℝ) * (ε * ((C (clu a)).card : ℝ)) < (d - ε) * ((C (clu a)).card : ℝ) := by
                refine' lt_of_le_of_lt _ ( hcap ( clu a ) );
                gcongr;
                · refine' le_trans ( Finset.card_le_card _ ) _;
                  exact Finset.image f' ( Finset.filter ( fun x => clu x = clu a ) ( S.erase a ) );
                  · simp_all +decide [ Finset.disjoint_left ];
                    grind;
                  · exact Finset.card_image_le.trans ( Finset.card_mono <| fun x hx => by aesop );
                · exact hB a;
              apply good_fresh_neighbor_clusters G hε0 hε1 (hne (clu a)) (fun j hj => hne j) (fun j hj => huni (clu a) j (by
              simp +zetaDelta at *;
              obtain ⟨ x, hx, rfl ⟩ := hj; exact hhom x a hx |> SimpleGraph.Adj.symm;)) (fun j hj => hdens (clu a) j (by
              simp +zetaDelta at *;
              obtain ⟨ x, hx, rfl ⟩ := hj; exact hhom x a hx |> SimpleGraph.Adj.symm;)) (by
              grind +splitIndPred) (by
              exact hU);
            refine' ⟨ Function.update f' a w, _, _, _, _ ⟩;
            · intro x hx y hy hxy;
              by_cases hx' : x = a <;> by_cases hy' : y = a <;> simp +decide [ hx', hy', Function.update_apply ] at hxy ⊢;
              · grind;
              · grind;
              · exact hf'.1 ( Finset.mem_erase_of_ne_of_mem hx' hx ) ( Finset.mem_erase_of_ne_of_mem hy' hy ) hxy;
            · grind +splitImp;
            · grind;
            · intro x hx y hy; by_cases hx' : x = a <;> by_cases hy' : y = a <;> simp +decide [ *, Function.update_apply ] at *;
              · grind +splitImp;
              · exact hw.2.1.symm |> fun h => by subst hy; exact h;
              · grind;
  obtain ⟨ f, hf₁, hf₂, hf₃, hf₄ ⟩ := hkey univ fun a _ b hab => by simp;
  exact ⟨ f, fun a b hab => hf₁ ( Finset.mem_univ a ) ( Finset.mem_univ b ) hab, fun a => hf₂ a ( Finset.mem_univ a ), fun a b hab => hf₄ a ( Finset.mem_univ a ) b hab ⟩

end Erdos550
