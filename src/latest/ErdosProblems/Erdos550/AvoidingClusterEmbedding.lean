import Mathlib
import ErdosProblems.Erdos550.WeightedClusterEmbedding

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Weighted multi-cluster forest embedding avoiding a per-cluster forbidden set

This generalises `Erdos550.regularClusters_forest_embedding_weighted` by
additionally forbidding, in each cluster `i`, a
prescribed set `Uav i ⊆ V`: the produced embedding places no vertex of the forest
onto a vertex of `Uav (clu a)`.  The capacity budget `hcap` simply pays for the
extra `|Uav i|` forbidden vertices in each cluster.

This is used for the **skeleton** of a τ-fine tree partition: the skeleton is
embedded into the dense head clusters while avoiding the (small) set of vertices
that are *atypical* toward the regular-matching clusters, so that the resulting
skeleton images are typical toward every matching cluster — exactly the
`hanc` hypothesis consumed by
`Erdos550.combined_skeleton_shrub_embedding`.
-/

open SimpleGraph Finset

namespace Erdos550

set_option maxHeartbeats 1000000 in
/-- **Avoiding weighted multi-cluster candidate-set forest embedding.**

Like `regularClusters_forest_embedding_weighted`, but every placed vertex also
avoids a prescribed per-cluster forbidden set `Uav (clu a)`. -/
theorem regularClusters_forest_embedding_weighted_avoiding
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    {ι : Type*} [DecidableEq ι] (C : ι → Finset V) (R : SimpleGraph ι) (dcap : ι → ℝ)
    (hdcap1 : ∀ i, dcap i ≤ 1)
    (hne : ∀ i, (C i).Nonempty)
    (hdisj : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (huni : ∀ i j, R.Adj i j → G.IsUniform ε (C i) (C j))
    (hdens : ∀ i j, R.Adj i j → dcap j ≤ (G.edgeDensity (C i) (C j) : ℝ))
    {α : Type*} [Fintype α] [DecidableEq α]
    (parent : α → Option α) (rank : α → ℕ)
    (hrank : ∀ a b, parent a = some b → rank b < rank a)
    (clu : α → ι)
    (hhom : ∀ a b, parent a = some b → R.Adj (clu a) (clu b))
    (BB : ℕ)
    (hB : ∀ a, ((univ.filter (fun x => parent x = some a)).image clu).card ≤ BB)
    (Uav : ι → Finset V)
    (hcap : ∀ i, ((univ.filter (fun a => clu a = i)).card : ℝ) + ((Uav i).card : ℝ)
              + (BB : ℝ) * (ε * ((C i).card : ℝ)) < (dcap i - ε) * ((C i).card : ℝ)) :
    ∃ f : α → V, Function.Injective f ∧
      (∀ a, f a ∈ C (clu a)) ∧
      (∀ a, f a ∉ Uav (clu a)) ∧
      (∀ a b, parent a = some b → G.Adj (f a) (f b)) := by
  have hkey : ∀ S : Finset α, (∀ a ∈ S, ∀ b, parent a = some b → b ∈ S) →
    ∃ f : α → V, Set.InjOn f S ∧
      (∀ a ∈ S, f a ∈ C (clu a)) ∧
      (∀ a ∈ S, ∀ j ∈ (univ.filter (fun x => parent x = some a)).image clu, (dcap j - ε) * ((C j).card : ℝ) ≤ (((C j).filter (fun b => G.Adj (f a) b)).card : ℝ)) ∧
      (∀ a ∈ S, ∀ b, parent a = some b → G.Adj (f a) (f b)) ∧
      (∀ a ∈ S, f a ∉ Uav (clu a)) := by
        intro S hS
        induction' S using Finset.strongInduction with S ih S ih;
        by_cases hS_empty : S = ∅;
        · simp only [mem_image, mem_filter, mem_univ, true_and, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂];
          contrapose! hcap;
          exact False.elim ( hcap.2.elim ( Classical.choose ( hne ( clu hcap.1.some ) ) ) );
        · obtain ⟨a, haS, ha_max⟩ : ∃ a ∈ S, ∀ b ∈ S, rank b ≤ rank a := by
            exact Finset.exists_max_image _ _ ( Finset.nonempty_of_ne_empty hS_empty );
          obtain ⟨f', hf'⟩ := ih (S.erase a) (by
          exact Finset.erase_ssubset haS) (by
          grind);
          have himC : ((Finset.image f' (S.erase a) ∩ C (clu a)).card : ℝ)
              ≤ ((Finset.filter (fun x => clu x = clu a) Finset.univ).card : ℝ) := by
            refine le_trans (Nat.cast_le.mpr (Finset.card_le_card
              (show Finset.image f' (S.erase a) ∩ C (clu a)
                ⊆ Finset.image f' (Finset.filter (fun x => clu x = clu a) Finset.univ) from ?_))) ?_
            · intro y hy
              rw [Finset.mem_inter] at hy
              obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy.1
              refine Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, ?_⟩, rfl⟩
              by_contra hne'
              exact Finset.disjoint_left.1 (hdisj _ _ hne') (hf'.2.1 x hx) hy.2
            · exact_mod_cast Finset.card_image_le
          have hJprod : (((univ.filter (fun x => parent x = some a)).image clu).card : ℝ)
                * (ε * ((C (clu a)).card : ℝ))
              ≤ (BB : ℝ) * (ε * ((C (clu a)).card : ℝ)) := by
            apply mul_le_mul_of_nonneg_right (by exact_mod_cast hB a) (by positivity)
          by_cases ha_root : parent a = none;
          · obtain ⟨w, hwmem, hwnotU, hwgood⟩ := exists_good_unused_clusters_weighted (dtar := dcap) G hε0 hε1 (hne (clu a)) (fun j hj => hne j) (fun j hj => huni (clu a) j (by
              simp +zetaDelta at *;
              obtain ⟨ x, hx, rfl ⟩ := hj; exact hhom x a hx |> SimpleGraph.Adj.symm)) (fun j hj => hdens (clu a) j (by
              simp +zetaDelta at *;
              obtain ⟨ x, hx, rfl ⟩ := hj; exact hhom x a hx |> SimpleGraph.Adj.symm)) (show
                (((Finset.image f' (S.erase a) ∩ C (clu a)) ∪ Uav (clu a)).card : ℝ)
                + (((univ.filter (fun x => parent x = some a)).image clu).card : ℝ) * (ε * ((C (clu a)).card : ℝ))
                < ((C (clu a)).card : ℝ) by
              have hcardU : (((Finset.image f' (S.erase a) ∩ C (clu a)) ∪ Uav (clu a)).card : ℝ)
                  ≤ ((Finset.image f' (S.erase a) ∩ C (clu a)).card : ℝ) + ((Uav (clu a)).card : ℝ) := by
                exact_mod_cast Finset.card_union_le _ _
              have hdcaple : (dcap (clu a) - ε) * ((C (clu a)).card : ℝ) ≤ ((C (clu a)).card : ℝ) := by
                apply mul_le_of_le_one_left (Nat.cast_nonneg _); linarith [hdcap1 (clu a)]
              linarith [hcardU, himC, hJprod, hcap (clu a), hdcaple]);
            have hwnotimg : w ∉ Finset.image f' (S.erase a) :=
              fun h => hwnotU (Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨h, hwmem⟩));
            have hwnotUav : w ∉ Uav (clu a) := fun h => hwnotU (Finset.mem_union_right _ h);
            clear himC hJprod hwnotU;
            refine' ⟨ fun x => if x = a then w else f' x, _, _, _, _, _ ⟩ <;> simp +decide [ Set.InjOn, * ];
            · intro x₁ hx₁ x₂ hx₂ h; by_cases hx₁a : x₁ = a <;> by_cases hx₂a : x₂ = a <;> simp +decide [ hx₁a, hx₂a ] at h ⊢;
              · exact False.elim ( hwnotimg ( h.symm ▸ Finset.mem_image_of_mem _ ( Finset.mem_erase_of_ne_of_mem hx₂a hx₂ ) ) );
              · exact hwnotimg ( h ▸ Finset.mem_image_of_mem _ ( Finset.mem_erase_of_ne_of_mem hx₁a hx₁ ) );
              · exact hf'.1 ( Finset.mem_erase_of_ne_of_mem hx₁a hx₁ ) ( Finset.mem_erase_of_ne_of_mem hx₂a hx₂ ) h;
            · grind;
            · grind;
            · grind;
            · grind;
          · obtain ⟨b, hb⟩ : ∃ b, parent a = some b := by
              exact Option.ne_none_iff_exists'.mp ha_root;
            obtain ⟨w, hw⟩ : ∃ w ∈ C (clu a), G.Adj (f' b) w ∧ w ∉ ((Finset.image f' (S.erase a) ∩ C (clu a)) ∪ Uav (clu a)) ∧ ∀ j ∈ (univ.filter (fun x => parent x = some a)).image clu, (dcap j - ε) * ((C j).card : ℝ) ≤ (((C j).filter (fun b => G.Adj w b)).card : ℝ) := by
              have hU : (((Finset.image f' (S.erase a) ∩ C (clu a)) ∪ Uav (clu a)).card : ℝ) + (((univ.filter (fun x => parent x = some a)).image clu).card : ℝ) * (ε * ((C (clu a)).card : ℝ)) < (dcap (clu a) - ε) * ((C (clu a)).card : ℝ) := by
                have hcardU : (((Finset.image f' (S.erase a) ∩ C (clu a)) ∪ Uav (clu a)).card : ℝ)
                    ≤ ((Finset.image f' (S.erase a) ∩ C (clu a)).card : ℝ) + ((Uav (clu a)).card : ℝ) := by
                  exact_mod_cast Finset.card_union_le _ _
                linarith [hcardU, himC, hJprod, hcap (clu a)]
              apply good_fresh_neighbor_clusters_weighted (di := dcap (clu a)) (dtar := dcap) G hε0 hε1 (hne (clu a)) (fun j hj => hne j) (fun j hj => huni (clu a) j (by
              simp +zetaDelta at *;
              obtain ⟨ x, hx, rfl ⟩ := hj; exact hhom x a hx |> SimpleGraph.Adj.symm;)) (fun j hj => hdens (clu a) j (by
              simp +zetaDelta at *;
              obtain ⟨ x, hx, rfl ⟩ := hj; exact hhom x a hx |> SimpleGraph.Adj.symm;)) (by
              grind +splitIndPred) hU;
            have hwnotimg : w ∉ Finset.image f' (S.erase a) :=
              fun h => hw.2.2.1 (Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨h, hw.1⟩));
            have hwnotUav : w ∉ Uav (clu a) := fun h => hw.2.2.1 (Finset.mem_union_right _ h);
            clear himC hJprod;
            refine' ⟨ Function.update f' a w, _, _, _, _, _ ⟩;
            · intro x hx y hy hxy;
              by_cases hx' : x = a <;> by_cases hy' : y = a <;> simp +decide [ hx', hy', Function.update_apply ] at hxy ⊢;
              · exact False.elim ( hwnotimg ( hxy.symm ▸ Finset.mem_image_of_mem _ ( Finset.mem_erase_of_ne_of_mem hy' hy ) ) );
              · exact False.elim ( hwnotimg ( hxy ▸ Finset.mem_image_of_mem _ ( Finset.mem_erase_of_ne_of_mem hx' hx ) ) );
              · exact hf'.1 ( Finset.mem_erase_of_ne_of_mem hx' hx ) ( Finset.mem_erase_of_ne_of_mem hy' hy ) hxy;
            · intro x hx; by_cases hx' : x = a;
              · rw [hx', Function.update_self]; exact hw.1;
              · rw [Function.update_of_ne hx']; exact hf'.2.1 x ( Finset.mem_erase_of_ne_of_mem hx' hx );
            · intro x hx j hj; by_cases hx' : x = a;
              · subst hx'; rw [Function.update_self]; exact hw.2.2.2 j (by simpa using! hj);
              · rw [Function.update_of_ne hx']; exact hf'.2.2.1 x ( Finset.mem_erase_of_ne_of_mem hx' hx ) j hj;
            · intro x hx c hc; by_cases hx' : x = a;
              · subst hx'; rw [hb] at hc; injection hc with hc; subst hc;
                rw [Function.update_self, Function.update_of_ne (by rintro rfl; exact absurd (hrank _ _ hb) (lt_irrefl _))];
                exact hw.2.1.symm;
              · have hca : c ≠ a := by
                  rintro rfl; have h1 := hrank x c hc; have h2 := ha_max x hx; omega;
                rw [Function.update_of_ne hx', Function.update_of_ne hca];
                exact hf'.2.2.2.1 x ( Finset.mem_erase_of_ne_of_mem hx' hx ) c hc;
            · intro x hx; by_cases hx' : x = a;
              · rw [hx', Function.update_self]; exact hwnotUav;
              · rw [Function.update_of_ne hx']; exact hf'.2.2.2.2 x ( Finset.mem_erase_of_ne_of_mem hx' hx );
  obtain ⟨ f, hf₁, hf₂, hf₃, hf₄, hf₅ ⟩ := hkey univ fun a _ b hab => by simp;
  exact ⟨ f, fun a b hab => hf₁ ( Finset.mem_univ a ) ( Finset.mem_univ b ) hab, fun a => hf₂ a ( Finset.mem_univ a ), fun a => hf₅ a ( Finset.mem_univ a ), fun a b hab => hf₄ a ( Finset.mem_univ a ) b hab ⟩

end Erdos550
