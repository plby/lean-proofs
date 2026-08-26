/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.HierarchicalCanonicalCleaning
import ErdosProblems.Erdos547b.LargeClusterReservoir

/-!
# Selecting the hierarchical global root in a quantitative reservoir

Uniformity is retained on the whole large cluster.  The selected image,
however, lies in Zhao's smaller high-degree reservoir.  We intersect that
reservoir only with an explicitly bounded union of whole-pair atypical sets;
we never assert uniformity of the sliced pair.
-/

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoHierarchicalRootReservoir

open Finset Fintype SimpleGraph
open Erdos547b.ZhaoStability
open Erdos547b.ZhaoQuantitativeLargeClusters
open Erdos547b.ZhaoLemma59Hierarchical
open Erdos547b.ZhaoLemma59HierarchicalOnline
open Erdos547b.ZhaoLemma59HierarchicalCanonical
open Erdos547b.ZhaoLemma59HierarchicalCanonical.HierarchicalSegmentForest

universe u v

/-- Choose the original-root image from a specified subreservoir of the
regularity source cluster. -/
theorem exists_oneRootImage_in_reservoir_of_bad_card
    {s : ℕ} {B : Type u} {RootGroup : Type*}
    [Fintype B] [DecidableEq B]
    (F : Erdos547b.ZhaoLemma59Hierarchical.HierarchicalSegmentForest 1 s)
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (rho : ℝ) (A reservoir : Finset B)
    (rootGroup : Fin s → RootGroup) (rootRaw : RootGroup → Finset B)
    (hreservoir : reservoir ⊆ A)
    (hbad : #(oneRootBad F G rho A rootGroup rootRaw) < #reservoir) :
    ∃ z ∈ reservoir, ∀ i, F.parent i = Sum.inl 0 →
      z ∈ Erdos547b.RegularPair.cleanedSide G rho A
        (rootRaw (rootGroup i)) := by
  classical
  have hpos : 0 < #(reservoir \ oneRootBad F G rho A rootGroup rootRaw) := by
    have hinter : #(reservoir ∩ oneRootBad F G rho A rootGroup rootRaw) ≤
        #(oneRootBad F G rho A rootGroup rootRaw) :=
      Finset.card_le_card Finset.inter_subset_right
    have hinter' : #(oneRootBad F G rho A rootGroup rootRaw ∩ reservoir) ≤
        #(oneRootBad F G rho A rootGroup rootRaw) := by
      rw [Finset.inter_comm]
      exact hinter
    rw [Finset.card_sdiff]
    omega
  obtain ⟨z, hz⟩ := Finset.card_pos.mp hpos
  have hzReservoir := (Finset.mem_sdiff.mp hz).1
  refine ⟨z, hzReservoir, ?_⟩
  intro i hp
  rw [Erdos547b.RegularPair.cleanedSide]
  refine Finset.mem_sdiff.mpr ⟨hreservoir hzReservoir, ?_⟩
  intro hzbad
  apply (Finset.mem_sdiff.mp hz).2
  apply Finset.mem_biUnion.mpr
  refine ⟨i, ?_, hzbad⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩

/-- Whole-cluster uniformity bounds the union of bad choices, while
quantitative largeness supplies the high-degree reservoir avoiding it. -/
theorem exists_highDegree_oneRootImage
    {s : ℕ} {B : Type u} {I : Type v} {RootGroup : Type*}
    [Fintype B] [DecidableEq B]
    [Fintype I] [DecidableEq I]
    (F : Erdos547b.ZhaoLemma59Hierarchical.HierarchicalSegmentForest 1 s)
    (Gpair Gdegree : SimpleGraph B)
    [DecidableRel Gpair.Adj] [DecidableRel Gdegree.Adj]
    (rho : ℝ) (P : ClusterAssignment B I) (A : I)
    (threshold quota : ℕ)
    (hA : A ∈ largeClustersAtLeast P Gdegree threshold quota)
    (rootGroup : Fin s → RootGroup) (rootRaw : RootGroup → Finset B)
    (huniform : ∀ i, F.parent i = Sum.inl 0 →
      Gpair.IsUniform rho (clusterVertices P A) (rootRaw (rootGroup i)))
    (hrho : rho ≤ 1)
    (hbadBudget :
      (#(Finset.univ.filter fun i ↦ F.parent i = Sum.inl 0) : ℝ) *
          (rho * #(clusterVertices P A)) < quota) :
    ∃ z ∈ largeVertexReservoir P Gdegree threshold A,
      threshold ≤ Gdegree.degree z ∧
      ∀ i, F.parent i = Sum.inl 0 →
        z ∈ Erdos547b.RegularPair.cleanedSide Gpair rho
          (clusterVertices P A) (rootRaw (rootGroup i)) := by
  have hbadReal :
      (#(oneRootBad F Gpair rho (clusterVertices P A) rootGroup rootRaw) : ℝ) <
        quota :=
    (card_oneRootBad_le F Gpair rho (clusterVertices P A) rootGroup rootRaw
      huniform hrho).trans_lt hbadBudget
  have hquotaCard : quota ≤
      (largeVertexReservoir P Gdegree threshold A).card :=
    largeVertexReservoir_card P Gdegree threshold quota hA
  have hbad :
      #(oneRootBad F Gpair rho (clusterVertices P A) rootGroup rootRaw) <
        #(largeVertexReservoir P Gdegree threshold A) := by
    have hbadNat :
        #(oneRootBad F Gpair rho (clusterVertices P A) rootGroup rootRaw) <
          quota := by
      exact_mod_cast hbadReal
    exact hbadNat.trans_le hquotaCard
  obtain ⟨z, hz, hclean⟩ :=
    exists_oneRootImage_in_reservoir_of_bad_card F Gpair rho
      (clusterVertices P A) (largeVertexReservoir P Gdegree threshold A)
      rootGroup rootRaw
      (largeVertexReservoir_subset_cluster P Gdegree threshold A) hbad
  exact ⟨z, hz,
    degree_of_mem_largeVertexReservoir P Gdegree threshold A hz, hclean⟩

/-! ## Target-relative original-root selection -/

/-- Bad choices in the actual original-root reservoir, measured against
the density of each whole source--target cluster pair.  This is the honest
form when the hierarchy targets are quantitative subreservoirs rather than
entire regularity clusters. -/
noncomputable def oneRootTargetBad
    {s : ℕ} {B : Type u} {RootGroup : Type*}
    [Fintype B] [DecidableEq B]
    (F : Erdos547b.ZhaoLemma59Hierarchical.HierarchicalSegmentForest 1 s)
    (G : SimpleGraph B) [DecidableRel G.Adj] (rho : ℝ)
    (sourceWhole sourceRaw : Finset B)
    (rootGroup : Fin s → RootGroup)
    (rootWhole rootRaw : RootGroup → Finset B) : Finset B := by
  classical
  exact (Finset.univ.filter fun i ↦ F.parent i = Sum.inl 0).biUnion fun i ↦
    targetLowDegreeVertices G rho sourceWhole (rootWhole (rootGroup i))
      sourceRaw (rootRaw (rootGroup i))

/-- Whole-pair uniformity bounds every direct target-relative bad set; no
uniformity of a sliced pair is asserted. -/
theorem card_oneRootTargetBad_le
    {s : ℕ} {B : Type u} {RootGroup : Type*}
    [Fintype B] [DecidableEq B]
    (F : Erdos547b.ZhaoLemma59Hierarchical.HierarchicalSegmentForest 1 s)
    (G : SimpleGraph B) [DecidableRel G.Adj] (rho : ℝ)
    (sourceWhole sourceRaw : Finset B)
    (rootGroup : Fin s → RootGroup)
    (rootWhole rootRaw : RootGroup → Finset B)
    (hsourceSubset : sourceRaw ⊆ sourceWhole)
    (hsourceLarge : rho * #sourceWhole ≤ #sourceRaw)
    (huniform : ∀ i, F.parent i = Sum.inl 0 →
      G.IsUniform rho sourceWhole (rootWhole (rootGroup i)))
    (htargetSubset : ∀ i, F.parent i = Sum.inl 0 →
      rootRaw (rootGroup i) ⊆ rootWhole (rootGroup i))
    (htargetLarge : ∀ i, F.parent i = Sum.inl 0 →
      rho * #(rootWhole (rootGroup i)) ≤ #(rootRaw (rootGroup i))) :
    (#(oneRootTargetBad F G rho sourceWhole sourceRaw rootGroup
        rootWhole rootRaw) : ℝ) ≤
      (#(Finset.univ.filter fun i ↦ F.parent i = Sum.inl 0) : ℝ) *
        (rho * #sourceWhole) := by
  classical
  let I := Finset.univ.filter fun i ↦ F.parent i = Sum.inl 0
  have hcardNat :
      #(oneRootTargetBad F G rho sourceWhole sourceRaw rootGroup
          rootWhole rootRaw) ≤
        ∑ i ∈ I,
          #(targetLowDegreeVertices G rho sourceWhole
            (rootWhole (rootGroup i)) sourceRaw (rootRaw (rootGroup i))) :=
    Finset.card_biUnion_le
  calc
    (#(oneRootTargetBad F G rho sourceWhole sourceRaw rootGroup
        rootWhole rootRaw) : ℝ) ≤
        ∑ i ∈ I,
          (#(targetLowDegreeVertices G rho sourceWhole
            (rootWhole (rootGroup i)) sourceRaw
              (rootRaw (rootGroup i))) : ℝ) := by
      exact_mod_cast hcardNat
    _ ≤ ∑ _i ∈ I, rho * #sourceWhole := by
      apply Finset.sum_le_sum
      intro i hi
      have hp := (Finset.mem_filter.mp hi).2
      exact card_targetLowDegreeVertices_le G (huniform i hp) hsourceSubset
        (htargetSubset i hp) hsourceLarge (htargetLarge i hp)
    _ = (#I : ℝ) * (rho * #sourceWhole) := by simp
    _ = _ := by rfl

/-- Choose the original root inside an actual reservoir and obtain its real
degree into every actual direct target reservoir. -/
theorem exists_oneRootImage_in_targetReservoir
    {s : ℕ} {B : Type u} {RootGroup : Type*}
    [Fintype B] [DecidableEq B]
    (F : Erdos547b.ZhaoLemma59Hierarchical.HierarchicalSegmentForest 1 s)
    (G : SimpleGraph B) [DecidableRel G.Adj] (rho : ℝ)
    (sourceWhole sourceRaw : Finset B)
    (rootGroup : Fin s → RootGroup)
    (rootWhole rootRaw : RootGroup → Finset B)
    (hsourceSubset : sourceRaw ⊆ sourceWhole)
    (hsourceLarge : rho * #sourceWhole ≤ #sourceRaw)
    (huniform : ∀ i, F.parent i = Sum.inl 0 →
      G.IsUniform rho sourceWhole (rootWhole (rootGroup i)))
    (htargetSubset : ∀ i, F.parent i = Sum.inl 0 →
      rootRaw (rootGroup i) ⊆ rootWhole (rootGroup i))
    (htargetLarge : ∀ i, F.parent i = Sum.inl 0 →
      rho * #(rootWhole (rootGroup i)) ≤ #(rootRaw (rootGroup i)))
    (hbadBudget :
      (#(Finset.univ.filter fun i ↦ F.parent i = Sum.inl 0) : ℝ) *
          (rho * #sourceWhole) < #sourceRaw) :
    ∃ z ∈ sourceRaw, ∀ i, F.parent i = Sum.inl 0 →
      (G.edgeDensity sourceWhole (rootWhole (rootGroup i)) - rho) *
          #(rootRaw (rootGroup i)) ≤
        (#((rootRaw (rootGroup i)).filter (G.Adj z)) : ℝ) := by
  classical
  have hbadReal :
      (#(oneRootTargetBad F G rho sourceWhole sourceRaw rootGroup
          rootWhole rootRaw) : ℝ) < #sourceRaw :=
    (card_oneRootTargetBad_le F G rho sourceWhole sourceRaw rootGroup
      rootWhole rootRaw hsourceSubset hsourceLarge huniform htargetSubset
      htargetLarge).trans_lt hbadBudget
  have hbad :
      #(oneRootTargetBad F G rho sourceWhole sourceRaw rootGroup
          rootWhole rootRaw) < #sourceRaw := by
    exact_mod_cast hbadReal
  have hpos : 0 < #(sourceRaw \ oneRootTargetBad F G rho sourceWhole
      sourceRaw rootGroup rootWhole rootRaw) := by
    have hinter : #(sourceRaw ∩ oneRootTargetBad F G rho sourceWhole sourceRaw
        rootGroup rootWhole rootRaw) ≤
        #(oneRootTargetBad F G rho sourceWhole sourceRaw rootGroup
          rootWhole rootRaw) :=
      Finset.card_le_card Finset.inter_subset_right
    have hinter' : #(oneRootTargetBad F G rho sourceWhole sourceRaw rootGroup
        rootWhole rootRaw ∩ sourceRaw) ≤
        #(oneRootTargetBad F G rho sourceWhole sourceRaw rootGroup
          rootWhole rootRaw) := by
      rw [Finset.inter_comm]
      exact hinter
    rw [Finset.card_sdiff]
    omega
  obtain ⟨z, hz⟩ := Finset.card_pos.mp hpos
  have hzRaw := (Finset.mem_sdiff.mp hz).1
  refine ⟨z, hzRaw, ?_⟩
  intro i hp
  apply target_degree_ge_of_not_mem_lowDegree G rho sourceWhole
    (rootWhole (rootGroup i)) sourceRaw (rootRaw (rootGroup i)) z hzRaw
  intro hzLow
  apply (Finset.mem_sdiff.mp hz).2
  apply Finset.mem_biUnion.mpr
  exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩, hzLow⟩

end Erdos547b.ZhaoHierarchicalRootReservoir

#print axioms Erdos547b.ZhaoHierarchicalRootReservoir.exists_oneRootImage_in_reservoir_of_bad_card
#print axioms Erdos547b.ZhaoHierarchicalRootReservoir.exists_highDegree_oneRootImage
#print axioms Erdos547b.ZhaoHierarchicalRootReservoir.exists_oneRootImage_in_targetReservoir
