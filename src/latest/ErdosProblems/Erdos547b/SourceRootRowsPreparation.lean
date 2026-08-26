/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceRootIncidence
import ErdosProblems.Erdos547b.SourceRootTruncation
import ErdosProblems.Erdos547b.Section6Dichotomy

/-!
# Selecting and realizing the two cleaned source roots

The two roots are chosen by the almost-all-target incidence estimate.
Their bad target unions are then removed from their incident edges. The
result is a literal subgraph with bounded degree loss and the upper-typical
inequality on every positive remaining source entry.
-/

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoSourceRootRowsPreparation

open Finset SimpleGraph Erdos547EC2
open Erdos547b.ZhaoStability Erdos547b.ZhaoSection6Dichotomy
open Erdos547b.ZhaoSourceRootIncidence Erdos547b.ZhaoSourceRootTruncation

theorem exists_two_clean_roots
    {V I : Type*} [Fintype V] [DecidableEq V] [DecidableEq I]
    (P : ClusterAssignment V I) (H : SimpleGraph V) [DecidableRel H.Adj]
    (A B : I) (hAB : A ≠ B) (poolA poolB : Finset V)
    (hpoolA : poolA ⊆ clusterVertices P A) (hpoolB : poolB ⊆ clusterVertices P B)
    (J : Finset I) (hJ : ∀ j ∈ J, j ≠ A ∧ j ≠ B)
    (N : ℕ) (hN : ∀ j ∈ J, (clusterVertices P j).card ≤ N)
    (ε δ : ℝ) (hδ : 0 < δ) (hεδ : ε ≤ δ ^ 2)
    (hAuniform : ∀ j ∈ J, H.IsUniform ε (clusterVertices P A) (clusterVertices P j))
    (hBuniform : ∀ j ∈ J, H.IsUniform ε (clusterVertices P B) (clusterVertices P j))
    (hAcard : δ * (clusterVertices P A).card < poolA.card)
    (hBcard : δ * (clusterVertices P B).card < poolB.card) :
    ∃ zA ∈ poolA, ∃ zB ∈ poolB, ∃ DA ⊆ J, ∃ DB ⊆ J,
      zA ≠ zB ∧
      ((clusterUnion P DA).card : ℝ) ≤ δ * J.card * N ∧
      ((clusterUnion P DB).card : ℝ) ≤ δ * J.card * N ∧
      let Hsource := truncateRoot (truncateRoot H zA (clusterUnion P DA))
        zB (clusterUnion P DB)
      Hsource ≤ H ∧
      DegreeLossAtMost H Hsource
        (max (clusterUnion P DA).card (clusterUnion P DB).card + 2) ∧
      (∀ j ∈ J, 0 < degreeInto Hsource zA (clusterVertices P j) →
        (degreeInto Hsource zA (clusterVertices P j) : ℝ) ≤
          (H.edgeDensity (clusterVertices P A) (clusterVertices P j) + ε) *
            (clusterVertices P j).card) ∧
      (∀ j ∈ J, 0 < degreeInto Hsource zB (clusterVertices P j) →
        (degreeInto Hsource zB (clusterVertices P j) : ℝ) ≤
          (H.edgeDensity (clusterVertices P B) (clusterVertices P j) + ε) *
            (clusterVertices P j).card) := by
  classical
  obtain ⟨zA, hzA, DA, hDA, hDAcard, hAupper⟩ := exists_root_upperTypical_most H
    (clusterVertices P A) poolA J (clusterVertices P) ε δ hδ hεδ
    hAuniform hpoolA hAcard
  obtain ⟨zB, hzB, DB, hDB, hDBcard, hBupper⟩ := exists_root_upperTypical_most H
    (clusterVertices P B) poolB J (clusterVertices P) ε δ hδ hεδ
    hBuniform hpoolB hBcard
  have hzAP : P zA = some A := (mem_clusterVertices P A zA).mp (hpoolA hzA)
  have hzBP : P zB = some B := (mem_clusterVertices P B zB).mp (hpoolB hzB)
  have hroots : zA ≠ zB := by
    intro h
    subst zB
    exact hAB (Option.some.inj (hzAP.symm.trans hzBP))
  have hzAclean : zA ∉ clusterUnion P DB := by
    intro hz
    obtain ⟨i, hi, hzi⟩ := (mem_clusterUnion P DB zA).mp hz
    have hiA : i = A := Option.some.inj (hzi.symm.trans hzAP)
    exact (hJ i (hDB hi)).1 hiA
  have hzBclean : zB ∉ clusterUnion P DA := by
    intro hz
    obtain ⟨i, hi, hzi⟩ := (mem_clusterUnion P DA zB).mp hz
    have hiB : i = B := Option.some.inj (hzi.symm.trans hzBP)
    exact (hJ i (hDA hi)).2 hiB
  have hmassA : ((clusterUnion P DA).card : ℝ) ≤ δ * J.card * N := by
    have hcount : ((clusterUnion P DA).card : ℝ) ≤ (DA.card : ℝ) * N := by
      exact_mod_cast card_clusterUnion_le P DA N (fun i hi => hN i (hDA hi))
    exact hcount.trans (mul_le_mul_of_nonneg_right hDAcard (by positivity))
  have hmassB : ((clusterUnion P DB).card : ℝ) ≤ δ * J.card * N := by
    have hcount : ((clusterUnion P DB).card : ℝ) ≤ (DB.card : ℝ) * N := by
      exact_mod_cast card_clusterUnion_le P DB N (fun i hi => hN i (hDB hi))
    exact hcount.trans (mul_le_mul_of_nonneg_right hDBcard (by positivity))
  let Hfirst := truncateRoot H zA (clusterUnion P DA)
  let Hsource := truncateRoot Hfirst zB (clusterUnion P DB)
  have hfirst : Hfirst ≤ H := truncateRoot_le H zA _
  have hsecond : Hsource ≤ Hfirst := truncateRoot_le Hfirst zB _
  have hsource : Hsource ≤ H := hsecond.trans hfirst
  refine ⟨zA, hzA, zB, hzB, DA, hDA, DB, hDB, hroots, hmassA, hmassB,
    hsource, ?_, ?_, ?_⟩
  · exact twoRoot_degree_loss H zA zB (clusterUnion P DA) (clusterUnion P DB)
      hroots hzAclean hzBclean
  · intro j hj hpositive
    have hjNot : j ∉ DA := by
      intro hjDA
      have hsubset : clusterVertices P j ⊆ clusterUnion P DA := by
        intro v hv
        exact (mem_clusterUnion P DA v).mpr
          ⟨j, hjDA, (mem_clusterVertices P j v).mp hv⟩
      have hzero : degreeInto Hfirst zA (clusterVertices P j) = 0 :=
        degreeInto_root_eq_zero H zA (clusterUnion P DA) (clusterVertices P j) hsubset
      have hle := degreeInto_le_of_le Hfirst Hsource hsecond zA (clusterVertices P j)
      exact (not_lt_of_ge (hle.trans_eq hzero)) hpositive
    have hupper := hAupper j (Finset.mem_sdiff.mpr ⟨hj, hjNot⟩)
    have hmono : (degreeInto Hsource zA (clusterVertices P j) : ℝ) ≤
        degreeInto H zA (clusterVertices P j) := by
      exact_mod_cast degreeInto_le_of_le H Hsource hsource zA (clusterVertices P j)
    exact hmono.trans hupper
  · intro j hj hpositive
    have hjNot : j ∉ DB := by
      intro hjDB
      have hsubset : clusterVertices P j ⊆ clusterUnion P DB := by
        intro v hv
        exact (mem_clusterUnion P DB v).mpr
          ⟨j, hjDB, (mem_clusterVertices P j v).mp hv⟩
      have hzero : degreeInto Hsource zB (clusterVertices P j) = 0 :=
        degreeInto_root_eq_zero Hfirst zB (clusterUnion P DB) (clusterVertices P j) hsubset
      exact (Nat.ne_of_gt hpositive) hzero
    have hupper := hBupper j (Finset.mem_sdiff.mpr ⟨hj, hjNot⟩)
    have hmono : (degreeInto Hsource zB (clusterVertices P j) : ℝ) ≤
        degreeInto H zB (clusterVertices P j) := by
      exact_mod_cast degreeInto_le_of_le H Hsource hsource zB (clusterVertices P j)
    exact hmono.trans hupper

end Erdos547b.ZhaoSourceRootRowsPreparation

#print axioms Erdos547b.ZhaoSourceRootRowsPreparation.exists_two_clean_roots
