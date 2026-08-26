/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceSwitchUnion
import ErdosProblems.Erdos547b.SourceMatchingCopySupport

/-! # The actual freed clusters and their compatible dense root pairs -/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoSourceFreedClusterGeometry

open Finset SimpleGraph Erdos547b.ZhaoStability Erdos547b.ZhaoDegreeForm
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceParameterSchedule
open Erdos547b.ZhaoSourceNearFullMatching Erdos547b.ZhaoSourceClaim617Switch
open Erdos547b.ZhaoSourceSwitchUnion Erdos547b.ZhaoMatchingSupportSeparation
open Erdos547b.ZhaoEvenReducedPadding Erdos547b.ZhaoLemma611Full
open Erdos547b.ZhaoSourceEmbeddingHost Erdos547b.ZhaoSourceMatchingCopySupport
open Erdos547b.ZhaoSourceParentCleanup Erdos547b.ZhaoSection6Dichotomy

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W) (S : CleanSourceWitness W Q)
variable {fb : ℝ} (O : Output W Q S fb) (sw : Switch W Q S O)

abbrev FreedIndex := {e // e ∈ sw.edges}

theorem partner_real_large (e : FreedIndex W Q S O sw) :
    ∃ C : Index W, sw.partner e = Sum.inl C ∧ C ∈ large W := by
  have h := (switched_properties W Q S O sw).2.2.2.1
    (Finset.mem_image.mpr ⟨e, Finset.mem_univ _, rfl⟩)
  cases heq : sw.partner e with
  | inl C => exact ⟨C, rfl, mem_padFinset_inl.mp (heq ▸ h)⟩
  | inr d => exact (not_mem_padFinset_inr d (heq ▸ h)).elim

def freedCluster (e : FreedIndex W Q S O sw) : Index W :=
  Classical.choose (partner_real_large W Q S O sw e)

theorem partner_eq (e : FreedIndex W Q S O sw) :
    sw.partner e = Sum.inl (freedCluster W Q S O sw e) :=
  (Classical.choose_spec (partner_real_large W Q S O sw e)).1

theorem freedCluster_large (e : FreedIndex W Q S O sw) :
    freedCluster W Q S O sw e ∈ large W :=
  (Classical.choose_spec (partner_real_large W Q S O sw e)).2

theorem freedCluster_injective : Function.Injective (freedCluster W Q S O sw) := by
  intro e f hef
  apply sw.partner_injective O.D.Min_isMatching
  rw [partner_eq, partner_eq, hef]

theorem freedIndex_card : Fintype.card (FreedIndex W Q S O sw) =
    ZhaoClaim617SwitchNumerics.switchCount (rho α : ℝ) (paddedHalf (Index W)) := by
  rw [Fintype.card_coe, sw.card_edges]

def whole (e : FreedIndex W Q S O sw) : Finset (Fin hostN) :=
  clusterVertices (assignment W) (freedCluster W Q S O sw e)

theorem whole_eq_pad (e : FreedIndex W Q S O sw) : whole W Q S O sw e =
    padCluster (clusterVertices (assignment W)) (sw.partner e) := by
  rw [partner_eq]
  rfl

theorem whole_card (e : FreedIndex W Q S O sw) :
    (whole W Q S O sw e).card = W.clusterSize := by
  unfold whole
  rw [clusterVertices_partitionAssignment]
  exact W.equal_clusters _ (freedCluster W Q S O sw e).property

theorem whole_disjoint (e f : FreedIndex W Q S O sw) (hef : e ≠ f) :
    Disjoint (whole W Q S O sw e) (whole W Q S O sw f) :=
  clusterVertices_disjoint (assignment W) (fun h => hef (freedCluster_injective W Q S O sw h))

theorem partner_away (e : FreedIndex W Q S O sw) :
    sw.partner e ≠ Sum.inl Q.A ∧ sw.partner e ≠ Sum.inl Q.B := by
  have hn : sw.partner e ∉ excluded W Q S O :=
    Finset.disjoint_left.mp (min_disjoint_excluded W Q S O) (sw.partner_mem_support e)
  constructor
  · intro h
    exact hn (Finset.mem_union_right _ (Finset.mem_insert.mpr (Or.inl h)))
  · intro h
    exact hn (Finset.mem_union_right _ (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr h))))

theorem partner_source_lower (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (e : FreedIndex W Q S O sw) :
    1 - 2 * (eta α : ℝ) < rootDensity W S (Sum.inl Q.A) (sw.partner e) := by
  obtain ⟨a, ha, c, hc⟩ := (mem_selectedSupport_iff Q.claim67.M (padFinset (large W))
    O.D.minEdges (sw.partner e)).mp (sw.partner_mem_support e)
  rw [← hc]
  have h := O.min_density W Q S hα hα1 ha
  fin_cases c
  · exact h.1
  · exact h.2

theorem root_pair (hα : 0 < α) (hα1 : α ≤ 1 / 4) (e : FreedIndex W Q S O sw) :
    (embeddingHost W).IsUniform (epsilon α : ℝ)
      (clusterVertices (assignment W) Q.A) (whole W Q S O sw e) ∧
      1 - 2 * (eta α : ℝ) - (epsilon α : ℝ) <
        ((embeddingHost W).edgeDensity (clusterVertices (assignment W) Q.A) (whole W Q S O sw e) : ℝ) := by
  have hl := partner_source_lower W Q S O sw hα hα1 e
  have hη : (eta α : ℝ) ≤ 1 / 1000000 := by
    obtain ⟨hr11, hrr1, her, _⟩ := parameter_upper_bounds hα hα1
    have hQ : eta α ≤ 1 / 1000000 := by linarith only [hr11, hrr1, her]
    have hR := (Rat.cast_le (K := ℝ)).mpr hQ
    norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at hR
    exact hR
  have hpos : 0 < rootDensity W S (Sum.inl Q.A) (sw.partner e) := by linarith only [hl, hη]
  have h := source_pair_A W S (partner_away W Q S O sw e).1 (partner_away W Q S O sw e).2 hpos
  rw [← whole_eq_pad] at h
  exact ⟨h.1, by linarith only [hl, h.2.2]⟩

theorem whole_disjoint_hostSupport (e : FreedIndex W Q S O sw) :
    Disjoint (whole W Q S O sw e) (hostSupport W Q (fullMatching W Q S O sw)) := by
  have hmem : sw.partner e ∈ sw.partnerSet := Finset.mem_image.mpr ⟨e, Finset.mem_univ _, rfl⟩
  have hroot (s : Fin 2) : Disjoint (whole W Q S O sw e) (reservoir W Q s) := by
    apply (clusterVertices_disjoint (assignment W) (show freedCluster W Q S O sw e ≠ rootCluster W Q s from ?_)).mono_right
      (reservoir_subset W Q s)
    intro heq
    have heq' := (partner_eq W Q S O sw e).trans (congrArg Sum.inl heq)
    fin_cases s
    · exact (partner_away W Q S O sw e).1 heq'
    · exact (partner_away W Q S O sw e).2 heq'
  rw [hostSupport, Finset.disjoint_union_right, Finset.disjoint_union_right]
  refine ⟨⟨hroot 0, hroot 1⟩, ?_⟩
  apply Finset.disjoint_left.mpr
  intro z hz hsupport
  obtain ⟨x, hx, hzx⟩ := Finset.mem_biUnion.mp hsupport
  have hne : sw.partner e ≠ x := by
    intro heq
    exact Finset.disjoint_left.mp (partners_disjoint_fullMatching W Q S O sw) hmem (heq ▸ hx)
  have hdis := clusterVertices_disjoint (padAssignment (assignment W)) hne
  simp only [clusterVertices_padAssignment] at hdis
  exact Finset.disjoint_left.mp hdis ((whole_eq_pad W Q S O sw e) ▸ hz) hzx

end Erdos547b.ZhaoSourceFreedClusterGeometry

#print axioms Erdos547b.ZhaoSourceFreedClusterGeometry.freedCluster_injective
#print axioms Erdos547b.ZhaoSourceFreedClusterGeometry.root_pair
#print axioms Erdos547b.ZhaoSourceFreedClusterGeometry.whole_disjoint_hostSupport
