/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim617SwitchedMatching
import ErdosProblems.Erdos547b.Claim617SwitchNumerics
import ErdosProblems.Erdos547b.MatchingSupportSeparation
import ErdosProblems.Erdos547b.SourceCrossingClusters

/-!
# The actual Claim-6.17 switch from a dense source crossing

The targets avoid the reserved matching and both distinguished clusters.
The new matching is kept separate from the original Claim-6.7 certificate.
-/

open scoped SimpleGraph Classical
noncomputable section

namespace Erdos547b.ZhaoSourceClaim617Switch

open Finset SimpleGraph Erdos547b.ZhaoStability
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceParameterSchedule
open Erdos547b.ZhaoSourceDegreeFormBounds Erdos547b.ZhaoSourceNearFullMatching
open Erdos547b.ZhaoSourceNearFullFromHost Erdos547b.ZhaoSourceCrossingClusters
open Erdos547b.ZhaoClaim617DistinctSwitch Erdos547b.ZhaoClaim617SwitchNumerics
open Erdos547b.ZhaoMatchingSupportSeparation Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma611Full Erdos547b.ZhaoRichClaim61Lemma611

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W) (S : CleanSourceWitness W Q)
variable {fb : ℝ} (O : Output W Q S fb)

def excluded : Finset (EvenPadding (Index W)) :=
  matchingSupport O.D.Mb ∪ {Sum.inl Q.A, Sum.inl Q.B}

def targets : Finset (EvenPadding (Index W)) := O.D.V2 \ excluded W Q S O

abbrev Switch := DistinctSwitch O.D.Min (padFinset (large W)) O.D.S1
  (targets W Q S O) (switchCount (rho α : ℝ) (paddedHalf (Index W)))

include Q S O in
theorem scale_lower (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hhost : hostN = 2 * q)
    (horder : orderThreshold α M ≤ q) :
    10 ≤ (rho α : ℝ) * paddedHalf (Index W) := by
  have hb := scale_bounds W Q S O hα hα1 hhost horder
  have hpos : (1 : ℝ) ≤ crossingScale W := by
    have hnat : 1 ≤ crossingScale W := hb.1
    exact_mod_cast hnat
  linarith only [hpos, hb.2.2.1]

theorem excluded_card_bound (hα : 0 < α) :
    ((excluded W Q S O).card : ℝ) ≤
      4 * (fourthRoot α : ℝ) * paddedHalf (Index W) + 2 := by
  have hcard : (excluded W Q S O).card ≤ (matchingSupport O.D.Mb).card + 2 := by
    have hp : #({Sum.inl Q.A, Sum.inl Q.B} : Finset (EvenPadding (Index W))) ≤ 2 := by
      simpa only [Finset.card_singleton] using Finset.card_insert_le
        (Sum.inl Q.A : EvenPadding (Index W)) {Sum.inl Q.B}
    exact (Finset.card_union_le _ _).trans (Nat.add_le_add_left hp _)
  have hR : ((excluded W Q S O).card : ℝ) ≤ (matchingSupport O.D.Mb).card + 2 := by
    exact_mod_cast hcard
  linarith only [hR, reserved_support_bound W Q S O hα]

theorem targets_disjoint_original : Disjoint (targets W Q S O) (matchingSupport O.D.Min) := by
  rw [Finset.disjoint_left]
  intro x hx hy
  exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hx).1).2 hy

theorem min_disjoint_excluded : Disjoint (matchingSupport O.D.Min) (excluded W Q S O) := by
  rw [excluded, Finset.disjoint_union_right]
  constructor
  · apply selectedSupport_disjoint Q.claim67.M Q.claim67.isMatching (padFinset (large W))
    rw [Finset.disjoint_left]
    intro e he hmb
    exact (Finset.mem_sdiff.mp (O.D.mb_subset hmb)).2 he
  · rw [Finset.disjoint_left]
    intro x hx hy
    obtain ⟨e, he, c, hc⟩ := (mem_selectedSupport_iff Q.claim67.M (padFinset (large W)) O.D.minEdges x).mp hx
    have hn := endpoint_ne_distinguished_of_mem_away Q.claim67.M (padFinset (large W))
      (Sum.inl Q.A) (Sum.inl Q.B) (O.min_subset_away W Q S he) c
    rcases Finset.mem_insert.mp hy with h | h
    · exact hn.1 (hc.trans h)
    · exact hn.2 (hc.trans (Finset.mem_singleton.mp h))

theorem exists_switch
    (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hhost : hostN = 2 * q)
    (horder : orderThreshold α M ≤ q)
    (hdense : 16 * (rho α : ℝ) * (paddedHalf (Index W) : ℝ) ^ 2 ≤
      ((padGraph (reduced W)).interedges O.D.S1 O.D.V2).card) :
    Nonempty (Switch W Q S O) := by
  have hr : (0 : ℝ) < rho α := by exact_mod_cast (parameter_pos hα).2.1
  have he : (0 : ℝ) ≤ eta α := by exact_mod_cast (parameter_pos hα).2.2.1.le
  have ht : (0 : ℝ) ≤ fourthRoot α := by exact_mod_cast (parameter_pos hα).2.2.2.1.le
  have hm : 80 * (rho α : ℝ) * (eta α : ℝ) + 4 * (fourthRoot α : ℝ) ≤ (rho α : ℝ) / 2 := by
    have h := (Rat.cast_le (K := ℝ)).mpr (parameter_margin hα hα1)
    norm_num only [Rat.cast_add, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_div] at h
    exact h
  exact exists_distinctSwitch_of_dense O.D.Min O.D.Min_isMatching (padFinset (large W))
    O.D.S1 O.D.V2 (excluded W Q S O) (rho α : ℝ) (eta α : ℝ) (fourthRoot α : ℝ)
    (paddedHalf (Index W)) hr he ht (scale_lower W Q S O hα hα1 hhost horder)
    (sourceS1_subset_support _ _) ((Finset.card_le_card (sourceS1_subset_support _ _)).trans O.D.V1_card_upper)
    (support_bounds W Q S O).2.2.2 (excluded_card_bound W Q S O hα) hm hdense

theorem switched_properties (D : Switch W Q S O) :
    D.switched.IsMatching ∧
      Disjoint (matchingSupport D.switched) (excluded W Q S O) ∧
      Disjoint D.partnerSet (matchingSupport D.switched) ∧
      D.partnerSet ⊆ padFinset (large W) ∧
      D.partnerSet.card = switchCount (rho α : ℝ) (paddedHalf (Index W)) := by
  have hM := O.D.Min_isMatching
  have ht := targets_disjoint_original W Q S O
  have htarget : Disjoint (targets W Q S O) (excluded W Q S O) := Finset.sdiff_disjoint
  exact ⟨D.switched_isMatching hM ht,
    D.switched_disjoint_of_disjoint _ (min_disjoint_excluded W Q S O) htarget,
    D.partnerSet_disjoint_switched hM ht, D.partnerSet_subset_large hM (Finset.Subset.refl _),
    D.partnerSet_card hM⟩

end Erdos547b.ZhaoSourceClaim617Switch

#print axioms Erdos547b.ZhaoSourceClaim617Switch.exists_switch
#print axioms Erdos547b.ZhaoSourceClaim617Switch.switched_properties
