/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos1166.Erdos1166HLOZHarnack
import ErdosProblems.Erdos1166.Erdos1166HLOZConditionalPairRuns

/-!
# Exact stopped first-exit expansion for HLOZ Appendix A

This file supplies the strong-Markov identity used between (A.16) and
(A.17).  An outer-path event is measurable at a random increment horizon.
The future walk first exits a finite annulus approximation at a prescribed
site and then realizes one of finitely many measurable profile-tail events.
The probability is exactly the outer mass times the first-exit kernel times
the corresponding profile-tail masses.

No Harnack estimate is assumed here.  The only ingredients are the whole-tail
IID restart theorem and the exact first-exit kernel.
-/

namespace Erdos1166.HLOZAppendixAExactExit

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
open KilledGreen

/-- Strong restart for an arbitrary measurable event of the whole future
increment sequence.  The zero-mass outer event is handled separately. -/
theorem measure_inter_incrementShiftAfter_eq_mul
    (τ : (ℕ → Direction) → ℕ) (A B : Set (ℕ → Direction))
    (hτ : Measurable τ)
    (hA : ∀ k, MeasurableSet[iidHistory (X := Direction) k]
      (A ∩ {ω | τ ω = k}))
    (hB : MeasurableSet B) :
    incrementLaw (A ∩ incrementShiftAfter τ ⁻¹' B) =
      incrementLaw A * incrementLaw B := by
  by_cases hA0 : incrementLaw A = 0
  · rw [hA0, zero_mul]
    exact measure_mono_null Set.inter_subset_left hA0
  · have hLaw := incrementShiftAfter_hasLaw_cond τ A hτ hA hA0
    have hAmeas := measurableSet_pastEvent τ A hA
    have hcond : incrementLaw[|A] (incrementShiftAfter τ ⁻¹' B) =
        incrementLaw B := by
      change incrementLaw[|A] {ω | incrementShiftAfter τ ω ∈ B} =
        incrementLaw B
      simpa only [Set.ofPred_mem_eq] using
        (hLaw.measure_eq (p := fun x ↦ x ∈ B) hB)
    rw [cond_apply hAmeas] at hcond
    have hAtop : incrementLaw A ≠ ∞ := measure_ne_top incrementLaw A
    calc
      incrementLaw (A ∩ incrementShiftAfter τ ⁻¹' B) =
          incrementLaw A * (incrementLaw A)⁻¹ *
            incrementLaw (A ∩ incrementShiftAfter τ ⁻¹' B) := by
        rw [ENNReal.mul_inv_cancel hA0 hAtop, one_mul]
      _ = incrementLaw A * incrementLaw B := by rw [mul_assoc, hcond]

/-- Exit from `D` at `y` after `n+1` steps, followed by a fresh tail event. -/
def firstExitThenEvent (D : Set Site) (x y : Site)
    (C : Set (ℕ → Direction)) : Set (ℕ → Direction) :=
  ⋃ n : ℕ, firstExitAtSuccEvent D x y n ∩
    incrementShiftAfter (fun _ ↦ n + 1) ⁻¹' C

lemma iidHistory_mono {k l : ℕ} (hkl : k ≤ l) :
    iidHistory (X := Direction) k ≤ iidHistory (X := Direction) l := by
  refine iSup_le fun i ↦ iSup_le fun hi ↦ ?_
  exact le_iSup_of_le i (le_iSup_of_le (lt_of_lt_of_le hi hkl) le_rfl)

lemma measurable_iidBlock_one_iidHistory_succ (n : ℕ) :
    Measurable[iidHistory (X := Direction) (n + 1)]
      (iidBlock (X := Direction) n 1) := by
  let _ : MeasurableSpace (ℕ → Direction) :=
    iidHistory (X := Direction) (n + 1)
  apply measurable_pi_lambda
  intro i
  apply measurable_iff_comap_le.mpr
  exact le_iSup_of_le (n + (i : ℕ))
    (le_iSup_of_le (by omega) le_rfl)

theorem measurableSet_firstExitAtSuccEvent_iidHistory_succ
    (D : Set Site) (x y : Site) (n : ℕ) (hy : y ∉ D) :
    MeasurableSet[iidHistory (X := Direction) (n + 1)]
      (firstExitAtSuccEvent D x y n) := by
  rw [← iUnion_killedThenExitDirectionEvent D x y n hy]
  apply MeasurableSet.iUnion
  intro d
  exact (iidHistory_mono (Nat.le_succ n) _
      (measurableSet_killedEndpointEvent_iidHistory D x
        (y - directionStep d) n)).inter
    ((measurable_iidBlock_one_iidHistory_succ n)
      (measurableSet_oneDirectionBlock d))

theorem measurableSet_firstExitThenEvent
    (D : Set Site) (x y : Site) (C : Set (ℕ → Direction))
    (hy : y ∉ D) (hC : MeasurableSet C) :
    MeasurableSet (firstExitThenEvent D x y C) := by
  apply MeasurableSet.iUnion
  intro n
  exact (measurableSet_firstExitAtSuccEvent D x y n hy).inter
    ((measurable_incrementShiftAfter measurable_const) hC)

/-- Exact first-exit-kernel factorization for one continuation event. -/
theorem measure_firstExitThenEvent
    (D : Set Site) (x y : Site) (C : Set (ℕ → Direction))
    (hy : y ∉ D) (hC : MeasurableSet C) :
    incrementLaw (firstExitThenEvent D x y C) =
      firstExitAtWeight D x y * incrementLaw C := by
  unfold firstExitThenEvent firstExitAtWeight
  rw [measure_iUnion]
  · have hatom (n : ℕ) :
        incrementLaw (firstExitAtSuccEvent D x y n ∩
          incrementShiftAfter (fun _ : ℕ → Direction ↦ n + 1) ⁻¹' C) =
          incrementLaw (firstExitAtSuccEvent D x y n) * incrementLaw C := by
        apply measure_inter_incrementShiftAfter_eq_mul
          (fun _ : ℕ → Direction ↦ n + 1)
          (firstExitAtSuccEvent D x y n) C measurable_const
        · intro k
          by_cases hk : k = n + 1
          · subst k
            convert measurableSet_firstExitAtSuccEvent_iidHistory_succ
              D x y n hy using 1
            ext ω
            simp
          · have heq : firstExitAtSuccEvent D x y n ∩
                {ω : ℕ → Direction | (fun _ ↦ n + 1) ω = k} = ∅ := by
              ext ω
              simp only [Set.mem_inter_iff, Set.mem_ofPred_eq,
                Set.mem_empty_iff_false, iff_false]
              intro h
              exact hk h.2.symm
            rw [heq]
            exact @MeasurableSet.empty _
              (iidHistory (X := Direction) k)
        · exact hC
    simp_rw [hatom]
    exact ENNReal.tsum_mul_right
  · exact fun n m hnm ↦
      (pairwiseDisjoint_firstExitAtSuccEvent D x y hnm).mono
        Set.inter_subset_left Set.inter_subset_left
  · intro n
    exact (measurableSet_firstExitAtSuccEvent D x y n hy).inter
      ((measurable_incrementShiftAfter measurable_const) hC)

theorem firstExitThenEvent_subset_firstExitAtEvent
    (D : Set Site) (x y : Site) (C : Set (ℕ → Direction)) :
    firstExitThenEvent D x y C ⊆ firstExitAtEvent D x y := by
  rintro ω hω
  rcases Set.mem_iUnion.mp hω with ⟨n, hn⟩
  exact Set.mem_iUnion.mpr ⟨n, hn.1⟩

theorem disjoint_firstExitAtEvent_of_ne
    (D : Set Site) (x : Site) {y z : Site} (hyz : y ≠ z) :
    Disjoint (firstExitAtEvent D x y) (firstExitAtEvent D x z) := by
  rw [Set.disjoint_left]
  intro ω hy hz
  rcases Set.mem_iUnion.mp hy with ⟨n, hn⟩
  rcases Set.mem_iUnion.mp hz with ⟨m, hm⟩
  by_cases hnm : n = m
  · subst m
    exact hyz (hn.2.1.symm.trans hm.2.1)
  · rcases lt_or_gt_of_ne hnm with hlt | hgt
    · have hmem : walkFrom x ω (n + 1) ∈ D := hm.1 (n + 1) (by omega)
      exact hn.2.2 (hn.2.1 ▸ hmem)
    · have hmem : walkFrom x ω (m + 1) ∈ D := hn.1 (m + 1) (by omega)
      exact hm.2.2 (hm.2.1 ▸ hmem)

theorem disjoint_firstExitThenEvent_of_exit_ne
    (D : Set Site) (x : Site) {y z : Site}
    (C E : Set (ℕ → Direction)) (hyz : y ≠ z) :
    Disjoint (firstExitThenEvent D x y C) (firstExitThenEvent D x z E) :=
  (disjoint_firstExitAtEvent_of_ne D x hyz).mono
    (firstExitThenEvent_subset_firstExitAtEvent D x y C)
    (firstExitThenEvent_subset_firstExitAtEvent D x z E)

theorem disjoint_firstExitThenEvent_of_tail_disjoint
    (D : Set Site) (x y : Site) {C E : Set (ℕ → Direction)}
    (hCE : Disjoint C E) :
    Disjoint (firstExitThenEvent D x y C) (firstExitThenEvent D x y E) := by
  rw [Set.disjoint_left]
  intro ω hC hE
  rcases Set.mem_iUnion.mp hC with ⟨n, hn⟩
  rcases Set.mem_iUnion.mp hE with ⟨m, hm⟩
  by_cases hnm : n = m
  · subst m
    exact Set.disjoint_left.mp hCE hn.2 hm.2
  · exact Set.disjoint_left.mp
      (pairwiseDisjoint_firstExitAtSuccEvent D x y hnm) hn.1 hm.1

/-- The annular event on a fresh increment sequence: first exit at one of
the allowed sites, followed by the profile-specific continuation event. -/
def annularExitProfileTail {β : Type*}
    (D : Set Site) (start : Site) (exitSites : Finset Site)
    (Q : Finset β) (profileTail : Site → β → Set (ℕ → Direction)) :
    Set (ℕ → Direction) :=
  ⋃ p ∈ exitSites.product Q,
    firstExitThenEvent D start p.1 (profileTail p.1 p.2)

theorem pairwiseDisjoint_annularExitProfileTail
    {β : Type*} (D : Set Site) (start : Site) (exitSites : Finset Site)
    (Q : Finset β) (profileTail : Site → β → Set (ℕ → Direction))
    (hprofileDisjoint : ∀ z ∈ exitSites,
      Set.PairwiseDisjoint (↑Q : Set β) (profileTail z)) :
    Set.PairwiseDisjoint (↑(exitSites.product Q) : Set (Site × β))
      (fun p ↦ firstExitThenEvent D start p.1 (profileTail p.1 p.2)) := by
  intro p hp p' hp' hne
  rcases Finset.mem_product.mp hp with ⟨hpz, hpq⟩
  rcases Finset.mem_product.mp hp' with ⟨hpz', hpq'⟩
  by_cases hz : p.1 = p'.1
  · have hq : p.2 ≠ p'.2 := by
      intro heq
      apply hne
      exact Prod.ext hz heq
    change Disjoint
      (firstExitThenEvent D start p.1 (profileTail p.1 p.2))
      (firstExitThenEvent D start p'.1 (profileTail p'.1 p'.2))
    rw [hz]
    exact disjoint_firstExitThenEvent_of_tail_disjoint D start p'.1
      (hprofileDisjoint p'.1 hpz' hpq hpq' hq)
  · exact disjoint_firstExitThenEvent_of_exit_ne D start
      (profileTail p.1 p.2) (profileTail p'.1 p'.2) hz

theorem measurableSet_annularExitProfileTail
    {β : Type*} (D : Set Site) (start : Site) (exitSites : Finset Site)
    (Q : Finset β) (profileTail : Site → β → Set (ℕ → Direction))
    (hexit : ∀ z ∈ exitSites, z ∉ D)
    (hprofileMeasurable : ∀ z ∈ exitSites, ∀ q ∈ Q,
      MeasurableSet (profileTail z q)) :
    MeasurableSet (annularExitProfileTail D start exitSites Q profileTail) := by
  unfold annularExitProfileTail
  apply Finset.measurableSet_biUnion
  intro p hp
  rcases Finset.mem_product.mp hp with ⟨hpz, hpq⟩
  exact measurableSet_firstExitThenEvent D start p.1 (profileTail p.1 p.2)
    (hexit p.1 hpz) (hprofileMeasurable p.1 hpz p.2 hpq)

/-- Exact finite first-exit/profile expansion on a fresh walk. -/
theorem measure_annularExitProfileTail
    {β : Type*} (D : Set Site) (start : Site) (exitSites : Finset Site)
    (Q : Finset β) (profileTail : Site → β → Set (ℕ → Direction))
    (hexit : ∀ z ∈ exitSites, z ∉ D)
    (hprofileMeasurable : ∀ z ∈ exitSites, ∀ q ∈ Q,
      MeasurableSet (profileTail z q))
    (hprofileDisjoint : ∀ z ∈ exitSites,
      Set.PairwiseDisjoint (↑Q : Set β) (profileTail z)) :
    incrementLaw (annularExitProfileTail D start exitSites Q profileTail) =
      ∑ z ∈ exitSites, firstExitAtWeight D start z *
        ∑ q ∈ Q, incrementLaw (profileTail z q) := by
  unfold annularExitProfileTail
  rw [measure_biUnion_finset
    (pairwiseDisjoint_annularExitProfileTail D start exitSites Q profileTail
      hprofileDisjoint)]
  · calc
      (∑ p ∈ exitSites.product Q,
          incrementLaw (firstExitThenEvent D start p.1
            (profileTail p.1 p.2))) =
          ∑ z ∈ exitSites, ∑ q ∈ Q,
            incrementLaw (firstExitThenEvent D start z
              (profileTail z q)) := by
        exact Finset.sum_product' exitSites Q
          (fun z q ↦ incrementLaw
            (firstExitThenEvent D start z (profileTail z q)))
      _ = ∑ z ∈ exitSites, firstExitAtWeight D start z *
          ∑ q ∈ Q, incrementLaw (profileTail z q) := by
        apply Finset.sum_congr rfl
        intro z hz
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q hq
        exact measure_firstExitThenEvent D start z (profileTail z q)
          (hexit z hz) (hprofileMeasurable z hz q hq)
  · intro p hp
    rcases Finset.mem_product.mp hp with ⟨hpz, hpq⟩
    exact measurableSet_firstExitThenEvent D start p.1 (profileTail p.1 p.2)
      (hexit p.1 hpz) (hprofileMeasurable p.1 hpz p.2 hpq)

/-- One profile atom after a random outer-path horizon. -/
def stoppedAnnularProfileAtom {β : Type*}
    (τ : (ℕ → Direction) → ℕ) (D : Set Site) (start : Site)
    (exitSites : Finset Site) (profileTail : Site → β → Set (ℕ → Direction))
    (q : β) : Set (ℕ → Direction) :=
  incrementShiftAfter τ ⁻¹'
    (⋃ z ∈ exitSites, firstExitThenEvent D start z (profileTail z q))

theorem stoppedAnnularProfileUnion_inter
    {β : Type*} (τ : (ℕ → Direction) → ℕ) (A : Set (ℕ → Direction))
    (D : Set Site) (start : Site) (exitSites : Finset Site)
    (Q : Finset β) (profileTail : Site → β → Set (ℕ → Direction)) :
    (⋃ q ∈ Q, stoppedAnnularProfileAtom τ D start exitSites profileTail q) ∩ A =
      A ∩ incrementShiftAfter τ ⁻¹'
        annularExitProfileTail D start exitSites Q profileTail := by
  ext ω
  simp only [stoppedAnnularProfileAtom, annularExitProfileTail,
    Set.mem_inter_iff, Set.mem_iUnion, Set.mem_preimage]
  constructor
  · rintro ⟨⟨q, hq, z, hz, htail⟩, hA⟩
    exact ⟨hA, ⟨(z, q), Finset.mem_product.mpr ⟨hz, hq⟩, htail⟩⟩
  · rintro ⟨hA, ⟨p, hp, htail⟩⟩
    rcases Finset.mem_product.mp hp with ⟨hz, hq⟩
    exact ⟨⟨p.2, hq, p.1, hz, htail⟩, hA⟩

/-- Exact strong-Markov expansion of the literal stopped annular event. -/
theorem measure_stoppedAnnularProfileUnion
    {β : Type*} (τ : (ℕ → Direction) → ℕ) (A : Set (ℕ → Direction))
    (D : Set Site) (start : Site) (exitSites : Finset Site)
    (Q : Finset β) (profileTail : Site → β → Set (ℕ → Direction))
    (hτ : Measurable τ)
    (hA : ∀ k, MeasurableSet[iidHistory (X := Direction) k]
      (A ∩ {ω | τ ω = k}))
    (hexit : ∀ z ∈ exitSites, z ∉ D)
    (hprofileMeasurable : ∀ z ∈ exitSites, ∀ q ∈ Q,
      MeasurableSet (profileTail z q))
    (hprofileDisjoint : ∀ z ∈ exitSites,
      Set.PairwiseDisjoint (↑Q : Set β) (profileTail z)) :
    incrementLaw
        ((⋃ q ∈ Q,
          stoppedAnnularProfileAtom τ D start exitSites profileTail q) ∩ A) =
      incrementLaw A *
        ∑ z ∈ exitSites, firstExitAtWeight D start z *
          ∑ q ∈ Q, incrementLaw (profileTail z q) := by
  rw [stoppedAnnularProfileUnion_inter]
  rw [measure_inter_incrementShiftAfter_eq_mul τ A
    (annularExitProfileTail D start exitSites Q profileTail) hτ hA]
  · rw [measure_annularExitProfileTail D start exitSites Q profileTail
      hexit hprofileMeasurable hprofileDisjoint]
  · exact measurableSet_annularExitProfileTail D start exitSites Q profileTail
      hexit hprofileMeasurable

end Erdos1166.HLOZAppendixAExactExit
