import ErdosProblems.Erdos587.HooleyPrimeRecursion

/-!
# Restricted moment sets and their exceptional mass

The lower-moment constraints are nested and preserved under squarefree
divisibility. The loss of harmonic mass on imposing one more constraint
is bounded by the corresponding restricted moment sum.
-/

open scoped BigOperators

namespace Erdos587

def MeetsDeltaMoments (E : ℕ → ℝ) (q n : ℕ) : Prop :=
  ∀ j : ℕ, 1 ≤ j → j ≤ q → deltaMoment n j / n.divisors.card ≤ E j

@[simp] lemma meetsDeltaMoments_zero (E : ℕ → ℝ) (n : ℕ) :
    MeetsDeltaMoments E 0 n := by
  intro j hj hj0
  omega

lemma meetsDeltaMoments_succ (E : ℕ → ℝ) (q n : ℕ) :
    MeetsDeltaMoments E (q + 1) n ↔
      MeetsDeltaMoments E q n ∧ deltaMoment n (q + 1) / n.divisors.card ≤ E (q + 1) := by
  constructor
  · intro h
    exact ⟨fun j hj hjq => h j hj (hjq.trans (Nat.le_succ q)), h (q + 1) (by omega) le_rfl⟩
  · rintro ⟨h, hlast⟩ j hj hjq
    by_cases hjq' : j ≤ q
    · exact h j hj hjq'
    · have heq : j = q + 1 := by omega
      simpa only [heq] using hlast

lemma MeetsDeltaMoments.mono_order {E : ℕ → ℝ} {q r n : ℕ}
    (h : MeetsDeltaMoments E q n) (hrq : r ≤ q) : MeetsDeltaMoments E r n :=
  fun j hj hjr => h j hj (hjr.trans hrq)

lemma MeetsDeltaMoments.of_dvd {E : ℕ → ℝ} {q m n : ℕ}
    (h : MeetsDeltaMoments E q n) (hn : Squarefree n) (hmn : m ∣ n) :
    MeetsDeltaMoments E q m := by
  intro j hj hjq
  exact (normalized_deltaMoment_le_of_dvd hn hmn (by omega)).trans (h j hj hjq)

noncomputable def deltaRestrictedSet (S : Finset ℕ) (E : ℕ → ℝ) (q : ℕ) : Finset ℕ := by
  classical
  exact S.filter (MeetsDeltaMoments E q)

@[simp] lemma mem_deltaRestrictedSet {S : Finset ℕ} {E : ℕ → ℝ} {q n : ℕ} :
    n ∈ deltaRestrictedSet S E q ↔ n ∈ S ∧ MeetsDeltaMoments E q n := by
  classical
  exact Finset.mem_filter

@[simp] lemma deltaRestrictedSet_zero (S : Finset ℕ) (E : ℕ → ℝ) :
    deltaRestrictedSet S E 0 = S := by
  classical
  simp [deltaRestrictedSet]

lemma deltaRestrictedSet_subset (S : Finset ℕ) (E : ℕ → ℝ) (q : ℕ) :
    deltaRestrictedSet S E q ⊆ S := by
  intro n hn
  exact (mem_deltaRestrictedSet.mp hn).1

lemma deltaRestrictedSet_antitone (S : Finset ℕ) (E : ℕ → ℝ) :
    Antitone (deltaRestrictedSet S E) := by
  intro q r hqr n hn
  obtain ⟨hnS, hn⟩ := mem_deltaRestrictedSet.mp hn
  exact mem_deltaRestrictedSet.mpr ⟨hnS, hn.mono_order hqr⟩

lemma deltaRestrictedSet_succ (S : Finset ℕ) (E : ℕ → ℝ) (q : ℕ) :
    deltaRestrictedSet S E (q + 1) = (deltaRestrictedSet S E q).filter
      (fun n => deltaMoment n (q + 1) / n.divisors.card ≤ E (q + 1)) := by
  classical
  ext n
  simp only [mem_deltaRestrictedSet, meetsDeltaMoments_succ, Finset.mem_filter, and_assoc]

lemma deltaRestrictedSet_one_eq (S : Finset ℕ) (E : ℕ → ℝ) (hE : 1 ≤ E 1) :
    deltaRestrictedSet S E 1 = S := by
  classical
  apply Finset.Subset.antisymm (deltaRestrictedSet_subset S E 1)
  intro n hn
  apply mem_deltaRestrictedSet.mpr
  refine ⟨hn, ?_⟩
  intro j hj hj1
  have hj' : j = 1 := by omega
  subst j
  rw [deltaMoment_one]
  by_cases hc : (n.divisors.card : ℝ) = 0
  · simp only [hc, zero_div]
    linarith
  · rw [div_self hc]
    exact hE

/-- Markov's inequality for the harmonic mass discarded at the next
moment order. The right side is exactly the restricted moment average. -/
theorem deltaRestrictedSet_step_mass_le (S : Finset ℕ) (E : ℕ → ℝ) (q : ℕ)
    (hE : 0 < E (q + 1)) :
    (∑ n ∈ deltaRestrictedSet S E q \ deltaRestrictedSet S E (q + 1), (1 : ℝ) / n) ≤
      (∑ n ∈ deltaRestrictedSet S E q,
        (deltaMoment n (q + 1) / n.divisors.card) / n) / E (q + 1) := by
  classical
  apply (le_div_iff₀ hE).mpr
  rw [Finset.sum_mul]
  calc
    _ ≤ ∑ n ∈ deltaRestrictedSet S E q \ deltaRestrictedSet S E (q + 1),
        (deltaMoment n (q + 1) / n.divisors.card) / n := by
      apply Finset.sum_le_sum
      intro n hn
      obtain ⟨hnq, hnnext⟩ := Finset.mem_sdiff.mp hn
      have hfail : ¬ deltaMoment n (q + 1) / n.divisors.card ≤ E (q + 1) := by
        intro h
        apply hnnext
        rw [deltaRestrictedSet_succ]
        exact Finset.mem_filter.mpr ⟨hnq, h⟩
      have hle := div_le_div_of_nonneg_right (le_of_lt (lt_of_not_ge hfail))
        (show (0 : ℝ) ≤ n by positivity)
      simpa only [one_div, div_eq_mul_inv, mul_comm, mul_one] using hle
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
      (fun n _ _ => div_nonneg (div_nonneg (deltaMoment_nonneg n _) (by positivity))
        (by positivity))

/-- Sum the one-step losses starting at order two; the first moment
constraint costs no exceptional mass. -/
theorem deltaRestrictedSet_mass_le (S : Finset ℕ) (E : ℕ → ℝ) (q : ℕ)
    (hEone : 1 ≤ E 1) (hE : ∀ j ∈ Finset.Icc 2 (q + 1), 0 < E j) :
    (∑ n ∈ S \ deltaRestrictedSet S E (q + 1), (1 : ℝ) / n) ≤
      ∑ j ∈ Finset.Icc 2 (q + 1),
        (∑ n ∈ deltaRestrictedSet S E (j - 1), (deltaMoment n j / n.divisors.card) / n) /
          E j := by
  classical
  induction q with
  | zero => simp [deltaRestrictedSet_one_eq S E hEone]
  | succ q ih =>
    have hEold : ∀ j ∈ Finset.Icc 2 (q + 1), 0 < E j := by
      intro j hj
      apply hE j
      have hj' := Finset.mem_Icc.mp hj
      apply Finset.mem_Icc.mpr
      omega
    have hold := ih hEold
    have hlast : 0 < E (q + 1 + 1) := hE _ (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩)
    have hstep := deltaRestrictedSet_step_mass_le S E (q + 1) hlast
    have hsplit :
        (∑ n ∈ S \ deltaRestrictedSet S E (q + 1 + 1), (1 : ℝ) / n) =
          (∑ n ∈ S \ deltaRestrictedSet S E (q + 1), (1 : ℝ) / n) +
            ∑ n ∈ deltaRestrictedSet S E (q + 1) \ deltaRestrictedSet S E (q + 1 + 1),
              (1 : ℝ) / n := by
      rw [Finset.sum_sdiff_eq_sub (deltaRestrictedSet_subset S E _),
        Finset.sum_sdiff_eq_sub (deltaRestrictedSet_subset S E _),
        Finset.sum_sdiff_eq_sub (deltaRestrictedSet_antitone S E (Nat.le_succ (q + 1)))]
      ring
    rw [hsplit, Finset.sum_Icc_succ_top (show 2 ≤ q + 1 + 1 by omega)]
    simpa only [Nat.add_sub_cancel] using add_le_add hold hstep

end Erdos587
