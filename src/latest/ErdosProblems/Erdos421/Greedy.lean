import ErdosProblems.Erdos421.Blocks

/-!
# Chojecki's gap-greedy construction

This file proves the finite-stage invariant and its passage to the infinite
union. It does not assert density one.
-/

namespace Erdos421

/-- The prime with zero-based index `k`. -/
noncomputable def prime (k : ℕ) : ℕ := Nat.nth Nat.Prime k

theorem prime_prime (k : ℕ) : (prime k).Prime :=
  Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime k

theorem prime_strictMono : StrictMono prime :=
  Nat.nth_strictMono Nat.infinite_setOfPred_prime

@[simp] theorem prime_zero : prime 0 = 2 := Nat.nth_prime_zero_eq_two

theorem prime_succ_le_two_mul (k : ℕ) : prime (k + 1) ≤ 2 * prime k := by
  obtain ⟨q, hq, hpq, hq2⟩ := Nat.exists_prime_lt_and_le_two_mul (prime k) (prime_prime k).ne_zero
  have heq : prime (Nat.count Nat.Prime q) = q := Nat.nth_count hq
  have hk : k < Nat.count Nat.Prime q := by
    apply prime_strictMono.lt_iff_lt.mp
    rwa [heq]
  have hle : prime (k + 1) ≤ prime (Nat.count Nat.Prime q) := prime_strictMono.monotone hk
  rw [heq] at hle
  exact hle.trans hq2

/-- Accept the whole gap exactly when its addition preserves distinct products. -/
noncomputable def gapStep (A : Finset ℕ) (p q : ℕ) : Finset ℕ := by
  classical
  exact if CollisionFree (A ∪ Finset.Ioc p q) then A ∪ Finset.Ioc p q else insert q A

theorem subset_gapStep (A : Finset ℕ) (p q : ℕ) : A ⊆ gapStep A p q := by
  classical
  unfold gapStep
  split_ifs
  · exact Finset.subset_union_left
  · exact Finset.subset_insert q A

theorem right_mem_gapStep (A : Finset ℕ) {p q : ℕ} (hpq : p < q) :
    q ∈ gapStep A p q := by
  classical
  unfold gapStep
  split_ifs
  · exact Finset.mem_union_right _ (Finset.mem_Ioc.mpr ⟨hpq, le_rfl⟩)
  · exact Finset.mem_insert_self q A

theorem mem_gapStep_iff_of_le (A : Finset ℕ) {p q a : ℕ}
    (ha : a ≤ p) (hpq : p < q) : a ∈ gapStep A p q ↔ a ∈ A := by
  classical
  unfold gapStep
  have hanew : a ∉ Finset.Ioc p q := by simp only [Finset.mem_Ioc]; omega
  have haq : a ≠ q := by omega
  split_ifs <;> simp [hanew, haq]

theorem gapStep_bounds {A : Finset ℕ} {p q : ℕ}
    (hA : ∀ a ∈ A, 2 ≤ a ∧ a ≤ p) (hp : 2 ≤ p) (hpq : p < q) :
    ∀ a ∈ gapStep A p q, 2 ≤ a ∧ a ≤ q := by
  classical
  intro a ha
  unfold gapStep at ha
  split_ifs at ha
  · rcases Finset.mem_union.mp ha with ha | ha
    · exact ⟨(hA a ha).1, (hA a ha).2.trans hpq.le⟩
    · have := Finset.mem_Ioc.mp ha
      omega
  · rcases Finset.mem_insert.mp ha with rfl | ha
    · omega
    · exact ⟨(hA a ha).1, (hA a ha).2.trans hpq.le⟩

theorem gapStep_collisionFree {A : Finset ℕ} {p q : ℕ}
    (hA : CollisionFree A) (hbound : ∀ a ∈ A, 2 ≤ a ∧ a ≤ p)
    (hq : q.Prime) (hpq : p < q) : CollisionFree (gapStep A p q) := by
  classical
  unfold gapStep
  split_ifs with h
  · exact h
  · exact hA.insert_prime hq (fun a ha ↦ ⟨(hbound a ha).1, (hbound a ha).2.trans_lt hpq⟩)

/-- The certified prefix at the `k`th prime. -/
noncomputable def stage : ℕ → Finset ℕ
  | 0 => {2}
  | k + 1 => gapStep (stage k) (prime k) (prime (k + 1))

theorem stage_bounds (k : ℕ) : ∀ a ∈ stage k, 2 ≤ a ∧ a ≤ prime k := by
  induction k with
  | zero => simp [stage]
  | succ k ih =>
    exact gapStep_bounds ih (prime_prime k).two_le (prime_strictMono (Nat.lt_succ_self k))

theorem stage_mono : Monotone stage := by
  apply monotone_nat_of_le_succ
  intro k
  exact subset_gapStep (stage k) (prime k) (prime (k + 1))

/-- Later stages never change membership below an already processed prime. -/
theorem stage_stable {k l a : ℕ} (hkl : k ≤ l) (ha : a ≤ prime k) :
    a ∈ stage l ↔ a ∈ stage k := by
  induction l, hkl using Nat.le_induction with
  | base => rfl
  | succ l hkl ih =>
    change a ∈ gapStep (stage l) (prime l) (prime (l + 1)) ↔ a ∈ stage k
    rw [mem_gapStep_iff_of_le _ (ha.trans (prime_strictMono.monotone hkl))
      (prime_strictMono (Nat.lt_succ_self l))]
    exact ih

theorem prime_mem_stage (k : ℕ) : prime k ∈ stage k := by
  cases k with
  | zero => simp [stage]
  | succ k => exact right_mem_gapStep _ (prime_strictMono (Nat.lt_succ_self k))

theorem stage_collisionFree (k : ℕ) : CollisionFree (stage k) := by
  induction k with
  | zero =>
    intro B C hB hC _
    have hB' : B = {2} := by
      obtain ⟨b, hb⟩ := hB.nonempty
      have hb2 : b = 2 := Finset.mem_singleton.mp (hB.subset hb)
      exact Finset.Subset.antisymm hB.subset (Finset.singleton_subset_iff.mpr (hb2 ▸ hb))
    have hC' : C = {2} := by
      obtain ⟨c, hc⟩ := hC.nonempty
      have hc2 : c = 2 := Finset.mem_singleton.mp (hC.subset hc)
      exact Finset.Subset.antisymm hC.subset (Finset.singleton_subset_iff.mpr (hc2 ▸ hc))
    exact hB'.trans hC'.symm
  | succ k ih =>
    exact gapStep_collisionFree ih (stage_bounds k) (prime_prime (k + 1))
      (prime_strictMono (Nat.lt_succ_self k))

/-- The infinite set produced by the construction in the selected paper. -/
def candidate : Set ℕ := {a | ∃ k, a ∈ stage k}

theorem stage_subset_candidate (k : ℕ) : ∀ a ∈ stage k, a ∈ candidate :=
  fun _ ha ↦ ⟨k, ha⟩

theorem candidate_two_le {a : ℕ} (ha : a ∈ candidate) : 2 ≤ a := by
  obtain ⟨k, hk⟩ := ha
  exact (stage_bounds k a hk).1

theorem candidate_mem_iff_stage {k a : ℕ} (ha : a ≤ prime k) :
    a ∈ candidate ↔ a ∈ stage k := by
  constructor
  · rintro ⟨l, hl⟩
    rcases le_total l k with hlk | hkl
    · exact stage_mono hlk hl
    · exact (stage_stable hkl ha).mp hl
  · exact stage_subset_candidate k a

/-- The whole interior of this prime gap is rejected by the finite test. -/
def Rejected (k : ℕ) : Prop :=
  ¬ CollisionFree (stage k ∪ Finset.Ioc (prime k) (prime (k + 1)))

/-- No later stage can change the all-or-nothing decision on a gap interior. -/
theorem candidate_mem_gap_iff {k a : ℕ}
    (ha : prime k < a) (haq : a < prime (k + 1)) :
    a ∈ candidate ↔ ¬ Rejected k := by
  classical
  rw [candidate_mem_iff_stage haq.le]
  change a ∈ gapStep (stage k) (prime k) (prime (k + 1)) ↔ ¬ Rejected k
  have haold : a ∉ stage k := by
    intro h
    exact ha.not_ge (stage_bounds k a h).2
  have hanew : a ∈ Finset.Ioc (prime k) (prime (k + 1)) :=
    Finset.mem_Ioc.mpr ⟨ha, haq.le⟩
  unfold gapStep Rejected
  split_ifs with h <;> simp [h, haold, hanew, haq.ne]

theorem candidate_contains_primes {p : ℕ} (hp : p.Prime) : p ∈ candidate := by
  have h := prime_mem_stage (Nat.count Nat.Prime p)
  have heq : prime (Nat.count Nat.Prime p) = p := Nat.nth_count hp
  refine ⟨Nat.count Nat.Prime p, ?_⟩
  rwa [heq] at h

theorem candidate_infinite : candidate.Infinite :=
  Nat.infinite_setOfPred_prime.mono (fun _ hp ↦ candidate_contains_primes hp)

theorem finite_subset_stage (B : Finset ℕ) (hB : ∀ b ∈ B, b ∈ candidate) :
    ∃ k, B ⊆ stage k := by
  induction B using Finset.induction_on with
  | empty => exact ⟨0, Finset.empty_subset _⟩
  | @insert a B ha ih =>
    obtain ⟨k, hk⟩ := hB a (Finset.mem_insert_self a B)
    obtain ⟨l, hl⟩ := ih (fun b hb ↦ hB b (Finset.mem_insert_of_mem hb))
    refine ⟨max k l, Finset.insert_subset_iff.mpr ⟨?_, ?_⟩⟩
    · exact stage_mono (le_max_left k l) hk
    · exact hl.trans (stage_mono (le_max_right k l))

/-- No finite collision appears for the first time at the infinite union. -/
theorem candidate_collisionFree : SetCollisionFree candidate := by
  intro B C hB hC hprod
  obtain ⟨k, hk⟩ := finite_subset_stage (B ∪ C) (by
    intro a ha
    rcases Finset.mem_union.mp ha with ha | ha
    · exact hB.subset a ha
    · exact hC.subset a ha)
  exact stage_collisionFree k B C
    (hB.restrict (stage_subset_candidate k) (Finset.subset_union_left.trans hk))
    (hC.restrict (stage_subset_candidate k) (Finset.subset_union_right.trans hk)) hprod

/-- The increasing enumeration of Chojecki's candidate. -/
noncomputable def candidateSequence : ℕ → ℕ := Nat.nth (· ∈ candidate)

theorem candidateSequence_strictMono : StrictMono candidateSequence :=
  Nat.nth_strictMono candidate_infinite

theorem range_candidateSequence : Set.range candidateSequence = candidate :=
  Nat.range_nth_of_infinite candidate_infinite

theorem candidateSequence_two_le (k : ℕ) : 2 ≤ candidateSequence k :=
  candidate_two_le (Nat.nth_mem_of_infinite candidate_infinite k)

/-- The original product-injectivity requirement holds for this candidate;
the density requirement is separate and is not proved in this file. -/
theorem candidateSequence_products_injective :
    {uv : ℕ × ℕ | uv.1 ≤ uv.2}.InjOn
      (fun uv ↦ ∏ i ∈ Finset.Icc uv.1 uv.2, candidateSequence i) := by
  apply blockProducts_injective candidateSequence_strictMono
  rw [range_candidateSequence]
  exact candidate_collisionFree

/-- A rejected gap gives adjacent boundary primes in the final enumeration. -/
theorem rejected_adjacent (k : ℕ) (hk : Rejected k) :
    ∃ i, candidateSequence i = prime k ∧ candidateSequence (i + 1) = prime (k + 1) := by
  have hp : prime k ∈ Set.range candidateSequence := by
    rw [range_candidateSequence]
    exact candidate_contains_primes (prime_prime k)
  have hq : prime (k + 1) ∈ Set.range candidateSequence := by
    rw [range_candidateSequence]
    exact candidate_contains_primes (prime_prime (k + 1))
  obtain ⟨i, hi⟩ := hp
  obtain ⟨j, hj⟩ := hq
  have hij : i < j := by
    apply candidateSequence_strictMono.lt_iff_lt.mp
    rw [hi, hj]
    exact prime_strictMono (Nat.lt_succ_self k)
  have heq : j = i + 1 := by
    by_contra h
    have hij' : i + 1 < j := by omega
    have hlo : prime k < candidateSequence (i + 1) := by
      rw [← hi]
      exact candidateSequence_strictMono (Nat.lt_succ_self i)
    have hhi : candidateSequence (i + 1) < prime (k + 1) := by
      rw [← hj]
      exact candidateSequence_strictMono hij'
    have hm : candidateSequence (i + 1) ∈ candidate :=
      Nat.nth_mem_of_infinite candidate_infinite (i + 1)
    exact (candidate_mem_gap_iff hlo hhi).mp hm hk
  exact ⟨i, hi, heq ▸ hj⟩

end Erdos421
