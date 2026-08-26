import ErdosProblems.Erdos421.RawGaps

/-!
# The parent forest of rejected prime gaps

Every nonraw rejection has an earlier rejected gap whose retained boundary
primes occur in its earlier witness block. Parent indices strictly decrease.
-/

namespace Erdos421

structure RejectedWitness (k : ℕ) where
  E : Finset ℕ
  m : ℕ
  n : ℕ
  gap_left : prime k < m
  later_nonempty : m ≤ n
  gap_right : n < prime (k + 1)
  earlier_block : IsBlock (stage k ∪ Finset.Ioc (prime k) (prime (k + 1))) E
  separated : ∀ e ∈ E, e < m
  product_eq : E.prod id = (Finset.Icc m n).prod id

theorem rejectedWitness_exists {k : ℕ} (hk : Rejected k) : Nonempty (RejectedWitness k) := by
  obtain ⟨E, m, n, hpm, hmn, hnq, hE, hsep, hprod, _⟩ :=
    canonical_rejection (stage_collisionFree k) (stage_bounds k) (prime_mem_stage k)
      (prime_prime k) (prime_prime (k + 1)) (prime_strictMono (Nat.lt_succ_self k)) hk
  exact ⟨⟨E, m, n, hpm, hmn, hnq, hE, hsep, hprod⟩⟩

theorem RejectedWitness.raw_of_eq_Icc {k : ℕ} (w : RejectedWitness k) (hk : Rejected k)
    {a b : ℕ} (ha : 2 ≤ a) (hab : a ≤ b) (hE : w.E = Finset.Icc a b) : Raw k := by
  refine ⟨hk, ⟨{
    a := a, b := b, m := w.m, n := w.n
    two_le_a := ha
    earlier_nonempty := hab
    separated := ?_
    gap_left := w.gap_left
    later_nonempty := w.later_nonempty
    gap_right := w.gap_right
    earlier_block := ?_
    product_eq := ?_
  }⟩⟩
  · apply w.separated b
    rw [hE]
    exact Finset.mem_Icc.mpr ⟨hab, le_rfl⟩
  · simpa only [hE] using w.earlier_block
  · simpa only [hE] using w.product_eq

theorem RejectedWitness.old_of_not_raw {k : ℕ} (w : RejectedWitness k)
    (hk : Rejected k) (hraw : ¬ Raw k) : IsBlock (stage k) w.E := by
  rcases earlier_block_location (prime_prime k) (prime_mem_stage k) (prime_succ_le_two_mul k)
      w.gap_left w.gap_right w.earlier_block w.separated w.product_eq with hE | hE
  · exact w.earlier_block.restrict Finset.subset_union_left hE
  · obtain ⟨a, b, hpa, hab, _, hE⟩ := hE
    have ha : 2 ≤ a := (prime_prime k).two_le.trans hpa.le
    exact False.elim (hraw (w.raw_of_eq_Icc hk ha hab hE))

theorem exists_prime_gap {n : ℕ} (hn : 2 ≤ n) :
    ∃ k, prime k ≤ n ∧ n < prime (k + 1) := by
  classical
  have hex : ∃ j, n < prime j :=
    ⟨n + 1, (Nat.lt_succ_self n).trans_le (prime_strictMono.id_le (n + 1))⟩
  let j := Nat.find hex
  have hj : n < prime j := Nat.find_spec hex
  have hj0 : j ≠ 0 := by
    intro h
    rw [h, prime_zero] at hj
    omega
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hj0
  refine ⟨k, ?_, ?_⟩
  · apply le_of_not_gt
    exact Nat.find_min hex (show k < j by omega)
  · simpa only [hk, Nat.succ_eq_add_one] using hj

theorem omitted_mem_rejected_gap {n : ℕ} (hn : 2 ≤ n) (hnot : n ∉ candidate) :
    ∃ k, prime k < n ∧ n < prime (k + 1) ∧ Rejected k := by
  classical
  obtain ⟨k, hk, hk'⟩ := exists_prime_gap hn
  have hlo : prime k < n := by
    by_contra h
    have heq : prime k = n := by omega
    exact hnot (heq ▸ candidate_contains_primes (prime_prime k))
  refine ⟨k, hlo, hk', ?_⟩
  by_contra h
  exact hnot ((candidate_mem_gap_iff hlo hk').mpr h)

theorem IsBlock.stage_to_candidate {k : ℕ} {E : Finset ℕ} (hE : IsBlock (stage k) E) :
    IsSetBlock candidate E := by
  refine ⟨hE.nonempty, fun e he ↦ stage_subset_candidate k e (hE.subset he), ?_⟩
  intro a b x ha hb hx hax hxb
  have hxb' := (stage_bounds k b (hE.subset hb)).2
  exact hE.convex ha hb ((candidate_mem_iff_stage (hxb.trans hxb')).mp hx) hax hxb

/-- An omitted integer inside a block locates a rejected gap crossed by that block. -/
theorem missing_in_block_parent {k : ℕ} {E : Finset ℕ} (hE : IsBlock (stage k) E)
    {a b x : ℕ} (ha : a ∈ E) (hb : b ∈ E) (hax : a ≤ x) (hxb : x ≤ b)
    (hxE : x ∉ E) :
    ∃ i, i < k ∧ Rejected i ∧ prime i ∈ E ∧ prime (i + 1) ∈ E := by
  have hapos := (stage_bounds k a (hE.subset ha)).1
  have hbmax := (stage_bounds k b (hE.subset hb)).2
  have hxstage : x ∉ stage k := fun hx ↦ hxE (hE.convex ha hb hx hax hxb)
  have hxcandidate : x ∉ candidate := by
    intro hx
    exact hxstage ((candidate_mem_iff_stage (hxb.trans hbmax)).mp hx)
  obtain ⟨i, hix, hxq, hiRej⟩ := omitted_mem_rejected_gap (hapos.trans hax) hxcandidate
  have hik : i < k := prime_strictMono.lt_iff_lt.mp (hix.trans_le (hxb.trans hbmax))
  have hacand := stage_subset_candidate k a (hE.subset ha)
  have hbcand := stage_subset_candidate k b (hE.subset hb)
  have hapi : a ≤ prime i := by
    by_contra h
    have hia : prime i < a := by omega
    exact (candidate_mem_gap_iff hia (hax.trans_lt hxq)).mp hacand hiRej
  have hqib : prime (i + 1) ≤ b := by
    by_contra h
    have hbq : b < prime (i + 1) := by omega
    exact (candidate_mem_gap_iff (hix.trans_le hxb) hbq).mp hbcand hiRej
  have hpiStage := stage_mono hik.le (prime_mem_stage i)
  have hqiStage := stage_mono (show i + 1 ≤ k from hik) (prime_mem_stage (i + 1))
  refine ⟨i, hik, hiRej, ?_, ?_⟩
  · exact hE.convex ha hb hpiStage hapi (hix.le.trans hxb)
  · exact hE.convex ha hb hqiStage (hax.trans hxq.le) hqib

structure ParentData (k : ℕ) where
  witness : RejectedWitness k
  old_block : IsBlock (stage k) witness.E
  index : ℕ
  index_lt : index < k
  rejected : Rejected index
  left_mem : prime index ∈ witness.E
  right_mem : prime (index + 1) ∈ witness.E

theorem parentData_exists {k : ℕ} (hk : Rejected k) (hraw : ¬ Raw k) : Nonempty (ParentData k) := by
  obtain ⟨w⟩ := rejectedWitness_exists hk
  have hE := w.old_of_not_raw hk hraw
  let a := w.E.min' hE.nonempty
  let b := w.E.max' hE.nonempty
  have ha : a ∈ w.E := w.E.min'_mem hE.nonempty
  have hb : b ∈ w.E := w.E.max'_mem hE.nonempty
  have hab : a ≤ b := w.E.min'_le b hb
  have hsub : w.E ⊆ Finset.Icc a b := by
    intro x hx
    exact Finset.mem_Icc.mpr ⟨w.E.min'_le x hx, w.E.le_max' x hx⟩
  have hne : w.E ≠ Finset.Icc a b := by
    intro heq
    exact hraw (w.raw_of_eq_Icc hk (stage_bounds k a (hE.subset ha)).1 hab heq)
  have hnsub : ¬ Finset.Icc a b ⊆ w.E := fun h ↦ hne (Finset.Subset.antisymm hsub h)
  obtain ⟨x, hx, hxE⟩ := Finset.not_subset.mp hnsub
  obtain ⟨hax, hxb⟩ := Finset.mem_Icc.mp hx
  obtain ⟨i, hik, hiRej, hpiE, hqiE⟩ := missing_in_block_parent hE ha hb hax hxb hxE
  exact ⟨⟨w, hE, i, hik, hiRej, hpiE, hqiE⟩⟩

noncomputable def chosenParentData (k : ℕ) (h : Rejected k ∧ ¬ Raw k) : ParentData k :=
  Classical.choice (parentData_exists h.1 h.2)

noncomputable def parent (k : ℕ) : ℕ := by
  classical
  exact if h : Rejected k ∧ ¬ Raw k then (chosenParentData k h).index else k

theorem parent_lt {k : ℕ} (hk : Rejected k) (hraw : ¬ Raw k) : parent k < k := by
  classical
  have h : Rejected k ∧ ¬ Raw k := ⟨hk, hraw⟩
  simp only [parent, dif_pos h]
  exact (chosenParentData k ⟨hk, hraw⟩).index_lt

theorem parent_rejected {k : ℕ} (hk : Rejected k) (hraw : ¬ Raw k) : Rejected (parent k) := by
  classical
  have h : Rejected k ∧ ¬ Raw k := ⟨hk, hraw⟩
  simp only [parent, dif_pos h]
  exact (chosenParentData k ⟨hk, hraw⟩).rejected

theorem parent_wellFounded :
    WellFounded (fun i j ↦ Rejected j ∧ ¬ Raw j ∧ parent j = i) := by
  apply Nat.lt_wfRel.wf.mono
  intro i j h
  exact h.2.2 ▸ parent_lt h.1 h.2.1

end Erdos421
