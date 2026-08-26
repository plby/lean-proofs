import ErdosProblems.Erdos421.SequenceBlocks

/-! # A uniform bound on the number of short children of a fixed parent -/

namespace Erdos421

theorem parentData_card_bound (I : Finset ℕ) (i L H : ℕ)
    (w : (k : I) → ParentData k)
    (hparent : ∀ k, (w k).index = i)
    (hL : ∀ k, (w k).witness.E.card ≤ L)
    (hH : ∀ k, (w k).witness.n - (w k).witness.m + 1 ≤ H) :
    I.card ≤ L * (H * L) := by
  classical
  have hp : prime i ∈ Set.range candidateSequence := by
    rw [range_candidateSequence]
    exact candidate_contains_primes (prime_prime i)
  obtain ⟨t, ht⟩ := hp
  have hstarts : ∀ k : I, ∃ u,
      (w k).witness.E = (Finset.Ico u (u + (w k).witness.E.card)).image candidateSequence := by
    intro k
    have hblock := (w k).old_block.stage_to_candidate
    rw [← range_candidateSequence] at hblock
    exact hblock.exists_start candidateSequence_strictMono
  choose start hstart using hstarts
  have hcross : ∀ k : I, start k ≤ t ∧ t < start k + (w k).witness.E.card := by
    intro k
    have hmem := (w k).left_mem
    rw [hparent k, ← ht, hstart k] at hmem
    obtain ⟨j, hj, heq⟩ := Finset.mem_image.mp hmem
    have hjt : j = t := candidateSequence_strictMono.injective heq
    simpa only [hjt, Finset.mem_Ico] using hj
  let code : I → Fin L × Fin H × Fin L := fun k ↦
    (⟨(w k).witness.E.card - 1, by
        have := (w k).old_block.nonempty.card_pos
        have := hL k
        omega⟩,
     ⟨(w k).witness.n - (w k).witness.m, by have := hH k; omega⟩,
     ⟨t - start k, by have := hcross k; have := hL k; omega⟩)
  have hinj : Function.Injective code := by
    intro k l heq
    have hr : (w k).witness.E.card = (w l).witness.E.card := by
      have h := congrArg (fun c : Fin L × Fin H × Fin L ↦ c.1.val) heq
      have := (w k).old_block.nonempty.card_pos
      have := (w l).old_block.nonempty.card_pos
      dsimp only [code] at h
      omega
    have hs : (w k).witness.n - (w k).witness.m =
        (w l).witness.n - (w l).witness.m :=
      congrArg (fun c : Fin L × Fin H × Fin L ↦ c.2.1.val) heq
    have hc : t - start k = t - start l :=
      congrArg (fun c : Fin L × Fin H × Fin L ↦ c.2.2.val) heq
    have hstartEq : start k = start l := by
      have := hcross k
      have := hcross l
      omega
    have hE : (w k).witness.E = (w l).witness.E := by
      rw [hstart k, hstart l, hstartEq, hr]
    have hprod : intervalProduct (w k).witness.m
        ((w k).witness.n - (w k).witness.m + 1) =
        intervalProduct (w l).witness.m ((w k).witness.n - (w k).witness.m + 1) := by
      calc
        _ = (w k).witness.E.prod id :=
          (intervalProduct_eq_Icc (w k).witness.later_nonempty).trans
            (w k).witness.product_eq.symm
        _ = (w l).witness.E.prod id := congrArg (Finset.prod · id) hE
        _ = _ := by
          rw [hs, intervalProduct_eq_Icc (w l).witness.later_nonempty]
          exact (w l).witness.product_eq
    have hm : (w k).witness.m = (w l).witness.m :=
      intervalProduct_injective (by omega) hprod
    apply Subtype.ext
    apply prime_gap_index_unique (w k).witness.gap_left
      ((w k).witness.later_nonempty.trans_lt (w k).witness.gap_right)
    · rw [hm]
      exact (w l).witness.gap_left
    · rw [hm]
      exact (w l).witness.later_nonempty.trans_lt (w l).witness.gap_right
  simpa only [Fintype.card_coe, Fintype.card_prod, Fintype.card_fin] using
    Fintype.card_le_of_injective code hinj

noncomputable def shortChildren (B i : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range B).filter
    (fun k ↦ Rejected k ∧ ¬ Raw k ∧ ShortGap k ∧ prime (k + 1) ≤ B ∧ parent k = i)

theorem mem_shortChildren {B i k : ℕ} : k ∈ shortChildren B i ↔
    Rejected k ∧ ¬ Raw k ∧ ShortGap k ∧ prime (k + 1) ≤ B ∧ parent k = i := by
  classical
  constructor
  · intro hk
    exact (Finset.mem_filter.mp hk).2
  · intro hk
    have hidx : k + 1 ≤ prime (k + 1) := prime_strictMono.id_le (k + 1)
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (hidx.trans hk.2.2.2.1), hk⟩

theorem shortChildren_card_scale (i : ℕ) {u : ℕ} (hu : 10 ≤ u) :
    (shortChildren (2 ^ (60 * u)) i).card ≤ 2 ^ (11 * u) := by
  classical
  let I := shortChildren (2 ^ (60 * u)) i
  have hmem : ∀ k : I, Rejected k ∧ ¬ Raw k ∧ ShortGap k ∧
      prime (k + 1) ≤ 2 ^ (60 * u) ∧ parent k = i := fun k ↦ mem_shortChildren.mp k.property
  let w : (k : I) → ParentData k :=
    fun k ↦ chosenParentData k ⟨(hmem k).1, (hmem k).2.1⟩
  have hparent : ∀ k : I, (w k).index = i := by
    intro k
    have h : Rejected k ∧ ¬ Raw k := ⟨(hmem k).1, (hmem k).2.1⟩
    have hp : parent k = (w k).index := by simp only [parent, dif_pos h, w]
    exact hp.symm.trans (hmem k).2.2.2.2
  have hcount := parentData_card_bound I i (2 ^ (4 * u)) (2 ^ (3 * u)) w hparent
    (fun k ↦ (w k).witness.length_le_scale (hmem k).2.2.1 (hmem k).2.2.2.1 hu)
    (fun k ↦ (w k).witness.later_length_le_scale (hmem k).2.2.1 (hmem k).2.2.2.1)
  have hp : 2 ^ (4 * u) * (2 ^ (3 * u) * 2 ^ (4 * u)) = 2 ^ (11 * u) := by
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  rwa [hp] at hcount

end Erdos421
