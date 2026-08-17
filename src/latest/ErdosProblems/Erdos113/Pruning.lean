import Mathlib

namespace Erdos113Pruning

theorem exists_pruned_subfamily_weighted {a : Type*} [DecidableEq a]
    (C : Finset a) (fibers : Finset (Finset a)) (t : Finset a → ℕ) :
    ∃ D : Finset a,
      D ⊆ C ∧
      C.card ≤ D.card + ∑ F ∈ fibers, (t F - 1) ∧
      ∀ F ∈ fibers, (D ∩ F).Nonempty → t F ≤ (D ∩ F).card := by
  induction hn : fibers.card using Nat.strong_induction_on generalizing C fibers with
  | h n ih =>
      by_cases hsmall : ∃ F ∈ fibers,
          (C ∩ F).Nonempty ∧ (C ∩ F).card < t F
      · obtain ⟨F, hFmem, _hFnonempty, hFsmall⟩ := hsmall
        have herase_lt : (fibers.erase F).card < n := by
          rw [← hn]
          exact Finset.card_erase_lt_of_mem hFmem
        obtain ⟨D, hDsub, hDcard, hDstab⟩ :=
          ih (fibers.erase F).card herase_lt (C \ F) (fibers.erase F) rfl
        refine ⟨D, hDsub.trans Finset.sdiff_subset, ?_, ?_⟩
        · have hsplit := Finset.card_sdiff_add_card_inter C F
          have hFbound : (C ∩ F).card ≤ t F - 1 := Nat.le_sub_one_of_lt hFsmall
          calc
            C.card = (C \ F).card + (C ∩ F).card := hsplit.symm
            _ ≤ (D.card + ∑ F' ∈ fibers.erase F, (t F' - 1)) +
                (t F - 1) := Nat.add_le_add hDcard hFbound
            _ = D.card + ∑ F' ∈ fibers, (t F' - 1) := by
              rw [← Finset.sum_erase_add fibers (fun F' ↦ t F' - 1) hFmem]
              omega
        · intro F' hF'mem hnonempty
          by_cases hF'eq : F' = F
          · subst F'
            obtain ⟨x, hx⟩ := hnonempty
            have ⟨hxD, hxF⟩ := Finset.mem_inter.mp hx
            exact ((Finset.mem_sdiff.mp (hDsub hxD)).2 hxF).elim
          · exact hDstab F' (Finset.mem_erase.mpr ⟨hF'eq, hF'mem⟩) hnonempty
      · refine ⟨C, Finset.Subset.rfl, ?_, ?_⟩
        · omega
        · intro F hF hnonempty
          exact le_of_not_gt (fun hlt ↦ hsmall ⟨F, hF, hnonempty, hlt⟩)

theorem exists_pruned_indexed {a K : Type*} [DecidableEq a] [DecidableEq K]
    (C : Finset a) (S : Finset K) (fiber : K → Finset a) (t : K → ℕ) :
    ∃ D : Finset a,
      D ⊆ C ∧
      C.card ≤ D.card + ∑ k ∈ S, (t k - 1) ∧
      ∀ k ∈ S, (D ∩ fiber k).Nonempty → t k ≤ (D ∩ fiber k).card := by
  induction hn : S.card using Nat.strong_induction_on generalizing C S with
  | h n ih =>
      by_cases hsmall : ∃ k ∈ S,
          (C ∩ fiber k).Nonempty ∧ (C ∩ fiber k).card < t k
      · obtain ⟨k, hk, _hne, hlt⟩ := hsmall
        have herase_lt : (S.erase k).card < n := by
          rw [← hn]
          exact Finset.card_erase_lt_of_mem hk
        obtain ⟨D, hDsub, hDcard, hDstab⟩ :=
          ih (S.erase k).card herase_lt (C \ fiber k) (S.erase k) rfl
        refine ⟨D, hDsub.trans Finset.sdiff_subset, ?_, ?_⟩
        · have hsplit := Finset.card_sdiff_add_card_inter C (fiber k)
          have hkbound : (C ∩ fiber k).card ≤ t k - 1 := Nat.le_sub_one_of_lt hlt
          calc
            C.card = (C \ fiber k).card + (C ∩ fiber k).card := hsplit.symm
            _ ≤ (D.card + ∑ j ∈ S.erase k, (t j - 1)) + (t k - 1) :=
              Nat.add_le_add hDcard hkbound
            _ = D.card + ∑ j ∈ S, (t j - 1) := by
              rw [← Finset.sum_erase_add S (fun j ↦ t j - 1) hk]
              omega
        · intro j hj hnonempty
          by_cases hjk : j = k
          · subst j
            obtain ⟨x, hx⟩ := hnonempty
            have ⟨hxD, hxF⟩ := Finset.mem_inter.mp hx
            exact ((Finset.mem_sdiff.mp (hDsub hxD)).2 hxF).elim
          · exact hDstab j (Finset.mem_erase.mpr ⟨hjk, hj⟩) hnonempty
      · refine ⟨C, Finset.Subset.rfl, by omega, ?_⟩
        intro k hk hne
        exact le_of_not_gt (fun hlt ↦ hsmall ⟨k, hk, hne, hlt⟩)

end Erdos113Pruning
