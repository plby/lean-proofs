import ErdosProblems.Erdos421.EqualDescendants

/-! # Equal-descendant counts weighted by the root gap length -/

namespace Erdos421

theorem gapLength_pos (i : ℕ) : 0 < gapLength i := by
  have h : prime i < prime (i + 1) := prime_strictMono (Nat.lt_succ_self i)
  unfold gapLength
  omega

/-- The root and its equal descendants can be encoded by distinct positive
multipliers, each at most `H / rootLength`. -/
theorem equal_descendant_card_mul_bound (S : Finset ℕ) (i H : ℕ)
    (hS : ∀ k ∈ S, gapLength k ≤ H ∧ (k = i ∨ EqualEdge i k)) :
    gapLength i * S.card ≤ H := by
  classical
  have hcode : ∀ k : S, ∃ j, 1 ≤ j ∧ j * gapLength i ≤ H ∧
      (j = 1 ↔ k.val = i) ∧
      (k.val ≠ i → prime k < j * prime i ∧ j * prime (i + 1) < prime (k + 1)) := by
    intro k
    have hk := hS k k.property
    by_cases hki : k.val = i
    · refine ⟨1, le_rfl, ?_, by simp [hki], fun h ↦ (h hki).elim⟩
      simpa only [one_mul, hki] using hk.1
    · obtain ⟨j, hj, hL, hR⟩ := hk.2.resolve_left hki
      have hlen : j * gapLength i < gapLength k :=
        equal_edge_length (prime_strictMono (Nat.lt_succ_self i)).le hL hR
      exact ⟨j, by omega, hlen.le.trans hk.1,
        by simp [hki, show j ≠ 1 by omega], fun _ ↦ ⟨hL, hR⟩⟩
  choose code hcode using hcode
  let f : S → Fin (H / gapLength i) := fun k ↦ ⟨code k - 1, by
    have hle : code k ≤ H / gapLength i :=
      (Nat.le_div_iff_mul_le (gapLength_pos i)).mpr (hcode k).2.1
    have hpos := (hcode k).1
    omega⟩
  have hinj : Function.Injective f := by
    intro k l heq
    have hc : code k = code l := by
      have h := congrArg Fin.val heq
      change code k - 1 = code l - 1 at h
      have := (hcode k).1
      have := (hcode l).1
      omega
    by_cases hki : k.val = i
    · have hli : l.val = i :=
        (hcode l).2.2.1.mp (hc ▸ (hcode k).2.2.1.mpr hki)
      exact Subtype.ext (hki.trans hli.symm)
    · have hli : l.val ≠ i := by
        intro hli
        exact hki ((hcode k).2.2.1.mp (hc.trans ((hcode l).2.2.1.mpr hli)))
      have hk := (hcode k).2.2.2 hki
      have hl := (hcode l).2.2.2 hli
      apply Subtype.ext
      apply prime_gap_index_unique hk.1
        ((Nat.mul_le_mul_left (code k) (prime_strictMono (Nat.lt_succ_self i)).le).trans_lt hk.2)
      · rw [hc]
        exact hl.1
      · rw [hc]
        exact (Nat.mul_le_mul_left (code l)
          (prime_strictMono (Nat.lt_succ_self i)).le).trans_lt hl.2
  have hcard : S.card ≤ H / gapLength i := by
    simpa only [Fintype.card_coe, Fintype.card_fin] using Fintype.card_le_of_injective f hinj
  calc
    gapLength i * S.card ≤ gapLength i * (H / gapLength i) := Nat.mul_le_mul_left _ hcard
    _ ≤ H := by simpa only [mul_comm] using Nat.div_mul_le_self H (gapLength i)

/-- Weighting the count avoids losing an extra factor of the short-gap threshold. -/
theorem equal_descendant_mass_mul_bound (S : Finset ℕ) (i H : ℕ)
    (hS : ∀ k ∈ S, gapLength k ≤ H ∧ (k = i ∨ EqualEdge i k)) :
    gapLength i * (∑ k ∈ S, gapLength k) ≤ H ^ 2 := by
  have hcard := equal_descendant_card_mul_bound S i H hS
  have hsum : (∑ k ∈ S, gapLength k) ≤ S.card * H :=
    Finset.sum_le_card_nsmul S gapLength H (fun k hk ↦ (hS k hk).1)
  calc
    _ ≤ gapLength i * (S.card * H) := Nat.mul_le_mul_left _ hsum
    _ = H * (gapLength i * S.card) := by ring
    _ ≤ H * H := Nat.mul_le_mul_left H hcard
    _ = H ^ 2 := by ring

theorem equalDescendants_mass_scale (i u : ℕ) :
    gapLength i * (∑ k ∈ equalDescendants (2 ^ (60 * u)) i, gapLength k) ≤ 2 ^ (6 * u) := by
  have h := equal_descendant_mass_mul_bound (equalDescendants (2 ^ (60 * u)) i)
    i (2 ^ (3 * u)) (by
      intro k hk
      have hmem := mem_equalDescendants.mp hk
      exact ⟨hmem.1.length_le_scale hmem.2.1, hmem.2.2⟩)
  have hpow : (2 ^ (3 * u)) ^ 2 = 2 ^ (6 * u) := by
    rw [← pow_mul]
    congr 1
    omega
  rwa [hpow] at h

end Erdos421
