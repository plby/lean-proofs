import ErdosProblems.Erdos587.GAPDilationCover

/-!
Uniform translate covers between coordinatewise commensurable GAPs.
Neither progression is required to be proper. This is the covering step
used to propagate bounded doubling beyond the selected high-fold scale.
-/

open scoped Pointwise BigOperators

namespace Erdos587.GeneralizedAP

theorem exists_row_remainder (a L C B k : ℕ) (ha : 0 < a) (haB : a ≤ B)
    (hk : k < C * (L + 1)) :
    ∃ u : Fin C, ∃ r : Fin B, ∃ s : Fin (L + 1),
      k = u.val * (a * (L + 1)) + r.val + a * s.val := by
  have hden : 0 < a * (L + 1) := Nat.mul_pos ha (Nat.succ_pos _)
  have hku : k < C * (a * (L + 1)) := by
    apply hk.trans_le
    exact Nat.mul_le_mul_left C (by nlinarith)
  refine ⟨⟨k / (a * (L + 1)), (Nat.div_lt_iff_lt_mul hden).mpr hku⟩,
    ⟨k % a, (Nat.mod_lt k ha).trans_le haB⟩,
    ⟨k / a % (L + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩, ?_⟩
  have h₁ := Nat.div_add_mod k a
  have h₂ := Nat.div_add_mod (k / a) (L + 1)
  rw [Nat.div_div_eq_div_mul] at h₂
  dsimp only
  nlinarith

/-- Positive coordinate multipliers give a translate cover whose cost is
the product of the multiplier and side-ratio bounds. -/
theorem exists_cover_of_positive_multipliers
    (P Q : GeneralizedAP) (hrank : Q.rank = P.rank)
    (a : Fin P.rank → ℕ) (C B : ℕ)
    (ha : ∀ i, 0 < a i ∧ a i ≤ B)
    (hstep : ∀ i : Fin Q.rank, ∀ j : Fin P.rank, i.val = j.val →
      Q.step i = (a j : ℤ) * P.step j)
    (hside : ∀ i : Fin Q.rank, ∀ j : Fin P.rank, i.val = j.val →
      P.length j < C * (Q.length i + 1)) :
    ∃ U : Finset ℤ, U.card ≤ (C * B) ^ P.rank ∧ P.carrier ⊆ U + Q.carrier := by
  classical
  let e : Fin P.rank ≃ Fin Q.rank := finCongr hrank.symm
  let offset (u : Fin P.rank → Fin C × Fin B) : ℤ :=
    P.base - Q.base + ∑ j : Fin P.rank,
      ((u j).1.val * (a j * (Q.length (e j) + 1)) + (u j).2.val : ℕ) * P.step j
  let U := (Finset.univ : Finset (Fin P.rank → Fin C × Fin B)).image offset
  refine ⟨U, ?_, ?_⟩
  · calc
      U.card ≤ (Finset.univ : Finset (Fin P.rank → Fin C × Fin B)).card :=
        Finset.card_image_le
      _ = (C * B) ^ P.rank := by simp
  · intro z hz
    obtain ⟨x, rfl⟩ := P.mem_carrier_iff.mp hz
    have hx (j : Fin P.rank) : (x j : ℕ) < C * (Q.length (e j) + 1) :=
      (Nat.le_of_lt_succ (x j).isLt).trans_lt (hside (e j) j rfl)
    choose u r s hs using fun j => exists_row_remainder (a j) (Q.length (e j)) C B
      (x j) (ha j).1 (ha j).2 (hx j)
    let y : Q.Param := fun i =>
      ⟨(s (e.symm i)).val, by simpa using (s (e.symm i)).isLt⟩
    have hy (j : Fin P.rank) : (y (e j) : ℕ) = (s j).val := by
      change (s (e.symm (e j))).val = (s j).val
      exact congrArg (fun k => (s k).val) (e.symm_apply_apply j)
    have heval : offset (fun j => (u j, r j)) + Q.eval y = P.eval x := by
      have hsum : (∑ i : Fin Q.rank, (y i : ℤ) * Q.step i) =
          ∑ j : Fin P.rank, (y (e j) : ℤ) * Q.step (e j) :=
        (Fintype.sum_equiv e _ _ (fun _ => rfl)).symm
      have hcoord (j : Fin P.rank) :
          (((u j).val * (a j * (Q.length (e j) + 1)) + (r j).val : ℕ) : ℤ) *
              P.step j + (y (e j) : ℤ) * Q.step (e j) = (x j : ℤ) * P.step j := by
        rw [hstep (e j) j rfl]
        have hc : (x j : ℤ) =
            (((u j).val * (a j * (Q.length (e j) + 1)) + (r j).val : ℕ) : ℤ) +
              (a j : ℤ) * (y (e j) : ℤ) := by
          exact_mod_cast (hs j).trans (by rw [hy])
        rw [hc]
        ring
      simp only [offset, eval]
      rw [hsum]
      have hh := Finset.sum_congr (s₁ := (Finset.univ : Finset (Fin P.rank)))
        (s₂ := Finset.univ) rfl (fun j _ => hcoord j)
      rw [Finset.sum_add_distrib] at hh
      linear_combination hh
    exact Finset.mem_add.mpr ⟨offset (fun j => (u j, r j)),
      Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩, Q.eval y,
      Q.mem_carrier_iff.mpr ⟨y, rfl⟩, heval⟩

theorem card_le_of_positive_multipliers
    (P Q : GeneralizedAP) (hrank : Q.rank = P.rank)
    (a : Fin P.rank → ℕ) (C B : ℕ)
    (ha : ∀ i, 0 < a i ∧ a i ≤ B)
    (hstep : ∀ i : Fin Q.rank, ∀ j : Fin P.rank, i.val = j.val →
      Q.step i = (a j : ℤ) * P.step j)
    (hside : ∀ i : Fin Q.rank, ∀ j : Fin P.rank, i.val = j.val →
      P.length j < C * (Q.length i + 1)) :
    P.carrier.card ≤ (C * B) ^ P.rank * Q.carrier.card := by
  obtain ⟨U, hU, hcover⟩ := P.exists_cover_of_positive_multipliers Q hrank a C B ha hstep hside
  exact (Finset.card_le_card hcover).trans
    (Finset.card_add_le.trans (Nat.mul_le_mul_right _ hU))

/-- Reflecting the coefficient intervals removes signs from the multipliers
without changing either carrier. -/
theorem card_le_of_integer_multipliers
    (P Q : GeneralizedAP) (hrank : Q.rank = P.rank)
    (a : Fin P.rank → ℤ) (C B : ℕ)
    (ha : ∀ i, a i ≠ 0 ∧ |a i| ≤ (B : ℤ))
    (hstep : ∀ i : Fin Q.rank, ∀ j : Fin P.rank, i.val = j.val →
      Q.step i = a j * P.step j)
    (hside : ∀ i : Fin Q.rank, ∀ j : Fin P.rank, i.val = j.val →
      P.length j < C * (Q.length i + 1)) :
    P.carrier.card ≤ (C * B) ^ P.rank * Q.carrier.card := by
  have h := P.positiveForm.card_le_of_positive_multipliers Q.positiveForm hrank
    (fun i => (a i).natAbs) C B
    (fun i => ⟨Int.natAbs_pos.mpr (ha i).1, by
      have hb : ((a i).natAbs : ℤ) ≤ (B : ℤ) := by
        simpa only [Int.natCast_natAbs] using (ha i).2
      exact_mod_cast hb⟩)
    (fun i j hij => by
      change |Q.step i| = ((a j).natAbs : ℤ) * |P.step j|
      rw [hstep i j hij, abs_mul, Int.natCast_natAbs]) hside
  simpa only [carrier_positiveForm, rank_positiveForm] using h

/-- Once a noncollapsed proper subprogression has bounded coordinate
multipliers, the same covering estimate applies to arbitrary dilations,
including dilations which are no longer proper. -/
theorem card_dilate_le_of_bounded_multipliers
    (P Q : GeneralizedAP) (hrank : Q.rank = P.rank)
    (hQ : Q.Proper) (hpos : ∀ i, 0 < Q.length i) (B C m n : ℕ)
    (hstep : Q.StepMultipliersBoundedByConstant P B)
    (hside : ∀ i : Fin Q.rank, ∀ j : Fin P.rank, i.val = j.val →
      m * P.length j < C * (n * Q.length i + 1)) :
    (P.dilate m).carrier.card ≤ (C * B) ^ P.rank * (Q.dilate n).carrier.card := by
  classical
  have hmult : ∀ j : Fin P.rank, ∃ a : ℤ, a ≠ 0 ∧ |a| ≤ (B : ℤ) ∧
      Q.step (Fin.cast hrank.symm j) = a * P.step j := by
    intro j
    obtain ⟨a, ha, habs⟩ := hstep (Fin.cast hrank.symm j) j rfl
    refine ⟨a, ?_, habs, ha⟩
    intro haz
    apply Q.step_ne_zero_of_proper_length_pos hQ (hpos (Fin.cast hrank.symm j))
    simp only [ha, haz, zero_mul]
  choose a hane habs haeq using hmult
  apply (P.dilate m).card_le_of_integer_multipliers (Q.dilate n) hrank a C B
    (fun i => ⟨hane i, habs i⟩) ?_ hside
  intro i j hij
  change Q.step i = a j * P.step j
  have heq : Fin.cast hrank.symm j = i := Fin.ext hij.symm
  simpa only [heq] using haeq j

end Erdos587.GeneralizedAP
