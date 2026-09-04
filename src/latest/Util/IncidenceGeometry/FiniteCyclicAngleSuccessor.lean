import Mathlib.Tactic
import Mathlib.Algebra.Group.Fin.Basic
import Util.IncidenceGeometry.Basic

open Classical
open scoped Fin.NatCast
noncomputable section

lemma FiniteCyclicAngleSuccessor {ι : Type*} [Fintype ι] [Nonempty ι]
    [DecidableEq ι]
    (θ : ι → ℝ)
    (hθ_mem : ∀ i : ι, 0 ≤ θ i ∧ θ i < 2 * Real.pi)
    (hθ_inj : Function.Injective θ) :
    ∃ clockwiseNext : Equiv.Perm ι,
      ∃ clockwiseTurn : ι → ι → ℝ,
        (∀ i j : ι,
          clockwiseTurn i j =
            if j = i then 2 * Real.pi
            else if θ j < θ i then θ i - θ j
            else θ i - θ j + 2 * Real.pi) ∧
        (∀ i j : ι, 0 < clockwiseTurn i j) ∧
        (∀ i j : ι, clockwiseTurn i j ≤ 2 * Real.pi) ∧
        (∀ i j : ι, clockwiseTurn i j = 2 * Real.pi ↔ j = i) ∧
        (∀ i j : ι, j ≠ i →
          clockwiseTurn i (clockwiseNext i) ≤ clockwiseTurn i j) ∧
        (∀ i j : ι, j ≠ i → j ≠ clockwiseNext i →
          clockwiseTurn i (clockwiseNext i) < clockwiseTurn i j) ∧
        (∀ i : ι, clockwiseNext i = i ↔ ∀ j : ι, j = i) ∧
        (∀ i : ι, ∀ α : ℝ,
          0 ≤ α → α < 2 * Real.pi →
            0 <
              (if α = θ i then 2 * Real.pi
               else if α < θ i then θ i - α
               else θ i - α + 2 * Real.pi) →
            (if α = θ i then 2 * Real.pi
             else if α < θ i then θ i - α
             else θ i - α + 2 * Real.pi) <
              clockwiseTurn i (clockwiseNext i) →
            ∀ j : ι, θ j ≠ α) ∧
        (∀ α : ℝ,
          0 ≤ α → α < 2 * Real.pi →
            (∀ j : ι, θ j ≠ α) →
              ∃ i : ι,
                0 <
                  (if α = θ i then 2 * Real.pi
                   else if α < θ i then θ i - α
                   else θ i - α + 2 * Real.pi) ∧
                (if α = θ i then 2 * Real.pi
                 else if α < θ i then θ i - α
                 else θ i - α + 2 * Real.pi) <
                  clockwiseTurn i (clockwiseNext i)) := by
  let n := Fintype.card ι
  have hnpos : 0 < n := Fintype.card_pos_iff.mpr inferInstance
  have : NeZero n := ⟨Nat.ne_of_gt hnpos⟩
  let : LinearOrder ι := LinearOrder.lift' (fun i => -θ i) (by
    intro a b h
    apply hθ_inj
    linarith)
  let e : Fin n ≃o ι := Fintype.orderIsoFinOfCardEq ι rfl
  let shift : Equiv.Perm (Fin n) :=
    { toFun := fun i => i + 1
      invFun := fun i => i - 1
      left_inv := by intro i; simp
      right_inv := by intro i; simp }
  let clockwiseNext : Equiv.Perm ι :=
    (e.symm : ι ≃ Fin n).trans (shift.trans (e : Fin n ≃ ι))
  let clockwiseTurn : ι → ι → ℝ := fun i j =>
    if j = i then 2 * Real.pi
    else if θ j < θ i then θ i - θ j
    else θ i - θ j + 2 * Real.pi
  have hturn_def : ∀ i j : ι,
      clockwiseTurn i j =
        if j = i then 2 * Real.pi
        else if θ j < θ i then θ i - θ j
        else θ i - θ j + 2 * Real.pi := by
    intro i j
    rfl
  have hneg_strict : StrictMono (fun k : Fin n => -θ (e k)) := by
    intro i j hij
    change -θ (e i) < -θ (e j)
    exact e.strictMono hij
  have hneg_mono : Monotone (fun k : Fin n => -θ (e k)) := hneg_strict.monotone
  have hθ_desc_lt : ∀ {i j : Fin n}, i < j → θ (e j) < θ (e i) := by
    intro i j hij
    have h := hneg_strict hij
    linarith
  have hθ_desc_le : ∀ {i j : Fin n}, i ≤ j → θ (e j) ≤ θ (e i) := by
    intro i j hij
    have h := hneg_mono hij
    linarith
  have hshift_apply : ∀ i : Fin n, shift i = i + 1 := by
    intro i
    rfl
  have hshift_fixed_all {a : Fin n} (ha : shift a = a) :
      ∀ b : Fin n, b = a := by
    have hone_zero : (1 : Fin n) = 0 := by
      apply add_left_cancel (a := a)
      calc
        a + 1 = a := by simpa [hshift_apply] using ha
        _ = a + 0 := by simp
    have hdiv : n ∣ 1 := by
      simpa using (Fin.natCast_eq_zero (a := 1) (n := n)).mp hone_zero
    have hnle : n ≤ 1 := Nat.le_of_dvd (by norm_num) hdiv
    intro b
    ext
    omega
  have hnext_fixed_all {i : ι} (hi : clockwiseNext i = i) :
      ∀ j : ι, j = i := by
    intro j
    apply e.symm.injective
    dsimp [clockwiseNext] at hi
    have hidx : shift (e.symm i) = e.symm i := by
      exact e.injective (by simpa [Equiv.trans_apply] using hi)
    exact hshift_fixed_all hidx (e.symm j)
  have hturn_pos : ∀ i j : ι, 0 < clockwiseTurn i j := by
    intro i j
    dsimp [clockwiseTurn]
    split_ifs with hji hlt
    · linarith [Real.pi_pos]
    · linarith
    · have hij_ne : θ j ≠ θ i := by
        intro hθ
        exact hji (hθ_inj hθ)
      have hgt : θ i < θ j := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hij_ne)
      linarith [hθ_mem i, hθ_mem j, Real.pi_pos]
  have hturn_le : ∀ i j : ι, clockwiseTurn i j ≤ 2 * Real.pi := by
    intro i j
    dsimp [clockwiseTurn]
    split_ifs with hji hlt
    · rfl
    · linarith [hθ_mem i, hθ_mem j]
    · have hle : θ i ≤ θ j := le_of_not_gt hlt
      linarith [hθ_mem i, hθ_mem j]
  have hturn_full : ∀ i j : ι, clockwiseTurn i j = 2 * Real.pi ↔ j = i := by
    intro i j
    dsimp [clockwiseTurn]
    constructor
    · intro h
      split_ifs at h with hji hlt
      · exact hji
      · have hltT : θ i - θ j < 2 * Real.pi := by
          linarith [hθ_mem i, hθ_mem j]
        linarith
      · have hle : θ i ≤ θ j := le_of_not_gt hlt
        have hθeq : θ i = θ j := by linarith
        exact hθ_inj hθeq.symm
    · intro h
      simp [h]
  have hshift_val_of_ne_zero :
      ∀ i : Fin n, shift i ≠ 0 → (shift i).val = i.val + 1 := by
    intro i hne
    have hne' : i + 1 ≠ 0 := by simpa [hshift_apply] using hne
    have hlt : i.val + 1 < n := by
      by_contra hnot
      have hle : i.val + 1 ≤ n := Nat.succ_le_of_lt i.isLt
      have heq : i.val + 1 = n := le_antisymm hle (le_of_not_gt hnot)
      have hzero : i + 1 = 0 := by
        have hone : ((1 : Fin n) : ℕ) = 1 := by
          change 1 % n = 1
          exact Nat.mod_eq_of_lt (by omega)
        ext
        rw [Fin.val_add_eq_ite]
        rw [hone, heq]
        simp
      exact hne' hzero
    simpa [hshift_apply] using Fin.val_add_one_of_lt' hlt
  have hshift_lt_of_ne_zero : ∀ i : Fin n, shift i ≠ 0 → i < shift i := by
    intro i hne
    rw [Fin.lt_def, hshift_val_of_ne_zero i hne]
    omega
  have hshift_le_of_lt :
      ∀ {i j : Fin n}, shift i ≠ 0 → i < j → shift i ≤ j := by
    intro i j hne hij
    rw [Fin.le_def, hshift_val_of_ne_zero i hne]
    exact Nat.succ_le_of_lt (Fin.lt_def.mp hij)
  have hwrap_max : ∀ {i j : Fin n}, shift i = 0 → j ≤ i := by
    intro i j hwrap
    refine le_of_not_gt ?_
    intro hij
    have hlt : i.val + 1 < n := by
      have hijv : i.val < j.val := Fin.lt_def.mp hij
      omega
    have hval : ((i + 1 : Fin n) : ℕ) = i.val + 1 :=
      Fin.val_add_one_of_lt' hlt
    have hzero : ((i + 1 : Fin n) : ℕ) = 0 := by
      simpa [hshift_apply] using congrArg Fin.val hwrap
    omega
  have hminimal_le : ∀ i j : ι, j ≠ i →
      clockwiseTurn i (clockwiseNext i) ≤ clockwiseTurn i j := by
    intro i j hji
    let a : Fin n := e.symm i
    let b : Fin n := e.symm j
    have hia : e a = i := by simp [a]
    have hjb : e b = j := by simp [b]
    have hba_ne : b ≠ a := by
      intro hba
      apply hji
      calc
        j = e b := by simp [b]
        _ = e a := by rw [hba]
        _ = i := by simp [a]
    have hnext_eq : clockwiseNext i = e (shift a) := by
      simp [clockwiseNext, a]
    have hnext_ne : clockwiseNext i ≠ i := by
      intro hfix
      exact hji (hnext_fixed_all hfix j)
    by_cases hwrap : shift a = 0
    · have hb_le_a : b ≤ a := hwrap_max hwrap
      have hb_lt_a : b < a := lt_of_le_of_ne hb_le_a hba_ne
      have hθ_ba : θ (e a) < θ (e b) := hθ_desc_lt hb_lt_a
      have hθ_0b : θ (e b) ≤ θ (e 0) := hθ_desc_le (Fin.zero_le b)
      have hturn_next :
          clockwiseTurn i (clockwiseNext i) =
            θ (e a) - θ (e 0) + 2 * Real.pi := by
        rw [hnext_eq, ← hia]
        have hne_e : e (shift a) ≠ e a := by
          intro h
          exact hnext_ne (by rw [hnext_eq, ← hia]; exact h)
        have hzero_ne_a : (0 : Fin n) ≠ a := by
          intro h0a
          exact hne_e (by rw [hwrap, h0a])
        have hnot : ¬ θ (e 0) < θ (e a) := by linarith
        simp [clockwiseTurn, hwrap, hzero_ne_a, hnot]
      have hturn_j :
          clockwiseTurn i j =
            θ (e a) - θ (e b) + 2 * Real.pi := by
        have hnot : ¬ θ (e b) < θ (e a) := by linarith
        rw [← hia, ← hjb]
        have hne_e : e b ≠ e a := fun h => hba_ne (e.injective h)
        simp [clockwiseTurn, hne_e, hnot]
      rw [hturn_next, hturn_j]
      linarith
    · have ha_lt_shift : a < shift a := hshift_lt_of_ne_zero a hwrap
      have hθ_shift_a : θ (e (shift a)) < θ (e a) := hθ_desc_lt ha_lt_shift
      have hturn_next :
          clockwiseTurn i (clockwiseNext i) =
            θ (e a) - θ (e (shift a)) := by
        rw [hnext_eq, ← hia]
        have hne_e : e (shift a) ≠ e a := by
          intro h
          exact hnext_ne (by rw [hnext_eq, ← hia]; exact h)
        have hlt : θ (e (shift a)) < θ (e a) := hθ_shift_a
        simp [clockwiseTurn, hne_e, hlt]
      by_cases hab : a < b
      · have hshift_le_b : shift a ≤ b := hshift_le_of_lt hwrap hab
        have hθ_b_shift : θ (e b) ≤ θ (e (shift a)) := hθ_desc_le hshift_le_b
        have hθ_ba : θ (e b) < θ (e a) := hθ_desc_lt hab
        have hturn_j :
            clockwiseTurn i j = θ (e a) - θ (e b) := by
          rw [← hia, ← hjb]
          have hne_e : e b ≠ e a := fun h => hba_ne (e.injective h)
          simp [clockwiseTurn, hne_e, hθ_ba]
        rw [hturn_next, hturn_j]
        linarith
      · have hb_lt_a : b < a := lt_of_le_of_ne (le_of_not_gt hab) hba_ne
        have hθ_ab : θ (e a) < θ (e b) := hθ_desc_lt hb_lt_a
        have hθ_shift_nonneg : 0 ≤ θ (e (shift a)) := (hθ_mem (e (shift a))).1
        have hθ_b_lt_two : θ (e b) < 2 * Real.pi := (hθ_mem (e b)).2
        have hturn_j :
            clockwiseTurn i j =
              θ (e a) - θ (e b) + 2 * Real.pi := by
          have hnot : ¬ θ (e b) < θ (e a) := by linarith
          rw [← hia, ← hjb]
          have hne_e : e b ≠ e a := fun h => hba_ne (e.injective h)
          simp [clockwiseTurn, hne_e, hnot]
        rw [hturn_next, hturn_j]
        linarith
  have hminimal_lt : ∀ i j : ι, j ≠ i → j ≠ clockwiseNext i →
      clockwiseTurn i (clockwiseNext i) < clockwiseTurn i j := by
    intro i j hji hjnext
    let a : Fin n := e.symm i
    let b : Fin n := e.symm j
    have hia : e a = i := by simp [a]
    have hjb : e b = j := by simp [b]
    have hba_ne : b ≠ a := by
      intro hba
      apply hji
      calc
        j = e b := by simp [b]
        _ = e a := by rw [hba]
        _ = i := by simp [a]
    have hnext_eq : clockwiseNext i = e (shift a) := by
      simp [clockwiseNext, a]
    have hb_ne_shift : b ≠ shift a := by
      intro hb
      apply hjnext
      calc
        j = e b := by simp [b]
        _ = e (shift a) := by rw [hb]
        _ = clockwiseNext i := hnext_eq.symm
    have hnext_ne : clockwiseNext i ≠ i := by
      intro hfix
      exact hji (hnext_fixed_all hfix j)
    by_cases hwrap : shift a = 0
    · have hb_le_a : b ≤ a := hwrap_max hwrap
      have hb_lt_a : b < a := lt_of_le_of_ne hb_le_a hba_ne
      have hzero_lt_b : (0 : Fin n) < b := lt_of_le_of_ne (Fin.zero_le b) (by
        intro hb0
        exact hb_ne_shift (by simp [hwrap, hb0]))
      have hθ_ba : θ (e a) < θ (e b) := hθ_desc_lt hb_lt_a
      have hθ_b0 : θ (e b) < θ (e 0) := hθ_desc_lt hzero_lt_b
      have hturn_next :
          clockwiseTurn i (clockwiseNext i) =
            θ (e a) - θ (e 0) + 2 * Real.pi := by
        rw [hnext_eq, ← hia]
        have hne_e : e (shift a) ≠ e a := by
          intro h
          exact hnext_ne (by rw [hnext_eq, ← hia]; exact h)
        have hzero_ne_a : (0 : Fin n) ≠ a := by
          intro h0a
          exact hne_e (by rw [hwrap, h0a])
        have hnot : ¬ θ (e 0) < θ (e a) := by linarith
        simp [clockwiseTurn, hwrap, hzero_ne_a, hnot]
      have hturn_j :
          clockwiseTurn i j =
            θ (e a) - θ (e b) + 2 * Real.pi := by
        have hnot : ¬ θ (e b) < θ (e a) := by linarith
        rw [← hia, ← hjb]
        have hne_e : e b ≠ e a := fun h => hba_ne (e.injective h)
        simp [clockwiseTurn, hne_e, hnot]
      rw [hturn_next, hturn_j]
      linarith
    · have ha_lt_shift : a < shift a := hshift_lt_of_ne_zero a hwrap
      have hθ_shift_a : θ (e (shift a)) < θ (e a) := hθ_desc_lt ha_lt_shift
      have hturn_next :
          clockwiseTurn i (clockwiseNext i) =
            θ (e a) - θ (e (shift a)) := by
        rw [hnext_eq, ← hia]
        have hne_e : e (shift a) ≠ e a := by
          intro h
          exact hnext_ne (by rw [hnext_eq, ← hia]; exact h)
        simp [clockwiseTurn, hne_e, hθ_shift_a]
      by_cases hab : a < b
      · have hshift_le_b : shift a ≤ b := hshift_le_of_lt hwrap hab
        have hshift_lt_b : shift a < b :=
          lt_of_le_of_ne hshift_le_b (Ne.symm hb_ne_shift)
        have hθ_b_shift : θ (e b) < θ (e (shift a)) := hθ_desc_lt hshift_lt_b
        have hθ_ba : θ (e b) < θ (e a) := hθ_desc_lt hab
        have hturn_j :
            clockwiseTurn i j = θ (e a) - θ (e b) := by
          rw [← hia, ← hjb]
          have hne_e : e b ≠ e a := fun h => hba_ne (e.injective h)
          simp [clockwiseTurn, hne_e, hθ_ba]
        rw [hturn_next, hturn_j]
        linarith
      · have hb_lt_a : b < a := lt_of_le_of_ne (le_of_not_gt hab) hba_ne
        have hθ_ab : θ (e a) < θ (e b) := hθ_desc_lt hb_lt_a
        have hθ_shift_nonneg : 0 ≤ θ (e (shift a)) := (hθ_mem (e (shift a))).1
        have hθ_b_lt_two : θ (e b) < 2 * Real.pi := (hθ_mem (e b)).2
        have hturn_j :
            clockwiseTurn i j =
              θ (e a) - θ (e b) + 2 * Real.pi := by
          have hnot : ¬ θ (e b) < θ (e a) := by linarith
          rw [← hia, ← hjb]
          have hne_e : e b ≠ e a := fun h => hba_ne (e.injective h)
          simp [clockwiseTurn, hne_e, hnot]
        rw [hturn_next, hturn_j]
        linarith
  have hfixed : ∀ i : ι, clockwiseNext i = i ↔ ∀ j : ι, j = i := by
    intro i
    constructor
    · intro hi
      exact hnext_fixed_all hi
    · intro hall
      exact hall (clockwiseNext i)
  have hgap_empty : ∀ i : ι, ∀ α : ℝ,
      0 ≤ α → α < 2 * Real.pi →
        0 <
          (if α = θ i then 2 * Real.pi
           else if α < θ i then θ i - α
           else θ i - α + 2 * Real.pi) →
        (if α = θ i then 2 * Real.pi
         else if α < θ i then θ i - α
         else θ i - α + 2 * Real.pi) <
          clockwiseTurn i (clockwiseNext i) →
        ∀ j : ι, θ j ≠ α := by
    intro i α hα0 hα2 hτpos hτlt j hja
    by_cases hji : j = i
    · subst j
      have hτeq :
          (if α = θ i then 2 * Real.pi
           else if α < θ i then θ i - α
           else θ i - α + 2 * Real.pi) = 2 * Real.pi := by
        simp [hja]
      have hle := hturn_le i (clockwiseNext i)
      linarith
    · have hturnj_eq :
          clockwiseTurn i j =
            (if α = θ i then 2 * Real.pi
             else if α < θ i then θ i - α
             else θ i - α + 2 * Real.pi) := by
        dsimp [clockwiseTurn]
        have hα_ne_i : α ≠ θ i := by
          intro hαi
          exact hji (hθ_inj (by rw [hja, hαi]))
        simp [hji, hja, hα_ne_i]
      have hle := hminimal_le i j hji
      linarith
  -- Cover is proved below by choosing the last sorted angle above `α`, or
  -- the last angle in the cyclic order if no angle is above `α`.
  have hgap_cover : ∀ α : ℝ,
      0 ≤ α → α < 2 * Real.pi →
        (∀ j : ι, θ j ≠ α) →
          ∃ i : ι,
            0 <
              (if α = θ i then 2 * Real.pi
               else if α < θ i then θ i - α
               else θ i - α + 2 * Real.pi) ∧
            (if α = θ i then 2 * Real.pi
             else if α < θ i then θ i - α
             else θ i - α + 2 * Real.pi) <
              clockwiseTurn i (clockwiseNext i) := by
    intro α hα0 hα2 hα_not
    let above : Finset (Fin n) := Finset.univ.filter (fun k => α < θ (e k))
    by_cases habove : above.Nonempty
    · let k : Fin n := above.max' habove
      have hk_mem : k ∈ above := by
        exact above.max'_mem habove
      have hk_above : α < θ (e k) := by
        exact (Finset.mem_filter.mp hk_mem).2
      have hα_ne_k : α ≠ θ (e k) := by
        intro h
        exact hα_not (e k) h.symm
      have hnot_above_of_gt : ∀ {l : Fin n}, k < l → ¬ α < θ (e l) := by
        intro l hkl hl
        have hl_mem : l ∈ above := by
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ l, hl⟩
        have hl_le_k : l ≤ k := by
          simpa [k] using above.le_max' l hl_mem
        exact (not_lt_of_ge hl_le_k) hkl
      refine ⟨e k, ?_, ?_⟩
      · simp [hα_ne_k, hk_above]
      · have hτeq :
            (if α = θ (e k) then 2 * Real.pi
             else if α < θ (e k) then θ (e k) - α
             else θ (e k) - α + 2 * Real.pi) =
              θ (e k) - α := by
          simp [hα_ne_k, hk_above]
        by_cases hwrap : shift k = 0
        · have hnext_eq : clockwiseNext (e k) = e 0 := by
            simp [clockwiseNext, hwrap]
          by_cases hsame : e 0 = e k
          · have hturn_next :
                clockwiseTurn (e k) (clockwiseNext (e k)) = 2 * Real.pi := by
              simp [hnext_eq, hsame, clockwiseTurn]
            rw [hτeq, hturn_next]
            linarith [hθ_mem (e k)]
          · have hturn_next :
                clockwiseTurn (e k) (clockwiseNext (e k)) =
                  θ (e k) - θ (e 0) + 2 * Real.pi := by
              rw [hnext_eq]
              have hnotlt : ¬ θ (e 0) < θ (e k) := by
                have hle : θ (e k) ≤ θ (e 0) := hθ_desc_le (Fin.zero_le k)
                linarith
              simp [clockwiseTurn, hsame, hnotlt]
            rw [hτeq, hturn_next]
            linarith [hθ_mem (e 0), hα0]
        · have hk_lt_shift : k < shift k := hshift_lt_of_ne_zero k hwrap
          have hshift_not_above : ¬ α < θ (e (shift k)) :=
            hnot_above_of_gt hk_lt_shift
          have hθ_shift_le_alpha : θ (e (shift k)) ≤ α := le_of_not_gt hshift_not_above
          have hθ_shift_ne_alpha : θ (e (shift k)) ≠ α := hα_not (e (shift k))
          have hθ_shift_lt_alpha : θ (e (shift k)) < α :=
            lt_of_le_of_ne hθ_shift_le_alpha hθ_shift_ne_alpha
          have hθ_shift_k : θ (e (shift k)) < θ (e k) := hθ_desc_lt hk_lt_shift
          have hnext_eq : clockwiseNext (e k) = e (shift k) := by
            simp [clockwiseNext]
          have hturn_next :
              clockwiseTurn (e k) (clockwiseNext (e k)) =
                θ (e k) - θ (e (shift k)) := by
            rw [hnext_eq]
            have hne_e : e (shift k) ≠ e k := by
              intro h
              exact (ne_of_gt hk_lt_shift) (e.injective h)
            simp [clockwiseTurn, hne_e, hθ_shift_k]
          rw [hτeq, hturn_next]
          linarith
    · have hnot_above : ∀ k : Fin n, ¬ α < θ (e k) := by
        intro k hk
        apply habove
        exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ k, hk⟩⟩
      let k : Fin n := -1
      have hk_not_above : ¬ α < θ (e k) := hnot_above k
      have hθk_le_alpha : θ (e k) ≤ α := le_of_not_gt hk_not_above
      have hθk_ne_alpha : θ (e k) ≠ α := hα_not (e k)
      have hθk_lt_alpha : θ (e k) < α :=
        lt_of_le_of_ne hθk_le_alpha hθk_ne_alpha
      have hα_ne_k : α ≠ θ (e k) := by
        intro h
        exact hθk_ne_alpha h.symm
      have hshift_k : shift k = 0 := by
        simp [hshift_apply, k]
      refine ⟨e k, ?_, ?_⟩
      · simp [hα_ne_k, hk_not_above]
        linarith [hθ_mem (e k), hα2]
      · have hτeq :
            (if α = θ (e k) then 2 * Real.pi
             else if α < θ (e k) then θ (e k) - α
             else θ (e k) - α + 2 * Real.pi) =
              θ (e k) - α + 2 * Real.pi := by
          simp [hα_ne_k, hk_not_above]
        have hnext_eq : clockwiseNext (e k) = e 0 := by
          simp [clockwiseNext, hshift_k]
        by_cases hsame : e 0 = e k
        · have hturn_next :
              clockwiseTurn (e k) (clockwiseNext (e k)) = 2 * Real.pi := by
            simp [hnext_eq, hsame, clockwiseTurn]
          rw [hτeq, hturn_next]
          linarith
        · have hθ0_lt_alpha : θ (e 0) < α := by
            have h0_not_above : ¬ α < θ (e 0) := hnot_above 0
            have hθ0_le_alpha : θ (e 0) ≤ α := le_of_not_gt h0_not_above
            exact lt_of_le_of_ne hθ0_le_alpha (hα_not (e 0))
          have hturn_next :
              clockwiseTurn (e k) (clockwiseNext (e k)) =
                θ (e k) - θ (e 0) + 2 * Real.pi := by
            rw [hnext_eq]
            have hnotlt : ¬ θ (e 0) < θ (e k) := by
              have hle : θ (e k) ≤ θ (e 0) := hθ_desc_le (Fin.zero_le k)
              linarith
            simp [clockwiseTurn, hsame, hnotlt]
          rw [hτeq, hturn_next]
          linarith
  exact ⟨clockwiseNext, clockwiseTurn, hturn_def, hturn_pos, hturn_le, hturn_full,
    hminimal_le, hminimal_lt, hfixed, hgap_empty, hgap_cover⟩
