/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos984.Blocks

/-!
# Assembly of the infinite coloring for Erdős Problem 984

This file proves the elementary reduction from a subpolynomial family of
finite off-diagonal colorings to the required coloring of `ℕ`.
-/

namespace Erdos984

def blockLength (t : ℕ) : ℕ :=
  blockStart (t + 1) - blockStart t

lemma blockLength_pos (t : ℕ) : 0 < blockLength t := by
  unfold blockLength
  have hlt : blockStart t < blockStart (t + 1) := by
    simp [blockStart, blockBase, pow_succ]
  omega

lemma blockLength_le_of_blockStart_le {t a : ℕ}
    (hstart : blockStart t ≤ blockBase ^ 5 * a) :
    blockLength t ≤ blockBase ^ 6 * a := by
  have hlen : blockLength t ≤ blockStart (t + 1) := by
    unfold blockLength
    exact Nat.sub_le _ _
  calc
    blockLength t ≤ blockStart (t + 1) := hlen
    _ = blockBase * blockStart t := by
      simp [blockStart, pow_succ, Nat.mul_comm]
    _ ≤ blockBase * (blockBase ^ 5 * a) := Nat.mul_le_mul_left _ hstart
    _ = blockBase ^ 6 * a := by ring

def assembledColor (D : OffDiagonalData) (n : ℕ) : Bool :=
  let t := blockIndex n
  let c := D.coloring (blockLength t) (n - blockStart t)
  if t % 2 = 0 then c else !c

lemma apTerm_add_index (a d j i : ℕ) :
    apTerm a d (j + i) = apTerm a d j + i * d := by
  simp [apTerm, Nat.add_mul, Nat.add_assoc]

lemma apTerm_sub_blockStart {a d j i t : ℕ}
    (hj : InBlock t (apTerm a d j)) :
    apTerm a d (j + i) - blockStart t =
      (apTerm a d j - blockStart t) + i * d := by
  rw [apTerm_add_index]
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
    Nat.add_sub_assoc hj.1 (i * d)

lemma block_local_endpoint_lt {a d j r t : ℕ} (hr : 0 < r)
    (hrun : ∀ i < r, InBlock t (apTerm a d (j + i))) :
    (apTerm a d j - blockStart t) + (r - 1) * d < blockLength t := by
  have hlast := hrun (r - 1) (by omega)
  have hj := hrun 0 hr
  simp only [Nat.add_zero] at hj
  have heq := apTerm_sub_blockStart (i := r - 1) hj
  unfold blockLength
  rw [← heq]
  exact (Nat.sub_lt_sub_iff_right hlast.1).2 hlast.2

lemma assembledColor_on_block (D : OffDiagonalData) {t n : ℕ}
    (hn : 0 < n) (hblock : InBlock t n) :
    assembledColor D n =
      if t % 2 = 0 then
        D.coloring (blockLength t) (n - blockStart t)
      else
        Bool.not (D.coloring (blockLength t) (n - blockStart t)) := by
  have hindex : blockIndex n = t := (inBlock_iff_blockIndex_eq hn).1 hblock
  simp [assembledColor, hindex]

lemma localColor_eq_of_assembled (D : OffDiagonalData) {t n : ℕ}
    (hn : 0 < n) (hblock : InBlock t n) {b : Bool}
    (hcolor : assembledColor D n = b) :
    D.coloring (blockLength t) (n - blockStart t) =
      if t % 2 = 0 then b else !b := by
  rw [assembledColor_on_block D hn hblock] at hcolor
  by_cases hp : t % 2 = 0
  · simpa [hp] using hcolor
  · have hg : Bool.not (D.coloring (blockLength t) (n - blockStart t)) = b := by
      simpa [hp] using hcolor
    cases hlocal : D.coloring (blockLength t) (n - blockStart t) <;>
      cases b <;> simp_all

lemma localColor_on_block_run (D : OffDiagonalData) {a d k t j r : ℕ}
    {b : Bool} (ha : 0 < a)
    (hglobal : ∀ i < k, assembledColor D (apTerm a d i) = b)
    (hr : 0 < r) (hjr : j + r ≤ k)
    (hrun : ∀ i < r, InBlock t (apTerm a d (j + i))) :
    ∀ i < r,
      D.coloring (blockLength t)
          ((apTerm a d j - blockStart t) + i * d) =
        if t % 2 = 0 then b else !b := by
  intro i hi
  have hji : j + i < k := by omega
  have hblock := hrun i hi
  have htermpos : 0 < apTerm a d (j + i) := by
    dsimp [apTerm]
    omega
  have hlocal := localColor_eq_of_assembled D htermpos hblock (hglobal _ hji)
  have hjblock := hrun 0 hr
  simp only [Nat.add_zero] at hjblock
  rw [← apTerm_sub_blockStart (i := i) hjblock]
  exact hlocal

lemma false_three_run_impossible (D : OffDiagonalData) {a d k t j : ℕ}
    {b : Bool} (ha : 0 < a) (hd : 0 < d)
    (hglobal : ∀ i < k, assembledColor D (apTerm a d i) = b)
    (hjr : j + 3 ≤ k)
    (hrun : ∀ i < 3, InBlock t (apTerm a d (j + i)))
    (htarget : (if t % 2 = 0 then b else !b) = false) : False := by
  let x := apTerm a d j - blockStart t
  have hend : x + (3 - 1) * d < blockLength t :=
    block_local_endpoint_lt (by norm_num) hrun
  have hcolors := localColor_on_block_run D ha hglobal (by norm_num) hjr hrun
  exact (D.good (blockLength t)).1.not_mono hd hend (fun i hi => by
    simpa [x, htarget] using hcolors i hi)

lemma block_run_length_lt_H (D : OffDiagonalData) {a d k t j m : ℕ}
    {b : Bool} (ha : 0 < a) (hd : 0 < d)
    (hglobal : ∀ i < k, assembledColor D (apTerm a d i) = b)
    (hm : 0 < m) (hjm : j + m ≤ k)
    (hrun : ∀ i < m, InBlock t (apTerm a d (j + i))) :
    m < D.H (blockLength t) := by
  let localTarget : Bool := if t % 2 = 0 then b else !b
  have hcolors := localColor_on_block_run D ha hglobal hm hjm hrun
  cases htarget : localTarget with
  | false =>
      have hm3 : m < 3 := by
        by_contra hnot
        have hthree : 3 ≤ m := by omega
        let x := apTerm a d j - blockStart t
        have hend : x + (3 - 1) * d < blockLength t :=
          block_local_endpoint_lt (by norm_num) (fun i hi => hrun i (by omega))
        exact (D.good (blockLength t)).1.not_mono hd hend (fun i hi => by
          have hc := hcolors i (by omega)
          simpa [localTarget, htarget, x] using hc)
      exact lt_of_lt_of_le hm3 (D.three_le_H (blockLength t))
  | true =>
      by_contra hnot
      have hHle : D.H (blockLength t) ≤ m := by omega
      have hHpos : 0 < D.H (blockLength t) :=
        lt_of_lt_of_le (by norm_num) (D.three_le_H (blockLength t))
      let x := apTerm a d j - blockStart t
      have hend : x + (D.H (blockLength t) - 1) * d < blockLength t :=
        block_local_endpoint_lt hHpos (fun i hi => hrun i (lt_of_lt_of_le hi hHle))
      exact (D.good (blockLength t)).2.not_mono hd hend (fun i hi => by
        have hc := hcolors i (lt_of_lt_of_le hi hHle)
        simpa [localTarget, htarget, x] using hc)

/-- The geometric-block assembly: Hunter's finite off-diagonal input implies
the exact affirmative statement of Erdős Problem 984. -/
theorem erdos984_of_offDiagonal (D : OffDiagonalData) : Erdos984Statement := by
  refine ⟨assembledColor D, ?_⟩
  intro ε hε
  obtain ⟨B, hBpos, hB⟩ := D.subpower ε hε
  let C : ℝ := 12 * B * ((blockBase ^ 6 : ℕ) : ℝ) ^ ε
  let A : ℝ := (blockDichotomyThreshold : ℝ) + C
  have hCpos : 0 < C := by
    dsimp [C]
    have hbase : (0 : ℝ) < ((blockBase ^ 6 : ℕ) : ℝ) := by
      norm_num [blockBase]
    positivity
  have hApos : 0 < A := by
    dsimp [A]
    positivity
  refine ⟨A, hApos, ?_⟩
  intro a d k ha hd hmono
  obtain ⟨b, hb⟩ := hmono
  have ha_real : (1 : ℝ) ≤ (a : ℝ) := by
    exact_mod_cast ha
  have ha_pow : (1 : ℝ) ≤ (a : ℝ) ^ ε :=
    Real.one_le_rpow ha_real hε.le
  by_cases hklarge : blockDichotomyThreshold < k
  · rcases block_dichotomy ha hd hklarge with hparity | hconcentrated
    · obtain ⟨te, to_, heven, hodd, hre, hro⟩ := hparity
      rcases hre with ⟨je, hje, hrune⟩
      rcases hro with ⟨jo, hjo, hruno⟩
      cases b with
      | false =>
          exact False.elim (false_three_run_impossible D ha hd hb hje hrune (by
            simp [heven]))
      | true =>
          exact False.elim (false_three_run_impossible D ha hd hb hjo hruno (by
            simp [hodd]))
    · obtain ⟨t, hkcard, hstart⟩ := hconcentrated
      let m := (blockIndices a d k t).card
      have hmpos : 0 < m := by
        dsimp [m]
        have hkpos : 0 < k := by omega
        omega
      obtain ⟨j, hjm, hrun⟩ :=
        exists_block_run_of_le_card (a := a) (d := d) (k := k) (t := t)
          (m := m) (by rfl)
      have hmH : m < D.H (blockLength t) :=
        block_run_length_lt_H D ha hd hb hmpos hjm hrun
      have hLpos : 0 < blockLength t := blockLength_pos t
      have hHbound := hB (blockLength t) hLpos
      have hLnat : blockLength t ≤ blockBase ^ 6 * a :=
        blockLength_le_of_blockStart_le hstart
      have hLreal : ((blockLength t : ℕ) : ℝ) ≤
          (((blockBase ^ 6 : ℕ) : ℝ) * (a : ℝ)) := by
        exact_mod_cast hLnat
      have hLpow : ((blockLength t : ℕ) : ℝ) ^ ε ≤
          (((blockBase ^ 6 : ℕ) : ℝ) * (a : ℝ)) ^ ε :=
        Real.rpow_le_rpow (by positivity) hLreal hε.le
      have hkreal : (k : ℝ) ≤ 12 * (m : ℝ) := by
        exact_mod_cast hkcard
      have hmreal : (m : ℝ) ≤ (D.H (blockLength t) : ℝ) := by
        exact_mod_cast (Nat.le_of_lt hmH)
      have hmain : (k : ℝ) ≤ C * (a : ℝ) ^ ε := by
        calc
          (k : ℝ) ≤ 12 * (m : ℝ) := hkreal
          _ ≤ 12 * (D.H (blockLength t) : ℝ) :=
            mul_le_mul_of_nonneg_left hmreal (by norm_num)
          _ ≤ 12 * (B * ((blockLength t : ℕ) : ℝ) ^ ε) := by
            gcongr
          _ ≤ 12 * (B * ((((blockBase ^ 6 : ℕ) : ℝ) * (a : ℝ)) ^ ε)) := by
            gcongr
          _ = C * (a : ℝ) ^ ε := by
            rw [Real.mul_rpow (by positivity) (by positivity)]
            simp [C]
            ring
      exact le_trans hmain (mul_le_mul_of_nonneg_right (by
        dsimp [A]
        exact le_add_of_nonneg_left (by positivity)) (by positivity))
  · have hkbound : k ≤ blockDichotomyThreshold := by omega
    have hkreal : (k : ℝ) ≤ (blockDichotomyThreshold : ℝ) := by
      exact_mod_cast hkbound
    have hthresholdA : (blockDichotomyThreshold : ℝ) ≤ A := by
      dsimp [A]
      exact le_add_of_nonneg_right hCpos.le
    exact le_trans (le_trans hkreal hthresholdA)
      (le_mul_of_one_le_right hApos.le ha_pow)

end Erdos984
