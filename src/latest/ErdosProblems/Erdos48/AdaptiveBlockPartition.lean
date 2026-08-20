/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.AdaptiveNegativeHybrid
import ErdosProblems.Erdos48.DetectorShellAggregation

/-!
# A globally separated adaptive block partition

The block denominator is the least power of two above `T+1`.  Consequently
every dyadic shell length is an integral multiple of its block length and
the grids on adjacent shells meet without a short boundary gap.
-/

namespace Erdos48

open scoped BigOperators

noncomputable section

/-- Least dyadic denominator above the vertical length. -/
def adaptiveBlockDenominator (T : ℕ) : ℕ :=
  2 ^ Nat.clog 2 (T + 1)

/-- Block length in the dyadic shell `(2^a,2^(a+1)]`. -/
def adaptiveShellBlockLength (T a : ℕ) : ℕ :=
  2 ^ (a - Nat.clog 2 (T + 1))

theorem adaptiveBlockDenominator_pos (T : ℕ) :
    0 < adaptiveBlockDenominator T := by
  unfold adaptiveBlockDenominator
  positivity

theorem vertical_le_adaptiveBlockDenominator (T : ℕ) :
    T + 1 ≤ adaptiveBlockDenominator T := by
  unfold adaptiveBlockDenominator
  exact Nat.le_pow_clog (by omega) (T + 1)

theorem adaptiveBlockDenominator_le_twice_vertical (T : ℕ) :
    adaptiveBlockDenominator T ≤ 2 * (T + 1) := by
  let d := Nat.clog 2 (T + 1)
  by_cases hT : T = 0
  · subst T
    norm_num [adaptiveBlockDenominator]
  · have hd : 0 < d := by
      dsimp [d]
      exact Nat.clog_pos (by omega) (by omega)
    have hpred : 2 ^ d.pred < T + 1 := by
      dsimp [d]
      exact Nat.pow_pred_clog_lt_self (by omega) (by omega)
    have hsucc : d.pred + 1 = d := Nat.succ_pred_eq_of_pos hd
    unfold adaptiveBlockDenominator
    change 2 ^ d ≤ 2 * (T + 1)
    rw [← hsucc, pow_succ]
    omega

theorem adaptiveShellBlockLength_mul_denominator
    {T a : ℕ} (hden : adaptiveBlockDenominator T ≤ 2 ^ a) :
    adaptiveShellBlockLength T a * adaptiveBlockDenominator T = 2 ^ a := by
  let d := Nat.clog 2 (T + 1)
  have hda : d ≤ a := by
    apply (Nat.clog_le_iff_le_pow (by omega)).2
    exact (vertical_le_adaptiveBlockDenominator T).trans hden
  unfold adaptiveShellBlockLength adaptiveBlockDenominator
  simpa only [d] using pow_sub_mul_pow 2 hda

theorem adaptiveShellBlockLength_pos (T a : ℕ) :
    0 < adaptiveShellBlockLength T a := by
  unfold adaptiveShellBlockLength
  positivity

/-- The finite type of all nonempty adaptive blocks in all active dyadic
shells of `(Y,N]`. -/
abbrev adaptiveDetectorBlocks (Y N T : ℕ) :=
  Σ a : {a // a ∈ detectorActiveShells Y N},
    {i // i ∈ shortBlockIndices (detectorDyadicShell Y N a.1)
      (2 ^ a.1) (adaptiveShellBlockLength T a.1)}

noncomputable def adaptiveDetectorBlock
    (Y N T : ℕ) (z : adaptiveDetectorBlocks Y N T) : Finset ℕ :=
  shortBlock (detectorDyadicShell Y N z.1.1) (2 ^ z.1.1)
    (adaptiveShellBlockLength T z.1.1) z.2

def adaptiveDetectorBlockStart
    (Y N T : ℕ) (z : adaptiveDetectorBlocks Y N T) : ℕ :=
  shortBlockStart (2 ^ z.1.1) (adaptiveShellBlockLength T z.1.1) z.2

noncomputable def adaptiveDetectorBlockCenter
    (Y N T : ℕ) (z : adaptiveDetectorBlocks Y N T) : ℝ :=
  shortBlockCenter (2 ^ z.1.1) (adaptiveShellBlockLength T z.1.1) z.2

def adaptiveDetectorBlockLength
    (Y N T : ℕ) (z : adaptiveDetectorBlocks Y N T) : ℕ :=
  adaptiveShellBlockLength T z.1.1

theorem adaptiveDetectorBlock_subset_Ioc
    {Y N T : ℕ} (hY : 1 ≤ Y) (z : adaptiveDetectorBlocks Y N T) :
    adaptiveDetectorBlock Y N T z ⊆
      Finset.Ioc (adaptiveDetectorBlockStart Y N T z)
        (adaptiveDetectorBlockStart Y N T z +
          adaptiveDetectorBlockLength Y N T z) := by
  exact shortBlock_subset_Ioc _ _ _
    (adaptiveShellBlockLength_pos T z.1.1)
    (detectorDyadicShell_subset Y N z.1.1 hY) z.2

theorem adaptiveDetectorBlock_pairwise_disjoint
    (Y N T : ℕ) :
    ∀ z w : adaptiveDetectorBlocks Y N T, z ≠ w →
      Disjoint (adaptiveDetectorBlock Y N T z)
        (adaptiveDetectorBlock Y N T w) := by
  rintro ⟨a, i⟩ ⟨b, j⟩ hzw
  by_cases ha : a = b
  · subst b
    have hi : i ≠ j := by
      intro hi
      subst j
      exact hzw rfl
    exact pairwiseDisjoint_shortBlock
      (detectorDyadicShell Y N a.1) (2 ^ a.1)
      (adaptiveShellBlockLength T a.1)
      (Finset.mem_univ i) (Finset.mem_univ j) hi
  · have hab : a.1 ≠ b.1 := by
      intro hab
      apply ha
      exact Subtype.ext hab
    apply Finset.disjoint_of_subset_left (Finset.filter_subset _ _)
    apply Finset.disjoint_of_subset_right (Finset.filter_subset _ _)
    exact disjoint_detectorDyadicShell_of_ne Y N hab

theorem biUnion_adaptiveDetectorBlock (Y N T : ℕ) :
    (Finset.univ : Finset (adaptiveDetectorBlocks Y N T)).biUnion
        (adaptiveDetectorBlock Y N T) = Finset.Ioc Y N := by
  classical
  ext n
  constructor
  · intro hn
    rw [Finset.mem_biUnion] at hn
    obtain ⟨z, hz, hnz⟩ := hn
    have hnshell : n ∈ detectorDyadicShell Y N z.1.1 :=
      (Finset.mem_filter.mp hnz).1
    exact (Finset.mem_filter.mp hnshell).1
  · intro hn
    have hshell : n ∈
        (detectorActiveShells Y N).biUnion (detectorDyadicShell Y N) := by
      rw [biUnion_detectorActiveShells]
      exact hn
    rw [Finset.mem_biUnion] at hshell
    obtain ⟨a, ha, hna⟩ := hshell
    have hblocks : n ∈
        (Finset.univ : Finset
          {i // i ∈ shortBlockIndices (detectorDyadicShell Y N a)
            (2 ^ a) (adaptiveShellBlockLength T a)}).biUnion
          (shortBlock (detectorDyadicShell Y N a) (2 ^ a)
            (adaptiveShellBlockLength T a)) := by
      rw [biUnion_shortBlock]
      exact hna
    rw [Finset.mem_biUnion] at hblocks ⊢
    obtain ⟨i, hi, hni⟩ := hblocks
    exact ⟨⟨⟨a, ha⟩, i⟩, Finset.mem_univ _, hni⟩

private theorem log_sub_log_lower_adaptive {x y : ℝ}
    (hx : 0 < x) (hxy : x ≤ y) :
    (y - x) / y ≤ Real.log y - Real.log x := by
  have hy : 0 < y := hx.trans_le hxy
  have h := Real.one_sub_inv_le_log_of_pos (div_pos hy hx)
  calc
    (y - x) / y = 1 - (y / x)⁻¹ := by field_simp
    _ ≤ Real.log (y / x) := h
    _ = Real.log y - Real.log x := Real.log_div hy.ne' hx.ne'

private theorem adaptive_center_nat_bounds
    {Y N T a : ℕ} (hY : 1 ≤ Y)
    (hden : adaptiveBlockDenominator T ≤ 2 ^ a)
    (i : {i // i ∈ shortBlockIndices (detectorDyadicShell Y N a)
      (2 ^ a) (adaptiveShellBlockLength T a)}) :
    2 ^ a + 1 ≤
        2 ^ a + i.1 * adaptiveShellBlockLength T a + 1 ∧
      2 ^ a + i.1 * adaptiveShellBlockLength T a + 1 +
          adaptiveShellBlockLength T a ≤ 2 * 2 ^ a + 1 := by
  let A := 2 ^ a
  let H := adaptiveShellBlockLength T a
  let P := adaptiveBlockDenominator T
  have hH : 0 < H := by dsimp [H]; exact adaptiveShellBlockLength_pos T a
  have hAeq : H * P = A := by
    simpa only [A, H, P] using
      adaptiveShellBlockLength_mul_denominator hden
  obtain ⟨n, hn, hni⟩ := Finset.mem_image.mp i.2
  have hnBounds := Finset.mem_Ioc.mp
    (detectorDyadicShell_subset Y N a hY hn)
  have hquot : (n - A - 1) / H = i.1 := by
    simpa only [A, H] using hni
  have hmul := Nat.div_mul_le_self (n - A - 1) H
  rw [hquot] at hmul
  have hiH : i.1 * H ≤ A - 1 := by omega
  have hiP : i.1 + 1 ≤ P := by
    by_contra hnot
    have hPi : P ≤ i.1 := by omega
    have hAP : A ≤ i.1 * H := by
      calc
        A = H * P := hAeq.symm
        _ ≤ H * i.1 := Nat.mul_le_mul_left H hPi
        _ = i.1 * H := Nat.mul_comm _ _
    omega
  constructor
  · omega
  · have hmul' := Nat.mul_le_mul_left H hiP
    rw [Nat.mul_add, Nat.mul_one] at hmul'
    have hright : i.1 * H + H ≤ A := by
      calc
        i.1 * H + H = H * i.1 + H := by rw [Nat.mul_comm i.1 H]
        _ ≤ H * P := hmul'
        _ = A := hAeq
    have hright' : i.1 * adaptiveShellBlockLength T a +
        adaptiveShellBlockLength T a ≤ 2 ^ a := by
      simpa only [A, H] using hright
    omega

theorem adaptiveDetectorBlockCenter_offset_le
    {Y N T : ℕ} (hY : 1 ≤ Y)
    (hden : ∀ a ∈ detectorActiveShells Y N,
      adaptiveBlockDenominator T ≤ 2 ^ a)
    (z : adaptiveDetectorBlocks Y N T) (n : ℕ)
    (hn : n ∈ adaptiveDetectorBlock Y N T z) :
    |Real.log n - adaptiveDetectorBlockCenter Y N T z| ≤
      (adaptiveBlockDenominator T : ℝ)⁻¹ := by
  have hratio :
      ((adaptiveShellBlockLength T z.1.1 : ℕ) : ℝ) /
          (2 ^ z.1.1 : ℕ) =
        (adaptiveBlockDenominator T : ℝ)⁻¹ := by
    have heq := adaptiveShellBlockLength_mul_denominator
      (hden z.1.1 z.1.2)
    have hP : (0 : ℝ) < adaptiveBlockDenominator T := by
      exact_mod_cast adaptiveBlockDenominator_pos T
    have hcast :
        ((adaptiveShellBlockLength T z.1.1 : ℕ) : ℝ) *
            (adaptiveBlockDenominator T : ℝ) =
          (2 ^ z.1.1 : ℕ) := by exact_mod_cast heq
    rw [inv_eq_one_div]
    apply (div_eq_div_iff (by positivity) hP.ne').2
    simpa only [one_mul] using hcast
  simpa only [adaptiveDetectorBlock, adaptiveDetectorBlockCenter, hratio] using
    shortBlock_log_offset_le
      (Nat.one_le_pow z.1.1 2 (by omega))
      (adaptiveShellBlockLength_pos T z.1.1)
      (detectorDyadicShell_subset Y N z.1.1 hY) z.2 n hn

/-- All adaptive block centres are separated at the reciprocal vertical
scale, including across dyadic-shell boundaries. -/
theorem adaptiveDetectorBlockCenter_separated
    {Y N T : ℕ} (hY : 1 ≤ Y)
    (hden : ∀ a ∈ detectorActiveShells Y N,
      adaptiveBlockDenominator T ≤ 2 ^ a) :
    ∀ z w : adaptiveDetectorBlocks Y N T, z ≠ w →
      (8 * (T + 1 : ℕ) : ℝ)⁻¹ ≤
        |adaptiveDetectorBlockCenter Y N T z -
          adaptiveDetectorBlockCenter Y N T w| := by
  rintro ⟨a, i⟩ ⟨b, j⟩ hzw
  let P : ℕ := adaptiveBlockDenominator T
  have hPpos : 0 < P := by dsimp [P]; exact adaptiveBlockDenominator_pos T
  have hPupper : P ≤ 2 * (T + 1) := by
    simpa only [P] using adaptiveBlockDenominator_le_twice_vertical T
  by_cases ha : a = b
  · subst b
    have hi : i ≠ j := by
      intro hi
      subst j
      exact hzw rfl
    have hlocal := shortBlockCenter_separated
      (Nat.one_le_pow a.1 2 (by omega))
      (adaptiveShellBlockLength_pos T a.1)
      (detectorDyadicShell_subset Y N a.1 hY) i j hi
    have hratio :
        ((adaptiveShellBlockLength T a.1 : ℕ) : ℝ) /
            (2 * 2 ^ a.1 : ℕ) = (2 * (P : ℝ))⁻¹ := by
      have heq := adaptiveShellBlockLength_mul_denominator
        (hden a.1 a.2)
      have hcast :
          ((adaptiveShellBlockLength T a.1 : ℕ) : ℝ) * P =
            (2 ^ a.1 : ℕ) := by exact_mod_cast heq
      have hPr : (0 : ℝ) < P := by exact_mod_cast hPpos
      rw [inv_eq_one_div]
      apply (div_eq_div_iff (by positivity) (by positivity)).2
      rw [Nat.cast_mul, Nat.cast_ofNat, one_mul]
      calc
        ((adaptiveShellBlockLength T a.1 : ℕ) : ℝ) * (2 * (P : ℝ)) =
            2 * (((adaptiveShellBlockLength T a.1 : ℕ) : ℝ) * P) := by ring
        _ = 2 * ((2 ^ a.1 : ℕ) : ℝ) := by rw [hcast]
    rw [hratio] at hlocal
    apply le_trans ?_ hlocal
    have hcast : (P : ℝ) ≤ 2 * (T + 1 : ℕ) := by exact_mod_cast hPupper
    apply (inv_le_inv₀ (show 0 < (8 * (T + 1 : ℕ) : ℝ) by positivity)
      (show 0 < (2 * (P : ℝ)) by positivity)).2
    nlinarith
  · have hab : a.1 ≠ b.1 := by
      intro hab
      exact ha (Subtype.ext hab)
    have hforward : ∀ z w : adaptiveDetectorBlocks Y N T,
        z.1.1 < w.1.1 →
          (8 * (T + 1 : ℕ) : ℝ)⁻¹ ≤
            |adaptiveDetectorBlockCenter Y N T z -
              adaptiveDetectorBlockCenter Y N T w| := by
      intro z w hablt
      let A : ℕ := 2 ^ z.1.1
      let H : ℕ := adaptiveShellBlockLength T z.1.1
      let cz : ℕ := A + z.2.1 * H + 1
      let y : ℕ := 2 * A + 1
      let cw : ℕ := 2 ^ w.1.1 + w.2.1 *
        adaptiveShellBlockLength T w.1.1 + 1
      have hzBounds := adaptive_center_nat_bounds hY
        (hden z.1.1 z.1.2) z.2
      have hwBounds := adaptive_center_nat_bounds hY
        (hden w.1.1 w.1.2) w.2
      have hpow : 2 * A ≤ 2 ^ w.1.1 := by
        calc
          2 * A = 2 ^ (z.1.1 + 1) := by
            dsimp [A]
            rw [pow_succ]
            omega
          _ ≤ 2 ^ w.1.1 := Nat.pow_le_pow_right (by omega) (by omega)
      have hczGap : cz + H ≤ 2 * A + 1 := by
        simpa only [cz, A, H] using hzBounds.2
      have hycw : y ≤ cw := by
        have hwLower : 2 ^ w.1.1 + 1 ≤ cw := by
          simpa only [cw] using hwBounds.1
        dsimp [y]
        omega
      have hczy : cz ≤ y := by
        dsimp [y]
        omega
      have hgap : H ≤ y - cz := by
        apply Nat.le_sub_of_add_le
        simpa only [y, Nat.add_comm H cz] using hczGap
      have hczPos : (0 : ℝ) < cz := by
        exact_mod_cast (show 0 < cz by dsimp [cz, A]; positivity)
      have hyPos : (0 : ℝ) < y := by
        exact_mod_cast (show 0 < y by dsimp [y, A]; positivity)
      have hcwPos : (0 : ℝ) < cw := by
        exact_mod_cast (show 0 < cw by dsimp [cw]; positivity)
      have hczyR : (cz : ℝ) ≤ y := by exact_mod_cast hczy
      have hycwR : (y : ℝ) ≤ cw := by exact_mod_cast hycw
      have hlog := log_sub_log_lower_adaptive hczPos hczyR
      have hHA : H * P = A := by
        simpa only [H, P, A] using
          adaptiveShellBlockLength_mul_denominator (hden z.1.1 z.1.2)
      have hHAreal : (H : ℝ) * P = A := by exact_mod_cast hHA
      have hgapR : (H : ℝ) ≤ (y : ℝ) - cz := by exact_mod_cast hgap
      have hPcast : (P : ℝ) ≤ 2 * (T + 1 : ℕ) := by
        exact_mod_cast hPupper
      have htarget : (y : ℝ) ≤ 8 * (T + 1 : ℕ) * H := by
        have hAposNat : 1 ≤ A := by
          dsimp [A]
          exact Nat.one_le_pow z.1.1 2 (by omega)
        have hApos : (1 : ℝ) ≤ A := by exact_mod_cast hAposNat
        have hyA : (y : ℝ) ≤ 3 * A := by
          dsimp [y]
          push_cast
          linarith
        calc
          (y : ℝ) ≤ 3 * A := hyA
          _ = 3 * ((H : ℝ) * P) := by rw [hHAreal]
          _ ≤ 3 * ((H : ℝ) * (2 * (T + 1 : ℕ))) := by gcongr
          _ ≤ 8 * (T + 1 : ℕ) * H := by
            have hnonneg : 0 ≤ (T + 1 : ℝ) * H := by positivity
            ring_nf at ⊢
            nlinarith
      have hcoarse :
          (8 * (T + 1 : ℕ) : ℝ)⁻¹ ≤
            ((y : ℝ) - cz) / y := by
        rw [inv_eq_one_div]
        apply (div_le_div_iff₀ (by positivity) hyPos).2
        have hscaled := mul_le_mul_of_nonneg_left hgapR
          (show 0 ≤ (8 * (T + 1 : ℕ) : ℝ) by positivity)
        calc
          (1 : ℝ) * y = y := one_mul _
          _ ≤ 8 * (T + 1 : ℕ) * H := htarget
          _ ≤ ((y : ℝ) - cz) * (8 * (T + 1 : ℕ)) := by
            simpa only [mul_comm] using hscaled
      have hlogMono : Real.log y ≤ Real.log cw :=
        Real.log_le_log hyPos hycwR
      rw [adaptiveDetectorBlockCenter, adaptiveDetectorBlockCenter,
        shortBlockCenter]
      change _ ≤ |Real.log cz - Real.log cw|
      rw [abs_sub_comm, abs_of_nonneg]
      · exact hcoarse.trans (hlog.trans (sub_le_sub_right hlogMono _))
      · exact sub_nonneg.mpr
          (Real.log_le_log hczPos (hczyR.trans hycwR))
    rcases lt_or_gt_of_ne hab with hablt | hbalt
    · exact hforward ⟨a, i⟩ ⟨b, j⟩ hablt
    · simpa only [abs_sub_comm] using hforward ⟨b, j⟩ ⟨a, i⟩ hbalt

end

end Erdos48
