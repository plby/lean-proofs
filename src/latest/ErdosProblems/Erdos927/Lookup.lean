/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 John Jennings. All rights reserved.
Released under Apache 2.0 license; see LICENSE.
Modified for this repository and Lean/Mathlib 4.33.0.
-/
/-
Erdős Problem 927.
Informal proof: Joel H. Spencer, "On cliques in graphs" (1971).
Formal authors: John Jennings and Aristotle (Harmonic).
Jake Mallen replaced native evaluation with kernel-checked proofs in the selected copy.
Source: https://www.erdosproblems.com/927#post-6850
https://gist.githubusercontent.com/JohnEdwardJennings/24c9debc9854cb118fbc1314c70941c3/raw/b4fc5ef91876a89018b10508c479c000258504fb/Erdos927.lean
https://github.com/Jayyhk/erdos-lean/tree/cc6c94bd3f9de7c4cf7703ed40d8fd06380780a3/problems/927
Original and selected toolchain: Lean 4.28.0.
Selected Mathlib commit: 8f9d9cff6bd728b17a24e163c9402775d9e6a365.
-/
import ErdosProblems.Erdos927.Graph

set_option linter.mathlibStandardSet false

namespace Erdos927

/-
# Small Clique — Lookup Properties

Properties of wLookup, vLookup, and findVPos needed for the small clique construction.
-/

/-! ## Offset definitions -/

/-- w-vertex offset at level ℓ: sum of recSeq n (i+1) for i = 0,...,ℓ-1. -/
def wOff (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | ℓ + 1 => wOff n ℓ + recSeq n (ℓ + 1)

/-- v-vertex offset at level ℓ: sum of levelVSize n i for i = 0,...,ℓ-1. -/
def vOff (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | ℓ + 1 => vOff n ℓ + levelVSize n ℓ

/-- Position offset within a level: sum of (2^i + 1) for i = 0,...,q-1. -/
def cPosOff : ℕ → ℕ
  | 0 => 0
  | q + 1 => cPosOff q + (2 ^ q + 1)

/-! ## Basic properties -/

@[simp] lemma wOff_zero (n : ℕ) : wOff n 0 = 0 := rfl
@[simp] lemma wOff_succ (n ℓ : ℕ) : wOff n (ℓ + 1) = wOff n ℓ + recSeq n (ℓ + 1) := rfl
@[simp] lemma vOff_zero (n : ℕ) : vOff n 0 = 0 := rfl
@[simp] lemma vOff_succ (n ℓ : ℕ) : vOff n (ℓ + 1) = vOff n ℓ + levelVSize n ℓ := rfl
@[simp] lemma cPosOff_zero_val : cPosOff 0 = 0 := rfl
@[simp] lemma cPosOff_succ_val (q : ℕ) : cPosOff (q + 1) = cPosOff q + (2 ^ q + 1) := rfl

lemma wOff_mono (n : ℕ) {a b : ℕ} (h : a ≤ b) : wOff n a ≤ wOff n b := by
  classical
  induction b with
  | zero => simp_all
  | succ b ih =>
    rcases Nat.eq_or_lt_of_le h with rfl | h'
    · exact le_refl _
    · exact le_trans (ih (Nat.lt_succ_iff.mp h')) (Nat.le_add_right _ _)

lemma vOff_mono (n : ℕ) {a b : ℕ} (h : a ≤ b) : vOff n a ≤ vOff n b := by
  classical
  induction b with
  | zero => simp_all
  | succ b ih =>
    rcases Nat.eq_or_lt_of_le h with rfl | h'
    · exact le_refl _
    · exact le_trans (ih (Nat.lt_succ_iff.mp h')) (Nat.le_add_right _ _)

lemma cPosOff_mono {a b : ℕ} (h : a ≤ b) : cPosOff a ≤ cPosOff b := by
  classical
  induction b with
  | zero => simp_all
  | succ b ih =>
    rcases Nat.eq_or_lt_of_le h with rfl | h'
    · exact le_refl _
    · exact le_trans (ih (Nat.lt_succ_iff.mp h')) (Nat.le_add_right _ _)

/-- cPosOff k = 2^k - 1 + k -/
lemma cPosOff_eq (k : ℕ) : cPosOff k = 2 ^ k - 1 + k := by
  classical
  induction k with
  | zero => simp [cPosOff]
  | succ k ih =>
    simp only [cPosOff_succ_val, ih]
    have h : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by norm_num)
    omega

/-- cPosOff (recSeq n (ℓ+1)) = levelVSize n ℓ -/
lemma cPosOff_eq_levelVSize (n ℓ : ℕ) :
    cPosOff (recSeq n (ℓ + 1)) = levelVSize n ℓ := by
  classical
  simp only [cPosOff_eq, levelVSize]
  have : 1 ≤ 2 ^ recSeq n (ℓ + 1) := Nat.one_le_pow _ 2 (by norm_num)
  omega

/-- cPosOff is strictly monotone -/
lemma cPosOff_strict_mono {a b : ℕ} (h : a < b) : cPosOff a < cPosOff b := by
  classical
  have h1 : cPosOff a + (2^a + 1) ≤ cPosOff b := by
    calc cPosOff a + (2^a + 1) = cPosOff (a + 1) := by simp [cPosOff]
      _ ≤ cPosOff b := cPosOff_mono (by omega)
  have h2 : 2 ^ a + 1 ≥ 2 := by
    have := Nat.one_le_pow a 2 (by norm_num); omega
  omega

/-! ## wLookup correctness -/

/-- wLookup correctness at arbitrary level.
  Starting from `level` with offset = wOff n ℓ - wOff n level + p,
  returns (ℓ, p) if level ≤ ℓ and fuel is sufficient. -/
lemma wLookup_wOff (n ℓ p level fuel : ℕ)
    (hp : p < recSeq n (ℓ + 1))
    (hℓ : level ≤ ℓ)
    (hfuel : ℓ - level < fuel)
    (hwoff_le : wOff n level ≤ wOff n ℓ) :
    wLookup n (wOff n ℓ - wOff n level + p) level fuel = some (ℓ, p) := by
  classical
  induction fuel generalizing level with
  | zero => omega
  | succ f ih =>
    simp only [wLookup]
    by_cases h_done : level = ℓ
    · subst h_done; simp [hp]
    · have h_lt : level < ℓ := Nat.lt_of_le_of_ne hℓ h_done
      have hwoff_succ : wOff n (level + 1) ≤ wOff n ℓ :=
        wOff_mono n (by omega)
      have h_ge : ¬ (wOff n ℓ - wOff n level + p < recSeq n (level + 1)) := by
        have : wOff n level + recSeq n (level + 1) = wOff n (level + 1) := rfl
        omega
      simp [h_ge]
      have h_off : wOff n ℓ - wOff n level + p - recSeq n (level + 1)
                 = wOff n ℓ - wOff n (level + 1) + p := by
        have : wOff n level + recSeq n (level + 1) = wOff n (level + 1) := rfl
        omega
      rw [h_off]
      exact ih (level + 1) (by omega) (by omega) hwoff_succ

/-- Main wLookup correctness lemma starting from level 0. -/
theorem wLookup_at_level (n ℓ p : ℕ)
    (hp : p < recSeq n (ℓ + 1))
    (hℓ : ℓ < n)
    (_ : wOff n (ℓ + 1) ≤ n) :
    wLookup n (wOff n ℓ + p) 0 n = some (ℓ, p) := by
  classical
  have h1 : wOff n ℓ + p = wOff n ℓ - wOff n 0 + p := by simp
  rw [h1]
  exact wLookup_wOff n ℓ p 0 n hp (Nat.zero_le _) (by omega) (by simp)

/-! ## findVPos correctness -/

/-- findVPos correctness: given offset = cPosOff q - cPosOff pos₀ + s
  with s < 2^q + 1 and pos₀ ≤ q, returns (q, s). -/
lemma findVPos_cPosOff (q s pos₀ fuel : ℕ)
    (hs : s < 2 ^ q + 1)
    (hq : pos₀ ≤ q)
    (hfuel : q - pos₀ < fuel)
    (hcpos : cPosOff pos₀ ≤ cPosOff q) :
    findVPos (cPosOff q - cPosOff pos₀ + s) pos₀ fuel = (q, s) := by
  classical
  induction fuel generalizing pos₀ with
  | zero => omega
  | succ f ih =>
    simp only [findVPos]
    by_cases h_done : pos₀ = q
    · subst h_done; simp [hs]
    · have h_lt : pos₀ < q := Nat.lt_of_le_of_ne hq h_done
      have hcpos_succ : cPosOff (pos₀ + 1) ≤ cPosOff q :=
        cPosOff_mono (by omega)
      have h_ge : ¬ (cPosOff q - cPosOff pos₀ + s < 2 ^ pos₀ + 1) := by
        have : cPosOff pos₀ + (2 ^ pos₀ + 1) = cPosOff (pos₀ + 1) := by simp [cPosOff]
        omega
      simp [h_ge]
      have h_off : cPosOff q - cPosOff pos₀ + s - (2 ^ pos₀ + 1)
                 = cPosOff q - cPosOff (pos₀ + 1) + s := by
        have : cPosOff pos₀ + (2 ^ pos₀ + 1) = cPosOff (pos₀ + 1) := by simp [cPosOff]
        omega
      rw [h_off]
      exact ih (pos₀ + 1) (by omega) (by omega) hcpos_succ

/-- findVPos starting from position 0. -/
theorem findVPos_at_pos (q s fuel : ℕ)
    (hs : s < 2 ^ q + 1) (hfuel : q < fuel) :
    findVPos (cPosOff q + s) 0 fuel = (q, s) := by
  classical
  have h : cPosOff q + s = cPosOff q - cPosOff 0 + s := by simp
  rw [h]
  exact findVPos_cPosOff q s 0 fuel hs (Nat.zero_le _) (by omega) (by simp)

/-! ## vLookup correctness -/

/-- vLookup correctness at arbitrary level. -/
lemma vLookup_vOff (n ℓ localOff level fuel : ℕ)
    (hloc : localOff < levelVSize n ℓ)
    (hℓ : level ≤ ℓ)
    (hfuel : ℓ - level < fuel)
    (hvoff_le : vOff n level ≤ vOff n ℓ) :
    vLookup n (vOff n ℓ - vOff n level + localOff) level fuel =
    (ℓ, (findVPos localOff 0 (recSeq n (ℓ + 1))).1,
     (findVPos localOff 0 (recSeq n (ℓ + 1))).2) := by
  classical
  induction fuel generalizing level with
  | zero => omega
  | succ f ih =>
    simp only [vLookup]
    by_cases h_done : level = ℓ
    · subst h_done
      simp [hloc]
    · have h_lt : level < ℓ := Nat.lt_of_le_of_ne hℓ h_done
      have hvoff_succ : vOff n (level + 1) ≤ vOff n ℓ :=
        vOff_mono n (by omega)
      have h_ge : ¬ (vOff n ℓ - vOff n level + localOff < levelVSize n level) := by
        have : vOff n level + levelVSize n level = vOff n (level + 1) := rfl
        omega
      simp [h_ge]
      have h_off : vOff n ℓ - vOff n level + localOff - levelVSize n level
                 = vOff n ℓ - vOff n (level + 1) + localOff := by
        have : vOff n level + levelVSize n level = vOff n (level + 1) := rfl
        omega
      rw [h_off]
      exact ih (level + 1) (by omega) (by omega) hvoff_succ

/-- Main vLookup correctness lemma: vLookup at level ℓ, position q, sub-index s. -/
theorem vLookup_at_level (n ℓ q s : ℕ)
    (hq : q < recSeq n (ℓ + 1))
    (hs : s < 2 ^ q + 1)
    (hℓ : ℓ < n)
    (_ : vOff n (ℓ + 1) ≤ spA n) :
    vLookup n (vOff n ℓ + cPosOff q + s) 0 n = (ℓ, q, s) := by
  classical
  have hloc : cPosOff q + s < levelVSize n ℓ := by
    have h1 : cPosOff q + s < cPosOff (q + 1) := by simp [cPosOff]; omega
    have h2 : cPosOff (q + 1) ≤ cPosOff (recSeq n (ℓ + 1)) := cPosOff_mono (by omega)
    rw [cPosOff_eq_levelVSize] at h2; omega
  have h1 : vOff n ℓ + cPosOff q + s = vOff n ℓ + (cPosOff q + s) := by omega
  rw [h1, show vOff n ℓ + (cPosOff q + s) = vOff n ℓ - vOff n 0 + (cPosOff q + s) by simp]
  have hvl := vLookup_vOff n ℓ (cPosOff q + s) 0 n hloc (Nat.zero_le _) (by omega) (by simp)
  rw [hvl]
  have hvp := findVPos_at_pos q s (recSeq n (ℓ + 1)) hs hq
  simp [hvp]

/-! ## wvAdj characterization -/

/-- wvAdj is true when wLookup and vLookup give same level, different position. -/
lemma wvAdj_true_of_ne (n : ℕ) (i : Fin n) (j : Fin (spA n))
    (ℓ p q s : ℕ)
    (hwl : wLookup n ((i : ℕ) - n / 2) 0 n = some (ℓ, p))
    (hvl : vLookup n (j : ℕ) 0 n = (ℓ, q, s))
    (hpq : p ≠ q) :
    wvAdj n i j = true := by
  classical
  unfold wvAdj
  change (match wLookup n ((i : ℕ) - n / 2) 0 n with
    | none => false
    | some (wl, wp) => match vLookup n (↑j) 0 n with
      | (vl, vp, _) => wl == vl && wp != vp) = _
  rw [hwl, hvl]
  simp [Bool.true_and, bne, hpq]

/-- wvAdj is false when wLookup and vLookup give same level, same position. -/
lemma wvAdj_false_of_eq (n : ℕ) (i : Fin n) (j : Fin (spA n))
    (ℓ p s : ℕ)
    (hwl : wLookup n ((i : ℕ) - n / 2) 0 n = some (ℓ, p))
    (hvl : vLookup n (j : ℕ) 0 n = (ℓ, p, s)) :
    wvAdj n i j = false := by
  classical
  unfold wvAdj
  change (match wLookup n ((i : ℕ) - n / 2) 0 n with
    | none => false
    | some (wl, wp) => match vLookup n (↑j) 0 n with
      | (vl, vp, _) => wl == vl && wp != vp) = _
  rw [hwl, hvl]
  simp [bne]

/-- wvAdj result when wLookup and vLookup give different levels. -/
lemma wvAdj_diff_level (n : ℕ) (i : Fin n) (j : Fin (spA n))
    (ℓ₁ p ℓ₂ q s : ℕ)
    (hwl : wLookup n ((i : ℕ) - n / 2) 0 n = some (ℓ₁, p))
    (hvl : vLookup n (j : ℕ) 0 n = (ℓ₂, q, s))
    (hne : ℓ₁ ≠ ℓ₂) :
    wvAdj n i j = false := by
  classical
  unfold wvAdj
  change (match wLookup n ((i : ℕ) - n / 2) 0 n with
    | none => false
    | some (wl, wp) => match vLookup n (↑j) 0 n with
      | (vl, vp, _) => wl == vl && wp != vp) = _
  rw [hwl, hvl]
  simp [beq_iff_eq, hne]

/-- wvAdj is false when wLookup returns none. -/
lemma wvAdj_none (n : ℕ) (i : Fin n) (j : Fin (spA n))
    (hwl : wLookup n ((i : ℕ) - n / 2) 0 n = none) :
    wvAdj n i j = false := by
  classical
  unfold wvAdj
  change (match wLookup n ((i : ℕ) - n / 2) 0 n with
    | none => false
    | some (wl, wp) => match vLookup n (↑j) 0 n with
      | (vl, vp, _) => wl == vl && wp != vp) = _
  rw [hwl]

/-! ## isGeneric characterization -/

/-- A y-vertex at index ≥ n/2 is non-generic. -/
lemma isGeneric_false_of_ge (n : ℕ) (i : Fin n) (h : n / 2 ≤ (i : ℕ)) :
    isGeneric n i = false := by
  classical
  unfold isGeneric; simp [Nat.not_lt.mpr h]

/-- A y-vertex at index < n/2 is generic. -/
lemma isGeneric_true_of_lt (n : ℕ) (i : Fin n) (h : (i : ℕ) < n / 2) :
    isGeneric n i = true := by
  classical
  unfold isGeneric; simp [h]

/-! ## recSeq properties -/

/-- recSeq n (k+1) < recSeq n k for recSeq n k ≥ 3. -/
lemma recSeq_decreasing (n k : ℕ) (h : recSeq n k ≥ 3) :
    recSeq n (k + 1) < recSeq n k := by
  classical
  simp only [recSeq]
  split_ifs with h'
  · omega
  · have := Nat.log_lt_of_lt_pow (show recSeq n k - 1 ≠ 0 by omega)
      (Nat.lt_pow_self (show 1 < 2 by norm_num))
    omega

/-- recSeq n (k+1) ≥ 2 when recSeq n k ≥ 2. -/
lemma recSeq_ge_two (n k : ℕ) (_ : recSeq n k ≥ 2) :
    recSeq n (k + 1) ≥ 2 := by
  classical
  simp only [recSeq]
  split_ifs with h' <;> [exact le_refl _; skip]
  have : Nat.log 2 (recSeq n k - 1) ≥ 1 := by
    apply Nat.le_log_of_pow_le (by norm_num)
    omega
  omega

/-- 2^(recSeq n (k+1)) > recSeq n k - 1 when recSeq n k ≥ 3.
  This ensures level overlap in the recursive construction. -/
lemma pow_recSeq_gt (n k : ℕ) (h : recSeq n k ≥ 3) :
    2 ^ recSeq n (k + 1) > recSeq n k - 1 := by
  classical
  have hge : recSeq n k ≥ 3 := h
  simp only [recSeq]
  split_ifs with h'
  · omega
  · have := Nat.lt_pow_succ_log_self (show 1 < 2 by norm_num) (recSeq n k - 1)
    simp only [Nat.succ_eq_add_one] at this
    exact this

/-- Level overlap: the max size at level k+1 is ≥ min size at level k. -/
lemma level_overlap (n k : ℕ) (h : recSeq n k ≥ 3) :
    2 ^ recSeq n (k + 1) + recSeq n (k + 1) ≥ recSeq n k + 2 := by
  classical
  have h1 := pow_recSeq_gt n k h
  have h2 := recSeq_ge_two n k (by omega)
  omega

/-
wLookup returns position < recSeq.
-/
lemma wLookup_pos_bound (n offset level fuel ℓ p : ℕ)
    (h : wLookup n offset level fuel = some (ℓ, p)) :
    p < recSeq n (ℓ + 1) := by
  classical
  induction' fuel with fuel ih generalizing level offset;
  · unfold wLookup at h;
    unfold recSeq; aesop;
  · unfold wLookup at h;
    grind

/-
wLookup offset reconstruction.
-/
lemma wLookup_offset_eq (n offset level fuel ℓ p : ℕ)
    (h : wLookup n offset level fuel = some (ℓ, p))
    (hlev : level ≤ ℓ) :
    offset = wOff n ℓ - wOff n level + p := by
  classical
  induction' fuel with fuel fuel_ih generalizing offset level ℓ p <;> simp_all +decide [ wLookup ];
  split_ifs at h <;> simp_all +decide;
  specialize fuel_ih ( offset - recSeq n ( level + 1 ) ) ( level + 1 ) ℓ p h;
  cases hlev.eq_or_lt <;> simp_all +decide [ add_comm ];
  · have h_wLookup_pos : ∀ {offset level fuel ℓ p}, wLookup n offset level fuel = some (ℓ, p) → level ≤ ℓ := by
      intros offset level fuel ℓ p h; induction' fuel with fuel fuel_ih generalizing offset level ℓ p <;> simp_all +decide [ wLookup ] ;
      grind;
    grind;
  · rw [ Nat.sub_eq_iff_eq_add ] at fuel_ih;
    · rw [ fuel_ih, add_assoc, tsub_add_eq_add_tsub ];
      · rw [ Nat.add_sub_add_right ];
      · exact Nat.le_induction ( by simp +decide [ wOff ] ) ( fun k hk ih => by simp +decide [ wOff ] at * ; linarith ) _ ‹level < ℓ›;
    · linarith

/-
findVPos returns sub < 2^pos + 1 when offset fits within fuel positions.
-/
lemma findVPos_sub_bound (offset pos fuel : ℕ)
    (h : offset < cPosOff (pos + fuel) - cPosOff pos) :
    (findVPos offset pos fuel).2 < 2 ^ (findVPos offset pos fuel).1 + 1 := by
  classical
  contrapose! h;
  induction' fuel with fuel ih generalizing offset pos;
  · aesop;
  · unfold findVPos at h;
    have := ih ( offset - ( 2 ^ pos + 1 ) ) ( pos + 1 ) ?_;
    · simp_all +decide [ Nat.add_comm, Nat.add_left_comm, Nat.add_assoc ];
      grind;
    · grind

/-
findVPos returns pos within bounds.
-/
lemma findVPos_pos_bound (offset pos fuel : ℕ)
    (h : offset < cPosOff (pos + fuel) - cPosOff pos) :
    (findVPos offset pos fuel).1 < pos + fuel := by
  classical
  contrapose! h;
  induction' fuel with fuel ih generalizing pos offset;
  · aesop;
  · by_cases h₂ : offset < 2 ^ pos + 1;
    · unfold findVPos at h; aesop;
    · specialize ih ( offset - ( 2 ^ pos + 1 ) ) ( pos + 1 ) ; simp_all +decide [ ];
      rw [ show findVPos offset pos ( fuel + 1 ) = findVPos ( offset - ( 2 ^ pos + 1 ) ) ( pos + 1 ) fuel from ?_ ] at h;
      · grind;
      · exact if_neg ( by linarith )

/-
findVPos offset reconstruction.
-/
lemma findVPos_offset_eq (offset pos fuel : ℕ)
    (h : offset < cPosOff (pos + fuel) - cPosOff pos) :
    offset = cPosOff (findVPos offset pos fuel).1 - cPosOff pos + (findVPos offset pos fuel).2 := by
  classical
  induction' fuel with fuel ih generalizing offset pos;
  · grind;
  · unfold findVPos;
    specialize ih ( offset - ( 2 ^ pos + 1 ) ) ( pos + 1 ) ; simp_all +decide [ ];
    split_ifs <;> simp_all +decide [ add_comm, add_left_comm ];
    convert congr_arg ( · + ( 1 + 2 ^ pos ) ) ( ih _ ) using 1;
    · rw [ Nat.sub_add_cancel ( by linarith ) ];
    · rw [ add_assoc, tsub_add_eq_add_tsub ];
      · rw [ Nat.add_sub_add_right ];
      · have h_findVPos_pos : (findVPos (offset - (1 + 2 ^ pos)) (pos + 1) fuel).1 ≥ pos + 1 := by
          have h_findVPos_pos : ∀ (offset pos fuel : ℕ), (findVPos offset pos fuel).1 ≥ pos := by
            intros offset pos fuel; induction' fuel with fuel ih generalizing offset pos <;> unfold findVPos <;> simp +arith +decide [ * ] ;
            grind;
          exact h_findVPos_pos _ _ _;
        refine' le_trans _ ( cPosOff_mono h_findVPos_pos );
        simp +arith +decide [ cPosOff ];
    · omega

/-! ## vLookup offset reconstruction -/

/-- If vLookup returns level ℓ, then the input offset equals vOff n ℓ - vOff n level + local offset. -/
lemma vLookup_level_ge (n offset level fuel : ℕ) :
    (vLookup n offset level fuel).1 ≥ level := by
  classical
  induction fuel generalizing offset level with
  | zero => simp [vLookup]
  | succ f ih =>
    simp only [vLookup]
    split_ifs with h
    · simp
    · exact le_trans (Nat.le_succ _) (ih _ _)

set_option maxHeartbeats 3200000 in
private lemma vLookup_offset_eq_step (n offset level fuel ℓ q s : ℕ)
    (ih : ∀ (offset level : ℕ),
      vLookup n offset level fuel = (ℓ, q, s) → level ≤ ℓ →
      offset = vOff n ℓ - vOff n level + cPosOff q + s)
    (h : vLookup n offset level (fuel + 1) = (ℓ, q, s))
    (_ : level ≤ ℓ) :
    offset = vOff n ℓ - vOff n level + cPosOff q + s := by
  classical
  unfold vLookup at h;
  by_cases h' : offset < levelVSize n level <;> simp +decide [ h' ] at h ⊢;
  · convert findVPos_offset_eq offset 0 ( recSeq n ( level + 1 ) ) _ using 1;
    · aesop;
    · convert h' using 1;
      convert cPosOff_eq_levelVSize n level using 1;
      norm_num;
  · have hlev' : level + 1 ≤ ℓ := by
      have := vLookup_level_ge n (offset - levelVSize n level) (level + 1) fuel
      simp only [h, ge_iff_le] at this; omega
    have h_ih := ih _ _ h hlev'
    have hvoff : vOff n (level + 1) = vOff n level + levelVSize n level := rfl
    have hvoff_le : vOff n (level + 1) ≤ vOff n ℓ := vOff_mono n hlev'
    have hoff_ge : offset ≥ levelVSize n level := Nat.le_of_not_lt h'
    rw [hvoff] at hvoff_le h_ih
    zify [hoff_ge, hvoff_le] at h_ih ⊢; omega

set_option maxHeartbeats 3200000 in
lemma vLookup_offset_eq (n offset level fuel ℓ q s : ℕ)
    (h : vLookup n offset level fuel = (ℓ, q, s))
    (hlev : level ≤ ℓ) :
    offset = vOff n ℓ - vOff n level + cPosOff q + s := by
  classical
  induction' fuel with fuel ih generalizing offset level;
  · cases h;
    by_cases h : offset < cPosOff ( 0 + ( recSeq n ( ℓ + 1 ) ) ) - cPosOff 0 <;> simp_all +decide [ cPosOff_eq ];
    · convert findVPos_offset_eq offset 0 ( recSeq n ( ℓ + 1 ) ) _ using 1;
      · rw [ cPosOff_eq ] ; norm_num;
      · convert h using 1;
        simp +decide [ cPosOff_eq ];
    · have h_findVPos : ∀ (offset pos fuel : ℕ), offset ≥ cPosOff (pos + fuel) - cPosOff pos → findVPos offset pos fuel
          = (pos + fuel, offset - (cPosOff (pos + fuel) - cPosOff pos)) := by
        intros offset pos fuel h; induction' fuel with fuel ih generalizing offset pos <;> simp_all +decide [ cPosOff_eq ] ;
        · rfl;
        · rw [ show findVPos offset pos ( fuel + 1 ) = findVPos ( offset - ( 2 ^ pos + 1 ) ) ( pos + 1 ) fuel from ?_ ];
          · convert ih ( offset - ( 2 ^ pos + 1 ) ) ( pos + 1 ) _ using 1;
            · simp +arith +decide [ Nat.pow_succ' ];
              rw [ Nat.sub_sub ] ; ring_nf;
              rw [ show 2 ^ pos * 2 - 1 = 2 ^ pos - 1 + 2 ^ pos by zify ; norm_num ; ring ] ; ring_nf;
              rw [ show 1 + fuel + pos + ( 2 ^ fuel * 2 ^ pos * 2 - 1 ) - ( pos + ( 2 ^ pos - 1 ) )
                          = 1 + ( fuel + pos + ( 2 ^ fuel * 2 ^ pos * 2 - 1 ) - ( pos + ( 2 ^ pos - 1 ) + 2 ^ pos ) ) + 2 ^ pos from ?_ ];
              rw [ Nat.sub_eq_of_eq_add ] ;
              linarith [ Nat.sub_add_cancel ( show pos + ( 2 ^ pos - 1 ) + 2 ^ pos ≤ fuel + pos + ( 2 ^ fuel * 2 ^ pos * 2 - 1 ) from by
                                                rcases fuel with ( _ | fuel ) <;> simp_all +decide [ Nat.pow_succ', Nat.mul_assoc ];
                                                · grind;
                                                · nlinarith [ Nat.sub_add_cancel ( show 1 ≤ 2 ^ pos from Nat.one_le_pow _ _ ( by decide ) ),
                                                      Nat.sub_add_cancel ( show 1 ≤ 2 * ( 2 ^ fuel * ( 2 ^ pos * 2 ) ) from Nat.one_le_iff_ne_zero.mpr <| by positivity ),
                                                      Nat.one_le_pow fuel 2 ( by decide ), Nat.one_le_pow pos 2 ( by decide )
                                                    ]
                                              ) ];
            · grind;
          · exact if_neg ( by
              contrapose! h;
              rw [ pow_add ];
              nlinarith [ Nat.sub_add_cancel ( Nat.one_le_pow pos 2 zero_lt_two ),
                Nat.pow_le_pow_right two_pos ( show fuel + 1 ≥ 1 by linarith ),
                Nat.sub_add_cancel ( show 1 ≤ 2 ^ pos * 2 ^ ( fuel + 1 ) from Nat.one_le_iff_ne_zero.mpr <| by positivity ) ] );
      rw [ h_findVPos ] <;> norm_num [ cPosOff_eq ];
      · rw [ Nat.add_sub_of_le h ];
      · omega
  · exact vLookup_offset_eq_step n offset level fuel ℓ q s ih h hlev

lemma vLookup_pos_bound (n offset level fuel ℓ q s : ℕ)
    (h : vLookup n offset level fuel = (ℓ, q, s))
    (hfuel : ℓ - level < fuel) :
    q < recSeq n (ℓ + 1) ∧ s < 2 ^ q + 1 := by
  classical
  induction' fuel with fuel ih generalizing offset level;
  · omega;
  · unfold vLookup at h;
    by_cases h : offset < levelVSize n level <;> simp_all +decide;
    · have := findVPos_pos_bound offset 0 ( recSeq n ( ℓ + 1 ) ) ?_ <;> simp_all +decide [ cPosOff_eq_levelVSize ];
      have := findVPos_sub_bound offset 0 ( recSeq n ( ℓ + 1 ) ) ?_ <;> simp_all +decide [ cPosOff_eq_levelVSize ];
      grind;
    · apply ih;
      expose_names; exact Prod.ext (congrArg Prod.fst h_1) (congrArg Prod.snd h_1)
      have := vLookup_level_ge n ( offset - levelVSize n level ) ( level + 1 ) fuel; simp_all +decide ; omega;

end Erdos927
