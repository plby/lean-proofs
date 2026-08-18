/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib.Combinatorics.Pigeonhole
import ErdosProblems.Erdos984.Basic

/-!
# Geometric blocks for Erdős Problem 984

The blocks are the half-open intervals `[100^t, 100^(t+1))`.  This file
develops their elementary interaction with finite arithmetic progressions.
-/

namespace Erdos984

def blockBase : ℕ := 100

def blockStart (t : ℕ) : ℕ := blockBase ^ t

def InBlock (t n : ℕ) : Prop :=
  blockStart t ≤ n ∧ n < blockStart (t + 1)

instance (t n : ℕ) : Decidable (InBlock t n) := by
  unfold InBlock
  infer_instance

def blockIndex (n : ℕ) : ℕ :=
  Nat.log blockBase n

def apTerm (a d i : ℕ) : ℕ :=
  a + i * d

def blockIndices (a d k t : ℕ) : Finset ℕ :=
  (Finset.range k).filter fun i => InBlock t (apTerm a d i)

def nearIndices (a d k s : ℕ) : Finset ℕ :=
  (Finset.range k).filter fun i => apTerm a d i < blockStart (s + 6)

@[simp] lemma blockBase_eq : blockBase = 100 := rfl

@[simp] lemma blockStart_zero : blockStart 0 = 1 := by
  simp [blockStart]

lemma one_lt_blockBase : 1 < blockBase := by norm_num [blockBase]

lemma blockStart_pos (t : ℕ) : 0 < blockStart t := by
  simp [blockStart, blockBase]

lemma blockStart_mono : Monotone blockStart := by
  intro s t hst
  exact Nat.pow_le_pow_right (by norm_num [blockBase]) hst

lemma blockIndex_spec {n : ℕ} (hn : 0 < n) : InBlock (blockIndex n) n := by
  constructor
  · exact Nat.pow_log_le_self blockBase hn.ne'
  · exact (Nat.log_lt_iff_lt_pow one_lt_blockBase hn.ne').mp
      (Nat.lt_succ_self (Nat.log blockBase n))

lemma inBlock_iff_blockIndex_eq {t n : ℕ} (hn : 0 < n) :
    InBlock t n ↔ blockIndex n = t := by
  constructor
  · intro h
    apply Nat.le_antisymm
    · have hlt : blockIndex n < t + 1 :=
        (Nat.log_lt_iff_lt_pow one_lt_blockBase hn.ne').2 h.2
      omega
    · exact (Nat.le_log_iff_pow_le one_lt_blockBase hn.ne').2 h.1
  · intro h
    simpa [h] using blockIndex_spec hn

@[simp] lemma mem_blockIndices {a d k t i : ℕ} :
    i ∈ blockIndices a d k t ↔ i < k ∧ InBlock t (apTerm a d i) := by
  simp [blockIndices]

@[simp] lemma mem_nearIndices {a d k s i : ℕ} :
    i ∈ nearIndices a d k s ↔
      i < k ∧ apTerm a d i < blockStart (s + 6) := by
  simp [nearIndices]

lemma apTerm_mono (a d : ℕ) : Monotone (apTerm a d) := by
  intro i j hij
  exact Nat.add_le_add_left (Nat.mul_le_mul_right d hij) a

lemma apTerm_strictMono {a d : ℕ} (hd : 0 < d) : StrictMono (apTerm a d) := by
  intro i j hij
  exact Nat.add_lt_add_left ((Nat.mul_lt_mul_right hd).2 hij) a

lemma blockIndices_ordConnected {a d k t x y z : ℕ}
    (hx : x ∈ blockIndices a d k t) (hz : z ∈ blockIndices a d k t)
    (hxy : x ≤ y) (hyz : y ≤ z) : y ∈ blockIndices a d k t := by
  rw [mem_blockIndices] at hx hz ⊢
  refine ⟨lt_of_le_of_lt hyz hz.1, ?_⟩
  constructor
  · exact le_trans hx.2.1 (apTerm_mono a d hxy)
  · exact lt_of_le_of_lt (apTerm_mono a d hyz) hz.2.2

/-- Three consecutive terms of the original progression lie in one block. -/
def HasThreeBlockRun (a d k t : ℕ) : Prop :=
  ∃ j : ℕ, j + 3 ≤ k ∧ ∀ i < 3, InBlock t (apTerm a d (j + i))

/-- If a whole geometric block lies inside a progression's span and its left
endpoint is at least one step past the beginning, the block contains three
consecutive terms. -/
lemma hasThreeBlockRun_of_full_block {a d k t : ℕ}
    (hd : 0 < d) (hk : 0 < k)
    (haL : a ≤ blockStart t) (hdL : d ≤ blockStart t)
    (hend : blockStart (t + 1) ≤ apTerm a d (k - 1)) :
    HasThreeBlockRun a d k t := by
  let L := blockStart t
  let j := (L - a) / d + 1
  have ha_delta : a + (L - a) = L := Nat.add_sub_of_le haL
  have hdiv_le : ((L - a) / d) * d ≤ L - a := Nat.div_mul_le_self _ _
  have hmod_lt : (L - a) % d < d := Nat.mod_lt _ hd
  have hdiv_gt : L - a < ((L - a) / d + 1) * d := by
    have hdecomp := Nat.div_add_mod (L - a) d
    calc
      L - a = (L - a) / d * d + (L - a) % d := by
        simpa [Nat.mul_comm] using hdecomp.symm
      _ < (L - a) / d * d + d := Nat.add_lt_add_left hmod_lt _
      _ = ((L - a) / d + 1) * d := by simp [Nat.add_mul]
  have hj_lower : L < apTerm a d j := by
    calc
      L = a + (L - a) := ha_delta.symm
      _ < a + ((L - a) / d + 1) * d := Nat.add_lt_add_left hdiv_gt _
      _ = apTerm a d j := by rfl
  have hj_upper : apTerm a d j ≤ L + d := by
    calc
      apTerm a d j = a + ((L - a) / d * d + d) := by
        simp [apTerm, j, Nat.add_mul]
      _ ≤ a + ((L - a) + d) :=
        Nat.add_le_add_left (Nat.add_le_add_right hdiv_le d) a
      _ = L + d := by omega
  have hwidth : L + 3 * d < blockStart (t + 1) := by
    have hLpos : 0 < L := blockStart_pos t
    have hfour : L + 3 * d ≤ 4 * L := by omega
    have hfour_hundred : 4 * L < 100 * L := by omega
    simpa [L, blockStart, blockBase, pow_succ, Nat.mul_comm,
      Nat.mul_left_comm, Nat.mul_assoc] using lt_of_le_of_lt hfour hfour_hundred
  have hj2_upper : apTerm a d (j + 2) < blockStart (t + 1) := by
    calc
      apTerm a d (j + 2) = apTerm a d j + 2 * d := by
        simp [apTerm, Nat.add_mul, Nat.add_assoc]
      _ ≤ (L + d) + 2 * d := Nat.add_le_add_right hj_upper _
      _ = L + 3 * d := by omega
      _ < blockStart (t + 1) := hwidth
  have hj2_end : apTerm a d (j + 2) < apTerm a d (k - 1) :=
    lt_of_lt_of_le hj2_upper hend
  have hj_index : j + 2 < k - 1 :=
    (apTerm_strictMono hd).lt_iff_lt.mp hj2_end
  refine ⟨j, by omega, ?_⟩
  intro i hi
  constructor
  · exact le_trans (Nat.le_of_lt hj_lower) (apTerm_mono a d (by omega))
  · exact lt_of_le_of_lt (apTerm_mono a d (by omega)) hj2_upper

/-- A sufficiently large intersection with one block contains that many
consecutive terms of the original progression. -/
lemma exists_block_run_of_le_card {a d k t m : ℕ}
    (hm : m ≤ (blockIndices a d k t).card) :
    ∃ j : ℕ, j + m ≤ k ∧
      ∀ i < m, InBlock t (apTerm a d (j + i)) := by
  by_cases hm0 : m = 0
  · exact ⟨0, by simp [hm0], by simp [hm0]⟩
  have hcard : 0 < (blockIndices a d k t).card := lt_of_lt_of_le (by omega) hm
  have hS : (blockIndices a d k t).Nonempty := Finset.card_pos.mp hcard
  let j := (blockIndices a d k t).min' hS
  have hjmem : j ∈ blockIndices a d k t := Finset.min'_mem _ hS
  have hjle : ∀ x ∈ blockIndices a d k t, j ≤ x := by
    intro x hx
    exact Finset.min'_le _ x hx
  have hrun : ∀ i < m, j + i ∈ blockIndices a d k t := by
    intro i hi
    by_contra hnot
    have hsub : blockIndices a d k t ⊆ Finset.Ico j (j + i) := by
      intro x hx
      have hjx : j ≤ x := hjle x hx
      have hxi : x < j + i := by
        by_contra hge
        have hji : j + i ≤ x := le_of_not_gt hge
        exact hnot (blockIndices_ordConnected hjmem hx (Nat.le_add_right _ _) hji)
      exact Finset.mem_Ico.mpr ⟨hjx, hxi⟩
    have hcard_le : (blockIndices a d k t).card ≤ i := by
      calc
        (blockIndices a d k t).card ≤ (Finset.Ico j (j + i)).card :=
          Finset.card_le_card hsub
        _ = i := by simp
    omega
  have hlast_mem : j + (m - 1) ∈ blockIndices a d k t := by
    apply hrun
    omega
  have hlast_lt : j + (m - 1) < k := (mem_blockIndices.mp hlast_mem).1
  refine ⟨j, by omega, ?_⟩
  intro i hi
  exact (mem_blockIndices.mp (hrun i hi)).2

def blockDichotomyThreshold : ℕ := 2 * blockBase ^ 3 + 2

/-- The fully integral quantitative form of the geometric-block dichotomy.
The first branch supplies three consecutive terms in one even and one odd
block.  The second supplies a nearby block containing at least `k/12` terms. -/
theorem block_dichotomy {a d k : ℕ} (ha : 0 < a) (hd : 0 < d)
    (hk : blockDichotomyThreshold < k) :
    (∃ te to_ : ℕ, te % 2 = 0 ∧ to_ % 2 = 1 ∧
        HasThreeBlockRun a d k te ∧ HasThreeBlockRun a d k to_) ∨
      ∃ t : ℕ, k ≤ 12 * (blockIndices a d k t).card ∧
        blockStart t ≤ blockBase ^ 5 * a := by
  let s := blockIndex a
  let S := nearIndices a d k s
  by_cases hnear : k ≤ 2 * S.card
  · right
    let n := (k - 1) / 12
    have hmaps : ∀ i ∈ S,
        blockIndex (apTerm a d i) ∈ Finset.Ico s (s + 6) := by
      intro i hi
      rw [Finset.mem_Ico]
      have hi' := mem_nearIndices.mp hi
      have htermpos : 0 < apTerm a d i := by
        dsimp [apTerm]
        omega
      constructor
      · apply (Nat.le_log_iff_pow_le one_lt_blockBase htermpos.ne').2
        exact le_trans (blockIndex_spec ha).1 (by simp [apTerm])
      · exact (Nat.log_lt_iff_lt_pow one_lt_blockBase htermpos.ne').2 hi'.2
    have hn_mul : 12 * n ≤ k - 1 := by
      simpa [n, Nat.mul_comm] using Nat.div_mul_le_self (k - 1) 12
    have hph_bound : (Finset.Ico s (s + 6)).card * n < S.card := by
      simp
      omega
    obtain ⟨t, ht, htcard⟩ :=
      Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to hmaps hph_bound
    have ht_bounds : s ≤ t ∧ t < s + 6 := Finset.mem_Ico.mp ht
    have hfiber :
        {i ∈ S | blockIndex (apTerm a d i) = t} = blockIndices a d k t := by
      ext i
      rw [Finset.mem_filter, mem_blockIndices]
      constructor
      · rintro ⟨hiS, hindex⟩
        have hi' := mem_nearIndices.mp hiS
        have htermpos : 0 < apTerm a d i := by
          dsimp [apTerm]
          omega
        exact ⟨hi'.1, (inBlock_iff_blockIndex_eq htermpos).2 hindex⟩
      · rintro ⟨hik, hiblock⟩
        have htermpos : 0 < apTerm a d i := by
          dsimp [apTerm]
          omega
        have hindex : blockIndex (apTerm a d i) = t :=
          (inBlock_iff_blockIndex_eq htermpos).1 hiblock
        have hupper : blockStart (t + 1) ≤ blockStart (s + 6) :=
          blockStart_mono (by omega)
        exact ⟨mem_nearIndices.mpr ⟨hik, lt_of_lt_of_le hiblock.2 hupper⟩, hindex⟩
    have htcard' : n < (blockIndices a d k t).card := by
      simpa [hfiber] using htcard
    have hmod : (k - 1) % 12 < 12 := Nat.mod_lt _ (by norm_num)
    have hdecomp := Nat.div_add_mod (k - 1) 12
    have hkn : k ≤ 12 * (n + 1) := by
      dsimp [n]
      omega
    have hcard_bound : k ≤ 12 * (blockIndices a d k t).card := by
      calc
        k ≤ 12 * (n + 1) := hkn
        _ ≤ 12 * (blockIndices a d k t).card :=
          Nat.mul_le_mul_left 12 (by omega)
    have hstart : blockStart t ≤ blockBase ^ 5 * a := by
      calc
        blockStart t ≤ blockStart (s + 5) := blockStart_mono (by omega)
        _ = blockBase ^ 5 * blockStart s := by
          simp [blockStart, pow_add, Nat.mul_comm]
        _ ≤ blockBase ^ 5 * a :=
          Nat.mul_le_mul_left _ (blockIndex_spec ha).1
    exact ⟨t, hcard_bound, hstart⟩
  · left
    have hfar : 2 * S.card < k := by omega
    let m := k / 2
    have hkpos : 0 < k := by
      have : 0 < blockDichotomyThreshold := by norm_num [blockDichotomyThreshold, blockBase]
      omega
    have hm_lt : m < k := by
      dsimp [m]
      exact Nat.div_lt_self hkpos (by norm_num)
    have hxlarge : blockStart (s + 6) ≤ apTerm a d m := by
      by_contra hnot
      have hxmlt : apTerm a d m < blockStart (s + 6) := Nat.lt_of_not_ge hnot
      have hsub : Finset.range (m + 1) ⊆ S := by
        intro i hi
        have him : i ≤ m := by simpa using hi
        apply mem_nearIndices.mpr
        exact ⟨lt_of_le_of_lt him hm_lt,
          lt_of_le_of_lt (apTerm_mono a d him) hxmlt⟩
      have hcard_le := Finset.card_le_card hsub
      simp only [Finset.card_range] at hcard_le
      dsimp [m] at hcard_le
      omega
    have ha_upper : a < blockStart (s + 1) := (blockIndex_spec ha).2
    have hq5a : blockBase ^ 5 * a < blockStart (s + 6) := by
      calc
        blockBase ^ 5 * a < blockBase ^ 5 * blockStart (s + 1) :=
          (Nat.mul_lt_mul_left (by norm_num [blockBase] : 0 < blockBase ^ 5)).2 ha_upper
        _ = blockStart (s + 6) := by
          simp [blockStart, pow_add]
          ring
    have hA : (blockBase ^ 5 - 1) * a < m * d := by
      have h := lt_of_lt_of_le hq5a hxlarge
      dsimp [apTerm] at h
      norm_num [blockBase] at h ⊢
      omega
    have hmle : m ≤ k := by
      dsimp [m]
      exact Nat.div_le_self _ _
    have hmdle : m * d ≤ k * d := Nat.mul_le_mul_right d hmle
    have hXtwo : 2 * (2 * blockBase ^ 3 * a) < k * d := by
      norm_num [blockBase] at hA ⊢
      omega
    have hYtwo : 2 * ((blockBase ^ 3 + 1) * d) < k * d := by
      calc
        2 * ((blockBase ^ 3 + 1) * d) =
            (2 * (blockBase ^ 3 + 1)) * d := by ring
        _ < k * d := (Nat.mul_lt_mul_right hd).2 (by
          norm_num [blockDichotomyThreshold, blockBase] at hk ⊢
          omega)
    have hsum :
        2 * blockBase ^ 3 * a + (blockBase ^ 3 + 1) * d < k * d := by
      have hdouble :
          2 * (2 * blockBase ^ 3 * a + (blockBase ^ 3 + 1) * d) <
            2 * (k * d) := by
        omega
      exact (Nat.mul_lt_mul_left (by norm_num : 0 < 2)).1 hdouble
    let z := a + (a / d + 1) * d
    have hquot : a / d * d ≤ a := Nat.div_mul_le_self _ _
    have hzle : z ≤ 2 * a + d := by
      dsimp [z]
      simp only [Nat.add_mul, one_mul]
      omega
    have hdz : d ≤ z := by
      dsimp [z]
      simp only [Nat.add_mul, one_mul]
      omega
    have hzpos : 0 < z := lt_of_lt_of_le hd hdz
    have hspan_aux : blockBase ^ 3 * z + d < k * d := by
      have hle := Nat.add_le_add_right (Nat.mul_le_mul_left (blockBase ^ 3) hzle) d
      have hbound : blockBase ^ 3 * (2 * a + d) + d < k * d := by
        norm_num [blockBase] at hsum ⊢
        omega
      exact lt_of_le_of_lt hle hbound
    have hkone : 1 ≤ k := by omega
    have hspan_step : blockBase ^ 3 * z < (k - 1) * d := by
      apply (Nat.add_lt_add_iff_right).mp
      calc
        blockBase ^ 3 * z + d < k * d := hspan_aux
        _ = (k - 1) * d + d := by
          calc
            k * d = ((k - 1) + 1) * d := by rw [Nat.sub_add_cancel hkone]
            _ = (k - 1) * d + d := by simp [Nat.add_mul]
    have hspan : blockBase ^ 3 * z < apTerm a d (k - 1) := by
      exact lt_of_lt_of_le hspan_step (Nat.le_add_left _ _)
    let u := blockIndex z + 1
    have hzu : z < blockStart u := by
      simpa [u] using (blockIndex_spec hzpos).2
    have hlogz : blockStart (blockIndex z) ≤ z := (blockIndex_spec hzpos).1
    have hu2 : blockStart (u + 2) ≤ blockBase ^ 3 * z := by
      calc
        blockStart (u + 2) = blockBase ^ 3 * blockStart (blockIndex z) := by
          simp [u, blockStart, pow_add]
          ring
        _ ≤ blockBase ^ 3 * z := Nat.mul_le_mul_left _ hlogz
    have hu2end : blockStart (u + 2) ≤ apTerm a d (k - 1) :=
      le_trans hu2 (Nat.le_of_lt hspan)
    have ha_u : a ≤ blockStart u :=
      le_trans (Nat.le_add_right a _) (Nat.le_of_lt hzu)
    have hd_u : d ≤ blockStart u := le_trans hdz (Nat.le_of_lt hzu)
    have hrun_u : HasThreeBlockRun a d k u :=
      hasThreeBlockRun_of_full_block hd hkpos ha_u hd_u
        (le_trans (blockStart_mono (by omega)) hu2end)
    have hstart_u_succ : blockStart u ≤ blockStart (u + 1) :=
      blockStart_mono (by omega)
    have hrun_us : HasThreeBlockRun a d k (u + 1) :=
      hasThreeBlockRun_of_full_block hd hkpos
        (le_trans ha_u hstart_u_succ) (le_trans hd_u hstart_u_succ) hu2end
    rcases Nat.mod_two_eq_zero_or_one u with hu | hu
    · have hus : (u + 1) % 2 = 1 := by omega
      exact ⟨u, u + 1, hu, hus, hrun_u, hrun_us⟩
    · have hus : (u + 1) % 2 = 0 := by omega
      exact ⟨u + 1, u, hus, hu, hrun_us, hrun_u⟩

end Erdos984
