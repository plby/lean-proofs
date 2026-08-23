/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 253.
https://www.erdosproblems.com/forum/thread/253

Informal authors:
- J. W. S. Cassels

Statement authors:
- Formal Conjectures authors

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos253.md
- https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/253.lean
-/
/-
Erdős Problem 253.  The counterexample below is a Fibonacci-block
version of Cassels's summable irrational-rotation construction.
-/

import Mathlib

namespace Erdos253

open BigOperators Filter Set
open scoped Topology goldenRatio ENNReal

/-! The two utility definitions used by the Formal Conjectures statement. -/

def subsetSums {M : Type*} [AddCommMonoid M] (A : Set M) : Set M :=
  {n | ∃ B : Finset M, ↑B ⊆ A ∧ n = ∑ i ∈ B, i}

def Set.IsAPOfLengthWith {α : Type*} [AddCommMonoid α]
    (s : Set α) (l : ℕ∞) (a d : α) : Prop :=
  ENat.card s = l ∧ s = {a + n • d | (n : ℕ) (_ : n < l)}

def Set.IsAPOfLength {α : Type*} [AddCommMonoid α]
    (s : Set α) (l : ℕ∞) : Prop :=
  ∃ a d : α, Set.IsAPOfLengthWith s l a d

/-- The predicate in the upstream statement. -/
@[inline]
def RepresentsAPs (a : ℕ → ℕ) : Prop :=
  StrictMono a ∧ ∀ l, Set.IsAPOfLength l ⊤ → (subsetSums (Set.range a) ∩ l).Infinite

private def blockBound (k : ℕ) : ℕ := 2 * (k + 1)

/-- The union of short blocks of multiples of Fibonacci denominators. -/
private def fibBlocks : Set ℕ :=
  {n | ∃ k t : ℕ, 1 ≤ t ∧ t ≤ blockBound k ∧ n = t * Nat.fib (k + 1)}

private lemma fibBlocks_pos {n : ℕ} (hn : n ∈ fibBlocks) : 0 < n := by
  rcases hn with ⟨k, t, ht, -, rfl⟩
  exact Nat.mul_pos ht (Nat.fib_pos.2 (Nat.succ_pos k))

private lemma fibBlocks_infinite : fibBlocks.Infinite := by
  apply Set.infinite_of_injective_forall_mem (f := fun k ↦ Nat.fib (k + 2))
  · exact Nat.fib_add_two_strictMono.injective
  · intro k
    refine ⟨k + 1, 1, by omega, ?_, by simp⟩
    simp [blockBound]
    omega

private noncomputable def baseSeq (n : ℕ) : ℕ := Nat.nth (· ∈ fibBlocks) n

private lemma baseSeq_strictMono : StrictMono baseSeq :=
  Nat.nth_strictMono fibBlocks_infinite

private lemma range_baseSeq : Set.range baseSeq = fibBlocks := by
  change Set.range (Nat.nth (fun n ↦ n ∈ fibBlocks)) = fibBlocks
  exact Nat.range_nth_of_infinite fibBlocks_infinite

/-! ### The irrational-rotation estimate -/

private lemma abs_goldenConj_lt_two_thirds : |Real.goldenConj| < (2 / 3 : ℝ) := by
  rw [abs_of_neg Real.goldenConj_neg]
  have hs5 : Real.sqrt 5 < 7 / 3 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5), Real.sqrt_nonneg 5]
  simp only [Real.goldenConj]
  linarith

private lemma fib_le_two_pow (n : ℕ) : Nat.fib (n + 1) ≤ 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [show n + 1 + 1 = n + 2 by omega, Nat.fib_add_two]
      calc
        Nat.fib n + Nat.fib (n + 1) ≤ Nat.fib (n + 1) + Nat.fib (n + 1) := by
          exact Nat.add_le_add_right Nat.fib_le_fib_succ _
        _ ≤ 2 ^ n + 2 ^ n := Nat.add_le_add ih ih
        _ = 2 ^ (n + 1) := by rw [pow_succ]; omega

private lemma block_norm_bound (k t : ℕ) :
    ‖(t * Nat.fib (k + 1)) • (Real.goldenRatio : UnitAddCircle)‖ ≤
      (t : ℝ) * |Real.goldenConj| ^ (k + 1) := by
  rw [← AddCircle.coe_nsmul, nsmul_eq_mul, Nat.cast_mul]
  have hident := Real.fib_succ_sub_goldenRatio_mul_fib (k + 1)
  have hreal :
      (t : ℝ) * (Nat.fib (k + 1) * Real.goldenRatio) -
          (t : ℝ) * Nat.fib (k + 2) = -(t : ℝ) * Real.goldenConj ^ (k + 1) := by
    nlinarith
  rw [show (t : ℝ) * Nat.fib (k + 1) * Real.goldenRatio =
      ((t : ℝ) * (Nat.fib (k + 1) * Real.goldenRatio) -
        (t : ℝ) * Nat.fib (k + 2)) + (t : ℝ) * Nat.fib (k + 2) by ring]
  rw [AddCircle.coe_add, show (((t : ℝ) * Nat.fib (k + 2) : ℝ) : UnitAddCircle) = 0 by
    rw [AddCircle.coe_eq_zero_iff]; exact ⟨t * Nat.fib (k + 2), by norm_num⟩, add_zero]
  rw [hreal]
  calc
    ‖((-(t : ℝ) * Real.goldenConj ^ (k + 1) : ℝ) : UnitAddCircle)‖
        ≤ |-(t : ℝ) * Real.goldenConj ^ (k + 1)| :=
          QuotientAddGroup.norm_mk_le_norm
    _ = (t : ℝ) * |Real.goldenConj| ^ (k + 1) := by
      rw [abs_mul, abs_neg, abs_of_nonneg (Nat.cast_nonneg t), abs_pow]

private noncomputable def blockWeight (k t : ℕ) : ℝ :=
  if 1 ≤ t ∧ t ≤ blockBound k then
    (t : ℝ) * |Real.goldenConj| ^ (k + 1)
  else 0

private lemma summable_blockWeight : Summable (Function.uncurry blockWeight) := by
  rw [summable_prod_of_nonneg (by
    rintro ⟨k, t⟩
    simp only [Function.uncurry]
    unfold blockWeight
    split <;> positivity)]
  constructor
  · intro k
    apply summable_of_hasFiniteSupport
    refine (Set.finite_Iic (blockBound k)).subset ?_
    intro t ht
    change blockWeight k t ≠ 0 at ht
    change t ≤ blockBound k
    by_contra h
    simp [blockWeight, h] at ht
  · have hgeom : Summable (fun k : ℕ ↦
        (4 * (k + 1) ^ 2 : ℝ) * (2 / 3 : ℝ) ^ (k + 1)) := by
      have h := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 2
        (r := (2 / 3 : ℝ)) (by norm_num)
      simpa [Nat.cast_add, Nat.cast_one, mul_assoc] using
        (h.comp_injective Nat.succ_injective).mul_left (4 : ℝ)
    have hmajor : ∀ k : ℕ,
        ∑' t : ℕ, blockWeight k t ≤
          (4 * (k + 1) ^ 2 : ℝ) * (2 / 3 : ℝ) ^ (k + 1) := by
      intro k
      rw [tsum_eq_sum' (s := Finset.Icc 1 (blockBound k))]
      · calc
          ∑ t ∈ Finset.Icc 1 (blockBound k), blockWeight k t
              = ∑ t ∈ Finset.Icc 1 (blockBound k),
                  (t : ℝ) * |Real.goldenConj| ^ (k + 1) := by
                    apply Finset.sum_congr rfl
                    intro t ht
                    simp [blockWeight, Finset.mem_Icc.mp ht]
          _ ≤ ((blockBound k : ℕ) : ℝ) ^ 2 * |Real.goldenConj| ^ (k + 1) := by
                rw [← Finset.sum_mul]
                gcongr
                calc
                  ∑ t ∈ Finset.Icc 1 (blockBound k), (t : ℝ)
                      ≤ ∑ _t ∈ Finset.Icc 1 (blockBound k), (blockBound k : ℝ) := by
                        gcongr with t ht
                        exact_mod_cast (Finset.mem_Icc.mp ht).2
                  _ ≤ (blockBound k : ℝ) ^ 2 := by
                        rw [Finset.sum_const, nsmul_eq_mul]
                        simp [Nat.card_Icc, pow_two]
          _ ≤ (4 * (k + 1) ^ 2 : ℝ) * (2 / 3 : ℝ) ^ (k + 1) := by
                have hc : |Real.goldenConj| ^ (k + 1) ≤ (2 / 3 : ℝ) ^ (k + 1) := by
                  gcongr
                  exact le_of_lt abs_goldenConj_lt_two_thirds
                simp only [blockBound, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add,
                  Nat.cast_one]
                rw [show (2 * ((k : ℝ) + 1)) ^ 2 = 4 * ((k : ℝ) + 1) ^ 2 by ring]
                gcongr
      · intro t ht
        change blockWeight k t ≠ 0 at ht
        change t ∈ Finset.Icc 1 (blockBound k)
        simp only [Finset.mem_Icc]
        by_contra hout
        simp [blockWeight, hout] at ht
    exact Summable.of_nonneg_of_le
      (fun k ↦ tsum_nonneg fun t ↦ by
        change 0 ≤ blockWeight k t
        unfold blockWeight
        split <;> positivity) hmajor
      hgeom

/-! Every member of `fibBlocks` is assigned one of its block representations.  This
turns the preceding double-series estimate into an estimate for the increasing
enumeration, without requiring the representation to be unique. -/

private def IsBlockRep (n : ℕ) (p : ℕ × ℕ) : Prop :=
  1 ≤ p.2 ∧ p.2 ≤ blockBound p.1 ∧ n = p.2 * Nat.fib (p.1 + 1)

private lemma mem_fibBlocks_iff (n : ℕ) :
    n ∈ fibBlocks ↔ ∃ p : ℕ × ℕ, IsBlockRep n p := by
  simp only [fibBlocks, Set.mem_ofPred_eq, IsBlockRep]
  constructor
  · rintro ⟨k, t, ht, htb, rfl⟩
    exact ⟨(k, t), ht, htb, rfl⟩
  · rintro ⟨⟨k, t⟩, ht, htb, rfl⟩
    exact ⟨k, t, ht, htb, rfl⟩

private noncomputable def fibRep (n : ℕ) : ℕ × ℕ :=
  by
    classical
    exact if hn : n ∈ fibBlocks then
      Classical.choose ((mem_fibBlocks_iff n).mp hn) else (0, 0)

private lemma fibRep_spec {n : ℕ} (hn : n ∈ fibBlocks) : IsBlockRep n (fibRep n) := by
  rw [fibRep, dif_pos hn]
  exact Classical.choose_spec ((mem_fibBlocks_iff n).mp hn)

private lemma fibRep_injOn : Set.InjOn fibRep fibBlocks := by
  intro n hn m hm hrep
  have hn' := fibRep_spec hn
  have hm' := fibRep_spec hm
  rw [hrep] at hn'
  exact hn'.2.2.trans hm'.2.2.symm

private lemma baseSeq_mem (i : ℕ) : baseSeq i ∈ fibBlocks := by
  rw [← range_baseSeq]
  exact ⟨i, rfl⟩

private lemma fibRep_baseSeq_injective : Function.Injective (fun i ↦ fibRep (baseSeq i)) := by
  intro i j hij
  exact baseSeq_strictMono.injective
    (fibRep_injOn (baseSeq_mem i) (baseSeq_mem j) hij)

private lemma summable_base_norm :
    Summable (fun i : ℕ ↦ ‖baseSeq i • (Real.goldenRatio : UnitAddCircle)‖) := by
  have hw : Summable (fun i : ℕ ↦ Function.uncurry blockWeight (fibRep (baseSeq i))) :=
    summable_blockWeight.comp_injective fibRep_baseSeq_injective
  apply Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) _ hw
  intro i
  have hs := fibRep_spec (baseSeq_mem i)
  rcases hrep : fibRep (baseSeq i) with ⟨k, t⟩
  simp only [IsBlockRep, hrep] at hs
  rw [hs.2.2]
  simp only [Function.uncurry]
  simpa [blockWeight, hs.1, hs.2.1] using block_norm_bound k t

/-! ### Gaps in the increasing enumeration -/

private def blockCap (k : ℕ) : ℕ := blockBound k * Nat.fib (k + 1)

private lemma exists_lt_blockCap (x : ℕ) : ∃ k, x < blockCap k := by
  refine ⟨x + 1, ?_⟩
  have hf : 1 ≤ Nat.fib (x + 1 + 1) := Nat.fib_pos.2 (by omega)
  simp only [blockCap, blockBound]
  nlinarith

private noncomputable def scale (x : ℕ) : ℕ := Nat.find (exists_lt_blockCap x)

private lemma lt_blockCap_scale (x : ℕ) : x < blockCap (scale x) :=
  Nat.find_spec (exists_lt_blockCap x)

private lemma blockCap_le_of_lt_scale {x j : ℕ} (hj : j < scale x) : blockCap j ≤ x := by
  by_contra h
  have hle : scale x ≤ j :=
    Nat.find_min' (exists_lt_blockCap x) (Nat.lt_of_not_ge h)
  omega

private noncomputable def nextBlockPoint (x : ℕ) : ℕ :=
  (x / Nat.fib (scale x + 1) + 1) * Nat.fib (scale x + 1)

private lemma nextBlockPoint_mem (x : ℕ) : nextBlockPoint x ∈ fibBlocks := by
  let k := scale x
  let q := Nat.fib (k + 1)
  have hq : 0 < q := Nat.fib_pos.2 (by omega)
  have hx : x < blockBound k * q := lt_blockCap_scale x
  have ht : x / q + 1 ≤ blockBound k := by
    exact Nat.succ_le_iff.mpr ((Nat.div_lt_iff_lt_mul hq).2 hx)
  exact ⟨k, x / q + 1, Nat.succ_pos _, ht, rfl⟩

private lemma nextBlockPoint_bounds (x : ℕ) :
    x < nextBlockPoint x ∧ nextBlockPoint x ≤ x + Nat.fib (scale x + 1) := by
  let q := Nat.fib (scale x + 1)
  have hq : 0 < q := Nat.fib_pos.2 (by omega)
  constructor
  · simpa [nextBlockPoint, q, Nat.add_mul] using Nat.lt_div_mul_add (a := x) hq
  · simp only [nextBlockPoint, Nat.add_mul, one_mul]
    exact Nat.add_le_add_right (Nat.div_mul_le_self x _) _

private lemma baseSeq_succ_le (n : ℕ) :
    baseSeq (n + 1) ≤ nextBlockPoint (baseSeq n) := by
  have hmem := nextBlockPoint_mem (baseSeq n)
  by_contra h
  have hlt : nextBlockPoint (baseSeq n) < baseSeq (n + 1) := Nat.lt_of_not_ge h
  have hle : nextBlockPoint (baseSeq n) ≤ baseSeq n := by
    exact Nat.le_nth_of_lt_nth_succ hlt hmem
  exact (Nat.not_le_of_gt (nextBlockPoint_bounds (baseSeq n)).1) hle

private lemma baseSeq_gap_le (n : ℕ) :
    baseSeq (n + 1) - baseSeq n ≤ Nat.fib (scale (baseSeq n) + 1) := by
  have hmono : baseSeq n ≤ baseSeq (n + 1) :=
    baseSeq_strictMono.monotone (by omega)
  have hs := baseSeq_succ_le n
  have hb := (nextBlockPoint_bounds (baseSeq n)).2
  omega

private lemma scale_baseSeq_tendsto : Tendsto (fun n ↦ scale (baseSeq n)) atTop atTop := by
  refine tendsto_atTop.2 ?_
  intro K
  have hbase : Tendsto baseSeq atTop atTop := baseSeq_strictMono.tendsto_atTop
  filter_upwards [hbase.eventually (eventually_ge_atTop
      (2 * (K + 1) * 2 ^ K))] with n hn
  by_contra hk
  have hsk : scale (baseSeq n) < K := Nat.lt_of_not_ge hk
  have hfib : Nat.fib (scale (baseSeq n) + 1) ≤ 2 ^ scale (baseSeq n) :=
    fib_le_two_pow _
  have hpow : 2 ^ scale (baseSeq n) ≤ 2 ^ K := Nat.pow_le_pow_right (by omega) hsk.le
  have hsle : scale (baseSeq n) + 1 ≤ K + 1 := by omega
  have hcap := lt_blockCap_scale (baseSeq n)
  simp only [blockCap, blockBound] at hcap
  nlinarith

private lemma fib_succ_le_two_mul (k : ℕ) (hk : 0 < k) :
    Nat.fib (k + 1) ≤ 2 * Nat.fib k := by
  cases k with
  | zero => omega
  | succ j =>
      rw [show j + 1 + 1 = j + 2 by omega, Nat.fib_add_two]
      have h := Nat.fib_le_fib_succ (n := j)
      omega

private lemma ratio_baseSeq_tendsto :
    Tendsto (fun n ↦ (baseSeq (n + 1) : ℝ) / baseSeq n) atTop (𝓝 1) := by
  have hkreal : Tendsto (fun n ↦ (scale (baseSeq n) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp scale_baseSeq_tendsto
  have hu : Tendsto (fun n ↦ 1 + (scale (baseSeq n) : ℝ)⁻¹) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add (tendsto_inv_atTop_zero.comp hkreal)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · exact Eventually.of_forall fun n ↦ by
      apply (le_div_iff₀ (Nat.cast_pos.2 (fibBlocks_pos (baseSeq_mem n)))).2
      norm_num
      exact_mod_cast baseSeq_strictMono.monotone (by omega)
  · filter_upwards [scale_baseSeq_tendsto.eventually_ge_atTop 1] with n hk
    let x := baseSeq n
    let k := scale x
    let q := Nat.fib (k + 1)
    have hx : 0 < x := fibBlocks_pos (baseSeq_mem n)
    have hk' : 0 < k := hk
    have hprev : blockCap (k - 1) ≤ x :=
      blockCap_le_of_lt_scale (Nat.sub_lt hk' (by omega))
    have hcap : 2 * k * Nat.fib k ≤ x := by
      simpa [blockCap, blockBound, Nat.sub_add_cancel hk'] using hprev
    have hq : q ≤ 2 * Nat.fib k := fib_succ_le_two_mul k hk'
    have hkq : k * q ≤ x := by nlinarith
    have hqx : (q : ℝ) ≤ (x : ℝ) / k := by
      apply (le_div_iff₀ (Nat.cast_pos.2 hk')).2
      exact_mod_cast (show q * k ≤ x by simpa [mul_comm] using hkq)
    have hnext : baseSeq (n + 1) ≤ x + q :=
      (baseSeq_succ_le n).trans (nextBlockPoint_bounds x).2
    calc
      (baseSeq (n + 1) : ℝ) / baseSeq n
          ≤ ((x : ℝ) + q) / x := by
            gcongr
            exact_mod_cast hnext
      _ = 1 + (q : ℝ) / x := by field_simp
      _ ≤ 1 + ((x : ℝ) / k) / x := by gcongr
      _ = 1 + (k : ℝ)⁻¹ := by field_simp

/-! ### Fibonacci blocks meet every residue class -/

private def fibPerm (d : ℕ) : Equiv.Perm (ZMod (d + 1) × ZMod (d + 1)) where
  toFun p := (p.2, p.1 + p.2)
  invFun p := (p.2 - p.1, p.1)
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp

private lemma fibPerm_iterate (d n : ℕ) :
    ((fibPerm d : (ZMod (d + 1) × ZMod (d + 1)) →
      (ZMod (d + 1) × ZMod (d + 1)))^[n]) (0, 1) =
      ((Nat.fib n : ZMod (d + 1)), (Nat.fib (n + 1) : ZMod (d + 1))) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      apply Prod.ext
      · simp [fibPerm]
      · simp only [fibPerm, Equiv.coe_fn_mk]
        norm_cast
        rw [show n + 1 + 1 = n + 2 by omega, Nat.fib_add_two]

private noncomputable def fibPeriod (d : ℕ) : ℕ := orderOf (fibPerm d)

private lemma fibPeriod_pos (d : ℕ) : 0 < fibPeriod d := orderOf_pos _

private lemma fib_period_one (d j : ℕ) :
    Nat.fib ((j + 1) * fibPeriod d + 1) ≡ 1 [MOD d + 1] := by
  let p := fibPeriod d
  have hp : fibPerm d ^ ((j + 1) * p) = 1 := by
    rw [mul_comm, pow_mul, show p = orderOf (fibPerm d) by rfl,
      pow_orderOf_eq_one, one_pow]
  have heval : (fibPerm d ^ ((j + 1) * p)) (0, 1) = (0, 1) := by rw [hp]; rfl
  rw [Equiv.Perm.coe_pow] at heval
  rw [fibPerm_iterate] at heval
  dsimp [p] at heval
  exact ZMod.natCast_eq_natCast_iff _ _ (d + 1) |>.mp (congrArg Prod.snd heval)

private def residueCoeff (r d : ℕ) : ℕ := if r % d = 0 then d else r % d

private lemma residueCoeff_pos {r d : ℕ} (hd : 0 < d) : 0 < residueCoeff r d := by
  unfold residueCoeff
  split <;> omega

private lemma residueCoeff_le {r d : ℕ} (hd : 0 < d) : residueCoeff r d ≤ d := by
  unfold residueCoeff
  split
  · exact le_rfl
  · exact (Nat.mod_lt r hd).le

private lemma residueCoeff_mod (r d : ℕ) : residueCoeff r d ≡ r [MOD d] := by
  change residueCoeff r d % d = r % d
  unfold residueCoeff
  split <;> simp_all

private noncomputable def residueHit (r d j : ℕ) : ℕ :=
  residueCoeff r d * Nat.fib ((j + d + 1) * fibPeriod (d - 1) + 1)

private lemma residueHit_mem {r d : ℕ} (hd : 0 < d) (j : ℕ) :
    residueHit r d j ∈ fibBlocks := by
  let p := fibPeriod (d - 1)
  let k := (j + d + 1) * p
  have hp : 0 < p := fibPeriod_pos _
  have htd : residueCoeff r d ≤ d := residueCoeff_le hd
  have hdk : d ≤ 2 * (k + 1) := by
    have : d ≤ k := by
      dsimp [k]
      nlinarith
    omega
  exact ⟨k, residueCoeff r d, residueCoeff_pos hd, htd.trans hdk, rfl⟩

private lemma residueHit_mod {r d : ℕ} (hd : 0 < d) (j : ℕ) :
    residueHit r d j ≡ r [MOD d] := by
  have hdform : d - 1 + 1 = d := Nat.sub_add_cancel hd
  have hf := fib_period_one (d - 1) (j + d)
  rw [hdform] at hf
  simpa [residueHit, add_assoc] using (residueCoeff_mod r d).mul hf

private lemma residueHit_strictMono {r d : ℕ} (hd : 0 < d) :
    StrictMono (residueHit r d) := by
  intro i j hij
  let p := fibPeriod (d - 1)
  have hp : 0 < p := fibPeriod_pos _
  have ht : 0 < residueCoeff r d := residueCoeff_pos hd
  have hindex :
      (i + d + 1) * p + 1 < (j + d + 1) * p + 1 := by nlinarith
  have htwo : 2 ≤ (i + d + 1) * p + 1 := by nlinarith
  have hfib : Nat.fib ((i + d + 1) * p + 1) <
      Nat.fib ((j + d + 1) * p + 1) :=
    (Nat.fib_lt_fib htwo).2 hindex
  simpa [residueHit, p] using Nat.mul_lt_mul_of_pos_left hfib ht

private lemma fibBlocks_residue_infinite (r : ℕ) {d : ℕ} (hd : 0 < d) :
    {n : ℕ | n ∈ fibBlocks ∧ n ≡ r [MOD d]}.Infinite := by
  apply Set.infinite_of_injective_forall_mem
      (f := residueHit r d) (residueHit_strictMono hd).injective
  intro j
  exact ⟨residueHit_mem hd j, residueHit_mod hd j⟩

private lemma range_baseSeq_tail (N : ℕ) :
    Set.range (fun i ↦ baseSeq (N + i)) = fibBlocks ∩ Set.Ici (baseSeq N) := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨baseSeq_mem _, baseSeq_strictMono.monotone (Nat.le_add_right _ _)⟩
  · rintro ⟨hx, hNx⟩
    rw [← range_baseSeq] at hx
    rcases hx with ⟨j, rfl⟩
    have hNj : N ≤ j := (baseSeq_strictMono.le_iff_le).mp hNx
    exact ⟨j - N, by simp [Nat.add_sub_of_le hNj]⟩

private lemma singleton_subsetSum {A : Set ℕ} {x : ℕ} (hx : x ∈ A) :
    x ∈ subsetSums A := by
  refine ⟨{x}, ?_, by simp⟩
  simpa using hx

private lemma tail_represents_APs (N : ℕ) :
    ∀ l, Set.IsAPOfLength l ⊤ →
      (subsetSums (Set.range fun i ↦ baseSeq (N + i)) ∩ l).Infinite := by
  intro l hl
  rcases hl with ⟨a, d, hcard, rfl⟩
  have hd : 0 < d := by
    by_contra hd0
    have : d = 0 := Nat.eq_zero_of_not_pos hd0
    subst d
    simp at hcard
  let S : Set ℕ := {n | n ∈ fibBlocks ∧ n ≡ a [MOD d]}
  have hS : S.Infinite := fibBlocks_residue_infinite a hd
  have htail : (S \ Set.Iio (max (baseSeq N) a)).Infinite := by
    exact hS.sdiff (Set.finite_Iio _)
  apply htail.mono
  intro x hx
  rcases hx with ⟨⟨hblock, hmod⟩, hxlarge⟩
  have hxN : baseSeq N ≤ x := by
    have := Nat.le_of_not_gt hxlarge
    exact (le_max_left _ _).trans this
  have hxa : a ≤ x := by
    have := Nat.le_of_not_gt hxlarge
    exact (le_max_right _ _).trans this
  constructor
  · apply singleton_subsetSum
    rw [range_baseSeq_tail]
    exact ⟨hblock, hxN⟩
  · simp only [Set.mem_ofPred_eq]
    rcases (Nat.modEq_iff_dvd' hxa).mp hmod.symm with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    refine ⟨by simp, ?_⟩
    symm
    calc
      x = a + (x - a) := (Nat.add_sub_of_le hxa).symm
      _ = a + d * n := by rw [hn]
      _ = a + n * d := by rw [mul_comm]

/-! ### An explicit infinite family far from the small circle arc -/

private lemma fib_add_three (n : ℕ) :
    Nat.fib (n + 3) = 2 * Nat.fib (n + 1) + Nat.fib n := by
  rw [show n + 3 = (n + 1) + 2 by omega, Nat.fib_add_two, Nat.fib_add_two]
  omega

private lemma even_fib_three_mul (j : ℕ) : Even (Nat.fib (3 * j)) := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [show 3 * (j + 1) = 3 * j + 3 by ring, fib_add_three]
      exact (even_two_mul _).add ih

private lemma odd_fib_three_mul_add_one (j : ℕ) : Odd (Nat.fib (3 * j + 1)) := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [show 3 * (j + 1) + 1 = (3 * j + 1) + 3 by ring, fib_add_three]
      exact (even_two_mul _).add_odd ih

private def farPoint (j : ℕ) : ℕ := Nat.fib (6 * (j + 1)) / 2

private lemma two_mul_farPoint (j : ℕ) : 2 * farPoint j = Nat.fib (6 * (j + 1)) := by
  apply Nat.two_mul_div_two_of_even
  simpa [show 6 * (j + 1) = 3 * (2 * (j + 1)) by ring] using
    even_fib_three_mul (2 * (j + 1))

private lemma farPoint_strictMono : StrictMono farPoint := by
  intro i j hij
  have hindex : 6 * (i + 1) < 6 * (j + 1) := by omega
  have htwo : 2 ≤ 6 * (i + 1) := by omega
  have hfib := (Nat.fib_lt_fib htwo).2 hindex
  have hi := two_mul_farPoint i
  have hj := two_mul_farPoint j
  omega

private lemma goldenConj_pow_small (j : ℕ) :
    |Real.goldenConj ^ (6 * (j + 1))| < (1 / 2 : ℝ) := by
  rw [abs_pow]
  have hpow : |Real.goldenConj| ^ (6 * (j + 1)) <
      (2 / 3 : ℝ) ^ (6 * (j + 1)) := by
    exact pow_lt_pow_left₀ abs_goldenConj_lt_two_thirds (abs_nonneg _)
      (by omega)
  have hmono : (2 / 3 : ℝ) ^ (6 * (j + 1)) ≤ (2 / 3 : ℝ) ^ 2 := by
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  norm_num at hmono ⊢
  linarith

private lemma farPoint_circle_eq (j : ℕ) :
    farPoint j • (Real.goldenRatio : UnitAddCircle) =
      (((1 / 2 : ℝ) - Real.goldenConj ^ (6 * (j + 1)) / 2 : ℝ) : UnitAddCircle) := by
  let n := 6 * (j + 1)
  let m : ℕ := Nat.fib (n + 1) / 2
  have heven : 2 * farPoint j = Nat.fib n := two_mul_farPoint j
  have hodd : 2 * m + 1 = Nat.fib (n + 1) := by
    apply Nat.two_mul_div_two_add_one_of_odd
    simpa [show n + 1 = 3 * (2 * (j + 1)) + 1 by simp [n]; ring] using
      odd_fib_three_mul_add_one (2 * (j + 1))
  have hident := Real.fib_succ_sub_goldenRatio_mul_fib n
  rw [← AddCircle.coe_nsmul, nsmul_eq_mul]
  have hreal :
      (farPoint j : ℝ) * Real.goldenRatio =
        (m : ℝ) + ((1 / 2 : ℝ) - Real.goldenConj ^ n / 2) := by
    have hevenR : (2 : ℝ) * farPoint j = Nat.fib n := by exact_mod_cast heven
    have hoddR : (2 : ℝ) * m + 1 = Nat.fib (n + 1) := by
      exact_mod_cast hodd
    rw [← hevenR, ← hoddR] at hident
    nlinarith [hident]
  have hm : (((m : ℕ) : ℝ) : UnitAddCircle) = 0 := by
    rw [AddCircle.coe_eq_zero_iff]
    exact ⟨Int.ofNat m, by simp⟩
  rw [hreal, AddCircle.coe_add]
  rw [hm, zero_add]

private lemma farPoint_circle_norm_gt (j : ℕ) :
    (1 / 4 : ℝ) < ‖farPoint j • (Real.goldenRatio : UnitAddCircle)‖ := by
  rw [farPoint_circle_eq]
  let u := Real.goldenConj ^ (6 * (j + 1))
  have huabs : |u| < (1 / 2 : ℝ) := goldenConj_pow_small j
  have hueven : 0 ≤ u := by
    dsimp [u]
    rw [show 6 * (j + 1) = 2 * (3 * (j + 1)) by ring, pow_mul]
    positivity
  have hu : u < (1 / 2 : ℝ) := lt_of_le_of_lt (le_abs_self u) huabs
  have hx0 : 0 ≤ (1 / 2 : ℝ) - u / 2 := by linarith
  have hrep : |(1 / 2 : ℝ) - u / 2| ≤ |(1 : ℝ)| / 2 := by
    rw [abs_of_nonneg hx0]
    simp
    linarith
  rw [(AddCircle.norm_coe_eq_abs_iff (p := (1 : ℝ)) (by norm_num)).2 hrep]
  rw [abs_of_nonneg hueven] at huabs
  rw [abs_of_nonneg hx0]
  linarith

private lemma subsetSum_circle_norm_le_tsum
    (a : ℕ → ℕ)
    (hsum : Summable (fun i ↦ ‖a i • (Real.goldenRatio : UnitAddCircle)‖))
    {z : ℕ} (hz : z ∈ subsetSums (Set.range a)) :
    ‖z • (Real.goldenRatio : UnitAddCircle)‖ ≤
      ∑' i, ‖a i • (Real.goldenRatio : UnitAddCircle)‖ := by
  classical
  rcases hz with ⟨B, hB, rfl⟩
  choose idx hidx using fun x : {x // x ∈ B} ↦ hB x.property
  have hidx_inj : Function.Injective idx := by
    intro x y hxy
    apply Subtype.ext
    rw [← hidx x, ← hidx y, hxy]
  have heq :
      (∑ i ∈ B, i) • (Real.goldenRatio : UnitAddCircle) =
        ∑ x : {x // x ∈ B}, a (idx x) • (Real.goldenRatio : UnitAddCircle) := by
    rw [← Finset.sum_nsmul_assoc, ← B.sum_attach, Finset.attach_eq_univ]
    apply Finset.sum_congr rfl
    intro x _
    rw [hidx x]
  rw [heq]
  calc
    ‖∑ x : {x // x ∈ B}, a (idx x) • (Real.goldenRatio : UnitAddCircle)‖
        ≤ ∑ x : {x // x ∈ B}, ‖a (idx x) • (Real.goldenRatio : UnitAddCircle)‖ :=
          norm_sum_le _ _
    _ = ∑' x : {x // x ∈ B},
          ‖a (idx x) • (Real.goldenRatio : UnitAddCircle)‖ := by rw [tsum_fintype]
    _ ≤ ∑' i, ‖a i • (Real.goldenRatio : UnitAddCircle)‖ := by
      exact tsum_comp_le_tsum_of_inj hsum (fun _ ↦ norm_nonneg _) hidx_inj

private lemma exists_small_tail :
    ∃ N : ℕ, ∑' i : ℕ,
      ‖baseSeq (N + i) • (Real.goldenRatio : UnitAddCircle)‖ < (1 / 4 : ℝ) := by
  let f : ℕ → ℝ := fun i ↦ ‖baseSeq i • (Real.goldenRatio : UnitAddCircle)‖
  have ht : Tendsto (fun N ↦ ∑' i, f (i + N)) atTop (𝓝 0) := by
    exact tendsto_sum_nat_add f
  have hev : ∀ᶠ N in atTop, (∑' i, f (i + N)) < (1 / 4 : ℝ) :=
    (tendsto_order.1 ht).2 _ (by norm_num)
  rcases hev.exists with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  simpa [f, add_comm] using hN

private lemma tail_subsetSums_not_cofinite (N : ℕ)
    (hN : ∑' i : ℕ, ‖baseSeq (N + i) • (Real.goldenRatio : UnitAddCircle)‖ <
      (1 / 4 : ℝ)) :
    subsetSums (Set.range fun i ↦ baseSeq (N + i)) ∉ Filter.cofinite := by
  let a : ℕ → ℕ := fun i ↦ baseSeq (N + i)
  have hs : Summable (fun i ↦ ‖a i • (Real.goldenRatio : UnitAddCircle)‖) := by
    exact summable_base_norm.comp_injective (fun _ _ h ↦ Nat.add_left_cancel h)
  have hfar : ∀ j, farPoint j ∉ subsetSums (Set.range a) := by
    intro j hj
    have hle := subsetSum_circle_norm_le_tsum a hs hj
    have hgt := farPoint_circle_norm_gt j
    dsimp [a] at hle
    linarith
  have hinf : (subsetSums (Set.range a))ᶜ.Infinite := by
    apply Set.infinite_of_injective_forall_mem
      (f := farPoint) farPoint_strictMono.injective
    intro j
    exact hfar j
  intro hcof
  exact hinf (mem_cofinite.mp hcof)

/-! The remaining construction is phrased as a single package, proved below from the
Fibonacci block estimates. -/

private theorem exists_cassels_sequence :
    ∃ a : ℕ → ℕ, 0 < a 0 ∧ StrictMono a ∧
      (∀ l, Set.IsAPOfLength l ⊤ → (subsetSums (Set.range a) ∩ l).Infinite) ∧
      Tendsto (fun n ↦ (a (n + 1) : ℝ) / a n) atTop (𝓝 1) ∧
      subsetSums (Set.range a) ∉ Filter.cofinite := by
  obtain ⟨N, hN⟩ := exists_small_tail
  let a : ℕ → ℕ := fun i ↦ baseSeq (N + i)
  refine ⟨a, ?_, ?_, ?_, ?_, ?_⟩
  · exact fibBlocks_pos (baseSeq_mem (N + 0))
  · intro i j hij
    exact baseSeq_strictMono (Nat.add_lt_add_left hij N)
  · exact tail_represents_APs N
  · have hshift : Tendsto (fun n : ℕ ↦ N + n) atTop atTop := by
      simpa [add_comm] using tendsto_add_atTop_nat N
    have h := ratio_baseSeq_tendsto.comp hshift
    apply h.congr'
    exact Eventually.of_forall fun n ↦ by simp [a, add_assoc]
  · exact tail_subsetSums_not_cofinite N hN

/-- Erdős Problem 253 has a negative answer. -/
theorem erdos_253 : ¬ ∀ a : ℕ → ℕ, 0 < a 0 →
    RepresentsAPs a → (Filter.atTop.Tendsto (fun n ↦ (a <| n + 1 : ℝ) / a n) (𝓝 1)) →
      subsetSums (Set.range a) ∈ Filter.cofinite := by
  rintro h
  obtain ⟨a, ha0, hmono, haps, hratio, hnot⟩ := exists_cassels_sequence
  exact hnot (h a ha0 ⟨hmono, haps⟩ hratio)

end Erdos253
