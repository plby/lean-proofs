/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/
import ErdosProblems.Erdos55.UpperSampling

/-!
# Dyadic assembly of the arbitrary-color upper bound

The sampling theorem supplies, for each fixed `r`, enlarged robust blocks at
all sufficiently large scales.  This file chooses such a block at every
dyadic scale, takes their union, and proves both required global properties:
every `r`-coloring represents all sufficiently large integers, and the
counting function is bounded by an absolute constant times `r log^2 N`.
-/

open scoped BigOperators

open Filter

namespace Erdos55

/-- The deterministic property needed from a block at dyadic scale `k`.

The last clause packages the finite pigeonhole step: for every `r`-coloring
of the ambient naturals, one color class inside the block covers the stated
interval by distinct subset sums. -/
def IsGoodRDyadicBlock (r k : ℕ) (S : Finset ℕ) : Prop :=
  (∀ n ∈ S, 2 ^ k ≤ n ∧ n < 2 ^ (k + 1)) ∧
    S.card ≤ 8000 * r * k ∧
    ∀ color : ℕ → Fin r, ∃ c : Fin r,
      Erdos54.CoversInterval (S.filter fun n ↦ color n = c)
        (1000 * k * 2 ^ k) (2200 * k * 2 ^ k)

/-- A family of good dyadic blocks for a fixed positive number of colors. -/
structure RDyadicBlockSystem (r : ℕ) where
  blocks : ℕ → Finset ℕ
  firstScale : ℕ
  colors_pos : 0 < r
  empty_before : ∀ k < firstScale, blocks k = ∅
  good : ∀ k ≥ firstScale, IsGoodRDyadicBlock r k (blocks k)

/-- An exact CFP robust block yields the colored dyadic-block property. -/
theorem isGoodRDyadicBlock_of_isRRobustBlock {r k : ℕ} (hr : 0 < r)
    {S : Finset ℕ}
    (hS : IsRRobustBlock r (2 ^ k) (Erdos54.ceilSixLog (2 ^ k)) S) :
    IsGoodRDyadicBlock r k S := by
  classical
  rcases hS with ⟨hSIco, hScard, hcover⟩
  have hqUpper := Erdos54.ceilSixLog_two_pow_le k
  have hqLower := Erdos54.ceilSixLog_two_pow_ge k
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    have hn' := Finset.mem_Ico.mp (hSIco hn)
    rw [Nat.pow_succ]
    omega
  · rw [hScard]
    nlinarith
  · intro color
    let q := Erdos54.ceilSixLog (2 ^ k)
    have huniv : (Finset.univ : Finset (Fin r)).Nonempty := by
      exact ⟨⟨0, hr⟩, Finset.mem_univ _⟩
    have haverage : (Finset.univ : Finset (Fin r)).card * (640 * q) ≤ S.card := by
      rw [Finset.card_univ, Fintype.card_fin, hScard]
      dsimp only [q]
      nlinarith
    obtain ⟨c, _hcuniv, hc⟩ :=
      Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to
        (s := S) (t := (Finset.univ : Finset (Fin r)))
        (f := color) (n := 640 * q)
        (fun _ _ ↦ Finset.mem_univ _) huniv haverage
    refine ⟨c, ?_⟩
    have hfull := hcover (S.filter fun n ↦ color n = c)
      (Finset.filter_subset _ _) (by simpa [q] using hc)
    intro n hn
    apply hfull
    rw [Finset.mem_Icc] at hn ⊢
    constructor
    · calc
        160 * Erdos54.ceilSixLog (2 ^ k) * 2 ^ k ≤
            1000 * k * 2 ^ k := by
          apply Nat.mul_le_mul_right
          omega
        _ ≤ n := hn.1
    · calc
        n ≤ 2200 * k * 2 ^ k := hn.2
        _ ≤ 560 * Erdos54.ceilSixLog (2 ^ k) * 2 ^ k := by
          apply Nat.mul_le_mul_right
          omega

/-- Choose one good enlarged block at every sufficiently large dyadic scale. -/
theorem nonempty_rDyadicBlockSystem_of_eventually_rRobustBlocks
    {r : ℕ} (hr : 0 < r)
    (hblocks : ∀ᶠ x : ℕ in atTop,
      ∃ S : Finset ℕ,
        IsRRobustBlock r x (Erdos54.ceilSixLog x) S) :
    Nonempty (RDyadicBlockSystem r) := by
  classical
  rw [eventually_atTop] at hblocks
  obtain ⟨K, hK⟩ := hblocks
  have hklePow : ∀ k : ℕ, k ≤ 2 ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [Nat.pow_succ]
        have hone : 1 ≤ 2 ^ k := Nat.one_le_two_pow
        omega
  have hexists : ∀ k ≥ K, ∃ S : Finset ℕ, IsGoodRDyadicBlock r k S := by
    intro k hk
    obtain ⟨S, hS⟩ := hK (2 ^ k) (hk.trans (hklePow k))
    exact ⟨S, isGoodRDyadicBlock_of_isRRobustBlock hr hS⟩
  let blocks : ℕ → Finset ℕ := fun k ↦
    if hk : K ≤ k then Classical.choose (hexists k hk) else ∅
  refine ⟨
    { blocks := blocks
      firstScale := K
      colors_pos := hr
      empty_before := ?_
      good := ?_ }⟩
  · intro k hk
    simp [blocks, not_le_of_gt hk]
  · intro k hk
    simpa only [blocks, dif_pos hk] using Classical.choose_spec (hexists k hk)

/-- The union of all sufficiently late dyadic blocks. -/
def RDyadicBlockSystem.carrier {r : ℕ} (D : RDyadicBlockSystem r) : Set ℕ :=
  {n | ∃ k, D.firstScale ≤ k ∧ n ∈ D.blocks k}

@[simp]
theorem RDyadicBlockSystem.mem_carrier {r : ℕ} {D : RDyadicBlockSystem r} {n : ℕ} :
    n ∈ D.carrier ↔ ∃ k, D.firstScale ≤ k ∧ n ∈ D.blocks k :=
  Iff.rfl

theorem RDyadicBlockSystem.block_subset_carrier {r : ℕ} (D : RDyadicBlockSystem r)
    {k : ℕ} (hk : D.firstScale ≤ k) : (D.blocks k : Set ℕ) ⊆ D.carrier := by
  intro n hn
  exact ⟨k, hk, hn⟩

theorem RDyadicBlockSystem.positive {r : ℕ} (D : RDyadicBlockSystem r) :
    IsPositiveNatSet D.carrier := by
  rw [isPositiveNatSet_iff_zero_not_mem]
  rintro ⟨k, hk, hzero⟩
  have hbounds := (D.good k hk).1 0 hzero
  have : 0 < 2 ^ k := pow_pos (by omega) _
  omega

/-- Convert an ordinary finite subset-sum witness into the subtype witness
used by the public arbitrary-color definition. -/
theorem isMonochromaticSum_of_subsetSumValues {r : ℕ} {A : Set ℕ}
    {T : Finset ℕ} {color : A → Fin r} {c : Fin r} {n : ℕ}
    (hTA : ∀ x ∈ T, x ∈ A)
    (hcolor : ∀ (x : ℕ) (hx : x ∈ T), color ⟨x, hTA x hx⟩ = c)
    (hn : n ∈ Erdos54.subsetSumValues T) :
    IsMonochromaticSum A color n := by
  rw [Erdos54.mem_subsetSumValues] at hn
  obtain ⟨u, huT, hsum⟩ := hn
  let inclusion : ↑u ↪ ↑A :=
    ⟨fun x ↦ ⟨x.1, hTA x.1 (huT x.2)⟩,
      fun _ _ h ↦ Subtype.ext (congrArg (fun z : ↑A ↦ (z : ℕ)) h)⟩
  let v : Finset ↑A := u.attach.map inclusion
  refine ⟨c, v, ?_, ?_⟩
  · intro y hy
    simp only [v, Finset.mem_map] at hy
    obtain ⟨x, _hx, rfl⟩ := hy
    exact hcolor x.1 (huT x.2)
  · simp only [v, Finset.sum_map]
    calc
      (∑ x ∈ u.attach, ((inclusion x : ↑A) : ℕ)) =
          ∑ x ∈ u.attach, (x : ℕ) := by rfl
      _ = ∑ x ∈ u, x := Finset.sum_attach u (fun x ↦ x)
      _ = n := hsum

/-- Every sufficiently late block represents its entire covered interval
monochromatically under a coloring of the global union. -/
theorem RDyadicBlockSystem.monochromatic_on_block {r : ℕ}
    (D : RDyadicBlockSystem r) (color : D.carrier → Fin r)
    {k n : ℕ} (hk : D.firstScale ≤ k)
    (hn : n ∈ Finset.Icc (1000 * k * 2 ^ k) (2200 * k * 2 ^ k)) :
    IsMonochromaticSum D.carrier color n := by
  classical
  let blockColor : ℕ → Fin r := fun x ↦
    if hx : x ∈ D.blocks k then color ⟨x, D.block_subset_carrier hk hx⟩
    else ⟨0, D.colors_pos⟩
  obtain ⟨c, hcover⟩ := (D.good k hk).2.2 blockColor
  let T := (D.blocks k).filter fun x ↦ blockColor x = c
  have hTS : T ⊆ D.blocks k := Finset.filter_subset _ _
  have hTA : ∀ x ∈ T, x ∈ D.carrier := by
    intro x hx
    exact D.block_subset_carrier hk (hTS hx)
  have hmono : ∀ (x : ℕ) (hx : x ∈ T), color ⟨x, hTA x hx⟩ = c := by
    intro x hx
    have hxT := Finset.mem_filter.mp hx
    simpa [blockColor, hxT.1] using hxT.2
  exact isMonochromaticSum_of_subsetSumValues hTA hmono (hcover hn)

/-- The union of the enlarged dyadic blocks is Ramsey `r`-complete. -/
theorem RDyadicBlockSystem.ramseyComplete {r : ℕ} (D : RDyadicBlockSystem r) :
    RamseyComplete r D.carrier := by
  intro color
  let K₀ := max D.firstScale 2000
  have hKfirst : D.firstScale ≤ K₀ := le_max_left _ _
  have hKchain : 2 * 1000 ≤ K₀ := le_max_right _ _
  let L : ℕ → ℕ := fun k ↦ 1000 * k * 2 ^ k
  let U : ℕ → ℕ := fun k ↦ 2200 * k * 2 ^ k
  have hLU : ∀ k ≥ K₀, L k ≤ U k := by
    intro k _hk
    exact Erdos54.dyadic_interval_nonempty (a := 1000) (b := 2200)
      (by omega) (by omega)
  have hchain : ∀ k ≥ K₀, L (k + 1) ≤ U k + 1 := by
    intro k hk
    exact Erdos54.dyadic_interval_chain (a := 1000) (b := 2200)
      (by omega) (by omega) (hKchain.trans hk)
  have hunbounded : ∀ n, ∃ k ≥ K₀, n ≤ U k := by
    intro n
    refine ⟨max K₀ n, le_max_left _ _, ?_⟩
    have hnle : n ≤ max K₀ n := le_max_right _ _
    have hpow : 1 ≤ 2 ^ max K₀ n := Nat.one_le_two_pow
    change n ≤ 2200 * max K₀ n * 2 ^ max K₀ n
    calc
      n ≤ max K₀ n := hnle
      _ ≤ 2200 * max K₀ n := by nlinarith
      _ ≤ 2200 * max K₀ n * 2 ^ max K₀ n := by
        simpa only [Nat.mul_assoc, Nat.mul_one] using
          Nat.mul_le_mul_left (2200 * max K₀ n) hpow
  refine ⟨L K₀, ?_⟩
  intro n hn
  obtain ⟨k, hk, hnk⟩ :=
    Erdos54.exists_mem_interval_of_chain L U K₀ hLU hchain hunbounded n hn
  apply D.monochromatic_on_block color (hKfirst.trans hk)
  simpa [L, U] using hnk

/-! ## The uniform quadratic logarithmic count -/

theorem RDyadicBlockSystem.prefix_subset_blocks {r : ℕ}
    (D : RDyadicBlockSystem r) {N n : ℕ}
    (hnN : n ∈ Finset.Icc 1 N) (hnA : n ∈ D.carrier) :
    n ∈ (Finset.range (Nat.log 2 N + 1)).biUnion D.blocks := by
  obtain ⟨k, hkfirst, hnk⟩ := hnA
  have hkpow : 2 ^ k ≤ n := (D.good k hkfirst).1 n hnk |>.1
  have hklog : k ≤ Nat.log 2 N :=
    Nat.le_log_of_pow_le (by norm_num) (hkpow.trans (Finset.mem_Icc.mp hnN).2)
  exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_range.mpr (by omega), hnk⟩

/-- Natural-number form of the uniform count bound. -/
theorem RDyadicBlockSystem.countUpTo_le_log_sq {r : ℕ}
    (D : RDyadicBlockSystem r) (N : ℕ) :
    countUpTo D.carrier N ≤ 8000 * r * (Nat.log 2 N + 1) ^ 2 := by
  classical
  let m := Nat.log 2 N
  have hprefix :
      (Finset.Icc 1 N).filter (fun n ↦ n ∈ D.carrier) ⊆
        (Finset.range (m + 1)).biUnion D.blocks := by
    intro n hn
    have hn' := Finset.mem_filter.mp hn
    simpa [m] using D.prefix_subset_blocks hn'.1 hn'.2
  have hcard : countUpTo D.carrier N ≤
      ((Finset.range (m + 1)).biUnion D.blocks).card := by
    simpa [countUpTo] using Finset.card_le_card hprefix
  have hunion : ((Finset.range (m + 1)).biUnion D.blocks).card ≤
      ∑ k ∈ Finset.range (m + 1), (D.blocks k).card :=
    Finset.card_biUnion_le
  have hsum : (∑ k ∈ Finset.range (m + 1), (D.blocks k).card) ≤
      ∑ k ∈ Finset.range (m + 1), 8000 * r * k := by
    apply Finset.sum_le_sum
    intro k hk
    by_cases hkfirst : D.firstScale ≤ k
    · exact (D.good k hkfirst).2.1
    · rw [D.empty_before k (by omega)]
      simp
  have hlinear : (∑ k ∈ Finset.range (m + 1), 8000 * r * k) ≤
      ∑ _k ∈ Finset.range (m + 1), 8000 * r * m := by
    apply Finset.sum_le_sum
    intro k hk
    have hkm : k ≤ m := by simpa using Finset.mem_range.mp hk
    exact Nat.mul_le_mul_left _ hkm
  have hfinal : (∑ _k ∈ Finset.range (m + 1), 8000 * r * m) ≤
      8000 * r * (m + 1) ^ 2 := by
    have heq : (∑ _k ∈ Finset.range (m + 1), 8000 * r * m) =
        (m + 1) * (8000 * r * m) := by simp
    rw [heq]
    nlinarith
  exact hcard.trans
    (hunion.trans (hsum.trans (hlinear.trans (by simpa [m] using hfinal))))

/-- The absolute real constant used for every number of colors. -/
noncomputable def upperCountingConstant : ℝ :=
  8000 * (2 / Real.log 2) ^ 2

theorem upperCountingConstant_pos : 0 < upperCountingConstant := by
  have hlogtwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  exact mul_pos (by norm_num)
    (sq_pos_of_pos (div_pos (by norm_num) hlogtwo))

/-- Real form of the count bound, with a constant independent of `r`. -/
theorem RDyadicBlockSystem.countUpTo_le_uniform {r : ℕ}
    (D : RDyadicBlockSystem r) {N : ℕ} (hN : 2 ≤ N) :
    (countUpTo D.carrier N : ℝ) ≤
      upperCountingConstant * (r : ℝ) * Real.log (N : ℝ) ^ 2 := by
  have hnat := D.countUpTo_le_log_sq N
  have hnatReal : (countUpTo D.carrier N : ℝ) ≤
      (8000 : ℝ) * (r : ℝ) * (((Nat.log 2 N + 1 : ℕ) : ℝ)) ^ 2 := by
    exact_mod_cast hnat
  have hlogtwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlog : (Nat.log 2 N : ℝ) ≤ Real.log (N : ℝ) / Real.log 2 := by
    simpa [Real.logb] using Real.natLog_le_logb N 2
  have hratio : 1 ≤ Real.log (N : ℝ) / Real.log 2 := by
    rw [le_div_iff₀ hlogtwo]
    have hNreal : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    simpa only [one_mul] using
      Real.log_le_log (by norm_num : (0 : ℝ) < 2) hNreal
  have hmplus : ((Nat.log 2 N + 1 : ℕ) : ℝ) ≤
      2 * (Real.log (N : ℝ) / Real.log 2) := by
    norm_num only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
    linarith
  have hsquare : (((Nat.log 2 N + 1 : ℕ) : ℝ)) ^ 2 ≤
      (2 * (Real.log (N : ℝ) / Real.log 2)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hmplus 2
  calc
    (countUpTo D.carrier N : ℝ) ≤
        (8000 : ℝ) * (r : ℝ) * (((Nat.log 2 N + 1 : ℕ) : ℝ)) ^ 2 :=
      hnatReal
    _ ≤ (8000 : ℝ) * (r : ℝ) *
        (2 * (Real.log (N : ℝ) / Real.log 2)) ^ 2 :=
      mul_le_mul_of_nonneg_left hsquare (by positivity)
    _ = upperCountingConstant * (r : ℝ) * Real.log (N : ℝ) ^ 2 := by
      dsimp [upperCountingConstant]
      ring

/-- The Conlon--Fox--Pham construction with an absolute constant uniform in
the number of colors. -/
theorem conlonFoxPham_upperBound : CFPUpperBound := by
  refine ⟨upperCountingConstant, upperCountingConstant_pos, ?_⟩
  intro r hr
  have hblocks := eventually_exists_rRobustBlock r (by omega)
  let D : RDyadicBlockSystem r :=
    Classical.choice
      (nonempty_rDyadicBlockSystem_of_eventually_rRobustBlocks (by omega) hblocks)
  let A : PositiveNatSet := PositiveNatSet.ofSet D.carrier D.positive
  refine ⟨A, ?_, ⟨2, ?_⟩⟩
  · change RamseyComplete r D.carrier
    exact D.ramseyComplete
  · intro N hN
    change (countUpTo D.carrier N : ℝ) ≤
      upperCountingConstant * (r : ℝ) * Real.log (N : ℝ) ^ 2
    exact D.countUpTo_le_uniform hN

end Erdos55
