/-
Copyright 2026.
Released under Apache 2.0 license.
-/

import ErdosProblems.Erdos438.Basic

/-!
# The Massias construction for Erdős Problem 438

This file verifies, in the kernel, the eleven residue classes modulo `32`
found by Massias.  It also proves exact two-sided block estimates for their
count in `{1, ..., N}`, and hence their limiting density `11 / 32`.
-/

open Filter
open scoped Topology

namespace Erdos438

/-- The eleven residue classes modulo `32` in Massias's construction. -/
def massiasResidues : Finset (ZMod 32) :=
  {1, 5, 9, 13, 14, 17, 21, 25, 26, 29, 30}

/-- Natural representatives of `massiasResidues`, all in `[0, 32)`. -/
def massiasNatResidues : Finset ℕ :=
  {1, 5, 9, 13, 14, 17, 21, 25, 26, 29, 30}

theorem massiasResidues_card : massiasResidues.card = 11 := by
  decide +kernel

theorem massiasNatResidues_card : massiasNatResidues.card = 11 := by
  decide +kernel

/-- No sum of two Massias residues is a square modulo `32`.

This is a finite certificate, checked by the Lean kernel rather than by native
code generation.
-/
theorem massiasResidues_sum_not_square :
    ∀ a ∈ massiasResidues, ∀ b ∈ massiasResidues, ¬ IsSquare (a + b) := by
  decide +kernel

private lemma massiasNatResidues_bounds {r : ℕ} (hr : r ∈ massiasNatResidues) :
    1 ≤ r ∧ r < 32 := by
  simp [massiasNatResidues] at hr
  omega

private lemma mem_massiasNatResidues_iff_zmod {r : ℕ} (hr : r < 32) :
    r ∈ massiasNatResidues ↔ (r : ZMod 32) ∈ massiasResidues := by
  interval_cases r <;> decide +kernel

/-- If two natural numbers occupy Massias residue classes, their sum is not a
natural-number square. -/
theorem massias_nat_sum_not_square {a b : ℕ}
    (ha : a % 32 ∈ massiasNatResidues)
    (hb : b % 32 ∈ massiasNatResidues) :
    ¬ IsSquare (a + b) := by
  intro hs
  have ha_lt : a % 32 < 32 := Nat.mod_lt _ (by omega)
  have hb_lt : b % 32 < 32 := Nat.mod_lt _ (by omega)
  have haZ : (a : ZMod 32) ∈ massiasResidues := by
    rw [← ZMod.natCast_mod a 32]
    exact (mem_massiasNatResidues_iff_zmod ha_lt).mp ha
  have hbZ : (b : ZMod 32) ∈ massiasResidues := by
    rw [← ZMod.natCast_mod b 32]
    exact (mem_massiasNatResidues_iff_zmod hb_lt).mp hb
  rcases hs with ⟨z, hz⟩
  apply massiasResidues_sum_not_square (a : ZMod 32) haZ (b : ZMod 32) hbZ
  refine ⟨(z : ZMod 32), ?_⟩
  simpa using congrArg (fun n : ℕ => (n : ZMod 32)) hz

/-- The truncation of the periodic Massias construction to `{1, ..., N}`. -/
def massiasSet (N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter fun n => n % 32 ∈ massiasNatResidues

@[simp] theorem mem_massiasSet {N n : ℕ} :
    n ∈ massiasSet N ↔ 1 ≤ n ∧ n ≤ N ∧ n % 32 ∈ massiasNatResidues := by
  simp [massiasSet, and_assoc]

theorem massiasSet_subset_Icc (N : ℕ) : massiasSet N ⊆ Finset.Icc 1 N := by
  intro n hn
  exact Finset.mem_Icc.mpr ⟨(mem_massiasSet.mp hn).1, (mem_massiasSet.mp hn).2.1⟩

theorem massiasSet_squareSumFree (N : ℕ) : SquareSumFree (massiasSet N) := by
  intro a ha b hb
  exact massias_nat_sum_not_square (mem_massiasSet.mp ha).2.2 (mem_massiasSet.mp hb).2.2

theorem massiasSet_admissible (N : ℕ) : admissible N (massiasSet N) :=
  ⟨massiasSet_subset_Icc N, massiasSet_squareSumFree N⟩

private def massiasBlocks (q : ℕ) : Finset ℕ :=
  ((Finset.range q).product massiasNatResidues).image fun kr => 32 * kr.1 + kr.2

private lemma massiasBlocks_card (q : ℕ) : (massiasBlocks q).card = 11 * q := by
  rw [massiasBlocks, Finset.card_image_iff.mpr]
  · simp [massiasNatResidues_card, mul_comm]
  · rintro ⟨k, r⟩ hkr ⟨l, s⟩ hls heq
    have hkr' := Finset.mem_product.mp
      (show (k, r) ∈ (Finset.range q).product massiasNatResidues from hkr)
    have hls' := Finset.mem_product.mp
      (show (l, s) ∈ (Finset.range q).product massiasNatResidues from hls)
    have hr := massiasNatResidues_bounds hkr'.2
    have hs := massiasNatResidues_bounds hls'.2
    change 32 * k + r = 32 * l + s at heq
    apply Prod.ext
    · omega
    · omega

private lemma massiasBlocks_mono (N : ℕ) :
    massiasBlocks (N / 32) ⊆ massiasSet N := by
  intro n hn
  rcases Finset.mem_image.mp hn with ⟨⟨k, r⟩, hkr, rfl⟩
  have hkr' := Finset.mem_product.mp hkr
  rw [Finset.mem_range] at hkr'
  have hr := massiasNatResidues_bounds hkr'.2
  have hdiv := Nat.div_mul_le_self N 32
  apply mem_massiasSet.mpr
  constructor
  · omega
  constructor
  · omega
  · have hmod : (32 * k + r) % 32 = r := by omega
    simpa [hmod] using hkr'.2

/-- Every complete block of length `32` contributes all eleven Massias
residues. -/
theorem massiasSet_card_lower (N : ℕ) :
    11 * (N / 32) ≤ (massiasSet N).card := by
  rw [← massiasBlocks_card (N / 32)]
  exact Finset.card_le_card (massiasBlocks_mono N)

private lemma massiasSet_subset_blocks (N : ℕ) :
    massiasSet N ⊆ massiasBlocks (N / 32 + 1) := by
  intro n hn
  have hn' := mem_massiasSet.mp hn
  let k := n / 32
  let r := n % 32
  have hr_lt : r < 32 := Nat.mod_lt _ (by omega)
  have hr : r ∈ massiasNatResidues := hn'.2.2
  have hk : k < N / 32 + 1 := by
    dsimp [k]
    exact Nat.lt_succ_of_le (Nat.div_le_div_right hn'.2.1)
  rw [massiasBlocks, Finset.mem_image]
  refine ⟨(k, r), ?_, ?_⟩
  · exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr hk, hr⟩
  · dsimp [k, r]
    omega

/-- At most eleven further terms occur after the last complete block. -/
theorem massiasSet_card_upper (N : ℕ) :
    (massiasSet N).card ≤ 11 * (N / 32 + 1) := by
  calc
    (massiasSet N).card ≤ (massiasBlocks (N / 32 + 1)).card :=
      Finset.card_le_card (massiasSet_subset_blocks N)
    _ = 11 * (N / 32 + 1) := massiasBlocks_card _

private lemma tendsto_natDiv_div (d : ℕ) (_hd : 0 < d) :
    Tendsto (fun N : ℕ => ((N / d : ℕ) : ℝ) / (N : ℝ)) atTop
      (𝓝 ((d : ℝ)⁻¹)) := by
  have h := tendsto_nat_floor_mul_div_atTop
    (R := ℝ) (a := (d : ℝ)⁻¹) (inv_nonneg.mpr (Nat.cast_nonneg d))
  have h' := h.comp tendsto_natCast_atTop_atTop
  refine h'.congr' (Eventually.of_forall fun N => ?_)
  simp only [Function.comp_apply]
  rw [show (d : ℝ)⁻¹ * (N : ℝ) = (N : ℝ) / (d : ℝ) by
    simp [div_eq_mul_inv, mul_comm]]
  rw [Nat.floor_div_eq_div]

/-- The Massias construction has asymptotic density exactly `11 / 32`. -/
theorem tendsto_massiasSet_density :
    Tendsto (fun N : ℕ => ((massiasSet N).card : ℝ) / (N : ℝ)) atTop
      (𝓝 ((11 : ℝ) / 32)) := by
  have hdiv := tendsto_natDiv_div 32 (by omega)
  have hlower :
      Tendsto (fun N : ℕ => ((11 * (N / 32) : ℕ) : ℝ) / (N : ℝ)) atTop
        (𝓝 ((11 : ℝ) / 32)) := by
    have hconst : Tendsto (fun _ : ℕ => (11 : ℝ)) atTop (𝓝 11) :=
      tendsto_const_nhds
    have h := hconst.mul hdiv
    simpa [div_eq_mul_inv, mul_assoc] using h
  have herror :
      Tendsto (fun N : ℕ => (11 : ℝ) / (N : ℝ)) atTop (𝓝 0) := by
    exact tendsto_const_nhds.div_atTop
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hupper :
      Tendsto (fun N : ℕ => ((11 * (N / 32 + 1) : ℕ) : ℝ) / (N : ℝ)) atTop
        (𝓝 ((11 : ℝ) / 32)) := by
    have h := hlower.add herror
    convert h using 1
    · funext N
      push_cast
      ring
    · norm_num
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper ?_ ?_
  · filter_upwards [eventually_atTop.2 ⟨1, fun _ h => h⟩] with N hN
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    exact div_le_div_of_nonneg_right (by exact_mod_cast massiasSet_card_lower N) hNpos.le
  · filter_upwards [eventually_atTop.2 ⟨1, fun _ h => h⟩] with N hN
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    exact div_le_div_of_nonneg_right (by exact_mod_cast massiasSet_card_upper N) hNpos.le

/-- The explicit Massias set gives the corresponding lower bound for the
extremal function. -/
theorem massias_lower_bound (N : ℕ) :
    (massiasSet N).card ≤ extremalSize N :=
  card_le_extremalSize (massiasSet_admissible N)

end Erdos438
