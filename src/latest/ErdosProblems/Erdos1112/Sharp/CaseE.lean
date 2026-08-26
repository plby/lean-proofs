/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Copyright 2026 Johan Land.
Licensed under the Apache License, Version 2.0; see LICENSE and NOTICE.
Modified for this repository and Lean/Mathlib 4.33.0. -/
/-
Erdős Problem 1112.
Informal proof: Johan Land, using Claude Fable 5 and Claude Opus 4.8.
Formal proof: Johan Land, using Claude Fable 5 and Claude Opus 4.8.
GPT-5.5 and Gemini 3.1 supplied advice and adversarial review.
Source: https://www.erdosproblems.com/1112#post-7375
https://github.com/beetree/math_erdos_1112/tree/63ed94d3e802782aeb521095c17d6109a2dc57b5
Original Lean version: 4.27.0.
Original Mathlib commit: a3a10db0e9d66acbebf76c5e6a135066525ac900.
-/
/-
Case E (the eta-box lemma): the universal η-box for `a ≥ 12`, `μ ≥ 12`
(with `a ∤ M`, `a ∤ b+M`). This branch carries the bulk of the hard core
(71,421 of the 83,251 triples with M ≤ 120). Paper: the bounded subset-sum covering section.

Route (mirrors the paper): with `η := M·b⁻¹ mod a` (`b` is a unit mod `a`
by `gcd(a,b) = 1`), the side hypotheses pin `η ∈ [2, a−2]`:
  * `η ≠ 0`  ⟺ `a ∤ M`,
  * `η ≠ a−1` ⟺ `a ∤ b+M`  (`b + M ≡ b(1+η)`),
  * `η ≠ 1`  from `h = M − b ∈ [1, a−2]` (hard core).
Set `t := min(η, a−η) ∈ [2, a/2]` and `(Y, Z) := (t−1, ⌊(a−1)/t⌋)`
(`⌊(a−1)/t⌋ = ⌈(a−t)/t⌉`). The box offsets `j·b + k·M ≡ b·(j + k·η) (mod a)`
sweep a complete residue system: `{j + k·t}` is `[0, t(Z+1)−1] ⊇ [0, a−1]`
when `t = η` (division algorithm), and `{j + k·(a−t)} ≡ {j − k·t}` covers
the mirrored interval when `t = a−η` (`eta_box_steps`). Hence
`(a, b, M, x, Y, Z)` with `x := ⌈(M−1+Y·b+Z·M)/a⌉` is a `FrameCert`; the
quadratic endpoint bound `2·(t+Z) ≤ a+4` (from `(t−2)(a−2t) ≥ 0`) plus
`M ≥ a+12` close the budget `x+Y+Z ≤ M−1` per the paper's threshold algebra
`a·σ ≤ (a−σ)·M`.
-/
import ErdosProblems.Erdos1112.Sharp.Frame
import ErdosProblems.Erdos1112.Sharp.Lift

namespace Erdos1112
namespace Proof

/-- Box coverage of `ℤ/a` by steps of `η`: every `w < a` is congruent to
`j + k·η (mod a)` with `j ≤ t−1`, `k ≤ ⌊(a−1)/t⌋` for `t := min(η, a−η)`.
For `t = η` this is the division algorithm `w = j + k·t`; for `t = a−η`
the step acts as `−t`, and `k := ⌈(a−w)/t⌉`, `j := k·t − (a−w)` gives
`j + k·η = (k−1)·a + w`. -/
private lemma eta_box_steps {a η w : ℕ} (hη1 : 1 ≤ η) (hηa : η + 1 ≤ a)
    (hw : w < a) :
    ∃ j k, j + 1 ≤ min η (a - η) ∧ k ≤ (a - 1) / min η (a - η) ∧
      (j + k * η) % a = w % a := by
  set t := min η (a - η) with htdef
  have ht1 : 1 ≤ t := by omega
  rcases le_total η (a - η) with hcase | hcase
  · -- `t = η`: division algorithm.
    have htη : t = η := by omega
    refine ⟨w % t, w / t, ?_, Nat.div_le_div_right (by omega), ?_⟩
    · have := Nat.mod_lt w (show 0 < t by omega)
      omega
    · rw [← htη, Nat.mod_add_div' w t]
  · -- `t = a − η`: the step `η = a − t` acts as `−t` mod `a`.
    have hηt : η + t = a := by omega
    rcases Nat.lt_or_ge w t with hwt | hwt
    · exact ⟨w, 0, by omega, Nat.zero_le _, by rw [Nat.zero_mul, Nat.add_zero]⟩
    · have hd1 := Nat.div_add_mod (a - w + t - 1) t
      have hd2 := Nat.mod_lt (a - w + t - 1) (show 0 < t by omega)
      have hd3 := Nat.div_mul_le_self (a - w + t - 1) t
      set k := (a - w + t - 1) / t with hkdef
      have hcomm : t * k = k * t := Nat.mul_comm t k
      have hklo : a - w ≤ k * t := by omega
      have hkhi : k * t ≤ a - w + t - 1 := hd3
      have hk1 : 1 ≤ k := by
        rcases Nat.eq_zero_or_pos k with hk0 | hk
        · rw [hk0, Nat.zero_mul] at hklo
          omega
        · exact hk
      refine ⟨k * t - (a - w), k, by omega, Nat.div_le_div_right (by omega), ?_⟩
      have hbr : k * η + k * t = k * a := by
        rw [← Nat.mul_add, hηt]
      have hone : (k - 1) * a + a = k * a := by
        have h : k - 1 + 1 = k := by omega
        calc (k - 1) * a + a = (k - 1 + 1) * a := by ring
          _ = k * a := by rw [h]
      have hjk : k * t - (a - w) + k * η = (k - 1) * a + w := by omega
      rw [hjk, Nat.add_comm, Nat.add_mul_mod_self_right]

/-- Ceiling-padding bounds: if `n ≤ a·B` then `x := ⌈n/a⌉ = (n+a−1)/a`
satisfies both `n ≤ a·x` and `x ≤ B`. -/
private lemma ceil_pad {a n B : ℕ} (ha : 0 < a) (hnB : n ≤ a * B) :
    n ≤ a * ((n + a - 1) / a) ∧ (n + a - 1) / a ≤ B := by
  constructor
  · have h1 := Nat.div_add_mod (n + a - 1) a
    have h2 := Nat.mod_lt (n + a - 1) ha
    omega
  · have h3 : n + a - 1 < (B + 1) * a := by
      have hexp : (B + 1) * a = a * B + a := by ring
      omega
    have h4 := (Nat.div_lt_iff_lt_mul ha).mpr h3
    omega

set_option maxHeartbeats 800000 in
-- Allow extra elaboration work for the arithmetic and combinatorial case splits.
/-- **Case E (η-box)**: `a ∤ M`, `a ∤ b + M`, `a ≥ 12`, `μ = M − a ≥ 12`. -/
theorem caseE {a b M : ℕ} (hc : HardCore a b M)
    (hnD : ¬ a ∣ M) (hnP : ¬ a ∣ (b + M))
    (ha : 12 ≤ a) (hμ : 12 ≤ M - a) : SharpTriple a b M := by
  obtain ⟨ha0, hab, hbM, hco, hδ⟩ := hc
  have : NeZero a := ⟨by omega⟩
  -- `b` is a unit mod `a`; `η := M·b⁻¹`.
  have hunit : IsUnit (b : ZMod a) := (ZMod.isUnit_iff_coprime b a).mpr hco.symm
  have hbmul : (b : ZMod a) * ↑hunit.unit⁻¹ = 1 := hunit.mul_val_inv
  set η : ℕ := ((M : ZMod a) * ↑hunit.unit⁻¹).val with hηdef
  have hηlt : η < a := ZMod.val_lt _
  have hηcast : (η : ZMod a) = (M : ZMod a) * ↑hunit.unit⁻¹ := by
    rw [hηdef, ZMod.natCast_val, ZMod.cast_id]
  have hbη : (b : ZMod a) * (η : ZMod a) = (M : ZMod a) := by
    rw [hηcast]
    calc (b : ZMod a) * ((M : ZMod a) * ↑hunit.unit⁻¹)
        = (M : ZMod a) * ((b : ZMod a) * ↑hunit.unit⁻¹) := by ring
      _ = (M : ZMod a) := by rw [hbmul, mul_one]
  -- η ∉ {0, 1, a−1}: the three excluded residue lines.
  have hη0 : η ≠ 0 := by
    intro h0
    apply hnD
    have hM0 : (M : ZMod a) = ((0 : ℕ) : ZMod a) := by
      rw [← hbη, h0]
      push_cast
      ring
    exact Nat.modEq_zero_iff_dvd.mp ((ZMod.natCast_eq_natCast_iff _ _ _).mp hM0)
  have hη1 : η ≠ 1 := by
    intro h1
    have hMb : (M : ZMod a) = ((b : ℕ) : ZMod a) := by
      rw [← hbη, h1]
      push_cast
      ring
    have hmb := (ZMod.natCast_eq_natCast_iff _ _ _).mp hMb
    have hdvd : a ∣ M - b := (Nat.modEq_iff_dvd' (le_of_lt hbM)).mp hmb.symm
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  have hηa1 : η ≠ a - 1 := by
    intro he
    apply hnP
    have hm1 : ((a - 1 : ℕ) : ZMod a) = -1 := by
      have hself := ZMod.natCast_self a
      rw [Nat.cast_sub (by omega : 1 ≤ a), hself]
      push_cast
      ring
    have hsum : ((b + M : ℕ) : ZMod a) = ((0 : ℕ) : ZMod a) := by
      push_cast
      rw [← hbη, he, hm1]
      ring
    exact Nat.modEq_zero_iff_dvd.mp ((ZMod.natCast_eq_natCast_iff _ _ _).mp hsum)
  -- the box parameters
  set t : ℕ := min η (a - η) with htdef
  have ht2 : 2 ≤ t := by omega
  have h2t : 2 * t ≤ a := by omega
  set Z : ℕ := (a - 1) / t with hZdef
  have hZt : Z * t ≤ a - 1 := by
    rw [hZdef]
    exact Nat.div_mul_le_self _ _
  -- quadratic endpoint bound: 2·(t+Z) ≤ a+4 via (t−2)(a−2t) ≥ 0
  have hσ : 2 * (t + Z) ≤ a + 4 := by
    have h1 : (Z : ℤ) * t ≤ (a : ℤ) - 1 := by
      have h := hZt
      zify [show 1 ≤ a by omega] at h
      exact h
    have h2 : (2 : ℤ) ≤ (t : ℤ) := by exact_mod_cast ht2
    have h3 : 2 * (t : ℤ) ≤ (a : ℤ) := by exact_mod_cast h2t
    have hkeyZ : (t : ℤ) * (2 * ((t : ℤ) + (Z : ℤ))) ≤ (t : ℤ) * ((a : ℤ) + 4) := by
      nlinarith [mul_nonneg (by omega : (0 : ℤ) ≤ (t : ℤ) - 2)
        (by omega : (0 : ℤ) ≤ (a : ℤ) - 2 * (t : ℤ)), h1]
    have hkey : t * (2 * (t + Z)) ≤ t * (a + 4) := by exact_mod_cast hkeyZ
    exact Nat.le_of_mul_le_mul_left hkey (by omega)
  have htZM : t + Z ≤ M := by omega
  -- the budget inequality (paper: a·σ ≤ (a−σ)·M for σ = t+Z, M ≥ a+12)
  have hKey : M - 1 + ((t - 1) * b + Z * M) ≤ a * (M - (t + Z)) := by
    zify [show 1 ≤ t by omega, show 1 ≤ M by omega, htZM]
    have hσ' : 2 * ((t : ℤ) + (Z : ℤ)) ≤ (a : ℤ) + 4 := by exact_mod_cast hσ
    have haM : (a : ℤ) + 12 ≤ (M : ℤ) := by omega
    have ha12 : (12 : ℤ) ≤ (a : ℤ) := by exact_mod_cast ha
    have hbM' : (b : ℤ) ≤ (M : ℤ) - 1 := by omega
    have ht1' : (1 : ℤ) ≤ (t : ℤ) := by omega
    nlinarith [mul_le_mul_of_nonneg_left hbM' (by omega : (0 : ℤ) ≤ (t : ℤ) - 1),
      mul_nonneg (by omega : (0 : ℤ) ≤ (a : ℤ) - 4)
        (by omega : (0 : ℤ) ≤ (M : ℤ) - (a : ℤ) - 12),
      mul_nonneg (by omega : (0 : ℤ) ≤ (M : ℤ))
        (by omega : (0 : ℤ) ≤ (a : ℤ) + 4 - 2 * ((t : ℤ) + (Z : ℤ))),
      mul_nonneg (by omega : (0 : ℤ) ≤ (a : ℤ))
        (by omega : (0 : ℤ) ≤ (a : ℤ) + 4 - 2 * ((t : ℤ) + (Z : ℤ)))]
  obtain ⟨hax, hxB⟩ := ceil_pad (show 0 < a by omega) hKey
  set x : ℕ := (M - 1 + ((t - 1) * b + Z * M) + a - 1) / a with hxdef
  -- assemble the frame certificate
  have hcert : FrameCert a b M x (t - 1) Z := by
    refine ⟨by omega, by omega, by omega, ?_⟩
    intro ρ hρ
    set w : ℕ := ((ρ : ZMod a) * ↑hunit.unit⁻¹).val with hwdef
    have hwlt : w < a := ZMod.val_lt _
    have hwcast : (w : ZMod a) = (ρ : ZMod a) * ↑hunit.unit⁻¹ := by
      rw [hwdef, ZMod.natCast_val, ZMod.cast_id]
    have hbw : (b : ZMod a) * (w : ZMod a) = (ρ : ZMod a) := by
      rw [hwcast]
      calc (b : ZMod a) * ((ρ : ZMod a) * ↑hunit.unit⁻¹)
          = (ρ : ZMod a) * ((b : ZMod a) * ↑hunit.unit⁻¹) := by ring
        _ = (ρ : ZMod a) := by rw [hbmul, mul_one]
    obtain ⟨j, k, hjt, hkZ, hmod⟩ :=
      eta_box_steps (show 1 ≤ η by omega) (show η + 1 ≤ a by omega) hwlt
    rw [← htdef] at hjt hkZ
    rw [← hZdef] at hkZ
    refine ⟨j, k, by omega, hkZ, ?_, ?_⟩
    · -- residue class: j·b + k·M ≡ b·(j + k·η) ≡ b·w ≡ ρ (mod a)
      have hjkw : ((j + k * η : ℕ) : ZMod a) = ((w : ℕ) : ZMod a) :=
        (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod
      have expand : ((j * b + k * M : ℕ) : ZMod a)
          = (b : ZMod a) * ((j + k * η : ℕ) : ZMod a) := by
        push_cast
        rw [← hbη]
        ring
      have hcast : ((j * b + k * M : ℕ) : ZMod a) = ((ρ : ℕ) : ZMod a) := by
        rw [expand, hjkw]
        exact hbw
      have hmodeq := (ZMod.natCast_eq_natCast_iff _ _ _).mp hcast
      rw [Nat.ModEq, Nat.mod_eq_of_lt hρ] at hmodeq
      exact hmodeq
    · -- height: the corner (t−1)·b + Z·M dominates, and x was chosen for it
      have hj' : j * b ≤ (t - 1) * b := Nat.mul_le_mul_right b (by omega)
      have hk' : k * M ≤ Z * M := Nat.mul_le_mul_right M hkZ
      omega
  exact hcert.sharpTriple

end Proof
end Erdos1112
