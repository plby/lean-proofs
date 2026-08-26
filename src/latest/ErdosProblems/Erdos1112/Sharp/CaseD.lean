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
Case D (the Case-D lemma): `a ∣ M` — half-price padding.
Paper: the bounded subset-sum covering section.

Construction: residues mod `a` are covered by `a−1` copies of `b`
(`gcd(a,b) = 1`); padding uses `x = q−1` copies of `a` and `z = xeff/q`
copies of `M = qa` (each `M` worth `q` units of `a` — the "half-price"
trick). Run start `c₀ = (a−1)·b`; for `n ∈ [c₀, c₀+M−1]` pick the residue
rep `j·b`, then `(n − j·b)/a = i + q·k` with `i ≤ q−1`, `k ≤ z`. Budget
`(a−1)+(q−1)+z ≤ M−1` closes because `xeff/q ≤ a−1` and `(q−2)(a−1) ≥ 0`.
-/
import ErdosProblems.Erdos1112.Sharp.Lift
import ErdosProblems.Erdos1112.Sharp.Frame
import ErdosProblems.Erdos1112.Sharp.Staircase

namespace Erdos1112
namespace Proof

/-- Coarse coverage: for `q ≥ 1`, every `t ≤ (q−1) + q·z` is `i + q·k` with
`i ≤ q−1`, `k ≤ z` (the `M`-blocks overlap because `x = q−1`). -/
private lemma coarse_cover {q z t : ℕ} (hq : 0 < q) (ht : t ≤ (q - 1) + q * z) :
    ∃ i k, i ≤ q - 1 ∧ k ≤ z ∧ t = i + q * k := by
  have hb : (z + 1) * q = q * z + q := by ring
  have hlt : t < (z + 1) * q := by omega
  have hkz : t / q ≤ z := by
    have := (Nat.div_lt_iff_lt_mul hq).mpr hlt
    omega
  have hmod := Nat.div_add_mod t q
  have hmq := Nat.mod_lt t hq
  exact ⟨t % q, t / q, by omega, hkz, by omega⟩

/-- Budget bound: with `M = a·q`, `a ≥ 3`, `q ≥ 2`, `z ≤ a−1`, the multiset of
size `(a−1)+(q−1)+z` fits within `M−1`. -/
private lemma caseD_budget {a q z M : ℕ} (ha : 3 ≤ a) (hq : 2 ≤ q)
    (hM : M = a * q) (hz : z ≤ a - 1) : (a - 1) + (q - 1) + z ≤ M - 1 := by
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 3 := ⟨a - 3, by omega⟩
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 2 := ⟨q - 2, by omega⟩
  subst hM
  have hexp : (a' + 3) * (q' + 2) = a' * q' + 2 * a' + 3 * q' + 6 := by ring
  omega

/-- Effective padding fits: `⌈((a−1)b + M − 1)/a⌉` (as a floor `xeff`) is
`≤ M − 1`. -/
private lemma caseD_xeff {a b M : ℕ} (ha : 3 ≤ a) (hb : b + 1 ≤ M) :
    ((a - 1) * b + M - 1) / a ≤ M - 1 := by
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  have hle : (a' + 1 - 1) * b + M - 1 ≤ (a' + 1) * (M - 1) := by
    have he : a' + 1 - 1 = a' := by omega
    rw [he]
    have hexp : (a' + 1) * (M - 1) = a' * (M - 1) + (M - 1) := by ring
    have hcb : a' * b ≤ a' * (M - 1) := Nat.mul_le_mul_left _ (by omega)
    omega
  calc ((a' + 1 - 1) * b + M - 1) / (a' + 1)
      ≤ ((a' + 1) * (M - 1)) / (a' + 1) := Nat.div_le_div_right hle
    _ = M - 1 := Nat.mul_div_cancel_left _ (by omega)

set_option maxHeartbeats 800000 in
-- Allow extra elaboration work for the arithmetic and combinatorial case splits.
/-- **Case D**: hard-core triple with `a ∣ M`. -/
theorem caseD {a b M : ℕ} (hc : HardCore a b M) (hD : a ∣ M) :
    SharpTriple a b M := by
  have ha3 := hc.three_le
  obtain ⟨ha0, hab, hbM, hco, hδ⟩ := hc
  obtain ⟨q, hq⟩ := hD                    -- `M = a * q`
  have hq2 : 2 ≤ q := by
    rcases Nat.lt_or_ge q 2 with h | h
    · interval_cases q <;> omega
    · exact h
  have hM1 : 1 ≤ M := by omega
  -- effective padding and the split `(x, z)`
  set xeff : ℕ := ((a - 1) * b + M - 1) / a with hxeffdef
  set z : ℕ := xeff / q with hzdef
  -- `xeff ≤ M − 1`
  have hxeff_le : xeff ≤ M - 1 := caseD_xeff ha3 (by omega)
  -- `z ≤ a − 1`
  have hz_lt : z < a := by
    have h1 : z ≤ (M - 1) / q := Nat.div_le_div_right hxeff_le
    have h2 : (M - 1) / q < a := by
      rw [Nat.div_lt_iff_lt_mul (by omega : 0 < q)]
      omega
    omega
  have hz_le : z ≤ a - 1 := by omega
  -- `a * xeff ≤ (a-1)*b + M - 1`  and  `xeff ≤ x + q*z`
  have haxeff : a * xeff ≤ (a - 1) * b + M - 1 := by
    have h := Nat.div_add_mod ((a - 1) * b + M - 1) a
    rw [← hxeffdef] at h
    omega
  have hqz : xeff ≤ (q - 1) + q * z := by
    have h := Nat.div_add_mod xeff q
    rw [← hzdef] at h
    have hmq := Nat.mod_lt xeff (by omega : 0 < q)
    omega
  -- the multiset and its budget
  refine ⟨Multiset.replicate (a - 1) b + Multiset.replicate (q - 1) a +
    Multiset.replicate z M, ?_, ?_, (a - 1) * b, ?_⟩
  · intro w hw
    rcases Multiset.mem_add.mp hw with hw | hw
    · rcases Multiset.mem_add.mp hw with hw | hw
      · exact Or.inr (Or.inl (Multiset.eq_of_mem_replicate hw))
      · exact Or.inl (Multiset.eq_of_mem_replicate hw)
    · exact Or.inr (Or.inr (Multiset.eq_of_mem_replicate hw))
  · simp only [Multiset.card_add, Multiset.card_replicate]
    exact caseD_budget ha3 hq2 hq hz_le
  · -- the run `[(a-1)*b, (a-1)*b + M - 1]`
    intro i hi
    set n : ℕ := (a - 1) * b + i with hndef
    -- residue rep `j * b` with `j ≤ a-1`
    obtain ⟨j, -, hja, hres⟩ := exists_frame ha0 hco.symm 0 n
    have hja' : j ≤ a - 1 := by omega
    have hjb_le : j * b ≤ (a - 1) * b := Nat.mul_le_mul_right b hja'
    have hjbn : j * b ≤ n := by omega
    have hdvd : a ∣ n - j * b := (Nat.modEq_iff_dvd' hjbn).mp hres
    set t : ℕ := (n - j * b) / a with htdef
    have hat : a * t = n - j * b := Nat.mul_div_cancel' hdvd
    -- `t ≤ xeff ≤ x + q*z`
    have htxeff : t ≤ xeff := by
      have h1 : n - j * b ≤ (a - 1) * b + M - 1 := by omega
      exact Nat.div_le_div_right h1
    have htqz : t ≤ (q - 1) + q * z := le_trans htxeff hqz
    obtain ⟨i', k, hi', hk, htik⟩ := coarse_cover (by omega : 0 < q) htqz
    -- assemble the subset sum
    refine mem_subsetSums.mpr ⟨Multiset.replicate j b + Multiset.replicate i' a +
      Multiset.replicate k M, ?_, ?_⟩
    · exact add_le_add (add_le_add
        ((Multiset.replicate_le_replicate b).mpr hja')
        ((Multiset.replicate_le_replicate a).mpr hi'))
        ((Multiset.replicate_le_replicate M).mpr hk)
    · simp only [Multiset.sum_add, Multiset.sum_replicate, smul_eq_mul]
      -- `j*b + i'*a + k*M = n`
      have hkM : k * M = a * (q * k) := by rw [hq]; ring
      have hai : i' * a = a * i' := Nat.mul_comm _ _
      have hexp : a * t = a * i' + a * (q * k) := by rw [htik]; ring
      omega

end Proof
end Erdos1112
