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
Case L (the Case-L lemma): scaled consecutive triples
`G = {a, a+g, a+2g}` (i.e. `e = h`). Three sub-cases by parity of `a` and
`g = 1` vs `g ≥ 2`, via the staircase short merge (c) / base form (d).
Paper: the bounded subset-sum covering section.

Notation: `g := b − a = M − b`, so `b = a + g`, `M = a + 2g`,
`(e′, μ′) = (1, 2)`, `C′ = 0`, `V′ = 2z + 1`. Multiset `(x, 1, z)` with
`z = ⌈(a−2)/2⌉`, `x = ⌊(a−2)/2⌋ + 2g`, budget `a + 2g − 1 = M − 1`.
The parity split uses `a = 2z + 2` (even) / `a = 2w + 3` (odd) to keep all
arithmetic subtraction-free.
-/
import ErdosProblems.Erdos1112.Sharp.Staircase

namespace Erdos1112
namespace Proof

/-- Assembly: a covered interval `[lo, hi]` of length `≥ M` with budget
`≤ M − 1` gives `SharpTriple`. -/
private lemma caseL_assemble {a b M x y z lo hi : ℕ}
    (hcov : ∀ n, lo ≤ n → n ≤ hi → n ∈ subsetSums (stair a b M x y z))
    (hlen : lo + M - 1 ≤ hi) (hM : 1 ≤ M) (hbud : x + y + z ≤ M - 1) :
    SharpTriple a b M := by
  refine ⟨stair a b M x y z, ?_, ?_, lo, ?_⟩
  · intro w hw
    simp only [stair, Multiset.mem_add, Multiset.mem_replicate] at hw
    rcases hw with (⟨_, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  · simp only [stair, Multiset.card_add, Multiset.card_replicate]; omega
  · intro i hi'
    exact hcov (lo + i) (Nat.le_add_right _ _) (by omega)

set_option maxHeartbeats 1600000 in
-- Allow extra elaboration work for the arithmetic and combinatorial case splits.
/-- **Case L**: hard-core triple with `e = h` (`b − a = M − b`). -/
theorem caseL {a b M : ℕ} (hc : HardCore a b M) (hL : b - a = M - b) :
    SharpTriple a b M := by
  have ha3 := hc.three_le
  have hhb := hc.h_bounds        -- `1 ≤ M − b ≤ a − 2`
  have hcop : Nat.Coprime a (b - a) := hc.coprime_a_e
  obtain ⟨ha0, hab, hbM, hco, hδ⟩ := hc
  set g : ℕ := b - a with hgdef0
  have hba : b - a = g := rfl
  have hg1 : 1 ≤ g := by omega
  have hg_le : g ≤ a - 2 := by omega
  have hb_eq : b = a + g := by omega
  have hM_eq : M = a + 2 * g := by omega
  have hMa : M - a = 2 * g := by omega
  have hM1 : 1 ≤ M := by omega
  -- the shared StairSetup with `(e′, μ′) = (1, 2)`
  have hStair : StairSetup a b M g 1 2 := by
    refine ⟨hab, hbM, ha0, ?_, ?_, ?_⟩
    · rw [hba, hMa]; exact (Nat.gcd_eq_left ⟨2, by ring⟩).symm
    · rw [hba, Nat.div_self (by omega : 0 < g)]
    · rw [hMa, Nat.mul_div_cancel 2 (by omega : 0 < g)]
  have hC' : (0 : ℕ) = (1 - 1) * (2 - 1) := by norm_num
  rcases Nat.even_or_odd a with ⟨r, hr⟩ | ⟨s, hs⟩
  · -- even: reparametrize `a = 2v + 2` (`v ≥ 1`)
    obtain ⟨v, hv⟩ : ∃ v, a = 2 * v + 2 := ⟨r - 1, by omega⟩
    have hv1 : 1 ≤ v := by omega
    -- multiset `(x, 1, z) = (v + 2g, 1, v)`,  `V' = 2v + 1`
    have hVeq : (2 * v + 1) + (0 : ℕ) = 1 * 1 + 2 * v := by omega
    have hcov := staircase_phase_extended (x := v + 2 * g) (y := 1) (z := v)
      (V' := 2 * v + 1) hStair hC' hVeq
      (by rw [← hba] at hcop; exact hcop) (by omega) (by omega)
      (by omega : 1 + v + g ≤ v + 2 * g) (by omega : a + 0 ≤ (2 * v + 1) + 1)
    refine caseL_assemble hcov ?_ hM1 (by omega)
    -- lo = (v+g)*a, hi = (v+g+1)*a + g*(2v+1)
    have hlo : (1 + v + g - 1) * a = (v + g) * a := by congr 1; omega
    have hhi : (v + 2 * g - g + 1) * a = (v + g) * a + a := by
      have : v + 2 * g - g + 1 = (v + g) + 1 := by omega
      rw [this]; ring
    have hprod : g * 3 ≤ g * (2 * v + 1) := Nat.mul_le_mul_left g (by omega)
    rw [hlo, hhi]; omega
  · -- odd: reparametrize `a = 2u + 3` (`u ≥ 0`)
    obtain ⟨u, hu⟩ : ∃ u, a = 2 * u + 3 := ⟨s - 1, by omega⟩
    rcases Nat.lt_or_ge g 2 with hg | hg2
    · -- `g = 1`  →  short merge (3.3c);  `(x, 1, z) = (u+2, 1, u+1)`
      have hgeq : g = 1 := by omega
      have hVeq : (2 * (u + 1) + 1) + (0 : ℕ) = 1 * 1 + 2 * (u + 1) := by omega
      have hcov := staircase_merge_c (x := u + 2) (y := 1) (z := u + 1)
        (V' := 2 * (u + 1) + 1) hStair hgeq hC' hVeq (by omega) (by omega)
        (by omega : u + 2 = 1 + (u + 1))
        (by omega)
      refine caseL_assemble hcov ?_ hM1 (by omega)
      have hcoef : (1 + (u + 1) + 1) * a = (1 + (u + 1)) * a + a := by ring
      rw [hcoef]; omega
    · -- `g ≥ 2`  →  extended form;  `(x, 1, z) = (u + 2g, 1, u+1)`,  `V' = 2u+3`
      have hVeq : (2 * (u + 1) + 1) + (0 : ℕ) = 1 * 1 + 2 * (u + 1) := by omega
      have hcov := staircase_phase_extended (x := u + 2 * g) (y := 1) (z := u + 1)
        (V' := 2 * (u + 1) + 1) hStair hC' hVeq
        (by rw [← hba] at hcop; exact hcop) (by omega) (by omega)
        (by omega : 1 + (u + 1) + g ≤ u + 2 * g)
        (by omega : a + 0 ≤ (2 * (u + 1) + 1) + 1)
      refine caseL_assemble hcov ?_ hM1 (by omega)
      -- lo = (u+1+g)*a, hi = (u+g+1)*a + g*(2u+3);  g*(2u+3) = g*a ≥ M-1
      have hlo : (1 + (u + 1) + g - 1) * a = (u + 1 + g) * a := by congr 1; omega
      have hhi : (u + 2 * g - g + 1) * a = (u + 1 + g) * a := by congr 1; omega
      have hVa : 2 * (u + 1) + 1 = a := by omega
      have h1 : 2 * (2 * u + 1) ≤ g * (2 * u + 1) := Nat.mul_le_mul_right _ (by omega)
      have h2 : g * a = g * (2 * u + 1) + 2 * g := by rw [hu]; ring
      have hga : a + 2 * g - 1 ≤ g * a := by omega
      rw [hlo, hhi, hVa]; omega

end Proof
end Erdos1112
