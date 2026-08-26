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
the subset-sum development certificate layer: the kernel-decidable frame-certificate checker
and its soundness theorem. Certificate DATA lives in `Sharp/TablesData.lean`
(6-tuples `(a, b, M, x, Y, Z)`, split into Table A and Table B).

All 360 table rows satisfy the per-residue frame condition
(`FrameCert`/`frameCertOK`), which is what the λ-lift transports, so one
certificate notion serves validity, lift-stability, and (SHARP)-witnessing
at once. Kernel `decide` only.
-/
import ErdosProblems.Erdos1112.Sharp.Lift

namespace Erdos1112
namespace Proof

/-- Boolean checker for `FrameCert`, kernel-`decide`-friendly. -/
def frameCertOK : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ → Bool
  | (a, b, M, x, Y, Z) =>
    decide (0 < M) && decide (x + Y + Z ≤ M - 1) && decide (Y + Z + 1 ≤ a) &&
    ((List.range a).all fun ρ =>
      (List.range (Y + 1)).any fun j =>
        (List.range (Z + 1)).any fun k =>
          decide ((j * b + k * M) % a = ρ) &&
          decide (M - 1 + (j * b + k * M) ≤ a * x))

/-- **Checker soundness**: a passing row is a genuine frame certificate. -/
theorem frameCertOK_sound {a b M x Y Z : ℕ}
    (h : frameCertOK (a, b, M, x, Y, Z) = true) : FrameCert a b M x Y Z := by
  rw [frameCertOK] at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.any_eq_true,
    List.mem_range, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := h
  refine ⟨h0, h1, h2, ?_⟩
  intro ρ hρ
  obtain ⟨j, hj, k, hk, hres, hht⟩ := h3 ρ hρ
  exact ⟨j, k, by omega, by omega, hres, hht⟩

/-- Convenience: a passing row yields its (SHARP) witness. -/
theorem frameCertOK_sharpTriple {a b M x Y Z : ℕ}
    (h : frameCertOK (a, b, M, x, Y, Z) = true) : SharpTriple a b M :=
  (frameCertOK_sound h).sharpTriple

end Proof
end Erdos1112
