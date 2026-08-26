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
Statement forms for the bounded subset-sum covering lemma and the hard core.
Paper: the bounded subset-sum covering section.
-/
import ErdosProblems.Erdos1112.SubsetSums

namespace Erdos1112
namespace Proof

/-- (SHARP) for the triple alphabet `{a, b, M}`: some multiset of at most
`M − 1` elements drawn from `{a,b,M}` has subset sums containing `M`
consecutive integers. -/
def SharpTriple (a b M : ℕ) : Prop :=
  ∃ S : Multiset ℕ, (∀ x ∈ S, x = a ∨ x = b ∨ x = M) ∧
    S.card ≤ M - 1 ∧ HasRun (subsetSums S) M

/-- (SHARP) at maximum `M`, for all alphabets: every finite `G` of at least
three positive integers with `gcd G = 1` and maximum `M` admits a multiset of
at most `M−1` of its elements whose subset sums contain `M` consecutive
integers. (`max` is encoded as `M ∈ G ∧ ∀ g ∈ G, g ≤ M`.) -/
def SharpAt (M : ℕ) : Prop :=
  ∀ G : Finset ℕ, (∀ g ∈ G, 0 < g) → 3 ≤ G.card → G.gcd id = 1 →
    (∀ g ∈ G, g ≤ M) → M ∈ G →
    ∃ S : Multiset ℕ, (∀ x ∈ S, x ∈ G) ∧ S.card ≤ M - 1 ∧
      HasRun (subsetSums S) M

/-- The hard core (paper the subset-sum section, "The hard core"): `G = {a, b, M}` with
`gcd(a,b) = 1` and `δ := a + b − M ≥ 2`. Everything else about the shape
(`3 ≤ a`, `h := M − b ∈ [1, a−2]`, `gcd(a,e) = 1` for `e := b − a`, …)
is derived. -/
def HardCore (a b M : ℕ) : Prop :=
  0 < a ∧ a < b ∧ b < M ∧ Nat.Coprime a b ∧ M + 2 ≤ a + b

namespace HardCore

variable {a b M : ℕ}

/-- In the hard core, `a ≥ 3` (from `M + 2 ≤ a + b` and `b < M` alone). -/
lemma three_le (h : HardCore a b M) : 3 ≤ a := by
  obtain ⟨-, -, hbM, -, hδ⟩ := h
  omega

/-- In the hard core, `h := M − b` satisfies `1 ≤ h ≤ a − 2`. -/
lemma h_bounds (h : HardCore a b M) : 1 ≤ M - b ∧ M - b ≤ a - 2 := by
  obtain ⟨-, -, hbM, -, hδ⟩ := h
  omega

/-- In the hard core, `gcd(a, e) = 1` for the letter difference `e = b − a`. -/
lemma coprime_a_e (h : HardCore a b M) : Nat.Coprime a (b - a) := by
  obtain ⟨-, hab, -, hco, -⟩ := h
  have h1 : Nat.gcd a (b - a) ∣ a := Nat.gcd_dvd_left _ _
  have h2 : Nat.gcd a (b - a) ∣ b - a := Nat.gcd_dvd_right _ _
  have h3 : Nat.gcd a (b - a) ∣ b := by
    have h5 : Nat.gcd a (b - a) ∣ b - a + a := Nat.dvd_add h2 h1
    rwa [Nat.sub_add_cancel (le_of_lt hab)] at h5
  have h4 : Nat.gcd a (b - a) ∣ Nat.gcd a b := Nat.dvd_gcd h1 h3
  rw [hco] at h4
  exact Nat.dvd_one.mp h4

end HardCore

/-- A `SharpTriple` witnesses `SharpAt`-style membership for `G = {a,b,M}`. -/
lemma SharpTriple.mem_insert {a b M : ℕ} (h : SharpTriple a b M) :
    ∃ S : Multiset ℕ, (∀ x ∈ S, x ∈ ({a, b, M} : Finset ℕ)) ∧
      S.card ≤ M - 1 ∧ HasRun (subsetSums S) M := by
  obtain ⟨S, hS, hc, hr⟩ := h
  exact ⟨S, fun x hx => by rcases hS x hx with rfl | rfl | rfl <;> simp, hc, hr⟩

end Proof
end Erdos1112
