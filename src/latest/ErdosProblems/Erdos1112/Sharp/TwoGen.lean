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
the two-generator lemma: the boxed two-generator interval. Chicken McNugget with
multiplicity bounds. Paper: the bounded subset-sum covering section.

Route: for `α ≥ 2` the base case `y = α − 1` uses Mathlib's
`frobeniusNumber_pair` (classical Chicken McNugget: `n ∉ closure {α,β}` forces
`n ≤ αβ−α−β`, so every `n ≥ C := (α−1)(β−1) = αβ−α−β+1` is representable),
followed by normalizing `j` modulo `α` (moving `β·α`-blocks into `i`), which
forces `i ≤ x` inside the base window. The step `y → y+1` peels one `β` per
the paper. `α = 1` is direct (`j := min y (n/β)`).
-/
import ErdosProblems.Erdos1112.Sharp.Defs

namespace Erdos1112
namespace Proof

set_option maxHeartbeats 1600000 in
-- Allow extra elaboration work for the arithmetic and combinatorial case splits.
/-- **the two-generator lemma (two-generator interval).** For coprime `α < β`, `x ≥ β − 1`,
`y ≥ α − 1`: every `n` in `[C, αx + βy − C]` with `C = (α−1)(β−1)` is
`iα + jβ` with `i ≤ x`, `j ≤ y`. -/
theorem twoGen_interval {α β x y : ℕ} (hαβ : α < β) (hα : 0 < α)
    (hco : Nat.Coprime α β) (hx : β - 1 ≤ x) (hy : α - 1 ≤ y) :
    ∀ n, (α - 1) * (β - 1) ≤ n → n + (α - 1) * (β - 1) ≤ α * x + β * y →
      ∃ i j, i ≤ x ∧ j ≤ y ∧ n = i * α + j * β := by
  have hβ0 : 0 < β := lt_trans hα hαβ
  rcases Nat.lt_or_ge α 2 with hα1 | hα2
  · -- α = 1: C = 0; take j := min y (n/β), i := n − jβ
    have hα1' : α = 1 := by omega
    subst hα1'
    intro n _hnlo hnhi
    simp only [Nat.sub_self, Nat.zero_mul, Nat.one_mul, Nat.add_zero] at hnhi
    have hβ1 : β - 1 + 1 = β := by omega
    rcases Nat.lt_or_ge (n / β) (y + 1) with hj | hj
    · -- j := n / β, i := n % β
      refine ⟨n % β, n / β, ?_, by omega, ?_⟩
      · have h1 := Nat.mod_lt n hβ0
        have h2 : n % β ≤ β - 1 := Nat.le_pred_of_lt h1
        linarith
      · calc n = β * (n / β) + n % β := (Nat.div_add_mod n β).symm
          _ = (n % β) * 1 + (n / β) * β := by ring
    · -- j := y, i := n − yβ
      have h4 : (y + 1) * β ≤ (n / β) * β := Nat.mul_le_mul_right β hj
      have h5 : (n / β) * β ≤ n := Nat.div_mul_le_self n β
      have h6 : y * β ≤ n := by
        have hexp : (y + 1) * β = y * β + β := by ring
        linarith
      refine ⟨n - y * β, y, ?_, le_refl y, ?_⟩
      · rw [Nat.sub_le_iff_le_add]
        have hbr : β * y = y * β := Nat.mul_comm _ _
        linarith
      · rw [mul_one, Nat.sub_add_cancel h6]
  · -- α ≥ 2
    have hβ2 : 2 ≤ β := by omega
    -- numeric identities
    have hCval : (α - 1) * (β - 1) + α + β = α * β + 1 := by
      zify [show 1 ≤ α by omega, show 1 ≤ β by omega]
      ring
    have hkey : (α - 1) * (β - 1) + (α - 1) = (α - 1) * β := by
      zify [show 1 ≤ α by omega, show 1 ≤ β by omega]
      ring
    induction y, hy using Nat.le_induction with
    | base =>
        intro n hnlo hnhi
        -- classical Chicken McNugget gives some representation
        have hF := frobeniusNumber_pair hco (by omega : 1 < α) (by omega : 1 < β)
        have hαβ' : α + β ≤ α * β := by
          have hC1 : 1 * 1 ≤ (α - 1) * (β - 1) :=
            Nat.mul_le_mul (by omega) (by omega)
          linarith [hCval]
        have hrep : ∃ i j : ℕ, n = i * α + j * β := by
          by_contra hcon
          push Not at hcon
          have hnotin : n ∉ AddSubmonoid.closure ({α, β} : Set ℕ) := by
            rw [AddSubmonoid.mem_closure_pair]
            rintro ⟨i, j, hij⟩
            exact hcon i j (by simpa [smul_eq_mul, eq_comm] using hij)
          have hle : n ≤ α * β - α - β := hF.2 hnotin
          have h2 : α * β - α - β + (α + β) = α * β := by
            rw [Nat.sub_sub, Nat.sub_add_cancel hαβ']
          linarith
        obtain ⟨i, j, hij⟩ := hrep
        -- normalize j modulo α
        have hα0 : 0 < α := by omega
        have hjmod : j % α ≤ α - 1 := Nat.le_pred_of_lt (Nat.mod_lt j hα0)
        have heq : n = (i + j / α * β) * α + (j % α) * β := by
          calc n = i * α + j * β := hij
            _ = i * α + (α * (j / α) + j % α) * β := by rw [Nat.div_add_mod]
            _ = (i + j / α * β) * α + (j % α) * β := by ring
        refine ⟨i + j / α * β, j % α, ?_, hjmod, heq⟩
        -- the boxed bound on i′
        have hbr : β * (α - 1) = (α - 1) * β := Nat.mul_comm _ _
        have hn_ub : n ≤ α * x + (α - 1) := by linarith
        have hi'α : (i + j / α * β) * α ≤ n := by
          have : (i + j / α * β) * α ≤ (i + j / α * β) * α + (j % α) * β :=
            Nat.le_add_right _ _
          linarith [heq.symm.le, this]
        have hlt : (i + j / α * β) * α < (x + 1) * α := by
          have hexp : (x + 1) * α = x * α + α := by ring
          have hbr2 : α * x = x * α := Nat.mul_comm _ _
          have hαm : α - 1 + 1 = α := by omega
          linarith
        exact Nat.lt_succ_iff.mp (Nat.lt_of_mul_lt_mul_right hlt)
    | succ y hy ih =>
        intro n hnlo hnhi
        rcases Nat.le_total (n + (α - 1) * (β - 1)) (α * x + β * y) with hcase | hcase
        · obtain ⟨i, j, hix, hjy, heq⟩ := ih n hnlo hcase
          exact ⟨i, j, hix, by omega, heq⟩
        · -- peel one β
          have hwin : 2 * ((α - 1) * (β - 1)) + β ≤ α * x + β * y := by
            have h1 : α * (β - 1) ≤ α * x := Nat.mul_le_mul_left α hx
            have h2 : β * (α - 1) ≤ β * y := Nat.mul_le_mul_left β hy
            have h3 : 2 * ((α - 1) * (β - 1)) + β + (α - 2) =
                α * (β - 1) + β * (α - 1) := by
              zify [show 1 ≤ α by omega, show 1 ≤ β by omega,
                show 2 ≤ α from hα2]
              ring
            linarith
          have hβn : β ≤ n := by
            have hC0 : 0 ≤ (α - 1) * (β - 1) := Nat.zero_le _
            linarith
          have hnlo' : (α - 1) * (β - 1) ≤ n - β :=
            Nat.le_sub_of_add_le (by linarith)
          have hnhi' : (n - β) + (α - 1) * (β - 1) ≤ α * x + β * y := by
            have hexp : β * (y + 1) = β * y + β := by ring
            have h4 : n - β + β = n := Nat.sub_add_cancel hβn
            linarith
          obtain ⟨i, j, hix, hjy, heq⟩ := ih (n - β) hnlo' hnhi'
          refine ⟨i, j + 1, hix, by omega, ?_⟩
          have h5 : n = (n - β) + β := (Nat.sub_add_cancel hβn).symm
          rw [h5, heq]
          ring

/-- Multiset form of the two-generator lemma: the corresponding run of subset sums of
`{x × α, y × β}`. -/
theorem twoGen_hasRun {α β x y : ℕ} (hαβ : α < β) (hα : 0 < α)
    (hco : Nat.Coprime α β) (hx : β - 1 ≤ x) (hy : α - 1 ≤ y) :
    ∀ n, (α - 1) * (β - 1) ≤ n → n + (α - 1) * (β - 1) ≤ α * x + β * y →
      n ∈ subsetSums (Multiset.replicate x α + Multiset.replicate y β) := by
  intro n hnlo hnhi
  obtain ⟨i, j, hix, hjy, heq⟩ := twoGen_interval hαβ hα hco hx hy n hnlo hnhi
  apply mem_subsetSums.mpr
  refine ⟨Multiset.replicate i α + Multiset.replicate j β, ?_, ?_⟩
  · exact add_le_add ((Multiset.replicate_le_replicate α).mpr hix)
      ((Multiset.replicate_le_replicate β).mpr hjy)
  · simp only [Multiset.sum_add, Multiset.sum_replicate, smul_eq_mul]
    exact heq.symm

end Proof
end Erdos1112
