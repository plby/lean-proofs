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
Offset choice past the small elements of `B`, nested safe intervals, and
the existence theorem with the explicit ratio `192·d₂`.
Paper: the existence section.

Construction notes:
  * `j₀ := 4·d₂²` — since `b` is strictly monotone on ℕ, `b j₀ ≥ j₀ = 4d₂²`
    directly (no least-index search needed); `c := b j₀ + 1`.
  * shifted targets `t i := b i − k·c` for `i > j₀`; the ratio survives
    additively: `t (i+1) ≥ 192·d₂·t i` from `b (i+1) ≥ 192·d₂·b i`.
  * the interval chain is a plain `Nat.rec` over `ℝ × ℝ` whose step is a
    `dite` on the free-gap existential (`Exists.choose` on the then-branch);
    the invariant and the step relation are recovered by `dif_pos`.
  * `γ* := ⨆ j, lo j`; monotone `lo` / antitone `hi` sandwich it into every
    interval, hence `γ*` is safe for every target simultaneously.
-/
import ErdosProblems.Erdos1112.Existence.FreeGap

namespace Erdos1112
namespace Proof

set_option maxHeartbeats 3200000 in
-- Allow extra elaboration work for the arithmetic and combinatorial case splits.
/-- **Theorem 1** (existence half, explicit bound): for `d₂ ≥ k + 1` the ratio
`r = 192·d₂` works. Statement identical to the frozen target
`Erdos1112.erdos_1112_existence_bound`. -/
theorem existence_bound (k d₁ d₂ : ℕ) (hk : 3 ≤ k) (hd₁ : 1 ≤ d₁)
    (hd : d₁ < d₂) (h : k + 1 ≤ d₂) :
    RatioWorks k d₁ d₂ (192 * d₂) := by
  classical
  intro b hb
  obtain ⟨hb0, hbmono, hbrat⟩ := hb
  have hd₂2 : 2 ≤ d₂ := by omega
  have hk0 : 0 < k := by omega
  -- (1.3): the offset
  set j₀ : ℕ := 4 * d₂ ^ 2 with hj₀def
  have hbj₀ : 4 * d₂ ^ 2 ≤ b j₀ := le_trans (le_of_eq hj₀def.symm) hbmono.le_apply
  set c : ℕ := b j₀ + 1 with hcdef
  have hd₂bj₀ : d₂ ≤ b j₀ := by nlinarith
  have hkc : k * c ≤ 2 * d₂ * b j₀ := by
    have h1 : k ≤ d₂ := by omega
    have h2 : k * c ≤ d₂ * (b j₀ + 1) := Nat.mul_le_mul h1 (le_refl _)
    nlinarith
  -- every b i with i > j₀ clears k·c with big room
  have hkc_lt : ∀ i, j₀ + 1 ≤ i → k * c + 32 * d₂ ^ 2 ≤ b i := by
    intro i hi
    have h1 : 192 * d₂ * b j₀ ≤ b (j₀ + 1) := hbrat j₀
    have h2 : b (j₀ + 1) ≤ b i := hbmono.monotone hi
    nlinarith
  -- the shifted targets
  set t : ℕ → ℕ := fun i => b i - k * c with htdef
  have ht_cast : ∀ i, j₀ + 1 ≤ i → (t i : ℝ) = (b i : ℝ) - (k : ℝ) * c := by
    intro i hi
    have := hkc_lt i hi
    simp only [htdef]
    push_cast [Nat.cast_sub (by omega : k * c ≤ b i)]
    ring
  set T : ℕ → ℝ := fun m => (t (j₀ + 1 + m) : ℝ) with hTdef
  have hT32 : ∀ m, 32 * (d₂ : ℝ) ^ 2 ≤ T m := by
    intro m
    have h1 := hkc_lt (j₀ + 1 + m) (by omega)
    have h2 : (32 * d₂ ^ 2 : ℕ) ≤ t (j₀ + 1 + m) := by
      simp only [htdef]; omega
    calc 32 * (d₂ : ℝ) ^ 2 = ((32 * d₂ ^ 2 : ℕ) : ℝ) := by push_cast; ring
      _ ≤ T m := by simp only [hTdef]; exact_mod_cast h2
  have hT0 : ∀ m, (0 : ℝ) < T m := by
    intro m
    have h1 := hT32 m
    have h2 : (0 : ℝ) < 32 * (d₂ : ℝ) ^ 2 := by
      have : (2 : ℝ) ≤ (d₂ : ℝ) := by exact_mod_cast hd₂2
      nlinarith
    linarith
  -- one growth step of the targets
  have hTstep' : ∀ m, 192 * (d₂ : ℝ) * T m ≤ T (m + 1) := by
    intro m
    have hi : j₀ + 1 ≤ j₀ + 1 + m := by omega
    have hi' : j₀ + 1 ≤ j₀ + 1 + m + 1 := by omega
    have e1 : T m = (b (j₀ + 1 + m) : ℝ) - (k : ℝ) * c := ht_cast _ hi
    have e2 : T (m + 1) = (b (j₀ + 1 + m + 1) : ℝ) - (k : ℝ) * c := by
      have : j₀ + 1 + (m + 1) = j₀ + 1 + m + 1 := by omega
      simp only [hTdef, this]
      exact ht_cast _ hi'
    have hrat : (192 : ℝ) * d₂ * b (j₀ + 1 + m) ≤ b (j₀ + 1 + m + 1) := by
      exact_mod_cast hbrat (j₀ + 1 + m)
    have hkc0 : (0 : ℝ) ≤ (k : ℝ) * c := by positivity
    have hd₂1 : (1 : ℝ) ≤ 192 * (d₂ : ℝ) := by
      have : (2 : ℝ) ≤ (d₂ : ℝ) := by exact_mod_cast hd₂2
      linarith
    rw [e1, e2]
    nlinarith
  -- the division form used to thread the interval lengths
  have hTstep : ∀ m, 4 * (d₂ : ℝ) ^ 2 / T (m + 1) ≤ (d₂ : ℝ) / (48 * T m) := by
    intro m
    have hd₂R : (2 : ℝ) ≤ (d₂ : ℝ) := by exact_mod_cast hd₂2
    rw [div_le_iff₀ (hT0 (m + 1)), div_mul_eq_mul_div,
      le_div_iff₀ (by nlinarith [hT0 m] : (0 : ℝ) < 48 * T m)]
    have h1 := hTstep' m
    nlinarith [hT0 m, hT0 (m + 1)]
  -- the nested chain of safe intervals
  set Q : ℕ → ℝ × ℝ → ℝ × ℝ → Prop := fun m p p' =>
    p.1 ≤ p'.1 ∧ p'.2 ≤ p.2 ∧ (d₂ : ℝ) / (48 * T m) ≤ p'.2 - p'.1 ∧
      ∀ γ ∈ Set.Icc p'.1 p'.2, SafeFor k (T m) γ with hQdef
  set next : ℕ → ℝ × ℝ → ℝ × ℝ := fun m p =>
    if hE : ∃ p' : ℝ × ℝ, Q m p p' then hE.choose else p with hnextdef
  set chain : ℕ → ℝ × ℝ := fun j =>
    Nat.rec ((d₂ : ℝ) - 1 / 2, (d₂ : ℝ) - 1 / 4) next j with hchaindef
  have hchainS : ∀ j, chain (j + 1) = next j (chain j) := fun _ => rfl
  have hchain0 : chain 0 = ((d₂ : ℝ) - 1 / 2, (d₂ : ℝ) - 1 / 4) := rfl
  have hd₂R : (2 : ℝ) ≤ (d₂ : ℝ) := by exact_mod_cast hd₂2
  -- the invariant, by induction
  have main : ∀ j, ((d₂ : ℝ) - 1 / 2 ≤ (chain j).1) ∧
      ((chain j).2 ≤ (d₂ : ℝ) - 1 / 4) ∧
      (4 * (d₂ : ℝ) ^ 2 / T j ≤ (chain j).2 - (chain j).1) := by
    intro j
    induction j with
    | zero =>
        rw [hchain0]
        refine ⟨le_refl _, le_refl _, ?_⟩
        rw [div_le_iff₀ (hT0 0)]
        have := hT32 0
        nlinarith
    | succ j ih =>
        have hE : ∃ p' : ℝ × ℝ, Q j (chain j) p' := by
          obtain ⟨lo', hi', h1, h2, h3, h4⟩ :=
            exists_safe_subinterval (by omega : 1 ≤ k) h (hT32 j) ih.1
              (by linarith [ih.2.1]) ih.2.2
          exact ⟨(lo', hi'), h1, h2, h3, h4⟩
        have hnext : chain (j + 1) = hE.choose := by
          rw [hchainS j]
          simp only [hnextdef]
          exact dif_pos hE
        have hQ := hE.choose_spec
        rw [← hnext] at hQ
        refine ⟨le_trans ih.1 hQ.1, le_trans hQ.2.1 ih.2.1, ?_⟩
        calc 4 * (d₂ : ℝ) ^ 2 / T (j + 1) ≤ (d₂ : ℝ) / (48 * T j) := hTstep j
          _ ≤ (chain (j + 1)).2 - (chain (j + 1)).1 := hQ.2.2.1
  -- the step relation (recomputed from the invariant)
  have hQstep : ∀ j, Q j (chain j) (chain (j + 1)) := by
    intro j
    have ih := main j
    have hE : ∃ p' : ℝ × ℝ, Q j (chain j) p' := by
      obtain ⟨lo', hi', h1, h2, h3, h4⟩ :=
        exists_safe_subinterval (by omega : 1 ≤ k) h (hT32 j) ih.1
          (by linarith [ih.2.1]) ih.2.2
      exact ⟨(lo', hi'), h1, h2, h3, h4⟩
    have hnext : chain (j + 1) = hE.choose := by
      rw [hchainS j]
      simp only [hnextdef]
      exact dif_pos hE
    rw [hnext]
    exact hE.choose_spec
  -- interval geometry: lo mono, hi anti, lo ≤ hi
  have lo_le_hi : ∀ j, (chain j).1 ≤ (chain j).2 := by
    intro j
    have h1 := (main j).2.2
    have h2 : (0 : ℝ) < 4 * (d₂ : ℝ) ^ 2 / T j := by
      apply div_pos (by nlinarith) (hT0 j)
    linarith
  have lo_mono : Monotone fun j => (chain j).1 :=
    monotone_nat_of_le_succ fun j => (hQstep j).1
  have hi_anti : Antitone fun j => (chain j).2 :=
    antitone_nat_of_succ_le fun j => (hQstep j).2.1
  -- the common slope γ*
  have hbdd : BddAbove (Set.range fun j => (chain j).1) := by
    refine ⟨(d₂ : ℝ) - 1 / 4, ?_⟩
    rintro x ⟨j, rfl⟩
    exact le_trans (lo_le_hi j) (main j).2.1
  set γ' : ℝ := ⨆ j, (chain j).1 with hγdef
  have hγlo : ∀ j, (chain j).1 ≤ γ' := fun j => le_ciSup hbdd j
  have hγhi : ∀ j, γ' ≤ (chain j).2 := by
    intro j
    apply ciSup_le
    intro m
    rcases le_total m j with hmj | hjm
    · exact le_trans (lo_mono hmj) (lo_le_hi j)
    · exact le_trans (lo_le_hi m) (hi_anti hjm)
  have hγ_ge : (d₂ : ℝ) - 1 / 2 ≤ γ' := by
    have := hγlo 0
    rw [hchain0] at this
    exact this
  have hγ_le : γ' ≤ (d₂ : ℝ) - 1 / 4 := by
    have := hγhi 0
    rw [hchain0] at this
    exact this
  have hγl : (d₂ : ℝ) - 1 < γ' := by linarith
  have hγu : γ' < (d₂ : ℝ) := by linarith
  have hγpos : (0 : ℝ) < γ' := by linarith
  -- γ* is safe for every target simultaneously
  have hγsafe : ∀ m, SafeFor k (T m) γ' :=
    fun m => (hQstep m).2.2.2 γ' ⟨hγlo (m + 1), hγhi (m + 1)⟩
  -- assembly
  have hgaps : HasGapsIn d₁ d₂ (beatty γ' c) := beatty_hasGapsIn hd₁ hd hγl hγu
  refine ⟨beatty γ' c, hgaps, disjoint_range_iff.mpr ?_⟩
  intro n hn i
  rcases Nat.lt_or_ge i (j₀ + 1) with hi | hi
  · -- small elements of B sit below min kA
    obtain ⟨f, rfl⟩ := hn
    have ha0 : c + 1 ≤ beatty γ' c 0 := by
      have h1 : (1 : ℤ) ≤ ⌊(((0 : ℕ) : ℝ) + 1) * γ'⌋ := by
        apply Int.le_floor.mpr
        push_cast
        nlinarith
      unfold beatty
      omega
    have hsum : k * beatty γ' c 0 ≤ ∑ j, beatty γ' c (f j) := by
      calc k * beatty γ' c 0 = ∑ _j : Fin k, beatty γ' c 0 := by
            simp [Finset.sum_const]
        _ ≤ ∑ j, beatty γ' c (f j) :=
            Finset.sum_le_sum fun j _ => hgaps.monotone (Nat.zero_le _)
    have hX : beatty γ' c 0 ≤ k * beatty γ' c 0 :=
      Nat.le_mul_of_pos_left _ hk0
    have hbi : b i ≤ b j₀ := hbmono.monotone (by omega)
    omega
  · -- large elements of B are dodged by the safe slope
    intro heq
    set m : ℕ := i - (j₀ + 1) with hmdef
    have him : j₀ + 1 + m = i := by omega
    have hTi : T m = (b i : ℝ) - (k : ℝ) * c := by
      simp only [hTdef, him]
      exact ht_cast i hi
    have hsafe : SafeFor k ((b i : ℝ) - (k : ℝ) * c) γ' := by
      rw [← hTi]; exact hγsafe m
    exact beatty_avoids hk0 hγpos hsafe (heq ▸ hn)

end Proof
end Erdos1112
