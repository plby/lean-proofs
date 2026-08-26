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
The Sturmian ladder: a two-letter tail with exactly
mechanical counting function (irrational slope) is tail-covering with m = 1.
Steps: (0) window bookkeeping, (1) uniform syndeticity from a Dirichlet-step
fract-walk (`MH/Walk.lean`; no three-gap needed), (2) exact fractional-sum
completion via the mod-1 pinning (`MH/Subwindow.lean`), (3) the ladder lands.
Paper: the paper's non-existence section, (2.10.1)–(2.10.11), followed literally.
-/
import ErdosProblems.Erdos1112.NonEx.TwoLetter.Balanced
import ErdosProblems.Erdos1112.NonEx.TwoLetter.MH.Walk
import ErdosProblems.Erdos1112.NonEx.TwoLetter.MH.Subwindow

namespace Erdos1112
namespace Proof

/-- **Step 1 (uniform syndeticity).** For irrational `α` and any arc length
`ε > 0` there is `L` such that every `L`-block of consecutive integers
contains an `n` with `Int.fract (n·α + β)` in any prescribed arc of length
`ε` — uniformly in the arc position and in `β`. -/
theorem uniform_syndeticity {α : ℝ} (hα : Irrational α) {ε : ℝ} (hε : 0 < ε) :
    ∃ L, 0 < L ∧ ∀ (β u : ℝ) (N : ℕ), u + ε ≤ 1 → 0 ≤ u →
      ∃ n, N < n ∧ n ≤ N + L ∧ Int.fract ((n : ℝ) * α + β) ∈ Set.Ioo u (u + ε) := by
  -- Dirichlet step, made positive, strictly below min(ε/2, 1/2)
  have hb0 : 0 < min (ε / 2) (1 / 2) := lt_min (half_pos hε) (by norm_num)
  obtain ⟨j, K, hj1, hθ0, hθb⟩ := MH.exists_pos_step hα hb0 (min_le_right _ _)
  set θ : ℝ := (j : ℝ) * α - K with hθ_def
  have hθε : 2 * θ < ε := by
    have h1 : θ < ε / 2 := lt_of_lt_of_le hθb (min_le_left _ _)
    linarith
  obtain ⟨M, hM⟩ := MH.walk_enters hθ0 hθε
  refine ⟨M * j + 1, Nat.succ_pos _, fun β u N hu1 hu0 => ?_⟩
  -- the fract-walk sampled along the AP n = N + 1 + m·j
  set x : ℕ → ℝ := fun m => Int.fract (((N + 1 + m * j : ℕ) : ℝ) * α + β) with hx_def
  have key : ∀ y : ℝ, Int.fract (Int.fract y + θ) = Int.fract (y + θ) := by
    intro y
    have harg : Int.fract y + θ = (y + θ) - ((⌊y⌋ : ℤ) : ℝ) := by
      rw [← Int.self_sub_floor]; ring
    rw [harg, Int.fract_sub_intCast]
  have hrec : ∀ m, x (m + 1) = Int.fract (x m + θ) := by
    intro m
    simp only [hx_def]
    rw [key]
    have harg : (((N + 1 + m * j : ℕ) : ℝ) * α + β) + θ =
        (((N + 1 + (m + 1) * j : ℕ) : ℝ) * α + β) - ((K : ℤ) : ℝ) := by
      rw [hθ_def]; push_cast; ring
    rw [harg, Int.fract_sub_intCast]
  obtain ⟨m, hmM, hmem⟩ := hM x hrec (Int.fract_nonneg _) (Int.fract_lt_one _)
    u hu0 hu1
  refine ⟨N + 1 + m * j, by omega, ?_, ?_⟩
  · have : m * j ≤ M * j := Nat.mul_le_mul_right j hmM
    omega
  · simpa only [hx_def] using hmem

set_option maxHeartbeats 1200000 in
-- Allow extra elaboration work for the arithmetic and combinatorial case splits.
/-- **Sturmian case**: mechanical tail ⇒ tail-covering.
Interface in ambient terms.

Step 3 (paper (2.10.7)–(2.10.11)):
`η := min α (1−α) / 4 ∈ (0, 1/8]`; `L` from `uniform_syndeticity` at arc
length `η/(2(k−1))`; `S₀` from `MH.subwindow`; `a n = a 0 + δn + e·q n` by
induction from `hgap`; for large `y`, solve `y − k·a0 = δs + ew` along the
admissible AP `s ≡ (y − k·a0)·δ⁻¹ (mod e)` (`ZMod e` inverse; `Nat.Coprime δ e`
from `hco` via `Nat.coprime_add_self_right`); `θ(s) = sα + kβ − w(s)` has
exact step `γ = δ + eα ∈ (0, k − 2η)` by (2.10.10)–(2.10.11); `X₀` large
makes `θ(s_min) < η`; the first admissible `θ ≥ η` lands in `[η, k−η]`
(no-skip); `MH.subwindow` yields the k indices; conclude via
`TailCovering.of_cofinite`. -/
theorem tailCovering_of_sturmian {k d₁ d₂ : ℕ} {a : ℕ → ℕ} (hk : 3 ≤ k)
    (hgaps : HasGapsIn d₁ d₂ a) (hd : d₂ ≤ k)
    (h : ℕ → Bool) (δ e : ℕ) (hδ : 0 < δ) (he : 0 < e)
    (hco : Nat.Coprime δ (δ + e)) (hd₂ : d₂ = δ + e)
    (hgap : ∀ n, gap a n = δ + e * (if h (n + 1) then 1 else 0))
    (α β : ℝ) (hα : Irrational α) (hαI : α ∈ Set.Ioo (0 : ℝ) 1)
    (hmech : ∀ n : ℕ, (qCount h n : ℤ) = ⌊(n : ℝ) * α + β⌋) :
    TailCovering k a := by
  apply TailCovering.of_cofinite
  have hα0 : 0 < α := hαI.1
  have hα1 : α < 1 := hαI.2
  have hkR : (3 : ℝ) ≤ k := by exact_mod_cast hk
  set η : ℝ := min α (1 - α) / 4 with hη
  have hmin0 : 0 < min α (1 - α) := lt_min hα0 (by linarith)
  have hη0 : 0 < η := by rw [hη]; linarith
  have hmin12 : min α (1 - α) ≤ 1 / 2 := by
    rcases le_total α (1 / 2) with hc | hc
    · exact le_trans (min_le_left _ _) hc
    · exact le_trans (min_le_right _ _) (by linarith)
  have hη8 : η ≤ 1 / 8 := by rw [hη]; linarith
  have hk1R : (0 : ℝ) < (k : ℝ) - 1 := by linarith
  set ε : ℝ := η / (2 * ((k : ℝ) - 1)) with hε
  have hε0 : 0 < ε := by rw [hε]; exact div_pos hη0 (by linarith)
  obtain ⟨L, hL0, hsyn0⟩ := uniform_syndeticity hα hε0
  obtain ⟨S₀, hSW⟩ := MH.subwindow h hmech hk hη0 hη8 L
    (fun u N h1 h2 => hsyn0 β u N h1 h2)
  -- Diophantine + θ-landing: every large integer has an admissible `(s, w)`.
  obtain ⟨X₀, hcore⟩ :
      ∃ X₀ : ℕ, ∀ x : ℕ, X₀ ≤ x → ∃ (s : ℕ) (w : ℤ),
        S₀ ≤ s ∧ η ≤ (s : ℝ) * α + k * β - w ∧ (s : ℝ) * α + k * β - w ≤ k - η ∧
        (δ : ℤ) * s + e * w = (x : ℤ) - k * (a 0) := by
    have hδe : Nat.Coprime δ e :=
      Nat.coprime_add_self_right.mp (by rwa [Nat.add_comm] at hco)
    set A : ℤ := Nat.gcdA δ e with hA
    set B : ℤ := Nat.gcdB δ e with hB
    have hAB : (δ : ℤ) * A + e * B = 1 := by
      have h := Nat.gcd_eq_gcd_ab δ e
      rw [show Nat.gcd δ e = 1 from hδe] at h; push_cast at h; linarith
    set γ : ℝ := (δ : ℝ) + e * α with hγdef
    have heR : (1 : ℝ) ≤ e := by exact_mod_cast he
    have hδR : (1 : ℝ) ≤ δ := by exact_mod_cast hδ
    have hγ0 : 0 < γ := by rw [hγdef]; nlinarith [hα0, heR, hδR]
    have hγk : γ ≤ (k : ℝ) - 2 * η := by
      have hd2R : (d₂ : ℝ) = δ + e := by rw [hd₂]; push_cast; ring
      have hd2k : (d₂ : ℝ) ≤ k := by exact_mod_cast hd
      have hmul : (1 : ℝ) * (1 - α) ≤ e * (1 - α) :=
        mul_le_mul_of_nonneg_right heR (by linarith)
      have hγd2 : γ = (d₂ : ℝ) - e * (1 - α) := by rw [hγdef, hd2R]; ring
      rw [hη]; linarith [min_le_right α (1 - α), hmul, hd2k, hγd2]
    have hABR : (δ : ℝ) * A + e * B = 1 := by exact_mod_cast hAB
    clear_value A B
    set M1 : ℝ := γ * S₀ + e * (k * β - η) with hM1
    set M2 : ℝ := δ * (η + γ - k * β) / α with hM2
    have hM1toNat : M1 ≤ (⌈M1⌉.toNat : ℝ) :=
      le_trans (Int.le_ceil M1) (by exact_mod_cast Int.self_le_toNat ⌈M1⌉)
    have hM2toNat : M2 ≤ (⌈M2⌉.toNat : ℝ) :=
      le_trans (Int.le_ceil M2) (by exact_mod_cast Int.self_le_toNat ⌈M2⌉)
    refine ⟨k * a 0 + ⌈M1⌉.toNat + ⌈M2⌉.toNat + 1, fun x hx => ?_⟩
    set X : ℤ := (x : ℤ) - k * (a 0) with hX
    clear_value X
    have hXR : ((⌈M1⌉.toNat : ℝ) + ⌈M2⌉.toNat + 1) ≤ (X : ℝ) := by
      have hXge : (⌈M1⌉.toNat : ℤ) + ⌈M2⌉.toNat + 1 ≤ X := by rw [hX]; omega
      have hc : (((⌈M1⌉.toNat : ℤ) + ⌈M2⌉.toNat + 1 : ℤ) : ℝ) ≤ (X : ℝ) := by
        exact_mod_cast hXge
      push_cast at hc; linarith
    have hXM1 : M1 ≤ (X : ℝ) := by
      linarith [hM1toNat, hXR, Nat.cast_nonneg (α := ℝ) ⌈M2⌉.toNat]
    have hXM2 : M2 ≤ (X : ℝ) := by
      linarith [hM2toNat, hXR, Nat.cast_nonneg (α := ℝ) ⌈M1⌉.toNat]
    -- θ-landing
    set θ₀ : ℝ := (X : ℝ) * (A * α - B) + k * β with hθ0
    set n : ℤ := ⌈(η - θ₀) / γ⌉ with hn
    have hθn_lo : η ≤ θ₀ + n * γ := by
      have h1 : (η - θ₀) / γ ≤ (n : ℝ) := by rw [hn]; exact Int.le_ceil _
      have h2 := (div_le_iff₀ hγ0).mp h1; linarith
    have hθn_hi : θ₀ + n * γ < η + γ := by
      have h1 : (n : ℝ) < (η - θ₀) / γ + 1 := by rw [hn]; exact Int.ceil_lt_add_one _
      have h2 : (n : ℝ) * γ < ((η - θ₀) / γ + 1) * γ := by nlinarith [h1, hγ0]
      rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hγ0), one_mul] at h2; linarith
    clear_value θ₀ n
    set sn : ℤ := X * A + e * n with hsn
    set wn : ℤ := X * B - δ * n with hwn
    have hsnR' : (sn : ℝ) = (X : ℝ) * A + e * n := by rw [hsn]; push_cast; ring
    have hwnR' : (wn : ℝ) = (X : ℝ) * B - δ * n := by rw [hwn]; push_cast; ring
    have hθ_eq : (sn : ℝ) * α + k * β - wn = θ₀ + n * γ := by
      rw [hsnR', hwnR', hθ0, hγdef]; ring
    have algS : ∀ Xr Ar Br nr : ℝ, (δ : ℝ) * Ar + e * Br = 1 →
        ((δ : ℝ) + e * α) * (Xr * Ar + e * nr)
          = Xr + e * ((Xr * (Ar * α - Br) + k * β) + nr * ((δ : ℝ) + e * α) - k * β) := by
      intro Xr Ar Br nr hab; linear_combination Xr * hab
    have algW : ∀ Xr Ar Br nr : ℝ, (δ : ℝ) * Ar + e * Br = 1 →
        ((δ : ℝ) + e * α) * (Xr * Br - δ * nr)
          = α * Xr + δ * (k * β - ((Xr * (Ar * α - Br) + k * β) + nr * ((δ : ℝ) + e * α))) := by
      intro Xr Ar Br nr hab; linear_combination (α * Xr) * hab
    have hkey_s : γ * (sn : ℝ) = X + e * (θ₀ + n * γ - k * β) := by
      rw [hsnR', hθ0, hγdef]; exact algS X A B n hABR
    have hkey_w : γ * (wn : ℝ) = α * X + δ * (k * β - (θ₀ + n * γ)) := by
      rw [hwnR', hθ0, hγdef]; exact algW X A B n hABR
    have hsn0 : (0 : ℤ) ≤ sn := by
      have hemul : (e : ℝ) * η ≤ e * (θ₀ + n * γ) :=
        mul_le_mul_of_nonneg_left hθn_lo (by positivity)
      have hge : γ * (S₀ : ℝ) ≤ γ * (sn : ℝ) := by nlinarith [hkey_s, hemul, hXM1, hM1]
      have : (S₀ : ℝ) ≤ (sn : ℝ) := le_of_mul_le_mul_left hge hγ0
      have : (0 : ℝ) ≤ (sn : ℝ) := le_trans (by positivity) this
      exact_mod_cast this
    have hsnS0 : (S₀ : ℤ) ≤ sn := by
      have hemul : (e : ℝ) * η ≤ e * (θ₀ + n * γ) :=
        mul_le_mul_of_nonneg_left hθn_lo (by positivity)
      have hge : γ * (S₀ : ℝ) ≤ γ * (sn : ℝ) := by nlinarith [hkey_s, hemul, hXM1, hM1]
      have : (S₀ : ℝ) ≤ (sn : ℝ) := le_of_mul_le_mul_left hge hγ0
      exact_mod_cast this
    have hwn0 : (0 : ℤ) ≤ wn := by
      have hαM2 : (δ : ℝ) * (η + γ - k * β) ≤ α * X := by
        rw [hM2, div_le_iff₀ hα0] at hXM2; linarith
      have hge : γ * (0 : ℝ) ≤ γ * (wn : ℝ) := by
        rw [mul_zero]; nlinarith [hkey_w, hθn_hi, hαM2, hδR]
      have : (0 : ℝ) ≤ (wn : ℝ) := le_of_mul_le_mul_left hge hγ0
      exact_mod_cast this
    have hsnR : ((sn.toNat : ℕ) : ℝ) = (sn : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hsn0
    refine ⟨sn.toNat, wn, ?_, ?_, ?_, ?_⟩
    · have : (S₀ : ℤ) ≤ (sn.toNat : ℤ) := by rw [Int.toNat_of_nonneg hsn0]; exact hsnS0
      exact_mod_cast this
    · rw [hsnR]; linarith [hθ_eq, hθn_lo]
    · rw [hsnR]; linarith [hθ_eq, hθn_hi, hγk]
    · rw [Int.toNat_of_nonneg hsn0]; simp only [hsn, hwn]; linear_combination (X : ℤ) * hAB
  refine ⟨X₀, fun x hx => ?_⟩
  obtain ⟨s, w, hsS0, hθlo, hθhi, hdioph⟩ := hcore x hx
  obtain ⟨f, hf1, hfs, hfw⟩ := hSW s hsS0 w hθlo hθhi
  have hw0 : 0 ≤ w := by rw [← hfw]; positivity
  have hfwN : ((∑ j, qCount h (f j) : ℕ) : ℤ) = w := by rw [Nat.cast_sum]; exact hfw
  have hwN : w.toNat ∈ Wset h k s :=
    ⟨f, hfs, by rw [← hfwN, Int.toNat_natCast]⟩
  have hmem := mem_kFold_of_Wset hgaps h δ e hgap hwN
  have hwt : (w.toNat : ℤ) = w := Int.toNat_of_nonneg hw0
  have hxeq : x = k * a 0 + δ * s + e * w.toNat := by
    have hZ : (x : ℤ) = ((k * a 0 + δ * s + e * w.toNat : ℕ) : ℤ) := by
      push_cast [hwt]; linarith [hdioph]
    exact_mod_cast hZ
  rw [hxeq]; exact hmem

end Proof
end Erdos1112
