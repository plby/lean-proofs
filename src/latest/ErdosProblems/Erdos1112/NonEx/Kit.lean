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
Shared toolkit for the non-existence "easy half" files (`NonEx/Certificate.lean`,
`NonEx/GapWord.lean`, `NonEx/TwoLetter/Core.lean`, `NonEx/SlotLemma.lean`).

`TailCoveringN` is the normalized tail-covering notion (reduced residue
`ρ < m`, so the covered congruence class is genuinely infinite). It is the
form produced by all non-existence case lemmas and consumed by the certificate lemma (the
certificate). It coincides definitionally with `TailCovering`, which also
requires `ρ < m`.
-/
import ErdosProblems.Erdos1112.NonEx.TailCovering

namespace Erdos1112
namespace Proof

/-- Normalized tail-covering: `kA` contains the full congruence-class tail
`{x ≥ X₀ : x ≡ ρ (mod m)}` with a *reduced* residue `ρ < m` (so the class is
genuinely infinite). This is the notion produced by all non-existence case lemmas
and consumed by the certificate lemma. -/
def TailCoveringN (k : ℕ) (a : ℕ → ℕ) : Prop :=
  ∃ m, 0 < m ∧ ∃ ρ, ρ < m ∧ ∃ X₀, ∀ x, X₀ ≤ x → x % m = ρ → x ∈ kFoldSumset k a

/-- Normalized tail-covering coincides with `TailCovering` (both require
`ρ < m`; the two notions are definitionally identical, and this bridge is
the identity repackaging). -/
lemma TailCoveringN.toTailCovering {k : ℕ} {a : ℕ → ℕ} (h : TailCoveringN k a) :
    TailCovering k a := by
  obtain ⟨m, hm, ρ, hρ, X₀, hX⟩ := h
  exact ⟨m, hm, ρ, hρ, X₀, hX⟩

/-! ### `kFoldSumset` composition -/

/-- The empty sum. -/
lemma zero_mem_kFoldSumset_zero {a : ℕ → ℕ} : 0 ∈ kFoldSumset 0 a :=
  ⟨Fin.elim0, by simp⟩

/-- A single summand. -/
lemma single_mem_kFoldSumset {a : ℕ → ℕ} (i : ℕ) : a i ∈ kFoldSumset 1 a :=
  ⟨fun _ => i, by simp⟩

/-- Sums compose: `k₁A + k₂A ⊆ (k₁+k₂)A`. -/
lemma add_mem_kFoldSumset {k₁ k₂ : ℕ} {a : ℕ → ℕ} {u v : ℕ}
    (hu : u ∈ kFoldSumset k₁ a) (hv : v ∈ kFoldSumset k₂ a) :
    u + v ∈ kFoldSumset (k₁ + k₂) a := by
  obtain ⟨f, rfl⟩ := hu
  obtain ⟨g, rfl⟩ := hv
  refine ⟨Fin.append f g, ?_⟩
  rw [Fin.sum_univ_add]
  congr 1
  · exact Finset.sum_congr rfl fun j _ => by rw [Fin.append_left]
  · exact Finset.sum_congr rfl fun j _ => by rw [Fin.append_right]

/-! ### Sums over a one-point update -/

/-- Updating one coordinate of a `Fin k`-indexed sum, additively phrased
(no `ℕ`-subtraction): the per-index summand family `H` may depend on the
index. -/
lemma sum_update_add {k : ℕ} (H : Fin k → ℕ → ℕ) (f : Fin k → ℕ)
    (j₀ : Fin k) (c : ℕ) :
    (∑ j, H j (Function.update f j₀ c j)) + H j₀ (f j₀) =
      H j₀ c + ∑ j, H j (f j) := by
  have h1 : ∀ j, H j (Function.update f j₀ c j) =
      Function.update (fun j => H j (f j)) j₀ (H j₀ c) j :=
    fun j => Function.apply_update (fun i v => H i v) f j₀ c j
  rw [Finset.sum_congr rfl fun j _ => h1 j,
    Finset.sum_update_of_mem (Finset.mem_univ j₀),
    Finset.sum_eq_sum_sdiff_singleton_add (Finset.mem_univ j₀)
      (fun j => H j (f j))]
  omega

/-! ### The AP covering constructor -/

/-- If some subsequence of `a` is the arithmetic progression `c + s·j`
(`j ≥ 0`), then `kA ⊇ {k·c + s·j : j ≥ 0}`. -/
lemma kfold_AP_mem {k c s : ℕ} {a : ℕ → ℕ} (hk : 0 < k) (g : ℕ → ℕ)
    (hg : ∀ j, a (g j) = c + s * j) (j : ℕ) :
    k * c + s * j ∈ kFoldSumset k a := by
  refine ⟨Function.update (fun _ => g 0) ⟨0, hk⟩ (g j), ?_⟩
  have h := sum_update_add (fun (_ : Fin k) v => a v) (fun _ => g 0) ⟨0, hk⟩ (g j)
  have hsum : (∑ _t : Fin k, a (g 0)) = k * a (g 0) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have h0 : a (g 0) = c := by have := hg 0; omega
  have hj : a (g j) = c + s * j := hg j
  have hka : k * a (g 0) = k * c := by rw [h0]
  omega

/-- The AP `{k·c + s·j : j ≥ 0} ⊆ kA` (`s ≥ 1`) gives normalized
tail-covering with modulus `s`. -/
lemma tailCoveringN_of_AP {k s c : ℕ} {a : ℕ → ℕ} (hs : 0 < s)
    (hmem : ∀ j, k * c + s * j ∈ kFoldSumset k a) : TailCoveringN k a := by
  refine ⟨s, hs, (k * c) % s, Nat.mod_lt _ hs, k * c, fun x hx hmod => ?_⟩
  have hdvd : s ∣ x - k * c :=
    (Nat.modEq_iff_dvd' hx).mp (show Nat.ModEq s (k * c) x from hmod.symm)
  obtain ⟨j, hj⟩ := hdvd
  have hx' : x = k * c + s * j := by omega
  rw [hx']
  exact hmem j

/-! ### Residue selection in a window (used by the sweep) -/

/-- For coprime `δ, e` (`e ≥ 1`), every window of `e` consecutive integers
contains an `s` with `δ·s ≡ y (mod e)`. -/
lemma exists_mul_mod_eq {δ e : ℕ} (he : 0 < e) (hco : Nat.Coprime δ e)
    (y lo : ℕ) : ∃ s, lo ≤ s ∧ s < lo + e ∧ δ * s % e = y % e := by
  have : NeZero e := ⟨he.ne'⟩
  have hu : IsUnit (δ : ZMod e) := (ZMod.isUnit_iff_coprime δ e).mpr hco
  set w : ZMod e := (δ : ZMod e)⁻¹ * (y : ZMod e) with hw
  set t := (w - (lo : ZMod e)).val with ht
  have htlt : t < e := ZMod.val_lt _
  refine ⟨lo + t, Nat.le_add_right _ _, by omega, ?_⟩
  have h1 : ((lo + t : ℕ) : ZMod e) = w := by
    push_cast [ht]
    rw [ZMod.natCast_val, ZMod.cast_id]
    ring
  have h2 : (δ : ZMod e) * w = (y : ZMod e) := by
    rw [hw, ← mul_assoc, ZMod.mul_inv_of_unit _ hu, one_mul]
  have h3 : ((δ * (lo + t) : ℕ) : ZMod e) = ((y : ℕ) : ZMod e) := by
    push_cast
    push_cast at h1
    rw [h1]
    exact_mod_cast h2
  exact (ZMod.natCast_eq_natCast_iff' _ _ _).mp h3

end Proof
end Erdos1112
