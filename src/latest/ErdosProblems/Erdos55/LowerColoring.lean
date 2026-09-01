/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/
import ErdosProblems.Erdos55.Core
import Mathlib.Data.Nat.Nth

/-!
# The rank-and-bit colorings in the CFP lower bound

An infinite subset of the positive integers has the canonical increasing
enumeration `Nat.nth (· ∈ A)`.  The hue of an element is its zero-based rank
modulo `h`.  Adding one bit gives `2*h` colors; the elementary decoding
lemmas below are the interface used by the red/blue estimates.
-/

namespace Erdos55

open scoped BigOperators

/-- The zero-based rank of `a` among the members of `A` below `a`. -/
noncomputable def rankIn (A : Set ℕ) (a : ℕ) : ℕ :=
  by
    classical
    exact Nat.count (fun n ↦ n ∈ A) a

/-- The `h`-valued hue assigned by the increasing enumeration of `A`. -/
noncomputable def hueIn (A : Set ℕ) (h : ℕ) (a : ℕ) : ℕ :=
  rankIn A a % h

theorem hueIn_lt {A : Set ℕ} {h a : ℕ} (hh : 0 < h) : hueIn A h a < h := by
  exact Nat.mod_lt _ hh

@[simp]
theorem rankIn_nth {A : Set ℕ} (hA : A.Infinite) (k : ℕ) :
    rankIn A (Nat.nth (fun n ↦ n ∈ A) k) = k := by
  classical
  change Nat.count (fun n ↦ n ∈ A) (Nat.nth (fun n ↦ n ∈ A) k) = k
  exact Nat.count_nth_of_infinite (p := fun n ↦ n ∈ A) hA k

@[simp]
theorem nth_rankIn {A : Set ℕ} {a : ℕ} (ha : a ∈ A) :
    Nat.nth (fun n ↦ n ∈ A) (rankIn A a) = a := by
  classical
  change Nat.nth (fun n ↦ n ∈ A) (Nat.count (fun n ↦ n ∈ A) a) = a
  exact Nat.nth_count ha

theorem rankIn_injective_on {A : Set ℕ} :
    Set.InjOn (rankIn A) A := by
  intro a ha b hb hab
  rw [← nth_rankIn ha, ← nth_rankIn hb, hab]

/-- Encode a hue and a Boolean bit in the disjoint intervals `[0,h)` and
`[h,2*h)`. -/
def encodeHueBit (h hue : ℕ) (bit : Bool) : ℕ :=
  if bit then h + hue else hue

theorem encodeHueBit_lt {h hue : ℕ} (hhue : hue < h) (bit : Bool) :
    encodeHueBit h hue bit < 2 * h := by
  cases bit <;> simp [encodeHueBit] at * <;> omega

theorem encodeHueBit_mod {h hue : ℕ} (hhue : hue < h)
    (bit : Bool) : encodeHueBit h hue bit % h = hue := by
  cases bit <;> simp [encodeHueBit, Nat.mod_eq_of_lt hhue]

theorem encodeHueBit_eq_iff {h hue₁ hue₂ : ℕ} (hh : 0 < h)
    (hhue₁ : hue₁ < h) (hhue₂ : hue₂ < h) (bit₁ bit₂ : Bool) :
    encodeHueBit h hue₁ bit₁ = encodeHueBit h hue₂ bit₂ ↔
      hue₁ = hue₂ ∧ bit₁ = bit₂ := by
  constructor
  · intro heq
    have hhue : hue₁ = hue₂ := by
      have := congrArg (fun n ↦ n % h) heq
      simpa [encodeHueBit_mod hhue₁, encodeHueBit_mod hhue₂] using this
    subst hue₂
    refine ⟨rfl, ?_⟩
    cases bit₁ <;> cases bit₂ <;> simp [encodeHueBit] at heq ⊢ <;> omega
  · rintro ⟨rfl, rfl⟩
    rfl

/-- The canonical hue-times-bit coloring of `A`. -/
noncomputable def hueBitColor (A : Set ℕ) (h : ℕ) (hh : 0 < h)
    (blue : ℕ → Bool) : A → Fin (2 * h) :=
  fun a ↦ ⟨encodeHueBit h (hueIn A h a) (blue a),
    encodeHueBit_lt (hueIn_lt hh) (blue a)⟩

theorem hueBitColor_eq_iff {A : Set ℕ} {h : ℕ} (hh : 0 < h)
    (blue : ℕ → Bool) (a b : A) :
    hueBitColor A h hh blue a = hueBitColor A h hh blue b ↔
      hueIn A h a = hueIn A h b ∧ blue a = blue b := by
  rw [Fin.mk.injEq]
  exact encodeHueBit_eq_iff hh (hueIn_lt hh) (hueIn_lt hh) _ _

/-- If `2*h ≤ r`, regard the hue-times-bit coloring as an `r`-coloring by
leaving the remaining colors unused. -/
noncomputable def hueBitColorCast (A : Set ℕ) (h r : ℕ) (hh : 0 < h)
    (hhr : 2 * h ≤ r) (blue : ℕ → Bool) : A → Fin r :=
  fun a ↦ Fin.castLE hhr (hueBitColor A h hh blue a)

theorem hueBitColorCast_eq_iff {A : Set ℕ} {h r : ℕ} (hh : 0 < h)
    (hhr : 2 * h ≤ r) (blue : ℕ → Bool) (a b : A) :
    hueBitColorCast A h r hh hhr blue a = hueBitColorCast A h r hh hhr blue b ↔
      hueIn A h a = hueIn A h b ∧ blue a = blue b := by
  change Fin.castLE hhr (hueBitColor A h hh blue a) =
      Fin.castLE hhr (hueBitColor A h hh blue b) ↔ _
  rw [Fin.castLE_inj, hueBitColor_eq_iff]

/-! ## The finite case -/

private theorem sum_finset_subtype_le_toFinset_sum {A : Set ℕ}
    (hA : A.Finite) (s : Finset A) :
    (∑ a ∈ s, (a : ℕ)) ≤ ∑ a ∈ hA.toFinset, a := by
  classical
  let e : A ↪ ℕ := Function.Embedding.subtype _
  have hmap : s.map e ⊆ hA.toFinset := by
    intro a ha
    rcases Finset.mem_map.mp ha with ⟨b, hb, rfl⟩
    exact hA.mem_toFinset.mpr b.property
  calc
    (∑ a ∈ s, (a : ℕ)) = ∑ a ∈ s.map e, a := by
      rw [Finset.sum_map]
      simp [e]
    _ ≤ ∑ a ∈ hA.toFinset, a :=
      Finset.sum_le_sum_of_subset_of_nonneg hmap (fun _ _ _ ↦ Nat.zero_le _)

/-- A finite set cannot be Ramsey complete for any positive number of
colors, since all of its subset sums are bounded by the sum of the set. -/
theorem finite_not_ramseyComplete {r : ℕ} (hr : 0 < r) {A : Set ℕ}
    (hA : A.Finite) : ¬ RamseyComplete r A := by
  intro hramsey
  let color : A → Fin r := fun _ ↦ ⟨0, hr⟩
  obtain ⟨N₀, hN₀⟩ := hramsey color
  let M := ∑ a ∈ hA.toFinset, a
  let n := N₀ + M + 1
  obtain ⟨i, s, hs, hsum⟩ := hN₀ n (by simp only [n]; omega)
  have hle := sum_finset_subtype_le_toFinset_sum hA s
  rw [hsum] at hle
  simp only [n, M] at hle
  omega

end Erdos55
