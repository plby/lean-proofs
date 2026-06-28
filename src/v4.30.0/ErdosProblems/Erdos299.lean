/- leanprover/lean4:v4.30.0  mathlib v4.30.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 299.
https://www.erdosproblems.com/forum/thread/299

Informal authors:
- Thomas Bloom

Formal authors:
- Bhavik Mehta
- Thomas Bloom

URLs:
- https://github.com/b-mehta/unit-fractions
-/
import ErdosProblems.Erdos298

namespace Erdos299

open UnitFractions

theorem not_erdos299 :
    ¬ ∃ a : ℕ → ℕ, StrictMono a ∧
      (∀ i : ℕ, 1 ≤ a i) ∧
      (∃ C : ℕ, ∀ i : ℕ, a (i + 1) - a i ≤ C) ∧
      ∀ S : Finset ℕ, rec_sum (S.image a) ≠ 1 := by
  intro h
  classical
  rcases h with ⟨a, ha, hapos, hgap, hnosum⟩
  rcases hgap with ⟨C, hC⟩
  let A : Set ℕ := Set.range a
  let D : ℕ := a 0 + C + 1
  have hDpos : 0 < (D : ℝ) := by
    exact_mod_cast (show 0 < D by
      dsimp [D]
      omega)
  have hbound : ∀ k : ℕ, a k ≤ a 0 + k * C := by
    intro k
    induction k with
    | zero =>
        simp
    | succ k hk =>
        calc
          a (k + 1) = a k + (a (k + 1) - a k) := by
            exact (Nat.add_sub_of_le (ha.monotone (Nat.le_succ k))).symm
          _ ≤ a k + C := by exact Nat.add_le_add_left (hC k) (a k)
          _ ≤ a 0 + k * C + C := by gcongr
          _ = a 0 + (k + 1) * C := by
            simp [Nat.succ_mul, Nat.add_assoc, Nat.add_comm]
  let T : Set ℕ := {N : ℕ | (1 / (D : ℝ)) ≤ partial_density A N}
  have himage : Set.range (fun k : ℕ => a k + 1) ⊆ T := by
    intro N hN
    rcases hN with ⟨k, rfl⟩
    have hsub :
        (Finset.range (k + 1)).image a ⊆
          (Finset.range (a k + 1)).filter fun n : ℕ => n ∈ A := by
      intro n hn
      rcases Finset.mem_image.mp hn with ⟨i, hi, rfl⟩
      refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · refine Finset.mem_range.mpr ?_
        exact lt_of_le_of_lt
          (ha.monotone (Nat.le_of_lt_succ (Finset.mem_range.mp hi)))
          (Nat.lt_succ_self _)
      · exact ⟨i, rfl⟩
    have hcard :
        k + 1 ≤ ((Finset.range (a k + 1)).filter fun n : ℕ => n ∈ A).card := by
      have hcardimg : ((Finset.range (k + 1)).image a).card = k + 1 := by
        rw [Finset.card_image_of_injective (Finset.range (k + 1)) ha.injective, Finset.card_range]
      rw [← hcardimg]
      exact Finset.card_le_card hsub
    have hcard' :
        (k + 1 : ℝ) ≤
          (((Finset.range (a k + 1)).filter fun n : ℕ => n ∈ A).card : ℝ) := by
      exact_mod_cast hcard
    have hboundk' : (((a k + 1 : ℕ) : ℝ)) ≤ (((a 0 + k * C + 1 : ℕ) : ℝ)) := by
      exact_mod_cast Nat.succ_le_succ (hbound k)
    have hgeom_nat : a 0 + k * C + 1 ≤ D * (k + 1) := by
      have ha0mul : a 0 ≤ a 0 * (k + 1) := by
        simpa [one_mul] using
          (Nat.mul_le_mul_left (a 0) (show 1 ≤ k + 1 by omega))
      have hkC : k * C ≤ (k + 1) * C := by
        exact Nat.mul_le_mul_right C (Nat.le_succ k)
      calc
        a 0 + k * C + 1 ≤ a 0 * (k + 1) + ((k + 1) * C + (k + 1)) := by
          omega
        _ = D * (k + 1) := by
          dsimp [D]
          ring
    have hgeom :
        (((a 0 + k * C + 1 : ℕ) : ℝ)) ≤ (D : ℝ) * (k + 1) := by
      exact_mod_cast hgeom_nat
    have hmain :
        (((a k + 1 : ℕ) : ℝ)) ≤
          (D : ℝ) *
            (((Finset.range (a k + 1)).filter fun n : ℕ => n ∈ A).card : ℝ) := by
      refine hboundk'.trans ?_
      refine hgeom.trans ?_
      gcongr
    dsimp [T]
    rw [partial_density]
    have hNpos : 0 < (((a k + 1 : ℕ) : ℝ)) := by positivity
    refine (le_div_iff₀ hNpos).2 ?_
    have hdiv :
        (((a k + 1 : ℕ) : ℝ) / D) ≤
          (((Finset.range (a k + 1)).filter fun n : ℕ => n ∈ A).card : ℝ) := by
      exact (div_le_iff₀ hDpos).2 (by simpa [mul_comm] using hmain)
    simpa [one_div, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hdiv
  have hTinf : T.Infinite := by
    refine (Set.infinite_range_of_injective ?_).mono himage
    intro x y hxy
    apply ha.injective
    exact Nat.succ.inj (by simpa [Nat.succ_eq_add_one] using hxy)
  have hfreq : ∃ᶠ N : ℕ in Filter.atTop, (1 / (D : ℝ)) ≤ partial_density A N := by
    rw [Nat.frequently_atTop_iff_infinite]
    exact hTinf
  have hupper : (1 / (D : ℝ)) ≤ upper_density A := by
    exact Filter.le_limsup_of_frequently_le hfreq
      (UnitFractions.is_bounded_under_le_partial_density (A := A))
  have hA : 0 < upper_density A := by
    exact lt_of_lt_of_le (one_div_pos.mpr hDpos) hupper
  rcases Erdos298.erdos298 A hA with ⟨S, hS, hrecS⟩
  let I : Finset ℕ := S.preimage a ha.injective.injOn
  have himageI : I.image a = S := by
    refine (Finset.image_preimage a S ha.injective.injOn).trans ?_
    ext n
    constructor
    · intro hn
      exact (Finset.mem_filter.mp hn).1
    · intro hn
      exact Finset.mem_filter.mpr ⟨hn, hS hn⟩
  have hrecI : rec_sum (I.image a) = 1 := by
    simpa [himageI] using hrecS
  exact hnosum I hrecI

#print axioms not_erdos299
-- 'Erdos299.not_erdos299' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos299
