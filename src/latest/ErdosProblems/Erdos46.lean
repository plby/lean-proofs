/- leanprover/lean4:v4.32.0  mathlib v4.32.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 46.
https://www.erdosproblems.com/forum/thread/46

Informal authors:
- Ernest S. Croot III

Formal authors:
- Bhavik Mehta
- Thomas Bloom

URLs:
- https://github.com/b-mehta/unit-fractions
-/
import ErdosProblems.Erdos298

namespace Erdos46

open UnitFractions

theorem erdos46 :
    ∀ {α : Type*} [Finite α] (c : ℤ → α),
      ∃ S : Finset ℕ, (∀ n ∈ S, 2 ≤ n) ∧ rec_sum S = 1 ∧ ∃ a : α, ∀ n ∈ S, c (n : ℤ) = a := by
  intro α _ c
  classical
  letI := Fintype.ofFinite α
  have hcard : 0 < Fintype.card α := Fintype.card_pos_iff.mpr ⟨c 0⟩
  letI : Nonempty α := ⟨c 0⟩
  let m : ℕ := Fintype.card α
  have hmpos : 0 < (m : ℝ) := by
    exact_mod_cast (by simpa [m] using hcard : 0 < m)
  let Acol : α → Set ℕ := fun a => {n : ℕ | c (n : ℤ) = a}
  have hblock :
      ∀ k : ℕ, ∃ a : α,
        k ≤ ((Finset.range (m * k)).filter fun n : ℕ => n ∈ Acol a).card := by
    intro k
    obtain ⟨a, -, ha⟩ :=
      Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to
        (s := Finset.range (m * k)) (t := (Finset.univ : Finset α))
        (f := fun n : ℕ => c (n : ℤ)) (n := k)
        (fun _ _ => by simp) Finset.univ_nonempty (by simp [m])
    refine ⟨a, ?_⟩
    simpa [Acol] using ha
  let g : ℕ → α := fun k => Classical.choose (hblock k)
  have hg :
      ∀ k : ℕ,
        k ≤ ((Finset.range (m * k)).filter fun n : ℕ => n ∈ Acol (g k)).card := by
    intro k
    exact Classical.choose_spec (hblock k)
  obtain ⟨a, haInf⟩ := Finite.exists_infinite_fiber g
  have haInf' : (g ⁻¹' {a}).Infinite := by
    exact Set.infinite_coe_iff.mp haInf
  let K' : Set ℕ := (g ⁻¹' {a}) \ {0}
  have hK' : K'.Infinite := Set.Infinite.diff haInf' (Set.finite_singleton 0)
  let T : Set ℕ := {N : ℕ | (1 / (m : ℝ)) ≤ partial_density (Acol a) N}
  have himage : (fun k : ℕ => m * k) '' K' ⊆ T := by
    intro N hN
    rcases hN with ⟨k, hk, rfl⟩
    have hk0 : 0 < k := Nat.pos_iff_ne_zero.mpr (by simpa using hk.2)
    have hka : g k = a := by simpa using hk.1
    have hkcount :
        k ≤ ((Finset.range (m * k)).filter fun n : ℕ => n ∈ Acol a).card := by
      simpa [g, hka] using hg k
    have hmkpos : 0 < (((m * k : ℕ) : ℝ)) := by
      exact_mod_cast Nat.mul_pos (by simpa [m] using hcard) hk0
    have hkcount' :
        (k : ℝ) ≤ (((Finset.range (m * k)).filter fun n : ℕ => n ∈ Acol a).card : ℝ) := by
      exact_mod_cast hkcount
    have hmne : (m : ℝ) ≠ 0 := by
      exact hmpos.ne'
    have hkne : (k : ℝ) ≠ 0 := by
      exact_mod_cast hk0.ne'
    dsimp [T]
    rw [partial_density]
    have hfrac : (1 / (m : ℝ)) = (k : ℝ) / (((m * k : ℕ) : ℝ)) := by
      rw [Nat.cast_mul]
      field_simp [hmne, hkne]
    rw [hfrac]
    exact (div_le_div_iff_of_pos_right hmkpos).2 hkcount'
  have hinj : Set.InjOn (fun k : ℕ => m * k) K' := by
    intro x hx y hy hxy
    exact Nat.eq_of_mul_eq_mul_left (by simpa [m] using hcard) hxy
  have hTinf : T.Infinite := (hK'.image hinj).mono himage
  have hfreq : ∃ᶠ N : ℕ in Filter.atTop, (1 / (m : ℝ)) ≤ partial_density (Acol a) N := by
    rw [Nat.frequently_atTop_iff_infinite]
    exact hTinf
  have hupper :
      (1 / (m : ℝ)) ≤ upper_density (Acol a) := by
    exact Filter.le_limsup_of_frequently_le hfreq
      (UnitFractions.is_bounded_under_le_partial_density (A := Acol a))
  have hAcol : 0 < upper_density (Acol a) := by
    exact lt_of_lt_of_le (one_div_pos.mpr hmpos) hupper
  let B : Set ℕ := Acol a \ ({0, 1} : Set ℕ)
  have hpres : upper_density (Acol a) = upper_density B := by
    simpa [B] using (upper_density_preserved (A := Acol a) (S := ({0, 1} : Finset ℕ)))
  have hB : 0 < upper_density B := by
    rwa [← hpres]
  rcases Erdos298.erdos298 B hB with ⟨S, hS, hrecS⟩
  refine ⟨S, ?_, hrecS, a, ?_⟩
  · intro n hn
    have hnB : n ∈ B := hS hn
    have hnB' : c (n : ℤ) = a ∧ n ≠ 0 ∧ n ≠ 1 := by
      simpa [B, Acol, Set.mem_insert_iff] using hnB
    omega
  · intro n hn
    have hnB : n ∈ B := hS hn
    simpa [B, Acol, Set.mem_insert_iff] using hnB.1

#print axioms erdos46
-- 'Erdos46.erdos46' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos46
