import Mathlib
import ErdosProblems.Erdos336.Basic
import ErdosProblems.Erdos336.LowerConstruction

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Exact exponent of the two-residue lower construction
-/

namespace Erdos336.Problem336

open Erdos336

/-- The two residues in the cyclic lower construction. -/
def lowerResidues (u : ℕ) : Set (ZMod (lowerModulus u)) :=
  {z | z = 1 ∨ z = (lowerStep u : ZMod (lowerModulus u))}

private lemma lower_modulus_pos (u : ℕ) : 0 < lowerModulus u := by
  simp [lowerModulus]

/-- Every sum of `l` copies of the two residues has the normal form
`l+j(x-1)` with `j≤l`. -/
lemma lowerResidues_sum_normal_form
    (u : ℕ) (xs : List (ZMod (lowerModulus u)))
    (hxs : ∀ z ∈ xs, z ∈ lowerResidues u) :
    ∃ j : ℕ, j ≤ xs.length ∧
      xs.sum = (xs.length : ZMod (lowerModulus u)) +
        (j : ZMod (lowerModulus u)) *
          ((lowerStep u : ZMod (lowerModulus u)) - 1) := by
  induction xs with
  | nil => exact ⟨0, by simp, by simp⟩
  | cons a xs ih =>
      have ha := hxs a (by simp)
      have htail : ∀ z ∈ xs, z ∈ lowerResidues u := by
        intro z hz
        exact hxs z (by simp [hz])
      obtain ⟨j, hj, hsum⟩ := ih htail
      rcases ha with ha | ha
      · refine ⟨j, by simp; omega, ?_⟩
        rw [List.sum_cons, ha, hsum]
        simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
        ring
      · refine ⟨j + 1, by simp; omega, ?_⟩
        rw [List.sum_cons, ha, hsum]
        simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
        push_cast
        ring

/-- At time `g-1`, every residue has an exact representation by the two
construction residues. -/
theorem lowerResidues_all_exact
    (u : ℕ) (hu : 1 ≤ u) (y : ZMod (lowerModulus u)) :
    GroupRepExactly (lowerResidues u) (lowerModulus u - 1) y := by
  let g := lowerModulus u
  let x := lowerStep u
  let k := g - 1
  let z : ZMod g := y - (k : ZMod g)
  let n := z.val
  obtain ⟨j, hjg, hjmod⟩ := lower_difference_hits_every_residue u n hu
  have hjk : j ≤ k := by
    dsimp [k, g]
    omega
  let xs : List (ZMod g) :=
    List.replicate j (x : ZMod g) ++ List.replicate (k - j) 1
  refine ⟨xs, ?_, ?_, ?_⟩
  · dsimp [xs]
    simp [hjk, k, g]
  · intro a ha
    simp only [xs, List.mem_append, List.mem_replicate] at ha
    rcases ha with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · exact Or.inr rfl
    · exact Or.inl rfl
  · have : NeZero g := ⟨by dsimp [g]; exact Nat.ne_of_gt (lower_modulus_pos u)⟩
    have hjz :
        (((lowerStep u - 1) * j : ℕ) : ZMod g) = (n : ZMod g) := by
      apply (ZMod.natCast_eq_natCast_iff' _ _ g).mpr
      simpa [g] using hjmod
    have hnz : (n : ZMod g) = z := by
      exact ZMod.natCast_zmod_val z
    simp only [xs, List.sum_append, List.sum_replicate]
    simp only [nsmul_eq_mul]
    rw [show (x : ZMod g) = 1 + ((lowerStep u : ZMod g) - 1) by
      dsimp [x]; ring]
    rw [show (((lowerStep u - 1) * j : ℕ) : ZMod g) =
      (j : ZMod g) * ((lowerStep u : ZMod g) - 1) by
        rw [Nat.cast_mul, Nat.cast_sub (by simp [lowerStep])]
        ring] at hjz
    rw [Nat.cast_sub hjk]
    calc
      (j : ZMod g) * (1 + ((lowerStep u : ZMod g) - 1)) +
          ((k : ZMod g) - (j : ZMod g)) * 1 =
        (k : ZMod g) +
          (j : ZMod g) * ((lowerStep u : ZMod g) - 1) := by ring
      _ = (k : ZMod g) + (n : ZMod g) := by rw [hjz]
      _ = y := by rw [hnz]; dsimp [z]; ring

/-- Before time `g-1`, a concrete residue is missing. -/
theorem lowerResidues_not_all_exact_before
    (u l : ℕ) (hu : 1 ≤ u) (hl : l < lowerModulus u - 1) :
    ¬ (∀ y : ZMod (lowerModulus u), GroupRepExactly (lowerResidues u) l y) := by
  let g := lowerModulus u
  let x := lowerStep u
  let d : ZMod g := (x : ZMod g) - 1
  let y : ZMod g := (l : ZMod g) + (l + 1 : ℕ) * d
  intro hall
  obtain ⟨xs, hlen, hmem, hsum⟩ := hall y
  obtain ⟨j, hjl, hnormal⟩ := lowerResidues_sum_normal_form u xs hmem
  have hnormal' : xs.sum = (l : ZMod g) + (j : ZMod g) * d := by
    simpa [hlen, d, x, g] using hnormal
  have heq : (j : ZMod g) * d = (l + 1 : ℕ) * d := by
    dsimp [y] at hsum
    rw [hsum] at hnormal'
    exact add_left_cancel hnormal'.symm
  have hdunit : IsUnit d := by
    dsimp [d, x, g]
    rw [show (lowerStep u : ZMod (lowerModulus u)) - 1 =
      (lowerStep u - 1 : ℕ) by
        push_cast
        have : 1 ≤ lowerStep u := by simp [lowerStep]
        rw [Nat.cast_sub this]
        rfl]
    exact (ZMod.isUnit_iff_coprime (lowerStep u - 1) (lowerModulus u)).mpr
      (lower_step_sub_one_coprime u)
  have hcast : (j : ZMod g) = (l + 1 : ℕ) :=
    hdunit.mul_right_cancel heq
  have hdiffpos : 0 < l + 1 - j := by omega
  have hdiffsmall : l + 1 - j < g := by
    dsimp [g]
    omega
  have hzero : ((l + 1 - j : ℕ) : ZMod g) = 0 := by
    rw [Nat.cast_sub (by omega)]
    rw [hcast]
    simp
  have hgdiv : g ∣ l + 1 - j :=
    (ZMod.natCast_eq_zero_iff (l + 1 - j) g).mp hzero
  exact (Nat.not_dvd_of_pos_of_lt hdiffpos hdiffsmall) hgdiv

end Erdos336.Problem336
