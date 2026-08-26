import ErdosProblems.Erdos941.Forms
import Mathlib.Data.ZMod.Basic

/-!
# The four integral half-turns on a sphere of norm two modulo three
-/

namespace Erdos941

abbrev Triple := ℤ × ℤ × ℤ
abbrev Axis := Bool × Bool

def sign (b : Bool) : ℤ := if b then 1 else -1

@[simp] theorem sign_sq (b : Bool) : sign b ^ 2 = 1 := by
  cases b <;> norm_num [sign]

def tripleNorm (v : Triple) : ℤ := norm3 v.1 v.2.1 v.2.2

def axisDot (a : Axis) (v : Triple) : ℤ :=
  v.1 + sign a.1 * v.2.1 + sign a.2 * v.2.2

def Admissible (a : Axis) (v : Triple) : Prop := (3 : ℤ) ∣ axisDot a v

instance (a : Axis) (v : Triple) : Decidable (Admissible a v) :=
  inferInstanceAs (Decidable ((3 : ℤ) ∣ axisDot a v))

def rotate (a : Axis) (v : Triple) : Triple :=
  let k := axisDot a v / 3
  (2 * k - v.1, 2 * sign a.1 * k - v.2.1, 2 * sign a.2 * k - v.2.2)

private theorem rotation_norm_identity (A B C e f k : ℤ) :
    norm3 (2 * k - A) (2 * e * k - B) (2 * f * k - C) - norm3 A B C =
      4 * k * (3 * k - (A + e * B + f * C)) +
        4 * k ^ 2 * ((e ^ 2 - 1) + (f ^ 2 - 1)) := by
  unfold norm3
  ring

theorem rotate_norm {a : Axis} {v : Triple} (h : Admissible a v) :
    tripleNorm (rotate a v) = tripleNorm v := by
  have hd : 3 * (axisDot a v / 3) = axisDot a v := Int.mul_ediv_cancel' h
  have hi := rotation_norm_identity v.1 v.2.1 v.2.2 (sign a.1) (sign a.2)
    (axisDot a v / 3)
  simp only [sign_sq, sub_self, add_zero, mul_zero] at hi
  change tripleNorm (rotate a v) - tripleNorm v =
    4 * (axisDot a v / 3) * (3 * (axisDot a v / 3) - axisDot a v) at hi
  rw [hd, sub_self, mul_zero] at hi
  exact sub_eq_zero.mp hi

theorem rotate_axisDot {a : Axis} {v : Triple} (h : Admissible a v) :
    axisDot a (rotate a v) = axisDot a v := by
  have hd : 3 * (axisDot a v / 3) = axisDot a v := Int.mul_ediv_cancel' h
  obtain ⟨e, f⟩ := a
  cases e <;> cases f <;>
    simp only [axisDot, rotate, sign, Bool.false_eq_true, ↓reduceIte, one_mul,
      neg_one_mul] at hd ⊢ <;> omega

theorem rotate_admissible {a : Axis} {v : Triple} (h : Admissible a v) :
    Admissible a (rotate a v) := by
  change (3 : ℤ) ∣ axisDot a (rotate a v)
  rw [rotate_axisDot h]
  exact h

theorem rotate_involutive {a : Axis} {v : Triple} (h : Admissible a v) :
    rotate a (rotate a v) = v := by
  rw [rotate]
  rw [rotate_axisDot h]
  apply Prod.ext
  · dsimp [rotate]
    ring
  · apply Prod.ext <;> dsimp [rotate] <;> ring

/-- Finite residue computation: exactly two of the four axes are integral. -/
private theorem admissible_residues (A B C : ZMod 3)
    (h : A ^ 2 + B ^ 2 + C ^ 2 = 2) :
    (Finset.univ.filter fun a : Axis =>
      A + (sign a.1 : ZMod 3) * B + (sign a.2 : ZMod 3) * C = 0).card = 2 := by
  revert A B C
  decide

theorem admissible_card {v : Triple} (h : tripleNorm v % 3 = 2) :
    (Finset.univ.filter fun a : Axis => Admissible a v).card = 2 := by
  have hcast : (v.1 : ZMod 3) ^ 2 + (v.2.1 : ZMod 3) ^ 2 +
      (v.2.2 : ZMod 3) ^ 2 = 2 := by
    have hd : (3 : ℤ) ∣ tripleNorm v - 2 := by omega
    have hh := (ZMod.intCast_zmod_eq_zero_iff_dvd (tripleNorm v - 2) 3).mpr hd
    push_cast at hh
    simpa [tripleNorm, norm3] using sub_eq_zero.mp hh
  convert admissible_residues (v.1 : ZMod 3) (v.2.1 : ZMod 3)
    (v.2.2 : ZMod 3) hcast using 2
  apply Finset.filter_congr
  intro a _
  change (3 : ℤ) ∣ axisDot a v ↔ _
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd (axisDot a v) 3).symm.trans
    (by simp only [axisDot, Int.cast_add, Int.cast_mul])

theorem exists_other_admissible {v : Triple} (h : tripleNorm v % 3 = 2)
    (a : Axis) : ∃ b : Axis, Admissible b v ∧ b ≠ a := by
  have hc := admissible_card h
  have hnot : ¬ (Finset.univ.filter fun b : Axis => Admissible b v) ⊆ {a} := by
    intro hs
    have := Finset.card_le_card hs
    simp only [Finset.card_singleton] at this
    omega
  obtain ⟨b, hb, hba⟩ := Finset.not_subset.mp hnot
  exact ⟨b, (Finset.mem_filter.mp hb).2, by simpa using hba⟩

theorem existsUnique_other_admissible {v : Triple} (h : tripleNorm v % 3 = 2)
    {a : Axis} (ha : Admissible a v) : ∃! b : Axis, Admissible b v ∧ b ≠ a := by
  obtain ⟨b, c, hbc, hset⟩ := Finset.card_eq_two.mp (admissible_card h)
  have mem_iff (x : Axis) : Admissible x v ↔ x = b ∨ x = c := by
    have hmem := congrArg (fun s : Finset Axis => x ∈ s) hset
    simpa using hmem
  have ha' := (mem_iff a).mp ha
  rcases ha' with rfl | rfl
  · refine ⟨c, ⟨(mem_iff c).mpr (Or.inr rfl), hbc.symm⟩, ?_⟩
    intro x hx
    exact ((mem_iff x).mp hx.1).resolve_left hx.2
  · refine ⟨b, ⟨(mem_iff b).mpr (Or.inl rfl), hbc⟩, ?_⟩
    intro x hx
    exact ((mem_iff x).mp hx.1).resolve_right hx.2

/-- A finite trajectory with its incoming axis recorded. Adjacent axes differ. -/
def Trajectory : ℕ → Triple → Axis → Prop
  | 0, _, _ => True
  | k + 1, v, a => ∃ b : Axis, Admissible b v ∧ b ≠ a ∧
      Trajectory k (rotate b v) b

theorem trajectory_exists (k : ℕ) {v : Triple} (h : tripleNorm v % 3 = 2)
    (a : Axis) : Trajectory k v a := by
  induction k generalizing v a with
  | zero => trivial
  | succ k ih =>
    obtain ⟨b, hb, hba⟩ := exists_other_admissible h a
    refine ⟨b, hb, hba, ih ?_ b⟩
    rwa [rotate_norm hb]

/-- On an odd-coordinate sphere, an integral rotation fixes the vector modulo four. -/
theorem rotate_all_odd_mod_four {a : Axis} {v : Triple} (h : Admissible a v)
    (hA : v.1 % 2 = 1) (hB : v.2.1 % 2 = 1) (hC : v.2.2 % 2 = 1) :
    (4 : ℤ) ∣ (rotate a v).1 - v.1 ∧
      (4 : ℤ) ∣ (rotate a v).2.1 - v.2.1 ∧
        (4 : ℤ) ∣ (rotate a v).2.2 - v.2.2 := by
  have hd : 3 * (axisDot a v / 3) = axisDot a v := Int.mul_ediv_cancel' h
  obtain ⟨e, f⟩ := a
  cases e <;> cases f <;>
    simp only [rotate, axisDot, sign, Bool.false_eq_true, ↓reduceIte,
      one_mul, neg_one_mul] at hd ⊢ <;> omega

/-- With two odd coordinates and one even coordinate, the vector is negated
modulo four. -/
theorem rotate_two_odd_mod_four {a : Axis} {v : Triple} (h : Admissible a v)
    (hA : v.1 % 2 = 1) (hB : v.2.1 % 2 = 0) (hC : v.2.2 % 2 = 1) :
    (4 : ℤ) ∣ (rotate a v).1 + v.1 ∧
      (4 : ℤ) ∣ (rotate a v).2.1 + v.2.1 ∧
        (4 : ℤ) ∣ (rotate a v).2.2 + v.2.2 := by
  have hd : 3 * (axisDot a v / 3) = axisDot a v := Int.mul_ediv_cancel' h
  obtain ⟨e, f⟩ := a
  cases e <;> cases f <;>
    simp only [rotate, axisDot, sign, Bool.false_eq_true, ↓reduceIte,
      one_mul, neg_one_mul] at hd ⊢ <;> omega

theorem rotate_preserves_fourteen_parity {a : Axis} {v : Triple}
    (h : Admissible a v) (hA : v.1 % 2 = 1) (hB : v.2.1 % 4 = 2)
    (hCA : (4 : ℤ) ∣ v.2.2 - v.1) :
    (rotate a v).1 % 2 = 1 ∧ (rotate a v).2.1 % 4 = 2 ∧
      (4 : ℤ) ∣ (rotate a v).2.2 - (rotate a v).1 := by
  have hB2 : v.2.1 % 2 = 0 := by omega
  have hC2 : v.2.2 % 2 = 1 := by omega
  obtain ⟨hX, hY, hZ⟩ := rotate_two_odd_mod_four h hA hB2 hC2
  omega

end Erdos941
