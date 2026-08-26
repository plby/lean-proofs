import ErdosProblems.Erdos69.ResidueModel
import ErdosProblems.Erdos69.CollisionPrimes

/-! # Residue models for the actual affine progression -/

open scoped BigOperators

namespace Erdos69.Elementary

theorem exists_affine_residues {ρ ι : Type*} (p : ρ → ℕ) (hp : ∀ j, 0 < p j)
    (Q b : ℕ) (hQ : ∀ j, Q.Coprime (p j)) (s : ι → ℕ)
    (hs : ∀ j i k, s i ≡ s k [MOD p j] → i = k) :
    ∃ r : ρ → ι → ℕ,
      (∀ j i t, p j ∣ b + Q * t + s i ↔ t ≡ r j i [MOD p j]) ∧
      ∀ j i k, r j i ≡ r j k [MOD p j] → i = k := by
  classical
  choose r hr using fun j i ↦ exists_affine_residue (p j) Q (b + s i) (hp j) (hQ j)
  have hr' (j : ρ) (i : ι) (t : ℕ) :
      p j ∣ b + Q * t + s i ↔ t ≡ r j i [MOD p j] := by
    simpa only [Nat.add_right_comm] using hr j i t
  refine ⟨r, hr', ?_⟩
  intro j i k hik
  have hi := (hr' j i (r j i)).mpr Nat.ModEq.rfl
  have hk := (hr' j k (r j i)).mpr hik
  have heq : b + Q * r j i + s i ≡ b + Q * r j i + s k [MOD p j] :=
    (Nat.modEq_zero_iff_dvd.mpr hi).trans (Nat.modEq_zero_iff_dvd.mpr hk).symm
  exact hs j i k (heq.add_left_cancel' _)

namespace FiniteLaw

variable {ρ ι : Type*} [Fintype ρ] [Fintype ι] [DecidableEq ρ] [DecidableEq ι]

theorem affine_moment_error (p : ρ → ℕ) (hp : ∀ j, 0 < p j)
    (hcop : Pairwise (fun i j ↦ (p i).Coprime (p j)))
    (Q b : ℕ) (hQ : ∀ j, Q.Coprime (p j)) (s : ι → ℕ)
    (hs : ∀ j i k, s i ≡ s k [MOD p j] → i = k)
    (hc : ∀ j, Fintype.card ι ≤ p j) (c : ι → ℝ) (T : ℕ) (hT : 0 < T) (m : ℕ) :
    |(uniform T hT).mean (fun t ↦
        (∑ j, ∑ i, c i * (if p j ∣ b + Q * t.val + s i then (1 : ℝ) else 0)) ^ m) -
      (independentProduct (fun j ↦ categorical ι (p j) (hp j) (hc j))).mean
        (fun x ↦ (∑ j, optionalValue c (x j)) ^ m)| ≤
      (1 : ℝ) / T * ((Fintype.card ρ : ℝ) * ∑ i, |c i|) ^ m := by
  obtain ⟨r, hr, hrdist⟩ := exists_affine_residues p hp Q b hQ s hs
  simp_rw [hr]
  exact residue_moment_error p hp hcop r hrdist c T hT m

end FiniteLaw

end Erdos69.Elementary
