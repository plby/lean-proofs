/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Uniform finite polynomial expansions on a diagonal sextic residue class.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Counting.LocalDiagonal

namespace Erdos477.Counting

open scoped BigOperators

variable {R : Type*} [CommRing R]

noncomputable def translateBivariate (x y : R) (F : MvPolynomial (Fin 2) R) :
    MvPolynomial (Fin 2) R :=
  MvPolynomial.eval₂ MvPolynomial.C
    ![MvPolynomial.C x + MvPolynomial.X 0, MvPolynomial.C y + MvPolynomial.X 1] F

lemma eval_translateBivariate (a b x y : R) (F : MvPolynomial (Fin 2) R) :
    MvPolynomial.eval ![x, y] (translateBivariate a b F) =
      MvPolynomial.eval ![a + x, b + y] F := by
  unfold translateBivariate
  rw [← MvPolynomial.eval_assoc]
  have hcoords : MvPolynomial.eval ![x, y] ∘
      ![MvPolynomial.C a + MvPolynomial.X 0, MvPolynomial.C b + MvPolynomial.X 1] =
      ![a + x, b + y] := by
    funext k
    fin_cases k <;> simp
  rw [hcoords]

/-- One polynomial expansion works for every point of the residue class and
every polynomial evaluated on the surface. The two free variables are
coordinate differences from the center. -/
theorem exists_diagonal_chart_expansion [IsLocalRing R] [BinomialRing R]
    (a : R) (ha : 6 * a = 1) (p : R) (hp : ¬ IsUnit p)
    (b : Fin 3 → Rˣ) (c : R) (center : Fin 3 → R) (hc : IsUnit (center 2)) (N : ℕ) :
    ∃ H : MvPolynomial (Fin 3) R → MvPolynomial (Fin 2) R,
      ∀ z : Fin 3 → R, p ∣ z 2 - center 2 →
        (∑ k, (b k : R) * z k ^ 6 = c) → ∀ F,
        p ^ N ∣ MvPolynomial.eval z F -
          MvPolynomial.eval ![z 0 - center 0, z 1 - center 1] (H F) := by
  obtain ⟨v, hv⟩ := hc
  let H := fun F => translateBivariate (center 0) (center 1)
    (onGraphApprox a v (diagonalGraph b c) N F)
  refine ⟨H, ?_⟩
  intro z hres hz F
  have hres' : p ∣ z 2 - (v : R) := by rw [hv]; exact hres
  have h := pow_dvd_eval_sub_onGraphApprox a ha p hp v (diagonalGraph b c) F
    (z 0) (z 1) (z 2) hres' (eval_diagonalGraph b c z hz) N
  have hvec : ![z 0, z 1, z 2] = z := by
    funext k
    fin_cases k <;> rfl
  dsimp only [H]
  rw [eval_translateBivariate, add_sub_cancel, add_sub_cancel]
  simpa only [hvec] using h

/-- Choose a unit coordinate and an expansion for a diagonal surface point.
No local parametrization is assumed: it is constructed from the truncated
binomial series proved above. -/
theorem exists_diagonal_expansion [IsLocalRing R] [BinomialRing R]
    (a : R) (ha : 6 * a = 1) (p : R) (hp : ¬ IsUnit p)
    (b : Fin 3 → Rˣ) (c : R) (hc : IsUnit c) (center : Fin 3 → R)
    (hcenter : ∑ k, (b k : R) * center k ^ 6 = c) (N : ℕ) :
    ∃ (e : Equiv.Perm (Fin 3)) (H : MvPolynomial (Fin 3) R → MvPolynomial (Fin 2) R),
      ∀ z : Fin 3 → R, (∀ k, p ∣ z k - center k) →
        (∑ k, (b k : R) * z k ^ 6 = c) → ∀ F,
        p ^ N ∣ MvPolynomial.eval z F -
          MvPolynomial.eval ![z (e 0) - center (e 0), z (e 1) - center (e 1)] (H F) := by
  obtain ⟨k, hk⟩ := diagonal_has_unit_coordinate b c hc center hcenter
  let e : Equiv.Perm (Fin 3) := Equiv.swap 2 k
  have he : e 2 = k := Equiv.swap_apply_left 2 k
  have hunit : IsUnit ((center ∘ e) 2) := by
    simpa only [Function.comp_apply, he] using hk
  obtain ⟨H, hH⟩ := exists_diagonal_chart_expansion a ha p hp (b ∘ e) c
    (center ∘ e) hunit N
  refine ⟨e, (fun F => H (MvPolynomial.rename e.symm F)), ?_⟩
  intro z hres hz F
  have hz' : ∑ i, ((b ∘ e) i : R) * (z ∘ e) i ^ 6 = c :=
    (Equiv.sum_comp e (fun i => (b i : R) * z i ^ 6)).trans hz
  have h := hH (z ∘ e) (hres (e 2)) hz' (MvPolynomial.rename e.symm F)
  rw [MvPolynomial.eval_rename] at h
  simpa only [Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id,
    Function.comp_apply] using h

#print axioms exists_diagonal_expansion
-- 'Erdos477.Counting.exists_diagonal_expansion' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Counting
