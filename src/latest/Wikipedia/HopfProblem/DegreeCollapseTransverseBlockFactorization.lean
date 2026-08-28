import Wikipedia.HopfProblem.DegreeCollapseTransverseGermLinearization

/-!
# Block factorization of a transverse linear coordinate change

The invertible projected block and the full linear equivalence construct
the Schur complement as an actual continuous linear equivalence. Removing
the two shears gives a smooth path through invertible maps while keeping
the transverse projected block fixed. The remaining diagonal blocks are
not assumed connected to identity here.
-/

noncomputable section

open Set Function
open scoped ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.TransverseGerms

variable {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B]

def transverseBlockMap (P : A ≃L[ℝ] A) (S : B ≃L[ℝ] B)
    (Q : B →L[ℝ] A) (R : A →L[ℝ] B) : (A × B) →L[ℝ] (A × B) :=
  let T := P.toContinuousLinearMap.comp
    (ContinuousLinearMap.fst ℝ A B + Q.comp (ContinuousLinearMap.snd ℝ A B))
  T.prod (S.toContinuousLinearMap.comp (ContinuousLinearMap.snd ℝ A B) + R.comp T)

theorem transverseBlockMap_apply (P : A ≃L[ℝ] A) (S : B ≃L[ℝ] B)
    (Q : B →L[ℝ] A) (R : A →L[ℝ] B) (p : A × B) :
    transverseBlockMap P S Q R p = (P (p.1 + Q p.2), S p.2 + R (P (p.1 + Q p.2))) := rfl

theorem bijective_transverseBlockMap (P : A ≃L[ℝ] A) (S : B ≃L[ℝ] B)
    (Q : B →L[ℝ] A) (R : A →L[ℝ] B) : Bijective (transverseBlockMap P S Q R) := by
  constructor
  · intro x y hxy
    have hfirst : P (x.1 + Q x.2) = P (y.1 + Q y.2) := congrArg Prod.fst hxy
    have hsecond : S x.2 + R (P (x.1 + Q x.2)) =
        S y.2 + R (P (y.1 + Q y.2)) := congrArg Prod.snd hxy
    rw [hfirst] at hsecond
    have hy : x.2 = y.2 := S.injective (add_right_cancel hsecond)
    have hx := P.injective hfirst
    rw [hy] at hx
    exact Prod.ext (add_right_cancel hx) hy
  · intro y
    refine ⟨(P.symm y.1 - Q (S.symm (y.2 - R y.1)), S.symm (y.2 - R y.1)), ?_⟩
    rw [transverseBlockMap_apply]
    simp only [sub_add_cancel, P.apply_symm_apply, S.apply_symm_apply]

variable [FiniteDimensional ℝ B]

/-- The Schur complement and both shears are constructed from the original
linear map and its invertible transverse projected block. -/
theorem exists_transverse_block_factorization (C : (A × B) ≃L[ℝ] (A × B))
    (P : A ≃L[ℝ] A) (hP : ∀ x : A, (C (x, 0)).1 = P x) :
    ∃ (Q : B →L[ℝ] A) (R : A →L[ℝ] B) (S : B ≃L[ℝ] B),
      C.toContinuousLinearMap = transverseBlockMap P S Q R := by
  let Q : B →L[ℝ] A := P.symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.fst ℝ A B).comp
      (C.toContinuousLinearMap.comp (ContinuousLinearMap.inr ℝ A B)))
  let R : A →L[ℝ] B := (ContinuousLinearMap.snd ℝ A B).comp
    (C.toContinuousLinearMap.comp
      ((ContinuousLinearMap.inl ℝ A B).comp P.symm.toContinuousLinearMap))
  let S₀ : B →L[ℝ] B := (ContinuousLinearMap.snd ℝ A B).comp
      (C.toContinuousLinearMap.comp (ContinuousLinearMap.inr ℝ A B)) -
    R.comp ((ContinuousLinearMap.fst ℝ A B).comp
      (C.toContinuousLinearMap.comp (ContinuousLinearMap.inr ℝ A B)))
  have hQ (y : B) : P (Q y) = (C (0, y)).1 := P.apply_symm_apply _
  have hR (x : A) : R (P x) = (C (x, 0)).2 := by
    change (C (P.symm (P x), 0)).2 = _
    rw [P.symm_apply_apply]
  have hsplit (p : A × B) : C p = C (p.1, 0) + C (0, p.2) := by
    rw [← map_add]
    congr 1
    simp
  have hmodel (p : A × B) : C p =
      (P (p.1 + Q p.2), S₀ p.2 + R (P (p.1 + Q p.2))) := by
    apply Prod.ext
    · rw [hsplit, Prod.fst_add, map_add, hP, hQ]
    · rw [hsplit, Prod.snd_add, map_add, map_add, hR, hQ]
      change (C (p.1, 0)).2 + (C (0, p.2)).2 =
        ((C (0, p.2)).2 - R ((C (0, p.2)).1)) +
          ((C (p.1, 0)).2 + R ((C (0, p.2)).1))
      abel
  have haxis (y : B) : C (-Q y, y) = (0, S₀ y) := by
    rw [hmodel]
    simp
  have hbij : Bijective S₀ := by
    constructor
    · intro x y hxy
      have he : C (-Q x, x) = C (-Q y, y) := by rw [haxis, haxis, hxy]
      exact congrArg Prod.snd (C.injective he)
    · intro y
      obtain ⟨p, hp⟩ := C.surjective (0, y)
      have hfirst : P (p.1 + Q p.2) = 0 := by
        have hh := congrArg Prod.fst hp
        rwa [hmodel] at hh
      have hsecond : S₀ p.2 + R (P (p.1 + Q p.2)) = y := by
        have hh := congrArg Prod.snd hp
        rwa [hmodel] at hh
      exact ⟨p.2, by simpa only [hfirst, map_zero, add_zero] using hsecond⟩
  let S := (LinearEquiv.ofBijective S₀.toLinearMap hbij).toContinuousLinearEquiv
  refine ⟨Q, R, S, ?_⟩
  apply ContinuousLinearMap.ext
  intro p
  exact hmodel p

/-- Remove the two off-diagonal shears by a smooth family of actual
invertible linear maps, retaining the transverse projected block at all times. -/
theorem exists_transverse_linear_diagonalization (C : (A × B) ≃L[ℝ] (A × B))
    (P : A ≃L[ℝ] A) (hP : ∀ x : A, (C (x, 0)).1 = P x) :
    ∃ (S : B ≃L[ℝ] B) (H : ℝ × (A × B) → A × B), ContDiff ℝ ∞ H ∧
      (∀ x, H (0, x) = C x) ∧ (∀ x, H (1, x) = (P x.1, S x.2)) ∧
      (∀ t, Bijective (fun x => H (t, x))) ∧
      ∀ t x, (H (t, (x, (0 : B)))).1 = P x := by
  obtain ⟨Q, R, S, hfactor⟩ := exists_transverse_block_factorization C P hP
  let H : ℝ × (A × B) → A × B := fun p =>
    (P (p.2.1 + (1 - p.1) • Q p.2.2),
      S p.2.2 + (1 - p.1) • R (P (p.2.1 + (1 - p.1) • Q p.2.2)))
  have hH : ContDiff ℝ ∞ H := by dsimp [H]; fun_prop
  refine ⟨S, H, hH, ?_, ?_, ?_, ?_⟩
  · intro x
    have hh := congrArg (fun L : (A × B) →L[ℝ] (A × B) => L x) hfactor
    change C x = transverseBlockMap P S Q R x at hh
    simpa only [transverseBlockMap_apply, H, sub_zero, one_smul] using hh.symm
  · intro x
    simp only [H, sub_self, zero_smul, add_zero]
  · intro t
    exact bijective_transverseBlockMap P S ((1 - t) • Q) ((1 - t) • R)
  · intro t x
    simp only [H, map_zero, smul_zero, add_zero]

end Wikipedia.HopfProblem.DegreeCollapse.TransverseGerms
