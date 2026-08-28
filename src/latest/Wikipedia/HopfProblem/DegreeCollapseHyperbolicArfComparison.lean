import Wikipedia.HopfProblem.DegreeCollapseHyperbolicQuotientSplit

/-!
# Polar nondegeneracy and Arf comparison through a constructed hyperbolic splitting

An actual quadratic isometry transports the polar pairing. A product with
the standard hyperbolic plane is polar-nondegenerate exactly when its
other factor is. For finite spaces, the original integer Gauss sum is
twice that of the other factor, so its sign and hence the Arf invariant
are preserved. Nondegeneracy is transported, never inferred globally.
-/

noncomputable section

open Function

namespace Wikipedia.HopfProblem.DegreeCollapse.HyperbolicReduction

open NoExoticSixSphere.Arf

variable {V W : Type*} [AddCommGroup V] [Module F₂ V] [AddCommGroup W] [Module F₂ W]
  (q : QuadraticForm F₂ V) (q' : QuadraticForm F₂ W)

theorem polar_isometry (E : q.IsometryEquiv q') (x y : V) :
    q'.polarBilin (E x) (E y) = q.polarBilin x y := by
  change q' (E x + E y) - q' (E x) - q' (E y) = q (x + y) - q x - q y
  rw [← map_add, E.map_app, E.map_app, E.map_app]

theorem polar_nondegenerate_transport (E : q.IsometryEquiv q')
    (hq : q.polarBilin.Nondegenerate) : q'.polarBilin.Nondegenerate := by
  have hleft : q'.polarBilin.SeparatingLeft := by
    intro x hx
    have hz : E.symm x = 0 := by
      apply hq.1
      intro y
      have h := polar_isometry q q' E (E.symm x) y
      rw [E.apply_symm_apply] at h
      exact h.symm.trans (hx (E y))
    calc
      x = E (E.symm x) := (E.apply_symm_apply x).symm
      _ = E 0 := congrArg E hz
      _ = 0 := map_zero E
  refine ⟨hleft, ?_⟩
  intro x hx
  apply hleft x
  intro y
  exact (QuadraticMap.polar_comm q' x y).trans (hx y)

theorem polar_prod_left (x : V) (y : V × W) :
    (q.prod q').polarBilin (x, 0) y = q.polarBilin x y.1 := by
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, QuadraticMap.prod_apply,
    Prod.fst_add, Prod.snd_add, Prod.fst_zero, Prod.snd_zero, zero_add, map_zero, add_zero]
  abel

theorem polar_nondegenerate_prod_left (h : (q.prod q').polarBilin.Nondegenerate) :
    q.polarBilin.Nondegenerate := by
  have hleft : q.polarBilin.SeparatingLeft := by
    intro x hx
    have hz : (x, (0 : W)) = 0 := by
      apply h.1
      intro y
      rw [polar_prod_left]
      exact hx y.1
    exact congrArg Prod.fst hz
  refine ⟨hleft, ?_⟩
  intro x hx
  apply hleft x
  intro y
  exact (QuadraticMap.polar_comm q x y).trans (hx y)

variable (E : q.IsometryEquiv (q'.prod hyperbolicPlane))

include E

theorem nondegenerate_after_split (hq : q.polarBilin.Nondegenerate) :
    q'.polarBilin.Nondegenerate :=
  polar_nondegenerate_prod_left q' hyperbolicPlane
    (polar_nondegenerate_transport q (q'.prod hyperbolicPlane) E hq)

theorem nondegenerate_before_split (hq' : q'.polarBilin.Nondegenerate) :
    q.polarBilin.Nondegenerate :=
  polar_nondegenerate_transport (q'.prod hyperbolicPlane) q E.symm
    (nondegenerate_polar_prod q' hyperbolicPlane hq' (plane_nondegenerate 0 0))

theorem nondegenerate_split_iff : q.polarBilin.Nondegenerate ↔ q'.polarBilin.Nondegenerate :=
  ⟨nondegenerate_after_split q q' E, nondegenerate_before_split q q' E⟩

variable [Fintype V] [Fintype W]

theorem gaussSum_split : gaussSum q = 2 * gaussSum q' := by
  have he : (fun x ↦ (q'.prod hyperbolicPlane) (E x)) = q := funext E.map_app
  have h := gaussSum_equiv (q'.prod hyperbolicPlane) E.toEquiv
  change gaussSum (fun x ↦ (q'.prod hyperbolicPlane) (E x)) = gaussSum (q'.prod hyperbolicPlane) at h
  rw [he] at h
  have hplane : gaussSum hyperbolicPlane = 2 := by
    rw [gaussSum_plane, zero_mul, sign_zero, mul_one]
  calc
    gaussSum q = gaussSum (q'.prod hyperbolicPlane) := h
    _ = gaussSum q' * gaussSum hyperbolicPlane := gaussSum_prod q' hyperbolicPlane
    _ = 2 * gaussSum q' := by rw [hplane, mul_comm]

theorem gaussSign_split : signParity (gaussSum q) = signParity (gaussSum q') := by
  rw [gaussSum_split q q' E]
  have h : 2 * gaussSum q' < 0 ↔ gaussSum q' < 0 := by omega
  simp only [signParity, h]

theorem arf_split (hq : q.polarBilin.Nondegenerate) :
    invariant q hq = invariant q' (nondegenerate_after_split q q' E hq) :=
  gaussSign_split q q' E

end Wikipedia.HopfProblem.DegreeCollapse.HyperbolicReduction
