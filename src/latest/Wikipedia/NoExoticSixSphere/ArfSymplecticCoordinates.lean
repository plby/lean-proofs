import Wikipedia.NoExoticSixSphere.ArfFiniteSums

/-!
# The symplectic-coordinate formula for the Arf invariant

Actual linear coordinates identifying the polar form with the standard
symplectic pairing determine the quadratic form from its values on the
coordinate vectors. The Gauss-sum invariant equals the usual sum of products
of paired values, so that expression is independent of the coordinates.

Existence of such coordinates and the geometric quadratic refinement are
separate from this calculation.
-/

open scoped BigOperators

namespace NoExoticSixSphere.Arf

variable {V : Type*} [AddCommGroup V] [Module F₂ V]

structure SymplecticCoordinates (q : QuadraticForm F₂ V) (ι : Type*) [Fintype ι] where
  equiv : V ≃ₗ[F₂] (ι → F₂ × F₂)
  polar : ∀ x y : ι → F₂ × F₂,
    q.polarBilin (equiv.symm x) (equiv.symm y) =
      ∑ i, ((x i).1 * (y i).2 + (x i).2 * (y i).1)

namespace SymplecticCoordinates

variable {q : QuadraticForm F₂ V} {ι : Type*} [Fintype ι] [DecidableEq ι]
  (C : SymplecticCoordinates q ι)

def pairMap (i : ι) : (F₂ × F₂) →ₗ[F₂] V :=
  C.equiv.symm.toLinearMap.comp (LinearMap.single F₂ (fun _ : ι ↦ F₂ × F₂) i)

def firstValue (i : ι) : F₂ := q (C.pairMap i (1, 0))

def secondValue (i : ι) : F₂ := q (C.pairMap i (0, 1))

theorem polar_pairMap (i j : ι) (p r : F₂ × F₂) :
    q.polarBilin (C.pairMap i p) (C.pairMap j r) =
      if i = j then p.1 * r.2 + p.2 * r.1 else 0 := by
  change q.polarBilin (C.equiv.symm (Pi.single i p))
    (C.equiv.symm (Pi.single j r)) = _
  rw [C.polar]
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl, Finset.sum_eq_single i]
    · simp
    · intro l _ hli
      simp [Pi.single_eq_of_ne hli]
    · simp
  · rw [if_neg hij]
    apply Finset.sum_eq_zero
    intro l _
    by_cases hli : l = i
    · subst l
      simp [Pi.single_eq_of_ne hij]
    · simp [Pi.single_eq_of_ne hli]

theorem polar_right_pairMap (v : V) (i : ι) (p : F₂ × F₂) :
    q.polarBilin v (C.pairMap i p) =
      (C.equiv v i).1 * p.2 + (C.equiv v i).2 * p.1 := by
  have he := C.polar (C.equiv v) (Pi.single i p)
  rw [C.equiv.symm_apply_apply] at he
  change q.polarBilin v (C.pairMap i p) = _ at he
  rw [he, Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [Pi.single_eq_of_ne hji]
  · simp

include C in
omit [DecidableEq ι] in
theorem nondegenerate : q.polarBilin.Nondegenerate := by
  classical
  have hleft : q.polarBilin.SeparatingLeft := by
    intro v hv
    apply C.equiv.injective
    rw [map_zero]
    funext i
    have h₀ := hv (C.pairMap i (0, 1))
    have h₁ := hv (C.pairMap i (1, 0))
    simp only [C.polar_right_pairMap, mul_one, mul_zero, add_zero, zero_add] at h₀ h₁
    exact Prod.ext h₀ h₁
  refine ⟨hleft, ?_⟩
  intro v hv
  apply hleft v
  intro w
  exact (QuadraticMap.polar_comm q v w).trans (hv w)

theorem quadratic_pairMap (i : ι) (p : F₂ × F₂) :
    q (C.pairMap i p) = plane (C.firstValue i) (C.secondValue i) p := by
  apply quadratic_plane_formula (q.comp (C.pairMap i))
  change q (C.pairMap i ((1, 0) + (0, 1))) - q (C.pairMap i (1, 0)) -
    q (C.pairMap i (0, 1)) = 1
  rw [map_add]
  change q.polarBilin (C.pairMap i (1, 0)) (C.pairMap i (0, 1)) = 1
  rw [C.polar_pairMap]
  simp

theorem reconstruct (x : ι → F₂ × F₂) :
    C.equiv.symm x = ∑ i, C.pairMap i (x i) := by
  change C.equiv.symm x = ∑ i, C.equiv.symm (Pi.single i (x i))
  rw [← map_sum, LinearMap.sum_single_apply]

theorem quadratic_formula (x : ι → F₂ × F₂) :
    q (C.equiv.symm x) = ∑ i, plane (C.firstValue i) (C.secondValue i) (x i) := by
  rw [C.reconstruct]
  rw [quadratic_sum_of_orthogonal q Finset.univ (fun i ↦ C.pairMap i (x i))]
  · apply Finset.sum_congr rfl
    intro i _
    exact C.quadratic_pairMap i (x i)
  · intro i _ j _ hij
    rw [C.polar_pairMap, if_neg hij]

variable [Fintype V]

theorem gaussSum_formula : gaussSum q =
    (2 : ℤ) ^ Fintype.card ι * sign (∑ i, C.firstValue i * C.secondValue i) := by
  rw [← gaussSum_equiv q C.equiv.symm.toEquiv]
  change gaussSum (q ∘ C.equiv.symm) = _
  have he : (q ∘ C.equiv.symm) =
      ⇑(QuadraticMap.pi (fun i ↦ plane (C.firstValue i) (C.secondValue i))) := by
    funext x
    exact (C.quadratic_formula x).trans (QuadraticMap.pi_apply _ x).symm
  rw [he, gaussSum_planes]

theorem invariant_formula (hq : q.polarBilin.Nondegenerate) :
    invariant q hq = ∑ i, C.firstValue i * C.secondValue i := by
  unfold invariant
  rw [C.gaussSum_formula]
  exact signParity_pos_mul_sign _ (pow_pos (by norm_num) _) _

omit [Fintype V] in
theorem paired_sum_independent {κ : Type*} [Fintype κ] [DecidableEq κ]
    (D : SymplecticCoordinates q κ) :
    (∑ i, C.firstValue i * C.secondValue i) = ∑ j, D.firstValue j * D.secondValue j := by
  let : Fintype V := Fintype.ofEquiv (ι → F₂ × F₂) C.equiv.symm.toEquiv
  rw [← C.invariant_formula C.nondegenerate, ← D.invariant_formula C.nondegenerate]

end SymplecticCoordinates

end NoExoticSixSphere.Arf
