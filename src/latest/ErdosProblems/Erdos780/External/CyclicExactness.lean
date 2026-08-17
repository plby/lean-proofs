import ErdosProblems.Erdos780.External.CyclicAlgebra
import ErdosProblems.Erdos780.External.PeriodicDescent

open scoped BigOperators

namespace CyclicAlgebra

variable {p : ℕ} {ι : Type*}

/-! ## The two exactness identities -/

/-- The canonical partial-sum primitive on each cyclic orbit.  At coordinate
`a`, it is the sum of the coordinates strictly before `a` in the standard
representative interval `[0,p)`.
-/
def cyclicPrimitive [NeZero p] (x : FreeCyclic p ι) : FreeCyclic p ι :=
  fun i a => ∑ k ∈ Finset.range a.val, x i (k : ZMod p)

/-- The partial-sum primitive differentiates to `x` whenever the cyclic
coordinate sum of `x` is zero.  The wraparound coordinate is exactly where
the hypothesis `N x = 0` is used.
-/
theorem D_cyclicPrimitive_of_N_eq_zero [NeZero p]
    {x : FreeCyclic p ι} (hx : N x = 0) : D (cyclicPrimitive x) = x := by
  by_cases hp1 : p = 1
  · letI : Unique (ZMod p) := hp1 ▸ inferInstance
    have hx0 : x = 0 := by
      funext i a
      have h := congrFun (congrFun hx i) (0 : ZMod p)
      have hsum : (∑ b : ZMod p, x i b) = 0 := by
        simpa only [N_apply, Pi.zero_apply] using h
      calc
        x i a = ∑ b : ZMod p, x i b := by
          simp only [Fintype.sum_unique]
          congr 1
          exact Subsingleton.elim _ _
        _ = 0 := hsum
    rw [hx0]
    funext i a
    simp [D_apply, cyclicPrimitive]
  · have hp : 1 < p :=
      (Nat.one_lt_iff_ne_zero_and_ne_one).2 ⟨NeZero.ne p, hp1⟩
    letI : Fact (1 < p) := ⟨hp⟩
    funext i a
    rw [D_apply]
    change (∑ k ∈ Finset.range (a + 1).val, x i (k : ZMod p)) -
      (∑ k ∈ Finset.range a.val, x i (k : ZMod p)) = x i a
    have hsum_univ : (∑ b : ZMod p, x i b) = 0 := by
      have h := congrFun (congrFun hx i) 0
      simpa [N_apply] using h
    have hsum_range : (∑ k ∈ Finset.range p, x i (k : ZMod p)) = 0 := by
      rw [← Fin.sum_univ_eq_sum_range]
      have hconvert :
          (∑ k : Fin p, x i (k.val : ZMod p)) = ∑ b : ZMod p, x i b := by
        apply Fintype.sum_equiv (ZMod.finEquiv p)
        intro k
        congr 2
        have hv : (ZMod.finEquiv p k).val = k.val := by
          cases p with
          | zero => exact (NeZero.ne 0 rfl).elim
          | succ p => rfl
        exact (congrArg (fun n : ℕ => (n : ZMod p)) hv.symm).trans
          (ZMod.natCast_zmod_val (ZMod.finEquiv p k))
      exact hconvert.trans hsum_univ
    by_cases ha : a.val + 1 < p
    · have hval : (a + 1).val = a.val + 1 := by
        have hlt : a.val + (1 : ZMod p).val < p := by
          simpa [ZMod.val_one p] using ha
        simpa [ZMod.val_one p] using ZMod.val_add_of_lt hlt
      rw [hval, Finset.sum_range_succ, ZMod.natCast_zmod_val,
        add_sub_cancel_left]
    · have hap : a.val + 1 = p := by
        have hva := a.val_lt
        omega
      have hval : (a + 1).val = 0 := by
        rw [ZMod.val_add, ZMod.val_one p, hap, Nat.mod_self]
      have hsum_last :
          (∑ k ∈ Finset.range a.val, x i (k : ZMod p)) + x i a = 0 := by
        rw [← ZMod.natCast_zmod_val a]
        simpa [← hap, Finset.sum_range_succ] using hsum_range
      rw [hval]
      simp only [Finset.sum_range_zero, zero_sub]
      omega

/-- Explicit range witness for the kernel of `N`. -/
theorem exists_cyclicPrimitive_of_N_eq_zero [NeZero p]
    {x : FreeCyclic p ι} (hx : N x = 0) :
    ∃ y, D y = x :=
  ⟨cyclicPrimitive x, D_cyclicPrimitive_of_N_eq_zero hx⟩

/-- The kernel of the cyclic difference is contained in the range of the norm. -/
theorem ker_D_le_range_N [NeZero p] :
    (D : FreeCyclic p ι →+ FreeCyclic p ι).ker ≤
      (N : FreeCyclic p ι →+ FreeCyclic p ι).range := by
  intro x hx
  obtain ⟨y, hy⟩ := exists_N_of_D_eq_zero hx
  exact ⟨y, hy⟩

/-- The kernel of the norm is contained in the range of the cyclic difference.

The witness in `exists_cyclicPrimitive_of_N_eq_zero` is the explicit cyclic partial-sum
primitive.  Thus this statement does not use a choice of representatives or
any divisibility argument in `ℤ`.
-/
theorem ker_N_le_range_D [NeZero p] :
    (N : FreeCyclic p ι →+ FreeCyclic p ι).ker ≤
      (D : FreeCyclic p ι →+ FreeCyclic p ι).range := by
  intro x hx
  obtain ⟨y, hy⟩ := exists_cyclicPrimitive_of_N_eq_zero hx
  exact ⟨y, hy⟩

theorem range_N_le_ker_D [NeZero p] :
    (N : FreeCyclic p ι →+ FreeCyclic p ι).range ≤
      (D : FreeCyclic p ι →+ FreeCyclic p ι).ker := by
  rintro x ⟨y, rfl⟩
  have h := congrArg
    (fun f : FreeCyclic p ι →+ FreeCyclic p ι => f y)
    (D_comp_N (p := p) (ι := ι))
  simpa using h

theorem range_D_le_ker_N [NeZero p] :
    (D : FreeCyclic p ι →+ FreeCyclic p ι).range ≤
      (N : FreeCyclic p ι →+ FreeCyclic p ι).ker := by
  rintro x ⟨y, rfl⟩
  have h := congrArg
    (fun f : FreeCyclic p ι →+ FreeCyclic p ι => f y)
    (N_comp_D (p := p) (ι := ι))
  simpa using h

/-- Exactness at the `D` term of the two-periodic cyclic resolution. -/
theorem ker_D_eq_range_N [NeZero p] :
    (D : FreeCyclic p ι →+ FreeCyclic p ι).ker =
      (N : FreeCyclic p ι →+ FreeCyclic p ι).range :=
  le_antisymm ker_D_le_range_N range_N_le_ker_D

/-- Exactness at the `N` term of the two-periodic cyclic resolution. -/
theorem ker_N_eq_range_D [NeZero p] :
    (N : FreeCyclic p ι →+ FreeCyclic p ι).ker =
      (D : FreeCyclic p ι →+ FreeCyclic p ι).range :=
  le_antisymm ker_N_le_range_D range_D_le_ker_N

/-! ## Augmentation -/

/-- Cyclic differences have augmentation zero. -/
@[simp] theorem augmentation_D [NeZero p] [Fintype ι] (x : FreeCyclic p ι) :
    augmentation (D x) = 0 := by
  simp only [augmentation, AddMonoidHom.coe_mk, ZeroHom.coe_mk, D_apply]
  apply Finset.sum_eq_zero
  intro i _hi
  rw [Finset.sum_sub_distrib]
  have hshift : (∑ a : ZMod p, x i (a + 1)) = ∑ a : ZMod p, x i a := by
    exact Fintype.sum_equiv (Equiv.addRight 1) _ _ (fun _ => rfl)
  rw [hshift, sub_self]

theorem augmentation_eq_zero_of_mem_range_D [NeZero p] [Fintype ι]
    {x : FreeCyclic p ι}
    (hx : x ∈ (D : FreeCyclic p ι →+ FreeCyclic p ι).range) :
    augmentation x = 0 := by
  obtain ⟨y, rfl⟩ := hx
  exact augmentation_D y

theorem augmentation_eq_zero_of_N_eq_zero [NeZero p] [Fintype ι]
    {x : FreeCyclic p ι} (hx : N x = 0) : augmentation x = 0 := by
  apply augmentation_eq_zero_of_mem_range_D
  exact ker_N_le_range_D hx

/-- The norm has augmentation divisible by the orbit size. -/
theorem orbitSize_dvd_augmentation_N [NeZero p] [Fintype ι]
    (x : FreeCyclic p ι) : (p : ℤ) ∣ augmentation (N x) := by
  rw [augmentation_N]
  exact dvd_mul_right _ _

/-! ## Packaging for `PeriodicDescent` -/

/-- Package the explicit cyclic exactness identities as a
`PeriodicDescent.Datum`.  The boundary-specific hypotheses are deliberately
arguments: exactness of `D,N` is independent of the chain boundary.
-/
def periodicDatum [NeZero p]
    (boundary : FreeCyclic p ι →+ FreeCyclic p ι)
    (boundary_sq : ∀ x, boundary (boundary x) = 0)
    (boundary_D : ∀ x, boundary (D x) = D (boundary x))
    (boundary_N : ∀ x, boundary (N x) = N (boundary x)) :
    PeriodicDescent.Datum (FreeCyclic p ι) where
  boundary := boundary
  tau := D
  normOp := N
  boundary_sq := boundary_sq
  boundary_tau := boundary_D
  boundary_norm := boundary_N
  ker_tau := fun {_x} hx => exists_N_of_D_eq_zero hx
  ker_norm := fun {_x} hx => exists_cyclicPrimitive_of_N_eq_zero hx

/-- The cyclic periodic datum with zero chain boundary, useful for testing the
resolution independently of a geometric chain complex. -/
def zeroBoundaryDatum [NeZero p] :
    PeriodicDescent.Datum (FreeCyclic p ι) :=
  periodicDatum 0 (by simp) (by simp) (by simp)

end CyclicAlgebra

/-! ## Transport to an ambient free-orbit module -/

namespace CyclicExactness

open CyclicAlgebra

variable {p : ℕ} {ι A : Type*}
variable [NeZero p] [Fintype ι]
variable [AddCommGroup A] [Module ℤ A]

/-- Coordinate data identifying an ambient module with a union of free cyclic
orbits.  These three compatibility equations are precisely what an orbit
decomposition must establish. -/
structure Transport (p : ℕ) (ι A : Type*) [NeZero p] [Fintype ι]
    [AddCommGroup A] [Module ℤ A] where
  equiv : A ≃ₗ[ℤ] FreeCyclic p ι
  tau : A →+ A
  normOp : A →+ A
  augmentation : A →+ ℤ
  equiv_tau : ∀ x, equiv (tau x) = D (equiv x)
  equiv_norm : ∀ x, equiv (normOp x) = N (equiv x)
  augmentation_equiv : ∀ x, augmentation x = CyclicAlgebra.augmentation (equiv x)

namespace Transport

variable (T : Transport p ι A)

/-- Exactness at the difference operator, transported through free-orbit
coordinates. -/
theorem ker_tau {x : A} (hx : T.tau x = 0) : ∃ y, T.normOp y = x := by
  have hx' : D (T.equiv x) = 0 := by
    rw [← T.equiv_tau x, hx, map_zero]
  obtain ⟨z, hz⟩ := exists_N_of_D_eq_zero hx'
  refine ⟨T.equiv.symm z, T.equiv.injective ?_⟩
  rw [T.equiv_norm, T.equiv.apply_symm_apply, hz]

/-- Exactness at the norm operator, transported through free-orbit
coordinates. -/
theorem ker_norm {x : A} (hx : T.normOp x = 0) : ∃ y, T.tau y = x := by
  have hx' : N (T.equiv x) = 0 := by
    rw [← T.equiv_norm x, hx, map_zero]
  obtain ⟨z, hz⟩ := exists_cyclicPrimitive_of_N_eq_zero hx'
  refine ⟨T.equiv.symm z, T.equiv.injective ?_⟩
  rw [T.equiv_tau, T.equiv.apply_symm_apply, hz]

/-- The ambient norm multiplies augmentation by the orbit size. -/
@[simp] theorem augmentation_norm (x : A) :
    T.augmentation (T.normOp x) = (p : ℤ) * T.augmentation x := by
  rw [T.augmentation_equiv, T.equiv_norm, CyclicAlgebra.augmentation_N,
    ← T.augmentation_equiv]

/-- The transported cyclic difference has augmentation zero. -/
@[simp] theorem augmentation_tau (x : A) :
    T.augmentation (T.tau x) = 0 := by
  rw [T.augmentation_equiv, T.equiv_tau, CyclicAlgebra.augmentation_D]

/-- Install the transported exactness equations directly into the descent
datum.  Only the usual boundary-square and equivariance laws remain as
arguments. -/
def toPeriodicDatum
    (boundary : A →+ A)
    (boundary_sq : ∀ x, boundary (boundary x) = 0)
    (boundary_tau : ∀ x, boundary (T.tau x) = T.tau (boundary x))
    (boundary_norm : ∀ x, boundary (T.normOp x) = T.normOp (boundary x)) :
    PeriodicDescent.Datum A where
  boundary := boundary
  tau := T.tau
  normOp := T.normOp
  boundary_sq := boundary_sq
  boundary_tau := boundary_tau
  boundary_norm := boundary_norm
  ker_tau := T.ker_tau
  ker_norm := T.ker_norm

/-- Both exactness implications and the norm-augmentation identity, as one
projection-free theorem. -/
theorem exactness_and_augmentation :
    (∀ {x : A}, T.tau x = 0 → ∃ y, T.normOp y = x) ∧
    (∀ {x : A}, T.normOp x = 0 → ∃ y, T.tau y = x) ∧
    (∀ x : A, T.augmentation (T.normOp x) = (p : ℤ) * T.augmentation x) :=
  ⟨fun hx ↦ T.ker_tau hx, fun hx ↦ T.ker_norm hx, T.augmentation_norm⟩

end Transport
end CyclicExactness
