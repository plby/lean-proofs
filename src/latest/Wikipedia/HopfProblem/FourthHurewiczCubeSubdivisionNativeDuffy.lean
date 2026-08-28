import Wikipedia.HopfProblem.FourthHurewiczCubeSubdivisionNativeBasic
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

/-!
# Product parametrizations of ordered simplices in every cube dimension

Prefix products give the actual Duffy maps. A zero parameter puts a suffix
on the outer zero face, while a unit parameter identifies adjacent ordered
coordinates. These formulas hold without a dimension-specific enumeration.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.HigherHurewicz.NativeSubdivision

/-- The product of the first `k` coordinates; the empty prefix has value one. -/
def prefixProduct {n : ℕ} (u : NativeCube (Fin n)) (k : ℕ) : I :=
  ∏ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k), u i

@[simp] theorem prefixProduct_zero {n : ℕ} (u : NativeCube (Fin n)) :
    prefixProduct u 0 = 1 := by
  simp [prefixProduct]

theorem prefixProduct_succ {n : ℕ} (u : NativeCube (Fin n))
    (k : ℕ) (hk : k < n) :
    prefixProduct u (k + 1) = prefixProduct u k * u ⟨k, hk⟩ := by
  have hs : (Finset.univ.filter fun i : Fin n => i.val < k + 1) =
      insert ⟨k, hk⟩ (Finset.univ.filter fun i : Fin n => i.val < k) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Fin.ext_iff]
    omega
  unfold prefixProduct
  rw [hs, Finset.prod_insert (by simp)]
  exact mul_comm _ _

theorem prefixProduct_eq_zero_of_coordinate {n : ℕ} (u : NativeCube (Fin n))
    (k : ℕ) (i : Fin n) (hik : i.val < k) (hi : u i = 0) :
    prefixProduct u k = 0 :=
  Finset.prod_eq_zero (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hik⟩) hi

theorem prefixProduct_succ_of_one {n : ℕ} (u : NativeCube (Fin n))
    (i : Fin n) (hi : u i = 1) :
    prefixProduct u (i.val + 1) = prefixProduct u i.val := by
  rw [prefixProduct_succ u i.val i.isLt, hi, mul_one]

theorem continuous_prefixProduct (n k : ℕ) :
    Continuous (fun u : NativeCube (Fin n) => prefixProduct u k) := by
  unfold prefixProduct
  generalize Finset.univ.filter (fun i : Fin n => i.val < k) = s
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty] using
      (continuous_const : Continuous (fun _ : NativeCube (Fin n) => (1 : I)))
  | @insert i s hi ih =>
      simp only [Finset.prod_insert hi]
      exact ((continuous_subtype_val.comp (continuous_apply i)).mul
        (continuous_subtype_val.comp ih)).subtype_mk _

/-- The canonical product parametrization, in descending coordinate order. -/
def nativeDuffyCubeCanonical (n : ℕ) : C(NativeCube (Fin n), NativeCube (Fin n)) where
  toFun u i := prefixProduct u (i.val + 1)
  continuous_toFun := continuous_pi fun i => continuous_prefixProduct n (i.val + 1)

@[simp] theorem nativeDuffyCubeCanonical_apply {n : ℕ}
    (u : NativeCube (Fin n)) (i : Fin n) :
    nativeDuffyCubeCanonical n u i = prefixProduct u (i.val + 1) := rfl

/-- Permuting the output coordinates gives the actual ordered Duffy simplex. -/
def nativeDuffyCube {n : ℕ} (e : Equiv.Perm (Fin n)) :
    C(NativeCube (Fin n), NativeCube (Fin n)) where
  toFun u i := nativeDuffyCubeCanonical n u (e.symm i)
  continuous_toFun := continuous_pi fun i =>
    (continuous_apply (e.symm i)).comp (nativeDuffyCubeCanonical n).continuous

theorem nativeDuffyCube_apply {n : ℕ} (e : Equiv.Perm (Fin n))
    (u : NativeCube (Fin n)) (i : Fin n) :
    nativeDuffyCube e u i = prefixProduct u ((e.symm i).val + 1) := rfl

@[simp] theorem nativeDuffyCube_coordinate {n : ℕ} (e : Equiv.Perm (Fin n))
    (u : NativeCube (Fin n)) (i : Fin n) :
    nativeDuffyCube e u (e i) = prefixProduct u (i.val + 1) := by
  simp [nativeDuffyCube_apply]

theorem nativeDuffyCube_coordinate_eq_zero {n : ℕ}
    (e : Equiv.Perm (Fin n)) (u : NativeCube (Fin n))
    (i j : Fin n) (hij : i ≤ j) (hi : u i = 0) :
    nativeDuffyCube e u (e j) = 0 := by
  rw [nativeDuffyCube_coordinate]
  exact prefixProduct_eq_zero_of_coordinate u _ i (by omega) hi

theorem nativeDuffyCube_coordinate_zero_of_one {n : ℕ}
    (e : Equiv.Perm (Fin (n + 1))) (u : NativeCube (Fin (n + 1)))
    (hu : u 0 = 1) : nativeDuffyCube e u (e 0) = 1 := by
  rw [nativeDuffyCube_coordinate, prefixProduct_succ_of_one u 0 hu]
  exact prefixProduct_zero u

theorem nativeDuffyCube_adjacent_of_one {n : ℕ}
    (e : Equiv.Perm (Fin (n + 1))) (u : NativeCube (Fin (n + 1)))
    (i : Fin n) (hi : u i.succ = 1) :
    nativeDuffyCube e u (e i.castSucc) = nativeDuffyCube e u (e i.succ) := by
  rw [nativeDuffyCube_coordinate, nativeDuffyCube_coordinate,
    prefixProduct_succ_of_one u i.succ hi]
  rfl

/-- All parameter faces land in an outer face or a coordinate equality plane. -/
theorem nativeDuffyCube_boundary {n : ℕ} (e : Equiv.Perm (Fin n))
    (u : NativeCube (Fin n)) (hu : u ∈ Cube.boundary (Fin n)) :
    nativeDuffyCube e u ∈ Cube.boundary (Fin n) ∨
      ∃ i j : Fin n, i ≠ j ∧ nativeDuffyCube e u i = nativeDuffyCube e u j := by
  obtain ⟨i, hi | hi⟩ := hu
  · exact Or.inl ⟨e i, Or.inl (nativeDuffyCube_coordinate_eq_zero e u i i le_rfl hi)⟩
  · cases n with
    | zero => exact Fin.elim0 i
    | succ n =>
      cases i using Fin.cases with
      | zero => exact Or.inl ⟨e 0, Or.inr (nativeDuffyCube_coordinate_zero_of_one e u hi)⟩
      | succ i =>
        exact Or.inr ⟨e i.castSucc, e i.succ,
          e.injective.ne (by intro h; have := congrArg Fin.val h; simp at this),
          nativeDuffyCube_adjacent_of_one e u i hi⟩

variable {X : Type*} [TopologicalSpace X] {x : X}

theorem nativeDuffyCube_based {n : ℕ} (p : GenLoop (Fin n) X x)
    (hp : NativeCubeInternalBased p) (e : Equiv.Perm (Fin n))
    (u : NativeCube (Fin n)) (hu : u ∈ Cube.boundary (Fin n)) :
    p (nativeDuffyCube e u) = x := by
  rcases nativeDuffyCube_boundary e u hu with h | ⟨i, j, hij, h⟩
  · exact p.property _ h
  · exact hp _ i j hij h

/-- The pullback is a genuine native generalized loop on the original space. -/
def nativeDuffyCubeLoop {n : ℕ} (p : GenLoop (Fin n) X x)
    (hp : NativeCubeInternalBased p) (e : Equiv.Perm (Fin n)) : GenLoop (Fin n) X x :=
  nativeCubePullbackLoop p (nativeDuffyCube e) (nativeDuffyCube_based p hp e)

@[simp] theorem nativeDuffyCubeLoop_apply {n : ℕ} (p : GenLoop (Fin n) X x)
    (hp : NativeCubeInternalBased p) (e : Equiv.Perm (Fin n)) (u : NativeCube (Fin n)) :
    nativeDuffyCubeLoop p hp e u = p (nativeDuffyCube e u) := rfl

end Wikipedia.HopfProblem.HigherHurewicz.NativeSubdivision
