import ErdosProblems.Erdos587.NVDevelopment

/-!
Linear lifting inside a twice-proper generalized arithmetic progression.
An arithmetic progression in the carrier lifts to an affine line in the
coefficient box. In particular, a long progression cannot use a short side.
-/

namespace Erdos587.GeneralizedAP

/-- The coefficient sum of two parameters belongs to the doubled box. -/
def addParam (P : GeneralizedAP) (x y : P.Param) : (P.dilate 2).Param :=
  fun i => ⟨(x i : ℕ) + (y i : ℕ), by
    have hx := (x i).isLt
    have hy := (y i).isLt
    change (x i : ℕ) + (y i : ℕ) < 2 * P.length i + 1
    omega⟩

theorem eval_addParam (P : GeneralizedAP) (x y : P.Param) :
    (P.dilate 2).eval (P.addParam x y) = P.eval x + P.eval y := by
  change (2 : ℤ) * P.base +
      (∑ i : Fin P.rank, (((x i : ℕ) + (y i : ℕ) : ℕ) : ℤ) * P.step i) =
    (P.base + ∑ i : Fin P.rank, (x i : ℤ) * P.step i) +
      (P.base + ∑ i : Fin P.rank, (y i : ℤ) * P.step i)
  simp only [Nat.cast_add, add_mul, Finset.sum_add_distrib]
  ring

/-- Twice-properness lifts every additive quadruple in the carrier. -/
theorem param_add_eq_of_eval_add_eq (P : GeneralizedAP) (hP : P.TProper 2)
    (x y u v : P.Param) (h : P.eval x + P.eval y = P.eval u + P.eval v)
    (i : Fin P.rank) :
    (x i : ℤ) + (y i : ℤ) = (u i : ℤ) + (v i : ℤ) := by
  have heval : (P.dilate 2).eval (P.addParam x y) =
      (P.dilate 2).eval (P.addParam u v) := by
    rw [eval_addParam, eval_addParam, h]
  have hi := congrArg (fun z => (z i).val) (hP heval)
  change (x i : ℕ) + (y i : ℕ) = (u i : ℕ) + (v i : ℕ) at hi
  exact_mod_cast hi

/-- Choose coordinates on the carrier; the value outside it is irrelevant. -/
noncomputable def coordinates (P : GeneralizedAP) (a : ℤ) : P.Param :=
  if ha : a ∈ P.carrier then (P.mem_carrier_iff.mp ha).choose else fun _ => 0

theorem eval_coordinates (P : GeneralizedAP) {a : ℤ} (ha : a ∈ P.carrier) :
    P.eval (P.coordinates a) = a := by
  classical
  simp only [coordinates, dif_pos ha]
  exact (P.mem_carrier_iff.mp ha).choose_spec

/-- The lift of `0,a,...,h*a` has constant coordinate increments. -/
theorem coordinates_nsmul_sub (P : GeneralizedAP) (hP : P.TProper 2)
    (a : ℤ) {h : ℕ} (hh : 0 < h)
    (hmem : ∀ t ≤ h, t • a ∈ P.carrier) {t : ℕ} (ht : t ≤ h)
    (i : Fin P.rank) :
    (P.coordinates (t • a) i : ℤ) - (P.coordinates 0 i : ℤ) =
      (t : ℤ) * ((P.coordinates a i : ℤ) - (P.coordinates 0 i : ℤ)) := by
  have hzero : (0 : ℤ) ∈ P.carrier := by simpa using hmem 0 (Nat.zero_le _)
  have ha : a ∈ P.carrier := by simpa using hmem 1 hh
  induction t with
  | zero => simp
  | succ t ih =>
    have hrec := P.param_add_eq_of_eval_add_eq hP
      (P.coordinates ((t + 1) • a)) (P.coordinates 0)
      (P.coordinates (t • a)) (P.coordinates a) (by
        rw [P.eval_coordinates (hmem (t + 1) ht), P.eval_coordinates hzero,
          P.eval_coordinates (hmem t (by omega)), P.eval_coordinates ha]
        simp only [succ_nsmul, add_zero]) i
    have hprev := ih (by omega)
    push_cast
    nlinarith

/-- Endpoint bounds for the linear lift, relative to the coordinates of zero. -/
theorem coordinates_nsmul_bounds (P : GeneralizedAP) (hP : P.TProper 2)
    (a : ℤ) {h : ℕ} (hh : 0 < h)
    (hmem : ∀ t ≤ h, t • a ∈ P.carrier) (i : Fin P.rank) :
    -(P.coordinates 0 i : ℤ) ≤
        (h : ℤ) * ((P.coordinates a i : ℤ) - (P.coordinates 0 i : ℤ)) ∧
      (h : ℤ) * ((P.coordinates a i : ℤ) - (P.coordinates 0 i : ℤ)) ≤
        (P.length i : ℤ) - (P.coordinates 0 i : ℤ) := by
  have hlin := P.coordinates_nsmul_sub hP a hh hmem (le_refl h) i
  have hlo : (0 : ℤ) ≤ (P.coordinates (h • a) i : ℤ) := by positivity
  have hhi : (P.coordinates (h • a) i : ℤ) ≤ (P.length i : ℤ) := by
    exact_mod_cast Nat.le_of_lt_succ (P.coordinates (h • a) i).isLt
  constructor <;> omega

/-- A coordinate shorter than the progression length has zero increment. -/
theorem coordinates_eq_zero_coordinate_of_short_side
    (P : GeneralizedAP) (hP : P.TProper 2) (a : ℤ) {h : ℕ}
    (hh : 0 < h) (hmem : ∀ t ≤ h, t • a ∈ P.carrier)
    (i : Fin P.rank) (hshort : P.length i < h) :
    P.coordinates a i = P.coordinates 0 i := by
  obtain ⟨hlo, hhi⟩ := P.coordinates_nsmul_bounds hP a hh hmem i
  have hzlo : (0 : ℤ) ≤ (P.coordinates 0 i : ℤ) := by positivity
  have hzhi : (P.coordinates 0 i : ℤ) ≤ (P.length i : ℤ) := by
    exact_mod_cast Nat.le_of_lt_succ (P.coordinates 0 i).isLt
  have hshort' : (P.length i : ℤ) < (h : ℤ) := by exact_mod_cast hshort
  have heq : (P.coordinates a i : ℤ) = (P.coordinates 0 i : ℤ) := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hd : (P.coordinates a i : ℤ) - (P.coordinates 0 i : ℤ) ≤ -1 := by omega
      nlinarith
    · have hd : 1 ≤ (P.coordinates a i : ℤ) - (P.coordinates 0 i : ℤ) := by omega
      nlinarith
  apply Fin.ext
  exact_mod_cast heq

end Erdos587.GeneralizedAP
