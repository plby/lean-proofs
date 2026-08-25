import Util.Bernays.InvertibleIdeal
import Mathlib.Data.List.Perm.Basic

/-!
# Uniqueness of factorization into invertible maximal ideals
-/

namespace Bernays.InvertibleIdeal

variable {R : Type*} [CommRing R] [IsDomain R]

theorem maximal_mem_of_prod_le (P : InvertibleIdeal R) (hP : (P : Ideal R).IsMaximal)
    (l : List (InvertibleIdeal R)) (hl : ∀ Q ∈ l, (Q : Ideal R).IsMaximal)
    (hle : ((l.prod : InvertibleIdeal R) : Ideal R) ≤ (P : Ideal R)) : P ∈ l := by
  induction l with
  | nil =>
    exact False.elim (hP.ne_top (top_unique hle))
  | cons Q l ih =>
    change (Q : Ideal R) * ((l.prod : InvertibleIdeal R) : Ideal R) ≤ (P : Ideal R) at hle
    rcases hP.isPrime.mul_le.mp hle with hQ | htail
    · have heq : Q = P := ext ((hl Q List.mem_cons_self).eq_of_le hP.ne_top hQ)
      exact List.mem_cons.mpr (Or.inl heq.symm)
    · exact List.mem_cons_of_mem Q (ih (fun T hT => hl T (List.mem_cons_of_mem Q hT)) htail)

theorem maximal_factors_perm {l r : List (InvertibleIdeal R)} (hprod : l.prod = r.prod)
    (hl : ∀ P ∈ l, (P : Ideal R).IsMaximal)
    (hr : ∀ P ∈ r, (P : Ideal R).IsMaximal) : l.Perm r := by
  classical
  induction l generalizing r with
  | nil =>
    cases r with
    | nil => exact List.Perm.nil
    | cons Q r =>
      have hle : (⊤ : Ideal R) ≤ (Q : Ideal R) := by
        change ((([] : List (InvertibleIdeal R)).prod : InvertibleIdeal R) : Ideal R) ≤ (Q : Ideal R)
        rw [hprod]
        exact Ideal.mul_le_left
      exact False.elim ((hr Q List.mem_cons_self).ne_top (top_unique hle))
  | cons P l ih =>
    have hP := hl P List.mem_cons_self
    have hle : ((r.prod : InvertibleIdeal R) : Ideal R) ≤ (P : Ideal R) := by
      rw [← hprod]
      exact Ideal.mul_le_left
    have hmem := maximal_mem_of_prod_le P hP r hr hle
    have hperm : r.Perm (P :: r.erase P) := List.perm_cons_erase hmem
    have heq : l.prod = (r.erase P).prod := by
      have h := hprod.trans hperm.prod_eq
      simp only [List.prod_cons] at h
      exact mul_right_cancel _ _ P (by simpa only [mul_comm] using h)
    exact ((ih heq (fun Q hQ => hl Q (List.mem_cons_of_mem P hQ))
      (fun Q hQ => hr Q (List.mem_of_mem_erase hQ))).cons P).trans hperm.symm

end Bernays.InvertibleIdeal
