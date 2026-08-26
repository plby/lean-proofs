import ErdosProblems.Erdos4.RestrictedProductNorm
import ErdosProblems.Erdos4.DivisorSlices
import ErdosProblems.Erdos4.ConductorSupport

/-!
# Tensor forms and restricted residue averages

This is the exact algebraic link between principal local matrices and the
contractive restricted product form. Coefficient splitting is an exact
finite reindexing, including empty coordinate sets.
-/

open scoped BigOperators

namespace Erdos4.RestrictedTensor

open ProductOrthogonality RestrictedProductNorm DivisorSlices

variable {P : Type*} [Fintype P] [DecidableEq P] {k : ℕ}

noncomputable def localKernel (ell : ℝ) (mask : Option (Fin k) → ℝ)
    (a b : Option (Fin k)) : ℝ :=
  LocalOrthogonality.mean ell (fun s => mask s *
    (LocalOrthogonality.extendedBasis ell a s * LocalOrthogonality.extendedBasis ell b s))

theorem mean_mask_basis_mul (ell : P → ℝ) (mask : P → Option (Fin k) → ℝ)
    (a b : P → Option (Fin k)) :
    mean ell (fun s => (∏ p, mask p (s p)) * (basis ell a s * basis ell b s)) =
      ∏ p, localKernel (ell p) (mask p) (a p) (b p) := by
  have hfactor (s : P → Option (Fin k)) :
      stateWeight ell s * ((∏ p, mask p (s p)) * (basis ell a s * basis ell b s)) =
        ∏ p, LocalOrthogonality.stateWeight (ell p) k (s p) *
          (mask p (s p) * (LocalOrthogonality.extendedBasis (ell p) (a p) (s p) *
            LocalOrthogonality.extendedBasis (ell p) (b p) (s p))) := by
    simp only [stateWeight, basis, Finset.prod_mul_distrib]
  unfold mean
  simp_rw [hfactor]
  rw [← Fintype.prod_sum (fun p s => LocalOrthogonality.stateWeight (ell p) k s *
    (mask p s * (LocalOrthogonality.extendedBasis (ell p) (a p) s *
      LocalOrthogonality.extendedBasis (ell p) (b p) s)))]
  apply Finset.prod_congr rfl
  intro p _hp
  exact (LocalOrthogonality.mean_eq_sum (ell p) _).symm

theorem restrictedForm_productMask_eq (ell : P → ℝ) (mask : P → Option (Fin k) → ℝ)
    (v w : (P → Option (Fin k)) → ℝ) :
    restrictedForm ell (fun s => ∏ p, mask p (s p)) v w =
      ∑ a, ∑ b, (v a * w b) * ∏ p, localKernel (ell p) (mask p) (a p) (b p) := by
  have heq (s : P → Option (Fin k)) :
      (∏ p, mask p (s p)) * (expansion ell v s * expansion ell w s) =
        ∑ a, ∑ b, (v a * w b) *
          ((∏ p, mask p (s p)) * (basis ell a s * basis ell b s)) := by
    unfold expansion
    rw [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _ha
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _hb
    ring
  unfold restrictedForm
  simp_rw [heq]
  rw [mean_sum]
  simp_rw [mean_sum, mean_const_mul, mean_mask_basis_mul]

theorem sum_join_complex (J : Finset P) (f : (P → Option (Fin k)) → ℂ) :
    (∑ a : J → Option (Fin k), ∑ b : {p : P // p ∉ J} → Option (Fin k),
      f (join J a b)) = ∑ c, f c := by
  let e := Equiv.piEquivPiSubtypeProd (fun p : P => p ∈ J)
    (fun _ => Option (Fin k))
  have hh := e.symm.sum_comp f
  rw [Fintype.sum_prod_type] at hh
  exact hh

def mixedMatrix (J : Finset P)
    (M : J → Option (Fin k) → Option (Fin k) → ℂ)
    (N : {p : P // p ∉ J} → Option (Fin k) → Option (Fin k) → ℂ)
    (p : P) (a b : Option (Fin k)) : ℂ :=
  if hp : p ∈ J then M ⟨p, hp⟩ a b else N ⟨p, hp⟩ a b

theorem prod_mixedMatrix_join (J : Finset P)
    (M : J → Option (Fin k) → Option (Fin k) → ℂ)
    (N : {p : P // p ∉ J} → Option (Fin k) → Option (Fin k) → ℂ)
    (a b : J → Option (Fin k))
    (x y : {p : P // p ∉ J} → Option (Fin k)) :
    (∏ p, mixedMatrix J M N p (join J a x p) (join J b y p)) =
      (∏ p : J, M p (a p) (b p)) *
        ∏ p : {p : P // p ∉ J}, N p (x p) (y p) := by
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun p : P => p ∈ J)
    (fun p => mixedMatrix J M N p (join J a x p) (join J b y p))]
  apply congrArg₂ (fun a b : ℂ => a * b)
  · apply Finset.prod_congr (by ext p; simp)
    intro p _hp
    simp only [mixedMatrix, join, dif_pos p.property]
  · apply Finset.prod_congr rfl
    intro p _hp
    simp only [mixedMatrix, join, dif_neg p.property]

theorem tensorForm_mixed (J : Finset P) (v : (P → Option (Fin k)) → ℝ)
    (M : J → Option (Fin k) → Option (Fin k) → ℂ)
    (N : {p : P // p ∉ J} → Option (Fin k) → Option (Fin k) → ℂ) :
    ConductorSupport.tensorForm v (mixedMatrix J M N) =
      ∑ a : J → Option (Fin k), ∑ b : J → Option (Fin k),
        (∏ p : J, M p (a p) (b p)) *
          ∑ x : {p : P // p ∉ J} → Option (Fin k),
            ∑ y : {p : P // p ∉ J} → Option (Fin k),
              (v (join J a x) : ℂ) * (v (join J b y) : ℂ) *
                ∏ p : {p : P // p ∉ J}, N p (x p) (y p) := by
  have hinner (c : P → Option (Fin k)) :
      (∑ d, (v c : ℂ) * (v d : ℂ) * ∏ p, mixedMatrix J M N p (c p) (d p)) =
        ∑ b : J → Option (Fin k), ∑ y : {p : P // p ∉ J} → Option (Fin k),
          (v c : ℂ) * (v (join J b y) : ℂ) *
            ∏ p, mixedMatrix J M N p (c p) (join J b y p) :=
    (sum_join_complex J _).symm
  unfold ConductorSupport.tensorForm
  rw [← sum_join_complex J (fun c =>
    ∑ d, (v c : ℂ) * (v d : ℂ) * ∏ p, mixedMatrix J M N p (c p) (d p))]
  simp_rw [hinner]
  apply Finset.sum_congr rfl
  intro a _ha
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _hb
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _hx
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _hy
  rw [prod_mixedMatrix_join]
  ring

end Erdos4.RestrictedTensor
