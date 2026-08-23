/- leanprover/lean4:v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos240.BakerLemma4Concrete
import ErdosProblems.Erdos240.InterpolationProducts

/-!
# Local Hermite residues for concrete Baker Lemma 4

This module proves the exact algebraic partial-fraction and normalized
small-circle coefficient-extraction identities behind source equation (9).
Unlike a global inverse-Vandermonde estimate, these identities retain the
factorial cancellation at the consecutive integral nodes.
-/

open scoped BigOperators
open Complex Finset Function Metric Polynomial Set

noncomputable section

namespace Erdos240.BakerLemma4Concrete

open Erdos240.HermiteInterpolation
open Erdos240.InterpolationProducts

def localNodalPolynomial (R S : ℕ) : ℂ[X] :=
  ∏ i ∈ range R, (X - C ((i + 1 : ℕ) : ℂ)) ^ S

def localOtherPolynomial (R S r : ℕ) : ℂ[X] :=
  ∏ i ∈ (range R).erase (r - 1), (X - C ((i + 1 : ℕ) : ℂ)) ^ S

theorem localNodalPolynomial_eq_mul_other {R S r : ℕ}
    (hr : 1 ≤ r) (hrR : r ≤ R) :
    localNodalPolynomial R S =
      (X - C (r : ℂ)) ^ S * localOtherPolynomial R S r := by
  rw [localNodalPolynomial, localOtherPolynomial]
  have hmem : r - 1 ∈ range R := by simp; omega
  rw [← Finset.mul_prod_erase _ _ hmem]
  congr 1
  simp only [Nat.sub_add_cancel hr]

@[simp] theorem localNodalPolynomial_eval (R S : ℕ) (z : ℂ) :
    (localNodalPolynomial R S).eval z =
      ∏ i ∈ range R, (z - ((i + 1 : ℕ) : ℂ)) ^ S := by
  simp only [localNodalPolynomial, eval_prod, eval_pow, eval_sub, eval_X, eval_C]

@[simp] theorem localOtherPolynomial_eval (R S r : ℕ) (z : ℂ) :
    (localOtherPolynomial R S r).eval z =
      ∏ i ∈ (range R).erase (r - 1),
        (z - ((i + 1 : ℕ) : ℂ)) ^ S := by
  simp only [localOtherPolynomial, eval_prod, eval_pow, eval_sub, eval_X, eval_C]

theorem hasseDeriv_mul_X_sub_C_pow_eval
    (B : ℂ[X]) (r : ℂ) (m k : ℕ) :
    (hasseDeriv k ((X - C r) ^ m * B)).eval r =
      if m ≤ k then (hasseDeriv (k - m) B).eval r else 0 := by
  rw [← taylor_coeff]
  rw [taylor_mul, taylor_pow, map_sub, taylor_X, taylor_C]
  simp only [add_sub_cancel_right]
  rw [coeff_X_pow_mul']
  split_ifs with h
  · rw [taylor_coeff]
  · rfl

theorem hasseDeriv_mul_X_sub_C_pow_eval_self
    (B : ℂ[X]) (r : ℂ) (m : ℕ) :
    (hasseDeriv m ((X - C r) ^ m * B)).eval r = B.eval r := by
  simp [hasseDeriv_mul_X_sub_C_pow_eval]

theorem localOtherPolynomial_eval_ne_zero {R S r : ℕ}
    (hr : 1 ≤ r) (hrR : r ≤ R) :
    (localOtherPolynomial R S r).eval (r : ℂ) ≠ 0 := by
  rw [localOtherPolynomial_eval]
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  have hir : i ≠ r - 1 := (Finset.mem_erase.mp hi).1
  have hcast : (r : ℂ) ≠ ((i + 1 : ℕ) : ℂ) := by
    exact_mod_cast (show r ≠ i + 1 by omega)
  exact pow_ne_zero _ (sub_ne_zero.mpr hcast)

def localPrincipalPolynomial (R S : ℕ)
    (rm : IntegralJetIndex R S) : ℂ[X] :=
  (X - C ((rm.1.1 + 1 : ℕ) : ℂ)) ^ rm.2.1 *
    localOtherPolynomial R S (rm.1.1 + 1)

theorem localPrincipalPolynomial_hasse_same
    {R S : ℕ} (r : Fin R) (m k : Fin S) :
    (hasseDeriv k.1 (localPrincipalPolynomial R S ⟨r, m⟩)).eval
        ((r.1 + 1 : ℕ) : ℂ) =
      if m.1 ≤ k.1 then
        (hasseDeriv (k.1 - m.1)
          (localOtherPolynomial R S (r.1 + 1))).eval
            ((r.1 + 1 : ℕ) : ℂ)
      else 0 := by
  exact hasseDeriv_mul_X_sub_C_pow_eval _ _ _ _

theorem localPrincipalPolynomial_hasse_other
    {R S : ℕ} (r t : Fin R) (hrt : t ≠ r) (m k : Fin S) :
    (hasseDeriv k.1 (localPrincipalPolynomial R S ⟨t, m⟩)).eval
        ((r.1 + 1 : ℕ) : ℂ) = 0 := by
  rw [← taylor_coeff]
  apply (X_pow_dvd_iff.mp ?_ k.1 k.2)
  change X ^ S ∣ (localPrincipalPolynomial R S ⟨t, m⟩).comp
    (X + C ((r.1 + 1 : ℕ) : ℂ))
  rw [← X_sub_C_pow_dvd_iff]
  unfold localPrincipalPolynomial localOtherPolynomial
  have hmem : r.1 ∈ (range R).erase t.1 := by
    rw [Finset.mem_erase]
    exact ⟨by exact fun h ↦ hrt (Fin.ext h.symm), Finset.mem_range.mpr r.2⟩
  simp only [Nat.add_sub_cancel]
  apply dvd_mul_of_dvd_right
  rw [← Finset.mul_prod_erase _ _ hmem]
  exact dvd_mul_right _ _

theorem localPrincipalPolynomial_hasse_diagonal_ne_zero
    {R S : ℕ} (r : Fin R) (m : Fin S) :
    (hasseDeriv m.1 (localPrincipalPolynomial R S ⟨r, m⟩)).eval
        ((r.1 + 1 : ℕ) : ℂ) ≠ 0 := by
  rw [localPrincipalPolynomial_hasse_same, if_pos le_rfl, Nat.sub_self,
    hasseDeriv_zero, LinearMap.id_apply]
  exact localOtherPolynomial_eval_ne_zero (by omega) (by omega)

theorem localPrincipalPolynomial_linearIndependent (R S : ℕ) :
    LinearIndependent ℂ (localPrincipalPolynomial R S) := by
  rw [Fintype.linearIndependent_iff]
  intro c hsum
  intro rm
  rcases rm with ⟨r, m⟩
  have hzero (k : ℕ) (hkS : k < S) : c ⟨r, ⟨k, hkS⟩⟩ = 0 := by
    induction k using Nat.strong_induction_on with
    | h k ih =>
      let kk : Fin S := ⟨k, hkS⟩
      have hderiv := congrArg
        (fun Q : ℂ[X] ↦ (hasseDeriv k Q).eval ((r.1 + 1 : ℕ) : ℂ)) hsum
      simp only [map_sum, map_smul, eval_finsetSum, eval_smul, eval_zero,
        smul_eq_mul] at hderiv
      rw [Fintype.sum_sigma] at hderiv
      have hcollapseOther :
          (∑ t : Fin R, ∑ j : Fin S,
              c ⟨t, j⟩ *
                (hasseDeriv k (localPrincipalPolynomial R S ⟨t, j⟩)).eval
                  ((r.1 + 1 : ℕ) : ℂ)) =
            ∑ j : Fin S, c ⟨r, j⟩ *
              (hasseDeriv k (localPrincipalPolynomial R S ⟨r, j⟩)).eval
                ((r.1 + 1 : ℕ) : ℂ) := by
        apply Finset.sum_eq_single r
        · intro t _ htr
          apply Finset.sum_eq_zero
          intro j _
          rw [localPrincipalPolynomial_hasse_other r t htr j kk, mul_zero]
        · intro hrnot
          exact (hrnot (Finset.mem_univ r)).elim
      rw [hcollapseOther] at hderiv
      have hcollapseHigh :
          (∑ j : Fin S, c ⟨r, j⟩ *
              (hasseDeriv k (localPrincipalPolynomial R S ⟨r, j⟩)).eval
                ((r.1 + 1 : ℕ) : ℂ)) =
            c ⟨r, kk⟩ *
              (hasseDeriv k (localPrincipalPolynomial R S ⟨r, kk⟩)).eval
                ((r.1 + 1 : ℕ) : ℂ) := by
        apply Finset.sum_eq_single kk
        · intro j _ hj
          by_cases hjk : j.1 < k
          · have hcj : c ⟨r, j⟩ = 0 := ih j.1 hjk j.2
            rw [hcj, zero_mul]
          · have hkj : k < j.1 := by
              have hne : j.1 ≠ k := fun h ↦ hj (Fin.ext h)
              omega
            have hnotle : ¬ j.1 ≤ kk.1 := by
              change ¬ j.1 ≤ k
              omega
            rw [localPrincipalPolynomial_hasse_same r j kk,
              if_neg hnotle, mul_zero]
        · intro hnot
          exact (hnot (Finset.mem_univ kk)).elim
      rw [hcollapseHigh] at hderiv
      have hderiv0 : c ⟨r, kk⟩ *
          (hasseDeriv kk.1 (localPrincipalPolynomial R S ⟨r, kk⟩)).eval
            ((r.1 + 1 : ℕ) : ℂ) = 0 := by
        simpa [kk] using hderiv
      exact mul_eq_zero.mp hderiv0 |>.resolve_right
        (localPrincipalPolynomial_hasse_diagonal_ne_zero r kk)
  exact hzero m.1 m.2

theorem localOtherPolynomial_monic (R S r : ℕ) :
    (localOtherPolynomial R S r).Monic := by
  unfold localOtherPolynomial
  apply monic_prod_of_monic
  intro i hi
  exact (monic_X_sub_C _).pow _

theorem localOtherPolynomial_natDegree {R S r : ℕ}
    (hr : 1 ≤ r) (hrR : r ≤ R) :
    (localOtherPolynomial R S r).natDegree = (R - 1) * S := by
  unfold localOtherPolynomial
  rw [natDegree_prod_of_monic]
  · simp only [natDegree_pow, natDegree_X_sub_C, Finset.sum_const_nat]
    rw [Finset.card_erase_of_mem]
    · simp
    · simp
      omega
  · intro i hi
    exact (monic_X_sub_C _).pow _

theorem localPrincipalPolynomial_natDegree {R S : ℕ}
    (rm : IntegralJetIndex R S) :
    (localPrincipalPolynomial R S rm).natDegree = (R - 1) * S + rm.2.1 := by
  rw [localPrincipalPolynomial, natDegree_mul]
  · rw [natDegree_pow, natDegree_X_sub_C,
      localOtherPolynomial_natDegree (by omega) (by omega)]
    simp [add_comm]
  · exact (monic_X_sub_C _).pow rm.2.1 |>.ne_zero
  · exact (localOtherPolynomial_monic R S (rm.1.1 + 1)).ne_zero

theorem localPrincipalPolynomial_mem_degreeLT {R S : ℕ}
    (rm : IntegralJetIndex R S) :
    localPrincipalPolynomial R S rm ∈ Polynomial.degreeLT ℂ (R * S) := by
  rw [Polynomial.mem_degreeLT,
    degree_eq_natDegree (by
      exact ((monic_X_sub_C _).pow rm.2.1 |>.mul
        (localOtherPolynomial_monic R S (rm.1.1 + 1))).ne_zero),
    localPrincipalPolynomial_natDegree]
  exact_mod_cast (show (R - 1) * S + rm.2.1 < R * S by
    have hR : 1 ≤ R := by
      exact Nat.one_le_iff_ne_zero.mpr (fun hR0 ↦ by
        subst R
        exact Fin.elim0 rm.1)
    have hm : rm.2.1 < S := rm.2.2
    calc
      (R - 1) * S + rm.2.1 < (R - 1) * S + S := Nat.add_lt_add_left hm _
      _ = R * S := by
        rw [show (R - 1) * S + S = ((R - 1) + 1) * S by ring,
          Nat.sub_add_cancel hR])

def localPrincipalMap (R S : ℕ) :
    (IntegralJetIndex R S → ℂ) →ₗ[ℂ] Polynomial.degreeLT ℂ (R * S) where
  toFun c := ⟨∑ rm, c rm • localPrincipalPolynomial R S rm, by
    apply Submodule.sum_mem
    intro rm _
    exact Submodule.smul_mem _ _
      (localPrincipalPolynomial_mem_degreeLT rm)⟩
  map_add' c d := by
    apply Subtype.ext
    change (∑ rm, (c rm + d rm) • localPrincipalPolynomial R S rm) =
      (∑ rm, c rm • localPrincipalPolynomial R S rm) +
        ∑ rm, d rm • localPrincipalPolynomial R S rm
    simp only [add_smul, Finset.sum_add_distrib]
  map_smul' a c := by
    apply Subtype.ext
    change (∑ rm, (a * c rm) • localPrincipalPolynomial R S rm) =
      a • ∑ rm, c rm • localPrincipalPolynomial R S rm
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro rm _
    rw [mul_smul]

theorem localPrincipalMap_injective (R S : ℕ) :
    Function.Injective (localPrincipalMap R S) := by
  intro c d hcd
  have hLI := localPrincipalPolynomial_linearIndependent R S
  rw [Fintype.linearIndependent_iff] at hLI
  have hzero : ∀ i, (c - d) i = 0 := hLI (c - d) (by
    change ∑ rm, (c rm - d rm) • localPrincipalPolynomial R S rm = 0
    simp_rw [sub_smul]
    rw [Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr (Subtype.ext_iff.mp hcd))
  funext i
  exact sub_eq_zero.mp (hzero i)

def localPrincipalEquiv (R S : ℕ) :
    (IntegralJetIndex R S → ℂ) ≃ₗ[ℂ] Polynomial.degreeLT ℂ (R * S) :=
  LinearEquiv.ofInjectiveOfFinrankEq (localPrincipalMap R S)
    (localPrincipalMap_injective R S) (by
      calc
        Module.finrank ℂ (IntegralJetIndex R S → ℂ) = R * S := by
          simp [IntegralJetIndex]
        _ = Module.finrank ℂ (Polynomial.degreeLT ℂ (R * S)) := by
          symm
          simpa using (Polynomial.degreeLTEquiv ℂ (R * S)).finrank_eq)

theorem localNodalPolynomial_monic (R S : ℕ) :
    (localNodalPolynomial R S).Monic := by
  unfold localNodalPolynomial
  apply monic_prod_of_monic
  intro i hi
  exact (monic_X_sub_C _).pow _

theorem localNodalPolynomial_natDegree (R S : ℕ) :
    (localNodalPolynomial R S).natDegree = R * S := by
  unfold localNodalPolynomial
  rw [natDegree_prod_of_monic]
  · simp only [natDegree_pow, natDegree_X_sub_C, Finset.sum_const_nat,
      Finset.card_range, nsmul_eq_mul]
    ring
  · intro i hi
    exact (monic_X_sub_C _).pow _

theorem localPrincipalPolynomial_monic (R S : ℕ)
    (rm : IntegralJetIndex R S) :
    (localPrincipalPolynomial R S rm).Monic :=
  ((monic_X_sub_C _).pow rm.2.1).mul
    (localOtherPolynomial_monic R S (rm.1.1 + 1))

theorem localPrincipalPolynomial_coeff_top {R S : ℕ}
    (hS : 1 ≤ S) (rm : IntegralJetIndex R S) :
    (localPrincipalPolynomial R S rm).coeff (R * S - 1) =
      if rm.2.1 = S - 1 then 1 else 0 := by
  have hR : 1 ≤ R := Nat.one_le_iff_ne_zero.mpr (fun hR0 ↦ by
    subst R
    exact Fin.elim0 rm.1)
  have hRS : R * S = (R - 1) * S + S := by
    symm
    calc
      (R - 1) * S + S = ((R - 1) + 1) * S := by ring
      _ = R * S := by rw [Nat.sub_add_cancel hR]
  have hdeg := localPrincipalPolynomial_natDegree rm
  by_cases hm : rm.2.1 = S - 1
  · rw [if_pos hm, ← (localPrincipalPolynomial_monic R S rm).coeff_natDegree]
    congr 1
    rw [hdeg, hm]
    rw [hRS]
    omega
  · rw [if_neg hm]
    apply coeff_eq_zero_of_natDegree_lt
    rw [hdeg]
    have hmle : rm.2.1 < S - 1 := by
      have hmS := rm.2.2
      omega
    calc
      (R - 1) * S + rm.2.1 < (R - 1) * S + (S - 1) :=
        Nat.add_lt_add_left hmle _
      _ = R * S - 1 := by rw [hRS]; omega

/-- Polynomial partial-fraction numerator decomposition underlying the
local-circle form of Hermite interpolation. -/
theorem exists_localPrincipal_decomposition
    {R S l : ℕ} (hR : 1 ≤ R) (hS : 1 ≤ S) (hRl : R < l)
    (P : ℂ[X]) (hPdeg : P ∈ Polynomial.degreeLT ℂ (R * S)) :
    ∃ c : IntegralJetIndex R S → ℂ,
      C ((localNodalPolynomial R S).eval (l : ℂ)) * P =
        C (P.eval (l : ℂ)) * localNodalPolynomial R S +
          (X - C (l : ℂ)) *
            ∑ rm, c rm • localPrincipalPolynomial R S rm := by
  let N : ℂ[X] :=
    C ((localNodalPolynomial R S).eval (l : ℂ)) * P -
      C (P.eval (l : ℂ)) * localNodalPolynomial R S
  have hNeval : N.eval (l : ℂ) = 0 := by
    dsimp only [N]
    rw [eval_sub, eval_mul, eval_C, eval_mul, eval_C]
    ring
  have hdvd : X - C (l : ℂ) ∣ N := by
    rw [dvd_iff_isRoot, IsRoot.def]
    exact hNeval
  obtain ⟨H, hH⟩ := hdvd
  have hNdeg : N.natDegree ≤ R * S := by
    dsimp only [N]
    apply (natDegree_sub_le _ _).trans
    apply max_le
    · exact (natDegree_C_mul_le _ P).trans (Nat.le_of_lt (by
        by_cases hP0 : P = 0
        · subst P
          simpa using Nat.mul_pos hR hS
        · exact (natDegree_lt_iff_degree_lt hP0).mpr
            (Polynomial.mem_degreeLT.mp hPdeg)))
    · exact (natDegree_C_mul_le _ _).trans_eq
        (localNodalPolynomial_natDegree R S)
  have hHdeg : H ∈ Polynomial.degreeLT ℂ (R * S) := by
    rw [Polynomial.mem_degreeLT]
    by_cases hH0 : H = 0
    · subst H
      simp
      exact WithBot.bot_lt_coe _
    · have hlinear : X - C (l : ℂ) ≠ 0 := (monic_X_sub_C _).ne_zero
      have hNat : 1 + H.natDegree = N.natDegree := by
        rw [hH, natDegree_mul hlinear hH0, natDegree_X_sub_C]
      rw [degree_eq_natDegree hH0]
      exact_mod_cast (show H.natDegree < R * S by omega)
  let Hsub : Polynomial.degreeLT ℂ (R * S) := ⟨H, hHdeg⟩
  let c : IntegralJetIndex R S → ℂ := (localPrincipalEquiv R S).symm Hsub
  refine ⟨c, ?_⟩
  have hc : H = ∑ rm, c rm • localPrincipalPolynomial R S rm := by
    change Hsub.1 = ((localPrincipalMap R S) c).1
    rw [show localPrincipalMap R S = (localPrincipalEquiv R S).toLinearMap by rfl]
    simp [c]
  dsimp only [N] at hH
  rw [← hc]
  simpa [add_comm] using (sub_eq_iff_eq_add).mp hH

theorem eval_add_sum_last_eq_zero_of_localPrincipal_decomposition
    {R S l : ℕ} (hR : 1 ≤ R) (hS : 1 ≤ S)
    (P : ℂ[X]) (hPdeg : P ∈ Polynomial.degreeLT ℂ (R * S))
    (c : IntegralJetIndex R S → ℂ)
    (hdecomp :
      C ((localNodalPolynomial R S).eval (l : ℂ)) * P =
        C (P.eval (l : ℂ)) * localNodalPolynomial R S +
          (X - C (l : ℂ)) *
            ∑ rm, c rm • localPrincipalPolynomial R S rm) :
    P.eval (l : ℂ) +
        ∑ r : Fin R, c ⟨r, ⟨S - 1, by omega⟩⟩ = 0 := by
  have hcoeff := congrArg (fun Q : ℂ[X] ↦ Q.coeff (R * S)) hdecomp
  have hPcoeff : P.coeff (R * S) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    by_cases hP0 : P = 0
    · subst P
      simpa using Nat.mul_pos hR hS
    · exact (natDegree_lt_iff_degree_lt hP0).mpr
        (Polynomial.mem_degreeLT.mp hPdeg)
  have hFcoeff : (localNodalPolynomial R S).coeff (R * S) = 1 := by
    rw [← (localNodalPolynomial_monic R S).coeff_natDegree,
      localNodalPolynomial_natDegree]
  have hQdeg : (∑ rm, c rm • localPrincipalPolynomial R S rm).natDegree <
      R * S := by
    let Qsub : Polynomial.degreeLT ℂ (R * S) := (localPrincipalMap R S) c
    by_cases hQ0 : Qsub.1 = 0
    · have hsum0 : ∑ rm, c rm • localPrincipalPolynomial R S rm = 0 := hQ0
      rw [hsum0, natDegree_zero]
      exact Nat.mul_pos (by omega) (by omega)
    · exact (natDegree_lt_iff_degree_lt hQ0).mpr
        (Polynomial.mem_degreeLT.mp Qsub.2)
  have hQtop : (∑ rm, c rm • localPrincipalPolynomial R S rm).coeff
      (R * S - 1) = ∑ r : Fin R, c ⟨r, ⟨S - 1, by omega⟩⟩ := by
    rw [Fintype.sum_sigma]
    change (Polynomial.lcoeff ℂ (R * S - 1))
        (∑ r : Fin R, ∑ m : Fin S,
          c ⟨r, m⟩ • localPrincipalPolynomial R S ⟨r, m⟩) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro r _
    rw [map_sum]
    simp only [Polynomial.lcoeff_apply, coeff_smul,
      localPrincipalPolynomial_coeff_top hS, smul_eq_mul, mul_ite, mul_one,
      mul_zero, Finset.sum_ite_irrel, Finset.sum_const_zero]
    let last : Fin S := ⟨S - 1, by omega⟩
    calc
      (∑ x : Fin S, if x.1 = S - 1 then c ⟨r, x⟩ else 0) =
          (if last.1 = S - 1 then c ⟨r, last⟩ else 0) := by
        apply Finset.sum_eq_single last
        · intro m _ hm
          rw [if_neg]
          intro hval
          exact hm (Fin.ext hval)
        · intro hnot
          exact (hnot (Finset.mem_univ _)).elim
      _ = c ⟨r, ⟨S - 1, by omega⟩⟩ := by simp [last]
  have hQabove : (∑ rm, c rm • localPrincipalPolynomial R S rm).coeff
      (R * S) = 0 := coeff_eq_zero_of_natDegree_lt hQdeg
  have hRSpos : 0 < R * S := Nat.mul_pos (by omega) (by omega)
  have hmulcoeff : ((X - C (l : ℂ)) *
      ∑ rm, c rm • localPrincipalPolynomial R S rm).coeff (R * S) =
        (∑ rm, c rm • localPrincipalPolynomial R S rm).coeff (R * S - 1) := by
    rw [sub_mul, coeff_sub, show R * S = (R * S - 1) + 1 by omega,
      coeff_X_mul, coeff_C_mul,
      show R * S - 1 + 1 = R * S by omega, hQabove]
    ring
  simp only [coeff_C_mul, coeff_add, hPcoeff, hFcoeff, hmulcoeff, hQtop] at hcoeff
  simpa using hcoeff.symm

theorem exists_localPrincipal_decomposition_with_last_sum
    {R S l : ℕ} (hR : 1 ≤ R) (hS : 1 ≤ S) (hRl : R < l)
    (P : ℂ[X]) (hPdeg : P ∈ Polynomial.degreeLT ℂ (R * S)) :
    ∃ c : IntegralJetIndex R S → ℂ,
      C ((localNodalPolynomial R S).eval (l : ℂ)) * P =
          C (P.eval (l : ℂ)) * localNodalPolynomial R S +
            (X - C (l : ℂ)) *
              ∑ rm, c rm • localPrincipalPolynomial R S rm ∧
        P.eval (l : ℂ) +
          ∑ r : Fin R, c ⟨r, ⟨S - 1, by omega⟩⟩ = 0 := by
  obtain ⟨c, hc⟩ := exists_localPrincipal_decomposition hR hS hRl P hPdeg
  exact ⟨c, hc,
    eval_add_sum_last_eq_zero_of_localPrincipal_decomposition hR hS P hPdeg c hc⟩

def localPolynomialKernel (R S : ℕ) (l : ℂ) (P : ℂ[X]) (z : ℂ) : ℂ :=
  (((localNodalPolynomial R S).eval l /
      (localNodalPolynomial R S).eval z) * P.eval z) / (z - l)

theorem eval_localPrincipalPolynomial (R S : ℕ)
    (rm : IntegralJetIndex R S) (z : ℂ) :
    (localPrincipalPolynomial R S rm).eval z =
      (z - ((rm.1.1 + 1 : ℕ) : ℂ)) ^ rm.2.1 *
        (localOtherPolynomial R S (rm.1.1 + 1)).eval z := by
  simp [localPrincipalPolynomial]

theorem eval_localPrincipal_div_localNodal
    {R S : ℕ} (rm : IntegralJetIndex R S) {z : ℂ}
    (hz : ∀ i : Fin R, z ≠ ((i.1 + 1 : ℕ) : ℂ)) :
    (localPrincipalPolynomial R S rm).eval z /
        (localNodalPolynomial R S).eval z =
      1 / (z - ((rm.1.1 + 1 : ℕ) : ℂ)) ^ (S - rm.2.1) := by
  let a : ℂ := z - ((rm.1.1 + 1 : ℕ) : ℂ)
  let B : ℂ := (localOtherPolynomial R S (rm.1.1 + 1)).eval z
  have ha : a ≠ 0 := sub_ne_zero.mpr (hz rm.1)
  have hF := congrArg (fun Q : ℂ[X] ↦ Q.eval z)
    (localNodalPolynomial_eq_mul_other
      (R := R) (S := S) (r := rm.1.1 + 1) (by omega) (by omega))
  have hFeq : (localNodalPolynomial R S).eval z = a ^ S * B := by
    simpa [a, B] using hF
  have hFne : (localNodalPolynomial R S).eval z ≠ 0 := by
    rw [localNodalPolynomial_eval]
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    have hiz : z ≠ ((i + 1 : ℕ) : ℂ) := hz ⟨i, Finset.mem_range.mp hi⟩
    exact pow_ne_zero _ (sub_ne_zero.mpr hiz)
  have hB : B ≠ 0 := by
    intro hB0
    rw [hFeq, hB0, mul_zero] at hFne
    exact hFne rfl
  rw [eval_localPrincipalPolynomial, hFeq]
  change a ^ rm.2.1 * B / (a ^ S * B) = 1 / a ^ (S - rm.2.1)
  have hsplit : S = rm.2.1 + (S - rm.2.1) := by omega
  have hpow : a ^ S = a ^ rm.2.1 * a ^ (S - rm.2.1) := by
    calc
      a ^ S = a ^ (rm.2.1 + (S - rm.2.1)) := by congr 1
      _ = a ^ rm.2.1 * a ^ (S - rm.2.1) := pow_add _ _ _
  rw [hpow]
  field_simp

theorem localPolynomialKernel_eq_partialFractions
    {R S : ℕ} (hR : 1 ≤ R) (hS : 1 ≤ S)
    {l z : ℂ} (P : ℂ[X]) (c : IntegralJetIndex R S → ℂ)
    (hdecomp :
      C ((localNodalPolynomial R S).eval l) * P =
        C (P.eval l) * localNodalPolynomial R S +
          (X - C l) * ∑ rm, c rm • localPrincipalPolynomial R S rm)
    (hzl : z ≠ l)
    (hznodes : ∀ i : Fin R, z ≠ ((i.1 + 1 : ℕ) : ℂ)) :
    localPolynomialKernel R S l P z =
      P.eval l / (z - l) +
        ∑ rm, c rm /
          (z - ((rm.1.1 + 1 : ℕ) : ℂ)) ^ (S - rm.2.1) := by
  have hFz : (localNodalPolynomial R S).eval z ≠ 0 := by
    rw [localNodalPolynomial_eval]
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    exact pow_ne_zero _ (sub_ne_zero.mpr (hznodes ⟨i, Finset.mem_range.mp hi⟩))
  have heval := congrArg (fun Q : ℂ[X] ↦ Q.eval z) hdecomp
  simp only [eval_mul, eval_C, eval_add, eval_sub, eval_X, eval_finsetSum,
    eval_smul, smul_eq_mul] at heval
  have hsum :
      (∑ rm, c rm /
          (z - ((rm.1.1 + 1 : ℕ) : ℂ)) ^ (S - rm.2.1)) =
        (∑ rm, c rm * (localPrincipalPolynomial R S rm).eval z) /
          (localNodalPolynomial R S).eval z := by
    calc
      (∑ rm, c rm /
          (z - ((rm.1.1 + 1 : ℕ) : ℂ)) ^ (S - rm.2.1)) =
          ∑ rm, c rm *
            ((localPrincipalPolynomial R S rm).eval z /
              (localNodalPolynomial R S).eval z) := by
            apply Finset.sum_congr rfl
            intro rm _
            rw [eval_localPrincipal_div_localNodal rm hznodes]
            ring
      _ = (∑ rm, c rm * (localPrincipalPolynomial R S rm).eval z) /
            (localNodalPolynomial R S).eval z := by
            rw [Finset.sum_div]
            apply Finset.sum_congr rfl
            intro rm _
            ring
  rw [hsum]
  unfold localPolynomialKernel
  field_simp [hFz, sub_ne_zero.mpr hzl]
  linear_combination heval

theorem circleIntegral_sub_inv_eq_zero_of_not_mem_closedBall
    {c w : ℂ} {ρ : ℝ} (hρ : 0 ≤ ρ) (hw : w ∉ Metric.closedBall c ρ) :
    (∮ z in C(c, ρ), (z - w)⁻¹) = 0 := by
  have hd : DifferentiableOn ℂ (fun z : ℂ => (z - w)⁻¹) ({w}ᶜ : Set ℂ) := by
    intro z hz
    exact (differentiableAt_inv (sub_ne_zero.mpr hz)).comp z
      (differentiableAt_id.sub_const w) |>.differentiableWithinAt
  have hclosed : Metric.closedBall c ρ ⊆ ({w}ᶜ : Set ℂ) := by
    intro z hz hzw
    apply hw
    simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using hzw ▸ hz
  exact (hd.diffContOnCl_ball hclosed).circleIntegral_eq_zero hρ

theorem circleIntegral_one_div_sub_pow_eq_zero_of_ne_one
    {c w : ℂ} {ρ : ℝ} {k : ℕ} (hρ : 0 ≤ ρ) (hk : k ≠ 1) :
    (∮ z in C(c, ρ), 1 / (z - w) ^ k) = 0 := by
  have hneg : -(k : ℤ) ≠ -1 := by omega
  rw [circleIntegral.integral_congr hρ (fun z _ ↦ by
    rw [one_div, ← zpow_natCast, ← zpow_neg])]
  exact circleIntegral.integral_sub_zpow_of_ne hneg c w ρ

theorem circleIntegral_one_div_sub_pow_center
    {c : ℂ} {ρ : ℝ} (hρ : ρ ≠ 0) :
    (∮ z in C(c, ρ), 1 / (z - c) ^ (1 : ℕ)) =
      2 * ((Real.pi : ℝ) : ℂ) * I := by
  simpa [one_div] using circleIntegral.integral_sub_center_inv c hρ

theorem natCast_not_mem_closedBall_half_of_lt {a b : ℕ} (hab : a < b) :
    (b : ℂ) ∉ Metric.closedBall (a : ℂ) (1 / 2 : ℝ) := by
  rw [Metric.mem_closedBall, dist_eq]
  have hsub : (b : ℂ) - (a : ℂ) = ((b - a : ℕ) : ℂ) := by
    simpa using (Nat.cast_sub hab.le : ((b - a : ℕ) : ℂ) = (b : ℂ) - (a : ℂ)).symm
  rw [hsub, Complex.norm_natCast]
  have hba : (1 : ℝ) ≤ (b - a : ℕ) := by exact_mod_cast (show 1 ≤ b - a by omega)
  exact not_le_of_gt ((by norm_num : (1 / 2 : ℝ) < 1).trans_le hba)

theorem natCast_not_mem_closedBall_half_of_ne {a b : ℕ} (hab : a ≠ b) :
    (b : ℂ) ∉ Metric.closedBall (a : ℂ) (1 / 2 : ℝ) := by
  rcases lt_or_gt_of_ne hab with hab | hba
  · exact natCast_not_mem_closedBall_half_of_lt hab
  · rw [Metric.mem_closedBall, dist_comm]
    exact natCast_not_mem_closedBall_half_of_lt hba

theorem natCast_not_mem_sphere_half (a b : ℕ) :
    (b : ℂ) ∉ Metric.sphere (a : ℂ) (1 / 2 : ℝ) := by
  by_cases hab : a = b
  · subst b
    simp [Metric.mem_sphere]
  · exact fun hb ↦ natCast_not_mem_closedBall_half_of_ne hab
      (Metric.sphere_subset_closedBall hb)

theorem circleIntegrable_one_div_sub_natCast_pow_half
    (a b k : ℕ) :
    CircleIntegrable (fun z : ℂ => 1 / (z - (b : ℂ)) ^ k)
      (a : ℂ) (1 / 2 : ℝ) := by
  apply ContinuousOn.circleIntegrable (by norm_num)
  exact continuousOn_const.div
    ((continuousOn_id.sub continuousOn_const).pow k) (fun z hz hzero ↦ by
      have hzb : z = (b : ℂ) := sub_eq_zero.mp (eq_zero_of_pow_eq_zero hzero)
      exact natCast_not_mem_sphere_half a b (hzb ▸ hz))

theorem normalized_circleIntegral_one_div_node_pow_eq_one
    {R S : ℕ} (hS : 1 ≤ S) (r : Fin R) :
    (2 * ((Real.pi : ℝ) : ℂ) * I)⁻¹ *
      (∮ z in C(((r.1 + 1 : ℕ) : ℂ), (1 / 2 : ℝ)),
        1 / (z - ((r.1 + 1 : ℕ) : ℂ)) ^ (S - (S - 1))) = 1 := by
  have hpow : S - (S - 1) = 1 := by omega
  rw [hpow, circleIntegral_one_div_sub_pow_center (by norm_num)]
  exact inv_mul_cancel₀ (mul_ne_zero
    (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero)

theorem normalized_circleIntegral_one_div_node_pow_eq_zero
    {R S : ℕ} (hS : 1 ≤ S) (r t : Fin R) (m : Fin S)
    (hoff : r ≠ t ∨ m.1 ≠ S - 1) :
    (2 * ((Real.pi : ℝ) : ℂ) * I)⁻¹ *
      (∮ z in C(((r.1 + 1 : ℕ) : ℂ), (1 / 2 : ℝ)),
        1 / (z - ((t.1 + 1 : ℕ) : ℂ)) ^ (S - m.1)) = 0 := by
  by_cases hk : S - m.1 = 1
  · have hm : m.1 = S - 1 := by omega
    have hrt : r ≠ t := by
      intro hrt
      exact hoff.elim (fun h ↦ h hrt) (fun h ↦ h hm)
    have hnat : r.1 + 1 ≠ t.1 + 1 := by omega
    have hout : ((t.1 + 1 : ℕ) : ℂ) ∉
        Metric.closedBall (((r.1 + 1 : ℕ) : ℂ)) (1 / 2 : ℝ) :=
      natCast_not_mem_closedBall_half_of_ne hnat
    rw [hk]
    have hzero := circleIntegral_sub_inv_eq_zero_of_not_mem_closedBall
      (c := ((r.1 + 1 : ℕ) : ℂ)) (w := ((t.1 + 1 : ℕ) : ℂ))
      (ρ := (1 / 2 : ℝ)) (by norm_num) hout
    simpa [one_div] using congrArg
      (fun x : ℂ => (2 * ((Real.pi : ℝ) : ℂ) * I)⁻¹ * x) hzero
  · rw [circleIntegral_one_div_sub_pow_eq_zero_of_ne_one (by norm_num) hk, mul_zero]

/-- A pole strictly inside a circle does not meet its boundary, so every
negative integral power of the corresponding local parameter is circle
integrable. -/
theorem circleIntegrable_one_div_sub_pow_of_mem_ball
    {c w : ℂ} {rho : ℝ} {k : ℕ} (hw : w ∈ Metric.ball c rho) :
    CircleIntegrable (fun z : ℂ => 1 / (z - w) ^ k) c rho := by
  have hrho : 0 ≤ rho := (dist_nonneg.trans_lt hw).le
  apply ContinuousOn.circleIntegrable hrho
  exact continuousOn_const.div
    ((continuousOn_id.sub continuousOn_const).pow k) (fun z hz hzero => by
      have hzw : z = w := sub_eq_zero.mp (eq_zero_of_pow_eq_zero hzero)
      exact Metric.sphere_disjoint_ball.ne_of_mem hz hw hzw)

/-- Normalized integral of a pole strictly inside an outer circle.  Only
the simple-pole term survives. -/
theorem normalized_circleIntegral_one_div_sub_pow_of_mem_ball
    {c w : ℂ} {rho : ℝ} {k : ℕ} (hw : w ∈ Metric.ball c rho) :
    (2 * ((Real.pi : ℝ) : ℂ) * I)⁻¹ *
        (∮ z in C(c, rho), 1 / (z - w) ^ k) =
      if k = 1 then 1 else 0 := by
  split_ifs with hk
  · subst k
    rw [show (fun z : ℂ => 1 / (z - w) ^ (1 : ℕ)) =
        fun z => (z - w)⁻¹ by funext z; simp]
    rw [circleIntegral.integral_sub_inv_of_mem_ball hw]
    exact inv_mul_cancel₀ (mul_ne_zero
      (mul_ne_zero (by norm_num)
        (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero)
  · rw [circleIntegral_one_div_sub_pow_eq_zero_of_ne_one
      (dist_nonneg.trans_lt hw).le hk, mul_zero]

theorem normalized_circleIntegral_localPolynomialKernel_eq_topCoefficient
    {R S l : ℕ} (hR : 1 ≤ R) (hS : 1 ≤ S) (hRl : R < l)
    (P : ℂ[X]) (c : IntegralJetIndex R S → ℂ)
    (hdecomp :
      C ((localNodalPolynomial R S).eval (l : ℂ)) * P =
        C (P.eval (l : ℂ)) * localNodalPolynomial R S +
          (X - C (l : ℂ)) * ∑ rm, c rm • localPrincipalPolynomial R S rm)
    (r : Fin R) :
    (2 * ((Real.pi : ℝ) : ℂ) * I)⁻¹ *
        (∮ z in C(((r.1 + 1 : ℕ) : ℂ), (1 / 2 : ℝ)),
          localPolynomialKernel R S (l : ℂ) P z) =
      c ⟨r, ⟨S - 1, by omega⟩⟩ := by
  let top : IntegralJetIndex R S := ⟨r, ⟨S - 1, by omega⟩⟩
  have htargetOutside : (l : ℂ) ∉
      Metric.closedBall (((r.1 + 1 : ℕ) : ℂ)) (1 / 2 : ℝ) := by
    apply natCast_not_mem_closedBall_half_of_lt
    omega
  have hcircle : ∀ z ∈ Metric.sphere (((r.1 + 1 : ℕ) : ℂ)) (1 / 2 : ℝ),
      localPolynomialKernel R S (l : ℂ) P z =
        P.eval (l : ℂ) / (z - (l : ℂ)) +
          ∑ rm, c rm /
            (z - ((rm.1.1 + 1 : ℕ) : ℂ)) ^ (S - rm.2.1) := by
    intro z hz
    apply localPolynomialKernel_eq_partialFractions hR hS P c hdecomp
    · intro hzl
      exact natCast_not_mem_sphere_half (r.1 + 1) l (hzl ▸ hz)
    · intro i hzi
      exact natCast_not_mem_sphere_half (r.1 + 1) (i.1 + 1) (hzi ▸ hz)
  have htarget : CircleIntegrable
      (fun z : ℂ => P.eval (l : ℂ) / (z - (l : ℂ)))
      (((r.1 + 1 : ℕ) : ℂ)) (1 / 2 : ℝ) := by
    apply ContinuousOn.circleIntegrable (by norm_num)
    exact continuousOn_const.div (continuousOn_id.sub continuousOn_const)
      (fun z hz hzero ↦
        natCast_not_mem_sphere_half (r.1 + 1) l (sub_eq_zero.mp hzero ▸ hz))
  have hterm (rm : IntegralJetIndex R S) : CircleIntegrable
      (fun z : ℂ => c rm /
        (z - ((rm.1.1 + 1 : ℕ) : ℂ)) ^ (S - rm.2.1))
      (((r.1 + 1 : ℕ) : ℂ)) (1 / 2 : ℝ) := by
    apply ContinuousOn.circleIntegrable (by norm_num)
    exact continuousOn_const.div
      ((continuousOn_id.sub continuousOn_const).pow (S - rm.2.1))
      (fun z hz hzero ↦
        natCast_not_mem_sphere_half (r.1 + 1) (rm.1.1 + 1)
          (sub_eq_zero.mp (eq_zero_of_pow_eq_zero hzero) ▸ hz))
  have hterms : CircleIntegrable
      (fun z : ℂ => ∑ rm, c rm /
        (z - ((rm.1.1 + 1 : ℕ) : ℂ)) ^ (S - rm.2.1))
      (((r.1 + 1 : ℕ) : ℂ)) (1 / 2 : ℝ) :=
    by
      have hfun : (fun z : ℂ => ∑ rm, c rm /
          (z - ((rm.1.1 + 1 : ℕ) : ℂ)) ^ (S - rm.2.1)) =
          ∑ rm, fun z : ℂ => c rm /
            (z - ((rm.1.1 + 1 : ℕ) : ℂ)) ^ (S - rm.2.1) := by
        funext z
        simp
      rw [hfun]
      exact CircleIntegrable.sum Finset.univ (fun rm _ ↦ hterm rm)
  rw [circleIntegral.integral_congr (by norm_num) hcircle,
    circleIntegral.integral_add htarget hterms, mul_add]
  have htargetZero :
      (∮ z in C(((r.1 + 1 : ℕ) : ℂ), (1 / 2 : ℝ)),
        P.eval (l : ℂ) / (z - (l : ℂ))) = 0 := by
    rw [show (fun z : ℂ => P.eval (l : ℂ) / (z - (l : ℂ))) =
        fun z => P.eval (l : ℂ) * (z - (l : ℂ))⁻¹ by
      funext z; rw [div_eq_mul_inv]]
    rw [circleIntegral.integral_const_mul,
      circleIntegral_sub_inv_eq_zero_of_not_mem_closedBall (by norm_num) htargetOutside,
      mul_zero]
  rw [htargetZero, mul_zero, zero_add,
    circleIntegral.integral_fun_sum (fun rm _ ↦ hterm rm), mul_sum]
  refine (Fintype.sum_eq_single top (fun rm hrm ↦ ?_)).trans ?_
  ·
    have hoff : r ≠ rm.1 ∨ rm.2.1 ≠ S - 1 := by
      contrapose! hrm
      refine Sigma.ext_iff.mpr ⟨hrm.1.symm, ?_⟩
      exact heq_of_eq (Fin.ext hrm.2)
    have hzero := normalized_circleIntegral_one_div_node_pow_eq_zero
      hS r rm.1 rm.2 hoff
    rw [show (∮ z in C(((r.1 + 1 : ℕ) : ℂ), (1 / 2 : ℝ)),
          c rm / (z - ((rm.1.1 + 1 : ℕ) : ℂ)) ^ (S - rm.2.1)) =
        c rm * (∮ z in C(((r.1 + 1 : ℕ) : ℂ), (1 / 2 : ℝ)),
          1 / (z - ((rm.1.1 + 1 : ℕ) : ℂ)) ^ (S - rm.2.1)) by
      simpa [div_eq_mul_inv] using circleIntegral.integral_const_mul (c rm)
        (fun z : ℂ => 1 / (z - ((rm.1.1 + 1 : ℕ) : ℂ)) ^ (S - rm.2.1))
        (((r.1 + 1 : ℕ) : ℂ)) (1 / 2 : ℝ)]
    calc
      (2 * ((Real.pi : ℝ) : ℂ) * I)⁻¹ *
          (c rm * (∮ z in C(((r.1 + 1 : ℕ) : ℂ), (1 / 2 : ℝ)),
            1 / (z - ((rm.1.1 + 1 : ℕ) : ℂ)) ^ (S - rm.2.1))) =
        c rm * ((2 * ((Real.pi : ℝ) : ℂ) * I)⁻¹ *
          (∮ z in C(((r.1 + 1 : ℕ) : ℂ), (1 / 2 : ℝ)),
            1 / (z - ((rm.1.1 + 1 : ℕ) : ℂ)) ^ (S - rm.2.1))) := by ring
      _ = 0 := by rw [hzero, mul_zero]
  · simp only [top]
    rw [show (∮ z in C(((r.1 + 1 : ℕ) : ℂ), (1 / 2 : ℝ)),
          c ⟨r, ⟨S - 1, by omega⟩⟩ /
            (z - ((r.1 + 1 : ℕ) : ℂ)) ^ (S - (S - 1))) =
        c ⟨r, ⟨S - 1, by omega⟩⟩ *
          (∮ z in C(((r.1 + 1 : ℕ) : ℂ), (1 / 2 : ℝ)),
            1 / (z - ((r.1 + 1 : ℕ) : ℂ)) ^ (S - (S - 1))) by
      simpa [div_eq_mul_inv] using circleIntegral.integral_const_mul
        (c ⟨r, ⟨S - 1, by omega⟩⟩)
        (fun z : ℂ => 1 / (z - ((r.1 + 1 : ℕ) : ℂ)) ^ (S - (S - 1)))
        (((r.1 + 1 : ℕ) : ℂ)) (1 / 2 : ℝ)]
    calc
      (2 * ((Real.pi : ℝ) : ℂ) * I)⁻¹ *
          (c ⟨r, ⟨S - 1, by omega⟩⟩ *
            (∮ z in C(((r.1 + 1 : ℕ) : ℂ), (1 / 2 : ℝ)),
              1 / (z - ((r.1 + 1 : ℕ) : ℂ)) ^ (S - (S - 1)))) =
        c ⟨r, ⟨S - 1, by omega⟩⟩ *
          ((2 * ((Real.pi : ℝ) : ℂ) * I)⁻¹ *
            (∮ z in C(((r.1 + 1 : ℕ) : ℂ), (1 / 2 : ℝ)),
              1 / (z - ((r.1 + 1 : ℕ) : ℂ)) ^ (S - (S - 1)))) := by ring
      _ = c ⟨r, ⟨S - 1, by omega⟩⟩ := by
        rw [normalized_circleIntegral_one_div_node_pow_eq_one hS r, mul_one]

/-- The outer integral of the polynomial kernel is exactly zero.  This is
the residue cancellation which is lost if the Hermite polynomial is bounded
separately on the outer circle: the residue at the target is `P(l)`, while
the sum of the simple-pole residues at the interpolation nodes is `-P(l)`.
All higher-pole terms integrate to zero. -/
theorem normalized_outerCircleIntegral_localPolynomialKernel_eq_zero
    {R S l : ℕ} (hR : 1 ≤ R) (hS : 1 ≤ S) (hRl : R < l)
    (P : ℂ[X]) (hPdeg : P ∈ Polynomial.degreeLT ℂ (R * S))
    {c : ℂ} {rho : ℝ}
    (hlball : (l : ℂ) ∈ Metric.ball c rho)
    (hnodes : ∀ r : Fin R,
      (((r.1 + 1 : ℕ) : ℂ)) ∈ Metric.ball c rho) :
    (2 * ((Real.pi : ℝ) : ℂ) * I)⁻¹ *
        (∮ z in C(c, rho), localPolynomialKernel R S (l : ℂ) P z) = 0 := by
  obtain ⟨a, hdecomp, hlast⟩ :=
    exists_localPrincipal_decomposition_with_last_sum hR hS hRl P hPdeg
  have hrho : 0 ≤ rho := (dist_nonneg.trans_lt hlball).le
  have hcircle : ∀ z ∈ Metric.sphere c rho,
      localPolynomialKernel R S (l : ℂ) P z =
        P.eval (l : ℂ) / (z - (l : ℂ)) +
          ∑ rm, a rm /
            (z - ((rm.1.1 + 1 : ℕ) : ℂ)) ^ (S - rm.2.1) := by
    intro z hz
    apply localPolynomialKernel_eq_partialFractions hR hS P a hdecomp
    · exact Metric.sphere_disjoint_ball.ne_of_mem hz hlball
    · intro i
      exact Metric.sphere_disjoint_ball.ne_of_mem hz (hnodes i)
  have htarget : CircleIntegrable
      (fun z : ℂ => P.eval (l : ℂ) / (z - (l : ℂ))) c rho := by
    apply ContinuousOn.circleIntegrable hrho
    exact continuousOn_const.div (continuousOn_id.sub continuousOn_const)
      (fun z hz hzero =>
        Metric.sphere_disjoint_ball.ne_of_mem hz hlball
          (sub_eq_zero.mp hzero))
  have hterm (rm : IntegralJetIndex R S) : CircleIntegrable
      (fun z : ℂ => a rm /
        (z - ((rm.1.1 + 1 : ℕ) : ℂ)) ^ (S - rm.2.1)) c rho := by
    apply ContinuousOn.circleIntegrable hrho
    exact continuousOn_const.div
      ((continuousOn_id.sub continuousOn_const).pow (S - rm.2.1))
      (fun z hz hzero =>
        Metric.sphere_disjoint_ball.ne_of_mem hz (hnodes rm.1)
          (sub_eq_zero.mp (eq_zero_of_pow_eq_zero hzero)))
  have hterms : CircleIntegrable
      (fun z : ℂ => ∑ rm, a rm /
        (z - ((rm.1.1 + 1 : ℕ) : ℂ)) ^ (S - rm.2.1)) c rho := by
    have hfun : (fun z : ℂ => ∑ rm, a rm /
        (z - ((rm.1.1 + 1 : ℕ) : ℂ)) ^ (S - rm.2.1)) =
        ∑ rm, fun z : ℂ => a rm /
          (z - ((rm.1.1 + 1 : ℕ) : ℂ)) ^ (S - rm.2.1) := by
      funext z
      simp
    rw [hfun]
    exact CircleIntegrable.sum Finset.univ (fun rm _ => hterm rm)
  rw [circleIntegral.integral_congr hrho hcircle,
    circleIntegral.integral_add htarget hterms,
    mul_add, circleIntegral.integral_fun_sum (fun rm _ => hterm rm), mul_sum]
  have htargetIntegral :
      (2 * ((Real.pi : ℝ) : ℂ) * I)⁻¹ *
          (∮ z in C(c, rho), P.eval (l : ℂ) / (z - (l : ℂ))) =
        P.eval (l : ℂ) := by
    rw [show (∮ z in C(c, rho), P.eval (l : ℂ) / (z - (l : ℂ))) =
        P.eval (l : ℂ) *
          (∮ z in C(c, rho), 1 / (z - (l : ℂ)) ^ (1 : ℕ)) by
      simpa [div_eq_mul_inv] using circleIntegral.integral_const_mul
        (P.eval (l : ℂ))
        (fun z : ℂ => 1 / (z - (l : ℂ)) ^ (1 : ℕ)) c rho]
    rw [show (2 * ((Real.pi : ℝ) : ℂ) * I)⁻¹ *
          (P.eval (l : ℂ) *
            (∮ z in C(c, rho), 1 / (z - (l : ℂ)) ^ (1 : ℕ))) =
        P.eval (l : ℂ) *
          ((2 * ((Real.pi : ℝ) : ℂ) * I)⁻¹ *
            (∮ z in C(c, rho), 1 / (z - (l : ℂ)) ^ (1 : ℕ))) by ring]
    rw [normalized_circleIntegral_one_div_sub_pow_of_mem_ball hlball, if_pos rfl,
      mul_one]
  rw [htargetIntegral]
  have hnodeIntegral (rm : IntegralJetIndex R S) :
      (2 * ((Real.pi : ℝ) : ℂ) * I)⁻¹ *
          (∮ z in C(c, rho), a rm /
            (z - ((rm.1.1 + 1 : ℕ) : ℂ)) ^ (S - rm.2.1)) =
        if rm.2.1 = S - 1 then a rm else 0 := by
    rw [show (∮ z in C(c, rho), a rm /
          (z - ((rm.1.1 + 1 : ℕ) : ℂ)) ^ (S - rm.2.1)) =
        a rm * (∮ z in C(c, rho),
          1 / (z - ((rm.1.1 + 1 : ℕ) : ℂ)) ^ (S - rm.2.1)) by
      simpa [div_eq_mul_inv] using circleIntegral.integral_const_mul (a rm)
        (fun z : ℂ => 1 /
          (z - ((rm.1.1 + 1 : ℕ) : ℂ)) ^ (S - rm.2.1)) c rho]
    rw [show (2 * ((Real.pi : ℝ) : ℂ) * I)⁻¹ *
          (a rm * (∮ z in C(c, rho),
            1 / (z - ((rm.1.1 + 1 : ℕ) : ℂ)) ^ (S - rm.2.1))) =
        a rm * ((2 * ((Real.pi : ℝ) : ℂ) * I)⁻¹ *
          (∮ z in C(c, rho),
            1 / (z - ((rm.1.1 + 1 : ℕ) : ℂ)) ^ (S - rm.2.1))) by ring]
    rw [normalized_circleIntegral_one_div_sub_pow_of_mem_ball (hnodes rm.1)]
    by_cases hm : rm.2.1 = S - 1
    · rw [if_pos hm, hm]
      have hpow : S - (S - 1) = 1 := by omega
      rw [hpow, if_pos rfl, mul_one]
    · rw [if_neg hm]
      have hpow : S - rm.2.1 ≠ 1 := by omega
      rw [if_neg hpow, mul_zero]
  rw [show (∑ rm, (2 * ((Real.pi : ℝ) : ℂ) * I)⁻¹ *
        (∮ z in C(c, rho), a rm /
          (z - ((rm.1.1 + 1 : ℕ) : ℂ)) ^ (S - rm.2.1))) =
      ∑ rm, if rm.2.1 = S - 1 then a rm else 0 by
    apply Finset.sum_congr rfl
    intro rm _
    exact hnodeIntegral rm]
  rw [Fintype.sum_sigma]
  have hcollapse :
      (∑ r : Fin R, ∑ m : Fin S,
          if m.1 = S - 1 then a ⟨r, m⟩ else 0) =
        ∑ r : Fin R, a ⟨r, ⟨S - 1, by omega⟩⟩ := by
    apply Finset.sum_congr rfl
    intro r _
    let last : Fin S := ⟨S - 1, by omega⟩
    calc
      (∑ m : Fin S, if m.1 = S - 1 then a ⟨r, m⟩ else 0) =
          (if last.1 = S - 1 then a ⟨r, last⟩ else 0) := by
        apply Fintype.sum_eq_single last
        intro m hm
        rw [if_neg]
        intro heq
        exact hm (Fin.ext heq)
      _ = a ⟨r, ⟨S - 1, by omega⟩⟩ := by simp [last]
  rw [hcollapse]
  exact hlast

/-- The same nodal product as `integralNodes`, written in polynomial form. -/
theorem localNodalPolynomial_eval_eq_nodeProduct (R S : ℕ) (z : ℂ) :
    (localNodalPolynomial R S).eval z =
      HermiteInterpolation.nodeProduct (integralNodes R S) z := by
  rw [hermite_nodeProduct_integralNodes]
  simp [integralNodalProduct, localNodalPolynomial_eval]

/-- The outer kernel with an arbitrary entire numerator. -/
def localEntireKernel (R S : ℕ) (l : ℂ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (((localNodalPolynomial R S).eval l /
      (localNodalPolynomial R S).eval z) * f z) / (z - l)

@[simp] theorem localEntireKernel_polynomial (R S : ℕ) (l : ℂ)
    (P : ℂ[X]) :
    localEntireKernel R S l (fun z => P.eval z) =
      localPolynomialKernel R S l P := rfl

theorem circleIntegrable_localEntireKernel_of_nodes_mem_ball
    {R S : ℕ} {l c : ℂ} {rho : ℝ} {f : ℂ → ℂ}
    (hlball : l ∈ Metric.ball c rho)
    (hnodes : ∀ r : Fin R,
      (((r.1 + 1 : ℕ) : ℂ)) ∈ Metric.ball c rho)
    (hf : ContinuousOn f (Metric.sphere c rho)) :
    CircleIntegrable (localEntireKernel R S l f) c rho := by
  have hrho : 0 ≤ rho := (dist_nonneg.trans_lt hlball).le
  apply ContinuousOn.circleIntegrable hrho
  unfold localEntireKernel
  apply ContinuousOn.div
  · apply ContinuousOn.mul
    · apply ContinuousOn.div continuousOn_const
        (Polynomial.differentiable (localNodalPolynomial R S)).continuous.continuousOn
      intro z hz hzero
      rw [localNodalPolynomial_eval] at hzero
      rcases Finset.prod_eq_zero_iff.mp hzero with ⟨i, hi, hpow⟩
      have hzi : z = ((i + 1 : ℕ) : ℂ) :=
        sub_eq_zero.mp (eq_zero_of_pow_eq_zero hpow)
      exact Metric.sphere_disjoint_ball.ne_of_mem hz
        (hnodes ⟨i, Finset.mem_range.mp hi⟩) hzi
    · exact hf
  · exact continuousOn_id.sub continuousOn_const
  · intro z hz hzero
    exact Metric.sphere_disjoint_ball.ne_of_mem hz hlball
      (sub_eq_zero.mp hzero)

/-- Exact Hermite remainder in the source's outer-kernel notation.  The
right side is a normalized outer integral of `f` minus its Hermite
polynomial; no norm estimate has yet been taken. -/
theorem normalized_outerCircleIntegral_entireKernel_sub_polynomial
    {R S l : ℕ} (hS : 1 ≤ S) (f : ℂ → ℂ)
    (hf : Differentiable ℂ f) {c : ℂ} {rho : ℝ}
    (hlball : (l : ℂ) ∈ Metric.ball c rho)
    (hnodes : ∀ r : Fin R,
      (((r.1 + 1 : ℕ) : ℂ)) ∈ Metric.ball c rho) :
    (2 * ((Real.pi : ℝ) : ℂ) * I)⁻¹ *
        (∮ z in C(c, rho),
          localEntireKernel R S (l : ℂ) f z -
            localPolynomialKernel R S (l : ℂ)
              (HermiteInterpolation.polynomial f (integralNodes R S)) z) =
      f (l : ℂ) -
        (HermiteInterpolation.polynomial f (integralNodes R S)).eval (l : ℂ) := by
  let P : ℂ[X] := HermiteInterpolation.polynomial f (integralNodes R S)
  have hrho : 0 < rho := dist_nonneg.trans_lt hlball
  have hnodesList : ∀ a ∈ integralNodes R S, a ∈ Metric.ball c rho := by
    intro a ha
    rcases mem_integralNodes_iff_data.mp ha with ⟨i, hi, _hS, rfl⟩
    exact hnodes ⟨i, hi⟩
  have hrem := HermiteInterpolation.remainder_eq_nodeProduct_mul_circleIntegral
    hf (integralNodes R S) hrho hlball hnodesList
  have hFcircle : ∀ z ∈ Metric.sphere c rho,
      (localNodalPolynomial R S).eval z ≠ 0 := by
    intro z hz
    rw [localNodalPolynomial_eval]
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    apply pow_ne_zero
    rw [sub_ne_zero]
    exact Metric.sphere_disjoint_ball.ne_of_mem hz
      (hnodes ⟨i, Finset.mem_range.mp hi⟩)
  have htargetCircle : ∀ z ∈ Metric.sphere c rho, z - (l : ℂ) ≠ 0 := by
    intro z hz
    exact sub_ne_zero.mpr
      (Metric.sphere_disjoint_ball.ne_of_mem hz hlball)
  have hpoint : ∀ z ∈ Metric.sphere c rho,
      localEntireKernel R S (l : ℂ) f z -
          localPolynomialKernel R S (l : ℂ) P z =
        (localNodalPolynomial R S).eval (l : ℂ) *
          ((z - (l : ℂ))⁻¹ *
            (((localNodalPolynomial R S).eval z)⁻¹ *
              (f z - P.eval z))) := by
    intro z hz
    unfold localEntireKernel localPolynomialKernel
    field_simp [hFcircle z hz, htargetCircle z hz]
  have hintegral :
      (∮ z in C(c, rho),
        localEntireKernel R S (l : ℂ) f z -
          localPolynomialKernel R S (l : ℂ) P z) =
        (localNodalPolynomial R S).eval (l : ℂ) *
          (∮ z in C(c, rho),
            (z - (l : ℂ))⁻¹ *
              (((localNodalPolynomial R S).eval z)⁻¹ *
                (f z - P.eval z))) := by
    rw [circleIntegral.integral_congr hrho.le hpoint]
    exact circleIntegral.integral_const_mul
      ((localNodalPolynomial R S).eval (l : ℂ))
      (fun z : ℂ => (z - (l : ℂ))⁻¹ *
        (((localNodalPolynomial R S).eval z)⁻¹ *
          (f z - P.eval z))) c rho
  rw [hintegral]
  simp_rw [← localNodalPolynomial_eval_eq_nodeProduct R S] at hrem
  calc
    (2 * ((Real.pi : ℝ) : ℂ) * I)⁻¹ *
        ((localNodalPolynomial R S).eval (l : ℂ) *
          (∮ z in C(c, rho),
            (z - (l : ℂ))⁻¹ *
              (((localNodalPolynomial R S).eval z)⁻¹ *
                (f z - P.eval z)))) =
      (localNodalPolynomial R S).eval (l : ℂ) *
        ((2 * ((Real.pi : ℝ) : ℂ) * I)⁻¹ *
          (∮ z in C(c, rho),
            (z - (l : ℂ))⁻¹ *
              (((localNodalPolynomial R S).eval z)⁻¹ *
                (f z - P.eval z)))) := by ring
    _ = f (l : ℂ) -
        (HermiteInterpolation.polynomial f (integralNodes R S)).eval (l : ℂ) := by
      simpa only [P] using hrem.symm

/-! ### Replacing the polynomial by its local Hasse--Taylor jet -/

/-- The Taylor polynomial of order `S - 1` at `r`, written directly in
the Hasse-normalized basis used by the source. -/
def localHasseTaylorPolynomial (S : ℕ) (r : ℂ) (P : ℂ[X]) : ℂ[X] :=
  ∑ m : Fin S,
    C ((hasseDeriv m.1 P).eval r) * (X - C r) ^ m.1

theorem localHasseTaylorPolynomial_hasse
    {S : ℕ} (r : ℂ) (P : ℂ[X]) (k : Fin S) :
    (hasseDeriv k.1 (localHasseTaylorPolynomial S r P)).eval r =
      (hasseDeriv k.1 P).eval r := by
  rw [localHasseTaylorPolynomial, map_sum, eval_finsetSum]
  refine (Fintype.sum_eq_single k (fun m hmk ↦ ?_)).trans ?_
  ·
    rw [mul_comm, hasseDeriv_mul_X_sub_C_pow_eval]
    by_cases hle : m.1 ≤ k.1
    · rw [if_pos hle, hasseDeriv_C _ _ (by omega), eval_zero]
    · rw [if_neg hle]
  · rw [mul_comm, hasseDeriv_mul_X_sub_C_pow_eval, if_pos le_rfl,
      Nat.sub_self, hasseDeriv_zero, LinearMap.id_apply, eval_C]

/-- Removing the first `S` Hasse coefficients leaves a polynomial divisible
by the `S`th power of the local parameter. -/
theorem localHasseTaylorPolynomial_remainder_dvd
    (S : ℕ) (r : ℂ) (P : ℂ[X]) :
    (X - C r) ^ S ∣ P - localHasseTaylorPolynomial S r P := by
  rw [X_sub_C_pow_dvd_iff, X_pow_dvd_iff]
  intro k hk
  rw [← taylor_apply, taylor_coeff, map_sub, eval_sub]
  exact sub_eq_zero.mpr
    (localHasseTaylorPolynomial_hasse r P ⟨k, hk⟩).symm

theorem localOtherPolynomial_eval_ne_zero_on_closedBall_half
    {R S r : ℕ} (hr : 1 ≤ r) (hrR : r ≤ R)
    {z : ℂ} (hz : z ∈ Metric.closedBall (r : ℂ) (1 / 2 : ℝ)) :
    (localOtherPolynomial R S r).eval z ≠ 0 := by
  rw [localOtherPolynomial_eval]
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  apply pow_ne_zero
  rw [sub_ne_zero]
  intro hzi
  have hir : r ≠ i + 1 := by
    have hiErase := (Finset.mem_erase.mp hi).1
    omega
  exact natCast_not_mem_closedBall_half_of_ne hir (hzi ▸ hz)

theorem circleIntegrable_localPolynomialKernel
    {R S l : ℕ} (hRl : R < l) (P : ℂ[X]) (r : Fin R) :
    CircleIntegrable (localPolynomialKernel R S (l : ℂ) P)
      (((r.1 + 1 : ℕ) : ℂ)) (1 / 2 : ℝ) := by
  apply ContinuousOn.circleIntegrable (by norm_num)
  unfold localPolynomialKernel
  apply ContinuousOn.div
  · apply ContinuousOn.mul
    · apply ContinuousOn.div continuousOn_const
        (Polynomial.differentiable (localNodalPolynomial R S)).continuous.continuousOn
      intro z hz hzero
      rw [localNodalPolynomial_eval] at hzero
      have hprod := Finset.prod_eq_zero_iff.mp hzero
      rcases hprod with ⟨i, hi, hpow⟩
      have hzi : z = ((i + 1 : ℕ) : ℂ) :=
        sub_eq_zero.mp (eq_zero_of_pow_eq_zero hpow)
      exact natCast_not_mem_sphere_half (r.1 + 1) (i + 1) (hzi ▸ hz)
    · exact (Polynomial.differentiable P).continuous.continuousOn
  · exact continuousOn_id.sub continuousOn_const
  · intro z hz hzero
    exact natCast_not_mem_sphere_half (r.1 + 1) l (sub_eq_zero.mp hzero ▸ hz)

theorem circleIntegral_localPolynomialKernel_sub_taylor_eq_zero
    {R S l : ℕ} (hR : 1 ≤ R) (hS : 1 ≤ S) (hRl : R < l)
    (P : ℂ[X]) (r : Fin R) :
    (∮ z in C(((r.1 + 1 : ℕ) : ℂ), (1 / 2 : ℝ)),
      localPolynomialKernel R S (l : ℂ) P z -
        localPolynomialKernel R S (l : ℂ)
          (localHasseTaylorPolynomial S ((r.1 + 1 : ℕ) : ℂ) P) z) = 0 := by
  obtain ⟨Q, hQ⟩ := localHasseTaylorPolynomial_remainder_dvd
    S (((r.1 + 1 : ℕ) : ℂ)) P
  have hpoint : ∀ z ∈ Metric.sphere (((r.1 + 1 : ℕ) : ℂ)) (1 / 2 : ℝ),
      localPolynomialKernel R S (l : ℂ) P z -
          localPolynomialKernel R S (l : ℂ)
            (localHasseTaylorPolynomial S ((r.1 + 1 : ℕ) : ℂ) P) z =
        (localNodalPolynomial R S).eval (l : ℂ) * Q.eval z /
          ((localOtherPolynomial R S (r.1 + 1)).eval z * (z - (l : ℂ))) := by
    intro z hz
    have hzrClosed : z ∈ Metric.closedBall
        (((r.1 + 1 : ℕ) : ℂ)) (1 / 2 : ℝ) :=
      Metric.sphere_subset_closedBall hz
    have hBne := localOtherPolynomial_eval_ne_zero_on_closedBall_half
      (S := S) (show 1 ≤ r.1 + 1 by omega)
      (show r.1 + 1 ≤ R by omega) hzrClosed
    have hzr : z - ((r.1 + 1 : ℕ) : ℂ) ≠ 0 := by
      intro hzero
      have hzcenter := sub_eq_zero.mp hzero
      simpa [hzcenter, Metric.mem_sphere] using hz
    have hzl : z - (l : ℂ) ≠ 0 := by
      exact sub_ne_zero.mpr fun h ↦
        natCast_not_mem_sphere_half (r.1 + 1) l (h.symm ▸ hz)
    have hF := congrArg (fun T : ℂ[X] ↦ T.eval z)
      (localNodalPolynomial_eq_mul_other
        (R := R) (S := S) (r := r.1 + 1) (by omega) (by omega))
    have hFeq : (localNodalPolynomial R S).eval z =
        (z - ((r.1 + 1 : ℕ) : ℂ)) ^ S *
          (localOtherPolynomial R S (r.1 + 1)).eval z := by
      simpa using hF
    have hQeval := congrArg (fun T : ℂ[X] ↦ T.eval z) hQ
    simp only [eval_sub, eval_mul, eval_pow, eval_X, eval_C] at hQeval
    unfold localPolynomialKernel
    calc
      (localNodalPolynomial R S).eval (l : ℂ) /
              (localNodalPolynomial R S).eval z * P.eval z / (z - (l : ℂ)) -
          (localNodalPolynomial R S).eval (l : ℂ) /
              (localNodalPolynomial R S).eval z *
                (localHasseTaylorPolynomial S
                  ((r.1 + 1 : ℕ) : ℂ) P).eval z / (z - (l : ℂ)) =
        (localNodalPolynomial R S).eval (l : ℂ) /
              (localNodalPolynomial R S).eval z *
          (P.eval z - (localHasseTaylorPolynomial S
            ((r.1 + 1 : ℕ) : ℂ) P).eval z) / (z - (l : ℂ)) := by ring
      _ = (localNodalPolynomial R S).eval (l : ℂ) * Q.eval z /
          ((localOtherPolynomial R S (r.1 + 1)).eval z * (z - (l : ℂ))) := by
        rw [hQeval, hFeq]
        field_simp [hBne, hzr, hzl]
  rw [circleIntegral.integral_congr (by norm_num) hpoint]
  let U : Set ℂ := {z | (localOtherPolynomial R S (r.1 + 1)).eval z *
    (z - (l : ℂ)) ≠ 0}
  have hd : DifferentiableOn ℂ
      (fun z : ℂ => (localNodalPolynomial R S).eval (l : ℂ) * Q.eval z /
        ((localOtherPolynomial R S (r.1 + 1)).eval z * (z - (l : ℂ)))) U := by
    intro z hz
    exact (((differentiableAt_const
      ((localNodalPolynomial R S).eval (l : ℂ))).mul
        (Polynomial.differentiable Q z)).div
          ((Polynomial.differentiable
            (localOtherPolynomial R S (r.1 + 1)) z).mul
              (differentiableAt_id.sub_const (l : ℂ))) hz).differentiableWithinAt
  have hclosed : Metric.closedBall (((r.1 + 1 : ℕ) : ℂ)) (1 / 2 : ℝ) ⊆ U := by
    intro z hz
    apply mul_ne_zero
    · exact localOtherPolynomial_eval_ne_zero_on_closedBall_half
        (S := S) (show 1 ≤ r.1 + 1 by omega)
        (show r.1 + 1 ≤ R by omega) hz
    · exact sub_ne_zero.mpr fun h ↦
        natCast_not_mem_closedBall_half_of_lt
          (show r.1 + 1 < l by omega) (h.symm ▸ hz)
  exact (hd.diffContOnCl_ball hclosed).circleIntegral_eq_zero (by norm_num)

theorem circleIntegral_localPolynomialKernel_eq_taylor
    {R S l : ℕ} (hR : 1 ≤ R) (hS : 1 ≤ S) (hRl : R < l)
    (P : ℂ[X]) (r : Fin R) :
    (∮ z in C(((r.1 + 1 : ℕ) : ℂ), (1 / 2 : ℝ)),
      localPolynomialKernel R S (l : ℂ) P z) =
    ∮ z in C(((r.1 + 1 : ℕ) : ℂ), (1 / 2 : ℝ)),
      localPolynomialKernel R S (l : ℂ)
        (localHasseTaylorPolynomial S ((r.1 + 1 : ℕ) : ℂ) P) z := by
  rw [← sub_eq_zero,
    ← circleIntegral.integral_sub
      (circleIntegrable_localPolynomialKernel hRl P r)
      (circleIntegrable_localPolynomialKernel hRl
        (localHasseTaylorPolynomial S ((r.1 + 1 : ℕ) : ℂ) P) r)]
  exact circleIntegral_localPolynomialKernel_sub_taylor_eq_zero hR hS hRl P r

theorem localCircleKernel_eq_localPolynomialKernel
    (R S r l m : ℕ) (z : ℂ) :
    localCircleKernel R S r l m z =
      localPolynomialKernel R S (l : ℂ) ((X - C (r : ℂ)) ^ m) z := by
  simp only [localCircleKernel, localPolynomialKernel,
    localNodalPolynomial_eval, eval_pow, eval_sub, eval_X, eval_C]

theorem localPolynomialKernel_taylor_eq_sum_localCircleKernel
    {R S l : ℕ} (P : ℂ[X]) (r : Fin R) (z : ℂ) :
    localPolynomialKernel R S (l : ℂ)
        (localHasseTaylorPolynomial S ((r.1 + 1 : ℕ) : ℂ) P) z =
      ∑ m : Fin S, (hasseDeriv m.1 P).eval ((r.1 + 1 : ℕ) : ℂ) *
        localCircleKernel R S (r.1 + 1) l m.1 z := by
  unfold localPolynomialKernel localHasseTaylorPolynomial
  simp only [eval_finsetSum, eval_mul, eval_C]
  rw [Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro m _
  rw [localCircleKernel_eq_localPolynomialKernel]
  unfold localPolynomialKernel
  simp only [eval_pow, eval_sub, eval_X, eval_C]
  ring

theorem circleIntegrable_localCircleKernel
    {R S r l m : ℕ} (hr : 1 ≤ r) (hrR : r ≤ R) (hRl : R < l) :
    CircleIntegrable (localCircleKernel R S r l m)
      (r : ℂ) (1 / 2 : ℝ) := by
  let rr : Fin R := ⟨r - 1, by omega⟩
  have hrr : rr.1 + 1 = r := by dsimp [rr]; omega
  rw [show localCircleKernel R S r l m =
      localPolynomialKernel R S (l : ℂ) ((X - C (r : ℂ)) ^ m) by
    funext z
    exact localCircleKernel_eq_localPolynomialKernel R S r l m z]
  simpa only [hrr] using
    circleIntegrable_localPolynomialKernel hRl ((X - C (r : ℂ)) ^ m) rr

theorem circleIntegral_localPolynomialKernel_eq_sum_localCircleKernel
    {R S l : ℕ} (hR : 1 ≤ R) (hS : 1 ≤ S) (hRl : R < l)
    (P : ℂ[X]) (r : Fin R) :
    (∮ z in C(((r.1 + 1 : ℕ) : ℂ), (1 / 2 : ℝ)),
      localPolynomialKernel R S (l : ℂ) P z) =
      ∑ m : Fin S, (hasseDeriv m.1 P).eval ((r.1 + 1 : ℕ) : ℂ) *
        (∮ z in C(((r.1 + 1 : ℕ) : ℂ), (1 / 2 : ℝ)),
          localCircleKernel R S (r.1 + 1) l m.1 z) := by
  rw [circleIntegral_localPolynomialKernel_eq_taylor hR hS hRl P r]
  rw [circleIntegral.integral_congr (by norm_num)
    (fun z _ ↦ localPolynomialKernel_taylor_eq_sum_localCircleKernel P r z)]
  rw [circleIntegral.integral_fun_sum]
  · apply Finset.sum_congr rfl
    intro m _
    exact circleIntegral.integral_const_mul
      ((hasseDeriv m.1 P).eval ((r.1 + 1 : ℕ) : ℂ))
      (localCircleKernel R S (r.1 + 1) l m.1)
      (((r.1 + 1 : ℕ) : ℂ)) (1 / 2 : ℝ)
  · intro m _
    have hkernel := circleIntegrable_localCircleKernel
      (S := S) (m := m.1) (show 1 ≤ r.1 + 1 by omega)
      (show r.1 + 1 ≤ R by omega) hRl
    exact hkernel.const_smul

/-- Exact local-circle representation of a polynomial of degree below the
confluent grid size.  This is the polynomial form of source equation (9):
the value at the new integer is a sum of normalized old-node Hasse jets,
and no global inverse-Vandermonde norm occurs. -/
theorem polynomial_eval_eq_neg_sum_normalized_localCircleKernel
    {R S l : ℕ} (hR : 1 ≤ R) (hS : 1 ≤ S) (hRl : R < l)
    (P : ℂ[X]) (hPdeg : P ∈ Polynomial.degreeLT ℂ (R * S)) :
    P.eval (l : ℂ) =
      -∑ r : Fin R, ∑ m : Fin S,
        (hasseDeriv m.1 P).eval ((r.1 + 1 : ℕ) : ℂ) *
          ((2 * ((Real.pi : ℝ) : ℂ) * I)⁻¹ *
            ∮ z in C(((r.1 + 1 : ℕ) : ℂ), (1 / 2 : ℝ)),
              localCircleKernel R S (r.1 + 1) l m.1 z) := by
  obtain ⟨c, hdecomp, hlast⟩ :=
    exists_localPrincipal_decomposition_with_last_sum hR hS hRl P hPdeg
  have hc (r : Fin R) : c ⟨r, ⟨S - 1, by omega⟩⟩ =
      ∑ m : Fin S, (hasseDeriv m.1 P).eval ((r.1 + 1 : ℕ) : ℂ) *
        ((2 * ((Real.pi : ℝ) : ℂ) * I)⁻¹ *
          ∮ z in C(((r.1 + 1 : ℕ) : ℂ), (1 / 2 : ℝ)),
            localCircleKernel R S (r.1 + 1) l m.1 z) := by
    rw [← normalized_circleIntegral_localPolynomialKernel_eq_topCoefficient
      hR hS hRl P c hdecomp r]
    rw [circleIntegral_localPolynomialKernel_eq_sum_localCircleKernel
      hR hS hRl P r, mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    ring
  rw [show (∑ r : Fin R, c ⟨r, ⟨S - 1, by omega⟩⟩) =
      ∑ r : Fin R, ∑ m : Fin S,
        (hasseDeriv m.1 P).eval ((r.1 + 1 : ℕ) : ℂ) *
          ((2 * ((Real.pi : ℝ) : ℂ) * I)⁻¹ *
            ∮ z in C(((r.1 + 1 : ℕ) : ℂ), (1 / 2 : ℝ)),
              localCircleKernel R S (r.1 + 1) l m.1 z) by
    apply Finset.sum_congr rfl
    intro r _
    exact hc r] at hlast
  linear_combination hlast

/-- Literal source equation (9).  The outer Hermite polynomial cancels
exactly, leaving the outer integral of the entire function and the sum of
the normalized old-node analytic jets over the half-unit local circles. -/
theorem entire_eval_eq_outer_sub_sum_normalized_localCircleKernel
    {R S l : ℕ} (hR : 1 ≤ R) (hS : 1 ≤ S) (hRl : R < l)
    (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    {c : ℂ} {rho : ℝ}
    (hlball : (l : ℂ) ∈ Metric.ball c rho)
    (hnodes : ∀ r : Fin R,
      (((r.1 + 1 : ℕ) : ℂ)) ∈ Metric.ball c rho) :
    f (l : ℂ) =
      (2 * ((Real.pi : ℝ) : ℂ) * I)⁻¹ *
        (∮ z in C(c, rho), localEntireKernel R S (l : ℂ) f z) -
      ∑ r : Fin R, ∑ m : Fin S,
        (iteratedDeriv m.1 f ((r.1 + 1 : ℕ) : ℂ) /
            (m.1.factorial : ℂ)) *
          ((2 * ((Real.pi : ℝ) : ℂ) * I)⁻¹ *
            ∮ z in C(((r.1 + 1 : ℕ) : ℂ), (1 / 2 : ℝ)),
              localCircleKernel R S (r.1 + 1) l m.1 z) := by
  let P : ℂ[X] := HermiteInterpolation.polynomial f (integralNodes R S)
  have hPdeg : P ∈ Polynomial.degreeLT ℂ (R * S) := by
    exact polynomial_integralNodes_mem_degreeLT f R S
  have houterSub := normalized_outerCircleIntegral_entireKernel_sub_polynomial
    hS f hf hlball hnodes
  have houterP := normalized_outerCircleIntegral_localPolynomialKernel_eq_zero
    hR hS hRl P hPdeg hlball hnodes
  have hfint : CircleIntegrable (localEntireKernel R S (l : ℂ) f) c rho :=
    circleIntegrable_localEntireKernel_of_nodes_mem_ball hlball hnodes
      hf.continuous.continuousOn
  have hPint : CircleIntegrable
      (localPolynomialKernel R S (l : ℂ) P) c rho := by
    rw [← localEntireKernel_polynomial]
    exact circleIntegrable_localEntireKernel_of_nodes_mem_ball hlball hnodes
      (Polynomial.differentiable P).continuous.continuousOn
  have houter :
      (2 * ((Real.pi : ℝ) : ℂ) * I)⁻¹ *
          (∮ z in C(c, rho), localEntireKernel R S (l : ℂ) f z) =
        f (l : ℂ) - P.eval (l : ℂ) := by
    calc
      (2 * ((Real.pi : ℝ) : ℂ) * I)⁻¹ *
          (∮ z in C(c, rho), localEntireKernel R S (l : ℂ) f z) =
        (2 * ((Real.pi : ℝ) : ℂ) * I)⁻¹ *
            (∮ z in C(c, rho),
              localEntireKernel R S (l : ℂ) f z -
                localPolynomialKernel R S (l : ℂ) P z) +
          (2 * ((Real.pi : ℝ) : ℂ) * I)⁻¹ *
            (∮ z in C(c, rho),
              localPolynomialKernel R S (l : ℂ) P z) := by
          rw [circleIntegral.integral_sub hfint hPint]
          ring
      _ = f (l : ℂ) - P.eval (l : ℂ) := by
        rw [houterSub, houterP, add_zero]
  have hjet (r : Fin R) (m : Fin S) :
      (hasseDeriv m.1 P).eval ((r.1 + 1 : ℕ) : ℂ) =
        iteratedDeriv m.1 f ((r.1 + 1 : ℕ) : ℂ) /
          (m.1.factorial : ℂ) := by
    rw [hasseDeriv_eval_eq_iteratedDeriv_div_factorial]
    obtain ⟨after, hsplit⟩ :=
      integralNodes_eq_append_replicate_append (S := S) r
    change iteratedDeriv m.1
      (fun z => (HermiteInterpolation.polynomial f (integralNodes R S)).eval z)
        ((r.1 + 1 : ℕ) : ℂ) / (m.1.factorial : ℂ) = _
    rw [hsplit]
    rw [iteratedDeriv_eval_polynomial_eq_of_replicate_block hf
      (integralNodes r.1 S) after ((r.1 + 1 : ℕ) : ℂ) S m.1 m.2]
  have hpoly := polynomial_eval_eq_neg_sum_normalized_localCircleKernel
    hR hS hRl P hPdeg
  simp_rw [hjet] at hpoly
  rw [houter, hpoly]
  ring

/-- Quantitative source equation (9) for the Hermite polynomial itself.
The `2/3` small-jet exponent and the `1/6` local-contour loss leave the
required `1/2` exponent, with no `log R` loss. -/
theorem norm_polynomial_eval_le_exp_neg_half_of_local_jets
    {R S l : ℕ} (hR : 1 ≤ R) (hS : 1 ≤ S) (hRl : R < l)
    (P : ℂ[X]) (hPdeg : P ∈ Polynomial.degreeLT ℂ (R * S))
    {A delta : ℝ} (hA : 0 ≤ A) (hdelta : 0 ≤ delta)
    (hsmall : delta ≤ Real.exp (-(2 / 3) * A))
    (hcontour :
      (2 : ℝ) ^ (((3 * R + l) * S) + R * S) ≤
        Real.exp ((1 / 6) * A))
    (hjet : ∀ r : Fin R, ∀ m : Fin S,
      ‖(hasseDeriv m.1 P).eval ((r.1 + 1 : ℕ) : ℂ)‖ ≤ delta) :
    ‖P.eval (l : ℂ)‖ ≤ Real.exp (-(1 / 2) * A) := by
  rw [polynomial_eval_eq_neg_sum_normalized_localCircleKernel
    hR hS hRl P hPdeg, norm_neg]
  exact norm_sum_normalized_localCircleKernel_integral_le_exp
    hRl hA hdelta hsmall hcontour
      (fun r m ↦ (hasseDeriv m.1 P).eval ((r.1 + 1 : ℕ) : ℂ)) hjet

/-- Exact source equation (9).  The normalized outer integral of an
entire function equals its value at the new integer plus the sum of the
normalized old-node jets against the local-circle kernels. -/
theorem normalized_outerCircleIntegral_localEntireKernel_eq_value_add_local
    {R S l : ℕ} (hR : 1 ≤ R) (hS : 1 ≤ S) (hRl : R < l)
    (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    {c : ℂ} {rho : ℝ}
    (hlball : (l : ℂ) ∈ Metric.ball c rho)
    (hnodes : ∀ r : Fin R,
      (((r.1 + 1 : ℕ) : ℂ)) ∈ Metric.ball c rho) :
    (2 * ((Real.pi : ℝ) : ℂ) * I)⁻¹ *
        (∮ z in C(c, rho), localEntireKernel R S (l : ℂ) f z) =
      f (l : ℂ) +
        ∑ r : Fin R, ∑ m : Fin S,
          (iteratedDeriv m.1 f ((r.1 + 1 : ℕ) : ℂ) /
            (m.1.factorial : ℂ)) *
            ((2 * ((Real.pi : ℝ) : ℂ) * I)⁻¹ *
              ∮ z in C(((r.1 + 1 : ℕ) : ℂ), (1 / 2 : ℝ)),
                localCircleKernel R S (r.1 + 1) l m.1 z) := by
  let P : ℂ[X] := HermiteInterpolation.polynomial f (integralNodes R S)
  have hrho : 0 < rho := dist_nonneg.trans_lt hlball
  have hFcircle : ∀ z ∈ Metric.sphere c rho,
      (localNodalPolynomial R S).eval z ≠ 0 := by
    intro z hz
    rw [localNodalPolynomial_eval]
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    apply pow_ne_zero
    rw [sub_ne_zero]
    exact Metric.sphere_disjoint_ball.ne_of_mem hz
      (hnodes ⟨i, Finset.mem_range.mp hi⟩)
  have htargetCircle : ∀ z ∈ Metric.sphere c rho,
      z - (l : ℂ) ≠ 0 := by
    intro z hz
    exact sub_ne_zero.mpr
      (Metric.sphere_disjoint_ball.ne_of_mem hz hlball)
  have hkernelIntegrable (g : ℂ → ℂ) (hg : Continuous g) :
      CircleIntegrable (localEntireKernel R S (l : ℂ) g) c rho := by
    apply ContinuousOn.circleIntegrable hrho.le
    unfold localEntireKernel
    apply ContinuousOn.div
    · apply ContinuousOn.mul
      · exact continuousOn_const.div
          (Polynomial.continuous _).continuousOn hFcircle
      · exact hg.continuousOn
    · exact continuousOn_id.sub continuousOn_const
    · exact htargetCircle
  have hfint : CircleIntegrable
      (localEntireKernel R S (l : ℂ) f) c rho :=
    hkernelIntegrable f hf.continuous
  have hPint : CircleIntegrable
      (localPolynomialKernel R S (l : ℂ) P) c rho := by
    simpa only [localEntireKernel_polynomial] using
      hkernelIntegrable (fun z ↦ P.eval z) (Polynomial.continuous P)
  have hsubIntegral := circleIntegral.integral_sub hfint hPint
  have hrem := normalized_outerCircleIntegral_entireKernel_sub_polynomial
    hS f hf hlball hnodes
  have hPdeg : P ∈ Polynomial.degreeLT ℂ (R * S) :=
    polynomial_integralNodes_mem_degreeLT f R S
  have houterP := normalized_outerCircleIntegral_localPolynomialKernel_eq_zero
    hR hS hRl P hPdeg hlball hnodes
  have hpoly := polynomial_eval_eq_neg_sum_normalized_localCircleKernel
    hR hS hRl P hPdeg
  have hjet (r : Fin R) (m : Fin S) :
      (hasseDeriv m.1 P).eval ((r.1 + 1 : ℕ) : ℂ) =
        iteratedDeriv m.1 f ((r.1 + 1 : ℕ) : ℂ) /
          (m.1.factorial : ℂ) := by
    rw [hasseDeriv_eval_eq_iteratedDeriv_div_factorial]
    obtain ⟨after, hsplit⟩ :=
      integralNodes_eq_append_replicate_append (S := S) r
    dsimp only [P]
    rw [hsplit]
    rw [HermiteInterpolation.iteratedDeriv_eval_polynomial_eq_of_replicate_block
      hf (integralNodes r.1 S) after ((r.1 + 1 : ℕ) : ℂ)
        S m.1 m.2]
  simp_rw [hjet] at hpoly
  calc
    (2 * ((Real.pi : ℝ) : ℂ) * I)⁻¹ *
        (∮ z in C(c, rho), localEntireKernel R S (l : ℂ) f z) =
      (2 * ((Real.pi : ℝ) : ℂ) * I)⁻¹ *
          (∮ z in C(c, rho),
            localEntireKernel R S (l : ℂ) f z -
              localPolynomialKernel R S (l : ℂ) P z) +
        (2 * ((Real.pi : ℝ) : ℂ) * I)⁻¹ *
          (∮ z in C(c, rho),
            localPolynomialKernel R S (l : ℂ) P z) := by
              rw [hsubIntegral]
              ring
    _ = (f (l : ℂ) - P.eval (l : ℂ)) + 0 := by
      rw [hrem, houterP]
    _ = f (l : ℂ) +
        ∑ r : Fin R, ∑ m : Fin S,
          (iteratedDeriv m.1 f ((r.1 + 1 : ℕ) : ℂ) /
            (m.1.factorial : ℂ)) *
            ((2 * ((Real.pi : ℝ) : ℂ) * I)⁻¹ *
              ∮ z in C(((r.1 + 1 : ℕ) : ℂ), (1 / 2 : ℝ)),
                localCircleKernel R S (r.1 + 1) l m.1 z) := by
      rw [hpoly]
      ring

/-- Source equation (9) with the paper's outer circle of radius
`3 * Rnext` and a target integer `R < l ≤ Rnext`. -/
theorem sourceEquationNine
    {R S l Rnext : ℕ} (hR : 1 ≤ R) (hS : 1 ≤ S)
    (hRl : R < l) (hlRnext : l ≤ Rnext)
    (f : ℂ → ℂ) (hf : Differentiable ℂ f) :
    (2 * ((Real.pi : ℝ) : ℂ) * I)⁻¹ *
        (∮ z in C(0, ((3 * Rnext : ℕ) : ℝ)),
          localEntireKernel R S (l : ℂ) f z) =
      f (l : ℂ) +
        ∑ r : Fin R, ∑ m : Fin S,
          (iteratedDeriv m.1 f ((r.1 + 1 : ℕ) : ℂ) /
            (m.1.factorial : ℂ)) *
            ((2 * ((Real.pi : ℝ) : ℂ) * I)⁻¹ *
              ∮ z in C(((r.1 + 1 : ℕ) : ℂ), (1 / 2 : ℝ)),
                localCircleKernel R S (r.1 + 1) l m.1 z) := by
  apply normalized_outerCircleIntegral_localEntireKernel_eq_value_add_local
    hR hS hRl f hf
  · rw [Metric.mem_ball, dist_zero_right, Complex.norm_natCast]
    exact_mod_cast (show l < 3 * Rnext by omega)
  · intro r
    rw [Metric.mem_ball, dist_zero_right, Complex.norm_natCast]
    exact_mod_cast (show r.1 + 1 < 3 * Rnext by omega)

end Erdos240.BakerLemma4Concrete
