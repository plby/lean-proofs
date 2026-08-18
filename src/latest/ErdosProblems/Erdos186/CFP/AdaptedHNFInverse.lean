/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.AdaptedHNF

/-!
# The inverse anisotropic estimate for an adapted lattice basis

An adapted basis is triangular with positive integral pivots.  Forward
substitution therefore bounds its basis coordinates in terms of ambient
coordinates.  The deliberately coarse constant below is uniform in the
coordinate and is sufficient for the bounding-box argument in CFP Lemma
2.16.
-/

namespace Erdos186.CFP.AdaptedHNF

open scoped BigOperators
open Module
open LatticeBasis

/-- The one-step loss in forward substitution. -/
def inverseCoefficientBase (d : ℕ) (v : Fin d → ℕ) : ℤ :=
  1 + (d : ℤ) * ∑ j, (v j : ℤ)

/-- A uniform loss for all `d` steps of forward substitution. -/
def inverseCoefficientConstant (d : ℕ) (v : Fin d → ℕ) : ℤ :=
  inverseCoefficientBase d v ^ d

/-- The same loss as a natural number, for use as a GAP radius. -/
def inverseCoefficientConstantNat (d : ℕ) (v : Fin d → ℕ) : ℕ :=
  (1 + d * ∑ j, v j) ^ d

@[simp, norm_cast] theorem coe_inverseCoefficientConstantNat
    (d : ℕ) (v : Fin d → ℕ) :
    (inverseCoefficientConstantNat d v : ℤ) =
      inverseCoefficientConstant d v := by
  simp [inverseCoefficientConstantNat, inverseCoefficientConstant,
    inverseCoefficientBase]

theorem one_le_inverseCoefficientBase (d : ℕ) (v : Fin d → ℕ) :
    1 ≤ inverseCoefficientBase d v := by
  unfold inverseCoefficientBase
  exact le_add_of_nonneg_right <|
    mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ ↦ by positivity)

theorem coordinate_term_bound {d : ℕ} {v w : Fin d → ℕ}
    {Gamma : Sublattice d} {b : Basis (Fin d) ℤ Gamma}
    (hb : IsAdapted (v := v) b) (hw : Monotone w)
    (y : Gamma) (i k : Fin d) (hki : k < i)
    (hk : |basisCoeff b y k| ≤
      inverseCoefficientBase d v ^ i.val * (w k : ℤ)) :
    |basisCoeff b y k * (((b k : Gamma) : LatticePoint d) i)| ≤
      inverseCoefficientBase d v ^ i.val * (w i : ℤ) *
        (∑ j, (v j : ℤ)) := by
  rw [abs_mul]
  have hentry0 : 0 ≤ (((b k : Gamma) : LatticePoint d) i) := (hb k i).2.1
  have hentryv : (((b k : Gamma) : LatticePoint d) i) ≤ (v i : ℤ) :=
    (hb k i).2.2
  rw [abs_of_nonneg hentry0]
  have hwki : (w k : ℤ) ≤ (w i : ℤ) := by
    exact_mod_cast hw hki.le
  have hvi : (v i : ℤ) ≤ ∑ j, (v j : ℤ) := by
    exact Finset.single_le_sum
      (s := Finset.univ) (f := fun j : Fin d ↦ (v j : ℤ))
      (fun j _ ↦ by exact_mod_cast Nat.zero_le (v j)) (Finset.mem_univ i)
  have hbase0 : 0 ≤ inverseCoefficientBase d v :=
    le_trans (by norm_num) (one_le_inverseCoefficientBase d v)
  have hpow0 : 0 ≤ inverseCoefficientBase d v ^ i.val :=
    pow_nonneg hbase0 _
  calc
    |basisCoeff b y k| * (((b k : Gamma) : LatticePoint d) i) ≤
        (inverseCoefficientBase d v ^ i.val * (w k : ℤ)) *
          (((b k : Gamma) : LatticePoint d) i) :=
      mul_le_mul_of_nonneg_right hk hentry0
    _ ≤ (inverseCoefficientBase d v ^ i.val * (w i : ℤ)) *
          (v i : ℤ) := by
      calc
        (inverseCoefficientBase d v ^ i.val * (w k : ℤ)) *
            (((b k : Gamma) : LatticePoint d) i) ≤
            (inverseCoefficientBase d v ^ i.val * (w i : ℤ)) *
              (((b k : Gamma) : LatticePoint d) i) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hwki hpow0) hentry0
        _ ≤ (inverseCoefficientBase d v ^ i.val * (w i : ℤ)) *
              (v i : ℤ) := by
          exact mul_le_mul_of_nonneg_left hentryv
            (mul_nonneg hpow0 (by positivity))
    _ ≤ inverseCoefficientBase d v ^ i.val * (w i : ℤ) *
          (∑ j, (v j : ℤ)) := by
      exact mul_le_mul_of_nonneg_left hvi
        (mul_nonneg hpow0 (by positivity))

/-- The forward-substitution estimate at the `i`th pivot. -/
theorem abs_basisCoeff_le_inverseCoefficientBase_pow {d : ℕ}
    {v w : Fin d → ℕ} {Gamma : Sublattice d}
    {b : Basis (Fin d) ℤ Gamma}
    (hb : IsAdapted (v := v) b) (hdiag : HasPositiveDiagonal b)
    (hw : Monotone w) (y : Gamma)
    (hy : ∀ j, |((y : Gamma) : LatticePoint d) j| ≤ (w j : ℤ)) :
    ∀ i, |basisCoeff b y i| ≤
      inverseCoefficientBase d v ^ (i.val + 1) * (w i : ℤ) := by
  intro i
  induction hi : i.val using Nat.strong_induction_on generalizing i with
  | h n ih =>
      have hprev : ∀ k : Fin d, k < i →
          |basisCoeff b y k| ≤
            inverseCoefficientBase d v ^ i.val * (w k : ℤ) := by
        intro k hki
        have hkn : k.val < n := by omega
        have hk := ih k.val hkn k rfl
        have hexp : k.val + 1 ≤ i.val := by omega
        exact hk.trans <| mul_le_mul_of_nonneg_right
          (pow_le_pow_right₀ (one_le_inverseCoefficientBase d v) hexp)
          (by positivity)
      have hrecon := basisCoeff_reconstruction_Iic b hb y i
      rw [Finset.Iic_eq_cons_Iio, Finset.sum_cons] at hrecon
      have hpivot : 1 ≤ (((b i : Gamma) : LatticePoint d) i) := hdiag i
      have hsumabs :
          |∑ k ∈ Finset.Iio i,
              basisCoeff b y k * (((b k : Gamma) : LatticePoint d) i)| ≤
            ∑ k ∈ Finset.Iio i,
              |basisCoeff b y k * (((b k : Gamma) : LatticePoint d) i)| := by
        exact Finset.abs_sum_le_sum_abs _ _
      have hterm : ∀ k ∈ Finset.Iio i,
          |basisCoeff b y k * (((b k : Gamma) : LatticePoint d) i)| ≤
            inverseCoefficientBase d v ^ i.val * (w i : ℤ) *
              (∑ j, (v j : ℤ)) := by
        intro k hk
        exact coordinate_term_bound hb hw y i k (Finset.mem_Iio.mp hk) <|
          hprev k (Finset.mem_Iio.mp hk)
      have hsum :
          ∑ k ∈ Finset.Iio i,
              |basisCoeff b y k * (((b k : Gamma) : LatticePoint d) i)| ≤
            (d : ℤ) *
              (inverseCoefficientBase d v ^ i.val * (w i : ℤ) *
                (∑ j, (v j : ℤ))) := by
        calc
          ∑ k ∈ Finset.Iio i,
              |basisCoeff b y k * (((b k : Gamma) : LatticePoint d) i)| ≤
              ∑ _k ∈ Finset.Iio i,
                (inverseCoefficientBase d v ^ i.val * (w i : ℤ) *
                  (∑ j, (v j : ℤ))) := by
            exact Finset.sum_le_sum fun k hk ↦ hterm k hk
          _ = ((Finset.Iio i).card : ℤ) *
                (inverseCoefficientBase d v ^ i.val * (w i : ℤ) *
                  (∑ j, (v j : ℤ))) := by simp
          _ ≤ (d : ℤ) *
                (inverseCoefficientBase d v ^ i.val * (w i : ℤ) *
                  (∑ j, (v j : ℤ))) := by
            apply mul_le_mul_of_nonneg_right
            · have hc : (Finset.Iio i).card ≤ d := by
                simpa using Finset.card_le_univ (Finset.Iio i)
              exact_mod_cast hc
            · exact mul_nonneg
                (mul_nonneg
                  (pow_nonneg
                    (le_trans (by norm_num)
                      (one_le_inverseCoefficientBase d v)) _)
                  (by positivity))
                (Finset.sum_nonneg fun _ _ ↦ by positivity)
      have hmul :
          |basisCoeff b y i| * (((b i : Gamma) : LatticePoint d) i) ≤
            (w i : ℤ) +
              (d : ℤ) *
                (inverseCoefficientBase d v ^ i.val * (w i : ℤ) *
                  (∑ j, (v j : ℤ))) := by
        calc
          |basisCoeff b y i| * (((b i : Gamma) : LatticePoint d) i) =
              |basisCoeff b y i * (((b i : Gamma) : LatticePoint d) i)| := by
                rw [abs_mul, abs_of_pos (hdiag i)]
          _ = |((y : Gamma) : LatticePoint d) i -
                ∑ k ∈ Finset.Iio i,
                  basisCoeff b y k * (((b k : Gamma) : LatticePoint d) i)| := by
            congr 1
            linarith
          _ ≤ |((y : Gamma) : LatticePoint d) i| +
                |∑ k ∈ Finset.Iio i,
                  basisCoeff b y k * (((b k : Gamma) : LatticePoint d) i)| :=
            abs_sub _ _
          _ ≤ (w i : ℤ) +
                ∑ k ∈ Finset.Iio i,
                  |basisCoeff b y k * (((b k : Gamma) : LatticePoint d) i)| :=
            add_le_add (hy i) hsumabs
          _ ≤ (w i : ℤ) +
              (d : ℤ) *
                (inverseCoefficientBase d v ^ i.val * (w i : ℤ) *
                  (∑ j, (v j : ℤ))) := add_le_add (le_refl _) hsum
      calc
        |basisCoeff b y i| = |basisCoeff b y i| * 1 := by ring
        _ ≤ |basisCoeff b y i| * (((b i : Gamma) : LatticePoint d) i) :=
          mul_le_mul_of_nonneg_left hpivot (abs_nonneg _)
        _ ≤ (w i : ℤ) +
              (d : ℤ) *
                (inverseCoefficientBase d v ^ i.val * (w i : ℤ) *
                  (∑ j, (v j : ℤ))) := hmul
        _ ≤ inverseCoefficientBase d v ^ (n + 1) * (w i : ℤ) := by
          rw [← hi]
          have hpow : 1 ≤ inverseCoefficientBase d v ^ i.val :=
            one_le_pow₀ (one_le_inverseCoefficientBase d v)
          have hwgrow : (w i : ℤ) ≤
              inverseCoefficientBase d v ^ i.val * (w i : ℤ) := by
            calc
              (w i : ℤ) = 1 * (w i : ℤ) := by ring
              _ ≤ inverseCoefficientBase d v ^ i.val * (w i : ℤ) :=
                mul_le_mul_of_nonneg_right hpow (by positivity)
          calc
            (w i : ℤ) +
                (d : ℤ) *
                  (inverseCoefficientBase d v ^ i.val * (w i : ℤ) *
                    (∑ j, (v j : ℤ))) ≤
                inverseCoefficientBase d v ^ i.val * (w i : ℤ) +
                  (d : ℤ) *
                    (inverseCoefficientBase d v ^ i.val * (w i : ℤ) *
                      (∑ j, (v j : ℤ))) := by
              simpa only [add_comm] using
                add_le_add_right hwgrow
                  ((d : ℤ) *
                    (inverseCoefficientBase d v ^ i.val * (w i : ℤ) *
                      (∑ j, (v j : ℤ))))
            _ = inverseCoefficientBase d v ^ (i.val + 1) * (w i : ℤ) := by
              rw [pow_succ]
              unfold inverseCoefficientBase
              ring

/-- Ambient coordinate bounds in a monotone box imply coordinatewise basis
coefficient bounds in the correspondingly scaled box. -/
theorem abs_basisCoeff_le_inverseCoefficientConstant {d : ℕ}
    {v w : Fin d → ℕ} {Gamma : Sublattice d}
    {b : Basis (Fin d) ℤ Gamma}
    (hb : IsAdapted (v := v) b) (hdiag : HasPositiveDiagonal b)
    (hw : Monotone w) (y : Gamma)
    (hy : ∀ j, |((y : Gamma) : LatticePoint d) j| ≤ (w j : ℤ))
    (i : Fin d) :
    |basisCoeff b y i| ≤
      inverseCoefficientConstant d v * (w i : ℤ) := by
  have hi := abs_basisCoeff_le_inverseCoefficientBase_pow hb hdiag hw y hy i
  refine hi.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
  exact pow_le_pow_right₀ (one_le_inverseCoefficientBase d v) (by omega)

/-- Natural-radius form of `abs_basisCoeff_le_inverseCoefficientConstant`. -/
theorem abs_basisCoeff_le_inverseCoefficientConstantNat {d : ℕ}
    {v w : Fin d → ℕ} {Gamma : Sublattice d}
    {b : Basis (Fin d) ℤ Gamma}
    (hb : IsAdapted (v := v) b) (hdiag : HasPositiveDiagonal b)
    (hw : Monotone w) (y : Gamma)
    (hy : ∀ j, |((y : Gamma) : LatticePoint d) j| ≤ (w j : ℤ))
    (i : Fin d) :
    |basisCoeff b y i| ≤
      (inverseCoefficientConstantNat d v * w i : ℕ) := by
  simpa using abs_basisCoeff_le_inverseCoefficientConstant hb hdiag hw y hy i

/-- A single sorted adapted basis controls both directions of the comparison
between an arbitrary ambient box and a basis-coefficient box.  The forward
loss is coordinatewise `d * v j`; the reverse loss is the dimension-only
forward-substitution constant for the permuted period vector. -/
theorem exists_widthAdapted_basis_with_inverse {d : ℕ}
    {v w : Fin d → ℕ} (hv : ∀ i, 0 < v i)
    (Gamma : Sublattice d) (hrect : rectangularSubgroup v ≤ Gamma) :
    ∃ (sigma : Equiv.Perm (Fin d)) (b : Basis (Fin d) ℤ Gamma),
      Monotone (w ∘ sigma) ∧
      (∀ (C : ℕ) (a : Fin d → ℤ),
        (∀ i, |a i| ≤ (C * w (sigma i) : ℕ)) →
        ∀ j,
          |((∑ i, a i • b i : Gamma) : LatticePoint d) j| ≤
            (C * d * v j * w j : ℕ)) ∧
      (∀ y : Gamma,
        (∀ j, |((y : Gamma) : LatticePoint d) j| ≤ (w j : ℤ)) →
        ∀ i,
          |basisCoeff b y i| ≤
            (inverseCoefficientConstantNat d (v ∘ sigma) *
              w (sigma i) : ℕ)) := by
  let sigma : Equiv.Perm (Fin d) := Tuple.sort w
  let vp : Fin d → ℕ := v ∘ sigma
  let wp : Fin d → ℕ := w ∘ sigma
  let GammaP : Sublattice d := permutedSublattice sigma Gamma
  have hvp : ∀ i, 0 < vp i := fun i ↦ hv (sigma i)
  have hrectP : rectangularSubgroup vp ≤ GammaP := by
    exact rectangularSubgroup_perm_le sigma hrect
  obtain ⟨bp, hbp, hdiagp⟩ :=
    exists_adapted_basis_with_pos hvp GammaP hrectP
  let e : Gamma ≃ₗ[ℤ] GammaP := permutedSublatticeEquiv sigma Gamma
  let b : Basis (Fin d) ℤ Gamma := bp.map e.symm
  have hwp : Monotone wp := Tuple.monotone_sort w
  refine ⟨sigma, b, hwp, ?_, ?_⟩
  · intro C a ha j
    let jp : Fin d := sigma.symm j
    have hCwp : Monotone (fun i ↦ C * wp i) := by
      intro i k hik
      exact Nat.mul_le_mul_left C (hwp hik)
    have hbound := abs_sum_basis_smul_apply_le
      (v := vp) (w := fun i ↦ C * wp i)
      hbp hCwp a (by simpa [wp] using ha) jp
    have hcoord :
        ((∑ i, a i • b i : Gamma) : LatticePoint d) j =
          ((∑ i, a i • bp i : GammaP) : LatticePoint d) jp := by
      change ((∑ i, a i • (bp.map e.symm) i : Gamma) : LatticePoint d) j = _
      simp only [Basis.map_apply]
      have heq : e (∑ i, a i • e.symm (bp i)) =
          ∑ i, a i • bp i := by simp
      have hfun := congrArg
        (fun z : GammaP ↦ ((z : LatticePoint d) jp)) heq
      calc
        ((∑ i, a i • e.symm (bp i) : Gamma) : LatticePoint d) j =
            coordinatePerm sigma
              (((∑ i, a i • e.symm (bp i) : Gamma) : LatticePoint d)) jp := by
                simp [jp]
        _ = ((e (∑ i, a i • e.symm (bp i)) : GammaP) :
              LatticePoint d) jp := rfl
        _ = ((∑ i, a i • bp i : GammaP) : LatticePoint d) jp := hfun
    rw [hcoord]
    simpa [vp, wp, jp, mul_assoc, mul_left_comm, mul_comm] using hbound
  · intro y hy i
    have hey : ∀ j,
        |((e y : GammaP) : LatticePoint d) j| ≤ (wp j : ℤ) := by
      intro j
      change |((y : Gamma) : LatticePoint d) (sigma j)| ≤
        (w (sigma j) : ℤ)
      exact hy (sigma j)
    have hbound := abs_basisCoeff_le_inverseCoefficientConstantNat
      hbp hdiagp hwp (e y) hey i
    have hcoeff : basisCoeff b y i = basisCoeff bp (e y) i := by
      simp [b, basisCoeff]
    rw [hcoeff]
    simpa [vp, wp] using hbound

end Erdos186.CFP.AdaptedHNF
