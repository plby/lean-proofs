/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.GallagherRoughTransform
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
# Imprimitive Gauss norms for Gallagher's rough-support amplifier

This file proves the finite CRT identity at the heart of the
Bombieri--Davenport--Gallagher amplifier.  A primitive multiplicative
character induced across a coprime squarefree multiplier has Gauss-sum
squared norm equal to its original conductor.  The proof also develops the
needed arbitrary-primitive-additive-character Gauss norm and the squarefree
Ramanujan unit-sum norm.
-/

open scoped BigOperators ArithmeticFunction.Moebius

noncomputable section

namespace Erdos48

private theorem sum_zmod_eq_sum_range
    {q : ℕ} [NeZero q] {A : Type*} [AddCommMonoid A]
    (f : ZMod q → A) :
    (∑ x : ZMod q, f x) = ∑ n ∈ Finset.range q, f (n : ZMod q) := by
  calc
    (∑ x : ZMod q, f x) = ∑ x : Fin q, f (ZMod.finEquiv q x) := by
      exact (Equiv.sum_comp (ZMod.finEquiv q).toEquiv f).symm
    _ = ∑ n ∈ Finset.range q, f (n : ZMod q) := by
      cases q with
      | zero => exact (NeZero.ne 0 rfl).elim
      | succ q =>
          have hpoint (x : Fin (q + 1)) :
              f (ZMod.finEquiv (q + 1) x) =
                f (x.1 : ZMod (q + 1)) := by
            congr 1
            apply Fin.ext
            simp only [ZMod.finEquiv, RingEquiv.refl_apply]
            exact (Nat.mod_eq_of_lt x.2).symm
          simp_rw [hpoint]
          exact Fin.sum_univ_eq_sum_range
            (f := fun n : ℕ => f (n : ZMod (q + 1))) (q + 1)

noncomputable def crtLeftAddChar {m n : ℕ} (h : m.Coprime n)
    (e : AddChar (ZMod (m * n)) ℂ) : AddChar (ZMod m) ℂ :=
  e.compAddMonoidHom
    ((ZMod.chineseRemainder h).symm.toAddMonoidHom.comp
      (AddMonoidHom.inl (ZMod m) (ZMod n)))

noncomputable def crtRightAddChar {m n : ℕ} (h : m.Coprime n)
    (e : AddChar (ZMod (m * n)) ℂ) : AddChar (ZMod n) ℂ :=
  e.compAddMonoidHom
    ((ZMod.chineseRemainder h).symm.toAddMonoidHom.comp
      (AddMonoidHom.inr (ZMod m) (ZMod n)))

theorem crtLeftAddChar_apply {m n : ℕ} (h : m.Coprime n)
    (e : AddChar (ZMod (m * n)) ℂ) (x : ZMod m) :
    crtLeftAddChar h e x =
      e ((ZMod.chineseRemainder h).symm (x, 0)) := rfl

theorem crtRightAddChar_apply {m n : ℕ} (h : m.Coprime n)
    (e : AddChar (ZMod (m * n)) ℂ) (x : ZMod n) :
    crtRightAddChar h e x =
      e ((ZMod.chineseRemainder h).symm (0, x)) := rfl

theorem crtLeftAddChar_isPrimitive {m n : ℕ} [NeZero m] [NeZero n]
    (h : m.Coprime n) (e : AddChar (ZMod (m * n)) ℂ)
    (he : e.IsPrimitive) : (crtLeftAddChar h e).IsPrimitive := by
  apply AddChar.zmod_char_primitive_of_eq_one_only_at_zero
  intro x hx
  have hzero : (ZMod.chineseRemainder h).symm (x, 0) = 0 :=
    (he.zmod_char_eq_one_iff (m * n)
      ((ZMod.chineseRemainder h).symm (x, 0))).1 hx
  have hpair := congrArg (ZMod.chineseRemainder h) hzero
  simpa using congrArg Prod.fst hpair

theorem crtRightAddChar_isPrimitive {m n : ℕ} [NeZero m] [NeZero n]
    (h : m.Coprime n) (e : AddChar (ZMod (m * n)) ℂ)
    (he : e.IsPrimitive) : (crtRightAddChar h e).IsPrimitive := by
  apply AddChar.zmod_char_primitive_of_eq_one_only_at_zero
  intro x hx
  have hzero : (ZMod.chineseRemainder h).symm (0, x) = 0 :=
    (he.zmod_char_eq_one_iff (m * n)
      ((ZMod.chineseRemainder h).symm (0, x))).1 hx
  have hpair := congrArg (ZMod.chineseRemainder h) hzero
  simpa using congrArg Prod.snd hpair

noncomputable def unitAddCharSum {R : Type*} [CommRing R] [Fintype R]
    [Fintype Rˣ]
    (e : AddChar R ℂ) : ℂ :=
  ∑ u : Rˣ, e (u : R)

theorem unitAddCharSum_crt {m n : ℕ} [NeZero m] [NeZero n]
    (h : m.Coprime n) (e : AddChar (ZMod (m * n)) ℂ) :
    unitAddCharSum e =
      unitAddCharSum (crtLeftAddChar h e) *
        unitAddCharSum (crtRightAddChar h e) := by
  classical
  let E : (ZMod (m * n))ˣ ≃* ((ZMod m)ˣ × (ZMod n)ˣ) :=
    (Units.mapEquiv (ZMod.chineseRemainder h).toMulEquiv).trans
      MulEquiv.prodUnits
  have hcoe (u : (ZMod m)ˣ × (ZMod n)ˣ) :
      ((E.symm u : (ZMod (m * n))ˣ) : ZMod (m * n)) =
        (ZMod.chineseRemainder h).symm
          ((u.1 : ZMod m), (u.2 : ZMod n)) := by
    apply (ZMod.chineseRemainder h).injective
    rw [(ZMod.chineseRemainder h).apply_symm_apply]
    have hE := E.apply_symm_apply u
    have hv := congrArg
      (fun z : (ZMod m)ˣ × (ZMod n)ˣ =>
        ((z.1 : ZMod m), (z.2 : ZMod n))) hE
    change
      ((↑(MulEquiv.prodUnits
          ((Units.mapEquiv (ZMod.chineseRemainder h).toMulEquiv)
            (E.symm u))).1 : ZMod m),
        (↑(MulEquiv.prodUnits
          ((Units.mapEquiv (ZMod.chineseRemainder h).toMulEquiv)
            (E.symm u))).2 : ZMod n)) =
        ((u.1 : ZMod m), (u.2 : ZMod n))
    exact hv
  calc
    unitAddCharSum e =
        ∑ u : (ZMod m)ˣ × (ZMod n)ˣ,
          e ((E.symm u : (ZMod (m * n))ˣ) : ZMod (m * n)) := by
      unfold unitAddCharSum
      exact (Equiv.sum_comp E.symm.toEquiv
        (fun u : (ZMod (m * n))ˣ => e (u : ZMod (m * n)))).symm
    _ = ∑ u : (ZMod m)ˣ × (ZMod n)ˣ,
          crtLeftAddChar h e (u.1 : ZMod m) *
            crtRightAddChar h e (u.2 : ZMod n) := by
      apply Fintype.sum_congr
      intro u
      rw [hcoe]
      rw [show (ZMod.chineseRemainder h).symm
          ((u.1 : ZMod m), (u.2 : ZMod n)) =
          (ZMod.chineseRemainder h).symm ((u.1 : ZMod m), 0) +
            (ZMod.chineseRemainder h).symm (0, (u.2 : ZMod n)) by
        apply (ZMod.chineseRemainder h).injective
        simp]
      rw [AddChar.map_add_eq_mul]
      rfl
    _ = unitAddCharSum (crtLeftAddChar h e) *
          unitAddCharSum (crtRightAddChar h e) := by
      unfold unitAddCharSum
      rw [Fintype.sum_prod_type]
      simp only [Prod.fst, Prod.snd]
      rw [← Fintype.sum_mul_sum]

private theorem unitAddCharSum_eq_sum_isUnitSubtype
    {R : Type*} [CommRing R] [Fintype R] [Fintype Rˣ]
    [Fintype (IsUnit.submonoid R)]
    (e : AddChar R ℂ) :
    unitAddCharSum e =
      ∑ x : IsUnit.submonoid R, e (x : R) := by
  unfold unitAddCharSum
  apply Fintype.sum_equiv
    (Submonoid.unitsTypeEquivIsUnitSubmonoid (M := R)).toEquiv
  intro u
  rfl

theorem unitAddCharSum_eq_neg_one_of_prime
    {p : ℕ} [NeZero p] (hp : p.Prime) (e : AddChar (ZMod p) ℂ)
    (he : e.IsPrimitive) : unitAddCharSum e = -1 := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  letI : Fintype (IsUnit.submonoid (ZMod p)) := Fintype.ofFinite _
  have hfilter :
      (Finset.univ : Finset (ZMod p)).filter IsUnit =
        Finset.univ.erase 0 := by
    ext x
    simp [isUnit_iff_ne_zero]
  have heNe : e ≠ 1 := by
    intro htriv
    apply he (a := (1 : ZMod p)) one_ne_zero
    simpa [htriv]
  have hsum : (∑ x : ZMod p, e x) = 0 :=
    AddChar.sum_eq_zero_of_ne_one heNe
  rw [← Finset.sum_erase_add _ _
    (Finset.mem_univ (0 : ZMod p))] at hsum
  calc
    unitAddCharSum e = ∑ x : IsUnit.submonoid (ZMod p), e (x : ZMod p) :=
      unitAddCharSum_eq_sum_isUnitSubtype e
    _ = ∑ x ∈ (Finset.univ : Finset (ZMod p)).filter IsUnit, e x := by
      exact (Finset.sum_subtype
        (p := IsUnit) ((Finset.univ : Finset (ZMod p)).filter IsUnit)
        (by simp) (fun x ↦ e x)).symm
    _ = ∑ x ∈ Finset.univ.erase (0 : ZMod p), e x := by rw [hfilter]
    _ = -1 := by
      have : (∑ x ∈ Finset.univ.erase (0 : ZMod p), e x) = -(e 0) := by
        exact eq_neg_of_add_eq_zero_left hsum
      simpa using this

theorem norm_unitAddCharSum_eq_one_of_prime
    {p : ℕ} [NeZero p] (hp : p.Prime) (e : AddChar (ZMod p) ℂ)
    (he : e.IsPrimitive) : ‖unitAddCharSum e‖ = 1 := by
  rw [unitAddCharSum_eq_neg_one_of_prime hp e he]
  norm_num

theorem norm_unitAddCharSum_eq_one_of_squarefree
    {n : ℕ} [NeZero n] (hn : Squarefree n)
    (e : AddChar (ZMod n) ℂ) (he : e.IsPrimitive) :
    ‖unitAddCharSum e‖ = 1 := by
  let motive : ℕ → Prop := fun k =>
    ∀ [NeZero k] (e : AddChar (ZMod k) ℂ), Squarefree k →
      e.IsPrimitive → ‖unitAddCharSum e‖ = 1
  have hall : ∀ k, motive k := by
    apply Nat.prime_composite_induction
    · intro hk
      exact (hk.ne 0 rfl).elim
    · intro _inst e _hsq _he
      have hsum : unitAddCharSum e = 1 := by
        unfold unitAddCharSum
        rw [Fintype.sum_unique]
        simpa only [show ((default : (ZMod 1)ˣ) : ZMod 1) = 0 by
          exact Subsingleton.elim _ _] using e.map_zero_eq_one
      rw [hsum]
      norm_num
    · intro p hp _inst e _hsq he
      exact norm_unitAddCharSum_eq_one_of_prime hp e he
    · intro a ha iha b hb ihb _inst e hab he
      have hcop : a.Coprime b := Nat.coprime_of_squarefree_mul hab
      letI : NeZero a := ⟨(lt_of_lt_of_le Nat.zero_lt_two ha).ne'⟩
      letI : NeZero b := ⟨(lt_of_lt_of_le Nat.zero_lt_two hb).ne'⟩
      rw [unitAddCharSum_crt hcop e, norm_mul,
        iha (crtLeftAddChar hcop e) hab.of_mul_left
          (crtLeftAddChar_isPrimitive hcop e he),
        ihb (crtRightAddChar hcop e) hab.of_mul_right
          (crtRightAddChar_isPrimitive hcop e he), one_mul]
  exact hall n e hn he

private theorem sum_star_mul_addCharFourier
    {q : ℕ} [NeZero q] (e : AddChar (ZMod q) ℂ)
    (he : e.IsPrimitive) (f : ZMod q → ℂ) :
    (∑ k : ZMod q,
      star (∑ j : ZMod q, e (-(j * k)) * f j) *
        (∑ j : ZMod q, e (-(j * k)) * f j)) =
      (q : ℂ) * ∑ j : ZMod q, star (f j) * f j := by
  classical
  have hstar (x : ZMod q) : star (e x) = e (-x) := by
    simpa only [Complex.star_def] using
      (AddChar.map_neg_eq_conj e x).symm
  simp only [star_sum, star_mul]
  simp_rw [hstar]
  simp only [neg_neg]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  have hsummand (i k : ZMod q) :
      star (f j) * e (j * k) * (e (-(i * k)) * f i) =
        (star (f j) * f i) * e (k * (j - i)) := by
    calc
      _ = (star (f j) * f i) * (e (j * k) * e (-(i * k))) := by ring
      _ = (star (f j) * f i) * e (j * k + -(i * k)) := by
        rw [AddChar.map_add_eq_mul]
      _ = _ := by
        rw [show j * k + -(i * k) = k * (j - i) by ring]
  simp_rw [hsummand, ← Finset.mul_sum]
  simp_rw [AddChar.sum_mulShift (ψ := e) _ he]
  simp only [sub_eq_zero, ZMod.card, Nat.cast_ite, Nat.cast_zero,
    mul_ite, mul_zero]
  simp [eq_comm]
  ring

private theorem sum_norm_sq_addCharFourier
    {q : ℕ} [NeZero q] (e : AddChar (ZMod q) ℂ)
    (he : e.IsPrimitive) (f : ZMod q → ℂ) :
    (∑ k : ZMod q, ‖∑ j : ZMod q, e (-(j * k)) * f j‖ ^ 2) =
      (q : ℝ) * ∑ j : ZMod q, ‖f j‖ ^ 2 := by
  have h := sum_star_mul_addCharFourier e he f
  rw [Complex.star_def] at h
  simp_rw [← Complex.normSq_eq_conj_mul_self,
    Complex.normSq_eq_norm_sq] at h
  exact_mod_cast h

theorem norm_gaussSum_of_isPrimitive_isPrimitive
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hchi : chi.IsPrimitive) (e : AddChar (ZMod q) ℂ)
    (he : e.IsPrimitive) :
    ‖gaussSum chi e‖ = Real.sqrt q := by
  have hmassNeg :
      (∑ k : ZMod q, ‖chi⁻¹ (-k)‖ ^ 2) = (Nat.totient q : ℝ) := by
    calc
      _ = ∑ k : ZMod q, ‖chi⁻¹ k‖ ^ 2 :=
        Equiv.sum_comp (Equiv.neg (ZMod q)) (fun k ↦ ‖chi⁻¹ k‖ ^ 2)
      _ = (Nat.totient q : ℝ) :=
        BoundedGaps.Maynard.sum_norm_sq_dirichletCharacter chi⁻¹
  have hparseval := sum_norm_sq_addCharFourier e he (f := fun j ↦ chi j)
  have hfourier (k : ZMod q) :
      (∑ j : ZMod q, e (-(j * k)) * chi j) =
        chi⁻¹ (-k) * gaussSum chi e := by
    calc
      _ = gaussSum chi (e.mulShift (-k)) := by
        unfold gaussSum
        apply Finset.sum_congr rfl
        intro j _hj
        simp only [AddChar.mulShift_apply]
        rw [show -(j * k) = j * (-k) by ring]
        ring
      _ = chi⁻¹ (-k) * gaussSum chi e :=
        gaussSum_mulShift_of_isPrimitive e hchi (-k)
  simp_rw [hfourier, norm_mul, mul_pow] at hparseval
  rw [← Finset.sum_mul, hmassNeg,
    BoundedGaps.Maynard.sum_norm_sq_dirichletCharacter chi] at hparseval
  have htotient : (Nat.totient q : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.totient_pos.mpr
      (Nat.pos_of_ne_zero (NeZero.ne q))))
  have hsquare : ‖gaussSum chi e‖ ^ 2 = (q : ℝ) := by
    apply mul_left_cancel₀ htotient
    calc
      (Nat.totient q : ℝ) * ‖gaussSum chi e‖ ^ 2 =
          (q : ℝ) * Nat.totient q := hparseval
      _ = (Nat.totient q : ℝ) * q := by ring
  nlinarith [Real.sq_sqrt (Nat.cast_nonneg q),
    norm_nonneg (gaussSum chi e), Real.sqrt_nonneg (q : ℝ)]

theorem gaussSum_eq_mul_of_crt_factor
    {m n : ℕ} [NeZero m] [NeZero n] (h : m.Coprime n)
    (chi : DirichletCharacter ℂ (m * n))
    (chiL : DirichletCharacter ℂ m) (chiR : DirichletCharacter ℂ n)
    (e : AddChar (ZMod (m * n)) ℂ)
    (hchi : ∀ x : ZMod m, ∀ y : ZMod n,
      chi ((ZMod.chineseRemainder h).symm (x, y)) = chiL x * chiR y) :
    gaussSum chi e =
      gaussSum chiL (crtLeftAddChar h e) *
        gaussSum chiR (crtRightAddChar h e) := by
  classical
  unfold gaussSum
  calc
    (∑ z : ZMod (m * n), chi z * e z) =
        ∑ z : ZMod m × ZMod n,
          chi ((ZMod.chineseRemainder h).symm z) *
            e ((ZMod.chineseRemainder h).symm z) := by
      exact (Equiv.sum_comp (ZMod.chineseRemainder h).symm.toEquiv
        (fun z : ZMod (m * n) ↦ chi z * e z)).symm
    _ = ∑ z : ZMod m × ZMod n,
          (chiL z.1 * crtLeftAddChar h e z.1) *
            (chiR z.2 * crtRightAddChar h e z.2) := by
      apply Fintype.sum_congr
      intro z
      rw [hchi z.1 z.2]
      rw [show (ZMod.chineseRemainder h).symm z =
          (ZMod.chineseRemainder h).symm (z.1, 0) +
            (ZMod.chineseRemainder h).symm (0, z.2) by
        apply (ZMod.chineseRemainder h).injective
        simp]
      rw [AddChar.map_add_eq_mul]
      rw [crtLeftAddChar_apply, crtRightAddChar_apply]
      ring
    _ = (∑ x : ZMod m, chiL x * crtLeftAddChar h e x) *
          ∑ y : ZMod n, chiR y * crtRightAddChar h e y := by
      rw [Fintype.sum_prod_type]
      simp only [Prod.fst, Prod.snd]
      rw [← Fintype.sum_mul_sum]

theorem changeLevel_apply_crt_eq_mul_one
    {m n : ℕ} [NeZero m] [NeZero n] (h : m.Coprime n)
    (psi : DirichletCharacter ℂ m) (x : ZMod m) (y : ZMod n) :
    (DirichletCharacter.changeLevel (Nat.dvd_mul_right m n) psi)
        ((ZMod.chineseRemainder h).symm (x, y)) =
      psi x * (1 : DirichletCharacter ℂ n) y := by
  let z : ZMod (m * n) := (ZMod.chineseRemainder h).symm (x, y)
  have hzpair : (ZMod.chineseRemainder h) z = (x, y) :=
    (ZMod.chineseRemainder h).apply_symm_apply (x, y)
  have hcast : ZMod.cast z = x := by
    have hx := congrArg Prod.fst hzpair
    simpa [ZMod.chineseRemainder, z] using hx
  change (DirichletCharacter.changeLevel (Nat.dvd_mul_right m n) psi) z =
    psi x * (1 : DirichletCharacter ℂ n) y
  by_cases hx : IsUnit x
  · by_cases hy : IsUnit y
    · have hxy : IsUnit (x, y) := Prod.isUnit_iff.mpr ⟨hx, hy⟩
      have hz : IsUnit z :=
        hxy.map (ZMod.chineseRemainder h).symm.toMonoidHom
      have hchange := DirichletCharacter.changeLevel_eq_cast_of_dvd psi
        (Nat.dvd_mul_right m n) hz.unit
      calc
        (DirichletCharacter.changeLevel (Nat.dvd_mul_right m n) psi) z =
            (DirichletCharacter.changeLevel (Nat.dvd_mul_right m n) psi)
              (hz.unit : ZMod (m * n)) :=
          congrArg _ hz.unit_spec.symm
        _ = psi (ZMod.cast (hz.unit : ZMod (m * n))) := hchange
        _ = psi (ZMod.cast z) := by rw [hz.unit_spec]
        _ = psi x := by rw [hcast]
        _ = psi x * (1 : DirichletCharacter ℂ n) y := by
          simp [MulChar.one_apply, hy]
    · have hz : ¬IsUnit z := by
        intro hzu
        have hxy := hzu.map (ZMod.chineseRemainder h).toMonoidHom
        have hzpair' : (ZMod.chineseRemainder h).toMonoidHom z = (x, y) :=
          hzpair
        rw [hzpair'] at hxy
        exact hy (Prod.isUnit_iff.mp hxy).2
      rw [MulChar.map_nonunit _ hz, MulChar.map_nonunit _ hy]
      simp
  · have hz : ¬IsUnit z := by
      intro hzu
      have hxy := hzu.map (ZMod.chineseRemainder h).toMonoidHom
      have hzpair' : (ZMod.chineseRemainder h).toMonoidHom z = (x, y) :=
        hzpair
      rw [hzpair'] at hxy
      exact hx (Prod.isUnit_iff.mp hxy).1
    rw [MulChar.map_nonunit _ hz, MulChar.map_nonunit _ hx]
    simp

theorem gaussSum_one_eq_unitAddCharSum
    {R : Type*} [CommRing R] [Fintype R] [Fintype Rˣ]
    (e : AddChar R ℂ) :
    gaussSum (1 : MulChar R ℂ) e = unitAddCharSum e := by
  classical
  letI : Fintype (IsUnit.submonoid R) := Fintype.ofFinite _
  unfold gaussSum
  calc
    (∑ x : R, (1 : MulChar R ℂ) x * e x) =
        ∑ x ∈ (Finset.univ : Finset R).filter IsUnit, e x := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro x _hx
      by_cases hxu : IsUnit x
      · simp [hxu, MulChar.one_apply]
      · simp [hxu, MulChar.map_nonunit]
    _ = ∑ x : IsUnit.submonoid R, e (x : R) := by
      exact Finset.sum_subtype
        (p := IsUnit) ((Finset.univ : Finset R).filter IsUnit)
        (by simp) (fun x ↦ e x)
    _ = unitAddCharSum e :=
      (unitAddCharSum_eq_sum_isUnitSubtype e).symm

theorem norm_gaussSum_changeLevel_sq_eq
    {m n : ℕ} [NeZero m] [NeZero n] (h : m.Coprime n)
    (hn : Squarefree n) (psi : DirichletCharacter ℂ m)
    (hpsi : psi.IsPrimitive) (e : AddChar (ZMod (m * n)) ℂ)
    (he : e.IsPrimitive) :
    ‖gaussSum (DirichletCharacter.changeLevel
      (Nat.dvd_mul_right m n) psi) e‖ ^ 2 = (m : ℝ) := by
  have hfactor := gaussSum_eq_mul_of_crt_factor h
    (DirichletCharacter.changeLevel (Nat.dvd_mul_right m n) psi)
    psi (1 : DirichletCharacter ℂ n) e
    (changeLevel_apply_crt_eq_mul_one h psi)
  rw [hfactor, gaussSum_one_eq_unitAddCharSum, norm_mul,
    norm_gaussSum_of_isPrimitive_isPrimitive psi hpsi
      (crtLeftAddChar h e) (crtLeftAddChar_isPrimitive h e he),
    norm_unitAddCharSum_eq_one_of_squarefree hn
      (crtRightAddChar h e) (crtRightAddChar_isPrimitive h e he),
    mul_one]
  exact Real.sq_sqrt (Nat.cast_nonneg m)

end Erdos48
