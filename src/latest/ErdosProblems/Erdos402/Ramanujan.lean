import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Data.Nat.Squarefree
import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.GroupWithZero.Units.Equiv
import Mathlib.Tactic

namespace Erdos402.Sieve

noncomputable section

def unitSum {R : Type*} [CommRing R] [Fintype Rˣ] (ψ : AddChar R ℂ) : ℂ :=
  ∑ u : Rˣ, ψ (u : R)

def leftChar {R S : Type*} [CommRing R] [CommRing S]
    (ψ : AddChar (R × S) ℂ) : AddChar R ℂ where
  toFun a := ψ (a, 0)
  map_zero_eq_one' := ψ.map_zero_eq_one
  map_add_eq_mul' a b := by simpa using ψ.map_add_eq_mul (a, 0) (b, 0)

def rightChar {R S : Type*} [CommRing R] [CommRing S]
    (ψ : AddChar (R × S) ℂ) : AddChar S ℂ where
  toFun a := ψ (0, a)
  map_zero_eq_one' := ψ.map_zero_eq_one
  map_add_eq_mul' a b := by simpa using ψ.map_add_eq_mul (0, a) (0, b)

lemma leftChar_primitive {R S : Type*} [CommRing R] [CommRing S]
    {ψ : AddChar (R × S) ℂ} (hψ : ψ.IsPrimitive) : (leftChar ψ).IsPrimitive := by
  intro a ha h
  apply hψ (a := (a, 0)) (by intro he; exact ha (congrArg Prod.fst he))
  ext x
  rcases x with ⟨x, y⟩
  have hx := DFunLike.congr_fun h x
  simpa [AddChar.mulShift_apply, leftChar] using hx

lemma rightChar_primitive {R S : Type*} [CommRing R] [CommRing S]
    {ψ : AddChar (R × S) ℂ} (hψ : ψ.IsPrimitive) : (rightChar ψ).IsPrimitive := by
  intro a ha h
  apply hψ (a := (0, a)) (by intro he; exact ha (congrArg Prod.snd he))
  ext x
  rcases x with ⟨x, y⟩
  have hx := DFunLike.congr_fun h y
  simpa [AddChar.mulShift_apply, rightChar] using hx

lemma primitive_comp_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    {ψ : AddChar S ℂ} (hψ : ψ.IsPrimitive) (e : R ≃+* S) :
    (ψ.compAddMonoidHom e.toAddMonoidHom).IsPrimitive := by
  intro a ha h
  apply hψ (a := e a) (by simpa using ha)
  ext x
  obtain ⟨y, rfl⟩ := e.surjective x
  have hy := DFunLike.congr_fun h y
  simpa [AddChar.mulShift_apply] using hy

lemma unitSum_comp_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    [Fintype Rˣ] [Fintype Sˣ] (ψ : AddChar S ℂ) (e : R ≃+* S) :
    unitSum (ψ.compAddMonoidHom e.toAddMonoidHom) = unitSum ψ := by
  apply Fintype.sum_equiv (Units.mapEquiv e.toMulEquiv).toEquiv
  intro u
  simp [Units.coe_mapEquiv]

lemma unitSum_prod {R S : Type*} [CommRing R] [CommRing S]
    [Fintype Rˣ] [Fintype Sˣ] [Fintype (R × S)ˣ]
    (ψ : AddChar (R × S) ℂ) :
    unitSum ψ = unitSum (leftChar ψ) * unitSum (rightChar ψ) := by
  classical
  calc
    _ = ∑ uv : Rˣ × Sˣ, ψ ((uv.1 : R), (uv.2 : S)) := by
      symm
      apply Fintype.sum_equiv (MulEquiv.prodUnits (M := R) (N := S)).symm.toEquiv
      intro uv
      rfl
    _ = ∑ uv : Rˣ × Sˣ, leftChar ψ (uv.1 : R) * rightChar ψ (uv.2 : S) := by
      apply Finset.sum_congr rfl
      intro uv _
      simpa [leftChar, rightChar] using
        ψ.map_add_eq_mul ((uv.1 : R), 0) (0, (uv.2 : S))
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp_rw [← Finset.mul_sum]
      rw [← Finset.sum_mul]
      rfl

lemma unitSum_field {F : Type*} [Field F] [Finite F] [Fintype Fˣ]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) : unitSum ψ = -1 := by
  classical
  let _ := Fintype.ofFinite F
  have hnontrivial : ψ ≠ 1 := by
    simpa only [AddChar.mulShift_one] using hψ (a := 1) one_ne_zero
  have hfull : ∑ a : F, ψ a = 0 := AddChar.sum_eq_zero_of_ne_one hnontrivial
  have heq : unitSum ψ = ∑ a ∈ (Finset.univ : Finset F).erase 0, ψ a := by
    calc
      _ = ∑ a : {a : F // a ≠ 0}, ψ a := by
        exact Fintype.sum_equiv unitsEquivNeZero _ _ (fun _ ↦ rfl)
      _ = _ := (Finset.sum_subtype _ (by simp) _).symm
  rw [heq]
  have h := Finset.sum_erase_add (s := Finset.univ) (f := fun a ↦ ψ a)
    (by simp : (0 : F) ∈ Finset.univ)
  rw [hfull, ψ.map_zero_eq_one] at h
  linear_combination h

/-- A primitive Ramanujan sum over a squarefree modulus has absolute value
one. The proof factors the character through the Chinese remainder theorem. -/
theorem norm_unitSum_squarefree (q : ℕ) (hsq : Squarefree q) [NeZero q]
    (ψ : AddChar (ZMod q) ℂ) (hψ : ψ.IsPrimitive) : ‖unitSum ψ‖ = 1 := by
  suffices h : ∀ q : ℕ, Squarefree q → ∀ [NeZero q]
      (ψ : AddChar (ZMod q) ℂ), ψ.IsPrimitive → ‖unitSum ψ‖ = 1 from h q hsq ψ hψ
  apply induction_on_primes
  · intro hs
    exact (not_squarefree_zero hs).elim
  · intro hs _ ψ hψ
    have hunit : unitSum ψ = 1 := by
      unfold unitSum
      have hterm : ∀ u : (ZMod 1)ˣ, ψ (u : ZMod 1) = 1 := by
        intro u
        rw [Subsingleton.elim (u : ZMod 1) 0, ψ.map_zero_eq_one]
      simp [hterm]
    rw [hunit, norm_one]
  · intro p a hp ih hs _ ψ hψ
    have hsa : Squarefree a := hs.of_mul_right
    let : Fact p.Prime := ⟨hp⟩
    let : NeZero a := ⟨hsa.ne_zero⟩
    let e := ZMod.chineseRemainder (Nat.coprime_of_squarefree_mul hs)
    let φ := ψ.compAddMonoidHom e.symm.toAddMonoidHom
    have hφ : φ.IsPrimitive := primitive_comp_ringEquiv hψ e.symm
    calc
      _ = ‖unitSum φ‖ := by rw [unitSum_comp_ringEquiv]
      _ = ‖unitSum (leftChar φ)‖ * ‖unitSum (rightChar φ)‖ := by
        rw [unitSum_prod, norm_mul]
      _ = 1 := by
        rw [unitSum_field (leftChar_primitive hφ), norm_neg, norm_one,
          ih hsa (rightChar φ) (rightChar_primitive hφ), mul_one]

lemma sum_units_mul_unit {q : ℕ} [NeZero q] (ψ : AddChar (ZMod q) ℂ)
    (v : (ZMod q)ˣ) : (∑ u : (ZMod q)ˣ, ψ ((u : ZMod q) * v)) = unitSum ψ := by
  apply Fintype.sum_equiv (Equiv.mulRight v)
  intro u
  rfl

lemma sum_units_mul_coprime {q : ℕ} [NeZero q] (ψ : AddChar (ZMod q) ℂ)
    (n : ℕ) (hn : n.Coprime q) :
    (∑ u : (ZMod q)ˣ, ψ ((u : ZMod q) * n)) = unitSum ψ := by
  simpa only [ZMod.coe_unitOfCoprime] using sum_units_mul_unit ψ (ZMod.unitOfCoprime n hn)

end
end Erdos402.Sieve
