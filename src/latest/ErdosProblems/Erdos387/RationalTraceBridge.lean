/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.RationalRootPhase
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.FieldTheory.SeparableDegree

/-!
# Rational root weights and finite-field traces

For a non-pole algebraic element, the logarithmic-derivative phase of its
minimal polynomial is the field trace of the simple-pole phase at that
element.  This is proved by mapping to an algebraic closure, identifying
embeddings of the simple extension with the roots of the minimal polynomial,
and using the root-sum formula from `RationalRootPhase.lean`.
-/

namespace Erdos387

open IntermediateField Polynomial
open scoped BigOperators

namespace RationalWeil

/-- The mapped simple-pole phase is natural under ring maps commuting with
the chosen base-field embeddings. -/
theorem mappedSimplePolePhase_map_ringHom
    {p : ℕ} [NeZero p]
    {E S : Type*} [Field E] [Field S]
    [Algebra (ZMod p) E] [Algebra (ZMod p) S]
    (f : E →+* S)
    (hcomm : ∀ a : ZMod p,
      f (algebraMap (ZMod p) E a) = algebraMap (ZMod p) S a)
    (coeff : ZMod p → ZMod p) (x : E) :
    f (mappedSimplePolePhase coeff x) =
      mappedSimplePolePhase coeff (f x) := by
  classical
  rw [mappedSimplePolePhase, mappedSimplePolePhase, map_sum]
  apply Finset.sum_congr rfl
  intro r hr
  simp only [map_mul, map_inv₀, map_sub]
  rw [hcomm, hcomm]

/-- Algebra-hom version of `mappedSimplePolePhase_map_ringHom`. -/
theorem mappedSimplePolePhase_map
    {p : ℕ} [NeZero p]
    {E S : Type*} [Field E] [Field S]
    [Algebra (ZMod p) E] [Algebra (ZMod p) S]
    (f : E →ₐ[ZMod p] S) (coeff : ZMod p → ZMod p) (x : E) :
    f (mappedSimplePolePhase coeff x) =
      mappedSimplePolePhase coeff (f x) :=
  mappedSimplePolePhase_map_ringHom f.toRingHom f.commutes coeff x

/-- If an algebraic element is not one of the embedded poles, its minimal
polynomial avoids every supported pole. -/
theorem avoidsPoleSupport_minpoly_of_ne_poles
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {L : Type*} [Field L] [Algebra (ZMod p) L]
    (coeff : ZMod p → ZMod p) (x : L) (hx : IsIntegral (ZMod p) x)
    (hnonpole : ∀ r ∈ InverseRational.poleSupport coeff,
      x ≠ algebraMap (ZMod p) L r) :
    AvoidsPoleSupport coeff (minpoly (ZMod p) x) := by
  intro r hr heval
  have hroot : Polynomial.aeval (algebraMap (ZMod p) L r)
      (minpoly (ZMod p) x) = 0 := by
    rw [aeval_algebraMap_apply_eq_algebraMap_eval, heval, map_zero]
  have heq' :
      minpoly (ZMod p) x =
        minpoly (ZMod p) (algebraMap (ZMod p) L r) :=
    minpoly.eq_of_irreducible_of_monic
      (x := algebraMap (ZMod p) L r) (p := minpoly (ZMod p) x)
      (minpoly.irreducible hx) hroot (minpoly.monic hx)
  have heq := heq'.symm
  rw [minpoly.eq_X_sub_C] at heq
  have hxroot := minpoly.aeval (ZMod p) x
  rw [← heq] at hxroot
  have hxr : x = algebraMap (ZMod p) L r := by
    simpa only [aeval_sub, aeval_X, aeval_C, sub_eq_zero] using hxroot
  exact hnonpole r hr hxr

/-- For a separable non-pole algebraic element, the polynomial phase of its
minimal polynomial is the trace of the point phase from the simple extension
it generates. -/
theorem logarithmicDerivativePhase_minpoly_eq_trace_adjoin
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {L : Type*} [Field L] [Algebra (ZMod p) L]
    (coeff : ZMod p → ZMod p) (x : L)
    (hx : IsIntegral (ZMod p) x) (hsep : IsSeparable (ZMod p) x)
    (hnonpole : ∀ r ∈ InverseRational.poleSupport coeff,
      x ≠ algebraMap (ZMod p) L r) :
    logarithmicDerivativePhase coeff (minpoly (ZMod p) x) =
      Algebra.trace (ZMod p) (ZMod p)⟮x⟯
        (mappedSimplePolePhase coeff
          (IntermediateField.AdjoinSimple.gen (ZMod p) x)) := by
  classical
  let E := AlgebraicClosure L
  let : FiniteDimensional (ZMod p) (ZMod p)⟮x⟯ :=
    IntermediateField.adjoin.finiteDimensional hx
  let : Algebra.IsSeparable (ZMod p) (ZMod p)⟮x⟯ :=
    (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable
      (ZMod p) L).2 hsep
  have havoid : AvoidsPoleSupport coeff (minpoly (ZMod p) x) :=
    avoidsPoleSupport_minpoly_of_ne_poles coeff x hx hnonpole
  apply (algebraMap (ZMod p) E).injective
  rw [map_logarithmicDerivativePhase_eq_sum_roots coeff havoid
      (IsAlgClosed.splits _),
    trace_eq_sum_embeddings E]
  have hemb :
      (∑ σ : (ZMod p)⟮x⟯ →ₐ[ZMod p] E,
        σ (mappedSimplePolePhase coeff
          (IntermediateField.AdjoinSimple.gen (ZMod p) x))) =
        ∑ y : {y // y ∈ (minpoly (ZMod p) x).aroots E},
          mappedSimplePolePhase coeff (y : E) := by
    let e := IntermediateField.algHomAdjoinIntegralEquiv
      (ZMod p) (K := E) hx
    apply Fintype.sum_equiv e
    intro σ
    have heval : (e σ : E) =
        σ (IntermediateField.AdjoinSimple.gen (ZMod p) x) := by
      symm
      simpa [e] using
        IntermediateField.algHomAdjoinIntegralEquiv_symm_apply_gen
          (ZMod p) hx (e σ)
    rw [mappedSimplePolePhase_map σ coeff]
    rw [heval]
  rw [hemb]
  rw [Finset.sum_mem_multiset, Finset.sum_eq_multiset_sum,
    Multiset.toFinset_val,
    Multiset.dedup_eq_self.mpr
      (nodup_roots ((Polynomial.separable_map _).mpr hsep))]
  intro y
  rfl

/-- The polynomial Euler weight of a minimal polynomial is the standard
additive character of the corresponding trace. -/
theorem polynomialWeight_minpoly_eq_character_trace_adjoin
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {L : Type*} [Field L] [Algebra (ZMod p) L]
    (coeff : ZMod p → ZMod p) (x : L)
    (hx : IsIntegral (ZMod p) x) (hsep : IsSeparable (ZMod p) x)
    (hnonpole : ∀ r ∈ InverseRational.poleSupport coeff,
      x ≠ algebraMap (ZMod p) L r) :
    polynomialWeight coeff (minpoly (ZMod p) x) =
      ZMod.stdAddChar
        (Algebra.trace (ZMod p) (ZMod p)⟮x⟯
          (mappedSimplePolePhase coeff
            (IntermediateField.AdjoinSimple.gen (ZMod p) x))) := by
  rw [polynomialWeight,
    if_pos (avoidsPoleSupport_minpoly_of_ne_poles coeff x hx hnonpole),
    logarithmicDerivativePhase_minpoly_eq_trace_adjoin
      coeff x hx hsep hnonpole]

/-- In a finite-dimensional ambient extension, the trace character at a
non-pole is the minimal-polynomial weight raised to the relative degree over
the simple subextension. -/
theorem character_trace_mappedSimplePolePhase_eq_polynomialWeight_pow
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {L : Type*} [Field L] [Algebra (ZMod p) L]
    [FiniteDimensional (ZMod p) L]
    (coeff : ZMod p → ZMod p) (x : L)
    (hsep : IsSeparable (ZMod p) x)
    (hnonpole : ∀ r ∈ InverseRational.poleSupport coeff,
      x ≠ algebraMap (ZMod p) L r) :
    ZMod.stdAddChar
        (Algebra.trace (ZMod p) L (mappedSimplePolePhase coeff x)) =
      polynomialWeight coeff (minpoly (ZMod p) x) ^
        Module.finrank (ZMod p)⟮x⟯ L := by
  let y : (ZMod p)⟮x⟯ :=
    mappedSimplePolePhase coeff
      (IntermediateField.AdjoinSimple.gen (ZMod p) x)
  have hpoint : algebraMap (ZMod p)⟮x⟯ L y =
      mappedSimplePolePhase coeff x := by
    dsimp only [y]
    rw [mappedSimplePolePhase_map_ringHom
      (algebraMap (ZMod p)⟮x⟯ L)
      (fun a => IsScalarTower.algebraMap_apply (ZMod p) (ZMod p)⟮x⟯ L a)
      coeff]
    congr 1
  have htrace :
      Algebra.trace (ZMod p) L (algebraMap (ZMod p)⟮x⟯ L y) =
        Module.finrank (ZMod p)⟮x⟯ L •
          Algebra.trace (ZMod p) (ZMod p)⟮x⟯ y := by
    calc
      Algebra.trace (ZMod p) L (algebraMap (ZMod p)⟮x⟯ L y) =
          Algebra.trace (ZMod p) (ZMod p)⟮x⟯
            (Algebra.trace (ZMod p)⟮x⟯ L
              (algebraMap (ZMod p)⟮x⟯ L y)) := by
        rw [Algebra.trace_trace]
      _ = Algebra.trace (ZMod p) (ZMod p)⟮x⟯
          (Module.finrank (ZMod p)⟮x⟯ L • y) := by
        rw [Algebra.trace_algebraMap]
      _ = Module.finrank (ZMod p)⟮x⟯ L •
          Algebra.trace (ZMod p) (ZMod p)⟮x⟯ y := by
        exact map_nsmul (Algebra.trace (ZMod p) (ZMod p)⟮x⟯) _ _
  rw [← hpoint, htrace, AddChar.map_nsmul_eq_pow,
    ← polynomialWeight_minpoly_eq_character_trace_adjoin
      coeff x hsep.isIntegral hsep hnonpole]

/-- Quotient form of the preceding relative-degree identity. -/
theorem character_trace_mappedSimplePolePhase_eq_polynomialWeight_pow_div
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {L : Type*} [Field L] [Algebra (ZMod p) L]
    [FiniteDimensional (ZMod p) L]
    (coeff : ZMod p → ZMod p) (x : L)
    (hsep : IsSeparable (ZMod p) x)
    (hnonpole : ∀ r ∈ InverseRational.poleSupport coeff,
      x ≠ algebraMap (ZMod p) L r) :
    ZMod.stdAddChar
        (Algebra.trace (ZMod p) L (mappedSimplePolePhase coeff x)) =
      polynomialWeight coeff (minpoly (ZMod p) x) ^
        (Module.finrank (ZMod p) L /
          (minpoly (ZMod p) x).natDegree) := by
  have hrelative :
      Module.finrank (ZMod p)⟮x⟯ L =
        Module.finrank (ZMod p) L /
          (minpoly (ZMod p) x).natDegree := by
    rw [← IntermediateField.adjoin.finrank hsep.isIntegral,
      ← Module.finrank_mul_finrank (ZMod p) (ZMod p)⟮x⟯ L,
      Nat.mul_div_cancel_left _ Module.finrank_pos]
  rw [← hrelative]
  exact character_trace_mappedSimplePolePhase_eq_polynomialWeight_pow
    coeff x hsep hnonpole

/-- The extension-point Euler weight, expressed through the minimal
polynomial and the relative degree. -/
noncomputable def extensionPointWeight
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {L : Type*} [Field L] [Algebra (ZMod p) L]
    [FiniteDimensional (ZMod p) L]
    (coeff : ZMod p → ZMod p) (x : L) : ℂ :=
  polynomialWeight coeff (minpoly (ZMod p) x) ^
    (Module.finrank (ZMod p) L / (minpoly (ZMod p) x).natDegree)

/-- At a non-pole in a finite field, the extension-point weight is exactly
the additive character of the traced rational phase. -/
theorem extensionPointWeight_eq_character_trace_of_ne_poles
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {L : Type*} [Field L] [Algebra (ZMod p) L]
    [FiniteDimensional (ZMod p) L]
    (coeff : ZMod p → ZMod p) (x : L)
    (hsep : IsSeparable (ZMod p) x)
    (hnonpole : ∀ r ∈ InverseRational.poleSupport coeff,
      x ≠ algebraMap (ZMod p) L r) :
    extensionPointWeight coeff x =
      ZMod.stdAddChar
        (Algebra.trace (ZMod p) L (mappedSimplePolePhase coeff x)) := by
  exact (character_trace_mappedSimplePolePhase_eq_polynomialWeight_pow_div
    coeff x hsep hnonpole).symm

/-- An extension-field point is one of the embedded base-field poles. -/
def IsMappedPole
    {p : ℕ} [NeZero p]
    {L : Type*} [Field L] [Algebra (ZMod p) L]
    (coeff : ZMod p → ZMod p) (x : L) : Prop :=
  ∃ r ∈ InverseRational.poleSupport coeff,
    x = algebraMap (ZMod p) L r

/-- The traced point weight, extended by zero at every pole. -/
noncomputable def zeroExtendedTraceWeight
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {L : Type*} [Field L] [Algebra (ZMod p) L]
    [FiniteDimensional (ZMod p) L]
    (coeff : ZMod p → ZMod p) (x : L) : ℂ := by
  classical
  exact if IsMappedPole coeff x then 0 else
    ZMod.stdAddChar
      (Algebra.trace (ZMod p) L (mappedSimplePolePhase coeff x))

/-- The minimal-polynomial extension weight vanishes at an embedded pole. -/
theorem extensionPointWeight_eq_zero_of_mappedPole
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {L : Type*} [Field L] [Algebra (ZMod p) L]
    [FiniteDimensional (ZMod p) L]
    (coeff : ZMod p → ZMod p) {x : L}
    (hx : IsMappedPole coeff x) :
    extensionPointWeight coeff x = 0 := by
  obtain ⟨r, hr, rfl⟩ := hx
  rw [extensionPointWeight, minpoly.eq_X_sub_C,
    polynomialWeight_X_sub_C_of_mem coeff hr]
  have hfinrank : 0 < Module.finrank (ZMod p) L := Module.finrank_pos
  rw [natDegree_X_sub_C, Nat.div_one, zero_pow hfinrank.ne']

/-- Over finite fields, the minimal-polynomial weight is exactly the
zero-extended traced point weight at every point. -/
theorem extensionPointWeight_eq_zeroExtendedTraceWeight
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {L : Type*} [Field L] [Algebra (ZMod p) L]
    [Finite L] [FiniteDimensional (ZMod p) L]
    (coeff : ZMod p → ZMod p) (x : L) :
    extensionPointWeight coeff x = zeroExtendedTraceWeight coeff x := by
  classical
  by_cases hx : IsMappedPole coeff x
  · rw [zeroExtendedTraceWeight, if_pos hx,
      extensionPointWeight_eq_zero_of_mappedPole coeff hx]
  · rw [zeroExtendedTraceWeight, if_neg hx]
    apply extensionPointWeight_eq_character_trace_of_ne_poles
      coeff x (Algebra.IsSeparable.isSeparable (ZMod p) x)
    intro r hr hxr
    apply hx
    exact ⟨r, hr, hxr⟩

end RationalWeil

end Erdos387
