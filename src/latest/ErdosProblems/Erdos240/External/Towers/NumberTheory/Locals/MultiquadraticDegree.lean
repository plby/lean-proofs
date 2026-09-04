import ErdosProblems.Erdos240.External.Towers.NumberTheory.Locals.TwoSquareClasses
import ErdosProblems.Erdos240.External.Towers.NumberTheory.Locals.UniversalPadicRoot
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.Set.Insert
import Mathlib.Data.Finset.Max
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Rat.Lemmas

/-!
# Milne, Chapter 7, Exercise 7-6

This file proves the degree-`2^m` assertion by square-class descent through
successive quadratic adjunctions, then proves that the sum of the square
roots is a primitive element whose minimal polynomial has degree `2^m`.
It also proves Milne's bounds on the degrees of the irreducible factors over
the `p`-adic fields: at most eight for `p = 2`, and at most four otherwise.
-/

namespace Towers.NumberTheory.Milne

open Polynomial

noncomputable section

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- Square descent through a quadratic adjunction.  If `q` becomes a square
after adjoining a root of `X² - p`, then either `q` or `q / p` was already a
square in the base field. -/
theorem square_div_algebra
    {F : Type*} [Field F] [CharZero F] {p q : F} (hp : p ≠ 0)
    (hq : IsSquare
      (algebraMap F (QuadraticAlgebra F p 0) q)) :
    IsSquare q ∨ IsSquare (q / p) := by
  obtain ⟨z, hz⟩ := hq
  have him := congrArg QuadraticAlgebra.im hz
  have him' : z.re * z.im + z.im * z.re = 0 := by
    simpa using him.symm
  have htwo : (2 : F) ≠ 0 := by norm_num
  have hprod : z.re * z.im = 0 := by
    have : (2 : F) * (z.re * z.im) = 0 := by
      calc
        (2 : F) * (z.re * z.im) =
            z.re * z.im + z.im * z.re := by ring
        _ = 0 := him'
    exact (mul_eq_zero.mp this).resolve_left htwo
  have hre := congrArg QuadraticAlgebra.re hz
  rcases mul_eq_zero.mp hprod with hre0 | him0
  · right
    refine ⟨z.im, ?_⟩
    have hqeq : q = p * z.im ^ 2 := by
      simpa [hre0, pow_two, mul_assoc] using hre
    rw [hqeq]
    field_simp
  · left
    refine ⟨z.re, ?_⟩
    simpa [him0, pow_two] using hre

/-- A nonempty product of distinct rational primes is not a square in `ℚ`.
This is the square-class independence input in the Kummer-theoretic proof of
Exercise 7-6. -/
theorem distinct_primes_square
    {ι : Type*} (p : ι → ℕ)
    (s : Finset ι) (hs : s.Nonempty)
    (hp : ∀ i ∈ s, Nat.Prime (p i)) (hinj : Set.InjOn p s) :
    ¬IsSquare ((∏ i ∈ s, p i : ℕ) : ℚ) := by
  classical
  rw [Rat.isSquare_natCast_iff]
  have hsquarefree : Squarefree (∏ i ∈ s, p i) := by
    apply Finset.squarefree_prod_of_pairwise_isCoprime
    · intro i hi j hj hij
      apply Nat.coprime_iff_isRelPrime.mp
      exact (Nat.coprime_primes (hp i hi) (hp j hj)).2 fun hpij ↦
        hij (hinj hi hj hpij)
    · intro i hi
      exact (hp i hi).squarefree
  rintro ⟨x, hx⟩
  have hxunit : IsUnit x := by
    apply hsquarefree x
    refine ⟨1, ?_⟩
    simp [hx]
  obtain ⟨i, hi⟩ := hs
  have hpidvd : p i ∣ ∏ j ∈ s, p j := Finset.dvd_prod_of_mem p hi
  have hxone : x = 1 := Nat.isUnit_iff.mp hxunit
  apply (hp i hi).not_dvd_one
  simpa [hx, hxone] using hpidvd

/-- Adjoining an element whose square is already in an intermediate field,
but which is not itself in that field, gives a quadratic extension. -/
theorem adjoin_sq_not
    {E : Type*} [Field E] [Algebra k E]
    (L : IntermediateField k E) (α : E)
    (hsq : α ^ 2 ∈ L) (hα : α ∉ L) :
    Module.finrank L (IntermediateField.adjoin L {α}) = 2 := by
  let a : L := ⟨α ^ 2, hsq⟩
  have hint : IsIntegral L α := by
    refine ⟨X ^ 2 - C a, monic_X_pow_sub_C a (by norm_num), ?_⟩
    simp [a]
  rw [IntermediateField.adjoin.finrank hint]
  have hdvd : minpoly L α ∣ X ^ 2 - C a := by
    apply minpoly.dvd
    simp [a]
  have hle : (minpoly L α).natDegree ≤ 2 := by
    have := natDegree_le_of_dvd hdvd (monic_X_pow_sub_C a (by norm_num)).ne_zero
    simpa using this
  have hpos : 0 < (minpoly L α).natDegree := minpoly.natDegree_pos hint
  have hne : (minpoly L α).natDegree ≠ 1 := by
    intro hone
    apply hα
    have hfin : Module.finrank L (IntermediateField.adjoin L {α}) = 1 := by
      rw [IntermediateField.adjoin.finrank hint, hone]
    have hbot : α ∈ (⊥ : IntermediateField L E) :=
      IntermediateField.finrank_adjoin_simple_eq_one_iff.mp hfin
    rw [IntermediateField.mem_bot] at hbot
    obtain ⟨x, hx⟩ := hbot
    rw [← hx]
    exact x.property
  omega

/-- Adjoining an element whose square is already in an intermediate field
has degree at most two. -/
theorem finrank_adjoin_sq
    {E : Type*} [Field E] [Algebra k E]
    (L : IntermediateField k E) (α : E) (hsq : α ^ 2 ∈ L) :
    Module.finrank L (IntermediateField.adjoin L {α}) ≤ 2 := by
  let a : L := ⟨α ^ 2, hsq⟩
  have hint : IsIntegral L α := by
    refine ⟨X ^ 2 - C a, monic_X_pow_sub_C a (by norm_num), ?_⟩
    simp [a]
  rw [IntermediateField.adjoin.finrank hint]
  have hdvd : minpoly L α ∣ X ^ 2 - C a := by
    apply minpoly.dvd
    simp [a]
  have hle :=
    natDegree_le_of_dvd hdvd (monic_X_pow_sub_C a (by norm_num)).ne_zero
  simpa using hle

noncomputable def quadraticAdjoinSquare
    {E : Type*} [Field E] [Algebra k E]
    (L : IntermediateField k E) (α : E) (p : L)
    (hsq : α ^ 2 = (p : E)) (hα : α ∉ L) :
    QuadraticAlgebra L p 0 ≃ₐ[L] IntermediateField.adjoin L {α} := by
  let A := IntermediateField.adjoin L {α}
  let αA : A := ⟨α, IntermediateField.subset_adjoin L {α} (Set.mem_singleton α)⟩
  letI : Fact (∀ r : L, r ^ 2 ≠ p + 0 * r) := ⟨by
    intro r hr
    apply hα
    have hrE : (r : E) ^ 2 = (p : E) := by
      simpa using congrArg Subtype.val hr
    rcases eq_or_eq_neg_of_sq_eq_sq α (r : E) (hsq.trans hrE.symm) with h | h
    · exact h ▸ r.property
    · rw [h]
      exact L.neg_mem r.property⟩
  let φ : QuadraticAlgebra L p 0 →ₐ[L] A :=
    QuadraticAlgebra.lift ⟨αA, by
      ext
      simpa [αA, Algebra.smul_def, pow_two] using hsq⟩
  have hφinj : Function.Injective φ := φ.injective
  have hint : IsIntegral L α := by
    refine ⟨X ^ 2 - C p, monic_X_pow_sub_C p (by norm_num), ?_⟩
    simp [hsq]
  letI : FiniteDimensional L A := by
    dsimp [A]
    exact IntermediateField.adjoin.finiteDimensional hint
  have hsqmem : α ^ 2 ∈ L := by
    rw [hsq]
    exact p.property
  have hdim :
      Module.finrank L (QuadraticAlgebra L p 0) = Module.finrank L A := by
    rw [QuadraticAlgebra.finrank_eq_two p 0,
      adjoin_sq_not L α hsqmem hα]
  have hφsurj : Function.Surjective φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      hdim (f := φ.toLinearMap)).mp hφinj
  exact AlgEquiv.ofBijective φ ⟨hφinj, hφsurj⟩

/-- Square descent stated for an actual simple quadratic intermediate field. -/
theorem square_or_div
    {E : Type*} [Field E] [Algebra k E] [CharZero k]
    (L : IntermediateField k E) (α : E) (p q : L)
    (hp : p ≠ 0) (hsq : α ^ 2 = (p : E)) (hα : α ∉ L)
    (hq : IsSquare
      (algebraMap L (IntermediateField.adjoin L {α}) q)) :
    IsSquare q ∨ IsSquare (q / p) := by
  let : CharZero L :=
    charZero_of_injective_algebraMap (algebraMap k L).injective
  let e := quadraticAdjoinSquare L α p hsq hα
  have hq' : IsSquare (algebraMap L (QuadraticAlgebra L p 0) q) := by
    simpa [e] using hq.map e.symm
  exact square_div_algebra hp hq'

/-- The tower obtained by adjoining `α 0`, then `α 1`, and so on. -/
def quadraticAdjoinTower
    {E : Type*} [Field E] [Algebra k E] (α : ℕ → E) :
    ℕ → IntermediateField k E
  | 0 => ⊥
  | n + 1 =>
      (IntermediateField.adjoin (quadraticAdjoinTower α n) {α n}).restrictScalars k

/-- The recursive tower is the field generated by the elements with index
strictly below the stage number. -/
theorem quadratic_tower_iio
    {E : Type*} [Field E] [Algebra k E] (α : ℕ → E) (n : ℕ) :
    quadraticAdjoinTower (k := k) α n =
      IntermediateField.adjoin k (α '' Set.Iio n) := by
  induction n with
  | zero => simp [quadraticAdjoinTower]
  | succ n ih =>
      have hiio : Set.Iio (n + 1) = Set.insert n (Set.Iio n) := by
        ext i
        change i < n + 1 ↔ i = n ∨ i < n
        omega
      rw [quadraticAdjoinTower, IntermediateField.restrictScalars_adjoin_eq_sup, ih,
        hiio]
      have himage :
          α '' Set.insert n (Set.Iio n) = Set.insert (α n) (α '' Set.Iio n) :=
        Set.image_insert_eq
      have hinsert :
          Set.insert (α n) (α '' Set.Iio n) = (α '' Set.Iio n) ∪ {α n} := by
        calc
          Set.insert (α n) (α '' Set.Iio n) = {α n} ∪ (α '' Set.Iio n) :=
            Set.insert_eq _ _
          _ = (α '' Set.Iio n) ∪ {α n} := Set.union_comm _ _
      rw [himage, hinsert, IntermediateField.adjoin_union]

/-- Products of square classes not yet adjoined remain nonsquares in the
successive quadratic tower.  This is the Kummer-independence induction used
in Exercise 7-6. -/
theorem square_adjoin_tower
    {E : Type*} [Field E] [Algebra k E] [CharZero k]
    (m : ℕ) (q : ℕ → k) (α : ℕ → E)
    (hsq : ∀ i < m, α i ^ 2 = algebraMap k E (q i))
    (hbase : ∀ s : Finset ℕ, s.Nonempty →
      (∀ i ∈ s, i < m) → ¬IsSquare (∏ i ∈ s, q i)) :
    ∀ n ≤ m, ∀ s : Finset ℕ, s.Nonempty →
      (∀ i ∈ s, n ≤ i ∧ i < m) →
      ¬IsSquare
        (algebraMap k (quadraticAdjoinTower (k := k) α n)
          (∏ i ∈ s, q i)) := by
  intro n
  induction n with
  | zero =>
      intro _ s hs hsupp hSquare
      apply hbase s hs (fun i hi ↦ (hsupp i hi).2)
      have hmapped := hSquare.map (IntermediateField.botEquiv k E)
      change IsSquare ((IntermediateField.botEquiv k E)
        (algebraMap k (⊥ : IntermediateField k E) (∏ i ∈ s, q i))) at hmapped
      rw [IntermediateField.botEquiv_def] at hmapped
      exact hmapped
  | succ n ih =>
      intro hnm s hs hsupp hSquare
      have hnlt : n < m := Nat.lt_of_succ_le hnm
      have hnle : n ≤ m := Nat.le_trans (Nat.le_succ n) hnm
      let L := quadraticAdjoinTower (k := k) α n
      have hαnot : α n ∉ L := by
        intro hαmem
        apply ih hnle {n} (by simp)
          (by
            intro i hi
            simp only [Finset.mem_singleton] at hi
            subst i
            exact ⟨Nat.le_refl n, hnlt⟩)
        refine ⟨⟨α n, hαmem⟩, ?_⟩
        ext
        simpa [pow_two] using (hsq n hnlt).symm
      let pL : L := algebraMap k L (q n)
      let qL : L := algebraMap k L (∏ i ∈ s, q i)
      have hqn0 : q n ≠ 0 := by
        intro hqn
        apply hbase {n} (by simp) (by
          intro i hi
          simp only [Finset.mem_singleton] at hi
          simpa [hi] using hnlt)
        exact ⟨0, by simp [hqn]⟩
      have hpL0 : pL ≠ 0 := by
        intro hpL
        apply hqn0
        apply (algebraMap k L).injective
        simpa [pL] using hpL
      have hsqL : α n ^ 2 = (pL : E) := by
        simpa [pL] using hsq n hnlt
      have hSquare' : IsSquare
          (algebraMap L (IntermediateField.adjoin L {α n}) qL) := by
        obtain ⟨y, hy⟩ := hSquare
        refine ⟨y, ?_⟩
        apply Subtype.ext
        calc
          ↑(algebraMap L (IntermediateField.adjoin L {α n}) qL) = (qL : E) := rfl
          _ = algebraMap k E (∏ i ∈ s, q i) := by
            simp only [qL, IntermediateField.coe_algebraMap_apply]
          _ = ↑(algebraMap k (quadraticAdjoinTower (k := k) α (n + 1))
              (∏ i ∈ s, q i)) :=
            (IntermediateField.coe_algebraMap_apply
              (S := quadraticAdjoinTower (k := k) α (n + 1)) _).symm
          _ = ↑(y * y) := congrArg Subtype.val hy
      rcases square_or_div
          L (α n) pL qL hpL0 hsqL hαnot hSquare' with hq | hqdiv
      · apply ih hnle s hs
          (fun i hi ↦ ⟨Nat.le_trans (Nat.le_succ n) (hsupp i hi).1,
            (hsupp i hi).2⟩)
        simpa [qL] using hq
      · have hns : n ∉ s := by
          intro hmem
          have := (hsupp n hmem).1
          omega
        apply ih hnle (insert n s) (by simp)
          (by
            intro i hi
            simp only [Finset.mem_insert] at hi
            rcases hi with rfl | hi
            · exact ⟨Nat.le_refl _, hnlt⟩
            · exact ⟨Nat.le_trans (Nat.le_succ n) (hsupp i hi).1,
                (hsupp i hi).2⟩)
        obtain ⟨y, hy⟩ := hqdiv
        refine ⟨pL * y, ?_⟩
        rw [Finset.prod_insert hns, map_mul]
        change pL * qL = (pL * y) * (pL * y)
        rw [← div_mul_cancel₀ qL hpL0, hy]
        ring

/-- If every successive element has square in the preceding stage and is not
already in that stage, adjoining the first `n` elements has degree `2^n`. -/
theorem finrank_quadratic_adjoin
    {E : Type*} [Field E] [Algebra k E] (α : ℕ → E)
    (hsq : ∀ n, α n ^ 2 ∈ quadraticAdjoinTower (k := k) α n)
    (hnew : ∀ n, α n ∉ quadraticAdjoinTower (k := k) α n) (n : ℕ) :
    Module.finrank k (quadraticAdjoinTower (k := k) α n) = 2 ^ n := by
  induction n with
  | zero =>
      change Module.finrank k (⊥ : IntermediateField k E) = 1
      exact IntermediateField.finrank_bot
  | succ n ih =>
      let L := quadraticAdjoinTower (k := k) α n
      let A := IntermediateField.adjoin L {α n}
      have hstep : Module.finrank L A = 2 := by
        exact adjoin_sq_not L (α n) (hsq n) (hnew n)
      change Module.finrank k (A.restrictScalars k) = 2 ^ (n + 1)
      calc
        Module.finrank k (A.restrictScalars k) =
            Module.finrank k L * Module.finrank L A := by
          exact (Module.finrank_mul_finrank k L A).symm
        _ = 2 ^ n * 2 := by rw [ih, hstep]
        _ = 2 ^ (n + 1) := by ring

/-- A bounded version of `finrank_quadratic_adjoin`, requiring the square
and novelty hypotheses only at the stages actually used. -/
theorem finrank_quadratic_tower
    {E : Type*} [Field E] [Algebra k E] (α : ℕ → E) (n : ℕ)
    (hsq : ∀ i < n, α i ^ 2 ∈ quadraticAdjoinTower (k := k) α i)
    (hnew : ∀ i < n, α i ∉ quadraticAdjoinTower (k := k) α i) :
    Module.finrank k (quadraticAdjoinTower (k := k) α n) = 2 ^ n := by
  induction n with
  | zero =>
      change Module.finrank k (⊥ : IntermediateField k E) = 1
      exact IntermediateField.finrank_bot
  | succ n ih =>
      let L := quadraticAdjoinTower (k := k) α n
      let A := IntermediateField.adjoin L {α n}
      have hstep : Module.finrank L A = 2 := by
        exact adjoin_sq_not L (α n)
          (hsq n (Nat.lt_succ_self n)) (hnew n (Nat.lt_succ_self n))
      have ih' : Module.finrank k L = 2 ^ n := by
        exact ih
          (fun i hi ↦ hsq i (Nat.lt_trans hi (Nat.lt_succ_self n)))
          (fun i hi ↦ hnew i (Nat.lt_trans hi (Nat.lt_succ_self n)))
      change Module.finrank k (A.restrictScalars k) = 2 ^ (n + 1)
      calc
        Module.finrank k (A.restrictScalars k) =
            Module.finrank k L * Module.finrank L A := by
          exact (Module.finrank_mul_finrank k L A).symm
        _ = 2 ^ n * 2 := by rw [ih', hstep]
        _ = 2 ^ (n + 1) := by ring

/-- If every successive element has square in the preceding stage, adjoining
the first `n` elements has degree at most `2^n`. -/
theorem finrank_adjoin_tower
    {E : Type*} [Field E] [Algebra k E] (α : ℕ → E) (n : ℕ)
    (hsq : ∀ i < n, α i ^ 2 ∈ quadraticAdjoinTower (k := k) α i) :
    Module.finrank k (quadraticAdjoinTower (k := k) α n) ≤ 2 ^ n := by
  induction n with
  | zero =>
      change Module.finrank k (⊥ : IntermediateField k E) ≤ 1
      rw [IntermediateField.finrank_bot]
  | succ n ih =>
      let L := quadraticAdjoinTower (k := k) α n
      let A := IntermediateField.adjoin L {α n}
      have hstep : Module.finrank L A ≤ 2 := by
        exact finrank_adjoin_sq L (α n)
          (hsq n (Nat.lt_succ_self n))
      have ih' : Module.finrank k L ≤ 2 ^ n := by
        exact ih (fun i hi ↦ hsq i (Nat.lt_trans hi (Nat.lt_succ_self n)))
      change Module.finrank k (A.restrictScalars k) ≤ 2 ^ (n + 1)
      calc
        Module.finrank k (A.restrictScalars k) =
            Module.finrank k L * Module.finrank L A := by
          exact (Module.finrank_mul_finrank k L A).symm
        _ ≤ 2 ^ n * 2 := Nat.mul_le_mul ih' hstep
        _ = 2 ^ (n + 1) := by ring

/-- A nonzero square modulo an odd prime lifts to a square in the ring of
`p`-adic integers, with an arbitrary `p`-adic integer as the target. -/
theorem square_z_mod
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (u : ℤ_[p])
    (hu0 : PadicInt.toZMod u ≠ 0)
    (hu : IsSquare (PadicInt.toZMod u)) :
    IsSquare u := by
  obtain ⟨r, hr⟩ := hu
  have hr0 : r ≠ 0 := by
    intro hrzero
    rw [hrzero, zero_mul] at hr
    exact hu0 hr
  let a : ℕ := r.val
  have ha0 : (a : ZMod p) ≠ 0 := by
    simpa [a, ZMod.natCast_zmod_val] using hr0
  have hres : ((a : ZMod p) ^ 2) = PadicInt.toZMod u := by
    simpa [a, ZMod.natCast_zmod_val, pow_two] using hr.symm
  let F : ℤ_[p][X] := X ^ 2 - C u
  have hFa : F.aeval (a : ℤ_[p]) = (a : ℤ_[p]) ^ 2 - u := by
    simp [F]
  have hFda : F.derivative.aeval (a : ℤ_[p]) = 2 * a := by
    norm_num [F, aeval_def]
  have hderiv : ‖F.derivative.aeval (a : ℤ_[p])‖ = 1 := by
    rw [hFda]
    rw [← Nat.cast_ofNat, ← Nat.cast_mul,
      PadicInt.norm_natCast_eq_one_iff,
      (Fact.out : p.Prime).coprime_iff_not_dvd]
    intro hdvd
    rcases (Fact.out : p.Prime).dvd_mul.mp hdvd with hpTwo | hpA
    · exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) (by decide)).mp hpTwo)
    · exact ha0 ((ZMod.natCast_eq_zero_iff a p).mpr hpA)
  have hnewton :
      ‖F.aeval (a : ℤ_[p])‖ < ‖F.derivative.aeval (a : ℤ_[p])‖ ^ 2 := by
    rw [hFa, hderiv, one_pow]
    rw [PadicInt.norm_lt_one_iff_dvd]
    rw [← Ideal.mem_span_singleton, ← PadicInt.maximalIdeal_eq_span_p,
      ← PadicInt.ker_toZMod, RingHom.mem_ker]
    simp [hres]
  obtain ⟨y, hy, -, -, -⟩ := padic_newton_root F (a : ℤ_[p]) hnewton
  refine ⟨y, ?_⟩
  have : y ^ 2 - u = 0 := by simpa [F] using hy
  simpa [pow_two] using (sub_eq_zero.mp this).symm

/-- For an odd prime `p`, every `p`-adic unit has square class represented
by either `1` or a chosen nonsquare residue. -/
theorem padic_odd_square
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (a₀ : ZMod p) (ha₀ : ¬IsSquare a₀) (u : ℤ_[p]ˣ) :
    ∃ b : Bool, ∃ y : ℚ_[p],
      (u : ℚ_[p]) = (if b then (a₀.val : ℚ_[p]) else 1) * y ^ 2 := by
  have ha₀0 : a₀ ≠ 0 := by
    intro h
    apply ha₀
    rw [h]
    exact IsSquare.zero
  let r : (ZMod p)ˣ := Units.map (PadicInt.toZMod (p := p)) u
  have hr0 : PadicInt.toZMod (u : ℤ_[p]) ≠ 0 := by
    change (r : ZMod p) ≠ 0
    exact r.ne_zero
  by_cases hrsq : IsSquare (PadicInt.toZMod (u : ℤ_[p]))
  · obtain ⟨y, hy⟩ :=
      square_z_mod p hp2 (u : ℤ_[p]) hr0 hrsq
    refine ⟨false, (y : ℚ_[p]), ?_⟩
    simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
    simpa [pow_two] using congrArg (fun z : ℤ_[p] ↦ (z : ℚ_[p])) hy
  · have hprodSq :
        IsSquare (PadicInt.toZMod (u : ℤ_[p]) * a₀) := by
      apply (quadraticChar_one_iff_isSquare (mul_ne_zero hr0 ha₀0)).mp
      rw [map_mul,
        quadraticChar_neg_one_iff_not_isSquare.mpr hrsq,
        quadraticChar_neg_one_iff_not_isSquare.mpr ha₀]
      norm_num
    have haCast :
        PadicInt.toZMod ((a₀.val : ℕ) : ℤ_[p]) = a₀ := by
      simp
    let v : ℤ_[p] := (u : ℤ_[p]) * (a₀.val : ℤ_[p])
    have hv0 : PadicInt.toZMod v ≠ 0 := by
      simp only [v, map_mul, haCast]
      exact mul_ne_zero hr0 ha₀0
    have hvsq : IsSquare (PadicInt.toZMod v) := by
      simpa [v, haCast] using hprodSq
    obtain ⟨y, hy⟩ :=
      square_z_mod p hp2 v hv0 hvsq
    have haNat0 : a₀.val ≠ 0 := by
      intro h
      apply ha₀0
      rw [← ZMod.natCast_zmod_val a₀, h]
      simp
    have haq0 : (a₀.val : ℚ_[p]) ≠ 0 := by exact_mod_cast haNat0
    refine ⟨true, (y : ℚ_[p]) / (a₀.val : ℚ_[p]), ?_⟩
    simp only [↓reduceIte]
    have hyq :
        (u : ℚ_[p]) * (a₀.val : ℚ_[p]) = (y : ℚ_[p]) * y := by
      exact congrArg (fun z : ℤ_[p] ↦ (z : ℚ_[p])) hy
    calc
      (u : ℚ_[p]) = ((u : ℚ_[p]) * a₀.val) / a₀.val := by field_simp
      _ = ((y : ℚ_[p]) * y) / a₀.val := by rw [hyq]
      _ = (a₀.val : ℚ_[p]) * ((y : ℚ_[p]) / a₀.val) ^ 2 := by
        field_simp

/-- For an odd prime `p`, every nonzero `p`-adic number has square class
represented by one of `1`, a chosen nonsquare unit, `p`, or their product. -/
theorem odd_square_class
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (a₀ : ZMod p) (ha₀ : ¬IsSquare a₀)
    (x : ℚ_[p]) (hx : x ≠ 0) :
    ∃ bp bu : Bool, ∃ y : ℚ_[p],
      x = (if bp then (p : ℚ_[p]) else 1) *
        (if bu then (a₀.val : ℚ_[p]) else 1) * y ^ 2 := by
  let v : ℤ := x.valuation
  let uq : ℚ_[p] := x * (p : ℚ_[p]) ^ (-v)
  have hp0 : (p : ℚ_[p]) ≠ 0 := by
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  have huq0 : uq ≠ 0 := mul_ne_zero hx (zpow_ne_zero _ hp0)
  have huqVal : uq.valuation = 0 := by
    have hvalP : Padic.valuation (p : ℚ_[p]) = 1 := by
      change Padic.valuation (((p : ℕ) : ℚ_[p])) = 1
      exact Padic.valuation_p
    rw [Padic.valuation_mul hx (zpow_ne_zero _ hp0),
      Padic.valuation_zpow, hvalP]
    dsimp [v]
    ring
  have huqNorm : ‖uq‖ = 1 := by
    rw [Padic.norm_eq_zpow_neg_valuation huq0, huqVal]
    simp
  let u : ℤ_[p]ˣ := PadicInt.mkUnits huqNorm
  obtain ⟨bu, y, hy⟩ := padic_odd_square p hp2 a₀ ha₀ u
  have huq : (u : ℚ_[p]) = uq := PadicInt.mkUnits_eq huqNorm
  have hxDecomp : x = uq * (p : ℚ_[p]) ^ v := by
    dsimp [uq]
    rw [mul_assoc, ← zpow_add₀ hp0, neg_add_cancel, zpow_zero, mul_one]
  obtain ⟨k, hk | hk⟩ := Int.even_or_odd' v
  · refine ⟨false, bu, y * (p : ℚ_[p]) ^ k, ?_⟩
    have hpow :
        (p : ℚ_[p]) ^ (2 * k) = ((p : ℚ_[p]) ^ k) ^ 2 := by
      rw [show 2 * k = k * 2 by ring, zpow_mul, zpow_ofNat]
    rw [hxDecomp, ← huq, hy, hk, hpow]
    simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
    ring
  · refine ⟨true, bu, y * (p : ℚ_[p]) ^ k, ?_⟩
    have hpow :
        (p : ℚ_[p]) ^ (2 * k) = ((p : ℚ_[p]) ^ k) ^ 2 := by
      rw [show 2 * k = k * 2 by ring, zpow_mul, zpow_ofNat]
    rw [hxDecomp, ← huq, hy, hk, zpow_add₀ hp0, hpow, zpow_one]
    simp only [↓reduceIte]
    ring

/-- If the square classes of the radicands are generated by `r` given
classes, then adjoining all their chosen square roots has degree at most
`2^r`. -/
theorem square_roots_generators
    {E : Type*} [Field E] [Algebra k E] [CharZero k]
    (m r : ℕ) (q b : ℕ → k) (α β : ℕ → E)
    (hα : ∀ i < m, α i ^ 2 = algebraMap k E (q i))
    (hβ : ∀ j < r, β j ^ 2 = algebraMap k E (b j))
    (hclass : ∀ i < m, ∃ t : Finset ℕ,
      (∀ j ∈ t, j < r) ∧
        ∃ y : k, q i = y ^ 2 * ∏ j ∈ t, b j) :
    Module.finrank k (IntermediateField.adjoin k (α '' Set.Iio m)) ≤
      2 ^ r := by
  let B := IntermediateField.adjoin k (β '' Set.Iio r)
  have hαmem : ∀ i < m, α i ∈ B := by
    intro i hi
    obtain ⟨t, ht, y, hq⟩ := hclass i hi
    let z : E := algebraMap k E y * ∏ j ∈ t, β j
    have hzmem : z ∈ B := by
      apply B.mul_mem (B.algebraMap_mem y)
      apply B.prod_mem
      intro j hj
      exact IntermediateField.subset_adjoin k (β '' Set.Iio r)
        ⟨j, ht j hj, rfl⟩
    have hzsq : α i ^ 2 = z ^ 2 := by
      calc
        α i ^ 2 = algebraMap k E (q i) := hα i hi
        _ = algebraMap k E (y ^ 2 * ∏ j ∈ t, b j) := by rw [hq]
        _ = (algebraMap k E y) ^ 2 *
            ∏ j ∈ t, algebraMap k E (b j) := by
          rw [map_mul, map_pow, map_prod]
        _ = (algebraMap k E y) ^ 2 * ∏ j ∈ t, β j ^ 2 := by
          congr 1
          apply Finset.prod_congr rfl
          intro j hj
          exact (hβ j (ht j hj)).symm
        _ = z ^ 2 := by
          rw [mul_pow, Finset.prod_pow]
    rcases eq_or_eq_neg_of_sq_eq_sq (α i) z hzsq with hiz | hiz
    · rwa [hiz]
    · rw [hiz]
      exact B.neg_mem hzmem
  have hadjoin : IntermediateField.adjoin k (α '' Set.Iio m) ≤ B := by
    rw [IntermediateField.adjoin_le_iff]
    intro x hx
    obtain ⟨i, hi, rfl⟩ := hx
    exact hαmem i hi
  let : Fintype (β '' Set.Iio r) :=
    ((Set.finite_Iio r).image β).fintype
  let : FiniteDimensional k B := by
    dsimp [B]
    apply IntermediateField.finiteDimensional_adjoin
    intro x hx
    obtain ⟨j, hj, rfl⟩ := hx
    refine ⟨X ^ 2 - C (b j), monic_X_pow_sub_C (b j) (by norm_num), ?_⟩
    simp [hβ j hj]
  have hmono :
      Module.finrank k (IntermediateField.adjoin k (α '' Set.Iio m)) ≤
        Module.finrank k B :=
    by
      simpa using Submodule.finrank_mono
        (s := (IntermediateField.adjoin k (α '' Set.Iio m)).toSubmodule)
        (t := B.toSubmodule) hadjoin
  apply hmono.trans
  change Module.finrank k (IntermediateField.adjoin k (β '' Set.Iio r)) ≤
    2 ^ r
  rw [← quadratic_tower_iio]
  apply finrank_adjoin_tower β r
  intro j hj
  rw [hβ j hj]
  exact (quadraticAdjoinTower (k := k) β j).algebraMap_mem (b j)

/-- If the radicand square classes are generated by `r` classes in the base
field, then adjoining their square roots has degree at most `2^r`.  Roots of
the class generators are supplied in an algebraic closure. -/
theorem adjoin_square_roots
    {E : Type*} [Field E] [Algebra k E] [CharZero k]
    (m r : ℕ) (q b : ℕ → k) (α : ℕ → E)
    (hα : ∀ i < m, α i ^ 2 = algebraMap k E (q i))
    (hclass : ∀ i < m, ∃ t : Finset ℕ,
      (∀ j ∈ t, j < r) ∧
        ∃ y : k, q i = y ^ 2 * ∏ j ∈ t, b j) :
    Module.finrank k (IntermediateField.adjoin k (α '' Set.Iio m)) ≤
      2 ^ r := by
  let A := IntermediateField.adjoin k (α '' Set.Iio m)
  let : Fintype (α '' Set.Iio m) :=
    ((Set.finite_Iio m).image α).fintype
  let : FiniteDimensional k A := by
    dsimp [A]
    apply IntermediateField.finiteDimensional_adjoin
    intro x hx
    obtain ⟨i, hi, rfl⟩ := hx
    refine ⟨X ^ 2 - C (q i), monic_X_pow_sub_C (q i) (by norm_num), ?_⟩
    simp [hα i hi]
  let Ω := AlgebraicClosure k
  let ι : A →ₐ[k] Ω := IsAlgClosed.lift
  let a : ℕ → A := fun i => if hi : i < m then
    ⟨α i, IntermediateField.subset_adjoin k (α '' Set.Iio m)
      ⟨i, hi, rfl⟩⟩ else 0
  have ha_sq : ∀ i < m, a i ^ 2 = algebraMap k A (q i) := by
    intro i hi
    apply Subtype.ext
    simp [a, hi, hα i hi]
  have hgenA : IntermediateField.adjoin k (a '' Set.Iio m) = ⊤ := by
    apply IntermediateField.map_injective A.val
    rw [IntermediateField.adjoin_map, ← AlgHom.fieldRange_eq_map,
      IntermediateField.fieldRange_val]
    change IntermediateField.adjoin k
      (Subtype.val '' (a '' Set.Iio m)) = A
    congr 1
    ext x
    constructor
    · rintro ⟨y, ⟨i, hi, rfl⟩, rfl⟩
      change i < m at hi
      exact ⟨i, hi, by simp [a, hi]⟩
    · rintro ⟨i, hi, rfl⟩
      change i < m at hi
      exact ⟨a i, ⟨i, hi, rfl⟩, by simp [a, hi]⟩
  let αΩ : ℕ → Ω := fun i => ι (a i)
  have hαΩ : ∀ i < m, αΩ i ^ 2 = algebraMap k Ω (q i) := by
    intro i hi
    simpa [αΩ] using congrArg ι (ha_sq i hi)
  have hgenΩ :
      IntermediateField.adjoin k (αΩ '' Set.Iio m) = ι.fieldRange := by
    calc
      IntermediateField.adjoin k (αΩ '' Set.Iio m) =
          (IntermediateField.adjoin k (a '' Set.Iio m)).map ι := by
        rw [IntermediateField.adjoin_map]
        congr 1
        ext x
        simp only [Set.mem_image]
        constructor
        · rintro ⟨i, hi, rfl⟩
          exact ⟨a i, ⟨i, hi, rfl⟩, rfl⟩
        · rintro ⟨y, ⟨i, hi, rfl⟩, rfl⟩
          exact ⟨i, hi, rfl⟩
      _ = (⊤ : IntermediateField k A).map ι := by rw [hgenA]
      _ = ι.fieldRange := by rw [AlgHom.fieldRange_eq_map]
  choose β hβ using fun j =>
    IsAlgClosed.exists_pow_nat_eq (algebraMap k Ω (b j))
      (by norm_num : 0 < 2)
  have hbound :=
    square_roots_generators
      m r q b αΩ β hαΩ (fun j _ => hβ j) hclass
  rw [hgenΩ] at hbound
  let e : A ≃ₐ[k] ι.fieldRange :=
    IntermediateField.topEquiv.symm.trans
      ((IntermediateField.equivMap (⊤ : IntermediateField k A) ι).trans
        (IntermediateField.equivOfEq (AlgHom.fieldRange_eq_map ι).symm))
  have hfin : Module.finrank k A = Module.finrank k ι.fieldRange :=
    e.toLinearEquiv.finrank_eq
  change Module.finrank k A ≤ 2 ^ r
  rw [hfin]
  exact hbound

/-- A field generated over `ℚ_[2]` by square roots of rational primes has
degree at most eight.  The proof uses the three square-class generators
`-1`, `5`, and `2` from Exercise 7-5. -/
theorem square_roots_eight
    {E : Type*} [Field E] [Algebra ℚ_[2] E]
    (m : ℕ) (p : ℕ → ℕ) (α : ℕ → E)
    (hp : ∀ i < m, Nat.Prime (p i))
    (hα : ∀ i < m, α i ^ 2 = algebraMap ℚ_[2] E (p i : ℚ_[2])) :
    Module.finrank ℚ_[2]
      (IntermediateField.adjoin ℚ_[2] (α '' Set.Iio m)) ≤ 8 := by
  let b : ℕ → ℚ_[2] := fun j =>
    if j = 0 then -1 else if j = 1 then 5 else 2
  have hclass : ∀ i < m, ∃ t : Finset ℕ,
      (∀ j ∈ t, j < 3) ∧
        ∃ y : ℚ_[2], (p i : ℚ_[2]) = y ^ 2 * ∏ j ∈ t, b j := by
    intro i hi
    have hp0 : (p i : ℚ_[2]) ≠ 0 := by
      exact_mod_cast (hp i hi).ne_zero
    obtain ⟨c, hc, y, hy⟩ := padic_two_square (p i : ℚ_[2]) hp0
    simp only [padicSquareRepresentatives, Finset.mem_insert,
      Finset.mem_singleton] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · refine ⟨∅, by simp, y, ?_⟩
      simpa [b, mul_comm] using hy
    · refine ⟨{0}, by simp, y, ?_⟩
      simpa [b, mul_comm] using hy
    · refine ⟨{1}, by simp, y, ?_⟩
      simpa [b, mul_comm] using hy
    · refine ⟨{0, 1}, by simp, y, ?_⟩
      simpa [b, mul_comm] using hy
    · refine ⟨{2}, by simp, y, ?_⟩
      simpa [b, mul_comm] using hy
    · refine ⟨{0, 2}, by simp, y, ?_⟩
      simpa [b, mul_comm] using hy
    · refine ⟨{1, 2}, by simp, y, ?_⟩
      have hten : (2 : ℚ_[2]) * 5 = 10 := by norm_num
      simpa [b, hten, mul_comm] using hy
    · refine ⟨{0, 1, 2}, by simp, y, ?_⟩
      have hten : (2 : ℚ_[2]) * 5 = 10 := by norm_num
      simpa [b, hten, mul_comm] using hy
  simpa using
    (adjoin_square_roots
      m 3 (fun i => (p i : ℚ_[2])) b α hα hclass)

/-- For an odd prime `p`, one nonsquare unit together with `p` generates the
square classes of all rational primes in `ℚ_[p]`. -/
theorem odd_square_generator
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    ∃ u : ℕ, p.Coprime u ∧ ¬IsSquare (u : ZMod p) ∧
      ∀ q : ℕ, q.Prime →
        IsSquare ((q : ℚ_[p]) / (p : ℚ_[p])) ∨
          IsSquare (q : ℚ_[p]) ∨
            IsSquare ((q : ℚ_[p]) / (u : ℚ_[p])) := by
  have hchar : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    exact hp2
  obtain ⟨a₀, ha₀⟩ := FiniteField.exists_nonsquare hchar
  have ha₀0 : a₀ ≠ 0 := by
    intro h
    apply ha₀
    rw [h]
    exact IsSquare.zero
  let u : ℕ := a₀.val
  have huCast : (u : ZMod p) = a₀ := by
    simp [u]
  have hucoprime : p.Coprime u := by
    rw [(Fact.out : p.Prime).coprime_iff_not_dvd]
    intro hdvd
    apply ha₀0
    rw [← huCast]
    exact (ZMod.natCast_eq_zero_iff u p).mpr hdvd
  have huNat0 : u ≠ 0 := by
    intro hu
    apply ha₀0
    rw [← huCast, hu]
    simp
  have huq0 : (u : ℚ_[p]) ≠ 0 := by exact_mod_cast huNat0
  refine ⟨u, hucoprime, ?_, ?_⟩
  · simpa [huCast] using ha₀
  · intro q hq
    by_cases hqp : q = p
    · subst q
      left
      refine ⟨1, ?_⟩
      simp
    · have hpq : p.Coprime q :=
        (Nat.coprime_primes (Fact.out : p.Prime) hq).2 (fun hpq ↦ hqp hpq.symm)
      have hqunit : IsUnit (q : ℤ_[p]) := by
        rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
        exact hpq
      let qu : ℤ_[p]ˣ := hqunit.unit
      have hqu : (qu : ℤ_[p]) = (q : ℤ_[p]) := hqunit.unit_spec
      obtain ⟨b, y, hy⟩ :=
        padic_odd_square p hp2 a₀ ha₀ qu
      have hquq : (qu : ℚ_[p]) = (q : ℚ_[p]) := by
        simpa using congrArg (fun z : ℤ_[p] => (z : ℚ_[p])) hqu
      have hyq :
          (q : ℚ_[p]) = (if b then (u : ℚ_[p]) else 1) * y ^ 2 := by
        rw [← hquq, hy]
      cases b with
      | false =>
          right
          left
          refine ⟨y, ?_⟩
          simpa [pow_two] using hyq
      | true =>
          right
          right
          refine ⟨y, ?_⟩
          have hdiv := congrArg (fun z : ℚ_[p] => z / (u : ℚ_[p])) hyq
          simpa [huq0, pow_two] using hdiv

/-- Over `ℚ_[p]` for odd `p`, a field generated by square roots of rational
primes has degree at most four. -/
theorem finrank_square_roots
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    {E : Type*} [Field E] [Algebra ℚ_[p] E]
    (m : ℕ) (q : ℕ → ℕ) (α : ℕ → E)
    (hq : ∀ i < m, Nat.Prime (q i))
    (hα : ∀ i < m, α i ^ 2 = algebraMap ℚ_[p] E (q i : ℚ_[p])) :
    Module.finrank ℚ_[p]
      (IntermediateField.adjoin ℚ_[p] (α '' Set.Iio m)) ≤ 4 := by
  obtain ⟨u, hucoprime, -, hclasses⟩ :=
    odd_square_generator p hp2
  have huNat0 : u ≠ 0 := by
    intro hu
    subst u
    have hpone : p = 1 := by simpa using hucoprime
    exact (Fact.out : p.Prime).ne_one hpone
  have hu0 : (u : ℚ_[p]) ≠ 0 := by exact_mod_cast huNat0
  have hp0 : (p : ℚ_[p]) ≠ 0 := by
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  let b : ℕ → ℚ_[p] := fun j => if j = 0 then (u : ℚ_[p]) else p
  have hclass : ∀ i < m, ∃ t : Finset ℕ,
      (∀ j ∈ t, j < 2) ∧
        ∃ y : ℚ_[p], (q i : ℚ_[p]) = y ^ 2 * ∏ j ∈ t, b j := by
    intro i hi
    rcases hclasses (q i) (hq i hi) with hqp | hsq | hqu
    · obtain ⟨y, hy⟩ := hqp
      refine ⟨{1}, by simp, y, ?_⟩
      calc
        (q i : ℚ_[p]) = ((q i : ℚ_[p]) / p) * p := by field_simp
        _ = (y * y) * p := by rw [hy]
        _ = y ^ 2 * ∏ j ∈ ({1} : Finset ℕ), b j := by simp [b, pow_two]
    · obtain ⟨y, hy⟩ := hsq
      refine ⟨∅, by simp, y, ?_⟩
      simpa [b, pow_two] using hy
    · obtain ⟨y, hy⟩ := hqu
      refine ⟨{0}, by simp, y, ?_⟩
      calc
        (q i : ℚ_[p]) = ((q i : ℚ_[p]) / u) * u := by field_simp
        _ = (y * y) * u := by rw [hy]
        _ = y ^ 2 * ∏ j ∈ ({0} : Finset ℕ), b j := by simp [b, pow_two]
  simpa using
    (adjoin_square_roots
      m 2 (fun i => (q i : ℚ_[p])) b α hα hclass)

/-- Independent square classes give the expected degree for the field
generated by their chosen square roots. -/
theorem tower_independent_classes
    {E : Type*} [Field E] [Algebra k E] [CharZero k]
    (m : ℕ) (q : ℕ → k) (α : ℕ → E)
    (hsq : ∀ i < m, α i ^ 2 = algebraMap k E (q i))
    (hbase : ∀ s : Finset ℕ, s.Nonempty →
      (∀ i ∈ s, i < m) → ¬IsSquare (∏ i ∈ s, q i)) :
    Module.finrank k (quadraticAdjoinTower (k := k) α m) = 2 ^ m := by
  apply finrank_quadratic_tower α m
  · intro i hi
    rw [hsq i hi]
    exact (quadraticAdjoinTower (k := k) α i).algebraMap_mem (q i)
  · intro i hi hmem
    have hnonsquare := square_adjoin_tower
      m q α hsq hbase i (Nat.le_of_lt hi) {i} (by simp)
      (by
        intro j hj
        simp only [Finset.mem_singleton] at hj
        subst j
        exact ⟨Nat.le_refl i, hi⟩)
    apply hnonsquare
    refine ⟨⟨α i, hmem⟩, ?_⟩
    ext
    simpa [pow_two] using (hsq i hi).symm

/-- The same independent-square-class degree formula, stated for the field
generated by the first `m` roots. -/
theorem iio_square_classes
    {E : Type*} [Field E] [Algebra k E] [CharZero k]
    (m : ℕ) (q : ℕ → k) (α : ℕ → E)
    (hsq : ∀ i < m, α i ^ 2 = algebraMap k E (q i))
    (hbase : ∀ s : Finset ℕ, s.Nonempty →
      (∀ i ∈ s, i < m) → ¬IsSquare (∏ i ∈ s, q i)) :
    Module.finrank k (IntermediateField.adjoin k (α '' Set.Iio m)) = 2 ^ m := by
  rw [← quadratic_tower_iio]
  exact tower_independent_classes
    m q α hsq hbase

/-- Independent square classes ensure that each chosen square root is absent
from the field generated by its predecessors. -/
theorem iio_independent_classes
    {E : Type*} [Field E] [Algebra k E] [CharZero k]
    (m : ℕ) (q : ℕ → k) (α : ℕ → E)
    (hsq : ∀ i < m, α i ^ 2 = algebraMap k E (q i))
    (hbase : ∀ s : Finset ℕ, s.Nonempty →
      (∀ i ∈ s, i < m) → ¬IsSquare (∏ i ∈ s, q i)) :
    ∀ i < m, α i ∉ IntermediateField.adjoin k (α '' Set.Iio i) := by
  intro i hi hmem
  rw [← quadratic_tower_iio] at hmem
  have hnonsquare := square_adjoin_tower
    m q α hsq hbase i (Nat.le_of_lt hi) {i} (by simp)
    (by
      intro j hj
      simp only [Finset.mem_singleton] at hj
      subst j
      exact ⟨Nat.le_refl i, hi⟩)
  apply hnonsquare
  refine ⟨⟨α i, hmem⟩, ?_⟩
  ext
  simpa [pow_two] using (hsq i hi).symm

/-- Milne, Exercise 7-6, degree assertion: adjoining square roots of `m`
distinct rational primes gives an extension of degree `2^m`. -/
theorem distinct_square_roots
    {E : Type*} [Field E] [Algebra ℚ E]
    (m : ℕ) (p : ℕ → ℕ) (α : ℕ → E)
    (hp : ∀ i < m, Nat.Prime (p i))
    (hinj : Set.InjOn p (Set.Iio m))
    (hsq : ∀ i < m, α i ^ 2 = algebraMap ℚ E (p i : ℚ)) :
    Module.finrank ℚ (IntermediateField.adjoin ℚ (α '' Set.Iio m)) = 2 ^ m := by
  apply iio_square_classes
    m (fun i ↦ (p i : ℚ)) α hsq
  intro s hs hsupp
  have h := distinct_primes_square p s hs
    (fun i hi ↦ hp i (hsupp i hi))
    (fun i hi j hj hij ↦ hinj (hsupp i hi) (hsupp j hj) hij)
  simpa using h

/-- For distinct rational primes, each chosen square root is absent from the
field generated by the preceding square roots. -/
theorem distinct_adjoin_prior
    {E : Type*} [Field E] [Algebra ℚ E]
    (m : ℕ) (p : ℕ → ℕ) (α : ℕ → E)
    (hp : ∀ i < m, Nat.Prime (p i))
    (hinj : Set.InjOn p (Set.Iio m))
    (hsq : ∀ i < m, α i ^ 2 = algebraMap ℚ E (p i : ℚ)) :
    ∀ i < m, α i ∉ IntermediateField.adjoin ℚ (α '' Set.Iio i) := by
  apply iio_independent_classes
    m (fun i ↦ (p i : ℚ)) α hsq
  intro s hs hsupp
  have h := distinct_primes_square p s hs
    (fun i hi ↦ hp i (hsupp i hi))
    (fun i hi j hj hij ↦ hinj (hsupp i hi) (hsupp j hj) hij)
  simpa using h

/-- At every stage of an independent quadratic-adjoin tower, the next
chosen square root is genuinely new. -/
theorem square_quadratic_tower
    {E : Type*} [Field E] [Algebra k E] [CharZero k]
    (m : ℕ) (q : ℕ → k) (α : ℕ → E)
    (hsq : ∀ i < m, α i ^ 2 = algebraMap k E (q i))
    (hbase : ∀ s : Finset ℕ, s.Nonempty →
      (∀ i ∈ s, i < m) → ¬IsSquare (∏ i ∈ s, q i))
    {i : ℕ} (hi : i < m) :
    α i ∉ quadraticAdjoinTower (k := k) α i := by
  intro hmem
  have hnonsquare := square_adjoin_tower
    m q α hsq hbase i (Nat.le_of_lt hi) {i} (by simp)
    (by
      intro j hj
      simp only [Finset.mem_singleton] at hj
      subst j
      exact ⟨Nat.le_refl i, hi⟩)
  apply hnonsquare
  refine ⟨⟨α i, hmem⟩, ?_⟩
  ext
  simpa [pow_two] using (hsq i hi).symm

/-- A nonempty sum of independent chosen square roots cannot vanish.  Taking
the largest index in the sum would otherwise put that root in the field
generated by the earlier roots. -/
theorem roots_independent_classes
    {E : Type*} [Field E] [Algebra k E] [CharZero k]
    (m : ℕ) (q : ℕ → k) (α : ℕ → E)
    (hsq : ∀ i < m, α i ^ 2 = algebraMap k E (q i))
    (hbase : ∀ s : Finset ℕ, s.Nonempty →
      (∀ i ∈ s, i < m) → ¬IsSquare (∏ i ∈ s, q i))
    (s : Finset ℕ) (hs : s.Nonempty) (hsupp : ∀ i ∈ s, i < m) :
    ∑ i ∈ s, α i ≠ 0 := by
  classical
  let j := s.max' hs
  have hjmem : j ∈ s := s.max'_mem hs
  have hjlt : j < m := hsupp j hjmem
  have hjnew : α j ∉ quadraticAdjoinTower (k := k) α j :=
    square_quadratic_tower m q α hsq hbase hjlt
  intro hsum
  apply hjnew
  have hroot_mem : ∀ i ∈ s.erase j,
      α i ∈ quadraticAdjoinTower (k := k) α j := by
    intro i hi
    rw [quadratic_tower_iio]
    apply IntermediateField.subset_adjoin
    exact ⟨i, s.lt_max'_of_mem_erase_max' hs hi, rfl⟩
  have herase_mem :
      ∑ i ∈ s.erase j, α i ∈ quadraticAdjoinTower (k := k) α j := by
    exact (quadraticAdjoinTower (k := k) α j).sum_mem hroot_mem
  have hj_eq : α j = -∑ i ∈ s.erase j, α i := by
    rw [eq_neg_iff_add_eq_zero]
    simpa [add_comm] using (Finset.sum_erase_add _ _ hjmem).trans hsum
  rw [hj_eq]
  exact (quadraticAdjoinTower (k := k) α j).neg_mem herase_mem

/-- The same degree formula stated directly for the field generated by the
first `n` elements. -/
theorem finrank_adjoin_iio
    {E : Type*} [Field E] [Algebra k E] (α : ℕ → E)
    (hsq : ∀ n, α n ^ 2 ∈ quadraticAdjoinTower (k := k) α n)
    (hnew : ∀ n, α n ∉ quadraticAdjoinTower (k := k) α n) (n : ℕ) :
    Module.finrank k (IntermediateField.adjoin k (α '' Set.Iio n)) = 2 ^ n := by
  rw [← quadratic_tower_iio]
  exact finrank_quadratic_adjoin α hsq hnew n

/-- An automorphism of a field generated by square roots has order dividing
two. -/
theorem aut_sq_roots
    [FiniteDimensional k K] (S : Set K)
    (hgen : IntermediateField.adjoin k S = ⊤)
    (hsq : ∀ x ∈ S, x ^ 2 ∈ Set.range (algebraMap k K))
    (σ : K ≃ₐ[k] K) :
    σ ^ 2 = 1 := by
  have hSalg : Algebra.adjoin k S = ⊤ := by
    rw [← IntermediateField.adjoin_toSubalgebra_of_isAlgebraic
      (fun x _ ↦ Algebra.IsAlgebraic.isAlgebraic x), hgen]
    rfl
  have heq : (σ ^ 2).toAlgHom = (1 : K ≃ₐ[k] K).toAlgHom := by
    apply AlgHom.ext_of_adjoin_eq_top hSalg
    intro x hx
    obtain ⟨a, ha⟩ := hsq x hx
    have hsigmaSq : (σ x) ^ 2 = x ^ 2 := by
      calc
        (σ x) ^ 2 = σ (x ^ 2) := (map_pow σ x 2).symm
        _ = σ (algebraMap k K a) := by rw [ha]
        _ = algebraMap k K a := σ.commutes a
        _ = x ^ 2 := ha
    rcases eq_or_eq_neg_of_sq_eq_sq (σ x) x hsigmaSq with hσ | hσ
    · simp [pow_two, AlgEquiv.mul_apply, hσ]
    · change σ (σ x) = x
      rw [hσ, map_neg, hσ, neg_neg]
  exact AlgEquiv.ext fun x ↦ DFunLike.congr_fun heq x

/-- Consequently, the automorphism group of a field generated by square
roots is abelian. -/
theorem aut_commute_roots
    [FiniteDimensional k K] (S : Set K)
    (hgen : IntermediateField.adjoin k S = ⊤)
    (hsq : ∀ x ∈ S, x ^ 2 ∈ Set.range (algebraMap k K))
    (σ τ : K ≃ₐ[k] K) :
    σ * τ = τ * σ := by
  have hpow (ρ : K ≃ₐ[k] K) : ρ ^ 2 = 1 :=
    aut_sq_roots S hgen hsq ρ
  have hinv (ρ : K ≃ₐ[k] K) : ρ⁻¹ = ρ := by
    apply inv_eq_of_mul_eq_one_right
    simpa [pow_two] using hpow ρ
  calc
    σ * τ = (σ * τ)⁻¹ := (hinv (σ * τ)).symm
    _ = τ⁻¹ * σ⁻¹ := mul_inv_rev σ τ
    _ = τ * σ := by rw [hinv τ, hinv σ]

/-- A finite extension of a characteristic-zero field generated by square
roots is Galois.  Each generator has a quadratic polynomial that already
splits in the extension, and splitting propagates through the adjoin. -/
theorem galois_square_roots
    [CharZero k] [FiniteDimensional k K] (S : Set K)
    (hgen : IntermediateField.adjoin k S = ⊤)
    (hsq : ∀ x ∈ S, x ^ 2 ∈ Set.range (algebraMap k K)) :
    IsGalois k K := by
  rw [isGalois_iff]
  refine ⟨inferInstance, ?_⟩
  rw [normal_iff]
  intro x
  refine ⟨IsIntegral.of_finite k x, ?_⟩
  apply IntermediateField.splits_of_mem_adjoin
    (F := k) (K := K) (S := S) (L := K)
  · intro y hy
    obtain ⟨a, ha⟩ := hsq y hy
    have hyint : IsIntegral k y := by
      refine ⟨X ^ 2 - C a, monic_X_pow_sub_C a (by norm_num), ?_⟩
      simp [← ha]
    refine ⟨hyint, ?_⟩
    have hdvd : minpoly k y ∣ X ^ 2 - C a := by
      apply minpoly.dvd
      simp [← ha]
    have hfactor :
        (X ^ 2 - C a).map (algebraMap k K) =
          (X - C y) * (X - C (-y)) := by
      simp only [Polynomial.map_sub, Polynomial.map_pow, map_X, map_C, ha,
        map_neg]
      rw [map_pow]
      ring
    have hsplit : ((X ^ 2 - C a).map (algebraMap k K)).Splits := by
      rw [hfactor]
      exact (Splits.X_sub_C y).mul (Splits.X_sub_C (-y))
    exact hsplit.of_dvd
      (map_ne_zero (monic_X_pow_sub_C a (by norm_num)).ne_zero)
      (Polynomial.map_dvd (algebraMap k K) hdvd)
  · rw [hgen]
    exact IntermediateField.mem_top

/-- If an automorphism changes at least one successive square root, then it
changes their sum.  The proof proceeds from the last root downward: changing
the last sign while fixing the total sum would put that root in the field
generated by its predecessors. -/
theorem sum_range_moved
    [CharZero k] (m : ℕ) (α : ℕ → K)
    (hsq : ∀ i < m, α i ^ 2 ∈ Set.range (algebraMap k K))
    (hnew : ∀ i < m, α i ∉ IntermediateField.adjoin k (α '' Set.Iio i))
    (σ : K ≃ₐ[k] K)
    (hmoved : ∃ i < m, σ (α i) ≠ α i) :
    σ (∑ i ∈ Finset.range m, α i) ≠ ∑ i ∈ Finset.range m, α i := by
  induction m with
  | zero => simp at hmoved
  | succ m ih =>
      have hsign : ∀ i < m + 1, σ (α i) = α i ∨ σ (α i) = -α i := by
        intro i hi
        obtain ⟨a, ha⟩ := hsq i hi
        have hsigmaSq : (σ (α i)) ^ 2 = (α i) ^ 2 := by
          calc
            (σ (α i)) ^ 2 = σ ((α i) ^ 2) := (map_pow σ (α i) 2).symm
            _ = σ (algebraMap k K a) := by rw [ha]
            _ = algebraMap k K a := σ.commutes a
            _ = (α i) ^ 2 := ha
        exact eq_or_eq_neg_of_sq_eq_sq _ _ hsigmaSq
      by_cases hlast : σ (α m) = α m
      · have hmoved' : ∃ i < m, σ (α i) ≠ α i := by
          obtain ⟨i, hi, hmove⟩ := hmoved
          have him : i ≤ m := Nat.le_of_lt_succ hi
          have hine : i ≠ m := by
            intro himEq
            exact hmove (himEq ▸ hlast)
          exact ⟨i, lt_of_le_of_ne him hine, hmove⟩
        simpa [Finset.sum_range_succ, map_add, hlast] using
          ih (fun i hi ↦ hsq i (Nat.lt_succ_of_lt hi))
            (fun i hi ↦ hnew i (Nat.lt_succ_of_lt hi)) hmoved'
      · have hlastneg : σ (α m) = -α m :=
          (hsign m (Nat.lt_succ_self m)).resolve_left hlast
        intro hsum
        have hsumprior :
            σ (∑ i ∈ Finset.range m, α i) =
              (∑ i ∈ Finset.range m, α i) + 2 * α m := by
          rw [Finset.sum_range_succ, map_add, hlastneg] at hsum
          linear_combination hsum
        let L := IntermediateField.adjoin k (α '' Set.Iio m)
        have hleft : σ (∑ i ∈ Finset.range m, α i) ∈ L := by
          rw [map_sum]
          apply L.sum_mem
          intro i hi
          rw [Finset.mem_range] at hi
          rcases hsign i (Nat.lt_trans hi (Nat.lt_succ_self m)) with h | h
          · rw [h]
            exact IntermediateField.subset_adjoin k _ ⟨i, hi, rfl⟩
          · rw [h]
            exact L.neg_mem (IntermediateField.subset_adjoin k _ ⟨i, hi, rfl⟩)
        have hprior : (∑ i ∈ Finset.range m, α i) ∈ L := by
          apply L.sum_mem
          intro i hi
          rw [Finset.mem_range] at hi
          exact IntermediateField.subset_adjoin k _ ⟨i, hi, rfl⟩
        have htwoalpha : 2 * α m ∈ L := by
          have hdiff := L.sub_mem hleft hprior
          rw [hsumprior] at hdiff
          convert hdiff using 1
          all_goals ring
        apply hnew m (Nat.lt_succ_self m)
        have htwoinv : algebraMap k K (2⁻¹) ∈ L := L.algebraMap_mem _
        have hmem := L.mul_mem htwoinv htwoalpha
        have htwoK : (2 : K) ≠ 0 := by
          intro h
          apply (by norm_num : (2 : k) ≠ 0)
          apply (algebraMap k K).injective
          simpa only [map_ofNat, map_zero] using h
        have heq : algebraMap k K (2⁻¹ : k) * (2 * α m) = α m := by
          rw [map_inv₀, map_ofNat]
          rw [← mul_assoc, inv_mul_cancel₀ htwoK, one_mul]
        rw [← heq]
        exact hmem

/-- A nonidentity automorphism of a field generated by successive square
roots changes their sum. -/
theorem range_moved_aut
    [CharZero k] [FiniteDimensional k K] (m : ℕ) (α : ℕ → K)
    (hgen : IntermediateField.adjoin k (α '' Set.Iio m) = ⊤)
    (hsq : ∀ i < m, α i ^ 2 ∈ Set.range (algebraMap k K))
    (hnew : ∀ i < m, α i ∉ IntermediateField.adjoin k (α '' Set.Iio i))
    (σ : K ≃ₐ[k] K) (hσ : σ ≠ 1) :
    σ (∑ i ∈ Finset.range m, α i) ≠ ∑ i ∈ Finset.range m, α i := by
  apply sum_range_moved m α hsq hnew σ
  by_contra hnone
  simp only [not_exists, not_and, not_not] at hnone
  apply hσ
  have hSalg : Algebra.adjoin k (α '' Set.Iio m) = ⊤ := by
    rw [← IntermediateField.adjoin_toSubalgebra_of_isAlgebraic
      (fun x _ ↦ Algebra.IsAlgebraic.isAlgebraic x), hgen]
    rfl
  have heq : σ.toAlgHom = (1 : K ≃ₐ[k] K).toAlgHom := by
    apply AlgHom.ext_of_adjoin_eq_top hSalg
    intro x hx
    obtain ⟨i, hi, rfl⟩ := hx
    simpa using hnone i hi
  exact AlgEquiv.ext fun x ↦ DFunLike.congr_fun heq x

/-- In a finite Galois extension, an element moved by every nonidentity
automorphism generates the extension. -/
theorem moved_nontrivial_aut
    [FiniteDimensional k K] [IsGalois k K] (γ : K)
    (hγ : ∀ σ : K ≃ₐ[k] K, σ ≠ 1 → σ γ ≠ γ) :
    IntermediateField.adjoin k {γ} = ⊤ := by
  let L : IntermediateField k K := IntermediateField.adjoin k {γ}
  have hfix : L.fixingSubgroup = ⊥ := by
    apply le_antisymm
    · intro σ hσ
      change σ = 1
      by_contra hσ1
      apply hγ σ hσ1
      exact (L.mem_fixingSubgroup_iff σ).1 hσ γ
        (IntermediateField.subset_adjoin k {γ} (Set.mem_singleton γ))
    · exact bot_le
  calc
    IntermediateField.adjoin k {γ} =
        IntermediateField.fixedField L.fixingSubgroup := by
      simpa [L] using (IsGalois.fixedField_fixingSubgroup L).symm
    _ = IntermediateField.fixedField (⊥ : Subgroup (K ≃ₐ[k] K)) := by rw [hfix]
    _ = ⊤ := IntermediateField.fixedField_bot

/-- Under the same hypothesis, the minimal polynomial of the element has the
full extension degree. -/
theorem moved_every_aut
    [FiniteDimensional k K] [IsGalois k K] (γ : K)
    (hγ : ∀ σ : K ≃ₐ[k] K, σ ≠ 1 → σ γ ≠ γ) :
    (minpoly k γ).natDegree = Module.finrank k K := by
  have htop := moved_nontrivial_aut γ hγ
  have hfin := IntermediateField.adjoin.finrank
    (Algebra.IsIntegral.isIntegral (R := k) γ)
  rw [htop] at hfin
  simpa using hfin.symm

/-- Milne, Exercise 7-6, primitive-element assertion: the sum of the chosen
square roots of distinct primes generates their compositum. -/
theorem adjoin_distinct_roots
    {E : Type*} [Field E] [Algebra ℚ E]
    (m : ℕ) (p : ℕ → ℕ) (α : ℕ → E)
    (hp : ∀ i < m, Nat.Prime (p i))
    (hinj : Set.InjOn p (Set.Iio m))
    (hsq : ∀ i < m, α i ^ 2 = algebraMap ℚ E (p i : ℚ))
    (hgen : IntermediateField.adjoin ℚ (α '' Set.Iio m) = ⊤) :
    IntermediateField.adjoin ℚ {∑ i ∈ Finset.range m, α i} = ⊤ := by
  have hfin : Module.finrank ℚ E = 2 ^ m := by
    have hfinAdjoin :=
      distinct_square_roots m p α hp hinj hsq
    rw [hgen] at hfinAdjoin
    simpa using hfinAdjoin
  let : FiniteDimensional ℚ E := FiniteDimensional.of_finrank_pos (by
    rw [hfin]
    positivity)
  let : IsGalois ℚ E := galois_square_roots
    (α '' Set.Iio m) hgen (by
      intro x hx
      obtain ⟨i, hi, rfl⟩ := hx
      exact ⟨(p i : ℚ), (hsq i hi).symm⟩)
  apply moved_nontrivial_aut
  intro σ hσ
  exact range_moved_aut m α hgen
    (fun i hi ↦ ⟨(p i : ℚ), (hsq i hi).symm⟩)
    (distinct_adjoin_prior m p α hp hinj hsq)
    σ hσ

/-- Milne, Exercise 7-6: the minimal polynomial of the sum of the chosen
square roots has degree `2^m`. -/
theorem minpoly_distinct_square
    {E : Type*} [Field E] [Algebra ℚ E]
    (m : ℕ) (p : ℕ → ℕ) (α : ℕ → E)
    (hp : ∀ i < m, Nat.Prime (p i))
    (hinj : Set.InjOn p (Set.Iio m))
    (hsq : ∀ i < m, α i ^ 2 = algebraMap ℚ E (p i : ℚ))
    (hgen : IntermediateField.adjoin ℚ (α '' Set.Iio m) = ⊤) :
    (minpoly ℚ (∑ i ∈ Finset.range m, α i)).natDegree = 2 ^ m := by
  have hfin : Module.finrank ℚ E = 2 ^ m := by
    have hfinAdjoin :=
      distinct_square_roots m p α hp hinj hsq
    rw [hgen] at hfinAdjoin
    simpa using hfinAdjoin
  let : FiniteDimensional ℚ E := FiniteDimensional.of_finrank_pos (by
    rw [hfin]
    positivity)
  have htop := adjoin_distinct_roots
    m p α hp hinj hsq hgen
  have hadjoin := IntermediateField.adjoin.finrank
    (IsIntegral.of_finite ℚ (∑ i ∈ Finset.range m, α i))
  rw [htop] at hadjoin
  calc
    (minpoly ℚ (∑ i ∈ Finset.range m, α i)).natDegree =
        Module.finrank ℚ E := by simpa using hadjoin.symm
    _ = 2 ^ m := hfin

/-- If a simple generator is a sum of square roots, then every irreducible
factor of its minimal polynomial after a scalar extension is generated by
the corresponding images of those square roots. -/
theorem square_roots_generating
    {kp E : Type*} [Field kp] [Field E] [Algebra k kp] [Algebra k E]
    (m : ℕ) (q : ℕ → k) (α : ℕ → E) (γ : E)
    (hα : ∀ i < m, α i ^ 2 = algebraMap k E (q i))
    (hγ : γ = ∑ i ∈ Finset.range m, α i)
    (hint : IsIntegral k γ)
    (htop : IntermediateField.adjoin k {γ} = ⊤)
    (g : kp[X]) [Fact (Irreducible g)]
    (hdvd : g ∣ (minpoly k γ).map (algebraMap k kp)) :
    ∃ β : ℕ → AdjoinRoot g,
      (∀ i < m, β i ^ 2 =
        algebraMap kp (AdjoinRoot g) (algebraMap k kp (q i))) ∧
      IntermediateField.adjoin kp (β '' Set.Iio m) = ⊤ := by
  let e : E ≃ₐ[k] AdjoinRoot (minpoly k γ) :=
    IntermediateField.topEquiv.symm |>.trans
      (IntermediateField.equivOfEq htop.symm) |>.trans
      (IntermediateField.adjoinRootEquivAdjoin k hint).symm
  let φ : AdjoinRoot (minpoly k γ) →ₐ[k] AdjoinRoot g :=
    AdjoinRoot.mapAlgHom (Algebra.ofId k kp) (minpoly k γ) g hdvd
  let β : ℕ → AdjoinRoot g := fun i ↦ φ (e (α i))
  refine ⟨β, ?_, ?_⟩
  · intro i hi
    calc
      β i ^ 2 = φ (e (α i ^ 2)) := by simp [β]
      _ = φ (e (algebraMap k E (q i))) := by rw [hα i hi]
      _ = algebraMap kp (AdjoinRoot g) (algebraMap k kp (q i)) := by
        rw [e.commutes]
        rw [φ.commutes, IsScalarTower.algebraMap_apply k kp (AdjoinRoot g)]
  · have heγ : e γ = AdjoinRoot.root (minpoly k γ) := by
      dsimp [e]
      change (IntermediateField.adjoinRootEquivAdjoin k hint).symm
        (IntermediateField.AdjoinSimple.gen k γ) = _
      rw [IntermediateField.adjoinRootEquivAdjoin_symm_apply_gen]
    have hroot : AdjoinRoot.root g = ∑ i ∈ Finset.range m, β i := by
      rw [← AdjoinRoot.map_root (Algebra.ofId k kp) (minpoly k γ) g hdvd]
      change φ (AdjoinRoot.root (minpoly k γ)) = _
      rw [← heγ]
      calc
        φ (e γ) = φ (e (∑ i ∈ Finset.range m, α i)) :=
          congrArg (fun x : E ↦ φ (e x)) hγ
        _ = ∑ i ∈ Finset.range m, β i := by simp [β]
    apply top_unique
    rw [← IntermediateField.adjoin_root_eq_top g]
    apply IntermediateField.adjoin_le_iff.mpr
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    rw [hroot]
    apply (IntermediateField.adjoin kp (β '' Set.Iio m)).sum_mem
    intro i hi
    rw [Finset.mem_range] at hi
    exact IntermediateField.subset_adjoin kp _ ⟨i, hi, rfl⟩

/-- A degree bound for fields generated by the transported square roots gives
the same bound for an irreducible factor of the scalar-extended minimal
polynomial. -/
theorem irreducible_roots_bound
    {kp E : Type*} [Field kp] [Field E] [Algebra k kp] [Algebra k E]
    (m : ℕ) (q : ℕ → k) (α : ℕ → E) (γ : E)
    (hα : ∀ i < m, α i ^ 2 = algebraMap k E (q i))
    (hγ : γ = ∑ i ∈ Finset.range m, α i)
    (hint : IsIntegral k γ)
    (htop : IntermediateField.adjoin k {γ} = ⊤)
    (g : kp[X]) [Fact (Irreducible g)]
    (hdvd : g ∣ (minpoly k γ).map (algebraMap k kp))
    (B : ℕ)
    (hbound : ∀ β : ℕ → AdjoinRoot g,
      (∀ i < m, β i ^ 2 =
        algebraMap kp (AdjoinRoot g) (algebraMap k kp (q i))) →
      Module.finrank kp
        (IntermediateField.adjoin kp (β '' Set.Iio m)) ≤ B) :
    g.natDegree ≤ B := by
  obtain ⟨β, hβ, hgen⟩ :=
    square_roots_generating
      m q α γ hα hγ hint htop g hdvd
  have h := hbound β hβ
  rw [hgen] at h
  have hfin : Module.finrank kp (AdjoinRoot g) = g.natDegree :=
    (AdjoinRoot.powerBasis (Fact.out : Irreducible g).ne_zero).finrank
  rw [← hfin]
  simpa using h

/-- Milne, Exercise 7-6, local factor assertion.  Every irreducible factor
over `ℚ_[p]` of the minimal polynomial of the sum has degree at most eight
when `p = 2`, and at most four for odd `p`. -/
theorem minpoly_distinct_roots
    {E : Type*} [Field E] [Algebra ℚ E]
    (m : ℕ) (q : ℕ → ℕ) (α : ℕ → E)
    (hq : ∀ i < m, Nat.Prime (q i))
    (hinj : Set.InjOn q (Set.Iio m))
    (hα : ∀ i < m, α i ^ 2 = algebraMap ℚ E (q i : ℚ))
    (hgen : IntermediateField.adjoin ℚ (α '' Set.Iio m) = ⊤)
    (p : ℕ) [Fact p.Prime]
    (g : ℚ_[p][X]) (hg : Irreducible g)
    (hdvd : g ∣
      (minpoly ℚ (∑ i ∈ Finset.range m, α i)).map (algebraMap ℚ ℚ_[p])) :
    g.natDegree ≤ if p = 2 then 8 else 4 := by
  let : Fact (Irreducible g) := ⟨hg⟩
  let γ : E := ∑ i ∈ Finset.range m, α i
  have hfin : Module.finrank ℚ E = 2 ^ m := by
    have hfinAdjoin :=
      distinct_square_roots m q α hq hinj hα
    rw [hgen] at hfinAdjoin
    simpa using hfinAdjoin
  let : FiniteDimensional ℚ E := FiniteDimensional.of_finrank_pos (by
    rw [hfin]
    positivity)
  have hint : IsIntegral ℚ γ := IsIntegral.of_finite ℚ γ
  have htop : IntermediateField.adjoin ℚ {γ} = ⊤ := by
    exact adjoin_distinct_roots
      m q α hq hinj hα hgen
  apply irreducible_roots_bound
    m (fun i ↦ (q i : ℚ)) α γ hα rfl hint htop g hdvd
  intro β hβ
  by_cases hp2 : p = 2
  · subst p
    simpa using square_roots_eight
      m q β hq (fun i hi ↦ by simpa using hβ i hi)
  · simpa [hp2] using finrank_square_roots
      p hp2 m q β hq (fun i hi ↦ by simpa using hβ i hi)

end

end Towers.NumberTheory.Milne
