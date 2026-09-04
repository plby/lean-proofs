import ErdosProblems.Erdos394.ZModPiCRT
import ErdosProblems.Erdos394.FiniteKernelLattice
import ErdosProblems.Erdos394.PairLattice

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Global pair-residue kernel lattice
-/

open Nat Finset Module Submodule
open scoped Matrix

namespace Erdos394

abbrev PrimeResidues (P : Finset ℕ) := ∀ p : {p // p ∈ P}, ZMod p.val

/-- Simultaneous reduction of both integer coordinates at all primes in `P`. -/
def pairCRTLinear (P : Finset ℕ) :
    (Fin 2 → ℤ) →ₗ[ℤ] (PrimeResidues P × PrimeResidues P) where
  toFun := fun x ↦ (zmodPiLinear P (x 0), zmodPiLinear P (x 1))
  map_add' x y := by ext p <;> simp
  map_smul' n x := by ext p <;> simp

@[simp] theorem pairCRTLinear_fst (P : Finset ℕ) (x : Fin 2 → ℤ)
    (p : {p // p ∈ P}) : (pairCRTLinear P x).1 p = (x 0 : ZMod p.val) := rfl

@[simp] theorem pairCRTLinear_snd (P : Finset ℕ) (x : Fin 2 → ℤ)
    (p : {p // p ∈ P}) : (pairCRTLinear P x).2 p = (x 1 : ZMod p.val) := rfl

/-- Coordinatewise CRT makes the pair reduction map surjective. -/
theorem pairCRTLinear_surjective (P : Finset ℕ)
    (hprime : ∀ p ∈ P, p.Prime) : Function.Surjective (pairCRTLinear P) := by
  intro y
  obtain ⟨j, hj⟩ := zmodPiLinear_surjective P hprime y.1
  obtain ⟨l, hl⟩ := zmodPiLinear_surjective P hprime y.2
  refine ⟨![j, l], ?_⟩
  change (zmodPiLinear P j, zmodPiLinear P l) = y
  exact Prod.ext hj hl

/-- Inclusion of the both-zero prime subtype into the full prime subtype. -/
def bothZeroPrimeIncl (P : Finset ℕ) (a b : ℕ → ℕ)
    (p : {p // p ∈ bothZeroLabelPrimes P a b}) : {p // p ∈ P} :=
  ⟨p.val, (Finset.mem_filter.mp p.property).1⟩

abbrev PairEquationSpace (P : Finset ℕ) (a b : ℕ → ℕ) :=
  PrimeResidues P × PrimeResidues (bothZeroLabelPrimes P a b)

/-- Quotient each local residue pair by its one equation, together with the
second independent coordinate at both-zero primes.  Its kernel is exactly the
underlying pair congruence condition. -/
def pairEquationLinear (P : Finset ℕ) (a b : ℕ → ℕ) :
    (PrimeResidues P × PrimeResidues P) →ₗ[ℤ] PairEquationSpace P a b where
  toFun := fun jl ↦
    (fun p ↦
      let A := a p.val
      let B := b p.val
      if A = 0 ∧ B = 0 then jl.1 p
      else if A = 0 then jl.1 p
      else if B = 0 then jl.2 p
      else (A : ZMod p.val) * jl.2 p - (B : ZMod p.val) * jl.1 p,
     fun p ↦ jl.2 (bothZeroPrimeIncl P a b p))
  map_add' x y := by
    apply Prod.ext
    · funext p
      dsimp
      split_ifs <;> try rfl
      ring
    · funext p
      rfl
  map_smul' n x := by
    apply Prod.ext
    · funext p
      dsimp
      split_ifs <;> try rfl
      simp [smul_eq_mul]
      ring
    · funext p
      rfl

/-- Regard a full-prime subtype element with both-zero labels as an element
of the both-zero prime subtype. -/
def mkBothZeroPrime (P : Finset ℕ) (a b : ℕ → ℕ)
    (p : {p // p ∈ P}) (h : a p.val = 0 ∧ b p.val = 0) :
    {p // p ∈ bothZeroLabelPrimes P a b} :=
  ⟨p.val, by
    unfold bothZeroLabelPrimes
    exact Finset.mem_filter.mpr ⟨p.property, h⟩⟩

/-- The local equation quotient is surjective when labels are below the prime
moduli and every non-both-zero equation has a nonzero coefficient. -/
theorem pairEquationLinear_surjective
    (P : Finset ℕ) (a b : ℕ → ℕ) {K : ℕ}
    (hprime : ∀ p ∈ P, p.Prime)
    (ha : ∀ p ∈ P, a p < K) (hb : ∀ p ∈ P, b p < K)
    (hKp : ∀ p ∈ P, K < p) :
    Function.Surjective (pairEquationLinear P a b) := by
  classical
  intro y
  let j : PrimeResidues P := fun p ↦
    if a p.val = 0 ∧ b p.val = 0 then y.1 p
    else if a p.val = 0 then y.1 p
    else 0
  let l : PrimeResidues P := fun p ↦
    if h : a p.val = 0 ∧ b p.val = 0 then
      y.2 (mkBothZeroPrime P a b p h)
    else if a p.val = 0 then 0
    else if b p.val = 0 then y.1 p
    else ((a p.val : ℕ) : ZMod p.val)⁻¹ * y.1 p
  refine ⟨(j, l), ?_⟩
  apply Prod.ext
  · funext p
    dsimp [pairEquationLinear, j, l]
    by_cases hboth : a p.val = 0 ∧ b p.val = 0
    · simp [hboth]
    · by_cases ha0 : a p.val = 0
      · simp [hboth, ha0]
      · by_cases hb0 : b p.val = 0
        · simp [hboth, ha0, hb0]
        · let : Fact p.val.Prime := ⟨hprime p.val p.property⟩
          have hapos : 0 < a p.val := Nat.pos_of_ne_zero ha0
          have hap : a p.val < p.val := (ha p.val p.property).trans (hKp p.val p.property)
          have hane : ((a p.val : ℕ) : ZMod p.val) ≠ 0 :=
            natCast_zmod_ne_zero_of_pos_of_lt hapos hap
          simp [j, l, hboth, ha0, hb0, hane]
  · funext p
    have hpzero : a p.val = 0 ∧ b p.val = 0 :=
      (Finset.mem_filter.mp p.property).2
    change l (bothZeroPrimeIncl P a b p) = y.2 p
    have hpzero' :
        a (bothZeroPrimeIncl P a b p).val = 0 ∧
          b (bothZeroPrimeIncl P a b p).val = 0 := by
      simpa [bothZeroPrimeIncl] using hpzero
    dsimp [l]
    rw [dif_pos hpzero']
    congr 1

/-- Compose CRT reduction with the local quotient.  This map's kernel is the
actual underlying pair-congruence lattice. -/
def globalPairEquationLinear (P : Finset ℕ) (a b : ℕ → ℕ) :
    (Fin 2 → ℤ) →ₗ[ℤ] PairEquationSpace P a b :=
  (pairEquationLinear P a b).comp (pairCRTLinear P)

/-- The global pair-equation map is surjective. -/
theorem globalPairEquationLinear_surjective
    (P : Finset ℕ) (a b : ℕ → ℕ) {K : ℕ}
    (hprime : ∀ p ∈ P, p.Prime)
    (ha : ∀ p ∈ P, a p < K) (hb : ∀ p ∈ P, b p < K)
    (hKp : ∀ p ∈ P, K < p) :
    Function.Surjective (globalPairEquationLinear P a b) :=
  (pairEquationLinear_surjective P a b hprime ha hb hKp).comp
    (pairCRTLinear_surjective P hprime)

/-- The simultaneous prime residue space has cardinality the prime product. -/
theorem natCard_primeResidues (P : Finset ℕ) :
    Nat.card (PrimeResidues P) = primeProduct P := by
  classical
  rw [Nat.card_pi]
  simp only [Nat.card_zmod]
  simpa [primeProduct] using Finset.prod_attach P (fun p ↦ p)

/-- The pair-equation target has cardinality `q q₀₀`. -/
theorem natCard_pairEquationSpace (P : Finset ℕ) (a b : ℕ → ℕ) :
    Nat.card (PairEquationSpace P a b) =
      primeProduct P * pairBothZeroProduct P a b := by
  rw [Nat.card_prod, natCard_primeResidues, natCard_primeResidues]
  rfl

/-- The actual underlying pair-congruence lattice. -/
def globalPairLattice (P : Finset ℕ) (a b : ℕ → ℕ) :
    Submodule ℤ (Fin 2 → ℤ) := LinearMap.ker (globalPairEquationLinear P a b)

/-- The quotient index of the global pair lattice is exactly `q q₀₀`. -/
theorem globalPairLattice_index
    (P : Finset ℕ) (a b : ℕ → ℕ) {K : ℕ}
    (hprime : ∀ p ∈ P, p.Prime)
    (ha : ∀ p ∈ P, a p < K) (hb : ∀ p ∈ P, b p < K)
    (hKp : ∀ p ∈ P, K < p) :
    Nat.card ((Fin 2 → ℤ) ⧸ globalPairLattice P a b) =
      primeProduct P * pairBothZeroProduct P a b := by
  let : ∀ p : {p // p ∈ P}, NeZero p.val :=
    fun p ↦ ⟨(hprime p.val p.property).ne_zero⟩
  let : ∀ p : {p // p ∈ bothZeroLabelPrimes P a b}, NeZero p.val :=
    fun p ↦ ⟨(hprime p.val (Finset.mem_filter.mp p.property).1).ne_zero⟩
  let : Finite (PairEquationSpace P a b) := inferInstance
  let f := globalPairEquationLinear P a b
  have hf : Function.Surjective f :=
    globalPairEquationLinear_surjective P a b hprime ha hb hKp
  calc
    Nat.card ((Fin 2 → ℤ) ⧸ globalPairLattice P a b) =
        Nat.card (PairEquationSpace P a b) := by
      exact kernel_quotient_natCard_eq f hf
    _ = primeProduct P * pairBothZeroProduct P a b :=
      natCard_pairEquationSpace P a b

/-- The pair lattice has a two-element integer basis. -/
noncomputable def globalPairLatticeBasis
    (P : Finset ℕ) (a b : ℕ → ℕ) {K : ℕ}
    (hprime : ∀ p ∈ P, p.Prime)
    (ha : ∀ p ∈ P, a p < K) (hb : ∀ p ∈ P, b p < K)
    (hKp : ∀ p ∈ P, K < p) :
    Basis (Fin 2) ℤ (globalPairLattice P a b) := by
  letI : ∀ p : {p // p ∈ P}, NeZero p.val :=
    fun p ↦ ⟨(hprime p.val p.property).ne_zero⟩
  letI : ∀ p : {p // p ∈ bothZeroLabelPrimes P a b}, NeZero p.val :=
    fun p ↦ ⟨(hprime p.val (Finset.mem_filter.mp p.property).1).ne_zero⟩
  letI : Finite (PairEquationSpace P a b) := inferInstance
  let f := globalPairEquationLinear P a b
  have hf : Function.Surjective f :=
    globalPairEquationLinear_surjective P a b hprime ha hb hKp
  exact kernelFinTwoBasis f hf

end Erdos394
