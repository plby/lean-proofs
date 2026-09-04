import ErdosProblems.Erdos394.PairResidueKernel

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Pair-congruence lattices with additional forced local origins
-/

open Nat Finset Module Submodule

namespace Erdos394

/-- Inclusion of a forced-prime subtype into the full prime subtype. -/
def forcedPrimeIncl {P F : Finset ℕ} (hFP : F ⊆ P)
    (p : {p // p ∈ F}) : {p // p ∈ P} := ⟨p.val, hFP p.property⟩

abbrev ForcedPairEquationSpace (P F : Finset ℕ) :=
  PrimeResidues P × PrimeResidues F

/-- At forced primes output both coordinates; elsewhere output the single
root-label equation coordinate. -/
def forcedPairEquationLinear (P F : Finset ℕ) (a b : ℕ → ℕ)
    (hFP : F ⊆ P) :
    (PrimeResidues P × PrimeResidues P) →ₗ[ℤ]
      ForcedPairEquationSpace P F where
  toFun := fun jl ↦
    (fun p ↦
      if p.val ∈ F then jl.1 p
      else if a p.val = 0 then jl.1 p
      else if b p.val = 0 then jl.2 p
      else (a p.val : ZMod p.val) * jl.2 p -
        (b p.val : ZMod p.val) * jl.1 p,
     fun p ↦ jl.2 (forcedPrimeIncl hFP p))
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
      simp
      ring
    · funext p
      rfl

/-- Regard a full-prime element known to be forced as a forced-prime subtype. -/
def mkForcedPrime {P F : Finset ℕ} (p : {p // p ∈ P}) (hpF : p.val ∈ F) :
    {p // p ∈ F} := ⟨p.val, hpF⟩

/-- The forced local equation quotient is surjective when every both-zero
label prime is forced. -/
theorem forcedPairEquationLinear_surjective
    (P F : Finset ℕ) (a b : ℕ → ℕ) {K : ℕ}
    (hFP : F ⊆ P)
    (hzeroF : bothZeroLabelPrimes P a b ⊆ F)
    (hprime : ∀ p ∈ P, p.Prime)
    (ha : ∀ p ∈ P, a p < K) (hb : ∀ p ∈ P, b p < K)
    (hKp : ∀ p ∈ P, K < p) :
    Function.Surjective (forcedPairEquationLinear P F a b hFP) := by
  classical
  intro y
  let j : PrimeResidues P := fun p ↦
    if p.val ∈ F then y.1 p
    else if a p.val = 0 then y.1 p
    else 0
  let l : PrimeResidues P := fun p ↦
    if hpF : p.val ∈ F then y.2 (mkForcedPrime p hpF)
    else if a p.val = 0 then 0
    else if b p.val = 0 then y.1 p
    else (a p.val : ZMod p.val)⁻¹ * y.1 p
  refine ⟨(j, l), ?_⟩
  apply Prod.ext
  · funext p
    dsimp [forcedPairEquationLinear, j, l]
    by_cases hpF : p.val ∈ F
    · simp [hpF]
    · have hnotboth : ¬(a p.val = 0 ∧ b p.val = 0) := by
        intro hz
        exact hpF (hzeroF (Finset.mem_filter.mpr ⟨p.property, hz⟩))
      by_cases ha0 : a p.val = 0
      · simp [hpF, ha0]
      · by_cases hb0 : b p.val = 0
        · simp [hpF, ha0, hb0]
        · let : Fact p.val.Prime := ⟨hprime p.val p.property⟩
          have hapos : 0 < a p.val := Nat.pos_of_ne_zero ha0
          have hap : a p.val < p.val :=
            (ha p.val p.property).trans (hKp p.val p.property)
          have hane : (a p.val : ZMod p.val) ≠ 0 :=
            natCast_zmod_ne_zero_of_pos_of_lt hapos hap
          simp [j, l, hpF, ha0, hb0, hane]
  · funext p
    change l (forcedPrimeIncl hFP p) = y.2 p
    have hpF' : (forcedPrimeIncl hFP p).val ∈ F := p.property
    dsimp [l]
    rw [dif_pos hpF']
    congr 1

/-- Global forced pair residue map. -/
def globalForcedPairEquationLinear (P F : Finset ℕ) (a b : ℕ → ℕ)
    (hFP : F ⊆ P) :
    (Fin 2 → ℤ) →ₗ[ℤ] ForcedPairEquationSpace P F :=
  (forcedPairEquationLinear P F a b hFP).comp (pairCRTLinear P)

theorem globalForcedPairEquationLinear_surjective
    (P F : Finset ℕ) (a b : ℕ → ℕ) {K : ℕ}
    (hFP : F ⊆ P)
    (hzeroF : bothZeroLabelPrimes P a b ⊆ F)
    (hprime : ∀ p ∈ P, p.Prime)
    (ha : ∀ p ∈ P, a p < K) (hb : ∀ p ∈ P, b p < K)
    (hKp : ∀ p ∈ P, K < p) :
    Function.Surjective (globalForcedPairEquationLinear P F a b hFP) :=
  (forcedPairEquationLinear_surjective P F a b hFP hzeroF hprime ha hb hKp).comp
    (pairCRTLinear_surjective P hprime)

/-- Forced pair lattice. -/
def globalForcedPairLattice (P F : Finset ℕ) (a b : ℕ → ℕ)
    (hFP : F ⊆ P) : Submodule ℤ (Fin 2 → ℤ) :=
  LinearMap.ker (globalForcedPairEquationLinear P F a b hFP)

/-- Its exact quotient index is `(∏P)(∏F)`. -/
theorem globalForcedPairLattice_index
    (P F : Finset ℕ) (a b : ℕ → ℕ) {K : ℕ}
    (hFP : F ⊆ P)
    (hzeroF : bothZeroLabelPrimes P a b ⊆ F)
    (hprime : ∀ p ∈ P, p.Prime)
    (ha : ∀ p ∈ P, a p < K) (hb : ∀ p ∈ P, b p < K)
    (hKp : ∀ p ∈ P, K < p) :
    Nat.card ((Fin 2 → ℤ) ⧸ globalForcedPairLattice P F a b hFP) =
      primeProduct P * primeProduct F := by
  let : ∀ p : {p // p ∈ P}, NeZero p.val :=
    fun p ↦ ⟨(hprime p.val p.property).ne_zero⟩
  let : ∀ p : {p // p ∈ F}, NeZero p.val :=
    fun p ↦ ⟨(hprime p.val (hFP p.property)).ne_zero⟩
  let : Finite (ForcedPairEquationSpace P F) := inferInstance
  let f := globalForcedPairEquationLinear P F a b hFP
  have hf : Function.Surjective f :=
    globalForcedPairEquationLinear_surjective P F a b hFP hzeroF hprime ha hb hKp
  calc
    Nat.card ((Fin 2 → ℤ) ⧸ globalForcedPairLattice P F a b hFP) =
        Nat.card (ForcedPairEquationSpace P F) := kernel_quotient_natCard_eq f hf
    _ = primeProduct P * primeProduct F := by
      rw [Nat.card_prod, natCard_primeResidues, natCard_primeResidues]

/-- The forced lattice has a two-element integer basis. -/
noncomputable def globalForcedPairLatticeBasis
    (P F : Finset ℕ) (a b : ℕ → ℕ) {K : ℕ}
    (hFP : F ⊆ P)
    (hzeroF : bothZeroLabelPrimes P a b ⊆ F)
    (hprime : ∀ p ∈ P, p.Prime)
    (ha : ∀ p ∈ P, a p < K) (hb : ∀ p ∈ P, b p < K)
    (hKp : ∀ p ∈ P, K < p) :
    Basis (Fin 2) ℤ (globalForcedPairLattice P F a b hFP) := by
  letI : ∀ p : {p // p ∈ P}, NeZero p.val :=
    fun p ↦ ⟨(hprime p.val p.property).ne_zero⟩
  letI : ∀ p : {p // p ∈ F}, NeZero p.val :=
    fun p ↦ ⟨(hprime p.val (hFP p.property)).ne_zero⟩
  letI : Finite (ForcedPairEquationSpace P F) := inferInstance
  let f := globalForcedPairEquationLinear P F a b hFP
  have hf : Function.Surjective f :=
    globalForcedPairEquationLinear_surjective P F a b hFP hzeroF hprime ha hb hKp
  exact kernelFinTwoBasis f hf

end Erdos394
