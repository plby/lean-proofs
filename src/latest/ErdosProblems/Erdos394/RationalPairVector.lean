import ErdosProblems.Erdos394.PairLabelEuler
import ErdosProblems.Erdos394.RationalLineLabels

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Local label sparsity forced by a rational pair-lattice vector
-/

open Nat Finset Module Submodule

namespace Erdos394

/-- At an unforced prime, membership in the forced pair lattice implies the
uniform root-label equation `a*l=b*j`, including the one-zero cases. -/
theorem forced_pair_lattice_unforced_equation
    (P F : Finset ℕ) (a b : ℕ → ℕ)
    (hFP : F ⊆ P)
    (hzeroF : bothZeroLabelPrimes P a b ⊆ F)
    (x : globalForcedPairLattice P F a b hFP)
    {p : ℕ} (hpP : p ∈ P) (hpF : p ∉ F) :
    (a p : ZMod p) * ((x : Fin 2 → ℤ) 1 : ZMod p) =
      (b p : ZMod p) * ((x : Fin 2 → ℤ) 0 : ZMod p) := by
  have hxker : globalForcedPairEquationLinear P F a b hFP
      (x : Fin 2 → ℤ) = 0 := LinearMap.mem_ker.mp x.property
  let pp : {p // p ∈ P} := ⟨p, hpP⟩
  have heq := congrArg (fun y : ForcedPairEquationSpace P F ↦ y.1 pp) hxker
  change (if p ∈ F then ((x : Fin 2 → ℤ) 0 : ZMod p)
    else if a p = 0 then ((x : Fin 2 → ℤ) 0 : ZMod p)
    else if b p = 0 then ((x : Fin 2 → ℤ) 1 : ZMod p)
    else (a p : ZMod p) * ((x : Fin 2 → ℤ) 1 : ZMod p) -
      (b p : ZMod p) * ((x : Fin 2 → ℤ) 0 : ZMod p)) = 0 at heq
  rw [if_neg hpF] at heq
  have hnotboth : ¬(a p = 0 ∧ b p = 0) := by
    intro hz
    exact hpF (hzeroF (Finset.mem_filter.mpr ⟨hpP, hz⟩))
  by_cases ha0 : a p = 0
  · have hb0 : b p ≠ 0 := fun hb0 ↦ hnotboth ⟨ha0, hb0⟩
    have hjz : ((x : Fin 2 → ℤ) 0 : ZMod p) = 0 := by
      simpa [ha0] using heq
    simp [ha0, hjz]
  · by_cases hb0 : b p = 0
    · have hlz : ((x : Fin 2 → ℤ) 1 : ZMod p) = 0 := by
        simpa [ha0, hb0] using heq
      simp [hb0, hlz]
    · have hsub : (a p : ZMod p) * ((x : Fin 2 → ℤ) 1 : ZMod p) -
          (b p : ZMod p) * ((x : Fin 2 → ℤ) 0 : ZMod p) = 0 := by
        simpa [ha0, hb0] using heq
      exact sub_eq_zero.mp hsub

/-- If `p` divides both integer coordinates, it divides their sup height. -/
theorem dvd_intSupHeight2_of_dvd_coords {p : ℕ} {x : Fin 2 → ℤ}
    (h0 : p ∣ (x 0).natAbs) (h1 : p ∣ (x 1).natAbs) :
    p ∣ intSupHeight2 x := by
  unfold intSupHeight2
  by_cases hle : (x 0).natAbs ≤ (x 1).natAbs
  · rw [max_eq_right hle]
    exact h1
  · rw [max_eq_left (Nat.le_of_not_ge hle)]
    exact h0

/-- A nonzero coordinate modulo `p` can cancel from a product equality. -/
theorem zmod_cross_eq_of_two_ratio_equations
    {p : ℕ} [Fact p.Prime]
    {A B a b : ℕ} {j l : ZMod p}
    (hrat : (A : ZMod p) * l = (B : ZMod p) * j)
    (hlabel : (a : ZMod p) * l = (b : ZMod p) * j)
    (hnonzero : j ≠ 0 ∨ l ≠ 0) :
    (a : ZMod p) * (B : ZMod p) = (b : ZMod p) * (A : ZMod p) := by
  rcases hnonzero with hj | hl
  · apply mul_right_cancel₀ hj
    calc
      ((a : ZMod p) * (B : ZMod p)) * j =
          (a : ZMod p) * ((B : ZMod p) * j) := by ring
      _ = (a : ZMod p) * ((A : ZMod p) * l) := by rw [← hrat]
      _ = (A : ZMod p) * ((a : ZMod p) * l) := by ring
      _ = (A : ZMod p) * ((b : ZMod p) * j) := by rw [hlabel]
      _ = ((b : ZMod p) * (A : ZMod p)) * j := by ring
  · apply mul_right_cancel₀ hl
    calc
      ((a : ZMod p) * (B : ZMod p)) * l =
          (B : ZMod p) * ((a : ZMod p) * l) := by ring
      _ = (B : ZMod p) * ((b : ZMod p) * j) := by rw [hlabel]
      _ = (b : ZMod p) * ((B : ZMod p) * j) := by ring
      _ = (b : ZMod p) * ((A : ZMod p) * l) := by rw [← hrat]
      _ = ((b : ZMod p) * (A : ZMod p)) * l := by ring

/-- If a selected lattice vector lies on a small exact rational line and its
height is not divisible by `p`, then the actual root-label pair at `p` lies on
that same exact line. -/
theorem rational_lattice_vector_forces_compatible_label
    (P F : Finset ℕ) (a b : ℕ → ℕ) {K A B L p : ℕ}
    (hFP : F ⊆ P)
    (hzeroF : bothZeroLabelPrimes P a b ⊆ F)
    (hprime : ∀ r ∈ P, r.Prime)
    (ha : ∀ r ∈ P, a r < K) (hb : ∀ r ∈ P, b r < K)
    (hKp : K * K < p) (hpP : p ∈ P)
    (x : globalForcedPairLattice P F a b hFP)
    (hL : L = intSupHeight2 (x : Fin 2 → ℤ))
    (hAK : A < K) (hBK : B < K) (hAB : A ≠ 0 ∨ B ≠ 0)
    (hrat : (A : ℤ) * (x : Fin 2 → ℤ) 1 =
      (B : ℤ) * (x : Fin 2 → ℤ) 0)
    (hpL : ¬p ∣ L) :
    (a p, b p) ∈ compatibleRatioLabels K A B := by
  have hp : p.Prime := hprime p hpP
  letI : Fact p.Prime := ⟨hp⟩
  have hpF : p ∉ F := by
    intro hpFin
    have hfac := forced_pair_lattice_coordinates_factor P F a b hFP hprime x
    obtain ⟨j, l, hj, hl⟩ := hfac
    have hpE : p ∣ primeProduct F := by
      unfold primeProduct
      exact Finset.dvd_prod_of_mem (fun r : ℕ ↦ r) hpFin
    have h0 : p ∣ ((x : Fin 2 → ℤ) 0).natAbs := by
      rw [hj, Int.natAbs_mul, Int.natAbs_natCast]
      exact dvd_mul_of_dvd_left hpE _
    have h1 : p ∣ ((x : Fin 2 → ℤ) 1).natAbs := by
      rw [hl, Int.natAbs_mul, Int.natAbs_natCast]
      exact dvd_mul_of_dvd_left hpE _
    exact hpL (hL ▸ dvd_intSupHeight2_of_dvd_coords h0 h1)
  have hlabel := forced_pair_lattice_unforced_equation P F a b hFP
    hzeroF x hpP hpF
  have hratZ : (A : ZMod p) * ((x : Fin 2 → ℤ) 1 : ZMod p) =
      (B : ZMod p) * ((x : Fin 2 → ℤ) 0 : ZMod p) := by
    have hz := congrArg (fun z : ℤ ↦ (z : ZMod p)) hrat
    simpa only [Int.cast_mul, Int.cast_natCast] using hz
  have hcoordNZ : ((x : Fin 2 → ℤ) 0 : ZMod p) ≠ 0 ∨
      ((x : Fin 2 → ℤ) 1 : ZMod p) ≠ 0 := by
    by_contra hz
    push Not at hz
    have h0int : (p : ℤ) ∣ (x : Fin 2 → ℤ) 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz.1
    have h1int : (p : ℤ) ∣ (x : Fin 2 → ℤ) 1 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz.2
    have h0 : p ∣ ((x : Fin 2 → ℤ) 0).natAbs := by
      simpa using (Int.natAbs_dvd_natAbs.mpr h0int)
    have h1 : p ∣ ((x : Fin 2 → ℤ) 1).natAbs := by
      simpa using (Int.natAbs_dvd_natAbs.mpr h1int)
    exact hpL (hL ▸ dvd_intSupHeight2_of_dvd_coords h0 h1)
  have hcross : (a p : ZMod p) * (B : ZMod p) =
      (b p : ZMod p) * (A : ZMod p) :=
    zmod_cross_eq_of_two_ratio_equations hratZ hlabel hcoordNZ
  have haB : a p * B < p := by
    have haK := ha p hpP
    by_cases hB0 : B = 0
    · simp [hB0, hp.pos]
    · exact (Nat.mul_lt_mul_of_pos_right haK (Nat.pos_of_ne_zero hB0)).trans
        ((Nat.mul_lt_mul_of_pos_left hBK (by omega)).trans hKp)
  have hbA : b p * A < p := by
    have hbK := hb p hpP
    by_cases hA0 : A = 0
    · simp [hA0, hp.pos]
    · exact (Nat.mul_lt_mul_of_pos_right hbK (Nat.pos_of_ne_zero hA0)).trans
        ((Nat.mul_lt_mul_of_pos_left hAK (by omega)).trans hKp)
  have hexact : a p * B = b p * A := by
    have hcross' : ((a p * B : ℕ) : ZMod p) =
        ((b p * A : ℕ) : ZMod p) := by
      push_cast
      exact hcross
    have hv := congrArg ZMod.val hcross'
    rw [ZMod.val_natCast_of_lt haB, ZMod.val_natCast_of_lt hbA] at hv
    exact hv
  apply Finset.mem_filter.mpr
  constructor
  · simp only [nonzeroLabelPairs, Finset.mem_erase, ne_eq,
      Finset.mem_product, Finset.mem_range]
    refine ⟨?_, ha p hpP, hb p hpP⟩
    intro hz
    have hab0 : a p = 0 ∧ b p = 0 := by
      simpa [Prod.ext_iff] using hz
    exact hpF (hzeroF (Finset.mem_filter.mpr ⟨hpP, hab0⟩))
  · exact hexact

end Erdos394
