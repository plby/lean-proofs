import ErdosProblems.Erdos394.PairStateWeights

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Simultaneous selected reductions and rational/non-rational state split
-/

open Nat Finset Module Submodule

namespace Erdos394

/-- Selected reduced height, extended by the harmless value one off the valid
label box. -/
noncomputable def pairStateSelectedHeight
    (P : Finset ℕ) (K Y : ℕ)
    (hprime : ∀ p ∈ P, p.Prime) (hKp : ∀ p ∈ P, K < p)
    (f : ∀ _p : ↥P, ℕ × ℕ) : ℕ :=
  if hf : f ∈ globalLabelPairs P K then
    (chosenPairStateCountData P K Y f hf hprime hKp).height
  else 1

/-- Underlying selected first basis vector, extended by zero off the label
box. -/
noncomputable def pairStateSelectedVector
    (P : Finset ℕ) (K Y : ℕ)
    (hprime : ∀ p ∈ P, p.Prime) (hKp : ∀ p ∈ P, K < p)
    (f : ∀ _p : ↥P, ℕ × ℕ) : Fin 2 → ℤ :=
  if hf : f ∈ globalLabelPairs P K then
    ((chosenPairStateCountData P K Y f hf hprime hKp).basis 0 : Fin 2 → ℤ)
  else 0

/-- A selected vector is rational if it lies on one of the nonzero small
label lines. -/
def pairStateSelectedRational
    (P : Finset ℕ) (K Y : ℕ)
    (hprime : ∀ p ∈ P, p.Prime) (hKp : ∀ p ∈ P, K < p)
    (f : ∀ _p : ↥P, ℕ × ℕ) : Prop :=
  ∃ w : ℕ × ℕ, w ∈ nonzeroLabelPairs K ∧
    (w.1 : ℤ) * pairStateSelectedVector P K Y hprime hKp f 1 =
      (w.2 : ℤ) * pairStateSelectedVector P K Y hprime hKp f 0

/-- Chosen rational witness, with a default off the rational states. -/
noncomputable def pairStateRationalWitness
    (P : Finset ℕ) (K Y : ℕ)
    (hprime : ∀ p ∈ P, p.Prime) (hKp : ∀ p ∈ P, K < p)
    (f : ∀ _p : ↥P, ℕ × ℕ) : ℕ × ℕ := by
  classical
  exact if h : pairStateSelectedRational P K Y hprime hKp f then
    Classical.choose h
  else (0, 0)

/-- Rational selected states. -/
noncomputable def rationalPairStates
    (P : Finset ℕ) (K Y : ℕ)
    (hprime : ∀ p ∈ P, p.Prime) (hKp : ∀ p ∈ P, K < p) :
    Finset (∀ _p : ↥P, ℕ × ℕ) := by
  classical
  exact (globalLabelPairs P K).filter
    (pairStateSelectedRational P K Y hprime hKp)

/-- Non-rational selected states. -/
noncomputable def nonrationalPairStates
    (P : Finset ℕ) (K Y : ℕ)
    (hprime : ∀ p ∈ P, p.Prime) (hKp : ∀ p ∈ P, K < p) :
    Finset (∀ _p : ↥P, ℕ × ℕ) := by
  classical
  exact (globalLabelPairs P K).filter
    (fun f ↦ ¬pairStateSelectedRational P K Y hprime hKp f)

/-- On a valid state the selected height is exactly the chosen data height. -/
theorem pairStateSelectedHeight_eq
    (P : Finset ℕ) (K Y : ℕ)
    (hprime : ∀ p ∈ P, p.Prime) (hKp : ∀ p ∈ P, K < p)
    (f : ∀ _p : ↥P, ℕ × ℕ) (hf : f ∈ globalLabelPairs P K) :
    pairStateSelectedHeight P K Y hprime hKp f =
      (chosenPairStateCountData P K Y f hf hprime hKp).height := by
  simp [pairStateSelectedHeight, hf]

/-- The selected height is positive on every valid state. -/
theorem pairStateSelectedHeight_pos
    (P : Finset ℕ) (K Y : ℕ)
    (hprime : ∀ p ∈ P, p.Prime) (hKp : ∀ p ∈ P, K < p)
    (f : ∀ _p : ↥P, ℕ × ℕ) (hf : f ∈ globalLabelPairs P K) :
    0 < pairStateSelectedHeight P K Y hprime hKp f := by
  rw [pairStateSelectedHeight_eq P K Y hprime hKp f hf]
  exact (chosenPairStateCountData P K Y f hf hprime hKp).height_pos

/-- Selected vector and selected height agree by construction. -/
theorem pairStateSelectedHeight_eq_vector
    (P : Finset ℕ) (K Y : ℕ)
    (hprime : ∀ p ∈ P, p.Prime) (hKp : ∀ p ∈ P, K < p)
    (f : ∀ _p : ↥P, ℕ × ℕ) (hf : f ∈ globalLabelPairs P K) :
    pairStateSelectedHeight P K Y hprime hKp f =
      intSupHeight2 (pairStateSelectedVector P K Y hprime hKp f) := by
  rw [pairStateSelectedHeight_eq P K Y hprime hKp f hf]
  simp only [pairStateSelectedVector, dif_pos hf]
  exact (chosenPairStateCountData P K Y f hf hprime hKp).height_eq

/-- The chosen state's lattice count. -/
theorem pairStateSelected_count_le
    (P : Finset ℕ) (K Y : ℕ)
    (hprime : ∀ p ∈ P, p.Prime) (hKp : ∀ p ∈ P, K < p)
    (f : ∀ _p : ↥P, ℕ × ℕ) (hf : f ∈ globalLabelPairs P K) :
    ((latticePositiveSquare (pairStateLattice P f) Y).card : ℝ) ≤
      (Y : ℝ) ^ 2 /
        ((primeProduct P * primeProduct (pairStateZeroPrimes P f) : ℕ) : ℝ) +
      40 * ((Y : ℝ) /
        (pairStateSelectedHeight P K Y hprime hKp f : ℝ)) + 4 := by
  rw [pairStateSelectedHeight_eq P K Y hprime hKp f hf]
  exact (chosenPairStateCountData P K Y f hf hprime hKp).count_le

/-- Properties of the chosen rational witness. -/
theorem pairStateRationalWitness_spec
    (P : Finset ℕ) (K Y : ℕ)
    (hprime : ∀ p ∈ P, p.Prime) (hKp : ∀ p ∈ P, K < p)
    (f : ∀ _p : ↥P, ℕ × ℕ)
    (hrat : pairStateSelectedRational P K Y hprime hKp f) :
    pairStateRationalWitness P K Y hprime hKp f ∈ nonzeroLabelPairs K ∧
      ((pairStateRationalWitness P K Y hprime hKp f).1 : ℤ) *
          pairStateSelectedVector P K Y hprime hKp f 1 =
        ((pairStateRationalWitness P K Y hprime hKp f).2 : ℤ) *
          pairStateSelectedVector P K Y hprime hKp f 0 := by
  unfold pairStateRationalWitness
  rw [dif_pos hrat]
  exact Classical.choose_spec hrat

/-- Non-rational selected states satisfy F-058's strong forced-factor height. -/
theorem nonrational_pairState_height
    (P : Finset ℕ) (K Y Z : ℕ)
    (hprime : ∀ p ∈ P, p.Prime) (hK : 1 < K)
    (hKp : ∀ p ∈ P, K < p)
    (hlarge : ∀ p ∈ P, Z ^ (K * K) ≤ p)
    (f : ∀ _p : ↥P, ℕ × ℕ) (hf : f ∈ globalLabelPairs P K)
    (hnon : ¬pairStateSelectedRational P K Y hprime hKp f) :
    primeProduct (pairStateZeroPrimes P f) *
        Z ^ (P \ pairStateZeroPrimes P f).card ≤
      2 * K * pairStateSelectedHeight P K Y hprime hKp f := by
  let d := chosenPairStateCountData P K Y f hf hprime hKp
  let x : pairStateLattice P f := d.basis 0
  have hbnd := globalLabel_bounds hf
  have hnorat : ∀ A < K, ∀ B < K, (A ≠ 0 ∨ B ≠ 0) →
      (A : ℤ) * (x : Fin 2 → ℤ) 1 ≠ (B : ℤ) * (x : Fin 2 → ℤ) 0 := by
    intro A hAK B hBK hAB heq
    apply hnon
    refine ⟨(A, B), ?_, ?_⟩
    · simp only [nonzeroLabelPairs, Finset.mem_erase, ne_eq,
        Finset.mem_product, Finset.mem_range]
      refine ⟨?_, hAK, hBK⟩
      intro hz
      have hz' : A = 0 ∧ B = 0 :=
        ⟨congrArg Prod.fst hz, congrArg Prod.snd hz⟩
      exact hAB.elim (fun h ↦ h hz'.1) (fun h ↦ h hz'.2)
    · simpa [pairStateSelectedVector, hf, d, x] using heq
  have hheight := forced_pair_lattice_quotient_nonrational_height
    P (pairStateZeroPrimes P f) (globalLabelFirst P f)
      (globalLabelSecond P f) (Finset.filter_subset _ _) (by rfl)
      hprime hK hbnd.1 hbnd.2 hlarge x hnorat
  rw [pairStateSelectedHeight_eq P K Y hprime hKp f hf]
  rw [(chosenPairStateCountData P K Y f hf hprime hKp).height_eq]
  simpa [d, x] using hheight

/-- Rational selected states satisfy F-060's local compatible-label condition. -/
theorem rational_pairState_local_compatible
    (P : Finset ℕ) (K Y : ℕ)
    (hprime : ∀ p ∈ P, p.Prime) (hKp : ∀ p ∈ P, K < p)
    (hK2p : ∀ p ∈ P, K * K < p)
    (f : ∀ _p : ↥P, ℕ × ℕ) (hf : f ∈ globalLabelPairs P K)
    (hrat : pairStateSelectedRational P K Y hprime hKp f)
    (p : ↥P) (hpL : ¬p.val ∣
      pairStateSelectedHeight P K Y hprime hKp f) :
    f p ∈ compatibleRatioLabels K
      (pairStateRationalWitness P K Y hprime hKp f).1
      (pairStateRationalWitness P K Y hprime hKp f).2 := by
  let d := chosenPairStateCountData P K Y f hf hprime hKp
  let x : pairStateLattice P f := d.basis 0
  let w := pairStateRationalWitness P K Y hprime hKp f
  have hwspec := pairStateRationalWitness_spec P K Y hprime hKp f hrat
  have hwmem := hwspec.1
  have hwdata : w.1 < K ∧ w.2 < K ∧ (w.1 ≠ 0 ∨ w.2 ≠ 0) := by
    have hm := Finset.mem_erase.mp hwmem
    have hrange := Finset.mem_product.mp hm.2
    refine ⟨Finset.mem_range.mp hrange.1, Finset.mem_range.mp hrange.2, ?_⟩
    by_contra hz
    push Not at hz
    exact hm.1 (Prod.ext hz.1 hz.2)
  have hbnd := globalLabel_bounds hf
  have hratx : (w.1 : ℤ) * (x : Fin 2 → ℤ) 1 =
      (w.2 : ℤ) * (x : Fin 2 → ℤ) 0 := by
    simpa [pairStateSelectedVector, hf, d, x, w] using hwspec.2
  have hLx : pairStateSelectedHeight P K Y hprime hKp f =
      intSupHeight2 (x : Fin 2 → ℤ) := by
    rw [pairStateSelectedHeight_eq P K Y hprime hKp f hf]
    exact d.height_eq
  have hcompat := rational_lattice_vector_forces_compatible_label
    P (pairStateZeroPrimes P f) (globalLabelFirst P f)
      (globalLabelSecond P f) (Finset.filter_subset _ _) (by rfl)
      hprime hbnd.1 hbnd.2 (hK2p p.val p.property) p.property x hLx
      hwdata.1 hwdata.2.1 hwdata.2.2 hratx hpL
  simpa [globalLabelFirst, globalLabelSecond, p.property, w] using hcompat

end Erdos394
