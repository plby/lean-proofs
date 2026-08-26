import ErdosProblems.Erdos520.QuadraticVariationReduction
import ErdosProblems.Erdos520.ThinBlockTail

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Filter Finset MeasureTheory Set
open scoped Topology

namespace Erdos
namespace Problem520

/-!
# From localized thin-block tails to the maximal block energy

`ThinBlockTail` proves the localized estimate used in equation (26), while
`CaichReduction` performs the finite union and Borel--Cantelli argument.
This file supplies the missing deterministic bridge: outside that union, the
actual maximum of the block energies is bounded by `B * A`.

The small-energy failure below also includes the harmless `j = 0` block.
For the concrete Caich energy this term is controlled directly by `I₀` via
Parseval; keeping it explicit makes the result independent of that choice of
normalization.
-/

/-- Failure of the common small-energy condition at one scale.  The first
set handles `U₀`; the second says that one of `I₀, ..., I_J` exceeds `A`. -/
def thinBlockMaximumSmallFailure
    (d : ThinBlockData Omega) (ell : ℕ) (A B : ℝ) : Set Omega :=
  {omega | B * A ≤ d.U ell 0 omega} ∪
    {omega | ∃ j ∈ Finset.range (d.J ell + 1), A < d.I ell j omega}

/-- The precise failure event whose complement bounds all of
`U₀, ..., U_J`. -/
def thinBlockMaximumFailure
    (d : ThinBlockData Omega) (ell : ℕ) (A B : ℝ) : Set Omega :=
  thinBlockFailure (thinBlockMaximumSmallFailure d ell A B)
    (fun j => localizedThinBlockBad d ell j A B) (d.J ell)

/-- If the harmless base block satisfies `U₀ ≤ I₀`, then the common
small-energy failure is contained in a single crossing event for the running
maximum of the energies `I_j`. -/
theorem thinBlockMaximumSmallFailure_subset_energyMaxCrossing
    (d : ThinBlockData Omega) {ell : ℕ} {A B : ℝ}
    (hA : 0 ≤ A) (hB : 1 ≤ B)
    (hbase : ∀ omega, d.U ell 0 omega ≤ d.I ell 0 omega) :
    thinBlockMaximumSmallFailure d ell A B ⊆
      {omega | A ≤ caichBlockEnergyMax d.J d.I ell omega} := by
  intro omega homega
  rcases homega with hU | hI
  · have hA_BA : A ≤ B * A := by
      calc
        A = 1 * A := by ring
        _ ≤ B * A := mul_le_mul_of_nonneg_right hB hA
    exact hA_BA.trans <| hU.trans <| (hbase omega).trans <|
      Finset.le_sup' (fun j => d.I ell j omega) (by simp)
  · rcases hI with ⟨j, hj, hIj⟩
    exact hIj.le.trans <| Finset.le_sup' (fun k => d.I ell k omega) hj

/-- Measure form of the preceding containment. -/
theorem measureReal_thinBlockMaximumSmallFailure_le_energyMaxCrossing
    (ν : Measure Omega) [IsFiniteMeasure ν] (d : ThinBlockData Omega)
    {ell : ℕ} {A B : ℝ} (hA : 0 ≤ A) (hB : 1 ≤ B)
    (hbase : ∀ omega, d.U ell 0 omega ≤ d.I ell 0 omega) :
    ν.real (thinBlockMaximumSmallFailure d ell A B) ≤
      ν.real {omega | A ≤ caichBlockEnergyMax d.J d.I ell omega} :=
  measureReal_mono
    (thinBlockMaximumSmallFailure_subset_energyMaxCrossing
      d hA hB hbase)

/-- A summable running-energy crossing budget therefore supplies the common
small-energy budget needed by the maximal thin-block argument. -/
theorem summable_measureReal_thinBlockMaximumSmallFailure_of_energyMax
    (ν : Measure Omega) [IsFiniteMeasure ν]
    (d : ThinBlockData Omega) (A : ℕ → ℝ) (B : ℝ)
    (hA : ∀ ell, 0 ≤ A ell) (hB : 1 ≤ B)
    (hbase : ∀ ell omega, d.U ell 0 omega ≤ d.I ell 0 omega)
    (henergy : Summable fun ell =>
      ν.real {omega | A ell ≤ caichBlockEnergyMax d.J d.I ell omega}) :
    Summable fun ell =>
      ν.real (thinBlockMaximumSmallFailure d ell (A ell) B) := by
  exact Summable.of_nonneg_of_le (fun _ => measureReal_nonneg)
    (fun ell =>
      measureReal_thinBlockMaximumSmallFailure_le_energyMaxCrossing
        ν d (hA ell) hB (hbase ell)) henergy

/-- Outside the explicit finite failure union, every block energy is at most
`B * A`.  This is the deterministic content of equation (27). -/
theorem caichBlockEnergyMax_le_of_not_thinBlockMaximumFailure
    (d : ThinBlockData Omega) {ell : ℕ} {A B : ℝ} {omega : Omega}
    (hgood : omega ∉ thinBlockMaximumFailure d ell A B) :
    caichBlockEnergyMax d.J d.U ell omega ≤ B * A := by
  unfold caichBlockEnergyMax
  apply Finset.sup'_le
  intro j hj
  have hjle : j ≤ d.J ell := by
    simpa only [Finset.mem_range, Nat.lt_add_one_iff] using! hj
  have hsmall : omega ∉ thinBlockMaximumSmallFailure d ell A B := by
    intro hbad
    exact hgood (Or.inl hbad)
  by_cases hj0 : j = 0
  · subst j
    exact le_of_not_ge fun hU => hsmall (Or.inl hU)
  · have hjpos : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr hj0
    have hI : d.I ell (j - 1) omega ≤ A := by
      apply le_of_not_gt
      intro hlarge
      apply hsmall
      right
      refine ⟨j - 1, ?_, hlarge⟩
      simp only [Finset.mem_range]
      omega
    have hnotLocalized :
        omega ∉ localizedThinBlockBad d ell j A B := by
      intro hbad
      apply hgood
      right
      apply Set.mem_iUnion.2
      refine ⟨j - 1, Set.mem_iUnion.2 ⟨?_, ?_⟩⟩
      · simp only [Finset.mem_range]
        omega
      · simpa [Nat.sub_add_cancel hjpos] using! hbad
    exact le_of_not_ge fun hU => hnotLocalized ⟨hU, hI⟩

/-- The failure event is exactly in the generic shape already handled by the
finite-union estimate in `CaichReduction`. -/
theorem measureReal_thinBlockMaximumFailure_le
    (ν : Measure Omega) (d : ThinBlockData Omega) (ell : ℕ) (A B q : ℝ)
    (hthin : ∀ j, j ∈ Finset.range (d.J ell) →
      ν.real (localizedThinBlockBad d ell (j + 1) A B) ≤ q) :
    ν.real (thinBlockMaximumFailure d ell A B) ≤
      ν.real (thinBlockMaximumSmallFailure d ell A B) +
        (d.J ell : ℝ) * q := by
  exact measureReal_thinBlockFailure_le ν
    (thinBlockMaximumSmallFailure d ell A B)
    (fun j => localizedThinBlockBad d ell j A B) (d.J ell) q hthin

/-- Polynomially many localized `2⁻ell` tails and a summable common
small-energy failure give a summable failure budget for the actual maximum. -/
theorem summable_measureReal_thinBlockMaximumFailure
    (ν : Measure Omega) (d : ThinBlockData Omega)
    (A : ℕ → ℝ) (B D : ℝ) (K : ℕ)
    (hJ : ∀ ell, (d.J ell : ℝ) ≤ D * (ell : ℝ) ^ K)
    (hsmall : Summable fun ell =>
      ν.real (thinBlockMaximumSmallFailure d ell (A ell) B))
    (hthin : ∀ ell j, j ∈ Finset.range (d.J ell) →
      ν.real (localizedThinBlockBad d ell (j + 1) (A ell) B) ≤
        (1 / 2 : ℝ) ^ ell) :
    Summable fun ell =>
      ν.real (thinBlockMaximumFailure d ell (A ell) B) := by
  simpa only [thinBlockMaximumFailure] using!
    summable_measureReal_thinBlockFailure ν
      (fun ell => thinBlockMaximumSmallFailure d ell (A ell) B)
      (fun ell j => localizedThinBlockBad d ell j (A ell) B)
      d.J D K hJ hsmall hthin

/-- Equation (27) followed by Borel--Cantelli, now stated as the actual
maximal block-energy inequality needed in equation (29). -/
theorem ae_eventually_caichBlockEnergyMax_le
    {ν : Measure Omega} [IsFiniteMeasure ν]
    (d : ThinBlockData Omega) (A : ℕ → ℝ) (B D : ℝ) (K : ℕ)
    (hJ : ∀ ell, (d.J ell : ℝ) ≤ D * (ell : ℝ) ^ K)
    (hsmall : Summable fun ell =>
      ν.real (thinBlockMaximumSmallFailure d ell (A ell) B))
    (hthin : ∀ ell j, j ∈ Finset.range (d.J ell) →
      ν.real (localizedThinBlockBad d ell (j + 1) (A ell) B) ≤
        (1 / 2 : ℝ) ^ ell) :
    ∀ᵐ omega ∂ν, ∀ᶠ ell : ℕ in atTop,
      caichBlockEnergyMax d.J d.U ell omega ≤ B * A ell := by
  have hnot : ∀ᵐ omega ∂ν, ∀ᶠ ell : ℕ in atTop,
      omega ∉ thinBlockMaximumFailure d ell (A ell) B :=
    ae_eventually_notMem_of_summable_measureReal
      (summable_measureReal_thinBlockMaximumFailure
        ν d A B D K hJ hsmall hthin)
  filter_upwards [hnot] with omega homega
  filter_upwards [homega] with ell hell
  exact caichBlockEnergyMax_le_of_not_thinBlockMaximumFailure d hell

/-- Specialization of the preceding result to the repaired Caich threshold.
This discharges the `blockEnergyMaxGoodAtScale` input of
`QuadraticVariationReduction` from the explicit small-energy and localized
tail budgets. -/
theorem ae_eventually_blockEnergyMaxGoodAtScale_of_thinBlockTails
    {ν : Measure Omega} [IsFiniteMeasure ν]
    (d : ThinBlockData Omega) (B D : ℝ) (K Kblocks : ℕ)
    (hJ : ∀ ell, (d.J ell : ℝ) ≤ D * (ell : ℝ) ^ Kblocks)
    (hsmall : Summable fun ell =>
      ν.real (thinBlockMaximumSmallFailure d ell
        (Real.sqrt
          ((ell : ℝ) ^ 10 /
            ((ell : ℝ) * Real.log (ell : ℝ))) /
          (ell : ℝ) ^ ((K : ℝ) / 2)) B))
    (hthin : ∀ ell j, j ∈ Finset.range (d.J ell) →
      ν.real (localizedThinBlockBad d ell (j + 1)
        (Real.sqrt
          ((ell : ℝ) ^ 10 /
            ((ell : ℝ) * Real.log (ell : ℝ))) /
          (ell : ℝ) ^ ((K : ℝ) / 2)) B) ≤
        (1 / 2 : ℝ) ^ ell) :
    ∀ᵐ omega ∂ν, ∀ᶠ ell : ℕ in atTop,
      blockEnergyMaxGoodAtScale d.J d.U B K ell omega := by
  have hmax := ae_eventually_caichBlockEnergyMax_le d
      (fun ell =>
        Real.sqrt
          ((ell : ℝ) ^ 10 /
            ((ell : ℝ) * Real.log (ell : ℝ))) /
          (ell : ℝ) ^ ((K : ℝ) / 2))
      B D Kblocks hJ hsmall hthin
  filter_upwards [hmax] with omega homega
  filter_upwards [homega] with ell hell
  unfold blockEnergyMaxGoodAtScale
  simpa only [div_eq_mul_inv, mul_assoc] using! hell

end Problem520
end Erdos
