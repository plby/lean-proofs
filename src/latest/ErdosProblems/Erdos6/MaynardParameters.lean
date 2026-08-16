import BoundedGaps.Maynard.ConcreteParameters

/-!
# Tuple-generic Maynard parameters for Erdős Problem 6

The bundled bounded-gaps proof freezes the final parameter family at the
105-element Engelsma tuple.  The arithmetic cutoff itself is independent of
that tuple.  This file records the tuple-generic normalization, pre-sieve
residue, and eventual coverage facts needed for the four-prime version.
-/

namespace Erdos6.Maynard

open Filter

noncomputable section

/-- A uniform upper bound for all entries, hence for all pairwise distances,
of a finite tuple. -/
def tupleBound (H : Finset ℕ) : ℕ := H.sup id

theorem mem_le_tupleBound {H : Finset ℕ} {h : ℕ} (hh : h ∈ H) :
    h ≤ tupleBound H := by
  exact Finset.le_sup (f := id) hh

theorem tuple_shiftDiameterBound (H : Finset ℕ) :
    BoundedGaps.Maynard.ShiftDiameterBound H (tupleBound H) := by
  intro a b hab
  have ha : a.1 ≤ tupleBound H := mem_le_tupleBound a.2
  have hb : b.1 ≤ tupleBound H := mem_le_tupleBound b.2
  unfold Nat.dist
  omega

/-- The standard triple-log primorial eventually contains every prime which
can divide a difference of two shifts in the fixed tuple. -/
theorem eventually_tuple_coverage (H : Finset ℕ) :
    ∀ᶠ N : ℕ in atTop,
      BoundedGaps.Maynard.CoversShiftDifferencePrimes H
        (BoundedGaps.Maynard.engelsmaMaynardModulus N) := by
  obtain ⟨N₀, hN₀⟩ :=
    BoundedGaps.Maynard.exists_tripleLogCutoff_ge (tupleBound H)
  filter_upwards [eventually_ge_atTop (N₀ + 1)] with N hN
  unfold BoundedGaps.Maynard.engelsmaMaynardModulus
  apply BoundedGaps.Maynard.coversShiftDifferencePrimes_of_diameter
  intro a b hab
  exact (tuple_shiftDiameterBound H hab).trans (hN₀ (N - 1) (by omega))

/-- A chosen admissible residue modulo the standard pre-sieve modulus. -/
noncomputable def preSieveResidue (H : Finset ℕ)
    (hH : BoundedGaps.IsAdmissible H) (N : ℕ) : ℕ :=
  Classical.choose
    (BoundedGaps.Maynard.exists_preSieveResidueClass_primorial hH
      (BoundedGaps.Maynard.tripleLogCutoff (N - 1)))

theorem preSieveResidue_spec (H : Finset ℕ)
    (hH : BoundedGaps.IsAdmissible H) (N : ℕ) :
    preSieveResidue H hH N <
        BoundedGaps.Maynard.engelsmaMaynardModulus N ∧
      ∀ h ∈ H, Nat.Coprime (preSieveResidue H hH N + h)
        (BoundedGaps.Maynard.engelsmaMaynardModulus N) := by
  exact Classical.choose_spec
    (BoundedGaps.Maynard.exists_preSieveResidueClass_primorial hH
      (BoundedGaps.Maynard.tripleLogCutoff (N - 1)))

theorem preSieveResidue_lt (H : Finset ℕ)
    (hH : BoundedGaps.IsAdmissible H) (N : ℕ) :
    preSieveResidue H hH N <
      BoundedGaps.Maynard.engelsmaMaynardModulus N :=
  (preSieveResidue_spec H hH N).1

theorem preSieveResidue_coprime (H : Finset ℕ)
    (hH : BoundedGaps.IsAdmissible H) (N : ℕ)
    {h : ℕ} (hh : h ∈ H) :
    Nat.Coprime (preSieveResidue H hH N + h)
      (BoundedGaps.Maynard.engelsmaMaynardModulus N) :=
  (preSieveResidue_spec H hH N).2 h hh

/-- The tuple-generic Maynard main-term scale. -/
noncomputable def maynardScale (H : Finset ℕ) (alpha : ℝ) (N : ℕ) : ℝ :=
  BoundedGaps.Maynard.maynardSieveScale H.card
    (BoundedGaps.Maynard.engelsmaMaynardModulus N) N
    (BoundedGaps.Maynard.engelsmaMaynardRealRadius alpha N)

theorem eventually_maynardScale_pos (H : Finset ℕ)
    {alpha : ℝ} (halpha : 0 < alpha) :
    ∀ᶠ N : ℕ in atTop, 0 < maynardScale H alpha N := by
  filter_upwards [eventually_ge_atTop 3] with N hN
  apply BoundedGaps.Maynard.maynardSieveScale_pos
  · exact primorial_pos (BoundedGaps.Maynard.tripleLogCutoff (N - 1))
  · omega
  · apply BoundedGaps.Maynard.maynardRealCutoff_gt_one
    · omega
    · exact halpha

end

end Erdos6.Maynard
