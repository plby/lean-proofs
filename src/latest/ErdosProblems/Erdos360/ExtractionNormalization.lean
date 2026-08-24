/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos360.PrimeRandomAssembly

/-!
# Exact random-pool normalization after divisor extraction

Divisor extraction supplies a quotient set `Z` with a lower cardinal bound
and diversity only through a finite cutoff.  The random-pool theorem, on the
other hand, asks for an ambient set whose cardinality is an exact multiple of
the number of cells.  This file records the lossless normalization used in the
CFP argument.

We delete precisely `Z.card % h` points.  Thus fewer than `h` points are lost,
the retained set has cardinality `h * (Z.card / h)`, and cutoff diversity loses
at most `h - 1`.  Crucially, the discarded points are not discarded from the
terminal Lev set: the `post_partition` estimate below is still stated with
`Z.card`.  Hence the R9 unused-mass term suffers no rounding loss.
-/

namespace Erdos360

open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- The deterministic exact-multiple ambient set used for random sampling. -/
noncomputable def extractionNormalizedAmbient (Z : Finset ℕ) (h : ℕ) :
    Finset ℕ :=
  lowerPart Z (Z.card % h)

lemma extractionNormalizedAmbient_subset (Z : Finset ℕ) (h : ℕ) :
    extractionNormalizedAmbient Z h ⊆ Z := by
  exact lowerPart_subset Z _

lemma extractionNormalizedAmbient_card
    {Z : Finset ℕ} {h : ℕ} (hh : 0 < h) :
    (extractionNormalizedAmbient Z h).card = h * (Z.card / h) := by
  simpa [extractionNormalizedAmbient] using
    lowerPart_mod_card (Z := Z) hh

/-- Exact normalization deletes fewer than one cell count. -/
lemma extractionNormalizedAmbient_discarded_card_lt
    {Z : Finset ℕ} {h : ℕ} (hh : 0 < h) :
    (Z \ extractionNormalizedAmbient Z h).card < h := by
  rw [extractionNormalizedAmbient, card_sdiff_lowerPart]
  exact (min_le_left _ _).trans_lt (Nat.mod_lt _ hh)

/-- A lower bound for `Z.card`, with the explicit `h-1` rounding reserve,
implies the cardinal room needed after exact-multiple normalization. -/
lemma extractionNormalizedAmbient_card_room
    {Z : Finset ℕ} {h q : ℕ} (hh : 0 < h)
    (hroom : q + (h - 1) ≤ Z.card) :
    q ≤ (extractionNormalizedAmbient Z h).card := by
  rw [extractionNormalizedAmbient_card hh]
  have hmod : Z.card % h ≤ h - 1 := by
    have := Nat.mod_lt Z.card hh
    omega
  have hdecomp : Z.card = Z.card % h + h * (Z.card / h) := by
    omega
  omega

/-- Cutoff diversity upgrades to honest diversity after exact normalization.
For moduli above the cutoff, positivity and the ambient interval bound control
the number of divisible elements. -/
lemma extractionNormalizedAmbient_diverse
    {Z : Finset ℕ} {h k k₀ M N : ℕ}
    (hh : 0 < h)
    (htrim : k + (h - 1) ≤ k₀)
    (hroom : k + N / (M + 1) + (h - 1) ≤ Z.card)
    (hZrange : Z ⊆ Finset.Icc 1 N)
    (hdiverse : RandomDiversity.DiverseUpTo Z k₀ M) :
    DiverseSampling.DiverseNat (extractionNormalizedAmbient Z h) k := by
  apply diverse_lowerPart_of_cutoff
      (r := Z.card % h) (R := h - 1) (k₀ := k₀)
      (M := M) (N := N)
  · have := Nat.mod_lt Z.card hh
    omega
  · exact htrim
  · simpa [extractionNormalizedAmbient] using
      extractionNormalizedAmbient_card_room (Z := Z) (h := h)
        (q := k + N / (M + 1)) hh hroom
  · exact hZrange
  · exact hdiverse

/-- Normalize a divisor-extraction quotient and feed it directly to the
checked random-partition interface.  No exact cardinality hypothesis on `Z`
is required.  The final unused-mass inequality retains `Z.card`, including
the fewer-than-`h` points deleted from the sampling ambient. -/
noncomputable def randomPreLevInput_of_extraction_normalization
    {n d y : ℕ} {Z : Finset ℕ}
    (h ell k k₀ M diversity nzero diameter : ℕ)
    (hh : 0 < h)
    (hZrange : Z ⊆ Finset.Icc 1 (2 * y / d))
    (hdiverse : RandomDiversity.DiverseUpTo Z k₀ M)
    (htrim : k + (h - 1) ≤ k₀)
    (hroom : k + (2 * y / d) / (M + 1) + (h - 1) ≤ Z.card)
    (hcount : ell + 2 ≤ h)
    (hprobability : ∀ i < ell,
      RandomDiversity.exactSplitFailureMass (2 * y / d)
        (Z.card / h) (h - i)
        (RandomDiversity.residualDiversity k h i) < 1)
    (hdiversity : ∀ i < ell,
      diversity ≤ RandomDiversity.residualDiversity k h i /
        (2 * (h - i)))
    (hordinary : ∀ P : Finset ℕ,
      P ⊆ extractionNormalizedAmbient Z h → P.card = Z.card / h →
      DiverseSampling.DiverseNat P diversity →
      Nonempty (CFPOrdinaryGrowthCertificate P nzero diameter))
    (hnzero : 3 ≤ nzero)
    (hlev : 2 * ((diameter - 1) ⌈/⌉ (nzero - 2)) ≤ ell)
    (hwidth : 2 * y ≤ ell * (nzero - 1) + 1)
    (hsum : ell * (Z.card / h) * (2 * y / d) < n / d)
    (hunused : n / d ≤
      (y / d + 1) * (Z.card - ell * (Z.card / h)))
    (hZnonempty : Z.Nonempty) :
    CFPRandomPreLevInput n d y Z := by
  let A := extractionNormalizedAmbient Z h
  have hAcard : A.card = h * (Z.card / h) := by
    simpa [A] using extractionNormalizedAmbient_card (Z := Z) hh
  have hAdiverse : DiverseSampling.DiverseNat A k := by
    simpa [A] using extractionNormalizedAmbient_diverse
      (Z := Z) (h := h) (k := k) (k₀ := k₀) (M := M)
      (N := 2 * y / d) hh htrim hroom hZrange hdiverse
  exact
    { A := A
      k := k
      N := 2 * y / d
      h := h
      s := Z.card / h
      ell := ell
      diversity := diversity
      nzero := nzero
      diameter := diameter
      A_subset := by
        simpa [A] using extractionNormalizedAmbient_subset Z h
      count_room := hcount
      card_A := hAcard
      diverse_A := hAdiverse
      range_A := by
        intro a ha
        exact Finset.mem_Icc.mp (hZrange
          (extractionNormalizedAmbient_subset Z h (by simpa [A] using ha)))
      probability_ledger := hprobability
      diversity_ledger := hdiversity
      ordinary := by
        simpa [A] using hordinary
      nzero_ge := hnzero
      lev_multiplicity := hlev
      dyadic_width := hwidth
      post_partition := by
        intro parts hparts
        constructor
        · exact (sum_levFamilyUnion_le_of_randomParts hparts
            (fun a ha ↦ (Finset.mem_Icc.mp
              (hZrange (extractionNormalizedAmbient_subset Z h
                (by simpa [A] using ha)))).2)).trans_lt hsum
        · rw [card_levFamilyUnion_of_randomParts hparts]
          exact hunused
      Z_nonempty := hZnonempty }

/-- Direct divisor-extraction form of the normalization connector.  The
source estimate `L + K * e` supplies the uniform cutoff diversity
`L + 2*K`; exact-multiple rounding is then paid for by the displayed
`h-1` reserve in the cardinal lower bound. -/
noncomputable def randomPreLevInput_of_divisorExtraction_normalization
    {n d y B L K : ℕ} {Z : Finset ℕ}
    (h ell k M diversity nzero diameter : ℕ)
    (hh : 0 < h)
    (hZrange : Z ⊆ Finset.Icc 1 (2 * y / d))
    (hcutoff : d * M ≤ B)
    (hdiverse : ∀ e : ℕ, 1 < e → d * e ≤ B →
      L + K * e ≤ (Z.filter fun z ↦ ¬e ∣ z).card)
    (htrim : k + (h - 1) ≤ L + 2 * K)
    (hroom : k + (2 * y / d) / (M + 1) + (h - 1) ≤ Z.card)
    (hcount : ell + 2 ≤ h)
    (hprobability : ∀ i < ell,
      RandomDiversity.exactSplitFailureMass (2 * y / d)
        (Z.card / h) (h - i)
        (RandomDiversity.residualDiversity k h i) < 1)
    (hdiversity : ∀ i < ell,
      diversity ≤ RandomDiversity.residualDiversity k h i /
        (2 * (h - i)))
    (hordinary : ∀ P : Finset ℕ,
      P ⊆ extractionNormalizedAmbient Z h → P.card = Z.card / h →
      DiverseSampling.DiverseNat P diversity →
      Nonempty (CFPOrdinaryGrowthCertificate P nzero diameter))
    (hnzero : 3 ≤ nzero)
    (hlev : 2 * ((diameter - 1) ⌈/⌉ (nzero - 2)) ≤ ell)
    (hwidth : 2 * y ≤ ell * (nzero - 1) + 1)
    (hsum : ell * (Z.card / h) * (2 * y / d) < n / d)
    (hunused : n / d ≤
      (y / d + 1) * (Z.card - ell * (Z.card / h)))
    (hZnonempty : Z.Nonempty) :
    CFPRandomPreLevInput n d y Z := by
  apply randomPreLevInput_of_extraction_normalization
      (h := h) (ell := ell) (k := k) (k₀ := L + 2 * K)
      (M := M) (diversity := diversity) (nzero := nzero)
      (diameter := diameter) hh hZrange
      (RandomDiversity.strongDiverseUpTo_of_divisorExtraction
        hcutoff hdiverse) htrim hroom hcount hprobability hdiversity
      hordinary hnzero hlev hwidth hsum hunused hZnonempty

end Erdos360

#print axioms Erdos360.randomPreLevInput_of_extraction_normalization
#print axioms Erdos360.randomPreLevInput_of_divisorExtraction_normalization
