/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos360.FiniteSourceAssembly

/-!
# Fixed-size random pools inside an oversized extracted class

The ambient class returned by divisor extraction can be much larger than the
scale required by the R8 upper-sum estimate.  Taking one fixed fraction of
that class is therefore inappropriate.  The normalization in this file fixes
the size `s` of every random pool first and sets the number of available cells
to `Z.card / s`.

Only `Z.card % s < s` points are removed in order to obtain an exact multiple
of `s`.  Thus the diversity loss is bounded by `s - 1`, independently of how
large `Z` is.  The selected union has exactly `ell * s` elements, while the
unused-mass estimate continues to use all of `Z.card`; this is the form needed
by R8 and R9.
-/

namespace Erdos360

open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- Exact-multiple ambient set for pools of a prescribed cardinality `s`. -/
noncomputable def prescribedPoolAmbient (Z : Finset ℕ) (s : ℕ) :
    Finset ℕ :=
  lowerPart Z (Z.card % s)

lemma prescribedPoolAmbient_subset (Z : Finset ℕ) (s : ℕ) :
    prescribedPoolAmbient Z s ⊆ Z := by
  exact lowerPart_subset Z _

lemma prescribedPoolAmbient_card
    {Z : Finset ℕ} {s : ℕ} (_hs : 0 < s) :
    (prescribedPoolAmbient Z s).card = (Z.card / s) * s := by
  rw [prescribedPoolAmbient, card_lowerPart]
  have hdecomp := Nat.mod_add_div Z.card s
  rw [Nat.mul_comm s (Z.card / s)] at hdecomp
  omega

lemma prescribedPoolAmbient_discarded_card_lt
    {Z : Finset ℕ} {s : ℕ} (hs : 0 < s) :
    (Z \ prescribedPoolAmbient Z s).card < s := by
  rw [prescribedPoolAmbient, card_sdiff_lowerPart]
  exact (min_le_left _ _).trans_lt (Nat.mod_lt _ hs)

/-- Deleting the remainder modulo the prescribed pool size costs fewer than
`s` witnesses for every modulus. -/
lemma prescribedPoolAmbient_diverse
    {Z : Finset ℕ} {s k k₀ : ℕ}
    (hs : 0 < s) (htrim : k + (s - 1) ≤ k₀)
    (hdiverse : DiverseSampling.DiverseNat Z k₀) :
    DiverseSampling.DiverseNat (prescribedPoolAmbient Z s) k := by
  intro e he
  have hZ := hdiverse e he
  have hcompare := card_filter_le_lowerPart_add Z (Z.card % s)
    (fun z ↦ ¬e ∣ z)
  have hmod : Z.card % s ≤ s - 1 := by
    have := Nat.mod_lt Z.card hs
    omega
  change (Z.filter fun z ↦ ¬e ∣ z).card ≤
      ((prescribedPoolAmbient Z s).filter fun z ↦ ¬e ∣ z).card +
        Z.card % s at hcompare
  omega

private lemma card_divideMultiples_le_div_prescribed
    {A : Finset ℕ} {e N : ℕ} (he : 0 < e)
    (hA : A ⊆ Finset.Icc 1 N) :
    (divideMultiples A e).card ≤ N / e := by
  calc
    (divideMultiples A e).card ≤ (Finset.Icc 1 (N / e)).card :=
      Finset.card_le_card (divideMultiples_subset_Icc he hA)
    _ ≤ N / e := by simp

/-- Cutoff diversity similarly upgrades to honest diversity in the normalized
ambient.  Above the cutoff, the interval bound controls the divisible
elements. -/
lemma prescribedPoolAmbient_diverse_of_cutoff
    {Z : Finset ℕ} {s k k₀ M N : ℕ}
    (hs : 0 < s)
    (htrim : k + (s - 1) ≤ k₀)
    (hroom : k + N / (M + 1) + (s - 1) ≤ Z.card)
    (hZrange : Z ⊆ Finset.Icc 1 N)
    (hdiverse : RandomDiversity.DiverseUpTo Z k₀ M) :
    DiverseSampling.DiverseNat (prescribedPoolAmbient Z s) k := by
  intro e he
  by_cases heM : e ≤ M
  · have hZ := hdiverse e he heM
    have hcompare := card_filter_le_lowerPart_add Z (Z.card % s)
      (fun z ↦ ¬e ∣ z)
    have hmod : Z.card % s ≤ s - 1 := by
      have := Nat.mod_lt Z.card hs
      omega
    change (Z.filter fun z ↦ ¬e ∣ z).card ≤
        ((prescribedPoolAmbient Z s).filter fun z ↦ ¬e ∣ z).card +
          Z.card % s at hcompare
    omega
  · have hMe : M + 1 ≤ e := by omega
    have hA : prescribedPoolAmbient Z s ⊆ Finset.Icc 1 N :=
      (prescribedPoolAmbient_subset Z s).trans hZrange
    have hmul := card_divideMultiples_le_div_prescribed
      (A := prescribedPoolAmbient Z s) (e := e) (N := N) (by omega) hA
    have hdiv : N / e ≤ N / (M + 1) :=
      Nat.div_le_div_left hMe (by omega)
    have hAcard : k + N / (M + 1) ≤
        (prescribedPoolAmbient Z s).card := by
      rw [prescribedPoolAmbient, card_lowerPart]
      have := Nat.mod_lt Z.card hs
      omega
    rw [← card_sub_card_divideMultiples
      (Y := prescribedPoolAmbient Z s) (e := e) (by omega)]
    omega

/-- Cardinality of the union of pairwise-disjoint prescribed random pools. -/
lemma card_levFamilyUnion_of_prescribed_randomParts
    {A : Finset ℕ} {ell s diversity : ℕ}
    {parts : List (Finset ℕ)}
    (h : IsCFPRandomParts A ell s diversity parts) :
    (levFamilyUnion parts).card = ell * s := by
  have haux : ∀ (ps : List (Finset ℕ)),
      ps.Pairwise (fun P Q ↦ Disjoint P Q) →
      (∀ P ∈ ps, P.card = s) →
      (levFamilyUnion ps).card = ps.length * s := by
    intro ps
    induction ps with
    | nil => simp [levFamilyUnion]
    | cons P ps ih =>
        intro hpairwise hcard
        have hpairwise' := hpairwise
        rw [List.pairwise_cons] at hpairwise'
        have hdisjoint : Disjoint P (levFamilyUnion ps) :=
          disjoint_levFamilyUnion_of_pairwise hpairwise
        simp only [levFamilyUnion]
        rw [Finset.card_union_of_disjoint hdisjoint,
          hcard P (by simp), ih hpairwise'.2]
        · simp [Nat.add_mul, Nat.add_comm]
        · intro Q hQ
          exact hcard Q (by simp [hQ])
  rw [haux parts h.2.1 (fun P hP ↦ (h.2.2 P hP).2.1), h.1]

/-- The union sum is controlled by its exact fixed cardinality, independently
of the cardinality of the oversized ambient set. -/
lemma sum_levFamilyUnion_le_of_prescribed_randomParts
    {A : Finset ℕ} {ell s diversity N : ℕ}
    {parts : List (Finset ℕ)}
    (h : IsCFPRandomParts A ell s diversity parts)
    (hA : ∀ a ∈ A, a ≤ N) :
    ∑ z ∈ levFamilyUnion parts, z ≤ ell * s * N := by
  have hsubset : levFamilyUnion parts ⊆ A := by
    apply levFamilyUnion_subset
    intro P hP
    exact (h.2.2 P hP).1
  calc
    ∑ z ∈ levFamilyUnion parts, z ≤
        ∑ _z ∈ levFamilyUnion parts, N := by
      apply Finset.sum_le_sum
      intro z hz
      exact hA z (hsubset hz)
    _ = (levFamilyUnion parts).card * N := by simp
    _ = ell * s * N := by
      rw [card_levFamilyUnion_of_prescribed_randomParts h]

/-- Select `ell` disjoint pools of the prescribed size `s` from an arbitrarily
large `Z`.  The effective number of cells is `Z.card / s`; in particular the
selected union and unused complement are exactly the quantities occurring in
R8 and R9. -/
theorem exists_disjoint_prescribedCard_diverse_pieces
    {Z : Finset ℕ} {s ell k k₀ N diversity : ℕ}
    (hs : 0 < s)
    (hcount : ell + 2 ≤ Z.card / s)
    (hdiverse : DiverseSampling.DiverseNat Z k₀)
    (htrim : k + (s - 1) ≤ k₀)
    (hZrange : ∀ z ∈ Z, 0 < z ∧ z ≤ N)
    (hprobability : ∀ i < ell,
      RandomDiversity.exactSplitFailureMass N s (Z.card / s - i)
        (RandomDiversity.residualDiversity k (Z.card / s) i) < 1)
    (hdiversity : ∀ i < ell,
      diversity ≤ RandomDiversity.residualDiversity k (Z.card / s) i /
        (2 * (Z.card / s - i))) :
    ∃ parts : List (Finset ℕ),
      IsCFPRandomParts Z ell s diversity parts ∧
      (levFamilyUnion parts).card = ell * s ∧
      (Z \ levFamilyUnion parts).card = Z.card - ell * s := by
  let A := prescribedPoolAmbient Z s
  have hAcard : A.card = (Z.card / s) * s := by
    simpa [A] using prescribedPoolAmbient_card (Z := Z) hs
  have hAdiverse : DiverseSampling.DiverseNat A k := by
    simpa [A] using prescribedPoolAmbient_diverse hs htrim hdiverse
  have hArange : ∀ z ∈ A, 0 < z ∧ z ≤ N := by
    intro z hz
    exact hZrange z (prescribedPoolAmbient_subset Z s (by
      simpa [A] using hz))
  obtain ⟨parts, hlength, hpairwise, hparts⟩ :=
    RandomDiversity.exists_disjoint_fixedCard_diverse_pieces
      hcount hAcard hAdiverse hArange hprobability hdiversity
  have hpartsZ : ∀ P ∈ parts,
      P ⊆ Z ∧ P.card = s ∧
        DiverseSampling.DiverseNat P diversity := by
    intro P hP
    exact ⟨(hparts P hP).1.trans (prescribedPoolAmbient_subset Z s),
      (hparts P hP).2⟩
  have hrandom : IsCFPRandomParts Z ell s diversity parts :=
    ⟨hlength, hpairwise, hpartsZ⟩
  refine ⟨parts, hrandom,
    card_levFamilyUnion_of_prescribed_randomParts hrandom, ?_⟩
  rw [Finset.card_sdiff_of_subset]
  · rw [card_levFamilyUnion_of_prescribed_randomParts hrandom]
  · apply levFamilyUnion_subset
    intro P hP
    exact (hpartsZ P hP).1

/-- Constructor for the existing pre-Lev interface with a prescribed pool
size.  This is the direct replacement for constructors which set
`s = Z.card / h`: R8 depends on `ell * s`, while R9 retains the full
`Z.card - ell * s`. -/
noncomputable def randomPreLevInput_of_prescribed_pool_size
    {n d y : ℕ} {Z : Finset ℕ}
    (s ell k k₀ M diversity nzero diameter : ℕ)
    (hs : 0 < s)
    (hZrange : Z ⊆ Finset.Icc 1 (2 * y / d))
    (hcutoffDiverse : RandomDiversity.DiverseUpTo Z k₀ M)
    (htrim : k + (s - 1) ≤ k₀)
    (hroom : k + (2 * y / d) / (M + 1) + (s - 1) ≤ Z.card)
    (hcount : ell + 2 ≤ Z.card / s)
    (hprobability : ∀ i < ell,
      RandomDiversity.exactSplitFailureMass (2 * y / d) s
        (Z.card / s - i)
        (RandomDiversity.residualDiversity k (Z.card / s) i) < 1)
    (hdiversity : ∀ i < ell,
      diversity ≤ RandomDiversity.residualDiversity k (Z.card / s) i /
        (2 * (Z.card / s - i)))
    (hordinary : ∀ P : Finset ℕ,
      P ⊆ prescribedPoolAmbient Z s → P.card = s →
      DiverseSampling.DiverseNat P diversity →
      Nonempty (CFPOrdinaryGrowthCertificate P nzero diameter))
    (hnzero : 3 ≤ nzero)
    (hlev : 2 * ((diameter - 1) ⌈/⌉ (nzero - 2)) ≤ ell)
    (hwidth : 2 * y ≤ ell * (nzero - 1) + 1)
    (hsum : ell * s * (2 * y / d) < n / d)
    (hunused : n / d ≤ (y / d + 1) * (Z.card - ell * s))
    (hZnonempty : Z.Nonempty) :
    CFPRandomPreLevInput n d y Z := by
  let A := prescribedPoolAmbient Z s
  let h := Z.card / s
  have hAcard : A.card = h * s := by
    simpa [A, h] using prescribedPoolAmbient_card (Z := Z) hs
  have hAdiverse : DiverseSampling.DiverseNat A k := by
    simpa [A] using prescribedPoolAmbient_diverse_of_cutoff
      (Z := Z) (s := s) (k := k) (k₀ := k₀) (M := M)
      (N := 2 * y / d) hs htrim hroom hZrange hcutoffDiverse
  exact
    { A := A
      k := k
      N := 2 * y / d
      h := h
      s := s
      ell := ell
      diversity := diversity
      nzero := nzero
      diameter := diameter
      A_subset := by
        simpa [A] using prescribedPoolAmbient_subset Z s
      count_room := by simpa [h] using hcount
      card_A := hAcard
      diverse_A := hAdiverse
      range_A := by
        intro z hz
        exact Finset.mem_Icc.mp (hZrange
          (prescribedPoolAmbient_subset Z s (by simpa [A] using hz)))
      probability_ledger := by simpa [h] using hprobability
      diversity_ledger := by simpa [h] using hdiversity
      ordinary := by simpa [A] using hordinary
      nzero_ge := hnzero
      lev_multiplicity := hlev
      dyadic_width := hwidth
      post_partition := by
        intro parts hparts
        constructor
        · exact (sum_levFamilyUnion_le_of_prescribed_randomParts hparts
            (fun z hz ↦ (Finset.mem_Icc.mp (hZrange
              (prescribedPoolAmbient_subset Z s
                (by simpa [A] using hz)))).2)).trans_lt hsum
        · rw [card_levFamilyUnion_of_prescribed_randomParts hparts]
          exact hunused
      Z_nonempty := hZnonempty }

end Erdos360

#print axioms Erdos360.exists_disjoint_prescribedCard_diverse_pieces
#print axioms Erdos360.randomPreLevInput_of_prescribed_pool_size
