/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos360.Core

/-!
# The source-accurate modular phase bookkeeping in CFP Lemma 5.6

This source-faithful phase machine is separate from `bounded_modular_subsetSum_growth`.
That theorem uses a quarter-density phase definition.  Conlon--Fox--Pham
instead call a phase a growth phase when an *occupied* fibre has cardinality
at most a fixed threshold `Q` (in the application, `Q = y^(3/4)`).

The definitions below use the already checked remainder recursion and its
subgroup-internal subset-sum cardinality.  The final theorem is parameterized
by precisely the three estimates supplied by the adaptive choice of the next
element in the paper:

* multiplicative internal growth below half of the remaining set;
* additive internal growth above that point;
* a uniform increment in every unsaturated phase.

Everything after those interfaces -- the number of growth phases, the
saturated-fibre alternative, and the final minimum lower bound -- is proved
here.
-/

namespace Erdos360

open scoped BigOperators Pointwise

attribute [local instance] Classical.propDecidable

section Fibres

/-- If every ambient representative sees at least `L` points in its
`H`-coset fibre, then `index(H) * L` points lie in `S`.  It is stated in the
cyclic `closureModulus` coordinates used by the CFP process. -/
lemma closureModulus_mul_le_card_of_all_fibers
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R S : Finset (ZMod b)) (L : ℕ)
    (hlarge : ∀ u : ZMod b,
      L ≤ (normalizedCosetFiber
        (AddSubgroup.closure (R : Set (ZMod b))) S u).card) :
    closureModulus hb R * L ≤ S.card := by
  classical
  let H := AddSubgroup.closure (R : Set (ZMod b))
  letI : Fintype H :=
    Fintype.ofInjective (fun h : H ↦ h.1) Subtype.val_injective
  let I : Finset (Σ _u : ZMod b, H) :=
    (Finset.univ : Finset (ZMod b)).sigma fun u ↦
      normalizedCosetFiber H S u
  let J : Finset (ZMod b × H) := S ×ˢ (Finset.univ : Finset H)
  have hIJ : I.card = J.card := by
    apply Finset.card_bij'
        (fun p _ ↦ (p.1 + p.2.1, p.2))
        (fun p _ ↦ ⟨p.1 - p.2.1, p.2⟩)
    · rintro ⟨u, h⟩ hp
      simp [sub_eq_add_neg]
    · rintro ⟨s, h⟩ hp
      simp [sub_eq_add_neg]
    · intro p hp
      dsimp only [J]
      rw [Finset.mem_product]
      dsimp only [I] at hp
      have hpFiber := (Finset.mem_sigma.mp hp).2
      exact ⟨mem_normalizedCosetFiber.mp hpFiber, Finset.mem_univ _⟩
    · intro p hp
      dsimp only [I]
      rw [Finset.mem_sigma]
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [mem_normalizedCosetFiber]
      dsimp only [J] at hp
      rw [Finset.mem_product] at hp
      simpa [sub_eq_add_neg] using hp.1
  have hsum : Fintype.card (ZMod b) * L ≤ I.card := by
    calc
      Fintype.card (ZMod b) * L = ∑ _u : ZMod b, L := by simp
      _ ≤ ∑ u : ZMod b,
          (normalizedCosetFiber H S u).card := by
        exact Finset.sum_le_sum fun u _ ↦ hlarge u
      _ = I.card := by simp only [I, Finset.card_sigma]
  have hHcard : Fintype.card H = b / closureModulus hb R := by
    rw [show Fintype.card H = (H : Set (ZMod b)).ncard by
      exact Set.fintypeCard_eq_ncard (H : Set (ZMod b))]
    exact ncard_closure_eq_div_modulus hb R
  have hIcard : I.card = S.card * (b / closureModulus hb R) := by
    simp only [hIJ, J, Finset.card_product, Finset.card_univ, hHcard]
  have hqpos : 0 < closureModulus hb R := closureModulus_pos hb R
  have hquotpos : 0 < b / closureModulus hb R := by
    exact Nat.div_pos (Nat.le_of_dvd hb (closureModulus_dvd hb R)) hqpos
  have hmul :
      (closureModulus hb R * L) * (b / closureModulus hb R) ≤
        S.card * (b / closureModulus hb R) := by
    calc
      (closureModulus hb R * L) * (b / closureModulus hb R) =
          (closureModulus hb R * (b / closureModulus hb R)) * L := by
        ring
      _ = b * L := by rw [Nat.mul_div_cancel' (closureModulus_dvd hb R)]
      _ = Fintype.card (ZMod b) * L := by rw [ZMod.card]
      _ ≤ I.card := hsum
      _ = S.card * (b / closureModulus hb R) := hIcard
  exact Nat.le_of_mul_le_mul_right hmul hquotpos

end Fibres

section SourcePhases

variable {b : ℕ} [NeZero b]

/-- The current unused residue set. -/
noncomputable abbrev cfpRemainder (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀) (i : ℕ) : Finset (ZMod b) :=
  modularRemainder hb R₀ E hE hdiverse i

/-- The subgroup index `d_i` in the source proof. -/
noncomputable abbrev cfpModulus (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀) (i : ℕ) : ℕ :=
  closureModulus hb (cfpRemainder hb R₀ E hE hdiverse i)

/-- The source's `Σ(d_i,i-1)`, represented inside the subgroup generated
by the unused residues. -/
noncomputable abbrev cfpInternalCard (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀) (i : ℕ) : ℕ :=
  modularInternalCard R₀ (cfpRemainder hb R₀ E hE hdiverse i)

/-- The fibre of the already exposed subset sums in the current subgroup
coset represented by `u`. -/
noncomputable abbrev cfpFiber (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀) (i : ℕ) (u : ZMod b) :=
  normalizedCosetFiber
    (AddSubgroup.closure
      (cfpRemainder hb R₀ E hE hdiverse i : Set (ZMod b)))
    (modularPhaseSums hb R₀ E hE hdiverse i) u

/-- CFP growth phase: an occupied current coset fibre has size at most `Q`.
The paper uses `Q = y^(3/4)`. -/
noncomputable def IsCFPGrowthPhase (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀) (Q i : ℕ) : Prop :=
  ∃ u : ZMod b,
    (cfpFiber hb R₀ E hE hdiverse i u).Nonempty ∧
      (cfpFiber hb R₀ E hE hdiverse i u).card ≤ Q

/-- CFP unsaturated phase.  `sat d` is the target size of a fibre when the
current subgroup has index `d`; in the application it is the integer form of
`ξ t / d`. -/
noncomputable def IsCFPUnsaturatedPhase (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀) (Q : ℕ) (sat : ℕ → ℕ)
    (i : ℕ) : Prop :=
  ¬ IsCFPGrowthPhase hb R₀ E hE hdiverse Q i ∧
    ∃ u : ZMod b,
      (cfpFiber hb R₀ E hE hdiverse i u).Nonempty ∧
      Q < (cfpFiber hb R₀ E hE hdiverse i u).card ∧
      (cfpFiber hb R₀ E hE hdiverse i u).card <
        sat (cfpModulus hb R₀ E hE hdiverse i)

/-- The residual case in the source trichotomy. -/
noncomputable def IsCFPSaturatedPhase (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀) (Q : ℕ) (sat : ℕ → ℕ)
    (i : ℕ) : Prop :=
  ¬ IsCFPGrowthPhase hb R₀ E hE hdiverse Q i ∧
    ¬ IsCFPUnsaturatedPhase hb R₀ E hE hdiverse Q sat i

/-- Indices of source growth phases among the first `k` steps. -/
noncomputable def cfpGrowthIndices (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀) (Q k : ℕ) : Finset ℕ :=
  (Finset.range k).filter
    (IsCFPGrowthPhase hb R₀ E hE hdiverse Q)

lemma cfpModulus_dvd_of_le (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀) {i j : ℕ} (hij : i ≤ j) :
    cfpModulus hb R₀ E hE hdiverse i ∣
      cfpModulus hb R₀ E hE hdiverse j := by
  exact closureModulus_dvd_of_subset hb
    (modularRemainder_antitone hb R₀ E hE hdiverse hij)

lemma cfpModulus_eq_of_log_eq (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀) {i j : ℕ} (hij : i ≤ j)
    (hlog : Nat.log 2 (cfpModulus hb R₀ E hE hdiverse i) =
      Nat.log 2 (cfpModulus hb R₀ E hE hdiverse j)) :
    cfpModulus hb R₀ E hE hdiverse i =
      cfpModulus hb R₀ E hE hdiverse j := by
  exact eq_of_dvd_of_log_two_eq
    (closureModulus_pos hb _) (closureModulus_pos hb _)
    (cfpModulus_dvd_of_le hb R₀ E hE hdiverse hij) hlog

/-- Every source growth phase has internal subset-sum cardinality at most
the fibre threshold. -/
lemma cfpInternalCard_le_threshold_of_growth (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀) (Q : ℕ) {i : ℕ}
    (hi : 2 * i ≤ R₀.card)
    (hg : IsCFPGrowthPhase hb R₀ E hE hdiverse Q i) :
    cfpInternalCard hb R₀ E hE hdiverse i ≤ Q := by
  obtain ⟨u, huNe, huQ⟩ := hg
  let R := cfpRemainder hb R₀ E hE hdiverse i
  let H := AddSubgroup.closure (R : Set (ZMod b))
  have hiCard : i ≤ R₀.card := by omega
  have hRcard : R.card = R₀.card - i :=
    card_modularRemainder hb R₀ E hE hdiverse hiCard
  have hwide : R₀.card ≤ 2 * R.card := by rw [hRcard]; omega
  have hle := seededSubsetSum_fiber_lower H E (R₀ \ R) u huNe
  exact hle.trans huQ

/-- A saturated source phase contributes `d_i * sat(d_i)` residues. -/
lemma cfp_saturated_phase_card (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀) (Q : ℕ) (sat : ℕ → ℕ)
    {i : ℕ} (hi : 2 * i ≤ R₀.card)
    (hsat : IsCFPSaturatedPhase hb R₀ E hE hdiverse Q sat i) :
    cfpModulus hb R₀ E hE hdiverse i *
        sat (cfpModulus hb R₀ E hE hdiverse i) ≤
      (modularPhaseSums hb R₀ E hE hdiverse i).card := by
  let R := cfpRemainder hb R₀ E hE hdiverse i
  have hiCard : i ≤ R₀.card := by omega
  have hRcard : R.card = R₀.card - i :=
    card_modularRemainder hb R₀ E hE hdiverse hiCard
  have hwide : R₀.card ≤ 2 * R.card := by rw [hRcard]; omega
  have hlarge : ∀ u : ZMod b,
      sat (closureModulus hb R) ≤
        (normalizedCosetFiber (AddSubgroup.closure (R : Set (ZMod b)))
          (modularPhaseSums hb R₀ E hE hdiverse i) u).card := by
    intro u
    have huNe := normalizedCosetFiber_nonempty_of_diverse_used
      hb R₀ R E hE
        (hdiverse R
          (modularRemainder_subset_initial hb R₀ E hE hdiverse i)
          hwide) u
    by_contra hnot
    have hlt : (normalizedCosetFiber
        (AddSubgroup.closure (R : Set (ZMod b)))
        (modularPhaseSums hb R₀ E hE hdiverse i) u).card <
          sat (closureModulus hb R) := by omega
    have hnotGrowth := hsat.1
    have hQlt : Q < (normalizedCosetFiber
        (AddSubgroup.closure (R : Set (ZMod b)))
        (modularPhaseSums hb R₀ E hE hdiverse i) u).card := by
      by_contra hnotQ
      apply hnotGrowth
      refine ⟨u, ?_, ?_⟩
      · simpa [cfpFiber, cfpRemainder, modularPhaseSums, R] using huNe
      · simpa [cfpFiber, cfpRemainder, modularPhaseSums, R] using
          (show (normalizedCosetFiber
            (AddSubgroup.closure (R : Set (ZMod b)))
            (modularPhaseSums hb R₀ E hE hdiverse i) u).card ≤ Q by
              omega)
    apply hsat.2
    refine ⟨hnotGrowth, u, ?_, ?_, ?_⟩
    · simpa [cfpFiber, cfpRemainder, modularPhaseSums, R] using huNe
    · simpa [cfpFiber, cfpRemainder, modularPhaseSums, R] using hQlt
    · simpa [cfpFiber, cfpRemainder, cfpModulus,
        modularPhaseSums, R] using hlt
  exact closureModulus_mul_le_card_of_all_fibers hb R
    (modularPhaseSums hb R₀ E hE hdiverse i)
    (sat (closureModulus hb R)) hlarge

/-! ## Counting growth phases

The source proof has two internal-growth regimes.  Below half the remaining
set the internal subset-sum set grows by a factor `3/2`; above half it gains
at least a fixed amount `L` (equal to `z/(256ℓ)` in CFP).  The predicates
below record exactly that split.
-/

noncomputable def IsCFPSmallGrowthPhase (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀) (Q i : ℕ) : Prop :=
  IsCFPGrowthPhase hb R₀ E hE hdiverse Q i ∧
    2 * cfpInternalCard hb R₀ E hE hdiverse i <
      (cfpRemainder hb R₀ E hE hdiverse i).card

noncomputable def IsCFPLargeGrowthPhase (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀) (Q i : ℕ) : Prop :=
  IsCFPGrowthPhase hb R₀ E hE hdiverse Q i ∧
    (cfpRemainder hb R₀ E hE hdiverse i).card ≤
      2 * cfpInternalCard hb R₀ E hE hdiverse i

noncomputable def cfpSmallGrowthIndices (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀) (Q k : ℕ) : Finset ℕ :=
  (Finset.range k).filter
    (IsCFPSmallGrowthPhase hb R₀ E hE hdiverse Q)

noncomputable def cfpLargeGrowthIndices (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀) (Q k : ℕ) : Finset ℕ :=
  (Finset.range k).filter
    (IsCFPLargeGrowthPhase hb R₀ E hE hdiverse Q)

/-- Three small-growth phases cannot have both the same binary modulus
bucket and the same binary internal-cardinality bucket.  Two `3/2` gains
force an overall doubling. -/
lemma cfp_small_growth_code_not_three (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀) (Q k : ℕ)
    (hsmallStep : ∀ i < k,
      IsCFPSmallGrowthPhase hb R₀ E hE hdiverse Q i →
      cfpModulus hb R₀ E hE hdiverse i =
        cfpModulus hb R₀ E hE hdiverse (i + 1) →
      3 * cfpInternalCard hb R₀ E hE hdiverse i ≤
        2 * cfpInternalCard hb R₀ E hE hdiverse (i + 1))
    {i j r : ℕ} (hij : i < j) (hjr : j < r) (hrk : r < k)
    (hgi : IsCFPSmallGrowthPhase hb R₀ E hE hdiverse Q i)
    (hgj : IsCFPSmallGrowthPhase hb R₀ E hE hdiverse Q j)
    (hqIJ : Nat.log 2 (cfpModulus hb R₀ E hE hdiverse i) =
      Nat.log 2 (cfpModulus hb R₀ E hE hdiverse j))
    (hqJR : Nat.log 2 (cfpModulus hb R₀ E hE hdiverse j) =
      Nat.log 2 (cfpModulus hb R₀ E hE hdiverse r))
    (hcIJ : Nat.log 2 (cfpInternalCard hb R₀ E hE hdiverse i) =
      Nat.log 2 (cfpInternalCard hb R₀ E hE hdiverse j))
    (hcJR : Nat.log 2 (cfpInternalCard hb R₀ E hE hdiverse j) =
      Nat.log 2 (cfpInternalCard hb R₀ E hE hdiverse r)) : False := by
  let qi := cfpModulus hb R₀ E hE hdiverse i
  let qj := cfpModulus hb R₀ E hE hdiverse j
  let qr := cfpModulus hb R₀ E hE hdiverse r
  let ci := cfpInternalCard hb R₀ E hE hdiverse i
  let cj := cfpInternalCard hb R₀ E hE hdiverse j
  let cr := cfpInternalCard hb R₀ E hE hdiverse r
  have hqEqIJ : qi = qj :=
    cfpModulus_eq_of_log_eq hb R₀ E hE hdiverse hij.le hqIJ
  have hqEqJR : qj = qr :=
    cfpModulus_eq_of_log_eq hb R₀ E hE hdiverse hjr.le hqJR
  have hqiSucc : qi = cfpModulus hb R₀ E hE hdiverse (i + 1) := by
    exact closureModulus_eq_between hb R₀ E hE hdiverse
      (by omega) (by omega) hqEqIJ
  have hqjSucc : qj = cfpModulus hb R₀ E hE hdiverse (j + 1) := by
    exact closureModulus_eq_between hb R₀ E hE hdiverse
      (by omega) (by omega) hqEqJR
  have hgrowI : 3 * ci ≤
      2 * cfpInternalCard hb R₀ E hE hdiverse (i + 1) :=
    hsmallStep i (by omega) hgi hqiSucc
  have hmonoIJ : cfpInternalCard hb R₀ E hE hdiverse (i + 1) ≤ cj := by
    exact modularInternalCard_mono_of_modulus_eq hb R₀ E hE hdiverse
      (by omega) (hqiSucc.symm.trans hqEqIJ)
  have hgrowJ : 3 * cj ≤
      2 * cfpInternalCard hb R₀ E hE hdiverse (j + 1) :=
    hsmallStep j (by omega) hgj hqjSucc
  have hmonoJR : cfpInternalCard hb R₀ E hE hdiverse (j + 1) ≤ cr := by
    exact modularInternalCard_mono_of_modulus_eq hb R₀ E hE hdiverse
      (by omega) (hqjSucc.symm.trans hqEqJR)
  have hthreeI : 3 * ci ≤ 2 * cj :=
    hgrowI.trans (Nat.mul_le_mul_left 2 hmonoIJ)
  have hthreeJ : 3 * cj ≤ 2 * cr :=
    hgrowJ.trans (Nat.mul_le_mul_left 2 hmonoJR)
  have hciPos : 0 < ci := modularInternalCard_pos R₀ _
  have hdouble : 2 * ci ≤ cr := by omega
  have hloglt : Nat.log 2 ci < Nat.log 2 cr :=
    log_two_lt_of_double_le hciPos hdouble
  exact (Nat.ne_of_lt hloglt) (hcIJ.trans hcJR)

/-- Source small-growth phases are bounded by the number of modulus buckets
times the number of internal-cardinality buckets, with multiplicity at most
two in each pair of buckets. -/
theorem card_cfpSmallGrowthIndices_le (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀) (Q dMax k : ℕ)
    (hmodMax : ∀ i < k,
      cfpModulus hb R₀ E hE hdiverse i ≤ dMax)
    (hsmallStep : ∀ i < k,
      IsCFPSmallGrowthPhase hb R₀ E hE hdiverse Q i →
      cfpModulus hb R₀ E hE hdiverse i =
        cfpModulus hb R₀ E hE hdiverse (i + 1) →
      3 * cfpInternalCard hb R₀ E hE hdiverse i ≤
        2 * cfpInternalCard hb R₀ E hE hdiverse (i + 1)) :
    (cfpSmallGrowthIndices hb R₀ E hE hdiverse Q k).card ≤
      2 * (Nat.log 2 dMax + 1) * (Nat.log 2 b + 1) := by
  classical
  let G := cfpSmallGrowthIndices hb R₀ E hE hdiverse Q k
  let C := Fin (Nat.log 2 dMax + 1) × Fin (Nat.log 2 b + 1)
  let f : ℕ → C := fun i ↦
    (⟨min (Nat.log 2 (cfpModulus hb R₀ E hE hdiverse i))
        (Nat.log 2 dMax),
      Nat.lt_succ_of_le (min_le_right _ _)⟩,
     ⟨Nat.log 2 (cfpInternalCard hb R₀ E hE hdiverse i),
      Nat.lt_succ_of_le (Nat.log_mono_right
        (modularInternalCard_le R₀ _))⟩)
  by_contra hnot
  have hlarge : (Finset.univ : Finset C).card * 2 < G.card := by
    simp only [Finset.card_univ, C, Fintype.card_prod, Fintype.card_fin]
    dsimp only [G] at hnot ⊢
    have hgt : 2 * (Nat.log 2 dMax + 1) * (Nat.log 2 b + 1) <
        (cfpSmallGrowthIndices hb R₀ E hE hdiverse Q k).card :=
      Nat.lt_of_not_ge hnot
    simpa [mul_assoc, mul_left_comm, mul_comm] using hgt
  obtain ⟨y, -, hy⟩ :=
    Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
      (s := G) (t := Finset.univ) (f := f)
      (n := 2) (fun _ _ ↦ Finset.mem_univ _) hlarge
  let S := G.filter fun i ↦ f i = y
  have hScard : 2 < S.card := by simpa only [S] using hy
  obtain ⟨i, hiS, j, hjS, r, hrS, hij, hjr⟩ :=
    exists_three_ordered_of_two_lt_card hScard
  have hiG : i ∈ G := (Finset.mem_filter.mp hiS).1
  have hjG : j ∈ G := (Finset.mem_filter.mp hjS).1
  have hrG : r ∈ G := (Finset.mem_filter.mp hrS).1
  have hfi : f i = y := (Finset.mem_filter.mp hiS).2
  have hfj : f j = y := (Finset.mem_filter.mp hjS).2
  have hfr : f r = y := (Finset.mem_filter.mp hrS).2
  have hiData := Finset.mem_filter.mp hiG
  have hjData := Finset.mem_filter.mp hjG
  have hrData := Finset.mem_filter.mp hrG
  have hiMod := hmodMax i (Finset.mem_range.mp hiData.1)
  have hjMod := hmodMax j (Finset.mem_range.mp hjData.1)
  have hrMod := hmodMax r (Finset.mem_range.mp hrData.1)
  have hiLog : Nat.log 2 (cfpModulus hb R₀ E hE hdiverse i) ≤
      Nat.log 2 dMax := Nat.log_mono_right hiMod
  have hjLog : Nat.log 2 (cfpModulus hb R₀ E hE hdiverse j) ≤
      Nat.log 2 dMax := Nat.log_mono_right hjMod
  have hrLog : Nat.log 2 (cfpModulus hb R₀ E hE hdiverse r) ≤
      Nat.log 2 dMax := Nat.log_mono_right hrMod
  have hcodeIJ := congrArg (fun z : C ↦ z.1.val) (hfi.trans hfj.symm)
  have hcodeJR := congrArg (fun z : C ↦ z.1.val) (hfj.trans hfr.symm)
  have hcIJ := congrArg (fun z : C ↦ z.2.val) (hfi.trans hfj.symm)
  have hcJR := congrArg (fun z : C ↦ z.2.val) (hfj.trans hfr.symm)
  dsimp only [f] at hcodeIJ hcodeJR hcIJ hcJR
  rw [min_eq_left hiLog, min_eq_left hjLog] at hcodeIJ
  rw [min_eq_left hjLog, min_eq_left hrLog] at hcodeJR
  exact cfp_small_growth_code_not_three hb R₀ E hE hdiverse Q k
    hsmallStep hij hjr (Finset.mem_range.mp hrData.1)
    hiData.2 hjData.2 hcodeIJ hcodeJR hcIJ hcJR

/-- Above the half-way threshold, every source growth phase gains at least
`L` internal subset sums.  For a fixed binary modulus bucket, division by
`L` is therefore injective on the sequence of large-growth phases. -/
theorem card_cfpLargeGrowthIndices_le (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀) (Q dMax L k : ℕ)
    (hL : 0 < L) (hhalf : 2 * k ≤ R₀.card)
    (hmodMax : ∀ i < k,
      cfpModulus hb R₀ E hE hdiverse i ≤ dMax)
    (hlargeStep : ∀ i < k,
      IsCFPLargeGrowthPhase hb R₀ E hE hdiverse Q i →
      cfpModulus hb R₀ E hE hdiverse i =
        cfpModulus hb R₀ E hE hdiverse (i + 1) →
      L + cfpInternalCard hb R₀ E hE hdiverse i ≤
        cfpInternalCard hb R₀ E hE hdiverse (i + 1)) :
    (cfpLargeGrowthIndices hb R₀ E hE hdiverse Q k).card ≤
      (Nat.log 2 dMax + 1) * (Q / L + 1) := by
  classical
  let G := cfpLargeGrowthIndices hb R₀ E hE hdiverse Q k
  let C := Fin (Nat.log 2 dMax + 1) × Fin (Q / L + 1)
  let f : ℕ → C := fun i ↦
    (⟨min (Nat.log 2 (cfpModulus hb R₀ E hE hdiverse i))
        (Nat.log 2 dMax),
      Nat.lt_succ_of_le (min_le_right _ _)⟩,
     ⟨min (cfpInternalCard hb R₀ E hE hdiverse i / L) (Q / L),
      Nat.lt_succ_of_le (min_le_right _ _)⟩)
  have hordered : ∀ {i j : ℕ}, i ∈ G → j ∈ G → i < j → f i ≠ f j := by
    intro i j hiG hjG hij hf
    have hiData := Finset.mem_filter.mp hiG
    have hjData := Finset.mem_filter.mp hjG
    have hiRange : i < k := Finset.mem_range.mp hiData.1
    have hjRange : j < k := Finset.mem_range.mp hjData.1
    have hiMod := hmodMax i hiRange
    have hjMod := hmodMax j hjRange
    have hiLog : Nat.log 2 (cfpModulus hb R₀ E hE hdiverse i) ≤
        Nat.log 2 dMax := Nat.log_mono_right hiMod
    have hjLog : Nat.log 2 (cfpModulus hb R₀ E hE hdiverse j) ≤
        Nat.log 2 dMax := Nat.log_mono_right hjMod
    have hciQ : cfpInternalCard hb R₀ E hE hdiverse i ≤ Q :=
      cfpInternalCard_le_threshold_of_growth hb R₀ E hE hdiverse Q
        (by omega) hiData.2.1
    have hcjQ : cfpInternalCard hb R₀ E hE hdiverse j ≤ Q :=
      cfpInternalCard_le_threshold_of_growth hb R₀ E hE hdiverse Q
        (by omega) hjData.2.1
    have hiQuot : cfpInternalCard hb R₀ E hE hdiverse i / L ≤ Q / L :=
      Nat.div_le_div_right hciQ
    have hjQuot : cfpInternalCard hb R₀ E hE hdiverse j / L ≤ Q / L :=
      Nat.div_le_div_right hcjQ
    have hqLog := congrArg (fun z : C ↦ z.1.val) hf
    have hcQuot := congrArg (fun z : C ↦ z.2.val) hf
    dsimp only [f] at hqLog hcQuot
    rw [min_eq_left hiLog, min_eq_left hjLog] at hqLog
    rw [min_eq_left hiQuot, min_eq_left hjQuot] at hcQuot
    have hqEq := cfpModulus_eq_of_log_eq hb R₀ E hE hdiverse
      hij.le hqLog
    have hqiSucc : cfpModulus hb R₀ E hE hdiverse i =
        cfpModulus hb R₀ E hE hdiverse (i + 1) := by
      exact closureModulus_eq_between hb R₀ E hE hdiverse
        (by omega) (by omega) hqEq
    have hadd := hlargeStep i hiRange hiData.2 hqiSucc
    have hmono : cfpInternalCard hb R₀ E hE hdiverse (i + 1) ≤
        cfpInternalCard hb R₀ E hE hdiverse j := by
      exact modularInternalCard_mono_of_modulus_eq hb R₀ E hE hdiverse
        (by omega) (hqiSucc.symm.trans hqEq)
    have hinc : L + cfpInternalCard hb R₀ E hE hdiverse i ≤
        cfpInternalCard hb R₀ E hE hdiverse j := hadd.trans hmono
    have hdiv := Nat.div_le_div_right hinc (c := L)
    rw [show L + cfpInternalCard hb R₀ E hE hdiverse i =
        cfpInternalCard hb R₀ E hE hdiverse i + L by omega,
      Nat.add_div_right _ hL] at hdiv
    omega
  have hcard : G.card ≤ (Finset.univ : Finset C).card := by
    apply Finset.card_le_card_of_injOn f
    · intro i hi
      exact Finset.mem_univ _
    · intro i hi j hj hf
      by_contra hne
      rcases lt_or_gt_of_ne hne with hij | hji
      · exact (hordered hi hj hij) hf
      · exact (hordered hj hi hji) hf.symm
  simpa only [G, Finset.card_univ, C, Fintype.card_prod,
    Fintype.card_fin] using hcard

/-- Concrete source-phase growth count.  This is the checked analogue of
CFP Claim 1.  The binary-bucket term `2 log₂ b` is a slightly coarser
integer presentation of their `log_{3/2} t`; the additive term is the exact
`Q/L` coming from growth between `|A_{i-1}|/2` and `Q`. -/
theorem card_cfpGrowthIndices_le (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀) (Q dMax L k : ℕ)
    (hL : 0 < L) (hhalf : 2 * k ≤ R₀.card)
    (hmodMax : ∀ i < k,
      cfpModulus hb R₀ E hE hdiverse i ≤ dMax)
    (hsmallStep : ∀ i < k,
      IsCFPSmallGrowthPhase hb R₀ E hE hdiverse Q i →
      cfpModulus hb R₀ E hE hdiverse i =
        cfpModulus hb R₀ E hE hdiverse (i + 1) →
      3 * cfpInternalCard hb R₀ E hE hdiverse i ≤
        2 * cfpInternalCard hb R₀ E hE hdiverse (i + 1))
    (hlargeStep : ∀ i < k,
      IsCFPLargeGrowthPhase hb R₀ E hE hdiverse Q i →
      cfpModulus hb R₀ E hE hdiverse i =
        cfpModulus hb R₀ E hE hdiverse (i + 1) →
      L + cfpInternalCard hb R₀ E hE hdiverse i ≤
        cfpInternalCard hb R₀ E hE hdiverse (i + 1)) :
    (cfpGrowthIndices hb R₀ E hE hdiverse Q k).card ≤
      (Nat.log 2 dMax + 1) *
        (2 * (Nat.log 2 b + 1) + (Q / L + 1)) := by
  let G := cfpGrowthIndices hb R₀ E hE hdiverse Q k
  let Gsmall := cfpSmallGrowthIndices hb R₀ E hE hdiverse Q k
  let Glarge := cfpLargeGrowthIndices hb R₀ E hE hdiverse Q k
  have hpart : G ⊆ Gsmall ∪ Glarge := by
    intro i hi
    have hiData := Finset.mem_filter.mp hi
    rw [Finset.mem_union]
    by_cases hs : 2 * cfpInternalCard hb R₀ E hE hdiverse i <
        (cfpRemainder hb R₀ E hE hdiverse i).card
    · left
      change i ∈ cfpSmallGrowthIndices hb R₀ E hE hdiverse Q k
      rw [cfpSmallGrowthIndices, Finset.mem_filter]
      exact ⟨hiData.1, hiData.2, hs⟩
    · right
      change i ∈ cfpLargeGrowthIndices hb R₀ E hE hdiverse Q k
      rw [cfpLargeGrowthIndices, Finset.mem_filter]
      exact ⟨hiData.1, hiData.2, by omega⟩
  have hGS := card_cfpSmallGrowthIndices_le hb R₀ E hE hdiverse
    Q dMax k hmodMax hsmallStep
  have hGL := card_cfpLargeGrowthIndices_le hb R₀ E hE hdiverse
    Q dMax L k hL hhalf hmodMax hlargeStep
  calc
    G.card ≤ (Gsmall ∪ Glarge).card := Finset.card_le_card hpart
    _ ≤ Gsmall.card + Glarge.card := Finset.card_union_le _ _
    _ ≤ 2 * (Nat.log 2 dMax + 1) * (Nat.log 2 b + 1) +
        (Nat.log 2 dMax + 1) * (Q / L + 1) := Nat.add_le_add hGS hGL
    _ = (Nat.log 2 dMax + 1) *
        (2 * (Nat.log 2 b + 1) + (Q / L + 1)) := by ring

/-! ## Accumulating the unsaturated phases -/

noncomputable def cfpNonGrowthIndices (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀) (Q k : ℕ) : Finset ℕ :=
  (Finset.range k).filter fun i ↦
    ¬ IsCFPGrowthPhase hb R₀ E hE hdiverse Q i

lemma card_cfpNonGrowthIndices (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀) (Q k : ℕ) :
    (cfpNonGrowthIndices hb R₀ E hE hdiverse Q k).card =
      k - (cfpGrowthIndices hb R₀ E hE hdiverse Q k).card := by
  classical
  have heq : cfpNonGrowthIndices hb R₀ E hE hdiverse Q k =
      Finset.range k \ cfpGrowthIndices hb R₀ E hE hdiverse Q k := by
    ext i
    simp only [cfpNonGrowthIndices, cfpGrowthIndices,
      Finset.mem_filter, Finset.mem_sdiff, Finset.mem_range]
    tauto
  rw [heq, Finset.card_sdiff_of_subset]
  · simp
  · exact Finset.filter_subset _ _

/-- Summing a uniform gain over every nongrowth phase.  Growth phases need
only monotonicity, which is automatic for the subset-sum recursion. -/
theorem cfp_nongrowth_increment_lower (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀) (Q D k : ℕ)
    (hstep : ∀ i < k,
      ¬ IsCFPGrowthPhase hb R₀ E hE hdiverse Q i →
      D + (modularPhaseSums hb R₀ E hE hdiverse i).card ≤
        (modularPhaseSums hb R₀ E hE hdiverse (i + 1)).card) :
    D * (cfpNonGrowthIndices hb R₀ E hE hdiverse Q k).card ≤
      (modularPhaseSums hb R₀ E hE hdiverse k).card := by
  induction k with
  | zero => simp [cfpNonGrowthIndices]
  | succ k ih =>
      have hIH := ih (fun i hi ↦ hstep i (by omega))
      by_cases hg : IsCFPGrowthPhase hb R₀ E hE hdiverse Q k
      · have hcard :
            (cfpNonGrowthIndices hb R₀ E hE hdiverse Q (k + 1)).card =
              (cfpNonGrowthIndices hb R₀ E hE hdiverse Q k).card := by
          rw [cfpNonGrowthIndices, cfpNonGrowthIndices,
            Finset.range_add_one, Finset.filter_insert]
          simp [hg]
        rw [hcard]
        exact hIH.trans (Finset.card_le_card
          (modularPhaseSums_mono hb R₀ E hE hdiverse (by omega)))
      · have hcard :
            (cfpNonGrowthIndices hb R₀ E hE hdiverse Q (k + 1)).card =
              (cfpNonGrowthIndices hb R₀ E hE hdiverse Q k).card + 1 := by
          rw [cfpNonGrowthIndices, cfpNonGrowthIndices,
            Finset.range_add_one, Finset.filter_insert]
          simp [hg]
        rw [hcard]
        have hk := hstep k (by omega) hg
        calc
          D * ((cfpNonGrowthIndices hb R₀ E hE hdiverse Q k).card + 1) =
              D * (cfpNonGrowthIndices hb R₀ E hE hdiverse Q k).card + D := by
            ring
          _ ≤ (modularPhaseSums hb R₀ E hE hdiverse k).card + D :=
            Nat.add_le_add_right hIH D
          _ = D + (modularPhaseSums hb R₀ E hE hdiverse k).card := by
            omega
          _ ≤ (modularPhaseSums hb R₀ E hE hdiverse (k + 1)).card := hk

lemma modularPhaseSums_subset_full (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀) (i : ℕ) :
    modularPhaseSums hb R₀ E hE hdiverse i ⊆ E + R₀.subsetSum := by
  rw [modularPhaseSums]
  apply Finset.add_subset_add_left
  exact Finset.subsetSum_mono (Finset.sdiff_subset.trans (by rfl))

/-- Parameterized, fully checked CFP Lemma 5.6 phase machine.

`satTarget` is the global target furnished by a saturated phase (the source
uses `ξ t`), while `unsatTarget` is the target furnished by the many
unsaturated phases (the source uses `32t/ℓ`).  The theorem returns their
minimum, exactly as in the paper. -/
theorem cfp_modular_phase_machine (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀)
    (Q dMax L D k satTarget unsatTarget : ℕ) (sat : ℕ → ℕ)
    (hL : 0 < L) (hhalf : 2 * k ≤ R₀.card)
    (hmodMax : ∀ i < k,
      cfpModulus hb R₀ E hE hdiverse i ≤ dMax)
    (hsmallStep : ∀ i < k,
      IsCFPSmallGrowthPhase hb R₀ E hE hdiverse Q i →
      cfpModulus hb R₀ E hE hdiverse i =
        cfpModulus hb R₀ E hE hdiverse (i + 1) →
      3 * cfpInternalCard hb R₀ E hE hdiverse i ≤
        2 * cfpInternalCard hb R₀ E hE hdiverse (i + 1))
    (hlargeStep : ∀ i < k,
      IsCFPLargeGrowthPhase hb R₀ E hE hdiverse Q i →
      cfpModulus hb R₀ E hE hdiverse i =
        cfpModulus hb R₀ E hE hdiverse (i + 1) →
      L + cfpInternalCard hb R₀ E hE hdiverse i ≤
        cfpInternalCard hb R₀ E hE hdiverse (i + 1))
    (hunsaturatedStep : ∀ i < k,
      IsCFPUnsaturatedPhase hb R₀ E hE hdiverse Q sat i →
      D + (modularPhaseSums hb R₀ E hE hdiverse i).card ≤
        (modularPhaseSums hb R₀ E hE hdiverse (i + 1)).card)
    (hsatTarget : ∀ i < k,
      satTarget ≤ cfpModulus hb R₀ E hE hdiverse i *
        sat (cfpModulus hb R₀ E hE hdiverse i))
    (hgrowthBudget :
      (Nat.log 2 dMax + 1) *
          (2 * (Nat.log 2 b + 1) + (Q / L + 1)) ≤ k)
    (hunsatTarget : unsatTarget ≤ D *
      (k - (Nat.log 2 dMax + 1) *
        (2 * (Nat.log 2 b + 1) + (Q / L + 1)))) :
    min satTarget unsatTarget ≤ (E + R₀.subsetSum).card := by
  classical
  let B := (Nat.log 2 dMax + 1) *
    (2 * (Nat.log 2 b + 1) + (Q / L + 1))
  by_cases hex : ∃ i < k,
      IsCFPSaturatedPhase hb R₀ E hE hdiverse Q sat i
  · obtain ⟨i, hi, hsat⟩ := hex
    have hphase := cfp_saturated_phase_card hb R₀ E hE hdiverse
      Q sat (by omega) hsat
    have hfull := Finset.card_le_card
      (modularPhaseSums_subset_full hb R₀ E hE hdiverse i)
    exact (min_le_left _ _).trans
      ((hsatTarget i hi).trans (hphase.trans hfull))
  · have hnonGrowthUnsat : ∀ i < k,
        ¬ IsCFPGrowthPhase hb R₀ E hE hdiverse Q i →
        IsCFPUnsaturatedPhase hb R₀ E hE hdiverse Q sat i := by
      intro i hi hng
      by_contra hnu
      apply hex
      exact ⟨i, hi, hng, hnu⟩
    have hinc := cfp_nongrowth_increment_lower hb R₀ E hE hdiverse
      Q D k (fun i hi hng ↦ hunsaturatedStep i hi
        (hnonGrowthUnsat i hi hng))
    have hgrowth := card_cfpGrowthIndices_le hb R₀ E hE hdiverse
      Q dMax L k hL hhalf hmodMax hsmallStep hlargeStep
    have hnonCard := card_cfpNonGrowthIndices hb R₀ E hE hdiverse Q k
    have hfull := Finset.card_le_card
      (modularPhaseSums_subset_full hb R₀ E hE hdiverse k)
    have hremain : k - B ≤
        (cfpNonGrowthIndices hb R₀ E hE hdiverse Q k).card := by
      rw [hnonCard]
      exact Nat.sub_le_sub_left hgrowth k
    have htarget : unsatTarget ≤
        (modularPhaseSums hb R₀ E hE hdiverse k).card := by
      calc
        unsatTarget ≤ D * (k - B) := by simpa [B] using hunsatTarget
        _ ≤ D * (cfpNonGrowthIndices hb R₀ E hE hdiverse Q k).card :=
          Nat.mul_le_mul_left D hremain
        _ ≤ (modularPhaseSums hb R₀ E hE hdiverse k).card := hinc
    exact (min_le_right _ _).trans (htarget.trans hfull)

end SourcePhases

end Erdos360
