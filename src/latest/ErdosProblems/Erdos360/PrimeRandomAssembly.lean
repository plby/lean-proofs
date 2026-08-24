/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos360.GapAudit
import ErdosProblems.Erdos360.LowerAssemblyNumeric

/-!
# Prime/random assembly for Erdős 360

This module connects the divisor-extraction output to the fixed-cardinality
random theorem.  The small-modulus diversity returned by extraction is enough:
after deleting fewer than eight points, large moduli are handled simply by
counting their positive multiples in the dyadic quotient interval.
-/

namespace Erdos360

open Filter
open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-! ## The sole modular ordinary-growth input -/

/-- Number of elements requested from each of the `ell` random pools. -/
def primeRandomPoolSize (z ell : ℕ) : ℕ := z / (8 * ell)

/-- Integer fourth-root diversity retained by the modular argument. -/
noncomputable def primeRandomPoolDiversity (y ell : ℕ) : ℕ :=
  fourthRootCeil y / (32 * ell)

/-- The ordinary subset-sum cardinality used in the Lev application. -/
def primeRandomNzero (y z ell d : ℕ) : ℕ :=
  y * z / (ell ^ 2 * d)

/-- The containing-interval diameter used in the Lev application. -/
def primeRandomDiameter (y z ell d : ℕ) : ℕ :=
  (y * z) ⌈/⌉ (4 * ell * d)

/-- Explicit finite inequalities needed by the constant-loss ordinary phase
argument for one random pool.  They are separated from the combinatorial
principle so the eventual parameter proof can discharge them uniformly. -/
structure CFPPrimePoolOrdinaryNumerics
    (ell y z d : ℕ) : Prop where
  probability :
    (2 : ℝ) * (((2 * y / d : ℕ) : ℝ) + 1) *
      Real.exp (-(primeRandomPoolDiversity y ell : ℝ) / 24) < 1
  scale : 2 * (2 * y / d) ≤
    (primeRandomPoolDiversity y ell / 4 + 1) *
      (primeRandomPoolSize z ell / 4)
  log : 4 * (Nat.log 2 (2 * y / d) + 1) ^ 2 ≤
    primeRandomPoolSize z ell / 8
  modulus :
    64 * (primeRandomNzero y z ell d ⌈/⌉
      (primeRandomPoolSize z ell / 4)) ≤ y / d + 1
  quadratic :
    64 * (primeRandomNzero y z ell d ⌈/⌉
      (primeRandomPoolSize z ell / 4)) ≤
      (primeRandomPoolSize z ell / 8) *
        (primeRandomPoolSize z ell / 4)
  pool_pos : 0 < primeRandomPoolSize z ell / 4
  diversity_pos : 0 < primeRandomPoolDiversity y ell
  sum : primeRandomPoolSize z ell * (2 * y / d) ≤
    primeRandomDiameter y z ell d

/-- Exact modular/ordinary-growth statement left to the phase machine.
All parameters are fixed by the random and Lev ledgers; in particular this
principle contains no analytic, probabilistic, or coloring hypothesis. -/
def CFPPrimePoolOrdinaryGrowthPrinciple (ell : ℕ) : Prop :=
  ∀ (y z d : ℕ) (P : Finset ℕ),
    CFPPrimePoolOrdinaryNumerics ell y z d →
    P.card = primeRandomPoolSize z ell →
    P ⊆ Finset.Icc (y / d + 1) (2 * y / d) →
    DiverseSampling.DiverseNat P (primeRandomPoolDiversity y ell) →
    Nonempty (CFPOrdinaryGrowthCertificate P
      (primeRandomNzero y z ell d)
      (primeRandomDiameter y z ell d))

/-! ## From cutoff diversity to honest diversity -/

lemma card_divideMultiples_le_div
    {A : Finset ℕ} {e N : ℕ} (he : 0 < e)
    (hA : A ⊆ Finset.Icc 1 N) :
    (divideMultiples A e).card ≤ N / e := by
  calc
    (divideMultiples A e).card ≤ (Finset.Icc 1 (N / e)).card :=
      Finset.card_le_card (divideMultiples_subset_Icc he hA)
    _ ≤ N / e := by simp

/-- If `Z` is diverse up to `M`, trim at most `R` points.  Above `M`, the
positive-multiple count in `[1,N]` supplies the missing diversity. -/
lemma diverse_lowerPart_of_cutoff
    {Z : Finset ℕ} {r R k k₀ M N : ℕ}
    (hr : r ≤ R) (htrim : k + R ≤ k₀)
    (hlarge : k + N / (M + 1) ≤ (lowerPart Z r).card)
    (hZrange : Z ⊆ Finset.Icc 1 N)
    (hdiverse : RandomDiversity.DiverseUpTo Z k₀ M) :
    DiverseSampling.DiverseNat (lowerPart Z r) k := by
  intro e he
  by_cases heM : e ≤ M
  · have hZ := hdiverse e he heM
    have hcompare := card_filter_le_lowerPart_add Z r
      (fun z ↦ ¬e ∣ z)
    omega
  · have hMe : M + 1 ≤ e := by omega
    have hA : lowerPart Z r ⊆ Finset.Icc 1 N :=
      (lowerPart_subset Z r).trans hZrange
    have hmul := card_divideMultiples_le_div (A := lowerPart Z r)
      (e := e) (N := N) (by omega) hA
    have hdiv : N / e ≤ N / (M + 1) :=
      Nat.div_le_div_left hMe (by omega)
    rw [← card_sub_card_divideMultiples (Y := lowerPart Z r)
      (e := e) (by omega)]
    omega

lemma extracted_dyadic_quotient_Icc
    {n colors y d : ℕ} {Y : Finset (BelowTarget n)}
    {c : BelowTarget n → Fin colors} {i : Fin colors}
    {Z : Finset ℕ}
    (hY : ∀ x ∈ Y, y < x.1 ∧ x.1 ≤ 2 * y)
    (hd : 0 < d)
    (hscale : ∀ z ∈ Z, d * z ∈ integerColorClass Y c i) :
    Z ⊆ Finset.Icc 1 (2 * y / d) := by
  intro z hz
  obtain ⟨x, hxY, -, hxval⟩ :=
    mem_integerColorClass.mp (hscale z hz)
  have hx := hY x hxY
  have hprodPos : 0 < d * z := by
    rw [← hxval]
    omega
  refine Finset.mem_Icc.mpr ⟨?_, ?_⟩
  · exact Nat.pos_of_mul_pos_left hprodPos
  · apply (Nat.le_div_iff_mul_le hd).2
    simpa [mul_comm, hxval] using hx.2

/-- Exact dyadic range of the extracted quotients.  The earlier `Icc 1`
form is convenient for random sampling; the lower endpoint retained here is
the one needed by the ordinary modular phase argument. -/
lemma extracted_dyadic_quotient_exact_Icc
    {n colors y d : ℕ} {Y : Finset (BelowTarget n)}
    {c : BelowTarget n → Fin colors} {i : Fin colors}
    {Z : Finset ℕ}
    (hY : ∀ x ∈ Y, y < x.1 ∧ x.1 ≤ 2 * y)
    (hd : 0 < d)
    (hscale : ∀ z ∈ Z, d * z ∈ integerColorClass Y c i) :
    Z ⊆ Finset.Icc (y / d + 1) (2 * y / d) := by
  intro z hz
  obtain ⟨x, hxY, -, hxval⟩ :=
    mem_integerColorClass.mp (hscale z hz)
  have hx := hY x hxY
  refine Finset.mem_Icc.mpr ⟨?_, ?_⟩
  · have hdivlt : y / d < z := by
      rw [Nat.div_lt_iff_lt_mul hd]
      simpa [mul_comm, hxval] using hx.1
    omega
  · apply (Nat.le_div_iff_mul_le hd).2
    simpa [mul_comm, hxval] using hx.2

lemma lowerPart_mod_eight_card (Z : Finset ℕ) :
    (lowerPart Z (Z.card % 8)).card = 8 * (Z.card / 8) := by
  rw [card_lowerPart]
  omega

lemma lowerPart_mod_eight_remainder (Z : Finset ℕ) : Z.card % 8 ≤ 7 := by
  omega

lemma lowerPart_mod_card {Z : Finset ℕ} {h : ℕ} (hh : 0 < h) :
    (lowerPart Z (Z.card % h)).card = h * (Z.card / h) := by
  rw [card_lowerPart]
  have hdecomp := Nat.mod_add_div Z.card h
  omega

lemma lowerPart_mod_remainder_lt {Z : Finset ℕ} {h : ℕ} (hh : 0 < h) :
    Z.card % h < h := Nat.mod_lt _ hh

/-! ## A closed four-cell probability ledger -/

lemma residualDiversity_eight_lower
    {k i : ℕ} (hk : 64 ≤ k) (hi : i < 4) :
    k / 4 ≤ RandomDiversity.residualDiversity k 8 i := by
  interval_cases i <;>
    simp only [RandomDiversity.residualDiversity] <;> omega

lemma one_le_residualDiversity_eight_div
    {k i : ℕ} (hk : 128 ≤ k) (hi : i < 4) :
    1 ≤ RandomDiversity.residualDiversity k 8 i /
      (2 * (8 - i)) := by
  have hres := residualDiversity_eight_lower (by omega : 64 ≤ k) hi
  have hden : 2 * (8 - i) ≤ 16 := by omega
  apply (Nat.le_div_iff_mul_le (by omega : 0 < 2 * (8 - i))).2
  omega

lemma complementDiversityTailBound_le_exp_fixed
    {h k : ℕ} (hh₀ : 3 ≤ h) (hh₁ : h ≤ 8) :
    RandomDiversity.complementDiversityTailBound h k ≤
      Real.exp (-(k : ℝ) / 208) := by
  apply Real.exp_le_exp.mpr
  interval_cases h <;>
    norm_num [RandomDiversity.complementDiversityTailBound] <;>
    nlinarith [show (0 : ℝ) ≤ k by positivity]

lemma exactSplitFailureMass_four_cell_bound
    {N s k i : ℕ} (hk : 64 ≤ k) (hi : i < 4) :
    RandomDiversity.exactSplitFailureMass N s (8 - i)
        (RandomDiversity.residualDiversity k 8 i) ≤
      (4 : ℝ) * (8 * s + 1) * (N + 1) *
        Real.exp (-(k : ℝ) / 1664) := by
  let q := RandomDiversity.residualDiversity k 8 i
  have hq : k / 4 ≤ q := residualDiversity_eight_lower hk hi
  have hh₀ : 3 ≤ 8 - i := by omega
  have hh₁ : 8 - i ≤ 8 := by omega
  have hsample : Real.exp (-(q : ℝ) / (12 * ((8 - i : ℕ) : ℝ))) ≤
      Real.exp (-(k : ℝ) / 1664) := by
    apply Real.exp_le_exp.mpr
    have hqcast : ((k / 4 : ℕ) : ℝ) ≤ q := by exact_mod_cast hq
    have hkfloor : (k : ℝ) / 4 < ((k / 4 : ℕ) : ℝ) + 1 := by
      rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 4)]
      exact_mod_cast (show k < (k / 4 + 1) * 4 by
        have hdecomp := Nat.div_add_mod' k 4
        have hmod := Nat.mod_lt k (by omega : 0 < 4)
        omega)
    have hkR : (64 : ℝ) ≤ k := by exact_mod_cast hk
    have hqrough : (k : ℝ) / 8 ≤ q := by linarith
    have hden : (0 : ℝ) < 12 * ((8 - i : ℕ) : ℝ) := by positivity
    have hden_le : 12 * ((8 - i : ℕ) : ℝ) ≤ 96 := by
      exact_mod_cast (Nat.mul_le_mul_left 12 hh₁)
    have hfrac : (k : ℝ) / 1664 ≤
        (q : ℝ) / (12 * ((8 - i : ℕ) : ℝ)) := by
      rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 1664) hden]
      nlinarith
    simpa only [neg_div] using neg_le_neg hfrac
  have hcomp : RandomDiversity.complementDiversityTailBound (8 - i) q ≤
      Real.exp (-(k : ℝ) / 1664) := by
    calc
      RandomDiversity.complementDiversityTailBound (8 - i) q ≤
          Real.exp (-(q : ℝ) / 208) :=
        complementDiversityTailBound_le_exp_fixed hh₀ hh₁
      _ ≤ Real.exp (-(k : ℝ) / 1664) := by
        apply Real.exp_le_exp.mpr
        have hqcast : ((k / 4 : ℕ) : ℝ) ≤ q := by exact_mod_cast hq
        have hkfloor : (k : ℝ) / 4 < ((k / 4 : ℕ) : ℝ) + 1 := by
          rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 4)]
          exact_mod_cast (show k < (k / 4 + 1) * 4 by
            have hdecomp := Nat.div_add_mod' k 4
            have hmod := Nat.mod_lt k (by omega : 0 < 4)
            omega)
        have hkR : (64 : ℝ) ≤ k := by exact_mod_cast hk
        have hqrough : (k : ℝ) / 8 ≤ q := by linarith
        nlinarith
  unfold RandomDiversity.exactSplitFailureMass
  have hfactor : (((8 - i) * s + 1 : ℕ) : ℝ) ≤ 8 * s + 1 := by
    have hmul : (8 - i) * s ≤ 8 * s := Nat.mul_le_mul_right s hh₁
    exact_mod_cast Nat.add_le_add_right hmul 1
  have hnonneg : 0 ≤ Real.exp (-(q : ℝ) /
      (12 * ((8 - i : ℕ) : ℝ))) +
      RandomDiversity.complementDiversityTailBound (8 - i) q := by
    exact add_nonneg (Real.exp_pos _).le (by
      unfold RandomDiversity.complementDiversityTailBound
      exact (Real.exp_pos _).le)
  calc
    (((8 - i) * s + 1 : ℕ) : ℝ) * (2 * ((N : ℝ) + 1)) *
          (Real.exp (-(q : ℝ) / (12 * ((8 - i : ℕ) : ℝ))) +
            RandomDiversity.complementDiversityTailBound (8 - i) q) ≤
        ((8 * s + 1 : ℕ) : ℝ) * (2 * ((N : ℝ) + 1)) *
          (Real.exp (-(q : ℝ) / (12 * ((8 - i : ℕ) : ℝ))) +
            RandomDiversity.complementDiversityTailBound (8 - i) q) := by
      gcongr
    _ ≤ ((8 * s + 1 : ℕ) : ℝ) * (2 * ((N : ℝ) + 1)) *
          (2 * Real.exp (-(k : ℝ) / 1664)) := by
      gcongr
      nlinarith
    _ = (4 : ℝ) * (8 * s + 1) * (N + 1) *
          Real.exp (-(k : ℝ) / 1664) := by
      push_cast
      ring

lemma four_cell_probability_ledger
    {N s k : ℕ} (hk : 64 ≤ k)
    (hsmall : (4 : ℝ) * (8 * s + 1) * (N + 1) *
      Real.exp (-(k : ℝ) / 1664) < 1) :
    ∀ i < 4,
      RandomDiversity.exactSplitFailureMass N s (8 - i)
        (RandomDiversity.residualDiversity k 8 i) < 1 := by
  intro i hi
  exact (exactSplitFailureMass_four_cell_bound hk hi).trans_lt hsmall

/-! ## Deterministic bookkeeping for a random family -/

lemma card_levFamilyUnion_of_randomParts
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

lemma sum_levFamilyUnion_le_of_randomParts
    {A : Finset ℕ} {ell s diversity N : ℕ}
    {parts : List (Finset ℕ)}
    (h : IsCFPRandomParts A ell s diversity parts)
    (hA : ∀ a ∈ A, a ≤ N) :
    ∑ z ∈ levFamilyUnion parts, z ≤ ell * s * N := by
  have hsub : levFamilyUnion parts ⊆ A := by
    apply levFamilyUnion_subset
    intro P hP
    exact (h.2.2 P hP).1
  calc
    ∑ z ∈ levFamilyUnion parts, z ≤
        ∑ _z ∈ levFamilyUnion parts, N := by
      apply Finset.sum_le_sum
      intro z hz
      exact hA z (hsub hz)
    _ = (levFamilyUnion parts).card * N := by simp
    _ = ell * s * N := by rw [card_levFamilyUnion_of_randomParts h]

/-- General exact-multiple reduction.  The diversity loss caused by the
remainder is recorded explicitly as `h - 1`; no unmentioned trimming is
performed.  The source-faithful choice later is `h = 8 * ell`, so the selected
random pools use only one eighth of the terminal set. -/
noncomputable def randomPreLevInput_of_trimmed_extraction_general
    {n d y B L K : ℕ} {Z : Finset ℕ}
    (h ell k diversity nzero diameter : ℕ) (hh : 0 < h)
    (hZrange : Z ⊆ Finset.Icc 1 (2 * y / d))
    (hdiverse : ∀ e : ℕ, 1 < e → d * e ≤ B →
      L + K * e ≤ (Z.filter fun z ↦ ¬e ∣ z).card)
    (hkL : k + (h - 1) ≤ L)
    (hlarge : k + (2 * y / d) / (B / d + 1) ≤
      h * (Z.card / h))
    (hcount : ell + 2 ≤ h)
    (hprobability : ∀ i < ell,
      RandomDiversity.exactSplitFailureMass (2 * y / d)
        (Z.card / h) (h - i)
        (RandomDiversity.residualDiversity k h i) < 1)
    (hdiversity : ∀ i < ell,
      diversity ≤ RandomDiversity.residualDiversity k h i /
        (2 * (h - i)))
    (hordinary : ∀ P : Finset ℕ,
      P ⊆ lowerPart Z (Z.card % h) → P.card = Z.card / h →
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
  let A := lowerPart Z (Z.card % h)
  have hAcard : A.card = h * (Z.card / h) := by
    simpa [A] using lowerPart_mod_card (Z := Z) hh
  have hAdiverse : DiverseSampling.DiverseNat A k := by
    apply diverse_lowerPart_of_cutoff
      (r := Z.card % h) (R := h - 1) (k₀ := L)
      (M := B / d) (N := 2 * y / d)
    · have := lowerPart_mod_remainder_lt (Z := Z) hh
      omega
    · exact hkL
    · simpa [A, hAcard] using hlarge
    · exact hZrange
    · intro e he heM
      exact (Nat.le_add_right L (K * e)).trans
        (hdiverse e he ((Nat.mul_le_mul_left d heM).trans
          (Nat.mul_div_le B d)))
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
      A_subset := lowerPart_subset Z _
      count_room := hcount
      card_A := hAcard
      diverse_A := hAdiverse
      range_A := by
        intro a ha
        exact Finset.mem_Icc.mp (hZrange (lowerPart_subset Z _ ha))
      probability_ledger := hprobability
      diversity_ledger := hdiversity
      ordinary := hordinary
      nzero_ge := hnzero
      lev_multiplicity := hlev
      dyadic_width := hwidth
      post_partition := by
        intro parts hparts
        constructor
        · exact (sum_levFamilyUnion_le_of_randomParts hparts
            (fun a ha ↦ (Finset.mem_Icc.mp
              (hZrange (lowerPart_subset Z _ ha))).2)).trans_lt hsum
        · rw [card_levFamilyUnion_of_randomParts hparts]
          exact hunused
      Z_nonempty := hZnonempty }

/-- A finite constructor with every random and integer inequality exposed.
The only additive-combinatorial field is `ordinary`. -/
noncomputable def randomPreLevInput_of_trimmed_extraction
    {n d y B L K : ℕ} {Z : Finset ℕ}
    (ell k diversity nzero diameter : ℕ)
    (hZrange : Z ⊆ Finset.Icc 1 (2 * y / d))
    (hdiverse : ∀ e : ℕ, 1 < e → d * e ≤ B →
      L + K * e ≤ (Z.filter fun z ↦ ¬e ∣ z).card)
    (hkL : k + 7 ≤ L)
    (hlarge : k + (2 * y / d) / (B / d + 1) ≤
      8 * (Z.card / 8))
    (hcount : ell + 2 ≤ 8)
    (hprobability : ∀ i < ell,
      RandomDiversity.exactSplitFailureMass (2 * y / d)
        (Z.card / 8) (8 - i)
        (RandomDiversity.residualDiversity k 8 i) < 1)
    (hdiversity : ∀ i < ell,
      diversity ≤ RandomDiversity.residualDiversity k 8 i /
        (2 * (8 - i)))
    (hordinary : ∀ P : Finset ℕ,
      P ⊆ lowerPart Z (Z.card % 8) → P.card = Z.card / 8 →
      DiverseSampling.DiverseNat P diversity →
      Nonempty (CFPOrdinaryGrowthCertificate P nzero diameter))
    (hnzero : 3 ≤ nzero)
    (hlev : 2 * ((diameter - 1) ⌈/⌉ (nzero - 2)) ≤ ell)
    (hwidth : 2 * y ≤ ell * (nzero - 1) + 1)
    (hsum : ell * (Z.card / 8) * (2 * y / d) < n / d)
    (hunused : n / d ≤
      (y / d + 1) * (Z.card - ell * (Z.card / 8)))
    (hZnonempty : Z.Nonempty) :
    CFPRandomPreLevInput n d y Z := by
  exact randomPreLevInput_of_trimmed_extraction_general
    (h := 8) (ell := ell) (k := k) (diversity := diversity)
    (nzero := nzero) (diameter := diameter) (by omega)
    hZrange hdiverse hkL hlarge hcount hprobability hdiversity
    hordinary hnzero hlev hwidth hsum hunused hZnonempty

/-- Four-cell specialization.  Its single exponential inequality implies
the complete stage-by-stage random ledger, and diversity one follows from
the explicit residual-diversity calculation. -/
noncomputable def fourCellRandomPreLevInput_of_trimmed_extraction
    {n d y B L K k nzero diameter : ℕ} {Z : Finset ℕ}
    (hZrange : Z ⊆ Finset.Icc 1 (2 * y / d))
    (hdiverse : ∀ e : ℕ, 1 < e → d * e ≤ B →
      L + K * e ≤ (Z.filter fun z ↦ ¬e ∣ z).card)
    (hk : 128 ≤ k) (hkL : k + 7 ≤ L)
    (hlarge : k + (2 * y / d) / (B / d + 1) ≤
      8 * (Z.card / 8))
    (hprobability : (4 : ℝ) * (((8 * (Z.card / 8) + 1 : ℕ) : ℝ)) *
      (((2 * y / d + 1 : ℕ) : ℝ)) * Real.exp (-(k : ℝ) / 1664) < 1)
    (hordinary : ∀ P : Finset ℕ,
      P ⊆ lowerPart Z (Z.card % 8) → P.card = Z.card / 8 →
      DiverseSampling.DiverseNat P 1 →
      Nonempty (CFPOrdinaryGrowthCertificate P nzero diameter))
    (hnzero : 3 ≤ nzero)
    (hlev : 2 * ((diameter - 1) ⌈/⌉ (nzero - 2)) ≤ 4)
    (hwidth : 2 * y ≤ 4 * (nzero - 1) + 1)
    (hsum : 4 * (Z.card / 8) * (2 * y / d) < n / d)
    (hunused : n / d ≤
      (y / d + 1) * (Z.card - 4 * (Z.card / 8)))
    (hZnonempty : Z.Nonempty) :
    CFPRandomPreLevInput n d y Z := by
  apply randomPreLevInput_of_trimmed_extraction
    (ell := 4) (k := k) (diversity := 1)
    (nzero := nzero) (diameter := diameter)
    hZrange hdiverse hkL hlarge
  · omega
  · apply four_cell_probability_ledger (by omega)
    norm_num at hprobability ⊢
    exact hprobability
  · intro i hi
    exact one_le_residualDiversity_eight_div hk hi
  · exact hordinary
  · exact hnzero
  · exact hlev
  · exact hwidth
  · exact hsum
  · exact hunused
  · exact hZnonempty

/-- Source-faithful specialization `h = 8*ell`.  The theorem makes the
separation of concerns literal: `hordinary` is the only modular-growth
input, while every other premise is an elementary integer or exponential
ledger entry. -/
noncomputable def primeRandomPreLevInput_of_parameter_ledger
    {n d y B L K : ℕ} {Z : Finset ℕ} {ell : ℕ}
    (hell : 0 < ell)
    (hZrange : Z ⊆ Finset.Icc (y / d + 1) (2 * y / d))
    (hdiverse : ∀ e : ℕ, 1 < e → d * e ≤ B →
      L + K * e ≤ (Z.filter fun z ↦ ¬e ∣ z).card)
    (hkL : (L - (8 * ell - 1)) + (8 * ell - 1) ≤ L)
    (hlarge : (L - (8 * ell - 1)) +
        (2 * y / d) / (B / d + 1) ≤
      (8 * ell) * (Z.card / (8 * ell)))
    (hprobability : ∀ i < ell,
      RandomDiversity.exactSplitFailureMass (2 * y / d)
        (Z.card / (8 * ell)) (8 * ell - i)
        (RandomDiversity.residualDiversity
          (L - (8 * ell - 1)) (8 * ell) i) < 1)
    (hdiversity : ∀ i < ell,
      primeRandomPoolDiversity y ell ≤
        RandomDiversity.residualDiversity
          (L - (8 * ell - 1)) (8 * ell) i /
            (2 * (8 * ell - i)))
    (hordinaryNumerics : CFPPrimePoolOrdinaryNumerics ell y Z.card d)
    (hordinary : CFPPrimePoolOrdinaryGrowthPrinciple ell)
    (hnzero : 3 ≤ primeRandomNzero y Z.card ell d)
    (hlev : 2 * ((primeRandomDiameter y Z.card ell d - 1) ⌈/⌉
        (primeRandomNzero y Z.card ell d - 2)) ≤ ell)
    (hwidth : 2 * y ≤
      ell * (primeRandomNzero y Z.card ell d - 1) + 1)
    (hsum : ell * (Z.card / (8 * ell)) * (2 * y / d) < n / d)
    (hunused : n / d ≤
      (y / d + 1) *
        (Z.card - ell * (Z.card / (8 * ell))))
    (hZnonempty : Z.Nonempty) :
    CFPRandomPreLevInput n d y Z := by
  apply randomPreLevInput_of_trimmed_extraction_general
    (h := 8 * ell) (ell := ell)
    (k := L - (8 * ell - 1))
    (diversity := primeRandomPoolDiversity y ell)
    (nzero := primeRandomNzero y Z.card ell d)
    (diameter := primeRandomDiameter y Z.card ell d)
    (by positivity) (by
      intro z hz
      have hzI := Finset.mem_Icc.mp (hZrange hz)
      exact Finset.mem_Icc.mpr
        ⟨(Nat.succ_le_succ (Nat.zero_le (y / d))).trans hzI.1, hzI.2⟩)
      hdiverse hkL hlarge
  · omega
  · exact hprobability
  · exact hdiversity
  · intro P hP hPcard hPdiverse
    exact hordinary y Z.card d P hordinaryNumerics (by
      simpa [primeRandomPoolSize] using hPcard)
      (hP.trans ((lowerPart_subset Z _).trans hZrange)) hPdiverse
  · exact hnzero
  · exact hlev
  · exact hwidth
  · exact hsum
  · exact hunused
  · exact hZnonempty

/-! ## Extraction-facing ledger and source theorem -/

/-- Every non-additive condition needed after divisor extraction.  This is
an auditable list: cardinal room, four random estimates, four residual
diversity estimates, the three Lev integer inequalities, and the two endpoint
mass inequalities. -/
def CFPPrimeRandomParameterLedger
    (n colors y B L K ell : ℕ) (Y : Finset (BelowTarget n)) : Prop :=
  ∀ (c : BelowTarget n → Fin colors) (i : Fin colors)
      (d : ℕ) (Z : Finset ℕ),
    Y.card ≤ colors * (integerColorClass Y c i).card →
    0 < d → d ≤ B →
    (∀ z ∈ Z, d * z ∈ integerColorClass Y c i) →
    (integerColorClass Y c i).card - Z.card ≤
      L * Nat.log 2 B + K * B →
    (∀ e : ℕ, 1 < e → d * e ≤ B →
      L + K * e ≤ (Z.filter fun z ↦ ¬e ∣ z).card) →
    let k := L - (8 * ell - 1)
    Z.Nonempty ∧
    k + (2 * y / d) / (B / d + 1) ≤
      (8 * ell) * (Z.card / (8 * ell)) ∧
    (∀ j < ell,
      RandomDiversity.exactSplitFailureMass (2 * y / d)
        (Z.card / (8 * ell)) (8 * ell - j)
        (RandomDiversity.residualDiversity k (8 * ell) j) < 1) ∧
    (∀ j < ell,
      primeRandomPoolDiversity y ell ≤
        RandomDiversity.residualDiversity k (8 * ell) j /
          (2 * (8 * ell - j))) ∧
    CFPPrimePoolOrdinaryNumerics ell y Z.card d ∧
    3 ≤ primeRandomNzero y Z.card ell d ∧
    2 * ((primeRandomDiameter y Z.card ell d - 1) ⌈/⌉
      (primeRandomNzero y Z.card ell d - 2)) ≤ ell ∧
    2 * y ≤ ell * (primeRandomNzero y Z.card ell d - 1) + 1 ∧
    ell * (Z.card / (8 * ell)) * (2 * y / d) < n / d ∧
    n / d ≤ (y / d + 1) *
      (Z.card - ell * (Z.card / (8 * ell)))

/-- Once the explicit ledger is proved, the complete finite source theorem
depends only on the modular ordinary-growth principle. -/
theorem randomPreLevTestSetSourceCompletion_of_parameterLedger
    {n colors y B L K ell : ℕ} {Y : Finset (BelowTarget n)}
    (hell : 0 < ell)
    (hY : ∀ x ∈ Y, y < x.1 ∧ x.1 ≤ 2 * y)
    (hledger : CFPPrimeRandomParameterLedger n colors y B L K ell Y)
    (hordinary : CFPPrimePoolOrdinaryGrowthPrinciple ell) :
    CFPRandomPreLevTestSetSourceCompletion n colors y B L K Y := by
  intro c i d Z hclass hd hdB hscale hloss hdiverse
  have hdata := hledger c i d Z hclass hd hdB hscale hloss hdiverse
  dsimp only at hdata
  rcases hdata with
    ⟨hZnonempty, hlarge, hprobability, hdiversity, hordinaryNumerics, hnzero,
      hlev, hwidth, hsum, hunused⟩
  have hkL : (L - (8 * ell - 1)) + (8 * ell - 1) ≤ L := by
    have hdiv0 := hdiversity 0 hell
    simp only [RandomDiversity.residualDiversity, Nat.sub_zero] at hdiv0
    have hone : 1 ≤ primeRandomPoolDiversity y ell :=
      hordinaryNumerics.diversity_pos
    have hquot : 1 ≤ (L - (8 * ell - 1)) / (2 * (8 * ell)) :=
      hone.trans hdiv0
    have hden : 0 < 2 * (8 * ell) := by positivity
    have hle := (Nat.le_div_iff_mul_le hden).mp hquot
    omega
  exact ⟨primeRandomPreLevInput_of_parameter_ledger hell
    (extracted_dyadic_quotient_exact_Icc hY hd hscale) hdiverse
    hkL hlarge hprobability hdiversity
    hordinaryNumerics hordinary
    hnzero hlev hwidth hsum hunused hZnonempty⟩

/-- Eventual form of the completely explicit ledger. -/
def EventuallyCFPPrimeRandomParameterLedger (c : ℝ) (ell : ℕ) : Prop :=
  ∀ᶠ n : ℕ in atTop,
    let colors := lowerColorCount c n
    let y := initialLowerY n colors
    ∃ U B L K : ℕ, ∃ hy : 2 * y < n,
      0 < U ∧ 0 < B ∧ B ≤ y / U ∧
      CFPPrimeRandomParameterLedger n colors y B L K ell
        (primeStructuredBelowTarget n y U hy)

/-- All prime-test-set packaging, random selection, and finite endpoint
bookkeeping are discharged from the eventual ledger. -/
theorem eventuallyPrimeRandomPreLev_of_parameterLedger
    {c : ℝ} {ell : ℕ} (hell : 0 < ell)
    (hordinary : CFPPrimePoolOrdinaryGrowthPrinciple ell)
    (hledger : EventuallyCFPPrimeRandomParameterLedger c ell) :
    EventuallyCFPPrimeRandomPreLevTheorem c := by
  apply eventually_primeRandomPreLev_of_primeStructured_source
  filter_upwards [hledger] with n hn
  dsimp only at hn ⊢
  obtain ⟨U, B, L, K, hy, hU, hB, hBcut, hfinite⟩ := hn
  refine ⟨U, B, L, K, hy, hU, hB, hBcut, ?_⟩
  apply randomPreLevTestSetSourceCompletion_of_parameterLedger
    hell (hledger := hfinite) (hordinary := hordinary)
  intro x hx
  exact primeStructuredBelowTarget_dyadic hx

/-- Final resolution connector.  Once the ledger theorem is closed, the only
remaining mathematical inputs in the type are the modular ordinary-growth
principle and Lev's high-multiplicity principle. -/
theorem resolution_of_primeRandom_parameterLedger
    {c : ℝ} (hc : 0 < c) {ell : ℕ} (hell : 0 < ell)
    (hordinary : CFPPrimePoolOrdinaryGrowthPrinciple ell)
    (hlev : CFPLevHighMultiplicityPrinciple)
    (hledger : EventuallyCFPPrimeRandomParameterLedger c ell) :
    Resolution := by
  exact resolution_of_primeRandomPreLev hc hlev
    (eventuallyPrimeRandomPreLev_of_parameterLedger hell hordinary hledger)

end Erdos360

#print axioms Erdos360.randomPreLevInput_of_trimmed_extraction
