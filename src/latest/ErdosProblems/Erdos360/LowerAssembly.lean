/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos360.FiniteReduction
import ErdosProblems.Erdos360.BadQuotients
import ErdosProblems.Erdos360.InitialMertens
import ErdosProblems.Erdos360.AdaptiveSelector
import ErdosProblems.Erdos360.OrdinaryGrowth
import ErdosProblems.Erdos360.LevCompletion
import ErdosProblems.Erdos360.StepBoundedCover
import ErdosProblems.Erdos360.LowerAnalytic

/-!
# Assembly of the diagonal lower bound for Erdős 360

This file records the exact public interface between the already formalized
finite/analytic infrastructure and the one remaining source theorem.  In
particular, it does not hide rounding, passage from natural numbers to
`BelowTarget`, divisor extraction, or the final Lev completion.
-/

namespace Erdos360

open Filter
open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-! ## Putting the structured test set in the coloring domain -/

/-- Regard an arbitrary natural-number finset contained in `[1,n)` as a
finset in the actual coloring domain. -/
noncomputable def natFinsetBelowTarget (n : ℕ) (S : Finset ℕ)
    (hS : S ⊆ Finset.Ico 1 n) : Finset (BelowTarget n) :=
  S.attach.map
    (⟨fun a : {a // a ∈ S} ↦ ⟨a.1, hS a.2⟩,
      fun _a _b hab ↦
        Subtype.ext (congrArg (fun x : BelowTarget n ↦ x.1) hab)⟩ :
      {a // a ∈ S} ↪ BelowTarget n)

@[simp] lemma mem_natFinsetBelowTarget_iff
    {n : ℕ} {S : Finset ℕ} {hS : S ⊆ Finset.Ico 1 n}
    {x : BelowTarget n} :
    x ∈ natFinsetBelowTarget n S hS ↔ x.1 ∈ S := by
  classical
  rw [natFinsetBelowTarget, Finset.mem_map]
  constructor
  · rintro ⟨a, -, hax⟩
    have hval : a.1 = x.1 := congrArg Subtype.val hax
    exact hval ▸ a.2
  · intro hx
    refine ⟨⟨x.1, hx⟩, by simp, ?_⟩
    exact Subtype.ext rfl

lemma card_natFinsetBelowTarget
    (n : ℕ) (S : Finset ℕ) (hS : S ⊆ Finset.Ico 1 n) :
    (natFinsetBelowTarget n S hS).card = S.card := by
  classical
  simp [natFinsetBelowTarget]

/-- The structured natural-number test set, regarded as a finset of the
actual coloring domain.  The range proof is part of the definition's data. -/
noncomputable def structuredBelowTarget (n r y U : ℕ) (hy : 2 * y < n) :
    Finset (BelowTarget n) :=
  (structuredTestSet n r y U).attach.map
    (⟨fun a : {a // a ∈ structuredTestSet n r y U} ↦
        ⟨a.1, structuredTestSet_subset_Ico hy a.2⟩,
      fun _a _b hab ↦
        Subtype.ext (congrArg (fun x : BelowTarget n ↦ x.1) hab)⟩ :
      {a // a ∈ structuredTestSet n r y U} ↪ BelowTarget n)

@[simp] lemma mem_structuredBelowTarget_iff
    {n r y U : ℕ} {hy : 2 * y < n} {x : BelowTarget n} :
    x ∈ structuredBelowTarget n r y U hy ↔
      x.1 ∈ structuredTestSet n r y U := by
  classical
  rw [structuredBelowTarget, Finset.mem_map]
  constructor
  · rintro ⟨a, -, hax⟩
    have hval : a.1 = x.1 := congrArg Subtype.val hax
    exact hval ▸ a.2
  · intro hx
    refine ⟨⟨x.1, hx⟩, by simp, ?_⟩
    exact Subtype.ext rfl

lemma card_structuredBelowTarget
    (n r y U : ℕ) (hy : 2 * y < n) :
    (structuredBelowTarget n r y U hy).card =
      (structuredTestSet n r y U).card := by
  classical
  simp [structuredBelowTarget]

lemma integerColorClass_structured_bounds
    {n r y U k : ℕ} {hy : 2 * y < n}
    {c : BelowTarget n → Fin k} {i : Fin k} {a : ℕ}
    (ha : a ∈ integerColorClass
      (structuredBelowTarget n r y U hy) c i) :
    y < a ∧ a ≤ 2 * y := by
  obtain ⟨x, hx, -, rfl⟩ := mem_integerColorClass.mp ha
  have hx' : x.1 ∈ structuredTestSet n r y U :=
    mem_structuredBelowTarget_iff.mp hx
  exact ⟨structuredTestSet_gt_scale hx',
    structuredTestSet_le_two_mul hx'⟩

/-- Quotient bounds inherited automatically from the dyadic structured
test set after a positive common divisor is removed. -/
lemma extracted_structured_quotient_bounds
    {n colors y U d : ℕ} {hy : 2 * y < n}
    {c : BelowTarget n → Fin colors} {i : Fin colors}
    {Z : Finset ℕ} (hd : 0 < d)
    (hscale : ∀ z ∈ Z, d * z ∈ integerColorClass
      (structuredBelowTarget n colors y U hy) c i) :
    ∀ z ∈ Z, y / d + 1 ≤ z ∧ z ≤ 2 * y := by
  intro z hz
  have hb := integerColorClass_structured_bounds (hscale z hz)
  constructor
  · have hdiv : y / d < z := (Nat.div_lt_iff_lt_mul hd).2 (by
      simpa [Nat.mul_comm] using hb.1)
    omega
  · exact (Nat.le_mul_of_pos_left z hd).trans hb.2

/-- Generic form of the preceding quotient estimate.  It lets the final
assembly use any counted sub-test-set of the dyadic structured set (in
particular the complete-prime subfibres) without duplicating the divisor
extraction argument. -/
lemma extracted_dyadic_quotient_bounds
    {n colors y d : ℕ} {Y : Finset (BelowTarget n)}
    {c : BelowTarget n → Fin colors} {i : Fin colors}
    {Z : Finset ℕ}
    (hY : ∀ x ∈ Y, y < x.1 ∧ x.1 ≤ 2 * y)
    (hd : 0 < d)
    (hscale : ∀ z ∈ Z, d * z ∈ integerColorClass Y c i) :
    ∀ z ∈ Z, y / d + 1 ≤ z ∧ z ≤ 2 * y := by
  intro z hz
  obtain ⟨x, hxY, -, hxval⟩ :=
    mem_integerColorClass.mp (hscale z hz)
  have hb := hY x hxY
  have hprod : y < d * z := by simpa [hxval] using hb.1
  have hprodUpper : d * z ≤ 2 * y := by simpa [hxval] using hb.2
  constructor
  · have hdiv : y / d < z := (Nat.div_lt_iff_lt_mul hd).2 (by
      simpa [Nat.mul_comm] using hprod)
    omega
  · exact (Nat.le_mul_of_pos_left z hd).trans hprodUpper

/-! ## The precise residual finite theorem -/

/-- Data produced after the modular phase argument, ordinary growth, and
Lev's many-summand theorem.  Every field is consumed by the already proved
post-Lev completion theorem. -/
structure CFPLevCompletionData (n d : ℕ) (Z : Finset ℕ) where
  parts : List (Finset ℕ)
  ell : ℕ
  nzero : ℕ
  diameter : ℕ
  lowerScale : ℕ
  width : ℕ
  family : IsCFPLevFamily parts ell nzero diameter
  lev : HasCFPLevInterval parts ell nzero
  parts_subset : ∀ P ∈ parts, P ⊆ Z
  width_le : width ≤ ell * (nzero - 1) + 1
  upper : ∀ z ∈ Z, z ≤ width
  lower_bound : ∀ z ∈ Z, lowerScale ≤ z
  sum_upper : (∑ z ∈ levFamilyUnion parts, z) < n / d
  unused_mass : n / d ≤ lowerScale * (Z.card - (levFamilyUnion parts).card)

lemma CFPLevCompletionData.quotient_mem
    {n d : ℕ} {Z : Finset ℕ}
    (h : CFPLevCompletionData n d Z) :
    n / d ∈ Z.subsetSum := by
  exact quotient_mem_subsetSum_of_cfp_lev_family_sum_bound
    h.family h.lev h.parts_subset h.width_le h.upper h.lower_bound
    h.sum_upper h.unused_mass

/-- The genuinely source-dependent part of the Lev package.  The dyadic
upper and lower bounds on `Z` are omitted because they follow formally from
membership in the structured test set and positivity of the extracted
divisor. -/
structure CFPLevSourceData (n d y : ℕ) (Z : Finset ℕ) where
  parts : List (Finset ℕ)
  ell : ℕ
  nzero : ℕ
  diameter : ℕ
  family : IsCFPLevFamily parts ell nzero diameter
  lev : HasCFPLevInterval parts ell nzero
  parts_subset : ∀ P ∈ parts, P ⊆ Z
  dyadic_width : 2 * y ≤ ell * (nzero - 1) + 1
  sum_upper : (∑ z ∈ levFamilyUnion parts, z) < n / d
  unused_mass : n / d ≤
    (y / d + 1) * (Z.card - (levFamilyUnion parts).card)

/-- A per-pool certificate in exactly the form produced by the modular
phase machine and consumed by the ordinary-growth bridge. -/
structure CFPOrdinaryGrowthCertificate
    (P : Finset ℕ) (nzero diameter : ℕ) where
  seed : Finset ℕ
  pivots : Finset ℕ
  residueGain : ℕ
  diversity : ℕ
  union_eq : seed ∪ pivots = P
  disjoint : Disjoint seed pivots
  pivots_pos : ∀ t ∈ pivots, 0 < t
  residues : ∀ t ∈ pivots,
    residueGain ≤ (occupiedResidues seed.subsetSum t).card
  target : nzero ≤ seed.subsetSum.card + pivots.card * residueGain
  diversity_pos : 0 < diversity
  diverse : Diverse (seed ∪ pivots) diversity
  sum_le : (∑ z ∈ P, z) ≤ diameter

lemma CFPOrdinaryGrowthCertificate.ordinary_properties
    {P : Finset ℕ} {nzero diameter : ℕ}
    (h : CFPOrdinaryGrowthCertificate P nzero diameter) :
    nzero ≤ P.subsetSum.card ∧
      P.subsetSum ⊆ Finset.Icc 0 diameter ∧
      ¬ ContainedInNontrivialAP P.subsetSum := by
  have hgrowth := ordinary_subsetSum_growth_and_aperiodic
    h.disjoint h.pivots_pos h.residues h.diversity_pos h.diverse
  constructor
  · rw [← h.union_eq]
    exact h.target.trans hgrowth.1
  constructor
  · intro s hs
    exact Finset.mem_Icc.mpr ⟨Nat.zero_le _,
      (mem_subsetSum_le_sum hs).trans h.sum_le⟩
  · rw [← h.union_eq]
    exact hgrowth.2

/-- A source-facing form of the Lev data in which each ordinary pool is
certified by its modular residue growth.  The theorem below converts it to
`CFPLevSourceData`, so the final assembly does not assume the ordinary
growth conclusion separately. -/
structure CFPLevRawSourceData (n d y : ℕ) (Z : Finset ℕ) where
  parts : List (Finset ℕ)
  ell : ℕ
  nzero : ℕ
  diameter : ℕ
  length_eq : parts.length = ell
  pairwise : parts.Pairwise (fun P Q ↦ Disjoint P Q)
  ordinary : ∀ P ∈ parts,
    Nonempty (CFPOrdinaryGrowthCertificate P nzero diameter)
  lev : HasCFPLevInterval parts ell nzero
  parts_subset : ∀ P ∈ parts, P ⊆ Z
  dyadic_width : 2 * y ≤ ell * (nzero - 1) + 1
  sum_upper : (∑ z ∈ levFamilyUnion parts, z) < n / d
  unused_mass : n / d ≤
    (y / d + 1) * (Z.card - (levFamilyUnion parts).card)
  nonempty : Z.Nonempty

noncomputable def CFPLevRawSourceData.toSourceData
    {n d y : ℕ} {Z : Finset ℕ}
    (h : CFPLevRawSourceData n d y Z) : CFPLevSourceData n d y Z where
  parts := h.parts
  ell := h.ell
  nzero := h.nzero
  diameter := h.diameter
  family := ⟨h.length_eq, h.pairwise, by
    intro P hP
    exact Classical.choice (h.ordinary P hP) |>.ordinary_properties⟩
  lev := h.lev
  parts_subset := h.parts_subset
  dyadic_width := h.dyadic_width
  sum_upper := h.sum_upper
  unused_mass := h.unused_mass

lemma CFPLevSourceData.quotient_mem_of_bounds
    {n d y : ℕ} {Z : Finset ℕ}
    (h : CFPLevSourceData n d y Z)
    (hbounds : ∀ z ∈ Z, y / d + 1 ≤ z ∧ z ≤ 2 * y) :
    n / d ∈ Z.subsetSum := by
  exact quotient_mem_subsetSum_of_cfp_lev_family_sum_bound
    h.family h.lev h.parts_subset h.dyadic_width
    (fun z hz ↦ (hbounds z hz).2)
    (fun z hz ↦ (hbounds z hz).1)
    h.sum_upper h.unused_mass

/-- The exact finite CFP statement for a specified coloring test set.  It
starts with the output of `exists_divisorExtraction` and ends with the
target divisor plus a source-faithful Lev package. -/
def CFPTestSetCompletion
    (n colors y B L K : ℕ) (Y : Finset (BelowTarget n)) : Prop :=
  ∀ (c : BelowTarget n → Fin colors) (i : Fin colors)
      (d : ℕ) (Z : Finset ℕ),
    Y.card ≤ colors * (integerColorClass Y c i).card →
    0 < d → d ≤ B →
    (∀ z ∈ Z, d * z ∈ integerColorClass Y c i) →
    (integerColorClass Y c i).card - Z.card ≤
      L * Nat.log 2 B + K * B →
    (∀ e : ℕ, 1 < e → d * e ≤ B →
      L + K * e ≤ (Z.filter fun z ↦ ¬e ∣ z).card) →
    d ∣ n ∧ Nonempty (CFPLevRawSourceData n d y Z)

/-- Additive-combinatorial source theorem before the elementary proof that
the extracted common divisor divides the target. -/
def CFPTestSetSourceCompletion
    (n colors y B L K : ℕ) (Y : Finset (BelowTarget n)) : Prop :=
  ∀ (c : BelowTarget n → Fin colors) (i : Fin colors)
      (d : ℕ) (Z : Finset ℕ),
    Y.card ≤ colors * (integerColorClass Y c i).card →
    0 < d → d ≤ B →
    (∀ z ∈ Z, d * z ∈ integerColorClass Y c i) →
    (integerColorClass Y c i).card - Z.card ≤
      L * Nat.log 2 B + K * B →
    (∀ e : ℕ, 1 < e → d * e ≤ B →
      L + K * e ≤ (Z.filter fun z ↦ ¬e ∣ z).card) →
    Nonempty (CFPLevRawSourceData n d y Z)

/-- Supply target divisibility separately from the additive source theorem.
This is the form used for prime quotient test sets. -/
lemma cfpTestSetCompletion_of_source
    {n colors y B L K : ℕ} {Y : Finset (BelowTarget n)}
    (hsource : CFPTestSetSourceCompletion n colors y B L K Y)
    (hdivisor : ∀ (c : BelowTarget n → Fin colors) (i : Fin colors)
        (d : ℕ) (Z : Finset ℕ),
      0 < d → d ≤ B →
      (∀ z ∈ Z, d * z ∈ integerColorClass Y c i) →
      Z.Nonempty → d ∣ n) :
    CFPTestSetCompletion n colors y B L K Y := by
  intro c i d Z hlarge hd hdB hscale hloss hdiverse
  have hdata := hsource c i d Z hlarge hd hdB hscale hloss hdiverse
  obtain ⟨data⟩ := hdata
  exact ⟨hdivisor c i d Z hd hdB hscale data.nonempty, ⟨data⟩⟩

/-- A common divisor bounded by `B` must divide the target when every test
element is a target divisor times a prime strictly larger than `B`.  This is
the elementary reason for using prime-only quotient fibres in the final
test set. -/
lemma commonDivisor_dvd_target_of_large_prime_testSet
    {n colors B d : ℕ} {Y : Finset (BelowTarget n)}
    {c : BelowTarget n → Fin colors} {i : Fin colors}
    {Z : Finset ℕ}
    (hfactor : ∀ x ∈ Y, ∃ u q : ℕ,
      u ∣ n ∧ q.Prime ∧ B < q ∧ x.1 = u * q)
    (hd : 0 < d) (hdB : d ≤ B)
    (hscale : ∀ z ∈ Z, d * z ∈ integerColorClass Y c i)
    (hZ : Z.Nonempty) :
    d ∣ n := by
  obtain ⟨z, hz⟩ := hZ
  obtain ⟨x, hxY, -, hxval⟩ :=
    mem_integerColorClass.mp (hscale z hz)
  obtain ⟨u, q, hun, hqprime, hBq, hxu⟩ := hfactor x hxY
  have hdprod : d ∣ u * q := by
    refine ⟨z, ?_⟩
    calc
      u * q = x.1 := hxu.symm
      _ = d * z := hxval
  have hnqd : ¬q ∣ d := by
    intro hqd
    have hqle : q ≤ d := Nat.le_of_dvd hd hqd
    omega
  have hcop : Nat.Coprime d q :=
    (hqprime.coprime_iff_not_dvd.mpr hnqd).symm
  exact (hcop.dvd_of_dvd_mul_right hdprod).trans hun

/-- Prime-test-set specialization combining the preceding two connectors. -/
lemma cfpTestSetCompletion_of_large_prime_source
    {n colors y B L K : ℕ} {Y : Finset (BelowTarget n)}
    (hfactor : ∀ x ∈ Y, ∃ u q : ℕ,
      u ∣ n ∧ q.Prime ∧ B < q ∧ x.1 = u * q)
    (hsource : CFPTestSetSourceCompletion n colors y B L K Y) :
    CFPTestSetCompletion n colors y B L K Y := by
  apply cfpTestSetCompletion_of_source hsource
  intro c i d Z hd hdB hscale hZ
  exact commonDivisor_dvd_target_of_large_prime_testSet
    hfactor hd hdB hscale hZ

/-- Structured-set specialization of `CFPTestSetCompletion`. -/
def CFPStructuredCompletion
    (n colors y U B L K : ℕ) (hy : 2 * y < n) : Prop :=
  CFPTestSetCompletion n colors y B L K
    (structuredBelowTarget n colors y U hy)

/-- Generic finite lower-bound assembly for a dyadic test set. -/
theorem forcesTarget_of_CFPTestSetCompletion
    {n colors y B L K : ℕ} {Y : Finset (BelowTarget n)}
    (hcolors : 0 < colors) (hB : 0 < B)
    (hY : ∀ x ∈ Y, y < x.1 ∧ x.1 ≤ 2 * y)
    (hCFP : CFPTestSetCompletion n colors y B L K Y) :
    ForcesTarget n colors := by
  apply forcesTarget_of_extracted_colorClass_completion hcolors hB Y
  intro c i d Z hlarge hd hdB hscale hloss hdiverse
  obtain ⟨hdn, hdata⟩ :=
    hCFP c i d Z hlarge hd hdB hscale hloss hdiverse
  obtain ⟨data⟩ := hdata
  have hbounds := extracted_dyadic_quotient_bounds hY hd hscale
  exact ⟨hdn, data.toSourceData.quotient_mem_of_bounds hbounds⟩

/-- The full finite lower-bound assembly.  Pigeonhole, divisor extraction,
and post-Lev interval completion are discharged; only
`CFPStructuredCompletion` remains. -/
theorem forcesTarget_of_CFPStructuredCompletion
    {n colors y U B L K : ℕ}
    (hcolors : 0 < colors) (hB : 0 < B) (hy : 2 * y < n)
    (hCFP : CFPStructuredCompletion n colors y U B L K hy) :
    ForcesTarget n colors := by
  apply forcesTarget_of_CFPTestSetCompletion
    (y := y) (B := B) (L := L) (K := K)
    (Y := structuredBelowTarget n colors y U hy) hcolors hB
  · intro x hx
    have hx' := mem_structuredBelowTarget_iff.mp hx
    exact ⟨structuredTestSet_gt_scale hx',
      structuredTestSet_le_two_mul hx'⟩
  · exact hCFP

/-! ## Diagonal analytic assembly -/

/-- The three source-side numerical estimates which put the canonical
rounded `y` in the geometric range of CFP Claim B.4. -/
def CFPDiagonalNumericBounds (n colors : ℕ) : Prop :=
  ((colors : ℝ) ^ 2) ^ 2 ≤
      (15 / 2 : ℝ) * colors * Nat.totient n * Real.log (colors : ℝ) ∧
  Real.rpow (n : ℝ) (6 / 5 : ℝ) ≤
      (15 / 2 : ℝ) * colors * Nat.totient n * Real.log (colors : ℝ) ∧
  100 * colors * Nat.totient n * Real.log (colors : ℝ) ≤
      ((n : ℝ) / 2) ^ 2

lemma two_initialLowerY_lt_of_diagonal_bounds
    {n colors : ℕ} (hn : 0 < n) (hcolors : 0 < colors)
    (hMertens : InitialMissingMertensBounds n colors)
    (hnum : CFPDiagonalNumericBounds n colors) :
    2 * initialLowerY n colors < n := by
  obtain ⟨-, -, hy⟩ := initialLowerY_range_of_numeric_bounds hn hcolors
    hMertens hnum.1 hnum.2.1 hnum.2.2
  have hy' : (2 * initialLowerY n colors : ℕ) < n := by
    exact_mod_cast (show (2 : ℝ) * initialLowerY n colors < n by
      nlinarith)
  exact hy'

/-- Eventual source theorem in its narrowest useful form: at the canonical
diagonal parameters it supplies cutoffs and the residual finite completion.
The Mertens estimate and all rounding/range facts are deliberately absent
from this definition; the theorem below supplies them. -/
def EventuallyCFPFiniteTheorem (c : ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop,
    let colors := lowerColorCount c n
    let y := initialLowerY n colors
    ∃ U B L K : ℕ, 0 < B ∧
      ∀ hy : 2 * y < n,
        CFPStructuredCompletion n colors y U B L K hy

/-- Prime-subset-ready version of the eventual finite theorem.  The source
may choose the actual dyadic coloring test set; this is the interface used by
the complete-prime construction, for which the extracted divisor is
automatically a divisor of the target. -/
def EventuallyCFPTestSetTheorem (c : ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop,
    let colors := lowerColorCount c n
    let y := initialLowerY n colors
    ∃ Y : Finset (BelowTarget n), ∃ B L K : ℕ,
      0 < B ∧
      (∀ x ∈ Y, y < x.1 ∧ x.1 ≤ 2 * y) ∧
      CFPTestSetCompletion n colors y B L K Y

/-- Source-facing version of `EventuallyCFPTestSetTheorem` for the
prime-only structured test set.  The final divisor argument is not part of
the additive source theorem: it is encoded by the factorization of every
test element as a target divisor times a prime above the extraction cutoff.
This is the narrowest eventual proposition that the modular/ordinary/Lev
assembly has to prove. -/
def EventuallyCFPLargePrimeSourceTheorem (c : ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop,
    let colors := lowerColorCount c n
    let y := initialLowerY n colors
    ∃ Y : Finset (BelowTarget n), ∃ B L K : ℕ,
      0 < B ∧
      (∀ x ∈ Y, y < x.1 ∧ x.1 ≤ 2 * y) ∧
      (∀ x ∈ Y, ∃ u q : ℕ,
        u ∣ n ∧ q.Prime ∧ B < q ∧ x.1 = u * q) ∧
      CFPTestSetSourceCompletion n colors y B L K Y

/-- Prime factorization closes the target-divisibility obligation, so the
source-facing eventual theorem implies the exact finite completion theorem
consumed by the lower-bound assembly. -/
lemma EventuallyCFPLargePrimeSourceTheorem.toTestSet
    {c : ℝ} (h : EventuallyCFPLargePrimeSourceTheorem c) :
    EventuallyCFPTestSetTheorem c := by
  filter_upwards [h] with n hfin
  dsimp only at hfin ⊢
  obtain ⟨Y, B, L, K, hB, hY, hfactor, hsource⟩ := hfin
  exact ⟨Y, B, L, K, hB, hY,
    cfpTestSetCompletion_of_large_prime_source hfactor hsource⟩

/-- The old structured-set source theorem implies the flexible test-set
version once the canonical range inequality `2y<n` is known. -/
lemma EventuallyCFPFiniteTheorem.toTestSet
    {c : ℝ} (hc : 0 < c)
    (hnumeric : ∀ᶠ n : ℕ in atTop,
      CFPDiagonalNumericBounds n (lowerColorCount c n))
    (h : EventuallyCFPFiniteTheorem c) :
    EventuallyCFPTestSetTheorem c := by
  filter_upwards [eventually_gt_atTop 0,
    eventually_three_le_lowerColorCount hc,
    eventually_initialMissingMertensBounds_lowerColorCount hc,
    hnumeric, h] with n hn hcolors hMertens hnum hfin
  dsimp only at hfin ⊢
  obtain ⟨U, B, L, K, hB, hCFP⟩ := hfin
  have hy : 2 * initialLowerY n (lowerColorCount c n) < n :=
    two_initialLowerY_lt_of_diagonal_bounds hn (by omega) hMertens hnum
  refine ⟨structuredBelowTarget n (lowerColorCount c n)
      (initialLowerY n (lowerColorCount c n)) U hy,
    B, L, K, hB, ?_, hCFP hy⟩
  intro x hx
  have hx' := mem_structuredBelowTarget_iff.mp hx
  exact ⟨structuredTestSet_gt_scale hx',
    structuredTestSet_le_two_mul hx'⟩

/-- Analytic assembly for a source theorem which supplies its own exact
dyadic coloring test set. -/
theorem eventuallyForcesResolutionFloor_of_CFPTestSet
    {c : ℝ} (hc : 0 < c)
    (hfinite : EventuallyCFPTestSetTheorem c) :
    EventuallyForcesResolutionFloor c := by
  filter_upwards [eventually_three_le_lowerColorCount hc, hfinite] with
      n hcolors hfin
  dsimp only at hfin
  obtain ⟨Y, B, L, K, hB, hY, hCFP⟩ := hfin
  simpa [lowerColorCount] using
    forcesTarget_of_CFPTestSetCompletion
      (y := initialLowerY n (lowerColorCount c n))
      (B := B) (L := L) (K := K) (Y := Y)
      (by omega) hB hY hCFP

/-- Final lower-bound endgame from the prime-only source theorem.  All
divisor extraction, target divisibility, and post-Lev interval completion
are discharged by the preceding public connectors. -/
theorem eventuallyForcesResolutionFloor_of_largePrimeSource
    {c : ℝ} (hc : 0 < c)
    (hsource : EventuallyCFPLargePrimeSourceTheorem c) :
    EventuallyForcesResolutionFloor c := by
  exact eventuallyForcesResolutionFloor_of_CFPTestSet hc hsource.toTestSet

/-- Complete diagonal assembly, conditional only on the explicit numeric
asymptotics and the finite CFP source theorem.  Initial-prime Mertens,
integral rounding of the color count, the canonical square-root choice of
`y`, and its embedding in `{1,...,n-1}` are all discharged here. -/
theorem eventuallyForcesResolutionFloor_of_CFP
    {c : ℝ} (hc : 0 < c)
    (hnumeric : ∀ᶠ n : ℕ in atTop,
      CFPDiagonalNumericBounds n (lowerColorCount c n))
    (hfinite : EventuallyCFPFiniteTheorem c) :
    EventuallyForcesResolutionFloor c := by
  exact eventuallyForcesResolutionFloor_of_CFPTestSet hc
    (hfinite.toTestSet hc hnumeric)

end Erdos360
