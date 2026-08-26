/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.Base

/-!
# General finite CRT systems for the large-gap divisor expansion

The first exact CRT layer in `Erdos4b.Base` uses pairwise-coprime coordinate
moduli.  Maynard's unseparated doubled weight also has compatible systems in
which a first-form modulus and a companion-form modulus share a prime.  This
file records the exact finite counting API needed for that situation.  It
does not assume pairwise coprimality: compatibility simply means that the
simultaneous system has a solution, and its period is the least common
multiple of all coordinate moduli.
-/

namespace Erdos4b

open scoped BigOperators

noncomputable section

noncomputable local instance generalCrtPropDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- A finite family of congruences is compatible when it has a simultaneous
solution.  This formulation is equivalent to the usual pairwise gcd
criterion, but is more convenient for exact finite counting. -/
def GeneralCrtCompatible {ι : Type*} (S : Finset ι)
    (modulus residue : ι → ℕ) : Prop :=
  ∃ r : ℕ, ∀ i ∈ S, r ≡ residue i [MOD modulus i]

/-- The period of a general finite congruence system. -/
def generalCrtModulus {ι : Type*} (S : Finset ι)
    (modulus : ι → ℕ) : ℕ :=
  S.lcm modulus

/-- A canonical simultaneous residue, chosen as the least natural-number
witness of compatibility. -/
noncomputable def generalCrtResidue {ι : Type*} (S : Finset ι)
    (modulus residue : ι → ℕ)
    (hcompat : GeneralCrtCompatible S modulus residue) : ℕ :=
  Nat.find hcompat

theorem generalCrtResidue_spec {ι : Type*} (S : Finset ι)
    (modulus residue : ι → ℕ)
    (hcompat : GeneralCrtCompatible S modulus residue) :
    ∀ i ∈ S,
      generalCrtResidue S modulus residue hcompat ≡ residue i
        [MOD modulus i] := by
  exact Nat.find_spec hcompat

/-- The familiar pairwise gcd compatibility condition. -/
def GeneralCrtPairwiseCompatible {ι : Type*} (S : Finset ι)
    (modulus residue : ι → ℕ) : Prop :=
  ∀ i ∈ S, ∀ j ∈ S,
    residue i ≡ residue j [MOD Nat.gcd (modulus i) (modulus j)]

/-- Distributivity of natural gcd over lcm, in the nonzero form needed by
the finite generalized CRT induction. -/
theorem gcd_lcm_distrib_of_ne_zero {a b c : ℕ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    Nat.gcd a (Nat.lcm b c) =
      Nat.lcm (Nat.gcd a b) (Nat.gcd a c) := by
  have hab : Nat.gcd a b ≠ 0 :=
    (Nat.gcd_pos_of_pos_left b (Nat.pos_of_ne_zero ha)).ne'
  have hac : Nat.gcd a c ≠ 0 :=
    (Nat.gcd_pos_of_pos_left c (Nat.pos_of_ne_zero ha)).ne'
  have hbc : Nat.lcm b c ≠ 0 := Nat.lcm_ne_zero hb hc
  have hleft : Nat.gcd a (Nat.lcm b c) ≠ 0 :=
    (Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero ha)).ne'
  have hright : Nat.lcm (Nat.gcd a b) (Nat.gcd a c) ≠ 0 :=
    Nat.lcm_ne_zero hab hac
  apply Nat.factorization_inj hleft hright
  rw [Nat.factorization_gcd ha hbc, Nat.factorization_lcm hb hc,
    Nat.factorization_lcm hab hac, Nat.factorization_gcd ha hb,
    Nat.factorization_gcd ha hc]
  ext p
  exact min_max_distrib_left
    (a.factorization p) (b.factorization p) (c.factorization p)

theorem gcd_finset_lcm_of_ne_zero {ι : Type*}
    (S : Finset ι) (f : ι → ℕ) (a : ℕ)
    (ha : a ≠ 0) (hf : ∀ i ∈ S, f i ≠ 0) :
    Nat.gcd a (S.lcm f) =
      S.lcm (fun i => Nat.gcd a (f i)) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
      rw [Finset.lcm_insert, Finset.lcm_insert]
      simp only [lcm_eq_nat_lcm]
      rw [gcd_lcm_distrib_of_ne_zero
        (a := a) (b := f i) (c := S.lcm f) ha
        (hf i (by simp))
        (Finset.lcm_ne_zero_iff.mpr
          (fun j hj => hf j (by simp [hj])))]
      rw [ih (fun j hj => hf j (by simp [hj]))]

/-- Solvability implies all pairwise gcd conditions.  The converse is the
generalized CRT; the forward direction is the one needed to expose the
cross-family collision factors in the divisor expansion. -/
theorem GeneralCrtCompatible.pairwise {ι : Type*} {S : Finset ι}
    {modulus residue : ι → ℕ}
    (hcompat : GeneralCrtCompatible S modulus residue) :
    GeneralCrtPairwiseCompatible S modulus residue := by
  obtain ⟨r, hr⟩ := hcompat
  intro i hi j hj
  have hri : r ≡ residue i
      [MOD Nat.gcd (modulus i) (modulus j)] :=
    (hr i hi).of_dvd (Nat.gcd_dvd_left _ _)
  have hrj : r ≡ residue j
      [MOD Nat.gcd (modulus i) (modulus j)] :=
    (hr j hj).of_dvd (Nat.gcd_dvd_right _ _)
  exact hri.symm.trans hrj

/-- Congruence modulo every member of a finite family combines to congruence
modulo their least common multiple. -/
theorem modEq_finset_lcm {ι : Type*} (S : Finset ι)
    (modulus : ι → ℕ) {a b : ℕ}
    (h : ∀ i ∈ S, a ≡ b [MOD modulus i]) :
    a ≡ b [MOD S.lcm modulus] := by
  classical
  induction S using Finset.induction_on with
  | empty => exact Nat.modEq_one
  | @insert i S hi ih =>
      rw [Finset.lcm_insert]
      apply Nat.mod_lcm
      · exact h i (by simp)
      · apply ih
        intro j hj
        exact h j (by simp [hj])

/-- The generalized finite Chinese remainder theorem: for positive moduli,
the pairwise gcd congruences are also sufficient for a simultaneous
solution. -/
theorem GeneralCrtPairwiseCompatible.compatible {ι : Type*}
    {S : Finset ι} {modulus residue : ι → ℕ}
    (hpair : GeneralCrtPairwiseCompatible S modulus residue)
    (hpos : ∀ i ∈ S, 0 < modulus i) :
    GeneralCrtCompatible S modulus residue := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      exact ⟨0, by simp⟩
  | @insert i S hi ih =>
      have hposS : ∀ j ∈ S, 0 < modulus j := by
        intro j hj
        exact hpos j (by simp [hj])
      have hpairS : GeneralCrtPairwiseCompatible S modulus residue := by
        intro j hj k hk
        exact hpair j (by simp [hj]) k (by simp [hk])
      obtain ⟨r, hr⟩ := ih hpairS hposS
      have hmods : ∀ j ∈ S,
          r ≡ residue i [MOD Nat.gcd (modulus i) (modulus j)] := by
        intro j hj
        have hrj : r ≡ residue j
            [MOD Nat.gcd (modulus i) (modulus j)] :=
          (hr j hj).of_dvd
            (Nat.gcd_dvd_right (modulus i) (modulus j))
        have hji := hpair j (by simp [hj]) i (by simp)
        rw [Nat.gcd_comm] at hji
        exact hrj.trans hji
      have hmodL : r ≡ residue i
          [MOD Nat.gcd (modulus i) (S.lcm modulus)] := by
        rw [gcd_finset_lcm_of_ne_zero S modulus (modulus i)
          (hpos i (by simp)).ne' (fun j hj => (hposS j hj).ne')]
        exact modEq_finset_lcm S
          (fun j => Nat.gcd (modulus i) (modulus j)) hmods
      let z := Nat.chineseRemainder' hmodL.symm
      refine ⟨z, ?_⟩
      intro j hj
      rw [Finset.mem_insert] at hj
      rcases hj with rfl | hj
      · exact z.2.1
      · exact (z.2.2.of_dvd (Finset.dvd_lcm hj)).trans (hr j hj)

theorem generalCrtCompatible_iff_pairwise {ι : Type*}
    {S : Finset ι} {modulus residue : ι → ℕ}
    (hpos : ∀ i ∈ S, 0 < modulus i) :
    GeneralCrtCompatible S modulus residue ↔
      GeneralCrtPairwiseCompatible S modulus residue := by
  exact ⟨GeneralCrtCompatible.pairwise,
    fun h => h.compatible hpos⟩

/-- A compatible finite system is exactly one residue class modulo the lcm
of its coordinate moduli. -/
theorem modEq_generalCrtResidue_iff {ι : Type*} (S : Finset ι)
    (modulus residue : ι → ℕ)
    (hcompat : GeneralCrtCompatible S modulus residue) (n : ℕ) :
    n ≡ generalCrtResidue S modulus residue hcompat
          [MOD generalCrtModulus S modulus] ↔
      ∀ i ∈ S, n ≡ residue i [MOD modulus i] := by
  constructor
  · intro hn i hi
    have hn' : n ≡ generalCrtResidue S modulus residue hcompat
        [MOD modulus i] :=
      hn.of_dvd (Finset.dvd_lcm hi)
    exact hn'.trans (generalCrtResidue_spec S modulus residue hcompat i hi)
  · intro hn
    unfold generalCrtModulus
    apply modEq_finset_lcm
    intro i hi
    exact (hn i hi).trans
      (generalCrtResidue_spec S modulus residue hcompat i hi).symm

theorem generalCrtModulus_pos {ι : Type*} {S : Finset ι}
    {modulus : ι → ℕ} (hpos : ∀ i ∈ S, 0 < modulus i) :
    0 < generalCrtModulus S modulus := by
  unfold generalCrtModulus
  apply Nat.pos_of_ne_zero
  rw [Finset.lcm_ne_zero_iff]
  intro i hi
  exact (hpos i hi).ne'

/-- The least witness chosen for a compatible CRT system is the canonical
representative below the lcm period. -/
theorem generalCrtResidue_lt_modulus {ι : Type*} (S : Finset ι)
    (modulus residue : ι → ℕ)
    (hcompat : GeneralCrtCompatible S modulus residue)
    (hpos : ∀ i ∈ S, 0 < modulus i) :
    generalCrtResidue S modulus residue hcompat <
      generalCrtModulus S modulus := by
  let M := generalCrtModulus S modulus
  let r := generalCrtResidue S modulus residue hcompat
  have hM : 0 < M := generalCrtModulus_pos hpos
  have hmod : r % M ≡ r [MOD M] := by
    simp [Nat.ModEq]
  have hsystem : ∀ i ∈ S, r % M ≡ residue i [MOD modulus i] :=
    (modEq_generalCrtResidue_iff S modulus residue hcompat (r % M)).mp
      hmod
  have hleast : r ≤ r % M := Nat.find_min' hcompat hsystem
  exact hleast.trans_lt (Nat.mod_lt r hM)

theorem coprime_finset_lcm {ι : Type*} (S : Finset ι)
    (modulus : ι → ℕ) (a : ℕ)
    (hcop : ∀ i ∈ S, a.Coprime (modulus i)) :
    a.Coprime (S.lcm modulus) := by
  apply Nat.Coprime.of_dvd_right (Finset.lcm_dvd_prod S modulus)
  apply Nat.Coprime.prod_right
  intro i hi
  exact hcop i hi

theorem generalCrtResidue_coprime_modulus {ι : Type*}
    (S : Finset ι) (modulus residue : ι → ℕ)
    (hcompat : GeneralCrtCompatible S modulus residue)
    (hcoord : ∀ i ∈ S, (residue i).Coprime (modulus i)) :
    (generalCrtResidue S modulus residue hcompat).Coprime
      (generalCrtModulus S modulus) := by
  apply coprime_finset_lcm
  intro i hi
  exact (coprime_modulus_iff_of_modEq
    (generalCrtResidue_spec S modulus residue hcompat i hi)).mpr
      (hcoord i hi)

/-- Adding one distinguished pre-sieve coordinate changes the period by an
ordinary binary lcm. -/
theorem preSievedFinsetLcm_eq_lcm {ι : Type*} [Fintype ι]
    (W : ℕ) (modulus : ι → ℕ) :
    (Finset.univ : Finset (Option ι)).lcm
        (BoundedGaps.Maynard.preSievedModulus W modulus) =
      Nat.lcm W ((Finset.univ : Finset ι).lcm modulus) := by
  classical
  apply Nat.dvd_antisymm
  · apply Finset.lcm_dvd
    intro i hi
    cases i with
    | none => exact Nat.dvd_lcm_left W _
    | some i =>
        exact (Finset.dvd_lcm (show i ∈ (Finset.univ : Finset ι) by simp)).trans
          (Nat.dvd_lcm_right W _)
  · apply Nat.lcm_dvd
    · exact Finset.dvd_lcm
        (show none ∈ (Finset.univ : Finset (Option ι)) by simp)
    · apply Finset.lcm_dvd
      intro i hi
      exact Finset.dvd_lcm
        (show some i ∈ (Finset.univ : Finset (Option ι)) by simp)

/-- Number of members of a half-open interval satisfying a compatible
finite congruence system. -/
noncomputable def generalCrtClassCount {ι : Type*} (S : Finset ι)
    (modulus residue : ι → ℕ)
    (_hcompat : GeneralCrtCompatible S modulus residue)
    (A B : ℕ) : ℕ :=
  ((Finset.Ico A B).filter fun n =>
    ∀ i ∈ S, n ≡ residue i [MOD modulus i]).card

/-- Exact discrepancy from interval length divided by the lcm period. -/
noncomputable def generalCrtClassError {ι : Type*} (S : Finset ι)
    (modulus residue : ι → ℕ)
    (hcompat : GeneralCrtCompatible S modulus residue)
    (A B : ℕ) : ℝ :=
  BoundedGaps.Maynard.intervalModEqCardError A B
    (generalCrtModulus S modulus)
    (generalCrtResidue S modulus residue hcompat)

theorem generalCrtClassCount_eq_main_add_error {ι : Type*}
    (S : Finset ι) (modulus residue : ι → ℕ)
    (hcompat : GeneralCrtCompatible S modulus residue)
    (A B : ℕ) :
    (generalCrtClassCount S modulus residue hcompat A B : ℝ) =
      ((B : ℝ) - A) / generalCrtModulus S modulus +
        generalCrtClassError S modulus residue hcompat A B := by
  classical
  unfold generalCrtClassCount generalCrtClassError
  have hfilter :
      (Finset.Ico A B).filter (fun n =>
          ∀ i ∈ S, n ≡ residue i [MOD modulus i]) =
        (Finset.Ico A B).filter (fun n =>
          n ≡ generalCrtResidue S modulus residue hcompat
            [MOD generalCrtModulus S modulus]) := by
    ext n
    simp only [Finset.mem_filter, and_congr_right_iff]
    intro _hn
    exact (modEq_generalCrtResidue_iff S modulus residue hcompat n).symm
  rw [hfilter,
    BoundedGaps.Maynard.intervalModEq_card_eq_length_div_add_error]

theorem generalCrtClassError_abs_le_one {ι : Type*}
    (S : Finset ι) (modulus residue : ι → ℕ)
    (hcompat : GeneralCrtCompatible S modulus residue)
    (A B : ℕ) (hAB : A ≤ B)
    (hpos : ∀ i ∈ S, 0 < modulus i) :
    |generalCrtClassError S modulus residue hcompat A B| ≤ 1 := by
  exact BoundedGaps.Maynard.intervalModEqCardError_abs_le_one
    A B (generalCrtModulus S modulus)
    (generalCrtResidue S modulus residue hcompat) hAB
    (generalCrtModulus_pos hpos)

/-! ## The unseparated doubled large-gap system -/

/-- The complete finite coordinate set: the `none` coordinate is the
pre-sieving congruence and the `some` coordinates are the two copies of the
shift tuple. -/
abbrev LargeGapGeneralCrtIndex (H : Finset ℕ) :=
  Option (LargeGapCrtIndex H)

/-- Coordinate moduli of the unseparated doubled CRT system. -/
def largeGapGeneralCrtCoordinateModulus (H : Finset ℕ) (W : ℕ)
    (d e d' e' : H → ℕ) : LargeGapGeneralCrtIndex H → ℕ :=
  BoundedGaps.Maynard.preSievedModulus W
    (largeGapCrtModulus H d e d' e')

/-- Coordinate residues of the unseparated doubled CRT system. -/
def largeGapGeneralCrtCoordinateResidue (H : Finset ℕ)
    (v m q : ℕ) (d e d' e' : H → ℕ) :
    LargeGapGeneralCrtIndex H → ℕ :=
  BoundedGaps.Maynard.preSievedResidue v
    (largeGapCrtResidue H m q d e d' e')

/-- Compatibility of one pre-sieve residue with one doubled divisor
quadruple, allowing common cross-family factors. -/
def LargeGapGeneralCrtCompatible (H : Finset ℕ)
    (W v m q : ℕ) (d e d' e' : H → ℕ) : Prop :=
  GeneralCrtCompatible Finset.univ
    (largeGapGeneralCrtCoordinateModulus H W d e d' e')
    (largeGapGeneralCrtCoordinateResidue H v m q d e d' e')

/-- Compatibility of the doubled coordinates before adjoining the
pre-sieving residue. -/
def LargeGapCoordinateCrtCompatible (H : Finset ℕ)
    (m q : ℕ) (d e d' e' : H → ℕ) : Prop :=
  GeneralCrtCompatible Finset.univ
    (largeGapCrtModulus H d e d' e')
    (largeGapCrtResidue H m q d e d' e')

def largeGapCoordinateCrtModulus (H : Finset ℕ)
    (d e d' e' : H → ℕ) : ℕ :=
  (Finset.univ : Finset (LargeGapCrtIndex H)).lcm
    (largeGapCrtModulus H d e d' e')

/-- Exact pairwise-gcd characterization of compatibility for the doubled
coordinate system.  This is the logical form consumed by an auxiliary
`a_(i,j)` expansion. -/
theorem largeGapCoordinateCrtCompatible_iff_pairwise
    (H : Finset ℕ) (m q : ℕ) (d e d' e' : H → ℕ)
    (hDpos : ∀ h : H, 0 < Nat.lcm (d h) (d' h))
    (hEpos : ∀ h : H, 0 < Nat.lcm (e h) (e' h)) :
    LargeGapCoordinateCrtCompatible H m q d e d' e' ↔
      GeneralCrtPairwiseCompatible Finset.univ
        (largeGapCrtModulus H d e d' e')
        (largeGapCrtResidue H m q d e d' e') := by
  apply generalCrtCompatible_iff_pairwise
  intro i hi
  cases i with
  | inl h => exact hDpos h
  | inr h => exact hEpos h

/-- The true period of a possibly non-pairwise-coprime doubled system. -/
def largeGapGeneralCrtModulus (H : Finset ℕ) (W : ℕ)
    (d e d' e' : H → ℕ) : ℕ :=
  generalCrtModulus Finset.univ
    (largeGapGeneralCrtCoordinateModulus H W d e d' e')

theorem largeGapGeneralCrtModulus_eq_lcm
    (H : Finset ℕ) (W : ℕ) (d e d' e' : H → ℕ) :
    largeGapGeneralCrtModulus H W d e d' e' =
      Nat.lcm W (largeGapCoordinateCrtModulus H d e d' e') := by
  exact preSievedFinsetLcm_eq_lcm W (largeGapCrtModulus H d e d' e')

theorem largeGapGeneralCrtModulus_eq_mul
    (H : Finset ℕ) (W : ℕ) (d e d' e' : H → ℕ)
    (hWcop : ∀ i : LargeGapCrtIndex H,
      W.Coprime (largeGapCrtModulus H d e d' e' i)) :
    largeGapGeneralCrtModulus H W d e d' e' =
      W * largeGapCoordinateCrtModulus H d e d' e' := by
  rw [largeGapGeneralCrtModulus_eq_lcm]
  apply Nat.Coprime.lcm_eq_mul
  exact coprime_finset_lcm Finset.univ
    (largeGapCrtModulus H d e d' e') W (fun i _ => hWcop i)

/-- When every doubled coordinate is coprime to the pre-sieve, adjoining an
arbitrary allowed residue neither creates nor removes compatibility. -/
theorem largeGapGeneralCompatible_iff_coordinate
    (H : Finset ℕ) (W v m q : ℕ) (d e d' e' : H → ℕ)
    (hWcop : ∀ i : LargeGapCrtIndex H,
      W.Coprime (largeGapCrtModulus H d e d' e' i)) :
    LargeGapGeneralCrtCompatible H W v m q d e d' e' ↔
      LargeGapCoordinateCrtCompatible H m q d e d' e' := by
  constructor
  · rintro ⟨r, hr⟩
    refine ⟨r, ?_⟩
    intro i hi
    exact hr (some i) (Finset.mem_univ _)
  · rintro ⟨r, hr⟩
    let M := (Finset.univ : Finset (LargeGapCrtIndex H)).lcm
      (largeGapCrtModulus H d e d' e')
    have hWM : W.Coprime M := coprime_finset_lcm Finset.univ
      (largeGapCrtModulus H d e d' e') W (fun i _ => hWcop i)
    let z : ℕ := Nat.chineseRemainder hWM v r
    refine ⟨z, ?_⟩
    intro i hi
    cases i with
    | none => exact (Nat.chineseRemainder hWM v r).2.1
    | some i =>
        have hzM : z ≡ r [MOD M] :=
          (Nat.chineseRemainder hWM v r).2.2
        exact (hzM.of_dvd
          (Finset.dvd_lcm (show i ∈
            (Finset.univ : Finset (LargeGapCrtIndex H)) by simp))).trans
          (hr i (Finset.mem_univ _))

/-- Canonical residue of a compatible unseparated doubled system. -/
noncomputable def largeGapGeneralCrtResidue (H : Finset ℕ)
    (W v m q : ℕ) (d e d' e' : H → ℕ)
    (hcompat : LargeGapGeneralCrtCompatible H W v m q d e d' e') : ℕ :=
  generalCrtResidue Finset.univ
    (largeGapGeneralCrtCoordinateModulus H W d e d' e')
    (largeGapGeneralCrtCoordinateResidue H v m q d e d' e') hcompat

theorem largeGapGeneralCrtModulus_pos
    (H : Finset ℕ) (W : ℕ) (d e d' e' : H → ℕ)
    (hW : 0 < W)
    (hDpos : ∀ h : H, 0 < Nat.lcm (d h) (d' h))
    (hEpos : ∀ h : H, 0 < Nat.lcm (e h) (e' h)) :
    0 < largeGapGeneralCrtModulus H W d e d' e' := by
  apply generalCrtModulus_pos
  intro i hi
  cases i with
  | none => exact hW
  | some i =>
      cases i with
      | inl h => exact hDpos h
      | inr h => exact hEpos h

/-- Every compatible unseparated quadruple satisfies the exact gcd
congruence between each first-form coordinate and each companion-form
coordinate.  These gcds are the finite objects encoded by Maynard's
auxiliary `a_(i,j)` variables. -/
theorem LargeGapGeneralCrtCompatible.cross_family_modEq
    {H : Finset ℕ} {W v m q : ℕ} {d e d' e' : H → ℕ}
    (hcompat : LargeGapGeneralCrtCompatible H W v m q d e d' e')
    (a b : H) :
    largeGapCrtResidue H m q d e d' e' (Sum.inl a) ≡
        largeGapCrtResidue H m q d e d' e' (Sum.inr b)
      [MOD Nat.gcd
        (largeGapCrtModulus H d e d' e' (Sum.inl a))
        (largeGapCrtModulus H d e d' e' (Sum.inr b))] := by
  have hp := GeneralCrtCompatible.pairwise hcompat
  exact hp (some (Sum.inl a)) (Finset.mem_univ _)
    (some (Sum.inr b)) (Finset.mem_univ _)

/-- Arithmetic form of the cross-family collision condition.  A common
factor of the first modulus at `a` and companion modulus at `b` can occur
only when it divides the affine difference encoded by this congruence. -/
theorem LargeGapGeneralCrtCompatible.cross_family_affine_modEq
    {H : Finset ℕ} {W v m q : ℕ} {d e d' e' : H → ℕ}
    (hcompat : LargeGapGeneralCrtCompatible H W v m q d e d' e')
    (hDpos : ∀ h : H, 0 < Nat.lcm (d h) (d' h))
    (hEpos : ∀ h : H, 0 < Nat.lcm (e h) (e' h))
    (hmE : ∀ h : H, m.Coprime (Nat.lcm (e h) (e' h)))
    (a b : H) :
    m * (a.1 * q) + 1 ≡ m * (b.1 * q)
      [MOD Nat.gcd (Nat.lcm (d a) (d' a))
        (Nat.lcm (e b) (e' b))] := by
  let D := Nat.lcm (d a) (d' a)
  let E := Nat.lcm (e b) (e' b)
  let g := Nat.gcd D E
  let rD := BoundedGaps.Maynard.negativeShiftResidue D (a.1 * q)
  let rE := companionResidue m E (b.1 * q)
  have hcross : rD ≡ rE [MOD g] := by
    simpa [D, E, g, rD, rE, largeGapCrtResidue,
      largeGapCrtModulus] using hcompat.cross_family_modEq a b
  have hnegD : rD + a.1 * q ≡ 0 [MOD D] := by
    apply Nat.modEq_zero_iff_dvd.mpr
    exact BoundedGaps.Maynard.negativeShiftResidue_add_dvd
      D (a.1 * q) (by simpa [D] using hDpos a)
  have hneg : rD + a.1 * q ≡ 0 [MOD g] :=
    hnegD.of_dvd (Nat.gcd_dvd_left D E)
  have hcompE : m * (rE + b.1 * q) ≡ 1 [MOD E] :=
    companionResidue_spec (by simpa [E] using hEpos b) (by
      simpa [E] using hmE b)
  have hcomp : m * (rD + b.1 * q) ≡ 1 [MOD g] := by
    exact ((hcross.add_right (b.1 * q)).mul_left m).trans
      (hcompE.of_dvd (Nat.gcd_dvd_right D E))
  have hleft : m * rD + (m * (a.1 * q) + 1) ≡ 1 [MOD g] := by
    have hz := (hneg.mul_left m).add_right 1
    simpa [mul_add, add_assoc] using hz
  have hright : m * rD + m * (b.1 * q) ≡ 1 [MOD g] := by
    simpa [mul_add] using hcomp
  have hboth :
      m * rD + (m * (a.1 * q) + 1) ≡
        m * rD + m * (b.1 * q) [MOD g] :=
    hleft.trans hright.symm
  exact Nat.ModEq.add_left_cancel' (m * rD) hboth

theorem LargeGapGeneralCrtCompatible.cross_family_factor_dvd
    {H : Finset ℕ} {W v m q r : ℕ} {d e d' e' : H → ℕ}
    (hcompat : LargeGapGeneralCrtCompatible H W v m q d e d' e')
    (hDpos : ∀ h : H, 0 < Nat.lcm (d h) (d' h))
    (hEpos : ∀ h : H, 0 < Nat.lcm (e h) (e' h))
    (hmE : ∀ h : H, m.Coprime (Nat.lcm (e h) (e' h)))
    (a b : H)
    (hrD : r ∣ Nat.lcm (d a) (d' a))
    (hrE : r ∣ Nat.lcm (e b) (e' b)) :
    (r : ℤ) ∣
      (m * (b.1 * q) : ℕ) - (m * (a.1 * q) + 1 : ℕ) := by
  have hmod := hcompat.cross_family_affine_modEq hDpos hEpos hmE a b
  have hr : r ∣ Nat.gcd (Nat.lcm (d a) (d' a))
      (Nat.lcm (e b) (e' b)) := Nat.dvd_gcd hrD hrE
  exact (hmod.of_dvd hr).dvd

/-- Any integer satisfying the pre-sieve residue and the doubled divisor
conditions witnesses compatibility of the general CRT system. -/
theorem largeGapGeneralCrtCompatible_of_solution
    (H : Finset ℕ) (W v m q n : ℕ) (d e d' e' : H → ℕ)
    (hm : 0 < m)
    (hDpos : ∀ h : H, 0 < Nat.lcm (d h) (d' h))
    (hEpos : ∀ h : H, 0 < Nat.lcm (e h) (e' h))
    (hmE : ∀ h : H, m.Coprime (Nat.lcm (e h) (e' h)))
    (hnshift : ∀ h : H, 0 < n + h.1 * q)
    (hnv : n ≡ v [MOD W])
    (hcond : largeGapDivisorCondition H m q n d e ∧
      largeGapDivisorCondition H m q n d' e') :
    LargeGapGeneralCrtCompatible H W v m q d e d' e' := by
  refine ⟨n, ?_⟩
  intro i hi
  cases i with
  | none => exact hnv
  | some i =>
      exact (largeGapDivisorCondition_pair_iff_modEq H m q n d e d' e'
        hm hDpos hEpos hmE hnshift).mp hcond i

/-- Exact CRT description of the unseparated doubled system. -/
theorem modEq_largeGapGeneralCrtResidue_iff
    (H : Finset ℕ) (W v m q n : ℕ) (d e d' e' : H → ℕ)
    (hm : 0 < m)
    (hDpos : ∀ h : H, 0 < Nat.lcm (d h) (d' h))
    (hEpos : ∀ h : H, 0 < Nat.lcm (e h) (e' h))
    (hmE : ∀ h : H, m.Coprime (Nat.lcm (e h) (e' h)))
    (hnshift : ∀ h : H, 0 < n + h.1 * q)
    (hcompat : LargeGapGeneralCrtCompatible H W v m q d e d' e') :
    n ≡ largeGapGeneralCrtResidue H W v m q d e d' e' hcompat
          [MOD largeGapGeneralCrtModulus H W d e d' e'] ↔
      n ≡ v [MOD W] ∧
        largeGapDivisorCondition H m q n d e ∧
          largeGapDivisorCondition H m q n d' e' := by
  change GeneralCrtCompatible Finset.univ
    (largeGapGeneralCrtCoordinateModulus H W d e d' e')
    (largeGapGeneralCrtCoordinateResidue H v m q d e d' e') at hcompat
  change
    (n ≡ generalCrtResidue Finset.univ
        (largeGapGeneralCrtCoordinateModulus H W d e d' e')
        (largeGapGeneralCrtCoordinateResidue H v m q d e d' e') hcompat
      [MOD generalCrtModulus Finset.univ
        (largeGapGeneralCrtCoordinateModulus H W d e d' e')]) ↔ _
  rw [modEq_generalCrtResidue_iff]
  constructor
  · intro hall
    refine ⟨hall none (Finset.mem_univ _), ?_⟩
    apply (largeGapDivisorCondition_pair_iff_modEq H m q n d e d' e'
      hm hDpos hEpos hmE hnshift).mpr
    intro i
    exact hall (some i) (Finset.mem_univ _)
  · rintro ⟨hnv, hcond⟩ i hi
    cases i with
    | none => exact hnv
    | some i =>
        exact (largeGapDivisorCondition_pair_iff_modEq H m q n d e d' e'
          hm hDpos hEpos hmE hnshift).mp hcond i

/-- The class count is zero for an incompatible system and otherwise uses
the canonical lcm residue. -/
noncomputable def largeGapGeneralCrtClassCount (H : Finset ℕ)
    (W v m q T : ℕ) (d e d' e' : H → ℕ) : ℕ :=
  if hcompat : LargeGapGeneralCrtCompatible H W v m q d e d' e' then
    generalCrtClassCount Finset.univ
      (largeGapGeneralCrtCoordinateModulus H W d e d' e')
      (largeGapGeneralCrtCoordinateResidue H v m q d e d' e')
      hcompat 1 (T + 1)
  else 0

/-- Literal endpoint error of the totalized general class count. -/
noncomputable def largeGapGeneralCrtClassError (H : Finset ℕ)
    (W v m q T : ℕ) (d e d' e' : H → ℕ) : ℝ :=
  if hcompat : LargeGapGeneralCrtCompatible H W v m q d e d' e' then
    generalCrtClassError Finset.univ
      (largeGapGeneralCrtCoordinateModulus H W d e d' e')
      (largeGapGeneralCrtCoordinateResidue H v m q d e d' e')
      hcompat 1 (T + 1)
  else 0

/-- Main term of the totalized general class count. -/
noncomputable def largeGapGeneralCrtClassMain (H : Finset ℕ)
    (W v m q T : ℕ) (d e d' e' : H → ℕ) : ℝ :=
  if LargeGapGeneralCrtCompatible H W v m q d e d' e' then
    (T : ℝ) / largeGapGeneralCrtModulus H W d e d' e'
  else 0

theorem largeGapGeneralCrtClassCount_eq_main_add_error
    (H : Finset ℕ) (W v m q T : ℕ) (d e d' e' : H → ℕ) :
    (largeGapGeneralCrtClassCount H W v m q T d e d' e' : ℝ) =
      largeGapGeneralCrtClassMain H W v m q T d e d' e' +
        largeGapGeneralCrtClassError H W v m q T d e d' e' := by
  classical
  by_cases hcompat : LargeGapGeneralCrtCompatible H W v m q d e d' e'
  · have hc : GeneralCrtCompatible Finset.univ
        (largeGapGeneralCrtCoordinateModulus H W d e d' e')
        (largeGapGeneralCrtCoordinateResidue H v m q d e d' e') := hcompat
    rw [largeGapGeneralCrtClassCount, dif_pos hcompat,
      largeGapGeneralCrtClassMain, if_pos hcompat,
      largeGapGeneralCrtClassError, dif_pos hcompat]
    have hmain := generalCrtClassCount_eq_main_add_error Finset.univ
      (largeGapGeneralCrtCoordinateModulus H W d e d' e')
      (largeGapGeneralCrtCoordinateResidue H v m q d e d' e')
      hc 1 (T + 1)
    simpa [largeGapGeneralCrtModulus] using hmain
  · simp [largeGapGeneralCrtClassCount, largeGapGeneralCrtClassMain,
      largeGapGeneralCrtClassError, hcompat]

theorem largeGapGeneralCrtClassError_abs_le_one
    (H : Finset ℕ) (W v m q T : ℕ) (d e d' e' : H → ℕ)
    (hW : 0 < W)
    (hDpos : ∀ h : H, 0 < Nat.lcm (d h) (d' h))
    (hEpos : ∀ h : H, 0 < Nat.lcm (e h) (e' h)) :
    |largeGapGeneralCrtClassError H W v m q T d e d' e'| ≤ 1 := by
  classical
  by_cases hcompat : LargeGapGeneralCrtCompatible H W v m q d e d' e'
  · rw [largeGapGeneralCrtClassError, dif_pos hcompat]
    apply generalCrtClassError_abs_le_one
    · omega
    · intro i hi
      cases i with
      | none => exact hW
      | some i =>
          cases i with
          | inl h => exact hDpos h
          | inr h => exact hEpos h
  · simp [largeGapGeneralCrtClassError, hcompat]

/-- The old quadruple count is exactly the sum of the totalized general CRT
class counts.  This theorem is the finite-algebra replacement for the
pairwise-coprime-only identity in `Base`. -/
theorem preSievedLargeGapQuadrupleCount_eq_sum_generalCrt
    (H : Finset ℕ) (W m q T : ℕ) (d e d' e' : H → ℕ)
    (hW : 1 < W) (hm : 0 < m)
    (hDpos : ∀ h : H, 0 < Nat.lcm (d h) (d' h))
    (hEpos : ∀ h : H, 0 < Nat.lcm (e h) (e' h))
    (hmE : ∀ h : H, m.Coprime (Nat.lcm (e h) (e' h))) :
    preSievedLargeGapQuadrupleCount H W m q T d e d' e' =
      ∑ v ∈ allowedPreSieveResidues W m,
        largeGapGeneralCrtClassCount H W v m q T d e d' e' := by
  classical
  rw [preSievedLargeGapQuadrupleCount,
    ← sum_allowed_residue_filter_card W m T
      (fun n => largeGapDivisorCondition H m q n d e ∧
        largeGapDivisorCondition H m q n d' e') hW hm]
  apply Finset.sum_congr rfl
  intro v hv
  by_cases hcompat : LargeGapGeneralCrtCompatible H W v m q d e d' e'
  · rw [largeGapGeneralCrtClassCount, dif_pos hcompat]
    unfold generalCrtClassCount
    apply congrArg Finset.card
    ext n
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hn, hnv, hcond⟩
      refine ⟨hn, ?_⟩
      have hnshift : ∀ h : H, 0 < n + h.1 * q := by
        intro h
        have := (Finset.mem_Icc.mp hn).1
        omega
      intro i hi
      cases i with
      | none => exact hnv
      | some i =>
          exact (largeGapDivisorCondition_pair_iff_modEq
            H m q n d e d' e' hm hDpos hEpos hmE hnshift).mp hcond i
    · rintro ⟨hn, hall⟩
      have hnshift : ∀ h : H, 0 < n + h.1 * q := by
        intro h
        have := (Finset.mem_Icc.mp hn).1
        omega
      refine ⟨hn, hall none (Finset.mem_univ _), ?_⟩
      apply (largeGapDivisorCondition_pair_iff_modEq
        H m q n d e d' e' hm hDpos hEpos hmE hnshift).mpr
      intro i
      exact hall (some i) (Finset.mem_univ _)
  · rw [largeGapGeneralCrtClassCount, dif_neg hcompat]
    apply Finset.card_eq_zero.mpr
    rw [Finset.filter_eq_empty_iff]
    intro n hn hcond
    have hnshift : ∀ h : H, 0 < n + h.1 * q := by
      intro h
      have := (Finset.mem_Icc.mp hn).1
      omega
    exact hcompat (largeGapGeneralCrtCompatible_of_solution
      H W v m q n d e d' e' hm hDpos hEpos hmE hnshift hcond.1 hcond.2)

/-- Exact main-term/error expansion for arbitrary cross-family collisions. -/
theorem preSievedLargeGapQuadrupleCount_eq_generalMain_add_error
    (H : Finset ℕ) (W m q T : ℕ) (d e d' e' : H → ℕ)
    (hW : 1 < W) (hm : 0 < m)
    (hDpos : ∀ h : H, 0 < Nat.lcm (d h) (d' h))
    (hEpos : ∀ h : H, 0 < Nat.lcm (e h) (e' h))
    (hmE : ∀ h : H, m.Coprime (Nat.lcm (e h) (e' h))) :
    (preSievedLargeGapQuadrupleCount H W m q T d e d' e' : ℝ) =
      (∑ v ∈ allowedPreSieveResidues W m,
        largeGapGeneralCrtClassMain H W v m q T d e d' e') +
      ∑ v ∈ allowedPreSieveResidues W m,
        largeGapGeneralCrtClassError H W v m q T d e d' e' := by
  rw [preSievedLargeGapQuadrupleCount_eq_sum_generalCrt
    H W m q T d e d' e' hW hm hDpos hEpos hmE]
  push_cast
  simp_rw [largeGapGeneralCrtClassCount_eq_main_add_error]
  rw [Finset.sum_add_distrib]

/-! ## General doubled normalization -/

/-- The positivity and companion-coprimality conditions needed for the
general CRT expansion.  There is deliberately no cross-family coprimality
field. -/
structure DoubledSelbergGeneralSupport (H : Finset ℕ)
    (D E : Finset (H → ℕ)) (m : ℕ) : Prop where
  first_lcm_pos : ∀ d ∈ D, ∀ d' ∈ D, ∀ h : H,
    0 < Nat.lcm (d h) (d' h)
  companion_lcm_pos : ∀ e ∈ E, ∀ e' ∈ E, ∀ h : H,
    0 < Nat.lcm (e h) (e' h)
  companion_coprime : ∀ e ∈ E, ∀ e' ∈ E, ∀ h : H,
    m.Coprime (Nat.lcm (e h) (e' h))

/-- The ordinary first Maynard support and the full companion support satisfy
the general hypotheses.  No prime-range separation between the two supports
is imposed. -/
theorem standardDoubledGeneralSupport
    (H : Finset ℕ) (RD RE W m : ℕ) :
    DoubledSelbergGeneralSupport H
      (BoundedGaps.Maynard.maynardDivisorTupleSupport H RD W)
      (fullySeparatedCompanionSupport H RE W m) m := by
  refine
    { first_lcm_pos := ?_
      companion_lcm_pos := ?_
      companion_coprime := ?_ }
  · intro d hd d' hd' h
    have hdT := BoundedGaps.Maynard.isMaynardDivisorTuple_of_mem_support hd
    have hd'T := BoundedGaps.Maynard.isMaynardDivisorTuple_of_mem_support hd'
    exact Nat.lcm_pos
      (Nat.pos_of_ne_zero (hdT.coordinate_squarefree h).ne_zero)
      (Nat.pos_of_ne_zero (hd'T.coordinate_squarefree h).ne_zero)
  · intro e he e' he' h
    have heT := BoundedGaps.Maynard.isMaynardDivisorTuple_of_mem_support he
    have he'T := BoundedGaps.Maynard.isMaynardDivisorTuple_of_mem_support he'
    exact Nat.lcm_pos
      (Nat.pos_of_ne_zero (heT.coordinate_squarefree h).ne_zero)
      (Nat.pos_of_ne_zero (he'T.coordinate_squarefree h).ne_zero)
  · intro e he e' he' h
    have heT := BoundedGaps.Maynard.isMaynardDivisorTuple_of_mem_support he
    have he'T := BoundedGaps.Maynard.isMaynardDivisorTuple_of_mem_support he'
    have hme : m.Coprime (e h) :=
      (Nat.Coprime.of_dvd_right (dvd_mul_left m W)
        (heT.coordinate_coprime_W h)).symm
    have hme' : m.Coprime (e' h) :=
      (Nat.Coprime.of_dvd_right (dvd_mul_left m W)
        (he'T.coordinate_coprime_W h)).symm
    apply Nat.Coprime.of_dvd_right (Nat.lcm_dvd_mul (e h) (e' h))
    exact hme.mul_right hme'

theorem standardDoubledGeneralSupport_preSieve_coprime
    {H : Finset ℕ} {RD RE W m : ℕ}
    {d d' : H → ℕ}
    (hd : d ∈ BoundedGaps.Maynard.maynardDivisorTupleSupport H RD W)
    (hd' : d' ∈ BoundedGaps.Maynard.maynardDivisorTupleSupport H RD W)
    {e e' : H → ℕ}
    (he : e ∈ fullySeparatedCompanionSupport H RE W m)
    (he' : e' ∈ fullySeparatedCompanionSupport H RE W m) :
    ∀ i : LargeGapCrtIndex H,
      W.Coprime (largeGapCrtModulus H d e d' e' i) := by
  have hdT := BoundedGaps.Maynard.isMaynardDivisorTuple_of_mem_support hd
  have hd'T := BoundedGaps.Maynard.isMaynardDivisorTuple_of_mem_support hd'
  have heT := BoundedGaps.Maynard.isMaynardDivisorTuple_of_mem_support he
  have he'T := BoundedGaps.Maynard.isMaynardDivisorTuple_of_mem_support he'
  intro i
  cases i with
  | inl h =>
      apply Nat.Coprime.of_dvd_right (Nat.lcm_dvd_mul (d h) (d' h))
      exact (hdT.coordinate_coprime_W h).symm.mul_right
        (hd'T.coordinate_coprime_W h).symm
  | inr h =>
      have hWe : W.Coprime (e h) :=
        (Nat.Coprime.of_dvd_right (dvd_mul_right W m)
          (heT.coordinate_coprime_W h)).symm
      have hWe' : W.Coprime (e' h) :=
        (Nat.Coprime.of_dvd_right (dvd_mul_right W m)
          (he'T.coordinate_coprime_W h)).symm
      apply Nat.Coprime.of_dvd_right (Nat.lcm_dvd_mul (e h) (e' h))
      exact hWe.mul_right hWe'

/-- Once the pre-sieve is coprime to every doubled coordinate, the sum over
allowed residues is simply their cardinality times the common lcm main
term, provided the coordinate system is compatible. -/
theorem sum_largeGapGeneralCrtClassMain_eq
    (H : Finset ℕ) (W m q T : ℕ) (d e d' e' : H → ℕ)
    (hWcop : ∀ i : LargeGapCrtIndex H,
      W.Coprime (largeGapCrtModulus H d e d' e' i)) :
    (∑ v ∈ allowedPreSieveResidues W m,
      largeGapGeneralCrtClassMain H W v m q T d e d' e') =
      if LargeGapCoordinateCrtCompatible H m q d e d' e' then
        (allowedPreSieveResidues W m).card *
          ((T : ℝ) / largeGapGeneralCrtModulus H W d e d' e')
      else 0 := by
  classical
  by_cases hc : LargeGapCoordinateCrtCompatible H m q d e d' e'
  · have hv : ∀ v,
        LargeGapGeneralCrtCompatible H W v m q d e d' e' := by
      intro v
      exact (largeGapGeneralCompatible_iff_coordinate
        H W v m q d e d' e' hWcop).mpr hc
    rw [if_pos hc]
    simp_rw [largeGapGeneralCrtClassMain, if_pos (hv _)]
    simp
  · have hv : ∀ v,
        ¬LargeGapGeneralCrtCompatible H W v m q d e d' e' := by
      intro v h
      exact hc ((largeGapGeneralCompatible_iff_coordinate
        H W v m q d e d' e' hWcop).mp h)
    rw [if_neg hc]
    simp_rw [largeGapGeneralCrtClassMain, if_neg (hv _)]
    simp

/-- The literal lcm main term, summed over every compatible pre-sieve
residue and every divisor quadruple. -/
noncomputable def doubledSelbergGeneralNormalizationMain
    (H : Finset ℕ) (D E : Finset (H → ℕ))
    (lambda : (H → ℕ) → (H → ℕ) → ℝ)
    (W m q T : ℕ) : ℝ :=
  ∑ d ∈ D, ∑ e ∈ E, ∑ d' ∈ D, ∑ e' ∈ E,
    lambda d e * lambda d' e' *
      ∑ v ∈ allowedPreSieveResidues W m,
        largeGapGeneralCrtClassMain H W v m q T d e d' e'

/-- Aggregate endpoint error in the unseparated normalization. -/
noncomputable def doubledSelbergGeneralNormalizationError
    (H : Finset ℕ) (D E : Finset (H → ℕ))
    (lambda : (H → ℕ) → (H → ℕ) → ℝ)
    (W m q T : ℕ) : ℝ :=
  ∑ d ∈ D, ∑ e ∈ E, ∑ d' ∈ D, ∑ e' ∈ E,
    lambda d e * lambda d' e' *
      ∑ v ∈ allowedPreSieveResidues W m,
        largeGapGeneralCrtClassError H W v m q T d e d' e'

/-- Arithmetic lcm kernel remaining after the pre-sieve density and interval
length have been factored from the unseparated main term. -/
noncomputable def doubledSelbergCoordinateLcmKernel
    (H : Finset ℕ) (D E : Finset (H → ℕ))
    (lambda : (H → ℕ) → (H → ℕ) → ℝ)
    (m q : ℕ) : ℝ :=
  ∑ d ∈ D, ∑ e ∈ E, ∑ d' ∈ D, ∑ e' ∈ E,
    if LargeGapCoordinateCrtCompatible H m q d e d' e' then
      lambda d e * lambda d' e' /
        largeGapCoordinateCrtModulus H d e d' e'
    else 0

/-- For the two ordinary Maynard supports, the exact general main term is
the pre-sieve density times the coordinate lcm kernel. -/
theorem doubledSelbergGeneralNormalizationMain_standard_eq
    (H : Finset ℕ) (RD RE W m q T : ℕ) (hW : 0 < W)
    (lambda : (H → ℕ) → (H → ℕ) → ℝ) :
    doubledSelbergGeneralNormalizationMain H
        (BoundedGaps.Maynard.maynardDivisorTupleSupport H RD W)
        (fullySeparatedCompanionSupport H RE W m)
        lambda W m q T =
      (((allowedPreSieveResidues W m).card : ℝ) * (T : ℝ) / W) *
        doubledSelbergCoordinateLcmKernel H
          (BoundedGaps.Maynard.maynardDivisorTupleSupport H RD W)
          (fullySeparatedCompanionSupport H RE W m) lambda m q := by
  classical
  let D := BoundedGaps.Maynard.maynardDivisorTupleSupport H RD W
  let E := fullySeparatedCompanionSupport H RE W m
  let A : ℝ := ((allowedPreSieveResidues W m).card : ℝ) * (T : ℝ) / W
  change (∑ d ∈ D, ∑ e ∈ E, ∑ d' ∈ D, ∑ e' ∈ E,
      lambda d e * lambda d' e' *
        ∑ v ∈ allowedPreSieveResidues W m,
          largeGapGeneralCrtClassMain H W v m q T d e d' e') =
    A * (∑ d ∈ D, ∑ e ∈ E, ∑ d' ∈ D, ∑ e' ∈ E,
      if LargeGapCoordinateCrtCompatible H m q d e d' e' then
        lambda d e * lambda d' e' /
          largeGapCoordinateCrtModulus H d e d' e'
      else 0)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d' hd'
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e' he'
  have hWcop := standardDoubledGeneralSupport_preSieve_coprime
    (H := H) (RD := RD) (RE := RE) (W := W) (m := m)
    (d := d) (d' := d') hd hd' (e := e) (e' := e') he he'
  rw [sum_largeGapGeneralCrtClassMain_eq
    H W m q T d e d' e' hWcop]
  by_cases hc : LargeGapCoordinateCrtCompatible H m q d e d' e'
  · rw [if_pos hc, if_pos hc,
      largeGapGeneralCrtModulus_eq_mul H W d e d' e' hWcop]
    have hM : 0 < largeGapCoordinateCrtModulus H d e d' e' := by
      apply generalCrtModulus_pos
      intro i hi
      cases i with
      | inl h =>
          exact (standardDoubledGeneralSupport H RD RE W m).first_lcm_pos
            d hd d' hd' h
      | inr h =>
          exact (standardDoubledGeneralSupport H RD RE W m).companion_lcm_pos
            e he e' he' h
    dsimp [A]
    field_simp [hW.ne', hM.ne']
    push_cast
    ring
  · simp [hc]

/-- Fully expanded exact normalization identity with all compatible
cross-family collisions retained. -/
theorem preSievedDoubledWeightSum_eq_generalMain_add_error
    (H : Finset ℕ) (D E : Finset (H → ℕ))
    (lambda : (H → ℕ) → (H → ℕ) → ℝ)
    (w m q T : ℕ) (hw : 2 ≤ w) (hm : 0 < m)
    (support : DoubledSelbergGeneralSupport H D E m) :
    (∑ n ∈ Finset.Icc 0 T,
      if largeGapPreSieved w m n then
        doubledSelbergWeight H D E lambda m q n else 0) =
      doubledSelbergGeneralNormalizationMain H D E lambda
          (primorial w) m q T +
        doubledSelbergGeneralNormalizationError H D E lambda
          (primorial w) m q T := by
  classical
  rw [preSievedDoubledWeightSum_eq_quadrupleCounts
    H D E lambda w m q T hw]
  unfold doubledSelbergGeneralNormalizationMain
    doubledSelbergGeneralNormalizationError
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e he
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d' hd'
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e' he'
  rw [← mul_add]
  congr 1
  rw [preSievedLargeGapQuadrupleCount_eq_generalMain_add_error
    H (primorial w) m q T d e d' e'
    (one_lt_primorial_of_two_le hw) hm
    (support.first_lcm_pos d hd d' hd')
    (support.companion_lcm_pos e he e' he')
    (support.companion_coprime e he e' he')]

/-- The general aggregate CRT endpoint error has the same elementary
cardinality envelope as the separated-support error. -/
theorem doubledSelbergGeneralNormalizationError_abs_le
    (H : Finset ℕ) (D E : Finset (H → ℕ))
    (lambda : (H → ℕ) → (H → ℕ) → ℝ)
    (W m q T : ℕ) (support : DoubledSelbergGeneralSupport H D E m)
    (hW : 0 < W) (L : ℝ) (hL : 0 ≤ L)
    (hcoeff : ∀ d ∈ D, ∀ e ∈ E, |lambda d e| ≤ L) :
    |doubledSelbergGeneralNormalizationError H D E lambda W m q T| ≤
      (D.card : ℝ) ^ 2 * (E.card : ℝ) ^ 2 *
        (L ^ 2 * (allowedPreSieveResidues W m).card) := by
  unfold doubledSelbergGeneralNormalizationError
  apply abs_fourfold_sum_le_card_mul_bound
  intro d hd e he d' hd' e' he'
  rw [abs_mul, abs_mul]
  have hsum :
      |∑ v ∈ allowedPreSieveResidues W m,
          largeGapGeneralCrtClassError H W v m q T d e d' e'| ≤
        (allowedPreSieveResidues W m).card := by
    calc
      |∑ v ∈ allowedPreSieveResidues W m,
          largeGapGeneralCrtClassError H W v m q T d e d' e'| ≤
          ∑ v ∈ allowedPreSieveResidues W m,
            |largeGapGeneralCrtClassError H W v m q T d e d' e'| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _v ∈ allowedPreSieveResidues W m, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro v hv
        exact largeGapGeneralCrtClassError_abs_le_one
          H W v m q T d e d' e' hW
          (support.first_lcm_pos d hd d' hd')
          (support.companion_lcm_pos e he e' he')
      _ = (allowedPreSieveResidues W m).card := by simp
  have hcard : (0 : ℝ) ≤ (allowedPreSieveResidues W m).card := by
    positivity
  calc
    |lambda d e| * |lambda d' e'| *
        |∑ v ∈ allowedPreSieveResidues W m,
          largeGapGeneralCrtClassError H W v m q T d e d' e'| ≤
      L * L * (allowedPreSieveResidues W m).card := by
        gcongr
        · exact hcoeff d hd e he
        · exact hcoeff d' hd' e' he'
    _ = L ^ 2 * (allowedPreSieveResidues W m).card := by ring

/-- Exact unseparated Maynard normalization in its final finite-algebra
form.  The only remaining normalization task is the analytic evaluation of
`doubledSelbergCoordinateLcmKernel`. -/
theorem preSievedStandardDoubledWeightSum_eq_lcmKernel_add_error
    (H : Finset ℕ) (RD RE w m q T : ℕ)
    (lambda : (H → ℕ) → (H → ℕ) → ℝ)
    (hw : 2 ≤ w) (hm : 0 < m) :
    (∑ n ∈ Finset.Icc 0 T,
      if largeGapPreSieved w m n then
        doubledSelbergWeight H
          (BoundedGaps.Maynard.maynardDivisorTupleSupport H RD (primorial w))
          (fullySeparatedCompanionSupport H RE (primorial w) m)
          lambda m q n
      else 0) =
      (((allowedPreSieveResidues (primorial w) m).card : ℝ) * (T : ℝ) /
          primorial w) *
        doubledSelbergCoordinateLcmKernel H
          (BoundedGaps.Maynard.maynardDivisorTupleSupport H RD (primorial w))
          (fullySeparatedCompanionSupport H RE (primorial w) m)
          lambda m q +
        doubledSelbergGeneralNormalizationError H
          (BoundedGaps.Maynard.maynardDivisorTupleSupport H RD (primorial w))
          (fullySeparatedCompanionSupport H RE (primorial w) m)
          lambda (primorial w) m q T := by
  rw [preSievedDoubledWeightSum_eq_generalMain_add_error
    H
    (BoundedGaps.Maynard.maynardDivisorTupleSupport H RD (primorial w))
    (fullySeparatedCompanionSupport H RE (primorial w) m)
    lambda w m q T hw hm (standardDoubledGeneralSupport
      H RD RE (primorial w) m)]
  rw [doubledSelbergGeneralNormalizationMain_standard_eq
    H RD RE (primorial w) m q T (primorial_pos w) lambda]

end

end Erdos4b
