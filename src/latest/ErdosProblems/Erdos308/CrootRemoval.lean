/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos285.Approximation
import ErdosProblems.Erdos285.RoughCounts
import ErdosProblems.Erdos308.Numerics

/-!
# Erdős 308: Croot's large-prime-power removal stage

This is the finite descent used in the proof of the eventual initial-interval
theorem.  It deliberately contains the required residual bookkeeping locally:
the corresponding older module has an unrelated dependency on a PNT package
which is not part of this proof.
-/

namespace Erdos308.CrootRemoval

open Filter Finset Real
open scoped BigOperators Topology

noncomputable section

attribute [local instance] Classical.propDecidable

open Erdos285 Erdos285.PrimePowers Erdos285.RoughCounts

/-! ## Smooth initial sets and residual states -/

def initialSmoothBlock (alpha : ℝ) (x : ℕ) (z : ℝ) : Finset ℕ :=
  (Finset.Ioc ⌊alpha * (x : ℝ)⌋₊ x).filter (UnitFractions.is_smooth z)

@[simp] lemma mem_initialSmoothBlock {alpha z : ℝ} {x n : ℕ} :
    n ∈ initialSmoothBlock alpha x z ↔
      ⌊alpha * (x : ℝ)⌋₊ < n ∧ n ≤ x ∧ UnitFractions.is_smooth z n := by
  simp [initialSmoothBlock, and_assoc]

lemma initialSmoothBlock_zero_not_mem (alpha z : ℝ) (x : ℕ) :
    0 ∉ initialSmoothBlock alpha x z := by
  intro h
  have := (mem_initialSmoothBlock.mp h).1
  omega

lemma initialSmoothBlock_lower {alpha z : ℝ} {x n : ℕ}
    (_halpha : 0 ≤ alpha) (hn : n ∈ initialSmoothBlock alpha x z) :
    alpha * (x : ℝ) < n :=
  Nat.lt_of_floor_lt (mem_initialSmoothBlock.mp hn).1

def initialApproximationState (alpha : ℝ) (x : ℕ) (z : ℝ) :
    Erdos285.ApproximationState where
  selected := initialSmoothBlock alpha x z
  used := initialSmoothBlock alpha x z

structure ResidualApproximationState (r : ℚ) where
  terms : Erdos285.ApproximationState
  residual : ℚ
  balance : UnitFractions.rec_sum terms.selected + residual = r

def ResidualApproximationState.Coherent {r : ℚ}
    (s : ResidualApproximationState r) : Prop :=
  s.terms.selected ⊆ s.terms.used

def residualDelta (d : Erdos285.ApproximationStep) : ℚ :=
  UnitFractions.rec_sum d.remove - UnitFractions.rec_sum d.add

def ResidualApproximationState.applyStep {r : ℚ}
    (s : ResidualApproximationState r) (d : Erdos285.ApproximationStep)
    (hd : d.Valid s.terms) : ResidualApproximationState r where
  terms := s.terms.applyStep d
  residual := s.residual + residualDelta d
  balance := by
    change UnitFractions.rec_sum (s.terms.applyStep d).selected +
      (s.residual + (UnitFractions.rec_sum d.remove - UnitFractions.rec_sum d.add)) = r
    linarith [s.balance, hd.rec_sum_balance]

lemma ResidualApproximationState.Coherent.applyStep {r : ℚ}
    {s : ResidualApproximationState r} {d : Erdos285.ApproximationStep}
    (hd : d.Valid s.terms) :
    (s.applyStep d hd).Coherent :=
  hd.selected_subset_used_after

def ResidualApproximationState.primePowerMeasure {r : ℚ}
    (s : ResidualApproximationState r) : ℕ :=
  largestPrimePowerPart s.residual.den

def eliminationRemovalStep (U : Finset ℕ) : Erdos285.ApproximationStep where
  remove := U
  add := ∅

lemma eliminationRemovalStep_valid {r : ℚ} {s : ResidualApproximationState r}
    (hs : s.Coherent) {U : Finset ℕ} (hU : U ⊆ s.terms.selected) :
    (eliminationRemovalStep U).Valid s.terms := by
  refine ⟨hs, hU, ?_⟩
  simp [eliminationRemovalStep]

lemma eliminationRemovalStep_selected {r : ℚ} {s : ResidualApproximationState r}
    {U : Finset ℕ} (hs : s.Coherent) (hU : U ⊆ s.terms.selected) :
    (s.applyStep (eliminationRemovalStep U)
      (eliminationRemovalStep_valid hs hU)).terms.selected =
        s.terms.selected \ U := by
  simp [ResidualApproximationState.applyStep, Erdos285.ApproximationState.applyStep,
    eliminationRemovalStep]

lemma eliminationRemovalStep_residual {r : ℚ} {s : ResidualApproximationState r}
    {U : Finset ℕ} (hs : s.Coherent) (hU : U ⊆ s.terms.selected) :
    (s.applyStep (eliminationRemovalStep U)
      (eliminationRemovalStep_valid hs hU)).residual =
      s.residual + UnitFractions.rec_sum U := by
  simp [ResidualApproximationState.applyStep, residualDelta,
    eliminationRemovalStep]

def AvailableBelow (base : Finset ℕ) {r : ℚ}
    (s : ResidualApproximationState r) : Prop :=
  ∀ n ∈ base,
    largestPrimePowerPart n ≤ s.primePowerMeasure → n ∈ s.terms.selected

lemma AvailableBelow.eliminationRemovalStep
    {base : Finset ℕ} {r : ℚ} {s : ResidualApproximationState r}
    (havail : AvailableBelow base s) (hs : s.Coherent)
    {U : Finset ℕ} (hU : U ⊆ s.terms.selected)
    (htag : ∀ n ∈ U, largestPrimePowerPart n = s.primePowerMeasure)
    (hdesc :
      (s.applyStep (eliminationRemovalStep U)
        (eliminationRemovalStep_valid hs hU)).primePowerMeasure <
          s.primePowerMeasure) :
    AvailableBelow base
      (s.applyStep (eliminationRemovalStep U)
        (eliminationRemovalStep_valid hs hU)) := by
  intro n hnbase hntag
  have hnold : n ∈ s.terms.selected :=
    havail n hnbase (hntag.trans hdesc.le)
  rw [eliminationRemovalStep_selected hs hU, Finset.mem_sdiff]
  refine ⟨hnold, ?_⟩
  intro hnU
  have := htag n hnU
  omega

/-! ## Smooth-denominator facts -/

lemma isSmooth_of_largestPrimePowerPart_le
    {z : ℝ} {n : ℕ} (hn : n ≠ 0)
    (hmax : (largestPrimePowerPart n : ℝ) ≤ z) :
    UnitFractions.is_smooth z n := by
  intro q hqpp hqdiv
  have hqexact : ∃ exactPart : ℕ,
      exactPart ∈ primePowerParts n ∧ q ∣ exactPart := by
    rcases (isPrimePow_nat_iff q).1 hqpp with ⟨p, k, hp, hk, rfl⟩
    let exactPart := p ^ n.factorization p
    have hkle : k ≤ n.factorization p :=
      (hp.pow_dvd_iff_le_factorization hn).1 hqdiv
    have hfac : n.factorization p ≠ 0 := Nat.ne_zero_of_lt (hk.trans_le hkle)
    refine ⟨exactPart, (mem_primePowerParts hn).2 ?_, ?_⟩
    · refine ⟨hp.isPrimePow.pow hfac, ?_, ?_⟩
      · dsimp [exactPart]
        simpa using Nat.ordProj_dvd n p
      · dsimp [exactPart]
        exact ((UnitFractions.factorization_eq_iff (n := n) hp hfac).2 rfl).2
    · dsimp [exactPart]
      exact pow_dvd_pow p hkle
  obtain ⟨exactPart, hpart, hqpart⟩ := hqexact
  have hpartpos : 0 < exactPart := ((mem_primePowerParts hn).1 hpart).1.pos
  have hqle : (q : ℝ) ≤ exactPart := by
    exact_mod_cast Nat.le_of_dvd hpartpos hqpart
  have hpartmax : (exactPart : ℝ) ≤ largestPrimePowerPart n := by
    exact_mod_cast le_largestPrimePowerPart hpart
  exact hqle.trans (hpartmax.trans hmax)

lemma recSum_den_isSmooth {y : ℝ} {A : Finset ℕ}
    (hzero : ∀ n ∈ A, n ≠ 0)
    (hsmooth : ∀ n ∈ A, UnitFractions.is_smooth y n) :
    UnitFractions.is_smooth y (UnitFractions.rec_sum A).den := by
  intro q hq hqden
  have hqlcm : q ∣ A.lcm id :=
    hqden.trans (Erdos285.PrimePowers.recSum_den_dvd_lcm A)
  obtain ⟨n, hn, hqn⟩ :=
    Erdos308.LargePrime.isPrimePow_dvd_finsetLcm hq hzero hqlcm
  exact hsmooth n hn q hq hqn

lemma sub_recSum_den_isSmooth {y : ℝ} (rho : ℚ) {A : Finset ℕ}
    (hrho : UnitFractions.is_smooth y rho.den)
    (hzero : ∀ n ∈ A, n ≠ 0)
    (hA : ∀ n ∈ A, UnitFractions.is_smooth y n) :
    UnitFractions.is_smooth y (rho - UnitFractions.rec_sum A).den := by
  have hsum := recSum_den_isSmooth hzero hA
  intro q hq hqden
  have hqLcm : q ∣ Nat.lcm rho.den (UnitFractions.rec_sum A).den :=
    hqden.trans (Rat.sub_den_dvd_lcm rho (UnitFractions.rec_sum A))
  rcases Erdos308.LargePrime.isPrimePow_dvd_lcm hq rho.den_ne_zero
      (UnitFractions.rec_sum A).den_ne_zero hqLcm with hqrho | hqsum
  · exact hrho q hq hqrho
  · exact hsum q hq hqsum

lemma largestPrimePowerPart_le_floor_of_isSmooth
    {y : ℝ} {n : ℕ}
    (hsmooth : UnitFractions.is_smooth y n) :
    largestPrimePowerPart n ≤ ⌊y⌋₊ := by
  by_cases hn : 2 ≤ n
  · have hmem := largestPrimePowerPart_mem hn
    have hspec := (mem_primePowerParts (by omega : n ≠ 0)).mp hmem
    exact Nat.le_floor (hsmooth _ hspec.1 hspec.2.1)
  · have hempty : primePowerParts n = ∅ :=
      primePowerParts_empty_iff.mpr (Nat.lt_of_not_ge hn)
    simp [largestPrimePowerPart, hempty]

/-! ## One Croot removal step -/

theorem croot_eliminationRemovalStep
    {r : ℚ} {alpha xi z : ℝ} {x : ℕ}
    {s : ResidualApproximationState r} {M : Finset ℕ}
    (hs : s.Coherent)
    (havail : AvailableBelow (initialSmoothBlock alpha x z) s)
    (hdata : Erdos308.LargePrime.CandidateData xi x s.primePowerMeasure
      (-s.residual) M)
    (hsurj : Erdos308.LargePrime.BoundedInverseSubsetSurjective
      s.primePowerMeasure
      (Erdos308.LargePrime.martinBlockBound x s.primePowerMeasure) M)
    (hxi : (⌊alpha * (x : ℝ)⌋₊ : ℝ) < xi * x)
    (hqz : (s.primePowerMeasure : ℝ) ≤ z) :
    ∃ U : Finset ℕ,
      U.card ≤ Erdos308.LargePrime.martinBlockBound x s.primePowerMeasure ∧
      U ⊆ initialSmoothBlock alpha x z ∧
      ∃ hp : (eliminationRemovalStep U).Valid s.terms,
        (s.applyStep (eliminationRemovalStep U) hp).primePowerMeasure <
          s.primePowerMeasure ∧
        AvailableBelow (initialSmoothBlock alpha x z)
          (s.applyStep (eliminationRemovalStep U) hp) := by
  obtain ⟨U, hUcard, hUint, hUtag, -, hdescNeg⟩ :=
    Erdos308.LargePrime.largePrimePowerElimination hdata hsurj
  have hqspec :=
    (mem_primePowerParts (-s.residual).den_ne_zero).mp hdata.q_part
  have hqpos : 0 < s.primePowerMeasure := hqspec.1.pos
  have hz : 0 ≤ z :=
    (by exact_mod_cast hqpos.le : (0 : ℝ) ≤ s.primePowerMeasure).trans hqz
  have hUbase : U ⊆ initialSmoothBlock alpha x z := by
    intro u hu
    apply mem_initialSmoothBlock.mpr
    have huLowerR : (⌊alpha * (x : ℝ)⌋₊ : ℝ) < u :=
      hxi.trans_le (hUint u hu).1
    have huLower : ⌊alpha * (x : ℝ)⌋₊ < u := by exact_mod_cast huLowerR
    have huUpper : u ≤ x := by exact_mod_cast (hUint u hu).2
    have hu0 : u ≠ 0 := by omega
    have huSmooth : UnitFractions.is_smooth z u := by
      apply isSmooth_of_largestPrimePowerPart_le hu0
      rw [hUtag u hu]
      exact hqz
    exact ⟨huLower, huUpper, huSmooth⟩
  have hUselected : U ⊆ s.terms.selected := by
    intro u hu
    exact havail u (hUbase hu) (by rw [hUtag u hu])
  let hp : (eliminationRemovalStep U).Valid s.terms :=
    eliminationRemovalStep_valid hs hUselected
  have hresidual :
      (s.applyStep (eliminationRemovalStep U) hp).residual =
        s.residual + UnitFractions.rec_sum U :=
    eliminationRemovalStep_residual hs hUselected
  have hdenEq :
      ((-s.residual) - UnitFractions.rec_sum U).den =
        (s.residual + UnitFractions.rec_sum U).den := by
    have heq : (-s.residual) - UnitFractions.rec_sum U =
        -(s.residual + UnitFractions.rec_sum U) := by ring
    rw [heq, Rat.den_neg_eq_den]
  have hdesc :
      (s.applyStep (eliminationRemovalStep U) hp).primePowerMeasure <
        s.primePowerMeasure := by
    rw [ResidualApproximationState.primePowerMeasure, hresidual, ← hdenEq]
    exact hdescNeg
  exact ⟨U, hUcard, hUbase, hp, hdesc,
    havail.eliminationRemovalStep hs hUselected hUtag hdesc⟩

/-! ## Well-founded descent with exact bookkeeping -/

def totalEliminationBudget (x Q : ℕ) : ℕ :=
  ∑ q ∈ Finset.range (Q + 1), Erdos308.LargePrime.martinBlockBound x q

lemma largestPrimePowerPart_mem_of_pos {n : ℕ}
    (hpos : 0 < largestPrimePowerPart n) :
    largestPrimePowerPart n ∈ primePowerParts n := by
  apply largestPrimePowerPart_mem
  by_contra hn
  have hempty : primePowerParts n = ∅ :=
    primePowerParts_empty_iff.mpr (Nat.lt_of_not_ge hn)
  rw [largestPrimePowerPart, hempty] at hpos
  simp at hpos

lemma primePower_dvd_cofactor_lt_largest
    {t : ℚ} {q ell : ℕ}
    (hqpart : q ∈ primePowerParts t.den)
    (hmax : largestPrimePowerPart t.den = q)
    (hellpp : IsPrimePow ell) (helldiv : ell ∣ t.den / q) : ell < q := by
  have hqspec := (mem_primePowerParts t.den_ne_zero).mp hqpart
  have hellden : ell ∣ t.den :=
    helldiv.trans (Nat.div_dvd_of_dvd hqspec.2.1)
  have hsmooth : UnitFractions.is_smooth (q : ℝ) t.den := by
    apply isSmooth_of_largestPrimePowerPart_le t.den_ne_zero
    rw [hmax]
  have hellle : ell ≤ q := by exact_mod_cast hsmooth ell hellpp hellden
  have hellne : ell ≠ q := by
    intro heq
    subst ell
    have hqone := Nat.eq_one_of_dvd_coprimes hqspec.2.2 dvd_rfl helldiv
    exact hqspec.1.ne_one hqone
  exact lt_of_le_of_ne hellle hellne

structure RemovalDescentOutcome
    (base : Finset ℕ) (x y : ℕ) {r : ℚ}
    (start : ResidualApproximationState r) where
  final : ResidualApproximationState r
  removed : Finset ℕ
  coherent : final.Coherent
  available : AvailableBelow base final
  measure_le : final.primePowerMeasure ≤ y
  removed_subset_base : removed ⊆ base
  removed_subset_selected : removed ⊆ start.terms.selected
  selected_eq : final.terms.selected = start.terms.selected \ removed
  used_eq : final.terms.used = start.terms.used
  residual_eq : final.residual = start.residual + UnitFractions.rec_sum removed
  card_le : removed.card ≤ totalEliminationBudget x start.primePowerMeasure

lemma eliminationRemovalStep_used {r : ℚ} {s : ResidualApproximationState r}
    {U : Finset ℕ} (hs : s.Coherent) (hU : U ⊆ s.terms.selected) :
    (s.applyStep (eliminationRemovalStep U)
      (eliminationRemovalStep_valid hs hU)).terms.used = s.terms.used := by
  simp [ResidualApproximationState.applyStep, Erdos285.ApproximationState.applyStep,
    eliminationRemovalStep]

noncomputable def exists_removalDescentOutcome
    (base : Finset ℕ) (x y measureBound : ℕ) {r : ℚ}
    (start : ResidualApproximationState r) (hcoh : start.Coherent)
    (havail : AvailableBelow base start)
    (hbound : start.primePowerMeasure ≤ measureBound)
    (hstep : ∀ s : ResidualApproximationState r, s.Coherent →
      AvailableBelow base s → s.primePowerMeasure ≤ measureBound →
      y < s.primePowerMeasure →
      ∃ U : Finset ℕ,
        U.card ≤ Erdos308.LargePrime.martinBlockBound x s.primePowerMeasure ∧
        U ⊆ base ∧
        ∃ hp : (eliminationRemovalStep U).Valid s.terms,
          (s.applyStep (eliminationRemovalStep U) hp).primePowerMeasure <
            s.primePowerMeasure ∧
          AvailableBelow base (s.applyStep (eliminationRemovalStep U) hp)) :
    RemovalDescentOutcome base x y start := by
  induction hmeasure : start.primePowerMeasure using Nat.strongRecOn generalizing start with
  | ind q ih =>
      by_cases hdone : start.primePowerMeasure ≤ y
      · exact
          { final := start
            removed := ∅
            coherent := hcoh
            available := havail
            measure_le := hdone
            removed_subset_base := by simp
            removed_subset_selected := by simp
            selected_eq := by simp
            used_eq := rfl
            residual_eq := by simp
            card_le := by simp [totalEliminationBudget] }
      · have habove : y < start.primePowerMeasure := Nat.lt_of_not_ge hdone
        let hstage := hstep start hcoh havail hbound habove
        let U : Finset ℕ := Classical.choose hstage
        have hUfacts := Classical.choose_spec hstage
        have hUcard : U.card ≤
            Erdos308.LargePrime.martinBlockBound x start.primePowerMeasure :=
          hUfacts.1
        have hUbase : U ⊆ base := hUfacts.2.1
        let hp : (eliminationRemovalStep U).Valid start.terms :=
          Classical.choose hUfacts.2.2
        have hpFacts := Classical.choose_spec hUfacts.2.2
        have hdesc :
            (start.applyStep (eliminationRemovalStep U) hp).primePowerMeasure <
              start.primePowerMeasure := hpFacts.1
        have hnextAvail : AvailableBelow base
            (start.applyStep (eliminationRemovalStep U) hp) := hpFacts.2
        have hUselected : U ⊆ start.terms.selected := hp.2.1
        let next := start.applyStep (eliminationRemovalStep U) hp
        have hnextCoh : next.Coherent :=
          ResidualApproximationState.Coherent.applyStep hp
        have hnextSelected : next.terms.selected = start.terms.selected \ U := by
          simp [next, ResidualApproximationState.applyStep,
            Erdos285.ApproximationState.applyStep, eliminationRemovalStep]
        have hnextMeasure : next.primePowerMeasure < q := by
          rw [← hmeasure]
          exact hdesc
        have hnextBound : next.primePowerMeasure ≤ measureBound :=
          hdesc.le.trans hbound
        have tail :=
          ih next.primePowerMeasure hnextMeasure next hnextCoh hnextAvail hnextBound rfl
        let removed := U ∪ tail.removed
        have hdisjoint : Disjoint U tail.removed := by
          rw [Finset.disjoint_left]
          intro n hnU hnTail
          have hnNext : n ∈ next.terms.selected := tail.removed_subset_selected hnTail
          have hnDiff : n ∈ start.terms.selected \ U := by
            rwa [hnextSelected] at hnNext
          exact (Finset.mem_sdiff.mp hnDiff).2 hnU
        refine
          { final := tail.final
            removed := removed
            coherent := tail.coherent
            available := tail.available
            measure_le := tail.measure_le
            removed_subset_base := ?_
            removed_subset_selected := ?_
            selected_eq := ?_
            used_eq := ?_
            residual_eq := ?_
            card_le := ?_ }
        · intro n hn
          rcases Finset.mem_union.mp hn with hnU | hnTail
          · exact hUbase hnU
          · exact tail.removed_subset_base hnTail
        · intro n hn
          rcases Finset.mem_union.mp hn with hnU | hnTail
          · exact hUselected hnU
          · have hnNext := tail.removed_subset_selected hnTail
            have hnDiff : n ∈ start.terms.selected \ U := by
              rwa [hnextSelected] at hnNext
            exact (Finset.mem_sdiff.mp hnDiff).1
        · rw [tail.selected_eq]
          ext n
          simp only [hnextSelected, Finset.mem_sdiff]
          simp [removed]
          tauto
        · rw [tail.used_eq]
          exact eliminationRemovalStep_used hcoh hUselected
        · rw [tail.residual_eq]
          have hnextResidual : next.residual =
              start.residual + UnitFractions.rec_sum U := by
            simpa [next] using eliminationRemovalStep_residual hcoh hUselected
          rw [hnextResidual, UnitFractions.rec_sum_disjoint hdisjoint]
          ring
        · rw [Finset.card_union_of_disjoint hdisjoint]
          have htailBudget :
              totalEliminationBudget x next.primePowerMeasure ≤
                ∑ i ∈ Finset.range start.primePowerMeasure,
                  Erdos308.LargePrime.martinBlockBound x i := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · exact Finset.range_mono hdesc
            · simp
          calc
            U.card + tail.removed.card ≤
                Erdos308.LargePrime.martinBlockBound x start.primePowerMeasure +
                  totalEliminationBudget x next.primePowerMeasure :=
              Nat.add_le_add hUcard tail.card_le
            _ ≤ Erdos308.LargePrime.martinBlockBound x start.primePowerMeasure +
                ∑ i ∈ Finset.range start.primePowerMeasure,
                  Erdos308.LargePrime.martinBlockBound x i :=
              Nat.add_le_add_left htailBudget _
            _ = totalEliminationBudget x start.primePowerMeasure := by
              rw [totalEliminationBudget, Finset.sum_range_succ]
              omega

/-! ## Uniform descent for integral targets -/

def proposition6MainCutoff (x : ℕ) : ℝ :=
  (x : ℝ) / Real.log (x : ℝ) ^ 30

def mainCutoffNat (x : ℕ) : ℕ := logPowerCutoff 30 x

lemma mainCutoffNat_eq (x : ℕ) :
    mainCutoffNat x = ⌊proposition6MainCutoff x⌋₊ := rfl

def fullSmoothBlock (x : ℕ) (z : ℝ) : Finset ℕ :=
  initialSmoothBlock 0 x z

def removalBase (x : ℕ) (z : ℝ) : Finset ℕ :=
  initialSmoothBlock
    ((9 / 10 : ℝ) * Erdos308.Numerics.crootIntervalRatio) x z

def initialResidual (k x : ℕ) (z : ℝ) : ℚ :=
  (k : ℚ) - UnitFractions.rec_sum (fullSmoothBlock x z)

def initialState (k x : ℕ) (z : ℝ) : ResidualApproximationState (k : ℚ) where
  terms := initialApproximationState 0 x z
  residual := initialResidual k x z
  balance := by simp [initialResidual, fullSmoothBlock, initialApproximationState]

lemma initialState_coherent (k x : ℕ) (z : ℝ) :
    (initialState k x z).Coherent := Finset.Subset.rfl

lemma removalBase_subset_fullSmoothBlock (x : ℕ) (z : ℝ) :
    removalBase x z ⊆ fullSmoothBlock x z := by
  intro n hn
  rw [removalBase, mem_initialSmoothBlock] at hn
  rw [fullSmoothBlock, mem_initialSmoothBlock]
  exact ⟨by simpa using Nat.zero_lt_of_lt hn.1, hn.2⟩

lemma initialState_available (k x : ℕ) (z : ℝ) :
    AvailableBelow (removalBase x z) (initialState k x z) := by
  intro n hn _
  exact removalBase_subset_fullSmoothBlock x z hn

lemma nat_target_smooth (k : ℕ) (z : ℝ) :
    UnitFractions.is_smooth z (k : ℚ).den := by
  intro q hq hqdiv
  have hqone : q = 1 := Nat.dvd_one.mp (by simpa using hqdiv)
  exact (hq.ne_one hqone).elim

lemma initialResidual_den_isSmooth
    {k x : ℕ} {z : ℝ} :
    UnitFractions.is_smooth z (initialResidual k x z).den := by
  rw [initialResidual]
  apply sub_recSum_den_isSmooth (k : ℚ) (nat_target_smooth k z)
  · intro n hn hn0
    subst n
    exact initialSmoothBlock_zero_not_mem 0 z x hn
  · intro n hn
    exact (mem_initialSmoothBlock.mp hn).2.2

lemma initialState_measure_le_floor {k x : ℕ} {z : ℝ} :
    (initialState k x z).primePowerMeasure ≤ ⌊z⌋₊ := by
  apply largestPrimePowerPart_le_floor_of_isSmooth
  exact initialResidual_den_isSmooth

def selectedResidual (k : ℕ) (S : Finset ℕ) : ℚ :=
  (k : ℚ) - UnitFractions.rec_sum S

def selectedState (k : ℕ) (S : Finset ℕ) :
    ResidualApproximationState (k : ℚ) where
  terms := { selected := S, used := S }
  residual := selectedResidual k S
  balance := by simp [selectedResidual]

lemma selectedState_coherent (k : ℕ) (S : Finset ℕ) :
    (selectedState k S).Coherent := Finset.Subset.rfl

lemma selectedState_available {k x : ℕ} {z : ℝ} {S : Finset ℕ}
    (hbase : removalBase x z ⊆ S) :
    AvailableBelow (removalBase x z) (selectedState k S) := by
  intro n hn _
  exact hbase hn

lemma selectedResidual_den_isSmooth {k x : ℕ} {z : ℝ} {S : Finset ℕ}
    (hS : S ⊆ fullSmoothBlock x z) :
    UnitFractions.is_smooth z (selectedResidual k S).den := by
  rw [selectedResidual]
  apply sub_recSum_den_isSmooth (k : ℚ) (nat_target_smooth k z)
  · intro n hn hn0
    subst n
    exact initialSmoothBlock_zero_not_mem 0 z x (hS hn)
  · intro n hn
    exact (mem_initialSmoothBlock.mp (hS hn)).2.2

lemma selectedState_measure_le_floor {k x : ℕ} {z : ℝ} {S : Finset ℕ}
    (hS : S ⊆ fullSmoothBlock x z) :
    (selectedState k S).primePowerMeasure ≤ ⌊z⌋₊ := by
  apply largestPrimePowerPart_le_floor_of_isSmooth
  exact selectedResidual_den_isSmooth hS

theorem eventually_crootRemovalDescent_from :
    ∀ᶠ x : ℕ in atTop, ∀ (k : ℕ) (S : Finset ℕ),
      S ⊆ fullSmoothBlock x (proposition6MainCutoff x) →
      removalBase x (proposition6MainCutoff x) ⊆ S →
      Nonempty (RemovalDescentOutcome
        (removalBase x (proposition6MainCutoff x)) x
        (Erdos285.approximationCorrectionScale x)
        (selectedState k S)) := by
  have hlogTop : Tendsto (fun x : ℕ ↦ Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [Erdos308.Numerics.eventually_crootStepData,
    eventually_ge_atTop 1, hlogTop.eventually_ge_atTop 1]
      with x hstepData hx hlog
  intro k S hSfull hbase
  let z := proposition6MainCutoff x
  let y := Erdos285.approximationCorrectionScale x
  let Q := ⌊z⌋₊
  let start := selectedState k S
  let alpha := (9 / 10 : ℝ) * Erdos308.Numerics.crootIntervalRatio
  let xi := Erdos308.Numerics.crootIntervalRatio
  have hz : 0 ≤ z := by
    dsimp [z, proposition6MainCutoff]
    positivity
  have hbound : start.primePowerMeasure ≤ Q :=
    selectedState_measure_le_floor (by simpa [z] using hSfull)
  have hQz : (Q : ℝ) ≤ z := Nat.floor_le hz
  have halpha : 0 ≤ alpha := by
    dsimp [alpha, Erdos308.Numerics.crootIntervalRatio,
      Erdos308.Numerics.crootCandidateRatio]
    positivity
  have hAlphaXi : alpha < xi := by
    dsimp [alpha, xi, Erdos308.Numerics.crootIntervalRatio,
      Erdos308.Numerics.crootCandidateRatio]
    norm_num
  have hxi : (⌊alpha * (x : ℝ)⌋₊ : ℝ) < xi * x := by
    have hfloor : (⌊alpha * (x : ℝ)⌋₊ : ℝ) ≤ alpha * x :=
      Nat.floor_le (mul_nonneg halpha (Nat.cast_nonneg x))
    have hxR : (0 : ℝ) < x := by exact_mod_cast (Nat.zero_lt_of_lt hx)
    exact hfloor.trans_lt (mul_lt_mul_of_pos_right hAlphaXi hxR)
  have hstep : ∀ s : ResidualApproximationState (k : ℚ),
      s.Coherent → AvailableBelow (removalBase x z) s →
      s.primePowerMeasure ≤ Q → y < s.primePowerMeasure →
      ∃ U : Finset ℕ,
        U.card ≤ Erdos308.LargePrime.martinBlockBound x s.primePowerMeasure ∧
        U ⊆ removalBase x z ∧
        ∃ hp : (eliminationRemovalStep U).Valid s.terms,
          (s.applyStep (eliminationRemovalStep U) hp).primePowerMeasure <
            s.primePowerMeasure ∧
          AvailableBelow (removalBase x z)
            (s.applyStep (eliminationRemovalStep U) hp) := by
    intro s hs havail hsQ hys
    have hrootLt : (x : ℝ) ^ ((5 : ℝ)⁻¹) <
        ((⌊(x : ℝ) ^ ((5 : ℝ)⁻¹)⌋₊ + 1 : ℕ) : ℝ) := by
      simpa using Nat.lt_floor_add_one ((x : ℝ) ^ ((5 : ℝ)⁻¹))
    have hsucc : ⌊(x : ℝ) ^ ((5 : ℝ)⁻¹)⌋₊ + 1 ≤
        s.primePowerMeasure := by
      change y + 1 ≤ s.primePowerMeasure
      omega
    have hstrong : Erdos308.Numerics.InStrongEliminationRange
        x s.primePowerMeasure := by
      constructor
      · have hsuccR :
          ((⌊(x : ℝ) ^ ((5 : ℝ)⁻¹)⌋₊ + 1 : ℕ) : ℝ) ≤
            (s.primePowerMeasure : ℝ) := by exact_mod_cast hsucc
        simpa only [show ((5 : ℝ)⁻¹) = (1 : ℝ) / 5 by norm_num] using
          hrootLt.le.trans hsuccR
      · have hqQ : (s.primePowerMeasure : ℝ) ≤ Q := by exact_mod_cast hsQ
        calc
          (s.primePowerMeasure : ℝ) ≤ z := hqQ.trans hQz
          _ = (x : ℝ) * Real.log x ^ (-30 : ℝ) := by
            dsimp [z, proposition6MainCutoff]
            rw [show (-30 : ℝ) = -(30 : ℝ) by norm_num,
              Real.rpow_neg (zero_lt_one.trans_le hlog).le,
              show (30 : ℝ) = ((30 : ℕ) : ℝ) by norm_num,
              Real.rpow_natCast]
            ring
    have hqpos : 0 < s.primePowerMeasure := by omega
    have hqpartResidual : s.primePowerMeasure ∈
        primePowerParts s.residual.den := largestPrimePowerPart_mem_of_pos hqpos
    have hqpart : s.primePowerMeasure ∈
        primePowerParts (-s.residual).den := by simpa using hqpartResidual
    have hqspec := (mem_primePowerParts (-s.residual).den_ne_zero).mp hqpart
    have hcofactor : ∀ ell : ℕ, IsPrimePow ell →
        ell ∣ (-s.residual).den / s.primePowerMeasure →
        ell < s.primePowerMeasure := by
      intro ell hellpp helldiv
      apply primePower_dvd_cofactor_lt_largest hqpart
      · simp [ResidualApproximationState.primePowerMeasure]
      · exact hellpp
      · exact helldiv
    obtain ⟨M, hdata, hsurj⟩ := hstepData s.primePowerMeasure
      (-s.residual) hqspec.1 hstrong hqpart hcofactor
    have havail' : AvailableBelow (initialSmoothBlock alpha x z) s := by
      simpa [removalBase, alpha] using havail
    have hout := croot_eliminationRemovalStep hs havail' hdata hsurj
      hxi (by
        have hqQ : (s.primePowerMeasure : ℝ) ≤ Q := by exact_mod_cast hsQ
        exact hqQ.trans hQz)
    simpa [removalBase, alpha] using hout
  exact ⟨exists_removalDescentOutcome
    (removalBase x z) x y Q start
    (selectedState_coherent k S)
    (selectedState_available (by simpa [z] using hbase)) hbound hstep⟩

theorem eventually_crootRemovalDescent :
    ∀ᶠ x : ℕ in atTop, ∀ k : ℕ,
      Nonempty (RemovalDescentOutcome
        (removalBase x (proposition6MainCutoff x)) x
        (Erdos285.approximationCorrectionScale x)
        (initialState k x (proposition6MainCutoff x))) := by
  filter_upwards [eventually_crootRemovalDescent_from] with x hx
  intro k
  have h := hx k (fullSmoothBlock x (proposition6MainCutoff x))
    Finset.Subset.rfl (removalBase_subset_fullSmoothBlock _ _)
  simpa [initialState, selectedState, initialResidual, selectedResidual,
    initialApproximationState, fullSmoothBlock] using h

end

end Erdos308.CrootRemoval

#print axioms Erdos308.CrootRemoval.eventually_crootRemovalDescent
