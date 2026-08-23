import ErdosProblems.Erdos1166.Erdos1166HLOZDecomposition
import ErdosProblems.Erdos1166.Erdos1166HLOZGreenBounds
import ErdosProblems.Erdos1166.Erdos1166HLOZProp45Union

/-!
An original-time algebraic model for the finite Chernoff/union step in
HLOZ Proposition 4.5.  Its horizon `N` is an original walk time.  Thus the
declarations in this file do **not** by themselves identify the source event,
whose deterministic comparison horizon is an external-chain time and whose
original-time realization uses an inverse external clock (or the stopped
time `T_m^k`).  The source-clock bridge is kept separate so that a fixed-
original-time negative-binomial law is never confused with Proposition 4.3.
-/

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal BigOperators

namespace Erdos1166.HLOZProp45Theta

open HLOZFoundation HLOZDecomposition HLOZUrn
open KilledGreen HLOZProp45Union

/-- The even chessboard class used for the unprimed decomposition. -/
def thetaChessEven (x : Site) : Prop := Even (x.1 + x.2)

lemma negBinMeasure_apply_singleton (i j : ℕ) :
    negBinMeasure i {j} = ENNReal.ofReal (negBinMass i j) := by
  rw [← ENNReal.ofReal_toReal (measure_ne_top (negBinMeasure i) {j})]
  exact congrArg ENNReal.ofReal (negBinMeasure_real_singleton i j)

lemma negBinMeasure_upperTail (i : ℕ) (hi : 1 ≤ i) (b : ℝ) :
    negBinMeasure i {j : ℕ | b ≤ (j : ℝ)} = ENNReal.ofReal (negBinUpperTail i b) := by
  let S : Set ℕ := {j : ℕ | b ≤ (j : ℝ)}
  have hS : S = ⋃ j : S, ({j.1} : Set ℕ) := by
    ext j
    simp [S]
  change negBinMeasure i S = _
  rw [hS, measure_iUnion]
  · calc
      ∑' j : S, negBinMeasure i {j.1} =
          ∑' j : S, ENNReal.ofReal (negBinMass i j.1) := by
        apply tsum_congr
        intro j
        exact negBinMeasure_apply_singleton i j.1
      _ = ENNReal.ofReal (∑' j : S, negBinMass i j.1) := by
        rw [ENNReal.ofReal_tsum_of_nonneg]
        · intro j
          exact negBinMass_nonneg i j.1
        · exact (negBinMass_summable i hi).subtype _
      _ = ENNReal.ofReal (negBinUpperTail i b) := by
        apply congrArg ENNReal.ofReal
        rw [negBinUpperTail, tsum_subtype]
        apply tsum_congr
        intro j
        simp [S, Set.indicator_apply]
  · intro j k hjk
    simp only [Function.onFun, Set.disjoint_singleton]
    exact fun h ↦ hjk (Subtype.ext h)
  · intro j
    exact measurableSet_singleton j.1

lemma negBinMeasure_lowerTail (i : ℕ) (hi : 1 ≤ i) (b : ℝ) :
    negBinMeasure i {j : ℕ | (j : ℝ) ≤ b} = ENNReal.ofReal (negBinLowerTail i b) := by
  let S : Set ℕ := {j : ℕ | (j : ℝ) ≤ b}
  have hS : S = ⋃ j : S, ({j.1} : Set ℕ) := by
    ext j
    simp [S]
  change negBinMeasure i S = _
  rw [hS, measure_iUnion]
  · calc
      ∑' j : S, negBinMeasure i {j.1} =
          ∑' j : S, ENNReal.ofReal (negBinMass i j.1) := by
        apply tsum_congr
        intro j
        exact negBinMeasure_apply_singleton i j.1
      _ = ENNReal.ofReal (∑' j : S, negBinMass i j.1) := by
        rw [ENNReal.ofReal_tsum_of_nonneg]
        · intro j
          exact negBinMass_nonneg i j.1
        · exact (negBinMass_summable i hi).subtype _
      _ = ENNReal.ofReal (negBinLowerTail i b) := by
        apply congrArg ENNReal.ofReal
        rw [negBinLowerTail, tsum_subtype]
        apply tsum_congr
        intro j
        simp [S, Set.indicator_apply]
  · intro j k hjk
    simp only [Function.onFun, Set.disjoint_singleton]
    exact fun h ↦ hjk (Subtype.ext h)
  · intro j
    exact measurableSet_singleton j.1

lemma hasLaw_negBin_upperDeviation_le_exp
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (X : Ω → ℕ) {i : ℕ} (hi : 1 ≤ i) (d : ℝ)
    (hd0 : 0 ≤ d) (hdi : d ≤ i)
    (hLaw : HasLaw X (negBinMeasure i) μ) :
    μ {ω | (i : ℝ) / 15 + d ≤ X ω} ≤
      ENNReal.ofReal (Real.exp (-(d ^ 2 / (4 * (i : ℝ))))) := by
  have hEq := hLaw.measure_eq
    (p := fun j : ℕ ↦ (i : ℝ) / 15 + d ≤ (j : ℝ))
    (show MeasurableSet {j : ℕ | (i : ℝ) / 15 + d ≤ (j : ℝ)} from
      (Set.countable_univ.mono (Set.subset_univ _)).measurableSet)
  rw [hEq]
  rw [negBinMeasure_upperTail i hi]
  exact ENNReal.ofReal_le_ofReal (negBinUpperTail_le_exp i hi d hd0 hdi)

lemma hasLaw_negBin_lowerDeviation_le_exp
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (X : Ω → ℕ) {i : ℕ} (hi : 1 ≤ i) (d : ℝ)
    (hd0 : 0 ≤ d) (hdi : d ≤ i)
    (hLaw : HasLaw X (negBinMeasure i) μ) :
    μ {ω | (X ω : ℝ) ≤ (i : ℝ) / 15 - d} ≤
      ENNReal.ofReal (Real.exp (-(d ^ 2 / (4 * (i : ℝ))))) := by
  have hEq := hLaw.measure_eq
    (p := fun j : ℕ ↦ (j : ℝ) ≤ (i : ℝ) / 15 - d)
    (show MeasurableSet {j : ℕ | (j : ℝ) ≤ (i : ℝ) / 15 - d} from
      (Set.countable_univ.mono (Set.subset_univ _)).measurableSet)
  rw [hEq]
  rw [negBinMeasure_lowerTail i hi]
  exact ENNReal.ofReal_le_ofReal (negBinLowerTail_le_exp i hi d hd0 hdi)

/-- The deterministic finite site set which contains every location reached
by the canonical planar walk through time `N`. -/
noncomputable def horizonSites (N : ℕ) : Finset Site := squareDisk N

/-- Even-lattice half of the deterministic horizon box. -/
noncomputable def evenHorizonSites (N : ℕ) : Finset Site := by
  classical
  exact (horizonSites N).filter thetaChessEven

lemma simpleRandomWalk_mem_horizonSites
    (ω : ℕ → Direction) {n N : ℕ} (hn : n ≤ N) :
    simpleRandomWalk ω n ∈ horizonSites N :=
  simpleRandomWalk_mem_squareDisk_of_time_le ω hn

/-- Original-time analogue of the one-site lower-imbalance clause in HLOZ
(4.16): external local time is too low although total local time is in
`[a,b)`. -/
def thetaMinusAt (N lowerCut a b : ℕ) (x : Site) : Set (ℕ → Site) :=
  {s | paperExternalLocalTime s N x ≤ lowerCut ∧
    a ≤ localTime s N x ∧ localTime s N x < b}

/-- Original-time analogue of the one-site upper-imbalance clause. -/
def thetaPlusAt (N upperCut a b : ℕ) (x : Site) : Set (ℕ → Site) :=
  {s | upperCut < paperExternalLocalTime s N x ∧
    a ≤ localTime s N x ∧ localTime s N x < b}

/-- The fixed-original-time `Theta^-` model, restricted to the even lattice. -/
def thetaMinusEvent (N lowerCut a b : ℕ) : Set (ℕ → Site) :=
  ⋃ x ∈ evenHorizonSites N, thetaMinusAt N lowerCut a b x

/-- The finite-horizon unprimed `Theta^+` event. -/
def thetaPlusEvent (N upperCut a b : ℕ) : Set (ℕ → Site) :=
  ⋃ x ∈ evenHorizonSites N, thetaPlusAt N upperCut a b x

/-- Union of the two fixed-original-time imbalance models. -/
def thetaEvent (N lowerCut upperCut a b : ℕ) : Set (ℕ → Site) :=
  thetaMinusEvent N lowerCut a b ∪ thetaPlusEvent N upperCut a b

lemma measurable_paperLazyLocalTime (N : ℕ) (x : Site) :
    Measurable (fun s ↦ paperLazyLocalTime s N x) :=
  (measurable_paperLazyLocalTime_lookahead N x).mono
    (canonicalFiltration.le (N + 1)) le_rfl

lemma measurable_paperExternalLocalTime (N : ℕ) (x : Site) :
    Measurable (fun s ↦ paperExternalLocalTime s N x) :=
  (measurable_paperExternalLocalTime_lookahead N x).mono
    (canonicalFiltration.le (N + 1)) le_rfl

lemma measurable_localTime (N : ℕ) (x : Site) :
    Measurable (fun s ↦ localTime s N x) :=
  (adapted_localTime x N).mono (canonicalFiltration.le N) le_rfl

lemma measurableSet_thetaMinusAt (N lowerCut a b : ℕ) (x : Site) :
    MeasurableSet (thetaMinusAt N lowerCut a b x) := by
  have hlow : MeasurableSet {s : ℕ → Site |
      paperExternalLocalTime s N x ≤ lowerCut} :=
    measurableSet_le (measurable_paperExternalLocalTime N x) measurable_const
  have ha : MeasurableSet {s : ℕ → Site | a ≤ localTime s N x} :=
    measurableSet_le measurable_const (measurable_localTime N x)
  have hb : MeasurableSet {s : ℕ → Site | localTime s N x < b} :=
    measurableSet_lt (measurable_localTime N x) measurable_const
  simpa only [thetaMinusAt, Set.ofPred_and] using hlow.inter (ha.inter hb)

lemma measurableSet_thetaPlusAt (N upperCut a b : ℕ) (x : Site) :
    MeasurableSet (thetaPlusAt N upperCut a b x) := by
  have hupp : MeasurableSet {s : ℕ → Site |
      upperCut < paperExternalLocalTime s N x} :=
    measurableSet_lt measurable_const (measurable_paperExternalLocalTime N x)
  have ha : MeasurableSet {s : ℕ → Site | a ≤ localTime s N x} :=
    measurableSet_le measurable_const (measurable_localTime N x)
  have hb : MeasurableSet {s : ℕ → Site | localTime s N x < b} :=
    measurableSet_lt (measurable_localTime N x) measurable_const
  simpa only [thetaPlusAt, Set.ofPred_and] using hupp.inter (ha.inter hb)

lemma measurableSet_thetaMinusEvent (N lowerCut a b : ℕ) :
    MeasurableSet (thetaMinusEvent N lowerCut a b) := by
  apply MeasurableSet.iUnion
  intro x
  apply MeasurableSet.iUnion
  intro hx
  exact measurableSet_thetaMinusAt N lowerCut a b x

lemma measurableSet_thetaPlusEvent (N upperCut a b : ℕ) :
    MeasurableSet (thetaPlusEvent N upperCut a b) := by
  apply MeasurableSet.iUnion
  intro x
  apply MeasurableSet.iUnion
  intro hx
  exact measurableSet_thetaPlusAt N upperCut a b x

lemma measurableSet_thetaEvent (N lowerCut upperCut a b : ℕ) :
    MeasurableSet (thetaEvent N lowerCut upperCut a b) :=
  (measurableSet_thetaMinusEvent N lowerCut a b).union
    (measurableSet_thetaPlusEvent N upperCut a b)

/-- Fixed-external-profile event used after conditioning in Proposition 4.3. -/
def externalProfileEvent (sites : Finset Site) (N : ℕ)
    (profile : Site → ℕ) : Set (ℕ → Site) :=
  {s | ∀ x ∈ sites, paperExternalLocalTime s N x = profile x}

lemma measurableSet_externalProfileEvent (sites : Finset Site) (N : ℕ)
    (profile : Site → ℕ) : MeasurableSet (externalProfileEvent sites N profile) := by
  rw [externalProfileEvent]
  simp only [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro x
  apply MeasurableSet.iInter
  intro hx
  exact measurableSet_eq_fun (measurable_paperExternalLocalTime N x) measurable_const

/-- The upper-tail coordinate event to which a lower external imbalance is
reduced using the exact lazy/external identity (2.14). -/
def lazyUpperDeviationAt (N : ℕ) (profile : Site → ℕ)
    (deviation : Site → ℝ) (x : Site) : Set (ℕ → Site) :=
  {s | (profile x : ℝ) / 15 + deviation x ≤ paperLazyLocalTime s N x}

/-- The lower-tail coordinate event used for `Theta^+`. -/
def lazyLowerDeviationAt (N : ℕ) (profile : Site → ℕ)
    (deviation : Site → ℝ) (x : Site) : Set (ℕ → Site) :=
  {s | (paperLazyLocalTime s N x : ℝ) ≤
    (profile x : ℝ) / 15 - deviation x}

lemma measurableSet_lazyUpperDeviationAt (N : ℕ) (profile : Site → ℕ)
    (deviation : Site → ℝ) (x : Site) :
    MeasurableSet (lazyUpperDeviationAt N profile deviation x) := by
  have hcast : Measurable (fun s : ℕ → Site ↦
      (paperLazyLocalTime s N x : ℝ)) :=
    (measurable_of_countable (fun n : ℕ ↦ (n : ℝ))).comp
      (measurable_paperLazyLocalTime N x)
  simpa only [lazyUpperDeviationAt] using
    (measurableSet_le measurable_const hcast)

lemma measurableSet_lazyLowerDeviationAt (N : ℕ) (profile : Site → ℕ)
    (deviation : Site → ℝ) (x : Site) :
    MeasurableSet (lazyLowerDeviationAt N profile deviation x) := by
  have hcast : Measurable (fun s : ℕ → Site ↦
      (paperLazyLocalTime s N x : ℝ)) :=
    (measurable_of_countable (fun n : ℕ ↦ (n : ℝ))).comp
      (measurable_paperLazyLocalTime N x)
  simpa only [lazyLowerDeviationAt] using
    (measurableSet_le hcast measurable_const)

/-- Deterministic reduction of `Theta^-`, after the external profile has
been fixed, to coordinate negative-binomial upper deviations. -/
theorem inter_thetaMinus_subset_lazyUpperDeviation
    (C : Set (ℕ → Site)) (sites : Finset Site) (N lowerCut a b : ℕ)
    (profile : Site → ℕ) (deviation : Site → ℝ)
    (hC : C ⊆ externalProfileEvent sites N profile)
    (hsite : evenHorizonSites N ⊆ sites)
    (hthreshold : ∀ x ∈ evenHorizonSites N, profile x ≤ lowerCut →
      (profile x : ℝ) / 15 + deviation x ≤ (a : ℝ) - profile x) :
    C ∩ thetaMinusEvent N lowerCut a b ⊆
      ⋃ x ∈ (evenHorizonSites N).filter (fun x ↦ profile x ≤ lowerCut),
        lazyUpperDeviationAt N profile deviation x := by
  rintro s ⟨hsC, hsTheta⟩
  rw [thetaMinusEvent] at hsTheta
  simp only [Set.mem_iUnion] at hsTheta ⊢
  rcases hsTheta with ⟨x, hx, hsx⟩
  have hprofile := hC hsC x (hsite hx)
  refine ⟨x, Finset.mem_filter.mpr ⟨hx, hprofile ▸ hsx.1⟩, ?_⟩
  · have hid := localTime_eq_paperExternal_add_paperLazy s N x
    have hneed := hthreshold x hx (hprofile ▸ hsx.1)
    rw [lazyUpperDeviationAt, Set.mem_ofPred_eq]
    have hintNat : a ≤ profile x + paperLazyLocalTime s N x := by
      rw [← hprofile, ← hid]
      exact hsx.2.1
    have hint : (a : ℝ) ≤
        (profile x : ℝ) + paperLazyLocalTime s N x := by
      exact_mod_cast hintNat
    exact hneed.trans (by linarith)

/-- Deterministic reduction of `Theta^+` to lower deviations. The threshold
hypothesis is the exact integer-to-real implication needed from the upper
cut in (4.16). -/
theorem inter_thetaPlus_subset_lazyLowerDeviation
    (C : Set (ℕ → Site)) (sites : Finset Site) (N upperCut a b : ℕ)
    (profile : Site → ℕ) (deviation : Site → ℝ)
    (hC : C ⊆ externalProfileEvent sites N profile)
    (hsite : evenHorizonSites N ⊆ sites)
    (hthreshold : ∀ x ∈ evenHorizonSites N, upperCut < profile x →
      ∀ l : ℕ, profile x + l < b →
        (l : ℝ) ≤ (profile x : ℝ) / 15 - deviation x) :
    C ∩ thetaPlusEvent N upperCut a b ⊆
      ⋃ x ∈ (evenHorizonSites N).filter (fun x ↦ upperCut < profile x),
        lazyLowerDeviationAt N profile deviation x := by
  rintro s ⟨hsC, hsTheta⟩
  rw [thetaPlusEvent] at hsTheta
  simp only [Set.mem_iUnion] at hsTheta ⊢
  rcases hsTheta with ⟨x, hx, hsx⟩
  have hprofile := hC hsC x (hsite hx)
  refine ⟨x, Finset.mem_filter.mpr ⟨hx, hprofile ▸ hsx.1⟩, ?_⟩
  · rw [lazyLowerDeviationAt, Set.mem_ofPred_eq]
    apply hthreshold x hx (hprofile ▸ hsx.1)
      (paperLazyLocalTime s N x)
    rw [← hprofile, ← localTime_eq_paperExternal_add_paperLazy]
    exact hsx.2.2

/-- Chernoff turns the conditional negative-binomial law of one lazy
coordinate into the `exp(-17 r)` input of (4.22). -/
theorem cond_lazyUpperDeviation_le_exp_seventeen
    (μ : Measure (ℕ → Site)) (C : Set (ℕ → Site)) (N : ℕ)
    (profile : Site → ℕ) (deviation : Site → ℝ) (x : Site) (r : ℝ)
    (hi : 1 ≤ profile x) (hd0 : 0 ≤ deviation x)
    (hdi : deviation x ≤ profile x)
    (hexponent : 17 * r ≤
      deviation x ^ 2 / (4 * (profile x : ℝ)))
    (hLaw : HasLaw (fun s ↦ paperLazyLocalTime s N x)
      (negBinMeasure (profile x)) μ[|C]) :
    μ[|C] (lazyUpperDeviationAt N profile deviation x) ≤
      ENNReal.ofReal (Real.exp (-17 * r)) := by
  calc
    μ[|C] (lazyUpperDeviationAt N profile deviation x) ≤
        ENNReal.ofReal (Real.exp
          (-(deviation x ^ 2 / (4 * (profile x : ℝ))))) :=
      hasLaw_negBin_upperDeviation_le_exp _ hi _ hd0 hdi hLaw
    _ ≤ ENNReal.ofReal (Real.exp (-17 * r)) := by
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      linarith

/-- Lower-tail analogue for the upper external imbalance. -/
theorem cond_lazyLowerDeviation_le_exp_seventeen
    (μ : Measure (ℕ → Site)) (C : Set (ℕ → Site)) (N : ℕ)
    (profile : Site → ℕ) (deviation : Site → ℝ) (x : Site) (r : ℝ)
    (hi : 1 ≤ profile x) (hd0 : 0 ≤ deviation x)
    (hdi : deviation x ≤ profile x)
    (hexponent : 17 * r ≤
      deviation x ^ 2 / (4 * (profile x : ℝ)))
    (hLaw : HasLaw (fun s ↦ paperLazyLocalTime s N x)
      (negBinMeasure (profile x)) μ[|C]) :
    μ[|C] (lazyLowerDeviationAt N profile deviation x) ≤
      ENNReal.ofReal (Real.exp (-17 * r)) := by
  calc
    μ[|C] (lazyLowerDeviationAt N profile deviation x) ≤
        ENNReal.ofReal (Real.exp
          (-(deviation x ^ 2 / (4 * (profile x : ℝ))))) :=
      hasLaw_negBin_lowerDeviation_le_exp _ hi _ hd0 hdi hLaw
    _ ≤ ENNReal.ofReal (Real.exp (-17 * r)) := by
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      linarith

/-- Fixed-original-time lower-imbalance bridge.  A caller must separately
justify its conditional law; Proposition 4.3 does not directly supply the
`hLaw` below because the paper works at an inverse external clock/stopping
horizon. -/
theorem cond_inter_thetaMinus_le_exp
    (μ : Measure (ℕ → Site)) (C : Set (ℕ → Site))
    (sites : Finset Site) (N lowerCut a b : ℕ)
    (profile : Site → ℕ) (deviation : Site → ℝ) (r : ℝ)
    (hC : C ⊆ externalProfileEvent sites N profile)
    (hsite : evenHorizonSites N ⊆ sites)
    (hthreshold : ∀ x ∈ evenHorizonSites N, profile x ≤ lowerCut →
      (profile x : ℝ) / 15 + deviation x ≤ (a : ℝ) - profile x)
    (hcard : (((evenHorizonSites N).filter
      (fun x ↦ profile x ≤ lowerCut)).card : ℝ) ≤ Real.exp (16 * r))
    (hi : ∀ x ∈ (evenHorizonSites N).filter
      (fun x ↦ profile x ≤ lowerCut), 1 ≤ profile x)
    (hd0 : ∀ x ∈ (evenHorizonSites N).filter
      (fun x ↦ profile x ≤ lowerCut), 0 ≤ deviation x)
    (hdi : ∀ x ∈ (evenHorizonSites N).filter
      (fun x ↦ profile x ≤ lowerCut), deviation x ≤ profile x)
    (hexponent : ∀ x ∈ (evenHorizonSites N).filter
      (fun x ↦ profile x ≤ lowerCut),
        17 * r ≤ deviation x ^ 2 / (4 * (profile x : ℝ)))
    (hLaw : ∀ x ∈ (evenHorizonSites N).filter
      (fun x ↦ profile x ≤ lowerCut),
      HasLaw (fun s ↦ paperLazyLocalTime s N x)
        (negBinMeasure (profile x)) μ[|C]) :
    μ[|C] (C ∩ thetaMinusEvent N lowerCut a b) ≤
      ENNReal.ofReal (Real.exp (-r)) := by
  apply cond_finite_union_exp_sixteen_seventeen μ C _
    (lazyUpperDeviationAt N profile deviation)
    (C ∩ thetaMinusEvent N lowerCut a b) r
  · exact inter_thetaMinus_subset_lazyUpperDeviation C sites N lowerCut a b
      profile deviation hC hsite hthreshold
  · exact hcard
  · intro x hx
    exact cond_lazyUpperDeviation_le_exp_seventeen μ C N profile deviation x r
      (hi x hx) (hd0 x hx) (hdi x hx) (hexponent x hx) (hLaw x hx)

/-- Symmetric conditional lower-tail bridge for `Theta^+`. -/
theorem cond_inter_thetaPlus_le_exp
    (μ : Measure (ℕ → Site)) (C : Set (ℕ → Site))
    (sites : Finset Site) (N upperCut a b : ℕ)
    (profile : Site → ℕ) (deviation : Site → ℝ) (r : ℝ)
    (hC : C ⊆ externalProfileEvent sites N profile)
    (hsite : evenHorizonSites N ⊆ sites)
    (hthreshold : ∀ x ∈ evenHorizonSites N, upperCut < profile x →
      ∀ l : ℕ, profile x + l < b →
        (l : ℝ) ≤ (profile x : ℝ) / 15 - deviation x)
    (hcard : (((evenHorizonSites N).filter
      (fun x ↦ upperCut < profile x)).card : ℝ) ≤ Real.exp (16 * r))
    (hi : ∀ x ∈ (evenHorizonSites N).filter
      (fun x ↦ upperCut < profile x), 1 ≤ profile x)
    (hd0 : ∀ x ∈ (evenHorizonSites N).filter
      (fun x ↦ upperCut < profile x), 0 ≤ deviation x)
    (hdi : ∀ x ∈ (evenHorizonSites N).filter
      (fun x ↦ upperCut < profile x), deviation x ≤ profile x)
    (hexponent : ∀ x ∈ (evenHorizonSites N).filter
      (fun x ↦ upperCut < profile x),
        17 * r ≤ deviation x ^ 2 / (4 * (profile x : ℝ)))
    (hLaw : ∀ x ∈ (evenHorizonSites N).filter
      (fun x ↦ upperCut < profile x),
      HasLaw (fun s ↦ paperLazyLocalTime s N x)
        (negBinMeasure (profile x)) μ[|C]) :
    μ[|C] (C ∩ thetaPlusEvent N upperCut a b) ≤
      ENNReal.ofReal (Real.exp (-r)) := by
  apply cond_finite_union_exp_sixteen_seventeen μ C _
    (lazyLowerDeviationAt N profile deviation)
    (C ∩ thetaPlusEvent N upperCut a b) r
  · exact inter_thetaPlus_subset_lazyLowerDeviation C sites N upperCut a b
      profile deviation hC hsite hthreshold
  · exact hcard
  · intro x hx
    exact cond_lazyLowerDeviation_le_exp_seventeen μ C N profile deviation x r
      (hi x hx) (hd0 x hx) (hdi x hx) (hexponent x hx) (hLaw x hx)

/-! ## The two-scale split in HLOZ (4.22)--(4.24) -/

/-- Sites eligible for `Theta^-` after the external profile is fixed. -/
noncomputable def lowExternalCandidates (N lowerCut : ℕ)
    (profile : Site → ℕ) : Finset Site := by
  classical
  exact (evenHorizonSites N).filter (fun x ↦ profile x ≤ lowerCut)

/-- High-profile candidates, whose cardinality is controlled by Proposition 1.3. -/
noncomputable def nearLowExternalCandidates (N lowerCut profileCut : ℕ)
    (profile : Site → ℕ) : Finset Site := by
  classical
  exact (lowExternalCandidates N lowerCut profile).filter
    (fun x ↦ profileCut ≤ profile x)

/-- Low-profile candidates, charged to the full deterministic horizon. -/
noncomputable def farLowExternalCandidates (N lowerCut profileCut : ℕ)
    (profile : Site → ℕ) : Finset Site := by
  classical
  exact (lowExternalCandidates N lowerCut profile).filter
    (fun x ↦ profile x < profileCut)

lemma nearLowExternalCandidates_subset_low (N lowerCut profileCut : ℕ)
    (profile : Site → ℕ) :
    nearLowExternalCandidates N lowerCut profileCut profile ⊆
      lowExternalCandidates N lowerCut profile := by
  intro x hx
  exact (Finset.mem_filter.mp hx).1

lemma farLowExternalCandidates_subset_low (N lowerCut profileCut : ℕ)
    (profile : Site → ℕ) :
    farLowExternalCandidates N lowerCut profileCut profile ⊆
      lowExternalCandidates N lowerCut profile := by
  intro x hx
  exact (Finset.mem_filter.mp hx).1

lemma farLowExternalCandidates_subset_horizon (N lowerCut profileCut : ℕ)
    (profile : Site → ℕ) :
    farLowExternalCandidates N lowerCut profileCut profile ⊆
      evenHorizonSites N := by
  exact (farLowExternalCandidates_subset_low N lowerCut profileCut profile).trans
    (Finset.filter_subset _ _)

/-- Exact pathwise partition used before the two union estimates (4.22) and
(4.23). -/
theorem inter_thetaMinus_subset_near_union_far
    (C : Set (ℕ → Site)) (sites : Finset Site)
    (N lowerCut profileCut a b : ℕ)
    (profile : Site → ℕ) (deviation : Site → ℝ)
    (hC : C ⊆ externalProfileEvent sites N profile)
    (hsite : evenHorizonSites N ⊆ sites)
    (hthreshold : ∀ x ∈ evenHorizonSites N, profile x ≤ lowerCut →
      (profile x : ℝ) / 15 + deviation x ≤ (a : ℝ) - profile x) :
    C ∩ thetaMinusEvent N lowerCut a b ⊆
      (⋃ x ∈ nearLowExternalCandidates N lowerCut profileCut profile,
        lazyUpperDeviationAt N profile deviation x) ∪
      (⋃ x ∈ farLowExternalCandidates N lowerCut profileCut profile,
        lazyUpperDeviationAt N profile deviation x) := by
  intro s hs
  have hbase := inter_thetaMinus_subset_lazyUpperDeviation C sites N lowerCut a b
    profile deviation hC hsite hthreshold hs
  change s ∈ ⋃ x ∈ lowExternalCandidates N lowerCut profile,
    lazyUpperDeviationAt N profile deviation x at hbase
  simp only [Set.mem_iUnion, Set.mem_union] at hbase ⊢
  rcases hbase with ⟨x, hxlow, hsx⟩
  by_cases hxnear : profileCut ≤ profile x
  · left
    exact ⟨x, Finset.mem_filter.mpr ⟨hxlow, hxnear⟩, hsx⟩
  · right
    exact ⟨x, Finset.mem_filter.mpr ⟨hxlow, by omega⟩, hsx⟩

/-- The two-scale calculation underlying (4.22)--(4.24), still at a fixed
original time.  Both Chernoff estimates and both union bounds are derived;
the `hLaw` premise is deliberately not labeled as Proposition 4.3. -/
theorem cond_inter_thetaMinus_le_two_scale
    (m : ℕ) (r : ℝ)
    (μ : Measure (ℕ → Site)) (C : Set (ℕ → Site))
    (sites : Finset Site) (N lowerCut profileCut a b : ℕ)
    (profile : Site → ℕ) (deviation : Site → ℝ)
    (hC : C ⊆ externalProfileEvent sites N profile)
    (hsite : evenHorizonSites N ⊆ sites)
    (hthreshold : ∀ x ∈ evenHorizonSites N, profile x ≤ lowerCut →
      (profile x : ℝ) / 15 + deviation x ≤ (a : ℝ) - profile x)
    (hnearCard : ((nearLowExternalCandidates N lowerCut profileCut profile).card : ℝ) ≤
      Real.exp (16 * r))
    (hhorizon : ((evenHorizonSites N).card : ℝ) ≤
      Real.exp (16 * Real.sqrt (m : ℝ)))
    (hi : ∀ x ∈ lowExternalCandidates N lowerCut profile, 1 ≤ profile x)
    (hd0 : ∀ x ∈ lowExternalCandidates N lowerCut profile, 0 ≤ deviation x)
    (hdi : ∀ x ∈ lowExternalCandidates N lowerCut profile,
      deviation x ≤ profile x)
    (hnearExponent : ∀ x ∈ nearLowExternalCandidates N lowerCut profileCut profile,
      17 * r ≤ deviation x ^ 2 / (4 * (profile x : ℝ)))
    (hfarExponent : ∀ x ∈ farLowExternalCandidates N lowerCut profileCut profile,
      17 * Real.sqrt (m : ℝ) ≤
        deviation x ^ 2 / (4 * (profile x : ℝ)))
    (hLaw : ∀ x ∈ lowExternalCandidates N lowerCut profile,
      HasLaw (fun s ↦ paperLazyLocalTime s N x)
        (negBinMeasure (profile x)) μ[|C]) :
    μ[|C] (C ∩ thetaMinusEvent N lowerCut a b) ≤
      ENNReal.ofReal (Real.exp (-r)) +
        ENNReal.ofReal (Real.exp (-Real.sqrt (m : ℝ))) := by
  let near := nearLowExternalCandidates N lowerCut profileCut profile
  let far := farLowExternalCandidates N lowerCut profileCut profile
  let E := lazyUpperDeviationAt N profile deviation
  have hnear : μ[|C] (⋃ x ∈ near, E x) ≤
      ENNReal.ofReal (Real.exp (-r)) := by
    apply finite_union_exp_sixteen_seventeen μ[|C] near E _ r
      Set.Subset.rfl (by simpa [near] using hnearCard)
    intro x hx
    have hx' : x ∈ nearLowExternalCandidates N lowerCut profileCut profile := by
      simpa [near] using hx
    have hxlow : x ∈ lowExternalCandidates N lowerCut profile :=
      nearLowExternalCandidates_subset_low N lowerCut profileCut profile hx'
    exact cond_lazyUpperDeviation_le_exp_seventeen μ C N profile deviation x r
      (hi x hxlow) (hd0 x hxlow) (hdi x hxlow)
      (hnearExponent x hx') (hLaw x hxlow)
  have hfarCard : (far.card : ℝ) ≤
      Real.exp (16 * Real.sqrt (m : ℝ)) := by
    calc
      (far.card : ℝ) ≤ ((evenHorizonSites N).card : ℝ) := by
        exact_mod_cast Finset.card_le_card
          (farLowExternalCandidates_subset_horizon N lowerCut profileCut profile)
      _ ≤ Real.exp (16 * Real.sqrt (m : ℝ)) := hhorizon
  have hfar : μ[|C] (⋃ x ∈ far, E x) ≤
      ENNReal.ofReal (Real.exp (-Real.sqrt (m : ℝ))) := by
    apply finite_union_exp_sixteen_seventeen μ[|C] far E _
      (Real.sqrt (m : ℝ)) Set.Subset.rfl hfarCard
    intro x hx
    have hx' : x ∈ farLowExternalCandidates N lowerCut profileCut profile := by
      simpa [far] using hx
    have hxlow : x ∈ lowExternalCandidates N lowerCut profile :=
      farLowExternalCandidates_subset_low N lowerCut profileCut profile hx'
    exact cond_lazyUpperDeviation_le_exp_seventeen μ C N profile deviation x
      (Real.sqrt (m : ℝ)) (hi x hxlow) (hd0 x hxlow) (hdi x hxlow)
      (hfarExponent x hx') (hLaw x hxlow)
  calc
    μ[|C] (C ∩ thetaMinusEvent N lowerCut a b) ≤
        μ[|C] ((⋃ x ∈ near, E x) ∪ (⋃ x ∈ far, E x)) := by
      apply measure_mono
      simpa [near, far, E] using
        (inter_thetaMinus_subset_near_union_far C sites N lowerCut profileCut
          a b profile deviation hC hsite hthreshold)
    _ ≤ μ[|C] (⋃ x ∈ near, E x) + μ[|C] (⋃ x ∈ far, E x) :=
      measure_union_le _ _
    _ ≤ ENNReal.ofReal (Real.exp (-r)) +
        ENNReal.ofReal (Real.exp (-Real.sqrt (m : ℝ))) :=
      add_le_add hnear hfar

end Erdos1166.HLOZProp45Theta
