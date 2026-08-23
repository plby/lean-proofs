import ErdosProblems.Erdos1166.Erdos1166HLOZDecomposition
import ErdosProblems.Erdos1166.Erdos1166HLOZPairRuns
import ErdosProblems.Erdos1166.Erdos1166HLOZPairing
import ErdosProblems.Erdos1166.Erdos1166HLOZConditionalProduct
import ErdosProblems.Erdos1166.Erdos1166HLOZExternalPairPath

namespace Erdos1166.HLOZReconstruction

open HLOZDecomposition
open HLOZPairing
open scoped BigOperators ENNReal

abbrev PairRun := ℕ × IncrementPair

def terminalLabels (runs : List PairRun) : List IncrementPair :=
  runs.map Prod.snd

/-- Expand every `(run length, terminal label)` into the corresponding list
of distinguished lazy pairs followed by its non-lazy terminal pair. -/
def expandPairRuns : List PairRun → List IncrementPair
  | [] => []
  | (t, p) :: runs =>
      List.replicate t distinguishedIncrementPair ++ p :: expandPairRuns runs

/-- Streaming inverse of `expandPairRuns`; the accumulator records the
number of distinguished pairs since the preceding terminal label. -/
def decodePairRunsAux : ℕ → List IncrementPair → List PairRun
  | _, [] => []
  | t, p :: pairs =>
      if p = distinguishedIncrementPair then
        decodePairRunsAux (t + 1) pairs
      else
        (t, p) :: decodePairRunsAux 0 pairs

def decodePairRuns (pairs : List IncrementPair) : List PairRun :=
  decodePairRunsAux 0 pairs

theorem decodePairRunsAux_replicate_cons
    (n t : ℕ) (p : IncrementPair) (pairs : List IncrementPair)
    (hp : p ≠ distinguishedIncrementPair) :
    decodePairRunsAux n
        (List.replicate t distinguishedIncrementPair ++ p :: pairs) =
      (n + t, p) :: decodePairRunsAux 0 pairs := by
  induction t generalizing n with
  | zero => simp [decodePairRunsAux, hp]
  | succ t ih =>
      simp only [List.replicate_succ, List.cons_append, decodePairRunsAux]
      rw [if_pos trivial]
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (n := n + 1)

theorem decodePairRuns_expandPairRuns (runs : List PairRun)
    (hnondist : ∀ run ∈ runs, run.2 ≠ distinguishedIncrementPair) :
    decodePairRuns (expandPairRuns runs) = runs := by
  induction runs with
  | nil => rfl
  | cons run runs ih =>
      rcases run with ⟨t, p⟩
      have hp : p ≠ distinguishedIncrementPair := hnondist (t, p) (by simp)
      have hrs : ∀ run ∈ runs, run.2 ≠ distinguishedIncrementPair := by
        intro run hrun
        exact hnondist run (by simp [hrun])
      simp only [expandPairRuns, decodePairRuns]
      rw [decodePairRunsAux_replicate_cons 0 t p (expandPairRuns runs) hp]
      simp only [Nat.zero_add]
      change (t, p) :: decodePairRuns (expandPairRuns runs) = (t, p) :: runs
      rw [ih hrs]

theorem expandPairRuns_injective
    {runs₁ runs₂ : List PairRun}
    (h₁ : ∀ run ∈ runs₁, run.2 ≠ distinguishedIncrementPair)
    (h₂ : ∀ run ∈ runs₂, run.2 ≠ distinguishedIncrementPair)
    (hexpand : expandPairRuns runs₁ = expandPairRuns runs₂) :
    runs₁ = runs₂ := by
  have hdecode := congrArg decodePairRuns hexpand
  simpa [decodePairRuns_expandPairRuns runs₁ h₁,
    decodePairRuns_expandPairRuns runs₂ h₂] using hdecode

/-- The two ordinary direction labels represented by an increment pair. -/
def pairDirections (p : IncrementPair) : List Direction := [p 0, p 1]

def flattenPairs (pairs : List IncrementPair) : List Direction :=
  pairs.flatMap pairDirections

theorem incrementPair_ext {p q : IncrementPair}
    (h0 : p 0 = q 0) (h1 : p 1 = q 1) : p = q := by
  funext i
  fin_cases i
  · exact h0
  · exact h1

theorem flattenPairs_injective : Function.Injective flattenPairs := by
  intro pairs₁
  induction pairs₁ with
  | nil =>
      intro pairs₂ h
      cases pairs₂ with
      | nil => rfl
      | cons q qs => simp [flattenPairs, pairDirections] at h
  | cons p ps ih =>
      intro pairs₂ h
      cases pairs₂ with
      | nil => simp [flattenPairs, pairDirections] at h
      | cons q qs =>
          simp only [flattenPairs, List.flatMap_cons, pairDirections,
            List.cons_append] at h
          injection h with h0 hrest
          injection hrest with h1 htail
          have hpq : p = q := incrementPair_ext h0 h1
          subst q
          exact congrArg (List.cons p) (ih htail)

theorem directionStep_injective : Function.Injective directionStep := by
  intro d e h
  fin_cases d <;> fin_cases e <;> simp [directionStep] at h ⊢

/-- Sites visited after leaving `a` and following `directions`.  The initial
site itself is omitted, which makes concatenation recursive without duplicate
endpoints. -/
def reconstructTail : Site → List Direction → List Site
  | _, [] => []
  | a, d :: directions =>
      let b := a + directionStep d
      b :: reconstructTail b directions

def reconstructFromDirections (a : Site) (directions : List Direction) : List Site :=
  a :: reconstructTail a directions

theorem reconstructTail_injective (a : Site) :
    Function.Injective (reconstructTail a) := by
  intro directions₁
  induction directions₁ generalizing a with
  | nil =>
      intro directions₂ h
      cases directions₂ with
      | nil => rfl
      | cons d ds => simp [reconstructTail] at h
  | cons d ds ih =>
      intro directions₂ h
      cases directions₂ with
      | nil => simp [reconstructTail] at h
      | cons e es =>
          simp only [reconstructTail] at h
          injection h with hhead htail
          have hstep : directionStep d = directionStep e := by
            exact add_left_cancel hhead
          have hde : d = e := directionStep_injective hstep
          subst e
          exact congrArg (List.cons d) (ih (a := a + directionStep d) htail)

def reconstructedPrefix (a : Site) (runs : List PairRun) : List Site :=
  reconstructFromDirections a (flattenPairs (expandPairRuns runs))

/-- For fixed initial site, a valid run/terminal-label vector is uniquely
recoverable from the reconstructed original prefix. -/
theorem reconstructedPrefix_injective
    (a : Site) {runs₁ runs₂ : List PairRun}
    (h₁ : ∀ run ∈ runs₁, run.2 ≠ distinguishedIncrementPair)
    (h₂ : ∀ run ∈ runs₂, run.2 ≠ distinguishedIncrementPair)
    (hreconstruct : reconstructedPrefix a runs₁ = reconstructedPrefix a runs₂) :
    runs₁ = runs₂ := by
  have htail : reconstructTail a (flattenPairs (expandPairRuns runs₁)) =
      reconstructTail a (flattenPairs (expandPairRuns runs₂)) := by
    exact List.cons.inj hreconstruct |>.2
  have hdirections := reconstructTail_injective a htail
  have hpairs := flattenPairs_injective hdirections
  exact expandPairRuns_injective h₁ h₂ hpairs

/-- The labeled-pair cylinder producing a given reconstructed prefix. -/
def reconstructedPrefixCylinder (runs : List PairRun) : Set (ℕ → Direction) :=
  firstPairRunsWithLabelsEqFrom 0 runs

/-- Before the stopping constraints are imposed, the conditional atom of a
reconstructed run vector given its terminal-label path is exactly the iid
geometric product furnished by `HLOZPairRuns`. -/
theorem reconstructedPrefixCylinder_conditional_mass
    (runs : List PairRun)
    (hnondist : ∀ run ∈ runs, run.2 ≠ distinguishedIncrementPair) :
    incrementLaw (reconstructedPrefixCylinder runs) /
        incrementLaw
          (firstPairTerminalLabelsEqFrom 0 (terminalLabels runs)) =
      (runs.map fun run ↦
        (15 : ℝ≥0∞) / 16 ^ (run.1 + 1)).prod := by
  unfold reconstructedPrefixCylinder terminalLabels
  exact firstPairRunLengths_conditional_on_terminalLabels 0 runs hnondist

/-- Source-facing version of the same atom: conditioning on the finite
external path reconstructed from the terminal pair labels gives the same iid
geometric run law. -/
theorem reconstructedPrefixCylinder_conditional_on_externalPath
    (runs : List PairRun)
    (hnondist : ∀ run ∈ runs,
      run.2 ≠ distinguishedIncrementPair) :
    incrementLaw (reconstructedPrefixCylinder runs) /
        incrementLaw (firstPairExternalPathEqFrom 0
          (Erdos1166.externalPathFromLabels (terminalLabels runs))) =
      (runs.map fun run ↦
        (15 : ℝ≥0∞) / 16 ^ (run.1 + 1)).prod := by
  unfold reconstructedPrefixCylinder terminalLabels
  exact firstPairRunLengths_conditional_on_externalPath 0 runs hnondist

/-! ### Recursive reconstruction and the local-time profile -/

def pairEndpoint (a : Site) (p : IncrementPair) : Site :=
  a + directionStep (p 0) + directionStep (p 1)

/-- Site list contributed by a list of complete increment pairs, omitting the
initial site. -/
def reconstructPairTail : Site → List IncrementPair → List Site
  | _, [] => []
  | a, p :: pairs =>
      let b := a + directionStep (p 0)
      let c := pairEndpoint a p
      b :: c :: reconstructPairTail c pairs

theorem reconstructTail_flattenPairs (a : Site) (pairs : List IncrementPair) :
    reconstructTail a (flattenPairs pairs) = reconstructPairTail a pairs := by
  induction pairs generalizing a with
  | nil => rfl
  | cons p pairs ih =>
      simp only [flattenPairs, List.flatMap_cons, pairDirections,
        List.cons_append, List.nil_append, reconstructTail, reconstructPairTail]
      change (a + directionStep (p 0)) :: pairEndpoint a p ::
          reconstructTail (pairEndpoint a p) (flattenPairs pairs) =
        (a + directionStep (p 0)) :: pairEndpoint a p ::
          reconstructPairTail (pairEndpoint a p) pairs
      rw [ih]

@[simp] theorem pairEndpoint_distinguished (a : Site) :
    pairEndpoint a distinguishedIncrementPair = a := by
  ext <;> simp [pairEndpoint, directionStep, distinguishedIncrementPair]

/-- Prefix `t` copies of `(a,a+e₁,a)` to an already constructed tail.  Since
the initial `a` is outside this tail, each loop contributes exactly the two
new visits `a+e₁,a`. -/
def prependLazyLoops (a : Site) : ℕ → List Site → List Site
  | 0, tail => tail
  | t + 1, tail =>
      (a + paperE1) :: a :: prependLazyLoops a t tail

theorem paperE1_ne_zero : paperE1 ≠ (0 : Site) := by
  norm_num [paperE1]

theorem add_paperE1_ne_self (a : Site) : a + paperE1 ≠ a := by
  intro h
  have h' : a + paperE1 = a + 0 := by simpa using h
  exact paperE1_ne_zero (add_left_cancel h')

theorem reconstructPairTail_replicate_distinguished
    (a : Site) (t : ℕ) (pairs : List IncrementPair) :
    reconstructPairTail a
        (List.replicate t distinguishedIncrementPair ++ pairs) =
      prependLazyLoops a t (reconstructPairTail a pairs) := by
  induction t with
  | zero => rfl
  | succ t ih =>
      simp only [List.replicate_succ, List.cons_append, reconstructPairTail,
        prependLazyLoops]
      rw [pairEndpoint_distinguished, ih]
      congr 2

/-- Recursive reconstruction directly from HLOZ block coordinates. -/
def reconstructRunTail : Site → List PairRun → List Site
  | _, [] => []
  | a, (t, p) :: runs =>
      let b := a + directionStep (p 0)
      let c := pairEndpoint a p
      prependLazyLoops a t (b :: c :: reconstructRunTail c runs)

/-- The external prefix obtained by retaining just the terminal pair labels. -/
def reconstructExternalTail : Site → List IncrementPair → List Site
  | _, [] => []
  | a, p :: labels =>
      let b := a + directionStep (p 0)
      let c := pairEndpoint a p
      b :: c :: reconstructExternalTail c labels

theorem reconstructPairTail_expandPairRuns (a : Site) (runs : List PairRun) :
    reconstructPairTail a (expandPairRuns runs) = reconstructRunTail a runs := by
  induction runs generalizing a with
  | nil => rfl
  | cons run runs ih =>
      rcases run with ⟨t, p⟩
      simp only [expandPairRuns, reconstructRunTail]
      rw [reconstructPairTail_replicate_distinguished]
      simp only [reconstructPairTail]
      rw [ih]

theorem reconstructedPrefix_eq_runReconstruction (a : Site) (runs : List PairRun) :
    reconstructedPrefix a runs = a :: reconstructRunTail a runs := by
  unfold reconstructedPrefix reconstructFromDirections
  rw [reconstructTail_flattenPairs, reconstructPairTail_expandPairRuns]

theorem reconstructExternalTail_terminalLabels
    (a : Site) (runs : List PairRun) :
    reconstructExternalTail a (terminalLabels runs) =
      reconstructPairTail a (terminalLabels runs) := by
  induction runs generalizing a with
  | nil => rfl
  | cons run runs ih =>
      rcases run with ⟨t, p⟩
      simp only [terminalLabels, List.map_cons, reconstructExternalTail,
        reconstructPairTail]
      rw [show List.map Prod.snd runs = terminalLabels runs by rfl]
      rw [ih]

/-- Total lazy contribution at an individual site. -/
def lazyVisitCount : Site → List PairRun → Site → ℕ
  | _, [], _ => 0
  | a, (t, p) :: runs, x =>
      (if x = a + paperE1 then t else 0) +
        (if x = a then t else 0) +
          lazyVisitCount (pairEndpoint a p) runs x

theorem count_prependLazyLoops (x a : Site) (t : ℕ) (tail : List Site) :
    List.count x (prependLazyLoops a t tail) =
      (if x = a + paperE1 then t else 0) +
        (if x = a then t else 0) + List.count x tail := by
  induction t with
  | zero => simp [prependLazyLoops]
  | succ t ih =>
      rw [prependLazyLoops, List.count_cons, List.count_cons, ih]
      simp only [beq_iff_eq]
      by_cases hxp : x = a + paperE1
      · by_cases hxa : x = a
        · exact (add_paperE1_ne_self a (hxp.symm.trans hxa)).elim
        · have hpx : a + paperE1 = x := hxp.symm
          have hax : ¬a = x := fun h ↦ hxa h.symm
          repeat rw [if_pos hxp]
          repeat rw [if_pos hpx]
          repeat rw [if_neg hxa]
          repeat rw [if_neg hax]
          omega
      · by_cases hxa : x = a
        · have hpx : ¬a + paperE1 = x := fun h ↦ hxp h.symm
          have hax : a = x := hxa.symm
          repeat rw [if_neg hxp]
          repeat rw [if_neg hpx]
          repeat rw [if_pos hxa]
          repeat rw [if_pos hax]
          omega
        · have hpx : ¬a + paperE1 = x := fun h ↦ hxp h.symm
          have hax : ¬a = x := fun h ↦ hxa h.symm
          repeat rw [if_neg hxp]
          repeat rw [if_neg hpx]
          repeat rw [if_neg hxa]
          repeat rw [if_neg hax]
          omega

/-- Exact pathwise local-time decomposition for the reconstructed prefix:
the full visit count is the external-prefix count plus the visits inserted by
the lazy run coordinates. -/
theorem count_reconstructRunTail (a : Site) (runs : List PairRun) (x : Site) :
    List.count x (reconstructRunTail a runs) =
      List.count x (reconstructExternalTail a (terminalLabels runs)) +
        lazyVisitCount a runs x := by
  induction runs generalizing a with
  | nil => rfl
  | cons run runs ih =>
      rcases run with ⟨t, p⟩
      simp only [reconstructRunTail, terminalLabels, List.map_cons,
        reconstructExternalTail, lazyVisitCount]
      rw [count_prependLazyLoops]
      simp only [List.count_cons]
      rw [show List.map Prod.snd runs = terminalLabels runs by rfl]
      rw [ih]
      omega

theorem count_reconstructedPrefix (a : Site) (runs : List PairRun) (x : Site) :
    List.count x (reconstructedPrefix a runs) =
      List.count x (a :: reconstructExternalTail a (terminalLabels runs)) +
        lazyVisitCount a runs x := by
  rw [reconstructedPrefix_eq_runReconstruction]
  simp only [List.count_cons, count_reconstructRunTail]
  omega

/-! ### HLOZ block sums and constraints (4.7)--(4.8) -/

/-- The run coordinates `ρ(x,l)` attached to successive external visits of
the even base site `x`. -/
def runLengthsAtBase : Site → List PairRun → Site → List ℕ
  | _, [], _ => []
  | a, (t, p) :: runs, x =>
      let tail := runLengthsAtBase (pairEndpoint a p) runs x
      if a = x then t :: tail else tail

/-- The sum `∑_l ρ(x,l)` occurring in (4.7) and (4.8). -/
def lazyBlockSum : Site → List PairRun → Site → ℕ
  | _, [], _ => 0
  | a, (t, p) :: runs, x =>
      (if a = x then t else 0) + lazyBlockSum (pairEndpoint a p) runs x

theorem sum_runLengthsAtBase (a : Site) (runs : List PairRun) (x : Site) :
    (runLengthsAtBase a runs x).sum = lazyBlockSum a runs x := by
  induction runs generalizing a with
  | nil => rfl
  | cons run runs ih =>
      rcases run with ⟨t, p⟩
      simp only [runLengthsAtBase, lazyBlockSum]
      by_cases hax : a = x
      · repeat rw [if_pos hax]
        rw [List.sum_cons, ih]
      · repeat rw [if_neg hax]
        rw [ih]
        simp

/-- External even-pair bases, one for each run coordinate. -/
def externalPairBases : Site → List PairRun → List Site
  | _, [] => []
  | a, (_, p) :: runs => a :: externalPairBases (pairEndpoint a p) runs

theorem length_runLengthsAtBase (a : Site) (runs : List PairRun) (x : Site) :
    (runLengthsAtBase a runs x).length =
      List.count x (externalPairBases a runs) := by
  induction runs generalizing a with
  | nil => rfl
  | cons run runs ih =>
      rcases run with ⟨t, p⟩
      simp only [runLengthsAtBase, externalPairBases, List.count_cons]
      simp only [beq_iff_eq]
      by_cases hax : a = x
      · repeat rw [if_pos hax]
        simp only [List.length_cons]
        rw [ih]
      · repeat rw [if_neg hax]
        rw [ih]
        simp

theorem chessEven_add_directionStep_iff (a : Site) (d : Direction) :
    chessEven (a + directionStep d) ↔ ¬chessEven a := by
  fin_cases d
  · change chessEven (a.1 + 1, a.2 + 0) ↔ ¬chessEven a
    simpa [directionStep, shift, vec, east] using
      shift_vec_chessEven_iff east a
  · change chessEven (a.1 + -1, a.2 + 0) ↔ ¬chessEven a
    simpa [directionStep, shift, vec, west] using
      shift_vec_chessEven_iff west a
  · change chessEven (a.1 + 0, a.2 + 1) ↔ ¬chessEven a
    simpa [directionStep, shift, vec, north] using
      shift_vec_chessEven_iff north a
  · change chessEven (a.1 + 0, a.2 + -1) ↔ ¬chessEven a
    simpa [directionStep, shift, vec, south] using
      shift_vec_chessEven_iff south a

theorem chessEven_pairEndpoint_iff (a : Site) (p : IncrementPair) :
    chessEven (pairEndpoint a p) ↔ chessEven a := by
  unfold pairEndpoint
  rw [chessEven_add_directionStep_iff, chessEven_add_directionStep_iff]
  tauto

theorem not_chessEven_add_paperE1 {a : Site} (ha : chessEven a) :
    ¬chessEven (a + paperE1) := by
  have hiff := chessEven_add_directionStep_iff a (0 : Direction)
  have heq : a + paperE1 = a + directionStep (0 : Direction) := by
    rfl
  rw [heq, hiff]
  exact not_not_intro ha

theorem add_paperE1_injective :
    Function.Injective (fun x : Site ↦ x + paperE1) := by
  intro x y h
  exact add_right_cancel h

/-- At an even base site, the individual-site lazy local time is exactly the
sum of the run coordinates assigned to that external base. -/
theorem lazyVisitCount_eq_lazyBlockSum_base
    (a : Site) (runs : List PairRun) (x : Site)
    (ha : chessEven a) (hx : chessEven x) :
    lazyVisitCount a runs x = lazyBlockSum a runs x := by
  induction runs generalizing a with
  | nil => rfl
  | cons run runs ih =>
      rcases run with ⟨t, p⟩
      have hc : chessEven (pairEndpoint a p) :=
        (chessEven_pairEndpoint_iff a p).2 ha
      have hxp : x ≠ a + paperE1 := by
        intro h
        exact not_chessEven_add_paperE1 ha (h ▸ hx)
      simp only [lazyVisitCount, lazyBlockSum]
      rw [if_neg hxp]
      by_cases hax : a = x
      · have hxa : x = a := hax.symm
        rw [if_pos hax, if_pos hxa, ih (a := pairEndpoint a p) hc]
        omega
      · have hxa : x ≠ a := fun h ↦ hax h.symm
        rw [if_neg hax, if_neg hxa, ih (a := pairEndpoint a p) hc]

/-- The partner site gets the same lazy contribution, because every inserted
excursion visits both members of the domino once. -/
theorem lazyVisitCount_eq_lazyBlockSum_partner
    (a : Site) (runs : List PairRun) (x : Site)
    (ha : chessEven a) (hx : chessEven x) :
    lazyVisitCount a runs (x + paperE1) = lazyBlockSum a runs x := by
  induction runs generalizing a with
  | nil => rfl
  | cons run runs ih =>
      rcases run with ⟨t, p⟩
      have hc : chessEven (pairEndpoint a p) :=
        (chessEven_pairEndpoint_iff a p).2 ha
      have hpartnerNotBase : x + paperE1 ≠ a := by
        intro h
        exact not_chessEven_add_paperE1 hx (h ▸ ha)
      simp only [lazyVisitCount, lazyBlockSum]
      rw [if_neg hpartnerNotBase]
      by_cases hax : a = x
      · have hpartners : x + paperE1 = a + paperE1 := congrArg (· + paperE1) hax.symm
        rw [if_pos hax, if_pos hpartners, ih (a := pairEndpoint a p) hc]
        omega
      · have hpartners : x + paperE1 ≠ a + paperE1 := fun h ↦
          hax (add_paperE1_injective h).symm
        rw [if_neg hax, if_neg hpartners, ih (a := pairEndpoint a p) hc]

def reconstructedLocalTime (a : Site) (runs : List PairRun) (x : Site) : ℕ :=
  List.count x (reconstructedPrefix a runs)

def reconstructedExternalLocalTime
    (a : Site) (runs : List PairRun) (x : Site) : ℕ :=
  List.count x (a :: reconstructExternalTail a (terminalLabels runs))

def reconstructedPairMax (a : Site) (runs : List PairRun) (x : Site) : ℕ :=
  max (reconstructedLocalTime a runs x)
    (reconstructedLocalTime a runs (x + paperE1))

def reconstructedExternalPairMax
    (a : Site) (runs : List PairRun) (x : Site) : ℕ :=
  max (reconstructedExternalLocalTime a runs x)
    (reconstructedExternalLocalTime a runs (x + paperE1))

/-- The common deterministic identity underneath both (4.7) and (4.8). -/
theorem reconstructedPairMax_eq_external_add_block
    (a : Site) (runs : List PairRun) (x : Site)
    (ha : chessEven a) (hx : chessEven x) :
    reconstructedPairMax a runs x =
      lazyBlockSum a runs x + reconstructedExternalPairMax a runs x := by
  have hbase := count_reconstructedPrefix a runs x
  have hpartner := count_reconstructedPrefix a runs (x + paperE1)
  rw [lazyVisitCount_eq_lazyBlockSum_base a runs x ha hx] at hbase
  rw [lazyVisitCount_eq_lazyBlockSum_partner a runs x ha hx] at hpartner
  unfold reconstructedPairMax reconstructedLocalTime
  rw [hbase, hpartner]
  unfold reconstructedExternalPairMax reconstructedExternalLocalTime
  rw [add_comm (List.count x _) (lazyBlockSum a runs x),
    add_comm (List.count (x + paperE1) _) (lazyBlockSum a runs x)]
  exact Nat.add_max_add_left _ _ _

/-- Equation (4.7), expressed as an exact equivalence between its block-sum
form and the reconstructed domino maximum.  `δ` is the terminal-site
indicator appearing on the right-hand side of (4.7). -/
theorem equation47_iff_reconstructedPairMax
    (a : Site) (runs : List PairRun) (x : Site) (m δ : ℕ)
    (ha : chessEven a) (hx : chessEven x) :
    lazyBlockSum a runs x + reconstructedExternalPairMax a runs x = m - δ ↔
      reconstructedPairMax a runs x = m - δ := by
  rw [reconstructedPairMax_eq_external_add_block a runs x ha hx]

/-- Inequality (4.8), in the same deterministic reconstructed form. -/
theorem inequality48_iff_reconstructedPairMax_lt
    (a : Site) (runs : List PairRun) (x : Site) (m : ℕ)
    (ha : chessEven a) (hx : chessEven x) :
    lazyBlockSum a runs x + reconstructedExternalPairMax a runs x < m ↔
      reconstructedPairMax a runs x < m := by
  rw [reconstructedPairMax_eq_external_add_block a runs x ha hx]

/-! ### Genuine finite conditional product at an external stopping horizon -/

noncomputable def paperExternalPairMaxAt
    (s : ℕ → Site) (T : ℕ) (x : Site) : ℕ :=
  max (paperExternalLocalTime s T x)
    (paperExternalLocalTime s T (x + paperE1))

/-- The threshold in HLOZ (4.8), read directly from the external local-time
profile at the finite original-time horizon `T`. -/
noncomputable def paperBlockThreshold
    (s : ℕ → Site) (T m : ℕ) (x : Site) : ℕ :=
  m - paperExternalPairMaxAt s T x

section FiniteConditionalLaw

variable {β : Type*} [Fintype β]
variable {ι : β → Type*} [∀ b, Fintype (ι b)] [∀ b, DecidableEq (ι b)]

/-- One bounded-sum constraint for every selected domino.  This is the finite
product event in Proposition 4.3 after the external path (hence its clock and
external local-time profile) has been fixed. -/
noncomputable def paperBlockConstraints
    (s : ℕ → Site) (T m : ℕ) (site : β → Site) :
    ∀ b, Finset (ι b → ℕ) :=
  fun b ↦ HLOZConditionalProduct.natSumBelow
    (paperBlockThreshold s T m (site b))

omit [Fintype β] in
theorem mem_paperBlockConstraints_iff
    (s : ℕ → Site) (T m : ℕ) (site : β → Site)
    (ρ : ∀ b, ι b → ℕ) (b : β) :
    ρ b ∈ paperBlockConstraints (ι := ι) s T m site b ↔
      (∑ i, ρ b i) + paperExternalPairMaxAt s T (site b) < m := by
  rw [paperBlockConstraints,
    HLOZConditionalProduct.mem_natSumBelow_iff]
  unfold paperBlockThreshold
  omega

omit [Fintype β] in
theorem mem_blockEvent_paperBlockConstraints_iff
    (s : ℕ → Site) (T m : ℕ) (site : β → Site)
    (ρ : ∀ b, ι b → ℕ) :
    ρ ∈ HLOZConditionalProduct.blockEvent
        (paperBlockConstraints (ι := ι) s T m site) ↔
      ∀ b, (∑ i, ρ b i) + paperExternalPairMaxAt s T (site b) < m := by
  constructor
  · intro h b
    exact (mem_paperBlockConstraints_iff s T m site ρ b).mp (h b)
  · intro h b
    exact (mem_paperBlockConstraints_iff s T m site ρ b).mpr (h b)

/-- Specialization of the finite filter theorem to the exact external-profile
constraints of Proposition 4.3.  This is a conditional law, not merely a
reconstruction statement: the PMF filtered by all site constraints factors
as the product of the separately filtered block PMFs. -/
theorem filter_paperBlockConstraints_apply_eq_prod
    (s : ℕ → Site) (T m : ℕ) (site : β → Site)
    (μ : PMF (∀ b, ι b → ℕ)) (μb : ∀ b, PMF (ι b → ℕ))
    (hprod : ∀ ρ, μ ρ = ∏ b, μb b (ρ b))
    (hE : ∀ b, ∃ y ∈
      (paperBlockConstraints (ι := ι) s T m site b : Set (ι b → ℕ)),
        y ∈ (μb b).support)
    (ρ : ∀ b, ι b → ℕ) :
    (μ.filter
      (HLOZConditionalProduct.blockEvent
        (paperBlockConstraints (ι := ι) s T m site))
      (HLOZConditionalProduct.blockEvent_meets_support μ μb hprod
        (paperBlockConstraints (ι := ι) s T m site) hE)) ρ =
      ∏ b, ((μb b).filter
        (paperBlockConstraints (ι := ι) s T m site b : Set (ι b → ℕ))
        (hE b)) (ρ b) := by
  exact HLOZConditionalProduct.filter_blockEvent_apply_eq_prod
    μ μb hprod (paperBlockConstraints (ι := ι) s T m site) hE ρ

/-- The explicit geometric-product version: every block has iid
geometric `(15/16)` coordinates before filtering, and after imposing (4.8)
the joint atom is the product of the separately normalized truncated block
atoms. -/
theorem filter_paperBlockConstraints_apply_eq_geometric_product
    (s : ℕ → Site) (T m : ℕ) (site : β → Site)
    (μ : PMF (∀ b, ι b → ℕ)) (μb : ∀ b, PMF (ι b → ℕ))
    (hprod : ∀ ρ, μ ρ = ∏ b, μb b (ρ b))
    (hgeom : ∀ b x, μb b x =
      ∏ i, (15 / 16 : ℝ≥0∞) * (1 / 16 : ℝ≥0∞) ^ x i)
    (hE : ∀ b, ∃ y ∈
      (paperBlockConstraints (ι := ι) s T m site b : Set (ι b → ℕ)),
        y ∈ (μb b).support)
    (ρ : ∀ b, ι b → ℕ)
    (hρ : ∀ b,
      (∑ i, ρ b i) + paperExternalPairMaxAt s T (site b) < m) :
    (μ.filter
      (HLOZConditionalProduct.blockEvent
        (paperBlockConstraints (ι := ι) s T m site))
      (HLOZConditionalProduct.blockEvent_meets_support μ μb hprod
        (paperBlockConstraints (ι := ι) s T m site) hE)) ρ =
      ∏ b,
        (∏ i, (15 / 16 : ℝ≥0∞) * (1 / 16 : ℝ≥0∞) ^ ρ b i) /
          ∑ n ∈ Finset.range (paperBlockThreshold s T m (site b)),
            ((Fintype.card (ι b) + n - 1).choose n : ℝ≥0∞) *
              (15 / 16 : ℝ≥0∞) ^ Fintype.card (ι b) *
                (1 / 16 : ℝ≥0∞) ^ n := by
  rw [filter_paperBlockConstraints_apply_eq_prod s T m site μ μb hprod hE ρ]
  apply Finset.prod_congr rfl
  intro b _
  apply HLOZConditionalProduct.filter_natSumBelow_apply
    (μb b) (15 / 16) (1 / 16) (hgeom b)
    (paperBlockThreshold s T m (site b)) (hE b)
  unfold paperBlockThreshold
  have := hρ b
  omega

end FiniteConditionalLaw

/-! ### Identification with the landed external path at an even horizon -/

/-- Original time indices retained after the first `N` complete increment
pairs: time zero, followed by both times of every non-distinguished pair. -/
noncomputable def explicitRetainedPairTimes
    (ω : ℕ → Direction) (N : ℕ) : Finset ℕ :=
  {0} ∪ (Finset.range N).biUnion fun r ↦
    if incrementPair r ω = distinguishedIncrementPair then ∅
    else {2 * r + 1, 2 * r + 2}

theorem retainedTimes_even_eq_explicit
    (ω : ℕ → Direction) (N : ℕ) :
    retainedTimes (simpleRandomWalk ω) (2 * N) =
      explicitRetainedPairTimes ω N := by
  classical
  ext j
  simp only [retainedTimes, lazyRemovedTimes, partialLazyRemovedTimes,
    not_isLazyEnd_odd (simpleRandomWalk ω) N, if_false,
    Finset.union_empty, completedLazyRemovedTimes,
    lazyEndsThrough_even_eq_image, explicitRetainedPairTimes,
    Finset.mem_sdiff, Finset.mem_range, Finset.mem_union, Finset.mem_insert,
    Finset.mem_singleton, Finset.mem_biUnion, Finset.mem_image]
  constructor
  · rintro ⟨hjN, hjNotRemoved⟩
    by_cases hj0 : j = 0
    · exact Or.inl hj0
    · right
      let r := (j - 1) / 2
      have hrN : r < N := by
        dsimp only [r]
        omega
      refine ⟨r, hrN, ?_⟩
      have hjshape : j = 2 * r + 1 ∨ j = 2 * r + 2 := by
        dsimp only [r]
        omega
      by_cases hrLazy : incrementPair r ω = distinguishedIncrementPair
      · exfalso
        apply hjNotRemoved
        refine ⟨2 * r + 2, ?_, ?_⟩
        · refine ⟨r, ?_, rfl⟩
          exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hrN, hrLazy⟩
        · rcases hjshape with hj | hj
          · left
            omega
          · right
            exact hj
      · simp only [hrLazy, if_false, Finset.mem_insert, Finset.mem_singleton]
        exact hjshape
  · intro hj
    rcases hj with rfl | hj
    · constructor
      · simp
      · rintro ⟨k, hk, hk0⟩
        rcases hk with ⟨q, hq, rfl⟩
        rcases hk0 with hk0 | hk0 <;> omega
    · rcases hj with ⟨r, hrN, hjr⟩
      by_cases hrLazy : incrementPair r ω = distinguishedIncrementPair
      · simp [hrLazy] at hjr
      · simp only [hrLazy, if_false, Finset.mem_insert,
          Finset.mem_singleton] at hjr
        refine ⟨by rcases hjr with rfl | rfl <;> omega, ?_⟩
        rintro ⟨k, hk, hjk⟩
        rcases hk with ⟨q, hq, rfl⟩
        have hqLazy := (Finset.mem_filter.mp hq).2
        rcases hjr with hjr | hjr
        · rcases hjk with hjk | hjk
          · have hqr : q = r := by omega
            subst q
            exact hrLazy hqLazy
          · omega
        · rcases hjk with hjk | hjk
          · omega
          · have hqr : q = r := by omega
            subst q
            exact hrLazy hqLazy

/-- Increasing list form of `explicitRetainedPairTimes`. -/
def explicitRetainedPairTimeList
    (ω : ℕ → Direction) (N : ℕ) : List ℕ :=
  0 :: (List.range N).flatMap fun r ↦
    if incrementPair r ω = distinguishedIncrementPair then []
    else [2 * r + 1, 2 * r + 2]

theorem explicitRetainedPairTimeList_nodup_bound
    (ω : ℕ → Direction) (N : ℕ) :
    (explicitRetainedPairTimeList ω N).Nodup ∧
      ∀ j ∈ explicitRetainedPairTimeList ω N, j ≤ 2 * N := by
  induction N with
  | zero => simp [explicitRetainedPairTimeList]
  | succ N ih =>
      rw [explicitRetainedPairTimeList, List.range_succ, List.flatMap_append]
      change ((explicitRetainedPairTimeList ω N) ++
        [N].flatMap (fun r ↦
          if incrementPair r ω = distinguishedIncrementPair then []
          else [2 * r + 1, 2 * r + 2])).Nodup ∧ _
      by_cases hN : incrementPair N ω = distinguishedIncrementPair
      · simp only [hN, if_true, List.flatMap_singleton, List.append_nil]
        exact ⟨ih.1, fun j hj ↦ (ih.2 j hj).trans (by omega)⟩
      · simp only [hN, if_false, List.flatMap_singleton]
        change ((explicitRetainedPairTimeList ω N) ++
          [2 * N + 1, 2 * N + 2]).Nodup ∧
            ∀ j ∈ (explicitRetainedPairTimeList ω N) ++
              [2 * N + 1, 2 * N + 2], j ≤ 2 * (N + 1)
        constructor
        · rw [List.nodup_append]
          refine ⟨ih.1, by simp, ?_⟩
          intro a ha b hb
          have haN := ih.2 a ha
          simp only [List.mem_cons, List.not_mem_nil,
            or_false] at hb
          rcases hb with rfl | rfl <;> omega
        · intro j hj
          rw [List.mem_append] at hj
          rcases hj with hj | hj
          · exact (ih.2 j hj).trans (by omega)
          · simp only [List.mem_cons, List.not_mem_nil,
              or_false] at hj
            rcases hj with rfl | rfl <;> omega

theorem explicitRetainedPairTimeList_toFinset
    (ω : ℕ → Direction) (N : ℕ) :
    (explicitRetainedPairTimeList ω N).toFinset =
      explicitRetainedPairTimes ω N := by
  classical
  ext j
  simp only [List.mem_toFinset, explicitRetainedPairTimeList,
    List.mem_cons, List.mem_flatMap, List.mem_range,
    explicitRetainedPairTimes, Finset.mem_union, Finset.mem_singleton,
    Finset.mem_biUnion, Finset.mem_range]
  constructor
  · rintro (rfl | ⟨r, hrN, hjr⟩)
    · exact Or.inl rfl
    · right
      refine ⟨r, hrN, ?_⟩
      by_cases hr : incrementPair r ω = distinguishedIncrementPair
      · simp [hr] at hjr
      · simpa [hr] using hjr
  · rintro (rfl | ⟨r, hrN, hjr⟩)
    · exact Or.inl rfl
    · right
      refine ⟨r, hrN, ?_⟩
      by_cases hr : incrementPair r ω = distinguishedIncrementPair
      · simp [hr] at hjr
      · simpa [hr] using hjr

/-- The landed deleted path is the original walk sampled at exactly the
retained pair-time indices. -/
theorem paperDeletedPath_eq_map_explicitRetainedTimes
    (ω : ℕ → Direction) (N : ℕ) :
    paperDeletedPathAtPairHorizon ω N =
      (explicitRetainedPairTimeList ω N).map (simpleRandomWalk ω) := by
  induction N with
  | zero => simp [paperDeletedPathAtPairHorizon,
      paperDeletedDirectionsAtPairHorizon, explicitRetainedPairTimeList,
      simpleRandomWalk]
  | succ N ih =>
      rw [paperDeletedPathAtPairHorizon,
        paperDeletedDirectionsAtPairHorizon_eq, deletedDirectionsThrough,
        List.range_succ, List.flatMap_append, List.scanl_append]
      rw [explicitRetainedPairTimeList, List.range_succ,
        List.flatMap_append]
      rw [List.map_cons, List.map_append]
      have ih' := ih
      rw [paperDeletedPathAtPairHorizon,
        paperDeletedDirectionsAtPairHorizon_eq] at ih'
      have hdel :
          (List.range N).flatMap (fun r ↦
            if incrementPair r ω = distinguishedIncrementPair then []
            else [ω (2 * r), ω (2 * r + 1)]) =
            deletedDirectionsThrough ω N := rfl
      rw [hdel]
      rw [ih']
      change (explicitRetainedPairTimeList ω N).map (simpleRandomWalk ω) ++
          (List.scanl (fun x d ↦ x + directionStep d)
            ((deletedDirectionsThrough ω N).foldl
              (fun x d ↦ x + directionStep d) (0, 0))
            ([N].flatMap fun r ↦
              if incrementPair r ω = distinguishedIncrementPair then []
              else [ω (2 * r), ω (2 * r + 1)])).tail =
        (explicitRetainedPairTimeList ω N).map (simpleRandomWalk ω) ++
          ([N].flatMap fun r ↦
            if incrementPair r ω = distinguishedIncrementPair then []
            else [2 * r + 1, 2 * r + 2]).map (simpleRandomWalk ω)
      rw [foldl_deletedDirectionsThrough]
      apply congrArg ((explicitRetainedPairTimeList ω N).map
        (simpleRandomWalk ω) ++ ·)
      by_cases hN : incrementPair N ω = distinguishedIncrementPair
      · simp [hN]
      · simp only [hN, if_false, List.flatMap_singleton, List.scanl_cons,
          List.tail_cons, List.map_cons, List.map_nil]
        rw [simpleRandomWalk_succ' ω (2 * N),
          show 2 * N + 2 = (2 * N + 1) + 1 by omega,
          simpleRandomWalk_succ' ω (2 * N + 1)]
        rw [simpleRandomWalk_succ' ω (2 * N)]
        rfl

theorem card_filter_toFinset_eq_count_map
    {α : Type*} [DecidableEq α]
    (l : List α) (hNodup : l.Nodup) (f : α → Site) (y : Site) :
    (l.toFinset.filter fun x ↦ f x = y).card = (l.map f).count y := by
  induction l with
  | nil => simp
  | cons a l ih =>
      rw [List.nodup_cons] at hNodup
      rw [List.toFinset_cons, Finset.filter_insert, List.map_cons]
      by_cases h : f a = y
      · rw [if_pos h]
        have ha : a ∉ l.toFinset.filter fun x ↦ f x = y := by
          intro haFilter
          have haFinset : a ∈ l.toFinset := (Finset.mem_filter.mp haFilter).1
          exact hNodup.1 (by simpa using haFinset)
        rw [Finset.card_insert_of_notMem ha]
        rw [← h] at ih ⊢
        rw [List.count_cons_self, ih hNodup.2]
      · rw [if_neg h]
        rw [List.count_cons_of_ne h, ih hNodup.2]

/-- Exact identification missing from the decomposition layer: at every even
pair horizon, `paperExternalLocalTime` is the visit count on the landed
finite deleted/external path. -/
theorem paperExternalLocalTime_even_eq_deletedPath_count
    (ω : ℕ → Direction) (N : ℕ) (x : Site) :
    paperExternalLocalTime (simpleRandomWalk ω) (2 * N) x =
      (paperDeletedPathAtPairHorizon ω N).count x := by
  unfold paperExternalLocalTime
  rw [retainedTimes_even_eq_explicit,
    ← explicitRetainedPairTimeList_toFinset,
    paperDeletedPath_eq_map_explicitRetainedTimes]
  exact card_filter_toFinset_eq_count_map
    (explicitRetainedPairTimeList ω N)
    (explicitRetainedPairTimeList_nodup_bound ω N).1
    (simpleRandomWalk ω) x

/-- Scanning the two directions of every terminal label is definitionally the
same path as the recursive external-tail reconstruction. -/
theorem scanl_externalDirectionsFromLabels_eq_reconstructExternalTail
    (a : Site) (labels : List IncrementPair) :
    (Erdos1166.externalDirectionsFromLabels labels).scanl
        (fun x d ↦ x + directionStep d) a =
      a :: reconstructExternalTail a labels := by
  induction labels generalizing a with
  | nil => rfl
  | cons p labels ih =>
      simp only [Erdos1166.externalDirectionsFromLabels, List.flatMap_cons,
        Erdos1166.pairDirections, List.cons_append, List.nil_append,
        List.scanl_cons, reconstructExternalTail]
      change a :: (a + directionStep (p 0)) ::
          (Erdos1166.externalDirectionsFromLabels labels).scanl
            (fun x d ↦ x + directionStep d) (pairEndpoint a p) =
        a :: (a + directionStep (p 0)) :: pairEndpoint a p ::
          reconstructExternalTail (pairEndpoint a p) labels
      rw [ih]

theorem externalPathFromLabels_eq_reconstructExternalTail
    (labels : List IncrementPair) :
    Erdos1166.externalPathFromLabels labels =
      (0, 0) :: reconstructExternalTail (0, 0) labels := by
  exact scanl_externalDirectionsFromLabels_eq_reconstructExternalTail
    (0, 0) labels

/-- A run vector whose labels are the actual terminal labels through pair
horizon `N` realizes, without any bridge premise, both the paper clock and the
paper external-local-time profile. -/
theorem paperExternalState_even_of_terminalLabels
    (ω : ℕ → Direction) (N : ℕ) (runs : List PairRun)
    (hlabels : terminalLabels runs = terminalPairLabelsThrough ω N) :
    paperExternalClock (simpleRandomWalk ω) (2 * N) = 2 * runs.length ∧
      ∀ x, paperExternalLocalTime (simpleRandomWalk ω) (2 * N) x =
        reconstructedExternalLocalTime (0, 0) runs x := by
  constructor
  · rw [paperExternalClock_even_eq_external_length,
      externalDirectionsFromLabels_length, ← hlabels]
    simp [terminalLabels]
  · intro x
    rw [paperExternalLocalTime_even_eq_deletedPath_count,
      ← externalPathFromLabels_eq_paperDeletedPath, ← hlabels,
      externalPathFromLabels_eq_reconstructExternalTail]
    rfl

theorem paperExternalPairMax_even_eq_reconstructed
    (ω : ℕ → Direction) (N : ℕ) (runs : List PairRun)
    (hlabels : terminalLabels runs = terminalPairLabelsThrough ω N)
    (x : Site) :
    paperExternalPairMaxAt (simpleRandomWalk ω) (2 * N) x =
      reconstructedExternalPairMax (0, 0) runs x := by
  unfold paperExternalPairMaxAt reconstructedExternalPairMax
  rw [(paperExternalState_even_of_terminalLabels ω N runs hlabels).2 x,
    (paperExternalState_even_of_terminalLabels ω N runs hlabels).2
      (x + paperE1)]

/-- Once reconstruction is matched to the finite paper horizon, membership in
the actual paper-profile constraint is exactly inequality (4.8) for the
reconstructed domino. -/
theorem paper_constraint_iff_reconstructed_inequality48
    (ω : ℕ → Direction) (N : ℕ) (runs : List PairRun)
    (hlabels : terminalLabels runs = terminalPairLabelsThrough ω N)
    (x : Site) (m : ℕ) (hx : chessEven x) :
    lazyBlockSum (0, 0) runs x +
        paperExternalPairMaxAt (simpleRandomWalk ω) (2 * N) x < m ↔
      reconstructedPairMax (0, 0) runs x < m := by
  rw [paperExternalPairMax_even_eq_reconstructed ω N runs hlabels x]
  exact inequality48_iff_reconstructedPairMax_lt
    (0, 0) runs x m (by simp [chessEven]) hx

theorem paper_equation47_iff_reconstructedPairMax
    (ω : ℕ → Direction) (N : ℕ) (runs : List PairRun)
    (hlabels : terminalLabels runs = terminalPairLabelsThrough ω N)
    (x : Site) (m δ : ℕ) (hx : chessEven x) :
    lazyBlockSum (0, 0) runs x +
        paperExternalPairMaxAt (simpleRandomWalk ω) (2 * N) x = m - δ ↔
      reconstructedPairMax (0, 0) runs x = m - δ := by
  rw [paperExternalPairMax_even_eq_reconstructed ω N runs hlabels x]
  exact equation47_iff_reconstructedPairMax
    (0, 0) runs x m δ (by simp [chessEven]) hx

section ReconstructedFiniteConditionalLaw

variable {β : Type*} [Fintype β]
variable {ι : β → Type*} [∀ b, Fintype (ι b)] [∀ b, DecidableEq (ι b)]

omit [Fintype β] in
/-- If the coordinate vector `ρ b` lists precisely the reconstructed run
coordinates at the selected base `site b`, the paper's finite product event
is equivalent to requiring (4.8) for every reconstructed domino. -/
theorem mem_paperBlockEvent_iff_reconstructed_constraints
    (ω : ℕ → Direction) (N : ℕ) (runs : List PairRun)
    (hlabels : terminalLabels runs = terminalPairLabelsThrough ω N)
    (m : ℕ) (site : β → Site) (ρ : ∀ b, ι b → ℕ)
    (hsite : ∀ b, chessEven (site b))
    (hcoordinates : ∀ b, ∑ i, ρ b i =
      lazyBlockSum (0, 0) runs (site b)) :
    ρ ∈ HLOZConditionalProduct.blockEvent
        (paperBlockConstraints (ι := ι)
          (simpleRandomWalk ω) (2 * N) m site) ↔
      ∀ b, reconstructedPairMax (0, 0) runs (site b) < m := by
  rw [mem_blockEvent_paperBlockConstraints_iff]
  constructor
  · intro h b
    apply (paper_constraint_iff_reconstructed_inequality48
      ω N runs hlabels (site b) m (hsite b)).mp
    rw [← hcoordinates b]
    exact h b
  · intro h b
    rw [hcoordinates b]
    exact (paper_constraint_iff_reconstructed_inequality48
      ω N runs hlabels (site b) m (hsite b)).mpr (h b)

/-- Strong reconstructed form of the finite Proposition 4.3 law.  The input
atom is identified with the run coordinates of the injective reconstruction;
assuming all reconstructed non-special dominoes satisfy (4.8), its filtered
mass is the explicit product of truncated geometric block masses. -/
theorem reconstructed_filter_apply_eq_geometric_product
    (ω : ℕ → Direction) (N : ℕ) (runs : List PairRun)
    (hlabels : terminalLabels runs = terminalPairLabelsThrough ω N)
    (m : ℕ) (site : β → Site) (ρ : ∀ b, ι b → ℕ)
    (hsite : ∀ b, chessEven (site b))
    (hcoordinates : ∀ b, ∑ i, ρ b i =
      lazyBlockSum (0, 0) runs (site b))
    (hreconstructed : ∀ b,
      reconstructedPairMax (0, 0) runs (site b) < m)
    (μ : PMF (∀ b, ι b → ℕ)) (μb : ∀ b, PMF (ι b → ℕ))
    (hprod : ∀ x, μ x = ∏ b, μb b (x b))
    (hgeom : ∀ b x, μb b x =
      ∏ i, (15 / 16 : ℝ≥0∞) * (1 / 16 : ℝ≥0∞) ^ x i)
    (hE : ∀ b, ∃ y ∈
      (paperBlockConstraints (ι := ι)
        (simpleRandomWalk ω) (2 * N) m site b : Set (ι b → ℕ)),
        y ∈ (μb b).support) :
    (μ.filter
      (HLOZConditionalProduct.blockEvent
        (paperBlockConstraints (ι := ι)
          (simpleRandomWalk ω) (2 * N) m site))
      (HLOZConditionalProduct.blockEvent_meets_support μ μb hprod
        (paperBlockConstraints (ι := ι)
          (simpleRandomWalk ω) (2 * N) m site) hE)) ρ =
      ∏ b,
        (∏ i, (15 / 16 : ℝ≥0∞) * (1 / 16 : ℝ≥0∞) ^ ρ b i) /
          ∑ n ∈ Finset.range (paperBlockThreshold
            (simpleRandomWalk ω) (2 * N) m (site b)),
            ((Fintype.card (ι b) + n - 1).choose n : ℝ≥0∞) *
              (15 / 16 : ℝ≥0∞) ^ Fintype.card (ι b) *
                (1 / 16 : ℝ≥0∞) ^ n := by
  apply filter_paperBlockConstraints_apply_eq_geometric_product
    (simpleRandomWalk ω) (2 * N) m site μ μb hprod hgeom hE ρ
  intro b
  have hp := (paper_constraint_iff_reconstructed_inequality48
    ω N runs hlabels (site b) m (hsite b)).mpr (hreconstructed b)
  rw [← hcoordinates b] at hp
  exact hp

end ReconstructedFiniteConditionalLaw

end Erdos1166.HLOZReconstruction
