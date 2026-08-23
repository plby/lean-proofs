import ErdosProblems.Erdos1166.Erdos1166HLOZExternalUpper
import ErdosProblems.Erdos1166.Erdos1166HLOZProp44
import ErdosProblems.Erdos1166.Erdos1166HLOZReconstruction

/-!
The infinite external chain used in Hao--Li--Okada--Zheng.  Its coordinates
are iid direction pairs, uniformly distributed over the fifteen pairs other
than the distinguished backtrack `(+e₁,-e₁)`.  This file constructs the
path law, proves the even-time stationarity and parity properties needed by
Proposition 4.4, and identifies every finite prefix with the deleted path
constructed from the original walk.
-/

namespace Erdos1166.HLOZExternalChain

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

open HLOZDecomposition
open HLOZExternalUpper
open HLOZProp44

/-- One terminal label of the external chain: any direction pair except the
distinguished pair which is deleted by the HLOZ time change. -/
abbrev ExternalPairLabel :=
  {p : IncrementPair // p ≠ distinguishedIncrementPair}

instance : Nonempty ExternalPairLabel :=
  ⟨⟨fun _ ↦ (2 : Direction), by decide⟩⟩

/-- The uniform law on the fifteen possible terminal pair labels. -/
noncomputable def externalPairLabelLaw : Measure ExternalPairLabel :=
  (PMF.uniformOfFintype ExternalPairLabel).toMeasure

instance : IsProbabilityMeasure externalPairLabelLaw := by
  unfold externalPairLabelLaw
  infer_instance

/-- The iid infinite sequence of terminal pair labels. -/
noncomputable def externalLabelLaw : Measure (ℕ → ExternalPairLabel) :=
  Measure.infinitePi fun _ : ℕ ↦ externalPairLabelLaw

instance : IsProbabilityMeasure externalLabelLaw := by
  unfold externalLabelLaw
  infer_instance

/-- The within-pair coordinate of external time `t`. -/
def pairOffset (t : ℕ) : Fin 2 := ⟨t % 2, Nat.mod_lt _ (by omega)⟩

/-- Flatten an infinite sequence of retained pair labels to directions. -/
def externalDirectionStream
    (labels : ℕ → ExternalPairLabel) (t : ℕ) : Direction :=
  (labels (t / 2) : IncrementPair) (pairOffset t)

/-- The infinite external path reconstructed from iid terminal labels. -/
def externalWalk (labels : ℕ → ExternalPairLabel) : ℕ → Site :=
  simpleRandomWalk (externalDirectionStream labels)

/-- The canonical law of the HLOZ external path. -/
noncomputable def externalPathLaw : Measure (ℕ → Site) :=
  externalLabelLaw.map externalWalk

theorem measurable_externalDirectionStream :
    Measurable externalDirectionStream := by
  apply measurable_pi_lambda
  intro t
  exact (measurable_of_countable
    (fun p : ExternalPairLabel ↦
      (p.1 : IncrementPair) (pairOffset t))).comp
      (measurable_pi_apply (t / 2))

theorem measurable_externalWalk : Measurable externalWalk := by
  exact measurable_simpleRandomWalk.comp measurable_externalDirectionStream

instance : IsProbabilityMeasure externalPathLaw := by
  unfold externalPathLaw
  exact Measure.isProbabilityMeasure_map measurable_externalWalk.aemeasurable

/-- Drop the first `j` terminal labels. -/
def labelShift (j : ℕ) (labels : ℕ → ExternalPairLabel) :
    ℕ → ExternalPairLabel := fun q ↦ labels (j + q)

theorem measurable_labelShift (j : ℕ) : Measurable (labelShift j) := by
  apply measurable_pi_lambda
  intro q
  exact measurable_pi_apply (j + q)

/-- An iid product law is invariant under deletion of a deterministic
prefix. -/
theorem externalLabelLaw_map_labelShift (j : ℕ) :
    externalLabelLaw.map (labelShift j) = externalLabelLaw := by
  unfold externalLabelLaw labelShift
  simpa using
    (Measure.map_infinitePi_infinitePi_of_inj
      (P := fun _ : ℕ ↦ externalPairLabelLaw)
      (f := fun q : ℕ ↦ j + q)
      (fun _ _ h ↦ Nat.add_left_cancel h))

theorem externalDirectionStream_even_shift
    (labels : ℕ → ExternalPairLabel) (j q : ℕ) :
    externalDirectionStream labels (2 * j + q) =
      externalDirectionStream (labelShift j labels) q := by
  change
    (labels ((2 * j + q) / 2) : IncrementPair)
        ⟨(2 * j + q) % 2, Nat.mod_lt _ (by omega)⟩ =
      (labels (j + q / 2) : IncrementPair)
        ⟨q % 2, Nat.mod_lt _ (by omega)⟩
  have hdiv : (2 * j + q) / 2 = j + q / 2 := by omega
  have hmod : (2 * j + q) % 2 = q % 2 := by omega
  rw [hdiv]
  have hoff :
      (⟨(2 * j + q) % 2, Nat.mod_lt _ (by omega)⟩ : Fin 2) =
        ⟨q % 2, Nat.mod_lt _ (by omega)⟩ := Fin.ext hmod
  rw [hoff]

/-- Restarting the path after `2j` external steps is exactly shifting the
terminal-label sequence by `j`. -/
theorem shiftedPath_externalWalk_even
    (labels : ℕ → ExternalPairLabel) (j : ℕ) :
    shiftedPath (externalWalk labels) (2 * j) =
      externalWalk (labelShift j labels) := by
  funext q
  unfold shiftedPath externalWalk simpleRandomWalk
  rw [Finset.sum_range_add]
  simp only [add_sub_cancel_left]
  apply Finset.sum_congr rfl
  intro r hr
  rw [externalDirectionStream_even_shift]

/-- The canonical external path has stationary increments when restarted at
an even external time, precisely the structural hypothesis used in HLOZ
Proposition 4.4. -/
theorem externalPathLaw_hasStationaryEvenIncrements :
    HasStationaryEvenIncrements externalPathLaw := by
  intro j
  unfold externalPathLaw
  have hcomp :
      (fun labels ↦ shiftedPath (externalWalk labels) (2 * j)) =
        externalWalk ∘ labelShift j := by
    funext labels
    exact shiftedPath_externalWalk_even labels j
  calc
    Measure.map (fun s ↦ shiftedPath s (2 * j))
        (Measure.map externalWalk externalLabelLaw) =
        Measure.map
          ((fun s ↦ shiftedPath s (2 * j)) ∘ externalWalk)
          externalLabelLaw :=
      Measure.map_map (measurable_shiftedPath (2 * j))
        measurable_externalWalk
    _ = Measure.map (externalWalk ∘ labelShift j) externalLabelLaw := by
      congr 1
    _ = Measure.map externalWalk
        (Measure.map (labelShift j) externalLabelLaw) :=
      (Measure.map_map measurable_externalWalk
        (measurable_labelShift j)).symm
    _ = Measure.map externalWalk externalLabelLaw := by
      rw [externalLabelLaw_map_labelShift]

theorem externalWalk_succ
    (labels : ℕ → ExternalPairLabel) (t : ℕ) :
    externalWalk labels (t + 1) =
      externalWalk labels t +
        directionStep (externalDirectionStream labels t) := by
  simp [externalWalk, simpleRandomWalk, Finset.sum_range_succ]

/-- Chessboard parity of a nearest-neighbour external path. -/
theorem chessEven_externalWalk_iff
    (labels : ℕ → ExternalPairLabel) (t : ℕ) :
    HLOZPairing.chessEven (externalWalk labels t) ↔ Even t := by
  induction t with
  | zero => simp [externalWalk, simpleRandomWalk, HLOZPairing.chessEven]
  | succ t ih =>
      rw [externalWalk_succ,
        HLOZReconstruction.chessEven_add_directionStep_iff, ih]
      simpa only [Nat.even_add_one]

theorem externalWalk_evenSitesAtEvenTimes
    (labels : ℕ → ExternalPairLabel) :
    EvenSitesAtEvenTimes (externalWalk labels) := by
  intro t ht
  exact (chessEven_externalWalk_iff labels t).mp ht

theorem externalPathLaw_evenSitesAtEvenTimes :
    ∀ᵐ s ∂externalPathLaw, EvenSitesAtEvenTimes s := by
  have hmeas : MeasurableSet
      {s : ℕ → Site | EvenSitesAtEvenTimes s} := by
    have heq : {s : ℕ → Site | EvenSitesAtEvenTimes s} =
        ⋂ t : ℕ, {s | isEvenSite (s t) → Even t} := by
      ext s
      simp [EvenSitesAtEvenTimes]
    rw [heq]
    apply MeasurableSet.iInter
    intro t
    have hsite : MeasurableSet {x : Site | isEvenSite x} :=
      (Set.to_countable {x : Site | isEvenSite x}).measurableSet
    have hp : Measurable (fun s : ℕ → Site ↦ isEvenSite (s t)) :=
      measurableSet_setOfPred.mp <|
        hsite.preimage
          (measurable_pi_apply t : Measurable fun s : ℕ → Site ↦ s t)
    exact (hp.imp measurable_const).setOf
  unfold externalPathLaw
  rw [ae_map_iff measurable_externalWalk.aemeasurable hmeas]
  exact Filter.Eventually.of_forall externalWalk_evenSitesAtEvenTimes

/-! ### Finite-prefix and deleted-path coupling -/

/-- The first `L` iid external labels, viewed as ordinary increment pairs. -/
def externalLabelPrefix
    (labels : ℕ → ExternalPairLabel) (L : ℕ) : List IncrementPair :=
  List.ofFn fun i : Fin L ↦ (labels i : IncrementPair)

theorem externalLabelPrefix_nondistinguished
    (labels : ℕ → ExternalPairLabel) (L : ℕ) :
    ∀ p ∈ externalLabelPrefix labels L,
      p ≠ distinguishedIncrementPair := by
  intro p hp
  rw [externalLabelPrefix, List.mem_ofFn] at hp
  obtain ⟨i, rfl⟩ := hp
  exact (labels i).property

theorem externalLabelPrefix_length
    (labels : ℕ → ExternalPairLabel) (L : ℕ) :
    (externalLabelPrefix labels L).length = L := by
  simp [externalLabelPrefix]

theorem externalDirections_labelPrefix
    (labels : ℕ → ExternalPairLabel) (L : ℕ) :
    externalDirectionsFromLabels (externalLabelPrefix labels L) =
      List.ofFn fun t : Fin (2 * L) ↦ externalDirectionStream labels t := by
  unfold externalLabelPrefix externalDirectionsFromLabels
  change List.flatten
      (List.map pairDirections
        (List.ofFn fun i : Fin L ↦ (labels i : IncrementPair))) = _
  rw [List.map_ofFn, List.ofFn_mul']
  congr 1
  rw [List.ofFn_inj]
  funext i
  simp only [Function.comp_apply]
  rw [show pairDirections (labels i : IncrementPair) =
      List.ofFn (fun k : Fin 2 ↦ (labels i : IncrementPair) k) by
    simp [pairDirections, List.ofFn_succ]]
  rw [List.ofFn_inj]
  funext k
  fin_cases k
  · symm
    simpa [labelShift, externalDirectionStream, pairOffset] using
      externalDirectionStream_even_shift labels (i : ℕ) 0
  · symm
    simpa [labelShift, externalDirectionStream, pairOffset] using
      externalDirectionStream_even_shift labels (i : ℕ) 1

theorem foldl_directionPrefix_eq_walk
    (ω : ℕ → Direction) (N : ℕ) :
    List.foldl (fun x d ↦ x + directionStep d) (0, 0)
        (List.ofFn fun i : Fin N ↦ ω i) = simpleRandomWalk ω N := by
  induction N with
  | zero => simp [simpleRandomWalk]
  | succ N ih =>
      simp only [List.ofFn_succ', Fin.val_castSucc, Fin.val_last]
      rw [List.concat_eq_append, List.foldl_append, ih]
      simp [simpleRandomWalk_succ']

theorem take_directionPrefix {α : Type*}
    (f : ℕ → α) (N k : ℕ) (hk : k ≤ N) :
    (List.ofFn fun i : Fin N ↦ f i).take k =
      List.ofFn fun i : Fin k ↦ f i := by
  apply List.ext_getElem
  · simp [Nat.min_eq_left hk]
  · intro i hi₁ hi₂
    rw [List.getElem_take]
    simp

/-- Scanning the first `N` values of an infinite direction stream produces
exactly the first `N+1` vertices of its partial-sum walk. -/
theorem scanl_directionPrefix_eq_walkPrefix
    (ω : ℕ → Direction) (N : ℕ) :
    (List.ofFn fun i : Fin N ↦ ω i).scanl
        (fun x d ↦ x + directionStep d) (0, 0) =
      List.ofFn fun i : Fin (N + 1) ↦ simpleRandomWalk ω i := by
  apply List.ext_getElem
  · simp
  · intro i hi₁ hi₂
    rw [List.getElem_scanl]
    rw [take_directionPrefix ω N i (by simpa using hi₁)]
    rw [foldl_directionPrefix_eq_walk]
    cases i <;> simp

/-- Exact finite-prefix identity between the infinite iid external chain and
the finite terminal-label reconstruction used in the decomposition. -/
theorem externalPath_labelPrefix
    (labels : ℕ → ExternalPairLabel) (L : ℕ) :
    externalPathFromLabels (externalLabelPrefix labels L) =
      List.ofFn fun t : Fin (2 * L + 1) ↦ externalWalk labels t := by
  unfold externalPathFromLabels externalWalk
  rw [externalDirections_labelPrefix,
    scanl_directionPrefix_eq_walkPrefix]

/-- At a deterministic original pair horizon, any iid label stream whose
prefix is the observed terminal-label list reconstructs the paper's deleted
path exactly. -/
theorem externalWalkPrefix_eq_paperDeletedPath
    (labels : ℕ → ExternalPairLabel) (ω : ℕ → Direction) (N L : ℕ)
    (hprefix : externalLabelPrefix labels L =
      terminalPairLabelsThrough ω N) :
    List.ofFn (fun t : Fin (2 * L + 1) ↦ externalWalk labels t) =
      paperDeletedPathAtPairHorizon ω N := by
  rw [← externalPath_labelPrefix, hprefix,
    externalPathFromLabels_eq_paperDeletedPath]

theorem count_walkPrefix_eq_localTime
    (s : ℕ → Site) (n : ℕ) (x : Site) :
    (List.ofFn fun t : Fin (n + 1) ↦ s t).count x =
      localTime s n x := by
  induction n with
  | zero =>
      unfold localTime
      change List.count x [s 0] =
        (({0} : Finset ℕ).filter fun j ↦ s j = x).card
      rw [Finset.filter_singleton]
      by_cases h : s 0 = x <;> simp [h]
  | succ n ih =>
      rw [List.ofFn_succ']
      simp only [Fin.val_castSucc, Fin.val_last]
      rw [List.concat_eq_append, List.count_append, ih]
      change localTime s n x + List.count x [s (n + 1)] =
        localTime s (n + 1) x
      have hrec : localTime s (n + 1) x =
          localTime s n x + if s (n + 1) = x then 1 else 0 := by
        unfold localTime
        rw [show n + 1 + 1 = (n + 1) + 1 by omega,
          Finset.range_add_one, Finset.filter_insert]
        have hnmem : n + 1 ∉
            (Finset.range (n + 1)).filter (fun j ↦ s j = x) := by
          simp
        split_ifs
        · rw [Finset.card_insert_of_notMem hnmem]
        · rfl
      rw [hrec]
      by_cases h : s (n + 1) = x <;> simp [h]

theorem take_externalWalkPrefix
    (labels : ℕ → ExternalPairLabel) (n : ℕ) :
    (List.ofFn (fun t : Fin (2 * externalLabelCount n + 1) ↦
        externalWalk labels t)).take (n + 1) =
      List.ofFn fun t : Fin (n + 1) ↦ externalWalk labels t := by
  exact take_directionPrefix (externalWalk labels)
    (2 * externalLabelCount n + 1) (n + 1)
    (external_time_fits_labelCount n)

/-- The list statistic used in `externalChainUpperBad` is exactly ordinary
local time of the infinite external path. -/
theorem externalOriginLocalTime_labelPrefix
    (labels : ℕ → ExternalPairLabel) (n : ℕ) :
    externalOriginLocalTimeFromLabels n
        (externalLabelPrefix labels (externalLabelCount n)) =
      localTime (externalWalk labels) n (0, 0) := by
  unfold externalOriginLocalTimeFromLabels
  rw [externalPath_labelPrefix, take_externalWalkPrefix,
    count_walkPrefix_eq_localTime]

theorem externalReturn_labelPrefix
    (labels : ℕ → ExternalPairLabel) (n : ℕ) :
    (externalPathFromLabels
        (externalLabelPrefix labels (externalLabelCount n))).getD n (0, 0) =
      externalWalk labels n := by
  rw [externalPath_labelPrefix]
  have hnlt : n < 2 * externalLabelCount n + 1 := by
    have := external_time_fits_labelCount n
    omega
  have hget := List.getElem_eq_getD
    (l := List.ofFn (fun t : Fin (2 * externalLabelCount n + 1) ↦
      externalWalk labels t)) (i := n)
    (h := by simpa using hnlt) (0, 0)
  calc
    (List.ofFn (fun t : Fin (2 * externalLabelCount n + 1) ↦
      externalWalk labels t)).getD n (0, 0) =
        (List.ofFn (fun t : Fin (2 * externalLabelCount n + 1) ↦
          externalWalk labels t))[n]'(by simpa using hnlt) := hget.symm
    _ = externalWalk labels n := by
      cases n <;> simp

/-- A fixed finite terminal-label prefix is a cell in the iid external-label
product space. -/
def externalPrefixCell {L : ℕ} (v : Fin L → ExternalPairLabel) :
    Set (ℕ → ExternalPairLabel) :=
  {labels | ∀ i : Fin L, labels i = v i}

theorem measurableSet_externalPrefixCell {L : ℕ}
    (v : Fin L → ExternalPairLabel) :
    MeasurableSet (externalPrefixCell v) := by
  have heq : externalPrefixCell v =
      ⋂ i : Fin L, {labels | labels i = v i} := by
    ext labels
    simp [externalPrefixCell]
  rw [heq]
  exact MeasurableSet.iInter fun i ↦
    measurableSet_eq_fun (measurable_pi_apply (i : ℕ)) measurable_const

theorem externalPrefixCell_eq_block {L : ℕ}
    (v : Fin L → ExternalPairLabel) :
    externalPrefixCell v =
      {labels | iidBlock (X := ExternalPairLabel) 0 L labels = v} := by
  ext labels
  simp [externalPrefixCell, iidBlock, funext_iff]

theorem externalPairLabelLaw_singleton (p : ExternalPairLabel) :
    externalPairLabelLaw {p} = (15 : ENNReal)⁻¹ := by
  simp [externalPairLabelLaw]

theorem externalLabelLaw_prefixCell {L : ℕ}
    (v : Fin L → ExternalPairLabel) :
    externalLabelLaw (externalPrefixCell v) =
      ((15 : ENNReal)⁻¹) ^ L := by
  rw [externalPrefixCell_eq_block]
  calc
    externalLabelLaw
        {labels | iidBlock (X := ExternalPairLabel) 0 L labels = v} =
        (externalLabelLaw.map
          (iidBlock (X := ExternalPairLabel) 0 L)) {v} := by
      rw [Measure.map_apply (measurable_iidBlock 0 L)
        (measurableSet_singleton v)]
      rfl
    _ = (Measure.infinitePi fun _ : Fin L ↦ externalPairLabelLaw) {v} := by
      rw [externalLabelLaw]
      exact congrArg (fun μ : Measure (Fin L → ExternalPairLabel) ↦ μ {v})
        (iidBlock_map externalPairLabelLaw 0 L)
    _ = ∏ i : Fin L, externalPairLabelLaw {v i} := by
      rw [Measure.infinitePi_singleton_of_fintype]
    _ = ((15 : ENNReal)⁻¹) ^ L := by
      simp [externalPairLabelLaw_singleton]

/-- Two different prescribed terminal-label vectors give disjoint product
cells. -/
theorem disjoint_externalPrefixCell {L : ℕ}
    {v w : Fin L → ExternalPairLabel} (hvw : v ≠ w) :
    Disjoint (externalPrefixCell v) (externalPrefixCell w) := by
  rw [Set.disjoint_left]
  intro labels hv hw
  apply hvw
  funext i
  exact (hv i).symm.trans (hw i)

/-- Uniqueness of a finite sequence of non-distinguished terminal labels in
the original increment stream. -/
theorem firstPairTerminalLabels_unique
    (start : ℕ) {a b : List IncrementPair}
    (ha : ∀ p ∈ a, p ≠ distinguishedIncrementPair)
    (hb : ∀ p ∈ b, p ≠ distinguishedIncrementPair)
    (hlen : a.length = b.length) {ω : ℕ → Direction}
    (hωa : ω ∈ firstPairTerminalLabelsEqFrom start a)
    (hωb : ω ∈ firstPairTerminalLabelsEqFrom start b) : a = b := by
  induction a generalizing start b with
  | nil =>
      cases b with
      | nil => rfl
      | cons q b => simp at hlen
  | cons p a ih =>
      cases b with
      | nil => simp at hlen
      | cons q b =>
          have hp : p ≠ distinguishedIncrementPair := ha p (by simp)
          have hq : q ≠ distinguishedIncrementPair := hb q (by simp)
          simp only [firstPairTerminalLabelsEqFrom, Set.mem_iUnion,
            Set.mem_inter_iff] at hωa hωb
          obtain ⟨t, hta, htaila⟩ := hωa
          obtain ⟨u, hub, htailb⟩ := hωb
          have htu : t = u := by
            by_contra hne
            rcases lt_or_gt_of_ne hne with hlt | hgt
            · have hdist := hub.1 t hlt
              exact hp (hta.2.symm.trans hdist)
            · have hdist := hta.1 u hgt
              exact hq (hub.2.symm.trans hdist)
          subst u
          have hpq : p = q := hta.2.symm.trans hub.2
          subst q
          congr 1
          apply ih (start := start + t + 1)
          · intro r hr
            exact ha r (by simp [hr])
          · intro r hr
            exact hb r (by simp [hr])
          · simpa using hlen
          · exact htaila
          · exact htailb

theorem disjoint_firstPairTerminalLabel_vectors {L : ℕ}
    {v w : Fin L → ExternalPairLabel} (hvw : v ≠ w) :
    Disjoint
      (firstPairTerminalLabelsEqFrom 0
        (List.ofFn fun i : Fin L ↦ (v i : IncrementPair)))
      (firstPairTerminalLabelsEqFrom 0
        (List.ofFn fun i : Fin L ↦ (w i : IncrementPair))) := by
  rw [Set.disjoint_left]
  intro ω hv hw
  apply hvw
  have heq := firstPairTerminalLabels_unique 0
    (fun p hp ↦ by
      rw [List.mem_ofFn] at hp
      obtain ⟨i, rfl⟩ := hp
      exact (v i).property)
    (fun p hp ↦ by
      rw [List.mem_ofFn] at hp
      obtain ⟨i, rfl⟩ := hp
      exact (w i).property)
    (by simp) hv hw
  have hfun : (fun i : Fin L ↦ (v i : IncrementPair)) =
      fun i : Fin L ↦ (w i : IncrementPair) :=
    List.ofFn_injective heq
  funext i
  exact Subtype.ext (congrFun hfun i)

/-! ### Exact finite-law bridge -/

def vectorLabels {L : ℕ} (v : Fin L → ExternalPairLabel) :
    List IncrementPair :=
  List.ofFn fun i ↦ (v i : IncrementPair)

theorem vectorLabels_length {L : ℕ} (v : Fin L → ExternalPairLabel) :
    (vectorLabels v).length = L := by simp [vectorLabels]

theorem vectorLabels_nondistinguished {L : ℕ}
    (v : Fin L → ExternalPairLabel) :
    ∀ p ∈ vectorLabels v, p ≠ distinguishedIncrementPair := by
  intro p hp
  rw [vectorLabels, List.mem_ofFn] at hp
  obtain ⟨i, rfl⟩ := hp
  exact (v i).property

noncomputable def selectedLabelEvent {L : ℕ}
    (P : (Fin L → ExternalPairLabel) → Prop) :
    Set (ℕ → ExternalPairLabel) := by
  classical
  exact ⋃ v, if P v then externalPrefixCell v else ∅

noncomputable def selectedOriginalEvent {L : ℕ}
    (P : (Fin L → ExternalPairLabel) → Prop) :
    Set (ℕ → Direction) := by
  classical
  exact ⋃ v, if P v then
    firstPairTerminalLabelsEqFrom 0 (vectorLabels v) else ∅

noncomputable def selectedMass {L : ℕ}
    (P : (Fin L → ExternalPairLabel) → Prop) : ENNReal := by
  classical
  exact ∑' v, if P v then ((15 : ENNReal)⁻¹) ^ L else 0

theorem measure_selectedLabelEvent {L : ℕ}
    (P : (Fin L → ExternalPairLabel) → Prop) :
    externalLabelLaw (selectedLabelEvent P) =
      selectedMass P := by
  classical
  unfold selectedLabelEvent selectedMass
  rw [measure_iUnion]
  · apply tsum_congr
    intro v
    by_cases hv : P v
    · simp [hv, externalLabelLaw_prefixCell]
    · simp [hv]
  · intro v w hvw
    change Disjoint (if P v then externalPrefixCell v else ∅)
      (if P w then externalPrefixCell w else ∅)
    by_cases hv : P v <;> by_cases hw : P w
    · simpa [hv, hw] using disjoint_externalPrefixCell hvw
    · simp [hw]
    · simp [hv]
    · simp [hv, hw]
  · intro v
    by_cases hv : P v
    · simpa [hv] using measurableSet_externalPrefixCell v
    · simp [hv]

theorem measure_selectedOriginalEvent {L : ℕ}
    (P : (Fin L → ExternalPairLabel) → Prop) :
    incrementLaw (selectedOriginalEvent P) =
      selectedMass P := by
  classical
  unfold selectedOriginalEvent selectedMass
  rw [measure_iUnion]
  · apply tsum_congr
    intro v
    by_cases hv : P v
    · simp only [hv, if_true]
      simpa [vectorLabels_length] using
        firstPairTerminalLabelsEqFrom_prob 0 (vectorLabels v)
          (vectorLabels_nondistinguished v)
    · simp [hv]
  · intro v w hvw
    change Disjoint
      (if P v then firstPairTerminalLabelsEqFrom 0 (vectorLabels v) else ∅)
      (if P w then firstPairTerminalLabelsEqFrom 0 (vectorLabels w) else ∅)
    by_cases hv : P v <;> by_cases hw : P w
    · simpa [hv, hw, vectorLabels] using
        disjoint_firstPairTerminalLabel_vectors hvw
    · simp [hw]
    · simp [hv]
    · simp [hv, hw]
  · intro v
    by_cases hv : P v
    · simpa [hv] using
        (iidTail_le 0 _
          (measurableSet_firstPairTerminalLabelsEqFrom_iidTail
            0 (vectorLabels v)))
    · simp [hv]

theorem measure_selected_events_eq {L : ℕ}
    (P : (Fin L → ExternalPairLabel) → Prop) :
    externalLabelLaw (selectedLabelEvent P) =
      incrementLaw (selectedOriginalEvent P) := by
  rw [measure_selectedLabelEvent, measure_selectedOriginalEvent]

def highVector (n : ℕ)
    (v : Fin (externalLabelCount n) → ExternalPairLabel) : Prop :=
  externalThreshold n ≤
    (externalOriginLocalTimeFromLabels n (vectorLabels v) : ℝ)

def returnVector (n : ℕ)
    (v : Fin (externalLabelCount n) → ExternalPairLabel) : Prop :=
  (externalPathFromLabels (vectorLabels v)).getD n (0, 0) = (0, 0)

theorem selectedLabelEvent_highVector (n : ℕ) :
    selectedLabelEvent (highVector n) =
      {labels | externalThreshold n ≤
        (localTime (externalWalk labels) n (0, 0) : ℝ)} := by
  classical
  ext labels
  constructor
  · intro h
    change externalThreshold n ≤
      (localTime (externalWalk labels) n (0, 0) : ℝ)
    simp only [selectedLabelEvent, Set.mem_iUnion] at h
    obtain ⟨v, hv⟩ := h
    by_cases hgood : highVector n v
    · simp only [hgood, if_true] at hv
      have hpref : externalLabelPrefix labels (externalLabelCount n) =
          vectorLabels v := by
        unfold externalLabelPrefix vectorLabels
        apply congrArg List.ofFn
        funext i
        exact congrArg Subtype.val (hv i)
      rw [← externalOriginLocalTime_labelPrefix labels n, hpref]
      exact hgood
    · simp [hgood] at hv
  · intro h
    change externalThreshold n ≤
      (localTime (externalWalk labels) n (0, 0) : ℝ) at h
    simp only [selectedLabelEvent, Set.mem_iUnion]
    let v : Fin (externalLabelCount n) → ExternalPairLabel :=
      fun i ↦ labels i
    refine ⟨v, ?_⟩
    have hgood : highVector n v := by
      rw [highVector, show vectorLabels v =
        externalLabelPrefix labels (externalLabelCount n) by rfl,
        externalOriginLocalTime_labelPrefix]
      exact h
    simp [hgood, externalPrefixCell, v]

theorem selectedLabelEvent_returnVector (n : ℕ) :
    selectedLabelEvent (returnVector n) =
      {labels | externalWalk labels n = (0, 0)} := by
  classical
  ext labels
  constructor
  · intro h
    change externalWalk labels n = (0, 0)
    simp only [selectedLabelEvent, Set.mem_iUnion] at h
    obtain ⟨v, hv⟩ := h
    by_cases hgood : returnVector n v
    · simp only [hgood, if_true] at hv
      have hpref : externalLabelPrefix labels (externalLabelCount n) =
          vectorLabels v := by
        unfold externalLabelPrefix vectorLabels
        apply congrArg List.ofFn
        funext i
        exact congrArg Subtype.val (hv i)
      rw [← externalReturn_labelPrefix labels n, hpref]
      exact hgood
    · simp [hgood] at hv
  · intro h
    change externalWalk labels n = (0, 0) at h
    simp only [selectedLabelEvent, Set.mem_iUnion]
    let v : Fin (externalLabelCount n) → ExternalPairLabel :=
      fun i ↦ labels i
    refine ⟨v, ?_⟩
    have hgood : returnVector n v := by
      rw [returnVector, show vectorLabels v =
        externalLabelPrefix labels (externalLabelCount n) by rfl,
        externalReturn_labelPrefix]
      exact h
    simp [hgood, externalPrefixCell, v]

private theorem vector_of_nondistinguished_list
    {L : ℕ} (l : List IncrementPair) (hlen : l.length = L)
    (hnondist : ∀ p ∈ l, p ≠ distinguishedIncrementPair) :
    ∃ v : Fin L → ExternalPairLabel, vectorLabels v = l := by
  let v : Fin L → ExternalPairLabel := fun i ↦
    let hi : i.val < l.length := by simpa [hlen] using i.isLt
    ⟨l[i]'hi, by
      apply hnondist
      exact List.getElem_mem hi⟩
  refine ⟨v, ?_⟩
  apply List.ext_getElem
  · simp [vectorLabels, hlen]
  · intro i hi₁ hi₂
    simp [vectorLabels, v]

theorem selectedOriginalEvent_highVector (n : ℕ) :
    selectedOriginalEvent (highVector n) = externalChainUpperBad n := by
  classical
  ext ω
  constructor
  · intro h
    simp only [selectedOriginalEvent, Set.mem_iUnion] at h
    obtain ⟨v, hv⟩ := h
    by_cases hgood : highVector n v
    · simp only [hgood, if_true] at hv
      rw [externalChainUpperBad]
      simp only [Set.mem_iUnion]
      refine ⟨vectorLabels v, ?_⟩
      rw [if_pos]
      · exact hv
      · exact ⟨vectorLabels_length v,
          vectorLabels_nondistinguished v, hgood⟩
    · simp [hgood] at hv
  · intro h
    rw [externalChainUpperBad] at h
    simp only [Set.mem_iUnion] at h
    obtain ⟨l, hl⟩ := h
    split_ifs at hl with hcond
    · obtain ⟨v, rfl⟩ := vector_of_nondistinguished_list l hcond.1 hcond.2.1
      simp only [selectedOriginalEvent, Set.mem_iUnion]
      refine ⟨v, ?_⟩
      have hgood : highVector n v := hcond.2.2
      simpa [hgood] using hl
    · simp at hl

theorem selectedOriginalEvent_returnVector (n : ℕ) :
    selectedOriginalEvent (returnVector n) = externalChainReturnAt n := by
  classical
  ext ω
  constructor
  · intro h
    simp only [selectedOriginalEvent, Set.mem_iUnion] at h
    obtain ⟨v, hv⟩ := h
    by_cases hgood : returnVector n v
    · simp only [hgood, if_true] at hv
      rw [externalChainReturnAt]
      simp only [Set.mem_iUnion]
      refine ⟨vectorLabels v, ?_⟩
      rw [if_pos]
      · exact hv
      · exact ⟨vectorLabels_length v,
          vectorLabels_nondistinguished v, hgood⟩
    · simp [hgood] at hv
  · intro h
    rw [externalChainReturnAt] at h
    simp only [Set.mem_iUnion] at h
    obtain ⟨l, hl⟩ := h
    split_ifs at hl with hcond
    · obtain ⟨v, rfl⟩ := vector_of_nondistinguished_list l hcond.1 hcond.2.1
      simp only [selectedOriginalEvent, Set.mem_iUnion]
      refine ⟨v, ?_⟩
      have hgood : returnVector n v := hcond.2.2
      simpa [hgood] using hl
    · simp at hl

/-- Exact law bridge for the one-origin external-local-time event used in
HLOZ Lemma 2.5 and Proposition 4.4. -/
theorem externalPathLaw_highLocalTime_eq_externalChainUpperBad (n : ℕ) :
    externalPathLaw {s | externalThreshold n ≤
        (localTime s n (0, 0) : ℝ)} =
      incrementLaw (externalChainUpperBad n) := by
  rw [externalPathLaw, Measure.map_apply measurable_externalWalk]
  · change externalLabelLaw
      {labels | externalThreshold n ≤
        (localTime (externalWalk labels) n (0, 0) : ℝ)} = _
    rw [← selectedLabelEvent_highVector,
      measure_selected_events_eq, selectedOriginalEvent_highVector]
  · exact measurableSet_le measurable_const
      ((measurable_of_countable fun k : ℕ ↦ (k : ℝ)).comp
        (measurable_localTime_eval n (0, 0)))

/-- Exact law bridge for the return event and hence for the external Green
function. -/
theorem externalPathLaw_return_eq_externalChainReturnAt (n : ℕ) :
    externalPathLaw {s | s n = (0, 0)} =
      incrementLaw (externalChainReturnAt n) := by
  rw [externalPathLaw, Measure.map_apply measurable_externalWalk]
  · change externalLabelLaw
      {labels | externalWalk labels n = (0, 0)} = _
    rw [← selectedLabelEvent_returnVector,
      measure_selected_events_eq, selectedOriginalEvent_returnVector]
  · exact measurableSet_eq_fun (measurable_pi_apply n) measurable_const

end Erdos1166.HLOZExternalChain
