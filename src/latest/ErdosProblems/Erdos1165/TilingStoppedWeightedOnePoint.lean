/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.ExternalStoppedWeightedOnePoint
import ErdosProblems.Erdos1165.HLOZTilingGapRandomClockScreen
import ErdosProblems.Erdos1165.TilingSpatialInsertionFiber
import ErdosProblems.Erdos1165.TilingExternalPhaseSplit

/-!
# Weighted one-site transport for all six domino tilings

State-dependent deletion has the same retained endpoint law as the canonical
deleted walk.  The proof does not use a lattice symmetry: at each spatial
base it swaps the unique removable zero-displacement block with the canonical
removable zero-displacement block.  This is an involution on finite raw block
words and preserves every block endpoint.

For arbitrary ordinary-time prefixes there is one unavoidable boundary
effect: an incomplete final block may later be deleted.  We therefore expose
the exact completed-pair cap and the sharp one-unit local-time loss needed by
the random-clock screen.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.TilingStoppedWeightedOnePoint

open LazyDecomposition PathInsertion TilingLazyDecomposition
open TilingSpatialInsertionFiber ExternalWalk ExternalOnePoint ExternalCountTransport
open ExternalWeightedOnePoint ExternalWeightedOnePointCanonical
open ExternalStoppedWeightedOnePoint ExternalProposition44 ExternalHLOZOnePoint
open ExternalGreenRenewal
open ExternalThickCount HLOZGapRandomClockScreen HLOZTilingGapRandomClockScreen
open ShiftedPrefixBridge SpatialInsertionFiber
open TilingExternalPhaseSplit
open StoppedInsertion

noncomputable section

attribute [local instance] Classical.propDecidable

abbrev DominoTiling := Tilings.Tiling

/-! ## Endpoint-preserving normalization of stateful deletion -/

/-- At a spatial base, exchange the tiling-removable return block with the
canonical even-phase removable return block. -/
def normalizeTilingBlock (t : DominoTiling) (x : Point) :
    PathInsertion.Block ≃ PathInsertion.Block :=
  Equiv.swap (tilingRemovableBlock t x) (PathInsertion.removableBlock .even)

@[simp] lemma normalizeTilingBlock_removable (t : DominoTiling) (x : Point) :
    normalizeTilingBlock t x (tilingRemovableBlock t x) =
      PathInsertion.removableBlock .even := by
  exact Equiv.swap_apply_left _ _

@[simp] lemma normalizeTilingBlock_involutive (t : DominoTiling)
    (x : Point) (b : PathInsertion.Block) :
    normalizeTilingBlock t x (normalizeTilingBlock t x b) = b := by
  exact Equiv.swap_apply_self _ _ _

lemma normalizeTilingBlock_eq_removable_iff (t : DominoTiling)
    (x : Point) (b : PathInsertion.Block) :
    normalizeTilingBlock t x b = PathInsertion.removableBlock .even ↔
      b = tilingRemovableBlock t x := by
  change (Equiv.swap (tilingRemovableBlock t x)
      (PathInsertion.removableBlock .even)) b =
      PathInsertion.removableBlock .even ↔ b = tilingRemovableBlock t x
  rw [Equiv.swap_apply_eq_iff]
  simp only [Equiv.swap_apply_right]

lemma blockEnd_normalizeTilingBlock (t : DominoTiling)
    (x : Point) (b : PathInsertion.Block) :
    PathInsertion.blockEnd x (normalizeTilingBlock t x b) =
      PathInsertion.blockEnd x b := by
  by_cases hb : b = tilingRemovableBlock t x
  · subst b
    rw [normalizeTilingBlock_removable, blockEnd_removableBlock,
      blockEnd_tilingRemovableBlock]
  · by_cases hc : b = PathInsertion.removableBlock .even
    · subst b
      simp only [normalizeTilingBlock, Equiv.swap_apply_right,
        blockEnd_tilingRemovableBlock, blockEnd_removableBlock]
    · rw [show normalizeTilingBlock t x b = b by
        exact Equiv.swap_apply_of_ne_of_ne hb hc]

/-- Stateful normalization of a fixed finite raw block word. -/
def normalizeTilingWord (t : DominoTiling) :
    (a : ℕ) → Point → (Fin a → PathInsertion.Block) →
      Fin a → PathInsertion.Block
  | 0, _, _ => Fin.elim0
  | a + 1, x, u =>
      Fin.cases (normalizeTilingBlock t x (u 0))
        (normalizeTilingWord t a (PathInsertion.blockEnd x (u 0))
          (fun j ↦ u j.succ))

@[simp] lemma normalizeTilingWord_zero (t : DominoTiling) (x : Point)
    (u : Fin 0 → PathInsertion.Block) :
    normalizeTilingWord t 0 x u = u := by
  funext j
  exact Fin.elim0 j

@[simp] lemma normalizeTilingWord_succ_zero (t : DominoTiling) (x : Point)
    {a : ℕ} (u : Fin (a + 1) → PathInsertion.Block) :
    normalizeTilingWord t (a + 1) x u 0 = normalizeTilingBlock t x (u 0) := rfl

@[simp] lemma normalizeTilingWord_succ (t : DominoTiling) (x : Point)
    {a : ℕ} (u : Fin (a + 1) → PathInsertion.Block) (j : Fin a) :
    normalizeTilingWord t (a + 1) x u j.succ =
      normalizeTilingWord t a (PathInsertion.blockEnd x (u 0))
        (fun k ↦ u k.succ) j := rfl

theorem normalizeTilingWord_involutive (t : DominoTiling) :
    ∀ (a : ℕ) (x : Point) (u : Fin a → PathInsertion.Block),
      normalizeTilingWord t a x (normalizeTilingWord t a x u) = u := by
  intro a
  induction a with
  | zero =>
      intro x u
      funext j
      exact Fin.elim0 j
  | succ a ih =>
      intro x u
      funext j
      refine Fin.cases ?_ (fun k ↦ ?_) j
      · simp only [normalizeTilingWord_succ_zero,
          normalizeTilingBlock_involutive]
      · change normalizeTilingWord t a
            (PathInsertion.blockEnd x (normalizeTilingBlock t x (u 0)))
            (normalizeTilingWord t a (PathInsertion.blockEnd x (u 0))
              (fun k ↦ u k.succ)) k = u k.succ
        rw [blockEnd_normalizeTilingBlock]
        exact congrFun (ih (PathInsertion.blockEnd x (u 0))
          (fun k ↦ u k.succ)) k

/-- The normalization is a genuine permutation of all `16^a` raw words. -/
def normalizeTilingWordEquiv (t : DominoTiling) (a : ℕ) (x : Point) :
    (Fin a → PathInsertion.Block) ≃ (Fin a → PathInsertion.Block) where
  toFun := normalizeTilingWord t a x
  invFun := normalizeTilingWord t a x
  left_inv := normalizeTilingWord_involutive t a x
  right_inv := normalizeTilingWord_involutive t a x

lemma blockEndpointPath_delete_normalize (t : DominoTiling) :
    ∀ (a : ℕ) (x : Point) (u : Fin a → PathInsertion.Block),
      blockEndpointPath x
          (deleteRemovableBlocks .even
            (List.ofFn (normalizeTilingWord t a x u))) =
        blockEndpointPath x (deleteTilingBlocks t x (List.ofFn u)) := by
  intro a
  induction a with
  | zero =>
      intro x u
      simp [normalizeTilingWord, deleteRemovableBlocks, deleteTilingBlocks]
  | succ a ih =>
      intro x u
      rw [List.ofFn_succ, List.ofFn_succ]
      by_cases hb : u 0 = tilingRemovableBlock t x
      · have hnorm : normalizeTilingBlock t x (u 0) =
            PathInsertion.removableBlock .even :=
          (normalizeTilingBlock_eq_removable_iff t x (u 0)).2 hb
        simpa [normalizeTilingWord, deleteRemovableBlocks,
          deleteTilingBlocks, hb, hnorm] using ih x (fun j ↦ u j.succ)
      · have hnorm : normalizeTilingBlock t x (u 0) ≠
            PathInsertion.removableBlock .even :=
          (normalizeTilingBlock_eq_removable_iff t x (u 0)).not.mpr hb
        simpa [normalizeTilingWord, deleteRemovableBlocks,
          deleteTilingBlocks, hb, hnorm, blockEnd_normalizeTilingBlock] using
          congrArg (List.cons x)
            (ih (PathInsertion.blockEnd x (u 0)) (fun j ↦ u j.succ))

/-! ## Exact finite uniform transport -/

def tilingDeletedMemberProperty (t : DominoTiling) (start x : Point)
    {a : ℕ} (u : Fin a → PathInsertion.Block) : Prop :=
  x ∈ (blockEndpointPath start
    (deleteTilingBlocks t start (List.ofFn u))).toFinset

def tilingDeletedCandidateProperty (t : DominoTiling) (start x : Point)
    (k : ℕ) {a : ℕ} (u : Fin a → PathInsertion.Block) : Prop :=
  tilingDeletedMemberProperty t start x u ∧
    k ≤ listLocalTime
      (blockEndpointPath start (deleteTilingBlocks t start (List.ofFn u))) x

def canonicalDeletedMemberProperty (start x : Point)
    {a : ℕ} (u : Fin a → PathInsertion.Block) : Prop :=
  x ∈ (blockEndpointPath start
    (deleteRemovableBlocks .even (List.ofFn u))).toFinset

def canonicalDeletedCandidateProperty (start x : Point) (k : ℕ)
    {a : ℕ} (u : Fin a → PathInsertion.Block) : Prop :=
  canonicalDeletedMemberProperty start x u ∧
    k ≤ listLocalTime
      (blockEndpointPath start (deleteRemovableBlocks .even (List.ofFn u))) x

lemma tilingDeletedMember_normalize_iff (t : DominoTiling) (start x : Point)
    {a : ℕ} (u : Fin a → PathInsertion.Block) :
    tilingDeletedMemberProperty t start x u ↔
      canonicalDeletedMemberProperty start x
        (normalizeTilingWord t a start u) := by
  unfold tilingDeletedMemberProperty canonicalDeletedMemberProperty
  rw [blockEndpointPath_delete_normalize]

lemma tilingDeletedCandidate_normalize_iff (t : DominoTiling)
    (start x : Point) (k : ℕ) {a : ℕ}
    (u : Fin a → PathInsertion.Block) :
    tilingDeletedCandidateProperty t start x k u ↔
      canonicalDeletedCandidateProperty start x k
        (normalizeTilingWord t a start u) := by
  unfold tilingDeletedCandidateProperty canonicalDeletedCandidateProperty
  rw [← tilingDeletedMember_normalize_iff]
  rw [blockEndpointPath_delete_normalize]

def finiteBlockPropertyFinset (a : ℕ)
    (P : (Fin a → PathInsertion.Block) → Prop) :
    Finset (Fin a → PathInsertion.Block) :=
  Finset.univ.filter P

lemma card_finiteBlockPropertyFinset (a : ℕ)
    (P : (Fin a → PathInsertion.Block) → Prop) :
    (finiteBlockPropertyFinset a P).card = Fintype.card {u // P u} := by
  calc
    (finiteBlockPropertyFinset a P).card =
        Nat.card ↥(finiteBlockPropertyFinset a P) :=
      (Nat.card_eq_finsetCard _).symm
    _ = Nat.card {u // P u} :=
      Nat.card_congr (filterUnivSubtypeEquiv P)
    _ = Fintype.card {u // P u} := Nat.card_eq_fintype_card

theorem fairSteps_pairedSegment_property_mass (start a : ℕ)
    (P : (Fin a → PathInsertion.Block) → Prop) :
    fairSteps {omega | P (pairedSegment start a omega)} =
      (Fintype.card {u // P u} : ℝ≥0∞) / 16 ^ a := by
  let G := finiteBlockPropertyFinset a P
  have hG : MeasurableSet (G : Set (Fin a → PathInsertion.Block)) := by
    measurability
  calc
    fairSteps {omega | P (pairedSegment start a omega)} =
        (fairSteps.map (pairedSegment start a)) G := by
      rw [Measure.map_apply (measurable_pairedSegment start a) hG]
      congr 1
      ext omega
      simp [G, finiteBlockPropertyFinset]
    _ = ProbabilityTheory.uniformOn
        (Set.univ : Set (Fin a → PathInsertion.Block)) G := by
      rw [fairSteps_map_pairedSegment]
    _ = (G.card : ℝ≥0∞) / 16 ^ a := by
      rw [ProbabilityTheory.uniformOn_univ, Measure.count_apply_finset]
      congr 2
      simp
    _ = _ := by rw [card_finiteBlockPropertyFinset]

lemma card_tilingDeletedMember_eq_canonical (t : DominoTiling)
    (start x : Point) (a : ℕ) :
    Fintype.card {u : Fin a → PathInsertion.Block //
        tilingDeletedMemberProperty t start x u} =
      Fintype.card {u : Fin a → PathInsertion.Block //
        canonicalDeletedMemberProperty start x u} := by
  exact Fintype.card_congr
    ((normalizeTilingWordEquiv t a start).subtypeEquiv
      (tilingDeletedMember_normalize_iff t start x))

lemma card_tilingDeletedCandidate_eq_canonical (t : DominoTiling)
    (start x : Point) (k a : ℕ) :
    Fintype.card {u : Fin a → PathInsertion.Block //
        tilingDeletedCandidateProperty t start x k u} =
      Fintype.card {u : Fin a → PathInsertion.Block //
        canonicalDeletedCandidateProperty start x k u} := by
  exact Fintype.card_congr
    ((normalizeTilingWordEquiv t a start).subtypeEquiv
      (tilingDeletedCandidate_normalize_iff t start x k))

theorem fairSteps_tilingDeletedMember_eq_canonical (t : DominoTiling)
    (start x : Point) (pairStart a : ℕ) :
    fairSteps {omega |
        tilingDeletedMemberProperty t start x (pairedSegment pairStart a omega)} =
      fairSteps {omega |
        canonicalDeletedMemberProperty start x (pairedSegment pairStart a omega)} := by
  rw [fairSteps_pairedSegment_property_mass,
    fairSteps_pairedSegment_property_mass,
    card_tilingDeletedMember_eq_canonical]

theorem fairSteps_tilingDeletedCandidate_eq_canonical (t : DominoTiling)
    (start x : Point) (pairStart a k : ℕ) :
    fairSteps {omega | tilingDeletedCandidateProperty t start x k
        (pairedSegment pairStart a omega)} =
      fairSteps {omega | canonicalDeletedCandidateProperty start x k
        (pairedSegment pairStart a omega)} := by
  rw [fairSteps_pairedSegment_property_mass,
    fairSteps_pairedSegment_property_mass,
    card_tilingDeletedCandidate_eq_canonical]

lemma canonicalDeletedMember_iff_hasGood (start x : Point)
    {a : ℕ} (u : Fin a → PathInsertion.Block) :
    canonicalDeletedMemberProperty start x u ↔
      HasGoodExtracted .even
        (retainedMemberProperty .even (x - start)) u := by
  rw [hasGoodExtracted_retainedMember_iff]
  unfold canonicalDeletedMemberProperty
  simp only [List.mem_toFinset]
  exact mem_blockEndpointPath_translate_iff start x _

lemma canonicalDeletedCandidate_iff_hasGood (start x : Point) (k : ℕ)
    {a : ℕ} (u : Fin a → PathInsertion.Block) :
    canonicalDeletedCandidateProperty start x k u ↔
      HasGoodExtracted .even
        (retainedCandidateProperty .even (x - start) k) u := by
  rw [hasGoodExtracted_retainedCandidate_iff]
  unfold canonicalDeletedCandidateProperty canonicalDeletedMemberProperty
  simp only [List.mem_toFinset]
  rw [mem_blockEndpointPath_translate_iff,
    listLocalTime_blockEndpointPath_translate]

theorem fairSteps_canonicalDeleted_weighted_oneSite
    (start x : Point) (pairStart a N k : ℕ) (q : ℝ≥0∞)
    (haN : a ≤ N)
    (hone : externalBlocks .even {eta |
      k ≤ externalOriginLocalTime .even eta N} ≤ q) :
    fairSteps {omega | canonicalDeletedCandidateProperty start x k
        (pairedSegment pairStart a omega)} ≤
      q * fairSteps {omega | canonicalDeletedMemberProperty start x
        (pairedSegment pairStart a omega)} := by
  rw [show {omega | canonicalDeletedCandidateProperty start x k
        (pairedSegment pairStart a omega)} =
      {omega | HasGoodExtracted .even
        (retainedCandidateProperty .even (x - start) k)
          (pairedSegment pairStart a omega)} by
      ext omega
      exact canonicalDeletedCandidate_iff_hasGood start x k _]
  rw [show {omega | canonicalDeletedMemberProperty start x
        (pairedSegment pairStart a omega)} =
      {omega | HasGoodExtracted .even
        (retainedMemberProperty .even (x - start))
          (pairedSegment pairStart a omega)} by
      ext omega
      exact canonicalDeletedMember_iff_hasGood start x _]
  exact fairSteps_pairedSegment_weighted .even (x - start)
    pairStart a N k q haN hone

theorem fairSteps_tilingDeleted_weighted_oneSite (t : DominoTiling)
    (start x : Point) (pairStart a N k : ℕ) (q : ℝ≥0∞)
    (haN : a ≤ N)
    (hone : externalBlocks .even {eta |
      k ≤ externalOriginLocalTime .even eta N} ≤ q) :
    fairSteps {omega | tilingDeletedCandidateProperty t start x k
        (pairedSegment pairStart a omega)} ≤
      q * fairSteps {omega | tilingDeletedMemberProperty t start x
        (pairedSegment pairStart a omega)} := by
  rw [fairSteps_tilingDeletedCandidate_eq_canonical,
    fairSteps_tilingDeletedMember_eq_canonical]
  exact fairSteps_canonicalDeleted_weighted_oneSite start x pairStart
    a N k q haN hone

/-! ## Exact endpoint phase of an ordinary-time prefix -/

theorem phasedExternalEndpointPath_even (t : DominoTiling)
    (omega : StepPath) (n : ℕ) :
    phasedExternalVertexPath t .even .endpoint
        (finitePathList (pathPrefix (trajectory omega) n)) =
      blockEndpointPath (0, 0)
        (deleteTilingBlocks t (0, 0)
          (List.ofFn (pairedSegment 0 (n / 2) omega))) := by
  unfold phasedExternalVertexPath tilingExternalPhasePath phaseVertices
  rw [tilingExternalPath_even_prefix_blocks]
  rw [list_ofFn_pairedSegment_zero]
  unfold prefixRemainder
  by_cases hmod : n % 2 = 0
  · simp only [hmod, if_pos, List.append_nil]
    exact endpointPhaseVertices_blockPath _ _
  · simp only [hmod, if_false]
    exact endpointPhaseVertices_blockPath_append_singleton _ _ _

theorem phasedExternalEndpointPath_shifted (t : DominoTiling)
    (omega : StepPath) (n : ℕ) (hn : 0 < n) :
    phasedExternalVertexPath t .shifted .endpoint
        (finitePathList (pathPrefix (trajectory omega) n)) =
      blockEndpointPath (trajectory omega 1)
        (deleteTilingBlocks t (trajectory omega 1)
          (List.ofFn (pairedSegment 1 ((n - 1) / 2) omega))) := by
  unfold phasedExternalVertexPath tilingExternalPhasePath phaseVertices
  rw [tilingExternalPath_shifted_prefix_blocks t omega n hn]
  rw [list_ofFn_pairedSegment_one]
  unfold shiftedPrefixRemainder segmentRemainder
  by_cases hmod : (n - 1) % 2 = 0
  · simp only [hmod, if_pos, List.append_nil]
    exact endpointPhaseVertices_blockPath _ _
  · simp only [hmod, if_false]
    exact endpointPhaseVertices_blockPath_append_singleton _ _ _

theorem phasedExternalEndpointPath_shifted_zero (t : DominoTiling)
    (omega : StepPath) :
    phasedExternalVertexPath t .shifted .endpoint
        (finitePathList (pathPrefix (trajectory omega) 0)) = [] := by
  rfl

theorem phasedExternalEndpointLocalTime_even (t : DominoTiling)
    (omega : StepPath) (n : ℕ) (x : Point) :
    phasedExternalVertexLocalTime t .even .endpoint
        (finitePathList (pathPrefix (trajectory omega) n)) x =
      listLocalTime
        (blockEndpointPath (0, 0)
          (deleteTilingBlocks t (0, 0)
            (List.ofFn (pairedSegment 0 (n / 2) omega)))) x := by
  exact congrArg (fun p : List Point ↦ listLocalTime p x)
    (phasedExternalEndpointPath_even t omega n)

theorem phasedExternalEndpointLocalTime_shifted (t : DominoTiling)
    (omega : StepPath) (n : ℕ) (hn : 0 < n) (x : Point) :
    phasedExternalVertexLocalTime t .shifted .endpoint
        (finitePathList (pathPrefix (trajectory omega) n)) x =
      listLocalTime
        (blockEndpointPath (trajectory omega 1)
          (deleteTilingBlocks t (trajectory omega 1)
            (List.ofFn (pairedSegment 1 ((n - 1) / 2) omega)))) x := by
  exact congrArg (fun p : List Point ↦ listLocalTime p x)
    (phasedExternalEndpointPath_shifted t omega n hn)

theorem phasedExternalEndpointVisited_even (t : DominoTiling)
    (omega : StepPath) (n : ℕ) :
    phasedExternalVertexVisitedSites t .even .endpoint
        (finitePathList (pathPrefix (trajectory omega) n)) =
      (blockEndpointPath (0, 0)
        (deleteTilingBlocks t (0, 0)
          (List.ofFn (pairedSegment 0 (n / 2) omega)))).toFinset := by
  exact congrArg List.toFinset (phasedExternalEndpointPath_even t omega n)

theorem phasedExternalEndpointVisited_shifted (t : DominoTiling)
    (omega : StepPath) (n : ℕ) (hn : 0 < n) :
    phasedExternalVertexVisitedSites t .shifted .endpoint
        (finitePathList (pathPrefix (trajectory omega) n)) =
      (blockEndpointPath (trajectory omega 1)
        (deleteTilingBlocks t (trajectory omega 1)
          (List.ofFn (pairedSegment 1 ((n - 1) / 2) omega)))).toFinset := by
  exact congrArg List.toFinset
    (phasedExternalEndpointPath_shifted t omega n hn)

/-! ## Deterministic prefix/future factorization -/

lemma indepFun_stepPrefix_pairedSegment (start a : ℕ) :
    IndepFun (stepPrefix start) (pairedSegment start a) fairSteps := by
  let pair : (Fin (2 * a) → Direction) →
      Fin a → PathInsertion.Block := fun u j ↦
    (u ⟨2 * (j : ℕ), by omega⟩, u ⟨2 * (j : ℕ) + 1, by omega⟩)
  have h := (indepFun_stepPrefix_stepBlock start (2 * a)).comp
    (measurable_id : Measurable (id : (Fin start → Direction) → _))
    (measurable_of_countable pair)
  convert h using 1
  · rfl
  · funext omega j
    rfl

lemma fairSteps_prefix_inter_pairedSegment_property
    (start a : ℕ) (A : Set StepPath)
    (hA : MeasurableSet[incrementFiltration start] A)
    (P : (Fin a → PathInsertion.Block) → Prop) :
    fairSteps (A ∩ {omega | P (pairedSegment start a omega)}) =
      fairSteps A * fairSteps {omega | P (pairedSegment start a omega)} := by
  rw [incrementFiltration_apply] at hA
  obtain ⟨S, hS, hAeq⟩ := hA
  let C : Set (Fin a → PathInsertion.Block) := {u | P u}
  have h := (indepFun_stepPrefix_pairedSegment start a).measure_inter_preimage_eq_mul
    S C hS (Set.to_countable C).measurableSet
  simpa only [hAeq, C, Set.preimage_ofPred_eq] using h

def tilingEndpointTailLarge (t : DominoTiling) (x : Point)
    (N k : ℕ) (u : Fin N → PathInsertion.Block) : Prop :=
  k ≤ listLocalTime
    (blockEndpointPath x (deleteTilingBlocks t x (List.ofFn u))) x

lemma tilingDeletedMember_self (t : DominoTiling) (x : Point)
    {a : ℕ} (u : Fin a → PathInsertion.Block) :
    tilingDeletedMemberProperty t x x u := by
  unfold tilingDeletedMemberProperty
  cases deleteTilingBlocks t x (List.ofFn u) <;> simp [blockEndpointPath]

theorem fairSteps_tilingEndpointTailLarge_le (t : DominoTiling)
    (x : Point) (pairStart N k : ℕ) (q : ℝ≥0∞)
    (hone : externalBlocks .even {eta |
      k ≤ externalOriginLocalTime .even eta N} ≤ q) :
    fairSteps {omega |
        tilingEndpointTailLarge t x N k
          (pairedSegment pairStart N omega)} ≤ q := by
  have h := fairSteps_tilingDeleted_weighted_oneSite t x x pairStart
    N N k q le_rfl hone
  have hmember : {omega : StepPath |
      tilingDeletedMemberProperty t x x
        (pairedSegment pairStart N omega)} = Set.univ := by
    ext omega
    simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    exact tilingDeletedMember_self t x _
  have hcand : {omega : StepPath |
      tilingDeletedCandidateProperty t x x k
        (pairedSegment pairStart N omega)} =
      {omega | tilingEndpointTailLarge t x N k
        (pairedSegment pairStart N omega)} := by
    ext omega
    simp only [Set.mem_ofPred_eq, tilingDeletedCandidateProperty,
      tilingEndpointTailLarge, tilingDeletedMember_self, true_and]
  rw [hcand, hmember, measure_univ, mul_one] at h
  exact h

theorem fairSteps_prefix_inter_tilingEndpointTailLarge_le
    (t : DominoTiling) (x : Point) (start N k : ℕ)
    (q : ℝ≥0∞) (A : Set StepPath)
    (hA : MeasurableSet[incrementFiltration start] A)
    (hone : externalBlocks .even {eta |
      k ≤ externalOriginLocalTime .even eta N} ≤ q) :
    fairSteps (A ∩ {omega |
        tilingEndpointTailLarge t x N k
          (pairedSegment start N omega)}) ≤
      q * fairSteps A := by
  rw [fairSteps_prefix_inter_pairedSegment_property start N A hA]
  calc
    fairSteps A * fairSteps {omega |
        tilingEndpointTailLarge t x N k
          (pairedSegment start N omega)} ≤ fairSteps A * q := by
      gcongr
      exact fairSteps_tilingEndpointTailLarge_le t x start N k q hone
    _ = q * fairSteps A := mul_comm _ _

/-! ## Prefix/suffix algebra for stateful deletion -/

lemma pairedSegmentList_add (omega : StepPath) (start r a : ℕ) :
    List.ofFn (pairedSegment start (r + a) omega) =
      List.ofFn (pairedSegment start r omega) ++
        List.ofFn (pairedSegment (start + 2 * r) a omega) := by
  rw [← List.ofFn_fin_append]
  apply congrArg List.ofFn
  funext j
  refine Fin.addCases (m := r) (n := a) ?_ ?_ j
  · intro i
    simp [pairedSegment]
  · intro i
    rw [Fin.append_right]
    change
      (omega (start + 2 * (r + (i : ℕ))),
          omega (start + 2 * (r + (i : ℕ)) + 1)) =
        (omega (start + 2 * r + 2 * (i : ℕ)),
          omega (start + 2 * r + 2 * (i : ℕ) + 1))
    have hidx : start + 2 * (r + (i : ℕ)) =
        start + 2 * r + 2 * (i : ℕ) := by omega
    rw [hidx]

lemma followBlocks_deleteTilingBlocks (t : DominoTiling) (x : Point) :
    ∀ bs : List PathInsertion.Block,
      followBlocks x (deleteTilingBlocks t x bs) = followBlocks x bs := by
  intro bs
  induction bs generalizing x with
  | nil => rfl
  | cons b bs ih =>
      by_cases hb : b = tilingRemovableBlock t x
      · subst b
        simp only [deleteTilingBlocks, if_true,
          blockEnd_tilingRemovableBlock, followBlocks, List.foldl_cons]
        exact ih x
      · simp only [deleteTilingBlocks, hb, if_false, followBlocks,
          List.foldl_cons]
        exact ih (PathInsertion.blockEnd x b)

lemma deleteTilingBlocks_append (t : DominoTiling) (x : Point) :
    ∀ as bs : List PathInsertion.Block,
      deleteTilingBlocks t x (as ++ bs) =
        deleteTilingBlocks t x as ++
          deleteTilingBlocks t (followBlocks x as) bs := by
  intro as
  induction as generalizing x with
  | nil => simp [deleteTilingBlocks, followBlocks]
  | cons a as ih =>
      intro bs
      by_cases ha : a = tilingRemovableBlock t x
      · subst a
        simp only [List.cons_append, deleteTilingBlocks, if_true,
          blockEnd_tilingRemovableBlock]
        simpa [followBlocks] using ih x bs
      · simp only [List.cons_append, deleteTilingBlocks, ha, if_false,
          List.cons_append, followBlocks, List.foldl_cons]
        rw [ih]
        congr 1

lemma blockEndpointPath_append (x : Point) :
    ∀ as bs : List PathInsertion.Block,
      blockEndpointPath x (as ++ bs) =
        (blockEndpointPath x as).dropLast ++
          blockEndpointPath (followBlocks x as) bs := by
  intro as
  induction as generalizing x with
  | nil => simp [blockEndpointPath, followBlocks]
  | cons a as ih =>
      intro bs
      change x :: blockEndpointPath (PathInsertion.blockEnd x a) (as ++ bs) =
        (x :: blockEndpointPath (PathInsertion.blockEnd x a) as).dropLast ++
          blockEndpointPath
            (followBlocks (PathInsertion.blockEnd x a) as) bs
      rw [List.dropLast_cons_of_ne_nil]
      · rw [ih]
        rfl
      · cases as <;> simp [blockEndpointPath]

lemma tilingEndpointPath_append (t : DominoTiling) (x : Point)
    (as bs : List PathInsertion.Block) :
    blockEndpointPath x (deleteTilingBlocks t x (as ++ bs)) =
      (blockEndpointPath x (deleteTilingBlocks t x as)).dropLast ++
        blockEndpointPath (followBlocks x as)
          (deleteTilingBlocks t (followBlocks x as) bs) := by
  rw [deleteTilingBlocks_append, blockEndpointPath_append,
    followBlocks_deleteTilingBlocks]

/-! ## The first statefully retained endpoint -/

def tilingRawFirstAt (t : DominoTiling) (start x : Point)
    (pairStart r : ℕ) (omega : StepPath) : Prop :=
  tilingDeletedMemberProperty t start x (pairedSegment pairStart r omega) ∧
    ∀ j < r,
      ¬tilingDeletedMemberProperty t start x
        (pairedSegment pairStart j omega)

lemma pairedSegment_take (omega : StepPath) (pairStart : ℕ)
    {j r : ℕ} (hjr : j ≤ r) :
    pairedSegment pairStart j omega =
      Fin.take j hjr (pairedSegment pairStart r omega) := by
  funext i
  rfl

theorem exists_tilingRawFirstAt_of_member (t : DominoTiling)
    (start x : Point) (pairStart a : ℕ) (omega : StepPath)
    (hmember : tilingDeletedMemberProperty t start x
      (pairedSegment pairStart a omega)) :
    ∃ r ≤ a, tilingRawFirstAt t start x pairStart r omega := by
  let P : ℕ → Prop := fun r ↦ r ≤ a ∧
    tilingDeletedMemberProperty t start x (pairedSegment pairStart r omega)
  have hex : ∃ r, P r := ⟨a, le_rfl, hmember⟩
  let r := Nat.find hex
  have hr := Nat.find_spec hex
  refine ⟨r, hr.1, hr.2, ?_⟩
  intro j hj hmem
  exact Nat.find_min hex hj ⟨(Nat.le_of_lt hj).trans hr.1, hmem⟩

lemma tilingRawFirstAt_unique (t : DominoTiling) (start x : Point)
    (pairStart : ℕ) {r s : ℕ} {omega : StepPath}
    (hr : tilingRawFirstAt t start x pairStart r omega)
    (hs : tilingRawFirstAt t start x pairStart s omega) : r = s := by
  rcases lt_trichotomy r s with hrs | hrs | hrs
  · exact (hs.2 r hrs hr.1).elim
  · exact hrs
  · exact (hr.2 s hrs hs.1).elim

def pairedSegmentFromPrefix (pairStart r : ℕ)
    (u : Fin (pairStart + 2 * r) → Direction) :
    Fin r → PathInsertion.Block := fun j ↦
  (u ⟨pairStart + 2 * (j : ℕ), by omega⟩,
    u ⟨pairStart + 2 * (j : ℕ) + 1, by omega⟩)

lemma pairedSegmentFromPrefix_stepPrefix (pairStart r : ℕ)
    (omega : StepPath) :
    pairedSegmentFromPrefix pairStart r
        (stepPrefix (pairStart + 2 * r) omega) =
      pairedSegment pairStart r omega := by
  funext j
  rfl

theorem measurableSet_tilingRawFirstAt_filtration (t : DominoTiling)
    (start x : Point) (pairStart r : ℕ) :
    MeasurableSet[incrementFiltration (pairStart + 2 * r)]
      {omega | tilingRawFirstAt t start x pairStart r omega} := by
  let C : Set (Fin r → PathInsertion.Block) := {u |
    tilingDeletedMemberProperty t start x u ∧
      ∀ (j : ℕ) (hj : j < r),
        ¬tilingDeletedMemberProperty t start x
          (Fin.take j (Nat.le_of_lt hj) u)}
  have hC : MeasurableSet C := (Set.to_countable C).measurableSet
  have heq : {omega | tilingRawFirstAt t start x pairStart r omega} =
      stepPrefix (pairStart + 2 * r) ⁻¹'
        (pairedSegmentFromPrefix pairStart r ⁻¹' C) := by
    ext omega
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, C, tilingRawFirstAt]
    rw [pairedSegmentFromPrefix_stepPrefix]
    constructor
    · rintro ⟨hmem, hfirst⟩
      refine ⟨hmem, fun j hj ↦ ?_⟩
      rw [← pairedSegment_take omega pairStart (Nat.le_of_lt hj)]
      exact hfirst j hj
    · rintro ⟨hmem, hfirst⟩
      refine ⟨hmem, fun j hj ↦ ?_⟩
      rw [pairedSegment_take omega pairStart (Nat.le_of_lt hj)]
      exact hfirst j hj
  rw [heq, incrementFiltration_apply]
  exact ⟨_, (measurable_of_countable
    (pairedSegmentFromPrefix pairStart r)) hC, rfl⟩

lemma measurableSet_const_le_finiteStoppingTime
    {tau : StepPath → ℕ} (htau : IsFiniteStoppingTime tau) (n : ℕ) :
    MeasurableSet[incrementFiltration n] {omega | n ≤ tau omega} := by
  cases n with
  | zero =>
      have heq : {omega : StepPath | 0 ≤ tau omega} = Set.univ := by ext; simp
      rw [heq]
      exact MeasurableSet.univ
  | succ n =>
      have hle : MeasurableSet[incrementFiltration n]
          {omega | tau omega ≤ n} := by
        change IsStoppingTime incrementFiltration
          (fun omega ↦ (tau omega : WithTop ℕ)) at htau
        simpa using htau n
      have hle' : MeasurableSet[incrementFiltration (n + 1)]
          {omega | tau omega ≤ n} :=
        incrementFiltration.mono (Nat.le_succ n) _ hle
      have heq : {omega : StepPath | n + 1 ≤ tau omega} =
          {omega | tau omega ≤ n}ᶜ := by
        ext omega
        simp only [Set.mem_ofPred_eq, Set.mem_compl_iff]
        omega
      rw [heq]
      exact hle'.compl

def tilingFirstPiece (t : DominoTiling) (start x : Point)
    (pairStart r : ℕ) (tau : StepPath → ℕ) : Set StepPath :=
  {omega | tilingRawFirstAt t start x pairStart r omega} ∩
    {omega | pairStart + 2 * r ≤ tau omega}

theorem measurableSet_tilingFirstPiece (t : DominoTiling)
    (start x : Point) (pairStart r : ℕ) (tau : StepPath → ℕ)
    (htau : IsFiniteStoppingTime tau) :
    MeasurableSet[incrementFiltration (pairStart + 2 * r)]
      (tilingFirstPiece t start x pairStart r tau) :=
  (measurableSet_tilingRawFirstAt_filtration t start x pairStart r).inter
    (measurableSet_const_le_finiteStoppingTime htau (pairStart + 2 * r))

lemma tilingFirstPiece_pairwiseDisjoint (t : DominoTiling)
    (start x : Point) (pairStart : ℕ) (tau : StepPath → ℕ) :
    Pairwise fun r s ↦ Disjoint
      (tilingFirstPiece t start x pairStart r tau)
      (tilingFirstPiece t start x pairStart s tau) := by
  intro r s hrs
  rw [Set.disjoint_left]
  intro omega hr hs
  exact hrs (tilingRawFirstAt_unique t start x pairStart hr.1 hs.1)

def tilingRawEndpointPath (t : DominoTiling) (start : Point)
    (pairStart r : ℕ) (omega : StepPath) : List Point :=
  blockEndpointPath start
    (deleteTilingBlocks t start
      (List.ofFn (pairedSegment pairStart r omega)))

lemma tilingDeletedMemberProperty_iff_mem_rawEndpointPath
    (t : DominoTiling) (start x : Point) (pairStart r : ℕ)
    (omega : StepPath) :
    tilingDeletedMemberProperty t start x
        (pairedSegment pairStart r omega) ↔
      x ∈ tilingRawEndpointPath t start pairStart r omega := by
  simp [tilingDeletedMemberProperty, tilingRawEndpointPath]

lemma tilingRawEndpointPath_succ (t : DominoTiling) (start : Point)
    (pairStart r : ℕ) (omega : StepPath) :
    tilingRawEndpointPath t start pairStart (r + 1) omega =
        tilingRawEndpointPath t start pairStart r omega ∨
      tilingRawEndpointPath t start pairStart (r + 1) omega =
        tilingRawEndpointPath t start pairStart r omega ++
          [followBlocks start
            (List.ofFn (pairedSegment pairStart (r + 1) omega))] := by
  let bs := List.ofFn (pairedSegment pairStart r omega)
  let b := pairedSegment pairStart (r + 1) omega (Fin.last r)
  have hword : List.ofFn (pairedSegment pairStart (r + 1) omega) =
      bs ++ [b] := by
    simp only [bs, b, List.ofFn_succ_last]
    congr 1
  unfold tilingRawEndpointPath
  rw [hword, deleteTilingBlocks_append]
  by_cases hb : b = tilingRemovableBlock t (followBlocks start bs)
  · left
    simp [deleteTilingBlocks, hb, bs]
  · right
    simp only [deleteTilingBlocks, hb, if_false]
    rw [blockEndpointPath_append_singleton]
    rw [followBlocks_append, followBlocks_deleteTilingBlocks]
    simp [followBlocks, bs]

theorem tilingRawFirstAt_endpoint_spec (t : DominoTiling)
    (start x : Point) (pairStart r : ℕ) (omega : StepPath)
    (hfirst : tilingRawFirstAt t start x pairStart r omega) :
    followBlocks start (List.ofFn (pairedSegment pairStart r omega)) = x ∧
      listLocalTime
        (tilingRawEndpointPath t start pairStart r omega).dropLast x = 0 := by
  cases r with
  | zero =>
      have hx : start = x := by
        have hxs : x = start := by
          simpa [tilingRawEndpointPath, tilingDeletedMemberProperty,
            blockEndpointPath, deleteTilingBlocks] using hfirst.1
        exact hxs.symm
      subst x
      simp [tilingRawEndpointPath, listLocalTime,
        deleteTilingBlocks, followBlocks]
  | succ r =>
      have hprev : x ∉ tilingRawEndpointPath t start pairStart r omega := by
        simpa [tilingDeletedMemberProperty_iff_mem_rawEndpointPath] using
          hfirst.2 r (Nat.lt_succ_self r)
      have hcurrent : x ∈
          tilingRawEndpointPath t start pairStart (r + 1) omega := by
        simpa [tilingDeletedMemberProperty_iff_mem_rawEndpointPath] using hfirst.1
      rcases tilingRawEndpointPath_succ t start pairStart r omega with hsame | happ
      · rw [hsame] at hcurrent
        exact (hprev hcurrent).elim
      · have hxlast : followBlocks start
            (List.ofFn (pairedSegment pairStart (r + 1) omega)) = x := by
          rw [happ] at hcurrent
          have hxs : x = followBlocks start
              (List.ofFn (pairedSegment pairStart (r + 1) omega)) := by
            simpa [hprev] using hcurrent
          exact hxs.symm
        refine ⟨hxlast, ?_⟩
        rw [happ, List.dropLast_concat]
        unfold listLocalTime
        exact List.count_eq_zero.mpr hprev

lemma tilingRawEndpointPath_prefix (t : DominoTiling) (start : Point)
    (pairStart : ℕ) {r a : ℕ} (hra : r ≤ a) (omega : StepPath) :
    tilingRawEndpointPath t start pairStart r omega <+:
      tilingRawEndpointPath t start pairStart a omega := by
  have ha : a = r + (a - r) := (Nat.add_sub_of_le hra).symm
  rw [ha, tilingRawEndpointPath, tilingRawEndpointPath,
    pairedSegmentList_add]
  apply blockEndpointPath_prefix_of_prefix
  rw [deleteTilingBlocks_append]
  exact List.prefix_append _ _

lemma tilingDeletedMemberProperty_mono (t : DominoTiling)
    (start x : Point) (pairStart : ℕ) {r a : ℕ} (hra : r ≤ a)
    (omega : StepPath)
    (hmember : tilingDeletedMemberProperty t start x
      (pairedSegment pairStart r omega)) :
    tilingDeletedMemberProperty t start x
      (pairedSegment pairStart a omega) := by
  rw [tilingDeletedMemberProperty_iff_mem_rawEndpointPath] at hmember ⊢
  exact (tilingRawEndpointPath_prefix t start pairStart hra omega).mem hmember

theorem tilingRawFirstAt_tail_large (t : DominoTiling)
    (start x : Point) (pairStart r a N k : ℕ) (omega : StepPath)
    (hra : r ≤ a) (haN : a ≤ N)
    (hfirst : tilingRawFirstAt t start x pairStart r omega)
    (hlarge : k ≤ listLocalTime
      (tilingRawEndpointPath t start pairStart a omega) x) :
    tilingEndpointTailLarge t x N k
      (pairedSegment (pairStart + 2 * r) N omega) := by
  obtain ⟨hend, hbefore⟩ :=
    tilingRawFirstAt_endpoint_spec t start x pairStart r omega hfirst
  have ha : a = r + (a - r) := (Nat.add_sub_of_le hra).symm
  have hword : List.ofFn (pairedSegment pairStart a omega) =
      List.ofFn (pairedSegment pairStart r omega) ++
        List.ofFn (pairedSegment (pairStart + 2 * r) (a - r) omega) := by
    conv_lhs => rw [ha]
    exact pairedSegmentList_add omega pairStart r (a - r)
  have hpath : tilingRawEndpointPath t start pairStart a omega =
      (tilingRawEndpointPath t start pairStart r omega).dropLast ++
        tilingRawEndpointPath t x (pairStart + 2 * r) (a - r) omega := by
    unfold tilingRawEndpointPath
    rw [hword, tilingEndpointPath_append, hend]
  rw [hpath] at hlarge
  have hshort : k ≤ listLocalTime
      (tilingRawEndpointPath t x (pairStart + 2 * r) (a - r) omega) x := by
    unfold listLocalTime at hbefore hlarge ⊢
    rw [List.count_append, hbefore, zero_add] at hlarge
    exact hlarge
  have hsub : a - r ≤ N := (Nat.sub_le a r).trans haN
  have hprefix := tilingRawEndpointPath_prefix t x
    (pairStart + 2 * r) hsub omega
  unfold tilingEndpointTailLarge
  change k ≤ listLocalTime
    (tilingRawEndpointPath t x (pairStart + 2 * r) N omega) x
  exact hshort.trans (hprefix.count_le x)

/-! ## Stopped endpoint chain: even temporal phase -/

def evenStoppedTilingEndpointMember (t : DominoTiling)
    (tau : StepPath → ℕ) (x : Point) : Set StepPath :=
  {omega | tilingDeletedMemberProperty t (0, 0) x
    (pairedSegment 0 (tau omega / 2) omega)}

def evenStoppedTilingEndpointLarge (t : DominoTiling)
    (tau : StepPath → ℕ) (k : ℕ) (x : Point) : Set StepPath :=
  {omega | k ≤ listLocalTime
    (tilingRawEndpointPath t (0, 0) 0 (tau omega / 2) omega) x}

theorem iUnion_tilingFirstPiece_even (t : DominoTiling)
    (tau : StepPath → ℕ) (x : Point) :
    (⋃ r : ℕ, tilingFirstPiece t (0, 0) x 0 r tau) =
      evenStoppedTilingEndpointMember t tau x := by
  ext omega
  simp only [Set.mem_iUnion, tilingFirstPiece, Set.mem_inter_iff,
    Set.mem_ofPred_eq, evenStoppedTilingEndpointMember]
  constructor
  · rintro ⟨r, hfirst, hgate⟩
    apply tilingDeletedMemberProperty_mono t (0, 0) x 0
      (show r ≤ tau omega / 2 by omega) omega hfirst.1
  · intro hmember
    obtain ⟨r, hra, hfirst⟩ := exists_tilingRawFirstAt_of_member
      t (0, 0) x 0 (tau omega / 2) omega hmember
    exact ⟨r, hfirst, by omega⟩

theorem fairSteps_evenStoppedTilingEndpoint_weighted_oneSite
    (t : DominoTiling) (tau : StepPath → ℕ) (N k : ℕ) (q : ℝ≥0∞)
    (x : Point)
    (htau : IsFiniteStoppingTime tau)
    (hN : ∀ omega, tau omega / 2 ≤ N)
    (hlarge : MeasurableSet (evenStoppedTilingEndpointLarge t tau k x))
    (hone : externalBlocks .even {eta |
      k ≤ externalOriginLocalTime .even eta N} ≤ q) :
    fairSteps (evenStoppedTilingEndpointMember t tau x ∩
        evenStoppedTilingEndpointLarge t tau k x) ≤
      q * fairSteps (evenStoppedTilingEndpointMember t tau x) := by
  let piece : ℕ → Set StepPath :=
    fun r ↦ tilingFirstPiece t (0, 0) x 0 r tau
  have hpieceFiltration : ∀ r,
      MeasurableSet[incrementFiltration (2 * r)] (piece r) := fun r ↦ by
    dsimp only [piece]
    rw [← Nat.zero_add (2 * r)]
    exact measurableSet_tilingFirstPiece t (0, 0) x 0 r tau htau
  have hpieceMeas : ∀ r, MeasurableSet (piece r) := fun r ↦
    incrementFiltration.le (2 * r) _ (hpieceFiltration r)
  have hpieceDisjoint : Pairwise fun r s ↦ Disjoint (piece r) (piece s) := by
    simpa only [piece] using
      tilingFirstPiece_pairwiseDisjoint t (0, 0) x 0 tau
  have hpieceLarge : ∀ r, fairSteps
      (piece r ∩ evenStoppedTilingEndpointLarge t tau k x) ≤
        q * fairSteps (piece r) := by
    intro r
    let tail : Set StepPath := {omega |
      tilingEndpointTailLarge t x N k (pairedSegment (2 * r) N omega)}
    have hsubset : piece r ∩ evenStoppedTilingEndpointLarge t tau k x ⊆
        piece r ∩ tail := by
      rintro omega ⟨hpiece, hlargeOmega⟩
      refine ⟨hpiece, ?_⟩
      change omega ∈ tilingFirstPiece t (0, 0) x 0 r tau at hpiece
      have hra : r ≤ tau omega / 2 := by
        change tilingRawFirstAt t (0, 0) x 0 r omega ∧
          0 + 2 * r ≤ tau omega at hpiece
        omega
      change tilingEndpointTailLarge t x N k
        (pairedSegment (2 * r) N omega)
      simpa only [zero_add] using tilingRawFirstAt_tail_large t (0, 0) x 0 r
          (tau omega / 2) N k omega hra (hN omega) hpiece.1 hlargeOmega
    calc
      fairSteps (piece r ∩ evenStoppedTilingEndpointLarge t tau k x) ≤
          fairSteps (piece r ∩ tail) := measure_mono hsubset
      _ ≤ q * fairSteps (piece r) := by
        exact fairSteps_prefix_inter_tilingEndpointTailLarge_le
          t x (2 * r) N k q (piece r) (hpieceFiltration r) hone
  have hunion : (⋃ r, piece r) = evenStoppedTilingEndpointMember t tau x := by
    simpa only [piece] using iUnion_tilingFirstPiece_even t tau x
  have hinter : (⋃ r, piece r ∩ evenStoppedTilingEndpointLarge t tau k x) =
      evenStoppedTilingEndpointMember t tau x ∩
        evenStoppedTilingEndpointLarge t tau k x := by
    rw [← iUnion_inter, hunion]
  rw [← hinter, measure_iUnion
    (fun _ _ hrs ↦ (hpieceDisjoint hrs).mono inter_subset_left inter_subset_left)
    (fun r ↦ (hpieceMeas r).inter hlarge)]
  calc
    ∑' r, fairSteps (piece r ∩ evenStoppedTilingEndpointLarge t tau k x) ≤
        ∑' r, q * fairSteps (piece r) :=
      ENNReal.tsum_le_tsum hpieceLarge
    _ = q * ∑' r, fairSteps (piece r) := ENNReal.tsum_mul_left
    _ = q * fairSteps (evenStoppedTilingEndpointMember t tau x) := by
      rw [← measure_iUnion hpieceDisjoint hpieceMeas, hunion]

/-! ## Stopped endpoint chain: shifted temporal phase -/

def shiftedStoppedTilingEndpointMember (t : DominoTiling)
    (tau : StepPath → ℕ) (x : Point) : Set StepPath :=
  {omega | 0 < tau omega ∧
    tilingDeletedMemberProperty t (directionVector (omega 0)) x
      (pairedSegment 1 ((tau omega - 1) / 2) omega)}

def shiftedStoppedTilingEndpointLarge (t : DominoTiling)
    (tau : StepPath → ℕ) (k : ℕ) (x : Point) : Set StepPath :=
  {omega | 0 < tau omega ∧ k ≤ listLocalTime
    (tilingRawEndpointPath t (directionVector (omega 0)) 1
      ((tau omega - 1) / 2) omega) x}

def shiftedTilingFirstPiece (t : DominoTiling) (x : Point)
    (tau : StepPath → ℕ) (z : Direction × ℕ) : Set StepPath :=
  {omega | omega 0 = z.1} ∩
    tilingFirstPiece t (directionVector z.1) x 1 z.2 tau

lemma measurableSet_firstDirection_filtration (d : Direction) :
    MeasurableSet[incrementFiltration 1]
      {omega : StepPath | omega 0 = d} := by
  rw [incrementFiltration_apply]
  refine ⟨{u : Fin 1 → Direction | u 0 = d},
    (Set.to_countable _).measurableSet, ?_⟩
  ext omega
  simp [stepPrefix]

theorem measurableSet_shiftedTilingFirstPiece (t : DominoTiling)
    (x : Point) (tau : StepPath → ℕ) (htau : IsFiniteStoppingTime tau)
    (z : Direction × ℕ) :
    MeasurableSet[incrementFiltration (1 + 2 * z.2)]
      (shiftedTilingFirstPiece t x tau z) := by
  exact (incrementFiltration.mono (by omega) _
      (measurableSet_firstDirection_filtration z.1)).inter
    (measurableSet_tilingFirstPiece t (directionVector z.1) x 1 z.2 tau htau)

lemma shiftedTilingFirstPiece_pairwiseDisjoint (t : DominoTiling)
    (x : Point) (tau : StepPath → ℕ) :
    Pairwise fun z w ↦ Disjoint
      (shiftedTilingFirstPiece t x tau z)
      (shiftedTilingFirstPiece t x tau w) := by
  intro z w hzw
  rw [Set.disjoint_left]
  intro omega hz hw
  by_cases hd : z.1 = w.1
  · have hr : z.2 = w.2 := tilingRawFirstAt_unique t
        (directionVector z.1) x 1 hz.2.1 (hd ▸ hw.2.1)
    exact hzw (Prod.ext hd hr)
  · exact hd (hz.1.symm.trans hw.1)

theorem iUnion_shiftedTilingFirstPiece (t : DominoTiling)
    (tau : StepPath → ℕ) (x : Point) :
    (⋃ z : Direction × ℕ, shiftedTilingFirstPiece t x tau z) =
      shiftedStoppedTilingEndpointMember t tau x := by
  ext omega
  simp only [Set.mem_iUnion, shiftedTilingFirstPiece, Set.mem_inter_iff,
    Set.mem_ofPred_eq, shiftedStoppedTilingEndpointMember, tilingFirstPiece]
  constructor
  · rintro ⟨⟨d, r⟩, hd, hfirst, hgate⟩
    have htauPos : 0 < tau omega :=
      (show 0 < 1 + 2 * r by omega).trans_le hgate
    have hra : r ≤ (tau omega - 1) / 2 := by
      apply (Nat.le_div_iff_mul_le (by omega : 0 < 2)).2
      rw [mul_comm]
      exact (Nat.le_sub_one_iff_lt htauPos).2 (by omega)
    refine ⟨htauPos, ?_⟩
    rw [hd]
    apply tilingDeletedMemberProperty_mono t (directionVector d) x 1
      hra omega hfirst.1
  · rintro ⟨htauPos, hmember⟩
    let d := omega 0
    obtain ⟨r, hra, hfirst⟩ := exists_tilingRawFirstAt_of_member t
      (directionVector d) x 1 ((tau omega - 1) / 2) omega hmember
    have hmul : r * 2 ≤ tau omega - 1 :=
      (Nat.le_div_iff_mul_le (by omega : 0 < 2)).1 hra
    have hlt : 2 * r < tau omega :=
      (Nat.le_sub_one_iff_lt htauPos).1 (by simpa [mul_comm] using hmul)
    exact ⟨(d, r), rfl, hfirst, by omega⟩

theorem fairSteps_shiftedStoppedTilingEndpoint_weighted_oneSite
    (t : DominoTiling) (tau : StepPath → ℕ) (N k : ℕ) (q : ℝ≥0∞)
    (x : Point)
    (htau : IsFiniteStoppingTime tau)
    (hN : ∀ omega, (tau omega - 1) / 2 ≤ N)
    (hlarge : MeasurableSet (shiftedStoppedTilingEndpointLarge t tau k x))
    (hone : externalBlocks .even {eta |
      k ≤ externalOriginLocalTime .even eta N} ≤ q) :
    fairSteps (shiftedStoppedTilingEndpointMember t tau x ∩
        shiftedStoppedTilingEndpointLarge t tau k x) ≤
      q * fairSteps (shiftedStoppedTilingEndpointMember t tau x) := by
  let piece : Direction × ℕ → Set StepPath :=
    shiftedTilingFirstPiece t x tau
  have hpieceFiltration : ∀ z,
      MeasurableSet[incrementFiltration (1 + 2 * z.2)] (piece z) := fun z ↦ by
    exact measurableSet_shiftedTilingFirstPiece t x tau htau z
  have hpieceMeas : ∀ z, MeasurableSet (piece z) := fun z ↦
    incrementFiltration.le (1 + 2 * z.2) _ (hpieceFiltration z)
  have hpieceDisjoint : Pairwise fun z w ↦ Disjoint (piece z) (piece w) := by
    exact shiftedTilingFirstPiece_pairwiseDisjoint t x tau
  have hpieceLarge : ∀ z, fairSteps
      (piece z ∩ shiftedStoppedTilingEndpointLarge t tau k x) ≤
        q * fairSteps (piece z) := by
    rintro ⟨d, r⟩
    let tail : Set StepPath := {omega |
      tilingEndpointTailLarge t x N k (pairedSegment (1 + 2 * r) N omega)}
    have hsubset : piece (d, r) ∩ shiftedStoppedTilingEndpointLarge t tau k x ⊆
        piece (d, r) ∩ tail := by
      rintro omega ⟨hpiece, hlargeOmega⟩
      refine ⟨hpiece, ?_⟩
      change omega ∈ shiftedTilingFirstPiece t x tau (d, r) at hpiece
      have hd : omega 0 = d := hpiece.1
      have hraw := hpiece.2
      change omega ∈ tilingFirstPiece t (directionVector d) x 1 r tau at hraw
      change tilingRawFirstAt t (directionVector d) x 1 r omega ∧
        1 + 2 * r ≤ tau omega at hraw
      have htauPos : 0 < tau omega :=
        (show 0 < 1 + 2 * r by omega).trans_le hraw.2
      have hra : r ≤ (tau omega - 1) / 2 := by
        apply (Nat.le_div_iff_mul_le (by omega : 0 < 2)).2
        rw [mul_comm]
        exact (Nat.le_sub_one_iff_lt htauPos).2 (by omega)
      change tilingEndpointTailLarge t x N k
        (pairedSegment (1 + 2 * r) N omega)
      apply tilingRawFirstAt_tail_large t (directionVector d) x 1 r
        ((tau omega - 1) / 2) N k omega hra (hN omega) hraw.1
      simpa only [shiftedStoppedTilingEndpointLarge, Set.mem_ofPred_eq, hd] using
        hlargeOmega.2
    calc
      fairSteps (piece (d, r) ∩ shiftedStoppedTilingEndpointLarge t tau k x) ≤
          fairSteps (piece (d, r) ∩ tail) := measure_mono hsubset
      _ ≤ q * fairSteps (piece (d, r)) := by
        exact fairSteps_prefix_inter_tilingEndpointTailLarge_le
          t x (1 + 2 * r) N k q (piece (d, r))
            (hpieceFiltration (d, r)) hone
  have hunion : (⋃ z, piece z) = shiftedStoppedTilingEndpointMember t tau x :=
    iUnion_shiftedTilingFirstPiece t tau x
  have hinter : (⋃ z, piece z ∩ shiftedStoppedTilingEndpointLarge t tau k x) =
      shiftedStoppedTilingEndpointMember t tau x ∩
        shiftedStoppedTilingEndpointLarge t tau k x := by
    rw [← iUnion_inter, hunion]
  rw [← hinter, measure_iUnion
    (fun _ _ hzw ↦ (hpieceDisjoint hzw).mono inter_subset_left inter_subset_left)
    (fun z ↦ (hpieceMeas z).inter hlarge)]
  calc
    ∑' z, fairSteps (piece z ∩ shiftedStoppedTilingEndpointLarge t tau k x) ≤
        ∑' z, q * fairSteps (piece z) :=
      ENNReal.tsum_le_tsum hpieceLarge
    _ = q * ∑' z, fairSteps (piece z) := ENNReal.tsum_mul_left
    _ = q * fairSteps (shiftedStoppedTilingEndpointMember t tau x) := by
      rw [← measure_iUnion hpieceDisjoint hpieceMeas, hunion]

/-! ## Identification with the exact random-clock band definitions -/

theorem trajectory_preimage_tilingRandomClockMember_even
    (t : DominoTiling) (m cutoff : ℕ) (band : RandomClockBand)
    (horient : band.orientation = .even)
    (hphase : band.vertexPhase = false) (x : Point) :
    trajectory ⁻¹' memberEvent
        (tilingRandomClockVisitedSites t m cutoff band) x =
      evenStoppedTilingEndpointMember t
        (truncatedLevelTime m band.oldRank cutoff) x := by
  ext omega
  simp only [Set.mem_preimage, memberEvent, Set.mem_ofPred_eq,
    tilingRandomClockVisitedSites, pathPhaseFilteredExternalVisitedSites,
    horient, hphase,
    externalVertexPhaseOfBool, evenStoppedTilingEndpointMember]
  rw [pathTruncatedLevelTime_trajectory]
  rw [phasedExternalEndpointVisited_even]
  rfl

theorem trajectory_preimage_tilingRandomClockLarge_even
    (t : DominoTiling) (m cutoff : ℕ) (band : RandomClockBand)
    (horient : band.orientation = .even)
    (hphase : band.vertexPhase = false) (x : Point) :
    trajectory ⁻¹' tilingRandomClockExternalLargeEvent
        t m cutoff band x =
      evenStoppedTilingEndpointLarge t
        (truncatedLevelTime m band.oldRank cutoff)
        band.externalThreshold x := by
  ext omega
  simp only [Set.mem_preimage, tilingRandomClockExternalLargeEvent,
    Set.mem_ofPred_eq, pathPhaseFilteredExternalLocalTime, horient, hphase,
    externalVertexPhaseOfBool, evenStoppedTilingEndpointLarge]
  rw [pathTruncatedLevelTime_trajectory]
  rw [phasedExternalEndpointLocalTime_even]
  rfl

theorem trajectory_preimage_tilingRandomClockMember_shifted
    (t : DominoTiling) (m cutoff : ℕ) (band : RandomClockBand)
    (horient : band.orientation = .shifted)
    (hphase : band.vertexPhase = false) (x : Point) :
    trajectory ⁻¹' memberEvent
        (tilingRandomClockVisitedSites t m cutoff band) x =
      shiftedStoppedTilingEndpointMember t
        (truncatedLevelTime m band.oldRank cutoff) x := by
  ext omega
  simp only [Set.mem_preimage, memberEvent, Set.mem_ofPred_eq,
    tilingRandomClockVisitedSites, pathPhaseFilteredExternalVisitedSites,
    horient, hphase,
    externalVertexPhaseOfBool, shiftedStoppedTilingEndpointMember]
  rw [pathTruncatedLevelTime_trajectory]
  let n := truncatedLevelTime m band.oldRank cutoff omega
  change x ∈ phasedExternalVertexVisitedSites t .shifted .endpoint
      (finitePathList (pathPrefix (trajectory omega) n)) ↔
    0 < n ∧ tilingDeletedMemberProperty t (directionVector (omega 0)) x
      (pairedSegment 1 ((n - 1) / 2) omega)
  by_cases hn : n = 0
  · rw [hn]
    change x ∈ (phasedExternalVertexPath t .shifted .endpoint
      (finitePathList (pathPrefix (trajectory omega) 0))).toFinset ↔ _
    rw [phasedExternalEndpointPath_shifted_zero]
    simp
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    rw [phasedExternalEndpointVisited_shifted t omega n hnpos]
    rw [trajectory_one]
    simp only [hnpos, true_and]
    rfl

theorem trajectory_preimage_tilingRandomClockLarge_shifted
    (t : DominoTiling) (m cutoff : ℕ) (band : RandomClockBand)
    (horient : band.orientation = .shifted)
    (hphase : band.vertexPhase = false) (hthreshold : 0 < band.externalThreshold)
    (x : Point) :
    trajectory ⁻¹' tilingRandomClockExternalLargeEvent
        t m cutoff band x =
      shiftedStoppedTilingEndpointLarge t
        (truncatedLevelTime m band.oldRank cutoff)
        band.externalThreshold x := by
  ext omega
  simp only [Set.mem_preimage, tilingRandomClockExternalLargeEvent,
    Set.mem_ofPred_eq, pathPhaseFilteredExternalLocalTime, horient, hphase,
    externalVertexPhaseOfBool, shiftedStoppedTilingEndpointLarge]
  rw [pathTruncatedLevelTime_trajectory]
  let n := truncatedLevelTime m band.oldRank cutoff omega
  change band.externalThreshold ≤ phasedExternalVertexLocalTime
      t .shifted .endpoint
        (finitePathList (pathPrefix (trajectory omega) n)) x ↔
    0 < n ∧ band.externalThreshold ≤ listLocalTime
      (tilingRawEndpointPath t (directionVector (omega 0)) 1
        ((n - 1) / 2) omega) x
  by_cases hn : n = 0
  · rw [hn]
    change band.externalThreshold ≤ listLocalTime
        (phasedExternalVertexPath t .shifted .endpoint
          (finitePathList (pathPrefix (trajectory omega) 0))) x ↔ _
    rw [phasedExternalEndpointPath_shifted_zero]
    simp [listLocalTime, Nat.not_le.mpr hthreshold]
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    rw [phasedExternalEndpointLocalTime_shifted t omega n hnpos]
    rw [trajectory_one]
    simp only [hnpos, true_and]
    rfl

/-! ## Exact weighted one-site theorem for an endpoint-phase band -/

theorem simpleRandomWalk_tilingRandomClockEndpoint_weighted_oneSite
    (t : DominoTiling) (m cutoff N : ℕ) (band : RandomClockBand)
    (q : ℝ≥0∞) (hphase : band.vertexPhase = false)
    (hcutoff : cutoff ≤ N) (hthreshold : 0 < band.externalThreshold)
    (hone : externalBlocks .even {eta |
      band.externalThreshold ≤ externalOriginLocalTime .even eta N} ≤ q)
    (x : Point) :
    simpleRandomWalk
        (candidateEvent (tilingRandomClockVisitedSites t m cutoff band)
          (tilingRandomClockExternalLargeEvent t m cutoff band) x) ≤
      q * simpleRandomWalk
        (memberEvent (tilingRandomClockVisitedSites t m cutoff band) x) := by
  let tau : StepPath → ℕ := truncatedLevelTime m band.oldRank cutoff
  have htau : IsFiniteStoppingTime tau :=
    isFiniteStoppingTime_truncatedLevelTime m band.oldRank cutoff
  have htauN : ∀ omega, tau omega ≤ N := fun omega ↦
    (truncatedLevelTime_le m band.oldRank cutoff omega).trans hcutoff
  have hmemberMeas : MeasurableSet
      (memberEvent (tilingRandomClockVisitedSites t m cutoff band) x) :=
    measurableSet_memberEvent_tilingRandomClockVisitedSites t m cutoff band x
  have hlargeMeas : MeasurableSet
      (tilingRandomClockExternalLargeEvent t m cutoff band x) :=
    measurableSet_tilingRandomClockExternalLargeEvent t m cutoff band x
  have hcandMeas : MeasurableSet
      (candidateEvent (tilingRandomClockVisitedSites t m cutoff band)
        (tilingRandomClockExternalLargeEvent t m cutoff band) x) :=
    hmemberMeas.inter hlargeMeas
  rw [simpleRandomWalk, Measure.map_apply measurable_trajectory hcandMeas,
    Measure.map_apply measurable_trajectory hmemberMeas]
  cases horient : band.orientation with
  | even =>
      have hmember := trajectory_preimage_tilingRandomClockMember_even
        t m cutoff band horient hphase x
      have hlarge := trajectory_preimage_tilingRandomClockLarge_even
        t m cutoff band horient hphase x
      have hlargeStep : MeasurableSet
          (evenStoppedTilingEndpointLarge t tau band.externalThreshold x) := by
        rw [← hlarge]
        exact hlargeMeas.preimage measurable_trajectory
      rw [show trajectory ⁻¹'
            candidateEvent (tilingRandomClockVisitedSites t m cutoff band)
              (tilingRandomClockExternalLargeEvent t m cutoff band) x =
          evenStoppedTilingEndpointMember t tau x ∩
            evenStoppedTilingEndpointLarge t tau band.externalThreshold x by
          rw [candidateEvent, preimage_inter, hmember, hlarge],
        hmember]
      exact fairSteps_evenStoppedTilingEndpoint_weighted_oneSite
        t tau N band.externalThreshold q x htau
          (fun omega ↦ (Nat.div_le_self (tau omega) 2).trans (htauN omega))
          hlargeStep hone
  | shifted =>
      have hmember := trajectory_preimage_tilingRandomClockMember_shifted
        t m cutoff band horient hphase x
      have hlarge := trajectory_preimage_tilingRandomClockLarge_shifted
        t m cutoff band horient hphase hthreshold x
      have hlargeStep : MeasurableSet
          (shiftedStoppedTilingEndpointLarge t tau band.externalThreshold x) := by
        rw [← hlarge]
        exact hlargeMeas.preimage measurable_trajectory
      rw [show trajectory ⁻¹'
            candidateEvent (tilingRandomClockVisitedSites t m cutoff band)
              (tilingRandomClockExternalLargeEvent t m cutoff band) x =
          shiftedStoppedTilingEndpointMember t tau x ∩
            shiftedStoppedTilingEndpointLarge t tau band.externalThreshold x by
          rw [candidateEvent, preimage_inter, hmember, hlarge],
        hmember]
      exact fairSteps_shiftedStoppedTilingEndpoint_weighted_oneSite
        t tau N band.externalThreshold q x htau
          (fun omega ↦ (Nat.div_le_self (tau omega - 1) 2).trans
            ((Nat.sub_le (tau omega) 1).trans (htauN omega)))
          hlargeStep hone

/-- HLOZ-parameter form.  This is the exact `weighted` field required by
`TilingStoppedExternalOnePointData` for endpoint-phase bands. -/
theorem eventually_simpleRandomWalk_tilingRandomClockEndpoint_weightedOneSite44
    (t : DominoTiling) :
    ∀ᶠ m : ℕ in Filter.atTop, ∀ (cutoff : ℕ) (band : RandomClockBand),
      cutoff ≤ hlozCutoff44 m →
      band.vertexPhase = false →
      hlozOnePointLevel44 m + 1 ≤ band.externalThreshold →
      ∀ x : Point,
        simpleRandomWalk
            (candidateEvent (tilingRandomClockVisitedSites t m cutoff band)
              (tilingRandomClockExternalLargeEvent t m cutoff band) x) ≤
          hlozOnePointRate44 m * simpleRandomWalk
            (memberEvent (tilingRandomClockVisitedSites t m cutoff band) x) := by
  filter_upwards [hlozSharpExternalOnePointTail44 .even] with m hone
  intro cutoff band hcutoff hphase hmargin x
  have hthreshold : 0 < band.externalThreshold := by omega
  have htail : externalBlocks .even {eta |
      band.externalThreshold ≤ externalOriginLocalTime .even eta
        (hlozCutoff44 m)} ≤ hlozOnePointRate44 m :=
    (measure_mono fun _ hlocal ↦
      (show hlozOnePointLevel44 m ≤ band.externalThreshold by omega).trans
        hlocal).trans hone
  exact simpleRandomWalk_tilingRandomClockEndpoint_weighted_oneSite
    t m cutoff (hlozCutoff44 m) band (hlozOnePointRate44 m)
      hphase hcutoff hthreshold htail x

end

end Erdos1165.TilingStoppedWeightedOnePoint
