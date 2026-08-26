import ErdosProblems.Erdos118.LeafResponses

/-!
Concrete interfaces joining root, body, stem, leaf, and completion responses.
Their local transitions and transitions on either component of a pair are
well founded. No graph payoff or triangle theorem is assumed.
-/

namespace Erdos118.DecisionStates

open LabelledExtensions LabelledFrames Negative Negative.Exact Erdos590.Larson

structure BodyDecision where
  stem : Stem
  roots : List ℕ
  room : stem.done.length + 1 < stem.root
  rootSlots : Slots (stem.done.length + 1) stem.root stem.rootLabel roots
  rootSelected : stem.done.length + 1 ∈ stem.rootLabel

def ofRoot {k : ℕ} (A : RootResponses.Setup k) : BodyDecision where
  stem := A.stem
  roots := A.stem.rootLabel.tail
  room := A.room
  rootSlots := by
    rw [A.first_body]
    exact label_tail_slots _ _ A.stem.label_pairwise A.stem.label_before_root
  rootSelected := by
    rw [A.first_body]
    apply first_mem
    intro he
    have h := A.label_length
    simp [he] at h

def applyBody (D : BodyDecision) {k : ℕ} (A : BodyResponses.Setup D.stem k) : Pending where
  position := A.position
  roots := D.roots
  leaves := A.position.label.tail
  rootSlots := by rw [A.stem_eq]; exact D.rootSlots
  leafSlots := by
    rw [A.entries_length]
    exact label_tail_slots _ _ A.position.label_pairwise A.position.label_before_marker
  rootSelected := by rw [A.stem_eq]; exact D.rootSelected
  leafSelected := by
    rw [A.entries_length]
    apply first_mem
    intro he
    have h := A.label_length
    simp [he] at h

theorem next_body_bounds (F : Pending) (c : ℕ) (rest : List ℕ)
    (hF : F.roots = c :: rest) :
    F.position.stem.done.length < c - 1 ∧ c - 1 ≤ F.position.stem.root ∧
      0 < c ∧ c < F.position.stem.root := by
  have hslot := F.rootSlots.bounded c (hF ▸ List.mem_cons_self ..)
  omega

def ofStem (F : Pending) (c : ℕ) (rest : List ℕ) (hF : F.roots = c :: rest)
    (A : StemResponses.Setup F.position (c - 1)) : BodyDecision := by
  have hslot := F.rootSlots.bounded c (hF ▸ List.mem_cons_self ..)
  have hcount : A.stem.done.length + 1 = c := by rw [A.count]; omega
  exact
    { stem := A.stem, roots := rest
      room := by rw [hcount, A.root_eq]; exact hslot.2.1
      rootSlots := by
        rw [hcount, A.root_eq, A.rootLabel_eq]
        exact Slots.tail (by simpa only [hF] using F.rootSlots)
      rootSelected := by rw [hcount, A.rootLabel_eq]; exact hslot.2.2 }

structure Completed where
  stem : Stem
  full : stem.done.length = stem.root

def ofCompletion (F : Pending) (A : StemResponses.Setup F.position F.position.stem.root) :
    Completed := ⟨A.stem, A.count.trans A.root_eq.symm⟩

def ofGood (s : G) : Completed where
  stem :=
    { root := s.1.length, rootLabel := [], done := s.1.map plain
      count := by simp
      increasing := by simpa only [List.nil_append, plain_decorated, word] using s.2 }
  full := by simp

theorem ofGood_ordinary (s : G) : (ofGood s).stem.ordinary = word s.1 := by
  simp [ofGood, Stem.ordinary, word]

theorem ofGood_decorated (s : G) : (ofGood s).stem.decorated = word s.1 := by
  simp [ofGood, Stem.decorated, word]

inductive State
  | initial
  | body (D : BodyDecision)
  | leaf (F : Pending)
  | complete (T : Completed)

def State.ordinary : State → List ℕ
  | .initial => []
  | .body D => D.stem.ordinary
  | .leaf F => F.position.ordinary
  | .complete T => T.stem.ordinary

def State.decorated : State → List ℕ
  | .initial => []
  | .body D => D.stem.decorated
  | .leaf F => F.position.decorated
  | .complete T => T.stem.decorated

def State.rootLabel : State → Option (List ℕ)
  | .initial => none
  | .body D => some D.stem.rootLabel
  | .leaf F => some F.position.stem.rootLabel
  | .complete T => some T.stem.rootLabel

def State.bodyLabels : State → List (List ℕ)
  | .initial => []
  | .body D => D.stem.bodyLabels
  | .leaf F => F.position.bodyLabels
  | .complete T => T.stem.bodyLabels

structure LabelsExtend (S T : State) : Prop where
  root : ∀ C, S.rootLabel = some C → T.rootLabel = some C
  bodies : S.bodyLabels <+: T.bodyLabels

theorem LabelsExtend.refl (S : State) : LabelsExtend S S :=
  ⟨fun _ h ↦ h, List.prefix_rfl⟩

theorem LabelsExtend.trans {S T U : State} (hST : LabelsExtend S T)
    (hTU : LabelsExtend T U) : LabelsExtend S U :=
  ⟨fun C hC ↦ hTU.root C (hST.root C hC), hST.bodies.trans hTU.bodies⟩

/-- The new state is the first argument, as in a well-founded child relation. -/
inductive Step : State → State → Prop
  | root {k : ℕ} (A : RootResponses.Setup k) : Step (.body (ofRoot A)) .initial
  | whole (s : G) : Step (.complete (ofGood s)) .initial
  | body (D : BodyDecision) {k : ℕ} (A : BodyResponses.Setup D.stem k) :
      Step (.leaf (applyBody D A)) (.body D)
  | leaf (F : Pending) (j : ℕ) (rest : List ℕ) (hF : F.leaves = j :: rest)
      (A : LeafResponses.Setup F.position j) :
      Step (.leaf (LeafResponses.toPending F j rest hF A)) (.leaf F)
  | nextBody (F : Pending) (c : ℕ) (rest : List ℕ) (hR : F.roots = c :: rest)
      (hL : F.leaves = []) (A : StemResponses.Setup F.position (c - 1)) :
      Step (.body (ofStem F c rest hR A)) (.leaf F)
  | finish (F : Pending) (hR : F.roots = []) (hL : F.leaves = [])
      (A : StemResponses.Setup F.position F.position.stem.root) :
      Step (.complete (ofCompletion F A)) (.leaf F)

theorem step_extensions {S T : State} (h : Step T S) :
    ∃ v d : List ℕ, T.ordinary = S.ordinary ++ v ∧ T.decorated = S.decorated ++ d ∧
      v ≠ [] ∧ v.Sublist d := by
  cases h with
  | root A =>
    exact ⟨A.stem.ordinary, A.stem.decorated, rfl, rfl,
      by simp [Stem.ordinary], A.stem.ordinary_sublist⟩
  | whole s =>
    exact ⟨word s.1, word s.1, ofGood_ordinary s, ofGood_decorated s,
      by simp [word], List.Sublist.refl _⟩
  | body D A =>
    exact ⟨A.position.size :: A.position.entries, BodyResponses.newWord A.position,
      BodyResponses.setup_ordinary A, BodyResponses.setup_decorated A, List.cons_ne_nil _ _,
      List.sublist_append_right _ _⟩
  | leaf F j rest hF A =>
    have hslot := F.leafSlots.bounded j (hF ▸ List.mem_cons_self ..)
    exact ⟨A.newWord, A.newWord, LeafResponses.position_ordinary A hslot.1 hslot.2.1,
      LeafResponses.position_decorated A hslot.1 hslot.2.1,
      LeafResponses.newWord_ne_nil A hslot.1, List.Sublist.refl _⟩
  | nextBody F c rest hR hL A =>
    exact ⟨A.newWord, A.newWord, A.ordinary, A.decorated, A.nonempty, List.Sublist.refl _⟩
  | finish F hR hL A =>
    exact ⟨A.newWord, A.newWord, A.ordinary, A.decorated, A.nonempty, List.Sublist.refl _⟩

theorem step_labels {S T : State} (h : Step T S) : LabelsExtend S T := by
  cases h with
  | root A => exact ⟨by simp [State.rootLabel], List.nil_prefix⟩
  | whole s => exact ⟨by simp [State.rootLabel], List.nil_prefix⟩
  | body D A =>
    refine ⟨?_, ?_⟩
    · intro C hC
      change some A.position.stem.rootLabel = some C
      rw [A.stem_eq]
      exact hC
    · change D.stem.bodyLabels <+: A.position.bodyLabels
      rw [Position.bodyLabels, A.stem_eq]
      exact List.prefix_append _ _
  | leaf F j rest hF A => exact ⟨fun _ hC ↦ hC, List.prefix_rfl⟩
  | nextBody F c rest hR hL A =>
    refine ⟨?_, StemResponses.labels_prefix A⟩
    intro C hC
    change some A.stem.rootLabel = some C
    rw [A.rootLabel_eq]
    exact hC
  | finish F hR hL A =>
    refine ⟨?_, StemResponses.labels_prefix A⟩
    intro C hC
    change some A.stem.rootLabel = some C
    rw [A.rootLabel_eq]
    exact hC

abbrev Rank := ℕ × (ℕ × ℕ)
def RankLT : Rank → Rank → Prop := Prod.Lex (· < ·) (Prod.Lex (· < ·) (· < ·))

def rank : State → Rank
  | .initial => (1, 0, 0)
  | .body D => (0, D.roots.length + 1, 0)
  | .leaf F => (0, F.roots.length, F.leaves.length + 1)
  | .complete _ => (0, 0, 0)

theorem rank_wellFounded : WellFounded RankLT :=
  (Prod.lex Nat.lt_wfRel (Prod.lex Nat.lt_wfRel Nat.lt_wfRel)).wf

theorem step_decreases {S T : State} (h : Step T S) : RankLT (rank T) (rank S) := by
  cases h with
  | root A => exact Prod.Lex.left _ _ (by decide)
  | whole s => exact Prod.Lex.left _ _ (by decide)
  | body D A =>
    exact Prod.Lex.right _ (Prod.Lex.left _ _ (Nat.lt_succ_self _))
  | leaf F j rest hF A =>
    apply Prod.Lex.right
    apply Prod.Lex.right
    change rest.length + 1 < F.leaves.length + 1
    simp [hF]
  | nextBody F c rest hR hL A =>
    apply Prod.Lex.right
    change Prod.Lex (· < ·) (· < ·) (rest.length + 1, 0) (F.roots.length, F.leaves.length + 1)
    rw [hR, hL]
    exact Prod.Lex.right _ (by decide)
  | finish F hR hL A =>
    change Prod.Lex (· < ·) (Prod.Lex (· < ·) (· < ·)) (0, 0, 0)
      (0, F.roots.length, F.leaves.length + 1)
    rw [hR, hL]
    exact Prod.Lex.right _ (Prod.Lex.right _ (by decide))

theorem step_wellFounded : WellFounded Step :=
  (InvImage.wf rank rank_wellFounded).mono (fun _ _ h ↦ step_decreases h)

def addRank (a b : Rank) : Rank := (a.1 + b.1, a.2.1 + b.2.1, a.2.2 + b.2.2)

theorem rankLT_add {a b : Rank} (h : RankLT a b) (c : Rank) :
    RankLT (addRank a c) (addRank b c) := by
  rcases a with ⟨a, a', a''⟩
  rcases b with ⟨b, b', b''⟩
  simp only [RankLT, Prod.lex_def, addRank] at h ⊢
  omega

theorem addRank_comm (a b : Rank) : addRank a b = addRank b a := by
  simp [addRank, Nat.add_comm]

def pairRank (S : State × State) : Rank := addRank (rank S.1) (rank S.2)

inductive PairStep : (State × State) → (State × State) → Prop
  | left {S T : State} (U : State) (h : Step T S) : PairStep (T, U) (S, U)
  | right (U : State) {S T : State} (h : Step T S) : PairStep (U, T) (U, S)

theorem pairStep_decreases {S T : State × State} (h : PairStep T S) :
    RankLT (pairRank T) (pairRank S) := by
  cases h with
  | left U h => exact rankLT_add (step_decreases h) _
  | right U h =>
    simpa only [pairRank, addRank_comm (rank U)] using rankLT_add (step_decreases h) (rank U)

theorem pairStep_wellFounded : WellFounded PairStep :=
  (InvImage.wf pairRank rank_wellFounded).mono (fun _ _ h ↦ pairStep_decreases h)

end Erdos118.DecisionStates
