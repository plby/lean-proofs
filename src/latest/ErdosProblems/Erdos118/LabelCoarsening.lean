import ErdosProblems.Erdos118.LabelledRealization
import Mathlib.Data.List.TakeWhile

/-!
Select precisely the annotations used by a finite family of certified cuts.
All ordinary coordinates are retained. This projection does not assert the
remaining clear-pair geometry or any coloring/game conclusion.
-/

namespace Erdos118.LabelCoarsening

open LabelledExtensions LabelledFrames

def filterLabels (labels : List (List ℕ)) (keep : ℕ → ℕ → Bool) : List (List ℕ) :=
  labels.mapIdx fun i D ↦ D.filter (keep i)

def filterBodies (bodies : List Body) (keep : ℕ → ℕ → Bool) : List Body :=
  bodies.mapIdx fun i a ↦ ⟨a.values, a.label.filter (keep i)⟩

@[simp] theorem filterBodies_length (bodies : List Body) (keep : ℕ → ℕ → Bool) :
    (filterBodies bodies keep).length = bodies.length := by
  simp [filterBodies]

theorem filterBodies_ordinary (bodies : List Body) (keep : ℕ → ℕ → Bool) :
    (filterBodies bodies keep).flatMap Body.ordinary = bodies.flatMap Body.ordinary := by
  induction bodies generalizing keep with
  | nil => rfl
  | cons a bodies ih =>
    simp only [filterBodies, List.mapIdx_cons, List.flatMap_cons]
    exact congrArg (a.ordinary ++ ·) (ih (fun i ↦ keep (i + 1)))

theorem filterBodies_decorated (bodies : List Body) (keep : ℕ → ℕ → Bool) :
    ((filterBodies bodies keep).flatMap Body.decorated).Sublist
      (bodies.flatMap Body.decorated) := by
  induction bodies generalizing keep with
  | nil => exact List.Sublist.refl _
  | cons a bodies ih =>
    simp only [filterBodies, List.mapIdx_cons, List.flatMap_cons]
    exact ((List.filter_sublist).append (List.Sublist.refl a.ordinary)).append
      (ih (fun i ↦ keep (i + 1)))

theorem filterBodies_labels (bodies : List Body) (keep : ℕ → ℕ → Bool) :
    (filterBodies bodies keep).map Body.label = filterLabels (bodies.map Body.label) keep := by
  induction bodies generalizing keep with
  | nil => rfl
  | cons a bodies ih =>
    simp only [filterBodies, filterLabels, List.mapIdx_cons, List.map_cons]
    exact congrArg (a.label.filter (keep 0) :: ·) (ih (fun i ↦ keep (i + 1)))

theorem filterLabels_prefix {xs ys : List (List ℕ)} (h : xs <+: ys)
    (keep : ℕ → ℕ → Bool) : filterLabels xs keep <+: filterLabels ys keep := by
  obtain ⟨rest, rfl⟩ := h
  unfold filterLabels
  rw [List.mapIdx_append]
  exact List.prefix_append _ _

def coarsenStem (S : Stem) (rootKeep : ℕ → Bool) (bodyKeep : ℕ → ℕ → Bool) : Stem where
  root := S.root
  rootLabel := S.rootLabel.filter rootKeep
  done := filterBodies S.done bodyKeep
  count := by simpa using S.count
  increasing := S.increasing.sublist
    ((List.filter_sublist).append ((filterBodies_decorated S.done bodyKeep).cons_cons S.root))

@[simp] theorem coarsenStem_ordinary (S : Stem) (rootKeep : ℕ → Bool)
    (bodyKeep : ℕ → ℕ → Bool) : (coarsenStem S rootKeep bodyKeep).ordinary = S.ordinary := by
  simp [coarsenStem, Stem.ordinary, filterBodies_ordinary]

theorem coarsenStem_decorated (S : Stem) (rootKeep : ℕ → Bool)
    (bodyKeep : ℕ → ℕ → Bool) :
    (coarsenStem S rootKeep bodyKeep).decorated.Sublist S.decorated :=
  (List.filter_sublist).append ((filterBodies_decorated S.done bodyKeep).cons_cons S.root)

theorem coarsenStem_labels (S : Stem) (rootKeep : ℕ → Bool)
    (bodyKeep : ℕ → ℕ → Bool) :
    (coarsenStem S rootKeep bodyKeep).bodyLabels = filterLabels S.bodyLabels bodyKeep :=
  filterBodies_labels S.done bodyKeep

def coarsenPosition (P : Position) (rootKeep : ℕ → Bool)
    (bodyKeep : ℕ → ℕ → Bool) : Position where
  stem := coarsenStem P.stem rootKeep bodyKeep
  size := P.size
  label := P.label.filter (bodyKeep P.stem.done.length)
  entries := P.entries
  room := by simpa [coarsenStem] using P.room
  started := P.started
  unfinished := P.unfinished
  increasing := P.increasing.sublist ((coarsenStem_decorated P.stem rootKeep bodyKeep).append
    ((List.filter_sublist).append (List.Sublist.refl (P.size :: P.entries))))

@[simp] theorem coarsenPosition_ordinary (P : Position) (rootKeep : ℕ → Bool)
    (bodyKeep : ℕ → ℕ → Bool) :
    (coarsenPosition P rootKeep bodyKeep).ordinary = P.ordinary := by
  simp [coarsenPosition, Position.ordinary]

theorem coarsenPosition_decorated (P : Position) (rootKeep : ℕ → Bool)
    (bodyKeep : ℕ → ℕ → Bool) :
    (coarsenPosition P rootKeep bodyKeep).decorated.Sublist P.decorated :=
  (coarsenStem_decorated P.stem rootKeep bodyKeep).append
    ((List.filter_sublist).append (List.Sublist.refl (P.size :: P.entries)))

theorem coarsenPosition_labels (P : Position) (rootKeep : ℕ → Bool)
    (bodyKeep : ℕ → ℕ → Bool) :
    (coarsenPosition P rootKeep bodyKeep).bodyLabels =
      filterLabels P.bodyLabels bodyKeep := by
  change (coarsenStem P.stem rootKeep bodyKeep).bodyLabels ++
    [P.label.filter (bodyKeep P.stem.done.length)] = _
  rw [coarsenStem_labels]
  simp [Position.bodyLabels, filterLabels, Stem.bodyLabels]

theorem slots_filter {lo hi : ℕ} {label remaining : List ℕ}
    (h : Slots lo hi label remaining) (keep : ℕ → Bool) :
    Slots lo hi (label.filter keep) (remaining.filter keep) := by
  refine ⟨h.increasing.sublist List.filter_sublist, ?_⟩
  intro x hx
  obtain ⟨hxr, hxkeep⟩ := List.mem_filter.mp hx
  obtain ⟨hlo, hhi, hxl⟩ := h.bounded x hxr
  exact ⟨hlo, hhi, List.mem_filter.mpr ⟨hxl, hxkeep⟩⟩

def coarsenPending (P : Pending) (rootKeep : ℕ → Bool)
    (bodyKeep : ℕ → ℕ → Bool)
    (hr : rootKeep (P.position.stem.done.length + 1) = true)
    (hl : bodyKeep P.position.stem.done.length P.position.entries.length = true) : Pending where
  position := coarsenPosition P.position rootKeep bodyKeep
  roots := P.roots.filter rootKeep
  leaves := P.leaves.filter (bodyKeep P.position.stem.done.length)
  rootSlots := by simpa [coarsenPosition, coarsenStem] using slots_filter P.rootSlots rootKeep
  leafSlots := slots_filter P.leafSlots (bodyKeep P.position.stem.done.length)
  rootSelected := by
    simpa [coarsenPosition, coarsenStem] using List.mem_filter.mpr ⟨P.rootSelected, hr⟩
  leafSelected := List.mem_filter.mpr ⟨P.leafSelected, hl⟩

theorem coarsenPending_extends (P : Pending) (S : Stem) (hS : S.done.length = S.root)
    (h : LabelsExtend (.pending P) (.terminal S hS))
    (rootKeep : ℕ → Bool) (bodyKeep : ℕ → ℕ → Bool)
    (hr : rootKeep (P.position.stem.done.length + 1) = true)
    (hl : bodyKeep P.position.stem.done.length P.position.entries.length = true) :
    LabelsExtend (.pending (coarsenPending P rootKeep bodyKeep hr hl))
      (.terminal (coarsenStem S rootKeep bodyKeep)
        (by simpa [coarsenStem] using hS)) := by
  apply LabelsExtend.terminal
  · have he : S.rootLabel = P.position.stem.rootLabel :=
      Option.some.inj (h.root _ rfl)
    exact congrArg (List.filter rootKeep) he
  · change (coarsenPosition P.position rootKeep bodyKeep).bodyLabels <+:
      (coarsenStem S rootKeep bodyKeep).bodyLabels
    rw [coarsenPosition_labels, coarsenStem_labels]
    exact filterLabels_prefix h.bodies bodyKeep

theorem selected_root_mem (P : Pending) (S : Stem) (hS : S.done.length = S.root)
    (h : LabelsExtend (.pending P) (.terminal S hS)) :
    P.position.stem.done.length + 1 ∈ S.rootLabel := by
  have he : S.rootLabel = P.position.stem.rootLabel := Option.some.inj (h.root _ rfl)
  rw [he]
  exact P.rootSelected

theorem selected_body_mem (P : Pending) (S : Stem) (hS : S.done.length = S.root)
    (h : LabelsExtend (.pending P) (.terminal S hS)) :
    ∃ hi : P.position.stem.done.length < S.bodyLabels.length,
      P.position.entries.length ∈ S.bodyLabels[P.position.stem.done.length] := by
  have hi : P.position.stem.done.length < P.position.bodyLabels.length := by
    simp [Position.bodyLabels, Stem.bodyLabels]
  have hb : P.position.bodyLabels <+: S.bodyLabels := h.bodies
  have he := hb.getElem hi
  refine ⟨hi.trans_le hb.length_le, ?_⟩
  rw [← he]
  simpa [Position.bodyLabels, Stem.bodyLabels] using P.leafSelected

/-- Matching annotations let the literal length markers recover every earlier
complete body, not just its label. -/
theorem decorated_prefix_cancel {p q : List Body} {D u : List ℕ}
    (hlabels : p.map Body.label ++ [D] <+: q.map Body.label)
    (hword : p.flatMap Body.decorated ++ (D ++ u) <+: q.flatMap Body.decorated) :
    ∃ a : Body, ∃ rest : List Body,
      q = p ++ a :: rest ∧ a.label = D ∧ u <+: a.ordinary ++ rest.flatMap Body.decorated := by
  induction p generalizing q with
  | nil =>
    cases q with
    | nil => simp at hlabels
    | cons a q =>
      have hD : D = a.label := (List.cons_prefix_cons.mp hlabels).1
      refine ⟨a, q, rfl, hD.symm, ?_⟩
      simpa [Body.decorated, hD, List.append_assoc] using hword
  | cons a p ih =>
    cases q with
    | nil => simp at hlabels
    | cons b q =>
      have hL : a.label = b.label ∧ p.map Body.label ++ [D] <+: q.map Body.label := by
        simpa only [List.map_cons, List.cons_append, List.cons_prefix_cons] using hlabels
      have hw : a.ordinary ++ (p.flatMap Body.decorated ++ (D ++ u)) <+:
          b.ordinary ++ q.flatMap Body.decorated := by
        simpa only [List.flatMap_cons, Body.decorated, List.append_assoc, hL.1,
          List.prefix_append_right_inj] using hword
      obtain ⟨hvalues, htail⟩ := WordResponses.levelWord_prefix_cancel hw
      have hab : a = b := by
        cases a
        cases b
        simp_all
      subst b
      obtain ⟨c, rest, hq, hc, hu⟩ := ih hL.2 htail
      exact ⟨c, rest, by simp [hq], hc, hu⟩

structure CutExtension (P : Position) (S : Stem) : Prop where
  root : S.root = P.stem.root
  rootLabel : S.rootLabel = P.stem.rootLabel
  bodies : ∃ a : Body, ∃ rest : List Body,
    S.done = P.stem.done ++ a :: rest ∧ a.label = P.label ∧
      a.values.length = P.size ∧ P.entries <+: a.values

theorem cutExtension_of_prefix (P : Pending) (S : Stem) (hS : S.done.length = S.root)
    (hlabels : LabelsExtend (.pending P) (.terminal S hS))
    (hprefix : P.position.decorated <+: S.decorated) : CutExtension P.position S := by
  have hC : S.rootLabel = P.position.stem.rootLabel :=
    Option.some.inj (hlabels.root _ rfl)
  have hp : P.position.stem.root = S.root ∧
      P.position.stem.done.flatMap Body.decorated ++ (P.position.label ++
        P.position.size :: P.position.entries) <+: S.done.flatMap Body.decorated := by
    simpa only [Position.decorated, Stem.decorated, List.append_assoc, List.cons_append,
      hC, List.prefix_append_right_inj, List.cons_prefix_cons] using hprefix
  obtain ⟨a, rest, hdone, hD, hu⟩ := decorated_prefix_cancel hlabels.bodies hp.2
  have hcur : P.position.size = a.values.length ∧
      P.position.entries <+: a.values ++ rest.flatMap Body.decorated := by
    simpa only [Body.ordinary, Negative.Exact.levelWord, List.cons_append,
      List.cons_prefix_cons] using hu
  refine ⟨hp.1.symm, hC, a, rest, hdone, hD, hcur.1.symm, ?_⟩
  apply List.prefix_of_prefix_length_le hcur.2 (List.prefix_append _ _)
  exact P.position.unfinished.le.trans hcur.1.le

theorem filterBodies_append (p q : List Body) (keep : ℕ → ℕ → Bool) :
    filterBodies (p ++ q) keep = filterBodies p keep ++
      filterBodies q (fun i ↦ keep (i + p.length)) := by
  exact List.mapIdx_append

/-- Both filtered streams split at the same interior position; the new
decorated suffix is obtained only by deletions from the old suffix. -/
theorem cutExtension_coarsen_split (P : Position) (S : Stem) (h : CutExtension P S)
    (rootKeep : ℕ → Bool) (bodyKeep : ℕ → ℕ → Bool) :
    ∃ v w : List ℕ, S.decorated = P.decorated ++ v ∧
      (coarsenStem S rootKeep bodyKeep).decorated =
        (coarsenPosition P rootKeep bodyKeep).decorated ++ w ∧ w.Sublist v := by
  obtain ⟨a, rest, hdone, hD, hlen, entriesTail, hentries⟩ := h.bodies
  have hsize : (P.entries ++ entriesTail).length = P.size := by rw [hentries, hlen]
  refine ⟨entriesTail ++ rest.flatMap Body.decorated,
    entriesTail ++ (filterBodies rest (fun i ↦ bodyKeep (i + 1 + P.stem.done.length))).flatMap
      Body.decorated, ?_, ?_, ?_⟩
  · simp only [Stem.decorated, Position.decorated, h.root, h.rootLabel, hdone,
      List.flatMap_append, List.flatMap_cons, Body.decorated, Body.ordinary,
      Negative.Exact.levelWord, hD, ← hentries, hsize, List.cons_append, List.append_assoc]
  · simp only [coarsenStem, coarsenPosition, Stem.decorated, Position.decorated,
      h.root, h.rootLabel, hdone, filterBodies, List.mapIdx_append, List.mapIdx_cons,
      List.flatMap_append, List.flatMap_cons, Body.decorated, Body.ordinary,
      Negative.Exact.levelWord, hD, ← hentries, hsize, List.cons_append,
      Nat.zero_add, List.append_assoc]
  · exact (List.Sublist.refl entriesTail).append (filterBodies_decorated rest _)

theorem below_split_bounds (y : ℕ) (p q : List ℕ)
    (hinc : (p ++ q).Pairwise (· < ·)) (hcut : PrefixRealization.below y (p ++ q) = p) :
    (∀ x ∈ p, x < y) ∧ ∀ x ∈ q, y ≤ x := by
  have hp : ∀ x ∈ p, x < y := by
    intro x hx
    rw [← hcut] at hx
    exact of_decide_eq_true (List.mem_takeWhile_imp (p := fun z ↦ decide (z < y)) hx)
  have he : p ++ PrefixRealization.below y q = p := by
    simpa only [PrefixRealization.below, List.takeWhile_append_of_pos
      (fun x hx ↦ decide_eq_true (hp x hx))] using hcut
  have hnil : PrefixRealization.below y q = [] :=
    List.append_cancel_left (he.trans (List.append_nil p).symm)
  refine ⟨hp, ?_⟩
  cases q with
  | nil => simp
  | cons a q =>
    have hya : y ≤ a := by
      by_contra hy
      have hay : a < y := Nat.lt_of_not_ge hy
      simp [PrefixRealization.below, hay] at hnil
    have hq := (List.pairwise_append.mp hinc).2.1
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hya
    · exact hya.trans ((List.pairwise_cons.mp hq).1 x hx).le

/-- Deleting unused labels preserves an actual decorated threshold cut. -/
theorem coarsen_decorated_cut (P : Pending) (S : Stem) (hS : S.done.length = S.root)
    (hlabels : LabelsExtend (.pending P) (.terminal S hS)) (y : ℕ)
    (hcut : P.position.decorated = PrefixRealization.below y S.decorated)
    (rootKeep : ℕ → Bool) (bodyKeep : ℕ → ℕ → Bool) :
    (coarsenPosition P.position rootKeep bodyKeep).decorated =
      PrefixRealization.below y (coarsenStem S rootKeep bodyKeep).decorated := by
  have hprefix : P.position.decorated <+: S.decorated := by
    rw [hcut]
    exact List.takeWhile_prefix _
  obtain ⟨v, w, hSdec, hTdec, hwv⟩ := cutExtension_coarsen_split P.position S
    (cutExtension_of_prefix P S hS hlabels hprefix) rootKeep bodyKeep
  obtain ⟨hp, hv⟩ := below_split_bounds y P.position.decorated v
    (hSdec ▸ S.increasing) (by rw [← hSdec]; exact hcut.symm)
  have hp' : ∀ x ∈ (coarsenPosition P.position rootKeep bodyKeep).decorated, x < y :=
    fun x hx ↦ hp x ((coarsenPosition_decorated ..).subset hx)
  have hw : ∀ x ∈ w, y ≤ x := fun x hx ↦ hv x (hwv.subset hx)
  have hw0 : PrefixRealization.below y w = [] := by
    cases w with
    | nil => rfl
    | cons a w =>
      have hay : ¬ a < y := Nat.not_lt.mpr (hw a (List.mem_cons_self ..))
      simp [PrefixRealization.below, hay]
  rw [hTdec]
  simp only [PrefixRealization.below, List.takeWhile_append_of_pos
    (fun x hx ↦ decide_eq_true (hp' x hx)), show w.takeWhile (fun x ↦ decide (x < y)) = [] from hw0,
    List.append_nil]

noncomputable def rootKeep (cuts : List Pending) (x : ℕ) : Bool := by
  classical
  exact decide (∃ P ∈ cuts, P.position.stem.done.length + 1 = x)

noncomputable def bodyKeep (cuts : List Pending) (i j : ℕ) : Bool := by
  classical
  exact decide (∃ P ∈ cuts, P.position.stem.done.length = i ∧ P.position.entries.length = j)

@[simp] theorem rootKeep_true (cuts : List Pending) (x : ℕ) :
    rootKeep cuts x = true ↔ ∃ P ∈ cuts, P.position.stem.done.length + 1 = x := by
  classical
  simp [rootKeep]

@[simp] theorem bodyKeep_true (cuts : List Pending) (i j : ℕ) :
    bodyKeep cuts i j = true ↔
      ∃ P ∈ cuts, P.position.stem.done.length = i ∧ P.position.entries.length = j := by
  classical
  simp [bodyKeep]

theorem selected_root_exact (S : Stem) (hS : S.done.length = S.root) (cuts : List Pending)
    (hcuts : ∀ P ∈ cuts, LabelsExtend (.pending P) (.terminal S hS)) (x : ℕ) :
    x ∈ (coarsenStem S (rootKeep cuts) (bodyKeep cuts)).rootLabel ↔
      ∃ P ∈ cuts, P.position.stem.done.length + 1 = x := by
  change x ∈ S.rootLabel.filter (rootKeep cuts) ↔ _
  rw [List.mem_filter, rootKeep_true]
  constructor
  · exact And.right
  · rintro ⟨P, hP, rfl⟩
    exact ⟨selected_root_mem P S hS (hcuts P hP), ⟨P, hP, rfl⟩⟩

theorem selected_body_exact (S : Stem) (hS : S.done.length = S.root) (cuts : List Pending)
    (hcuts : ∀ P ∈ cuts, LabelsExtend (.pending P) (.terminal S hS))
    (i : ℕ) (hi : i < S.bodyLabels.length) (j : ℕ) :
    j ∈ (coarsenStem S (rootKeep cuts) (bodyKeep cuts)).bodyLabels[i]'(by
      simpa [coarsenStem_labels, filterLabels] using hi) ↔
      ∃ P ∈ cuts, P.position.stem.done.length = i ∧ P.position.entries.length = j := by
  simp only [coarsenStem_labels, filterLabels, List.getElem_mapIdx, List.mem_filter,
    bodyKeep_true]
  constructor
  · exact And.right
  · rintro ⟨P, hP, rfl, rfl⟩
    obtain ⟨_, hmem⟩ := selected_body_mem P S hS (hcuts P hP)
    exact ⟨hmem, ⟨P, hP, rfl, rfl⟩⟩

/-- Project a finite cut family without changing any of its ordinary words.
The label sets are exactly those of the selected body/leaf indices. -/
theorem project_cut_family (S : Stem) (hS : S.done.length = S.root) (cuts : List Pending)
    (hcuts : ∀ P ∈ cuts, LabelsExtend (.pending P) (.terminal S hS)) :
    ∃ T : Stem, ∃ hT : T.done.length = T.root,
      T.root = S.root ∧ T.ordinary = S.ordinary ∧ T.decorated.Sublist S.decorated ∧
      (∀ x, x ∈ T.rootLabel ↔ ∃ P ∈ cuts, P.position.stem.done.length + 1 = x) ∧
      (∀ i, ∀ hi : i < T.bodyLabels.length, ∀ j,
        j ∈ T.bodyLabels[i] ↔ ∃ P ∈ cuts,
          P.position.stem.done.length = i ∧ P.position.entries.length = j) ∧
      ∀ P ∈ cuts, ∃ Q : Pending,
        Q.position.ordinary = P.position.ordinary ∧
        Q.position.stem.done.length = P.position.stem.done.length ∧
        Q.position.entries.length = P.position.entries.length ∧
        LabelsExtend (.pending Q) (.terminal T hT) := by
  let T := coarsenStem S (rootKeep cuts) (bodyKeep cuts)
  have hT : T.done.length = T.root := by simpa [T, coarsenStem] using hS
  refine ⟨T, hT, rfl, coarsenStem_ordinary .., coarsenStem_decorated ..,
    selected_root_exact S hS cuts hcuts, ?_, ?_⟩
  · intro i hi j
    have hiS : i < S.bodyLabels.length := by
      simpa [T, coarsenStem_labels, filterLabels] using hi
    exact selected_body_exact S hS cuts hcuts i hiS j
  · intro P hP
    have hr : rootKeep cuts (P.position.stem.done.length + 1) = true :=
      (rootKeep_true ..).mpr ⟨P, hP, rfl⟩
    have hl : bodyKeep cuts P.position.stem.done.length P.position.entries.length = true :=
      (bodyKeep_true ..).mpr ⟨P, hP, rfl, rfl⟩
    refine ⟨coarsenPending P (rootKeep cuts) (bodyKeep cuts) hr hl,
      coarsenPosition_ordinary .., ?_, rfl,
      coarsenPending_extends P S hS (hcuts P hP) _ _ hr hl⟩
    exact filterBodies_length ..

theorem project_joint_cut (S : Stem) (hS : S.done.length = S.root) (cuts : List Pending)
    (P : Pending) (hP : P ∈ cuts)
    (hlabels : LabelsExtend (.pending P) (.terminal S hS)) (y : ℕ)
    (ho : P.position.ordinary = PrefixRealization.below y S.ordinary)
    (hd : P.position.decorated = PrefixRealization.below y S.decorated) :
    ∃ Q : Pending,
      Q.position.ordinary = PrefixRealization.below y
        (coarsenStem S (rootKeep cuts) (bodyKeep cuts)).ordinary ∧
      Q.position.decorated = PrefixRealization.below y
        (coarsenStem S (rootKeep cuts) (bodyKeep cuts)).decorated ∧
      LabelsExtend (.pending Q) (.terminal (coarsenStem S (rootKeep cuts) (bodyKeep cuts))
        (by simpa [coarsenStem] using hS)) := by
  have hr : rootKeep cuts (P.position.stem.done.length + 1) = true :=
    (rootKeep_true ..).mpr ⟨P, hP, rfl⟩
  have hl : bodyKeep cuts P.position.stem.done.length P.position.entries.length = true :=
    (bodyKeep_true ..).mpr ⟨P, hP, rfl, rfl⟩
  refine ⟨coarsenPending P (rootKeep cuts) (bodyKeep cuts) hr hl, ?_,
    coarsen_decorated_cut P S hS hlabels y hd _ _,
    coarsenPending_extends P S hS hlabels _ _ hr hl⟩
  change (coarsenPosition P.position _ _).ordinary = _
  rw [coarsenPosition_ordinary, coarsenStem_ordinary]
  exact ho

def ProperBelow (y : ℕ) (S : Stem) : Prop :=
  PrefixRealization.below y S.ordinary ≠ [] ∧
    PrefixRealization.below y S.ordinary ≠ S.ordinary

structure JointCut (P : Pending) (S : Stem) (hS : S.done.length = S.root) (y : ℕ) : Prop where
  ordinary : P.position.ordinary = PrefixRealization.below y S.ordinary
  decorated : P.position.decorated = PrefixRealization.below y S.decorated
  labels : LabelsExtend (.pending P) (.terminal S hS)

theorem finite_joint_cuts (S : Stem) (hS : S.done.length = S.root) (ys : List ℕ)
    (h : ∀ y ∈ ys, ProperBelow y S → ∃ P : Pending, JointCut P S hS y) :
    ∃ cuts : List Pending,
      (∀ P ∈ cuts, ∃ y ∈ ys, ProperBelow y S ∧ JointCut P S hS y) ∧
      ∀ y ∈ ys, ProperBelow y S → ∃ P ∈ cuts, JointCut P S hS y := by
  classical
  induction ys with
  | nil => exact ⟨[], by simp, by simp⟩
  | cons y ys ih =>
    obtain ⟨cuts, hused, hcover⟩ := ih (fun z hz ↦ h z (List.mem_cons_of_mem y hz))
    by_cases hy : ProperBelow y S
    · obtain ⟨P, hP⟩ := h y (List.mem_cons_self ..) hy
      refine ⟨P :: cuts, ?_, ?_⟩
      · intro Q hQ
        rcases List.mem_cons.mp hQ with rfl | hQ
        · exact ⟨y, List.mem_cons_self .., hy, hP⟩
        · obtain ⟨z, hz, hproper, hcut⟩ := hused Q hQ
          exact ⟨z, List.mem_cons_of_mem y hz, hproper, hcut⟩
      · intro z hz hproper
        rcases List.mem_cons.mp hz with rfl | hz
        · exact ⟨P, List.mem_cons_self .., hP⟩
        · obtain ⟨Q, hQ, hcut⟩ := hcover z hz hproper
          exact ⟨Q, List.mem_cons_of_mem P hQ, hcut⟩
    · refine ⟨cuts, ?_, ?_⟩
      · intro Q hQ
        obtain ⟨z, hz, hproper, hcut⟩ := hused Q hQ
        exact ⟨z, List.mem_cons_of_mem y hz, hproper, hcut⟩
      · intro z hz hproper
        rcases List.mem_cons.mp hz with rfl | hz
        · exact (hy hproper).elim
        · exact hcover z hz hproper

/-- A projection retains every proper joint cut, and every surviving label
has an actual cut witnessing its use. -/
structure Projection (S : Stem) (hS : S.done.length = S.root) (ys : List ℕ)
    (T : Stem) (hT : T.done.length = T.root) : Prop where
  root : T.root = S.root
  ordinary : T.ordinary = S.ordinary
  decorated : T.decorated.Sublist S.decorated
  cuts : ∀ y ∈ ys, ProperBelow y S → ∃ P : Pending, JointCut P T hT y
  rootUsed : ∀ x ∈ T.rootLabel, ∃ P : Pending, ∃ y ∈ ys,
    ProperBelow y S ∧ JointCut P S hS y ∧ P.position.stem.done.length + 1 = x
  bodyUsed : ∀ i, ∀ hi : i < T.bodyLabels.length, ∀ j ∈ T.bodyLabels[i],
    ∃ P : Pending, ∃ y ∈ ys, ProperBelow y S ∧ JointCut P S hS y ∧
      P.position.stem.done.length = i ∧ P.position.entries.length = j

theorem project_thresholds (S : Stem) (hS : S.done.length = S.root) (ys : List ℕ)
    (h : ∀ y ∈ ys, ProperBelow y S → ∃ P : Pending, JointCut P S hS y) :
    ∃ T : Stem, ∃ hT : T.done.length = T.root, Projection S hS ys T hT := by
  obtain ⟨cuts, hused, hcover⟩ := finite_joint_cuts S hS ys h
  have hlabels : ∀ P ∈ cuts, LabelsExtend (.pending P) (.terminal S hS) := by
    intro P hP
    obtain ⟨_, _, _, hcut⟩ := hused P hP
    exact hcut.labels
  let T := coarsenStem S (rootKeep cuts) (bodyKeep cuts)
  have hT : T.done.length = T.root := by simpa [T, coarsenStem] using hS
  refine ⟨T, hT, rfl, coarsenStem_ordinary .., coarsenStem_decorated .., ?_, ?_, ?_⟩
  · intro y hy hproper
    obtain ⟨P, hP, hcut⟩ := hcover y hy hproper
    obtain ⟨Q, ho, hd, hQ⟩ := project_joint_cut S hS cuts P hP hcut.labels y
      hcut.ordinary hcut.decorated
    exact ⟨Q, ho, hd, hQ⟩
  · intro x hx
    obtain ⟨P, hP, hindex⟩ := (selected_root_exact S hS cuts hlabels x).mp hx
    obtain ⟨y, hy, hproper, hcut⟩ := hused P hP
    exact ⟨P, y, hy, hproper, hcut, hindex⟩
  · intro i hi j hj
    have hiS : i < S.bodyLabels.length := by
      simpa [T, coarsenStem_labels, filterLabels] using hi
    obtain ⟨P, hP, hiP, hjP⟩ := (selected_body_exact S hS cuts hlabels i hiS j).mp hj
    obtain ⟨y, hy, hproper, hcut⟩ := hused P hP
    exact ⟨P, y, hy, hproper, hcut, hiP, hjP⟩

/-- The actual ordinary coordinates of a different root supply all thresholds.
This theorem projects annotations, not colors. -/
theorem output_pair_projection {H : Set ℕ} (hH : H.Infinite)
    (s t : Negative.G2)
    (hroots : (LabelledRealization.vertex hH s).1.length ≠
      (LabelledRealization.vertex hH t).1.length) :
    ∃ T : Stem, ∃ hT : T.done.length = T.root,
      Projection (LabelledRealization.output hH s).stem (LabelledRealization.output hH s).full
        (LabelledRealization.output hH t).stem.ordinary T hT := by
  apply project_thresholds
  intro y hy hproper
  have hyD := (LabelledRealization.output hH t).stem.ordinary_sublist.subset hy
  obtain ⟨P, ho, hd, hl⟩ :=
    (LabelledRealization.output_properties_of_roots_ne hH s t hroots).2
      y hyD hproper.1 hproper.2
  exact ⟨P, ho, hd, hl⟩

end Erdos118.LabelCoarsening
