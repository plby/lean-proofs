import ErdosProblems.Erdos118.CutIndices

/-!
Native clear-pair geometry for height-two words. Joint threshold cuts keep
every node label wholly on the same side of a foreign ordinary coordinate
as its marker. Both projected chronological outputs satisfy this condition.
No coloring, game certificate, or partition theorem is assumed.
-/

namespace Erdos118.ClearPairs

open Negative Negative.Exact LabelledExtensions LabelledFrames LabelCoarsening
open PrefixRealization (below)
open CutIndices

theorem frame_empty_decorated (F : Frame) (h : F.ordinary = []) : F.decorated = [] := by
  cases F <;> simp_all [Frame.ordinary, Frame.decorated, Position.ordinary, Stem.ordinary]

theorem below_eq_nil_iff (y : ℕ) (xs : List ℕ) (hxs : xs.Pairwise (· < ·)) :
    below y xs = [] ↔ ∀ x ∈ xs, y ≤ x := by
  constructor
  · intro h
    exact (below_split_bounds y [] xs hxs h).2
  · intro h
    cases xs with
    | nil => rfl
    | cons x xs =>
      have hxy : ¬ x < y := Nat.not_lt.mpr (h x (List.mem_cons_self ..))
      simp [below, hxy]

theorem below_sublist_empty {xs ys : List ℕ} (hys : ys.Pairwise (· < ·))
    (hsub : xs.Sublist ys) {y : ℕ} (h : below y ys = []) : below y xs = [] := by
  apply (below_eq_nil_iff y xs (hys.sublist hsub)).mpr
  exact fun x hx ↦ (below_eq_nil_iff y ys hys).mp h x (hsub.subset hx)

theorem output_empty_cut {H : Set ℕ} (hH : H.Infinite) (s t : G2)
    (hroots : s.length ≠ t.length) {y : ℕ}
    (hy : y ∈ (LabelledRealization.output hH t).stem.decorated)
    (hempty : below y (LabelledRealization.output hH s).stem.ordinary = []) :
    below y (LabelledRealization.output hH s).stem.decorated = [] := by
  let p := word s ++ [0]
  let q := word t ++ [0]
  have hp : PrefixRealization.Phase.root.run p ≠ .dead := by
    simp [p, PrefixRealization.run_word_terminal]
  have hq : PrefixRealization.Phase.root.run q ≠ .dead := by
    simp [q, PrefixRealization.run_word_terminal]
  have hheads : p.head? ≠ q.head? := by simpa [p, q, word] using hroots
  have hy' : y ∈ (LabelledRealization.frame hH q).decorated := by
    simpa [q, LabelledRealization.output_decorated] using hy
  obtain ⟨r, _, hro, hrd⟩ := LabelledRealization.below_frame_prefix_joint hH p y hp
    (fun r a hra hrLive ↦ LabelledRealization.block_separated_from_coordinate
      hH p q hheads hq hy' r a hra hrLive)
  have he : (LabelledRealization.frame hH r).ordinary = [] := by
    rw [← LabelledRealization.output_ordinary] at hro
    exact hro.trans hempty
  rw [LabelledRealization.output_decorated]
  exact hrd.symm.trans (frame_empty_decorated _ he)

def EmptyCuts (S T : Stem) : Prop :=
  ∀ y ∈ T.ordinary, below y S.ordinary = [] → below y S.decorated = []

def JointCuts (S : Stem) (hS : S.done.length = S.root) (T : Stem) : Prop :=
  ∀ y ∈ T.ordinary, ProperBelow y S → ∃ P : Pending, JointCut P S hS y

structure NodeSeparated (S T : Stem) : Prop where
  root : ∀ y ∈ T.ordinary, y < S.root → ∀ d ∈ S.rootLabel, y < d
  body : ∀ a ∈ S.done, ∀ y ∈ T.ordinary, y < a.values.length → ∀ d ∈ a.label, y < d

theorem body_marker_mem (S : Stem) (a : Body) (ha : a ∈ S.done) :
    a.values.length ∈ S.ordinary := by
  apply List.mem_cons_of_mem
  exact List.mem_flatMap.mpr ⟨a, ha, List.mem_cons_self ..⟩

theorem body_label_mem (S : Stem) (a : Body) (ha : a ∈ S.done) {d : ℕ}
    (hd : d ∈ a.label) : d ∈ S.decorated := by
  apply List.mem_append_right
  apply List.mem_cons_of_mem
  exact List.mem_flatMap.mpr ⟨a, ha, List.mem_append_left _ hd⟩

theorem foreign_ne {S T : Stem} (hdis : Disjoint S.decorated.toFinset T.decorated.toFinset)
    {y d : ℕ} (hy : y ∈ T.ordinary) (hd : d ∈ S.decorated) : y ≠ d := by
  intro he
  subst d
  exact Finset.disjoint_left.mp hdis (List.mem_toFinset.mpr hd)
    (List.mem_toFinset.mpr (T.ordinary_sublist.subset hy))

theorem jointCut_body_separated {P : Pending} {S : Stem} {hS : S.done.length = S.root}
    {y : ℕ} (hcut : JointCut P S hS y) (a : Body) (ha : a ∈ S.done)
    (hym : y < a.values.length) : ∀ d ∈ a.label, y ≤ d := by
  have hprefix : P.position.decorated <+: S.decorated := by
    rw [hcut.decorated]
    exact List.takeWhile_prefix _
  have h := cutExtension_of_prefix P S hS hcut.labels hprefix
  obtain ⟨b, rest, hdone, hD, hlen, tail, hentries⟩ := h.bodies
  have hsize : (P.position.entries ++ tail).length = P.position.size := by
    rw [hentries, hlen]
  have hsplit : S.decorated = P.position.decorated ++
      (tail ++ rest.flatMap Body.decorated) := by
    simp only [Stem.decorated, Position.decorated, h.root, h.rootLabel, hdone,
      List.flatMap_append, List.flatMap_cons, Body.decorated, Body.ordinary,
      levelWord, hD, ← hentries, hsize, List.cons_append, List.append_assoc]
  have hbounds := below_split_bounds y P.position.decorated
    (tail ++ rest.flatMap Body.decorated) (hsplit ▸ S.increasing)
    (by rw [← hsplit]; exact hcut.decorated.symm)
  rw [hdone] at ha
  rcases List.mem_append.mp ha with ha | ha
  · have hm : a.values.length ∈ P.position.ordinary :=
      List.mem_append_left _ (body_marker_mem P.position.stem a ha)
    rw [hcut.ordinary] at hm
    have hmy : a.values.length < y :=
      of_decide_eq_true (List.mem_takeWhile_imp (p := fun z ↦ decide (z < y)) hm)
    omega
  · rcases List.mem_cons.mp ha with rfl | ha
    · have hm : P.position.size ∈ P.position.ordinary :=
        List.mem_append_right _ (List.mem_cons_self ..)
      rw [hcut.ordinary] at hm
      have hmy : P.position.size < y :=
        of_decide_eq_true (List.mem_takeWhile_imp (p := fun z ↦ decide (z < y)) hm)
      omega
    · intro d hd
      exact hbounds.2 d (List.mem_append_right _
        (List.mem_flatMap.mpr ⟨a, ha, List.mem_append_left _ hd⟩))

theorem nodeSeparated_of_cuts {S T : Stem} (hS : S.done.length = S.root)
    (hdis : Disjoint S.decorated.toFinset T.decorated.toFinset)
    (hempty : EmptyCuts S T) (hcuts : JointCuts S hS T) : NodeSeparated S T := by
  constructor
  · intro y hy hym d hd
    have ho : below y S.ordinary = [] := by
      simp [below, Stem.ordinary, Nat.not_lt.mpr hym.le]
    have hge := (below_eq_nil_iff y S.decorated S.increasing).mp (hempty y hy ho)
      d (List.mem_append_left _ hd)
    exact Nat.lt_of_le_of_ne hge (foreign_ne hdis hy (List.mem_append_left _ hd))
  · intro a ha y hy hym d hd
    have hge : y ≤ d := by
      by_cases ho : below y S.ordinary = []
      · exact (below_eq_nil_iff y S.decorated S.increasing).mp (hempty y hy ho)
          d (body_label_mem S a ha hd)
      · have hproper : below y S.ordinary ≠ S.ordinary := by
          intro he
          have hm := body_marker_mem S a ha
          rw [← he] at hm
          have hmy : a.values.length < y :=
            of_decide_eq_true (List.mem_takeWhile_imp (p := fun z ↦ decide (z < y)) hm)
          omega
        obtain ⟨P, hP⟩ := hcuts y hy ⟨ho, hproper⟩
        exact jointCut_body_separated hP a ha hym d hd
    exact Nat.lt_of_le_of_ne hge (foreign_ne hdis hy (body_label_mem S a ha hd))

theorem projection_emptyCuts {S T U : Stem} {hS : S.done.length = S.root}
    {hU : U.done.length = U.root} (A : Projection S hS T.ordinary U hU)
    (h : EmptyCuts S T) : EmptyCuts U T := by
  intro y hy hempty
  rw [A.ordinary] at hempty
  exact below_sublist_empty S.increasing A.decorated (h y hy hempty)

theorem emptyCuts_congr_other {S T T' : Stem} (hT : T'.ordinary = T.ordinary)
    (h : EmptyCuts S T) : EmptyCuts S T' := by
  simpa only [EmptyCuts, hT] using h

structure ClearPair (S T : Stem) : Prop where
  disjoint : Disjoint S.decorated.toFinset T.decorated.toFinset
  interiorLeft : InteriorCuts S T
  interiorRight : InteriorCuts T S
  exactLeft : ExactAnnotations S T
  exactRight : ExactAnnotations T S
  separatedLeft : NodeSeparated S T
  separatedRight : NodeSeparated T S

theorem ClearPair.symm {S T : Stem} (h : ClearPair S T) : ClearPair T S :=
  ⟨h.disjoint.symm, h.interiorRight, h.interiorLeft, h.exactRight, h.exactLeft,
    h.separatedRight, h.separatedLeft⟩

theorem ClearPair.roots_ne {S T : Stem} (h : ClearPair S T) : S.root ≠ T.root := by
  exact (foreign_ne h.disjoint (List.mem_cons_self ..)
    (List.mem_append_right _ (List.mem_cons_self ..))).symm

theorem clearPair_of_projections {S T U V : Stem}
    {hS : S.done.length = S.root} {hT : T.done.length = T.root}
    {hU : U.done.length = U.root} {hV : V.done.length = V.root}
    (A : Projection S hS T.ordinary U hU) (B : Projection T hT S.ordinary V hV)
    (hdis : Disjoint S.decorated.toFinset T.decorated.toFinset)
    (hST : EmptyCuts S T) (hTS : EmptyCuts T S) : ClearPair U V := by
  have hUsub : U.decorated.toFinset ⊆ S.decorated.toFinset :=
    fun x hx ↦ List.mem_toFinset.mpr (A.decorated.subset (List.mem_toFinset.mp hx))
  have hVsub : V.decorated.toFinset ⊆ T.decorated.toFinset :=
    fun x hx ↦ List.mem_toFinset.mpr (B.decorated.subset (List.mem_toFinset.mp hx))
  have hd := hdis.mono hUsub hVsub
  refine ⟨hd, interiorCuts_congr_other B.ordinary (projection_interior A),
    interiorCuts_congr_other A.ordinary (projection_interior B),
    exactAnnotations_congr_other B.ordinary (projection_exact A),
    exactAnnotations_congr_other A.ordinary (projection_exact B), ?_, ?_⟩
  · apply nodeSeparated_of_cuts hU hd
      (emptyCuts_congr_other B.ordinary (projection_emptyCuts A hST))
    intro y hy hp
    rw [B.ordinary] at hy
    have hpS : ProperBelow y S := by simpa only [ProperBelow, A.ordinary] using hp
    exact A.cuts y hy hpS
  · apply nodeSeparated_of_cuts hV hd.symm
      (emptyCuts_congr_other A.ordinary (projection_emptyCuts B hTS))
    intro y hy hp
    rw [A.ordinary] at hy
    have hpT : ProperBelow y T := by simpa only [ProperBelow, B.ordinary] using hp
    exact B.cuts y hy hpT

/-- The original words are unchanged; every clear-pair geometric condition
is proved for their projected annotations, in both directions. -/
theorem output_pair_clear {H : Set ℕ} (hH : H.Infinite) (s t : G2)
    (hroots : (LabelledRealization.vertex hH s).1.length ≠
      (LabelledRealization.vertex hH t).1.length) :
    ∃ U : Stem, ∃ _hU : U.done.length = U.root, ∃ V : Stem, ∃ _hV : V.done.length = V.root,
      U.root = (LabelledRealization.output hH s).stem.root ∧
      V.root = (LabelledRealization.output hH t).stem.root ∧
      U.ordinary = (LabelledRealization.output hH s).stem.ordinary ∧
      V.ordinary = (LabelledRealization.output hH t).stem.ordinary ∧ ClearPair U V := by
  obtain ⟨U, hU, hPU⟩ := output_pair_projection hH s t hroots
  obtain ⟨V, hV, hPV⟩ := output_pair_projection hH t s hroots.symm
  have hst : s.length ≠ t.length :=
    fun he ↦ hroots (LabelledRealization.vertex_root_eq_of_length_eq hH s t he)
  refine ⟨U, hU, V, hV, hPU.root, hPV.root, hPU.ordinary, hPV.ordinary,
    clearPair_of_projections hPU hPV
      (LabelledRealization.output_decorated_disjoint hH s t hst) ?_ ?_⟩
  · intro y hy hempty
    exact output_empty_cut hH s t hst
      ((LabelledRealization.output hH t).stem.ordinary_sublist.subset hy) hempty
  · intro y hy hempty
    exact output_empty_cut hH t s hst.symm
      ((LabelledRealization.output hH s).stem.ordinary_sublist.subset hy) hempty

end Erdos118.ClearPairs
