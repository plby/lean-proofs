import ErdosProblems.Erdos118.FinalCutRun
import ErdosProblems.Erdos118.StemReplay

/-!
Literal decoding of a next selected body and its forced body response.
Exact labels exclude intervening annotated bodies; both actual payloads
retain the final word's decorations. Global chronological scheduling is
not supplied by these local lemmas.
-/

namespace Erdos118.NextBodyCuts

open Negative Negative.Exact LabelledExtensions LabelledFrames LabelCoarsening
open CutIndices DecisionStates

theorem next_root_minimal (S T : Stem) (hS : S.done.length = S.root)
    (hexact : ExactAnnotations S T) (P : Pending) {x : ℕ} (hP : JointCut P S hS x)
    (hslots : ExactSlots.Exact (.leaf P)) (c : ℕ) (rest : List ℕ)
    (hnext : P.roots = c :: rest) (i j : ℕ) (hcut : Cut S T i j)
    (hafter : P.position.stem.done.length < i) : c ≤ i + 1 := by
  have hir : i + 1 ∈ S.rootLabel := (hexact.root (i + 1)).mpr ⟨i, j, hcut, rfl⟩
  have hr : S.rootLabel = P.position.stem.rootLabel :=
    Option.some.inj (hP.labels.root _ rfl)
  have hm : i + 1 ∈ ExactSlots.above P.position.stem.rootLabel
      (P.position.stem.done.length + 1) :=
    List.mem_filter.mpr ⟨hr ▸ hir, decide_eq_true (Nat.add_lt_add_right hafter 1)⟩
  rw [← hslots.1, hnext] at hm
  have hinc : (c :: rest).Pairwise (· < ·) := hnext ▸ P.rootSlots.increasing
  simpa only [List.head_cons] using (hinc.imp Nat.le_of_lt).rel_head hm

theorem between_label_empty (S T : Stem) (hS : S.done.length = S.root)
    (hexact : ExactAnnotations S T) (P : Pending) {x : ℕ} (hP : JointCut P S hS x)
    (hslots : ExactSlots.Exact (.leaf P)) (c : ℕ) (rest : List ℕ)
    (hnext : P.roots = c :: rest) (i : ℕ) (hi : i < S.bodyLabels.length)
    (hafter : P.position.stem.done.length < i) (hbefore : i < c - 1) :
    S.bodyLabels[i] = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro j hj
  have hc := (hexact.body i hi j).mp hj
  have hmin := next_root_minimal S T hS hexact P hP hslots c rest hnext i j hc hafter
  omega

private theorem stem_ext (S T : Stem) (hr : S.root = T.root)
    (hc : S.rootLabel = T.rootLabel) (hd : S.done = T.done) : S = T := by
  cases S
  cases T
  cases hr
  cases hc
  cases hd
  rfl

theorem stem_eq_of_ordinary_labels (S T : Stem) (ho : S.ordinary = T.ordinary)
    (hr : S.rootLabel = T.rootLabel) (hb : S.bodyLabels = T.bodyLabels) : S = T := by
  have he : S.root = T.root ∧ S.done.flatMap Body.ordinary = T.done.flatMap Body.ordinary :=
    List.cons.inj ho
  have hlen : (S.done.map Body.values).length = (T.done.map Body.values).length := by
    simpa only [Stem.bodyLabels, List.length_map] using congrArg List.length hb
  have hv : S.done.map Body.values = T.done.map Body.values := by
    apply WordResponses.flatMap_prefix_rigid hlen
    rw [List.flatMap_map, List.flatMap_map]
    change S.done.flatMap Body.ordinary <+: T.done.flatMap Body.ordinary
    rw [he.2]
  exact stem_ext S T he.1 hr (StemResponses.bodies_eq_of_projections hv hb)

theorem earlier_stem_extension {P Q : Pending} {S : Stem} {hS : S.done.length = S.root}
    {x y : ℕ} (hP : JointCut P S hS x) (hQ : JointCut Q S hS y)
    (hmore : P.position.stem.done.length < Q.position.stem.done.length) :
    Q.position.stem.root = P.position.stem.root ∧
      Q.position.stem.rootLabel = P.position.stem.rootLabel ∧
      P.position.ordinary <+: Q.position.stem.ordinary := by
  have hpe := cutExtension_of_prefix P S hS hP.labels (by
    rw [hP.decorated]; exact List.takeWhile_prefix _)
  have hqe := cutExtension_of_prefix Q S hS hQ.labels (by
    rw [hQ.decorated]; exact List.takeWhile_prefix _)
  obtain ⟨a, as, hpd, _, hpn, hpu⟩ := hpe.bodies
  obtain ⟨d, ds, hqd, _⟩ := hqe.bodies
  have hpref : P.position.stem.done ++ [a] <+: S.done := by
    refine ⟨as, ?_⟩
    simpa only [List.append_assoc, List.singleton_append] using hpd.symm
  have hqref : Q.position.stem.done <+: S.done := ⟨d :: ds, hqd.symm⟩
  have hpreq : P.position.stem.done ++ [a] <+: Q.position.stem.done :=
    List.prefix_of_prefix_length_le hpref hqref (by
      simp only [List.length_append, List.length_singleton]
      omega)
  obtain ⟨qs, hqs⟩ := hpreq
  have hdone : Q.position.stem.done = P.position.stem.done ++ a :: qs := by
    simpa only [List.append_assoc, List.singleton_append] using hqs.symm
  obtain ⟨v, hv⟩ := hpu
  have hnv : (P.position.entries ++ v).length = P.position.size :=
    (congrArg List.length hv).trans hpn
  have hroot : Q.position.stem.root = P.position.stem.root := hqe.root.symm.trans hpe.root
  refine ⟨hroot, hqe.rootLabel.symm.trans hpe.rootLabel, v ++ qs.flatMap Body.ordinary, ?_⟩
  simp only [Position.ordinary, Stem.ordinary, hroot, hdone, List.flatMap_append,
    List.flatMap_cons, Body.ordinary, levelWord, ← hv, hnv,
    List.cons_append, List.append_assoc]

theorem intermediate_labels (S T : Stem) (hS : S.done.length = S.root)
    (hexact : ExactAnnotations S T) (P Q : Pending) {x y : ℕ}
    (hP : JointCut P S hS x) (hQ : JointCut Q S hS y)
    (hslots : ExactSlots.Exact (.leaf P)) (c : ℕ) (rest : List ℕ)
    (hnext : P.roots = c :: rest) (hcount : Q.position.stem.done.length = c - 1) :
    Q.position.stem.bodyLabels = P.position.bodyLabels ++
      List.replicate (c - 1 - (P.position.stem.done.length + 1)) [] := by
  have hpref : P.position.bodyLabels <+: S.bodyLabels := hP.labels.bodies
  have hqref : Q.position.stem.bodyLabels <+: S.bodyLabels :=
    (List.prefix_append Q.position.stem.bodyLabels [Q.position.label]).trans hQ.labels.bodies
  have hlenPQ : P.position.bodyLabels.length ≤ Q.position.stem.bodyLabels.length := by
    simp only [Position.bodyLabels, Stem.bodyLabels, List.length_append,
      List.length_map, List.length_singleton, hcount]
    exact (next_body_bounds P c rest hnext).1
  obtain ⟨ds, hds⟩ := List.prefix_of_prefix_length_le hpref hqref hlenPQ
  have hlen : ds.length = c - 1 - (P.position.stem.done.length + 1) := by
    have he := congrArg List.length hds
    simp only [List.length_append, Position.bodyLabels, Stem.bodyLabels,
      List.length_map, List.length_singleton, hcount] at he
    omega
  have hd : ∀ D ∈ ds, D = [] := by
    intro D hD
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hD
    let k := P.position.bodyLabels.length + i
    have hkQ : k < Q.position.stem.bodyLabels.length := by
      rw [← hds, List.length_append]
      exact Nat.add_lt_add_left hi _
    have hkS := hkQ.trans_le hqref.length_le
    have hafter : P.position.stem.done.length < k := by
      simp only [k, Position.bodyLabels, Stem.bodyLabels, List.length_append,
        List.length_map, List.length_singleton]
      omega
    have hbefore : k < c - 1 := by simpa only [Stem.bodyLabels, List.length_map, hcount] using hkQ
    have he := between_label_empty S T hS hexact P hP hslots c rest hnext k hkS hafter hbefore
    rw [← hqref.getElem hkQ] at he
    simpa only [← hds, k, List.getElem_append_right (Nat.le_add_right _ _),
      Nat.add_sub_cancel_left] using he
  rw [← hds, List.eq_replicate_of_mem hd, hlen]

theorem next_stem_setup (S T : Stem) (hS : S.done.length = S.root)
    (hexact : ExactAnnotations S T) (P Q : Pending) {x y : ℕ}
    (hP : JointCut P S hS x) (hQ : JointCut Q S hS y)
    (hslots : ExactSlots.Exact (.leaf P)) (c : ℕ) (rest : List ℕ)
    (hnext : P.roots = c :: rest) (hcount : Q.position.stem.done.length = c - 1) :
    ∃ A : StemResponses.Setup P.position (c - 1), A.stem = Q.position.stem := by
  have hmore : P.position.stem.done.length < Q.position.stem.done.length := by
    rw [hcount]
    exact (next_body_bounds P c rest hnext).1
  obtain ⟨hr, hC, v, hv⟩ := earlier_stem_extension hP hQ hmore
  obtain ⟨A, _, ho⟩ := CompletionReplay.setup_of_literal_stem P.position Q.position.stem
    (c - 1) hr hcount (next_body_bounds P c rest hnext).1 v hv.symm
  refine ⟨A, stem_eq_of_ordinary_labels A.stem Q.position.stem ho
    (A.rootLabel_eq.trans hC.symm) ?_⟩
  rw [A.labels, intermediate_labels S T hS hexact P Q hP hQ hslots c rest hnext hcount]

theorem first_cut_at_body (S T : Stem) (hS : S.done.length = S.root)
    (hexact : ExactAnnotations S T)
    (hcuts : ∀ y ∈ T.ordinary, ProperBelow y S → ∃ Q : Pending, JointCut Q S hS y)
    (c : ℕ) (hc : c ∈ S.rootLabel) :
    ∃ y ∈ T.ordinary, ∃ Q : Pending, JointCut Q S hS y ∧
      Q.position.stem.done.length = c - 1 ∧
      Q.position.entries.length = Q.position.label.headD 0 := by
  obtain ⟨i, j, hcij, hic⟩ := (hexact.root c).mp hc
  have hi : i < S.bodyLabels.length := by
    have hcr := S.label_before_root c hc
    simp only [Stem.bodyLabels, List.length_map, hS]
    omega
  have hj := (hexact.body i hi j).mpr hcij
  have hne : S.bodyLabels[i] ≠ [] := List.ne_nil_of_mem hj
  have hfirst := (hexact.body i hi (S.bodyLabels[i].headD 0)).mp (first_mem hne)
  obtain ⟨y, hy, hp, I, hI, hIi, hIj⟩ := hfirst
  obtain ⟨Q, hQ⟩ := hcuts y hy hp
  have hind := jointCut_indices hQ hI
  have hiQ : Q.position.stem.done.length = i := hind.1.symm.trans hIi
  have hjQ : Q.position.entries.length = S.bodyLabels[i].headD 0 := hind.2.symm.trans hIj
  have hlabels : Q.position.bodyLabels <+: S.bodyLabels := hQ.labels.bodies
  have hiQmem : Q.position.stem.done.length < Q.position.bodyLabels.length := by
    simp [Position.bodyLabels, Stem.bodyLabels]
  have he : S.bodyLabels[Q.position.stem.done.length] = Q.position.label := by
    rw [← hlabels.getElem hiQmem]
    simp [Position.bodyLabels, Stem.bodyLabels]
  have he' : S.bodyLabels[i] = Q.position.label := by simpa only [hiQ] using he
  refine ⟨y, hy, Q, hQ, ?_, ?_⟩
  · omega
  · rw [hjQ, he']

theorem retained_body (S T : Stem) (hS : S.done.length = S.root)
    (hexact : ExactAnnotations S T)
    (hcuts : ∀ y ∈ T.ordinary, ProperBelow y S → ∃ Q : Pending, JointCut Q S hS y)
    (P : Pending) {x : ℕ} (hP : JointCut P S hS x)
    (hslots : ExactSlots.Exact (.leaf P)) (c : ℕ) (rest : List ℕ)
    (hnext : P.roots = c :: rest) (hleaves : P.leaves = []) :
    ∃ y ∈ T.ordinary, ∃ A : StemResponses.Setup P.position (c - 1),
      ∃ n : ℕ, ∃ Q : BodyResponses.Setup A.stem n,
        JointCut (applyBody (ofStem P c rest hnext A) Q) S hS y ∧
        ExactSlots.Exact (.leaf (applyBody (ofStem P c rest hnext A) Q)) := by
  have hslot := P.rootSlots.bounded c (hnext ▸ List.mem_cons_self ..)
  have hC : S.rootLabel = P.position.stem.rootLabel :=
    Option.some.inj (hP.labels.root _ rfl)
  have hcS : c ∈ S.rootLabel := hC ▸ hslot.2.2
  obtain ⟨y, hy, F, hF, hcount, hhead⟩ := first_cut_at_body S T hS hexact hcuts c hcS
  obtain ⟨A, hA⟩ := next_stem_setup S T hS hexact P F hP hF hslots c rest hnext hcount
  let n := F.position.label.length - 1
  have hpos : 0 < F.position.label.length :=
    List.length_pos_iff.mpr (List.ne_nil_of_mem F.leafSelected)
  let Q : BodyResponses.Setup A.stem n :=
    { position := F.position, stem_eq := hA.symm
      label_length := by dsimp [n]; omega
      entries_length := hhead }
  refine ⟨y, hy, A, n, Q, ?_, ?_⟩
  · exact InitialSplit.jointCut_of_position_eq (P := F) rfl hF
  · exact ExactSlots.step_exact (DecisionStates.Step.body (ofStem P c rest hnext A) Q)
      (ExactSlots.step_exact (DecisionStates.Step.nextBody P c rest hnext hleaves A) hslots)

end Erdos118.NextBodyCuts
