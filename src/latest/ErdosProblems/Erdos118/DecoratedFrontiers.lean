import ErdosProblems.Erdos118.CutFrontiers

/-!
Lift ordinary frontier bounds to actual decorated suffixes, using node
separation. Retarget a joint cut at its ordinary boundary without changing
its position or annotations. The global scheduler is still separate.
-/

namespace Erdos118.DecoratedFrontiers

open Negative Negative.Exact LabelledExtensions LabelledFrames LabelCoarsening
open DecisionStates ClearPairs
open PrefixRealization (below)

theorem stem_dominated (S : Stem) (x : ℕ) (hx : x ∈ S.decorated) :
    ∃ y ∈ S.ordinary, x ≤ y := by
  rcases List.mem_append.mp hx with hx | hx
  · exact ⟨S.root, List.mem_cons_self .., (S.label_before_root x hx).le⟩
  · rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨S.root, List.mem_cons_self .., le_rfl⟩
    · obtain ⟨a, ha, hx⟩ := List.mem_flatMap.mp hx
      rcases List.mem_append.mp hx with hx | hx
      · have hb := (List.pairwise_flatMap.mp
          (List.pairwise_cons.mp (List.pairwise_append.mp S.increasing).2.1).2).1 a ha
        have hxm := (List.pairwise_append.mp hb).2.2 x hx a.values.length (List.mem_cons_self ..)
        exact ⟨a.values.length, body_marker_mem S a ha, hxm.le⟩
      · exact ⟨x, List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨a, ha, hx⟩), le_rfl⟩

theorem position_dominated (P : Position) (x : ℕ) (hx : x ∈ P.decorated) :
    ∃ y ∈ P.ordinary, x ≤ y := by
  rcases List.mem_append.mp hx with hx | hx
  · obtain ⟨y, hy, hxy⟩ := stem_dominated P.stem x hx
    exact ⟨y, List.mem_append_left _ hy, hxy⟩
  · rcases List.mem_append.mp hx with hx | hx
    · exact ⟨P.size, List.mem_append_right _ (List.mem_cons_self ..),
        (P.label_before_marker x hx).le⟩
    · exact ⟨x, List.mem_append_right _ hx, le_rfl⟩

theorem state_dominated (W : State) (x : ℕ) (hx : x ∈ W.decorated) :
    ∃ y ∈ W.ordinary, x ≤ y := by
  cases W with
  | initial => simp [State.decorated] at hx
  | body D => exact stem_dominated D.stem x hx
  | leaf P => exact position_dominated P.position x hx
  | complete S => exact stem_dominated S.stem x hx

theorem whole_after_foreign (S T : Stem) (hsep : NodeSeparated S T)
    (y : ℕ) (hy : y ∈ T.ordinary) (hbefore : ∀ x ∈ S.ordinary, y < x) :
    ∀ x ∈ S.decorated, y < x := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact hsep.root y hy (hbefore S.root (List.mem_cons_self ..)) x hx
  · rcases List.mem_cons.mp hx with rfl | hx
    · exact hbefore S.root (List.mem_cons_self ..)
    · obtain ⟨a, ha, hx⟩ := List.mem_flatMap.mp hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hsep.body a ha y hy (hbefore a.values.length (body_marker_mem S a ha)) x hx
      · exact hbefore x (List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨a, ha, hx⟩))

theorem pending_suffix_after_foreign (S T : Stem) (hS : S.done.length = S.root)
    (hsep : NodeSeparated S T) (P : Pending) {t : ℕ} (hP : JointCut P S hS t)
    (v d : List ℕ) (hord : S.ordinary = P.position.ordinary ++ v)
    (hdec : S.decorated = P.position.decorated ++ d)
    (y : ℕ) (hy : y ∈ T.ordinary) (hbefore : ∀ x ∈ v, y < x) :
    ∀ x ∈ d, y < x := by
  have he := cutExtension_of_prefix P S hS hP.labels (by
    rw [hP.decorated]; exact List.takeWhile_prefix _)
  obtain ⟨a, as, hdone, hlabel, hsize, u, hu⟩ := he.bodies
  have hlen : (P.position.entries ++ u).length = P.position.size :=
    (congrArg List.length hu).trans hsize
  have ho : S.ordinary = P.position.ordinary ++ (u ++ as.flatMap Body.ordinary) := by
    simp only [Position.ordinary, Stem.ordinary, he.root, hdone, List.flatMap_append,
      List.flatMap_cons, Body.ordinary, levelWord, ← hu, hlen,
      List.cons_append, List.append_assoc]
  have hd : S.decorated = P.position.decorated ++ (u ++ as.flatMap Body.decorated) := by
    simp only [Position.decorated, Stem.decorated, he.root, he.rootLabel, hdone,
      List.flatMap_append, List.flatMap_cons, Body.decorated, Body.ordinary,
      levelWord, hlabel, ← hu, hlen, List.cons_append, List.append_assoc]
  have hv : v = u ++ as.flatMap Body.ordinary := List.append_cancel_left (hord.symm.trans ho)
  have hd' : d = u ++ as.flatMap Body.decorated := List.append_cancel_left (hdec.symm.trans hd)
  rw [hv] at hbefore
  rw [hd']
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact hbefore x (List.mem_append_left _ hx)
  · obtain ⟨a', ha', hx⟩ := List.mem_flatMap.mp hx
    rcases List.mem_append.mp hx with hx | hx
    · have hm : a'.values.length ∈ u ++ as.flatMap Body.ordinary :=
        List.mem_append_right _ (List.mem_flatMap.mpr ⟨a', ha', List.mem_cons_self ..⟩)
      have haS : a' ∈ S.done := by
        rw [hdone]
        exact List.mem_append_right _ (List.mem_cons_of_mem _ ha')
      exact hsep.body a' haS y hy (hbefore a'.values.length hm) x hx
    · exact hbefore x (List.mem_append_right _ (List.mem_flatMap.mpr ⟨a', ha', hx⟩))

theorem response_after_state (S T : Stem) (hS : S.done.length = S.root)
    (hsep : NodeSeparated S T) (P : Pending) {t : ℕ} (hP : JointCut P S hS t)
    (W : State) (hW : W.ordinary <+: T.ordinary) (v : List ℕ)
    (hord : S.ordinary = P.position.ordinary ++ v)
    (hbefore : ∀ y ∈ W.ordinary, ∀ x ∈ v, y < x)
    (e : List ℕ) (he : P.position.decorated ++ e <+: S.decorated) :
    ∀ y ∈ W.decorated, ∀ x ∈ e, y < x := by
  have hpref : P.position.decorated <+: S.decorated := by
    rw [hP.decorated]
    exact List.takeWhile_prefix _
  obtain ⟨d, hd⟩ := hpref
  have hed : e <+: d := by simpa only [← hd, List.prefix_append_right_inj] using he
  intro y hy x hx
  obtain ⟨z, hz, hyz⟩ := state_dominated W y hy
  exact hyz.trans_lt (pending_suffix_after_foreign S T hS hsep P hP v d hord hd.symm
    z (hW.subset hz) (hbefore z hz) x (hed.subset hx))

theorem joint_cut_retarget (S T : Stem) (hS : S.done.length = S.root)
    (hsep : NodeSeparated S T) (hdis : Disjoint S.decorated.toFinset T.decorated.toFinset)
    (P : Pending) {t : ℕ} (hP : JointCut P S hS t)
    (y : ℕ) (hy : y ∈ T.ordinary) (hord : P.position.ordinary = below y S.ordinary) :
    JointCut P S hS y := by
  have hpref : P.position.ordinary <+: S.ordinary := by
    rw [hord]
    exact List.takeWhile_prefix _
  obtain ⟨v, hv⟩ := hpref
  have hdpref : P.position.decorated <+: S.decorated := by
    rw [hP.decorated]
    exact List.takeWhile_prefix _
  obtain ⟨d, hd⟩ := hdpref
  have hb := below_split_bounds y P.position.ordinary v
    (hv.symm ▸ S.increasing.sublist S.ordinary_sublist) (by rw [hv]; exact hord.symm)
  have hnew : ∀ x ∈ v, y < x := by
    intro x hx
    apply Nat.lt_of_le_of_ne (hb.2 x hx)
    apply foreign_ne hdis hy
    apply S.ordinary_sublist.subset
    rw [← hv]
    exact List.mem_append_right _ hx
  have hnewD := pending_suffix_after_foreign S T hS hsep P hP v d hv.symm hd.symm y hy hnew
  have holdD : ∀ x ∈ P.position.decorated, x < y := by
    intro x hx
    obtain ⟨z, hz, hxz⟩ := position_dominated P.position x hx
    exact hxz.trans_lt (hb.1 z hz)
  have hdinc : (P.position.decorated ++ d).Pairwise (· < ·) := by
    rw [hd]
    exact S.increasing
  have hdnil : below y d = [] :=
    (below_eq_nil_iff y d (List.pairwise_append.mp hdinc).2.1).mpr
      (fun x hx ↦ (hnewD x hx).le)
  refine ⟨hord, ?_, hP.labels⟩
  symm
  rw [← hd]
  simp only [below, List.takeWhile_append_of_pos (fun x hx ↦ decide_eq_true (holdD x hx))]
  change P.position.decorated ++ below y d = P.position.decorated
  rw [hdnil, List.append_nil]

end Erdos118.DecoratedFrontiers
