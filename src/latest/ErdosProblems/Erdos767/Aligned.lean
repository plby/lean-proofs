import ErdosProblems.Erdos58.Menger

namespace E767AlignedAlt

open SimpleGraph

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V}

/-- `q` meets the vertices of the oriented path `p` in their `p`-order.

The filtered-sublist presentation is equivalent to the usual pairwise
"appears before" definition for simple paths, but behaves substantially
better under taking prefixes and suffixes. -/
def Aligned {x y a b : V} (p : G.Walk x y) (q : G.Walk a b) : Prop :=
  (q.support.filter fun v => v ∈ p.support).Sublist p.support

@[simp] lemma filter_mem_self (l : List V) :
    l.filter (fun v => v ∈ l) = l := by
  apply List.filter_eq_self.mpr
  simp

lemma aligned_refl {x y : V} (p : G.Walk x y) : Aligned p p := by
  simp [Aligned]

/-- Taking a sublist of the second path preserves alignment. -/
lemma aligned_of_support_sublist {x y a b c d : V}
    {p : G.Walk x y} {q : G.Walk a b} {r : G.Walk c d}
    (hq : Aligned p q) (hrq : r.support.Sublist q.support) :
    Aligned p r := by
  exact (hrq.filter _).trans hq

lemma aligned_takeUntil {x y a b u : V}
    {p : G.Walk x y} {q : G.Walk a b} (hq : Aligned p q)
    (hu : u ∈ q.support) : Aligned p (q.takeUntil u hu) := by
  apply aligned_of_support_sublist hq
  exact q.support_takeUntil_prefix_support hu |>.sublist

lemma aligned_dropUntil {x y a b u : V}
    {p : G.Walk x y} {q : G.Walk a b} (hq : Aligned p q)
    (hu : u ∈ q.support) : Aligned p (q.dropUntil u hu) := by
  apply aligned_of_support_sublist hq
  exact q.support_dropUntil_suffix_support hu |>.sublist

lemma isPath_append_of_disjoint_tail {a b c : V}
    {p : G.Walk a b} {q : G.Walk b c}
    (hp : p.IsPath) (hq : q.IsPath)
    (hd : p.support.Disjoint q.support.tail) :
    (p.append q).IsPath := by
  rw [Walk.isPath_def, Walk.support_append]
  exact List.Nodup.append hp.support_nodup hq.support_nodup.tail hd

lemma isPath_append_dropUntil_of_first_hit {a b c u : V}
    {p : G.Walk a u} {q : G.Walk b c}
    (hp : p.IsPath) (hq : q.IsPath) (hu : u ∈ q.support)
    (hfirst : ∀ v, v ∈ q.support → v ∈ p.support → v = u) :
    (p.append (q.dropUntil u hu)).IsPath := by
  apply isPath_append_of_disjoint_tail hp (hq.dropUntil hu)
  rw [List.disjoint_left]
  intro v hvp hvqtail
  have hvqdrop : v ∈ (q.dropUntil u hu).support := List.mem_of_mem_tail hvqtail
  have hvq : v ∈ q.support := q.support_dropUntil_subset_support hu hvqdrop
  have hvu : v = u := hfirst v hvq hvp
  subst v
  exact (hq.dropUntil hu).support_nodup.rel_head_tail hvqtail (by simp)

lemma filter_eq_ite_singleton_of_nodup_of_forall_eq
    (l : List V) (s : V → Prop) [DecidablePred s] (u : V)
    (hl : l.Nodup) (honly : ∀ v, v ∈ l → s v → v = u) :
    l.filter s = if u ∈ l ∧ s u then [u] else [] := by
  induction l with
  | nil => simp
  | cons a l ih =>
      have hnodup := List.nodup_cons.mp hl
      have ih' := ih hnodup.2 (fun v hv hsv ↦ honly v (by simp [hv]) hsv)
      by_cases hsa : s a
      · have hau : a = u := honly a (by simp) hsa
        subst a
        have hul : u ∉ l := hnodup.1
        simp [hsa, hul, ih']
      · simp only [List.filter_cons, hsa, ↓reduceIte, ih']
        by_cases hu : u ∈ l ∧ s u
        · have huna : u ≠ a := by
            intro hua
            exact hsa (hua ▸ hu.2)
          simp [hu, huna]
        · by_cases hua : u = a
          · subst a
            simp [hu, hsa]
          · simp [hu, hua]

/-- Adding the common initial edge to both the reference path and an aligned
path preserves alignment, provided the new initial vertex is genuinely new. -/
lemma aligned_cons {x v y b : V} {h : G.Adj x v}
    {p : G.Walk v y} {q : G.Walk v b}
    (hxp : x ∉ p.support) (hxq : x ∉ q.support) (hq : Aligned p q) :
    Aligned (Walk.cons h p) (Walk.cons h q) := by
  unfold Aligned at hq ⊢
  have hfilter :
      (Walk.cons h q).support.filter
          (fun w => w ∈ (Walk.cons h p).support) =
        x :: q.support.filter (fun w => w ∈ p.support) := by
    simp only [Walk.support_cons, List.filter_cons]
    rw [if_pos (by simp)]
    congr 1
    apply List.filter_congr
    intro w hw
    simp only [List.mem_cons]
    have hwne : w ≠ x := by
      intro hwx
      exact hxq (hwx ▸ hw)
    simp [hwne]
  rw [hfilter, Walk.support_cons]
  exact hq.cons_cons x

/-- A path aligned with the tail remains aligned with the whole reference
path when the removed first vertex is absent from it. -/
lemma aligned_cons_reference {x v y a b : V} {h : G.Adj x v}
    {p : G.Walk v y} {q : G.Walk a b}
    (hxq : x ∉ q.support) (hq : Aligned p q) :
    Aligned (Walk.cons h p) q := by
  unfold Aligned at hq ⊢
  have hfilter :
      q.support.filter (fun w => w ∈ (Walk.cons h p).support) =
        q.support.filter (fun w => w ∈ p.support) := by
    apply List.filter_congr
    intro w hw
    simp only [Walk.support_cons, List.mem_cons]
    have hwne : w ≠ x := by
      intro hwx
      exact hxq (hwx ▸ hw)
    simp [hwne]
  rw [hfilter, Walk.support_cons]
  exact hq.cons x

/-- If a new reference initial vertex is also the initial vertex of `q`,
then it may be added in front of a path already aligned with the reference
tail. -/
lemma aligned_cons_left {x v y b : V} {h : G.Adj x v}
    {p : G.Walk v y} {q : G.Walk x b}
    (hxp : x ∉ p.support) (hxq : x ∉ q.support.tail)
    (hq : Aligned p q) :
    Aligned (Walk.cons h p) q := by
  unfold Aligned at hq ⊢
  have hfilter :
      q.support.filter (fun w => w ∈ (Walk.cons h p).support) =
        x :: q.support.filter (fun w => w ∈ p.support) := by
    conv_lhs => rw [← q.cons_tail_support]
    conv_rhs => rw [← q.cons_tail_support]
    simp only [Walk.support_cons, List.filter_cons]
    rw [if_pos (by simp), if_neg (by simpa using hxp)]
    congr 1
    apply List.filter_congr
    intro w hw
    simp only [List.mem_cons]
    have hwne : w ≠ x := by
      intro h
      exact hxq (h ▸ hw)
    simp [hwne]
  rw [hfilter, Walk.support_cons]
  exact hq.cons_cons x

/-- Alignment of the Case-2 splice: a path from the new root which first
meets the old reference path at its endpoint is followed by the suffix of an
already aligned branch through that endpoint. -/
lemma aligned_cons_append_dropUntil_of_first_hit
    {x v y b u : V} {h : G.Adj x v}
    {p : G.Walk v y} {q : G.Walk x u} {r : G.Walk v b}
    (hxp : x ∉ p.support) (hxr : x ∉ r.support)
    (hq : q.IsPath) (hr : Aligned p r) (hu : u ∈ r.support)
    (hfirstP : ∀ w, w ∈ p.support → w ∈ q.support → w = u) :
    Aligned (Walk.cons h p) (q.append (r.dropUntil u hu)) := by
  let d := r.dropUntil u hu
  have hd : Aligned p d := aligned_dropUntil hr hu
  have hqd :
      q.support.filter (fun w => w ∈ p.support) =
        if u ∈ p.support then [u] else [] := by
    have hf := filter_eq_ite_singleton_of_nodup_of_forall_eq
      q.support (fun w => w ∈ p.support) u hq.support_nodup
      (fun w hwq hwp => hfirstP w hwp hwq)
    simpa using hf
  have hqfull :
      q.support.filter (fun w => w ∈ (Walk.cons h p).support) =
        x :: (if u ∈ p.support then [u] else []) := by
    rw [← q.cons_tail_support, List.filter_cons]
    rw [if_pos (by simp)]
    have hxqt : x ∉ q.support.tail := by
      intro hx
      have hne := hq.support_nodup.rel_head_tail hx
      exact hne (by simpa only [q.head_support])
    have htailFull :
        q.support.tail.filter (fun w => w ∈ (Walk.cons h p).support) =
          q.support.tail.filter (fun w => w ∈ p.support) := by
      apply List.filter_congr
      intro w hw
      simp only [Walk.support_cons, List.mem_cons]
      have hwne : w ≠ x := by
        intro hwx
        exact hxqt (hwx ▸ hw)
      simp [hwne]
    rw [htailFull]
    have htailP :
        q.support.tail.filter (fun w => w ∈ p.support) =
          q.support.filter (fun w => w ∈ p.support) := by
      have hs :
          (x :: q.support.tail).filter (fun w => w ∈ p.support) =
            q.support.filter (fun w => w ∈ p.support) := congrArg
        (fun l : List V => l.filter (fun w => w ∈ p.support))
        q.cons_tail_support
      have hskip :
          (x :: q.support.tail).filter (fun w => w ∈ p.support) =
            q.support.tail.filter (fun w => w ∈ p.support) := by
        simp only [List.filter_cons]
        rw [if_neg (by simpa using hxp)]
      exact hskip.symm.trans hs
    rw [htailP, hqd]
  have hxdt : x ∉ d.support.tail := by
    intro hx
    exact hxr (r.support_dropUntil_subset_support hu (List.mem_of_mem_tail hx))
  have hdtail :
      d.support.tail.filter (fun w => w ∈ (Walk.cons h p).support) =
        d.support.tail.filter (fun w => w ∈ p.support) := by
    apply List.filter_congr
    intro w hw
    simp only [Walk.support_cons, List.mem_cons]
    have hwne : w ≠ x := by
      intro hwx
      exact hxdt (hwx ▸ hw)
    simp [hwne]
  unfold Aligned at hd ⊢
  rw [Walk.support_append, List.filter_append, hqfull, hdtail,
    Walk.support_cons]
  change
    (x :: ((if u ∈ p.support then [u] else []) ++
      d.support.tail.filter (fun w => w ∈ p.support))).Sublist
      (x :: p.support)
  apply List.Sublist.cons_cons
  have hdSupport :
      d.support.filter (fun w => w ∈ p.support) =
        (if u ∈ p.support then [u] else []) ++
          d.support.tail.filter (fun w => w ∈ p.support) := by
    conv_lhs => rw [← d.cons_tail_support]
    simp only [List.filter_cons]
    by_cases hup : u ∈ p.support <;> simp [hup]
  rw [← hdSupport]
  exact hd

lemma start_not_mem_dropUntil_of_ne {v y u : V} {p : G.Walk v y}
    (hp : p.IsPath) (hu : u ∈ p.support) (huv : u ≠ v) :
    v ∉ (p.dropUntil u hu).support := by
  intro hv
  obtain ⟨t, ht⟩ := p.support_dropUntil_suffix_support hu
  have hnd : (t ++ (p.dropUntil u hu).support).Nodup := by
    rw [ht]
    exact hp.support_nodup
  have hsep := (List.nodup_append.mp hnd).2.2
  cases t with
  | nil =>
      have hs : (p.dropUntil u hu).support = p.support := by simpa using ht
      have huv' : u = v := by
        calc
          u = (p.dropUntil u hu).support.head
              (p.dropUntil u hu).support_ne_nil :=
            (p.dropUntil u hu).head_support.symm
          _ = p.support.head p.support_ne_nil := by simpa only [hs]
          _ = v := p.head_support
      exact huv huv'
  | cons a t =>
      have hav : a = v := by
        have hcons : a :: (t ++ (p.dropUntil u hu).support) =
            v :: p.support.tail := by
          simpa [p.cons_tail_support] using ht
        exact List.cons.inj hcons |>.1
      exact hsep a (by simp) v hv hav

private lemma tail_sublist_of_cons_sublist_append_cons
    {w : V} {cs pre post : List V}
    (hwpre : w ∉ pre) (hwpost : w ∉ post)
    (h : (w :: cs).Sublist (pre ++ w :: post)) :
    cs.Sublist post := by
  induction pre with
  | nil =>
      simp only [List.nil_append] at h
      rcases List.cons_sublist_cons'.mp h with hbad | hgood
      · exact (hwpost (hbad.subset (by simp))).elim
      · exact hgood.2
  | cons a pre ih =>
      have haw : w ≠ a := by
        intro hwa
        exact hwpre (by simp [hwa])
      have hwpre' : w ∉ pre := by
        intro hw
        exact hwpre (by simp [hw])
      apply ih hwpre'
      exact h.of_cons_of_ne haw

private lemma append_tail_sublist_of_infix_of_last
    {w : V} {a cs l : List V}
    (hl : l.Nodup) (ha : a <:+: l) (ha0 : a ≠ [])
    (halast : a.getLast ha0 = w) (hc : (w :: cs).Sublist l) :
    (a ++ cs).Sublist l := by
  obtain ⟨pre, post, hprepost⟩ := ha
  have hadecomp := a.dropLast_append_getLast ha0
  rw [halast] at hadecomp
  have heq : pre ++ a.dropLast ++ w :: post = pre ++ a ++ post := by
    calc
      pre ++ a.dropLast ++ w :: post =
          pre ++ (a.dropLast ++ [w]) ++ post := by
        simp only [List.append_assoc, List.singleton_append]
      _ = pre ++ a ++ post := by rw [hadecomp]
  have hl' : (pre ++ a.dropLast ++ w :: post).Nodup := by
    rw [heq, hprepost]
    exact hl
  have hc' : (w :: cs).Sublist (pre ++ a.dropLast ++ w :: post) := by
    rw [heq, hprepost]
    exact hc
  have hparts := List.nodup_append.mp hl'
  have htailparts := List.nodup_cons.mp hparts.2.1
  have hwpre : w ∉ pre ++ a.dropLast := by
    intro hw
    exact hparts.2.2 w hw w (by simp) rfl
  have hwpost : w ∉ post := htailparts.1
  have hcs : cs.Sublist post :=
    tail_sublist_of_cons_sublist_append_cons hwpre hwpost hc'
  have hkeep : (a ++ cs).Sublist (a ++ post) :=
    (List.Sublist.refl a).append hcs
  have hskip : (a ++ cs).Sublist (pre ++ a ++ post) := by
    simpa [List.append_assoc] using (List.nil_sublist pre).append hkeep
  rw [hprepost] at hskip
  exact hskip

lemma aligned_cons_indirect_splice
    {x v y z u w : V} {h : G.Adj x v}
    {ref : G.Walk v y} {q : G.Walk x u} {t : G.Walk u w}
    {r : G.Walk v z}
    (hxref : x ∉ ref.support) (hxr : x ∉ r.support)
    (href : ref.IsPath) (hq : q.IsPath) (huref : u ∈ ref.support)
    (hfirstRef : ∀ a, a ∈ ref.support → a ∈ q.support → a = u)
    (htinfix : t.support <:+: ref.support)
    (hwr : w ∈ r.support) (hwtref : w ∈ ref.support)
    (har : Aligned ref r) :
    Aligned (Walk.cons h ref)
      ((q.append t).append (r.dropUntil w hwr)) := by
  let s := r.dropUntil w hwr
  have hsAligned : Aligned ref s := aligned_dropUntil har hwr
  have hqRef :
      q.support.filter (fun a => a ∈ ref.support) = [u] := by
    have hfilter := filter_eq_ite_singleton_of_nodup_of_forall_eq
      q.support (fun a => a ∈ ref.support) u hq.support_nodup
      (fun a haq haref => hfirstRef a haref haq)
    simpa [huref] using hfilter
  have hxqtail : x ∉ q.support.tail := by
    intro hx
    have hne := hq.support_nodup.rel_head_tail hx
    exact hne (by simpa only [q.head_support])
  have hqFull :
      q.support.filter (fun a => a ∈ (Walk.cons h ref).support) = [x, u] := by
    rw [← q.cons_tail_support, List.filter_cons]
    rw [if_pos (by simp)]
    have htailFull :
        q.support.tail.filter (fun a => a ∈ (Walk.cons h ref).support) =
          q.support.tail.filter (fun a => a ∈ ref.support) := by
      apply List.filter_congr
      intro a ha
      simp only [Walk.support_cons, List.mem_cons]
      have hax : a ≠ x := by
        intro hax
        exact hxqtail (hax ▸ ha)
      simp [hax]
    rw [htailFull]
    have htailRef :
        q.support.tail.filter (fun a => a ∈ ref.support) =
          q.support.filter (fun a => a ∈ ref.support) := by
      have hs :
          (x :: q.support.tail).filter (fun a => a ∈ ref.support) =
            q.support.filter (fun a => a ∈ ref.support) := congrArg
        (fun l : List V => l.filter (fun a => a ∈ ref.support))
        q.cons_tail_support
      have hskip :
          (x :: q.support.tail).filter (fun a => a ∈ ref.support) =
            q.support.tail.filter (fun a => a ∈ ref.support) := by
        simp only [List.filter_cons]
        rw [if_neg (by simpa using hxref)]
      exact hskip.symm.trans hs
    rw [htailRef, hqRef]
  have htfilter :
      t.support.filter (fun a => a ∈ ref.support) = t.support := by
    apply List.filter_eq_self.mpr
    intro a ha
    simpa using htinfix.subset ha
  have hxttail : x ∉ t.support.tail := by
    intro hx
    exact hxref (htinfix.subset (List.mem_of_mem_tail hx))
  have htTailFull :
      t.support.tail.filter (fun a => a ∈ (Walk.cons h ref).support) =
        t.support.tail := by
    apply List.filter_eq_self.mpr
    intro a ha
    simp only [Walk.support_cons, List.mem_cons]
    simpa using Or.inr (htinfix.subset (List.mem_of_mem_tail ha))
  have hxstail : x ∉ s.support.tail := by
    intro hx
    exact hxr (r.support_dropUntil_subset_support hwr (List.mem_of_mem_tail hx))
  have hsTailFull :
      s.support.tail.filter (fun a => a ∈ (Walk.cons h ref).support) =
        s.support.tail.filter (fun a => a ∈ ref.support) := by
    apply List.filter_congr
    intro a ha
    simp only [Walk.support_cons, List.mem_cons]
    have hax : a ≠ x := by
      intro hax
      exact hxstail (hax ▸ ha)
    simp [hax]
  have hsCommonCons :
      w :: s.support.tail.filter (fun a => a ∈ ref.support) =
        s.support.filter (fun a => a ∈ ref.support) := by
    conv_rhs => rw [← s.cons_tail_support]
    simp only [List.filter_cons]
    rw [if_pos (by simpa using hwtref)]
  have htailSub :
      (t.support ++ s.support.tail.filter (fun a => a ∈ ref.support)).Sublist
        ref.support := by
    apply append_tail_sublist_of_infix_of_last href.support_nodup htinfix
      t.support_ne_nil t.getLast_support
    rw [hsCommonCons]
    exact hsAligned
  unfold Aligned at hsAligned ⊢
  rw [Walk.support_append, Walk.support_append, List.filter_append,
    List.filter_append, hqFull, htTailFull, hsTailFull, Walk.support_cons]
  simpa [List.append_assoc] using htailSub.cons_cons x

lemma isPath_append_of_meet_eq_end {a b c : V}
    {p : G.Walk a b} {q : G.Walk b c}
    (hp : p.IsPath) (hq : q.IsPath)
    (hmeet : ∀ t, t ∈ p.support → t ∈ q.support → t = b) :
    (p.append q).IsPath := by
  apply isPath_append_of_disjoint_tail hp hq
  rw [List.disjoint_left]
  intro t htp htqt
  have htb := hmeet t htp (List.mem_of_mem_tail htqt)
  subst t
  exact hq.support_nodup.rel_head_tail htqt (by simp)

lemma isPath_indirect_splice
    {x u w v z : V} {q : G.Walk x u} {r : G.Walk u w}
    {a : G.Walk v z}
    (hq : q.IsPath) (hr : r.IsPath) (ha : a.IsPath) (hw : w ∈ a.support)
    (hqr : ∀ t, t ∈ q.support → t ∈ r.support → t = u)
    (hqa : ∀ t, t ∈ q.support → t ∈ a.support → t = u)
    (hua : u ∉ a.support)
    (hra : ∀ t, t ∈ r.support → t ∈ a.support → t = w) :
    ((q.append r).append (a.dropUntil w hw)).IsPath := by
  have hqrs : (q.append r).IsPath := isPath_append_of_meet_eq_end hq hr hqr
  apply isPath_append_of_meet_eq_end hqrs (ha.dropUntil hw)
  intro t htqr hta
  rw [Walk.mem_support_append_iff] at htqr
  have hta' : t ∈ a.support := a.support_dropUntil_subset_support hw hta
  rcases htqr with htq | htr
  · have htu : t = u := hqa t htq hta'
    exact (hua (htu ▸ hta')).elim
  · exact hra t htr hta'

/-- The certificate in Dirac's aligned two-path lemma.  The explicit
intersection equation is easier to use than a nested `List.Disjoint` after
the two paths have their common first vertex. -/
structure AlignedFan {x y z : V} (p : G.Walk x y) where
  toZ : G.Walk x z
  toY : G.Walk x y
  toZ_isPath : toZ.IsPath
  toY_isPath : toY.IsPath
  meet_eq_start : ∀ ⦃w : V⦄, w ∈ toZ.support → w ∈ toY.support → w = x
  toZ_aligned : Aligned p toZ
  toY_aligned : Aligned p toY

@[simp] lemma aligned_nil {x y a : V} (p : G.Walk x y) :
    Aligned p (.nil : G.Walk a a) := by
  by_cases ha : a ∈ p.support
  · simpa [Aligned, ha] using (List.singleton_sublist.mpr ha)
  · simp [Aligned, ha]

lemma aligned_edge_of_avoids_end {x y z : V} (hxy : G.Adj x y)
    (q : G.Walk x z) (hq : q.IsPath) (hy : y ∉ q.support) :
    Aligned hxy.toWalk q := by
  have hxnot : x ∉ q.support.tail := by
    have hn := hq.support_nodup
    rw [← q.cons_tail_support, List.nodup_cons] at hn
    exact hn.1
  have hynot : y ∉ q.support.tail := fun h ↦ hy (List.mem_of_mem_tail h)
  have hfilter : q.support.tail.filter (fun v ↦ v ∈ [x, y]) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro a ha
    have hax : a ≠ x := fun h ↦ hxnot (h ▸ ha)
    have hay : a ≠ y := fun h ↦ hynot (h ▸ ha)
    simp [hax, hay]
  unfold Aligned
  rw [hxy.support_toWalk, ← q.cons_tail_support]
  rw [List.filter_cons_of_pos (by simp), hfilter]
  exact (List.nil_sublist [y]).cons_cons x

/-- A path in `G - v` from `x` toward `y`, stopped at its first point on
the reference path or either old branch. -/
lemma exists_first_connector
    (hG : Erdos58.TwoConnected G) {x v y z : V}
    (hxv : G.Adj x v) (p : G.Walk v y) (hvy : v ≠ y)
    (a : G.Walk v z) (b : G.Walk v y) :
    ∃ (u : V) (q : G.Walk x u),
      q.IsPath ∧ v ∉ q.support ∧
      u ∈ p.support.toFinset ∪ a.support.toFinset ∪ b.support.toFinset ∧
      (∀ t, t ∈ p.support.toFinset ∪ a.support.toFinset ∪ b.support.toFinset →
        t ∈ q.support → t = u) := by
  obtain ⟨r, hr, hrv⟩ := hG.exists_path_avoiding v hxv.ne hvy.symm
  let S : Finset V :=
    p.support.toFinset ∪ a.support.toFinset ∪ b.support.toFinset
  have hmeet : {t ∈ S | t ∈ r.support}.Nonempty := by
    refine ⟨y, ?_⟩
    simp [S]
  obtain ⟨u, huS, huR, hfirst⟩ :=
    r.exists_mem_support_forall_mem_support_imp_eq S hmeet
  let q : G.Walk x u := r.takeUntil u huR
  refine ⟨u, q, hr.takeUntil huR, ?_, huS, ?_⟩
  · intro hvq
    exact hrv (r.support_takeUntil_subset_support huR hvq)
  · intro t htS htq
    exact hfirst t htS htq

/-- Starting at a reference vertex, walk forward to the first point on
either old branch.  Its support is a contiguous segment of the reference. -/
lemma exists_first_branch_hit_along_reference
    {v y z u : V} (p : G.Walk v y) (hp : p.IsPath)
    (a : G.Walk v z) (b : G.Walk v y) (hu : u ∈ p.support) :
    ∃ (w : V) (r : G.Walk u w),
      r.IsPath ∧ r.support.IsInfix p.support ∧
      w ∈ a.support.toFinset ∪ b.support.toFinset ∧
      (∀ t, t ∈ a.support.toFinset ∪ b.support.toFinset →
        t ∈ r.support → t = w) := by
  let d : G.Walk u y := p.dropUntil u hu
  let S : Finset V := a.support.toFinset ∪ b.support.toFinset
  have hmeet : {t ∈ S | t ∈ d.support}.Nonempty := by
    refine ⟨y, ?_⟩
    simp [S, d]
  obtain ⟨w, hwS, hwd, hfirst⟩ :=
    d.exists_mem_support_forall_mem_support_imp_eq S hmeet
  let r : G.Walk u w := d.takeUntil w hwd
  refine ⟨w, r, (hp.dropUntil hu).takeUntil hwd, ?_, hwS, ?_⟩
  · exact (d.support_takeUntil_prefix_support hwd).isInfix.trans
      (p.support_dropUntil_suffix_support hu).isInfix
  · intro t htS htr
    exact hfirst t htS htr

namespace AlignedFan

/-- Indirect Case 2: the connector first hits the reference path, then a
forward reference segment first hits the old `z` branch. -/
noncomputable def lift_indirect_toZ {x v y z u w : V} {h : G.Adj x v}
    {p : G.Walk v y} (F : AlignedFan (z := z) p)
    (hp : p.IsPath) (hxp : x ∉ p.support) (hxZ : x ∉ F.toZ.support)
    (hxY : x ∉ F.toY.support)
    (q : G.Walk x u) (t : G.Walk u w) (hq : q.IsPath) (ht : t.IsPath)
    (hqv : v ∉ q.support) (huP : u ∈ p.support)
    (huZ : u ∉ F.toZ.support) (huY : u ∉ F.toY.support)
    (hwZ : w ∈ F.toZ.support) (hwP : w ∈ p.support)
    (hvw : v ≠ w) (htinfix : t.support <:+: p.support)
    (hfirstP : ∀ a, a ∈ p.support → a ∈ q.support → a = u)
    (hfirstZq : ∀ a, a ∈ F.toZ.support → a ∈ q.support → a = u)
    (hfirstYq : ∀ a, a ∈ F.toY.support → a ∈ q.support → a = u)
    (hfirstZt : ∀ a, a ∈ F.toZ.support → a ∈ t.support → a = w)
    (hfirstYt : ∀ a, a ∈ F.toY.support → a ∈ t.support → a = w) :
    AlignedFan (z := z) (Walk.cons h p) := by
  let rz : G.Walk x z := (q.append t).append (F.toZ.dropUntil w hwZ)
  let ry : G.Walk x y := Walk.cons h F.toY
  have hqr : ∀ a, a ∈ q.support → a ∈ t.support → a = u := by
    intro a haq hat
    exact hfirstP a (htinfix.subset hat) haq
  have hrz : rz.IsPath := isPath_indirect_splice hq ht F.toZ_isPath hwZ
    hqr (fun a haq haZ => hfirstZq a haZ haq) huZ
    (fun a hat haZ => hfirstZt a haZ hat)
  have hry : ry.IsPath := (Walk.cons_isPath_iff h F.toY).2
    ⟨F.toY_isPath, hxY⟩
  have hwY : w ∉ F.toY.support := by
    intro hwY
    exact hvw (F.meet_eq_start hwZ hwY).symm
  have hvSuffix : v ∉ (F.toZ.dropUntil w hwZ).support :=
    start_not_mem_dropUntil_of_ne F.toZ_isPath hwZ hvw.symm
  refine
    { toZ := rz
      toY := ry
      toZ_isPath := hrz
      toY_isPath := hry
      meet_eq_start := ?_
      toZ_aligned := ?_
      toY_aligned := aligned_cons hxp hxY F.toY_aligned }
  · intro a haZ haY
    simp only [ry, Walk.support_cons, List.mem_cons] at haY
    rcases haY with rfl | haY
    · rfl
    · simp only [rz, Walk.mem_support_append_iff] at haZ
      rcases haZ with haqt | haS
      · rcases haqt with haq | hat
        · have hau : a = u := hfirstYq a haY haq
          exact (huY (hau ▸ haY)).elim
        · have haw : a = w := hfirstYt a haY hat
          exact (hwY (haw ▸ haY)).elim
      · have haOldZ := F.toZ.support_dropUntil_subset_support hwZ haS
        have hav : a = v := F.meet_eq_start haOldZ haY
        exact (hvSuffix (hav ▸ haS)).elim
  · exact aligned_cons_indirect_splice hxp hxZ hp hq huP
      hfirstP htinfix hwZ hwP F.toZ_aligned

/-- Symmetric indirect Case 2, with the forward reference segment first
hitting the old `y` branch. -/
noncomputable def lift_indirect_toY {x v y z u w : V} {h : G.Adj x v}
    {p : G.Walk v y} (F : AlignedFan (z := z) p)
    (hp : p.IsPath) (hxp : x ∉ p.support) (hxZ : x ∉ F.toZ.support)
    (hxY : x ∉ F.toY.support)
    (q : G.Walk x u) (t : G.Walk u w) (hq : q.IsPath) (ht : t.IsPath)
    (hqv : v ∉ q.support) (huP : u ∈ p.support)
    (huZ : u ∉ F.toZ.support) (huY : u ∉ F.toY.support)
    (hwY : w ∈ F.toY.support) (hwP : w ∈ p.support)
    (hvw : v ≠ w) (htinfix : t.support <:+: p.support)
    (hfirstP : ∀ a, a ∈ p.support → a ∈ q.support → a = u)
    (hfirstZq : ∀ a, a ∈ F.toZ.support → a ∈ q.support → a = u)
    (hfirstYq : ∀ a, a ∈ F.toY.support → a ∈ q.support → a = u)
    (hfirstZt : ∀ a, a ∈ F.toZ.support → a ∈ t.support → a = w)
    (hfirstYt : ∀ a, a ∈ F.toY.support → a ∈ t.support → a = w) :
    AlignedFan (z := z) (Walk.cons h p) := by
  let rz : G.Walk x z := Walk.cons h F.toZ
  let ry : G.Walk x y := (q.append t).append (F.toY.dropUntil w hwY)
  have hqr : ∀ a, a ∈ q.support → a ∈ t.support → a = u := by
    intro a haq hat
    exact hfirstP a (htinfix.subset hat) haq
  have hrz : rz.IsPath := (Walk.cons_isPath_iff h F.toZ).2
    ⟨F.toZ_isPath, hxZ⟩
  have hry : ry.IsPath := isPath_indirect_splice hq ht F.toY_isPath hwY
    hqr (fun a haq haY => hfirstYq a haY haq) huY
    (fun a hat haY => hfirstYt a haY hat)
  have hwZ : w ∉ F.toZ.support := by
    intro hwZ
    exact hvw (F.meet_eq_start hwZ hwY).symm
  have hvSuffix : v ∉ (F.toY.dropUntil w hwY).support :=
    start_not_mem_dropUntil_of_ne F.toY_isPath hwY hvw.symm
  refine
    { toZ := rz
      toY := ry
      toZ_isPath := hrz
      toY_isPath := hry
      meet_eq_start := ?_
      toZ_aligned := aligned_cons hxp hxZ F.toZ_aligned
      toY_aligned := ?_ }
  · intro a haZ haY
    simp only [rz, Walk.support_cons, List.mem_cons] at haZ
    rcases haZ with rfl | haZ
    · rfl
    · simp only [ry, Walk.mem_support_append_iff] at haY
      rcases haY with haqt | haS
      · rcases haqt with haq | hat
        · have hau : a = u := hfirstZq a haZ haq
          exact (huZ (hau ▸ haZ)).elim
        · have haw : a = w := hfirstZt a haZ hat
          exact (hwZ (haw ▸ haZ)).elim
      · have haOldY := F.toY.support_dropUntil_subset_support hwY haS
        have hav : a = v := F.meet_eq_start haZ haOldY
        exact (hvSuffix (hav ▸ haS)).elim
  · exact aligned_cons_indirect_splice hxp hxY hp hq huP
      hfirstP htinfix hwY hwP F.toY_aligned

/-- Case 2 when the first connector hits the old `z`-branch directly. -/
noncomputable def lift_of_first_hit_toZ {x v y z u : V} {h : G.Adj x v}
    {p : G.Walk v y} (F : AlignedFan (z := z) p)
    (hxp : x ∉ p.support) (hxZ : x ∉ F.toZ.support)
    (hxY : x ∉ F.toY.support) (q : G.Walk x u) (hq : q.IsPath)
    (hqv : v ∉ q.support) (huZ : u ∈ F.toZ.support)
    (hfirstP : ∀ w, w ∈ p.support → w ∈ q.support → w = u)
    (hfirstZ : ∀ w, w ∈ F.toZ.support → w ∈ q.support → w = u)
    (hfirstY : ∀ w, w ∈ F.toY.support → w ∈ q.support → w = u) :
    AlignedFan (z := z) (Walk.cons h p) := by
  let rz : G.Walk x z := q.append (F.toZ.dropUntil u huZ)
  let ry : G.Walk x y := Walk.cons h F.toY
  have huv : u ≠ v := by
    intro huv
    exact hqv (huv ▸ q.end_mem_support)
  have hvSuffix : v ∉ (F.toZ.dropUntil u huZ).support :=
    start_not_mem_dropUntil_of_ne F.toZ_isPath huZ huv
  have hrz : rz.IsPath :=
    isPath_append_dropUntil_of_first_hit hq F.toZ_isPath huZ hfirstZ
  have hry : ry.IsPath := (Walk.cons_isPath_iff h F.toY).2
    ⟨F.toY_isPath, hxY⟩
  refine
    { toZ := rz
      toY := ry
      toZ_isPath := hrz
      toY_isPath := hry
      meet_eq_start := ?_
      toZ_aligned := ?_
      toY_aligned := aligned_cons hxp hxY F.toY_aligned }
  · intro w hwz hwy
    simp only [ry, Walk.support_cons, List.mem_cons] at hwy
    rcases hwy with rfl | hwy
    · rfl
    · simp only [rz, Walk.mem_support_append_iff] at hwz
      rcases hwz with hwq | hwS
      · have hwu : w = u := hfirstY w hwy hwq
        have huY : u ∈ F.toY.support := hwu ▸ hwy
        have huv' : u = v := F.meet_eq_start huZ huY
        exact (hqv (huv' ▸ q.end_mem_support)).elim
      · have hwZ : w ∈ F.toZ.support :=
          F.toZ.support_dropUntil_subset_support huZ hwS
        have hwv : w = v := F.meet_eq_start hwZ hwy
        exact (hvSuffix (hwv ▸ hwS)).elim
  · exact aligned_cons_append_dropUntil_of_first_hit hxp hxZ hq
      F.toZ_aligned huZ hfirstP

/-- Case 2 when the first connector hits the old `y`-branch directly. -/
noncomputable def lift_of_first_hit_toY {x v y z u : V} {h : G.Adj x v}
    {p : G.Walk v y} (F : AlignedFan (z := z) p)
    (hxp : x ∉ p.support) (hxZ : x ∉ F.toZ.support)
    (hxY : x ∉ F.toY.support) (q : G.Walk x u) (hq : q.IsPath)
    (hqv : v ∉ q.support) (huY : u ∈ F.toY.support)
    (hfirstP : ∀ w, w ∈ p.support → w ∈ q.support → w = u)
    (hfirstZ : ∀ w, w ∈ F.toZ.support → w ∈ q.support → w = u)
    (hfirstY : ∀ w, w ∈ F.toY.support → w ∈ q.support → w = u) :
    AlignedFan (z := z) (Walk.cons h p) := by
  let rz : G.Walk x z := Walk.cons h F.toZ
  let ry : G.Walk x y := q.append (F.toY.dropUntil u huY)
  have huv : u ≠ v := by
    intro huv
    exact hqv (huv ▸ q.end_mem_support)
  have hvSuffix : v ∉ (F.toY.dropUntil u huY).support :=
    start_not_mem_dropUntil_of_ne F.toY_isPath huY huv
  have hrz : rz.IsPath := (Walk.cons_isPath_iff h F.toZ).2
    ⟨F.toZ_isPath, hxZ⟩
  have hry : ry.IsPath :=
    isPath_append_dropUntil_of_first_hit hq F.toY_isPath huY hfirstY
  refine
    { toZ := rz
      toY := ry
      toZ_isPath := hrz
      toY_isPath := hry
      meet_eq_start := ?_
      toZ_aligned := aligned_cons hxp hxZ F.toZ_aligned
      toY_aligned := ?_ }
  · intro w hwz hwy
    simp only [rz, Walk.support_cons, List.mem_cons] at hwz
    rcases hwz with rfl | hwz
    · rfl
    · simp only [ry, Walk.mem_support_append_iff] at hwy
      rcases hwy with hwq | hwS
      · have hwu : w = u := hfirstZ w hwz hwq
        have huZ : u ∈ F.toZ.support := hwu ▸ hwz
        have huv' : u = v := F.meet_eq_start huZ huY
        exact (hqv (huv' ▸ q.end_mem_support)).elim
      · have hwY : w ∈ F.toY.support :=
          F.toY.support_dropUntil_subset_support huY hwS
        have hwv : w = v := F.meet_eq_start hwz hwY
        exact (hvSuffix (hwv ▸ hwS)).elim
  · exact aligned_cons_append_dropUntil_of_first_hit hxp hxY hq
      F.toY_aligned huY hfirstP

/-- The inductive construction when the new reference-path initial vertex
already occurs on the `z` branch.  This is Case 1 of Dirac's proof. -/
noncomputable def lift_of_mem_toZ {x v y z : V} {h : G.Adj x v}
    {p : G.Walk v y} (F : AlignedFan (z := z) p) (hxp : x ∉ p.support)
    (hx : x ∈ F.toZ.support) : AlignedFan (z := z) (Walk.cons h p) := by
  let rz : G.Walk x z := F.toZ.dropUntil x hx
  let ry : G.Walk x y := Walk.cons h F.toY
  have hx_toY : x ∉ F.toY.support := by
    intro hxY
    have hxv : x = v := F.meet_eq_start hx hxY
    exact h.ne hxv
  have hrz : rz.IsPath := F.toZ_isPath.dropUntil hx
  have hry : ry.IsPath := (Walk.cons_isPath_iff h F.toY).2
    ⟨F.toY_isPath, hx_toY⟩
  have hv_rz : v ∉ rz.support := by
    intro hv
    obtain ⟨t, ht⟩ := F.toZ.support_dropUntil_suffix_support hx
    have hnd : (t ++ rz.support).Nodup := by
      rw [ht]
      exact F.toZ_isPath.support_nodup
    have hsep := (List.nodup_append.mp hnd).2.2
    cases t with
    | nil =>
        have hsupport : rz.support = F.toZ.support := by simpa using ht
        have hxv : x = v := by
          calc
            x = rz.support.head rz.support_ne_nil := rz.head_support.symm
            _ = F.toZ.support.head F.toZ.support_ne_nil := by
              simpa only [hsupport]
            _ = v := F.toZ.head_support
        exact h.ne hxv
    | cons a t =>
        have hav : a = v := by
          have hcons : a :: (t ++ rz.support) = v :: F.toZ.support.tail := by
            simpa [F.toZ.cons_tail_support] using ht
          exact List.cons.inj hcons |>.1
        exact hsep a (by simp) v hv hav
  refine
    { toZ := rz
      toY := ry
      toZ_isPath := hrz
      toY_isPath := hry
      meet_eq_start := ?_
      toZ_aligned := ?_
      toY_aligned := ?_ }
  · intro w hwz hwy
    simp only [ry, Walk.support_cons, List.mem_cons] at hwy
    rcases hwy with rfl | hwy
    · rfl
    · have hwz' : w ∈ F.toZ.support :=
        F.toZ.support_dropUntil_subset_support hx hwz
      have hwv : w = v := F.meet_eq_start hwz' hwy
      exact (hv_rz (hwv ▸ hwz)).elim
  · have hxrz : x ∉ rz.support.tail := by
      intro hxTail
      have hne := hrz.support_nodup.rel_head_tail hxTail
      exact hne (by simpa only [rz.head_support])
    apply aligned_cons_left hxp hxrz
    exact aligned_dropUntil F.toZ_aligned hx
  · exact aligned_cons hxp hx_toY F.toY_aligned

/-- Symmetric Case 1: the new initial vertex occurs on the `y` branch. -/
noncomputable def lift_of_mem_toY {x v y z : V} {h : G.Adj x v}
    {p : G.Walk v y} (F : AlignedFan (z := z) p) (hxp : x ∉ p.support)
    (hx : x ∈ F.toY.support) : AlignedFan (z := z) (Walk.cons h p) := by
  let rz : G.Walk x z := Walk.cons h F.toZ
  let ry : G.Walk x y := F.toY.dropUntil x hx
  have hx_toZ : x ∉ F.toZ.support := by
    intro hxZ
    have hxv : x = v := F.meet_eq_start hxZ hx
    exact h.ne hxv
  have hrz : rz.IsPath := (Walk.cons_isPath_iff h F.toZ).2
    ⟨F.toZ_isPath, hx_toZ⟩
  have hry : ry.IsPath := F.toY_isPath.dropUntil hx
  have hv_ry : v ∉ ry.support := by
    intro hv
    obtain ⟨t, ht⟩ := F.toY.support_dropUntil_suffix_support hx
    have hnd : (t ++ ry.support).Nodup := by
      rw [ht]
      exact F.toY_isPath.support_nodup
    have hsep := (List.nodup_append.mp hnd).2.2
    cases t with
    | nil =>
        have hsupport : ry.support = F.toY.support := by simpa using ht
        have hxv : x = v := by
          calc
            x = ry.support.head ry.support_ne_nil := ry.head_support.symm
            _ = F.toY.support.head F.toY.support_ne_nil := by
              simpa only [hsupport]
            _ = v := F.toY.head_support
        exact h.ne hxv
    | cons a t =>
        have hav : a = v := by
          have hcons : a :: (t ++ ry.support) = v :: F.toY.support.tail := by
            simpa [F.toY.cons_tail_support] using ht
          exact List.cons.inj hcons |>.1
        exact hsep a (by simp) v hv hav
  refine
    { toZ := rz
      toY := ry
      toZ_isPath := hrz
      toY_isPath := hry
      meet_eq_start := ?_
      toZ_aligned := ?_
      toY_aligned := ?_ }
  · intro w hwz hwy
    simp only [rz, Walk.support_cons, List.mem_cons] at hwz
    rcases hwz with rfl | hwz
    · rfl
    · have hwy' : w ∈ F.toY.support :=
        F.toY.support_dropUntil_subset_support hx hwy
      have hwv : w = v := F.meet_eq_start hwz hwy'
      exact (hv_ry (hwv ▸ hwy)).elim
  · exact aligned_cons hxp hx_toZ F.toZ_aligned
  · have hxry : x ∉ ry.support.tail := by
      intro hxTail
      have hne := hry.support_nodup.rel_head_tail hxTail
      exact hne (by simpa only [ry.head_support])
    apply aligned_cons_left hxp hxry
    exact aligned_dropUntil F.toY_aligned hx

end AlignedFan

/-- The initial-vertex case of the aligned-fan lemma. -/
noncomputable def AlignedFan.atStart {x y : V} (p : G.Walk x y)
    (hp : p.IsPath) : AlignedFan (z := x) p :=
  { toZ := .nil
    toY := p
    toZ_isPath := .nil
    toY_isPath := hp
    meet_eq_start := by
      intro w hw _
      simpa using hw
    toZ_aligned := aligned_nil p
    toY_aligned := aligned_refl p }

/-- An infix of a simple path which starts away from the path's initial
vertex cannot contain that initial vertex. -/
lemma start_not_mem_of_support_infix {v y u w : V}
    {p : G.Walk v y} {t : G.Walk u w} (hp : p.IsPath)
    (ht : t.support.IsInfix p.support) (huv : u ≠ v) :
    v ∉ t.support := by
  intro hvt
  obtain ⟨pre, post, hsplit⟩ := ht
  have hnd : (pre ++ t.support ++ post).Nodup := by
    rw [hsplit]
    exact hp.support_nodup
  cases pre with
  | nil =>
      have hcons : u :: (t.support.tail ++ post) = v :: p.support.tail := by
        calc
          u :: (t.support.tail ++ post) = (u :: t.support.tail) ++ post := rfl
          _ = t.support ++ post := by rw [t.cons_tail_support]
          _ = p.support := hsplit
          _ = v :: p.support.tail := p.cons_tail_support.symm
      exact huv (List.cons.inj hcons).1
  | cons a pre =>
      have hav : a = v := by
        have hcons : a :: (pre ++ t.support ++ post) =
            v :: p.support.tail := by
          simpa [p.cons_tail_support] using hsplit
        exact (List.cons.inj hcons).1
      have hnd' : (a :: (pre ++ t.support ++ post)).Nodup := by
        simpa only [List.cons_append, List.append_assoc] using hnd
      exact (List.nodup_cons.mp hnd').1 (by simp [hav, hvt])

/-- Dirac's aligned-two-path lemma, in the endpoint-distinct form used by
the lollipop proof. -/
theorem exists_alignedFan (hG : Erdos58.TwoConnected G) :
    ∀ {x y : V} (p : G.Walk x y), p.IsPath →
      ∀ {z : V}, z ∈ p.support → z ≠ y →
        Nonempty (AlignedFan (z := z) p) := by
  intro x y p
  induction p with
  | nil =>
      intro _ z hz hzy
      exact (hzy (by simpa using hz)).elim
  | @cons x v y h p ih =>
      intro hpath z hz hzy
      have hp : p.IsPath := (Walk.cons_isPath_iff h p).mp hpath |>.1
      have hxp : x ∉ p.support := (Walk.cons_isPath_iff h p).mp hpath |>.2
      by_cases hzx : z = x
      · subst z
        exact ⟨AlignedFan.atStart (Walk.cons h p) hpath⟩
      have hzp : z ∈ p.support := by
        simpa only [Walk.support_cons, List.mem_cons, hzx, false_or] using hz
      obtain ⟨F⟩ := ih hp hzp hzy
      by_cases hxZ : x ∈ F.toZ.support
      · exact ⟨F.lift_of_mem_toZ hxp hxZ⟩
      by_cases hxY : x ∈ F.toY.support
      · exact ⟨F.lift_of_mem_toY hxp hxY⟩
      have hvy : v ≠ y := by
        intro hvy
        subst y
        have hpNil : p = .nil := Walk.isPath_iff_eq_nil.mp hp
        subst p
        have hzv : z = v := by simpa using hzp
        exact hzy hzv
      obtain ⟨u, q, hq, hqv, huS, hfirst⟩ :=
        exists_first_connector hG h p hvy F.toZ F.toY
      have hfirstP : ∀ a, a ∈ p.support → a ∈ q.support → a = u := by
        intro a ha haq
        apply hfirst a
        · simp only [Finset.mem_union, List.mem_toFinset]
          exact Or.inl (Or.inl ha)
        · exact haq
      have hfirstZ : ∀ a, a ∈ F.toZ.support → a ∈ q.support → a = u := by
        intro a ha haq
        apply hfirst a
        · simp only [Finset.mem_union, List.mem_toFinset]
          exact Or.inl (Or.inr ha)
        · exact haq
      have hfirstY : ∀ a, a ∈ F.toY.support → a ∈ q.support → a = u := by
        intro a ha haq
        apply hfirst a
        · simp only [Finset.mem_union, List.mem_toFinset]
          exact Or.inr ha
        · exact haq
      simp only [Finset.mem_union, List.mem_toFinset] at huS
      rcases huS with (huP | huZ) | huY
      · by_cases huZ' : u ∈ F.toZ.support
        · exact ⟨F.lift_of_first_hit_toZ hxp hxZ hxY q hq hqv huZ'
            hfirstP hfirstZ hfirstY⟩
        by_cases huY' : u ∈ F.toY.support
        · exact ⟨F.lift_of_first_hit_toY hxp hxZ hxY q hq hqv huY'
            hfirstP hfirstZ hfirstY⟩
        have huZn : u ∉ F.toZ.support := huZ'
        have huYn : u ∉ F.toY.support := huY'
        obtain ⟨w, t, ht, htinfix, hwS, hfirstT⟩ :=
          exists_first_branch_hit_along_reference p hp F.toZ F.toY huP
        have hfirstZT : ∀ a, a ∈ F.toZ.support → a ∈ t.support → a = w := by
          intro a ha hat
          apply hfirstT a
          · simp only [Finset.mem_union, List.mem_toFinset]
            exact Or.inl ha
          · exact hat
        have hfirstYT : ∀ a, a ∈ F.toY.support → a ∈ t.support → a = w := by
          intro a ha hat
          apply hfirstT a
          · simp only [Finset.mem_union, List.mem_toFinset]
            exact Or.inr ha
          · exact hat
        have huv : u ≠ v := by
          intro huv
          exact hqv (huv ▸ q.end_mem_support)
        have hvw : v ≠ w := by
          intro hvw
          subst w
          exact start_not_mem_of_support_infix hp htinfix huv
            t.end_mem_support
        have hwP : w ∈ p.support := htinfix.subset t.end_mem_support
        simp only [Finset.mem_union, List.mem_toFinset] at hwS
        rcases hwS with hwZ | hwY
        · exact ⟨F.lift_indirect_toZ hp hxp hxZ hxY q t hq ht hqv huP
            huZn huYn hwZ hwP hvw htinfix hfirstP hfirstZ hfirstY
            hfirstZT hfirstYT⟩
        · exact ⟨F.lift_indirect_toY hp hxp hxZ hxY q t hq ht hqv huP
            huZn huYn hwY hwP hvw htinfix hfirstP hfirstZ hfirstY
            hfirstZT hfirstYT⟩
      · exact ⟨F.lift_of_first_hit_toZ hxp hxZ hxY q hq hqv huZ
          hfirstP hfirstZ hfirstY⟩
      · exact ⟨F.lift_of_first_hit_toY hxp hxZ hxY q hq hqv huY
          hfirstP hfirstZ hfirstY⟩

end E767AlignedAlt

#print axioms E767AlignedAlt.exists_alignedFan

