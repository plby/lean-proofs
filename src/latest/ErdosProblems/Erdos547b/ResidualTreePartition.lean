import ErdosProblems.Erdos547b.TreePartition

open scoped Sym2

namespace Erdos547b.TreePartition

open SimpleGraph

universe u

variable {V : Type u}

noncomputable def children [Fintype V] (T : SimpleGraph V) (r x : V) : Finset V := by
  classical
  exact Finset.univ.filter fun y => IsChild T r x y

@[simp] theorem mem_children [Fintype V] {T : SimpleGraph V} {r x y : V} :
    y ∈ children T r x ↔ IsChild T r x y := by
  classical
  simp [children]

theorem child_measure_lt [Fintype V] {T : SimpleGraph V} (hT : T.IsTree)
    {r x y : V} (hxy : IsChild T r x y) :
    Fintype.card V - T.dist r y < Fintype.card V - T.dist r x := by
  obtain ⟨p, hp, hplen⟩ := hT.connected.exists_path_of_dist r x
  have hdist_lt : T.dist r x < Fintype.card V := by
    rw [← hplen]
    exact hp.length_lt
  have hLevel : T.dist r y = T.dist r x + 1 := hxy.2
  omega

/-- The residual branch size in the bottom-up version of Zhao's carving.
A child branch larger than `m` is cut off and contributes zero to its parent. -/
noncomputable def residualSize [Fintype V] (T : SimpleGraph V) (hT : T.IsTree)
    (r : V) (m : ℕ) (x : V) : ℕ :=
  1 + ∑ y : ↑(children T r x),
    if residualSize T hT r m y.1 ≤ m then residualSize T hT r m y.1 else 0
termination_by Fintype.card V - T.dist r x
decreasing_by
  all_goals
    apply child_measure_lt hT
    exact mem_children.mp y.property

/-- The residual piece retained below `x`: recurse through exactly the child
branches whose residual size is at most `m`. -/
noncomputable def residualVertices [Fintype V] (T : SimpleGraph V) (hT : T.IsTree)
    (r : V) (m : ℕ) (x : V) : Finset V := by
  classical
  exact insert x <| Finset.univ.biUnion fun y : ↑(children T r x) =>
    if residualSize T hT r m y.1 ≤ m then residualVertices T hT r m y.1 else ∅
termination_by Fintype.card V - T.dist r x
decreasing_by
  all_goals
    apply child_measure_lt hT
    exact mem_children.mp y.property

@[simp] theorem self_mem_residualVertices [Fintype V] (T : SimpleGraph V)
    (hT : T.IsTree) (r : V) (m : ℕ) (x : V) :
    x ∈ residualVertices T hT r m x := by
  classical
  rw [residualVertices.eq_def]
  simp

theorem residualVertices_subset_rootedDescendants [Fintype V]
    (T : SimpleGraph V) (hT : T.IsTree) (r : V) (m : ℕ) (x : V) :
    residualVertices T hT r m x ⊆ rootedDescendants T r x := by
  classical
  refine residualVertices.induct T hT r (motive := fun x =>
    residualVertices T hT r m x ⊆ rootedDescendants T r x) ?_ x
  intro x ih
  rw [residualVertices.eq_def]
  intro z hz
  simp only [Finset.mem_insert, Finset.mem_biUnion, Finset.mem_univ, true_and] at hz
  rcases hz with rfl | ⟨y, hy⟩
  · exact self_mem_rootedDescendants T r z
  · split at hy
    next hsmall =>
      exact rootedDescendants_mono_of_child hT (mem_children.mp y.property)
        (ih y hy)
    next hlarge => simp at hy

theorem root_not_mem_residualVertices_of_child [Fintype V]
    {T : SimpleGraph V} (hT : T.IsTree) {r x y : V} (m : ℕ)
    (hxy : IsChild T r x y) : x ∉ residualVertices T hT r m y := by
  intro hx
  have hdesc := residualVertices_subset_rootedDescendants T hT r m y hx
  rw [mem_rootedDescendants] at hdesc
  have hlevel := hxy.2
  omega

/-- The recursive size is the actual cardinality of the retained residual
piece.  This is the counting invariant used in Zhao's packing argument. -/
theorem card_residualVertices [Fintype V] (T : SimpleGraph V) (hT : T.IsTree)
    (r : V) (m : ℕ) (x : V) :
    (residualVertices T hT r m x).card = residualSize T hT r m x := by
  classical
  refine residualVertices.induct T hT r (motive := fun x =>
    (residualVertices T hT r m x).card = residualSize T hT r m x) ?_ x
  intro x ih
  rw [residualVertices.eq_def, residualSize.eq_def]
  have hxnot : x ∉ Finset.univ.biUnion (fun y : ↑(children T r x) =>
      if residualSize T hT r m y.1 ≤ m then residualVertices T hT r m y.1 else ∅) := by
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
    rintro ⟨y, hy⟩
    split at hy
    next hsmall =>
      exact root_not_mem_residualVertices_of_child hT m
        (mem_children.mp y.property) hy
    next hlarge => simp at hy
  rw [Finset.card_insert_of_notMem hxnot]
  rw [Finset.card_biUnion]
  · rw [Nat.add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro y hy
    split
    next hsmall => exact ih y
    next hlarge => simp
  · rintro a - b - hab
    simp only [Function.onFun]
    split
    next ha =>
      split
      next hb =>
        exact (disjoint_rootedDescendants_of_distinct_children hT
          (mem_children.mp a.property) (mem_children.mp b.property)
          (fun heq => hab (Subtype.ext heq))).mono
            (residualVertices_subset_rootedDescendants T hT r m a)
            (residualVertices_subset_rootedDescendants T hT r m b)
      next hb => simp
    next ha => simp

/-- The nearest carved ancestor in the basic (pre-parity-refinement) Zhao
partition.  A non-root vertex starts a new piece exactly when its residual
piece has more than `m` vertices. -/
noncomputable def basicRootOf [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (hT : T.IsTree) (r : V) (m : ℕ) (x : V) : V := by
  exact if hx : x = r then r
    else if m < residualSize T hT r m x then x
    else basicRootOf T hT r m (parent hT r hx)
termination_by T.dist r x
decreasing_by
  have hp := parent_dist_add_one hT r hx
  omega

@[simp] theorem basicRootOf_root [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (hT : T.IsTree)
    (r : V) (m : ℕ) : basicRootOf T hT r m r = r := by
  rw [basicRootOf.eq_def]
  simp

theorem basicRootOf_eq_self_of_large [Fintype V] [DecidableEq V]
    (T : SimpleGraph V)
    (hT : T.IsTree) (r : V) (m : ℕ) {x : V}
    (hx : m < residualSize T hT r m x) : basicRootOf T hT r m x = x := by
  rw [basicRootOf.eq_def]
  split
  · next hxr => simpa [hxr]
  · simp [hx]

theorem basicRootOf_eq_parent_of_small [Fintype V] [DecidableEq V]
    (T : SimpleGraph V)
    (hT : T.IsTree) (r : V) (m : ℕ) {x : V} (hxr : x ≠ r)
    (hx : residualSize T hT r m x ≤ m) :
    basicRootOf T hT r m x = basicRootOf T hT r m (parent hT r hxr) := by
  rw [basicRootOf.eq_def]
  simp [hxr, Nat.not_lt.mpr hx]

theorem basicRootOf_child_of_small [Fintype V] [DecidableEq V]
    (T : SimpleGraph V)
    (hT : T.IsTree) (r : V) (m : ℕ) {x y : V} (hxy : IsChild T r x y)
    (hy : residualSize T hT r m y ≤ m) :
    basicRootOf T hT r m y = basicRootOf T hT r m x := by
  have hyr : y ≠ r := by
    intro hyr
    subst y
    have hlevel := hxy.2
    simp at hlevel
  rw [basicRootOf_eq_parent_of_small T hT r m hyr hy]
  rw [(eq_parent_of_adj_of_dist_add_one hT r hyr hxy.1 hxy.2.symm).symm]

theorem basicRootOf_eq_of_mem_residualVertices [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (hT : T.IsTree) (r : V) (m : ℕ) {x z : V}
    (hz : z ∈ residualVertices T hT r m x) :
    basicRootOf T hT r m z = basicRootOf T hT r m x := by
  classical
  refine residualVertices.induct T hT r (motive := fun x => ∀ {z},
    z ∈ residualVertices T hT r m x →
      basicRootOf T hT r m z = basicRootOf T hT r m x) ?_ x hz
  intro x ih z hz
  rw [residualVertices.eq_def] at hz
  simp only [Finset.mem_insert, Finset.mem_biUnion, Finset.mem_univ, true_and] at hz
  rcases hz with rfl | ⟨y, hy⟩
  · rfl
  · split at hy
    next hsmall =>
      exact (ih y hy).trans (basicRootOf_child_of_small T hT r m
        (x := x) (y := y) (mem_children.mp y.property) hsmall)
    next hlarge => simp at hy

noncomputable def basicRoots [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (hT : T.IsTree)
    (r : V) (m : ℕ) : Finset V := by
  classical
  exact Finset.univ.filter fun x => x = r ∨ m < residualSize T hT r m x

@[simp] theorem mem_basicRoots [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (hT : T.IsTree)
    (r : V) (m : ℕ) (x : V) :
    x ∈ basicRoots T hT r m ↔ x = r ∨ m < residualSize T hT r m x := by
  classical
  simp [basicRoots]

theorem basicRootOf_mem_basicRoots [Fintype V] [DecidableEq V]
    (T : SimpleGraph V)
    (hT : T.IsTree) (r : V) (m : ℕ) (x : V) :
    basicRootOf T hT r m x ∈ basicRoots T hT r m := by
  classical
  refine basicRootOf.induct T hT r m (motive := fun x =>
    basicRootOf T hT r m x ∈ basicRoots T hT r m) ?_ ?_ ?_ x
  · simp
  · intro x hxr hlarge
    rw [basicRootOf_eq_self_of_large T hT r m hlarge]
    simp [hlarge]
  · intro x hxr hsmall ih
    rw [basicRootOf_eq_parent_of_small T hT r m hxr (Nat.le_of_not_gt hsmall)]
    exact ih

theorem residualVertices_subset_basicFiber [Fintype V] [DecidableEq V]
    (T : SimpleGraph V)
    (hT : T.IsTree) (r : V) (m : ℕ) {x : V}
    (hx : x ∈ basicRoots T hT r m) :
    residualVertices T hT r m x ⊆
      Finset.univ.filter fun z => basicRootOf T hT r m z = x := by
  classical
  intro z hz
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  rw [basicRootOf_eq_of_mem_residualVertices T hT r m hz]
  rcases (mem_basicRoots T hT r m x).mp hx with hxr | hxLarge
  · subst x
    exact basicRootOf_root T hT r m
  · exact basicRootOf_eq_self_of_large T hT r m hxLarge

noncomputable def basicFiber [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (hT : T.IsTree) (r : V) (m : ℕ) (x : V) : Finset V :=
  Finset.univ.filter fun z => basicRootOf T hT r m z = x

@[simp] theorem mem_basicFiber [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (hT : T.IsTree) (r : V) (m : ℕ) (x z : V) :
    z ∈ basicFiber T hT r m x ↔ basicRootOf T hT r m z = x := by
  simp [basicFiber]

theorem basicRoot_mem_basicFiber [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (hT : T.IsTree) (r : V) (m : ℕ) {x : V}
    (hx : x ∈ basicRoots T hT r m) : x ∈ basicFiber T hT r m x := by
  rw [mem_basicFiber]
  rcases (mem_basicRoots T hT r m x).mp hx with hxr | hxLarge
  · subst x
    simp
  · exact basicRootOf_eq_self_of_large T hT r m hxLarge

theorem basicFiber_card_ge_succ_m [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (hT : T.IsTree) (r : V) (m : ℕ) {x : V}
    (hx : x ∈ basicRoots T hT r m) (hxr : x ≠ r) :
    m + 1 ≤ (basicFiber T hT r m x).card := by
  have hxLarge : m < residualSize T hT r m x :=
    ((mem_basicRoots T hT r m x).mp hx).resolve_left hxr
  have hsub : residualVertices T hT r m x ⊆ basicFiber T hT r m x :=
    residualVertices_subset_basicFiber T hT r m hx
  have hcard := Finset.card_le_card hsub
  rw [card_residualVertices T hT r m x] at hcard
  omega

theorem basicFibers_biUnion [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (hT : T.IsTree) (r : V) (m : ℕ) :
    (basicRoots T hT r m).biUnion (basicFiber T hT r m) = Finset.univ := by
  ext z
  simp only [Finset.mem_biUnion, mem_basicFiber, Finset.mem_univ, iff_true]
  exact ⟨basicRootOf T hT r m z, basicRootOf_mem_basicRoots T hT r m z, rfl⟩

theorem basicFibers_pairwiseDisjoint [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (hT : T.IsTree) (r : V) (m : ℕ) :
    (↑(basicRoots T hT r m) : Set V).PairwiseDisjoint (basicFiber T hT r m) := by
  rintro a ha b hb hab
  simp only [Function.onFun]
  rw [Finset.disjoint_left]
  intro z hza hzb
  rw [mem_basicFiber] at hza hzb
  exact hab (hza.symm.trans hzb)

theorem sum_card_basicFibers [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (hT : T.IsTree) (r : V) (m : ℕ) :
    ∑ x ∈ basicRoots T hT r m, (basicFiber T hT r m x).card = Fintype.card V := by
  rw [← Finset.card_biUnion (basicFibers_pairwiseDisjoint T hT r m),
    basicFibers_biUnion T hT r m, Finset.card_univ]

/-- The packing estimate for Zhao's basic carving.  Every non-root piece has
at least `m+1` vertices, while the root piece is nonempty. -/
theorem card_basicRoots_le [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (hT : T.IsTree) (r : V) (m : ℕ) :
    (basicRoots T hT r m).card ≤ (Fintype.card V + m) / (m + 1) := by
  let R := basicRoots T hT r m
  let F := basicFiber T hT r m
  change R.card ≤ (Fintype.card V + m) / (m + 1)
  have hr : r ∈ R := by simp [R]
  have hroot : 1 ≤ (F r).card := by
    exact Finset.card_pos.mpr ⟨r, by
      simpa [F] using basicRoot_mem_basicFiber T hT r m hr⟩
  have hparts : ∀ x ∈ R.erase r, m + 1 ≤ (F x).card := by
    intro x hx
    have hxR := (Finset.mem_erase.mp hx).2
    have hxr := (Finset.mem_erase.mp hx).1
    exact basicFiber_card_ge_succ_m T hT r m hxR hxr
  have hlower : (R.erase r).card * (m + 1) + 1 ≤
      ∑ x ∈ R, (F x).card := by
    calc
      (R.erase r).card * (m + 1) + 1 =
          (∑ x ∈ R.erase r, (m + 1)) + 1 := by simp
      _ ≤ (∑ x ∈ R.erase r, (F x).card) + (F r).card := by
        exact Nat.add_le_add (Finset.sum_le_sum hparts) hroot
      _ = ∑ x ∈ R, (F x).card := by
        rw [Finset.sum_erase_add _ _ hr]
  have hsum : ∑ x ∈ R, (F x).card = Fintype.card V := by
    exact sum_card_basicFibers T hT r m
  have hErase : (R.erase r).card = R.card - 1 := Finset.card_erase_of_mem hr
  apply (Nat.le_div_iff_mul_le (Nat.succ_pos m)).2
  rw [hErase] at hlower
  rw [hsum] at hlower
  have hRpos : 0 < R.card := Finset.card_pos.mpr ⟨r, hr⟩
  have hRsplit : R.card = (R.card - 1) + 1 := by omega
  have hmul := congrArg (fun k : ℕ => k * (m + 1)) hRsplit
  calc
    R.card * (m + 1) = ((R.card - 1) + 1) * (m + 1) := hmul
    _ = ((R.card - 1) * (m + 1) + 1) + m := by
      rw [Nat.add_mul]
      omega
    _ ≤ Fintype.card V + m := Nat.add_le_add hlower (Nat.le_refl m)

theorem residualSize_le_of_mem_basicFiber_of_ne_root [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (hT : T.IsTree) (r : V) (m : ℕ) {a x : V}
    (hx : x ∈ basicFiber T hT r m a) (hxa : x ≠ a) :
    residualSize T hT r m x ≤ m := by
  rw [mem_basicFiber] at hx
  by_contra hlarge
  have hself := basicRootOf_eq_self_of_large T hT r m (Nat.lt_of_not_ge hlarge)
  exact hxa (hself.symm.trans hx)

theorem parent_mem_same_basicFiber_of_ne_root [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (hT : T.IsTree) (r : V) (m : ℕ) {a x : V}
    (hx : x ∈ basicFiber T hT r m a) (hxa : x ≠ a) :
    ∃ hxr : x ≠ r, parent hT r hxr ∈ basicFiber T hT r m a := by
  have hxr : x ≠ r := by
    intro hxr
    subst x
    rw [mem_basicFiber] at hx
    simp at hx
    exact hxa hx
  have hsmall := residualSize_le_of_mem_basicFiber_of_ne_root T hT r m hx hxa
  refine ⟨hxr, ?_⟩
  rw [mem_basicFiber] at hx ⊢
  rw [← basicRootOf_eq_parent_of_small T hT r m hxr
    hsmall]
  exact hx

theorem dist_basicRootOf_le [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (hT : T.IsTree) (r : V) (m : ℕ) (x : V) :
    T.dist r (basicRootOf T hT r m x) ≤ T.dist r x := by
  refine basicRootOf.induct T hT r m (motive := fun x =>
    T.dist r (basicRootOf T hT r m x) ≤ T.dist r x) ?_ ?_ ?_ x
  · simp
  · intro x hxr hlarge
    rw [basicRootOf_eq_self_of_large T hT r m hlarge]
  · intro x hxr hsmall ih
    rw [basicRootOf_eq_parent_of_small T hT r m hxr (Nat.le_of_not_gt hsmall)]
    exact ih.trans (by
      have hp := parent_dist_add_one hT r hxr
      omega)

/-- A fully explicit basic forest carving.  Its fibers are the connected
pieces before Zhao's parity repair; the later repair only splits these fibers. -/
structure BasicForestCarving [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (hT : T.IsTree) (globalRoot : V) (m : ℕ) where
  roots : Finset V
  rootOf : V → V
  globalRoot_mem : globalRoot ∈ roots
  rootOf_mem : ∀ x, rootOf x ∈ roots
  roots_fixed : ∀ x ∈ roots, rootOf x = x
  fibers_cover : roots.biUnion (fun a => Finset.univ.filter fun x => rootOf x = a) =
    Finset.univ
  fibers_disjoint : (↑roots : Set V).PairwiseDisjoint
    (fun a => Finset.univ.filter fun x => rootOf x = a)
  small_off_root : ∀ a x, rootOf x = a → x ≠ a → residualSize T hT globalRoot m x ≤ m
  parent_closed : ∀ a x, rootOf x = a → x ≠ a →
    ∃ hxr : x ≠ globalRoot, rootOf (parent hT globalRoot hxr) = a
  root_parent_earlier : ∀ x, x ∈ roots → ∀ hxr : x ≠ globalRoot,
    T.dist globalRoot (rootOf (parent hT globalRoot hxr)) <
      T.dist globalRoot x
  root_count : roots.card ≤ (Fintype.card V + m) / (m + 1)
  parity_root_count : ∀ q : Fin 2,
    (roots.filter fun x => T.dist globalRoot x % 2 = q.val).card ≤
      (Fintype.card V + m) / (m + 1)

/-- Existence of Zhao's basic ordered forest carving, including its exact
packing estimate and the per-parity estimate inherited from the total count. -/
theorem exists_basicForestCarving [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (hT : T.IsTree) (r : V) (m : ℕ) :
    Nonempty (BasicForestCarving T hT r m) := by
  let R := basicRoots T hT r m
  let f := basicRootOf T hT r m
  refine ⟨{
    roots := R
    rootOf := f
    globalRoot_mem := by simp [R]
    rootOf_mem := by
      intro x
      exact basicRootOf_mem_basicRoots T hT r m x
    roots_fixed := by
      intro x hx
      rcases (mem_basicRoots T hT r m x).mp hx with hxr | hlarge
      · subst x
        simp [f]
      · exact basicRootOf_eq_self_of_large T hT r m hlarge
    fibers_cover := by
      exact basicFibers_biUnion T hT r m
    fibers_disjoint := by
      exact basicFibers_pairwiseDisjoint T hT r m
    small_off_root := by
      intro a x hx hxa
      apply residualSize_le_of_mem_basicFiber_of_ne_root T hT r m
      · exact (mem_basicFiber T hT r m a x).mpr hx
      · exact hxa
    parent_closed := by
      intro a x hx hxa
      obtain ⟨hxr, hp⟩ := parent_mem_same_basicFiber_of_ne_root T hT r m
        ((mem_basicFiber T hT r m a x).mpr hx) hxa
      exact ⟨hxr, (mem_basicFiber T hT r m a _).mp hp⟩
    root_parent_earlier := by
      intro x hx hxr
      exact (dist_basicRootOf_le T hT r m (parent hT r hxr)).trans_lt (by
        have hp := parent_dist_add_one hT r hxr
        omega)
    root_count := card_basicRoots_le T hT r m
    parity_root_count := by
      intro q
      exact (Finset.card_filter_le _ _).trans
        (card_basicRoots_le T hT r m)
  }⟩

/-- A basic root whose attachment violates Zhao's reconnection condition.  Its
actual parent is added as a new root in the parity-repair step. -/
def IsBadBasicRoot [Fintype V] [DecidableEq V] (T : SimpleGraph V)
    (hT : T.IsTree) (r : V) (m : ℕ) (w : V) : Prop :=
  ∃ (hw : w ∈ basicRoots T hT r m) (hwr : w ≠ r),
    let p := parent hT r hwr
    p ≠ basicRootOf T hT r m p ∧
      T.dist r w % 2 ≠ T.dist r (basicRootOf T hT r m p) % 2

noncomputable def repairParents [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (hT : T.IsTree) (r : V) (m : ℕ) : Finset V := by
  classical
  exact Finset.univ.filter fun p =>
    ∃ w : V, ∃ hw : w ∈ basicRoots T hT r m, ∃ hwr : w ≠ r,
      IsBadBasicRoot T hT r m w ∧ parent hT r hwr = p

@[simp] theorem mem_repairParents [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (hT : T.IsTree) (r : V) (m : ℕ) (p : V) :
    p ∈ repairParents T hT r m ↔
      ∃ w : V, ∃ hw : w ∈ basicRoots T hT r m, ∃ hwr : w ≠ r,
        IsBadBasicRoot T hT r m w ∧ parent hT r hwr = p := by
  classical
  simp [repairParents]

noncomputable def repairedRoots [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (hT : T.IsTree) (r : V) (m : ℕ) : Finset V :=
  basicRoots T hT r m ∪ repairParents T hT r m

theorem repairParents_disjoint_basicRoots [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (hT : T.IsTree) (r : V) (m : ℕ) :
    Disjoint (repairParents T hT r m) (basicRoots T hT r m) := by
  rw [Finset.disjoint_left]
  intro p hpRepair hpBasic
  obtain ⟨w, hw, hwr, hbad, hp⟩ :=
    (mem_repairParents T hT r m p).mp hpRepair
  rcases hbad with ⟨_, _, hpNotRoot, _⟩
  have hpNot : p ≠ basicRootOf T hT r m p := by
    simpa [hp] using hpNotRoot
  have hpFixed : basicRootOf T hT r m p = p := by
    rcases (mem_basicRoots T hT r m p).mp hpBasic with hpr | hpLarge
    · calc
        basicRootOf T hT r m p = basicRootOf T hT r m r :=
          congrArg (basicRootOf T hT r m) hpr
        _ = r := basicRootOf_root T hT r m
        _ = p := hpr.symm
    · exact basicRootOf_eq_self_of_large T hT r m hpLarge
  exact hpNot hpFixed.symm

noncomputable def repairWitness [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (hT : T.IsTree) (r : V) (m : ℕ)
    (p : V) (hp : p ∈ repairParents T hT r m) : V :=
  ((mem_repairParents T hT r m p).mp hp).choose

theorem repairWitness_spec [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (hT : T.IsTree) (r : V) (m : ℕ)
    (p : V) (hp : p ∈ repairParents T hT r m) :
    ∃ hw : repairWitness T hT r m p hp ∈ basicRoots T hT r m,
      ∃ hwr : repairWitness T hT r m p hp ≠ r,
        IsBadBasicRoot T hT r m (repairWitness T hT r m p hp) ∧
          parent hT r hwr = p :=
  ((mem_repairParents T hT r m p).mp hp).choose_spec

theorem repairWitness_parity_ne [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (hT : T.IsTree) (r : V) (m : ℕ)
    (p : V) (hp : p ∈ repairParents T hT r m) :
    T.dist r (repairWitness T hT r m p hp) % 2 ≠ T.dist r p % 2 := by
  obtain ⟨hw, hwr, hbad, hparent⟩ := repairWitness_spec T hT r m p hp
  apply rootParity_ne_of_adj hT r
  simpa [hparent] using (parent_adj hT r hwr).symm

noncomputable def repairCode [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (hT : T.IsTree) (r : V) (m : ℕ) (p : V) : V :=
  if hp : p ∈ repairParents T hT r m then repairWitness T hT r m p hp else r

noncomputable def repairedRootCode [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (hT : T.IsTree) (r : V) (m : ℕ) (x : V) : V :=
  if x ∈ basicRoots T hT r m then x else repairCode T hT r m x

theorem repairCode_spec [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (hT : T.IsTree) (r : V) (m : ℕ) {p : V}
    (hp : p ∈ repairParents T hT r m) :
    ∃ hw : repairCode T hT r m p ∈ basicRoots T hT r m,
      ∃ hwr : repairCode T hT r m p ≠ r,
        IsBadBasicRoot T hT r m (repairCode T hT r m p) ∧
          parent hT r hwr = p := by
  rw [repairCode]
  simp only [dif_pos hp]
  exact repairWitness_spec T hT r m p hp

theorem repairCode_parity_ne [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (hT : T.IsTree) (r : V) (m : ℕ) {p : V}
    (hp : p ∈ repairParents T hT r m) :
    T.dist r (repairCode T hT r m p) % 2 ≠ T.dist r p % 2 := by
  rw [repairCode]
  simp only [dif_pos hp]
  exact repairWitness_parity_ne T hT r m p hp

theorem repairedRootCode_mapsTo_basicRoots [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (hT : T.IsTree) (r : V) (m : ℕ) (q : Fin 2) :
    Set.MapsTo (repairedRootCode T hT r m)
      ↑((repairedRoots T hT r m).filter fun x => T.dist r x % 2 = q.val)
      ↑(basicRoots T hT r m) := by
  intro x hx
  have hxR := (Finset.mem_filter.mp hx).1
  rw [repairedRoots, Finset.mem_union] at hxR
  by_cases hxBasic : x ∈ basicRoots T hT r m
  · simpa [repairedRootCode, hxBasic]
  · have hxRepair : x ∈ repairParents T hT r m := hxR.resolve_left hxBasic
    simp only [repairedRootCode, if_neg hxBasic]
    exact (repairCode_spec T hT r m hxRepair).choose

theorem repairedRootCode_injOn_parity [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (hT : T.IsTree) (r : V) (m : ℕ) (q : Fin 2) :
    Set.InjOn (repairedRootCode T hT r m)
      ↑((repairedRoots T hT r m).filter fun x => T.dist r x % 2 = q.val) := by
  intro x hx y hy hcode
  have hxMem := (Finset.mem_filter.mp hx).1
  have hyMem := (Finset.mem_filter.mp hy).1
  have hxParity := (Finset.mem_filter.mp hx).2
  have hyParity := (Finset.mem_filter.mp hy).2
  rw [repairedRoots, Finset.mem_union] at hxMem hyMem
  by_cases hxBasic : x ∈ basicRoots T hT r m
  · by_cases hyBasic : y ∈ basicRoots T hT r m
    · simpa [repairedRootCode, hxBasic, hyBasic] using hcode
    · have hyRepair : y ∈ repairParents T hT r m := hyMem.resolve_left hyBasic
      have hxy : x = repairCode T hT r m y := by
        simpa [repairedRootCode, hxBasic, hyBasic] using hcode
      exfalso
      apply repairCode_parity_ne T hT r m hyRepair
      rw [← hxy, hxParity, hyParity]
  · have hxRepair : x ∈ repairParents T hT r m := hxMem.resolve_left hxBasic
    by_cases hyBasic : y ∈ basicRoots T hT r m
    · have hxy : repairCode T hT r m x = y := by
        simpa [repairedRootCode, hxBasic, hyBasic] using hcode
      exfalso
      apply repairCode_parity_ne T hT r m hxRepair
      rw [hxy, hxParity, hyParity]
    · have hyRepair : y ∈ repairParents T hT r m := hyMem.resolve_left hyBasic
      have hcodes : repairCode T hT r m x = repairCode T hT r m y := by
        simpa [repairedRootCode, hxBasic, hyBasic] using hcode
      obtain ⟨hxw, hxwr, hxbad, hxparent⟩ :=
        repairCode_spec T hT r m hxRepair
      obtain ⟨hyw, hywr, hybad, hyparent⟩ :=
        repairCode_spec T hT r m hyRepair
      have hyAdj : T.Adj y (repairCode T hT r m x) := by
        rw [hcodes]
        simpa only [hyparent] using parent_adj hT r hywr
      have hyDist : T.dist r y + 1 = T.dist r (repairCode T hT r m x) := by
        rw [hcodes]
        simpa only [hyparent] using parent_dist_add_one hT r hywr
      have hyEq : y = parent hT r hxwr :=
        eq_parent_of_adj_of_dist_add_one hT r hxwr hyAdj hyDist
      exact hxparent.symm.trans hyEq.symm

/-- Zhao's parity repair adds parents of the bad attachments.  Each parity
class of repaired roots still injects into the basic roots: old roots map to
themselves, new parent roots map to one of their child roots of opposite
parity. -/
theorem repairedRoots_parity_bound [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (hT : T.IsTree) (r : V) (m : ℕ) (q : Fin 2) :
    ((repairedRoots T hT r m).filter fun x => T.dist r x % 2 = q.val).card ≤
      (Fintype.card V + m) / (m + 1) := by
  exact (Finset.card_le_card_of_injOn (repairedRootCode T hT r m)
    (repairedRootCode_mapsTo_basicRoots T hT r m q)
    (repairedRootCode_injOn_parity T hT r m q)).trans
      (card_basicRoots_le T hT r m)

/-- Nearest repaired root above a vertex. -/
noncomputable def repairedRootOf [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (hT : T.IsTree) (r : V) (m : ℕ) (x : V) : V :=
  if hx : x ∈ repairedRoots T hT r m then x
  else
    let hxr : x ≠ r := by
      intro h
      subst x
      apply hx
      simp [repairedRoots]
    repairedRootOf T hT r m (parent hT r hxr)
termination_by T.dist r x
decreasing_by
  have hp := parent_dist_add_one hT r hxr
  omega

theorem repairedRootOf_eq_self [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (hT : T.IsTree) (r : V) (m : ℕ) {x : V}
    (hx : x ∈ repairedRoots T hT r m) : repairedRootOf T hT r m x = x := by
  rw [repairedRootOf.eq_def]
  simp [hx]

theorem repairedRootOf_eq_parent [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (hT : T.IsTree) (r : V) (m : ℕ) {x : V}
    (hx : x ∉ repairedRoots T hT r m) (hxr : x ≠ r) :
    repairedRootOf T hT r m x =
      repairedRootOf T hT r m (parent hT r hxr) := by
  rw [repairedRootOf.eq_def]
  simp [hx]

theorem repairedRootOf_mem [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (hT : T.IsTree) (r : V) (m : ℕ) (x : V) :
    repairedRootOf T hT r m x ∈ repairedRoots T hT r m := by
  refine repairedRootOf.induct T hT r m (motive := fun x =>
    repairedRootOf T hT r m x ∈ repairedRoots T hT r m) ?_ ?_ x
  · intro x hx
    rw [repairedRootOf_eq_self T hT r m hx]
    exact hx
  · intro x hx hxr ih
    rw [repairedRootOf_eq_parent T hT r m hx hxr]
    exact ih

theorem basicRootOf_repairedRootOf [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (hT : T.IsTree) (r : V) (m : ℕ) (x : V) :
    basicRootOf T hT r m (repairedRootOf T hT r m x) =
      basicRootOf T hT r m x := by
  refine repairedRootOf.induct T hT r m (motive := fun x =>
    basicRootOf T hT r m (repairedRootOf T hT r m x) =
      basicRootOf T hT r m x) ?_ ?_ x
  · intro x hx
    rw [repairedRootOf_eq_self T hT r m hx]
  · intro x hx hxr ih
    have hxBasic : x ∉ basicRoots T hT r m := by
      intro hxb
      apply hx
      exact Finset.mem_union_left _ hxb
    have hsmall : residualSize T hT r m x ≤ m := by
      by_contra hlarge
      apply hxBasic
      simp [Nat.lt_of_not_ge hlarge]
    rw [repairedRootOf_eq_parent T hT r m hx hxr, ih]
    exact (basicRootOf_eq_parent_of_small T hT r m hxr hsmall).symm

theorem repairParent_parity_eq_basicRoot [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (hT : T.IsTree) (r : V) (m : ℕ) {p : V}
    (hp : p ∈ repairParents T hT r m) :
    T.dist r p % 2 = T.dist r (basicRootOf T hT r m p) % 2 := by
  obtain ⟨w, hw, hwr, hbad, hparent⟩ :=
    (mem_repairParents T hT r m p).mp hp
  rcases hbad with ⟨_, _, hpNot, hwBadParity⟩
  have hwp : T.dist r w % 2 ≠ T.dist r p % 2 := by
    apply rootParity_ne_of_adj hT r
    simpa only [hparent] using (parent_adj hT r hwr).symm
  have hwBadParity' :
      T.dist r w % 2 ≠ T.dist r (basicRootOf T hT r m p) % 2 := by
    simpa only [hparent] using hwBadParity
  have hwlt : T.dist r w % 2 < 2 := Nat.mod_lt _ (by omega)
  have hplt : T.dist r p % 2 < 2 := Nat.mod_lt _ (by omega)
  have hblt : T.dist r (basicRootOf T hT r m p) % 2 < 2 :=
    Nat.mod_lt _ (by omega)
  omega

theorem repairedRoot_parity_eq_basicRoot [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (hT : T.IsTree) (r : V) (m : ℕ) {x : V}
    (hx : x ∈ repairedRoots T hT r m) :
    T.dist r x % 2 = T.dist r (basicRootOf T hT r m x) % 2 := by
  rw [repairedRoots, Finset.mem_union] at hx
  rcases hx with hxBasic | hxRepair
  · have hfixed : basicRootOf T hT r m x = x := by
      rcases (mem_basicRoots T hT r m x).mp hxBasic with hxr | hlarge
      · subst x
        simp
      · exact basicRootOf_eq_self_of_large T hT r m hlarge
    rw [hfixed]
  · exact repairParent_parity_eq_basicRoot T hT r m hxRepair

/-- The repaired fibers satisfy Zhao's reconnection rule.  If the actual
parent is not itself the root of the preceding piece, the two piece roots
have the same global-root parity. -/
theorem repaired_reconnect_rule [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (hT : T.IsTree) (r : V) (m : ℕ) {x : V}
    (hx : x ∈ repairedRoots T hT r m) (hxr : x ≠ r) :
    let p := parent hT r hxr
    p = repairedRootOf T hT r m p ∨
      T.dist r x % 2 = T.dist r (repairedRootOf T hT r m p) % 2 := by
  let p := parent hT r hxr
  by_cases hp : p ∈ repairedRoots T hT r m
  · left
    exact (repairedRootOf_eq_self T hT r m hp).symm
  · right
    have htargetMem := repairedRootOf_mem T hT r m p
    have htargetParity := repairedRoot_parity_eq_basicRoot T hT r m htargetMem
    rw [basicRootOf_repairedRootOf T hT r m p] at htargetParity
    suffices hxParity : T.dist r x % 2 = T.dist r (basicRootOf T hT r m p) % 2 by
      exact hxParity.trans htargetParity.symm
    rw [repairedRoots, Finset.mem_union] at hx
    rcases hx with hxBasic | hxRepair
    · by_contra hpar
      have hpNotFixed : p ≠ basicRootOf T hT r m p := by
        intro hfixed
        apply hp
        apply Finset.mem_union_left
        have hrootMem := basicRootOf_mem_basicRoots T hT r m p
        have hpBasic : p ∈ basicRoots T hT r m := by
          rw [hfixed]
          exact hrootMem
        exact hpBasic
      have hbad : IsBadBasicRoot T hT r m x := by
        exact ⟨hxBasic, hxr, hpNotFixed, hpar⟩
      apply hp
      apply Finset.mem_union_right
      rw [mem_repairParents]
      exact ⟨x, hxBasic, hxr, hbad, rfl⟩
    · have hxNotBasic : x ∉ basicRoots T hT r m := by
        exact fun hxb => (Finset.disjoint_left.mp
          (repairParents_disjoint_basicRoots T hT r m)) hxRepair hxb
      have hxSmall : residualSize T hT r m x ≤ m := by
        by_contra hlarge
        apply hxNotBasic
        simp [Nat.lt_of_not_ge hlarge]
      have hbasic := basicRootOf_eq_parent_of_small T hT r m hxr hxSmall
      have hxParityBase := repairParent_parity_eq_basicRoot T hT r m hxRepair
      rw [hbasic] at hxParityBase
      exact hxParityBase

noncomputable def repairedFiber [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (hT : T.IsTree) (r : V) (m : ℕ) (a : V) : Finset V :=
  Finset.univ.filter fun x => repairedRootOf T hT r m x = a

@[simp] theorem mem_repairedFiber [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (hT : T.IsTree) (r : V) (m : ℕ) (a x : V) :
    x ∈ repairedFiber T hT r m a ↔ repairedRootOf T hT r m x = a := by
  simp [repairedFiber]

theorem repairedFibers_biUnion [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (hT : T.IsTree) (r : V) (m : ℕ) :
    (repairedRoots T hT r m).biUnion (repairedFiber T hT r m) = Finset.univ := by
  ext x
  simp only [Finset.mem_biUnion, mem_repairedFiber, Finset.mem_univ, iff_true]
  exact ⟨repairedRootOf T hT r m x, repairedRootOf_mem T hT r m x, rfl⟩

theorem repairedFibers_pairwiseDisjoint [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (hT : T.IsTree) (r : V) (m : ℕ) :
    (↑(repairedRoots T hT r m) : Set V).PairwiseDisjoint
      (repairedFiber T hT r m) := by
  rintro a ha b hb hab
  simp only [Function.onFun]
  rw [Finset.disjoint_left]
  intro x hxa hxb
  rw [mem_repairedFiber] at hxa hxb
  exact hab (hxa.symm.trans hxb)

theorem residualSize_le_of_repairedFiber_off_root [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (hT : T.IsTree) (r : V) (m : ℕ) {a x : V}
    (hx : x ∈ repairedFiber T hT r m a) (hxa : x ≠ a) :
    residualSize T hT r m x ≤ m := by
  rw [mem_repairedFiber] at hx
  have hxNotRepaired : x ∉ repairedRoots T hT r m := by
    intro hxRoot
    have hself := repairedRootOf_eq_self T hT r m hxRoot
    exact hxa (hself.symm.trans hx)
  have hxNotBasic : x ∉ basicRoots T hT r m := by
    exact fun hxb => hxNotRepaired (Finset.mem_union_left _ hxb)
  by_contra hlarge
  apply hxNotBasic
  simp [Nat.lt_of_not_ge hlarge]

theorem parent_mem_same_repairedFiber_off_root [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (hT : T.IsTree) (r : V) (m : ℕ) {a x : V}
    (hx : x ∈ repairedFiber T hT r m a) (hxa : x ≠ a) :
    ∃ hxr : x ≠ r, parent hT r hxr ∈ repairedFiber T hT r m a := by
  rw [mem_repairedFiber] at hx
  have hxNotRepaired : x ∉ repairedRoots T hT r m := by
    intro hxRoot
    exact hxa ((repairedRootOf_eq_self T hT r m hxRoot).symm.trans hx)
  have hxr : x ≠ r := by
    intro h
    subst x
    apply hxNotRepaired
    simp [repairedRoots]
  refine ⟨hxr, ?_⟩
  rw [mem_repairedFiber]
  rw [← repairedRootOf_eq_parent T hT r m hxNotRepaired hxr]
  exact hx

theorem dist_repairedRootOf_le [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (hT : T.IsTree) (r : V) (m : ℕ) (x : V) :
    T.dist r (repairedRootOf T hT r m x) ≤ T.dist r x := by
  refine repairedRootOf.induct T hT r m (motive := fun x =>
    T.dist r (repairedRootOf T hT r m x) ≤ T.dist r x) ?_ ?_ x
  · intro x hx
    rw [repairedRootOf_eq_self T hT r m hx]
  · intro x hx hxr ih
    rw [repairedRootOf_eq_parent T hT r m hx hxr]
    exact ih.trans (by
      have hp := parent_dist_add_one hT r hxr
      omega)

/-- A root-set/fiber formulation of Zhao Definition 6.2.  Ordering is encoded
intrinsically by strict decrease of root distance along every attachment.  The
`m`-tree bound is recorded through the residual pieces, whose exact cardinality
was proved in `card_residualVertices`; the fibers are obtained only by further
splitting those basic pieces. -/
structure ZhaoResidualForestPartition [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (hT : T.IsTree) (globalRoot : V) (m : ℕ) where
  roots : Finset V
  rootOf : V → V
  globalRoot_mem : globalRoot ∈ roots
  rootOf_mem : ∀ x, rootOf x ∈ roots
  roots_fixed : ∀ x ∈ roots, rootOf x = x
  fibers_cover : roots.biUnion (fun a => Finset.univ.filter fun x => rootOf x = a) =
    Finset.univ
  fibers_disjoint : (↑roots : Set V).PairwiseDisjoint
    (fun a => Finset.univ.filter fun x => rootOf x = a)
  branch_card_le : ∀ a x, rootOf x = a → x ≠ a →
    (residualVertices T hT globalRoot m x).card ≤ m
  parent_closed : ∀ a x, rootOf x = a → x ≠ a →
    ∃ hxr : x ≠ globalRoot, rootOf (parent hT globalRoot hxr) = a
  parent_root_earlier : ∀ x, x ∈ roots → ∀ hxr : x ≠ globalRoot,
    T.dist globalRoot (rootOf (parent hT globalRoot hxr)) < T.dist globalRoot x
  parity_root_bound : ∀ q : Fin 2,
    (roots.filter fun x => T.dist globalRoot x % 2 = q.val).card ≤
      (Fintype.card V + m) / (m + 1)
  reconnect_rule : ∀ x, x ∈ roots → ∀ hxr : x ≠ globalRoot,
    let p := parent hT globalRoot hxr
    p = rootOf p ∨
      T.dist globalRoot x % 2 = T.dist globalRoot (rootOf p) % 2

theorem exists_zhaoResidualForestPartition [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (hT : T.IsTree) (r : V) (m : ℕ) :
    Nonempty (ZhaoResidualForestPartition T hT r m) := by
  refine ⟨{
    roots := repairedRoots T hT r m
    rootOf := repairedRootOf T hT r m
    globalRoot_mem := by simp [repairedRoots]
    rootOf_mem := repairedRootOf_mem T hT r m
    roots_fixed := by
      intro x hx
      exact repairedRootOf_eq_self T hT r m hx
    fibers_cover := repairedFibers_biUnion T hT r m
    fibers_disjoint := repairedFibers_pairwiseDisjoint T hT r m
    branch_card_le := by
      intro a x hx hxa
      rw [card_residualVertices T hT r m x]
      exact residualSize_le_of_repairedFiber_off_root T hT r m
        ((mem_repairedFiber T hT r m a x).mpr hx) hxa
    parent_closed := by
      intro a x hx hxa
      obtain ⟨hxr, hp⟩ := parent_mem_same_repairedFiber_off_root T hT r m
        ((mem_repairedFiber T hT r m a x).mpr hx) hxa
      exact ⟨hxr, (mem_repairedFiber T hT r m a _).mp hp⟩
    parent_root_earlier := by
      intro x hx hxr
      exact (dist_repairedRootOf_le T hT r m (parent hT r hxr)).trans_lt (by
        have hp := parent_dist_add_one hT r hxr
        omega)
    parity_root_bound := repairedRoots_parity_bound T hT r m
    reconnect_rule := by
      intro x hx hxr
      exact repaired_reconnect_rule T hT r m hx hxr
  }⟩

end Erdos547b.TreePartition

#print axioms Erdos547b.TreePartition.exists_zhaoResidualForestPartition
