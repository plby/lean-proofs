/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.ResidualTreePartition
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Prod.Lex

open scoped Sym2

noncomputable section

namespace Erdos547b.TreePartition

open Finset Fintype SimpleGraph

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (T : SimpleGraph V) (hT : T.IsTree) (r : V) (m : ℕ)

/-- The actual cut edge attached to every non-global residual root. -/
def residualCutEdges (P : ZhaoResidualForestPartition T hT r m) :
    Finset (Sym2 V) :=
  Finset.univ.image fun x : {x : V // x ∈ P.roots ∧ x ≠ r} ↦
    s(x.1, parent hT r x.2.2)

/-- The forest obtained by carrying out all residual-root cuts. -/
abbrev residualCutGraph (P : ZhaoResidualForestPartition T hT r m) :
    SimpleGraph V :=
  T.deleteEdges (↑(residualCutEdges T hT r m P) : Set (Sym2 V))

theorem residualCutEdge_injective
    (P : ZhaoResidualForestPartition T hT r m)
    {x y : V} (hxr : x ≠ r) (hyr : y ≠ r)
    (hxy : s(x, parent hT r hxr) = s(y, parent hT r hyr)) : x = y := by
  rcases Sym2.eq_iff.mp hxy with h | h
  · exact h.1
  · have hx := parent_dist_add_one hT r hxr
    have hy := parent_dist_add_one hT r hyr
    have h₁ := congrArg (T.dist r) h.1
    have h₂ := congrArg (T.dist r) h.2
    omega

theorem not_root_of_ne_rootOf
    (P : ZhaoResidualForestPartition T hT r m) {x : V}
    (hx : x ≠ P.rootOf x) : x ∉ P.roots := by
  intro hroot
  exact hx (P.roots_fixed x hroot).symm

theorem residualCutGraph_parent_adj
    (P : ZhaoResidualForestPartition T hT r m) {x : V}
    (hx : x ≠ P.rootOf x) (hxr : x ≠ r) :
    (residualCutGraph T hT r m P).Adj
      (parent hT r hxr) x := by
  apply SimpleGraph.deleteEdges_adj.mpr
  refine ⟨parent_adj hT r hxr, ?_⟩
  intro hcut
  change s(parent hT r hxr, x) ∈ residualCutEdges T hT r m P at hcut
  rw [residualCutEdges, Finset.mem_image] at hcut
  obtain ⟨y, -, hy⟩ := hcut
  have hy' : s(x, parent hT r hxr) =
      s(y.1, parent hT r y.2.2) := Sym2.eq_swap.trans hy.symm
  have hxy := residualCutEdge_injective T hT r m P hxr y.2.2 hy'
  exact not_root_of_ne_rootOf T hT r m P hx (hxy ▸ y.2.1)

theorem rootOf_eq_of_residualCutGraph_adj
    (P : ZhaoResidualForestPartition T hT r m) {x y : V}
    (hxy : (residualCutGraph T hT r m P).Adj x y) :
    P.rootOf x = P.rootOf y := by
  have hxyT : T.Adj x y := (SimpleGraph.deleteEdges_adj.mp hxy).1
  rcases hT.dist_eq_dist_add_one_of_adj r hxyT with hlevel | hlevel
  · have hxr : x ≠ r := by
      intro hxr
      subst x
      have hzero : T.dist r r = 0 := by simp
      omega
    have hparent : y = parent hT r hxr :=
      eq_parent_of_adj_of_dist_add_one hT r hxr hxyT.symm hlevel.symm
    have hxnot : x ∉ P.roots := by
      intro hxroot
      have hmem : s(x, parent hT r hxr) ∈ residualCutEdges T hT r m P := by
        rw [residualCutEdges, Finset.mem_image]
        exact ⟨⟨x, hxroot, hxr⟩, Finset.mem_univ _, rfl⟩
      have hnot := (SimpleGraph.deleteEdges_adj.mp hxy).2
      apply hnot
      change s(x, y) ∈ residualCutEdges T hT r m P
      simpa only [hparent] using hmem
    have hxne : x ≠ P.rootOf x := by
      intro heq
      apply hxnot
      rw [heq]
      exact P.rootOf_mem x
    obtain ⟨_hxr', hp⟩ := P.parent_closed (P.rootOf x) x rfl hxne
    simpa only [hparent] using hp.symm
  · have hyr : y ≠ r := by
      intro hyr
      subst y
      have hzero : T.dist r r = 0 := by simp
      omega
    have hparent : x = parent hT r hyr :=
      eq_parent_of_adj_of_dist_add_one hT r hyr hxyT hlevel.symm
    have hynot : y ∉ P.roots := by
      intro hyroot
      have hmem : s(y, parent hT r hyr) ∈ residualCutEdges T hT r m P := by
        rw [residualCutEdges, Finset.mem_image]
        exact ⟨⟨y, hyroot, hyr⟩, Finset.mem_univ _, rfl⟩
      have hnot := (SimpleGraph.deleteEdges_adj.mp hxy).2
      apply hnot
      change s(x, y) ∈ residualCutEdges T hT r m P
      simpa only [hparent, Sym2.eq_swap] using hmem
    have hyne : y ≠ P.rootOf y := by
      intro heq
      apply hynot
      rw [heq]
      exact P.rootOf_mem y
    obtain ⟨_hyr', hp⟩ := P.parent_closed (P.rootOf y) y rfl hyne
    simpa only [hparent] using hp

theorem residualCutGraph_reachable_rootOf
    (P : ZhaoResidualForestPartition T hT r m) (x : V) :
    (residualCutGraph T hT r m P).Reachable x (P.rootOf x) := by
  induction hd : T.dist r x using Nat.strong_induction_on generalizing x with
  | h d ih =>
      by_cases hx : x = P.rootOf x
      · rw [hx]
        rw [P.roots_fixed (P.rootOf x) (P.rootOf_mem x)]
      · have hxr : x ≠ r := by
          intro h
          subst x
          exact hx (P.roots_fixed r P.globalRoot_mem).symm
        obtain ⟨hxr', hp⟩ := P.parent_closed (P.rootOf x) x rfl hx
        have hsame : hxr' = hxr := Subsingleton.elim _ _
        subst hxr'
        have hpd : T.dist r (parent hT r hxr) < d := by
          have hdist := parent_dist_add_one hT r hxr
          omega
        have hi := ih (T.dist r (parent hT r hxr)) hpd
          (parent hT r hxr) rfl
        rw [hp] at hi
        exact (residualCutGraph_parent_adj T hT r m P hx hxr).symm.reachable.trans hi

theorem rootOf_eq_of_residualCutGraph_reachable
    (P : ZhaoResidualForestPartition T hT r m) {x y : V}
    (hxy : (residualCutGraph T hT r m P).Reachable x y) :
    P.rootOf x = P.rootOf y := by
  rcases hxy with ⟨w⟩
  induction w with
  | nil => rfl
  | cons hadj w ih =>
      exact (rootOf_eq_of_residualCutGraph_adj T hT r m P hadj).trans ih

theorem residualCutGraph_connectedComponentMk_eq_iff
    (P : ZhaoResidualForestPartition T hT r m) (x y : V) :
    (residualCutGraph T hT r m P).connectedComponentMk x =
        (residualCutGraph T hT r m P).connectedComponentMk y ↔
      P.rootOf x = P.rootOf y := by
  constructor
  · intro h
    exact rootOf_eq_of_residualCutGraph_reachable T hT r m P
      (SimpleGraph.ConnectedComponent.exact h)
  · intro h
    apply SimpleGraph.ConnectedComponent.sound
    exact (residualCutGraph_reachable_rootOf T hT r m P x).trans
      ((h ▸ residualCutGraph_reachable_rootOf T hT r m P y).symm)

/-! ### A distance-sorted enumeration of the residual roots -/

/-- Root-distance followed by an arbitrary finite tie-breaker. -/
def rootDistanceKey (x : V) : ℕ ×ₗ ℕ :=
  toLex (T.dist r x, (Fintype.equivFin V x).val)

theorem rootDistanceKey_injective :
    Function.Injective (rootDistanceKey T r : V → ℕ ×ₗ ℕ) := by
  intro x y h
  have h' := toLex.injective h
  have hval : (Fintype.equivFin V x).val = (Fintype.equivFin V y).val :=
    congrArg Prod.snd h'
  apply (Fintype.equivFin V).injective
  exact Fin.ext hval

/-- The linear order used to number roots.  It refines strict root distance. -/
def rootDistanceLinearOrder : LinearOrder V :=
  LinearOrder.lift' (rootDistanceKey T r) (rootDistanceKey_injective T r)

theorem lt_rootDistanceLinearOrder_of_dist_lt {x y : V}
    (hxy : T.dist r x < T.dist r y) :
    @LT.lt V (rootDistanceLinearOrder T r).toLT x y := by
  change rootDistanceKey T r x < rootDistanceKey T r y
  rw [Prod.Lex.lt_iff]
  exact Or.inl hxy

/-- The roots, increasingly numbered by distance from the global root. -/
def residualRootEnum (P : ZhaoResidualForestPartition T hT r m) :
    Fin P.roots.card ≃ P.roots := by
  letI : LinearOrder V := rootDistanceLinearOrder T r
  exact (P.roots.orderIsoOfFin rfl).toEquiv

@[simp] theorem residualRootEnum_mem
    (P : ZhaoResidualForestPartition T hT r m) (i : Fin P.roots.card) :
    (residualRootEnum T hT r m P i).1 ∈ P.roots :=
  (residualRootEnum T hT r m P i).2

theorem residualRootEnum_zero
    (P : ZhaoResidualForestPartition T hT r m)
    (hpos : 0 < P.roots.card) :
    (residualRootEnum T hT r m P ⟨0, hpos⟩).1 = r := by
  let : LinearOrder V := rootDistanceLinearOrder T r
  let e : Fin P.roots.card ≃o P.roots := P.roots.orderIsoOfFin rfl
  have hle : e ⟨0, hpos⟩ ≤ ⟨r, P.globalRoot_mem⟩ := by
    have hfin : (⟨0, hpos⟩ : Fin P.roots.card) ≤
        e.symm ⟨r, P.globalRoot_mem⟩ := by
      rw [Fin.le_iff_val_le_val]
      exact Nat.zero_le _
    simpa using e.monotone hfin
  change rootDistanceKey T r (e ⟨0, hpos⟩).1 ≤ rootDistanceKey T r r at hle
  rw [Prod.Lex.le_iff] at hle
  have hzero : T.dist r (e ⟨0, hpos⟩).1 = 0 := by
    rcases hle with hlt | heq
    · simp only [rootDistanceKey, ofLex_toLex, SimpleGraph.dist_self] at hlt
      omega
    · simpa only [rootDistanceKey, ofLex_toLex, SimpleGraph.dist_self] using heq.1
  have her : (e ⟨0, hpos⟩).1 = r :=
    ((hT.connected.dist_eq_zero_iff (u := r) (v := (e ⟨0, hpos⟩).1)).mp hzero).symm
  change (e ⟨0, hpos⟩).1 = r
  exact her

/-- Index of a residual root in the distance-sorted enumeration. -/
def residualRootIndex (P : ZhaoResidualForestPartition T hT r m)
    (x : V) (hx : x ∈ P.roots) : Fin P.roots.card :=
  (residualRootEnum T hT r m P).symm ⟨x, hx⟩

@[simp] theorem residualRootEnum_index
    (P : ZhaoResidualForestPartition T hT r m) (x : V) (hx : x ∈ P.roots) :
    (residualRootEnum T hT r m P (residualRootIndex T hT r m P x hx)).1 = x := by
  exact congrArg Subtype.val ((residualRootEnum T hT r m P).apply_symm_apply ⟨x, hx⟩)

theorem residualRootIndex_lt_of_dist_lt
    (P : ZhaoResidualForestPartition T hT r m)
    {x y : V} (hx : x ∈ P.roots) (hy : y ∈ P.roots)
    (hxy : T.dist r x < T.dist r y) :
    (residualRootIndex T hT r m P x hx).val <
      (residualRootIndex T hT r m P y hy).val := by
  let : LinearOrder V := rootDistanceLinearOrder T r
  let e : Fin P.roots.card ≃o P.roots := P.roots.orderIsoOfFin rfl
  have hsub : (⟨x, hx⟩ : P.roots) < ⟨y, hy⟩ := by
    exact lt_rootDistanceLinearOrder_of_dist_lt T r hxy
  have hind : e.symm ⟨x, hx⟩ < e.symm ⟨y, hy⟩ :=
    e.symm.lt_iff_lt.mpr hsub
  change e.symm ⟨x, hx⟩ < e.symm ⟨y, hy⟩
  exact hind

@[simp] theorem residualRootIndex_enum
    (P : ZhaoResidualForestPartition T hT r m) (j : Fin P.roots.card) :
    residualRootIndex T hT r m P
      (residualRootEnum T hT r m P j).1
      (residualRootEnum_mem T hT r m P j) = j := by
  exact (residualRootEnum T hT r m P).symm_apply_apply j

/-- The numbered root is non-global exactly when its index is nonzero. -/
theorem residualRootEnum_ne_global_of_val_ne_zero
    (P : ZhaoResidualForestPartition T hT r m)
    (j : Fin P.roots.card) (hj : j.val ≠ 0) :
    (residualRootEnum T hT r m P j).1 ≠ r := by
  have hpos : 0 < P.roots.card := Finset.card_pos.mpr ⟨r, P.globalRoot_mem⟩
  intro hroot
  have hzeroRoot := residualRootEnum_zero T hT r m P hpos
  have hj0 : j = ⟨0, hpos⟩ := by
    apply (residualRootEnum T hT r m P).injective
    apply Subtype.ext
    exact hroot.trans hzeroRoot.symm
  exact hj (congrArg Fin.val hj0)

/-- Parent vertex attached to a numbered non-global residual root. -/
def residualNumberedParent (P : ZhaoResidualForestPartition T hT r m)
    (j : Fin P.roots.card) (hj : j.val ≠ 0) : V :=
  parent hT r (residualRootEnum_ne_global_of_val_ne_zero T hT r m P j hj)

/-- The component index containing a numbered root's parent. -/
def residualNumberedParentPart (P : ZhaoResidualForestPartition T hT r m)
    (j : Fin P.roots.card) (hj : j.val ≠ 0) : Fin P.roots.card :=
  residualRootIndex T hT r m P
    (P.rootOf (residualNumberedParent T hT r m P j hj))
    (P.rootOf_mem _)

theorem residualNumberedParentPart_earlier
    (P : ZhaoResidualForestPartition T hT r m)
    (j : Fin P.roots.card) (hj : j.val ≠ 0) :
    (residualNumberedParentPart T hT r m P j hj).val < j.val := by
  let x := (residualRootEnum T hT r m P j).1
  let hxr : x ≠ r := residualRootEnum_ne_global_of_val_ne_zero T hT r m P j hj
  have hd := P.parent_root_earlier x
    (residualRootEnum_mem T hT r m P j) hxr
  have hindex := residualRootIndex_lt_of_dist_lt T hT r m P
    (P.rootOf_mem (parent hT r hxr))
    (residualRootEnum_mem T hT r m P j) hd
  change (residualNumberedParentPart T hT r m P j hj).val < j.val
  simpa only [residualNumberedParentPart, residualNumberedParent,
    residualRootIndex_enum, x, hxr] using hindex

theorem zhaoCutEdges_residualRootEnum
    (P : ZhaoResidualForestPartition T hT r m) :
    zhaoCutEdges
      (fun i => (residualRootEnum T hT r m P i).1)
      (residualNumberedParent T hT r m P) =
        residualCutEdges T hT r m P := by
  ext e
  constructor
  · intro he
    rw [zhaoCutEdges, Finset.mem_image] at he
    obtain ⟨j, -, rfl⟩ := he
    rw [residualCutEdges, Finset.mem_image]
    let x : {x : V // x ∈ P.roots ∧ x ≠ r} :=
      ⟨(residualRootEnum T hT r m P j.1).1,
        residualRootEnum_mem T hT r m P j.1,
        residualRootEnum_ne_global_of_val_ne_zero T hT r m P j.1 j.2⟩
    exact ⟨x, Finset.mem_univ _, rfl⟩
  · intro he
    rw [residualCutEdges, Finset.mem_image] at he
    obtain ⟨x, -, rfl⟩ := he
    let j := residualRootIndex T hT r m P x.1 x.2.1
    have hjroot : (residualRootEnum T hT r m P j).1 = x.1 :=
      residualRootEnum_index T hT r m P x.1 x.2.1
    have hj : j.val ≠ 0 := by
      intro hj0
      have hpos : 0 < P.roots.card := Finset.card_pos.mpr ⟨r, P.globalRoot_mem⟩
      have hjeq : j = ⟨0, hpos⟩ := Fin.ext hj0
      rw [hjeq, residualRootEnum_zero T hT r m P hpos] at hjroot
      exact x.2.2 hjroot.symm
    rw [zhaoCutEdges, Finset.mem_image]
    refine ⟨⟨j, hj⟩, Finset.mem_univ _, ?_⟩
    rw [Sym2.eq_iff]
    left
    refine ⟨hjroot, ?_⟩
    let a : {z : V // z ≠ r} :=
      ⟨(residualRootEnum T hT r m P j).1,
        residualRootEnum_ne_global_of_val_ne_zero T hT r m P j hj⟩
    let b : {z : V // z ≠ r} := ⟨x.1, x.2.2⟩
    have hab : a = b := Subtype.ext hjroot
    exact congrArg (fun z : {z : V // z ≠ r} => parent hT r z.2) hab

/-! ### Identification of the connected components -/

/-- Residual roots are in bijection with the connected components of the cut
graph. -/
def residualComponents (P : ZhaoResidualForestPartition T hT r m) :
    Fin P.roots.card ≃ (residualCutGraph T hT r m P).ConnectedComponent :=
  Equiv.ofBijective
    (fun i => (residualCutGraph T hT r m P).connectedComponentMk
      (residualRootEnum T hT r m P i).1) (by
      constructor
      · intro i j hij
        have hrootOf :=
          (residualCutGraph_connectedComponentMk_eq_iff T hT r m P _ _).mp hij
        rw [P.roots_fixed _ (residualRootEnum_mem T hT r m P i),
          P.roots_fixed _ (residualRootEnum_mem T hT r m P j)] at hrootOf
        apply (residualRootEnum T hT r m P).injective
        exact Subtype.ext hrootOf
      · intro C
        refine SimpleGraph.ConnectedComponent.ind (G := residualCutGraph T hT r m P)
          (fun x => ?_) C
        let i := residualRootIndex T hT r m P (P.rootOf x) (P.rootOf_mem x)
        refine ⟨i, ?_⟩
        apply SimpleGraph.ConnectedComponent.sound
        have hr := residualCutGraph_reachable_rootOf T hT r m P x
        have hi : (residualRootEnum T hT r m P i).1 = P.rootOf x :=
          residualRootEnum_index T hT r m P _ _
        rw [hi]
        exact hr.symm)

theorem mem_residualComponents_iff
    (P : ZhaoResidualForestPartition T hT r m)
    (i : Fin P.roots.card) (x : V) :
    x ∈ (residualComponents T hT r m P i).supp ↔
      P.rootOf x = (residualRootEnum T hT r m P i).1 := by
  change (residualCutGraph T hT r m P).connectedComponentMk x =
      residualComponents T hT r m P i ↔ _
  change (residualCutGraph T hT r m P).connectedComponentMk x =
      (residualCutGraph T hT r m P).connectedComponentMk
        (residualRootEnum T hT r m P i).1 ↔ _
  rw [residualCutGraph_connectedComponentMk_eq_iff T hT r m P]
  rw [P.roots_fixed _ (residualRootEnum_mem T hT r m P i)]

theorem residualRoot_mem_component
    (P : ZhaoResidualForestPartition T hT r m)
    (i : Fin P.roots.card) :
    (residualRootEnum T hT r m P i).1 ∈
      (residualComponents T hT r m P i).supp := by
  rw [mem_residualComponents_iff T hT r m P]
  exact P.roots_fixed _ (residualRootEnum_mem T hT r m P i)

theorem residualNumberedParent_mem_component
    (P : ZhaoResidualForestPartition T hT r m)
    (j : Fin P.roots.card) (hj : j.val ≠ 0) :
    residualNumberedParent T hT r m P j hj ∈
      (residualComponents T hT r m P
        (residualNumberedParentPart T hT r m P j hj)).supp := by
  rw [mem_residualComponents_iff T hT r m P]
  exact (residualRootEnum_index T hT r m P _ _).symm

/-! ### The rooted `m`-tree bound inside each component -/

theorem residualVertices_child_subset {x y : V}
    (hxy : IsChild T r x y) (hsmall : residualSize T hT r m y ≤ m) :
    residualVertices T hT r m y ⊆ residualVertices T hT r m x := by
  intro z hz
  rw [residualVertices.eq_def]
  simp only [Finset.mem_insert, Finset.mem_biUnion, Finset.mem_univ, true_and]
  right
  let ys : {y : V // y ∈ children T r x} := ⟨y, mem_children.mpr hxy⟩
  refine ⟨ys, ?_⟩
  change z ∈ if residualSize T hT r m y ≤ m then
    residualVertices T hT r m y else ∅
  rw [if_pos hsmall]
  exact hz

theorem residualVertices_transitive (x : V) :
    ∀ {z : V}, z ∈ residualVertices T hT r m x →
      residualVertices T hT r m z ⊆ residualVertices T hT r m x := by
  classical
  refine residualVertices.induct T hT r (motive := fun x =>
    ∀ {z : V}, z ∈ residualVertices T hT r m x →
      residualVertices T hT r m z ⊆ residualVertices T hT r m x) ?_ x
  intro x ih z hz
  rw [residualVertices.eq_def] at hz
  simp only [Finset.mem_insert, Finset.mem_biUnion, Finset.mem_univ, true_and] at hz
  rcases hz with rfl | ⟨y, hy⟩
  · exact fun _ h => h
  · split at hy
    next hsmall =>
      exact (ih y hy).trans
        (residualVertices_child_subset T hT r m (mem_children.mp y.2) hsmall)
    next hlarge => simp at hy

/-- A parent-chain walk from a vertex to its residual root, with its exact
length measured by global-root distance. -/
theorem exists_residualCutGraph_walk_rootOf
    (P : ZhaoResidualForestPartition T hT r m) (x : V) :
    ∃ w : (residualCutGraph T hT r m P).Walk x (P.rootOf x),
      w.length + T.dist r (P.rootOf x) = T.dist r x := by
  induction hd : T.dist r x using Nat.strong_induction_on generalizing x with
  | h d ih =>
      by_cases hx : x = P.rootOf x
      · refine ⟨SimpleGraph.Walk.nil.copy rfl hx, ?_⟩
        have hdist : T.dist r (P.rootOf x) = d := by
          rw [← hx]
          exact hd
        simpa only [SimpleGraph.Walk.length_copy, SimpleGraph.Walk.length_nil,
          zero_add] using hdist
      · have hxr : x ≠ r := by
          intro h
          subst x
          exact hx (P.roots_fixed r P.globalRoot_mem).symm
        obtain ⟨hxr', hp⟩ := P.parent_closed (P.rootOf x) x rfl hx
        have hsame : hxr' = hxr := Subsingleton.elim _ _
        subst hxr'
        have hpd : T.dist r (parent hT r hxr) < d := by
          have hdist := parent_dist_add_one hT r hxr
          omega
        obtain ⟨w, hw⟩ := ih (T.dist r (parent hT r hxr)) hpd
          (parent hT r hxr) rfl
        let w' : (residualCutGraph T hT r m P).Walk
            (parent hT r hxr) (P.rootOf x) := w.copy rfl hp
        have hw' : w'.length + T.dist r (P.rootOf x) =
            T.dist r (parent hT r hxr) := by
          simpa only [w', SimpleGraph.Walk.length_copy, hp] using hw
        refine ⟨SimpleGraph.Walk.cons
          (residualCutGraph_parent_adj T hT r m P hx hxr).symm w', ?_⟩
        simp only [SimpleGraph.Walk.length_cons]
        have hdist := parent_dist_add_one hT r hxr
        omega

/-- Lift an ambient walk whose endpoints lie in a connected component to
that component's induced graph, retaining its length. -/
def walkToSimpleGraphWithLength
    {G : SimpleGraph V} (C : G.ConnectedComponent) {x y : V}
    (hx : x ∈ C.supp) (hy : y ∈ C.supp) (w : G.Walk x y) :
    {q : C.toSimpleGraph.Walk ⟨x, hx⟩ ⟨y, hy⟩ // q.length = w.length} := by
  cases w with
  | nil => exact ⟨SimpleGraph.Walk.nil, rfl⟩
  | @cons v z y h p =>
      have hz : z ∈ C.supp := C.mem_supp_of_adj_mem_supp hx h
      have h' : C.toSimpleGraph.Adj ⟨x, hx⟩ ⟨z, hz⟩ := h
      let q := walkToSimpleGraphWithLength C hz hy p
      refine ⟨SimpleGraph.Walk.cons h' q.1, ?_⟩
      simp only [SimpleGraph.Walk.length_cons]
      exact congrArg Nat.succ q.2

/-- Exact component-root distance: cutting does not change the parent-chain
distance inside a residual fiber. -/
theorem residualComponent_dist_root_add
    (P : ZhaoResidualForestPartition T hT r m)
    (i : Fin P.roots.card)
    (x : residualComponents T hT r m P i) :
    (residualComponents T hT r m P i).toSimpleGraph.dist
        ⟨(residualRootEnum T hT r m P i).1,
          residualRoot_mem_component T hT r m P i⟩ x +
      T.dist r (residualRootEnum T hT r m P i).1 = T.dist r x.1 := by
  let C := residualComponents T hT r m P i
  let a : V := (residualRootEnum T hT r m P i).1
  have hrootOf : P.rootOf x.1 = a :=
    (mem_residualComponents_iff T hT r m P i x.1).mp x.2
  obtain ⟨w₀, hw₀⟩ := exists_residualCutGraph_walk_rootOf T hT r m P x.1
  let w : (residualCutGraph T hT r m P).Walk x.1 a := w₀.copy rfl hrootOf
  have hw : w.length + T.dist r a = T.dist r x.1 := by
    simpa only [w, SimpleGraph.Walk.length_copy, hrootOf] using hw₀
  let q := walkToSimpleGraphWithLength C x.2
    (residualRoot_mem_component T hT r m P i) w
  have hupp : C.toSimpleGraph.dist
      ⟨a, residualRoot_mem_component T hT r m P i⟩ x ≤ w.length := by
    rw [SimpleGraph.dist_comm]
    exact (SimpleGraph.dist_le q.1).trans_eq q.2
  obtain ⟨p, hp⟩ := C.connected_toSimpleGraph.exists_walk_length_eq_dist
    (⟨a, residualRoot_mem_component T hT r m P i⟩ : C) x
  let plift := (p.map C.toSimpleGraph_hom).mapLe
    (T.deleteEdges_le (↑(residualCutEdges T hT r m P) : Set (Sym2 V)))
  have hlow : T.dist a x.1 ≤ C.toSimpleGraph.dist
      ⟨a, residualRoot_mem_component T hT r m P i⟩ x := by
    rw [← hp]
    have hplift := SimpleGraph.dist_le plift
    simp only [C.toSimpleGraph_hom_apply] at hplift
    have hlength : plift.length = p.length := by
      simp only [plift, SimpleGraph.Walk.length_mapLe,
        SimpleGraph.Walk.length_map]
    exact hplift.trans_eq hlength
  have htriangle := hT.connected.dist_triangle (u := r) (v := a) (w := x.1)
  change C.toSimpleGraph.dist
      ⟨a, residualRoot_mem_component T hT r m P i⟩ x +
    T.dist r a = T.dist r x.1
  omega

/-- Every strict descendant in a finite rooted tree lies below an immediate
child.  This local form avoids importing any of the later embedding files. -/
theorem exists_child_of_mem_rootedDescendants_local
    {W : Type*} {S : SimpleGraph W} (hS : S.IsTree)
    {root x y : W} (hy : y ∈ rootedDescendantsSet S root x) (hyx : y ≠ x) :
    ∃ z : W, IsChild S root x z ∧
      y ∈ rootedDescendantsSet S root z ∧
      S.dist x y = 1 + S.dist z y := by
  obtain ⟨p, hpPath, hpLength⟩ := hS.connected.exists_path_of_dist x y
  have hpNotNil : ¬ p.Nil := SimpleGraph.Walk.not_nil_of_ne hyx.symm
  let z := p.snd
  have hxz : S.Adj x z := p.adj_snd hpNotNil
  have hxzDist : S.dist x z = 1 := S.dist_eq_one_iff_adj.mpr hxz
  have htailLength : p.tail.length = S.dist z y :=
    SimpleGraph.length_eq_dist_of_subwalk hpLength
      ((SimpleGraph.Walk.isSubwalk_rfl p).tail)
  have hsplit : S.dist x y = 1 + S.dist z y := by
    rw [← hpLength, ← htailLength]
    have hlen := p.length_tail_add_one hpNotNil
    omega
  have hyroot := hy
  change S.dist root y = S.dist root x + S.dist x y at hyroot
  rcases hS.dist_eq_dist_add_one_of_adj root hxz with hup | hdown
  · have htriangle := hS.connected.dist_triangle (u := root) (v := z) (w := y)
    omega
  · refine ⟨z, ⟨hxz, hdown⟩, ?_, hsplit⟩
    change S.dist root y = S.dist root z + S.dist z y
    exact (by omega)

/-- Ambient distance is at most distance inside a cut component. -/
theorem residualComponent_ambient_dist_le
    (P : ZhaoResidualForestPartition T hT r m)
    (i : Fin P.roots.card)
    (x y : residualComponents T hT r m P i) :
    T.dist x.1 y.1 ≤
      (residualComponents T hT r m P i).toSimpleGraph.dist x y := by
  let C := residualComponents T hT r m P i
  obtain ⟨p, hp⟩ := C.connected_toSimpleGraph.exists_walk_length_eq_dist x y
  let plift := (p.map C.toSimpleGraph_hom).mapLe
    (T.deleteEdges_le (↑(residualCutEdges T hT r m P) : Set (Sym2 V)))
  have hdist := SimpleGraph.dist_le plift
  simp only [C.toSimpleGraph_hom_apply] at hdist
  have hlength : plift.length = p.length := by
    simp only [plift, SimpleGraph.Walk.length_mapLe,
      SimpleGraph.Walk.length_map]
  rw [← hp]
  exact hdist.trans_eq hlength

/-- A child in a cut component, with the component rooted at its residual
root, is also a child in the original globally rooted tree. -/
theorem residualComponent_child_is_global_child
    (P : ZhaoResidualForestPartition T hT r m)
    (i : Fin P.roots.card)
    {x y : residualComponents T hT r m P i}
    (hxy : IsChild (residualComponents T hT r m P i).toSimpleGraph
      ⟨(residualRootEnum T hT r m P i).1,
        residualRoot_mem_component T hT r m P i⟩ x y) :
    IsChild T r x.1 y.1 := by
  let C := residualComponents T hT r m P i
  let a : C := ⟨(residualRootEnum T hT r m P i).1,
    residualRoot_mem_component T hT r m P i⟩
  have hadjCut : (residualCutGraph T hT r m P).Adj x.1 y.1 := hxy.1
  have hadjT : T.Adj x.1 y.1 := (SimpleGraph.deleteEdges_adj.mp hadjCut).1
  have hxdist := residualComponent_dist_root_add T hT r m P i x
  have hydist := residualComponent_dist_root_add T hT r m P i y
  change C.toSimpleGraph.dist a x +
    T.dist r (residualRootEnum T hT r m P i).1 = T.dist r x.1 at hxdist
  change C.toSimpleGraph.dist a y +
    T.dist r (residualRootEnum T hT r m P i).1 = T.dist r y.1 at hydist
  refine ⟨hadjT, ?_⟩
  change T.dist r y.1 = T.dist r x.1 + 1
  have hlevel := hxy.2
  change C.toSimpleGraph.dist a y = C.toSimpleGraph.dist a x + 1 at hlevel
  omega

/-- Component descendants are contained in the recursively retained residual
piece below their starting vertex. -/
theorem residualComponent_descendant_mem_residualVertices
    (P : ZhaoResidualForestPartition T hT r m)
    (i : Fin P.roots.card)
    (x y : residualComponents T hT r m P i)
    (hy : y ∈ rootedDescendantsSet
      (residualComponents T hT r m P i).toSimpleGraph
      ⟨(residualRootEnum T hT r m P i).1,
        residualRoot_mem_component T hT r m P i⟩ x) :
    y.1 ∈ residualVertices T hT r m x.1 := by
  let C := residualComponents T hT r m P i
  let a : C := ⟨(residualRootEnum T hT r m P i).1,
    residualRoot_mem_component T hT r m P i⟩
  have hCTree : C.toSimpleGraph.IsTree :=
    isTree_deleteEdges_connectedComponent_of_isTree hT _ C
  induction hd : C.toSimpleGraph.dist x y using Nat.strong_induction_on
      generalizing x y with
  | h d ih =>
      by_cases hyx : y = x
      · subst y
        exact self_mem_residualVertices T hT r m x.1
      · obtain ⟨z, hxz, hyz, hsplit⟩ :=
          exists_child_of_mem_rootedDescendants_local hCTree hy hyx
        have hzylt : C.toSimpleGraph.dist z y < d := by omega
        have hyRVz := ih (C.toSimpleGraph.dist z y) hzylt z y hyz rfl
        have hxzGlobal :=
          residualComponent_child_is_global_child T hT r m P i hxz
        have hzRootOf : P.rootOf z.1 = (residualRootEnum T hT r m P i).1 :=
          (mem_residualComponents_iff T hT r m P i z.1).mp z.2
        have hzNeRoot : z.1 ≠ (residualRootEnum T hT r m P i).1 := by
          intro hz
          have hzsub : z = a := Subtype.ext hz
          have hlevel := hxz.2
          change C.toSimpleGraph.dist a z = C.toSimpleGraph.dist a x + 1 at hlevel
          rw [hzsub] at hlevel
          simp at hlevel
        have hzCard := P.branch_card_le
          (residualRootEnum T hT r m P i).1 z.1 hzRootOf hzNeRoot
        have hzSmall : residualSize T hT r m z.1 ≤ m := by
          rw [← card_residualVertices T hT r m z.1]
          exact hzCard
        exact residualVertices_child_subset T hT r m hxzGlobal hzSmall hyRVz

/-- Each numbered cut component is an `m`-tree in Zhao's exact `Set.ncard`
formulation. -/
theorem residualComponent_isRootedMTreeNcard
    (P : ZhaoResidualForestPartition T hT r m)
    (i : Fin P.roots.card) :
    IsRootedMTreeNcard m
      (residualComponents T hT r m P i).toSimpleGraph
      ⟨(residualRootEnum T hT r m P i).1,
        residualRoot_mem_component T hT r m P i⟩ := by
  let C := residualComponents T hT r m P i
  let a : C := ⟨(residualRootEnum T hT r m P i).1,
    residualRoot_mem_component T hT r m P i⟩
  refine ⟨isTree_deleteEdges_connectedComponent_of_isTree hT _ C, ?_⟩
  intro x hxa
  have hxRootOf : P.rootOf x.1 = (residualRootEnum T hT r m P i).1 :=
    (mem_residualComponents_iff T hT r m P i x.1).mp x.2
  have hxNeRoot : x.1 ≠ (residualRootEnum T hT r m P i).1 := by
    intro hx
    exact hxa (Subtype.ext hx)
  have hcard := P.branch_card_le
    (residualRootEnum T hT r m P i).1 x.1 hxRootOf hxNeRoot
  apply (Set.ncard_le_ncard_of_injOn (s := rootedDescendantsSet C.toSimpleGraph a x)
    (t := (↑(residualVertices T hT r m x.1) : Set V)) Subtype.val ?_
      (Set.injOn_of_injective Subtype.val_injective)).trans
  · simpa using hcard
  · intro y hy
    exact residualComponent_descendant_mem_residualVertices T hT r m P i x y hy

/-! ### Assembly of the literal `ZhaoForestPartition` structure -/

theorem card_filter_residualRootEnum
    (P : ZhaoResidualForestPartition T hT r m) (p : V → Prop)
    [DecidablePred p] :
    (Finset.univ.filter fun i : Fin P.roots.card =>
      p (residualRootEnum T hT r m P i).1).card =
      (P.roots.filter p).card := by
  classical
  apply Finset.card_bij
    (fun i _ => (residualRootEnum T hT r m P i).1)
  · intro i hi
    rw [Finset.mem_filter] at hi ⊢
    exact ⟨residualRootEnum_mem T hT r m P i, hi.2⟩
  · intro i hi j hj hij
    apply (residualRootEnum T hT r m P).injective
    exact Subtype.ext hij
  · intro x hx
    rw [Finset.mem_filter] at hx
    let i := residualRootIndex T hT r m P x hx.1
    refine ⟨i, ?_, ?_⟩
    · rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by
        simpa only [i, residualRootEnum_index] using hx.2⟩
    · exact residualRootEnum_index T hT r m P x hx.1

theorem cast_connectedComponentMk
    {G H : SimpleGraph V} (h : G = H) (x : V) :
    Equiv.cast (congrArg (fun K : SimpleGraph V => K.ConnectedComponent) h)
        (G.connectedComponentMk x) = H.connectedComponentMk x := by
  subst H
  rfl

theorem mem_cast_connectedComponent
    {G H : SimpleGraph V} (h : G = H) (C : G.ConnectedComponent)
    {x : V} (hx : x ∈ C.supp) :
    x ∈ (Equiv.cast
      (congrArg (fun K : SimpleGraph V => K.ConnectedComponent) h) C).supp := by
  subst H
  exact hx

theorem cast_connectedComponent_isRootedMTreeNcard
    {G H : SimpleGraph V} (h : G = H) (C : G.ConnectedComponent)
    (root : V) (hroot : root ∈ C.supp)
    (hm : IsRootedMTreeNcard m C.toSimpleGraph ⟨root, hroot⟩) :
    IsRootedMTreeNcard m
      (Equiv.cast
        (congrArg (fun K : SimpleGraph V => K.ConnectedComponent) h) C).toSimpleGraph
      ⟨root, mem_cast_connectedComponent h C hroot⟩ := by
  subst H
  simpa using hm

/-- The residual root/fiber partition canonically determines all fields of
the literal numbered forest partition: roots are distance-sorted, cut
components are the fibers, and every structural field is transported from
the residual invariants. -/
theorem exists_zhaoForestPartition (hT : T.IsTree) [DecidableRel T.Adj] :
    Nonempty (ZhaoForestPartition T r m) := by
  classical
  let P : ZhaoResidualForestPartition T hT r m :=
    Classical.choice (exists_zhaoResidualForestPartition T hT r m)
  have hpos : 0 < P.roots.card :=
    Finset.card_pos.mpr ⟨r, P.globalRoot_mem⟩
  let rootsFn : Fin P.roots.card → V :=
    fun i => (residualRootEnum T hT r m P i).1
  let parentFn : ∀ j : Fin P.roots.card, j.val ≠ 0 → V :=
    residualNumberedParent T hT r m P
  have hcuts : zhaoCutEdges rootsFn parentFn =
      residualCutEdges T hT r m P := by
    simpa only [rootsFn, parentFn] using
      zhaoCutEdges_residualRootEnum T hT r m P
  have hgraph : residualCutGraph T hT r m P =
      T.deleteEdges
        (↑(zhaoCutEdges rootsFn parentFn) : Set (Sym2 V)) := by
    rw [hcuts]
  let ccCast : (residualCutGraph T hT r m P).ConnectedComponent ≃
      (T.deleteEdges
        (↑(zhaoCutEdges rootsFn parentFn) : Set (Sym2 V))).ConnectedComponent :=
    Equiv.cast (congrArg
      (fun K : SimpleGraph V => K.ConnectedComponent) hgraph)
  let componentsFn : Fin P.roots.card ≃
      (T.deleteEdges
        (↑(zhaoCutEdges rootsFn parentFn) : Set (Sym2 V))).ConnectedComponent := by
    exact (residualComponents T hT r m P).trans ccCast
  refine ⟨{
    numParts := P.roots.card
    numParts_pos := hpos
    roots := rootsFn
    parent := parentFn
    cut_adj := ?_
    components := componentsFn
    root_mem := ?_
    first_root := ?_
    parentPart := residualNumberedParentPart T hT r m P
    parent_mem := ?_
    parent_earlier := ?_
    component_mTree := ?_
    parity_root_bound := ?_
    reconnect_rule := ?_
  }⟩
  · intro j hj
    exact (parent_adj hT r
      (residualRootEnum_ne_global_of_val_ne_zero T hT r m P j hj)).symm
  · intro i
    change (T.deleteEdges
      (↑(zhaoCutEdges rootsFn parentFn) : Set (Sym2 V))).connectedComponentMk
        (rootsFn i) = componentsFn i
    rw [← cast_connectedComponentMk hgraph]
    change ccCast ((residualCutGraph T hT r m P).connectedComponentMk
      (residualRootEnum T hT r m P i).1) =
        ccCast (residualComponents T hT r m P i)
    exact congrArg ccCast (residualRoot_mem_component T hT r m P i)
  · change (residualRootEnum T hT r m P ⟨0, hpos⟩).1 = r
    exact residualRootEnum_zero T hT r m P hpos
  · intro j hj
    change (T.deleteEdges
      (↑(zhaoCutEdges rootsFn parentFn) : Set (Sym2 V))).connectedComponentMk
        (parentFn j hj) =
      componentsFn (residualNumberedParentPart T hT r m P j hj)
    rw [← cast_connectedComponentMk hgraph]
    change ccCast ((residualCutGraph T hT r m P).connectedComponentMk
      (residualNumberedParent T hT r m P j hj)) =
        ccCast (residualComponents T hT r m P
          (residualNumberedParentPart T hT r m P j hj))
    exact congrArg ccCast
      (residualNumberedParent_mem_component T hT r m P j hj)
  · exact residualNumberedParentPart_earlier T hT r m P
  · intro i
    change IsRootedMTreeNcard m
      (ccCast (residualComponents T hT r m P i)).toSimpleGraph
      ⟨(residualRootEnum T hT r m P i).1, _⟩
    simpa only [ccCast] using
      cast_connectedComponent_isRootedMTreeNcard (m := m) hgraph
        (residualComponents T hT r m P i)
        (residualRootEnum T hT r m P i).1
        (residualRoot_mem_component T hT r m P i)
        (residualComponent_isRootedMTreeNcard T hT r m P i)
  · intro q
    change (Finset.univ.filter fun i : Fin P.roots.card =>
      T.dist r (residualRootEnum T hT r m P i).1 % 2 = q.val).card ≤ _
    calc
      _ = (P.roots.filter fun x => T.dist r x % 2 = q.val).card :=
        card_filter_residualRootEnum T hT r m P _
      _ ≤ _ := P.parity_root_bound q
  · intro j hj
    let x : V := (residualRootEnum T hT r m P j).1
    let hxr : x ≠ r :=
      residualRootEnum_ne_global_of_val_ne_zero T hT r m P j hj
    let p : V := parent hT r hxr
    have hrec := P.reconnect_rule x
      (residualRootEnum_mem T hT r m P j) hxr
    have hparent : parentFn j hj = p := by
      simp only [parentFn, residualNumberedParent, p, x]
    have hroot :
        rootsFn (residualNumberedParentPart T hT r m P j hj) = P.rootOf p := by
      change (residualRootEnum T hT r m P
        (residualNumberedParentPart T hT r m P j hj)).1 = P.rootOf p
      exact residualRootEnum_index T hT r m P _ _
    rcases hrec with hp | hpar
    · left
      rw [hparent, hroot]
      exact hp
    · right
      change T.dist r x % 2 =
        T.dist r (rootsFn (residualNumberedParentPart T hT r m P j hj)) % 2
      rw [hroot]
      exact hpar

end Erdos547b.TreePartition

#print axioms Erdos547b.TreePartition.exists_zhaoForestPartition
