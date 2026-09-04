/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos916.AHTWatkinsMesner
import ErdosProblems.Erdos916.AHTK32Routing
import ErdosProblems.Erdos916.ThreeTerminalPath
import ErdosProblems.Erdos916.Blocks

/-!
# The maximal-separator step of Watkins--Mesner

This module is deliberately above both the source `K_{3,2}` construction
and its clean routing lemma.  It develops the finite Menger extraction of
the two vertex cuts used in AHT Theorem 5.1.  Keeping this step in a higher
module avoids a dependency cycle: `AHTWatkinsMesner` supplies the theta
source and the literal seven-condition certificate, while
`AHTK32Routing` supplies the six-half-route argument.
-/

attribute [local instance] Classical.propDecidable

namespace Erdos916

open SimpleGraph

universe u

variable {V : Type} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Transport a complementary connected component across equality of the
deleted vertex sets. -/
def ComponentCompl.transport {K L : Set V} (h : K = L)
    (C : G.ComponentCompl K) : G.ComponentCompl L :=
  h ▸ C

@[simp] theorem ComponentCompl.mem_transport {K L : Set V} (h : K = L)
    (C : G.ComponentCompl K) (v : V) :
    v ∈ (ComponentCompl.transport h C : Set V) ↔ v ∈ (C : Set V) := by
  subst L
  rfl

/-- A walk which starts in a complementary connected component and avoids
the deleted set stays in that component. -/
theorem ComponentCompl.walk_end_mem {K : Set V}
    (D : G.ComponentCompl K) {a b : V} (p : G.Walk a b)
    (ha : a ∈ (D : Set V))
    (havoid : ∀ w, w ∈ p.support → w ∉ K) : b ∈ (D : Set V) := by
  induction p with
  | nil => exact ha
  | @cons a b c hab p ih =>
      apply ih
      · exact ComponentCompl.mem_of_adj a b ha
          (havoid b (by simp)) hab
      · intro w hw
        exact havoid w (by simp [hw])

/-- Two vertices of one complementary component are joined by a simple
ambient path all of whose vertices remain in that component. -/
theorem ComponentCompl.exists_path_within {K : Set V}
    (D : G.ComponentCompl K) {a b : V}
    (ha : a ∈ (D : Set V)) (hb : b ∈ (D : Set V)) :
    ∃ p : G.Walk a b, p.IsPath ∧
      ∀ w, w ∈ p.support → w ∈ (D : Set V) := by
  let a' : {w : V // w ∈ Kᶜ} := ⟨a, ha.1⟩
  let b' : {w : V // w ∈ Kᶜ} := ⟨b, hb.1⟩
  have hreach : (G.induce Kᶜ).Reachable a' b' :=
    ConnectedComponent.exact (ha.2.trans hb.2.symm)
  obtain ⟨q, hq⟩ := hreach.exists_isPath
  let inc : G.induce Kᶜ →g G :=
    (SimpleGraph.Embedding.induce (G := G) (s := Kᶜ)).toHom
  let p₀ := q.map inc
  let p : G.Walk a b := p₀.copy rfl rfl
  have hp : p.IsPath := by
    exact (Walk.isPath_copy p₀ rfl rfl).2
      (hq.map Subtype.val_injective)
  have hpAvoid : ∀ w, w ∈ p.support → w ∉ K := by
    intro w hw
    have hw₀ : w ∈ p₀.support := by
      change w ∈ (p₀.copy rfl rfl).support at hw
      rw [Walk.support_copy] at hw
      exact hw
    change w ∈ (q.map inc).support at hw₀
    rw [Walk.support_map] at hw₀
    obtain ⟨v, -, rfl⟩ := List.mem_map.mp hw₀
    have hvinc : inc v = v.1 := rfl
    rw [hvinc]
    exact v.2
  refine ⟨p, hp, ?_⟩
  intro w hw
  apply ComponentCompl.walk_end_mem D (p.takeUntil w hw) ha
  intro v hv
  exact hpAvoid v (p.support_takeUntil_subset_support hw hv)

/-! ## Splitting a fan centre into three false twins -/

/-- Replace `x` by three source copies. -/
abbrev ThreeSplitVertex (x : V) := Fin 3 ⊕ {v : V // v ≠ x}

/-- The graph obtained by replacing `x` by three pairwise nonadjacent false
twins, each having the old neighbourhood of `x`. -/
def threeSplitGraph (G : SimpleGraph V) (x : V) :
    SimpleGraph (ThreeSplitVertex x) where
  Adj p q :=
    match p, q with
    | .inl _, .inl _ => False
    | .inl _, .inr q => G.Adj x q.1
    | .inr p, .inl _ => G.Adj p.1 x
    | .inr p, .inr q => G.Adj p.1 q.1
  symm := ⟨by
    rintro (i | p) (j | q) <;> simp only
    · exact id
    · exact G.adj_symm
    · exact G.adj_symm
    · exact G.adj_symm⟩
  loopless := ⟨by
    rintro (i | p) <;> simp only
    · exact id
    · exact G.loopless.irrefl p.1⟩

@[simp] theorem threeSplitGraph_adj_source_old {x : V} {i : Fin 3}
    {v : {w : V // w ≠ x}} :
    (threeSplitGraph G x).Adj (.inl i) (.inr v) ↔ G.Adj x v.1 :=
  Iff.rfl

@[simp] theorem threeSplitGraph_adj_old_source {x : V} {i : Fin 3}
    {v : {w : V // w ≠ x}} :
    (threeSplitGraph G x).Adj (.inr v) (.inl i) ↔ G.Adj v.1 x :=
  Iff.rfl

@[simp] theorem threeSplitGraph_adj_old_old {x : V}
    {v w : {q : V // q ≠ x}} :
    (threeSplitGraph G x).Adj (.inr v) (.inr w) ↔ G.Adj v.1 w.1 :=
  Iff.rfl

@[simp] theorem not_threeSplitGraph_adj_source_source {x : V}
    {i j : Fin 3} : ¬(threeSplitGraph G x).Adj (.inl i) (.inl j) :=
  id

/-- Lift an old walk all of whose vertices avoid the split vertex. -/
def threeSplitTail {x : V} :
    ∀ {a b : V} (p : G.Walk a b) (hout : ∀ w ∈ p.support, w ≠ x),
      (threeSplitGraph G x).Walk
        (.inr ⟨a, hout a p.start_mem_support⟩)
        (.inr ⟨b, hout b p.end_mem_support⟩)
  | _, _, .nil, _ => .nil
  | _, _, .cons hab q, hout =>
      .cons (by exact hab)
        (threeSplitTail q fun w hw ↦ hout w (by simp [hw]))

private theorem threeSplitTail_cons_eq {x a b c : V} (hab : G.Adj a b)
    (q : G.Walk b c) (hout : ∀ w ∈ (q.cons hab).support, w ≠ x) :
    threeSplitTail (q.cons hab) hout =
      (threeSplitTail q (fun w hw ↦ hout w (by simp [hw]))).cons
        (show (threeSplitGraph G x).Adj
          (.inr ⟨a, hout a (by simp)⟩)
          (.inr ⟨b, hout b (by simp)⟩) from hab) := by
  rfl

private theorem threeSplitTail_support_cases {x a b : V}
    (p : G.Walk a b) (hout : ∀ w ∈ p.support, w ≠ x)
    {q : ThreeSplitVertex x} (hq : q ∈ (threeSplitTail p hout).support) :
    ∃ w, ∃ hwx : w ≠ x, w ∈ p.support ∧ q = .inr ⟨w, hwx⟩ := by
  let rec go {a b : V} (p : G.Walk a b)
      (hout : ∀ w ∈ p.support, w ≠ x) {q : ThreeSplitVertex x}
      (hq : q ∈ (threeSplitTail p hout).support) :
      ∃ w, ∃ hwx : w ≠ x, w ∈ p.support ∧ q = .inr ⟨w, hwx⟩ := by
    cases p with
    | nil =>
        refine ⟨a, hout a (by simp), by simp, ?_⟩
        simpa [threeSplitTail] using hq
    | @cons a b c hab r =>
        have hq' : q = .inr ⟨a, hout a (by simp)⟩ ∨
            q ∈ (threeSplitTail r
              (fun w hw ↦ hout w (by simp [hw]))).support := by
          rw [threeSplitTail_cons_eq hab r hout, Walk.support_cons] at hq
          exact List.mem_cons.mp hq
        rcases hq' with rfl | hq'
        · exact ⟨a, hout a (by simp), by simp, rfl⟩
        · obtain ⟨w, hwx, hwr, rfl⟩ := go r _ hq'
          exact ⟨w, hwx, by simp [hwr], rfl⟩
  exact go p hout hq

private theorem threeSplitTail_isPath {x a b : V} (p : G.Walk a b)
    (hp : p.IsPath) (hout : ∀ w ∈ p.support, w ≠ x) :
    (threeSplitTail p hout).IsPath := by
  rw [Walk.isPath_def]
  induction p with
  | nil => simp [threeSplitTail]
  | @cons a b c hab q ih =>
      rw [threeSplitTail_cons_eq hab q hout, Walk.support_cons,
        List.nodup_cons]
      have hpN : (a :: q.support).Nodup := hp.support_nodup
      constructor
      · intro ha
        obtain ⟨w, hwx, hwq, haw⟩ := threeSplitTail_support_cases q _ ha
        have : a = w := by
          have h := congrArg (fun z : ThreeSplitVertex x ↦ match z with
            | .inl _ => x
            | .inr z => z.1) haw
          simpa using h
        exact (List.nodup_cons.mp hpN).1 (this ▸ hwq)
      · exact ih (Walk.IsPath.mk' (List.nodup_cons.mp hpN).2) _

/-- Lift a nontrivial old path beginning at `x` to a path beginning at a
chosen source copy. -/
noncomputable def threeSplitArm {x t : V} (i : Fin 3)
    (p : G.Walk x t) (hp : p.IsPath) (hxt : x ≠ t) :
    (threeSplitGraph G x).Walk (.inl i) (.inr ⟨t, hxt.symm⟩) := by
  cases p with
  | nil => exact False.elim (hxt rfl)
  | @cons _ a _ hxa q =>
      have hout : ∀ w ∈ q.support, w ≠ x := by
        intro w hw h
        subst w
        exact (List.nodup_cons.mp hp.support_nodup).1 hw
      exact (threeSplitTail q hout).cons (by exact hxa)

private theorem threeSplitArm_cons_eq {x a t : V} (i : Fin 3)
    (hxa : G.Adj x a) (q : G.Walk a t) (hp : (q.cons hxa).IsPath)
    (hxt : x ≠ t) :
    threeSplitArm i (q.cons hxa) hp hxt =
      (threeSplitTail q (fun w hw ↦ by
        exact fun h ↦ (List.nodup_cons.mp hp.support_nodup).1 (h ▸ hw))).cons
        (show (threeSplitGraph G x).Adj (.inl i)
          (.inr ⟨a, by
            exact fun h ↦ (List.nodup_cons.mp hp.support_nodup).1
              (h ▸ q.start_mem_support)⟩) from hxa) := by
  rfl

private theorem threeSplitArm_isPath {x t : V} (i : Fin 3)
    (p : G.Walk x t) (hp : p.IsPath) (hxt : x ≠ t) :
    (threeSplitArm i p hp hxt).IsPath := by
  cases p with
  | nil => exact False.elim (hxt rfl)
  | @cons _ a _ hxa q =>
      have hpN : (x :: q.support).Nodup := hp.support_nodup
      have hq : q.IsPath := Walk.IsPath.mk' (List.nodup_cons.mp hpN).2
      have hout : ∀ w ∈ q.support, w ≠ x := by
        intro w hw h
        subst w
        exact (List.nodup_cons.mp hpN).1 hw
      have hfresh : (.inl i : ThreeSplitVertex x) ∉
          (threeSplitTail q hout).support := by
        intro h
        obtain ⟨w, hwx, -, heq⟩ := threeSplitTail_support_cases q hout h
        simp at heq
      exact (threeSplitTail_isPath q hq hout).cons hfresh

private theorem threeSplitArm_support_cases {x t : V} (i : Fin 3)
    (p : G.Walk x t) (hp : p.IsPath) (hxt : x ≠ t)
    {q : ThreeSplitVertex x} (hq : q ∈ (threeSplitArm i p hp hxt).support) :
    q = .inl i ∨
      ∃ w, ∃ hwx : w ≠ x, w ∈ p.support ∧ q = .inr ⟨w, hwx⟩ := by
  cases p with
  | nil => exact False.elim (hxt rfl)
  | @cons _ a _ hxa r =>
      have hout : ∀ w ∈ r.support, w ≠ x := by
        intro w hw h
        subst w
        exact (List.nodup_cons.mp hp.support_nodup).1 hw
      have hq' : q = .inl i ∨ q ∈ (threeSplitTail r hout).support := by
        rw [threeSplitArm_cons_eq i hxa r hp hxt, Walk.support_cons] at hq
        exact List.mem_cons.mp hq
      rcases hq' with h | h
      · exact Or.inl h
      · obtain ⟨w, hwx, hwr, rfl⟩ :=
          threeSplitTail_support_cases r hout h
        exact Or.inr ⟨w, hwx, by simp [hwr], rfl⟩

/-- The three source copies. -/
def threeSplitSources (x : V) : Set (ThreeSplitVertex x) :=
  Set.range Sum.inl

/-- Old vertices belonging to the target set. -/
def threeSplitTargets (x : V) (R : Set V) : Set (ThreeSplitVertex x) :=
  {q | ∃ v : {w : V // w ≠ x}, v.1 ∈ R ∧ q = .inr v}

@[simp] theorem mem_threeSplitSources {x : V} {q : ThreeSplitVertex x} :
    q ∈ threeSplitSources x ↔ ∃ i, q = .inl i := by
  simp [threeSplitSources, eq_comm]

@[simp] theorem mem_threeSplitTargets {x : V} {R : Set V}
    {q : ThreeSplitVertex x} :
    q ∈ threeSplitTargets x R ↔
      ∃ v : {w : V // w ≠ x}, v.1 ∈ R ∧ q = .inr v := by
  rfl

/-- Collapse the three source copies back to the original fan centre. -/
def collapseThreeSplitHom (G : SimpleGraph V) (x : V) :
    threeSplitGraph G x →g G where
  toFun q := match q with
    | .inl _ => x
    | .inr v => v.1
  map_rel' := by
    rintro (i | v) (j | w) h <;> simp only at h ⊢
    · exact h.elim
    · exact h
    · exact h
    · exact h

@[simp] theorem collapseThreeSplitHom_source (G : SimpleGraph V)
    (x : V) (i : Fin 3) : collapseThreeSplitHom G x (.inl i) = x :=
  rfl

@[simp] theorem collapseThreeSplitHom_old (G : SimpleGraph V)
    (x : V) (v : {w : V // w ≠ x}) :
    collapseThreeSplitHom G x (.inr v) = v.1 :=
  rfl

private def otherThreeSource (i : Fin 3) : Fin 3 :=
  if i = 0 then 1 else 0

private theorem otherThreeSource_ne (i : Fin 3) : otherThreeSource i ≠ i := by
  fin_cases i <;> simp [otherThreeSource]

/-! ## Every fan separator has at least two vertices -/

/-- Vertex-two-connectivity rules out a separator of size zero or one
between the three split sources and a target set containing two distinct
old vertices. -/
theorem two_le_ncard_threeSplit_separator
    {x y z : V} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (R : Set V) (hyR : y ∈ R) (hzR : z ∈ R)
    (hconn : G.Connected)
    (hdelete : ∀ d : V, (G.induce fun w : V ↦ w ≠ d).Connected)
    (S : Set (ThreeSplitVertex x))
    (hS : Erdos599.Countable.Separates (threeSplitGraph G x)
      (threeSplitSources x) (threeSplitTargets x R) S) :
    2 ≤ S.ncard := by
  classical
  by_contra hnot
  have hlt : S.ncard < 2 := Nat.lt_of_not_ge hnot
  have hfinite : S.Finite := Set.toFinite S
  have hcases : S = ∅ ∨ ∃ s, S = {s} := by
    have hzero_or_one : S.ncard = 0 ∨ S.ncard = 1 := by omega
    rcases hzero_or_one with hzero | hone
    · exact Or.inl (Set.ncard_eq_zero hfinite |>.mp hzero)
    · exact Or.inr (Set.ncard_eq_one.mp hone)
  have target_mem {t : V} (htx : t ≠ x) (htR : t ∈ R) :
      (.inr ⟨t, htx⟩ : ThreeSplitVertex x) ∈ threeSplitTargets x R := by
    exact ⟨⟨t, htx⟩, htR, rfl⟩
  rcases hcases with rfl | ⟨s, rfl⟩
  · obtain ⟨p, hp⟩ := (hconn x y).exists_isPath
    let q := threeSplitArm (G := G) 0 p hp hxy
    have hq : q.IsPath := threeSplitArm_isPath 0 p hp hxy
    rcases hS (.inl 0) ⟨0, rfl⟩ (.inr ⟨y, hxy.symm⟩)
        (target_mem hxy.symm hyR) q hq with ⟨w, -, hw⟩
    exact hw
  · cases s with
    | inl j =>
        let i := otherThreeSource j
        have hij : i ≠ j := otherThreeSource_ne j
        obtain ⟨p, hp⟩ := (hconn x y).exists_isPath
        let q := threeSplitArm (G := G) i p hp hxy
        have hq : q.IsPath := threeSplitArm_isPath i p hp hxy
        rcases hS (.inl i) ⟨i, rfl⟩ (.inr ⟨y, hxy.symm⟩)
            (target_mem hxy.symm hyR) q hq with ⟨w, hwq, hw⟩
        have hwj : w = .inl j := by simpa using hw
        rcases threeSplitArm_support_cases i p hp hxy hwq with hwi |
            ⟨a, hax, -, hwa⟩
        · exact hij (Sum.inl.inj (hwi.symm.trans hwj))
        · cases hwa.symm.trans hwj
    | inr d =>
        let t : V := if d.1 = y then z else y
        have htx : t ≠ x := by
          simp only [t]
          split
          · exact hxz.symm
          · exact hxy.symm
        have htd : t ≠ d.1 := by
          simp only [t]
          split
          · rename_i hdy
            intro hzd
            exact hyz (hdy.symm.trans hzd.symm)
          · rename_i hdy
            exact fun hyd ↦ hdy hyd.symm
        have htR : t ∈ R := by
          simp only [t]
          split
          · exact hzR
          · exact hyR
        let x' : {w : V // w ≠ d.1} := ⟨x, fun h ↦ d.2 h.symm⟩
        let t' : {w : V // w ≠ d.1} := ⟨t, htd⟩
        obtain ⟨p', hp'⟩ := ((hdelete d.1) x' t').exists_isPath
        let inc := SimpleGraph.Embedding.induce
          (G := G) (s := fun w : V ↦ w ≠ d.1)
        let p : G.Walk x t := p'.map inc.toHom
        have hp : p.IsPath := hp'.map inc.injective
        let q := threeSplitArm (G := G) 0 p hp htx.symm
        have hq : q.IsPath := threeSplitArm_isPath 0 p hp htx.symm
        rcases hS (.inl 0) ⟨0, rfl⟩ (.inr ⟨t, htx⟩)
            (target_mem htx htR) q hq with ⟨w, hwq, hw⟩
        have hwd : w = .inr d := by simpa using hw
        rcases threeSplitArm_support_cases 0 p hp htx.symm hwq with hwi |
            ⟨a, hax, hap, hwa⟩
        · cases hwi.symm.trans hwd
        · have had : a = d.1 := by
            have hs : (⟨a, hax⟩ : {w : V // w ≠ x}) = d :=
              Sum.inr.inj (hwa.symm.trans hwd)
            exact congrArg Subtype.val hs
          have haAvoid : a ≠ d.1 := by
            change a ∈ (p'.map inc.toHom).support at hap
            rw [Walk.support_map] at hap
            obtain ⟨w, -, hwa⟩ := List.mem_map.mp hap
            exact fun h ↦ w.2 (by simpa [inc] using hwa.trans h)
          exact haAvoid had

/-- A two-element separator between the three sources and a target
containing two old vertices cannot spend either of its vertices on a source
copy.  Thus it is exactly the lift of two distinct old vertices. -/
theorem threeSplit_separator_eq_old_pair
    {x y z : V} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (R : Set V) (hyR : y ∈ R) (hzR : z ∈ R)
    (hconn : G.Connected)
    (hdelete : ∀ d : V, (G.induce fun w : V ↦ w ≠ d).Connected)
    (S : Set (ThreeSplitVertex x))
    (hS : Erdos599.Countable.Separates (threeSplitGraph G x)
      (threeSplitSources x) (threeSplitTargets x R) S)
    (hcard : S.ncard = 2) :
    ∃ a b : {w : V // w ≠ x}, a ≠ b ∧ S = {.inr a, .inr b} := by
  classical
  obtain ⟨s, t, hst, rfl⟩ := Set.ncard_eq_two.mp hcard
  have target_mem {q : V} (hqx : q ≠ x) (hqR : q ∈ R) :
      (.inr ⟨q, hqx⟩ : ThreeSplitVertex x) ∈ threeSplitTargets x R :=
    ⟨⟨q, hqx⟩, hqR, rfl⟩
  have old_path_avoiding (d : {w : V // w ≠ x}) :
      ∃ q : V, q ∈ R ∧ q ≠ x ∧ q ≠ d.1 ∧
        ∃ p : G.Walk x q, p.IsPath ∧ d.1 ∉ p.support := by
    let q : V := if d.1 = y then z else y
    have hqR : q ∈ R := by
      simp only [q]
      split
      · exact hzR
      · exact hyR
    have hqx : q ≠ x := by
      simp only [q]
      split
      · exact hxz.symm
      · exact hxy.symm
    have hqd : q ≠ d.1 := by
      simp only [q]
      split
      · rename_i hdy
        intro hzd
        exact hyz (hdy.symm.trans hzd.symm)
      · rename_i hdy
        exact fun hyd ↦ hdy hyd.symm
    let x' : {w : V // w ≠ d.1} := ⟨x, fun h ↦ d.2 h.symm⟩
    let q' : {w : V // w ≠ d.1} := ⟨q, hqd⟩
    obtain ⟨p', hp'⟩ := ((hdelete d.1) x' q').exists_isPath
    let inc := SimpleGraph.Embedding.induce
      (G := G) (s := fun w : V ↦ w ≠ d.1)
    let p : G.Walk x q := p'.map inc.toHom
    have hp : p.IsPath := hp'.map inc.injective
    refine ⟨q, hqR, hqx, hqd, p, hp, ?_⟩
    change d.1 ∉ (p'.map inc.toHom).support
    rw [Walk.support_map]
    intro hd
    obtain ⟨w, -, hw⟩ := List.mem_map.mp hd
    exact w.2 (by simpa [inc] using hw)
  have false_source_source (i j : Fin 3) (hij : i ≠ j)
      (hsep : Erdos599.Countable.Separates (threeSplitGraph G x)
        (threeSplitSources x) (threeSplitTargets x R) {(.inl i), (.inl j)}) :
      False := by
    have hpairCard : ({i, j} : Finset (Fin 3)).card ≤ 2 :=
      Finset.card_insert_le i {j} |>.trans (by simp)
    have hstrict : ({i, j} : Finset (Fin 3)).card < Fintype.card (Fin 3) := by
      simp only [Fintype.card_fin]
      omega
    obtain ⟨k, -, hk⟩ :=
      Finset.exists_mem_notMem_of_card_lt_card hstrict
    have hki : k ≠ i := by intro h; exact hk (by simp [h])
    have hkj : k ≠ j := by intro h; exact hk (by simp [h])
    obtain ⟨p, hp⟩ := (hconn x y).exists_isPath
    let q := threeSplitArm (G := G) k p hp hxy
    have hq : q.IsPath := threeSplitArm_isPath k p hp hxy
    rcases hsep (.inl k) ⟨k, rfl⟩ (.inr ⟨y, hxy.symm⟩)
        (target_mem hxy.symm hyR) q hq with ⟨w, hwq, hw⟩
    have hwcases : w = .inl i ∨ w = .inl j := by simpa using hw
    rcases threeSplitArm_support_cases k p hp hxy hwq with hwk |
        ⟨a, hax, -, hwa⟩
    · rcases hwcases with hwi | hwj
      · exact hki (Sum.inl.inj (hwk.symm.trans hwi))
      · exact hkj (Sum.inl.inj (hwk.symm.trans hwj))
    · rcases hwcases with hwi | hwj
      · cases hwa.symm.trans hwi
      · cases hwa.symm.trans hwj
  have false_source_old (i : Fin 3) (d : {w : V // w ≠ x})
      (hsep : Erdos599.Countable.Separates (threeSplitGraph G x)
        (threeSplitSources x) (threeSplitTargets x R) {(.inl i), (.inr d)}) :
      False := by
    let k := otherThreeSource i
    have hki : k ≠ i := otherThreeSource_ne i
    obtain ⟨q, hqR, hqx, hqd, p, hp, hdP⟩ := old_path_avoiding d
    let w := threeSplitArm (G := G) k p hp hqx.symm
    have hw : w.IsPath := threeSplitArm_isPath k p hp hqx.symm
    rcases hsep (.inl k) ⟨k, rfl⟩ (.inr ⟨q, hqx⟩)
        (target_mem hqx hqR) w hw with ⟨v, hvw, hv⟩
    have hvcases : v = .inl i ∨ v = .inr d := by simpa using hv
    rcases threeSplitArm_support_cases k p hp hqx.symm hvw with hvk |
        ⟨a, hax, haP, hva⟩
    · rcases hvcases with hvi | hvd
      · exact hki (Sum.inl.inj (hvk.symm.trans hvi))
      · cases hvk.symm.trans hvd
    · rcases hvcases with hvi | hvd
      · cases hva.symm.trans hvi
      · have had : a = d.1 := by
          have hs : (⟨a, hax⟩ : {w : V // w ≠ x}) = d :=
            Sum.inr.inj (hva.symm.trans hvd)
          exact congrArg Subtype.val hs
        exact hdP (had ▸ haP)
  cases s with
  | inl i =>
      cases t with
      | inl j =>
          have hij : i ≠ j := fun h ↦ hst (by simp [h])
          exact (false_source_source i j hij hS).elim
      | inr b => exact (false_source_old i b hS).elim
  | inr a =>
      cases t with
      | inl j =>
          have hsep : Erdos599.Countable.Separates (threeSplitGraph G x)
              (threeSplitSources x) (threeSplitTargets x R)
              {(.inl j), (.inr a)} := by
            simpa [Set.pair_comm] using hS
          exact (false_source_old j a hsep).elim
      | inr b =>
          have hab : a ≠ b := by
            intro h
            exact hst (by simp [h])
          exact ⟨a, b, hab, rfl⟩

/-! ## Converting a Menger separator into a cycle separator -/

/-- A two-element separator in the split graph gives the exact
`VertexCycleSeparator` on the original graph. -/
theorem exists_vertexCycleSeparator_of_threeSplit_separator
    {r x : V} (C : G.Walk r r) (hxC : x ∉ C.support)
    (hconn : G.Connected)
    (hdelete : ∀ d : V, (G.induce fun w : V ↦ w ≠ d).Connected)
    (S : Set (ThreeSplitVertex x))
    (hS : Erdos599.Countable.Separates (threeSplitGraph G x)
      (threeSplitSources x)
      (threeSplitTargets x {w | w ∈ C.support}) S)
    (hcard : S.ncard = 2)
    {y z : V} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hyC : y ∈ C.support) (hzC : z ∈ C.support) :
    Nonempty (VertexCycleSeparator C x) := by
  classical
  obtain ⟨a, b, hab, hS_eq⟩ := threeSplit_separator_eq_old_pair
    hxy hxz hyz {w | w ∈ C.support} hyC hzC hconn hdelete S hS hcard
  have hxa : x ≠ a.1 := a.2.symm
  have hxb : x ≠ b.1 := b.2.symm
  have hxNotPair : x ∉ (({a.1, b.1} : Finset V) : Set V) := by
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton,
      not_or]
    exact ⟨hxa, hxb⟩
  let side : G.ComponentCompl
      (({a.1, b.1} : Finset V) : Set V) :=
    G.componentComplMk hxNotPair
  have hxSide : x ∈ (side : Set V) := by
    exact G.componentComplMk_mem hxNotPair
  refine ⟨{
    left := a.1
    right := b.1
    left_ne_right := fun h ↦ hab (Subtype.ext h)
    x_ne_left := hxa
    x_ne_right := hxb
    side := side
    x_mem_side := hxSide
    rim_outside_side := ?_ }⟩
  intro w hwC hwa hwb hwSide
  have hwNotPair : w ∉ (({a.1, b.1} : Finset V) : Set V) := by
    simpa [hwa, hwb]
  have hwEq : G.componentComplMk hwNotPair = side := hwSide.choose_spec
  have hreach : (G.induce
      (((({a.1, b.1} : Finset V) : Set V))ᶜ)).Reachable
      (⟨x, by simp [hxa, hxb]⟩ :
        {q : V // q ∉ (({a.1, b.1} : Finset V) : Set V)})
      ⟨w, hwNotPair⟩ := by
    rw [ConnectedComponent.eq] at hwEq
    exact hwEq.symm
  obtain ⟨p', hp'⟩ := hreach.exists_isPath
  let inc := SimpleGraph.Embedding.induce
    (G := G) (s := ((({a.1, b.1} : Finset V) : Set V))ᶜ)
  let p : G.Walk x w := p'.map inc.toHom
  have hp : p.IsPath := hp'.map inc.injective
  have hxw : x ≠ w := by
    intro h
    exact hxC (h ▸ hwC)
  let q := threeSplitArm (G := G) 0 p hp hxw
  have hq : q.IsPath := threeSplitArm_isPath 0 p hp hxw
  have hwTarget : (.inr ⟨w, hxw.symm⟩ : ThreeSplitVertex x) ∈
      threeSplitTargets x {v | v ∈ C.support} :=
    ⟨⟨w, hxw.symm⟩, hwC, rfl⟩
  rcases hS (.inl 0) ⟨0, rfl⟩ (.inr ⟨w, hxw.symm⟩)
      hwTarget q hq with ⟨v, hvq, hvS⟩
  have hvPair : v = .inr a ∨ v = .inr b := by
    rw [hS_eq] at hvS
    simpa using hvS
  rcases threeSplitArm_support_cases 0 p hp hxw hvq with hv0 |
      ⟨d, hdx, hdp, hvd⟩
  · rcases hvPair with hva | hvb
    · cases hv0.symm.trans hva
    · cases hv0.symm.trans hvb
  · have hdAvoid : d ∉ (({a.1, b.1} : Finset V) : Set V) := by
      change d ∈ (p'.map inc.toHom).support at hdp
      rw [Walk.support_map] at hdp
      obtain ⟨e, -, he⟩ := List.mem_map.mp hdp
      have hed : e.1 = d := by simpa [inc] using he
      exact hed ▸ e.2
    rcases hvPair with hva | hvb
    · have hda : d = a.1 := by
        have hs : (⟨d, hdx⟩ : {q : V // q ≠ x}) = a :=
          Sum.inr.inj (hvd.symm.trans hva)
        exact congrArg Subtype.val hs
      exact hdAvoid (by simp [hda])
    · have hdb : d = b.1 := by
        have hs : (⟨d, hdx⟩ : {q : V // q ≠ x}) = b :=
          Sum.inr.inj (hvd.symm.trans hvb)
        exact congrArg Subtype.val hs
      exact hdAvoid (by simp [hdb])

/-! ## The three-fan alternative -/

/-- Three clean, internally disjoint arms from a cycle to one outside
vertex. -/
structure CleanThreeFanToCycle {r x : V} (C : G.Walk r r) where
  endpoint : Fin 3 → V
  endpoint_injective : Function.Injective endpoint
  endpoint_mem : ∀ i, endpoint i ∈ C.support
  arm : ∀ i, G.Walk (endpoint i) x
  arm_isPath : ∀ i, (arm i).IsPath
  arms_meet_only_x : Pairwise fun i j ↦
    ∀ w, w ∈ (arm i).support → w ∈ (arm j).support → w = x
  arm_meets_cycle_only_start : ∀ i w, w ∈ (arm i).support →
    w ∈ C.support → w = endpoint i

/-- Three disjoint paths from the split sources to a cycle collapse and
truncate to a clean three-fan in the original graph. -/
theorem exists_cleanThreeFanToCycle_of_threeABLinkage
    {r x : V} (C : G.Walk r r) (hxC : x ∉ C.support)
    (L : ThreeABLinkage (threeSplitGraph G x) (threeSplitSources x)
      (threeSplitTargets x {w | w ∈ C.support})) :
    Nonempty (CleanThreeFanToCycle (x := x) C) := by
  classical
  choose source hsource using fun i ↦
    (mem_threeSplitSources.mp (L.left_mem i))
  have hleft (i) : L.left i = .inl (source i) := hsource i
  have hsource_inj : Function.Injective source := by
    intro i j hij
    by_contra hne
    have hd := L.disjoint hne
    have hi : L.left i ∈ (L.path i).support := (L.path i).start_mem_support
    have hj : L.left i ∈ (L.path j).support := by
      have : L.left i = L.left j := by rw [hleft i, hleft j, hij]
      rw [this]
      exact (L.path j).start_mem_support
    exact Set.disjoint_left.mp hd hi hj
  have hsource_surj : Function.Surjective source :=
    (Fintype.bijective_iff_injective_and_card source).mpr
      ⟨hsource_inj, by simp⟩ |>.2
  have source_mem_only (i j : Fin 3)
      (h : (.inl j : ThreeSplitVertex x) ∈ (L.path i).support) :
      (.inl j : ThreeSplitVertex x) = L.left i := by
    obtain ⟨k, hk⟩ := hsource_surj j
    by_cases hki : k = i
    · subst k
      rw [hleft i, hk]
    · have hd := L.disjoint hki
      have hkpath : (.inl j : ThreeSplitVertex x) ∈ (L.path k).support := by
        have : (.inl j : ThreeSplitVertex x) = L.left k := by
          rw [hleft k, hk]
        rw [this]
        exact (L.path k).start_mem_support
      exact False.elim (Set.disjoint_left.mp hd hkpath h)
  choose rawEnd hrawEndC hright using fun i ↦
    (mem_threeSplitTargets.mp (L.right_mem i))
  let raw (i : Fin 3) : G.Walk x (rawEnd i).1 :=
    ((L.path i).map (collapseThreeSplitHom G x)).copy
      (by rw [hleft i]; rfl) (by rw [hright i]; rfl)
  have hrawPath (i : Fin 3) : (raw i).IsPath := by
    rw [Walk.isPath_def]
    simp only [raw, Walk.support_copy, Walk.support_map]
    apply List.Nodup.map_on ?_ (L.isPath i).support_nodup
    intro a ha b hb hab
    cases a with
    | inl ia =>
        cases b with
        | inl ib =>
            have ha' := source_mem_only i ia ha
            have hb' := source_mem_only i ib hb
            exact ha'.trans hb'.symm
        | inr b =>
            exfalso
            exact b.2 (by simpa [collapseThreeSplitHom] using hab.symm)
    | inr a =>
        cases b with
        | inl ib =>
            exfalso
            exact a.2 (by simpa [collapseThreeSplitHom] using hab)
        | inr b =>
            exact congrArg Sum.inr (Subtype.ext (by
              simpa [collapseThreeSplitHom] using hab))
  let target : Finset V := C.support.toFinset
  have hxTarget : x ∉ target := by simpa [target] using hxC
  have hrawEndTarget (i : Fin 3) : (rawEnd i).1 ∈ target := by
    simpa [target] using hrawEndC i
  choose endpoint hendTarget q hqPath hqSub hqFirst using fun i ↦
    exists_initialPath_to_finset_wm target hxTarget (hrawEndTarget i)
      (raw i) (hrawPath i)
  let arm (i : Fin 3) : G.Walk (endpoint i) x := (q i).reverse
  have hendC (i : Fin 3) : endpoint i ∈ C.support := by
    simpa [target] using hendTarget i
  have harmPath (i : Fin 3) : (arm i).IsPath := (hqPath i).reverse
  have hqInRaw (i : Fin 3) {w : V} (hw : w ∈ (q i).support) :
      w ∈ (raw i).support := hqSub i w hw
  have preimage_of_mem_raw (i : Fin 3) {w : V} (hw : w ∈ (raw i).support) :
      ∃ v ∈ (L.path i).support, collapseThreeSplitHom G x v = w := by
    change w ∈ (((L.path i).map (collapseThreeSplitHom G x)).copy _ _).support at hw
    rw [Walk.support_copy, Walk.support_map] at hw
    obtain ⟨v, hv, hvw⟩ := List.mem_map.mp hw
    exact ⟨v, hv, hvw⟩
  have harmsMeet : Pairwise fun i j ↦
      ∀ w, w ∈ (arm i).support → w ∈ (arm j).support → w = x := by
    intro i j hij w hwi hwj
    by_contra hwx
    have hwiq : w ∈ (q i).support := by
      simpa only [arm, Walk.support_reverse, List.mem_reverse] using hwi
    have hwjq : w ∈ (q j).support := by
      simpa only [arm, Walk.support_reverse, List.mem_reverse] using hwj
    obtain ⟨vi, hvi, hviw⟩ := preimage_of_mem_raw i (hqInRaw i hwiq)
    obtain ⟨vj, hvj, hvjw⟩ := preimage_of_mem_raw j (hqInRaw j hwjq)
    have vi_old : ∃ a : {v : V // v ≠ x}, vi = .inr a := by
      cases vi with
      | inl k => exact (hwx (by simpa [collapseThreeSplitHom] using hviw.symm)).elim
      | inr a => exact ⟨a, rfl⟩
    have vj_old : ∃ a : {v : V // v ≠ x}, vj = .inr a := by
      cases vj with
      | inl k => exact (hwx (by simpa [collapseThreeSplitHom] using hvjw.symm)).elim
      | inr a => exact ⟨a, rfl⟩
    obtain ⟨ai, rfl⟩ := vi_old
    obtain ⟨aj, rfl⟩ := vj_old
    have haij : ai = aj := Subtype.ext (by
      simpa [collapseThreeSplitHom] using hviw.trans hvjw.symm)
    exact Set.disjoint_left.mp (L.disjoint hij) hvi (haij ▸ hvj)
  have hendInj : Function.Injective endpoint := by
    intro i j hij
    by_contra hne
    have hi : endpoint i ∈ (arm i).support := (arm i).start_mem_support
    have hj : endpoint i ∈ (arm j).support := by
      rw [hij]
      exact (arm j).start_mem_support
    have hx : endpoint i = x := harmsMeet hne _ hi hj
    exact hxC (hx.symm ▸ hendC i)
  refine ⟨{
    endpoint := endpoint
    endpoint_injective := hendInj
    endpoint_mem := hendC
    arm := arm
    arm_isPath := harmPath
    arms_meet_only_x := harmsMeet
    arm_meets_cycle_only_start := ?_ }⟩
  intro i w hwArm hwC
  have hwq : w ∈ (q i).support := by
    simpa only [arm, Walk.support_reverse, List.mem_reverse] using hwArm
  apply hqFirst i w hwq
  simpa [target] using hwC

/-- Three clean arms from an outside vertex to a simple cycle force a
cycle through that vertex and any two prescribed distinct vertices of the
old cycle.  This is the fan lemma used contrapositively in Watkins--Mesner.
-/
theorem hasCycleThroughThree_of_cleanThreeFanToCycle
    {r x y z : V} {C : G.Walk r r} (hC : C.IsCycle)
    (hxC : x ∉ C.support) (hyC : y ∈ C.support)
    (hzC : z ∈ C.support) (hyz : y ≠ z)
    (F : CleanThreeFanToCycle (x := x) C) :
    HasCycleThroughThree G x y z := by
  classical
  let R : G.Walk y y := C.rotate y hyC
  have hR : R.IsCycle := hC.rotate hyC
  have hRnotNil : ¬R.Nil := hR.not_nil
  let P : G.Walk y R.penultimate := R.dropLast
  let Q : G.Walk y R.penultimate := (R.adj_penultimate hRnotNil).symm.toWalk
  have hP : P.IsPath := hR.isPath_dropLast
  have hQ : Q.IsPath := Walk.IsPath.of_adj _
  have memR_iff (w : V) : w ∈ R.support ↔ w ∈ C.support := by
    constructor
    · intro hw
      have hw' : w ∈ R.toSubgraph.verts := by
        simpa only [Walk.mem_verts_toSubgraph] using hw
      have : w ∈ C.toSubgraph.verts := by
        simpa only [R, Walk.toSubgraph_rotate] using hw'
      simpa only [Walk.mem_verts_toSubgraph] using this
    · intro hw
      have hw' : w ∈ C.toSubgraph.verts := by
        simpa only [Walk.mem_verts_toSubgraph] using hw
      have : w ∈ R.toSubgraph.verts := by
        simpa only [R, Walk.toSubgraph_rotate] using hw'
      simpa only [Walk.mem_verts_toSubgraph] using this
  have memP_of_memC {w : V} (hw : w ∈ C.support) : w ∈ P.support := by
    have hwR : w ∈ R.support := (memR_iff w).mpr hw
    have hsupport := R.support_dropLast_concat hRnotNil
    have hwCases : w ∈ P.support ∨ w = y := by
      rw [← hsupport] at hwR
      simpa only [P, List.mem_append, List.mem_singleton] using hwR
    exact hwCases.elim id (fun h ↦ h ▸ P.start_mem_support)
  have hzP : z ∈ P.support := memP_of_memC hzC
  have hendP (i : Fin 3) : F.endpoint i ∈ P.support :=
    memP_of_memC (F.endpoint_mem i)
  let Left : Fin 3 → Prop := fun i ↦
    F.endpoint i ∈ (P.takeUntil z hzP).support
  have hside (i : Fin 3) : Left i ∨
      F.endpoint i ∈ (P.dropUntil z hzP).support := by
    have : F.endpoint i ∈
        ((P.takeUntil z hzP).append (P.dropUntil z hzP)).support := by
      rw [Walk.take_spec]
      exact hendP i
    simpa only [Left, Walk.mem_support_append_iff] using this
  have hpigeon : ∃ i j : Fin 3, i ≠ j ∧ (Left i ↔ Left j) := by
    by_cases h01 : Left 0 ↔ Left 1
    · exact ⟨0, 1, by decide, h01⟩
    by_cases h02 : Left 0 ↔ Left 2
    · exact ⟨0, 2, by decide, h02⟩
    refine ⟨1, 2, by decide, ?_⟩
    tauto
  obtain ⟨i, j, hij, hsame⟩ := hpigeon
  have hef : F.endpoint i ≠ F.endpoint j :=
    F.endpoint_injective.ne hij
  have hmeetPQ : ∀ w, w ∈ P.support → w ∈ Q.support →
      w = y ∨ w = R.penultimate := by
    intro w _ hwQ
    simpa only [Q, SimpleGraph.Adj.support_toWalk, List.mem_cons,
      List.mem_singleton, List.not_mem_nil, or_false] using hwQ
  have hyQ : y ∈ Q.support := Q.start_mem_support
  have support_inside_cycle {w : V}
      (hw : w ∈ P.support ∨ w ∈ Q.support) : w ∈ C.support := by
    rcases hw with hwP | hwQ
    · apply (memR_iff w).mp
      have : w ∈ (P.concat (R.adj_penultimate hRnotNil)).support := by
        simp only [Walk.support_concat, List.mem_append, List.mem_singleton]
        exact Or.inl hwP
      simpa only [P, R.concat_dropLast] using this
    · have hwCases : w = y ∨ w = R.penultimate := by
        simpa only [Q, SimpleGraph.Adj.support_toWalk, List.mem_cons,
          List.mem_singleton, List.not_mem_nil, or_false] using hwQ
      rcases hwCases with rfl | rfl
      · exact hyC
      · apply (memR_iff R.penultimate).mp
        exact List.mem_of_mem_dropLast
          (R.penultimate_mem_dropLast_support hRnotNil)
  have finish (I : AHTK32Routing.PairInsidePath
      (p := z) (q := y) (e := F.endpoint i) (f := F.endpoint j) P Q) :
      HasCycleThroughThree G x y z := by
    have hxe : x ≠ F.endpoint i := by
      intro h
      exact hxC (h ▸ F.endpoint_mem i)
    have hxf : x ≠ F.endpoint j := by
      intro h
      exact hxC (h ▸ F.endpoint_mem j)
    apply AHTK32Routing.hasCycleThroughThree_of_cleanTwoFan
      (F.arm i) (F.arm j) I.path
      (F.arm_isPath i) (F.arm_isPath j) I.isPath
      hef hxe hxf (F.arms_meet_only_x hij)
    · intro w hwArm hwInside
      apply F.arm_meets_cycle_only_start i w hwArm
      exact support_inside_cycle (I.support_subset w hwInside)
    · intro w hwArm hwInside
      apply F.arm_meets_cycle_only_start j w hwArm
      exact support_inside_cycle (I.support_subset w hwInside)
    · exact I.q_mem
    · exact I.p_mem
  by_cases hi : Left i
  · have hj : Left j := hsame.mp hi
    obtain ⟨I⟩ := AHTK32Routing.exists_pairInsidePath_sameRoute_leftHalf
      P Q hP hQ hzP hyQ hi hj hef hmeetPQ
    exact finish I
  · have hj : ¬Left j := fun h ↦ hi (hsame.mpr h)
    obtain ⟨I⟩ := AHTK32Routing.exists_pairInsidePath_sameRoute_rightHalf
      P Q hP hQ hzP hyQ ((hside i).resolve_left hi)
        ((hside j).resolve_left hj) hef hmeetPQ
    exact finish I

/-- In a vertex-two-connected graph with no common cycle through `x,y,z`,
every cycle through `y,z` and avoiding `x` has a two-vertex separator from
`x`.  This is AHT Lemma 3.5 in the exact form used three times in Theorem
5.1. -/
theorem exists_vertexCycleSeparator_of_no_common_cycle
    {r x y z : V} (C : G.Walk r r) (hC : C.IsCycle)
    (hxC : x ∉ C.support) (hyC : y ∈ C.support)
    (hzC : z ∈ C.support)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hconn : G.Connected)
    (hdelete : ∀ d : V, (G.induce fun w : V ↦ w ≠ d).Connected)
    (hno : ¬HasCycleThroughThree G x y z) :
    Nonempty (VertexCycleSeparator C x) := by
  classical
  let H := threeSplitGraph G x
  let A := threeSplitSources x
  let B := threeSplitTargets x {w | w ∈ C.support}
  by_cases hlarge : ∀ S, Erdos599.Countable.Separates H A B S → 3 ≤ S.ncard
  · obtain ⟨L⟩ : Nonempty (ThreeABLinkage H A B) :=
      exists_threeABLinkage_of_separator_three_le H A B hlarge
    obtain ⟨F⟩ := exists_cleanThreeFanToCycle_of_threeABLinkage C hxC L
    exact (hno (hasCycleThroughThree_of_cleanThreeFanToCycle
      hC hxC hyC hzC hyz F)).elim
  · push_neg at hlarge
    obtain ⟨S, hS, hScard⟩ := hlarge
    have htwo : 2 ≤ S.ncard := two_le_ncard_threeSplit_separator
      hxy hxz hyz {w | w ∈ C.support} hyC hzC hconn hdelete S hS
    have heq : S.ncard = 2 := by omega
    exact exists_vertexCycleSeparator_of_threeSplit_separator
      C hxC hconn hdelete S hS heq hxy hxz hyz hyC hzC

/-- Upgrade a cycle separator to the routed form when two internally
disjoint arms run from two rim vertices to the separated terminal.  The
two separator vertices are reordered, if necessary, so the first lies on
the first arm and the second on the second arm. -/
theorem exists_routedCycleSeparator_of_vertexCycleSeparator
    {a b x r : V} {pA : G.Walk a x} {pB : G.Walk b x}
    {C : G.Walk r r} (hpA : pA.IsPath) (hpB : pB.IsPath)
    (haC : a ∈ C.support) (hbC : b ∈ C.support)
    (harms : ∀ w, w ∈ pA.support → w ∈ pB.support → w = x)
    (S : VertexCycleSeparator C x) :
    ∃ R : RoutedCycleSeparator pA pB C,
      ∀ w, w ∈ (R.side : Set V) ↔ w ∈ (S.side : Set V) := by
  classical
  have arm_hits {s : V} (p : G.Walk s x) (hsC : s ∈ C.support) :
      S.left ∈ p.support ∨ S.right ∈ p.support := by
    by_contra h
    push_neg at h
    have hsLeft : s ≠ S.left := by
      intro hs
      exact h.1 (hs ▸ p.start_mem_support)
    have hsRight : s ≠ S.right := by
      intro hs
      exact h.2 (hs ▸ p.start_mem_support)
    have havoid : ∀ w ∈ p.support,
        w ∈ ((({S.left, S.right} : Finset V) : Set V))ᶜ := by
      intro w hw
      simp only [Set.mem_compl_iff, Finset.mem_coe, Finset.mem_insert,
        Finset.mem_singleton, not_or]
      exact ⟨fun hwL ↦ h.1 (hwL ▸ hw),
        fun hwR ↦ h.2 (hwR ▸ hw)⟩
    let q := p.induce
      ((({S.left, S.right} : Finset V) : Set V))ᶜ havoid
    have hcomp : G.componentComplMk (havoid s p.start_mem_support) =
        G.componentComplMk (havoid x p.end_mem_support) := by
      rw [ConnectedComponent.eq]
      exact q.reachable
    have hxEq : G.componentComplMk (havoid x p.end_mem_support) = S.side :=
      S.x_mem_side.choose_spec
    have hsSide : s ∈ (S.side : Set V) :=
      ⟨havoid s p.start_mem_support, hcomp.trans hxEq⟩
    exact S.rim_outside_side s hsC hsLeft hsRight hsSide
  have hA := arm_hits pA haC
  have hB := arm_hits pB hbC
  have not_same {w : V} (hwA : w ∈ pA.support)
      (hwB : w ∈ pB.support) (hwSep : w = S.left ∨ w = S.right) : False := by
    have hwx : w = x := harms w hwA hwB
    rcases hwSep with rfl | rfl
    · exact S.x_ne_left hwx.symm
    · exact S.x_ne_right hwx.symm
  rcases hA with hAl | hAr <;> rcases hB with hBl | hBr
  · exact (not_same hAl hBl (Or.inl rfl)).elim
  · exact ⟨{
      toVertexCycleSeparator := S
      left_mem_aArm := hAl
      left_ne_terminal := S.x_ne_left.symm
      right_mem_bArm := hBr
      right_ne_terminal := S.x_ne_right.symm }, fun _ ↦ Iff.rfl⟩
  · let side' : G.ComponentCompl
        (({S.right, S.left} : Finset V) : Set V) := by
        apply ComponentCompl.transport
          (C := S.side)
        ext v
        simp [or_comm]
    refine ⟨{
      left := S.right
      right := S.left
      left_ne_right := S.left_ne_right.symm
      x_ne_left := S.x_ne_right
      x_ne_right := S.x_ne_left
      side := side'
      x_mem_side := ?_
      rim_outside_side := ?_
      left_mem_aArm := hAr
      left_ne_terminal := S.x_ne_right.symm
      right_mem_bArm := hBl
      right_ne_terminal := S.x_ne_left.symm }, ?_⟩
    · simpa only [side', ComponentCompl.mem_transport] using S.x_mem_side
    · intro w hwC hwR hwL hwSide
      apply S.rim_outside_side w hwC hwL hwR
      simpa only [side', ComponentCompl.mem_transport] using hwSide
    · intro w
      simp only [side', ComponentCompl.mem_transport]
  · exact (not_same hAr hBr (Or.inr rfl)).elim

/-- The prefix and reversed suffix of a simple path at a displayed vertex
meet only at that vertex. -/
theorem _root_.SimpleGraph.Walk.IsPath.takeUntil_inter_reverse_dropUntil_only
    {W : Type u} [DecidableEq W] {H : SimpleGraph W}
    {a b x : W} {p : H.Walk a b} (hp : p.IsPath)
    (hx : x ∈ p.support) (w : W)
    (hwL : w ∈ (p.takeUntil x hx).support)
    (hwR : w ∈ (p.dropUntil x hx).reverse.support) : w = x := by
  have hwDrop : w ∈ (p.dropUntil x hx).support := by
    simpa only [Walk.support_reverse, List.mem_reverse] using hwR
  by_contra hwx
  have hwTail : w ∈ (p.dropUntil x hx).support.tail := by
    rw [← (p.dropUntil x hx).cons_tail_support] at hwDrop
    exact (List.mem_cons.mp hwDrop).resolve_left hwx
  have hnd : ((p.takeUntil x hx).support ++
      (p.dropUntil x hx).support.tail).Nodup := by
    simpa only [← Walk.support_append, p.take_spec hx]
      using hp.support_nodup
  exact (List.nodup_append.mp hnd).2.2 w hwL w hwTail rfl

/-- The interval between two internal vertices of a simple path is again a
simple path and contains neither end of the ambient path. -/
theorem _root_.SimpleGraph.Walk.IsPath.exists_internal_interval
    {W : Type u} [DecidableEq W] {H : SimpleGraph W}
    {a b w v : W} {p : H.Walk a b} (hp : p.IsPath)
    (hw : w ∈ p.support) (hv : v ∈ p.support)
    (hwa : w ≠ a) (hwb : w ≠ b) (hva : v ≠ a) (hvb : v ≠ b) :
    ∃ q : H.Walk w v, q.IsPath ∧
      (∀ t, t ∈ q.support → t ∈ p.support) ∧
      ∀ t, t ∈ q.support → t ≠ a ∧ t ≠ b := by
  have hvCases : v ∈ (p.takeUntil w hw).support ∨
      v ∈ (p.dropUntil w hw).support := by
    have : v ∈ ((p.takeUntil w hw).append (p.dropUntil w hw)).support := by
      rw [p.take_spec hw]
      exact hv
    simpa only [Walk.mem_support_append_iff] using this
  rcases hvCases with hvL | hvR
  · let r := (p.takeUntil w hw).dropUntil v hvL
    let q : H.Walk w v := r.reverse
    refine ⟨q, (hp.takeUntil hw).dropUntil hvL |>.reverse, ?_, ?_⟩
    · intro t ht
      have htr : t ∈ r.support := by
        simpa only [q, Walk.support_reverse, List.mem_reverse] using ht
      exact p.support_takeUntil_subset_support hw
        ((p.takeUntil w hw).support_dropUntil_subset_support hvL htr)
    · intro t ht
      have htr : t ∈ r.support := by
        simpa only [q, Walk.support_reverse, List.mem_reverse] using ht
      have htTake : t ∈ (p.takeUntil w hw).support :=
        (p.takeUntil w hw).support_dropUntil_subset_support hvL htr
      constructor
      · intro hta
        have haTakeV : a ∈
            ((p.takeUntil w hw).takeUntil v hvL).support :=
          ((p.takeUntil w hw).takeUntil v hvL).start_mem_support
        have haRevDrop : a ∈
            ((p.takeUntil w hw).dropUntil v hvL).reverse.support := by
          simpa only [Walk.support_reverse, List.mem_reverse, hta] using htr
        have hav := Walk.IsPath.takeUntil_inter_reverse_dropUntil_only
          (hp.takeUntil hw) hvL a haTakeV haRevDrop
        exact hva hav.symm
      · exact fun htb ↦
          (Walk.endpoint_notMem_support_takeUntil hp hw hwb.symm) (htb ▸ htTake)
  · let r := p.dropUntil w hw
    let q : H.Walk w v := r.takeUntil v hvR
    refine ⟨q, (hp.dropUntil hw).takeUntil hvR, ?_, ?_⟩
    · intro t ht
      exact p.support_dropUntil_subset_support hw
        (r.support_takeUntil_subset_support hvR (by simpa only [q] using ht))
    · intro t ht
      have htR : t ∈ r.support :=
        r.support_takeUntil_subset_support hvR (by simpa only [q] using ht)
      constructor
      · intro hta
        have haTake : a ∈ (p.takeUntil w hw).support :=
          (p.takeUntil w hw).start_mem_support
        have haRev : a ∈ (p.dropUntil w hw).reverse.support := by
          simpa only [Walk.support_reverse, List.mem_reverse, hta] using htR
        have haw := Walk.IsPath.takeUntil_inter_reverse_dropUntil_only
          hp hw a haTake haRev
        exact hwa haw.symm
      · exact fun htb ↦
          (Walk.endpoint_notMem_support_takeUntil
            (hp.dropUntil hw) hvR hvb.symm) (by
              have htq : t ∈ q.support := ht
              have hbq : b ∈ q.support := by
                simpa only [htb] using htq
              simpa only [q, r] using hbq)

/-- Two noninitial vertices of a simple path are joined along that path
without using its initial vertex. -/
theorem _root_.SimpleGraph.Walk.IsPath.exists_subpath_avoiding_start
    {a b x y : V} (p : G.Walk a b) (hp : p.IsPath)
    (hx : x ∈ p.support) (hy : y ∈ p.support)
    (hxa : x ≠ a) (hya : y ≠ a) :
    ∃ q : G.Walk x y, q.IsPath ∧
      (∀ v, v ∈ q.support → v ∈ p.support) ∧
      ∀ v, v ∈ q.support → v ≠ a := by
  have hxSplit : x ∈ (p.takeUntil y hy).support ∨
      x ∈ (p.dropUntil y hy).support := by
    have hxWhole : x ∈ ((p.takeUntil y hy).append
        (p.dropUntil y hy)).support := by
      rw [p.take_spec hy]
      exact hx
    simpa only [Walk.mem_support_append_iff] using hxWhole
  by_cases hxTake : x ∈ (p.takeUntil y hy).support
  · let q : G.Walk x y := (p.takeUntil y hy).dropUntil x hxTake
    refine ⟨q, (hp.takeUntil hy).dropUntil hxTake, ?_, ?_⟩
    · intro v hv
      apply p.support_takeUntil_subset_support hy
      apply (p.takeUntil y hy).support_dropUntil_subset_support hxTake
      simpa only [q] using hv
    · intro v hv hva
      subst v
      have haRev : a ∈
          ((p.takeUntil y hy).dropUntil x hxTake).reverse.support := by
        simpa only [Walk.support_reverse, List.mem_reverse, q] using hv
      have hax := Walk.IsPath.takeUntil_inter_reverse_dropUntil_only
        (hp.takeUntil hy) hxTake a
        ((p.takeUntil y hy).takeUntil x hxTake).start_mem_support haRev
      exact hxa hax.symm
  · have hxDrop : x ∈ (p.dropUntil y hy).support :=
      hxSplit.resolve_left hxTake
    let q : G.Walk x y :=
      ((p.dropUntil y hy).takeUntil x hxDrop).reverse
    refine ⟨q, ((hp.dropUntil hy).takeUntil hxDrop).reverse, ?_, ?_⟩
    · intro v hv
      have hvTake : v ∈
          ((p.dropUntil y hy).takeUntil x hxDrop).support := by
        simpa only [q, Walk.support_reverse, List.mem_reverse] using hv
      apply p.support_dropUntil_subset_support hy
      exact (p.dropUntil y hy).support_takeUntil_subset_support hxDrop hvTake
    · intro v hv hva
      subst v
      have haTake : a ∈
          ((p.dropUntil y hy).takeUntil x hxDrop).support := by
        simpa only [q, Walk.support_reverse, List.mem_reverse] using hv
      have haDrop : a ∈ (p.dropUntil y hy).support :=
        (p.dropUntil y hy).support_takeUntil_subset_support hxDrop haTake
      have haRev : a ∈ (p.dropUntil y hy).reverse.support := by
        simpa only [Walk.support_reverse, List.mem_reverse] using haDrop
      have hay := Walk.IsPath.takeUntil_inter_reverse_dropUntil_only
        hp hy a (p.takeUntil y hy).start_mem_support haRev
      exact hya hay.symm

/-- On a simple path, taking up to its terminal vertex returns the whole
path. -/
theorem _root_.SimpleGraph.Walk.IsPath.takeUntil_end
    {a b : V} (p : G.Walk a b) (hp : p.IsPath) :
    p.takeUntil b p.end_mem_support = p := by
  have hdrop : p.dropUntil b p.end_mem_support = (.nil : G.Walk b b) :=
    Walk.isPath_iff_eq_nil.mp (hp.dropUntil p.end_mem_support)
  have hspec := p.take_spec p.end_mem_support
  rw [hdrop] at hspec
  simpa using hspec

/-- Splitting an appended simple prefix at its terminal vertex leaves the
second walk. -/
theorem _root_.SimpleGraph.Walk.IsPath.dropUntil_append_join
    {a b c : V} (p : G.Walk a b) (q : G.Walk b c)
    (hp : p.IsPath) :
    (p.append q).dropUntil b
      (Walk.support_subset_support_append_left p q p.end_mem_support) = q := by
  let hb : b ∈ (p.append q).support :=
    Walk.support_subset_support_append_left p q p.end_mem_support
  have htake : (p.append q).takeUntil b hb = p := by
    rw [Walk.takeUntil_append_of_mem_left p q p.end_mem_support]
    exact Walk.IsPath.takeUntil_end p hp
  have hspec := (p.append q).take_spec hb
  rw [htake] at hspec
  apply Walk.support_injective
  have hsupp := congrArg Walk.support hspec
  simp only [Walk.support_append] at hsupp
  have htail : ((p.append q).dropUntil b hb).support.tail =
      q.support.tail := List.append_cancel_left hsupp
  rw [← ((p.append q).dropUntil b hb).cons_tail_support,
    ← q.cons_tail_support, htail]

/-- Reverse a path around a displayed internal vertex, keeping the two
halves syntactically visible. -/
def _root_.SimpleGraph.Walk.reverseSplit {a b t : V} (p : G.Walk a b)
    (ht : t ∈ p.support) : G.Walk b a :=
  (p.dropUntil t ht).reverse.append (p.takeUntil t ht).reverse

theorem _root_.SimpleGraph.Walk.IsPath.reverseSplit
    {a b t : V} (p : G.Walk a b) (hp : p.IsPath)
    (ht : t ∈ p.support) : (p.reverseSplit ht).IsPath := by
  have hinter : ∀ w,
      w ∈ (p.dropUntil t ht).reverse.support →
      w ∈ (p.takeUntil t ht).reverse.support → w = t := by
    intro w hwDrop hwTake
    have hwTake' : w ∈ (p.takeUntil t ht).support := by
      simpa only [Walk.support_reverse, List.mem_reverse] using hwTake
    exact Walk.IsPath.takeUntil_inter_reverse_dropUntil_only
      hp ht w hwTake' hwDrop
  rw [Walk.reverseSplit, Walk.isPath_def, Walk.support_append,
    List.nodup_append]
  refine ⟨(hp.dropUntil ht).reverse.support_nodup,
    (hp.takeUntil ht).reverse.support_nodup.tail, ?_⟩
  intro w hwLeft v hvRight hwv
  subst v
  have hwt : w = t := hinter w hwLeft (List.mem_of_mem_tail hvRight)
  subst w
  have hnd := (hp.takeUntil ht).reverse.support_nodup
  rw [← (p.takeUntil t ht).reverse.cons_tail_support] at hnd
  exact (List.nodup_cons.mp hnd).1 hvRight

theorem _root_.SimpleGraph.Walk.mem_reverseSplit_terminal
    {a b t : V} (p : G.Walk a b) (ht : t ∈ p.support) :
    t ∈ (p.reverseSplit ht).support := by
  simp only [Walk.reverseSplit, Walk.mem_support_append_iff]
  exact Or.inl (by
    simpa only [Walk.support_reverse, List.mem_reverse] using
      (p.dropUntil t ht).start_mem_support)

theorem _root_.SimpleGraph.Walk.IsPath.reverseSplit_armA
    {a b t : V} (p : G.Walk a b) (hp : p.IsPath)
    (ht : t ∈ p.support) :
    (p.reverseSplit ht).takeUntil t (p.mem_reverseSplit_terminal ht) =
      (p.dropUntil t ht).reverse := by
  have htake := Walk.takeUntil_append_of_mem_left
    (p.dropUntil t ht).reverse (p.takeUntil t ht).reverse
      (p.dropUntil t ht).reverse.end_mem_support
  rw [Walk.IsPath.takeUntil_end _ (hp.dropUntil ht).reverse] at htake
  simpa only [Walk.reverseSplit] using htake

theorem _root_.SimpleGraph.Walk.IsPath.reverseSplit_armB
    {a b t : V} (p : G.Walk a b) (hp : p.IsPath)
    (ht : t ∈ p.support) :
    ((p.reverseSplit ht).dropUntil t
      (p.mem_reverseSplit_terminal ht)).reverse = p.takeUntil t ht := by
  have hdrop := Walk.IsPath.dropUntil_append_join
    (p.dropUntil t ht).reverse (p.takeUntil t ht).reverse
      (hp.dropUntil ht).reverse
  simpa only [Walk.reverseSplit, Walk.reverse_reverse] using
    congrArg Walk.reverse hdrop

theorem _root_.SimpleGraph.Walk.reverseSplit_support_subset
    {a b t w : V} (p : G.Walk a b) (ht : t ∈ p.support)
    (hw : w ∈ (p.reverseSplit ht).support) : w ∈ p.support := by
  simp only [Walk.reverseSplit, Walk.mem_support_append_iff,
    Walk.support_reverse, List.mem_reverse] at hw
  rcases hw with hwDrop | hwTake
  · exact p.support_dropUntil_subset_support ht hwDrop
  · exact p.support_takeUntil_subset_support ht hwTake

theorem _root_.SimpleGraph.Walk.support_subset_reverseSplit
    {a b t w : V} (p : G.Walk a b) (ht : t ∈ p.support)
    (hw : w ∈ p.support) : w ∈ (p.reverseSplit ht).support := by
  have hwSplit : w ∈ (p.takeUntil t ht).support ∨
      w ∈ (p.dropUntil t ht).support := by
    have : w ∈ ((p.takeUntil t ht).append
        (p.dropUntil t ht)).support := by
      rw [p.take_spec ht]
      exact hw
    simpa only [Walk.mem_support_append_iff] using this
  simp only [Walk.reverseSplit, Walk.mem_support_append_iff,
    Walk.support_reverse, List.mem_reverse]
  exact hwSplit.elim Or.inr Or.inl

theorem _root_.SimpleGraph.Walk.mem_reverseSplit_support_iff
    {a b t w : V} (p : G.Walk a b) (ht : t ∈ p.support) :
    w ∈ (p.reverseSplit ht).support ↔ w ∈ p.support :=
  ⟨p.reverseSplit_support_subset ht, p.support_subset_reverseSplit ht⟩

/-! ## Clean path splices

The last two contradictions in AHT Theorem 5.1 are both eight-piece
cycles.  Keeping the list arithmetic here avoids repeating it in each of
the matching cases. -/

/-- Two paths meeting only at their common endpoint concatenate to a
path. -/
private theorem _root_.SimpleGraph.Walk.IsPath.append_of_meet_only_endpoint_wm
    {a b c : V} {p : G.Walk a b} {q : G.Walk b c}
    (hp : p.IsPath) (hq : q.IsPath)
    (hinter : ∀ w, w ∈ p.support → w ∈ q.support → w = b) :
    (p.append q).IsPath := by
  rw [Walk.isPath_def, Walk.support_append, List.nodup_append]
  refine ⟨hp.support_nodup, hq.support_nodup.tail, ?_⟩
  intro w hwp v hvq hwv
  subst v
  have hwb : w = b := hinter w hwp (List.mem_of_mem_tail hvq)
  subst w
  have hqN := hq.support_nodup
  rw [← q.cons_tail_support] at hqN
  exact (List.nodup_cons.mp hqN).1 hvq

/-- The canonical path through the separated terminal, from the separator
vertex on the first arm to the separator vertex on the second arm. -/
def RoutedCycleSeparator.terminalBridge
    {a b x r : V} {pA : G.Walk a x} {pB : G.Walk b x}
    {C : G.Walk r r} (S : RoutedCycleSeparator pA pB C) :
    G.Walk S.left S.right :=
  (pA.dropUntil S.left S.left_mem_aArm).append
    (pB.dropUntil S.right S.right_mem_bArm).reverse

theorem RoutedCycleSeparator.terminalBridge_isPath
    {a b x r : V} {pA : G.Walk a x} {pB : G.Walk b x}
    {C : G.Walk r r} (S : RoutedCycleSeparator pA pB C)
    (hpA : pA.IsPath) (hpB : pB.IsPath)
    (harms : ∀ w, w ∈ pA.support → w ∈ pB.support → w = x) :
    S.terminalBridge.IsPath := by
  apply (hpA.dropUntil S.left_mem_aArm).append_of_meet_only_endpoint_wm
    (hpB.dropUntil S.right_mem_bArm).reverse
  intro w hwA hwB
  apply harms w
  · exact pA.support_dropUntil_subset_support S.left_mem_aArm hwA
  · apply pB.support_dropUntil_subset_support S.right_mem_bArm
    simpa only [Walk.support_reverse, List.mem_reverse] using hwB

@[simp] theorem RoutedCycleSeparator.left_mem_terminalBridge
    {a b x r : V} {pA : G.Walk a x} {pB : G.Walk b x}
    {C : G.Walk r r} (S : RoutedCycleSeparator pA pB C) :
    S.left ∈ S.terminalBridge.support := by
  simp [RoutedCycleSeparator.terminalBridge]

@[simp] theorem RoutedCycleSeparator.right_mem_terminalBridge
    {a b x r : V} {pA : G.Walk a x} {pB : G.Walk b x}
    {C : G.Walk r r} (S : RoutedCycleSeparator pA pB C) :
    S.right ∈ S.terminalBridge.support := by
  simp [RoutedCycleSeparator.terminalBridge]

@[simp] theorem RoutedCycleSeparator.terminal_mem_terminalBridge
    {a b x r : V} {pA : G.Walk a x} {pB : G.Walk b x}
    {C : G.Walk r r} (S : RoutedCycleSeparator pA pB C) :
    x ∈ S.terminalBridge.support := by
  simp [RoutedCycleSeparator.terminalBridge]

/-- Every vertex of the first arm after its separator vertex lies in the
terminal-side component (apart from the separator vertex itself). -/
theorem RoutedCycleSeparator.mem_side_of_mem_aSuffix
    {a b x r w : V} {pA : G.Walk a x} {pB : G.Walk b x}
    {C : G.Walk r r} (S : RoutedCycleSeparator pA pB C)
    (hpA : pA.IsPath)
    (harms : ∀ v, v ∈ pA.support → v ∈ pB.support → v = x)
    (hw : w ∈ (pA.dropUntil S.left S.left_mem_aArm).support)
    (hwl : w ≠ S.left) : w ∈ (S.side : Set V) := by
  classical
  let q := pA.dropUntil S.left S.left_mem_aArm
  have hqPath : q.IsPath := hpA.dropUntil S.left_mem_aArm
  have hwq : w ∈ q.support := hw
  have hwrev : w ∈ q.reverse.support := by
    simpa only [Walk.support_reverse, List.mem_reverse] using hwq
  let s := q.reverse.takeUntil w hwrev
  have hleft : S.left ∉ s.support := by
    exact Walk.endpoint_notMem_support_takeUntil hqPath.reverse hwrev hwl.symm
  have hrightA : S.right ∉ pA.support := by
    intro hrA
    exact S.right_ne_terminal (harms S.right hrA S.right_mem_bArm)
  have havoid : ∀ v ∈ s.support,
      v ∈ ((({S.left, S.right} : Finset V) : Set V))ᶜ := by
    intro v hv
    simp only [Set.mem_compl_iff, Finset.mem_coe, Finset.mem_insert,
      Finset.mem_singleton, not_or]
    constructor
    · exact fun h ↦ hleft (h ▸ hv)
    · intro h
      have hvqrev : v ∈ q.reverse.support :=
        q.reverse.support_takeUntil_subset_support hwrev hv
      have hvq : v ∈ q.support := by
        simpa only [Walk.support_reverse, List.mem_reverse] using hvqrev
      have hrq : S.right ∈ q.support := by
        rwa [h] at hvq
      exact hrightA
        (pA.support_dropUntil_subset_support S.left_mem_aArm hrq)
  have hcomp :
      G.componentComplMk (havoid x s.start_mem_support) =
        G.componentComplMk (havoid w s.end_mem_support) := by
    rw [ConnectedComponent.eq]
    exact (s.induce _ havoid).reachable
  have hxEq : G.componentComplMk (havoid x s.start_mem_support) = S.side :=
    S.x_mem_side.choose_spec
  exact ⟨havoid w s.end_mem_support, hcomp.symm.trans hxEq⟩

/-- Symmetric terminal-side membership for the second arm suffix. -/
theorem RoutedCycleSeparator.mem_side_of_mem_bSuffix
    {a b x r w : V} {pA : G.Walk a x} {pB : G.Walk b x}
    {C : G.Walk r r} (S : RoutedCycleSeparator pA pB C)
    (hpB : pB.IsPath)
    (harms : ∀ v, v ∈ pA.support → v ∈ pB.support → v = x)
    (hw : w ∈ (pB.dropUntil S.right S.right_mem_bArm).support)
    (hwr : w ≠ S.right) : w ∈ (S.side : Set V) := by
  classical
  let q := pB.dropUntil S.right S.right_mem_bArm
  have hqPath : q.IsPath := hpB.dropUntil S.right_mem_bArm
  have hwrev : w ∈ q.reverse.support := by
    simpa only [Walk.support_reverse, List.mem_reverse] using hw
  let s := q.reverse.takeUntil w hwrev
  have hright : S.right ∉ s.support := by
    exact Walk.endpoint_notMem_support_takeUntil hqPath.reverse hwrev hwr.symm
  have hleftB : S.left ∉ pB.support := by
    intro hlB
    exact S.left_ne_terminal (harms S.left S.left_mem_aArm hlB)
  have havoid : ∀ v ∈ s.support,
      v ∈ ((({S.left, S.right} : Finset V) : Set V))ᶜ := by
    intro v hv
    simp only [Set.mem_compl_iff, Finset.mem_coe, Finset.mem_insert,
      Finset.mem_singleton, not_or]
    constructor
    · intro h
      have hvqrev : v ∈ q.reverse.support :=
        q.reverse.support_takeUntil_subset_support hwrev hv
      have hvq : v ∈ q.support := by
        simpa only [Walk.support_reverse, List.mem_reverse] using hvqrev
      have hlq : S.left ∈ q.support := by
        rwa [h] at hvq
      exact hleftB
        (pB.support_dropUntil_subset_support S.right_mem_bArm hlq)
    · exact fun h ↦ hright (h ▸ hv)
  have hcomp :
      G.componentComplMk (havoid x s.start_mem_support) =
        G.componentComplMk (havoid w s.end_mem_support) := by
    rw [ConnectedComponent.eq]
    exact (s.induce _ havoid).reachable
  have hxEq : G.componentComplMk (havoid x s.start_mem_support) = S.side :=
    S.x_mem_side.choose_spec
  exact ⟨havoid w s.end_mem_support, hcomp.symm.trans hxEq⟩

/-- If a routed separator uses the two branch ends of one displayed route,
then every nonboundary vertex of that route belongs to its terminal side. -/
theorem RoutedCycleSeparator.mem_side_of_route_of_eq_branches
    {A B t r : V} {P : G.Walk A B} (ht : t ∈ P.support)
    {C : G.Walk r r}
    (S : RoutedCycleSeparator (P.takeUntil t ht)
      (P.dropUntil t ht).reverse C)
    (hP : P.IsPath) (hleft : S.left = A) (hright : S.right = B)
    {w : V} (hwP : w ∈ P.support)
    (hwleft : w ≠ S.left) (hwright : w ≠ S.right) :
    w ∈ (S.side : Set V) := by
  have harms : ∀ v,
      v ∈ (P.takeUntil t ht).support →
      v ∈ (P.dropUntil t ht).reverse.support → v = t := by
    intro v hvA hvB
    exact Walk.IsPath.takeUntil_inter_reverse_dropUntil_only
      hP ht v hvA hvB
  have hsplit :
      w ∈ (P.takeUntil t ht).support ∨
      w ∈ (P.dropUntil t ht).support := by
    have hw : w ∈ ((P.takeUntil t ht).append
        (P.dropUntil t ht)).support := by
      rw [P.take_spec ht]
      exact hwP
    simpa only [Walk.mem_support_append_iff] using hw
  rcases hsplit with hwA | hwB
  · apply S.mem_side_of_mem_aSuffix (hP.takeUntil ht) harms
    · have hmem {l : V} (hl : l = A)
          (hlp : l ∈ (P.takeUntil t ht).support) :
          w ∈ ((P.takeUntil t ht).dropUntil l hlp).support := by
        subst l
        simpa only [Walk.dropUntil_first] using hwA
      exact hmem hleft S.left_mem_aArm
    · exact hwleft
  · apply S.mem_side_of_mem_bSuffix (hP.dropUntil ht).reverse harms
    · have hmem {r : V} (hr : r = B)
          (hrp : r ∈ (P.dropUntil t ht).reverse.support) :
          w ∈ ((P.dropUntil t ht).reverse.dropUntil r hrp).support := by
        subst r
        simpa only [Walk.dropUntil_first, Walk.support_reverse,
          List.mem_reverse] using hwB
      exact hmem hright S.right_mem_bArm
    · exact hwright

/-- The canonical bridge has no vertices outside its terminal component
except its two named attachments. -/
theorem RoutedCycleSeparator.terminalBridge_support
    {a b x r w : V} {pA : G.Walk a x} {pB : G.Walk b x}
    {C : G.Walk r r} (S : RoutedCycleSeparator pA pB C)
    (hpA : pA.IsPath) (hpB : pB.IsPath)
    (harms : ∀ v, v ∈ pA.support → v ∈ pB.support → v = x)
    (hw : w ∈ S.terminalBridge.support) :
    w = S.left ∨ w = S.right ∨ w ∈ (S.side : Set V) := by
  have hcases :
      w ∈ (pA.dropUntil S.left S.left_mem_aArm).support ∨
      w ∈ (pB.dropUntil S.right S.right_mem_bArm).reverse.support := by
    simpa only [RoutedCycleSeparator.terminalBridge,
      Walk.mem_support_append_iff] using hw
  rcases hcases with hwA | hwB
  · by_cases hwl : w = S.left
    · exact Or.inl hwl
    · exact Or.inr (Or.inr (S.mem_side_of_mem_aSuffix hpA harms hwA hwl))
  · have hwB' : w ∈ (pB.dropUntil S.right S.right_mem_bArm).support := by
      simpa only [Walk.support_reverse, List.mem_reverse] using hwB
    by_cases hwr : w = S.right
    · exact Or.inr (Or.inl hwr)
    · exact Or.inr (Or.inr (S.mem_side_of_mem_bSuffix hpB harms hwB' hwr))

/-- A cycle through three named vertices obtained from two clean arcs with
the same ends. -/
theorem hasCycleThroughThree_of_two_clean_arcs
    {s t w x y z : V} (p q : G.Walk s t)
    (hp : p.IsPath) (hq : q.IsPath)
    (hw : w ∈ p.support) (hws : w ≠ s) (hwt : w ≠ t)
    (hmeet : ∀ v, v ∈ p.support → v ∈ q.support →
      v = s ∨ v = t)
    (hx : x ∈ p.support ∨ x ∈ q.support)
    (hy : y ∈ p.support ∨ y ∈ q.support)
    (hz : z ∈ p.support ∨ z ∈ q.support) :
    HasCycleThroughThree G x y z := by
  let C : G.Walk s s := p.append q.reverse
  have hC : C.IsCycle := by
    dsimp only [C]
    exact Walk.IsPath.isCycle_append_reverse_of_meet_only_ends
      hp hq hw hws hwt hmeet
  refine ⟨s, C, hC, ?_, ?_, ?_⟩
  · simpa only [C, Walk.mem_support_append_iff,
      Walk.support_reverse, List.mem_reverse] using hx
  · simpa only [C, Walk.mem_support_append_iff,
      Walk.support_reverse, List.mem_reverse] using hy
  · simpa only [C, Walk.mem_support_append_iff,
      Walk.support_reverse, List.mem_reverse] using hz

/-- Let `D` be a component after deleting two vertices of a simple cycle.
If one open arc of the cycle meets `D`, while `y` and `z` lie on the cycle
outside `D`, then the other open arc contains both `y` and `z`.  A path
between the deleted vertices through `x ∈ D` is internally contained in
`D`, so it and that complementary arc form a cycle through `x,y,z`. -/
theorem hasCycleThroughThree_of_cycle_component_split
    {a b x y z r c : V} (C : G.Walk c c) (hC : C.IsCycle)
    (haC : a ∈ C.support) (hbC : b ∈ C.support) (hab : a ≠ b)
    (hrC : r ∈ C.support) (hyC : y ∈ C.support)
    (hzC : z ∈ C.support)
    (hya : y ≠ a) (hyb : y ≠ b)
    (hza : z ≠ a) (hzb : z ≠ b)
    (D : G.ComponentCompl
      ((({a, b} : Finset V) : Set V)))
    (hxD : x ∈ (D : Set V)) (hrD : r ∈ (D : Set V))
    (hyD : y ∉ (D : Set V)) (hzD : z ∉ (D : Set V))
    (hconn : G.Connected)
    (hdelete : ∀ d : V, (G.induce fun w : V ↦ w ≠ d).Connected) :
    HasCycleThroughThree G x y z := by
  classical
  have hxEnds : x ≠ a ∧ x ≠ b := by
    simpa only [Finset.mem_coe, Finset.mem_insert,
      Finset.mem_singleton, not_or] using hxD.1
  have hrEnds : r ≠ a ∧ r ≠ b := by
    simpa only [Finset.mem_coe, Finset.mem_insert,
      Finset.mem_singleton, not_or] using hrD.1
  obtain ⟨P, hP, hxP⟩ := exists_path_between_through hab
    hxEnds.1.symm hxEnds.2.symm hconn hdelete
  obtain ⟨A⟩ := exists_cycleArcPair hC haC hbC hab
  have finish (R Q : G.Walk a b) (hR : R.IsPath) (hQ : Q.IsPath)
      (hRsub : ∀ w, w ∈ R.support → w ∈ C.support)
      (hQsub : ∀ w, w ∈ Q.support → w ∈ C.support)
      (hcover : ∀ w, w ∈ C.support →
        w ∈ R.support ∨ w ∈ Q.support)
      (hmeetRQ : ∀ w, w ∈ R.support → w ∈ Q.support →
        w = a ∨ w = b)
      (hrR : r ∈ R.support) : HasCycleThroughThree G x y z := by
    have internal_R_mem_D {w : V} (hwR : w ∈ R.support)
        (hwa : w ≠ a) (hwb : w ≠ b) : w ∈ (D : Set V) := by
      obtain ⟨q, -, -, hqAvoid⟩ := hR.exists_internal_interval
        hrR hwR hrEnds.1 hrEnds.2 hwa hwb
      apply ComponentCompl.walk_end_mem D q hrD
      intro v hv
      have hvEnds := hqAvoid v hv
      simpa only [Finset.mem_coe, Finset.mem_insert,
        Finset.mem_singleton, not_or] using hvEnds
    have hyR : y ∉ R.support := by
      intro hyR
      exact hyD (internal_R_mem_D hyR hya hyb)
    have hzR : z ∉ R.support := by
      intro hzR
      exact hzD (internal_R_mem_D hzR hza hzb)
    have hyQ : y ∈ Q.support :=
      (hcover y hyC).resolve_left hyR
    have hzQ : z ∈ Q.support :=
      (hcover z hzC).resolve_left hzR
    have internal_P_mem_D {w : V} (hwP : w ∈ P.support)
        (hwa : w ≠ a) (hwb : w ≠ b) : w ∈ (D : Set V) := by
      obtain ⟨q, -, -, hqAvoid⟩ := hP.exists_internal_interval
        hxP hwP hxEnds.1 hxEnds.2 hwa hwb
      apply ComponentCompl.walk_end_mem D q hxD
      intro v hv
      have hvEnds := hqAvoid v hv
      simpa only [Finset.mem_coe, Finset.mem_insert,
        Finset.mem_singleton, not_or] using hvEnds
    have internal_Q_not_mem_D {w : V} (hwQ : w ∈ Q.support)
        (hwa : w ≠ a) (hwb : w ≠ b) : w ∉ (D : Set V) := by
      intro hwD
      obtain ⟨q, -, -, hqAvoid⟩ := hQ.exists_internal_interval
        hyQ hwQ hya hyb hwa hwb
      apply hyD
      apply ComponentCompl.walk_end_mem D q.reverse hwD
      intro v hv
      have hvq : v ∈ q.support := by
        simpa only [Walk.support_reverse, List.mem_reverse] using hv
      have hvEnds := hqAvoid v hvq
      simpa only [Finset.mem_coe, Finset.mem_insert,
        Finset.mem_singleton, not_or] using hvEnds
    have hmeetPQ : ∀ w, w ∈ P.support → w ∈ Q.support →
        w = a ∨ w = b := by
      intro w hwP hwQ
      by_cases hwa : w = a
      · exact Or.inl hwa
      by_cases hwb : w = b
      · exact Or.inr hwb
      exact (internal_Q_not_mem_D hwQ hwa hwb
        (internal_P_mem_D hwP hwa hwb)).elim
    exact hasCycleThroughThree_of_two_clean_arcs P Q hP hQ hxP
      hxEnds.1 hxEnds.2 hmeetPQ (Or.inl hxP)
      (Or.inr hyQ) (Or.inr hzQ)
  rcases A.cover r hrC with hrFirst | hrSecond
  · exact finish A.first A.second A.first_isPath A.second_isPath
      A.first_subset A.second_subset A.cover A.meet_only_ends hrFirst
  · exact finish A.second A.first A.second_isPath A.first_isPath
      A.second_subset A.first_subset
      (fun w hw ↦ (A.cover w hw).symm)
      (fun w hwS hwF ↦ A.meet_only_ends w hwF hwS) hrSecond

/-- Convenience wrapper for the four-by-four path splices on AHT
pp. 15--16.  Each new constituent is required to meet its assembled prefix
only at the joining endpoint, and the two completed arcs meet only at their
common ends. -/
theorem hasCycleThroughThree_of_four_by_four_splice
    {s a₁ a₂ a₃ t b₁ b₂ b₃ x y z : V}
    (p₀ : G.Walk s a₁) (p₁ : G.Walk a₁ a₂)
    (p₂ : G.Walk a₂ a₃) (p₃ : G.Walk a₃ t)
    (q₀ : G.Walk s b₁) (q₁ : G.Walk b₁ b₂)
    (q₂ : G.Walk b₂ b₃) (q₃ : G.Walk b₃ t)
    (hp₀ : p₀.IsPath) (hp₁ : p₁.IsPath)
    (hp₂' : p₂.IsPath) (hp₃' : p₃.IsPath)
    (hq₀ : q₀.IsPath) (hq₁ : q₁.IsPath)
    (hq₂' : q₂.IsPath) (hq₃' : q₃.IsPath)
    (hp₀₁ : ∀ w, w ∈ p₀.support → w ∈ p₁.support → w = a₁)
    (hp₂ : ∀ w, w ∈ (p₀.append p₁).support →
      w ∈ p₂.support → w = a₂)
    (hp₃ : ∀ w, w ∈ ((p₀.append p₁).append p₂).support →
      w ∈ p₃.support → w = a₃)
    (hq₀₁ : ∀ w, w ∈ q₀.support → w ∈ q₁.support → w = b₁)
    (hq₂ : ∀ w, w ∈ (q₀.append q₁).support →
      w ∈ q₂.support → w = b₂)
    (hq₃ : ∀ w, w ∈ ((q₀.append q₁).append q₂).support →
      w ∈ q₃.support → w = b₃)
    (hmeet : ∀ w,
      w ∈ (((p₀.append p₁).append p₂).append p₃).support →
      w ∈ (((q₀.append q₁).append q₂).append q₃).support →
      w = s ∨ w = t)
    (hx₀ : x ∈ p₀.support) (hxs : x ≠ s) (hxt : x ≠ t)
    (hy :
      y ∈ (((p₀.append p₁).append p₂).append p₃).support ∨
      y ∈ (((q₀.append q₁).append q₂).append q₃).support)
    (hz :
      z ∈ (((p₀.append p₁).append p₂).append p₃).support ∨
      z ∈ (((q₀.append q₁).append q₂).append q₃).support) :
    HasCycleThroughThree G x y z := by
  have hp₀₁' : (p₀.append p₁).IsPath :=
    hp₀.append_of_meet_only_endpoint_wm hp₁ hp₀₁
  have hp₀₁₂ : ((p₀.append p₁).append p₂).IsPath :=
    hp₀₁'.append_of_meet_only_endpoint_wm hp₂' hp₂
  have hp : (((p₀.append p₁).append p₂).append p₃).IsPath :=
    hp₀₁₂.append_of_meet_only_endpoint_wm hp₃' hp₃
  have hq₀₁' : (q₀.append q₁).IsPath :=
    hq₀.append_of_meet_only_endpoint_wm hq₁ hq₀₁
  have hq₀₁₂ : ((q₀.append q₁).append q₂).IsPath :=
    hq₀₁'.append_of_meet_only_endpoint_wm hq₂' hq₂
  have hq : (((q₀.append q₁).append q₂).append q₃).IsPath :=
    hq₀₁₂.append_of_meet_only_endpoint_wm hq₃' hq₃
  have hx : x ∈ (((p₀.append p₁).append p₂).append p₃).support := by
    simp only [Walk.mem_support_append_iff]
    exact Or.inl (Or.inl (Or.inl hx₀))
  refine hasCycleThroughThree_of_two_clean_arcs
    (((p₀.append p₁).append p₂).append p₃)
    (((q₀.append q₁).append q₂).append q₃)
    hp hq hx hxs hxt hmeet ?_ hy hz
  exact Or.inl hx

/-! ## The three maximal routed separators -/

private theorem HasCycleThroughThree.reorder_yxz
    {x y z : V} (h : HasCycleThroughThree G y x z) :
    HasCycleThroughThree G x y z := by
  obtain ⟨r, C, hC, hy, hx, hz⟩ := h
  exact ⟨r, C, hC, hx, hy, hz⟩

private theorem HasCycleThroughThree.reorder_zxy
    {x y z : V} (h : HasCycleThroughThree G z x y) :
    HasCycleThroughThree G x y z := by
  obtain ⟨r, C, hC, hz, hx, hy⟩ := h
  exact ⟨r, C, hC, hx, hy, hz⟩

/-- Maximal routed separator of `x` from the rim through `y,z`. -/
theorem WatkinsMesnerK32Source.exists_maximal_xSeparator
    {x y z : V} (T : WatkinsMesnerK32Source G x y z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hconn : G.Connected)
    (hdelete : ∀ d : V, (G.induce fun w : V ↦ w ≠ d).Connected)
    (hno : ¬HasCycleThroughThree G x y z) :
    ∃ S : RoutedCycleSeparator T.xArmA T.xArmB T.xRim, S.IsMaximal := by
  have hyRim : y ∈ T.xRim.support := by
    simp [WatkinsMesnerK32Source.xRim, T.y_mem]
  have hzRim : z ∈ T.xRim.support := by
    simp [WatkinsMesnerK32Source.xRim, T.z_mem]
  obtain ⟨S⟩ := exists_vertexCycleSeparator_of_no_common_cycle
    T.xRim T.xRim_isCycle T.x_not_mem_xRim hyRim hzRim
      hxy hxz hyz hconn hdelete hno
  have hbranchA : T.branchA ∈ T.xRim.support := T.xRim.start_mem_support
  have hbranchB : T.branchB ∈ T.xRim.support := by
    simp [WatkinsMesnerK32Source.xRim]
  obtain ⟨R, -⟩ := exists_routedCycleSeparator_of_vertexCycleSeparator
    (T.xRoute_isPath.takeUntil T.x_mem)
    (T.xRoute_isPath.dropUntil T.x_mem).reverse
    hbranchA hbranchB
    (fun w hwA hwB ↦
      Walk.IsPath.takeUntil_inter_reverse_dropUntil_only
        T.xRoute_isPath T.x_mem w hwA hwB) S
  exact exists_maximal_routedCycleSeparator ⟨R⟩

/-- Maximal routed separator of `y` from the rim through `x,z`. -/
theorem WatkinsMesnerK32Source.exists_maximal_ySeparator
    {x y z : V} (T : WatkinsMesnerK32Source G x y z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hconn : G.Connected)
    (hdelete : ∀ d : V, (G.induce fun w : V ↦ w ≠ d).Connected)
    (hno : ¬HasCycleThroughThree G x y z) :
    ∃ S : RoutedCycleSeparator T.yArmA T.yArmB T.yRim, S.IsMaximal := by
  have hxRim : x ∈ T.yRim.support := by
    simp [WatkinsMesnerK32Source.yRim, T.x_mem]
  have hzRim : z ∈ T.yRim.support := by
    simp [WatkinsMesnerK32Source.yRim, T.z_mem]
  have hno' : ¬HasCycleThroughThree G y x z :=
    fun h ↦ hno h.reorder_yxz
  obtain ⟨S⟩ := exists_vertexCycleSeparator_of_no_common_cycle
    T.yRim T.yRim_isCycle T.y_not_mem_yRim hxRim hzRim
      hxy.symm hyz hxz hconn hdelete hno'
  have hbranchA : T.branchA ∈ T.yRim.support := T.yRim.start_mem_support
  have hbranchB : T.branchB ∈ T.yRim.support := by
    simp [WatkinsMesnerK32Source.yRim]
  obtain ⟨R, -⟩ := exists_routedCycleSeparator_of_vertexCycleSeparator
    (T.yRoute_isPath.takeUntil T.y_mem)
    (T.yRoute_isPath.dropUntil T.y_mem).reverse
    hbranchA hbranchB
    (fun w hwA hwB ↦
      Walk.IsPath.takeUntil_inter_reverse_dropUntil_only
        T.yRoute_isPath T.y_mem w hwA hwB) S
  exact exists_maximal_routedCycleSeparator ⟨R⟩

/-- Maximal routed separator of `z` from the rim through `x,y`. -/
theorem WatkinsMesnerK32Source.exists_maximal_zSeparator
    {x y z : V} (T : WatkinsMesnerK32Source G x y z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hconn : G.Connected)
    (hdelete : ∀ d : V, (G.induce fun w : V ↦ w ≠ d).Connected)
    (hno : ¬HasCycleThroughThree G x y z) :
    ∃ S : RoutedCycleSeparator T.zArmA T.zArmB T.zRim, S.IsMaximal := by
  have hxRim : x ∈ T.zRim.support := by
    simp [WatkinsMesnerK32Source.zRim, T.x_mem]
  have hyRim : y ∈ T.zRim.support := by
    simp [WatkinsMesnerK32Source.zRim, T.y_mem]
  have hno' : ¬HasCycleThroughThree G z x y :=
    fun h ↦ hno h.reorder_zxy
  obtain ⟨S⟩ := exists_vertexCycleSeparator_of_no_common_cycle
    T.zRim T.zRim_isCycle T.z_not_mem_zRim hxRim hyRim
      hxz.symm hyz.symm hxy hconn hdelete hno'
  have hbranchA : T.branchA ∈ T.zRim.support := T.zRim.start_mem_support
  have hbranchB : T.branchB ∈ T.zRim.support := by
    simp [WatkinsMesnerK32Source.zRim]
  obtain ⟨R, -⟩ := exists_routedCycleSeparator_of_vertexCycleSeparator
    (T.zRoute_isPath.takeUntil T.z_mem)
    (T.zRoute_isPath.dropUntil T.z_mem).reverse
    hbranchA hbranchB
    (fun w hwA hwB ↦
      Walk.IsPath.takeUntil_inter_reverse_dropUntil_only
        T.zRoute_isPath T.z_mem w hwA hwB) S
  exact exists_maximal_routedCycleSeparator ⟨R⟩

/-
The tempting assertion that the complement of an arbitrary routed side is
automatically two-connected is false: the separator vertices lie on the
terminal arms, not on the opposite rim.  Condition (vi) genuinely uses the
maximality of the terminal side.  The abandoned direct argument is kept
out of the elaborated development below while the maximality refinement is
proved.

/-! ## The complement of a routed side is two-connected -/

/-- The two rim vertices bounding a routed component remain connected on
the rim after deleting any third vertex. -/
theorem RoutedCycleSeparator.boundary_reachable_avoiding
    {a b x r : V} {pA : G.Walk a x} {pB : G.Walk b x}
    {C : G.Walk r r} (hC : C.IsCycle)
    (S : RoutedCycleSeparator pA pB C) (d : V)
    (hdl : S.left ≠ d) (hdr : S.right ≠ d) :
    (G.induce fun w : V ↦
      w ∉ componentCarrier (G := G) {S.left, S.right} S.side ∧ w ≠ d).Reachable
      ⟨S.left, by
        constructor
        · intro h
          exact ComponentCompl.notMem_of_mem
            (by simpa only [mem_componentCarrier] using h) (by simp)
        · exact hdl⟩
      ⟨S.right, by
        constructor
        · intro h
          exact ComponentCompl.notMem_of_mem
            (by simpa only [mem_componentCarrier] using h) (by simp)
        · exact hdr⟩ := by
  classical
  obtain ⟨A⟩ := exists_cycleArcPair hC S.left_mem_aArm
    S.right_mem_bArm S.left_ne_right
  have arc_good (q : G.Walk S.left S.right)
      (hqSub : ∀ w, w ∈ q.support → w ∈ C.support)
      (hdq : d ∉ q.support) :
      (G.induce fun w : V ↦
        w ∉ componentCarrier (G := G) {S.left, S.right} S.side ∧ w ≠ d).Reachable
        ⟨S.left, by
          constructor
          · intro h
            exact ComponentCompl.notMem_of_mem
              (by simpa only [mem_componentCarrier] using h) (by simp)
          · exact hdl⟩
        ⟨S.right, by
          constructor
          · intro h
            exact ComponentCompl.notMem_of_mem
              (by simpa only [mem_componentCarrier] using h) (by simp)
          · exact hdr⟩ := by
    have hgood : ∀ w ∈ q.support,
        w ∉ componentCarrier (G := G) {S.left, S.right} S.side ∧ w ≠ d := by
      intro w hw
      constructor
      · intro hwSide
        have hwSide' : w ∈ (S.side : Set V) := by
          simpa only [mem_componentCarrier] using hwSide
        by_cases hwL : w = S.left
        · subst w
          exact ComponentCompl.notMem_of_mem hwSide' (by simp)
        by_cases hwR : w = S.right
        · subst w
          exact ComponentCompl.notMem_of_mem hwSide' (by simp)
        exact S.rim_outside_side w (hqSub w hw) hwL hwR hwSide'
      · exact fun h ↦ hdq (h ▸ hw)
    exact (q.induce _ hgood).reachable
  by_cases hdA : d ∈ A.first.support
  · have hdSecond : d ∉ A.second.support := by
      intro hd
      rcases A.meet_only_ends d hdA hd with h | h
      · exact hdl h.symm
      · exact hdr h.symm
    exact arc_good A.second A.second_subset hdSecond
  · exact arc_good A.first A.first_subset hdA

/-- Deleting the terminal-side component of a routed two-cut leaves a
vertex-two-connected graph.  The proof contracts every excursion through
the deleted component to a surviving boundary vertex; the opposite rim
connects the two boundary vertices after any third vertex is deleted. -/
theorem RoutedCycleSeparator.complementVertexTwoConnected
    {a b x r : V} {pA : G.Walk a x} {pB : G.Walk b x}
    {C : G.Walk r r} (hC : C.IsCycle)
    (S : RoutedCycleSeparator pA pB C)
    (hconn : G.Connected)
    (hdelete : ∀ d : V, (G.induce fun w : V ↦ w ≠ d).Connected) :
    ComplementVertexTwoConnected G
      (componentCarrier (G := G) {S.left, S.right} S.side) := by
  classical
  let X := componentCarrier (G := G) {S.left, S.right} S.side
  have hleftX : S.left ∉ X := by
    intro h
    exact ComponentCompl.notMem_of_mem
      (by simpa only [X, mem_componentCarrier] using h) (by simp)
  have hrightX : S.right ∉ X := by
    intro h
    exact ComponentCompl.notMem_of_mem
      (by simpa only [X, mem_componentCarrier] using h) (by simp)
  have boundary_of_adj {v w : V} (hvX : v ∈ X) (hwX : w ∉ X)
      (hvw : G.Adj v w) : w = S.left ∨ w = S.right := by
    by_contra h
    push_neg at h
    have hwPair : w ∉ ((({S.left, S.right} : Finset V) : Set V)) := by
      simpa [h.1, h.2]
    have hvSide : v ∈ (S.side : Set V) := by
      simpa only [X, mem_componentCarrier] using hvX
    have hwSide : w ∈ (S.side : Set V) :=
      ComponentCompl.mem_of_adj v w hvSide hwPair hvw
    exact hwX (by simpa only [X, mem_componentCarrier] using hwSide)
  have deleted_connected (d : {v : V // v ∉ X}) :
      ((G.induce fun v : V ↦ v ∉ X).induce
        fun w : {v : V // v ∉ X} ↦ w ≠ d).Connected := by
    let D := G.induce fun v : V ↦ v ≠ d.1
    let J := G.induce fun v : V ↦ v ∉ X ∧ v ≠ d.1
    let e : {v : V // v ∉ X ∧ v ≠ d.1} ≣
        {w : {v : V // v ∉ X} // w ≠ d} :=
      { toFun := fun v ↦
          ⟨⟨v.1, v.2.1⟩, fun h ↦ v.2.2 (congrArg Subtype.val h)⟩
        invFun := fun v ↦
          ⟨v.1.1, v.1.2, fun h ↦ v.2 (Subtype.ext h)⟩
        left_inv := by intro v; rfl
        right_inv := by intro v; rfl }
    let gi : J ≃g
        ((G.induce fun v : V ↦ v ∉ X).induce
          fun w : {v : V // v ∉ X} ↦ w ≠ d) :=
      { toEquiv := e
        map_rel_iff' := by intro u v; rfl }
    have chooseBoundary : ∃ c : V,
        c ∉ X ∧ c ≠ d.1 ∧
        ∀ f : V, f ∉ X → f ≠ d.1 →
          (f = S.left ∨ f = S.right) →
          J.Reachable ⟨c, by assumption⟩ ⟨f, by assumption⟩ := by
      by_cases hdl : S.left = d.1
      · refine ⟨S.right, hrightX, ?_, ?_⟩
        · exact fun h ↦ S.left_ne_right (hdl.trans h.symm)
        · intro f hfX hfd hf
          rcases hf with rfl | rfl
          · exact (hfd hdl).elim
          · exact Reachable.refl _
      by_cases hdr : S.right = d.1
      · refine ⟨S.left, hleftX, hdl, ?_⟩
        intro f hfX hfd hf
        rcases hf with rfl | rfl
        · exact Reachable.refl _
        · exact (hfd hdr).elim
      · refine ⟨S.left, hleftX, hdl, ?_⟩
        intro f hfX hfd hf
        rcases hf with rfl | rfl
        · exact Reachable.refl _
        · simpa only [J, X] using
            S.boundary_reachable_avoiding hC d.1 hdl hdr
    obtain ⟨c, hcX, hcd, hboundary⟩ := chooseBoundary
    let anchor : {v : V // v ≠ d.1} → {v : V // v ∉ X ∧ v ≠ d.1} :=
      fun v ↦ if hv : v.1 ∈ X then ⟨c, hcX, hcd⟩
        else ⟨v.1, hv, v.2⟩
    have anchor_outside {v : {v : V // v ≠ d.1}} (hv : v.1 ∉ X) :
        anchor v = ⟨v.1, hv, v.2⟩ := by
      simp [anchor, hv]
    have anchor_adj (v w : {q : V // q ≠ d.1}) (hvw : D.Adj v w) :
        J.Reachable (anchor v) (anchor w) := by
      by_cases hvX : v.1 ∈ X <;> by_cases hwX : w.1 ∈ X
      · simp [anchor, hvX, hwX]
      · have hwB : w.1 = S.left ∨ w.1 = S.right :=
          boundary_of_adj hvX hwX hvw
        simpa only [anchor, dif_pos hvX, dif_neg hwX] using
          hboundary w.1 hwX w.2 hwB
      · have hvB : v.1 = S.left ∨ v.1 = S.right :=
          boundary_of_adj hwX hvX hvw.symm
        simpa only [anchor, dif_neg hvX, dif_pos hwX] using
          (hboundary v.1 hvX v.2 hvB).symm
      · have hadj : J.Adj ⟨v.1, hvX, v.2⟩ ⟨w.1, hwX, w.2⟩ := hvw
        simpa only [anchor, dif_neg hvX, dif_neg hwX] using hadj.reachable
    have anchor_walk {v w : {q : V // q ≠ d.1}} (p : D.Walk v w) :
        J.Reachable (anchor v) (anchor w) := by
      induction p with
      | nil => exact Reachable.refl _
      | @cons v w t hvw p ih =>
          exact (anchor_adj v w hvw).trans ih
    have hJpre : J.Preconnected := by
      intro u v
      let uD : {q : V // q ≠ d.1} := ⟨u.1, u.2.2⟩
      let vD : {q : V // q ≠ d.1} := ⟨v.1, v.2.2⟩
      obtain ⟨p, -⟩ := ((hdelete d.1) uD vD).exists_isPath
      have h := anchor_walk p
      simpa only [anchor_outside u.2.1, anchor_outside v.2.1] using h
    have hJ : J.Connected :=
      { preconnected := hJpre
        nonempty := ⟨⟨c, hcX, hcd⟩⟩ }
    exact gi.connected_iff.mp hJ
  refine ⟨?_, deleted_connected⟩
  let H := G.induce fun v : V ↦ v ∉ X
  have hLR : H.Reachable ⟨S.left, hleftX⟩ ⟨S.right, hrightX⟩ := by
    obtain ⟨A⟩ := exists_cycleArcPair hC S.left_mem_aArm
      S.right_mem_bArm S.left_ne_right
    have hgood : ∀ w, w ∈ A.first.support → w ∉ X := by
      intro w hw hwX
      have hwSide : w ∈ (S.side : Set V) := by
        simpa only [X, mem_componentCarrier] using hwX
      by_cases hwL : w = S.left
      · subst w; exact hleftX hwX
      by_cases hwR : w = S.right
      · subst w; exact hrightX hwX
      exact S.rim_outside_side w (A.first_subset w hw) hwL hwR hwSide
    exact (A.first.induce _ hgood).reachable
  have hHpre : H.Preconnected := by
    intro u v
    by_cases huL : u.1 = S.left <;> by_cases hvL : v.1 = S.left
    · subst u; subst v; exact Reachable.refl _
    · subst u
      let d : {q : V // q ∉ X} := ⟨S.left, hleftX⟩
      have hdel := deleted_connected d
      let r : {q : {q : V // q ∉ X} // q ≠ d} :=
        ⟨⟨S.right, hrightX⟩, fun h ↦ S.left_ne_right (congrArg Subtype.val h).symm⟩
      let v' : {q : {q : V // q ∉ X} // q ≠ d} :=
        ⟨v, fun h ↦ hvL (congrArg Subtype.val h)⟩
      exact hLR.trans ((hdel r v').map
        (SimpleGraph.Embedding.induce
          (G := H) (s := fun q : {q : V // q ∉ X} ↦ q ≠ d)).toHom)
    · subst v
      let d : {q : V // q ∉ X} := ⟨S.left, hleftX⟩
      have hdel := deleted_connected d
      let r : {q : {q : V // q ∉ X} // q ≠ d} :=
        ⟨⟨S.right, hrightX⟩, fun h ↦ S.left_ne_right (congrArg Subtype.val h).symm⟩
      let u' : {q : {q : V // q ∉ X} // q ≠ d} :=
        ⟨u, fun h ↦ huL (congrArg Subtype.val h)⟩
      exact (hLR.trans ((hdel r u').map
        (SimpleGraph.Embedding.induce
          (G := H) (s := fun q : {q : V // q ∉ X} ↦ q ≠ d)).toHom)).symm
    · let d : {q : V // q ∉ X} := ⟨S.left, hleftX⟩
      let u' : {q : {q : V // q ∉ X} // q ≠ d} :=
        ⟨u, fun h ↦ huL (congrArg Subtype.val h)⟩
      let v' : {q : {q : V // q ∉ X} // q ≠ d} :=
        ⟨v, fun h ↦ hvL (congrArg Subtype.val h)⟩
      exact (deleted_connected d u' v').map
        (SimpleGraph.Embedding.induce
          (G := H) (s := fun q : {q : V // q ∉ X} ↦ q ≠ d)).toHom
  exact { preconnected := hHpre, nonempty := ⟨⟨S.left, hleftX⟩⟩ }

-/

/-! ## Packaging the three simultaneous maximal choices -/

/-- The three maximal routed terminal sides selected in the proof of AHT
Theorem 5.1.  The remaining refinement shows that their six boundary
vertices form the splitter sets `A,B`. -/
structure WatkinsMesnerMaximalTriple {x y z : V}
    (T : WatkinsMesnerK32Source G x y z) where
  xSep : RoutedCycleSeparator T.xArmA T.xArmB T.xRim
  ySep : RoutedCycleSeparator T.yArmA T.yArmB T.yRim
  zSep : RoutedCycleSeparator T.zArmA T.zArmB T.zRim
  x_maximal : xSep.IsMaximal
  y_maximal : ySep.IsMaximal
  z_maximal : zSep.IsMaximal

/-- A maximal routed separator has no routed competitor with a strictly
larger terminal-side component.  This is the finite-cardinality form used
at every maximality contradiction on pp.14--15 of AHT. -/
theorem RoutedCycleSeparator.IsMaximal.not_ssubset_componentCarrier
    {a b x r : V} {pA : G.Walk a x} {pB : G.Walk b x}
    {C : G.Walk r r} {S : RoutedCycleSeparator pA pB C}
    (hS : S.IsMaximal) (R : RoutedCycleSeparator pA pB C) :
    ¬componentCarrier (G := G) {S.left, S.right} S.side ⊂
      componentCarrier (G := G) {R.left, R.right} R.side := by
  intro hstrict
  have hlt := Finset.card_lt_card hstrict
  have hle := hS R
  omega

/-- Replace the displayed rim by another closed walk with the same support.
Only the direction needed by the separator's rim-avoidance field is used. -/
def RoutedCycleSeparator.changeRim
    {a b x r s : V} {pA : G.Walk a x} {pB : G.Walk b x}
    {C : G.Walk r r} {D : G.Walk s s}
    (S : RoutedCycleSeparator pA pB C)
    (hDC : ∀ w, w ∈ D.support → w ∈ C.support) :
    RoutedCycleSeparator pA pB D where
  left := S.left
  right := S.right
  left_ne_right := S.left_ne_right
  x_ne_left := S.x_ne_left
  x_ne_right := S.x_ne_right
  side := S.side
  x_mem_side := S.x_mem_side
  rim_outside_side := fun w hw hwl hwr ↦
    S.rim_outside_side w (hDC w hw) hwl hwr
  left_mem_aArm := S.left_mem_aArm
  left_ne_terminal := S.left_ne_terminal
  right_mem_bArm := S.right_mem_bArm
  right_ne_terminal := S.right_ne_terminal

/-- Maximality is invariant under changing the rim to a walk with the same
vertex support. -/
theorem RoutedCycleSeparator.IsMaximal.changeRim
    {a b x r s : V} {pA : G.Walk a x} {pB : G.Walk b x}
    {C : G.Walk r r} {D : G.Walk s s}
    (S : RoutedCycleSeparator pA pB C) (hS : S.IsMaximal)
    (hDC : ∀ w, w ∈ D.support → w ∈ C.support)
    (hCD : ∀ w, w ∈ C.support → w ∈ D.support) :
    (S.changeRim hDC).IsMaximal := by
  intro R
  let R' : RoutedCycleSeparator pA pB C := R.changeRim hCD
  have hle := hS R'
  simpa only [R', RoutedCycleSeparator.changeRim] using hle

/-- Replace the two displayed terminal arms while retaining the same
separator vertices and terminal-side component. -/
def RoutedCycleSeparator.changeArms
    {a b a' b' x r : V} {pA : G.Walk a x} {pB : G.Walk b x}
    {pA' : G.Walk a' x} {pB' : G.Walk b' x} {C : G.Walk r r}
    (S : RoutedCycleSeparator pA pB C)
    (hleft : S.left ∈ pA'.support)
    (hright : S.right ∈ pB'.support) :
    RoutedCycleSeparator pA' pB' C where
  left := S.left
  right := S.right
  left_ne_right := S.left_ne_right
  x_ne_left := S.x_ne_left
  x_ne_right := S.x_ne_right
  side := S.side
  x_mem_side := S.x_mem_side
  rim_outside_side := S.rim_outside_side
  left_mem_aArm := hleft
  left_ne_terminal := S.left_ne_terminal
  right_mem_bArm := hright
  right_ne_terminal := S.right_ne_terminal

/-- Maximality is invariant under replacing the displayed arms when every
vertex of either new arm also lies on the corresponding old arm. -/
theorem RoutedCycleSeparator.IsMaximal.changeArms
    {a b a' b' x r : V} {pA : G.Walk a x} {pB : G.Walk b x}
    {pA' : G.Walk a' x} {pB' : G.Walk b' x} {C : G.Walk r r}
    (S : RoutedCycleSeparator pA pB C) (hS : S.IsMaximal)
    (hleft : S.left ∈ pA'.support)
    (hright : S.right ∈ pB'.support)
    (hA : ∀ w, w ∈ pA'.support → w ∈ pA.support)
    (hB : ∀ w, w ∈ pB'.support → w ∈ pB.support) :
    (S.changeArms hleft hright).IsMaximal := by
  intro R
  let R' : RoutedCycleSeparator pA pB C :=
    R.changeArms (hA R.left R.left_mem_aArm)
      (hB R.right R.right_mem_bArm)
  have hle := hS R'
  simpa only [R', RoutedCycleSeparator.changeArms] using hle

/-- Reverse the A/B orientation of a routed separator, transporting its
component across the equality `{left,right} = {right,left}`. -/
noncomputable def RoutedCycleSeparator.flipAB
    {a b x r s : V} {pA : G.Walk a x} {pB : G.Walk b x}
    {C : G.Walk r r} {D : G.Walk s s}
    (S : RoutedCycleSeparator pA pB C)
    (hDC : ∀ w, w ∈ D.support → w ∈ C.support) :
    RoutedCycleSeparator pB pA D := by
  have hpair :
      ((({S.left, S.right} : Finset V) : Set V)) =
        ((({S.right, S.left} : Finset V) : Set V)) := by
    ext w
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton]
    exact or_comm
  let side : G.ComponentCompl
      ((({S.right, S.left} : Finset V) : Set V)) :=
    ComponentCompl.transport hpair S.side
  refine {
    left := S.right
    right := S.left
    left_ne_right := S.left_ne_right.symm
    x_ne_left := S.x_ne_right
    x_ne_right := S.x_ne_left
    side := side
    x_mem_side := ?_
    rim_outside_side := ?_
    left_mem_aArm := S.right_mem_bArm
    left_ne_terminal := S.right_ne_terminal
    right_mem_bArm := S.left_mem_aArm
    right_ne_terminal := S.left_ne_terminal }
  · simpa only [side, ComponentCompl.mem_transport] using S.x_mem_side
  · intro w hwD hwRight hwLeft hwSide
    have hwOld : w ∈ (S.side : Set V) := by
      simpa only [side, ComponentCompl.mem_transport] using hwSide
    exact S.rim_outside_side w (hDC w hwD) hwLeft hwRight hwOld

@[simp] theorem RoutedCycleSeparator.componentCarrier_flipAB
    {a b x r s : V} {pA : G.Walk a x} {pB : G.Walk b x}
    {C : G.Walk r r} {D : G.Walk s s}
    (S : RoutedCycleSeparator pA pB C)
    (hDC : ∀ w, w ∈ D.support → w ∈ C.support) :
    componentCarrier (G := G)
        {(S.flipAB hDC).left, (S.flipAB hDC).right}
        (S.flipAB hDC).side =
      componentCarrier (G := G) {S.left, S.right} S.side := by
  ext w
  simp only [mem_componentCarrier, RoutedCycleSeparator.flipAB,
    ComponentCompl.mem_transport]

theorem RoutedCycleSeparator.IsMaximal.flipAB
    {a b x r s : V} {pA : G.Walk a x} {pB : G.Walk b x}
    {C : G.Walk r r} {D : G.Walk s s}
    (S : RoutedCycleSeparator pA pB C) (hS : S.IsMaximal)
    (hDC : ∀ w, w ∈ D.support → w ∈ C.support)
    (hCD : ∀ w, w ∈ C.support → w ∈ D.support) :
    (S.flipAB hDC).IsMaximal := by
  intro R
  let R' : RoutedCycleSeparator pA pB C := R.flipAB hCD
  have hle := hS R'
  rw [RoutedCycleSeparator.componentCarrier_flipAB] at hle
  simpa only [RoutedCycleSeparator.componentCarrier_flipAB] using hle

/-- A connected component outside one deletion set is contained in a
component outside another deletion set as soon as it avoids the latter set
and the two components share one vertex. -/
theorem ComponentCompl.subset_of_disjoint_of_shared
    {K L : Set V} (C : G.ComponentCompl K) (D : G.ComponentCompl L)
    (hCL : Disjoint (C : Set V) L) {w : V}
    (hwC : w ∈ (C : Set V)) (hwD : w ∈ (D : Set V)) :
    (C : Set V) ⊆ (D : Set V) := by
  intro v hvC
  obtain ⟨hwK, hwEq⟩ := hwC
  obtain ⟨hvK, hvEq⟩ := hvC
  have hreach : (G.induce Kᶜ).Reachable
      (⟨w, hwK⟩ : {q : V // q ∈ Kᶜ}) ⟨v, hvK⟩ := by
    rw [← ConnectedComponent.eq]
    exact hwEq.trans hvEq.symm
  obtain ⟨p⟩ := hreach
  have walk_mem : ∀ {a b : {q : V // q ∈ Kᶜ}}
      (q : (G.induce Kᶜ).Walk a b),
      a.1 ∈ (C : Set V) → a.1 ∈ (D : Set V) → b.1 ∈ (D : Set V) := by
    intro a b q haC haD
    induction q with
    | nil => exact haD
    | @cons a b c hab q ih =>
        have hbC : b.1 ∈ (C : Set V) :=
          ComponentCompl.mem_of_adj a.1 b.1 haC b.2 hab
        have hbD : b.1 ∈ (D : Set V) :=
          ComponentCompl.mem_of_adj a.1 b.1 haD
            (fun hbL ↦ Set.disjoint_left.mp hCL hbC hbL) hab
        exact ih hbC hbD
  exact walk_mem p ⟨hwK, hwEq⟩ hwD

/-- If a component of `G - {a,b}` is bypassed by an `a`--`b` route, then
deleting the component (but retaining its two boundary vertices) leaves a
connected graph.  This is the connectivity half of condition (vi); the
one-vertex-deletion half is where maximality enters.

The proof contracts every visit of an ambient walk to the deleted component
to `a`.  An edge entering or leaving that component does so at `a` or `b`,
and the supplied bypass joins those two possible images. -/
theorem ComponentCompl.connected_induce_compl_componentCarrier
    {a b : V} (C : G.ComponentCompl (({a, b} : Finset V) : Set V))
    (hab : a ≠ b)
    (hconn : G.Connected)
    (habOutside : (G.induce fun v : V ↦
      v ∉ componentCarrier (G := G) {a, b} C).Reachable
        ⟨a, by
          intro ha
          exact ComponentCompl.notMem_of_mem
            (mem_componentCarrier.mp ha) (by simp)⟩
        ⟨b, by
          intro hb
          exact ComponentCompl.notMem_of_mem
            (mem_componentCarrier.mp hb) (by simp)⟩) :
    (G.induce fun v : V ↦
      v ∉ componentCarrier (G := G) {a, b} C).Connected := by
  classical
  let X := componentCarrier (G := G) {a, b} C
  let H := G.induce fun v : V ↦ v ∉ X
  have haX : a ∉ X := by
    intro ha
    have ha' : a ∈ componentCarrier (G := G) {a, b} C := by
      simpa only [X] using ha
    exact ComponentCompl.notMem_of_mem
      (mem_componentCarrier.mp ha') (by simp)
  have hbX : b ∉ X := by
    intro hb
    have hb' : b ∈ componentCarrier (G := G) {a, b} C := by
      simpa only [X] using hb
    exact ComponentCompl.notMem_of_mem
      (mem_componentCarrier.mp hb') (by simp)
  have boundary_of_adj {v w : V} (hvX : v ∈ X) (hwX : w ∉ X)
      (hvw : G.Adj v w) : w = a ∨ w = b := by
    by_contra hw
    push_neg at hw
    have hwPair : w ∉ ((({a, b} : Finset V) : Set V)) := by
      simpa [hw.1, hw.2]
    have hvC : v ∈ (C : Set V) := by
      simpa only [X, mem_componentCarrier] using hvX
    have hwC : w ∈ (C : Set V) :=
      ComponentCompl.mem_of_adj v w hvC hwPair hvw
    exact hwX (by simpa only [X, mem_componentCarrier] using hwC)
  let anchor : V → {v : V // v ∉ X} := fun v ↦
    if hv : v ∈ X then ⟨a, haX⟩ else ⟨v, hv⟩
  have anchor_outside {v : V} (hv : v ∉ X) :
      anchor v = ⟨v, hv⟩ := by
    simp [anchor, hv]
  have anchor_adj {v w : V} (hvw : G.Adj v w) :
      H.Reachable (anchor v) (anchor w) := by
    by_cases hvX : v ∈ X <;> by_cases hwX : w ∈ X
    · simp [anchor, hvX, hwX]
    · rcases boundary_of_adj hvX hwX hvw with rfl | rfl
      · simp [anchor, hvX, hwX]
      · simpa only [H, X, anchor, dif_pos hvX, dif_neg hwX] using
          habOutside
    · rcases boundary_of_adj hwX hvX hvw.symm with rfl | rfl
      · simp [anchor, hvX, hwX]
      · simpa only [H, X, anchor, dif_neg hvX, dif_pos hwX] using
          habOutside.symm
    · simpa only [anchor, dif_neg hvX, dif_neg hwX] using
        (show H.Adj ⟨v, hvX⟩ ⟨w, hwX⟩ from hvw).reachable
  have anchor_walk {v w : V} (p : G.Walk v w) :
      H.Reachable (anchor v) (anchor w) := by
    induction p with
    | nil => exact Reachable.refl _
    | @cons v w t hvw p ih => exact (anchor_adj hvw).trans ih
  have hpre : H.Preconnected := by
    intro u v
    obtain ⟨p⟩ := hconn.preconnected u.1 v.1
    have h := anchor_walk p
    simpa only [anchor_outside u.2, anchor_outside v.2,
      Subtype.coe_eta] using h
  exact { preconnected := hpre, nonempty := ⟨⟨a, haX⟩⟩ }

/-- Deletion version of
`ComponentCompl.connected_induce_compl_componentCarrier`.  Once `a` and
`b` can still be joined outside the chosen component after deleting `d`,
every ambient walk in `G-d` can again be contracted across that component.

This formulation deliberately makes the one genuinely maximality-dependent
fact -- the surviving `a`--`b` bypass -- an explicit hypothesis. -/
theorem ComponentCompl.connected_delete_induce_compl_componentCarrier
    {a b : V} (C : G.ComponentCompl (({a, b} : Finset V) : Set V))
    (hab : a ≠ b)
    (hdelete : ∀ d : V, (G.induce fun w : V ↦ w ≠ d).Connected)
    (d : {v : V //
      v ∉ componentCarrier (G := G) {a, b} C})
    (habOutside : ∀ (hda : a ≠ d.1) (hdb : b ≠ d.1),
      (G.induce fun v : V ↦
        v ∉ componentCarrier (G := G) {a, b} C ∧ v ≠ d.1).Reachable
          ⟨a, by
            constructor
            · intro ha
              exact ComponentCompl.notMem_of_mem
                (mem_componentCarrier.mp ha) (by simp)
            · exact hda⟩
          ⟨b, by
            constructor
            · intro hb
              exact ComponentCompl.notMem_of_mem
                (mem_componentCarrier.mp hb) (by simp)
            · exact hdb⟩) :
    ((G.induce fun v : V ↦
      v ∉ componentCarrier (G := G) {a, b} C).induce
        fun w : {v : V //
          v ∉ componentCarrier (G := G) {a, b} C} ↦ w ≠ d).Connected := by
  classical
  let X := componentCarrier (G := G) {a, b} C
  let J := G.induce fun v : V ↦ v ∉ X ∧ v ≠ d.1
  let K := (G.induce fun v : V ↦ v ∉ X).induce
    fun w : {v : V // v ∉ X} ↦ w ≠ d
  have haX : a ∉ X := by
    intro ha
    have ha' : a ∈ componentCarrier (G := G) {a, b} C := by
      simpa only [X] using ha
    exact ComponentCompl.notMem_of_mem
      (mem_componentCarrier.mp ha') (by simp)
  have hbX : b ∉ X := by
    intro hb
    have hb' : b ∈ componentCarrier (G := G) {a, b} C := by
      simpa only [X] using hb
    exact ComponentCompl.notMem_of_mem
      (mem_componentCarrier.mp hb') (by simp)
  have boundary_of_adj {v w : V} (hvX : v ∈ X) (hwX : w ∉ X)
      (hvw : G.Adj v w) : w = a ∨ w = b := by
    by_contra hw
    push_neg at hw
    have hwPair : w ∉ ((({a, b} : Finset V) : Set V)) := by
      simpa [hw.1, hw.2]
    have hvC : v ∈ (C : Set V) := by
      simpa only [X, mem_componentCarrier] using hvX
    have hwC : w ∈ (C : Set V) :=
      ComponentCompl.mem_of_adj v w hvC hwPair hvw
    exact hwX (by simpa only [X, mem_componentCarrier] using hwC)
  let e : {v : V // v ∉ X ∧ v ≠ d.1} ≃
      {w : {v : V // v ∉ X} // w ≠ d} :=
    { toFun := fun v ↦
        ⟨⟨v.1, v.2.1⟩, fun h ↦ v.2.2 (congrArg Subtype.val h)⟩
      invFun := fun v ↦
        ⟨v.1.1, v.1.2, fun h ↦ v.2 (Subtype.ext h)⟩
      left_inv := by intro v; rfl
      right_inv := by intro v; rfl }
  let gi : J ≃g K :=
    { toEquiv := e
      map_rel_iff' := by intro u v; rfl }
  have chooseBoundary : ∃ (c : V) (hcX : c ∉ X) (hcd : c ≠ d.1),
      ∀ (f : V) (hfX : f ∉ X) (hfd : f ≠ d.1),
        (f = a ∨ f = b) →
        J.Reachable ⟨c, hcX, hcd⟩ ⟨f, hfX, hfd⟩ := by
    by_cases hda : a = d.1
    · refine ⟨b, hbX, ?_, ?_⟩
      · exact fun h ↦ hab (hda.trans h.symm)
      · intro f hfX hfd hf
        rcases hf with rfl | rfl
        · exact (hfd hda).elim
        · exact Reachable.refl _
    by_cases hdb : b = d.1
    · refine ⟨a, haX, hda, ?_⟩
      intro f hfX hfd hf
      rcases hf with rfl | rfl
      · exact Reachable.refl _
      · exact (hfd hdb).elim
    · refine ⟨a, haX, hda, ?_⟩
      intro f hfX hfd hf
      rcases hf with rfl | rfl
      · exact Reachable.refl _
      · simpa only [J, X] using habOutside hda hdb
  obtain ⟨c, hcX, hcd, hboundary⟩ := chooseBoundary
  let anchor : {v : V // v ≠ d.1} →
      {v : V // v ∉ X ∧ v ≠ d.1} := fun v ↦
    if hv : v.1 ∈ X then ⟨c, hcX, hcd⟩ else ⟨v.1, hv, v.2⟩
  have anchor_outside {v : {q : V // q ≠ d.1}} (hv : v.1 ∉ X) :
      anchor v = ⟨v.1, hv, v.2⟩ := by
    simp [anchor, hv]
  have anchor_adj (v w : {q : V // q ≠ d.1})
      (hvw : (G.induce fun q : V ↦ q ≠ d.1).Adj v w) :
      J.Reachable (anchor v) (anchor w) := by
    by_cases hvX : v.1 ∈ X <;> by_cases hwX : w.1 ∈ X
    · simp [anchor, hvX, hwX]
    · have hwB : w.1 = a ∨ w.1 = b :=
        boundary_of_adj hvX hwX hvw
      simpa only [anchor, dif_pos hvX, dif_neg hwX] using
        hboundary w.1 hwX w.2 hwB
    · have hvB : v.1 = a ∨ v.1 = b :=
        boundary_of_adj hwX hvX hvw.symm
      simpa only [anchor, dif_neg hvX, dif_pos hwX] using
        (hboundary v.1 hvX v.2 hvB).symm
    · simpa only [anchor, dif_neg hvX, dif_neg hwX] using
        (show J.Adj ⟨v.1, hvX, v.2⟩ ⟨w.1, hwX, w.2⟩
          from hvw).reachable
  have anchor_walk {v w : {q : V // q ≠ d.1}}
      (p : (G.induce fun q : V ↦ q ≠ d.1).Walk v w) :
      J.Reachable (anchor v) (anchor w) := by
    induction p with
    | nil => exact Reachable.refl _
    | @cons v w t hvw p ih => exact (anchor_adj v w hvw).trans ih
  have hJpre : J.Preconnected := by
    intro u v
    let uD : {q : V // q ≠ d.1} := ⟨u.1, u.2.2⟩
    let vD : {q : V // q ≠ d.1} := ⟨v.1, v.2.2⟩
    obtain ⟨p⟩ := (hdelete d.1).preconnected uD vD
    have h := anchor_walk p
    rw [anchor_outside (v := uD) u.2.1,
      anchor_outside (v := vD) v.2.1] at h
    convert h using 1 <;> apply Subtype.ext <;> rfl
  have hJ : J.Connected :=
    { preconnected := hJpre
      nonempty := ⟨⟨c, hcX, hcd⟩⟩ }
  exact gi.connected_iff.mp hJ

/-- A two-cut component has vertex-two-connected complement as soon as its
two boundary vertices remain mutually reachable outside the component,
both before and after deletion of every surviving third vertex. -/
theorem ComponentCompl.complementVertexTwoConnected_of_boundary_reachable
    {a b : V} (C : G.ComponentCompl (({a, b} : Finset V) : Set V))
    (hab : a ≠ b) (hconn : G.Connected)
    (hdelete : ∀ d : V, (G.induce fun w : V ↦ w ≠ d).Connected)
    (habOutside : (G.induce fun v : V ↦
      v ∉ componentCarrier (G := G) {a, b} C).Reachable
        ⟨a, by
          intro ha
          exact ComponentCompl.notMem_of_mem
            (mem_componentCarrier.mp ha) (by simp)⟩
        ⟨b, by
          intro hb
          exact ComponentCompl.notMem_of_mem
            (mem_componentCarrier.mp hb) (by simp)⟩)
    (habDelete : ∀ (d : {v : V //
        v ∉ componentCarrier (G := G) {a, b} C})
      (hda : a ≠ d.1) (hdb : b ≠ d.1),
      (G.induce fun v : V ↦
        v ∉ componentCarrier (G := G) {a, b} C ∧ v ≠ d.1).Reachable
          ⟨a, by
            constructor
            · intro ha
              exact ComponentCompl.notMem_of_mem
                (mem_componentCarrier.mp ha) (by simp)
            · exact hda⟩
          ⟨b, by
            constructor
            · intro hb
              exact ComponentCompl.notMem_of_mem
                (mem_componentCarrier.mp hb) (by simp)
            · exact hdb⟩) :
    ComplementVertexTwoConnected G
      (componentCarrier (G := G) {a, b} C) := by
  refine ⟨ComponentCompl.connected_induce_compl_componentCarrier
    C hab hconn habOutside, ?_⟩
  intro d
  exact ComponentCompl.connected_delete_induce_compl_componentCarrier C
    hab hdelete d (habDelete d)

/-- Contract a component of `G-{a,b}` to `a` along a walk which already
avoids `b`.  This is the local contraction used when a hypothetical new
two-cut `{d,b}` puts a rim vertex on the terminal side. -/
theorem ComponentCompl.reachable_compl_component_of_reachable_avoiding_right
    {a b d u v : V}
    (C : G.ComponentCompl (({a, b} : Finset V) : Set V))
    (had : a ≠ d)
    (huX : u ∉ componentCarrier (G := G) {a, b} C) (hud : u ≠ d)
    (hub : u ≠ b)
    (hvX : v ∉ componentCarrier (G := G) {a, b} C) (hvd : v ≠ d)
    (hvb : v ≠ b)
    (hreach : (G.induce fun w : V ↦ w ≠ d ∧ w ≠ b).Reachable
      ⟨u, hud, hub⟩ ⟨v, hvd, hvb⟩) :
    (G.induce fun w : V ↦
      w ∉ componentCarrier (G := G) {a, b} C ∧ w ≠ d).Reachable
        ⟨u, huX, hud⟩ ⟨v, hvX, hvd⟩ := by
  classical
  let X := componentCarrier (G := G) {a, b} C
  let J := G.induce fun w : V ↦ w ∉ X ∧ w ≠ d
  have haX : a ∉ X := by
    intro ha
    have ha' : a ∈ componentCarrier (G := G) {a, b} C := by
      simpa only [X] using ha
    exact ComponentCompl.notMem_of_mem
      (mem_componentCarrier.mp ha') (by simp)
  have boundary_of_adj {s t : V} (hsX : s ∈ X) (htX : t ∉ X)
      (hst : G.Adj s t) : t = a ∨ t = b := by
    by_contra ht
    push_neg at ht
    have htPair : t ∉ ((({a, b} : Finset V) : Set V)) := by
      simpa [ht.1, ht.2]
    have hsC : s ∈ (C : Set V) := by
      simpa only [X, mem_componentCarrier] using hsX
    have htC : t ∈ (C : Set V) :=
      ComponentCompl.mem_of_adj s t hsC htPair hst
    exact htX (by simpa only [X, mem_componentCarrier] using htC)
  obtain ⟨p⟩ := hreach
  let anchor : {w : V // w ≠ d ∧ w ≠ b} →
      {w : V // w ∉ X ∧ w ≠ d} := fun w ↦
    if hw : w.1 ∈ X then ⟨a, haX, had⟩ else ⟨w.1, hw, w.2.1⟩
  have anchor_outside {w : {q : V // q ≠ d ∧ q ≠ b}}
      (hw : w.1 ∉ X) : anchor w = ⟨w.1, hw, w.2.1⟩ := by
    simp [anchor, hw]
  have anchor_adj (s t : {q : V // q ≠ d ∧ q ≠ b})
      (hst : (G.induce fun q : V ↦ q ≠ d ∧ q ≠ b).Adj s t) :
      J.Reachable (anchor s) (anchor t) := by
    by_cases hsX : s.1 ∈ X <;> by_cases htX : t.1 ∈ X
    · simp [anchor, hsX, htX]
    · rcases boundary_of_adj hsX htX hst with h | h
      · have heq : (⟨a, haX, had⟩ : {w : V // w ∉ X ∧ w ≠ d}) =
            ⟨t.1, htX, t.2.1⟩ := Subtype.ext h.symm
        simpa only [anchor, dif_pos hsX, dif_neg htX, heq] using
          (Reachable.refl (⟨a, haX, had⟩ : {w : V // w ∉ X ∧ w ≠ d}))
      · exact (t.2.2 h).elim
    · rcases boundary_of_adj htX hsX hst.symm with h | h
      · have heq : (⟨s.1, hsX, s.2.1⟩ : {w : V // w ∉ X ∧ w ≠ d}) =
            ⟨a, haX, had⟩ := Subtype.ext h
        simpa only [anchor, dif_neg hsX, dif_pos htX, heq] using
          (Reachable.refl (⟨a, haX, had⟩ : {w : V // w ∉ X ∧ w ≠ d}))
      · exact (s.2.2 h).elim
    · simpa only [anchor, dif_neg hsX, dif_neg htX] using
        (show J.Adj ⟨s.1, hsX, s.2.1⟩ ⟨t.1, htX, t.2.1⟩
          from hst).reachable
  have anchor_walk {s t : {q : V // q ≠ d ∧ q ≠ b}}
      (q : (G.induce fun q : V ↦ q ≠ d ∧ q ≠ b).Walk s t) :
      J.Reachable (anchor s) (anchor t) := by
    induction q with
    | nil => exact Reachable.refl _
    | @cons s t r hst q ih => exact (anchor_adj s t hst).trans ih
  have h := anchor_walk p
  rw [anchor_outside (w := ⟨u, hud, hub⟩) (by simpa only [X] using huX),
    anchor_outside (w := ⟨v, hvd, hvb⟩) (by simpa only [X] using hvX)] at h
  convert h using 1 <;> apply Subtype.ext <;> rfl

/-- The prefix of the first routed arm, up to its separator vertex, lies
outside the separated terminal component.  The two arms are assumed to meet
only at their common terminal and the arm's initial vertex lies on the
opposite rim. -/
theorem RoutedCycleSeparator.aPrefix_outside_side
    {a b x r : V} {pA : G.Walk a x} {pB : G.Walk b x}
    {C : G.Walk r r} (S : RoutedCycleSeparator pA pB C)
    (hpA : pA.IsPath) (haC : a ∈ C.support)
    (harms : ∀ w, w ∈ pA.support → w ∈ pB.support → w = x) :
    ∀ w, w ∈ (pA.takeUntil S.left S.left_mem_aArm).support →
      w ∉ (S.side : Set V) := by
  intro w hwPrefix hwSide
  have hwA : w ∈ pA.support :=
    pA.support_takeUntil_subset_support S.left_mem_aArm hwPrefix
  have hrightNotA : S.right ∉ pA.support := by
    intro hrA
    have hrx := harms S.right hrA S.right_mem_bArm
    exact S.right_ne_terminal hrx
  have hwLeft : w ≠ S.left := by
    intro h
    subst w
    exact ComponentCompl.notMem_of_mem hwSide (by simp)
  let q := pA.takeUntil w hwA
  have hleftQ : S.left ∉ q.support := by
    exact pA.notMem_support_takeUntil_support_takeUntil_subset
      (x := w) (w := S.left) hwLeft S.left_mem_aArm hwPrefix
  have hrightQ : S.right ∉ q.support := fun h ↦
    hrightNotA (pA.support_takeUntil_subset_support hwA h)
  have havoid : ∀ v ∈ q.support,
      v ∈ ((({S.left, S.right} : Finset V) : Set V))ᶜ := by
    intro v hv
    simpa only [Set.mem_compl_iff, Finset.mem_coe, Finset.mem_insert,
      Finset.mem_singleton, not_or] using
      ⟨fun h ↦ hleftQ (h ▸ hv), fun h ↦ hrightQ (h ▸ hv)⟩
  have hcomp : G.componentComplMk (havoid a q.start_mem_support) =
      G.componentComplMk (havoid w q.end_mem_support) := by
    rw [ConnectedComponent.eq]
    exact (q.induce _ havoid).reachable
  have hwEq : G.componentComplMk (havoid w q.end_mem_support) = S.side :=
    hwSide.choose_spec
  have haSide : a ∈ (S.side : Set V) :=
    ⟨havoid a q.start_mem_support, hcomp.trans hwEq⟩
  have haLeft : a ≠ S.left := fun h ↦
    ComponentCompl.notMem_of_mem haSide (by simp [h])
  have haRight : a ≠ S.right := fun h ↦
    ComponentCompl.notMem_of_mem haSide (by simp [h])
  exact S.rim_outside_side a haC haLeft haRight haSide

/-- Symmetric prefix lemma for the second routed arm. -/
theorem RoutedCycleSeparator.bPrefix_outside_side
    {a b x r : V} {pA : G.Walk a x} {pB : G.Walk b x}
    {C : G.Walk r r} (S : RoutedCycleSeparator pA pB C)
    (hpB : pB.IsPath) (hbC : b ∈ C.support)
    (harms : ∀ w, w ∈ pA.support → w ∈ pB.support → w = x) :
    ∀ w, w ∈ (pB.takeUntil S.right S.right_mem_bArm).support →
      w ∉ (S.side : Set V) := by
  intro w hwPrefix hwSide
  have hwB : w ∈ pB.support :=
    pB.support_takeUntil_subset_support S.right_mem_bArm hwPrefix
  have hleftNotB : S.left ∉ pB.support := by
    intro hlB
    have hlx := harms S.left S.left_mem_aArm hlB
    exact S.left_ne_terminal hlx
  have hwRight : w ≠ S.right := by
    intro h
    subst w
    exact ComponentCompl.notMem_of_mem hwSide (by simp)
  let q := pB.takeUntil w hwB
  have hrightQ : S.right ∉ q.support := by
    exact pB.notMem_support_takeUntil_support_takeUntil_subset
      (x := w) (w := S.right) hwRight S.right_mem_bArm hwPrefix
  have hleftQ : S.left ∉ q.support := fun h ↦
    hleftNotB (pB.support_takeUntil_subset_support hwB h)
  have havoid : ∀ v ∈ q.support,
      v ∈ ((({S.left, S.right} : Finset V) : Set V))ᶜ := by
    intro v hv
    simpa only [Set.mem_compl_iff, Finset.mem_coe, Finset.mem_insert,
      Finset.mem_singleton, not_or] using
      ⟨fun h ↦ hleftQ (h ▸ hv), fun h ↦ hrightQ (h ▸ hv)⟩
  have hcomp : G.componentComplMk (havoid b q.start_mem_support) =
      G.componentComplMk (havoid w q.end_mem_support) := by
    rw [ConnectedComponent.eq]
    exact (q.induce _ havoid).reachable
  have hwEq : G.componentComplMk (havoid w q.end_mem_support) = S.side :=
    hwSide.choose_spec
  have hbSide : b ∈ (S.side : Set V) :=
    ⟨havoid b q.start_mem_support, hcomp.trans hwEq⟩
  have hbLeft : b ≠ S.left := fun h ↦
    ComponentCompl.notMem_of_mem hbSide (by simp [h])
  have hbRight : b ≠ S.right := fun h ↦
    ComponentCompl.notMem_of_mem hbSide (by simp [h])
  exact S.rim_outside_side b hbC hbLeft hbRight hbSide

/-- The standard outer bypass associated with a routed separator: go back
along the first arm to its rim end, traverse a chosen rim route, then go
forward along the second arm to the other separator vertex. -/
def RoutedCycleSeparator.outerBypass
    {a b x r : V} {pA : G.Walk a x} {pB : G.Walk b x}
    {C : G.Walk r r} (S : RoutedCycleSeparator pA pB C)
    (q : G.Walk a b) : G.Walk S.left S.right :=
  (pA.takeUntil S.left S.left_mem_aArm).reverse |>.append
    (q.append (pB.takeUntil S.right S.right_mem_bArm))

/-- If the middle route of an outer bypass lies on the displayed rim, the
whole bypass avoids the separated terminal component. -/
theorem RoutedCycleSeparator.outerBypass_outside_side
    {a b x r : V} {pA : G.Walk a x} {pB : G.Walk b x}
    {C : G.Walk r r} (S : RoutedCycleSeparator pA pB C)
    (hpA : pA.IsPath) (hpB : pB.IsPath)
    (haC : a ∈ C.support) (hbC : b ∈ C.support)
    (harms : ∀ w, w ∈ pA.support → w ∈ pB.support → w = x)
    (q : G.Walk a b) (hqC : ∀ w, w ∈ q.support → w ∈ C.support) :
    ∀ w, w ∈ (S.outerBypass q).support → w ∉ (S.side : Set V) := by
  intro w hw hwSide
  have hwCases :
      w ∈ (pA.takeUntil S.left S.left_mem_aArm).reverse.support ∨
      w ∈ q.support ∨
      w ∈ (pB.takeUntil S.right S.right_mem_bArm).support := by
    simpa only [RoutedCycleSeparator.outerBypass,
      Walk.mem_support_append_iff, Walk.support_reverse,
      List.mem_reverse, or_assoc] using hw
  rcases hwCases with hwA | hwQ | hwB
  · exact S.aPrefix_outside_side hpA haC harms w
      (by simpa only [Walk.support_reverse, List.mem_reverse] using hwA) hwSide
  · have hwC := hqC w hwQ
    by_cases hwL : w = S.left
    · subst w
      exact ComponentCompl.notMem_of_mem hwSide (by simp)
    by_cases hwR : w = S.right
    · subst w
      exact ComponentCompl.notMem_of_mem hwSide (by simp)
    exact S.rim_outside_side w hwC hwL hwR hwSide
  · exact S.bPrefix_outside_side hpB hbC harms w hwB hwSide

/-- The outer bypass gives reachability between the two boundary vertices
in the complement of the terminal component. -/
theorem RoutedCycleSeparator.outerBypass_reachable
    {a b x r : V} {pA : G.Walk a x} {pB : G.Walk b x}
    {C : G.Walk r r} (S : RoutedCycleSeparator pA pB C)
    (hpA : pA.IsPath) (hpB : pB.IsPath)
    (haC : a ∈ C.support) (hbC : b ∈ C.support)
    (harms : ∀ w, w ∈ pA.support → w ∈ pB.support → w = x)
    (q : G.Walk a b) (hqC : ∀ w, w ∈ q.support → w ∈ C.support) :
    (G.induce fun v : V ↦
      v ∉ componentCarrier (G := G) {S.left, S.right} S.side).Reachable
        ⟨S.left, by
          intro h
          exact ComponentCompl.notMem_of_mem
            (mem_componentCarrier.mp h) (by simp)⟩
        ⟨S.right, by
          intro h
          exact ComponentCompl.notMem_of_mem
            (mem_componentCarrier.mp h) (by simp)⟩ := by
  let p := S.outerBypass q
  have hout : ∀ w ∈ p.support,
      w ∉ componentCarrier (G := G) {S.left, S.right} S.side := by
    intro w hw hmem
    exact S.outerBypass_outside_side hpA hpB haC hbC harms q hqC w hw
      (by simpa only [mem_componentCarrier] using hmem)
  exact (p.induce _ hout).reachable

/-- Two outer bypasses whose middle routes meet only at their ends can both
contain a vertex only if that vertex already lies on one of the two arm
prefixes.  Thus a vertex which blocks both canonical bypasses is located on
an arm, exactly as in the maximality argument for condition (vi). -/
theorem RoutedCycleSeparator.mem_prefix_of_mem_two_outerBypasses
    {a b x r : V} {pA : G.Walk a x} {pB : G.Walk b x}
    {C : G.Walk r r} (S : RoutedCycleSeparator pA pB C)
    (q₁ q₂ : G.Walk a b)
    (hmeet : ∀ w, w ∈ q₁.support → w ∈ q₂.support →
      w = a ∨ w = b) {d : V}
    (hd₁ : d ∈ (S.outerBypass q₁).support)
    (hd₂ : d ∈ (S.outerBypass q₂).support) :
    d ∈ (pA.takeUntil S.left S.left_mem_aArm).support ∨
      d ∈ (pB.takeUntil S.right S.right_mem_bArm).support := by
  have split (q : G.Walk a b)
      (hd : d ∈ (S.outerBypass q).support) :
      d ∈ (pA.takeUntil S.left S.left_mem_aArm).support ∨
      d ∈ q.support ∨
      d ∈ (pB.takeUntil S.right S.right_mem_bArm).support := by
    simpa only [RoutedCycleSeparator.outerBypass,
      Walk.mem_support_append_iff, Walk.support_reverse,
      List.mem_reverse, or_assoc] using hd
  rcases split q₁ hd₁ with hdA | hdQ₁ | hdB
  · exact Or.inl hdA
  · rcases split q₂ hd₂ with hdA | hdQ₂ | hdB
    · exact Or.inl hdA
    · rcases hmeet d hdQ₁ hdQ₂ with rfl | rfl
      · exact Or.inl (pA.takeUntil S.left S.left_mem_aArm).start_mem_support
      · exact Or.inr (pB.takeUntil S.right S.right_mem_bArm).start_mem_support
    · exact Or.inr hdB
  · exact Or.inr hdB

/-- If `d` lies on the first arm prefix, every other rim vertex can reach
the second boundary vertex outside the terminal component and without
using `d`.  On the rim we choose one of the two cycle arcs avoiding `d`,
then follow the second arm prefix. -/
theorem RoutedCycleSeparator.rim_reachable_right_avoiding_of_mem_aPrefix
    {a b x r d w : V} {pA : G.Walk a x} {pB : G.Walk b x}
    {C : G.Walk r r} (S : RoutedCycleSeparator pA pB C)
    (hpB : pB.IsPath) (hC : C.IsCycle) (hbC : b ∈ C.support)
    (harms : ∀ q, q ∈ pA.support → q ∈ pB.support → q = x)
    (hdA : d ∈ (pA.takeUntil S.left S.left_mem_aArm).support)
    (hdSide : d ∉ (S.side : Set V))
    (hwC : w ∈ C.support) (hwd : w ≠ d) (hbd : b ≠ d) :
    (G.induce fun q : V ↦
      q ∉ componentCarrier (G := G) {S.left, S.right} S.side ∧ q ≠ d).Reachable
        ⟨w, by
          constructor
          · intro hwSide
            have hwSide' : w ∈ (S.side : Set V) := by
              simpa only [mem_componentCarrier] using hwSide
            by_cases hwL : w = S.left
            · subst w
              exact ComponentCompl.notMem_of_mem hwSide' (by simp)
            by_cases hwR : w = S.right
            · subst w
              exact ComponentCompl.notMem_of_mem hwSide' (by simp)
            exact S.rim_outside_side w hwC hwL hwR hwSide'
          · exact hwd⟩
        ⟨S.right, by
          constructor
          · intro hr
            exact ComponentCompl.notMem_of_mem
              (mem_componentCarrier.mp hr) (by simp)
          · intro hrd
            subst d
            have hrB : S.right ∈ pB.support :=
              pB.support_takeUntil_subset_support S.right_mem_bArm
                (pB.takeUntil S.right S.right_mem_bArm).end_mem_support
            have hrA : S.right ∈ pA.support := by
              exact pA.support_takeUntil_subset_support S.left_mem_aArm hdA
            exact S.right_ne_terminal (harms S.right hrA hrB)⟩ := by
  have hdB : d ∉ (pB.takeUntil S.right S.right_mem_bArm).support := by
    intro hdB
    have hdPA : d ∈ pA.support :=
      pA.support_takeUntil_subset_support S.left_mem_aArm hdA
    have hdPB : d ∈ pB.support :=
      pB.support_takeUntil_subset_support S.right_mem_bArm hdB
    have hdx : d = x := harms d hdPA hdPB
    exact hdSide (hdx ▸ S.x_mem_side)
  obtain ⟨q, hqC, hdq⟩ : ∃ q : G.Walk w b,
      (∀ v, v ∈ q.support → v ∈ C.support) ∧ d ∉ q.support := by
    by_cases hwb : w = b
    · subst w
      exact ⟨Walk.nil, by simp [hbC], by simpa using (Ne.symm hbd)⟩
    · obtain ⟨A⟩ := exists_cycleArcPair hC hwC hbC hwb
      by_cases hdFirst : d ∈ A.first.support
      · have hdSecond : d ∉ A.second.support := by
          intro hdSecond
          rcases A.meet_only_ends d hdFirst hdSecond with hdw | hdb
          · exact hwd hdw.symm
          · exact hbd hdb.symm
        exact ⟨A.second, A.second_subset, hdSecond⟩
      · exact ⟨A.first, A.first_subset, hdFirst⟩
  let p := q.append (pB.takeUntil S.right S.right_mem_bArm)
  have hout : ∀ v ∈ p.support,
      v ∉ componentCarrier (G := G) {S.left, S.right} S.side ∧ v ≠ d := by
    intro v hv
    have hvCases : v ∈ q.support ∨
        v ∈ (pB.takeUntil S.right S.right_mem_bArm).support := by
      simpa only [p, Walk.mem_support_append_iff] using hv
    constructor
    · intro hvCarrier
      have hvSide : v ∈ (S.side : Set V) := by
        simpa only [mem_componentCarrier] using hvCarrier
      rcases hvCases with hvQ | hvB
      · have hvC := hqC v hvQ
        by_cases hvL : v = S.left
        · subst v
          exact ComponentCompl.notMem_of_mem hvSide (by simp)
        by_cases hvR : v = S.right
        · subst v
          exact ComponentCompl.notMem_of_mem hvSide (by simp)
        exact S.rim_outside_side v hvC hvL hvR hvSide
      · exact S.bPrefix_outside_side hpB hbC harms v hvB hvSide
    · intro hvd
      subst v
      exact hvCases.elim hdq hdB
  exact (p.induce _ hout).reachable

/-- Maximality rules out a cutvertex on the first arm prefix.  If deleting
such a vertex `d` separated the old left and right boundary vertices in the
complement of the terminal component, then the component of the terminal
after deleting `{d,right}` would strictly contain the old component (it
also contains `left`).  The preceding rim lemma shows that this new
component is still disjoint from the rim, so it is a larger routed
separator. -/
theorem RoutedCycleSeparator.boundary_reachable_avoiding_of_maximal_mem_aPrefix
    {a b x r d : V} {pA : G.Walk a x} {pB : G.Walk b x}
    {C : G.Walk r r} (S : RoutedCycleSeparator pA pB C)
    (hmax : S.IsMaximal) (hpB : pB.IsPath)
    (hC : C.IsCycle) (hbC : b ∈ C.support)
    (harms : ∀ q, q ∈ pA.support → q ∈ pB.support → q = x)
    (hdelete : ∀ v : V, (G.induce fun w : V ↦ w ≠ v).Connected)
    (hdA : d ∈ (pA.takeUntil S.left S.left_mem_aArm).support)
    (hdSide : d ∉ (S.side : Set V))
    (hdLeft : d ≠ S.left) :
    (G.induce fun q : V ↦
      q ∉ componentCarrier (G := G) {S.left, S.right} S.side ∧ q ≠ d).Reachable
        ⟨S.left, by
          constructor
          · intro hl
            exact ComponentCompl.notMem_of_mem
              (mem_componentCarrier.mp hl) (by simp)
          · exact Ne.symm hdLeft⟩
        ⟨S.right, by
          constructor
          · intro hr
            exact ComponentCompl.notMem_of_mem
              (mem_componentCarrier.mp hr) (by simp)
          · intro hrd
            subst d
            have hrA : S.right ∈ pA.support :=
              pA.support_takeUntil_subset_support S.left_mem_aArm hdA
            exact S.right_ne_terminal
              (harms S.right hrA S.right_mem_bArm)⟩ := by
  classical
  by_contra hnot
  have hdRight : d ≠ S.right := by
    intro h
    subst d
    have hrA : S.right ∈ pA.support :=
      pA.support_takeUntil_subset_support S.left_mem_aArm hdA
    exact S.right_ne_terminal (harms S.right hrA S.right_mem_bArm)
  have hdx : d ≠ x := by
    intro h
    subst d
    exact hdSide S.x_mem_side
  have hbd : b ≠ d := by
    intro h
    subst d
    have hbA : b ∈ pA.support :=
      pA.support_takeUntil_subset_support S.left_mem_aArm hdA
    have hbx : b = x := harms b hbA pB.start_mem_support
    exact hdSide (hbx ▸ S.x_mem_side)
  have hxNew : x ∉ (({d, S.right} : Finset V) : Set V) := by
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton,
      not_or]
    exact ⟨hdx.symm, S.x_ne_right⟩
  let D : G.ComponentCompl (({d, S.right} : Finset V) : Set V) :=
    G.componentComplMk hxNew
  have hxD : x ∈ (D : Set V) := by
    exact ⟨hxNew, rfl⟩
  have hdisOldNew : Disjoint (S.side : Set V)
      (({d, S.right} : Finset V) : Set V) := by
    rw [Set.disjoint_left]
    intro v hvSide hvPair
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hvPair
    rcases hvPair with rfl | rfl
    · exact hdSide hvSide
    · exact ComponentCompl.notMem_of_mem hvSide (by simp)
  have hsub : (S.side : Set V) ⊆ (D : Set V) :=
    ComponentCompl.subset_of_disjoint_of_shared S.side D hdisOldNew
      S.x_mem_side hxD
  obtain ⟨u, huSide, huLeft⟩ :=
    (ComponentCompl.exists_adj_to_each_of_delete_connected
      S.left_ne_right hdelete S.side).1
  have huD : u ∈ (D : Set V) := hsub huSide
  have hleftAvoid : S.left ∉ (({d, S.right} : Finset V) : Set V) := by
    simp [Ne.symm hdLeft, S.left_ne_right]
  have hleftD : S.left ∈ (D : Set V) :=
    ComponentCompl.mem_of_adj u S.left huD hleftAvoid huLeft
  let R : RoutedCycleSeparator pA pB C :=
    { left := d
      right := S.right
      left_ne_right := hdRight
      x_ne_left := hdx.symm
      x_ne_right := S.x_ne_right
      side := D
      x_mem_side := hxD
      rim_outside_side := by
        intro w hwC hwd hwRight hwD
        have hwOldOutside :
            w ∉ componentCarrier (G := G) {S.left, S.right} S.side := by
          intro hwCarrier
          have hwSide : w ∈ (S.side : Set V) := by
            simpa only [mem_componentCarrier] using hwCarrier
          by_cases hwLeft : w = S.left
          · subst w
            exact ComponentCompl.notMem_of_mem hwSide (by simp)
          exact S.rim_outside_side w hwC hwLeft hwRight hwSide
        have hleftOldOutside :
            S.left ∉ componentCarrier (G := G) {S.left, S.right} S.side := by
          intro h
          exact ComponentCompl.notMem_of_mem
            (mem_componentCarrier.mp h) (by simp)
        have hreachPair :
            (G.induce ((({d, S.right} : Finset V) : Set V))ᶜ).Reachable
              ⟨S.left, hleftAvoid⟩
              ⟨w, by simpa [hwd, hwRight]⟩ := by
          rw [← ConnectedComponent.eq]
          exact hleftD.2.trans hwD.2.symm
        have hreachNew :
            (G.induce fun q : V ↦ q ≠ d ∧ q ≠ S.right).Reachable
              ⟨S.left, Ne.symm hdLeft, S.left_ne_right⟩
              ⟨w, hwd, hwRight⟩ := by
          let e : {q : V //
                q ∈ ((({d, S.right} : Finset V) : Set V))ᶜ} ≃
              {q : V // q ≠ d ∧ q ≠ S.right} :=
            { toFun := fun q ↦ ⟨q.1, by
                simpa only [Set.mem_compl_iff, Finset.mem_coe,
                  Finset.mem_insert, Finset.mem_singleton, not_or] using q.2⟩
              invFun := fun q ↦ ⟨q.1, by
                simpa only [Set.mem_compl_iff, Finset.mem_coe,
                  Finset.mem_insert, Finset.mem_singleton, not_or] using q.2⟩
              left_inv := by intro q; rfl
              right_inv := by intro q; rfl }
          let gi : G.induce (((({d, S.right} : Finset V) : Set V))ᶜ) ≃g
              G.induce (fun q : V ↦ q ≠ d ∧ q ≠ S.right) :=
            { toEquiv := e
              map_rel_iff' := by intro u v; rfl }
          have h := hreachPair.map gi.toHom
          convert h using 1 <;> apply Subtype.ext <;> rfl
        have hleftW :=
          ComponentCompl.reachable_compl_component_of_reachable_avoiding_right
            S.side (Ne.symm hdLeft)
            hleftOldOutside (Ne.symm hdLeft) S.left_ne_right
            hwOldOutside hwd hwRight hreachNew
        have hwRightReach :=
          S.rim_reachable_right_avoiding_of_mem_aPrefix hpB hC hbC
            harms hdA hdSide hwC hwd hbd
        exact hnot (hleftW.trans hwRightReach)
      left_mem_aArm :=
        pA.support_takeUntil_subset_support S.left_mem_aArm hdA
      left_ne_terminal := hdx
      right_mem_bArm := S.right_mem_bArm
      right_ne_terminal := S.right_ne_terminal }
  have hstrict :
      componentCarrier (G := G) {S.left, S.right} S.side ⊂
        componentCarrier (G := G) {R.left, R.right} R.side := by
    rw [Finset.ssubset_iff_subset_ne]
    constructor
    · intro v hv
      have hvSide : v ∈ (S.side : Set V) := by
        simpa only [mem_componentCarrier] using hv
      have hvD := hsub hvSide
      simpa only [R, mem_componentCarrier] using hvD
    · intro heq
      have hleftOld : S.left ∈
          componentCarrier (G := G) {S.left, S.right} S.side := by
        rw [heq]
        simpa only [R, mem_componentCarrier] using hleftD
      exact ComponentCompl.notMem_of_mem
        (mem_componentCarrier.mp hleftOld) (by simp)
  exact (hmax.not_ssubset_componentCarrier R) hstrict

/-- Exchange the two routed arms and the two separator vertices. -/
def RoutedCycleSeparator.swap
    {a b x r : V} {pA : G.Walk a x} {pB : G.Walk b x}
    {C : G.Walk r r} (S : RoutedCycleSeparator pA pB C) :
    RoutedCycleSeparator pB pA C := by
  let side' : G.ComponentCompl
      (({S.right, S.left} : Finset V) : Set V) := by
    apply ComponentCompl.transport (C := S.side)
    ext v
    simp [or_comm]
  exact
    { left := S.right
      right := S.left
      left_ne_right := S.left_ne_right.symm
      x_ne_left := S.x_ne_right
      x_ne_right := S.x_ne_left
      side := side'
      x_mem_side := by
        simpa only [side', ComponentCompl.mem_transport] using S.x_mem_side
      rim_outside_side := by
        intro w hwC hwR hwL hwSide
        apply S.rim_outside_side w hwC hwL hwR
        simpa only [side', ComponentCompl.mem_transport] using hwSide
      left_mem_aArm := S.right_mem_bArm
      left_ne_terminal := S.right_ne_terminal
      right_mem_bArm := S.left_mem_aArm
      right_ne_terminal := S.left_ne_terminal }

@[simp] theorem RoutedCycleSeparator.swap_left
    {a b x r : V} {pA : G.Walk a x} {pB : G.Walk b x}
    {C : G.Walk r r} (S : RoutedCycleSeparator pA pB C) :
    S.swap.left = S.right := rfl

@[simp] theorem RoutedCycleSeparator.swap_right
    {a b x r : V} {pA : G.Walk a x} {pB : G.Walk b x}
    {C : G.Walk r r} (S : RoutedCycleSeparator pA pB C) :
    S.swap.right = S.left := rfl

@[simp] theorem RoutedCycleSeparator.mem_swap_side
    {a b x r : V} {pA : G.Walk a x} {pB : G.Walk b x}
    {C : G.Walk r r} (S : RoutedCycleSeparator pA pB C) (v : V) :
    v ∈ (S.swap.side : Set V) ↔ v ∈ (S.side : Set V) := by
  simp only [RoutedCycleSeparator.swap]
  exact ComponentCompl.mem_transport _ S.side v

@[simp] theorem RoutedCycleSeparator.componentCarrier_swap
    {a b x r : V} {pA : G.Walk a x} {pB : G.Walk b x}
    {C : G.Walk r r} (S : RoutedCycleSeparator pA pB C) :
    componentCarrier (G := G) {S.swap.left, S.swap.right} S.swap.side =
      componentCarrier (G := G) {S.left, S.right} S.side := by
  ext v
  simp only [mem_componentCarrier, RoutedCycleSeparator.swap,
    ComponentCompl.mem_transport]

/-- Maximality is invariant under swapping the two arms. -/
theorem RoutedCycleSeparator.IsMaximal.swap
    {a b x r : V} {pA : G.Walk a x} {pB : G.Walk b x}
    {C : G.Walk r r} {S : RoutedCycleSeparator pA pB C}
    (hmax : S.IsMaximal) : S.swap.IsMaximal := by
  intro R
  have h := hmax R.swap
  simpa only [RoutedCycleSeparator.componentCarrier_swap] using h

/-- Symmetric maximality obstruction for a vertex on the second arm
prefix. -/
theorem RoutedCycleSeparator.boundary_reachable_avoiding_of_maximal_mem_bPrefix
    {a b x r d : V} {pA : G.Walk a x} {pB : G.Walk b x}
    {C : G.Walk r r} (S : RoutedCycleSeparator pA pB C)
    (hmax : S.IsMaximal) (hpA : pA.IsPath)
    (hC : C.IsCycle) (haC : a ∈ C.support)
    (harms : ∀ q, q ∈ pA.support → q ∈ pB.support → q = x)
    (hdelete : ∀ v : V, (G.induce fun w : V ↦ w ≠ v).Connected)
    (hdB : d ∈ (pB.takeUntil S.right S.right_mem_bArm).support)
    (hdSide : d ∉ (S.side : Set V))
    (hdRight : d ≠ S.right) :
    (G.induce fun q : V ↦
      q ∉ componentCarrier (G := G) {S.left, S.right} S.side ∧ q ≠ d).Reachable
        ⟨S.left, by
          constructor
          · intro hl
            exact ComponentCompl.notMem_of_mem
              (mem_componentCarrier.mp hl) (by simp)
          · intro hld
            subst d
            have hlB : S.left ∈ pB.support :=
              pB.support_takeUntil_subset_support S.right_mem_bArm hdB
            exact S.left_ne_terminal
              (harms S.left S.left_mem_aArm hlB)⟩
        ⟨S.right, by
          constructor
          · intro hr
            exact ComponentCompl.notMem_of_mem
              (mem_componentCarrier.mp hr) (by simp)
          · exact Ne.symm hdRight⟩ := by
  have hswap := S.swap.boundary_reachable_avoiding_of_maximal_mem_aPrefix
    hmax.swap hpA hC haC
    (fun q hqB hqA ↦ harms q hqA hqB)
    hdelete hdB (by
      intro hd
      exact hdSide ((RoutedCycleSeparator.mem_swap_side S d).mp hd))
    hdRight
  let X₁ : Set V :=
    componentCarrier (G := G) {S.swap.left, S.swap.right} S.swap.side
  let X₂ : Set V :=
    componentCarrier (G := G) {S.left, S.right} S.side
  have hX : X₁ = X₂ := by
    exact congrArg (fun K : Finset V ↦ (K : Set V))
      S.componentCarrier_swap
  let e : {q : V // q ∉ X₁ ∧ q ≠ d} ≃ {q : V // q ∉ X₂ ∧ q ≠ d} :=
    { toFun := fun q ↦ ⟨q.1, by
          constructor
          · simpa only [← hX] using q.2.1
          · exact q.2.2⟩
      invFun := fun q ↦ ⟨q.1, by
          constructor
          · simpa only [hX] using q.2.1
          · exact q.2.2⟩
      left_inv := by intro q; rfl
      right_inv := by intro q; rfl }
  let gi : G.induce (fun q : V ↦ q ∉ X₁ ∧ q ≠ d) ≃g
      G.induce (fun q : V ↦ q ∉ X₂ ∧ q ≠ d) :=
    { toEquiv := e
      map_rel_iff' := by intro u v; rfl }
  have h := hswap.symm.map gi.toHom
  change (G.induce fun q : V ↦ q ∉ X₂ ∧ q ≠ d).Reachable _ _
  convert h using 1
  · apply Subtype.ext
    change S.left = S.swap.right
    exact S.swap_right.symm
  · apply Subtype.ext
    change S.right = S.swap.left
    exact S.swap_left.symm

/-- Full one-vertex-deletion bypass for a maximal routed separator.  Two
internally disjoint rim routes give two canonical outer bypasses.  If one
avoids `d`, use it.  If both meet `d`, the common-bypass lemma puts `d` on
one of the arm prefixes, where maximality supplies the desired route. -/
theorem RoutedCycleSeparator.boundary_reachable_avoiding_of_maximal
    {a b x r d : V} {pA : G.Walk a x} {pB : G.Walk b x}
    {C : G.Walk r r} (S : RoutedCycleSeparator pA pB C)
    (hmax : S.IsMaximal) (hpA : pA.IsPath) (hpB : pB.IsPath)
    (hC : C.IsCycle) (haC : a ∈ C.support) (hbC : b ∈ C.support)
    (harms : ∀ q, q ∈ pA.support → q ∈ pB.support → q = x)
    (hdelete : ∀ v : V, (G.induce fun w : V ↦ w ≠ v).Connected)
    (q₁ q₂ : G.Walk a b)
    (hq₁C : ∀ w, w ∈ q₁.support → w ∈ C.support)
    (hq₂C : ∀ w, w ∈ q₂.support → w ∈ C.support)
    (hmeet : ∀ w, w ∈ q₁.support → w ∈ q₂.support →
      w = a ∨ w = b)
    (hdSide : d ∉ (S.side : Set V))
    (hdLeft : d ≠ S.left) (hdRight : d ≠ S.right) :
    (G.induce fun q : V ↦
      q ∉ componentCarrier (G := G) {S.left, S.right} S.side ∧ q ≠ d).Reachable
        ⟨S.left, by
          constructor
          · intro hl
            exact ComponentCompl.notMem_of_mem
              (mem_componentCarrier.mp hl) (by simp)
          · exact Ne.symm hdLeft⟩
        ⟨S.right, by
          constructor
          · intro hr
            exact ComponentCompl.notMem_of_mem
              (mem_componentCarrier.mp hr) (by simp)
          · exact Ne.symm hdRight⟩ := by
  have direct (q : G.Walk a b)
      (hqC : ∀ w, w ∈ q.support → w ∈ C.support)
      (hdq : d ∉ (S.outerBypass q).support) :
      (G.induce fun q : V ↦
        q ∉ componentCarrier (G := G) {S.left, S.right} S.side ∧ q ≠ d).Reachable
          ⟨S.left, by
            constructor
            · intro hl
              exact ComponentCompl.notMem_of_mem
                (mem_componentCarrier.mp hl) (by simp)
            · exact Ne.symm hdLeft⟩
          ⟨S.right, by
            constructor
            · intro hr
              exact ComponentCompl.notMem_of_mem
                (mem_componentCarrier.mp hr) (by simp)
            · exact Ne.symm hdRight⟩ := by
    let p := S.outerBypass q
    have hout : ∀ w ∈ p.support,
        w ∉ componentCarrier (G := G) {S.left, S.right} S.side ∧ w ≠ d := by
      intro w hw
      constructor
      · intro hwCarrier
        exact S.outerBypass_outside_side hpA hpB haC hbC harms q hqC w hw
          (by simpa only [mem_componentCarrier] using hwCarrier)
      · exact fun h ↦ hdq (h ▸ hw)
    exact (p.induce _ hout).reachable
  by_cases hd₁ : d ∈ (S.outerBypass q₁).support
  · by_cases hd₂ : d ∈ (S.outerBypass q₂).support
    · rcases S.mem_prefix_of_mem_two_outerBypasses q₁ q₂ hmeet hd₁ hd₂ with
        hdA | hdB
      · exact S.boundary_reachable_avoiding_of_maximal_mem_aPrefix
          hmax hpB hC hbC harms hdelete hdA hdSide hdLeft
      · exact S.boundary_reachable_avoiding_of_maximal_mem_bPrefix
          hmax hpA hC haC harms hdelete hdB hdSide hdRight
    · exact direct q₂ hq₂C hd₂
  · exact direct q₁ hq₁C hd₁

/-! Elementary separator/component coercion lemmas are kept in the root
namespace so dot notation remains available throughout the maximal-triple
development. -/

theorem VertexCycleSeparator.left_not_mem_componentCarrier
    {r x : V} {C : G.Walk r r} (S : VertexCycleSeparator C x) :
    S.left ∉ componentCarrier (G := G) {S.left, S.right} S.side := by
  intro h
  exact ComponentCompl.notMem_of_mem (mem_componentCarrier.mp h) (by simp)

theorem VertexCycleSeparator.right_not_mem_componentCarrier
    {r x : V} {C : G.Walk r r} (S : VertexCycleSeparator C x) :
    S.right ∉ componentCarrier (G := G) {S.left, S.right} S.side := by
  intro h
  exact ComponentCompl.notMem_of_mem (mem_componentCarrier.mp h) (by simp)

/-- A replacement side containing the old side and its old left boundary
strictly enlarges the terminal component, contradicting maximality. -/
theorem RoutedCycleSeparator.IsMaximal.not_replacement_of_subset_of_left_mem
    {a b x r : V} {pA : G.Walk a x} {pB : G.Walk b x}
    {C : G.Walk r r} (S : RoutedCycleSeparator pA pB C)
    (hmax : S.IsMaximal) (R : RoutedCycleSeparator pA pB C)
    (hsub : (S.side : Set V) ⊆ (R.side : Set V))
    (hleft : S.left ∈ (R.side : Set V)) : False := by
  apply (hmax.not_ssubset_componentCarrier R)
  rw [Finset.ssubset_iff_subset_ne]
  constructor
  · intro v hv
    have hvSide : v ∈ (S.side : Set V) := by
      simpa only [mem_componentCarrier] using hv
    simpa only [mem_componentCarrier] using hsub hvSide
  · intro heq
    have hold : S.left ∈
        componentCarrier (G := G) {S.left, S.right} S.side := by
      rw [heq]
      simpa only [mem_componentCarrier] using hleft
    exact S.left_not_mem_componentCarrier hold

/-- Right-boundary version of the preceding replacement contradiction. -/
theorem RoutedCycleSeparator.IsMaximal.not_replacement_of_subset_of_right_mem
    {a b x r : V} {pA : G.Walk a x} {pB : G.Walk b x}
    {C : G.Walk r r} (S : RoutedCycleSeparator pA pB C)
    (hmax : S.IsMaximal) (R : RoutedCycleSeparator pA pB C)
    (hsub : (S.side : Set V) ⊆ (R.side : Set V))
    (hright : S.right ∈ (R.side : Set V)) : False := by
  apply (hmax.not_ssubset_componentCarrier R)
  rw [Finset.ssubset_iff_subset_ne]
  constructor
  · intro v hv
    have hvSide : v ∈ (S.side : Set V) := by
      simpa only [mem_componentCarrier] using hv
    simpa only [mem_componentCarrier] using hsub hvSide
  · intro heq
    have hold : S.right ∈
        componentCarrier (G := G) {S.left, S.right} S.side := by
      rw [heq]
      simpa only [mem_componentCarrier] using hright
    exact S.right_not_mem_componentCarrier hold

theorem VertexCycleSeparator.not_mem_componentCarrier_of_mem_rim
    {r x w : V} {C : G.Walk r r} (S : VertexCycleSeparator C x)
    (hwC : w ∈ C.support) :
    w ∉ componentCarrier (G := G) {S.left, S.right} S.side := by
  intro hw
  have hwSide : w ∈ (S.side : Set V) := mem_componentCarrier.mp hw
  by_cases hwL : w = S.left
  · subst w
    exact ComponentCompl.notMem_of_mem hwSide (by simp)
  by_cases hwR : w = S.right
  · subst w
    exact ComponentCompl.notMem_of_mem hwSide (by simp)
  exact S.rim_outside_side w hwC hwL hwR hwSide

/-- Two literal components of the same deleted graph that share a vertex
are equal on vertices.  Root-namespace placement enables dot notation. -/
theorem IsComponentAfterDeleting.mem_of_shared
    {W : Type u} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj]
    {S C D : Finset W} (hC : IsComponentAfterDeleting H S C)
    (hD : IsComponentAfterDeleting H S D) {w v : W}
    (hwC : w ∈ C) (hwD : w ∈ D) (hvD : v ∈ D) : v ∈ C := by
  let wD : {q : W // q ∈ (D : Set W)} := ⟨w, hwD⟩
  let vD : {q : W // q ∈ (D : Set W)} := ⟨v, hvD⟩
  obtain ⟨p⟩ := hD.2.2.1.preconnected wD vD
  have walk_mem : ∀ {a b : {q : W // q ∈ (D : Set W)}}
      (q : (H.induce (D : Set W)).Walk a b), a.1 ∈ C → b.1 ∈ C := by
    intro a b q ha
    induction q with
    | nil => exact ha
    | @cons a b c hab q ih =>
        apply ih
        exact hC.2.2.2 a.1 ha b.1
          (fun hbS ↦ Finset.disjoint_left.mp hD.2.1 b.2 hbS) hab
  exact walk_mem p hwC

/-- A walk which starts in a deletion component and avoids the deleted
set stays in that component. -/
theorem IsComponentAfterDeleting.walk_end_mem
    {W : Type u} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj]
    {S C : Finset W} (hC : IsComponentAfterDeleting H S C)
    {a b : W} (p : H.Walk a b) :
    a ∈ C → (∀ w, w ∈ p.support → w ∉ S) → b ∈ C := by
  induction p with
  | nil =>
      intro ha _
      exact ha
  | @cons a b c hab p ih =>
      intro ha havoid
      apply ih
      · exact hC.2.2.2 a ha b (havoid b (by simp)) hab
      · intro w hw
        exact havoid w (by simp [hw])

/-- A simple path ending at one boundary vertex of a two-vertex deletion,
while avoiding the other boundary vertex, cannot enter a different
component of the deleted graph. -/
theorem IsComponentAfterDeleting.path_to_boundary_avoids_component
    {a b s : V} {C : Finset V}
    (hC : IsComponentAfterDeleting G ({a, b} : Finset V) C)
    (p : G.Walk s b) (hp : p.IsPath) (hsC : s ∉ C)
    (ha : a ∉ p.support) :
    ∀ w, w ∈ p.support → w ∉ C := by
  intro w hw hwC
  have hwb : w ≠ b := by
    intro h
    subst w
    exact Finset.disjoint_left.mp hC.2.1 hwC (by simp)
  have hbPrefix : b ∉ (p.takeUntil w hw).support :=
    Walk.endpoint_notMem_support_takeUntil hp hw hwb.symm
  have hstart : s ∈ C := by
    apply hC.walk_end_mem (p.takeUntil w hw).reverse hwC
    intro v hv
    have hvPrefix : v ∈ (p.takeUntil w hw).support := by
      simpa only [Walk.support_reverse, List.mem_reverse] using hv
    have hva : v ≠ a := by
      intro h
      subst v
      exact ha (p.support_takeUntil_subset_support hw hvPrefix)
    have hvb : v ≠ b := fun h ↦ hbPrefix (h ▸ hvPrefix)
    simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using
      ⟨hva, hvb⟩
  exact hsC hstart

/-- If a simple path starts and ends outside a two-cut component, starts
at neither cut vertex, and can meet either cut vertex only at its terminal
end, then it avoids the component throughout. -/
theorem IsComponentAfterDeleting.path_avoids_of_boundary_only_at_end
    {a b s t : V} {C : Finset V}
    (hC : IsComponentAfterDeleting G ({a, b} : Finset V) C)
    (hab : a ≠ b) (p : G.Walk s t) (hp : p.IsPath)
    (hsC : s ∉ C) (htC : t ∉ C)
    (hsA : s ≠ a) (hsB : s ≠ b)
    (haOnly : a ∈ p.support → a = t)
    (hbOnly : b ∈ p.support → b = t) :
    ∀ w, w ∈ p.support → w ∉ C := by
  by_cases hta : t = a
  · subst t
    have hCswap : IsComponentAfterDeleting G ({b, a} : Finset V) C := by
      rw [Finset.pair_comm b a]
      exact hC
    have hbAvoid : b ∉ p.support := by
      intro hb
      exact hab (hbOnly hb).symm
    exact hCswap.path_to_boundary_avoids_component p hp hsC hbAvoid
  by_cases htb : t = b
  · subst t
    have haAvoid : a ∉ p.support := by
      intro ha
      exact hab (haOnly ha)
    exact hC.path_to_boundary_avoids_component p hp hsC haAvoid
  · intro w hw hwC
    have hsMem : s ∈ C := by
      apply hC.walk_end_mem (p.takeUntil w hw).reverse hwC
      intro v hv
      have hvPrefix : v ∈ (p.takeUntil w hw).support := by
        simpa only [Walk.support_reverse, List.mem_reverse] using hv
      have hvP : v ∈ p.support :=
        p.support_takeUntil_subset_support hw hvPrefix
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      constructor
      · intro hva
        subst v
        exact hta (haOnly hvP).symm
      · intro hvb
        subst v
        exact htb (hbOnly hvP).symm
    exact hsC hsMem

/-- More generally, a walk starting outside a deletion component and
avoiding every deleted vertex cannot enter that component. -/
theorem IsComponentAfterDeleting.walk_avoids_component
    {S C : Finset V} (hC : IsComponentAfterDeleting G S C)
    {s t : V} (p : G.Walk s t) (hsC : s ∉ C)
    (havoid : ∀ w, w ∈ p.support → w ∉ S) :
    ∀ w, w ∈ p.support → w ∉ C := by
  intro w hw hwC
  have hsMem : s ∈ C := by
    apply hC.walk_end_mem (p.takeUntil w hw).reverse hwC
    intro v hv
    have hvPrefix : v ∈ (p.takeUntil w hw).support := by
      simpa only [Walk.support_reverse, List.mem_reverse] using hv
    exact havoid v (p.support_takeUntil_subset_support hw hvPrefix)
  exact hsC hsMem

/-- A simple path whose two ends lie outside a component of a one-vertex
deletion cannot enter that component.  Otherwise the deleted vertex occurs
on both sides of the first displayed component vertex, contradicting
simplicity. -/
theorem IsComponentAfterDeleting.path_avoids_singleton_component
    {W : Type u} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj]
    {d s t : W} {C : Finset W}
    (hC : IsComponentAfterDeleting H ({d} : Finset W) C)
    (p : H.Walk s t) (hp : p.IsPath) (hsC : s ∉ C) (htC : t ∉ C) :
    ∀ w, w ∈ p.support → w ∉ C := by
  intro w hw hwC
  have hdPrefix : d ∈ (p.takeUntil w hw).support := by
    by_contra hd
    apply hsC
    apply hC.walk_end_mem (p.takeUntil w hw).reverse hwC
    intro v hv
    have hvPrefix : v ∈ (p.takeUntil w hw).support := by
      simpa only [Walk.support_reverse, List.mem_reverse] using hv
    simpa only [Finset.mem_singleton] using
      (fun hvd : v = d ↦ hd (hvd ▸ hvPrefix))
  have hdSuffix : d ∈ (p.dropUntil w hw).reverse.support := by
    have hdDrop : d ∈ (p.dropUntil w hw).support := by
      by_contra hd
      apply htC
      apply hC.walk_end_mem (p.dropUntil w hw) hwC
      intro v hv
      simpa only [Finset.mem_singleton] using
        (fun hvd : v = d ↦ hd (hvd ▸ hv))
    simpa only [Walk.support_reverse, List.mem_reverse] using hdDrop
  have hdw := Walk.IsPath.takeUntil_inter_reverse_dropUntil_only
    hp hw d hdPrefix hdSuffix
  have hdC : d ∈ C := by simpa only [hdw] using hwC
  exact Finset.disjoint_left.mp hC.2.1 hdC (by simp)

/-- Two vertices which see the same literal deletion component can be
joined through that component.  After erasing repetitions, the resulting
path has no vertices outside the component except its two prescribed
ends.  This is the elementary path extraction used in condition (vii). -/
theorem IsComponentAfterDeleting.exists_path_through_component
    {S D : Finset V} (hD : IsComponentAfterDeleting G S D)
    {a b u v : V} (huD : u ∈ D) (hvD : v ∈ D)
    (hua : G.Adj u a) (hvb : G.Adj v b) :
    ∃ p : G.Walk a b, p.IsPath ∧
      ∀ w, w ∈ p.support → w = a ∨ w = b ∨ w ∈ D := by
  obtain ⟨qD⟩ := hD.2.2.1.preconnected
    (⟨u, huD⟩ : {w : V // w ∈ (D : Set V)})
    (⟨v, hvD⟩ : {w : V // w ∈ (D : Set V)})
  let q₀ := qD.map (SimpleGraph.Embedding.induce (D : Set V)).toHom
  let q : G.Walk u v := q₀.copy rfl rfl
  let au : G.Walk a u := .cons hua.symm .nil
  let vb : G.Walk v b := .cons hvb .nil
  let raw : G.Walk a b := au.append (q.append vb)
  let p : G.Walk a b := raw.toPath
  refine ⟨p, raw.toPath.prop, ?_⟩
  intro w hwp
  have hwraw : w ∈ raw.support := raw.support_toPath_subset_support hwp
  have hwcases : w ∈ au.support ∨ w ∈ q.support ∨ w ∈ vb.support := by
    simpa only [raw, Walk.mem_support_append_iff] using hwraw
  rcases hwcases with hwau | hwq | hwvb
  · have : w = a ∨ w = u := by simpa [au] using hwau
    exact this.elim (fun h ↦ Or.inl h) (fun h ↦ Or.inr (Or.inr (h.symm ▸ huD)))
  · right; right
    change w ∈ (qD.map (SimpleGraph.Embedding.induce (D : Set V)).toHom).support at hwq
    rw [Walk.support_map] at hwq
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hwq
    exact t.2
  · have : w = v ∨ w = b := by simpa [vb] using hwvb
    exact this.elim (fun h ↦ Or.inr (Or.inr (h.symm ▸ hvD)))
      (fun h ↦ Or.inr (Or.inl h))

/-! ## The two-path Menger form used by the final splitter refinement -/

/-- Two explicitly indexed, vertex-disjoint paths from `A` to `B`.
This is AHT Lemma 3.1 with its pairing left unspecified: the two right
ends may occur in either order. -/
structure WMTwoABLinkage {W : Type*} (H : SimpleGraph W) (A B : Set W) where
  left : Fin 2 → W
  right : Fin 2 → W
  path : ∀ i, H.Walk (left i) (right i)
  left_mem : ∀ i, left i ∈ A
  right_mem : ∀ i, right i ∈ B
  isPath : ∀ i, (path i).IsPath
  disjoint : Pairwise fun i j ↦
    Disjoint {v | v ∈ (path i).support} {v | v ∈ (path j).support}

/-- The deletion formulation of vertex two-connectivity used for the
finite connector subgraphs `G_A` and `G_B`. -/
def AHTVertexTwoConnected {W : Type*} (H : SimpleGraph W) : Prop :=
  H.Connected ∧ ∀ d : W, (H.induce fun w : W ↦ w ≠ d).Connected

/-- A connected finite graph with at least two displayed vertices and no
cut vertex is vertex-two-connected in the deletion formulation used here. -/
theorem ahtVertexTwoConnected_of_connected_noCut
    {W : Type} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (hH : H.Connected) {u v : W} (huv : u ≠ v)
    (hncut : ∀ d : W, ¬IsCutVertex H d) :
    AHTVertexTwoConnected H := by
  refine ⟨hH, ?_⟩
  intro d
  have hpre : (deleteVertex H d).Preconnected := by
    by_contra h
    exact hncut d h
  refine { preconnected := hpre, nonempty := ?_ }
  by_cases hdu : d = u
  · refine ⟨⟨v, ?_⟩⟩
    intro hvd
    exact huv (hdu.symm.trans hvd.symm)
  · exact ⟨⟨u, Ne.symm hdu⟩⟩

/-- A path in a two-connected ambient subgraph avoiding a prescribed third
vertex, mapped back to the original graph. -/
theorem exists_subgraph_path_avoiding
    (H : G.Subgraph) (h2 : AHTVertexTwoConnected H.coe)
    {u v d : H.verts} (hud : u ≠ d) (hvd : v ≠ d) :
    ∃ p : G.Walk u.1 v.1, p.IsPath ∧ d.1 ∉ p.support ∧
      ∀ w, w ∈ p.support → w ∈ H.verts := by
  let u' : {w : H.verts // w ≠ d} := ⟨u, hud⟩
  let v' : {w : H.verts // w ≠ d} := ⟨v, hvd⟩
  obtain ⟨q, hq⟩ := (h2.2 d u' v').exists_isPath
  let inc := SimpleGraph.Embedding.induce
    (G := H.coe) (s := fun w : H.verts ↦ w ≠ d)
  let qH : H.coe.Walk u v :=
    (q.map inc.toHom).copy rfl rfl
  let p : G.Walk u.1 v.1 := qH.map H.hom
  refine ⟨p, ?_, ?_, ?_⟩
  · have hqH : qH.IsPath := by
      exact (Walk.isPath_copy (q.map inc.toHom) rfl rfl).2
        (hq.map inc.injective)
    exact hqH.map Subgraph.hom_injective
  · intro hd
    change d.1 ∈ (qH.map H.hom).support at hd
    rw [Walk.support_map] at hd
    obtain ⟨w, hw, hwd⟩ := List.mem_map.mp hd
    change w ∈ (q.map inc.toHom).support at hw
    rw [Walk.support_map] at hw
    obtain ⟨t, -, htw⟩ := List.mem_map.mp hw
    apply t.2
    apply Subtype.ext
    change w.1 = d.1 at hwd
    exact (congrArg Subtype.val htw).trans hwd
  · intro w hw
    change w ∈ (qH.map H.hom).support at hw
    rw [Walk.support_map] at hw
    obtain ⟨t, -, rfl⟩ := List.mem_map.mp hw
    exact t.2

/-- In a vertex-two-connected graph, no separator between two genuine
two-element terminal sets has cardinality below two. -/
theorem two_le_ncard_separator_of_vertexTwoConnected
    {W : Type} [Finite W] (H : SimpleGraph W)
    (h2 : AHTVertexTwoConnected H)
    {A B : Set W} {a₀ a₁ b₀ b₁ : W}
    (ha₀ : a₀ ∈ A) (ha₁ : a₁ ∈ A) (ha : a₀ ≠ a₁)
    (hb₀ : b₀ ∈ B) (hb₁ : b₁ ∈ B) (hb : b₀ ≠ b₁)
    (S : Set W) (hS : Erdos599.Countable.Separates H A B S) :
    2 ≤ S.ncard := by
  classical
  by_contra hcard
  have hle : S.ncard ≤ 1 := by omega
  rcases (Set.ncard_le_one_iff_eq (Set.toFinite S)).mp hle with rfl | ⟨d, rfl⟩
  · obtain ⟨p, hp⟩ := (h2.1 a₀ b₀).exists_isPath
    obtain ⟨v, -, hv⟩ := hS a₀ ha₀ b₀ hb₀ p hp
    exact hv
  · let a := if a₀ = d then a₁ else a₀
    let b := if b₀ = d then b₁ else b₀
    have haA : a ∈ A := by
      by_cases h : a₀ = d <;> simp [a, h, ha₀, ha₁]
    have hbB : b ∈ B := by
      by_cases h : b₀ = d <;> simp [b, h, hb₀, hb₁]
    have had : a ≠ d := by
      by_cases h : a₀ = d
      · simpa [a, h] using fun h₁ : a₁ = d ↦ ha (h.trans h₁.symm)
      · simpa [a, h]
    have hbd : b ≠ d := by
      by_cases h : b₀ = d
      · simpa [b, h] using fun h₁ : b₁ = d ↦ hb (h.trans h₁.symm)
      · simpa [b, h]
    obtain ⟨q, hq⟩ :=
      ((h2.2 d) (⟨a, had⟩ : {w : W // w ≠ d}) ⟨b, hbd⟩).exists_isPath
    let inc := SimpleGraph.Embedding.induce
      (G := H) (s := fun w : W ↦ w ≠ d)
    let p : H.Walk a b := q.map inc.toHom
    have hp : p.IsPath := hq.map inc.injective
    obtain ⟨v, hvp, hv⟩ := hS a haA b hbB p hp
    have hvd : v = d := by simpa using hv
    subst v
    change d ∈ (q.map inc.toHom).support at hvp
    rw [Walk.support_map] at hvp
    obtain ⟨w, -, hw⟩ := List.mem_map.mp hvp
    exact w.2 (by simpa [inc] using hw)

/-- Finite vertex Menger specialized to two paths.  Later applications
discharge `hsep` from two-connectivity of the chosen `G_A` or `G_B`. -/
theorem exists_wmTwoABLinkage_of_separator_two_le {W : Type} [Finite W]
    (H : SimpleGraph W) (A B : Set W)
    (hsep : ∀ S, Erdos599.Countable.Separates H A B S → 2 ≤ S.ncard) :
    Nonempty (WMTwoABLinkage H A B) := by
  classical
  have hEM : Erdos599.Countable.HasErdosMengerPair H A B :=
    Erdos599.Countable.hasErdosMengerPair_of_safePathRemoval_of_countable
      Erdos599.Countable.safePathRemoval H A B (Set.toFinite A).countable
  rcases hEM with ⟨ι, left, right, path, S, hleft, hright, hpath,
    hdisjoint, hSsub, horth, hseparates⟩
  have hScard : 2 ≤ S.ncard := hsep S hseparates
  have hSfinite : S.Finite := Set.toFinite S
  let _ : Fintype S := hSfinite.fintype
  have hcard : 2 ≤ Fintype.card S := by
    simpa [Set.fintypeCard_eq_ncard] using hScard
  have htwo : Fintype.card (Fin 2) ≤ Fintype.card S := by
    simpa using hcard
  rcases Function.Embedding.nonempty_of_card_le htwo with ⟨pickS⟩
  choose pickI hpickI using fun i : Fin 2 ↦ hSsub (pickS i).property
  have hpickI_inj : Function.Injective pickI := by
    intro i j hij
    by_contra hne
    have hi : (pickS i : W) ∈ S ∧
        (pickS i : W) ∈ (path (pickI i)).support :=
      ⟨(pickS i).property, hpickI i⟩
    have hj : (pickS j : W) ∈ S ∧
        (pickS j : W) ∈ (path (pickI i)).support := by
      rw [hij]
      exact ⟨(pickS j).property, hpickI j⟩
    have hsEq : (pickS i : W) = pickS j :=
      (horth (pickI i)).unique hi hj
    exact hne (pickS.injective (Subtype.ext hsEq))
  exact ⟨{
    left := fun i ↦ left (pickI i)
    right := fun i ↦ right (pickI i)
    path := fun i ↦ path (pickI i)
    left_mem := fun i ↦ hleft (pickI i)
    right_mem := fun i ↦ hright (pickI i)
    isPath := fun i ↦ hpath (pickI i)
    disjoint := fun i j hij ↦ hdisjoint (hpickI_inj.ne hij) }⟩

/-- AHT Lemma 3.1 in contrapositive form: one existing `A`--`B` path
and the absence of a one-vertex separator force two vertex-disjoint
`A`--`B` paths. -/
theorem exists_wmTwoABLinkage_of_no_singleton_separator
    {W : Type} [Finite W] (H : SimpleGraph W)
    {A B : Set W} {a b : W}
    (ha : a ∈ A) (hb : b ∈ B)
    (p : H.Walk a b) (hp : p.IsPath)
    (hnone : ∀ u : W, ¬Erdos599.Countable.Separates H A B ({u} : Set W)) :
    Nonempty (WMTwoABLinkage H A B) := by
  apply exists_wmTwoABLinkage_of_separator_two_le
  intro S hS
  by_contra hlt
  have hle : S.ncard ≤ 1 := by omega
  rcases (Set.ncard_le_one_iff_eq (Set.toFinite S)).mp hle with
    rfl | ⟨u, rfl⟩
  · obtain ⟨v, -, hv⟩ := hS a ha b hb p hp
    exact hv
  · exact hnone u hS

/-- The explicit two-pair form of the preceding no-singleton-separator
lemma.  The two disjoint paths realize one of the two possible matchings
between the displayed pairs. -/
theorem exists_disjoint_pair_paths_of_no_singleton_separator
    {W : Type} [Finite W] (H : SimpleGraph W)
    {a₀ a₁ b₀ b₁ : W}
    (p₀ : H.Walk a₀ b₀) (hp₀ : p₀.IsPath)
    (hnone : ∀ u : W,
      ¬Erdos599.Countable.Separates H ({a₀, a₁} : Set W)
        ({b₀, b₁} : Set W) ({u} : Set W)) :
    (∃ (p : H.Walk a₀ b₀) (q : H.Walk a₁ b₁),
      p.IsPath ∧ q.IsPath ∧
        Disjoint {v | v ∈ p.support} {v | v ∈ q.support}) ∨
    (∃ (p : H.Walk a₀ b₁) (q : H.Walk a₁ b₀),
      p.IsPath ∧ q.IsPath ∧
        Disjoint {v | v ∈ p.support} {v | v ∈ q.support}) := by
  classical
  obtain ⟨L⟩ := exists_wmTwoABLinkage_of_no_singleton_separator H
    (A := ({a₀, a₁} : Set W)) (B := ({b₀, b₁} : Set W))
    (a := a₀) (b := b₀) (by simp) (by simp) p₀ hp₀ hnone
  have hleft_ne : L.left 0 ≠ L.left 1 := by
    intro h
    have hmem : L.left 0 ∈ (L.path 1).support := by
      rw [h]
      exact (L.path 1).start_mem_support
    exact Set.disjoint_left.mp (L.disjoint (by decide))
      (L.path 0).start_mem_support hmem
  have emit (i j : Fin 2) (hij : i ≠ j)
      (hi : L.left i = a₀) (hj : L.left j = a₁) :
      (∃ (p : H.Walk a₀ b₀) (q : H.Walk a₁ b₁),
        p.IsPath ∧ q.IsPath ∧
          Disjoint {v | v ∈ p.support} {v | v ∈ q.support}) ∨
      (∃ (p : H.Walk a₀ b₁) (q : H.Walk a₁ b₀),
        p.IsPath ∧ q.IsPath ∧
          Disjoint {v | v ∈ p.support} {v | v ∈ q.support}) := by
    have hright_ne : L.right i ≠ L.right j := by
      intro h
      have hmem : L.right i ∈ (L.path j).support := by
        rw [h]
        exact (L.path j).end_mem_support
      exact Set.disjoint_left.mp (L.disjoint hij)
        (L.path i).end_mem_support hmem
    have hri : L.right i = b₀ ∨ L.right i = b₁ := by
      simpa using L.right_mem i
    have hrj : L.right j = b₀ ∨ L.right j = b₁ := by
      simpa using L.right_mem j
    rcases hri with hri | hri
    · have hrj' : L.right j = b₁ :=
        hrj.resolve_left (fun h ↦ hright_ne (hri.trans h.symm))
      let p : H.Walk a₀ b₀ := (L.path i).copy hi hri
      let q : H.Walk a₁ b₁ := (L.path j).copy hj hrj'
      left
      exact ⟨p, q,
        (Walk.isPath_copy _ _ _).mpr (L.isPath i),
        (Walk.isPath_copy _ _ _).mpr (L.isPath j), by
          simpa [p, q, Walk.support_copy] using L.disjoint hij⟩
    · have hrj' : L.right j = b₀ :=
        hrj.resolve_right (fun h ↦ hright_ne (hri.trans h.symm))
      let p : H.Walk a₀ b₁ := (L.path i).copy hi hri
      let q : H.Walk a₁ b₀ := (L.path j).copy hj hrj'
      right
      exact ⟨p, q,
        (Walk.isPath_copy _ _ _).mpr (L.isPath i),
        (Walk.isPath_copy _ _ _).mpr (L.isPath j), by
          simpa [p, q, Walk.support_copy] using L.disjoint hij⟩
  have hleft₀ : L.left 0 = a₀ ∨ L.left 0 = a₁ := by
    simpa using L.left_mem 0
  have hleft₁ : L.left 1 = a₀ ∨ L.left 1 = a₁ := by
    simpa using L.left_mem 1
  rcases hleft₀ with h₀ | h₀ <;> rcases hleft₁ with h₁ | h₁
  · exact (hleft_ne (h₀.trans h₁.symm)).elim
  · exact emit 0 1 (by decide) h₀ h₁
  · exact emit 1 0 (by decide) h₁ h₀
  · exact (hleft_ne (h₀.trans h₁.symm)).elim

/-- AHT Lemma 3.1 in the form used inside either two-connected connector:
two distinct prescribed vertices on each side admit two disjoint paths,
with the matching determined by the paths. -/
theorem exists_wmTwoABLinkage_of_vertexTwoConnected
    {W : Type} [Finite W] (H : SimpleGraph W)
    (h2 : AHTVertexTwoConnected H)
    {A B : Set W} {a₀ a₁ b₀ b₁ : W}
    (ha₀ : a₀ ∈ A) (ha₁ : a₁ ∈ A) (ha : a₀ ≠ a₁)
    (hb₀ : b₀ ∈ B) (hb₁ : b₁ ∈ B) (hb : b₀ ≠ b₁) :
    Nonempty (WMTwoABLinkage H A B) := by
  apply exists_wmTwoABLinkage_of_separator_two_le
  intro S hS
  exact two_le_ncard_separator_of_vertexTwoConnected H h2
    ha₀ ha₁ ha hb₀ hb₁ hb S hS

/-- Explicit two-pair form of AHT Lemma 3.1.  The output records the only
two possible matchings of the prescribed ends, which is the convenient
form for the cycle splices on pp.15--16. -/
theorem exists_disjoint_pair_paths_of_vertexTwoConnected
    {W : Type} [Finite W] (H : SimpleGraph W)
    (h2 : AHTVertexTwoConnected H)
    {a₀ a₁ b₀ b₁ : W} (ha : a₀ ≠ a₁) (hb : b₀ ≠ b₁) :
    (∃ (p : H.Walk a₀ b₀) (q : H.Walk a₁ b₁),
      p.IsPath ∧ q.IsPath ∧
        Disjoint {v | v ∈ p.support} {v | v ∈ q.support}) ∨
    (∃ (p : H.Walk a₀ b₁) (q : H.Walk a₁ b₀),
      p.IsPath ∧ q.IsPath ∧
        Disjoint {v | v ∈ p.support} {v | v ∈ q.support}) := by
  classical
  obtain ⟨L⟩ := exists_wmTwoABLinkage_of_vertexTwoConnected H h2
    (A := ({a₀, a₁} : Set W)) (B := ({b₀, b₁} : Set W))
    (a₀ := a₀) (a₁ := a₁) (b₀ := b₀) (b₁ := b₁)
    (by simp) (by simp) ha (by simp) (by simp) hb
  have hleft_ne : L.left 0 ≠ L.left 1 := by
    intro h
    have hmem : L.left 0 ∈ (L.path 1).support := by
      rw [h]
      exact (L.path 1).start_mem_support
    exact Set.disjoint_left.mp (L.disjoint (by decide))
      (L.path 0).start_mem_support hmem
  have emit (i j : Fin 2) (hij : i ≠ j)
      (hi : L.left i = a₀) (hj : L.left j = a₁) :
      (∃ (p : H.Walk a₀ b₀) (q : H.Walk a₁ b₁),
        p.IsPath ∧ q.IsPath ∧
          Disjoint {v | v ∈ p.support} {v | v ∈ q.support}) ∨
      (∃ (p : H.Walk a₀ b₁) (q : H.Walk a₁ b₀),
        p.IsPath ∧ q.IsPath ∧
          Disjoint {v | v ∈ p.support} {v | v ∈ q.support}) := by
    have hright_ne : L.right i ≠ L.right j := by
      intro h
      have hmem : L.right i ∈ (L.path j).support := by
        rw [h]
        exact (L.path j).end_mem_support
      exact Set.disjoint_left.mp (L.disjoint hij)
        (L.path i).end_mem_support hmem
    have hri : L.right i = b₀ ∨ L.right i = b₁ := by
      simpa using L.right_mem i
    have hrj : L.right j = b₀ ∨ L.right j = b₁ := by
      simpa using L.right_mem j
    rcases hri with hri | hri
    · have hrj' : L.right j = b₁ :=
        hrj.resolve_left (fun h ↦ hright_ne (hri.trans h.symm))
      let p : H.Walk a₀ b₀ := (L.path i).copy hi hri
      let q : H.Walk a₁ b₁ := (L.path j).copy hj hrj'
      left
      exact ⟨p, q,
        (Walk.isPath_copy _ _ _).mpr (L.isPath i),
        (Walk.isPath_copy _ _ _).mpr (L.isPath j), by
          simpa [p, q, Walk.support_copy] using L.disjoint hij⟩
    · have hrj' : L.right j = b₀ :=
        hrj.resolve_right (fun h ↦ hright_ne (hri.trans h.symm))
      let p : H.Walk a₀ b₁ := (L.path i).copy hi hri
      let q : H.Walk a₁ b₀ := (L.path j).copy hj hrj'
      right
      exact ⟨p, q,
        (Walk.isPath_copy _ _ _).mpr (L.isPath i),
        (Walk.isPath_copy _ _ _).mpr (L.isPath j), by
          simpa [p, q, Walk.support_copy] using L.disjoint hij⟩
  have hleft₀ : L.left 0 = a₀ ∨ L.left 0 = a₁ := by
    simpa using L.left_mem 0
  have hleft₁ : L.left 1 = a₀ ∨ L.left 1 = a₁ := by
    simpa using L.left_mem 1
  rcases hleft₀ with h₀ | h₀ <;> rcases hleft₁ with h₁ | h₁
  · exact (hleft_ne (h₀.trans h₁.symm)).elim
  · exact emit 0 1 (by decide) h₀ h₁
  · exact emit 1 0 (by decide) h₁ h₀
  · exact (hleft_ne (h₀.trans h₁.symm)).elim

/-- Map the explicit two-pair linkage in a two-connected subgraph back to
the ambient graph, retaining both disjointness and support containment. -/
theorem exists_ambient_disjoint_pair_paths_of_subgraph_twoConnected
    (H : G.Subgraph) (h2 : AHTVertexTwoConnected H.coe)
    {a₀ a₁ b₀ b₁ : H.verts} (ha : a₀ ≠ a₁) (hb : b₀ ≠ b₁) :
    (∃ (p : G.Walk a₀.1 b₀.1) (q : G.Walk a₁.1 b₁.1),
      p.IsPath ∧ q.IsPath ∧
        Disjoint {v | v ∈ p.support} {v | v ∈ q.support} ∧
        (∀ w, w ∈ p.support → w ∈ H.verts) ∧
        ∀ w, w ∈ q.support → w ∈ H.verts) ∨
    (∃ (p : G.Walk a₀.1 b₁.1) (q : G.Walk a₁.1 b₀.1),
      p.IsPath ∧ q.IsPath ∧
        Disjoint {v | v ∈ p.support} {v | v ∈ q.support} ∧
        (∀ w, w ∈ p.support → w ∈ H.verts) ∧
        ∀ w, w ∈ q.support → w ∈ H.verts) := by
  classical
  have mapSupport {u v : H.verts} (p : H.coe.Walk u v) :
      ∀ w, w ∈ (p.map H.hom).support → w ∈ H.verts := by
    intro w hw
    rw [Walk.support_map] at hw
    obtain ⟨t, -, rfl⟩ := List.mem_map.mp hw
    exact t.2
  have mapDisjoint {u₀ v₀ u₁ v₁ : H.verts}
      (p : H.coe.Walk u₀ v₀) (q : H.coe.Walk u₁ v₁)
      (hdis : Disjoint {w | w ∈ p.support} {w | w ∈ q.support}) :
      Disjoint {w | w ∈ (p.map H.hom).support}
        {w | w ∈ (q.map H.hom).support} := by
    rw [Set.disjoint_left]
    intro w hwp hwq
    rw [Walk.support_map] at hwp hwq
    obtain ⟨u, hu, huw⟩ := List.mem_map.mp hwp
    obtain ⟨v, hv, hvw⟩ := List.mem_map.mp hwq
    have huv : u = v := by
      apply Subtype.ext
      exact huw.trans hvw.symm
    subst v
    exact Set.disjoint_left.mp hdis hu hv
  rcases exists_disjoint_pair_paths_of_vertexTwoConnected H.coe h2 ha hb with
      ⟨p, q, hp, hq, hdis⟩ | ⟨p, q, hp, hq, hdis⟩
  · left
    exact ⟨p.map H.hom, q.map H.hom,
      hp.map Subgraph.hom_injective, hq.map Subgraph.hom_injective,
      mapDisjoint p q hdis, mapSupport p, mapSupport q⟩
  · right
    exact ⟨p.map H.hom, q.map H.hom,
      hp.map Subgraph.hom_injective, hq.map Subgraph.hom_injective,
      mapDisjoint p q hdis, mapSupport p, mapSupport q⟩

/-- Map the explicit no-singleton-separator linkage in a subgraph back to
the ambient graph, retaining disjointness and support containment. -/
theorem exists_ambient_disjoint_pair_paths_of_subgraph_no_singleton_separator
    (H : G.Subgraph) {a₀ a₁ b₀ b₁ : H.verts}
    (p₀ : H.coe.Walk a₀ b₀) (hp₀ : p₀.IsPath)
    (hnone : ∀ u : H.verts,
      ¬Erdos599.Countable.Separates H.coe ({a₀, a₁} : Set H.verts)
        ({b₀, b₁} : Set H.verts) ({u} : Set H.verts)) :
    (∃ (p : G.Walk a₀.1 b₀.1) (q : G.Walk a₁.1 b₁.1),
      p.IsPath ∧ q.IsPath ∧
        Disjoint {v | v ∈ p.support} {v | v ∈ q.support} ∧
        (∀ w, w ∈ p.support → w ∈ H.verts) ∧
        ∀ w, w ∈ q.support → w ∈ H.verts) ∨
    (∃ (p : G.Walk a₀.1 b₁.1) (q : G.Walk a₁.1 b₀.1),
      p.IsPath ∧ q.IsPath ∧
        Disjoint {v | v ∈ p.support} {v | v ∈ q.support} ∧
        (∀ w, w ∈ p.support → w ∈ H.verts) ∧
        ∀ w, w ∈ q.support → w ∈ H.verts) := by
  classical
  have mapSupport {u v : H.verts} (p : H.coe.Walk u v) :
      ∀ w, w ∈ (p.map H.hom).support → w ∈ H.verts := by
    intro w hw
    rw [Walk.support_map] at hw
    obtain ⟨t, -, rfl⟩ := List.mem_map.mp hw
    exact t.2
  have mapDisjoint {u₀ v₀ u₁ v₁ : H.verts}
      (p : H.coe.Walk u₀ v₀) (q : H.coe.Walk u₁ v₁)
      (hdis : Disjoint {w | w ∈ p.support} {w | w ∈ q.support}) :
      Disjoint {w | w ∈ (p.map H.hom).support}
        {w | w ∈ (q.map H.hom).support} := by
    rw [Set.disjoint_left]
    intro w hwp hwq
    rw [Walk.support_map] at hwp hwq
    obtain ⟨u, hu, huw⟩ := List.mem_map.mp hwp
    obtain ⟨v, hv, hvw⟩ := List.mem_map.mp hwq
    have huv : u = v := by
      apply Subtype.ext
      exact huw.trans hvw.symm
    subst v
    exact Set.disjoint_left.mp hdis hu hv
  rcases exists_disjoint_pair_paths_of_no_singleton_separator
      H.coe p₀ hp₀ hnone with
    ⟨p, q, hp, hq, hdis⟩ | ⟨p, q, hp, hq, hdis⟩
  · left
    exact ⟨p.map H.hom, q.map H.hom,
      hp.map Subgraph.hom_injective, hq.map Subgraph.hom_injective,
      mapDisjoint p q hdis, mapSupport p, mapSupport q⟩
  · right
    exact ⟨p.map H.hom, q.map H.hom,
      hp.map Subgraph.hom_injective, hq.map Subgraph.hom_injective,
      mapDisjoint p q hdis, mapSupport p, mapSupport q⟩

/-- The three maximal separators exist unconditionally in the no-common-
cycle branch. -/
theorem exists_watkinsMesnerMaximalTriple
    {x y z : V} (T : WatkinsMesnerK32Source G x y z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hconn : G.Connected)
    (hdelete : ∀ d : V, (G.induce fun w : V ↦ w ≠ d).Connected)
    (hno : ¬HasCycleThroughThree G x y z) :
    Nonempty (WatkinsMesnerMaximalTriple T) := by
  obtain ⟨xSep, hxMax⟩ :=
    T.exists_maximal_xSeparator hxy hxz hyz hconn hdelete hno
  obtain ⟨ySep, hyMax⟩ :=
    T.exists_maximal_ySeparator hxy hxz hyz hconn hdelete hno
  obtain ⟨zSep, hzMax⟩ :=
    T.exists_maximal_zSeparator hxy hxz hyz hconn hdelete hno
  exact ⟨{
    xSep := xSep
    ySep := ySep
    zSep := zSep
    x_maximal := hxMax
    y_maximal := hyMax
    z_maximal := hzMax }⟩

namespace WatkinsMesnerMaximalTriple

variable {x y z : V} {T : WatkinsMesnerK32Source G x y z}
    (M : WatkinsMesnerMaximalTriple T)

/-- A vertex separator of the displayed `x`-rim cannot contain the old
maximal `x`-side together with its old A-boundary vertex.  The arm-routing
lemma orders the two new separator vertices, after which this is exactly
the maximality contradiction.  This is the reusable maximal-`X` half of
the external-path exchange on p.15. -/
theorem false_of_x_vertexCycleSeparator_replacement
    (R : VertexCycleSeparator T.xRim x)
    (hsub : (M.xSep.side : Set V) ⊆ (R.side : Set V))
    (hleft : M.xSep.left ∈ (R.side : Set V)) : False := by
  obtain ⟨Q, hQside⟩ := exists_routedCycleSeparator_of_vertexCycleSeparator
    (T.xRoute_isPath.takeUntil T.x_mem)
    (T.xRoute_isPath.dropUntil T.x_mem).reverse
    T.xRim.start_mem_support
    (by simp [WatkinsMesnerK32Source.xRim])
    (fun w hwA hwB ↦
      Walk.IsPath.takeUntil_inter_reverse_dropUntil_only
        T.xRoute_isPath T.x_mem w hwA hwB) R
  exact M.x_maximal.not_replacement_of_subset_of_left_mem M.xSep Q
    (fun w hw ↦ (hQside w).2 (hsub hw)) ((hQside M.xSep.left).2 hleft)

/-- Any two (possibly equal) vertices on a simple cycle are joined by a
simple path supported on that cycle. -/
theorem exists_path_in_cycleSupport
    {r s t : V} {C : G.Walk r r} (hC : C.IsCycle)
    (hs : s ∈ C.support) (ht : t ∈ C.support) :
    ∃ p : G.Walk s t, p.IsPath ∧
      ∀ w, w ∈ p.support → w ∈ C.support := by
  by_cases hst : s = t
  · subst t
    refine ⟨.nil, by simp, ?_⟩
    intro w hw
    have hws : w = s := by
      simpa only [Walk.support_nil, List.mem_singleton] using hw
    exact hws ▸ hs
  · obtain ⟨A⟩ := exists_cycleArcPair hC hs ht hst
    exact ⟨A.first, A.first_isPath, A.first_subset⟩

/-- Two vertices of a simple cycle can be joined along the cycle while
avoiding any prescribed third vertex. -/
theorem exists_path_in_cycleSupport_avoiding
    {r s t d : V} {C : G.Walk r r} (hC : C.IsCycle)
    (hs : s ∈ C.support) (ht : t ∈ C.support)
    (hds : d ≠ s) (hdt : d ≠ t) :
    ∃ p : G.Walk s t, p.IsPath ∧
      (∀ w, w ∈ p.support → w ∈ C.support) ∧ d ∉ p.support := by
  by_cases hst : s = t
  · subst t
    refine ⟨.nil, by simp, ?_, ?_⟩
    · intro w hw
      have hws : w = s := by
        simpa only [Walk.support_nil, List.mem_singleton] using hw
      exact hws ▸ hs
    · simpa only [Walk.support_nil, List.mem_singleton] using hds
  · obtain ⟨A⟩ := exists_cycleArcPair hC hs ht hst
    by_cases hdFirst : d ∈ A.first.support
    · have hdSecond : d ∉ A.second.support := by
        intro hdSecond
        rcases A.meet_only_ends d hdFirst hdSecond with h | h
        · exact hds h
        · exact hdt h
      exact ⟨A.second, A.second_isPath, A.second_subset, hdSecond⟩
    · exact ⟨A.first, A.first_isPath, A.first_subset, hdFirst⟩

/-- Two forbidden vertices on a simple cycle admit a common avoiding arc,
unless they lie on opposite arcs between the prescribed ends.  The latter
alternative records both complementary arcs with the orientation used in
the two-cut external-path exchange on p.15. -/
theorem exists_cyclePath_avoiding_two_or_opposite_arcs
    {r s t d e : V} {C : G.Walk r r} (hC : C.IsCycle)
    (hs : s ∈ C.support) (ht : t ∈ C.support) (hst : s ≠ t)
    (hds : d ≠ s) (hdt : d ≠ t)
    (hes : e ≠ s) (het : e ≠ t) :
    (∃ p : G.Walk s t, p.IsPath ∧
      (∀ w, w ∈ p.support → w ∈ C.support) ∧
      d ∉ p.support ∧ e ∉ p.support) ∨
    ∃ p q : G.Walk s t,
      p.IsPath ∧ q.IsPath ∧
      (∀ w, w ∈ p.support → w ∈ C.support) ∧
      (∀ w, w ∈ q.support → w ∈ C.support) ∧
      d ∉ p.support ∧ e ∈ p.support ∧
      e ∉ q.support ∧ d ∈ q.support ∧
      ∀ w, w ∈ p.support → w ∈ q.support → w = s ∨ w = t := by
  obtain ⟨A⟩ := exists_cycleArcPair hC hs ht hst
  have outside_other {w : V} (hws : w ≠ s) (hwt : w ≠ t)
      {p q : G.Walk s t}
      (hmeet : ∀ v, v ∈ p.support → v ∈ q.support →
        v = s ∨ v = t)
      (hwp : w ∈ p.support) : w ∉ q.support := by
    intro hwq
    rcases hmeet w hwp hwq with h | h
    · exact hws h
    · exact hwt h
  by_cases hdF : d ∈ A.first.support
  · have hdS : d ∉ A.second.support :=
      outside_other hds hdt A.meet_only_ends hdF
    by_cases heF : e ∈ A.first.support
    · have heS : e ∉ A.second.support :=
        outside_other hes het A.meet_only_ends heF
      exact Or.inl ⟨A.second, A.second_isPath, A.second_subset,
        hdS, heS⟩
    · by_cases heS : e ∈ A.second.support
      · exact Or.inr ⟨A.second, A.first,
          A.second_isPath, A.first_isPath,
          A.second_subset, A.first_subset,
          hdS, heS, heF, hdF,
          fun w hwS hwF ↦ A.meet_only_ends w hwF hwS⟩
      · exact Or.inl ⟨A.second, A.second_isPath, A.second_subset,
          hdS, heS⟩
  · by_cases heF : e ∈ A.first.support
    · have heS : e ∉ A.second.support :=
        outside_other hes het A.meet_only_ends heF
      by_cases hdS : d ∈ A.second.support
      · exact Or.inr ⟨A.first, A.second,
          A.first_isPath, A.second_isPath,
          A.first_subset, A.second_subset,
          hdF, heF, heS, hdS, A.meet_only_ends⟩
      · exact Or.inl ⟨A.second, A.second_isPath, A.second_subset,
          hdS, heS⟩
    · exact Or.inl ⟨A.first, A.first_isPath, A.first_subset,
        hdF, heF⟩

/-- The candidate `A`-side boundary triple. -/
def aSet : Finset V := {M.xSep.left, M.ySep.left, M.zSep.left}

/-- The candidate `B`-side boundary triple. -/
def bSet : Finset V := {M.xSep.right, M.ySep.right, M.zSep.right}

/-- The three terminal-side component carriers. -/
noncomputable def xPart : Finset V :=
  componentCarrier (G := G) {M.xSep.left, M.xSep.right} M.xSep.side

noncomputable def yPart : Finset V :=
  componentCarrier (G := G) {M.ySep.left, M.ySep.right} M.ySep.side

noncomputable def zPart : Finset V :=
  componentCarrier (G := G) {M.zSep.left, M.zSep.right} M.zSep.side

@[simp] theorem x_mem_xPart : x ∈ M.xPart := by
  simpa only [xPart, mem_componentCarrier] using M.xSep.x_mem_side

@[simp] theorem y_mem_yPart : y ∈ M.yPart := by
  simpa only [yPart, mem_componentCarrier] using M.ySep.x_mem_side

@[simp] theorem z_mem_zPart : z ∈ M.zPart := by
  simpa only [zPart, mem_componentCarrier] using M.zSep.x_mem_side

@[simp] theorem xA_mem_aSet : M.xSep.left ∈ M.aSet := by simp [aSet]
@[simp] theorem yA_mem_aSet : M.ySep.left ∈ M.aSet := by simp [aSet]
@[simp] theorem zA_mem_aSet : M.zSep.left ∈ M.aSet := by simp [aSet]
@[simp] theorem xB_mem_bSet : M.xSep.right ∈ M.bSet := by simp [bSet]
@[simp] theorem yB_mem_bSet : M.ySep.right ∈ M.bSet := by simp [bSet]
@[simp] theorem zB_mem_bSet : M.zSep.right ∈ M.bSet := by simp [bSet]

/-- The three canonical attachment-to-attachment paths through the named
terminals. -/
def xTerminalBridge : G.Walk M.xSep.left M.xSep.right :=
  M.xSep.terminalBridge

def yTerminalBridge : G.Walk M.ySep.left M.ySep.right :=
  M.ySep.terminalBridge

def zTerminalBridge : G.Walk M.zSep.left M.zSep.right :=
  M.zSep.terminalBridge

theorem xTerminalBridge_isPath : M.xTerminalBridge.IsPath := by
  apply M.xSep.terminalBridge_isPath
      (T.xRoute_isPath.takeUntil T.x_mem)
      (T.xRoute_isPath.dropUntil T.x_mem).reverse
  exact fun w hwA hwB ↦
    Walk.IsPath.takeUntil_inter_reverse_dropUntil_only
      T.xRoute_isPath T.x_mem w hwA hwB

theorem yTerminalBridge_isPath : M.yTerminalBridge.IsPath := by
  apply M.ySep.terminalBridge_isPath
      (T.yRoute_isPath.takeUntil T.y_mem)
      (T.yRoute_isPath.dropUntil T.y_mem).reverse
  exact fun w hwA hwB ↦
    Walk.IsPath.takeUntil_inter_reverse_dropUntil_only
      T.yRoute_isPath T.y_mem w hwA hwB

theorem zTerminalBridge_isPath : M.zTerminalBridge.IsPath := by
  apply M.zSep.terminalBridge_isPath
      (T.zRoute_isPath.takeUntil T.z_mem)
      (T.zRoute_isPath.dropUntil T.z_mem).reverse
  exact fun w hwA hwB ↦
    Walk.IsPath.takeUntil_inter_reverse_dropUntil_only
      T.zRoute_isPath T.z_mem w hwA hwB

@[simp] theorem x_mem_xTerminalBridge : x ∈ M.xTerminalBridge.support :=
  M.xSep.terminal_mem_terminalBridge

@[simp] theorem y_mem_yTerminalBridge : y ∈ M.yTerminalBridge.support :=
  M.ySep.terminal_mem_terminalBridge

@[simp] theorem z_mem_zTerminalBridge : z ∈ M.zTerminalBridge.support :=
  M.zSep.terminal_mem_terminalBridge

theorem xTerminalBridge_support {w : V}
    (hw : w ∈ M.xTerminalBridge.support) :
    w = M.xSep.left ∨ w = M.xSep.right ∨ w ∈ M.xPart := by
  have h := M.xSep.terminalBridge_support
      (T.xRoute_isPath.takeUntil T.x_mem)
      (T.xRoute_isPath.dropUntil T.x_mem).reverse
      (fun v hvA hvB ↦
        Walk.IsPath.takeUntil_inter_reverse_dropUntil_only
          T.xRoute_isPath T.x_mem v hvA hvB) hw
  simpa only [xPart, mem_componentCarrier] using h

theorem yTerminalBridge_support {w : V}
    (hw : w ∈ M.yTerminalBridge.support) :
    w = M.ySep.left ∨ w = M.ySep.right ∨ w ∈ M.yPart := by
  have h := M.ySep.terminalBridge_support
      (T.yRoute_isPath.takeUntil T.y_mem)
      (T.yRoute_isPath.dropUntil T.y_mem).reverse
      (fun v hvA hvB ↦
        Walk.IsPath.takeUntil_inter_reverse_dropUntil_only
          T.yRoute_isPath T.y_mem v hvA hvB) hw
  simpa only [yPart, mem_componentCarrier] using h

theorem zTerminalBridge_support {w : V}
    (hw : w ∈ M.zTerminalBridge.support) :
    w = M.zSep.left ∨ w = M.zSep.right ∨ w ∈ M.zPart := by
  have h := M.zSep.terminalBridge_support
      (T.zRoute_isPath.takeUntil T.z_mem)
      (T.zRoute_isPath.dropUntil T.z_mem).reverse
      (fun v hvA hvB ↦
        Walk.IsPath.takeUntil_inter_reverse_dropUntil_only
          T.zRoute_isPath T.z_mem v hvA hvB) hw
  simpa only [zPart, mem_componentCarrier] using h

/-! The separator component is disjoint from its two deleted boundary
vertices and from every vertex of the displayed opposite rim.  These are
the elementary component facts behind conditions (i)--(iv) in the source
proof. -/

private theorem xRim_mem_of_yRoute_mem {w : V}
    (hw : w ∈ T.yRoute.support) : w ∈ T.xRim.support := by
  simp only [WatkinsMesnerK32Source.xRim, Walk.mem_support_append_iff]
  exact Or.inl hw

private theorem xRim_mem_of_zRoute_mem {w : V}
    (hw : w ∈ T.zRoute.support) : w ∈ T.xRim.support := by
  simp only [WatkinsMesnerK32Source.xRim, Walk.mem_support_append_iff,
    Walk.support_reverse, List.mem_reverse]
  exact Or.inr hw

private theorem yRim_mem_of_xRoute_mem {w : V}
    (hw : w ∈ T.xRoute.support) : w ∈ T.yRim.support := by
  simp only [WatkinsMesnerK32Source.yRim, Walk.mem_support_append_iff]
  exact Or.inl hw

private theorem yRim_mem_of_zRoute_mem {w : V}
    (hw : w ∈ T.zRoute.support) : w ∈ T.yRim.support := by
  simp only [WatkinsMesnerK32Source.yRim, Walk.mem_support_append_iff,
    Walk.support_reverse, List.mem_reverse]
  exact Or.inr hw

private theorem zRim_mem_of_xRoute_mem {w : V}
    (hw : w ∈ T.xRoute.support) : w ∈ T.zRim.support := by
  simp only [WatkinsMesnerK32Source.zRim, Walk.mem_support_append_iff]
  exact Or.inl hw

private theorem zRim_mem_of_yRoute_mem {w : V}
    (hw : w ∈ T.yRoute.support) : w ∈ T.zRim.support := by
  simp only [WatkinsMesnerK32Source.zRim, Walk.mem_support_append_iff,
    Walk.support_reverse, List.mem_reverse]
  exact Or.inr hw

theorem xPart_disjoint_aSet : Disjoint M.xPart M.aSet := by
  rw [Finset.disjoint_left]
  intro w hwX hwA
  have hwCases : w = M.xSep.left ∨ w = M.ySep.left ∨
      w = M.zSep.left := by simpa [aSet] using hwA
  rcases hwCases with rfl | rfl | rfl
  · exact M.xSep.left_not_mem_componentCarrier hwX
  · apply M.xSep.not_mem_componentCarrier_of_mem_rim
      (xRim_mem_of_yRoute_mem
        (T.yRoute.support_takeUntil_subset_support T.y_mem
          M.ySep.left_mem_aArm)) hwX
  · apply M.xSep.not_mem_componentCarrier_of_mem_rim
      (xRim_mem_of_zRoute_mem
        (T.zRoute.support_takeUntil_subset_support T.z_mem
          M.zSep.left_mem_aArm)) hwX

theorem xPart_disjoint_bSet : Disjoint M.xPart M.bSet := by
  rw [Finset.disjoint_left]
  intro w hwX hwB
  have hwCases : w = M.xSep.right ∨ w = M.ySep.right ∨
      w = M.zSep.right := by simpa [bSet] using hwB
  rcases hwCases with rfl | rfl | rfl
  · exact M.xSep.right_not_mem_componentCarrier hwX
  · apply M.xSep.not_mem_componentCarrier_of_mem_rim
      (xRim_mem_of_yRoute_mem
        (T.yRoute.support_dropUntil_subset_support T.y_mem (by
          simpa only [WatkinsMesnerK32Source.yArmB, Walk.support_reverse,
            List.mem_reverse] using M.ySep.right_mem_bArm))) hwX
  · apply M.xSep.not_mem_componentCarrier_of_mem_rim
      (xRim_mem_of_zRoute_mem
        (T.zRoute.support_dropUntil_subset_support T.z_mem (by
          simpa only [WatkinsMesnerK32Source.zArmB, Walk.support_reverse,
            List.mem_reverse] using M.zSep.right_mem_bArm))) hwX

theorem yPart_disjoint_aSet : Disjoint M.yPart M.aSet := by
  rw [Finset.disjoint_left]
  intro w hwY hwA
  have hwCases : w = M.xSep.left ∨ w = M.ySep.left ∨
      w = M.zSep.left := by simpa [aSet] using hwA
  rcases hwCases with rfl | rfl | rfl
  · apply M.ySep.not_mem_componentCarrier_of_mem_rim
      (yRim_mem_of_xRoute_mem
        (T.xRoute.support_takeUntil_subset_support T.x_mem
          M.xSep.left_mem_aArm)) hwY
  · exact M.ySep.left_not_mem_componentCarrier hwY
  · apply M.ySep.not_mem_componentCarrier_of_mem_rim
      (yRim_mem_of_zRoute_mem
        (T.zRoute.support_takeUntil_subset_support T.z_mem
          M.zSep.left_mem_aArm)) hwY

theorem yPart_disjoint_bSet : Disjoint M.yPart M.bSet := by
  rw [Finset.disjoint_left]
  intro w hwY hwB
  have hwCases : w = M.xSep.right ∨ w = M.ySep.right ∨
      w = M.zSep.right := by simpa [bSet] using hwB
  rcases hwCases with rfl | rfl | rfl
  · apply M.ySep.not_mem_componentCarrier_of_mem_rim
      (yRim_mem_of_xRoute_mem
        (T.xRoute.support_dropUntil_subset_support T.x_mem (by
          simpa only [WatkinsMesnerK32Source.xArmB, Walk.support_reverse,
            List.mem_reverse] using M.xSep.right_mem_bArm))) hwY
  · exact M.ySep.right_not_mem_componentCarrier hwY
  · apply M.ySep.not_mem_componentCarrier_of_mem_rim
      (yRim_mem_of_zRoute_mem
        (T.zRoute.support_dropUntil_subset_support T.z_mem (by
          simpa only [WatkinsMesnerK32Source.zArmB, Walk.support_reverse,
            List.mem_reverse] using M.zSep.right_mem_bArm))) hwY

theorem zPart_disjoint_aSet : Disjoint M.zPart M.aSet := by
  rw [Finset.disjoint_left]
  intro w hwZ hwA
  have hwCases : w = M.xSep.left ∨ w = M.ySep.left ∨
      w = M.zSep.left := by simpa [aSet] using hwA
  rcases hwCases with rfl | rfl | rfl
  · apply M.zSep.not_mem_componentCarrier_of_mem_rim
      (zRim_mem_of_xRoute_mem
        (T.xRoute.support_takeUntil_subset_support T.x_mem
          M.xSep.left_mem_aArm)) hwZ
  · apply M.zSep.not_mem_componentCarrier_of_mem_rim
      (zRim_mem_of_yRoute_mem
        (T.yRoute.support_takeUntil_subset_support T.y_mem
          M.ySep.left_mem_aArm)) hwZ
  · exact M.zSep.left_not_mem_componentCarrier hwZ

theorem zPart_disjoint_bSet : Disjoint M.zPart M.bSet := by
  rw [Finset.disjoint_left]
  intro w hwZ hwB
  have hwCases : w = M.xSep.right ∨ w = M.ySep.right ∨
      w = M.zSep.right := by simpa [bSet] using hwB
  rcases hwCases with rfl | rfl | rfl
  · apply M.zSep.not_mem_componentCarrier_of_mem_rim
      (zRim_mem_of_xRoute_mem
        (T.xRoute.support_dropUntil_subset_support T.x_mem (by
          simpa only [WatkinsMesnerK32Source.xArmB, Walk.support_reverse,
            List.mem_reverse] using M.xSep.right_mem_bArm))) hwZ
  · apply M.zSep.not_mem_componentCarrier_of_mem_rim
      (zRim_mem_of_yRoute_mem
        (T.yRoute.support_dropUntil_subset_support T.y_mem (by
          simpa only [WatkinsMesnerK32Source.yArmB, Walk.support_reverse,
            List.mem_reverse] using M.ySep.right_mem_bArm))) hwZ
  · exact M.zSep.right_not_mem_componentCarrier hwZ

theorem xPart_disjoint_aSet_union_bSet :
    Disjoint M.xPart (M.aSet ∪ M.bSet) :=
  Finset.disjoint_union_right.mpr
    ⟨M.xPart_disjoint_aSet, M.xPart_disjoint_bSet⟩

theorem yPart_disjoint_aSet_union_bSet :
    Disjoint M.yPart (M.aSet ∪ M.bSet) :=
  Finset.disjoint_union_right.mpr
    ⟨M.yPart_disjoint_aSet, M.yPart_disjoint_bSet⟩

theorem zPart_disjoint_aSet_union_bSet :
    Disjoint M.zPart (M.aSet ∪ M.bSet) :=
  Finset.disjoint_union_right.mpr
    ⟨M.zPart_disjoint_aSet, M.zPart_disjoint_bSet⟩

theorem xPart_isComponent :
    IsComponentAfterDeleting G (M.aSet ∪ M.bSet) M.xPart := by
  apply isComponentAfterDeleting_componentCarrier_of_subset
    {M.xSep.left, M.xSep.right} (M.aSet ∪ M.bSet) M.xSep.side
  · intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact Finset.mem_union_left _ M.xA_mem_aSet
    · exact Finset.mem_union_right _ M.xB_mem_bSet
  · exact M.xPart_disjoint_aSet_union_bSet

theorem yPart_isComponent :
    IsComponentAfterDeleting G (M.aSet ∪ M.bSet) M.yPart := by
  apply isComponentAfterDeleting_componentCarrier_of_subset
    {M.ySep.left, M.ySep.right} (M.aSet ∪ M.bSet) M.ySep.side
  · intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact Finset.mem_union_left _ M.yA_mem_aSet
    · exact Finset.mem_union_right _ M.yB_mem_bSet
  · exact M.yPart_disjoint_aSet_union_bSet

theorem zPart_isComponent :
    IsComponentAfterDeleting G (M.aSet ∪ M.bSet) M.zPart := by
  apply isComponentAfterDeleting_componentCarrier_of_subset
    {M.zSep.left, M.zSep.right} (M.aSet ∪ M.bSet) M.zSep.side
  · intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact Finset.mem_union_left _ M.zA_mem_aSet
    · exact Finset.mem_union_right _ M.zB_mem_bSet
  · exact M.zPart_disjoint_aSet_union_bSet

private theorem leftHalf_ne_rightHalf_of_distinct_routes
    {A B p q : V} {P Q : G.Walk A B}
    (hP : P.IsPath) (hQ : Q.IsPath)
    (hp : p ∈ P.support) (hq : q ∈ Q.support)
    (hpA : p ≠ A) (hpB : p ≠ B)
    (hqA : q ≠ A) (hqB : q ≠ B)
    (hmeet : ∀ w, w ∈ P.support → w ∈ Q.support →
      w = A ∨ w = B)
    {l r : V} (hl : l ∈ (P.takeUntil p hp).support)
    (hr : r ∈ (Q.dropUntil q hq).reverse.support) : l ≠ r := by
  intro hlr
  have hlP : l ∈ P.support := P.support_takeUntil_subset_support hp hl
  have hrDrop : r ∈ (Q.dropUntil q hq).support := by
    simpa only [Walk.support_reverse, List.mem_reverse] using hr
  have hrQ : r ∈ Q.support := Q.support_dropUntil_subset_support hq hrDrop
  rcases hmeet l hlP (hlr ▸ hrQ) with hlA | hlB
  · have hAq : A ∈ (Q.takeUntil q hq).support :=
      (Q.takeUntil q hq).start_mem_support
    have hAr : A ∈ (Q.dropUntil q hq).reverse.support := by
      exact Eq.mp (congrArg
        (fun w : V ↦ w ∈ (Q.dropUntil q hq).reverse.support)
        (hlA.symm.trans hlr)).symm hr
    have := Walk.IsPath.takeUntil_inter_reverse_dropUntil_only
      hQ hq A hAq hAr
    exact hqA this.symm
  · have hBr : B ∈ (P.dropUntil p hp).reverse.support := by
      simpa only [Walk.support_reverse, List.mem_reverse] using
        (P.dropUntil p hp).end_mem_support
    have := Walk.IsPath.takeUntil_inter_reverse_dropUntil_only hP hp B
      (hlB ▸ hl) hBr
    exact hpB this.symm

private theorem eq_branchA_of_leftHalves_eq
    {A B p q : V} {P Q : G.Walk A B}
    (hP : P.IsPath) (hp : p ∈ P.support) (hpB : p ≠ B)
    (hq : q ∈ Q.support)
    (hmeet : ∀ w, w ∈ P.support → w ∈ Q.support →
      w = A ∨ w = B)
    {l m : V} (hl : l ∈ (P.takeUntil p hp).support)
    (hm : m ∈ (Q.takeUntil q hq).support) (hlm : l = m) : l = A := by
  have hlP : l ∈ P.support := P.support_takeUntil_subset_support hp hl
  have hmQ : m ∈ Q.support := Q.support_takeUntil_subset_support hq hm
  rcases hmeet l hlP (hlm ▸ hmQ) with hA | hB
  · exact hA
  · exact (Walk.endpoint_notMem_support_takeUntil hP hp hpB.symm
      (hB ▸ hl)).elim

private theorem eq_branchB_of_rightHalves_eq
    {A B p q : V} {P Q : G.Walk A B}
    (hP : P.IsPath) (hp : p ∈ P.support) (hpA : p ≠ A)
    (hq : q ∈ Q.support)
    (hmeet : ∀ w, w ∈ P.support → w ∈ Q.support →
      w = A ∨ w = B)
    {l m : V} (hl : l ∈ (P.dropUntil p hp).reverse.support)
    (hm : m ∈ (Q.dropUntil q hq).reverse.support) (hlm : l = m) : l = B := by
  have hlDrop : l ∈ (P.dropUntil p hp).support := by
    simpa only [Walk.support_reverse, List.mem_reverse] using hl
  have hlP : l ∈ P.support := P.support_dropUntil_subset_support hp hlDrop
  have hmDrop : m ∈ (Q.dropUntil q hq).support := by
    simpa only [Walk.support_reverse, List.mem_reverse] using hm
  have hmQ : m ∈ Q.support := Q.support_dropUntil_subset_support hq hmDrop
  rcases hmeet l hlP (hlm ▸ hmQ) with hA | hB
  · have hAtake : A ∈ (P.takeUntil p hp).support :=
      (P.takeUntil p hp).start_mem_support
    have hArev : A ∈ (P.dropUntil p hp).reverse.support := by
      simpa only [hA] using hl
    have h := Walk.IsPath.takeUntil_inter_reverse_dropUntil_only
      hP hp A hAtake hArev
    exact (hpA h.symm).elim
  · exact hB

/-- Candidate `A` and `B` are disjoint already from the six-route geometry;
maximality is not needed for this part of condition (iii). -/
theorem aSet_disjoint_bSet : Disjoint M.aSet M.bSet := by
  classical
  rw [Finset.disjoint_left]
  intro a haA hbB
  have ha : a = M.xSep.left ∨ a = M.ySep.left ∨ a = M.zSep.left := by
    simpa [aSet] using haA
  have hb : a = M.xSep.right ∨ a = M.ySep.right ∨ a = M.zSep.right := by
    simpa [bSet] using hbB
  rcases ha with rfl | rfl | rfl <;> rcases hb with h | h | h
  · exact M.xSep.left_ne_right h
  · exact (leftHalf_ne_rightHalf_of_distinct_routes
      T.xRoute_isPath T.yRoute_isPath T.x_mem T.y_mem
      T.x_internal.1 T.x_internal.2 T.y_internal.1 T.y_internal.2
      T.xRoute_inter_yRoute M.xSep.left_mem_aArm
      M.ySep.right_mem_bArm) h
  · exact (leftHalf_ne_rightHalf_of_distinct_routes
      T.xRoute_isPath T.zRoute_isPath T.x_mem T.z_mem
      T.x_internal.1 T.x_internal.2 T.z_internal.1 T.z_internal.2
      T.xRoute_inter_zRoute M.xSep.left_mem_aArm
      M.zSep.right_mem_bArm) h
  · exact (leftHalf_ne_rightHalf_of_distinct_routes
      T.yRoute_isPath T.xRoute_isPath T.y_mem T.x_mem
      T.y_internal.1 T.y_internal.2 T.x_internal.1 T.x_internal.2
      (fun w hwY hwX ↦ T.xRoute_inter_yRoute w hwX hwY)
      M.ySep.left_mem_aArm M.xSep.right_mem_bArm) h
  · exact M.ySep.left_ne_right h
  · exact (leftHalf_ne_rightHalf_of_distinct_routes
      T.yRoute_isPath T.zRoute_isPath T.y_mem T.z_mem
      T.y_internal.1 T.y_internal.2 T.z_internal.1 T.z_internal.2
      T.yRoute_inter_zRoute M.ySep.left_mem_aArm
      M.zSep.right_mem_bArm) h
  · exact (leftHalf_ne_rightHalf_of_distinct_routes
      T.zRoute_isPath T.xRoute_isPath T.z_mem T.x_mem
      T.z_internal.1 T.z_internal.2 T.x_internal.1 T.x_internal.2
      (fun w hwZ hwX ↦ T.xRoute_inter_zRoute w hwX hwZ)
      M.zSep.left_mem_aArm M.xSep.right_mem_bArm) h
  · exact (leftHalf_ne_rightHalf_of_distinct_routes
      T.zRoute_isPath T.yRoute_isPath T.z_mem T.y_mem
      T.z_internal.1 T.z_internal.2 T.y_internal.1 T.y_internal.2
      (fun w hwZ hwY ↦ T.yRoute_inter_zRoute w hwY hwZ)
      M.zSep.left_mem_aArm M.ySep.right_mem_bArm) h
  · exact M.zSep.left_ne_right h

theorem xA_eq_yA_imp_branchA (h : M.xSep.left = M.ySep.left) :
    M.xSep.left = T.branchA := by
  exact eq_branchA_of_leftHalves_eq T.xRoute_isPath T.x_mem
    T.x_internal.2 T.y_mem T.xRoute_inter_yRoute
    M.xSep.left_mem_aArm M.ySep.left_mem_aArm h

theorem xA_eq_zA_imp_branchA (h : M.xSep.left = M.zSep.left) :
    M.xSep.left = T.branchA := by
  exact eq_branchA_of_leftHalves_eq T.xRoute_isPath T.x_mem
    T.x_internal.2 T.z_mem T.xRoute_inter_zRoute
    M.xSep.left_mem_aArm M.zSep.left_mem_aArm h

theorem yA_eq_zA_imp_branchA (h : M.ySep.left = M.zSep.left) :
    M.ySep.left = T.branchA := by
  exact eq_branchA_of_leftHalves_eq T.yRoute_isPath T.y_mem
    T.y_internal.2 T.z_mem T.yRoute_inter_zRoute
    M.ySep.left_mem_aArm M.zSep.left_mem_aArm h

theorem xB_eq_yB_imp_branchB (h : M.xSep.right = M.ySep.right) :
    M.xSep.right = T.branchB := by
  exact eq_branchB_of_rightHalves_eq T.xRoute_isPath T.x_mem
    T.x_internal.1 T.y_mem T.xRoute_inter_yRoute
    M.xSep.right_mem_bArm M.ySep.right_mem_bArm h

theorem xB_eq_zB_imp_branchB (h : M.xSep.right = M.zSep.right) :
    M.xSep.right = T.branchB := by
  exact eq_branchB_of_rightHalves_eq T.xRoute_isPath T.x_mem
    T.x_internal.1 T.z_mem T.xRoute_inter_zRoute
    M.xSep.right_mem_bArm M.zSep.right_mem_bArm h

theorem yB_eq_zB_imp_branchB (h : M.ySep.right = M.zSep.right) :
    M.ySep.right = T.branchB := by
  exact eq_branchB_of_rightHalves_eq T.yRoute_isPath T.y_mem
    T.y_internal.1 T.z_mem T.yRoute_inter_zRoute
    M.ySep.right_mem_bArm M.zSep.right_mem_bArm h

/-- AHT p.14, first maximality exchange: if the `x` and `y` separators
have the same `A` boundary but the `z` boundary there is different, their
`B` boundaries must be different. -/
theorem xB_ne_yB_of_xA_eq_yA
    (hdelete : ∀ d : V, (G.induce fun w : V ↦ w ≠ d).Connected)
    (hxyA : M.xSep.left = M.ySep.left)
    (hzA : M.zSep.left ≠ M.xSep.left) :
    M.xSep.right ≠ M.ySep.right := by
  classical
  intro hxyB
  have hbranchA : M.xSep.left = T.branchA :=
    M.xA_eq_yA_imp_branchA hxyA
  have hbranchB : M.xSep.right = T.branchB :=
    M.xB_eq_yB_imp_branchB hxyB
  have hzLeft : z ≠ M.xSep.left := by
    intro h
    exact T.z_internal.1 (h.trans hbranchA)
  have hzRight : z ≠ M.xSep.right := by
    intro h
    exact T.z_internal.2 (h.trans hbranchB)
  have hzAvoid :
      z ∉ ((({M.xSep.left, M.xSep.right} : Finset V) : Set V)) := by
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton,
      not_or]
    exact ⟨hzLeft, hzRight⟩
  let D : G.ComponentCompl
      ((({M.xSep.left, M.xSep.right} : Finset V) : Set V)) :=
    G.componentComplMk hzAvoid
  have hzD : z ∈ (D : Set V) := ⟨hzAvoid, rfl⟩
  have hdisOldNew : Disjoint (M.zSep.side : Set V)
      ((({M.xSep.left, M.xSep.right} : Finset V) : Set V)) := by
    rw [Set.disjoint_left]
    intro v hvSide hvPair
    have hvPart : v ∈ M.zPart := by
      simpa only [zPart, mem_componentCarrier] using hvSide
    simp only [Finset.mem_coe, Finset.mem_insert,
      Finset.mem_singleton] at hvPair
    rcases hvPair with rfl | rfl
    · exact Finset.disjoint_left.mp M.zPart_disjoint_aSet
        hvPart M.xA_mem_aSet
    · exact Finset.disjoint_left.mp M.zPart_disjoint_bSet
        hvPart M.xB_mem_bSet
  have hsub : (M.zSep.side : Set V) ⊆ (D : Set V) :=
    ComponentCompl.subset_of_disjoint_of_shared M.zSep.side D
      hdisOldNew M.zSep.x_mem_side hzD
  obtain ⟨u, huSide, huAdj⟩ :=
    (ComponentCompl.exists_adj_to_each_of_delete_connected
      M.zSep.left_ne_right hdelete M.zSep.side).1
  have huD : u ∈ (D : Set V) := hsub huSide
  have hzA_ne_xB : M.zSep.left ≠ M.xSep.right := by
    intro h
    exact Finset.disjoint_left.mp M.aSet_disjoint_bSet
      M.zA_mem_aSet (by simpa only [h] using M.xB_mem_bSet)
  have hzAAvoid : M.zSep.left ∉
      ((({M.xSep.left, M.xSep.right} : Finset V) : Set V)) := by
    simp only [Finset.mem_coe, Finset.mem_insert,
      Finset.mem_singleton, not_or]
    exact ⟨hzA, hzA_ne_xB⟩
  have hzAD : M.zSep.left ∈ (D : Set V) :=
    ComponentCompl.mem_of_adj u M.zSep.left huD hzAAvoid huAdj
  have hyPair :
      ((({M.ySep.left, M.ySep.right} : Finset V) : Set V)) =
        ((({M.xSep.left, M.xSep.right} : Finset V) : Set V)) := by
    ext v
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton]
    rw [← hxyA, ← hxyB]
  let Y : G.ComponentCompl
      ((({M.xSep.left, M.xSep.right} : Finset V) : Set V)) :=
    ComponentCompl.transport hyPair M.ySep.side
  let R : RoutedCycleSeparator T.zArmA T.zArmB T.zRim :=
    { left := M.xSep.left
      right := M.xSep.right
      left_ne_right := M.xSep.left_ne_right
      x_ne_left := hzLeft
      x_ne_right := hzRight
      side := D
      x_mem_side := hzD
      rim_outside_side := by
        intro w hwRim hwLeft hwRight hwD
        simp only [WatkinsMesnerK32Source.zRim,
          Walk.mem_support_append_iff, Walk.support_reverse,
          List.mem_reverse] at hwRim
        rcases hwRim with hwX | hwY
        · have hwXSide : w ∈ (M.xSep.side : Set V) :=
            M.xSep.mem_side_of_route_of_eq_branches T.x_mem
              T.xRoute_isPath hbranchA hbranchB hwX hwLeft hwRight
          have hzXSide : z ∈ (M.xSep.side : Set V) :=
            ⟨hzAvoid, hzD.2.trans (hwD.2.symm.trans hwXSide.2)⟩
          exact M.xSep.rim_outside_side z
            (by simp [WatkinsMesnerK32Source.xRim, T.z_mem])
            hzLeft hzRight hzXSide
        · have hwYSide : w ∈ (M.ySep.side : Set V) :=
            M.ySep.mem_side_of_route_of_eq_branches T.y_mem
              T.yRoute_isPath
              (hxyA.symm.trans hbranchA)
              (hxyB.symm.trans hbranchB) hwY
              (fun h ↦ hwLeft (h.trans hxyA.symm))
              (fun h ↦ hwRight (h.trans hxyB.symm))
          have hwY' : w ∈ (Y : Set V) := by
            simpa only [Y, ComponentCompl.mem_transport] using hwYSide
          have hzY' : z ∈ (Y : Set V) :=
            ⟨hzAvoid, hzD.2.trans (hwD.2.symm.trans hwY'.2)⟩
          have hzYSide : z ∈ (M.ySep.side : Set V) := by
            simpa only [Y, ComponentCompl.mem_transport] using hzY'
          exact M.ySep.rim_outside_side z
            (by simp [WatkinsMesnerK32Source.yRim, T.z_mem])
            (fun h ↦ hzLeft (h.trans hxyA.symm))
            (fun h ↦ hzRight (h.trans hxyB.symm)) hzYSide
      left_mem_aArm := by
        simpa only [hbranchA] using T.zArmA.start_mem_support
      left_ne_terminal := hzLeft.symm
      right_mem_bArm := by
        simpa only [hbranchB] using T.zArmB.start_mem_support
      right_ne_terminal := hzRight.symm }
  have hstrict :
      componentCarrier (G := G) {M.zSep.left, M.zSep.right}
          M.zSep.side ⊂
        componentCarrier (G := G) {R.left, R.right} R.side := by
    rw [Finset.ssubset_iff_subset_ne]
    constructor
    · intro v hv
      have hvSide : v ∈ (M.zSep.side : Set V) := by
        simpa only [mem_componentCarrier] using hv
      simpa only [R, mem_componentCarrier] using hsub hvSide
    · intro heq
      have hzAOld : M.zSep.left ∈
          componentCarrier (G := G) {M.zSep.left, M.zSep.right}
            M.zSep.side := by
        rw [heq]
        simpa only [R, mem_componentCarrier] using hzAD
      exact M.zSep.left_not_mem_componentCarrier hzAOld
  exact (M.z_maximal.not_ssubset_componentCarrier R) hstrict

abbrev conditionVGraph : SimpleGraph
    {w : V // w ∉ M.zPart ∧ w ≠ M.xSep.left} :=
  G.induce {w : V | w ∉ M.zPart ∧ w ≠ M.xSep.left}

def conditionVZA (hzA : M.zSep.left ≠ M.xSep.left) :
    {w : V // w ∉ M.zPart ∧ w ≠ M.xSep.left} :=
  ⟨M.zSep.left,
    fun h ↦ Finset.disjoint_left.mp M.zPart_disjoint_aSet h M.zA_mem_aSet,
    hzA⟩

def conditionVZB :
    {w : V // w ∉ M.zPart ∧ w ≠ M.xSep.left} :=
  ⟨M.zSep.right,
    fun h ↦ Finset.disjoint_left.mp M.zPart_disjoint_bSet h M.zB_mem_bSet,
    fun h ↦ Finset.disjoint_left.mp M.aSet_disjoint_bSet
      M.xA_mem_aSet (h.symm ▸ M.zB_mem_bSet)⟩

def conditionVXB :
    {w : V // w ∉ M.zPart ∧ w ≠ M.xSep.left} :=
  ⟨M.xSep.right,
    fun h ↦ Finset.disjoint_left.mp M.zPart_disjoint_bSet h M.xB_mem_bSet,
    M.xSep.left_ne_right.symm⟩

def conditionVYB :
    {w : V // w ∉ M.zPart ∧ w ≠ M.xSep.left} :=
  ⟨M.ySep.right,
    fun h ↦ Finset.disjoint_left.mp M.zPart_disjoint_bSet h M.yB_mem_bSet,
    fun h ↦ Finset.disjoint_left.mp M.aSet_disjoint_bSet
      M.xA_mem_aSet (h.symm ▸ M.yB_mem_bSet)⟩

theorem aSet_nonempty : M.aSet.Nonempty :=
  ⟨M.xSep.left, by simp [aSet]⟩

theorem bSet_nonempty : M.bSet.Nonempty :=
  ⟨M.xSep.right, by simp [bSet]⟩

/-- Before the maximality argument excludes the middle case, a displayed
triple has cardinality one, two, or three. -/
theorem aSet_card_trichotomy :
    M.aSet.card = 1 ∨ M.aSet.card = 2 ∨ M.aSet.card = 3 := by
  have hpos : 0 < M.aSet.card := Finset.card_pos.mpr M.aSet_nonempty
  have hle : M.aSet.card ≤ 3 := by
    have htail : ({M.ySep.left, M.zSep.left} : Finset V).card ≤ 2 := by
      simpa using (Finset.card_insert_le M.ySep.left {M.zSep.left})
    have hins := Finset.card_insert_le M.xSep.left
      {M.ySep.left, M.zSep.left}
    rw [aSet]
    omega
  omega

theorem bSet_card_trichotomy :
    M.bSet.card = 1 ∨ M.bSet.card = 2 ∨ M.bSet.card = 3 := by
  have hpos : 0 < M.bSet.card := Finset.card_pos.mpr M.bSet_nonempty
  have hle : M.bSet.card ≤ 3 := by
    have htail : ({M.ySep.right, M.zSep.right} : Finset V).card ≤ 2 := by
      simpa using (Finset.card_insert_le M.ySep.right {M.zSep.right})
    have hins := Finset.card_insert_le M.xSep.right
      {M.ySep.right, M.zSep.right}
    rw [bSet]
    omega
  omega

theorem all_A_eq_of_card_one (h : M.aSet.card = 1) :
    M.xSep.left = M.ySep.left ∧ M.xSep.left = M.zSep.left := by
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h
  have hx : M.xSep.left = a := by
    have : M.xSep.left ∈ ({a} : Finset V) := by
      rw [← ha]
      exact M.xA_mem_aSet
    simpa using this
  have hy : M.ySep.left = a := by
    have : M.ySep.left ∈ ({a} : Finset V) := by
      rw [← ha]
      exact M.yA_mem_aSet
    simpa using this
  have hz : M.zSep.left = a := by
    have : M.zSep.left ∈ ({a} : Finset V) := by
      rw [← ha]
      exact M.zA_mem_aSet
    simpa using this
  exact ⟨hx.trans hy.symm, hx.trans hz.symm⟩

theorem all_B_eq_of_card_one (h : M.bSet.card = 1) :
    M.xSep.right = M.ySep.right ∧ M.xSep.right = M.zSep.right := by
  obtain ⟨b, hb⟩ := Finset.card_eq_one.mp h
  have hx : M.xSep.right = b := by
    have : M.xSep.right ∈ ({b} : Finset V) := by
      rw [← hb]
      exact M.xB_mem_bSet
    simpa using this
  have hy : M.ySep.right = b := by
    have : M.ySep.right ∈ ({b} : Finset V) := by
      rw [← hb]
      exact M.yB_mem_bSet
    simpa using this
  have hz : M.zSep.right = b := by
    have : M.zSep.right ∈ ({b} : Finset V) := by
      rw [← hb]
      exact M.zB_mem_bSet
    simpa using this
  exact ⟨hx.trans hy.symm, hx.trans hz.symm⟩

theorem branchA_eq_of_aSet_card_one (h : M.aSet.card = 1) :
    M.xSep.left = T.branchA :=
  M.xA_eq_yA_imp_branchA (M.all_A_eq_of_card_one h).1

theorem branchB_eq_of_bSet_card_one (h : M.bSet.card = 1) :
    M.xSep.right = T.branchB :=
  M.xB_eq_yB_imp_branchB (M.all_B_eq_of_card_one h).1

theorem aSet_eq_singleton_branchA (h : M.aSet.card = 1) :
    M.aSet = {T.branchA} := by
  obtain ⟨hxy, hxz⟩ := M.all_A_eq_of_card_one h
  rw [aSet, ← hxy, ← hxz, M.branchA_eq_of_aSet_card_one h]
  simp

theorem bSet_eq_singleton_branchB (h : M.bSet.card = 1) :
    M.bSet = {T.branchB} := by
  obtain ⟨hxy, hxz⟩ := M.all_B_eq_of_card_one h
  rw [bSet, ← hxy, ← hxz, M.branchB_eq_of_bSet_card_one h]
  simp

theorem A_pair_pattern_of_card_two (h : M.aSet.card = 2) :
    (M.xSep.left = M.ySep.left ∧ M.xSep.left ≠ M.zSep.left) ∨
    (M.xSep.left = M.zSep.left ∧ M.xSep.left ≠ M.ySep.left) ∨
    (M.ySep.left = M.zSep.left ∧ M.ySep.left ≠ M.xSep.left) := by
  by_cases hxy : M.xSep.left = M.ySep.left
  · by_cases hxz : M.xSep.left = M.zSep.left
    · have : M.aSet.card = 1 := by
        rw [aSet, ← hxy, ← hxz]
        simp
      omega
    · exact Or.inl ⟨hxy, hxz⟩
  · by_cases hxz : M.xSep.left = M.zSep.left
    · exact Or.inr (Or.inl ⟨hxz, hxy⟩)
    · by_cases hyz : M.ySep.left = M.zSep.left
      · exact Or.inr (Or.inr ⟨hyz, Ne.symm hxy⟩)
      · have : M.aSet.card = 3 := by
          simp [aSet, hxy, hxz, hyz]
        omega

theorem B_pair_pattern_of_card_two (h : M.bSet.card = 2) :
    (M.xSep.right = M.ySep.right ∧ M.xSep.right ≠ M.zSep.right) ∨
    (M.xSep.right = M.zSep.right ∧ M.xSep.right ≠ M.ySep.right) ∨
    (M.ySep.right = M.zSep.right ∧ M.ySep.right ≠ M.xSep.right) := by
  by_cases hxy : M.xSep.right = M.ySep.right
  · by_cases hxz : M.xSep.right = M.zSep.right
    · have : M.bSet.card = 1 := by
        rw [bSet, ← hxy, ← hxz]
        simp
      omega
    · exact Or.inl ⟨hxy, hxz⟩
  · by_cases hxz : M.xSep.right = M.zSep.right
    · exact Or.inr (Or.inl ⟨hxz, hxy⟩)
    · by_cases hyz : M.ySep.right = M.zSep.right
      · exact Or.inr (Or.inr ⟨hyz, Ne.symm hxy⟩)
      · have : M.bSet.card = 3 := by
          simp [bSet, hxy, hxz, hyz]
        omega

/-- In the forbidden cardinality-two case, the repeated `A`-attachment is
the left theta branch vertex.  This is the exact symmetry split used at the
start of AHT's proof of condition (v). -/
theorem A_branch_pattern_of_card_two (h : M.aSet.card = 2) :
    (M.xSep.left = M.ySep.left ∧
      M.xSep.left = T.branchA ∧ M.zSep.left ≠ T.branchA) ∨
    (M.xSep.left = M.zSep.left ∧
      M.xSep.left = T.branchA ∧ M.ySep.left ≠ T.branchA) ∨
    (M.ySep.left = M.zSep.left ∧
      M.ySep.left = T.branchA ∧ M.xSep.left ≠ T.branchA) := by
  rcases M.A_pair_pattern_of_card_two h with hxy | hxz | hyz
  · have hbranch := M.xA_eq_yA_imp_branchA hxy.1
    exact Or.inl ⟨hxy.1, hbranch, fun hz ↦ hxy.2 (hbranch.trans hz.symm)⟩
  · have hbranch := M.xA_eq_zA_imp_branchA hxz.1
    exact Or.inr (Or.inl
      ⟨hxz.1, hbranch, fun hy ↦ hxz.2 (hbranch.trans hy.symm)⟩)
  · have hbranch := M.yA_eq_zA_imp_branchA hyz.1
    exact Or.inr (Or.inr
      ⟨hyz.1, hbranch, fun hx ↦ hyz.2 (hbranch.trans hx.symm)⟩)

/-- Symmetric right-branch pattern for a cardinality-two `B`. -/
theorem B_branch_pattern_of_card_two (h : M.bSet.card = 2) :
    (M.xSep.right = M.ySep.right ∧
      M.xSep.right = T.branchB ∧ M.zSep.right ≠ T.branchB) ∨
    (M.xSep.right = M.zSep.right ∧
      M.xSep.right = T.branchB ∧ M.ySep.right ≠ T.branchB) ∨
    (M.ySep.right = M.zSep.right ∧
      M.ySep.right = T.branchB ∧ M.xSep.right ≠ T.branchB) := by
  rcases M.B_pair_pattern_of_card_two h with hxy | hxz | hyz
  · have hbranch := M.xB_eq_yB_imp_branchB hxy.1
    exact Or.inl ⟨hxy.1, hbranch, fun hz ↦ hxy.2 (hbranch.trans hz.symm)⟩
  · have hbranch := M.xB_eq_zB_imp_branchB hxz.1
    exact Or.inr (Or.inl
      ⟨hxz.1, hbranch, fun hy ↦ hxz.2 (hbranch.trans hy.symm)⟩)
  · have hbranch := M.yB_eq_zB_imp_branchB hyz.1
    exact Or.inr (Or.inr
      ⟨hyz.1, hbranch, fun hx ↦ hyz.2 (hbranch.trans hx.symm)⟩)

/-- The other two terminals lie outside the `x`-side component. -/
theorem y_not_mem_xPart : y ∉ M.xPart := by
  have hyL : y ≠ M.xSep.left := by
    intro h
    have hleftRoute : M.xSep.left ∈ T.xRoute.support :=
      T.xRoute.support_takeUntil_subset_support T.x_mem M.xSep.left_mem_aArm
    rcases T.xRoute_inter_yRoute y
      (by simpa only [h] using hleftRoute) T.y_mem with hA | hB
    · exact T.y_internal.1 hA
    · exact T.y_internal.2 hB
  have hyR : y ≠ M.xSep.right := by
    intro h
    have hrightDrop : M.xSep.right ∈
        (T.xRoute.dropUntil x T.x_mem).support := by
      simpa only [WatkinsMesnerK32Source.xArmB, Walk.support_reverse,
        List.mem_reverse] using M.xSep.right_mem_bArm
    have hrightRoute : M.xSep.right ∈ T.xRoute.support :=
      T.xRoute.support_dropUntil_subset_support T.x_mem hrightDrop
    rcases T.xRoute_inter_yRoute y
      (by simpa only [h] using hrightRoute) T.y_mem with hA | hB
    · exact T.y_internal.1 hA
    · exact T.y_internal.2 hB
  have hyRim : y ∈ T.xRim.support := by
    simp [WatkinsMesnerK32Source.xRim, T.y_mem]
  intro hyX
  apply M.xSep.rim_outside_side y hyRim hyL hyR
  simpa only [xPart, mem_componentCarrier] using hyX

theorem z_not_mem_xPart : z ∉ M.xPart := by
  have hzL : z ≠ M.xSep.left := by
    intro h
    have hleftRoute : M.xSep.left ∈ T.xRoute.support :=
      T.xRoute.support_takeUntil_subset_support T.x_mem M.xSep.left_mem_aArm
    rcases T.xRoute_inter_zRoute z
      (by simpa only [h] using hleftRoute) T.z_mem with hA | hB
    · exact T.z_internal.1 hA
    · exact T.z_internal.2 hB
  have hzR : z ≠ M.xSep.right := by
    intro h
    have hrightDrop : M.xSep.right ∈
        (T.xRoute.dropUntil x T.x_mem).support := by
      simpa only [WatkinsMesnerK32Source.xArmB, Walk.support_reverse,
        List.mem_reverse] using M.xSep.right_mem_bArm
    have hrightRoute : M.xSep.right ∈ T.xRoute.support :=
      T.xRoute.support_dropUntil_subset_support T.x_mem hrightDrop
    rcases T.xRoute_inter_zRoute z
      (by simpa only [h] using hrightRoute) T.z_mem with hA | hB
    · exact T.z_internal.1 hA
    · exact T.z_internal.2 hB
  have hzRim : z ∈ T.xRim.support := by
    simp [WatkinsMesnerK32Source.xRim, T.z_mem]
  intro hzX
  apply M.xSep.rim_outside_side z hzRim hzL hzR
  simpa only [xPart, mem_componentCarrier] using hzX

theorem x_not_mem_yPart : x ∉ M.yPart := by
  have hxL : x ≠ M.ySep.left := by
    intro h
    have hleftRoute : M.ySep.left ∈ T.yRoute.support :=
      T.yRoute.support_takeUntil_subset_support T.y_mem M.ySep.left_mem_aArm
    rcases T.xRoute_inter_yRoute x T.x_mem
      (by simpa only [h] using hleftRoute) with hA | hB
    · exact T.x_internal.1 hA
    · exact T.x_internal.2 hB
  have hxR : x ≠ M.ySep.right := by
    intro h
    have hrightDrop : M.ySep.right ∈
        (T.yRoute.dropUntil y T.y_mem).support := by
      simpa only [WatkinsMesnerK32Source.yArmB, Walk.support_reverse,
        List.mem_reverse] using M.ySep.right_mem_bArm
    have hrightRoute : M.ySep.right ∈ T.yRoute.support :=
      T.yRoute.support_dropUntil_subset_support T.y_mem hrightDrop
    rcases T.xRoute_inter_yRoute x T.x_mem
      (by simpa only [h] using hrightRoute) with hA | hB
    · exact T.x_internal.1 hA
    · exact T.x_internal.2 hB
  have hxRim : x ∈ T.yRim.support := by
    simp [WatkinsMesnerK32Source.yRim, T.x_mem]
  intro hxY
  apply M.ySep.rim_outside_side x hxRim hxL hxR
  simpa only [yPart, mem_componentCarrier] using hxY

theorem z_not_mem_yPart : z ∉ M.yPart := by
  have hzL : z ≠ M.ySep.left := by
    intro h
    have hleftRoute : M.ySep.left ∈ T.yRoute.support :=
      T.yRoute.support_takeUntil_subset_support T.y_mem M.ySep.left_mem_aArm
    rcases T.yRoute_inter_zRoute z
      (by simpa only [h] using hleftRoute) T.z_mem with hA | hB
    · exact T.z_internal.1 hA
    · exact T.z_internal.2 hB
  have hzR : z ≠ M.ySep.right := by
    intro h
    have hrightDrop : M.ySep.right ∈
        (T.yRoute.dropUntil y T.y_mem).support := by
      simpa only [WatkinsMesnerK32Source.yArmB, Walk.support_reverse,
        List.mem_reverse] using M.ySep.right_mem_bArm
    have hrightRoute : M.ySep.right ∈ T.yRoute.support :=
      T.yRoute.support_dropUntil_subset_support T.y_mem hrightDrop
    rcases T.yRoute_inter_zRoute z
      (by simpa only [h] using hrightRoute) T.z_mem with hA | hB
    · exact T.z_internal.1 hA
    · exact T.z_internal.2 hB
  have hzRim : z ∈ T.yRim.support := by
    simp [WatkinsMesnerK32Source.yRim, T.z_mem]
  intro hzY
  apply M.ySep.rim_outside_side z hzRim hzL hzR
  simpa only [yPart, mem_componentCarrier] using hzY

theorem x_not_mem_zPart : x ∉ M.zPart := by
  have hxL : x ≠ M.zSep.left := by
    intro h
    have hleftRoute : M.zSep.left ∈ T.zRoute.support :=
      T.zRoute.support_takeUntil_subset_support T.z_mem M.zSep.left_mem_aArm
    rcases T.xRoute_inter_zRoute x T.x_mem
      (by simpa only [h] using hleftRoute) with hA | hB
    · exact T.x_internal.1 hA
    · exact T.x_internal.2 hB
  have hxR : x ≠ M.zSep.right := by
    intro h
    have hrightDrop : M.zSep.right ∈
        (T.zRoute.dropUntil z T.z_mem).support := by
      simpa only [WatkinsMesnerK32Source.zArmB, Walk.support_reverse,
        List.mem_reverse] using M.zSep.right_mem_bArm
    have hrightRoute : M.zSep.right ∈ T.zRoute.support :=
      T.zRoute.support_dropUntil_subset_support T.z_mem hrightDrop
    rcases T.xRoute_inter_zRoute x T.x_mem
      (by simpa only [h] using hrightRoute) with hA | hB
    · exact T.x_internal.1 hA
    · exact T.x_internal.2 hB
  have hxRim : x ∈ T.zRim.support := by
    simp [WatkinsMesnerK32Source.zRim, T.x_mem]
  intro hxZ
  apply M.zSep.rim_outside_side x hxRim hxL hxR
  simpa only [zPart, mem_componentCarrier] using hxZ

theorem y_not_mem_zPart : y ∉ M.zPart := by
  have hyL : y ≠ M.zSep.left := by
    intro h
    have hleftRoute : M.zSep.left ∈ T.zRoute.support :=
      T.zRoute.support_takeUntil_subset_support T.z_mem M.zSep.left_mem_aArm
    rcases T.yRoute_inter_zRoute y T.y_mem
      (by simpa only [h] using hleftRoute) with hA | hB
    · exact T.y_internal.1 hA
    · exact T.y_internal.2 hB
  have hyR : y ≠ M.zSep.right := by
    intro h
    have hrightDrop : M.zSep.right ∈
        (T.zRoute.dropUntil z T.z_mem).support := by
      simpa only [WatkinsMesnerK32Source.zArmB, Walk.support_reverse,
        List.mem_reverse] using M.zSep.right_mem_bArm
    have hrightRoute : M.zSep.right ∈ T.zRoute.support :=
      T.zRoute.support_dropUntil_subset_support T.z_mem hrightDrop
    rcases T.yRoute_inter_zRoute y T.y_mem
      (by simpa only [h] using hrightRoute) with hA | hB
    · exact T.y_internal.1 hA
    · exact T.y_internal.2 hB
  have hyRim : y ∈ T.zRim.support := by
    simp [WatkinsMesnerK32Source.zRim, T.y_mem]
  intro hyZ
  apply M.zSep.rim_outside_side y hyRim hyL hyR
  simpa only [zPart, mem_componentCarrier] using hyZ

/-- The three displayed terminal components are pairwise distinct
components after deleting the common candidate boundary `A ∪ B`. -/
theorem xPart_disjoint_yPart : Disjoint M.xPart M.yPart := by
  rw [Finset.disjoint_left]
  intro w hwX hwY
  have hyX : y ∈ M.xPart :=
    M.xPart_isComponent.mem_of_shared M.yPart_isComponent
      hwX hwY M.y_mem_yPart
  exact M.y_not_mem_xPart hyX

theorem xPart_disjoint_zPart : Disjoint M.xPart M.zPart := by
  rw [Finset.disjoint_left]
  intro w hwX hwZ
  have hzX : z ∈ M.xPart :=
    M.xPart_isComponent.mem_of_shared M.zPart_isComponent
      hwX hwZ M.z_mem_zPart
  exact M.z_not_mem_xPart hzX

theorem yPart_disjoint_zPart : Disjoint M.yPart M.zPart := by
  rw [Finset.disjoint_left]
  intro w hwY hwZ
  have hzY : z ∈ M.yPart :=
    M.yPart_isComponent.mem_of_shared M.zPart_isComponent
      hwY hwZ M.z_mem_zPart
  exact M.z_not_mem_yPart hzY

/-! The undeleted outer bypasses.  These establish the connectedness half
of condition (vi) directly from the `K_{3,2}` source.  For the deletion
half, a failed bypass will be converted into a larger routed separator by
maximality. -/

theorem x_boundary_reachable :
    (G.induce fun v : V ↦ v ∉ M.xPart).Reachable
      ⟨M.xSep.left, by
        exact M.xSep.left_not_mem_componentCarrier⟩
      ⟨M.xSep.right, by
        exact M.xSep.right_not_mem_componentCarrier⟩ := by
  have hq : ∀ w, w ∈ T.yRoute.support → w ∈ T.xRim.support := by
    intro w hw
    simp only [WatkinsMesnerK32Source.xRim,
      Walk.mem_support_append_iff]
    exact Or.inl hw
  simpa only [xPart] using M.xSep.outerBypass_reachable
    (T.xRoute_isPath.takeUntil T.x_mem)
    (T.xRoute_isPath.dropUntil T.x_mem).reverse
    T.xRim.start_mem_support
    (by simp [WatkinsMesnerK32Source.xRim])
    (fun w hwA hwB ↦
      Walk.IsPath.takeUntil_inter_reverse_dropUntil_only
        T.xRoute_isPath T.x_mem w hwA hwB)
    T.yRoute hq

theorem y_boundary_reachable :
    (G.induce fun v : V ↦ v ∉ M.yPart).Reachable
      ⟨M.ySep.left, by
        exact M.ySep.left_not_mem_componentCarrier⟩
      ⟨M.ySep.right, by
        exact M.ySep.right_not_mem_componentCarrier⟩ := by
  have hq : ∀ w, w ∈ T.xRoute.support → w ∈ T.yRim.support := by
    intro w hw
    simp only [WatkinsMesnerK32Source.yRim,
      Walk.mem_support_append_iff]
    exact Or.inl hw
  simpa only [yPart] using M.ySep.outerBypass_reachable
    (T.yRoute_isPath.takeUntil T.y_mem)
    (T.yRoute_isPath.dropUntil T.y_mem).reverse
    T.yRim.start_mem_support
    (by simp [WatkinsMesnerK32Source.yRim])
    (fun w hwA hwB ↦
      Walk.IsPath.takeUntil_inter_reverse_dropUntil_only
        T.yRoute_isPath T.y_mem w hwA hwB)
    T.xRoute hq

theorem z_boundary_reachable :
    (G.induce fun v : V ↦ v ∉ M.zPart).Reachable
      ⟨M.zSep.left, by
        exact M.zSep.left_not_mem_componentCarrier⟩
      ⟨M.zSep.right, by
        exact M.zSep.right_not_mem_componentCarrier⟩ := by
  have hq : ∀ w, w ∈ T.xRoute.support → w ∈ T.zRim.support := by
    intro w hw
    simp only [WatkinsMesnerK32Source.zRim,
      Walk.mem_support_append_iff]
    exact Or.inl hw
  simpa only [zPart] using M.zSep.outerBypass_reachable
    (T.zRoute_isPath.takeUntil T.z_mem)
    (T.zRoute_isPath.dropUntil T.z_mem).reverse
    T.zRim.start_mem_support
    (by simp [WatkinsMesnerK32Source.zRim])
    (fun w hwA hwB ↦
      Walk.IsPath.takeUntil_inter_reverse_dropUntil_only
        T.zRoute_isPath T.z_mem w hwA hwB)
    T.xRoute hq

/-- Deletion bypass for the `x`-separator. -/
theorem x_boundary_reachable_delete
    (hdelete : ∀ d : V, (G.induce fun w : V ↦ w ≠ d).Connected)
    (d : {v : V // v ∉ M.xPart})
    (hda : M.xSep.left ≠ d.1) (hdb : M.xSep.right ≠ d.1) :
    (G.induce fun q : V ↦ q ∉ M.xPart ∧ q ≠ d.1).Reachable
      ⟨M.xSep.left, M.xSep.left_not_mem_componentCarrier, hda⟩
      ⟨M.xSep.right, M.xSep.right_not_mem_componentCarrier, hdb⟩ := by
  have hySub : ∀ w, w ∈ T.yRoute.support → w ∈ T.xRim.support := by
    intro w hw
    simp only [WatkinsMesnerK32Source.xRim,
      Walk.mem_support_append_iff]
    exact Or.inl hw
  have hzSub : ∀ w, w ∈ T.zRoute.support → w ∈ T.xRim.support := by
    intro w hw
    simp only [WatkinsMesnerK32Source.xRim,
      Walk.mem_support_append_iff, Walk.support_reverse, List.mem_reverse]
    exact Or.inr hw
  simpa only [xPart] using
    M.xSep.boundary_reachable_avoiding_of_maximal
      M.x_maximal
      (T.xRoute_isPath.takeUntil T.x_mem)
      (T.xRoute_isPath.dropUntil T.x_mem).reverse
      T.xRim_isCycle T.xRim.start_mem_support
      (by simp [WatkinsMesnerK32Source.xRim])
      (fun w hwA hwB ↦
        Walk.IsPath.takeUntil_inter_reverse_dropUntil_only
          T.xRoute_isPath T.x_mem w hwA hwB)
      hdelete T.yRoute T.zRoute hySub hzSub T.yRoute_inter_zRoute
      (by simpa only [xPart, mem_componentCarrier] using d.2)
      hda.symm hdb.symm

/-- Deletion bypass for the `y`-separator. -/
theorem y_boundary_reachable_delete
    (hdelete : ∀ d : V, (G.induce fun w : V ↦ w ≠ d).Connected)
    (d : {v : V // v ∉ M.yPart})
    (hda : M.ySep.left ≠ d.1) (hdb : M.ySep.right ≠ d.1) :
    (G.induce fun q : V ↦ q ∉ M.yPart ∧ q ≠ d.1).Reachable
      ⟨M.ySep.left, M.ySep.left_not_mem_componentCarrier, hda⟩
      ⟨M.ySep.right, M.ySep.right_not_mem_componentCarrier, hdb⟩ := by
  have hxSub : ∀ w, w ∈ T.xRoute.support → w ∈ T.yRim.support := by
    intro w hw
    simp only [WatkinsMesnerK32Source.yRim,
      Walk.mem_support_append_iff]
    exact Or.inl hw
  have hzSub : ∀ w, w ∈ T.zRoute.support → w ∈ T.yRim.support := by
    intro w hw
    simp only [WatkinsMesnerK32Source.yRim,
      Walk.mem_support_append_iff, Walk.support_reverse, List.mem_reverse]
    exact Or.inr hw
  simpa only [yPart] using
    M.ySep.boundary_reachable_avoiding_of_maximal
      M.y_maximal
      (T.yRoute_isPath.takeUntil T.y_mem)
      (T.yRoute_isPath.dropUntil T.y_mem).reverse
      T.yRim_isCycle T.yRim.start_mem_support
      (by simp [WatkinsMesnerK32Source.yRim])
      (fun w hwA hwB ↦
        Walk.IsPath.takeUntil_inter_reverse_dropUntil_only
          T.yRoute_isPath T.y_mem w hwA hwB)
      hdelete T.xRoute T.zRoute hxSub hzSub T.xRoute_inter_zRoute
      (by simpa only [yPart, mem_componentCarrier] using d.2)
      hda.symm hdb.symm

/-- Deletion bypass for the `z`-separator. -/
theorem z_boundary_reachable_delete
    (hdelete : ∀ d : V, (G.induce fun w : V ↦ w ≠ d).Connected)
    (d : {v : V // v ∉ M.zPart})
    (hda : M.zSep.left ≠ d.1) (hdb : M.zSep.right ≠ d.1) :
    (G.induce fun q : V ↦ q ∉ M.zPart ∧ q ≠ d.1).Reachable
      ⟨M.zSep.left, M.zSep.left_not_mem_componentCarrier, hda⟩
      ⟨M.zSep.right, M.zSep.right_not_mem_componentCarrier, hdb⟩ := by
  have hxSub : ∀ w, w ∈ T.xRoute.support → w ∈ T.zRim.support := by
    intro w hw
    simp only [WatkinsMesnerK32Source.zRim,
      Walk.mem_support_append_iff]
    exact Or.inl hw
  have hySub : ∀ w, w ∈ T.yRoute.support → w ∈ T.zRim.support := by
    intro w hw
    simp only [WatkinsMesnerK32Source.zRim,
      Walk.mem_support_append_iff, Walk.support_reverse, List.mem_reverse]
    exact Or.inr hw
  simpa only [zPart] using
    M.zSep.boundary_reachable_avoiding_of_maximal
      M.z_maximal
      (T.zRoute_isPath.takeUntil T.z_mem)
      (T.zRoute_isPath.dropUntil T.z_mem).reverse
      T.zRim_isCycle T.zRim.start_mem_support
      (by simp [WatkinsMesnerK32Source.zRim])
      (fun w hwA hwB ↦
        Walk.IsPath.takeUntil_inter_reverse_dropUntil_only
          T.zRoute_isPath T.z_mem w hwA hwB)
      hdelete T.xRoute T.yRoute hxSub hySub T.xRoute_inter_yRoute
      (by simpa only [zPart, mem_componentCarrier] using d.2)
      hda.symm hdb.symm

/-- Condition (vi) for the `x`-side, proved from maximality. -/
theorem x_complementVertexTwoConnected
    (hconn : G.Connected)
    (hdelete : ∀ d : V, (G.induce fun w : V ↦ w ≠ d).Connected) :
    ComplementVertexTwoConnected G M.xPart := by
  simpa only [xPart] using
    ComponentCompl.complementVertexTwoConnected_of_boundary_reachable M.xSep.side
      M.xSep.left_ne_right hconn hdelete M.x_boundary_reachable
      (fun d hda hdb ↦ M.x_boundary_reachable_delete hdelete d hda hdb)

theorem y_complementVertexTwoConnected
    (hconn : G.Connected)
    (hdelete : ∀ d : V, (G.induce fun w : V ↦ w ≠ d).Connected) :
    ComplementVertexTwoConnected G M.yPart := by
  simpa only [yPart] using
    ComponentCompl.complementVertexTwoConnected_of_boundary_reachable M.ySep.side
      M.ySep.left_ne_right hconn hdelete M.y_boundary_reachable
      (fun d hda hdb ↦ M.y_boundary_reachable_delete hdelete d hda hdb)

theorem z_complementVertexTwoConnected
    (hconn : G.Connected)
    (hdelete : ∀ d : V, (G.induce fun w : V ↦ w ≠ d).Connected) :
    ComplementVertexTwoConnected G M.zPart := by
  simpa only [zPart] using
    ComponentCompl.complementVertexTwoConnected_of_boundary_reachable M.zSep.side
      M.zSep.left_ne_right hconn hdelete M.z_boundary_reachable
      (fun d hda hdb ↦ M.z_boundary_reachable_delete hdelete d hda hdb)

/-! ## The two outer connector subgraphs -/

/-- The three initial `A`-side stems used to show that the class of
admissible connector pairs is nonempty. -/
def xAStem : G.Walk T.branchA M.xSep.left :=
  T.xArmA.takeUntil M.xSep.left M.xSep.left_mem_aArm

def yAStem : G.Walk T.branchA M.ySep.left :=
  T.yArmA.takeUntil M.ySep.left M.ySep.left_mem_aArm

def zAStem : G.Walk T.branchA M.zSep.left :=
  T.zArmA.takeUntil M.zSep.left M.zSep.left_mem_aArm

/-- The corresponding `B`-side stems, oriented from the second theta
branch vertex to the three `B` attachments. -/
def xBStem : G.Walk T.branchB M.xSep.right :=
  T.xArmB.takeUntil M.xSep.right M.xSep.right_mem_bArm

def yBStem : G.Walk T.branchB M.ySep.right :=
  T.yArmB.takeUntil M.ySep.right M.ySep.right_mem_bArm

def zBStem : G.Walk T.branchB M.zSep.right :=
  T.zArmB.takeUntil M.zSep.right M.zSep.right_mem_bArm

theorem xAStem_subset_route {w : V} (hw : w ∈ M.xAStem.support) :
    w ∈ T.xRoute.support := by
  exact T.xRoute.support_takeUntil_subset_support T.x_mem
    (T.xArmA.support_takeUntil_subset_support M.xSep.left_mem_aArm hw)

theorem yAStem_subset_route {w : V} (hw : w ∈ M.yAStem.support) :
    w ∈ T.yRoute.support := by
  exact T.yRoute.support_takeUntil_subset_support T.y_mem
    (T.yArmA.support_takeUntil_subset_support M.ySep.left_mem_aArm hw)

theorem zAStem_subset_route {w : V} (hw : w ∈ M.zAStem.support) :
    w ∈ T.zRoute.support := by
  exact T.zRoute.support_takeUntil_subset_support T.z_mem
    (T.zArmA.support_takeUntil_subset_support M.zSep.left_mem_aArm hw)

theorem xBStem_subset_route {w : V} (hw : w ∈ M.xBStem.support) :
    w ∈ T.xRoute.support := by
  have hwArm : w ∈ T.xArmB.support :=
    T.xArmB.support_takeUntil_subset_support M.xSep.right_mem_bArm hw
  have hwDrop : w ∈ (T.xRoute.dropUntil x T.x_mem).support := by
    simpa only [WatkinsMesnerK32Source.xArmB, Walk.support_reverse,
      List.mem_reverse] using hwArm
  exact T.xRoute.support_dropUntil_subset_support T.x_mem hwDrop

theorem yBStem_subset_route {w : V} (hw : w ∈ M.yBStem.support) :
    w ∈ T.yRoute.support := by
  have hwArm : w ∈ T.yArmB.support :=
    T.yArmB.support_takeUntil_subset_support M.ySep.right_mem_bArm hw
  have hwDrop : w ∈ (T.yRoute.dropUntil y T.y_mem).support := by
    simpa only [WatkinsMesnerK32Source.yArmB, Walk.support_reverse,
      List.mem_reverse] using hwArm
  exact T.yRoute.support_dropUntil_subset_support T.y_mem hwDrop

theorem zBStem_subset_route {w : V} (hw : w ∈ M.zBStem.support) :
    w ∈ T.zRoute.support := by
  have hwArm : w ∈ T.zArmB.support :=
    T.zArmB.support_takeUntil_subset_support M.zSep.right_mem_bArm hw
  have hwDrop : w ∈ (T.zRoute.dropUntil z T.z_mem).support := by
    simpa only [WatkinsMesnerK32Source.zArmB, Walk.support_reverse,
      List.mem_reverse] using hwArm
  exact T.zRoute.support_dropUntil_subset_support T.z_mem hwDrop

private theorem zBStem_inter_xBStem_only_branchB {w : V}
    (hwZ : w ∈ M.zBStem.support) (hwX : w ∈ M.xBStem.support) :
    w = T.branchB := by
  have hwZRoute := M.zBStem_subset_route hwZ
  have hwXRoute := M.xBStem_subset_route hwX
  rcases T.xRoute_inter_zRoute w hwXRoute hwZRoute with hA | hB
  · subst w
    have hright : T.branchA ∈
        (T.zRoute.dropUntil z T.z_mem).reverse.support := by
      have hArm : T.branchA ∈ T.zArmB.support :=
        T.zArmB.support_takeUntil_subset_support M.zSep.right_mem_bArm hwZ
      simpa only [WatkinsMesnerK32Source.zArmB] using hArm
    have hleft : T.branchA ∈
        (T.zRoute.takeUntil z T.z_mem).support :=
      (T.zRoute.takeUntil z T.z_mem).start_mem_support
    exact (T.z_internal.1
      (Walk.IsPath.takeUntil_inter_reverse_dropUntil_only
        T.zRoute_isPath T.z_mem T.branchA hleft hright).symm).elim
  · exact hB

private theorem zBStem_inter_yBStem_only_branchB {w : V}
    (hwZ : w ∈ M.zBStem.support) (hwY : w ∈ M.yBStem.support) :
    w = T.branchB := by
  have hwZRoute := M.zBStem_subset_route hwZ
  have hwYRoute := M.yBStem_subset_route hwY
  rcases T.yRoute_inter_zRoute w hwYRoute hwZRoute with hA | hB
  · subst w
    have hright : T.branchA ∈
        (T.zRoute.dropUntil z T.z_mem).reverse.support := by
      have hArm : T.branchA ∈ T.zArmB.support :=
        T.zArmB.support_takeUntil_subset_support M.zSep.right_mem_bArm hwZ
      simpa only [WatkinsMesnerK32Source.zArmB] using hArm
    have hleft : T.branchA ∈
        (T.zRoute.takeUntil z T.z_mem).support :=
      (T.zRoute.takeUntil z T.z_mem).start_mem_support
    exact (T.z_internal.1
      (Walk.IsPath.takeUntil_inter_reverse_dropUntil_only
        T.zRoute_isPath T.z_mem T.branchA hleft hright).symm).elim
  · exact hB

private theorem xBStem_inter_yBStem_only_branchB {w : V}
    (hwX : w ∈ M.xBStem.support) (hwY : w ∈ M.yBStem.support) :
    w = T.branchB := by
  have hwXRoute := M.xBStem_subset_route hwX
  have hwYRoute := M.yBStem_subset_route hwY
  rcases T.xRoute_inter_yRoute w hwXRoute hwYRoute with hA | hB
  · subst w
    have hright : T.branchA ∈
        (T.xRoute.dropUntil x T.x_mem).reverse.support := by
      have hArm : T.branchA ∈ T.xArmB.support :=
        T.xArmB.support_takeUntil_subset_support M.xSep.right_mem_bArm hwX
      simpa only [WatkinsMesnerK32Source.xArmB] using hArm
    have hleft : T.branchA ∈
        (T.xRoute.takeUntil x T.x_mem).support :=
      (T.xRoute.takeUntil x T.x_mem).start_mem_support
    exact (T.x_internal.1
      (Walk.IsPath.takeUntil_inter_reverse_dropUntil_only
        T.xRoute_isPath T.x_mem T.branchA hleft hright).symm).elim
  · exact hB

/-- The two explicit right-side paths used to localize a singleton
separator in condition (v). -/
def zBToXBStemPath : G.Walk M.zSep.right M.xSep.right :=
  M.zBStem.reverse.append M.xBStem

def zBToYBStemPath : G.Walk M.zSep.right M.ySep.right :=
  M.zBStem.reverse.append M.yBStem

theorem zBToXBStemPath_isPath : M.zBToXBStemPath.IsPath := by
  apply Walk.IsPath.append_of_meet_only_endpoint_wm
    (((T.zRoute_isPath.dropUntil T.z_mem).reverse
      ).takeUntil M.zSep.right_mem_bArm).reverse
    (((T.xRoute_isPath.dropUntil T.x_mem).reverse
      ).takeUntil M.xSep.right_mem_bArm)
  intro w hwZ hwX
  apply zBStem_inter_xBStem_only_branchB (M := M)
  · change w ∈ M.zBStem.reverse.support at hwZ
    simpa only [Walk.support_reverse, List.mem_reverse] using hwZ
  · exact hwX

theorem zBToYBStemPath_isPath : M.zBToYBStemPath.IsPath := by
  apply Walk.IsPath.append_of_meet_only_endpoint_wm
    (((T.zRoute_isPath.dropUntil T.z_mem).reverse
      ).takeUntil M.zSep.right_mem_bArm).reverse
    (((T.yRoute_isPath.dropUntil T.y_mem).reverse
      ).takeUntil M.ySep.right_mem_bArm)
  intro w hwZ hwY
  apply zBStem_inter_yBStem_only_branchB (M := M)
  · change w ∈ M.zBStem.reverse.support at hwZ
    simpa only [Walk.support_reverse, List.mem_reverse] using hwZ
  · exact hwY

theorem mem_zBStem_of_mem_both_stem_paths {w : V}
    (hwX : w ∈ M.zBToXBStemPath.support)
    (hwY : w ∈ M.zBToYBStemPath.support) :
    w ∈ M.zBStem.support := by
  have hxCases : w ∈ M.zBStem.reverse.support ∨ w ∈ M.xBStem.support := by
    simpa only [zBToXBStemPath, Walk.mem_support_append_iff] using hwX
  have hyCases : w ∈ M.zBStem.reverse.support ∨ w ∈ M.yBStem.support := by
    simpa only [zBToYBStemPath, Walk.mem_support_append_iff] using hwY
  rcases hxCases with hwZ | hwX <;> rcases hyCases with hwZ' | hwY
  · simpa only [Walk.support_reverse, List.mem_reverse] using hwZ
  · simpa only [Walk.support_reverse, List.mem_reverse] using hwZ
  · simpa only [Walk.support_reverse, List.mem_reverse] using hwZ'
  · have hwB := xBStem_inter_yBStem_only_branchB (M := M) hwX hwY
    simpa only [hwB, zBStem] using M.zBStem.start_mem_support

theorem xAStem_disjoint_xPart :
    Disjoint M.xAStem.toSubgraph.verts (M.xPart : Set V) := by
  rw [Set.disjoint_left]
  intro w hwStem hwPart
  simp only [Walk.mem_verts_toSubgraph] at hwStem
  apply M.xSep.aPrefix_outside_side
      (T.xRoute_isPath.takeUntil T.x_mem) T.xRim.start_mem_support
      (fun v hvA hvB ↦ Walk.IsPath.takeUntil_inter_reverse_dropUntil_only
        T.xRoute_isPath T.x_mem v hvA hvB) w hwStem
  exact mem_componentCarrier.mp (by simpa only [Finset.mem_coe, xPart] using hwPart)

theorem xBStem_disjoint_xPart :
    Disjoint M.xBStem.toSubgraph.verts (M.xPart : Set V) := by
  rw [Set.disjoint_left]
  intro w hwStem hwPart
  simp only [Walk.mem_verts_toSubgraph] at hwStem
  apply M.xSep.bPrefix_outside_side
      (T.xRoute_isPath.dropUntil T.x_mem).reverse
      (by simp [WatkinsMesnerK32Source.xRim])
      (fun v hvA hvB ↦ Walk.IsPath.takeUntil_inter_reverse_dropUntil_only
        T.xRoute_isPath T.x_mem v hvA hvB) w hwStem
  exact mem_componentCarrier.mp (by simpa only [Finset.mem_coe, xPart] using hwPart)

theorem yAStem_disjoint_yPart :
    Disjoint M.yAStem.toSubgraph.verts (M.yPart : Set V) := by
  rw [Set.disjoint_left]
  intro w hwStem hwPart
  simp only [Walk.mem_verts_toSubgraph] at hwStem
  apply M.ySep.aPrefix_outside_side
      (T.yRoute_isPath.takeUntil T.y_mem) T.yRim.start_mem_support
      (fun v hvA hvB ↦ Walk.IsPath.takeUntil_inter_reverse_dropUntil_only
        T.yRoute_isPath T.y_mem v hvA hvB) w hwStem
  exact mem_componentCarrier.mp (by simpa only [Finset.mem_coe, yPart] using hwPart)

theorem yBStem_disjoint_yPart :
    Disjoint M.yBStem.toSubgraph.verts (M.yPart : Set V) := by
  rw [Set.disjoint_left]
  intro w hwStem hwPart
  simp only [Walk.mem_verts_toSubgraph] at hwStem
  apply M.ySep.bPrefix_outside_side
      (T.yRoute_isPath.dropUntil T.y_mem).reverse
      (by simp [WatkinsMesnerK32Source.yRim])
      (fun v hvA hvB ↦ Walk.IsPath.takeUntil_inter_reverse_dropUntil_only
        T.yRoute_isPath T.y_mem v hvA hvB) w hwStem
  exact mem_componentCarrier.mp (by simpa only [Finset.mem_coe, yPart] using hwPart)

theorem zAStem_disjoint_zPart :
    Disjoint M.zAStem.toSubgraph.verts (M.zPart : Set V) := by
  rw [Set.disjoint_left]
  intro w hwStem hwPart
  simp only [Walk.mem_verts_toSubgraph] at hwStem
  apply M.zSep.aPrefix_outside_side
      (T.zRoute_isPath.takeUntil T.z_mem) T.zRim.start_mem_support
      (fun v hvA hvB ↦ Walk.IsPath.takeUntil_inter_reverse_dropUntil_only
        T.zRoute_isPath T.z_mem v hvA hvB) w hwStem
  exact mem_componentCarrier.mp (by simpa only [Finset.mem_coe, zPart] using hwPart)

theorem zBStem_disjoint_zPart :
    Disjoint M.zBStem.toSubgraph.verts (M.zPart : Set V) := by
  rw [Set.disjoint_left]
  intro w hwStem hwPart
  simp only [Walk.mem_verts_toSubgraph] at hwStem
  apply M.zSep.bPrefix_outside_side
      (T.zRoute_isPath.dropUntil T.z_mem).reverse
      (by simp [WatkinsMesnerK32Source.zRim])
      (fun v hvA hvB ↦ Walk.IsPath.takeUntil_inter_reverse_dropUntil_only
        T.zRoute_isPath T.z_mem v hvA hvB) w hwStem
  exact mem_componentCarrier.mp (by simpa only [Finset.mem_coe, zPart] using hwPart)

def initialAGraph : G.Subgraph :=
  M.xAStem.toSubgraph ⊔ M.yAStem.toSubgraph ⊔ M.zAStem.toSubgraph

def initialBGraph : G.Subgraph :=
  M.xBStem.toSubgraph ⊔ M.yBStem.toSubgraph ⊔ M.zBStem.toSubgraph

private theorem leftStem_disjoint_rightStem_sameRoute
    {A B p l r : V} (P : G.Walk A B) (hP : P.IsPath)
    (hp : p ∈ P.support)
    (hl : l ∈ (P.takeUntil p hp).support)
    (hr : r ∈ (P.dropUntil p hp).reverse.support) (hlp : l ≠ p) :
    Disjoint
      ((P.takeUntil p hp).takeUntil l hl).toSubgraph.verts
      ((P.dropUntil p hp).reverse.takeUntil r hr).toSubgraph.verts := by
  rw [Set.disjoint_left]
  intro w hwL hwR
  simp only [Walk.mem_verts_toSubgraph] at hwL hwR
  have hwLt : w ∈ (P.takeUntil p hp).support :=
    (P.takeUntil p hp).support_takeUntil_subset_support hl hwL
  have hwRt : w ∈ (P.dropUntil p hp).reverse.support :=
    (P.dropUntil p hp).reverse.support_takeUntil_subset_support hr hwR
  have hwp := Walk.IsPath.takeUntil_inter_reverse_dropUntil_only
    hP hp w hwLt hwRt
  exact (Walk.endpoint_notMem_support_takeUntil (hP.takeUntil hp) hl hlp.symm
    (hwp ▸ hwL)).elim

private theorem leftStem_disjoint_rightStem_distinctRoutes
    {A B p q l r : V} (P Q : G.Walk A B)
    (hP : P.IsPath) (hQ : Q.IsPath)
    (hp : p ∈ P.support) (hq : q ∈ Q.support)
    (hpB : p ≠ B) (hqA : q ≠ A)
    (hmeet : ∀ w, w ∈ P.support → w ∈ Q.support → w = A ∨ w = B)
    (hl : l ∈ (P.takeUntil p hp).support)
    (hr : r ∈ (Q.dropUntil q hq).reverse.support) :
    Disjoint
      ((P.takeUntil p hp).takeUntil l hl).toSubgraph.verts
      ((Q.dropUntil q hq).reverse.takeUntil r hr).toSubgraph.verts := by
  rw [Set.disjoint_left]
  intro w hwL hwR
  simp only [Walk.mem_verts_toSubgraph] at hwL hwR
  have hwPt : w ∈ (P.takeUntil p hp).support :=
    (P.takeUntil p hp).support_takeUntil_subset_support hl hwL
  have hwP : w ∈ P.support := P.support_takeUntil_subset_support hp hwPt
  have hwQr : w ∈ (Q.dropUntil q hq).reverse.support :=
    (Q.dropUntil q hq).reverse.support_takeUntil_subset_support hr hwR
  have hwQd : w ∈ (Q.dropUntil q hq).support := by
    simpa only [Walk.support_reverse, List.mem_reverse] using hwQr
  have hwQ : w ∈ Q.support := Q.support_dropUntil_subset_support hq hwQd
  rcases hmeet w hwP hwQ with hA | hB
  · have hAt : A ∈ (Q.takeUntil q hq).support :=
      (Q.takeUntil q hq).start_mem_support
    have hAr : A ∈ (Q.dropUntil q hq).reverse.support := hA ▸ hwQr
    have hAq := Walk.IsPath.takeUntil_inter_reverse_dropUntil_only
      hQ hq A hAt hAr
    exact hqA hAq.symm
  · have hBr : B ∈ (P.dropUntil p hp).reverse.support :=
      (P.dropUntil p hp).reverse.start_mem_support
    have hBp := Walk.IsPath.takeUntil_inter_reverse_dropUntil_only
      hP hp B (hB ▸ hwPt) hBr
    exact hpB hBp.symm

theorem initialAGraph_connected : M.initialAGraph.Connected := by
  apply Subgraph.connected_sup
  · exact (Subgraph.connected_sup
      M.xAStem.toSubgraph_connected.preconnected
      M.yAStem.toSubgraph_connected.preconnected
      ⟨T.branchA, by simp [xAStem, yAStem]⟩).preconnected
  · exact M.zAStem.toSubgraph_connected.preconnected
  · exact ⟨T.branchA, by simp [initialAGraph, xAStem, yAStem, zAStem]⟩

theorem initialBGraph_connected : M.initialBGraph.Connected := by
  apply Subgraph.connected_sup
  · exact (Subgraph.connected_sup
      M.xBStem.toSubgraph_connected.preconnected
      M.yBStem.toSubgraph_connected.preconnected
      ⟨T.branchB, by simp [xBStem, yBStem]⟩).preconnected
  · exact M.zBStem.toSubgraph_connected.preconnected
  · exact ⟨T.branchB, by simp [initialBGraph, xBStem, yBStem, zBStem]⟩

theorem aSet_subset_initialAGraph :
    ∀ a ∈ M.aSet, a ∈ M.initialAGraph.verts := by
  intro a ha
  have hcases : a = M.xSep.left ∨ a = M.ySep.left ∨
      a = M.zSep.left := by simpa [aSet] using ha
  rcases hcases with rfl | rfl | rfl
  · simp [initialAGraph, xAStem]
  · simp [initialAGraph, yAStem]
  · simp [initialAGraph, zAStem]

theorem bSet_subset_initialBGraph :
    ∀ b ∈ M.bSet, b ∈ M.initialBGraph.verts := by
  intro b hb
  have hcases : b = M.xSep.right ∨ b = M.ySep.right ∨
      b = M.zSep.right := by simpa [bSet] using hb
  rcases hcases with rfl | rfl | rfl
  · simp [initialBGraph, xBStem]
  · simp [initialBGraph, yBStem]
  · simp [initialBGraph, zBStem]

theorem initialGraphs_vertex_disjoint :
    Disjoint M.initialAGraph.verts M.initialBGraph.verts := by
  rw [Set.disjoint_left]
  intro w hwA hwB
  simp only [initialAGraph, initialBGraph, Subgraph.verts_sup,
    Set.mem_union] at hwA hwB
  rcases hwA with (hxA | hyA) | hzA <;>
    rcases hwB with (hxB | hyB) | hzB
  · exact Set.disjoint_left.mp
      (leftStem_disjoint_rightStem_sameRoute T.xRoute T.xRoute_isPath
        T.x_mem M.xSep.left_mem_aArm M.xSep.right_mem_bArm
        M.xSep.left_ne_terminal) hxA hxB
  · exact Set.disjoint_left.mp
      (leftStem_disjoint_rightStem_distinctRoutes T.xRoute T.yRoute
        T.xRoute_isPath T.yRoute_isPath T.x_mem T.y_mem
        T.x_internal.2 T.y_internal.1 T.xRoute_inter_yRoute
        M.xSep.left_mem_aArm M.ySep.right_mem_bArm) hxA hyB
  · exact Set.disjoint_left.mp
      (leftStem_disjoint_rightStem_distinctRoutes T.xRoute T.zRoute
        T.xRoute_isPath T.zRoute_isPath T.x_mem T.z_mem
        T.x_internal.2 T.z_internal.1 T.xRoute_inter_zRoute
        M.xSep.left_mem_aArm M.zSep.right_mem_bArm) hxA hzB
  · exact Set.disjoint_left.mp
      (leftStem_disjoint_rightStem_distinctRoutes T.yRoute T.xRoute
        T.yRoute_isPath T.xRoute_isPath T.y_mem T.x_mem
        T.y_internal.2 T.x_internal.1
        (fun v hvY hvX ↦ T.xRoute_inter_yRoute v hvX hvY)
        M.ySep.left_mem_aArm M.xSep.right_mem_bArm) hyA hxB
  · exact Set.disjoint_left.mp
      (leftStem_disjoint_rightStem_sameRoute T.yRoute T.yRoute_isPath
        T.y_mem M.ySep.left_mem_aArm M.ySep.right_mem_bArm
        M.ySep.left_ne_terminal) hyA hyB
  · exact Set.disjoint_left.mp
      (leftStem_disjoint_rightStem_distinctRoutes T.yRoute T.zRoute
        T.yRoute_isPath T.zRoute_isPath T.y_mem T.z_mem
        T.y_internal.2 T.z_internal.1 T.yRoute_inter_zRoute
        M.ySep.left_mem_aArm M.zSep.right_mem_bArm) hyA hzB
  · exact Set.disjoint_left.mp
      (leftStem_disjoint_rightStem_distinctRoutes T.zRoute T.xRoute
        T.zRoute_isPath T.xRoute_isPath T.z_mem T.x_mem
        T.z_internal.2 T.x_internal.1
        (fun v hvZ hvX ↦ T.xRoute_inter_zRoute v hvX hvZ)
        M.zSep.left_mem_aArm M.xSep.right_mem_bArm) hzA hxB
  · exact Set.disjoint_left.mp
      (leftStem_disjoint_rightStem_distinctRoutes T.zRoute T.yRoute
        T.zRoute_isPath T.yRoute_isPath T.z_mem T.y_mem
        T.z_internal.2 T.y_internal.1
        (fun v hvZ hvY ↦ T.yRoute_inter_zRoute v hvY hvZ)
        M.zSep.left_mem_aArm M.ySep.right_mem_bArm) hzA hyB
  · exact Set.disjoint_left.mp
      (leftStem_disjoint_rightStem_sameRoute T.zRoute T.zRoute_isPath
        T.z_mem M.zSep.left_mem_aArm M.zSep.right_mem_bArm
        M.zSep.left_ne_terminal) hzA hzB

theorem initialAGraph_disjoint_xPart :
    Disjoint M.initialAGraph.verts (M.xPart : Set V) := by
  rw [Set.disjoint_left]
  intro w hw hwX
  simp only [initialAGraph, Subgraph.verts_sup, Set.mem_union] at hw
  rcases hw with (hx | hy) | hz
  · exact Set.disjoint_left.mp M.xAStem_disjoint_xPart hx hwX
  · apply M.xSep.not_mem_componentCarrier_of_mem_rim
        (xRim_mem_of_yRoute_mem (M.yAStem_subset_route (by
          simpa only [Walk.mem_verts_toSubgraph] using hy)))
    simpa only [Finset.mem_coe, xPart] using hwX
  · apply M.xSep.not_mem_componentCarrier_of_mem_rim
        (xRim_mem_of_zRoute_mem (M.zAStem_subset_route (by
          simpa only [Walk.mem_verts_toSubgraph] using hz)))
    simpa only [Finset.mem_coe, xPart] using hwX

theorem initialBGraph_disjoint_xPart :
    Disjoint M.initialBGraph.verts (M.xPart : Set V) := by
  rw [Set.disjoint_left]
  intro w hw hwX
  simp only [initialBGraph, Subgraph.verts_sup, Set.mem_union] at hw
  rcases hw with (hx | hy) | hz
  · exact Set.disjoint_left.mp M.xBStem_disjoint_xPart hx hwX
  · apply M.xSep.not_mem_componentCarrier_of_mem_rim
        (xRim_mem_of_yRoute_mem (M.yBStem_subset_route (by
          simpa only [Walk.mem_verts_toSubgraph] using hy)))
    simpa only [Finset.mem_coe, xPart] using hwX
  · apply M.xSep.not_mem_componentCarrier_of_mem_rim
        (xRim_mem_of_zRoute_mem (M.zBStem_subset_route (by
          simpa only [Walk.mem_verts_toSubgraph] using hz)))
    simpa only [Finset.mem_coe, xPart] using hwX

theorem initialAGraph_disjoint_yPart :
    Disjoint M.initialAGraph.verts (M.yPart : Set V) := by
  rw [Set.disjoint_left]
  intro w hw hwY
  simp only [initialAGraph, Subgraph.verts_sup, Set.mem_union] at hw
  rcases hw with (hx | hy) | hz
  · apply M.ySep.not_mem_componentCarrier_of_mem_rim
        (yRim_mem_of_xRoute_mem (M.xAStem_subset_route (by
          simpa only [Walk.mem_verts_toSubgraph] using hx)))
    simpa only [Finset.mem_coe, yPart] using hwY
  · exact Set.disjoint_left.mp M.yAStem_disjoint_yPart hy hwY
  · apply M.ySep.not_mem_componentCarrier_of_mem_rim
        (yRim_mem_of_zRoute_mem (M.zAStem_subset_route (by
          simpa only [Walk.mem_verts_toSubgraph] using hz)))
    simpa only [Finset.mem_coe, yPart] using hwY

theorem initialBGraph_disjoint_yPart :
    Disjoint M.initialBGraph.verts (M.yPart : Set V) := by
  rw [Set.disjoint_left]
  intro w hw hwY
  simp only [initialBGraph, Subgraph.verts_sup, Set.mem_union] at hw
  rcases hw with (hx | hy) | hz
  · apply M.ySep.not_mem_componentCarrier_of_mem_rim
        (yRim_mem_of_xRoute_mem (M.xBStem_subset_route (by
          simpa only [Walk.mem_verts_toSubgraph] using hx)))
    simpa only [Finset.mem_coe, yPart] using hwY
  · exact Set.disjoint_left.mp M.yBStem_disjoint_yPart hy hwY
  · apply M.ySep.not_mem_componentCarrier_of_mem_rim
        (yRim_mem_of_zRoute_mem (M.zBStem_subset_route (by
          simpa only [Walk.mem_verts_toSubgraph] using hz)))
    simpa only [Finset.mem_coe, yPart] using hwY

theorem initialAGraph_disjoint_zPart :
    Disjoint M.initialAGraph.verts (M.zPart : Set V) := by
  rw [Set.disjoint_left]
  intro w hw hwZ
  simp only [initialAGraph, Subgraph.verts_sup, Set.mem_union] at hw
  rcases hw with (hx | hy) | hz
  · apply M.zSep.not_mem_componentCarrier_of_mem_rim
        (zRim_mem_of_xRoute_mem (M.xAStem_subset_route (by
          simpa only [Walk.mem_verts_toSubgraph] using hx)))
    simpa only [Finset.mem_coe, zPart] using hwZ
  · apply M.zSep.not_mem_componentCarrier_of_mem_rim
        (zRim_mem_of_yRoute_mem (M.yAStem_subset_route (by
          simpa only [Walk.mem_verts_toSubgraph] using hy)))
    simpa only [Finset.mem_coe, zPart] using hwZ
  · exact Set.disjoint_left.mp M.zAStem_disjoint_zPart hz hwZ

theorem initialBGraph_disjoint_zPart :
    Disjoint M.initialBGraph.verts (M.zPart : Set V) := by
  rw [Set.disjoint_left]
  intro w hw hwZ
  simp only [initialBGraph, Subgraph.verts_sup, Set.mem_union] at hw
  rcases hw with (hx | hy) | hz
  · apply M.zSep.not_mem_componentCarrier_of_mem_rim
        (zRim_mem_of_xRoute_mem (M.xBStem_subset_route (by
          simpa only [Walk.mem_verts_toSubgraph] using hx)))
    simpa only [Finset.mem_coe, zPart] using hwZ
  · apply M.zSep.not_mem_componentCarrier_of_mem_rim
        (zRim_mem_of_yRoute_mem (M.yBStem_subset_route (by
          simpa only [Walk.mem_verts_toSubgraph] using hy)))
    simpa only [Finset.mem_coe, zPart] using hwZ
  · exact Set.disjoint_left.mp M.zBStem_disjoint_zPart hz hwZ

theorem zBToXBStemPath_subset_initialBGraph {w : V}
    (hw : w ∈ M.zBToXBStemPath.support) :
    w ∈ M.initialBGraph.verts := by
  have hw' : w ∈ M.zBStem.reverse.support ∨ w ∈ M.xBStem.support := by
    simpa only [zBToXBStemPath, Walk.mem_support_append_iff] using hw
  rcases hw' with hwZ | hwX
  · have : w ∈ M.zBStem.toSubgraph.verts := by
      simp only [Walk.mem_verts_toSubgraph, Walk.support_reverse,
        List.mem_reverse] at hwZ ⊢
      exact hwZ
    simp only [initialBGraph, Subgraph.verts_sup, Set.mem_union]
    exact Or.inr this
  · have : w ∈ M.xBStem.toSubgraph.verts := by
      simpa only [Walk.mem_verts_toSubgraph] using hwX
    simp only [initialBGraph, Subgraph.verts_sup, Set.mem_union]
    exact Or.inl (Or.inl this)

theorem zBToYBStemPath_subset_initialBGraph {w : V}
    (hw : w ∈ M.zBToYBStemPath.support) :
    w ∈ M.initialBGraph.verts := by
  have hw' : w ∈ M.zBStem.reverse.support ∨ w ∈ M.yBStem.support := by
    simpa only [zBToYBStemPath, Walk.mem_support_append_iff] using hw
  rcases hw' with hwZ | hwY
  · have : w ∈ M.zBStem.toSubgraph.verts := by
      simp only [Walk.mem_verts_toSubgraph, Walk.support_reverse,
        List.mem_reverse] at hwZ ⊢
      exact hwZ
    simp only [initialBGraph, Subgraph.verts_sup, Set.mem_union]
    exact Or.inr this
  · have : w ∈ M.yBStem.toSubgraph.verts := by
      simpa only [Walk.mem_verts_toSubgraph] using hwY
    simp only [initialBGraph, Subgraph.verts_sup, Set.mem_union]
    exact Or.inl (Or.inr this)

theorem zBToXBStemPath_avoids_zPart {w : V}
    (hw : w ∈ M.zBToXBStemPath.support) : w ∉ M.zPart := by
  intro hwZ
  exact Set.disjoint_left.mp M.initialBGraph_disjoint_zPart
    (M.zBToXBStemPath_subset_initialBGraph hw) hwZ

theorem zBToYBStemPath_avoids_zPart {w : V}
    (hw : w ∈ M.zBToYBStemPath.support) : w ∉ M.zPart := by
  intro hwZ
  exact Set.disjoint_left.mp M.initialBGraph_disjoint_zPart
    (M.zBToYBStemPath_subset_initialBGraph hw) hwZ

theorem zBToXBStemPath_avoids_xA {w : V}
    (hw : w ∈ M.zBToXBStemPath.support) : w ≠ M.xSep.left := by
  intro h
  subst w
  exact Set.disjoint_left.mp M.initialGraphs_vertex_disjoint
    (M.aSet_subset_initialAGraph M.xSep.left M.xA_mem_aSet)
    (M.zBToXBStemPath_subset_initialBGraph hw)

theorem zBToYBStemPath_avoids_xA {w : V}
    (hw : w ∈ M.zBToYBStemPath.support) : w ≠ M.xSep.left := by
  intro h
  subst w
  exact Set.disjoint_left.mp M.initialGraphs_vertex_disjoint
    (M.aSet_subset_initialAGraph M.xSep.left M.xA_mem_aSet)
    (M.zBToYBStemPath_subset_initialBGraph hw)

/-- AHT p.14, localization of the hypothetical one-vertex separator in
condition (v).  The two displayed paths from `zB` to `xB` and `yB` both
lie in `G - (Z ∪ {xA})`.  Hence a singleton separating
`{zA,zB}` from `{xB,yB}` meets both paths; their only common vertices are
on the `zB` stem. -/
theorem mem_zBStem_of_conditionV_singleton_separator
    (hzA : M.zSep.left ≠ M.xSep.left)
    (u : {w : V // w ∉ M.zPart ∧ w ≠ M.xSep.left})
    (hsep : Erdos599.Countable.Separates M.conditionVGraph
      ({M.conditionVZA hzA, M.conditionVZB} : Set
        {w : V // w ∉ M.zPart ∧ w ≠ M.xSep.left})
      ({M.conditionVXB, M.conditionVYB} : Set
        {w : V // w ∉ M.zPart ∧ w ≠ M.xSep.left})
      ({u} : Set {w : V // w ∉ M.zPart ∧ w ≠ M.xSep.left})) :
    u.1 ∈ M.zBStem.support := by
  classical
  let pX₀ := M.zBToXBStemPath.induce
    {w : V | w ∉ M.zPart ∧ w ≠ M.xSep.left}
    (fun w hw ↦ ⟨M.zBToXBStemPath_avoids_zPart hw,
      M.zBToXBStemPath_avoids_xA hw⟩)
  let pX : M.conditionVGraph.Walk M.conditionVZB M.conditionVXB :=
    pX₀.copy (Subtype.ext rfl) (Subtype.ext rfl)
  let pY₀ := M.zBToYBStemPath.induce
    {w : V | w ∉ M.zPart ∧ w ≠ M.xSep.left}
    (fun w hw ↦ ⟨M.zBToYBStemPath_avoids_zPart hw,
      M.zBToYBStemPath_avoids_xA hw⟩)
  let pY : M.conditionVGraph.Walk M.conditionVZB M.conditionVYB :=
    pY₀.copy (Subtype.ext rfl) (Subtype.ext rfl)
  let inc : M.conditionVGraph →g G :=
    (SimpleGraph.Embedding.induce
      (G := G) (s := {w : V | w ∉ M.zPart ∧ w ≠ M.xSep.left})).toHom
  have hmapX : pX.map inc = M.zBToXBStemPath := by
    simp only [pX, pX₀, inc, Walk.map_copy]
    exact Walk.map_induce
      (s := {w : V | w ∉ M.zPart ∧ w ≠ M.xSep.left})
      M.zBToXBStemPath
      (fun w hw ↦ ⟨M.zBToXBStemPath_avoids_zPart hw,
        M.zBToXBStemPath_avoids_xA hw⟩)
  have hmapY : pY.map inc = M.zBToYBStemPath := by
    simp only [pY, pY₀, inc, Walk.map_copy]
    exact Walk.map_induce
      (s := {w : V | w ∉ M.zPart ∧ w ≠ M.xSep.left})
      M.zBToYBStemPath
      (fun w hw ↦ ⟨M.zBToYBStemPath_avoids_zPart hw,
        M.zBToYBStemPath_avoids_xA hw⟩)
  have hpX : pX.IsPath := by
    apply Walk.IsPath.of_map (f := inc)
    rw [hmapX]
    exact M.zBToXBStemPath_isPath
  have hpY : pY.IsPath := by
    apply Walk.IsPath.of_map (f := inc)
    rw [hmapY]
    exact M.zBToYBStemPath_isPath
  obtain ⟨vX, hvXp, hvXu⟩ := hsep M.conditionVZB (by simp)
    M.conditionVXB (by simp) pX hpX
  obtain ⟨vY, hvYp, hvYu⟩ := hsep M.conditionVZB (by simp)
    M.conditionVYB (by simp) pY hpY
  have hvXeq : vX = u := by simpa only [Set.mem_singleton_iff] using hvXu
  have hvYeq : vY = u := by simpa only [Set.mem_singleton_iff] using hvYu
  subst vX
  subst vY
  have huX : u.1 ∈ M.zBToXBStemPath.support := by
    have : u.1 ∈ (pX.map inc).support := by
      rw [Walk.support_map]
      exact List.mem_map.mpr ⟨u, hvXp, rfl⟩
    rwa [hmapX] at this
  have huY : u.1 ∈ M.zBToYBStemPath.support := by
    have : u.1 ∈ (pY.map inc).support := by
      rw [Walk.support_map]
      exact List.mem_map.mpr ⟨u, hvYp, rfl⟩
    rwa [hmapY] at this
  exact M.mem_zBStem_of_mem_both_stem_paths huX huY

/-- Strict maximality half of the condition-(v) exchange.  Once the
component of `z` after deleting `{xA,u}` misses the `z`-rim, it is a routed
`z`-separator strictly larger than the old one: the old side is contained
in it and the old boundary vertex `zA` has joined it. -/
theorem false_of_conditionV_replacement_rim_free
    (hdelete : ∀ d : V, (G.induce fun w : V ↦ w ≠ d).Connected)
    (hxyA : M.xSep.left = M.ySep.left)
    (hzA : M.zSep.left ≠ M.xSep.left)
    (u : {w : V // w ∉ M.zPart ∧ w ≠ M.xSep.left})
    (huStem : u.1 ∈ M.zBStem.support)
    (hrim : ∀ (hzLeft : z ≠ M.xSep.left) (hzRight : z ≠ u.1),
      let D : G.ComponentCompl
          ((({M.xSep.left, u.1} : Finset V) : Set V)) :=
        G.componentComplMk (by
          simp only [Finset.mem_coe, Finset.mem_insert,
            Finset.mem_singleton, not_or]
          exact ⟨hzLeft, hzRight⟩)
      ∀ w, w ∈ T.zRim.support → w ≠ M.xSep.left → w ≠ u.1 →
        w ∉ (D : Set V)) : False := by
  classical
  have hbranchA : M.xSep.left = T.branchA :=
    M.xA_eq_yA_imp_branchA hxyA
  have hzLeft : z ≠ M.xSep.left := by
    intro h
    exact T.z_internal.1 (h.trans hbranchA)
  have hzNotStem : z ∉ M.zBStem.support := by
    apply Walk.endpoint_notMem_support_takeUntil
      ((T.zRoute_isPath.dropUntil T.z_mem).reverse)
      M.zSep.right_mem_bArm M.zSep.right_ne_terminal.symm
  have hzRight : z ≠ u.1 := by
    intro h
    apply hzNotStem
    exact (congrArg (fun v : V ↦ v ∈ M.zBStem.support) h.symm).mp huStem
  have hzAvoid : z ∉
      ((({M.xSep.left, u.1} : Finset V) : Set V)) := by
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton,
      not_or]
    exact ⟨hzLeft, hzRight⟩
  let D : G.ComponentCompl
      ((({M.xSep.left, u.1} : Finset V) : Set V)) :=
    G.componentComplMk hzAvoid
  have hzD : z ∈ (D : Set V) := ⟨hzAvoid, rfl⟩
  have hdisOldNew : Disjoint (M.zSep.side : Set V)
      ((({M.xSep.left, u.1} : Finset V) : Set V)) := by
    rw [Set.disjoint_left]
    intro v hvSide hvPair
    have hvPart : v ∈ M.zPart := by
      simpa only [zPart, mem_componentCarrier] using hvSide
    simp only [Finset.mem_coe, Finset.mem_insert,
      Finset.mem_singleton] at hvPair
    rcases hvPair with rfl | rfl
    · exact Finset.disjoint_left.mp M.zPart_disjoint_aSet
        hvPart M.xA_mem_aSet
    · exact u.2.1 hvPart
  have hsub : (M.zSep.side : Set V) ⊆ (D : Set V) :=
    ComponentCompl.subset_of_disjoint_of_shared M.zSep.side D
      hdisOldNew M.zSep.x_mem_side hzD
  obtain ⟨v, hvSide, hvAdj⟩ :=
    (ComponentCompl.exists_adj_to_each_of_delete_connected
      M.zSep.left_ne_right hdelete M.zSep.side).1
  have hvD : v ∈ (D : Set V) := hsub hvSide
  have hzA_ne_u : M.zSep.left ≠ u.1 := by
    intro h
    have huB : u.1 ∈ M.initialBGraph.verts := by
      simp only [initialBGraph, Subgraph.verts_sup, Set.mem_union]
      exact Or.inr (by
        simpa only [Walk.mem_verts_toSubgraph] using huStem)
    have hzAA : M.zSep.left ∈ M.initialAGraph.verts :=
      M.aSet_subset_initialAGraph M.zSep.left M.zA_mem_aSet
    exact Set.disjoint_left.mp M.initialGraphs_vertex_disjoint hzAA (h ▸ huB)
  have hzAAvoid : M.zSep.left ∉
      ((({M.xSep.left, u.1} : Finset V) : Set V)) := by
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton,
      not_or]
    exact ⟨hzA, hzA_ne_u⟩
  have hzAD : M.zSep.left ∈ (D : Set V) :=
    ComponentCompl.mem_of_adj v M.zSep.left hvD hzAAvoid hvAdj
  have huArm : u.1 ∈ T.zArmB.support :=
    T.zArmB.support_takeUntil_subset_support M.zSep.right_mem_bArm huStem
  let R : RoutedCycleSeparator T.zArmA T.zArmB T.zRim :=
    { left := M.xSep.left
      right := u.1
      left_ne_right := u.2.2.symm
      x_ne_left := hzLeft
      x_ne_right := hzRight
      side := D
      x_mem_side := hzD
      rim_outside_side := by
        intro w hwRim hwLeft hwRight
        exact hrim hzLeft hzRight w hwRim hwLeft hwRight
      left_mem_aArm := by
        simpa only [hbranchA] using T.zArmA.start_mem_support
      left_ne_terminal := hzLeft.symm
      right_mem_bArm := huArm
      right_ne_terminal := hzRight.symm }
  exact M.z_maximal.not_replacement_of_subset_of_left_mem M.zSep R
    hsub hzAD

/-- Every displayed `z`-rim vertex is outside the old terminal component,
including the harmless cases where it is one of the two boundary vertices. -/
theorem not_mem_zPart_of_mem_zRim {w : V} (hw : w ∈ T.zRim.support) :
    w ∉ M.zPart := by
  intro hwZ
  by_cases hwL : w = M.zSep.left
  · subst w
    exact Finset.disjoint_left.mp M.zPart_disjoint_aSet
      hwZ M.zA_mem_aSet
  by_cases hwR : w = M.zSep.right
  · subst w
    exact Finset.disjoint_left.mp M.zPart_disjoint_bSet
      hwZ M.zB_mem_bSet
  apply M.zSep.rim_outside_side w hw hwL hwR
  simpa only [zPart, mem_componentCarrier] using hwZ

/-- First-exit tail used in condition (v).  If a vertex outside the old
`z`-component lies with `z` in the component after deleting `{xA,u}`, then
there is a path from one old boundary vertex `zA` or `zB` to it whose whole
support avoids the old component and both new deleted vertices. -/
theorem exists_conditionV_boundary_tail
    (u : {w : V // w ∉ M.zPart ∧ w ≠ M.xSep.left})
    (hzLeft : z ≠ M.xSep.left) (hzRight : z ≠ u.1)
    {w : V} (hwZ : w ∉ M.zPart)
    (hwD : w ∈ (G.componentComplMk (K :=
      ((({M.xSep.left, u.1} : Finset V) : Set V))) (by
        simp only [Finset.mem_coe, Finset.mem_insert,
          Finset.mem_singleton, not_or]
        exact ⟨hzLeft, hzRight⟩) : Set V)) :
    ∃ s : V, (s = M.zSep.left ∨ s = M.zSep.right) ∧
      ∃ q : G.Walk s w, q.IsPath ∧
        ∀ v, v ∈ q.support →
          v ∉ M.zPart ∧ v ≠ M.xSep.left ∧ v ≠ u.1 := by
  classical
  let K : Set V := ((({M.xSep.left, u.1} : Finset V) : Set V))
  have hzK : z ∉ K := by
    simp only [K, Finset.mem_coe, Finset.mem_insert,
      Finset.mem_singleton, not_or]
    exact ⟨hzLeft, hzRight⟩
  let D : G.ComponentCompl K := G.componentComplMk hzK
  have hzD : z ∈ (D : Set V) := ⟨hzK, rfl⟩
  have hwD' : w ∈ (D : Set V) := by
    simpa only [D, K] using hwD
  have hreach : (G.induce Kᶜ).Reachable
      ⟨w, hwD'.1⟩ ⟨z, hzD.1⟩ := by
    rw [← ConnectedComponent.eq]
    exact hwD'.2.trans hzD.2.symm
  obtain ⟨pD, hpD⟩ := hreach.exists_isPath
  let emb := SimpleGraph.Embedding.induce (G := G) (s := Kᶜ)
  let inc : G.induce Kᶜ →g G := emb.toHom
  let p : G.Walk w z := (pD.map inc).copy rfl rfl
  have hp : p.IsPath := by
    exact (Walk.isPath_copy (pD.map inc) rfl rfl).2
      (hpD.map emb.injective)
  have hpAvoid : ∀ v, v ∈ p.support →
      v ≠ M.xSep.left ∧ v ≠ u.1 := by
    intro v hv
    have hvMap : v ∈ (pD.map inc).support := by
      change v ∈ ((pD.map inc).copy rfl rfl).support at hv
      simpa only [Walk.support_copy] using hv
    rw [Walk.support_map] at hvMap
    obtain ⟨vD, -, rfl⟩ := List.mem_map.mp hvMap
    change vD.1 ≠ M.xSep.left ∧ vD.1 ≠ u.1
    simpa only [inc, K, Set.mem_compl_iff, Finset.mem_coe,
      Finset.mem_insert, Finset.mem_singleton, not_or] using vD.2
  obtain ⟨s, hsZ, q, hq, hqSub, hqFirst⟩ :=
    exists_initialPath_to_finset_wm M.zPart hwZ M.z_mem_zPart p hp
  have hqNotNil : ¬q.Nil := by
    intro hnil
    have hws : w = s := hnil.eq
    exact hwZ (hws ▸ hsZ)
  have hsNotDrop : s ∉ q.dropLast.support := by
    have hnd := hq.support_nodup
    have hsupp := q.support_dropLast_concat hqNotNil
    rw [← hsupp] at hnd
    exact fun hsDrop ↦ hnd.disjoint hsDrop (by simp)
  have hpenDrop : q.penultimate ∈ q.dropLast.support :=
    q.dropLast.end_mem_support
  have hpenQ : q.penultimate ∈ q.support := by
    rw [q.support_dropLast hqNotNil] at hpenDrop
    exact List.mem_of_mem_dropLast hpenDrop
  have hpenNotZ : q.penultimate ∉ M.zPart := by
    intro hpenZ
    have hpenEq : q.penultimate = s := hqFirst q.penultimate hpenQ hpenZ
    apply hsNotDrop
    exact (congrArg (fun v : V ↦ v ∈ q.dropLast.support) hpenEq).mp hpenDrop
  have hpenBoundary : q.penultimate = M.zSep.left ∨
      q.penultimate = M.zSep.right := by
    have hadj : G.Adj s q.penultimate :=
      (q.adj_penultimate hqNotNil).symm
    by_contra h
    push_neg at h
    have hpenAvoid : q.penultimate ∉
        ((({M.zSep.left, M.zSep.right} : Finset V) : Set V)) := by
      simpa only [Finset.mem_coe, Finset.mem_insert,
        Finset.mem_singleton, not_or] using h
    have hsSide : s ∈ (M.zSep.side : Set V) := by
      simpa only [zPart, mem_componentCarrier] using hsZ
    have hpenSide : q.penultimate ∈ (M.zSep.side : Set V) :=
      ComponentCompl.mem_of_adj s q.penultimate hsSide hpenAvoid hadj
    exact hpenNotZ (by
      simpa only [zPart, mem_componentCarrier] using hpenSide)
  let r : G.Walk q.penultimate w := q.dropLast.reverse
  have hr : r.IsPath := hq.dropLast.reverse
  have hrGood : ∀ v, v ∈ r.support →
      v ∉ M.zPart ∧ v ≠ M.xSep.left ∧ v ≠ u.1 := by
    intro v hv
    have hvDrop : v ∈ q.dropLast.support := by
      simpa only [r, Walk.support_reverse, List.mem_reverse] using hv
    have hvQ : v ∈ q.support := by
      rw [q.support_dropLast hqNotNil] at hvDrop
      exact List.mem_of_mem_dropLast hvDrop
    have hvP := hqSub v hvQ
    refine ⟨?_, hpAvoid v hvP⟩
    intro hvZ
    have hvs : v = s := hqFirst v hvQ hvZ
    exact hsNotDrop (hvs ▸ hvDrop)
  rcases hpenBoundary with hpen | hpen
  · refine ⟨M.zSep.left, Or.inl rfl, r.copy hpen rfl, ?_, ?_⟩
    · exact (Walk.isPath_copy r hpen rfl).2 hr
    · intro v hv
      exact hrGood v (by simpa only [Walk.support_copy] using hv)
  · refine ⟨M.zSep.right, Or.inr rfl, r.copy hpen rfl, ?_, ?_⟩
    · exact (Walk.isPath_copy r hpen rfl).2 hr
    · intro v hv
      exact hrGood v (by simpa only [Walk.support_copy] using hv)

/-- A path in `G-(Z∪{xA})` from one `z` boundary to one of `xB,yB`
which avoids `u` contradicts the singleton-separator hypothesis. -/
theorem false_of_conditionV_good_path
    (hzA : M.zSep.left ≠ M.xSep.left)
    (u : {w : V // w ∉ M.zPart ∧ w ≠ M.xSep.left})
    (hsep : Erdos599.Countable.Separates M.conditionVGraph
      ({M.conditionVZA hzA, M.conditionVZB} : Set
        {w : V // w ∉ M.zPart ∧ w ≠ M.xSep.left})
      ({M.conditionVXB, M.conditionVYB} : Set
        {w : V // w ∉ M.zPart ∧ w ≠ M.xSep.left})
      ({u} : Set {w : V // w ∉ M.zPart ∧ w ≠ M.xSep.left}))
    {s t : V} (hs : s = M.zSep.left ∨ s = M.zSep.right)
    (ht : t = M.xSep.right ∨ t = M.ySep.right)
    (q : G.Walk s t) (hq : q.IsPath)
    (hgood : ∀ v, v ∈ q.support →
      v ∉ M.zPart ∧ v ≠ M.xSep.left ∧ v ≠ u.1) : False := by
  classical
  let sI : {w : V // w ∉ M.zPart ∧ w ≠ M.xSep.left} :=
    ⟨s, (hgood s q.start_mem_support).1,
      (hgood s q.start_mem_support).2.1⟩
  let tI : {w : V // w ∉ M.zPart ∧ w ≠ M.xSep.left} :=
    ⟨t, (hgood t q.end_mem_support).1,
      (hgood t q.end_mem_support).2.1⟩
  let q₀ := q.induce
    {w : V | w ∉ M.zPart ∧ w ≠ M.xSep.left}
    (fun v hv ↦ ⟨(hgood v hv).1, (hgood v hv).2.1⟩)
  let qI : M.conditionVGraph.Walk sI tI :=
    q₀.copy (Subtype.ext rfl) (Subtype.ext rfl)
  let inc : M.conditionVGraph →g G :=
    (SimpleGraph.Embedding.induce (G := G)
      (s := {w : V | w ∉ M.zPart ∧ w ≠ M.xSep.left})).toHom
  have hmap : qI.map inc = q := by
    simp only [qI, q₀, inc, Walk.map_copy]
    exact Walk.map_induce
      (s := {w : V | w ∉ M.zPart ∧ w ≠ M.xSep.left})
      q (fun v hv ↦ ⟨(hgood v hv).1, (hgood v hv).2.1⟩)
  have hqI : qI.IsPath := by
    apply Walk.IsPath.of_map (f := inc)
    rw [hmap]
    exact hq
  have hsI : sI ∈
      ({M.conditionVZA hzA, M.conditionVZB} : Set
        {w : V // w ∉ M.zPart ∧ w ≠ M.xSep.left}) := by
    rcases hs with rfl | rfl
    · left
      apply Subtype.ext
      rfl
    · right
      apply Subtype.ext
      rfl
  have htI : tI ∈
      ({M.conditionVXB, M.conditionVYB} : Set
        {w : V // w ∉ M.zPart ∧ w ≠ M.xSep.left}) := by
    rcases ht with rfl | rfl
    · left
      apply Subtype.ext
      rfl
    · right
      apply Subtype.ext
      rfl
  obtain ⟨v, hvq, hvu⟩ := hsep sI hsI tI htI qI hqI
  have hvEq : v = u := by simpa only [Set.mem_singleton_iff] using hvu
  have hvAmbient : v.1 ∈ q.support := by
    have hvMap : v.1 ∈ (qI.map inc).support := by
      rw [Walk.support_map]
      exact List.mem_map.mpr ⟨v, hvq, rfl⟩
    rwa [hmap] at hvMap
  exact (hgood v.1 hvAmbient).2.2 (congrArg Subtype.val hvEq)

/-- AHT p.14, the missing rim-exclusion step in the condition-(v)
exchange.  A new component meeting the `x`- or `y`-route yields a clean
path from `zA` or `zB` to the corresponding B-boundary, contradicting the
singleton separator.  If that target is itself `u = branchB`, the new and
old routed separators have the same deleted pair, so component equality
contradicts the old separator directly. -/
theorem conditionV_replacement_rim_free
    (hxyA : M.xSep.left = M.ySep.left)
    (hzA : M.zSep.left ≠ M.xSep.left)
    (u : {w : V // w ∉ M.zPart ∧ w ≠ M.xSep.left})
    (huStem : u.1 ∈ M.zBStem.support)
    (hsep : Erdos599.Countable.Separates M.conditionVGraph
      ({M.conditionVZA hzA, M.conditionVZB} : Set
        {w : V // w ∉ M.zPart ∧ w ≠ M.xSep.left})
      ({M.conditionVXB, M.conditionVYB} : Set
        {w : V // w ∉ M.zPart ∧ w ≠ M.xSep.left})
      ({u} : Set {w : V // w ∉ M.zPart ∧ w ≠ M.xSep.left}))
    (hzLeft : z ≠ M.xSep.left) (hzRight : z ≠ u.1)
    {w : V} (hwRim : w ∈ T.zRim.support)
    (hwLeft : w ≠ M.xSep.left) (hwRight : w ≠ u.1) :
    w ∉ (G.componentComplMk (K :=
      ((({M.xSep.left, u.1} : Finset V) : Set V))) (by
        simp only [Finset.mem_coe, Finset.mem_insert,
          Finset.mem_singleton, not_or]
        exact ⟨hzLeft, hzRight⟩) : Set V) := by
  classical
  intro hwD
  have hbranchA : M.xSep.left = T.branchA :=
    M.xA_eq_yA_imp_branchA hxyA
  have hwZ : w ∉ M.zPart := M.not_mem_zPart_of_mem_zRim hwRim
  obtain ⟨s, hs, q, hq, hqGood⟩ :=
    M.exists_conditionV_boundary_tail u hzLeft hzRight hwZ hwD
  have huZRoute : u.1 ∈ T.zRoute.support := M.zBStem_subset_route huStem
  have hu_ne_branchA : u.1 ≠ T.branchA := by
    intro h
    exact u.2.2 (h.trans hbranchA.symm)
  have make_contradiction {t : V} (ht : t = M.xSep.right ∨
      t = M.ySep.right) (r : G.Walk w t) (hr : r.IsPath)
      (hrGood : ∀ v, v ∈ r.support →
        v ∉ M.zPart ∧ v ≠ M.xSep.left ∧ v ≠ u.1) : False := by
    let raw : G.Walk s t := q.append r
    let p : G.Walk s t := raw.toPath
    have hp : p.IsPath := raw.toPath.prop
    have hpGood : ∀ v, v ∈ p.support →
        v ∉ M.zPart ∧ v ≠ M.xSep.left ∧ v ≠ u.1 := by
      intro v hv
      have hvRaw : v ∈ raw.support := raw.support_toPath_subset_support hv
      have hvCases : v ∈ q.support ∨ v ∈ r.support := by
        simpa only [raw, Walk.mem_support_append_iff] using hvRaw
      exact hvCases.elim (hqGood v) (hrGood v)
    exact M.false_of_conditionV_good_path hzA u hsep hs ht p hp hpGood
  have hwCases : w ∈ T.xRoute.support ∨ w ∈ T.yRoute.support := by
    simpa only [WatkinsMesnerK32Source.zRim,
      Walk.mem_support_append_iff, Walk.support_reverse,
      List.mem_reverse] using hwRim
  rcases hwCases with hwX | hwY
  · have hxBRoute : M.xSep.right ∈ T.xRoute.support :=
      M.xBStem_subset_route M.xBStem.end_mem_support
    have hw_ne_branchA : w ≠ T.branchA :=
      fun h ↦ hwLeft (h.trans hbranchA.symm)
    have hxB_ne_branchA : M.xSep.right ≠ T.branchA := by
      intro h
      exact M.xSep.left_ne_right (hbranchA.trans h.symm)
    by_cases huB : u.1 = T.branchB
    · by_cases hxBu : M.xSep.right = u.1
      · have hrightB : M.xSep.right = T.branchB := hxBu.trans huB
        have hwXSide : w ∈ (M.xSep.side : Set V) :=
          M.xSep.mem_side_of_route_of_eq_branches T.x_mem
            T.xRoute_isPath hbranchA hrightB hwX hwLeft
            (fun h ↦ hwRight (h.trans hxBu))
        let K : Set V :=
          ((({M.xSep.left, u.1} : Finset V) : Set V))
        have hzAvoid : z ∉ K := by
          simp only [K, Finset.mem_coe, Finset.mem_insert,
            Finset.mem_singleton, not_or]
          exact ⟨hzLeft, hzRight⟩
        let D : G.ComponentCompl K := G.componentComplMk hzAvoid
        have hzD : z ∈ (D : Set V) := ⟨hzAvoid, rfl⟩
        have hwD' : w ∈ (D : Set V) := by
          simpa only [D, K] using hwD
        have hpair :
            ((({M.xSep.left, M.xSep.right} : Finset V) : Set V)) = K := by
          ext v
          simp only [K, Finset.mem_coe, Finset.mem_insert,
            Finset.mem_singleton]
          rw [hxBu]
        let X : G.ComponentCompl K :=
          ComponentCompl.transport hpair M.xSep.side
        have hwX' : w ∈ (X : Set V) := by
          simpa only [X, ComponentCompl.mem_transport] using hwXSide
        have hzX' : z ∈ (X : Set V) :=
          ⟨hzAvoid, hzD.2.trans (hwD'.2.symm.trans hwX'.2)⟩
        have hzXSide : z ∈ (M.xSep.side : Set V) := by
          simpa only [X, ComponentCompl.mem_transport] using hzX'
        exact M.z_not_mem_xPart (by
          simpa only [xPart, mem_componentCarrier] using hzXSide)
      · have hw_ne_branchB : w ≠ T.branchB :=
          fun h ↦ hwRight (h.trans huB.symm)
        have hxB_ne_branchB : M.xSep.right ≠ T.branchB :=
          fun h ↦ hxBu (h.trans huB.symm)
        obtain ⟨r, hr, hrSub, hrEnds⟩ :=
          T.xRoute_isPath.exists_internal_interval hwX hxBRoute
            hw_ne_branchA hw_ne_branchB hxB_ne_branchA hxB_ne_branchB
        apply make_contradiction (Or.inl rfl) r hr
        intro v hv
        have hvRoute := hrSub v hv
        have hvRim : v ∈ T.zRim.support := by
          simp only [WatkinsMesnerK32Source.zRim,
            Walk.mem_support_append_iff]
          exact Or.inl hvRoute
        exact ⟨M.not_mem_zPart_of_mem_zRim hvRim,
          fun h ↦ (hrEnds v hv).1 (h.trans hbranchA),
          fun h ↦ (hrEnds v hv).2 (h.trans huB)⟩
    · have huNotX : u.1 ∉ T.xRoute.support := by
        intro huX
        rcases T.xRoute_inter_zRoute u.1 huX huZRoute with hA | hB
        · exact hu_ne_branchA hA
        · exact huB hB
      obtain ⟨r, hr, hrSub, hrA⟩ :=
        Walk.IsPath.exists_subpath_avoiding_start T.xRoute
          T.xRoute_isPath hwX hxBRoute hw_ne_branchA hxB_ne_branchA
      apply make_contradiction (Or.inl rfl) r hr
      intro v hv
      have hvRoute := hrSub v hv
      have hvRim : v ∈ T.zRim.support := by
        simp only [WatkinsMesnerK32Source.zRim,
          Walk.mem_support_append_iff]
        exact Or.inl hvRoute
      exact ⟨M.not_mem_zPart_of_mem_zRim hvRim,
        fun h ↦ hrA v hv (h.trans hbranchA),
        fun h ↦ huNotX (h ▸ hvRoute)⟩
  · have hyBRoute : M.ySep.right ∈ T.yRoute.support :=
      M.yBStem_subset_route M.yBStem.end_mem_support
    have hyLeftA : M.ySep.left = T.branchA := hxyA.symm.trans hbranchA
    have hw_ne_branchA : w ≠ T.branchA :=
      fun h ↦ hwLeft (h.trans hbranchA.symm)
    have hyB_ne_branchA : M.ySep.right ≠ T.branchA := by
      intro h
      exact M.ySep.left_ne_right (hyLeftA.trans h.symm)
    by_cases huB : u.1 = T.branchB
    · by_cases hyBu : M.ySep.right = u.1
      · have hrightB : M.ySep.right = T.branchB := hyBu.trans huB
        have hwYSide : w ∈ (M.ySep.side : Set V) :=
          M.ySep.mem_side_of_route_of_eq_branches T.y_mem
            T.yRoute_isPath hyLeftA hrightB hwY
            (fun h ↦ hwLeft (h.trans hxyA.symm))
            (fun h ↦ hwRight (h.trans hyBu))
        let K : Set V :=
          ((({M.xSep.left, u.1} : Finset V) : Set V))
        have hzAvoid : z ∉ K := by
          simp only [K, Finset.mem_coe, Finset.mem_insert,
            Finset.mem_singleton, not_or]
          exact ⟨hzLeft, hzRight⟩
        let D : G.ComponentCompl K := G.componentComplMk hzAvoid
        have hzD : z ∈ (D : Set V) := ⟨hzAvoid, rfl⟩
        have hwD' : w ∈ (D : Set V) := by
          simpa only [D, K] using hwD
        have hpair :
            ((({M.ySep.left, M.ySep.right} : Finset V) : Set V)) = K := by
          ext v
          simp only [K, Finset.mem_coe, Finset.mem_insert,
            Finset.mem_singleton]
          rw [← hxyA, hyBu]
        let Y : G.ComponentCompl K :=
          ComponentCompl.transport hpair M.ySep.side
        have hwY' : w ∈ (Y : Set V) := by
          simpa only [Y, ComponentCompl.mem_transport] using hwYSide
        have hzY' : z ∈ (Y : Set V) :=
          ⟨hzAvoid, hzD.2.trans (hwD'.2.symm.trans hwY'.2)⟩
        have hzYSide : z ∈ (M.ySep.side : Set V) := by
          simpa only [Y, ComponentCompl.mem_transport] using hzY'
        exact M.z_not_mem_yPart (by
          simpa only [yPart, mem_componentCarrier] using hzYSide)
      · have hw_ne_branchB : w ≠ T.branchB :=
          fun h ↦ hwRight (h.trans huB.symm)
        have hyB_ne_branchB : M.ySep.right ≠ T.branchB :=
          fun h ↦ hyBu (h.trans huB.symm)
        obtain ⟨r, hr, hrSub, hrEnds⟩ :=
          T.yRoute_isPath.exists_internal_interval hwY hyBRoute
            hw_ne_branchA hw_ne_branchB hyB_ne_branchA hyB_ne_branchB
        apply make_contradiction (Or.inr rfl) r hr
        intro v hv
        have hvRoute := hrSub v hv
        have hvRim : v ∈ T.zRim.support := by
          simp only [WatkinsMesnerK32Source.zRim,
            Walk.mem_support_append_iff, Walk.support_reverse,
            List.mem_reverse]
          exact Or.inr hvRoute
        exact ⟨M.not_mem_zPart_of_mem_zRim hvRim,
          fun h ↦ (hrEnds v hv).1 (h.trans hbranchA),
          fun h ↦ (hrEnds v hv).2 (h.trans huB)⟩
    · have huNotY : u.1 ∉ T.yRoute.support := by
        intro huY
        rcases T.yRoute_inter_zRoute u.1 huY huZRoute with hA | hB
        · exact hu_ne_branchA hA
        · exact huB hB
      obtain ⟨r, hr, hrSub, hrA⟩ :=
        Walk.IsPath.exists_subpath_avoiding_start T.yRoute
          T.yRoute_isPath hwY hyBRoute hw_ne_branchA hyB_ne_branchA
      apply make_contradiction (Or.inr rfl) r hr
      intro v hv
      have hvRoute := hrSub v hv
      have hvRim : v ∈ T.zRim.support := by
        simp only [WatkinsMesnerK32Source.zRim,
          Walk.mem_support_append_iff, Walk.support_reverse,
          List.mem_reverse]
        exact Or.inr hvRoute
      exact ⟨M.not_mem_zPart_of_mem_zRim hvRim,
        fun h ↦ hrA v hv (h.trans hbranchA),
        fun h ↦ huNotY (h ▸ hvRoute)⟩

/-- Therefore the condition-(v) auxiliary graph has no one-vertex
separator between `{zA,zB}` and `{xB,yB}`. -/
theorem conditionV_no_singleton_separator
    (hdelete : ∀ d : V, (G.induce fun w : V ↦ w ≠ d).Connected)
    (hxyA : M.xSep.left = M.ySep.left)
    (hzA : M.zSep.left ≠ M.xSep.left) :
    ∀ u : {w : V // w ∉ M.zPart ∧ w ≠ M.xSep.left},
      ¬Erdos599.Countable.Separates M.conditionVGraph
        ({M.conditionVZA hzA, M.conditionVZB} : Set
          {w : V // w ∉ M.zPart ∧ w ≠ M.xSep.left})
        ({M.conditionVXB, M.conditionVYB} : Set
          {w : V // w ∉ M.zPart ∧ w ≠ M.xSep.left})
        ({u} : Set {w : V // w ∉ M.zPart ∧ w ≠ M.xSep.left}) := by
  intro u hsep
  have huStem := M.mem_zBStem_of_conditionV_singleton_separator hzA u hsep
  apply M.false_of_conditionV_replacement_rim_free
    hdelete hxyA hzA u huStem
  intro hzLeft hzRight
  dsimp only
  intro w hwRim hwLeft hwRight
  exact M.conditionV_replacement_rim_free hxyA hzA u huStem hsep
    hzLeft hzRight hwRim hwLeft hwRight

/-- Map a path in the condition-(v) auxiliary induced graph back to the
ambient graph. -/
noncomputable def conditionVPath
    {s t : {w : V // w ∉ M.zPart ∧ w ≠ M.xSep.left}}
    (p : M.conditionVGraph.Walk s t) : G.Walk s.1 t.1 :=
  p.map (SimpleGraph.Embedding.induce
    (G := G) (s := {w : V | w ∉ M.zPart ∧
      w ≠ M.xSep.left})).toHom

theorem conditionVPath_isPath
    {s t : {w : V // w ∉ M.zPart ∧ w ≠ M.xSep.left}}
    {p : M.conditionVGraph.Walk s t} (hp : p.IsPath) :
    (M.conditionVPath p).IsPath := by
  exact hp.map (SimpleGraph.Embedding.induce
    (G := G) (s := {w : V | w ∉ M.zPart ∧
      w ≠ M.xSep.left})).injective

theorem conditionVPath_support_good
    {s t : {w : V // w ∉ M.zPart ∧ w ≠ M.xSep.left}}
    {p : M.conditionVGraph.Walk s t} {w : V}
    (hw : w ∈ (M.conditionVPath p).support) :
    w ∉ M.zPart ∧ w ≠ M.xSep.left := by
  let inc := (SimpleGraph.Embedding.induce
    (G := G) (s := {w : V | w ∉ M.zPart ∧
      w ≠ M.xSep.left})).toHom
  have hsupp : (M.conditionVPath p).support = p.support.map inc := by
    convert (Walk.support_map (p := p) (f := inc)) using 1 <;>
      rfl
  rw [hsupp] at hw
  obtain ⟨u, -, rfl⟩ := List.mem_map.mp hw
  exact u.2

/-- Vertex-disjoint paths in the auxiliary induced graph remain
vertex-disjoint after they are mapped back to the ambient graph. -/
theorem conditionVPaths_disjoint
    {s₀ t₀ s₁ t₁ :
      {w : V // w ∉ M.zPart ∧ w ≠ M.xSep.left}}
    {p : M.conditionVGraph.Walk s₀ t₀}
    {q : M.conditionVGraph.Walk s₁ t₁}
    (hdis : Disjoint {u | u ∈ p.support} {u | u ∈ q.support}) :
    Disjoint {w | w ∈ (M.conditionVPath p).support}
      {w | w ∈ (M.conditionVPath q).support} := by
  let inc := (SimpleGraph.Embedding.induce
    (G := G) (s := {w : V | w ∉ M.zPart ∧
      w ≠ M.xSep.left})).toHom
  have hpSupp : (M.conditionVPath p).support = p.support.map inc := by
    convert (Walk.support_map (p := p) (f := inc)) using 1 <;>
      rfl
  have hqSupp : (M.conditionVPath q).support = q.support.map inc := by
    convert (Walk.support_map (p := q) (f := inc)) using 1 <;>
      rfl
  rw [Set.disjoint_left]
  intro w hwp hwq
  rw [hpSupp] at hwp
  rw [hqSupp] at hwq
  obtain ⟨u, hu, huw⟩ := List.mem_map.mp hwp
  obtain ⟨v, hv, hvw⟩ := List.mem_map.mp hwq
  have huv : u = v := Subtype.ext (huw.trans hvw.symm)
  exact Set.disjoint_left.mp hdis hu (huv ▸ hv)

/-- A lifted linkage path disjoint from a path ending at `xB` misses the
entire `x`-terminal bridge. -/
theorem conditionVPath_disjoint_xBridge_of_disjoint_xBPath
    {s t r : {w : V // w ∉ M.zPart ∧ w ≠ M.xSep.left}}
    (p : M.conditionVGraph.Walk s M.conditionVXB)
    (q : M.conditionVGraph.Walk r t)
    (hdis : Disjoint {w | w ∈ (M.conditionVPath p).support}
      {w | w ∈ (M.conditionVPath q).support})
    (hrX : r.1 ∉ M.xPart) :
    Disjoint {w | w ∈ M.xTerminalBridge.support}
      {w | w ∈ (M.conditionVPath q).support} := by
  have hxBp : M.xSep.right ∈ (M.conditionVPath p).support := by
    simpa only [conditionVXB] using (M.conditionVPath p).end_mem_support
  have hqAvoidPair : ∀ w, w ∈ (M.conditionVPath q).support →
      w ∉ ({M.xSep.left, M.xSep.right} : Finset V) := by
    intro w hw
    have hwGood := M.conditionVPath_support_good hw
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    refine ⟨hwGood.2, ?_⟩
    intro h
    subst w
    exact Set.disjoint_left.mp hdis hxBp hw
  have hqAvoidPart : ∀ w, w ∈ (M.conditionVPath q).support →
      w ∉ M.xPart := by
    exact IsComponentAfterDeleting.walk_avoids_component
      (isComponentAfterDeleting_componentCarrier
        (G := G) {M.xSep.left, M.xSep.right} M.xSep.side)
      (M.conditionVPath q) hrX hqAvoidPair
  rw [Set.disjoint_left]
  intro w hwBridge hwq
  rcases M.xTerminalBridge_support hwBridge with rfl | rfl | hwPart
  · exact (M.conditionVPath_support_good hwq).2 rfl
  · exact Set.disjoint_left.mp hdis hxBp hwq
  · exact hqAvoidPart w hwq hwPart

/-- The symmetric wrong-linkage-path exclusion for the `y` bridge in the
normalized case `xA = yA`. -/
theorem conditionVPath_disjoint_yBridge_of_disjoint_yBPath
    (hxyA : M.xSep.left = M.ySep.left)
    {s t r : {w : V // w ∉ M.zPart ∧ w ≠ M.xSep.left}}
    (p : M.conditionVGraph.Walk s M.conditionVYB)
    (q : M.conditionVGraph.Walk r t)
    (hdis : Disjoint {w | w ∈ (M.conditionVPath p).support}
      {w | w ∈ (M.conditionVPath q).support})
    (hrY : r.1 ∉ M.yPart) :
    Disjoint {w | w ∈ M.yTerminalBridge.support}
      {w | w ∈ (M.conditionVPath q).support} := by
  have hyBp : M.ySep.right ∈ (M.conditionVPath p).support := by
    simpa only [conditionVYB] using (M.conditionVPath p).end_mem_support
  have hqAvoidPair : ∀ w, w ∈ (M.conditionVPath q).support →
      w ∉ ({M.ySep.left, M.ySep.right} : Finset V) := by
    intro w hw
    have hwGood := M.conditionVPath_support_good hw
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    refine ⟨fun h ↦ hwGood.2 (h.trans hxyA.symm), ?_⟩
    intro h
    subst w
    exact Set.disjoint_left.mp hdis hyBp hw
  have hqAvoidPart : ∀ w, w ∈ (M.conditionVPath q).support →
      w ∉ M.yPart := by
    exact IsComponentAfterDeleting.walk_avoids_component
      (isComponentAfterDeleting_componentCarrier
        (G := G) {M.ySep.left, M.ySep.right} M.ySep.side)
      (M.conditionVPath q) hrY hqAvoidPair
  rw [Set.disjoint_left]
  intro w hwBridge hwq
  rcases M.yTerminalBridge_support hwBridge with rfl | rfl | hwPart
  · exact (M.conditionVPath_support_good hwq).2 hxyA.symm
  · exact Set.disjoint_left.mp hdis hyBp hwq
  · exact hqAvoidPart w hwq hwPart

/-- A lifted condition-(v) path ending at `xB` meets the canonical
`x`-terminal bridge only at `xB`, provided its other endpoint is outside
the `x`-component. -/
theorem conditionVPath_to_xB_meets_xBridge_only
    {s : {w : V // w ∉ M.zPart ∧ w ≠ M.xSep.left}}
    (p : M.conditionVGraph.Walk s M.conditionVXB)
    (hp : p.IsPath) (hsX : s.1 ∉ M.xPart) :
    ∀ w, w ∈ M.xTerminalBridge.support →
      w ∈ (M.conditionVPath p).support → w = M.xSep.right := by
  have hq : (M.conditionVPath p).IsPath := M.conditionVPath_isPath hp
  have hqA : M.xSep.left ∉ (M.conditionVPath p).support := by
    intro hw
    exact (M.conditionVPath_support_good hw).2 rfl
  have havoid : ∀ w, w ∈ (M.conditionVPath p).support → w ∉ M.xPart := by
    intro w hw
    exact IsComponentAfterDeleting.path_to_boundary_avoids_component
      (isComponentAfterDeleting_componentCarrier
        (G := G) {M.xSep.left, M.xSep.right} M.xSep.side)
      (M.conditionVPath p) hq hsX hqA w hw
  intro w hwBridge hwPath
  rcases M.xTerminalBridge_support hwBridge with rfl | rfl | hwX
  · exact ((M.conditionVPath_support_good hwPath).2 rfl).elim
  · rfl
  · exact (havoid w hwPath hwX).elim

/-- The symmetric bridge-intersection fact for a path ending at `yB` in
the normalized condition-(v) case `xA = yA`. -/
theorem conditionVPath_to_yB_meets_yBridge_only
    (hxyA : M.xSep.left = M.ySep.left)
    {s : {w : V // w ∉ M.zPart ∧ w ≠ M.xSep.left}}
    (p : M.conditionVGraph.Walk s M.conditionVYB)
    (hp : p.IsPath) (hsY : s.1 ∉ M.yPart) :
    ∀ w, w ∈ M.yTerminalBridge.support →
      w ∈ (M.conditionVPath p).support → w = M.ySep.right := by
  have hq : (M.conditionVPath p).IsPath := M.conditionVPath_isPath hp
  have hqA : M.ySep.left ∉ (M.conditionVPath p).support := by
    intro hw
    exact (M.conditionVPath_support_good hw).2 hxyA.symm
  have havoid : ∀ w, w ∈ (M.conditionVPath p).support → w ∉ M.yPart := by
    intro w hw
    exact IsComponentAfterDeleting.path_to_boundary_avoids_component
      (isComponentAfterDeleting_componentCarrier
        (G := G) {M.ySep.left, M.ySep.right} M.ySep.side)
      (M.conditionVPath p) hq hsY hqA w hw
  intro w hwBridge hwPath
  rcases M.yTerminalBridge_support hwBridge with rfl | rfl | hwY
  · exact ((M.conditionVPath_support_good hwPath).2 hxyA.symm).elim
  · rfl
  · exact (havoid w hwPath hwY).elim

/-- Menger's two paths for the normalized condition-(v) auxiliary graph,
with the only two possible endpoint matchings made explicit. -/
theorem exists_conditionV_disjoint_pair_paths
    (hdelete : ∀ d : V, (G.induce fun w : V ↦ w ≠ d).Connected)
    (hxyA : M.xSep.left = M.ySep.left)
    (hzA : M.zSep.left ≠ M.xSep.left) :
    (∃ (p : M.conditionVGraph.Walk (M.conditionVZA hzA) M.conditionVXB)
        (q : M.conditionVGraph.Walk M.conditionVZB M.conditionVYB),
      p.IsPath ∧ q.IsPath ∧
        Disjoint {u | u ∈ p.support} {u | u ∈ q.support}) ∨
    (∃ (p : M.conditionVGraph.Walk (M.conditionVZA hzA) M.conditionVYB)
        (q : M.conditionVGraph.Walk M.conditionVZB M.conditionVXB),
      p.IsPath ∧ q.IsPath ∧
        Disjoint {u | u ∈ p.support} {u | u ∈ q.support}) := by
  let p₀ := M.zBToXBStemPath.induce
    {w : V | w ∉ M.zPart ∧ w ≠ M.xSep.left}
    (fun w hw ↦ ⟨M.zBToXBStemPath_avoids_zPart hw,
      M.zBToXBStemPath_avoids_xA hw⟩)
  let p : M.conditionVGraph.Walk M.conditionVZB M.conditionVXB :=
    p₀.copy (Subtype.ext rfl) (Subtype.ext rfl)
  let inc : M.conditionVGraph →g G :=
    (SimpleGraph.Embedding.induce
      (G := G) (s := {w : V | w ∉ M.zPart ∧
        w ≠ M.xSep.left})).toHom
  have hmap : p.map inc = M.zBToXBStemPath := by
    simp only [p, p₀, inc, Walk.map_copy]
    exact Walk.map_induce
      (s := {w : V | w ∉ M.zPart ∧ w ≠ M.xSep.left})
      M.zBToXBStemPath
      (fun w hw ↦ ⟨M.zBToXBStemPath_avoids_zPart hw,
        M.zBToXBStemPath_avoids_xA hw⟩)
  have hp : p.IsPath := by
    apply Walk.IsPath.of_map (f := inc)
    rw [hmap]
    exact M.zBToXBStemPath_isPath
  have hlink := exists_disjoint_pair_paths_of_no_singleton_separator
    (a₀ := M.conditionVZB) (a₁ := M.conditionVZA hzA)
    (b₀ := M.conditionVXB) (b₁ := M.conditionVYB)
    M.conditionVGraph p hp
      (by
        simpa only [Set.pair_comm M.conditionVZB (M.conditionVZA hzA)] using
          M.conditionV_no_singleton_separator hdelete hxyA hzA)
  rcases hlink with hstraight | hcross
  · rcases hstraight with ⟨pXB, qAY, hpXB, hqAY, hdis⟩
    right
    exact ⟨qAY, pXB, hqAY, hpXB, hdis.symm⟩
  · rcases hcross with ⟨pYB, qAX, hpYB, hqAX, hdis⟩
    left
    exact ⟨qAX, pYB, hqAX, hpYB, hdis.symm⟩

/-- Of the two disjoint lifted linkage paths starting at `zA` and `zB`,
the first meets the `z`-terminal bridge only at `zA`. -/
theorem conditionVPath_from_zA_meets_zBridge_only
    (hzA : M.zSep.left ≠ M.xSep.left)
    {t u : {w : V // w ∉ M.zPart ∧ w ≠ M.xSep.left}}
    (p : M.conditionVGraph.Walk (M.conditionVZA hzA) t)
    (q : M.conditionVGraph.Walk M.conditionVZB u)
    (hdis : Disjoint {w | w ∈ (M.conditionVPath p).support}
      {w | w ∈ (M.conditionVPath q).support}) :
    ∀ w, w ∈ (M.conditionVPath p).support →
      w ∈ M.zTerminalBridge.support → w = M.zSep.left := by
  intro w hwp hwZ
  rcases M.zTerminalBridge_support hwZ with rfl | rfl | hwPart
  · rfl
  · have hzBq : M.zSep.right ∈ (M.conditionVPath q).support := by
      simpa only [conditionVZB] using (M.conditionVPath q).start_mem_support
    exact (Set.disjoint_left.mp hdis hwp hzBq).elim
  · exact ((M.conditionVPath_support_good hwp).1 hwPart).elim

/-- The symmetric `zB` endpoint fact for the second lifted linkage path. -/
theorem conditionVPath_from_zB_meets_zBridge_only
    (hzA : M.zSep.left ≠ M.xSep.left)
    {t u : {w : V // w ∉ M.zPart ∧ w ≠ M.xSep.left}}
    (p : M.conditionVGraph.Walk (M.conditionVZA hzA) t)
    (q : M.conditionVGraph.Walk M.conditionVZB u)
    (hdis : Disjoint {w | w ∈ (M.conditionVPath p).support}
      {w | w ∈ (M.conditionVPath q).support}) :
    ∀ w, w ∈ (M.conditionVPath q).support →
      w ∈ M.zTerminalBridge.support → w = M.zSep.right := by
  intro w hwq hwZ
  rcases M.zTerminalBridge_support hwZ with rfl | rfl | hwPart
  · have hzAp : M.zSep.left ∈ (M.conditionVPath p).support := by
      simpa only [conditionVZA] using (M.conditionVPath p).start_mem_support
    exact (Set.disjoint_left.mp hdis hzAp hwq).elim
  · rfl
  · exact ((M.conditionVPath_support_good hwq).1 hwPart).elim

/-- In the normalized condition-(v) case the `x`- and `y`-terminal
bridges meet only at their common A-end. -/
theorem xBridge_meets_yBridge_only_xA
    (hxyA : M.xSep.left = M.ySep.left)
    (hxyB : M.xSep.right ≠ M.ySep.right) :
    ∀ w, w ∈ M.xTerminalBridge.support →
      w ∈ M.yTerminalBridge.support → w = M.xSep.left := by
  intro w hwX hwY
  rcases M.xTerminalBridge_support hwX with rfl | rfl | hwPartX
  · rfl
  · rcases M.yTerminalBridge_support hwY with hA | hB | hwPartY
    · exact (Finset.disjoint_left.mp M.aSet_disjoint_bSet
        M.yA_mem_aSet (hA ▸ M.xB_mem_bSet)).elim
    · exact (hxyB hB).elim
    · exact (Finset.disjoint_left.mp M.yPart_disjoint_bSet
        hwPartY M.xB_mem_bSet).elim
  · rcases M.yTerminalBridge_support hwY with hA | hB | hwPartY
    · exact (Finset.disjoint_left.mp M.xPart_disjoint_aSet hwPartX
        (by simpa only [hA] using M.yA_mem_aSet)).elim
    · exact (Finset.disjoint_left.mp M.xPart_disjoint_bSet hwPartX
        (by simpa only [hB] using M.yB_mem_bSet)).elim
    · exact (Finset.disjoint_left.mp M.xPart_disjoint_yPart
        hwPartX hwPartY).elim

/-- The `x`- and `z`-terminal bridges can meet only at the B-end of the
`z` bridge; this formulation also covers the case `xB = zB`. -/
theorem xBridge_meets_zBridge_only_zB
    (hzA : M.zSep.left ≠ M.xSep.left) :
    ∀ w, w ∈ M.xTerminalBridge.support →
      w ∈ M.zTerminalBridge.support → w = M.zSep.right := by
  intro w hwX hwZ
  rcases M.xTerminalBridge_support hwX with rfl | rfl | hwPartX
  · rcases M.zTerminalBridge_support hwZ with hA | hB | hwPartZ
    · exact (hzA hA.symm).elim
    · exact (Finset.disjoint_left.mp M.aSet_disjoint_bSet
        M.xA_mem_aSet (hB ▸ M.zB_mem_bSet)).elim
    · exact (Finset.disjoint_left.mp M.zPart_disjoint_aSet
        hwPartZ M.xA_mem_aSet).elim
  · rcases M.zTerminalBridge_support hwZ with hA | hB | hwPartZ
    · exact (Finset.disjoint_left.mp M.aSet_disjoint_bSet
        M.zA_mem_aSet (hA ▸ M.xB_mem_bSet)).elim
    · exact hB
    · exact (Finset.disjoint_left.mp M.zPart_disjoint_bSet
        hwPartZ M.xB_mem_bSet).elim
  · rcases M.zTerminalBridge_support hwZ with hA | hB | hwPartZ
    · exact (Finset.disjoint_left.mp M.xPart_disjoint_aSet hwPartX
        (by simpa only [hA] using M.zA_mem_aSet)).elim
    · exact (Finset.disjoint_left.mp M.xPart_disjoint_bSet hwPartX
        (by simpa only [hB] using M.zB_mem_bSet)).elim
    · exact (Finset.disjoint_left.mp M.xPart_disjoint_zPart
        hwPartX hwPartZ).elim

/-- The analogous `y`--`z` bridge intersection in the normalized case. -/
theorem yBridge_meets_zBridge_only_zB
    (hxyA : M.xSep.left = M.ySep.left)
    (hzA : M.zSep.left ≠ M.xSep.left) :
    ∀ w, w ∈ M.yTerminalBridge.support →
      w ∈ M.zTerminalBridge.support → w = M.zSep.right := by
  intro w hwY hwZ
  rcases M.yTerminalBridge_support hwY with rfl | rfl | hwPartY
  · rcases M.zTerminalBridge_support hwZ with hA | hB | hwPartZ
    · exact (hzA (hA.symm.trans hxyA.symm)).elim
    · exact (Finset.disjoint_left.mp M.aSet_disjoint_bSet
        M.yA_mem_aSet (hB ▸ M.zB_mem_bSet)).elim
    · exact (Finset.disjoint_left.mp M.zPart_disjoint_aSet
        hwPartZ M.yA_mem_aSet).elim
  · rcases M.zTerminalBridge_support hwZ with hA | hB | hwPartZ
    · exact (Finset.disjoint_left.mp M.aSet_disjoint_bSet
        M.zA_mem_aSet (hA ▸ M.yB_mem_bSet)).elim
    · exact hB
    · exact (Finset.disjoint_left.mp M.zPart_disjoint_bSet
        hwPartZ M.yB_mem_bSet).elim
  · rcases M.zTerminalBridge_support hwZ with hA | hB | hwPartZ
    · exact (Finset.disjoint_left.mp M.yPart_disjoint_aSet hwPartY
        (by simpa only [hA] using M.zA_mem_aSet)).elim
    · exact (Finset.disjoint_left.mp M.yPart_disjoint_bSet hwPartY
        (by simpa only [hB] using M.zB_mem_bSet)).elim
    · exact (Finset.disjoint_left.mp M.yPart_disjoint_zPart
        hwPartY hwPartZ).elim

theorem xBridge_disjoint_zBridge
    (hzA : M.zSep.left ≠ M.xSep.left)
    (hxzB : M.xSep.right ≠ M.zSep.right) :
    Disjoint {w | w ∈ M.xTerminalBridge.support}
      {w | w ∈ M.zTerminalBridge.support} := by
  rw [Set.disjoint_left]
  intro w hwX hwZ
  have hw := M.xBridge_meets_zBridge_only_zB hzA w hwX hwZ
  subst w
  rcases M.xTerminalBridge_support hwX with hA | hB | hwPart
  · exact (Finset.disjoint_left.mp M.aSet_disjoint_bSet
      (by simpa only [hA] using M.xA_mem_aSet) M.zB_mem_bSet).elim
  · exact hxzB hB.symm
  · exact (Finset.disjoint_left.mp M.xPart_disjoint_bSet
      hwPart M.zB_mem_bSet).elim

theorem yBridge_disjoint_zBridge
    (hxyA : M.xSep.left = M.ySep.left)
    (hzA : M.zSep.left ≠ M.xSep.left)
    (hyzB : M.ySep.right ≠ M.zSep.right) :
    Disjoint {w | w ∈ M.yTerminalBridge.support}
      {w | w ∈ M.zTerminalBridge.support} := by
  rw [Set.disjoint_left]
  intro w hwY hwZ
  have hw := M.yBridge_meets_zBridge_only_zB hxyA hzA w hwY hwZ
  subst w
  rcases M.yTerminalBridge_support hwY with hA | hB | hwPart
  · exact (Finset.disjoint_left.mp M.aSet_disjoint_bSet
      (by simpa only [hA] using M.yA_mem_aSet) M.zB_mem_bSet).elim
  · exact hyzB hB.symm
  · exact (Finset.disjoint_left.mp M.yPart_disjoint_bSet
      hwPart M.zB_mem_bSet).elim

/-- The first condition-(v) Menger matching, `zA--xB` and `zB--yB`,
splices with the three terminal bridges to form the forbidden cycle. -/
theorem hasCycleThroughThree_of_conditionV_straight
    (hxyA : M.xSep.left = M.ySep.left)
    (hzA : M.zSep.left ≠ M.xSep.left)
    (hxyB : M.xSep.right ≠ M.ySep.right)
    (p : M.conditionVGraph.Walk (M.conditionVZA hzA) M.conditionVXB)
    (q : M.conditionVGraph.Walk M.conditionVZB M.conditionVYB)
    (hp : p.IsPath) (hq : q.IsPath)
    (hdis : Disjoint {u | u ∈ p.support} {u | u ∈ q.support}) :
    HasCycleThroughThree G x y z := by
  let X := M.xTerminalBridge
  let Y : G.Walk M.xSep.left M.ySep.right :=
    M.yTerminalBridge.copy hxyA.symm rfl
  let Z := M.zTerminalBridge
  let ZR : G.Walk (M.conditionVZB : V) M.zSep.left :=
    M.zTerminalBridge.reverse.copy rfl rfl
  let P := M.conditionVPath p
  let Q := M.conditionVPath q
  have hP : P.IsPath := M.conditionVPath_isPath hp
  have hQ : Q.IsPath := M.conditionVPath_isPath hq
  have hY : Y.IsPath :=
    (Walk.isPath_copy _ _ _).mpr M.yTerminalBridge_isPath
  have hPQ : Disjoint {w | w ∈ P.support} {w | w ∈ Q.support} :=
    M.conditionVPaths_disjoint hdis
  have hzAX : M.zSep.left ∉ M.xPart := fun h ↦
    Finset.disjoint_left.mp M.xPart_disjoint_aSet h M.zA_mem_aSet
  have hzBX : M.zSep.right ∉ M.xPart := fun h ↦
    Finset.disjoint_left.mp M.xPart_disjoint_bSet h M.zB_mem_bSet
  have hzAY : M.zSep.left ∉ M.yPart := fun h ↦
    Finset.disjoint_left.mp M.yPart_disjoint_aSet h M.zA_mem_aSet
  have hzBY : M.zSep.right ∉ M.yPart := fun h ↦
    Finset.disjoint_left.mp M.yPart_disjoint_bSet h M.zB_mem_bSet
  have hxzB : M.xSep.right ≠ M.zSep.right := by
    intro h
    have hxBp : M.xSep.right ∈ P.support := by
      simpa only [P, conditionVXB] using P.end_mem_support
    have hzBq : M.zSep.right ∈ Q.support := by
      simpa only [Q, conditionVZB] using Q.start_mem_support
    have hxBq : M.xSep.right ∈ Q.support :=
      (congrArg (fun v : V ↦ v ∈ Q.support) h.symm).mp hzBq
    exact Set.disjoint_left.mp hPQ hxBp hxBq
  have hXP : ∀ w, w ∈ X.support → w ∈ P.reverse.support →
      w = M.xSep.right := by
    intro w hwX hwP
    apply M.conditionVPath_to_xB_meets_xBridge_only p hp hzAX w hwX
    simpa only [P, Walk.support_reverse, List.mem_reverse] using hwP
  have hYQ : ∀ w, w ∈ Y.support → w ∈ Q.reverse.support →
      w = M.ySep.right := by
    intro w hwY hwQ
    apply M.conditionVPath_to_yB_meets_yBridge_only hxyA q hq hzBY w
    · simpa only [Y, Walk.support_copy] using hwY
    · simpa only [Q, Walk.support_reverse, List.mem_reverse] using hwQ
  have hXQ : Disjoint {w | w ∈ X.support} {w | w ∈ Q.support} := by
    simpa only [X, Q] using
      M.conditionVPath_disjoint_xBridge_of_disjoint_xBPath p q hPQ hzBX
  have hYP : Disjoint {w | w ∈ Y.support} {w | w ∈ P.support} := by
    simpa only [Y, P, Walk.support_copy] using
      M.conditionVPath_disjoint_yBridge_of_disjoint_yBPath
        hxyA q p hPQ.symm hzAY
  have hXZ : Disjoint {w | w ∈ X.support} {w | w ∈ Z.support} := by
    simpa only [X, Z] using M.xBridge_disjoint_zBridge hzA hxzB
  have hXY : ∀ w, w ∈ X.support → w ∈ Y.support →
      w = M.xSep.left := by
    intro w hwX hwY
    apply M.xBridge_meets_yBridge_only_xA hxyA hxyB w hwX
    simpa only [Y, Walk.support_copy] using hwY
  let L := X.append P.reverse
  have hL : L.IsPath := by
    exact M.xTerminalBridge_isPath.append_of_meet_only_endpoint_wm
      hP.reverse hXP
  let R₁ := Y.append Q.reverse
  have hR₁ : R₁.IsPath := hY.append_of_meet_only_endpoint_wm hQ.reverse hYQ
  have hZR : ZR.IsPath :=
    (Walk.isPath_copy _ _ _).mpr M.zTerminalBridge_isPath.reverse
  have hZRsupport : ZR.support = M.zTerminalBridge.reverse.support := by
    dsimp only [ZR]
    exact Walk.support_copy _ _ _
  have hRZ : ∀ w, w ∈ R₁.support → w ∈ ZR.support →
      w = M.zSep.right := by
    intro w hwR hwZ
    have hwZ' : w ∈ Z.support := by
      have hwZR := hwZ
      rw [hZRsupport, Walk.support_reverse, List.mem_reverse] at hwZR
      simpa only [Z] using hwZR
    have hwCases : w ∈ Y.support ∨ w ∈ Q.reverse.support := by
      change w ∈ (Y.append Q.reverse).support at hwR
      exact (Walk.mem_support_append_iff Y Q.reverse).mp hwR
    rcases hwCases with hwY | hwQ
    · apply M.yBridge_meets_zBridge_only_zB hxyA hzA w
      · simpa only [Y, Walk.support_copy] using hwY
      · exact hwZ'
    · apply M.conditionVPath_from_zB_meets_zBridge_only hzA p q hPQ w
      · simpa only [Q, Walk.support_reverse, List.mem_reverse] using hwQ
      · exact hwZ'
  let R := R₁.append ZR
  have hR : R.IsPath :=
    hR₁.append_of_meet_only_endpoint_wm hZR hRZ
  have hmeet : ∀ w, w ∈ L.support → w ∈ R.support →
      w = M.xSep.left ∨ w = M.zSep.left := by
    intro w hwL hwR
    have hwLCases : w ∈ X.support ∨ w ∈ P.reverse.support := by
      change w ∈ (X.append P.reverse).support at hwL
      exact (Walk.mem_support_append_iff X P.reverse).mp hwL
    have hwRCases : (w ∈ Y.support ∨ w ∈ Q.reverse.support) ∨
        w ∈ ZR.support := by
      change w ∈ ((Y.append Q.reverse).append ZR).support at hwR
      rcases (Walk.mem_support_append_iff (Y.append Q.reverse) ZR).mp hwR with
        hwR₁ | hwZ
      · exact Or.inl ((Walk.mem_support_append_iff Y Q.reverse).mp hwR₁)
      · exact Or.inr hwZ
    rcases hwLCases with hwX | hwP
    · rcases hwRCases with (hwY | hwQ) | hwZ
      · exact Or.inl (hXY w hwX hwY)
      · have hwQ' : w ∈ Q.support := by
          simpa only [Walk.support_reverse, List.mem_reverse] using hwQ
        exact (Set.disjoint_left.mp hXQ hwX hwQ').elim
      · have hwZ' : w ∈ Z.support := by
          have hwZR := hwZ
          rw [hZRsupport, Walk.support_reverse, List.mem_reverse] at hwZR
          simpa only [Z] using hwZR
        exact (Set.disjoint_left.mp hXZ hwX hwZ').elim
    · have hwP' : w ∈ P.support := by
        simpa only [Walk.support_reverse, List.mem_reverse] using hwP
      rcases hwRCases with (hwY | hwQ) | hwZ
      · exact (Set.disjoint_left.mp hYP hwY hwP').elim
      · have hwQ' : w ∈ Q.support := by
          simpa only [Walk.support_reverse, List.mem_reverse] using hwQ
        exact (Set.disjoint_left.mp hPQ hwP' hwQ').elim
      · right
        apply M.conditionVPath_from_zA_meets_zBridge_only hzA p q hPQ w hwP'
        have hwZR := hwZ
        rw [hZRsupport, Walk.support_reverse, List.mem_reverse] at hwZR
        simpa only [Z] using hwZR
  have hxL : x ∈ L.support := by
    change x ∈ (X.append P.reverse).support
    exact (Walk.mem_support_append_iff X P.reverse).mpr
      (Or.inl M.x_mem_xTerminalBridge)
  have hyR : y ∈ R.support := by
    change y ∈ ((Y.append Q.reverse).append ZR).support
    apply (Walk.mem_support_append_iff (Y.append Q.reverse) ZR).mpr
    apply Or.inl
    apply (Walk.mem_support_append_iff Y Q.reverse).mpr
    exact Or.inl (by
      simpa only [Y, Walk.support_copy] using M.y_mem_yTerminalBridge)
  have hzR : z ∈ R.support := by
    change z ∈ ((Y.append Q.reverse).append ZR).support
    apply (Walk.mem_support_append_iff (Y.append Q.reverse) ZR).mpr
    apply Or.inr
    rw [hZRsupport, Walk.support_reverse, List.mem_reverse]
    exact M.z_mem_zTerminalBridge
  have hxzA : x ≠ M.zSep.left := by
    intro h
    have hzAX : M.zSep.left ∈ M.xPart :=
      (congrArg (fun v : V ↦ v ∈ M.xPart) h).mp M.x_mem_xPart
    exact Finset.disjoint_left.mp M.xPart_disjoint_aSet hzAX M.zA_mem_aSet
  exact hasCycleThroughThree_of_two_clean_arcs L R hL hR hxL
    M.xSep.x_ne_left hxzA hmeet
    (Or.inl hxL) (Or.inr hyR) (Or.inr hzR)

/-- The crossed condition-(v) matching, `zA--yB` and `zB--xB`, gives
the complementary literal cycle splice. -/
theorem hasCycleThroughThree_of_conditionV_crossed
    (hxyA : M.xSep.left = M.ySep.left)
    (hzA : M.zSep.left ≠ M.xSep.left)
    (hxyB : M.xSep.right ≠ M.ySep.right)
    (p : M.conditionVGraph.Walk (M.conditionVZA hzA) M.conditionVYB)
    (q : M.conditionVGraph.Walk M.conditionVZB M.conditionVXB)
    (hp : p.IsPath) (hq : q.IsPath)
    (hdis : Disjoint {u | u ∈ p.support} {u | u ∈ q.support}) :
    HasCycleThroughThree G x y z := by
  let X := M.xTerminalBridge
  let Y : G.Walk M.xSep.left M.ySep.right :=
    M.yTerminalBridge.copy hxyA.symm rfl
  let Z := M.zTerminalBridge
  let ZR : G.Walk (M.conditionVZB : V) M.zSep.left :=
    M.zTerminalBridge.reverse.copy rfl rfl
  let P := M.conditionVPath p
  let Q := M.conditionVPath q
  have hP : P.IsPath := M.conditionVPath_isPath hp
  have hQ : Q.IsPath := M.conditionVPath_isPath hq
  have hY : Y.IsPath :=
    (Walk.isPath_copy _ _ _).mpr M.yTerminalBridge_isPath
  have hPQ : Disjoint {w | w ∈ P.support} {w | w ∈ Q.support} :=
    M.conditionVPaths_disjoint hdis
  have hzAX : M.zSep.left ∉ M.xPart := fun h ↦
    Finset.disjoint_left.mp M.xPart_disjoint_aSet h M.zA_mem_aSet
  have hzBX : M.zSep.right ∉ M.xPart := fun h ↦
    Finset.disjoint_left.mp M.xPart_disjoint_bSet h M.zB_mem_bSet
  have hzAY : M.zSep.left ∉ M.yPart := fun h ↦
    Finset.disjoint_left.mp M.yPart_disjoint_aSet h M.zA_mem_aSet
  have hzBY : M.zSep.right ∉ M.yPart := fun h ↦
    Finset.disjoint_left.mp M.yPart_disjoint_bSet h M.zB_mem_bSet
  have hyzB : M.ySep.right ≠ M.zSep.right := by
    intro h
    have hyBp : M.ySep.right ∈ P.support := by
      simpa only [P, conditionVYB] using P.end_mem_support
    have hzBq : M.zSep.right ∈ Q.support := by
      simpa only [Q, conditionVZB] using Q.start_mem_support
    have hyBq : M.ySep.right ∈ Q.support :=
      (congrArg (fun v : V ↦ v ∈ Q.support) h.symm).mp hzBq
    exact Set.disjoint_left.mp hPQ hyBp hyBq
  have hXQ : ∀ w, w ∈ X.support → w ∈ Q.reverse.support →
      w = M.xSep.right := by
    intro w hwX hwQ
    apply M.conditionVPath_to_xB_meets_xBridge_only q hq hzBX w hwX
    simpa only [Q, Walk.support_reverse, List.mem_reverse] using hwQ
  have hYP : ∀ w, w ∈ Y.support → w ∈ P.reverse.support →
      w = M.ySep.right := by
    intro w hwY hwP
    apply M.conditionVPath_to_yB_meets_yBridge_only hxyA p hp hzAY w
    · simpa only [Y, Walk.support_copy] using hwY
    · simpa only [P, Walk.support_reverse, List.mem_reverse] using hwP
  have hXP : Disjoint {w | w ∈ X.support} {w | w ∈ P.support} := by
    simpa only [X, P] using
      M.conditionVPath_disjoint_xBridge_of_disjoint_xBPath
        q p hPQ.symm hzAX
  have hYQ : Disjoint {w | w ∈ Y.support} {w | w ∈ Q.support} := by
    simpa only [Y, Q, Walk.support_copy] using
      M.conditionVPath_disjoint_yBridge_of_disjoint_yBPath
        hxyA p q hPQ hzBY
  have hYZ : Disjoint {w | w ∈ Y.support} {w | w ∈ Z.support} := by
    simpa only [Y, Z, Walk.support_copy] using
      M.yBridge_disjoint_zBridge hxyA hzA hyzB
  have hXY : ∀ w, w ∈ X.support → w ∈ Y.support →
      w = M.xSep.left := by
    intro w hwX hwY
    apply M.xBridge_meets_yBridge_only_xA hxyA hxyB w hwX
    simpa only [Y, Walk.support_copy] using hwY
  let L₁ := X.append Q.reverse
  have hL₁ : L₁.IsPath :=
    M.xTerminalBridge_isPath.append_of_meet_only_endpoint_wm hQ.reverse hXQ
  have hZR : ZR.IsPath :=
    (Walk.isPath_copy _ _ _).mpr M.zTerminalBridge_isPath.reverse
  have hZRsupport : ZR.support = M.zTerminalBridge.reverse.support := by
    dsimp only [ZR]
    exact Walk.support_copy _ _ _
  have hLZ : ∀ w, w ∈ L₁.support → w ∈ ZR.support →
      w = M.zSep.right := by
    intro w hwL hwZ
    have hwZ' : w ∈ Z.support := by
      have hwZR := hwZ
      rw [hZRsupport, Walk.support_reverse, List.mem_reverse] at hwZR
      simpa only [Z] using hwZR
    have hwCases : w ∈ X.support ∨ w ∈ Q.reverse.support := by
      change w ∈ (X.append Q.reverse).support at hwL
      exact (Walk.mem_support_append_iff X Q.reverse).mp hwL
    rcases hwCases with hwX | hwQ
    · apply M.xBridge_meets_zBridge_only_zB hzA w hwX hwZ'
    · apply M.conditionVPath_from_zB_meets_zBridge_only hzA p q hPQ w
      · simpa only [Q, Walk.support_reverse, List.mem_reverse] using hwQ
      · exact hwZ'
  let L := L₁.append ZR
  have hL : L.IsPath :=
    hL₁.append_of_meet_only_endpoint_wm hZR hLZ
  let R := Y.append P.reverse
  have hR : R.IsPath := hY.append_of_meet_only_endpoint_wm hP.reverse hYP
  have hmeet : ∀ w, w ∈ L.support → w ∈ R.support →
      w = M.xSep.left ∨ w = M.zSep.left := by
    intro w hwL hwR
    have hwLCases : (w ∈ X.support ∨ w ∈ Q.reverse.support) ∨
        w ∈ ZR.support := by
      change w ∈ ((X.append Q.reverse).append ZR).support at hwL
      rcases (Walk.mem_support_append_iff (X.append Q.reverse) ZR).mp hwL with
        hwL₁ | hwZ
      · exact Or.inl ((Walk.mem_support_append_iff X Q.reverse).mp hwL₁)
      · exact Or.inr hwZ
    have hwRCases : w ∈ Y.support ∨ w ∈ P.reverse.support := by
      change w ∈ (Y.append P.reverse).support at hwR
      exact (Walk.mem_support_append_iff Y P.reverse).mp hwR
    rcases hwLCases with (hwX | hwQ) | hwZ
    · rcases hwRCases with hwY | hwP
      · exact Or.inl (hXY w hwX hwY)
      · have hwP' : w ∈ P.support := by
          simpa only [Walk.support_reverse, List.mem_reverse] using hwP
        exact (Set.disjoint_left.mp hXP hwX hwP').elim
    · have hwQ' : w ∈ Q.support := by
        simpa only [Walk.support_reverse, List.mem_reverse] using hwQ
      rcases hwRCases with hwY | hwP
      · exact (Set.disjoint_left.mp hYQ hwY hwQ').elim
      · have hwP' : w ∈ P.support := by
          simpa only [Walk.support_reverse, List.mem_reverse] using hwP
        exact (Set.disjoint_left.mp hPQ hwP' hwQ').elim
    · have hwZ' : w ∈ Z.support := by
        have hwZR := hwZ
        rw [hZRsupport, Walk.support_reverse, List.mem_reverse] at hwZR
        simpa only [Z] using hwZR
      rcases hwRCases with hwY | hwP
      · exact (Set.disjoint_left.mp hYZ hwY hwZ').elim
      · right
        have hwP' : w ∈ P.support := by
          simpa only [Walk.support_reverse, List.mem_reverse] using hwP
        exact M.conditionVPath_from_zA_meets_zBridge_only
          hzA p q hPQ w hwP' hwZ'
  have hxL : x ∈ L.support := by
    change x ∈ ((X.append Q.reverse).append ZR).support
    apply (Walk.mem_support_append_iff (X.append Q.reverse) ZR).mpr
    exact Or.inl ((Walk.mem_support_append_iff X Q.reverse).mpr
      (Or.inl M.x_mem_xTerminalBridge))
  have hzL : z ∈ L.support := by
    change z ∈ ((X.append Q.reverse).append ZR).support
    apply (Walk.mem_support_append_iff (X.append Q.reverse) ZR).mpr
    apply Or.inr
    rw [hZRsupport, Walk.support_reverse, List.mem_reverse]
    exact M.z_mem_zTerminalBridge
  have hyR : y ∈ R.support := by
    change y ∈ (Y.append P.reverse).support
    apply (Walk.mem_support_append_iff Y P.reverse).mpr
    exact Or.inl (by
      simpa only [Y, Walk.support_copy] using M.y_mem_yTerminalBridge)
  have hxzA : x ≠ M.zSep.left := by
    intro h
    have hzAX : M.zSep.left ∈ M.xPart :=
      (congrArg (fun v : V ↦ v ∈ M.xPart) h).mp M.x_mem_xPart
    exact Finset.disjoint_left.mp M.xPart_disjoint_aSet hzAX M.zA_mem_aSet
  exact hasCycleThroughThree_of_two_clean_arcs L R hL hR hxL
    M.xSep.x_ne_left hxzA hmeet
    (Or.inl hxL) (Or.inr hyR) (Or.inl hzL)

/-- AHT condition (v), normalized so the repeated A-boundary is
`xA = yA`: the maximality exchange and Menger splices force a common
cycle through `x,y,z`. -/
theorem hasCycleThroughThree_of_xA_eq_yA
    (hdelete : ∀ d : V, (G.induce fun w : V ↦ w ≠ d).Connected)
    (hxyA : M.xSep.left = M.ySep.left)
    (hzA : M.zSep.left ≠ M.xSep.left) :
    HasCycleThroughThree G x y z := by
  have hxyB := M.xB_ne_yB_of_xA_eq_yA hdelete hxyA hzA
  rcases M.exists_conditionV_disjoint_pair_paths hdelete hxyA hzA with
      ⟨p, q, hp, hq, hdis⟩ | ⟨p, q, hp, hq, hdis⟩
  · exact M.hasCycleThroughThree_of_conditionV_straight
      hxyA hzA hxyB p q hp hq hdis
  · exact M.hasCycleThroughThree_of_conditionV_crossed
      hxyA hzA hxyB p q hp hq hdis

/-- Relabel the source routes by the transposition `y ↔ z`. -/
def swapYZSource (T : WatkinsMesnerK32Source G x y z) :
    WatkinsMesnerK32Source G x z y where
  branchA := T.branchA
  branchB := T.branchB
  branch_ne := T.branch_ne
  xRoute := T.xRoute
  yRoute := T.zRoute
  zRoute := T.yRoute
  xRoute_isPath := T.xRoute_isPath
  yRoute_isPath := T.zRoute_isPath
  zRoute_isPath := T.yRoute_isPath
  x_mem := T.x_mem
  y_mem := T.z_mem
  z_mem := T.y_mem
  x_internal := T.x_internal
  y_internal := T.z_internal
  z_internal := T.y_internal
  xRoute_inter_yRoute := T.xRoute_inter_zRoute
  xRoute_inter_zRoute := T.xRoute_inter_yRoute
  yRoute_inter_zRoute := fun w hwZ hwY ↦
    T.yRoute_inter_zRoute w hwY hwZ

/-- Cyclically relabel the source routes `(x,y,z) ↦ (y,z,x)`. -/
def rotateYZXSource (T : WatkinsMesnerK32Source G x y z) :
    WatkinsMesnerK32Source G y z x where
  branchA := T.branchA
  branchB := T.branchB
  branch_ne := T.branch_ne
  xRoute := T.yRoute
  yRoute := T.zRoute
  zRoute := T.xRoute
  xRoute_isPath := T.yRoute_isPath
  yRoute_isPath := T.zRoute_isPath
  zRoute_isPath := T.xRoute_isPath
  x_mem := T.y_mem
  y_mem := T.z_mem
  z_mem := T.x_mem
  x_internal := T.y_internal
  y_internal := T.z_internal
  z_internal := T.x_internal
  xRoute_inter_yRoute := T.yRoute_inter_zRoute
  xRoute_inter_zRoute := fun w hwY hwX ↦
    T.xRoute_inter_yRoute w hwX hwY
  yRoute_inter_zRoute := fun w hwZ hwX ↦
    T.xRoute_inter_zRoute w hwX hwZ

/-- Reverse the A/B orientation of all three source routes.  Writing each
reversed route as the two old terminal arms in reverse order makes the
new arms definitionally recover the old opposite arms. -/
def reverseABSource (T : WatkinsMesnerK32Source G x y z) :
    WatkinsMesnerK32Source G x y z where
  branchA := T.branchB
  branchB := T.branchA
  branch_ne := T.branch_ne.symm
  xRoute := T.xRoute.reverseSplit T.x_mem
  yRoute := T.yRoute.reverseSplit T.y_mem
  zRoute := T.zRoute.reverseSplit T.z_mem
  xRoute_isPath := Walk.IsPath.reverseSplit T.xRoute T.xRoute_isPath T.x_mem
  yRoute_isPath := Walk.IsPath.reverseSplit T.yRoute T.yRoute_isPath T.y_mem
  zRoute_isPath := Walk.IsPath.reverseSplit T.zRoute T.zRoute_isPath T.z_mem
  x_mem := T.xRoute.mem_reverseSplit_terminal T.x_mem
  y_mem := T.yRoute.mem_reverseSplit_terminal T.y_mem
  z_mem := T.zRoute.mem_reverseSplit_terminal T.z_mem
  x_internal := ⟨T.x_internal.2, T.x_internal.1⟩
  y_internal := ⟨T.y_internal.2, T.y_internal.1⟩
  z_internal := ⟨T.z_internal.2, T.z_internal.1⟩
  xRoute_inter_yRoute := by
    intro w hwX hwY
    rcases T.xRoute_inter_yRoute w
        (T.xRoute.reverseSplit_support_subset T.x_mem hwX)
        (T.yRoute.reverseSplit_support_subset T.y_mem hwY) with hA | hB
    · exact Or.inr hA
    · exact Or.inl hB
  xRoute_inter_zRoute := by
    intro w hwX hwZ
    rcases T.xRoute_inter_zRoute w
        (T.xRoute.reverseSplit_support_subset T.x_mem hwX)
        (T.zRoute.reverseSplit_support_subset T.z_mem hwZ) with hA | hB
    · exact Or.inr hA
    · exact Or.inl hB
  yRoute_inter_zRoute := by
    intro w hwY hwZ
    rcases T.yRoute_inter_zRoute w
        (T.yRoute.reverseSplit_support_subset T.y_mem hwY)
        (T.zRoute.reverseSplit_support_subset T.z_mem hwZ) with hA | hB
    · exact Or.inr hA
    · exact Or.inl hB

@[simp] theorem reverseABSource_xArmA :
    (reverseABSource T).xArmA = T.xArmB := by
  simpa only [reverseABSource, WatkinsMesnerK32Source.xArmA,
    WatkinsMesnerK32Source.xArmB] using
      Walk.IsPath.reverseSplit_armA T.xRoute T.xRoute_isPath T.x_mem

@[simp] theorem reverseABSource_xArmB :
    (reverseABSource T).xArmB = T.xArmA := by
  simpa only [reverseABSource, WatkinsMesnerK32Source.xArmA,
    WatkinsMesnerK32Source.xArmB] using
      Walk.IsPath.reverseSplit_armB T.xRoute T.xRoute_isPath T.x_mem

@[simp] theorem reverseABSource_yArmA :
    (reverseABSource T).yArmA = T.yArmB := by
  simpa only [reverseABSource, WatkinsMesnerK32Source.yArmA,
    WatkinsMesnerK32Source.yArmB] using
      Walk.IsPath.reverseSplit_armA T.yRoute T.yRoute_isPath T.y_mem

@[simp] theorem reverseABSource_yArmB :
    (reverseABSource T).yArmB = T.yArmA := by
  simpa only [reverseABSource, WatkinsMesnerK32Source.yArmA,
    WatkinsMesnerK32Source.yArmB] using
      Walk.IsPath.reverseSplit_armB T.yRoute T.yRoute_isPath T.y_mem

@[simp] theorem reverseABSource_zArmA :
    (reverseABSource T).zArmA = T.zArmB := by
  simpa only [reverseABSource, WatkinsMesnerK32Source.zArmA,
    WatkinsMesnerK32Source.zArmB] using
      Walk.IsPath.reverseSplit_armA T.zRoute T.zRoute_isPath T.z_mem

@[simp] theorem reverseABSource_zArmB :
    (reverseABSource T).zArmB = T.zArmA := by
  simpa only [reverseABSource, WatkinsMesnerK32Source.zArmA,
    WatkinsMesnerK32Source.zArmB] using
      Walk.IsPath.reverseSplit_armB T.zRoute T.zRoute_isPath T.z_mem

/-- Reverse the orientation of all three maximal separators.  Their side
components are transported across the unordered boundary pairs. -/
noncomputable def reverseABTriple (M : WatkinsMesnerMaximalTriple T) :
    WatkinsMesnerMaximalTriple (reverseABSource T) := by
  have hxNewOld : ∀ w,
      w ∈ (reverseABSource T).xRim.support → w ∈ T.xRim.support := by
    intro w hw
    simp only [reverseABSource, WatkinsMesnerK32Source.xRim,
      Walk.mem_support_append_iff, Walk.support_reverse,
      List.mem_reverse] at hw ⊢
    exact hw.elim
      (fun h ↦ Or.inl (T.yRoute.reverseSplit_support_subset T.y_mem h))
      (fun h ↦ Or.inr (T.zRoute.reverseSplit_support_subset T.z_mem h))
  have hxOldNew : ∀ w,
      w ∈ T.xRim.support → w ∈ (reverseABSource T).xRim.support := by
    intro w hw
    simp only [reverseABSource, WatkinsMesnerK32Source.xRim,
      Walk.mem_support_append_iff, Walk.support_reverse,
      List.mem_reverse] at hw ⊢
    exact hw.elim
      (fun h ↦ Or.inl (T.yRoute.support_subset_reverseSplit T.y_mem h))
      (fun h ↦ Or.inr (T.zRoute.support_subset_reverseSplit T.z_mem h))
  have hyNewOld : ∀ w,
      w ∈ (reverseABSource T).yRim.support → w ∈ T.yRim.support := by
    intro w hw
    simp only [reverseABSource, WatkinsMesnerK32Source.yRim,
      Walk.mem_support_append_iff, Walk.support_reverse,
      List.mem_reverse] at hw ⊢
    exact hw.elim
      (fun h ↦ Or.inl (T.xRoute.reverseSplit_support_subset T.x_mem h))
      (fun h ↦ Or.inr (T.zRoute.reverseSplit_support_subset T.z_mem h))
  have hyOldNew : ∀ w,
      w ∈ T.yRim.support → w ∈ (reverseABSource T).yRim.support := by
    intro w hw
    simp only [reverseABSource, WatkinsMesnerK32Source.yRim,
      Walk.mem_support_append_iff, Walk.support_reverse,
      List.mem_reverse] at hw ⊢
    exact hw.elim
      (fun h ↦ Or.inl (T.xRoute.support_subset_reverseSplit T.x_mem h))
      (fun h ↦ Or.inr (T.zRoute.support_subset_reverseSplit T.z_mem h))
  have hzNewOld : ∀ w,
      w ∈ (reverseABSource T).zRim.support → w ∈ T.zRim.support := by
    intro w hw
    simp only [reverseABSource, WatkinsMesnerK32Source.zRim,
      Walk.mem_support_append_iff, Walk.support_reverse,
      List.mem_reverse] at hw ⊢
    exact hw.elim
      (fun h ↦ Or.inl (T.xRoute.reverseSplit_support_subset T.x_mem h))
      (fun h ↦ Or.inr (T.yRoute.reverseSplit_support_subset T.y_mem h))
  have hzOldNew : ∀ w,
      w ∈ T.zRim.support → w ∈ (reverseABSource T).zRim.support := by
    intro w hw
    simp only [reverseABSource, WatkinsMesnerK32Source.zRim,
      Walk.mem_support_append_iff, Walk.support_reverse,
      List.mem_reverse] at hw ⊢
    exact hw.elim
      (fun h ↦ Or.inl (T.xRoute.support_subset_reverseSplit T.x_mem h))
      (fun h ↦ Or.inr (T.yRoute.support_subset_reverseSplit T.y_mem h))
  let xS₀ := M.xSep.flipAB hxNewOld
  let yS₀ := M.ySep.flipAB hyNewOld
  let zS₀ := M.zSep.flipAB hzNewOld
  have hxLeft : xS₀.left ∈ (reverseABSource T).xArmA.support := by
    rw [reverseABSource_xArmA]
    exact xS₀.left_mem_aArm
  have hxRight : xS₀.right ∈ (reverseABSource T).xArmB.support := by
    rw [reverseABSource_xArmB]
    exact xS₀.right_mem_bArm
  have hyLeft : yS₀.left ∈ (reverseABSource T).yArmA.support := by
    rw [reverseABSource_yArmA]
    exact yS₀.left_mem_aArm
  have hyRight : yS₀.right ∈ (reverseABSource T).yArmB.support := by
    rw [reverseABSource_yArmB]
    exact yS₀.right_mem_bArm
  have hzLeft : zS₀.left ∈ (reverseABSource T).zArmA.support := by
    rw [reverseABSource_zArmA]
    exact zS₀.left_mem_aArm
  have hzRight : zS₀.right ∈ (reverseABSource T).zArmB.support := by
    rw [reverseABSource_zArmB]
    exact zS₀.right_mem_bArm
  let xS := xS₀.changeArms hxLeft hxRight
  let yS := yS₀.changeArms hyLeft hyRight
  let zS := zS₀.changeArms hzLeft hzRight
  have hxMax : xS.IsMaximal := by
    dsimp only [xS]
    apply RoutedCycleSeparator.IsMaximal.changeArms xS₀
      (RoutedCycleSeparator.IsMaximal.flipAB
        M.xSep M.x_maximal hxNewOld hxOldNew) hxLeft hxRight
    · intro w hw
      rwa [reverseABSource_xArmA] at hw
    · intro w hw
      rwa [reverseABSource_xArmB] at hw
  have hyMax : yS.IsMaximal := by
    dsimp only [yS]
    apply RoutedCycleSeparator.IsMaximal.changeArms yS₀
      (RoutedCycleSeparator.IsMaximal.flipAB
        M.ySep M.y_maximal hyNewOld hyOldNew) hyLeft hyRight
    · intro w hw
      rwa [reverseABSource_yArmA] at hw
    · intro w hw
      rwa [reverseABSource_yArmB] at hw
  have hzMax : zS.IsMaximal := by
    dsimp only [zS]
    apply RoutedCycleSeparator.IsMaximal.changeArms zS₀
      (RoutedCycleSeparator.IsMaximal.flipAB
        M.zSep M.z_maximal hzNewOld hzOldNew) hzLeft hzRight
    · intro w hw
      rwa [reverseABSource_zArmA] at hw
    · intro w hw
      rwa [reverseABSource_zArmB] at hw
  exact {
    xSep := xS
    ySep := yS
    zSep := zS
    x_maximal := hxMax
    y_maximal := hyMax
    z_maximal := hzMax }

@[simp] theorem reverseABTriple_xSep_left :
    (reverseABTriple M).xSep.left = M.xSep.right := by
  simp [reverseABTriple, RoutedCycleSeparator.changeArms,
    RoutedCycleSeparator.flipAB]

@[simp] theorem reverseABTriple_ySep_left :
    (reverseABTriple M).ySep.left = M.ySep.right := by
  simp [reverseABTriple, RoutedCycleSeparator.changeArms,
    RoutedCycleSeparator.flipAB]

@[simp] theorem reverseABTriple_zSep_left :
    (reverseABTriple M).zSep.left = M.zSep.right := by
  simp [reverseABTriple, RoutedCycleSeparator.changeArms,
    RoutedCycleSeparator.flipAB]

@[simp] theorem reverseABTriple_xSep_right :
    (reverseABTriple M).xSep.right = M.xSep.left := by
  simp [reverseABTriple, RoutedCycleSeparator.changeArms,
    RoutedCycleSeparator.flipAB]

@[simp] theorem reverseABTriple_ySep_right :
    (reverseABTriple M).ySep.right = M.ySep.left := by
  simp [reverseABTriple, RoutedCycleSeparator.changeArms,
    RoutedCycleSeparator.flipAB]

@[simp] theorem reverseABTriple_zSep_right :
    (reverseABTriple M).zSep.right = M.zSep.left := by
  simp [reverseABTriple, RoutedCycleSeparator.changeArms,
    RoutedCycleSeparator.flipAB]

/-- Relabel a maximal triple along `swapYZSource`.  The only nonliteral
field is the `x`-rim, whose orientation is reversed; `changeRim` transfers
both the separator and its maximality. -/
noncomputable def swapYZTriple (M : WatkinsMesnerMaximalTriple T) :
    WatkinsMesnerMaximalTriple (swapYZSource T) := by
  have hxNewOld : ∀ w,
      w ∈ (swapYZSource T).xRim.support → w ∈ T.xRim.support := by
    intro w hw
    simp only [swapYZSource, WatkinsMesnerK32Source.xRim,
      Walk.mem_support_append_iff, Walk.support_reverse,
      List.mem_reverse] at hw ⊢
    exact hw.elim Or.inr Or.inl
  have hxOldNew : ∀ w,
      w ∈ T.xRim.support → w ∈ (swapYZSource T).xRim.support := by
    intro w hw
    simp only [swapYZSource, WatkinsMesnerK32Source.xRim,
      Walk.mem_support_append_iff, Walk.support_reverse,
      List.mem_reverse] at hw ⊢
    exact hw.elim Or.inr Or.inl
  let xS₀ := M.xSep.changeRim hxNewOld
  let xS : RoutedCycleSeparator (swapYZSource T).xArmA
      (swapYZSource T).xArmB (swapYZSource T).xRim := by
    change RoutedCycleSeparator T.xArmA T.xArmB (swapYZSource T).xRim
    exact xS₀
  let yS : RoutedCycleSeparator (swapYZSource T).yArmA
      (swapYZSource T).yArmB (swapYZSource T).yRim := by
    change RoutedCycleSeparator T.zArmA T.zArmB T.zRim
    exact M.zSep
  let zS : RoutedCycleSeparator (swapYZSource T).zArmA
      (swapYZSource T).zArmB (swapYZSource T).zRim := by
    change RoutedCycleSeparator T.yArmA T.yArmB T.yRim
    exact M.ySep
  refine {
    xSep := xS
    ySep := yS
    zSep := zS
    x_maximal := ?_
    y_maximal := ?_
    z_maximal := ?_ }
  · change xS.IsMaximal
    have h := RoutedCycleSeparator.IsMaximal.changeRim
      M.xSep M.x_maximal hxNewOld hxOldNew
    simpa only [xS, xS₀, swapYZSource, id_eq,
      WatkinsMesnerK32Source.xArmA,
      WatkinsMesnerK32Source.xArmB] using h
  · change yS.IsMaximal
    change M.zSep.IsMaximal
    exact M.z_maximal
  · change zS.IsMaximal
    change M.ySep.IsMaximal
    exact M.y_maximal

/-- Relabel a maximal triple along the cyclic source permutation. -/
noncomputable def rotateYZXTriple (M : WatkinsMesnerMaximalTriple T) :
    WatkinsMesnerMaximalTriple (rotateYZXSource T) := by
  have hxNewOld : ∀ w,
      w ∈ (rotateYZXSource T).xRim.support → w ∈ T.yRim.support := by
    intro w hw
    simp only [rotateYZXSource, WatkinsMesnerK32Source.xRim,
      WatkinsMesnerK32Source.yRim, Walk.mem_support_append_iff,
      Walk.support_reverse, List.mem_reverse] at hw ⊢
    exact hw.elim Or.inr Or.inl
  have hxOldNew : ∀ w,
      w ∈ T.yRim.support → w ∈ (rotateYZXSource T).xRim.support := by
    intro w hw
    simp only [rotateYZXSource, WatkinsMesnerK32Source.xRim,
      WatkinsMesnerK32Source.yRim, Walk.mem_support_append_iff,
      Walk.support_reverse, List.mem_reverse] at hw ⊢
    exact hw.elim Or.inr Or.inl
  have hyNewOld : ∀ w,
      w ∈ (rotateYZXSource T).yRim.support → w ∈ T.zRim.support := by
    intro w hw
    simp only [rotateYZXSource, WatkinsMesnerK32Source.yRim,
      WatkinsMesnerK32Source.zRim, Walk.mem_support_append_iff,
      Walk.support_reverse, List.mem_reverse] at hw ⊢
    exact hw.elim Or.inr Or.inl
  have hyOldNew : ∀ w,
      w ∈ T.zRim.support → w ∈ (rotateYZXSource T).yRim.support := by
    intro w hw
    simp only [rotateYZXSource, WatkinsMesnerK32Source.yRim,
      WatkinsMesnerK32Source.zRim, Walk.mem_support_append_iff,
      Walk.support_reverse, List.mem_reverse] at hw ⊢
    exact hw.elim Or.inr Or.inl
  let xS₀ := M.ySep.changeRim hxNewOld
  let yS₀ := M.zSep.changeRim hyNewOld
  let xS : RoutedCycleSeparator (rotateYZXSource T).xArmA
      (rotateYZXSource T).xArmB (rotateYZXSource T).xRim := by
    change RoutedCycleSeparator T.yArmA T.yArmB (rotateYZXSource T).xRim
    exact xS₀
  let yS : RoutedCycleSeparator (rotateYZXSource T).yArmA
      (rotateYZXSource T).yArmB (rotateYZXSource T).yRim := by
    change RoutedCycleSeparator T.zArmA T.zArmB (rotateYZXSource T).yRim
    exact yS₀
  let zS : RoutedCycleSeparator (rotateYZXSource T).zArmA
      (rotateYZXSource T).zArmB (rotateYZXSource T).zRim := by
    change RoutedCycleSeparator T.xArmA T.xArmB T.xRim
    exact M.xSep
  refine {
    xSep := xS
    ySep := yS
    zSep := zS
    x_maximal := ?_
    y_maximal := ?_
    z_maximal := ?_ }
  · change xS.IsMaximal
    have h := RoutedCycleSeparator.IsMaximal.changeRim
      M.ySep M.y_maximal hxNewOld hxOldNew
    simpa only [xS, xS₀, rotateYZXSource, id_eq,
      WatkinsMesnerK32Source.xArmA, WatkinsMesnerK32Source.xArmB,
      WatkinsMesnerK32Source.yArmA,
      WatkinsMesnerK32Source.yArmB] using h
  · change yS.IsMaximal
    have h := RoutedCycleSeparator.IsMaximal.changeRim
      M.zSep M.z_maximal hyNewOld hyOldNew
    simpa only [yS, yS₀, rotateYZXSource, id_eq,
      WatkinsMesnerK32Source.yArmA, WatkinsMesnerK32Source.yArmB,
      WatkinsMesnerK32Source.zArmA,
      WatkinsMesnerK32Source.zArmB] using h
  · change zS.IsMaximal
    change M.xSep.IsMaximal
    exact M.x_maximal

@[simp] theorem swapYZTriple_xSep_left :
    (swapYZTriple M).xSep.left = M.xSep.left := by
  simp [swapYZTriple, swapYZSource, RoutedCycleSeparator.changeRim,
    WatkinsMesnerK32Source.xArmA, WatkinsMesnerK32Source.xArmB]

@[simp] theorem swapYZTriple_ySep_left :
    (swapYZTriple M).ySep.left = M.zSep.left := by
  simp [swapYZTriple, swapYZSource, WatkinsMesnerK32Source.yArmA,
    WatkinsMesnerK32Source.yArmB, WatkinsMesnerK32Source.yRim,
    WatkinsMesnerK32Source.zArmA, WatkinsMesnerK32Source.zArmB,
    WatkinsMesnerK32Source.zRim]
  change M.zSep.left = M.zSep.left
  rfl

@[simp] theorem swapYZTriple_zSep_left :
    (swapYZTriple M).zSep.left = M.ySep.left := by
  simp [swapYZTriple, swapYZSource, WatkinsMesnerK32Source.zArmA,
    WatkinsMesnerK32Source.zArmB, WatkinsMesnerK32Source.zRim,
    WatkinsMesnerK32Source.yArmA, WatkinsMesnerK32Source.yArmB,
    WatkinsMesnerK32Source.yRim]
  change M.ySep.left = M.ySep.left
  rfl

@[simp] theorem swapYZTriple_xSep_right :
    (swapYZTriple M).xSep.right = M.xSep.right := by
  simp [swapYZTriple, swapYZSource, RoutedCycleSeparator.changeRim,
    WatkinsMesnerK32Source.xArmA, WatkinsMesnerK32Source.xArmB]

@[simp] theorem swapYZTriple_ySep_right :
    (swapYZTriple M).ySep.right = M.zSep.right := by
  simp [swapYZTriple, swapYZSource, WatkinsMesnerK32Source.yArmA,
    WatkinsMesnerK32Source.yArmB, WatkinsMesnerK32Source.yRim,
    WatkinsMesnerK32Source.zArmA, WatkinsMesnerK32Source.zArmB,
    WatkinsMesnerK32Source.zRim]
  change M.zSep.right = M.zSep.right
  rfl

@[simp] theorem swapYZTriple_zSep_right :
    (swapYZTriple M).zSep.right = M.ySep.right := by
  simp [swapYZTriple, swapYZSource, WatkinsMesnerK32Source.zArmA,
    WatkinsMesnerK32Source.zArmB, WatkinsMesnerK32Source.zRim,
    WatkinsMesnerK32Source.yArmA, WatkinsMesnerK32Source.yArmB,
    WatkinsMesnerK32Source.yRim]
  change M.ySep.right = M.ySep.right
  rfl

theorem swapYZTriple_aSet : (swapYZTriple M).aSet = M.aSet := by
  ext w
  simp only [aSet, Finset.mem_insert, Finset.mem_singleton,
    swapYZTriple_xSep_left, swapYZTriple_ySep_left,
    swapYZTriple_zSep_left]
  aesop

theorem swapYZTriple_bSet : (swapYZTriple M).bSet = M.bSet := by
  ext w
  simp only [bSet, Finset.mem_insert, Finset.mem_singleton,
    swapYZTriple_xSep_right, swapYZTriple_ySep_right,
    swapYZTriple_zSep_right]
  aesop

theorem swapYZTriple_xPart : (swapYZTriple M).xPart = M.xPart := by
  ext w
  simp [xPart, mem_componentCarrier, swapYZTriple, swapYZSource,
    RoutedCycleSeparator.changeRim, WatkinsMesnerK32Source.xArmA,
    WatkinsMesnerK32Source.xArmB]

theorem swapYZTriple_yPart : (swapYZTriple M).yPart = M.zPart := by
  change M.zPart = M.zPart
  rfl

theorem swapYZTriple_zPart : (swapYZTriple M).zPart = M.yPart := by
  change M.yPart = M.yPart
  rfl

@[simp] theorem rotateYZXTriple_xSep_left :
    (rotateYZXTriple M).xSep.left = M.ySep.left := by
  simp [rotateYZXTriple, rotateYZXSource,
    RoutedCycleSeparator.changeRim, WatkinsMesnerK32Source.xArmA,
    WatkinsMesnerK32Source.xArmB, WatkinsMesnerK32Source.yArmA,
    WatkinsMesnerK32Source.yArmB]

@[simp] theorem rotateYZXTriple_ySep_left :
    (rotateYZXTriple M).ySep.left = M.zSep.left := by
  simp [rotateYZXTriple, rotateYZXSource,
    RoutedCycleSeparator.changeRim, WatkinsMesnerK32Source.yArmA,
    WatkinsMesnerK32Source.yArmB, WatkinsMesnerK32Source.zArmA,
    WatkinsMesnerK32Source.zArmB]

@[simp] theorem rotateYZXTriple_zSep_left :
    (rotateYZXTriple M).zSep.left = M.xSep.left := by
  simp [rotateYZXTriple, rotateYZXSource, WatkinsMesnerK32Source.zArmA,
    WatkinsMesnerK32Source.zArmB, WatkinsMesnerK32Source.zRim,
    WatkinsMesnerK32Source.xArmA, WatkinsMesnerK32Source.xArmB,
    WatkinsMesnerK32Source.xRim]
  change M.xSep.left = M.xSep.left
  rfl

@[simp] theorem rotateYZXTriple_xSep_right :
    (rotateYZXTriple M).xSep.right = M.ySep.right := by
  simp [rotateYZXTriple, rotateYZXSource,
    RoutedCycleSeparator.changeRim, WatkinsMesnerK32Source.xArmA,
    WatkinsMesnerK32Source.xArmB, WatkinsMesnerK32Source.yArmA,
    WatkinsMesnerK32Source.yArmB]

@[simp] theorem rotateYZXTriple_ySep_right :
    (rotateYZXTriple M).ySep.right = M.zSep.right := by
  simp [rotateYZXTriple, rotateYZXSource,
    RoutedCycleSeparator.changeRim, WatkinsMesnerK32Source.yArmA,
    WatkinsMesnerK32Source.yArmB, WatkinsMesnerK32Source.zArmA,
    WatkinsMesnerK32Source.zArmB]

@[simp] theorem rotateYZXTriple_zSep_right :
    (rotateYZXTriple M).zSep.right = M.xSep.right := by
  simp [rotateYZXTriple, rotateYZXSource, WatkinsMesnerK32Source.zArmA,
    WatkinsMesnerK32Source.zArmB, WatkinsMesnerK32Source.zRim,
    WatkinsMesnerK32Source.xArmA, WatkinsMesnerK32Source.xArmB,
    WatkinsMesnerK32Source.xRim]
  change M.xSep.right = M.xSep.right
  rfl

theorem rotateYZXTriple_aSet : (rotateYZXTriple M).aSet = M.aSet := by
  ext w
  simp only [aSet, Finset.mem_insert, Finset.mem_singleton,
    rotateYZXTriple_xSep_left, rotateYZXTriple_ySep_left,
    rotateYZXTriple_zSep_left]
  aesop

theorem rotateYZXTriple_bSet : (rotateYZXTriple M).bSet = M.bSet := by
  ext w
  simp only [bSet, Finset.mem_insert, Finset.mem_singleton,
    rotateYZXTriple_xSep_right, rotateYZXTriple_ySep_right,
    rotateYZXTriple_zSep_right]
  aesop

theorem rotateYZXTriple_xPart : (rotateYZXTriple M).xPart = M.yPart := by
  ext w
  simp [xPart, yPart, mem_componentCarrier, rotateYZXTriple,
    rotateYZXSource, RoutedCycleSeparator.changeRim,
    WatkinsMesnerK32Source.xArmA, WatkinsMesnerK32Source.xArmB,
    WatkinsMesnerK32Source.yArmA, WatkinsMesnerK32Source.yArmB]

theorem rotateYZXTriple_yPart : (rotateYZXTriple M).yPart = M.zPart := by
  ext w
  simp [yPart, zPart, mem_componentCarrier, rotateYZXTriple,
    rotateYZXSource, RoutedCycleSeparator.changeRim,
    WatkinsMesnerK32Source.yArmA, WatkinsMesnerK32Source.yArmB,
    WatkinsMesnerK32Source.zArmA, WatkinsMesnerK32Source.zArmB]

theorem rotateYZXTriple_zPart : (rotateYZXTriple M).zPart = M.xPart := by
  change M.xPart = M.xPart
  rfl

/-- AHT condition (v): the A-boundary cannot have cardinality two. -/
theorem aSet_card_ne_two
    (hdelete : ∀ d : V, (G.induce fun w : V ↦ w ≠ d).Connected)
    (hno : ¬HasCycleThroughThree G x y z) :
    M.aSet.card ≠ 2 := by
  intro hcard
  rcases M.A_branch_pattern_of_card_two hcard with
      ⟨hxy, hxBranch, hzBranch⟩ |
      ⟨hxz, hxBranch, hyBranch⟩ |
      ⟨hyz, hyBranch, hxBranch⟩
  · have hzX : M.zSep.left ≠ M.xSep.left :=
      fun h ↦ hzBranch (h.trans hxBranch)
    exact hno (M.hasCycleThroughThree_of_xA_eq_yA hdelete hxy hzX)
  · let M' := swapYZTriple M
    have hxy' : M'.xSep.left = M'.ySep.left := by
      simpa only [M', swapYZTriple_xSep_left, swapYZTriple_ySep_left]
        using hxz
    have hyX : M.ySep.left ≠ M.xSep.left :=
      fun h ↦ hyBranch (h.trans hxBranch)
    have hz' : M'.zSep.left ≠ M'.xSep.left := by
      simpa only [M', swapYZTriple_zSep_left, swapYZTriple_xSep_left]
        using hyX
    obtain ⟨r, C, hC, hx, hz, hy⟩ :=
      M'.hasCycleThroughThree_of_xA_eq_yA hdelete hxy' hz'
    exact hno ⟨r, C, hC, hx, hy, hz⟩
  · let M' := rotateYZXTriple M
    have hxy' : M'.xSep.left = M'.ySep.left := by
      simpa only [M', rotateYZXTriple_xSep_left,
        rotateYZXTriple_ySep_left] using hyz
    have hxY : M.xSep.left ≠ M.ySep.left :=
      fun h ↦ hxBranch (h.trans hyBranch)
    have hz' : M'.zSep.left ≠ M'.xSep.left := by
      simpa only [M', rotateYZXTriple_zSep_left,
        rotateYZXTriple_xSep_left] using hxY
    obtain ⟨r, C, hC, hy, hz, hx⟩ :=
      M'.hasCycleThroughThree_of_xA_eq_yA hdelete hxy' hz'
    exact hno ⟨r, C, hC, hx, hy, hz⟩

theorem reverseABTriple_aSet :
    (reverseABTriple M).aSet = M.bSet := by
  ext w
  simp only [aSet, bSet, Finset.mem_insert, Finset.mem_singleton,
    reverseABTriple_xSep_left, reverseABTriple_ySep_left,
    reverseABTriple_zSep_left]

theorem reverseABTriple_bSet :
    (reverseABTriple M).bSet = M.aSet := by
  ext w
  simp only [bSet, aSet, Finset.mem_insert, Finset.mem_singleton,
    reverseABTriple_xSep_right, reverseABTriple_ySep_right,
    reverseABTriple_zSep_right]

theorem reverseABTriple_xPart : (reverseABTriple M).xPart = M.xPart := by
  ext w
  simp only [xPart, mem_componentCarrier]
  change w ∈ (ComponentCompl.transport _ M.xSep.side : Set V) ↔
    w ∈ (M.xSep.side : Set V)
  exact ComponentCompl.mem_transport _ _ _

theorem reverseABTriple_yPart : (reverseABTriple M).yPart = M.yPart := by
  ext w
  simp only [yPart, mem_componentCarrier]
  change w ∈ (ComponentCompl.transport _ M.ySep.side : Set V) ↔
    w ∈ (M.ySep.side : Set V)
  exact ComponentCompl.mem_transport _ _ _

theorem reverseABTriple_zPart : (reverseABTriple M).zPart = M.zPart := by
  ext w
  simp only [zPart, mem_componentCarrier]
  change w ∈ (ComponentCompl.transport _ M.zSep.side : Set V) ↔
    w ∈ (M.zSep.side : Set V)
  exact ComponentCompl.mem_transport _ _ _

/-- The B-side half of AHT condition (v), obtained by reversing all three
source routes and applying the proved A-side theorem. -/
theorem bSet_card_ne_two
    (hdelete : ∀ d : V, (G.induce fun w : V ↦ w ≠ d).Connected)
    (hno : ¬HasCycleThroughThree G x y z) :
    M.bSet.card ≠ 2 := by
  intro hcard
  let M' := reverseABTriple M
  have hAcard : M'.aSet.card = 2 := by
    simpa only [M', reverseABTriple_aSet] using hcard
  exact M'.aSet_card_ne_two hdelete hno hAcard

theorem aSet_card_one_or_three
    (hdelete : ∀ d : V, (G.induce fun w : V ↦ w ≠ d).Connected)
    (hno : ¬HasCycleThroughThree G x y z) :
    M.aSet.card = 1 ∨ M.aSet.card = 3 := by
  rcases M.aSet_card_trichotomy with h | h | h
  · exact Or.inl h
  · exact (M.aSet_card_ne_two hdelete hno h).elim
  · exact Or.inr h

theorem bSet_card_one_or_three
    (hdelete : ∀ d : V, (G.induce fun w : V ↦ w ≠ d).Connected)
    (hno : ¬HasCycleThroughThree G x y z) :
    M.bSet.card = 1 ∨ M.bSet.card = 3 := by
  rcases M.bSet_card_trichotomy with h | h | h
  · exact Or.inl h
  · exact (M.bSet_card_ne_two hdelete hno h).elim
  · exact Or.inr h

/-! ### Cutting a candidate connector at one of its cut vertices

The minimization argument on p.15 repeatedly replaces a connected candidate
by the part consisting of one component after deleting a cut vertex, with the
cut vertex put back.  We package that operation at the level of ambient
subgraphs.  The component itself lives in `H.coe`; `coeSubgraph` maps the
induced end piece back into the ambient graph without adding any edges. -/

/-- The component `K` of `H-d`, together with `d`, regarded again as an
ambient subgraph of `G`. -/
noncomputable def cutComponentPiece (H : G.Subgraph) (d : H.verts)
    (K : (deleteVertex H.coe d).ConnectedComponent) : G.Subgraph :=
  Subgraph.coeSubgraph
    ((⊤ : H.coe.Subgraph).induce (ComponentEndBlock.verts d K))

/-- Remove one component side of `H-d`, retaining the cut vertex and all
other components.  This is the pruning operation needed when a component
of a connector cut contains none of the three prescribed attachments. -/
noncomputable def cutComponentComplement (H : G.Subgraph) (d : H.verts)
    (K : (deleteVertex H.coe d).ConnectedComponent) : G.Subgraph :=
  Subgraph.coeSubgraph
    ((⊤ : H.coe.Subgraph).induce
      ((ComponentEndBlock.side d K)ᶜ))

theorem cutComponentPiece_le (H : G.Subgraph) (d : H.verts)
    (K : (deleteVertex H.coe d).ConnectedComponent) :
    cutComponentPiece H d K ≤ H :=
  Subgraph.coeSubgraph_le _

theorem cutComponentComplement_le (H : G.Subgraph) (d : H.verts)
    (K : (deleteVertex H.coe d).ConnectedComponent) :
    cutComponentComplement H d K ≤ H :=
  Subgraph.coeSubgraph_le _

@[simp] theorem mem_cutComponentPiece_verts_iff (H : G.Subgraph)
    (d : H.verts) (K : (deleteVertex H.coe d).ConnectedComponent)
    (w : V) :
    w ∈ (cutComponentPiece H d K).verts ↔
      ∃ hw : w ∈ H.verts,
        (⟨w, hw⟩ : H.verts) ∈ ComponentEndBlock.verts d K := by
  simp [cutComponentPiece]

@[simp] theorem mem_cutComponentComplement_verts_iff (H : G.Subgraph)
    (d : H.verts) (K : (deleteVertex H.coe d).ConnectedComponent)
    (w : V) :
    w ∈ (cutComponentComplement H d K).verts ↔
      ∃ hw : w ∈ H.verts,
        (⟨w, hw⟩ : H.verts) ∉ ComponentEndBlock.side d K := by
  simp only [cutComponentComplement, Subgraph.verts_coeSubgraph,
    Subgraph.induce_verts, Set.mem_image, Set.mem_compl_iff]
  constructor
  · rintro ⟨hw, hside, rfl⟩
    exact ⟨hw.2, hside⟩
  · rintro ⟨hw, hside⟩
    exact ⟨⟨w, hw⟩, hside, rfl⟩

@[simp] theorem cut_mem_cutComponentPiece (H : G.Subgraph) (d : H.verts)
    (K : (deleteVertex H.coe d).ConnectedComponent) :
    d.1 ∈ (cutComponentPiece H d K).verts := by
  rw [mem_cutComponentPiece_verts_iff]
  exact ⟨d.2, by simp [ComponentEndBlock.verts]⟩

@[simp] theorem cut_mem_cutComponentComplement (H : G.Subgraph)
    (d : H.verts) (K : (deleteVertex H.coe d).ConnectedComponent) :
    d.1 ∈ (cutComponentComplement H d K).verts := by
  rw [mem_cutComponentComplement_verts_iff]
  exact ⟨d.2, ComponentEndBlock.cut_not_mem_side d K⟩

/-- A component end piece of a connected candidate remains connected after
it is mapped back to the ambient graph. -/
theorem cutComponentPiece_connected (H : G.Subgraph) (hH : H.Connected)
    (d : H.verts) (K : (deleteVertex H.coe d).ConnectedComponent) :
    (cutComponentPiece H d K).Connected := by
  apply Subgraph.Connected.map H.hom
  rw [← connected_induce_iff]
  exact ComponentEndBlock.verts_connected hH.coe K

/-- The component side maps onto the end piece with its cut vertex deleted.
Using inequality of underlying ambient vertices in the target keeps the
dependent cut-vertex witness out of the definition. -/
noncomputable def cutSideToPieceDeleteHom (H : G.Subgraph)
    (d : H.verts) (K : (deleteVertex H.coe d).ConnectedComponent) :
    H.coe.induce (ComponentEndBlock.side d K) →g
      (cutComponentPiece H d K).coe.induce
        (fun w : (cutComponentPiece H d K).verts ↦ w.1 ≠ d.1) where
  toFun q := ⟨⟨q.1.1, by
      rw [mem_cutComponentPiece_verts_iff]
      exact ⟨q.1.2, Set.mem_insert_iff.mpr (Or.inr q.2)⟩⟩, by
    intro hqd
    apply ComponentEndBlock.cut_not_mem_side d K
    have hq : q.1 = d := Subtype.ext hqd
    have hside := q.2
    rw [hq] at hside
    exact hside⟩
  map_rel' := by
    intro q r hqr
    apply (Subgraph.coeSubgraph_adj
      ((⊤ : H.coe.Subgraph).induce (ComponentEndBlock.verts d K))
      q.1.1 r.1.1).2
    refine ⟨q.1.2, r.1.2, ?_⟩
    exact ⟨Set.mem_insert_iff.mpr (Or.inr q.2),
      Set.mem_insert_iff.mpr (Or.inr r.2), hqr⟩

/-- Every vertex of the deleted end piece comes from its component side. -/
theorem cutSideToPieceDeleteHom_surjective (H : G.Subgraph)
    (d : H.verts) (K : (deleteVertex H.coe d).ConnectedComponent) :
    Function.Surjective (cutSideToPieceDeleteHom H d K) := by
  intro w
  obtain ⟨hwH, hwPiece⟩ :=
    (mem_cutComponentPiece_verts_iff H d K w.1.1).mp w.1.2
  have hwSide :
      (⟨w.1.1, hwH⟩ : H.verts) ∈ ComponentEndBlock.side d K := by
    rw [ComponentEndBlock.verts, Set.mem_insert_iff] at hwPiece
    exact hwPiece.resolve_left (fun h ↦ w.2 (congrArg Subtype.val h))
  refine ⟨⟨⟨w.1.1, hwH⟩, hwSide⟩, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  rfl

/-- Removing the restored cut vertex from a component end piece leaves the
original connected component side, hence a connected graph. -/
theorem cutComponentPiece_delete_cut_connected (H : G.Subgraph)
    (d : H.verts) (K : (deleteVertex H.coe d).ConnectedComponent) :
    ((cutComponentPiece H d K).coe.induce
      (fun w : (cutComponentPiece H d K).verts ↦
        w ≠ ⟨d.1, cut_mem_cutComponentPiece H d K⟩)).Connected := by
  have hconn :
      ((cutComponentPiece H d K).coe.induce
        (fun w : (cutComponentPiece H d K).verts ↦ w.1 ≠ d.1)).Connected :=
    (ComponentEndBlock.side_connected d K).map
      (cutSideToPieceDeleteHom H d K)
      (cutSideToPieceDeleteHom_surjective H d K)
  have hpred :
      (fun w : (cutComponentPiece H d K).verts ↦ w.1 ≠ d.1) =
        (fun w : (cutComponentPiece H d K).verts ↦
          w ≠ ⟨d.1, cut_mem_cutComponentPiece H d K⟩) := by
    funext w
    apply propext
    constructor
    · intro h hwd
      exact h (congrArg Subtype.val hwd)
    · intro h hwd
      apply h
      apply Subtype.ext
      exact hwd
  rw [hpred] at hconn
  exact hconn

/-- A pair of disjoint connected outer subgraphs containing all three
attachments on their respective sides and avoiding the three displayed
terminal components.  This is the exact finite object denoted `(G_A,G_B)`
on pp.14--16 of AHT. -/
structure ABConnectorPair where
  aGraph : G.Subgraph
  bGraph : G.Subgraph
  a_connected : aGraph.Connected
  b_connected : bGraph.Connected
  a_contains : ∀ a ∈ M.aSet, a ∈ aGraph.verts
  b_contains : ∀ b ∈ M.bSet, b ∈ bGraph.verts
  vertex_disjoint : Disjoint aGraph.verts bGraph.verts
  avoids_terminal_parts :
    Disjoint (aGraph.verts ∪ bGraph.verts)
      ((M.xPart : Set V) ∪ (M.yPart : Set V) ∪ (M.zPart : Set V))

/-- The six attachment vertices, typed in their corresponding connector
subgraphs. -/
def ABConnectorPair.xAIn (C : M.ABConnectorPair) : C.aGraph.verts :=
  ⟨M.xSep.left, C.a_contains _ M.xA_mem_aSet⟩

def ABConnectorPair.yAIn (C : M.ABConnectorPair) : C.aGraph.verts :=
  ⟨M.ySep.left, C.a_contains _ M.yA_mem_aSet⟩

def ABConnectorPair.zAIn (C : M.ABConnectorPair) : C.aGraph.verts :=
  ⟨M.zSep.left, C.a_contains _ M.zA_mem_aSet⟩

def ABConnectorPair.xBIn (C : M.ABConnectorPair) : C.bGraph.verts :=
  ⟨M.xSep.right, C.b_contains _ M.xB_mem_bSet⟩

def ABConnectorPair.yBIn (C : M.ABConnectorPair) : C.bGraph.verts :=
  ⟨M.ySep.right, C.b_contains _ M.yB_mem_bSet⟩

def ABConnectorPair.zBIn (C : M.ABConnectorPair) : C.bGraph.verts :=
  ⟨M.zSep.right, C.b_contains _ M.zB_mem_bSet⟩

private theorem ABConnectorPair.terminalBridge_meets_aGraph_only_left
    (C : M.ABConnectorPair) {l r : V} {P : G.Walk l r}
    {D : Finset V}
    (hP : ∀ w, w ∈ P.support → w = l ∨ w = r ∨ w ∈ D)
    (hl : l ∈ M.aSet) (hr : r ∈ M.bSet)
    (hD : (D : Set V) ⊆
      (M.xPart : Set V) ∪ (M.yPart : Set V) ∪ (M.zPart : Set V))
    {w : V} (hwP : w ∈ P.support) (hwA : w ∈ C.aGraph.verts) :
    w = l := by
  rcases hP w hwP with h | h | hwD
  · exact h
  · subst w
    exact (Set.disjoint_left.mp C.vertex_disjoint hwA
      (C.b_contains r hr)).elim
  · exfalso
    exact Set.disjoint_left.mp C.avoids_terminal_parts
      (Or.inl hwA) (hD hwD)

private theorem ABConnectorPair.terminalBridge_meets_bGraph_only_right
    (C : M.ABConnectorPair) {l r : V} {P : G.Walk l r}
    {D : Finset V}
    (hP : ∀ w, w ∈ P.support → w = l ∨ w = r ∨ w ∈ D)
    (hl : l ∈ M.aSet) (hr : r ∈ M.bSet)
    (hD : (D : Set V) ⊆
      (M.xPart : Set V) ∪ (M.yPart : Set V) ∪ (M.zPart : Set V))
    {w : V} (hwP : w ∈ P.support) (hwB : w ∈ C.bGraph.verts) :
    w = r := by
  rcases hP w hwP with h | h | hwD
  · subst w
    exact (Set.disjoint_left.mp C.vertex_disjoint
      (C.a_contains l hl) hwB).elim
  · exact h
  · exfalso
    exact Set.disjoint_left.mp C.avoids_terminal_parts
      (Or.inr hwB) (hD hwD)

theorem ABConnectorPair.xTerminalBridge_meets_aGraph_only_left
    (C : M.ABConnectorPair) {w : V}
    (hwP : w ∈ M.xTerminalBridge.support) (hwA : w ∈ C.aGraph.verts) :
    w = M.xSep.left := by
  rcases M.xTerminalBridge_support hwP with rfl | rfl | hw
  · rfl
  · exact (Set.disjoint_left.mp C.vertex_disjoint hwA
      (C.b_contains _ M.xB_mem_bSet)).elim
  · exact (Set.disjoint_left.mp C.avoids_terminal_parts
      (Or.inl hwA) (Or.inl (Or.inl hw))).elim

theorem ABConnectorPair.xTerminalBridge_meets_bGraph_only_right
    (C : M.ABConnectorPair) {w : V}
    (hwP : w ∈ M.xTerminalBridge.support) (hwB : w ∈ C.bGraph.verts) :
    w = M.xSep.right := by
  rcases M.xTerminalBridge_support hwP with rfl | rfl | hw
  · exact (Set.disjoint_left.mp C.vertex_disjoint
      (C.a_contains _ M.xA_mem_aSet) hwB).elim
  · rfl
  · exact (Set.disjoint_left.mp C.avoids_terminal_parts
      (Or.inr hwB) (Or.inl (Or.inl hw))).elim

theorem ABConnectorPair.yTerminalBridge_meets_aGraph_only_left
    (C : M.ABConnectorPair) {w : V}
    (hwP : w ∈ M.yTerminalBridge.support) (hwA : w ∈ C.aGraph.verts) :
    w = M.ySep.left := by
  rcases M.yTerminalBridge_support hwP with rfl | rfl | hw
  · rfl
  · exact (Set.disjoint_left.mp C.vertex_disjoint hwA
      (C.b_contains _ M.yB_mem_bSet)).elim
  · exact (Set.disjoint_left.mp C.avoids_terminal_parts
      (Or.inl hwA) (Or.inl (Or.inr hw))).elim

theorem ABConnectorPair.yTerminalBridge_meets_bGraph_only_right
    (C : M.ABConnectorPair) {w : V}
    (hwP : w ∈ M.yTerminalBridge.support) (hwB : w ∈ C.bGraph.verts) :
    w = M.ySep.right := by
  rcases M.yTerminalBridge_support hwP with rfl | rfl | hw
  · exact (Set.disjoint_left.mp C.vertex_disjoint
      (C.a_contains _ M.yA_mem_aSet) hwB).elim
  · rfl
  · exact (Set.disjoint_left.mp C.avoids_terminal_parts
      (Or.inr hwB) (Or.inl (Or.inr hw))).elim

theorem ABConnectorPair.zTerminalBridge_meets_aGraph_only_left
    (C : M.ABConnectorPair) {w : V}
    (hwP : w ∈ M.zTerminalBridge.support) (hwA : w ∈ C.aGraph.verts) :
    w = M.zSep.left := by
  rcases M.zTerminalBridge_support hwP with rfl | rfl | hw
  · rfl
  · exact (Set.disjoint_left.mp C.vertex_disjoint hwA
      (C.b_contains _ M.zB_mem_bSet)).elim
  · exact (Set.disjoint_left.mp C.avoids_terminal_parts
      (Or.inl hwA) (Or.inr hw)).elim

theorem ABConnectorPair.zTerminalBridge_meets_bGraph_only_right
    (C : M.ABConnectorPair) {w : V}
    (hwP : w ∈ M.zTerminalBridge.support) (hwB : w ∈ C.bGraph.verts) :
    w = M.zSep.right := by
  rcases M.zTerminalBridge_support hwP with rfl | rfl | hw
  · exact (Set.disjoint_left.mp C.vertex_disjoint
      (C.a_contains _ M.zA_mem_aSet) hwB).elim
  · rfl
  · exact (Set.disjoint_left.mp C.avoids_terminal_parts
      (Or.inr hwB) (Or.inr hw)).elim

/-- If every `A`-attachment lies in one component end piece of `C.aGraph`,
that piece can replace the whole `A`-connector while preserving all
admissibility conditions.  This is the pruning move in the first sentence
of the cut-vertex argument on p.15. -/
noncomputable def ABConnectorPair.pruneA (C : M.ABConnectorPair)
    (d : C.aGraph.verts)
    (K : (deleteVertex C.aGraph.coe d).ConnectedComponent)
    (hcontains : ∀ a ∈ M.aSet,
      a ∈ (cutComponentPiece C.aGraph d K).verts) :
    M.ABConnectorPair := by
  let A' := cutComponentPiece C.aGraph d K
  have hA'le : A' ≤ C.aGraph := cutComponentPiece_le C.aGraph d K
  refine {
    aGraph := A'
    bGraph := C.bGraph
    a_connected := cutComponentPiece_connected C.aGraph C.a_connected d K
    b_connected := C.b_connected
    a_contains := hcontains
    b_contains := C.b_contains
    vertex_disjoint := ?_
    avoids_terminal_parts := ?_ }
  · rw [Set.disjoint_left]
    intro w hwA' hwB
    exact Set.disjoint_left.mp C.vertex_disjoint (hA'le.1 hwA') hwB
  · rw [Set.disjoint_left]
    intro w hw hparts
    apply Set.disjoint_left.mp C.avoids_terminal_parts
    · rcases hw with hwA' | hwB
      · exact Or.inl (hA'le.1 hwA')
      · exact Or.inr hwB
    · exact hparts

/-- The symmetric pruning move for the `B`-connector. -/
noncomputable def ABConnectorPair.pruneB (C : M.ABConnectorPair)
    (d : C.bGraph.verts)
    (K : (deleteVertex C.bGraph.coe d).ConnectedComponent)
    (hcontains : ∀ b ∈ M.bSet,
      b ∈ (cutComponentPiece C.bGraph d K).verts) :
    M.ABConnectorPair := by
  let B' := cutComponentPiece C.bGraph d K
  have hB'le : B' ≤ C.bGraph := cutComponentPiece_le C.bGraph d K
  refine {
    aGraph := C.aGraph
    bGraph := B'
    a_connected := C.a_connected
    b_connected := cutComponentPiece_connected C.bGraph C.b_connected d K
    a_contains := C.a_contains
    b_contains := hcontains
    vertex_disjoint := ?_
    avoids_terminal_parts := ?_ }
  · rw [Set.disjoint_left]
    intro w hwA hwB'
    exact Set.disjoint_left.mp C.vertex_disjoint hwA (hB'le.1 hwB')
  · rw [Set.disjoint_left]
    intro w hw hparts
    apply Set.disjoint_left.mp C.avoids_terminal_parts
    · rcases hw with hwA | hwB'
      · exact Or.inl hwA
      · exact Or.inr (hB'le.1 hwB')
    · exact hparts

/-! ### General connector exchanges

The later maximality argument does not only discard an end piece.  It also
adjoins a path to one of the two connector graphs and then suppresses the
now-redundant branches.  The following two constructors isolate the part of
that exchange which is independent of the particular path.  In particular,
the minimality argument below can be reused once the graph-theoretic
component calculation shows that an exchanged connector has smaller
cut-defect. -/

/-- Replace the `A`-connector by any other admissible connected subgraph,
leaving the `B`-connector fixed. -/
noncomputable def ABConnectorPair.replaceA (C : M.ABConnectorPair)
    (A' : G.Subgraph) (hconnected : A'.Connected)
    (hcontains : ∀ a ∈ M.aSet, a ∈ A'.verts)
    (hdisjoint : Disjoint A'.verts C.bGraph.verts)
    (havoids : Disjoint (A'.verts ∪ C.bGraph.verts)
      ((M.xPart : Set V) ∪ (M.yPart : Set V) ∪ (M.zPart : Set V))) :
    M.ABConnectorPair where
  aGraph := A'
  bGraph := C.bGraph
  a_connected := hconnected
  b_connected := C.b_connected
  a_contains := hcontains
  b_contains := C.b_contains
  vertex_disjoint := hdisjoint
  avoids_terminal_parts := havoids

/-- Replace the `B`-connector by any other admissible connected subgraph,
leaving the `A`-connector fixed. -/
noncomputable def ABConnectorPair.replaceB (C : M.ABConnectorPair)
    (B' : G.Subgraph) (hconnected : B'.Connected)
    (hcontains : ∀ b ∈ M.bSet, b ∈ B'.verts)
    (hdisjoint : Disjoint C.aGraph.verts B'.verts)
    (havoids : Disjoint (C.aGraph.verts ∪ B'.verts)
      ((M.xPart : Set V) ∪ (M.yPart : Set V) ∪ (M.zPart : Set V))) :
    M.ABConnectorPair where
  aGraph := C.aGraph
  bGraph := B'
  a_connected := C.a_connected
  b_connected := hconnected
  a_contains := C.a_contains
  b_contains := hcontains
  vertex_disjoint := hdisjoint
  avoids_terminal_parts := havoids

/-- The three theta-prefix stars give the initial admissible connector
pair required before minimizing the cut-defect. -/
noncomputable def initialABConnectorPair : M.ABConnectorPair := by
  refine {
    aGraph := M.initialAGraph
    bGraph := M.initialBGraph
    a_connected := M.initialAGraph_connected
    b_connected := M.initialBGraph_connected
    a_contains := M.aSet_subset_initialAGraph
    b_contains := M.bSet_subset_initialBGraph
    vertex_disjoint := M.initialGraphs_vertex_disjoint
    avoids_terminal_parts := ?_ }
  rw [Set.disjoint_left]
  intro w hwGraphs hwParts
  rcases hwGraphs with hwA | hwB
  · rcases hwParts with (hwX | hwY) | hwZ
    · exact Set.disjoint_left.mp M.initialAGraph_disjoint_xPart hwA hwX
    · exact Set.disjoint_left.mp M.initialAGraph_disjoint_yPart hwA hwY
    · exact Set.disjoint_left.mp M.initialAGraph_disjoint_zPart hwA hwZ
  · rcases hwParts with (hwX | hwY) | hwZ
    · exact Set.disjoint_left.mp M.initialBGraph_disjoint_xPart hwB hwX
    · exact Set.disjoint_left.mp M.initialBGraph_disjoint_yPart hwB hwY
    · exact Set.disjoint_left.mp M.initialBGraph_disjoint_zPart hwB hwZ

/-- The AHT cut-defect parameter
`c(H) = ∑_v (comp(H-v)-1)` for a finite subgraph. -/
noncomputable def connectorCutDefect (H : G.Subgraph) : ℕ :=
  ∑ d : H.verts,
    (Fintype.card
      ((H.coe.induce fun w : H.verts ↦ w ≠ d).ConnectedComponent) - 1)

/-- A finite connected graph has exactly one connected component. -/
theorem card_connectedComponent_eq_one {W : Type} [Fintype W]
    [DecidableEq W] (J : SimpleGraph W) [DecidableRel J.Adj]
    (hJ : J.Connected) : Fintype.card J.ConnectedComponent = 1 := by
  let : Nonempty W := hJ.nonempty
  let : Subsingleton J.ConnectedComponent :=
    hJ.preconnected.subsingleton_connectedComponent
  exact Fintype.card_eq_one_of_forall_eq
    (i := J.connectedComponentMk (Classical.choice (inferInstance : Nonempty W)))
    (fun _ ↦ Subsingleton.elim _ _)

/-- The cut-vertex summand of a component end piece is zero: deleting the
restored cut vertex leaves exactly its one chosen component. -/
theorem cutComponentPiece_cut_summand_eq_zero
    (H : G.Subgraph) (d : H.verts)
    (K : (deleteVertex H.coe d).ConnectedComponent) :
    Fintype.card
        (((cutComponentPiece H d K).coe.induce
          (fun w : (cutComponentPiece H d K).verts ↦
            w ≠ ⟨d.1, cut_mem_cutComponentPiece H d K⟩)).ConnectedComponent) - 1 =
      0 := by
  rw [card_connectedComponent_eq_one _
    (cutComponentPiece_delete_cut_connected H d K)]

/-- Deleting a genuine cut vertex produces at least two connected
components.  This is the strictly positive summand in the end-piece
cut-defect comparison. -/
theorem two_le_card_delete_components_of_isCutVertex
    (H : G.Subgraph) {d : H.verts} (hd : IsCutVertex H.coe d) :
    2 ≤ Fintype.card
      ((H.coe.induce fun w : H.verts ↦ w ≠ d).ConnectedComponent) := by
  classical
  obtain ⟨u, v, huv⟩ :=
    (isCutVertex_iff_exists_not_reachable H.coe d).mp hd
  have hne :
      (H.coe.induce fun w : H.verts ↦ w ≠ d).connectedComponentMk u ≠
        (H.coe.induce fun w : H.verts ↦ w ≠ d).connectedComponentMk v := by
    intro h
    exact huv (ConnectedComponent.exact h)
  rw [show (2 : ℕ) = 1 + 1 by omega]
  exact Fintype.one_lt_card_iff.mpr ⟨_, _, hne⟩

/-- The same lower bound stated with the named vertex-deletion graph.  Keeping
this form avoids expensive reduction between the named definition and an
explicit induced graph in later component-pruning arguments. -/
theorem two_le_card_deleteVertex_components_of_isCutVertex
    (H : G.Subgraph) {d : H.verts} (hd : IsCutVertex H.coe d) :
    2 ≤ Fintype.card (deleteVertex H.coe d).ConnectedComponent := by
  classical
  obtain ⟨u, v, huv⟩ :=
    (isCutVertex_iff_exists_not_reachable H.coe d).mp hd
  have hne :
      (deleteVertex H.coe d).connectedComponentMk u ≠
        (deleteVertex H.coe d).connectedComponentMk v := by
    intro h
    exact huv (ConnectedComponent.exact h)
  rw [show (2 : ℕ) = 1 + 1 by omega]
  exact Fintype.one_lt_card_iff.mpr ⟨_, _, hne⟩

/-- Consequently the summand indexed by a cut vertex is positive. -/
theorem one_le_cutDefect_summand_of_isCutVertex
    (H : G.Subgraph) {d : H.verts} (hd : IsCutVertex H.coe d) :
    1 ≤ Fintype.card
        ((H.coe.induce fun w : H.verts ↦ w ≠ d).ConnectedComponent) - 1 := by
  have htwo := two_le_card_delete_components_of_isCutVertex H hd
  omega

/-- At a cut vertex, the end piece has a strictly smaller summand than the
ambient connector. -/
theorem cutComponentPiece_cut_summand_lt
    (H : G.Subgraph) (d : H.verts)
    (K : (deleteVertex H.coe d).ConnectedComponent)
    (hd : IsCutVertex H.coe d) :
    Fintype.card
        (((cutComponentPiece H d K).coe.induce
          (fun w : (cutComponentPiece H d K).verts ↦
            w ≠ ⟨d.1, cut_mem_cutComponentPiece H d K⟩)).ConnectedComponent) - 1 <
      Fintype.card
          ((H.coe.induce fun w : H.verts ↦ w ≠ d).ConnectedComponent) - 1 := by
  rw [cutComponentPiece_cut_summand_eq_zero H d K]
  exact one_le_cutDefect_summand_of_isCutVertex H hd

/-- A graph with a cut vertex has nonzero total cut-defect. -/
theorem connectorCutDefect_pos_of_isCutVertex
    (H : G.Subgraph) {d : H.verts} (hd : IsCutVertex H.coe d) :
    0 < connectorCutDefect H := by
  classical
  have hterm := one_le_cutDefect_summand_of_isCutVertex H hd
  rw [connectorCutDefect]
  have hdpos : 0 < Fintype.card
      ((H.coe.induce fun w : H.verts ↦ w ≠ d).ConnectedComponent) - 1 := by
    omega
  let defect : H.verts → ℕ := fun q ↦
    Fintype.card
      ((H.coe.induce fun w : H.verts ↦ w ≠ q).ConnectedComponent) - 1
  have hdle : defect d ≤ ∑ q : H.verts, defect q :=
    Finset.single_le_sum (s := Finset.univ) (f := defect)
      (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ d)
  exact lt_of_lt_of_le (by simpa only [defect] using hdpos)
    (by simpa only [defect] using hdle)

/-- The finite-sum comparison underlying every strict cut-defect exchange.
It remains only to provide the graph-theoretic injection of old component
classes into the new ones.  The embedding also allows the replacement
connector to have a different vertex set. -/
theorem connectorCutDefect_lt_of_embedding
    (P H : G.Subgraph) (f : P.verts ↪ H.verts)
    (hle : ∀ p : P.verts,
      Fintype.card
          ((P.coe.induce fun w : P.verts ↦ w ≠ p).ConnectedComponent) - 1 ≤
        Fintype.card
          ((H.coe.induce fun w : H.verts ↦ w ≠ f p).ConnectedComponent) - 1)
    (p₀ : P.verts)
    (hlt :
      Fintype.card
          ((P.coe.induce fun w : P.verts ↦ w ≠ p₀).ConnectedComponent) - 1 <
        Fintype.card
          ((H.coe.induce fun w : H.verts ↦ w ≠ f p₀).ConnectedComponent) - 1) :
    connectorCutDefect P < connectorCutDefect H := by
  classical
  let defectP : P.verts → ℕ := fun p ↦
    Fintype.card
        ((P.coe.induce fun w : P.verts ↦ w ≠ p).ConnectedComponent) - 1
  let defectH : H.verts → ℕ := fun q ↦
    Fintype.card
        ((H.coe.induce fun w : H.verts ↦ w ≠ q).ConnectedComponent) - 1
  have hsumlt :
      ∑ p : P.verts, defectP p < ∑ p : P.verts, defectH (f p) := by
    apply Finset.sum_lt_sum
    · intro p _
      exact hle p
    · exact ⟨p₀, Finset.mem_univ p₀, hlt⟩
  have hsubsum :
      (Finset.univ.map f).sum defectH ≤
        ∑ q : H.verts, defectH q :=
    Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  rw [Finset.sum_map] at hsubsum
  simpa only [connectorCutDefect, defectP, defectH] using
    lt_of_lt_of_le hsumlt hsubsum

/-- Dual finite-sum comparison for an enlargement.  Here the old connector
embeds into the replacement, every new vertex has zero cut summand, and the
old summands do not increase, with one strict decrease.  This is the exact
arithmetic form of AHT's external-path exchange on p.15. -/
theorem connectorCutDefect_lt_of_enlargement
    (P H : G.Subgraph) (f : H.verts ↪ P.verts)
    (hle : ∀ h : H.verts,
      Fintype.card
          ((P.coe.induce fun w : P.verts ↦ w ≠ f h).ConnectedComponent) - 1 ≤
        Fintype.card
          ((H.coe.induce fun w : H.verts ↦ w ≠ h).ConnectedComponent) - 1)
    (hnew : ∀ p : P.verts, p ∉ Set.range f →
      Fintype.card
          ((P.coe.induce fun w : P.verts ↦ w ≠ p).ConnectedComponent) - 1 = 0)
    (h₀ : H.verts)
    (hlt :
      Fintype.card
          ((P.coe.induce fun w : P.verts ↦ w ≠ f h₀).ConnectedComponent) - 1 <
        Fintype.card
          ((H.coe.induce fun w : H.verts ↦ w ≠ h₀).ConnectedComponent) - 1) :
    connectorCutDefect P < connectorCutDefect H := by
  classical
  let defectP : P.verts → ℕ := fun p ↦
    Fintype.card
        ((P.coe.induce fun w : P.verts ↦ w ≠ p).ConnectedComponent) - 1
  let defectH : H.verts → ℕ := fun h ↦
    Fintype.card
        ((H.coe.induce fun w : H.verts ↦ w ≠ h).ConnectedComponent) - 1
  have hsupport :
      ∑ p : P.verts, defectP p = ∑ h : H.verts, defectP (f h) := by
    have hsubset : (Finset.univ.map f : Finset P.verts) ⊆ Finset.univ :=
      Finset.subset_univ _
    have hsum :
        (Finset.univ.map f : Finset P.verts).sum defectP =
          ∑ p : P.verts, defectP p := by
      apply Finset.sum_subset hsubset
      intro p _ hp
      apply hnew p
      intro hrange
      obtain ⟨h, rfl⟩ := hrange
      exact hp (Finset.mem_map.mpr ⟨h, Finset.mem_univ h, rfl⟩)
    rw [← hsum, Finset.sum_map]
  have hstrict :
      ∑ h : H.verts, defectP (f h) < ∑ h : H.verts, defectH h := by
    apply Finset.sum_lt_sum
    · intro h _
      exact hle h
    · exact ⟨h₀, Finset.mem_univ h₀, hlt⟩
  change (∑ p : P.verts, defectP p) < ∑ h : H.verts, defectH h
  rw [hsupport]
  exact hstrict

/-! The abstract finite-sum comparison above is useful only once the
component map for a component end piece is known to be injective.  The
following small ``weak homomorphism'' lemma is the convenient way to prove
that fact.  Collapsing all vertices outside an end piece to its restored cut
vertex need not be a graph homomorphism (an outside edge becomes a loop), but
it sends each edge either to an edge or to equality, which is all that
reachability needs. -/

/-- A map which sends every edge either to an edge or to equality preserves
reachability. -/
theorem SimpleGraph.Reachable.map_of_adj_eq_or_adj
    {W U : Type*} {J : SimpleGraph W} {K : SimpleGraph U}
    (f : W → U)
    (hmap : ∀ ⦃u v⦄, J.Adj u v → f u = f v ∨ K.Adj (f u) (f v))
    {u v : W} (huv : J.Reachable u v) : K.Reachable (f u) (f v) := by
  rcases huv with ⟨p⟩
  induction p with
  | nil => exact ⟨.nil⟩
  | @cons a b c hab p ih =>
      rcases hmap hab with heq | hadj
      · simpa only [heq] using ih
      · rcases ih with ⟨q⟩
        exact ⟨q.cons hadj⟩

/-- If every vertex of the target graph can be reached from the image of a
graph homomorphism, the induced map on connected components is onto.  This
is the component-counting direction used for an ear extension: every
component of the enlarged graph still contains an old vertex. -/
theorem ConnectedComponent.map_surjective_of_forall_reachable
    {W U : Type*} {J : SimpleGraph W} {K : SimpleGraph U}
    (f : J →g K) (hreach : ∀ v : U, ∃ u : W, K.Reachable (f u) v) :
    Function.Surjective (fun C : J.ConnectedComponent ↦ C.map f) := by
  intro C
  refine ConnectedComponent.ind (c := C) ?_
  intro v
  obtain ⟨u, huv⟩ := hreach v
  refine ⟨J.connectedComponentMk u, ?_⟩
  change K.connectedComponentMk (f u) = K.connectedComponentMk v
  exact ConnectedComponent.sound huv

/-- The old vertices embedded in the union of a connector and an ear. -/
def connectorEarOldVertsEmbedding (H : G.Subgraph) {s t : V}
    (p : G.Walk s t) : H.verts ↪ (H ⊔ p.toSubgraph).verts where
  toFun w := ⟨w.1, by
    simp only [Subgraph.verts_sup, Set.mem_union]
    exact Or.inl w.2⟩
  inj' u v h := by
    apply Subtype.ext
    exact congrArg (fun w : (H ⊔ p.toSubgraph).verts ↦ w.1) h

/-- The ear walk regarded as a walk in the edge-restricted union subgraph.
Using `mapToSubgraph` here is essential: merely inducing the ambient walk
on the union's vertex set would also retain ambient chord edges. -/
noncomputable def connectorEarWalkInExtension (H : G.Subgraph)
    {s t : V} (p : G.Walk s t) :
    (H ⊔ p.toSubgraph).coe.Walk
      ⟨s, by
        simp only [Subgraph.verts_sup, Set.mem_union,
          Walk.mem_verts_toSubgraph]
        exact Or.inr p.start_mem_support⟩
      ⟨t, by
        simp only [Subgraph.verts_sup, Set.mem_union,
          Walk.mem_verts_toSubgraph]
        exact Or.inr p.end_mem_support⟩ :=
  (p.mapToSubgraph.map
    (Subgraph.inclusion
      (show p.toSubgraph ≤ H ⊔ p.toSubgraph from le_sup_right))).copy
        (Subtype.ext rfl) (Subtype.ext rfl)

theorem connectorEarWalkInExtension_map (H : G.Subgraph)
    {s t : V} (p : G.Walk s t) :
    (connectorEarWalkInExtension H p).map (H ⊔ p.toSubgraph).hom = p := by
  simp only [connectorEarWalkInExtension, Walk.map_copy, Walk.map_map]
  exact p.map_mapToSubgraph_hom

theorem mem_connectorEarWalkInExtension_support_iff
    (H : G.Subgraph) {s t : V} (p : G.Walk s t)
    (w : (H ⊔ p.toSubgraph).verts) :
    w ∈ (connectorEarWalkInExtension H p).support ↔ w.1 ∈ p.support := by
  constructor
  · intro hw
    have hw' : w.1 ∈ ((connectorEarWalkInExtension H p).map
        (H ⊔ p.toSubgraph).hom).support := by
      rw [Walk.support_map]
      exact List.mem_map.mpr ⟨w, hw, rfl⟩
    rw [connectorEarWalkInExtension_map H p] at hw'
    exact hw'
  · intro hw
    have hw' : w.1 ∈ ((connectorEarWalkInExtension H p).map
        (H ⊔ p.toSubgraph).hom).support := by
      rw [connectorEarWalkInExtension_map H p]
      exact hw
    rw [Walk.support_map] at hw'
    obtain ⟨w', hw', heq⟩ := List.mem_map.mp hw'
    have hww : w' = w := Subtype.ext heq
    simpa only [hww] using hw'

/-- Inclusion of the old connector after deleting corresponding old
vertices from the connector and from its ear extension. -/
def connectorEarOldDeleteInclusion (H : G.Subgraph) {s t : V}
    (p : G.Walk s t) (d : H.verts) :
    (H.coe.induce fun w : H.verts ↦ w ≠ d) →g
      ((H ⊔ p.toSubgraph).coe.induce
        fun w : (H ⊔ p.toSubgraph).verts ↦
          w ≠ connectorEarOldVertsEmbedding H p d) where
  toFun w := ⟨connectorEarOldVertsEmbedding H p w.1, by
    intro h
    apply w.2
    apply Subtype.ext
    exact congrArg (fun q : (H ⊔ p.toSubgraph).verts ↦ q.1) h⟩
  map_rel' h := by
    change (H ⊔ p.toSubgraph).Adj _ _
    exact Or.inl h

/-- Component-count inequality for an old deletion in an ear extension.
The graph-theoretic hypothesis says precisely that every enlarged component
contains an old vertex. -/
theorem connectorEarOldDelete_component_card_le
    (H : G.Subgraph) {s t : V} (p : G.Walk s t) (d : H.verts)
    (hreach : ∀ v : {w : (H ⊔ p.toSubgraph).verts //
        w ≠ connectorEarOldVertsEmbedding H p d},
      ∃ u : {w : H.verts // w ≠ d},
        ((H ⊔ p.toSubgraph).coe.induce
          fun w : (H ⊔ p.toSubgraph).verts ↦
            w ≠ connectorEarOldVertsEmbedding H p d).Reachable
          (connectorEarOldDeleteInclusion H p d u) v) :
    Fintype.card
        (((H ⊔ p.toSubgraph).coe.induce
          fun w : (H ⊔ p.toSubgraph).verts ↦
            w ≠ connectorEarOldVertsEmbedding H p d).ConnectedComponent) ≤
      Fintype.card
        ((H.coe.induce fun w : H.verts ↦ w ≠ d).ConnectedComponent) := by
  apply Fintype.card_le_of_surjective
    (fun C : (H.coe.induce fun w : H.verts ↦ w ≠ d).ConnectedComponent ↦
      C.map (connectorEarOldDeleteInclusion H p d))
  exact ConnectedComponent.map_surjective_of_forall_reachable
    (connectorEarOldDeleteInclusion H p d) hreach

/-- Strict component-count inequality at an old vertex whose deletion
separates the two ends of the new ear.  Surjectivity gives the weak
inequality; the two old components containing the ends are identified by
the ear, so the component map is not injective. -/
theorem connectorEarOldDelete_component_card_lt
    (H : G.Subgraph) {s t : V} (p : G.Walk s t) (d : H.verts)
    (hs : s ∈ H.verts) (ht : t ∈ H.verts)
    (hsd : (⟨s, hs⟩ : H.verts) ≠ d)
    (htd : (⟨t, ht⟩ : H.verts) ≠ d)
    (hreach : ∀ v : {w : (H ⊔ p.toSubgraph).verts //
        w ≠ connectorEarOldVertsEmbedding H p d},
      ∃ u : {w : H.verts // w ≠ d},
        ((H ⊔ p.toSubgraph).coe.induce
          fun w : (H ⊔ p.toSubgraph).verts ↦
            w ≠ connectorEarOldVertsEmbedding H p d).Reachable
          (connectorEarOldDeleteInclusion H p d u) v)
    (hstOld : ¬(H.coe.induce fun w : H.verts ↦ w ≠ d).Reachable
      ⟨⟨s, hs⟩, hsd⟩ ⟨⟨t, ht⟩, htd⟩)
    (hear : ((H ⊔ p.toSubgraph).coe.induce
      fun w : (H ⊔ p.toSubgraph).verts ↦
        w ≠ connectorEarOldVertsEmbedding H p d).Reachable
      (connectorEarOldDeleteInclusion H p d ⟨⟨s, hs⟩, hsd⟩)
      (connectorEarOldDeleteInclusion H p d ⟨⟨t, ht⟩, htd⟩)) :
    Fintype.card
        (((H ⊔ p.toSubgraph).coe.induce
          fun w : (H ⊔ p.toSubgraph).verts ↦
            w ≠ connectorEarOldVertsEmbedding H p d).ConnectedComponent) <
      Fintype.card
        ((H.coe.induce fun w : H.verts ↦ w ≠ d).ConnectedComponent) := by
  let f := fun C :
      (H.coe.induce fun w : H.verts ↦ w ≠ d).ConnectedComponent ↦
    C.map (connectorEarOldDeleteInclusion H p d)
  have hsurj : Function.Surjective f :=
    ConnectedComponent.map_surjective_of_forall_reachable
      (connectorEarOldDeleteInclusion H p d) hreach
  have hne :
      (H.coe.induce fun w : H.verts ↦ w ≠ d).connectedComponentMk
          ⟨⟨s, hs⟩, hsd⟩ ≠
        (H.coe.induce fun w : H.verts ↦ w ≠ d).connectedComponentMk
          ⟨⟨t, ht⟩, htd⟩ := by
    intro heq
    exact hstOld (ConnectedComponent.exact heq)
  have heq : f ((H.coe.induce fun w : H.verts ↦ w ≠ d).connectedComponentMk
        ⟨⟨s, hs⟩, hsd⟩) =
      f ((H.coe.induce fun w : H.verts ↦ w ≠ d).connectedComponentMk
        ⟨⟨t, ht⟩, htd⟩) := by
    simp only [f, ConnectedComponent.map_mk]
    exact ConnectedComponent.sound hear
  have hninj : ¬Function.Injective f := by
    intro hinj
    exact hne (hinj heq)
  exact Fintype.card_lt_of_surjective_not_injective f hsurj hninj

/-- The ear itself joins its old endpoints after any old vertex other than
those endpoints is deleted.  Internal ear vertices are new, so the induced
ear walk survives the deletion. -/
theorem connectorEar_ends_reachable_after_delete_old
    (H : G.Subgraph) {s t : V} (p : G.Walk s t) (hp : p.IsPath)
    (hs : s ∈ H.verts) (ht : t ∈ H.verts)
    (hint : ∀ w, w ∈ p.support → w ≠ s → w ≠ t → w ∉ H.verts)
    (d : H.verts) (hsd : (⟨s, hs⟩ : H.verts) ≠ d)
    (htd : (⟨t, ht⟩ : H.verts) ≠ d) :
    ((H ⊔ p.toSubgraph).coe.induce
      fun w : (H ⊔ p.toSubgraph).verts ↦
        w ≠ connectorEarOldVertsEmbedding H p d).Reachable
      (connectorEarOldDeleteInclusion H p d ⟨⟨s, hs⟩, hsd⟩)
      (connectorEarOldDeleteInclusion H p d ⟨⟨t, ht⟩, htd⟩) := by
  have hpd : ∀ (w : (H ⊔ p.toSubgraph).verts),
      w.1 ∈ p.support →
        w ≠ connectorEarOldVertsEmbedding H p d := by
    intro w hw heq
    have hwd : w.1 = d.1 := congrArg Subtype.val heq
    have hwH : w.1 ∈ H.verts := hwd.symm ▸ d.2
    by_cases hws : w.1 = s
    · apply hsd
      apply Subtype.ext
      exact hws.symm.trans hwd
    by_cases hwt : w.1 = t
    · apply htd
      apply Subtype.ext
      exact hwt.symm.trans hwd
    exact (hint w.1 hw hws hwt) hwH
  let sExt : (H ⊔ p.toSubgraph).verts :=
    connectorEarOldVertsEmbedding H p ⟨s, hs⟩
  let tExt : (H ⊔ p.toSubgraph).verts :=
    connectorEarOldVertsEmbedding H p ⟨t, ht⟩
  let pSup : (H ⊔ p.toSubgraph).coe.Walk sExt tExt :=
    (connectorEarWalkInExtension H p).copy
      (Subtype.ext rfl) (Subtype.ext rfl)
  let pDel := pSup.induce
    (fun w : (H ⊔ p.toSubgraph).verts ↦
      w ≠ connectorEarOldVertsEmbedding H p d)
    (fun w hw ↦ by
      apply hpd w
      apply (mem_connectorEarWalkInExtension_support_iff H p w).mp
      simpa only [pSup, Walk.support_copy] using hw)
  have hreach := pDel.reachable
  change _
  convert hreach using 1 <;>
    apply Subtype.ext <;> apply Subtype.ext <;> rfl

/-- Every component of an ear extension after deleting an old vertex still
contains an old vertex.  A new vertex reaches one of the two ear ends along
the side of the simple ear which avoids the deleted old vertex. -/
theorem connectorEarOldDelete_every_component_meets_old
    (H : G.Subgraph) (hH : H.Connected) {s t : V}
    (p : G.Walk s t) (hp : p.IsPath)
    (hs : s ∈ H.verts) (ht : t ∈ H.verts) (hst : s ≠ t)
    (hint : ∀ w, w ∈ p.support → w ≠ s → w ≠ t → w ∉ H.verts)
    (d : H.verts) :
    ∀ v : {w : (H ⊔ p.toSubgraph).verts //
        w ≠ connectorEarOldVertsEmbedding H p d},
      ∃ u : {w : H.verts // w ≠ d},
        ((H ⊔ p.toSubgraph).coe.induce
          fun w : (H ⊔ p.toSubgraph).verts ↦
            w ≠ connectorEarOldVertsEmbedding H p d).Reachable
          (connectorEarOldDeleteInclusion H p d u) v := by
  classical
  let sExt : (H ⊔ p.toSubgraph).verts :=
    connectorEarOldVertsEmbedding H p ⟨s, hs⟩
  let tExt : (H ⊔ p.toSubgraph).verts :=
    connectorEarOldVertsEmbedding H p ⟨t, ht⟩
  let pExt : (H ⊔ p.toSubgraph).coe.Walk sExt tExt :=
    (connectorEarWalkInExtension H p).copy
      (Subtype.ext rfl) (Subtype.ext rfl)
  have hpExt : pExt.IsPath := by
    have hbase : (connectorEarWalkInExtension H p).IsPath := by
      apply Walk.IsPath.of_map (f := (H ⊔ p.toSubgraph).hom)
      rw [connectorEarWalkInExtension_map H p]
      exact hp
    exact (Walk.isPath_copy (connectorEarWalkInExtension H p)
      (Subtype.ext rfl) (Subtype.ext rfl)).2 hbase
  intro v
  by_cases hvH : v.1.1 ∈ H.verts
  · let u : {w : H.verts // w ≠ d} :=
      ⟨⟨v.1.1, hvH⟩, by
        intro heq
        apply v.2
        apply Subtype.ext
        exact congrArg (fun q : H.verts ↦ q.1) heq⟩
    refine ⟨u, ?_⟩
    have heq : connectorEarOldDeleteInclusion H p d u = v := by
      apply Subtype.ext
      apply Subtype.ext
      rfl
    simpa only [heq] using
      (Reachable.refl v)
  have hvp : v.1.1 ∈ p.support := by
    have hv := v.1.2
    simp only [Subgraph.verts_sup, Set.mem_union,
      Walk.mem_verts_toSubgraph] at hv
    exact hv.resolve_left hvH
  have hvpExt : v.1 ∈ pExt.support := by
    apply (mem_connectorEarWalkInExtension_support_iff H p v.1).2
    simpa only [pExt, Walk.support_copy] using hvp
  have path_vertex_old_only_at_ends {w : V} (hw : w ∈ p.support)
      (hwH : w ∈ H.verts) : w = s ∨ w = t := by
    by_contra h
    push_neg at h
    exact (hint w hw h.1 h.2) hwH
  by_cases hsd : (⟨s, hs⟩ : H.verts) = d
  · have htd : (⟨t, ht⟩ : H.verts) ≠ d := by
      intro h
      apply hst
      exact congrArg Subtype.val (hsd.trans h.symm)
    let u : {w : H.verts // w ≠ d} := ⟨⟨t, ht⟩, htd⟩
    let r := pExt.dropUntil v.1 hvpExt
    have hrd : ∀ (w : (H ⊔ p.toSubgraph).verts)
        (hw : w ∈ r.support),
        w ≠ connectorEarOldVertsEmbedding H p d := by
      intro w hw heq
      have hwd : w.1 = d.1 := congrArg Subtype.val heq
      have hwH : w.1 ∈ H.verts := hwd.symm ▸ d.2
      have hwExt : w ∈ pExt.support :=
        pExt.support_dropUntil_subset_support hvpExt hw
      have hwP : w.1 ∈ p.support := by
        apply (mem_connectorEarWalkInExtension_support_iff H p w).1
        simpa only [pExt, Walk.support_copy] using hwExt
      rcases path_vertex_old_only_at_ends
          hwP hwH with hws | hwt
      · have hwsExt : w = sExt := Subtype.ext hws
        have hwr : w ∈ (pExt.dropUntil v.1 hvpExt).reverse.support := by
          simpa only [Walk.support_reverse, List.mem_reverse] using hw
        have hsv : sExt = v.1 :=
          Walk.IsPath.takeUntil_inter_reverse_dropUntil_only
            hpExt hvpExt sExt
            (pExt.takeUntil v.1 hvpExt).start_mem_support (hwsExt ▸ hwr)
        apply v.2
        exact hsv.symm.trans (by
          exact congrArg (connectorEarOldVertsEmbedding H p) hsd)
      · apply htd
        apply Subtype.ext
        exact hwt.symm.trans hwd
    let rDel := r.induce
      (fun w : (H ⊔ p.toSubgraph).verts ↦
        w ≠ connectorEarOldVertsEmbedding H p d)
      hrd
    refine ⟨u, ?_⟩
    have hreach := rDel.reachable.symm
    convert hreach using 1 <;>
      apply Subtype.ext <;> apply Subtype.ext <;> rfl

  · let u : {w : H.verts // w ≠ d} := ⟨⟨s, hs⟩, hsd⟩
    let r := (pExt.takeUntil v.1 hvpExt).reverse
    have hrd : ∀ (w : (H ⊔ p.toSubgraph).verts)
        (hw : w ∈ r.support),
        w ≠ connectorEarOldVertsEmbedding H p d := by
      intro w hw heq
      have hwd : w.1 = d.1 := congrArg Subtype.val heq
      have hwH : w.1 ∈ H.verts := hwd.symm ▸ d.2
      have hwTake : w ∈ (pExt.takeUntil v.1 hvpExt).support := by
        simpa only [r, Walk.support_reverse, List.mem_reverse] using hw
      have hwExt : w ∈ pExt.support :=
        pExt.support_takeUntil_subset_support hvpExt hwTake
      have hwP : w.1 ∈ p.support := by
        apply (mem_connectorEarWalkInExtension_support_iff H p w).1
        simpa only [pExt, Walk.support_copy] using hwExt
      rcases path_vertex_old_only_at_ends
          hwP hwH with hws | hwt
      · apply hsd
        apply Subtype.ext
        exact hws.symm.trans hwd
      · have hwtExt : w = tExt := Subtype.ext hwt
        have htv : tExt = v.1 :=
          Walk.IsPath.takeUntil_inter_reverse_dropUntil_only
            hpExt hvpExt tExt (hwtExt ▸ hwTake)
            (pExt.dropUntil v.1 hvpExt).reverse.start_mem_support
        apply v.2
        exact htv.symm.trans (by
          exact congrArg (connectorEarOldVertsEmbedding H p)
            (show (⟨t, ht⟩ : H.verts) = d from
              Subtype.ext (hwt.symm.trans hwd)))
    let rDel := r.induce
      (fun w : (H ⊔ p.toSubgraph).verts ↦
        w ≠ connectorEarOldVertsEmbedding H p d)
      hrd
    refine ⟨u, ?_⟩
    have hreach := rDel.reachable.symm
    convert hreach using 1 <;>
      apply Subtype.ext <;> apply Subtype.ext <;> rfl

/-- Deleting a genuinely new internal vertex of an ear leaves the extension
connected.  The two pieces of the broken ear remain attached to its two old
ends, and the old connector joins those ends. -/
theorem connectorEarDeleteNew_connected
    (H : G.Subgraph) (hH : H.Connected) {s t : V}
    (p : G.Walk s t) (hp : p.IsPath)
    (hs : s ∈ H.verts) (ht : t ∈ H.verts)
    (q : (H ⊔ p.toSubgraph).verts)
    (hqnew : q ∉ Set.range (connectorEarOldVertsEmbedding H p)) :
    ((H ⊔ p.toSubgraph).coe.induce
      fun w : (H ⊔ p.toSubgraph).verts ↦ w ≠ q).Connected := by
  classical
  have hqH : q.1 ∉ H.verts := by
    intro h
    apply hqnew
    refine ⟨⟨q.1, h⟩, ?_⟩
    apply Subtype.ext
    rfl
  have hqp : q.1 ∈ p.support := by
    have hq := q.2
    simp only [Subgraph.verts_sup, Set.mem_union,
      Walk.mem_verts_toSubgraph] at hq
    exact hq.resolve_left hqH
  have hqs : q.1 ≠ s := by
    intro h
    apply hqH
    rw [h]
    exact hs
  have hqt : q.1 ≠ t := by
    intro h
    apply hqH
    rw [h]
    exact ht
  let sSup : (H ⊔ p.toSubgraph).verts :=
    connectorEarOldVertsEmbedding H p ⟨s, hs⟩
  let tSup : (H ⊔ p.toSubgraph).verts :=
    connectorEarOldVertsEmbedding H p ⟨t, ht⟩
  have hsQ : sSup ≠ q := by
    intro h
    exact hqs (congrArg Subtype.val h).symm
  let anchor : {w : (H ⊔ p.toSubgraph).verts // w ≠ q} :=
    ⟨sSup, hsQ⟩
  have hOldQ (w : H.verts) :
      connectorEarOldVertsEmbedding H p w ≠ q := by
    intro h
    exact hqnew ⟨w, h⟩
  let oldInc : H.coe →g ((H ⊔ p.toSubgraph).coe.induce
      fun w : (H ⊔ p.toSubgraph).verts ↦ w ≠ q) :=
    { toFun := fun w ↦
        ⟨connectorEarOldVertsEmbedding H p w, hOldQ w⟩
      map_rel' := by
        intro u v huv
        change (H ⊔ p.toSubgraph).Adj _ _
        exact Or.inl huv }
  have old_reaches_anchor
      (vH : H.verts) :
      ((H ⊔ p.toSubgraph).coe.induce
        fun w : (H ⊔ p.toSubgraph).verts ↦ w ≠ q).Reachable
        ⟨connectorEarOldVertsEmbedding H p vH, hOldQ vH⟩
        anchor := by
    obtain ⟨r⟩ := hH.preconnected vH ⟨s, hs⟩
    have hr := (r.map oldInc).reachable
    convert hr using 1 <;>
      apply Subtype.ext <;> apply Subtype.ext <;> rfl
  let pExt : (H ⊔ p.toSubgraph).coe.Walk sSup tSup :=
    (connectorEarWalkInExtension H p).copy
      (Subtype.ext rfl) (Subtype.ext rfl)
  have hpExt : pExt.IsPath := by
    have hbase : (connectorEarWalkInExtension H p).IsPath := by
      apply Walk.IsPath.of_map (f := (H ⊔ p.toSubgraph).hom)
      rw [connectorEarWalkInExtension_map H p]
      exact hp
    exact (Walk.isPath_copy (connectorEarWalkInExtension H p)
      (Subtype.ext rfl) (Subtype.ext rfl)).2 hbase
  have every_reaches_anchor : ∀ v :
      {w : (H ⊔ p.toSubgraph).verts // w ≠ q},
      ((H ⊔ p.toSubgraph).coe.induce
        fun w : (H ⊔ p.toSubgraph).verts ↦ w ≠ q).Reachable v anchor := by
    intro v
    by_cases hvH : v.1.1 ∈ H.verts
    · convert old_reaches_anchor ⟨v.1.1, hvH⟩ using 1 <;>
        apply Subtype.ext <;> apply Subtype.ext <;> rfl
    have hvp : v.1.1 ∈ p.support := by
      have hv := v.1.2
      simp only [Subgraph.verts_sup, Set.mem_union,
        Walk.mem_verts_toSubgraph] at hv
      exact hv.resolve_left hvH
    have hvpExt : v.1 ∈ pExt.support := by
      apply (mem_connectorEarWalkInExtension_support_iff H p v.1).2
      simpa only [pExt, Walk.support_copy] using hvp
    by_cases hqPrefix : q ∈ (pExt.takeUntil v.1 hvpExt).support
    · let r := pExt.dropUntil v.1 hvpExt
      have hrq : ∀ (w : (H ⊔ p.toSubgraph).verts)
          (hw : w ∈ r.support), w ≠ q := by
        intro w hw heq
        have hqSuffix : q ∈ (pExt.dropUntil v.1 hvpExt).reverse.support := by
          have hwRev : w ∈
              (pExt.dropUntil v.1 hvpExt).reverse.support := by
            simpa only [Walk.support_reverse, List.mem_reverse] using hw
          exact heq ▸ hwRev
        have hqv := Walk.IsPath.takeUntil_inter_reverse_dropUntil_only
          hpExt hvpExt q hqPrefix hqSuffix
        apply v.2
        exact hqv.symm
      let rDel := r.induce
        (fun w : (H ⊔ p.toSubgraph).verts ↦ w ≠ q) hrq
      have hvt := rDel.reachable
      have htold := old_reaches_anchor ⟨t, ht⟩
      have hvt' :
          ((H ⊔ p.toSubgraph).coe.induce
            fun w : (H ⊔ p.toSubgraph).verts ↦ w ≠ q).Reachable v
            ⟨connectorEarOldVertsEmbedding H p ⟨t, ht⟩,
              hOldQ ⟨t, ht⟩⟩ := by
        convert hvt using 1 <;>
          apply Subtype.ext <;> apply Subtype.ext <;> rfl
      exact hvt'.trans htold
    · let r := (pExt.takeUntil v.1 hvpExt).reverse
      have hrq : ∀ (w : (H ⊔ p.toSubgraph).verts)
          (hw : w ∈ r.support), w ≠ q := by
        intro w hw heq
        apply hqPrefix
        have hwTake : w ∈ (pExt.takeUntil v.1 hvpExt).support := by
          simpa only [r, Walk.support_reverse, List.mem_reverse] using hw
        rw [heq] at hwTake
        exact hwTake
      let rDel := r.induce
        (fun w : (H ⊔ p.toSubgraph).verts ↦ w ≠ q) hrq
      have hvs := rDel.reachable
      convert hvs using 1 <;>
        apply Subtype.ext <;> apply Subtype.ext <;> rfl
  refine { preconnected := ?_, nonempty := ⟨anchor⟩ }
  intro u v
  exact (every_reaches_anchor u).trans (every_reaches_anchor v).symm

/-- AHT p.15: adjoining a clean external ear strictly decreases the
cut-defect when its ends are separated by deletion of an old vertex. -/
theorem connectorCutDefect_sup_path_lt
    (H : G.Subgraph) (hH : H.Connected) {s t : V}
    (p : G.Walk s t) (hp : p.IsPath)
    (hs : s ∈ H.verts) (ht : t ∈ H.verts)
    (hint : ∀ w, w ∈ p.support → w ≠ s → w ≠ t → w ∉ H.verts)
    (d : H.verts) (hsd : (⟨s, hs⟩ : H.verts) ≠ d)
    (htd : (⟨t, ht⟩ : H.verts) ≠ d)
    (hsep : ¬(H.coe.induce fun w : H.verts ↦ w ≠ d).Reachable
      ⟨⟨s, hs⟩, hsd⟩ ⟨⟨t, ht⟩, htd⟩) :
    connectorCutDefect (H ⊔ p.toSubgraph) < connectorCutDefect H := by
  classical
  have hst : s ≠ t := by
    intro h
    subst t
    apply hsep
    have heq : (⟨⟨s, hs⟩, hsd⟩ : {w : H.verts // w ≠ d}) =
        ⟨⟨s, ht⟩, htd⟩ := by
      apply Subtype.ext
      apply Subtype.ext
      rfl
    simpa only [heq] using
      (Reachable.refl (⟨⟨s, ht⟩, htd⟩ : {w : H.verts // w ≠ d}))
  let f := connectorEarOldVertsEmbedding H p
  refine connectorCutDefect_lt_of_enlargement
    (H ⊔ p.toSubgraph) H f ?_ ?_ d ?_
  · intro q
    have hreach := connectorEarOldDelete_every_component_meets_old
      H hH p hp hs ht hst hint q
    have hcard := connectorEarOldDelete_component_card_le H p q hreach
    simpa only [f] using (Nat.sub_le_sub_right hcard 1)
  · intro q hqnew
    have hconn := connectorEarDeleteNew_connected H hH p hp hs ht q hqnew
    rw [card_connectedComponent_eq_one _ hconn]
  · have hreach := connectorEarOldDelete_every_component_meets_old
      H hH p hp hs ht hst hint d
    have hear := connectorEar_ends_reachable_after_delete_old
      H p hp hs ht hint d hsd htd
    have hcard := connectorEarOldDelete_component_card_lt
      H p d hs ht hsd htd hreach hsep hear
    have hpos : 0 < Fintype.card
        (((H ⊔ p.toSubgraph).coe.induce
          fun w : (H ⊔ p.toSubgraph).verts ↦
            w ≠ connectorEarOldVertsEmbedding H p d).ConnectedComponent) := by
      rw [Fintype.card_pos_iff]
      exact ⟨((H ⊔ p.toSubgraph).coe.induce
        fun w : (H ⊔ p.toSubgraph).verts ↦
          w ≠ connectorEarOldVertsEmbedding H p d).connectedComponentMk
            (connectorEarOldDeleteInclusion H p d ⟨⟨s, hs⟩, hsd⟩)⟩
    simpa only [f] using (show
      Fintype.card
          (((H ⊔ p.toSubgraph).coe.induce
            fun w : (H ⊔ p.toSubgraph).verts ↦
              w ≠ connectorEarOldVertsEmbedding H p d).ConnectedComponent) - 1 <
        Fintype.card
          ((H.coe.induce fun w : H.verts ↦ w ≠ d).ConnectedComponent) - 1 by
      omega)

/-- The vertex inclusion from a component end piece into the connector from
which it was cut. -/
def cutComponentPieceVertsEmbedding (H : G.Subgraph) (d : H.verts)
    (K : (deleteVertex H.coe d).ConnectedComponent) :
    (cutComponentPiece H d K).verts ↪ H.verts where
  toFun w := ⟨w.1, (cutComponentPiece_le H d K).1 w.2⟩
  inj' u v h := by
    apply Subtype.ext
    exact congrArg (fun w : H.verts ↦ w.1) h

/-- Inclusion after deleting corresponding vertices of an end piece and its
ambient connector. -/
def cutComponentPieceDeleteInclusion (H : G.Subgraph) (d : H.verts)
    (K : (deleteVertex H.coe d).ConnectedComponent)
    (p : (cutComponentPiece H d K).verts) :
    ((cutComponentPiece H d K).coe.induce
        (fun w : (cutComponentPiece H d K).verts ↦ w ≠ p)) →g
      (H.coe.induce
        (fun w : H.verts ↦
          w ≠ cutComponentPieceVertsEmbedding H d K p)) where
  toFun w := ⟨cutComponentPieceVertsEmbedding H d K w.1, by
    intro h
    apply w.2
    apply Subtype.ext
    exact congrArg (fun q : H.verts ↦ q.1) h⟩
  map_rel' h := (cutComponentPiece_le H d K).2 h

/-- Away from the restored cut vertex, collapse the complement of the end
piece back to the cut vertex.  This is a left inverse to the preceding
inclusion on vertices. -/
noncomputable def cutComponentPieceDeleteRetraction
    (H : G.Subgraph) (d : H.verts)
    (K : (deleteVertex H.coe d).ConnectedComponent)
    (p : (cutComponentPiece H d K).verts) (hpd : p.1 ≠ d.1) :
    {w : H.verts // w ≠ cutComponentPieceVertsEmbedding H d K p} →
      {w : (cutComponentPiece H d K).verts // w ≠ p} :=
  fun w ↦
    if hw : w.1.1 ∈ (cutComponentPiece H d K).verts then
      ⟨⟨w.1.1, hw⟩, by
        intro h
        apply w.2
        apply Subtype.ext
        exact congrArg
          (fun q : (cutComponentPiece H d K).verts ↦ q.1) h⟩
    else
      ⟨⟨d.1, cut_mem_cutComponentPiece H d K⟩, by
        intro h
        exact hpd (congrArg
          (fun q : (cutComponentPiece H d K).verts ↦ q.1) h).symm⟩

@[simp] theorem cutComponentPieceDeleteRetraction_inclusion
    (H : G.Subgraph) (d : H.verts)
    (K : (deleteVertex H.coe d).ConnectedComponent)
    (p : (cutComponentPiece H d K).verts) (hpd : p.1 ≠ d.1)
    (w : {q : (cutComponentPiece H d K).verts // q ≠ p}) :
    cutComponentPieceDeleteRetraction H d K p hpd
        (cutComponentPieceDeleteInclusion H d K p w) = w := by
  have hwPiece :
      (cutComponentPieceDeleteInclusion H d K p w).1.1 ∈
        (cutComponentPiece H d K).verts := by
    exact w.1.2
  apply Subtype.ext
  apply Subtype.ext
  rw [cutComponentPieceDeleteRetraction, dif_pos hwPiece]
  rfl

/-- The weak retraction sends an ambient-connector edge either to equality
or to an edge of the deleted end piece.  The only boundary vertex of a
component end piece is its restored cut vertex. -/
theorem cutComponentPieceDeleteRetraction_adj_eq_or_adj
    (H : G.Subgraph) (d : H.verts)
    (K : (deleteVertex H.coe d).ConnectedComponent)
    (p : (cutComponentPiece H d K).verts) (hpd : p.1 ≠ d.1)
    {u v : {w : H.verts //
      w ≠ cutComponentPieceVertsEmbedding H d K p}}
    (huv : (H.coe.induce
      (fun w : H.verts ↦
        w ≠ cutComponentPieceVertsEmbedding H d K p)).Adj u v) :
    cutComponentPieceDeleteRetraction H d K p hpd u =
        cutComponentPieceDeleteRetraction H d K p hpd v ∨
      ((cutComponentPiece H d K).coe.induce
        (fun w : (cutComponentPiece H d K).verts ↦ w ≠ p)).Adj
          (cutComponentPieceDeleteRetraction H d K p hpd u)
          (cutComponentPieceDeleteRetraction H d K p hpd v) := by
  classical
  by_cases hu : u.1.1 ∈ (cutComponentPiece H d K).verts
  · by_cases hv : v.1.1 ∈ (cutComponentPiece H d K).verts
    · right
      simp only [cutComponentPieceDeleteRetraction, dif_pos hu, dif_pos hv]
      obtain ⟨_, huEnd⟩ := (mem_cutComponentPiece_verts_iff H d K u.1.1).mp hu
      obtain ⟨_, hvEnd⟩ := (mem_cutComponentPiece_verts_iff H d K v.1.1).mp hv
      apply (Subgraph.coeSubgraph_adj
        ((⊤ : H.coe.Subgraph).induce (ComponentEndBlock.verts d K))
        u.1.1 v.1.1).2
      exact ⟨u.1.2, v.1.2, huEnd, hvEnd, huv⟩
    · obtain ⟨huH, huEnd⟩ :=
        (mem_cutComponentPiece_verts_iff H d K u.1.1).mp hu
      have huEnd' : u.1 ∈ ComponentEndBlock.verts d K := by
        simpa only [Subtype.coe_eta] using huEnd
      rw [ComponentEndBlock.verts, Set.mem_insert_iff] at huEnd'
      rcases huEnd' with hud | huSide
      · left
        apply Subtype.ext
        apply Subtype.ext
        simpa [cutComponentPieceDeleteRetraction, hu, hv] using
          congrArg Subtype.val hud
      · exfalso
        apply hv
        rw [mem_cutComponentPiece_verts_iff H d K v.1.1]
        refine ⟨v.1.2, ?_⟩
        have hvEnd : v.1 ∈ ComponentEndBlock.verts d K :=
          ComponentEndBlock.neighborSet_subset_verts
            (G := H.coe) K huSide huv
        simpa only [Subtype.coe_eta] using hvEnd
  · by_cases hv : v.1.1 ∈ (cutComponentPiece H d K).verts
    · obtain ⟨hvH, hvEnd⟩ :=
        (mem_cutComponentPiece_verts_iff H d K v.1.1).mp hv
      have hvEnd' : v.1 ∈ ComponentEndBlock.verts d K := by
        simpa only [Subtype.coe_eta] using hvEnd
      rw [ComponentEndBlock.verts, Set.mem_insert_iff] at hvEnd'
      rcases hvEnd' with hvd | hvSide
      · left
        apply Subtype.ext
        apply Subtype.ext
        simpa [cutComponentPieceDeleteRetraction, hu, hv] using
          (congrArg Subtype.val hvd).symm
      · exfalso
        apply hu
        rw [mem_cutComponentPiece_verts_iff H d K u.1.1]
        refine ⟨u.1.2, ?_⟩
        have huEnd : u.1 ∈ ComponentEndBlock.verts d K :=
          ComponentEndBlock.neighborSet_subset_verts
            (G := H.coe) K hvSide huv.symm
        simpa only [Subtype.coe_eta] using huEnd
    · left
      apply Subtype.ext
      apply Subtype.ext
      simp [cutComponentPieceDeleteRetraction, hu, hv]

/-- Except at the restored cut vertex, inclusion of a component end piece
induces an injection on connected components after deleting a vertex. -/
theorem cutComponentPieceDelete_componentMap_injective
    (H : G.Subgraph) (d : H.verts)
    (K : (deleteVertex H.coe d).ConnectedComponent)
    (p : (cutComponentPiece H d K).verts) (hpd : p.1 ≠ d.1) :
    Function.Injective (fun C :
      ((cutComponentPiece H d K).coe.induce
        (fun w : (cutComponentPiece H d K).verts ↦ w ≠ p)).ConnectedComponent ↦
      C.map (cutComponentPieceDeleteInclusion H d K p)) := by
  intro C D
  refine ConnectedComponent.ind₂ (c := C) (d := D) ?_
  intro u v huv
  change
    (H.coe.induce
      (fun w : H.verts ↦
        w ≠ cutComponentPieceVertsEmbedding H d K p)).connectedComponentMk
        (cutComponentPieceDeleteInclusion H d K p u) =
      (H.coe.induce
        (fun w : H.verts ↦
          w ≠ cutComponentPieceVertsEmbedding H d K p)).connectedComponentMk
        (cutComponentPieceDeleteInclusion H d K p v) at huv
  apply ConnectedComponent.sound
  have hreach := SimpleGraph.Reachable.map_of_adj_eq_or_adj
    (J := H.coe.induce (fun w : H.verts ↦
      w ≠ cutComponentPieceVertsEmbedding H d K p))
    (K := (cutComponentPiece H d K).coe.induce
      (fun w : (cutComponentPiece H d K).verts ↦ w ≠ p))
    (cutComponentPieceDeleteRetraction H d K p hpd)
    (fun {_ _} huv' ↦
      cutComponentPieceDeleteRetraction_adj_eq_or_adj H d K p hpd huv')
    (ConnectedComponent.exact huv)
  simpa only [cutComponentPieceDeleteRetraction_inclusion] using hreach

/-- Every non-cut summand of an end piece's cut-defect is bounded by the
corresponding summand of the ambient connector. -/
theorem cutComponentPiece_delete_component_card_le
    (H : G.Subgraph) (d : H.verts)
    (K : (deleteVertex H.coe d).ConnectedComponent)
    (p : (cutComponentPiece H d K).verts) (hpd : p.1 ≠ d.1) :
    Fintype.card
        (((cutComponentPiece H d K).coe.induce
          (fun w : (cutComponentPiece H d K).verts ↦ w ≠ p)).ConnectedComponent) ≤
      Fintype.card
        ((H.coe.induce
          (fun w : H.verts ↦
            w ≠ cutComponentPieceVertsEmbedding H d K p)).ConnectedComponent) :=
  Fintype.card_le_of_injective
    (fun C ↦ C.map (cutComponentPieceDeleteInclusion H d K p))
    (cutComponentPieceDelete_componentMap_injective H d K p hpd)

/-- The component end piece at a genuine cut vertex has strictly smaller
total cut-defect than its ambient connected connector.  This discharges the
strict hypothesis in both pruning moves. -/
theorem connectorCutDefect_cutComponentPiece_lt
    (H : G.Subgraph) (d : H.verts)
    (K : (deleteVertex H.coe d).ConnectedComponent)
    (hd : IsCutVertex H.coe d) :
    connectorCutDefect (cutComponentPiece H d K) < connectorCutDefect H := by
  let f := cutComponentPieceVertsEmbedding H d K
  refine connectorCutDefect_lt_of_embedding
    (cutComponentPiece H d K) H f ?_
      ⟨d.1, cut_mem_cutComponentPiece H d K⟩ ?_
  · intro p
    by_cases hpd : p.1 = d.1
    · have hp : p =
          ⟨d.1, cut_mem_cutComponentPiece H d K⟩ := Subtype.ext hpd
      subst p
      rw [cutComponentPiece_cut_summand_eq_zero H d K]
      omega
    · have hcard := cutComponentPiece_delete_component_card_le
        H d K p hpd
      simpa only [f, cutComponentPieceVertsEmbedding] using
        (Nat.sub_le_sub_right hcard 1)
  · have hfcut : f ⟨d.1, cut_mem_cutComponentPiece H d K⟩ = d := by
      apply Subtype.ext
      rfl
    rw [hfcut]
    exact cutComponentPiece_cut_summand_lt H d K hd

noncomputable def ABConnectorPair.cutDefect (C : M.ABConnectorPair) : ℕ :=
  connectorCutDefect C.aGraph + connectorCutDefect C.bGraph

/-- A connector pair minimizing AHT's cut-defect parameter among all
admissible pairs.  Finiteness of `G.Subgraph` supplies such a pair once the
three-stem pair above is shown admissible. -/
structure MinimalABConnectorPair extends M.ABConnectorPair where
  minimal : ∀ C : M.ABConnectorPair,
    toABConnectorPair.cutDefect ≤ C.cutDefect

/-- Finite minimization of AHT's cut-defect parameter. -/
theorem exists_minimalABConnectorPair :
    Nonempty (M.MinimalABConnectorPair) := by
  classical
  let candidates : Finset (G.Subgraph × G.Subgraph) :=
    Finset.univ.filter fun p ↦
      ∃ C : M.ABConnectorPair, (C.aGraph, C.bGraph) = p
  have hcandidates : candidates.Nonempty := by
    let C := M.initialABConnectorPair
    refine ⟨(C.aGraph, C.bGraph), ?_⟩
    simp only [candidates, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨C, rfl⟩
  obtain ⟨p, hp, hmin⟩ := candidates.exists_min_image
    (fun q ↦ connectorCutDefect q.1 + connectorCutDefect q.2) hcandidates
  have hp' : ∃ C : M.ABConnectorPair, (C.aGraph, C.bGraph) = p :=
    (Finset.mem_filter.mp hp).2
  obtain ⟨C, rfl⟩ := hp'
  refine ⟨{
    toABConnectorPair := C
    minimal := ?_ }⟩
  intro D
  apply hmin (D.aGraph, D.bGraph)
  simp only [candidates, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨D, rfl⟩

/-- A minimal pair cannot have all three `A`-attachments in a prunable end
piece whose cut-defect is strictly smaller.  The separate strict-defect
lemma is the finite component-count calculation isolated by AHT's
parameter `c`. -/
theorem MinimalABConnectorPair.not_all_A_in_prunable_piece
    (C : M.MinimalABConnectorPair)
    (d : C.aGraph.verts)
    (K : (deleteVertex C.aGraph.coe d).ConnectedComponent)
    (hdefect : connectorCutDefect (cutComponentPiece C.aGraph d K) <
      connectorCutDefect C.aGraph) :
    ¬(∀ a ∈ M.aSet,
      a ∈ (cutComponentPiece C.aGraph d K).verts) := by
  intro hcontains
  have hmin := C.minimal
    (ABConnectorPair.pruneA (M := M) C.toABConnectorPair d K hcontains)
  change connectorCutDefect C.aGraph + connectorCutDefect C.bGraph ≤
      connectorCutDefect (cutComponentPiece C.aGraph d K) +
        connectorCutDefect C.bGraph at hmin
  omega

/-- Symmetric `B`-side pruning obstruction. -/
theorem MinimalABConnectorPair.not_all_B_in_prunable_piece
    (C : M.MinimalABConnectorPair)
    (d : C.bGraph.verts)
    (K : (deleteVertex C.bGraph.coe d).ConnectedComponent)
    (hdefect : connectorCutDefect (cutComponentPiece C.bGraph d K) <
      connectorCutDefect C.bGraph) :
    ¬(∀ b ∈ M.bSet,
      b ∈ (cutComponentPiece C.bGraph d K).verts) := by
  intro hcontains
  have hmin := C.minimal
    (ABConnectorPair.pruneB (M := M) C.toABConnectorPair d K hcontains)
  change connectorCutDefect C.aGraph + connectorCutDefect C.bGraph ≤
      connectorCutDefect C.aGraph +
        connectorCutDefect (cutComponentPiece C.bGraph d K) at hmin
  omega

/-- The reusable minimality inequality for an admissible exchange on the
`A` side.  The proof is purely the cancellation step in AHT's minimization;
all path and component work is confined to constructing the hypotheses. -/
theorem MinimalABConnectorPair.cutDefect_aGraph_le_of_replaceA
    (C : M.MinimalABConnectorPair)
    (A' : G.Subgraph) (hconnected : A'.Connected)
    (hcontains : ∀ a ∈ M.aSet, a ∈ A'.verts)
    (hdisjoint : Disjoint A'.verts C.bGraph.verts)
    (havoids : Disjoint (A'.verts ∪ C.bGraph.verts)
      ((M.xPart : Set V) ∪ (M.yPart : Set V) ∪ (M.zPart : Set V))) :
    connectorCutDefect C.aGraph ≤ connectorCutDefect A' := by
  have hmin := C.minimal
    (ABConnectorPair.replaceA (M := M) C.toABConnectorPair A'
      hconnected hcontains hdisjoint havoids)
  change connectorCutDefect C.aGraph + connectorCutDefect C.bGraph ≤
      connectorCutDefect A' + connectorCutDefect C.bGraph at hmin
  omega

/-- The symmetric minimality inequality for an admissible exchange on the
`B` side. -/
theorem MinimalABConnectorPair.cutDefect_bGraph_le_of_replaceB
    (C : M.MinimalABConnectorPair)
    (B' : G.Subgraph) (hconnected : B'.Connected)
    (hcontains : ∀ b ∈ M.bSet, b ∈ B'.verts)
    (hdisjoint : Disjoint C.aGraph.verts B'.verts)
    (havoids : Disjoint (C.aGraph.verts ∪ B'.verts)
      ((M.xPart : Set V) ∪ (M.yPart : Set V) ∪ (M.zPart : Set V))) :
    connectorCutDefect C.bGraph ≤ connectorCutDefect B' := by
  have hmin := C.minimal
    (ABConnectorPair.replaceB (M := M) C.toABConnectorPair B'
      hconnected hcontains hdisjoint havoids)
  change connectorCutDefect C.aGraph + connectorCutDefect C.bGraph ≤
      connectorCutDefect C.aGraph + connectorCutDefect B' at hmin
  omega

/-! ### Maximal isolating sides at a cut vertex

After pruning has shown that the three attachments do not all lie in one
end piece, AHT chooses a component side containing one named attachment and
excluding the other two, maximal by inclusion.  Choosing maximum cardinality
is a convenient finite strengthening of that requirement.  This certificate
keeps the cut vertex and component dependent types together. -/

/-- A component of `H-d` which contains `a` but neither `b` nor `c`. -/
structure IsolatingCutSide (H : G.Subgraph) (a b c : H.verts) where
  cut : H.verts
  component : (deleteVertex H.coe cut).ConnectedComponent
  a_mem : a ∈ ComponentEndBlock.side cut component
  b_not_mem : b ∉ ComponentEndBlock.side cut component
  c_not_mem : c ∉ ComponentEndBlock.side cut component

/-- Interchange the two excluded attachments of an isolating side. -/
def IsolatingCutSide.swapBC {H : G.Subgraph} {a b c : H.verts}
    (S : IsolatingCutSide H a b c) : IsolatingCutSide H a c b where
  cut := S.cut
  component := S.component
  a_mem := S.a_mem
  b_not_mem := S.c_not_mem
  c_not_mem := S.b_not_mem

/-- A singleton which separates one displayed vertex from two others
determines the corresponding isolating component side.  This is the local
component extraction used in the maximal-endpiece exchange on p.15. -/
theorem exists_isolatingCutSide_of_singleton_separator
    {H : G.Subgraph} {a b c u : H.verts}
    (hau : a ≠ u)
    (hsep : Erdos599.Countable.Separates H.coe ({a} : Set H.verts)
      ({b, c} : Set H.verts) ({u} : Set H.verts)) :
    ∃ S : IsolatingCutSide H a b c, S.cut = u := by
  classical
  let a' : {w : H.verts // w ≠ u} := ⟨a, hau⟩
  let K : (deleteVertex H.coe u).ConnectedComponent :=
    (deleteVertex H.coe u).connectedComponentMk a'
  have haK : a ∈ ComponentEndBlock.side u K := by
    refine ⟨hau, ?_⟩
    simpa only [a', K, ConnectedComponent.mem_supp_iff,
      Subtype.coe_eta]
  have target_not_mem (t : H.verts)
      (htTarget : t ∈ ({b, c} : Set H.verts)) :
      t ∉ ComponentEndBlock.side u K := by
    intro htK
    obtain ⟨htu', htK'⟩ := htK
    let t' : {w : H.verts // w ≠ u} := ⟨t, htu'⟩
    have hcomp :
        (deleteVertex H.coe u).connectedComponentMk a' =
          (deleteVertex H.coe u).connectedComponentMk t' := by
      have htEq :
          (deleteVertex H.coe u).connectedComponentMk t' = K := by
        simpa only [ConnectedComponent.mem_supp_iff] using htK'
      exact (by simpa only [K] using htEq.symm)
    obtain ⟨q, hq⟩ := (ConnectedComponent.exact hcomp).exists_isPath
    let inc : deleteVertex H.coe u →g H.coe :=
      (SimpleGraph.Embedding.induce
        (G := H.coe) (s := fun w : H.verts ↦ w ≠ u)).toHom
    let p : H.coe.Walk a t := (q.map inc).copy rfl rfl
    have hp : p.IsPath := by
      exact (Walk.isPath_copy (q.map inc) rfl rfl).2
        (hq.map Subtype.val_injective)
    obtain ⟨v, hvp, hvu⟩ := hsep a (by simp) t htTarget p hp
    have hvEq : v = u := by simpa only [Set.mem_singleton_iff] using hvu
    subst v
    have huMap : u ∈ (q.map inc).support := by
      change u ∈ ((q.map inc).copy rfl rfl).support at hvp
      simpa only [Walk.support_copy] using hvp
    rw [Walk.support_map] at huMap
    obtain ⟨w, -, hwu⟩ := List.mem_map.mp huMap
    exact w.2 hwu
  exact ⟨{
    cut := u
    component := K
    a_mem := haK
    b_not_mem := target_not_mem b (by simp)
    c_not_mem := target_not_mem c (by simp) }, rfl⟩

/-- An isolating side remains in one component after a second ambient
vertex outside its connector is deleted.  Connectivity inside `H-cut`
supplies the required ambient path; the second deletion cannot meet it
because every vertex of that path belongs to `H`. -/
theorem IsolatingCutSide.side_subset_componentCompl
    {H : G.Subgraph} {a b c : H.verts}
    (S : IsolatingCutSide H a b c) {e : V}
    (he : e ∉ H.verts)
    (D : G.ComponentCompl
      ((({S.cut.1, e} : Finset V) : Set V)))
    (haD : a.1 ∈ (D : Set V)) :
    ∀ w : H.verts, w ∈ ComponentEndBlock.side S.cut S.component →
      w.1 ∈ (D : Set V) := by
  classical
  let K : Set V := ((({S.cut.1, e} : Finset V) : Set V))
  let f : (deleteVertex H.coe S.cut) →g G.induce Kᶜ :=
    { toFun := fun w =>
        (⟨w.1.1, by
          simp only [K, Set.mem_compl_iff, Finset.mem_coe,
            Finset.mem_insert, Finset.mem_singleton, not_or]
          constructor
          · intro h
            exact w.2 (Subtype.ext h)
          · intro h
            apply he
            rw [← h]
            exact w.1.2⟩ : {v : V // v ∈ Kᶜ})
      map_rel' := by
        intro u v h
        change G.Adj u.1.1 v.1.1
        exact H.hom.map_rel h }
  intro w hw
  let a' : {u : H.verts // u ≠ S.cut} := ⟨a, S.a_mem.1⟩
  let w' : {u : H.verts // u ≠ S.cut} := ⟨w, hw.1⟩
  have haEq :
      (deleteVertex H.coe S.cut).connectedComponentMk a' =
        S.component := by
    simpa only [a', ConnectedComponent.mem_supp_iff] using S.a_mem.2
  have hwEq :
      (deleteVertex H.coe S.cut).connectedComponentMk w' =
        S.component := by
    simpa only [w', ConnectedComponent.mem_supp_iff] using hw.2
  have hreach : (deleteVertex H.coe S.cut).Reachable a' w' :=
    ConnectedComponent.exact (haEq.trans hwEq.symm)
  have hmapped : (G.induce Kᶜ).Reachable (f a') (f w') :=
    hreach.map f
  have hcomp : (G.induce Kᶜ).connectedComponentMk (f a') =
      (G.induce Kᶜ).connectedComponentMk (f w') :=
    ConnectedComponent.sound hmapped
  have haComp : (G.induce Kᶜ).connectedComponentMk (f a') = D := by
    let aK : {v : V // v ∈ Kᶜ} := ⟨a.1, by
      simpa only [K, Set.mem_compl_iff] using haD.1⟩
    have hfa : f a' = aK := Subtype.ext rfl
    rw [hfa]
    simpa only [K, aK] using haD.2
  refine ⟨(f w').2, ?_⟩
  let wK : {v : V // v ∈ Kᶜ} := ⟨w.1, (f w').2⟩
  have hfw : wK = f w' := Subtype.ext rfl
  change (G.induce Kᶜ).connectedComponentMk wK = D
  rw [hfw]
  exact hcomp.symm.trans haComp

/-- In the two-vertex deletion formed by an A-isolating cut and any
B-connector vertex, the component containing `x` also contains `xA`.
The prefix of the canonical `xA--xB` bridge ending at `x` avoids both
deleted vertices: it meets the A-connector only at `xA`, and the
B-connector only at `xB`, which occurs strictly after `x`. -/
theorem MinimalABConnectorPair.xA_mem_pairComponent
    (C : M.MinimalABConnectorPair)
    (S : IsolatingCutSide C.aGraph
      (ABConnectorPair.xAIn (M := M) C.toABConnectorPair)
      (ABConnectorPair.yAIn (M := M) C.toABConnectorPair)
      (ABConnectorPair.zAIn (M := M) C.toABConnectorPair))
    (vB : C.bGraph.verts)
    (D : G.ComponentCompl
      ((({S.cut.1, vB.1} : Finset V) : Set V)))
    (hxD : x ∈ (D : Set V)) : M.xSep.left ∈ (D : Set V) := by
  classical
  let P : G.Walk M.xSep.left x :=
    M.xTerminalBridge.takeUntil x M.x_mem_xTerminalBridge
  have hxBNotP : M.xSep.right ∉ P.support := by
    exact Walk.endpoint_notMem_support_takeUntil
      M.xTerminalBridge_isPath M.x_mem_xTerminalBridge
        M.xSep.x_ne_right.symm
  have havoid : ∀ w, w ∈ P.support →
      w ∈ (((({S.cut.1, vB.1} : Finset V) : Set V)))ᶜ := by
    intro w hw
    have hwBridge : w ∈ M.xTerminalBridge.support :=
      M.xTerminalBridge.support_takeUntil_subset_support
        M.x_mem_xTerminalBridge hw
    simp only [Set.mem_compl_iff, Finset.mem_coe,
      Finset.mem_insert, Finset.mem_singleton, not_or]
    constructor
    · intro h
      have hwA : w ∈ C.aGraph.verts := by
        rw [h]
        exact S.cut.2
      have hwEq := C.xTerminalBridge_meets_aGraph_only_left
        (M := M) hwBridge hwA
      exact S.a_mem.1 (Subtype.ext (hwEq.symm.trans h))
    · intro h
      have hwB : w ∈ C.bGraph.verts := by
        rw [h]
        exact vB.2
      have hwEq := C.xTerminalBridge_meets_bGraph_only_right
        (M := M) hwBridge hwB
      exact hxBNotP (hwEq ▸ hw)
  let q := P.induce
    (((({S.cut.1, vB.1} : Finset V) : Set V)))ᶜ havoid
  have hcomp :
      G.componentComplMk (havoid M.xSep.left P.start_mem_support) =
        G.componentComplMk (havoid x P.end_mem_support) := by
    rw [ConnectedComponent.eq]
    exact q.reachable
  refine ⟨havoid M.xSep.left P.start_mem_support, ?_⟩
  exact hcomp.trans hxD.2

/-- With active isolating sides on both connectors, the same pair
component also contains `xB`.  This is the symmetric terminal-bridge
suffix needed to put `CA ∪ X ∪ CB` in one component of
`G - {vA,vB}`. -/
theorem MinimalABConnectorPair.xB_mem_pairComponent
    (C : M.MinimalABConnectorPair)
    (SA : IsolatingCutSide C.aGraph
      (ABConnectorPair.xAIn (M := M) C.toABConnectorPair)
      (ABConnectorPair.yAIn (M := M) C.toABConnectorPair)
      (ABConnectorPair.zAIn (M := M) C.toABConnectorPair))
    (SB : IsolatingCutSide C.bGraph
      (ABConnectorPair.xBIn (M := M) C.toABConnectorPair)
      (ABConnectorPair.yBIn (M := M) C.toABConnectorPair)
      (ABConnectorPair.zBIn (M := M) C.toABConnectorPair))
    (D : G.ComponentCompl
      ((({SA.cut.1, SB.cut.1} : Finset V) : Set V)))
    (hxD : x ∈ (D : Set V)) : M.xSep.right ∈ (D : Set V) := by
  classical
  let P : G.Walk x M.xSep.right :=
    M.xTerminalBridge.dropUntil x M.x_mem_xTerminalBridge
  have hxANotP : M.xSep.left ∉ P.support := by
    intro hxA
    have hxARev : M.xSep.left ∈
        (M.xTerminalBridge.dropUntil x
          M.x_mem_xTerminalBridge).reverse.support := by
      simpa only [P, Walk.support_reverse, List.mem_reverse] using hxA
    have hxATake : M.xSep.left ∈
        (M.xTerminalBridge.takeUntil x
          M.x_mem_xTerminalBridge).support :=
      (M.xTerminalBridge.takeUntil x
        M.x_mem_xTerminalBridge).start_mem_support
    have hEq := Walk.IsPath.takeUntil_inter_reverse_dropUntil_only
      M.xTerminalBridge_isPath M.x_mem_xTerminalBridge
      M.xSep.left hxATake hxARev
    exact M.xSep.x_ne_left hEq.symm
  have havoid : ∀ w, w ∈ P.support →
      w ∈ (((({SA.cut.1, SB.cut.1} : Finset V) : Set V)))ᶜ := by
    intro w hw
    have hwBridge : w ∈ M.xTerminalBridge.support :=
      M.xTerminalBridge.support_dropUntil_subset_support
        M.x_mem_xTerminalBridge hw
    simp only [Set.mem_compl_iff, Finset.mem_coe,
      Finset.mem_insert, Finset.mem_singleton, not_or]
    constructor
    · intro h
      have hwA : w ∈ C.aGraph.verts := by
        simpa only [h] using SA.cut.2
      have hwEq := C.xTerminalBridge_meets_aGraph_only_left
        (M := M) hwBridge hwA
      exact hxANotP (hwEq ▸ hw)
    · intro h
      have hwB : w ∈ C.bGraph.verts := by
        simpa only [h] using SB.cut.2
      have hwEq := C.xTerminalBridge_meets_bGraph_only_right
        (M := M) hwBridge hwB
      exact SB.a_mem.1 (Subtype.ext (hwEq.symm.trans h))
  let q := P.induce
    (((({SA.cut.1, SB.cut.1} : Finset V) : Set V)))ᶜ havoid
  have hcomp :
      G.componentComplMk (havoid x P.start_mem_support) =
        G.componentComplMk (havoid M.xSep.right P.end_mem_support) := by
    rw [ConnectedComponent.eq]
    exact q.reachable
  refine ⟨havoid M.xSep.right P.end_mem_support, ?_⟩
  exact hcomp.symm.trans hxD.2

/-- The component of `G-{vA,vB}` containing `x` contains the entire old
maximal `x`-side and the chosen A-isolating side.  Thus, if its opposite
rim were outside that component, it would be a forbidden enlargement of
the maximal routed `x`-separator. -/
theorem MinimalABConnectorPair.pairComponent_contains_xSides
    (C : M.MinimalABConnectorPair)
    (S : IsolatingCutSide C.aGraph
      (ABConnectorPair.xAIn (M := M) C.toABConnectorPair)
      (ABConnectorPair.yAIn (M := M) C.toABConnectorPair)
      (ABConnectorPair.zAIn (M := M) C.toABConnectorPair))
    (vB : C.bGraph.verts)
    (D : G.ComponentCompl
      ((({S.cut.1, vB.1} : Finset V) : Set V)))
    (hxD : x ∈ (D : Set V)) :
    (M.xSep.side : Set V) ⊆ (D : Set V) ∧
      M.xSep.left ∈ (D : Set V) ∧
      ∀ w : C.aGraph.verts,
        w ∈ ComponentEndBlock.side S.cut S.component →
          w.1 ∈ (D : Set V) := by
  have hdisjoint : Disjoint (M.xSep.side : Set V)
      ((({S.cut.1, vB.1} : Finset V) : Set V)) := by
    rw [Set.disjoint_left]
    intro w hwSide hwPair
    have hwX : w ∈ M.xPart := by
      simpa only [xPart, mem_componentCarrier] using hwSide
    simp only [Finset.mem_coe, Finset.mem_insert,
      Finset.mem_singleton] at hwPair
    rcases hwPair with hwA | hwB
    · have hcutA : S.cut.1 ∈ C.aGraph.verts := S.cut.2
      exact Set.disjoint_left.mp C.avoids_terminal_parts
        (Or.inl hcutA) (Or.inl (Or.inl (hwA ▸ hwX)))
    · exact Set.disjoint_left.mp C.avoids_terminal_parts
        (Or.inr vB.2) (Or.inl (Or.inl (hwB ▸ hwX)))
  have hOld : (M.xSep.side : Set V) ⊆ (D : Set V) :=
    ComponentCompl.subset_of_disjoint_of_shared M.xSep.side D
      hdisjoint M.xSep.x_mem_side hxD
  have hxAD := C.xA_mem_pairComponent (M := M) S vB D hxD
  have hvBNotA : vB.1 ∉ C.aGraph.verts := by
    intro h
    exact Set.disjoint_left.mp C.vertex_disjoint h vB.2
  exact ⟨hOld, hxAD,
    S.side_subset_componentCompl hvBNotA D hxAD⟩

/-- In the active/active case the component of `G - {vA,vB}` containing
`x` contains both chosen isolating sides.  The `B` assertion is the
preceding symmetric bridge fact followed by transport across
`{vA,vB} = {vB,vA}`. -/
theorem MinimalABConnectorPair.pairComponent_contains_activeSides
    (C : M.MinimalABConnectorPair)
    (SA : IsolatingCutSide C.aGraph
      (ABConnectorPair.xAIn (M := M) C.toABConnectorPair)
      (ABConnectorPair.yAIn (M := M) C.toABConnectorPair)
      (ABConnectorPair.zAIn (M := M) C.toABConnectorPair))
    (SB : IsolatingCutSide C.bGraph
      (ABConnectorPair.xBIn (M := M) C.toABConnectorPair)
      (ABConnectorPair.yBIn (M := M) C.toABConnectorPair)
      (ABConnectorPair.zBIn (M := M) C.toABConnectorPair))
    (D : G.ComponentCompl
      ((({SA.cut.1, SB.cut.1} : Finset V) : Set V)))
    (hxD : x ∈ (D : Set V)) :
    (∀ w : C.aGraph.verts,
      w ∈ ComponentEndBlock.side SA.cut SA.component →
        w.1 ∈ (D : Set V)) ∧
    ∀ w : C.bGraph.verts,
      w ∈ ComponentEndBlock.side SB.cut SB.component →
        w.1 ∈ (D : Set V) := by
  have hA := (C.pairComponent_contains_xSides
    (M := M) SA SB.cut D hxD).2.2
  have hxBD : M.xSep.right ∈ (D : Set V) :=
    C.xB_mem_pairComponent (M := M) SA SB D hxD
  have hpair :
      ((({SA.cut.1, SB.cut.1} : Finset V) : Set V)) =
        ((({SB.cut.1, SA.cut.1} : Finset V) : Set V)) := by
    ext w
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton]
    tauto
  let D' : G.ComponentCompl
      ((({SB.cut.1, SA.cut.1} : Finset V) : Set V)) :=
    ComponentCompl.transport hpair D
  have hxBD' : M.xSep.right ∈ (D' : Set V) := by
    simpa only [D', ComponentCompl.mem_transport] using hxBD
  have hAcutNotB : SA.cut.1 ∉ C.bGraph.verts := by
    intro h
    exact Set.disjoint_left.mp C.vertex_disjoint SA.cut.2 h
  have hB' := SB.side_subset_componentCompl hAcutNotB D' hxBD'
  refine ⟨hA, ?_⟩
  intro w hw
  have hwD' := hB' w hw
  simpa only [D', ComponentCompl.mem_transport] using hwD'

/-- Maximality of the routed `x`-separator forces the component of
`G-{vA,vB}` containing `x` to meet the opposite `x`-rim away from both
new cut vertices.  Otherwise that very component is a vertex-cycle
separator containing the old `x`-side and `xA`, contradicting maximality. -/
theorem MinimalABConnectorPair.exists_xRim_mem_pairComponent
    (C : M.MinimalABConnectorPair)
    (S : IsolatingCutSide C.aGraph
      (ABConnectorPair.xAIn (M := M) C.toABConnectorPair)
      (ABConnectorPair.yAIn (M := M) C.toABConnectorPair)
      (ABConnectorPair.zAIn (M := M) C.toABConnectorPair))
    (vB : C.bGraph.verts) (hcuts : S.cut.1 ≠ vB.1)
    (D : G.ComponentCompl
      ((({S.cut.1, vB.1} : Finset V) : Set V)))
    (hxD : x ∈ (D : Set V)) :
    ∃ w, w ∈ T.xRim.support ∧ w ≠ S.cut.1 ∧
      w ≠ vB.1 ∧ w ∈ (D : Set V) := by
  by_contra h
  have hrim : ∀ w, w ∈ T.xRim.support → w ≠ S.cut.1 →
      w ≠ vB.1 → w ∉ (D : Set V) := by
    intro w hw hwA hwB hwD
    exact h ⟨w, hw, hwA, hwB, hwD⟩
  have hxCuts : x ≠ S.cut.1 ∧ x ≠ vB.1 := by
    simpa only [Finset.mem_coe, Finset.mem_insert,
      Finset.mem_singleton, not_or] using hxD.1
  let R : VertexCycleSeparator T.xRim x :=
    { left := S.cut.1
      right := vB.1
      left_ne_right := hcuts
      x_ne_left := hxCuts.1
      x_ne_right := hxCuts.2
      side := D
      x_mem_side := hxD
      rim_outside_side := hrim }
  obtain ⟨hOld, hxAD, -⟩ :=
    C.pairComponent_contains_xSides (M := M) S vB D hxD
  exact M.false_of_x_vertexCycleSeparator_replacement R hOld hxAD

/-- Concrete external-path output of the maximal-`X` exchange.  For an
A-side isolating cut and any B-connector vertex, there is a simple path
from `xA` to the opposite `x`-rim which avoids both cut vertices; its rim
end is different from them as well. -/
theorem MinimalABConnectorPair.exists_externalPath_to_xRim
    (C : M.MinimalABConnectorPair)
    (S : IsolatingCutSide C.aGraph
      (ABConnectorPair.xAIn (M := M) C.toABConnectorPair)
      (ABConnectorPair.yAIn (M := M) C.toABConnectorPair)
      (ABConnectorPair.zAIn (M := M) C.toABConnectorPair))
    (vB : C.bGraph.verts) :
    ∃ w, w ∈ T.xRim.support ∧ w ≠ S.cut.1 ∧ w ≠ vB.1 ∧
      ∃ p : G.Walk M.xSep.left w, p.IsPath ∧
        ∀ u, u ∈ p.support → u ≠ S.cut.1 ∧ u ≠ vB.1 := by
  classical
  have hcuts : S.cut.1 ≠ vB.1 := by
    intro h
    exact Set.disjoint_left.mp C.vertex_disjoint S.cut.2
      (h ▸ vB.2)
  have hxAvoid :
      x ∈ (((({S.cut.1, vB.1} : Finset V) : Set V)))ᶜ := by
    simp only [Set.mem_compl_iff, Finset.mem_coe,
      Finset.mem_insert, Finset.mem_singleton, not_or]
    constructor
    · intro h
      have hxA : x ∈ C.aGraph.verts := by
        simpa only [h] using S.cut.2
      exact Set.disjoint_left.mp C.avoids_terminal_parts
        (Or.inl hxA) (Or.inl (Or.inl M.x_mem_xPart))
    · intro h
      have hxB : x ∈ C.bGraph.verts := by
        simpa only [h] using vB.2
      exact Set.disjoint_left.mp C.avoids_terminal_parts
        (Or.inr hxB) (Or.inl (Or.inl M.x_mem_xPart))
  let D : G.ComponentCompl
      ((({S.cut.1, vB.1} : Finset V) : Set V)) :=
    G.componentComplMk hxAvoid
  have hxD : x ∈ (D : Set V) := ⟨hxAvoid, rfl⟩
  obtain ⟨w, hwRim, hwA, hwB, hwD⟩ :=
    C.exists_xRim_mem_pairComponent (M := M) S vB hcuts D hxD
  have hxAD : M.xSep.left ∈ (D : Set V) :=
    C.xA_mem_pairComponent (M := M) S vB D hxD
  let xA' : {u : V // u ∈
      (((({S.cut.1, vB.1} : Finset V) : Set V)))ᶜ} :=
    ⟨M.xSep.left, hxAD.1⟩
  let w' : {u : V // u ∈
      (((({S.cut.1, vB.1} : Finset V) : Set V)))ᶜ} :=
    ⟨w, hwD.1⟩
  have hreach :
      (G.induce (((({S.cut.1, vB.1} : Finset V) : Set V)))ᶜ).Reachable
        xA' w' :=
    ConnectedComponent.exact (hxAD.2.trans hwD.2.symm)
  obtain ⟨q, hq⟩ := hreach.exists_isPath
  let inc : G.induce
      (((({S.cut.1, vB.1} : Finset V) : Set V)))ᶜ →g G :=
    (SimpleGraph.Embedding.induce
      (G := G)
      (s := (((({S.cut.1, vB.1} : Finset V) : Set V)))ᶜ)).toHom
  let p₀ := q.map inc
  let p : G.Walk M.xSep.left w := p₀.copy rfl rfl
  refine ⟨w, hwRim, hwA, hwB, p, ?_, ?_⟩
  · exact (Walk.isPath_copy p₀ rfl rfl).2
      (hq.map Subtype.val_injective)
  · intro u hu
    have hu₀ : u ∈ p₀.support := by
      change u ∈ (p₀.copy rfl rfl).support at hu
      rw [Walk.support_copy] at hu
      exact hu
    change u ∈ (q.map inc).support at hu₀
    rw [Walk.support_map] at hu₀
    obtain ⟨v, -, rfl⟩ := List.mem_map.mp hu₀
    have hvNot : v.1 ∉
        ((({S.cut.1, vB.1} : Finset V) : Set V)) := v.2
    have hvinc : inc v = v.1 := rfl
    rw [hvinc]
    simpa only [Finset.mem_coe, Finset.mem_insert,
      Finset.mem_singleton, not_or] using hvNot

/-- The minimality half of the p.15 external-ear exchange.  A clean ear
from an isolated component side back to a different component of the same
connector strictly lowers the cut-defect, so it cannot remain disjoint from
the other connector and from the three terminal components. -/
theorem MinimalABConnectorPair.false_of_clean_A_ear
    (C : M.MinimalABConnectorPair)
    (S : IsolatingCutSide C.aGraph
      (ABConnectorPair.xAIn (M := M) C.toABConnectorPair)
      (ABConnectorPair.yAIn (M := M) C.toABConnectorPair)
      (ABConnectorPair.zAIn (M := M) C.toABConnectorPair))
    {s t : V} (p : G.Walk s t) (hp : p.IsPath)
    (hs : s ∈ C.aGraph.verts) (ht : t ∈ C.aGraph.verts)
    (hsSide : (⟨s, hs⟩ : C.aGraph.verts) ∈
      ComponentEndBlock.side S.cut S.component)
    (htCut : (⟨t, ht⟩ : C.aGraph.verts) ≠ S.cut)
    (htSide : (⟨t, ht⟩ : C.aGraph.verts) ∉
      ComponentEndBlock.side S.cut S.component)
    (hint : ∀ w, w ∈ p.support → w ≠ s → w ≠ t →
      w ∉ C.aGraph.verts)
    (hdisjoint : Disjoint (C.aGraph ⊔ p.toSubgraph).verts
      C.bGraph.verts)
    (havoids : Disjoint
      ((C.aGraph ⊔ p.toSubgraph).verts ∪ C.bGraph.verts)
      ((M.xPart : Set V) ∪ (M.yPart : Set V) ∪ (M.zPart : Set V))) :
    False := by
  classical
  have hsCut : (⟨s, hs⟩ : C.aGraph.verts) ≠ S.cut := hsSide.1
  have hsep : ¬(C.aGraph.coe.induce
      fun w : C.aGraph.verts ↦ w ≠ S.cut).Reachable
      ⟨⟨s, hs⟩, hsCut⟩ ⟨⟨t, ht⟩, htCut⟩ := by
    intro hreach
    apply htSide
    refine ⟨htCut, ?_⟩
    have hsEq :
        (deleteVertex C.aGraph.coe S.cut).connectedComponentMk
            ⟨⟨s, hs⟩, hsCut⟩ = S.component := by
      simpa only [ConnectedComponent.mem_supp_iff] using hsSide.2
    have hstEq :
        (deleteVertex C.aGraph.coe S.cut).connectedComponentMk
            ⟨⟨s, hs⟩, hsCut⟩ =
          (deleteVertex C.aGraph.coe S.cut).connectedComponentMk
            ⟨⟨t, ht⟩, htCut⟩ :=
      ConnectedComponent.sound hreach
    simpa only [ConnectedComponent.mem_supp_iff] using hstEq.symm.trans hsEq
  have hstrict : connectorCutDefect (C.aGraph ⊔ p.toSubgraph) <
      connectorCutDefect C.aGraph :=
    connectorCutDefect_sup_path_lt C.aGraph C.a_connected p hp hs ht hint
      S.cut hsCut htCut hsep
  have hconnected : (C.aGraph ⊔ p.toSubgraph).Connected := by
    apply Subgraph.connected_sup C.a_connected.preconnected
      p.toSubgraph_connected.preconnected
    exact ⟨s, hs, p.mem_verts_toSubgraph.mpr p.start_mem_support⟩
  have hcontains : ∀ a ∈ M.aSet,
      a ∈ (C.aGraph ⊔ p.toSubgraph).verts := by
    intro a ha
    exact Or.inl (C.a_contains a ha)
  have hle := C.cutDefect_aGraph_le_of_replaceA (M := M)
    (C.aGraph ⊔ p.toSubgraph) hconnected hcontains hdisjoint havoids
  omega

/-- Symmetric minimality exchange for a clean ear of the `B` connector. -/
theorem MinimalABConnectorPair.false_of_clean_B_ear
    (C : M.MinimalABConnectorPair)
    (S : IsolatingCutSide C.bGraph
      (ABConnectorPair.xBIn (M := M) C.toABConnectorPair)
      (ABConnectorPair.yBIn (M := M) C.toABConnectorPair)
      (ABConnectorPair.zBIn (M := M) C.toABConnectorPair))
    {s t : V} (p : G.Walk s t) (hp : p.IsPath)
    (hs : s ∈ C.bGraph.verts) (ht : t ∈ C.bGraph.verts)
    (hsSide : (⟨s, hs⟩ : C.bGraph.verts) ∈
      ComponentEndBlock.side S.cut S.component)
    (htCut : (⟨t, ht⟩ : C.bGraph.verts) ≠ S.cut)
    (htSide : (⟨t, ht⟩ : C.bGraph.verts) ∉
      ComponentEndBlock.side S.cut S.component)
    (hint : ∀ w, w ∈ p.support → w ≠ s → w ≠ t →
      w ∉ C.bGraph.verts)
    (hdisjoint : Disjoint C.aGraph.verts
      (C.bGraph ⊔ p.toSubgraph).verts)
    (havoids : Disjoint
      (C.aGraph.verts ∪ (C.bGraph ⊔ p.toSubgraph).verts)
      ((M.xPart : Set V) ∪ (M.yPart : Set V) ∪ (M.zPart : Set V))) :
    False := by
  classical
  have hsCut : (⟨s, hs⟩ : C.bGraph.verts) ≠ S.cut := hsSide.1
  have hsep : ¬(C.bGraph.coe.induce
      fun w : C.bGraph.verts ↦ w ≠ S.cut).Reachable
      ⟨⟨s, hs⟩, hsCut⟩ ⟨⟨t, ht⟩, htCut⟩ := by
    intro hreach
    apply htSide
    refine ⟨htCut, ?_⟩
    have hsEq :
        (deleteVertex C.bGraph.coe S.cut).connectedComponentMk
            ⟨⟨s, hs⟩, hsCut⟩ = S.component := by
      simpa only [ConnectedComponent.mem_supp_iff] using hsSide.2
    have hstEq :
        (deleteVertex C.bGraph.coe S.cut).connectedComponentMk
            ⟨⟨s, hs⟩, hsCut⟩ =
          (deleteVertex C.bGraph.coe S.cut).connectedComponentMk
            ⟨⟨t, ht⟩, htCut⟩ :=
      ConnectedComponent.sound hreach
    simpa only [ConnectedComponent.mem_supp_iff] using hstEq.symm.trans hsEq
  have hstrict : connectorCutDefect (C.bGraph ⊔ p.toSubgraph) <
      connectorCutDefect C.bGraph :=
    connectorCutDefect_sup_path_lt C.bGraph C.b_connected p hp hs ht hint
      S.cut hsCut htCut hsep
  have hconnected : (C.bGraph ⊔ p.toSubgraph).Connected := by
    apply Subgraph.connected_sup C.b_connected.preconnected
      p.toSubgraph_connected.preconnected
    exact ⟨s, hs, p.mem_verts_toSubgraph.mpr p.start_mem_support⟩
  have hcontains : ∀ b ∈ M.bSet,
      b ∈ (C.bGraph ⊔ p.toSubgraph).verts := by
    intro b hb
    exact Or.inl (C.b_contains b hb)
  have hle := C.cutDefect_bGraph_le_of_replaceB (M := M)
    (C.bGraph ⊔ p.toSubgraph) hconnected hcontains hdisjoint havoids
  omega

/-- User-facing form of the `A`-ear contradiction.  Once the path meets
the two connector graphs only at its two `A`-ends and avoids the three
terminal components, all admissibility side conditions for the strict
cut-defect exchange are automatic. -/
theorem MinimalABConnectorPair.false_of_connector_clean_A_ear
    (C : M.MinimalABConnectorPair)
    (S : IsolatingCutSide C.aGraph
      (ABConnectorPair.xAIn (M := M) C.toABConnectorPair)
      (ABConnectorPair.yAIn (M := M) C.toABConnectorPair)
      (ABConnectorPair.zAIn (M := M) C.toABConnectorPair))
    {s t : V} (p : G.Walk s t) (hp : p.IsPath)
    (hs : s ∈ C.aGraph.verts) (ht : t ∈ C.aGraph.verts)
    (hsSide : (⟨s, hs⟩ : C.aGraph.verts) ∈
      ComponentEndBlock.side S.cut S.component)
    (htCut : (⟨t, ht⟩ : C.aGraph.verts) ≠ S.cut)
    (htSide : (⟨t, ht⟩ : C.aGraph.verts) ∉
      ComponentEndBlock.side S.cut S.component)
    (hmeet : ∀ w, w ∈ p.support →
      w ∈ C.aGraph.verts ∪ C.bGraph.verts → w = s ∨ w = t)
    (hparts : ∀ w, w ∈ p.support →
      w ∉ (M.xPart : Set V) ∪ (M.yPart : Set V) ∪
        (M.zPart : Set V)) : False := by
  have hint : ∀ w, w ∈ p.support → w ≠ s → w ≠ t →
      w ∉ C.aGraph.verts := by
    intro w hw hws hwt hwA
    rcases hmeet w hw (Or.inl hwA) with h | h
    · exact hws h
    · exact hwt h
  have hdisjoint : Disjoint (C.aGraph ⊔ p.toSubgraph).verts
      C.bGraph.verts := by
    rw [Set.disjoint_left]
    intro w hwSup hwB
    simp only [Subgraph.verts_sup, Set.mem_union] at hwSup
    rcases hwSup with hwA | hwP
    · exact Set.disjoint_left.mp C.vertex_disjoint hwA hwB
    · have hw : w ∈ p.support := by
        simpa only [Walk.mem_verts_toSubgraph] using hwP
      rcases hmeet w hw (Or.inr hwB) with rfl | rfl
      · exact Set.disjoint_left.mp C.vertex_disjoint hs hwB
      · exact Set.disjoint_left.mp C.vertex_disjoint ht hwB
  have havoids : Disjoint
      ((C.aGraph ⊔ p.toSubgraph).verts ∪ C.bGraph.verts)
      ((M.xPart : Set V) ∪ (M.yPart : Set V) ∪
        (M.zPart : Set V)) := by
    rw [Set.disjoint_left]
    intro w hw hwPart
    rcases hw with hwSup | hwB
    · simp only [Subgraph.verts_sup, Set.mem_union] at hwSup
      rcases hwSup with hwA | hwP
      · exact Set.disjoint_left.mp C.avoids_terminal_parts
          (Or.inl hwA) hwPart
      · apply hparts w
        · simpa only [Walk.mem_verts_toSubgraph] using hwP
        · exact hwPart
    · exact Set.disjoint_left.mp C.avoids_terminal_parts
        (Or.inr hwB) hwPart
  exact C.false_of_clean_A_ear (M := M) S p hp hs ht hsSide htCut
    htSide hint hdisjoint havoids

/-- Symmetric connector-clean `B`-ear contradiction. -/
theorem MinimalABConnectorPair.false_of_connector_clean_B_ear
    (C : M.MinimalABConnectorPair)
    (S : IsolatingCutSide C.bGraph
      (ABConnectorPair.xBIn (M := M) C.toABConnectorPair)
      (ABConnectorPair.yBIn (M := M) C.toABConnectorPair)
      (ABConnectorPair.zBIn (M := M) C.toABConnectorPair))
    {s t : V} (p : G.Walk s t) (hp : p.IsPath)
    (hs : s ∈ C.bGraph.verts) (ht : t ∈ C.bGraph.verts)
    (hsSide : (⟨s, hs⟩ : C.bGraph.verts) ∈
      ComponentEndBlock.side S.cut S.component)
    (htCut : (⟨t, ht⟩ : C.bGraph.verts) ≠ S.cut)
    (htSide : (⟨t, ht⟩ : C.bGraph.verts) ∉
      ComponentEndBlock.side S.cut S.component)
    (hmeet : ∀ w, w ∈ p.support →
      w ∈ C.aGraph.verts ∪ C.bGraph.verts → w = s ∨ w = t)
    (hparts : ∀ w, w ∈ p.support →
      w ∉ (M.xPart : Set V) ∪ (M.yPart : Set V) ∪
        (M.zPart : Set V)) : False := by
  have hint : ∀ w, w ∈ p.support → w ≠ s → w ≠ t →
      w ∉ C.bGraph.verts := by
    intro w hw hws hwt hwB
    rcases hmeet w hw (Or.inr hwB) with h | h
    · exact hws h
    · exact hwt h
  have hdisjoint : Disjoint C.aGraph.verts
      (C.bGraph ⊔ p.toSubgraph).verts := by
    rw [Set.disjoint_left]
    intro w hwA hwSup
    simp only [Subgraph.verts_sup, Set.mem_union] at hwSup
    rcases hwSup with hwB | hwP
    · exact Set.disjoint_left.mp C.vertex_disjoint hwA hwB
    · have hw : w ∈ p.support := by
        simpa only [Walk.mem_verts_toSubgraph] using hwP
      rcases hmeet w hw (Or.inl hwA) with rfl | rfl
      · exact Set.disjoint_left.mp C.vertex_disjoint hwA hs
      · exact Set.disjoint_left.mp C.vertex_disjoint hwA ht
  have havoids : Disjoint
      (C.aGraph.verts ∪ (C.bGraph ⊔ p.toSubgraph).verts)
      ((M.xPart : Set V) ∪ (M.yPart : Set V) ∪
        (M.zPart : Set V)) := by
    rw [Set.disjoint_left]
    intro w hw hwPart
    rcases hw with hwA | hwSup
    · exact Set.disjoint_left.mp C.avoids_terminal_parts
        (Or.inl hwA) hwPart
    · simp only [Subgraph.verts_sup, Set.mem_union] at hwSup
      rcases hwSup with hwB | hwP
      · exact Set.disjoint_left.mp C.avoids_terminal_parts
          (Or.inr hwB) hwPart
      · apply hparts w
        · simpa only [Walk.mem_verts_toSubgraph] using hwP
        · exact hwPart
  exact C.false_of_clean_B_ear (M := M) S p hp hs ht hsSide htCut
    htSide hint hdisjoint havoids

/-- Distinct components after deleting a vertex have disjoint component
sides when viewed back in the undeleted graph. -/
theorem componentEndBlock_side_disjoint_of_ne {H : G.Subgraph}
    {d : H.verts}
    {K L : (deleteVertex H.coe d).ConnectedComponent} (hKL : K ≠ L) :
    Disjoint (ComponentEndBlock.side d K)
      (ComponentEndBlock.side d L) := by
  rw [Set.disjoint_left]
  intro w hwK hwL
  obtain ⟨hwd, hwK⟩ := hwK
  obtain ⟨hwd', hwL⟩ := hwL
  apply hKL
  apply ConnectedComponent.eq_of_common_vertex hwK
  simpa only [Subtype.coe_eta] using hwL

/-- Removing one component of `H-d` but retaining `d` and every other
component preserves connectedness.  Each retained component reaches the
common cut vertex inside its own endblock. -/
theorem cutComponentComplement_connected (H : G.Subgraph)
    (hH : H.Connected) (d : H.verts)
    (K : (deleteVertex H.coe d).ConnectedComponent) :
    (cutComponentComplement H d K).Connected := by
  classical
  apply Subgraph.Connected.map H.hom
  rw [← connected_induce_iff]
  let W : Set H.verts := (ComponentEndBlock.side d K)ᶜ
  let J : SimpleGraph W := H.coe.induce W
  change J.Connected
  let dJ : W := ⟨d, ComponentEndBlock.cut_not_mem_side d K⟩
  have reaches_cut (u : W) : J.Reachable u dJ := by
    by_cases hud : u.1 = d
    · have hudJ : u = dJ := Subtype.ext hud
      simpa only [hudJ] using Reachable.refl dJ
    · let uDel : {w : H.verts // w ≠ d} := ⟨u.1, hud⟩
      let L : (deleteVertex H.coe d).ConnectedComponent :=
        (deleteVertex H.coe d).connectedComponentMk uDel
      have huL : u.1 ∈ ComponentEndBlock.side d L := by
        refine ⟨hud, ?_⟩
        simpa only [L, uDel, ConnectedComponent.mem_supp_iff,
          Subtype.coe_eta]
      have hLK : L ≠ K := by
        intro h
        apply u.2
        exact h ▸ huL
      have huEnd : u.1 ∈ ComponentEndBlock.verts d L := by
        rw [ComponentEndBlock.verts, Set.mem_insert_iff]
        exact Or.inr huL
      have hdEnd : d ∈ ComponentEndBlock.verts d L := by
        simp [ComponentEndBlock.verts]
      let uE : {w : H.verts //
          w ∈ ComponentEndBlock.verts d L} := ⟨u.1, huEnd⟩
      let dE : {w : H.verts //
          w ∈ ComponentEndBlock.verts d L} := ⟨d, hdEnd⟩
      obtain ⟨p, hp⟩ :=
        ((ComponentEndBlock.verts_connected hH.coe L) uE dE).exists_isPath
      let f : H.coe.induce (ComponentEndBlock.verts d L) →g J :=
        { toFun := fun w => ⟨w.1, by
            intro hwK
            have hwEnd := w.2
            change w.1 ∈ insert d (ComponentEndBlock.side d L) at hwEnd
            rw [Set.mem_insert_iff] at hwEnd
            rcases hwEnd with hwd | hwL
            · have hwKd : d ∈ ComponentEndBlock.side d K :=
                Eq.mp (congrArg
                  (fun q : H.verts ↦ q ∈ ComponentEndBlock.side d K) hwd) hwK
              exact ComponentEndBlock.cut_not_mem_side d K hwKd
            · exact Set.disjoint_left.mp
                (componentEndBlock_side_disjoint_of_ne hLK) hwL hwK⟩
          map_rel' := fun h => h }
      let q : J.Walk u dJ :=
        (p.map f).copy (Subtype.ext rfl) (Subtype.ext rfl)
      exact q.reachable
  refine { preconnected := ?_, nonempty := ⟨dJ⟩ }
  intro u v
  exact (reaches_cut u).trans (reaches_cut v).symm

/-- Vertex inclusion from the connector with one deleted-component side
removed back into the original connector. -/
def cutComponentComplementVertsEmbedding (H : G.Subgraph) (d : H.verts)
    (K : (deleteVertex H.coe d).ConnectedComponent) :
    (cutComponentComplement H d K).verts ↪ H.verts where
  toFun w := ⟨w.1, (cutComponentComplement_le H d K).1 w.2⟩
  inj' u v h := by
    apply Subtype.ext
    exact congrArg (fun w : H.verts ↦ w.1) h

/-- Inclusion after deleting corresponding vertices from the pruned
connector and the original connector. -/
def cutComponentComplementDeleteInclusion (H : G.Subgraph) (d : H.verts)
    (K : (deleteVertex H.coe d).ConnectedComponent)
    (p : (cutComponentComplement H d K).verts) :
    ((cutComponentComplement H d K).coe.induce
        (fun w : (cutComponentComplement H d K).verts ↦ w ≠ p)) →g
      (H.coe.induce
        (fun w : H.verts ↦
          w ≠ cutComponentComplementVertsEmbedding H d K p)) where
  toFun w := ⟨cutComponentComplementVertsEmbedding H d K w.1, by
    intro h
    apply w.2
    apply Subtype.ext
    exact congrArg (fun q : H.verts ↦ q.1) h⟩
  map_rel' h := (cutComponentComplement_le H d K).2 h

/-- Away from the retained cut vertex, collapse the removed component side
back to the cut vertex.  Edges crossing the removed side can meet the
retained connector only at that cut. -/
noncomputable def cutComponentComplementDeleteRetraction
    (H : G.Subgraph) (d : H.verts)
    (K : (deleteVertex H.coe d).ConnectedComponent)
    (p : (cutComponentComplement H d K).verts) (hpd : p.1 ≠ d.1) :
    {w : H.verts //
        w ≠ cutComponentComplementVertsEmbedding H d K p} →
      {w : (cutComponentComplement H d K).verts // w ≠ p} :=
  fun w ↦
    if hw : w.1.1 ∈ (cutComponentComplement H d K).verts then
      ⟨⟨w.1.1, hw⟩, by
        intro h
        apply w.2
        apply Subtype.ext
        exact congrArg
          (fun q : (cutComponentComplement H d K).verts ↦ q.1) h⟩
    else
      ⟨⟨d.1, cut_mem_cutComponentComplement H d K⟩, by
        intro h
        exact hpd (congrArg
          (fun q : (cutComponentComplement H d K).verts ↦ q.1) h).symm⟩

@[simp] theorem cutComponentComplementDeleteRetraction_inclusion
    (H : G.Subgraph) (d : H.verts)
    (K : (deleteVertex H.coe d).ConnectedComponent)
    (p : (cutComponentComplement H d K).verts) (hpd : p.1 ≠ d.1)
    (w : {q : (cutComponentComplement H d K).verts // q ≠ p}) :
    cutComponentComplementDeleteRetraction H d K p hpd
        (cutComponentComplementDeleteInclusion H d K p w) = w := by
  have hwComplement :
      (cutComponentComplementDeleteInclusion H d K p w).1.1 ∈
        (cutComponentComplement H d K).verts := w.1.2
  apply Subtype.ext
  apply Subtype.ext
  rw [cutComponentComplementDeleteRetraction, dif_pos hwComplement]
  rfl

/-- The complement-pruning retraction sends an original-connector edge to
either equality or an edge of the pruned connector. -/
theorem cutComponentComplementDeleteRetraction_adj_eq_or_adj
    (H : G.Subgraph) (d : H.verts)
    (K : (deleteVertex H.coe d).ConnectedComponent)
    (p : (cutComponentComplement H d K).verts) (hpd : p.1 ≠ d.1)
    {u v : {w : H.verts //
      w ≠ cutComponentComplementVertsEmbedding H d K p}}
    (huv : (H.coe.induce
      (fun w : H.verts ↦
        w ≠ cutComponentComplementVertsEmbedding H d K p)).Adj u v) :
    cutComponentComplementDeleteRetraction H d K p hpd u =
        cutComponentComplementDeleteRetraction H d K p hpd v ∨
      ((cutComponentComplement H d K).coe.induce
        (fun w : (cutComponentComplement H d K).verts ↦ w ≠ p)).Adj
          (cutComponentComplementDeleteRetraction H d K p hpd u)
          (cutComponentComplementDeleteRetraction H d K p hpd v) := by
  classical
  by_cases hu : u.1.1 ∈ (cutComponentComplement H d K).verts
  · by_cases hv : v.1.1 ∈ (cutComponentComplement H d K).verts
    · right
      simp only [cutComponentComplementDeleteRetraction,
        dif_pos hu, dif_pos hv]
      obtain ⟨_, huNotK⟩ :=
        (mem_cutComponentComplement_verts_iff H d K u.1.1).mp hu
      obtain ⟨_, hvNotK⟩ :=
        (mem_cutComponentComplement_verts_iff H d K v.1.1).mp hv
      apply (Subgraph.coeSubgraph_adj
        ((⊤ : H.coe.Subgraph).induce
          ((ComponentEndBlock.side d K)ᶜ)) u.1.1 v.1.1).2
      exact ⟨u.1.2, v.1.2, huNotK, hvNotK, huv⟩
    · have hvSide : v.1 ∈ ComponentEndBlock.side d K := by
        by_contra hvNotSide
        apply hv
        rw [mem_cutComponentComplement_verts_iff H d K v.1.1]
        exact ⟨v.1.2, by simpa only [Subtype.coe_eta] using hvNotSide⟩
      obtain ⟨_, huNotSide⟩ :=
        (mem_cutComponentComplement_verts_iff H d K u.1.1).mp hu
      have huEnd : u.1 ∈ ComponentEndBlock.verts d K :=
        ComponentEndBlock.neighborSet_subset_verts
          (G := H.coe) K hvSide huv.symm
      rw [ComponentEndBlock.verts, Set.mem_insert_iff] at huEnd
      rcases huEnd with hud | huSide
      · left
        apply Subtype.ext
        apply Subtype.ext
        simpa [cutComponentComplementDeleteRetraction, hu, hv] using
          congrArg Subtype.val hud
      · exact (huNotSide (by simpa only [Subtype.coe_eta] using huSide)).elim
  · by_cases hv : v.1.1 ∈ (cutComponentComplement H d K).verts
    · have huSide : u.1 ∈ ComponentEndBlock.side d K := by
        by_contra huNotSide
        apply hu
        rw [mem_cutComponentComplement_verts_iff H d K u.1.1]
        exact ⟨u.1.2, by simpa only [Subtype.coe_eta] using huNotSide⟩
      obtain ⟨_, hvNotSide⟩ :=
        (mem_cutComponentComplement_verts_iff H d K v.1.1).mp hv
      have hvEnd : v.1 ∈ ComponentEndBlock.verts d K :=
        ComponentEndBlock.neighborSet_subset_verts
          (G := H.coe) K huSide huv
      rw [ComponentEndBlock.verts, Set.mem_insert_iff] at hvEnd
      rcases hvEnd with hvd | hvSide
      · left
        apply Subtype.ext
        apply Subtype.ext
        simpa [cutComponentComplementDeleteRetraction, hu, hv] using
          (congrArg Subtype.val hvd).symm
      · exact (hvNotSide (by simpa only [Subtype.coe_eta] using hvSide)).elim
    · left
      apply Subtype.ext
      apply Subtype.ext
      simp [cutComponentComplementDeleteRetraction, hu, hv]

/-- At every retained vertex other than the restored cut vertex, pruning one
deleted-component side cannot increase the number of components after the
corresponding deletion. -/
theorem cutComponentComplementDelete_componentMap_injective
    (H : G.Subgraph) (d : H.verts)
    (K : (deleteVertex H.coe d).ConnectedComponent)
    (p : (cutComponentComplement H d K).verts) (hpd : p.1 ≠ d.1) :
    Function.Injective (fun C :
      ((cutComponentComplement H d K).coe.induce
        (fun w : (cutComponentComplement H d K).verts ↦ w ≠ p)).ConnectedComponent ↦
      C.map (cutComponentComplementDeleteInclusion H d K p)) := by
  intro C D
  refine ConnectedComponent.ind₂ (c := C) (d := D) ?_
  intro u v huv
  change
    (H.coe.induce
      (fun w : H.verts ↦
        w ≠ cutComponentComplementVertsEmbedding H d K p)).connectedComponentMk
        (cutComponentComplementDeleteInclusion H d K p u) =
      (H.coe.induce
        (fun w : H.verts ↦
          w ≠ cutComponentComplementVertsEmbedding H d K p)).connectedComponentMk
        (cutComponentComplementDeleteInclusion H d K p v) at huv
  apply ConnectedComponent.sound
  have hreach := SimpleGraph.Reachable.map_of_adj_eq_or_adj
    (J := H.coe.induce (fun w : H.verts ↦
      w ≠ cutComponentComplementVertsEmbedding H d K p))
    (K := (cutComponentComplement H d K).coe.induce
      (fun w : (cutComponentComplement H d K).verts ↦ w ≠ p))
    (cutComponentComplementDeleteRetraction H d K p hpd)
    (fun {_ _} huv' ↦
      cutComponentComplementDeleteRetraction_adj_eq_or_adj
        H d K p hpd huv')
    (ConnectedComponent.exact huv)
  simpa only [cutComponentComplementDeleteRetraction_inclusion] using hreach

theorem cutComponentComplement_delete_component_card_le
    (H : G.Subgraph) (d : H.verts)
    (K : (deleteVertex H.coe d).ConnectedComponent)
    (p : (cutComponentComplement H d K).verts) (hpd : p.1 ≠ d.1) :
    Fintype.card
        (((cutComponentComplement H d K).coe.induce
          (fun w : (cutComponentComplement H d K).verts ↦ w ≠ p)).ConnectedComponent) ≤
      Fintype.card
        ((H.coe.induce
          (fun w : H.verts ↦
            w ≠ cutComponentComplementVertsEmbedding H d K p)).ConnectedComponent) :=
  Fintype.card_le_of_injective
    (fun C ↦ C.map (cutComponentComplementDeleteInclusion H d K p))
    (cutComponentComplementDelete_componentMap_injective H d K p hpd)

/-- At the restored cut itself, the deletion inclusion has the original
deleted graph as codomain. -/
def cutComponentComplementCutDeleteInclusion (H : G.Subgraph) (d : H.verts)
    (K : (deleteVertex H.coe d).ConnectedComponent) :
    ((cutComponentComplement H d K).coe.induce
      (fun w : (cutComponentComplement H d K).verts ↦
        w ≠ ⟨d.1, cut_mem_cutComponentComplement H d K⟩)) →g
      (H.coe.induce fun w : H.verts ↦ w ≠ d) where
  toFun w := ⟨cutComponentComplementVertsEmbedding H d K w.1, by
    intro h
    apply w.2
    apply Subtype.ext
    exact congrArg (fun q : H.verts ↦ q.1) h⟩
  map_rel' h := (cutComponentComplement_le H d K).2 h

/-- Collapse the omitted deleted component onto a retained basepoint.  Since
distinct components of `H-d` have no edge between them, this is again a weak
graph retraction. -/
noncomputable def cutComponentComplementCutDeleteRetraction
    (H : G.Subgraph) (d : H.verts)
    (K : (deleteVertex H.coe d).ConnectedComponent)
    (b : {w : (cutComponentComplement H d K).verts //
      w ≠ ⟨d.1, cut_mem_cutComponentComplement H d K⟩}) :
    {w : H.verts // w ≠ d} →
      {w : (cutComponentComplement H d K).verts //
        w ≠ ⟨d.1, cut_mem_cutComponentComplement H d K⟩} :=
  fun w ↦
    if hw : w.1.1 ∈ (cutComponentComplement H d K).verts then
      ⟨⟨w.1.1, hw⟩, by
        intro h
        apply w.2
        apply Subtype.ext
        exact congrArg
          (fun q : (cutComponentComplement H d K).verts ↦ q.1) h⟩
    else b

@[simp] theorem cutComponentComplementCutDeleteRetraction_inclusion
    (H : G.Subgraph) (d : H.verts)
    (K : (deleteVertex H.coe d).ConnectedComponent)
    (b : {w : (cutComponentComplement H d K).verts //
      w ≠ ⟨d.1, cut_mem_cutComponentComplement H d K⟩})
    (w : {q : (cutComponentComplement H d K).verts //
      q ≠ ⟨d.1, cut_mem_cutComponentComplement H d K⟩}) :
    cutComponentComplementCutDeleteRetraction H d K b
        (cutComponentComplementCutDeleteInclusion H d K w) = w := by
  have hwComplement :
      (cutComponentComplementCutDeleteInclusion H d K w).1.1 ∈
        (cutComponentComplement H d K).verts := w.1.2
  apply Subtype.ext
  apply Subtype.ext
  rw [cutComponentComplementCutDeleteRetraction, dif_pos hwComplement]
  rfl

theorem cutComponentComplementCutDeleteRetraction_adj_eq_or_adj
    (H : G.Subgraph) (d : H.verts)
    (K : (deleteVertex H.coe d).ConnectedComponent)
    (b : {w : (cutComponentComplement H d K).verts //
      w ≠ ⟨d.1, cut_mem_cutComponentComplement H d K⟩})
    {u v : {w : H.verts // w ≠ d}}
    (huv : (H.coe.induce fun w : H.verts ↦ w ≠ d).Adj u v) :
    cutComponentComplementCutDeleteRetraction H d K b u =
        cutComponentComplementCutDeleteRetraction H d K b v ∨
      ((cutComponentComplement H d K).coe.induce
        (fun w : (cutComponentComplement H d K).verts ↦
          w ≠ ⟨d.1, cut_mem_cutComponentComplement H d K⟩)).Adj
          (cutComponentComplementCutDeleteRetraction H d K b u)
          (cutComponentComplementCutDeleteRetraction H d K b v) := by
  classical
  by_cases hu : u.1.1 ∈ (cutComponentComplement H d K).verts
  · by_cases hv : v.1.1 ∈ (cutComponentComplement H d K).verts
    · right
      simp only [cutComponentComplementCutDeleteRetraction,
        dif_pos hu, dif_pos hv]
      obtain ⟨_, huNotK⟩ :=
        (mem_cutComponentComplement_verts_iff H d K u.1.1).mp hu
      obtain ⟨_, hvNotK⟩ :=
        (mem_cutComponentComplement_verts_iff H d K v.1.1).mp hv
      apply (Subgraph.coeSubgraph_adj
        ((⊤ : H.coe.Subgraph).induce
          ((ComponentEndBlock.side d K)ᶜ)) u.1.1 v.1.1).2
      exact ⟨u.1.2, v.1.2, huNotK, hvNotK, huv⟩
    · have hvSide : v.1 ∈ ComponentEndBlock.side d K := by
        by_contra hvNotSide
        apply hv
        rw [mem_cutComponentComplement_verts_iff H d K v.1.1]
        exact ⟨v.1.2, by simpa only [Subtype.coe_eta] using hvNotSide⟩
      obtain ⟨_, huNotSide⟩ :=
        (mem_cutComponentComplement_verts_iff H d K u.1.1).mp hu
      have huEnd : u.1 ∈ ComponentEndBlock.verts d K :=
        ComponentEndBlock.neighborSet_subset_verts
          (G := H.coe) K hvSide huv.symm
      rw [ComponentEndBlock.verts, Set.mem_insert_iff] at huEnd
      rcases huEnd with hud | huSide
      · exact (u.2 hud).elim
      · exact (huNotSide (by simpa only [Subtype.coe_eta] using huSide)).elim
  · by_cases hv : v.1.1 ∈ (cutComponentComplement H d K).verts
    · have huSide : u.1 ∈ ComponentEndBlock.side d K := by
        by_contra huNotSide
        apply hu
        rw [mem_cutComponentComplement_verts_iff H d K u.1.1]
        exact ⟨u.1.2, by simpa only [Subtype.coe_eta] using huNotSide⟩
      obtain ⟨_, hvNotSide⟩ :=
        (mem_cutComponentComplement_verts_iff H d K v.1.1).mp hv
      have hvEnd : v.1 ∈ ComponentEndBlock.verts d K :=
        ComponentEndBlock.neighborSet_subset_verts
          (G := H.coe) K huSide huv
      rw [ComponentEndBlock.verts, Set.mem_insert_iff] at hvEnd
      rcases hvEnd with hvd | hvSide
      · exact (v.2 hvd).elim
      · exact (hvNotSide (by simpa only [Subtype.coe_eta] using hvSide)).elim
    · left
      simp [cutComponentComplementCutDeleteRetraction, hu, hv]

/-- A genuine cut has a retained vertex outside any one selected deleted
component, so the cut-deleted complement has a basepoint. -/
theorem cutComponentComplementCutDelete_nonempty
    (H : G.Subgraph) (d : H.verts)
    (K : (deleteVertex H.coe d).ConnectedComponent)
    (hd : IsCutVertex H.coe d) :
    Nonempty {w : (cutComponentComplement H d K).verts //
      w ≠ ⟨d.1, cut_mem_cutComponentComplement H d K⟩} := by
  classical
  have hone : 1 < Fintype.card
      (H.coe.induce fun w : H.verts ↦ w ≠ d).ConnectedComponent := by
    have htwo' := two_le_card_delete_components_of_isCutVertex H hd
    omega
  obtain ⟨L, hLK⟩ := Fintype.exists_ne_of_one_lt_card hone K
  obtain ⟨q, hqL⟩ := L.nonempty_supp
  have hqSideL : q.1 ∈ ComponentEndBlock.side d L := ⟨q.2, hqL⟩
  have hqNotSideK : q.1 ∉ ComponentEndBlock.side d K := by
    intro hqK
    exact Set.disjoint_left.mp
      (componentEndBlock_side_disjoint_of_ne hLK) hqSideL hqK
  have hqComplement : q.1.1 ∈ (cutComponentComplement H d K).verts := by
    rw [mem_cutComponentComplement_verts_iff H d K q.1.1]
    exact ⟨q.1.2, by simpa only [Subtype.coe_eta] using hqNotSideK⟩
  let qP : (cutComponentComplement H d K).verts :=
    ⟨q.1.1, hqComplement⟩
  refine ⟨⟨qP, ?_⟩⟩
  intro h
  apply q.2
  apply Subtype.ext
  exact congrArg
    (fun w : (cutComponentComplement H d K).verts ↦ w.1) h

/-- The cut-deleted component map is injective: collapse the omitted
component onto any retained basepoint and transport reachability back. -/
theorem cutComponentComplementCutDelete_componentMap_injective
    (H : G.Subgraph) (d : H.verts)
    (K : (deleteVertex H.coe d).ConnectedComponent)
    (b : {w : (cutComponentComplement H d K).verts //
      w ≠ ⟨d.1, cut_mem_cutComponentComplement H d K⟩}) :
    Function.Injective (fun C :
      ((cutComponentComplement H d K).coe.induce
        (fun w : (cutComponentComplement H d K).verts ↦
          w ≠ ⟨d.1, cut_mem_cutComponentComplement H d K⟩)).ConnectedComponent ↦
      C.map (cutComponentComplementCutDeleteInclusion H d K)) := by
  intro C D
  refine ConnectedComponent.ind₂ (c := C) (d := D) ?_
  intro u v huv
  change
    (H.coe.induce fun w : H.verts ↦ w ≠ d).connectedComponentMk
        (cutComponentComplementCutDeleteInclusion H d K u) =
      (H.coe.induce fun w : H.verts ↦ w ≠ d).connectedComponentMk
        (cutComponentComplementCutDeleteInclusion H d K v) at huv
  apply ConnectedComponent.sound
  have hreach := SimpleGraph.Reachable.map_of_adj_eq_or_adj
    (J := H.coe.induce fun w : H.verts ↦ w ≠ d)
    (K := (cutComponentComplement H d K).coe.induce
      (fun w : (cutComponentComplement H d K).verts ↦
        w ≠ ⟨d.1, cut_mem_cutComponentComplement H d K⟩))
    (cutComponentComplementCutDeleteRetraction H d K b)
    (fun {_ _} huv' ↦
      cutComponentComplementCutDeleteRetraction_adj_eq_or_adj
        H d K b huv')
    (ConnectedComponent.exact huv)
  simpa only [cutComponentComplementCutDeleteRetraction_inclusion] using hreach

/-- At the cut vertex itself, pruning one deleted component strictly lowers
the component count: inclusion is injective, and the omitted component `K`
is not in its image. -/
theorem cutComponentComplement_cut_component_card_lt
    (H : G.Subgraph) (d : H.verts)
    (K : (deleteVertex H.coe d).ConnectedComponent)
    (hd : IsCutVertex H.coe d) :
    Fintype.card
        (((cutComponentComplement H d K).coe.induce
          (fun w : (cutComponentComplement H d K).verts ↦
            w ≠ ⟨d.1, cut_mem_cutComponentComplement H d K⟩)).ConnectedComponent) <
      Fintype.card
        (H.coe.induce fun w : H.verts ↦ w ≠ d).ConnectedComponent := by
  classical
  let b := Classical.choice
    (cutComponentComplementCutDelete_nonempty H d K hd)
  let f := fun C :
      ((cutComponentComplement H d K).coe.induce
        (fun w : (cutComponentComplement H d K).verts ↦
          w ≠ ⟨d.1, cut_mem_cutComponentComplement H d K⟩)).ConnectedComponent ↦
    C.map (cutComponentComplementCutDeleteInclusion H d K)
  have hinj : Function.Injective f :=
    cutComponentComplementCutDelete_componentMap_injective H d K b
  have hnSurj : ¬Function.Surjective f := by
    intro hsurj
    obtain ⟨C, hC⟩ := hsurj K
    revert hC
    refine ConnectedComponent.ind (c := C) ?_
    intro u hC
    have hmk :
        (H.coe.induce fun w : H.verts ↦ w ≠ d).connectedComponentMk
            (cutComponentComplementCutDeleteInclusion H d K u) = K := by
      simpa only [f, ConnectedComponent.map_mk] using hC
    have huSupp :
        cutComponentComplementCutDeleteInclusion H d K u ∈
          (show (H.coe.induce fun w : H.verts ↦ w ≠ d).ConnectedComponent
            from K).supp := by
      exact (ConnectedComponent.mem_supp_iff
        (show (H.coe.induce fun w : H.verts ↦ w ≠ d).ConnectedComponent
          from K)
        (cutComponentComplementCutDeleteInclusion H d K u)).2 hmk
    have huSide :
        (cutComponentComplementCutDeleteInclusion H d K u).1 ∈
          ComponentEndBlock.side d K := by
      refine ⟨(cutComponentComplementCutDeleteInclusion H d K u).2, ?_⟩
      exact huSupp
    obtain ⟨huH, huNotSide⟩ :=
      (mem_cutComponentComplement_verts_iff H d K u.1.1).mp u.1.2
    apply huNotSide
    have heq :
        (cutComponentComplementCutDeleteInclusion H d K u).1 =
          (⟨u.1.1, huH⟩ : H.verts) := Subtype.ext rfl
    exact Eq.mp (congrArg
      (fun q : H.verts ↦ q ∈ ComponentEndBlock.side d K) heq) huSide
  exact Fintype.card_lt_of_injective_not_surjective f hinj hnSurj

theorem cutComponentComplement_cut_summand_lt
    (H : G.Subgraph) (d : H.verts)
    (K : (deleteVertex H.coe d).ConnectedComponent)
    (hd : IsCutVertex H.coe d) :
    Fintype.card
        (((cutComponentComplement H d K).coe.induce
          (fun w : (cutComponentComplement H d K).verts ↦
            w ≠ ⟨d.1, cut_mem_cutComponentComplement H d K⟩)).ConnectedComponent) - 1 <
      Fintype.card
        (H.coe.induce fun w : H.verts ↦ w ≠ d).ConnectedComponent - 1 := by
  have hcard := cutComponentComplement_cut_component_card_lt H d K hd
  let b := Classical.choice
    (cutComponentComplementCutDelete_nonempty H d K hd)
  have hpos : 0 < Fintype.card
      (((cutComponentComplement H d K).coe.induce
        (fun w : (cutComponentComplement H d K).verts ↦
          w ≠ ⟨d.1, cut_mem_cutComponentComplement H d K⟩)).ConnectedComponent) :=
    Fintype.card_pos_iff.mpr ⟨((cutComponentComplement H d K).coe.induce
      (fun w : (cutComponentComplement H d K).verts ↦
        w ≠ ⟨d.1, cut_mem_cutComponentComplement H d K⟩)).connectedComponentMk b⟩
  omega

/-- Removing one whole component side at a genuine cut vertex, while
retaining the cut and all other sides, strictly lowers the total AHT
cut-defect. -/
theorem connectorCutDefect_cutComponentComplement_lt
    (H : G.Subgraph) (d : H.verts)
    (K : (deleteVertex H.coe d).ConnectedComponent)
    (hd : IsCutVertex H.coe d) :
    connectorCutDefect (cutComponentComplement H d K) <
      connectorCutDefect H := by
  let f := cutComponentComplementVertsEmbedding H d K
  have hfcut :
      f ⟨d.1, cut_mem_cutComponentComplement H d K⟩ = d := by
    apply Subtype.ext
    rfl
  refine connectorCutDefect_lt_of_embedding
    (cutComponentComplement H d K) H f ?_
      ⟨d.1, cut_mem_cutComponentComplement H d K⟩ ?_
  · intro p
    by_cases hpd : p.1 = d.1
    · have hp : p =
          ⟨d.1, cut_mem_cutComponentComplement H d K⟩ :=
        Subtype.ext hpd
      subst p
      have hstrict := cutComponentComplement_cut_summand_lt H d K hd
      rw [hfcut]
      exact Nat.le_of_lt hstrict
    · have hcard := cutComponentComplement_delete_component_card_le
        H d K p hpd
      simpa only [f, cutComponentComplementVertsEmbedding] using
        (Nat.sub_le_sub_right hcard 1)
  ·
    rw [hfcut]
    exact cutComponentComplement_cut_summand_lt H d K hd

/-- Minimality forbids an attachment-free component on the `A` side of a
connector cut: delete that whole component, retain the cut and every other
component, and use the strict complement-pruning defect inequality. -/
theorem MinimalABConnectorPair.false_of_A_attachment_free_cutComponent
    (C : M.MinimalABConnectorPair) (d : C.aGraph.verts)
    (K : (deleteVertex C.aGraph.coe d).ConnectedComponent)
    (hd : IsCutVertex C.aGraph.coe d)
    (hfree : ∀ a (ha : a ∈ M.aSet),
      (⟨a, C.a_contains a ha⟩ : C.aGraph.verts) ∉
        ComponentEndBlock.side d K) : False := by
  let A' := cutComponentComplement C.aGraph d K
  have hconnected : A'.Connected :=
    cutComponentComplement_connected C.aGraph C.a_connected d K
  have hcontains : ∀ a ∈ M.aSet, a ∈ A'.verts := by
    intro a ha
    rw [mem_cutComponentComplement_verts_iff C.aGraph d K a]
    exact ⟨C.a_contains a ha, hfree a ha⟩
  have hdisjoint : Disjoint A'.verts C.bGraph.verts := by
    rw [Set.disjoint_left]
    intro w hwA hwB
    exact Set.disjoint_left.mp C.vertex_disjoint
      ((cutComponentComplement_le C.aGraph d K).1 hwA) hwB
  have havoids : Disjoint (A'.verts ∪ C.bGraph.verts)
      ((M.xPart : Set V) ∪ (M.yPart : Set V) ∪ (M.zPart : Set V)) := by
    rw [Set.disjoint_left]
    intro w hwGraphs hwPart
    apply Set.disjoint_left.mp C.avoids_terminal_parts
    · rcases hwGraphs with hwA | hwB
      · exact Or.inl ((cutComponentComplement_le C.aGraph d K).1 hwA)
      · exact Or.inr hwB
    · exact hwPart
  have hmin :=
    MinimalABConnectorPair.cutDefect_aGraph_le_of_replaceA
      (M := M) C A' hconnected hcontains hdisjoint havoids
  have hstrict := connectorCutDefect_cutComponentComplement_lt
    C.aGraph d K hd
  exact (Nat.not_lt_of_ge hmin) hstrict

/-- Symmetric attachment-free component pruning on the `B` connector. -/
theorem MinimalABConnectorPair.false_of_B_attachment_free_cutComponent
    (C : M.MinimalABConnectorPair) (d : C.bGraph.verts)
    (K : (deleteVertex C.bGraph.coe d).ConnectedComponent)
    (hd : IsCutVertex C.bGraph.coe d)
    (hfree : ∀ b (hb : b ∈ M.bSet),
      (⟨b, C.b_contains b hb⟩ : C.bGraph.verts) ∉
        ComponentEndBlock.side d K) : False := by
  let B' := cutComponentComplement C.bGraph d K
  have hconnected : B'.Connected :=
    cutComponentComplement_connected C.bGraph C.b_connected d K
  have hcontains : ∀ b ∈ M.bSet, b ∈ B'.verts := by
    intro b hb
    rw [mem_cutComponentComplement_verts_iff C.bGraph d K b]
    exact ⟨C.b_contains b hb, hfree b hb⟩
  have hdisjoint : Disjoint C.aGraph.verts B'.verts := by
    rw [Set.disjoint_left]
    intro w hwA hwB
    exact Set.disjoint_left.mp C.vertex_disjoint hwA
      ((cutComponentComplement_le C.bGraph d K).1 hwB)
  have havoids : Disjoint (C.aGraph.verts ∪ B'.verts)
      ((M.xPart : Set V) ∪ (M.yPart : Set V) ∪ (M.zPart : Set V)) := by
    rw [Set.disjoint_left]
    intro w hwGraphs hwPart
    apply Set.disjoint_left.mp C.avoids_terminal_parts
    · rcases hwGraphs with hwA | hwB
      · exact Or.inl hwA
      · exact Or.inr ((cutComponentComplement_le C.bGraph d K).1 hwB)
    · exact hwPart
  have hmin :=
    MinimalABConnectorPair.cutDefect_bGraph_le_of_replaceB
      (M := M) C B' hconnected hcontains hdisjoint havoids
  have hstrict := connectorCutDefect_cutComponentComplement_lt
    C.bGraph d K hd
  exact (Nat.not_lt_of_ge hmin) hstrict

/-- A separator is contradicted by any connected subgraph which contains a
chosen source and target but omits the alleged singleton cut.  This small
adapter keeps the repeated subtype maps in the connector-cut analysis local. -/
theorem false_of_separator_of_connected_subgraph
    (H R : G.Subgraph) (hR : R.Connected) (hsub : R ≤ H)
    {A B : Set H.verts} {s t u : H.verts}
    (hsA : s ∈ A) (htB : t ∈ B)
    (hsR : s.1 ∈ R.verts) (htR : t.1 ∈ R.verts)
    (huR : u.1 ∉ R.verts)
    (hsep : Erdos599.Countable.Separates H.coe A B ({u} : Set H.verts)) : False := by
  let sR : R.verts := ⟨s.1, hsR⟩
  let tR : R.verts := ⟨t.1, htR⟩
  obtain ⟨q, hq⟩ := (hR.coe sR tR).exists_isPath
  let inc : R.coe →g H.coe := Subgraph.inclusion hsub
  let p₀ := q.map inc
  let p : H.coe.Walk s t := p₀.copy (Subtype.ext rfl) (Subtype.ext rfl)
  have hinc : Function.Injective inc := by
    intro a b hab
    apply Subtype.ext
    change a.1 = b.1
    exact congrArg (fun w : H.verts ↦ w.1) hab
  have hp : p.IsPath := by
    exact (Walk.isPath_copy p₀ (Subtype.ext rfl) (Subtype.ext rfl)).2
      (hq.map hinc)
  obtain ⟨v, hvp, hvu⟩ := hsep s hsA t htB p hp
  have hvEq : v = u := by simpa only [Set.mem_singleton_iff] using hvu
  subst v
  have huP₀ : u ∈ p₀.support := by
    simpa only [p, Walk.support_copy] using hvp
  rw [Walk.support_map] at huP₀
  obtain ⟨w, -, hwu⟩ := List.mem_map.mp huP₀
  apply huR
  have hval : w.1 = u.1 := congrArg Subtype.val hwu
  rw [← hval]
  exact w.2

/-- Two vertices in the same component after deleting `u` give a path which
avoids `u`, and hence refute a claimed singleton separator. -/
theorem false_of_separator_of_same_delete_component
    (H : G.Subgraph) {A B : Set H.verts} {s t u : H.verts}
    (hsA : s ∈ A) (htB : t ∈ B) (hsu : s ≠ u) (htu : t ≠ u)
    (hcomp : (deleteVertex H.coe u).connectedComponentMk ⟨s, hsu⟩ =
      (deleteVertex H.coe u).connectedComponentMk ⟨t, htu⟩)
    (hsep : Erdos599.Countable.Separates H.coe A B ({u} : Set H.verts)) : False := by
  obtain ⟨q, hq⟩ := (ConnectedComponent.exact hcomp).exists_isPath
  let inc := (SimpleGraph.Embedding.induce
    (G := H.coe) (s := {w : H.verts | w ≠ u})).toHom
  let p₀ := q.map inc
  let p : H.coe.Walk s t := p₀.copy (Subtype.ext rfl) (Subtype.ext rfl)
  have hp : p.IsPath := by
    exact (Walk.isPath_copy p₀ (Subtype.ext rfl) (Subtype.ext rfl)).2
      (hq.map Subtype.val_injective)
  obtain ⟨v, hvp, hvu⟩ := hsep s hsA t htB p hp
  have hvEq : v = u := by simpa only [Set.mem_singleton_iff] using hvu
  subst v
  have huP₀ : u ∈ p₀.support := by
    simpa only [p, Walk.support_copy] using hvp
  change u ∈ (q.map inc).support at huP₀
  have hsupp : (q.map inc).support = q.support.map inc := by
    convert (Walk.support_map (p := q) (f := inc)) using 1 <;> rfl
  rw [hsupp] at huP₀
  obtain ⟨w, -, hwu⟩ := List.mem_map.mp huP₀
  exact w.2 hwu

/-- If three vertices all avoid `d` but do not all lie in any one end piece
at `d`, one of their three component sides isolates that vertex from the
other two.  The disjunction records the harmless relabelling denoted
"without loss of generality" in the paper. -/
theorem exists_isolatingCutSide_of_avoid_cut
    {H : G.Subgraph} {a b c d : H.verts}
    (had : a ≠ d) (hbd : b ≠ d) (hcd : c ≠ d)
    (hnoAll : ∀ K : (deleteVertex H.coe d).ConnectedComponent,
      ¬(a ∈ ComponentEndBlock.verts d K ∧
        b ∈ ComponentEndBlock.verts d K ∧
        c ∈ ComponentEndBlock.verts d K)) :
    Nonempty (IsolatingCutSide H a b c) ∨
      Nonempty (IsolatingCutSide H b a c) ∨
      Nonempty (IsolatingCutSide H c a b) := by
  classical
  let a' : {w : H.verts // w ≠ d} := ⟨a, had⟩
  let Ka : (deleteVertex H.coe d).ConnectedComponent :=
    (deleteVertex H.coe d).connectedComponentMk a'
  have haKa : a ∈ ComponentEndBlock.side d Ka := by
    refine ⟨had, ?_⟩
    simpa only [a', Ka, Subtype.coe_eta] using
      ((ConnectedComponent.mem_supp_iff Ka a').2 rfl)
  by_cases hbKa : b ∈ ComponentEndBlock.side d Ka
  · by_cases hcKa : c ∈ ComponentEndBlock.side d Ka
    · exfalso
      exact hnoAll Ka ⟨
        Set.mem_insert_iff.mpr (Or.inr haKa),
        Set.mem_insert_iff.mpr (Or.inr hbKa),
        Set.mem_insert_iff.mpr (Or.inr hcKa)⟩
    · let c' : {w : H.verts // w ≠ d} := ⟨c, hcd⟩
      let Kc : (deleteVertex H.coe d).ConnectedComponent :=
        (deleteVertex H.coe d).connectedComponentMk c'
      have hcKc : c ∈ ComponentEndBlock.side d Kc := by
        refine ⟨hcd, ?_⟩
        simpa only [c', Kc, Subtype.coe_eta] using
          ((ConnectedComponent.mem_supp_iff Kc c').2 rfl)
      have hKcKa : Kc ≠ Ka := by
        intro heq
        apply hcKa
        simpa only [heq] using hcKc
      have hdis := componentEndBlock_side_disjoint_of_ne (G := G) hKcKa
      right
      right
      exact ⟨{
        cut := d
        component := Kc
        a_mem := hcKc
        b_not_mem := fun haKc ↦
          Set.disjoint_left.mp hdis haKc haKa
        c_not_mem := fun hbKc ↦
          Set.disjoint_left.mp hdis hbKc hbKa }⟩
  · by_cases hcKa : c ∈ ComponentEndBlock.side d Ka
    · let b' : {w : H.verts // w ≠ d} := ⟨b, hbd⟩
      let Kb : (deleteVertex H.coe d).ConnectedComponent :=
        (deleteVertex H.coe d).connectedComponentMk b'
      have hbKb : b ∈ ComponentEndBlock.side d Kb := by
        refine ⟨hbd, ?_⟩
        simpa only [b', Kb, Subtype.coe_eta] using
          ((ConnectedComponent.mem_supp_iff Kb b').2 rfl)
      have hKbKa : Kb ≠ Ka := by
        intro heq
        apply hbKa
        simpa only [heq] using hbKb
      have hdis := componentEndBlock_side_disjoint_of_ne (G := G) hKbKa
      right
      left
      exact ⟨{
        cut := d
        component := Kb
        a_mem := hbKb
        b_not_mem := fun haKb ↦
          Set.disjoint_left.mp hdis haKb haKa
        c_not_mem := fun hcKb ↦
          Set.disjoint_left.mp hdis hcKb hcKa }⟩
    · left
      exact ⟨{
        cut := d
        component := Ka
        a_mem := haKa
        b_not_mem := hbKa
        c_not_mem := hcKa }⟩

/-- Version of `exists_isolatingCutSide_of_avoid_cut` allowing the cut
vertex itself to be one of the three attachments.  Pairwise distinctness
then leaves two attachments off the cut, and the no-common-end-piece
hypothesis forces their component sides to be distinct. -/
theorem exists_isolatingCutSide_of_not_all_mem_verts
    {H : G.Subgraph} {a b c d : H.verts}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hnoAll : ∀ K : (deleteVertex H.coe d).ConnectedComponent,
      ¬(a ∈ ComponentEndBlock.verts d K ∧
        b ∈ ComponentEndBlock.verts d K ∧
        c ∈ ComponentEndBlock.verts d K)) :
    Nonempty (IsolatingCutSide H a b c) ∨
      Nonempty (IsolatingCutSide H b a c) ∨
      Nonempty (IsolatingCutSide H c a b) := by
  classical
  by_cases had : a = d
  · have hbd : b ≠ d := fun h ↦ hab (had.trans h.symm)
    have hcd : c ≠ d := fun h ↦ hac (had.trans h.symm)
    let b' : {w : H.verts // w ≠ d} := ⟨b, hbd⟩
    let Kb : (deleteVertex H.coe d).ConnectedComponent :=
      (deleteVertex H.coe d).connectedComponentMk b'
    have hbKb : b ∈ ComponentEndBlock.side d Kb := by
      refine ⟨hbd, ?_⟩
      simpa only [b', Kb, Subtype.coe_eta] using
        ((ConnectedComponent.mem_supp_iff Kb b').2 rfl)
    have hcKb : c ∉ ComponentEndBlock.side d Kb := by
      intro hc
      apply hnoAll Kb
      exact ⟨by
          rw [ComponentEndBlock.verts, had]
          exact Set.mem_insert d (ComponentEndBlock.side d Kb),
        Set.mem_insert_iff.mpr (Or.inr hbKb),
        Set.mem_insert_iff.mpr (Or.inr hc)⟩
    right
    left
    exact ⟨{
      cut := d
      component := Kb
      a_mem := hbKb
      b_not_mem := by
        intro ha
        exact ComponentEndBlock.cut_not_mem_side d Kb (had ▸ ha)
      c_not_mem := hcKb }⟩
  · by_cases hbdEq : b = d
    · have hcd : c ≠ d := fun h ↦ hbc (hbdEq.trans h.symm)
      let a' : {w : H.verts // w ≠ d} := ⟨a, had⟩
      let Ka : (deleteVertex H.coe d).ConnectedComponent :=
        (deleteVertex H.coe d).connectedComponentMk a'
      have haKa : a ∈ ComponentEndBlock.side d Ka := by
        exact ⟨had, (ConnectedComponent.mem_supp_iff Ka ⟨a, had⟩).2 rfl⟩
      have hcKa : c ∉ ComponentEndBlock.side d Ka := by
        intro hc
        apply hnoAll Ka
        exact ⟨Set.mem_insert_iff.mpr (Or.inr haKa),
          by
            rw [ComponentEndBlock.verts, hbdEq]
            exact Set.mem_insert d (ComponentEndBlock.side d Ka),
          Set.mem_insert_iff.mpr (Or.inr hc)⟩
      left
      exact ⟨{
        cut := d
        component := Ka
        a_mem := haKa
        b_not_mem := by
          intro hb
          exact ComponentEndBlock.cut_not_mem_side d Ka (hbdEq ▸ hb)
        c_not_mem := hcKa }⟩
    · by_cases hcdEq : c = d
      · let a' : {w : H.verts // w ≠ d} := ⟨a, had⟩
        let Ka : (deleteVertex H.coe d).ConnectedComponent :=
          (deleteVertex H.coe d).connectedComponentMk a'
        have haKa : a ∈ ComponentEndBlock.side d Ka := by
          refine ⟨had, ?_⟩
          simpa only [a', Ka, Subtype.coe_eta] using
            ((ConnectedComponent.mem_supp_iff Ka a').2 rfl)
        have hbKa : b ∉ ComponentEndBlock.side d Ka := by
          intro hb
          apply hnoAll Ka
          exact ⟨Set.mem_insert_iff.mpr (Or.inr haKa),
            Set.mem_insert_iff.mpr (Or.inr hb),
            by
              rw [ComponentEndBlock.verts, hcdEq]
              exact Set.mem_insert d (ComponentEndBlock.side d Ka)⟩
        left
        exact ⟨{
          cut := d
          component := Ka
          a_mem := haKa
          b_not_mem := hbKa
          c_not_mem := by
            intro hc
            exact ComponentEndBlock.cut_not_mem_side d Ka (hcdEq ▸ hc) }⟩
      · exact exists_isolatingCutSide_of_avoid_cut
          (G := G) had hbdEq hcdEq hnoAll

/-- At a cut vertex of a minimal `A` connector, some attachment lies in a
component side which contains neither of the other two attachments.  The
strict pruning theorem rules out the only alternative. -/
theorem MinimalABConnectorPair.exists_isolating_A_of_cut
    (C : M.MinimalABConnectorPair) (hA : M.aSet.card = 3)
    (d : C.aGraph.verts) (hd : IsCutVertex C.aGraph.coe d) :
    Nonempty (IsolatingCutSide C.aGraph
      (ABConnectorPair.xAIn (M := M) C.toABConnectorPair)
      (ABConnectorPair.yAIn (M := M) C.toABConnectorPair)
      (ABConnectorPair.zAIn (M := M) C.toABConnectorPair)) ∨
    Nonempty (IsolatingCutSide C.aGraph
      (ABConnectorPair.yAIn (M := M) C.toABConnectorPair)
      (ABConnectorPair.xAIn (M := M) C.toABConnectorPair)
      (ABConnectorPair.zAIn (M := M) C.toABConnectorPair)) ∨
    Nonempty (IsolatingCutSide C.aGraph
      (ABConnectorPair.zAIn (M := M) C.toABConnectorPair)
      (ABConnectorPair.xAIn (M := M) C.toABConnectorPair)
      (ABConnectorPair.yAIn (M := M) C.toABConnectorPair)) := by
  have hxy : M.xSep.left ≠ M.ySep.left := by
    intro h
    have hsub : M.aSet ⊆ ({M.ySep.left, M.zSep.left} : Finset V) := by
      intro w hw
      simpa [aSet, h] using hw
    have hle := Finset.card_le_card hsub
    have htwo : ({M.ySep.left, M.zSep.left} : Finset V).card ≤ 2 :=
      Finset.card_insert_le _ _
    omega
  have hxz : M.xSep.left ≠ M.zSep.left := by
    intro h
    have hsub : M.aSet ⊆ ({M.ySep.left, M.zSep.left} : Finset V) := by
      intro w hw
      simpa [aSet, h] using hw
    have hle := Finset.card_le_card hsub
    have htwo : ({M.ySep.left, M.zSep.left} : Finset V).card ≤ 2 :=
      Finset.card_insert_le _ _
    omega
  have hyz : M.ySep.left ≠ M.zSep.left := by
    intro h
    have hsub : M.aSet ⊆ ({M.xSep.left, M.zSep.left} : Finset V) := by
      intro w hw
      simpa [aSet, h] using hw
    have hle := Finset.card_le_card hsub
    have htwo : ({M.xSep.left, M.zSep.left} : Finset V).card ≤ 2 :=
      Finset.card_insert_le _ _
    omega
  apply exists_isolatingCutSide_of_not_all_mem_verts
  · exact fun h ↦ hxy (congrArg Subtype.val h)
  · exact fun h ↦ hxz (congrArg Subtype.val h)
  · exact fun h ↦ hyz (congrArg Subtype.val h)
  · intro K hAll
    apply (C.not_all_A_in_prunable_piece (M := M) d K
      (connectorCutDefect_cutComponentPiece_lt C.aGraph d K hd))
    intro a ha
    have ha' : a = M.xSep.left ∨ a = M.ySep.left ∨
        a = M.zSep.left := by
      simpa [aSet] using ha
    rcases ha' with rfl | rfl | rfl
    · rw [mem_cutComponentPiece_verts_iff]
      exact ⟨(ABConnectorPair.xAIn (M := M) C.toABConnectorPair).2, by
        simpa [ABConnectorPair.xAIn] using hAll.1⟩
    · rw [mem_cutComponentPiece_verts_iff]
      exact ⟨(ABConnectorPair.yAIn (M := M) C.toABConnectorPair).2, by
        simpa [ABConnectorPair.yAIn] using hAll.2.1⟩
    · rw [mem_cutComponentPiece_verts_iff]
      exact ⟨(ABConnectorPair.zAIn (M := M) C.toABConnectorPair).2, by
        simpa [ABConnectorPair.zAIn] using hAll.2.2⟩

/-- Symmetric isolating-side extraction for a cut vertex of the minimal
`B` connector. -/
theorem MinimalABConnectorPair.exists_isolating_B_of_cut
    (C : M.MinimalABConnectorPair) (hB : M.bSet.card = 3)
    (d : C.bGraph.verts) (hd : IsCutVertex C.bGraph.coe d) :
    Nonempty (IsolatingCutSide C.bGraph
      (ABConnectorPair.xBIn (M := M) C.toABConnectorPair)
      (ABConnectorPair.yBIn (M := M) C.toABConnectorPair)
      (ABConnectorPair.zBIn (M := M) C.toABConnectorPair)) ∨
    Nonempty (IsolatingCutSide C.bGraph
      (ABConnectorPair.yBIn (M := M) C.toABConnectorPair)
      (ABConnectorPair.xBIn (M := M) C.toABConnectorPair)
      (ABConnectorPair.zBIn (M := M) C.toABConnectorPair)) ∨
    Nonempty (IsolatingCutSide C.bGraph
      (ABConnectorPair.zBIn (M := M) C.toABConnectorPair)
      (ABConnectorPair.xBIn (M := M) C.toABConnectorPair)
      (ABConnectorPair.yBIn (M := M) C.toABConnectorPair)) := by
  have hxy : M.xSep.right ≠ M.ySep.right := by
    intro h
    have hsub : M.bSet ⊆ ({M.ySep.right, M.zSep.right} : Finset V) := by
      intro w hw
      simpa [bSet, h] using hw
    have hle := Finset.card_le_card hsub
    have htwo : ({M.ySep.right, M.zSep.right} : Finset V).card ≤ 2 :=
      Finset.card_insert_le _ _
    omega
  have hxz : M.xSep.right ≠ M.zSep.right := by
    intro h
    have hsub : M.bSet ⊆ ({M.ySep.right, M.zSep.right} : Finset V) := by
      intro w hw
      simpa [bSet, h] using hw
    have hle := Finset.card_le_card hsub
    have htwo : ({M.ySep.right, M.zSep.right} : Finset V).card ≤ 2 :=
      Finset.card_insert_le _ _
    omega
  have hyz : M.ySep.right ≠ M.zSep.right := by
    intro h
    have hsub : M.bSet ⊆ ({M.xSep.right, M.zSep.right} : Finset V) := by
      intro w hw
      simpa [bSet, h] using hw
    have hle := Finset.card_le_card hsub
    have htwo : ({M.xSep.right, M.zSep.right} : Finset V).card ≤ 2 :=
      Finset.card_insert_le _ _
    omega
  apply exists_isolatingCutSide_of_not_all_mem_verts
  · exact fun h ↦ hxy (congrArg Subtype.val h)
  · exact fun h ↦ hxz (congrArg Subtype.val h)
  · exact fun h ↦ hyz (congrArg Subtype.val h)
  · intro K hAll
    apply (C.not_all_B_in_prunable_piece (M := M) d K
      (connectorCutDefect_cutComponentPiece_lt C.bGraph d K hd))
    intro b hb
    have hb' : b = M.xSep.right ∨ b = M.ySep.right ∨
        b = M.zSep.right := by
      simpa [bSet] using hb
    rcases hb' with rfl | rfl | rfl
    · rw [mem_cutComponentPiece_verts_iff]
      exact ⟨(ABConnectorPair.xBIn (M := M) C.toABConnectorPair).2, by
        simpa [ABConnectorPair.xBIn] using hAll.1⟩
    · rw [mem_cutComponentPiece_verts_iff]
      exact ⟨(ABConnectorPair.yBIn (M := M) C.toABConnectorPair).2, by
        simpa [ABConnectorPair.yBIn] using hAll.2.1⟩
    · rw [mem_cutComponentPiece_verts_iff]
      exact ⟨(ABConnectorPair.zBIn (M := M) C.toABConnectorPair).2, by
        simpa [ABConnectorPair.zBIn] using hAll.2.2⟩

/-- The finite carrier of an isolating component side. -/
noncomputable def IsolatingCutSide.carrier {H : G.Subgraph}
    {a b c : H.verts} (S : IsolatingCutSide H a b c) : Finset H.verts :=
  (ComponentEndBlock.side S.cut S.component).toFinset

@[simp] theorem IsolatingCutSide.mem_carrier_iff {H : G.Subgraph}
    {a b c : H.verts} (S : IsolatingCutSide H a b c) (w : H.verts) :
    w ∈ S.carrier ↔ w ∈ ComponentEndBlock.side S.cut S.component := by
  simp [IsolatingCutSide.carrier]

/-- The same finite component side, with subgraph subtype information
forgotten. -/
noncomputable def IsolatingCutSide.ambientCarrier {H : G.Subgraph}
    {a b c : H.verts} (S : IsolatingCutSide H a b c) : Finset V :=
  S.carrier.image Subtype.val

@[simp] theorem IsolatingCutSide.mem_ambientCarrier_iff {H : G.Subgraph}
    {a b c : H.verts} (S : IsolatingCutSide H a b c) (w : V) :
    w ∈ S.ambientCarrier ↔
      ∃ hw : w ∈ H.verts,
        (⟨w, hw⟩ : H.verts) ∈
          ComponentEndBlock.side S.cut S.component := by
  constructor
  · intro hw
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hw
    exact ⟨u.2, (S.mem_carrier_iff u).mp hu⟩
  · rintro ⟨hwH, hwSide⟩
    apply Finset.mem_image.mpr
    exact ⟨⟨w, hwH⟩, (S.mem_carrier_iff _).mpr hwSide, rfl⟩

theorem IsolatingCutSide.ambientCarrier_subset {H : G.Subgraph}
    {a b c : H.verts} (S : IsolatingCutSide H a b c) :
    (S.ambientCarrier : Set V) ⊆ H.verts := by
  intro w hw
  exact ((S.mem_ambientCarrier_iff w).mp hw).1

/-- An isolating side for two distinct excluded vertices is based at a
genuine cut vertex.  At least one excluded vertex survives deletion of the
cut and lies in a different component from the isolated vertex. -/
theorem IsolatingCutSide.isCutVertex {H : G.Subgraph}
    {a b c : H.verts} (S : IsolatingCutSide H a b c) (hbc : b ≠ c) :
    IsCutVertex H.coe S.cut := by
  intro hpre
  by_cases hb : b = S.cut
  · have hc : c ≠ S.cut := by
      intro hc
      exact hbc (hb.trans hc.symm)
    have hreach := hpre
      (⟨a, S.a_mem.1⟩ : {w : H.verts // w ≠ S.cut})
      (⟨c, hc⟩ : {w : H.verts // w ≠ S.cut})
    have hcomp := ConnectedComponent.sound hreach
    apply S.c_not_mem
    refine ⟨hc, ?_⟩
    have haComp :
        (deleteVertex H.coe S.cut).connectedComponentMk
            (⟨a, S.a_mem.1⟩ : {w : H.verts // w ≠ S.cut}) = S.component := by
      simpa only [ConnectedComponent.mem_supp_iff] using S.a_mem.2
    simpa only [ConnectedComponent.mem_supp_iff] using hcomp.symm.trans haComp
  · have hreach := hpre
      (⟨a, S.a_mem.1⟩ : {w : H.verts // w ≠ S.cut})
      (⟨b, hb⟩ : {w : H.verts // w ≠ S.cut})
    have hcomp := ConnectedComponent.sound hreach
    apply S.b_not_mem
    refine ⟨hb, ?_⟩
    have haComp :
        (deleteVertex H.coe S.cut).connectedComponentMk
            (⟨a, S.a_mem.1⟩ : {w : H.verts // w ≠ S.cut}) = S.component := by
      simpa only [ConnectedComponent.mem_supp_iff] using S.a_mem.2
    simpa only [ConnectedComponent.mem_supp_iff] using hcomp.symm.trans haComp

@[simp] theorem IsolatingCutSide.a_mem_ambientCarrier {H : G.Subgraph}
    {a b c : H.verts} (S : IsolatingCutSide H a b c) :
    a.1 ∈ S.ambientCarrier := by
  exact (S.mem_ambientCarrier_iff a.1).mpr ⟨a.2, S.a_mem⟩

@[simp] theorem IsolatingCutSide.b_not_mem_ambientCarrier
    {H : G.Subgraph} {a b c : H.verts}
    (S : IsolatingCutSide H a b c) : b.1 ∉ S.ambientCarrier := by
  intro h
  obtain ⟨hb, hbSide⟩ := (S.mem_ambientCarrier_iff b.1).mp h
  exact S.b_not_mem (by simpa using hbSide)

@[simp] theorem IsolatingCutSide.c_not_mem_ambientCarrier
    {H : G.Subgraph} {a b c : H.verts}
    (S : IsolatingCutSide H a b c) : c.1 ∉ S.ambientCarrier := by
  intro h
  obtain ⟨hc, hcSide⟩ := (S.mem_ambientCarrier_iff c.1).mp h
  exact S.c_not_mem (by simpa using hcSide)

@[simp] theorem IsolatingCutSide.cut_not_mem_ambientCarrier
    {H : G.Subgraph} {a b c : H.verts}
    (S : IsolatingCutSide H a b c) : S.cut.1 ∉ S.ambientCarrier := by
  intro h
  obtain ⟨hcut, hside⟩ := (S.mem_ambientCarrier_iff S.cut.1).mp h
  exact hside.1 (Subtype.ext rfl)

/-- If the cut of a second isolating side lies outside the first endblock,
then the entire first carrier and its old cut lie in the second component.
The old cut is not in the old carrier, so the second carrier is strictly
larger. -/
theorem IsolatingCutSide.carrier_ssubset_of_cut_not_mem_endBlock
    {H : G.Subgraph} {a b c : H.verts}
    (hH : H.Connected) (S R : IsolatingCutSide H a b c)
    (hcut : R.cut ∉ ComponentEndBlock.verts S.cut S.component) :
    S.carrier ⊂ R.carrier := by
  classical
  have lift_mem (w : H.verts)
      (hw : w ∈ ComponentEndBlock.verts S.cut S.component) :
      w ∈ ComponentEndBlock.side R.cut R.component := by
    have hwCut : w ≠ R.cut := by
      intro h
      exact hcut (h ▸ hw)
    have haEnd : a ∈ ComponentEndBlock.verts S.cut S.component := by
      rw [ComponentEndBlock.verts, Set.mem_insert_iff]
      exact Or.inr S.a_mem
    have haCut : a ≠ R.cut := R.a_mem.1
    let aE : {v : H.verts //
        v ∈ ComponentEndBlock.verts S.cut S.component} := ⟨a, haEnd⟩
    let wE : {v : H.verts //
        v ∈ ComponentEndBlock.verts S.cut S.component} := ⟨w, hw⟩
    obtain ⟨q, hq⟩ :=
      ((ComponentEndBlock.verts_connected hH.coe S.component) aE wE).exists_isPath
    let f : H.coe.induce (ComponentEndBlock.verts S.cut S.component) →g
        deleteVertex H.coe R.cut :=
      { toFun := fun v => ⟨v.1, by
          intro h
          exact hcut (h ▸ v.2)⟩
        map_rel' := fun h => h }
    have hreach : (deleteVertex H.coe R.cut).Reachable
        ⟨a, haCut⟩ ⟨w, hwCut⟩ := by
      let q' : (deleteVertex H.coe R.cut).Walk
          ⟨a, haCut⟩ ⟨w, hwCut⟩ :=
        (q.map f).copy (Subtype.ext rfl) (Subtype.ext rfl)
      exact q'.reachable
    have hcomp :
        (deleteVertex H.coe R.cut).connectedComponentMk ⟨a, haCut⟩ =
          (deleteVertex H.coe R.cut).connectedComponentMk ⟨w, hwCut⟩ :=
      ConnectedComponent.sound hreach
    refine ⟨hwCut, ?_⟩
    have haComp :
        (deleteVertex H.coe R.cut).connectedComponentMk ⟨a, haCut⟩ =
          R.component := by
      simpa only [ConnectedComponent.mem_supp_iff] using R.a_mem.2
    have hwComp :
        (deleteVertex H.coe R.cut).connectedComponentMk ⟨w, hwCut⟩ =
          R.component := hcomp.symm.trans haComp
    simpa only [ConnectedComponent.mem_supp_iff] using hwComp
  rw [Finset.ssubset_iff_subset_ne]
  constructor
  · intro w hw
    apply (R.mem_carrier_iff w).mpr
    apply lift_mem w
    rw [ComponentEndBlock.verts, Set.mem_insert_iff]
    exact Or.inr ((S.mem_carrier_iff w).mp hw)
  · intro heq
    have hOldCutNew : S.cut ∈ R.carrier := by
      apply (R.mem_carrier_iff S.cut).mpr
      apply lift_mem S.cut
      simp [ComponentEndBlock.verts]
    have hOldCutOld : S.cut ∈ S.carrier := by rwa [heq]
    exact ComponentEndBlock.cut_not_mem_side S.cut S.component
      ((S.mem_carrier_iff S.cut).mp hOldCutOld)

/-- The finite carrier of an isolating side is literally one component of
the connector after deleting its cut vertex. -/
theorem IsolatingCutSide.carrier_isComponentAfterDeleting
    {H : G.Subgraph} {a b c : H.verts}
    (S : IsolatingCutSide H a b c) :
    IsComponentAfterDeleting H.coe ({S.cut} : Finset H.verts) S.carrier := by
  have hcarrier : ((S.carrier : Finset H.verts) : Set H.verts) =
      ComponentEndBlock.side S.cut S.component := by
    ext w
    exact S.mem_carrier_iff w
  refine ⟨⟨a, (S.mem_carrier_iff a).mpr S.a_mem⟩, ?_, ?_, ?_⟩
  · rw [Finset.disjoint_left]
    intro w hwC hwCut
    have hw : w = S.cut := by simpa using hwCut
    subst w
    exact ComponentEndBlock.cut_not_mem_side S.cut S.component
      ((S.mem_carrier_iff S.cut).mp hwC)
  · rw [hcarrier]
    exact ComponentEndBlock.side_connected S.cut S.component
  · intro u hu v hvCut huv
    have huSide : u ∈ ComponentEndBlock.side S.cut S.component := by
      rw [← hcarrier]
      exact hu
    have hvVerts := ComponentEndBlock.neighborSet_subset_verts
      (G := H.coe) S.component huSide huv
    rw [ComponentEndBlock.verts, Set.mem_insert_iff] at hvVerts
    rcases hvVerts with hv | hvSide
    · subst v
      exact (hvCut (by simp)).elim
    · exact (S.mem_carrier_iff v).mpr hvSide

/-- The isolated attachment and any vertex of its component side can be
joined disjointly from a path between the other two attachments.  Both
paths are mapped back to the ambient graph, with connector support
containment retained. -/
theorem IsolatingCutSide.exists_ambient_direct_linkage
    {H : G.Subgraph} (hH : H.Connected) {a b c : H.verts}
    (S : IsolatingCutSide H a b c) {s : H.verts}
    (hs : s ∈ ComponentEndBlock.side S.cut S.component) :
    ∃ (p : G.Walk a.1 s.1) (q : G.Walk b.1 c.1),
      p.IsPath ∧ q.IsPath ∧
      Disjoint {w | w ∈ p.support} {w | w ∈ q.support} ∧
      (∀ w, w ∈ p.support → w ∈ H.verts) ∧
      ∀ w, w ∈ q.support → w ∈ H.verts := by
  let hC := S.carrier_isComponentAfterDeleting (G := G)
  let aC : {w : H.verts // w ∈ (S.carrier : Set H.verts)} :=
    ⟨a, (S.mem_carrier_iff a).mpr S.a_mem⟩
  let sC : {w : H.verts // w ∈ (S.carrier : Set H.verts)} :=
    ⟨s, (S.mem_carrier_iff s).mpr hs⟩
  obtain ⟨pC, hpC⟩ := (hC.2.2.1 aC sC).exists_isPath
  let incC := (SimpleGraph.Embedding.induce
    (G := H.coe) (s := (S.carrier : Set H.verts))).toHom
  let pH₀ := pC.map incC
  let pH : H.coe.Walk a s := pH₀.copy rfl rfl
  have hpH : pH.IsPath := by
    exact (Walk.isPath_copy pH₀ rfl rfl).2
      (hpC.map Subtype.val_injective)
  have hpCarrier : ∀ w, w ∈ pH.support → w ∈ S.carrier := by
    intro w hw
    change w ∈ pH₀.support at hw
    rw [Walk.support_map] at hw
    obtain ⟨v, hv, hvw⟩ := List.mem_map.mp hw
    have : w = v.1 := hvw.symm
    subst w
    exact v.2
  obtain ⟨qH, hqH⟩ := (hH.coe b c).exists_isPath
  have hbCarrier : b ∉ S.carrier := by
    intro hb
    exact S.b_not_mem ((S.mem_carrier_iff b).mp hb)
  have hcCarrier : c ∉ S.carrier := by
    intro hc
    exact S.c_not_mem ((S.mem_carrier_iff c).mp hc)
  have hqAvoid : ∀ w, w ∈ qH.support → w ∉ S.carrier :=
    hC.path_avoids_singleton_component qH hqH hbCarrier hcCarrier
  let p : G.Walk a.1 s.1 := pH.map H.hom
  let q : G.Walk b.1 c.1 := qH.map H.hom
  refine ⟨p, q, hpH.map Subgraph.hom_injective,
    hqH.map Subgraph.hom_injective, ?_, ?_, ?_⟩
  · rw [Set.disjoint_left]
    intro w hwp hwq
    change w ∈ (pH.map H.hom).support at hwp
    change w ∈ (qH.map H.hom).support at hwq
    rw [Walk.support_map] at hwp hwq
    obtain ⟨u, hu, huw⟩ := List.mem_map.mp hwp
    obtain ⟨v, hv, hvw⟩ := List.mem_map.mp hwq
    have huv : u = v := by
      apply Subtype.ext
      exact huw.trans hvw.symm
    subst v
    exact hqAvoid u hv (hpCarrier u hu)
  · intro w hw
    change w ∈ (pH.map H.hom).support at hw
    rw [Walk.support_map] at hw
    obtain ⟨v, -, rfl⟩ := List.mem_map.mp hw
    exact v.2
  · intro w hw
    change w ∈ (qH.map H.hom).support at hw
    rw [Walk.support_map] at hw
    obtain ⟨v, -, rfl⟩ := List.mem_map.mp hw
    exact v.2

/-- Cardinal maximality among all isolating component sides.  This is the
form used in the exchange contradiction: a strictly larger isolated side
is forbidden, without having to compare dependent component witnesses. -/
def IsolatingCutSide.IsMaximal {H : G.Subgraph} {a b c : H.verts}
    (S : IsolatingCutSide H a b c) : Prop :=
  ∀ R : IsolatingCutSide H a b c, R.carrier.card ≤ S.carrier.card

/-- Maximality is unchanged when the two excluded attachments are
interchanged. -/
theorem IsolatingCutSide.swapBC_isMaximal
    {H : G.Subgraph} {a b c : H.verts}
    (S : IsolatingCutSide H a b c) (hS : S.IsMaximal) :
    S.swapBC.IsMaximal := by
  intro R
  have h := hS R.swapBC
  exact h

/-- Any nonempty family of isolating sides contains one of maximum finite
cardinality. -/
theorem exists_maximal_isolatingCutSide {H : G.Subgraph}
    {a b c : H.verts} (hne : Nonempty (IsolatingCutSide H a b c)) :
    ∃ S : IsolatingCutSide H a b c, S.IsMaximal := by
  classical
  let : Nonempty (IsolatingCutSide H a b c) := hne
  let size : IsolatingCutSide H a b c → ℕ := fun S ↦ S.carrier.card
  have hfinite :
      (size '' (Set.univ : Set (IsolatingCutSide H a b c))).Finite := by
    apply (Finset.finite_toSet
      (Finset.range (Fintype.card H.verts + 1))).subset
    intro n hn
    obtain ⟨S, -, rfl⟩ := hn
    simp only [Finset.mem_coe, Finset.mem_range]
    exact Nat.lt_succ_of_le (Finset.card_le_univ S.carrier)
  obtain ⟨S, -, hS⟩ := Set.Finite.exists_maximalFor'
    size (Set.univ : Set (IsolatingCutSide H a b c)) hfinite
    Set.univ_nonempty
  refine ⟨S, ?_⟩
  intro R
  rcases le_total (size R) (size S) with h | h
  · exact h
  · exact hS (by simp) h

/-- A maximum-cardinality isolating side cannot be strictly enlarged by
another isolating side.  This is the exact contradiction used after an
external path has been absorbed into the connector. -/
theorem IsolatingCutSide.IsMaximal.not_ssubset_carrier {H : G.Subgraph}
    {a b c : H.verts} {S : IsolatingCutSide H a b c}
    (hS : S.IsMaximal) (R : IsolatingCutSide H a b c) :
    ¬S.carrier ⊂ R.carrier := by
  intro hstrict
  have hlt := Finset.card_lt_card hstrict
  have hle := hS R
  omega

/-- A singleton separator whose cut lies outside a maximum isolating
endblock would create a strictly larger isolating component.  The second
source vertex is irrelevant to the extraction; retaining it in the
statement matches the two-pair Menger application on p.15. -/
theorem IsolatingCutSide.IsMaximal.false_of_separator_cut_outside_endBlock
    {H : G.Subgraph} {a b c : H.verts}
    (hH : H.Connected) (S : IsolatingCutSide H a b c)
    (hS : S.IsMaximal) {t u : H.verts} (hau : a ≠ u)
    (hsep : Erdos599.Countable.Separates H.coe ({a, t} : Set H.verts)
      ({b, c} : Set H.verts) ({u} : Set H.verts))
    (hu : u ∉ ComponentEndBlock.verts S.cut S.component) : False := by
  have hsepA : Erdos599.Countable.Separates H.coe ({a} : Set H.verts)
      ({b, c} : Set H.verts) ({u} : Set H.verts) := by
    intro a' ha' v hv q hq
    exact hsep a' (by
      simp only [Set.mem_singleton_iff] at ha'
      subst a'
      simp) v hv q hq
  obtain ⟨R, rfl⟩ := exists_isolatingCutSide_of_singleton_separator
    (G := G) hau hsepA
  apply hS.not_ssubset_carrier R
  exact S.carrier_ssubset_of_cut_not_mem_endBlock hH R hu

/-- A maximum `xB`-isolating side rules out a singleton separator between
`{xB,t}` and `{yB,zB}` whenever `t` is outside that side and its cut.  Cuts
inside the isolated component are bypassed through the connected complement;
the old cut itself would leave the component containing `t` attachment-free,
which is forbidden by complement pruning. -/
theorem MinimalABConnectorPair.no_singleton_B_separator_of_active
    (C : M.MinimalABConnectorPair) (hB : M.bSet.card = 3)
    (S : IsolatingCutSide C.bGraph
      (ABConnectorPair.xBIn (M := M) C.toABConnectorPair)
      (ABConnectorPair.yBIn (M := M) C.toABConnectorPair)
      (ABConnectorPair.zBIn (M := M) C.toABConnectorPair))
    (hS : S.IsMaximal) {t : C.bGraph.verts}
    (htSide : t ∉ ComponentEndBlock.side S.cut S.component)
    (htCut : t ≠ S.cut) :
    ∀ u : C.bGraph.verts,
      ¬Erdos599.Countable.Separates C.bGraph.coe
        ({ABConnectorPair.xBIn (M := M) C.toABConnectorPair, t} :
          Set C.bGraph.verts)
        ({ABConnectorPair.yBIn (M := M) C.toABConnectorPair,
          ABConnectorPair.zBIn (M := M) C.toABConnectorPair} :
          Set C.bGraph.verts)
        ({u} : Set C.bGraph.verts) := by
  classical
  have hByz : M.ySep.right ≠ M.zSep.right := by
    intro h
    have hsub : M.bSet ⊆
        ({M.xSep.right, M.zSep.right} : Finset V) := by
      intro w hw
      simpa [bSet, h] using hw
    have hle := Finset.card_le_card hsub
    have htwo : ({M.xSep.right, M.zSep.right} : Finset V).card ≤ 2 :=
      Finset.card_insert_le _ _
    omega
  have hyz : ABConnectorPair.yBIn (M := M) C.toABConnectorPair ≠
      ABConnectorPair.zBIn (M := M) C.toABConnectorPair := by
    intro h
    exact hByz (congrArg Subtype.val h)
  have hd : IsCutVertex C.bGraph.coe S.cut := S.isCutVertex hyz
  intro u hsep
  by_cases huEnd : u ∈ ComponentEndBlock.verts S.cut S.component
  · rw [ComponentEndBlock.verts, Set.mem_insert_iff] at huEnd
    rcases huEnd with huCut | huSide
    · have huCut' : u = S.cut := huCut
      subst u
      let tDel : {w : C.bGraph.verts // w ≠ S.cut} := ⟨t, htCut⟩
      let K : (deleteVertex C.bGraph.coe S.cut).ConnectedComponent :=
        (deleteVertex C.bGraph.coe S.cut).connectedComponentMk tDel
      apply C.false_of_B_attachment_free_cutComponent (M := M) S.cut K hd
      intro b hb hside
      have hbCases : b = M.xSep.right ∨ b = M.ySep.right ∨
          b = M.zSep.right := by
        simpa [bSet] using hb
      rcases hbCases with rfl | rfl | rfl
      · have hxComp :
            (deleteVertex C.bGraph.coe S.cut).connectedComponentMk
                ⟨ABConnectorPair.xBIn (M := M) C.toABConnectorPair,
                  hside.1⟩ = K := hside.2
        have hKS : K = S.component := hxComp.symm.trans S.a_mem.2
        apply htSide
        refine ⟨htCut, ?_⟩
        simpa only [tDel, K, ConnectedComponent.mem_supp_iff] using hKS
      · apply false_of_separator_of_same_delete_component C.bGraph
          (A := ({ABConnectorPair.xBIn (M := M) C.toABConnectorPair, t} :
            Set C.bGraph.verts))
          (B := ({ABConnectorPair.yBIn (M := M) C.toABConnectorPair,
            ABConnectorPair.zBIn (M := M) C.toABConnectorPair} :
            Set C.bGraph.verts))
          (s := t)
          (t := ABConnectorPair.yBIn (M := M) C.toABConnectorPair)
          (u := S.cut) (by simp) (by simp) htCut hside.1
          (by
            let yDel : {w : C.bGraph.verts // w ≠ S.cut} :=
              ⟨ABConnectorPair.yBIn (M := M) C.toABConnectorPair,
                hside.1⟩
            have hyDel : yDel =
                (⟨⟨M.ySep.right, C.b_contains _ M.yB_mem_bSet⟩,
                  hside.1⟩ : {w : C.bGraph.verts // w ≠ S.cut}) := by
              apply Subtype.ext
              apply Subtype.ext
              rfl
            change K = (deleteVertex C.bGraph.coe S.cut).connectedComponentMk
              yDel
            rw [hyDel]
            exact hside.2.symm) hsep
      · apply false_of_separator_of_same_delete_component C.bGraph
          (A := ({ABConnectorPair.xBIn (M := M) C.toABConnectorPair, t} :
            Set C.bGraph.verts))
          (B := ({ABConnectorPair.yBIn (M := M) C.toABConnectorPair,
            ABConnectorPair.zBIn (M := M) C.toABConnectorPair} :
            Set C.bGraph.verts))
          (s := t)
          (t := ABConnectorPair.zBIn (M := M) C.toABConnectorPair)
          (u := S.cut) (by simp) (by simp) htCut hside.1
          (by
            let zDel : {w : C.bGraph.verts // w ≠ S.cut} :=
              ⟨ABConnectorPair.zBIn (M := M) C.toABConnectorPair,
                hside.1⟩
            have hzDel : zDel =
                (⟨⟨M.zSep.right, C.b_contains _ M.zB_mem_bSet⟩,
                  hside.1⟩ : {w : C.bGraph.verts // w ≠ S.cut}) := by
              apply Subtype.ext
              apply Subtype.ext
              rfl
            change K = (deleteVertex C.bGraph.coe S.cut).connectedComponentMk
              zDel
            rw [hzDel]
            exact hside.2.symm) hsep
    · let R := cutComponentComplement C.bGraph S.cut S.component
      apply false_of_separator_of_connected_subgraph C.bGraph R
        (cutComponentComplement_connected C.bGraph C.b_connected
          S.cut S.component)
        (cutComponentComplement_le C.bGraph S.cut S.component)
        (A := ({ABConnectorPair.xBIn (M := M) C.toABConnectorPair, t} :
          Set C.bGraph.verts))
        (B := ({ABConnectorPair.yBIn (M := M) C.toABConnectorPair,
          ABConnectorPair.zBIn (M := M) C.toABConnectorPair} :
          Set C.bGraph.verts))
        (s := t)
        (t := ABConnectorPair.yBIn (M := M) C.toABConnectorPair)
        (u := u) (by simp) (by simp)
      · rw [mem_cutComponentComplement_verts_iff]
        exact ⟨t.2, htSide⟩
      · rw [mem_cutComponentComplement_verts_iff]
        exact ⟨(ABConnectorPair.yBIn (M := M)
          C.toABConnectorPair).2, S.b_not_mem⟩
      · intro huR
        exact ((mem_cutComponentComplement_verts_iff
          C.bGraph S.cut S.component u.1).mp huR).2 huSide
      · exact hsep
  · have hxu : ABConnectorPair.xBIn (M := M) C.toABConnectorPair ≠ u := by
      intro h
      apply huEnd
      rw [ComponentEndBlock.verts, Set.mem_insert_iff]
      right
      simpa only [h] using S.a_mem
    exact IsolatingCutSide.IsMaximal.false_of_separator_cut_outside_endBlock
      C.b_connected S hS hxu hsep huEnd

/-- In the default `B` choice there is no `xB`-isolating side.  A singleton
separator away from `xB` would create one.  If the separator is `xB` itself,
the component containing the second source is attachment-free and is removed
by the strict complement-pruning exchange. -/
theorem MinimalABConnectorPair.no_singleton_B_separator_of_default
    (C : M.MinimalABConnectorPair) (hB : M.bSet.card = 3)
    (hnone : ¬Nonempty (IsolatingCutSide C.bGraph
      (ABConnectorPair.xBIn (M := M) C.toABConnectorPair)
      (ABConnectorPair.yBIn (M := M) C.toABConnectorPair)
      (ABConnectorPair.zBIn (M := M) C.toABConnectorPair)))
    {t : C.bGraph.verts}
    (htX : t ≠ ABConnectorPair.xBIn (M := M) C.toABConnectorPair) :
    ∀ u : C.bGraph.verts,
      ¬Erdos599.Countable.Separates C.bGraph.coe
        ({ABConnectorPair.xBIn (M := M) C.toABConnectorPair, t} :
          Set C.bGraph.verts)
        ({ABConnectorPair.yBIn (M := M) C.toABConnectorPair,
          ABConnectorPair.zBIn (M := M) C.toABConnectorPair} :
          Set C.bGraph.verts)
        ({u} : Set C.bGraph.verts) := by
  classical
  have hxy : M.xSep.right ≠ M.ySep.right := by
    intro h
    have hsub : M.bSet ⊆
        ({M.ySep.right, M.zSep.right} : Finset V) := by
      intro w hw
      simpa [bSet, h] using hw
    have hle := Finset.card_le_card hsub
    have htwo : ({M.ySep.right, M.zSep.right} : Finset V).card ≤ 2 :=
      Finset.card_insert_le _ _
    omega
  have hxz : M.xSep.right ≠ M.zSep.right := by
    intro h
    have hsub : M.bSet ⊆
        ({M.ySep.right, M.zSep.right} : Finset V) := by
      intro w hw
      simpa [bSet, h] using hw
    have hle := Finset.card_le_card hsub
    have htwo : ({M.ySep.right, M.zSep.right} : Finset V).card ≤ 2 :=
      Finset.card_insert_le _ _
    omega
  intro u hsep
  by_cases hxu : ABConnectorPair.xBIn (M := M)
      C.toABConnectorPair = u
  · subst u
    let xB := ABConnectorPair.xBIn (M := M) C.toABConnectorPair
    let tDel : {w : C.bGraph.verts // w ≠ xB} := ⟨t, htX⟩
    let K : (deleteVertex C.bGraph.coe xB).ConnectedComponent :=
      (deleteVertex C.bGraph.coe xB).connectedComponentMk tDel
    have hyX : ABConnectorPair.yBIn (M := M) C.toABConnectorPair ≠ xB := by
      intro h
      exact hxy (congrArg Subtype.val h.symm)
    have hd : IsCutVertex C.bGraph.coe xB := by
      intro hpre
      apply false_of_separator_of_same_delete_component C.bGraph
        (A := ({xB, t} : Set C.bGraph.verts))
        (B := ({ABConnectorPair.yBIn (M := M) C.toABConnectorPair,
          ABConnectorPair.zBIn (M := M) C.toABConnectorPair} :
          Set C.bGraph.verts))
        (s := t)
        (t := ABConnectorPair.yBIn (M := M) C.toABConnectorPair)
        (u := xB) (by simp) (by simp) htX hyX
        (ConnectedComponent.sound (hpre ⟨t, htX⟩
          ⟨ABConnectorPair.yBIn (M := M) C.toABConnectorPair, hyX⟩)) hsep
    apply C.false_of_B_attachment_free_cutComponent (M := M) xB K hd
    intro b hb hside
    have hbCases : b = M.xSep.right ∨ b = M.ySep.right ∨
        b = M.zSep.right := by
      simpa [bSet] using hb
    rcases hbCases with rfl | rfl | rfl
    · exact hside.1 (Subtype.ext rfl)
    · apply false_of_separator_of_same_delete_component C.bGraph
        (A := ({xB, t} : Set C.bGraph.verts))
        (B := ({ABConnectorPair.yBIn (M := M) C.toABConnectorPair,
          ABConnectorPair.zBIn (M := M) C.toABConnectorPair} :
          Set C.bGraph.verts))
        (s := t)
        (t := ABConnectorPair.yBIn (M := M) C.toABConnectorPair)
        (u := xB) (by simp) (by simp) htX hside.1
        (by
          let yDel : {w : C.bGraph.verts // w ≠ xB} :=
            ⟨ABConnectorPair.yBIn (M := M) C.toABConnectorPair, hside.1⟩
          have hyDel : yDel =
              (⟨⟨M.ySep.right, C.b_contains _ M.yB_mem_bSet⟩,
                hside.1⟩ : {w : C.bGraph.verts // w ≠ xB}) := by
            apply Subtype.ext
            apply Subtype.ext
            rfl
          change K = (deleteVertex C.bGraph.coe xB).connectedComponentMk yDel
          rw [hyDel]
          exact hside.2.symm) hsep
    · apply false_of_separator_of_same_delete_component C.bGraph
        (A := ({xB, t} : Set C.bGraph.verts))
        (B := ({ABConnectorPair.yBIn (M := M) C.toABConnectorPair,
          ABConnectorPair.zBIn (M := M) C.toABConnectorPair} :
          Set C.bGraph.verts))
        (s := t)
        (t := ABConnectorPair.zBIn (M := M) C.toABConnectorPair)
        (u := xB) (by simp) (by simp) htX hside.1
        (by
          let zDel : {w : C.bGraph.verts // w ≠ xB} :=
            ⟨ABConnectorPair.zBIn (M := M) C.toABConnectorPair, hside.1⟩
          have hzDel : zDel =
              (⟨⟨M.zSep.right, C.b_contains _ M.zB_mem_bSet⟩,
                hside.1⟩ : {w : C.bGraph.verts // w ≠ xB}) := by
            apply Subtype.ext
            apply Subtype.ext
            rfl
          change K = (deleteVertex C.bGraph.coe xB).connectedComponentMk zDel
          rw [hzDel]
          exact hside.2.symm) hsep
  · have hsepX : Erdos599.Countable.Separates C.bGraph.coe
        ({ABConnectorPair.xBIn (M := M) C.toABConnectorPair} :
          Set C.bGraph.verts)
        ({ABConnectorPair.yBIn (M := M) C.toABConnectorPair,
          ABConnectorPair.zBIn (M := M) C.toABConnectorPair} :
          Set C.bGraph.verts)
        ({u} : Set C.bGraph.verts) := by
      intro a ha b hb p hp
      apply hsep a ?_ b hb p hp
      simp only [Set.mem_singleton_iff] at ha
      subst a
      simp
    obtain ⟨R, -⟩ := exists_isolatingCutSide_of_singleton_separator
      (G := G) hxu hsepX
    exact hnone ⟨R⟩

/-- AHT's `B`-side choice on p.15: either a maximum isolating side for
`xB` exists, or no such side exists and the degenerate choice is
`vB = xB`, `CB = ∅`.  Keeping the alternatives in one datatype prevents
the default case from being silently lost in the external-path exchange. -/
inductive BIsolationChoice (C : M.MinimalABConnectorPair) : Type u
  | active
      (side : IsolatingCutSide C.bGraph
        (ABConnectorPair.xBIn (M := M) C.toABConnectorPair)
        (ABConnectorPair.yBIn (M := M) C.toABConnectorPair)
        (ABConnectorPair.zBIn (M := M) C.toABConnectorPair))
      (maximal : side.IsMaximal)
  | default
      (none : ¬Nonempty (IsolatingCutSide C.bGraph
        (ABConnectorPair.xBIn (M := M) C.toABConnectorPair)
        (ABConnectorPair.yBIn (M := M) C.toABConnectorPair)
        (ABConnectorPair.zBIn (M := M) C.toABConnectorPair)))

namespace BIsolationChoice

variable {C : M.MinimalABConnectorPair}

/-- The chosen `B` cut, with the default choice equal to `xB`. -/
def cut (B : BIsolationChoice (M := M) C) : C.bGraph.verts :=
  match B with
  | .active S _ => S.cut
  | .default _ => ABConnectorPair.xBIn (M := M) C.toABConnectorPair

/-- The chosen ambient component carrier, empty in the default case. -/
noncomputable def carrier (B : BIsolationChoice (M := M) C) : Finset V :=
  match B with
  | .active S _ => S.ambientCarrier
  | .default _ => ∅

theorem carrier_subset_bGraph (B : BIsolationChoice (M := M) C) :
    (B.carrier : Set V) ⊆ C.bGraph.verts := by
  intro w hw
  cases B with
  | active S hmax =>
      obtain ⟨hwH, -⟩ := (S.mem_ambientCarrier_iff w).mp hw
      exact hwH
  | default hnone => simp [carrier] at hw

theorem xB_mem_carrier_or_cut_eq
    (B : BIsolationChoice (M := M) C) :
    M.xSep.right ∈ B.carrier ∨ B.cut.1 = M.xSep.right := by
  cases B with
  | active S hmax =>
      left
      apply (S.mem_ambientCarrier_iff M.xSep.right).mpr
      exact ⟨(ABConnectorPair.xBIn (M := M)
        C.toABConnectorPair).2, S.a_mem⟩
  | default hnone =>
      right
      rfl

theorem yB_not_mem_carrier (B : BIsolationChoice (M := M) C) :
    M.ySep.right ∉ B.carrier := by
  cases B with
  | active S hmax =>
      intro h
      obtain ⟨hy, hySide⟩ :=
        (S.mem_ambientCarrier_iff M.ySep.right).mp h
      exact S.b_not_mem (by
        simpa only [ABConnectorPair.yBIn] using hySide)
  | default hnone => simp [carrier]

theorem zB_not_mem_carrier (B : BIsolationChoice (M := M) C) :
    M.zSep.right ∉ B.carrier := by
  cases B with
  | active S hmax =>
      intro h
      obtain ⟨hz, hzSide⟩ :=
        (S.mem_ambientCarrier_iff M.zSep.right).mp h
      exact S.c_not_mem (by
        simpa only [ABConnectorPair.zBIn] using hzSide)
  | default hnone => simp [carrier]

theorem cut_not_mem_carrier (B : BIsolationChoice (M := M) C) :
    B.cut.1 ∉ B.carrier := by
  cases B with
  | active S hmax =>
      intro h
      obtain ⟨hcut, hside⟩ :=
        (S.mem_ambientCarrier_iff S.cut.1).mp h
      exact hside.1 (Subtype.ext rfl)
  | default hnone => simp [cut, carrier]

end BIsolationChoice

/-- The optional maximum `B`-side choice always exists. -/
theorem MinimalABConnectorPair.exists_BIsolationChoice
    (C : M.MinimalABConnectorPair) :
    Nonempty (BIsolationChoice (M := M) C) := by
  classical
  by_cases h : Nonempty (IsolatingCutSide C.bGraph
      (ABConnectorPair.xBIn (M := M) C.toABConnectorPair)
      (ABConnectorPair.yBIn (M := M) C.toABConnectorPair)
      (ABConnectorPair.zBIn (M := M) C.toABConnectorPair))
  · obtain ⟨S, hS⟩ := exists_maximal_isolatingCutSide h
    exact ⟨BIsolationChoice.active S hS⟩
  · exact ⟨BIsolationChoice.default h⟩

/-- The chosen optional `B` carrier belongs to the same pair component as
`x`; this is vacuous in the default case. -/
theorem BIsolationChoice.carrier_subset_pairComponent
    (C : M.MinimalABConnectorPair)
    (SA : IsolatingCutSide C.aGraph
      (ABConnectorPair.xAIn (M := M) C.toABConnectorPair)
      (ABConnectorPair.yAIn (M := M) C.toABConnectorPair)
      (ABConnectorPair.zAIn (M := M) C.toABConnectorPair))
    (B : BIsolationChoice (M := M) C)
    (D : G.ComponentCompl
      ((({SA.cut.1, B.cut.1} : Finset V) : Set V)))
    (hxD : x ∈ (D : Set V)) :
    (B.carrier : Set V) ⊆ (D : Set V) := by
  intro w hw
  cases B with
  | active SB hSB =>
      obtain ⟨hwB, hwSide⟩ :=
        (SB.mem_ambientCarrier_iff w).mp hw
      exact (C.pairComponent_contains_activeSides
        (M := M) SA SB D hxD).2 ⟨w, hwB⟩ hwSide
  | default hnone => simp [BIsolationChoice.carrier] at hw

/-- The initial cluster in the standard p.15 path extraction:
`CA ∪ CB ∪ X`, with `CB = ∅` in the default case. -/
noncomputable def MinimalABConnectorPair.pairNearRegion
    (C : M.MinimalABConnectorPair)
    (SA : IsolatingCutSide C.aGraph
      (ABConnectorPair.xAIn (M := M) C.toABConnectorPair)
      (ABConnectorPair.yAIn (M := M) C.toABConnectorPair)
      (ABConnectorPair.zAIn (M := M) C.toABConnectorPair))
    (B : BIsolationChoice (M := M) C) : Finset V :=
  SA.ambientCarrier ∪ B.carrier ∪ M.xPart

@[simp] theorem MinimalABConnectorPair.x_mem_pairNearRegion
    (C : M.MinimalABConnectorPair)
    (SA : IsolatingCutSide C.aGraph
      (ABConnectorPair.xAIn (M := M) C.toABConnectorPair)
      (ABConnectorPair.yAIn (M := M) C.toABConnectorPair)
      (ABConnectorPair.zAIn (M := M) C.toABConnectorPair))
    (B : BIsolationChoice (M := M) C) :
    x ∈ C.pairNearRegion (M := M) SA B := by
  simp only [MinimalABConnectorPair.pairNearRegion,
    Finset.mem_union]
  exact Or.inr M.x_mem_xPart

theorem MinimalABConnectorPair.pairNearRegion_subset_pairComponent
    (C : M.MinimalABConnectorPair)
    (SA : IsolatingCutSide C.aGraph
      (ABConnectorPair.xAIn (M := M) C.toABConnectorPair)
      (ABConnectorPair.yAIn (M := M) C.toABConnectorPair)
      (ABConnectorPair.zAIn (M := M) C.toABConnectorPair))
    (B : BIsolationChoice (M := M) C)
    (D : G.ComponentCompl
      ((({SA.cut.1, B.cut.1} : Finset V) : Set V)))
    (hxD : x ∈ (D : Set V)) :
    (C.pairNearRegion (M := M) SA B : Set V) ⊆ (D : Set V) := by
  obtain ⟨hX, -, hA⟩ := C.pairComponent_contains_xSides
    (M := M) SA B.cut D hxD
  have hB := B.carrier_subset_pairComponent (M := M) C SA D hxD
  intro w hw
  simp only [MinimalABConnectorPair.pairNearRegion,
    Finset.mem_coe, Finset.mem_union] at hw
  rcases hw with (hwA | hwB) | hwX
  · obtain ⟨hwGraph, hwSide⟩ :=
      (SA.mem_ambientCarrier_iff w).mp hwA
    exact hA ⟨w, hwGraph⟩ hwSide
  · exact hB hwB
  · have hwSide : w ∈ (M.xSep.side : Set V) := by
      simpa only [xPart, mem_componentCarrier] using hwX
    exact hX hwSide

/-- The four attachments on the opposite `x`-rim are outside the initial
cluster. -/
theorem MinimalABConnectorPair.farAttachments_not_mem_pairNearRegion
    (C : M.MinimalABConnectorPair)
    (SA : IsolatingCutSide C.aGraph
      (ABConnectorPair.xAIn (M := M) C.toABConnectorPair)
      (ABConnectorPair.yAIn (M := M) C.toABConnectorPair)
      (ABConnectorPair.zAIn (M := M) C.toABConnectorPair))
    (B : BIsolationChoice (M := M) C) :
    M.ySep.left ∉ C.pairNearRegion (M := M) SA B ∧
      M.zSep.left ∉ C.pairNearRegion (M := M) SA B ∧
      M.ySep.right ∉ C.pairNearRegion (M := M) SA B ∧
      M.zSep.right ∉ C.pairNearRegion (M := M) SA B := by
  have left_not_Bcarrier {w : V} (hwA : w ∈ C.aGraph.verts) :
      w ∉ B.carrier := by
    intro hwB
    exact Set.disjoint_left.mp C.vertex_disjoint hwA
      (B.carrier_subset_bGraph (M := M) hwB)
  have right_not_Acarrier {w : V} (hwB : w ∈ C.bGraph.verts) :
      w ∉ SA.ambientCarrier := by
    intro hwA
    exact Set.disjoint_left.mp C.vertex_disjoint
      (SA.ambientCarrier_subset hwA) hwB
  simp only [MinimalABConnectorPair.pairNearRegion,
    Finset.mem_union, not_or]
  constructor
  · exact ⟨⟨by simpa only [ABConnectorPair.yAIn] using
          SA.b_not_mem_ambientCarrier,
        left_not_Bcarrier (C.a_contains _ M.yA_mem_aSet)⟩,
      fun hwX ↦ Finset.disjoint_left.mp M.xPart_disjoint_aSet
        hwX M.yA_mem_aSet⟩
  constructor
  · exact ⟨⟨by simpa only [ABConnectorPair.zAIn] using
          SA.c_not_mem_ambientCarrier,
        left_not_Bcarrier (C.a_contains _ M.zA_mem_aSet)⟩,
      fun hwX ↦ Finset.disjoint_left.mp M.xPart_disjoint_aSet
        hwX M.zA_mem_aSet⟩
  constructor
  · exact ⟨⟨right_not_Acarrier (C.b_contains _ M.yB_mem_bSet),
        B.yB_not_mem_carrier⟩,
      fun hwX ↦ Finset.disjoint_left.mp M.xPart_disjoint_bSet
        hwX M.yB_mem_bSet⟩
  · exact ⟨⟨right_not_Acarrier (C.b_contains _ M.zB_mem_bSet),
        B.zB_not_mem_carrier⟩,
      fun hwX ↦ Finset.disjoint_left.mp M.xPart_disjoint_bSet
        hwX M.zB_mem_bSet⟩

/-- Trim an arbitrary simple connector-to-connector path to the segment
which last leaves a prescribed union `U` of connector sides and first
returns to the remaining connector vertices.  Its interior has no vertex
in either connector.  This is the finite first/last-contact operation used
to obtain AHT's external path `S`. -/
theorem ABConnectorPair.exists_cleanExitPath
    (C : M.ABConnectorPair) (U : Finset V)
    {a b : V} (raw : G.Walk a b) (hraw : raw.IsPath)
    (hUsub : (U : Set V) ⊆ C.aGraph.verts ∪ C.bGraph.verts)
    (haU : a ∈ U)
    (hbConn : b ∈ C.aGraph.verts ∪ C.bGraph.verts)
    (hbU : b ∉ U) :
    ∃ s, s ∈ U ∧ ∃ t,
      t ∈ C.aGraph.verts ∪ C.bGraph.verts ∧ t ∉ U ∧
      ∃ p : G.Walk s t, p.IsPath ∧
        (∀ w, w ∈ p.support → w ∈ raw.support) ∧
        ∀ w, w ∈ p.support →
          w ∈ C.aGraph.verts ∪ C.bGraph.verts → w = s ∨ w = t := by
  classical
  let F : Finset V :=
    (C.aGraph.verts ∪ C.bGraph.verts).toFinset \ U
  have haF : a ∉ F := by
    intro ha
    exact (Finset.mem_sdiff.mp ha).2 haU
  have hbF : b ∈ F := by
    simp only [F, Finset.mem_sdiff, Set.mem_toFinset]
    exact ⟨hbConn, hbU⟩
  obtain ⟨t, htF, q, hq, hqRaw, hqFirst⟩ :=
    exists_initialPath_to_finset_wm F haF hbF raw hraw
  have htConn : t ∈ C.aGraph.verts ∪ C.bGraph.verts := by
    simpa only [Set.mem_toFinset] using (Finset.mem_sdiff.mp htF).1
  have htU : t ∉ U := (Finset.mem_sdiff.mp htF).2
  obtain ⟨s, hsU, r, hr, hrQ, hrFirst⟩ :=
    exists_initialPath_to_finset_wm U htU haU q.reverse hq.reverse
  let p : G.Walk s t := r.reverse
  refine ⟨s, hsU, t, htConn, htU, p, hr.reverse, ?_, ?_⟩
  · intro w hw
    have hwr : w ∈ r.support := by
      simpa only [p, Walk.support_reverse, List.mem_reverse] using hw
    have hwqr : w ∈ q.reverse.support := hrQ w hwr
    have hwq : w ∈ q.support := by
      simpa only [Walk.support_reverse, List.mem_reverse] using hwqr
    exact hqRaw w hwq
  · intro w hw hwConn
    have hwr : w ∈ r.support := by
      simpa only [p, Walk.support_reverse, List.mem_reverse] using hw
    by_cases hwU : w ∈ U
    · exact Or.inl (hrFirst w hwr hwU)
    · right
      have hwqr : w ∈ q.reverse.support := hrQ w hwr
      have hwq : w ∈ q.support := by
        simpa only [Walk.support_reverse, List.mem_reverse] using hwqr
      apply hqFirst w hwq
      simp only [F, Finset.mem_sdiff, Set.mem_toFinset]
      exact ⟨hwConn, hwU⟩

/-- A finite first/last-contact lemma in its symmetric form.  A simple path
from `U` to a disjoint set `F` contains a subpath whose only vertices in
`U ∪ F` are its two ends.  This is the path-trimming operation used in
the "standard" external-path extraction on p.15. -/
theorem exists_cleanPath_between_finsets
    (U F : Finset V) (hUF : Disjoint U F)
    {a b : V} (raw : G.Walk a b) (hraw : raw.IsPath)
    (haU : a ∈ U) (hbF : b ∈ F) :
    ∃ s, s ∈ U ∧ ∃ t, t ∈ F ∧
      ∃ p : G.Walk s t, p.IsPath ∧
        (∀ w, w ∈ p.support → w ∈ raw.support) ∧
        ∀ w, w ∈ p.support → w ∈ U ∪ F →
          w = s ∨ w = t := by
  classical
  have haF : a ∉ F := by
    intro ha
    exact Finset.disjoint_left.mp hUF haU ha
  obtain ⟨t, htF, q, hq, hqRaw, hqFirst⟩ :=
    exists_initialPath_to_finset_wm F haF hbF raw hraw
  have htU : t ∉ U := by
    intro ht
    exact Finset.disjoint_left.mp hUF ht htF
  obtain ⟨s, hsU, r, hr, hrQ, hrFirst⟩ :=
    exists_initialPath_to_finset_wm U htU haU q.reverse hq.reverse
  let p : G.Walk s t := r.reverse
  refine ⟨s, hsU, t, htF, p, hr.reverse, ?_, ?_⟩
  · intro w hw
    have hwr : w ∈ r.support := by
      simpa only [p, Walk.support_reverse, List.mem_reverse] using hw
    have hwqr : w ∈ q.reverse.support := hrQ w hwr
    have hwq : w ∈ q.support := by
      simpa only [Walk.support_reverse, List.mem_reverse] using hwqr
    exact hqRaw w hwq
  · intro w hw hwUF
    have hwr : w ∈ r.support := by
      simpa only [p, Walk.support_reverse, List.mem_reverse] using hw
    rcases Finset.mem_union.mp hwUF with hwU | hwF
    · exact Or.inl (hrFirst w hwr hwU)
    · right
      have hwqr : w ∈ q.reverse.support := hrQ w hwr
      have hwq : w ∈ q.support := by
        simpa only [Walk.support_reverse, List.mem_reverse] using hwqr
      exact hqFirst w hwq hwF

/-- Combine the maximal-`X` external path with an arc of the opposite rim,
then trim it by the preceding first/last-contact lemma.  The result starts
in any prescribed connector-side union `U` containing `xA`, ends in the
remaining connector vertices (for example at or before `yA`), and has no
internal connector vertices. -/
theorem MinimalABConnectorPair.exists_cleanExternalExit
    (C : M.MinimalABConnectorPair)
    (S : IsolatingCutSide C.aGraph
      (ABConnectorPair.xAIn (M := M) C.toABConnectorPair)
      (ABConnectorPair.yAIn (M := M) C.toABConnectorPair)
      (ABConnectorPair.zAIn (M := M) C.toABConnectorPair))
    (vB : C.bGraph.verts) (U : Finset V)
    (hUsub : (U : Set V) ⊆ C.aGraph.verts ∪ C.bGraph.verts)
    (hxAU : M.xSep.left ∈ U) (hyAU : M.ySep.left ∉ U) :
    ∃ s, s ∈ U ∧ ∃ t,
      t ∈ C.aGraph.verts ∪ C.bGraph.verts ∧ t ∉ U ∧
      ∃ p : G.Walk s t, p.IsPath ∧
        ∀ w, w ∈ p.support →
          w ∈ C.aGraph.verts ∪ C.bGraph.verts → w = s ∨ w = t := by
  classical
  obtain ⟨w, hwRim, -, -, p, hp, -⟩ :=
    C.exists_externalPath_to_xRim (M := M) S vB
  have hyRim : M.ySep.left ∈ T.xRim.support := by
    apply xRim_mem_of_yRoute_mem
    apply T.yRoute.support_takeUntil_subset_support T.y_mem
    exact M.ySep.left_mem_aArm
  obtain ⟨q, hq, hqRim⟩ :=
    exists_path_in_cycleSupport T.xRim_isCycle hwRim hyRim
  let raw₀ : G.Walk M.xSep.left M.ySep.left := p.append q
  let raw : G.Walk M.xSep.left M.ySep.left := raw₀.toPath
  obtain ⟨s, hsU, t, htConn, htU, r, hr, -, hrMeet⟩ :=
    ABConnectorPair.exists_cleanExitPath (M := M) C.toABConnectorPair U raw
      raw₀.toPath.prop hUsub hxAU
      (Or.inl (C.a_contains _ M.yA_mem_aSet)) hyAU
  exact ⟨s, hsU, t, htConn, htU, r, hr, hrMeet⟩

/-- A cut-avoiding raw path from `xA` to a connector vertex outside the
initial near region can be trimmed to the exact external path used on p.15.
Unlike `exists_cleanNearExit` below, this formulation remembers that *both*
chosen cut vertices are absent from the resulting path.  It is the form used
when the component of `G - {vA,vB}` containing `x` already contains one of
the four far attachments. -/
theorem MinimalABConnectorPair.exists_cleanNearExit_of_cutAvoidingRaw
    (C : M.MinimalABConnectorPair)
    (SA : IsolatingCutSide C.aGraph
      (ABConnectorPair.xAIn (M := M) C.toABConnectorPair)
      (ABConnectorPair.yAIn (M := M) C.toABConnectorPair)
      (ABConnectorPair.zAIn (M := M) C.toABConnectorPair))
    (B : BIsolationChoice (M := M) C) {f : V}
    (hfConn : f ∈ C.aGraph.verts ∪ C.bGraph.verts)
    (hfNear : f ∉ C.pairNearRegion (M := M) SA B)
    (hfX : f ∉ M.xPart)
    (raw : G.Walk M.xSep.left f) (hraw : raw.IsPath)
    (hrawCuts : ∀ w, w ∈ raw.support →
      w ≠ SA.cut.1 ∧ w ≠ B.cut.1) :
    ∃ s, s ∈ C.pairNearRegion (M := M) SA B ∧ ∃ t,
      t ∈ C.aGraph.verts ∪ C.bGraph.verts ∧
      t ∉ C.pairNearRegion (M := M) SA B ∧
      ∃ p : G.Walk s t, p.IsPath ∧
        (∀ w, w ∈ p.support →
          w ∈ C.aGraph.verts ∪ C.bGraph.verts → w = s ∨ w = t) ∧
        (∀ w, w ∈ p.support →
          w ∈ C.pairNearRegion (M := M) SA B → w = s) ∧
        (∀ w, w ∈ p.support →
          w ≠ SA.cut.1 ∧ w ≠ B.cut.1) ∧
        ∀ w, w ∈ p.support → w ∉ M.xPart := by
  classical
  let U : Finset V := C.pairNearRegion (M := M) SA B
  let F : Finset V :=
    (C.aGraph.verts ∪ C.bGraph.verts).toFinset \ U
  have hUF : Disjoint U F := by
    rw [Finset.disjoint_left]
    intro w hwU hwF
    exact (Finset.mem_sdiff.mp hwF).2 hwU
  have hxAU : M.xSep.left ∈ U := by
    simp only [U, MinimalABConnectorPair.pairNearRegion,
      Finset.mem_union]
    left
    left
    apply (SA.mem_ambientCarrier_iff M.xSep.left).mpr
    exact ⟨(ABConnectorPair.xAIn (M := M)
      C.toABConnectorPair).2, SA.a_mem⟩
  have hfF : f ∈ F := by
    simp only [F, Finset.mem_sdiff, Set.mem_toFinset]
    exact ⟨hfConn, hfNear⟩
  obtain ⟨s, hsU, t, htF, p, hp, hpRaw, hpMeet⟩ :=
    exists_cleanPath_between_finsets (G := G) U F hUF raw hraw hxAU hfF
  have htConn : t ∈ C.aGraph.verts ∪ C.bGraph.verts := by
    simpa only [F, Finset.mem_sdiff, Set.mem_toFinset] using
      (Finset.mem_sdiff.mp htF).1
  have htU : t ∉ U := (Finset.mem_sdiff.mp htF).2
  have hpMeetConn : ∀ w, w ∈ p.support →
      w ∈ C.aGraph.verts ∪ C.bGraph.verts → w = s ∨ w = t := by
    intro w hw hwConn
    have hwUF : w ∈ U ∪ F := by
      by_cases hwU : w ∈ U
      · exact Finset.mem_union_left F hwU
      · apply Finset.mem_union_right U
        simp only [F, Finset.mem_sdiff, Set.mem_toFinset]
        exact ⟨hwConn, hwU⟩
    exact hpMeet w hw hwUF
  have hpOnlyNear : ∀ w, w ∈ p.support → w ∈ U → w = s := by
    intro w hw hwU
    rcases hpMeet w hw (Finset.mem_union_left F hwU) with h | h
    · exact h
    · subst w
      exact (htU hwU).elim
  have hsNotX : s ∉ M.xPart := by
    cases B with
    | active SB hSB =>
        intro hsX
        have hxBU : M.xSep.right ∈ U := by
          simp only [U, MinimalABConnectorPair.pairNearRegion,
            BIsolationChoice.carrier, Finset.mem_union]
          left
          right
          exact SB.a_mem_ambientCarrier
        have hst : s ≠ t := by
          intro h
          subst t
          exact htU hsU
        have hnon : ¬p.Nil := p.not_nil_of_ne hst
        have huSupport : p.snd ∈ p.support :=
          List.mem_of_mem_tail (p.snd_mem_tail_support hnon)
        have huNotU : p.snd ∉ U := by
          intro huU
          have hus : p.snd = s := hpOnlyNear p.snd huSupport huU
          exact (p.adj_snd hnon).ne hus.symm
        by_cases huX : p.snd ∈ M.xPart
        · exact huNotU (by
            simp only [U, MinimalABConnectorPair.pairNearRegion,
              Finset.mem_union]
            exact Or.inr huX)
        · have hsSide : s ∈ (M.xSep.side : Set V) := by
            simpa only [xPart, mem_componentCarrier] using hsX
          by_cases huA : p.snd = M.xSep.left
          · exact huNotU (huA ▸ hxAU)
          by_cases huB : p.snd = M.xSep.right
          · exact huNotU (huB ▸ hxBU)
          have huAvoid : p.snd ∉
              ((({M.xSep.left, M.xSep.right} : Finset V) : Set V)) := by
            simpa only [Finset.mem_coe, Finset.mem_insert,
              Finset.mem_singleton, not_or] using ⟨huA, huB⟩
          have huSide : p.snd ∈ (M.xSep.side : Set V) :=
            ComponentCompl.mem_of_adj s p.snd hsSide huAvoid
              (p.adj_snd hnon)
          exact huX (by
            simpa only [xPart, mem_componentCarrier] using huSide)
    | default hnone =>
        have hXstd : IsComponentAfterDeleting G
            ({M.xSep.left, M.xSep.right} : Finset V) M.xPart := by
          simpa only [xPart] using
            (isComponentAfterDeleting_componentCarrier
              (G := G) ({M.xSep.left, M.xSep.right} : Finset V)
              M.xSep.side)
        have hXswap : IsComponentAfterDeleting G
            ({M.xSep.right, M.xSep.left} : Finset V) M.xPart := by
          rw [Finset.pair_comm M.xSep.right M.xSep.left]
          exact hXstd
        have hxBNotReverse : M.xSep.right ∉ raw.reverse.support := by
          simp only [Walk.support_reverse, List.mem_reverse]
          intro hxB
          exact (hrawCuts M.xSep.right hxB).2 rfl
        have hrawNoX : ∀ w, w ∈ raw.support → w ∉ M.xPart := by
          have hrev := hXswap.path_to_boundary_avoids_component
            raw.reverse hraw.reverse hfX hxBNotReverse
          intro w hw
          apply hrev w
          simpa only [Walk.support_reverse, List.mem_reverse] using hw
        exact hrawNoX s (hpRaw s p.start_mem_support)
  have hpNoX : ∀ w, w ∈ p.support → w ∉ M.xPart := by
    intro w hw hwX
    have hwU : w ∈ U := by
      simp only [U, MinimalABConnectorPair.pairNearRegion,
        Finset.mem_union]
      exact Or.inr hwX
    have hws : w = s := hpOnlyNear w hw hwU
    exact hsNotX (hws ▸ hwX)
  refine ⟨s, hsU, t, htConn, htU, p, hp, hpMeetConn, hpOnlyNear, ?_, hpNoX⟩
  intro w hw
  exact hrawCuts w (hpRaw w hw)

/-- If the component of `G - {vA,vB}` containing `x` already contains
one of the four attachments on the opposite `x`-rim, connectivity inside
that component supplies the cut-avoiding raw path required by the preceding
trimming lemma.  This is the direct (non-rim-bridge) branch of the standard
path extraction on p.15. -/
theorem MinimalABConnectorPair.exists_cleanNearExit_of_farAttachment_mem
    (C : M.MinimalABConnectorPair)
    (SA : IsolatingCutSide C.aGraph
      (ABConnectorPair.xAIn (M := M) C.toABConnectorPair)
      (ABConnectorPair.yAIn (M := M) C.toABConnectorPair)
      (ABConnectorPair.zAIn (M := M) C.toABConnectorPair))
    (B : BIsolationChoice (M := M) C)
    (D : G.ComponentCompl
      ((({SA.cut.1, B.cut.1} : Finset V) : Set V)))
    (hxD : x ∈ (D : Set V)) {f : V}
    (hf : f = M.ySep.left ∨ f = M.zSep.left ∨
      f = M.ySep.right ∨ f = M.zSep.right)
    (hfD : f ∈ (D : Set V)) :
    ∃ s, s ∈ C.pairNearRegion (M := M) SA B ∧ ∃ t,
      t ∈ C.aGraph.verts ∪ C.bGraph.verts ∧
      t ∉ C.pairNearRegion (M := M) SA B ∧
      ∃ p : G.Walk s t, p.IsPath ∧
        (∀ w, w ∈ p.support →
          w ∈ C.aGraph.verts ∪ C.bGraph.verts → w = s ∨ w = t) ∧
        (∀ w, w ∈ p.support →
          w ∈ C.pairNearRegion (M := M) SA B → w = s) ∧
        (∀ w, w ∈ p.support →
          w ≠ SA.cut.1 ∧ w ≠ B.cut.1) ∧
        ∀ w, w ∈ p.support → w ∉ M.xPart := by
  classical
  have hfConn : f ∈ C.aGraph.verts ∪ C.bGraph.verts := by
    rcases hf with rfl | rfl | rfl | rfl
    · exact Or.inl (C.a_contains _ M.yA_mem_aSet)
    · exact Or.inl (C.a_contains _ M.zA_mem_aSet)
    · exact Or.inr (C.b_contains _ M.yB_mem_bSet)
    · exact Or.inr (C.b_contains _ M.zB_mem_bSet)
  have hfNear : f ∉ C.pairNearRegion (M := M) SA B := by
    obtain ⟨hyA, hzA, hyB, hzB⟩ :=
      C.farAttachments_not_mem_pairNearRegion (M := M) SA B
    rcases hf with rfl | rfl | rfl | rfl
    · exact hyA
    · exact hzA
    · exact hyB
    · exact hzB
  have hfParts : f ∉
      (M.xPart : Set V) ∪ (M.yPart : Set V) ∪ (M.zPart : Set V) :=
    Set.disjoint_left.mp C.avoids_terminal_parts hfConn
  have hfX : f ∉ M.xPart := by
    intro hfX
    exact hfParts (Or.inl (Or.inl hfX))
  have hxAD : M.xSep.left ∈ (D : Set V) :=
    C.xA_mem_pairComponent (M := M) SA B.cut D hxD
  let xA' : {u : V // u ∈
      (((({SA.cut.1, B.cut.1} : Finset V) : Set V)))ᶜ} :=
    ⟨M.xSep.left, hxAD.1⟩
  let f' : {u : V // u ∈
      (((({SA.cut.1, B.cut.1} : Finset V) : Set V)))ᶜ} :=
    ⟨f, hfD.1⟩
  have hreach :
      (G.induce (((({SA.cut.1, B.cut.1} : Finset V) : Set V)))ᶜ).Reachable
        xA' f' :=
    ConnectedComponent.exact (hxAD.2.trans hfD.2.symm)
  obtain ⟨q, hq⟩ := hreach.exists_isPath
  let inc : G.induce
      (((({SA.cut.1, B.cut.1} : Finset V) : Set V)))ᶜ →g G :=
    (SimpleGraph.Embedding.induce
      (G := G)
      (s := (((({SA.cut.1, B.cut.1} : Finset V) : Set V)))ᶜ)).toHom
  let raw₀ := q.map inc
  let raw : G.Walk M.xSep.left f := raw₀.copy rfl rfl
  have hraw : raw.IsPath := by
    exact (Walk.isPath_copy raw₀ rfl rfl).2
      (hq.map Subtype.val_injective)
  have hrawCuts : ∀ w, w ∈ raw.support →
      w ≠ SA.cut.1 ∧ w ≠ B.cut.1 := by
    intro w hw
    have hw₀ : w ∈ raw₀.support := by
      change w ∈ (raw₀.copy rfl rfl).support at hw
      rw [Walk.support_copy] at hw
      exact hw
    change w ∈ (q.map inc).support at hw₀
    rw [Walk.support_map] at hw₀
    obtain ⟨v, -, rfl⟩ := List.mem_map.mp hw₀
    have hvNot : v.1 ∉
        ((({SA.cut.1, B.cut.1} : Finset V) : Set V)) := v.2
    have hvinc : inc v = v.1 := rfl
    rw [hvinc]
    simpa only [Finset.mem_coe, Finset.mem_insert,
      Finset.mem_singleton, not_or] using hvNot
  exact C.exists_cleanNearExit_of_cutAvoidingRaw (M := M) SA B
    hfConn hfNear hfX raw hraw hrawCuts

/-- Suppose both chosen connector cuts lie on the opposite `x`-rim and
the pair-deletion component containing `x` meets that rim.  Then the pair
component contains one of the four far attachments, unless the two
cut-to-cut arcs already form a cycle through `x,y,z`. -/
theorem MinimalABConnectorPair.farAttachment_mem_pairComponent_or_cycle
    (C : M.MinimalABConnectorPair)
    (SA : IsolatingCutSide C.aGraph
      (ABConnectorPair.xAIn (M := M) C.toABConnectorPair)
      (ABConnectorPair.yAIn (M := M) C.toABConnectorPair)
      (ABConnectorPair.zAIn (M := M) C.toABConnectorPair))
    (B : BIsolationChoice (M := M) C)
    (D : G.ComponentCompl
      ((({SA.cut.1, B.cut.1} : Finset V) : Set V)))
    (hxD : x ∈ (D : Set V)) {r : V}
    (hrRim : r ∈ T.xRim.support) (hrD : r ∈ (D : Set V))
    (hcutARim : SA.cut.1 ∈ T.xRim.support)
    (hcutBRim : B.cut.1 ∈ T.xRim.support)
    (hconn : G.Connected)
    (hdelete : ∀ d : V, (G.induce fun w : V ↦ w ≠ d).Connected) :
    (∃ f, (f = M.ySep.left ∨ f = M.zSep.left ∨
        f = M.ySep.right ∨ f = M.zSep.right) ∧
      f ∈ (D : Set V)) ∨ HasCycleThroughThree G x y z := by
  classical
  by_cases hyAD : M.ySep.left ∈ (D : Set V)
  · exact Or.inl ⟨M.ySep.left, Or.inl rfl, hyAD⟩
  by_cases hzAD : M.zSep.left ∈ (D : Set V)
  · exact Or.inl ⟨M.zSep.left, Or.inr (Or.inl rfl), hzAD⟩
  by_cases hyBD : M.ySep.right ∈ (D : Set V)
  · exact Or.inl ⟨M.ySep.right, Or.inr (Or.inr (Or.inl rfl)), hyBD⟩
  by_cases hzBD : M.zSep.right ∈ (D : Set V)
  · exact Or.inl ⟨M.zSep.right, Or.inr (Or.inr (Or.inr rfl)), hzBD⟩
  right
  have hyD : y ∉ (D : Set V) := by
    intro hyD
    obtain ⟨p, hp, hpD⟩ :=
      ComponentCompl.exists_path_within D hxD hyD
    have hYpair : IsComponentAfterDeleting G
        ({M.ySep.left, M.ySep.right} : Finset V) M.yPart := by
      simpa only [yPart] using
        (isComponentAfterDeleting_componentCarrier
          (G := G) ({M.ySep.left, M.ySep.right} : Finset V)
          M.ySep.side)
    have havoid : ∀ w, w ∈ p.reverse.support →
        w ∉ ({M.ySep.left, M.ySep.right} : Finset V) := by
      intro w hw
      have hwp : w ∈ p.support := by
        simpa only [Walk.support_reverse, List.mem_reverse] using hw
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      constructor
      · intro h
        subst w
        exact hyAD (hpD _ hwp)
      · intro h
        subst w
        exact hyBD (hpD _ hwp)
    have hxY : x ∈ M.yPart :=
      hYpair.walk_end_mem p.reverse M.y_mem_yPart havoid
    exact Finset.disjoint_left.mp M.xPart_disjoint_yPart
      M.x_mem_xPart hxY
  have hzD : z ∉ (D : Set V) := by
    intro hzD
    obtain ⟨p, hp, hpD⟩ :=
      ComponentCompl.exists_path_within D hxD hzD
    have hZpair : IsComponentAfterDeleting G
        ({M.zSep.left, M.zSep.right} : Finset V) M.zPart := by
      simpa only [zPart] using
        (isComponentAfterDeleting_componentCarrier
          (G := G) ({M.zSep.left, M.zSep.right} : Finset V)
          M.zSep.side)
    have havoid : ∀ w, w ∈ p.reverse.support →
        w ∉ ({M.zSep.left, M.zSep.right} : Finset V) := by
      intro w hw
      have hwp : w ∈ p.support := by
        simpa only [Walk.support_reverse, List.mem_reverse] using hw
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      constructor
      · intro h
        subst w
        exact hzAD (hpD _ hwp)
      · intro h
        subst w
        exact hzBD (hpD _ hwp)
    have hxZ : x ∈ M.zPart :=
      hZpair.walk_end_mem p.reverse M.z_mem_zPart havoid
    exact Finset.disjoint_left.mp M.xPart_disjoint_zPart
      M.x_mem_xPart hxZ
  have hcuts : SA.cut.1 ≠ B.cut.1 := by
    intro h
    exact Set.disjoint_left.mp C.vertex_disjoint SA.cut.2
      (h ▸ B.cut.2)
  have terminal_ne_connector {t d : V}
      (ht : t ∈ (M.xPart : Set V) ∪ (M.yPart : Set V) ∪
        (M.zPart : Set V))
      (hd : d ∈ C.aGraph.verts ∪ C.bGraph.verts) : t ≠ d := by
    intro h
    exact Set.disjoint_left.mp C.avoids_terminal_parts hd (h ▸ ht)
  have hyA : y ≠ SA.cut.1 := terminal_ne_connector
    (Or.inl (Or.inr M.y_mem_yPart)) (Or.inl SA.cut.2)
  have hyB : y ≠ B.cut.1 := terminal_ne_connector
    (Or.inl (Or.inr M.y_mem_yPart)) (Or.inr B.cut.2)
  have hzA : z ≠ SA.cut.1 := terminal_ne_connector
    (Or.inr M.z_mem_zPart) (Or.inl SA.cut.2)
  have hzB : z ≠ B.cut.1 := terminal_ne_connector
    (Or.inr M.z_mem_zPart) (Or.inr B.cut.2)
  have hyRim : y ∈ T.xRim.support := by
    simp [WatkinsMesnerK32Source.xRim, T.y_mem]
  have hzRim : z ∈ T.xRim.support := by
    simp [WatkinsMesnerK32Source.xRim, T.z_mem]
  exact hasCycleThroughThree_of_cycle_component_split
    T.xRim T.xRim_isCycle hcutARim hcutBRim hcuts hrRim
    hyRim hzRim hyA hyB hzA hzB D hxD hrD hyD hzD hconn hdelete

/-- Full standard external-path extraction from AHT p.15.  The initial
maximal-`X` path reaches the opposite rim while avoiding both chosen cuts.
Cut the rim between that contact and a far A-attachment.  Either one arc
avoids both cuts, or the cuts lie on opposite arcs; in the latter case the
preceding component dichotomy supplies a far attachment in the same pair
component (the alternative is the forbidden common cycle).  In every case
we obtain a clean near-region exit avoiding both cuts. -/
theorem MinimalABConnectorPair.exists_cleanNearExit_avoiding_cuts
    (C : M.MinimalABConnectorPair) (hA : M.aSet.card = 3)
    (SA : IsolatingCutSide C.aGraph
      (ABConnectorPair.xAIn (M := M) C.toABConnectorPair)
      (ABConnectorPair.yAIn (M := M) C.toABConnectorPair)
      (ABConnectorPair.zAIn (M := M) C.toABConnectorPair))
    (B : BIsolationChoice (M := M) C)
    (hconn : G.Connected)
    (hdelete : ∀ d : V, (G.induce fun w : V ↦ w ≠ d).Connected)
    (hno : ¬HasCycleThroughThree G x y z) :
    ∃ s, s ∈ C.pairNearRegion (M := M) SA B ∧ ∃ t,
      t ∈ C.aGraph.verts ∪ C.bGraph.verts ∧
      t ∉ C.pairNearRegion (M := M) SA B ∧
      ∃ p : G.Walk s t, p.IsPath ∧
        (∀ w, w ∈ p.support →
          w ∈ C.aGraph.verts ∪ C.bGraph.verts → w = s ∨ w = t) ∧
        (∀ w, w ∈ p.support →
          w ∈ C.pairNearRegion (M := M) SA B → w = s) ∧
        (∀ w, w ∈ p.support →
          w ≠ SA.cut.1 ∧ w ≠ B.cut.1) ∧
        ∀ w, w ∈ p.support → w ∉ M.xPart := by
  classical
  have hcuts : SA.cut.1 ≠ B.cut.1 := by
    intro h
    exact Set.disjoint_left.mp C.vertex_disjoint SA.cut.2
      (h ▸ B.cut.2)
  have hxAvoid :
      x ∈ (((({SA.cut.1, B.cut.1} : Finset V) : Set V)))ᶜ := by
    simp only [Set.mem_compl_iff, Finset.mem_coe, Finset.mem_insert,
      Finset.mem_singleton, not_or]
    constructor
    · intro h
      have hxA : x ∈ C.aGraph.verts := by
        simpa only [h] using SA.cut.2
      exact Set.disjoint_left.mp C.avoids_terminal_parts
        (Or.inl hxA) (Or.inl (Or.inl M.x_mem_xPart))
    · intro h
      have hxB : x ∈ C.bGraph.verts := by
        simpa only [h] using B.cut.2
      exact Set.disjoint_left.mp C.avoids_terminal_parts
        (Or.inr hxB) (Or.inl (Or.inl M.x_mem_xPart))
  let D : G.ComponentCompl
      ((({SA.cut.1, B.cut.1} : Finset V) : Set V)) :=
    G.componentComplMk hxAvoid
  have hxD : x ∈ (D : Set V) := ⟨hxAvoid, rfl⟩
  obtain ⟨r, hrRim, hrA, hrB, p, hp, hpAvoid⟩ :=
    C.exists_externalPath_to_xRim (M := M) SA B.cut
  have hxAD : M.xSep.left ∈ (D : Set V) :=
    C.xA_mem_pairComponent (M := M) SA B.cut D hxD
  have hrD : r ∈ (D : Set V) := by
    apply ComponentCompl.walk_end_mem D p hxAD
    intro w hw
    have hwEnds := hpAvoid w hw
    simpa only [Finset.mem_coe, Finset.mem_insert,
      Finset.mem_singleton, not_or] using hwEnds
  have hyz : M.ySep.left ≠ M.zSep.left := by
    intro h
    have hsub : M.aSet ⊆
        ({M.xSep.left, M.zSep.left} : Finset V) := by
      intro w hw
      simpa [aSet, h] using hw
    have hle := Finset.card_le_card hsub
    have htwo : ({M.xSep.left, M.zSep.left} : Finset V).card ≤ 2 :=
      Finset.card_insert_le _ _
    omega
  let farA : V :=
    if SA.cut.1 = M.ySep.left then M.zSep.left else M.ySep.left
  have hfarA : farA = M.ySep.left ∨ farA = M.zSep.left := by
    simp only [farA]
    split <;> simp
  have hfarAttachment : farA = M.ySep.left ∨
      farA = M.zSep.left ∨ farA = M.ySep.right ∨
        farA = M.zSep.right := by
    rcases hfarA with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  have hcutANeFar : SA.cut.1 ≠ farA := by
    simp only [farA]
    split
    · rename_i hcut
      exact fun h ↦ hyz (hcut.symm.trans h)
    · rename_i hcut
      exact hcut
  have hfarConnA : farA ∈ C.aGraph.verts := by
    rcases hfarA with hfar | hfar
    · rw [hfar]
      exact C.a_contains _ M.yA_mem_aSet
    · rw [hfar]
      exact C.a_contains _ M.zA_mem_aSet
  have hcutBNeFar : B.cut.1 ≠ farA := by
    intro h
    exact Set.disjoint_left.mp C.vertex_disjoint hfarConnA
      (h.symm ▸ B.cut.2)
  have hfarNear : farA ∉ C.pairNearRegion (M := M) SA B := by
    rcases hfarA with hfar | hfar
    · rw [hfar]
      exact (C.farAttachments_not_mem_pairNearRegion
        (M := M) SA B).1
    · rw [hfar]
      exact (C.farAttachments_not_mem_pairNearRegion
        (M := M) SA B).2.1
  have hfarParts : farA ∉
      (M.xPart : Set V) ∪ (M.yPart : Set V) ∪ (M.zPart : Set V) :=
    Set.disjoint_left.mp C.avoids_terminal_parts (Or.inl hfarConnA)
  have hfarX : farA ∉ M.xPart := by
    intro h
    exact hfarParts (Or.inl (Or.inl h))
  by_cases hfarD : farA ∈ (D : Set V)
  · exact C.exists_cleanNearExit_of_farAttachment_mem (M := M)
      SA B D hxD hfarAttachment hfarD
  have hrFar : r ≠ farA := by
    intro h
    exact hfarD (h ▸ hrD)
  have hfarRim : farA ∈ T.xRim.support := by
    rcases hfarA with hfar | hfar
    · rw [hfar]
      apply xRim_mem_of_yRoute_mem
      apply T.yRoute.support_takeUntil_subset_support T.y_mem
      exact M.ySep.left_mem_aArm
    · rw [hfar]
      apply xRim_mem_of_zRoute_mem
      apply T.zRoute.support_takeUntil_subset_support T.z_mem
      exact M.zSep.left_mem_aArm
  rcases exists_cyclePath_avoiding_two_or_opposite_arcs
      T.xRim_isCycle hrRim hfarRim hrFar
      hrA.symm hcutANeFar hrB.symm hcutBNeFar with
    hgood | ⟨q₁, q₂, hq₁, hq₂, hq₁Rim, hq₂Rim,
      hAq₁, hBq₁, hBq₂, hAq₂, hmeet⟩
  · obtain ⟨q, hq, hqRim, hqA, hqB⟩ := hgood
    let raw₀ : G.Walk M.xSep.left farA := p.append q
    let raw : G.Walk M.xSep.left farA := raw₀.toPath
    have hraw : raw.IsPath := raw₀.toPath.prop
    have hrawCuts : ∀ w, w ∈ raw.support →
        w ≠ SA.cut.1 ∧ w ≠ B.cut.1 := by
      intro w hw
      have hw₀ : w ∈ raw₀.support :=
        raw₀.support_toPath_subset_support hw
      rcases (Walk.mem_support_append_iff p q).mp hw₀ with hwp | hwq
      · exact hpAvoid w hwp
      · exact ⟨fun h ↦ hqA (h ▸ hwq),
          fun h ↦ hqB (h ▸ hwq)⟩
    exact C.exists_cleanNearExit_of_cutAvoidingRaw (M := M) SA B
      (Or.inl hfarConnA) hfarNear hfarX raw hraw hrawCuts
  · have hcutARim : SA.cut.1 ∈ T.xRim.support :=
      hq₂Rim _ hAq₂
    have hcutBRim : B.cut.1 ∈ T.xRim.support :=
      hq₁Rim _ hBq₁
    rcases C.farAttachment_mem_pairComponent_or_cycle (M := M)
        SA B D hxD hrRim hrD hcutARim hcutBRim hconn hdelete with
      ⟨f, hf, hfD⟩ | hcycle
    · exact C.exists_cleanNearExit_of_farAttachment_mem
        (M := M) SA B D hxD hf hfD
    · exact (hno hcycle).elim

/-- The maximal-`X` path, trimmed against the full initial region
`CA ∪ CB ∪ X`.  The far end is a connector vertex outside that region,
and no other connector vertex occurs on the trimmed path.  We retain the
precise provenance needed for the remaining endpoint classification: every
vertex either lies on the opposite `x`-rim or avoids both chosen cut
vertices. -/
theorem MinimalABConnectorPair.exists_cleanNearExit
    (C : M.MinimalABConnectorPair)
    (hA : M.aSet.card = 3)
    (SA : IsolatingCutSide C.aGraph
      (ABConnectorPair.xAIn (M := M) C.toABConnectorPair)
      (ABConnectorPair.yAIn (M := M) C.toABConnectorPair)
      (ABConnectorPair.zAIn (M := M) C.toABConnectorPair))
    (B : BIsolationChoice (M := M) C) :
    ∃ s, s ∈ C.pairNearRegion (M := M) SA B ∧ ∃ t,
      t ∈ C.aGraph.verts ∪ C.bGraph.verts ∧
      t ∉ C.pairNearRegion (M := M) SA B ∧
      ∃ p : G.Walk s t, p.IsPath ∧
        (∀ w, w ∈ p.support →
          w ∈ C.aGraph.verts ∪ C.bGraph.verts → w = s ∨ w = t) ∧
        (∀ w, w ∈ p.support →
          w ∈ C.pairNearRegion (M := M) SA B → w = s) ∧
        (∀ w, w ∈ p.support → w ≠ SA.cut.1) ∧
        (∀ w, w ∈ p.support → w ∉ M.xPart) ∧
        ∀ w, w ∈ p.support →
          w ∈ T.xRim.support ∨
            (w ≠ SA.cut.1 ∧ w ≠ B.cut.1) := by
  classical
  let U : Finset V := C.pairNearRegion (M := M) SA B
  let F : Finset V :=
    (C.aGraph.verts ∪ C.bGraph.verts).toFinset \ U
  have hUF : Disjoint U F := by
    rw [Finset.disjoint_left]
    intro w hwU hwF
    exact (Finset.mem_sdiff.mp hwF).2 hwU
  have hxAU : M.xSep.left ∈ U := by
    simp only [U, MinimalABConnectorPair.pairNearRegion,
      Finset.mem_union]
    left
    left
    apply (SA.mem_ambientCarrier_iff M.xSep.left).mpr
    exact ⟨(ABConnectorPair.xAIn (M := M)
      C.toABConnectorPair).2, SA.a_mem⟩
  have hyz : M.ySep.left ≠ M.zSep.left := by
    intro h
    have hsub : M.aSet ⊆
        ({M.xSep.left, M.zSep.left} : Finset V) := by
      intro w hw
      simpa [aSet, h] using hw
    have hle := Finset.card_le_card hsub
    have htwo : ({M.xSep.left, M.zSep.left} : Finset V).card ≤ 2 :=
      Finset.card_insert_le _ _
    omega
  let farA : V :=
    if SA.cut.1 = M.ySep.left then M.zSep.left else M.ySep.left
  have hfarA : farA = M.ySep.left ∨ farA = M.zSep.left := by
    simp only [farA]
    split <;> simp
  have hcutNeFar : SA.cut.1 ≠ farA := by
    simp only [farA]
    split
    · rename_i hcut
      exact fun h ↦ hyz (hcut.symm.trans h)
    · rename_i hcut
      exact hcut
  have hfarANotU : farA ∉ U := by
    rcases hfarA with hfar | hfar
    · rw [hfar]
      exact (C.farAttachments_not_mem_pairNearRegion
        (M := M) SA B).1
    · rw [hfar]
      exact (C.farAttachments_not_mem_pairNearRegion
        (M := M) SA B).2.1
  have hfarAF : farA ∈ F := by
    simp only [F, Finset.mem_sdiff, Set.mem_toFinset]
    refine ⟨?_, hfarANotU⟩
    rcases hfarA with hfar | hfar
    · rw [hfar]
      exact Or.inl (C.a_contains _ M.yA_mem_aSet)
    · rw [hfar]
      exact Or.inl (C.a_contains _ M.zA_mem_aSet)
  obtain ⟨r, hrRim, hrA, -, p, hp, hpAvoid⟩ :=
    C.exists_externalPath_to_xRim (M := M) SA B.cut
  have hfarRim : farA ∈ T.xRim.support := by
    rcases hfarA with hfar | hfar
    · rw [hfar]
      apply xRim_mem_of_yRoute_mem
      apply T.yRoute.support_takeUntil_subset_support T.y_mem
      exact M.ySep.left_mem_aArm
    · rw [hfar]
      apply xRim_mem_of_zRoute_mem
      apply T.zRoute.support_takeUntil_subset_support T.z_mem
      exact M.zSep.left_mem_aArm
  obtain ⟨q, hq, hqRim, hqAvoid⟩ :=
    exists_path_in_cycleSupport_avoiding T.xRim_isCycle hrRim hfarRim
      hrA.symm hcutNeFar
  let raw₀ : G.Walk M.xSep.left farA := p.append q
  let raw : G.Walk M.xSep.left farA := raw₀.toPath
  obtain ⟨s, hsU, t, htF, e, he, heRaw, heMeet⟩ :=
    exists_cleanPath_between_finsets (G := G) U F hUF raw raw₀.toPath.prop
      hxAU hfarAF
  have htConn : t ∈ C.aGraph.verts ∪ C.bGraph.verts := by
    simpa only [F, Finset.mem_sdiff, Set.mem_toFinset] using
      (Finset.mem_sdiff.mp htF).1
  have htU : t ∉ U := (Finset.mem_sdiff.mp htF).2
  have heMeetConn : ∀ w, w ∈ e.support →
      w ∈ C.aGraph.verts ∪ C.bGraph.verts → w = s ∨ w = t := by
    intro w hw hwConn
    have hwUF : w ∈ U ∪ F := by
      by_cases hwU : w ∈ U
      · exact Finset.mem_union_left F hwU
      · apply Finset.mem_union_right U
        simp only [F, Finset.mem_sdiff, Set.mem_toFinset]
        exact ⟨hwConn, hwU⟩
    exact heMeet w hw hwUF
  have heOnlyNear : ∀ w, w ∈ e.support → w ∈ U → w = s := by
    intro w hw hwU
    rcases heMeet w hw (Finset.mem_union_left F hwU) with h | h
    · exact h
    · subst w
      exact (htU hwU).elim
  have hrNotX : r ∉ M.xPart := by
    intro hrX
    apply M.xSep.not_mem_componentCarrier_of_mem_rim hrRim
    simpa only [xPart] using hrX
  have hqNoX : ∀ w, w ∈ q.support → w ∉ M.xPart := by
    intro w hw hwX
    apply M.xSep.not_mem_componentCarrier_of_mem_rim (hqRim w hw)
    simpa only [xPart] using hwX
  have hsNotX : s ∉ M.xPart := by
    cases B with
    | active SB hSB =>
        intro hsX
        have hxAU' : M.xSep.left ∈ U := hxAU
        have hxBU : M.xSep.right ∈ U := by
          simp only [U, MinimalABConnectorPair.pairNearRegion,
            BIsolationChoice.carrier, Finset.mem_union]
          left
          right
          exact SB.a_mem_ambientCarrier
        have hst : s ≠ t := by
          intro h
          subst t
          exact htU hsU
        have hnon : ¬e.Nil := e.not_nil_of_ne hst
        have huSupport : e.snd ∈ e.support :=
          List.mem_of_mem_tail (e.snd_mem_tail_support hnon)
        have huNotU : e.snd ∉ U := by
          intro huU
          have hus : e.snd = s := heOnlyNear e.snd huSupport huU
          exact (e.adj_snd hnon).ne hus.symm
        by_cases huX : e.snd ∈ M.xPart
        · exact huNotU (by
            simp only [U, MinimalABConnectorPair.pairNearRegion,
              Finset.mem_union]
            exact Or.inr huX)
        · have hsSide : s ∈ (M.xSep.side : Set V) := by
            simpa only [xPart, mem_componentCarrier] using hsX
          by_cases huA : e.snd = M.xSep.left
          · exact huNotU (huA ▸ hxAU')
          by_cases huB : e.snd = M.xSep.right
          · exact huNotU (huB ▸ hxBU)
          have huAvoid : e.snd ∉
              ((({M.xSep.left, M.xSep.right} : Finset V) : Set V)) := by
            simpa only [Finset.mem_coe, Finset.mem_insert,
              Finset.mem_singleton, not_or] using ⟨huA, huB⟩
          have huSide : e.snd ∈ (M.xSep.side : Set V) :=
            ComponentCompl.mem_of_adj s e.snd hsSide huAvoid
              (e.adj_snd hnon)
          exact huX (by
            simpa only [xPart, mem_componentCarrier] using huSide)
    | default hnone =>
        have hXstd : IsComponentAfterDeleting G
            ({M.xSep.left, M.xSep.right} : Finset V) M.xPart := by
          simpa only [xPart] using
            (isComponentAfterDeleting_componentCarrier
              (G := G) ({M.xSep.left, M.xSep.right} : Finset V)
              M.xSep.side)
        have hXswap : IsComponentAfterDeleting G
            ({M.xSep.right, M.xSep.left} : Finset V) M.xPart := by
          rw [Finset.pair_comm M.xSep.right M.xSep.left]
          exact hXstd
        have hxBNotReverse : M.xSep.right ∉ p.reverse.support := by
          simp only [Walk.support_reverse, List.mem_reverse]
          intro hxB
          exact (hpAvoid M.xSep.right hxB).2 rfl
        have hpNoX : ∀ w, w ∈ p.support → w ∉ M.xPart := by
          have hrev := hXswap.path_to_boundary_avoids_component
            p.reverse hp.reverse hrNotX hxBNotReverse
          intro w hw
          apply hrev w
          simpa only [Walk.support_reverse, List.mem_reverse] using hw
        intro hsX
        have hsRaw : s ∈ raw.support := heRaw s e.start_mem_support
        have hsRaw₀ : s ∈ raw₀.support :=
          raw₀.support_toPath_subset_support hsRaw
        rcases (Walk.mem_support_append_iff p q).mp hsRaw₀ with hsp | hsq
        · exact hpNoX s hsp hsX
        · exact hqNoX s hsq hsX
  have heNoX : ∀ w, w ∈ e.support → w ∉ M.xPart := by
    intro w hw hwX
    have hwU : w ∈ U := by
      simp only [U, MinimalABConnectorPair.pairNearRegion,
        Finset.mem_union]
      exact Or.inr hwX
    have hws : w = s := heOnlyNear w hw hwU
    exact hsNotX (hws ▸ hwX)
  refine ⟨s, hsU, t, htConn, htU, e, he, heMeetConn, ?_, ?_, heNoX, ?_⟩
  · intro w hw hwU
    apply heOnlyNear w hw
    simpa only [U] using hwU
  · intro w hw hcut
    subst w
    have hcutRaw : SA.cut.1 ∈ raw.support := heRaw SA.cut.1 hw
    have hcutRaw₀ : SA.cut.1 ∈ raw₀.support :=
      raw₀.support_toPath_subset_support hcutRaw
    rcases (Walk.mem_support_append_iff p q).mp hcutRaw₀ with hwp | hwq
    · exact (hpAvoid SA.cut.1 hwp).1 rfl
    · exact hqAvoid hwq
  · intro w hw
    have hwRaw : w ∈ raw.support := heRaw w hw
    have hwRaw₀ : w ∈ raw₀.support :=
      raw₀.support_toPath_subset_support hwRaw
    rcases (Walk.mem_support_append_iff p q).mp hwRaw₀ with hwp | hwq
    · exact Or.inr (hpAvoid w hwp)
    · exact Or.inl (hqRim w hwq)

/-- The property ultimately forced by minimality and the three maximal
terminal separators. -/
def ABConnectorPair.IsTwoConnected (C : M.ABConnectorPair) : Prop :=
  AHTVertexTwoConnected C.aGraph.coe ∧
    AHTVertexTwoConnected C.bGraph.coe

/-- Relabel a connector pair along the transposition of `y,z`. -/
def ABConnectorPair.swapYZ (C : M.ABConnectorPair) :
    (swapYZTriple M).ABConnectorPair where
  aGraph := C.aGraph
  bGraph := C.bGraph
  a_connected := C.a_connected
  b_connected := C.b_connected
  a_contains := by
    intro a ha
    apply C.a_contains a
    rwa [← swapYZTriple_aSet M]
  b_contains := by
    intro b hb
    apply C.b_contains b
    rwa [← swapYZTriple_bSet M]
  vertex_disjoint := C.vertex_disjoint
  avoids_terminal_parts := by
    rw [swapYZTriple_xPart, swapYZTriple_yPart, swapYZTriple_zPart]
    simpa only [Set.union_assoc, Set.union_left_comm, Set.union_comm] using
      C.avoids_terminal_parts

theorem ABConnectorPair.swapYZ_isTwoConnected (C : M.ABConnectorPair)
    (h2 : C.IsTwoConnected) : C.swapYZ.IsTwoConnected := h2

/-- Relabel a connector pair along the cyclic permutation `x,y,z ↦ y,z,x`. -/
def ABConnectorPair.rotateYZX (C : M.ABConnectorPair) :
    (rotateYZXTriple M).ABConnectorPair where
  aGraph := C.aGraph
  bGraph := C.bGraph
  a_connected := C.a_connected
  b_connected := C.b_connected
  a_contains := by
    intro a ha
    apply C.a_contains a
    rwa [← rotateYZXTriple_aSet M]
  b_contains := by
    intro b hb
    apply C.b_contains b
    rwa [← rotateYZXTriple_bSet M]
  vertex_disjoint := C.vertex_disjoint
  avoids_terminal_parts := by
    rw [rotateYZXTriple_xPart, rotateYZXTriple_yPart,
      rotateYZXTriple_zPart]
    simpa only [Set.union_assoc, Set.union_left_comm, Set.union_comm] using
      C.avoids_terminal_parts

theorem ABConnectorPair.rotateYZX_isTwoConnected (C : M.ABConnectorPair)
    (h2 : C.IsTwoConnected) : C.rotateYZX.IsTwoConnected := h2

/-- Minimality of the connector cut-defect is invariant under swapping
the labels `y,z`. -/
def MinimalABConnectorPair.swapYZ (C : M.MinimalABConnectorPair) :
    (swapYZTriple M).MinimalABConnectorPair where
  toABConnectorPair := C.toABConnectorPair.swapYZ
  minimal := by
    intro D
    let E : M.ABConnectorPair :=
      { aGraph := D.aGraph
        bGraph := D.bGraph
        a_connected := D.a_connected
        b_connected := D.b_connected
        a_contains := by
          intro a ha
          apply D.a_contains a
          rwa [swapYZTriple_aSet]
        b_contains := by
          intro b hb
          apply D.b_contains b
          rwa [swapYZTriple_bSet]
        vertex_disjoint := D.vertex_disjoint
        avoids_terminal_parts := by
          have h := D.avoids_terminal_parts
          rw [swapYZTriple_xPart, swapYZTriple_yPart,
            swapYZTriple_zPart] at h
          simpa only [Set.union_assoc, Set.union_left_comm,
            Set.union_comm] using h }
    have hmin := C.minimal E
    simpa only [ABConnectorPair.cutDefect, E,
      ABConnectorPair.swapYZ] using hmin

/-- Minimality of the connector cut-defect is invariant under the cyclic
relabeling `x,y,z ↦ y,z,x`. -/
def MinimalABConnectorPair.rotateYZX (C : M.MinimalABConnectorPair) :
    (rotateYZXTriple M).MinimalABConnectorPair where
  toABConnectorPair := C.toABConnectorPair.rotateYZX
  minimal := by
    intro D
    let E : M.ABConnectorPair :=
      { aGraph := D.aGraph
        bGraph := D.bGraph
        a_connected := D.a_connected
        b_connected := D.b_connected
        a_contains := by
          intro a ha
          apply D.a_contains a
          rwa [rotateYZXTriple_aSet]
        b_contains := by
          intro b hb
          apply D.b_contains b
          rwa [rotateYZXTriple_bSet]
        vertex_disjoint := D.vertex_disjoint
        avoids_terminal_parts := by
          have h := D.avoids_terminal_parts
          rw [rotateYZXTriple_xPart, rotateYZXTriple_yPart,
            rotateYZXTriple_zPart] at h
          simpa only [Set.union_assoc, Set.union_left_comm,
            Set.union_comm] using h }
    have hmin := C.minimal E
    simpa only [ABConnectorPair.cutDefect, E,
      ABConnectorPair.rotateYZX] using hmin

/-- Reverse the A/B orientation of a connector pair. -/
def ABConnectorPair.reverseAB (C : M.ABConnectorPair) :
    (reverseABTriple M).ABConnectorPair where
  aGraph := C.bGraph
  bGraph := C.aGraph
  a_connected := C.b_connected
  b_connected := C.a_connected
  a_contains := by
    intro a ha
    apply C.b_contains a
    rwa [reverseABTriple_aSet] at ha
  b_contains := by
    intro b hb
    apply C.a_contains b
    rwa [reverseABTriple_bSet] at hb
  vertex_disjoint := C.vertex_disjoint.symm
  avoids_terminal_parts := by
    rw [reverseABTriple_xPart, reverseABTriple_yPart,
      reverseABTriple_zPart]
    simpa only [Set.union_comm] using C.avoids_terminal_parts

/-- Minimality of the connector cut-defect is invariant under reversing
the A/B orientation. -/
def MinimalABConnectorPair.reverseAB (C : M.MinimalABConnectorPair) :
    (reverseABTriple M).MinimalABConnectorPair where
  toABConnectorPair := C.toABConnectorPair.reverseAB
  minimal := by
    intro D
    let E : M.ABConnectorPair :=
      { aGraph := D.bGraph
        bGraph := D.aGraph
        a_connected := D.b_connected
        b_connected := D.a_connected
        a_contains := by
          intro a ha
          apply D.b_contains a
          rwa [reverseABTriple_bSet]
        b_contains := by
          intro b hb
          apply D.a_contains b
          rwa [reverseABTriple_aSet]
        vertex_disjoint := D.vertex_disjoint.symm
        avoids_terminal_parts := by
          have h := D.avoids_terminal_parts
          rw [reverseABTriple_xPart, reverseABTriple_yPart,
            reverseABTriple_zPart] at h
          simpa only [Set.union_comm] using h }
    have hmin := C.minimal E
    simpa only [ABConnectorPair.cutDefect, E,
      ABConnectorPair.reverseAB, Nat.add_comm] using hmin

theorem ABConnectorPair.reverseAB_isTwoConnected (C : M.ABConnectorPair)
    (h2 : C.IsTwoConnected) : C.reverseAB.IsTwoConnected := h2.symm

/-! ## The path form of a failure of condition (vii) -/

/-- The three allowed edges between the two attachment triples. -/
def IsMatchedAttachmentPair (a b : V) : Prop :=
  (a = M.xSep.left ∧ b = M.xSep.right) ∨
  (a = M.ySep.left ∧ b = M.ySep.right) ∨
  (a = M.zSep.left ∧ b = M.zSep.right)

theorem a_attachments_pairwise_ne (hA : M.aSet.card = 3) :
    M.xSep.left ≠ M.ySep.left ∧
    M.xSep.left ≠ M.zSep.left ∧
    M.ySep.left ≠ M.zSep.left := by
  constructor
  · intro h
    have hsub : M.aSet ⊆ ({M.ySep.left, M.zSep.left} : Finset V) := by
      intro w hw
      simpa [aSet, h] using hw
    have hle := Finset.card_le_card hsub
    have htwo : ({M.ySep.left, M.zSep.left} : Finset V).card ≤ 2 := by
      exact Finset.card_insert_le _ _
    omega
  constructor
  · intro h
    have hsub : M.aSet ⊆ ({M.ySep.left, M.zSep.left} : Finset V) := by
      intro w hw
      simpa [aSet, h] using hw
    have hle := Finset.card_le_card hsub
    have htwo : ({M.ySep.left, M.zSep.left} : Finset V).card ≤ 2 := by
      exact Finset.card_insert_le _ _
    omega
  · intro h
    have hsub : M.aSet ⊆ ({M.xSep.left, M.zSep.left} : Finset V) := by
      intro w hw
      simpa [aSet, h] using hw
    have hle := Finset.card_le_card hsub
    have htwo : ({M.xSep.left, M.zSep.left} : Finset V).card ≤ 2 := by
      exact Finset.card_insert_le _ _
    omega

theorem b_attachments_pairwise_ne (hB : M.bSet.card = 3) :
    M.xSep.right ≠ M.ySep.right ∧
    M.xSep.right ≠ M.zSep.right ∧
    M.ySep.right ≠ M.zSep.right := by
  constructor
  · intro h
    have hsub : M.bSet ⊆ ({M.ySep.right, M.zSep.right} : Finset V) := by
      intro w hw
      simpa [bSet, h] using hw
    have hle := Finset.card_le_card hsub
    have htwo : ({M.ySep.right, M.zSep.right} : Finset V).card ≤ 2 := by
      exact Finset.card_insert_le _ _
    omega
  constructor
  · intro h
    have hsub : M.bSet ⊆ ({M.ySep.right, M.zSep.right} : Finset V) := by
      intro w hw
      simpa [bSet, h] using hw
    have hle := Finset.card_le_card hsub
    have htwo : ({M.ySep.right, M.zSep.right} : Finset V).card ≤ 2 := by
      exact Finset.card_insert_le _ _
    omega
  · intro h
    have hsub : M.bSet ⊆ ({M.xSep.right, M.zSep.right} : Finset V) := by
      intro w hw
      simpa [bSet, h] using hw
    have hle := Finset.card_le_card hsub
    have htwo : ({M.xSep.right, M.zSep.right} : Finset V).card ≤ 2 := by
      exact Finset.card_insert_le _ _
    omega

/-- Two terminal bridges supported in disjoint deletion components are
vertex-disjoint when their four boundary vertices are distinct on each
side. -/
private theorem terminalBridge_disjoint_of_support
    {pA pB qA qB : V} {P : G.Walk pA pB} {Q : G.Walk qA qB}
    {A B X Y : Finset V}
    (hP : ∀ w, w ∈ P.support → w = pA ∨ w = pB ∨ w ∈ X)
    (hQ : ∀ w, w ∈ Q.support → w = qA ∨ w = qB ∨ w ∈ Y)
    (hpA : pA ∈ A) (hpB : pB ∈ B) (hqA : qA ∈ A) (hqB : qB ∈ B)
    (hpqA : pA ≠ qA) (hpqB : pB ≠ qB)
    (hAB : Disjoint A B)
    (hXA : Disjoint X A) (hXB : Disjoint X B)
    (hYA : Disjoint Y A) (hYB : Disjoint Y B)
    (hXY : Disjoint X Y) :
    Disjoint {w | w ∈ P.support} {w | w ∈ Q.support} := by
  rw [Set.disjoint_left]
  intro w hwP hwQ
  rcases hP w hwP with rfl | rfl | hwX
  · rcases hQ _ hwQ with h | h | hwY
    · exact hpqA h
    · exact Finset.disjoint_left.mp hAB hpA (h ▸ hqB)
    · exact Finset.disjoint_left.mp hYA hwY hpA
  · rcases hQ _ hwQ with h | h | hwY
    · exact Finset.disjoint_left.mp hAB hqA (h ▸ hpB)
    · exact hpqB h
    · exact Finset.disjoint_left.mp hYB hwY hpB
  · rcases hQ w hwQ with h | h | hwY
    · exact Finset.disjoint_left.mp hXA hwX (h ▸ hqA)
    · exact Finset.disjoint_left.mp hXB hwX (h ▸ hqB)
    · exact Finset.disjoint_left.mp hXY hwX hwY

/-- Under the triple/triple hypothesis the three canonical terminal
bridges are pairwise vertex-disjoint. -/
theorem terminalBridges_pairwise_disjoint
    (hA : M.aSet.card = 3) (hB : M.bSet.card = 3) :
    Disjoint {w | w ∈ M.xTerminalBridge.support}
        {w | w ∈ M.yTerminalBridge.support} ∧
      Disjoint {w | w ∈ M.xTerminalBridge.support}
        {w | w ∈ M.zTerminalBridge.support} ∧
      Disjoint {w | w ∈ M.yTerminalBridge.support}
        {w | w ∈ M.zTerminalBridge.support} := by
  obtain ⟨hAxy, hAxz, hAyz⟩ := M.a_attachments_pairwise_ne hA
  obtain ⟨hBxy, hBxz, hByz⟩ := M.b_attachments_pairwise_ne hB
  constructor
  · exact terminalBridge_disjoint_of_support
      (fun w hw ↦ M.xTerminalBridge_support (w := w) hw)
      (fun w hw ↦ M.yTerminalBridge_support (w := w) hw)
      M.xA_mem_aSet M.xB_mem_bSet M.yA_mem_aSet M.yB_mem_bSet
      hAxy hBxy M.aSet_disjoint_bSet
      M.xPart_disjoint_aSet M.xPart_disjoint_bSet
      M.yPart_disjoint_aSet M.yPart_disjoint_bSet
      M.xPart_disjoint_yPart
  constructor
  · exact terminalBridge_disjoint_of_support
      (fun w hw ↦ M.xTerminalBridge_support (w := w) hw)
      (fun w hw ↦ M.zTerminalBridge_support (w := w) hw)
      M.xA_mem_aSet M.xB_mem_bSet M.zA_mem_aSet M.zB_mem_bSet
      hAxz hBxz M.aSet_disjoint_bSet
      M.xPart_disjoint_aSet M.xPart_disjoint_bSet
      M.zPart_disjoint_aSet M.zPart_disjoint_bSet
      M.xPart_disjoint_zPart
  · exact terminalBridge_disjoint_of_support
      (fun w hw ↦ M.yTerminalBridge_support (w := w) hw)
      (fun w hw ↦ M.zTerminalBridge_support (w := w) hw)
      M.yA_mem_aSet M.yB_mem_bSet M.zA_mem_aSet M.zB_mem_bSet
      hAyz hByz M.aSet_disjoint_bSet
      M.yPart_disjoint_aSet M.yPart_disjoint_bSet
      M.zPart_disjoint_aSet M.zPart_disjoint_bSet
      M.yPart_disjoint_zPart

/-- The representative off-diagonal edge contradiction.  The other five
ordered pairs are obtained by permuting `x,y,z`. -/
theorem ABConnectorPair.hasCycleThroughThree_of_adj_xA_yB
    (C : M.ABConnectorPair) (h2 : C.IsTwoConnected)
    (hA : M.aSet.card = 3) (hB : M.bSet.card = 3)
    (hxy : G.Adj M.xSep.left M.ySep.right) :
    HasCycleThroughThree G x y z := by
  obtain ⟨hAxy, hAxz, -⟩ := M.a_attachments_pairwise_ne hA
  obtain ⟨hBxy, -, hByz⟩ := M.b_attachments_pairwise_ne hB
  obtain ⟨Ayz, hAyz, hxAyz, hAyzSub⟩ :=
    exists_subgraph_path_avoiding C.aGraph h2.1
      (u := ABConnectorPair.yAIn (M := M) C)
      (v := ABConnectorPair.zAIn (M := M) C)
      (d := ABConnectorPair.xAIn (M := M) C)
      (fun h ↦ hAxy.symm (congrArg Subtype.val h))
      (fun h ↦ hAxz.symm (congrArg Subtype.val h))
  obtain ⟨Bxz, hBxz, hyBxz, hBxzSub⟩ :=
    exists_subgraph_path_avoiding C.bGraph h2.2
      (u := ABConnectorPair.xBIn (M := M) C)
      (v := ABConnectorPair.zBIn (M := M) C)
      (d := ABConnectorPair.yBIn (M := M) C)
      (fun h ↦ hBxy (congrArg Subtype.val h))
      (fun h ↦ hByz.symm (congrArg Subtype.val h))
  obtain ⟨hXY, hXZ, hYZ⟩ := M.terminalBridges_pairwise_disjoint hA hB
  let p₀ := M.xTerminalBridge
  let p₁ := Bxz
  let p₂ := M.zTerminalBridge.reverse
  let p₃ := Ayz.reverse
  let p₄ := M.yTerminalBridge
  have hp₀₁meet : ∀ w, w ∈ p₀.support → w ∈ p₁.support →
      w = M.xSep.right := by
    intro w hw₀ hw₁
    exact ABConnectorPair.xTerminalBridge_meets_bGraph_only_right
      (M := M) C hw₀ (hBxzSub w hw₁)
  have hp₀₁ : (p₀.append p₁).IsPath :=
    M.xTerminalBridge_isPath.append_of_meet_only_endpoint_wm
      hBxz hp₀₁meet
  have hp₂meet : ∀ w, w ∈ (p₀.append p₁).support →
      w ∈ p₂.support → w = M.zSep.right := by
    intro w hw01 hw₂
    have hwZ : w ∈ M.zTerminalBridge.support := by
      simpa only [p₂, Walk.support_reverse, List.mem_reverse] using hw₂
    have hwCases : w ∈ p₀.support ∨ w ∈ p₁.support := by
      exact (Walk.mem_support_append_iff p₀ p₁).mp hw01
    rcases hwCases with hwX | hwB
    · exact (Set.disjoint_left.mp hXZ hwX hwZ).elim
    · exact ABConnectorPair.zTerminalBridge_meets_bGraph_only_right
        (M := M) C hwZ
        (hBxzSub w hwB)
  have hp₀₁₂ : ((p₀.append p₁).append p₂).IsPath :=
    hp₀₁.append_of_meet_only_endpoint_wm M.zTerminalBridge_isPath.reverse
      hp₂meet
  have hp₃meet : ∀ w, w ∈ ((p₀.append p₁).append p₂).support →
      w ∈ p₃.support → w = M.zSep.left := by
    intro w hw012 hw₃
    have hwAyz : w ∈ Ayz.support := by
      simpa only [p₃, Walk.support_reverse, List.mem_reverse] using hw₃
    have hwA : w ∈ C.aGraph.verts := hAyzSub w hwAyz
    have hwCases : w ∈ p₀.support ∨ w ∈ p₁.support ∨ w ∈ p₂.support := by
      rcases (Walk.mem_support_append_iff (p₀.append p₁) p₂).mp hw012 with
        hw01 | hw₂
      · rcases (Walk.mem_support_append_iff p₀ p₁).mp hw01 with hw₀ | hw₁
        · exact Or.inl hw₀
        · exact Or.inr (Or.inl hw₁)
      · exact Or.inr (Or.inr hw₂)
    rcases hwCases with hwX | hwB | hwZ
    · have hwEq := ABConnectorPair.xTerminalBridge_meets_aGraph_only_left
          (M := M) C hwX hwA
      apply (hxAyz ?_).elim
      change M.xSep.left ∈ Ayz.support
      exact (congrArg (fun v : V ↦ v ∈ Ayz.support) hwEq).mp hwAyz
    · exact (Set.disjoint_left.mp C.vertex_disjoint hwA
        (hBxzSub w hwB)).elim
    · have hwZ' : w ∈ M.zTerminalBridge.support := by
        simpa only [p₂, Walk.support_reverse, List.mem_reverse] using hwZ
      exact ABConnectorPair.zTerminalBridge_meets_aGraph_only_left
        (M := M) C hwZ' hwA
  have hp₀₁₂₃ : (((p₀.append p₁).append p₂).append p₃).IsPath :=
    hp₀₁₂.append_of_meet_only_endpoint_wm hAyz.reverse hp₃meet
  have hp₄meet : ∀ w,
      w ∈ (((p₀.append p₁).append p₂).append p₃).support →
      w ∈ p₄.support → w = M.ySep.left := by
    intro w hw0123 hwY
    have hwCases : w ∈ p₀.support ∨ w ∈ p₁.support ∨
        w ∈ p₂.support ∨ w ∈ p₃.support := by
      rcases (Walk.mem_support_append_iff ((p₀.append p₁).append p₂) p₃).mp
          hw0123 with hw012 | hw₃
      · rcases (Walk.mem_support_append_iff (p₀.append p₁) p₂).mp hw012 with
          hw01 | hw₂
        · rcases (Walk.mem_support_append_iff p₀ p₁).mp hw01 with hw₀ | hw₁
          · exact Or.inl hw₀
          · exact Or.inr (Or.inl hw₁)
        · exact Or.inr (Or.inr (Or.inl hw₂))
      · exact Or.inr (Or.inr (Or.inr hw₃))
    rcases hwCases with hwX | hwB | hwZ | hwA
    · exact (Set.disjoint_left.mp hXY hwX hwY).elim
    · have hwEq := ABConnectorPair.yTerminalBridge_meets_bGraph_only_right
          (M := M) C hwY
          (hBxzSub w hwB)
      apply (hyBxz ?_).elim
      change M.ySep.right ∈ Bxz.support
      exact (congrArg (fun v : V ↦ v ∈ Bxz.support) hwEq).mp hwB
    · have hwZ' : w ∈ M.zTerminalBridge.support := by
        simpa only [p₂, Walk.support_reverse, List.mem_reverse] using hwZ
      exact (Set.disjoint_left.mp hYZ hwY hwZ').elim
    · have hwA' : w ∈ Ayz.support := by
        simpa only [p₃, Walk.support_reverse, List.mem_reverse] using hwA
      exact ABConnectorPair.yTerminalBridge_meets_aGraph_only_left
        (M := M) C hwY (hAyzSub w hwA')
  let detour := (((p₀.append p₁).append p₂).append p₃).append p₄
  have hdetour : detour.IsPath :=
    hp₀₁₂₃.append_of_meet_only_endpoint_wm M.yTerminalBridge_isPath hp₄meet
  let cross : G.Walk M.xSep.left M.ySep.right := .cons hxy .nil
  have hcross : cross.IsPath := by simp [cross, hxy.ne]
  have hxdetour : x ∈ detour.support := by
    change x ∈ ((((p₀.append p₁).append p₂).append p₃).append p₄).support
    apply (Walk.mem_support_append_iff (((p₀.append p₁).append p₂).append p₃) p₄).mpr
    apply Or.inl
    apply (Walk.mem_support_append_iff ((p₀.append p₁).append p₂) p₃).mpr
    apply Or.inl
    apply (Walk.mem_support_append_iff (p₀.append p₁) p₂).mpr
    apply Or.inl
    exact (Walk.mem_support_append_iff p₀ p₁).mpr
      (Or.inl M.x_mem_xTerminalBridge)
  have hydetour : y ∈ detour.support := by
    change y ∈ ((((p₀.append p₁).append p₂).append p₃).append p₄).support
    exact (Walk.mem_support_append_iff (((p₀.append p₁).append p₂).append p₃) p₄).mpr
      (Or.inr M.y_mem_yTerminalBridge)
  have hzdetour : z ∈ detour.support := by
    change z ∈ ((((p₀.append p₁).append p₂).append p₃).append p₄).support
    apply (Walk.mem_support_append_iff (((p₀.append p₁).append p₂).append p₃) p₄).mpr
    apply Or.inl
    apply (Walk.mem_support_append_iff ((p₀.append p₁).append p₂) p₃).mpr
    apply Or.inl
    apply (Walk.mem_support_append_iff (p₀.append p₁) p₂).mpr
    apply Or.inr
    change z ∈ M.zTerminalBridge.reverse.support
    simpa only [Walk.support_reverse, List.mem_reverse] using
      M.z_mem_zTerminalBridge
  have hxyB : x ≠ M.ySep.right := by
    intro h
    have hxB : x ∈ M.bSet :=
      (congrArg (fun v : V ↦ v ∈ M.bSet) h).mpr M.yB_mem_bSet
    exact Finset.disjoint_left.mp M.xPart_disjoint_bSet M.x_mem_xPart
      hxB
  have hmeet : ∀ w, w ∈ detour.support → w ∈ cross.support →
      w = M.xSep.left ∨ w = M.ySep.right := by
    intro w _ hw
    simpa [cross] using hw
  exact hasCycleThroughThree_of_two_clean_arcs detour cross
    hdetour hcross hxdetour M.xSep.x_ne_left hxyB hmeet
    (Or.inl hxdetour) (Or.inl hydetour) (Or.inl hzdetour)

theorem ABConnectorPair.not_adj_xA_yB
    (C : M.ABConnectorPair) (h2 : C.IsTwoConnected)
    (hA : M.aSet.card = 3) (hB : M.bSet.card = 3)
    (hno : ¬HasCycleThroughThree G x y z) :
    ¬G.Adj M.xSep.left M.ySep.right :=
  fun h ↦ hno (ABConnectorPair.hasCycleThroughThree_of_adj_xA_yB
    (M := M) C h2 hA hB h)

/-- The `xA--zB` off-diagonal edge is the `y,z` relabelling of the
representative edge obstruction. -/
theorem ABConnectorPair.hasCycleThroughThree_of_adj_xA_zB
    (C : M.ABConnectorPair) (h2 : C.IsTwoConnected)
    (hA : M.aSet.card = 3) (hB : M.bSet.card = 3)
    (hxz : G.Adj M.xSep.left M.zSep.right) :
    HasCycleThroughThree G x y z := by
  let N := swapYZTriple M
  let C' := ABConnectorPair.swapYZ (M := M) C
  have h2' : C'.IsTwoConnected :=
    ABConnectorPair.swapYZ_isTwoConnected (M := M) C h2
  have hA' : N.aSet.card = 3 := by
    simpa only [N, swapYZTriple_aSet] using hA
  have hB' : N.bSet.card = 3 := by
    simpa only [N, swapYZTriple_bSet] using hB
  have hxy' : G.Adj N.xSep.left N.ySep.right := by
    simpa only [N, swapYZTriple_xSep_left,
      swapYZTriple_ySep_right] using hxz
  obtain ⟨r, W, hW, hx, hz, hy⟩ :=
    ABConnectorPair.hasCycleThroughThree_of_adj_xA_yB
      (M := N) C' h2' hA' hB' hxy'
  exact ⟨r, W, hW, hx, hy, hz⟩

/-- The `yA--zB` off-diagonal edge is the cyclic relabelling of the
representative edge obstruction. -/
theorem ABConnectorPair.hasCycleThroughThree_of_adj_yA_zB
    (C : M.ABConnectorPair) (h2 : C.IsTwoConnected)
    (hA : M.aSet.card = 3) (hB : M.bSet.card = 3)
    (hyz : G.Adj M.ySep.left M.zSep.right) :
    HasCycleThroughThree G x y z := by
  let N := rotateYZXTriple M
  let C' := ABConnectorPair.rotateYZX (M := M) C
  have h2' : C'.IsTwoConnected :=
    ABConnectorPair.rotateYZX_isTwoConnected (M := M) C h2
  have hA' : N.aSet.card = 3 := by
    simpa only [N, rotateYZXTriple_aSet] using hA
  have hB' : N.bSet.card = 3 := by
    simpa only [N, rotateYZXTriple_bSet] using hB
  have hxy' : G.Adj N.xSep.left N.ySep.right := by
    simpa only [N, rotateYZXTriple_xSep_left,
      rotateYZXTriple_ySep_right] using hyz
  obtain ⟨r, W, hW, hy, hz, hx⟩ :=
    ABConnectorPair.hasCycleThroughThree_of_adj_xA_yB
      (M := N) C' h2' hA' hB' hxy'
  exact ⟨r, W, hW, hx, hy, hz⟩

/-- Reversing the connector orientation reduces the `yA--xB` edge to the
representative edge obstruction. -/
theorem ABConnectorPair.hasCycleThroughThree_of_adj_yA_xB
    (C : M.ABConnectorPair) (h2 : C.IsTwoConnected)
    (hA : M.aSet.card = 3) (hB : M.bSet.card = 3)
    (hyx : G.Adj M.ySep.left M.xSep.right) :
    HasCycleThroughThree G x y z := by
  let N := reverseABTriple M
  let C' := ABConnectorPair.reverseAB (M := M) C
  have h2' : C'.IsTwoConnected :=
    ABConnectorPair.reverseAB_isTwoConnected (M := M) C h2
  have hA' : N.aSet.card = 3 := by
    simpa only [N, reverseABTriple_aSet] using hB
  have hB' : N.bSet.card = 3 := by
    simpa only [N, reverseABTriple_bSet] using hA
  have hxy' : G.Adj N.xSep.left N.ySep.right := by
    simpa only [N, reverseABTriple_xSep_left,
      reverseABTriple_ySep_right] using hyx.symm
  exact ABConnectorPair.hasCycleThroughThree_of_adj_xA_yB
    (M := N) C' h2' hA' hB' hxy'

/-- Reversing the connector orientation reduces the `zA--xB` edge to the
`xA--zB` orientation. -/
theorem ABConnectorPair.hasCycleThroughThree_of_adj_zA_xB
    (C : M.ABConnectorPair) (h2 : C.IsTwoConnected)
    (hA : M.aSet.card = 3) (hB : M.bSet.card = 3)
    (hzx : G.Adj M.zSep.left M.xSep.right) :
    HasCycleThroughThree G x y z := by
  let N := reverseABTriple M
  let C' := ABConnectorPair.reverseAB (M := M) C
  have h2' : C'.IsTwoConnected :=
    ABConnectorPair.reverseAB_isTwoConnected (M := M) C h2
  have hA' : N.aSet.card = 3 := by
    simpa only [N, reverseABTriple_aSet] using hB
  have hB' : N.bSet.card = 3 := by
    simpa only [N, reverseABTriple_bSet] using hA
  have hxz' : G.Adj N.xSep.left N.zSep.right := by
    simpa only [N, reverseABTriple_xSep_left,
      reverseABTriple_zSep_right] using hzx.symm
  exact ABConnectorPair.hasCycleThroughThree_of_adj_xA_zB
    (M := N) C' h2' hA' hB' hxz'

/-- Reversing the connector orientation reduces the `zA--yB` edge to the
`yA--zB` orientation. -/
theorem ABConnectorPair.hasCycleThroughThree_of_adj_zA_yB
    (C : M.ABConnectorPair) (h2 : C.IsTwoConnected)
    (hA : M.aSet.card = 3) (hB : M.bSet.card = 3)
    (hzy : G.Adj M.zSep.left M.ySep.right) :
    HasCycleThroughThree G x y z := by
  let N := reverseABTriple M
  let C' := ABConnectorPair.reverseAB (M := M) C
  have h2' : C'.IsTwoConnected :=
    ABConnectorPair.reverseAB_isTwoConnected (M := M) C h2
  have hA' : N.aSet.card = 3 := by
    simpa only [N, reverseABTriple_aSet] using hB
  have hB' : N.bSet.card = 3 := by
    simpa only [N, reverseABTriple_bSet] using hA
  have hyz' : G.Adj N.ySep.left N.zSep.right := by
    simpa only [N, reverseABTriple_ySep_left,
      reverseABTriple_zSep_right] using hzy.symm
  exact ABConnectorPair.hasCycleThroughThree_of_adj_yA_zB
    (M := N) C' h2' hA' hB' hyz'

/-- Condition (vii), matched-edge clause.  Every one of the six
off-diagonal attachment edges gives the representative common-cycle
contradiction after a cyclic relabelling and, when necessary, reversal of
the connector orientation. -/
theorem ABConnectorPair.matched_edges_of_both_triples
    (C : M.ABConnectorPair) (h2 : C.IsTwoConnected)
    (hA : M.aSet.card = 3) (hB : M.bSet.card = 3)
    (hno : ¬HasCycleThroughThree G x y z) :
    ∀ a ∈ M.aSet, ∀ b ∈ M.bSet, G.Adj a b →
      M.IsMatchedAttachmentPair a b := by
  intro a ha b hb hab
  have ha' : a = M.xSep.left ∨ a = M.ySep.left ∨
      a = M.zSep.left := by
    simpa [aSet] using ha
  have hb' : b = M.xSep.right ∨ b = M.ySep.right ∨
      b = M.zSep.right := by
    simpa [bSet] using hb
  rcases ha' with rfl | rfl | rfl
  · rcases hb' with rfl | rfl | rfl
    · exact Or.inl ⟨rfl, rfl⟩
    · exact (hno (ABConnectorPair.hasCycleThroughThree_of_adj_xA_yB
        (M := M) C h2 hA hB hab)).elim
    · exact (hno (ABConnectorPair.hasCycleThroughThree_of_adj_xA_zB
        (M := M) C h2 hA hB hab)).elim
  · rcases hb' with rfl | rfl | rfl
    · exact (hno (ABConnectorPair.hasCycleThroughThree_of_adj_yA_xB
        (M := M) C h2 hA hB hab)).elim
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · exact (hno (ABConnectorPair.hasCycleThroughThree_of_adj_yA_zB
        (M := M) C h2 hA hB hab)).elim
  · rcases hb' with rfl | rfl | rfl
    · exact (hno (ABConnectorPair.hasCycleThroughThree_of_adj_zA_xB
        (M := M) C h2 hA hB hab)).elim
    · exact (hno (ABConnectorPair.hasCycleThroughThree_of_adj_zA_yB
        (M := M) C h2 hA hB hab)).elim
    · exact Or.inr (Or.inr ⟨rfl, rfl⟩)

/-- A path witnessing the normal form used by AHT when condition (vii)
fails: it joins an unmatched `A`--`B` pair and all its other vertices lie
in one component of `G-(A∪B)`. -/
structure MismatchedBoundaryPath (D : Finset V) where
  a : V
  b : V
  a_mem : a ∈ M.aSet
  b_mem : b ∈ M.bSet
  unmatched : ¬M.IsMatchedAttachmentPair a b
  path : G.Walk a b
  path_isPath : path.IsPath
  path_support : ∀ w, w ∈ path.support → w = a ∨ w = b ∨ w ∈ D

/-- Relabel a mismatched path along `swapYZTriple`; the set of the three
matched attachment pairs is unchanged. -/
def MismatchedBoundaryPath.swapYZ {D : Finset V}
    (S : M.MismatchedBoundaryPath D) :
    (swapYZTriple M).MismatchedBoundaryPath D where
  a := S.a
  b := S.b
  a_mem := by
    rw [swapYZTriple_aSet]
    exact S.a_mem
  b_mem := by
    rw [swapYZTriple_bSet]
    exact S.b_mem
  unmatched := by
    intro h
    apply S.unmatched
    rcases h with h | h | h
    · exact Or.inl ⟨by simpa using h.1, by simpa using h.2⟩
    · exact Or.inr (Or.inr ⟨by simpa using h.1, by simpa using h.2⟩)
    · exact Or.inr (Or.inl ⟨by simpa using h.1, by simpa using h.2⟩)
  path := S.path
  path_isPath := S.path_isPath
  path_support := S.path_support

/-- Relabel a mismatched path along the cyclic permutation. -/
def MismatchedBoundaryPath.rotateYZX {D : Finset V}
    (S : M.MismatchedBoundaryPath D) :
    (rotateYZXTriple M).MismatchedBoundaryPath D where
  a := S.a
  b := S.b
  a_mem := by
    rw [rotateYZXTriple_aSet]
    exact S.a_mem
  b_mem := by
    rw [rotateYZXTriple_bSet]
    exact S.b_mem
  unmatched := by
    intro h
    apply S.unmatched
    rcases h with h | h | h
    · exact Or.inr (Or.inl ⟨by simpa using h.1, by simpa using h.2⟩)
    · exact Or.inr (Or.inr ⟨by simpa using h.1, by simpa using h.2⟩)
    · exact Or.inl ⟨by simpa using h.1, by simpa using h.2⟩
  path := S.path
  path_isPath := S.path_isPath
  path_support := S.path_support

/-- Reverse a mismatched A--B path together with the A/B orientation. -/
def MismatchedBoundaryPath.reverseAB {D : Finset V}
    (S : M.MismatchedBoundaryPath D) :
    (reverseABTriple M).MismatchedBoundaryPath D where
  a := S.b
  b := S.a
  a_mem := by
    rw [reverseABTriple_aSet]
    exact S.b_mem
  b_mem := by
    rw [reverseABTriple_bSet]
    exact S.a_mem
  unmatched := by
    intro h
    apply S.unmatched
    rcases h with h | h | h
    · exact Or.inl ⟨by simpa using h.2, by simpa using h.1⟩
    · exact Or.inr (Or.inl ⟨by simpa using h.2, by simpa using h.1⟩)
    · exact Or.inr (Or.inr ⟨by simpa using h.2, by simpa using h.1⟩)
  path := S.path.reverse
  path_isPath := S.path_isPath.reverse
  path_support := by
    intro w hw
    have hwS : w ∈ S.path.support := by
      simpa only [Walk.support_reverse, List.mem_reverse] using hw
    rcases S.path_support w hwS with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr h)

/-- The first/last-contact core of a boundary path.  It starts in the
`A` connector, ends in the `B` connector, and has no other connector
vertices. -/
structure CleanConnectorCore (C : M.ABConnectorPair) {D : Finset V}
    (S : M.MismatchedBoundaryPath D) where
  left : C.aGraph.verts
  right : C.bGraph.verts
  path : G.Walk left.1 right.1
  path_isPath : path.IsPath
  support_subset : ∀ w, w ∈ path.support → w ∈ S.path.support
  meets_aGraph_only_left :
    ∀ w, w ∈ path.support → w ∈ C.aGraph.verts → w = left.1
  meets_bGraph_only_right :
    ∀ w, w ∈ path.support → w ∈ C.bGraph.verts → w = right.1

/-- Trim first at the first `B`-connector hit, then reverse and trim at the
first `A`-connector hit. -/
theorem exists_cleanConnectorCore (C : M.ABConnectorPair)
    {D : Finset V} (S : M.MismatchedBoundaryPath D) :
    Nonempty (M.CleanConnectorCore C S) := by
  classical
  let A : Finset V := C.aGraph.verts.toFinset
  let B : Finset V := C.bGraph.verts.toFinset
  have haA : S.a ∈ A := by
    simpa only [A, Set.mem_toFinset] using C.a_contains S.a S.a_mem
  have hbB : S.b ∈ B := by
    simpa only [B, Set.mem_toFinset] using C.b_contains S.b S.b_mem
  have haB : S.a ∉ B := by
    simp only [B, Set.mem_toFinset]
    intro h
    exact Set.disjoint_left.mp C.vertex_disjoint
      (C.a_contains S.a S.a_mem) h
  obtain ⟨sB, hsBB, q, hq, hqS, hqFirstB⟩ :=
    exists_initialPath_to_finset_wm B haB hbB S.path S.path_isPath
  have hsB_B : sB ∈ C.bGraph.verts := by
    simpa only [B, Set.mem_toFinset] using hsBB
  have hsB_A : sB ∉ A := by
    simp only [A, Set.mem_toFinset]
    intro h
    exact Set.disjoint_left.mp C.vertex_disjoint h hsB_B
  obtain ⟨sA, hsAA, r, hr, hrq, hrFirstA⟩ :=
    exists_initialPath_to_finset_wm A hsB_A haA q.reverse hq.reverse
  have hsA_A : sA ∈ C.aGraph.verts := by
    simpa only [A, Set.mem_toFinset] using hsAA
  let sA' : C.aGraph.verts := ⟨sA, hsA_A⟩
  let sB' : C.bGraph.verts := ⟨sB, hsB_B⟩
  refine ⟨{
    left := sA'
    right := sB'
    path := r.reverse
    path_isPath := hr.reverse
    support_subset := ?_
    meets_aGraph_only_left := ?_
    meets_bGraph_only_right := ?_ }⟩
  · intro w hw
    have hwr : w ∈ r.support := by
      simpa only [Walk.support_reverse, List.mem_reverse] using hw
    have hwqr : w ∈ q.reverse.support := hrq w hwr
    have hwq : w ∈ q.support := by
      simpa only [Walk.support_reverse, List.mem_reverse] using hwqr
    exact hqS w hwq
  · intro w hw hwA
    have hwr : w ∈ r.support := by
      simpa only [Walk.support_reverse, List.mem_reverse] using hw
    have hwA' : w ∈ A := by
      simpa only [A, Set.mem_toFinset] using hwA
    simpa only [sA'] using hrFirstA w hwr hwA'
  · intro w hw hwB
    have hwr : w ∈ r.support := by
      simpa only [Walk.support_reverse, List.mem_reverse] using hw
    have hwqr : w ∈ q.reverse.support := hrq w hwr
    have hwq : w ∈ q.support := by
      simpa only [Walk.support_reverse, List.mem_reverse] using hwqr
    have hwB' : w ∈ B := by
      simpa only [B, Set.mem_toFinset] using hwB
    simpa only [sB'] using hqFirstB w hwq hwB'

/-- A boundary vertex different from the two ends of a mismatched path
does not occur on the path. -/
theorem MismatchedBoundaryPath.not_mem_support_of_boundary_ne
    {D : Finset V} (S : M.MismatchedBoundaryPath D)
    (hD : IsComponentAfterDeleting G (M.aSet ∪ M.bSet) D)
    {w : V} (hwAB : w ∈ M.aSet ∪ M.bSet)
    (hwa : w ≠ S.a) (hwb : w ≠ S.b) :
    w ∉ S.path.support := by
  intro hw
  rcases S.path_support w hw with h | h | hwD
  · exact hwa h
  · exact hwb h
  · exact Finset.disjoint_left.mp hD.2.1 hwD hwAB

/-- The carrier of a routed terminal component has external boundary in
its two deleted separator vertices. -/
theorem routedComponentCarrier_externalBoundary
    {a b t r : V} {pA : G.Walk a t} {pB : G.Walk b t}
    {R : G.Walk r r} (S : RoutedCycleSeparator pA pB R) :
    HasExternalBoundaryIn G
      (componentCarrier (G := G) {S.left, S.right} S.side)
      {S.left, S.right} := by
  intro u hu v huv hvCarrier
  by_contra hvPair
  have huSide : u ∈ (S.side : Set V) := by
    simpa only [mem_componentCarrier] using hu
  have hvAvoid : v ∉
      ((({S.left, S.right} : Finset V) : Set V)) := by
    simpa only [Finset.mem_coe] using hvPair
  have hvSide : v ∈ (S.side : Set V) :=
    ComponentCompl.mem_of_adj u v huSide hvAvoid huv
  apply hvCarrier
  simpa only [mem_componentCarrier] using hvSide

theorem xPart_externalBoundary :
    HasExternalBoundaryIn G M.xPart {M.xSep.left, M.xSep.right} := by
  simpa only [xPart] using routedComponentCarrier_externalBoundary M.xSep

/-- If a walk leaves a finite region immediately after its unique contact
at the initial vertex, and that region contains the entire `x`-component
and both of its boundary vertices, then the initial vertex is not in the
`x`-component. -/
theorem not_mem_xPart_of_exit_with_unique_region_contact
    (U : Finset V) {s t : V} (p : G.Walk s t)
    (hsU : s ∈ U) (htU : t ∉ U)
    (hxSub : M.xPart ⊆ U)
    (hxA : M.xSep.left ∈ U) (hxB : M.xSep.right ∈ U)
    (hOnly : ∀ w, w ∈ p.support → w ∈ U → w = s) :
    s ∉ M.xPart := by
  intro hsX
  have hst : s ≠ t := by
    intro h
    subst t
    exact htU hsU
  have hnon : ¬p.Nil := p.not_nil_of_ne hst
  have huSupport : p.snd ∈ p.support :=
    List.mem_of_mem_tail (p.snd_mem_tail_support hnon)
  have huNotU : p.snd ∉ U := by
    intro huU
    have hus : p.snd = s := hOnly p.snd huSupport huU
    exact (p.adj_snd hnon).ne hus.symm
  by_cases huX : p.snd ∈ M.xPart
  · exact huNotU (hxSub huX)
  · have huPair : p.snd ∈
        ({M.xSep.left, M.xSep.right} : Finset V) :=
      M.xPart_externalBoundary s hsX p.snd (p.adj_snd hnon) huX
    simp only [Finset.mem_insert, Finset.mem_singleton] at huPair
    rcases huPair with huA | huB
    · exact huNotU (huA ▸ hxA)
    · exact huNotU (huB ▸ hxB)

/-- For either the active or the default `B` choice, a clean near-region
exit which avoids the old `X` component starts in `CA ∪ CB`. -/
theorem MinimalABConnectorPair.cleanNearExit_start_mem_carrier
    (C : M.MinimalABConnectorPair)
    (SA : IsolatingCutSide C.aGraph
      (ABConnectorPair.xAIn (M := M) C.toABConnectorPair)
      (ABConnectorPair.yAIn (M := M) C.toABConnectorPair)
      (ABConnectorPair.zAIn (M := M) C.toABConnectorPair))
    (B : BIsolationChoice (M := M) C)
    {s t : V} (p : G.Walk s t)
    (hsNear : s ∈ C.pairNearRegion (M := M) SA B)
    (hAvoidX : ∀ w, w ∈ p.support → w ∉ M.xPart) :
    s ∈ SA.ambientCarrier ∨ s ∈ B.carrier := by
  simp only [MinimalABConnectorPair.pairNearRegion,
    Finset.mem_union] at hsNear
  exact hsNear.resolve_right (hAvoidX s p.start_mem_support)

/-- In the nondegenerate `B` choice, the first vertex of a clean exit from
`CA ∪ CB ∪ X` belongs to one of the two chosen isolating carriers. -/
theorem MinimalABConnectorPair.cleanNearExit_start_mem_activeCarrier
    (C : M.MinimalABConnectorPair)
    (SA : IsolatingCutSide C.aGraph
      (ABConnectorPair.xAIn (M := M) C.toABConnectorPair)
      (ABConnectorPair.yAIn (M := M) C.toABConnectorPair)
      (ABConnectorPair.zAIn (M := M) C.toABConnectorPair))
    (SB : IsolatingCutSide C.bGraph
      (ABConnectorPair.xBIn (M := M) C.toABConnectorPair)
      (ABConnectorPair.yBIn (M := M) C.toABConnectorPair)
      (ABConnectorPair.zBIn (M := M) C.toABConnectorPair))
    {s t : V} (p : G.Walk s t)
    (hsU : s ∈ SA.ambientCarrier ∪ SB.ambientCarrier ∪ M.xPart)
    (htU : t ∉ SA.ambientCarrier ∪ SB.ambientCarrier ∪ M.xPart)
    (hOnly : ∀ w, w ∈ p.support →
      w ∈ SA.ambientCarrier ∪ SB.ambientCarrier ∪ M.xPart → w = s) :
    s ∈ SA.ambientCarrier ∨ s ∈ SB.ambientCarrier := by
  let U : Finset V := SA.ambientCarrier ∪ SB.ambientCarrier ∪ M.xPart
  have hxSub : M.xPart ⊆ U := by
    intro w hw
    simp only [U, Finset.mem_union]
    exact Or.inr hw
  have hxA : M.xSep.left ∈ U := by
    simp only [U, Finset.mem_union]
    left
    left
    apply (SA.mem_ambientCarrier_iff M.xSep.left).mpr
    exact ⟨(ABConnectorPair.xAIn (M := M)
      C.toABConnectorPair).2, SA.a_mem⟩
  have hxB : M.xSep.right ∈ U := by
    simp only [U, Finset.mem_union]
    left
    right
    apply (SB.mem_ambientCarrier_iff M.xSep.right).mpr
    exact ⟨(ABConnectorPair.xBIn (M := M)
      C.toABConnectorPair).2, SB.a_mem⟩
  have hsNotX : s ∉ M.xPart :=
    M.not_mem_xPart_of_exit_with_unique_region_contact U p
      (by simpa only [U] using hsU)
      (by simpa only [U] using htU) hxSub hxA hxB
      (by simpa only [U] using hOnly)
  simp only [Finset.mem_union] at hsU
  exact hsU.resolve_right hsNotX

theorem yPart_externalBoundary :
    HasExternalBoundaryIn G M.yPart {M.ySep.left, M.ySep.right} := by
  simpa only [yPart] using routedComponentCarrier_externalBoundary M.ySep

theorem zPart_externalBoundary :
    HasExternalBoundaryIn G M.zPart {M.zSep.left, M.zSep.right} := by
  simpa only [zPart] using routedComponentCarrier_externalBoundary M.zSep

/-- Once the near endpoint has been classified into `CA ∪ CB`, the clean
exit path avoids all three terminal components.  For `X` this follows from
the last-near-region property.  For `Y` and `Z`, a first entry would have
to cross one of the corresponding two connector boundary vertices; path
cleanliness allows such a boundary vertex only at the far endpoint, while
the near endpoint lies in neither far isolating boundary. -/
theorem MinimalABConnectorPair.cleanNearExit_avoids_terminalParts
    (C : M.MinimalABConnectorPair)
    (SA : IsolatingCutSide C.aGraph
      (ABConnectorPair.xAIn (M := M) C.toABConnectorPair)
      (ABConnectorPair.yAIn (M := M) C.toABConnectorPair)
      (ABConnectorPair.zAIn (M := M) C.toABConnectorPair))
    (B : BIsolationChoice (M := M) C)
    {s t : V} (p : G.Walk s t) (hp : p.IsPath)
    (hsCarrier : s ∈ SA.ambientCarrier ∨ s ∈ B.carrier)
    (htConn : t ∈ C.aGraph.verts ∪ C.bGraph.verts)
    (hmeet : ∀ w, w ∈ p.support →
      w ∈ C.aGraph.verts ∪ C.bGraph.verts → w = s ∨ w = t)
    (hOnlyNear : ∀ w, w ∈ p.support →
      w ∈ C.pairNearRegion (M := M) SA B → w = s) :
    ∀ w, w ∈ p.support →
      w ∉ (M.xPart : Set V) ∪ (M.yPart : Set V) ∪
        (M.zPart : Set V) := by
  have hsConn : s ∈ C.aGraph.verts ∪ C.bGraph.verts := by
    rcases hsCarrier with hsA | hsB
    · exact Or.inl (SA.ambientCarrier_subset hsA)
    · exact Or.inr (B.carrier_subset_bGraph (M := M) hsB)
  have hsParts : s ∉
      (M.xPart : Set V) ∪ (M.yPart : Set V) ∪
        (M.zPart : Set V) := by
    exact Set.disjoint_left.mp C.avoids_terminal_parts hsConn
  have htParts : t ∉
      (M.xPart : Set V) ∪ (M.yPart : Set V) ∪
        (M.zPart : Set V) := by
    exact Set.disjoint_left.mp C.avoids_terminal_parts htConn
  have hsNeYA : s ≠ M.ySep.left := by
    intro h
    rcases hsCarrier with hsA | hsB
    · apply SA.b_not_mem_ambientCarrier
      simpa only [ABConnectorPair.yAIn, h] using hsA
    · exact Set.disjoint_left.mp C.vertex_disjoint
        (C.a_contains M.ySep.left M.yA_mem_aSet)
        (by simpa only [h] using B.carrier_subset_bGraph (M := M) hsB)
  have hsNeZA : s ≠ M.zSep.left := by
    intro h
    rcases hsCarrier with hsA | hsB
    · apply SA.c_not_mem_ambientCarrier
      simpa only [ABConnectorPair.zAIn, h] using hsA
    · exact Set.disjoint_left.mp C.vertex_disjoint
        (C.a_contains M.zSep.left M.zA_mem_aSet)
        (by simpa only [h] using B.carrier_subset_bGraph (M := M) hsB)
  have hsNeYB : s ≠ M.ySep.right := by
    intro h
    rcases hsCarrier with hsA | hsB
    · exact Set.disjoint_left.mp C.vertex_disjoint
        (by simpa only [h] using SA.ambientCarrier_subset hsA)
        (C.b_contains M.ySep.right M.yB_mem_bSet)
    · apply B.yB_not_mem_carrier (M := M)
      simpa only [h] using hsB
  have hsNeZB : s ≠ M.zSep.right := by
    intro h
    rcases hsCarrier with hsA | hsB
    · exact Set.disjoint_left.mp C.vertex_disjoint
        (by simpa only [h] using SA.ambientCarrier_subset hsA)
        (C.b_contains M.zSep.right M.zB_mem_bSet)
    · apply B.zB_not_mem_carrier (M := M)
      simpa only [h] using hsB
  have boundaryOnly {a : V}
      (haConn : a ∈ C.aGraph.verts ∪ C.bGraph.verts)
      (hsa : s ≠ a) (ha : a ∈ p.support) : a = t := by
    rcases hmeet a ha haConn with h | h
    · exact (hsa h.symm).elim
    · exact h
  have hsNotX : s ∉ M.xPart := by
    intro hsX
    apply hsParts
    exact Or.inl (Or.inl hsX)
  have htNotX : t ∉ M.xPart := by
    intro htX
    apply htParts
    exact Or.inl (Or.inl htX)
  have hsNotY : s ∉ M.yPart := by
    intro hsY
    apply hsParts
    exact Or.inl (Or.inr hsY)
  have htNotY : t ∉ M.yPart := by
    intro htY
    apply htParts
    exact Or.inl (Or.inr htY)
  have hsNotZ : s ∉ M.zPart := by
    intro hsZ
    apply hsParts
    exact Or.inr hsZ
  have htNotZ : t ∉ M.zPart := by
    intro htZ
    apply htParts
    exact Or.inr htZ
  have hxAvoid : ∀ w, w ∈ p.support → w ∉ M.xPart := by
    intro w hw hwX
    have hwNear : w ∈ C.pairNearRegion (M := M) SA B := by
      simp only [MinimalABConnectorPair.pairNearRegion,
        Finset.mem_union]
      exact Or.inr hwX
    have hws : w = s := hOnlyNear w hw hwNear
    exact hsNotX (hws ▸ hwX)
  have hYpair : IsComponentAfterDeleting G
      ({M.ySep.left, M.ySep.right} : Finset V) M.yPart := by
    simpa only [yPart] using
      (isComponentAfterDeleting_componentCarrier
        (G := G) ({M.ySep.left, M.ySep.right} : Finset V)
        M.ySep.side)
  have hZpair : IsComponentAfterDeleting G
      ({M.zSep.left, M.zSep.right} : Finset V) M.zPart := by
    simpa only [zPart] using
      (isComponentAfterDeleting_componentCarrier
        (G := G) ({M.zSep.left, M.zSep.right} : Finset V)
        M.zSep.side)
  have hyAvoid : ∀ w, w ∈ p.support → w ∉ M.yPart :=
    hYpair.path_avoids_of_boundary_only_at_end
      M.ySep.left_ne_right p hp hsNotY htNotY hsNeYA hsNeYB
      (boundaryOnly (Or.inl (C.a_contains M.ySep.left M.yA_mem_aSet))
        hsNeYA)
      (boundaryOnly (Or.inr (C.b_contains M.ySep.right M.yB_mem_bSet))
        hsNeYB)
  have hzAvoid : ∀ w, w ∈ p.support → w ∉ M.zPart :=
    hZpair.path_avoids_of_boundary_only_at_end
      M.zSep.left_ne_right p hp hsNotZ htNotZ hsNeZA hsNeZB
      (boundaryOnly (Or.inl (C.a_contains M.zSep.left M.zA_mem_aSet))
        hsNeZA)
      (boundaryOnly (Or.inr (C.b_contains M.zSep.right M.zB_mem_bSet))
        hsNeZB)
  intro w hw hwParts
  rcases hwParts with (hwX | hwY) | hwZ
  · exact hxAvoid w hw hwX
  · exact hyAvoid w hw hwY
  · exact hzAvoid w hw hwZ

/-- Classified form of the full two-cut-avoiding external path.  Its near
end belongs to one chosen isolating carrier, it meets the two connector
graphs only at its ends, and its whole support avoids the three terminal
components and both chosen cut vertices. -/
theorem MinimalABConnectorPair.exists_classifiedCleanNearExit_avoiding_cuts
    (C : M.MinimalABConnectorPair)
    (hA : M.aSet.card = 3)
    (SA : IsolatingCutSide C.aGraph
      (ABConnectorPair.xAIn (M := M) C.toABConnectorPair)
      (ABConnectorPair.yAIn (M := M) C.toABConnectorPair)
      (ABConnectorPair.zAIn (M := M) C.toABConnectorPair))
    (B : BIsolationChoice (M := M) C)
    (hconn : G.Connected)
    (hdelete : ∀ d : V, (G.induce fun w : V ↦ w ≠ d).Connected)
    (hno : ¬HasCycleThroughThree G x y z) :
    ∃ s, (s ∈ SA.ambientCarrier ∨ s ∈ B.carrier) ∧ ∃ t,
      t ∈ C.aGraph.verts ∪ C.bGraph.verts ∧
      t ∉ C.pairNearRegion (M := M) SA B ∧
      ∃ p : G.Walk s t, p.IsPath ∧
        (∀ w, w ∈ p.support →
          w ∈ C.aGraph.verts ∪ C.bGraph.verts → w = s ∨ w = t) ∧
        (∀ w, w ∈ p.support →
          w ∈ C.pairNearRegion (M := M) SA B → w = s) ∧
        (∀ w, w ∈ p.support →
          w ≠ SA.cut.1 ∧ w ≠ B.cut.1) ∧
        ∀ w, w ∈ p.support →
          w ∉ (M.xPart : Set V) ∪ (M.yPart : Set V) ∪
            (M.zPart : Set V) := by
  obtain ⟨s, hsNear, t, htConn, htNear, p, hp, hmeet,
      hOnlyNear, hcuts, hAvoidX⟩ :=
    C.exists_cleanNearExit_avoiding_cuts
      (M := M) hA SA B hconn hdelete hno
  have hsCarrier : s ∈ SA.ambientCarrier ∨ s ∈ B.carrier :=
    C.cleanNearExit_start_mem_carrier (M := M) SA B p hsNear hAvoidX
  have hparts := C.cleanNearExit_avoids_terminalParts (M := M) SA B p hp
    hsCarrier htConn hmeet hOnlyNear
  exact ⟨s, hsCarrier, t, htConn, htNear, p, hp, hmeet,
    hOnlyNear, hcuts, hparts⟩

/-- Consolidated clean-exit package: its near endpoint lies in `CA ∪ CB`,
the path meets the connector graphs only at its ends, and every vertex of
the path avoids `X ∪ Y ∪ Z`. -/
theorem MinimalABConnectorPair.exists_classifiedCleanNearExit
    (C : M.MinimalABConnectorPair)
    (hA : M.aSet.card = 3)
    (SA : IsolatingCutSide C.aGraph
      (ABConnectorPair.xAIn (M := M) C.toABConnectorPair)
      (ABConnectorPair.yAIn (M := M) C.toABConnectorPair)
      (ABConnectorPair.zAIn (M := M) C.toABConnectorPair))
    (B : BIsolationChoice (M := M) C) :
    ∃ s, (s ∈ SA.ambientCarrier ∨ s ∈ B.carrier) ∧ ∃ t,
      t ∈ C.aGraph.verts ∪ C.bGraph.verts ∧
      t ∉ C.pairNearRegion (M := M) SA B ∧
      ∃ p : G.Walk s t, p.IsPath ∧
        (∀ w, w ∈ p.support →
          w ∈ C.aGraph.verts ∪ C.bGraph.verts → w = s ∨ w = t) ∧
        (∀ w, w ∈ p.support →
          w ∈ C.pairNearRegion (M := M) SA B → w = s) ∧
        (∀ w, w ∈ p.support → w ≠ SA.cut.1) ∧
        (∀ w, w ∈ p.support →
          w ∉ (M.xPart : Set V) ∪ (M.yPart : Set V) ∪
            (M.zPart : Set V)) ∧
        ∀ w, w ∈ p.support →
          w ∈ T.xRim.support ∨
            (w ≠ SA.cut.1 ∧ w ≠ B.cut.1) := by
  obtain ⟨s, hsNear, t, htConn, htNear, p, hp, hmeet,
      hOnlyNear, hAvoidCut, hAvoidX, hprovenance⟩ :=
    C.exists_cleanNearExit (M := M) hA SA B
  have hsCarrier : s ∈ SA.ambientCarrier ∨ s ∈ B.carrier :=
    C.cleanNearExit_start_mem_carrier (M := M) SA B p hsNear hAvoidX
  have hparts := C.cleanNearExit_avoids_terminalParts (M := M) SA B p hp
    hsCarrier htConn hmeet hOnlyNear
  exact ⟨s, hsCarrier, t, htConn, htNear, p, hp, hmeet,
    hOnlyNear, hAvoidCut, hparts, hprovenance⟩

/-- The classified clean exit cannot have both ends in the `A` connector
when its near end lies in `CA`: adjoining it is the strict cut-defect ear
exchange, contradicting minimality of the connector pair. -/
theorem MinimalABConnectorPair.false_of_classifiedCleanNearExit_same_A
    (C : M.MinimalABConnectorPair)
    (SA : IsolatingCutSide C.aGraph
      (ABConnectorPair.xAIn (M := M) C.toABConnectorPair)
      (ABConnectorPair.yAIn (M := M) C.toABConnectorPair)
      (ABConnectorPair.zAIn (M := M) C.toABConnectorPair))
    (B : BIsolationChoice (M := M) C)
    {s t : V} (p : G.Walk s t) (hp : p.IsPath)
    (hsCarrier : s ∈ SA.ambientCarrier)
    (htA : t ∈ C.aGraph.verts)
    (htNear : t ∉ C.pairNearRegion (M := M) SA B)
    (hmeet : ∀ w, w ∈ p.support →
      w ∈ C.aGraph.verts ∪ C.bGraph.verts → w = s ∨ w = t)
    (hAvoidCut : ∀ w, w ∈ p.support → w ≠ SA.cut.1)
    (hparts : ∀ w, w ∈ p.support →
      w ∉ (M.xPart : Set V) ∪ (M.yPart : Set V) ∪
        (M.zPart : Set V)) : False := by
  obtain ⟨hsA, hsSide⟩ :=
    (SA.mem_ambientCarrier_iff s).mp hsCarrier
  have htCut : (⟨t, htA⟩ : C.aGraph.verts) ≠ SA.cut := by
    intro h
    exact hAvoidCut t p.end_mem_support (congrArg Subtype.val h)
  have htSide : (⟨t, htA⟩ : C.aGraph.verts) ∉
      ComponentEndBlock.side SA.cut SA.component := by
    intro htSide
    apply htNear
    simp only [MinimalABConnectorPair.pairNearRegion,
      Finset.mem_union]
    exact Or.inl (Or.inl ((SA.mem_ambientCarrier_iff t).mpr
      ⟨htA, htSide⟩))
  exact C.false_of_connector_clean_A_ear (M := M) SA p hp hsA htA
    hsSide htCut htSide hmeet hparts

/-- Therefore, whenever the classified exit starts in `CA`, its far
connector endpoint lies in the `B` connector. -/
theorem MinimalABConnectorPair.classifiedCleanNearExit_far_mem_B_of_start_A
    (C : M.MinimalABConnectorPair)
    (SA : IsolatingCutSide C.aGraph
      (ABConnectorPair.xAIn (M := M) C.toABConnectorPair)
      (ABConnectorPair.yAIn (M := M) C.toABConnectorPair)
      (ABConnectorPair.zAIn (M := M) C.toABConnectorPair))
    (B : BIsolationChoice (M := M) C)
    {s t : V} (p : G.Walk s t) (hp : p.IsPath)
    (hsCarrier : s ∈ SA.ambientCarrier)
    (htConn : t ∈ C.aGraph.verts ∪ C.bGraph.verts)
    (htNear : t ∉ C.pairNearRegion (M := M) SA B)
    (hmeet : ∀ w, w ∈ p.support →
      w ∈ C.aGraph.verts ∪ C.bGraph.verts → w = s ∨ w = t)
    (hAvoidCut : ∀ w, w ∈ p.support → w ≠ SA.cut.1)
    (hparts : ∀ w, w ∈ p.support →
      w ∉ (M.xPart : Set V) ∪ (M.yPart : Set V) ∪
        (M.zPart : Set V)) : t ∈ C.bGraph.verts := by
  rcases htConn with htA | htB
  · exact (C.false_of_classifiedCleanNearExit_same_A (M := M) SA B p hp
      hsCarrier htA htNear hmeet hAvoidCut hparts).elim
  · exact htB

/-- A component violating all three paired-boundary alternatives is
disjoint from each of the three terminal components. -/
theorem component_disjoint_terminal_parts_of_boundary_failure
    (D : Finset V)
    (hD : IsComponentAfterDeleting G (M.aSet ∪ M.bSet) D)
    (hnotX : ¬HasExternalBoundaryIn G D
      {M.xSep.left, M.xSep.right})
    (hnotY : ¬HasExternalBoundaryIn G D
      {M.ySep.left, M.ySep.right})
    (hnotZ : ¬HasExternalBoundaryIn G D
      {M.zSep.left, M.zSep.right}) :
    Disjoint D M.xPart ∧ Disjoint D M.yPart ∧ Disjoint D M.zPart := by
  have one {P U : Finset V}
      (hP : IsComponentAfterDeleting G (M.aSet ∪ M.bSet) P)
      (hboundary : HasExternalBoundaryIn G P U)
      (hnot : ¬HasExternalBoundaryIn G D U) : Disjoint D P := by
    rw [Finset.disjoint_left]
    intro w hwD hwP
    apply hnot
    intro u huD v huv hvD
    have huP : u ∈ P := hP.mem_of_shared hD hwP hwD huD
    apply hboundary u huP v huv
    intro hvP
    exact hvD (hD.mem_of_shared hP hwD hwP hvP)
  exact ⟨one M.xPart_isComponent M.xPart_externalBoundary hnotX,
    one M.yPart_isComponent M.yPart_externalBoundary hnotY,
    one M.zPart_isComponent M.zPart_externalBoundary hnotZ⟩

/-- A trimmed mismatched path can meet a path supported in the deleted
boundary together with a component disjoint from `D` only at its two
connector endpoints. -/
theorem cleanConnectorCore_meets_path_only_ends
    (C : M.ABConnectorPair) {D : Finset V}
    (S : M.MismatchedBoundaryPath D) (core : M.CleanConnectorCore C S)
    (hD : IsComponentAfterDeleting G (M.aSet ∪ M.bSet) D)
    {qStart qEnd : V} {K : Finset V} (Q : G.Walk qStart qEnd)
    (hQ : ∀ w, w ∈ Q.support → w ∈ M.aSet ∪ M.bSet ∨ w ∈ K)
    (hDK : Disjoint D K) :
    ∀ w, w ∈ core.path.support → w ∈ Q.support →
      w = core.left.1 ∨ w = core.right.1 := by
  intro w hwCore hwQ
  have hwS : w ∈ S.path.support := core.support_subset w hwCore
  have left_of_a (hwa : w = S.a) : w = core.left.1 := by
    apply core.meets_aGraph_only_left w hwCore
    rw [hwa]
    exact C.a_contains S.a S.a_mem
  have right_of_b (hwb : w = S.b) : w = core.right.1 := by
    apply core.meets_bGraph_only_right w hwCore
    rw [hwb]
    exact C.b_contains S.b S.b_mem
  rcases hQ w hwQ with hwAB | hwK
  · by_cases hwa : w = S.a
    · exact Or.inl (left_of_a hwa)
    · by_cases hwb : w = S.b
      · exact Or.inr (right_of_b hwb)
      · exact (MismatchedBoundaryPath.not_mem_support_of_boundary_ne
          (M := M) S hD hwAB hwa hwb hwS).elim
  · rcases S.path_support w hwS with hwa | hwb | hwD
    · exact Or.inl (left_of_a hwa)
    · exact Or.inr (right_of_b hwb)
    · exact (Finset.disjoint_left.mp hDK hwD hwK).elim

theorem cleanConnectorCore_meets_xTerminalBridge_only_ends
    (C : M.ABConnectorPair) {D : Finset V}
    (S : M.MismatchedBoundaryPath D) (core : M.CleanConnectorCore C S)
    (hD : IsComponentAfterDeleting G (M.aSet ∪ M.bSet) D)
    (hDX : Disjoint D M.xPart) :
    ∀ w, w ∈ core.path.support → w ∈ M.xTerminalBridge.support →
      w = core.left.1 ∨ w = core.right.1 := by
  apply cleanConnectorCore_meets_path_only_ends (M := M) C S core hD
    M.xTerminalBridge
  · intro w hw
    rcases M.xTerminalBridge_support hw with rfl | rfl | hwX
    · exact Or.inl (Finset.mem_union_left _ M.xA_mem_aSet)
    · exact Or.inl (Finset.mem_union_right _ M.xB_mem_bSet)
    · exact Or.inr hwX
  · exact hDX

theorem cleanConnectorCore_meets_yTerminalBridge_only_ends
    (C : M.ABConnectorPair) {D : Finset V}
    (S : M.MismatchedBoundaryPath D) (core : M.CleanConnectorCore C S)
    (hD : IsComponentAfterDeleting G (M.aSet ∪ M.bSet) D)
    (hDY : Disjoint D M.yPart) :
    ∀ w, w ∈ core.path.support → w ∈ M.yTerminalBridge.support →
      w = core.left.1 ∨ w = core.right.1 := by
  apply cleanConnectorCore_meets_path_only_ends (M := M) C S core hD
    M.yTerminalBridge
  · intro w hw
    rcases M.yTerminalBridge_support hw with rfl | rfl | hwY
    · exact Or.inl (Finset.mem_union_left _ M.yA_mem_aSet)
    · exact Or.inl (Finset.mem_union_right _ M.yB_mem_bSet)
    · exact Or.inr hwY
  · exact hDY

theorem cleanConnectorCore_meets_zTerminalBridge_only_ends
    (C : M.ABConnectorPair) {D : Finset V}
    (S : M.MismatchedBoundaryPath D) (core : M.CleanConnectorCore C S)
    (hD : IsComponentAfterDeleting G (M.aSet ∪ M.bSet) D)
    (hDZ : Disjoint D M.zPart) :
    ∀ w, w ∈ core.path.support → w ∈ M.zTerminalBridge.support →
      w = core.left.1 ∨ w = core.right.1 := by
  apply cleanConnectorCore_meets_path_only_ends (M := M) C S core hD
    M.zTerminalBridge
  · intro w hw
    rcases M.zTerminalBridge_support hw with rfl | rfl | hwZ
    · exact Or.inl (Finset.mem_union_left _ M.zA_mem_aSet)
    · exact Or.inl (Finset.mem_union_right _ M.zB_mem_bSet)
    · exact Or.inr hwZ
  · exact hDZ

theorem cleanConnectorCore_meets_aPath_only_left
    (C : M.ABConnectorPair) {D : Finset V}
    (S : M.MismatchedBoundaryPath D) (core : M.CleanConnectorCore C S)
    {u v : V} (p : G.Walk u v)
    (hsub : ∀ w, w ∈ p.support → w ∈ C.aGraph.verts) :
    ∀ w, w ∈ core.path.support → w ∈ p.support → w = core.left.1 := by
  intro w hwCore hwP
  exact core.meets_aGraph_only_left w hwCore (hsub w hwP)

theorem cleanConnectorCore_meets_bPath_only_right
    (C : M.ABConnectorPair) {D : Finset V}
    (S : M.MismatchedBoundaryPath D) (core : M.CleanConnectorCore C S)
    {u v : V} (p : G.Walk u v)
    (hsub : ∀ w, w ∈ p.support → w ∈ C.bGraph.verts) :
    ∀ w, w ∈ core.path.support → w ∈ p.support → w = core.right.1 := by
  intro w hwCore hwP
  exact core.meets_bGraph_only_right w hwCore (hsub w hwP)

/-- A convenient union form of the preceding clean-intersection lemmas.
Every detour used in the AHT condition-(vii) splice is assembled from
paths in the two connector graphs and the three terminal bridges. -/
theorem cleanConnectorCore_meets_connector_detour_only_ends
    (C : M.ABConnectorPair) {D : Finset V}
    (S : M.MismatchedBoundaryPath D) (core : M.CleanConnectorCore C S)
    (hD : IsComponentAfterDeleting G (M.aSet ∪ M.bSet) D)
    (hDX : Disjoint D M.xPart) (hDY : Disjoint D M.yPart)
    (hDZ : Disjoint D M.zPart)
    {u v : V} (p : G.Walk u v)
    (hclass : ∀ w, w ∈ p.support →
      w ∈ C.aGraph.verts ∨ w ∈ C.bGraph.verts ∨
      w ∈ M.xTerminalBridge.support ∨
      w ∈ M.yTerminalBridge.support ∨
      w ∈ M.zTerminalBridge.support) :
    ∀ w, w ∈ core.path.support → w ∈ p.support →
      w = core.left.1 ∨ w = core.right.1 := by
  intro w hwCore hwP
  rcases hclass w hwP with hwA | hwB | hwX | hwY | hwZ
  · exact Or.inl (core.meets_aGraph_only_left w hwCore hwA)
  · exact Or.inr (core.meets_bGraph_only_right w hwCore hwB)
  · exact cleanConnectorCore_meets_xTerminalBridge_only_ends
      (M := M) C S core hD hDX w hwCore hwX
  · exact cleanConnectorCore_meets_yTerminalBridge_only_ends
      (M := M) C S core hD hDY w hwCore hwY
  · exact cleanConnectorCore_meets_zTerminalBridge_only_ends
      (M := M) C S core hD hDZ w hwCore hwZ

/-- In the normalized off-diagonal case `xA--yB`, the trimmed connector
ends avoid the four other attachments.  These are exactly the inequalities
needed by the two-linkage applications in the five AHT splice cases. -/
theorem cleanConnectorCore_normalized_endpoint_ne
    (C : M.ABConnectorPair) {D : Finset V}
    (S : M.MismatchedBoundaryPath D) (core : M.CleanConnectorCore C S)
    (hD : IsComponentAfterDeleting G (M.aSet ∪ M.bSet) D)
    (hSa : S.a = M.xSep.left) (hSb : S.b = M.ySep.right)
    (hA : M.aSet.card = 3) (hB : M.bSet.card = 3) :
    core.left.1 ≠ M.ySep.left ∧ core.left.1 ≠ M.zSep.left ∧
      core.right.1 ≠ M.xSep.right ∧ core.right.1 ≠ M.zSep.right := by
  obtain ⟨hAxy, hAxz, hAyz⟩ := M.a_attachments_pairwise_ne hA
  obtain ⟨hBxy, hBxz, hByz⟩ := M.b_attachments_pairwise_ne hB
  have hleftS : core.left.1 ∈ S.path.support :=
    core.support_subset _ core.path.start_mem_support
  have hrightS : core.right.1 ∈ S.path.support :=
    core.support_subset _ core.path.end_mem_support
  have avoidA {w : V} (hwA : w ∈ M.aSet)
      (hwx : w ≠ M.xSep.left) : w ∉ S.path.support := by
    apply MismatchedBoundaryPath.not_mem_support_of_boundary_ne (M := M) S hD
      (Finset.mem_union_left M.bSet hwA)
    · simpa only [hSa] using hwx
    · intro h
      have hwB : w ∈ M.bSet := by simpa only [hSb, h] using M.yB_mem_bSet
      exact Finset.disjoint_left.mp M.aSet_disjoint_bSet hwA hwB
  have avoidB {w : V} (hwB : w ∈ M.bSet)
      (hwy : w ≠ M.ySep.right) : w ∉ S.path.support := by
    apply MismatchedBoundaryPath.not_mem_support_of_boundary_ne (M := M) S hD
      (Finset.mem_union_right M.aSet hwB)
    · intro h
      have hwA : w ∈ M.aSet := by simpa only [hSa, h] using M.xA_mem_aSet
      exact Finset.disjoint_left.mp M.aSet_disjoint_bSet hwA hwB
    · simpa only [hSb] using hwy
  constructor
  · intro h
    exact avoidA M.yA_mem_aSet hAxy.symm (h ▸ hleftS)
  constructor
  · intro h
    exact avoidA M.zA_mem_aSet hAxz.symm (h ▸ hleftS)
  constructor
  · intro h
    exact avoidB M.xB_mem_bSet hBxy (h ▸ hrightS)
  · intro h
    exact avoidB M.zB_mem_bSet hByz.symm (h ▸ hrightS)

/-- Assemble the seven-piece detours occurring in the five normalized
condition-(vii) cases.  This keeps the case proofs focused on their
pairwise connector/bridge intersection calculations. -/
private theorem hasCycleThroughThree_of_seven_piece_detour
    {v₀ v₁ v₂ v₃ v₄ v₅ v₆ v₇ w x y z : V}
    (p₀ : G.Walk v₀ v₁) (p₁ : G.Walk v₁ v₂)
    (p₂ : G.Walk v₂ v₃) (p₃ : G.Walk v₃ v₄)
    (p₄ : G.Walk v₄ v₅) (p₅ : G.Walk v₅ v₆)
    (p₆ : G.Walk v₆ v₇) (cross : G.Walk v₀ v₇)
    (hp₀ : p₀.IsPath) (hp₁ : p₁.IsPath) (hp₂ : p₂.IsPath)
    (hp₃ : p₃.IsPath) (hp₄ : p₄.IsPath) (hp₅ : p₅.IsPath)
    (hp₆ : p₆.IsPath) (hcross : cross.IsPath)
    (h₁ : ∀ u, u ∈ p₀.support → u ∈ p₁.support → u = v₁)
    (h₂ : ∀ u, u ∈ (p₀.append p₁).support →
      u ∈ p₂.support → u = v₂)
    (h₃ : ∀ u, u ∈ ((p₀.append p₁).append p₂).support →
      u ∈ p₃.support → u = v₃)
    (h₄ : ∀ u, u ∈ (((p₀.append p₁).append p₂).append p₃).support →
      u ∈ p₄.support → u = v₄)
    (h₅ : ∀ u,
      u ∈ ((((p₀.append p₁).append p₂).append p₃).append p₄).support →
      u ∈ p₅.support → u = v₅)
    (h₆ : ∀ u,
      u ∈ (((((p₀.append p₁).append p₂).append p₃).append p₄).append p₅).support →
      u ∈ p₆.support → u = v₆)
    (hmeet : ∀ u,
      u ∈ ((((((p₀.append p₁).append p₂).append p₃).append p₄).append p₅).append p₆).support →
      u ∈ cross.support → u = v₀ ∨ u = v₇)
    (hw : w ∈
      ((((((p₀.append p₁).append p₂).append p₃).append p₄).append p₅).append p₆).support)
    (hw₀ : w ≠ v₀) (hw₇ : w ≠ v₇)
    (hx : x ∈
      ((((((p₀.append p₁).append p₂).append p₃).append p₄).append p₅).append p₆).support)
    (hy : y ∈
      ((((((p₀.append p₁).append p₂).append p₃).append p₄).append p₅).append p₆).support)
    (hz : z ∈
      ((((((p₀.append p₁).append p₂).append p₃).append p₄).append p₅).append p₆).support) :
    HasCycleThroughThree G x y z := by
  have hp₀₁ : (p₀.append p₁).IsPath :=
    hp₀.append_of_meet_only_endpoint_wm hp₁ h₁
  have hp₀₁₂ : ((p₀.append p₁).append p₂).IsPath :=
    hp₀₁.append_of_meet_only_endpoint_wm hp₂ h₂
  have hp₀₁₂₃ : (((p₀.append p₁).append p₂).append p₃).IsPath :=
    hp₀₁₂.append_of_meet_only_endpoint_wm hp₃ h₃
  have hp₀₁₂₃₄ : ((((p₀.append p₁).append p₂).append p₃).append p₄).IsPath :=
    hp₀₁₂₃.append_of_meet_only_endpoint_wm hp₄ h₄
  have hp₀₁₂₃₄₅ :
      (((((p₀.append p₁).append p₂).append p₃).append p₄).append p₅).IsPath :=
    hp₀₁₂₃₄.append_of_meet_only_endpoint_wm hp₅ h₅
  have hp :
      ((((((p₀.append p₁).append p₂).append p₃).append p₄).append p₅).append p₆).IsPath :=
    hp₀₁₂₃₄₅.append_of_meet_only_endpoint_wm hp₆ h₆
  exact hasCycleThroughThree_of_two_clean_arcs
    ((((((p₀.append p₁).append p₂).append p₃).append p₄).append p₅).append p₆)
    cross hp hcross hw hw₀ hw₇ hmeet
    (Or.inl hx) (Or.inl hy) (Or.inl hz)

/-- The first of the five normalized AHT condition-(vii) splices.  The
two connector linkages use the direct matchings
`xA--sA, yA--zA` and `xB--yB, sB--zB`. -/
private theorem ABConnectorPair.hasCycleThroughThree_of_direct_direct_generic
    (C : M.ABConnectorPair)
    (hA : M.aSet.card = 3) (hB : M.bSet.card = 3)
    {s t : V} (cross : G.Walk s t)
    (hsA : s ∈ C.aGraph.verts) (htB : t ∈ C.bGraph.verts)
    (hcross : cross.IsPath)
    (hcrossClass : ∀ w, w ∈ cross.support →
      (w ∈ C.aGraph.verts ∨ w ∈ C.bGraph.verts ∨
        w ∈ M.xTerminalBridge.support ∨
        w ∈ M.yTerminalBridge.support ∨
        w ∈ M.zTerminalBridge.support) → w = s ∨ w = t)
    (Axs : G.Walk M.xSep.left s)
    (Ayz : G.Walk M.ySep.left M.zSep.left)
    (Bxy : G.Walk M.xSep.right M.ySep.right)
    (Bsz : G.Walk t M.zSep.right)
    (hAxs : Axs.IsPath) (hAyz : Ayz.IsPath)
    (hBxy : Bxy.IsPath) (hBsz : Bsz.IsPath)
    (hAdis : Disjoint {w | w ∈ Axs.support} {w | w ∈ Ayz.support})
    (hBdis : Disjoint {w | w ∈ Bxy.support} {w | w ∈ Bsz.support})
    (hAxsSub : ∀ w, w ∈ Axs.support → w ∈ C.aGraph.verts)
    (hAyzSub : ∀ w, w ∈ Ayz.support → w ∈ C.aGraph.verts)
    (hBxySub : ∀ w, w ∈ Bxy.support → w ∈ C.bGraph.verts)
    (hBszSub : ∀ w, w ∈ Bsz.support → w ∈ C.bGraph.verts) :
    HasCycleThroughThree G x y z := by
  obtain ⟨hXY, hXZ, hYZ⟩ := M.terminalBridges_pairwise_disjoint hA hB
  let X := M.xTerminalBridge
  let Y := M.yTerminalBridge
  let Z := M.zTerminalBridge
  have h01meet : ∀ w, w ∈ Axs.reverse.support → w ∈ X.support →
      w = M.xSep.left := by
    intro w hwA hwX
    have hwA' : w ∈ Axs.support := by
      simpa only [Walk.support_reverse, List.mem_reverse] using hwA
    exact ABConnectorPair.xTerminalBridge_meets_aGraph_only_left
      (M := M) C hwX (hAxsSub w hwA')
  have h01 : (Axs.reverse.append X).IsPath :=
    hAxs.reverse.append_of_meet_only_endpoint_wm
      M.xTerminalBridge_isPath h01meet
  have h2meet : ∀ w, w ∈ (Axs.reverse.append X).support →
      w ∈ Bxy.support → w = M.xSep.right := by
    intro w hw01 hwB
    rcases (Walk.mem_support_append_iff Axs.reverse X).mp hw01 with hwA | hwX
    · have hwA' : w ∈ Axs.support := by
        simpa only [Walk.support_reverse, List.mem_reverse] using hwA
      exact (Set.disjoint_left.mp C.vertex_disjoint
        (hAxsSub w hwA') (hBxySub w hwB)).elim
    · exact ABConnectorPair.xTerminalBridge_meets_bGraph_only_right
        (M := M) C hwX (hBxySub w hwB)
  have h012 : ((Axs.reverse.append X).append Bxy).IsPath :=
    h01.append_of_meet_only_endpoint_wm hBxy h2meet
  have h3meet : ∀ w, w ∈ ((Axs.reverse.append X).append Bxy).support →
      w ∈ Y.reverse.support → w = M.ySep.right := by
    intro w hw012 hwYrev
    have hwY : w ∈ Y.support := by
      simpa only [Walk.support_reverse, List.mem_reverse] using hwYrev
    rcases (Walk.mem_support_append_iff (Axs.reverse.append X) Bxy).mp
        hw012 with hw01 | hwB
    · rcases (Walk.mem_support_append_iff Axs.reverse X).mp hw01 with hwA | hwX
      · have hwA' : w ∈ Axs.support := by
          simpa only [Walk.support_reverse, List.mem_reverse] using hwA
        have hwEq := ABConnectorPair.yTerminalBridge_meets_aGraph_only_left
          (M := M) C hwY (hAxsSub w hwA')
        have hyAxs : M.ySep.left ∈ Axs.support := by
          rw [← hwEq]
          exact hwA'
        exact (Set.disjoint_left.mp hAdis hyAxs Ayz.start_mem_support).elim
      · exact (Set.disjoint_left.mp hXY hwX hwY).elim
    · exact ABConnectorPair.yTerminalBridge_meets_bGraph_only_right
        (M := M) C hwY (hBxySub w hwB)
  have h0123 : (((Axs.reverse.append X).append Bxy).append Y.reverse).IsPath :=
    h012.append_of_meet_only_endpoint_wm M.yTerminalBridge_isPath.reverse h3meet
  have h4meet : ∀ w,
      w ∈ (((Axs.reverse.append X).append Bxy).append Y.reverse).support →
      w ∈ Ayz.support → w = M.ySep.left := by
    intro w hw0123 hwAyz
    rcases (Walk.mem_support_append_iff
        ((Axs.reverse.append X).append Bxy) Y.reverse).mp hw0123 with
      hw012 | hwYrev
    · rcases (Walk.mem_support_append_iff (Axs.reverse.append X) Bxy).mp
          hw012 with hw01 | hwB
      · rcases (Walk.mem_support_append_iff Axs.reverse X).mp hw01 with hwA | hwX
        · have hwA' : w ∈ Axs.support := by
            simpa only [Walk.support_reverse, List.mem_reverse] using hwA
          exact (Set.disjoint_left.mp hAdis hwA' hwAyz).elim
        · have hwEq := ABConnectorPair.xTerminalBridge_meets_aGraph_only_left
            (M := M) C hwX (hAyzSub w hwAyz)
          have hxAyz : M.xSep.left ∈ Ayz.support := by
            rw [← hwEq]
            exact hwAyz
          exact (Set.disjoint_left.mp hAdis Axs.start_mem_support hxAyz).elim
      · exact (Set.disjoint_left.mp C.vertex_disjoint
          (hAyzSub w hwAyz) (hBxySub w hwB)).elim
    · have hwY : w ∈ Y.support := by
        simpa only [Walk.support_reverse, List.mem_reverse] using hwYrev
      exact ABConnectorPair.yTerminalBridge_meets_aGraph_only_left
        (M := M) C hwY (hAyzSub w hwAyz)
  have h01234 :
      ((((Axs.reverse.append X).append Bxy).append Y.reverse).append Ayz).IsPath :=
    h0123.append_of_meet_only_endpoint_wm hAyz h4meet
  have h5meet : ∀ w,
      w ∈ ((((Axs.reverse.append X).append Bxy).append Y.reverse).append Ayz).support →
      w ∈ Z.support → w = M.zSep.left := by
    intro w hw01234 hwZ
    rcases (Walk.mem_support_append_iff
        (((Axs.reverse.append X).append Bxy).append Y.reverse) Ayz).mp
        hw01234 with hw0123 | hwAyz
    · rcases (Walk.mem_support_append_iff
          ((Axs.reverse.append X).append Bxy) Y.reverse).mp hw0123 with
        hw012 | hwYrev
      · rcases (Walk.mem_support_append_iff (Axs.reverse.append X) Bxy).mp
            hw012 with hw01 | hwB
        · rcases (Walk.mem_support_append_iff Axs.reverse X).mp hw01 with hwA | hwX
          · have hwA' : w ∈ Axs.support := by
              simpa only [Walk.support_reverse, List.mem_reverse] using hwA
            have hwEq := ABConnectorPair.zTerminalBridge_meets_aGraph_only_left
              (M := M) C hwZ (hAxsSub w hwA')
            have hzAxs : M.zSep.left ∈ Axs.support := by
              rw [← hwEq]
              exact hwA'
            exact (Set.disjoint_left.mp hAdis hzAxs Ayz.end_mem_support).elim
          · exact (Set.disjoint_left.mp hXZ hwX hwZ).elim
        · have hwEq := ABConnectorPair.zTerminalBridge_meets_bGraph_only_right
            (M := M) C hwZ (hBxySub w hwB)
          have hzBxy : M.zSep.right ∈ Bxy.support := by
            rw [← hwEq]
            exact hwB
          exact (Set.disjoint_left.mp hBdis hzBxy Bsz.end_mem_support).elim
      · have hwY : w ∈ Y.support := by
          simpa only [Walk.support_reverse, List.mem_reverse] using hwYrev
        exact (Set.disjoint_left.mp hYZ hwY hwZ).elim
    · exact ABConnectorPair.zTerminalBridge_meets_aGraph_only_left
        (M := M) C hwZ (hAyzSub w hwAyz)
  have h012345 :
      (((((Axs.reverse.append X).append Bxy).append Y.reverse).append Ayz).append Z).IsPath :=
    h01234.append_of_meet_only_endpoint_wm M.zTerminalBridge_isPath h5meet
  have h6meet : ∀ w,
      w ∈ (((((Axs.reverse.append X).append Bxy).append Y.reverse).append Ayz).append Z).support →
      w ∈ Bsz.reverse.support → w = M.zSep.right := by
    intro w hw012345 hwBrev
    have hwBsz : w ∈ Bsz.support := by
      simpa only [Walk.support_reverse, List.mem_reverse] using hwBrev
    rcases (Walk.mem_support_append_iff
        ((((Axs.reverse.append X).append Bxy).append Y.reverse).append Ayz) Z).mp
        hw012345 with hw01234 | hwZ
    · rcases (Walk.mem_support_append_iff
          (((Axs.reverse.append X).append Bxy).append Y.reverse) Ayz).mp
          hw01234 with hw0123 | hwAyz
      · rcases (Walk.mem_support_append_iff
            ((Axs.reverse.append X).append Bxy) Y.reverse).mp hw0123 with
          hw012 | hwYrev
        · rcases (Walk.mem_support_append_iff (Axs.reverse.append X) Bxy).mp
              hw012 with hw01 | hwBxy
          · rcases (Walk.mem_support_append_iff Axs.reverse X).mp hw01 with
              hwA | hwX
            · have hwA' : w ∈ Axs.support := by
                simpa only [Walk.support_reverse, List.mem_reverse] using hwA
              exact (Set.disjoint_left.mp C.vertex_disjoint
                (hAxsSub w hwA') (hBszSub w hwBsz)).elim
            · have hwEq := ABConnectorPair.xTerminalBridge_meets_bGraph_only_right
                (M := M) C hwX (hBszSub w hwBsz)
              have hxBsz : M.xSep.right ∈ Bsz.support := by
                rw [← hwEq]
                exact hwBsz
              exact (Set.disjoint_left.mp hBdis Bxy.start_mem_support hxBsz).elim
          · exact (Set.disjoint_left.mp hBdis hwBxy hwBsz).elim
        · have hwY : w ∈ Y.support := by
            simpa only [Walk.support_reverse, List.mem_reverse] using hwYrev
          have hwEq := ABConnectorPair.yTerminalBridge_meets_bGraph_only_right
            (M := M) C hwY (hBszSub w hwBsz)
          have hyBsz : M.ySep.right ∈ Bsz.support := by
            rw [← hwEq]
            exact hwBsz
          exact (Set.disjoint_left.mp hBdis Bxy.end_mem_support hyBsz).elim
      · exact (Set.disjoint_left.mp C.vertex_disjoint
          (hAyzSub w hwAyz) (hBszSub w hwBsz)).elim
    · exact ABConnectorPair.zTerminalBridge_meets_bGraph_only_right
        (M := M) C hwZ (hBszSub w hwBsz)
  let detour :=
    (((((Axs.reverse.append X).append Bxy).append Y.reverse).append Ayz).append Z).append
      Bsz.reverse
  have hdetour : detour.IsPath :=
    h012345.append_of_meet_only_endpoint_wm hBsz.reverse h6meet
  have hclass : ∀ w, w ∈ detour.support →
      w ∈ C.aGraph.verts ∨ w ∈ C.bGraph.verts ∨
      w ∈ M.xTerminalBridge.support ∨
      w ∈ M.yTerminalBridge.support ∨
      w ∈ M.zTerminalBridge.support := by
    intro w hw
    dsimp only [detour] at hw
    rcases (Walk.mem_support_append_iff _ _).mp hw with hw012345 | hwBrev
    · rcases (Walk.mem_support_append_iff _ _).mp hw012345 with hw01234 | hwZ
      · rcases (Walk.mem_support_append_iff _ _).mp hw01234 with hw0123 | hwAyz
        · rcases (Walk.mem_support_append_iff _ _).mp hw0123 with hw012 | hwYrev
          · rcases (Walk.mem_support_append_iff _ _).mp hw012 with hw01 | hwB
            · rcases (Walk.mem_support_append_iff _ _).mp hw01 with hwArev | hwX
              · have hwA : w ∈ Axs.support := by
                  simpa only [Walk.support_reverse, List.mem_reverse] using hwArev
                exact Or.inl (hAxsSub w hwA)
              · exact Or.inr (Or.inr (Or.inl hwX))
            · exact Or.inr (Or.inl (hBxySub w hwB))
          · have hwY : w ∈ Y.support := by
              simpa only [Walk.support_reverse, List.mem_reverse] using hwYrev
            exact Or.inr (Or.inr (Or.inr (Or.inl hwY)))
        · exact Or.inl (hAyzSub w hwAyz)
      · exact Or.inr (Or.inr (Or.inr (Or.inr hwZ)))
    · have hwBsz : w ∈ Bsz.support := by
        simpa only [Walk.support_reverse, List.mem_reverse] using hwBrev
      exact Or.inr (Or.inl (hBszSub w hwBsz))
  have hmeet : ∀ w, w ∈ detour.support → w ∈ cross.support →
      w = s ∨ w = t := by
    intro w hwDetour hwCross
    exact hcrossClass w hwCross (hclass w hwDetour)
  have hxdetour : x ∈ detour.support := by
    dsimp only [detour]
    simp only [Walk.mem_support_append_iff]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl
      (Or.inr M.x_mem_xTerminalBridge)))))
  have hydetour : y ∈ detour.support := by
    dsimp only [detour]
    simp only [Walk.mem_support_append_iff, Walk.support_reverse,
      List.mem_reverse]
    exact Or.inl (Or.inl (Or.inl (Or.inr M.y_mem_yTerminalBridge)))
  have hzdetour : z ∈ detour.support := by
    dsimp only [detour]
    simp only [Walk.mem_support_append_iff]
    exact Or.inl (Or.inr M.z_mem_zTerminalBridge)
  have hxleft : x ≠ s := by
    intro h
    have hxPart : s ∈ M.xPart := by
      rw [← h]
      exact M.x_mem_xPart
    apply Set.disjoint_left.mp C.avoids_terminal_parts
      (Or.inl hsA)
      (Or.inl (Or.inl hxPart))
  have hxright : x ≠ t := by
    intro h
    have hxPart : t ∈ M.xPart := by
      rw [← h]
      exact M.x_mem_xPart
    apply Set.disjoint_left.mp C.avoids_terminal_parts
      (Or.inr htB)
      (Or.inl (Or.inl hxPart))
  exact hasCycleThroughThree_of_two_clean_arcs detour cross
    hdetour hcross hxdetour hxleft hxright hmeet
    (Or.inl hxdetour) (Or.inl hydetour) (Or.inl hzdetour)

/-- Condition-(vii) wrapper for the generic direct/direct splice. -/
private theorem ABConnectorPair.hasCycleThroughThree_of_normalized_direct_direct
    (C : M.ABConnectorPair)
    (hA : M.aSet.card = 3) (hB : M.bSet.card = 3)
    {D : Finset V} (S : M.MismatchedBoundaryPath D)
    (core : M.CleanConnectorCore C S)
    (hD : IsComponentAfterDeleting G (M.aSet ∪ M.bSet) D)
    (hDX : Disjoint D M.xPart) (hDY : Disjoint D M.yPart)
    (hDZ : Disjoint D M.zPart)
    (Axs : G.Walk M.xSep.left core.left.1)
    (Ayz : G.Walk M.ySep.left M.zSep.left)
    (Bxy : G.Walk M.xSep.right M.ySep.right)
    (Bsz : G.Walk core.right.1 M.zSep.right)
    (hAxs : Axs.IsPath) (hAyz : Ayz.IsPath)
    (hBxy : Bxy.IsPath) (hBsz : Bsz.IsPath)
    (hAdis : Disjoint {w | w ∈ Axs.support} {w | w ∈ Ayz.support})
    (hBdis : Disjoint {w | w ∈ Bxy.support} {w | w ∈ Bsz.support})
    (hAxsSub : ∀ w, w ∈ Axs.support → w ∈ C.aGraph.verts)
    (hAyzSub : ∀ w, w ∈ Ayz.support → w ∈ C.aGraph.verts)
    (hBxySub : ∀ w, w ∈ Bxy.support → w ∈ C.bGraph.verts)
    (hBszSub : ∀ w, w ∈ Bsz.support → w ∈ C.bGraph.verts) :
    HasCycleThroughThree G x y z := by
  apply ABConnectorPair.hasCycleThroughThree_of_direct_direct_generic
    (M := M) C hA hB core.path core.left.2 core.right.2
      core.path_isPath ?_ Axs Ayz Bxy Bsz hAxs hAyz hBxy hBsz
      hAdis hBdis hAxsSub hAyzSub hBxySub hBszSub
  intro w hwCore hwClass
  rcases hwClass with hwA | hwB | hwX | hwY | hwZ
  · exact Or.inl (core.meets_aGraph_only_left w hwCore hwA)
  · exact Or.inr (core.meets_bGraph_only_right w hwCore hwB)
  · exact cleanConnectorCore_meets_xTerminalBridge_only_ends
      (M := M) C S core hD hDX w hwCore hwX
  · exact cleanConnectorCore_meets_yTerminalBridge_only_ends
      (M := M) C S core hD hDY w hwCore hwY
  · exact cleanConnectorCore_meets_zTerminalBridge_only_ends
      (M := M) C S core hD hDZ w hwCore hwZ

/-- The generic second A-side splice: the A-linkage is direct while the
B-linkage uses the crossed matching, and the cross path has no further
intersection with the five constituent regions of the detour. -/
private theorem ABConnectorPair.hasCycleThroughThree_of_direct_cross_generic
    (C : M.ABConnectorPair)
    (hA : M.aSet.card = 3) (hB : M.bSet.card = 3)
    {s t : V} (cross : G.Walk s t)
    (hsA : s ∈ C.aGraph.verts) (htB : t ∈ C.bGraph.verts)
    (hcross : cross.IsPath)
    (hcrossClass : ∀ w, w ∈ cross.support →
      (w ∈ C.aGraph.verts ∨ w ∈ C.bGraph.verts ∨
        w ∈ M.xTerminalBridge.support ∨ w ∈ M.yTerminalBridge.support ∨
        w ∈ M.zTerminalBridge.support) → w = s ∨ w = t)
    (Axs : G.Walk M.xSep.left s)
    (Ayz : G.Walk M.ySep.left M.zSep.left)
    (Bxz : G.Walk M.xSep.right M.zSep.right)
    (Bsy : G.Walk t M.ySep.right)
    (hAxs : Axs.IsPath) (hAyz : Ayz.IsPath)
    (hBxz : Bxz.IsPath) (hBsy : Bsy.IsPath)
    (hAdis : Disjoint {w | w ∈ Axs.support} {w | w ∈ Ayz.support})
    (hBdis : Disjoint {w | w ∈ Bxz.support} {w | w ∈ Bsy.support})
    (hAxsSub : ∀ w, w ∈ Axs.support → w ∈ C.aGraph.verts)
    (hAyzSub : ∀ w, w ∈ Ayz.support → w ∈ C.aGraph.verts)
    (hBxzSub : ∀ w, w ∈ Bxz.support → w ∈ C.bGraph.verts)
    (hBsySub : ∀ w, w ∈ Bsy.support → w ∈ C.bGraph.verts) :
    HasCycleThroughThree G x y z := by
  obtain ⟨hXY, hXZ, hYZ⟩ := M.terminalBridges_pairwise_disjoint hA hB
  let X := M.xTerminalBridge
  let Y := M.yTerminalBridge
  let Z := M.zTerminalBridge
  have h₁ : ∀ w, w ∈ Axs.reverse.support → w ∈ X.support →
      w = M.xSep.left := by
    intro w hwA hwX
    have hwA' : w ∈ Axs.support := by
      simpa only [Walk.support_reverse, List.mem_reverse] using hwA
    exact ABConnectorPair.xTerminalBridge_meets_aGraph_only_left
      (M := M) C hwX (hAxsSub w hwA')
  have h₂ : ∀ w, w ∈ (Axs.reverse.append X).support →
      w ∈ Bxz.support → w = M.xSep.right := by
    intro w hw01 hwB
    rcases (Walk.mem_support_append_iff _ _).mp hw01 with hwA | hwX
    · have hwA' : w ∈ Axs.support := by
        simpa only [Walk.support_reverse, List.mem_reverse] using hwA
      exact (Set.disjoint_left.mp C.vertex_disjoint
        (hAxsSub w hwA') (hBxzSub w hwB)).elim
    · exact ABConnectorPair.xTerminalBridge_meets_bGraph_only_right
        (M := M) C hwX (hBxzSub w hwB)
  have h₃ : ∀ w, w ∈ ((Axs.reverse.append X).append Bxz).support →
      w ∈ Z.reverse.support → w = M.zSep.right := by
    intro w hw012 hwZrev
    have hwZ : w ∈ Z.support := by
      simpa only [Walk.support_reverse, List.mem_reverse] using hwZrev
    rcases (Walk.mem_support_append_iff _ _).mp hw012 with hw01 | hwB
    · rcases (Walk.mem_support_append_iff _ _).mp hw01 with hwA | hwX
      · have hwA' : w ∈ Axs.support := by
          simpa only [Walk.support_reverse, List.mem_reverse] using hwA
        have hwEq := ABConnectorPair.zTerminalBridge_meets_aGraph_only_left
          (M := M) C hwZ (hAxsSub w hwA')
        have hzAxs : M.zSep.left ∈ Axs.support := by
          rw [← hwEq]
          exact hwA'
        exact (Set.disjoint_left.mp hAdis hzAxs Ayz.end_mem_support).elim
      · exact (Set.disjoint_left.mp hXZ hwX hwZ).elim
    · exact ABConnectorPair.zTerminalBridge_meets_bGraph_only_right
        (M := M) C hwZ (hBxzSub w hwB)
  have h₄ : ∀ w,
      w ∈ (((Axs.reverse.append X).append Bxz).append Z.reverse).support →
      w ∈ Ayz.reverse.support → w = M.zSep.left := by
    intro w hw0123 hwAyzRev
    have hwAyz : w ∈ Ayz.support := by
      simpa only [Walk.support_reverse, List.mem_reverse] using hwAyzRev
    rcases (Walk.mem_support_append_iff _ _).mp hw0123 with hw012 | hwZrev
    · rcases (Walk.mem_support_append_iff _ _).mp hw012 with hw01 | hwB
      · rcases (Walk.mem_support_append_iff _ _).mp hw01 with hwA | hwX
        · have hwA' : w ∈ Axs.support := by
            simpa only [Walk.support_reverse, List.mem_reverse] using hwA
          exact (Set.disjoint_left.mp hAdis hwA' hwAyz).elim
        · have hwEq := ABConnectorPair.xTerminalBridge_meets_aGraph_only_left
            (M := M) C hwX (hAyzSub w hwAyz)
          have hxAyz : M.xSep.left ∈ Ayz.support := by
            rw [← hwEq]
            exact hwAyz
          exact (Set.disjoint_left.mp hAdis Axs.start_mem_support hxAyz).elim
      · exact (Set.disjoint_left.mp C.vertex_disjoint
          (hAyzSub w hwAyz) (hBxzSub w hwB)).elim
    · have hwZ : w ∈ Z.support := by
        simpa only [Walk.support_reverse, List.mem_reverse] using hwZrev
      exact ABConnectorPair.zTerminalBridge_meets_aGraph_only_left
        (M := M) C hwZ (hAyzSub w hwAyz)
  have h₅ : ∀ w,
      w ∈ ((((Axs.reverse.append X).append Bxz).append Z.reverse).append Ayz.reverse).support →
      w ∈ Y.support → w = M.ySep.left := by
    intro w hw01234 hwY
    rcases (Walk.mem_support_append_iff _ _).mp hw01234 with hw0123 | hwAyzRev
    · rcases (Walk.mem_support_append_iff _ _).mp hw0123 with hw012 | hwZrev
      · rcases (Walk.mem_support_append_iff _ _).mp hw012 with hw01 | hwB
        · rcases (Walk.mem_support_append_iff _ _).mp hw01 with hwA | hwX
          · have hwA' : w ∈ Axs.support := by
              simpa only [Walk.support_reverse, List.mem_reverse] using hwA
            have hwEq := ABConnectorPair.yTerminalBridge_meets_aGraph_only_left
              (M := M) C hwY (hAxsSub w hwA')
            have hyAxs : M.ySep.left ∈ Axs.support := by
              rw [← hwEq]
              exact hwA'
            exact (Set.disjoint_left.mp hAdis hyAxs Ayz.start_mem_support).elim
          · exact (Set.disjoint_left.mp hXY hwX hwY).elim
        · have hwEq := ABConnectorPair.yTerminalBridge_meets_bGraph_only_right
            (M := M) C hwY (hBxzSub w hwB)
          have hyBxz : M.ySep.right ∈ Bxz.support := by
            rw [← hwEq]
            exact hwB
          exact (Set.disjoint_left.mp hBdis hyBxz Bsy.end_mem_support).elim
      · have hwZ : w ∈ Z.support := by
          simpa only [Walk.support_reverse, List.mem_reverse] using hwZrev
        exact (Set.disjoint_left.mp hYZ hwY hwZ).elim
    · have hwAyz : w ∈ Ayz.support := by
        simpa only [Walk.support_reverse, List.mem_reverse] using hwAyzRev
      exact ABConnectorPair.yTerminalBridge_meets_aGraph_only_left
        (M := M) C hwY (hAyzSub w hwAyz)
  have h₆ : ∀ w,
      w ∈ (((((Axs.reverse.append X).append Bxz).append Z.reverse).append Ayz.reverse).append
        Y).support →
      w ∈ Bsy.reverse.support → w = M.ySep.right := by
    intro w hw012345 hwBsyRev
    have hwBsy : w ∈ Bsy.support := by
      simpa only [Walk.support_reverse, List.mem_reverse] using hwBsyRev
    rcases (Walk.mem_support_append_iff _ _).mp hw012345 with hw01234 | hwY
    · rcases (Walk.mem_support_append_iff _ _).mp hw01234 with hw0123 | hwAyzRev
      · rcases (Walk.mem_support_append_iff _ _).mp hw0123 with hw012 | hwZrev
        · rcases (Walk.mem_support_append_iff _ _).mp hw012 with hw01 | hwB
          · rcases (Walk.mem_support_append_iff _ _).mp hw01 with hwA | hwX
            · have hwA' : w ∈ Axs.support := by
                simpa only [Walk.support_reverse, List.mem_reverse] using hwA
              exact (Set.disjoint_left.mp C.vertex_disjoint
                (hAxsSub w hwA') (hBsySub w hwBsy)).elim
            · have hwEq := ABConnectorPair.xTerminalBridge_meets_bGraph_only_right
                (M := M) C hwX (hBsySub w hwBsy)
              have hxBsy : M.xSep.right ∈ Bsy.support := by
                rw [← hwEq]
                exact hwBsy
              exact (Set.disjoint_left.mp hBdis Bxz.start_mem_support hxBsy).elim
          · exact (Set.disjoint_left.mp hBdis hwB hwBsy).elim
        · have hwZ : w ∈ Z.support := by
            simpa only [Walk.support_reverse, List.mem_reverse] using hwZrev
          have hwEq := ABConnectorPair.zTerminalBridge_meets_bGraph_only_right
            (M := M) C hwZ (hBsySub w hwBsy)
          have hzBsy : M.zSep.right ∈ Bsy.support := by
            rw [← hwEq]
            exact hwBsy
          exact (Set.disjoint_left.mp hBdis Bxz.end_mem_support hzBsy).elim
      · have hwAyz : w ∈ Ayz.support := by
          simpa only [Walk.support_reverse, List.mem_reverse] using hwAyzRev
        exact (Set.disjoint_left.mp C.vertex_disjoint
          (hAyzSub w hwAyz) (hBsySub w hwBsy)).elim
    · exact ABConnectorPair.yTerminalBridge_meets_bGraph_only_right
        (M := M) C hwY (hBsySub w hwBsy)
  let detour := (((((Axs.reverse.append X).append Bxz).append Z.reverse).append Ayz.reverse).append
    Y).append Bsy.reverse
  have hclass : ∀ w, w ∈ detour.support →
      w ∈ C.aGraph.verts ∨ w ∈ C.bGraph.verts ∨
      w ∈ M.xTerminalBridge.support ∨ w ∈ M.yTerminalBridge.support ∨
      w ∈ M.zTerminalBridge.support := by
    intro w hw
    dsimp only [detour] at hw
    rcases (Walk.mem_support_append_iff _ _).mp hw with hw012345 | hwBsyRev
    · rcases (Walk.mem_support_append_iff _ _).mp hw012345 with hw01234 | hwY
      · rcases (Walk.mem_support_append_iff _ _).mp hw01234 with hw0123 | hwAyzRev
        · rcases (Walk.mem_support_append_iff _ _).mp hw0123 with hw012 | hwZrev
          · rcases (Walk.mem_support_append_iff _ _).mp hw012 with hw01 | hwB
            · rcases (Walk.mem_support_append_iff _ _).mp hw01 with hwARev | hwX
              · have hwA : w ∈ Axs.support := by
                  simpa only [Walk.support_reverse, List.mem_reverse] using hwARev
                exact Or.inl (hAxsSub w hwA)
              · exact Or.inr (Or.inr (Or.inl hwX))
            · exact Or.inr (Or.inl (hBxzSub w hwB))
          · have hwZ : w ∈ Z.support := by
              simpa only [Walk.support_reverse, List.mem_reverse] using hwZrev
            exact Or.inr (Or.inr (Or.inr (Or.inr hwZ)))
        · have hwAyz : w ∈ Ayz.support := by
            simpa only [Walk.support_reverse, List.mem_reverse] using hwAyzRev
          exact Or.inl (hAyzSub w hwAyz)
      · exact Or.inr (Or.inr (Or.inr (Or.inl hwY)))
    · have hwBsy : w ∈ Bsy.support := by
        simpa only [Walk.support_reverse, List.mem_reverse] using hwBsyRev
      exact Or.inr (Or.inl (hBsySub w hwBsy))
  have hmeet : ∀ w, w ∈ detour.support → w ∈ cross.support →
      w = s ∨ w = t := by
    intro w hwDetour hwCross
    exact hcrossClass w hwCross (hclass w hwDetour)
  have hxdetour : x ∈ detour.support := by
    dsimp only [detour]
    simp only [Walk.mem_support_append_iff]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl
      (Or.inr M.x_mem_xTerminalBridge)))))
  have hydetour : y ∈ detour.support := by
    dsimp only [detour]
    simp only [Walk.mem_support_append_iff]
    exact Or.inl (Or.inr M.y_mem_yTerminalBridge)
  have hzdetour : z ∈ detour.support := by
    dsimp only [detour]
    simp only [Walk.mem_support_append_iff, Walk.support_reverse,
      List.mem_reverse]
    exact Or.inl (Or.inl (Or.inl
      (Or.inr M.z_mem_zTerminalBridge)))
  have hxleft : x ≠ s := by
    intro h
    have hxPart : s ∈ M.xPart := by rw [← h]; exact M.x_mem_xPart
    exact Set.disjoint_left.mp C.avoids_terminal_parts
      (Or.inl hsA) (Or.inl (Or.inl hxPart))
  have hxright : x ≠ t := by
    intro h
    have hxPart : t ∈ M.xPart := by rw [← h]; exact M.x_mem_xPart
    exact Set.disjoint_left.mp C.avoids_terminal_parts
      (Or.inr htB) (Or.inl (Or.inl hxPart))
  exact hasCycleThroughThree_of_seven_piece_detour
    Axs.reverse X Bxz Z.reverse Ayz.reverse Y Bsy.reverse cross
    hAxs.reverse M.xTerminalBridge_isPath hBxz
    M.zTerminalBridge_isPath.reverse hAyz.reverse
    M.yTerminalBridge_isPath hBsy.reverse hcross
    h₁ h₂ h₃ h₄ h₅ h₆ hmeet hxdetour hxleft hxright
    hxdetour hydetour hzdetour

/-- The p.15 contradiction once the clean external path starts in the
chosen A-isolating carrier.  The two possible B-linkage matchings are the
direct/direct and direct/cross splices above. -/
theorem MinimalABConnectorPair.false_of_classifiedCleanNearExit_start_A
    (C : M.MinimalABConnectorPair)
    (hA : M.aSet.card = 3) (hB : M.bSet.card = 3)
    (SA : IsolatingCutSide C.aGraph
      (ABConnectorPair.xAIn (M := M) C.toABConnectorPair)
      (ABConnectorPair.yAIn (M := M) C.toABConnectorPair)
      (ABConnectorPair.zAIn (M := M) C.toABConnectorPair))
    (B : BIsolationChoice (M := M) C)
    {s t : V} (p : G.Walk s t) (hp : p.IsPath)
    (hsA : s ∈ SA.ambientCarrier)
    (htConn : t ∈ C.aGraph.verts ∪ C.bGraph.verts)
    (htNear : t ∉ C.pairNearRegion (M := M) SA B)
    (hmeet : ∀ w, w ∈ p.support →
      w ∈ C.aGraph.verts ∪ C.bGraph.verts → w = s ∨ w = t)
    (hcuts : ∀ w, w ∈ p.support →
      w ≠ SA.cut.1 ∧ w ≠ B.cut.1)
    (hparts : ∀ w, w ∈ p.support →
      w ∉ (M.xPart : Set V) ∪ (M.yPart : Set V) ∪
        (M.zPart : Set V))
    (hno : ¬HasCycleThroughThree G x y z) : False := by
  classical
  have htB : t ∈ C.bGraph.verts :=
    C.classifiedCleanNearExit_far_mem_B_of_start_A (M := M)
      SA B p hp hsA htConn htNear hmeet
      (fun w hw ↦ (hcuts w hw).1) hparts
  obtain ⟨hsGraph, hsSide⟩ := (SA.mem_ambientCarrier_iff s).mp hsA
  obtain ⟨Axs, Ayz, hAxs, hAyz, hAdis, hAxsSub, hAyzSub⟩ :=
    SA.exists_ambient_direct_linkage C.a_connected hsSide
  let xB := ABConnectorPair.xBIn (M := M) C.toABConnectorPair
  let yB := ABConnectorPair.yBIn (M := M) C.toABConnectorPair
  let zB := ABConnectorPair.zBIn (M := M) C.toABConnectorPair
  let tB : C.bGraph.verts := ⟨t, htB⟩
  obtain ⟨p₀, hp₀⟩ := (C.b_connected.coe xB yB).exists_isPath
  have htNotCarrier : t ∉ B.carrier := by
    intro htCarrier
    apply htNear
    simp only [MinimalABConnectorPair.pairNearRegion, Finset.mem_union]
    exact Or.inl (Or.inr htCarrier)
  have htNotCut : t ≠ B.cut.1 := (hcuts t p.end_mem_support).2
  have hnone : ∀ u : C.bGraph.verts,
      ¬Erdos599.Countable.Separates C.bGraph.coe ({xB, tB} : Set C.bGraph.verts)
        ({yB, zB} : Set C.bGraph.verts) ({u} : Set C.bGraph.verts) := by
    cases B with
    | active SB hSB =>
        apply C.no_singleton_B_separator_of_active (M := M) hB SB hSB
        · intro htSide
          apply htNotCarrier
          exact (SB.mem_ambientCarrier_iff t).mpr ⟨htB, htSide⟩
        · intro htCut
          exact htNotCut (congrArg Subtype.val htCut)
    | default hnone =>
        apply C.no_singleton_B_separator_of_default (M := M) hB hnone
        intro htX
        apply htNotCut
        simpa only [BIsolationChoice.cut] using congrArg Subtype.val htX
  have hcrossClass : ∀ w, w ∈ p.support →
      (w ∈ C.aGraph.verts ∨ w ∈ C.bGraph.verts ∨
        w ∈ M.xTerminalBridge.support ∨
        w ∈ M.yTerminalBridge.support ∨
        w ∈ M.zTerminalBridge.support) → w = s ∨ w = t := by
    intro w hw hwClass
    rcases hwClass with hwA | hwB | hwX | hwY | hwZ
    · exact hmeet w hw (Or.inl hwA)
    · exact hmeet w hw (Or.inr hwB)
    · rcases M.xTerminalBridge_support hwX with rfl | rfl | hwPart
      · exact hmeet _ hw (Or.inl (C.a_contains _ M.xA_mem_aSet))
      · exact hmeet _ hw (Or.inr (C.b_contains _ M.xB_mem_bSet))
      · exact False.elim ((hparts w hw) (Or.inl (Or.inl hwPart)))
    · rcases M.yTerminalBridge_support hwY with rfl | rfl | hwPart
      · exact hmeet _ hw (Or.inl (C.a_contains _ M.yA_mem_aSet))
      · exact hmeet _ hw (Or.inr (C.b_contains _ M.yB_mem_bSet))
      · exact False.elim ((hparts w hw) (Or.inl (Or.inr hwPart)))
    · rcases M.zTerminalBridge_support hwZ with rfl | rfl | hwPart
      · exact hmeet _ hw (Or.inl (C.a_contains _ M.zA_mem_aSet))
      · exact hmeet _ hw (Or.inr (C.b_contains _ M.zB_mem_bSet))
      · exact False.elim ((hparts w hw) (Or.inr hwPart))
  rcases exists_ambient_disjoint_pair_paths_of_subgraph_no_singleton_separator
      C.bGraph p₀ hp₀ hnone with
    ⟨Bxy, Btz, hBxy, hBtz, hBdis, hBxySub, hBtzSub⟩ |
    ⟨Bxz, Bty, hBxz, hBty, hBdis, hBxzSub, hBtySub⟩
  · apply hno
    exact ABConnectorPair.hasCycleThroughThree_of_direct_direct_generic
      (M := M) C.toABConnectorPair hA hB p hsGraph htB hp hcrossClass
      Axs Ayz Bxy Btz hAxs hAyz hBxy hBtz hAdis hBdis
      hAxsSub hAyzSub hBxySub hBtzSub
  · apply hno
    exact ABConnectorPair.hasCycleThroughThree_of_direct_cross_generic
      (M := M) C.toABConnectorPair hA hB p hsGraph htB hp hcrossClass
      Axs Ayz Bxz Bty hAxs hAyz hBxz hBty hAdis hBdis
      hAxsSub hAyzSub hBxzSub hBtySub

/-- The symmetric p.15 contradiction when the clean external path starts
in the active B-isolating carrier.  Reversing the connector orientation
turns it into the preceding A-start case. -/
theorem MinimalABConnectorPair.false_of_classifiedCleanNearExit_start_B
    (C : M.MinimalABConnectorPair)
    (hA : M.aSet.card = 3) (hB : M.bSet.card = 3)
    (SA : IsolatingCutSide C.aGraph
      (ABConnectorPair.xAIn (M := M) C.toABConnectorPair)
      (ABConnectorPair.yAIn (M := M) C.toABConnectorPair)
      (ABConnectorPair.zAIn (M := M) C.toABConnectorPair))
    (hSA : SA.IsMaximal)
    (B : BIsolationChoice (M := M) C)
    {s t : V} (p : G.Walk s t) (hp : p.IsPath)
    (hsB : s ∈ B.carrier)
    (htConn : t ∈ C.aGraph.verts ∪ C.bGraph.verts)
    (htNear : t ∉ C.pairNearRegion (M := M) SA B)
    (hmeet : ∀ w, w ∈ p.support →
      w ∈ C.aGraph.verts ∪ C.bGraph.verts → w = s ∨ w = t)
    (hcuts : ∀ w, w ∈ p.support →
      w ≠ SA.cut.1 ∧ w ≠ B.cut.1)
    (hparts : ∀ w, w ∈ p.support →
      w ∉ (M.xPart : Set V) ∪ (M.yPart : Set V) ∪
        (M.zPart : Set V))
    (hno : ¬HasCycleThroughThree G x y z) : False := by
  classical
  cases B with
  | default hnone =>
      simpa [BIsolationChoice.carrier] using hsB
  | active SB hSB =>
      let N := reverseABTriple M
      let C' := MinimalABConnectorPair.reverseAB (M := M) C
      let SA' : IsolatingCutSide C'.aGraph
          (ABConnectorPair.xAIn (M := N) C'.toABConnectorPair)
          (ABConnectorPair.yAIn (M := N) C'.toABConnectorPair)
          (ABConnectorPair.zAIn (M := N) C'.toABConnectorPair) := by
        change IsolatingCutSide C.bGraph
          (ABConnectorPair.xBIn (M := M) C.toABConnectorPair)
          (ABConnectorPair.yBIn (M := M) C.toABConnectorPair)
          (ABConnectorPair.zBIn (M := M) C.toABConnectorPair)
        exact SB
      have hSA' : SA'.IsMaximal := by
        dsimp only [SA']
        exact hSB
      let SB' : IsolatingCutSide C'.bGraph
          (ABConnectorPair.xBIn (M := N) C'.toABConnectorPair)
          (ABConnectorPair.yBIn (M := N) C'.toABConnectorPair)
          (ABConnectorPair.zBIn (M := N) C'.toABConnectorPair) := by
        change IsolatingCutSide C.aGraph
          (ABConnectorPair.xAIn (M := M) C.toABConnectorPair)
          (ABConnectorPair.yAIn (M := M) C.toABConnectorPair)
          (ABConnectorPair.zAIn (M := M) C.toABConnectorPair)
        exact SA
      have hSB' : SB'.IsMaximal := by
        dsimp only [SB']
        exact hSA
      let B' : BIsolationChoice.{0} (M := N) C' :=
        BIsolationChoice.active SB' hSB'
      apply C'.false_of_classifiedCleanNearExit_start_A
        (M := N) (by simpa only [N, reverseABTriple_aSet] using hB)
        (by simpa only [N, reverseABTriple_bSet] using hA)
        SA' B' p hp
      · change s ∈ SA'.ambientCarrier
        change s ∈ SB.ambientCarrier
        simpa only [BIsolationChoice.carrier] using hsB
      · simpa only [C', MinimalABConnectorPair.reverseAB,
          ABConnectorPair.reverseAB, Set.union_comm] using htConn
      · intro htNear'
        apply htNear
        have ht' : t ∈ SA'.ambientCarrier ∪ B'.carrier ∪ N.xPart := by
          simpa only [MinimalABConnectorPair.pairNearRegion] using htNear'
        change t ∈ SA.ambientCarrier ∪ SB.ambientCarrier ∪ M.xPart
        simp only [Finset.mem_union] at ht' ⊢
        rcases ht' with (htSA' | htB') | htX
        · apply Or.inl; apply Or.inr
          change t ∈ SB.ambientCarrier at htSA'
          exact htSA'
        · apply Or.inl; apply Or.inl
          change t ∈ SA.ambientCarrier at htB'
          exact htB'
        · apply Or.inr
          simpa only [N, reverseABTriple_xPart] using htX
      · intro w hw hwConn
        apply hmeet w hw
        simpa only [C', MinimalABConnectorPair.reverseAB,
          ABConnectorPair.reverseAB, Set.union_comm] using hwConn
      · intro w hw
        have h := hcuts w hw
        constructor
        · change w ≠ SB.cut.1
          exact h.2
        · change w ≠ SA.cut.1
          exact h.1
      · intro w hw
        simpa only [N, reverseABTriple_xPart, reverseABTriple_yPart,
          reverseABTriple_zPart] using hparts w hw
      · exact hno

/-- A maximum `xA`-isolating end piece is impossible.  The clean external
path starts in one of the two chosen near carriers, and the preceding two
lemmas close the corresponding A- or B-start case. -/
theorem MinimalABConnectorPair.false_of_maximal_xA_isolating
    (C : M.MinimalABConnectorPair)
    (hA : M.aSet.card = 3) (hB : M.bSet.card = 3)
    (SA : IsolatingCutSide C.aGraph
      (ABConnectorPair.xAIn (M := M) C.toABConnectorPair)
      (ABConnectorPair.yAIn (M := M) C.toABConnectorPair)
      (ABConnectorPair.zAIn (M := M) C.toABConnectorPair))
    (hSA : SA.IsMaximal)
    (hconn : G.Connected)
    (hdelete : ∀ d : V, (G.induce fun w : V ↦ w ≠ d).Connected)
    (hno : ¬HasCycleThroughThree G x y z) : False := by
  classical
  obtain ⟨B⟩ :=
    MinimalABConnectorPair.exists_BIsolationChoice.{0} (M := M) C
  obtain ⟨s, hsA | hsB, t, htConn, htNear, p, hp, hmeet,
      hOnlyNear, hcuts, hparts⟩ :=
    C.exists_classifiedCleanNearExit_avoiding_cuts
      (M := M) hA SA B hconn hdelete hno
  · exact C.false_of_classifiedCleanNearExit_start_A
      (M := M) hA hB SA B p hp hsA htConn htNear hmeet hcuts hparts hno
  · exact C.false_of_classifiedCleanNearExit_start_B
      (M := M) hA hB SA hSA B p hp hsB htConn htNear hmeet hcuts hparts hno

/-- The A connector of a minimal pair is vertex-two-connected.  Any cut
has an isolating side; after cyclic relabeling its isolated attachment is
`xA`, contradicting the maximal-side exchange above. -/
theorem MinimalABConnectorPair.aGraph_twoConnected
    (C : M.MinimalABConnectorPair)
    (hA : M.aSet.card = 3) (hB : M.bSet.card = 3)
    (hconn : G.Connected)
    (hdelete : ∀ d : V, (G.induce fun w : V ↦ w ≠ d).Connected)
    (hno : ¬HasCycleThroughThree G x y z) :
    AHTVertexTwoConnected C.aGraph.coe := by
  classical
  have hne := M.a_attachments_pairwise_ne hA
  apply ahtVertexTwoConnected_of_connected_noCut
    C.aGraph.coe C.a_connected.coe
    (u := ABConnectorPair.xAIn (M := M) C.toABConnectorPair)
    (v := ABConnectorPair.yAIn (M := M) C.toABConnectorPair)
  · intro h
    exact hne.1 (congrArg Subtype.val h)
  · intro d hd
    rcases C.exists_isolating_A_of_cut (M := M) hA d hd with
      hx | hy | hz
    · obtain ⟨S, hS⟩ := exists_maximal_isolatingCutSide hx
      exact C.false_of_maximal_xA_isolating
        (M := M) hA hB S hS hconn hdelete hno
    · obtain ⟨S, hS⟩ := exists_maximal_isolatingCutSide hy
      let N := rotateYZXTriple M
      let C' := MinimalABConnectorPair.rotateYZX (M := M) C
      let S' : IsolatingCutSide C'.aGraph
          (ABConnectorPair.xAIn (M := N) C'.toABConnectorPair)
          (ABConnectorPair.yAIn (M := N) C'.toABConnectorPair)
          (ABConnectorPair.zAIn (M := N) C'.toABConnectorPair) := by
        change IsolatingCutSide C.aGraph
          (ABConnectorPair.yAIn (M := M) C.toABConnectorPair)
          (ABConnectorPair.zAIn (M := M) C.toABConnectorPair)
          (ABConnectorPair.xAIn (M := M) C.toABConnectorPair)
        exact S.swapBC
      have hS' : S'.IsMaximal := by
        dsimp only [S']
        exact S.swapBC_isMaximal hS
      have hno' : ¬HasCycleThroughThree G y z x := by
        rintro ⟨r, W, hW, hyW, hzW, hxW⟩
        exact hno ⟨r, W, hW, hxW, hyW, hzW⟩
      exact C'.false_of_maximal_xA_isolating
        (M := N)
        (by simpa only [N, rotateYZXTriple_aSet] using hA)
        (by simpa only [N, rotateYZXTriple_bSet] using hB)
        S' hS' hconn hdelete hno'
    · obtain ⟨S, hS⟩ := exists_maximal_isolatingCutSide hz
      let N₁ := rotateYZXTriple M
      let C₁ := MinimalABConnectorPair.rotateYZX (M := M) C
      let N₂ := rotateYZXTriple N₁
      let C₂ := MinimalABConnectorPair.rotateYZX (M := N₁) C₁
      let S₂ : IsolatingCutSide C₂.aGraph
          (ABConnectorPair.xAIn (M := N₂) C₂.toABConnectorPair)
          (ABConnectorPair.yAIn (M := N₂) C₂.toABConnectorPair)
          (ABConnectorPair.zAIn (M := N₂) C₂.toABConnectorPair) := by
        change IsolatingCutSide C.aGraph
          (ABConnectorPair.zAIn (M := M) C.toABConnectorPair)
          (ABConnectorPair.xAIn (M := M) C.toABConnectorPair)
          (ABConnectorPair.yAIn (M := M) C.toABConnectorPair)
        exact S
      have hS₂ : S₂.IsMaximal := by
        dsimp only [S₂]
        exact hS
      have hno₂ : ¬HasCycleThroughThree G z x y := by
        rintro ⟨r, W, hW, hzW, hxW, hyW⟩
        exact hno ⟨r, W, hW, hxW, hyW, hzW⟩
      exact C₂.false_of_maximal_xA_isolating
        (M := N₂)
        (by simpa only [N₂, N₁, rotateYZXTriple_aSet] using hA)
        (by simpa only [N₂, N₁, rotateYZXTriple_bSet] using hB)
        S₂ hS₂ hconn hdelete hno₂

/-- The B connector is vertex-two-connected by reversing the connector
orientation and applying the A-side theorem. -/
theorem MinimalABConnectorPair.bGraph_twoConnected
    (C : M.MinimalABConnectorPair)
    (hA : M.aSet.card = 3) (hB : M.bSet.card = 3)
    (hconn : G.Connected)
    (hdelete : ∀ d : V, (G.induce fun w : V ↦ w ≠ d).Connected)
    (hno : ¬HasCycleThroughThree G x y z) :
    AHTVertexTwoConnected C.bGraph.coe := by
  let N := reverseABTriple M
  let C' := MinimalABConnectorPair.reverseAB (M := M) C
  have h := C'.aGraph_twoConnected
    (M := N)
    (by simpa only [N, reverseABTriple_aSet] using hB)
    (by simpa only [N, reverseABTriple_bSet] using hA)
    hconn hdelete hno
  simpa only [C', MinimalABConnectorPair.reverseAB,
    ABConnectorPair.reverseAB] using h

/-- Both members of a minimal connector pair are vertex-two-connected. -/
theorem MinimalABConnectorPair.isTwoConnected
    (C : M.MinimalABConnectorPair)
    (hconn : G.Connected)
    (hdelete : ∀ d : V, (G.induce fun w : V ↦ w ≠ d).Connected)
    (hno : ¬HasCycleThroughThree G x y z)
    (hA : M.aSet.card = 3) (hB : M.bSet.card = 3) :
    C.toABConnectorPair.IsTwoConnected := by
  exact ⟨C.aGraph_twoConnected (M := M) hA hB hconn hdelete hno,
    C.bGraph_twoConnected (M := M) hA hB hconn hdelete hno⟩
/-- Condition-(vii) wrapper for the generic direct/cross splice. -/
private theorem ABConnectorPair.hasCycleThroughThree_of_normalized_direct_cross
    (C : M.ABConnectorPair)
    (hA : M.aSet.card = 3) (hB : M.bSet.card = 3)
    {D : Finset V} (S : M.MismatchedBoundaryPath D)
    (core : M.CleanConnectorCore C S)
    (hD : IsComponentAfterDeleting G (M.aSet ∪ M.bSet) D)
    (hDX : Disjoint D M.xPart) (hDY : Disjoint D M.yPart)
    (hDZ : Disjoint D M.zPart)
    (Axs : G.Walk M.xSep.left core.left.1)
    (Ayz : G.Walk M.ySep.left M.zSep.left)
    (Bxz : G.Walk M.xSep.right M.zSep.right)
    (Bsy : G.Walk core.right.1 M.ySep.right)
    (hAxs : Axs.IsPath) (hAyz : Ayz.IsPath)
    (hBxz : Bxz.IsPath) (hBsy : Bsy.IsPath)
    (hAdis : Disjoint {w | w ∈ Axs.support} {w | w ∈ Ayz.support})
    (hBdis : Disjoint {w | w ∈ Bxz.support} {w | w ∈ Bsy.support})
    (hAxsSub : ∀ w, w ∈ Axs.support → w ∈ C.aGraph.verts)
    (hAyzSub : ∀ w, w ∈ Ayz.support → w ∈ C.aGraph.verts)
    (hBxzSub : ∀ w, w ∈ Bxz.support → w ∈ C.bGraph.verts)
    (hBsySub : ∀ w, w ∈ Bsy.support → w ∈ C.bGraph.verts) :
    HasCycleThroughThree G x y z := by
  apply ABConnectorPair.hasCycleThroughThree_of_direct_cross_generic
    (M := M) C hA hB core.path core.left.2 core.right.2
      core.path_isPath ?_ Axs Ayz Bxz Bsy hAxs hAyz hBxz hBsy
      hAdis hBdis hAxsSub hAyzSub hBxzSub hBsySub
  intro w hwCore hwClass
  rcases hwClass with hwA | hwB | hwX | hwY | hwZ
  · exact Or.inl (core.meets_aGraph_only_left w hwCore hwA)
  · exact Or.inr (core.meets_bGraph_only_right w hwCore hwB)
  · exact cleanConnectorCore_meets_xTerminalBridge_only_ends
      (M := M) C S core hD hDX w hwCore hwX
  · exact cleanConnectorCore_meets_yTerminalBridge_only_ends
      (M := M) C S core hD hDY w hwCore hwY
  · exact cleanConnectorCore_meets_zTerminalBridge_only_ends
      (M := M) C S core hD hDZ w hwCore hwZ

/-- The first symmetric B-side case in the normalized AHT table. -/
private theorem ABConnectorPair.hasCycleThroughThree_of_normalized_symmetric_direct
    (C : M.ABConnectorPair)
    (hA : M.aSet.card = 3) (hB : M.bSet.card = 3)
    {D : Finset V} (S : M.MismatchedBoundaryPath D)
    (core : M.CleanConnectorCore C S)
    (hD : IsComponentAfterDeleting G (M.aSet ∪ M.bSet) D)
    (hDX : Disjoint D M.xPart) (hDY : Disjoint D M.yPart)
    (hDZ : Disjoint D M.zPart)
    (Asz : G.Walk core.left.1 M.zSep.left)
    (Ayx : G.Walk M.ySep.left M.xSep.left)
    (Bxz : G.Walk M.xSep.right M.zSep.right)
    (Bys : G.Walk M.ySep.right core.right.1)
    (hAsz : Asz.IsPath) (hAyx : Ayx.IsPath)
    (hBxz : Bxz.IsPath) (hBys : Bys.IsPath)
    (hAdis : Disjoint {w | w ∈ Asz.support} {w | w ∈ Ayx.support})
    (hBdis : Disjoint {w | w ∈ Bxz.support} {w | w ∈ Bys.support})
    (hAszSub : ∀ w, w ∈ Asz.support → w ∈ C.aGraph.verts)
    (hAyxSub : ∀ w, w ∈ Ayx.support → w ∈ C.aGraph.verts)
    (hBxzSub : ∀ w, w ∈ Bxz.support → w ∈ C.bGraph.verts)
    (hBysSub : ∀ w, w ∈ Bys.support → w ∈ C.bGraph.verts) :
    HasCycleThroughThree G x y z := by
  obtain ⟨hXY, hXZ, hYZ⟩ := M.terminalBridges_pairwise_disjoint hA hB
  let X := M.xTerminalBridge
  let Y := M.yTerminalBridge
  let Z := M.zTerminalBridge
  have h₁ : ∀ w, w ∈ Asz.support → w ∈ Z.support →
      w = M.zSep.left := by
    intro w hwA hwZ
    exact ABConnectorPair.zTerminalBridge_meets_aGraph_only_left
      (M := M) C hwZ (hAszSub w hwA)
  have h₂ : ∀ w, w ∈ (Asz.append Z).support →
      w ∈ Bxz.reverse.support → w = M.zSep.right := by
    intro w hw01 hwBrev
    have hwB : w ∈ Bxz.support := by
      simpa only [Walk.support_reverse, List.mem_reverse] using hwBrev
    rcases (Walk.mem_support_append_iff _ _).mp hw01 with hwA | hwZ
    · exact (Set.disjoint_left.mp C.vertex_disjoint
        (hAszSub w hwA) (hBxzSub w hwB)).elim
    · exact ABConnectorPair.zTerminalBridge_meets_bGraph_only_right
        (M := M) C hwZ (hBxzSub w hwB)
  have h₃ : ∀ w, w ∈ ((Asz.append Z).append Bxz.reverse).support →
      w ∈ X.reverse.support → w = M.xSep.right := by
    intro w hw012 hwXrev
    have hwX : w ∈ X.support := by
      simpa only [Walk.support_reverse, List.mem_reverse] using hwXrev
    rcases (Walk.mem_support_append_iff _ _).mp hw012 with hw01 | hwBrev
    · rcases (Walk.mem_support_append_iff _ _).mp hw01 with hwA | hwZ
      · have hwEq := ABConnectorPair.xTerminalBridge_meets_aGraph_only_left
          (M := M) C hwX (hAszSub w hwA)
        have hxAsz : M.xSep.left ∈ Asz.support := by
          rw [← hwEq]
          exact hwA
        exact (Set.disjoint_left.mp hAdis hxAsz Ayx.end_mem_support).elim
      · exact (Set.disjoint_left.mp hXZ hwX hwZ).elim
    · have hwB : w ∈ Bxz.support := by
        simpa only [Walk.support_reverse, List.mem_reverse] using hwBrev
      exact ABConnectorPair.xTerminalBridge_meets_bGraph_only_right
        (M := M) C hwX (hBxzSub w hwB)
  have h₄ : ∀ w,
      w ∈ (((Asz.append Z).append Bxz.reverse).append X.reverse).support →
      w ∈ Ayx.reverse.support → w = M.xSep.left := by
    intro w hw0123 hwAyxRev
    have hwAyx : w ∈ Ayx.support := by
      simpa only [Walk.support_reverse, List.mem_reverse] using hwAyxRev
    rcases (Walk.mem_support_append_iff _ _).mp hw0123 with hw012 | hwXrev
    · rcases (Walk.mem_support_append_iff _ _).mp hw012 with hw01 | hwBrev
      · rcases (Walk.mem_support_append_iff _ _).mp hw01 with hwA | hwZ
        · exact (Set.disjoint_left.mp hAdis hwA hwAyx).elim
        · have hwEq := ABConnectorPair.zTerminalBridge_meets_aGraph_only_left
            (M := M) C hwZ (hAyxSub w hwAyx)
          have hzAyx : M.zSep.left ∈ Ayx.support := by
            rw [← hwEq]
            exact hwAyx
          exact (Set.disjoint_left.mp hAdis Asz.end_mem_support hzAyx).elim
      · have hwB : w ∈ Bxz.support := by
          simpa only [Walk.support_reverse, List.mem_reverse] using hwBrev
        exact (Set.disjoint_left.mp C.vertex_disjoint
          (hAyxSub w hwAyx) (hBxzSub w hwB)).elim
    · have hwX : w ∈ X.support := by
        simpa only [Walk.support_reverse, List.mem_reverse] using hwXrev
      exact ABConnectorPair.xTerminalBridge_meets_aGraph_only_left
        (M := M) C hwX (hAyxSub w hwAyx)
  have h₅ : ∀ w,
      w ∈ ((((Asz.append Z).append Bxz.reverse).append X.reverse).append Ayx.reverse).support →
      w ∈ Y.support → w = M.ySep.left := by
    intro w hw01234 hwY
    rcases (Walk.mem_support_append_iff _ _).mp hw01234 with hw0123 | hwAyxRev
    · rcases (Walk.mem_support_append_iff _ _).mp hw0123 with hw012 | hwXrev
      · rcases (Walk.mem_support_append_iff _ _).mp hw012 with hw01 | hwBrev
        · rcases (Walk.mem_support_append_iff _ _).mp hw01 with hwA | hwZ
          · have hwEq := ABConnectorPair.yTerminalBridge_meets_aGraph_only_left
              (M := M) C hwY (hAszSub w hwA)
            have hyAsz : M.ySep.left ∈ Asz.support := by
              rw [← hwEq]
              exact hwA
            exact (Set.disjoint_left.mp hAdis hyAsz Ayx.start_mem_support).elim
          · exact (Set.disjoint_left.mp hYZ hwY hwZ).elim
        · have hwB : w ∈ Bxz.support := by
            simpa only [Walk.support_reverse, List.mem_reverse] using hwBrev
          have hwEq := ABConnectorPair.yTerminalBridge_meets_bGraph_only_right
            (M := M) C hwY (hBxzSub w hwB)
          have hyBxz : M.ySep.right ∈ Bxz.support := by
            rw [← hwEq]
            exact hwB
          exact (Set.disjoint_left.mp hBdis hyBxz Bys.start_mem_support).elim
      · have hwX : w ∈ X.support := by
          simpa only [Walk.support_reverse, List.mem_reverse] using hwXrev
        exact (Set.disjoint_left.mp hXY hwX hwY).elim
    · have hwAyx : w ∈ Ayx.support := by
        simpa only [Walk.support_reverse, List.mem_reverse] using hwAyxRev
      exact ABConnectorPair.yTerminalBridge_meets_aGraph_only_left
        (M := M) C hwY (hAyxSub w hwAyx)
  have h₆ : ∀ w,
      w ∈ (((((Asz.append Z).append Bxz.reverse).append X.reverse).append Ayx.reverse).append
        Y).support → w ∈ Bys.support → w = M.ySep.right := by
    intro w hw012345 hwBys
    rcases (Walk.mem_support_append_iff _ _).mp hw012345 with hw01234 | hwY
    · rcases (Walk.mem_support_append_iff _ _).mp hw01234 with hw0123 | hwAyxRev
      · rcases (Walk.mem_support_append_iff _ _).mp hw0123 with hw012 | hwXrev
        · rcases (Walk.mem_support_append_iff _ _).mp hw012 with hw01 | hwBrev
          · rcases (Walk.mem_support_append_iff _ _).mp hw01 with hwA | hwZ
            · exact (Set.disjoint_left.mp C.vertex_disjoint
                (hAszSub w hwA) (hBysSub w hwBys)).elim
            · have hwEq := ABConnectorPair.zTerminalBridge_meets_bGraph_only_right
                (M := M) C hwZ (hBysSub w hwBys)
              have hzBys : M.zSep.right ∈ Bys.support := by
                rw [← hwEq]
                exact hwBys
              exact (Set.disjoint_left.mp hBdis Bxz.end_mem_support hzBys).elim
          · have hwB : w ∈ Bxz.support := by
              simpa only [Walk.support_reverse, List.mem_reverse] using hwBrev
            exact (Set.disjoint_left.mp hBdis hwB hwBys).elim
        · have hwX : w ∈ X.support := by
            simpa only [Walk.support_reverse, List.mem_reverse] using hwXrev
          have hwEq := ABConnectorPair.xTerminalBridge_meets_bGraph_only_right
            (M := M) C hwX (hBysSub w hwBys)
          have hxBys : M.xSep.right ∈ Bys.support := by
            rw [← hwEq]
            exact hwBys
          exact (Set.disjoint_left.mp hBdis Bxz.start_mem_support hxBys).elim
      · have hwAyx : w ∈ Ayx.support := by
          simpa only [Walk.support_reverse, List.mem_reverse] using hwAyxRev
        exact (Set.disjoint_left.mp C.vertex_disjoint
          (hAyxSub w hwAyx) (hBysSub w hwBys)).elim
    · exact ABConnectorPair.yTerminalBridge_meets_bGraph_only_right
        (M := M) C hwY (hBysSub w hwBys)
  let detour := (((((Asz.append Z).append Bxz.reverse).append X.reverse).append Ayx.reverse).append
    Y).append Bys
  have hclass : ∀ w, w ∈ detour.support →
      w ∈ C.aGraph.verts ∨ w ∈ C.bGraph.verts ∨
      w ∈ M.xTerminalBridge.support ∨ w ∈ M.yTerminalBridge.support ∨
      w ∈ M.zTerminalBridge.support := by
    intro w hw
    dsimp only [detour] at hw
    rcases (Walk.mem_support_append_iff _ _).mp hw with hw012345 | hwBys
    · rcases (Walk.mem_support_append_iff _ _).mp hw012345 with hw01234 | hwY
      · rcases (Walk.mem_support_append_iff _ _).mp hw01234 with hw0123 | hwAyxRev
        · rcases (Walk.mem_support_append_iff _ _).mp hw0123 with hw012 | hwXrev
          · rcases (Walk.mem_support_append_iff _ _).mp hw012 with hw01 | hwBrev
            · rcases (Walk.mem_support_append_iff _ _).mp hw01 with hwA | hwZ
              · exact Or.inl (hAszSub w hwA)
              · exact Or.inr (Or.inr (Or.inr (Or.inr hwZ)))
            · have hwB : w ∈ Bxz.support := by
                simpa only [Walk.support_reverse, List.mem_reverse] using hwBrev
              exact Or.inr (Or.inl (hBxzSub w hwB))
          · have hwX : w ∈ X.support := by
              simpa only [Walk.support_reverse, List.mem_reverse] using hwXrev
            exact Or.inr (Or.inr (Or.inl hwX))
        · have hwAyx : w ∈ Ayx.support := by
            simpa only [Walk.support_reverse, List.mem_reverse] using hwAyxRev
          exact Or.inl (hAyxSub w hwAyx)
      · exact Or.inr (Or.inr (Or.inr (Or.inl hwY)))
    · exact Or.inr (Or.inl (hBysSub w hwBys))
  have hmeet : ∀ w, w ∈ detour.support → w ∈ core.path.support →
      w = core.left.1 ∨ w = core.right.1 := by
    intro w hwDetour hwCore
    exact cleanConnectorCore_meets_connector_detour_only_ends
      (M := M) C S core hD hDX hDY hDZ detour hclass w hwCore hwDetour
  have hxdetour : x ∈ detour.support := by
    dsimp only [detour]
    simp only [Walk.mem_support_append_iff, Walk.support_reverse,
      List.mem_reverse]
    exact Or.inl (Or.inl (Or.inl (Or.inr M.x_mem_xTerminalBridge)))
  have hydetour : y ∈ detour.support := by
    dsimp only [detour]
    simp only [Walk.mem_support_append_iff]
    exact Or.inl (Or.inr M.y_mem_yTerminalBridge)
  have hzdetour : z ∈ detour.support := by
    dsimp only [detour]
    simp only [Walk.mem_support_append_iff]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl
      (Or.inr M.z_mem_zTerminalBridge)))))
  have hxleft : x ≠ core.left.1 := by
    intro h
    have hxPart : core.left.1 ∈ M.xPart := by rw [← h]; exact M.x_mem_xPart
    exact Set.disjoint_left.mp C.avoids_terminal_parts
      (Or.inl core.left.2) (Or.inl (Or.inl hxPart))
  have hxright : x ≠ core.right.1 := by
    intro h
    have hxPart : core.right.1 ∈ M.xPart := by rw [← h]; exact M.x_mem_xPart
    exact Set.disjoint_left.mp C.avoids_terminal_parts
      (Or.inr core.right.2) (Or.inl (Or.inl hxPart))
  exact hasCycleThroughThree_of_seven_piece_detour
    Asz Z Bxz.reverse X.reverse Ayx.reverse Y Bys core.path
    hAsz M.zTerminalBridge_isPath hBxz.reverse
    M.xTerminalBridge_isPath.reverse hAyx.reverse
    M.yTerminalBridge_isPath hBys core.path_isPath
    h₁ h₂ h₃ h₄ h₅ h₆ hmeet hxdetour hxleft hxright
    hxdetour hydetour hzdetour

/-- The second symmetric B-side case is the checked direct/cross splice
with its two connector-end paths read in the reverse direction. -/
private theorem ABConnectorPair.hasCycleThroughThree_of_normalized_symmetric_cross
    (C : M.ABConnectorPair)
    (hA : M.aSet.card = 3) (hB : M.bSet.card = 3)
    {D : Finset V} (S : M.MismatchedBoundaryPath D)
    (core : M.CleanConnectorCore C S)
    (hD : IsComponentAfterDeleting G (M.aSet ∪ M.bSet) D)
    (hDX : Disjoint D M.xPart) (hDY : Disjoint D M.yPart)
    (hDZ : Disjoint D M.zPart)
    (Asx : G.Walk core.left.1 M.xSep.left)
    (Ayz : G.Walk M.ySep.left M.zSep.left)
    (Bxz : G.Walk M.xSep.right M.zSep.right)
    (Bys : G.Walk M.ySep.right core.right.1)
    (hAsx : Asx.IsPath) (hAyz : Ayz.IsPath)
    (hBxz : Bxz.IsPath) (hBys : Bys.IsPath)
    (hAdis : Disjoint {w | w ∈ Asx.support} {w | w ∈ Ayz.support})
    (hBdis : Disjoint {w | w ∈ Bxz.support} {w | w ∈ Bys.support})
    (hAsxSub : ∀ w, w ∈ Asx.support → w ∈ C.aGraph.verts)
    (hAyzSub : ∀ w, w ∈ Ayz.support → w ∈ C.aGraph.verts)
    (hBxzSub : ∀ w, w ∈ Bxz.support → w ∈ C.bGraph.verts)
    (hBysSub : ∀ w, w ∈ Bys.support → w ∈ C.bGraph.verts) :
    HasCycleThroughThree G x y z := by
  apply ABConnectorPair.hasCycleThroughThree_of_normalized_direct_cross
    (M := M) C hA hB S core hD hDX hDY hDZ
    Asx.reverse Ayz Bxz Bys.reverse
    hAsx.reverse hAyz hBxz hBys.reverse
  · simpa only [Walk.support_reverse, List.mem_reverse] using hAdis
  · simpa only [Walk.support_reverse, List.mem_reverse] using hBdis
  · intro w hw
    apply hAsxSub w
    simpa only [Walk.support_reverse, List.mem_reverse] using hw
  · exact hAyzSub
  · exact hBxzSub
  · intro w hw
    apply hBysSub w
    simpa only [Walk.support_reverse, List.mem_reverse] using hw

/-- The residual forced matching in the normalized AHT table. -/
private theorem ABConnectorPair.hasCycleThroughThree_of_normalized_residual
    (C : M.ABConnectorPair)
    (hA : M.aSet.card = 3) (hB : M.bSet.card = 3)
    {D : Finset V} (S : M.MismatchedBoundaryPath D)
    (core : M.CleanConnectorCore C S)
    (hD : IsComponentAfterDeleting G (M.aSet ∪ M.bSet) D)
    (hDX : Disjoint D M.xPart) (hDY : Disjoint D M.yPart)
    (hDZ : Disjoint D M.zPart)
    (Ays : G.Walk M.ySep.left core.left.1)
    (Axz : G.Walk M.xSep.left M.zSep.left)
    (Byz : G.Walk M.ySep.right M.zSep.right)
    (Bxs : G.Walk M.xSep.right core.right.1)
    (hAys : Ays.IsPath) (hAxz : Axz.IsPath)
    (hByz : Byz.IsPath) (hBxs : Bxs.IsPath)
    (hAdis : Disjoint {w | w ∈ Ays.support} {w | w ∈ Axz.support})
    (hBdis : Disjoint {w | w ∈ Byz.support} {w | w ∈ Bxs.support})
    (hAysSub : ∀ w, w ∈ Ays.support → w ∈ C.aGraph.verts)
    (hAxzSub : ∀ w, w ∈ Axz.support → w ∈ C.aGraph.verts)
    (hByzSub : ∀ w, w ∈ Byz.support → w ∈ C.bGraph.verts)
    (hBxsSub : ∀ w, w ∈ Bxs.support → w ∈ C.bGraph.verts) :
    HasCycleThroughThree G x y z := by
  obtain ⟨hXY, hXZ, hYZ⟩ := M.terminalBridges_pairwise_disjoint hA hB
  let X := M.xTerminalBridge
  let Y := M.yTerminalBridge
  let Z := M.zTerminalBridge
  have h₁ : ∀ w, w ∈ Ays.reverse.support → w ∈ Y.support →
      w = M.ySep.left := by
    intro w hwARev hwY
    have hwA : w ∈ Ays.support := by
      simpa only [Walk.support_reverse, List.mem_reverse] using hwARev
    exact ABConnectorPair.yTerminalBridge_meets_aGraph_only_left
      (M := M) C hwY (hAysSub w hwA)
  have h₂ : ∀ w, w ∈ (Ays.reverse.append Y).support →
      w ∈ Byz.support → w = M.ySep.right := by
    intro w hw01 hwB
    rcases (Walk.mem_support_append_iff _ _).mp hw01 with hwARev | hwY
    · have hwA : w ∈ Ays.support := by
        simpa only [Walk.support_reverse, List.mem_reverse] using hwARev
      exact (Set.disjoint_left.mp C.vertex_disjoint
        (hAysSub w hwA) (hByzSub w hwB)).elim
    · exact ABConnectorPair.yTerminalBridge_meets_bGraph_only_right
        (M := M) C hwY (hByzSub w hwB)
  have h₃ : ∀ w, w ∈ ((Ays.reverse.append Y).append Byz).support →
      w ∈ Z.reverse.support → w = M.zSep.right := by
    intro w hw012 hwZRev
    have hwZ : w ∈ Z.support := by
      simpa only [Walk.support_reverse, List.mem_reverse] using hwZRev
    rcases (Walk.mem_support_append_iff _ _).mp hw012 with hw01 | hwB
    · rcases (Walk.mem_support_append_iff _ _).mp hw01 with hwARev | hwY
      · have hwA : w ∈ Ays.support := by
          simpa only [Walk.support_reverse, List.mem_reverse] using hwARev
        have hwEq := ABConnectorPair.zTerminalBridge_meets_aGraph_only_left
          (M := M) C hwZ (hAysSub w hwA)
        have hzAys : M.zSep.left ∈ Ays.support := by rw [← hwEq]; exact hwA
        exact (Set.disjoint_left.mp hAdis hzAys Axz.end_mem_support).elim
      · exact (Set.disjoint_left.mp hYZ hwY hwZ).elim
    · exact ABConnectorPair.zTerminalBridge_meets_bGraph_only_right
        (M := M) C hwZ (hByzSub w hwB)
  have h₄ : ∀ w,
      w ∈ (((Ays.reverse.append Y).append Byz).append Z.reverse).support →
      w ∈ Axz.reverse.support → w = M.zSep.left := by
    intro w hw0123 hwAxzRev
    have hwAxz : w ∈ Axz.support := by
      simpa only [Walk.support_reverse, List.mem_reverse] using hwAxzRev
    rcases (Walk.mem_support_append_iff _ _).mp hw0123 with hw012 | hwZRev
    · rcases (Walk.mem_support_append_iff _ _).mp hw012 with hw01 | hwB
      · rcases (Walk.mem_support_append_iff _ _).mp hw01 with hwARev | hwY
        · have hwA : w ∈ Ays.support := by
            simpa only [Walk.support_reverse, List.mem_reverse] using hwARev
          exact (Set.disjoint_left.mp hAdis hwA hwAxz).elim
        · have hwEq := ABConnectorPair.yTerminalBridge_meets_aGraph_only_left
            (M := M) C hwY (hAxzSub w hwAxz)
          have hyAxz : M.ySep.left ∈ Axz.support := by rw [← hwEq]; exact hwAxz
          exact (Set.disjoint_left.mp hAdis Ays.start_mem_support hyAxz).elim
      · exact (Set.disjoint_left.mp C.vertex_disjoint
          (hAxzSub w hwAxz) (hByzSub w hwB)).elim
    · have hwZ : w ∈ Z.support := by
        simpa only [Walk.support_reverse, List.mem_reverse] using hwZRev
      exact ABConnectorPair.zTerminalBridge_meets_aGraph_only_left
        (M := M) C hwZ (hAxzSub w hwAxz)
  have h₅ : ∀ w,
      w ∈ ((((Ays.reverse.append Y).append Byz).append Z.reverse).append Axz.reverse).support →
      w ∈ X.support → w = M.xSep.left := by
    intro w hw01234 hwX
    rcases (Walk.mem_support_append_iff _ _).mp hw01234 with hw0123 | hwAxzRev
    · rcases (Walk.mem_support_append_iff _ _).mp hw0123 with hw012 | hwZRev
      · rcases (Walk.mem_support_append_iff _ _).mp hw012 with hw01 | hwB
        · rcases (Walk.mem_support_append_iff _ _).mp hw01 with hwARev | hwY
          · have hwA : w ∈ Ays.support := by
              simpa only [Walk.support_reverse, List.mem_reverse] using hwARev
            have hwEq := ABConnectorPair.xTerminalBridge_meets_aGraph_only_left
              (M := M) C hwX (hAysSub w hwA)
            have hxAys : M.xSep.left ∈ Ays.support := by rw [← hwEq]; exact hwA
            exact (Set.disjoint_left.mp hAdis hxAys Axz.start_mem_support).elim
          · exact (Set.disjoint_left.mp hXY hwX hwY).elim
        · have hwEq := ABConnectorPair.xTerminalBridge_meets_bGraph_only_right
            (M := M) C hwX (hByzSub w hwB)
          have hxByz : M.xSep.right ∈ Byz.support := by rw [← hwEq]; exact hwB
          exact (Set.disjoint_left.mp hBdis hxByz Bxs.start_mem_support).elim
      · have hwZ : w ∈ Z.support := by
          simpa only [Walk.support_reverse, List.mem_reverse] using hwZRev
        exact (Set.disjoint_left.mp hXZ hwX hwZ).elim
    · have hwAxz : w ∈ Axz.support := by
        simpa only [Walk.support_reverse, List.mem_reverse] using hwAxzRev
      exact ABConnectorPair.xTerminalBridge_meets_aGraph_only_left
        (M := M) C hwX (hAxzSub w hwAxz)
  have h₆ : ∀ w,
      w ∈ (((((Ays.reverse.append Y).append Byz).append Z.reverse).append Axz.reverse).append
        X).support → w ∈ Bxs.support → w = M.xSep.right := by
    intro w hw012345 hwBxs
    rcases (Walk.mem_support_append_iff _ _).mp hw012345 with hw01234 | hwX
    · rcases (Walk.mem_support_append_iff _ _).mp hw01234 with hw0123 | hwAxzRev
      · rcases (Walk.mem_support_append_iff _ _).mp hw0123 with hw012 | hwZRev
        · rcases (Walk.mem_support_append_iff _ _).mp hw012 with hw01 | hwB
          · rcases (Walk.mem_support_append_iff _ _).mp hw01 with hwARev | hwY
            · have hwA : w ∈ Ays.support := by
                simpa only [Walk.support_reverse, List.mem_reverse] using hwARev
              exact (Set.disjoint_left.mp C.vertex_disjoint
                (hAysSub w hwA) (hBxsSub w hwBxs)).elim
            · have hwEq := ABConnectorPair.yTerminalBridge_meets_bGraph_only_right
                (M := M) C hwY (hBxsSub w hwBxs)
              have hyBxs : M.ySep.right ∈ Bxs.support := by rw [← hwEq]; exact hwBxs
              exact (Set.disjoint_left.mp hBdis Byz.start_mem_support hyBxs).elim
          · exact (Set.disjoint_left.mp hBdis hwB hwBxs).elim
        · have hwZ : w ∈ Z.support := by
            simpa only [Walk.support_reverse, List.mem_reverse] using hwZRev
          have hwEq := ABConnectorPair.zTerminalBridge_meets_bGraph_only_right
            (M := M) C hwZ (hBxsSub w hwBxs)
          have hzBxs : M.zSep.right ∈ Bxs.support := by rw [← hwEq]; exact hwBxs
          exact (Set.disjoint_left.mp hBdis Byz.end_mem_support hzBxs).elim
      · have hwAxz : w ∈ Axz.support := by
          simpa only [Walk.support_reverse, List.mem_reverse] using hwAxzRev
        exact (Set.disjoint_left.mp C.vertex_disjoint
          (hAxzSub w hwAxz) (hBxsSub w hwBxs)).elim
    · exact ABConnectorPair.xTerminalBridge_meets_bGraph_only_right
        (M := M) C hwX (hBxsSub w hwBxs)
  let detour := (((((Ays.reverse.append Y).append Byz).append Z.reverse).append Axz.reverse).append
    X).append Bxs
  have hclass : ∀ w, w ∈ detour.support →
      w ∈ C.aGraph.verts ∨ w ∈ C.bGraph.verts ∨
      w ∈ M.xTerminalBridge.support ∨ w ∈ M.yTerminalBridge.support ∨
      w ∈ M.zTerminalBridge.support := by
    intro w hw
    dsimp only [detour] at hw
    rcases (Walk.mem_support_append_iff _ _).mp hw with hw012345 | hwBxs
    · rcases (Walk.mem_support_append_iff _ _).mp hw012345 with hw01234 | hwX
      · rcases (Walk.mem_support_append_iff _ _).mp hw01234 with hw0123 | hwAxzRev
        · rcases (Walk.mem_support_append_iff _ _).mp hw0123 with hw012 | hwZRev
          · rcases (Walk.mem_support_append_iff _ _).mp hw012 with hw01 | hwB
            · rcases (Walk.mem_support_append_iff _ _).mp hw01 with hwARev | hwY
              · have hwA : w ∈ Ays.support := by
                  simpa only [Walk.support_reverse, List.mem_reverse] using hwARev
                exact Or.inl (hAysSub w hwA)
              · exact Or.inr (Or.inr (Or.inr (Or.inl hwY)))
            · exact Or.inr (Or.inl (hByzSub w hwB))
          · have hwZ : w ∈ Z.support := by
              simpa only [Walk.support_reverse, List.mem_reverse] using hwZRev
            exact Or.inr (Or.inr (Or.inr (Or.inr hwZ)))
        · have hwAxz : w ∈ Axz.support := by
            simpa only [Walk.support_reverse, List.mem_reverse] using hwAxzRev
          exact Or.inl (hAxzSub w hwAxz)
      · exact Or.inr (Or.inr (Or.inl hwX))
    · exact Or.inr (Or.inl (hBxsSub w hwBxs))
  have hmeet : ∀ w, w ∈ detour.support → w ∈ core.path.support →
      w = core.left.1 ∨ w = core.right.1 := by
    intro w hwDetour hwCore
    exact cleanConnectorCore_meets_connector_detour_only_ends
      (M := M) C S core hD hDX hDY hDZ detour hclass w hwCore hwDetour
  have hxdetour : x ∈ detour.support := by
    dsimp only [detour]
    simp only [Walk.mem_support_append_iff]
    exact Or.inl (Or.inr M.x_mem_xTerminalBridge)
  have hydetour : y ∈ detour.support := by
    dsimp only [detour]
    simp only [Walk.mem_support_append_iff]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl
      (Or.inr M.y_mem_yTerminalBridge)))))
  have hzdetour : z ∈ detour.support := by
    dsimp only [detour]
    simp only [Walk.mem_support_append_iff, Walk.support_reverse,
      List.mem_reverse]
    exact Or.inl (Or.inl (Or.inl (Or.inr M.z_mem_zTerminalBridge)))
  have hxleft : x ≠ core.left.1 := by
    intro h
    have hxPart : core.left.1 ∈ M.xPart := by rw [← h]; exact M.x_mem_xPart
    exact Set.disjoint_left.mp C.avoids_terminal_parts
      (Or.inl core.left.2) (Or.inl (Or.inl hxPart))
  have hxright : x ≠ core.right.1 := by
    intro h
    have hxPart : core.right.1 ∈ M.xPart := by rw [← h]; exact M.x_mem_xPart
    exact Set.disjoint_left.mp C.avoids_terminal_parts
      (Or.inr core.right.2) (Or.inl (Or.inl hxPart))
  exact hasCycleThroughThree_of_seven_piece_detour
    Ays.reverse Y Byz Z.reverse Axz.reverse X Bxs core.path
    hAys.reverse M.yTerminalBridge_isPath hByz
    M.zTerminalBridge_isPath.reverse hAxz.reverse
    M.xTerminalBridge_isPath hBxs core.path_isPath
    h₁ h₂ h₃ h₄ h₅ h₆ hmeet hxdetour hxleft hxright
    hxdetour hydetour hzdetour

/-- The complete normalized path contradiction at the bottom of AHT
p.15: an unmatched `xA--yB` path through a remaining component, together
with two-connected connector graphs, yields a common `x,y,z` cycle. -/
theorem ABConnectorPair.hasCycleThroughThree_of_normalized_mismatchedBoundaryPath
    (C : M.ABConnectorPair) (h2 : C.IsTwoConnected)
    (hA : M.aSet.card = 3) (hB : M.bSet.card = 3)
    {D : Finset V} (S : M.MismatchedBoundaryPath D)
    (hD : IsComponentAfterDeleting G (M.aSet ∪ M.bSet) D)
    (hDX : Disjoint D M.xPart) (hDY : Disjoint D M.yPart)
    (hDZ : Disjoint D M.zPart)
    (hSa : S.a = M.xSep.left) (hSb : S.b = M.ySep.right) :
    HasCycleThroughThree G x y z := by
  classical
  obtain ⟨core⟩ := M.exists_cleanConnectorCore C S
  obtain ⟨hsAy, hsAz, hsBx, hsBz⟩ :=
    cleanConnectorCore_normalized_endpoint_ne
      (M := M) C S core hD hSa hSb hA hB
  obtain ⟨hAxy, hAxz, hAyz⟩ := M.a_attachments_pairwise_ne hA
  obtain ⟨hBxy, hBxz, hByz⟩ := M.b_attachments_pairwise_ne hB
  have hxB_sB : ABConnectorPair.xBIn (M := M) C ≠ core.right := by
    intro h
    exact hsBx (congrArg Subtype.val h).symm
  have hyA_sA : ABConnectorPair.yAIn (M := M) C ≠ core.left := by
    intro h
    exact hsAy (congrArg Subtype.val h).symm
  have hsA_zA : core.left ≠ ABConnectorPair.zAIn (M := M) C := by
    intro h
    exact hsAz (congrArg Subtype.val h)
  have hsB_zB : core.right ≠ ABConnectorPair.zBIn (M := M) C := by
    intro h
    exact hsBz (congrArg Subtype.val h)
  have hxA_yA : ABConnectorPair.xAIn (M := M) C ≠
      ABConnectorPair.yAIn (M := M) C := by
    intro h
    exact hAxy (congrArg Subtype.val h)
  have hxA_zA : ABConnectorPair.xAIn (M := M) C ≠
      ABConnectorPair.zAIn (M := M) C := by
    intro h
    exact hAxz (congrArg Subtype.val h)
  have hxB_yB : ABConnectorPair.xBIn (M := M) C ≠
      ABConnectorPair.yBIn (M := M) C := by
    intro h
    exact hBxy (congrArg Subtype.val h)
  have hyB_zB : ABConnectorPair.yBIn (M := M) C ≠
      ABConnectorPair.zBIn (M := M) C := by
    intro h
    exact hByz (congrArg Subtype.val h)
  by_cases hAcase : ∃ (Axs : G.Walk M.xSep.left core.left.1)
      (Ayz : G.Walk M.ySep.left M.zSep.left),
      Axs.IsPath ∧ Ayz.IsPath ∧
      Disjoint {w | w ∈ Axs.support} {w | w ∈ Ayz.support} ∧
      (∀ w, w ∈ Axs.support → w ∈ C.aGraph.verts) ∧
      ∀ w, w ∈ Ayz.support → w ∈ C.aGraph.verts
  · obtain ⟨Axs, Ayz, hAxs, hAyzP, hAdis, hAxsSub, hAyzSub⟩ := hAcase
    rcases exists_ambient_disjoint_pair_paths_of_subgraph_twoConnected
        C.bGraph h2.2
        (a₀ := ABConnectorPair.xBIn (M := M) C) (a₁ := core.right)
        (b₀ := ABConnectorPair.yBIn (M := M) C)
        (b₁ := ABConnectorPair.zBIn (M := M) C)
        hxB_sB hyB_zB with
      ⟨Bxy, Bsz, hBxyP, hBsz, hBdis, hBxySub, hBszSub⟩ |
      ⟨Bxz, Bsy, hBxzP, hBsy, hBdis, hBxzSub, hBsySub⟩
    · exact ABConnectorPair.hasCycleThroughThree_of_normalized_direct_direct
        (M := M) C hA hB
        S core hD hDX hDY hDZ Axs Ayz Bxy Bsz
        hAxs hAyzP hBxyP hBsz hAdis hBdis
        hAxsSub hAyzSub hBxySub hBszSub
    · exact ABConnectorPair.hasCycleThroughThree_of_normalized_direct_cross
        (M := M) C hA hB
        S core hD hDX hDY hDZ Axs Ayz Bxz Bsy
        hAxs hAyzP hBxzP hBsy hAdis hBdis
        hAxsSub hAyzSub hBxzSub hBsySub
  · by_cases hBcase : ∃ (Bys : G.Walk M.ySep.right core.right.1)
        (Bxz : G.Walk M.xSep.right M.zSep.right),
        Bys.IsPath ∧ Bxz.IsPath ∧
        Disjoint {w | w ∈ Bys.support} {w | w ∈ Bxz.support} ∧
        (∀ w, w ∈ Bys.support → w ∈ C.bGraph.verts) ∧
        ∀ w, w ∈ Bxz.support → w ∈ C.bGraph.verts
    · obtain ⟨Bys, Bxz, hBys, hBxzP, hBdis, hBysSub, hBxzSub⟩ := hBcase
      rcases exists_ambient_disjoint_pair_paths_of_subgraph_twoConnected
          C.aGraph h2.1
          (a₀ := ABConnectorPair.yAIn (M := M) C) (a₁ := core.left)
          (b₀ := ABConnectorPair.xAIn (M := M) C)
          (b₁ := ABConnectorPair.zAIn (M := M) C)
          hyA_sA hxA_zA with
        ⟨Ayx, Asz, hAyx, hAsz, hAdis, hAyxSub, hAszSub⟩ |
        ⟨Ayz, Asx, hAyzP, hAsx, hAdis, hAyzSub, hAsxSub⟩
      · exact ABConnectorPair.hasCycleThroughThree_of_normalized_symmetric_direct
          (M := M) C hA hB
          S core hD hDX hDY hDZ Asz Ayx Bxz Bys
          hAsz hAyx hBxzP hBys hAdis.symm hBdis.symm
          hAszSub hAyxSub hBxzSub hBysSub
      · exact ABConnectorPair.hasCycleThroughThree_of_normalized_symmetric_cross
          (M := M) C hA hB
          S core hD hDX hDY hDZ Asx Ayz Bxz Bys
          hAsx hAyzP hBxzP hBys hAdis.symm hBdis.symm
          hAsxSub hAyzSub hBxzSub hBysSub
    · rcases exists_ambient_disjoint_pair_paths_of_subgraph_twoConnected
          C.aGraph h2.1
          (a₀ := ABConnectorPair.xAIn (M := M) C)
          (a₁ := ABConnectorPair.yAIn (M := M) C)
          (b₀ := core.left) (b₁ := ABConnectorPair.zAIn (M := M) C)
          hxA_yA hsA_zA with
        ⟨Axs, Ayz, hAxs, hAyzP, hAdis, hAxsSub, hAyzSub⟩ |
        ⟨Axz, Ays, hAxzP, hAys, hAdis, hAxzSub, hAysSub⟩
      · exact (hAcase ⟨Axs, Ayz, hAxs, hAyzP, hAdis,
          hAxsSub, hAyzSub⟩).elim
      · rcases exists_ambient_disjoint_pair_paths_of_subgraph_twoConnected
            C.bGraph h2.2
            (a₀ := ABConnectorPair.xBIn (M := M) C)
            (a₁ := ABConnectorPair.yBIn (M := M) C)
            (b₀ := core.right) (b₁ := ABConnectorPair.zBIn (M := M) C)
            hxB_yB hsB_zB with
          ⟨Bxs, Byz, hBxs, hByzP, hBdis, hBxsSub, hByzSub⟩ |
          ⟨Bxz, Bys, hBxzP, hBys, hBdis, hBxzSub, hBysSub⟩
        · exact ABConnectorPair.hasCycleThroughThree_of_normalized_residual
            (M := M) C hA hB
            S core hD hDX hDY hDZ Ays Axz Byz Bxs
            hAys hAxzP hByzP hBxs hAdis.symm hBdis.symm
            hAysSub hAxzSub hByzSub hBxsSub
        · exact (hBcase ⟨Bys, Bxz, hBys, hBxzP, hBdis.symm,
            hBysSub, hBxzSub⟩).elim

/-- The second normalized orientation of the condition-(vii) path:
an unmatched `xA--zB` path.  This is the `y,z` relabeling of the
`xA--yB` router. -/
theorem ABConnectorPair.hasCycleThroughThree_of_xA_zB_mismatchedBoundaryPath
    (C : M.ABConnectorPair) (h2 : C.IsTwoConnected)
    (hA : M.aSet.card = 3) (hB : M.bSet.card = 3)
    {D : Finset V} (S : M.MismatchedBoundaryPath D)
    (hD : IsComponentAfterDeleting G (M.aSet ∪ M.bSet) D)
    (hDX : Disjoint D M.xPart) (hDY : Disjoint D M.yPart)
    (hDZ : Disjoint D M.zPart)
    (hSa : S.a = M.xSep.left) (hSb : S.b = M.zSep.right) :
    HasCycleThroughThree G x y z := by
  let N := swapYZTriple M
  let C' := ABConnectorPair.swapYZ (M := M) C
  let S' := MismatchedBoundaryPath.swapYZ (M := M) S
  have h2' : C'.IsTwoConnected := by
    exact ABConnectorPair.swapYZ_isTwoConnected (M := M) C h2
  have hA' : N.aSet.card = 3 := by
    simpa only [N, swapYZTriple_aSet] using hA
  have hB' : N.bSet.card = 3 := by
    simpa only [N, swapYZTriple_bSet] using hB
  have hD' : IsComponentAfterDeleting G (N.aSet ∪ N.bSet) D := by
    simpa only [N, swapYZTriple_aSet, swapYZTriple_bSet] using hD
  have hDX' : Disjoint D N.xPart := by
    simpa only [N, swapYZTriple_xPart] using hDX
  have hDY' : Disjoint D N.yPart := by
    simpa only [N, swapYZTriple_yPart] using hDZ
  have hDZ' : Disjoint D N.zPart := by
    simpa only [N, swapYZTriple_zPart] using hDY
  have hSa' : S'.a = N.xSep.left := by
    simpa only [S', MismatchedBoundaryPath.swapYZ, N,
      swapYZTriple_xSep_left] using hSa
  have hSb' : S'.b = N.ySep.right := by
    simpa only [S', MismatchedBoundaryPath.swapYZ, N,
      swapYZTriple_ySep_right] using hSb
  obtain ⟨r, W, hW, hx, hz, hy⟩ :=
    ABConnectorPair.hasCycleThroughThree_of_normalized_mismatchedBoundaryPath
      (M := N) C' h2' hA' hB' S' hD' hDX' hDY' hDZ' hSa' hSb'
  exact ⟨r, W, hW, hx, hy, hz⟩

/-- The third normalized orientation of the condition-(vii) path:
an unmatched `yA--zB` path.  This is the cyclic relabeling of the
`xA--yB` router. -/
theorem ABConnectorPair.hasCycleThroughThree_of_yA_zB_mismatchedBoundaryPath
    (C : M.ABConnectorPair) (h2 : C.IsTwoConnected)
    (hA : M.aSet.card = 3) (hB : M.bSet.card = 3)
    {D : Finset V} (S : M.MismatchedBoundaryPath D)
    (hD : IsComponentAfterDeleting G (M.aSet ∪ M.bSet) D)
    (hDX : Disjoint D M.xPart) (hDY : Disjoint D M.yPart)
    (hDZ : Disjoint D M.zPart)
    (hSa : S.a = M.ySep.left) (hSb : S.b = M.zSep.right) :
    HasCycleThroughThree G x y z := by
  let N := rotateYZXTriple M
  let C' := ABConnectorPair.rotateYZX (M := M) C
  let S' := MismatchedBoundaryPath.rotateYZX (M := M) S
  have h2' : C'.IsTwoConnected := by
    exact ABConnectorPair.rotateYZX_isTwoConnected (M := M) C h2
  have hA' : N.aSet.card = 3 := by
    simpa only [N, rotateYZXTriple_aSet] using hA
  have hB' : N.bSet.card = 3 := by
    simpa only [N, rotateYZXTriple_bSet] using hB
  have hD' : IsComponentAfterDeleting G (N.aSet ∪ N.bSet) D := by
    simpa only [N, rotateYZXTriple_aSet, rotateYZXTriple_bSet] using hD
  have hDX' : Disjoint D N.xPart := by
    simpa only [N, rotateYZXTriple_xPart] using hDY
  have hDY' : Disjoint D N.yPart := by
    simpa only [N, rotateYZXTriple_yPart] using hDZ
  have hDZ' : Disjoint D N.zPart := by
    simpa only [N, rotateYZXTriple_zPart] using hDX
  have hSa' : S'.a = N.xSep.left := by
    simpa only [S', MismatchedBoundaryPath.rotateYZX, N,
      rotateYZXTriple_xSep_left] using hSa
  have hSb' : S'.b = N.ySep.right := by
    simpa only [S', MismatchedBoundaryPath.rotateYZX, N,
      rotateYZXTriple_ySep_right] using hSb
  obtain ⟨r, W, hW, hy, hz, hx⟩ :=
    ABConnectorPair.hasCycleThroughThree_of_normalized_mismatchedBoundaryPath
      (M := N) C' h2' hA' hB' S' hD' hDX' hDY' hDZ' hSa' hSb'
  exact ⟨r, W, hW, hx, hy, hz⟩

/-- Reverse the A/B orientation to reduce an unmatched `yA--xB` path to
the normalized `xA--yB` router. -/
theorem ABConnectorPair.hasCycleThroughThree_of_yA_xB_mismatchedBoundaryPath
    (C : M.ABConnectorPair) (h2 : C.IsTwoConnected)
    (hA : M.aSet.card = 3) (hB : M.bSet.card = 3)
    {D : Finset V} (S : M.MismatchedBoundaryPath D)
    (hD : IsComponentAfterDeleting G (M.aSet ∪ M.bSet) D)
    (hDX : Disjoint D M.xPart) (hDY : Disjoint D M.yPart)
    (hDZ : Disjoint D M.zPart)
    (hSa : S.a = M.ySep.left) (hSb : S.b = M.xSep.right) :
    HasCycleThroughThree G x y z := by
  let N := reverseABTriple M
  let C' := ABConnectorPair.reverseAB (M := M) C
  let S' := MismatchedBoundaryPath.reverseAB (M := M) S
  have h2' : C'.IsTwoConnected := by
    exact ABConnectorPair.reverseAB_isTwoConnected (M := M) C h2
  have hA' : N.aSet.card = 3 := by
    simpa only [N, reverseABTriple_aSet] using hB
  have hB' : N.bSet.card = 3 := by
    simpa only [N, reverseABTriple_bSet] using hA
  have hD' : IsComponentAfterDeleting G (N.aSet ∪ N.bSet) D := by
    simpa only [N, reverseABTriple_aSet, reverseABTriple_bSet,
      Finset.union_comm] using hD
  have hDX' : Disjoint D N.xPart := by
    simpa only [N, reverseABTriple_xPart] using hDX
  have hDY' : Disjoint D N.yPart := by
    simpa only [N, reverseABTriple_yPart] using hDY
  have hDZ' : Disjoint D N.zPart := by
    simpa only [N, reverseABTriple_zPart] using hDZ
  have hSa' : S'.a = N.xSep.left := by
    simpa only [S', MismatchedBoundaryPath.reverseAB, N,
      reverseABTriple_xSep_left] using hSb
  have hSb' : S'.b = N.ySep.right := by
    simpa only [S', MismatchedBoundaryPath.reverseAB, N,
      reverseABTriple_ySep_right] using hSa
  exact
    ABConnectorPair.hasCycleThroughThree_of_normalized_mismatchedBoundaryPath
      (M := N) C' h2' hA' hB' S' hD' hDX' hDY' hDZ' hSa' hSb'

/-- Reverse the A/B orientation to reduce an unmatched `zA--xB` path to
the `xA--zB` cyclic router. -/
theorem ABConnectorPair.hasCycleThroughThree_of_zA_xB_mismatchedBoundaryPath
    (C : M.ABConnectorPair) (h2 : C.IsTwoConnected)
    (hA : M.aSet.card = 3) (hB : M.bSet.card = 3)
    {D : Finset V} (S : M.MismatchedBoundaryPath D)
    (hD : IsComponentAfterDeleting G (M.aSet ∪ M.bSet) D)
    (hDX : Disjoint D M.xPart) (hDY : Disjoint D M.yPart)
    (hDZ : Disjoint D M.zPart)
    (hSa : S.a = M.zSep.left) (hSb : S.b = M.xSep.right) :
    HasCycleThroughThree G x y z := by
  let N := reverseABTriple M
  let C' := ABConnectorPair.reverseAB (M := M) C
  let S' := MismatchedBoundaryPath.reverseAB (M := M) S
  have h2' : C'.IsTwoConnected := by
    exact ABConnectorPair.reverseAB_isTwoConnected (M := M) C h2
  have hA' : N.aSet.card = 3 := by
    simpa only [N, reverseABTriple_aSet] using hB
  have hB' : N.bSet.card = 3 := by
    simpa only [N, reverseABTriple_bSet] using hA
  have hD' : IsComponentAfterDeleting G (N.aSet ∪ N.bSet) D := by
    simpa only [N, reverseABTriple_aSet, reverseABTriple_bSet,
      Finset.union_comm] using hD
  have hDX' : Disjoint D N.xPart := by
    simpa only [N, reverseABTriple_xPart] using hDX
  have hDY' : Disjoint D N.yPart := by
    simpa only [N, reverseABTriple_yPart] using hDY
  have hDZ' : Disjoint D N.zPart := by
    simpa only [N, reverseABTriple_zPart] using hDZ
  have hSa' : S'.a = N.xSep.left := by
    simpa only [S', MismatchedBoundaryPath.reverseAB, N,
      reverseABTriple_xSep_left] using hSb
  have hSb' : S'.b = N.zSep.right := by
    simpa only [S', MismatchedBoundaryPath.reverseAB, N,
      reverseABTriple_zSep_right] using hSa
  exact ABConnectorPair.hasCycleThroughThree_of_xA_zB_mismatchedBoundaryPath
    (M := N) C' h2' hA' hB' S' hD' hDX' hDY' hDZ' hSa' hSb'

/-- Reverse the A/B orientation to reduce an unmatched `zA--yB` path to
the `yA--zB` cyclic router. -/
theorem ABConnectorPair.hasCycleThroughThree_of_zA_yB_mismatchedBoundaryPath
    (C : M.ABConnectorPair) (h2 : C.IsTwoConnected)
    (hA : M.aSet.card = 3) (hB : M.bSet.card = 3)
    {D : Finset V} (S : M.MismatchedBoundaryPath D)
    (hD : IsComponentAfterDeleting G (M.aSet ∪ M.bSet) D)
    (hDX : Disjoint D M.xPart) (hDY : Disjoint D M.yPart)
    (hDZ : Disjoint D M.zPart)
    (hSa : S.a = M.zSep.left) (hSb : S.b = M.ySep.right) :
    HasCycleThroughThree G x y z := by
  let N := reverseABTriple M
  let C' := ABConnectorPair.reverseAB (M := M) C
  let S' := MismatchedBoundaryPath.reverseAB (M := M) S
  have h2' : C'.IsTwoConnected := by
    exact ABConnectorPair.reverseAB_isTwoConnected (M := M) C h2
  have hA' : N.aSet.card = 3 := by
    simpa only [N, reverseABTriple_aSet] using hB
  have hB' : N.bSet.card = 3 := by
    simpa only [N, reverseABTriple_bSet] using hA
  have hD' : IsComponentAfterDeleting G (N.aSet ∪ N.bSet) D := by
    simpa only [N, reverseABTriple_aSet, reverseABTriple_bSet,
      Finset.union_comm] using hD
  have hDX' : Disjoint D N.xPart := by
    simpa only [N, reverseABTriple_xPart] using hDX
  have hDY' : Disjoint D N.yPart := by
    simpa only [N, reverseABTriple_yPart] using hDY
  have hDZ' : Disjoint D N.zPart := by
    simpa only [N, reverseABTriple_zPart] using hDZ
  have hSa' : S'.a = N.ySep.left := by
    simpa only [S', MismatchedBoundaryPath.reverseAB, N,
      reverseABTriple_ySep_left] using hSb
  have hSb' : S'.b = N.zSep.right := by
    simpa only [S', MismatchedBoundaryPath.reverseAB, N,
      reverseABTriple_zSep_right] using hSa
  exact ABConnectorPair.hasCycleThroughThree_of_yA_zB_mismatchedBoundaryPath
    (M := N) C' h2' hA' hB' S' hD' hDX' hDY' hDZ' hSa' hSb'

/-- Every unmatched path between the two attachment triples has one of
the six off-diagonal orientations.  The cyclic and A/B-reversal routers
above reduce all six to the normalized `xA--yB` splice. -/
theorem ABConnectorPair.hasCycleThroughThree_of_mismatchedBoundaryPath
    (C : M.ABConnectorPair) (h2 : C.IsTwoConnected)
    (hA : M.aSet.card = 3) (hB : M.bSet.card = 3)
    {D : Finset V} (S : M.MismatchedBoundaryPath D)
    (hD : IsComponentAfterDeleting G (M.aSet ∪ M.bSet) D)
    (hDX : Disjoint D M.xPart) (hDY : Disjoint D M.yPart)
    (hDZ : Disjoint D M.zPart) :
    HasCycleThroughThree G x y z := by
  have ha : S.a = M.xSep.left ∨ S.a = M.ySep.left ∨
      S.a = M.zSep.left := by
    simpa [aSet] using S.a_mem
  have hb : S.b = M.xSep.right ∨ S.b = M.ySep.right ∨
      S.b = M.zSep.right := by
    simpa [bSet] using S.b_mem
  rcases ha with hax | hay | haz
  · rcases hb with hbx | hby | hbz
    · exact (S.unmatched (Or.inl ⟨hax, hbx⟩)).elim
    · exact
        ABConnectorPair.hasCycleThroughThree_of_normalized_mismatchedBoundaryPath
          (M := M) C h2 hA hB S hD hDX hDY hDZ hax hby
    · exact
        ABConnectorPair.hasCycleThroughThree_of_xA_zB_mismatchedBoundaryPath
          (M := M) C h2 hA hB S hD hDX hDY hDZ hax hbz
  · rcases hb with hbx | hby | hbz
    · exact
        ABConnectorPair.hasCycleThroughThree_of_yA_xB_mismatchedBoundaryPath
          (M := M) C h2 hA hB S hD hDX hDY hDZ hay hbx
    · exact (S.unmatched (Or.inr (Or.inl ⟨hay, hby⟩))).elim
    · exact
        ABConnectorPair.hasCycleThroughThree_of_yA_zB_mismatchedBoundaryPath
          (M := M) C h2 hA hB S hD hDX hDY hDZ hay hbz
  · rcases hb with hbx | hby | hbz
    · exact
        ABConnectorPair.hasCycleThroughThree_of_zA_xB_mismatchedBoundaryPath
          (M := M) C h2 hA hB S hD hDX hDY hDZ haz hbx
    · exact
        ABConnectorPair.hasCycleThroughThree_of_zA_yB_mismatchedBoundaryPath
          (M := M) C h2 hA hB S hD hDX hDY hDZ haz hby
    · exact (S.unmatched (Or.inr (Or.inr ⟨haz, hbz⟩))).elim

/-- An unmatched edge is the degenerate, length-one instance of the same
path obstruction.  Keeping it in the common path form lets the final AHT
cycle splice prove both clauses of condition (vii) at once. -/
theorem mismatchedBoundaryPath_of_unmatched_edge
    (D : Finset V) {a b : V} (ha : a ∈ M.aSet) (hb : b ∈ M.bSet)
    (hab : G.Adj a b) (hunmatched : ¬M.IsMatchedAttachmentPair a b) :
    Nonempty (M.MismatchedBoundaryPath D) := by
  let p : G.Walk a b := .cons hab .nil
  exact ⟨{
    a := a
    b := b
    a_mem := ha
    b_mem := hb
    unmatched := hunmatched
    path := p
    path_isPath := by
      simp [p, hab.ne]
    path_support := by
      intro w hw
      have : w = a ∨ w = b := by simpa [p] using hw
      exact this.elim Or.inl (fun h ↦ Or.inr (Or.inl h)) }⟩

/-- Failure of the five boundary alternatives in condition (vii) produces
an unmatched `A`--`B` path through the offending component.  This is the
precise reduction to the path `S` at the bottom of p.15 of AHT. -/
theorem exists_mismatchedBoundaryPath_of_boundary_failure
    (D : Finset V)
    (hD : IsComponentAfterDeleting G (M.aSet ∪ M.bSet) D)
    (hAcard : M.aSet.card = 3) (hBcard : M.bSet.card = 3)
    (hnotA : ¬HasExternalBoundaryIn G D M.aSet)
    (hnotB : ¬HasExternalBoundaryIn G D M.bSet)
    (hnotX : ¬HasExternalBoundaryIn G D
      {M.xSep.left, M.xSep.right})
    (hnotY : ¬HasExternalBoundaryIn G D
      {M.ySep.left, M.ySep.right})
    (hnotZ : ¬HasExternalBoundaryIn G D
      {M.zSep.left, M.zSep.right}) :
    Nonempty (M.MismatchedBoundaryPath D) := by
  classical
  have outside {U : Finset V} (hU : ¬HasExternalBoundaryIn G D U) :
      ∃ u ∈ D, ∃ w, G.Adj u w ∧ w ∉ D ∧ w ∉ U := by
    rw [HasExternalBoundaryIn] at hU
    push Not at hU
    exact hU
  have in_boundary {u w : V} (huD : u ∈ D) (huw : G.Adj u w)
      (hwD : w ∉ D) : w ∈ M.aSet ∪ M.bSet := by
    by_contra hw
    exact hwD (hD.2.2.2 u huD w hw huw)
  obtain ⟨uA, huAD, a, hua, haD, haB⟩ := outside hnotB
  have haAB := in_boundary huAD hua haD
  have haA : a ∈ M.aSet :=
    (Finset.mem_union.mp haAB).resolve_right haB
  obtain ⟨uB, huBD, b, hub, hbD, hbA⟩ := outside hnotA
  have hbAB := in_boundary huBD hub hbD
  have hbB : b ∈ M.bSet :=
    (Finset.mem_union.mp hbAB).resolve_left hbA
  obtain ⟨hAxy, hAxz, hAyz⟩ := M.a_attachments_pairwise_ne hAcard
  obtain ⟨hBxy, hBxz, hByz⟩ := M.b_attachments_pairwise_ne hBcard
  have hAyx := Ne.symm hAxy
  have hAzx := Ne.symm hAxz
  have hAzy := Ne.symm hAyz
  have hByx := Ne.symm hBxy
  have hBzx := Ne.symm hBxz
  have hBzy := Ne.symm hByz
  have make {a' b' u v : V} (huD : u ∈ D) (hvD : v ∈ D)
      (hua' : G.Adj u a') (hvb' : G.Adj v b')
      (ha' : a' ∈ M.aSet) (hb' : b' ∈ M.bSet)
      (hunmatched : ¬M.IsMatchedAttachmentPair a' b') :
      Nonempty (M.MismatchedBoundaryPath D) := by
    obtain ⟨p, hp, hpsub⟩ :=
      hD.exists_path_through_component huD hvD hua' hvb'
    exact ⟨{
      a := a'
      b := b'
      a_mem := ha'
      b_mem := hb'
      unmatched := hunmatched
      path := p
      path_isPath := hp
      path_support := hpsub }⟩
  by_cases hab : M.IsMatchedAttachmentPair a b
  · rcases hab with hX | hY | hZ
    · rcases hX with ⟨rfl, rfl⟩
      obtain ⟨u, huD, c, huc, hcD, hcPair⟩ := outside hnotX
      have hcAB := in_boundary huD huc hcD
      rcases Finset.mem_union.mp hcAB with hcA | hcB
      · have hc : c = M.xSep.left ∨ c = M.ySep.left ∨
            c = M.zSep.left := by simpa [aSet] using hcA
        rcases hc with rfl | rfl | rfl
        · exact (hcPair (by simp)).elim
        · apply make huD huBD huc hub hcA hbB
          simp_all [IsMatchedAttachmentPair]
        · apply make huD huBD huc hub hcA hbB
          simp_all [IsMatchedAttachmentPair]
      · have hc : c = M.xSep.right ∨ c = M.ySep.right ∨
            c = M.zSep.right := by simpa [bSet] using hcB
        rcases hc with rfl | rfl | rfl
        · exact (hcPair (by simp)).elim
        · apply make huAD huD hua huc haA hcB
          simp_all [IsMatchedAttachmentPair]
        · apply make huAD huD hua huc haA hcB
          simp_all [IsMatchedAttachmentPair]
    · rcases hY with ⟨rfl, rfl⟩
      obtain ⟨u, huD, c, huc, hcD, hcPair⟩ := outside hnotY
      have hcAB := in_boundary huD huc hcD
      rcases Finset.mem_union.mp hcAB with hcA | hcB
      · have hc : c = M.xSep.left ∨ c = M.ySep.left ∨
            c = M.zSep.left := by simpa [aSet] using hcA
        rcases hc with rfl | rfl | rfl
        · apply make huD huBD huc hub hcA hbB
          simp_all [IsMatchedAttachmentPair]
        · exact (hcPair (by simp)).elim
        · apply make huD huBD huc hub hcA hbB
          simp_all [IsMatchedAttachmentPair]
      · have hc : c = M.xSep.right ∨ c = M.ySep.right ∨
            c = M.zSep.right := by simpa [bSet] using hcB
        rcases hc with rfl | rfl | rfl
        · apply make huAD huD hua huc haA hcB
          simp_all [IsMatchedAttachmentPair]
        · exact (hcPair (by simp)).elim
        · apply make huAD huD hua huc haA hcB
          simp_all [IsMatchedAttachmentPair]
    · rcases hZ with ⟨rfl, rfl⟩
      obtain ⟨u, huD, c, huc, hcD, hcPair⟩ := outside hnotZ
      have hcAB := in_boundary huD huc hcD
      rcases Finset.mem_union.mp hcAB with hcA | hcB
      · have hc : c = M.xSep.left ∨ c = M.ySep.left ∨
            c = M.zSep.left := by simpa [aSet] using hcA
        rcases hc with rfl | rfl | rfl
        · apply make huD huBD huc hub hcA hbB
          simp_all [IsMatchedAttachmentPair]
        · apply make huD huBD huc hub hcA hbB
          simp_all [IsMatchedAttachmentPair]
        · exact (hcPair (by simp)).elim
      · have hc : c = M.xSep.right ∨ c = M.ySep.right ∨
            c = M.zSep.right := by simpa [bSet] using hcB
        rcases hc with rfl | rfl | rfl
        · apply make huAD huD hua huc haA hcB
          simp_all [IsMatchedAttachmentPair]
        · apply make huAD huD hua huc haA hcB
          simp_all [IsMatchedAttachmentPair]
        · exact (hcPair (by simp)).elim
  · exact make huAD huBD hua hub haA hbB hab

/-- Condition (vii), component-boundary clause.  If a remaining component
had none of the five permitted boundaries, the preceding extraction and
six-orientation router would produce a common cycle through `x,y,z`. -/
theorem ABConnectorPair.component_boundary_of_both_triples
    (C : M.ABConnectorPair) (h2 : C.IsTwoConnected)
    (hA : M.aSet.card = 3) (hB : M.bSet.card = 3)
    (hno : ¬HasCycleThroughThree G x y z)
    (D : Finset V)
    (hD : IsComponentAfterDeleting G (M.aSet ∪ M.bSet) D) :
    HasExternalBoundaryIn G D M.aSet ∨
      HasExternalBoundaryIn G D M.bSet ∨
      HasExternalBoundaryIn G D {M.xSep.left, M.xSep.right} ∨
      HasExternalBoundaryIn G D {M.ySep.left, M.ySep.right} ∨
      HasExternalBoundaryIn G D {M.zSep.left, M.zSep.right} := by
  by_contra hall
  have hnotA : ¬HasExternalBoundaryIn G D M.aSet := by
    intro h
    exact hall (Or.inl h)
  have hnotB : ¬HasExternalBoundaryIn G D M.bSet := by
    intro h
    exact hall (Or.inr (Or.inl h))
  have hnotX : ¬HasExternalBoundaryIn G D
      {M.xSep.left, M.xSep.right} := by
    intro h
    exact hall (Or.inr (Or.inr (Or.inl h)))
  have hnotY : ¬HasExternalBoundaryIn G D
      {M.ySep.left, M.ySep.right} := by
    intro h
    exact hall (Or.inr (Or.inr (Or.inr (Or.inl h))))
  have hnotZ : ¬HasExternalBoundaryIn G D
      {M.zSep.left, M.zSep.right} := by
    intro h
    exact hall (Or.inr (Or.inr (Or.inr (Or.inr h))))
  obtain ⟨S⟩ := M.exists_mismatchedBoundaryPath_of_boundary_failure
    D hD hA hB hnotA hnotB hnotX hnotY hnotZ
  obtain ⟨hDX, hDY, hDZ⟩ :=
    M.component_disjoint_terminal_parts_of_boundary_failure
      D hD hnotX hnotY hnotZ
  exact hno (ABConnectorPair.hasCycleThroughThree_of_mismatchedBoundaryPath
    (M := M) C h2 hA hB S hD hDX hDY hDZ)

/-- Assemble the literal seven-condition splitter once the maximal-
separator refinement lemmas have supplied the remaining disjointness,
cardinality, connectivity, and triple/triple restrictions.  All component
and unique-attachment fields are derived here rather than repeated by the
refinement proof. -/
noncomputable def toWatkinsMesnerSplitter
    (hdelete : ∀ d : V, (G.induce fun w : V ↦ w ≠ d).Connected)
    (hAcard : M.aSet.card = 1 ∨ M.aSet.card = 3)
    (hBcard : M.bSet.card = 1 ∨ M.bSet.card = 3)
    (hXtwo : ComplementVertexTwoConnected G M.xPart)
    (hYtwo : ComplementVertexTwoConnected G M.yPart)
    (hZtwo : ComplementVertexTwoConnected G M.zPart)
    (hmatched : M.aSet.card = 3 → M.bSet.card = 3 →
      ∀ a ∈ M.aSet, ∀ b ∈ M.bSet, G.Adj a b →
        (a = M.xSep.left ∧ b = M.xSep.right) ∨
        (a = M.ySep.left ∧ b = M.ySep.right) ∨
        (a = M.zSep.left ∧ b = M.zSep.right))
    (hboundary : M.aSet.card = 3 → M.bSet.card = 3 →
      ∀ D : Finset V, IsComponentAfterDeleting G (M.aSet ∪ M.bSet) D →
        HasExternalBoundaryIn G D M.aSet ∨
        HasExternalBoundaryIn G D M.bSet ∨
        HasExternalBoundaryIn G D {M.xSep.left, M.xSep.right} ∨
        HasExternalBoundaryIn G D {M.ySep.left, M.ySep.right} ∨
        HasExternalBoundaryIn G D {M.zSep.left, M.zSep.right}) :
    WatkinsMesnerSplitter G x y z := by
  classical
  have xB_not_A : M.xSep.right ∉ M.aSet := by
    intro h
    exact Finset.disjoint_left.mp M.aSet_disjoint_bSet h M.xB_mem_bSet
  have xA_not_B : M.xSep.left ∉ M.bSet := by
    intro h
    exact Finset.disjoint_left.mp M.aSet_disjoint_bSet M.xA_mem_aSet h
  have yB_not_A : M.ySep.right ∉ M.aSet := by
    intro h
    exact Finset.disjoint_left.mp M.aSet_disjoint_bSet h M.yB_mem_bSet
  have yA_not_B : M.ySep.left ∉ M.bSet := by
    intro h
    exact Finset.disjoint_left.mp M.aSet_disjoint_bSet M.yA_mem_aSet h
  have zB_not_A : M.zSep.right ∉ M.aSet := by
    intro h
    exact Finset.disjoint_left.mp M.aSet_disjoint_bSet h M.zB_mem_bSet
  have zA_not_B : M.zSep.left ∉ M.bSet := by
    intro h
    exact Finset.disjoint_left.mp M.aSet_disjoint_bSet M.zA_mem_aSet h
  refine {
    aSet := M.aSet
    bSet := M.bSet
    xPart := M.xPart
    yPart := M.yPart
    zPart := M.zPart
    xA := M.xSep.left
    yA := M.ySep.left
    zA := M.zSep.left
    xB := M.xSep.right
    yB := M.ySep.right
    zB := M.zSep.right
    A_nonempty := M.aSet_nonempty
    B_nonempty := M.bSet_nonempty
    A_disjoint_B := M.aSet_disjoint_bSet
    X_component := M.xPart_isComponent
    Y_component := M.yPart_isComponent
    Z_component := M.zPart_isComponent
    X_disjoint_Y := M.xPart_disjoint_yPart
    X_disjoint_Z := M.xPart_disjoint_zPart
    Y_disjoint_Z := M.yPart_disjoint_zPart
    x_mem_X := M.x_mem_xPart
    y_mem_Y := M.y_mem_yPart
    z_mem_Z := M.z_mem_zPart
    X_A_attachment := ComponentCompl.isUniqueAttachment_left
      M.xSep.left_ne_right hdelete M.xSep.side M.aSet
        M.xA_mem_aSet xB_not_A M.xPart_disjoint_aSet
    Y_A_attachment := ComponentCompl.isUniqueAttachment_left
      M.ySep.left_ne_right hdelete M.ySep.side M.aSet
        M.yA_mem_aSet yB_not_A M.yPart_disjoint_aSet
    Z_A_attachment := ComponentCompl.isUniqueAttachment_left
      M.zSep.left_ne_right hdelete M.zSep.side M.aSet
        M.zA_mem_aSet zB_not_A M.zPart_disjoint_aSet
    X_B_attachment := ComponentCompl.isUniqueAttachment_right
      M.xSep.left_ne_right hdelete M.xSep.side M.bSet
        M.xB_mem_bSet xA_not_B M.xPart_disjoint_bSet
    Y_B_attachment := ComponentCompl.isUniqueAttachment_right
      M.ySep.left_ne_right hdelete M.ySep.side M.bSet
        M.yB_mem_bSet yA_not_B M.yPart_disjoint_bSet
    Z_B_attachment := ComponentCompl.isUniqueAttachment_right
      M.zSep.left_ne_right hdelete M.zSep.side M.bSet
        M.zB_mem_bSet zA_not_B M.zPart_disjoint_bSet
    A_eq := rfl
    B_eq := rfl
    A_card := hAcard
    B_card := hBcard
    twoConnected_compl_X := hXtwo
    twoConnected_compl_Y := hYtwo
    twoConnected_compl_Z := hZtwo
    matched_edges_of_both_triples := hmatched
    component_boundary_of_both_triples := hboundary }

end WatkinsMesnerMaximalTriple

/-- The unconditional Watkins--Mesner splitter existence theorem.  Starting
from a vertex-two-connected graph with no common cycle through the three
distinct terminals, the maximal-separator construction and the minimal
connector refinement satisfy all seven literal splitter conditions. -/
theorem exists_watkinsMesnerSplitter
    {x y z : V}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hconn : G.Connected)
    (hdelete : ∀ d : V, (G.induce fun w : V ↦ w ≠ d).Connected)
    (hno : ¬HasCycleThroughThree G x y z) :
    Nonempty (WatkinsMesnerSplitter G x y z) := by
  classical
  obtain ⟨T⟩ := exists_watkinsMesnerK32Source
    hxy hxz hyz hconn hdelete hno
  obtain ⟨M⟩ := exists_watkinsMesnerMaximalTriple
    T hxy hxz hyz hconn hdelete hno
  obtain ⟨C⟩ := M.exists_minimalABConnectorPair
  have hAcard := M.aSet_card_one_or_three hdelete hno
  have hBcard := M.bSet_card_one_or_three hdelete hno
  refine ⟨M.toWatkinsMesnerSplitter hdelete hAcard hBcard
    (M.x_complementVertexTwoConnected hconn hdelete)
    (M.y_complementVertexTwoConnected hconn hdelete)
    (M.z_complementVertexTwoConnected hconn hdelete) ?_ ?_⟩
  · intro hA hB
    exact WatkinsMesnerMaximalTriple.ABConnectorPair.matched_edges_of_both_triples
      (M := M) C.toABConnectorPair
      (WatkinsMesnerMaximalTriple.MinimalABConnectorPair.isTwoConnected
        (M := M) C hconn hdelete hno hA hB) hA hB hno
  · intro hA hB D hD
    exact WatkinsMesnerMaximalTriple.ABConnectorPair.component_boundary_of_both_triples
      (M := M) C.toABConnectorPair
      (WatkinsMesnerMaximalTriple.MinimalABConnectorPair.isTwoConnected
        (M := M) C hconn hdelete hno hA hB) hA hB hno D hD

end Erdos916
