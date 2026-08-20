/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos916.AHTMader
import ErdosProblems.Erdos916.AHTSourceLemma62
import ErdosProblems.Erdos916.AHTSourceLemma64
import ErdosProblems.Erdos916.AHTWatkinsMesner
import ErdosProblems.Erdos916.AHTK32Routing
import ErdosProblems.Erdos718
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Walk.Decomp
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps

/-!
# The edge-minimal three-connectivity reduction in AHT Section 4

This file isolates the exact last path certificate in AHT Lemma 4.5.  If
deleting `ab` leaves a three-connected graph, the source proof constructs,
for each endpoint (say `a`), a cycle in the deleted-edge graph which avoids
`a` and contains `b` and two distinct surviving neighbours of `a`.  That
cycle is immediately the rim of a wheel centred at `a`.

The construction of this cycle is the only remaining Menger/fan step.  The
lemmas below formalize all bookkeeping after that step, including the exact
degree contradiction which proves Corollary 4.6.
-/

attribute [local instance] Classical.propDecidable

namespace Erdos916

open _root_.SimpleGraph

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

namespace AHTMinimalThreeConnected

private theorem eraseEdge_le_local (G : SimpleGraph V) (a b : V) :
    eraseEdge G a b ≤ G := by
  exact SimpleGraph.deleteEdges_le _

private theorem not_eraseEdge_adj_endpoints {a b : V} :
    ¬(eraseEdge G a b).Adj a b := by
  simp

/-! ## The three internally disjoint endpoint paths -/

/-- Replace `a` and `b` by three copies each, retaining one copy of every
other vertex.  Menger on this auxiliary graph gives three internally
vertex-disjoint `a`--`b` paths. -/
abbrev SplitEndpoints (a b : V) :=
  Fin 3 ⊕ ({v : V // v ≠ a ∧ v ≠ b} ⊕ Fin 3)

def splitEndpointsCollapse (a b : V) : SplitEndpoints a b → V
  | .inl _ => a
  | .inr (.inl v) => v.1
  | .inr (.inr _) => b

def splitEndpointsGraph (H : SimpleGraph V) (a b : V) :
    SimpleGraph (SplitEndpoints a b) :=
  H.comap (splitEndpointsCollapse a b)

def splitSource {a b : V} (i : Fin 3) : SplitEndpoints a b := .inl i

def splitTarget {a b : V} (i : Fin 3) : SplitEndpoints a b := .inr (.inr i)

def splitOld {a b : V} (v : {v : V // v ≠ a ∧ v ≠ b}) :
    SplitEndpoints a b := .inr (.inl v)

@[simp] theorem splitEndpointsCollapse_source (a b : V) (i : Fin 3) :
    splitEndpointsCollapse a b (splitSource i) = a := rfl

@[simp] theorem splitEndpointsCollapse_target (a b : V) (i : Fin 3) :
    splitEndpointsCollapse a b (splitTarget i) = b := rfl

@[simp] theorem splitEndpointsCollapse_old {a b : V}
    (v : {v : V // v ≠ a ∧ v ≠ b}) :
    splitEndpointsCollapse a b (splitOld v) = v.1 := rfl

private def splitLift {a b : V} (i j : Fin 3) (v : V) :
    SplitEndpoints a b :=
  if hva : v = a then splitSource i
  else if hvb : v = b then splitTarget j
  else splitOld ⟨v, hva, hvb⟩

@[simp] private theorem splitLift_at_left {a b : V} (i j : Fin 3) :
    splitLift i j a = (splitSource i : SplitEndpoints a b) := by
  simp [splitLift]

@[simp] private theorem splitLift_at_right {a b : V} (hab : a ≠ b)
    (i j : Fin 3) :
    splitLift i j b = (splitTarget j : SplitEndpoints a b) := by
  simp [splitLift, hab.symm]

@[simp] private theorem collapse_splitLift {a b : V} (i j : Fin 3) (v : V) :
    splitEndpointsCollapse a b (splitLift i j v) = v := by
  simp only [splitLift]
  split
  · rename_i h; simp [h]
  · split
    · rename_i h; simp [h]
    · rfl

private theorem splitLift_injective {a b : V} (i j : Fin 3) :
    Function.Injective (splitLift (a := a) (b := b) i j) := by
  intro x y h
  have := congrArg (splitEndpointsCollapse a b) h
  simpa using this

private def splitLiftHom (H : SimpleGraph V) {a b : V} (i j : Fin 3) :
    H →g splitEndpointsGraph H a b where
  toFun := splitLift i j
  map_rel' := by
    intro x y hxy
    change H.Adj
      (splitEndpointsCollapse a b (splitLift i j x))
      (splitEndpointsCollapse a b (splitLift i j y))
    simpa using hxy

def splitSources (a b : V) : Set (SplitEndpoints a b) := Set.range splitSource

def splitTargets (a b : V) : Set (SplitEndpoints a b) := Set.range splitTarget

@[simp] theorem mem_splitSources {a b : V} {z : SplitEndpoints a b} :
    z ∈ splitSources a b ↔ ∃ i, z = splitSource i := by
  simp [splitSources, eq_comm]

@[simp] theorem mem_splitTargets {a b : V} {z : SplitEndpoints a b} :
    z ∈ splitTargets a b ↔ ∃ i, z = splitTarget i := by
  simp [splitTargets, eq_comm]

/-- The finite Menger input for the split-endpoint construction.  This is
the first substantive step of AHT Lemma 4.5. -/
private theorem splitEndpoints_separator_three_le_type0
    {V : Type} [Fintype V] [DecidableEq V]
    {H : SimpleGraph V} [DecidableRel H.Adj]
    {a b : V} (hab : a ≠ b) (hthree : IsThreeConnected H)
    (S : Set (SplitEndpoints a b))
    (hS : Erdos599.Separates (splitEndpointsGraph H a b)
      (splitSources a b) (splitTargets a b) S) :
    3 ≤ S.ncard := by
  classical
  by_contra hnot
  have hSlt : S.ncard < 3 := Nat.lt_of_not_ge hnot
  have hi : ∃ i : Fin 3, splitSource i ∉ S := by
    by_contra hall
    push_neg at hall
    have hsub : Set.range (splitSource (a := a) (b := b)) ⊆ S := by
      rintro _ ⟨i, rfl⟩
      exact hall i
    have hcard := Set.ncard_le_ncard hsub
    rw [Set.ncard_range_of_injective] at hcard
    · have hthreeS : 3 ≤ S.ncard := by simpa using hcard
      exact (not_lt_of_ge hthreeS hSlt)
    · intro i j hij
      exact Sum.inl.inj hij
  have hj : ∃ j : Fin 3, splitTarget j ∉ S := by
    by_contra hall
    push_neg at hall
    have hsub : Set.range (splitTarget (a := a) (b := b)) ⊆ S := by
      rintro _ ⟨j, rfl⟩
      exact hall j
    have hcard := Set.ncard_le_ncard hsub
    rw [Set.ncard_range_of_injective] at hcard
    · have hthreeS : 3 ≤ S.ncard := by simpa using hcard
      exact (not_lt_of_ge hthreeS hSlt)
    · intro i j hij
      exact Sum.inr.inj (Sum.inr.inj hij)
  obtain ⟨i, hiS⟩ := hi
  obtain ⟨j, hjS⟩ := hj
  let D : Finset V := Finset.univ.filter fun v =>
    ∃ hva : v ≠ a, ∃ hvb : v ≠ b,
      splitOld (⟨v, hva, hvb⟩ : {w : V // w ≠ a ∧ w ≠ b}) ∈ S
  have hDcard : D.card ≤ S.ncard := by
    let toS : {v : V // v ∈ D} → {z : SplitEndpoints a b // z ∈ S} := fun v => by
      have hv : ∃ hva : v.1 ≠ a, ∃ hvb : v.1 ≠ b,
          splitOld (⟨v.1, hva, hvb⟩ :
            {w : V // w ≠ a ∧ w ≠ b}) ∈ S := by
        simpa only [D, Finset.mem_filter, Finset.mem_univ, true_and] using v.2
      let hva : v.1 ≠ a := Classical.choose hv
      let hv' := Classical.choose_spec hv
      let hvb : v.1 ≠ b := Classical.choose hv'
      have hvS : splitOld (⟨v.1, hva, hvb⟩ :
          {w : V // w ≠ a ∧ w ≠ b}) ∈ S := Classical.choose_spec hv'
      exact ⟨splitOld ⟨v.1, hva, hvb⟩, hvS⟩
    have hinj : Function.Injective toS := by
      intro v w hvw
      apply Subtype.ext
      have := congrArg (fun z : {z : SplitEndpoints a b // z ∈ S} =>
        splitEndpointsCollapse a b z.1) hvw
      simpa [toS] using this
    letI : Fintype S := Fintype.ofFinite S
    have hc := Fintype.card_le_of_injective toS hinj
    simpa [Set.fintypeCard_eq_ncard] using hc
  have hDlt : D.card < 3 := lt_of_le_of_lt hDcard hSlt
  have haD : a ∉ D := by simp [D]
  have hbD : b ∉ D := by simp [D]
  have hpre := hthree.induce_compl_preconnected D hDlt
  let aD : {v : V // v ∉ D} := ⟨a, haD⟩
  let bD : {v : V // v ∉ D} := ⟨b, hbD⟩
  obtain ⟨pD, hpD⟩ := (hpre aD bD).exists_isPath
  let inc : H.induce {v : V | v ∉ D} →g H :=
    (SimpleGraph.Embedding.induce (G := H) (s := {v : V | v ∉ D})).toHom
  let p : H.Walk a b := pD.map inc
  have hp : p.IsPath := hpD.map Subtype.val_injective
  let q0 := p.map (splitLiftHom H (a := a) (b := b) i j)
  let q : (splitEndpointsGraph H a b).Walk (splitSource i) (splitTarget j) :=
    q0.copy (by
      change splitLift i j a = (splitSource i : SplitEndpoints a b)
      exact splitLift_at_left i j)
      (by
        change splitLift i j b = (splitTarget j : SplitEndpoints a b)
        exact splitLift_at_right hab i j)
  have hq : q.IsPath := by
    apply (Walk.isPath_copy _ _ _).mpr
    exact hp.map (splitLift_injective i j)
  rcases hS (splitSource i) (by simp) (splitTarget j) (by simp) q hq with
    ⟨z, hzq, hzS⟩
  have hzq0 : z ∈ q0.support := by simpa [q, Walk.support_copy] using hzq
  change z ∈ (p.map (splitLiftHom H (a := a) (b := b) i j)).support at hzq0
  rw [Walk.support_map] at hzq0
  obtain ⟨w, hwp, hwz⟩ := List.mem_map.mp hzq0
  have hwD : w ∉ D := by
    change w ∈ (pD.map inc).support at hwp
    rw [Walk.support_map] at hwp
    obtain ⟨wD, _hwDp, hwDw⟩ := List.mem_map.mp hwp
    have hwval : wD.1 = w := by simpa [inc] using hwDw
    exact fun hwmem => wD.2 (hwval ▸ hwmem)
  by_cases hwa : w = a
  · subst w
    have hz : z = splitSource i := by
      change splitLift i j a = z at hwz
      exact hwz.symm.trans (splitLift_at_left i j)
    exact hiS (hz ▸ hzS)
  by_cases hwb : w = b
  · subst w
    have hz : z = splitTarget j := by
      change splitLift i j b = z at hwz
      exact hwz.symm.trans (splitLift_at_right hab i j)
    exact hjS (hz ▸ hzS)
  have hzold : z = splitOld (⟨w, hwa, hwb⟩ :
      {v : V // v ≠ a ∧ v ≠ b}) := by
    change splitLift i j w = z at hwz
    exact hwz.symm.trans (by simp [splitLift, hwa, hwb])
  apply hwD
  simp only [D, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨hwa, hwb, hzold ▸ hzS⟩

/-- Three fully disjoint paths between the three split copies of the two
endpoints.  Collapsing the copies gives the standard three internally
disjoint `a`--`b` paths used at the start of AHT Lemma 4.5. -/
theorem exists_three_splitEndpoint_paths_type0
    {V : Type} [Fintype V] [DecidableEq V]
    {H : SimpleGraph V} [DecidableRel H.Adj]
    {a b : V} (hab : a ≠ b) (hthree : IsThreeConnected H) :
    Nonempty (Erdos718.ABLinkage (splitEndpointsGraph H a b)
      (splitSources a b) (splitTargets a b) 3) := by
  apply Erdos718.exists_abLinkage_of_forall_separator_ncard_ge
  intro S hS
  exact splitEndpoints_separator_three_le_type0 hab hthree S hS

private def splitSourceFinset (a b : V) : Finset (SplitEndpoints a b) :=
  Finset.univ.image splitSource

private def splitTargetFinset (a b : V) : Finset (SplitEndpoints a b) :=
  Finset.univ.image splitTarget

@[simp] private theorem mem_splitSourceFinset {a b : V}
    {z : SplitEndpoints a b} :
    z ∈ splitSourceFinset a b ↔ ∃ i : Fin 3, z = splitSource i := by
  simp [splitSourceFinset, eq_comm]

@[simp] private theorem mem_splitTargetFinset {a b : V}
    {z : SplitEndpoints a b} :
    z ∈ splitTargetFinset a b ↔ ∃ i : Fin 3, z = splitTarget i := by
  simp [splitTargetFinset, eq_comm]

/-- Trim one path of the split-endpoint linkage at its last source copy and
first target copy.  Its support is still contained in the original linkage
path, and no other split copy of either endpoint remains. -/
private theorem ABLinkage.exists_clean_splitEndpoint_path
    {V : Type} [Fintype V] [DecidableEq V]
    {H : SimpleGraph V} [DecidableRel H.Adj]
    {a b : V}
    (L : Erdos718.ABLinkage (splitEndpointsGraph H a b)
      (splitSources a b) (splitTargets a b) 3)
    (i : Fin 3) :
    ∃ si ti : Fin 3,
      ∃ p : (splitEndpointsGraph H a b).Walk (splitSource si) (splitTarget ti),
        p.IsPath ∧
        (∀ z, z ∈ p.support → z ∈ (L.path i).support) ∧
        (∀ z, z ∈ p.support → z ∈ splitSources a b → z = splitSource si) ∧
        (∀ z, z ∈ p.support → z ∈ splitTargets a b → z = splitTarget ti) := by
  classical
  obtain ⟨li, hli⟩ := (mem_splitSources.mp (L.left_mem i))
  obtain ⟨ri, hri⟩ := (mem_splitTargets.mp (L.right_mem i))
  let T := splitTargetFinset a b
  have hleftT : L.left i ∉ T := by
    rw [hli]
    intro h
    obtain ⟨j, hj⟩ := mem_splitTargetFinset.mp h
    exact Sum.inl_ne_inr hj
  have hrightT : L.right i ∈ T := by
    rw [hri]
    simp [T]
  obtain ⟨t, htT, q, hq, hqsub, hqfirst⟩ :=
    exists_initialPath_to_finset T hleftT hrightT (L.path i) (L.isPath i)
  let S := splitSourceFinset a b
  have htS : t ∉ S := by
    obtain ⟨ti, rfl⟩ := mem_splitTargetFinset.mp htT
    intro h
    obtain ⟨j, hj⟩ := mem_splitSourceFinset.mp h
    exact Sum.inr_ne_inl hj
  have hleftS : L.left i ∈ S := by
    rw [hli]
    simp [S]
  have hleftQ : L.left i ∈ q.reverse.support := by simp
  obtain ⟨s, hsS, r, hr, hrsub, hrfirst⟩ :=
    exists_initialPath_to_finset S htS hleftS q.reverse hq.reverse
  obtain ⟨si, hsi⟩ := mem_splitSourceFinset.mp hsS
  obtain ⟨ti, hti⟩ := mem_splitTargetFinset.mp htT
  subst s
  subst t
  let p : (splitEndpointsGraph H a b).Walk (splitSource si) (splitTarget ti) :=
    r.reverse
  refine ⟨si, ti, p, hr.reverse, ?_, ?_, ?_⟩
  · intro z hzp
    have hzr : z ∈ r.support := by simpa [p] using hzp
    have hzqrev : z ∈ q.reverse.support := hrsub z hzr
    have hzq : z ∈ q.support := by simpa using hzqrev
    exact hqsub z hzq
  · intro z hzp hzsource
    have hzr : z ∈ r.support := by simpa [p] using hzp
    have hzS : z ∈ S := by
      simpa only [S, mem_splitSourceFinset, mem_splitSources] using hzsource
    exact hrfirst z hzr hzS
  · intro z hzp hztarget
    have hzr : z ∈ r.support := by simpa [p] using hzp
    have hzqrev : z ∈ q.reverse.support := hrsub z hzr
    have hzq : z ∈ q.support := by simpa using hzqrev
    have hzT : z ∈ T := by
      simpa only [T, mem_splitTargetFinset, mem_splitTargets] using hztarget
    exact hqfirst z hzq hzT

private def splitEndpointsCollapseHom (H : SimpleGraph V) (a b : V) :
    splitEndpointsGraph H a b →g H where
  toFun := splitEndpointsCollapse a b
  map_rel' := by intro x y hxy; exact hxy

/-- The collapse map is injective on a clean split path. -/
private theorem collapse_injOn_clean_splitPath
    {a b : V} (hab : a ≠ b) {si ti : Fin 3}
    {p : (splitEndpointsGraph G a b).Walk (splitSource si) (splitTarget ti)}
    (hsource : ∀ z, z ∈ p.support →
      z ∈ splitSources a b → z = splitSource si)
    (htarget : ∀ z, z ∈ p.support →
      z ∈ splitTargets a b → z = splitTarget ti) :
    Set.InjOn (splitEndpointsCollapse a b) {z | z ∈ p.support} := by
  intro x hx y hy hxy
  rcases x with i | x
  · have hxi : (Sum.inl i : SplitEndpoints a b) = splitSource si :=
      hsource _ hx (by exact ⟨i, rfl⟩)
    rcases y with j | y
    · have hyj : (Sum.inl j : SplitEndpoints a b) = splitSource si :=
        hsource _ hy (by exact ⟨j, rfl⟩)
      exact hxi.trans hyj.symm
    · rcases y with v | j
      · exact (v.2.1 hxy.symm).elim
      · exact (hab hxy).elim
  · rcases x with v | i
    · rcases y with j | y
      · exact (v.2.1 hxy).elim
      · rcases y with w | j
        · exact congrArg Sum.inr (congrArg Sum.inl (Subtype.ext hxy))
        · exact (v.2.2 hxy).elim
    · have hxi : (Sum.inr (Sum.inr i) : SplitEndpoints a b) = splitTarget ti :=
        htarget _ hx (by exact ⟨i, rfl⟩)
      rcases y with j | y
      · exact (hab hxy.symm).elim
      · rcases y with v | j
        · exact (v.2.2 hxy.symm).elim
        · have hyj : (Sum.inr (Sum.inr j) : SplitEndpoints a b) = splitTarget ti :=
            htarget _ hy (by exact ⟨j, rfl⟩)
          exact hxi.trans hyj.symm

private theorem splitEndpoints_eq_of_collapse_eq_of_ne
    {a b : V} {x y : SplitEndpoints a b}
    (hxa : splitEndpointsCollapse a b x ≠ a)
    (hxb : splitEndpointsCollapse a b x ≠ b)
    (hya : splitEndpointsCollapse a b y ≠ a)
    (hyb : splitEndpointsCollapse a b y ≠ b)
    (hxy : splitEndpointsCollapse a b x = splitEndpointsCollapse a b y) :
    x = y := by
  rcases x with i | x
  · exact (hxa rfl).elim
  · rcases x with v | i
    · rcases y with j | y
      · exact (hya rfl).elim
      · rcases y with w | j
        · exact congrArg Sum.inr (congrArg Sum.inl (Subtype.ext hxy))
        · exact (hyb rfl).elim
    · exact (hxb rfl).elim

/-- Three `a`--`b` paths whose interiors are pairwise disjoint. -/
structure ThreeEndpointPaths (H : SimpleGraph V) (a b : V) where
  path : Fin 3 → H.Walk a b
  isPath : ∀ i, (path i).IsPath
  meet_only_endpoints : Pairwise fun i j ↦
    ∀ w, w ∈ (path i).support → w ∈ (path j).support → w = a ∨ w = b

/-- Collapse the cleaned split linkage.  Full disjointness upstairs becomes
pairwise interior disjointness downstairs, since only the split copies of
`a` and `b` are identified. -/
theorem exists_threeEndpointPaths
    {V : Type} [Fintype V] [DecidableEq V]
    {H : SimpleGraph V} [DecidableRel H.Adj]
    {a b : V} (hab : a ≠ b) (hthree : IsThreeConnected H) :
    Nonempty (ThreeEndpointPaths H a b) := by
  classical
  obtain ⟨L⟩ := exists_three_splitEndpoint_paths_type0 hab hthree
  choose si ti p hp hsub hsource htarget using
    fun i ↦
      Erdos916.AHTMinimalThreeConnected.ABLinkage.exists_clean_splitEndpoint_path L i
  let collapse := splitEndpointsCollapseHom H a b
  let q : ∀ i : Fin 3, H.Walk a b := fun i ↦ (p i).map collapse
  have hqPath : ∀ i, (q i).IsPath := by
    intro i
    change ((p i).map collapse).IsPath
    rw [Walk.isPath_def, Walk.support_map]
    exact (hp i).support_nodup.map_on
      (collapse_injOn_clean_splitPath hab (hsource i) (htarget i))
  refine ⟨{
    path := q
    isPath := hqPath
    meet_only_endpoints := ?_ }⟩
  intro i j hij w hwi hwj
  by_contra hends
  push Not at hends
  have hwa : w ≠ a := hends.1
  have hwb : w ≠ b := hends.2
  change w ∈ ((p i).map collapse).support at hwi
  change w ∈ ((p j).map collapse).support at hwj
  rw [Walk.support_map] at hwi hwj
  obtain ⟨zi, hzi, hziw⟩ := List.mem_map.mp hwi
  obtain ⟨zj, hzj, hzjw⟩ := List.mem_map.mp hwj
  have hzia : splitEndpointsCollapse a b zi ≠ a := by
    intro h
    exact hwa (hziw.symm.trans h)
  have hzib : splitEndpointsCollapse a b zi ≠ b := by
    intro h
    exact hwb (hziw.symm.trans h)
  have hzja : splitEndpointsCollapse a b zj ≠ a := by
    intro h
    exact hwa (hzjw.symm.trans h)
  have hzjb : splitEndpointsCollapse a b zj ≠ b := by
    intro h
    exact hwb (hzjw.symm.trans h)
  have hzizj : zi = zj := splitEndpoints_eq_of_collapse_eq_of_ne
    hzia hzib hzja hzjb (hziw.trans hzjw.symm)
  have hziL : zi ∈ (L.path i).support := hsub i zi hzi
  have hzjL : zj ∈ (L.path j).support := hsub j zj hzj
  exact Set.disjoint_left.mp (L.disjoint hij) hziL (hzizj ▸ hzjL)

/-- The first edges of three internally disjoint `a`--`b` paths give three
distinct neighbours of `a` and pairwise internally disjoint arms from those
neighbours to `b`. -/
structure ThreeFanToEndpoint (H : SimpleGraph V) (a b : V) where
  neighbor : Fin 3 → V
  neighbor_injective : Function.Injective neighbor
  adj_neighbor : ∀ i, H.Adj a (neighbor i)
  neighbor_ne_endpoint : ∀ i, neighbor i ≠ b
  arm : ∀ i, H.Walk (neighbor i) b
  arm_isPath : ∀ i, (arm i).IsPath
  center_not_mem : ∀ i, a ∉ (arm i).support
  arms_meet_only_endpoint : Pairwise fun i j ↦
    ∀ w, w ∈ (arm i).support → w ∈ (arm j).support → w = b

theorem exists_threeFanToEndpoint
    {V : Type} [Fintype V] [DecidableEq V]
    {H : SimpleGraph V} [DecidableRel H.Adj]
    {a b : V} (hab : a ≠ b) (hnadj : ¬H.Adj a b)
    (hthree : IsThreeConnected H) :
    Nonempty (ThreeFanToEndpoint H a b) := by
  obtain ⟨P⟩ := exists_threeEndpointPaths hab hthree
  have hnonNil : ∀ i, ¬(P.path i).Nil := fun i ↦
    (P.path i).not_nil_of_ne hab
  let n : Fin 3 → V := fun i ↦ (P.path i).snd
  let arm : ∀ i : Fin 3, H.Walk (n i) b := fun i ↦ (P.path i).tail
  have hadj : ∀ i, H.Adj a (n i) := by
    intro i
    exact (P.path i).adj_snd (hnonNil i)
  have hnb : ∀ i, n i ≠ b := by
    intro i h
    exact hnadj (h ▸ hadj i)
  have haArm : ∀ i, a ∉ (arm i).support := by
    intro i
    have hnd := (P.isPath i).support_nodup
    rw [← (P.path i).cons_support_tail (hnonNil i)] at hnd
    exact (List.nodup_cons.mp hnd).1
  have hmeet : Pairwise fun i j ↦
      ∀ w, w ∈ (arm i).support → w ∈ (arm j).support → w = b := by
    intro i j hij w hwi hwj
    have hwi' : w ∈ (P.path i).support := by
      rw [← (P.path i).cons_support_tail (hnonNil i)]
      exact List.mem_cons_of_mem a hwi
    have hwj' : w ∈ (P.path j).support := by
      rw [← (P.path j).cons_support_tail (hnonNil j)]
      exact List.mem_cons_of_mem a hwj
    rcases P.meet_only_endpoints hij w hwi' hwj' with hwa | hwb
    · exact (haArm i (hwa ▸ hwi)).elim
    · exact hwb
  have hninj : Function.Injective n := by
    intro i j hn
    by_contra hij
    have hni : n i ∈ (arm i).support := (arm i).start_mem_support
    have hnj : n j ∈ (arm j).support := (arm j).start_mem_support
    have hnj' : n i ∈ (arm j).support := by
      rw [hn]
      exact hnj
    have := hmeet hij (n i) hni hnj'
    exact hnb i this
  refine ⟨{
    neighbor := n
    neighbor_injective := hninj
    adj_neighbor := hadj
    neighbor_ne_endpoint := hnb
    arm := arm
    arm_isPath := fun i ↦ (P.isPath i).tail
    center_not_mem := haArm
    arms_meet_only_endpoint := hmeet }⟩

/-- The cycle-selection core of AHT Lemma 4.5.  In the graph obtained by
deleting the prospective centre `a`, either the three fan starts lie on one
cycle, or the Watkins--Mesner `K_{3,2}` source together with the three fan
arms yields a cycle through `b` and two fan starts. -/
private theorem cycleAlternative_of_threeFanToEndpoint_type0
    {V : Type} [Fintype V] [DecidableEq V]
    {H : SimpleGraph V} [DecidableRel H.Adj]
    {a b : V} (hab : a ≠ b) (hthree : IsThreeConnected H)
    (F : ThreeFanToEndpoint H a b) :
    let K := H.induce fun w : V ↦ w ≠ a
    let n : Fin 3 → {w : V // w ≠ a} := fun i ↦
      ⟨F.neighbor i, (F.adj_neighbor i).ne.symm⟩
    let b' : {w : V // w ≠ a} := ⟨b, hab.symm⟩
    HasCycleThroughThree K (n 0) (n 1) (n 2) ∨
      HasCycleThroughThree K b' (n 0) (n 1) ∨
      HasCycleThroughThree K b' (n 0) (n 2) ∨
      HasCycleThroughThree K b' (n 1) (n 2) := by
  let K := H.induce fun w : V ↦ w ≠ a
  let n : Fin 3 → {w : V // w ≠ a} := fun i ↦
    ⟨F.neighbor i, (F.adj_neighbor i).ne.symm⟩
  let b' : {w : V // w ≠ a} := ⟨b, hab.symm⟩
  have hninj : Function.Injective n := by
    intro i j hij
    apply F.neighbor_injective
    exact congrArg Subtype.val hij
  have hn01 : n 0 ≠ n 1 := hninj.ne (by decide)
  have hn02 : n 0 ≠ n 2 := hninj.ne (by decide)
  have hn12 : n 1 ≠ n 2 := hninj.ne (by decide)
  have htwo := vertexTwoConnected_delete_of_isThreeConnected hthree a
  by_cases hcycle : HasCycleThroughThree K (n 0) (n 1) (n 2)
  · exact Or.inl hcycle
  right
  obtain ⟨T⟩ := exists_watkinsMesnerK32Source
    hn01 hn02 hn12 htwo.1 htwo.2 hcycle
  have hsupport (i : Fin 3) :
      ∀ w, w ∈ (F.arm i).support → w ≠ a := by
    intro w hw hwa
    subst w
    exact F.center_not_mem i hw
  let armK : ∀ i : Fin 3, K.Walk (n i) b' := fun i ↦
    ((F.arm i).induce (fun w : V ↦ w ≠ a) (hsupport i)).copy
      (Subtype.ext rfl) (Subtype.ext rfl)
  let inc : K →g H :=
    (SimpleGraph.Embedding.induce (G := H) (s := fun w : V ↦ w ≠ a)).toHom
  have harmMap (i : Fin 3) : (armK i).map inc = F.arm i := by
    simp only [armK, inc, Walk.map_copy]
    exact Walk.map_induce (s := fun w : V ↦ w ≠ a)
      (F.arm i) (hsupport i)
  have harmPath (i : Fin 3) : (armK i).IsPath := by
    apply Walk.IsPath.of_map (f := inc)
    rw [harmMap]
    exact F.arm_isPath i
  have harmMem {i : Fin 3} {w : {w : V // w ≠ a}}
      (hw : w ∈ (armK i).support) : w.1 ∈ (F.arm i).support := by
    have hw' : w.1 ∈ ((armK i).map inc).support := by
      rw [Walk.support_map]
      exact List.mem_map.mpr ⟨w, hw, rfl⟩
    rwa [harmMap] at hw'
  have hmeet {i j : Fin 3} (hij : i ≠ j) :
      ∀ w, w ∈ (armK i).support → w ∈ (armK j).support → w = b' := by
    intro w hwi hwj
    apply Subtype.ext
    exact F.arms_meet_only_endpoint hij w.1 (harmMem hwi) (harmMem hwj)
  rcases AHTK32Routing.cycleThroughTwoTerminals_of_k32Source_and_threeArms
      T (armK 0) (armK 1) (armK 2)
      (harmPath 0) (harmPath 1) (harmPath 2)
      (hmeet (by decide)) (hmeet (by decide)) (hmeet (by decide)) with
    h01 | h02 | h12
  · exact Or.inl h01
  · exact Or.inr (Or.inl h02)
  · exact Or.inr (Or.inr h12)

/-- A simple cycle avoiding a vertex and containing three displayed,
pairwise-distinct neighbours witnesses that the vertex is a wheel centre. -/
theorem hasWheelCenteredAt_of_cycle_three_neighbors
    {r k n₀ n₁ n₂ : V} (C : G.Walk r r) (hC : C.IsCycle)
    (hkC : k ∉ C.support)
    (hkn₀ : G.Adj k n₀) (hkn₁ : G.Adj k n₁) (hkn₂ : G.Adj k n₂)
    (hn₀C : n₀ ∈ C.support) (hn₁C : n₁ ∈ C.support)
    (hn₂C : n₂ ∈ C.support)
    (hn₀n₁ : n₀ ≠ n₁) (hn₀n₂ : n₀ ≠ n₂) (hn₁n₂ : n₁ ≠ n₂) :
    HasWheelCenteredAt G k := by
  refine ⟨r, C, hC, hkC, ?_⟩
  have hn₀ : n₀ ∈ G.neighborFinset k ∩ C.support.toFinset := by
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
      List.mem_toFinset]
    exact ⟨hkn₀, hn₀C⟩
  have hn₁ : n₁ ∈ G.neighborFinset k ∩ C.support.toFinset := by
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
      List.mem_toFinset]
    exact ⟨hkn₁, hn₁C⟩
  have hn₂ : n₂ ∈ G.neighborFinset k ∩ C.support.toFinset := by
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
      List.mem_toFinset]
    exact ⟨hkn₂, hn₂C⟩
  exact (by
    have := Finset.two_lt_card_iff.mpr
      ⟨n₀, n₁, n₂, hn₀, hn₁, hn₂, hn₀n₁, hn₀n₂, hn₁n₂⟩
    omega)

/-- Wheel centres are invariant under graph isomorphism.  The proof chooses
three explicit neighbours on the old rim, maps the rim, and reuses the
three-neighbour wheel criterion. -/
private theorem hasWheelCenteredAt_map_iso
    {W : Type*} [Fintype W] [DecidableEq W]
    {G : SimpleGraph V} {J : SimpleGraph W}
    [DecidableRel G.Adj] [DecidableRel J.Adj]
    (e : G ≃g J) {a : V} (ha : HasWheelCenteredAt G a) :
    HasWheelCenteredAt J (e a) := by
  obtain ⟨r, C, hC, haC, hthree⟩ := ha
  have htwo : 2 < (G.neighborFinset a ∩ C.support.toFinset).card := by
    omega
  obtain ⟨x₀, x₁, x₂, hx₀, hx₁, hx₂, hx₀x₁, hx₀x₂, hx₁x₂⟩ :=
    Finset.two_lt_card_iff.mp htwo
  have hx₀' := Finset.mem_inter.mp hx₀
  have hx₁' := Finset.mem_inter.mp hx₁
  have hx₂' := Finset.mem_inter.mp hx₂
  let rim : J.Walk (e r) (e r) := C.map e.toHom
  have hrim : rim.IsCycle := hC.map e.injective
  have ha_not : e a ∉ rim.support := by
    intro hea
    change e a ∈ (C.map e.toHom).support at hea
    rw [Walk.support_map] at hea
    obtain ⟨w, hwC, hwa⟩ := List.mem_map.mp hea
    exact haC (e.injective hwa ▸ hwC)
  have map_mem (x : V) (hx : x ∈ C.support) : e x ∈ rim.support := by
    change e x ∈ (C.map e.toHom).support
    rw [Walk.support_map]
    exact List.mem_map.mpr ⟨x, hx, rfl⟩
  have hax₀ : G.Adj a x₀ := by
    simpa only [SimpleGraph.mem_neighborFinset] using hx₀'.1
  have hax₁ : G.Adj a x₁ := by
    simpa only [SimpleGraph.mem_neighborFinset] using hx₁'.1
  have hax₂ : G.Adj a x₂ := by
    simpa only [SimpleGraph.mem_neighborFinset] using hx₂'.1
  exact hasWheelCenteredAt_of_cycle_three_neighbors rim hrim ha_not
    (e.toHom.map_rel hax₀) (e.toHom.map_rel hax₁)
    (e.toHom.map_rel hax₂)
    (map_mem x₀ (by simpa using hx₀'.2))
    (map_mem x₁ (by simpa using hx₁'.2))
    (map_mem x₂ (by simpa using hx₂'.2))
    (e.injective.ne hx₀x₁) (e.injective.ne hx₀x₂)
    (e.injective.ne hx₁x₂)

/-- Separation-three-connectivity implies the deletion-of-two-vertices
formulation.  This local converse to
`isThreeConnected_of_vertexThreeConnected` is used only to transport the
Menger input across a finite relabelling. -/
private theorem vertexThreeConnected_local
    (hthree : IsThreeConnected G) : VertexThreeConnected G := by
  refine ⟨hthree.four_le_card, ?_, ?_⟩
  · have hpre₀ :=
      hthree.induce_compl_preconnected (∅ : Finset V) (by simp)
    have hpre : G.Preconnected := by
      intro x y
      let x' : {w : V // w ∉ (∅ : Finset V)} := ⟨x, by simp⟩
      let y' : {w : V // w ∉ (∅ : Finset V)} := ⟨y, by simp⟩
      let inc : (G.induce fun w : V ↦ w ∉ (∅ : Finset V)) →g G :=
        (SimpleGraph.Embedding.induce
          (G := G) (s := fun w : V ↦ w ∉ (∅ : Finset V))).toHom
      exact (hpre₀ x' y').map inc
    exact {
      preconnected := hpre
      nonempty := Fintype.card_pos_iff.mp (by
        have := hthree.four_le_card
        omega) }
  · intro x y hxy
    have hpre₀ := hthree.delete_pair_preconnected hxy
    let epair : {w : V // w ∉ ({x, y} : Finset V)} ≃
        {w : V // w ≠ x ∧ w ≠ y} :=
      Equiv.setCongr (by ext q; simp)
    let gipair :
        (G.induce fun w : V ↦ w ∉ ({x, y} : Finset V)) ≃g
          (G.induce fun w : V ↦ w ≠ x ∧ w ≠ y) :=
      { toEquiv := epair
        map_rel_iff' := by intro u v; rfl }
    have hpre : (G.induce fun w : V ↦ w ≠ x ∧ w ≠ y).Preconnected :=
      gipair.preconnected_iff.mp hpre₀
    have hpairSmall : ({x, y} : Finset V).card < Fintype.card V := by
      have hle := Finset.card_insert_le x ({y} : Finset V)
      simp only [Finset.card_singleton] at hle
      have hfour := hthree.four_le_card
      omega
    obtain ⟨q, _hq, hqnot⟩ :=
      Finset.exists_mem_notMem_of_card_lt_card hpairSmall
    have hqx : q ≠ x := by
      intro h
      exact hqnot (by simp [h])
    have hqy : q ≠ y := by
      intro h
      exact hqnot (by simp [h])
    exact {
      preconnected := hpre
      nonempty := ⟨⟨q, hqx, hqy⟩⟩ }

/-- The deletion-of-two-vertices definition is invariant under a graph
isomorphism. -/
private theorem vertexThreeConnected_map_iso
    {W : Type*} [Fintype W]
    {G : SimpleGraph V} {J : SimpleGraph W}
    (e : G ≃g J) (hthree : VertexThreeConnected G) :
    VertexThreeConnected J := by
  refine ⟨?_, (SimpleGraph.Iso.connected_iff e).mp hthree.2.1, ?_⟩
  · have hcard := Fintype.card_congr e.toEquiv
    exact hcard ▸ hthree.1
  · intro x y hxy
    have hpreimage_ne : e.symm x ≠ e.symm y := e.symm.injective.ne hxy
    have hdelete := hthree.2.2 (e.symm x) (e.symm y) hpreimage_ne
    have hbij : Set.BijOn e
        {w : V | w ≠ e.symm x ∧ w ≠ e.symm y}
        {z : W | z ≠ x ∧ z ≠ y} := by
      refine ⟨?_, e.injective.injOn, ?_⟩
      · intro w hw
        constructor
        · intro hewx
          exact hw.1 (by
            apply e.injective
            simpa using hewx)
        · intro hewy
          exact hw.2 (by
            apply e.injective
            simpa using hewy)
      · intro z hz
        exact ⟨e.symm z,
          ⟨e.symm.injective.ne hz.1, e.symm.injective.ne hz.2⟩,
          e.apply_symm_apply z⟩
    let edel := e.induce hbij
    exact (SimpleGraph.Iso.connected_iff edel).mp hdelete

/-- Separation-three-connectivity is invariant under a graph isomorphism. -/
private theorem isThreeConnected_map_iso
    {W : Type*} [Fintype W]
    {G : SimpleGraph V} {J : SimpleGraph W}
    (e : G ≃g J) (hthree : IsThreeConnected G) :
    IsThreeConnected J := by
  exact ahtDoublePinReplacement.isThreeConnected_of_vertexThreeConnected
    (vertexThreeConnected_map_iso e (vertexThreeConnected_local hthree))

/-- Map a cycle of an induced subgraph back to a supergraph.  If its three
displayed vertices are distinct neighbours of the deleted vertex, the
mapped cycle is the required wheel rim. -/
private theorem hasWheelCenteredAt_of_induce_cycle_type0
    {V : Type} [Fintype V] [DecidableEq V]
    {H G : SimpleGraph V} [DecidableRel H.Adj] [DecidableRel G.Adj]
    {a : V} {x₀ x₁ x₂ : {w : V // w ≠ a}}
    (hHG : H ≤ G)
    (hcycle : HasCycleThroughThree (H.induce fun w : V ↦ w ≠ a) x₀ x₁ x₂)
    (hax₀ : G.Adj a x₀.1) (hax₁ : G.Adj a x₁.1)
    (hax₂ : G.Adj a x₂.1)
    (hx₀x₁ : x₀.1 ≠ x₁.1) (hx₀x₂ : x₀.1 ≠ x₂.1)
    (hx₁x₂ : x₁.1 ≠ x₂.1) :
    HasWheelCenteredAt G a := by
  obtain ⟨r, C, hC, hx₀C, hx₁C, hx₂C⟩ := hcycle
  let inc : (H.induce fun w : V ↦ w ≠ a) →g H :=
    (SimpleGraph.Embedding.induce (G := H) (s := fun w : V ↦ w ≠ a)).toHom
  let rimH : H.Walk r.1 r.1 := C.map inc
  let rim : G.Walk r.1 r.1 := rimH.mapLe hHG
  have hrimH : rimH.IsCycle := by
    exact hC.map Subtype.val_injective
  have hrim : rim.IsCycle := hrimH.mapLe hHG
  have hsupport : rim.support = rimH.support := by
    exact Walk.support_mapLe_eq_support hHG rimH
  have ha_not_H : a ∉ rimH.support := by
    intro ha
    change a ∈ (C.map inc).support at ha
    rw [Walk.support_map] at ha
    obtain ⟨w, _hwC, hwa⟩ := List.mem_map.mp ha
    exact w.2 (by simpa [inc] using hwa)
  have ha_not : a ∉ rim.support := by
    simpa only [hsupport] using ha_not_H
  have vertex_mem_rim (x : {w : V // w ≠ a}) (hx : x ∈ C.support) :
      x.1 ∈ rim.support := by
    have hxH : x.1 ∈ rimH.support := by
      change x.1 ∈ (C.map inc).support
      rw [Walk.support_map]
      exact List.mem_map.mpr ⟨x, hx, by simp [inc]⟩
    simpa only [hsupport] using hxH
  exact hasWheelCenteredAt_of_cycle_three_neighbors rim hrim ha_not
    hax₀ hax₁ hax₂
    (vertex_mem_rim x₀ hx₀C) (vertex_mem_rim x₁ hx₁C)
    (vertex_mem_rim x₂ hx₂C) hx₀x₁ hx₀x₂ hx₁x₂

/-- AHT Lemma 4.5 for the first endpoint, over the universe-zero finite
types required by the finite Menger theorem. -/
theorem hasWheelCenteredAt_left_of_eraseEdge_isThreeConnected_type0
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {a b : V} (hab : G.Adj a b)
    (hdel : IsThreeConnected (eraseEdge G a b)) :
    HasWheelCenteredAt G a := by
  let H := eraseEdge G a b
  have hnadj : ¬H.Adj a b := by
    simpa only [H] using
      (not_eraseEdge_adj_endpoints (G := G) (a := a) (b := b))
  obtain ⟨F⟩ := exists_threeFanToEndpoint
    (H := H) hab.ne hnadj hdel
  let K := H.induce fun w : V ↦ w ≠ a
  let n : Fin 3 → {w : V // w ≠ a} := fun i ↦
    ⟨F.neighbor i, (F.adj_neighbor i).ne.symm⟩
  let b' : {w : V // w ≠ a} := ⟨b, hab.ne.symm⟩
  have hAlt :
      HasCycleThroughThree K (n 0) (n 1) (n 2) ∨
        HasCycleThroughThree K b' (n 0) (n 1) ∨
        HasCycleThroughThree K b' (n 0) (n 2) ∨
        HasCycleThroughThree K b' (n 1) (n 2) := by
    simpa only [K, n, b'] using
      (cycleAlternative_of_threeFanToEndpoint_type0
        (H := H) hab.ne hdel F)
  have hHG : H ≤ G := by
    simpa only [H] using eraseEdge_le G a b
  have hfanAdj (i : Fin 3) : G.Adj a (n i).1 := by
    exact hHG (F.adj_neighbor i)
  have hn01 : (n 0).1 ≠ (n 1).1 := by
    simpa only [n] using F.neighbor_injective.ne (by decide : (0 : Fin 3) ≠ 1)
  have hn02 : (n 0).1 ≠ (n 2).1 := by
    simpa only [n] using F.neighbor_injective.ne (by decide : (0 : Fin 3) ≠ 2)
  have hn12 : (n 1).1 ≠ (n 2).1 := by
    simpa only [n] using F.neighbor_injective.ne (by decide : (1 : Fin 3) ≠ 2)
  have hb0 : b ≠ (n 0).1 := by
    simpa only [n] using (F.neighbor_ne_endpoint 0).symm
  have hb1 : b ≠ (n 1).1 := by
    simpa only [n] using (F.neighbor_ne_endpoint 1).symm
  have hb2 : b ≠ (n 2).1 := by
    simpa only [n] using (F.neighbor_ne_endpoint 2).symm
  rcases hAlt with h012 | hb01 | hb02 | hb12
  · exact hasWheelCenteredAt_of_induce_cycle_type0
      (H := H) hHG h012 (hfanAdj 0) (hfanAdj 1) (hfanAdj 2)
      hn01 hn02 hn12
  · exact hasWheelCenteredAt_of_induce_cycle_type0
      (H := H) hHG hb01 hab (hfanAdj 0) (hfanAdj 1)
      hb0 hb1 hn01
  · exact hasWheelCenteredAt_of_induce_cycle_type0
      (H := H) hHG hb02 hab (hfanAdj 0) (hfanAdj 2)
      hb0 hb2 hn02
  · exact hasWheelCenteredAt_of_induce_cycle_type0
      (H := H) hHG hb12 hab (hfanAdj 1) (hfanAdj 2)
      hb1 hb2 hn12

/-- Exact universe-zero form of AHT Lemma 4.5: both endpoints of a
nonessential edge in a three-connected graph are wheel centres. -/
theorem wheelCenters_endpoints_of_eraseEdge_isThreeConnected_type0
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {a b : V} (hab : G.Adj a b)
    (hdel : IsThreeConnected (eraseEdge G a b)) :
    HasWheelCenteredAt G a ∧ HasWheelCenteredAt G b := by
  refine ⟨hasWheelCenteredAt_left_of_eraseEdge_isThreeConnected_type0
    hab hdel, ?_⟩
  apply hasWheelCenteredAt_left_of_eraseEdge_isThreeConnected_type0 hab.symm
  rw [eraseEdge_comm G b a]
  exact hdel

/-- In an almost-wheel-free graph every actual wheel centre has degree
exactly three.  This is the definition-level fact used in Corollary 4.6. -/
theorem degree_eq_three_of_almostWheelFree_of_center
    (halmost : AlmostWheelFree G) {a : V}
    (ha : HasWheelCenteredAt G a) : G.degree a = 3 := by
  rcases halmost with hnone | hone | htwo
  · exact (hnone a ha).elim
  · obtain ⟨c, hcdeg, hc⟩ := hone
    exact (hc a ha) ▸ hcdeg
  · obtain ⟨c, d, _hcd, hcdeg, hddeg, hcenters⟩ := htwo
    rcases hcenters a ha with rfl | rfl
    · exact hcdeg
    · exact hddeg

/-- Universe-zero form of AHT Corollary 4.6. -/
theorem isEdgeMinimallyThreeConnected_of_isThreeConnected_of_almostWheelFree_type0
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hthree : IsThreeConnected G) (halmost : AlmostWheelFree G) :
    IsEdgeMinimallyThreeConnected G := by
  refine ⟨hthree, ?_⟩
  intro a b hab hdel
  have hcenter : HasWheelCenteredAt G a :=
    (wheelCenters_endpoints_of_eraseEdge_isThreeConnected_type0 hab hdel).1
  have hdegree : G.degree a = 3 :=
    degree_eq_three_of_almostWheelFree_of_center halmost hcenter
  have hfour : 4 ≤ G.degree a :=
    (four_le_degree_endpoints_of_eraseEdge_isThreeConnected hab hdel).1
  omega

/-- AHT Lemma 4.5 in the repository's universe-polymorphic finite-graph
API.  Relabel the deleted graph by `Fin (card V)`, apply the universe-zero
Menger proof, and transport both wheel centres back. -/
theorem wheelCenters_endpoints_of_eraseEdge_isThreeConnected
    {a b : V} (hab : G.Adj a b)
    (hdel : IsThreeConnected (eraseEdge G a b)) :
    HasWheelCenteredAt G a ∧ HasWheelCenteredAt G b := by
  classical
  letI : DecidableEq (Fin (Fintype.card V)) := fun x y ↦
    Classical.propDecidable (x = y)
  let e : V ≃ Fin (Fintype.card V) := Fintype.equivFin V
  let J : SimpleGraph (Fin (Fintype.card V)) := G.map e
  let φ : G ≃g J := SimpleGraph.Iso.map e G
  let φdel : eraseEdge G a b ≃g eraseEdge J (e a) (e b) :=
    { toEquiv := e
      map_rel_iff' := by
        intro x y
        simp only [eraseEdge_adj]
        change
          ((G.map e).Adj (e x) (e y) ∧
              ¬((e x = e a ∧ e y = e b) ∨
                (e x = e b ∧ e y = e a))) ↔
            G.Adj x y ∧
              ¬((x = a ∧ y = b) ∨ (x = b ∧ y = a))
        have hadj : (G.map e).Adj (e x) (e y) ↔ G.Adj x y := by
          exact (SimpleGraph.Iso.map e G).map_adj_iff
        rw [hadj]
        simp only [e.injective.eq_iff] }
  have hdelJ := isThreeConnected_map_iso φdel hdel
  have habJ : J.Adj (e a) (e b) := φ.toHom.map_rel hab
  have hcentersJ :=
    wheelCenters_endpoints_of_eraseEdge_isThreeConnected_type0 habJ hdelJ
  have ha : HasWheelCenteredAt G (φ.symm (e a)) :=
    hasWheelCenteredAt_map_iso φ.symm hcentersJ.1
  have hb : HasWheelCenteredAt G (φ.symm (e b)) :=
    hasWheelCenteredAt_map_iso φ.symm hcentersJ.2
  have hφa : φ.symm (e a) = a := by
    change e.symm (e a) = a
    exact e.symm_apply_apply a
  have hφb : φ.symm (e b) = b := by
    change e.symm (e b) = b
    exact e.symm_apply_apply b
  exact ⟨by simpa only [hφa] using ha, by simpa only [hφb] using hb⟩

/-- AHT Corollary 4.6: a three-connected almost-wheel-free graph is
edge-minimally three-connected. -/
theorem isEdgeMinimallyThreeConnected_of_isThreeConnected_of_almostWheelFree
    (hthree : IsThreeConnected G) (halmost : AlmostWheelFree G) :
    IsEdgeMinimallyThreeConnected G := by
  refine ⟨hthree, ?_⟩
  intro a b hab hdel
  have hcenter : HasWheelCenteredAt G a :=
    (wheelCenters_endpoints_of_eraseEdge_isThreeConnected hab hdel).1
  have hdegree : G.degree a = 3 :=
    degree_eq_three_of_almostWheelFree_of_center halmost hcenter
  have hfour : 4 ≤ G.degree a :=
    (four_le_degree_endpoints_of_eraseEdge_isThreeConnected hab hdel).1
  omega

/-- The exact cycle certificate produced in the last paragraph of the proof
of AHT Lemma 4.5 for the endpoint `a` of the deleted edge `ab`.

The two vertices `x,y` are distinct surviving neighbours of `a`; the rim is
a cycle of the deleted-edge graph, avoids `a`, and contains `b,x,y`. -/
structure EndpointCycleCertificate (G : SimpleGraph V) (a b : V) where
  x : V
  y : V
  root : V
  rim : (eraseEdge G a b).Walk root root
  isCycle : rim.IsCycle
  center_not_mem : a ∉ rim.support
  adj_x : (eraseEdge G a b).Adj a x
  adj_y : (eraseEdge G a b).Adj a y
  x_ne_y : x ≠ y
  endpoint_mem : b ∈ rim.support
  x_mem : x ∈ rim.support
  y_mem : y ∈ rim.support

/-- AHT Lemma 4.5 after its sole path/fan construction: the endpoint-cycle
certificate gives a wheel centred at the endpoint of the deleted edge. -/
theorem hasWheelCenteredAt_of_endpointCycleCertificate
    {a b : V} (hab : G.Adj a b)
    (C : EndpointCycleCertificate G a b) :
    HasWheelCenteredAt G a := by
  let rim : G.Walk C.root C.root := C.rim.mapLe (eraseEdge_le_local G a b)
  have hrim : rim.IsCycle := C.isCycle.mapLe (eraseEdge_le_local G a b)
  have hsupport : rim.support = C.rim.support := by
    exact Walk.support_mapLe_eq_support (eraseEdge_le_local G a b) C.rim
  have ha_not : a ∉ rim.support := by
    simpa only [hsupport] using C.center_not_mem
  refine ⟨C.root, rim, hrim, ha_not, ?_⟩
  have hax : G.Adj a C.x := (eraseEdge_le_local G a b) C.adj_x
  have hay : G.Adj a C.y := (eraseEdge_le_local G a b) C.adj_y
  have hbx : b ≠ C.x := by
    intro h
    apply not_eraseEdge_adj_endpoints (G := G) (a := a) (b := b)
    simpa [h] using C.adj_x
  have hby : b ≠ C.y := by
    intro h
    apply not_eraseEdge_adj_endpoints (G := G) (a := a) (b := b)
    simpa [h] using C.adj_y
  have hbmem : b ∈ G.neighborFinset a ∩ rim.support.toFinset := by
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
      List.mem_toFinset]
    exact ⟨hab, by simpa only [hsupport] using C.endpoint_mem⟩
  have hxmem : C.x ∈ G.neighborFinset a ∩ rim.support.toFinset := by
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
      List.mem_toFinset]
    exact ⟨hax, by simpa only [hsupport] using C.x_mem⟩
  have hymem : C.y ∈ G.neighborFinset a ∩ rim.support.toFinset := by
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
      List.mem_toFinset]
    exact ⟨hay, by simpa only [hsupport] using C.y_mem⟩
  have hthree := Finset.two_lt_card_iff.mpr
    ⟨b, C.x, C.y, hbmem, hxmem, hymem, hbx, hby, C.x_ne_y⟩
  omega

/-- The symmetric certificate output gives exactly the two wheel centres in
AHT Lemma 4.5.  The still-missing Menger/fan step is precisely the
construction of the two certificate arguments from three-connectivity of the
deleted-edge graph. -/
theorem wheelCenters_endpoints_of_endpointCycleCertificates
    {a b : V} (hab : G.Adj a b)
    (Ca : EndpointCycleCertificate G a b)
    (Cb : EndpointCycleCertificate G b a) :
    HasWheelCenteredAt G a ∧ HasWheelCenteredAt G b := by
  exact ⟨hasWheelCenteredAt_of_endpointCycleCertificate hab Ca,
    hasWheelCenteredAt_of_endpointCycleCertificate hab.symm Cb⟩

/-- The complete definition-level and degree-count part of AHT Corollary
4.6.  Once the source's endpoint-cycle certificate has been constructed,
deleting that edge cannot preserve three-connectivity in an
almost-wheel-free graph. -/
theorem eraseEdge_not_isThreeConnected_of_endpointCycleCertificate
    (halmost : AlmostWheelFree G) {a b : V} (hab : G.Adj a b)
    (C : EndpointCycleCertificate G a b) :
    ¬IsThreeConnected (eraseEdge G a b) := by
  intro hdel
  have hcenter : HasWheelCenteredAt G a :=
    hasWheelCenteredAt_of_endpointCycleCertificate hab C
  have hdegree : G.degree a = 3 :=
    degree_eq_three_of_almostWheelFree_of_center halmost hcenter
  have hfour : 4 ≤ G.degree a :=
    (four_le_degree_endpoints_of_eraseEdge_isThreeConnected hab hdel).1
  omega

end AHTMinimalThreeConnected

end Erdos916
