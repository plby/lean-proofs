/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos916.AHTSourceLemma

/-!
# The double-pin replacement in AHT Lemma 6.4

In Lemma 6.4 of Aboulker--Havet--Trotignon, a three-boundary fragment is
first replaced by a torso with three distinguished pins `a'`, `b'`, `c'`.
The final, source-exact operation adjoins two vertices `d,d'`, both adjacent
to precisely those three pins.  The authors use this deliberately introduced
pair as one of the two disjoint twin pairs in their minimal-counterexample
argument.

The first part isolates the unconditional double-pin operation.  The second
part defines the source-exact three-fragment, including the optional fresh
pins, and develops the fragment-side connectivity and wheel-centre
bookkeeping used in the proof of Lemma 6.4.
-/

namespace Erdos916

open SimpleGraph

universe u

/-- A centred wheel transports along an injective graph homomorphism, with
its centre transported by the same map. -/
theorem HasWheelCenteredAt.mapHomOfInjective
    {X Y : Type u} [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y]
    {K : SimpleGraph X} [DecidableRel K.Adj]
    {L : SimpleGraph Y} [DecidableRel L.Adj]
    (f : K →g L) (hf : Function.Injective f) {x : X}
    (h : HasWheelCenteredAt K x) : HasWheelCenteredAt L (f x) := by
  obtain ⟨a, p, hp, hxp, hthree⟩ := h
  let q : L.Walk (f a) (f a) := p.map f
  have hq : q.IsCycle := hp.map hf
  have hxq : f x ∉ q.support := by
    intro hx
    simp only [q, SimpleGraph.Walk.support_map] at hx
    obtain ⟨y, hyp, hyx⟩ := List.mem_map.mp hx
    exact hxp (hf hyx ▸ hyp)
  refine ⟨f a, q, hq, hxq, ?_⟩
  have htwo : 2 < (K.neighborFinset x ∩ p.support.toFinset).card := by
    omega
  obtain ⟨y₁, y₂, y₃, hy₁, hy₂, hy₃, hy₁₂, hy₁₃, hy₂₃⟩ :=
    Finset.two_lt_card_iff.mp htwo
  have map_mem (y : X)
      (hy : y ∈ K.neighborFinset x ∩ p.support.toFinset) :
      f y ∈ L.neighborFinset (f x) ∩ q.support.toFinset := by
    rw [Finset.mem_inter] at hy ⊢
    constructor
    · rw [SimpleGraph.mem_neighborFinset] at hy ⊢
      exact f.map_adj hy.1
    · rw [List.mem_toFinset] at hy ⊢
      simp only [q, SimpleGraph.Walk.support_map]
      exact List.mem_map.mpr ⟨y, hy.2, rfl⟩
  have hcard :
      2 < (L.neighborFinset (f x) ∩ q.support.toFinset).card := by
    apply Finset.two_lt_card_iff.mpr
    exact ⟨f y₁, f y₂, f y₃, map_mem y₁ hy₁, map_mem y₂ hy₂,
      map_mem y₃ hy₃, hf.ne hy₁₂, hf.ne hy₁₃, hf.ne hy₂₃⟩
  omega

/-- A degree-one vertex cannot lie on a cycle. -/
theorem not_mem_cycle_support_of_degree_eq_one
    {X : Type u} [Fintype X] [DecidableEq X]
    {K : SimpleGraph X} [DecidableRel K.Adj]
    {r : X} (hr : K.degree r = 1)
    {a : X} {p : K.Walk a a} (hp : p.IsCycle) :
    r ∉ p.support := by
  intro hrp
  have hncard := hp.ncard_neighborSet_toSubgraph_eq_two hrp
  have hlarge : 1 < (p.toSubgraph.neighborSet r).ncard := by omega
  obtain ⟨y, hy, z, hz, hyz⟩ :=
    Set.one_lt_ncard_iff_nontrivial.mp hlarge
  have hyK : y ∈ K.neighborFinset r := by
    rw [SimpleGraph.mem_neighborFinset]
    exact hy.adj_sub
  have hzK : z ∈ K.neighborFinset r := by
    rw [SimpleGraph.mem_neighborFinset]
    exact hz.adj_sub
  have hcard : 1 < (K.neighborFinset r).card :=
    Finset.one_lt_card.mpr ⟨y, hyK, z, hzK, hyz⟩
  rw [K.card_neighborFinset_eq_degree, hr] at hcard
  omega

/-- A degree-one vertex on a simple path is one of its endpoints. -/
theorem eq_start_or_eq_end_of_mem_path_of_degree_eq_one
    {X : Type u} [Fintype X] [DecidableEq X]
    {K : SimpleGraph X} [DecidableRel K.Adj]
    {s t r : X} {p : K.Walk s t} (hp : p.IsPath)
    (hr : K.degree r = 1) (hrp : r ∈ p.support) : r = s ∨ r = t := by
  obtain ⟨n, hnr, hnle⟩ :=
    SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hrp
  by_cases hn0 : n = 0
  · left
    subst n
    simpa using hnr.symm
  by_cases hnlast : n = p.length
  · right
    rw [hnlast, SimpleGraph.Walk.getVert_length] at hnr
    exact hnr.symm
  have hnlt : n < p.length := lt_of_le_of_ne hnle hnlast
  have hncard := hp.ncard_neighborSet_toSubgraph_internal_eq_two hn0 hnlt
  rw [hnr] at hncard
  have hlarge : 1 < (p.toSubgraph.neighborSet r).ncard := by omega
  obtain ⟨y, hy, z, hz, hyz⟩ :=
    Set.one_lt_ncard_iff_nontrivial.mp hlarge
  have hyK : y ∈ K.neighborFinset r := by
    rw [SimpleGraph.mem_neighborFinset]
    exact hy.adj_sub
  have hzK : z ∈ K.neighborFinset r := by
    rw [SimpleGraph.mem_neighborFinset]
    exact hz.adj_sub
  have hcard : 1 < (K.neighborFinset r).card :=
    Finset.one_lt_card.mpr ⟨y, hyK, z, hzK, hyz⟩
  rw [K.card_neighborFinset_eq_degree, hr] at hcard
  omega

/-- Two simple paths with the same distinct ends and no other common vertex
form a simple cycle when the first path has a displayed internal vertex. -/
theorem SimpleGraph.Walk.IsPath.isCycle_append_reverse_of_meet_only_ends_local
    {X : Type u} {K : SimpleGraph X} {s t w : X}
    {p q : K.Walk s t} (hp : p.IsPath) (hq : q.IsPath)
    (hw : w ∈ p.support) (hws : w ≠ s) (hwt : w ≠ t)
    (hmeet : ∀ a, a ∈ p.support → a ∈ q.support → a = s ∨ a = t) :
    (p.append q.reverse).IsCycle := by
  apply hp.isCycle_append hq.reverse
  · rw [List.disjoint_left]
    intro a hap haqr
    have hap' : a ∈ p.support := List.mem_of_mem_tail hap
    have haq' : a ∈ q.support := by
      have : a ∈ q.reverse.support := List.mem_of_mem_tail haqr
      simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using this
    rcases hmeet a hap' haq' with rfl | rfl
    · have hnd := hp.support_nodup
      rw [← p.cons_tail_support] at hnd
      exact (List.nodup_cons.mp hnd).1 hap
    · have hnd := hq.reverse.support_nodup
      rw [← q.reverse.cons_tail_support] at hnd
      exact (List.nodup_cons.mp hnd).1 haqr
  · left
    by_contra hlen
    have hle : p.length ≤ 1 := by omega
    have hends : p.support = [s, t] ∨ s = t := by
      cases p with
      | nil => exact Or.inr rfl
      | @cons _ a _ hadj r =>
          cases r with
          | nil => simp
          | @cons _ b _ hab r => simp at hle
    rcases hends with hsupp | hst
    · have hwst : w = s ∨ w = t := by simpa [hsupp] using hw
      exact hwst.elim hws hwt
    · subst t
      have hpnil : p = .nil := SimpleGraph.Walk.isPath_iff_eq_nil.mp hp
      subst p
      exact hws (by simpa using hw)


/-- AHT's final fragment-replacement operation: keep the old graph on the
left summand and add two independent vertices, each joined to the same three
old pins. -/
def ahtDoublePinReplacement {V : Type u} (H : SimpleGraph V)
    (a b c : V) : SimpleGraph (V ⊕ Fin 2) where
  Adj x y :=
    match x, y with
    | .inl p, .inl q => H.Adj p q
    | .inl p, .inr _ => p = a ∨ p = b ∨ p = c
    | .inr _, .inl q => q = a ∨ q = b ∨ q = c
    | .inr _, .inr _ => False
  symm.symm := by
    intro x y h
    rcases x with p | i <;> rcases y with q | j
    · exact H.symm.symm p q h
    · exact h
    · exact h
    · exact h
  loopless.irrefl := by
    intro x h
    rcases x with p | i
    · exact H.loopless.irrefl p h
    · exact h

/-- The replacement graph has decidable adjacency whenever the old torso
does. -/
instance ahtDoublePinReplacement.instDecidableRel {V : Type u}
    [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (a b c : V) : DecidableRel (ahtDoublePinReplacement H a b c).Adj := by
  intro x y
  rcases x with p | i <;> rcases y with q | j
  · change Decidable (H.Adj p q)
    exact inferInstance
  · change Decidable (p = a ∨ p = b ∨ p = c)
    exact inferInstance
  · change Decidable (q = a ∨ q = b ∨ q = c)
    exact inferInstance
  · exact isFalse id

namespace ahtDoublePinReplacement

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {H : SimpleGraph V} [DecidableRel H.Adj]
variable {a b c : V}

/-- Inclusion of an old torso vertex into the replacement graph. -/
def oldVertexEmbedding : V ↪ V ⊕ Fin 2 := Function.Embedding.inl

@[simp]
theorem adj_old_old_iff {p q : V} :
    (ahtDoublePinReplacement H a b c).Adj (.inl p) (.inl q) ↔
      H.Adj p q := by
  rfl

@[simp]
theorem adj_old_new_iff {p : V} {i : Fin 2} :
    (ahtDoublePinReplacement H a b c).Adj (.inl p) (.inr i) ↔
      p = a ∨ p = b ∨ p = c := by
  rfl

@[simp]
theorem adj_new_old_iff {i : Fin 2} {p : V} :
    (ahtDoublePinReplacement H a b c).Adj (.inr i) (.inl p) ↔
      p = a ∨ p = b ∨ p = c := by
  rfl

@[simp]
theorem not_adj_new_new (i j : Fin 2) :
    ¬(ahtDoublePinReplacement H a b c).Adj (.inr i) (.inr j) := by
  exact id

/-- Each new vertex has exactly the three old pins as its open
neighbourhood. -/
theorem neighborSet_new (i : Fin 2) :
    (ahtDoublePinReplacement H a b c).neighborSet (.inr i) =
      {(.inl a : V ⊕ Fin 2), .inl b, .inl c} := by
  ext x
  rcases x with p | j
  · simp only [SimpleGraph.mem_neighborSet, adj_new_old_iff,
      Set.mem_insert_iff, Set.mem_singleton_iff, Sum.inl.injEq]
  · simp only [SimpleGraph.mem_neighborSet, not_adj_new_new,
      Set.mem_insert_iff, Set.mem_singleton_iff, Sum.inr.injEq,
      Sum.inr_ne_inl, or_self, or_false]

/-- Finite form of the exact new-vertex neighbourhood. -/
theorem neighborFinset_new (i : Fin 2) :
    (ahtDoublePinReplacement H a b c).neighborFinset (.inr i) =
      {(.inl a : V ⊕ Fin 2), .inl b, .inl c} := by
  ext x
  rw [SimpleGraph.mem_neighborFinset]
  rw [← SimpleGraph.mem_neighborSet]
  rw [neighborSet_new (H := H) (a := a) (b := b) (c := c) i]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff,
    Finset.mem_insert, Finset.mem_singleton]

/-- The two vertices adjoined in AHT Lemma 6.4 are false twins. -/
theorem new_vertices_areFalseTwins :
    AreFalseTwins (ahtDoublePinReplacement H a b c)
      (.inr 0) (.inr 1) := by
  refine ⟨?_, ?_⟩
  · intro h
    have h01 : (0 : Fin 2) = 1 := Sum.inr.inj h
    exact (by decide : (0 : Fin 2) ≠ 1) h01
  exact (neighborSet_new (H := H) (a := a) (b := b) (c := c) 0).trans
    (neighborSet_new (H := H) (a := a) (b := b) (c := c) 1).symm

/-- When the three pins are distinct, both deliberately adjoined false twins
have degree three, exactly as required in AHT's two-pair conclusion. -/
theorem degree_new (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (i : Fin 2) :
    (ahtDoublePinReplacement H a b c).degree (.inr i) = 3 := by
  classical
  rw [← (ahtDoublePinReplacement H a b c).card_neighborFinset_eq_degree]
  rw [neighborFinset_new]
  simp [hab, hac, hbc]

/-- The sacrificial new pair is disjoint from every pair of old torso
vertices. -/
theorem new_pair_disjoint_old_pair (p q : V) :
    Disjoint ({(.inr 0 : V ⊕ Fin 2), .inr 1} : Finset (V ⊕ Fin 2))
      {(.inl p : V ⊕ Fin 2), .inl q} := by
  simp [Finset.disjoint_left]

/-- Every designated pin gains precisely the two new vertices as neighbours;
all of its old torso neighbours are retained. -/
theorem neighborFinset_old_pin {p : V}
    (hp : p = a ∨ p = b ∨ p = c) :
    (ahtDoublePinReplacement H a b c).neighborFinset (.inl p) =
      (H.neighborFinset p).map oldVertexEmbedding ∪
        {(.inr 0 : V ⊕ Fin 2), .inr 1} := by
  ext x
  rcases x with q | i
  · simp [SimpleGraph.mem_neighborFinset, oldVertexEmbedding]
  · fin_cases i <;>
      simp [SimpleGraph.mem_neighborFinset, oldVertexEmbedding, hp]

/-- Degree bookkeeping for a pin in the AHT replacement. -/
theorem degree_old_pin {p : V} (hp : p = a ∨ p = b ∨ p = c) :
    (ahtDoublePinReplacement H a b c).degree (.inl p) = H.degree p + 2 := by
  rw [← (ahtDoublePinReplacement H a b c).card_neighborFinset_eq_degree,
    neighborFinset_old_pin hp]
  have hd : Disjoint
      ((H.neighborFinset p).map oldVertexEmbedding)
      ({(.inr 0 : V ⊕ Fin 2), .inr 1} : Finset (V ⊕ Fin 2)) := by
    simp [Finset.disjoint_left, oldVertexEmbedding]
  rw [Finset.card_union_of_disjoint hd, Finset.card_map,
    H.card_neighborFinset_eq_degree]
  simp

/-- In the prepared torso of Lemma 6.4 every pin has degree one.  The
double-pin operation therefore makes it degree three. -/
theorem degree_old_pin_eq_three {p : V}
    (hp : p = a ∨ p = b ∨ p = c) (hdeg : H.degree p = 1) :
    (ahtDoublePinReplacement H a b c).degree (.inl p) = 3 := by
  rw [degree_old_pin hp, hdeg]

/-- An old vertex which is not one of the three pins acquires no neighbour
in the double-pin step.  This is the degree comparison used for the only
possible wheel centres left after the gadget vertices have been excluded. -/
theorem neighborFinset_old_nonpin {p : V}
    (hpa : p ≠ a) (hpb : p ≠ b) (hpc : p ≠ c) :
    (ahtDoublePinReplacement H a b c).neighborFinset (.inl p) =
      (H.neighborFinset p).map oldVertexEmbedding := by
  ext x
  rcases x with q | i
  · simp [SimpleGraph.mem_neighborFinset, oldVertexEmbedding]
  · simp [SimpleGraph.mem_neighborFinset, oldVertexEmbedding, hpa, hpb, hpc]

/-- Consequently the double-pin step preserves the degree of every old
non-pin vertex. -/
theorem degree_old_nonpin {p : V}
    (hpa : p ≠ a) (hpb : p ≠ b) (hpc : p ≠ c) :
    (ahtDoublePinReplacement H a b c).degree (.inl p) = H.degree p := by
  rw [← (ahtDoublePinReplacement H a b c).card_neighborFinset_eq_degree,
    neighborFinset_old_nonpin hpa hpb hpc, Finset.card_map,
    H.card_neighborFinset_eq_degree]

/-- The canonical inclusion of the old graph into its double-pin
replacement. -/
def oldGraphHom : H →g ahtDoublePinReplacement H a b c where
  toFun := Sum.inl
  map_rel' := by intro p q hpq; exact hpq

@[simp] theorem oldGraphHom_apply (p : V) :
    oldGraphHom (H := H) (a := a) (b := b) (c := c) p = .inl p := rfl

theorem oldGraphHom_injective :
    Function.Injective (oldGraphHom (H := H) (a := a) (b := b) (c := c)) :=
  Sum.inl_injective

/-- A replacement walk all of whose vertices are old is the image of an old
walk.  This is the contraction-free branch of the wheel transfer in AHT
Lemma 6.4. -/
theorem exists_oldWalk_of_support_avoids_new {p q : V}
    (w : (ahtDoublePinReplacement H a b c).Walk (.inl p) (.inl q))
    (hold : ∀ z ∈ w.support, ∃ r : V, z = .inl r) :
    ∃ r : H.Walk p q,
      r.map (oldGraphHom (H := H) (a := a) (b := b) (c := c)) = w := by
  let rec lower (n : ℕ) {s t : V}
      (v : (ahtDoublePinReplacement H a b c).Walk (.inl s) (.inl t))
      (hlen : v.length ≤ n)
      (hv : ∀ z ∈ v.support, ∃ r : V, z = .inl r) :
      ∃ r : H.Walk s t,
        r.map (oldGraphHom (H := H) (a := a) (b := b) (c := c)) = v := by
    cases n with
    | zero =>
      cases v with
      | nil => exact ⟨.nil, rfl⟩
      | cons huz tail => simp at hlen
    | succ n =>
      cases v with
      | nil => exact ⟨.nil, rfl⟩
      | @cons _ z _ huz tail =>
        obtain ⟨m, hm⟩ := hv z (by simp)
        subst z
        have huzH : H.Adj s m := huz
        have htail : ∀ y ∈ tail.support, ∃ r : V, y = .inl r := by
          intro y hy
          exact hv y (by simp [hy])
        have htailLen : tail.length ≤ n := by
          simp only [SimpleGraph.Walk.length_cons] at hlen
          omega
        obtain ⟨r, hr⟩ := lower n tail htailLen htail
        refine ⟨r.cons huzH, ?_⟩
        simp [hr]
  termination_by n
  decreasing_by omega
  exact lower w.length w le_rfl hold

/-- Cut a simple replacement rim at one of the two artificial vertices.
What remains is a simple path between two distinct pins, and together with
the cut vertex this path contains the entire rim support.  The other
artificial vertex is allowed to occur on the path; this is intentional, as
it is the first of the two cases in the rim analysis of AHT Lemma 6.4. -/
theorem exists_pinPath_around_new
    {r : V ⊕ Fin 2}
    (rim : (ahtDoublePinReplacement H a b c).Walk r r)
    (hcycle : rim.IsCycle) (i : Fin 2)
    (hi : (.inr i : V ⊕ Fin 2) ∈ rim.support) :
    ∃ y z : V,
      (y = a ∨ y = b ∨ y = c) ∧
      (z = a ∨ z = b ∨ z = c) ∧ y ≠ z ∧
      ∃ p : (ahtDoublePinReplacement H a b c).Walk (.inl y) (.inl z),
        p.IsPath ∧
        (.inr i : V ⊕ Fin 2) ∉ p.support ∧
        (∀ w ∈ p.support, w ∈ rim.support) ∧
        ∀ w ∈ rim.support, w = .inr i ∨ w ∈ p.support := by
  let cr := rim.rotate (.inr i) hi
  have hcr : cr.IsCycle := hcycle.rotate hi
  have htail : ¬cr.tail.Nil := by
    apply SimpleGraph.Walk.not_nil_iff_lt_length.mpr
    have hlen : 3 ≤ cr.length := hcr.three_le_length
    simp only [SimpleGraph.Walk.length_tail]
    omega
  let p₀ := cr.tail.dropLast
  have hp₀ : p₀.IsPath := hcr.isPath_tail.dropLast
  have hinew : (.inr i : V ⊕ Fin 2) ∉ p₀.support := by
    have hnodup := hcr.isPath_tail.support_nodup
    have hs := cr.tail.support_dropLast_concat htail
    dsimp only [p₀]
    rw [← hs] at hnodup
    exact fun h ↦ hnodup.disjoint h (by simp)
  have hsndAdj :
      (ahtDoublePinReplacement H a b c).Adj (.inr i) cr.snd :=
    cr.adj_snd hcr.not_nil
  obtain ⟨y, hyPin, hy⟩ : ∃ y : V,
      (y = a ∨ y = b ∨ y = c) ∧ cr.snd = .inl y := by
    cases hsnd : cr.snd with
    | inl y =>
        refine ⟨y, ?_, rfl⟩
        exact (adj_new_old_iff (H := H) (a := a) (b := b) (c := c)).mp
          (by simpa only [hsnd] using hsndAdj)
    | inr j =>
        have hij :
            (ahtDoublePinReplacement H a b c).Adj (.inr i) (.inr j) := by
          simpa only [hsnd] using hsndAdj
        exact (not_adj_new_new (H := H) (a := a) (b := b) (c := c) i j hij).elim
  have hlastAdj :
      (ahtDoublePinReplacement H a b c).Adj cr.tail.penultimate (.inr i) :=
    cr.tail.adj_penultimate htail
  obtain ⟨z, hzPin, hz⟩ : ∃ z : V,
      (z = a ∨ z = b ∨ z = c) ∧ cr.tail.penultimate = .inl z := by
    cases hlast : cr.tail.penultimate with
    | inl z =>
        refine ⟨z, ?_, rfl⟩
        exact (adj_old_new_iff (H := H) (a := a) (b := b) (c := c)).mp
          (by simpa only [hlast] using hlastAdj)
    | inr j =>
        have hji :
            (ahtDoublePinReplacement H a b c).Adj (.inr j) (.inr i) := by
          simpa only [hlast] using hlastAdj
        exact (not_adj_new_new (H := H) (a := a) (b := b) (c := c) j i hji).elim
  have hpen : cr.penultimate = cr.tail.penultimate := by
    calc
      cr.penultimate =
          (cr.tail.cons (cr.adj_snd hcr.not_nil)).penultimate := by
            rw [cr.cons_tail_eq hcr.not_nil]
      _ = cr.tail.penultimate :=
        SimpleGraph.Walk.penultimate_cons_of_not_nil _ _ htail
  have hyz : y ≠ z := by
    intro hyz
    subst z
    apply hcr.snd_ne_penultimate
    exact hy.trans (hz.symm.trans hpen.symm)
  let p : (ahtDoublePinReplacement H a b c).Walk (.inl y) (.inl z) :=
    p₀.copy hy hz
  have hp : p.IsPath := (SimpleGraph.Walk.isPath_copy p₀ hy hz).2 hp₀
  have hip : (.inr i : V ⊕ Fin 2) ∉ p.support := by
    simpa only [p, SimpleGraph.Walk.support_copy] using hinew
  have hpSub : ∀ w ∈ p.support, w ∈ rim.support := by
    intro w hwp
    have hwp₀ : w ∈ p₀.support := by
      simpa only [p, SimpleGraph.Walk.support_copy] using hwp
    have hwtail : w ∈ cr.tail.support := by
      rw [← cr.tail.support_dropLast_concat htail, List.mem_append]
      exact Or.inl hwp₀
    have hwcr : w ∈ cr.support := by
      rw [← cr.cons_support_tail hcr.not_nil]
      exact List.mem_cons_of_mem _ hwtail
    exact (rim.mem_support_rotate_iff (.inr i) hi).1 hwcr
  refine ⟨y, z, hyPin, hzPin, hyz, p, hp, hip, hpSub, ?_⟩
  intro w hw
  have hwcr : w ∈ cr.support := by
    exact (rim.mem_support_rotate_iff (.inr i) hi).2 hw
  have hwhead : w = .inr i ∨ w ∈ cr.tail.support := by
    have : w ∈ (.inr i : V ⊕ Fin 2) :: cr.tail.support := by
      rw [cr.cons_support_tail hcr.not_nil]
      exact hwcr
    simpa only [List.mem_cons] using this
  rcases hwhead with hwnew | hwtail
  · exact Or.inl hwnew
  · have hs := cr.tail.support_dropLast_concat htail
    rw [← hs, List.mem_append] at hwtail
    rcases hwtail with hwp₀ | hwlast
    · right
      simpa only [p, SimpleGraph.Walk.support_copy] using hwp₀
    · left
      simpa only [List.mem_singleton] using hwlast

/-- If a simple replacement rim contains exactly one of the artificial
vertices, deleting its two incident rim edges leaves a simple path in the
old graph between two distinct pins.  The support comparison is exact on
old vertices. -/
theorem exists_old_pinPath_of_cycle_contains_exactly_one_new
    {r : V ⊕ Fin 2}
    (rim : (ahtDoublePinReplacement H a b c).Walk r r)
    (hcycle : rim.IsCycle) (i j : Fin 2)
    (hij : i ≠ j) (hcover : ∀ k : Fin 2, k = i ∨ k = j)
    (hi : (.inr i : V ⊕ Fin 2) ∈ rim.support)
    (hj : (.inr j : V ⊕ Fin 2) ∉ rim.support) :
    ∃ y z : V,
      (y = a ∨ y = b ∨ y = c) ∧
      (z = a ∨ z = b ∨ z = c) ∧ y ≠ z ∧
      ∃ p : H.Walk y z, p.IsPath ∧
        ∀ w : V, w ∈ p.support ↔ (.inl w : V ⊕ Fin 2) ∈ rim.support := by
  obtain ⟨y, z, hyPin, hzPin, hyz, q, hq, hiq, hqSub, hrim⟩ :=
    exists_pinPath_around_new rim hcycle i hi
  have hold : ∀ w ∈ q.support, ∃ x : V, w = .inl x := by
    intro w hw
    rcases w with x | k
    · exact ⟨x, rfl⟩
    · rcases hcover k with rfl | rfl
      · exact (hiq hw).elim
      · exact (hj (hqSub _ hw)).elim
  obtain ⟨p, hpMap⟩ := exists_oldWalk_of_support_avoids_new q hold
  have hp : p.IsPath := by
    apply SimpleGraph.Walk.IsPath.of_map
    rw [hpMap]
    exact hq
  have hpMapSupport :
      p.support.map (Sum.inl : V → V ⊕ Fin 2) = q.support := by
    calc
      _ = p.support.map
          (oldGraphHom (H := H) (a := a) (b := b) (c := c)) := by
            apply List.map_congr_left
            intro x hx
            rfl
      _ = (p.map (oldGraphHom (H := H) (a := a) (b := b) (c := c))).support :=
        (SimpleGraph.Walk.support_map _ _).symm
      _ = q.support := congrArg SimpleGraph.Walk.support hpMap
  have hpq (w : V) :
      w ∈ p.support ↔ (.inl w : V ⊕ Fin 2) ∈ q.support := by
    rw [← hpMapSupport]
    simp only [List.mem_map, Sum.inl.injEq]
    constructor
    · intro hw; exact ⟨w, hw, rfl⟩
    · rintro ⟨x, hx, hxw⟩; exact hxw ▸ hx
  refine ⟨y, z, hyPin, hzPin, hyz, p, hp, ?_⟩
  intro w
  constructor
  · intro hwp
    exact hqSub _ ((hpq w).1 hwp)
  · intro hwrim
    rcases hrim (.inl w) hwrim with hwi | hwq
    · exact (Sum.inl_ne_inr hwi).elim
    · exact (hpq w).2 hwq

/-- Four occurrences drawn from three pins cannot be pairwise separated in
the cyclic order relevant to the two-new-vertex rim.  Thus one of the two
prepared pieces between consecutive gadget edges is trivial. -/
theorem left_or_right_pin_repeats
    {y z u v : V}
    (hy : y = a ∨ y = b ∨ y = c)
    (hz : z = a ∨ z = b ∨ z = c)
    (hu : u = a ∨ u = b ∨ u = c)
    (hv : v = a ∨ v = b ∨ v = c)
    (hyz : y ≠ z) (hyv : y ≠ v) (huz : u ≠ z) (huv : u ≠ v) :
    y = u ∨ v = z := by
  by_contra h
  push_neg at h
  rcases hy with rfl | rfl | rfl <;>
    rcases hz with rfl | rfl | rfl <;>
    rcases hu with rfl | rfl | rfl <;>
    rcases hv with rfl | rfl | rfl <;>
    simp_all

/-- Split a simple pin-to-pin path at an artificial vertex on it.  Removing
the two incident edges produces two simple pin-to-pin pieces.  Their supports
stay in the original path, and the cut vertex occurs in neither piece.  Since
there are only three pins, one of the two pieces has equal endpoints. -/
theorem exists_pinPath_split_at_new
    {y z : V}
    (hyPin : y = a ∨ y = b ∨ y = c)
    (hzPin : z = a ∨ z = b ∨ z = c)
    (hyz : y ≠ z)
    (p : (ahtDoublePinReplacement H a b c).Walk (.inl y) (.inl z))
    (hp : p.IsPath) (j : Fin 2)
    (hj : (.inr j : V ⊕ Fin 2) ∈ p.support) :
    ∃ u v : V,
      (u = a ∨ u = b ∨ u = c) ∧
      (v = a ∨ v = b ∨ v = c) ∧ u ≠ v ∧
      ∃ pLeft : (ahtDoublePinReplacement H a b c).Walk (.inl y) (.inl u),
        pLeft.IsPath ∧ (.inr j : V ⊕ Fin 2) ∉ pLeft.support ∧
        (∀ w ∈ pLeft.support, w ∈ p.support) ∧
      ∃ pRight : (ahtDoublePinReplacement H a b c).Walk (.inl v) (.inl z),
        pRight.IsPath ∧ (.inr j : V ⊕ Fin 2) ∉ pRight.support ∧
        (∀ w ∈ pRight.support, w ∈ p.support) ∧
        (∀ w ∈ p.support,
          w = .inr j ∨ w ∈ pLeft.support ∨ w ∈ pRight.support) ∧
        (y = u ∨ v = z) := by
  let l := p.takeUntil (.inr j) hj
  let r := p.dropUntil (.inr j) hj
  have hlNot : ¬l.Nil :=
    SimpleGraph.Walk.not_nil_of_ne Sum.inl_ne_inr
  have hrNot : ¬r.Nil :=
    SimpleGraph.Walk.not_nil_of_ne Sum.inr_ne_inl
  have hlPath : l.IsPath := hp.takeUntil hj
  have hrPath : r.IsPath := hp.dropUntil hj
  have hlAdj :
      (ahtDoublePinReplacement H a b c).Adj l.penultimate (.inr j) :=
    l.adj_penultimate hlNot
  obtain ⟨u, huPin, hu⟩ : ∃ u : V,
      (u = a ∨ u = b ∨ u = c) ∧ l.penultimate = .inl u := by
    cases hlu : l.penultimate with
    | inl u =>
        refine ⟨u, ?_, rfl⟩
        exact (adj_old_new_iff (H := H) (a := a) (b := b) (c := c)).mp
          (by simpa only [hlu] using hlAdj)
    | inr i =>
        have hij :
            (ahtDoublePinReplacement H a b c).Adj (.inr i) (.inr j) := by
          simpa only [hlu] using hlAdj
        exact (not_adj_new_new (H := H) (a := a) (b := b) (c := c) i j hij).elim
  have hrAdj :
      (ahtDoublePinReplacement H a b c).Adj (.inr j) r.snd :=
    r.adj_snd hrNot
  obtain ⟨v, hvPin, hv⟩ : ∃ v : V,
      (v = a ∨ v = b ∨ v = c) ∧ r.snd = .inl v := by
    cases hrv : r.snd with
    | inl v =>
        refine ⟨v, ?_, rfl⟩
        exact (adj_new_old_iff (H := H) (a := a) (b := b) (c := c)).mp
          (by simpa only [hrv] using hrAdj)
    | inr i =>
        have hji :
            (ahtDoublePinReplacement H a b c).Adj (.inr j) (.inr i) := by
          simpa only [hrv] using hrAdj
        exact (not_adj_new_new (H := H) (a := a) (b := b) (c := c) j i hji).elim
  have hnodup : (l.support ++ r.support.tail).Nodup := by
    have h := hp.support_nodup
    rw [← p.take_spec hj, SimpleGraph.Walk.support_append] at h
    exact h
  have huLeft : (.inl u : V ⊕ Fin 2) ∈ l.support := by
    rw [← hu]
    exact List.mem_of_mem_dropLast (l.penultimate_mem_dropLast_support hlNot)
  have hvRight : (.inl v : V ⊕ Fin 2) ∈ r.support.tail := by
    rw [← hv]
    exact r.snd_mem_tail_support hrNot
  have hyLeft : (.inl y : V ⊕ Fin 2) ∈ l.support := l.start_mem_support
  have hzRight : (.inl z : V ⊕ Fin 2) ∈ r.support.tail :=
    r.end_mem_tail_support hrNot
  have huv : u ≠ v := by
    intro huv
    subst v
    exact ((List.nodup_append.mp hnodup).2.2 _ huLeft _ hvRight) rfl
  have hyv : y ≠ v := by
    intro hyv
    subst v
    exact ((List.nodup_append.mp hnodup).2.2 _ hyLeft _ hvRight) rfl
  have huz : u ≠ z := by
    intro huz
    subst z
    exact ((List.nodup_append.mp hnodup).2.2 _ huLeft _ hzRight) rfl
  have hdirect : y = u ∨ v = z :=
    left_or_right_pin_repeats hyPin hzPin huPin hvPin hyz hyv huz huv
  let pLeft : (ahtDoublePinReplacement H a b c).Walk (.inl y) (.inl u) :=
    l.dropLast.copy rfl hu
  let pRight : (ahtDoublePinReplacement H a b c).Walk (.inl v) (.inl z) :=
    r.tail.copy hv rfl
  have hpLeft : pLeft.IsPath :=
    (SimpleGraph.Walk.isPath_copy l.dropLast rfl hu).2 hlPath.dropLast
  have hpRight : pRight.IsPath :=
    (SimpleGraph.Walk.isPath_copy r.tail hv rfl).2 hrPath.tail
  have hjLeft : (.inr j : V ⊕ Fin 2) ∉ pLeft.support := by
    have hlNodup := hlPath.support_nodup
    have hs := l.support_dropLast_concat hlNot
    rw [← hs] at hlNodup
    have hjDrop : (.inr j : V ⊕ Fin 2) ∉ l.dropLast.support :=
      fun hmem ↦ hlNodup.disjoint hmem (by simp)
    simpa only [pLeft, SimpleGraph.Walk.support_copy] using hjDrop
  have hjRight : (.inr j : V ⊕ Fin 2) ∉ pRight.support := by
    have hrNodup := hrPath.support_nodup
    rw [← r.cons_support_tail hrNot] at hrNodup
    have hjTail : (.inr j : V ⊕ Fin 2) ∉ r.tail.support :=
      (List.nodup_cons.mp hrNodup).1
    simpa only [pRight, SimpleGraph.Walk.support_copy] using hjTail
  have hpLeftSub : ∀ w ∈ pLeft.support, w ∈ p.support := by
    intro w hw
    have hwDrop : w ∈ l.dropLast.support := by
      simpa only [pLeft, SimpleGraph.Walk.support_copy] using hw
    have hwL : w ∈ l.support := by
      rw [l.support_dropLast hlNot] at hwDrop
      exact List.mem_of_mem_dropLast hwDrop
    exact p.support_takeUntil_subset_support hj hwL
  have hpRightSub : ∀ w ∈ pRight.support, w ∈ p.support := by
    intro w hw
    have hwTail : w ∈ r.tail.support := by
      simpa only [pRight, SimpleGraph.Walk.support_copy] using hw
    have hwR : w ∈ r.support := by
      rw [r.support_tail_of_not_nil hrNot] at hwTail
      exact List.mem_of_mem_tail hwTail
    exact p.support_dropUntil_subset_support hj hwR
  have hpCover : ∀ w ∈ p.support,
      w = .inr j ∨ w ∈ pLeft.support ∨ w ∈ pRight.support := by
    intro w hw
    have hwParts : w ∈ l.support ∨ w ∈ r.support.tail := by
      have : w ∈ (l.append r).support := by
        rw [p.take_spec hj]
        exact hw
      simpa only [SimpleGraph.Walk.support_append, List.mem_append] using this
    rcases hwParts with hwL | hwR
    · have hs := l.support_dropLast_concat hlNot
      rw [← hs, List.mem_append] at hwL
      rcases hwL with hwDrop | hwj
      · right; left
        simpa only [pLeft, SimpleGraph.Walk.support_copy] using hwDrop
      · left
        simpa only [List.mem_singleton] using hwj
    · right; right
      have hwTail : w ∈ r.tail.support := by
        rw [r.support_tail_of_not_nil hrNot]
        exact hwR
      simpa only [pRight, SimpleGraph.Walk.support_copy] using hwTail
  exact ⟨u, v, huPin, hvPin, huv, pLeft, hpLeft, hjLeft, hpLeftSub,
    pRight, hpRight, hjRight, hpRightSub, hpCover, hdirect⟩

/-- If both artificial vertices lie on a simple replacement rim, removing
their four incident rim edges leaves two old simple paths.  Because the four
gadget incidences use only three pins, one of those paths is nil.  On old
vertices the two path supports together are exactly the rim support. -/
theorem exists_old_pinPaths_of_cycle_contains_both_new
    {s : V ⊕ Fin 2}
    (rim : (ahtDoublePinReplacement H a b c).Walk s s)
    (hcycle : rim.IsCycle) (i j : Fin 2)
    (hij : i ≠ j) (hfin : ∀ k : Fin 2, k = i ∨ k = j)
    (hi : (.inr i : V ⊕ Fin 2) ∈ rim.support)
    (hj : (.inr j : V ⊕ Fin 2) ∈ rim.support) :
    ∃ y z u v : V,
      (y = a ∨ y = b ∨ y = c) ∧
      (z = a ∨ z = b ∨ z = c) ∧
      (u = a ∨ u = b ∨ u = c) ∧
      (v = a ∨ v = b ∨ v = c) ∧ y ≠ z ∧ u ≠ v ∧
      ∃ pLeft : H.Walk y u, pLeft.IsPath ∧
      ∃ pRight : H.Walk v z, pRight.IsPath ∧
        (y = u ∨ v = z) ∧
        ∀ w : V, (.inl w : V ⊕ Fin 2) ∈ rim.support ↔
          w ∈ pLeft.support ∨ w ∈ pRight.support := by
  obtain ⟨y, z, hyPin, hzPin, hyz, q, hq, hiq, hqSub, hrim⟩ :=
    exists_pinPath_around_new rim hcycle i hi
  have hjq : (.inr j : V ⊕ Fin 2) ∈ q.support := by
    rcases hrim (.inr j) hj with hji | hjq
    · have : j = i := Sum.inr.inj hji
      exact (hij this.symm).elim
    · exact hjq
  obtain ⟨u, v, huPin, hvPin, huv,
      qLeft, hqLeft, hjLeft, hqLeftSub,
      qRight, hqRight, hjRight, hqRightSub, hqCover, hdirect⟩ :=
    exists_pinPath_split_at_new hyPin hzPin hyz q hq j hjq
  have holdLeft : ∀ w ∈ qLeft.support, ∃ x : V, w = .inl x := by
    intro w hw
    rcases w with x | k
    · exact ⟨x, rfl⟩
    · rcases hfin k with rfl | rfl
      · exact (hiq (hqLeftSub _ hw)).elim
      · exact (hjLeft hw).elim
  have holdRight : ∀ w ∈ qRight.support, ∃ x : V, w = .inl x := by
    intro w hw
    rcases w with x | k
    · exact ⟨x, rfl⟩
    · rcases hfin k with rfl | rfl
      · exact (hiq (hqRightSub _ hw)).elim
      · exact (hjRight hw).elim
  obtain ⟨pLeft, hpLeftMap⟩ :=
    exists_oldWalk_of_support_avoids_new qLeft holdLeft
  obtain ⟨pRight, hpRightMap⟩ :=
    exists_oldWalk_of_support_avoids_new qRight holdRight
  have hpLeft : pLeft.IsPath := by
    apply SimpleGraph.Walk.IsPath.of_map
    rw [hpLeftMap]
    exact hqLeft
  have hpRight : pRight.IsPath := by
    apply SimpleGraph.Walk.IsPath.of_map
    rw [hpRightMap]
    exact hqRight
  have hpLeftMapSupport :
      pLeft.support.map (Sum.inl : V → V ⊕ Fin 2) = qLeft.support := by
    calc
      _ = pLeft.support.map
          (oldGraphHom (H := H) (a := a) (b := b) (c := c)) := by
            apply List.map_congr_left
            intro x hx
            rfl
      _ = (pLeft.map
          (oldGraphHom (H := H) (a := a) (b := b) (c := c))).support :=
        (SimpleGraph.Walk.support_map _ _).symm
      _ = qLeft.support := congrArg SimpleGraph.Walk.support hpLeftMap
  have hpRightMapSupport :
      pRight.support.map (Sum.inl : V → V ⊕ Fin 2) = qRight.support := by
    calc
      _ = pRight.support.map
          (oldGraphHom (H := H) (a := a) (b := b) (c := c)) := by
            apply List.map_congr_left
            intro x hx
            rfl
      _ = (pRight.map
          (oldGraphHom (H := H) (a := a) (b := b) (c := c))).support :=
        (SimpleGraph.Walk.support_map _ _).symm
      _ = qRight.support := congrArg SimpleGraph.Walk.support hpRightMap
  have hpLeftQ (w : V) :
      w ∈ pLeft.support ↔ (.inl w : V ⊕ Fin 2) ∈ qLeft.support := by
    rw [← hpLeftMapSupport]
    simp only [List.mem_map, Sum.inl.injEq]
    constructor
    · intro hw; exact ⟨w, hw, rfl⟩
    · rintro ⟨x, hx, hxw⟩; exact hxw ▸ hx
  have hpRightQ (w : V) :
      w ∈ pRight.support ↔ (.inl w : V ⊕ Fin 2) ∈ qRight.support := by
    rw [← hpRightMapSupport]
    simp only [List.mem_map, Sum.inl.injEq]
    constructor
    · intro hw; exact ⟨w, hw, rfl⟩
    · rintro ⟨x, hx, hxw⟩; exact hxw ▸ hx
  refine ⟨y, z, u, v, hyPin, hzPin, huPin, hvPin, hyz, huv,
    pLeft, hpLeft, pRight, hpRight, hdirect, ?_⟩
  intro w
  constructor
  · intro hwrim
    rcases hrim (.inl w) hwrim with hwi | hwq
    · exact (Sum.inl_ne_inr hwi).elim
    · rcases hqCover (.inl w) hwq with hwj | hwLeft | hwRight
      · exact (Sum.inl_ne_inr hwj).elim
      · exact Or.inl ((hpLeftQ w).2 hwLeft)
      · exact Or.inr ((hpRightQ w).2 hwRight)
  · rintro (hwLeft | hwRight)
    · exact hqSub _ (hqLeftSub _ ((hpLeftQ w).1 hwLeft))
    · exact hqSub _ (hqRightSub _ ((hpRightQ w).1 hwRight))

/-- If the rim of a wheel centred at an old vertex avoids both newly added
vertices, the whole wheel already lies in the old graph.  The spokes to the
rim are old--old edges, so the exact three-neighbour count is preserved. -/
theorem hasWheelCenteredAt_old_of_cycle_avoids_new {x r₀ : V}
    (rim : (ahtDoublePinReplacement H a b c).Walk (.inl r₀) (.inl r₀))
    (hcycle : rim.IsCycle) (hxrim : (.inl x : V ⊕ Fin 2) ∉ rim.support)
    (hthree : 3 ≤ ((ahtDoublePinReplacement H a b c).neighborFinset (.inl x) ∩
      rim.support.toFinset).card)
    (havoid : ∀ i : Fin 2, (.inr i : V ⊕ Fin 2) ∉ rim.support) :
    HasWheelCenteredAt H x := by
  classical
  have hold : ∀ z ∈ rim.support, ∃ r : V, z = .inl r := by
    intro z hz
    rcases z with r | i
    · exact ⟨r, rfl⟩
    · exact (havoid i hz).elim
  obtain ⟨q, hqMap⟩ := exists_oldWalk_of_support_avoids_new rim hold
  have hqCycle : q.IsCycle := by
    apply SimpleGraph.Walk.IsCycle.of_map
    rw [hqMap]
    exact hcycle
  have hqrim (y : V) :
      (.inl y : V ⊕ Fin 2) ∈ rim.support ↔ y ∈ q.support := by
    rw [← hqMap]
    change (.inl y : V ⊕ Fin 2) ∈
      (q.map (oldGraphHom (H := H) (a := a) (b := b) (c := c))).support ↔ _
    rw [SimpleGraph.Walk.support_map]
    simp
  have hxq : x ∉ q.support := by
    intro hx
    exact hxrim ((hqrim x).2 hx)
  let e : V ↪ V ⊕ Fin 2 := oldVertexEmbedding
  have hfin :
      (ahtDoublePinReplacement H a b c).neighborFinset (.inl x) ∩
          rim.support.toFinset =
        (H.neighborFinset x ∩ q.support.toFinset).map e := by
    ext z
    rcases z with y | i
    · simp [SimpleGraph.mem_neighborFinset, hqrim, e, oldVertexEmbedding]
    · simp [SimpleGraph.mem_neighborFinset, havoid i, e, oldVertexEmbedding]
  refine ⟨r₀, q, hqCycle, hxq, ?_⟩
  rw [hfin, Finset.card_map] at hthree
  exact hthree

/-! ## Three-connectivity of the double-pin operation -/

/-- Three distinct pins cannot all belong to a set of cardinality below
three. -/
theorem exists_pin_not_mem {D : Finset V}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hD : D.card < 3) :
    ∃ p : V, (p = a ∨ p = b ∨ p = c) ∧ p ∉ D := by
  by_contra h
  push_neg at h
  have hsub : ({a, b, c} : Finset V) ⊆ D := by
    intro p hp
    have hp' : p = a ∨ p = b ∨ p = c := by simpa using hp
    exact h p hp'
  have hcard := Finset.card_le_card hsub
  have hthree : ({a, b, c} : Finset V).card = 3 := by
    simp [hab, hac, hbc]
  rw [hthree] at hcard
  omega

/-- The replacement graph is connected as soon as the old torso is
preconnected and one pin is available. -/
theorem connected (hH : H.Connected) :
    (ahtDoublePinReplacement H a b c).Connected := by
  let f : H →g ahtDoublePinReplacement H a b c :=
    { toFun := Sum.inl
      map_rel' := by intro p q hpq; exact hpq }
  let root : V ⊕ Fin 2 := .inl a
  have hreach (x : V ⊕ Fin 2) :
      (ahtDoublePinReplacement H a b c).Reachable x root := by
    rcases x with p | i
    · exact (hH p a).map f
    · exact (adj_new_old_iff.mpr (Or.inl rfl)).reachable
  exact {
    preconnected := fun x y ↦ (hreach x).trans (hreach y).symm
    nonempty := ⟨root⟩ }

/-- Adding the two degree-three vertices on three distinct pins preserves
three-vertex-connectivity.  The proof uses exactly the deletion-of-two
vertices formulation: after any two deletions, one of the three pins
survives, and every surviving new vertex attaches there. -/
theorem vertexThreeConnected_of_isThreeConnected
    (hH : IsThreeConnected H)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    VertexThreeConnected (ahtDoublePinReplacement H a b c) := by
  let R := ahtDoublePinReplacement H a b c
  have hconnH : H.Connected := by
    have hpre := hH.induce_compl_preconnected (∅ : Finset V) (by simp)
    have hpreH : H.Preconnected := by
      intro p q
      let p' : {v : V // v ∉ (∅ : Finset V)} := ⟨p, by simp⟩
      let q' : {v : V // v ∉ (∅ : Finset V)} := ⟨q, by simp⟩
      let f : (H.induce fun v : V ↦ v ∉ (∅ : Finset V)) →g H :=
        { toFun := Subtype.val
          map_rel' := by intro u v huv; exact huv }
      exact (hpre p' q').map f
    exact { preconnected := hpreH
            nonempty := Fintype.card_pos_iff.mp (by
              have := hH.four_le_card
              omega) }
  have connect_delete (x y : V ⊕ Fin 2) (hxy : x ≠ y)
      (D : Finset V) (hD : D.card < 3)
      (hiff : ∀ p : V, p ∉ D ↔
        ((.inl p : V ⊕ Fin 2) ≠ x ∧ (.inl p : V ⊕ Fin 2) ≠ y)) :
      (R.induce fun z : V ⊕ Fin 2 ↦ z ≠ x ∧ z ≠ y).Connected := by
    obtain ⟨r, hrpin, hrD⟩ := exists_pin_not_mem hab hac hbc hD
    let VK := {p : V // p ∉ D}
    let VL := {z : V ⊕ Fin 2 // z ≠ x ∧ z ≠ y}
    let K : SimpleGraph VK := H.induce fun p : V ↦ p ∉ D
    let L : SimpleGraph VL := R.induce fun z : V ⊕ Fin 2 ↦ z ≠ x ∧ z ≠ y
    let f : K →g L :=
      { toFun := fun p ↦ ⟨.inl p.1, (hiff p.1).mp p.2⟩
        map_rel' := by
          intro p q hpq
          exact hpq }
    let rK : VK := ⟨r, hrD⟩
    let rL : VL := f rK
    have hpreK : K.Preconnected :=
      hH.induce_compl_preconnected D hD
    have hreach (z : VL) : L.Reachable z rL := by
      rcases z with ⟨z, hz⟩
      rcases z with p | i
      · let pK : VK := ⟨p, (hiff p).mpr hz⟩
        exact (hpreK pK rK).map f
      · apply SimpleGraph.Adj.reachable
        change R.Adj (.inr i) (.inl r)
        exact adj_new_old_iff.mpr hrpin
    exact {
      preconnected := fun z w ↦ (hreach z).trans (hreach w).symm
      nonempty := ⟨rL⟩ }
  refine ⟨?_, connected hconnH, ?_⟩
  · simp only [Fintype.card_sum, Fintype.card_fin]
    have := hH.four_le_card
    omega
  · intro x y hxy
    rcases x with p | i <;> rcases y with q | j
    · have hpq : p ≠ q := by
        intro hpq
        exact hxy (congrArg Sum.inl hpq)
      apply connect_delete (.inl p) (.inl q) hxy ({p, q} : Finset V)
      · simp [hpq]
      · intro r
        simp
    · apply connect_delete (.inl p) (.inr j) hxy ({p} : Finset V)
      · simp
      · intro r
        simp
    · apply connect_delete (.inr i) (.inl q) hxy ({q} : Finset V)
      · simp
      · intro r
        simp
    · apply connect_delete (.inr i) (.inr j) hxy (∅ : Finset V)
      · simp
      · intro r
        simp

/-! The two connectivity conventions used in the AHT development are
equivalent in the direction needed below.  We record the nontrivial
direction here because the double-pin proof above naturally uses deletion
of two vertices, while the paper states Lemma 6.4 using separations. -/

/-- Every walk from the strict left side of an AHT separation to its strict
right side contains a separator vertex. -/
theorem AHTSeparation.walk_meets_separator_local
    (s : AHTSeparation H) {u v : V} (p : H.Walk u v)
    (hu : u ∈ s.left \ s.right) (hv : v ∈ s.right \ s.left) :
    ∃ x, x ∈ p.support ∧ x ∈ s.separator := by
  induction p with
  | nil =>
      rw [Finset.mem_sdiff] at hu hv
      exact (hv.2 hu.1).elim
  | @cons u w v huw p ih =>
      rw [Finset.mem_sdiff] at hu hv
      rcases s.mem_left_or_mem_right w with hwL | hwR
      · by_cases hwR : w ∈ s.right
        · exact ⟨w, by simp, Finset.mem_inter.2 ⟨hwL, hwR⟩⟩
        · obtain ⟨x, hxp, hxs⟩ := ih
              (Finset.mem_sdiff.2 ⟨hwL, hwR⟩) (Finset.mem_sdiff.2 hv)
          exact ⟨x, by simp [hxp], hxs⟩
      · by_cases hwL : w ∈ s.left
        · exact ⟨w, by simp, Finset.mem_inter.2 ⟨hwL, hwR⟩⟩
        · exact (s.not_adj hu.1 hu.2 hwR hwL huw).elim

/-- A vertex set which contains one vertex of a walk and is closed under
adjacency in the walk's edge-subgraph contains the entire support.  This is
the small connectedness device used in the fresh-pin wheel-centre exclusion:
the four gadget vertices form a closed set in the alleged rim. -/
theorem walk_support_subset_of_toSubgraph_neighbor_closed
    {u v : V} (p : H.Walk u v) (S : Set V) {s : V}
    (hsP : s ∈ p.support) (hsS : s ∈ S)
    (hclosed : ∀ x ∈ S, p.toSubgraph.neighborSet x ⊆ S) :
    ∀ x ∈ p.support, x ∈ S := by
  have endpoint_closed {x y : p.toSubgraph.verts}
      (q : p.toSubgraph.coe.Walk x y) (hx : x.1 ∈ S) : y.1 ∈ S := by
    induction q with
    | nil => exact hx
    | @cons x z y hxz q ih =>
        apply ih
        exact hclosed x.1 hx hxz
  intro x hxP
  let s' : p.toSubgraph.verts :=
    ⟨s, p.mem_verts_toSubgraph.mpr hsP⟩
  let x' : p.toSubgraph.verts :=
    ⟨x, p.mem_verts_toSubgraph.mpr hxP⟩
  obtain ⟨q⟩ := p.toSubgraph_connected s' x'
  exact endpoint_closed q hsS

/-- On a finite graph, connectivity after deletion of every two distinct
vertices implies AHT's separation-based notion of three-connectivity. -/
theorem isThreeConnected_of_vertexThreeConnected
    (hH : VertexThreeConnected H) : IsThreeConnected H := by
  refine ⟨Nat.lt_of_succ_le hH.1, ?_⟩
  intro s hs
  by_contra horder
  have hsepCard : s.separator.card ≤ 2 := by
    have : s.order < 3 := Nat.lt_of_not_ge horder
    change s.separator.card ≤ 2
    change s.separator.card < 3 at this
    omega
  obtain ⟨u, hu⟩ := hs.1
  obtain ⟨v, hv⟩ := hs.2
  have huv : u ≠ v := by
    intro huv
    subst v
    exact (Finset.mem_sdiff.1 hv).2 (Finset.mem_sdiff.1 hu).1
  let T : Finset V := Finset.univ \ {u, v}
  have hsepT : s.separator ⊆ T := by
    intro x hx
    have hxLR := Finset.mem_inter.1 hx
    have hxu : x ≠ u := by
      intro hxu
      subst x
      exact (Finset.mem_sdiff.1 hu).2 hxLR.2
    have hxv : x ≠ v := by
      intro hxv
      subst x
      exact (Finset.mem_sdiff.1 hv).2 hxLR.1
    simp [T, hxu, hxv]
  have hcardT : 2 ≤ T.card := by
    have hcard := hH.1
    have hpair : ({u, v} : Finset V).card = 2 := by simp [huv]
    have hcardEq : T.card = Fintype.card V - 2 := by
      simp [T, Finset.card_sdiff, hpair]
    rw [hcardEq]
    omega
  obtain ⟨D, hsepD, hDT, hcardD⟩ :=
    Finset.exists_subsuperset_card_eq hsepT hsepCard hcardT
  obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hcardD
  have huD : u ∉ ({x, y} : Finset V) := by
    intro huD
    have := hDT huD
    simpa [T] using this
  have hvD : v ∉ ({x, y} : Finset V) := by
    intro hvD
    have := hDT hvD
    simpa [T] using this
  let K := H.induce (fun z : V ↦ z ≠ x ∧ z ≠ y)
  let uK : {z : V // z ≠ x ∧ z ≠ y} := ⟨u, by simpa using huD⟩
  let vK : {z : V // z ≠ x ∧ z ≠ y} := ⟨v, by simpa using hvD⟩
  have hconnK : K.Connected := hH.2.2 x y hxy
  obtain ⟨p⟩ := hconnK uK vK
  let f : K →g H :=
    { toFun := Subtype.val
      map_rel' := by intro z w hzw; exact hzw }
  let q : H.Walk u v := p.map f
  obtain ⟨z, hzq, hzs⟩ :=
    AHTSeparation.walk_meets_separator_local s q hu hv
  have hzD : z ∈ ({x, y} : Finset V) := hsepD hzs
  have hzNotD : z ∉ ({x, y} : Finset V) := by
    dsimp [q] at hzq
    rw [SimpleGraph.Walk.support_map] at hzq
    obtain ⟨zK, hzK, hzEq⟩ := List.mem_map.mp hzq
    subst z
    have hf : f zK = zK.1 := rfl
    rw [hf]
    have hzKprop : (zK : V) ≠ x ∧ (zK : V) ≠ y := zK.property
    simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hzKprop
  exact hzNotD hzD

/-- The double-pin replacement is three-connected in the exact
separation-based sense used in AHT Lemma 6.4 whenever its prepared torso is
three-connected. -/
theorem isThreeConnected_of_isThreeConnected
    (hH : IsThreeConnected H)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    IsThreeConnected (ahtDoublePinReplacement H a b c) :=
  isThreeConnected_of_vertexThreeConnected
    (vertexThreeConnected_of_isThreeConnected hH hab hac hbc)

/-! ## Triangle and wheel-centre bookkeeping for the source torso -/

/-- The triangle-freeness check in AHT Lemma 6.4.  In the prepared torso the
three pins are independent (the three possible boundary edges were deleted),
so adding the two common neighbours creates no triangle. -/
theorem triangleFree
    (htri : AHTTriangleFree H)
    (hpins : ∀ p q : V,
      (p = a ∨ p = b ∨ p = c) →
      (q = a ∨ q = b ∨ q = c) → ¬H.Adj p q) :
    AHTTriangleFree (ahtDoublePinReplacement H a b c) := by
  intro x y z hxy hyz hzx
  rcases x with x | i <;> rcases y with y | j <;> rcases z with z | k
  · exact htri hxy hyz hzx
  · exact hpins x y
      (adj_new_old_iff (H := H) (a := a) (b := b) (c := c) |>.mp hzx)
      (adj_old_new_iff (H := H) (a := a) (b := b) (c := c) |>.mp hyz) hxy
  · exact hpins x z
      (adj_old_new_iff (H := H) (a := a) (b := b) (c := c) |>.mp hxy)
      (adj_new_old_iff (H := H) (a := a) (b := b) (c := c) |>.mp hyz) hzx.symm
  · exact not_adj_new_new (H := H) (a := a) (b := b) (c := c) j k hyz
  · exact hpins y z
      (adj_new_old_iff (H := H) (a := a) (b := b) (c := c) |>.mp hxy)
      (adj_old_new_iff (H := H) (a := a) (b := b) (c := c) |>.mp hzx) hyz
  · exact not_adj_new_new (H := H) (a := a) (b := b) (c := c) i k hzx
  · exact not_adj_new_new (H := H) (a := a) (b := b) (c := c) i j hxy
  · exact not_adj_new_new (H := H) (a := a) (b := b) (c := c) i j hxy

/-- A newly adjoined vertex cannot be a wheel centre when every pin has
degree one in the prepared torso.  This is the parity/degree argument used
for `d,d'` in AHT Lemma 6.4: a rim through all three pins would force the
other new vertex to have three incident rim edges. -/
theorem not_hasWheelCenteredAt_new_of_other
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hdega : H.degree a = 1) (hdegb : H.degree b = 1)
    (hdegc : H.degree c = 1)
    (i j : Fin 2) (hij : i ≠ j) (hcover : ∀ k : Fin 2, k = i ∨ k = j) :
    ¬HasWheelCenteredAt (ahtDoublePinReplacement H a b c) (.inr i) := by
  let R := ahtDoublePinReplacement H a b c
  intro hw
  rcases hw with ⟨r, rim, hcycle, hiRim, hthree⟩
  have hNcard : (R.neighborFinset (.inr i)).card = 3 := by
    simpa [R] using degree_new (H := H) hab hac hbc i
  have hinterEq :
      R.neighborFinset (.inr i) ∩ rim.support.toFinset =
        R.neighborFinset (.inr i) := by
    apply Finset.eq_of_subset_of_card_le Finset.inter_subset_left
    simpa [hNcard] using hthree
  have hneighborsSupport :
      R.neighborFinset (.inr i) ⊆ rim.support.toFinset := by
    intro z hz
    have hz' : z ∈ R.neighborFinset (.inr i) ∩ rim.support.toFinset := by
      rw [hinterEq]
      exact hz
    exact (Finset.mem_inter.1 hz').2
  have haSupport : (.inl a : V ⊕ Fin 2) ∈ rim.support := by
    have haN : (.inl a : V ⊕ Fin 2) ∈ R.neighborFinset (.inr i) := by
      simp [R, SimpleGraph.mem_neighborFinset]
    simpa using hneighborsSupport haN
  have hbSupport : (.inl b : V ⊕ Fin 2) ∈ rim.support := by
    have hbN : (.inl b : V ⊕ Fin 2) ∈ R.neighborFinset (.inr i) := by
      simp [R, SimpleGraph.mem_neighborFinset]
    simpa using hneighborsSupport hbN
  have hcSupport : (.inl c : V ⊕ Fin 2) ∈ rim.support := by
    have hcN : (.inl c : V ⊕ Fin 2) ∈ R.neighborFinset (.inr i) := by
      simp [R, SimpleGraph.mem_neighborFinset]
    simpa using hneighborsSupport hcN
  have pin_other_edge (p : V) (hpSupport : (.inl p : V ⊕ Fin 2) ∈ rim.support)
      (hdegp : H.degree p = 1) :
      rim.toSubgraph.Adj (.inl p) (.inr j) := by
    by_contra hpj
    have hsub : rim.toSubgraph.neighborSet (.inl p) ⊆
        Sum.inl '' H.neighborSet p := by
      intro z hz
      have hzAdj : rim.toSubgraph.Adj (.inl p) z := hz
      have hzR : R.Adj (.inl p) z := hzAdj.adj_sub
      rcases z with q | k
      · refine ⟨q, ?_, rfl⟩
        exact hzR
      · rcases hcover k with hki | hkj
        · have hkSupport : (.inr k : V ⊕ Fin 2) ∈ rim.support :=
            rim.mem_verts_toSubgraph.mp hzAdj.snd_mem
          have hiSupport : (.inr i : V ⊕ Fin 2) ∈ rim.support := by
            simpa [hki] using hkSupport
          exact (hiRim hiSupport).elim
        · have hzAdj' : rim.toSubgraph.Adj (.inl p) (.inr j) := by
            simpa [hkj] using hzAdj
          exact (hpj hzAdj').elim
    have hleOne : (rim.toSubgraph.neighborSet (.inl p)).ncard ≤ 1 := by
      calc
        (rim.toSubgraph.neighborSet (.inl p)).ncard ≤
            (Sum.inl '' H.neighborSet p).ncard := Set.ncard_le_ncard hsub
        _ = (H.neighborSet p).ncard :=
          Set.ncard_image_of_injective _ Sum.inl_injective
        _ = Fintype.card (H.neighborSet p) :=
          (Set.fintypeCard_eq_ncard (H.neighborSet p)).symm
        _ = H.degree p := by
          exact H.card_neighborSet_eq_degree p
        _ = 1 := hdegp
    have htwo := hcycle.ncard_neighborSet_toSubgraph_eq_two hpSupport
    omega
  have haj := pin_other_edge a haSupport hdega
  have hbj := pin_other_edge b hbSupport hdegb
  have hcj := pin_other_edge c hcSupport hdegc
  have hjSupport : (.inr j : V ⊕ Fin 2) ∈ rim.support :=
    rim.mem_verts_toSubgraph.mp haj.snd_mem
  have hthreeAtJ : 3 ≤ (rim.toSubgraph.neighborSet (.inr j)).ncard := by
    have hsub : ({(.inl a : V ⊕ Fin 2), .inl b, .inl c} : Set (V ⊕ Fin 2)) ⊆
        rim.toSubgraph.neighborSet (.inr j) := by
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl
      · exact haj.symm
      · exact hbj.symm
      · exact hcj.symm
    have := Set.ncard_le_ncard hsub
    simpa [hab, hac, hbc] using this
  have htwoAtJ := hcycle.ncard_neighborSet_toSubgraph_eq_two hjSupport
  omega

/-- Both vertices `d,d'` adjoined by AHT Lemma 6.4 are excluded from the
set of wheel centres. -/
theorem not_hasWheelCenteredAt_new
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hdega : H.degree a = 1) (hdegb : H.degree b = 1)
    (hdegc : H.degree c = 1) (i : Fin 2) :
    ¬HasWheelCenteredAt (ahtDoublePinReplacement H a b c) (.inr i) := by
  fin_cases i
  · exact not_hasWheelCenteredAt_new_of_other hab hac hbc hdega hdegb hdegc
      0 1 (by decide) (by intro k; fin_cases k <;> simp)
  · exact not_hasWheelCenteredAt_new_of_other hab hac hbc hdega hdegb hdegc
      1 0 (by decide) (by intro k; fin_cases k <;> simp)

/-- Source-exact packaged output of the double-pin step: the two new
vertices are degree-three false twins. -/
theorem new_vertices_degree_three_falseTwins
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    AreFalseTwins (ahtDoublePinReplacement H a b c) (.inr 0) (.inr 1) ∧
      (ahtDoublePinReplacement H a b c).degree (.inr 0) = 3 ∧
      (ahtDoublePinReplacement H a b c).degree (.inr 1) = 3 := by
  exact ⟨new_vertices_areFalseTwins,
    degree_new hab hac hbc 0, degree_new hab hac hbc 1⟩

end ahtDoublePinReplacement

/-! ## The source-exact three-fragment construction -/

/-- A three-fragment in the sense used in AHT Section 6.  Its external open
neighbourhood is exactly the three displayed vertices, and both the fragment
and the part on the other side of its boundary are nonempty. -/
structure AHTThreeFragment {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] where
  verts : Finset V
  a : V
  b : V
  c : V
  ab : a ≠ b
  ac : a ≠ c
  bc : b ≠ c
  boundary_disjoint : Disjoint verts ({a, b, c} : Finset V)
  nonempty : verts.Nonempty
  outside_nonempty :
    (Finset.univ \ (verts ∪ ({a, b, c} : Finset V))).Nonempty
  boundary_exact : ∀ x : V, x ∉ verts →
    ((∃ y ∈ verts, G.Adj x y) ↔ x = a ∨ x = b ∨ x = c)

namespace AHTThreeFragment

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable (F : AHTThreeFragment G)

/-- The ordered boundary triple `a,b,c`. -/
def boundaryVertex : Fin 3 → V := ![F.a, F.b, F.c]

def boundaryFinset : Finset V := {F.a, F.b, F.c}

def otherBoundaryFinset (i : Fin 3) : Finset V :=
  F.boundaryFinset.erase (F.boundaryVertex i)

@[simp] theorem boundaryVertex_zero : F.boundaryVertex 0 = F.a := rfl
@[simp] theorem boundaryVertex_one : F.boundaryVertex 1 = F.b := rfl
@[simp] theorem boundaryVertex_two : F.boundaryVertex 2 = F.c := rfl

theorem boundaryFinset_card : F.boundaryFinset.card = 3 := by
  simp [boundaryFinset, F.ab, F.ac, F.bc]

theorem boundaryVertex_mem_boundaryFinset (i : Fin 3) :
    F.boundaryVertex i ∈ F.boundaryFinset := by
  fin_cases i <;> simp [boundaryFinset]

theorem otherBoundaryFinset_card (i : Fin 3) :
    (F.otherBoundaryFinset i).card = 2 := by
  rw [otherBoundaryFinset, Finset.card_erase_of_mem
    (F.boundaryVertex_mem_boundaryFinset i), F.boundaryFinset_card]

theorem boundaryVertex_not_mem_otherBoundaryFinset (i : Fin 3) :
    F.boundaryVertex i ∉ F.otherBoundaryFinset i := by
  simp [otherBoundaryFinset]

theorem otherBoundaryFinset_subset_boundaryFinset (i : Fin 3) :
    F.otherBoundaryFinset i ⊆ F.boundaryFinset :=
  Finset.erase_subset _ _

/-- The vertices retained from the ambient graph before fresh pins are
introduced. -/
abbrev BaseVertex :=
  {v : V // v ∈ F.verts ∪ ({F.a, F.b, F.c} : Finset V)}

/-- Ambient neighbours of boundary vertex `i` that lie in the fragment. -/
def insideNeighborFinset (i : Fin 3) : Finset V :=
  G.neighborFinset (F.boundaryVertex i) ∩ F.verts

/-- Exactly the source condition under which a fresh degree-one pin is
attached to a boundary vertex. -/
def NeedsFreshPin (i : Fin 3) : Prop := 2 ≤ (F.insideNeighborFinset i).card

instance (i : Fin 3) : Decidable (F.NeedsFreshPin i) := by
  unfold NeedsFreshPin
  exact inferInstance

/-- Fresh pins are present only for boundary vertices having at least two
neighbours in the fragment. -/
abbrev FreshPin := {i : Fin 3 // F.NeedsFreshPin i}

/-- Vertex type of the prepared graph before `d,d'` are adjoined. -/
abbrev PreparedVertex := F.BaseVertex ⊕ F.FreshPin

/-- The graph obtained from `G[F ∪ {a,b,c}]` by deleting the three possible
boundary edges and attaching the optional fresh pins. -/
def preparedGraph : SimpleGraph F.PreparedVertex where
  Adj x y :=
    match x, y with
    | .inl p, .inl q =>
        G.Adj p.1 q.1 ∧
          ¬(p.1 ∈ ({F.a, F.b, F.c} : Finset V) ∧
            q.1 ∈ ({F.a, F.b, F.c} : Finset V))
    | .inl p, .inr j => p.1 = F.boundaryVertex j.1
    | .inr i, .inl q => q.1 = F.boundaryVertex i.1
    | .inr _, .inr _ => False
  symm.symm := by
    intro x y h
    rcases x with p | i <;> rcases y with q | j
    · exact ⟨h.1.symm, fun hbad ↦ h.2 ⟨hbad.2, hbad.1⟩⟩
    · exact h
    · exact h
    · exact h
  loopless.irrefl := by
    intro x h
    rcases x with p | i
    · exact G.loopless.irrefl p.1 h.1
    · exact h

instance preparedGraph.instDecidableRel : DecidableRel F.preparedGraph.Adj := by
  intro x y
  rcases x with p | i <;> rcases y with q | j
  · change Decidable (G.Adj p.1 q.1 ∧
        ¬(p.1 ∈ ({F.a, F.b, F.c} : Finset V) ∧
          q.1 ∈ ({F.a, F.b, F.c} : Finset V)))
    exact inferInstance
  · change Decidable (p.1 = F.boundaryVertex j.1)
    exact inferInstance
  · change Decidable (q.1 = F.boundaryVertex i.1)
    exact inferInstance
  · exact isFalse id

/-- The old-vertex part of the prepared graph, expressed on the base-vertex
type itself.  Its only missing ambient edges are the three possible edges
inside the boundary triple. -/
def preparedOldGraph : SimpleGraph F.BaseVertex :=
  F.preparedGraph.comap (Sum.inl : F.BaseVertex → F.PreparedVertex)

instance preparedOldGraph.instDecidableRel :
    DecidableRel F.preparedOldGraph.Adj := by
  unfold preparedOldGraph
  infer_instance

/-- Forgetting the fragment carrier sends every old prepared edge to its
ambient edge. -/
def preparedOldToAmbient : F.preparedOldGraph →g G where
  toFun := Subtype.val
  map_rel' := by
    intro p q hpq
    exact hpq.1

theorem preparedOldToAmbient_injective :
    Function.Injective F.preparedOldToAmbient := Subtype.val_injective

/-- Inclusion of the old-vertex part back into the prepared graph. -/
def preparedOldInclusion : F.preparedOldGraph →g F.preparedGraph where
  toFun := Sum.inl
  map_rel' := by intro p q hpq; exact hpq

@[simp] theorem preparedOldInclusion_apply (p : F.BaseVertex) :
    F.preparedOldInclusion p = (.inl p : F.PreparedVertex) := rfl

theorem preparedOldInclusion_injective :
    Function.Injective F.preparedOldInclusion := Sum.inl_injective

/-- A prepared walk which avoids every fresh pin is a walk in the old part
of the prepared graph. -/
theorem exists_preparedOldWalk_of_support_avoids_fresh
    {p q : F.BaseVertex}
    (w : F.preparedGraph.Walk (.inl p) (.inl q))
    (hold : ∀ z ∈ w.support, ∃ r : F.BaseVertex, z = .inl r) :
    ∃ r : F.preparedOldGraph.Walk p q,
      r.map F.preparedOldInclusion = w := by
  let rec lower (n : ℕ) {s t : F.BaseVertex}
      (v : F.preparedGraph.Walk (.inl s) (.inl t))
      (hlen : v.length ≤ n)
      (hv : ∀ z ∈ v.support, ∃ r : F.BaseVertex, z = .inl r) :
      ∃ r : F.preparedOldGraph.Walk s t,
        r.map F.preparedOldInclusion = v := by
    cases n with
    | zero =>
      cases v with
      | nil => exact ⟨.nil, rfl⟩
      | cons huz tail => simp at hlen
    | succ n =>
      cases v with
      | nil => exact ⟨.nil, rfl⟩
      | @cons _ z _ huz tail =>
        obtain ⟨m, hm⟩ := hv z (by simp)
        subst z
        have huzOld : F.preparedOldGraph.Adj s m := huz
        have htail : ∀ y ∈ tail.support, ∃ r : F.BaseVertex, y = .inl r := by
          intro y hy
          exact hv y (by simp [hy])
        have htailLen : tail.length ≤ n := by
          simp only [SimpleGraph.Walk.length_cons] at hlen
          omega
        obtain ⟨r, hr⟩ := lower n tail htailLen htail
        refine ⟨r.cons huzOld, ?_⟩
        simp [hr]
  termination_by n
  decreasing_by omega
  exact lower w.length w le_rfl hold

/-- A prepared wheel whose rim avoids the pendant fresh pins lifts directly
to an ambient wheel.  Boundary--boundary edges were only deleted, so every
old prepared edge and spoke is an ambient edge. -/
theorem ambient_hasWheelCenteredAt_of_prepared_cycle_avoids_fresh
    {x r₀ : F.BaseVertex}
    (rim : F.preparedGraph.Walk (.inl r₀) (.inl r₀))
    (hcycle : rim.IsCycle)
    (hxrim : (.inl x : F.PreparedVertex) ∉ rim.support)
    (hthree : 3 ≤ (F.preparedGraph.neighborFinset (.inl x) ∩
      rim.support.toFinset).card)
    (havoid : ∀ i : F.FreshPin, (.inr i : F.PreparedVertex) ∉ rim.support) :
    HasWheelCenteredAt G x.1 := by
  classical
  have hold : ∀ z ∈ rim.support, ∃ r : F.BaseVertex, z = .inl r := by
    intro z hz
    rcases z with r | i
    · exact ⟨r, rfl⟩
    · exact (havoid i hz).elim
  obtain ⟨q, hqMap⟩ :=
    F.exists_preparedOldWalk_of_support_avoids_fresh rim hold
  have hqCycle : q.IsCycle := by
    apply SimpleGraph.Walk.IsCycle.of_map
    rw [hqMap]
    exact hcycle
  have hqrim (y : F.BaseVertex) :
      (.inl y : F.PreparedVertex) ∈ rim.support ↔ y ∈ q.support := by
    rw [← hqMap]
    change (.inl y : F.PreparedVertex) ∈
      (q.map F.preparedOldInclusion).support ↔ _
    rw [SimpleGraph.Walk.support_map]
    simp
  have hxq : x ∉ q.support := by
    intro hx
    exact hxrim ((hqrim x).2 hx)
  let e : F.BaseVertex ↪ F.PreparedVertex := Function.Embedding.inl
  have hfin :
      F.preparedGraph.neighborFinset (.inl x) ∩ rim.support.toFinset =
        (F.preparedOldGraph.neighborFinset x ∩ q.support.toFinset).map e := by
    ext z
    rcases z with y | i
    · simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
        List.mem_toFinset, hqrim, Finset.mem_map, e]
      constructor
      · rintro ⟨hxy, hyq⟩
        exact ⟨y, ⟨hxy, hyq⟩, rfl⟩
      · rintro ⟨z, ⟨hxz, hzq⟩, hz⟩
        have hzy : z = y := Sum.inl_injective hz
        subst z
        exact ⟨hxz, hzq⟩
    · simp [SimpleGraph.mem_neighborFinset, havoid i, e, preparedOldGraph]
  have hthreeOld : 3 ≤
      (F.preparedOldGraph.neighborFinset x ∩ q.support.toFinset).card := by
    rw [hfin, Finset.card_map] at hthree
    exact hthree
  have hwOld : HasWheelCenteredAt F.preparedOldGraph x :=
    ⟨r₀, q, hqCycle, hxq, hthreeOld⟩
  exact hwOld.mapHomOfInjective F.preparedOldToAmbient
    F.preparedOldToAmbient_injective

/-- The distinguished source pin `a'`, `b'`, or `c'`: use a fresh pendant
vertex in the high-inside-degree case and the boundary vertex itself in the
one-neighbour case. -/
def pin (i : Fin 3) : F.PreparedVertex :=
  if h : F.NeedsFreshPin i then .inr ⟨i, h⟩
  else .inl ⟨F.boundaryVertex i, by
    fin_cases i <;> simp [boundaryVertex]⟩

/-- The graph denoted `G_F` in AHT Lemma 6.4. -/
def replacementGraph : SimpleGraph (F.PreparedVertex ⊕ Fin 2) :=
  ahtDoublePinReplacement F.preparedGraph (F.pin 0) (F.pin 1) (F.pin 2)

instance replacementGraph.instDecidableRel : DecidableRel F.replacementGraph.Adj := by
  unfold replacementGraph
  infer_instance

theorem boundary_not_mem (i : Fin 3) : F.boundaryVertex i ∉ F.verts := by
  have hd := Finset.disjoint_left.1 F.boundary_disjoint
  fin_cases i <;> intro h <;> apply hd h <;> simp

theorem boundary_mem_base (i : Fin 3) :
    F.boundaryVertex i ∈ F.verts ∪ ({F.a, F.b, F.c} : Finset V) := by
  fin_cases i <;> simp

theorem boundaryVertex_injective : Function.Injective F.boundaryVertex := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [F.ab, F.ac, F.bc]
  · exact (F.ab hij.symm).elim
  · exact (F.ac hij.symm).elim
  · exact (F.bc hij.symm).elim

/-- Every boundary vertex has a neighbour on the exterior side of the
fragment.  Otherwise the other two boundary vertices form a proper
separation of order two: the strict fragment side is `F ∪ {boundary i}` and
the strict exterior side is the nonempty complement. -/
theorem exists_boundary_neighbor_outside
    (hthree : IsThreeConnected G) (i : Fin 3) :
    ∃ x ∈ Finset.univ \ (F.verts ∪ F.boundaryFinset),
      G.Adj (F.boundaryVertex i) x := by
  classical
  by_contra hex
  have hno (x : V)
      (hx : x ∈ Finset.univ \ (F.verts ∪ F.boundaryFinset)) :
      ¬G.Adj (F.boundaryVertex i) x := by
    intro hadj
    exact hex ⟨x, hx, hadj⟩
  let C : Finset V := F.verts ∪ F.boundaryFinset
  let O : Finset V := Finset.univ \ C
  let B : Finset V := F.otherBoundaryFinset i
  let s : AHTSeparation G :=
    { left := C
      right := O ∪ B
      cover := by
        apply Finset.eq_univ_iff_forall.2
        intro x
        by_cases hx : x ∈ C
        · exact Finset.mem_union_left _ hx
        · apply Finset.mem_union_right C
          apply Finset.mem_union_left B
          exact Finset.mem_sdiff.2 ⟨Finset.mem_univ x, hx⟩
      not_adj := by
        intro u v huC huRight hvRight hvC huv
        have hvO : v ∈ O := by
          rcases Finset.mem_union.mp hvRight with hvO | hvB
          · exact hvO
          · exact (hvC (F.otherBoundaryFinset_subset_boundaryFinset i hvB
              |> Finset.mem_union_right F.verts)).elim
        rcases Finset.mem_union.mp huC with huF | huBoundary
        · have hvNotF : v ∉ F.verts := by
            intro hvF
            exact hvC (Finset.mem_union_left _ hvF)
          have hvBoundary :
              v = F.a ∨ v = F.b ∨ v = F.c :=
            (F.boundary_exact v hvNotF).1 ⟨u, huF, huv.symm⟩
          apply hvC
          apply Finset.mem_union_right F.verts
          simpa [boundaryFinset] using hvBoundary
        · have huNotB : u ∉ B := by
            intro huB
            exact huRight (Finset.mem_union_right O huB)
          have hui : u = F.boundaryVertex i := by
            have huNeOrEq := eq_or_ne u (F.boundaryVertex i)
            rcases huNeOrEq with hui | hui
            · exact hui
            · exact (huNotB (by
                simpa [B, otherBoundaryFinset, hui] using huBoundary)).elim
          subst u
          exact hno v (by simpa [O, C] using hvO) huv }
  have hproper : s.Proper := by
    constructor
    · refine ⟨F.boundaryVertex i, Finset.mem_sdiff.2 ⟨?_, ?_⟩⟩
      · apply Finset.mem_union_right F.verts
        exact F.boundaryVertex_mem_boundaryFinset i
      · intro hiRight
        rcases Finset.mem_union.mp hiRight with hiO | hiB
        · exact (Finset.mem_sdiff.1 hiO).2
            (Finset.mem_union_right F.verts
              (F.boundaryVertex_mem_boundaryFinset i))
        · exact F.boundaryVertex_not_mem_otherBoundaryFinset i hiB
    · obtain ⟨o, ho⟩ := F.outside_nonempty
      have hoO : o ∈ O := by
        simpa [O, C, boundaryFinset] using ho
      refine ⟨o, Finset.mem_sdiff.2 ⟨Finset.mem_union_left B hoO, ?_⟩⟩
      exact (Finset.mem_sdiff.1 hoO).2
  have hsep : s.separator = B := by
    ext x
    simp only [AHTSeparation.separator, s, Finset.mem_inter,
      Finset.mem_union]
    constructor
    · rintro ⟨hxC, hxO | hxB⟩
      · exact ((Finset.mem_sdiff.1 hxO).2 hxC).elim
      · exact hxB
    · intro hxB
      exact ⟨F.otherBoundaryFinset_subset_boundaryFinset i hxB
        |> Finset.mem_union_right F.verts, Or.inr hxB⟩
  have horder : s.order = 2 := by
    rw [AHTSeparation.order, hsep, F.otherBoundaryFinset_card]
  have hs := hthree.2 s hproper
  rw [horder] at hs
  omega

/-- Delete one boundary vertex `i`.  An exterior neighbour of `i` then lies
on a simple path between the other two boundary vertices.  This is exactly
the two-fan used in the boundary-centre case of AHT Lemma 6.4.  The final
support clause records that no third boundary vertex occurs on the path;
combined with `boundary_exact`, it is the input for proving that the path's
interior lies on the exterior side of the fragment. -/
theorem exists_otherBoundary_path_through_exterior_neighbor
    (hthree : IsThreeConnected G) (i j k : Fin 3)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hcover : ∀ l : Fin 3, l = i ∨ l = j ∨ l = k) :
    ∃ x ∈ Finset.univ \ (F.verts ∪ F.boundaryFinset),
      G.Adj (F.boundaryVertex i) x ∧
      ∃ p : G.Walk (F.boundaryVertex j) (F.boundaryVertex k),
        p.IsPath ∧ x ∈ p.support ∧
        F.boundaryVertex i ∉ p.support ∧
        ∀ l : Fin 3, F.boundaryVertex l ∈ p.support →
          l = j ∨ l = k := by
  classical
  obtain ⟨x, hxOutside, hix⟩ :=
    F.exists_boundary_neighbor_outside hthree i
  have hxi : x ≠ F.boundaryVertex i := by
    intro hxi
    subst x
    exact (Finset.mem_sdiff.1 hxOutside).2
      (Finset.mem_union_right F.verts
        (F.boundaryVertex_mem_boundaryFinset i))
  have hji : F.boundaryVertex j ≠ F.boundaryVertex i :=
    F.boundaryVertex_injective.ne hij.symm
  have hki : F.boundaryVertex k ≠ F.boundaryVertex i :=
    F.boundaryVertex_injective.ne hik.symm
  have hjx : F.boundaryVertex j ≠ x := by
    intro hjx
    subst x
    exact (Finset.mem_sdiff.1 hxOutside).2
      (Finset.mem_union_right F.verts
        (F.boundaryVertex_mem_boundaryFinset j))
  have hkx : F.boundaryVertex k ≠ x := by
    intro hkx
    subst x
    exact (Finset.mem_sdiff.1 hxOutside).2
      (Finset.mem_union_right F.verts
        (F.boundaryVertex_mem_boundaryFinset k))
  have hjkV : F.boundaryVertex j ≠ F.boundaryVertex k :=
    F.boundaryVertex_injective.ne hjk
  let H := G.induce fun v : V ↦ v ≠ F.boundaryVertex i
  let jH : {v : V // v ≠ F.boundaryVertex i} :=
    ⟨F.boundaryVertex j, hji⟩
  let kH : {v : V // v ≠ F.boundaryVertex i} :=
    ⟨F.boundaryVertex k, hki⟩
  let xH : {v : V // v ≠ F.boundaryVertex i} := ⟨x, hxi⟩
  obtain ⟨hconn, hdelete⟩ :=
    vertexTwoConnected_delete_of_isThreeConnected hthree
      (F.boundaryVertex i)
  obtain ⟨q, hq, hxq⟩ := exists_rooted_three_path
    (G := H) (r := jH) (a := xH) (b := kH)
      (by exact fun h ↦ hjx (congrArg Subtype.val h))
      (by exact fun h ↦ hjkV (congrArg Subtype.val h))
      (by exact fun h ↦ hkx (congrArg Subtype.val h).symm)
      hconn hdelete
  let inc : H →g G :=
    { toFun := Subtype.val
      map_rel' := by intro u v huv; exact huv }
  let p : G.Walk (F.boundaryVertex j) (F.boundaryVertex k) := q.map inc
  have hp : p.IsPath := hq.map Subtype.val_injective
  have hxp : x ∈ p.support := by
    change x ∈ (q.map inc).support
    rw [SimpleGraph.Walk.support_map]
    exact List.mem_map.mpr ⟨xH, hxq, rfl⟩
  have hip : F.boundaryVertex i ∉ p.support := by
    intro hi
    change F.boundaryVertex i ∈ (q.map inc).support at hi
    rw [SimpleGraph.Walk.support_map] at hi
    obtain ⟨z, -, hz⟩ := List.mem_map.mp hi
    exact z.2 hz
  refine ⟨x, hxOutside, hix, p, hp, hxp, hip, ?_⟩
  intro l hl
  rcases hcover l with rfl | rfl | rfl
  · exact (hip hl).elim
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- Every walk which starts in the fragment and ends outside it meets one of
the three boundary vertices.  This elementary first-exit statement is used
twice in the wheel transfer: once to keep the ambient replacement path on
the exterior side, and once to trim the prepared rim path to the fragment
side. -/
theorem walk_meets_boundary_of_start_mem_end_not_mem
    {u v : V} (p : G.Walk u v) (hu : u ∈ F.verts) (hv : v ∉ F.verts) :
    ∃ i : Fin 3, F.boundaryVertex i ∈ p.support := by
  induction p with
  | nil => exact (hv hu).elim
  | @cons u w v huw p ih =>
      by_cases hwF : w ∈ F.verts
      · obtain ⟨i, hi⟩ := ih hwF hv
        exact ⟨i, by simp [hi]⟩
      · have hwBoundary : w = F.a ∨ w = F.b ∨ w = F.c :=
          (F.boundary_exact w hwF).1 ⟨u, hu, huw.symm⟩
        rcases hwBoundary with rfl | rfl | rfl
        · exact ⟨0, by simp⟩
        · exact ⟨1, by simp⟩
        · exact ⟨2, by simp⟩

/-- Reversed first-exit form. -/
theorem walk_meets_boundary_of_start_not_mem_end_mem
    {u v : V} (p : G.Walk u v) (hu : u ∉ F.verts) (hv : v ∈ F.verts) :
    ∃ i : Fin 3, F.boundaryVertex i ∈ p.support := by
  simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using
    F.walk_meets_boundary_of_start_mem_end_not_mem p.reverse hv hu

/-- If `q` is the unique fragment neighbour of the `i`th boundary vertex,
then a walk from the fragment to that boundary which avoids `q` must first
leave through one of the other two boundary vertices.  This is the
first-exit input needed when the singleton pin in a two-new-vertex rim is
itself a spoke of an interior centre. -/
theorem walk_meets_other_boundary_of_start_mem_end_boundary
    (i : Fin 3) (q : V) (hqInside : q ∈ F.insideNeighborFinset i)
    (hunique : (F.insideNeighborFinset i).card = 1)
    {u : V} (p : G.Walk u (F.boundaryVertex i))
    (hu : u ∈ F.verts) (hqAvoid : q ∉ p.support) :
    ∃ l : Fin 3, l ≠ i ∧ F.boundaryVertex l ∈ p.support := by
  generalize hv : F.boundaryVertex i = v at p
  induction p with
  | nil =>
      exact (F.boundary_not_mem i (by simpa only [hv] using hu)).elim
  | @cons u w v huw p ih =>
      by_cases hwF : w ∈ F.verts
      · obtain ⟨l, hli, hl⟩ := ih hwF hv (by
          intro hq
          exact hqAvoid (by simp [hq]))
        exact ⟨l, hli, by
          simp only [SimpleGraph.Walk.support_cons, List.mem_cons]
          exact Or.inr hl⟩
      · have hwBoundary : w = F.a ∨ w = F.b ∨ w = F.c :=
          (F.boundary_exact w hwF).1 ⟨u, hu, huw.symm⟩
        obtain ⟨l, hwl⟩ : ∃ l : Fin 3, w = F.boundaryVertex l := by
          rcases hwBoundary with rfl | rfl | rfl
          · exact ⟨0, rfl⟩
          · exact ⟨1, rfl⟩
          · exact ⟨2, rfl⟩
        have hli : l ≠ i := by
          intro hli
          subst l
          have huInside : u ∈ F.insideNeighborFinset i := by
            simp only [insideNeighborFinset, Finset.mem_inter,
              SimpleGraph.mem_neighborFinset]
            exact ⟨by simpa only [hwl] using huw.symm, hu⟩
          obtain ⟨r, hr⟩ := Finset.card_eq_one.mp hunique
          have hur : u = r := by simpa [hr] using huInside
          have hqr : q = r := by simpa [hr] using hqInside
          have huq : u = q := hur.trans hqr.symm
          exact hqAvoid (by simp [huq])
        exact ⟨l, hli, by
          simp only [SimpleGraph.Walk.support_cons, List.mem_cons]
          exact Or.inr (by simpa only [hwl] using p.start_mem_support)⟩

/-- Delete the prospective interior wheel centre.  If it is the unique
fragment neighbour of boundary `i`, two-connectivity of the deletion gives
a path from the other two boundary vertices through `i`.  The strengthened
first-exit lemma above shows that the whole path lies outside the fragment.
This is the exterior splice for the sole exceptional two-artificial-pin
wheel configuration. -/
theorem exists_otherBoundary_exterior_path_through_boundary_avoiding_center
    (hthree : IsThreeConnected G) (i j k : Fin 3)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hcover : ∀ l : Fin 3, l = i ∨ l = j ∨ l = k)
    (q : V) (hqF : q ∈ F.verts)
    (hqInside : q ∈ F.insideNeighborFinset i)
    (hunique : (F.insideNeighborFinset i).card = 1) :
    ∃ p : G.Walk (F.boundaryVertex j) (F.boundaryVertex k),
      p.IsPath ∧ F.boundaryVertex i ∈ p.support ∧ q ∉ p.support ∧
        (∀ l : Fin 3, F.boundaryVertex l ∈ p.support →
          l = i ∨ l = j ∨ l = k) ∧
        ∀ y ∈ p.support, y ∉ F.verts := by
  classical
  have hqi : q ≠ F.boundaryVertex i := by
    intro h
    subst q
    exact F.boundary_not_mem i hqF
  have hqj : q ≠ F.boundaryVertex j := by
    intro h
    subst q
    exact F.boundary_not_mem j hqF
  have hqk : q ≠ F.boundaryVertex k := by
    intro h
    subst q
    exact F.boundary_not_mem k hqF
  have hjiV : F.boundaryVertex j ≠ F.boundaryVertex i :=
    F.boundaryVertex_injective.ne hij.symm
  have hjkV : F.boundaryVertex j ≠ F.boundaryVertex k :=
    F.boundaryVertex_injective.ne hjk
  have hikV : F.boundaryVertex i ≠ F.boundaryVertex k :=
    F.boundaryVertex_injective.ne hik
  let H := G.induce fun v : V ↦ v ≠ q
  let jH : {v : V // v ≠ q} := ⟨F.boundaryVertex j, hqj.symm⟩
  let iH : {v : V // v ≠ q} := ⟨F.boundaryVertex i, hqi.symm⟩
  let kH : {v : V // v ≠ q} := ⟨F.boundaryVertex k, hqk.symm⟩
  obtain ⟨hconn, hdelete⟩ :=
    vertexTwoConnected_delete_of_isThreeConnected hthree q
  obtain ⟨r, hr, hir⟩ := exists_rooted_three_path
    (G := H) (r := jH) (a := iH) (b := kH)
      (by exact fun h ↦ hjiV (congrArg Subtype.val h))
      (by exact fun h ↦ hjkV (congrArg Subtype.val h))
      (by exact fun h ↦ hikV (congrArg Subtype.val h))
      hconn hdelete
  let inc : H →g G :=
    { toFun := Subtype.val
      map_rel' := by intro u v huv; exact huv }
  let p : G.Walk (F.boundaryVertex j) (F.boundaryVertex k) := r.map inc
  have hp : p.IsPath := hr.map Subtype.val_injective
  have hip : F.boundaryVertex i ∈ p.support := by
    change F.boundaryVertex i ∈ (r.map inc).support
    rw [SimpleGraph.Walk.support_map]
    exact List.mem_map.mpr ⟨iH, hir, rfl⟩
  have hqp : q ∉ p.support := by
    intro hq
    change q ∈ (r.map inc).support at hq
    rw [SimpleGraph.Walk.support_map] at hq
    obtain ⟨z, -, hz⟩ := List.mem_map.mp hq
    exact z.2 hz
  have hboundary : ∀ l : Fin 3, F.boundaryVertex l ∈ p.support →
      l = i ∨ l = j ∨ l = k := by
    intro l _
    exact hcover l
  let left := p.takeUntil (F.boundaryVertex i) hip
  let right := p.dropUntil (F.boundaryVertex i) hip
  have hleftPath : left.IsPath := hp.takeUntil hip
  have hrightPath : right.IsPath := hp.dropUntil hip
  have hsplitNodup : (left.support ++ right.support.tail).Nodup := by
    simpa only [left, right, ← SimpleGraph.Walk.support_append,
      p.take_spec hip] using hp.support_nodup
  have hjLeft : F.boundaryVertex j ∈ left.support := left.start_mem_support
  have hkRight : F.boundaryVertex k ∈ right.support.tail := by
    exact right.end_mem_tail_support
      (SimpleGraph.Walk.not_nil_of_ne hikV)
  refine ⟨p, hp, hip, hqp, hboundary, ?_⟩
  intro y hyp hyF
  have hyParts : y ∈ left.support ∨ y ∈ right.support.tail := by
    have : y ∈ (left.append right).support := by
      rw [p.take_spec hip]
      exact hyp
    simpa only [SimpleGraph.Walk.support_append, List.mem_append] using this
  rcases hyParts with hyLeft | hyRightTail
  · let s := left.dropUntil y hyLeft
    have hqAvoidS : q ∉ s.support := by
      intro hq
      exact hqp (p.support_takeUntil_subset_support hip
        (left.support_dropUntil_subset_support hyLeft hq))
    obtain ⟨l, hli, hls⟩ :=
      F.walk_meets_other_boundary_of_start_mem_end_boundary
        i q hqInside hunique s hyF hqAvoidS
    have hlLeft : F.boundaryVertex l ∈ left.support :=
      left.support_dropUntil_subset_support hyLeft hls
    have hlp : F.boundaryVertex l ∈ p.support :=
      p.support_takeUntil_subset_support hip hlLeft
    rcases hboundary l hlp with hli' | hlj | hlk
    · exact (hli hli').elim
    · subst l
      have hjy : F.boundaryVertex j ≠ y := by
        intro hjy
        subst y
        exact F.boundary_not_mem j hyF
      have hyi : y ≠ F.boundaryVertex i := by
        intro hyi
        subst y
        exact F.boundary_not_mem i hyF
      have hsNot : ¬s.Nil := SimpleGraph.Walk.not_nil_of_ne hyi
      have hjTail : F.boundaryVertex j ∈ s.support.tail := by
        rw [← s.cons_support_tail hsNot] at hls
        have : F.boundaryVertex j ∈ s.tail.support :=
          (List.mem_cons.mp hls).resolve_left hjy
        simpa only [s.support_tail_of_not_nil hsNot] using this
      have hleftSplit :
          ((left.takeUntil y hyLeft).support ++ s.support.tail).Nodup := by
        simpa only [s, ← SimpleGraph.Walk.support_append,
          left.take_spec hyLeft] using hleftPath.support_nodup
      exact ((List.nodup_append.mp hleftSplit).2.2 _
        (left.takeUntil y hyLeft).start_mem_support _ hjTail) rfl
    · subst l
      have hkNotLeft : F.boundaryVertex k ∉ left.support :=
        SimpleGraph.Walk.endpoint_notMem_support_takeUntil hp hip hikV.symm
      exact hkNotLeft hlLeft
  · have hyRight : y ∈ right.support := List.mem_of_mem_tail hyRightTail
    let s := right.takeUntil y hyRight
    have hqAvoidS : q ∉ s.reverse.support := by
      intro hq
      have hqs : q ∈ s.support := by
        simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using hq
      exact hqp (p.support_dropUntil_subset_support hip
        (right.support_takeUntil_subset_support hyRight hqs))
    obtain ⟨l, hli, hls⟩ :=
      F.walk_meets_other_boundary_of_start_mem_end_boundary
        i q hqInside hunique s.reverse hyF hqAvoidS
    have hls' : F.boundaryVertex l ∈ s.support := by
      simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using hls
    have hlRight : F.boundaryVertex l ∈ right.support :=
      right.support_takeUntil_subset_support hyRight hls'
    have hlp : F.boundaryVertex l ∈ p.support :=
      p.support_dropUntil_subset_support hip hlRight
    rcases hboundary l hlp with hli' | hlj | hlk
    · exact (hli hli').elim
    · subst l
      have hjRightTail : F.boundaryVertex j ∈ right.support.tail := by
        rw [← right.cons_support_tail
          (SimpleGraph.Walk.not_nil_of_ne hikV)] at hlRight
        have : F.boundaryVertex j ∈ right.tail.support :=
          (List.mem_cons.mp hlRight).resolve_left hjiV
        simpa only [right.support_tail_of_not_nil
          (SimpleGraph.Walk.not_nil_of_ne hikV)] using this
      exact ((List.nodup_append.mp hsplitNodup).2.2 _ hjLeft _
        hjRightTail) rfl
    · subst l
      have hky : F.boundaryVertex k ≠ y := by
        intro hky
        subst y
        exact F.boundary_not_mem k hyF
      have hkNotS : F.boundaryVertex k ∉ s.support :=
        SimpleGraph.Walk.endpoint_notMem_support_takeUntil
          hrightPath hyRight hky
      exact hkNotS hls'

/-- Exterior form of the two-fan lemma.  The rooted path supplied above
cannot enter the fragment: on either side of its displayed exterior vertex,
a first entrance into `F` would force an additional boundary occurrence.
Path simplicity rules out reusing the corresponding endpoint, while the
third boundary is explicitly avoided. -/
theorem exists_otherBoundary_exterior_path_through_neighbor
    (hthree : IsThreeConnected G) (i j k : Fin 3)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hcover : ∀ l : Fin 3, l = i ∨ l = j ∨ l = k) :
    ∃ x ∈ Finset.univ \ (F.verts ∪ F.boundaryFinset),
      G.Adj (F.boundaryVertex i) x ∧
      ∃ p : G.Walk (F.boundaryVertex j) (F.boundaryVertex k),
        p.IsPath ∧ x ∈ p.support ∧
        F.boundaryVertex i ∉ p.support ∧
        (∀ l : Fin 3, F.boundaryVertex l ∈ p.support →
          l = j ∨ l = k) ∧
        ∀ y ∈ p.support, y ∉ F.verts := by
  classical
  obtain ⟨x, hxOutside, hix, p, hp, hxp, hip, hboundary⟩ :=
    F.exists_otherBoundary_path_through_exterior_neighbor
      hthree i j k hij hik hjk hcover
  have hxF : x ∉ F.verts := by
    intro hx
    exact (Finset.mem_sdiff.1 hxOutside).2 (Finset.mem_union_left _ hx)
  have hxj : x ≠ F.boundaryVertex j := by
    intro hx
    subst x
    exact (Finset.mem_sdiff.1 hxOutside).2
      (Finset.mem_union_right F.verts
        (F.boundaryVertex_mem_boundaryFinset j))
  have hxk : x ≠ F.boundaryVertex k := by
    intro hx
    subst x
    exact (Finset.mem_sdiff.1 hxOutside).2
      (Finset.mem_union_right F.verts
        (F.boundaryVertex_mem_boundaryFinset k))
  let left := p.takeUntil x hxp
  let right := p.dropUntil x hxp
  have hleftPath : left.IsPath := hp.takeUntil hxp
  have hrightPath : right.IsPath := hp.dropUntil hxp
  have hsplitNodup : (left.support ++ right.support.tail).Nodup := by
    simpa only [left, right, ← SimpleGraph.Walk.support_append,
      p.take_spec hxp] using hp.support_nodup
  have hjLeft : F.boundaryVertex j ∈ left.support := left.start_mem_support
  have hkRight : F.boundaryVertex k ∈ right.support.tail := by
    exact right.end_mem_tail_support
      (SimpleGraph.Walk.not_nil_of_ne hxk)
  refine ⟨x, hxOutside, hix, p, hp, hxp, hip, hboundary, ?_⟩
  intro y hyp hyF
  have hyx : y ≠ x := by
    intro hyx
    subst y
    exact hxF hyF
  have hyParts : y ∈ left.support ∨ y ∈ right.support.tail := by
    have : y ∈ (left.append right).support := by
      rw [p.take_spec hxp]
      exact hyp
    simpa only [SimpleGraph.Walk.support_append, List.mem_append] using this
  rcases hyParts with hyLeft | hyRightTail
  · let q := left.dropUntil y hyLeft
    have hqNot : ¬q.Nil :=
      SimpleGraph.Walk.not_nil_of_ne hyx
    obtain ⟨l, hlq⟩ :=
      F.walk_meets_boundary_of_start_mem_end_not_mem q hyF hxF
    have hlLeft : F.boundaryVertex l ∈ left.support :=
      left.support_dropUntil_subset_support hyLeft hlq
    have hlp : F.boundaryVertex l ∈ p.support :=
      p.support_takeUntil_subset_support hxp hlLeft
    rcases hboundary l hlp with hlj | hlk
    · subst l
      have hjy : F.boundaryVertex j ≠ y := by
        intro hjy
        subst y
        exact F.boundary_not_mem j hyF
      have hjTail : F.boundaryVertex j ∈ q.support.tail := by
        rw [← q.cons_support_tail hqNot] at hlq
        have : F.boundaryVertex j ∈ q.tail.support :=
          (List.mem_cons.mp hlq).resolve_left hjy
        simpa only [q.support_tail_of_not_nil hqNot] using this
      have hleftSplit :
          ((left.takeUntil y hyLeft).support ++ q.support.tail).Nodup := by
        simpa only [q, ← SimpleGraph.Walk.support_append,
          left.take_spec hyLeft] using hleftPath.support_nodup
      exact ((List.nodup_append.mp hleftSplit).2.2 _
        (left.takeUntil y hyLeft).start_mem_support _ hjTail) rfl
    · subst l
      have hkNotLeft : F.boundaryVertex k ∉ left.support :=
        SimpleGraph.Walk.endpoint_notMem_support_takeUntil hp hxp hxk.symm
      exact hkNotLeft hlLeft
  · have hyRight : y ∈ right.support :=
      List.mem_of_mem_tail hyRightTail
    let q := right.takeUntil y hyRight
    obtain ⟨l, hlq⟩ :=
      F.walk_meets_boundary_of_start_not_mem_end_mem q hxF hyF
    have hlRight : F.boundaryVertex l ∈ right.support :=
      right.support_takeUntil_subset_support hyRight hlq
    have hlp : F.boundaryVertex l ∈ p.support :=
      p.support_dropUntil_subset_support hxp hlRight
    rcases hboundary l hlp with hlj | hlk
    · subst l
      have hjRightTail : F.boundaryVertex j ∈ right.support.tail := by
        rw [← right.cons_support_tail
          (SimpleGraph.Walk.not_nil_of_ne hxk)] at hlRight
        have : F.boundaryVertex j ∈ right.tail.support :=
          (List.mem_cons.mp hlRight).resolve_left hxj.symm
        simpa only [right.support_tail_of_not_nil
          (SimpleGraph.Walk.not_nil_of_ne hxk)] using this
      exact ((List.nodup_append.mp hsplitNodup).2.2 _ hjLeft _
        hjRightTail) rfl
    · subst l
      have hky : F.boundaryVertex k ≠ y := by
        intro hky
        subst y
        exact F.boundary_not_mem k hyF
      have hkNotQ : F.boundaryVertex k ∉ q.support :=
        SimpleGraph.Walk.endpoint_notMem_support_takeUntil
          hrightPath hyRight hky
      exact hkNotQ hlq

/-- Three-connectivity forces no additional hypothesis here: the exact
boundary equation already says each displayed boundary vertex has an inside
neighbour. -/
theorem insideNeighborFinset_nonempty (i : Fin 3) :
    (F.insideNeighborFinset i).Nonempty := by
  have h := (F.boundary_exact (F.boundaryVertex i) (F.boundary_not_mem i)).2
  have hi : F.boundaryVertex i = F.a ∨ F.boundaryVertex i = F.b ∨
      F.boundaryVertex i = F.c := by
    fin_cases i <;> simp
  obtain ⟨y, hyF, hxy⟩ := h hi
  exact ⟨y, by simp [insideNeighborFinset, hyF, hxy]⟩

theorem insideNeighborFinset_card_pos (i : Fin 3) :
    0 < (F.insideNeighborFinset i).card :=
  Finset.card_pos.mpr (F.insideNeighborFinset_nonempty i)

/-- In the branch where no fresh pin is introduced, the boundary vertex has
exactly one neighbour in the fragment. -/
theorem insideNeighborFinset_card_eq_one_of_not_needsFreshPin
    (i : Fin 3) (hi : ¬F.NeedsFreshPin i) :
    (F.insideNeighborFinset i).card = 1 := by
  have hpos := F.insideNeighborFinset_card_pos i
  change ¬2 ≤ (F.insideNeighborFinset i).card at hi
  omega

/-- If a high-inside-degree boundary vertex itself belongs to a set of fewer
than three ambient shadows, some inside neighbour avoids that set.  This is
the small counting step used when the fresh pin at that boundary was one of
the deleted replacement vertices. -/
theorem exists_insideNeighbor_not_mem {D : Finset V} (i : Fin 3)
    (hi : F.NeedsFreshPin i) (hiD : F.boundaryVertex i ∈ D)
    (hD : D.card < 3) :
    ∃ y ∈ F.insideNeighborFinset i, y ∉ D := by
  by_contra h
  push_neg at h
  have hboundaryNotInside :
      F.boundaryVertex i ∉ F.insideNeighborFinset i := by
    simp [insideNeighborFinset, SimpleGraph.mem_neighborFinset]
  have hsub : insert (F.boundaryVertex i) (F.insideNeighborFinset i) ⊆ D := by
    intro y hy
    rw [Finset.mem_insert] at hy
    rcases hy with rfl | hy
    · exact hiD
    · exact h y hy
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hboundaryNotInside] at hcard
  change 2 ≤ (F.insideNeighborFinset i).card at hi
  omega

/-- Ambient shadow of a prepared vertex.  Both an identified boundary pin
and its possible fresh replacement shadow the same ambient boundary vertex. -/
def preparedShadow : F.PreparedVertex → V
  | .inl q => q.1
  | .inr i => F.boundaryVertex i.1

@[simp] theorem preparedShadow_old (q : F.BaseVertex) :
    F.preparedShadow (.inl q) = q.1 := rfl

@[simp] theorem preparedShadow_fresh (i : F.FreshPin) :
    F.preparedShadow (.inr i) = F.boundaryVertex i.1 := rfl

@[simp] theorem preparedShadow_pin (i : Fin 3) :
    F.preparedShadow (F.pin i) = F.boundaryVertex i := by
  by_cases hi : F.NeedsFreshPin i <;> simp [pin, hi]

/-- Ambient shadow set of a finite collection of deleted prepared vertices. -/
def preparedDeletionShadow (E : Finset F.PreparedVertex) : Finset V :=
  E.image F.preparedShadow

theorem preparedDeletionShadow_card_le (E : Finset F.PreparedVertex) :
    (F.preparedDeletionShadow E).card ≤ E.card := by
  exact Finset.card_image_le

theorem preparedDeletionShadow_subset_fragment_boundary
    (E : Finset F.PreparedVertex) :
    F.preparedDeletionShadow E ⊆
      F.verts ∪ ({F.a, F.b, F.c} : Finset V) := by
  intro v hv
  obtain ⟨z, hzE, rfl⟩ := Finset.mem_image.1 hv
  rcases z with q | i
  · exact q.2
  · exact F.boundary_mem_base i.1

theorem boundary_mem_preparedDeletionShadow_of_pin_mem
    {E : Finset F.PreparedVertex} {i : Fin 3} (hi : F.pin i ∈ E) :
    F.boundaryVertex i ∈ F.preparedDeletionShadow E := by
  exact Finset.mem_image.2 ⟨F.pin i, hi, F.preparedShadow_pin i⟩

theorem not_mem_preparedDeletion_of_shadow_not_mem
    {E : Finset F.PreparedVertex} {z : F.PreparedVertex}
    (hz : F.preparedShadow z ∉ F.preparedDeletionShadow E) : z ∉ E := by
  intro hzE
  exact hz (Finset.mem_image.2 ⟨z, hzE, rfl⟩)

/-- An undeleted inside vertex is not accidentally shadowed by a deleted
fresh pin: fragment vertices and boundary vertices are disjoint. -/
theorem inside_shadow_not_mem_of_old_not_mem
    {E : Finset F.PreparedVertex} {p : V} (hpF : p ∈ F.verts)
    (hpE : (.inl ⟨p, Finset.mem_union_left _ hpF⟩ : F.PreparedVertex) ∉ E) :
    p ∉ F.preparedDeletionShadow E := by
  intro hp
  obtain ⟨z, hzE, hz⟩ := Finset.mem_image.1 hp
  rcases z with q | i
  · have hq : q = ⟨p, Finset.mem_union_left _ hpF⟩ :=
      Subtype.ext hz
    exact hpE (hq ▸ hzE)
  · have hpBoundary : p = F.boundaryVertex i.1 := hz.symm
    exact F.boundary_not_mem i.1 (hpBoundary ▸ hpF)

/-- The rerouting kernel of the connectivity proof in AHT Lemma 6.4.
Follow an ambient walk from an inside vertex until it first leaves the
fragment.  Exactness of the boundary identifies that first outside vertex
with one of `a,b,c`; the corresponding walk inside the prepared graph ends
at its pin.  If the ambient walk avoids `D`, then so does the selected
boundary vertex. -/
theorem walk_inside_to_surviving_pin {D : Finset V} {u v : V}
    (p : G.Walk u v) (hu : u ∈ F.verts) (hv : v ∉ F.verts)
    (havoid : ∀ z ∈ p.support, z ∉ D) :
    ∃ i : Fin 3, F.boundaryVertex i ∉ D ∧
      F.preparedGraph.Reachable
        (.inl ⟨u, Finset.mem_union_left _ hu⟩)
        (F.pin i) := by
  induction p with
  | nil => exact (hv hu).elim
  | @cons u w v huw p ih =>
      by_cases hwF : w ∈ F.verts
      · have havoidTail : ∀ z ∈ p.support, z ∉ D := by
          intro z hz
          exact havoid z (by simp [hz])
        obtain ⟨i, hiD, hreach⟩ := ih hwF hv havoidTail
        have huNotB : u ∉ ({F.a, F.b, F.c} : Finset V) :=
          Finset.disjoint_left.1 F.boundary_disjoint hu
        have huwP : F.preparedGraph.Adj
            (.inl ⟨u, Finset.mem_union_left _ hu⟩)
            (.inl ⟨w, Finset.mem_union_left _ hwF⟩) := by
          exact ⟨huw, fun hbad ↦ huNotB hbad.1⟩
        exact ⟨i, hiD, huwP.reachable.trans hreach⟩
      · have hwBoundary :
            w = F.a ∨ w = F.b ∨ w = F.c :=
          (F.boundary_exact w hwF).1 ⟨u, hu, huw.symm⟩
        obtain ⟨i, rfl⟩ : ∃ i : Fin 3, w = F.boundaryVertex i := by
          rcases hwBoundary with rfl | rfl | rfl
          · exact ⟨0, rfl⟩
          · exact ⟨1, rfl⟩
          · exact ⟨2, rfl⟩
        have hiD : F.boundaryVertex i ∉ D := by
          apply havoid (F.boundaryVertex i)
          simp
        have huNotB : u ∉ ({F.a, F.b, F.c} : Finset V) :=
          Finset.disjoint_left.1 F.boundary_disjoint hu
        let bi : F.BaseVertex :=
          ⟨F.boundaryVertex i, F.boundary_mem_base i⟩
        have hub : F.preparedGraph.Adj
            (.inl ⟨u, Finset.mem_union_left _ hu⟩) (.inl bi) := by
          exact ⟨huw, fun hbad ↦ huNotB hbad.1⟩
        by_cases hi : F.NeedsFreshPin i
        · have hbpin : F.preparedGraph.Adj (.inl bi) (F.pin i) := by
            simpa only [pin, dif_pos hi] using
              (show F.preparedGraph.Adj (.inl bi) (.inr ⟨i, hi⟩) from rfl)
          exact ⟨i, hiD, hub.reachable.trans hbpin.reachable⟩
        · have hpin : F.pin i = (.inl bi : F.PreparedVertex) := by
            simp [pin, hi, bi]
          exact ⟨i, hiD, hpin.symm ▸ hub.reachable⟩

/-- Strengthened first-exit rerouting which retains the actual prepared walk
and records that every one of its vertices avoids the ambient shadow set.
This is the form needed when one or two old replacement vertices have been
deleted. -/
theorem walk_inside_to_surviving_pin_avoiding {D : Finset V} {u v : V}
    (p : G.Walk u v) (hu : u ∈ F.verts) (hv : v ∉ F.verts)
    (havoid : ∀ z ∈ p.support, z ∉ D) :
    ∃ i : Fin 3, F.boundaryVertex i ∉ D ∧
      ∃ w : F.preparedGraph.Walk
        (.inl ⟨u, Finset.mem_union_left _ hu⟩) (F.pin i),
        ∀ z ∈ w.support, F.preparedShadow z ∉ D := by
  induction p with
  | nil => exact (hv hu).elim
  | @cons u w v huw p ih =>
      by_cases hwF : w ∈ F.verts
      · have havoidTail : ∀ z ∈ p.support, z ∉ D := by
          intro z hz
          exact havoid z (by simp [hz])
        obtain ⟨i, hiD, q, hqAvoid⟩ := ih hwF hv havoidTail
        have huNotB : u ∉ ({F.a, F.b, F.c} : Finset V) :=
          Finset.disjoint_left.1 F.boundary_disjoint hu
        have huwP : F.preparedGraph.Adj
            (.inl ⟨u, Finset.mem_union_left _ hu⟩)
            (.inl ⟨w, Finset.mem_union_left _ hwF⟩) :=
          ⟨huw, fun hbad ↦ huNotB hbad.1⟩
        let q' := q.cons huwP
        refine ⟨i, hiD, q', ?_⟩
        intro z hz
        change z ∈ (q.cons huwP).support at hz
        simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
        rcases hz with rfl | hz
        · exact havoid u (by simp)
        · exact hqAvoid z hz
      · have hwBoundary :
            w = F.a ∨ w = F.b ∨ w = F.c :=
          (F.boundary_exact w hwF).1 ⟨u, hu, huw.symm⟩
        obtain ⟨i, rfl⟩ : ∃ i : Fin 3, w = F.boundaryVertex i := by
          rcases hwBoundary with rfl | rfl | rfl
          · exact ⟨0, rfl⟩
          · exact ⟨1, rfl⟩
          · exact ⟨2, rfl⟩
        have hiD : F.boundaryVertex i ∉ D := by
          apply havoid (F.boundaryVertex i)
          simp
        have huD : u ∉ D := havoid u (by simp)
        have huNotB : u ∉ ({F.a, F.b, F.c} : Finset V) :=
          Finset.disjoint_left.1 F.boundary_disjoint hu
        let bi : F.BaseVertex :=
          ⟨F.boundaryVertex i, F.boundary_mem_base i⟩
        have hub : F.preparedGraph.Adj
            (.inl ⟨u, Finset.mem_union_left _ hu⟩) (.inl bi) :=
          ⟨huw, fun hbad ↦ huNotB hbad.1⟩
        by_cases hi : F.NeedsFreshPin i
        · have hbpin : F.preparedGraph.Adj (.inl bi) (F.pin i) := by
            simpa only [pin, dif_pos hi] using
              (show F.preparedGraph.Adj (.inl bi) (.inr ⟨i, hi⟩) from rfl)
          let q := hbpin.toWalk.cons hub
          refine ⟨i, hiD, q, ?_⟩
          intro z hz
          change z ∈ (hbpin.toWalk.cons hub).support at hz
          simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Adj.support_toWalk,
            List.mem_cons, List.mem_singleton, List.not_mem_nil] at hz
          simp at hz
          rcases hz with rfl | rfl | rfl
          · exact huD
          · exact hiD
          · simpa [pin, hi] using hiD
        · have hpin : (.inl bi : F.PreparedVertex) = F.pin i := by
            simp [pin, hi, bi]
          let q := hub.toWalk.copy rfl hpin
          refine ⟨i, hiD, q, ?_⟩
          intro z hz
          change z ∈ (hub.toWalk.copy rfl hpin).support at hz
          simp only [SimpleGraph.Walk.support_copy,
            SimpleGraph.Adj.support_toWalk, List.mem_cons,
            List.mem_singleton, List.not_mem_nil] at hz
          rcases hz with rfl | rfl | hz
          · exact huD
          · exact hiD
          · exact hz.elim

/-- After deleting fewer than three prepared vertices, every surviving
inside vertex still reaches a surviving pin.  The ambient deletion set is
the image of the deleted prepared vertices under `preparedShadow`; ambient
three-connectivity supplies the walk to the exterior and the strengthened
first-exit lemma keeps the reroute away from every deleted vertex. -/
theorem inside_reaches_pin_after_prepared_deletion
    (hthree : IsThreeConnected G) (E : Finset F.PreparedVertex)
    (hE : E.card < 3) {p : V} (hpF : p ∈ F.verts)
    (hpE : (.inl ⟨p, Finset.mem_union_left _ hpF⟩ : F.PreparedVertex) ∉ E) :
    ∃ i : Fin 3, ∃ hiE : F.pin i ∉ E,
      (F.preparedGraph.induce fun z : F.PreparedVertex ↦ z ∉ E).Reachable
        ⟨.inl ⟨p, Finset.mem_union_left _ hpF⟩, hpE⟩
        ⟨F.pin i, hiE⟩ := by
  let D := F.preparedDeletionShadow E
  have hD : D.card < 3 := by
    dsimp [D]
    exact lt_of_le_of_lt (F.preparedDeletionShadow_card_le E) hE
  have hpD : p ∉ D := F.inside_shadow_not_mem_of_old_not_mem hpF hpE
  obtain ⟨o, ho⟩ := F.outside_nonempty
  have hoOutside := (Finset.mem_sdiff.1 ho).2
  have hoF : o ∉ F.verts := by
    intro hoF
    exact hoOutside (Finset.mem_union_left _ hoF)
  have hoD : o ∉ D := by
    intro hoD
    have hoCarrier := F.preparedDeletionShadow_subset_fragment_boundary E hoD
    exact hoOutside hoCarrier
  have hpre := hthree.induce_compl_preconnected D hD
  let pD : {v : V // v ∉ D} := ⟨p, hpD⟩
  let oD : {v : V // v ∉ D} := ⟨o, hoD⟩
  obtain ⟨w⟩ := hpre pD oD
  let emb : (G.induce fun v : V ↦ v ∉ D) →g G :=
    { toFun := Subtype.val
      map_rel' := by intro x y hxy; exact hxy }
  let q : G.Walk p o := w.map emb
  have havoid : ∀ z ∈ q.support, z ∉ D := by
    intro z hz
    dsimp [q] at hz
    rw [SimpleGraph.Walk.support_map] at hz
    obtain ⟨zD, hzD, hzEq⟩ := List.mem_map.mp hz
    subst z
    have hemb : emb zD = zD.1 := rfl
    rw [hemb]
    exact zD.2
  obtain ⟨i, hiD, r, hrAvoid⟩ :=
    F.walk_inside_to_surviving_pin_avoiding q hpF hoF havoid
  have hiE : F.pin i ∉ E := by
    apply F.not_mem_preparedDeletion_of_shadow_not_mem
    simpa using hiD
  have hrE : ∀ z ∈ r.support, z ∉ E := by
    intro z hz
    exact F.not_mem_preparedDeletion_of_shadow_not_mem (hrAvoid z hz)
  let rE := r.induce (fun z : F.PreparedVertex ↦ z ∉ E) hrE
  exact ⟨i, hiE, rE.reachable⟩

/-- The preceding reroute extends from fragment vertices to every surviving
prepared vertex.  A fresh pin is itself a pin.  An identified boundary pin
is likewise immediate.  For a boundary vertex with a fresh pin, either that
pin survives, or its deletion shadows the boundary; in the latter case the
boundary has two inside neighbours, so one avoids the fewer-than-three
ambient shadows and the inside rerouting lemma applies. -/
theorem prepared_reaches_pin_after_deletion
    (hthree : IsThreeConnected G) (E : Finset F.PreparedVertex)
    (hE : E.card < 3) {z : F.PreparedVertex} (hzE : z ∉ E) :
    ∃ i : Fin 3, ∃ hiE : F.pin i ∉ E,
      (F.preparedGraph.induce fun w : F.PreparedVertex ↦ w ∉ E).Reachable
        ⟨z, hzE⟩ ⟨F.pin i, hiE⟩ := by
  rcases z with q | j
  · rcases Finset.mem_union.mp q.2 with hqF | hqB
    · exact F.inside_reaches_pin_after_prepared_deletion hthree E hE hqF hzE
    · have hq : q.1 = F.a ∨ q.1 = F.b ∨ q.1 = F.c := by
        simpa using hqB
      obtain ⟨i, hqi⟩ : ∃ i : Fin 3, q.1 = F.boundaryVertex i := by
        rcases hq with hq | hq
        · exact ⟨0, by simpa using hq⟩
        · rcases hq with hq | hq
          · exact ⟨1, by simpa using hq⟩
          · exact ⟨2, by simpa using hq⟩
      let bi : F.BaseVertex :=
        ⟨F.boundaryVertex i, F.boundary_mem_base i⟩
      have hqbi : q = bi := Subtype.ext hqi
      subst q
      by_cases hi : F.NeedsFreshPin i
      · by_cases hpinE : F.pin i ∈ E
        · let D := F.preparedDeletionShadow E
          have hD : D.card < 3 :=
            lt_of_le_of_lt (F.preparedDeletionShadow_card_le E) hE
          have hiD : F.boundaryVertex i ∈ D :=
            F.boundary_mem_preparedDeletionShadow_of_pin_mem hpinE
          obtain ⟨y, hy, hyD⟩ :=
            F.exists_insideNeighbor_not_mem i hi hiD hD
          have hy' := Finset.mem_inter.1 hy
          have hyF : y ∈ F.verts := hy'.2
          have hyAdj : G.Adj (F.boundaryVertex i) y := by
            simpa [SimpleGraph.mem_neighborFinset] using hy'.1
          have hyNotB : y ∉ ({F.a, F.b, F.c} : Finset V) :=
            Finset.disjoint_left.1 F.boundary_disjoint hyF
          let yi : F.BaseVertex :=
            ⟨y, Finset.mem_union_left _ hyF⟩
          have hyE : (.inl yi : F.PreparedVertex) ∉ E := by
            apply F.not_mem_preparedDeletion_of_shadow_not_mem
            simpa [D, yi] using hyD
          obtain ⟨k, hkE, hreach⟩ :=
            F.inside_reaches_pin_after_prepared_deletion
              hthree E hE hyF hyE
          have hby : F.preparedGraph.Adj (.inl bi) (.inl yi) :=
            ⟨hyAdj, fun hbad ↦ hyNotB hbad.2⟩
          have hbyE :
              (F.preparedGraph.induce fun w : F.PreparedVertex ↦ w ∉ E).Adj
                ⟨.inl bi, hzE⟩ ⟨.inl yi, hyE⟩ := hby
          exact ⟨k, hkE, hbyE.reachable.trans hreach⟩
        · have hbpin : F.preparedGraph.Adj (.inl bi) (F.pin i) := by
            simpa only [pin, dif_pos hi] using
              (show F.preparedGraph.Adj (.inl bi) (.inr ⟨i, hi⟩) from rfl)
          have hbpinE :
              (F.preparedGraph.induce fun w : F.PreparedVertex ↦ w ∉ E).Adj
                ⟨.inl bi, hzE⟩ ⟨F.pin i, hpinE⟩ := hbpin
          exact ⟨i, hpinE, hbpinE.reachable⟩
      · have hpin : F.pin i = (.inl bi : F.PreparedVertex) := by
          simp [pin, hi, bi]
        have hpinE : F.pin i ∉ E := by simpa [hpin] using hzE
        refine ⟨i, hpinE, ?_⟩
        simpa [hpin] using
          (SimpleGraph.Reachable.rfl :
            (F.preparedGraph.induce fun w : F.PreparedVertex ↦ w ∉ E).Reachable
              ⟨.inl bi, hzE⟩ ⟨.inl bi, hzE⟩)
  · have hpin : F.pin j.1 = (.inr j : F.PreparedVertex) := by
      simp [pin, j.2]
    have hpinE : F.pin j.1 ∉ E := by simpa [hpin] using hzE
    refine ⟨j.1, hpinE, ?_⟩
    simpa [hpin] using
      (SimpleGraph.Reachable.rfl :
        (F.preparedGraph.induce fun w : F.PreparedVertex ↦ w ∉ E).Reachable
          ⟨.inr j, hzE⟩ ⟨.inr j, hzE⟩)

@[simp] theorem prepared_adj_old_fresh {p : F.BaseVertex} {j : F.FreshPin} :
    F.preparedGraph.Adj (.inl p) (.inr j) ↔
      p.1 = F.boundaryVertex j.1 := by
  rfl

@[simp] theorem prepared_adj_fresh_old {i : F.FreshPin} {q : F.BaseVertex} :
    F.preparedGraph.Adj (.inr i) (.inl q) ↔
      q.1 = F.boundaryVertex i.1 := by
  rfl

@[simp] theorem prepared_not_adj_fresh_fresh (i j : F.FreshPin) :
    ¬F.preparedGraph.Adj (.inr i) (.inr j) := id

/-- Every fresh pin is pendant before `d,d'` are adjoined. -/
theorem degree_freshPin (i : F.FreshPin) :
    F.preparedGraph.degree (.inr i) = 1 := by
  rw [← F.preparedGraph.card_neighborFinset_eq_degree]
  have hneigh : F.preparedGraph.neighborFinset (.inr i) =
      {(.inl ⟨F.boundaryVertex i.1, by
        exact F.boundary_mem_base i.1⟩ : F.PreparedVertex)} := by
    ext z
    rcases z with q | j
    · simp [SimpleGraph.mem_neighborFinset, Subtype.ext_iff]
    · simp [SimpleGraph.mem_neighborFinset]
  rw [hneigh]
  simp

/-- Every distinguished pin has degree one in the prepared graph.  For an
identified pin this is precisely the branch where its inside-neighbour set
has cardinality one; all boundary-boundary edges have been deleted. -/
theorem degree_pin (i : Fin 3) : F.preparedGraph.degree (F.pin i) = 1 := by
  classical
  by_cases hi : F.NeedsFreshPin i
  · rw [show F.pin i = (.inr ⟨i, hi⟩ : F.PreparedVertex) by
      simp [pin, hi]]
    exact F.degree_freshPin ⟨i, hi⟩
  · let qi : F.BaseVertex := ⟨F.boundaryVertex i, F.boundary_mem_base i⟩
    have hpin : F.pin i = (.inl qi : F.PreparedVertex) := by
      simp [pin, hi, qi]
    rw [hpin, ← F.preparedGraph.card_neighborFinset_eq_degree]
    let value : F.PreparedVertex → V
      | .inl q => q.1
      | .inr j => F.boundaryVertex j.1
    have neighbor_old (z : F.PreparedVertex)
        (hz : z ∈ F.preparedGraph.neighborFinset (.inl qi)) :
        ∃ q : F.BaseVertex, z = .inl q := by
      rw [SimpleGraph.mem_neighborFinset] at hz
      rcases z with q | j
      · exact ⟨q, rfl⟩
      · change F.boundaryVertex i = F.boundaryVertex j.1 at hz
        have hij : i = j.1 := F.boundaryVertex_injective hz
        subst i
        exact (hi j.2).elim
    have hmap (z : F.PreparedVertex)
        (hz : z ∈ F.preparedGraph.neighborFinset (.inl qi)) :
        value z ∈ F.insideNeighborFinset i := by
      obtain ⟨q, rfl⟩ := neighbor_old z hz
      rw [SimpleGraph.mem_neighborFinset] at hz
      change G.Adj (F.boundaryVertex i) q.1 ∧
        ¬(F.boundaryVertex i ∈ ({F.a, F.b, F.c} : Finset V) ∧
          q.1 ∈ ({F.a, F.b, F.c} : Finset V)) at hz
      have hiB : F.boundaryVertex i ∈ ({F.a, F.b, F.c} : Finset V) := by
        fin_cases i <;> simp
      have hqF : q.1 ∈ F.verts := by
        rcases Finset.mem_union.mp q.2 with hqF | hqB
        · exact hqF
        · exact (hz.2 ⟨hiB, hqB⟩).elim
      simp [value, insideNeighborFinset, SimpleGraph.mem_neighborFinset,
        hz.1, hqF]
    have hinj (z₁ : F.PreparedVertex)
        (hz₁ : z₁ ∈ F.preparedGraph.neighborFinset (.inl qi))
        (z₂ : F.PreparedVertex)
        (hz₂ : z₂ ∈ F.preparedGraph.neighborFinset (.inl qi))
        (heq : value z₁ = value z₂) : z₁ = z₂ := by
      obtain ⟨q₁, rfl⟩ := neighbor_old z₁ hz₁
      obtain ⟨q₂, rfl⟩ := neighbor_old z₂ hz₂
      simp only [value] at heq
      exact congrArg (Sum.inl : F.BaseVertex → F.PreparedVertex)
        (Subtype.ext heq)
    have hsurj (y : V) (hy : y ∈ F.insideNeighborFinset i) :
        ∃ z : F.PreparedVertex,
          ∃ _hz : z ∈ F.preparedGraph.neighborFinset (.inl qi), value z = y := by
      have hy' := Finset.mem_inter.1 hy
      have hyAdj : G.Adj (F.boundaryVertex i) y := by
        simpa [SimpleGraph.mem_neighborFinset] using hy'.1
      have hyNotB : y ∉ ({F.a, F.b, F.c} : Finset V) := by
        intro hyB
        exact (Finset.disjoint_left.1 F.boundary_disjoint hy'.2 hyB)
      let qy : F.BaseVertex := ⟨y, Finset.mem_union_left _ hy'.2⟩
      let z : F.PreparedVertex := .inl qy
      have hz : z ∈ F.preparedGraph.neighborFinset (.inl qi) := by
        rw [SimpleGraph.mem_neighborFinset]
        change G.Adj (F.boundaryVertex i) y ∧
          ¬(F.boundaryVertex i ∈ ({F.a, F.b, F.c} : Finset V) ∧
            y ∈ ({F.a, F.b, F.c} : Finset V))
        exact ⟨hyAdj, fun hbad ↦ hyNotB hbad.2⟩
      exact ⟨z, hz, rfl⟩
    calc
      (F.preparedGraph.neighborFinset (.inl qi)).card =
          (F.insideNeighborFinset i).card :=
        Finset.card_bij (fun z hz ↦ value z) hmap hinj hsurj
      _ = 1 := F.insideNeighborFinset_card_eq_one_of_not_needsFreshPin i hi

/-- An interior fragment vertex has exactly the same neighbours, and hence
the same degree, in the prepared graph as in the ambient graph.  Every
ambient edge leaving the fragment ends at one of the three retained boundary
vertices, while fresh pins attach only to boundary vertices. -/
theorem prepared_degree_inside_eq_ambient (q : F.BaseVertex)
    (hqF : q.1 ∈ F.verts) :
    F.preparedGraph.degree (.inl q) = G.degree q.1 := by
  classical
  rw [← F.preparedGraph.card_neighborFinset_eq_degree,
    ← G.card_neighborFinset_eq_degree]
  let value : F.PreparedVertex → V
    | .inl r => r.1
    | .inr j => F.boundaryVertex j.1
  have neighbor_old (z : F.PreparedVertex)
      (hz : z ∈ F.preparedGraph.neighborFinset (.inl q)) :
      ∃ r : F.BaseVertex, z = .inl r := by
    rw [SimpleGraph.mem_neighborFinset] at hz
    rcases z with r | j
    · exact ⟨r, rfl⟩
    · change q.1 = F.boundaryVertex j.1 at hz
      exact (F.boundary_not_mem j.1 (hz ▸ hqF)).elim
  have hmap (z : F.PreparedVertex)
      (hz : z ∈ F.preparedGraph.neighborFinset (.inl q)) :
      value z ∈ G.neighborFinset q.1 := by
    obtain ⟨r, rfl⟩ := neighbor_old z hz
    rw [SimpleGraph.mem_neighborFinset] at hz ⊢
    exact hz.1
  have hinj (z₁ : F.PreparedVertex)
      (hz₁ : z₁ ∈ F.preparedGraph.neighborFinset (.inl q))
      (z₂ : F.PreparedVertex)
      (hz₂ : z₂ ∈ F.preparedGraph.neighborFinset (.inl q))
      (heq : value z₁ = value z₂) : z₁ = z₂ := by
    obtain ⟨r₁, rfl⟩ := neighbor_old z₁ hz₁
    obtain ⟨r₂, rfl⟩ := neighbor_old z₂ hz₂
    exact congrArg (Sum.inl : F.BaseVertex → F.PreparedVertex)
      (Subtype.ext heq)
  have hsurj (y : V) (hy : y ∈ G.neighborFinset q.1) :
      ∃ z : F.PreparedVertex,
        ∃ _hz : z ∈ F.preparedGraph.neighborFinset (.inl q), value z = y := by
    have hqy : G.Adj q.1 y := by simpa using hy
    have hyCarrier : y ∈ F.verts ∪ ({F.a, F.b, F.c} : Finset V) := by
      by_cases hyF : y ∈ F.verts
      · exact Finset.mem_union_left _ hyF
      · have hyBoundary : y = F.a ∨ y = F.b ∨ y = F.c :=
          (F.boundary_exact y hyF).1 ⟨q.1, hqF, hqy.symm⟩
        exact Finset.mem_union_right F.verts (by simpa using hyBoundary)
    let r : F.BaseVertex := ⟨y, hyCarrier⟩
    let z : F.PreparedVertex := .inl r
    have hqNotBoundary : q.1 ∉ ({F.a, F.b, F.c} : Finset V) :=
      Finset.disjoint_left.1 F.boundary_disjoint hqF
    have hz : z ∈ F.preparedGraph.neighborFinset (.inl q) := by
      rw [SimpleGraph.mem_neighborFinset]
      exact ⟨hqy, fun hbad ↦ hqNotBoundary hbad.1⟩
    exact ⟨z, hz, rfl⟩
  exact Finset.card_bij (fun z hz ↦ value z) hmap hinj hsurj

/-- Complete wheel transfer in the branch where the alleged replacement rim
avoids `d,d'`: first lower the rim to the prepared graph, then use pendantness
to remove all fresh pins, and finally forget the fragment carrier. -/
theorem ambient_hasWheelCenteredAt_of_replacement_cycle_avoids_new
    {x : F.BaseVertex} {r₀ : F.PreparedVertex}
    (rim : F.replacementGraph.Walk (.inl r₀) (.inl r₀))
    (hcycle : rim.IsCycle)
    (hxrim : (.inl (.inl x) : F.PreparedVertex ⊕ Fin 2) ∉ rim.support)
    (hthree : 3 ≤ (F.replacementGraph.neighborFinset (.inl (.inl x)) ∩
      rim.support.toFinset).card)
    (havoid : ∀ i : Fin 2,
      (.inr i : F.PreparedVertex ⊕ Fin 2) ∉ rim.support) :
    HasWheelCenteredAt G x.1 := by
  have hwPrepared : HasWheelCenteredAt F.preparedGraph (.inl x) :=
    ahtDoublePinReplacement.hasWheelCenteredAt_old_of_cycle_avoids_new
      rim hcycle hxrim hthree havoid
  obtain ⟨s, p, hp, hxp, hpThree⟩ := hwPrepared
  have havoidFresh (i : F.FreshPin) :
      (.inr i : F.PreparedVertex) ∉ p.support :=
    not_mem_cycle_support_of_degree_eq_one (F.degree_freshPin i) hp
  rcases s with s | i
  · exact F.ambient_hasWheelCenteredAt_of_prepared_cycle_avoids_fresh
      p hp hxp hpThree havoidFresh
  · exact (havoidFresh i p.start_mem_support).elim

/-- The three distinguished pins are pairwise different. -/
theorem pin_ne {i j : Fin 3} (hij : i ≠ j) : F.pin i ≠ F.pin j := by
  classical
  by_cases hi : F.NeedsFreshPin i <;> by_cases hj : F.NeedsFreshPin j
  · simp [pin, hi, hj, hij]
  · simp [pin, hi, hj]
  · simp [pin, hi, hj]
  · simp only [pin, dif_neg hi, dif_neg hj]
    intro heq
    have hsub := Sum.inl.inj heq
    have hval : F.boundaryVertex i = F.boundaryVertex j :=
      congrArg Subtype.val hsub
    exact hij (F.boundaryVertex_injective hval)

/-- The old boundary vertex at one index is different from the distinguished
pin at every other index. -/
theorem boundary_old_ne_pin {i j : Fin 3} (hij : i ≠ j) :
    (.inl ⟨F.boundaryVertex i, F.boundary_mem_base i⟩ : F.PreparedVertex) ≠
      F.pin j := by
  classical
  by_cases hj : F.NeedsFreshPin j
  · simp [pin, hj]
  · simp only [pin, dif_neg hj]
    intro heq
    have hsub := Sum.inl.inj heq
    have hval : F.boundaryVertex i = F.boundaryVertex j :=
      congrArg Subtype.val hsub
    exact hij (F.boundaryVertex_injective hval)

/-- The prepared pins are independent, including all four combinations of
fresh and identified pins. -/
theorem not_adj_pin {i j : Fin 3} (hij : i ≠ j) :
    ¬F.preparedGraph.Adj (F.pin i) (F.pin j) := by
  classical
  by_cases hi : F.NeedsFreshPin i <;> by_cases hj : F.NeedsFreshPin j
  · simp [pin, hi, hj]
  · simp only [pin, dif_pos hi, dif_neg hj, prepared_adj_fresh_old]
    intro heq
    exact hij (F.boundaryVertex_injective heq).symm
  · simp only [pin, dif_neg hi, dif_pos hj, prepared_adj_old_fresh]
    intro heq
    exact hij (F.boundaryVertex_injective heq)
  · simp only [pin, dif_neg hi, dif_neg hj]
    rintro ⟨-, hnot⟩
    apply hnot
    constructor <;> fin_cases i <;> fin_cases j <;> simp

/-- Trim the optional pendant pins from the endpoints of a simple prepared
pin-to-pin path and map the remaining old path to the ambient graph.  No old
vertex is lost: the support equivalence is exact for every base vertex. -/
theorem exists_ambient_path_of_prepared_pinPath
    (i j : Fin 3) (hij : i ≠ j)
    (p : F.preparedGraph.Walk (F.pin i) (F.pin j)) (hp : p.IsPath) :
    ∃ q : G.Walk (F.boundaryVertex i) (F.boundaryVertex j),
      q.IsPath ∧
      (∀ x : F.BaseVertex,
        (.inl x : F.PreparedVertex) ∈ p.support ↔ x.1 ∈ q.support) ∧
      ∀ y ∈ q.support, ∃ x : F.BaseVertex, x.1 = y := by
  classical
  let bi : F.BaseVertex :=
    ⟨F.boundaryVertex i, F.boundary_mem_base i⟩
  let bj : F.BaseVertex :=
    ⟨F.boundaryVertex j, F.boundary_mem_base j⟩
  have hpNot : ¬p.Nil :=
    SimpleGraph.Walk.not_nil_of_ne (F.pin_ne hij)
  have trim : ∃ w : F.preparedGraph.Walk (.inl bi) (.inl bj),
      w.IsPath ∧ ∀ x : F.BaseVertex,
        (.inl x : F.PreparedVertex) ∈ w.support ↔
          (.inl x : F.PreparedVertex) ∈ p.support := by
    by_cases hi : F.NeedsFreshPin i <;>
      by_cases hj : F.NeedsFreshPin j
    · let fi : F.FreshPin := ⟨i, hi⟩
      let fj : F.FreshPin := ⟨j, hj⟩
      have hpi : F.pin i = (.inr fi : F.PreparedVertex) := by
        simp [pin, hi, fi]
      have hpj : F.pin j = (.inr fj : F.PreparedVertex) := by
        simp [pin, hj, fj]
      have hsnd : p.snd = (.inl bi : F.PreparedVertex) := by
        have hadj : F.preparedGraph.Adj (.inr fi) p.snd := by
          simpa only [hpi] using p.adj_snd hpNot
        cases hs : p.snd with
        | inl x =>
            have hx : x.1 = F.boundaryVertex i :=
              (F.prepared_adj_fresh_old (i := fi) (q := x)).mp
                (by simpa only [hs] using hadj)
            have hxbi : x = bi := Subtype.ext hx
            simpa only [hs, hxbi]
        | inr f =>
            exact (F.prepared_not_adj_fresh_fresh fi f
              (by simpa only [hs] using hadj)).elim
      have htailNot : ¬p.tail.Nil := by
        apply SimpleGraph.Walk.not_nil_of_ne
        rw [hsnd, hpj]
        exact Sum.inl_ne_inr
      have hpen : p.tail.penultimate = (.inl bj : F.PreparedVertex) := by
        have hadj : F.preparedGraph.Adj p.tail.penultimate (.inr fj) := by
          simpa only [hpj] using p.tail.adj_penultimate htailNot
        cases hs : p.tail.penultimate with
        | inl x =>
            have hx : x.1 = F.boundaryVertex j :=
              (F.prepared_adj_old_fresh (p := x) (j := fj)).mp
                (by simpa only [hs] using hadj)
            have hxbj : x = bj := Subtype.ext hx
            simpa only [hs, hxbj]
        | inr f =>
            exact (F.prepared_not_adj_fresh_fresh f fj
              (by simpa only [hs] using hadj)).elim
      let w : F.preparedGraph.Walk (.inl bi) (.inl bj) :=
        p.tail.dropLast.copy hsnd hpen
      refine ⟨w, (SimpleGraph.Walk.isPath_copy _ _ _).2
        hp.tail.dropLast, ?_⟩
      intro x
      have hs1 := p.cons_support_tail hpNot
      have hs2 := p.tail.support_dropLast_concat htailNot
      simp only [w, SimpleGraph.Walk.support_copy]
      rw [← hs1, ← hs2]
      simp [hpi, hpj]
    · let fi : F.FreshPin := ⟨i, hi⟩
      have hpi : F.pin i = (.inr fi : F.PreparedVertex) := by
        simp [pin, hi, fi]
      have hpj : F.pin j = (.inl bj : F.PreparedVertex) := by
        simp [pin, hj, bj]
      have hsnd : p.snd = (.inl bi : F.PreparedVertex) := by
        have hadj : F.preparedGraph.Adj (.inr fi) p.snd := by
          simpa only [hpi] using p.adj_snd hpNot
        cases hs : p.snd with
        | inl x =>
            have hx : x.1 = F.boundaryVertex i :=
              (F.prepared_adj_fresh_old (i := fi) (q := x)).mp
                (by simpa only [hs] using hadj)
            have hxbi : x = bi := Subtype.ext hx
            simpa only [hs, hxbi]
        | inr f =>
            exact (F.prepared_not_adj_fresh_fresh fi f
              (by simpa only [hs] using hadj)).elim
      let w : F.preparedGraph.Walk (.inl bi) (.inl bj) :=
        p.tail.copy hsnd hpj
      refine ⟨w, (SimpleGraph.Walk.isPath_copy _ _ _).2 hp.tail, ?_⟩
      intro x
      have hs := p.cons_support_tail hpNot
      simp only [w, SimpleGraph.Walk.support_copy]
      rw [← hs]
      simp [hpi]
    · let fj : F.FreshPin := ⟨j, hj⟩
      have hpi : F.pin i = (.inl bi : F.PreparedVertex) := by
        simp [pin, hi, bi]
      have hpj : F.pin j = (.inr fj : F.PreparedVertex) := by
        simp [pin, hj, fj]
      have hpen : p.penultimate = (.inl bj : F.PreparedVertex) := by
        have hadj : F.preparedGraph.Adj p.penultimate (.inr fj) := by
          simpa only [hpj] using p.adj_penultimate hpNot
        cases hs : p.penultimate with
        | inl x =>
            have hx : x.1 = F.boundaryVertex j :=
              (F.prepared_adj_old_fresh (p := x) (j := fj)).mp
                (by simpa only [hs] using hadj)
            have hxbj : x = bj := Subtype.ext hx
            simpa only [hs, hxbj]
        | inr f =>
            exact (F.prepared_not_adj_fresh_fresh f fj
              (by simpa only [hs] using hadj)).elim
      let w : F.preparedGraph.Walk (.inl bi) (.inl bj) :=
        p.dropLast.copy hpi hpen
      refine ⟨w, (SimpleGraph.Walk.isPath_copy _ _ _).2 hp.dropLast, ?_⟩
      intro x
      have hs := p.support_dropLast_concat hpNot
      simp only [w, SimpleGraph.Walk.support_copy]
      rw [← hs]
      simp [hpj]
    · have hpi : F.pin i = (.inl bi : F.PreparedVertex) := by
        simp [pin, hi, bi]
      have hpj : F.pin j = (.inl bj : F.PreparedVertex) := by
        simp [pin, hj, bj]
      let w : F.preparedGraph.Walk (.inl bi) (.inl bj) :=
        p.copy hpi hpj
      refine ⟨w, (SimpleGraph.Walk.isPath_copy _ _ _).2 hp, ?_⟩
      intro x
      simp only [w, SimpleGraph.Walk.support_copy]
  obtain ⟨w, hw, hwSupport⟩ := trim
  have hold : ∀ z ∈ w.support, ∃ x : F.BaseVertex, z = .inl x := by
    intro z hz
    rcases z with x | f
    · exact ⟨x, rfl⟩
    · have hendpoint :=
        eq_start_or_eq_end_of_mem_path_of_degree_eq_one hw
          (F.degree_freshPin f) hz
      rcases hendpoint with hf | hf <;> exact (Sum.inr_ne_inl hf).elim
  obtain ⟨r, hrMap⟩ :=
    F.exists_preparedOldWalk_of_support_avoids_fresh w hold
  let q : G.Walk (F.boundaryVertex i) (F.boundaryVertex j) :=
    r.map F.preparedOldToAmbient
  have hr : r.IsPath := by
    apply SimpleGraph.Walk.IsPath.of_map
    rw [hrMap]
    exact hw
  have hq : q.IsPath := hr.map F.preparedOldToAmbient_injective
  refine ⟨q, hq, ?_, ?_⟩
  · intro x
    have hrw : x ∈ r.support ↔ (.inl x : F.PreparedVertex) ∈ w.support := by
      rw [← hrMap]
      change x ∈ r.support ↔
        (.inl x : F.PreparedVertex) ∈ (r.map F.preparedOldInclusion).support
      rw [SimpleGraph.Walk.support_map]
      simp
    have hrq : x ∈ r.support ↔ x.1 ∈ q.support := by
      change x ∈ r.support ↔
        x.1 ∈ (r.map F.preparedOldToAmbient).support
      rw [SimpleGraph.Walk.support_map]
      constructor
      · intro hx
        exact List.mem_map.mpr ⟨x, hx, rfl⟩
      · intro hx
        obtain ⟨z, hz, hzx⟩ := List.mem_map.mp hx
        have hzx' : z = x := Subtype.ext hzx
        simpa only [hzx'] using hz
    exact (hwSupport x).symm.trans (hrw.symm.trans hrq)
  · intro y hy
    change y ∈ (r.map F.preparedOldToAmbient).support at hy
    rw [SimpleGraph.Walk.support_map] at hy
    obtain ⟨x, hx, hxy⟩ := List.mem_map.mp hy
    exact ⟨x, hxy⟩

/-- Close a prepared path between two pins through the exterior side of the
fragment.  The third boundary vertex supplies a displayed exterior
neighbour on the resulting ambient cycle.  For every fragment vertex, and
also for that third boundary vertex, membership in the old prepared path is
equivalent to membership in the ambient cycle. -/
theorem exists_ambient_cycle_of_prepared_pinPath
    (hthree : IsThreeConnected G) (i j k : Fin 3)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hcover : ∀ l : Fin 3, l = i ∨ l = j ∨ l = k)
    (p : F.preparedGraph.Walk (F.pin j) (F.pin k)) (hp : p.IsPath) :
    ∃ x ∈ Finset.univ \ (F.verts ∪ F.boundaryFinset),
      G.Adj (F.boundaryVertex i) x ∧
      ∃ rim : G.Walk (F.boundaryVertex j) (F.boundaryVertex j),
        rim.IsCycle ∧ x ∈ rim.support ∧
        (∀ y : F.BaseVertex,
          (.inl y : F.PreparedVertex) ∈ p.support → y.1 ∈ rim.support) ∧
        ∀ y : F.BaseVertex,
          (y.1 ∈ F.verts ∨ y.1 = F.boundaryVertex i) →
          ((.inl y : F.PreparedVertex) ∈ p.support ↔ y.1 ∈ rim.support) := by
  classical
  obtain ⟨x, hxOutside, hix, ext, hext, hxext, hiExt,
      hboundary, hextF⟩ :=
    F.exists_otherBoundary_exterior_path_through_neighbor
      hthree i j k hij hik hjk hcover
  obtain ⟨q, hq, hpq, hqCarrier⟩ :=
    F.exists_ambient_path_of_prepared_pinPath j k hjk p hp
  have hxj : x ≠ F.boundaryVertex j := by
    intro hx
    subst x
    exact (Finset.mem_sdiff.1 hxOutside).2
      (Finset.mem_union_right F.verts
        (F.boundaryVertex_mem_boundaryFinset j))
  have hxk : x ≠ F.boundaryVertex k := by
    intro hx
    subst x
    exact (Finset.mem_sdiff.1 hxOutside).2
      (Finset.mem_union_right F.verts
        (F.boundaryVertex_mem_boundaryFinset k))
  have hmeet : ∀ y, y ∈ ext.support → y ∈ q.support →
      y = F.boundaryVertex j ∨ y = F.boundaryVertex k := by
    intro y hyExt hyq
    obtain ⟨z, hzy⟩ := hqCarrier y hyq
    have hzNotF : z.1 ∉ F.verts := by
      intro hzF
      exact hextF y hyExt (hzy ▸ hzF)
    have hzBoundary : z.1 ∈ F.boundaryFinset := by
      rcases Finset.mem_union.mp z.2 with hzF | hzB
      · exact (hzNotF hzF).elim
      · simpa [boundaryFinset] using hzB
    obtain ⟨l, hzl⟩ : ∃ l : Fin 3, z.1 = F.boundaryVertex l := by
      have hz : z.1 = F.a ∨ z.1 = F.b ∨ z.1 = F.c := by
        simpa [boundaryFinset] using hzBoundary
      rcases hz with ha | hb | hc
      · exact ⟨0, by simpa using ha⟩
      · exact ⟨1, by simpa using hb⟩
      · exact ⟨2, by simpa using hc⟩
    have hyl : y = F.boundaryVertex l := hzy.symm.trans hzl
    have hlExt : F.boundaryVertex l ∈ ext.support := by
      exact hyl ▸ hyExt
    rcases hboundary l hlExt with rfl | rfl
    · left; exact hyl
    · right; exact hyl
  let rim : G.Walk (F.boundaryVertex j) (F.boundaryVertex j) :=
    ext.append q.reverse
  have hrim : rim.IsCycle := by
    exact SimpleGraph.Walk.IsPath.isCycle_append_reverse_of_meet_only_ends_local
      hext hq hxext hxj hxk hmeet
  have hxrim : x ∈ rim.support := by
    exact SimpleGraph.Walk.support_subset_support_append_left ext q.reverse hxext
  refine ⟨x, hxOutside, hix, rim, hrim, hxrim, ?_, ?_⟩
  · intro y hyp
    have hyq : y.1 ∈ q.support := (hpq y).1 hyp
    have hyqr : y.1 ∈ q.reverse.support := by
      simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using hyq
    exact SimpleGraph.Walk.support_subset_support_append_right ext q.reverse hyqr
  intro y hy
  constructor
  · intro hyp
    have hyq : y.1 ∈ q.support := (hpq y).1 hyp
    have hyqr : y.1 ∈ q.reverse.support := by
      simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using hyq
    exact SimpleGraph.Walk.support_subset_support_append_right ext q.reverse hyqr
  · intro hyrim
    have hyParts : y.1 ∈ ext.support ∨ y.1 ∈ q.reverse.support := by
      exact (SimpleGraph.Walk.mem_support_append_iff ext q.reverse).mp hyrim
    rcases hyParts with hyExt | hyqr
    · rcases hy with hyF | hyi
      · exact (hextF y.1 hyExt hyF).elim
      · exact (hiExt (hyi ▸ hyExt)).elim
    · have hyq : y.1 ∈ q.support := by
        simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using hyqr
      exact (hpq y).2 hyq

/-- Exceptional closure for an interior centre.  The exterior path now runs
through the third boundary vertex itself, while avoiding the centre which
is its unique fragment neighbour.  Provided the prepared path avoids that
boundary and the centre, the two paths meet only at their two common ends;
their union is an ambient cycle containing the third boundary and every old
vertex of the prepared path. -/
theorem exists_ambient_cycle_of_prepared_pinPath_through_boundary
    (hthree : IsThreeConnected G) (i j k : Fin 3)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hcover : ∀ l : Fin 3, l = i ∨ l = j ∨ l = k)
    (center : F.BaseVertex) (hcenterF : center.1 ∈ F.verts)
    (hcenterInside : center.1 ∈ F.insideNeighborFinset i)
    (hunique : (F.insideNeighborFinset i).card = 1)
    (p : F.preparedGraph.Walk (F.pin j) (F.pin k)) (hp : p.IsPath)
    (hcenterP : (.inl center : F.PreparedVertex) ∉ p.support)
    (hiP :
      (.inl ⟨F.boundaryVertex i, F.boundary_mem_base i⟩ :
        F.PreparedVertex) ∉ p.support) :
    ∃ rim : G.Walk (F.boundaryVertex j) (F.boundaryVertex j),
      rim.IsCycle ∧ F.boundaryVertex i ∈ rim.support ∧
        center.1 ∉ rim.support ∧
        ∀ y : F.BaseVertex,
          (.inl y : F.PreparedVertex) ∈ p.support → y.1 ∈ rim.support := by
  classical
  obtain ⟨ext, hext, hiExt, hcenterExt, hboundary, hextF⟩ :=
    F.exists_otherBoundary_exterior_path_through_boundary_avoiding_center
      hthree i j k hij hik hjk hcover center.1 hcenterF
        hcenterInside hunique
  obtain ⟨q, hq, hpq, hqCarrier⟩ :=
    F.exists_ambient_path_of_prepared_pinPath j k hjk p hp
  have hcenterQ : center.1 ∉ q.support := by
    intro hc
    exact hcenterP ((hpq center).2 hc)
  let bi : F.BaseVertex :=
    ⟨F.boundaryVertex i, F.boundary_mem_base i⟩
  have hiQ : F.boundaryVertex i ∉ q.support := by
    intro hi
    exact hiP ((hpq bi).2 (by simpa only [bi] using hi))
  have hjiV : F.boundaryVertex j ≠ F.boundaryVertex i :=
    F.boundaryVertex_injective.ne hij.symm
  have hikV : F.boundaryVertex i ≠ F.boundaryVertex k :=
    F.boundaryVertex_injective.ne hik
  have hmeet : ∀ y, y ∈ ext.support → y ∈ q.support →
      y = F.boundaryVertex j ∨ y = F.boundaryVertex k := by
    intro y hyExt hyq
    obtain ⟨z, hzy⟩ := hqCarrier y hyq
    have hzNotF : z.1 ∉ F.verts := by
      intro hzF
      exact hextF y hyExt (hzy ▸ hzF)
    have hzBoundary : z.1 ∈ F.boundaryFinset := by
      rcases Finset.mem_union.mp z.2 with hzF | hzB
      · exact (hzNotF hzF).elim
      · simpa [boundaryFinset] using hzB
    obtain ⟨l, hzl⟩ : ∃ l : Fin 3, z.1 = F.boundaryVertex l := by
      have hz : z.1 = F.a ∨ z.1 = F.b ∨ z.1 = F.c := by
        simpa [boundaryFinset] using hzBoundary
      rcases hz with ha | hb | hc
      · exact ⟨0, by simpa using ha⟩
      · exact ⟨1, by simpa using hb⟩
      · exact ⟨2, by simpa using hc⟩
    have hyl : y = F.boundaryVertex l := hzy.symm.trans hzl
    have hlExt : F.boundaryVertex l ∈ ext.support := hyl ▸ hyExt
    rcases hboundary l hlExt with hli | hlj | hlk
    · subst l
      exact (hiQ (hyl ▸ hyq)).elim
    · subst l
      exact Or.inl hyl
    · subst l
      exact Or.inr hyl
  let rim : G.Walk (F.boundaryVertex j) (F.boundaryVertex j) :=
    ext.append q.reverse
  have hrim : rim.IsCycle := by
    exact SimpleGraph.Walk.IsPath.isCycle_append_reverse_of_meet_only_ends_local
      hext hq hiExt hjiV.symm hikV hmeet
  have hiRim : F.boundaryVertex i ∈ rim.support :=
    SimpleGraph.Walk.support_subset_support_append_left ext q.reverse hiExt
  have hcenterRim : center.1 ∉ rim.support := by
    intro hc
    rcases (SimpleGraph.Walk.mem_support_append_iff ext q.reverse).mp hc with
      hcExt | hcQ
    · exact hcenterExt hcExt
    · exact hcenterQ (by
        simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse]
          using hcQ)
  refine ⟨rim, hrim, hiRim, hcenterRim, ?_⟩
  intro y hyp
  have hyq : y.1 ∈ q.support := (hpq y).1 hyp
  have hyqr : y.1 ∈ q.reverse.support := by
    simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using hyq
  exact SimpleGraph.Walk.support_subset_support_append_right ext q.reverse hyqr

/-- An interior fragment vertex has no new kind of neighbour in the
replacement graph.  Its neighbours are old base vertices, and every such
replacement edge is an ambient edge. -/
theorem replacement_neighbor_of_inside_center_is_old
    (q : F.BaseVertex) (hqF : q.1 ∈ F.verts)
    (hqPin : ∀ i : Fin 3, (.inl q : F.PreparedVertex) ≠ F.pin i)
    {z : F.PreparedVertex ⊕ Fin 2}
    (hqz : F.replacementGraph.Adj (.inl (.inl q)) z) :
    ∃ y : F.BaseVertex,
      z = .inl (.inl y) ∧ G.Adj q.1 y.1 := by
  rcases z with (y | j) | d
  · refine ⟨y, rfl, ?_⟩
    exact hqz.1
  · change q.1 = F.boundaryVertex j.1 at hqz
    exact (F.boundary_not_mem j.1 (hqz ▸ hqF)).elim
  · change (.inl q : F.PreparedVertex) = F.pin 0 ∨
      (.inl q : F.PreparedVertex) = F.pin 1 ∨
      (.inl q : F.PreparedVertex) = F.pin 2 at hqz
    rcases hqz with hqz | hqz | hqz
    · exact (hqPin 0 hqz).elim
    · exact (hqPin 1 hqz).elim
    · exact (hqPin 2 hqz).elim

/-- Spoke accounting for an interior centre.  Once every old vertex of a
replacement rim is known to occur on an ambient cycle, the three distinct
replacement spokes inject into ambient spokes. -/
theorem ambient_hasWheelCenteredAt_of_inside_rim_support_transfer
    (q : F.BaseVertex) (hqF : q.1 ∈ F.verts)
    (hqPin : ∀ i : Fin 3, (.inl q : F.PreparedVertex) ≠ F.pin i)
    {s : F.PreparedVertex ⊕ Fin 2}
    (rim : F.replacementGraph.Walk s s) (hrim : rim.IsCycle)
    (hqRim : (.inl (.inl q) : F.PreparedVertex ⊕ Fin 2) ∉ rim.support)
    (hthree : 3 ≤ (F.replacementGraph.neighborFinset (.inl (.inl q)) ∩
      rim.support.toFinset).card)
    {t : V} (ambientRim : G.Walk t t) (hambient : ambientRim.IsCycle)
    (hqAmbient : q.1 ∉ ambientRim.support)
    (hsupport : ∀ y : F.BaseVertex,
      (.inl (.inl y) : F.PreparedVertex ⊕ Fin 2) ∈ rim.support →
        y.1 ∈ ambientRim.support) :
    HasWheelCenteredAt G q.1 := by
  classical
  have htwo : 2 < (F.replacementGraph.neighborFinset (.inl (.inl q)) ∩
      rim.support.toFinset).card := by omega
  obtain ⟨z₁, z₂, z₃, hz₁, hz₂, hz₃, hz₁₂, hz₁₃, hz₂₃⟩ :=
    Finset.two_lt_card_iff.mp htwo
  have old_spoke (z : F.PreparedVertex ⊕ Fin 2)
      (hz : z ∈ F.replacementGraph.neighborFinset (.inl (.inl q)) ∩
        rim.support.toFinset) :
      ∃ y : F.BaseVertex, z = .inl (.inl y) ∧
        y.1 ∈ G.neighborFinset q.1 ∩ ambientRim.support.toFinset := by
    have hz' := Finset.mem_inter.mp hz
    have hqz : F.replacementGraph.Adj (.inl (.inl q)) z := by
      simpa only [SimpleGraph.mem_neighborFinset] using hz'.1
    obtain ⟨y, rfl, hqy⟩ :=
      F.replacement_neighbor_of_inside_center_is_old q hqF hqPin hqz
    refine ⟨y, rfl, ?_⟩
    rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset, List.mem_toFinset]
    refine ⟨hqy, hsupport y ?_⟩
    simpa only [List.mem_toFinset] using hz'.2
  obtain ⟨y₁, rfl, hy₁⟩ := old_spoke z₁ hz₁
  obtain ⟨y₂, rfl, hy₂⟩ := old_spoke z₂ hz₂
  obtain ⟨y₃, rfl, hy₃⟩ := old_spoke z₃ hz₃
  have hy₁₂ : y₁.1 ≠ y₂.1 := by
    intro h
    exact hz₁₂ (congrArg
      (fun y : F.BaseVertex ↦
        (.inl (.inl y) : F.PreparedVertex ⊕ Fin 2)) (Subtype.ext h))
  have hy₁₃ : y₁.1 ≠ y₃.1 := by
    intro h
    exact hz₁₃ (congrArg
      (fun y : F.BaseVertex ↦
        (.inl (.inl y) : F.PreparedVertex ⊕ Fin 2)) (Subtype.ext h))
  have hy₂₃ : y₂.1 ≠ y₃.1 := by
    intro h
    exact hz₂₃ (congrArg
      (fun y : F.BaseVertex ↦
        (.inl (.inl y) : F.PreparedVertex ⊕ Fin 2)) (Subtype.ext h))
  have hambientThree :
      2 < (G.neighborFinset q.1 ∩ ambientRim.support.toFinset).card := by
    exact Finset.two_lt_card_iff.mpr
      ⟨y₁.1, y₂.1, y₃.1, hy₁, hy₂, hy₃,
        hy₁₂, hy₁₃, hy₂₃⟩
  exact ⟨t, ambientRim, hambient, hqAmbient, by omega⟩

/-- Spoke-local form of the preceding transfer.  It is enough to preserve
the old rim vertices which are actually adjacent to the centre.  This is
used when a two-new-vertex rim has a singleton old pin which is not a
spoke and therefore need not occur on the chosen ambient closure. -/
theorem ambient_hasWheelCenteredAt_of_inside_spoke_support_transfer
    (q : F.BaseVertex) (hqF : q.1 ∈ F.verts)
    (hqPin : ∀ i : Fin 3, (.inl q : F.PreparedVertex) ≠ F.pin i)
    {s : F.PreparedVertex ⊕ Fin 2}
    (rim : F.replacementGraph.Walk s s) (hrim : rim.IsCycle)
    (hqRim : (.inl (.inl q) : F.PreparedVertex ⊕ Fin 2) ∉ rim.support)
    (hthree : 3 ≤ (F.replacementGraph.neighborFinset (.inl (.inl q)) ∩
      rim.support.toFinset).card)
    {t : V} (ambientRim : G.Walk t t) (hambient : ambientRim.IsCycle)
    (hqAmbient : q.1 ∉ ambientRim.support)
    (hsupport : ∀ y : F.BaseVertex,
      F.replacementGraph.Adj (.inl (.inl q)) (.inl (.inl y)) →
      (.inl (.inl y) : F.PreparedVertex ⊕ Fin 2) ∈ rim.support →
        y.1 ∈ ambientRim.support) :
    HasWheelCenteredAt G q.1 := by
  classical
  have htwo : 2 < (F.replacementGraph.neighborFinset (.inl (.inl q)) ∩
      rim.support.toFinset).card := by omega
  obtain ⟨z₁, z₂, z₃, hz₁, hz₂, hz₃, hz₁₂, hz₁₃, hz₂₃⟩ :=
    Finset.two_lt_card_iff.mp htwo
  have old_spoke (z : F.PreparedVertex ⊕ Fin 2)
      (hz : z ∈ F.replacementGraph.neighborFinset (.inl (.inl q)) ∩
        rim.support.toFinset) :
      ∃ y : F.BaseVertex, z = .inl (.inl y) ∧
        y.1 ∈ G.neighborFinset q.1 ∩ ambientRim.support.toFinset := by
    have hz' := Finset.mem_inter.mp hz
    have hqz : F.replacementGraph.Adj (.inl (.inl q)) z := by
      simpa only [SimpleGraph.mem_neighborFinset] using hz'.1
    obtain ⟨y, rfl, hqy⟩ :=
      F.replacement_neighbor_of_inside_center_is_old q hqF hqPin hqz
    refine ⟨y, rfl, ?_⟩
    rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset, List.mem_toFinset]
    refine ⟨hqy, hsupport y hqz ?_⟩
    simpa only [List.mem_toFinset] using hz'.2
  obtain ⟨y₁, rfl, hy₁⟩ := old_spoke z₁ hz₁
  obtain ⟨y₂, rfl, hy₂⟩ := old_spoke z₂ hz₂
  obtain ⟨y₃, rfl, hy₃⟩ := old_spoke z₃ hz₃
  have hy₁₂ : y₁.1 ≠ y₂.1 := by
    intro h
    exact hz₁₂ (congrArg
      (fun y : F.BaseVertex ↦
        (.inl (.inl y) : F.PreparedVertex ⊕ Fin 2)) (Subtype.ext h))
  have hy₁₃ : y₁.1 ≠ y₃.1 := by
    intro h
    exact hz₁₃ (congrArg
      (fun y : F.BaseVertex ↦
        (.inl (.inl y) : F.PreparedVertex ⊕ Fin 2)) (Subtype.ext h))
  have hy₂₃ : y₂.1 ≠ y₃.1 := by
    intro h
    exact hz₂₃ (congrArg
      (fun y : F.BaseVertex ↦
        (.inl (.inl y) : F.PreparedVertex ⊕ Fin 2)) (Subtype.ext h))
  have hambientThree :
      2 < (G.neighborFinset q.1 ∩ ambientRim.support.toFinset).card := by
    exact Finset.two_lt_card_iff.mpr
      ⟨y₁.1, y₂.1, y₃.1, hy₁, hy₂, hy₃,
        hy₁₂, hy₁₃, hy₂₃⟩
  exact ⟨t, ambientRim, hambient, hqAmbient, by omega⟩

/-- Wheel transfer for an interior centre when the replacement rim contains
exactly one of `d,d'`.  Cutting at that vertex gives a prepared path between
two pins; closing that path through the third boundary preserves every old
rim vertex and hence all three spokes. -/
theorem ambient_hasWheelCenteredAt_of_replacement_cycle_contains_exactly_one_new
    (hthreeConnected : IsThreeConnected G)
    (q : F.BaseVertex) (hqF : q.1 ∈ F.verts)
    (hqPin : ∀ i : Fin 3, (.inl q : F.PreparedVertex) ≠ F.pin i)
    {s : F.PreparedVertex ⊕ Fin 2}
    (rim : F.replacementGraph.Walk s s) (hrim : rim.IsCycle)
    (hqRim : (.inl (.inl q) : F.PreparedVertex ⊕ Fin 2) ∉ rim.support)
    (hthree : 3 ≤ (F.replacementGraph.neighborFinset (.inl (.inl q)) ∩
      rim.support.toFinset).card)
    (d e : Fin 2) (hde : d ≠ e) (hfin : ∀ f : Fin 2, f = d ∨ f = e)
    (hd : (.inr d : F.PreparedVertex ⊕ Fin 2) ∈ rim.support)
    (he : (.inr e : F.PreparedVertex ⊕ Fin 2) ∉ rim.support) :
    HasWheelCenteredAt G q.1 := by
  classical
  obtain ⟨y, z, hyPin, hzPin, hyz, p, hp, hpSupport⟩ :=
    ahtDoublePinReplacement.exists_old_pinPath_of_cycle_contains_exactly_one_new
      rim hrim d e hde hfin hd he
  obtain ⟨j, hj⟩ : ∃ j : Fin 3, y = F.pin j := by
    rcases hyPin with rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
  obtain ⟨k, hk⟩ : ∃ k : Fin 3, z = F.pin k := by
    rcases hzPin with rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
  subst y
  subst z
  have hjk : j ≠ k := by
    intro hjk
    subst k
    exact hyz rfl
  obtain ⟨i, hij, hik, hcover⟩ : ∃ i : Fin 3, i ≠ j ∧ i ≠ k ∧
      ∀ l : Fin 3, l = i ∨ l = j ∨ l = k := by
    have hmissing : ∀ j k : Fin 3, j ≠ k →
        ∃ i : Fin 3, i ≠ j ∧ i ≠ k ∧
          ∀ l : Fin 3, l = i ∨ l = j ∨ l = k := by decide
    exact hmissing j k hjk
  obtain ⟨x, hxOutside, hix, ambientRim, hambient, hxAmbient,
      hpAmbient, hpAmbientExact⟩ :=
    F.exists_ambient_cycle_of_prepared_pinPath hthreeConnected
      i j k hij hik hjk hcover p hp
  have hqp : (.inl q : F.PreparedVertex) ∉ p.support := by
    intro hqp
    exact hqRim ((hpSupport (.inl q)).1 hqp)
  have hqAmbient : q.1 ∉ ambientRim.support := by
    intro hq
    exact hqp ((hpAmbientExact q (Or.inl hqF)).2 hq)
  apply F.ambient_hasWheelCenteredAt_of_inside_rim_support_transfer
    q hqF hqPin rim hrim hqRim hthree ambientRim hambient hqAmbient
  intro w hw
  exact hpAmbient w ((hpSupport (.inl w)).2 hw)

/-- When both artificial vertices occur on a replacement rim around an old
non-pin centre, the four gadget edges leave one trivial pin piece and one
genuine path between the other two pins.  The wheel has three rim neighbours,
so the two pieces cannot both be trivial.  This packages the precise cyclic
order needed in the remaining branch of the Lemma 6.4 wheel transfer. -/
theorem exists_nontrivial_prepared_pinPath_of_cycle_contains_both_new
    (q : F.BaseVertex)
    (hqPin : ∀ i : Fin 3, (.inl q : F.PreparedVertex) ≠ F.pin i)
    {s : F.PreparedVertex ⊕ Fin 2}
    (rim : F.replacementGraph.Walk s s) (hrim : rim.IsCycle)
    (hthree : 3 ≤ (F.replacementGraph.neighborFinset (.inl (.inl q)) ∩
      rim.support.toFinset).card)
    (d e : Fin 2) (hde : d ≠ e) (hfin : ∀ f : Fin 2, f = d ∨ f = e)
    (hd : (.inr d : F.PreparedVertex ⊕ Fin 2) ∈ rim.support)
    (he : (.inr e : F.PreparedVertex ⊕ Fin 2) ∈ rim.support) :
    ∃ i j k : Fin 3,
      i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      (∀ l : Fin 3, l = i ∨ l = j ∨ l = k) ∧
      ∃ p : F.preparedGraph.Walk (F.pin j) (F.pin k),
        p.IsPath ∧ F.pin j ≠ F.pin k ∧
        ∀ w : F.PreparedVertex,
          (.inl w : F.PreparedVertex ⊕ Fin 2) ∈ rim.support ↔
            w = F.pin i ∨ w ∈ p.support := by
  classical
  obtain ⟨y, z, u, v, hyPin, hzPin, huPin, hvPin, hyz, huv,
      pLeft, hpLeft, pRight, hpRight, hdirect, hpSupport⟩ :=
    ahtDoublePinReplacement.exists_old_pinPaths_of_cycle_contains_both_new
      rim hrim d e hde hfin hd he
  obtain ⟨iy, rfl⟩ : ∃ iy : Fin 3, y = F.pin iy := by
    rcases hyPin with rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
  obtain ⟨iz, rfl⟩ : ∃ iz : Fin 3, z = F.pin iz := by
    rcases hzPin with rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
  obtain ⟨iu, rfl⟩ : ∃ iu : Fin 3, u = F.pin iu := by
    rcases huPin with rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
  obtain ⟨iv, rfl⟩ : ∃ iv : Fin 3, v = F.pin iv := by
    rcases hvPin with rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
  have hpinInjective : Function.Injective F.pin := by
    intro r t hrt
    by_contra hne
    exact F.pin_ne hne hrt
  have hiyiz : iy ≠ iz := by
    intro h
    exact hyz (congrArg F.pin h)
  have hiuiv : iu ≠ iv := by
    intro h
    exact huv (congrArg F.pin h)
  have hdirectIndex : iy = iu ∨ iv = iz := by
    rcases hdirect with h | h
    · exact Or.inl (hpinInjective h)
    · exact Or.inr (hpinInjective h)
  have not_both_trivial : ¬(iy = iu ∧ iv = iz) := by
    rintro ⟨hleft, hright⟩
    subst iu
    subst iz
    have hpLeftNil : pLeft = .nil :=
      SimpleGraph.Walk.isPath_iff_eq_nil.mp hpLeft
    have hpRightNil : pRight = .nil :=
      SimpleGraph.Walk.isPath_iff_eq_nil.mp hpRight
    have hsub :
        F.replacementGraph.neighborFinset (.inl (.inl q)) ∩
            rim.support.toFinset ⊆
          {(.inl (F.pin iy) : F.PreparedVertex ⊕ Fin 2),
            .inl (F.pin iv)} := by
      intro w hw
      have hw' := Finset.mem_inter.1 hw
      have hqw : F.replacementGraph.Adj (.inl (.inl q)) w := by
        simpa only [SimpleGraph.mem_neighborFinset] using hw'.1
      rcases w with w | f
      · have hwrim :
            (.inl w : F.PreparedVertex ⊕ Fin 2) ∈ rim.support := by
          simpa only [List.mem_toFinset] using hw'.2
        have hwparts := (hpSupport w).1 hwrim
        rw [hpLeftNil, hpRightNil] at hwparts
        simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hwparts
        rcases hwparts with rfl | rfl <;> simp
      · have hqf :=
          ahtDoublePinReplacement.adj_old_new_iff.mp hqw
        rcases hqf with hqf | hqf | hqf
        · exact (hqPin 0 hqf).elim
        · exact (hqPin 1 hqf).elim
        · exact (hqPin 2 hqf).elim
    have hcard := Finset.card_le_card hsub
    have hpairCard :
        ({(.inl (F.pin iy) : F.PreparedVertex ⊕ Fin 2),
          .inl (F.pin iv)} : Finset (F.PreparedVertex ⊕ Fin 2)).card ≤ 2 := by
      exact Finset.card_le_two
    omega
  rcases hdirectIndex with hleft | hright
  · have hrightNe : iv ≠ iz := by
      intro h
      exact not_both_trivial ⟨hleft, h⟩
    subst iu
    have hiyiv : iy ≠ iv := by
      intro h
      exact hiuiv h
    have hcover : ∀ l : Fin 3, l = iy ∨ l = iv ∨ l = iz := by
      have hcomplete : ∀ a b c : Fin 3,
          a ≠ b → a ≠ c → b ≠ c →
            ∀ l : Fin 3, l = a ∨ l = b ∨ l = c := by decide
      exact hcomplete iy iv iz hiyiv hiyiz hrightNe
    have hpLeftNil : pLeft = .nil :=
      SimpleGraph.Walk.isPath_iff_eq_nil.mp hpLeft
    refine ⟨iy, iv, iz, hiyiv, hiyiz, hrightNe, hcover,
      pRight, hpRight, F.pin_ne hrightNe, ?_⟩
    intro w
    constructor
    · intro hw
      have hw' := (hpSupport w).1 hw
      rw [hpLeftNil] at hw'
      simpa only [SimpleGraph.Walk.support_nil, List.mem_singleton] using hw'
    · intro hw
      apply (hpSupport w).2
      rw [hpLeftNil]
      simpa only [SimpleGraph.Walk.support_nil, List.mem_singleton] using hw
  · have hleftNe : iy ≠ iu := by
      intro h
      exact not_both_trivial ⟨h, hright⟩
    subst iz
    have hiviy : iv ≠ iy := by
      intro h
      exact hiyiz h.symm
    have hiviu : iv ≠ iu := hiuiv.symm
    have hcover : ∀ l : Fin 3, l = iv ∨ l = iy ∨ l = iu := by
      have hcomplete : ∀ a b c : Fin 3,
          a ≠ b → a ≠ c → b ≠ c →
            ∀ l : Fin 3, l = a ∨ l = b ∨ l = c := by decide
      exact hcomplete iv iy iu hiviy hiviu hleftNe
    have hpRightNil : pRight = .nil :=
      SimpleGraph.Walk.isPath_iff_eq_nil.mp hpRight
    refine ⟨iv, iy, iu, hiviy, hiviu, hleftNe, hcover,
      pLeft, hpLeft, F.pin_ne hleftNe, ?_⟩
    intro w
    constructor
    · intro hw
      have hw' := (hpSupport w).1 hw
      rw [hpRightNil] at hw'
      simpa only [SimpleGraph.Walk.support_nil, List.mem_singleton, or_comm]
        using hw'
    · intro hw
      apply (hpSupport w).2
      rw [hpRightNil]
      simpa only [SimpleGraph.Walk.support_nil, List.mem_singleton, or_comm]
        using hw

/-- Wheel transfer for an interior centre when both artificial vertices lie
on the replacement rim.  The rim decomposition has one singleton pin and
one genuine pin-to-pin path.  If the singleton is not a spoke, ordinary
exterior closure preserves all three spokes.  If it is a spoke, it is an
identified boundary pin whose unique fragment neighbour is the centre; an
exterior path through that boundary in `G - q` gives the required closure. -/
theorem ambient_hasWheelCenteredAt_of_replacement_cycle_contains_both_new
    (hthreeConnected : IsThreeConnected G)
    (q : F.BaseVertex) (hqF : q.1 ∈ F.verts)
    (hqPin : ∀ i : Fin 3, (.inl q : F.PreparedVertex) ≠ F.pin i)
    {s : F.PreparedVertex ⊕ Fin 2}
    (rim : F.replacementGraph.Walk s s) (hrim : rim.IsCycle)
    (hqRim : (.inl (.inl q) : F.PreparedVertex ⊕ Fin 2) ∉ rim.support)
    (hthree : 3 ≤ (F.replacementGraph.neighborFinset (.inl (.inl q)) ∩
      rim.support.toFinset).card)
    (d e : Fin 2) (hde : d ≠ e) (hfin : ∀ f : Fin 2, f = d ∨ f = e)
    (hd : (.inr d : F.PreparedVertex ⊕ Fin 2) ∈ rim.support)
    (he : (.inr e : F.PreparedVertex ⊕ Fin 2) ∈ rim.support) :
    HasWheelCenteredAt G q.1 := by
  classical
  obtain ⟨i, j, k, hij, hik, hjk, hcover, p, hp, -, hpSupport⟩ :=
    F.exists_nontrivial_prepared_pinPath_of_cycle_contains_both_new
      q hqPin rim hrim hthree d e hde hfin hd he
  have hpSub : ∀ w ∈ p.support,
      (.inl w : F.PreparedVertex ⊕ Fin 2) ∈ rim.support := by
    intro w hw
    exact (hpSupport w).2 (Or.inr hw)
  have hqP : (.inl q : F.PreparedVertex) ∉ p.support := by
    intro hq
    exact hqRim (hpSub (.inl q) hq)
  let bi : F.BaseVertex :=
    ⟨F.boundaryVertex i, F.boundary_mem_base i⟩
  by_cases hqi : F.replacementGraph.Adj
      (.inl (.inl q)) (.inl (F.pin i))
  · obtain ⟨y, hpinY, hqy⟩ :=
      F.replacement_neighbor_of_inside_center_is_old q hqF hqPin hqi
    have hpinY' : F.pin i = (.inl y : F.PreparedVertex) :=
      Sum.inl.inj hpinY
    have hiFresh : ¬F.NeedsFreshPin i := by
      intro hi
      have : (.inr ⟨i, hi⟩ : F.PreparedVertex) = .inl y := by
        simpa [pin, hi] using hpinY'
      exact Sum.inr_ne_inl this
    have hpinBi : F.pin i = (.inl bi : F.PreparedVertex) := by
      simp [pin, hiFresh, bi]
    have hybi : y = bi := by
      exact Sum.inl.inj (hpinY'.symm.trans hpinBi)
    have hqBoundary : G.Adj q.1 (F.boundaryVertex i) := by
      simpa only [hybi, bi] using hqy
    have hqInside : q.1 ∈ F.insideNeighborFinset i := by
      simp only [insideNeighborFinset, Finset.mem_inter,
        SimpleGraph.mem_neighborFinset]
      exact ⟨hqBoundary.symm, hqF⟩
    have hunique : (F.insideNeighborFinset i).card = 1 :=
      F.insideNeighborFinset_card_eq_one_of_not_needsFreshPin i hiFresh
    by_cases hiP : (.inl bi : F.PreparedVertex) ∈ p.support
    · obtain ⟨x, hxOutside, hix, ambientRim, hambient, hxAmbient,
          hpAmbient, hpAmbientExact⟩ :=
        F.exists_ambient_cycle_of_prepared_pinPath hthreeConnected
          i j k hij hik hjk hcover p hp
      have hqAmbient : q.1 ∉ ambientRim.support := by
        intro hq
        exact hqP ((hpAmbientExact q (Or.inl hqF)).2 hq)
      apply F.ambient_hasWheelCenteredAt_of_inside_rim_support_transfer
        q hqF hqPin rim hrim hqRim hthree ambientRim hambient hqAmbient
      intro w hw
      rcases (hpSupport (.inl w)).1 hw with hwi | hwp
      · have hwbi : w = bi := by
          exact Sum.inl.inj (hwi.trans hpinBi)
        subst w
        exact hpAmbient bi hiP
      · exact hpAmbient w hwp
    · obtain ⟨ambientRim, hambient, hiAmbient, hqAmbient,
          hpAmbient⟩ :=
        F.exists_ambient_cycle_of_prepared_pinPath_through_boundary
          hthreeConnected i j k hij hik hjk hcover q hqF hqInside
            hunique p hp hqP hiP
      apply F.ambient_hasWheelCenteredAt_of_inside_rim_support_transfer
        q hqF hqPin rim hrim hqRim hthree ambientRim hambient hqAmbient
      intro w hw
      rcases (hpSupport (.inl w)).1 hw with hwi | hwp
      · have hwbi : w = bi := by
          exact Sum.inl.inj (hwi.trans hpinBi)
        subst w
        simpa only [bi] using hiAmbient
      · exact hpAmbient w hwp
  · obtain ⟨x, hxOutside, hix, ambientRim, hambient, hxAmbient,
        hpAmbient, hpAmbientExact⟩ :=
      F.exists_ambient_cycle_of_prepared_pinPath hthreeConnected
        i j k hij hik hjk hcover p hp
    have hqAmbient : q.1 ∉ ambientRim.support := by
      intro hq
      exact hqP ((hpAmbientExact q (Or.inl hqF)).2 hq)
    apply F.ambient_hasWheelCenteredAt_of_inside_spoke_support_transfer
      q hqF hqPin rim hrim hqRim hthree ambientRim hambient hqAmbient
    intro w hqw hw
    rcases (hpSupport (.inl w)).1 hw with hwi | hwp
    · apply (hqi ?_).elim
      simpa only [hwi] using hqw
    · exact hpAmbient w hwp

/-- Complete interior-centre transfer, by the exhaustive finite split
according to the artificial vertices occurring on the replacement rim. -/
theorem replacement_hasWheelCenteredAt_inside_imp_ambient
    (hthreeConnected : IsThreeConnected G)
    (q : F.BaseVertex) (hqF : q.1 ∈ F.verts)
    (hqPin : ∀ i : Fin 3, (.inl q : F.PreparedVertex) ≠ F.pin i)
    (hwheel : HasWheelCenteredAt F.replacementGraph (.inl (.inl q))) :
    HasWheelCenteredAt G q.1 := by
  classical
  obtain ⟨s, rim, hrim, hqRim, hthree⟩ := hwheel
  by_cases h0 : (.inr 0 : F.PreparedVertex ⊕ Fin 2) ∈ rim.support
  · by_cases h1 : (.inr 1 : F.PreparedVertex ⊕ Fin 2) ∈ rim.support
    · exact F.ambient_hasWheelCenteredAt_of_replacement_cycle_contains_both_new
        hthreeConnected q hqF hqPin rim hrim hqRim hthree
          0 1 (by decide) (by intro f; fin_cases f <;> simp) h0 h1
    · exact F.ambient_hasWheelCenteredAt_of_replacement_cycle_contains_exactly_one_new
        hthreeConnected q hqF hqPin rim hrim hqRim hthree
          0 1 (by decide) (by intro f; fin_cases f <;> simp) h0 h1
  · by_cases h1 : (.inr 1 : F.PreparedVertex ⊕ Fin 2) ∈ rim.support
    · exact F.ambient_hasWheelCenteredAt_of_replacement_cycle_contains_exactly_one_new
        hthreeConnected q hqF hqPin rim hrim hqRim hthree
          1 0 (by decide) (by intro f; fin_cases f <;> simp) h1 h0
    · have havoid : ∀ d : Fin 2,
          (.inr d : F.PreparedVertex ⊕ Fin 2) ∉ rim.support := by
        intro d
        fin_cases d
        · exact h0
        · exact h1
      rcases s with r₀ | d
      · exact F.ambient_hasWheelCenteredAt_of_replacement_cycle_avoids_new
          (x := q) (r₀ := r₀) rim hrim hqRim hthree havoid
      · exact (havoid d rim.start_mem_support).elim

/-- The prepared graph inherits triangle-freeness from the ambient graph.
The only new vertices are pendant, and all edges among boundary vertices were
deleted. -/
theorem prepared_triangleFree (htri : AHTTriangleFree G) :
    AHTTriangleFree F.preparedGraph := by
  intro x y z hxy hyz hzx
  rcases x with x | i <;> rcases y with y | j <;> rcases z with z | k
  · exact htri hxy.1 hyz.1 hzx.1
  · have hy : y.1 = F.boundaryVertex k.1 := hyz
    have hx : x.1 = F.boundaryVertex k.1 := hzx
    exact hxy.1.ne (hx.trans hy.symm)
  · have hx : x.1 = F.boundaryVertex j.1 := hxy
    have hz : z.1 = F.boundaryVertex j.1 := hyz
    exact hzx.1.ne (hz.trans hx.symm)
  · exact hyz
  · have hy : y.1 = F.boundaryVertex i.1 := hxy
    have hz : z.1 = F.boundaryVertex i.1 := hzx
    exact hyz.1.ne (hy.trans hz.symm)
  · exact hzx
  · exact hxy
  · exact hxy

theorem pins_independent (p q : F.PreparedVertex)
    (hp : p = F.pin 0 ∨ p = F.pin 1 ∨ p = F.pin 2)
    (hq : q = F.pin 0 ∨ q = F.pin 1 ∨ q = F.pin 2) :
    ¬F.preparedGraph.Adj p q := by
  rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl
  · exact F.preparedGraph.loopless.irrefl _
  · exact F.not_adj_pin (by decide)
  · exact F.not_adj_pin (by decide)
  · exact fun h ↦ F.not_adj_pin (by decide) h.symm
  · exact F.preparedGraph.loopless.irrefl _
  · exact F.not_adj_pin (by decide)
  · exact fun h ↦ F.not_adj_pin (by decide) h.symm
  · exact fun h ↦ F.not_adj_pin (by decide) h.symm
  · exact F.preparedGraph.loopless.irrefl _

/-- The exact graph `G_F` is triangle-free whenever the ambient graph is.
This is the local triangle check in the proof of AHT Lemma 6.4. -/
theorem replacement_triangleFree (htri : AHTTriangleFree G) :
    AHTTriangleFree F.replacementGraph := by
  exact ahtDoublePinReplacement.triangleFree
    (F.prepared_triangleFree htri) F.pins_independent

/-- The source-exact exclusion of the two newly added vertices `d,d'` from
the wheel-centre set of `G_F`. -/
theorem replacement_not_hasWheelCenteredAt_new (i : Fin 2) :
    ¬HasWheelCenteredAt F.replacementGraph (.inr i) := by
  exact ahtDoublePinReplacement.not_hasWheelCenteredAt_new
    (F.pin_ne (by decide : (0 : Fin 3) ≠ 1))
    (F.pin_ne (by decide : (0 : Fin 3) ≠ 2))
    (F.pin_ne (by decide : (1 : Fin 3) ≠ 2))
    (F.degree_pin 0) (F.degree_pin 1) (F.degree_pin 2) i

/-- No distinguished pin can become a wheel centre after `d,d'` are
adjoined.  On an alleged rim, both artificial vertices have as their two rim
neighbours the other two pins.  Those four vertices therefore form a set
closed under rim adjacency.  Since the rim is connected, it cannot also
contain the unique prepared neighbour of the centre pin. -/
theorem replacement_not_hasWheelCenteredAt_pin_of_other_indices
    (i j k : Fin 3)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hcover : ∀ l : Fin 3, l = i ∨ l = j ∨ l = k) :
    ¬HasWheelCenteredAt F.replacementGraph (.inl (F.pin i)) := by
  classical
  let R := F.replacementGraph
  intro hw
  obtain ⟨r, rim, hcycle, hcenterNotRim, hthree⟩ := hw
  have hcenterAmong :
      F.pin i = F.pin 0 ∨ F.pin i = F.pin 1 ∨ F.pin i = F.pin 2 := by
    fin_cases i <;> simp
  have hcenterDegree : R.degree (.inl (F.pin i)) = 3 := by
    exact ahtDoublePinReplacement.degree_old_pin_eq_three
      hcenterAmong (F.degree_pin i)
  have hinterEq :
      R.neighborFinset (.inl (F.pin i)) ∩ rim.support.toFinset =
        R.neighborFinset (.inl (F.pin i)) := by
    apply Finset.eq_of_subset_of_card_le Finset.inter_subset_left
    simpa [R, hcenterDegree] using hthree
  have hneighborsSupport :
      R.neighborFinset (.inl (F.pin i)) ⊆ rim.support.toFinset := by
    intro z hz
    have hz' : z ∈
        R.neighborFinset (.inl (F.pin i)) ∩ rim.support.toFinset := by
      rw [hinterEq]
      exact hz
    exact (Finset.mem_inter.1 hz').2
  obtain ⟨t, htN⟩ : (F.preparedGraph.neighborFinset (F.pin i)).Nonempty := by
    rw [← Finset.card_pos, F.preparedGraph.card_neighborFinset_eq_degree,
      F.degree_pin]
    decide
  have htAdj : F.preparedGraph.Adj (F.pin i) t := by
    simpa [SimpleGraph.mem_neighborFinset] using htN
  have htSupport :
      (.inl t : F.PreparedVertex ⊕ Fin 2) ∈ rim.support := by
    have ht : (.inl t : F.PreparedVertex ⊕ Fin 2) ∈ rim.support.toFinset := by
      apply hneighborsSupport
      rw [SimpleGraph.mem_neighborFinset]
      exact htAdj
    simpa using ht
  have hnewSupport (d : Fin 2) :
      (.inr d : F.PreparedVertex ⊕ Fin 2) ∈ rim.support := by
    have hd : (.inr d : F.PreparedVertex ⊕ Fin 2) ∈ rim.support.toFinset := by
      apply hneighborsSupport
      rw [SimpleGraph.mem_neighborFinset]
      change R.Adj (.inl (F.pin i)) (.inr d)
      exact ahtDoublePinReplacement.adj_old_new_iff.mpr hcenterAmong
    simpa using hd
  have new_neighborSet_eq_other_pins (d : Fin 2) :
      rim.toSubgraph.neighborSet (.inr d) =
        {(.inl (F.pin j) : F.PreparedVertex ⊕ Fin 2), .inl (F.pin k)} := by
    apply Set.eq_of_subset_of_ncard_le (ht := by toFinite_tac)
    · intro z hz
      have hzR : R.Adj (.inr d) z := hz.adj_sub
      rcases z with p | e
      · have hp := ahtDoublePinReplacement.adj_new_old_iff.mp hzR
        obtain ⟨l, hpl⟩ : ∃ l : Fin 3, p = F.pin l := by
          rcases hp with hp | hp | hp
          · exact ⟨0, hp⟩
          · exact ⟨1, hp⟩
          · exact ⟨2, hp⟩
        subst p
        have hli : l ≠ i := by
          intro hli
          subst l
          have hiSupport :
              (.inl (F.pin i) : F.PreparedVertex ⊕ Fin 2) ∈ rim.support :=
            rim.mem_verts_toSubgraph.mp hz.snd_mem
          exact hcenterNotRim hiSupport
        rcases hcover l with hli' | hlj | hlk
        · exact (hli hli').elim
        · subst l
          simp
        · subst l
          simp
      · exact (ahtDoublePinReplacement.not_adj_new_new d e hzR).elim
    · have htwo := hcycle.ncard_neighborSet_toSubgraph_eq_two (hnewSupport d)
      rw [Set.ncard_pair (Sum.inl_injective.ne (F.pin_ne hjk))]
      omega
  have h0j : rim.toSubgraph.Adj (.inr 0) (.inl (F.pin j)) := by
    have : (.inl (F.pin j) : F.PreparedVertex ⊕ Fin 2) ∈
        rim.toSubgraph.neighborSet (.inr 0) := by
      rw [new_neighborSet_eq_other_pins 0]
      simp
    exact this
  have h0k : rim.toSubgraph.Adj (.inr 0) (.inl (F.pin k)) := by
    have : (.inl (F.pin k) : F.PreparedVertex ⊕ Fin 2) ∈
        rim.toSubgraph.neighborSet (.inr 0) := by
      rw [new_neighborSet_eq_other_pins 0]
      simp
    exact this
  have h1j : rim.toSubgraph.Adj (.inr 1) (.inl (F.pin j)) := by
    have : (.inl (F.pin j) : F.PreparedVertex ⊕ Fin 2) ∈
        rim.toSubgraph.neighborSet (.inr 1) := by
      rw [new_neighborSet_eq_other_pins 1]
      simp
    exact this
  have h1k : rim.toSubgraph.Adj (.inr 1) (.inl (F.pin k)) := by
    have : (.inl (F.pin k) : F.PreparedVertex ⊕ Fin 2) ∈
        rim.toSubgraph.neighborSet (.inr 1) := by
      rw [new_neighborSet_eq_other_pins 1]
      simp
    exact this
  have rim_neighborSet_eq_pair {x y z : F.PreparedVertex ⊕ Fin 2}
      (hx : x ∈ rim.support) (hxy : rim.toSubgraph.Adj x y)
      (hxz : rim.toSubgraph.Adj x z) (hyz : y ≠ z) :
      rim.toSubgraph.neighborSet x = {y, z} := by
    have hsub : ({y, z} : Set (F.PreparedVertex ⊕ Fin 2)) ⊆
        rim.toSubgraph.neighborSet x := by
      intro w hw
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with rfl | rfl
      · simpa only [SimpleGraph.Subgraph.mem_neighborSet] using hxy
      · simpa only [SimpleGraph.Subgraph.mem_neighborSet] using hxz
    have heq : ({y, z} : Set (F.PreparedVertex ⊕ Fin 2)) =
        rim.toSubgraph.neighborSet x := by
      apply Set.eq_of_subset_of_ncard_le hsub
      rw [hcycle.ncard_neighborSet_toSubgraph_eq_two hx,
        Set.ncard_pair hyz]
    exact heq.symm
  have hjNeighbors : rim.toSubgraph.neighborSet (.inl (F.pin j)) =
      {(.inr 0 : F.PreparedVertex ⊕ Fin 2), .inr 1} := by
    apply rim_neighborSet_eq_pair
    · exact rim.mem_verts_toSubgraph.mp h0j.snd_mem
    · exact h0j.symm
    · exact h1j.symm
    · exact Sum.inr_injective.ne (by decide : (0 : Fin 2) ≠ 1)
  have hkNeighbors : rim.toSubgraph.neighborSet (.inl (F.pin k)) =
      {(.inr 0 : F.PreparedVertex ⊕ Fin 2), .inr 1} := by
    apply rim_neighborSet_eq_pair
    · exact rim.mem_verts_toSubgraph.mp h0k.snd_mem
    · exact h0k.symm
    · exact h1k.symm
    · exact Sum.inr_injective.ne (by decide : (0 : Fin 2) ≠ 1)
  let S : Set (F.PreparedVertex ⊕ Fin 2) :=
    {(.inr 0), .inr 1, .inl (F.pin j), .inl (F.pin k)}
  have hnew0S : (.inr 0 : F.PreparedVertex ⊕ Fin 2) ∈ S :=
    Set.mem_insert _ _
  have hnew1S : (.inr 1 : F.PreparedVertex ⊕ Fin 2) ∈ S :=
    Set.mem_insert_of_mem _ (Set.mem_insert _ _)
  have hjS : (.inl (F.pin j) : F.PreparedVertex ⊕ Fin 2) ∈ S :=
    Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have hkS : (.inl (F.pin k) : F.PreparedVertex ⊕ Fin 2) ∈ S :=
    Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
      (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  have hclosed : ∀ x ∈ S, rim.toSubgraph.neighborSet x ⊆ S := by
    intro x hx
    simp only [S, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · rw [new_neighborSet_eq_other_pins 0]
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact hjS
      · exact hkS
    · rw [new_neighborSet_eq_other_pins 1]
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact hjS
      · exact hkS
    · rw [hjNeighbors]
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact hnew0S
      · exact hnew1S
    · rw [hkNeighbors]
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact hnew0S
      · exact hnew1S
  have hsupportSub : ∀ x ∈ rim.support, x ∈ S :=
    ahtDoublePinReplacement.walk_support_subset_of_toSubgraph_neighbor_closed rim S
      (hnewSupport 0) (by simp [S]) hclosed
  have htNotS : (.inl t : F.PreparedVertex ⊕ Fin 2) ∉ S := by
    have htj : t ≠ F.pin j := by
      intro htj
      subst t
      exact F.not_adj_pin hij htAdj
    have htk : t ≠ F.pin k := by
      intro htk
      subst t
      exact F.not_adj_pin hik htAdj
    simp only [S, Set.mem_insert_iff, Set.mem_singleton_iff,
      Sum.inl.injEq, Sum.inl_ne_inr, false_or]
    exact fun h ↦ h.elim htj htk
  exact htNotS (hsupportSub _ htSupport)

/-- None of the three distinguished pins is a wheel centre. -/
theorem replacement_not_hasWheelCenteredAt_pin (i : Fin 3) :
    ¬HasWheelCenteredAt F.replacementGraph (.inl (F.pin i)) := by
  fin_cases i
  · exact F.replacement_not_hasWheelCenteredAt_pin_of_other_indices
      0 1 2 (by decide) (by decide) (by decide)
      (by intro l; fin_cases l <;> simp)
  · exact F.replacement_not_hasWheelCenteredAt_pin_of_other_indices
      1 0 2 (by decide) (by decide) (by decide)
      (by intro l; fin_cases l <;> simp)
  · exact F.replacement_not_hasWheelCenteredAt_pin_of_other_indices
      2 0 1 (by decide) (by decide) (by decide)
      (by intro l; fin_cases l <;> simp)

/-- In particular, none of the optional fresh pins is a wheel centre. -/
theorem replacement_not_hasWheelCenteredAt_freshPin (i : F.FreshPin) :
    ¬HasWheelCenteredAt F.replacementGraph (.inl (.inr i)) := by
  have hpin : F.pin i.1 = (.inr i : F.PreparedVertex) := by
    simp [pin, i.2]
  simpa [hpin] using F.replacement_not_hasWheelCenteredAt_pin i.1

/-- Every wheel centre of the replacement is an old base vertex and is not
one of the three distinguished pins.  This is the exact case split preceding
the two wheel-transfer arguments in AHT Lemma 6.4. -/
theorem replacement_wheelCenter_is_old_nonpin
    {z : F.PreparedVertex ⊕ Fin 2}
    (hz : HasWheelCenteredAt F.replacementGraph z) :
    ∃ q : F.BaseVertex, z = .inl (.inl q) ∧
      ∀ i : Fin 3, (.inl q : F.PreparedVertex) ≠ F.pin i := by
  rcases z with (q | j) | d
  · refine ⟨q, rfl, ?_⟩
    intro i hqi
    have : HasWheelCenteredAt F.replacementGraph (.inl (F.pin i)) := by
      simpa [hqi] using hz
    exact F.replacement_not_hasWheelCenteredAt_pin i this
  · exact (F.replacement_not_hasWheelCenteredAt_freshPin j hz).elim
  · exact (F.replacement_not_hasWheelCenteredAt_new d hz).elim

theorem old_nonpin_inside_or_fresh_boundary (q : F.BaseVertex)
    (hq : ∀ i : Fin 3, (.inl q : F.PreparedVertex) ≠ F.pin i) :
    q.1 ∈ F.verts ∨
      ∃ i : Fin 3,
        q = ⟨F.boundaryVertex i, F.boundary_mem_base i⟩ ∧
          F.NeedsFreshPin i := by
  rcases Finset.mem_union.mp q.2 with hqF | hqB
  · exact Or.inl hqF
  · right
    have hq' : q.1 = F.a ∨ q.1 = F.b ∨ q.1 = F.c := by
      simpa using hqB
    obtain ⟨i, hqi⟩ : ∃ i : Fin 3, q.1 = F.boundaryVertex i := by
      rcases hq' with hq' | hq'
      · exact ⟨0, by simpa using hq'⟩
      · rcases hq' with hq' | hq'
        · exact ⟨1, by simpa using hq'⟩
        · exact ⟨2, by simpa using hq'⟩
    let bi : F.BaseVertex :=
      ⟨F.boundaryVertex i, F.boundary_mem_base i⟩
    have hqbi : q = bi := Subtype.ext hqi
    refine ⟨i, hqbi, ?_⟩
    by_contra hi
    apply hq i
    rw [hqbi]
    simp [pin, hi, bi]

/-- A boundary vertex for which a fresh pin was introduced has only two
kinds of neighbours in the replacement: old fragment neighbours, and its
own fresh pin.  In particular it is adjacent to neither artificial vertex
and to no other fresh pin. -/
theorem replacement_neighbor_of_fresh_boundary_center
    (i : Fin 3) (hi : F.NeedsFreshPin i)
    (hqPin : ∀ j : Fin 3,
      (.inl ⟨F.boundaryVertex i, F.boundary_mem_base i⟩ :
        F.PreparedVertex) ≠ F.pin j)
    {z : F.PreparedVertex ⊕ Fin 2}
    (hz : F.replacementGraph.Adj
      (.inl (.inl ⟨F.boundaryVertex i, F.boundary_mem_base i⟩)) z) :
    (∃ y : F.BaseVertex, y.1 ∈ F.verts ∧
        z = .inl (.inl y) ∧ G.Adj (F.boundaryVertex i) y.1) ∨
      z = .inl (F.pin i) := by
  classical
  let qi : F.BaseVertex :=
    ⟨F.boundaryVertex i, F.boundary_mem_base i⟩
  rcases z with (y | j) | d
  · left
    have hz' : F.preparedGraph.Adj (.inl qi) (.inl y) := hz
    have hyF : y.1 ∈ F.verts := by
      rcases Finset.mem_union.mp y.2 with hyF | hyB
      · exact hyF
      · have hiB :
            F.boundaryVertex i ∈ ({F.a, F.b, F.c} : Finset V) := by
          fin_cases i <;> simp
        exact (hz'.2 ⟨hiB, hyB⟩).elim
    exact ⟨y, hyF, rfl, hz'.1⟩
  · right
    have hijV : F.boundaryVertex i = F.boundaryVertex j.1 := hz
    have hij : i = j.1 := F.boundaryVertex_injective hijV
    have hj : j = ⟨i, hi⟩ := Subtype.ext hij.symm
    subst j
    simp [pin, hi]
  · have hz' := ahtDoublePinReplacement.adj_old_new_iff.mp hz
    rcases hz' with hz' | hz' | hz'
    · exact (hqPin 0 hz').elim
    · exact (hqPin 1 hz').elim
    · exact (hqPin 2 hz').elim

/-- A prepared pin-to-pin path contained in a replacement rim avoiding a
high-inside-degree boundary centre cannot start or end at that centre's
fresh pin: its first (respectively last) prepared edge would immediately
return to the excluded boundary centre. -/
theorem fresh_boundary_index_ne_endpoints_of_pinPath_on_rim
    (i : Fin 3) (hi : F.NeedsFreshPin i)
    {s : F.PreparedVertex ⊕ Fin 2}
    (rim : F.replacementGraph.Walk s s)
    (hcenter :
      (.inl (.inl ⟨F.boundaryVertex i, F.boundary_mem_base i⟩) :
        F.PreparedVertex ⊕ Fin 2) ∉ rim.support)
    (j k : Fin 3) (hjk : j ≠ k)
    (p : F.preparedGraph.Walk (F.pin j) (F.pin k)) (hp : p.IsPath)
    (hsub : ∀ w ∈ p.support,
      (.inl w : F.PreparedVertex ⊕ Fin 2) ∈ rim.support) :
    i ≠ j ∧ i ≠ k := by
  classical
  let qi : F.BaseVertex :=
    ⟨F.boundaryVertex i, F.boundary_mem_base i⟩
  let fi : F.FreshPin := ⟨i, hi⟩
  have hpin : F.pin i = (.inr fi : F.PreparedVertex) := by
    simp [pin, hi, fi]
  have start_ne (r t : Fin 3) (hrt : r ≠ t)
      (q : F.preparedGraph.Walk (F.pin r) (F.pin t)) (hq : q.IsPath)
      (hqSub : ∀ w ∈ q.support,
        (.inl w : F.PreparedVertex ⊕ Fin 2) ∈ rim.support) : i ≠ r := by
    intro hir
    subst r
    have hqNot : ¬q.Nil :=
      SimpleGraph.Walk.not_nil_of_ne (F.pin_ne hrt)
    have hadj : F.preparedGraph.Adj (.inr fi) q.snd := by
      simpa only [hpin] using q.adj_snd hqNot
    have hsnd : q.snd = (.inl qi : F.PreparedVertex) := by
      rcases hs : q.snd with y | f
      · have hy : y.1 = F.boundaryVertex i :=
          (F.prepared_adj_fresh_old (i := fi) (q := y)).mp
            (by simpa only [hs] using hadj)
        have hyqi : y = qi := Subtype.ext hy
        simpa only [hs, hyqi]
      · exact (F.prepared_not_adj_fresh_fresh fi f
          (by simpa only [hs] using hadj)).elim
    have hsndMem : q.snd ∈ q.support :=
      List.mem_of_mem_tail (q.snd_mem_tail_support hqNot)
    have hsndRim := hqSub q.snd hsndMem
    exact hcenter (by simpa only [hsnd] using hsndRim)
  refine ⟨start_ne j k hjk p hp hsub, ?_⟩
  have hsubReverse : ∀ w ∈ p.reverse.support,
      (.inl w : F.PreparedVertex ⊕ Fin 2) ∈ rim.support := by
    intro w hw
    apply hsub w
    simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using hw
  exact start_ne k j hjk.symm p.reverse hp.reverse hsubReverse

/-- Spoke accounting for the fresh-boundary-centre case.  At most one of
three replacement spokes is the fresh pin, so two distinct old fragment
spokes survive on the ambient rim.  The exterior neighbour supplied by the
fragment side is the third ambient spoke. -/
theorem ambient_hasWheelCenteredAt_of_fresh_boundary_support_transfer
    (i : Fin 3) (hi : F.NeedsFreshPin i)
    (hqPin : ∀ j : Fin 3,
      (.inl ⟨F.boundaryVertex i, F.boundary_mem_base i⟩ :
        F.PreparedVertex) ≠ F.pin j)
    {s : F.PreparedVertex ⊕ Fin 2}
    (rim : F.replacementGraph.Walk s s) (hrim : rim.IsCycle)
    (hcenterRim :
      (.inl (.inl ⟨F.boundaryVertex i, F.boundary_mem_base i⟩) :
        F.PreparedVertex ⊕ Fin 2) ∉ rim.support)
    (hthree : 3 ≤
      (F.replacementGraph.neighborFinset
          (.inl (.inl ⟨F.boundaryVertex i, F.boundary_mem_base i⟩)) ∩
        rim.support.toFinset).card)
    {t x : V} (ambientRim : G.Walk t t) (hambient : ambientRim.IsCycle)
    (hcenterAmbient : F.boundaryVertex i ∉ ambientRim.support)
    (hxF : x ∈ Finset.univ \ (F.verts ∪ F.boundaryFinset))
    (hix : G.Adj (F.boundaryVertex i) x)
    (hxAmbient : x ∈ ambientRim.support)
    (hsupport : ∀ y : F.BaseVertex,
      y.1 ∈ F.verts →
      (.inl (.inl y) : F.PreparedVertex ⊕ Fin 2) ∈ rim.support →
      y.1 ∈ ambientRim.support) :
    HasWheelCenteredAt G (F.boundaryVertex i) := by
  classical
  have htwo : 2 <
      (F.replacementGraph.neighborFinset
          (.inl (.inl ⟨F.boundaryVertex i, F.boundary_mem_base i⟩)) ∩
        rim.support.toFinset).card := by omega
  obtain ⟨z₁, z₂, z₃, hz₁, hz₂, hz₃, hz₁₂, hz₁₃, hz₂₃⟩ :=
    Finset.two_lt_card_iff.mp htwo
  have classify (z : F.PreparedVertex ⊕ Fin 2)
      (hz : z ∈ F.replacementGraph.neighborFinset
          (.inl (.inl ⟨F.boundaryVertex i, F.boundary_mem_base i⟩)) ∩
        rim.support.toFinset) :
      (∃ y : F.BaseVertex, y.1 ∈ F.verts ∧
        z = .inl (.inl y) ∧
        y.1 ∈ G.neighborFinset (F.boundaryVertex i) ∩
          ambientRim.support.toFinset) ∨
      z = .inl (F.pin i) := by
    have hz' := Finset.mem_inter.1 hz
    have hadj : F.replacementGraph.Adj
        (.inl (.inl ⟨F.boundaryVertex i, F.boundary_mem_base i⟩)) z := by
      simpa only [SimpleGraph.mem_neighborFinset] using hz'.1
    rcases F.replacement_neighbor_of_fresh_boundary_center i hi hqPin hadj with
      ⟨y, hyF, rfl, hiy⟩ | hpin
    · left
      refine ⟨y, hyF, rfl, ?_⟩
      rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
        List.mem_toFinset]
      refine ⟨hiy, hsupport y hyF ?_⟩
      simpa only [List.mem_toFinset] using hz'.2
    · exact Or.inr hpin
  have finish {z w : F.PreparedVertex ⊕ Fin 2} (hzw : z ≠ w)
      {y r : F.BaseVertex}
      (hyF : y.1 ∈ F.verts) (hz : z = .inl (.inl y))
      (hy : y.1 ∈ G.neighborFinset (F.boundaryVertex i) ∩
        ambientRim.support.toFinset)
      (hrF : r.1 ∈ F.verts) (hw : w = .inl (.inl r))
      (hr : r.1 ∈ G.neighborFinset (F.boundaryVertex i) ∩
        ambientRim.support.toFinset) :
      HasWheelCenteredAt G (F.boundaryVertex i) := by
    have hyr : y.1 ≠ r.1 := by
      intro hyr
      apply hzw
      rw [hz, hw]
      exact congrArg (fun a : F.BaseVertex ↦
        (.inl (.inl a) : F.PreparedVertex ⊕ Fin 2)) (Subtype.ext hyr)
    have hyx : y.1 ≠ x := by
      intro hyx
      subst x
      exact (Finset.mem_sdiff.1 hxF).2 (Finset.mem_union_left _ hyF)
    have hrx : r.1 ≠ x := by
      intro hrx
      subst x
      exact (Finset.mem_sdiff.1 hxF).2 (Finset.mem_union_left _ hrF)
    have hx : x ∈ G.neighborFinset (F.boundaryVertex i) ∩
        ambientRim.support.toFinset := by
      rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
        List.mem_toFinset]
      exact ⟨hix, hxAmbient⟩
    have hcard : 2 <
        (G.neighborFinset (F.boundaryVertex i) ∩
          ambientRim.support.toFinset).card :=
      Finset.two_lt_card_iff.mpr
        ⟨y.1, r.1, x, hy, hr, hx, hyr, hyx, hrx⟩
    exact ⟨t, ambientRim, hambient, hcenterAmbient, by omega⟩
  rcases classify z₁ hz₁ with ⟨y₁, hy₁F, hz₁', hy₁⟩ | hz₁'
  · rcases classify z₂ hz₂ with ⟨y₂, hy₂F, hz₂', hy₂⟩ | hz₂'
    · exact finish hz₁₂ hy₁F hz₁' hy₁ hy₂F hz₂' hy₂
    · rcases classify z₃ hz₃ with ⟨y₃, hy₃F, hz₃', hy₃⟩ | hz₃'
      · exact finish hz₁₃ hy₁F hz₁' hy₁ hy₃F hz₃' hy₃
      · exact (hz₂₃ (hz₂'.trans hz₃'.symm)).elim
  · rcases classify z₂ hz₂ with ⟨y₂, hy₂F, hz₂', hy₂⟩ | hz₂'
    · rcases classify z₃ hz₃ with ⟨y₃, hy₃F, hz₃', hy₃⟩ | hz₃'
      · exact finish hz₂₃ hy₂F hz₂' hy₂ hy₃F hz₃' hy₃
      · exact (hz₁₃ (hz₁'.trans hz₃'.symm)).elim
    · exact (hz₁₂ (hz₁'.trans hz₂'.symm)).elim

/-- Boundary-centre transfer when exactly one artificial vertex lies on the
rim.  Cutting at that vertex leaves a path between the other two pins; the
fresh centre pin cannot be an endpoint, so the exterior closure through the
third boundary supplies the required ambient rim. -/
theorem ambient_hasWheelCenteredAt_of_fresh_boundary_cycle_contains_exactly_one_new
    (hthreeConnected : IsThreeConnected G)
    (i : Fin 3) (hi : F.NeedsFreshPin i)
    (hqPin : ∀ j : Fin 3,
      (.inl ⟨F.boundaryVertex i, F.boundary_mem_base i⟩ :
        F.PreparedVertex) ≠ F.pin j)
    {s : F.PreparedVertex ⊕ Fin 2}
    (rim : F.replacementGraph.Walk s s) (hrim : rim.IsCycle)
    (hcenterRim :
      (.inl (.inl ⟨F.boundaryVertex i, F.boundary_mem_base i⟩) :
        F.PreparedVertex ⊕ Fin 2) ∉ rim.support)
    (hthree : 3 ≤
      (F.replacementGraph.neighborFinset
          (.inl (.inl ⟨F.boundaryVertex i, F.boundary_mem_base i⟩)) ∩
        rim.support.toFinset).card)
    (d e : Fin 2) (hde : d ≠ e) (hfin : ∀ f : Fin 2, f = d ∨ f = e)
    (hd : (.inr d : F.PreparedVertex ⊕ Fin 2) ∈ rim.support)
    (he : (.inr e : F.PreparedVertex ⊕ Fin 2) ∉ rim.support) :
    HasWheelCenteredAt G (F.boundaryVertex i) := by
  classical
  obtain ⟨y, z, hyPin, hzPin, hyz, p, hp, hpSupport⟩ :=
    ahtDoublePinReplacement.exists_old_pinPath_of_cycle_contains_exactly_one_new
      rim hrim d e hde hfin hd he
  obtain ⟨j, rfl⟩ : ∃ j : Fin 3, y = F.pin j := by
    rcases hyPin with rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
  obtain ⟨k, rfl⟩ : ∃ k : Fin 3, z = F.pin k := by
    rcases hzPin with rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
  have hjk : j ≠ k := by
    intro hjk
    subst k
    exact hyz rfl
  have hpSub : ∀ w ∈ p.support,
      (.inl w : F.PreparedVertex ⊕ Fin 2) ∈ rim.support := by
    intro w hw
    exact (hpSupport w).1 hw
  obtain ⟨hij, hik⟩ :=
    F.fresh_boundary_index_ne_endpoints_of_pinPath_on_rim
      i hi rim hcenterRim j k hjk p hp hpSub
  have hcover : ∀ l : Fin 3, l = i ∨ l = j ∨ l = k := by
    intro l
    fin_cases l <;> fin_cases i <;> fin_cases j <;> fin_cases k <;>
      simp_all
  obtain ⟨x, hxOutside, hix, ambientRim, hambient, hxAmbient,
      hpAmbient, hpAmbientExact⟩ :=
    F.exists_ambient_cycle_of_prepared_pinPath hthreeConnected
      i j k hij hik hjk hcover p hp
  let qi : F.BaseVertex :=
    ⟨F.boundaryVertex i, F.boundary_mem_base i⟩
  have hqiP : (.inl qi : F.PreparedVertex) ∉ p.support := by
    intro hqi
    exact hcenterRim (hpSub (.inl qi) hqi)
  have hcenterAmbient : F.boundaryVertex i ∉ ambientRim.support := by
    intro hcenter
    exact hqiP ((hpAmbientExact qi (Or.inr rfl)).2 hcenter)
  apply F.ambient_hasWheelCenteredAt_of_fresh_boundary_support_transfer
    i hi hqPin rim hrim hcenterRim hthree ambientRim hambient
      hcenterAmbient hxOutside hix hxAmbient
  intro w hwF hwRim
  exact hpAmbient w ((hpSupport (.inl w)).2 hwRim)

/-- Boundary-centre transfer when both artificial vertices lie on the rim.
The singleton gadget piece must be the centre's own fresh pin; the genuine
piece joins the other two pins and carries every old rim vertex. -/
theorem ambient_hasWheelCenteredAt_of_fresh_boundary_cycle_contains_both_new
    (hthreeConnected : IsThreeConnected G)
    (i : Fin 3) (hi : F.NeedsFreshPin i)
    (hqPin : ∀ j : Fin 3,
      (.inl ⟨F.boundaryVertex i, F.boundary_mem_base i⟩ :
        F.PreparedVertex) ≠ F.pin j)
    {s : F.PreparedVertex ⊕ Fin 2}
    (rim : F.replacementGraph.Walk s s) (hrim : rim.IsCycle)
    (hcenterRim :
      (.inl (.inl ⟨F.boundaryVertex i, F.boundary_mem_base i⟩) :
        F.PreparedVertex ⊕ Fin 2) ∉ rim.support)
    (hthree : 3 ≤
      (F.replacementGraph.neighborFinset
          (.inl (.inl ⟨F.boundaryVertex i, F.boundary_mem_base i⟩)) ∩
        rim.support.toFinset).card)
    (d e : Fin 2) (hde : d ≠ e) (hfin : ∀ f : Fin 2, f = d ∨ f = e)
    (hd : (.inr d : F.PreparedVertex ⊕ Fin 2) ∈ rim.support)
    (he : (.inr e : F.PreparedVertex ⊕ Fin 2) ∈ rim.support) :
    HasWheelCenteredAt G (F.boundaryVertex i) := by
  classical
  obtain ⟨l, j, k, hlj, hlk, hjk, hcover, p, hp, -, hpSupport⟩ :=
    F.exists_nontrivial_prepared_pinPath_of_cycle_contains_both_new
      ⟨F.boundaryVertex i, F.boundary_mem_base i⟩ hqPin
      rim hrim hthree d e hde hfin hd he
  have hpSub : ∀ w ∈ p.support,
      (.inl w : F.PreparedVertex ⊕ Fin 2) ∈ rim.support := by
    intro w hw
    exact (hpSupport w).2 (Or.inr hw)
  obtain ⟨hij, hik⟩ :=
    F.fresh_boundary_index_ne_endpoints_of_pinPath_on_rim
      i hi rim hcenterRim j k hjk p hp hpSub
  have hil : i = l := by
    rcases hcover i with hil | hij' | hik'
    · exact hil
    · exact (hij hij').elim
    · exact (hik hik').elim
  subst l
  obtain ⟨x, hxOutside, hix, ambientRim, hambient, hxAmbient,
      hpAmbient, hpAmbientExact⟩ :=
    F.exists_ambient_cycle_of_prepared_pinPath hthreeConnected
      i j k hij hik hjk hcover p hp
  let qi : F.BaseVertex :=
    ⟨F.boundaryVertex i, F.boundary_mem_base i⟩
  have hqiP : (.inl qi : F.PreparedVertex) ∉ p.support := by
    intro hqi
    exact hcenterRim (hpSub (.inl qi) hqi)
  have hcenterAmbient : F.boundaryVertex i ∉ ambientRim.support := by
    intro hcenter
    exact hqiP ((hpAmbientExact qi (Or.inr rfl)).2 hcenter)
  have hpinFresh : F.pin i = (.inr ⟨i, hi⟩ : F.PreparedVertex) := by
    simp [pin, hi]
  apply F.ambient_hasWheelCenteredAt_of_fresh_boundary_support_transfer
    i hi hqPin rim hrim hcenterRim hthree ambientRim hambient
      hcenterAmbient hxOutside hix hxAmbient
  intro w hwF hwRim
  rcases (hpSupport (.inl w)).1 hwRim with hwi | hwp
  · rw [hpinFresh] at hwi
    exact (Sum.inl_ne_inr hwi).elim
  · exact hpAmbient w hwp

/-- Complete fresh-boundary-centre transfer, by the exhaustive finite split
according to whether neither, one, or both of `d,d'` occur on the rim. -/
theorem ambient_hasWheelCenteredAt_of_fresh_boundary
    (hthreeConnected : IsThreeConnected G)
    (i : Fin 3) (hi : F.NeedsFreshPin i)
    (hqPin : ∀ j : Fin 3,
      (.inl ⟨F.boundaryVertex i, F.boundary_mem_base i⟩ :
        F.PreparedVertex) ≠ F.pin j)
    {s : F.PreparedVertex ⊕ Fin 2}
    (rim : F.replacementGraph.Walk s s) (hrim : rim.IsCycle)
    (hcenterRim :
      (.inl (.inl ⟨F.boundaryVertex i, F.boundary_mem_base i⟩) :
        F.PreparedVertex ⊕ Fin 2) ∉ rim.support)
    (hthree : 3 ≤
      (F.replacementGraph.neighborFinset
          (.inl (.inl ⟨F.boundaryVertex i, F.boundary_mem_base i⟩)) ∩
        rim.support.toFinset).card) :
    HasWheelCenteredAt G (F.boundaryVertex i) := by
  classical
  by_cases h0 :
      (.inr 0 : F.PreparedVertex ⊕ Fin 2) ∈ rim.support
  · by_cases h1 :
        (.inr 1 : F.PreparedVertex ⊕ Fin 2) ∈ rim.support
    · exact F.ambient_hasWheelCenteredAt_of_fresh_boundary_cycle_contains_both_new
        hthreeConnected i hi hqPin rim hrim hcenterRim hthree
          0 1 (by decide) (by intro f; fin_cases f <;> simp) h0 h1
    · exact F.ambient_hasWheelCenteredAt_of_fresh_boundary_cycle_contains_exactly_one_new
        hthreeConnected i hi hqPin rim hrim hcenterRim hthree
          0 1 (by decide) (by intro f; fin_cases f <;> simp) h0 h1
  · by_cases h1 :
        (.inr 1 : F.PreparedVertex ⊕ Fin 2) ∈ rim.support
    · exact F.ambient_hasWheelCenteredAt_of_fresh_boundary_cycle_contains_exactly_one_new
        hthreeConnected i hi hqPin rim hrim hcenterRim hthree
          1 0 (by decide) (by intro f; fin_cases f <;> simp) h1 h0
    · have havoid : ∀ d : Fin 2,
          (.inr d : F.PreparedVertex ⊕ Fin 2) ∉ rim.support := by
        intro d
        fin_cases d
        · exact h0
        · exact h1
      rcases s with r₀ | d
      · exact F.ambient_hasWheelCenteredAt_of_replacement_cycle_avoids_new
          (x := ⟨F.boundaryVertex i, F.boundary_mem_base i⟩)
          (r₀ := r₀) rim hrim hcenterRim hthree havoid
      · exact (havoid d rim.start_mem_support).elim

/-- Every replacement wheel has the same old centre in the ambient graph.
The centre classification reduces to the complete interior transfer above
or to the fresh-boundary transfer. -/
theorem replacement_hasWheelCenteredAt_imp_ambient
    (hthreeConnected : IsThreeConnected G)
    {z : F.PreparedVertex ⊕ Fin 2}
    (hwheel : HasWheelCenteredAt F.replacementGraph z) :
    ∃ q : F.BaseVertex,
      z = .inl (.inl q) ∧ HasWheelCenteredAt G q.1 := by
  obtain ⟨q, hz, hqPin⟩ := F.replacement_wheelCenter_is_old_nonpin hwheel
  refine ⟨q, hz, ?_⟩
  rcases F.old_nonpin_inside_or_fresh_boundary q hqPin with hqF |
      ⟨i, hqi, hi⟩
  · subst z
    exact F.replacement_hasWheelCenteredAt_inside_imp_ambient
      hthreeConnected q hqF hqPin hwheel
  · subst q
    subst z
    obtain ⟨s, rim, hrim, hcenterRim, hthree⟩ := hwheel
    exact F.ambient_hasWheelCenteredAt_of_fresh_boundary
      hthreeConnected i hi hqPin rim hrim hcenterRim hthree

/-- Two distinct high-inside-degree boundary vertices cannot be adjacent if
the first has ambient degree three.  Its two fragment neighbours, an
exterior neighbour forced by three-connectivity, and the second boundary
vertex would otherwise be four distinct neighbours. -/
theorem not_adj_boundary_of_needsFreshPin_of_degree_three
    (hthreeConnected : IsThreeConnected G)
    (i j : Fin 3) (hij : i ≠ j) (hi : F.NeedsFreshPin i)
    (hdeg : G.degree (F.boundaryVertex i) = 3) :
    ¬G.Adj (F.boundaryVertex i) (F.boundaryVertex j) := by
  classical
  intro hijAdj
  obtain ⟨x, hxOutside, hix⟩ :=
    F.exists_boundary_neighbor_outside hthreeConnected i
  let S : Finset V :=
    insert (F.boundaryVertex j) (insert x (F.insideNeighborFinset i))
  have hjNotInside :
      F.boundaryVertex j ∉ F.insideNeighborFinset i := by
    intro hj
    have hjF := (Finset.mem_inter.1 hj).2
    exact F.boundary_not_mem j hjF
  have hxNotInside : x ∉ F.insideNeighborFinset i := by
    intro hx
    have hxF := (Finset.mem_inter.1 hx).2
    exact (Finset.mem_sdiff.1 hxOutside).2 (Finset.mem_union_left _ hxF)
  have hjx : F.boundaryVertex j ≠ x := by
    intro hjx
    subst x
    exact (Finset.mem_sdiff.1 hxOutside).2
      (Finset.mem_union_right F.verts
        (F.boundaryVertex_mem_boundaryFinset j))
  have hScard : 4 ≤ S.card := by
    dsimp only [S]
    rw [Finset.card_insert_of_notMem]
    · rw [Finset.card_insert_of_notMem hxNotInside]
      change 2 ≤ (F.insideNeighborFinset i).card at hi
      omega
    · simp only [Finset.mem_insert]
      exact fun h ↦ h.elim hjx hjNotInside
  have hsub : S ⊆ G.neighborFinset (F.boundaryVertex i) := by
    intro y hy
    simp only [S, Finset.mem_insert] at hy
    rcases hy with rfl | rfl | hy
    · simpa only [SimpleGraph.mem_neighborFinset] using hijAdj
    · simpa only [SimpleGraph.mem_neighborFinset] using hix
    · exact (Finset.mem_inter.1 hy).1
  have hcard := Finset.card_le_card hsub
  rw [G.card_neighborFinset_eq_degree, hdeg] at hcard
  omega

/-- Once a possible replacement wheel centre has been reduced to an old
non-pin vertex, adjoining `d,d'` has not changed its degree. -/
theorem replacement_degree_old_nonpin (q : F.BaseVertex)
    (hq : ∀ i : Fin 3, (.inl q : F.PreparedVertex) ≠ F.pin i) :
    F.replacementGraph.degree (.inl (.inl q)) =
      F.preparedGraph.degree (.inl q) := by
  exact ahtDoublePinReplacement.degree_old_nonpin
    (hq 0) (hq 1) (hq 2)

/-- At a boundary centre with a fresh pin, replacement neighbours inject
into ambient neighbours: old neighbours map to themselves and the single
fresh pin maps to a fixed exterior neighbour. -/
theorem replacement_degree_fresh_boundary_le_ambient
    (hthreeConnected : IsThreeConnected G)
    (i : Fin 3) (hi : F.NeedsFreshPin i)
    (hqPin : ∀ j : Fin 3,
      (.inl ⟨F.boundaryVertex i, F.boundary_mem_base i⟩ :
        F.PreparedVertex) ≠ F.pin j) :
    F.replacementGraph.degree
        (.inl (.inl ⟨F.boundaryVertex i, F.boundary_mem_base i⟩)) ≤
      G.degree (F.boundaryVertex i) := by
  classical
  obtain ⟨x, hxOutside, hix⟩ :=
    F.exists_boundary_neighbor_outside hthreeConnected i
  let center : F.PreparedVertex ⊕ Fin 2 :=
    .inl (.inl ⟨F.boundaryVertex i, F.boundary_mem_base i⟩)
  let R := F.replacementGraph.neighborFinset center
  let A := G.neighborFinset (F.boundaryVertex i)
  let value : F.PreparedVertex ⊕ Fin 2 → V
    | .inl (.inl y) => y.1
    | _ => x
  have hpin : F.pin i = (.inr ⟨i, hi⟩ : F.PreparedVertex) := by
    simp [pin, hi]
  have hvalue (z : F.PreparedVertex ⊕ Fin 2) (hz : z ∈ R) :
      value z ∈ A := by
    have hadj : F.replacementGraph.Adj center z := by
      simpa only [R, SimpleGraph.mem_neighborFinset] using hz
    rcases F.replacement_neighbor_of_fresh_boundary_center
        i hi hqPin (by simpa only [center] using hadj) with
      ⟨y, hyF, rfl, hiy⟩ | rfl
    · simpa only [value, A, SimpleGraph.mem_neighborFinset] using hiy
    · simpa [hpin, value, A, SimpleGraph.mem_neighborFinset] using hix
  let f : {z // z ∈ R} → {y // y ∈ A} :=
    fun z ↦ ⟨value z.1, hvalue z.1 z.2⟩
  have hfinj : Function.Injective f := by
    intro z w hzw
    apply Subtype.ext
    have hzAdj : F.replacementGraph.Adj center z.1 := by
      simpa only [R, SimpleGraph.mem_neighborFinset] using z.2
    have hwAdj : F.replacementGraph.Adj center w.1 := by
      simpa only [R, SimpleGraph.mem_neighborFinset] using w.2
    have hzClass := F.replacement_neighbor_of_fresh_boundary_center
      i hi hqPin (by simpa only [center] using hzAdj)
    have hwClass := F.replacement_neighbor_of_fresh_boundary_center
      i hi hqPin (by simpa only [center] using hwAdj)
    have hval : value z.1 = value w.1 :=
      congrArg Subtype.val hzw
    rcases hzClass with ⟨y, hyF, hzy, hiy⟩ | hzi <;>
      rcases hwClass with ⟨r, hrF, hwr, hir⟩ | hwi
    · rw [hzy, hwr] at hval
      have hyr : y = r := Subtype.ext (by simpa only [value] using hval)
      simpa only [hzy, hwr, hyr]
    · rw [hzy, hwi] at hval
      have hyx : y.1 ≠ x := by
        intro hyx
        subst x
        exact (Finset.mem_sdiff.1 hxOutside).2
          (Finset.mem_union_left _ hyF)
      exact (hyx (by simpa [hpin, value] using hval)).elim
    · rw [hzi, hwr] at hval
      have hrx : r.1 ≠ x := by
        intro hrx
        subst x
        exact (Finset.mem_sdiff.1 hxOutside).2
          (Finset.mem_union_left _ hrF)
      exact (hrx (by simpa [hpin, value] using hval.symm)).elim
    · exact hzi.trans hwi.symm
  have hcard := Fintype.card_le_of_injective f hfinj
  rw [← F.replacementGraph.card_neighborFinset_eq_degree,
    ← G.card_neighborFinset_eq_degree]
  change R.card ≤ A.card
  simpa only [Fintype.card_coe] using hcard

/-- The deliberately adjoined pair in the exact fragment construction is a
degree-three false-twin pair. -/
theorem replacement_new_vertices_degree_three_falseTwins :
    AreFalseTwins F.replacementGraph (.inr 0) (.inr 1) ∧
      F.replacementGraph.degree (.inr 0) = 3 ∧
      F.replacementGraph.degree (.inr 1) = 3 := by
  exact ahtDoublePinReplacement.new_vertices_degree_three_falseTwins
    (F.pin_ne (by decide : (0 : Fin 3) ≠ 1))
    (F.pin_ne (by decide : (0 : Fin 3) ≠ 2))
    (F.pin_ne (by decide : (1 : Fin 3) ≠ 2))

/-! ## Connectivity rerouting from the ambient fragment -/

/-- Ambient vertex deleted when a replacement vertex is deleted.  Old base
vertices shadow themselves, a fresh pin shadows its boundary vertex, and the
two artificial vertices have no ambient shadow. -/
def ambientShadow : F.PreparedVertex ⊕ Fin 2 → Finset V
  | .inl (.inl q) => {q.1}
  | .inl (.inr i) => {F.boundaryVertex i.1}
  | .inr _ => ∅

@[simp] theorem ambientShadow_old (q : F.BaseVertex) :
    F.ambientShadow (.inl (.inl q)) = {q.1} := rfl

@[simp] theorem ambientShadow_fresh (i : F.FreshPin) :
    F.ambientShadow (.inl (.inr i)) = {F.boundaryVertex i.1} := rfl

@[simp] theorem ambientShadow_new (i : Fin 2) :
    F.ambientShadow (.inr i) = ∅ := rfl

theorem ambientShadow_card_le_one (x : F.PreparedVertex ⊕ Fin 2) :
    (F.ambientShadow x).card ≤ 1 := by
  rcases x with (q | i) | j <;> simp

/-- Two deleted replacement vertices shadow fewer than three ambient
vertices, exactly the bound needed to invoke ambient three-connectivity. -/
theorem ambientShadow_pair_card_lt_three
    (x y : F.PreparedVertex ⊕ Fin 2) :
    (F.ambientShadow x ∪ F.ambientShadow y).card < 3 := by
  have hu := Finset.card_union_le (F.ambientShadow x) (F.ambientShadow y)
  have hx := F.ambientShadow_card_le_one x
  have hy := F.ambientShadow_card_le_one y
  omega

theorem ambientShadow_subset_fragment_boundary
    (x : F.PreparedVertex ⊕ Fin 2) :
    F.ambientShadow x ⊆
      F.verts ∪ ({F.a, F.b, F.c} : Finset V) := by
  rcases x with (q | i) | j
  · simpa using q.2
  · intro z hz
    simp only [ambientShadow_fresh, Finset.mem_singleton] at hz
    subst z
    exact F.boundary_mem_base i.1
  · simp

/-- The prepared vertices among a finite set of deleted replacement
vertices.  This is the exact deletion set used to invoke the prepared
rerouting theorem. -/
def oldDeletion
    (D : Finset (F.PreparedVertex ⊕ Fin 2)) : Finset F.PreparedVertex :=
  Finset.univ.filter fun z => (.inl z : F.PreparedVertex ⊕ Fin 2) ∈ D

@[simp] theorem mem_oldDeletion
    {D : Finset (F.PreparedVertex ⊕ Fin 2)} {z : F.PreparedVertex} :
    z ∈ F.oldDeletion D ↔ (.inl z : F.PreparedVertex ⊕ Fin 2) ∈ D := by
  simp [oldDeletion]

theorem oldDeletion_card_le
    (D : Finset (F.PreparedVertex ⊕ Fin 2)) :
    (F.oldDeletion D).card ≤ D.card := by
  let inc : F.PreparedVertex ↪ F.PreparedVertex ⊕ Fin 2 :=
    ⟨Sum.inl, Sum.inl_injective⟩
  have hsub : (F.oldDeletion D).map inc ⊆ D := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := Finset.mem_map.1 hz
    change (.inl w : F.PreparedVertex ⊕ Fin 2) ∈ D
    simpa using hw
  simpa using Finset.card_le_card hsub

/-- The prepared fragment graph is connected.  For an inside vertex, delete
the other two boundary vertices in the ambient three-connected graph and
walk to the nonempty exterior.  The first boundary hit must be the remaining
one.  Pendant pins and boundary vertices then attach through an inside
neighbour.  This is the `d,d'`-deletion case of AHT Lemma 6.4. -/
theorem preparedGraph_connected (hthree : IsThreeConnected G) :
    F.preparedGraph.Connected := by
  let D : Finset V := {F.b, F.c}
  obtain ⟨o, ho⟩ := F.outside_nonempty
  have hoOutside := (Finset.mem_sdiff.1 ho).2
  have hoF : o ∉ F.verts := by
    intro hoF
    exact hoOutside (Finset.mem_union_left _ hoF)
  have hoD : o ∉ D := by
    intro hoD
    apply hoOutside
    apply Finset.mem_union_right F.verts
    have hoBC : o = F.b ∨ o = F.c := by simpa [D] using hoD
    rcases hoBC with rfl | rfl <;> simp
  have hDcard : D.card < 3 := by simp [D, F.bc]
  have hpre := hthree.induce_compl_preconnected D hDcard
  have inside_reaches_pin0 (p : V) (hpF : p ∈ F.verts) :
      F.preparedGraph.Reachable
        (.inl ⟨p, Finset.mem_union_left _ hpF⟩) (F.pin 0) := by
    have hpNotB : p ∉ ({F.a, F.b, F.c} : Finset V) :=
      Finset.disjoint_left.1 F.boundary_disjoint hpF
    have hpD : p ∉ D := by
      intro hpD
      apply hpNotB
      have hpBC : p = F.b ∨ p = F.c := by simpa [D] using hpD
      rcases hpBC with rfl | rfl <;> simp
    let pD : {v : V // v ∉ D} := ⟨p, hpD⟩
    let oD : {v : V // v ∉ D} := ⟨o, hoD⟩
    obtain ⟨w⟩ := hpre pD oD
    let emb : (G.induce fun v : V ↦ v ∉ D) →g G :=
      { toFun := Subtype.val
        map_rel' := by intro x y hxy; exact hxy }
    let q : G.Walk p o := w.map emb
    have havoid : ∀ z ∈ q.support, z ∉ D := by
      intro z hz
      dsimp [q] at hz
      rw [SimpleGraph.Walk.support_map] at hz
      obtain ⟨zD, hzD, hzEq⟩ := List.mem_map.mp hz
      subst z
      have hemb : emb zD = zD.1 := rfl
      rw [hemb]
      exact zD.2
    obtain ⟨i, hiD, hreach⟩ :=
      F.walk_inside_to_surviving_pin q hpF hoF havoid
    have hi : i = 0 := by
      fin_cases i
      · rfl
      · exact (hiD (by simp [D])).elim
      · exact (hiD (by simp [D])).elim
    simpa [hi] using hreach
  have boundary_reaches_pin0 (i : Fin 3) :
      F.preparedGraph.Reachable
        (.inl ⟨F.boundaryVertex i, F.boundary_mem_base i⟩)
        (F.pin 0) := by
    obtain ⟨y, hy⟩ := F.insideNeighborFinset_nonempty i
    have hy' := Finset.mem_inter.1 hy
    have hyF : y ∈ F.verts := hy'.2
    have hyAdj : G.Adj (F.boundaryVertex i) y := by
      simpa [SimpleGraph.mem_neighborFinset] using hy'.1
    have hyNotB : y ∉ ({F.a, F.b, F.c} : Finset V) :=
      Finset.disjoint_left.1 F.boundary_disjoint hyF
    have hby : F.preparedGraph.Adj
        (.inl ⟨F.boundaryVertex i, F.boundary_mem_base i⟩)
        (.inl ⟨y, Finset.mem_union_left _ hyF⟩) := by
      exact ⟨hyAdj, fun hbad ↦ hyNotB hbad.2⟩
    exact hby.reachable.trans (inside_reaches_pin0 y hyF)
  have pin_reaches_pin0 (i : Fin 3) :
      F.preparedGraph.Reachable (F.pin i) (F.pin 0) := by
    by_cases hi : F.NeedsFreshPin i
    · have hpb : F.preparedGraph.Adj (F.pin i)
          (.inl ⟨F.boundaryVertex i, F.boundary_mem_base i⟩) := by
        simp [pin, hi]
      exact hpb.reachable.trans (boundary_reaches_pin0 i)
    · simpa [pin, hi] using boundary_reaches_pin0 i
  have hreach (z : F.PreparedVertex) :
      F.preparedGraph.Reachable z (F.pin 0) := by
    rcases z with q | i
    · rcases Finset.mem_union.mp q.2 with hqF | hqB
      · exact inside_reaches_pin0 q.1 hqF
      · have hq : q.1 = F.a ∨ q.1 = F.b ∨ q.1 = F.c := by
          simpa using hqB
        rcases hq with hq | hq
        · let qa : F.BaseVertex :=
            ⟨F.a, by simp⟩
          have hqa : q = qa := Subtype.ext hq
          rw [hqa]
          simpa [qa] using boundary_reaches_pin0 0
        · rcases hq with hq | hq
          · let qb : F.BaseVertex :=
              ⟨F.b, by simp⟩
            have hqb : q = qb := Subtype.ext hq
            rw [hqb]
            simpa [qb] using boundary_reaches_pin0 1
          · let qc : F.BaseVertex :=
              ⟨F.c, by simp⟩
            have hqc : q = qc := Subtype.ext hq
            rw [hqc]
            simpa [qc] using boundary_reaches_pin0 2
    · simpa [pin, i.2] using pin_reaches_pin0 i.1
  exact {
    preconnected := fun x y ↦ (hreach x).trans (hreach y).symm
    nonempty := ⟨F.pin 0⟩ }

/-- In particular the exact replacement graph is connected. -/
theorem replacementGraph_connected (hthree : IsThreeConnected G) :
    F.replacementGraph.Connected :=
  ahtDoublePinReplacement.connected (F.preparedGraph_connected hthree)

/-- Deleting any set of fewer than three vertices from the exact replacement
graph leaves it connected.  If one artificial vertex survives, every
surviving prepared vertex is rerouted to a surviving pin and hence to that
artificial vertex.  If both artificial vertices were deleted, the cardinal
bound says no prepared vertex was deleted, so connectivity reduces to the
prepared graph. -/
theorem replacementGraph_induce_compl_connected
    (hthree : IsThreeConnected G)
    (D : Finset (F.PreparedVertex ⊕ Fin 2)) (hD : D.card < 3) :
    (F.replacementGraph.induce
      fun z : F.PreparedVertex ⊕ Fin 2 ↦ z ∉ D).Connected := by
  classical
  let E := F.oldDeletion D
  have hE : E.card < 3 :=
    lt_of_le_of_lt (F.oldDeletion_card_le D) hD
  by_cases hnew : ∃ j : Fin 2, (.inr j : F.PreparedVertex ⊕ Fin 2) ∉ D
  · obtain ⟨j, hjD⟩ := hnew
    let VK := {z : F.PreparedVertex // z ∉ E}
    let VL := {z : F.PreparedVertex ⊕ Fin 2 // z ∉ D}
    let K : SimpleGraph VK :=
      F.preparedGraph.induce fun z : F.PreparedVertex ↦ z ∉ E
    let L : SimpleGraph VL := F.replacementGraph.induce
      fun z : F.PreparedVertex ⊕ Fin 2 ↦ z ∉ D
    let inc : K →g L :=
      { toFun := fun z ↦ ⟨.inl z.1, by simpa [E] using z.2⟩
        map_rel' := by intro u v huv; exact huv }
    let root : VL := ⟨.inr j, hjD⟩
    have hreach (x : VL) : L.Reachable x root := by
      rcases x with ⟨x, hxD⟩
      rcases x with z | k
      · have hzE : z ∉ E := by simpa [E] using hxD
        obtain ⟨i, hiE, p⟩ :=
          F.prepared_reaches_pin_after_deletion hthree E hE hzE
        have hiD : (.inl (F.pin i) : F.PreparedVertex ⊕ Fin 2) ∉ D := by
          simpa [E] using hiE
        have hedge : L.Adj ⟨.inl (F.pin i), hiD⟩ root := by
          change F.replacementGraph.Adj (.inl (F.pin i)) (.inr j)
          apply ahtDoublePinReplacement.adj_old_new_iff.mpr
          fin_cases i <;> simp
        exact (p.map inc).trans hedge.reachable
      · obtain ⟨p, hp, hpE⟩ :=
          ahtDoublePinReplacement.exists_pin_not_mem
            (F.pin_ne (by decide : (0 : Fin 3) ≠ 1))
            (F.pin_ne (by decide : (0 : Fin 3) ≠ 2))
            (F.pin_ne (by decide : (1 : Fin 3) ≠ 2)) hE
        have hpD : (.inl p : F.PreparedVertex ⊕ Fin 2) ∉ D := by
          simpa [E] using hpE
        have hkp : L.Adj ⟨.inr k, hxD⟩ ⟨.inl p, hpD⟩ := by
          change F.replacementGraph.Adj (.inr k) (.inl p)
          exact ahtDoublePinReplacement.adj_new_old_iff.mpr hp
        have hpj : L.Adj ⟨.inl p, hpD⟩ root := by
          change F.replacementGraph.Adj (.inl p) (.inr j)
          exact ahtDoublePinReplacement.adj_old_new_iff.mpr hp
        exact hkp.reachable.trans hpj.reachable
    exact {
      preconnected := fun x y ↦ (hreach x).trans (hreach y).symm
      nonempty := ⟨root⟩ }
  · have hnewD (j : Fin 2) :
        (.inr j : F.PreparedVertex ⊕ Fin 2) ∈ D := by
      by_contra hj
      exact hnew ⟨j, hj⟩
    let P : Finset (F.PreparedVertex ⊕ Fin 2) := {(.inr 0), (.inr 1)}
    have hPD : P ⊆ D := by
      intro z hz
      simp only [P, Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact hnewD 0
      · exact hnewD 1
    have hPcard : P.card = 2 := by simp [P]
    have hDle : D.card ≤ P.card := by
      rw [hPcard]
      omega
    have hPD_eq : P = D := Finset.eq_of_subset_of_card_le hPD hDle
    let VL := {z : F.PreparedVertex ⊕ Fin 2 // z ∉ D}
    let L : SimpleGraph VL := F.replacementGraph.induce
      fun z : F.PreparedVertex ⊕ Fin 2 ↦ z ∉ D
    have holdD (z : F.PreparedVertex) :
        (.inl z : F.PreparedVertex ⊕ Fin 2) ∉ D := by
      rw [← hPD_eq]
      simp [P]
    let inc : F.preparedGraph →g L :=
      { toFun := fun z ↦ ⟨.inl z, holdD z⟩
        map_rel' := by intro u v huv; exact huv }
    let root : VL := ⟨.inl (F.pin 0), holdD (F.pin 0)⟩
    have hprepared := F.preparedGraph_connected hthree
    have hreach (x : VL) : L.Reachable x root := by
      rcases x with ⟨x, hxD⟩
      rcases x with z | j
      · exact (hprepared z (F.pin 0)).map inc
      · exact (hxD (hnewD j)).elim
    exact {
      preconnected := fun x y ↦ (hreach x).trans (hreach y).symm
      nonempty := ⟨root⟩ }

/-- Source-exact three-connectivity conclusion of AHT Lemma 6.4, first in
the deletion-of-two-vertices form. -/
theorem replacementGraph_vertexThreeConnected
    (hthree : IsThreeConnected G) :
    VertexThreeConnected F.replacementGraph := by
  classical
  have hbase : 3 ≤ Fintype.card F.BaseVertex := by
    let e : Fin 3 ↪ F.BaseVertex :=
      { toFun := fun i ↦ ⟨F.boundaryVertex i, F.boundary_mem_base i⟩
        inj' := fun i j hij ↦ F.boundaryVertex_injective
          (congrArg Subtype.val hij) }
    exact Fintype.card_le_of_injective e e.injective
  have hcard : 4 ≤ Fintype.card (F.PreparedVertex ⊕ Fin 2) := by
    simp only [Fintype.card_sum, Fintype.card_fin]
    change 4 ≤ Fintype.card F.BaseVertex + Fintype.card F.FreshPin + 2
    omega
  refine ⟨hcard, F.replacementGraph_connected hthree, ?_⟩
  intro x y hxy
  let D : Finset (F.PreparedVertex ⊕ Fin 2) := {x, y}
  have hD : D.card < 3 := by simp [D, hxy]
  have hconn := F.replacementGraph_induce_compl_connected hthree D hD
  let e : {z : F.PreparedVertex ⊕ Fin 2 // z ∉ D} ≃
      {z : F.PreparedVertex ⊕ Fin 2 // z ≠ x ∧ z ≠ y} :=
    Equiv.setCongr (by ext z; simp [D])
  let gi :
      (F.replacementGraph.induce
        fun z : F.PreparedVertex ⊕ Fin 2 ↦ z ∉ D) ≃g
      (F.replacementGraph.induce
        fun z : F.PreparedVertex ⊕ Fin 2 ↦ z ≠ x ∧ z ≠ y) :=
    { toEquiv := e
      map_rel_iff' := by intro u v; rfl }
  exact gi.connected_iff.mp hconn

/-- Source-exact separation-based three-connectivity conclusion of AHT
Lemma 6.4. -/
theorem replacementGraph_isThreeConnected
    (hthree : IsThreeConnected G) : IsThreeConnected F.replacementGraph :=
  ahtDoublePinReplacement.isThreeConnected_of_vertexThreeConnected
    (F.replacementGraph_vertexThreeConnected hthree)

/-! ## Almost-wheel-free conclusion of AHT Lemma 6.4 -/

/-- Local source-level form of the elementary degree consequence of
`AlmostWheelFree`, kept here so Lemma 6.4 has no dependency on Lemma 6.5. -/
theorem ambient_center_degree_eq_three_of_almostWheelFree
    (halmost : AlmostWheelFree G) {q : V}
    (hq : HasWheelCenteredAt G q) : G.degree q = 3 := by
  rcases halmost with hnone | hone | htwo
  · exact (hnone q hq).elim
  · obtain ⟨a, hdeg, hcenters⟩ := hone
    rw [hcenters q hq]
    exact hdeg
  · obtain ⟨a, b, hab, hdega, hdegb, hcenters⟩ := htwo
    rcases hcenters q hq with rfl | rfl
    · exact hdega
    · exact hdegb

/-- With two distinct ambient wheel centres fixed, every other ambient
wheel centre is one of them. -/
theorem ambient_center_eq_left_or_right
    (halmost : AlmostWheelFree G) {p q r : V}
    (hp : HasWheelCenteredAt G p) (hq : HasWheelCenteredAt G q)
    (hpq : p ≠ q) (hr : HasWheelCenteredAt G r) :
    r = p ∨ r = q := by
  rcases halmost with hnone | hone | htwo
  · exact (hnone p hp).elim
  · obtain ⟨a, hdeg, hcenters⟩ := hone
    exact (hpq ((hcenters p hp).trans (hcenters q hq).symm)).elim
  · obtain ⟨a, b, hab, hdega, hdegb, hcenters⟩ := htwo
    rcases hcenters p hp with rfl | rfl <;>
      rcases hcenters q hq with rfl | rfl
    · exact (hpq rfl).elim
    · exact hcenters r hr
    · rcases hcenters r hr with rfl | rfl
      · exact Or.inr rfl
      · exact Or.inl rfl
    · exact (hpq rfl).elim

/-- Distinct ambient centres of an almost-wheel-free graph are adjacent. -/
theorem ambient_centers_eq_or_adj
    (halmost : AlmostWheelFree G) {p q : V}
    (hp : HasWheelCenteredAt G p) (hq : HasWheelCenteredAt G q) :
    p = q ∨ G.Adj p q := by
  rcases halmost with hnone | hone | htwo
  · exact (hnone p hp).elim
  · obtain ⟨a, hdeg, hcenters⟩ := hone
    exact Or.inl ((hcenters p hp).trans (hcenters q hq).symm)
  · obtain ⟨a, b, hab, hdega, hdegb, hcenters⟩ := htwo
    rcases hcenters p hp with rfl | rfl <;>
      rcases hcenters q hq with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr hab
    · exact Or.inr hab.symm
    · exact Or.inl rfl

/-- Every replacement wheel centre has degree three.  Interior degrees are
unchanged; a fresh-boundary degree injects into its ambient degree and is
bounded below by replacement three-connectivity. -/
theorem replacement_center_degree_eq_three
    (hthree : IsThreeConnected G) (halmost : AlmostWheelFree G)
    {z : F.PreparedVertex ⊕ Fin 2}
    (hz : HasWheelCenteredAt F.replacementGraph z) :
    F.replacementGraph.degree z = 3 := by
  obtain ⟨q, hzq, hqPin⟩ :=
    F.replacement_wheelCenter_is_old_nonpin hz
  subst z
  obtain ⟨r, hrq, hrAmbient⟩ :=
    F.replacement_hasWheelCenteredAt_imp_ambient hthree hz
  have hrq' : r = q := by
    have h := Sum.inl.inj (Sum.inl.inj hrq)
    exact h.symm
  subst r
  have hambientDegree : G.degree q.1 = 3 :=
    ambient_center_degree_eq_three_of_almostWheelFree
      halmost hrAmbient
  rcases F.old_nonpin_inside_or_fresh_boundary q hqPin with hqF |
      ⟨i, hqi, hi⟩
  · rw [F.replacement_degree_old_nonpin q hqPin,
      F.prepared_degree_inside_eq_ambient q hqF, hambientDegree]
  · subst q
    have hle := F.replacement_degree_fresh_boundary_le_ambient
      hthree i hi hqPin
    have hge := (F.replacementGraph_isThreeConnected hthree).degree_ge
      (.inl (.inl ⟨F.boundaryVertex i, F.boundary_mem_base i⟩))
    rw [hambientDegree] at hle
    exact Nat.le_antisymm hle hge

/-- Distinct replacement wheel centres are adjacent.  Their ambient images
are distinct centres, hence adjacent.  The only possible obstruction to
retaining that edge in the prepared graph would be two boundary vertices;
the degree-three boundary count rules that case out. -/
theorem replacement_centers_adj_of_ne
    (hthree : IsThreeConnected G) (halmost : AlmostWheelFree G)
    {z w : F.PreparedVertex ⊕ Fin 2}
    (hz : HasWheelCenteredAt F.replacementGraph z)
    (hw : HasWheelCenteredAt F.replacementGraph w) (hzw : z ≠ w) :
    F.replacementGraph.Adj z w := by
  obtain ⟨q, hzq, hqAmbient⟩ :=
    F.replacement_hasWheelCenteredAt_imp_ambient hthree hz
  obtain ⟨r, hwr, hrAmbient⟩ :=
    F.replacement_hasWheelCenteredAt_imp_ambient hthree hw
  have hqr : q.1 ≠ r.1 := by
    intro h
    apply hzw
    rw [hzq, hwr]
    exact congrArg (fun a : F.BaseVertex ↦
      (.inl (.inl a) : F.PreparedVertex ⊕ Fin 2)) (Subtype.ext h)
  have hambientAdj : G.Adj q.1 r.1 :=
    (ambient_centers_eq_or_adj halmost hqAmbient hrAmbient).resolve_left hqr
  obtain ⟨q', hzq', hqPin'⟩ :=
    F.replacement_wheelCenter_is_old_nonpin hz
  obtain ⟨r', hwr', hrPin'⟩ :=
    F.replacement_wheelCenter_is_old_nonpin hw
  have hqq' : q' = q := by
    exact Sum.inl.inj (Sum.inl.inj (hzq'.symm.trans hzq))
  have hrr' : r' = r := by
    exact Sum.inl.inj (Sum.inl.inj (hwr'.symm.trans hwr))
  subst q'
  subst r'
  rw [hzq, hwr]
  change F.preparedGraph.Adj (.inl q) (.inl r)
  change G.Adj q.1 r.1 ∧
    ¬(q.1 ∈ ({F.a, F.b, F.c} : Finset V) ∧
      r.1 ∈ ({F.a, F.b, F.c} : Finset V))
  refine ⟨hambientAdj, ?_⟩
  rcases F.old_nonpin_inside_or_fresh_boundary q hqPin' with hqF |
      ⟨i, hqi, hi⟩
  · exact fun hbad ↦
      (Finset.disjoint_left.1 F.boundary_disjoint hqF hbad.1).elim
  rcases F.old_nonpin_inside_or_fresh_boundary r hrPin' with hrF |
      ⟨j, hrj, hj⟩
  · exact fun hbad ↦
      (Finset.disjoint_left.1 F.boundary_disjoint hrF hbad.2).elim
  · subst q
    subst r
    have hij : i ≠ j := by
      intro hij
      subst j
      exact hqr rfl
    have hdegi : G.degree (F.boundaryVertex i) = 3 :=
      ambient_center_degree_eq_three_of_almostWheelFree
        halmost hqAmbient
    exact (F.not_adj_boundary_of_needsFreshPin_of_degree_three
      hthree i j hij hi hdegi hambientAdj).elim

/-- Three replacement centres cannot be distinct: their ambient images are
three ambient centres, while `AlmostWheelFree` permits at most the two
already displayed. -/
theorem replacement_center_eq_left_or_right
    (hthree : IsThreeConnected G) (halmost : AlmostWheelFree G)
    {p q r : F.PreparedVertex ⊕ Fin 2}
    (hp : HasWheelCenteredAt F.replacementGraph p)
    (hq : HasWheelCenteredAt F.replacementGraph q) (hpq : p ≠ q)
    (hr : HasWheelCenteredAt F.replacementGraph r) :
    r = p ∨ r = q := by
  obtain ⟨a, hpa, ha⟩ :=
    F.replacement_hasWheelCenteredAt_imp_ambient hthree hp
  obtain ⟨b, hqb, hb⟩ :=
    F.replacement_hasWheelCenteredAt_imp_ambient hthree hq
  obtain ⟨c, hrc, hc⟩ :=
    F.replacement_hasWheelCenteredAt_imp_ambient hthree hr
  have hab : a.1 ≠ b.1 := by
    intro hab
    apply hpq
    rw [hpa, hqb]
    exact congrArg (fun x : F.BaseVertex ↦
      (.inl (.inl x) : F.PreparedVertex ⊕ Fin 2)) (Subtype.ext hab)
  rcases ambient_center_eq_left_or_right halmost ha hb hab hc with
    hca | hcb
  · left
    rw [hrc, hpa]
    exact congrArg (fun x : F.BaseVertex ↦
      (.inl (.inl x) : F.PreparedVertex ⊕ Fin 2)) (Subtype.ext hca)
  · right
    rw [hrc, hqb]
    exact congrArg (fun x : F.BaseVertex ↦
      (.inl (.inl x) : F.PreparedVertex ⊕ Fin 2)) (Subtype.ext hcb)

/-- Full source-exact almost-wheel-free conclusion of AHT Lemma 6.4. -/
theorem replacementGraph_almostWheelFree
    (hthree : IsThreeConnected G) (halmost : AlmostWheelFree G) :
    AlmostWheelFree F.replacementGraph := by
  classical
  by_cases hnone : ∀ z : F.PreparedVertex ⊕ Fin 2,
      ¬HasWheelCenteredAt F.replacementGraph z
  · exact Or.inl hnone
  · push_neg at hnone
    obtain ⟨a, ha⟩ := hnone
    by_cases hone : ∀ z : F.PreparedVertex ⊕ Fin 2,
        HasWheelCenteredAt F.replacementGraph z → z = a
    · exact Or.inr (Or.inl ⟨a,
        F.replacement_center_degree_eq_three hthree halmost ha, hone⟩)
    · push_neg at hone
      obtain ⟨b, hb, hba⟩ := hone
      refine Or.inr (Or.inr ⟨a, b,
        F.replacement_centers_adj_of_ne hthree halmost ha hb hba.symm,
        F.replacement_center_degree_eq_three hthree halmost ha,
        F.replacement_center_degree_eq_three hthree halmost hb, ?_⟩)
      intro z hz
      exact F.replacement_center_eq_left_or_right
        hthree halmost ha hb hba.symm hz

end AHTThreeFragment

end Erdos916
