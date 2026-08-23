import ErdosProblems.Erdos1105.OrePath

namespace Erdos1105

open SimpleGraph

/-- A complete graph admits a Hamiltonian path with any distinct prescribed endpoints. -/
theorem complete_hamiltonian_path {V : Type*} [Fintype V] [DecidableEq V]
    (hcard : 3 ≤ Fintype.card V) (a b : V) (hab : a ≠ b) :
    ∃ p : (⊤ : SimpleGraph V).Walk a b, p.IsHamiltonian := by
  classical
  have htop : (⊤ : SimpleGraph V).IsHamiltonian := by
    apply SimpleGraph.dirac_theorem hcard
    intro v
    rw [((⊤ : SimpleGraph V).degree_eq_card_sub_one v).mpr (by simp [IsUniversal])]
    omega
  let : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨q, hq⟩ := htop.exists_isHamiltonianCycle b
  let e := Equiv.swap q.snd a
  let f := (Iso.completeGraph e).toHom
  have he₀ : f q.snd = a := Equiv.swap_apply_left _ _
  have he₁ : f b = b := Equiv.swap_apply_of_ne_of_ne
    (q.adj_snd hq.isCycle.not_nil).ne hab.symm
  let p := (q.tail.map f).copy he₀ he₁
  refine ⟨p, ?_⟩
  have hmap := hq.isHamiltonian_tail.map f e.bijective
  simpa only [p, Walk.IsHamiltonian, Walk.support_copy] using hmap

/-- Add one vertex adjacent precisely to the two prescribed endpoints. -/
def endpointAugment {V : Type*} (G : SimpleGraph V) (a b : V) : SimpleGraph (Option V) where
  Adj
    | some u, some v => G.Adj u v
    | none, some v => v = a ∨ v = b
    | some u, none => u = a ∨ u = b
    | none, none => False
  symm := ⟨by rintro (_ | u) (_ | v) h <;> first | exact h | exact h.symm⟩
  loopless := ⟨by rintro (_ | u) <;> first | exact not_false | exact G.loopless.irrefl u⟩

@[simp] lemma endpointAugment_some {V : Type*} (G : SimpleGraph V) (a b u v : V) :
    (endpointAugment G a b).Adj (some u) (some v) ↔ G.Adj u v := Iff.rfl

@[simp] lemma endpointAugment_none {V : Type*} (G : SimpleGraph V) (a b v : V) :
    (endpointAugment G a b).Adj none (some v) ↔ v = a ∨ v = b := Iff.rfl

def endpointAugmentCopy {V : Type*} (G : SimpleGraph V) (a b : V) : G.Copy (endpointAugment G a b) where
  toHom := { toFun := some, map_rel' := fun h ↦ h }
  injective' := Option.some_injective V

/-- The degree-sum hypothesis makes the original vertices a clique in the
closure of the augmented graph, hence that augmented graph is Hamiltonian. -/
theorem endpointAugment_hamiltonian {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hcard : 3 ≤ Fintype.card V)
    (hdeg : ∀ u v, u ≠ v → Fintype.card V + 1 ≤ G.degree u + G.degree v)
    (a b : V) (hab : a ≠ b) : (endpointAugment G a b).IsHamiltonian := by
  classical
  let H := endpointAugment G a b
  let f := endpointAugmentCopy G a b
  have hold (u v : V) (huv : u ≠ v) : H.closure.Adj (some u) (some v) := by
    apply H.closure_spec ((Option.some_injective V).ne huv)
    have hsum := (hdeg u v huv).trans (Nat.add_le_add (f.degree_le u) (f.degree_le v))
    have hsum' := hsum.trans (Nat.add_le_add
      (H.degree_le_of_le (v := some u) H.self_le_closure)
      (H.degree_le_of_le (v := some v) H.self_le_closure))
    simpa only [Fintype.card_option] using hsum'
  let g : (⊤ : SimpleGraph V).Copy H.closure :=
    { toHom := { toFun := some, map_rel' := fun {u v} huv ↦ hold u v huv }
      injective' := Option.some_injective V }
  obtain ⟨p, hp⟩ := complete_hamiltonian_path hcard a b hab
  let p' := p.map g.toHom
  have hp' : p'.IsPath := hp.isPath.map g.injective
  have hnone : none ∉ p'.support := by
    rw [Walk.support_map, List.mem_map]
    rintro ⟨u, _, hu⟩
    exact Option.some_ne_none u hu
  have ha : H.closure.Adj none (some a) := H.self_le_closure (Or.inl rfl)
  have hb : H.closure.Adj (some b) none := H.self_le_closure (Or.inr rfl)
  let r := p'.concat hb
  have hr : r.IsPath := hp'.concat hnone hb
  let q := Walk.cons ha r
  have hq : q.IsCycle := by
    apply (Walk.cons_isCycle_iff r ha).mpr
    refine ⟨hr, ?_⟩
    intro he
    have h := hr.length_eq_one_of_mem_edges (Sym2.eq_swap ▸ he)
    have hlen := hp.length_eq
    rw [Walk.length_concat, Walk.length_map] at h
    omega
  have hqham : q.IsHamiltonianCycle := by
    apply Walk.isHamiltonianCycle_iff_isCycle_and_length_eq.mpr
    refine ⟨hq, ?_⟩
    have hlen := hp.length_eq
    simp only [q, r, p', Walk.length_cons, Walk.length_concat, Walk.length_map, Fintype.card_option]
    omega
  apply (SimpleGraph.from_closure_iff (G := H)).mp
  exact fun _ ↦ ⟨none, q, hqham⟩

lemma induced_walk_length {V : Type*} {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (S : Set V) (hS : ∀ x ∈ p.support, x ∈ S) :
    (p.induce S hS).length = p.length := by
  calc
    (p.induce S hS).length = ((p.induce S hS).map (Embedding.induce S).toHom).length :=
      (Walk.length_map _ _).symm
    _ = p.length := congrArg Walk.length (Walk.map_induce p hS)

lemma path_end_not_mem_dropLast {V : Type*} {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (hp : p.IsPath) (hlen : 1 ≤ p.length) : v ∉ p.dropLast.support := by
  intro hv
  obtain ⟨i, hi, hilen⟩ := Walk.mem_support_iff_exists_getVert.mp hv
  have hil : i < p.length := by rw [Walk.length_dropLast] at hilen; omega
  rw [Walk.getVert_dropLast hil] at hi
  have heq : p.getVert i = p.getVert p.length := by simpa only [Walk.getVert_length] using hi
  have h := hp.getVert_injOn (by change i ≤ p.length; omega) (by simp) heq
  omega

def endpointAugmentSomeIso {V : Type*} (G : SimpleGraph V) (a b : V) :
    (endpointAugment G a b).induce {x | x.isSome} ≃g G where
  toEquiv := Equiv.optionIsSomeEquiv V
  map_rel_iff' := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩
    cases x with
    | none => simp at hx
    | some x =>
      cases y with
      | none => simp at hy
      | some y => rfl

lemma endpointAugmentSomeIso_some {V : Type*} (G : SimpleGraph V) (a b : V)
    (x : {x : Option V // x.isSome}) :
    some (endpointAugmentSomeIso G a b x) = x.val := by
  rcases x with ⟨x, hx⟩
  cases x with
  | none => simp at hx
  | some x => rfl

/-- Removing the added degree-two vertex recovers a Hamiltonian path
with the two prescribed endpoints. -/
theorem hamiltonian_path_of_endpointAugment {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hcard : 3 ≤ Fintype.card V) (a b : V)
    (hH : (endpointAugment G a b).IsHamiltonian) :
    ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  let H := endpointAugment G a b
  let : Nontrivial (Option V) := ⟨none, some a, by simp⟩
  obtain ⟨q, hq⟩ := hH.exists_isHamiltonianCycle none
  have hlenq : q.length = Fintype.card V + 1 := by
    simpa only [Fintype.card_option] using hq.length_eq
  let p := q.tail.dropLast
  have hp : p.IsPath := hq.isCycle.isPath_tail.dropLast
  have hnone : none ∉ p.support := path_end_not_mem_dropLast q.tail hq.isCycle.isPath_tail
    (by rw [Walk.length_tail, hlenq]; omega)
  have hs : ∀ x ∈ p.support, x ∈ ({x : Option V | x.isSome} : Set (Option V)) := by
    intro x hx
    cases x with
    | none => exact (hnone hx).elim
    | some x => simp
  let e := endpointAugmentSomeIso G a b
  let p' := p.induce {x | x.isSome} hs
  let r := p'.map e.toHom
  have hp' : p'.IsPath := by
    apply (Walk.isPath_map_iff_of_injective
      (f := (Embedding.induce (G := H) {x | x.isSome}).toHom)
      (p := p') (Embedding.induce (G := H) {x | x.isSome}).injective).mp
    rw [Walk.map_induce]
    exact hp
  have hr : r.IsHamiltonian := by
    apply Walk.isHamiltonian_iff_isPath_and_length_eq.mpr
    refine ⟨hp'.map e.injective, ?_⟩
    rw [Walk.length_map, induced_walk_length, Walk.length_dropLast, Walk.length_tail, hlenq]
    omega
  have hpenult : q.tail.penultimate = q.penultimate := by
    change q.tail.getVert (q.tail.length - 1) = q.getVert (q.length - 1)
    rw [Walk.getVert_tail, Walk.length_tail]
    congr 1
    omega
  let s : {x : Option V // x.isSome} := ⟨q.snd, hs _ p.start_mem_support⟩
  let t : {x : Option V // x.isSome} := ⟨q.tail.penultimate, hs _ p.end_mem_support⟩
  have hsadj : H.Adj none (some (e s)) := by
    rw [endpointAugmentSomeIso_some]
    exact q.adj_snd hq.isCycle.not_nil
  have htadj : H.Adj none (some (e t)) := by
    rw [endpointAugmentSomeIso_some]
    change H.Adj none q.tail.penultimate
    rw [hpenult]
    exact (q.adj_penultimate hq.isCycle.not_nil).symm
  have hsval : e s = a ∨ e s = b := hsadj
  have htval : e t = a ∨ e t = b := htadj
  have hst : e s ≠ e t := by
    intro h
    have h' := congrArg (some : V → Option V) h
    rw [endpointAugmentSomeIso_some, endpointAugmentSomeIso_some] at h'
    change q.snd = q.tail.penultimate at h'
    rw [hpenult] at h'
    exact hq.isCycle.snd_ne_penultimate h'
  rcases hsval with hsval | hsval <;> rcases htval with htval | htval
  · exact (hst (hsval.trans htval.symm)).elim
  · refine ⟨r.copy hsval htval, ?_⟩
    simpa only [Walk.IsHamiltonian, Walk.support_copy] using hr
  · refine ⟨r.reverse.copy htval hsval, ?_⟩
    simpa only [Walk.IsHamiltonian, Walk.support_copy, Walk.support_reverse, List.count_reverse] using hr
  · exact (hst (hsval.trans htval.symm)).elim

/-- The Hamiltonian-connected version of Ore's degree-sum theorem. -/
theorem hamiltonian_path_of_degree_sum {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hcard : 3 ≤ Fintype.card V)
    (hdeg : ∀ u v, u ≠ v → Fintype.card V + 1 ≤ G.degree u + G.degree v)
    (a b : V) (hab : a ≠ b) : ∃ p : G.Walk a b, p.IsHamiltonian :=
  hamiltonian_path_of_endpointAugment G hcard a b
    (endpointAugment_hamiltonian G hcard hdeg a b hab)

#print axioms hamiltonian_path_of_degree_sum

end Erdos1105
