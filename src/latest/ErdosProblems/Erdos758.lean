/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 758.
https://www.erdosproblems.com/forum/thread/758

Informal authors:
- Bhavik Mehta

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos758.md
-/
/-
This is a Lean formalization of the resolution of Erdős Problem 758.
https://www.erdosproblems.com/758

Informal sources:
- Paul Erdős and John Gimbel, Some Problems and Results in Cochromatic Theory (1993)
- Ahu Akdemir and Tınaz Ekim, Advances on Defective Parameters in Graphs (2015)
- Bhavik Mehta's later computation, recorded on the Erdős Problems page

Formal author: Codex
-/

import Mathlib
import Mathlib.Tactic.Sat.FromLRAT
import ErdosProblems.Erdos758.D12.Semantic
import ErdosProblems.Erdos758.D12.Certificates

namespace Erdos758

open SimpleGraph

/-! # Erdős Problem 758

The cochromatic number of a finite graph is the least number of vertex colours
for which every colour class is either a clique or an independent set.  The
quantity `z n` is the least number that works uniformly for every graph on
`Fin n`; for finite labelled graphs this is exactly the maximum of their
individual cochromatic numbers.
-/

/-- A colouring is cochromatic when each colour fibre is a clique or an independent set. -/
def IsCochromaticColoring {V : Type*} (G : SimpleGraph V) {k : ℕ}
    (c : V → Fin k) : Prop :=
  ∀ i : Fin k,
    (∀ u v, c u = i → c v = i → u ≠ v → G.Adj u v) ∨
    (∀ u v, c u = i → c v = i → u ≠ v → ¬ G.Adj u v)

/-- `G` admits a cochromatic colouring using at most `k` colours. -/
def CochromaticColorable {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ c : V → Fin k, IsCochromaticColoring G c

instance instDecidableIsCochromaticColoring {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ}
    (c : V → Fin k) : Decidable (IsCochromaticColoring G c) := by
  unfold IsCochromaticColoring
  exact Fintype.decidableForallFintype

instance instDecidableCochromaticColorable {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) :
    Decidable (CochromaticColorable G k) := by
  unfold CochromaticColorable
  exact Fintype.decidableExistsFintype

/-- A graph on `Fin n` is cochromatically colourable with `n` singleton colours. -/
theorem cochromaticColorable_fin (G : SimpleGraph (Fin n)) :
    CochromaticColorable G n := by
  refine ⟨id, ?_⟩
  intro i
  right
  intro u v hu hv huv
  exact (huv (hu.trans hv.symm)).elim

/-- Extra unused colours preserve cochromatic colourability. -/
theorem CochromaticColorable.mono {V : Type*} {G : SimpleGraph V} {k l : ℕ}
    (h : CochromaticColorable G k) (hkl : k ≤ l) : CochromaticColorable G l := by
  obtain ⟨c, hc⟩ := h
  let e : Fin k ↪ Fin l := Fin.castLEEmb hkl
  refine ⟨fun v ↦ e (c v), ?_⟩
  intro i
  by_cases hi : ∃ j : Fin k, e j = i
  · obtain ⟨j, rfl⟩ := hi
    rcases hc j with hj | hj
    · left
      intro u v hu hv huv
      exact hj u v (e.injective hu) (e.injective hv) huv
    · right
      intro u v hu hv huv
      exact hj u v (e.injective hu) (e.injective hv) huv
  · right
    intro u v hu
    exact (hi ⟨c u, hu⟩).elim

/-- The cochromatic number of an individual finite graph. -/
noncomputable def cochromaticNumber {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ :=
  by
  classical
  exact Nat.find (show ∃ k, CochromaticColorable G k from by
    let e := Fintype.equivFin V
    refine ⟨Fintype.card V, e, ?_⟩
    intro i
    right
    intro u v hu hv huv
    exact (huv (e.injective (hu.trans hv.symm))).elim)

/-- The minimum defining `cochromaticNumber` is attained. -/
theorem cochromaticNumber_spec {V : Type*} [Fintype V] (G : SimpleGraph V) :
    CochromaticColorable G (cochromaticNumber G) := by
  classical
  exact Nat.find_spec (show ∃ k, CochromaticColorable G k from by
    let e := Fintype.equivFin V
    refine ⟨Fintype.card V, e, ?_⟩
    intro i
    right
    intro u v hu hv huv
    exact (huv (e.injective (hu.trans hv.symm))).elim)

/-- Numerical comparison with the cochromatic number is the same as colourability. -/
theorem cochromaticNumber_le_iff {V : Type*} [Fintype V] (G : SimpleGraph V) (k : ℕ) :
    cochromaticNumber G ≤ k ↔ CochromaticColorable G k := by
  classical
  constructor
  · exact fun h ↦ (cochromaticNumber_spec G).mono h
  · intro h
    exact Nat.find_min' (show ∃ k, CochromaticColorable G k from by
      let e := Fintype.equivFin V
      refine ⟨Fintype.card V, e, ?_⟩
      intro i
      right
      intro u v hu hv huv
      exact (huv (e.injective (hu.trans hv.symm))).elim) h

/-- `z n` is the least number uniformly sufficient for every graph on `n` vertices. -/
noncomputable def z (n : ℕ) : ℕ :=
  by
  classical
  exact Nat.find (show ∃ k, ∀ G : SimpleGraph (Fin n), CochromaticColorable G k from
    ⟨n, cochromaticColorable_fin⟩)

/-- The defining uniform upper bound for `z`. -/
theorem z_spec (n : ℕ) :
    ∀ G : SimpleGraph (Fin n), CochromaticColorable G (z n) := by
  classical
  exact Nat.find_spec (show ∃ k, ∀ G : SimpleGraph (Fin n), CochromaticColorable G k from
    ⟨n, cochromaticColorable_fin⟩)

/-- Any uniform bound on `n`-vertex graphs bounds `z n`. -/
theorem z_le {n k : ℕ}
    (h : ∀ G : SimpleGraph (Fin n), CochromaticColorable G k) : z n ≤ k := by
  classical
  exact Nat.find_min' (show ∃ k, ∀ G : SimpleGraph (Fin n), CochromaticColorable G k from
    ⟨n, cochromaticColorable_fin⟩) h

/-- On the finite set of labelled `n`-vertex graphs, `z n` is literally the maximum of
their individual cochromatic numbers. -/
theorem z_eq_max_cochromaticNumber (n : ℕ) :
    z n = (Finset.univ : Finset (SimpleGraph (Fin n))).sup cochromaticNumber := by
  apply Nat.le_antisymm
  · apply z_le
    intro G
    apply (cochromaticNumber_le_iff G _).mp
    exact Finset.le_sup (f := cochromaticNumber) (Finset.mem_univ G)
  · apply Finset.sup_le
    intro G _
    exact (cochromaticNumber_le_iff G _).mpr (z_spec n G)

/-- A uniform upper bound and one graph requiring that many colours determine `z`. -/
theorem z_eq_of_upper_and_witness {n k : ℕ}
    (upper : ∀ G : SimpleGraph (Fin n), CochromaticColorable G k)
    (hk : 0 < k)
    (lower : ∃ G : SimpleGraph (Fin n), ¬ CochromaticColorable G (k - 1)) :
    z n = k := by
  apply Nat.le_antisymm (z_le upper)
  by_contra h
  have hzk : z n < k := Nat.lt_of_not_ge h
  obtain ⟨G, hG⟩ := lower
  apply hG
  exact (z_spec n G).mono (by omega)

/-! ## The sharp lower bound at twelve vertices -/

/-- A finite vertex set is homogeneous when all its distinct pairs are edges or all are nonedges. -/
def IsHomogeneousFinset {V : Type*} (G : SimpleGraph V) (S : Finset V) : Prop :=
  (∀ u ∈ S, ∀ v ∈ S, u ≠ v → G.Adj u v) ∨
  (∀ u ∈ S, ∀ v ∈ S, u ≠ v → ¬ G.Adj u v)

instance instDecidableIsHomogeneousFinset {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    Decidable (IsHomogeneousFinset G S) := by
  let d₁ : Decidable
      (∀ u : V, u ∈ S → ∀ v : V, v ∈ S → u ≠ v → G.Adj u v) := by
    infer_instance
  let d₂ : Decidable
      (∀ u : V, u ∈ S → ∀ v : V, v ∈ S → u ≠ v → ¬ G.Adj u v) := by
    infer_instance
  exact @instDecidableOr _ _ d₁ d₂

/-- `G` has no clique or independent set on four vertices. -/
def HasNoHomogeneousFour {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ S : Finset V, S.card = 4 → ¬ IsHomogeneousFinset G S

instance instDecidableHasNoHomogeneousFour {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Decidable (HasNoHomogeneousFour G) := by
  unfold HasNoHomogeneousFour
  exact Fintype.decidableForallFintype

/-- A graph on twelve vertices with no homogeneous four-set cannot be covered by three
homogeneous colour fibres: the strong pigeonhole principle produces a fibre of size at least
four. -/
theorem not_cochromaticColorable_three_of_no_homogeneous_four
    (G : SimpleGraph (Fin 12)) (hno : HasNoHomogeneousFour G) :
    ¬ CochromaticColorable G 3 := by
  rintro ⟨c, hc⟩
  have hsize : Fintype.card (Fin 3) * 3 < Fintype.card (Fin 12) := by decide
  obtain ⟨i, hi⟩ := Fintype.exists_lt_card_fiber_of_mul_lt_card (f := c) hsize
  let S : Finset (Fin 12) := Finset.univ.filter fun v ↦ c v = i
  have hi' : 3 < S.card := by simpa [S] using hi
  obtain ⟨T, hTS, hTcard⟩ := Finset.exists_subset_card_eq (by omega : 4 ≤ S.card)
  apply hno T hTcard
  rcases hc i with hclique | hindependent
  · left
    intro u hu v hv huv
    apply hclique u v
    · simpa [S] using hTS hu
    · simpa [S] using hTS hv
    · exact huv
  · right
    intro u hu v hv huv
    apply hindependent u v
    · simpa [S] using hTS hu
    · simpa [S] using hTS hv
    · exact huv

/-- The nonzero quadratic residues modulo 17. -/
def quadraticResidues17 : Finset ℕ := {1, 2, 4, 8, 9, 13, 15, 16}

/-- The induced subgraph of the Paley graph on the first twelve residues `0, ..., 11`. -/
def paleyPrefix12 : SimpleGraph (Fin 12) :=
  SimpleGraph.fromRel fun u v ↦ (u.1 + 17 - v.1) % 17 ∈ quadraticResidues17

instance paleyPrefix12AdjDecidable : DecidableRel paleyPrefix12.Adj := fun u v ↦ by
  rw [paleyPrefix12, SimpleGraph.fromRel_adj]
  infer_instance

/-- Four labelled vertices form a homogeneous set. -/
def HomogeneousFour {V : Type*} (G : SimpleGraph V) (a b c d : V) : Prop :=
  (G.Adj a b ∧ G.Adj a c ∧ G.Adj a d ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj c d) ∨
  (¬ G.Adj a b ∧ ¬ G.Adj a c ∧ ¬ G.Adj a d ∧
    ¬ G.Adj b c ∧ ¬ G.Adj b d ∧ ¬ G.Adj c d)

instance instDecidableHomogeneousFour {V : Type*} (G : SimpleGraph V)
    [DecidableRel G.Adj] (a b c d : V) : Decidable (HomogeneousFour G a b c d) := by
  unfold HomogeneousFour
  infer_instance

/-- Small kernel computation on four labelled vertices: the Paley-prefix witness has no
homogeneous four-tuple of pairwise distinct vertices. -/
theorem paleyPrefix12_no_homogeneous_four_points :
    ∀ a b c d : Fin 12,
      a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
      ¬ HomogeneousFour paleyPrefix12 a b c d := by
  decide

/-- The labelled four-vertex certificate implies the finset formulation. -/
theorem paleyPrefix12_no_homogeneous_four : HasNoHomogeneousFour paleyPrefix12 := by
  intro S hcard hhom
  have hlarge : 3 < S.card := by omega
  obtain ⟨a, b, c, d, ha, hb, hc, hd, hab, hac, had, hbc, hbd, hcd⟩ :=
    Finset.three_lt_card_iff.mp hlarge
  apply paleyPrefix12_no_homogeneous_four_points a b c d hab hac had hbc hbd hcd
  rcases hhom with h | h
  · left
    exact ⟨h a ha b hb hab, h a ha c hc hac, h a ha d hd had,
      h b hb c hc hbc, h b hb d hd hbd, h c hc d hd hcd⟩
  · right
    exact ⟨h a ha b hb hab, h a ha c hc hac, h a ha d hd had,
      h b hb c hc hbc, h b hb d hd hbd, h c hc d hd hcd⟩

/-- The explicit twelve-vertex witness needs at least four cochromatic colours. -/
theorem paleyPrefix12_not_three : ¬ CochromaticColorable paleyPrefix12 3 :=
  not_cochromaticColorable_three_of_no_homogeneous_four _
    paleyPrefix12_no_homogeneous_four

/-! ## The eight-vertex decomposition certificate

The checked LRAT certificate proves the finite statement used in the upper
bound: every two-colouring of the edges of `K₈` has either a monochromatic
four-set or two vertex-disjoint monochromatic triples.  The semantic bridge
below turns those alternatives into three cochromatic colour classes.
-/

namespace D8Certificate

lrat_proof raw
  (include_str "Erdos758/D8.cnf")
  (include_str "Erdos758/D8.lrat")

open Lean Elab Term Meta

private def choose : (k : Nat) → List Nat → List (List Nat)
  | 0, _ => [[]]
  | _ + 1, [] => []
  | k + 1, x :: xs =>
      (choose k xs).map (fun ys => x :: ys) ++ choose (k + 1) xs

private def pairs : List Nat → List (Nat × Nat)
  | [] => []
  | x :: xs => xs.map (fun y => (x, y)) ++ pairs xs

private def edges : List (Nat × Nat) := pairs (List.range 8)

private def triangles : List (List Nat) := choose 3 (List.range 8)

private def edgeIndex (i j : Nat) : Nat :=
  (edges.zipIdx.find? fun p => p.1 = (i, j)).get!.2

private def edgeExpr (e : Expr) (i j : Nat) : Expr :=
  mkApp e (mkNatLit (edgeIndex i j))

private def mkAndExpr : List Expr → MetaM Expr
  | [] => pure (mkConst ``True)
  | [p] => pure p
  | p :: ps => return mkApp2 (mkConst ``And) p (← mkAndExpr ps)

private def homogeneousExpr (e : Expr) (s : List Nat) : MetaM Expr := do
  let es := (pairs s).map fun ij => edgeExpr e ij.1 ij.2
  let pos ← mkAndExpr es
  let neg ← mkAndExpr (es.map fun p => mkApp (mkConst ``Not) p)
  return mkApp2 (mkConst ``Or) pos neg

private def homogeneousParts (e : Expr) (s : List Nat) : MetaM (Expr × Expr) := do
  let es := (pairs s).map fun ij => edgeExpr e ij.1 ij.2
  return (← mkAndExpr es, ← mkAndExpr (es.map fun p => mkApp (mkConst ``Not) p))

private def disjoint (s t : List Nat) : Bool :=
  s.all fun x => !t.contains x

private partial def balancedOr (xs : Array Expr) (start stop : Nat) : Expr :=
  match stop - start with
  | 0 => mkConst ``False
  | 1 => xs[start]!
  | len =>
      let mid := start + len / 2
      mkApp2 (mkConst ``Or) (balancedOr xs start mid) (balancedOr xs mid stop)

private inductive LeafKind
  | same
  | impossible (pos neg : Expr) (positive : Bool)
  deriving Inhabited

private inductive ColoringKind
  | four (s : List Nat) (positive : Bool)
  | twoTriples (s t : List Nat)
  deriving Inhabited

private structure Leaf where
  raw : Expr
  target : Expr
  kind : LeafKind
  coloring : Option ColoringKind
  deriving Inhabited

private def leaves (e : Expr) : MetaM (Array Leaf) := do
  let mut out := #[]
  for s in choose 4 (List.range 8) do
    let (pos, neg) ← homogeneousParts e s
    out := out.push ⟨pos, pos, .same, some (.four s true)⟩
    out := out.push ⟨neg, neg, .same, some (.four s false)⟩
  for s in triangles do
    let (pos, neg) ← homogeneousParts e s
    let hom := mkApp2 (mkConst ``Or) pos neg
    out := out.push ⟨mkApp2 (mkConst ``And) (mkApp (mkConst ``Not) hom) pos,
      mkConst ``False, .impossible pos neg true, none⟩
    out := out.push ⟨mkApp2 (mkConst ``And) (mkApp (mkConst ``Not) hom) neg,
      mkConst ``False, .impossible pos neg false, none⟩
  let mut twoTriples := []
  for (s, i) in triangles.zipIdx do
    for (t, j) in triangles.zipIdx do
      if i < j && disjoint s t then
        let hs ← homogeneousExpr e s
        let ht ← homogeneousExpr e t
        twoTriples := (mkApp2 (mkConst ``And) hs ht, s, t) :: twoTriples
  for (p, s, t) in twoTriples.reverse do
    out := out.push ⟨p, p, .same, some (.twoTriples s t)⟩
  return out

private def conclusionExpr (e : Expr) : MetaM Expr := do
  let ls ← leaves e
  return balancedOr (ls.map fun l => l.target) 0 ls.size

private def rawSpecialization (e : Expr) : MetaM Expr := do
  let mut out := Lean.mkConst ``raw
  for (i, j) in edges do
    out := mkApp out (edgeExpr e i j)
  for s in triangles do
    out := mkApp out (← homogeneousExpr e s)
  return out

private partial def bridgeRange (ls : Array Leaf) (start stop : Nat)
    (h : Expr) : MetaM Expr := do
  match stop - start with
  | 0 => return mkApp (mkConst ``False.elim) h
  | 1 =>
      match ls[start]!.kind with
      | .same => return h
      | .impossible pos neg positive =>
          let hom := mkApp2 (mkConst ``Or) pos neg
          let notHom := mkApp3 (mkConst ``And.left) (mkApp (mkConst ``Not) hom)
            (if positive then pos else neg) h
          let mono := mkApp3 (mkConst ``And.right) (mkApp (mkConst ``Not) hom)
            (if positive then pos else neg) h
          let witness := if positive then
            mkApp3 (mkConst ``Or.inl) pos neg mono
          else
            mkApp3 (mkConst ``Or.inr) pos neg mono
          return mkApp notHom witness
  | len =>
      let mid := start + len / 2
      let rawLeft := balancedOr (ls.map fun l => l.raw) start mid
      let rawRight := balancedOr (ls.map fun l => l.raw) mid stop
      let targetLeft := balancedOr (ls.map fun l => l.target) start mid
      let targetRight := balancedOr (ls.map fun l => l.target) mid stop
      let target := mkApp2 (mkConst ``Or) targetLeft targetRight
      withLocalDeclD `hl rawLeft fun hl => do
        let pl ← bridgeRange ls start mid hl
        let pl := mkApp3 (mkConst ``Or.inl) targetLeft targetRight pl
        let fl ← mkLambdaFVars #[hl] pl
        withLocalDeclD `hr rawRight fun hr => do
          let pr ← bridgeRange ls mid stop hr
          let pr := mkApp3 (mkConst ``Or.inr) targetLeft targetRight pr
          let fr ← mkLambdaFVars #[hr] pr
          return mkApp6 (mkConst ``Or.elim) rawLeft rawRight target h fl fr

private def bridgedSpecialization (e : Expr) : MetaM Expr := do
  let ls ← leaves e
  bridgeRange ls 0 ls.size (← rawSpecialization e)

syntax "d8ConclusionBody(" term ")" : term
syntax "d8BridgedSpecialized(" term ")" : term

elab_rules : term
  | `(d8ConclusionBody($e)) => do
      conclusionExpr (← elabTerm e none)
  | `(d8BridgedSpecialized($e)) => do
      bridgedSpecialization (← elabTerm e none)

private def Conclusion (edge : Nat → Prop) : Prop := d8ConclusionBody(edge)

private theorem semantic (edge : Nat → Prop) : Conclusion edge := by
  exact d8BridgedSpecialized(edge)

private theorem homogeneous_of_card_le_two {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) (hcard : S.card ≤ 2) :
    IsHomogeneousFinset G S := by
  by_cases h : ∃ u ∈ S, ∃ v ∈ S, u ≠ v ∧ G.Adj u v
  · obtain ⟨u, hu, v, hv, huv, hadj⟩ := h
    have hpair : ({u, v} : Finset V) ⊆ S := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact hu
      · exact hv
    have heq : ({u, v} : Finset V) = S :=
      Finset.eq_of_subset_of_card_le hpair (by
        calc
          S.card ≤ 2 := hcard
          _ = ({u, v} : Finset V).card := (Finset.card_pair huv).symm)
    left
    intro x hx y hy hxy
    rw [← heq] at hx hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact (hxy rfl).elim
    · exact hadj
    · exact hadj.symm
    · exact (hxy rfl).elim
  · right
    intro u hu v hv huv hadj
    exact h ⟨u, hu, v, hv, huv, hadj⟩

private theorem colorable_of_three_homogeneous_blocks (G : SimpleGraph (Fin 8))
    (A B C : Finset (Fin 8))
    (cover : ∀ v, v ∈ A ∨ v ∈ B ∨ v ∈ C)
    (hA : IsHomogeneousFinset G A) (hB : IsHomogeneousFinset G B)
    (hC : IsHomogeneousFinset G C) : CochromaticColorable G 3 := by
  let c : Fin 8 → Fin 3 := fun v ↦ if v ∈ A then 0 else if v ∈ B then 1 else 2
  refine ⟨c, ?_⟩
  have fiber_mem_A : ∀ v, c v = 0 → v ∈ A := by
    intro v hv
    by_contra hn
    by_cases hb : v ∈ B
    · simp [c, hn, hb] at hv
    · simp [c, hn, hb] at hv
  have fiber_mem_B : ∀ v, c v = 1 → v ∈ B := by
    intro v hv
    by_cases ha : v ∈ A
    · simp [c, ha] at hv
    by_contra hb
    simp [c, ha, hb] at hv
  have fiber_mem_C : ∀ v, c v = 2 → v ∈ C := by
    intro v hv
    by_cases ha : v ∈ A
    · simp [c, ha] at hv
    by_cases hb : v ∈ B
    · simp [c, ha, hb] at hv
    rcases cover v with hA | hB | hC
    · exact (ha hA).elim
    · exact (hb hB).elim
    · exact hC
  intro i
  fin_cases i
  · rcases hA with hA | hA
    · left
      intro u v hu hv huv
      exact hA u (fiber_mem_A u hu) v (fiber_mem_A v hv) huv
    · right
      intro u v hu hv huv
      exact hA u (fiber_mem_A u hu) v (fiber_mem_A v hv) huv
  · rcases hB with hB | hB
    · left
      intro u v hu hv huv
      exact hB u (fiber_mem_B u hu) v (fiber_mem_B v hv) huv
    · right
      intro u v hu hv huv
      exact hB u (fiber_mem_B u hu) v (fiber_mem_B v hv) huv
  · rcases hC with hC | hC
    · left
      intro u v hu hv huv
      exact hC u (fiber_mem_C u hu) v (fiber_mem_C v hv) huv
    · right
      intro u v hu hv huv
      exact hC u (fiber_mem_C u hu) v (fiber_mem_C v hv) huv

private def unorderedPairs {α : Type*} : List α → List (α × α)
  | [] => []
  | x :: xs => xs.map (fun y => (x, y)) ++ unorderedPairs xs

private def conjunction : List Prop → Prop
  | [] => True
  | [p] => p
  | p :: q :: ps => p ∧ conjunction (q :: ps)

private def PairConjunction {α : Type*} (r : α → α → Prop) (xs : List α) : Prop :=
  conjunction ((unorderedPairs xs).map fun p => r p.1 p.2)

private theorem conjunction_of_mem {ps : List Prop} (h : conjunction ps)
    {p : Prop} (hp : p ∈ ps) : p := by
  induction ps with
  | nil => simp at hp
  | cons q qs ih =>
      cases qs with
      | nil =>
          simp only [List.mem_singleton] at hp
          subst p
          exact h
      | cons r rs =>
          simp only [conjunction] at h
          rcases h with ⟨hq, hrest⟩
          simp only [List.mem_cons] at hp
          rcases hp with rfl | hp
          · exact hq
          · exact ih hrest (by simpa only [List.mem_cons] using hp)

private theorem pair_mem_unorderedPairs_of_mem_ne {α : Type*} [DecidableEq α]
    {u v : α} {xs : List α} (hu : u ∈ xs) (hv : v ∈ xs) (hne : u ≠ v) :
    (u, v) ∈ unorderedPairs xs ∨ (v, u) ∈ unorderedPairs xs := by
  induction xs with
  | nil => simp at hu
  | cons x xs ih =>
      simp only [List.mem_cons] at hu hv
      rcases hu with rfl | hu <;> rcases hv with rfl | hv
      · exact (hne rfl).elim
      · left
        simp [unorderedPairs, hv]
      · right
        simp [unorderedPairs, hu]
      · rcases ih hu hv with hp | hp
        · left
          simp [unorderedPairs, hp]
        · right
          simp [unorderedPairs, hp]

private theorem homogeneous_of_pairConjunction_pos (G : SimpleGraph (Fin 8))
    (xs : List (Fin 8)) (h : PairConjunction G.Adj xs) :
    IsHomogeneousFinset G xs.toFinset := by
  left
  intro u hu v hv hne
  have hu' : u ∈ xs := by simpa using hu
  have hv' : v ∈ xs := by simpa using hv
  rcases pair_mem_unorderedPairs_of_mem_ne hu' hv' hne with hp | hp
  · exact conjunction_of_mem h (List.mem_map.mpr ⟨(u, v), hp, rfl⟩)
  · exact (conjunction_of_mem h (List.mem_map.mpr ⟨(v, u), hp, rfl⟩)).symm

private theorem homogeneous_of_pairConjunction_neg (G : SimpleGraph (Fin 8))
    (xs : List (Fin 8))
    (h : PairConjunction (fun u v => ¬ G.Adj u v) xs) :
    IsHomogeneousFinset G xs.toFinset := by
  right
  intro u hu v hv hne
  have hu' : u ∈ xs := by simpa using hu
  have hv' : v ∈ xs := by simpa using hv
  rcases pair_mem_unorderedPairs_of_mem_ne hu' hv' hne with hp | hp
  · exact conjunction_of_mem h (List.mem_map.mpr ⟨(u, v), hp, rfl⟩)
  · intro huv
    exact conjunction_of_mem h (List.mem_map.mpr ⟨(v, u), hp, rfl⟩) huv.symm

private def CoverThree (A B C : List (Fin 8)) : Prop :=
  ∀ v, v ∈ A ∨ v ∈ B ∨ v ∈ C

private instance (A B C : List (Fin 8)) : Decidable (CoverThree A B C) := by
  unfold CoverThree
  infer_instance

private theorem colorable_of_positive_four (G : SimpleGraph (Fin 8))
    (A B C : List (Fin 8)) (cover : CoverThree A B C)
    (hB : B.toFinset.card ≤ 2) (hC : C.toFinset.card ≤ 2)
    (hA : PairConjunction G.Adj A) : CochromaticColorable G 3 := by
  apply colorable_of_three_homogeneous_blocks G A.toFinset B.toFinset C.toFinset
  · simpa [CoverThree] using cover
  · exact homogeneous_of_pairConjunction_pos G A hA
  · exact homogeneous_of_card_le_two G B.toFinset hB
  · exact homogeneous_of_card_le_two G C.toFinset hC

private theorem colorable_of_negative_four (G : SimpleGraph (Fin 8))
    (A B C : List (Fin 8)) (cover : CoverThree A B C)
    (hB : B.toFinset.card ≤ 2) (hC : C.toFinset.card ≤ 2)
    (hA : PairConjunction (fun u v => ¬ G.Adj u v) A) :
    CochromaticColorable G 3 := by
  apply colorable_of_three_homogeneous_blocks G A.toFinset B.toFinset C.toFinset
  · simpa [CoverThree] using cover
  · exact homogeneous_of_pairConjunction_neg G A hA
  · exact homogeneous_of_card_le_two G B.toFinset hB
  · exact homogeneous_of_card_le_two G C.toFinset hC

private theorem colorable_of_two_triples (G : SimpleGraph (Fin 8))
    (A B C : List (Fin 8)) (cover : CoverThree A B C)
    (hC : C.toFinset.card ≤ 2)
    (hAB :
      (PairConjunction G.Adj A ∨ PairConjunction (fun u v => ¬ G.Adj u v) A) ∧
      (PairConjunction G.Adj B ∨ PairConjunction (fun u v => ¬ G.Adj u v) B)) :
    CochromaticColorable G 3 := by
  apply colorable_of_three_homogeneous_blocks G A.toFinset B.toFinset C.toFinset
  · simpa [CoverThree] using cover
  · rcases hAB.1 with h | h
    · exact homogeneous_of_pairConjunction_pos G A h
    · exact homogeneous_of_pairConjunction_neg G A h
  · rcases hAB.2 with h | h
    · exact homogeneous_of_pairConjunction_pos G B h
    · exact homogeneous_of_pairConjunction_neg G B h
  · exact homogeneous_of_card_le_two G C.toFinset hC

private def graphEdge (G : SimpleGraph (Fin 8)) : Nat → Prop
  | 0 => G.Adj 0 1
  | 1 => G.Adj 0 2
  | 2 => G.Adj 0 3
  | 3 => G.Adj 0 4
  | 4 => G.Adj 0 5
  | 5 => G.Adj 0 6
  | 6 => G.Adj 0 7
  | 7 => G.Adj 1 2
  | 8 => G.Adj 1 3
  | 9 => G.Adj 1 4
  | 10 => G.Adj 1 5
  | 11 => G.Adj 1 6
  | 12 => G.Adj 1 7
  | 13 => G.Adj 2 3
  | 14 => G.Adj 2 4
  | 15 => G.Adj 2 5
  | 16 => G.Adj 2 6
  | 17 => G.Adj 2 7
  | 18 => G.Adj 3 4
  | 19 => G.Adj 3 5
  | 20 => G.Adj 3 6
  | 21 => G.Adj 3 7
  | 22 => G.Adj 4 5
  | 23 => G.Adj 4 6
  | 24 => G.Adj 4 7
  | 25 => G.Adj 5 6
  | 26 => G.Adj 5 7
  | 27 => G.Adj 6 7
  | _ => False

private def fin8ListExpr (xs : List Nat) : MetaM Expr := do
  let fin8 := mkApp (mkConst ``Fin) (mkNatLit 8)
  let mut out := []
  for x in xs do
    let hxTy ← mkAppM ``LT.lt #[mkNatLit x, mkNatLit 8]
    let hx ← mkDecideProof hxTy
    out := mkApp3 (mkConst ``Fin.mk) (mkNatLit 8) (mkNatLit x) hx :: out
  mkListLit fin8 out.reverse

private def coloringLeafProof (G : Expr) (leaf : Leaf) (h : Expr) : MetaM Expr := do
  match leaf.coloring with
  | none =>
      let target ← mkAppM ``CochromaticColorable #[G, mkNatLit 3]
      return mkApp2 (mkConst ``False.elim [0]) target h
  | some (.four s positive) =>
      let rest := (List.range 8).filter fun x => !s.contains x
      let b := rest.take 2
      let c := rest.drop 2
      let A ← fin8ListExpr s
      let B ← fin8ListExpr b
      let C ← fin8ListExpr c
      let cover ← mkDecideProof (mkApp3 (mkConst ``CoverThree) A B C)
      let bFinset ← mkAppM ``List.toFinset #[B]
      let cFinset ← mkAppM ``List.toFinset #[C]
      let bCard ← mkAppM ``Finset.card #[bFinset]
      let cCard ← mkAppM ``Finset.card #[cFinset]
      let hbTy ← mkAppM ``LE.le #[bCard, mkNatLit 2]
      let hcTy ← mkAppM ``LE.le #[cCard, mkNatLit 2]
      let hb ← mkDecideProof hbTy
      let hc ← mkDecideProof hcTy
      let helperName := if positive then
        ``colorable_of_positive_four
      else
        ``colorable_of_negative_four
      mkAppM helperName #[G, A, B, C, cover, hb, hc, h]
  | some (.twoTriples s t) =>
      let rest := (List.range 8).filter fun x => !s.contains x && !t.contains x
      let A ← fin8ListExpr s
      let B ← fin8ListExpr t
      let C ← fin8ListExpr rest
      let cover ← mkDecideProof (mkApp3 (mkConst ``CoverThree) A B C)
      let cFinset ← mkAppM ``List.toFinset #[C]
      let cCard ← mkAppM ``Finset.card #[cFinset]
      let hcTy ← mkAppM ``LE.le #[cCard, mkNatLit 2]
      let hc ← mkDecideProof hcTy
      mkAppM ``colorable_of_two_triples #[G, A, B, C, cover, hc, h]

private partial def graphColoringRange (G : Expr) (ls : Array Leaf)
    (start stop : Nat) (h : Expr) : MetaM Expr := do
  match stop - start with
  | 0 =>
      let target ← mkAppM ``CochromaticColorable #[G, mkNatLit 3]
      return mkApp2 (mkConst ``False.elim [0]) target h
  | 1 => coloringLeafProof G ls[start]! h
  | len =>
      let mid := start + len / 2
      let left := balancedOr (ls.map fun l => l.target) start mid
      let right := balancedOr (ls.map fun l => l.target) mid stop
      let target ← mkAppM ``CochromaticColorable #[G, mkNatLit 3]
      withLocalDeclD `hl left fun hl => do
        let pl ← graphColoringRange G ls start mid hl
        let fl ← mkLambdaFVars #[hl] pl
        withLocalDeclD `hr right fun hr => do
          let pr ← graphColoringRange G ls mid stop hr
          let fr ← mkLambdaFVars #[hr] pr
          return mkApp6 (mkConst ``Or.elim) left right target h fl fr

private def graphColoringSpecialization (G : Expr) : MetaM Expr := do
  let edge := mkApp (mkConst ``graphEdge) G
  let ls ← leaves edge
  graphColoringRange G ls 0 ls.size (mkApp (mkConst ``semantic) edge)

syntax "d8GraphColoring(" term ")" : term

elab_rules : term
  | `(d8GraphColoring($G)) => do
      graphColoringSpecialization (← elabTerm G none)

theorem everyGraphColorableThree (G : SimpleGraph (Fin 8)) :
    CochromaticColorable G 3 := by
  exact d8GraphColoring(G)

end D8Certificate

/-- Every graph on eight vertices is cochromatically colourable with three colours. -/
theorem every_graph_on_eight_colorable_three (G : SimpleGraph (Fin 8)) :
    CochromaticColorable G 3 :=
  D8Certificate.everyGraphColorableThree G

/-- Cochromatic colourability is invariant under relabelling by an equivalence. -/
theorem cochromaticColorable_comap_equiv {V W : Type*}
    (G : SimpleGraph W) (e : V ≃ W) (k : ℕ) :
    CochromaticColorable (G.comap e) k ↔ CochromaticColorable G k := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨fun w ↦ c (e.symm w), ?_⟩
    intro i
    rcases hc i with h | h
    · left
      intro u v hu hv huv
      have hne : e.symm u ≠ e.symm v := by
        intro heq
        exact huv (e.symm.injective heq)
      have hadj := h (e.symm u) (e.symm v) hu hv hne
      simpa only [SimpleGraph.comap_adj, Equiv.apply_symm_apply] using hadj
    · right
      intro u v hu hv huv
      have hne : e.symm u ≠ e.symm v := by
        intro heq
        exact huv (e.symm.injective heq)
      have hnadj := h (e.symm u) (e.symm v) hu hv hne
      simpa only [SimpleGraph.comap_adj, Equiv.apply_symm_apply] using hnadj
  · rintro ⟨c, hc⟩
    refine ⟨fun v ↦ c (e v), ?_⟩
    intro i
    rcases hc i with h | h
    · left
      intro u v hu hv huv
      simpa only [SimpleGraph.comap_adj] using
        h (e u) (e v) hu hv (e.injective.ne huv)
    · right
      intro u v hu hv huv
      simpa only [SimpleGraph.comap_adj] using
        h (e u) (e v) hu hv (e.injective.ne huv)

/-- Adjoin one homogeneous block to a cochromatic colouring of its complement.
The existing colours are embedded into `Fin (k + 1)` and the new block receives
the last colour. -/
theorem cochromaticColorable_add_homogeneous_block
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) (k : ℕ)
    (hrest : CochromaticColorable (G.induce {v | v ∉ S}) k)
    (hS : IsHomogeneousFinset G S) :
    CochromaticColorable G (k + 1) := by
  obtain ⟨d, hd⟩ := hrest
  let c : V → Fin (k + 1) := fun v ↦
    if h : v ∈ S then Fin.last k else (d ⟨v, h⟩).castSucc
  refine ⟨c, ?_⟩
  intro i
  rcases i.eq_castSucc_or_eq_last with ⟨j, rfl⟩ | rfl
  · have fiber_out (v : V) (hv : c v = j.castSucc) :
        ∃ h : v ∉ S, d ⟨v, h⟩ = j := by
      by_cases h : v ∈ S
      · have hbad : Fin.last k = j.castSucc := by simpa [c, h] using hv
        exact (j.castSucc_ne_last hbad.symm).elim
      · refine ⟨h, ?_⟩
        simpa [c, h] using hv
    rcases hd j with hj | hj
    · left
      intro u v hu hv huv
      obtain ⟨huS, hu'⟩ := fiber_out u hu
      obtain ⟨hvS, hv'⟩ := fiber_out v hv
      exact hj ⟨u, huS⟩ ⟨v, hvS⟩ hu' hv' (by
        intro he
        exact huv (congrArg Subtype.val he))
    · right
      intro u v hu hv huv
      obtain ⟨huS, hu'⟩ := fiber_out u hu
      obtain ⟨hvS, hv'⟩ := fiber_out v hv
      exact hj ⟨u, huS⟩ ⟨v, hvS⟩ hu' hv' (by
        intro he
        exact huv (congrArg Subtype.val he))
  · have fiber_in (v : V) (hv : c v = Fin.last k) : v ∈ S := by
      by_contra h
      simp [c, h] at hv
    rcases hS with hS | hS
    · left
      intro u v hu hv huv
      exact hS u (fiber_in u hu) v (fiber_in v hv) huv
    · right
      intro u v hu hv huv
      exact hS u (fiber_in u hu) v (fiber_in v hv) huv

/-- If a twelve-vertex graph has a homogeneous four-set, the universal
eight-vertex bound supplies a four-colour cochromatic colouring. -/
theorem colorable_four_of_homogeneous_four
    (G : SimpleGraph (Fin 12)) (S : Finset (Fin 12))
    (hcard : S.card = 4) (hS : IsHomogeneousFinset G S) :
    CochromaticColorable G 4 := by
  let T := {v : Fin 12 // v ∉ S}
  have hTcard : Fintype.card T = 8 := by
    dsimp [T]
    rw [Fintype.card_subtype_compl]
    simpa only [Fintype.card_fin, Fintype.card_coe, hcard] using
      (show 12 - 4 = 8 by decide)
  let e : Fin 8 ≃ T := Fintype.equivOfCardEq (by simpa using hTcard.symm)
  let R : SimpleGraph T := G.induce {v | v ∉ S}
  have hR : CochromaticColorable R 3 :=
    (cochromaticColorable_comap_equiv R e 3).mp
      (every_graph_on_eight_colorable_three (R.comap e))
  exact cochromaticColorable_add_homogeneous_block G S 3 hR hS

#print axioms every_graph_on_eight_colorable_three
#print axioms colorable_four_of_homogeneous_four

namespace D12Normalization

open SimpleGraph

noncomputable local instance graphAdjDecidableFin12
    (G : SimpleGraph (Fin 12)) : DecidableRel G.Adj :=
  Classical.decRel _

/-! Generic finite relabelling infrastructure for the symmetry reductions in Problem 758. -/

/-- A permutation which is obtained by extending a permutation of the subtype `S`
fixes every point outside `S`. -/
theorem exists_perm_sort_within {α : Type*} [Fintype α] [DecidableEq α]
    (S A B : Finset α) (hAS : A ⊆ S) (hBS : B ⊆ S) (hcard : A.card = B.card) :
    ∃ σ : Equiv.Perm α,
      (∀ x, σ x ∈ S ↔ x ∈ S) ∧
      (∀ x, x ∉ S → σ x = x) ∧
      (∀ x, x ∈ S → (σ x ∈ B ↔ x ∈ A)) := by
  classical
  let A' : Finset S := Finset.univ.filter fun x : S ↦ (x : α) ∈ A
  let B' : Finset S := Finset.univ.filter fun x : S ↦ (x : α) ∈ B
  have hcardA' : A'.card = A.card := by
    refine Finset.card_bij (s := A') (t := A) (fun x _ ↦ (x : α)) ?_ ?_ ?_
    · intro x hx
      simpa [A'] using hx
    · intro x hx y hy hxy
      exact Subtype.ext hxy
    · intro a ha
      exact ⟨⟨a, hAS ha⟩, by simp [A', ha], rfl⟩
  have hcardB' : B'.card = B.card := by
    refine Finset.card_bij (s := B') (t := B) (fun x _ ↦ (x : α)) ?_ ?_ ?_
    · intro x hx
      simpa [B'] using hx
    · intro x hx y hy hxy
      exact Subtype.ext hxy
    · intro b hb
      exact ⟨⟨b, hBS hb⟩, by simp [B', hb], rfl⟩
  obtain ⟨τ, hτ⟩ := Equiv.Perm.exists_map_finset_eq A' B'
    (hcardA'.trans (hcard.trans hcardB'.symm))
  let σ : Equiv.Perm α := τ.extendDomain (Equiv.refl S)
  refine ⟨σ, ?_, ?_, ?_⟩
  · intro x
    by_cases hx : x ∈ S
    · have hσ : σ x = (τ ⟨x, hx⟩ : S) := by
        exact Equiv.Perm.extendDomain_apply_subtype τ (Equiv.refl S) hx
      constructor
      · intro _
        exact hx
      · intro _
        rw [hσ]
        exact (τ ⟨x, hx⟩).property
    · have hσ := Equiv.Perm.extendDomain_apply_not_subtype τ (Equiv.refl S) hx
      constructor
      · intro hmem
        rw [hσ] at hmem
        exact (hx hmem).elim
      · intro hmem
        exact (hx hmem).elim
  · intro x hx
    exact Equiv.Perm.extendDomain_apply_not_subtype τ (Equiv.refl S) hx
  · intro x hx
    have hσ : σ x = (τ ⟨x, hx⟩ : S) := by
      exact Equiv.Perm.extendDomain_apply_subtype τ (Equiv.refl S) hx
    have hmem : τ ⟨x, hx⟩ ∈ B' ↔ (⟨x, hx⟩ : S) ∈ A' := by
      rw [← hτ]
      simp
    simpa [σ, A', B', hσ] using hmem

/-- The neighbors represented with a fixed classical decider, so later
relabellings do not carry graph-dependent finite-subtype instances. -/
noncomputable def neighbors12 (G : SimpleGraph (Fin 12)) (v : Fin 12) :
    Finset (Fin 12) :=
  @Finset.filter (Fin 12) (fun x ↦ G.Adj v x)
    (fun x ↦ Classical.propDecidable (G.Adj v x)) Finset.univ

@[simp] theorem mem_neighbors12 (G : SimpleGraph (Fin 12)) (v x : Fin 12) :
    x ∈ neighbors12 G v ↔ G.Adj v x := by
  unfold neighbors12
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- The number of neighbors. -/
noncomputable def degree12 (G : SimpleGraph (Fin 12)) (v : Fin 12) : ℕ :=
  (neighbors12 G v).card

theorem degree12_eq_degree (G : SimpleGraph (Fin 12)) (v : Fin 12) :
    degree12 G v = G.degree v := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  unfold degree12
  congr 1
  ext x
  simp only [mem_neighbors12, SimpleGraph.mem_neighborFinset]

theorem degree12_le_eleven (G : SimpleGraph (Fin 12)) (v : Fin 12) :
    degree12 G v ≤ 11 := by
  unfold degree12
  calc
    (neighbors12 G v).card ≤
        ((Finset.univ : Finset (Fin 12)).erase v).card := by
      apply Finset.card_le_card
      intro x hx
      have hadj : G.Adj v x := (mem_neighbors12 G v x).mp hx
      exact Finset.mem_erase.mpr ⟨(G.ne_of_adj hadj).symm, Finset.mem_univ _⟩
    _ = 11 := by simp

/-- Complement at a vertex has degree `card - 1 - degree`. -/
theorem degree_compl_fin12 (G : SimpleGraph (Fin 12)) (v : Fin 12) :
    degree12 Gᶜ v = 11 - degree12 G v := by
  have hcompl : neighbors12 Gᶜ v =
      (Finset.univ.erase v).filter (fun x ↦ ¬G.Adj v x) := by
    ext x
    simp only [mem_neighbors12, Finset.mem_filter, Finset.mem_erase,
      Finset.mem_univ, and_true, SimpleGraph.compl_adj]
    tauto
  have horig : neighbors12 G v =
      (Finset.univ.erase v).filter (fun x ↦ G.Adj v x) := by
    ext x
    simp only [mem_neighbors12, Finset.mem_filter, Finset.mem_erase,
      Finset.mem_univ, and_true]
    constructor
    · intro h
      exact ⟨(G.ne_of_adj h).symm, h⟩
    · exact fun h ↦ h.2
  unfold degree12
  rw [hcompl, horig]
  have hsum := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.erase v) (p := fun x ↦ G.Adj v x)
  have herase : (Finset.univ.erase v : Finset (Fin 12)).card = 11 := by simp
  omega

/-- Complementing if necessary makes the degree of vertex zero at least six. -/
noncomputable def orientAtZero (G : SimpleGraph (Fin 12)) : SimpleGraph (Fin 12) :=
  if 6 ≤ degree12 G 0 then G else Gᶜ

theorem orientAtZero_degree (G : SimpleGraph (Fin 12)) :
    6 ≤ degree12 (orientAtZero G) 0 := by
  classical
  by_cases h : 6 ≤ degree12 G 0
  · have hO : orientAtZero G = G := if_pos h
    rw [hO]
    exact h
  · have hO : orientAtZero G = Gᶜ := if_neg h
    rw [hO, degree_compl_fin12]
    have hdeg : degree12 G 0 ≤ 11 := degree12_le_eleven G 0
    omega

theorem orientAtZero_degree_le (G : SimpleGraph (Fin 12)) :
    degree12 (orientAtZero G) 0 ≤ 11 := by
  exact degree12_le_eleven (orientAtZero G) 0

/-- The labels `1,...,d`, viewed as a finset of `Fin n`. -/
def initialAfterZero (n d : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun i ↦ 0 < i.val ∧ i.val ≤ d

theorem card_initialAfterZero {n d : ℕ} (hd : d < n) :
    (initialAfterZero n d).card = d := by
  classical
  have hcard : (Finset.range d).card = (initialAfterZero n d).card := by
    refine Finset.card_bij (s := Finset.range d) (t := initialAfterZero n d)
        (fun i (hi : i ∈ Finset.range d) ↦ (⟨i + 1, by
          have hi' : i < d := Finset.mem_range.mp hi
          omega⟩ : Fin n)) ?_ ?_ ?_
    · intro i hi
      simp only [initialAfterZero, Finset.mem_filter, Finset.mem_univ, true_and]
      have hi' : i < d := Finset.mem_range.mp hi
      omega
    · intro i hi j hj hij
      have hijv : i + 1 = j + 1 := by
        simpa only [Fin.val_mk] using congrArg Fin.val hij
      omega
    · intro x hx
      simp only [initialAfterZero, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      refine ⟨x.val - 1, Finset.mem_range.mpr (by omega), ?_⟩
      apply Fin.ext
      simp only [Fin.val_mk]
      omega
  simpa only [Finset.card_range] using hcard.symm

/-- A consecutive block of `len` labels beginning with `start`. -/
def intervalFrom (n start len : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun i ↦ start ≤ i.val ∧ i.val < start + len

theorem card_intervalFrom {n start len : ℕ} (h : start + len ≤ n) :
    (intervalFrom n start len).card = len := by
  classical
  have hcard : (Finset.range len).card = (intervalFrom n start len).card := by
    refine Finset.card_bij (s := Finset.range len) (t := intervalFrom n start len)
        (fun i (hi : i ∈ Finset.range len) ↦ (⟨start + i, by
          have hi' : i < len := Finset.mem_range.mp hi
          omega⟩ : Fin n)) ?_ ?_ ?_
    · intro i hi
      simp only [intervalFrom, Finset.mem_filter, Finset.mem_univ, true_and]
      have hi' : i < len := Finset.mem_range.mp hi
      omega
    · intro i hi j hj hij
      apply Nat.add_left_cancel
      simpa only [Fin.val_mk] using congrArg Fin.val hij
    · intro x hx
      simp only [intervalFrom, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      refine ⟨x.val - start, Finset.mem_range.mpr (by omega), ?_⟩
      apply Fin.ext
      simp only [Fin.val_mk]
      omega
  simpa only [Finset.card_range] using hcard.symm

theorem intervalFrom_subset_intervalFrom {n a l a' l' : ℕ}
    (ha : a' ≤ a) (hz : a + l ≤ a' + l') :
    intervalFrom n a l ⊆ intervalFrom n a' l' := by
  intro x hx
  simp only [intervalFrom, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  omega

theorem mem_intervalFrom_two_iff_le {r : ℕ} {x : Fin 12} (hx : 2 ≤ x.val) :
    x ∈ intervalFrom 12 2 r ↔ x.val ≤ r + 1 := by
  simp only [intervalFrom, Finset.mem_filter, Finset.mem_univ, true_and]
  omega

theorem mem_intervalFrom_after_degree_iff_le {d s : ℕ} {x : Fin 12}
    (hx : d + 1 ≤ x.val) :
    x ∈ intervalFrom 12 (d + 1) s ↔ x.val ≤ d + s := by
  simp only [intervalFrom, Finset.mem_filter, Finset.mem_univ, true_and]
  omega

theorem mem_intervalFrom_residual_iff_le {r t : ℕ} {x : Fin 12}
    (hx : r + 2 ≤ x.val) :
    x ∈ intervalFrom 12 (r + 2) t ↔ x.val ≤ r + 1 + t := by
  simp only [intervalFrom, Finset.mem_filter, Finset.mem_univ, true_and]
  omega

theorem initialAfterZero_subset_erase_zero {n d : ℕ} [NeZero n] :
    initialAfterZero n d ⊆ Finset.univ.erase (0 : Fin n) := by
  intro x hx
  simp only [initialAfterZero, Finset.mem_filter, Finset.mem_univ, true_and] at hx
  simp only [Finset.mem_erase, Finset.mem_univ, and_true]
  intro h
  have hval : x.val = 0 := congrArg Fin.val h
  omega

theorem neighborFinset_subset_erase_self {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj] (v : α) :
    G.neighborFinset v ⊆ Finset.univ.erase v := by
  intro x hx
  have hadj : G.Adj v x := by simpa using hx
  exact Finset.mem_erase.mpr ⟨G.ne_of_adj hadj |>.symm, Finset.mem_univ _⟩

/-- Degree of a vertex with only neighbors in `S` counted. -/
def degreeWithin {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj] (S : Finset α) (v : α) : ℕ :=
  (S.filter fun x ↦ G.Adj v x).card

/-- A convenient finset formulation of being triangle-free on `S`: adjacent
vertices in `S` have no common neighbor in `S`. -/
def TriangleFreeOnFinset {α : Type*} (G : SimpleGraph α) (S : Finset α) : Prop :=
  ∀ a, a ∈ S → ∀ b, b ∈ S → G.Adj a b →
    ∀ x, x ∈ S → G.Adj a x → ¬G.Adj b x

/-- The elementary minimum-degree form of Mantel's argument.  If a
triangle-free graph has at most `2*k+1` vertices, some vertex has degree at
most `k`.  The proof takes an edge `a-b`; the two neighborhoods are disjoint. -/
theorem exists_degreeWithin_le_of_triangleFree
    {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (S : Finset α) (hne : S.Nonempty) (k : ℕ)
    (hcard : S.card ≤ 2 * k + 1) (htri : TriangleFreeOnFinset G S) :
    ∃ v ∈ S, degreeWithin G S v ≤ k := by
  classical
  obtain ⟨a, ha⟩ := hne
  let Na := S.filter fun x ↦ G.Adj a x
  by_cases hNa : Na.card ≤ k
  · exact ⟨a, ha, hNa⟩
  · have hNaPos : 0 < Na.card := by omega
    obtain ⟨b, hbNa⟩ := Finset.card_pos.mp hNaPos
    have hbS : b ∈ S := (Finset.mem_filter.mp hbNa).1
    have hab : G.Adj a b := (Finset.mem_filter.mp hbNa).2
    let Nb := S.filter fun x ↦ G.Adj b x
    have hdisj : Disjoint Na Nb := by
      rw [Finset.disjoint_left]
      intro x hxNa hxNb
      exact htri a ha b hbS hab x (Finset.mem_filter.mp hxNa).1
        (Finset.mem_filter.mp hxNa).2 (Finset.mem_filter.mp hxNb).2
    have hunion : Na ∪ Nb ⊆ S := by
      exact Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    have hsum : Na.card + Nb.card ≤ S.card := by
      rw [← Finset.card_union_of_disjoint hdisj]
      exact Finset.card_le_card hunion
    refine ⟨b, hbS, ?_⟩
    change Nb.card ≤ k
    omega

/-- Relabelling a cell setwise preserves its internal degree multiset. -/
theorem degreeWithin_comap_perm
    {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (S : Finset α) (σ : Equiv.Perm α)
    (hσS : ∀ x, σ x ∈ S ↔ x ∈ S) (p : α) :
    degreeWithin (G.comap σ) S p = degreeWithin G S (σ p) := by
  classical
  unfold degreeWithin
  apply Finset.card_bij (fun x _ ↦ σ x)
  · intro x hx
    rw [Finset.mem_filter] at hx ⊢
    exact ⟨(hσS x).2 hx.1, by simpa only [SimpleGraph.comap_adj] using hx.2⟩
  · intro x hx y hy hxy
    exact σ.injective hxy
  · intro y hy
    refine ⟨σ.symm y, ?_, σ.apply_symm_apply y⟩
    rw [Finset.mem_filter] at hy ⊢
    refine ⟨?_, ?_⟩
    · apply (hσS (σ.symm y)).1
      simpa using hy.1
    · change G.Adj (σ p) (σ (σ.symm y))
      simpa using hy.2

/-- A no-homogeneous-four graph is triangle-free on any set of neighbors of
one fixed vertex. -/
theorem triangleFreeOnFinset_of_no_homogeneous_four_at
    (G : SimpleGraph (Fin 12))
    (hno : ∀ S : Finset (Fin 12), S.card = 4 →
      ¬((∀ u ∈ S, ∀ v ∈ S, u ≠ v → G.Adj u v) ∨
        (∀ u ∈ S, ∀ v ∈ S, u ≠ v → ¬G.Adj u v)))
    (p : Fin 12) (S : Finset (Fin 12))
    (hpS : p ∉ S) (hp : ∀ x, x ∈ S → G.Adj p x) :
    TriangleFreeOnFinset G S := by
  intro a ha b hb hab x hx hax hbx
  have hpa := hp a ha
  have hpb := hp b hb
  have hpx := hp x hx
  have habne := G.ne_of_adj hab
  have haxne := G.ne_of_adj hax
  have hbxne := G.ne_of_adj hbx
  have hpane := G.ne_of_adj hpa
  have hpbne := G.ne_of_adj hpb
  have hpxne := G.ne_of_adj hpx
  let T : Finset (Fin 12) := {p, a, b, x}
  apply hno T
  · simp only [T]
    simp [hpane, hpbne, hpxne, habne, haxne, hbxne]
  · left
    intro u hu v hv huv
    simp only [T, Finset.mem_insert, Finset.mem_singleton] at hu hv
    rcases hu with rfl | rfl | rfl | rfl <;>
      rcases hv with rfl | rfl | rfl | rfl <;>
      simp_all only [SimpleGraph.irrefl, not_false_eq_true,
        SimpleGraph.adj_comm, ne_eq, not_true_eq_false]

/-- Relabel a graph so that the neighbors of vertex zero have precisely the labels
`1,...,degree(0)`.  The permutation fixes vertex zero. -/
theorem exists_root_neighbor_normalization (G : SimpleGraph (Fin 12))
    [DecidableRel G.Adj] :
    ∃ σ : Equiv.Perm (Fin 12),
      σ 0 = 0 ∧
      ∀ x : Fin 12,
        (G.comap σ).Adj 0 x ↔ x ∈ initialAfterZero 12 (degree12 G 0) := by
  classical
  have hd : degree12 G 0 < 12 := by
    exact lt_of_le_of_lt (degree12_le_eleven G 0) (by omega)
  obtain ⟨σ, hσS, hσfix, hσsort⟩ := exists_perm_sort_within
    (Finset.univ.erase (0 : Fin 12))
    (initialAfterZero 12 (degree12 G 0))
    (neighbors12 G 0)
    initialAfterZero_subset_erase_zero
    (by
      intro x hx
      have hadj : G.Adj 0 x := (mem_neighbors12 G 0 x).mp hx
      exact Finset.mem_erase.mpr ⟨(G.ne_of_adj hadj).symm, Finset.mem_univ _⟩)
    (card_initialAfterZero hd)
  refine ⟨σ, hσfix 0 (by simp), ?_⟩
  intro x
  by_cases hx : x = 0
  · subst x
    simp [initialAfterZero]
  · have hxS : x ∈ Finset.univ.erase (0 : Fin 12) := by simp [hx]
    rw [SimpleGraph.comap_adj, hσfix 0 (by simp)]
    simpa only [mem_neighbors12] using hσsort x hxS

/-- Sort the adjacency-to-`p` predicate inside a block `S`, placing exactly the
adjacent vertices in the prescribed target subblock `T`.  The relabelling fixes
the complement of `S` and preserves `S` setwise.  This can be applied repeatedly
to the nested cells in the certificate hierarchy. -/
theorem exists_comap_sort_adjacency_within
    {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (p : α) (S T : Finset α) (hpS : p ∉ S) (hTS : T ⊆ S)
    (hcard : T.card = (S.filter fun x ↦ G.Adj p x).card) :
    ∃ σ : Equiv.Perm α,
      σ p = p ∧
      (∀ x, σ x ∈ S ↔ x ∈ S) ∧
      (∀ x, x ∉ S → σ x = x) ∧
      ∀ x, x ∈ S → ((G.comap σ).Adj p x ↔ x ∈ T) := by
  classical
  obtain ⟨σ, hσS, hσfix, hσsort⟩ := exists_perm_sort_within
    S T (S.filter fun x ↦ G.Adj p x) hTS (Finset.filter_subset _ _ ) hcard
  refine ⟨σ, hσfix p hpS, hσS, hσfix, ?_⟩
  intro x hx
  rw [SimpleGraph.comap_adj, hσfix p hpS]
  have hσxS : σ x ∈ S := (hσS x).2 hx
  simpa only [Finset.mem_filter, hσxS, true_and] using hσsort x hx

/-- A later cell sort preserves every earlier pivot row which was constant on
that cell. -/
theorem exists_comap_sort_adjacency_within_preserving
    {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (p q : α) (S T : Finset α) (hpS : p ∉ S) (hqS : q ∉ S)
    (hTS : T ⊆ S)
    (hcard : T.card = (S.filter fun x ↦ G.Adj p x).card)
    (b : Prop) (hconst : ∀ x, x ∈ S → (G.Adj q x ↔ b)) :
    ∃ σ : Equiv.Perm α,
      σ p = p ∧ σ q = q ∧
      (∀ x, σ x ∈ S ↔ x ∈ S) ∧
      (∀ x, x ∉ S → σ x = x) ∧
      (∀ x, x ∈ S → ((G.comap σ).Adj p x ↔ x ∈ T)) ∧
      ∀ x, x ∈ S → ((G.comap σ).Adj q x ↔ b) := by
  classical
  obtain ⟨σ, hp, hσS, hσfix, hsort⟩ :=
    exists_comap_sort_adjacency_within G p S T hpS hTS hcard
  refine ⟨σ, hp, hσfix q hqS, hσS, hσfix, hsort, ?_⟩
  intro x hx
  rw [SimpleGraph.comap_adj, hσfix q hqS]
  exact hconst (σ x) ((hσS x).2 hx)

/-- Normalize the part of row one inside `A = {1,...,d}`.  On the cell
`{2,...,d}`, its `r` neighbors are moved to `{2,...,r+1}` while row zero
remains constantly true. -/
theorem exists_sort_row_one_inside
    (G : SimpleGraph (Fin 12)) [DecidableRel G.Adj]
    (d r : ℕ) (hdpos : 1 ≤ d) (hdle : d ≤ 11) (hr : r ≤ d - 1)
    (hcount : ((intervalFrom 12 2 (d - 1)).filter fun x ↦ G.Adj 1 x).card = r)
    (hroot : ∀ x, x ∈ intervalFrom 12 2 (d - 1) → G.Adj 0 x) :
    ∃ σ : Equiv.Perm (Fin 12),
      σ 0 = 0 ∧ σ 1 = 1 ∧
      (∀ x, σ x ∈ intervalFrom 12 2 (d - 1) ↔
        x ∈ intervalFrom 12 2 (d - 1)) ∧
      (∀ x, x ∉ intervalFrom 12 2 (d - 1) → σ x = x) ∧
      (∀ x, x ∈ intervalFrom 12 2 (d - 1) →
        ((G.comap σ).Adj 1 x ↔ x ∈ intervalFrom 12 2 r)) ∧
      ∀ x, x ∈ intervalFrom 12 2 (d - 1) → (G.comap σ).Adj 0 x := by
  classical
  have h2r : 2 + r ≤ 12 := by omega
  have hsub : intervalFrom 12 2 r ⊆ intervalFrom 12 2 (d - 1) :=
    intervalFrom_subset_intervalFrom (by omega) (by omega)
  have h0out : (0 : Fin 12) ∉ intervalFrom 12 2 (d - 1) := by
    simp [intervalFrom]
  have h1out : (1 : Fin 12) ∉ intervalFrom 12 2 (d - 1) := by
    simp [intervalFrom]
  have hcard : (intervalFrom 12 2 r).card =
      ((intervalFrom 12 2 (d - 1)).filter fun x ↦ G.Adj 1 x).card := by
    rw [card_intervalFrom h2r, hcount]
  obtain ⟨σ, h1, h0, hσS, hσfix, hrow, hkeep⟩ :=
    exists_comap_sort_adjacency_within_preserving G 1 0
      (intervalFrom 12 2 (d - 1)) (intervalFrom 12 2 r)
      h1out h0out hsub hcard True
      (fun x hx ↦ iff_true_intro (hroot x hx))
  exact ⟨σ, h0, h1, hσS, hσfix, hrow,
    fun x hx ↦ (hkeep x hx).2 trivial⟩

/-- Normalize the part of row one outside `A ∪ {0}`.  Its `s` neighbors
are moved to the first `s` labels of `{d+1,...,11}`, while row zero remains
constantly false. -/
theorem exists_sort_row_one_outside
    (G : SimpleGraph (Fin 12)) [DecidableRel G.Adj]
    (d s : ℕ) (hdpos : 1 ≤ d) (hd : d ≤ 11) (hs : s ≤ 11 - d)
    (hcount : ((intervalFrom 12 (d + 1) (11 - d)).filter
      fun x ↦ G.Adj 1 x).card = s)
    (hroot : ∀ x, x ∈ intervalFrom 12 (d + 1) (11 - d) → ¬G.Adj 0 x) :
    ∃ σ : Equiv.Perm (Fin 12),
      σ 0 = 0 ∧ σ 1 = 1 ∧
      (∀ x, σ x ∈ intervalFrom 12 (d + 1) (11 - d) ↔
        x ∈ intervalFrom 12 (d + 1) (11 - d)) ∧
      (∀ x, x ∉ intervalFrom 12 (d + 1) (11 - d) → σ x = x) ∧
      (∀ x, x ∈ intervalFrom 12 (d + 1) (11 - d) →
        ((G.comap σ).Adj 1 x ↔ x ∈ intervalFrom 12 (d + 1) s)) ∧
      ∀ x, x ∈ intervalFrom 12 (d + 1) (11 - d) → ¬(G.comap σ).Adj 0 x := by
  classical
  have hds : d + 1 + s ≤ 12 := by omega
  have hsub : intervalFrom 12 (d + 1) s ⊆
      intervalFrom 12 (d + 1) (11 - d) :=
    intervalFrom_subset_intervalFrom (by omega) (by omega)
  have h0out : (0 : Fin 12) ∉ intervalFrom 12 (d + 1) (11 - d) := by
    simp only [intervalFrom, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have h1out : (1 : Fin 12) ∉ intervalFrom 12 (d + 1) (11 - d) := by
    simp only [intervalFrom, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have hcard : (intervalFrom 12 (d + 1) s).card =
      ((intervalFrom 12 (d + 1) (11 - d)).filter fun x ↦ G.Adj 1 x).card := by
    rw [card_intervalFrom hds, hcount]
  obtain ⟨σ, h1, h0, hσS, hσfix, hrow, hkeep⟩ :=
    exists_comap_sort_adjacency_within_preserving G 1 0
      (intervalFrom 12 (d + 1) (11 - d)) (intervalFrom 12 (d + 1) s)
      h1out h0out hsub hcard False
      (fun x hx ↦ iff_false_intro (hroot x hx))
  exact ⟨σ, h0, h1, hσS, hσfix, hrow,
    fun x hx hadj ↦ (hkeep x hx).1 hadj⟩

/-- Normalize row two on the residual inside cell `B={r+2,...,d}`.
Rows zero and one are preserved because they are respectively constantly
true and constantly false on this cell. -/
theorem exists_sort_row_two_residual
    (G : SimpleGraph (Fin 12)) [DecidableRel G.Adj]
    (d r t : ℕ) (hd : d ≤ 11) (hrpos : 1 ≤ r) (hrd : r + 1 ≤ d)
    (ht : t ≤ d - (r + 1))
    (hcount : ((intervalFrom 12 (r + 2) (d - (r + 1))).filter
      fun x ↦ G.Adj 2 x).card = t)
    (hroot : ∀ x, x ∈ intervalFrom 12 (r + 2) (d - (r + 1)) → G.Adj 0 x)
    (hrow1 : ∀ x, x ∈ intervalFrom 12 (r + 2) (d - (r + 1)) → ¬G.Adj 1 x) :
    ∃ σ : Equiv.Perm (Fin 12),
      σ 0 = 0 ∧ σ 1 = 1 ∧ σ 2 = 2 ∧
      (∀ x, σ x ∈ intervalFrom 12 (r + 2) (d - (r + 1)) ↔
        x ∈ intervalFrom 12 (r + 2) (d - (r + 1))) ∧
      (∀ x, x ∉ intervalFrom 12 (r + 2) (d - (r + 1)) → σ x = x) ∧
      (∀ x, x ∈ intervalFrom 12 (r + 2) (d - (r + 1)) →
        ((G.comap σ).Adj 2 x ↔ x ∈ intervalFrom 12 (r + 2) t)) ∧
      (∀ x, x ∈ intervalFrom 12 (r + 2) (d - (r + 1)) →
        (G.comap σ).Adj 0 x) ∧
      ∀ x, x ∈ intervalFrom 12 (r + 2) (d - (r + 1)) →
        ¬(G.comap σ).Adj 1 x := by
  classical
  let S := intervalFrom 12 (r + 2) (d - (r + 1))
  let T := intervalFrom 12 (r + 2) t
  have hrt : r + 2 + t ≤ 12 := by omega
  have hsub : T ⊆ S := by
    exact intervalFrom_subset_intervalFrom (by omega) (by omega)
  have h0out : (0 : Fin 12) ∉ S := by
    simp only [S, intervalFrom, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have h1out : (1 : Fin 12) ∉ S := by
    simp only [S, intervalFrom, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have h2out : (2 : Fin 12) ∉ S := by
    simp only [S, intervalFrom, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have hcard : T.card = (S.filter fun x ↦ G.Adj 2 x).card := by
    dsimp only [T, S]
    rw [card_intervalFrom hrt, hcount]
  obtain ⟨σ, h2, hσS, hσfix, hrow⟩ :=
    exists_comap_sort_adjacency_within G 2 S T h2out hsub hcard
  refine ⟨σ, hσfix 0 h0out, hσfix 1 h1out, h2, hσS, hσfix, hrow, ?_, ?_⟩
  · intro x hx
    rw [SimpleGraph.comap_adj, hσfix 0 h0out]
    exact hroot (σ x) ((hσS x).2 hx)
  · intro x hx
    rw [SimpleGraph.comap_adj, hσfix 1 h1out]
    exact hrow1 (σ x) ((hσS x).2 hx)

theorem filter_adj_initial_eq_inside
    (G : SimpleGraph (Fin 12)) [DecidableRel G.Adj]
    (d : ℕ) (hdpos : 1 ≤ d) :
    (initialAfterZero 12 d).filter (fun x ↦ G.Adj 1 x) =
      (intervalFrom 12 2 (d - 1)).filter (fun x ↦ G.Adj 1 x) := by
  ext x
  simp only [Finset.mem_filter, initialAfterZero, intervalFrom,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨hxpos, hxle⟩, hadj⟩
    have hxne : (1 : Fin 12) ≠ x := G.ne_of_adj hadj
    have hxvne : x.val ≠ 1 := by
      intro h
      exact hxne (Fin.ext h.symm)
    exact ⟨⟨by omega, by omega⟩, hadj⟩
  · rintro ⟨⟨hxlo, hxhi⟩, hadj⟩
    exact ⟨⟨by omega, by omega⟩, hadj⟩

end D12Normalization

noncomputable local instance graphAdjDecidableFin12
    (G : SimpleGraph (Fin 12)) : DecidableRel G.Adj :=
  Classical.decRel _

def RootRow (G : SimpleGraph (Fin 12)) (d : ℕ) : Prop :=
  ∀ x : Fin 12, G.Adj 0 x ↔
    x ∈ D12Normalization.initialAfterZero 12 d

def RowOneInside (G : SimpleGraph (Fin 12)) (d r : ℕ) : Prop :=
  ∀ x, x ∈ D12Normalization.intervalFrom 12 2 (d - 1) →
    (G.Adj 1 x ↔ x ∈ D12Normalization.intervalFrom 12 2 r)

def RowOneOutside (G : SimpleGraph (Fin 12)) (d s : ℕ) : Prop :=
  ∀ x, x ∈ D12Normalization.intervalFrom 12 (d + 1) (11 - d) →
    (G.Adj 1 x ↔ x ∈ D12Normalization.intervalFrom 12 (d + 1) s)

def RowTwoResidual (G : SimpleGraph (Fin 12)) (d r t : ℕ) : Prop :=
  ∀ x, x ∈ D12Normalization.intervalFrom 12 (r + 2) (d - (r + 1)) →
    (G.Adj 2 x ↔ x ∈ D12Normalization.intervalFrom 12 (r + 2) t)

/-- The parameter-level form of the historical root dispatcher.  For `d=7,
r=0` the dispatcher ignores `s`; retaining an arbitrary normalized `s` here
is a harmless strengthening of that single root.  The subsequent ten hard
roots and the `d=8,r=1,2` roots use `exists_sort_row_two_residual` to expose
the `t` parameter. -/
def HistoricalRootParameters (G : SimpleGraph (Fin 12)) : Prop :=
  (∃ r ≤ 3, ∃ s ≤ 5,
      RootRow G 6 ∧ RowOneInside G 6 r ∧ RowOneOutside G 6 s) ∨
  (∃ r ≤ 3, ∃ s ≤ 4,
      RootRow G 7 ∧ RowOneInside G 7 r ∧ RowOneOutside G 7 s) ∨
  (∃ r ≤ 4, RootRow G 8 ∧ RowOneInside G 8 r) ∨
  RootRow G 9 ∨ RootRow G 10 ∨ RootRow G 11

theorem IsCochromaticColoring.compl_normalization {V : Type*}
    {G : SimpleGraph V} {k : ℕ} {c : V → Fin k}
    (h : IsCochromaticColoring G c) :
    IsCochromaticColoring Gᶜ c := by
  intro i
  rcases h i with h | h
  · right
    intro u v hu hv huv hadj
    rw [SimpleGraph.compl_adj] at hadj
    exact hadj.2 (h u v hu hv huv)
  · left
    intro u v hu hv huv
    rw [SimpleGraph.compl_adj]
    exact ⟨huv, h u v hu hv huv⟩

private theorem compl_compl_eq_normalization {V : Type*} (G : SimpleGraph V) :
    Gᶜᶜ = G := by
  ext u v
  simp only [SimpleGraph.compl_adj]
  constructor
  · rintro ⟨huv, h⟩
    by_contra hn
    exact h ⟨huv, hn⟩
  · intro h
    exact ⟨G.ne_of_adj h, fun h' ↦ h'.2 h⟩

theorem cochromaticColorable_compl_normalization {V : Type*}
    (G : SimpleGraph V) (k : ℕ) :
    CochromaticColorable Gᶜ k ↔ CochromaticColorable G k := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    have hcc := hc.compl_normalization
    rwa [compl_compl_eq_normalization] at hcc
  · rintro ⟨c, hc⟩
    exact ⟨c, hc.compl_normalization⟩

theorem cochromaticColorable_comap_equiv_normalization {V W : Type*}
    (G : SimpleGraph W) (e : V ≃ W) (k : ℕ) :
    CochromaticColorable (G.comap e) k ↔ CochromaticColorable G k := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨fun w ↦ c (e.symm w), ?_⟩
    intro i
    rcases hc i with h | h
    · left
      intro u v hu hv huv
      have hadj :=
        h (e.symm u) (e.symm v) hu hv (e.symm.injective.ne huv)
      simpa only [SimpleGraph.comap_adj, Equiv.apply_symm_apply] using hadj
    · right
      intro u v hu hv huv
      have hnadj :=
        h (e.symm u) (e.symm v) hu hv (e.symm.injective.ne huv)
      simpa only [SimpleGraph.comap_adj, Equiv.apply_symm_apply] using hnadj
  · rintro ⟨c, hc⟩
    refine ⟨fun v ↦ c (e v), ?_⟩
    intro i
    rcases hc i with h | h
    · left
      intro u v hu hv huv
      simpa only [SimpleGraph.comap_adj] using
        h (e u) (e v) hu hv (e.injective.ne huv)
    · right
      intro u v hu hv huv
      simpa only [SimpleGraph.comap_adj] using
        h (e u) (e v) hu hv (e.injective.ne huv)

theorem IsHomogeneousFinset.compl_normalization {V : Type*}
    {G : SimpleGraph V} {S : Finset V} (h : IsHomogeneousFinset G S) :
    IsHomogeneousFinset Gᶜ S := by
  rcases h with h | h
  · right
    intro u hu v hv huv hadj
    rw [SimpleGraph.compl_adj] at hadj
    exact hadj.2 (h u hu v hv huv)
  · left
    intro u hu v hv huv
    rw [SimpleGraph.compl_adj]
    exact ⟨huv, h u hu v hv huv⟩

theorem isHomogeneousFinset_compl_iff_normalization {V : Type*}
    (G : SimpleGraph V) (S : Finset V) :
    IsHomogeneousFinset Gᶜ S ↔ IsHomogeneousFinset G S := by
  constructor
  · intro h
    have hcc := h.compl_normalization
    rwa [compl_compl_eq_normalization] at hcc
  · exact IsHomogeneousFinset.compl_normalization

theorem HasNoHomogeneousFour.compl_normalization {V : Type*}
    [DecidableEq V] {G : SimpleGraph V} (h : HasNoHomogeneousFour G) :
    HasNoHomogeneousFour Gᶜ := by
  intro S hcard hhom
  exact h S hcard ((isHomogeneousFinset_compl_iff_normalization G S).mp hhom)

theorem IsHomogeneousFinset.map_comap_normalization
    {V W : Type*} [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph W} (e : V ≃ W) {S : Finset V}
    (h : IsHomogeneousFinset (G.comap e) S) :
    IsHomogeneousFinset G (S.map e.toEmbedding) := by
  rcases h with h | h
  · left
    intro u hu v hv huv
    obtain ⟨u', hu'S, rfl⟩ := Finset.mem_map.mp hu
    obtain ⟨v', hv'S, rfl⟩ := Finset.mem_map.mp hv
    have hadj := h u' hu'S v' hv'S (e.injective.ne_iff.mp huv)
    change G.Adj (e u') (e v')
    simpa only [SimpleGraph.comap_adj] using hadj
  · right
    intro u hu v hv huv
    obtain ⟨u', hu'S, rfl⟩ := Finset.mem_map.mp hu
    obtain ⟨v', hv'S, rfl⟩ := Finset.mem_map.mp hv
    have hnadj := h u' hu'S v' hv'S (e.injective.ne_iff.mp huv)
    change ¬G.Adj (e u') (e v')
    simpa only [SimpleGraph.comap_adj] using hnadj

theorem HasNoHomogeneousFour.comap_equiv_normalization
    {V W : Type*} [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph W} (e : V ≃ W)
    (h : HasNoHomogeneousFour G) :
    HasNoHomogeneousFour (G.comap e) := by
  intro S hcard hhom
  apply h (S.map e.toEmbedding)
  · simpa using hcard
  · exact hhom.map_comap_normalization e

theorem exists_pivot_internal_normalization
    (H : SimpleGraph (Fin 12)) [DecidableRel H.Adj]
    (d k : ℕ) (hdpos : 1 ≤ d) (hdle : d ≤ 11)
    (hdk : d ≤ 2 * k + 1) (hroot : RootRow H d)
    (hno : HasNoHomogeneousFour H) :
    ∃ H' : SimpleGraph (Fin 12), ∃ r : ℕ,
      r ≤ k ∧ RootRow H' d ∧ RowOneInside H' d r ∧
      HasNoHomogeneousFour H' ∧
      ∀ q, CochromaticColorable H' q ↔ CochromaticColorable H q := by
  classical
  let A := D12Normalization.initialAfterZero 12 d
  have hdlt : d < 12 := by omega
  have hAcard : A.card = d :=
    D12Normalization.card_initialAfterZero hdlt
  have hAne : A.Nonempty := by
    rw [← Finset.card_pos, hAcard]
    omega
  have h0A : (0 : Fin 12) ∉ A := by
    simp [A, D12Normalization.initialAfterZero]
  have htri : D12Normalization.TriangleFreeOnFinset H A := by
    apply D12Normalization.triangleFreeOnFinset_of_no_homogeneous_four_at H
      (p := 0) (S := A)
    · simpa only [HasNoHomogeneousFour, IsHomogeneousFinset] using hno
    · exact h0A
    · intro x hx
      exact (hroot x).2 hx
  obtain ⟨a, ha, hadeg⟩ :=
    D12Normalization.exists_degreeWithin_le_of_triangleFree
      H A hAne k (by simpa [hAcard] using hdk) htri
  have h1A : (1 : Fin 12) ∈ A := by
    simp only [A, D12Normalization.initialAfterZero,
      Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  obtain ⟨σ, hσA, hσfix, hσsingleton⟩ :=
    D12Normalization.exists_perm_sort_within A
      ({1} : Finset (Fin 12)) ({a} : Finset (Fin 12))
      (by simpa using h1A) (by simpa using ha) (by simp)
  have hσone : σ 1 = a := by
    have hm := (hσsingleton 1 h1A).2 (by simp)
    simpa using hm
  have hσzero : σ 0 = 0 := hσfix 0 h0A
  let H1 := H.comap σ
  let : DecidableRel H1.Adj := by
    dsimp only [H1]
    exact SimpleGraph.instDecidableComapAdj σ H
  have hroot1 : RootRow H1 d := by
    intro x
    change H.Adj (σ 0) (σ x) ↔ x ∈ A
    rw [hσzero]
    exact (hroot (σ x)).trans (hσA x)
  have hno1 : HasNoHomogeneousFour H1 :=
    hno.comap_equiv_normalization σ
  let S := D12Normalization.intervalFrom 12 2 (d - 1)
  let r := D12Normalization.degreeWithin H1 S 1
  have hrA : r = D12Normalization.degreeWithin H1 A 1 := by
    unfold r D12Normalization.degreeWithin
    exact congrArg Finset.card
      (D12Normalization.filter_adj_initial_eq_inside H1 d hdpos).symm
  have hr : r ≤ k := by
    rw [hrA]
    have heq : D12Normalization.degreeWithin H1 A 1 =
        D12Normalization.degreeWithin H A (σ 1) := by
      simpa only [H1] using
        D12Normalization.degreeWithin_comap_perm H A σ hσA 1
    rw [heq, hσone]
    exact hadeg
  have hrange : r ≤ d - 1 := by
    unfold r D12Normalization.degreeWithin
    calc
      (S.filter fun x ↦ H1.Adj 1 x).card ≤ S.card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      _ = d - 1 := by
        apply D12Normalization.card_intervalFrom
        omega
  have hSA : S ⊆ A := by
    intro x hx
    simp only [S, A, D12Normalization.intervalFrom,
      D12Normalization.initialAfterZero, Finset.mem_filter,
      Finset.mem_univ, true_and] at hx ⊢
    omega
  have hcount : (S.filter fun x ↦ H1.Adj 1 x).card = r := rfl
  obtain ⟨τ, hτzero, hτone, hτS, hτfix, hinside, hrootS⟩ :=
    D12Normalization.exists_sort_row_one_inside H1 d r hdpos hdle hrange
      hcount (fun x hx ↦ (hroot1 x).2 (hSA hx))
  let H2 := H1.comap τ
  have hroot2 : RootRow H2 d := by
    intro x
    by_cases hx : x ∈ S
    · exact iff_of_true (hrootS x hx) (hSA hx)
    · change H1.Adj (τ 0) (τ x) ↔ x ∈ A
      rw [hτzero, hτfix x hx]
      exact hroot1 x
  refine ⟨H2, r, hr, hroot2, hinside, ?_, ?_⟩
  · exact hno1.comap_equiv_normalization τ
  · intro q
    exact (cochromaticColorable_comap_equiv_normalization H1 τ q).trans
      (cochromaticColorable_comap_equiv_normalization H σ q)

theorem exists_row_one_outside_normalization
    (H : SimpleGraph (Fin 12)) [DecidableRel H.Adj]
    (d r : ℕ) (hdpos : 1 ≤ d) (hdle : d ≤ 11)
    (hroot : RootRow H d) (hinside : RowOneInside H d r)
    (hno : HasNoHomogeneousFour H) :
    ∃ H' : SimpleGraph (Fin 12), ∃ s : ℕ,
      s ≤ 11 - d ∧ RootRow H' d ∧ RowOneInside H' d r ∧
      RowOneOutside H' d s ∧ HasNoHomogeneousFour H' ∧
      ∀ q, CochromaticColorable H' q ↔ CochromaticColorable H q := by
  classical
  let C := D12Normalization.intervalFrom 12 (d + 1) (11 - d)
  let I := D12Normalization.intervalFrom 12 2 (d - 1)
  let s := D12Normalization.degreeWithin H C 1
  have hCcard : C.card = 11 - d := by
    apply D12Normalization.card_intervalFrom
    omega
  have hs : s ≤ 11 - d := by
    change (C.filter fun x ↦ H.Adj 1 x).card ≤ 11 - d
    rw [← hCcard]
    exact Finset.card_le_card (Finset.filter_subset _ _)
  have hcount : (C.filter fun x ↦ H.Adj 1 x).card = s := rfl
  have hrootC : ∀ x, x ∈ C → ¬H.Adj 0 x := by
    intro x hx hadj
    have hxA := (hroot x).1 hadj
    simp only [C, D12Normalization.intervalFrom,
      D12Normalization.initialAfterZero, Finset.mem_filter,
      Finset.mem_univ, true_and] at hx hxA
    omega
  obtain ⟨τ, hτzero, hτone, hτC, hτfix, houtside, hrootC'⟩ :=
    D12Normalization.exists_sort_row_one_outside H d s hdpos hdle hs
      hcount hrootC
  let H' := H.comap τ
  have hroot' : RootRow H' d := by
    intro x
    by_cases hx : x ∈ C
    · have hxA : x ∉ D12Normalization.initialAfterZero 12 d := by
        intro hxA
        simp only [C, D12Normalization.intervalFrom,
          D12Normalization.initialAfterZero, Finset.mem_filter,
          Finset.mem_univ, true_and] at hx hxA
        omega
      exact iff_of_false (hrootC' x hx) hxA
    · change H.Adj (τ 0) (τ x) ↔
        x ∈ D12Normalization.initialAfterZero 12 d
      rw [hτzero, hτfix x hx]
      exact hroot x
  have hinside' : RowOneInside H' d r := by
    intro x hxI
    have hxC : x ∉ C := by
      intro hxC
      simp only [I, C, D12Normalization.intervalFrom,
        Finset.mem_filter, Finset.mem_univ, true_and] at hxI hxC
      omega
    change H.Adj (τ 1) (τ x) ↔
      x ∈ D12Normalization.intervalFrom 12 2 r
    rw [hτone, hτfix x hxC]
    exact hinside x hxI
  exact ⟨H', s, hs, hroot', hinside', houtside,
    hno.comap_equiv_normalization τ,
    fun q ↦ cochromaticColorable_comap_equiv_normalization H τ q⟩

theorem exists_row_two_residual_normalization
    (H : SimpleGraph (Fin 12)) [DecidableRel H.Adj]
    (d r : ℕ) (hd : d ≤ 11) (hrpos : 1 ≤ r) (hrd : r + 1 ≤ d)
    (hroot : RootRow H d) (hinside : RowOneInside H d r)
    (hno : HasNoHomogeneousFour H) :
    ∃ H' : SimpleGraph (Fin 12), ∃ t : ℕ,
      t ≤ d - (r + 1) ∧ RootRow H' d ∧ RowOneInside H' d r ∧
      RowTwoResidual H' d r t ∧ HasNoHomogeneousFour H' ∧
      (∀ s, RowOneOutside H d s → RowOneOutside H' d s) ∧
      ∀ q, CochromaticColorable H' q ↔ CochromaticColorable H q := by
  classical
  let B := D12Normalization.intervalFrom 12 (r + 2) (d - (r + 1))
  let t := D12Normalization.degreeWithin H B 2
  have hBcard : B.card = d - (r + 1) := by
    apply D12Normalization.card_intervalFrom
    omega
  have ht : t ≤ d - (r + 1) := by
    change (B.filter fun x ↦ H.Adj 2 x).card ≤ d - (r + 1)
    rw [← hBcard]
    exact Finset.card_le_card (Finset.filter_subset _ _)
  have hcount : (B.filter fun x ↦ H.Adj 2 x).card = t := rfl
  have hrootB : ∀ x, x ∈ B → H.Adj 0 x := by
    intro x hx
    apply (hroot x).2
    simp only [B, D12Normalization.intervalFrom,
      D12Normalization.initialAfterZero, Finset.mem_filter,
      Finset.mem_univ, true_and] at hx ⊢
    omega
  have hinsideB : ∀ x, x ∈ B → ¬H.Adj 1 x := by
    intro x hx hadj
    have hxI : x ∈ D12Normalization.intervalFrom 12 2 (d - 1) := by
      simp only [B, D12Normalization.intervalFrom,
        Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      omega
    have hxT := (hinside x hxI).1 hadj
    simp only [B, D12Normalization.intervalFrom,
      Finset.mem_filter, Finset.mem_univ, true_and] at hx hxT
    omega
  obtain ⟨τ, hτzero, hτone, hτtwo, hτB, hτfix, hrow2, hrootB', hrow1B'⟩ :=
    D12Normalization.exists_sort_row_two_residual H d r t hd hrpos hrd ht
      hcount hrootB hinsideB
  let H' := H.comap τ
  have hroot' : RootRow H' d := by
    intro x
    by_cases hx : x ∈ B
    · have hxA : x ∈ D12Normalization.initialAfterZero 12 d := by
        simp only [B, D12Normalization.intervalFrom,
          D12Normalization.initialAfterZero, Finset.mem_filter,
          Finset.mem_univ, true_and] at hx ⊢
        omega
      exact iff_of_true (hrootB' x hx) hxA
    · change H.Adj (τ 0) (τ x) ↔
        x ∈ D12Normalization.initialAfterZero 12 d
      rw [hτzero, hτfix x hx]
      exact hroot x
  have hinside' : RowOneInside H' d r := by
    intro x hxI
    by_cases hx : x ∈ B
    · have hxT : x ∉ D12Normalization.intervalFrom 12 2 r := by
        intro hxT
        simp only [B, D12Normalization.intervalFrom,
          Finset.mem_filter, Finset.mem_univ, true_and] at hx hxT
        omega
      exact iff_of_false (hrow1B' x hx) hxT
    · change H.Adj (τ 1) (τ x) ↔
        x ∈ D12Normalization.intervalFrom 12 2 r
      rw [hτone, hτfix x hx]
      exact hinside x hxI
  have houtside : ∀ s, RowOneOutside H d s → RowOneOutside H' d s := by
    intro s hs x hxC
    have hxB : x ∉ B := by
      intro hxB
      simp only [B, D12Normalization.intervalFrom,
        Finset.mem_filter, Finset.mem_univ, true_and] at hxB hxC
      omega
    change H.Adj (τ 1) (τ x) ↔
      x ∈ D12Normalization.intervalFrom 12 (d + 1) s
    rw [hτone, hτfix x hxB]
    exact hs x hxC
  exact ⟨H', t, ht, hroot', hinside', hrow2,
    hno.comap_equiv_normalization τ, houtside,
    fun q ↦ cochromaticColorable_comap_equiv_normalization H τ q⟩

theorem orient_comap_transport
    (G : SimpleGraph (Fin 12)) (σ : Equiv.Perm (Fin 12)) (q : ℕ) :
    CochromaticColorable
        ((D12Normalization.orientAtZero G).comap σ) q ↔
      CochromaticColorable G q := by
  rw [cochromaticColorable_comap_equiv_normalization]
  unfold D12Normalization.orientAtZero
  split <;> simp only [cochromaticColorable_compl_normalization]

theorem exists_historical_root_parameters
    (G : SimpleGraph (Fin 12)) (hno : HasNoHomogeneousFour G) :
    ∃ H : SimpleGraph (Fin 12),
      HistoricalRootParameters H ∧ HasNoHomogeneousFour H ∧
      ∀ q, CochromaticColorable H q ↔ CochromaticColorable G q := by
  classical
  let O := D12Normalization.orientAtZero G
  let : DecidableRel O.Adj := Classical.decRel _
  have hnoO : HasNoHomogeneousFour O := by
    dsimp only [O, D12Normalization.orientAtZero]
    split
    · exact hno
    · exact hno.compl_normalization
  obtain ⟨σ, _, hrow⟩ :=
    D12Normalization.exists_root_neighbor_normalization O
  let H0 := O.comap σ
  let : DecidableRel H0.Adj := by
    dsimp only [H0]
    exact SimpleGraph.instDecidableComapAdj σ O
  let d := D12Normalization.degree12 O 0
  have hdlo : 6 ≤ d := by
    dsimp only [d]
    exact D12Normalization.orientAtZero_degree G
  have hdhi : d ≤ 11 := by
    dsimp only [d]
    exact D12Normalization.orientAtZero_degree_le G
  have hrow0 : RootRow H0 (D12Normalization.degree12 O 0) := by
    intro x
    exact hrow x
  have hno0 : HasNoHomogeneousFour H0 := hnoO.comap_equiv_normalization σ
  have hcases : d = 6 ∨ d = 7 ∨ d = 8 ∨ d = 9 ∨ d = 10 ∨ d = 11 := by
    omega
  rcases hcases with hd | hd | hd | hd | hd | hd
  · have hd' : D12Normalization.degree12 O 0 = 6 := by
      simpa only [d] using hd
    have hroot0 : RootRow H0 6 := hd' ▸ hrow0
    obtain ⟨H1, r, hr, hroot1, hin1, hno1, htrans1⟩ :=
      exists_pivot_internal_normalization H0 6 3 (by omega) (by omega)
        (by omega) hroot0 hno0
    let : DecidableRel H1.Adj := Classical.decRel _
    obtain ⟨H2, s, hs, hroot2, hin2, hout2, hno2, htrans2⟩ :=
      exists_row_one_outside_normalization H1 6 r (by omega) (by omega)
        hroot1 hin1 hno1
    refine ⟨H2, ?_, hno2, ?_⟩
    · exact Or.inl ⟨r, hr, s, hs, hroot2, hin2, hout2⟩
    · intro q
      exact (htrans2 q).trans ((htrans1 q).trans (orient_comap_transport G σ q))
  · have hd' : D12Normalization.degree12 O 0 = 7 := by
      simpa only [d] using hd
    have hroot0 : RootRow H0 7 := hd' ▸ hrow0
    obtain ⟨H1, r, hr, hroot1, hin1, hno1, htrans1⟩ :=
      exists_pivot_internal_normalization H0 7 3 (by omega) (by omega)
        (by omega) hroot0 hno0
    let : DecidableRel H1.Adj := Classical.decRel _
    obtain ⟨H2, s, hs, hroot2, hin2, hout2, hno2, htrans2⟩ :=
      exists_row_one_outside_normalization H1 7 r (by omega) (by omega)
        hroot1 hin1 hno1
    refine ⟨H2, ?_, hno2, ?_⟩
    · exact Or.inr (Or.inl ⟨r, hr, s, hs, hroot2, hin2, hout2⟩)
    · intro q
      exact (htrans2 q).trans ((htrans1 q).trans (orient_comap_transport G σ q))
  · have hd' : D12Normalization.degree12 O 0 = 8 := by
      simpa only [d] using hd
    have hroot0 : RootRow H0 8 := hd' ▸ hrow0
    obtain ⟨H1, r, hr, hroot1, hin1, hno1, htrans1⟩ :=
      exists_pivot_internal_normalization H0 8 4 (by omega) (by omega)
        (by omega) hroot0 hno0
    refine ⟨H1, ?_, hno1, ?_⟩
    · exact Or.inr (Or.inr (Or.inl ⟨r, hr, hroot1, hin1⟩))
    · intro q
      exact (htrans1 q).trans (orient_comap_transport G σ q)
  · have hd' : D12Normalization.degree12 O 0 = 9 := by
      simpa only [d] using hd
    have hroot0 : RootRow H0 9 := hd' ▸ hrow0
    refine ⟨H0, ?_, hno0, ?_⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inl hroot0)))
    · exact orient_comap_transport G σ
  · have hd' : D12Normalization.degree12 O 0 = 10 := by
      simpa only [d] using hd
    have hroot0 : RootRow H0 10 := hd' ▸ hrow0
    refine ⟨H0, ?_, hno0, ?_⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hroot0))))
    · exact orient_comap_transport G σ
  · have hd' : D12Normalization.degree12 O 0 = 11 := by
      simpa only [d] using hd
    have hroot0 : RootRow H0 11 := hd' ▸ hrow0
    refine ⟨H0, ?_, hno0, ?_⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hroot0))))
    · exact orient_comap_transport G σ

theorem cochromaticColorable_orient_comap_normalization
    (G : SimpleGraph (Fin 12)) (σ : Equiv.Perm (Fin 12)) (k : ℕ) :
    CochromaticColorable
        ((D12Normalization.orientAtZero G).comap σ) k ↔
      CochromaticColorable G k := by
  rw [cochromaticColorable_comap_equiv_normalization]
  unfold D12Normalization.orientAtZero
  split <;> simp only [cochromaticColorable_compl_normalization]

theorem exists_oriented_root_normalization (G : SimpleGraph (Fin 12)) :
    ∃ σ : Equiv.Perm (Fin 12),
      6 ≤ D12Normalization.degree12
          (D12Normalization.orientAtZero G) 0 ∧
      D12Normalization.degree12
          (D12Normalization.orientAtZero G) 0 ≤ 11 ∧
      (∀ x : Fin 12,
        (((D12Normalization.orientAtZero G).comap σ).Adj 0 x ↔
          x ∈ D12Normalization.initialAfterZero 12
            (D12Normalization.degree12
              (D12Normalization.orientAtZero G) 0))) ∧
      ∀ k, CochromaticColorable
          ((D12Normalization.orientAtZero G).comap σ) k ↔
        CochromaticColorable G k := by
  classical
  let H := D12Normalization.orientAtZero G
  let : DecidableRel H.Adj := Classical.decRel _
  obtain ⟨σ, _, hrow⟩ := D12Normalization.exists_root_neighbor_normalization H
  refine ⟨σ, D12Normalization.orientAtZero_degree G,
    D12Normalization.orientAtZero_degree_le G, hrow, ?_⟩
  intro k
  exact cochromaticColorable_orient_comap_normalization G σ k

open Erdos758.D12Certificate

/-! The graph-side consumer for the D12 certificate outcomes. -/

private def unorderedPairs {α : Type*} : List α → List (α × α)
  | [] => []
  | x :: xs => xs.map (fun y ↦ (x, y)) ++ unorderedPairs xs

private def conjunction : List Prop → Prop
  | [] => True
  | [p] => p
  | p :: q :: ps => p ∧ conjunction (q :: ps)

private def PairConjunction {α : Type*} (r : α → α → Prop)
    (xs : List α) : Prop :=
  conjunction ((unorderedPairs xs).map fun p ↦ r p.1 p.2)

private theorem conjunction_of_mem {ps : List Prop} (h : conjunction ps)
    {p : Prop} (hp : p ∈ ps) : p := by
  induction ps with
  | nil => simp at hp
  | cons q qs ih =>
      cases qs with
      | nil =>
          simp only [List.mem_singleton] at hp
          subst p
          exact h
      | cons r rs =>
          simp only [conjunction] at h
          rcases h with ⟨hq, hrest⟩
          simp only [List.mem_cons] at hp
          rcases hp with rfl | hp
          · exact hq
          · exact ih hrest (by simpa only [List.mem_cons] using hp)

private theorem pair_mem_unorderedPairs_of_mem_ne {α : Type*} [DecidableEq α]
    {u v : α} {xs : List α} (hu : u ∈ xs) (hv : v ∈ xs) (hne : u ≠ v) :
    (u, v) ∈ unorderedPairs xs ∨ (v, u) ∈ unorderedPairs xs := by
  induction xs with
  | nil => simp at hu
  | cons x xs ih =>
      simp only [List.mem_cons] at hu hv
      rcases hu with rfl | hu <;> rcases hv with rfl | hv
      · exact (hne rfl).elim
      · left
        simp [unorderedPairs, hv]
      · right
        simp [unorderedPairs, hu]
      · rcases ih hu hv with hp | hp
        · left
          simp [unorderedPairs, hp]
        · right
          simp [unorderedPairs, hp]

private theorem homogeneous_of_pairConjunction_pos {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (xs : List V) (h : PairConjunction G.Adj xs) :
    IsHomogeneousFinset G xs.toFinset := by
  left
  intro u hu v hv hne
  have hu' : u ∈ xs := by simpa using hu
  have hv' : v ∈ xs := by simpa using hv
  rcases pair_mem_unorderedPairs_of_mem_ne hu' hv' hne with hp | hp
  · exact conjunction_of_mem h (List.mem_map.mpr ⟨(u, v), hp, rfl⟩)
  · exact (conjunction_of_mem h
      (List.mem_map.mpr ⟨(v, u), hp, rfl⟩)).symm

private theorem homogeneous_of_pairConjunction_neg {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (xs : List V)
    (h : PairConjunction (fun u v ↦ ¬ G.Adj u v) xs) :
    IsHomogeneousFinset G xs.toFinset := by
  right
  intro u hu v hv hne
  have hu' : u ∈ xs := by simpa using hu
  have hv' : v ∈ xs := by simpa using hv
  rcases pair_mem_unorderedPairs_of_mem_ne hu' hv' hne with hp | hp
  · exact conjunction_of_mem h (List.mem_map.mpr ⟨(u, v), hp, rfl⟩)
  · intro huv
    exact conjunction_of_mem h
      (List.mem_map.mpr ⟨(v, u), hp, rfl⟩) huv.symm

/-! ## The lexicographic graph edge assignment -/

private def edgePairs12 : List (Fin 12 × Fin 12) :=
  [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6),
   (0, 7), (0, 8), (0, 9), (0, 10), (0, 11),
   (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7),
   (1, 8), (1, 9), (1, 10), (1, 11),
   (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8),
   (2, 9), (2, 10), (2, 11),
   (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9),
   (3, 10), (3, 11),
   (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11),
   (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11),
   (6, 7), (6, 8), (6, 9), (6, 10), (6, 11),
   (7, 8), (7, 9), (7, 10), (7, 11),
   (8, 9), (8, 10), (8, 11),
   (9, 10), (9, 11),
   (10, 11)]

/-- Interpret the first 66 propositional variables as the lexicographically
ordered edges of a graph on `Fin 12`. -/
def graphEdge (G : SimpleGraph (Fin 12)) (n : Nat) : Prop :=
  match n with
  | 0 => G.Adj 0 1
  | 1 => G.Adj 0 2
  | 2 => G.Adj 0 3
  | 3 => G.Adj 0 4
  | 4 => G.Adj 0 5
  | 5 => G.Adj 0 6
  | 6 => G.Adj 0 7
  | 7 => G.Adj 0 8
  | 8 => G.Adj 0 9
  | 9 => G.Adj 0 10
  | 10 => G.Adj 0 11
  | 11 => G.Adj 1 2
  | 12 => G.Adj 1 3
  | 13 => G.Adj 1 4
  | 14 => G.Adj 1 5
  | 15 => G.Adj 1 6
  | 16 => G.Adj 1 7
  | 17 => G.Adj 1 8
  | 18 => G.Adj 1 9
  | 19 => G.Adj 1 10
  | 20 => G.Adj 1 11
  | 21 => G.Adj 2 3
  | 22 => G.Adj 2 4
  | 23 => G.Adj 2 5
  | 24 => G.Adj 2 6
  | 25 => G.Adj 2 7
  | 26 => G.Adj 2 8
  | 27 => G.Adj 2 9
  | 28 => G.Adj 2 10
  | 29 => G.Adj 2 11
  | 30 => G.Adj 3 4
  | 31 => G.Adj 3 5
  | 32 => G.Adj 3 6
  | 33 => G.Adj 3 7
  | 34 => G.Adj 3 8
  | 35 => G.Adj 3 9
  | 36 => G.Adj 3 10
  | 37 => G.Adj 3 11
  | 38 => G.Adj 4 5
  | 39 => G.Adj 4 6
  | 40 => G.Adj 4 7
  | 41 => G.Adj 4 8
  | 42 => G.Adj 4 9
  | 43 => G.Adj 4 10
  | 44 => G.Adj 4 11
  | 45 => G.Adj 5 6
  | 46 => G.Adj 5 7
  | 47 => G.Adj 5 8
  | 48 => G.Adj 5 9
  | 49 => G.Adj 5 10
  | 50 => G.Adj 5 11
  | 51 => G.Adj 6 7
  | 52 => G.Adj 6 8
  | 53 => G.Adj 6 9
  | 54 => G.Adj 6 10
  | 55 => G.Adj 6 11
  | 56 => G.Adj 7 8
  | 57 => G.Adj 7 9
  | 58 => G.Adj 7 10
  | 59 => G.Adj 7 11
  | 60 => G.Adj 8 9
  | 61 => G.Adj 8 10
  | 62 => G.Adj 8 11
  | 63 => G.Adj 9 10
  | 64 => G.Adj 9 11
  | 65 => G.Adj 10 11
  | _ => False

/-- The closed-form rank used by the certificate agrees with `graphEdge`. -/
private theorem graphEdge_edgeIndex12_row0 (G : SimpleGraph (Fin 12)) (j : Fin 12)
    (hij : (0 : Fin 12) ≠ j) :
    graphEdge G (edgeIndex12 0 j.val) ↔ G.Adj 0 j := by
  fin_cases j <;> simp_all [graphEdge, edgeIndex12]

private theorem graphEdge_edgeIndex12_row1 (G : SimpleGraph (Fin 12)) (j : Fin 12)
    (hij : (1 : Fin 12) ≠ j) :
    graphEdge G (edgeIndex12 1 j.val) ↔ G.Adj 1 j := by
  fin_cases j <;> simp_all [graphEdge, edgeIndex12]
  all_goals exact G.adj_comm _ _

private theorem graphEdge_edgeIndex12_row2 (G : SimpleGraph (Fin 12)) (j : Fin 12)
    (hij : (2 : Fin 12) ≠ j) :
    graphEdge G (edgeIndex12 2 j.val) ↔ G.Adj 2 j := by
  fin_cases j <;> simp_all [graphEdge, edgeIndex12]
  all_goals exact G.adj_comm _ _

private theorem graphEdge_edgeIndex12_row3 (G : SimpleGraph (Fin 12)) (j : Fin 12)
    (hij : (3 : Fin 12) ≠ j) :
    graphEdge G (edgeIndex12 3 j.val) ↔ G.Adj 3 j := by
  fin_cases j <;> simp_all [graphEdge, edgeIndex12]
  all_goals exact G.adj_comm _ _

private theorem graphEdge_edgeIndex12_row4 (G : SimpleGraph (Fin 12)) (j : Fin 12)
    (hij : (4 : Fin 12) ≠ j) :
    graphEdge G (edgeIndex12 4 j.val) ↔ G.Adj 4 j := by
  fin_cases j <;> simp_all only [Fin.isValue, Fin.mk_one, Fin.reduceFinMk, Fin.zero_eta]
  all_goals exact G.adj_comm _ _

private theorem graphEdge_edgeIndex12_row5 (G : SimpleGraph (Fin 12)) (j : Fin 12)
    (hij : (5 : Fin 12) ≠ j) :
    graphEdge G (edgeIndex12 5 j.val) ↔ G.Adj 5 j := by
  fin_cases j <;> simp_all only [Fin.isValue, Fin.mk_one, Fin.reduceFinMk, Fin.zero_eta]
  all_goals exact G.adj_comm _ _

private theorem graphEdge_edgeIndex12_row6 (G : SimpleGraph (Fin 12)) (j : Fin 12)
    (hij : (6 : Fin 12) ≠ j) :
    graphEdge G (edgeIndex12 6 j.val) ↔ G.Adj 6 j := by
  fin_cases j <;> simp_all only [Fin.isValue, Fin.mk_one, Fin.reduceFinMk, Fin.zero_eta]
  all_goals exact G.adj_comm _ _

private theorem graphEdge_edgeIndex12_row7 (G : SimpleGraph (Fin 12)) (j : Fin 12)
    (hij : (7 : Fin 12) ≠ j) :
    graphEdge G (edgeIndex12 7 j.val) ↔ G.Adj 7 j := by
  fin_cases j <;> simp_all only [Fin.isValue, Fin.mk_one, Fin.reduceFinMk, Fin.zero_eta]
  all_goals exact G.adj_comm _ _

private theorem graphEdge_edgeIndex12_row8 (G : SimpleGraph (Fin 12)) (j : Fin 12)
    (hij : (8 : Fin 12) ≠ j) :
    graphEdge G (edgeIndex12 8 j.val) ↔ G.Adj 8 j := by
  fin_cases j <;> simp_all only [Fin.isValue, Fin.mk_one, Fin.reduceFinMk, Fin.zero_eta]
  all_goals exact G.adj_comm _ _

private theorem graphEdge_edgeIndex12_row9 (G : SimpleGraph (Fin 12)) (j : Fin 12)
    (hij : (9 : Fin 12) ≠ j) :
    graphEdge G (edgeIndex12 9 j.val) ↔ G.Adj 9 j := by
  fin_cases j <;> simp_all only [Fin.isValue, Fin.mk_one, Fin.reduceFinMk, Fin.zero_eta]
  all_goals exact G.adj_comm _ _

private theorem graphEdge_edgeIndex12_row10 (G : SimpleGraph (Fin 12)) (j : Fin 12)
    (hij : (10 : Fin 12) ≠ j) :
    graphEdge G (edgeIndex12 10 j.val) ↔ G.Adj 10 j := by
  fin_cases j <;> simp_all only [Fin.isValue, Fin.mk_one, Fin.reduceFinMk, Fin.zero_eta]
  all_goals exact G.adj_comm _ _

private theorem graphEdge_edgeIndex12_row11 (G : SimpleGraph (Fin 12)) (j : Fin 12)
    (hij : (11 : Fin 12) ≠ j) :
    graphEdge G (edgeIndex12 11 j.val) ↔ G.Adj 11 j := by
  fin_cases j <;> simp_all only [Fin.isValue, Fin.mk_one, Fin.reduceFinMk, Fin.zero_eta]
  all_goals exact G.adj_comm _ _

theorem graphEdge_edgeIndex12 (G : SimpleGraph (Fin 12)) (i j : Fin 12)
    (hij : i ≠ j) :
    graphEdge G (edgeIndex12 i.val j.val) ↔ G.Adj i j := by
  fin_cases i
  · exact graphEdge_edgeIndex12_row0 G j hij
  · exact graphEdge_edgeIndex12_row1 G j hij
  · exact graphEdge_edgeIndex12_row2 G j hij
  · exact graphEdge_edgeIndex12_row3 G j hij
  · exact graphEdge_edgeIndex12_row4 G j hij
  · exact graphEdge_edgeIndex12_row5 G j hij
  · exact graphEdge_edgeIndex12_row6 G j hij
  · exact graphEdge_edgeIndex12_row7 G j hij
  · exact graphEdge_edgeIndex12_row8 G j hij
  · exact graphEdge_edgeIndex12_row9 G j hij
  · exact graphEdge_edgeIndex12_row10 G j hij
  · exact graphEdge_edgeIndex12_row11 G j hij

private def fin12OfNat (n : Nat) : Fin 12 := ⟨n % 12, Nat.mod_lt _ (by decide)⟩

@[simp] private theorem fin12OfNat_val_of_lt {n : Nat} (h : n < 12) :
    (fin12OfNat n).val = n := by
  simp [fin12OfNat, Nat.mod_eq_of_lt h]

private theorem graphEdge_edgeIndex_nat (G : SimpleGraph (Fin 12))
    {i j : Nat} (hi : i < 12) (hj : j < 12) (hij : i ≠ j) :
    graphEdge G (edgeIndex12 i j) ↔
      G.Adj (fin12OfNat i) (fin12OfNat j) := by
  have hfin : fin12OfNat i ≠ fin12OfNat j := by
    intro h
    have := congrArg Fin.val h
    apply hij
    simpa [fin12OfNat_val_of_lt hi, fin12OfNat_val_of_lt hj] using this
  simpa [fin12OfNat_val_of_lt hi, fin12OfNat_val_of_lt hj] using
    graphEdge_edgeIndex12 G (fin12OfNat i) (fin12OfNat j) hfin

private theorem semantic_homogeneous_three (edge : Nat → Prop) (a b c : Nat) :
    Homogeneous edge [a, b, c] ↔
      (edge (edgeIndex12 a b) ∧ edge (edgeIndex12 a c) ∧
        edge (edgeIndex12 b c)) ∨
      (¬ edge (edgeIndex12 a b) ∧ ¬ edge (edgeIndex12 a c) ∧
        ¬ edge (edgeIndex12 b c)) := by
  rfl

private theorem semantic_homogeneous_four (edge : Nat → Prop) (a b c d : Nat) :
    Homogeneous edge [a, b, c, d] ↔
      (edge (edgeIndex12 a b) ∧ edge (edgeIndex12 a c) ∧
        edge (edgeIndex12 a d) ∧ edge (edgeIndex12 b c) ∧
        edge (edgeIndex12 b d) ∧ edge (edgeIndex12 c d)) ∨
      (¬ edge (edgeIndex12 a b) ∧ ¬ edge (edgeIndex12 a c) ∧
        ¬ edge (edgeIndex12 a d) ∧ ¬ edge (edgeIndex12 b c) ∧
        ¬ edge (edgeIndex12 b d) ∧ ¬ edge (edgeIndex12 c d)) := by
  rfl

private def finList12 (s : List Nat) : List (Fin 12) := s.map fin12OfNat

private theorem self_mem_finList12 {s : List Nat} (v : Fin 12)
    (h : v.val ∈ s) : v ∈ (finList12 s).toFinset := by
  simp only [List.mem_toFinset, finList12, List.mem_map]
  refine ⟨v.val, h, ?_⟩
  apply Fin.ext
  simp [fin12OfNat, Nat.mod_eq_of_lt v.isLt]

private theorem finList12_nodup {s : List Nat} (hn : s.Nodup)
    (hb : ∀ x ∈ s, x < 12) : (finList12 s).Nodup := by
  unfold finList12
  apply hn.map_on
  intro x hx y hy hxy
  have hval := congrArg Fin.val hxy
  simpa [fin12OfNat_val_of_lt (hb x hx), fin12OfNat_val_of_lt (hb y hy)] using hval

private theorem homogeneousTriple_to_finset (G : SimpleGraph (Fin 12))
    (s : List Nat) (hlen : s.length = 3) (hn : s.Nodup)
    (hb : ∀ x ∈ s, x < 12) (hh : Homogeneous (graphEdge G) s) :
    IsHomogeneousFinset G (finList12 s).toFinset := by
  obtain ⟨a, b, c, rfl⟩ := List.length_eq_three.mp hlen
  have ha12 : a < 12 := hb a (by simp)
  have hb12 : b < 12 := hb b (by simp)
  have hc12 : c < 12 := hb c (by simp)
  have hab' : a ≠ b := by
    intro e
    subst b
    simpa using hn
  have hac' : a ≠ c := by
    intro e
    subst c
    simpa using hn
  have hbc' : b ≠ c := by
    intro e
    subst c
    simpa using hn
  rw [semantic_homogeneous_three] at hh
  rcases hh with ⟨hab, hac, hbc⟩ | ⟨hab, hac, hbc⟩
  · apply homogeneous_of_pairConjunction_pos
    change G.Adj (fin12OfNat a) (fin12OfNat b) ∧
      G.Adj (fin12OfNat a) (fin12OfNat c) ∧
      G.Adj (fin12OfNat b) (fin12OfNat c)
    exact ⟨(graphEdge_edgeIndex_nat G ha12 hb12 hab').mp hab,
      (graphEdge_edgeIndex_nat G ha12 hc12 hac').mp hac,
      (graphEdge_edgeIndex_nat G hb12 hc12 hbc').mp hbc⟩
  · apply homogeneous_of_pairConjunction_neg
    change (¬ G.Adj (fin12OfNat a) (fin12OfNat b)) ∧
      (¬ G.Adj (fin12OfNat a) (fin12OfNat c)) ∧
      (¬ G.Adj (fin12OfNat b) (fin12OfNat c))
    exact ⟨fun h ↦ hab ((graphEdge_edgeIndex_nat G ha12 hb12 hab').mpr h),
      fun h ↦ hac ((graphEdge_edgeIndex_nat G ha12 hc12 hac').mpr h),
      fun h ↦ hbc ((graphEdge_edgeIndex_nat G hb12 hc12 hbc').mpr h)⟩

private theorem homogeneousFour_to_finset (G : SimpleGraph (Fin 12))
    (s : List Nat) (hlen : s.length = 4) (hn : s.Nodup)
    (hb : ∀ x ∈ s, x < 12) (hh : Homogeneous (graphEdge G) s) :
    IsHomogeneousFinset G (finList12 s).toFinset := by
  obtain ⟨a, b, c, d, rfl⟩ := List.length_eq_four.mp hlen
  have ha12 : a < 12 := hb a (by simp)
  have hb12 : b < 12 := hb b (by simp)
  have hc12 : c < 12 := hb c (by simp)
  have hd12 : d < 12 := hb d (by simp)
  have hab' : a ≠ b := by intro e; subst b; simpa using hn
  have hac' : a ≠ c := by intro e; subst c; simpa using hn
  have had' : a ≠ d := by intro e; subst d; simpa using hn
  have hbc' : b ≠ c := by intro e; subst c; simpa using hn
  have hbd' : b ≠ d := by intro e; subst d; simpa using hn
  have hcd' : c ≠ d := by intro e; subst d; simpa using hn
  rw [semantic_homogeneous_four] at hh
  rcases hh with ⟨hab, hac, had, hbc, hbd, hcd⟩ |
      ⟨hab, hac, had, hbc, hbd, hcd⟩
  · apply homogeneous_of_pairConjunction_pos
    change G.Adj (fin12OfNat a) (fin12OfNat b) ∧
      G.Adj (fin12OfNat a) (fin12OfNat c) ∧
      G.Adj (fin12OfNat a) (fin12OfNat d) ∧
      G.Adj (fin12OfNat b) (fin12OfNat c) ∧
      G.Adj (fin12OfNat b) (fin12OfNat d) ∧
      G.Adj (fin12OfNat c) (fin12OfNat d)
    exact ⟨(graphEdge_edgeIndex_nat G ha12 hb12 hab').mp hab,
      (graphEdge_edgeIndex_nat G ha12 hc12 hac').mp hac,
      (graphEdge_edgeIndex_nat G ha12 hd12 had').mp had,
      (graphEdge_edgeIndex_nat G hb12 hc12 hbc').mp hbc,
      (graphEdge_edgeIndex_nat G hb12 hd12 hbd').mp hbd,
      (graphEdge_edgeIndex_nat G hc12 hd12 hcd').mp hcd⟩
  · apply homogeneous_of_pairConjunction_neg
    change (¬ G.Adj (fin12OfNat a) (fin12OfNat b)) ∧
      (¬ G.Adj (fin12OfNat a) (fin12OfNat c)) ∧
      (¬ G.Adj (fin12OfNat a) (fin12OfNat d)) ∧
      (¬ G.Adj (fin12OfNat b) (fin12OfNat c)) ∧
      (¬ G.Adj (fin12OfNat b) (fin12OfNat d)) ∧
      (¬ G.Adj (fin12OfNat c) (fin12OfNat d))
    exact ⟨fun h ↦ hab ((graphEdge_edgeIndex_nat G ha12 hb12 hab').mpr h),
      fun h ↦ hac ((graphEdge_edgeIndex_nat G ha12 hc12 hac').mpr h),
      fun h ↦ had ((graphEdge_edgeIndex_nat G ha12 hd12 had').mpr h),
      fun h ↦ hbc ((graphEdge_edgeIndex_nat G hb12 hc12 hbc').mpr h),
      fun h ↦ hbd ((graphEdge_edgeIndex_nat G hb12 hd12 hbd').mpr h),
      fun h ↦ hcd ((graphEdge_edgeIndex_nat G hc12 hd12 hcd').mpr h)⟩

/-! ## Certificate outcomes imply graph conclusions -/

/-- A graph-side no-four-set hypothesis eliminates the first D12 outcome. -/
theorem not_hasHomogeneousFour_graphEdge (G : SimpleGraph (Fin 12))
    (hno : HasNoHomogeneousFour G) :
    ¬ HasHomogeneousFour (graphEdge G) := by
  rintro ⟨s, hs, hh⟩
  rcases hs with ⟨hlen, hn, hrange⟩
  have hb : ∀ x ∈ s, x < 12 := by
    intro x hx
    exact Finset.mem_range.mp (hrange (by simpa using hx))
  apply hno (finList12 s).toFinset
  · rw [List.toFinset_card_of_nodup (finList12_nodup hn hb)]
    simpa [finList12] using hlen
  · exact homogeneousFour_to_finset G s hlen hn hb hh

private theorem colorable_of_four_homogeneous_blocks (G : SimpleGraph (Fin 12))
    (A B C D : Finset (Fin 12))
    (cover : ∀ v, v ∈ A ∨ v ∈ B ∨ v ∈ C ∨ v ∈ D)
    (hA : IsHomogeneousFinset G A) (hB : IsHomogeneousFinset G B)
    (hC : IsHomogeneousFinset G C) (hD : IsHomogeneousFinset G D) :
    CochromaticColorable G 4 := by
  let c : Fin 12 → Fin 4 := fun v ↦
    if v ∈ A then 0 else if v ∈ B then 1 else if v ∈ C then 2 else 3
  refine ⟨c, ?_⟩
  have fiberA : ∀ v, c v = 0 → v ∈ A := by
    intro v hv
    by_contra ha
    by_cases hb : v ∈ B <;> by_cases hc : v ∈ C <;> simp [c, ha, hb, hc] at hv
  have fiberB : ∀ v, c v = 1 → v ∈ B := by
    intro v hv
    by_cases ha : v ∈ A
    · simp [c, ha] at hv
    by_contra hb
    by_cases hc : v ∈ C <;> simp [c, ha, hb, hc] at hv
  have fiberC : ∀ v, c v = 2 → v ∈ C := by
    intro v hv
    by_cases ha : v ∈ A
    · simp [c, ha] at hv
    by_cases hb : v ∈ B
    · simp [c, ha, hb] at hv
    by_contra hc
    simp [c, ha, hb, hc] at hv
  have fiberD : ∀ v, c v = 3 → v ∈ D := by
    intro v hv
    by_cases ha : v ∈ A
    · simp [c, ha] at hv
    by_cases hb : v ∈ B
    · simp [c, ha, hb] at hv
    by_cases hc : v ∈ C
    · simp [c, ha, hb, hc] at hv
    rcases cover v with h | h | h | h
    · exact (ha h).elim
    · exact (hb h).elim
    · exact (hc h).elim
    · exact h
  intro i
  fin_cases i
  · rcases hA with h | h
    · exact Or.inl fun u v hu hv huv ↦ h u (fiberA u hu) v (fiberA v hv) huv
    · exact Or.inr fun u v hu hv huv ↦ h u (fiberA u hu) v (fiberA v hv) huv
  · rcases hB with h | h
    · exact Or.inl fun u v hu hv huv ↦ h u (fiberB u hu) v (fiberB v hv) huv
    · exact Or.inr fun u v hu hv huv ↦ h u (fiberB u hu) v (fiberB v hv) huv
  · rcases hC with h | h
    · exact Or.inl fun u v hu hv huv ↦ h u (fiberC u hu) v (fiberC v hv) huv
    · exact Or.inr fun u v hu hv huv ↦ h u (fiberC u hu) v (fiberC v hv) huv
  · rcases hD with h | h
    · exact Or.inl fun u v hu hv huv ↦ h u (fiberD u hu) v (fiberD v hv) huv
    · exact Or.inr fun u v hu hv huv ↦ h u (fiberD u hu) v (fiberD v hv) huv

/-- A four-triple D12 outcome is exactly a four-colour cochromatic cover of
the graph whose edges supplied the propositional assignment. -/
theorem colorable_four_of_hasFourHomogeneousTriples (G : SimpleGraph (Fin 12))
    (h : HasFourHomogeneousTriples (graphEdge G)) :
    CochromaticColorable G 4 := by
  obtain ⟨a, b, c, d, hp, ha, hb, hc, hd⟩ := h
  rcases hp with ⟨hala, halb, halc, hald, hn, hcover⟩
  have hbound : ∀ x ∈ a ++ b ++ c ++ d, x < 12 := by
    intro x hx
    apply Finset.mem_range.mp
    rw [← hcover]
    simpa using hx
  have hnabc : (a ++ b ++ c).Nodup := hn.of_append_left
  have hnab : (a ++ b).Nodup := hnabc.of_append_left
  have hna : a.Nodup := hnab.of_append_left
  have hnb : b.Nodup := hnab.of_append_right
  have hnc : c.Nodup := hnabc.of_append_right
  have hnd : d.Nodup := hn.of_append_right
  have hba : ∀ x ∈ a, x < 12 := fun x hx ↦ hbound x (by simp [hx])
  have hbb : ∀ x ∈ b, x < 12 := fun x hx ↦ hbound x (by simp [hx])
  have hbc : ∀ x ∈ c, x < 12 := fun x hx ↦ hbound x (by simp [hx])
  have hbd : ∀ x ∈ d, x < 12 := fun x hx ↦ hbound x (by simp [hx])
  apply colorable_of_four_homogeneous_blocks G
      (finList12 a).toFinset (finList12 b).toFinset
      (finList12 c).toFinset (finList12 d).toFinset
  · intro v
    have hvRange : v.val ∈ Finset.range 12 := Finset.mem_range.mpr v.isLt
    rw [← hcover] at hvRange
    simp only [List.mem_toFinset, List.mem_append] at hvRange
    rcases hvRange with ((hv | hv) | hv) | hv
    · left
      exact self_mem_finList12 v hv
    · right; left
      exact self_mem_finList12 v hv
    · right; right; left
      exact self_mem_finList12 v hv
    · right; right; right
      exact self_mem_finList12 v hv
  · exact homogeneousTriple_to_finset G a hala hna hba ha
  · exact homogeneousTriple_to_finset G b halb hnb hbb hb
  · exact homogeneousTriple_to_finset G c halc hnc hbc hc
  · exact homogeneousTriple_to_finset G d hald hnd hbd hd

/-- Consume a complete D12 semantic outcome after ruling out the graph and
normalization alternatives. -/
theorem colorable_four_of_outcome (G : SimpleGraph (Fin 12))
    (units : List (Nat × Bool)) (hno : HasNoHomogeneousFour G)
    (hout : D12Outcome (graphEdge G) units)
    (hu : SatisfiesUnits (graphEdge G) units) :
    CochromaticColorable G 4 := by
  apply colorable_four_of_hasFourHomogeneousTriples G
  exact fourHomogeneousTriples_of_outcome (graphEdge G) units hout
    (not_hasHomogeneousFour_graphEdge G hno) hu

/-! ## Canonical normalization unit lists -/

/-- Units fixing all eleven edges incident with vertex zero. -/
def rootUnits (d : Nat) : List (Nat × Bool) :=
  (List.range 11).map fun k ↦ (k + 1, decide (k < d))

/-- Units fixing vertex one's row inside the normalized neighborhood of zero. -/
def rowOneInsideUnits (d r : Nat) : List (Nat × Bool) :=
  (List.range (min (d - 1) 10)).map fun k ↦
    (edgeIndex12 1 (k + 2) + 1, decide (k < r))

/-- Units fixing vertex one's row outside the normalized neighborhood of zero. -/
def rowOneOutsideUnits (d s : Nat) : List (Nat × Bool) :=
  (List.range (if d = 0 then 0 else 11 - d)).map fun k ↦
    (edgeIndex12 1 (d + 1 + k) + 1, decide (k < s))

/-- Units fixing vertex two's residual row after the first two normalizations. -/
def rowTwoResidualUnits (d r t : Nat) : List (Nat × Bool) :=
  (List.range (if r = 0 then 0 else min (d - (r + 1)) (10 - r))).map fun k ↦
    (edgeIndex12 2 (r + 2 + k) + 1, decide (k < t))

theorem satisfiesUnits_append {edge : Nat → Prop} {xs ys : List (Nat × Bool)}
    (hx : SatisfiesUnits edge xs) (hy : SatisfiesUnits edge ys) :
    SatisfiesUnits edge (xs ++ ys) := by
  intro u hu
  rcases List.mem_append.mp hu with hu | hu
  · exact hx u hu
  · exact hy u hu

theorem rootRow_satisfies_rootUnits (G : SimpleGraph (Fin 12)) {d : Nat}
    (hroot : RootRow G d) :
    SatisfiesUnits (graphEdge G) (rootUnits d) := by
  intro u hu
  simp only [rootUnits, List.mem_map] at hu
  obtain ⟨k, hk, rfl⟩ := hu
  have hklt : k < 11 := List.mem_range.mp hk
  let x : Fin 12 := ⟨k + 1, by omega⟩
  have hxval : x.val = k + 1 := rfl
  have hne : (0 : Nat) ≠ k + 1 := by omega
  have hedge := graphEdge_edgeIndex_nat G (i := 0) (j := k + 1)
    (by omega) (by omega) hne
  have hrow := hroot x
  by_cases hkd : k < d
  · have hadj : G.Adj (fin12OfNat 0) (fin12OfNat (k + 1)) := by
      have : G.Adj 0 x := hrow.mpr (by
        simp [D12Normalization.initialAfterZero, x]
        omega)
      simpa [fin12OfNat, x, Nat.mod_eq_of_lt (by omega : k + 1 < 12)] using this
    simpa [SatisfiesUnit, hkd, edgeIndex12] using hedge.mpr hadj
  · have hnadj : ¬ G.Adj (fin12OfNat 0) (fin12OfNat (k + 1)) := by
      intro hadj
      have hxmem := hrow.mp (by
        simpa [fin12OfNat, Nat.mod_eq_of_lt (by omega : k + 1 < 12)] using hadj)
      simp [D12Normalization.initialAfterZero, x] at hxmem
      omega
    simpa [SatisfiesUnit, hkd, edgeIndex12] using fun h ↦ hnadj (hedge.mp h)

theorem rowOneInside_satisfies_units (G : SimpleGraph (Fin 12)) {d r : Nat}
    (hrow : RowOneInside G d r) :
    SatisfiesUnits (graphEdge G) (rowOneInsideUnits d r) := by
  intro u hu
  simp only [rowOneInsideUnits, List.mem_map] at hu
  obtain ⟨k, hk, rfl⟩ := hu
  have hklt := List.mem_range.mp hk
  let x : Fin 12 := ⟨k + 2, by omega⟩
  have hne : (1 : Nat) ≠ k + 2 := by omega
  have hedge := graphEdge_edgeIndex_nat G (i := 1) (j := k + 2)
    (by omega) (by omega) hne
  have hdomain : x ∈ D12Normalization.intervalFrom 12 2 (d - 1) := by
    simp [D12Normalization.intervalFrom, x]
    omega
  have hrowx := hrow x hdomain
  by_cases hkr : k < r
  · have hadj : G.Adj (fin12OfNat 1) (fin12OfNat (k + 2)) := by
      have : G.Adj 1 x := hrowx.mpr (by
        simp [D12Normalization.intervalFrom, x]
        omega)
      simpa [fin12OfNat, x, Nat.mod_eq_of_lt (by omega : k + 2 < 12)] using this
    simpa [SatisfiesUnit, hkr] using hedge.mpr hadj
  · have hnadj : ¬ G.Adj (fin12OfNat 1) (fin12OfNat (k + 2)) := by
      intro hadj
      have hxmem := hrowx.mp (by
        simpa [fin12OfNat, x, Nat.mod_eq_of_lt (by omega : k + 2 < 12)] using hadj)
      simp [D12Normalization.intervalFrom, x] at hxmem
      omega
    simpa [SatisfiesUnit, hkr] using fun h ↦ hnadj (hedge.mp h)

theorem rowOneOutside_satisfies_units (G : SimpleGraph (Fin 12)) {d s : Nat}
    (hrow : RowOneOutside G d s) :
    SatisfiesUnits (graphEdge G) (rowOneOutsideUnits d s) := by
  intro u hu
  simp only [rowOneOutsideUnits, List.mem_map] at hu
  obtain ⟨k, hk, rfl⟩ := hu
  have hklt := List.mem_range.mp hk
  have hdpos : 0 < d := by
    by_contra hd
    simp only [Nat.not_lt, Nat.le_zero] at hd
    simp [hd] at hklt
  have hkmain : k < 11 - d := by
    simpa [if_neg (Nat.ne_of_gt hdpos)] using hklt
  let x : Fin 12 := ⟨d + 1 + k, by omega⟩
  have hne : (1 : Nat) ≠ d + 1 + k := by omega
  have hedge := graphEdge_edgeIndex_nat G (i := 1) (j := d + 1 + k)
    (by omega) (by omega) hne
  have hdomain : x ∈ D12Normalization.intervalFrom 12 (d + 1) (11 - d) := by
    simp [D12Normalization.intervalFrom, x]
    omega
  have hrowx := hrow x hdomain
  by_cases hks : k < s
  · have hadj : G.Adj (fin12OfNat 1) (fin12OfNat (d + 1 + k)) := by
      have : G.Adj 1 x := hrowx.mpr (by
        simp [D12Normalization.intervalFrom, x]
        omega)
      simpa [fin12OfNat, x,
        Nat.mod_eq_of_lt (by omega : d + 1 + k < 12)] using this
    simpa [SatisfiesUnit, hks] using hedge.mpr hadj
  · have hnadj : ¬ G.Adj (fin12OfNat 1) (fin12OfNat (d + 1 + k)) := by
      intro hadj
      have hxmem := hrowx.mp (by
        simpa [fin12OfNat, x,
          Nat.mod_eq_of_lt (by omega : d + 1 + k < 12)] using hadj)
      simp [D12Normalization.intervalFrom, x] at hxmem
      omega
    simpa [SatisfiesUnit, hks] using fun h ↦ hnadj (hedge.mp h)

theorem rowTwoResidual_satisfies_units (G : SimpleGraph (Fin 12)) {d r t : Nat}
    (hrow : RowTwoResidual G d r t) :
    SatisfiesUnits (graphEdge G) (rowTwoResidualUnits d r t) := by
  intro u hu
  simp only [rowTwoResidualUnits, List.mem_map] at hu
  obtain ⟨k, hk, rfl⟩ := hu
  have hklt := List.mem_range.mp hk
  have hrpos : 0 < r := by
    by_contra hr
    simp only [Nat.not_lt, Nat.le_zero] at hr
    simp [hr] at hklt
  have hkboth : k < d - (r + 1) ∧ k < 10 - r := by
    simpa [if_neg (Nat.ne_of_gt hrpos)] using hklt
  have hkmain : k < d - (r + 1) := by
    exact hkboth.1
  have hkfin : k < 10 - r := by
    exact hkboth.2
  let x : Fin 12 := ⟨r + 2 + k, by omega⟩
  have hne : (2 : Nat) ≠ r + 2 + k := by omega
  have hedge := graphEdge_edgeIndex_nat G (i := 2) (j := r + 2 + k)
    (by omega) (by omega) hne
  have hdomain : x ∈ D12Normalization.intervalFrom 12 (r + 2) (d - (r + 1)) := by
    simp [D12Normalization.intervalFrom, x]
    omega
  have hrowx := hrow x hdomain
  by_cases hkt : k < t
  · have hadj : G.Adj (fin12OfNat 2) (fin12OfNat (r + 2 + k)) := by
      have : G.Adj 2 x := hrowx.mpr (by
        simp [D12Normalization.intervalFrom, x]
        omega)
      simpa [fin12OfNat, x,
        Nat.mod_eq_of_lt (by omega : r + 2 + k < 12)] using this
    simpa [SatisfiesUnit, hkt] using hedge.mpr hadj
  · have hnadj : ¬ G.Adj (fin12OfNat 2) (fin12OfNat (r + 2 + k)) := by
      intro hadj
      have hxmem := hrowx.mp (by
        simpa [fin12OfNat, x,
          Nat.mod_eq_of_lt (by omega : r + 2 + k < 12)] using hadj)
      simp [D12Normalization.intervalFrom, x] at hxmem
      omega
    simpa [SatisfiesUnit, hkt] using fun h ↦ hnadj (hedge.mp h)

/-! ## Dispatcher-facing wrappers -/

theorem d12ColorableD (H : SimpleGraph (Fin 12))
    (hno : HasNoHomogeneousFour H) {d : Nat} (hroot : RootRow H d)
    (units : List (Nat × Bool)) (huEq : units = rootUnits d)
    (hout : D12Outcome (graphEdge H) units) : CochromaticColorable H 4 := by
  apply colorable_four_of_outcome H units hno hout
  rw [huEq]
  exact rootRow_satisfies_rootUnits H hroot

theorem d12ColorableDR (H : SimpleGraph (Fin 12))
    (hno : HasNoHomogeneousFour H) {d r : Nat} (hroot : RootRow H d)
    (hinside : RowOneInside H d r) (units : List (Nat × Bool))
    (huEq : units = rootUnits d ++ rowOneInsideUnits d r)
    (hout : D12Outcome (graphEdge H) units) : CochromaticColorable H 4 := by
  apply colorable_four_of_outcome H units hno hout
  rw [huEq]
  exact satisfiesUnits_append (rootRow_satisfies_rootUnits H hroot)
    (rowOneInside_satisfies_units H hinside)

theorem d12ColorableDRS (H : SimpleGraph (Fin 12))
    (hno : HasNoHomogeneousFour H) {d r s : Nat} (hroot : RootRow H d)
    (hinside : RowOneInside H d r) (houtside : RowOneOutside H d s)
    (units : List (Nat × Bool))
    (huEq : units = rootUnits d ++ rowOneInsideUnits d r ++ rowOneOutsideUnits d s)
    (hout : D12Outcome (graphEdge H) units) : CochromaticColorable H 4 := by
  apply colorable_four_of_outcome H units hno hout
  rw [huEq]
  exact satisfiesUnits_append
    (satisfiesUnits_append (rootRow_satisfies_rootUnits H hroot)
      (rowOneInside_satisfies_units H hinside))
    (rowOneOutside_satisfies_units H houtside)

theorem d12ColorableDRT (H : SimpleGraph (Fin 12))
    (hno : HasNoHomogeneousFour H) {d r t : Nat} (hroot : RootRow H d)
    (hinside : RowOneInside H d r) (htwo : RowTwoResidual H d r t)
    (units : List (Nat × Bool))
    (huEq : units = rootUnits d ++ rowOneInsideUnits d r ++ rowTwoResidualUnits d r t)
    (hout : D12Outcome (graphEdge H) units) : CochromaticColorable H 4 := by
  apply colorable_four_of_outcome H units hno hout
  rw [huEq]
  exact satisfiesUnits_append
    (satisfiesUnits_append (rootRow_satisfies_rootUnits H hroot)
      (rowOneInside_satisfies_units H hinside))
    (rowTwoResidual_satisfies_units H htwo)

theorem d12ColorableDRST (H : SimpleGraph (Fin 12))
    (hno : HasNoHomogeneousFour H) {d r s t : Nat} (hroot : RootRow H d)
    (hinside : RowOneInside H d r) (houtside : RowOneOutside H d s)
    (htwo : RowTwoResidual H d r t) (units : List (Nat × Bool))
    (huEq : units = rootUnits d ++ rowOneInsideUnits d r ++
      rowOneOutsideUnits d s ++ rowTwoResidualUnits d r t)
    (hout : D12Outcome (graphEdge H) units) : CochromaticColorable H 4 := by
  apply colorable_four_of_outcome H units hno hout
  rw [huEq]
  exact satisfiesUnits_append
    (satisfiesUnits_append
      (satisfiesUnits_append (rootRow_satisfies_rootUnits H hroot)
        (rowOneInside_satisfies_units H hinside))
      (rowOneOutside_satisfies_units H houtside))
    (rowTwoResidual_satisfies_units H htwo)

theorem colorable_four_of_no_homogeneous_four
    (G : SimpleGraph (Fin 12)) (hno : HasNoHomogeneousFour G) :
    CochromaticColorable G 4 := by
  classical
  obtain ⟨H, hparameters, hnoH, htransport⟩ :=
    exists_historical_root_parameters G hno
  apply (htransport 4).mp
  let : DecidableRel H.Adj := Classical.decRel _
  rcases hparameters with hd6 | hd7 | hd8 | hd9 | hd10 | hd11
  · obtain ⟨r, hr, s, hs, hroot, hinside, houtside⟩ := hd6
    interval_cases r
    · interval_cases s
      · exact d12ColorableDRS H hnoH hroot hinside houtside
          d6_r0_s0_units (by decide) (d6_r0_s0 (graphEdge H))
      · exact d12ColorableDRS H hnoH hroot hinside houtside
          d6_r0_s1_units (by decide) (d6_r0_s1 (graphEdge H))
      · exact d12ColorableDRS H hnoH hroot hinside houtside
          d6_r0_s2_units (by decide) (d6_r0_s2 (graphEdge H))
      · exact d12ColorableDRS H hnoH hroot hinside houtside
          d6_r0_s3_units (by decide) (d6_r0_s3 (graphEdge H))
      · exact d12ColorableDRS H hnoH hroot hinside houtside
          d6_r0_s4_units (by decide) (d6_r0_s4 (graphEdge H))
      · exact d12ColorableDRS H hnoH hroot hinside houtside
          d6_r0_s5_units (by decide) (d6_r0_s5 (graphEdge H))
    · interval_cases s
      · exact d12ColorableDRS H hnoH hroot hinside houtside
          d6_r1_s0_units (by decide) (d6_r1_s0 (graphEdge H))
      · exact d12ColorableDRS H hnoH hroot hinside houtside
          d6_r1_s1_units (by decide) (d6_r1_s1 (graphEdge H))
      · obtain ⟨H', t, ht, hroot', hinside', htwo, hno', houtside', hback⟩ :=
          exists_row_two_residual_normalization H 6 1 (by omega) (by omega)
            (by omega) hroot hinside hnoH
        apply (hback 4).mp
        have houtside'' := houtside' 2 houtside
        interval_cases t
        · exact d12ColorableDRST H' hno' hroot' hinside' houtside'' htwo
            d6_r1_s2_t0_units (by decide) (d6_r1_s2_t0 (graphEdge H'))
        · exact d12ColorableDRST H' hno' hroot' hinside' houtside'' htwo
            d6_r1_s2_t1_units (by decide) (d6_r1_s2_t1 (graphEdge H'))
        · exact d12ColorableDRST H' hno' hroot' hinside' houtside'' htwo
            d6_r1_s2_t2_units (by decide) (d6_r1_s2_t2 (graphEdge H'))
        · exact d12ColorableDRST H' hno' hroot' hinside' houtside'' htwo
            d6_r1_s2_t3_units (by decide) (d6_r1_s2_t3 (graphEdge H'))
        · exact d12ColorableDRST H' hno' hroot' hinside' houtside'' htwo
            d6_r1_s2_t4_units (by decide) (d6_r1_s2_t4 (graphEdge H'))
      · obtain ⟨H', t, ht, hroot', hinside', htwo, hno', houtside', hback⟩ :=
          exists_row_two_residual_normalization H 6 1 (by omega) (by omega)
            (by omega) hroot hinside hnoH
        apply (hback 4).mp
        have houtside'' := houtside' 3 houtside
        interval_cases t
        · exact d12ColorableDRST H' hno' hroot' hinside' houtside'' htwo
            d6_r1_s3_t0_units (by decide) (d6_r1_s3_t0 (graphEdge H'))
        · exact d12ColorableDRST H' hno' hroot' hinside' houtside'' htwo
            d6_r1_s3_t1_units (by decide) (d6_r1_s3_t1 (graphEdge H'))
        · exact d12ColorableDRST H' hno' hroot' hinside' houtside'' htwo
            d6_r1_s3_t2_units (by decide) (d6_r1_s3_t2 (graphEdge H'))
        · exact d12ColorableDRST H' hno' hroot' hinside' houtside'' htwo
            d6_r1_s3_t3_units (by decide) (d6_r1_s3_t3 (graphEdge H'))
        · exact d12ColorableDRST H' hno' hroot' hinside' houtside'' htwo
            d6_r1_s3_t4_units (by decide) (d6_r1_s3_t4 (graphEdge H'))
      · obtain ⟨H', t, ht, hroot', hinside', htwo, hno', houtside', hback⟩ :=
          exists_row_two_residual_normalization H 6 1 (by omega) (by omega)
            (by omega) hroot hinside hnoH
        apply (hback 4).mp
        have houtside'' := houtside' 4 houtside
        interval_cases t
        · exact d12ColorableDRST H' hno' hroot' hinside' houtside'' htwo
            d6_r1_s4_t0_units (by decide) (d6_r1_s4_t0 (graphEdge H'))
        · exact d12ColorableDRST H' hno' hroot' hinside' houtside'' htwo
            d6_r1_s4_t1_units (by decide) (d6_r1_s4_t1 (graphEdge H'))
        · exact d12ColorableDRST H' hno' hroot' hinside' houtside'' htwo
            d6_r1_s4_t2_units (by decide) (d6_r1_s4_t2 (graphEdge H'))
        · exact d12ColorableDRST H' hno' hroot' hinside' houtside'' htwo
            d6_r1_s4_t3_units (by decide) (d6_r1_s4_t3 (graphEdge H'))
        · exact d12ColorableDRST H' hno' hroot' hinside' houtside'' htwo
            d6_r1_s4_t4_units (by decide) (d6_r1_s4_t4 (graphEdge H'))
      · exact d12ColorableDRS H hnoH hroot hinside houtside
          d6_r1_s5_units (by decide) (d6_r1_s5 (graphEdge H))
    · interval_cases s
      · exact d12ColorableDRS H hnoH hroot hinside houtside
          d6_r2_s0_units (by decide) (d6_r2_s0 (graphEdge H))
      · obtain ⟨H', t, ht, hroot', hinside', htwo, hno', houtside', hback⟩ :=
          exists_row_two_residual_normalization H 6 2 (by omega) (by omega)
            (by omega) hroot hinside hnoH
        apply (hback 4).mp
        have houtside'' := houtside' 1 houtside
        interval_cases t
        · exact d12ColorableDRST H' hno' hroot' hinside' houtside'' htwo
            d6_r2_s1_t0_units (by decide) (d6_r2_s1_t0 (graphEdge H'))
        · exact d12ColorableDRST H' hno' hroot' hinside' houtside'' htwo
            d6_r2_s1_t1_units (by decide) (d6_r2_s1_t1 (graphEdge H'))
        · exact d12ColorableDRST H' hno' hroot' hinside' houtside'' htwo
            d6_r2_s1_t2_units (by decide) (d6_r2_s1_t2 (graphEdge H'))
        · exact d12ColorableDRST H' hno' hroot' hinside' houtside'' htwo
            d6_r2_s1_t3_units (by decide) (d6_r2_s1_t3 (graphEdge H'))
      · obtain ⟨H', t, ht, hroot', hinside', htwo, hno', houtside', hback⟩ :=
          exists_row_two_residual_normalization H 6 2 (by omega) (by omega)
            (by omega) hroot hinside hnoH
        apply (hback 4).mp
        have houtside'' := houtside' 2 houtside
        interval_cases t
        · exact d12ColorableDRST H' hno' hroot' hinside' houtside'' htwo
            d6_r2_s2_t0_units (by decide) (d6_r2_s2_t0 (graphEdge H'))
        · exact d12ColorableDRST H' hno' hroot' hinside' houtside'' htwo
            d6_r2_s2_t1_units (by decide) (d6_r2_s2_t1 (graphEdge H'))
        · exact d12ColorableDRST H' hno' hroot' hinside' houtside'' htwo
            d6_r2_s2_t2_units (by decide) (d6_r2_s2_t2 (graphEdge H'))
        · exact d12ColorableDRST H' hno' hroot' hinside' houtside'' htwo
            d6_r2_s2_t3_units (by decide) (d6_r2_s2_t3 (graphEdge H'))
      · obtain ⟨H', t, ht, hroot', hinside', htwo, hno', houtside', hback⟩ :=
          exists_row_two_residual_normalization H 6 2 (by omega) (by omega)
            (by omega) hroot hinside hnoH
        apply (hback 4).mp
        have houtside'' := houtside' 3 houtside
        interval_cases t
        · exact d12ColorableDRST H' hno' hroot' hinside' houtside'' htwo
            d6_r2_s3_t0_units (by decide) (d6_r2_s3_t0 (graphEdge H'))
        · exact d12ColorableDRST H' hno' hroot' hinside' houtside'' htwo
            d6_r2_s3_t1_units (by decide) (d6_r2_s3_t1 (graphEdge H'))
        · exact d12ColorableDRST H' hno' hroot' hinside' houtside'' htwo
            d6_r2_s3_t2_units (by decide) (d6_r2_s3_t2 (graphEdge H'))
        · exact d12ColorableDRST H' hno' hroot' hinside' houtside'' htwo
            d6_r2_s3_t3_units (by decide) (d6_r2_s3_t3 (graphEdge H'))
      · obtain ⟨H', t, ht, hroot', hinside', htwo, hno', houtside', hback⟩ :=
          exists_row_two_residual_normalization H 6 2 (by omega) (by omega)
            (by omega) hroot hinside hnoH
        apply (hback 4).mp
        have houtside'' := houtside' 4 houtside
        interval_cases t
        · exact d12ColorableDRST H' hno' hroot' hinside' houtside'' htwo
            d6_r2_s4_t0_units (by decide) (d6_r2_s4_t0 (graphEdge H'))
        · exact d12ColorableDRST H' hno' hroot' hinside' houtside'' htwo
            d6_r2_s4_t1_units (by decide) (d6_r2_s4_t1 (graphEdge H'))
        · exact d12ColorableDRST H' hno' hroot' hinside' houtside'' htwo
            d6_r2_s4_t2_units (by decide) (d6_r2_s4_t2 (graphEdge H'))
        · exact d12ColorableDRST H' hno' hroot' hinside' houtside'' htwo
            d6_r2_s4_t3_units (by decide) (d6_r2_s4_t3 (graphEdge H'))
      · exact d12ColorableDRS H hnoH hroot hinside houtside
          d6_r2_s5_units (by decide) (d6_r2_s5 (graphEdge H))
    · interval_cases s
      · exact d12ColorableDRS H hnoH hroot hinside houtside
          d6_r3_s0_units (by decide) (d6_r3_s0 (graphEdge H))
      · obtain ⟨H', t, ht, hroot', hinside', htwo, hno', houtside', hback⟩ :=
          exists_row_two_residual_normalization H 6 3 (by omega) (by omega)
            (by omega) hroot hinside hnoH
        apply (hback 4).mp
        have houtside'' := houtside' 1 houtside
        interval_cases t
        · exact d12ColorableDRST H' hno' hroot' hinside' houtside'' htwo
            d6_r3_s1_t0_units (by decide) (d6_r3_s1_t0 (graphEdge H'))
        · exact d12ColorableDRST H' hno' hroot' hinside' houtside'' htwo
            d6_r3_s1_t1_units (by decide) (d6_r3_s1_t1 (graphEdge H'))
        · exact d12ColorableDRST H' hno' hroot' hinside' houtside'' htwo
            d6_r3_s1_t2_units (by decide) (d6_r3_s1_t2 (graphEdge H'))
      · obtain ⟨H', t, ht, hroot', hinside', htwo, hno', houtside', hback⟩ :=
          exists_row_two_residual_normalization H 6 3 (by omega) (by omega)
            (by omega) hroot hinside hnoH
        apply (hback 4).mp
        have houtside'' := houtside' 2 houtside
        interval_cases t
        · exact d12ColorableDRST H' hno' hroot' hinside' houtside'' htwo
            d6_r3_s2_t0_units (by decide) (d6_r3_s2_t0 (graphEdge H'))
        · exact d12ColorableDRST H' hno' hroot' hinside' houtside'' htwo
            d6_r3_s2_t1_units (by decide) (d6_r3_s2_t1 (graphEdge H'))
        · exact d12ColorableDRST H' hno' hroot' hinside' houtside'' htwo
            d6_r3_s2_t2_units (by decide) (d6_r3_s2_t2 (graphEdge H'))
      · exact d12ColorableDRS H hnoH hroot hinside houtside
          d6_r3_s3_units (by decide) (d6_r3_s3 (graphEdge H))
      · exact d12ColorableDRS H hnoH hroot hinside houtside
          d6_r3_s4_units (by decide) (d6_r3_s4 (graphEdge H))
      · exact d12ColorableDRS H hnoH hroot hinside houtside
          d6_r3_s5_units (by decide) (d6_r3_s5 (graphEdge H))
  · obtain ⟨r, hr, s, hs, hroot, hinside, houtside⟩ := hd7
    interval_cases r
    · exact d12ColorableDR H hnoH hroot hinside
        d7_r0_units (by decide) (d7_r0 (graphEdge H))
    · interval_cases s
      · exact d12ColorableDRS H hnoH hroot hinside houtside
          d7_r1_s0_units (by decide) (d7_r1_s0 (graphEdge H))
      · exact d12ColorableDRS H hnoH hroot hinside houtside
          d7_r1_s1_units (by decide) (d7_r1_s1 (graphEdge H))
      · exact d12ColorableDRS H hnoH hroot hinside houtside
          d7_r1_s2_units (by decide) (d7_r1_s2 (graphEdge H))
      · exact d12ColorableDRS H hnoH hroot hinside houtside
          d7_r1_s3_units (by decide) (d7_r1_s3 (graphEdge H))
      · exact d12ColorableDRS H hnoH hroot hinside houtside
          d7_r1_s4_units (by decide) (d7_r1_s4 (graphEdge H))
    · interval_cases s
      · exact d12ColorableDRS H hnoH hroot hinside houtside
          d7_r2_s0_units (by decide) (d7_r2_s0 (graphEdge H))
      · exact d12ColorableDRS H hnoH hroot hinside houtside
          d7_r2_s1_units (by decide) (d7_r2_s1 (graphEdge H))
      · exact d12ColorableDRS H hnoH hroot hinside houtside
          d7_r2_s2_units (by decide) (d7_r2_s2 (graphEdge H))
      · obtain ⟨H', t, ht, hroot', hinside', htwo, hno', houtside', hback⟩ :=
          exists_row_two_residual_normalization H 7 2 (by omega) (by omega)
            (by omega) hroot hinside hnoH
        apply (hback 4).mp
        have houtside'' := houtside' 3 houtside
        interval_cases t
        · exact d12ColorableDRST H' hno' hroot' hinside' houtside'' htwo
            d7_r2_s3_t0_units (by decide) (d7_r2_s3_t0 (graphEdge H'))
        · exact d12ColorableDRST H' hno' hroot' hinside' houtside'' htwo
            d7_r2_s3_t1_units (by decide) (d7_r2_s3_t1 (graphEdge H'))
        · exact d12ColorableDRST H' hno' hroot' hinside' houtside'' htwo
            d7_r2_s3_t2_units (by decide) (d7_r2_s3_t2 (graphEdge H'))
        · exact d12ColorableDRST H' hno' hroot' hinside' houtside'' htwo
            d7_r2_s3_t3_units (by decide) (d7_r2_s3_t3 (graphEdge H'))
        · exact d12ColorableDRST H' hno' hroot' hinside' houtside'' htwo
            d7_r2_s3_t4_units (by decide) (d7_r2_s3_t4 (graphEdge H'))
      · exact d12ColorableDRS H hnoH hroot hinside houtside
          d7_r2_s4_units (by decide) (d7_r2_s4 (graphEdge H))
    · interval_cases s
      · exact d12ColorableDRS H hnoH hroot hinside houtside
          d7_r3_s0_units (by decide) (d7_r3_s0 (graphEdge H))
      · exact d12ColorableDRS H hnoH hroot hinside houtside
          d7_r3_s1_units (by decide) (d7_r3_s1 (graphEdge H))
      · exact d12ColorableDRS H hnoH hroot hinside houtside
          d7_r3_s2_units (by decide) (d7_r3_s2 (graphEdge H))
      · exact d12ColorableDRS H hnoH hroot hinside houtside
          d7_r3_s3_units (by decide) (d7_r3_s3 (graphEdge H))
      · exact d12ColorableDRS H hnoH hroot hinside houtside
          d7_r3_s4_units (by decide) (d7_r3_s4 (graphEdge H))
  · obtain ⟨r, hr, hroot, hinside⟩ := hd8
    interval_cases r
    · exact d12ColorableDR H hnoH hroot hinside
        d8_r0_units (by decide) (d8_r0 (graphEdge H))
    · obtain ⟨H', t, ht, hroot', hinside', htwo, hno', _, hback⟩ :=
        exists_row_two_residual_normalization H 8 1 (by omega) (by omega)
          (by omega) hroot hinside hnoH
      apply (hback 4).mp
      interval_cases t
      · exact d12ColorableDRT H' hno' hroot' hinside' htwo
          d8_r1_t0_units (by decide) (d8_r1_t0 (graphEdge H'))
      · exact d12ColorableDRT H' hno' hroot' hinside' htwo
          d8_r1_t1_units (by decide) (d8_r1_t1 (graphEdge H'))
      · exact d12ColorableDRT H' hno' hroot' hinside' htwo
          d8_r1_t2_units (by decide) (d8_r1_t2 (graphEdge H'))
      · exact d12ColorableDRT H' hno' hroot' hinside' htwo
          d8_r1_t3_units (by decide) (d8_r1_t3 (graphEdge H'))
      · exact d12ColorableDRT H' hno' hroot' hinside' htwo
          d8_r1_t4_units (by decide) (d8_r1_t4 (graphEdge H'))
      · exact d12ColorableDRT H' hno' hroot' hinside' htwo
          d8_r1_t5_units (by decide) (d8_r1_t5 (graphEdge H'))
      · exact d12ColorableDRT H' hno' hroot' hinside' htwo
          d8_r1_t6_units (by decide) (d8_r1_t6 (graphEdge H'))
    · obtain ⟨H', t, ht, hroot', hinside', htwo, hno', _, hback⟩ :=
        exists_row_two_residual_normalization H 8 2 (by omega) (by omega)
          (by omega) hroot hinside hnoH
      apply (hback 4).mp
      interval_cases t
      · exact d12ColorableDRT H' hno' hroot' hinside' htwo
          d8_r2_t0_units (by decide) (d8_r2_t0 (graphEdge H'))
      · exact d12ColorableDRT H' hno' hroot' hinside' htwo
          d8_r2_t1_units (by decide) (d8_r2_t1 (graphEdge H'))
      · exact d12ColorableDRT H' hno' hroot' hinside' htwo
          d8_r2_t2_units (by decide) (d8_r2_t2 (graphEdge H'))
      · exact d12ColorableDRT H' hno' hroot' hinside' htwo
          d8_r2_t3_units (by decide) (d8_r2_t3 (graphEdge H'))
      · exact d12ColorableDRT H' hno' hroot' hinside' htwo
          d8_r2_t4_units (by decide) (d8_r2_t4 (graphEdge H'))
      · exact d12ColorableDRT H' hno' hroot' hinside' htwo
          d8_r2_t5_units (by decide) (d8_r2_t5 (graphEdge H'))
    · exact d12ColorableDR H hnoH hroot hinside
        d8_r3_units (by decide) (d8_r3 (graphEdge H))
    · exact d12ColorableDR H hnoH hroot hinside
        d8_r4_units (by decide) (d8_r4 (graphEdge H))
  · exact d12ColorableD H hnoH hd9
      d9_units (by decide) (d9 (graphEdge H))
  · exact d12ColorableD H hnoH hd10
      d10_units (by decide) (d10 (graphEdge H))
  · exact d12ColorableD H hnoH hd11
      d11_units (by decide) (d11 (graphEdge H))

/-- Every graph on twelve vertices admits a cochromatic colouring with four colours. -/
theorem every_graph_on_twelve_colorable_four (G : SimpleGraph (Fin 12)) :
    CochromaticColorable G 4 := by
  classical
  by_cases hno : HasNoHomogeneousFour G
  · exact colorable_four_of_no_homogeneous_four G hno
  · unfold HasNoHomogeneousFour at hno
    push Not at hno
    obtain ⟨S, hcard, hS⟩ := hno
    exact colorable_four_of_homogeneous_four G S hcard hS

/-- Erdős Problem 758: the largest cochromatic number of a twelve-vertex
graph is exactly four. -/
theorem erdos_758 : z 12 = 4 :=
  z_eq_of_upper_and_witness every_graph_on_twelve_colorable_four (by decide)
    ⟨paleyPrefix12, paleyPrefix12_not_three⟩

#print axioms every_graph_on_twelve_colorable_four
#print axioms erdos_758

end Erdos758
