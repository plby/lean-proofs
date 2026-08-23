/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 717.
https://www.erdosproblems.com/forum/thread/717

Informal authors:
- Jacob Fox
- Choongbum Lee
- Benny Sudakov

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos717.md
-/
/-
This is a Lean formalization of the affirmative resolution of Erdős Problem 717.
https://www.erdosproblems.com/717

Informal authors:
- Jacob Fox
- Choongbum Lee
- Benny Sudakov

Formal authors:
- Codex

The accompanying detailed proof and Leanization plan is `tex/717.tex`.
-/

import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import ErdosProblems.Erdos717.GlobalArithmetic

open Function Set
open SimpleGraph

namespace Erdos717

/-! ### Faithful clique-subdivision models -/

/-- One orientation of every unordered edge of `K_r`. -/
abbrev CliqueEdge (r : ℕ) := {e : Fin r × Fin r // e.1 < e.2}

/-- The vertices of a walk other than its two endpoints. -/
def walkInteriorSet {V : Type*} {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) : Set V :=
  {x | x ∈ p.support ∧ x ≠ u ∧ x ≠ v}

/-- A subdivision of `K_r` in `G`: distinct branch vertices and paths with
pairwise disjoint interiors which avoid every branch vertex. -/
structure CliqueSubdivision {V : Type*} (G : SimpleGraph V) (r : ℕ) where
  branch : Fin r ↪ V
  path : ∀ e : CliqueEdge r, G.Walk (branch e.1.1) (branch e.1.2)
  path_isPath : ∀ e, (path e).IsPath
  interior_avoids_branch : ∀ e,
    Disjoint (walkInteriorSet (path e)) (Set.range branch)
  interior_pairwise : Pairwise fun e f =>
    Disjoint (walkInteriorSet (path e)) (walkInteriorSet (path f))

/-- The graph `G` contains a subdivision of the complete graph `K_r`. -/
def ContainsCliqueSubdivision {V : Type*} (G : SimpleGraph V) (r : ℕ) : Prop :=
  Nonempty (CliqueSubdivision G r)

/-- Convert the shared subdivision model from the reusable `Erdos718`
development. -/
def CliqueSubdivision.ofErdos718 {V : Type*} {G : SimpleGraph V} {r : ℕ}
    (S : Erdos718.CliqueSubdivision G r) : CliqueSubdivision G r where
  branch := S.branch
  path := S.path
  path_isPath := S.path_isPath
  interior_avoids_branch := by
    intro e
    simpa only [walkInteriorSet, Erdos718.walkInteriorSet] using
      S.interior_avoids_branch e
  interior_pairwise := by
    intro e f hef
    simpa only [walkInteriorSet, Erdos718.walkInteriorSet] using
      S.interior_pairwise hef

theorem ContainsCliqueSubdivision.ofErdos718 {V : Type*}
    {G : SimpleGraph V} {r : ℕ}
    (h : Erdos718.ContainsCliqueSubdivision G r) :
    ContainsCliqueSubdivision G r :=
  h.map CliqueSubdivision.ofErdos718

@[simp]
theorem walkInteriorSet_mapLe {V : Type*} {G H : SimpleGraph V} (h : G ≤ H)
    {u v : V} (p : G.Walk u v) :
    walkInteriorSet (p.mapLe h) = walkInteriorSet p := by
  ext x
  simp only [walkInteriorSet, Set.mem_ofPred_eq, Walk.support_mapLe_eq_support]

/-- A subdivision remains a subdivision after graph edges are added. -/
def CliqueSubdivision.mapLe {V : Type*} {G H : SimpleGraph V} {r : ℕ}
    (s : CliqueSubdivision G r) (h : G ≤ H) : CliqueSubdivision H r where
  branch := s.branch
  path e := (s.path e).mapLe h
  path_isPath e := (s.path_isPath e).mapLe h
  interior_avoids_branch e := by
    simpa only [walkInteriorSet_mapLe] using s.interior_avoids_branch e
  interior_pairwise e f hef := by
    simpa only [walkInteriorSet_mapLe] using s.interior_pairwise hef

theorem ContainsCliqueSubdivision.mono {V : Type*} {G H : SimpleGraph V} {r : ℕ}
    (hG : ContainsCliqueSubdivision G r) (h : G ≤ H) :
    ContainsCliqueSubdivision H r := by
  exact hG.map fun s => s.mapLe h

/-- The inclusion of clique edges induced by `Fin r ↪ Fin s`. -/
def cliqueEdgeCastLE {r s : ℕ} (h : r ≤ s) : CliqueEdge r ↪ CliqueEdge s where
  toFun e := ⟨(Fin.castLE h e.1.1, Fin.castLE h e.1.2), by
    simpa only [Fin.castLE_lt_castLE_iff] using e.2⟩
  inj' := by
    intro e f hef
    apply Subtype.ext
    apply Prod.ext
    · exact (Fin.castLE_injective h)
        (congrArg (fun x => x.1) (congrArg Subtype.val hef))
    · exact (Fin.castLE_injective h)
        (congrArg (fun x => x.2) (congrArg Subtype.val hef))

/-- Restrict the branch set of a clique subdivision. -/
def CliqueSubdivision.restrict {V : Type*} {G : SimpleGraph V} {r s : ℕ}
    (S : CliqueSubdivision G s) (h : r ≤ s) : CliqueSubdivision G r where
  branch := (Fin.castLEEmb h).trans S.branch
  path e := S.path (cliqueEdgeCastLE h e)
  path_isPath e := S.path_isPath (cliqueEdgeCastLE h e)
  interior_avoids_branch e := by
    apply Set.disjoint_of_subset_right
    · show Set.range ((Fin.castLEEmb h).trans S.branch) ⊆ Set.range S.branch
      rintro x ⟨i, rfl⟩
      exact ⟨Fin.castLE h i, by rfl⟩
    exact S.interior_avoids_branch (cliqueEdgeCastLE h e)
  interior_pairwise e f hef := by
    exact S.interior_pairwise (fun hmap => hef ((cliqueEdgeCastLE h).injective hmap))

theorem ContainsCliqueSubdivision.antitone_order {V : Type*} {G : SimpleGraph V}
    {r s : ℕ} (hS : ContainsCliqueSubdivision G s) (h : r ≤ s) :
    ContainsCliqueSubdivision G r := by
  exact hS.map fun S => S.restrict h

private def induceInclusion {V : Type*} {G : SimpleGraph V} (S : Set V) :
    G.induce S →g G where
  toFun := Subtype.val
  map_rel' := by
    intro u v huv
    exact huv

/-- A clique subdivision in an induced graph is also one in the host graph. -/
def CliqueSubdivision.liftInduce {V : Type*} {G : SimpleGraph V}
    {S : Set V} {r : ℕ} (s : CliqueSubdivision (G.induce S) r) :
    CliqueSubdivision G r := by
  let inclusion : G.induce S →g G := induceInclusion S
  let valueEmbedding : S ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
  let branch : Fin r ↪ V := s.branch.trans valueEmbedding
  let mappedPath (e : CliqueEdge r) := (s.path e).map inclusion
  have branch_apply (i : Fin r) : branch i = (s.branch i : V) := by
    rfl
  have path_preimage (e : CliqueEdge r) {x : V}
      (hx : x ∈ walkInteriorSet (mappedPath e)) :
      ∃ y ∈ walkInteriorSet (s.path e), (y : V) = x := by
    rcases hx with ⟨hxsupp, hxstart, hxend⟩
    rw [SimpleGraph.Walk.support_map] at hxsupp
    obtain ⟨y, hysupp, hyx⟩ := List.mem_map.mp hxsupp
    have hyx' : (y : V) = x := by
      change (y : V) = x at hyx
      exact hyx
    refine ⟨y, ⟨hysupp, ?_, ?_⟩, hyx'⟩
    · intro hy
      subst y
      apply hxstart
      change x = (s.branch e.1.1 : V)
      exact hyx'.symm
    · intro hy
      subst y
      apply hxend
      change x = (s.branch e.1.2 : V)
      exact hyx'.symm
  refine {
    branch := branch
    path := mappedPath
    path_isPath := fun e => (s.path_isPath e).map Subtype.val_injective
    interior_avoids_branch := ?_
    interior_pairwise := ?_
  }
  · intro e
    rw [Set.disjoint_left]
    intro x hx hxbranch
    obtain ⟨y, hy, hyx⟩ := path_preimage e hx
    obtain ⟨i, hix⟩ := hxbranch
    have hybranch : y = s.branch i := by
      apply Subtype.ext
      rw [hyx, ← hix]
      exact branch_apply i
    exact (Set.disjoint_left.mp (s.interior_avoids_branch e)) hy
      ⟨i, hybranch.symm⟩
  · intro e e' hee'
    rw [Set.disjoint_left]
    intro x hxe hxe'
    obtain ⟨y, hye, hyx⟩ := path_preimage e hxe
    obtain ⟨y', hye', hy'x⟩ := path_preimage e' hxe'
    have hyy' : y = y' := Subtype.ext (hyx.trans hy'x.symm)
    subst y'
    exact (Set.disjoint_left.mp (s.interior_pairwise hee')) hye hye'

theorem ContainsCliqueSubdivision.liftInduce {V : Type*} {G : SimpleGraph V}
    {S : Set V} {r : ℕ}
    (hS : ContainsCliqueSubdivision (G.induce S) r) :
    ContainsCliqueSubdivision G r :=
  hS.map CliqueSubdivision.liftInduce

theorem containsCliqueSubdivision_zero {V : Type*} (G : SimpleGraph V) :
    ContainsCliqueSubdivision G 0 := by
  refine ⟨{
    branch := Function.Embedding.ofIsEmpty
    path := fun e => Fin.elim0 e.1.1
    path_isPath := fun e => Fin.elim0 e.1.1
    interior_avoids_branch := fun e => Fin.elim0 e.1.1
    interior_pairwise := fun e => Fin.elim0 e.1.1
  }⟩

private theorem CliqueEdge.one_isEmpty (e : CliqueEdge 1) : False := by
  omega

theorem containsCliqueSubdivision_one {V : Type*} (G : SimpleGraph V) (v : V) :
    ContainsCliqueSubdivision G 1 := by
  let branch : Fin 1 ↪ V :=
    ⟨fun _ => v, fun a b _ => Subsingleton.elim a b⟩
  refine ⟨{
    branch := branch
    path := fun e => (CliqueEdge.one_isEmpty e).elim
    path_isPath := fun e => (CliqueEdge.one_isEmpty e).elim
    interior_avoids_branch := fun e => (CliqueEdge.one_isEmpty e).elim
    interior_pairwise := fun e => (CliqueEdge.one_isEmpty e).elim
  }⟩

theorem containsCliqueSubdivision_one_of_nonempty {V : Type*} [Nonempty V]
    (G : SimpleGraph V) : ContainsCliqueSubdivision G 1 := by
  exact containsCliqueSubdivision_one G (Classical.choice inferInstance)

theorem card_le_of_containsCliqueSubdivision {V : Type*} [Fintype V]
    {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r) :
    r ≤ Fintype.card V := by
  obtain ⟨S⟩ := h
  simpa using Fintype.card_le_of_injective S.branch S.branch.injective

/-! ### The maximum order `σ(G)` -/

/-- The largest `r` for which `G` contains a subdivision of `K_r`. -/
noncomputable def cliqueSubdivisionNumber {V : Type*} [Fintype V]
    (G : SimpleGraph V) : ℕ := by
  classical
  exact Nat.findGreatest (ContainsCliqueSubdivision G) (Fintype.card V)

theorem cliqueSubdivisionNumber_le_card {V : Type*} [Fintype V]
    (G : SimpleGraph V) : cliqueSubdivisionNumber G ≤ Fintype.card V := by
  classical
  exact Nat.findGreatest_le _

theorem le_cliqueSubdivisionNumber {V : Type*} [Fintype V]
    {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r) :
    r ≤ cliqueSubdivisionNumber G := by
  classical
  exact Nat.le_findGreatest (card_le_of_containsCliqueSubdivision h) h

theorem containsCliqueSubdivision_cliqueSubdivisionNumber {V : Type*} [Fintype V]
    (G : SimpleGraph V) :
    ContainsCliqueSubdivision G (cliqueSubdivisionNumber G) := by
  classical
  exact Nat.findGreatest_spec (m := 0) (Nat.zero_le _)
    (containsCliqueSubdivision_zero G)

theorem containsCliqueSubdivision_iff_le {V : Type*} [Fintype V]
    {G : SimpleGraph V} {r : ℕ} :
    ContainsCliqueSubdivision G r ↔ r ≤ cliqueSubdivisionNumber G := by
  constructor
  · exact le_cliqueSubdivisionNumber
  · intro h
    exact (containsCliqueSubdivision_cliqueSubdivisionNumber G).antitone_order h

theorem one_le_cliqueSubdivisionNumber {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) : 1 ≤ cliqueSubdivisionNumber G := by
  exact le_cliqueSubdivisionNumber (containsCliqueSubdivision_one_of_nonempty G)

theorem cliqueSubdivisionNumber_mono {V : Type*} [Fintype V]
    {G H : SimpleGraph V} (h : G ≤ H) :
    cliqueSubdivisionNumber G ≤ cliqueSubdivisionNumber H := by
  exact le_cliqueSubdivisionNumber
    ((containsCliqueSubdivision_cliqueSubdivisionNumber G).mono h)

/-- The proved topological-density estimate, expressed in terms of the
public subdivision number of this file. -/
theorem le_cliqueSubdivisionNumber_of_five_mul_sq_mul_card_le_edges
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ)
    (hV : 0 < Fintype.card V)
    (hE : 5 * (r * r) * Fintype.card V ≤ G.edgeFinset.card) :
    r ≤ cliqueSubdivisionNumber G := by
  apply le_cliqueSubdivisionNumber
  apply ContainsCliqueSubdivision.ofErdos718
  exact Erdos717.ThomasWollanMassed.containsCliqueSubdivision_of_five_mul_sq_mul_card_le_edges
    G r hV hE

/-! ### The exact public statement -/

/-- The ordinary natural-valued chromatic number of a finite graph. -/
noncomputable def chiNat {V : Type*} (G : SimpleGraph V) : ℕ :=
  G.chromaticNumber.toNat

theorem chiNat_le_of_colorable {V : Type*} {G : SimpleGraph V} {m : ℕ}
    (h : G.Colorable m) : chiNat G ≤ m := by
  unfold chiNat
  exact ENat.toNat_le_toNat h.chromaticNumber_le (by simp)

theorem chiNat_le_card {V : Type*} [Fintype V] (G : SimpleGraph V) :
    chiNat G ≤ Fintype.card V := by
  exact chiNat_le_of_colorable G.colorable_of_fintype

theorem indepNum_le_card {V : Type*} [Fintype V] (G : SimpleGraph V) :
    G.indepNum ≤ Fintype.card V := by
  obtain ⟨I, hI⟩ := G.maximumIndepSet_exists
  rw [← G.maximumIndepSet_card_eq_indepNum I hI]
  exact Finset.card_le_univ I

/-- Extend a coloring of the complement of an independent finset by one
fresh color on that finset. -/
noncomputable def coloringOfInduceComplement {V : Type*} [Fintype V]
    (G : SimpleGraph V) (I : Finset V) (hI : G.IsIndepSet I) (m : ℕ)
    (C : (G.induce {v : V | v ∉ I}).Coloring (Fin m)) :
    G.Coloring (Fin (m + 1)) := by
  classical
  refine SimpleGraph.Coloring.mk
    (fun v => if hv : v ∈ I then Fin.last m else Fin.castSucc (C ⟨v, hv⟩)) ?_
  intro u v huv
  by_cases hu : u ∈ I
  · by_cases hv : v ∈ I
    · exact (hI hu hv huv.ne huv).elim
    · simp only [hu, hv, ↓reduceDIte]
      exact (Fin.castSucc_ne_last _).symm
  · by_cases hv : v ∈ I
    · simp only [hu, hv, ↓reduceDIte]
      exact Fin.castSucc_ne_last _
    · simp only [hu, hv, ↓reduceDIte]
      intro heq
      have hinduced :
          (G.induce {x : V | x ∉ I}).Adj (⟨u, hu⟩ : {x : V | x ∉ I})
            (⟨v, hv⟩ : {x : V | x ∉ I}) := huv
      exact (C.valid hinduced) (Fin.castSucc_injective m heq)

theorem chiNat_le_induce_complement_add_one {V : Type*} [Fintype V]
    (G : SimpleGraph V) (I : Finset V) (hI : G.IsIndepSet I) :
    chiNat G ≤ chiNat (G.induce {v : V | v ∉ I}) + 1 := by
  let H := G.induce {v : V | v ∉ I}
  have hcolor : H.Colorable (chiNat H) := by
    exact SimpleGraph.colorable_chromaticNumber_of_fintype H
  obtain ⟨C⟩ := hcolor
  apply chiNat_le_of_colorable
  exact ⟨coloringOfInduceComplement G I hI (chiNat H) C⟩

/-- Subdivision number cannot increase on passing to an induced graph. -/
theorem cliqueSubdivisionNumber_induce_le {V : Type*} [Fintype V]
    (G : SimpleGraph V) (S : Set V) [Fintype S] :
    cliqueSubdivisionNumber (G.induce S) ≤ cliqueSubdivisionNumber G := by
  classical
  apply le_cliqueSubdivisionNumber
  exact (containsCliqueSubdivision_cliqueSubdivisionNumber (G.induce S)).liftInduce

/-- Erdős Problem 717, in an exact uniform-constant formulation. -/
def Erdos717Bound : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      2 ≤ Fintype.card V →
      (chiNat G : ℝ) ≤
        C * (Real.sqrt (Fintype.card V : ℝ) / Real.log (Fintype.card V : ℝ)) *
          (cliqueSubdivisionNumber G : ℝ)

/-- Weighted form of the Fox--Lee--Sudakov theorem. -/
theorem erdos717_weight_bound
    (V : Type) [Fintype V] (G : SimpleGraph V) :
    chromaticWeight (Fintype.card V) (chiNat G) ≤
      erdos717Constant * cliqueSubdivisionNumber G := by
  classical
  let P : ℕ → Prop := fun n =>
    ∀ (W : Type) [Fintype W] (J : SimpleGraph W),
      Fintype.card W = n →
      chromaticWeight (Fintype.card W) (chiNat J) ≤
        erdos717Constant * cliqueSubdivisionNumber J
  have hmain : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      dsimp only [P]
      intro W _ J hnCard
      letI : DecidableEq W := Classical.decEq W
      letI : DecidableRel J.Adj := Classical.decRel J.Adj
      let c := chiNat J
      let a := J.indepNum
      let s := cliqueSubdivisionNumber J
      change chromaticWeight (Fintype.card W) c ≤
        erdos717Constant * (s : ℝ)
      by_cases hn0 : n = 0
      · have hcard : Fintype.card W = 0 := hnCard.trans hn0
        have hc0 : c = 0 := by
          have := chiNat_le_card J
          dsimp only [c]
          rw [hcard] at this
          omega
        rw [hc0, hcard]
        simp only [chromaticWeight, Nat.cast_zero, zero_mul, Real.sqrt_zero,
          zero_div]
        exact mul_nonneg erdos717Constant_pos.le (by positivity)
      have hn : 0 < n := Nat.pos_of_ne_zero hn0
      have hnW : 0 < Fintype.card W := by simpa only [hnCard] using hn
      letI : Nonempty W := Fintype.card_pos_iff.mp hnW
      have hs : 1 ≤ s := by
        dsimp only [s]
        exact one_le_cliqueSubdivisionNumber J
      have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs
      have hCnonneg : 0 ≤ erdos717Constant := erdos717Constant_pos.le
      have hCs : erdos717Constant ≤ erdos717Constant * (s : ℝ) := by
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_left hsR hCnonneg
      by_cases hcSmall : c ≤ 200
      · calc
          chromaticWeight (Fintype.card W) c ≤ 2 * (c : ℝ) :=
            chromaticWeight_le_two_mul _ _ hnW
          _ ≤ 400 := by exact_mod_cast (Nat.mul_le_mul_left 2 hcSmall)
          _ ≤ erdos717Constant := by
            calc
              (400 : ℝ) ≤ (10 : ℝ) ^ (200 : ℕ) := by norm_num
              _ ≤ erdos717Constant := by
                simp only [erdos717Constant]
                exact le_add_of_nonneg_right (by positivity)
          _ ≤ erdos717Constant * s := hCs
      have hcLarge : 201 ≤ c := by omega
      have hc : 0 < c := by omega
      have ha : 0 < a := by
        let v : W := Classical.choice inferInstance
        have hsingle : J.IsIndepSet ({v} : Finset W) := by simp
        have := hsingle.card_le_indepNum
        simpa only [a] using (lt_of_lt_of_le (by norm_num : 0 < 1) this)
      by_cases hnSmall : n < 10 ^ 100
      · have hcCard : c ≤ n := by
          dsimp only [c]
          rw [← hnCard]
          exact chiNat_le_card J
        have hlt : chromaticWeight (Fintype.card W) c <
            erdos717Constant * (s : ℝ) := by
          calc
            chromaticWeight (Fintype.card W) c ≤ 2 * (c : ℝ) :=
              chromaticWeight_le_two_mul _ _ hnW
            _ < (10 : ℝ) ^ (200 : ℕ) := by
              have hcBound : c < 10 ^ 100 := hcCard.trans_lt hnSmall
              have hNat : 2 * c < 10 ^ 200 := by
                have htwo : 2 * c < 2 * 10 ^ 100 := by omega
                have hnum : 2 * 10 ^ 100 < 10 ^ 200 := by norm_num
                omega
              exact_mod_cast hNat
            _ ≤ erdos717Constant := by
              simp only [erdos717Constant]
              exact le_add_of_nonneg_right (by positivity)
            _ ≤ erdos717Constant * s := hCs
        exact hlt.le
      have hnHuge : 10 ^ 100 ≤ n := by omega
      by_cases hactive : (c : ℝ) * a < 100 * n
      · have hactiveNat : c * a < 100 * n := by exact_mod_cast hactive
        have haHalf : 2 * a ≤ n := by
          have h201 : 201 * a ≤ c * a := Nat.mul_le_mul_right a hcLarge
          by_contra hnotHalf
          have hnlt : n < 2 * a := by omega
          have : 100 * n < 200 * a := by omega
          omega
        have hnot : ¬Erdos718.ContainsCliqueSubdivision J (s + 1) := by
          intro hsub
          have hpublic : ContainsCliqueSubdivision J (s + 1) :=
            ContainsCliqueSubdivision.ofErdos718 hsub
          have hle := le_cliqueSubdivisionNumber hpublic
          dsimp only [s] at hle
          omega
        have hbound := active_graph_weight_lt_forbidden_order J a c (s + 1)
          (by exact le_rfl)
          (by simpa only [hnCard] using hnHuge)
          (by simpa only [hnCard] using haHalf) ha hc
          (by simpa only [hnCard] using hactive)
          (by omega) hnot
        have hrhs : (((s + 1 : ℕ) : ℝ) - 1) = (s : ℝ) := by
          norm_num
        rw [hrhs] at hbound
        exact hbound.le
      · have hlargeR : (100 : ℝ) * n ≤ c * a := le_of_not_gt hactive
        have hlarge : 100 * n ≤ a * c := by
          have hlargeNat : 100 * n ≤ c * a := by exact_mod_cast hlargeR
          simpa only [mul_comm] using hlargeNat
        obtain ⟨I, hImax⟩ := J.maximumIndepSet_exists
        have hIcard : I.card = a := by
          simpa only [a] using J.maximumIndepSet_card_eq_indepNum I hImax
        let H := J.induce {v : W | v ∉ I}
        let n' := Fintype.card {v : W | v ∉ I}
        let c' := chiNat H
        have hn'Card : Fintype.card {v : W | v ∉ I} = n' := rfl
        have hn'Eq : n' + a = n := by
          have hIle : I.card ≤ Fintype.card W := Finset.card_le_univ I
          dsimp only [n']
          have hcompl : Fintype.card {v : W // v ∉ I} =
              Fintype.card W - I.card := by
            simpa using (Fintype.card_subtype_compl (fun v : W => v ∈ I))
          let e : (↑{v : W | v ∉ I}) ≃ {v : W // v ∉ I} :=
            { toFun := fun v => ⟨v.1, v.2⟩
              invFun := fun v => ⟨v.1, v.2⟩
              left_inv := fun v => by cases v; rfl
              right_inv := fun v => by cases v; rfl }
          have htypeCard : Fintype.card ↑{v : W | v ∉ I} =
              Fintype.card {v : W // v ∉ I} := Fintype.card_congr e
          calc
            Fintype.card ↑{v : W | v ∉ I} + a =
                Fintype.card {v : W // v ∉ I} + a := by rw [htypeCard]
            _ = (Fintype.card W - I.card) + a := by rw [hcompl]
            _ = (Fintype.card W - I.card) + I.card := by rw [hIcard]
            _ = Fintype.card W := Nat.sub_add_cancel hIle
            _ = n := hnCard
        have hchi : c ≤ c' + 1 := by
          simpa only [c, c', H] using
            chiNat_le_induce_complement_add_one J I hImax.isIndepSet
        have hc'Card : c' ≤ n' := by
          dsimp only [c', H, n']
          exact chiNat_le_card _
        have hn' : 0 < n' := by
          by_contra hzero
          have : n' = 0 := Nat.eq_zero_of_not_pos hzero
          omega
        have hn'Lt : n' < n := by omega
        have hn'Large : 100 ≤ n' := by
          by_contra hsmall
          have : n' < 100 := by omega
          omega
        have hscale : (c : ℝ) / fourthRoot n ≤
            (c' : ℝ) / fourthRoot n' :=
          chromaticScale_le_after_deletion n n' a c c' hn hn'
            (by omega) hn'Eq hchi hlarge
        have hfactor : Real.log (n : ℝ) / fourthRoot n ≤
            Real.log (n' : ℝ) / fourthRoot n' := by
          apply log_div_fourthRoot_antitone
          · exact exp_four_lt_hundred.le.trans (by exact_mod_cast hn'Large)
          · exact_mod_cast (show n' ≤ n by omega)
        have hweightMono : chromaticWeight n c ≤ chromaticWeight n' c' := by
          rw [chromaticWeight_eq_fourthRoot_factors n c hn,
            chromaticWeight_eq_fourthRoot_factors n' c' hn']
          have hlogNonneg : 0 ≤ Real.log (n : ℝ) := by
            apply Real.log_nonneg
            exact_mod_cast (show 1 ≤ n by omega)
          exact mul_le_mul hscale hfactor
            (div_nonneg hlogNonneg (fourthRoot_pos (by exact_mod_cast hn)).le)
            (div_nonneg (by positivity)
              (fourthRoot_pos (by exact_mod_cast hn')).le)
        have hrec := ih n' hn'Lt {v : W | v ∉ I} H rfl
        have hsigma : cliqueSubdivisionNumber H ≤ s := by
          dsimp only [H, s]
          exact cliqueSubdivisionNumber_induce_le J {v : W | v ∉ I}
        calc
          chromaticWeight (Fintype.card W) c = chromaticWeight n c := by rw [hnCard]
          _ ≤ chromaticWeight n' c' := hweightMono
          _ ≤ erdos717Constant * cliqueSubdivisionNumber H := by
            simpa only [H, c', n'] using hrec
          _ ≤ erdos717Constant * s :=
            mul_le_mul_of_nonneg_left (by exact_mod_cast hsigma) hCnonneg
  exact hmain (Fintype.card V) V G rfl

/-- Erdős Problem 717 has an affirmative answer. -/
theorem erdos_717 : Erdos717Bound := by
  refine ⟨erdos717Constant, erdos717Constant_pos, ?_⟩
  intro V _ G hn
  have hnPos : 0 < Fintype.card V := by omega
  have hnR : (0 : ℝ) < Fintype.card V := by exact_mod_cast hnPos
  have hsqrt : 0 < Real.sqrt (Fintype.card V : ℝ) := Real.sqrt_pos.2 hnR
  have hlog : 0 < Real.log (Fintype.card V : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < Fintype.card V by omega))
  have hweight := erdos717_weight_bound V G
  rw [chromaticWeight] at hweight
  rw [div_le_iff₀ hsqrt] at hweight
  rw [show erdos717Constant *
      (Real.sqrt (Fintype.card V : ℝ) / Real.log (Fintype.card V : ℝ)) *
        (cliqueSubdivisionNumber G : ℝ) =
      (erdos717Constant * (cliqueSubdivisionNumber G : ℝ) *
        Real.sqrt (Fintype.card V : ℝ)) /
          Real.log (Fintype.card V : ℝ) by ring]
  rw [le_div_iff₀ hlog]
  nlinarith

#print axioms Erdos717.erdos_717

end Erdos717
