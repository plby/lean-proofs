/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Erdős Problem 133.

For an n-vertex triangle-free graph of diameter at most two, minimize the
maximum degree.  We prove that this function is Θ(√n), and in particular its
ratio to √n does not tend to infinity.

The lower bound is the diameter-two Moore bound.  The upper bound uses an
explicit graph on pairs of elements of a finite set with a fixed-point-free
involution, followed by a controlled vertex duplication.
-/

import Mathlib

set_option linter.style.setOption false
set_option linter.flexible false

attribute [local instance] Classical.propDecidable

open Filter

namespace Erdos133

/-- The combinatorial form of having diameter at most two. -/
def HasDiameterTwo {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ x y, x ≠ y → G.Adj x y ∨ ∃ z, G.Adj x z ∧ G.Adj z y

/-- A finite witness used in the definition of the extremal function. -/
structure Model (n d : ℕ) where
  V : Type
  [fintypeV : Fintype V]
  G : SimpleGraph V
  card_eq : Fintype.card V = n
  triangleFree : G.CliqueFree 3
  diameterTwo : HasDiameterTwo G
  degree_le : ∀ v, G.degree v ≤ d

/-- The smallest possible maximum degree of an `n`-vertex triangle-free
diameter-two graph.  This is the standard meaning of the function in
Problem 133. -/
noncomputable def erdos133Function (n : ℕ) : ℕ :=
  sInf {d : ℕ | Nonempty (Model n d)}

/-! ## The Moore lower bound -/

/-- A graph of maximum degree `d` and diameter at most two has at most
`d^2 + 1` vertices. -/
theorem moore_bound {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (d : ℕ) (hdiam : HasDiameterTwo G)
    (hdeg : ∀ v, G.degree v ≤ d) :
    Fintype.card V ≤ d * d + 1 := by
  classical
  let v : V := Classical.choice ‹Nonempty V›
  let N : Finset V := G.neighborFinset v
  let B : Finset V := N.biUnion fun u => (G.neighborFinset u).erase v
  have hcover : Finset.univ ⊆ insert v (N ∪ B) := by
    intro w hw
    by_cases hwv : w = v
    · simp [hwv]
    · rw [Finset.mem_insert, Finset.mem_union]
      right
      rcases hdiam v w (Ne.symm hwv) with hvw | ⟨u, hvu, huw⟩
      · left
        exact (SimpleGraph.mem_neighborFinset G v w).2 hvw
      · right
        rw [Finset.mem_biUnion]
        refine ⟨u, (SimpleGraph.mem_neighborFinset G v u).2 hvu, ?_⟩
        rw [Finset.mem_erase]
        exact ⟨hwv, (SimpleGraph.mem_neighborFinset G u w).2 huw⟩
  have hN : N.card ≤ d := by
    simpa [N, SimpleGraph.card_neighborFinset_eq_degree] using hdeg v
  have herase : ∀ u ∈ N, ((G.neighborFinset u).erase v).card ≤ d - 1 := by
    intro u hu
    have hvu : G.Adj v u := (SimpleGraph.mem_neighborFinset G v u).1 (by simpa [N] using hu)
    have hvmem : v ∈ G.neighborFinset u :=
      (SimpleGraph.mem_neighborFinset G u v).2 hvu.symm
    rw [Finset.card_erase_of_mem hvmem,
      SimpleGraph.card_neighborFinset_eq_degree]
    exact Nat.sub_le_sub_right (hdeg u) 1
  have hB : B.card ≤ N.card * (d - 1) := by
    calc
      B.card ≤ ∑ u ∈ N, ((G.neighborFinset u).erase v).card := by
        exact Finset.card_biUnion_le
      _ ≤ ∑ _u ∈ N, (d - 1) := Finset.sum_le_sum herase
      _ = N.card * (d - 1) := by simp
  have hB' : B.card ≤ d * (d - 1) :=
    hB.trans (Nat.mul_le_mul_right (d - 1) hN)
  have hraw : Fintype.card V ≤ 1 + d + d * (d - 1) := by
    calc
      Fintype.card V = Finset.univ.card := by simp
      _ ≤ (insert v (N ∪ B)).card := Finset.card_le_card hcover
      _ ≤ (N ∪ B).card + 1 := Finset.card_insert_le _ _
      _ ≤ N.card + B.card + 1 := Nat.add_le_add_right (Finset.card_union_le N B) 1
      _ ≤ 1 + d + d * (d - 1) := by omega
  by_cases hd0 : d = 0
  · subst d
    simpa using hraw
  · have hd1 : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr hd0
    have hsub : d - 1 + 1 = d := Nat.sub_add_cancel hd1
    nlinarith

lemma erdos133Function_mem {n : ℕ}
    (h : ∃ d, Nonempty (Model n d)) :
    Nonempty (Model n (erdos133Function n)) := by
  exact Nat.sInf_mem h

lemma erdos133Function_le {n d : ℕ} (h : Nonempty (Model n d)) :
    erdos133Function n ≤ d := by
  exact Nat.sInf_le h

/-! ## The fixed-point-free involution construction -/

abbrev Block (k : ℕ) := Bool × Fin k

/-- Flip the Boolean coordinate and leave the finite coordinate unchanged. -/
def flip {k : ℕ} : Block k → Block k
  | (b, i) => (!b, i)

@[simp] lemma flip_fst {k : ℕ} (x : Block k) : (flip x).1 = !x.1 := by
  cases x
  rfl

@[simp] lemma flip_snd {k : ℕ} (x : Block k) : (flip x).2 = x.2 := by
  cases x
  rfl

@[simp] lemma flip_flip {k : ℕ} (x : Block k) : flip (flip x) = x := by
  cases x with
  | mk b i => cases b <;> rfl

@[simp] lemma flip_ne {k : ℕ} (x : Block k) : flip x ≠ x := by
  cases x with
  | mk b i => cases b <;> simp [flip]

@[simp] lemma ne_flip {k : ℕ} (x : Block k) : x ≠ flip x := by
  exact (flip_ne x).symm

lemma flip_injective {k : ℕ} : Function.Injective (@flip k) := by
  intro x y h
  rw [← flip_flip x, ← flip_flip y, h]

/-- Adjacency in the square-order construction.  An edge flips one
coordinate and changes the other coordinate. -/
def BaseAdj (k : ℕ) (x y : Block k × Block k) : Prop :=
  (y.1 = flip x.1 ∧ y.2 ≠ x.2) ∨
  (y.2 = flip x.2 ∧ y.1 ≠ x.1)

lemma baseAdj_symm (k : ℕ) : Std.Symm (BaseAdj k) := by
  constructor
  intro x y h
  rcases h with h | h
  · left
    constructor
    · simpa [h.1] using (flip_flip x.1).symm
    · exact h.2.symm
  · right
    constructor
    · simpa [h.1] using (flip_flip x.2).symm
    · exact h.2.symm

lemma baseAdj_loopless (k : ℕ) : Std.Irrefl (BaseAdj k) := by
  constructor
  intro x h
  rcases h with h | h
  · exact flip_ne x.1 h.1.symm
  · exact flip_ne x.2 h.1.symm

/-- The explicit triangle-free diameter-two graph on `(2k)^2` vertices. -/
def baseGraph (k : ℕ) : SimpleGraph (Block k × Block k) :=
  SimpleGraph.mk (BaseAdj k) (baseAdj_symm k) (baseAdj_loopless k)

@[simp] lemma baseGraph_adj {k : ℕ} {x y : Block k × Block k} :
    (baseGraph k).Adj x y ↔
      (y.1 = flip x.1 ∧ y.2 ≠ x.2) ∨
      (y.2 = flip x.2 ∧ y.1 ≠ x.1) := by
  rfl

lemma baseGraph_no_triangle {k : ℕ} {x y z : Block k × Block k}
    (hxy : (baseGraph k).Adj x y) (hyz : (baseGraph k).Adj y z)
    (hxz : (baseGraph k).Adj x z) : False := by
  simp only [baseGraph_adj] at hxy hyz hxz
  rcases hxy with hxy | hxy <;>
    rcases hyz with hyz | hyz <;>
      rcases hxz with hxz | hxz
  all_goals simp_all
  all_goals exact hxy.2 (flip_injective hyz.1.symm)

theorem baseGraph_triangleFree (k : ℕ) : (baseGraph k).CliqueFree 3 := by
  intro s hs
  rw [SimpleGraph.is3Clique_iff] at hs
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := hs
  exact baseGraph_no_triangle hxy hyz hxz

/-- A different index, available once `Fin k` has at least two elements. -/
def otherIndex {k : ℕ} (hk : 2 ≤ k) (i : Fin k) : Fin k :=
  if hi : i.val = 0 then ⟨1, by omega⟩ else ⟨0, by omega⟩

lemma otherIndex_ne {k : ℕ} (hk : 2 ≤ k) (i : Fin k) : otherIndex hk i ≠ i := by
  intro h
  by_cases hi : i.val = 0
  · have := congrArg Fin.val h
    simp [otherIndex, hi] at this
  · have := congrArg Fin.val h
    simp [otherIndex, hi] at this
    exact hi this.symm

/-- A point outside the two-element orbit `{x, flip x}`. -/
def spareBlock {k : ℕ} (hk : 2 ≤ k) (x : Block k) : Block k :=
  (x.1, otherIndex hk x.2)

lemma spareBlock_ne_left {k : ℕ} (hk : 2 ≤ k) (x : Block k) :
    spareBlock hk x ≠ x := by
  intro h
  exact otherIndex_ne hk x.2 (congrArg Prod.snd h)

lemma spareBlock_ne_flip {k : ℕ} (hk : 2 ≤ k) (x : Block k) :
    spareBlock hk x ≠ flip x := by
  intro h
  have hfst := congrArg Prod.fst h
  cases x with
  | mk b i => cases b <;> simp [spareBlock, flip] at hfst

theorem baseGraph_diameterTwo {k : ℕ} (hk : 2 ≤ k) :
    HasDiameterTwo (baseGraph k) := by
  intro x y hxy
  by_cases h₁ : y.1 = flip x.1
  · by_cases h₂ : y.2 = flip x.2
    · left
      exact baseGraph_adj.mpr (Or.inl ⟨h₁, by simpa [h₂] using flip_ne x.2⟩)
    · by_cases heq : x.2 = y.2
      · let t := spareBlock hk x.1
        refine Or.inr ⟨(t, flip x.2), ?_, ?_⟩
        · exact baseGraph_adj.mpr (Or.inr
            ⟨rfl, spareBlock_ne_left hk x.1⟩)
        · apply baseGraph_adj.mpr
          right
          constructor
          · simpa [heq] using (flip_flip x.2).symm
          · intro h
            exact spareBlock_ne_flip hk x.1 (h.symm.trans h₁)
      · left
        exact baseGraph_adj.mpr (Or.inl ⟨h₁, Ne.symm heq⟩)
  · by_cases h₂ : y.2 = flip x.2
    · by_cases heq : x.1 = y.1
      · let t := spareBlock hk x.2
        refine Or.inr ⟨(flip x.1, t), ?_, ?_⟩
        · exact baseGraph_adj.mpr (Or.inl
            ⟨rfl, spareBlock_ne_left hk x.2⟩)
        · apply baseGraph_adj.mpr
          left
          constructor
          · simpa [heq] using (flip_flip x.1).symm
          · intro h
            exact spareBlock_ne_flip hk x.2 (h.symm.trans h₂)
      · left
        exact baseGraph_adj.mpr (Or.inr ⟨h₂, Ne.symm heq⟩)
    · refine Or.inr ⟨(flip x.1, flip y.2), ?_, ?_⟩
      · apply baseGraph_adj.mpr
        left
        refine ⟨rfl, ?_⟩
        intro heq
        apply h₂
        calc
          y.2 = flip (flip y.2) := (flip_flip y.2).symm
          _ = flip x.2 := congrArg flip heq
      · apply baseGraph_adj.mpr
        right
        refine ⟨(flip_flip y.2).symm, h₁⟩

lemma baseGraph_has_neighbor {k : ℕ} (x : Block k × Block k) :
    ∃ y, (baseGraph k).Adj x y := by
  refine ⟨(flip x.1, flip x.2), ?_⟩
  apply baseGraph_adj.mpr
  left
  exact ⟨rfl, flip_ne x.2⟩

theorem baseGraph_degree_le (k : ℕ) (x : Block k × Block k) :
    (baseGraph k).degree x ≤ 4 * k := by
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  let A : Finset (Block k × Block k) :=
    ({flip x.1} : Finset (Block k)) ×ˢ Finset.univ
  let B : Finset (Block k × Block k) :=
    Finset.univ ×ˢ ({flip x.2} : Finset (Block k))
  calc
    ((baseGraph k).neighborFinset x).card ≤ (A ∪ B).card := by
      apply Finset.card_le_card
      intro y hy
      rw [SimpleGraph.mem_neighborFinset] at hy
      rcases baseGraph_adj.mp hy with hy | hy
      · rw [Finset.mem_union]
        left
        simp only [A, Finset.mem_product, Finset.mem_singleton,
          Finset.mem_univ, and_true]
        exact hy.1
      · rw [Finset.mem_union]
        right
        simp only [B, Finset.mem_product, Finset.mem_singleton,
          Finset.mem_univ, true_and]
        exact hy.1
    _ ≤ A.card + B.card := Finset.card_union_le A B
    _ = 4 * k := by simp [A, B]; omega

/-! ## A controlled vertex duplication -/

/-- Projection from a base copy together with one injectively indexed set of
duplicates. -/
def blowupProjection {X : Type*} {r : ℕ} (e : Fin r ↪ X) : X ⊕ Fin r → X
  | Sum.inl x => x
  | Sum.inr i => e i

/-- Pull back a graph along `blowupProjection`.  Every base vertex has one or
two preimages. -/
def blowupGraph {X : Type*} {r : ℕ} (H : SimpleGraph X) (e : Fin r ↪ X) :
    SimpleGraph (X ⊕ Fin r) :=
  H.comap (blowupProjection e)

@[simp] lemma blowupGraph_adj {X : Type*} {r : ℕ} {H : SimpleGraph X}
    {e : Fin r ↪ X} {x y : X ⊕ Fin r} :
    (blowupGraph H e).Adj x y ↔
      H.Adj (blowupProjection e x) (blowupProjection e y) := by
  rfl

theorem blowupGraph_triangleFree {k r : ℕ}
    (e : Fin r ↪ Block k × Block k) :
    (blowupGraph (baseGraph k) e).CliqueFree 3 := by
  intro s hs
  rw [SimpleGraph.is3Clique_iff] at hs
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := hs
  exact baseGraph_no_triangle
    (blowupGraph_adj.mp hxy) (blowupGraph_adj.mp hyz) (blowupGraph_adj.mp hxz)

theorem blowupGraph_diameterTwo {X : Type*} {r : ℕ} (H : SimpleGraph X)
    (e : Fin r ↪ X) (hdiam : HasDiameterTwo H)
    (hneighbor : ∀ x, ∃ y, H.Adj x y) :
    HasDiameterTwo (blowupGraph H e) := by
  intro x y hxy
  by_cases himage : blowupProjection e x = blowupProjection e y
  · obtain ⟨z, hz⟩ := hneighbor (blowupProjection e x)
    right
    refine ⟨Sum.inl z, ?_, ?_⟩
    · exact blowupGraph_adj.mpr hz
    · apply blowupGraph_adj.mpr
      change H.Adj z (blowupProjection e y)
      rw [← himage]
      exact hz.symm
  · rcases hdiam (blowupProjection e x) (blowupProjection e y) himage with h | ⟨z, hxz, hzy⟩
    · exact Or.inl (blowupGraph_adj.mpr h)
    · exact Or.inr ⟨Sum.inl z, blowupGraph_adj.mpr hxz,
        blowupGraph_adj.mpr hzy⟩

theorem blowupGraph_degree_le {X : Type*} [Fintype X] {r d : ℕ}
    (H : SimpleGraph X) (e : Fin r ↪ X) (hd : ∀ x, H.degree x ≤ d)
    (v : X ⊕ Fin r) :
    (blowupGraph H e).degree v ≤ 2 * d := by
  classical
  let N : Finset X := H.neighborFinset (blowupProjection e v)
  let R : Finset (Fin r) := Finset.univ.filter fun i => e i ∈ N
  let C : Finset (X ⊕ Fin r) :=
    N.map Function.Embedding.inl ∪ R.map Function.Embedding.inr
  have hsubset : (blowupGraph H e).neighborFinset v ⊆ C := by
    intro u hu
    rw [SimpleGraph.mem_neighborFinset, blowupGraph_adj] at hu
    cases u with
    | inl x =>
        rw [Finset.mem_union]
        left
        simp only [Finset.mem_map, Function.Embedding.inl_apply]
        refine ⟨x, ?_, rfl⟩
        exact (SimpleGraph.mem_neighborFinset H _ x).2 (by
          simpa [blowupProjection] using hu)
    | inr i =>
        rw [Finset.mem_union]
        right
        simp only [Finset.mem_map, Function.Embedding.inr_apply]
        refine ⟨i, ?_, rfl⟩
        simp only [R, Finset.mem_filter, Finset.mem_univ, true_and]
        exact (SimpleGraph.mem_neighborFinset H _ (e i)).2 (by
          simpa [blowupProjection] using hu)
  have hR : R.card ≤ N.card := by
    have hmap : (R.map e).card = R.card := Finset.card_map e
    rw [← hmap]
    apply Finset.card_le_card
    intro x hx
    simp only [Finset.mem_map] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    simpa [R] using hi
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  calc
    ((blowupGraph H e).neighborFinset v).card ≤ C.card :=
      Finset.card_le_card hsubset
    _ ≤ (N.map Function.Embedding.inl).card +
        (R.map Function.Embedding.inr).card :=
      Finset.card_union_le _ _
    _ = N.card + R.card := by simp
    _ ≤ 2 * N.card := by omega
    _ = 2 * H.degree (blowupProjection e v) := by
      simp only [N, SimpleGraph.card_neighborFinset_eq_degree]
    _ ≤ 2 * d := Nat.mul_le_mul_left 2 (hd _)

/-! ## An upper-bound model at every sufficiently large order -/

def constructionK (n : ℕ) : ℕ := n.sqrt / 2

def constructionP (n : ℕ) : ℕ := 2 * constructionK n

def constructionQ (n : ℕ) : ℕ := constructionP n * constructionP n

lemma construction_parameters {n : ℕ} (hn : 64 ≤ n) :
    2 ≤ constructionK n ∧
    constructionQ n ≤ n ∧
    n - constructionQ n ≤ constructionQ n ∧
    constructionP n ≤ n.sqrt := by
  let s := n.sqrt
  let k := constructionK n
  let p := constructionP n
  let q := constructionQ n
  have hs8 : 8 ≤ s := by
    rw [Nat.le_sqrt]
    norm_num [s]
    exact hn
  have hk : k = s / 2 := rfl
  have hp : p = 2 * k := rfl
  have hq : q = p * p := rfl
  have hk4 : 4 ≤ k := by omega
  have hp8 : 8 ≤ p := by omega
  have hp_le : p ≤ s := by omega
  have hq_le : q ≤ n := by
    rw [hq]
    exact (Nat.mul_le_mul hp_le hp_le).trans (Nat.sqrt_le n)
  have hs_succ : n < (s + 1) * (s + 1) := by
    simpa [s, Nat.succ_eq_add_one] using Nat.lt_succ_sqrt n
  have hs_le : s + 1 ≤ p + 2 := by omega
  have hsquares : (s + 1) * (s + 1) ≤ (p + 2) * (p + 2) :=
    Nat.mul_le_mul hs_le hs_le
  have hp_poly : (p + 2) * (p + 2) ≤ 2 * (p * p) := by
    nlinarith
  have hn_two_q : n ≤ 2 * q := by
    rw [hq]
    exact (hs_succ.trans_le (hsquares.trans hp_poly)).le
  have hr : n - q ≤ q := by omega
  exact ⟨by omega, hq_le, hr, hp_le⟩

/-- The explicit construction gives an `n`-vertex model of maximum degree
at most `8 * constructionK n`. -/
theorem exists_upper_model (n : ℕ) (hn : 64 ≤ n) :
    Nonempty (Model n (8 * constructionK n)) := by
  classical
  let k := constructionK n
  let p := constructionP n
  let q := constructionQ n
  let X := Block k × Block k
  let r := n - q
  have hparam := construction_parameters hn
  have hk : 2 ≤ k := hparam.1
  have hcardX : Fintype.card X = q := by
    simp [X, q, constructionQ, constructionP, k, constructionK,
      Fintype.card_prod]
  have hrq : r ≤ Fintype.card X := by
    rw [hcardX]
    exact hparam.2.2.1
  let e : Fin r ↪ X :=
    (Fin.castLEEmb hrq).trans (Fintype.equivFin X).symm.toEmbedding
  let G : SimpleGraph (X ⊕ Fin r) := blowupGraph (baseGraph k) e
  refine ⟨{
    V := X ⊕ Fin r
    G := G
    card_eq := ?_
    triangleFree := ?_
    diameterTwo := ?_
    degree_le := ?_
  }⟩
  · simp only [Fintype.card_sum, Fintype.card_fin, hcardX, r]
    omega
  · exact blowupGraph_triangleFree e
  · exact blowupGraph_diameterTwo (baseGraph k) e
      (baseGraph_diameterTwo hk) baseGraph_has_neighbor
  · intro v
    change (blowupGraph (baseGraph k) e).degree v ≤ 8 * constructionK n
    have hdeg := blowupGraph_degree_le
      (baseGraph k) e (baseGraph_degree_le k) v
    change (blowupGraph (baseGraph k) e).degree v ≤ 2 * (4 * k) at hdeg
    calc
      (blowupGraph (baseGraph k) e).degree v ≤ 2 * (4 * k) := hdeg
      _ = 8 * constructionK n := by simp [k]; ring

/-! ## Bounds for the extremal function -/

theorem erdos133Function_upper_nat (n : ℕ) (hn : 64 ≤ n) :
    erdos133Function n ≤ 8 * constructionK n :=
  erdos133Function_le (exists_upper_model n hn)

theorem erdos133Function_upper (n : ℕ) (hn : 64 ≤ n) :
    (erdos133Function n : ℝ) ≤ 4 * Real.sqrt n := by
  have hfun := erdos133Function_upper_nat n hn
  have hk : 8 * constructionK n ≤ 4 * n.sqrt := by
    simp only [constructionK]
    omega
  have hsqrt_nat : (n.sqrt : ℝ) ≤ Real.sqrt n := by
    apply Real.le_sqrt_of_sq_le
    norm_cast
    simpa [pow_two] using Nat.sqrt_le n
  calc
    (erdos133Function n : ℝ) ≤ (8 * constructionK n : ℕ) := by
      exact_mod_cast hfun
    _ ≤ (4 * n.sqrt : ℕ) := by exact_mod_cast hk
    _ = 4 * (n.sqrt : ℝ) := by norm_num
    _ ≤ 4 * Real.sqrt n := by nlinarith

theorem erdos133Function_lower (n : ℕ) (hn : 64 ≤ n) :
    Real.sqrt n ≤ erdos133Function n + 1 := by
  let M : Model n (erdos133Function n) :=
    Classical.choice (erdos133Function_mem ⟨_, exists_upper_model n hn⟩)
  letI : Fintype M.V := M.fintypeV
  have hcardpos : 0 < Fintype.card M.V := by
    rw [M.card_eq]
    omega
  letI : Nonempty M.V := Fintype.card_pos_iff.mp hcardpos
  have hmoore := moore_bound M.G (erdos133Function n)
    M.diameterTwo M.degree_le
  rw [M.card_eq] at hmoore
  rw [Real.sqrt_le_iff]
  constructor
  · positivity
  · norm_cast
    nlinarith

/-- The concrete two-sided estimate proving the order of growth. -/
theorem erdos133_two_sided (n : ℕ) (hn : 64 ≤ n) :
    Real.sqrt n - 1 ≤ erdos133Function n ∧
      (erdos133Function n : ℝ) ≤ 4 * Real.sqrt n := by
  constructor
  · have := erdos133Function_lower n hn
    norm_num at this ⊢
    linarith
  · exact erdos133Function_upper n hn

/-- The precise order-of-growth answer to Problem 133. -/
theorem erdos133_isTheta :
    Asymptotics.IsTheta Filter.atTop
      (fun n : ℕ => (erdos133Function n : ℝ))
      (fun n : ℕ => Real.sqrt n) := by
  constructor
  · apply Asymptotics.IsBigO.of_bound 4
    filter_upwards [Filter.eventually_ge_atTop 64] with n hn
    rw [Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ erdos133Function n),
      Real.norm_of_nonneg (Real.sqrt_nonneg n)]
    exact erdos133Function_upper n hn
  · apply Asymptotics.IsBigO.of_bound 2
    filter_upwards [Filter.eventually_ge_atTop 64] with n hn
    rw [Real.norm_of_nonneg (Real.sqrt_nonneg n),
      Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ erdos133Function n)]
    have hlower := erdos133Function_lower n hn
    have hsqrt : 2 ≤ Real.sqrt n := by
      rw [show (2 : ℝ) = Real.sqrt 4 by norm_num]
      exact Real.sqrt_le_sqrt (by norm_num; omega)
    norm_num at hlower ⊢
    nlinarith

/-- The conjectured divergence is false: the quotient is eventually bounded
by the absolute constant four. -/
theorem erdos133_ratio_not_tendsto_atTop :
    ¬ Filter.Tendsto
      (fun n : ℕ => (erdos133Function n : ℝ) / Real.sqrt n)
      Filter.atTop Filter.atTop := by
  intro h
  have hfive := (Filter.tendsto_atTop.1 h) 5
  have hfalse : ∀ᶠ _n : ℕ in Filter.atTop, False := by
    filter_upwards [hfive, Filter.eventually_ge_atTop 64] with n hfive hn
    have hupper := erdos133Function_upper n hn
    have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.2 (by positivity)
    have hratio : (erdos133Function n : ℝ) / Real.sqrt n ≤ 4 := by
      rw [div_le_iff₀ hsqrt]
      exact hupper
    linarith
  exact (Filter.Eventually.exists hfalse).choose_spec

/-- Erdős Problem 133: concrete bounds, the Θ-result, and the negative
answer to the proposed divergence. -/
theorem erdos_133 :
    (∀ n : ℕ, 64 ≤ n →
      Real.sqrt n - 1 ≤ erdos133Function n ∧
      (erdos133Function n : ℝ) ≤ 4 * Real.sqrt n) ∧
    Asymptotics.IsTheta Filter.atTop
      (fun n : ℕ => (erdos133Function n : ℝ))
      (fun n : ℕ => Real.sqrt n) ∧
    ¬ Filter.Tendsto
      (fun n : ℕ => (erdos133Function n : ℝ) / Real.sqrt n)
      Filter.atTop Filter.atTop := by
  exact ⟨erdos133_two_sided, erdos133_isTheta,
    erdos133_ratio_not_tendsto_atTop⟩

#print axioms erdos_133

end Erdos133
