/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos1024.LowerWeighted
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import ErdosProblems.Erdos1024.LocalLemma

/-!
# Sampling lemmas for the Phelps--Rödl lower bound

The random subset is represented by a uniform coloring `V → Fin K`; color
zero means selected.  All probability estimates below are finite sums over
this type.
-/

open scoped BigOperators

namespace Erdos1024
namespace Lower

variable {V : Type*} [Fintype V] [DecidableEq V]

def pairsAt (H : System V) (v : V) (Z : Finset V) :
    Finset (Finset V) :=
  (linkPairs H v (neighborhood H v)).filter (· ⊆ Z)

lemma extensionCount_eq_card_pairsAt (H : System V) (v : V) (Z : Finset V) :
    extensionCount H v Z = (pairsAt H v Z).card := by
  classical
  unfold extensionCount coveredPairs pairsAt
  congr 1
  ext a
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨ha, haSub⟩
    exact ⟨ha, fun x hxa ↦ (Finset.mem_inter.mp (haSub hxa)).1⟩
  · rintro ⟨ha, haZ⟩
    have haN : a ⊆ neighborhood H v := linkPairs_subset ha
    exact ⟨ha, fun x hxa ↦ Finset.mem_inter.mpr ⟨haZ hxa, haN hxa⟩⟩

lemma pairsAt_subset_powersetCard {H : System V} (h3 : ThreeUniform H)
    {v : V} {Z : Finset V} : pairsAt H v Z ⊆ Z.powersetCard 2 := by
  intro a ha
  have h := Finset.mem_filter.mp ha
  exact Finset.mem_powersetCard.mpr
    ⟨h.2, linkPairs_card_two h3 h.1⟩

lemma pairsAt_disjoint_of_outside {H : System V}
    (h3 : ThreeUniform H) (hlin : Linear H) {Z : Finset V}
    {v w : V} (hvZ : v ∉ Z) (hwZ : w ∉ Z) (hvw : v ≠ w) :
    Disjoint (pairsAt H v Z) (pairsAt H w Z) := by
  classical
  rw [Finset.disjoint_left]
  intro a hav haw
  have hav' := Finset.mem_filter.mp hav
  have haw' := Finset.mem_filter.mp haw
  obtain ⟨e, heH, hve, -, hea⟩ := mem_linkPairs.mp hav'.1
  obtain ⟨f, hfH, hwf, -, hfa⟩ := mem_linkPairs.mp haw'.1
  have haZ : a ⊆ Z := hav'.2
  have hvA : v ∉ a := fun h ↦ hvZ (haZ h)
  have hwA : w ∉ a := fun h ↦ hwZ (haZ h)
  have heq : e = insert v a := by
    rw [← hea]
    exact (Finset.insert_erase hve).symm
  have hfeq : f = insert w a := by
    rw [← hfa]
    exact (Finset.insert_erase hwf).symm
  have hef : e ≠ f := by
    intro h
    have hwE : w ∈ e := h ▸ hwf
    rw [heq] at hwE
    exact hwA ((Finset.mem_insert.mp hwE).resolve_left hvw.symm)
  have haInter : a ⊆ e ∩ f := by
    intro x hxa
    rw [heq, hfeq]
    simp [hxa]
  have htwo : 2 ≤ (e ∩ f).card := by
    have := Finset.card_le_card haInter
    simpa [linkPairs_card_two h3 hav'.1] using this
  exact (not_lt_of_ge htwo) (lt_of_le_of_lt (hlin heH hfH hef) (by omega))

/-- In a linear triple system, all extension pairs of an independent set
are distinct across outside vertices. -/
theorem sum_extensionCount_le_choose {H : System V}
    (h3 : ThreeUniform H) (hlin : Linear H) (Z : Finset V) :
    ∑ v ∈ Finset.univ \ Z, extensionCount H v Z ≤ Z.card.choose 2 := by
  classical
  let O : Finset V := Finset.univ \ Z
  have hpairwise : (O : Set V).PairwiseDisjoint (pairsAt H · Z) := by
    intro v hv w hw hvw
    exact pairsAt_disjoint_of_outside h3 hlin
      (Finset.mem_sdiff.mp hv).2 (Finset.mem_sdiff.mp hw).2 hvw
  have hUnion : O.biUnion (pairsAt H · Z) ⊆ Z.powersetCard 2 := by
    intro a ha
    obtain ⟨v, hvO, hav⟩ := Finset.mem_biUnion.mp ha
    exact pairsAt_subset_powersetCard h3 hav
  calc
    ∑ v ∈ Finset.univ \ Z, extensionCount H v Z =
        ∑ v ∈ O, (pairsAt H v Z).card := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [extensionCount_eq_card_pairsAt]
    _ = (O.biUnion (pairsAt H · Z)).card :=
      (Finset.card_biUnion hpairwise).symm
    _ ≤ (Z.powersetCard 2).card := Finset.card_le_card hUnion
    _ = Z.card.choose 2 := Finset.card_powersetCard 2 Z

theorem totalTruncatedExtension_le_choose {H : System V}
    (h3 : ThreeUniform H) (hlin : Linear H) (B : ℕ) (Z : Finset V) :
    totalTruncatedExtension H B Z ≤ Z.card.choose 2 := by
  unfold totalTruncatedExtension truncatedExtension
  calc
    ∑ v ∈ Finset.univ \ Z, min (extensionCount H v Z) B ≤
        ∑ v ∈ Finset.univ \ Z, extensionCount H v Z := by
      exact Finset.sum_le_sum fun _ _ ↦ min_le_left _ _
    _ ≤ _ := sum_extensionCount_le_choose h3 hlin Z

/-! ## Counting loose triangles -/

abbrev EdgeTriple (V : Type*) := (Finset V × Finset V) × Finset V

def IsLooseTriple (H : System V) (t : EdgeTriple V) : Prop :=
  let e := t.1.1
  let f := t.1.2
  let g := t.2
  e ∈ H ∧ f ∈ H ∧ g ∈ H ∧
    e ≠ f ∧ e ≠ g ∧ f ≠ g ∧
    (e ∩ f).card = 1 ∧ (e ∩ g).card = 1 ∧
    (f ∩ g).card = 1 ∧ (e ∩ f ∩ g).card = 0

instance isLooseTripleDecidable (H : System V) (t : EdgeTriple V) :
    Decidable (IsLooseTriple H t) := by
  unfold IsLooseTriple
  infer_instance

def looseTriangles (H : System V) : Finset (EdgeTriple V) :=
  ((H.product H).product H).filter (IsLooseTriple H)

@[simp] lemma mem_looseTriangles {H : System V} {t : EdgeTriple V} :
    t ∈ looseTriangles H ↔ IsLooseTriple H t := by
  rw [looseTriangles, Finset.mem_filter]
  constructor
  · exact fun h ↦ h.2
  · intro h
    refine ⟨Finset.mem_product.mpr ⟨?_, h.2.2.1⟩, h⟩
    exact Finset.mem_product.mpr ⟨h.1, h.2.1⟩

lemma hasLooseTriangle_iff_looseTriangles_nonempty {H : System V} :
    HasLooseTriangle H ↔ (looseTriangles H).Nonempty := by
  constructor
  · rintro ⟨e, he, f, hf, g, hg, hef, heg, hfg,
      hefCard, hegCard, hfgCard, htriple⟩
    exact ⟨((e, f), g), mem_looseTriangles.mpr
      ⟨he, hf, hg, hef, heg, hfg, hefCard, hegCard, hfgCard, htriple⟩⟩
  · rintro ⟨t, ht⟩
    rcases t with ⟨⟨e, f⟩, g⟩
    exact ⟨e, (mem_looseTriangles.mp ht).1,
      f, (mem_looseTriangles.mp ht).2.1,
      g, (mem_looseTriangles.mp ht).2.2.1,
      (mem_looseTriangles.mp ht).2.2.2.1,
      (mem_looseTriangles.mp ht).2.2.2.2.1,
      (mem_looseTriangles.mp ht).2.2.2.2.2.1,
      (mem_looseTriangles.mp ht).2.2.2.2.2.2.1,
      (mem_looseTriangles.mp ht).2.2.2.2.2.2.2.1,
      (mem_looseTriangles.mp ht).2.2.2.2.2.2.2.2.1,
      (mem_looseTriangles.mp ht).2.2.2.2.2.2.2.2.2⟩

lemma edge_eq_of_two_common {H : System V} (hlin : Linear H)
    {e f : Finset V} (he : e ∈ H) (hf : f ∈ H)
    {x y : V} (hxe : x ∈ e) (hxf : x ∈ f)
    (hye : y ∈ e) (hyf : y ∈ f) (hxy : x ≠ y) : e = f := by
  by_contra hef
  have hsub : ({x, y} : Finset V) ⊆ e ∩ f := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact Finset.mem_inter.mpr ⟨hxe, hxf⟩
    · exact Finset.mem_inter.mpr ⟨hye, hyf⟩
  have htwo : 2 ≤ (e ∩ f).card := by
    have := Finset.card_le_card hsub
    simpa [hxy, Ne.symm hxy] using this
  exact (not_lt_of_ge htwo) (lt_of_le_of_lt (hlin he hf hef) (by omega))

section TriangleCode

variable [LinearOrder V]

def singletonVertex (s : Finset V) (hs : s.card = 1) : V :=
  s.min' (Finset.card_pos.mp (by omega))

lemma singletonVertex_mem (s : Finset V) (hs : s.card = 1) :
    singletonVertex s hs ∈ s := by
  exact Finset.min'_mem _ _

abbrev LooseTriangle (H : System V) := {t : EdgeTriple V // t ∈ looseTriangles H}

def looseTriangleCode (H : System V) (t : LooseTriangle H) : V × V × V :=
  let h := mem_looseTriangles.mp t.property
  (singletonVertex (t.1.1.1 ∩ t.1.1.2) h.2.2.2.2.2.2.1,
    singletonVertex (t.1.1.1 ∩ t.1.2) h.2.2.2.2.2.2.2.1,
    singletonVertex (t.1.1.2 ∩ t.1.2) h.2.2.2.2.2.2.2.2.1)

lemma looseTriangleCode_injective {H : System V} (hlin : Linear H) :
    Function.Injective (looseTriangleCode H) := by
  rintro ⟨t, ht⟩ ⟨u, hu⟩ hcode
  rcases t with ⟨⟨e, f⟩, g⟩
  rcases u with ⟨⟨e', f'⟩, g'⟩
  have h := mem_looseTriangles.mp ht
  have h' := mem_looseTriangles.mp hu
  let x := singletonVertex (e ∩ f) h.2.2.2.2.2.2.1
  let y := singletonVertex (e ∩ g) h.2.2.2.2.2.2.2.1
  let z := singletonVertex (f ∩ g) h.2.2.2.2.2.2.2.2.1
  let x' := singletonVertex (e' ∩ f') h'.2.2.2.2.2.2.1
  let y' := singletonVertex (e' ∩ g') h'.2.2.2.2.2.2.2.1
  let z' := singletonVertex (f' ∩ g') h'.2.2.2.2.2.2.2.2.1
  have hxyz : (x, y, z) = (x', y', z') := hcode
  have hxx' : x = x' := congrArg Prod.fst hxyz
  have hyy' : y = y' := congrArg (fun q ↦ q.2.1) hxyz
  have hzz' : z = z' := congrArg (fun q ↦ q.2.2) hxyz
  have hx : x ∈ e ∩ f := singletonVertex_mem _ _
  have hy : y ∈ e ∩ g := singletonVertex_mem _ _
  have hz : z ∈ f ∩ g := singletonVertex_mem _ _
  have hx' : x' ∈ e' ∩ f' := singletonVertex_mem _ _
  have hy' : y' ∈ e' ∩ g' := singletonVertex_mem _ _
  have hz' : z' ∈ f' ∩ g' := singletonVertex_mem _ _
  have hxy : x ≠ y := by
    intro hxy
    have hcommon : x ∈ e ∩ f ∩ g := by
      exact Finset.mem_inter.mpr ⟨hx, hxy ▸ (Finset.mem_inter.mp hy).2⟩
    have : 0 < (e ∩ f ∩ g).card := Finset.card_pos.mpr ⟨x, hcommon⟩
    have hzero : (e ∩ f ∩ g).card = 0 := h.2.2.2.2.2.2.2.2.2
    omega
  have hxz : x ≠ z := by
    intro hxz
    have hcommon : x ∈ e ∩ f ∩ g := by
      exact Finset.mem_inter.mpr ⟨hx, hxz ▸ (Finset.mem_inter.mp hz).2⟩
    have : 0 < (e ∩ f ∩ g).card := Finset.card_pos.mpr ⟨x, hcommon⟩
    have hzero : (e ∩ f ∩ g).card = 0 := h.2.2.2.2.2.2.2.2.2
    omega
  have hyz : y ≠ z := by
    intro hyz
    have hcommon : y ∈ e ∩ f ∩ g := by
      exact Finset.mem_inter.mpr
        ⟨Finset.mem_inter.mpr
          ⟨(Finset.mem_inter.mp hy).1, hyz ▸ (Finset.mem_inter.mp hz).1⟩,
          (Finset.mem_inter.mp hy).2⟩
    have : 0 < (e ∩ f ∩ g).card := Finset.card_pos.mpr ⟨y, hcommon⟩
    have hzero : (e ∩ f ∩ g).card = 0 := h.2.2.2.2.2.2.2.2.2
    omega
  have hee' : e = e' := edge_eq_of_two_common hlin h.1 h'.1
    (Finset.mem_inter.mp hx).1 (hxx' ▸ (Finset.mem_inter.mp hx').1)
    (Finset.mem_inter.mp hy).1 (hyy' ▸ (Finset.mem_inter.mp hy').1) hxy
  have hff' : f = f' := edge_eq_of_two_common hlin h.2.1 h'.2.1
    (Finset.mem_inter.mp hx).2 (hxx' ▸ (Finset.mem_inter.mp hx').2)
    (Finset.mem_inter.mp hz).1 (hzz' ▸ (Finset.mem_inter.mp hz').1) hxz
  have hgg' : g = g' := edge_eq_of_two_common hlin h.2.2.1 h'.2.2.1
    (Finset.mem_inter.mp hy).2 (hyy' ▸ (Finset.mem_inter.mp hy').2)
    (Finset.mem_inter.mp hz).2 (hzz' ▸ (Finset.mem_inter.mp hz').2) hyz
  apply Subtype.ext
  simp [hee', hff', hgg']

theorem card_looseTriangles_le_cube {H : System V} (hlin : Linear H) :
    (looseTriangles H).card ≤ (Fintype.card V) ^ 3 := by
  let i : LooseTriangle H → V × V × V := looseTriangleCode H
  have hi : Function.Injective i := looseTriangleCode_injective hlin
  have hc := Fintype.card_le_of_injective i hi
  rw [← Fintype.card_coe]
  change Fintype.card (LooseTriangle H) ≤ (Fintype.card V) ^ 3
  simpa [i, Fintype.card_prod, pow_succ, mul_assoc] using hc

end TriangleCode

def triangleVertices (t : EdgeTriple V) : Finset V :=
  t.1.1 ∪ t.1.2 ∪ t.2

theorem card_triangleVertices_of_mem {H : System V} (h3 : ThreeUniform H)
    {t : EdgeTriple V} (ht : t ∈ looseTriangles H) :
    (triangleVertices t).card = 6 := by
  rcases t with ⟨⟨e, f⟩, g⟩
  have h := mem_looseTriangles.mp ht
  have hefUnion : (e ∪ f).card = 5 := by
    have hcard := Finset.card_union_add_card_inter e f
    rw [h3 e h.1, h3 f h.2.1, h.2.2.2.2.2.2.1] at hcard
    omega
  have hinterEq : (e ∪ f) ∩ g = (e ∩ g) ∪ (f ∩ g) := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_union]
    tauto
  have hdisj : Disjoint (e ∩ g) (f ∩ g) := by
    rw [Finset.disjoint_left]
    intro x hxE hxF
    have hcommon : x ∈ e ∩ f ∩ g := by
      exact Finset.mem_inter.mpr
        ⟨Finset.mem_inter.mpr
          ⟨(Finset.mem_inter.mp hxE).1, (Finset.mem_inter.mp hxF).1⟩,
          (Finset.mem_inter.mp hxE).2⟩
    have hzero : e ∩ f ∩ g = ∅ := Finset.card_eq_zero.mp h.2.2.2.2.2.2.2.2.2
    simpa [hzero] using hcommon
  have hinterCard : ((e ∪ f) ∩ g).card = 2 := by
    rw [hinterEq, Finset.card_union_of_disjoint hdisj,
      h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1]
  change (e ∪ f ∪ g).card = 6
  have hcard := Finset.card_union_add_card_inter (e ∪ f) g
  rw [hefUnion, h3 g h.2.2.1, hinterCard] at hcard
  omega

abbrev Coloring (V : Type*) (K : ℕ) := V → Fin K

def selectedSet {K : ℕ} [NeZero K] (omega : Coloring V K) : Finset V :=
  Finset.univ.filter fun v ↦ omega v = 0

@[simp] lemma mem_selectedSet {K : ℕ} [NeZero K]
    {omega : Coloring V K} {v : V} :
    v ∈ selectedSet omega ↔ omega v = 0 := by
  simp [selectedSet]

def selectedLooseTriangles {K : ℕ} [NeZero K]
    (H : System V) (omega : Coloring V K) : Finset (EdgeTriple V) :=
  (looseTriangles H).filter fun t ↦ triangleVertices t ⊆ selectedSet omega

@[simp] lemma mem_selectedLooseTriangles {K : ℕ} [NeZero K]
    {H : System V} {omega : Coloring V K} {t : EdgeTriple V} :
    t ∈ selectedLooseTriangles H omega ↔
      t ∈ looseTriangles H ∧ triangleVertices t ⊆ selectedSet omega := by
  simp [selectedLooseTriangles]

def subsetSelectedEvent {K : ℕ} [NeZero K]
    (S : Finset V) : Finset (Coloring V K) :=
  Finset.univ.filter fun omega ↦ S ⊆ selectedSet omega

@[simp] lemma mem_subsetSelectedEvent {K : ℕ} [NeZero K]
    {S : Finset V} {omega : Coloring V K} :
    omega ∈ subsetSelectedEvent (K := K) S ↔ S ⊆ selectedSet omega := by
  simp [subsetSelectedEvent]

def subsetSelectedEquiv {K : ℕ} [NeZero K] (S : Finset V) :
    ↥(subsetSelectedEvent (K := K) S) ≃ ({v : V // v ∉ S} → Fin K) where
  toFun omega v := omega.1 v.1
  invFun f := ⟨fun v ↦ if hv : v ∈ S then 0 else f ⟨v, hv⟩, by
    rw [mem_subsetSelectedEvent]
    intro v hv
    simp [hv]⟩
  left_inv omega := by
    apply Subtype.ext
    funext v
    by_cases hv : v ∈ S
    · have hzero : omega.1 v = 0 :=
        mem_selectedSet.mp ((mem_subsetSelectedEvent.mp omega.property) hv)
      simp [hv, hzero]
    · simp [hv]
  right_inv f := by
    funext v
    simp [v.property]

theorem card_subsetSelectedEvent {K : ℕ} [NeZero K] (S : Finset V) :
    (subsetSelectedEvent (K := K) S).card =
      K ^ (Fintype.card V - S.card) := by
  rw [← Fintype.card_coe]
  rw [Fintype.card_congr (subsetSelectedEquiv (K := K) S)]
  simp only [Fintype.card_fun, Fintype.card_fin]
  congr 1
  rw [Fintype.card_subtype_compl (fun v : V ↦ v ∈ S)]
  congr 1
  exact Fintype.card_of_subtype S (fun _ ↦ Iff.rfl)

theorem uniformProbability_subsetSelectedEvent {K : ℕ} [NeZero K]
    (S : Finset V) :
    LocalLemma.uniformProbability (subsetSelectedEvent (K := K) S) =
      1 / (K : ℝ) ^ S.card := by
  classical
  have hK : (0 : ℝ) < K := by exact_mod_cast (NeZero.pos K)
  have hS : S.card ≤ Fintype.card V := Finset.card_le_univ S
  have hN : Fintype.card V =
      (Fintype.card V - S.card) + S.card := by omega
  unfold LocalLemma.uniformProbability
  rw [card_subsetSelectedEvent]
  simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
  have hpow : (K : ℝ) ^ Fintype.card V =
      (K : ℝ) ^ (Fintype.card V - S.card) * (K : ℝ) ^ S.card := by
    conv_lhs => rw [hN, pow_add]
  rw [hpow]
  field_simp

theorem expect_indicator_subsetSelected {K : ℕ} [NeZero K]
    (S : Finset V) :
    𝔼 omega : Coloring V K,
        (if S ⊆ selectedSet omega then (1 : ℝ) else 0) =
      1 / (K : ℝ) ^ S.card := by
  rw [Fintype.expect_eq_sum_div_card]
  have hsum :
      (∑ omega : Coloring V K,
        (if S ⊆ selectedSet omega then (1 : ℝ) else 0)) =
        ((subsetSelectedEvent (K := K) S).card : ℝ) := by
    rw [← Finset.sum_filter]
    simp [subsetSelectedEvent]
  rw [hsum]
  exact uniformProbability_subsetSelectedEvent S

theorem expect_card_selectedSet {K : ℕ} [NeZero K] :
    𝔼 omega : Coloring V K, ((selectedSet omega).card : ℝ) =
      (Fintype.card V : ℝ) / K := by
  calc
    𝔼 omega : Coloring V K, ((selectedSet omega).card : ℝ) =
        𝔼 omega : Coloring V K,
          ∑ v : V, (if ({v} : Finset V) ⊆ selectedSet omega then (1 : ℝ) else 0) := by
      apply Finset.expect_congr rfl
      intro omega _
      simp only [Finset.singleton_subset_iff]
      simp [selectedSet]
    _ = ∑ v : V,
        𝔼 omega : Coloring V K,
          (if ({v} : Finset V) ⊆ selectedSet omega then (1 : ℝ) else 0) :=
      Finset.expect_sum_comm _ _ _
    _ = ∑ _v : V, (1 / (K : ℝ)) := by
      apply Finset.sum_congr rfl
      intro v _
      simpa using expect_indicator_subsetSelected (K := K) ({v} : Finset V)
    _ = (Fintype.card V : ℝ) / K := by
      simp [div_eq_mul_inv]

theorem expect_card_selectedLooseTriangles {K : ℕ} [NeZero K]
    {H : System V} (h3 : ThreeUniform H) :
    𝔼 omega : Coloring V K,
        ((selectedLooseTriangles H omega).card : ℝ) =
      ((looseTriangles H).card : ℝ) / (K : ℝ) ^ 6 := by
  calc
    𝔼 omega : Coloring V K,
        ((selectedLooseTriangles H omega).card : ℝ) =
      𝔼 omega : Coloring V K,
        ∑ t ∈ looseTriangles H,
          (if triangleVertices t ⊆ selectedSet omega then (1 : ℝ) else 0) := by
      apply Finset.expect_congr rfl
      intro omega _
      simp [selectedLooseTriangles]
    _ = ∑ t ∈ looseTriangles H,
        𝔼 omega : Coloring V K,
          (if triangleVertices t ⊆ selectedSet omega then (1 : ℝ) else 0) :=
      Finset.expect_sum_comm _ _ _
    _ = ∑ _t ∈ looseTriangles H, (1 / (K : ℝ) ^ 6) := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [expect_indicator_subsetSelected,
        card_triangleVertices_of_mem h3 ht]
    _ = ((looseTriangles H).card : ℝ) / (K : ℝ) ^ 6 := by
      simp [div_eq_mul_inv]

section TriangleDeletion

variable [LinearOrder V]

def triangleRepresentative (H : System V) (t : LooseTriangle H) : V :=
  (looseTriangleCode H t).1

lemma triangleRepresentative_mem (H : System V) (t : LooseTriangle H) :
    triangleRepresentative H t ∈ triangleVertices t.1 := by
  let h := mem_looseTriangles.mp t.property
  exact Finset.mem_union_left _ (Finset.mem_union_left _
    (Finset.mem_inter.mp (singletonVertex_mem
      (t.1.1.1 ∩ t.1.1.2) h.2.2.2.2.2.2.1)).1)

def selectedAsLoose {K : ℕ} [NeZero K] (H : System V)
    (omega : Coloring V K) (t : ↥(selectedLooseTriangles H omega)) :
    LooseTriangle H :=
  ⟨t.1, (mem_selectedLooseTriangles.mp t.property).1⟩

def deletedVertices {K : ℕ} [NeZero K]
    (H : System V) (omega : Coloring V K) : Finset V :=
  (selectedLooseTriangles H omega).attach.image fun t ↦
    triangleRepresentative H (selectedAsLoose H omega t)

def prunedSet {K : ℕ} [NeZero K]
    (H : System V) (omega : Coloring V K) : Finset V :=
  selectedSet omega \ deletedVertices H omega

lemma card_deletedVertices_le {K : ℕ} [NeZero K]
    (H : System V) (omega : Coloring V K) :
    (deletedVertices H omega).card ≤ (selectedLooseTriangles H omega).card := by
  unfold deletedVertices
  exact (Finset.card_image_le).trans_eq (Finset.card_attach)

lemma prunedSet_subset_selectedSet {K : ℕ} [NeZero K]
    (H : System V) (omega : Coloring V K) :
    prunedSet H omega ⊆ selectedSet omega := by
  exact Finset.sdiff_subset

lemma card_selectedSet_le_card_prunedSet_add_triangles
    {K : ℕ} [NeZero K] (H : System V) (omega : Coloring V K) :
    (selectedSet omega).card ≤ (prunedSet H omega).card +
      (selectedLooseTriangles H omega).card := by
  have hsplit := Finset.card_sdiff_add_card_inter
    (selectedSet omega) (deletedVertices H omega)
  change (selectedSet omega).card ≤
    (selectedSet omega \ deletedVertices H omega).card +
      (selectedLooseTriangles H omega).card
  calc
    (selectedSet omega).card =
        (selectedSet omega \ deletedVertices H omega).card +
          (selectedSet omega ∩ deletedVertices H omega).card := hsplit.symm
    _ ≤ (selectedSet omega \ deletedVertices H omega).card +
          (deletedVertices H omega).card := by
      gcongr
      exact (Finset.inter_subset_right :
          selectedSet omega ∩ deletedVertices H omega ⊆ deletedVertices H omega)
    _ ≤ _ := Nat.add_le_add_left (card_deletedVertices_le H omega) _

theorem pruned_triangleFree {K : ℕ} [NeZero K]
    (H : System V) (omega : Coloring V K) :
    TriangleFree (H.filter fun e ↦ e ⊆ prunedSet H omega) := by
  rw [TriangleFree]
  intro htri
  obtain ⟨e, he, f, hf, g, hg, hef, heg, hfg,
    hefCard, hegCard, hfgCard, htriple⟩ := htri
  have he' := Finset.mem_filter.mp he
  have hf' := Finset.mem_filter.mp hf
  have hg' := Finset.mem_filter.mp hg
  let t : EdgeTriple V := ((e, f), g)
  have ht : t ∈ looseTriangles H := mem_looseTriangles.mpr
    ⟨he'.1, hf'.1, hg'.1, hef, heg, hfg,
      hefCard, hegCard, hfgCard, htriple⟩
  have htPruned : triangleVertices t ⊆ prunedSet H omega := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · rcases Finset.mem_union.mp hx with hxE | hxF
      · exact he'.2 hxE
      · exact hf'.2 hxF
    · exact hg'.2 hx
  have htSelected : t ∈ selectedLooseTriangles H omega :=
    mem_selectedLooseTriangles.mpr
      ⟨ht, htPruned.trans (prunedSet_subset_selectedSet H omega)⟩
  let st : ↥(selectedLooseTriangles H omega) := ⟨t, htSelected⟩
  let v := triangleRepresentative H (selectedAsLoose H omega st)
  have hvDelete : v ∈ deletedVertices H omega := by
    apply Finset.mem_image.mpr
    exact ⟨st, Finset.mem_attach _ _, rfl⟩
  have hvTriangle : v ∈ triangleVertices t :=
    triangleRepresentative_mem H (selectedAsLoose H omega st)
  have hvPruned : v ∈ prunedSet H omega := htPruned hvTriangle
  exact (Finset.mem_sdiff.mp hvPruned).2 hvDelete

end TriangleDeletion

def selectedWeight {K : ℕ} [NeZero K]
    (w : V → ℕ) (omega : Coloring V K) : ℕ :=
  ∑ v : V, if omega v = 0 then w v else 0

lemma exp_le_one_add_two_mul {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.exp x ≤ 1 + 2 * x := by
  have hconv := convexOn_exp.2 (Set.mem_univ (0 : ℝ))
    (Set.mem_univ (1 : ℝ)) (sub_nonneg.mpr hx1) hx0 (by ring)
  have hrewrite : (1 - x) • (0 : ℝ) + x • (1 : ℝ) = x := by
    simp [smul_eq_mul]
  rw [hrewrite, Real.exp_zero] at hconv
  have he : Real.exp 1 < 3 := Real.exp_one_lt_three
  simp only [smul_eq_mul] at hconv
  nlinarith

lemma sum_exp_selectedWeight_eq_product {K : ℕ} [NeZero K]
    (B : ℕ) (w : V → ℕ) :
    ∑ omega : Coloring V K,
        Real.exp ((selectedWeight w omega : ℝ) / B) =
      (∏ v : V, (((K - 1 : ℕ) : ℝ) + Real.exp ((w v : ℝ) / B))) := by
  classical
  calc
    ∑ omega : Coloring V K,
        Real.exp ((selectedWeight w omega : ℝ) / B) =
        ∑ omega : Coloring V K,
          ∏ v : V, Real.exp (((if omega v = 0 then w v else 0 : ℕ) : ℝ) / B) := by
      apply Finset.sum_congr rfl
      intro omega _
      rw [← Real.exp_sum]
      congr 1
      unfold selectedWeight
      push_cast
      simp only [div_eq_mul_inv, Finset.sum_mul]
    _ = (∏ v : V, (∑ c : Fin K,
        Real.exp (((if c = 0 then w v else 0 : ℕ) : ℝ) / B))) := by
      simpa only [Fintype.piFinset_univ] using
        (Finset.sum_prod_piFinset (Finset.univ : Finset (Fin K))
          (fun v c ↦ Real.exp (((if c = 0 then w v else 0 : ℕ) : ℝ) / B)))
    _ = (∏ v : V, (((K - 1 : ℕ) : ℝ) + Real.exp ((w v : ℝ) / B))) := by
      apply Finset.prod_congr rfl
      intro v _
      have hzero : (0 : Fin K) ∈ (Finset.univ : Finset (Fin K)) := Finset.mem_univ _
      change (∑ c ∈ (Finset.univ : Finset (Fin K)),
        Real.exp (((if c = 0 then w v else 0 : ℕ) : ℝ) / B)) = _
      rw [← Finset.sum_erase_add _ _ hzero]
      simp only [if_pos, Nat.cast_zero, zero_div, Real.exp_zero]
      congr 1
      calc
        ∑ c ∈ (Finset.univ : Finset (Fin K)).erase 0,
            Real.exp (((if c = 0 then w v else 0 : ℕ) : ℝ) / B) =
            ∑ _c ∈ (Finset.univ : Finset (Fin K)).erase 0, (1 : ℝ) := by
          apply Finset.sum_congr rfl
          intro c hc
          have hc0 : c ≠ 0 := (Finset.mem_erase.mp hc).1
          simp [hc0]
        _ = (((Finset.univ : Finset (Fin K)).erase 0).card : ℝ) := by simp
        _ = ((K - 1 : ℕ) : ℝ) := by
          congr 1
          simp [Finset.card_erase_of_mem hzero, Fintype.card_fin]

lemma sum_exp_selectedWeight_bound {K B S : ℕ} [NeZero K]
    (hB : 0 < B) (w : V → ℕ) (hwB : ∀ v, w v ≤ B)
    (hwSum : ∑ v : V, w v ≤ S) :
    ∑ omega : Coloring V K,
        Real.exp ((selectedWeight w omega : ℝ) / B) ≤
      (K : ℝ) ^ Fintype.card V *
        Real.exp (2 * (S : ℝ) / ((K : ℝ) * B)) := by
  classical
  rw [sum_exp_selectedWeight_eq_product]
  have hK : (0 : ℝ) < K := by exact_mod_cast (NeZero.pos K)
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB
  have hfactor : ∀ v : V,
      ((K - 1 : ℕ) : ℝ) + Real.exp ((w v : ℝ) / B) ≤
        (K : ℝ) * Real.exp (2 * (w v : ℝ) / ((K : ℝ) * B)) := by
    intro v
    have hw0 : (0 : ℝ) ≤ (w v : ℝ) / B := by positivity
    have hw1 : (w v : ℝ) / B ≤ 1 := by
      rw [div_le_one hBR]
      exact_mod_cast hwB v
    have hsec := exp_le_one_add_two_mul hw0 hw1
    have hcast : ((K - 1 : ℕ) : ℝ) = (K : ℝ) - 1 := by
      rw [Nat.cast_sub NeZero.one_le]
      norm_num
    have harg0 : 0 ≤ 2 * (w v : ℝ) / ((K : ℝ) * B) := by positivity
    have hexp := Real.add_one_le_exp (2 * (w v : ℝ) / ((K : ℝ) * B))
    rw [hcast]
    calc
      (K : ℝ) - 1 + Real.exp ((w v : ℝ) / B) ≤
          (K : ℝ) + 2 * ((w v : ℝ) / B) := by linarith
      _ = (K : ℝ) *
          (1 + 2 * (w v : ℝ) / ((K : ℝ) * B)) := by field_simp
      _ ≤ (K : ℝ) * Real.exp
          (2 * (w v : ℝ) / ((K : ℝ) * B)) :=
        mul_le_mul_of_nonneg_left (by simpa [add_comm] using hexp) hK.le
  calc
    (∏ v : V, (((K - 1 : ℕ) : ℝ) + Real.exp ((w v : ℝ) / B))) ≤
        (∏ v : V, ((K : ℝ) *
          Real.exp (2 * (w v : ℝ) / ((K : ℝ) * B)))) := by
      exact Finset.prod_le_prod (fun _ _ ↦ by positivity) fun v _ ↦ hfactor v
    _ = (K : ℝ) ^ Fintype.card V *
        Real.exp (∑ v : V, 2 * (w v : ℝ) / ((K : ℝ) * B)) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, ← Real.exp_sum]
      simp only [Finset.card_univ]
    _ ≤ (K : ℝ) ^ Fintype.card V *
        Real.exp (2 * (S : ℝ) / ((K : ℝ) * B)) := by
      apply mul_le_mul_of_nonneg_left
      · apply Real.exp_le_exp.mpr
        have hwCast : (∑ v : V, (w v : ℝ)) ≤ S := by exact_mod_cast hwSum
        calc
          ∑ v : V, 2 * (w v : ℝ) / ((K : ℝ) * B) =
              2 * (∑ v : V, (w v : ℝ)) / ((K : ℝ) * B) := by
            simp_rw [div_eq_mul_inv]
            rw [← Finset.sum_mul, ← Finset.mul_sum]
          _ ≤ _ := by gcongr
      · positivity

def weightBadEvent {K : ℕ} [NeZero K] (w : V → ℕ) (T : ℕ) :
    Finset (Coloring V K) :=
  Finset.univ.filter fun omega ↦ T ≤ selectedWeight w omega

lemma uniformProbability_weightBadEvent {K B S T : ℕ} [NeZero K]
    (hB : 0 < B) (w : V → ℕ) (hwB : ∀ v, w v ≤ B)
    (hwSum : ∑ v : V, w v ≤ S) :
    LocalLemma.uniformProbability (Omega := Coloring V K)
      (weightBadEvent (K := K) w T) ≤
      Real.exp (2 * (S : ℝ) / ((K : ℝ) * B) - (T : ℝ) / B) := by
  classical
  let Omega := Coloring V K
  have hOmega : (0 : ℝ) < Fintype.card Omega := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card Omega)
  have hTexp : 0 < Real.exp ((T : ℝ) / B) := Real.exp_pos _
  have hbad :
      ((weightBadEvent (K := K) w T).card : ℝ) * Real.exp ((T : ℝ) / B) ≤
        ∑ omega ∈ weightBadEvent (K := K) w T,
          Real.exp ((selectedWeight w omega : ℝ) / B) := by
    calc
      ((weightBadEvent (K := K) w T).card : ℝ) * Real.exp ((T : ℝ) / B) =
          ∑ _omega ∈ weightBadEvent (K := K) w T,
            Real.exp ((T : ℝ) / B) := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro omega homega
        apply Real.exp_le_exp.mpr
        have hT : T ≤ selectedWeight w omega :=
          (Finset.mem_filter.mp homega).2
        exact div_le_div_of_nonneg_right (by exact_mod_cast hT) (by positivity)
  have hmgf :
      ∑ omega ∈ weightBadEvent (K := K) w T,
          Real.exp ((selectedWeight w omega : ℝ) / B) ≤
        (K : ℝ) ^ Fintype.card V *
          Real.exp (2 * (S : ℝ) / ((K : ℝ) * B)) := by
    calc
      _ ≤ ∑ omega : Coloring V K,
          Real.exp ((selectedWeight w omega : ℝ) / B) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun _ _ _ ↦ (Real.exp_pos _).le)
      _ ≤ _ := sum_exp_selectedWeight_bound hB w hwB hwSum
  have hcardOmega : (Fintype.card Omega : ℝ) =
      (K : ℝ) ^ Fintype.card V := by
    simp [Omega, Fintype.card_fun]
  have hcard : ((weightBadEvent (K := K) w T).card : ℝ) ≤
      (Fintype.card Omega : ℝ) *
        Real.exp (2 * (S : ℝ) / ((K : ℝ) * B) - (T : ℝ) / B) := by
    rw [Real.exp_sub]
    rw [show (Fintype.card Omega : ℝ) *
      (Real.exp (2 * (S : ℝ) / ((K : ℝ) * B)) /
        Real.exp ((T : ℝ) / B)) =
      ((Fintype.card Omega : ℝ) *
        Real.exp (2 * (S : ℝ) / ((K : ℝ) * B))) /
          Real.exp ((T : ℝ) / B) by ring]
    rw [le_div_iff₀ hTexp]
    rw [hcardOmega]
    exact hbad.trans hmgf
  unfold LocalLemma.uniformProbability
  rw [div_le_iff₀ hOmega]
  simpa [mul_comm, mul_left_comm, mul_assoc] using hcard

/-! ## A simultaneous extension bound -/

def extensionWeight (H : System V) (B : ℕ) (Z : Finset V) (v : V) : ℕ :=
  if v ∈ Z then 0 else truncatedExtension H B v Z

lemma extensionWeight_le (H : System V) (B : ℕ) (Z : Finset V) (v : V) :
    extensionWeight H B Z v ≤ B := by
  unfold extensionWeight truncatedExtension
  split_ifs
  · exact Nat.zero_le _
  · exact min_le_right _ _

lemma sum_extensionWeight_eq (H : System V) (B : ℕ) (Z : Finset V) :
    ∑ v : V, extensionWeight H B Z v = totalTruncatedExtension H B Z := by
  classical
  unfold extensionWeight totalTruncatedExtension
  calc
    (∑ v : V, if v ∈ Z then 0 else truncatedExtension H B v Z) =
        ∑ v ∈ Finset.univ \ Z,
          (if v ∈ Z then 0 else truncatedExtension H B v Z) := by
      symm
      apply Finset.sum_subset Finset.sdiff_subset
      intro v _ hv
      have hvZ : v ∈ Z := by simpa using hv
      simp [hvZ]
    _ = ∑ v ∈ Finset.univ \ Z, truncatedExtension H B v Z := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [if_neg (Finset.mem_sdiff.mp hv).2]

lemma sum_extensionWeight_le_choose {H : System V}
    (h3 : ThreeUniform H) (hlin : Linear H) {A B : ℕ}
    {Z : Finset V} (hZA : Z.card ≤ A) :
    ∑ v : V, extensionWeight H B Z v ≤ A.choose 2 := by
  rw [sum_extensionWeight_eq]
  exact (totalTruncatedExtension_le_choose h3 hlin B Z).trans
    (Nat.choose_le_choose 2 hZA)

lemma selectedWeight_extensionWeight_eq {K : ℕ} [NeZero K]
    (H : System V) (B : ℕ) (Z : Finset V) (omega : Coloring V K) :
    selectedWeight (extensionWeight H B Z) omega =
      ∑ v ∈ selectedSet omega \ Z, truncatedExtension H B v Z := by
  classical
  unfold selectedWeight extensionWeight selectedSet
  calc
    (∑ v : V, if omega v = 0 then
        (if v ∈ Z then 0 else truncatedExtension H B v Z) else 0) =
      ∑ v ∈ Finset.univ.filter (fun v ↦ omega v = 0) \ Z,
        (if omega v = 0 then
          (if v ∈ Z then 0 else truncatedExtension H B v Z) else 0) := by
      symm
      apply Finset.sum_subset
        (Finset.sdiff_subset.trans (Finset.filter_subset _ _))
      intro v _ hv
      by_cases hvZ : v ∈ Z
      · simp [hvZ]
      · have hvSel : v ∉ Finset.univ.filter (fun v ↦ omega v = 0) := by
          intro hv'
          exact hv (Finset.mem_sdiff.mpr ⟨hv', hvZ⟩)
        have hvOmega : omega v ≠ 0 := by simpa using hvSel
        simp [hvZ, hvOmega]
    _ = ∑ v ∈ Finset.univ.filter (fun v ↦ omega v = 0) \ Z,
        truncatedExtension H B v Z := by
      apply Finset.sum_congr rfl
      intro v hv
      have h := Finset.mem_sdiff.mp hv
      have hvOmega : omega v = 0 := (Finset.mem_filter.mp h.1).2
      simp [hvOmega, h.2]

def someExtensionBadEvent {K : ℕ} [NeZero K]
    (H : System V) (B T : ℕ) : Finset (Coloring V K) :=
  (independentSets H).biUnion fun Z ↦
    weightBadEvent (K := K) (extensionWeight H B Z) T

lemma card_independentSets_le_power {H : System V} {A : ℕ}
    (hA : A ≤ Fintype.card V)
    (hcard : ∀ Z ∈ independentSets H, Z.card ≤ A) :
    (independentSets H).card ≤ (Fintype.card V + 1) ^ (A + 1) := by
  classical
  let layers : Finset (Finset V) :=
    (Finset.range (A + 1)).biUnion fun i ↦ Finset.univ.powersetCard i
  have hsub : independentSets H ⊆ layers := by
    intro Z hZ
    apply Finset.mem_biUnion.mpr
    refine ⟨Z.card, Finset.mem_range.mpr (by
      have := hcard Z hZ
      omega), ?_⟩
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ Z, rfl⟩
  calc
    (independentSets H).card ≤ layers.card := Finset.card_le_card hsub
    _ ≤ ∑ i ∈ Finset.range (A + 1),
        ((Finset.univ : Finset V).powersetCard i).card :=
      Finset.card_biUnion_le
    _ = ∑ i ∈ Finset.range (A + 1), (Fintype.card V).choose i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.card_powersetCard, Finset.card_univ]
    _ ≤ ∑ _i ∈ Finset.range (A + 1),
        (Fintype.card V + 1) ^ A := by
      apply Finset.sum_le_sum
      intro i hi
      have hiA : i ≤ A := by
        have hi' := Finset.mem_range.mp hi
        omega
      calc
        (Fintype.card V).choose i ≤ (Fintype.card V) ^ i :=
          Nat.choose_le_pow _ _
        _ ≤ (Fintype.card V + 1) ^ i :=
          Nat.pow_le_pow_left (by omega) i
        _ ≤ (Fintype.card V + 1) ^ A :=
          Nat.pow_le_pow_right (by omega) hiA
    _ = (A + 1) * (Fintype.card V + 1) ^ A := by simp
    _ ≤ (Fintype.card V + 1) ^ (A + 1) := by
      rw [pow_succ]
      calc
        (A + 1) * (Fintype.card V + 1) ^ A =
            (Fintype.card V + 1) ^ A * (A + 1) := Nat.mul_comm _ _
        _ ≤ (Fintype.card V + 1) ^ A * (Fintype.card V + 1) :=
          Nat.mul_le_mul_left _ (Nat.succ_le_succ hA)

theorem uniformProbability_someExtensionBadEvent {K A B T : ℕ} [NeZero K]
    {H : System V} (h3 : ThreeUniform H) (hlin : Linear H)
    (hB : 0 < B) (hA : A ≤ Fintype.card V)
    (hcard : ∀ Z ∈ independentSets H, Z.card ≤ A) :
    LocalLemma.uniformProbability
        (someExtensionBadEvent (K := K) H B T) ≤
      ((Fintype.card V + 1 : ℕ) : ℝ) ^ (A + 1) *
        Real.exp (2 * ((A.choose 2 : ℕ) : ℝ) /
          ((K : ℝ) * B) - (T : ℝ) / B) := by
  classical
  let q : ℝ := Real.exp (2 * ((A.choose 2 : ℕ) : ℝ) /
    ((K : ℝ) * B) - (T : ℝ) / B)
  have hone :
      LocalLemma.uniformProbability
          (someExtensionBadEvent (K := K) H B T) ≤
        ∑ Z ∈ independentSets H,
          LocalLemma.uniformProbability
            (weightBadEvent (K := K) (extensionWeight H B Z) T) := by
    unfold someExtensionBadEvent LocalLemma.uniformProbability
    rw [← Finset.sum_div]
    apply div_le_div_of_nonneg_right
    · exact_mod_cast (Finset.card_biUnion_le :
        ((independentSets H).biUnion fun Z ↦
          weightBadEvent (K := K) (extensionWeight H B Z) T).card ≤
        ∑ Z ∈ independentSets H,
          (weightBadEvent (K := K) (extensionWeight H B Z) T).card)
    · positivity
  have heach : ∀ Z ∈ independentSets H,
      LocalLemma.uniformProbability
          (weightBadEvent (K := K) (extensionWeight H B Z) T) ≤ q := by
    intro Z hZ
    apply uniformProbability_weightBadEvent hB
    · exact extensionWeight_le H B Z
    · exact sum_extensionWeight_le_choose h3 hlin (hcard Z hZ)
  calc
    LocalLemma.uniformProbability
        (someExtensionBadEvent (K := K) H B T) ≤
      ∑ Z ∈ independentSets H,
        LocalLemma.uniformProbability
          (weightBadEvent (K := K) (extensionWeight H B Z) T) := hone
    _ ≤ ∑ _Z ∈ independentSets H, q := Finset.sum_le_sum heach
    _ = ((independentSets H).card : ℝ) * q := by simp
    _ ≤ (((Fintype.card V + 1) ^ (A + 1) : ℕ) : ℝ) * q := by
      gcongr
      exact_mod_cast card_independentSets_le_power hA hcard
    _ = ((Fintype.card V + 1 : ℕ) : ℝ) ^ (A + 1) *
        Real.exp (2 * ((A.choose 2 : ℕ) : ℝ) /
          ((K : ℝ) * B) - (T : ℝ) / B) := by
      simp [q]

lemma selected_extension_bound_of_not_bad {K B T : ℕ} [NeZero K]
    {H : System V} {omega : Coloring V K}
    (hgood : omega ∉ someExtensionBadEvent (K := K) H B T)
    {Z : Finset V} (hZ : Independent H Z) :
    ∑ v ∈ selectedSet omega \ Z, truncatedExtension H B v Z < T := by
  rw [← selectedWeight_extensionWeight_eq]
  by_contra hnot
  apply hgood
  apply Finset.mem_biUnion.mpr
  refine ⟨Z, mem_independentSets.mpr hZ, ?_⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Nat.le_of_not_gt hnot⟩

/-! ## Averaging and pruning -/

lemma expect_indicator_event {Omega : Type*} [Fintype Omega] [DecidableEq Omega]
    (E : Finset Omega) :
    𝔼 omega : Omega, (if omega ∈ E then (1 : ℝ) else 0) =
      ((E.card : ℝ) / Fintype.card Omega) := by
  rw [Fintype.expect_eq_sum_div_card]
  congr 1
  rw [← Finset.sum_filter]
  simp

def samplingScore {K : ℕ} [NeZero K]
    (H : System V) (B T : ℕ) (omega : Coloring V K) : ℝ :=
  ((selectedSet omega).card : ℝ) -
    ((selectedLooseTriangles H omega).card : ℝ) -
    (if omega ∈ someExtensionBadEvent (K := K) H B T then
      (Fintype.card V : ℝ) else 0)

lemma expect_samplingScore {K B T : ℕ} [NeZero K]
    {H : System V} (h3 : ThreeUniform H) :
    𝔼 omega : Coloring V K, samplingScore H B T omega =
      (Fintype.card V : ℝ) / K -
        ((looseTriangles H).card : ℝ) / (K : ℝ) ^ 6 -
        (Fintype.card V : ℝ) *
          LocalLemma.uniformProbability
            (someExtensionBadEvent (K := K) H B T) := by
  unfold samplingScore
  rw [Finset.expect_sub_distrib, Finset.expect_sub_distrib,
    expect_card_selectedSet, expect_card_selectedLooseTriangles h3]
  congr 1
  calc
    𝔼 omega : Coloring V K,
        (if omega ∈ someExtensionBadEvent (K := K) H B T then
          (Fintype.card V : ℝ) else 0) =
      (Fintype.card V : ℝ) *
        (𝔼 omega : Coloring V K,
          (if omega ∈ someExtensionBadEvent (K := K) H B T then
            (1 : ℝ) else 0)) := by
        rw [Finset.mul_expect]
        apply Finset.expect_congr rfl
        intro omega _
        split_ifs <;> simp
    _ = (Fintype.card V : ℝ) *
        LocalLemma.uniformProbability
          (someExtensionBadEvent (K := K) H B T) := by
      rw [expect_indicator_event]
      rfl

/-- A finite sampling lemma.  Its hypotheses are only explicit numerical
inequalities; all hypergraph structure is discharged in the conclusion. -/
theorem exists_large_pruned_sample {K A B T : ℕ} [NeZero K]
    [LinearOrder V] {H : System V} (h3 : ThreeUniform H) (hlin : Linear H)
    (hB : 0 < B) (hA : A ≤ Fintype.card V)
    (hcard : ∀ Z ∈ independentSets H, Z.card ≤ A)
    {L : ℝ} (hL : 0 < L)
    (hscore : L ≤
      (Fintype.card V : ℝ) / K -
        (((Fintype.card V) ^ 3 : ℕ) : ℝ) / (K : ℝ) ^ 6 -
        (Fintype.card V : ℝ) *
          (((Fintype.card V + 1 : ℕ) : ℝ) ^ (A + 1) *
            Real.exp (2 * ((A.choose 2 : ℕ) : ℝ) /
              ((K : ℝ) * B) - (T : ℝ) / B))) :
    ∃ omega : Coloring V K,
      omega ∉ someExtensionBadEvent (K := K) H B T ∧
      L ≤ ((prunedSet H omega).card : ℝ) ∧
      TriangleFree (H.filter fun e ↦ e ⊆ prunedSet H omega) ∧
      ∀ Z : Finset V, Independent H Z →
        ∑ v ∈ prunedSet H omega \ Z,
          truncatedExtension H B v Z < T := by
  classical
  have htri := card_looseTriangles_le_cube hlin
  have hbad := uniformProbability_someExtensionBadEvent
    h3 hlin hB hA hcard (K := K) (T := T)
  have havg : L ≤ 𝔼 omega : Coloring V K, samplingScore H B T omega := by
    rw [expect_samplingScore h3]
    apply hscore.trans
    have htriR : ((looseTriangles H).card : ℝ) ≤
        (((Fintype.card V) ^ 3 : ℕ) : ℝ) := by exact_mod_cast htri
    have hKpow : 0 ≤ (K : ℝ) ^ 6 := by positivity
    have hN : 0 ≤ (Fintype.card V : ℝ) := by positivity
    gcongr
  obtain ⟨omega, -, homega⟩ :=
    Finset.exists_le_of_le_expect (Finset.univ_nonempty :
      (Finset.univ : Finset (Coloring V K)).Nonempty) havg
  have hgood : omega ∉ someExtensionBadEvent (K := K) H B T := by
    intro hbadOmega
    have hsel : (selectedSet omega).card ≤ Fintype.card V :=
      Finset.card_le_univ _
    have htri0 : 0 ≤ ((selectedLooseTriangles H omega).card : ℝ) := by positivity
    have hselR : ((selectedSet omega).card : ℝ) ≤ Fintype.card V := by
      exact_mod_cast hsel
    unfold samplingScore at homega
    rw [if_pos hbadOmega] at homega
    linarith
  have hsize : L ≤ ((prunedSet H omega).card : ℝ) := by
    have hsplit := card_selectedSet_le_card_prunedSet_add_triangles H omega
    have hsplitR : ((selectedSet omega).card : ℝ) ≤
        (prunedSet H omega).card + (selectedLooseTriangles H omega).card := by
      exact_mod_cast hsplit
    unfold samplingScore at homega
    rw [if_neg hgood] at homega
    linarith
  refine ⟨omega, hgood, hsize, pruned_triangleFree H omega, ?_⟩
  intro Z hZ
  have hselected := selected_extension_bound_of_not_bad hgood hZ
  have hsub : prunedSet H omega \ Z ⊆ selectedSet omega \ Z := by
    intro v hv
    have hv' := Finset.mem_sdiff.mp hv
    exact Finset.mem_sdiff.mpr
      ⟨prunedSet_subset_selectedSet H omega hv'.1, hv'.2⟩
  calc
    ∑ v ∈ prunedSet H omega \ Z, truncatedExtension H B v Z ≤
        ∑ v ∈ selectedSet omega \ Z, truncatedExtension H B v Z :=
      Finset.sum_le_sum_of_subset hsub
    _ < T := hselected

end Lower
end Erdos1024

#print axioms Erdos1024.Lower.totalTruncatedExtension_le_choose
