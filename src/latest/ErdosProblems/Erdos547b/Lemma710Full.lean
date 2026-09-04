/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib
import ErdosProblems.Erdos547b.EC2
import ErdosProblems.Erdos547b.Partite
import ErdosProblems.Erdos547b.TreePartition

/-!
# Zhao's Lemma 7.10 — consolidated repository-integrable development

This file consolidates the complete proof and all support lemmas.  It imports
only Mathlib and existing repository modules; in particular it has no
dependency on any temporary scratch module.
-/

/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

/-!
# Zhao's Lemma 7.10 (alternate development)

This scratch file develops the exact finite extension machinery needed by the
proof of Lemma 7.10.  The final theorem is stated at the bottom of the file.
-/

open scoped SimpleGraph

noncomputable section

namespace Erdos547b.ZhaoLemma710Alt

open Finset SimpleGraph

universe u v

variable {A : Type u} {B : Type v}

/-- A (non-oriented) two-edge path, bundled with distinct endpoints. -/
structure TwoPath (T : SimpleGraph A) where
  left : A
  middle : A
  right : A
  left_ne_right : left ≠ right
  adj_left : T.Adj left middle
  adj_right : T.Adj middle right

namespace TwoPath

variable [Fintype A] [DecidableEq A]
variable {T : SimpleGraph A}

theorem middle_ne_left (P : TwoPath T) : P.middle ≠ P.left := P.adj_left.ne'

theorem middle_ne_right (P : TwoPath T) : P.middle ≠ P.right := P.adj_right.ne

/-- If the middle of a two-path has degree two, its only neighbors are its
two endpoints. -/
theorem neighborFinset_middle_eq (P : TwoPath T) [DecidableRel T.Adj]
    (hdeg : T.degree P.middle = 2) :
    T.neighborFinset P.middle = {P.left, P.right} := by
  have hsub : {P.left, P.right} ⊆ T.neighborFinset P.middle := by
    intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact (T.mem_neighborFinset P.middle P.left).mpr P.adj_left.symm
    · exact (T.mem_neighborFinset P.middle P.right).mpr P.adj_right
  have hcard : #(T.neighborFinset P.middle) ≤ #{P.left, P.right} := by
    rw [T.card_neighborFinset_eq_degree, hdeg, Finset.card_pair P.left_ne_right]
  exact (Finset.eq_of_subset_of_card_le hsub hcard).symm

/-- In a rooted tree, the endpoints of a degree-two-middle two-path not
containing the root lie at different root distances.  Thus the phrases
"nearer endpoint" and "farther endpoint" in Zhao's proof are unambiguous. -/
theorem endpoint_dist_ne (P : TwoPath T) [DecidableRel T.Adj]
    (hT : T.IsTree) (root : A)
    (hroot_left : root ≠ P.left) (hroot_middle : root ≠ P.middle)
    (hroot_right : root ≠ P.right)
    (hdeg : T.degree P.middle = 2) :
    T.dist root P.left ≠ T.dist root P.right := by
  intro heq
  have hLM := hT.dist_eq_dist_add_one_of_adj root P.adj_left
  have hMR := hT.dist_eq_dist_add_one_of_adj root P.adj_right
  rcases hLM with hLM | hLM <;> rcases hMR with hMR | hMR
  · omega
  · let p := Erdos547b.TreePartition.parent hT root hroot_middle.symm
    have hpAdj : T.Adj P.middle p :=
      (Erdos547b.TreePartition.parent_adj hT root hroot_middle.symm).symm
    have hpMem : p ∈ T.neighborFinset P.middle :=
      (T.mem_neighborFinset P.middle p).mpr hpAdj
    rw [P.neighborFinset_middle_eq hdeg] at hpMem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hpMem
    have hpDist := Erdos547b.TreePartition.parent_dist_add_one hT root hroot_middle.symm
    rcases hpMem with hp | hp
    · dsimp only [p] at hp
      rw [hp] at hpDist
      omega
    · dsimp only [p] at hp
      rw [hp] at hpDist
      omega
  · have hparL := Erdos547b.TreePartition.eq_parent_of_adj_of_dist_add_one
      hT root hroot_middle.symm P.adj_left hLM.symm
    have hparR := Erdos547b.TreePartition.eq_parent_of_adj_of_dist_add_one
      hT root hroot_middle.symm P.adj_right.symm hMR.symm
    exact P.left_ne_right (hparL.trans hparR.symm)
  · omega

end TwoPath

/-- Assemble a graph copy from a copy on the complement of a finite deleted
set and prescribed, pairwise distinct images of the deleted vertices.  This
is the graph-theoretic assembly step used after the two Hall matchings in
Zhao's Lemma 7.10. -/
theorem copy_of_induce_compl_and_extension
    [Fintype A] [DecidableEq A] [DecidableEq B]
    (T : SimpleGraph A) (G : SimpleGraph B) (D : Finset A)
    (f : (T.induce ((D : Set A)ᶜ)).Copy G) (g : D → B)
    (hg : Function.Injective g)
    (hfg : ∀ x y, f x ≠ g y)
    (hDD : ∀ x y : D, T.Adj x y → G.Adj (g x) (g y))
    (hDC : ∀ x : D, ∀ y : ↥((D : Set A)ᶜ),
      T.Adj x y → G.Adj (g x) (f y)) :
    ∃ F : T.Copy G,
      (∀ x : D, F x = g x) ∧
      (∀ x : ↥((D : Set A)ᶜ), F x = f x) := by
  classical
  let F : A → B := fun x => if hx : x ∈ D then g ⟨x, hx⟩ else f ⟨x, by simpa using hx⟩
  have hmap : ∀ {x y : A}, T.Adj x y → G.Adj (F x) (F y) := by
    intro x y hxy
    by_cases hx : x ∈ D
    · by_cases hy : y ∈ D
      · simpa [F, hx, hy] using hDD ⟨x, hx⟩ ⟨y, hy⟩ hxy
      · simpa [F, hx, hy] using hDC ⟨x, hx⟩ ⟨y, by simpa using hy⟩ hxy
    · by_cases hy : y ∈ D
      · have h := hDC ⟨y, hy⟩ ⟨x, by simpa using hx⟩ hxy.symm
        simpa [F, hx, hy] using h.symm
      · have hxy' : (T.induce ((D : Set A)ᶜ)).Adj
            ⟨x, by simpa using hx⟩ ⟨y, by simpa using hy⟩ := by
          simpa using hxy
        simpa [F, hx, hy] using f.toHom.map_adj hxy'
  have hinj : Function.Injective F := by
    intro x y hxy
    by_cases hx : x ∈ D
    · by_cases hy : y ∈ D
      · have : (⟨x, hx⟩ : D) = ⟨y, hy⟩ := by
          apply hg
          simpa [F, hx, hy] using hxy
        exact congrArg Subtype.val this
      · exfalso
        apply hfg ⟨y, by simpa using hy⟩ ⟨x, hx⟩
        simpa [F, hx, hy] using hxy.symm
    · by_cases hy : y ∈ D
      · exfalso
        apply hfg ⟨x, by simpa using hx⟩ ⟨y, hy⟩
        simpa [F, hx, hy] using hxy
      · have : (⟨x, by simpa using hx⟩ : ↥((D : Set A)ᶜ)) =
            ⟨y, by simpa using hy⟩ := by
          apply f.injective
          simpa [F, hx, hy] using hxy
        exact congrArg Subtype.val this
  let C : T.Copy G := ⟨⟨F, @hmap⟩, hinj⟩
  refine ⟨C, ?_, ?_⟩
  · intro x
    simpa [C, F] using x.property
  · intro x
    have hxSet := x.property
    change x.1 ∉ (D : Set A) at hxSet
    have hx : x.1 ∉ D := by simpa using hxSet
    change F x.1 = f x
    rw [show F x.1 = f ⟨x.1, by simpa using hx⟩ by simp [F, hx]]

/-- The exact host path system in condition (3) of Zhao's Lemma 7.10.
The midpoint index is the actual vertex of `Y₂`; endpoint injectivity encodes
that all supplied two-paths are vertex-disjoint. -/
structure CenteredTwoPathSystem [Fintype B] [DecidableEq B]
    (G : SimpleGraph B) (X Y₂ : Finset B) where
  left : Y₂ → B
  right : Y₂ → B
  left_mem : ∀ y : Y₂, left y ∈ X
  right_mem : ∀ y : Y₂, right y ∈ X
  adj_left : ∀ y : Y₂, G.Adj (left y) y
  adj_right : ∀ y : Y₂, G.Adj y (right y)
  endpointInjective : Function.Injective fun p : Y₂ × Fin 2 =>
    if p.2 = 0 then left p.1 else right p.1

namespace CenteredTwoPathSystem

variable [Fintype B] [DecidableEq B]
variable {G : SimpleGraph B} {X Y₂ : Finset B}

/-- All endpoints of the supplied host paths. -/
def endpoints (P : CenteredTwoPathSystem G X Y₂) : Finset B :=
  Finset.univ.image fun p : Y₂ × Fin 2 =>
    if p.2 = 0 then P.left p.1 else P.right p.1

theorem card_endpoints (P : CenteredTwoPathSystem G X Y₂) :
    #P.endpoints = 2 * #Y₂ := by
  classical
  rw [endpoints, Finset.card_image_iff.mpr fun _ _ _ _ h => P.endpointInjective h]
  simp [mul_comm]

theorem endpoints_subset (P : CenteredTwoPathSystem G X Y₂) :
    P.endpoints ⊆ X := by
  classical
  intro w hw
  obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp hw
  by_cases hp : p.2 = 0
  · simpa [hp] using P.left_mem p.1
  · simpa [hp] using P.right_mem p.1

theorem left_ne_right (P : CenteredTwoPathSystem G X Y₂)
    (y y' : Y₂) : P.left y ≠ P.right y' := by
  intro h
  have hp := P.endpointInjective (a₁ := (y, 0)) (a₂ := (y', 1)) (by simpa using h)
  have := congrArg (fun q : Y₂ × Fin 2 => q.2) hp
  simp at this

end CenteredTwoPathSystem

/-- Intersecting two neighborhoods costs at most the sum of their two defect
bounds.  This is the local counting estimate behind both the fixed-path
forest extension and the final Hall matchings. -/
theorem card_common_neighbors_add_two_mul_ge
    [Fintype B] [DecidableEq B] (G : SimpleGraph B) [DecidableRel G.Adj]
    (C : Finset B) (x y : B) (l : ℕ)
    (hx : #(C \ G.neighborFinset x) ≤ l)
    (hy : #(C \ G.neighborFinset y) ≤ l) :
    #((C ∩ G.neighborFinset x) ∩ G.neighborFinset y) + 2 * l ≥ #C := by
  classical
  let bad := (C \ G.neighborFinset x) ∪ (C \ G.neighborFinset y)
  have hbad : #bad ≤ 2 * l := by
    calc
      #bad ≤ #(C \ G.neighborFinset x) + #(C \ G.neighborFinset y) :=
        Finset.card_union_le _ _
      _ ≤ l + l := Nat.add_le_add hx hy
      _ = 2 * l := by omega
  have hgood : C \ bad = (C ∩ G.neighborFinset x) ∩ G.neighborFinset y := by
    ext w
    dsimp only [bad]
    simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter,
      G.mem_neighborFinset]
    tauto
  have hsplit := Finset.card_sdiff_add_card_inter C bad
  have hinter : #(C ∩ bad) ≤ #bad := Finset.card_le_card Finset.inter_subset_right
  rw [hgood] at hsplit
  omega

/-- The one-neighborhood version of the same defect estimate. -/
theorem card_neighbors_add_defect_ge
    [Fintype B] [DecidableEq B] (G : SimpleGraph B) [DecidableRel G.Adj]
    (C : Finset B) (x : B) (l : ℕ)
    (hx : #(C \ G.neighborFinset x) ≤ l) :
    #(C ∩ G.neighborFinset x) + l ≥ #C := by
  have hsplit := Finset.card_sdiff_add_card_inter C (G.neighborFinset x)
  omega

/-- The singleton-target branch of Lemma 7.10.  This is separated because
Proposition 7.11(3) is naturally stated for nontrivial trees. -/
theorem zhao_lemma_7_10_of_subsingleton
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (T : SimpleGraph A) (G : SimpleGraph B)
    (U1 U2 : Finset A) (X Y : Finset B) (z : A) (a : B)
    (hsub : Subsingleton A)
    (hbi : T.IsBipartiteWith (U1 : Set A) (U2 : Set A))
    (hz : z ∈ U1) (ha : a ∈ X) :
    ∃ f : T.Copy G, f z = a ∧
      (∀ v ∈ U1, f v ∈ X) ∧ (∀ v ∈ U2, f v ∈ Y) := by
  let F : A → B := fun _ => a
  have hFinj : Function.Injective F := fun x y _ => hsub.elim x y
  have hFmap : ∀ ⦃x y : A⦄, T.Adj x y → G.Adj (F x) (F y) := by
    intro x y hxy
    exact False.elim (hxy.ne (hsub.elim x y))
  let f : T.Copy G := ⟨⟨F, @hFmap⟩, hFinj⟩
  refine ⟨f, rfl, ?_, ?_⟩
  · intro v hv
    simpa [f, F] using ha
  · intro v hv
    have hvz : v = z := hsub.elim v z
    subst v
    exact False.elim (Set.disjoint_left.mp hbi.disjoint hz hv)

end Erdos547b.ZhaoLemma710Alt

#print axioms Erdos547b.ZhaoLemma710Alt.copy_of_induce_compl_and_extension
#print axioms Erdos547b.ZhaoLemma710Alt.zhao_lemma_7_10_of_subsingleton


/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

open scoped SimpleGraph

noncomputable section

namespace Erdos547b.ZhaoLemma710Alt

open Finset SimpleGraph

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The three vertices of the length-two path centred at `v`. -/
def twoPathVertices (T : SimpleGraph V) [DecidableRel T.Adj] (v : V) : Finset V :=
  insert v (T.neighborFinset v)

/-- Zhao's special two-path condition, expressed through its centre. -/
def IsSpecialTwoPathCenter (T : SimpleGraph V) [DecidableRel T.Adj] (v : V) : Prop :=
  T.degree v = 2 ∧
    ∀ x ∈ Erdos547EC2.openNeighborFinset T (T.neighborFinset v), T.degree x ≤ 2

/-- The two families supplied by Proposition 7.11(3).  The support-disjointness
field includes disjointness both within and between the two families. -/
structure Proposition711Part3Witness
    (T : SimpleGraph V) [DecidableRel T.Adj]
    (U1 U2 : Finset V) (z : V) (l : ℕ) where
  P : Finset V
  Q : Finset V
  card_P : P.card = 5 * l
  card_Q : Q.card = 4 * l
  P_mem : ∀ p ∈ P, p ∈ U2
  Q_mem : ∀ q ∈ Q, q ∈ U1
  P_special : ∀ p ∈ P, IsSpecialTwoPathCenter T p
  Q_degree_two : ∀ q ∈ Q, T.degree q = 2
  supports_pairwise : ((P ∪ Q : Finset V) : Set V).PairwiseDisjoint (twoPathVertices T)
  avoid_root : ∀ c ∈ P ∪ Q, z ∉ twoPathVertices T c

private theorem exists_disjoint_support_packing
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (support : α → Finset β) (D : Finset α) (r k : ℕ)
    (hr : 0 < r)
    (hne : ∀ x ∈ D, (support x).Nonempty)
    (hconflict : ∀ x ∈ D,
      (D.filter fun y => ¬Disjoint (support x) (support y)).card ≤ r)
    (hcard : r * k ≤ D.card) :
    ∃ P : Finset α, P ⊆ D ∧ P.card = k ∧ (P : Set α).PairwiseDisjoint support := by
  induction k generalizing D with
  | zero => exact ⟨∅, by simp⟩
  | succ k ih =>
      have hDpos : 0 < D.card := by
        have : r ≤ r * (k + 1) := by nlinarith
        omega
      obtain ⟨x, hxD⟩ := Finset.card_pos.mp hDpos
      let bad := D.filter fun y => ¬Disjoint (support x) (support y)
      let D' := D \ bad
      have hbad_sub : bad ⊆ D := Finset.filter_subset _ _
      have hbad_card : bad.card ≤ r := hconflict x hxD
      have hx_bad : x ∈ bad := by
        simp only [bad, Finset.mem_filter, hxD, true_and]
        intro hdisj
        obtain ⟨b, hb⟩ := hne x hxD
        exact (Finset.disjoint_left.mp hdisj) hb hb
      have hx_not_D' : x ∉ D' := by simp [D', hx_bad]
      have hD'card : r * k ≤ D'.card := by
        dsimp only [D']
        rw [Finset.card_sdiff_of_subset hbad_sub]
        rw [Nat.mul_succ] at hcard
        omega
      have hne' : ∀ y ∈ D', (support y).Nonempty := by
        intro y hy
        exact hne y (Finset.mem_sdiff.mp hy).1
      have hconflict' : ∀ y ∈ D',
          (D'.filter fun z => ¬Disjoint (support y) (support z)).card ≤ r := by
        intro y hy
        apply le_trans (Finset.card_le_card ?_) (hconflict y (Finset.mem_sdiff.mp hy).1)
        intro z hz
        simp only [Finset.mem_filter] at hz ⊢
        exact ⟨(Finset.mem_sdiff.mp hz.1).1, hz.2⟩
      obtain ⟨P, hPD', hPk, hPpair⟩ := ih D' hne' hconflict' hD'card
      have hxP : x ∉ P := fun hxP => hx_not_D' (hPD' hxP)
      have hxdisj : ∀ y ∈ (P : Set α), Disjoint (support x) (support y) := by
        intro y hyP
        have hyD' : y ∈ D' := hPD' hyP
        have hy_not_bad : y ∉ bad := (Finset.mem_sdiff.mp hyD').2
        apply not_not.mp
        intro hnot
        apply hy_not_bad
        exact Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hyD').1, hnot⟩
      refine ⟨insert x P, ?_, by simp [hPk, hxP], ?_⟩
      · intro y hy
        simp only [Finset.mem_insert] at hy
        rcases hy with rfl | hy
        · exact hxD
        · exact (Finset.mem_sdiff.mp (hPD' hy)).1
      · simpa only [Finset.coe_insert] using hPpair.insert_of_notMem hxP hxdisj

@[simp] private theorem mem_twoPathVertices {T : SimpleGraph V} [DecidableRel T.Adj]
    {u v : V} : u ∈ twoPathVertices T v ↔ u = v ∨ T.Adj v u := by
  simp [twoPathVertices, eq_comm]

private theorem card_twoPathVertices {T : SimpleGraph V} [DecidableRel T.Adj]
    {v : V} (hv : T.degree v = 2) : (twoPathVertices T v).card = 3 := by
  rw [twoPathVertices, Finset.card_insert_of_notMem]
  · simpa [T.card_neighborFinset_eq_degree, hv]
  · simp

private theorem card_secondNeighborhood_le_three
    (T : SimpleGraph V) [DecidableRel T.Adj] {v : V}
    (hv : T.degree v = 2)
    (hend : ∀ x, T.Adj v x → T.degree x ≤ 2) :
    (Erdos547EC2.openNeighborFinset T (T.neighborFinset v)).card ≤ 3 := by
  have hcardN : (T.neighborFinset v).card = 2 := by
    simpa [T.card_neighborFinset_eq_degree, hv]
  obtain ⟨a, b, hab, hN⟩ := Finset.card_eq_two.mp hcardN
  have hva : T.Adj v a := by
    rw [← T.mem_neighborFinset]
    simp [hN]
  have hvb : T.Adj v b := by
    rw [← T.mem_neighborFinset]
    simp [hN]
  have hdegA := hend a hva
  have hdegB := hend b hvb
  have hinter : 1 ≤ (T.neighborFinset a ∩ T.neighborFinset b).card := by
    exact Finset.card_pos.mpr ⟨v, by simp [hva.symm, hvb.symm]⟩
  have hunion := Finset.card_union_add_card_inter (T.neighborFinset a) (T.neighborFinset b)
  have hrewrite :
      Erdos547EC2.openNeighborFinset T (T.neighborFinset v) =
        T.neighborFinset a ∪ T.neighborFinset b := by
    ext x
    simp [Erdos547EC2.openNeighborFinset, hN]
  rw [hrewrite]
  rw [T.card_neighborFinset_eq_degree, T.card_neighborFinset_eq_degree] at hunion
  omega

private theorem card_conflicting_centers_le_three
    (T : SimpleGraph V) [DecidableRel T.Adj]
    {A B : Finset V} (hbi : T.IsBipartiteWith (A : Set V) (B : Set V))
    (D : Finset V) (hD : ∀ y ∈ D, y ∈ A ∧ T.degree y = 2)
    {x : V} (hxD : x ∈ D)
    (hend : ∀ u, T.Adj x u → T.degree u ≤ 2) :
    (D.filter fun y => ¬Disjoint (twoPathVertices T x) (twoPathVertices T y)).card ≤ 3 := by
  have hxA := (hD x hxD).1
  have hxdeg := (hD x hxD).2
  have hsame_not_adj {u v : V} (hu : u ∈ A) (hv : v ∈ A) : ¬T.Adj u v := by
    intro huv
    have hvB := hbi.mem_of_mem_adj hu huv
    exact Set.disjoint_left.mp hbi.disjoint hv hvB
  have hsubset :
      D.filter (fun y => ¬Disjoint (twoPathVertices T x) (twoPathVertices T y)) ⊆
        Erdos547EC2.openNeighborFinset T (T.neighborFinset x) := by
    intro y hy
    have hyD := (Finset.mem_filter.mp hy).1
    have hyA := (hD y hyD).1
    have hyconf := (Finset.mem_filter.mp hy).2
    by_cases hxy : y = x
    · subst y
      have hpos : 0 < (T.neighborFinset x).card := by
        simpa [T.card_neighborFinset_eq_degree, hxdeg]
      obtain ⟨u, hu⟩ := Finset.card_pos.mp hpos
      apply Finset.mem_biUnion.mpr
      exact ⟨u, hu, (T.mem_neighborFinset u x).mpr ((T.mem_neighborFinset x u).mp hu).symm⟩
    · obtain ⟨q, hqx, hqy⟩ := Finset.not_disjoint_iff.mp hyconf
      rw [mem_twoPathVertices] at hqx hqy
      rcases hqx with rfl | hxq
      · rcases hqy with hxy' | hyx
        · exact (hxy hxy'.symm).elim
        · exact (hsame_not_adj hyA hxA hyx).elim
      · rcases hqy with rfl | hyq
        · exact (hsame_not_adj hxA hyA hxq).elim
        · apply Finset.mem_biUnion.mpr
          exact ⟨q, (T.mem_neighborFinset x q).mpr hxq,
            (T.mem_neighborFinset q y).mpr hyq.symm⟩
  exact (Finset.card_le_card hsubset).trans
    (card_secondNeighborhood_le_three T hxdeg hend)

private theorem card_sdiff_lower_bound {α : Type*} [DecidableEq α]
    (A R : Finset α) : A.card ≤ (A \ R).card + R.card := by
  have h := Finset.card_sdiff_add_card_inter A R
  have hi := Finset.card_le_card (Finset.inter_subset_right : A ∩ R ⊆ R)
  omega

/-- Zhao, Proposition 7.11(3), with `l` an upper bound on the number of
leaves.  It produces the `5*l` special `U2`-centred paths and the further
`4*l` `U1`-centred paths, all mutually vertex-disjoint and avoiding `z`. -/
theorem zhao_proposition_7_11_part_three
    (T : SimpleGraph V) [DecidableRel T.Adj] [Nontrivial V]
    (U1 U2 : Finset V) (z : V) (l : ℕ)
    (hT : T.IsTree)
    (hbi : T.IsBipartiteWith (U1 : Set V) (U2 : Set V))
    (hcover : U1 ∪ U2 = Finset.univ)
    (hz : z ∈ U1)
    (hleaves : (Erdos547EC2.leafVertices T).card ≤ l)
    (hU1 : 26 * l ≤ U1.card) (hU2 : 26 * l ≤ U2.card) :
    Nonempty (Proposition711Part3Witness T U1 U2 z l) := by
  classical
  let L := Erdos547EC2.leafVertices T
  let Br := Erdos547EC2.branchVertices T
  let B1 := Br ∩ U1
  let B2 := Br ∩ U2
  let N : Finset V → Finset V := Erdos547EC2.openNeighborFinset T
  have hLtwo : 2 ≤ L.card := by
    dsimp only [L]
    obtain ⟨a, b, hab, ha, hb⟩ := hT.exists_ne_and_degree_eq_one
    have hs : {a, b} ⊆ Erdos547EC2.leafVertices T := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      simp only [Erdos547EC2.leafVertices, Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hx with rfl | rfl
      · exact ha
      · exact hb
    simpa [hab] using Finset.card_le_card hs
  have hBr : Br.card ≤ L.card - 2 := by
    simpa only [Br, L] using Erdos547EC2.zhao_prop_7_11_part_one T hT
  have hBr_add : Br.card + 2 ≤ L.card := by omega
  have hLle : L.card ≤ l := by simpa only [L] using hleaves
  have hdisj12 : Disjoint U1 U2 := Finset.disjoint_coe.mp hbi.disjoint
  have hBr_split : B1.card + B2.card = Br.card := by
    have hsub : Br ⊆ U1 ∪ U2 := by
      intro x hx
      rw [hcover]
      exact Finset.mem_univ x
    have heq : Br = B1 ∪ B2 := by
      ext x
      simp only [B1, B2, Finset.mem_union, Finset.mem_inter]
      constructor
      · intro hx
        have hor : x ∈ U1 ∨ x ∈ U2 := by
          simpa only [Finset.mem_union] using hsub hx
        exact hor.elim (fun h => Or.inl ⟨hx, h⟩) (fun h => Or.inr ⟨hx, h⟩)
      · rintro (⟨hx, -⟩ | ⟨hx, -⟩) <;> exact hx
    have hd : Disjoint B1 B2 := by
      apply Finset.disjoint_left.mpr
      intro x hx1 hx2
      exact Finset.disjoint_left.mp hdisj12 (Finset.mem_inter.mp hx1).2
        (Finset.mem_inter.mp hx2).2
    rw [heq, Finset.card_union_of_disjoint hd]
  have hN (S : Finset V) : (N S).card + 2 ≤ 2 * S.card + L.card := by
    simpa only [N, L] using Erdos547EC2.zhao_prop_7_11_part_two T hT S

  let firstBad := N (B1 ∪ {z})
  let secondBad := N (N B2)
  let badP := ((L ∪ Br) ∩ U2) ∪ firstBad ∪ secondBad
  let D2 := U2 \ badP
  have hfirst : firstBad.card ≤ 2 * B1.card + L.card := by
    have hn := hN (B1 ∪ {z})
    have hc : (B1 ∪ {z}).card ≤ B1.card + 1 := by
      simpa using Finset.card_union_le B1 {z}
    dsimp only [firstBad] at hn ⊢
    omega
  have hNB2 := hN B2
  have hsecondN := hN (N B2)
  have hsecond : secondBad.card + 6 ≤ 4 * B2.card + 3 * L.card := by
    dsimp only [secondBad]
    omega
  have hinitial : (((L ∪ Br) ∩ U2).card) ≤ L.card + Br.card := by
    calc
      ((L ∪ Br) ∩ U2).card ≤ (L ∪ Br).card :=
        Finset.card_le_card Finset.inter_subset_left
      _ ≤ L.card + Br.card := Finset.card_union_le _ _
  have hbadPsum : badP.card ≤
      ((L ∪ Br) ∩ U2).card + firstBad.card + secondBad.card := by
    dsimp only [badP]
    calc
      (((L ∪ Br) ∩ U2 ∪ firstBad) ∪ secondBad).card ≤
          (((L ∪ Br) ∩ U2) ∪ firstBad).card + secondBad.card :=
        Finset.card_union_le _ _
      _ ≤ (((L ∪ Br) ∩ U2).card + firstBad.card) + secondBad.card := by
        gcongr
        exact Finset.card_union_le _ _
  have hbadP : badP.card ≤ 11 * l := by
    have hB1 : B1.card ≤ Br.card := by
      exact Finset.card_le_card (Finset.inter_subset_left)
    have hB2 : B2.card ≤ Br.card := by
      exact Finset.card_le_card (Finset.inter_subset_left)
    calc
      badP.card ≤ ((L ∪ Br) ∩ U2).card + firstBad.card + secondBad.card := hbadPsum
      _ ≤ (L.card + Br.card) + (2 * B1.card + L.card) + secondBad.card := by
        omega
      _ ≤ 11 * l := by omega
  have hD2card0 := card_sdiff_lower_bound U2 badP
  have hD2card : 15 * l ≤ D2.card := by
    dsimp only [D2] at hD2card0 ⊢
    omega
  have hD2prop : ∀ v ∈ D2, v ∈ U2 ∧ T.degree v = 2 := by
    intro v hv
    have hvU2 := (Finset.mem_sdiff.mp hv).1
    have hvnot := (Finset.mem_sdiff.mp hv).2
    have hdegpos := hT.preconnected.degree_pos_of_nontrivial v
    refine ⟨hvU2, ?_⟩
    by_contra hne
    have hbadDegree : v ∈ (L ∪ Br) ∩ U2 := by
      refine Finset.mem_inter.mpr ⟨?_, hvU2⟩
      rw [Finset.mem_union]
      by_cases h1 : T.degree v = 1
      · left
        simpa only [L, Erdos547EC2.leafVertices, Finset.mem_filter,
          Finset.mem_univ, true_and]
      · right
        simp only [Br, Erdos547EC2.branchVertices, Finset.mem_filter,
          Finset.mem_univ, true_and]
        omega
    apply hvnot
    dsimp only [badP]
    simp only [Finset.mem_union]
    exact Or.inl (Or.inl hbadDegree)
  have hD2special : ∀ v ∈ D2, IsSpecialTwoPathCenter T v := by
    intro v hv
    refine ⟨(hD2prop v hv).2, ?_⟩
    intro x hx
    by_contra hnot
    have hxbr : x ∈ Br := by
      simp only [Br, Erdos547EC2.branchVertices, Finset.mem_filter,
        Finset.mem_univ, true_and]
      omega
    obtain ⟨u, huNv, hux⟩ := Finset.mem_biUnion.mp hx
    have hvU2 := (hD2prop v hv).1
    have huAdj : T.Adj v u := (T.mem_neighborFinset v u).mp huNv
    have huxAdj : T.Adj u x := (T.mem_neighborFinset u x).mp hux
    have huU1 : u ∈ U1 := hbi.symm.mem_of_mem_adj hvU2 huAdj
    have hxU2 : x ∈ U2 := hbi.mem_of_mem_adj huU1 huxAdj
    have hxB2 : x ∈ B2 := Finset.mem_inter.mpr ⟨hxbr, hxU2⟩
    have huNB2 : u ∈ N B2 := by
      apply Finset.mem_biUnion.mpr
      exact ⟨x, hxB2, (T.mem_neighborFinset x u).mpr huxAdj.symm⟩
    have hvSecond : v ∈ secondBad := by
      dsimp only [secondBad]
      apply Finset.mem_biUnion.mpr
      exact ⟨u, huNB2, (T.mem_neighborFinset u v).mpr huAdj.symm⟩
    exact (Finset.mem_sdiff.mp hv).2 (by
      dsimp only [badP]
      simp only [Finset.mem_union]
      exact Or.inr hvSecond)
  have hD2avoid : ∀ v ∈ D2, z ∉ twoPathVertices T v := by
    intro v hv hzpath
    rw [mem_twoPathVertices] at hzpath
    rcases hzpath with hzv | hvz
    · have hvU2 := (hD2prop v hv).1
      exact Finset.disjoint_left.mp hdisj12 hz (hzv ▸ hvU2)
    · have hzS : z ∈ B1 ∪ {z} := by simp
      have hvFirst : v ∈ firstBad := by
        dsimp only [firstBad]
        apply Finset.mem_biUnion.mpr
        exact ⟨z, hzS, (T.mem_neighborFinset z v).mpr hvz.symm⟩
      exact (Finset.mem_sdiff.mp hv).2 (by
        dsimp only [badP]
        simp only [Finset.mem_union]
        exact Or.inl (Or.inr hvFirst))
  have hD2conflict : ∀ x ∈ D2,
      (D2.filter fun y => ¬Disjoint (twoPathVertices T x) (twoPathVertices T y)).card ≤ 3 := by
    intro x hx
    apply card_conflicting_centers_le_three T hbi.symm D2 hD2prop hx
    intro u hxu
    by_contra hnot
    have huU1 := hbi.symm.mem_of_mem_adj (hD2prop x hx).1 hxu
    have huBr : u ∈ Br := by
      simp only [Br, Erdos547EC2.branchVertices, Finset.mem_filter,
        Finset.mem_univ, true_and]
      omega
    have huB1 : u ∈ B1 := Finset.mem_inter.mpr ⟨huBr, huU1⟩
    have hxFirst : x ∈ firstBad := by
      dsimp only [firstBad]
      apply Finset.mem_biUnion.mpr
      exact ⟨u, Finset.mem_union_left _ huB1,
        (T.mem_neighborFinset u x).mpr hxu.symm⟩
    exact (Finset.mem_sdiff.mp hx).2 (by
      dsimp only [badP]
      simp only [Finset.mem_union]
      exact Or.inl (Or.inr hxFirst))
  have hsupportNonempty : ∀ x ∈ D2, (twoPathVertices T x).Nonempty := by
    intro x hx
    exact ⟨x, by simp [twoPathVertices]⟩
  obtain ⟨P, hPD2, hPcard, hPpair⟩ :=
    exists_disjoint_support_packing (twoPathVertices T) D2 3 (5 * l)
      (by omega) hsupportNonempty hD2conflict (by omega)

  let Pends := P.biUnion fun p => T.neighborFinset p
  have hPends : Pends.card ≤ 10 * l := by
    calc
      Pends.card ≤ ∑ p ∈ P, (T.neighborFinset p).card := Finset.card_biUnion_le
      _ = ∑ _p ∈ P, 2 := by
        apply Finset.sum_congr rfl
        intro p hp
        simpa [T.card_neighborFinset_eq_degree, (hD2prop p (hPD2 hp)).2]
      _ = 10 * l := by simp [hPcard]; omega
  let nearB2 := N B2
  let baseBadQ := ((L ∪ Br) ∩ U1) ∪ {z} ∪ nearB2
  let badQ := baseBadQ ∪ Pends
  let D1 := U1 \ badQ
  have hnearB2 := hN B2
  have hinitQ : ((L ∪ Br) ∩ U1).card ≤
      (L ∩ U1).card + B1.card := by
    have hsub : (L ∪ Br) ∩ U1 ⊆ (L ∩ U1) ∪ B1 := by
      intro x hx
      simp only [Finset.mem_inter, Finset.mem_union] at hx ⊢
      rcases hx with ⟨hxL | hxB, hxU⟩
      · exact Or.inl ⟨hxL, hxU⟩
      · have hxB1 : x ∈ B1 := by
          dsimp only [B1]
          exact Finset.mem_inter.mpr ⟨hxB, hxU⟩
        exact Or.inr hxB1
    exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hL1 : (L ∩ U1).card ≤ L.card :=
    Finset.card_le_card Finset.inter_subset_left
  have hbaseBadQsum : baseBadQ.card ≤
      ((L ∪ Br) ∩ U1).card + 1 + nearB2.card := by
    dsimp only [baseBadQ]
    calc
      ((((L ∪ Br) ∩ U1) ∪ {z}) ∪ nearB2).card ≤
          (((L ∪ Br) ∩ U1) ∪ {z}).card + nearB2.card :=
        Finset.card_union_le _ _
      _ ≤ (((L ∪ Br) ∩ U1).card + 1) + nearB2.card := by
        gcongr
        simpa using Finset.card_union_le ((L ∪ Br) ∩ U1) {z}
  have hbaseBadQ : baseBadQ.card ≤ 4 * l := by
    have hnearB2' : nearB2.card + 2 ≤ 2 * B2.card + L.card := by
      simpa only [nearB2] using hnearB2
    omega
  have hbadQsum : badQ.card ≤ baseBadQ.card + Pends.card := by
    dsimp only [badQ]
    exact Finset.card_union_le _ _
  have hbadQ : badQ.card ≤ 14 * l := by omega
  have hD1card0 := card_sdiff_lower_bound U1 badQ
  have hD1card : 12 * l ≤ D1.card := by
    dsimp only [D1] at hD1card0 ⊢
    omega
  have hD1prop : ∀ v ∈ D1, v ∈ U1 ∧ T.degree v = 2 := by
    intro v hv
    have hvU1 := (Finset.mem_sdiff.mp hv).1
    have hvnot := (Finset.mem_sdiff.mp hv).2
    have hdegpos := hT.preconnected.degree_pos_of_nontrivial v
    refine ⟨hvU1, ?_⟩
    by_contra hne
    have hbadDegree : v ∈ (L ∪ Br) ∩ U1 := by
      refine Finset.mem_inter.mpr ⟨?_, hvU1⟩
      rw [Finset.mem_union]
      by_cases h1 : T.degree v = 1
      · left
        simpa only [L, Erdos547EC2.leafVertices, Finset.mem_filter,
          Finset.mem_univ, true_and]
      · right
        simp only [Br, Erdos547EC2.branchVertices, Finset.mem_filter,
          Finset.mem_univ, true_and]
        omega
    apply hvnot
    dsimp only [badQ, baseBadQ]
    simp only [Finset.mem_union]
    exact Or.inl (Or.inl (Or.inl hbadDegree))
  have hD1avoid : ∀ v ∈ D1, z ∉ twoPathVertices T v := by
    intro v hv hzpath
    rw [mem_twoPathVertices] at hzpath
    rcases hzpath with hzv | hvz
    · have hzbad : z ∈ badQ := by
        dsimp only [badQ, baseBadQ]
        simp
      exact (Finset.mem_sdiff.mp hv).2 (hzv ▸ hzbad)
    · have hvU1 := (hD1prop v hv).1
      have hzU2 := hbi.mem_of_mem_adj hvU1 hvz
      exact Finset.disjoint_left.mp hdisj12 hz hzU2
  have hD1conflict : ∀ x ∈ D1,
      (D1.filter fun y => ¬Disjoint (twoPathVertices T x) (twoPathVertices T y)).card ≤ 3 := by
    intro x hx
    apply card_conflicting_centers_le_three T hbi D1 hD1prop hx
    intro u hxu
    have huU2 := hbi.mem_of_mem_adj (hD1prop x hx).1 hxu
    by_contra hnot
    have huBr : u ∈ Br := by
      simp only [Br, Erdos547EC2.branchVertices, Finset.mem_filter,
        Finset.mem_univ, true_and]
      omega
    have huB2 : u ∈ B2 := Finset.mem_inter.mpr ⟨huBr, huU2⟩
    have hxNear : x ∈ nearB2 := by
      dsimp only [nearB2]
      apply Finset.mem_biUnion.mpr
      exact ⟨u, huB2, (T.mem_neighborFinset u x).mpr hxu.symm⟩
    exact (Finset.mem_sdiff.mp hx).2 (by
      dsimp only [badQ, baseBadQ]
      simp only [Finset.mem_union]
      exact Or.inl (Or.inr hxNear))
  have hsupportNonempty1 : ∀ x ∈ D1, (twoPathVertices T x).Nonempty := by
    intro x hx
    exact ⟨x, by simp [twoPathVertices]⟩
  obtain ⟨Q, hQD1, hQcard, hQpair⟩ :=
    exists_disjoint_support_packing (twoPathVertices T) D1 3 (4 * l)
      (by omega) hsupportNonempty1 hD1conflict (by omega)

  have hcross : ∀ p ∈ (P : Set V), ∀ q ∈ (Q : Set V), p ≠ q →
      Disjoint (twoPathVertices T p) (twoPathVertices T q) := by
    intro p hp q hq hpq
    apply Finset.disjoint_left.mpr
    intro w hwp hwq
    rw [mem_twoPathVertices] at hwp hwq
    have hpD := hPD2 hp
    have hqD := hQD1 hq
    have hpU2 := (hD2prop p hpD).1
    have hqU1 := (hD1prop q hqD).1
    have hqNotBad := (Finset.mem_sdiff.mp hqD).2
    rcases hwp with hwpEq | hpw
    · subst w
      rcases hwq with hpq' | hqp
      · exact hpq hpq'
      · have hqPend : q ∈ Pends := by
          dsimp only [Pends]
          apply Finset.mem_biUnion.mpr
          exact ⟨p, hp, (T.mem_neighborFinset p q).mpr hqp.symm⟩
        exact hqNotBad (by
          dsimp only [badQ]
          exact Finset.mem_union_right _ hqPend)
    · rcases hwq with hwqEq | hqw
      · subst w
        have hqPend : q ∈ Pends := by
          dsimp only [Pends]
          apply Finset.mem_biUnion.mpr
          exact ⟨p, hp, (T.mem_neighborFinset p q).mpr hpw⟩
        exact hqNotBad (by
          dsimp only [badQ]
          exact Finset.mem_union_right _ hqPend)
      · have hwU1 := hbi.symm.mem_of_mem_adj hpU2 hpw
        have hwU2 := hbi.mem_of_mem_adj hqU1 hqw
        exact Finset.disjoint_left.mp hdisj12 hwU1 hwU2
  have hpairUnion : ((P ∪ Q : Finset V) : Set V).PairwiseDisjoint (twoPathVertices T) := by
    simpa only [Finset.coe_union] using hPpair.union hQpair hcross
  refine ⟨
    { P := P
      Q := Q
      card_P := hPcard
      card_Q := hQcard
      P_mem := fun p hp => (hD2prop p (hPD2 hp)).1
      Q_mem := fun q hq => (hD1prop q (hQD1 hq)).1
      P_special := fun p hp => hD2special p (hPD2 hp)
      Q_degree_two := fun q hq => (hD1prop q (hQD1 hq)).2
      supports_pairwise := hpairUnion
      avoid_root := ?_ }⟩
  intro c hc
  simp only [Finset.mem_union] at hc
  rcases hc with hcP | hcQ
  · exact hD2avoid c (hPD2 hcP)
  · exact hD1avoid c (hQD1 hcQ)

end Erdos547b.ZhaoLemma710Alt

#print axioms Erdos547b.ZhaoLemma710Alt.zhao_proposition_7_11_part_three


/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

open scoped SimpleGraph

noncomputable section

namespace Erdos547b.ZhaoLemma710Alt

open Finset SimpleGraph

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The union of the supports of the two-paths centred at `C`. -/
def twoPathSupport (T : SimpleGraph V) [DecidableRel T.Adj] (C : Finset V) : Finset V :=
  C.biUnion (twoPathVertices T)

/-- The protected set used when the special two-paths and the root are deleted. -/
def protectedTwoPathSet (T : SimpleGraph V) [DecidableRel T.Adj]
    (z : V) (C : Finset V) : Finset V :=
  insert z (twoPathSupport T C)

@[simp] theorem mem_twoPathVertices_boundary {T : SimpleGraph V} [DecidableRel T.Adj]
    {u v : V} : u ∈ twoPathVertices T v ↔ u = v ∨ T.Adj v u := by
  simp [twoPathVertices]

@[simp] theorem mem_twoPathSupport {T : SimpleGraph V} [DecidableRel T.Adj]
    {C : Finset V} {u : V} : u ∈ twoPathSupport T C ↔
      ∃ c ∈ C, u = c ∨ T.Adj c u := by
  simp [twoPathSupport, mem_twoPathVertices_boundary]

@[simp] theorem mem_protectedTwoPathSet {T : SimpleGraph V} [DecidableRel T.Adj]
    {z : V} {C : Finset V} {u : V} : u ∈ protectedTwoPathSet T z C ↔
      u = z ∨ ∃ c ∈ C, u = c ∨ T.Adj c u := by
  simp [protectedTwoPathSet]

/-- A vertex outside the selected supports but adjacent to one of them has
degree at most two.  This is exactly what the extra clause in Zhao's
definition of a special two-path is designed to guarantee. -/
theorem degree_le_two_of_adj_twoPathSupport
    {T : SimpleGraph V} [DecidableRel T.Adj]
    {C : Finset V} (hspecial : ∀ c ∈ C, IsSpecialTwoPathCenter T c)
    {x y : V} (hx : x ∉ twoPathSupport T C)
    (hy : y ∈ twoPathSupport T C) (hxy : T.Adj x y) :
    T.degree x ≤ 2 := by
  obtain ⟨c, hcC, hyc | hcy⟩ := mem_twoPathSupport.mp hy
  · subst y
    have hxc : x ∈ T.neighborFinset c := (T.mem_neighborFinset c x).mpr hxy.symm
    exact (hx (Finset.mem_biUnion.mpr ⟨c, hcC, by simp [twoPathVertices, hxc]⟩)).elim
  · exact (hspecial c hcC).2 x (Finset.mem_biUnion.mpr
      ⟨y, (T.mem_neighborFinset c y).mpr hcy,
        (T.mem_neighborFinset y x).mpr hxy.symm⟩)

/-- Boundary sparsity of the protected set.  Outside the protected set, a
vertex with at least two protected neighbours has degree at most two.  In
fact, the proof shows the stronger fact that one neighbour in a path support
(as opposed to the distinguished root alone) suffices. -/
theorem boundary_sparse_of_special_twoPathCenters
    {T : SimpleGraph V} [DecidableRel T.Adj]
    {z : V} {C : Finset V}
    (hspecial : ∀ c ∈ C, IsSpecialTwoPathCenter T c)
    {x : V} (hx : x ∉ protectedTwoPathSet T z C) :
    (T.neighborFinset x ∩ protectedTwoPathSet T z C).card ≤ 1 ∨
      T.degree x ≤ 2 := by
  classical
  by_cases hcard : (T.neighborFinset x ∩ protectedTwoPathSet T z C).card ≤ 1
  · exact Or.inl hcard
  · right
    have htwo : 2 ≤ (T.neighborFinset x ∩ protectedTwoPathSet T z C).card := by omega
    have hnotSubset :
        ¬T.neighborFinset x ∩ protectedTwoPathSet T z C ⊆ {z} := by
      intro hsub
      have hle := Finset.card_le_card hsub
      simp at hle
      omega
    obtain ⟨y, hyInter, hyz⟩ := Finset.not_subset.mp hnotSubset
    have hyN : y ∈ T.neighborFinset x := (Finset.mem_inter.mp hyInter).1
    have hyProtected : y ∈ protectedTwoPathSet T z C :=
      (Finset.mem_inter.mp hyInter).2
    have hySupport : y ∈ twoPathSupport T C := by
      rw [protectedTwoPathSet, Finset.mem_insert] at hyProtected
      exact hyProtected.resolve_left (by simpa using hyz)
    have hxSupport : x ∉ twoPathSupport T C := by
      intro hxS
      exact hx (by simp [protectedTwoPathSet, hxS])
    exact degree_le_two_of_adj_twoPathSupport hspecial hxSupport hySupport
      ((T.mem_neighborFinset x y).mp hyN)

/-- Implication form of the boundary-sparsity theorem, convenient when the
two protected neighbours have already been exhibited. -/
theorem degree_le_two_of_two_protected_neighbors
    {T : SimpleGraph V} [DecidableRel T.Adj]
    {z : V} {C : Finset V}
    (hspecial : ∀ c ∈ C, IsSpecialTwoPathCenter T c)
    {x : V} (hx : x ∉ protectedTwoPathSet T z C)
    (hcard : 2 ≤ (T.neighborFinset x ∩ protectedTwoPathSet T z C).card) :
    T.degree x ≤ 2 := by
  rcases boundary_sparse_of_special_twoPathCenters hspecial hx with hle | hdeg
  · omega
  · exact hdeg

/-- Contrapositive form used for a remaining forest whose internal vertices
all have degree greater than two. -/
theorem card_protected_neighbors_le_one_of_two_lt_degree
    {T : SimpleGraph V} [DecidableRel T.Adj]
    {z : V} {C : Finset V}
    (hspecial : ∀ c ∈ C, IsSpecialTwoPathCenter T c)
    {x : V} (hx : x ∉ protectedTwoPathSet T z C)
    (hdeg : 2 < T.degree x) :
    (T.neighborFinset x ∩ protectedTwoPathSet T z C).card ≤ 1 := by
  rcases boundary_sparse_of_special_twoPathCenters hspecial hx with hle | hsmall
  · exact hle
  · omega

/-- The centre of a selected degree-two path has no neighbour outside the
protected set. -/
theorem neighborFinset_center_subset_protected
    {T : SimpleGraph V} [DecidableRel T.Adj]
    {z : V} {C : Finset V} {c : V} (hc : c ∈ C) :
    T.neighborFinset c ⊆ protectedTwoPathSet T z C := by
  intro y hy
  rw [protectedTwoPathSet, Finset.mem_insert]
  right
  exact Finset.mem_biUnion.mpr ⟨c, hc, by simp [twoPathVertices, hy]⟩

/-- Adjacency formulation of `neighborFinset_center_subset_protected`. -/
theorem center_has_no_neighbor_outside_protected
    {T : SimpleGraph V} [DecidableRel T.Adj]
    {z : V} {C : Finset V} {c x : V} (hc : c ∈ C)
    (hx : x ∉ protectedTwoPathSet T z C) :
    ¬T.Adj c x := by
  intro hcx
  exact hx (neighborFinset_center_subset_protected hc
    ((T.mem_neighborFinset c x).mpr hcx))

end Erdos547b.ZhaoLemma710Alt

#print axioms Erdos547b.ZhaoLemma710Alt.boundary_sparse_of_special_twoPathCenters
#print axioms Erdos547b.ZhaoLemma710Alt.degree_le_two_of_two_protected_neighbors
#print axioms Erdos547b.ZhaoLemma710Alt.card_protected_neighbors_le_one_of_two_lt_degree
#print axioms Erdos547b.ZhaoLemma710Alt.center_has_no_neighbor_outside_protected


/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

/-! # The forest-surgery step in Zhao's Lemma 7.10 -/

open scoped SimpleGraph

noncomputable section

namespace Erdos547b.ZhaoSurgeryAlt

open Finset SimpleGraph

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- A two-edge path with the three distinct vertices named. -/
structure TwoPath (T : SimpleGraph V) where
  left : V
  center : V
  right : V
  left_ne_center : left ≠ center
  center_ne_right : center ≠ right
  left_ne_right : left ≠ right
  adj_left : T.Adj left center
  adj_right : T.Adj center right

namespace TwoPath

variable {T : SimpleGraph V}

def vertices (P : TwoPath T) : Finset V := {P.left, P.center, P.right}

@[simp] theorem left_mem_vertices (P : TwoPath T) : P.left ∈ P.vertices := by
  simp [vertices]

@[simp] theorem center_mem_vertices (P : TwoPath T) : P.center ∈ P.vertices := by
  simp [vertices]

@[simp] theorem right_mem_vertices (P : TwoPath T) : P.right ∈ P.vertices := by
  simp [vertices]

theorem card_vertices (P : TwoPath T) : #P.vertices = 3 := by
  simp [vertices, P.left_ne_center, P.left_ne_right, P.center_ne_right]

/-- A degree-two centre of a named two-path has no neighbour other than its
two displayed endpoints. -/
theorem eq_left_or_right_of_adj_center (P : TwoPath T)
    (hcard : (T.neighborSet P.center).ncard = 2)
    {x : V} (hx : T.Adj x P.center) : x = P.left ∨ x = P.right := by
  have hsub : ({P.left, P.right} : Set V) ⊆ T.neighborSet P.center := by
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact P.adj_left.symm
    · exact P.adj_right
  have hpair : ({P.left, P.right} : Set V).ncard = 2 :=
    Set.ncard_pair P.left_ne_right
  have heq : ({P.left, P.right} : Set V) = T.neighborSet P.center :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [hcard, hpair])
  have : x ∈ ({P.left, P.right} : Set V) := by
    rw [heq]
    exact hx.symm
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using this

/-- Relative to a root different from a degree-two centre, the endpoints of
a two-path cannot lie on the same level. -/
theorem endpoint_dist_ne (P : TwoPath T) (hT : T.IsTree) (z : V)
    (hz : P.center ≠ z) (hcard : (T.neighborSet P.center).ncard = 2) :
    T.dist z P.left ≠ T.dist z P.right := by
  intro heq
  rcases hT.dist_eq_dist_add_one_of_adj z P.adj_left with hL | hL <;>
    rcases hT.dist_eq_dist_add_one_of_adj z P.adj_right with hR | hR
  · omega
  · let p := Erdos547b.TreePartition.parent hT z hz
    have hpAdj : T.Adj p P.center :=
      Erdos547b.TreePartition.parent_adj hT z hz
    have hpDist : T.dist z p + 1 = T.dist z P.center :=
      Erdos547b.TreePartition.parent_dist_add_one hT z hz
    rcases P.eq_left_or_right_of_adj_center hcard hpAdj with hp | hp
    · dsimp [p] at hp hpDist
      rw [hp] at hpDist
      omega
    · dsimp [p] at hp hpDist
      rw [hp] at hpDist
      omega
  · have hleft : P.left = Erdos547b.TreePartition.parent hT z hz :=
      Erdos547b.TreePartition.eq_parent_of_adj_of_dist_add_one hT z hz
        P.adj_left hL.symm
    have hright : P.right = Erdos547b.TreePartition.parent hT z hz :=
      Erdos547b.TreePartition.eq_parent_of_adj_of_dist_add_one hT z hz
        P.adj_right.symm hR.symm
    exact P.left_ne_right (hleft.trans hright.symm)
  · omega

/-- The endpoint closer to the chosen root. -/
def nearEndpoint (P : TwoPath T) (z : V) : V :=
  if T.dist z P.left < T.dist z P.right then P.left else P.right

/-- The other endpoint. -/
def farEndpoint (P : TwoPath T) (z : V) : V :=
  if T.dist z P.left < T.dist z P.right then P.right else P.left

theorem nearEndpoint_mem_vertices (P : TwoPath T) (z : V) :
    P.nearEndpoint z ∈ P.vertices := by
  simp only [nearEndpoint]
  split_ifs
  · exact P.left_mem_vertices
  · exact P.right_mem_vertices

theorem farEndpoint_mem_vertices (P : TwoPath T) (z : V) :
    P.farEndpoint z ∈ P.vertices := by
  simp only [farEndpoint]
  split_ifs
  · exact P.right_mem_vertices
  · exact P.left_mem_vertices

theorem nearEndpoint_eq_left_or_right (P : TwoPath T) (z : V) :
    P.nearEndpoint z = P.left ∨ P.nearEndpoint z = P.right := by
  simp only [nearEndpoint]
  split_ifs <;> simp

theorem farEndpoint_eq_left_or_right (P : TwoPath T) (z : V) :
    P.farEndpoint z = P.left ∨ P.farEndpoint z = P.right := by
  simp only [farEndpoint]
  split_ifs <;> simp

theorem endpoints_eq_near_far (P : TwoPath T) (z : V) :
    ({P.left, P.right} : Finset V) = {P.nearEndpoint z, P.farEndpoint z} := by
  by_cases h : T.dist z P.left < T.dist z P.right
  · simp [nearEndpoint, farEndpoint, h]
  · simp [nearEndpoint, farEndpoint, h, Finset.pair_comm]

/-- The two-path is oriented away from the root: its centre is one level
after the near endpoint, and the far endpoint one level after that. -/
theorem near_center_far_dist (P : TwoPath T) (hT : T.IsTree) (z : V)
    (hz : P.center ≠ z) (hcard : (T.neighborSet P.center).ncard = 2) :
    T.dist z (P.nearEndpoint z) + 1 = T.dist z P.center ∧
      T.dist z (P.nearEndpoint z) + 2 = T.dist z (P.farEndpoint z) := by
  have hne := P.endpoint_dist_ne hT z hz hcard
  rcases hT.dist_eq_dist_add_one_of_adj z P.adj_left with hL | hL <;>
    rcases hT.dist_eq_dist_add_one_of_adj z P.adj_right with hR | hR
  · have hlt : T.dist z P.right < T.dist z P.left := by omega
    have hnlt : ¬T.dist z P.left < T.dist z P.right := Nat.not_lt.mpr hlt.le
    simp only [nearEndpoint, farEndpoint, if_neg hnlt]
    omega
  · exfalso
    apply hne
    omega
  · exfalso
    apply hne
    omega
  · have hlt : T.dist z P.left < T.dist z P.right := by omega
    simp only [nearEndpoint, farEndpoint, if_pos hlt]
    omega

end TwoPath

/-- Inclusion of the first `4*l` indices into the `4*l+k` `P`-paths. -/
def initialPIndex (l k : ℕ) (i : Fin (4 * l)) : Fin (4 * l + k) :=
  Fin.castLE (Nat.le_add_right (4 * l) k) i

/-- Index of the `i`th exceptional path, i.e. path number `4*l+i`. -/
def exceptionalPIndex (l : ℕ) {k : ℕ} (i : Fin k) : Fin (4 * l + k) :=
  ⟨4 * l + i, Nat.add_lt_add_left i.isLt (4 * l)⟩

@[simp] theorem initialPIndex_val (l k : ℕ) (i : Fin (4 * l)) :
    (initialPIndex l k i).val = i.val := rfl

@[simp] theorem exceptionalPIndex_val (l : ℕ) {k : ℕ} (i : Fin k) :
    (exceptionalPIndex l i).val = 4 * l + i.val := rfl

theorem initialPIndex_ne_exceptionalPIndex (l : ℕ) {k : ℕ}
    (i : Fin (4 * l)) (j : Fin k) :
    initialPIndex l k i ≠ exceptionalPIndex l j := by
  intro h
  have := congrArg Fin.val h
  simp only [initialPIndex_val, exceptionalPIndex_val] at this
  omega

/-- Data for the combinatorial surgery.  The three disjointness fields say
that all `P`- and `Q`-paths are mutually vertex-disjoint. -/
structure SurgeryData (T : SimpleGraph V) (U₁ U₂ : Finset V) (z : V)
    (l k : ℕ) where
  tree : T.IsTree
  bipartite : T.IsBipartiteWith (U₁ : Set V) (U₂ : Set V)
  cover : U₁ ∪ U₂ = Finset.univ
  z_mem : z ∈ U₁
  P : Fin (4 * l + k) → TwoPath T
  Q : Fin (4 * l) → TwoPath T
  p_left_mem : ∀ i, (P i).left ∈ U₁
  p_center_mem : ∀ i, (P i).center ∈ U₂
  p_right_mem : ∀ i, (P i).right ∈ U₁
  q_left_mem : ∀ i, (Q i).left ∈ U₂
  q_center_mem : ∀ i, (Q i).center ∈ U₁
  q_right_mem : ∀ i, (Q i).right ∈ U₂
  q_degree_two : ∀ i, (T.neighborSet (Q i).center).ncard = 2
  p_disjoint : ∀ i j, i ≠ j → Disjoint (P i).vertices (P j).vertices
  q_disjoint : ∀ i j, i ≠ j → Disjoint (Q i).vertices (Q j).vertices
  pq_disjoint : ∀ i j, Disjoint (P i).vertices (Q j).vertices
  z_avoid_p : ∀ i, z ∉ (P i).vertices
  z_avoid_q : ∀ i, z ∉ (Q i).vertices
  p_special : ∀ i,
    (T.neighborSet (P i).center).ncard = 2 ∧
      ∀ x, (T.Adj x (P i).left ∨ T.Adj x (P i).right) →
        (T.neighborSet x).ncard ≤ 2

namespace SurgeryData

variable {T : SimpleGraph V} {U₁ U₂ : Finset V} {z : V} {l k : ℕ}

def deletedP (D : SurgeryData T U₁ U₂ z l k) : Finset V :=
  Finset.univ.image fun i : Fin (4 * l) => (D.P (initialPIndex l k i)).center

def deletedQ (D : SurgeryData T U₁ U₂ z l k) : Finset V :=
  Finset.univ.image fun i : Fin (4 * l) => (D.Q i).center

def deleted (D : SurgeryData T U₁ U₂ z l k) : Finset V :=
  D.deletedP ∪ D.deletedQ

def forest (D : SurgeryData T U₁ U₂ z l k) :
    SimpleGraph {v : V // v ∉ D.deleted} :=
  T.induce (D.deleted : Set V)ᶜ

def forestLeft (D : SurgeryData T U₁ U₂ z l k) : Finset V :=
  U₁ \ D.deletedQ

def forestRight (D : SurgeryData T U₁ U₂ z l k) : Finset V :=
  U₂ \ D.deletedP

private theorem p_center_injective (D : SurgeryData T U₁ U₂ z l k) :
    Function.Injective fun i : Fin (4 * l + k) => (D.P i).center := by
  intro i j hij
  by_contra hne
  have hd := D.p_disjoint i j hne
  have hm : (D.P i).center ∈ (D.P j).vertices := by
    simpa only [hij] using (D.P j).center_mem_vertices
  exact Finset.disjoint_left.mp hd
    (D.P i).center_mem_vertices hm

private theorem q_center_injective (D : SurgeryData T U₁ U₂ z l k) :
    Function.Injective fun i : Fin (4 * l) => (D.Q i).center := by
  intro i j hij
  by_contra hne
  have hd := D.q_disjoint i j hne
  have hm : (D.Q i).center ∈ (D.Q j).vertices := by
    simpa only [hij] using (D.Q j).center_mem_vertices
  exact Finset.disjoint_left.mp hd
    (D.Q i).center_mem_vertices hm

theorem card_deletedP (D : SurgeryData T U₁ U₂ z l k) :
    #D.deletedP = 4 * l := by
  classical
  rw [deletedP, Finset.card_image_iff.mpr]
  · simp
  · intro i _ j _ hij
    have hidx := p_center_injective D hij
    have hv : i.val = j.val := by
      simpa [initialPIndex] using
        congrArg (fun x : Fin (4 * l + k) => x.val) hidx
    exact Fin.ext hv

theorem card_deletedQ (D : SurgeryData T U₁ U₂ z l k) :
    #D.deletedQ = 4 * l := by
  classical
  rw [deletedQ, Finset.card_image_iff.mpr]
  · simp
  · exact (q_center_injective D).injOn

theorem deletedP_subset (D : SurgeryData T U₁ U₂ z l k) :
    D.deletedP ⊆ U₂ := by
  intro v hv
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hv
  exact D.p_center_mem _

theorem deletedQ_subset (D : SurgeryData T U₁ U₂ z l k) :
    D.deletedQ ⊆ U₁ := by
  intro v hv
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hv
  exact D.q_center_mem _

theorem disjoint_deletedP_deletedQ (D : SurgeryData T U₁ U₂ z l k) :
    Disjoint D.deletedP D.deletedQ := by
  rw [Finset.disjoint_left]
  intro x hxP hxQ
  exact Set.disjoint_left.mp D.bipartite.disjoint
    (deletedQ_subset D hxQ) (deletedP_subset D hxP)

theorem forest_isAcyclic (D : SurgeryData T U₁ U₂ z l k) :
    D.forest.IsAcyclic := by
  exact D.tree.isAcyclic.induce _

theorem card_forestLeft (D : SurgeryData T U₁ U₂ z l k) :
    #D.forestLeft = #U₁ - 4 * l := by
  rw [forestLeft, Finset.card_sdiff_of_subset (deletedQ_subset D), card_deletedQ]

theorem card_forestRight (D : SurgeryData T U₁ U₂ z l k) :
    #D.forestRight = #U₂ - 4 * l := by
  rw [forestRight, Finset.card_sdiff_of_subset (deletedP_subset D), card_deletedP]

theorem mem_forestLeft_iff (D : SurgeryData T U₁ U₂ z l k) (v : V) :
    v ∈ D.forestLeft ↔ v ∈ U₁ ∧ v ∉ D.deleted := by
  rw [forestLeft, Finset.mem_sdiff]
  constructor
  · rintro ⟨hvU, hvQ⟩
    refine ⟨hvU, ?_⟩
    simp only [deleted, Finset.mem_union]
    rintro (hvP | hvQ')
    · exact Set.disjoint_left.mp D.bipartite.disjoint hvU (deletedP_subset D hvP)
    · exact hvQ hvQ'
  · rintro ⟨hvU, hv⟩
    exact ⟨hvU, fun hvQ => hv (by simp [deleted, hvQ])⟩

theorem mem_forestRight_iff (D : SurgeryData T U₁ U₂ z l k) (v : V) :
    v ∈ D.forestRight ↔ v ∈ U₂ ∧ v ∉ D.deleted := by
  rw [forestRight, Finset.mem_sdiff]
  constructor
  · rintro ⟨hvU, hvP⟩
    refine ⟨hvU, ?_⟩
    simp only [deleted, Finset.mem_union]
    rintro (hvP' | hvQ)
    · exact hvP hvP'
    · exact Set.disjoint_left.mp D.bipartite.disjoint (deletedQ_subset D hvQ) hvU
  · rintro ⟨hvU, hv⟩
    exact ⟨hvU, fun hvP => hv (by simp [deleted, hvP])⟩

private theorem exceptional_vertex_not_deletedP
    (D : SurgeryData T U₁ U₂ z l k) (i : Fin k)
    {v : V} (hv : v ∈ (D.P (exceptionalPIndex l i)).vertices) :
    v ∉ D.deletedP := by
  intro hvdel
  obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hvdel
  have hd := D.p_disjoint (exceptionalPIndex l i) (initialPIndex l k j)
    (initialPIndex_ne_exceptionalPIndex l j i).symm
  exact Finset.disjoint_left.mp hd hv
    (hj ▸ (D.P (initialPIndex l k j)).center_mem_vertices)

private theorem exceptional_vertex_not_deletedQ
    (D : SurgeryData T U₁ U₂ z l k) (i : Fin k)
    {v : V} (hv : v ∈ (D.P (exceptionalPIndex l i)).vertices) :
    v ∉ D.deletedQ := by
  intro hvdel
  obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hvdel
  have hd := D.pq_disjoint (exceptionalPIndex l i) j
  exact Finset.disjoint_left.mp hd hv (hj ▸ (D.Q j).center_mem_vertices)

theorem exceptional_vertex_not_deleted
    (D : SurgeryData T U₁ U₂ z l k) (i : Fin k)
    {v : V} (hv : v ∈ (D.P (exceptionalPIndex l i)).vertices) :
    v ∉ D.deleted := by
  simp only [deleted, Finset.mem_union, not_or]
  exact ⟨exceptional_vertex_not_deletedP D i hv,
    exceptional_vertex_not_deletedQ D i hv⟩

theorem exceptional_path_survives
    (D : SurgeryData T U₁ U₂ z l k) (i : Fin k) :
    let P := D.P (exceptionalPIndex l i)
    D.forest.Adj
        ⟨P.left, exceptional_vertex_not_deleted D i P.left_mem_vertices⟩
        ⟨P.center, exceptional_vertex_not_deleted D i P.center_mem_vertices⟩ ∧
      D.forest.Adj
        ⟨P.center, exceptional_vertex_not_deleted D i P.center_mem_vertices⟩
        ⟨P.right, exceptional_vertex_not_deleted D i P.right_mem_vertices⟩ := by
  dsimp [forest]
  exact ⟨(D.P (exceptionalPIndex l i)).adj_left,
    (D.P (exceptionalPIndex l i)).adj_right⟩

/-! ## The parent/grandparent relation for exceptional paths -/

abbrev exceptionalPath (D : SurgeryData T U₁ U₂ z l k) (i : Fin k) : TwoPath T :=
  D.P (exceptionalPIndex l i)

/-- Zhao's `tᵢ`, the endpoint of the exceptional path closer to the root. -/
def exceptionalNearEndpoint (D : SurgeryData T U₁ U₂ z l k) (i : Fin k) : V :=
  (D.exceptionalPath i).nearEndpoint z

/-- The other endpoint of the exceptional path. -/
def exceptionalFarEndpoint (D : SurgeryData T U₁ U₂ z l k) (i : Fin k) : V :=
  (D.exceptionalPath i).farEndpoint z

theorem exceptional_center_ne_root
    (D : SurgeryData T U₁ U₂ z l k) (i : Fin k) :
    (D.exceptionalPath i).center ≠ z := by
  intro h
  have hzU₂ : z ∈ U₂ := by
    rw [← h]
    exact D.p_center_mem _
  exact Set.disjoint_left.mp D.bipartite.disjoint D.z_mem hzU₂

theorem exceptionalNearEndpoint_mem_vertices
    (D : SurgeryData T U₁ U₂ z l k) (i : Fin k) :
    D.exceptionalNearEndpoint i ∈ (D.exceptionalPath i).vertices :=
  (D.exceptionalPath i).nearEndpoint_mem_vertices z

theorem exceptionalFarEndpoint_mem_vertices
    (D : SurgeryData T U₁ U₂ z l k) (i : Fin k) :
    D.exceptionalFarEndpoint i ∈ (D.exceptionalPath i).vertices :=
  (D.exceptionalPath i).farEndpoint_mem_vertices z

theorem exceptionalNearEndpoint_mem_U₁
    (D : SurgeryData T U₁ U₂ z l k) (i : Fin k) :
    D.exceptionalNearEndpoint i ∈ U₁ := by
  rcases (D.exceptionalPath i).nearEndpoint_eq_left_or_right z with h | h
  · rw [exceptionalNearEndpoint, h]
    exact D.p_left_mem _
  · rw [exceptionalNearEndpoint, h]
    exact D.p_right_mem _

theorem exceptionalFarEndpoint_mem_U₁
    (D : SurgeryData T U₁ U₂ z l k) (i : Fin k) :
    D.exceptionalFarEndpoint i ∈ U₁ := by
  rcases (D.exceptionalPath i).farEndpoint_eq_left_or_right z with h | h
  · rw [exceptionalFarEndpoint, h]
    exact D.p_left_mem _
  · rw [exceptionalFarEndpoint, h]
    exact D.p_right_mem _

theorem exceptionalNearEndpoint_ne_root
    (D : SurgeryData T U₁ U₂ z l k) (i : Fin k) :
    D.exceptionalNearEndpoint i ≠ z := by
  intro h
  apply D.z_avoid_p (exceptionalPIndex l i)
  exact Eq.mp
    (congrArg (fun x : V => x ∈ (D.exceptionalPath i).vertices) h)
    (D.exceptionalNearEndpoint_mem_vertices i)

/-- The exact level relation that justifies Zhao's phrase “the endpoint
closer to `z`”. -/
theorem exceptional_near_center_far_dist
    (D : SurgeryData T U₁ U₂ z l k) (i : Fin k) :
    T.dist z (D.exceptionalNearEndpoint i) + 1 =
        T.dist z (D.exceptionalPath i).center ∧
      T.dist z (D.exceptionalNearEndpoint i) + 2 =
        T.dist z (D.exceptionalFarEndpoint i) := by
  exact (D.exceptionalPath i).near_center_far_dist D.tree z
    (D.exceptional_center_ne_root i) (D.p_special _).1

/-- Zhao's `sᵢ = p(tᵢ)`. -/
def exceptionalParent (D : SurgeryData T U₁ U₂ z l k) (i : Fin k) : V :=
  Erdos547b.TreePartition.parent D.tree z (D.exceptionalNearEndpoint_ne_root i)

theorem exceptionalParent_adj_near
    (D : SurgeryData T U₁ U₂ z l k) (i : Fin k) :
    T.Adj (D.exceptionalParent i) (D.exceptionalNearEndpoint i) :=
  Erdos547b.TreePartition.parent_adj D.tree z (D.exceptionalNearEndpoint_ne_root i)

theorem exceptionalParent_dist_add_one
    (D : SurgeryData T U₁ U₂ z l k) (i : Fin k) :
    T.dist z (D.exceptionalParent i) + 1 =
      T.dist z (D.exceptionalNearEndpoint i) :=
  Erdos547b.TreePartition.parent_dist_add_one D.tree z
    (D.exceptionalNearEndpoint_ne_root i)

theorem exceptionalParent_mem_U₂
    (D : SurgeryData T U₁ U₂ z l k) (i : Fin k) :
    D.exceptionalParent i ∈ U₂ :=
  D.bipartite.mem_of_mem_adj (D.exceptionalNearEndpoint_mem_U₁ i)
    (D.exceptionalParent_adj_near i).symm

theorem exceptionalParent_ne_root
    (D : SurgeryData T U₁ U₂ z l k) (i : Fin k) :
    D.exceptionalParent i ≠ z := by
  intro h
  have hzU₂ : z ∈ U₂ := h ▸ D.exceptionalParent_mem_U₂ i
  exact Set.disjoint_left.mp D.bipartite.disjoint D.z_mem hzU₂

theorem exceptionalParent_ne_center
    (D : SurgeryData T U₁ U₂ z l k) (i : Fin k) :
    D.exceptionalParent i ≠ (D.exceptionalPath i).center := by
  intro h
  have hp := D.exceptionalParent_dist_add_one i
  have hc := (D.exceptional_near_center_far_dist i).1
  rw [h] at hp
  omega

theorem exceptionalParent_ne_near
    (D : SurgeryData T U₁ U₂ z l k) (i : Fin k) :
    D.exceptionalParent i ≠ D.exceptionalNearEndpoint i :=
  (D.exceptionalParent_adj_near i).ne

theorem exceptionalParent_ne_far
    (D : SurgeryData T U₁ U₂ z l k) (i : Fin k) :
    D.exceptionalParent i ≠ D.exceptionalFarEndpoint i := by
  intro h
  have hp := D.exceptionalParent_dist_add_one i
  have hf := (D.exceptional_near_center_far_dist i).2
  rw [h] at hp
  omega

/-- Thus `sᵢP_{4l+i}` really is a three-edge path extension: `sᵢ` is not
already one of the three vertices of `P_{4l+i}`. -/
theorem exceptionalParent_not_mem_path
    (D : SurgeryData T U₁ U₂ z l k) (i : Fin k) :
    D.exceptionalParent i ∉ (D.exceptionalPath i).vertices := by
  have hend : D.exceptionalParent i ∉
      ({(D.exceptionalPath i).left, (D.exceptionalPath i).right} : Finset V) := by
    rw [(D.exceptionalPath i).endpoints_eq_near_far z]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨D.exceptionalParent_ne_near i, D.exceptionalParent_ne_far i⟩
  simp only [TwoPath.vertices, Finset.mem_insert, Finset.mem_singleton, not_or] at hend ⊢
  exact ⟨hend.1, D.exceptionalParent_ne_center i, hend.2⟩

/-- Zhao's `rᵢ = p(sᵢ)`. -/
def exceptionalGrandparent (D : SurgeryData T U₁ U₂ z l k) (i : Fin k) : V :=
  Erdos547b.TreePartition.parent D.tree z (D.exceptionalParent_ne_root i)

theorem exceptionalGrandparent_adj_parent
    (D : SurgeryData T U₁ U₂ z l k) (i : Fin k) :
    T.Adj (D.exceptionalGrandparent i) (D.exceptionalParent i) :=
  Erdos547b.TreePartition.parent_adj D.tree z (D.exceptionalParent_ne_root i)

theorem exceptionalGrandparent_dist_add_one
    (D : SurgeryData T U₁ U₂ z l k) (i : Fin k) :
    T.dist z (D.exceptionalGrandparent i) + 1 =
      T.dist z (D.exceptionalParent i) :=
  Erdos547b.TreePartition.parent_dist_add_one D.tree z (D.exceptionalParent_ne_root i)

theorem exceptionalGrandparent_mem_U₁
    (D : SurgeryData T U₁ U₂ z l k) (i : Fin k) :
    D.exceptionalGrandparent i ∈ U₁ :=
  D.bipartite.symm.mem_of_mem_adj (D.exceptionalParent_mem_U₂ i)
    (D.exceptionalGrandparent_adj_parent i).symm

/-- The specialness of `P_{4l+i}` forces `sᵢ` to have degree exactly two:
its two neighbours are `tᵢ` and `rᵢ`. -/
theorem exceptionalParent_neighbor_ncard_eq_two
    (D : SurgeryData T U₁ U₂ z l k) (i : Fin k) :
    (T.neighborSet (D.exceptionalParent i)).ncard = 2 := by
  have hupper : (T.neighborSet (D.exceptionalParent i)).ncard ≤ 2 := by
    apply (D.p_special (exceptionalPIndex l i)).2
    rcases (D.exceptionalPath i).nearEndpoint_eq_left_or_right z with h | h
    · exact Or.inl (by simpa [exceptionalNearEndpoint, h] using
        D.exceptionalParent_adj_near i)
    · exact Or.inr (by simpa [exceptionalNearEndpoint, h] using
        D.exceptionalParent_adj_near i)
  have hne : D.exceptionalNearEndpoint i ≠ D.exceptionalGrandparent i := by
    intro h
    have hp := D.exceptionalParent_dist_add_one i
    have hr := D.exceptionalGrandparent_dist_add_one i
    rw [← h] at hr
    omega
  have hsub : ({D.exceptionalNearEndpoint i, D.exceptionalGrandparent i} : Set V) ⊆
      T.neighborSet (D.exceptionalParent i) := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact D.exceptionalParent_adj_near i
    · exact (D.exceptionalGrandparent_adj_parent i).symm
  have hlower : 2 ≤ (T.neighborSet (D.exceptionalParent i)).ncard := by
    rw [← Set.ncard_pair hne]
    exact Set.ncard_le_ncard hsub (by toFinite_tac)
  omega

/-- Footnote 14 in Zhao's proof: if `rᵢ` is not a vertex of the induced
forest, then it is the deleted midpoint of one of the `Q`-paths. -/
theorem exists_Q_center_eq_grandparent_of_mem_deleted
    (D : SurgeryData T U₁ U₂ z l k) (i : Fin k)
    (hdel : D.exceptionalGrandparent i ∈ D.deleted) :
    ∃ j : Fin (4 * l), (D.Q j).center = D.exceptionalGrandparent i := by
  have hQ : D.exceptionalGrandparent i ∈ D.deletedQ := by
    rcases Finset.mem_union.mp hdel with hP | hQ
    · exact False.elim (Set.disjoint_left.mp D.bipartite.disjoint
        (D.exceptionalGrandparent_mem_U₁ i) (D.deletedP_subset hP))
    · exact hQ
  obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hQ
  exact ⟨j, hj⟩

end SurgeryData

end Erdos547b.ZhaoSurgeryAlt

#print axioms Erdos547b.ZhaoSurgeryAlt.SurgeryData.forest_isAcyclic
#print axioms Erdos547b.ZhaoSurgeryAlt.SurgeryData.card_forestLeft
#print axioms Erdos547b.ZhaoSurgeryAlt.SurgeryData.card_forestRight
#print axioms Erdos547b.ZhaoSurgeryAlt.SurgeryData.exceptional_path_survives
#print axioms Erdos547b.ZhaoSurgeryAlt.TwoPath.endpoint_dist_ne
#print axioms Erdos547b.ZhaoSurgeryAlt.SurgeryData.exceptionalParent_not_mem_path
#print axioms Erdos547b.ZhaoSurgeryAlt.SurgeryData.exceptionalParent_neighbor_ncard_eq_two
#print axioms Erdos547b.ZhaoSurgeryAlt.SurgeryData.exists_Q_center_eq_grandparent_of_mem_deleted


/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

open scoped SimpleGraph

noncomputable section

namespace Erdos547b.ZhaoPackingAdapterAlt

open Finset SimpleGraph

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

open ZhaoLemma710Alt

private theorem exists_twoPath_of_degree_two
    (T : SimpleGraph V) [DecidableRel T.Adj] (v : V)
    (hv : T.degree v = 2) :
    ∃ R : ZhaoSurgeryAlt.TwoPath T,
      R.center = v ∧ R.vertices = twoPathVertices T v := by
  have hcard : (T.neighborFinset v).card = 2 := by
    simpa [T.card_neighborFinset_eq_degree] using hv
  obtain ⟨a, b, hab, hN⟩ := Finset.card_eq_two.mp hcard
  have hva : T.Adj v a := by
    rw [← T.mem_neighborFinset]
    simp [hN]
  have hvb : T.Adj v b := by
    rw [← T.mem_neighborFinset]
    simp [hN]
  let R : ZhaoSurgeryAlt.TwoPath T :=
    { left := a
      center := v
      right := b
      left_ne_center := hva.ne'
      center_ne_right := hvb.ne
      left_ne_right := hab
      adj_left := hva.symm
      adj_right := hvb }
  refine ⟨R, rfl, ?_⟩
  ext x
  simp only [R, ZhaoSurgeryAlt.TwoPath.vertices, twoPathVertices, hN, Finset.mem_insert,
    Finset.mem_singleton]
  tauto

private noncomputable def twoPathOfDegreeTwo
    (T : SimpleGraph V) [DecidableRel T.Adj] (v : V)
    (hv : T.degree v = 2) : ZhaoSurgeryAlt.TwoPath T :=
  Classical.choose (exists_twoPath_of_degree_two T v hv)

@[simp] private theorem twoPathOfDegreeTwo_center
    (T : SimpleGraph V) [DecidableRel T.Adj] (v : V)
    (hv : T.degree v = 2) :
    (twoPathOfDegreeTwo T v hv).center = v :=
  (Classical.choose_spec (exists_twoPath_of_degree_two T v hv)).1

@[simp] private theorem twoPathOfDegreeTwo_vertices
    (T : SimpleGraph V) [DecidableRel T.Adj] (v : V)
    (hv : T.degree v = 2) :
    (twoPathOfDegreeTwo T v hv).vertices = twoPathVertices T v :=
  (Classical.choose_spec (exists_twoPath_of_degree_two T v hv)).2

private theorem degree_eq_neighborSet_ncard
    (T : SimpleGraph V) [DecidableRel T.Adj] (v : V) :
    T.degree v = (T.neighborSet v).ncard := by
  rw [Set.ncard_eq_toFinset_card, Set.toFinite_toFinset]
  exact (T.card_neighborFinset_eq_degree v).symm

/-- The packing produced by Proposition 7.11(3) supplies all the named paths
required by the surgery data of Lemma 7.10. -/
theorem surgeryData_of_proposition711Part3Witness
    (T : SimpleGraph V) [DecidableRel T.Adj]
    (U1 U2 : Finset V) (z : V) (l k : ℕ)
    (hT : T.IsTree)
    (hbi : T.IsBipartiteWith (U1 : Set V) (U2 : Set V))
    (hcover : U1 ∪ U2 = Finset.univ)
    (hz : z ∈ U1)
    (W : Proposition711Part3Witness T U1 U2 z l)
    (hk : k ≤ l) :
    Nonempty (ZhaoSurgeryAlt.SurgeryData T U1 U2 z l k) := by
  classical
  have hPsize : 4 * l + k ≤ 5 * l := by omega
  let eP : {x // x ∈ W.P} ≃ Fin (5 * l) :=
    Finset.equivFinOfCardEq W.card_P
  let eQ : {x // x ∈ W.Q} ≃ Fin (4 * l) :=
    Finset.equivFinOfCardEq W.card_Q
  let pSub (i : Fin (4 * l + k)) : {x // x ∈ W.P} :=
    eP.symm (Fin.castLE hPsize i)
  let qSub (i : Fin (4 * l)) : {x // x ∈ W.Q} := eQ.symm i
  let pc (i : Fin (4 * l + k)) : V := (pSub i).1
  let qc (i : Fin (4 * l)) : V := (qSub i).1
  have hpc_mem (i : Fin (4 * l + k)) : pc i ∈ W.P := (pSub i).2
  have hqc_mem (i : Fin (4 * l)) : qc i ∈ W.Q := (qSub i).2
  have hpc_deg (i : Fin (4 * l + k)) : T.degree (pc i) = 2 :=
    (W.P_special (pc i) (hpc_mem i)).1
  have hqc_deg (i : Fin (4 * l)) : T.degree (qc i) = 2 :=
    W.Q_degree_two (qc i) (hqc_mem i)
  let PP (i : Fin (4 * l + k)) : ZhaoSurgeryAlt.TwoPath T :=
    twoPathOfDegreeTwo T (pc i) (hpc_deg i)
  let QQ (i : Fin (4 * l)) : ZhaoSurgeryAlt.TwoPath T :=
    twoPathOfDegreeTwo T (qc i) (hqc_deg i)
  have hpc_inj : Function.Injective pc := by
    intro i j hij
    have hsub : pSub i = pSub j := Subtype.ext hij
    have hfin : Fin.castLE hPsize i = Fin.castLE hPsize j := by
      exact eP.symm.injective hsub
    exact Fin.castLE_injective hPsize hfin
  have hqc_inj : Function.Injective qc := by
    intro i j hij
    have hsub : qSub i = qSub j := Subtype.ext hij
    have hfin : i = j := eQ.symm.injective hsub
    exact hfin
  have hPP_center (i) : (PP i).center = pc i := by
    exact twoPathOfDegreeTwo_center T (pc i) (hpc_deg i)
  have hQQ_center (i) : (QQ i).center = qc i := by
    exact twoPathOfDegreeTwo_center T (qc i) (hqc_deg i)
  have hPP_vertices (i) : (PP i).vertices = twoPathVertices T (pc i) := by
    exact twoPathOfDegreeTwo_vertices T (pc i) (hpc_deg i)
  have hQQ_vertices (i) : (QQ i).vertices = twoPathVertices T (qc i) := by
    exact twoPathOfDegreeTwo_vertices T (qc i) (hqc_deg i)
  have hpc_U2 (i) : pc i ∈ U2 := W.P_mem (pc i) (hpc_mem i)
  have hqc_U1 (i) : qc i ∈ U1 := W.Q_mem (qc i) (hqc_mem i)
  have hp_union (i) : pc i ∈ W.P ∪ W.Q := Finset.mem_union_left _ (hpc_mem i)
  have hq_union (i) : qc i ∈ W.P ∪ W.Q := Finset.mem_union_right _ (hqc_mem i)
  have hp_left (i) : (PP i).left ∈ U1 := by
    apply hbi.symm.mem_of_mem_adj (hpc_U2 i)
    rw [← hPP_center i]
    exact (PP i).adj_left.symm
  have hp_right (i) : (PP i).right ∈ U1 := by
    apply hbi.symm.mem_of_mem_adj (hpc_U2 i)
    rw [← hPP_center i]
    exact (PP i).adj_right
  have hq_left (i) : (QQ i).left ∈ U2 := by
    apply hbi.mem_of_mem_adj (hqc_U1 i)
    rw [← hQQ_center i]
    exact (QQ i).adj_left.symm
  have hq_right (i) : (QQ i).right ∈ U2 := by
    apply hbi.mem_of_mem_adj (hqc_U1 i)
    rw [← hQQ_center i]
    exact (QQ i).adj_right
  have hp_disjoint (i j : Fin (4 * l + k)) (hij : i ≠ j) :
      Disjoint (PP i).vertices (PP j).vertices := by
    rw [hPP_vertices i, hPP_vertices j]
    exact W.supports_pairwise (hp_union i) (hp_union j) (fun h => hij (hpc_inj h))
  have hq_disjoint (i j : Fin (4 * l)) (hij : i ≠ j) :
      Disjoint (QQ i).vertices (QQ j).vertices := by
    rw [hQQ_vertices i, hQQ_vertices j]
    exact W.supports_pairwise (hq_union i) (hq_union j) (fun h => hij (hqc_inj h))
  have hpq_ne (i : Fin (4 * l + k)) (j : Fin (4 * l)) : pc i ≠ qc j := by
    intro heq
    exact Set.disjoint_left.mp hbi.disjoint (hqc_U1 j) (heq ▸ hpc_U2 i)
  have hpq_disjoint (i : Fin (4 * l + k)) (j : Fin (4 * l)) :
      Disjoint (PP i).vertices (QQ j).vertices := by
    rw [hPP_vertices i, hQQ_vertices j]
    exact W.supports_pairwise (hp_union i) (hq_union j) (hpq_ne i j)
  have hzP (i) : z ∉ (PP i).vertices := by
    rw [hPP_vertices i]
    exact W.avoid_root (pc i) (hp_union i)
  have hzQ (i) : z ∉ (QQ i).vertices := by
    rw [hQQ_vertices i]
    exact W.avoid_root (qc i) (hq_union i)
  have hp_special (i) :
      (T.neighborSet (PP i).center).ncard = 2 ∧
        ∀ x, (T.Adj x (PP i).left ∨ T.Adj x (PP i).right) →
          (T.neighborSet x).ncard ≤ 2 := by
    have hs := W.P_special (pc i) (hpc_mem i)
    constructor
    · rw [hPP_center i, ← degree_eq_neighborSet_ncard T]
      exact hs.1
    · intro x hx
      rw [← degree_eq_neighborSet_ncard T]
      apply hs.2
      simp only [Erdos547EC2.openNeighborFinset, Finset.mem_biUnion]
      rcases hx with hx | hx
      · refine ⟨(PP i).left, ?_, ?_⟩
        · rw [T.mem_neighborFinset, ← hPP_center i]
          exact (PP i).adj_left.symm
        · rw [T.mem_neighborFinset]
          exact hx.symm
      · refine ⟨(PP i).right, ?_, ?_⟩
        · rw [T.mem_neighborFinset, ← hPP_center i]
          exact (PP i).adj_right
        · rw [T.mem_neighborFinset]
          exact hx.symm
  have hq_degree_two (i) :
      (T.neighborSet (QQ i).center).ncard = 2 := by
    rw [hQQ_center i, ← degree_eq_neighborSet_ncard T]
    exact hqc_deg i
  exact ⟨
    { tree := hT
      bipartite := hbi
      cover := hcover
      z_mem := hz
      P := PP
      Q := QQ
      p_left_mem := hp_left
      p_center_mem := fun i => hPP_center i ▸ hpc_U2 i
      p_right_mem := hp_right
      q_left_mem := hq_left
      q_center_mem := fun i => hQQ_center i ▸ hqc_U1 i
      q_right_mem := hq_right
      q_degree_two := hq_degree_two
      p_disjoint := hp_disjoint
      q_disjoint := hq_disjoint
      pq_disjoint := hpq_disjoint
      z_avoid_p := hzP
      z_avoid_q := hzQ
      p_special := hp_special }⟩

#print axioms surgeryData_of_proposition711Part3Witness

end Erdos547b.ZhaoPackingAdapterAlt


/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

open scoped SimpleGraph

noncomputable section

namespace Erdos547b.ZhaoFixedExtend2

open Finset SimpleGraph

universe u v

variable {A : Type u} {B : Type v}

private theorem exists_maximal_path
    [Fintype A] (F : SimpleGraph A) [DecidableRel F.Adj] [Nonempty A] :
    ∃ (u v : A) (p : F.Walk u v) (_ : p.IsPath),
      ∀ (u' v' : A) (p' : F.Walk u' v') (_ : p'.IsPath),
        p'.length ≤ p.length := by
  let lengths : Set ℕ :=
    {n | ∃ (u v : A) (p : F.Walk u v), p.IsPath ∧ p.length = n}
  have hfinite : lengths.Finite :=
    Set.Finite.subset (Set.finite_le_nat F.edgeFinset.card) <| by
      rintro n ⟨u, v, p, hp, rfl⟩
      exact hp.isTrail.length_le_card_edgeFinset
  let x : A := Classical.choice inferInstance
  obtain ⟨n, hnmem, hnmax⟩ :=
    hfinite.exists_maximal ⟨0, ⟨x, x, .nil, by simp⟩⟩
  obtain ⟨u, v, p, hp, rfl⟩ := hnmem
  refine ⟨u, v, p, hp, ?_⟩
  intro u' v' p' hp'
  have h := hnmax ⟨u', v', p', hp', rfl⟩
  omega

/-- Every nonempty finite forest has a vertex of degree at most one. -/
theorem IsAcyclic.exists_neighborFinset_card_le_one
    [Fintype A] [DecidableEq A] {F : SimpleGraph A} [DecidableRel F.Adj]
    (hF : F.IsAcyclic) [Nonempty A] :
    ∃ x : A, (F.neighborFinset x).card ≤ 1 := by
  obtain ⟨u, v, p, hp, hmax⟩ := exists_maximal_path F
  refine ⟨u, ?_⟩
  rw [Finset.card_le_one_iff]
  intro a b ha hb
  have hua : F.Adj u a := (F.mem_neighborFinset u a).mp ha
  have hub : F.Adj u b := (F.mem_neighborFinset u b).mp hb
  have haSupp : a ∈ p.support := by
    by_contra haNot
    have hlong : (p.cons hua.symm).IsPath := hp.cons haNot
    have hle := hmax a v (p.cons hua.symm) hlong
    simp only [Walk.length_cons] at hle
    omega
  have hbSupp : b ∈ p.support := by
    by_contra hbNot
    have hlong : (p.cons hub.symm).IsPath := hp.cons hbNot
    have hle := hmax b v (p.cons hub.symm) hlong
    simp only [Walk.length_cons] at hle
    omega
  exact (hF.eq_snd_of_adj_start hp hua haSupp).trans
    (hF.eq_snd_of_adj_start hp hub hbSupp).symm

private theorem exists_vertex_card_neighbors_inter_le_one
    [Fintype A] [DecidableEq A]
    (F : SimpleGraph A) [DecidableRel F.Adj]
    (R : Finset A) (hR : R.Nonempty)
    (hacyclic : (F.induce (↑R : Set A)).IsAcyclic) :
    ∃ x ∈ R, (F.neighborFinset x ∩ R).card ≤ 1 := by
  let : Nonempty (↑R : Set A) := Set.nonempty_coe_sort.mpr (by simpa using hR)
  obtain ⟨x, hx⟩ := IsAcyclic.exists_neighborFinset_card_le_one hacyclic
  refine ⟨x, x.property, ?_⟩
  have heq := F.map_neighborFinset_induce x
  have hmapcard :
      ((((F.induce (↑R : Set A)).neighborFinset x).map
        (.subtype (· ∈ (↑R : Set A)))).card) =
        ((F.induce (↑R : Set A)).neighborFinset x).card :=
    Finset.card_map _
  have hsets :
      ((F.induce (↑R : Set A)).neighborFinset x).map
          (.subtype (· ∈ (↑R : Set A))) =
        F.neighborFinset (x : A) ∩ R := by
    ext y
    simp [F.mem_neighborFinset]
  rw [← hsets, hmapcard]
  exact hx

/-- Vertices whose images consume capacity in core part `Q i`.  Every
nonfixed vertex of colour `i` consumes one place; a fixed vertex consumes a
place precisely when its prescribed image belongs to that core part. -/
def coreDemand [Fintype A] [DecidableEq A] [DecidableEq B]
    {F : SimpleGraph A} (c : F.Coloring (Fin 2))
    (S : Finset A) (p : S → B) (i : Fin 2) (Q : Finset B) : Finset A :=
  Finset.univ.filter fun a =>
    c a = i ∧ ∀ ha : a ∈ S, p ⟨a, ha⟩ ∈ Q

private structure PartialCopy [Fintype A] [DecidableEq A] [DecidableEq B]
    (F : SimpleGraph A) (G : SimpleGraph B)
    (c : F.Coloring (Fin 2)) (S R : Finset A) (p : S → B)
    (Q : Fin 2 → Finset B) where
  toFun : ↥(S ∪ R) → B
  injective : Function.Injective toFun
  map_adj : ∀ x y : ↥(S ∪ R), F.Adj x y → G.Adj (toFun x) (toFun y)
  fixed : ∀ x : S, toFun ⟨x, Finset.mem_union_left R x.property⟩ = p x
  outside_part : ∀ x : ↥(S ∪ R), x.1 ∈ R → toFun x ∈ Q (c x)

private theorem exists_candidate
    [Fintype B] [DecidableEq B]
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (Q Z used : Finset B) (l demand : ℕ)
    (hZ : Z.card ≤ 2)
    (hmiss : ∀ z ∈ Z, (Q.filter fun w => ¬G.Adj z w).card ≤ l)
    (hused : used.card + 1 ≤ demand)
    (hcapacity : demand + 4 * l ≤ Q.card) :
    ∃ w ∈ Q, w ∉ used ∧ ∀ z ∈ Z, G.Adj z w := by
  classical
  let bad : Finset B := Z.biUnion fun z => Q.filter fun w => ¬G.Adj z w
  have hbad : bad.card ≤ 2 * l := by
    calc
      bad.card ≤ ∑ z ∈ Z, (Q.filter fun w => ¬G.Adj z w).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _z ∈ Z, l :=
        Finset.sum_le_sum fun z hz => hmiss z hz
      _ = Z.card * l := by simp
      _ ≤ 2 * l := Nat.mul_le_mul_right l hZ
  have hblocked : (used ∪ bad).card < Q.card := by
    have hu := Finset.card_union_le used bad
    omega
  obtain ⟨w, hwQ, hwblocked⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hblocked
  refine ⟨w, hwQ, ?_, ?_⟩
  · exact fun hw => hwblocked (Finset.mem_union_left bad hw)
  · intro z hz
    by_contra hza
    apply hwblocked
    apply Finset.mem_union_right used
    exact Finset.mem_biUnion.mpr ⟨z, hz, Finset.mem_filter.mpr ⟨hwQ, hza⟩⟩

private theorem card_neighbors_in_union_le_two
    [Fintype A] [DecidableEq A]
    (F : SimpleGraph A) [DecidableRel F.Adj]
    (S R : Finset A) (x : A)
    (hleaf : (F.neighborFinset x ∩ R).card ≤ 1)
    (hboundary :
      (F.neighborFinset x ∩ S).card ≤ 1 ∨ F.degree x ≤ 2) :
    (F.neighborFinset x ∩ (S ∪ R.erase x)).card ≤ 2 := by
  classical
  rcases hboundary with hboundary | hdegree
  · have houtside : (F.neighborFinset x ∩ R.erase x).card ≤ 1 := by
      have hsub : F.neighborFinset x ∩ R.erase x ⊆
          F.neighborFinset x ∩ R := by
        intro y hy
        exact Finset.mem_inter.mpr
          ⟨(Finset.mem_inter.mp hy).1,
            Finset.erase_subset x R (Finset.mem_inter.mp hy).2⟩
      exact (Finset.card_le_card hsub).trans hleaf
    have hsub : F.neighborFinset x ∩ (S ∪ R.erase x) ⊆
        (F.neighborFinset x ∩ S) ∪
          (F.neighborFinset x ∩ R.erase x) := by
      intro y hy
      simp only [Finset.mem_inter, Finset.mem_union] at hy ⊢
      rcases hy.2 with hyS | hyR
      · exact Or.inl ⟨hy.1, hyS⟩
      · exact Or.inr ⟨hy.1, hyR⟩
    have hc := Finset.card_le_card hsub
    have hu := Finset.card_union_le (F.neighborFinset x ∩ S)
      (F.neighborFinset x ∩ R.erase x)
    omega
  · exact (Finset.card_le_card Finset.inter_subset_left).trans (by
      simpa only [F.card_neighborFinset_eq_degree] using hdegree)

private theorem exists_partial_copy
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (F : SimpleGraph A) (G : SimpleGraph B)
    [DecidableRel F.Adj] [DecidableRel G.Adj]
    (hF : F.IsAcyclic) (c : F.Coloring (Fin 2))
    (S : Finset A) (p : S → B) (Q : Fin 2 → Finset B) (l : ℕ)
    (hp_inj : Function.Injective p)
    (hp_adj : ∀ x y : S, F.Adj x y → G.Adj (p x) (p y))
    (hQ : Set.PairwiseDisjoint Set.univ Q)
    (hp_core_color : ∀ (y : S) (i : Fin 2), p y ∈ Q i → c y = i)
    (hboundary : ∀ x, x ∉ S →
      (F.neighborFinset x ∩ S).card ≤ 1 ∨ F.degree x ≤ 2)
    (hfixed_neighbor_core : ∀ x, x ∉ S → ∀ y : S,
      F.Adj x y → p y ∈ Q (c y))
    (hmiss : ∀ i j, i ≠ j → ∀ b ∈ Q i,
      ((Q j).filter fun w => ¬G.Adj b w).card ≤ l)
    (hcapacity : ∀ i,
      (coreDemand c S p i (Q i)).card + 4 * l ≤ (Q i).card) :
    ∀ R : Finset A, Disjoint S R →
      Nonempty (PartialCopy F G c S R p Q) := by
  classical
  apply Finset.strongInduction
  intro R ih hSR
  by_cases hRempty : R = ∅
  · subst R
    let f : ↥(S ∪ ∅) → B := fun x => p ⟨x, by simpa using x.property⟩
    refine ⟨{
      toFun := f
      injective := ?_
      map_adj := ?_
      fixed := ?_
      outside_part := ?_ }⟩
    · intro x y hxy
      apply Subtype.ext
      apply Subtype.ext_iff.mp (hp_inj hxy)
    · intro x y hxy
      exact hp_adj ⟨x, by simpa using x.property⟩
        ⟨y, by simpa using y.property⟩ hxy
    · intro x
      rfl
    · intro x hx
      simp at hx
  · have hRnonempty : R.Nonempty := Finset.nonempty_iff_ne_empty.mpr hRempty
    obtain ⟨x, hxR, hxleaf⟩ :=
      exists_vertex_card_neighbors_inter_le_one F R hRnonempty
        (hF.induce (↑R : Set A))
    let R' : Finset A := R.erase x
    have hR'sub : R' ⊂ R := by
      exact Finset.erase_ssubset hxR
    have hSR' : Disjoint S R' :=
      hSR.mono_right (Finset.erase_subset x R)
    obtain ⟨e⟩ := ih R' hR'sub hSR'
    have hxS : x ∉ S := by
      exact fun hx => Finset.disjoint_left.mp hSR hx hxR
    have hneighbors :
        (F.neighborFinset x ∩ (S ∪ R')).card ≤ 2 := by
      apply card_neighbors_in_union_le_two F S R x hxleaf
      exact hboundary x hxS
    let N : Finset ↥(S ∪ R') :=
      Finset.univ.filter fun y => F.Adj x y
    let Z : Finset B := N.image e.toFun
    have hNcard : N.card =
        (F.neighborFinset x ∩ (S ∪ R')).card := by
      let q : (y : ↥(S ∪ R')) → y ∈ N → A := fun y _ => y.1
      apply Finset.card_bij q
      · intro y hy
        have hyN : F.Adj x y := by
          simpa [N] using hy
        exact Finset.mem_inter.mpr
          ⟨(F.mem_neighborFinset x y).mpr hyN, y.property⟩
      · intro y₁ hy₁ y₂ hy₂ heq
        exact Subtype.ext heq
      · intro y hy
        refine ⟨⟨y, (Finset.mem_inter.mp hy).2⟩, ?_, rfl⟩
        · simp only [N, Finset.mem_filter, Finset.mem_univ, true_and]
          exact (F.mem_neighborFinset x y).mp (Finset.mem_inter.mp hy).1
    have hZcard : Z.card ≤ 2 := by
      exact (Finset.card_image_le.trans (hNcard.le.trans hneighbors))
    let D : Finset ↥(S ∪ R') :=
      Finset.univ.filter fun y => e.toFun y ∈ Q (c x)
    let used : Finset B := D.image e.toFun
    let E : Finset A := D.image Subtype.val
    have hused_card : used.card = D.card := by
      exact Finset.card_image_iff.mpr fun _ _ _ _ h => e.injective h
    have hEcard : E.card = D.card := by
      exact Finset.card_image_iff.mpr fun _ _ _ _ h => Subtype.ext h
    have hEsub : E ⊆ coreDemand c S p (c x) (Q (c x)) := by
      intro a ha
      obtain ⟨y, hyD, rfl⟩ := Finset.mem_image.mp ha
      have hyQ : e.toFun y ∈ Q (c x) := by
        simpa only [D, Finset.mem_filter, Finset.mem_univ, true_and] using hyD
      have hycolor : c y = c x := by
        rcases Finset.mem_union.mp y.property with hyS | hyR'
        · let ys : S := ⟨y, hyS⟩
          have heq : e.toFun y = p ys := by
            simpa only [ys] using e.fixed ys
          exact hp_core_color ys (c x) (by simpa [heq] using hyQ)
        · have hyown : e.toFun y ∈ Q (c y) := e.outside_part y hyR'
          by_contra hne
          have hd := hQ (Set.mem_univ (c y)) (Set.mem_univ (c x)) hne
          exact Finset.disjoint_left.mp hd hyown hyQ
      simp only [coreDemand, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨hycolor, ?_⟩
      intro haS
      let ys : S := ⟨y, haS⟩
      have heq : e.toFun y = p ys := by
        simpa only [ys] using e.fixed ys
      simpa [heq] using hyQ
    have hxDemand : x ∈ coreDemand c S p (c x) (Q (c x)) := by
      simp only [coreDemand, Finset.mem_filter, Finset.mem_univ, true_and]
      intro hxSin
      exact False.elim (hxS hxSin)
    have hxNotE : x ∉ E := by
      intro hxE
      obtain ⟨y, -, hyx⟩ := Finset.mem_image.mp hxE
      have hyU := y.property
      rw [hyx] at hyU
      rcases Finset.mem_union.mp hyU with hxSin | hxR'
      · exact hxS hxSin
      · exact (Finset.mem_erase.mp hxR').1 rfl
    have hEssub : E ⊂ coreDemand c S p (c x) (Q (c x)) := by
      rw [Finset.ssubset_iff_subset_ne]
      refine ⟨hEsub, ?_⟩
      intro heq
      exact hxNotE (heq.symm ▸ hxDemand)
    have hused : used.card + 1 ≤
        (coreDemand c S p (c x) (Q (c x))).card := by
      have hc := Finset.card_lt_card hEssub
      omega
    have hZmiss : ∀ z ∈ Z,
        ((Q (c x)).filter fun w => ¬G.Adj z w).card ≤ l := by
      intro z hz
      obtain ⟨y, hyN, rfl⟩ := Finset.mem_image.mp hz
      have hyadj : F.Adj x y := by
        simpa only [N, Finset.mem_filter, Finset.mem_univ, true_and] using hyN
      have hycore : e.toFun y ∈ Q (c y) := by
        rcases Finset.mem_union.mp y.property with hyS | hyR'
        · let ys : S := ⟨y, hyS⟩
          have hpy := hfixed_neighbor_core x hxS ys hyadj
          simpa only [ys, e.fixed ys] using hpy
        · exact e.outside_part y hyR'
      exact hmiss (c y) (c x) (c.valid hyadj.symm) (e.toFun y) hycore
    obtain ⟨w, hwQ, hwunused, hwadj⟩ :=
      exists_candidate G (Q (c x)) Z used l
        (coreDemand c S p (c x) (Q (c x))).card
        hZcard hZmiss (by simpa [hused_card, hEcard] using hused)
        (hcapacity (c x))
    have hxNotOld : ∀ y : ↥(S ∪ R'), w ≠ e.toFun y := by
      intro y hwy
      apply hwunused
      apply Finset.mem_image.mpr
      refine ⟨y, ?_, hwy.symm⟩
      simp only [D, Finset.mem_filter, Finset.mem_univ, true_and]
      simpa [← hwy] using hwQ
    let oldOf : ∀ y : ↥(S ∪ R), y.1 ≠ x → ↥(S ∪ R') :=
      fun y hy => ⟨y, by
        rcases Finset.mem_union.mp y.property with hyS | hyR
        · exact Finset.mem_union_left R' hyS
        · exact Finset.mem_union_right S (Finset.mem_erase.mpr ⟨hy, hyR⟩)⟩
    let f : ↥(S ∪ R) → B := fun y =>
      if hy : y.1 = x then w else e.toFun (oldOf y hy)
    refine ⟨{
      toFun := f
      injective := ?_
      map_adj := ?_
      fixed := ?_
      outside_part := ?_ }⟩
    · intro a b hab
      by_cases ha : a.1 = x
      · by_cases hb : b.1 = x
        · exact Subtype.ext (ha.trans hb.symm)
        · exfalso
          have : w = e.toFun (oldOf b hb) := by simpa [f, ha, hb] using hab
          exact hxNotOld (oldOf b hb) this
      · by_cases hb : b.1 = x
        · exfalso
          have : e.toFun (oldOf a ha) = w := by simpa [f, ha, hb] using hab
          exact hxNotOld (oldOf a ha) this.symm
        · have hold : oldOf a ha = oldOf b hb := by
            apply e.injective
            simpa [f, ha, hb] using hab
          apply Subtype.ext
          change (a : A) = (b : A)
          exact congrArg (fun q : ↥(S ∪ R') => (q : A)) hold
    · intro a b hab
      by_cases ha : a.1 = x
      · by_cases hb : b.1 = x
        · exact False.elim (F.ne_of_adj hab (ha.trans hb.symm))
        · have hbN : oldOf b hb ∈ N := by
            simp only [N, Finset.mem_filter, Finset.mem_univ, true_and]
            simpa only [ha] using hab
          have hbeZ : e.toFun (oldOf b hb) ∈ Z :=
            Finset.mem_image.mpr ⟨oldOf b hb, hbN, rfl⟩
          have h := hwadj (e.toFun (oldOf b hb)) hbeZ
          simpa [f, ha, hb] using h.symm
      · by_cases hb : b.1 = x
        · have haN : oldOf a ha ∈ N := by
            simp only [N, Finset.mem_filter, Finset.mem_univ, true_and]
            simpa only [hb] using hab.symm
          have haeZ : e.toFun (oldOf a ha) ∈ Z :=
            Finset.mem_image.mpr ⟨oldOf a ha, haN, rfl⟩
          have h := hwadj (e.toFun (oldOf a ha)) haeZ
          simpa [f, ha, hb] using h
        · have holdAdj : F.Adj (oldOf a ha) (oldOf b hb) := hab
          have h := e.map_adj (oldOf a ha) (oldOf b hb) holdAdj
          simpa [f, ha, hb] using h
    · intro y
      have hyx : (y : A) ≠ x := fun heq => hxS (heq ▸ y.property)
      have holdEq : oldOf ⟨y, Finset.mem_union_left R y.property⟩ hyx =
          ⟨y, Finset.mem_union_left R' y.property⟩ := rfl
      simpa [f, hyx, holdEq] using e.fixed y
    · intro y hyR
      by_cases hyx : y.1 = x
      · subst x
        simpa [f] using hwQ
      · have hyR' : y.1 ∈ R' := Finset.mem_erase.mpr ⟨hyx, hyR⟩
        have h := e.outside_part (oldOf y hyx) hyR'
        simpa [f, hyx] using h

/-- A fixed partial embedding of a finite forest extends over every remaining
vertex. The only target-side hypothesis beyond acyclicity is Zhao's boundary
condition: a nonfixed vertex has at most one fixed neighbor, unless its total
degree is at most two. The host loses at most 2*l candidates to its at most
two embedded neighbors; the stated 4*l reserve is the form needed in Lemma
7.10. -/
theorem fixed_forest_embedding
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (F : SimpleGraph A) (G : SimpleGraph B)
    [DecidableRel F.Adj] [DecidableRel G.Adj]
    (hF : F.IsAcyclic) (c : F.Coloring (Fin 2))
    (S : Finset A) (p : S → B) (Q : Fin 2 → Finset B) (l : ℕ)
    (hp_inj : Function.Injective p)
    (hp_adj : ∀ x y : S, F.Adj x y → G.Adj (p x) (p y))
    (hQ : Set.PairwiseDisjoint Set.univ Q)
    (hp_core_color : ∀ (y : S) (i : Fin 2), p y ∈ Q i → c y = i)
    (hboundary : ∀ x, x ∉ S →
      (F.neighborFinset x ∩ S).card ≤ 1 ∨ F.degree x ≤ 2)
    (hfixed_neighbor_core : ∀ x, x ∉ S → ∀ y : S,
      F.Adj x y → p y ∈ Q (c y))
    (hmiss : ∀ i j, i ≠ j → ∀ b ∈ Q i,
      ((Q j).filter fun w => ¬G.Adj b w).card ≤ l)
    (hcapacity : ∀ i,
      (coreDemand c S p i (Q i)).card + 4 * l ≤ (Q i).card) :
    ∃ f : F.Copy G,
      (∀ x : S, f x = p x) ∧
      ∀ x, x ∉ S → f x ∈ Q (c x) := by
  classical
  let R : Finset A := Finset.univ \ S
  have hSR : Disjoint S R := by
    simp [R, Finset.disjoint_left]
  obtain ⟨e⟩ := exists_partial_copy F G hF c S p Q l hp_inj hp_adj hQ
    hp_core_color hboundary hfixed_neighbor_core hmiss hcapacity R hSR
  have hcover : S ∪ R = Finset.univ := by
    simp [R]
  let eAll : A → B := fun x => e.toFun ⟨x, by simpa [hcover]⟩
  have heInj : Function.Injective eAll := by
    intro x y hxy
    have hsub : (⟨x, by simpa [hcover]⟩ : ↥(S ∪ R)) =
        ⟨y, by simpa [hcover]⟩ := by
      apply e.injective
      exact hxy
    exact congrArg Subtype.val hsub
  let f : F.Copy G :=
    ⟨⟨eAll, by
      intro x y hxy
      exact e.map_adj ⟨x, by simpa [hcover]⟩ ⟨y, by simpa [hcover]⟩ hxy⟩,
      heInj⟩
  refine ⟨f, ?_, ?_⟩
  · intro x
    simpa [f, eAll, hcover] using e.fixed x
  · intro x hxS
    have hxR : x ∈ R := by simp [R, hxS]
    simpa [f, eAll, hcover] using
      e.outside_part ⟨x, by simpa [hcover]⟩ hxR

#print axioms fixed_forest_embedding

end Erdos547b.ZhaoFixedExtend2


/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

/-! The canonical partial embedding of the exceptional paths in Zhao 7.10. -/

open scoped SimpleGraph

noncomputable section

namespace Erdos547b.ZhaoExceptionalPremapAlt

open Finset SimpleGraph

universe u v

variable {V : Type u} {W : Type v}
variable [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

open Erdos547b.ZhaoSurgeryAlt
open Erdos547b.ZhaoLemma710Alt

/-- Names the root and the three vertices of each exceptional target path. -/
inductive ExceptionalIndex (k : ℕ)
  | root
  | left (i : Fin k)
  | center (i : Fin k)
  | right (i : Fin k)
  deriving DecidableEq

private def exceptionalIndexEnum (k : ℕ) :
    Unit ⊕ (Fin k × Fin 3) → ExceptionalIndex k
  | Sum.inl _ => .root
  | Sum.inr (i, j) =>
      if j = 0 then .left i else if j = 1 then .center i else .right i

noncomputable instance (k : ℕ) : Fintype (ExceptionalIndex k) :=
  Fintype.ofSurjective (exceptionalIndexEnum k) (by
    intro r
    cases r with
    | root => exact ⟨Sum.inl (), rfl⟩
    | left i => exact ⟨Sum.inr (i, 0), by simp [exceptionalIndexEnum]⟩
    | center i => exact ⟨Sum.inr (i, 1), by simp [exceptionalIndexEnum]⟩
    | right i => exact ⟨Sum.inr (i, 2), by simp [exceptionalIndexEnum]⟩)

namespace ExceptionalIndex

variable {T : SimpleGraph V} {U₁ U₂ : Finset V} {z : V} {l k : ℕ}

theorem root_not_deleted (D : SurgeryData T U₁ U₂ z l k) :
    z ∉ D.deleted := by
  rw [SurgeryData.deleted, Finset.mem_union, not_or]
  constructor
  · intro hzP
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hzP
    apply D.z_avoid_p (initialPIndex l k i)
    exact Eq.mp (congrArg
      (fun q : V => q ∈ (D.P (initialPIndex l k i)).vertices) hi)
      (D.P (initialPIndex l k i)).center_mem_vertices
  · intro hzQ
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hzQ
    apply D.z_avoid_q i
    exact Eq.mp (congrArg (fun q : V => q ∈ (D.Q i).vertices) hi)
      (D.Q i).center_mem_vertices

/-- The corresponding vertex of the surgically reduced forest. -/
def sourceVertex (D : SurgeryData T U₁ U₂ z l k) :
    ExceptionalIndex k → {x : V // x ∉ D.deleted}
  | root => ⟨z, root_not_deleted D⟩
  | left i => ⟨(D.exceptionalPath i).left,
      D.exceptional_vertex_not_deleted i (D.exceptionalPath i).left_mem_vertices⟩
  | center i => ⟨(D.exceptionalPath i).center,
      D.exceptional_vertex_not_deleted i (D.exceptionalPath i).center_mem_vertices⟩
  | right i => ⟨(D.exceptionalPath i).right,
      D.exceptional_vertex_not_deleted i (D.exceptionalPath i).right_mem_vertices⟩

@[simp] theorem sourceVertex_root (D : SurgeryData T U₁ U₂ z l k) :
    (sourceVertex D root : V) = z := rfl

@[simp] theorem sourceVertex_left (D : SurgeryData T U₁ U₂ z l k) (i : Fin k) :
    (sourceVertex D (left i) : V) = (D.exceptionalPath i).left := rfl

@[simp] theorem sourceVertex_center (D : SurgeryData T U₁ U₂ z l k) (i : Fin k) :
    (sourceVertex D (center i) : V) = (D.exceptionalPath i).center := rfl

@[simp] theorem sourceVertex_right (D : SurgeryData T U₁ U₂ z l k) (i : Fin k) :
    (sourceVertex D (right i) : V) = (D.exceptionalPath i).right := rfl

private theorem eq_index_of_vertices_eq
    (D : SurgeryData T U₁ U₂ z l k) {i j : Fin k}
    {r s : ExceptionalIndex k}
    (hr : r = left i ∨ r = center i ∨ r = right i)
    (hs : s = left j ∨ s = center j ∨ s = right j)
    (h : sourceVertex D r = sourceVertex D s) : r = s := by
  have hv : (sourceVertex D r : V) = sourceVertex D s := congrArg Subtype.val h
  by_cases hij : i = j
  · subst j
    rcases hr with rfl | rfl | rfl <;> rcases hs with rfl | rfl | rfl
    · rfl
    · exfalso; exact (D.exceptionalPath i).left_ne_center hv
    · exfalso; exact (D.exceptionalPath i).left_ne_right hv
    · exfalso; exact (D.exceptionalPath i).left_ne_center hv.symm
    · rfl
    · exfalso; exact (D.exceptionalPath i).center_ne_right hv
    · exfalso; exact (D.exceptionalPath i).left_ne_right hv.symm
    · exfalso; exact (D.exceptionalPath i).center_ne_right hv.symm
    · rfl
  · have hd := D.p_disjoint (exceptionalPIndex l i) (exceptionalPIndex l j)
        (fun he => hij (Fin.ext (by simpa using congrArg Fin.val he)))
    exfalso
    have hrMem : (sourceVertex D r : V) ∈ (D.exceptionalPath i).vertices := by
      rcases hr with hr | hr | hr
      · subst r; exact (D.exceptionalPath i).left_mem_vertices
      · subst r; exact (D.exceptionalPath i).center_mem_vertices
      · subst r; exact (D.exceptionalPath i).right_mem_vertices
    have hsMem : (sourceVertex D s : V) ∈ (D.exceptionalPath j).vertices := by
      rcases hs with hs | hs | hs
      · subst s; exact (D.exceptionalPath j).left_mem_vertices
      · subst s; exact (D.exceptionalPath j).center_mem_vertices
      · subst s; exact (D.exceptionalPath j).right_mem_vertices
    have hrMem' : (sourceVertex D r : V) ∈ (D.exceptionalPath j).vertices :=
      Eq.mpr (congrArg (fun q : V => q ∈ (D.exceptionalPath j).vertices) hv) hsMem
    exact Finset.disjoint_left.mp hd hrMem hrMem'

theorem sourceVertex_injective (D : SurgeryData T U₁ U₂ z l k) :
    Function.Injective (sourceVertex D) := by
  intro r s h
  cases r with
  | root =>
      cases s with
      | root => rfl
      | left j =>
          exfalso
          apply D.z_avoid_p (exceptionalPIndex l j)
          have hv := congrArg Subtype.val h
          rw [sourceVertex_root, sourceVertex_left] at hv
          exact Eq.mp (congrArg
            (fun q : V => q ∈ (D.exceptionalPath j).vertices) hv.symm)
            (D.exceptionalPath j).left_mem_vertices
      | center j =>
          exfalso
          apply D.z_avoid_p (exceptionalPIndex l j)
          have hv := congrArg Subtype.val h
          rw [sourceVertex_root, sourceVertex_center] at hv
          exact Eq.mp (congrArg
            (fun q : V => q ∈ (D.exceptionalPath j).vertices) hv.symm)
            (D.exceptionalPath j).center_mem_vertices
      | right j =>
          exfalso
          apply D.z_avoid_p (exceptionalPIndex l j)
          have hv := congrArg Subtype.val h
          rw [sourceVertex_root, sourceVertex_right] at hv
          exact Eq.mp (congrArg
            (fun q : V => q ∈ (D.exceptionalPath j).vertices) hv.symm)
            (D.exceptionalPath j).right_mem_vertices
  | left i =>
      cases s with
      | root => exact False.elim (by
          apply D.z_avoid_p (exceptionalPIndex l i)
          have hv := congrArg Subtype.val h
          rw [sourceVertex_left, sourceVertex_root] at hv
          exact Eq.mp (congrArg
            (fun q : V => q ∈ (D.exceptionalPath i).vertices) hv)
            (D.exceptionalPath i).left_mem_vertices)
      | left j => exact eq_index_of_vertices_eq D (Or.inl rfl) (Or.inl rfl) h
      | center j => exact eq_index_of_vertices_eq D (Or.inl rfl) (Or.inr (Or.inl rfl)) h
      | right j => exact eq_index_of_vertices_eq D (Or.inl rfl) (Or.inr (Or.inr rfl)) h
  | center i =>
      cases s with
      | root => exact False.elim (by
          apply D.z_avoid_p (exceptionalPIndex l i)
          have hv := congrArg Subtype.val h
          rw [sourceVertex_center, sourceVertex_root] at hv
          exact Eq.mp (congrArg
            (fun q : V => q ∈ (D.exceptionalPath i).vertices) hv)
            (D.exceptionalPath i).center_mem_vertices)
      | left j => exact eq_index_of_vertices_eq D (Or.inr (Or.inl rfl)) (Or.inl rfl) h
      | center j => exact eq_index_of_vertices_eq D (Or.inr (Or.inl rfl)) (Or.inr (Or.inl rfl)) h
      | right j => exact eq_index_of_vertices_eq D (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl)) h
  | right i =>
      cases s with
      | root => exact False.elim (by
          apply D.z_avoid_p (exceptionalPIndex l i)
          have hv := congrArg Subtype.val h
          rw [sourceVertex_right, sourceVertex_root] at hv
          exact Eq.mp (congrArg
            (fun q : V => q ∈ (D.exceptionalPath i).vertices) hv)
            (D.exceptionalPath i).right_mem_vertices)
      | left j => exact eq_index_of_vertices_eq D (Or.inr (Or.inr rfl)) (Or.inl rfl) h
      | center j => exact eq_index_of_vertices_eq D (Or.inr (Or.inr rfl)) (Or.inr (Or.inl rfl)) h
      | right j => exact eq_index_of_vertices_eq D (Or.inr (Or.inr rfl)) (Or.inr (Or.inr rfl)) h

/-- The finite set consisting of the root and all exceptional path supports. -/
def sourceSet (D : SurgeryData T U₁ U₂ z l k) :
    Finset {x : V // x ∉ D.deleted} :=
  Finset.univ.image (sourceVertex D)

@[simp] theorem sourceVertex_mem_sourceSet
    (D : SurgeryData T U₁ U₂ z l k) (r : ExceptionalIndex k) :
    sourceVertex D r ∈ sourceSet D := by
  simp [sourceSet]

/-- The canonical equivalence between names and the finite source set. -/
def sourceEquiv (D : SurgeryData T U₁ U₂ z l k) :
    ExceptionalIndex k ≃ sourceSet D where
  toFun r := ⟨sourceVertex D r, sourceVertex_mem_sourceSet D r⟩
  invFun x := Classical.choose (Finset.mem_image.mp x.property)
  left_inv r := by
    apply sourceVertex_injective D
    have h := (Classical.choose_spec (Finset.mem_image.mp
      (sourceVertex_mem_sourceSet D r))).2
    exact h
  right_inv x := by
    apply Subtype.ext
    exact (Classical.choose_spec (Finset.mem_image.mp x.property)).2

end ExceptionalIndex

namespace ExceptionalIndex

variable {T : SimpleGraph V} {G : SimpleGraph W}
variable {U₁ U₂ : Finset V} {X Y Y₂ : Finset W} {z : V} {l k : ℕ}

/-- An explicit equivalence when `k` is the cardinality of `Y₂`. -/
def finEquivY₂ (hk : k = #Y₂) : Fin k ≃ Y₂ :=
  (Fintype.equivFinOfCardEq (by simpa [hk])).symm

/-- The prescribed host image of each exceptional source name. -/
def targetVertex (P : CenteredTwoPathSystem G X Y₂)
    (e : Fin k ≃ Y₂) (a : W) : ExceptionalIndex k → W
  | root => a
  | left i => P.left (e i)
  | center i => e i
  | right i => P.right (e i)

@[simp] theorem targetVertex_root (P : CenteredTwoPathSystem G X Y₂)
    (e : Fin k ≃ Y₂) (a : W) : targetVertex P e a root = a := rfl

@[simp] theorem targetVertex_left (P : CenteredTwoPathSystem G X Y₂)
    (e : Fin k ≃ Y₂) (a : W) (i : Fin k) :
    targetVertex P e a (left i) = P.left (e i) := rfl

@[simp] theorem targetVertex_center (P : CenteredTwoPathSystem G X Y₂)
    (e : Fin k ≃ Y₂) (a : W) (i : Fin k) :
    targetVertex P e a (center i) = e i := rfl

@[simp] theorem targetVertex_right (P : CenteredTwoPathSystem G X Y₂)
    (e : Fin k ≃ Y₂) (a : W) (i : Fin k) :
    targetVertex P e a (right i) = P.right (e i) := rfl

private theorem left_mem_endpoints (P : CenteredTwoPathSystem G X Y₂) (y : Y₂) :
    P.left y ∈ P.endpoints := by
  classical
  rw [CenteredTwoPathSystem.endpoints]
  refine Finset.mem_image.mpr ⟨(y, 0), Finset.mem_univ _, ?_⟩
  simp

private theorem right_mem_endpoints (P : CenteredTwoPathSystem G X Y₂) (y : Y₂) :
    P.right y ∈ P.endpoints := by
  classical
  rw [CenteredTwoPathSystem.endpoints]
  refine Finset.mem_image.mpr ⟨(y, 1), Finset.mem_univ _, ?_⟩
  simp

private theorem left_injective (P : CenteredTwoPathSystem G X Y₂) :
    Function.Injective P.left := by
  intro y y' h
  have hp := P.endpointInjective (a₁ := (y, 0)) (a₂ := (y', 0)) (by simpa using h)
  exact congrArg Prod.fst hp

private theorem right_injective (P : CenteredTwoPathSystem G X Y₂) :
    Function.Injective P.right := by
  intro y y' h
  have hp := P.endpointInjective (a₁ := (y, 1)) (a₂ := (y', 1)) (by simpa using h)
  exact congrArg Prod.fst hp

theorem targetVertex_injective
    (P : CenteredTwoPathSystem G X Y₂) (e : Fin k ≃ Y₂) (a : W)
    (hG : G.IsBipartiteWith (X : Set W) (Y : Set W))
    (hY₂ : Y₂ ⊆ Y) (ha : a ∈ X) (haAvoid : a ∉ P.endpoints) :
    Function.Injective (targetVertex P e a) := by
  intro r s h
  cases r with
  | root =>
      cases s with
      | root => rfl
      | left j =>
        simp only [targetVertex_root, targetVertex_left] at h
        exact False.elim (haAvoid (by
          have hj := left_mem_endpoints P (e j)
          exact h ▸ hj))
      | center j =>
        simp only [targetVertex_root, targetVertex_center] at h
        exact False.elim (Set.disjoint_left.mp hG.disjoint ha (by
          have hj : (e j : W) ∈ Y := hY₂ (e j).property
          exact h ▸ hj))
      | right j =>
        simp only [targetVertex_root, targetVertex_right] at h
        exact False.elim (haAvoid (by
          have hj := right_mem_endpoints P (e j)
          exact h ▸ hj))
  | left i =>
      cases s with
      | root =>
        simp only [targetVertex_left, targetVertex_root] at h
        exact False.elim (haAvoid (by
          have hi := left_mem_endpoints P (e i)
          exact h.symm ▸ hi))
      | left j =>
          simp only [targetVertex_left] at h
          congr 1
          exact e.injective (left_injective P h)
      | center j =>
        simp only [targetVertex_left, targetVertex_center] at h
        exact False.elim (Set.disjoint_left.mp hG.disjoint
          (P.left_mem (e i)) (by
            have hj : (e j : W) ∈ Y := hY₂ (e j).property
            exact h ▸ hj))
      | right j =>
          simp only [targetVertex_left, targetVertex_right] at h
          exfalso
          exact P.left_ne_right (e i) (e j) h
  | center i =>
      cases s with
      | root =>
        simp only [targetVertex_center, targetVertex_root] at h
        exact False.elim (Set.disjoint_left.mp hG.disjoint ha (by
          have hi : (e i : W) ∈ Y := hY₂ (e i).property
          exact h.symm ▸ hi))
      | left j =>
        simp only [targetVertex_center, targetVertex_left] at h
        exact False.elim (Set.disjoint_left.mp hG.disjoint
          (P.left_mem (e j)) (by
            have hi : (e i : W) ∈ Y := hY₂ (e i).property
            exact h.symm ▸ hi))
      | center j =>
          simp only [targetVertex_center] at h
          congr 1
          exact e.injective (Subtype.ext h)
      | right j =>
        simp only [targetVertex_center, targetVertex_right] at h
        exact False.elim (Set.disjoint_left.mp hG.disjoint
          (P.right_mem (e j)) (by
            have hi : (e i : W) ∈ Y := hY₂ (e i).property
            exact h.symm ▸ hi))
  | right i =>
      cases s with
      | root =>
        simp only [targetVertex_right, targetVertex_root] at h
        exact False.elim (haAvoid (by
          have hi := right_mem_endpoints P (e i)
          exact h.symm ▸ hi))
      | left j =>
          simp only [targetVertex_right, targetVertex_left] at h
          exfalso
          exact P.left_ne_right (e j) (e i) h.symm
      | center j =>
        simp only [targetVertex_right, targetVertex_center] at h
        exact False.elim (Set.disjoint_left.mp hG.disjoint
          (P.right_mem (e i)) (by
            have hj : (e j : W) ∈ Y := hY₂ (e j).property
            exact h ▸ hj))
      | right j =>
          simp only [targetVertex_right] at h
          congr 1
          exact e.injective (right_injective P h)

private theorem not_adj_left_part (D : SurgeryData T U₁ U₂ z l k)
    {x y : V} (hx : x ∈ U₁) (hy : y ∈ U₁) : ¬T.Adj x y := by
  intro hxy
  have hy' : y ∈ U₂ := D.bipartite.mem_of_mem_adj hx hxy
  exact Set.disjoint_left.mp D.bipartite.disjoint hy hy'

private theorem not_adj_right_part (D : SurgeryData T U₁ U₂ z l k)
    {x y : V} (hx : x ∈ U₂) (hy : y ∈ U₂) : ¬T.Adj x y := by
  intro hxy
  have hy' : y ∈ U₁ := D.bipartite.symm.mem_of_mem_adj hx hxy
  exact Set.disjoint_left.mp D.bipartite.disjoint hy' hy

private theorem root_not_adj_exceptional_path
    (D : SurgeryData T U₁ U₂ z l k) (i : Fin k)
    {x : V} (hx : x ∈ (D.exceptionalPath i).vertices) : ¬T.Adj z x := by
  simp only [ZhaoSurgeryAlt.TwoPath.vertices, Finset.mem_insert,
    Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl
  · exact not_adj_left_part D D.z_mem (D.p_left_mem _)
  · intro hz
    rcases (D.exceptionalPath i).eq_left_or_right_of_adj_center
        (D.p_special _).1 hz with hzl | hzr
    · apply D.z_avoid_p (exceptionalPIndex l i)
      exact Eq.mpr (congrArg
        (fun q : V => q ∈ (D.exceptionalPath i).vertices) hzl)
        (D.exceptionalPath i).left_mem_vertices
    · apply D.z_avoid_p (exceptionalPIndex l i)
      exact Eq.mpr (congrArg
        (fun q : V => q ∈ (D.exceptionalPath i).vertices) hzr)
        (D.exceptionalPath i).right_mem_vertices
  · exact not_adj_left_part D D.z_mem (D.p_right_mem _)

private theorem not_adj_path_vertex_other_center
    (D : SurgeryData T U₁ U₂ z l k) {i j : Fin k} (hij : i ≠ j)
    {x : V} (hx : x ∈ (D.exceptionalPath i).vertices) :
    ¬T.Adj x (D.exceptionalPath j).center := by
  intro hxc
  have hidx : exceptionalPIndex l i ≠ exceptionalPIndex l j := by
    intro he
    apply hij
    exact Fin.ext (by simpa using congrArg Fin.val he)
  have hd := D.p_disjoint (exceptionalPIndex l i) (exceptionalPIndex l j) hidx
  rcases (D.exceptionalPath j).eq_left_or_right_of_adj_center
      (D.p_special _).1 hxc with hxl | hxr
  · have hxj : x ∈ (D.exceptionalPath j).vertices :=
      Eq.mpr (congrArg (fun q : V => q ∈ (D.exceptionalPath j).vertices) hxl)
        (D.exceptionalPath j).left_mem_vertices
    exact Finset.disjoint_left.mp hd hx hxj
  · have hxj : x ∈ (D.exceptionalPath j).vertices :=
      Eq.mpr (congrArg (fun q : V => q ∈ (D.exceptionalPath j).vertices) hxr)
        (D.exceptionalPath j).right_mem_vertices
    exact Finset.disjoint_left.mp hd hx hxj

/-- The named source and target maps preserve every edge induced by the fixed set. -/
theorem targetVertex_map_adj
    (D : SurgeryData T U₁ U₂ z l k)
    (P : CenteredTwoPathSystem G X Y₂) (e : Fin k ≃ Y₂) (a : W) :
    ∀ r s : ExceptionalIndex k,
      D.forest.Adj (ExceptionalIndex.sourceVertex D r)
          (ExceptionalIndex.sourceVertex D s) →
        G.Adj (targetVertex P e a r) (targetVertex P e a s) := by
  intro r s hrs
  have hT : T.Adj (ExceptionalIndex.sourceVertex D r : V)
      (ExceptionalIndex.sourceVertex D s : V) := hrs
  cases r with
  | root =>
      cases s with
      | root => exact (hT.ne rfl).elim
      | left j => exact (root_not_adj_exceptional_path D j
            (D.exceptionalPath j).left_mem_vertices hT).elim
      | center j => exact (root_not_adj_exceptional_path D j
            (D.exceptionalPath j).center_mem_vertices hT).elim
      | right j => exact (root_not_adj_exceptional_path D j
            (D.exceptionalPath j).right_mem_vertices hT).elim
  | left i =>
      cases s with
      | root => exact (root_not_adj_exceptional_path D i
            (D.exceptionalPath i).left_mem_vertices hT.symm).elim
      | left j => exact
          (not_adj_left_part D (D.p_left_mem _) (D.p_left_mem _) hT).elim
      | center j =>
          by_cases hij : i = j
          · subst j
            exact P.adj_left (e i)
          · exact (not_adj_path_vertex_other_center D hij
              (D.exceptionalPath i).left_mem_vertices hT).elim
      | right j => exact
          (not_adj_left_part D (D.p_left_mem _) (D.p_right_mem _) hT).elim
  | center i =>
      cases s with
      | root => exact (root_not_adj_exceptional_path D i
            (D.exceptionalPath i).center_mem_vertices hT.symm).elim
      | left j =>
          by_cases hij : i = j
          · subst j
            exact (P.adj_left (e i)).symm
          · exact (not_adj_path_vertex_other_center D (Ne.symm hij)
              (D.exceptionalPath j).left_mem_vertices hT.symm).elim
      | center j => exact
          (not_adj_right_part D (D.p_center_mem _) (D.p_center_mem _) hT).elim
      | right j =>
          by_cases hij : i = j
          · subst j
            exact P.adj_right (e i)
          · exact (not_adj_path_vertex_other_center D (Ne.symm hij)
              (D.exceptionalPath j).right_mem_vertices hT.symm).elim
  | right i =>
      cases s with
      | root => exact (root_not_adj_exceptional_path D i
            (D.exceptionalPath i).right_mem_vertices hT.symm).elim
      | left j => exact
          (not_adj_left_part D (D.p_right_mem _) (D.p_left_mem _) hT).elim
      | center j =>
          by_cases hij : i = j
          · subst j
            exact (P.adj_right (e i)).symm
          · exact (not_adj_path_vertex_other_center D hij
              (D.exceptionalPath i).right_mem_vertices hT).elim
      | right j => exact
          (not_adj_left_part D (D.p_right_mem _) (D.p_right_mem _) hT).elim

/-- The prescribed map, with domain literally the finite fixed source set. -/
def premap (D : SurgeryData T U₁ U₂ z l k)
    (P : CenteredTwoPathSystem G X Y₂) (e : Fin k ≃ Y₂) (a : W) :
    sourceSet D → W := fun x => targetVertex P e a ((sourceEquiv D).symm x)

@[simp] theorem premap_sourceVertex
    (D : SurgeryData T U₁ U₂ z l k)
    (P : CenteredTwoPathSystem G X Y₂) (e : Fin k ≃ Y₂) (a : W)
    (r : ExceptionalIndex k) :
    premap D P e a ⟨sourceVertex D r, sourceVertex_mem_sourceSet D r⟩ =
      targetVertex P e a r := by
  change targetVertex P e a
      ((sourceEquiv D).symm ((sourceEquiv D) r)) = targetVertex P e a r
  rw [(sourceEquiv D).symm_apply_apply]

theorem premap_injective
    (D : SurgeryData T U₁ U₂ z l k)
    (P : CenteredTwoPathSystem G X Y₂) (e : Fin k ≃ Y₂) (a : W)
    (hG : G.IsBipartiteWith (X : Set W) (Y : Set W))
    (hY₂ : Y₂ ⊆ Y) (ha : a ∈ X) (haAvoid : a ∉ P.endpoints) :
    Function.Injective (premap D P e a) :=
  (targetVertex_injective P e a hG hY₂ ha haAvoid).comp (sourceEquiv D).symm.injective

theorem premap_map_adj
    (D : SurgeryData T U₁ U₂ z l k)
    (P : CenteredTwoPathSystem G X Y₂) (e : Fin k ≃ Y₂) (a : W) :
    ∀ x y : sourceSet D,
      D.forest.Adj x.1 y.1 → G.Adj (premap D P e a x) (premap D P e a y) := by
  intro x y hxy
  generalize hrdef : (sourceEquiv D).symm x = r
  generalize hsdef : (sourceEquiv D).symm y = s
  have hr : (sourceEquiv D) r = x := by
    rw [← hrdef]
    exact (sourceEquiv D).apply_symm_apply x
  have hs : (sourceEquiv D) s = y := by
    rw [← hsdef]
    exact (sourceEquiv D).apply_symm_apply y
  have hr' : sourceVertex D r = x.1 := congrArg Subtype.val hr
  have hs' : sourceVertex D s = y.1 := congrArg Subtype.val hs
  have hsrc : D.forest.Adj (sourceVertex D r) (sourceVertex D s) := by
    rw [hr', hs']
    exact hxy
  simpa only [premap, hrdef, hsdef] using targetVertex_map_adj D P e a r s hsrc

theorem premap_mem_X_or_Y₂
    (D : SurgeryData T U₁ U₂ z l k)
    (P : CenteredTwoPathSystem G X Y₂) (e : Fin k ≃ Y₂) (a : W)
    (ha : a ∈ X) (x : sourceSet D) :
    premap D P e a x ∈ X ∨ premap D P e a x ∈ Y₂ := by
  generalize hrdef : (sourceEquiv D).symm x = r
  change targetVertex P e a ((sourceEquiv D).symm x) ∈ X ∨
    targetVertex P e a ((sourceEquiv D).symm x) ∈ Y₂
  rw [hrdef]
  cases r with
  | root => exact Or.inl ha
  | left i => exact Or.inl (P.left_mem (e i))
  | center i => exact Or.inr (e i).property
  | right i => exact Or.inl (P.right_mem (e i))

theorem premap_mem_X_of_source_mem_U₁
    (D : SurgeryData T U₁ U₂ z l k)
    (P : CenteredTwoPathSystem G X Y₂) (e : Fin k ≃ Y₂) (a : W)
    (ha : a ∈ X) (x : sourceSet D) (hx : (x.1 : V) ∈ U₁) :
    premap D P e a x ∈ X := by
  generalize hrdef : (sourceEquiv D).symm x = r
  have hr : (sourceEquiv D) r = x := by
    rw [← hrdef]
    exact (sourceEquiv D).apply_symm_apply x
  have hr' : sourceVertex D r = x.1 := congrArg Subtype.val hr
  change targetVertex P e a ((sourceEquiv D).symm x) ∈ X
  rw [hrdef]
  cases r with
  | root => exact ha
  | left i => exact P.left_mem (e i)
  | center i =>
      exfalso
      exact Set.disjoint_left.mp D.bipartite.disjoint hx
        (by simpa [← hr'] using D.p_center_mem (exceptionalPIndex l i))
  | right i => exact P.right_mem (e i)

theorem premap_mem_Y₂_of_source_mem_U₂
    (D : SurgeryData T U₁ U₂ z l k)
    (P : CenteredTwoPathSystem G X Y₂) (e : Fin k ≃ Y₂) (a : W)
    (x : sourceSet D) (hx : (x.1 : V) ∈ U₂) :
    premap D P e a x ∈ Y₂ := by
  generalize hrdef : (sourceEquiv D).symm x = r
  have hr : (sourceEquiv D) r = x := by
    rw [← hrdef]
    exact (sourceEquiv D).apply_symm_apply x
  have hr' : sourceVertex D r = x.1 := congrArg Subtype.val hr
  change targetVertex P e a ((sourceEquiv D).symm x) ∈ Y₂
  rw [hrdef]
  cases r with
  | root =>
      exfalso
      exact Set.disjoint_left.mp D.bipartite.disjoint D.z_mem
        (by simpa [← hr'] using hx)
  | left i =>
      exfalso
      exact Set.disjoint_left.mp D.bipartite.disjoint
        (D.p_left_mem (exceptionalPIndex l i)) (by simpa [← hr'] using hx)
  | center i => exact (e i).property
  | right i =>
      exfalso
      exact Set.disjoint_left.mp D.bipartite.disjoint
        (D.p_right_mem (exceptionalPIndex l i)) (by simpa [← hr'] using hx)

theorem premap_zero
    (D : SurgeryData T U₁ U₂ z l k)
    (P : CenteredTwoPathSystem G X Y₂) (e : Fin k ≃ Y₂) (a : W)
    (c : D.forest.Coloring (Fin 2))
    (hc₀ : ∀ x, c x = 0 → (x : V) ∈ U₁) (ha : a ∈ X) :
    ∀ x : sourceSet D, c x.1 = 0 → premap D P e a x ∈ X := by
  intro x hx
  exact premap_mem_X_of_source_mem_U₁ D P e a ha x (hc₀ x.1 hx)

theorem premap_one
    (D : SurgeryData T U₁ U₂ z l k)
    (P : CenteredTwoPathSystem G X Y₂) (e : Fin k ≃ Y₂) (a : W)
    (c : D.forest.Coloring (Fin 2))
    (hc₁ : ∀ x, c x = 1 → (x : V) ∈ U₂) :
    ∀ x : sourceSet D, c x.1 = 1 → premap D P e a x ∈ Y₂ := by
  intro x hx
  exact premap_mem_Y₂_of_source_mem_U₂ D P e a x (hc₁ x.1 hx)

@[simp] theorem premap_root
    (D : SurgeryData T U₁ U₂ z l k)
    (P : CenteredTwoPathSystem G X Y₂) (e : Fin k ≃ Y₂) (a : W) :
    premap D P e a
      ⟨sourceVertex D root, sourceVertex_mem_sourceSet D root⟩ = a := by
  rw [premap_sourceVertex]
  rfl

/-- A fixed prescribed image that lies in the `X` core comes from colour zero. -/
theorem premap_core_color
    (D : SurgeryData T U₁ U₂ z l k)
    (P : CenteredTwoPathSystem G X Y₂) (e : Fin k ≃ Y₂) (a : W)
    (c : D.forest.Coloring (Fin 2))
    (hc₀ : ∀ x, c x = 0 ↔ (x : V) ∈ U₁) (ha : a ∈ X)
    (Y₁ : Finset W) (hXY₂ : Disjoint X Y₂)
    (hXY₁ : Disjoint X Y₁) (hY₁Y₂ : Disjoint Y₁ Y₂)
    (Q : Fin 2 → Finset W) (hQ₀ : Q 0 = X) (hQ₁ : Q 1 = Y₁) :
    ∀ (y : sourceSet D) (i : Fin 2), premap D P e a y ∈ Q i → c y.1 = i := by
  intro y i hy
  fin_cases i
  · change premap D P e a y ∈ Q 0 at hy
    change c y.1 = 0
    rw [hQ₀] at hy
    apply (hc₀ y.1).2
    generalize hrdef : (sourceEquiv D).symm y = r
    have hr : (sourceEquiv D) r = y := by
      rw [← hrdef]
      exact (sourceEquiv D).apply_symm_apply y
    have hr' : sourceVertex D r = y.1 := congrArg Subtype.val hr
    change targetVertex P e a ((sourceEquiv D).symm y) ∈ X at hy
    rw [hrdef] at hy
    cases r with
    | root => simpa [← hr'] using D.z_mem
    | left j => simpa [← hr'] using D.p_left_mem (exceptionalPIndex l j)
    | center j =>
        exact False.elim (Finset.disjoint_left.mp hXY₂ hy (e j).property)
    | right j => simpa [← hr'] using D.p_right_mem (exceptionalPIndex l j)
  · change premap D P e a y ∈ Q 1 at hy
    change c y.1 = 1
    rw [hQ₁] at hy
    rcases premap_mem_X_or_Y₂ D P e a ha y with hyX | hyY₂
    · exact False.elim (Finset.disjoint_left.mp hXY₁ hyX hy)
    · exact False.elim (Finset.disjoint_left.mp hY₁Y₂ hy hyY₂)

/-- Any edge from outside the fixed set to a fixed vertex ends at an `X`-mapped
fixed vertex.  In particular the prescribed `Y₂` centres have no outside
neighbour, since their degree-two neighborhood is their displayed path. -/
theorem premap_fixed_neighbor_core
    (D : SurgeryData T U₁ U₂ z l k)
    (P : CenteredTwoPathSystem G X Y₂) (e : Fin k ≃ Y₂) (a : W)
    (c : D.forest.Coloring (Fin 2))
    (hc₀ : ∀ x, c x = 0 ↔ (x : V) ∈ U₁) (ha : a ∈ X)
    (Q : Fin 2 → Finset W) (hQ₀ : Q 0 = X) :
    ∀ x, x ∉ sourceSet D → ∀ y : sourceSet D,
      D.forest.Adj x y.1 → premap D P e a y ∈ Q (c y.1) := by
  intro x hx y hxy
  generalize hrdef : (sourceEquiv D).symm y = r
  have hr : (sourceEquiv D) r = y := by
    rw [← hrdef]
    exact (sourceEquiv D).apply_symm_apply y
  have hr' : sourceVertex D r = y.1 := congrArg Subtype.val hr
  have hT0 : T.Adj (x : V) (y.1 : V) := hxy
  have hT : T.Adj (x : V) (sourceVertex D r : V) := by
    rw [hr']
    exact hT0
  cases r with
  | root =>
      have hc : c y.1 = 0 := (hc₀ y.1).2 (by simpa [← hr'] using D.z_mem)
      rw [hc, hQ₀]
      change targetVertex P e a ((sourceEquiv D).symm y) ∈ X
      rw [hrdef]
      exact ha
  | left j =>
      have hc : c y.1 = 0 := (hc₀ y.1).2
        (by simpa [← hr'] using D.p_left_mem (exceptionalPIndex l j))
      rw [hc, hQ₀]
      change targetVertex P e a ((sourceEquiv D).symm y) ∈ X
      rw [hrdef]
      exact P.left_mem (e j)
  | center j =>
      exfalso
      rcases (D.exceptionalPath j).eq_left_or_right_of_adj_center
          (D.p_special _).1 hT with hxl | hxr
      · apply hx
        have heq : x = sourceVertex D (left j) := Subtype.ext hxl
        rw [heq]
        exact sourceVertex_mem_sourceSet D (left j)
      · apply hx
        have heq : x = sourceVertex D (right j) := Subtype.ext hxr
        rw [heq]
        exact sourceVertex_mem_sourceSet D (right j)
  | right j =>
      have hc : c y.1 = 0 := (hc₀ y.1).2
        (by simpa [← hr'] using D.p_right_mem (exceptionalPIndex l j))
      rw [hc, hQ₀]
      change targetVertex P e a ((sourceEquiv D).symm y) ∈ X
      rw [hrdef]
      exact P.right_mem (e j)

private theorem q_left_not_deleted
    (D : SurgeryData T U₁ U₂ z l k) (i : Fin (4 * l)) :
    (D.Q i).left ∉ D.deleted := by
  rw [SurgeryData.deleted, Finset.mem_union, not_or]
  constructor
  · intro hP
    obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hP
    have hd := D.pq_disjoint (initialPIndex l k j) i
    exact Finset.disjoint_left.mp hd
      (D.P (initialPIndex l k j)).center_mem_vertices
      (Eq.mpr (congrArg (fun q : V => q ∈ (D.Q i).vertices) hj)
        (D.Q i).left_mem_vertices)
  · intro hQ
    obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hQ
    by_cases hij : i = j
    · subst j
      exact (D.Q i).left_ne_center hj.symm
    · have hd := D.q_disjoint j i (Ne.symm hij)
      exact Finset.disjoint_left.mp hd (D.Q j).center_mem_vertices
        (Eq.mpr (congrArg (fun q : V => q ∈ (D.Q i).vertices) hj)
          (D.Q i).left_mem_vertices)

private theorem q_right_not_deleted
    (D : SurgeryData T U₁ U₂ z l k) (i : Fin (4 * l)) :
    (D.Q i).right ∉ D.deleted := by
  rw [SurgeryData.deleted, Finset.mem_union, not_or]
  constructor
  · intro hP
    obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hP
    have hd := D.pq_disjoint (initialPIndex l k j) i
    exact Finset.disjoint_left.mp hd
      (D.P (initialPIndex l k j)).center_mem_vertices
      (Eq.mpr (congrArg (fun q : V => q ∈ (D.Q i).vertices) hj)
        (D.Q i).right_mem_vertices)
  · intro hQ
    obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hQ
    by_cases hij : i = j
    · subst j
      exact (D.Q i).center_ne_right hj
    · have hd := D.q_disjoint j i (Ne.symm hij)
      exact Finset.disjoint_left.mp hd (D.Q j).center_mem_vertices
        (Eq.mpr (congrArg (fun q : V => q ∈ (D.Q i).vertices) hj)
          (D.Q i).right_mem_vertices)

/-- The two surviving endpoints of a deleted `Q`-centre, as forest vertices. -/
def qLeftVertex (D : SurgeryData T U₁ U₂ z l k) (i : Fin (4 * l)) :
    {x : V // x ∉ D.deleted} := ⟨(D.Q i).left, q_left_not_deleted D i⟩

def qRightVertex (D : SurgeryData T U₁ U₂ z l k) (i : Fin (4 * l)) :
    {x : V // x ∉ D.deleted} := ⟨(D.Q i).right, q_right_not_deleted D i⟩

private theorem q_vertex_not_sourceSet
    (D : SurgeryData T U₁ U₂ z l k) (i : Fin (4 * l))
    (v : {x : V // x ∉ D.deleted}) (hv : (v : V) ∈ (D.Q i).vertices) :
    v ∉ sourceSet D := by
  intro hvS
  obtain ⟨r, -, hr⟩ := Finset.mem_image.mp hvS
  have hrV : (sourceVertex D r : V) = v := congrArg Subtype.val hr
  cases r with
  | root =>
      apply D.z_avoid_q i
      exact Eq.mpr (congrArg (fun q : V => q ∈ (D.Q i).vertices) hrV) hv
  | left j =>
      have hd := D.pq_disjoint (exceptionalPIndex l j) i
      exact Finset.disjoint_left.mp hd (D.exceptionalPath j).left_mem_vertices
        (Eq.mpr (congrArg (fun q : V => q ∈ (D.Q i).vertices) hrV) hv)
  | center j =>
      have hd := D.pq_disjoint (exceptionalPIndex l j) i
      exact Finset.disjoint_left.mp hd (D.exceptionalPath j).center_mem_vertices
        (Eq.mpr (congrArg (fun q : V => q ∈ (D.Q i).vertices) hrV) hv)
  | right j =>
      have hd := D.pq_disjoint (exceptionalPIndex l j) i
      exact Finset.disjoint_left.mp hd (D.exceptionalPath j).right_mem_vertices
        (Eq.mpr (congrArg (fun q : V => q ∈ (D.Q i).vertices) hrV) hv)

theorem qLeftVertex_not_mem_sourceSet
    (D : SurgeryData T U₁ U₂ z l k) (i : Fin (4 * l)) :
    qLeftVertex D i ∉ sourceSet D :=
  q_vertex_not_sourceSet D i (qLeftVertex D i) (D.Q i).left_mem_vertices

theorem qRightVertex_not_mem_sourceSet
    (D : SurgeryData T U₁ U₂ z l k) (i : Fin (4 * l)) :
    qRightVertex D i ∉ sourceSet D :=
  q_vertex_not_sourceSet D i (qRightVertex D i) (D.Q i).right_mem_vertices

private theorem initial_p_left_not_deleted
    (D : SurgeryData T U₁ U₂ z l k) (i : Fin (4 * l)) :
    (D.P (initialPIndex l k i)).left ∉ D.deleted := by
  rw [SurgeryData.deleted, Finset.mem_union, not_or]
  constructor
  · intro hP
    exact Set.disjoint_left.mp D.bipartite.disjoint (D.p_left_mem _)
      (D.deletedP_subset hP)
  · intro hQ
    obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hQ
    have hd := D.pq_disjoint (initialPIndex l k i) j
    have hpj : (D.Q j).center ∈ (D.P (initialPIndex l k i)).vertices :=
      Eq.mpr (congrArg
        (fun q : V => q ∈ (D.P (initialPIndex l k i)).vertices) hj)
        (D.P (initialPIndex l k i)).left_mem_vertices
    exact Finset.disjoint_left.mp hd hpj (D.Q j).center_mem_vertices

private theorem initial_p_right_not_deleted
    (D : SurgeryData T U₁ U₂ z l k) (i : Fin (4 * l)) :
    (D.P (initialPIndex l k i)).right ∉ D.deleted := by
  rw [SurgeryData.deleted, Finset.mem_union, not_or]
  constructor
  · intro hP
    exact Set.disjoint_left.mp D.bipartite.disjoint (D.p_right_mem _)
      (D.deletedP_subset hP)
  · intro hQ
    obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hQ
    have hd := D.pq_disjoint (initialPIndex l k i) j
    have hpj : (D.Q j).center ∈ (D.P (initialPIndex l k i)).vertices :=
      Eq.mpr (congrArg
        (fun q : V => q ∈ (D.P (initialPIndex l k i)).vertices) hj)
        (D.P (initialPIndex l k i)).right_mem_vertices
    exact Finset.disjoint_left.mp hd hpj (D.Q j).center_mem_vertices

def initialPLeftVertex (D : SurgeryData T U₁ U₂ z l k) (i : Fin (4 * l)) :
    {x : V // x ∉ D.deleted} :=
  ⟨(D.P (initialPIndex l k i)).left, initial_p_left_not_deleted D i⟩

def initialPRightVertex (D : SurgeryData T U₁ U₂ z l k) (i : Fin (4 * l)) :
    {x : V // x ∉ D.deleted} :=
  ⟨(D.P (initialPIndex l k i)).right, initial_p_right_not_deleted D i⟩

private theorem initial_p_vertex_not_sourceSet
    (D : SurgeryData T U₁ U₂ z l k) (i : Fin (4 * l))
    (v : {x : V // x ∉ D.deleted})
    (hv : (v : V) ∈ (D.P (initialPIndex l k i)).vertices) :
    v ∉ sourceSet D := by
  intro hvS
  obtain ⟨r, -, hr⟩ := Finset.mem_image.mp hvS
  have hrV : (sourceVertex D r : V) = v := congrArg Subtype.val hr
  cases r with
  | root =>
      apply D.z_avoid_p (initialPIndex l k i)
      exact Eq.mpr (congrArg
        (fun q : V => q ∈ (D.P (initialPIndex l k i)).vertices) hrV) hv
  | left j =>
      have hd := D.p_disjoint (exceptionalPIndex l j) (initialPIndex l k i)
        (initialPIndex_ne_exceptionalPIndex l i j).symm
      exact Finset.disjoint_left.mp hd (D.exceptionalPath j).left_mem_vertices
        (Eq.mpr (congrArg
          (fun q : V => q ∈ (D.P (initialPIndex l k i)).vertices) hrV) hv)
  | center j =>
      have hd := D.p_disjoint (exceptionalPIndex l j) (initialPIndex l k i)
        (initialPIndex_ne_exceptionalPIndex l i j).symm
      exact Finset.disjoint_left.mp hd (D.exceptionalPath j).center_mem_vertices
        (Eq.mpr (congrArg
          (fun q : V => q ∈ (D.P (initialPIndex l k i)).vertices) hrV) hv)
  | right j =>
      have hd := D.p_disjoint (exceptionalPIndex l j) (initialPIndex l k i)
        (initialPIndex_ne_exceptionalPIndex l i j).symm
      exact Finset.disjoint_left.mp hd (D.exceptionalPath j).right_mem_vertices
        (Eq.mpr (congrArg
          (fun q : V => q ∈ (D.P (initialPIndex l k i)).vertices) hrV) hv)

theorem initialPLeftVertex_not_mem_sourceSet
    (D : SurgeryData T U₁ U₂ z l k) (i : Fin (4 * l)) :
    initialPLeftVertex D i ∉ sourceSet D :=
  initial_p_vertex_not_sourceSet D i (initialPLeftVertex D i)
    (D.P (initialPIndex l k i)).left_mem_vertices

theorem initialPRightVertex_not_mem_sourceSet
    (D : SurgeryData T U₁ U₂ z l k) (i : Fin (4 * l)) :
    initialPRightVertex D i ∉ sourceSet D :=
  initial_p_vertex_not_sourceSet D i (initialPRightVertex D i)
    (D.P (initialPIndex l k i)).right_mem_vertices

theorem premap_mem_Y₂_iff_center
    (D : SurgeryData T U₁ U₂ z l k)
    (P : CenteredTwoPathSystem G X Y₂) (e : Fin k ≃ Y₂) (a : W)
    (hdisj : Disjoint X Y₂) (ha : a ∈ X) (x : sourceSet D) :
    premap D P e a x ∈ Y₂ ↔
      ∃ i : Fin k, x.1 = sourceVertex D (center i) := by
  generalize hrdef : (sourceEquiv D).symm x = r
  have hr : (sourceEquiv D) r = x := by
    rw [← hrdef]
    exact (sourceEquiv D).apply_symm_apply x
  have hr' : sourceVertex D r = x.1 := congrArg Subtype.val hr
  change targetVertex P e a ((sourceEquiv D).symm x) ∈ Y₂ ↔ _
  rw [hrdef]
  cases r with
  | root =>
      constructor
      · intro hay
        exact False.elim (Finset.disjoint_left.mp hdisj ha hay)
      · rintro ⟨i, hi⟩
        have heq := sourceVertex_injective D (hr'.trans hi)
        cases heq
  | left j =>
      constructor
      · intro hy
        exact False.elim (Finset.disjoint_left.mp hdisj (P.left_mem (e j)) hy)
      · rintro ⟨i, hi⟩
        have := sourceVertex_injective D (hr'.trans hi)
        cases this
  | center j =>
      constructor
      · intro _
        exact ⟨j, hr'.symm⟩
      · intro _
        exact (e j).property
  | right j =>
      constructor
      · intro hy
        exact False.elim (Finset.disjoint_left.mp hdisj (P.right_mem (e j)) hy)
      · rintro ⟨i, hi⟩
        have := sourceVertex_injective D (hr'.trans hi)
        cases this

end ExceptionalIndex

end Erdos547b.ZhaoExceptionalPremapAlt


/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

open scoped SimpleGraph

noncomputable section

namespace Erdos547b.ZhaoBoundaryApplication710

open Finset SimpleGraph
open Erdos547b.ZhaoSurgeryAlt
open Erdos547b.ZhaoLemma710Alt
open Erdos547b.ZhaoExceptionalPremapAlt

attribute [local instance] Classical.propDecidable

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {T : SimpleGraph V} [DecidableRel T.Adj]
variable {U₁ U₂ : Finset V} {z : V} {l k : ℕ}

/-- The exceptional centres, now regarded as vertices of the surgically
reduced forest. -/
def exceptionalCenters (D : SurgeryData T U₁ U₂ z l k) :
    Finset {x : V // x ∉ D.deleted} :=
  Finset.univ.image fun i : Fin k =>
    ExceptionalIndex.sourceVertex D (.center i)

private theorem degree_eq_two_of_neighbor_ncard_eq_two
    (G : SimpleGraph V) [DecidableRel G.Adj] {v : V}
    (h : (G.neighborSet v).ncard = 2) : G.degree v = 2 := by
  rw [← G.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_def,
    ← Set.ncard_eq_toFinset_card']
  exact h

private theorem degree_le_two_of_neighbor_ncard_le_two
    (G : SimpleGraph V) [DecidableRel G.Adj] {v : V}
    (h : (G.neighborSet v).ncard ≤ 2) : G.degree v ≤ 2 := by
  rw [← G.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_def,
    ← Set.ncard_eq_toFinset_card']
  exact h

/-- Passing to an induced graph cannot increase degree. -/
theorem forest_degree_le_original
    (D : SurgeryData T U₁ U₂ z l k)
    (x : {v : V // v ∉ D.deleted}) :
    D.forest.degree x ≤ T.degree x.1 := by
  classical
  rw [← T.card_neighborFinset_eq_degree,
    ← D.forest.card_neighborFinset_eq_degree]
  let e : {v : V // v ∉ D.deleted} ↪ V := Function.Embedding.subtype _
  have hsub : (D.forest.neighborFinset x).map e ⊆ T.neighborFinset x.1 := by
    intro y hy
    obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp hy
    rw [T.mem_neighborFinset]
    exact (D.forest.mem_neighborFinset x w).mp hw
  have hc := Finset.card_le_card hsub
  simpa [e] using hc

/-- Each exceptional centre remains a Zhao-special centre after the surgery. -/
theorem exceptionalCenter_special
    (D : SurgeryData T U₁ U₂ z l k) (i : Fin k) :
    IsSpecialTwoPathCenter D.forest
      (ExceptionalIndex.sourceVertex D (.center i)) := by
  classical
  let : DecidableRel D.forest.Adj := Classical.decRel _
  let P := D.exceptionalPath i
  let c : {v : V // v ∉ D.deleted} := ExceptionalIndex.sourceVertex D (.center i)
  have hcval : (c : V) = P.center := rfl
  have hTdeg : T.degree P.center = 2 :=
    degree_eq_two_of_neighbor_ncard_eq_two T (D.p_special (exceptionalPIndex l i)).1
  have hneighborsSurvive : T.neighborSet P.center ⊆ (D.deleted : Set V)ᶜ := by
    intro y hy
    have hyAdj : T.Adj P.center y := hy
    rcases P.eq_left_or_right_of_adj_center
        (D.p_special (exceptionalPIndex l i)).1 hyAdj.symm with rfl | rfl
    · exact D.exceptional_vertex_not_deleted i P.left_mem_vertices
    · exact D.exceptional_vertex_not_deleted i P.right_mem_vertices
  have hFdeg : D.forest.degree c = 2 := by
    apply Nat.le_antisymm
    · have hcdeg : T.degree c.1 = 2 := by
        change T.degree P.center = 2
        exact hTdeg
      exact (forest_degree_le_original D c).trans hcdeg.le
    · let pl : {v : V // v ∉ D.deleted} :=
          ExceptionalIndex.sourceVertex D (.left i)
      let pr : {v : V // v ∉ D.deleted} :=
          ExceptionalIndex.sourceVertex D (.right i)
      have hne : pl ≠ pr := by
        intro h
        exact P.left_ne_right (congrArg Subtype.val h)
      have hsub : ({pl, pr} : Finset {v : V // v ∉ D.deleted}) ⊆
          D.forest.neighborFinset c := by
        intro y hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with rfl | rfl
        · exact (D.forest.mem_neighborFinset c pl).mpr
            (by
              change D.forest.Adj
                ⟨P.center, _⟩ ⟨P.left, _⟩
              exact (D.exceptional_path_survives i).1.symm)
        · exact (D.forest.mem_neighborFinset c pr).mpr
            (by
              change D.forest.Adj
                ⟨P.center, _⟩ ⟨P.right, _⟩
              exact (D.exceptional_path_survives i).2)
      have hc := Finset.card_le_card hsub
      rw [Finset.card_pair hne, D.forest.card_neighborFinset_eq_degree] at hc
      exact hc
  refine ⟨hFdeg, ?_⟩
  intro x hx
  obtain ⟨y, hyN, hyx⟩ := Finset.mem_biUnion.mp hx
  have hcyF : D.forest.Adj c y := (D.forest.mem_neighborFinset c y).mp hyN
  have hcyT : T.Adj P.center y.1 := by
    change T.Adj P.center y.1
    exact hcyF
  rcases P.eq_left_or_right_of_adj_center
      (D.p_special (exceptionalPIndex l i)).1 hcyT.symm with hyL | hyR
  · have hxyT : T.Adj x.1 P.left := by
      have hxyF : D.forest.Adj y x := (D.forest.mem_neighborFinset y x).mp hyx
      have : T.Adj y.1 x.1 := hxyF
      rw [hyL] at this
      exact this.symm
    have hsmall := (D.p_special (exceptionalPIndex l i)).2 x.1 (Or.inl hxyT)
    exact (forest_degree_le_original D x).trans
      (degree_le_two_of_neighbor_ncard_le_two T hsmall)
  · have hxyT : T.Adj x.1 P.right := by
      have hxyF : D.forest.Adj y x := (D.forest.mem_neighborFinset y x).mp hyx
      have : T.Adj y.1 x.1 := hxyF
      rw [hyR] at this
      exact this.symm
    have hsmall := (D.p_special (exceptionalPIndex l i)).2 x.1 (Or.inr hxyT)
    exact (forest_degree_le_original D x).trans
      (degree_le_two_of_neighbor_ncard_le_two T hsmall)

theorem exceptionalCenters_special
    (D : SurgeryData T U₁ U₂ z l k) :
    ∀ c ∈ exceptionalCenters D, IsSpecialTwoPathCenter D.forest c := by
  classical
  let : DecidableRel D.forest.Adj := Classical.decRel _
  intro c hc
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hc
  exact exceptionalCenter_special D i

/-- The abstract protected set of the exceptional centres is literally the
canonical source set used by the exceptional premap. -/
theorem protectedTwoPathSet_exceptionalCenters_eq_sourceSet
    (D : SurgeryData T U₁ U₂ z l k) :
    protectedTwoPathSet D.forest
        (ExceptionalIndex.sourceVertex D .root) (exceptionalCenters D) =
      ExceptionalIndex.sourceSet D := by
  classical
  let : DecidableRel D.forest.Adj := Classical.decRel _
  ext x
  constructor
  · intro hx
    rw [mem_protectedTwoPathSet] at hx
    rcases hx with hxroot | ⟨c, hcC, hxc | hcx⟩
    · rw [hxroot]
      exact ExceptionalIndex.sourceVertex_mem_sourceSet D .root
    · rw [hxc]
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hcC
      exact ExceptionalIndex.sourceVertex_mem_sourceSet D (.center i)
    · obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hcC
      subst c
      have hT : T.Adj (D.exceptionalPath i).center x.1 := hcx
      rcases (D.exceptionalPath i).eq_left_or_right_of_adj_center
          (D.p_special (exceptionalPIndex l i)).1 hT.symm with hxL | hxR
      · have hxEq : x = ExceptionalIndex.sourceVertex D (.left i) := by
          apply Subtype.ext
          exact hxL
        rw [hxEq]
        exact ExceptionalIndex.sourceVertex_mem_sourceSet D (.left i)
      · have hxEq : x = ExceptionalIndex.sourceVertex D (.right i) := by
          apply Subtype.ext
          exact hxR
        rw [hxEq]
        exact ExceptionalIndex.sourceVertex_mem_sourceSet D (.right i)
  · intro hx
    obtain ⟨r, -, hr⟩ := Finset.mem_image.mp hx
    subst x
    cases r with
    | root =>
        exact mem_protectedTwoPathSet.mpr (Or.inl rfl)
    | left i =>
        apply mem_protectedTwoPathSet.mpr
        right
        let c := ExceptionalIndex.sourceVertex D (.center i)
        refine ⟨c, ?_, Or.inr ?_⟩
        · exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
        · exact (D.exceptional_path_survives i).1.symm
    | center i =>
        apply mem_protectedTwoPathSet.mpr
        right
        let c := ExceptionalIndex.sourceVertex D (.center i)
        refine ⟨c, ?_, Or.inl rfl⟩
        exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    | right i =>
        apply mem_protectedTwoPathSet.mpr
        right
        let c := ExceptionalIndex.sourceVertex D (.center i)
        refine ⟨c, ?_, Or.inr ?_⟩
        · exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
        · exact (D.exceptional_path_survives i).2

/-- Boundary sparsity in the exact `SurgeryData`/`sourceSet` interface used
by the full proof of Zhao's Lemma 7.10. -/
theorem forest_sourceSet_boundary_sparse
    (D : SurgeryData T U₁ U₂ z l k) :
    ∀ x, x ∉ ExceptionalIndex.sourceSet D →
      (D.forest.neighborFinset x ∩ ExceptionalIndex.sourceSet D).card ≤ 1 ∨
        D.forest.degree x ≤ 2 := by
  classical
  let : DecidableRel D.forest.Adj := Classical.decRel _
  intro x hx
  have heq := protectedTwoPathSet_exceptionalCenters_eq_sourceSet D
  have hx' : x ∉ protectedTwoPathSet D.forest
      (ExceptionalIndex.sourceVertex D .root) (exceptionalCenters D) := by
    simpa only [heq] using hx
  have h := boundary_sparse_of_special_twoPathCenters
    (exceptionalCenters_special D) hx'
  simpa only [heq] using h

end Erdos547b.ZhaoBoundaryApplication710

#print axioms Erdos547b.ZhaoBoundaryApplication710.forest_sourceSet_boundary_sparse


/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

/-!
# The balanced Hall step for reinserting deleted midpoints

The first theorem is the elementary balanced minimum-degree form of Hall's
theorem.  The second theorem derives its hypotheses from the situation used
in Zhao's proof: there are `4*l` endpoint pairs and `4*l` candidates, all
`8*l` endpoints are distinct, and every vertex has at most `l` missing
cross-edges.  Hence an endpoint pair has at least `2*l` common candidates,
while a candidate is incompatible with at most `l` endpoint pairs.
-/

open Finset

namespace Erdos547b.ZhaoHallMidpointAlt

universe u v w

/-- A balanced bipartite relation with `4*l` vertices on each side and
minimum degree at least `2*l` has a matching saturating the left side. -/
theorem exists_injective_assignment_of_balanced_half_degree
    {I : Type u} {Y : Type v} [Fintype I] [DecidableEq I] [DecidableEq Y]
    (l : ℕ) (C : Finset Y) (Good : I → Y → Prop) [DecidableRel Good]
    (hI : Fintype.card I = 4 * l) (hC : #C = 4 * l)
    (hleft : ∀ i : I, 2 * l ≤ #(C.filter (Good i)))
    (hright : ∀ y ∈ C, 2 * l ≤ #(Finset.univ.filter fun i : I => Good i y)) :
    ∃ f : I → Y, Function.Injective f ∧
      ∀ i : I, f i ∈ C ∧ Good i (f i) := by
  classical
  let N : I → Finset {y // y ∈ C} := fun i =>
    Finset.univ.filter fun y => Good i (y : Y)
  have hNcard (i : I) : #(N i) = #(C.filter (Good i)) := by
    let e : {y // y ∈ C} ↪ Y := Function.Embedding.subtype _
    have himage : (N i).map e = C.filter (Good i) := by
      ext y
      simp [N, e, and_comm]
    rw [← himage, Finset.card_map]
  have hHall : ∀ S : Finset I, #S ≤ #(S.biUnion N) := by
    intro S
    by_cases hSempty : S = ∅
    · simp [hSempty]
    by_cases hsmall : 2 * #S ≤ 4 * l
    · obtain ⟨i, hiS⟩ := Finset.nonempty_iff_ne_empty.mpr hSempty
      have hsub : N i ⊆ S.biUnion N := fun y hy =>
        Finset.mem_biUnion.mpr ⟨i, hiS, hy⟩
      have hdeg := hleft i
      rw [← hNcard i] at hdeg
      have hcardmono := Finset.card_le_card hsub
      omega
    · have hlarge : 4 * l < 2 * #S := Nat.lt_of_not_ge hsmall
      have hfull : S.biUnion N = Finset.univ := by
        apply Finset.eq_univ_of_forall
        intro y
        by_contra hy
        let M : Finset I := Finset.univ.filter fun i => Good i (y : Y)
        have hMsub : M ⊆ Finset.univ \ S := by
          intro i hiM
          rw [Finset.mem_sdiff]
          refine ⟨Finset.mem_univ _, ?_⟩
          intro hiS
          apply hy
          exact Finset.mem_biUnion.mpr ⟨i, hiS,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hiM).2⟩⟩
        have hdis : Disjoint M S := by
          rw [Finset.disjoint_left]
          intro i hiM hiS
          exact (Finset.mem_sdiff.mp (hMsub hiM)).2 hiS
        have hsum : #M + #S ≤ Fintype.card I := by
          calc
            #M + #S = #(M ∪ S) := (Finset.card_union_of_disjoint hdis).symm
            _ ≤ #Finset.univ := Finset.card_le_card (Finset.subset_univ _)
            _ = Fintype.card I := Finset.card_univ
        have hdeg := hright (y : Y) y.2
        change 2 * l ≤ #M at hdeg
        rw [hI] at hsum
        omega
      rw [hfull]
      simp only [Finset.card_univ]
      calc
        #S ≤ Fintype.card I := Finset.card_le_univ S
        _ = 4 * l := hI
        _ = #C := hC.symm
        _ = Fintype.card {y // y ∈ C} := by simp
  obtain ⟨g, hginj, hgmem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_exists_injective N).mp hHall
  refine ⟨fun i => (g i : Y), ?_, ?_⟩
  · exact Subtype.val_injective.comp hginj
  · intro i
    have hi := Finset.mem_filter.mp (hgmem i)
    exact ⟨(g i).2, hi.2⟩

/-- The midpoint-reinsertion step in the form directly supplied by a dense
host pair.  The map `(i,b) ↦ endpoint` being injective says that the two
endpoints of every pair, and the endpoints belonging to different pairs,
are all distinct.

The two defect assumptions count missing edges in the candidate set `C`
and in the whole endpoint-side type `X`, respectively. -/
theorem exists_injective_common_neighbor_assignment
    {I : Type u} {X : Type v} {Y : Type w}
    [Fintype I] [DecidableEq I] [Fintype X] [DecidableEq X] [DecidableEq Y]
    (l : ℕ) (C : Finset Y) (R : X → Y → Prop) [DecidableRel R]
    (left right : I → X)
    (hI : Fintype.card I = 4 * l) (hC : #C = 4 * l)
    (hendpoints : Function.Injective fun ib : I × Bool =>
      if ib.2 then right ib.1 else left ib.1)
    (hdefect_left : ∀ x : X, #(C.filter fun y => ¬ R x y) ≤ l)
    (hdefect_right : ∀ y ∈ C,
      #(Finset.univ.filter fun x : X => ¬ R x y) ≤ l) :
    ∃ f : I → Y, Function.Injective f ∧
      ∀ i : I, f i ∈ C ∧ R (left i) (f i) ∧ R (right i) (f i) := by
  classical
  let Good : I → Y → Prop := fun i y => R (left i) y ∧ R (right i) y
  have hleftdegree : ∀ i : I, 2 * l ≤ #(C.filter (Good i)) := by
    intro i
    let badLeft : Finset Y := C.filter fun y => ¬ R (left i) y
    let badRight : Finset Y := C.filter fun y => ¬ R (right i) y
    let bad : Finset Y := C.filter fun y => ¬ Good i y
    have hbadsub : bad ⊆ badLeft ∪ badRight := by
      intro y hy
      simp only [bad, badLeft, badRight, Good, Finset.mem_filter,
        Finset.mem_union] at hy ⊢
      tauto
    have hbadcard : #bad ≤ 2 * l := by
      calc
        #bad ≤ #(badLeft ∪ badRight) := Finset.card_le_card hbadsub
        _ ≤ #badLeft + #badRight := Finset.card_union_le _ _
        _ ≤ l + l := Nat.add_le_add (hdefect_left (left i)) (hdefect_left (right i))
        _ = 2 * l := by omega
    have hpartition := Finset.card_filter_add_card_filter_not (s := C) (Good i)
    change #(C.filter (Good i)) + #bad = #C at hpartition
    omega
  have hrightdegree : ∀ y ∈ C,
      2 * l ≤ #(Finset.univ.filter fun i : I => Good i y) := by
    intro y hyC
    let bad : Finset I := Finset.univ.filter fun i => ¬ Good i y
    let badX : Finset X := Finset.univ.filter fun x => ¬ R x y
    let pick : I → X := fun i => if R (left i) y then right i else left i
    have hpick : Function.Injective pick := by
      intro i j hij
      let tag : I → Bool := fun k => if R (left k) y then true else false
      have htag :
          (if tag i then right i else left i) =
            (if tag j then right j else left j) := by
        simpa [tag, pick] using hij
      have hpairs : (i, tag i) = (j, tag j) := hendpoints htag
      exact congrArg Prod.fst hpairs
    have himage : bad.image pick ⊆ badX := by
      intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      have hibad : ¬ Good i y := (Finset.mem_filter.mp hi).2
      simp only [badX, Finset.mem_filter, Finset.mem_univ, true_and]
      by_cases hiLeft : R (left i) y
      · have hiRight : ¬ R (right i) y := by
          intro hiRight
          exact hibad ⟨hiLeft, hiRight⟩
        simpa [pick, hiLeft] using hiRight
      · simpa [pick, hiLeft] using hiLeft
    have hbadcard : #bad ≤ l := by
      calc
        #bad = #(bad.image pick) := (Finset.card_image_of_injective _ hpick).symm
        _ ≤ #badX := Finset.card_le_card himage
        _ ≤ l := hdefect_right y hyC
    have hpartition := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset I)) (fun i : I => Good i y)
    change #(Finset.univ.filter fun i : I => Good i y) + #bad = Fintype.card I at hpartition
    omega
  obtain ⟨f, hfinj, hf⟩ :=
    exists_injective_assignment_of_balanced_half_degree
      l C Good hI hC hleftdegree hrightdegree
  exact ⟨f, hfinj, hf⟩

#print axioms exists_injective_assignment_of_balanced_half_degree
#print axioms exists_injective_common_neighbor_assignment

end Erdos547b.ZhaoHallMidpointAlt


/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

/-! # Reinserting the deleted path centres in Zhao's Lemma 7.10 -/

open scoped SimpleGraph

noncomputable section

namespace Erdos547b.ZhaoReinsertDeletedAlt

open Finset SimpleGraph
open Erdos547b.ZhaoSurgeryAlt
open Erdos547b.ZhaoFixedExtend2

universe u v

variable {V : Type u} {W : Type v}
variable [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

/-- The vertices already occupied by a copy. -/
def usedVertices {H : SimpleGraph V} {G : SimpleGraph W} (f : H.Copy G) : Finset W :=
  Finset.univ.image f

theorem mem_usedVertices {H : SimpleGraph V} {G : SimpleGraph W} (f : H.Copy G)
    (x : V) : f x ∈ usedVertices f := by
  exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩

theorem not_mem_range_of_mem_sdiff_used
    {H : SimpleGraph V} {G : SimpleGraph W} (f : H.Copy G)
    {S : Finset W} {y : W} (hy : y ∈ S \ usedVertices f) (x : V) :
    f x ≠ y := by
  intro h
  exact (Finset.mem_sdiff.mp hy).2 (h ▸ mem_usedVertices f x)

/-- Choose exactly `r` unused vertices from a host set. -/
theorem exists_exact_unused
    {H : SimpleGraph V} {G : SimpleGraph W} (f : H.Copy G)
    (S : Finset W) (r : ℕ) (hfree : r ≤ #(S \ usedVertices f)) :
    ∃ C : Finset W, C ⊆ S \ usedVertices f ∧ #C = r :=
  Finset.exists_subset_card_eq hfree

/-- The `4*l` reserve in `fixed_forest_embedding` really remains unused.
The fixed vertices consume precisely the fixed part of `coreDemand`, while
every nonfixed vertex consumes precisely the part indexed by its colour. -/
theorem four_mul_le_card_part_sdiff_used_of_coreDemand
    {A : Type u} {B : Type v}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    {F : SimpleGraph A} {G : SimpleGraph B}
    (c : F.Coloring (Fin 2)) (S : Finset A) (p : S → B)
    (Q : Fin 2 → Finset B) (l : ℕ) (i : Fin 2) (f : F.Copy G)
    (hQ : Set.PairwiseDisjoint Set.univ Q)
    (hp_core_color : ∀ (y : S) (j : Fin 2), p y ∈ Q j → c y = j)
    (hfixed : ∀ x : S, f x = p x)
    (hout : ∀ x, x ∉ S → f x ∈ Q (c x))
    (hcapacity : #(coreDemand c S p i (Q i)) + 4 * l ≤ #(Q i)) :
    4 * l ≤ #((Q i) \ usedVertices f) := by
  classical
  let Dmd : Finset A := coreDemand c S p i (Q i)
  have himage : Q i ∩ usedVertices f = Dmd.image f := by
    ext y
    constructor
    · intro hy
      have hyQ := (Finset.mem_inter.mp hy).1
      obtain ⟨x, -, hxy⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hy).2
      apply Finset.mem_image.mpr
      refine ⟨x, ?_, hxy⟩
      have hfxQ : f x ∈ Q i := by simpa only [hxy] using hyQ
      change x ∈ coreDemand c S p i (Q i)
      rw [coreDemand, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_, ?_⟩
      · by_cases hxS : x ∈ S
        · let xs : S := ⟨x, hxS⟩
          have hfix : f x = p xs := by simpa only [xs] using hfixed xs
          exact hp_core_color xs i (by simpa only [hfix] using hfxQ)
        · have houtx := hout x hxS
          by_contra hci
          exact Finset.disjoint_left.mp
            (hQ (Set.mem_univ (c x)) (Set.mem_univ i) hci)
            houtx hfxQ
      · intro hxS
        let xs : S := ⟨x, hxS⟩
        have hfix : f x = p xs := by simpa only [xs] using hfixed xs
        simpa only [hfix] using hfxQ
    · intro hy
      obtain ⟨x, hxD, hxy⟩ := Finset.mem_image.mp hy
      change x ∈ coreDemand c S p i (Q i) at hxD
      have hx := Finset.mem_filter.mp hxD
      have hfxQ : f x ∈ Q i := by
        by_cases hxS : x ∈ S
        · have hp := hx.2.2 hxS
          have hfix := hfixed ⟨x, hxS⟩
          simpa only [hfix] using hp
        · have ho := hout x hxS
          simpa only [hx.2.1] using ho
      exact Finset.mem_inter.mpr ⟨hxy ▸ hfxQ,
        Finset.mem_image.mpr ⟨x, Finset.mem_univ _, hxy⟩⟩
  have hDcard : #(Dmd.image f) = #Dmd :=
    Finset.card_image_iff.mpr fun _ _ _ _ h => f.injective h
  have hsplit := Finset.card_sdiff_add_card_inter (Q i) (usedVertices f)
  rw [himage, hDcard] at hsplit
  dsimp only [Dmd] at hsplit
  omega

section Surgery

variable {T : SimpleGraph V} {U₁ U₂ : Finset V} {z : V} {l k : ℕ}

private theorem initialPIndex_injective :
    Function.Injective (initialPIndex l k) := by
  intro i j h
  apply Fin.ext
  simpa using congrArg Fin.val h

private theorem p_left_not_deleted
    (D : SurgeryData T U₁ U₂ z l k) (i : Fin (4 * l)) :
    (D.P (initialPIndex l k i)).left ∉ D.deleted := by
  simp only [SurgeryData.deleted, Finset.mem_union, not_or]
  constructor
  · intro h
    obtain ⟨j, -, hj⟩ := Finset.mem_image.mp h
    by_cases hij : i = j
    · subst j
      exact (D.P (initialPIndex l k i)).left_ne_center hj.symm
    · have hindex : initialPIndex l k i ≠ initialPIndex l k j :=
        fun h => hij (initialPIndex_injective h)
      exact Finset.disjoint_left.mp (D.p_disjoint _ _ hindex)
        (D.P (initialPIndex l k i)).left_mem_vertices
        (hj ▸ (D.P (initialPIndex l k j)).center_mem_vertices)
  · intro h
    obtain ⟨j, -, hj⟩ := Finset.mem_image.mp h
    exact Finset.disjoint_left.mp (D.pq_disjoint (initialPIndex l k i) j)
      (D.P (initialPIndex l k i)).left_mem_vertices
      (hj ▸ (D.Q j).center_mem_vertices)

private theorem p_right_not_deleted
    (D : SurgeryData T U₁ U₂ z l k) (i : Fin (4 * l)) :
    (D.P (initialPIndex l k i)).right ∉ D.deleted := by
  simp only [SurgeryData.deleted, Finset.mem_union, not_or]
  constructor
  · intro h
    obtain ⟨j, -, hj⟩ := Finset.mem_image.mp h
    by_cases hij : i = j
    · subst j
      exact (D.P (initialPIndex l k i)).center_ne_right hj
    · have hindex : initialPIndex l k i ≠ initialPIndex l k j :=
        fun h => hij (initialPIndex_injective h)
      exact Finset.disjoint_left.mp (D.p_disjoint _ _ hindex)
        (D.P (initialPIndex l k i)).right_mem_vertices
        (hj ▸ (D.P (initialPIndex l k j)).center_mem_vertices)
  · intro h
    obtain ⟨j, -, hj⟩ := Finset.mem_image.mp h
    exact Finset.disjoint_left.mp (D.pq_disjoint (initialPIndex l k i) j)
      (D.P (initialPIndex l k i)).right_mem_vertices
      (hj ▸ (D.Q j).center_mem_vertices)

private theorem q_left_not_deleted
    (D : SurgeryData T U₁ U₂ z l k) (i : Fin (4 * l)) :
    (D.Q i).left ∉ D.deleted := by
  simp only [SurgeryData.deleted, Finset.mem_union, not_or]
  constructor
  · intro h
    obtain ⟨j, -, hj⟩ := Finset.mem_image.mp h
    exact Finset.disjoint_left.mp (D.pq_disjoint (initialPIndex l k j) i)
      (hj ▸ (D.P (initialPIndex l k j)).center_mem_vertices)
      (D.Q i).left_mem_vertices
  · intro h
    obtain ⟨j, -, hj⟩ := Finset.mem_image.mp h
    by_cases hij : i = j
    · subst j
      exact (D.Q i).left_ne_center hj.symm
    · exact Finset.disjoint_left.mp (D.q_disjoint i j hij)
        (D.Q i).left_mem_vertices
        (hj ▸ (D.Q j).center_mem_vertices)

private theorem q_right_not_deleted
    (D : SurgeryData T U₁ U₂ z l k) (i : Fin (4 * l)) :
    (D.Q i).right ∉ D.deleted := by
  simp only [SurgeryData.deleted, Finset.mem_union, not_or]
  constructor
  · intro h
    obtain ⟨j, -, hj⟩ := Finset.mem_image.mp h
    exact Finset.disjoint_left.mp (D.pq_disjoint (initialPIndex l k j) i)
      (hj ▸ (D.P (initialPIndex l k j)).center_mem_vertices)
      (D.Q i).right_mem_vertices
  · intro h
    obtain ⟨j, -, hj⟩ := Finset.mem_image.mp h
    by_cases hij : i = j
    · subst j
      exact (D.Q i).center_ne_right hj
    · exact Finset.disjoint_left.mp (D.q_disjoint i j hij)
        (D.Q i).right_mem_vertices
        (hj ▸ (D.Q j).center_mem_vertices)

def pLeftVertex (D : SurgeryData T U₁ U₂ z l k) (i : Fin (4 * l)) :
    {v : V // v ∉ D.deleted} :=
  ⟨(D.P (initialPIndex l k i)).left, p_left_not_deleted D i⟩

def pRightVertex (D : SurgeryData T U₁ U₂ z l k) (i : Fin (4 * l)) :
    {v : V // v ∉ D.deleted} :=
  ⟨(D.P (initialPIndex l k i)).right, p_right_not_deleted D i⟩

def qLeftVertex (D : SurgeryData T U₁ U₂ z l k) (i : Fin (4 * l)) :
    {v : V // v ∉ D.deleted} :=
  ⟨(D.Q i).left, q_left_not_deleted D i⟩

def qRightVertex (D : SurgeryData T U₁ U₂ z l k) (i : Fin (4 * l)) :
    {v : V // v ∉ D.deleted} :=
  ⟨(D.Q i).right, q_right_not_deleted D i⟩

private theorem p_raw_endpoints_injective
    (D : SurgeryData T U₁ U₂ z l k) :
    Function.Injective fun ib : Fin (4 * l) × Bool =>
      if ib.2 then (D.P (initialPIndex l k ib.1)).right
      else (D.P (initialPIndex l k ib.1)).left := by
  rintro ⟨i, bi⟩ ⟨j, bj⟩ h
  cases bi <;> cases bj
  · change (D.P (initialPIndex l k i)).left =
      (D.P (initialPIndex l k j)).left at h
    have hij : i = j := by
      by_contra hne
      have hindex : initialPIndex l k i ≠ initialPIndex l k j :=
        fun e => hne (initialPIndex_injective e)
      exact Finset.disjoint_left.mp (D.p_disjoint _ _ hindex)
        (D.P (initialPIndex l k i)).left_mem_vertices
        (h.symm ▸ (D.P (initialPIndex l k j)).left_mem_vertices)
    subst j
    rfl
  · change (D.P (initialPIndex l k i)).left =
      (D.P (initialPIndex l k j)).right at h
    by_cases hij : i = j
    · subst j
      exact False.elim ((D.P (initialPIndex l k i)).left_ne_right h)
    · have hindex : initialPIndex l k i ≠ initialPIndex l k j :=
        fun e => hij (initialPIndex_injective e)
      exact False.elim (Finset.disjoint_left.mp (D.p_disjoint _ _ hindex)
        (D.P (initialPIndex l k i)).left_mem_vertices
        (h.symm ▸ (D.P (initialPIndex l k j)).right_mem_vertices))
  · change (D.P (initialPIndex l k i)).right =
      (D.P (initialPIndex l k j)).left at h
    by_cases hij : i = j
    · subst j
      exact False.elim ((D.P (initialPIndex l k i)).left_ne_right h.symm)
    · have hindex : initialPIndex l k i ≠ initialPIndex l k j :=
        fun e => hij (initialPIndex_injective e)
      exact False.elim (Finset.disjoint_left.mp (D.p_disjoint _ _ hindex)
        (D.P (initialPIndex l k i)).right_mem_vertices
        (h.symm ▸ (D.P (initialPIndex l k j)).left_mem_vertices))
  · change (D.P (initialPIndex l k i)).right =
      (D.P (initialPIndex l k j)).right at h
    have hij : i = j := by
      by_contra hne
      have hindex : initialPIndex l k i ≠ initialPIndex l k j :=
        fun e => hne (initialPIndex_injective e)
      exact Finset.disjoint_left.mp (D.p_disjoint _ _ hindex)
        (D.P (initialPIndex l k i)).right_mem_vertices
        (h.symm ▸ (D.P (initialPIndex l k j)).right_mem_vertices)
    subst j
    rfl

private theorem q_raw_endpoints_injective
    (D : SurgeryData T U₁ U₂ z l k) :
    Function.Injective fun ib : Fin (4 * l) × Bool =>
      if ib.2 then (D.Q ib.1).right else (D.Q ib.1).left := by
  rintro ⟨i, bi⟩ ⟨j, bj⟩ h
  cases bi <;> cases bj
  · change (D.Q i).left = (D.Q j).left at h
    have hij : i = j := by
      by_contra hne
      exact Finset.disjoint_left.mp (D.q_disjoint i j hne)
        (D.Q i).left_mem_vertices (h.symm ▸ (D.Q j).left_mem_vertices)
    subst j
    rfl
  · change (D.Q i).left = (D.Q j).right at h
    by_cases hij : i = j
    · subst j
      exact False.elim ((D.Q i).left_ne_right h)
    · exact False.elim (Finset.disjoint_left.mp (D.q_disjoint i j hij)
        (D.Q i).left_mem_vertices (h.symm ▸ (D.Q j).right_mem_vertices))
  · change (D.Q i).right = (D.Q j).left at h
    by_cases hij : i = j
    · subst j
      exact False.elim ((D.Q i).left_ne_right h.symm)
    · exact False.elim (Finset.disjoint_left.mp (D.q_disjoint i j hij)
        (D.Q i).right_mem_vertices (h.symm ▸ (D.Q j).left_mem_vertices))
  · change (D.Q i).right = (D.Q j).right at h
    have hij : i = j := by
      by_contra hne
      exact Finset.disjoint_left.mp (D.q_disjoint i j hne)
        (D.Q i).right_mem_vertices (h.symm ▸ (D.Q j).right_mem_vertices)
    subst j
    rfl

theorem p_image_endpoints_injective {G : SimpleGraph W}
    (D : SurgeryData T U₁ U₂ z l k) (f : D.forest.Copy G) :
    Function.Injective fun ib : Fin (4 * l) × Bool =>
      if ib.2 then f (pRightVertex D ib.1) else f (pLeftVertex D ib.1) := by
  intro a b h
  apply p_raw_endpoints_injective D
  have hv : (if a.2 then pRightVertex D a.1 else pLeftVertex D a.1) =
      (if b.2 then pRightVertex D b.1 else pLeftVertex D b.1) := by
    apply f.injective
    change (if a.2 then f.toHom (pRightVertex D a.1) else f.toHom (pLeftVertex D a.1)) =
      (if b.2 then f.toHom (pRightVertex D b.1) else f.toHom (pLeftVertex D b.1)) at h
    simpa only [apply_ite] using h
  simpa only [apply_ite, pRightVertex, pLeftVertex] using congrArg Subtype.val hv

theorem q_image_endpoints_injective {G : SimpleGraph W}
    (D : SurgeryData T U₁ U₂ z l k) (f : D.forest.Copy G) :
    Function.Injective fun ib : Fin (4 * l) × Bool =>
      if ib.2 then f (qRightVertex D ib.1) else f (qLeftVertex D ib.1) := by
  intro a b h
  apply q_raw_endpoints_injective D
  have hv : (if a.2 then qRightVertex D a.1 else qLeftVertex D a.1) =
      (if b.2 then qRightVertex D b.1 else qLeftVertex D b.1) := by
    apply f.injective
    change (if a.2 then f.toHom (qRightVertex D a.1) else f.toHom (qLeftVertex D a.1)) =
      (if b.2 then f.toHom (qRightVertex D b.1) else f.toHom (qLeftVertex D b.1)) at h
    simpa only [apply_ite] using h
  simpa only [apply_ite, qRightVertex, qLeftVertex] using congrArg Subtype.val hv

private theorem card_filter_subtype_eq_filter (S : Finset W) (p : W → Prop)
    [DecidablePred p] :
    #(Finset.filter (fun x : S => p x) Finset.univ) = #(S.filter p) := by
  let e : S ↪ W := Function.Embedding.subtype _
  have hmap : (Finset.filter (fun x : S => p x) Finset.univ).map e = S.filter p := by
    ext x
    simp [e, and_comm]
  rw [← hmap, Finset.card_map]

/-- Hall assignment for the deleted `P` centres.  The endpoints have already
been embedded in `X`, and the new centres are chosen, distinctly, from an
unused `4*l`-set in `Y₁`. -/
theorem exists_P_center_assignment {G : SimpleGraph W} [DecidableRel G.Adj]
    (D : SurgeryData T U₁ U₂ z l k) (f : D.forest.Copy G)
    (X Y₁ C : Finset W)
    (hCsub : C ⊆ Y₁ \ usedVertices f) (hCcard : #C = 4 * l)
    (hleftX : ∀ i, f (pLeftVertex D i) ∈ X)
    (hrightX : ∀ i, f (pRightVertex D i) ∈ X)
    (hdefectXY : ∀ x ∈ X, #(Y₁.filter fun y => ¬G.Adj x y) ≤ l)
    (hdefectYX : ∀ y ∈ Y₁, #(X.filter fun x => ¬G.Adj x y) ≤ l) :
    ∃ gP : Fin (4 * l) → W, Function.Injective gP ∧
      ∀ i, gP i ∈ C ∧ G.Adj (f (pLeftVertex D i)) (gP i) ∧
        G.Adj (f (pRightVertex D i)) (gP i) := by
  classical
  let left : Fin (4 * l) → X := fun i => ⟨f (pLeftVertex D i), hleftX i⟩
  let right : Fin (4 * l) → X := fun i => ⟨f (pRightVertex D i), hrightX i⟩
  let R : X → W → Prop := fun x y => G.Adj x y
  have hend : Function.Injective fun ib : Fin (4 * l) × Bool =>
      if ib.2 then right ib.1 else left ib.1 := by
    intro a b h
    apply p_image_endpoints_injective D f
    simpa only [left, right, apply_ite] using congrArg Subtype.val h
  have hdefL : ∀ x : X, #(C.filter fun y => ¬R x y) ≤ l := by
    intro x
    have hsub : C.filter (fun y => ¬R x y) ⊆
        Y₁.filter (fun y => ¬G.Adj x y) := by
      intro y hy
      have hy' := Finset.mem_filter.mp hy
      exact Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp (hCsub hy'.1)).1, hy'.2⟩
    exact (Finset.card_le_card hsub).trans (hdefectXY x x.property)
  have hdefR : ∀ y ∈ C,
      #((Finset.univ : Finset X).filter fun x => ¬R x y) ≤ l := by
    intro y hy
    change #(Finset.filter (fun x : X => ¬G.Adj x y) Finset.univ) ≤ l
    calc
      #(Finset.filter (fun x : X => ¬G.Adj x y) Finset.univ) =
          #(X.filter fun x => ¬G.Adj x y) :=
        card_filter_subtype_eq_filter X (fun x => ¬G.Adj x y)
      _ ≤ l := hdefectYX y (Finset.mem_sdiff.mp (hCsub hy)).1
  obtain ⟨gP, hinj, hgP⟩ :=
    Erdos547b.ZhaoHallMidpointAlt.exists_injective_common_neighbor_assignment
      l C R left right (by simp) hCcard hend hdefL hdefR
  refine ⟨gP, hinj, ?_⟩
  intro i
  simpa only [R, left, right] using hgP i

/-- The symmetric Hall assignment for the deleted `Q` centres.  Here their
endpoints lie in `Y₁`, and their new images are unused vertices of `X`. -/
theorem exists_Q_center_assignment {G : SimpleGraph W} [DecidableRel G.Adj]
    (D : SurgeryData T U₁ U₂ z l k) (f : D.forest.Copy G)
    (X Y₁ C : Finset W)
    (hCsub : C ⊆ X \ usedVertices f) (hCcard : #C = 4 * l)
    (hleftY : ∀ i, f (qLeftVertex D i) ∈ Y₁)
    (hrightY : ∀ i, f (qRightVertex D i) ∈ Y₁)
    (hdefectXY : ∀ x ∈ X, #(Y₁.filter fun y => ¬G.Adj x y) ≤ l)
    (hdefectYX : ∀ y ∈ Y₁, #(X.filter fun x => ¬G.Adj x y) ≤ l) :
    ∃ gQ : Fin (4 * l) → W, Function.Injective gQ ∧
      ∀ i, gQ i ∈ C ∧ G.Adj (gQ i) (f (qLeftVertex D i)) ∧
        G.Adj (gQ i) (f (qRightVertex D i)) := by
  classical
  let left : Fin (4 * l) → Y₁ := fun i => ⟨f (qLeftVertex D i), hleftY i⟩
  let right : Fin (4 * l) → Y₁ := fun i => ⟨f (qRightVertex D i), hrightY i⟩
  let R : Y₁ → W → Prop := fun y x => G.Adj x y
  have hend : Function.Injective fun ib : Fin (4 * l) × Bool =>
      if ib.2 then right ib.1 else left ib.1 := by
    intro a b h
    apply q_image_endpoints_injective D f
    simpa only [left, right, apply_ite] using congrArg Subtype.val h
  have hdefL : ∀ y : Y₁, #(C.filter fun x => ¬R y x) ≤ l := by
    intro y
    have hsub : C.filter (fun x => ¬R y x) ⊆
        X.filter (fun x => ¬G.Adj x y) := by
      intro x hx
      have hx' := Finset.mem_filter.mp hx
      exact Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp (hCsub hx'.1)).1, hx'.2⟩
    exact (Finset.card_le_card hsub).trans (hdefectYX y y.property)
  have hdefR : ∀ x ∈ C,
      #((Finset.univ : Finset Y₁).filter fun y => ¬R y x) ≤ l := by
    intro x hx
    change #(Finset.filter (fun y : Y₁ => ¬G.Adj x y) Finset.univ) ≤ l
    calc
      #(Finset.filter (fun y : Y₁ => ¬G.Adj x y) Finset.univ) =
          #(Y₁.filter fun y => ¬G.Adj x y) :=
        card_filter_subtype_eq_filter Y₁ (fun y => ¬G.Adj x y)
      _ ≤ l := hdefectXY x (Finset.mem_sdiff.mp (hCsub hx)).1
  obtain ⟨gQ, hinj, hgQ⟩ :=
    Erdos547b.ZhaoHallMidpointAlt.exists_injective_common_neighbor_assignment
      l C R left right (by simp) hCcard hend hdefL hdefR
  refine ⟨gQ, hinj, ?_⟩
  intro i
  simpa only [R, left, right] using hgQ i

end Surgery

end Erdos547b.ZhaoReinsertDeletedAlt

#print axioms Erdos547b.ZhaoReinsertDeletedAlt.exists_exact_unused
#print axioms Erdos547b.ZhaoReinsertDeletedAlt.four_mul_le_card_part_sdiff_used_of_coreDemand
#print axioms Erdos547b.ZhaoReinsertDeletedAlt.exists_P_center_assignment
#print axioms Erdos547b.ZhaoReinsertDeletedAlt.exists_Q_center_assignment


/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

/-! # The final midpoint reinsertion in Zhao's Lemma 7.10 -/

open scoped SimpleGraph

noncomputable section

namespace Erdos547b.ZhaoReinsertFinish2

open Finset SimpleGraph
open Erdos547b.ZhaoSurgeryAlt
open Erdos547b.ZhaoReinsertDeletedAlt

universe u v

variable {V : Type u} {W : Type v}
variable [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

private theorem defect_le_of_dense_inter
    (S N : Finset W) (l : ℕ) (h : #S - l ≤ #(N ∩ S)) :
    #(S \ N) ≤ l := by
  have hsplit := Finset.card_sdiff_add_card_inter S N
  rw [Finset.inter_comm N S] at h
  omega

section

variable {T : SimpleGraph V} {G : SimpleGraph W}
variable [DecidableRel T.Adj] [DecidableRel G.Adj]
variable {U₁ U₂ : Finset V} {z : V} {l k : ℕ}

/-- Once the forest from the surgery has been embedded, the `8*l` deleted
centres can be reinserted.  The two applications of Hall use respectively
unused vertices of `Y₁` for the deleted `P`-centres and unused vertices of
`X` for the deleted `Q`-centres.

The degree-two property of the `Q`-centres is part of `SurgeryData`. -/
theorem reinsert_deleted_centers
    (D : SurgeryData T U₁ U₂ z l k)
    (X Y Y₁ : Finset W)
    (f : D.forest.Copy G)
    (hfU₁ : ∀ x : {v : V // v ∉ D.deleted}, x.1 ∈ U₁ → f x ∈ X)
    (hfU₂ : ∀ x : {v : V // v ∉ D.deleted}, x.1 ∈ U₂ → f x ∈ Y)
    (hfQleft : ∀ i, f (qLeftVertex D i) ∈ Y₁)
    (hfQright : ∀ i, f (qRightVertex D i) ∈ Y₁)
    (hY₁Y : Y₁ ⊆ Y)
    (hXY₁ : Disjoint X Y₁)
    (hfreeX : 4 * l ≤ #(X \ usedVertices f))
    (hfreeY₁ : 4 * l ≤ #(Y₁ \ usedVertices f))
    (hdenseXY₁ : ∀ x ∈ X, #Y₁ - l ≤ #((G.neighborFinset x) ∩ Y₁))
    (hdenseY₁X : ∀ y ∈ Y₁, #X - l ≤ #((G.neighborFinset y) ∩ X)) :
    ∃ F : T.Copy G,
      (∀ x : {v : V // v ∉ D.deleted}, F x = f x) ∧
      (∀ x ∈ U₁, F x ∈ X) ∧
      (∀ x ∈ U₂, F x ∈ Y) := by
  classical
  obtain ⟨CP, hCPsub, hCPcard⟩ := exists_exact_unused f Y₁ (4 * l) hfreeY₁
  obtain ⟨CQ, hCQsub, hCQcard⟩ := exists_exact_unused f X (4 * l) hfreeX

  have hdefXY₁ : ∀ x ∈ X, #(Y₁.filter fun y => ¬ G.Adj x y) ≤ l := by
    intro x hx
    have heq : Y₁.filter (fun y => ¬ G.Adj x y) = Y₁ \ G.neighborFinset x := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_sdiff, G.mem_neighborFinset]
    rw [heq]
    exact defect_le_of_dense_inter Y₁ (G.neighborFinset x) l (hdenseXY₁ x hx)
  have hdefY₁X : ∀ y ∈ Y₁, #(X.filter fun x => ¬ G.Adj x y) ≤ l := by
    intro y hy
    have heq : X.filter (fun x => ¬ G.Adj x y) = X \ G.neighborFinset y := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_sdiff, G.mem_neighborFinset]
      exact and_congr_right fun _ => not_congr (G.adj_comm x y)
    rw [heq]
    exact defect_le_of_dense_inter X (G.neighborFinset y) l (hdenseY₁X y hy)
  obtain ⟨pA, hpAinj, hpA⟩ :=
    exists_P_center_assignment D f X Y₁ CP hCPsub hCPcard
      (fun i => hfU₁ _ (D.p_left_mem _))
      (fun i => hfU₁ _ (D.p_right_mem _)) hdefXY₁ hdefY₁X
  obtain ⟨qA, hqAinj, hqA⟩ :=
    exists_Q_center_assignment D f X Y₁ CQ hCQsub hCQcard
      hfQleft hfQright hdefXY₁ hdefY₁X

  -- Canonical inverse indices for the two centre images.
  have hpExists (x : D.deletedP) :
      ∃ i : Fin (4 * l), (D.P (initialPIndex l k i)).center = x := by
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp x.2
    exact ⟨i, hi⟩
  let pIndex : D.deletedP → Fin (4 * l) := fun x => Classical.choose (hpExists x)
  have hpIndex_spec (x : D.deletedP) :
      (D.P (initialPIndex l k (pIndex x))).center = x := by
    exact Classical.choose_spec (hpExists x)
  have hqExists (x : D.deletedQ) : ∃ i : Fin (4 * l), (D.Q i).center = x := by
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp x.2
    exact ⟨i, hi⟩
  let qIndex : D.deletedQ → Fin (4 * l) := fun x => Classical.choose (hqExists x)
  have hqIndex_spec (x : D.deletedQ) : (D.Q (qIndex x)).center = x := by
    exact Classical.choose_spec (hqExists x)

  let g : D.deleted → W := fun x =>
    if hx : x.1 ∈ D.deletedP then pA (pIndex ⟨x.1, hx⟩)
    else qA (qIndex ⟨x.1, (Finset.mem_union.mp x.2).resolve_left hx⟩)

  have hgP (x : D.deleted) (hx : x.1 ∈ D.deletedP) :
      g x = pA (pIndex ⟨x.1, hx⟩) := by simp [g, hx]
  have hgQ (x : D.deleted) (hx : x.1 ∈ D.deletedQ) :
      g x = qA (qIndex ⟨x.1, hx⟩) := by
    have hnotP : x.1 ∉ D.deletedP := fun hp =>
      Finset.disjoint_left.mp D.disjoint_deletedP_deletedQ hp hx
    simp [g, hnotP]
  have hg : Function.Injective g := by
    intro x y hxy
    rcases Finset.mem_union.mp x.2 with hxP | hxQ
    · rcases Finset.mem_union.mp y.2 with hyP | hyQ
      · have hi : pIndex ⟨x.1, hxP⟩ = pIndex ⟨y.1, hyP⟩ := by
          apply hpAinj
          simpa [hgP x hxP, hgP y hyP] using hxy
        apply Subtype.ext
        calc
          x.1 = (D.P (initialPIndex l k (pIndex ⟨x.1, hxP⟩))).center :=
            (hpIndex_spec ⟨x.1, hxP⟩).symm
          _ = (D.P (initialPIndex l k (pIndex ⟨y.1, hyP⟩))).center := by rw [hi]
          _ = y.1 := hpIndex_spec ⟨y.1, hyP⟩
      · exfalso
        have hxY₁ : g x ∈ Y₁ := by
          rw [hgP x hxP]
          exact (Finset.mem_sdiff.mp (hCPsub (hpA _).1)).1
        have hyX : g y ∈ X := by
          rw [hgQ y hyQ]
          exact (Finset.mem_sdiff.mp (hCQsub (hqA _).1)).1
        exact Finset.disjoint_left.mp hXY₁ hyX (hxy ▸ hxY₁)
    · rcases Finset.mem_union.mp y.2 with hyP | hyQ
      · exfalso
        have hxX : g x ∈ X := by
          rw [hgQ x hxQ]
          exact (Finset.mem_sdiff.mp (hCQsub (hqA _).1)).1
        have hyY₁ : g y ∈ Y₁ := by
          rw [hgP y hyP]
          exact (Finset.mem_sdiff.mp (hCPsub (hpA _).1)).1
        exact Finset.disjoint_left.mp hXY₁ hxX (hxy ▸ hyY₁)
      · have hi : qIndex ⟨x.1, hxQ⟩ = qIndex ⟨y.1, hyQ⟩ := by
          apply hqAinj
          simpa [hgQ x hxQ, hgQ y hyQ] using hxy
        apply Subtype.ext
        calc
          x.1 = (D.Q (qIndex ⟨x.1, hxQ⟩)).center :=
            (hqIndex_spec ⟨x.1, hxQ⟩).symm
          _ = (D.Q (qIndex ⟨y.1, hyQ⟩)).center := by rw [hi]
          _ = y.1 := hqIndex_spec ⟨y.1, hyQ⟩

  have hfg : ∀ x y, f x ≠ g y := by
    intro x y h
    rcases Finset.mem_union.mp y.2 with hyP | hyQ
    · have hu := (Finset.mem_sdiff.mp
        (hCPsub (hpA (pIndex ⟨y.1, hyP⟩)).1)).2
      apply hu
      rw [hgP y hyP] at h
      exact h ▸ mem_usedVertices f x
    · have hu := (Finset.mem_sdiff.mp
        (hCQsub (hqA (qIndex ⟨y.1, hyQ⟩)).1)).2
      apply hu
      rw [hgQ y hyQ] at h
      exact h ▸ mem_usedVertices f x

  have hDD : ∀ x y : D.deleted, T.Adj x y → G.Adj (g x) (g y) := by
    intro x y hxy
    exfalso
    rcases Finset.mem_union.mp x.2 with hxP | hxQ
    · let i := pIndex ⟨x.1, hxP⟩
      have hxcenter : (D.P (initialPIndex l k i)).center = x := hpIndex_spec _
      have hyend := (D.P (initialPIndex l k i)).eq_left_or_right_of_adj_center
        (D.p_special _).1 (by simpa only [hxcenter] using hxy.symm)
      rcases hyend with hy | hy
      · apply (pLeftVertex D i).property
        change (D.P (initialPIndex l k i)).left ∈ D.deleted
        rw [← hy]
        exact y.2
      · apply (pRightVertex D i).property
        change (D.P (initialPIndex l k i)).right ∈ D.deleted
        rw [← hy]
        exact y.2
    · let i := qIndex ⟨x.1, hxQ⟩
      have hxcenter : (D.Q i).center = x := hqIndex_spec _
      have hyend := (D.Q i).eq_left_or_right_of_adj_center
        (D.q_degree_two i) (by simpa only [hxcenter] using hxy.symm)
      rcases hyend with hy | hy
      · apply (qLeftVertex D i).property
        change (D.Q i).left ∈ D.deleted
        rw [← hy]
        exact y.2
      · apply (qRightVertex D i).property
        change (D.Q i).right ∈ D.deleted
        rw [← hy]
        exact y.2

  have hDC : ∀ x : D.deleted, ∀ y : ↑((D.deleted : Set V)ᶜ),
      T.Adj x y → G.Adj (g x) (f y) := by
    intro x y hxy
    rcases Finset.mem_union.mp x.2 with hxP | hxQ
    · let i := pIndex ⟨x.1, hxP⟩
      have hxcenter : (D.P (initialPIndex l k i)).center = x := hpIndex_spec _
      have hyend := (D.P (initialPIndex l k i)).eq_left_or_right_of_adj_center
        (D.p_special _).1 (by simpa only [hxcenter] using hxy.symm)
      rw [hgP x hxP]
      rcases hyend with hy | hy
      · have hey : y = pLeftVertex D i := Subtype.ext hy
        subst y
        exact (hpA i).2.1.symm
      · have hey : y = pRightVertex D i := Subtype.ext hy
        subst y
        exact (hpA i).2.2.symm
    · let i := qIndex ⟨x.1, hxQ⟩
      have hxcenter : (D.Q i).center = x := hqIndex_spec _
      have hyend := (D.Q i).eq_left_or_right_of_adj_center
        (D.q_degree_two i) (by simpa only [hxcenter] using hxy.symm)
      rw [hgQ x hxQ]
      rcases hyend with hy | hy
      · have hey : y = qLeftVertex D i := Subtype.ext hy
        subst y
        dsimp only [i]
        exact (hqA _).2.1
      · have hey : y = qRightVertex D i := Subtype.ext hy
        subst y
        dsimp only [i]
        exact (hqA _).2.2

  obtain ⟨F, hFdel, hFforest⟩ :=
    Erdos547b.ZhaoLemma710Alt.copy_of_induce_compl_and_extension
      T G D.deleted f g hg hfg hDD hDC
  refine ⟨F, hFforest, ?_, ?_⟩
  · intro x hxU
    by_cases hx : x ∈ D.deleted
    · have hxQ : x ∈ D.deletedQ := by
        rcases Finset.mem_union.mp hx with hxP | hxQ
        · exact False.elim (Set.disjoint_left.mp D.bipartite.disjoint hxU
            (D.deletedP_subset hxP))
        · exact hxQ
      rw [hFdel ⟨x, hx⟩, hgQ ⟨x, hx⟩ hxQ]
      exact (Finset.mem_sdiff.mp (hCQsub (hqA _).1)).1
    · rw [hFforest ⟨x, by simpa using hx⟩]
      exact hfU₁ _ hxU
  · intro x hxU
    by_cases hx : x ∈ D.deleted
    · have hxP : x ∈ D.deletedP := by
        rcases Finset.mem_union.mp hx with hxP | hxQ
        · exact hxP
        · exact False.elim (Set.disjoint_left.mp D.bipartite.disjoint
            (D.deletedQ_subset hxQ) hxU)
      rw [hFdel ⟨x, hx⟩, hgP ⟨x, hx⟩ hxP]
      exact hY₁Y (Finset.mem_sdiff.mp (hCPsub (hpA _).1)).1
    · rw [hFforest ⟨x, by simpa using hx⟩]
      exact hfU₂ _ hxU

end

end Erdos547b.ZhaoReinsertFinish2

#print axioms Erdos547b.ZhaoReinsertFinish2.reinsert_deleted_centers


/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

open scoped SimpleGraph

noncomputable section

namespace Erdos547b.ZhaoForestColoring710

open Finset SimpleGraph
open Erdos547b.ZhaoSurgeryAlt

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {T : SimpleGraph V} [DecidableRel T.Adj]
variable {U₁ U₂ : Finset V} {z : V} {l k : ℕ}

/-- The two-colouring of Zhao's surgery forest induced by its prescribed
    bipartition.  Colour zero is `U₁` and colour one is `U₂`. -/
def forestColoring (D : SurgeryData T U₁ U₂ z l k) :
    D.forest.Coloring (Fin 2) :=
  SimpleGraph.Coloring.mk
    (fun x => if x.1 ∈ U₁ then 0 else 1)
    (by
      intro x y hxy
      have hxyT : T.Adj x.1 y.1 := hxy
      by_cases hx : x.1 ∈ U₁
      · have hy₂ : y.1 ∈ U₂ := D.bipartite.mem_of_mem_adj hx hxyT
        have hy₁ : y.1 ∉ U₁ := fun hy =>
          Set.disjoint_left.mp D.bipartite.disjoint hy hy₂
        simp [hx, hy₁]
      · have hx₂ : x.1 ∈ U₂ := by
          have hu : x.1 ∈ U₁ ∪ U₂ := by
            rw [D.cover]
            exact Finset.mem_univ _
          exact (Finset.mem_union.mp hu).resolve_left hx
        have hy₁ : y.1 ∈ U₁ :=
          D.bipartite.symm.mem_of_mem_adj hx₂ hxyT
        simp [hx, hy₁])

@[simp] theorem forestColoring_eq_zero_iff
    (D : SurgeryData T U₁ U₂ z l k)
    (x : {v : V // v ∉ D.deleted}) :
    forestColoring D x = 0 ↔ x.1 ∈ U₁ := by
  change (if x.1 ∈ U₁ then (0 : Fin 2) else 1) = 0 ↔ x.1 ∈ U₁
  simp [forestColoring]

@[simp] theorem forestColoring_eq_one_iff
    (D : SurgeryData T U₁ U₂ z l k)
    (x : {v : V // v ∉ D.deleted}) :
    forestColoring D x = 1 ↔ x.1 ∈ U₂ := by
  constructor
  · intro hx
    have hxnot : x.1 ∉ U₁ := by
      intro hx₁
      change (if x.1 ∈ U₁ then (0 : Fin 2) else 1) = 1 at hx
      simp [hx₁] at hx
    have hu : x.1 ∈ U₁ ∪ U₂ := by
      rw [D.cover]
      exact Finset.mem_univ _
    exact (Finset.mem_union.mp hu).resolve_left hxnot
  · intro hx₂
    have hxnot : x.1 ∉ U₁ := fun hx₁ =>
      Set.disjoint_left.mp D.bipartite.disjoint hx₁ hx₂
    change (if x.1 ∈ U₁ then (0 : Fin 2) else 1) = 1
    simp [hxnot]

/-- The zero colour class is in cardinality-preserving bijection with
    `forestLeft`. -/
theorem card_filter_forestColoring_zero
    (D : SurgeryData T U₁ U₂ z l k) :
    #(Finset.univ.filter fun x => forestColoring D x = 0) = #D.forestLeft := by
  let q : (x : {v : V // v ∉ D.deleted}) →
      x ∈ Finset.univ.filter (fun x => forestColoring D x = 0) → V :=
    fun x _ => x.1
  apply Finset.card_bij q
  · intro x hx
    rw [D.mem_forestLeft_iff]
    exact ⟨(forestColoring_eq_zero_iff D x).mp (Finset.mem_filter.mp hx).2,
      x.property⟩
  · intro x hx y hy hxy
    exact Subtype.ext hxy
  · intro v hv
    have hv' := (D.mem_forestLeft_iff v).mp hv
    refine ⟨⟨v, hv'.2⟩, ?_, rfl⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, (forestColoring_eq_zero_iff D _).mpr hv'.1⟩

/-- The one colour class is in cardinality-preserving bijection with
    `forestRight`. -/
theorem card_filter_forestColoring_one
    (D : SurgeryData T U₁ U₂ z l k) :
    #(Finset.univ.filter fun x => forestColoring D x = 1) = #D.forestRight := by
  let q : (x : {v : V // v ∉ D.deleted}) →
      x ∈ Finset.univ.filter (fun x => forestColoring D x = 1) → V :=
    fun x _ => x.1
  apply Finset.card_bij q
  · intro x hx
    rw [D.mem_forestRight_iff]
    exact ⟨(forestColoring_eq_one_iff D x).mp (Finset.mem_filter.mp hx).2,
      x.property⟩
  · intro x hx y hy hxy
    exact Subtype.ext hxy
  · intro v hv
    have hv' := (D.mem_forestRight_iff v).mp hv
    refine ⟨⟨v, hv'.2⟩, ?_, rfl⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, (forestColoring_eq_one_iff D _).mpr hv'.1⟩

theorem partCard_forestColoring_zero
    (D : SurgeryData T U₁ U₂ z l k) :
    Coloring.partCard (forestColoring D) 0 = #U₁ - 4 * l := by
  rw [Coloring.partCard, card_filter_forestColoring_zero D,
    D.card_forestLeft]

theorem partCard_forestColoring_one
    (D : SurgeryData T U₁ U₂ z l k) :
    Coloring.partCard (forestColoring D) 1 = #U₂ - 4 * l := by
  rw [Coloring.partCard, card_filter_forestColoring_one D,
    D.card_forestRight]

/-- Forgetting the subtype gives a cardinality-preserving translation of an
    induced-forest neighbourhood restricted to any finite source set. -/
theorem card_neighborFinset_inter_eq
    (D : SurgeryData T U₁ U₂ z l k)
    [DecidableRel D.forest.Adj]
    (x : {v : V // v ∉ D.deleted})
    (S : Finset {v : V // v ∉ D.deleted}) :
    #(D.forest.neighborFinset x ∩ S) =
      #(T.neighborFinset x.1 ∩ S.image Subtype.val) := by
  let q : (y : {v : V // v ∉ D.deleted}) →
      y ∈ D.forest.neighborFinset x ∩ S → V := fun y _ => y.1
  apply Finset.card_bij q
  · intro y hy
    have hy' := Finset.mem_inter.mp hy
    exact Finset.mem_inter.mpr ⟨by
      rw [T.mem_neighborFinset]
      exact (D.forest.mem_neighborFinset x y).mp hy'.1,
      Finset.mem_image.mpr ⟨y, hy'.2, rfl⟩⟩
  · intro y hy w hw h
    exact Subtype.ext h
  · intro v hv
    have hvN := (Finset.mem_inter.mp hv).1
    obtain ⟨y, hyS, rfl⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hv).2
    refine ⟨y, ?_, rfl⟩
    exact Finset.mem_inter.mpr ⟨by
      rw [D.forest.mem_neighborFinset]
      exact (T.mem_neighborFinset x.1 y.1).mp hvN,
      hyS⟩

#print axioms forestColoring
#print axioms forestColoring_eq_zero_iff
#print axioms forestColoring_eq_one_iff
#print axioms partCard_forestColoring_zero
#print axioms partCard_forestColoring_one
#print axioms card_neighborFinset_inter_eq

end Erdos547b.ZhaoForestColoring710


/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

open scoped SimpleGraph

noncomputable section

namespace Erdos547b.ZhaoLemma710ApplicationAlt

open Finset SimpleGraph
open Erdos547b.ZhaoLemma710Alt
open Erdos547b.ZhaoSurgeryAlt
open Erdos547b.ZhaoFixedExtend2
open Erdos547b.ZhaoExceptionalPremapAlt
open Erdos547b.ZhaoExceptionalPremapAlt.ExceptionalIndex
open Erdos547b.ZhaoForestColoring710
open Erdos547b.ZhaoBoundaryApplication710
open Erdos547b.ZhaoReinsertDeletedAlt
open Erdos547b.ZhaoPackingAdapterAlt

universe u v

variable {V : Type u} {W : Type v}
variable [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

private theorem defect_le_of_dense_inter
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (S : Finset W) (x : W) (l : ℕ)
    (h : #S - l ≤ #((G.neighborFinset x) ∩ S)) :
    #(S.filter fun y => ¬G.Adj x y) ≤ l := by
  have heq : S.filter (fun y => ¬G.Adj x y) = S \ G.neighborFinset x := by
    ext y
    simp [G.mem_neighborFinset]
  rw [heq]
  have hs := Finset.card_sdiff_add_card_inter S (G.neighborFinset x)
  rw [Finset.inter_comm S (G.neighborFinset x)] at hs
  omega

private theorem card_exceptionalCenters
    {T : SimpleGraph V} {U₁ U₂ : Finset V} {z : V} {l k : ℕ}
    (D : SurgeryData T U₁ U₂ z l k) :
    #(exceptionalCenters D) = k := by
  classical
  rw [exceptionalCenters, Finset.card_image_iff.mpr]
  · simp
  · intro i _ j _ h
    have hc := sourceVertex_injective D h
    injection hc

/-- The generic forest extension and the two Hall matchings, specialized to
the surgery data used in Zhao's Lemma 7.10. -/
theorem zhao_lemma_7_10_of_surgeryData
    {T : SimpleGraph V} {G : SimpleGraph W}
    [DecidableRel T.Adj] [DecidableRel G.Adj]
    (U₁ U₂ : Finset V) (X Y Y₁ Y₂ : Finset W)
    (l k : ℕ) (z : V) (a : W)
    (D : SurgeryData T U₁ U₂ z l k)
    (hk : k = #Y₂)
    (hG : G.IsBipartiteWith (X : Set W) (Y : Set W))
    (hYsplit : Y₁ ∪ Y₂ = Y) (hYdisj : Disjoint Y₁ Y₂)
    (hX : #U₁ ≤ #X) (hY : #U₂ ≤ #Y)
    (hXY₁dense : ∀ x ∈ X, #Y₁ - l ≤ #((G.neighborFinset x) ∩ Y₁))
    (hY₁Xdense : ∀ y ∈ Y₁, #X - l ≤ #((G.neighborFinset y) ∩ X))
    (P : CenteredTwoPathSystem G X Y₂)
    (ha : a ∈ X) (haAvoid : a ∉ P.endpoints) :
    ∃ F : T.Copy G, F z = a ∧
      (∀ x ∈ U₁, F x ∈ X) ∧ (∀ x ∈ U₂, F x ∈ Y) := by
  classical
  let c := forestColoring D
  let S := sourceSet D
  let e : Fin k ≃ Y₂ := finEquivY₂ hk
  let p : S → W := premap D P e a
  let Q : Fin 2 → Finset W := fun i => if i = 0 then X else Y₁
  have hQ₀ : Q 0 = X := by simp [Q]
  have hQ₁ : Q 1 = Y₁ := by simp [Q]
  have hY₁sub : Y₁ ⊆ Y := by
    intro y hy
    rw [← hYsplit]
    exact Finset.mem_union_left Y₂ hy
  have hY₂sub : Y₂ ⊆ Y := by
    intro y hy
    rw [← hYsplit]
    exact Finset.mem_union_right Y₁ hy
  have hXY₁ : Disjoint X Y₁ := by
    rw [Finset.disjoint_left]
    intro x hxX hxY₁
    exact Set.disjoint_left.mp hG.disjoint hxX (hY₁sub hxY₁)
  have hXY₂ : Disjoint X Y₂ := by
    rw [Finset.disjoint_left]
    intro x hxX hxY₂
    exact Set.disjoint_left.mp hG.disjoint hxX (hY₂sub hxY₂)
  have hQdisj : Set.PairwiseDisjoint Set.univ Q := by
    intro i _ j _ hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · change Disjoint (Q 0) (Q 1)
      simpa [Q] using hXY₁
    · change Disjoint (Q 1) (Q 0)
      simpa [Q] using hXY₁.symm
    · exact (hij rfl).elim
  have hpInj : Function.Injective p := by
    exact premap_injective D P e a hG hY₂sub ha haAvoid
  have hpAdj : ∀ x y : S, D.forest.Adj x y → G.Adj (p x) (p y) := by
    exact premap_map_adj D P e a
  have hpCore : ∀ (y : S) (i : Fin 2), p y ∈ Q i → c y.1 = i := by
    exact premap_core_color D P e a c
      (fun x => forestColoring_eq_zero_iff D x) ha Y₁ hXY₂ hXY₁ hYdisj
      Q hQ₀ hQ₁
  have hfixedCore : ∀ x, x ∉ S → ∀ y : S,
      D.forest.Adj x y → p y ∈ Q (c y) := by
    exact premap_fixed_neighbor_core D P e a c
      (fun x => forestColoring_eq_zero_iff D x) ha Q hQ₀
  have hdefXY₁ : ∀ x ∈ X, #(Y₁.filter fun y => ¬G.Adj x y) ≤ l := by
    intro x hx
    exact defect_le_of_dense_inter G Y₁ x l (hXY₁dense x hx)
  have hdefY₁X : ∀ y ∈ Y₁, #(X.filter fun x => ¬G.Adj y x) ≤ l := by
    intro y hy
    have h := defect_le_of_dense_inter G X y l (hY₁Xdense y hy)
    simpa [G.adj_comm] using h
  have hmiss : ∀ i j, i ≠ j → ∀ b ∈ Q i,
      #((Q j).filter fun w => ¬G.Adj b w) ≤ l := by
    intro i j hij b hb
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · simpa [Q] using hdefXY₁ b (by simpa [Q] using hb)
    · simpa [Q, G.adj_comm] using hdefY₁X b (by simpa [Q] using hb)
    · exact (hij rfl).elim
  let D₀ := coreDemand c S p 0 X
  let D₁ := coreDemand c S p 1 Y₁
  have h4U₁ : 4 * l ≤ #U₁ := by
    rw [← D.card_deletedQ]
    exact Finset.card_le_card D.deletedQ_subset
  have h4U₂ : 4 * l ≤ #U₂ := by
    rw [← D.card_deletedP]
    exact Finset.card_le_card D.deletedP_subset
  have hD₀sub : D₀ ⊆ Finset.univ.filter fun x => c x = 0 := by
    intro x hx
    have hx' := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx'.2.1⟩
  have hcap₀ : #D₀ + 4 * l ≤ #X := by
    have hcD := Finset.card_le_card hD₀sub
    have hpart := partCard_forestColoring_zero D
    change #(Finset.univ.filter fun x => c x = 0) = #U₁ - 4 * l at hpart
    omega
  let C := exceptionalCenters D
  have hCsub : C ⊆ Finset.univ.filter fun x => c x = 1 := by
    intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (forestColoring_eq_one_iff D _).2 (D.p_center_mem _)⟩
  have hD₁sub : D₁ ⊆ Finset.univ.filter fun x => c x = 1 := by
    intro x hx
    have hx' := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx'.2.1⟩
  have hD₁C : Disjoint D₁ C := by
    rw [Finset.disjoint_left]
    intro x hxD hxC
    obtain ⟨i, -, hxi⟩ := Finset.mem_image.mp hxC
    subst x
    have hxD' := Finset.mem_filter.mp hxD
    have hpY₁ : p ⟨sourceVertex D (center i),
        sourceVertex_mem_sourceSet D (center i)⟩ ∈ Y₁ :=
      hxD'.2.2 (sourceVertex_mem_sourceSet D (center i))
    have hpY₂ : p ⟨sourceVertex D (center i),
        sourceVertex_mem_sourceSet D (center i)⟩ ∈ Y₂ := by
      change premap D P e a
        ⟨sourceVertex D (center i), sourceVertex_mem_sourceSet D (center i)⟩ ∈ Y₂
      rw [premap_sourceVertex]
      exact (e i).property
    exact Finset.disjoint_left.mp hYdisj hpY₁ hpY₂
  have hD₁Csub : D₁ ∪ C ⊆ Finset.univ.filter fun x => c x = 1 :=
    Finset.union_subset hD₁sub hCsub
  have hD₁plus : #D₁ + k ≤ #U₂ - 4 * l := by
    have hu := Finset.card_le_card hD₁Csub
    rw [Finset.card_union_of_disjoint hD₁C, card_exceptionalCenters D] at hu
    have hpart := partCard_forestColoring_one D
    change #(Finset.univ.filter fun x => c x = 1) = #U₂ - 4 * l at hpart
    omega
  have hYcard : #Y = #Y₁ + k := by
    have hu : #(Y₁ ∪ Y₂) = #Y₁ + #Y₂ :=
      Finset.card_union_of_disjoint hYdisj
    rw [hYsplit, ← hk] at hu
    exact hu
  have hcap₁ : #D₁ + 4 * l ≤ #Y₁ := by
    omega
  have hcapacity : ∀ i,
      #(coreDemand c S p i (Q i)) + 4 * l ≤ #(Q i) := by
    intro i
    fin_cases i
    · simpa [D₀, Q] using hcap₀
    · simpa [D₁, Q] using hcap₁
  obtain ⟨f, hfixed, hout⟩ := fixed_forest_embedding
    D.forest G D.forest_isAcyclic c S p Q l hpInj hpAdj hQdisj hpCore
      (forest_sourceSet_boundary_sparse D) hfixedCore hmiss hcapacity
  have houtQ : ∀ x, x ∉ S → f x ∈ Q (c x) := hout
  have hfU₁ : ∀ x : {v : V // v ∉ D.deleted}, x.1 ∈ U₁ → f x ∈ X := by
    intro x hx
    by_cases hxS : x ∈ S
    · rw [hfixed ⟨x, hxS⟩]
      exact premap_mem_X_of_source_mem_U₁ D P e a ha ⟨x, hxS⟩ hx
    · have hc0 : c x = 0 := (forestColoring_eq_zero_iff D x).2 hx
      simpa [Q, hc0] using houtQ x hxS
  have hfU₂ : ∀ x : {v : V // v ∉ D.deleted}, x.1 ∈ U₂ → f x ∈ Y := by
    intro x hx
    by_cases hxS : x ∈ S
    · rw [hfixed ⟨x, hxS⟩]
      exact hY₂sub (premap_mem_Y₂_of_source_mem_U₂ D P e a ⟨x, hxS⟩ hx)
    · have hc1 : c x = 1 := (forestColoring_eq_one_iff D x).2 hx
      exact hY₁sub (by simpa [Q, hc1] using houtQ x hxS)
  have hfQL : ∀ i, f (Erdos547b.ZhaoReinsertDeletedAlt.qLeftVertex D i) ∈ Y₁ := by
    intro i
    let qv := Erdos547b.ZhaoReinsertDeletedAlt.qLeftVertex D i
    have heq : qv = ExceptionalIndex.qLeftVertex D i := Subtype.ext rfl
    have hn : qv ∉ S := by
      rw [heq]
      exact qLeftVertex_not_mem_sourceSet D i
    have hc : c qv = 1 :=
      (forestColoring_eq_one_iff D _).2 (D.q_left_mem i)
    simpa [qv, Q, hc] using houtQ qv hn
  have hfQR : ∀ i, f (Erdos547b.ZhaoReinsertDeletedAlt.qRightVertex D i) ∈ Y₁ := by
    intro i
    let qv := Erdos547b.ZhaoReinsertDeletedAlt.qRightVertex D i
    have heq : qv = ExceptionalIndex.qRightVertex D i := Subtype.ext rfl
    have hn : qv ∉ S := by
      rw [heq]
      exact qRightVertex_not_mem_sourceSet D i
    have hc : c qv = 1 :=
      (forestColoring_eq_one_iff D _).2 (D.q_right_mem i)
    simpa [qv, Q, hc] using houtQ qv hn
  have hpCore' : ∀ (y : S) (j : Fin 2), p y ∈ Q j → c y = j := hpCore
  have hfree : ∀ i, 4 * l ≤ #((Q i) \ usedVertices f) := by
    intro i
    apply four_mul_le_card_part_sdiff_used_of_coreDemand c S p Q l i f
      hQdisj hpCore' hfixed
    · intro x hxS
      exact houtQ x hxS
    · exact hcapacity i
  obtain ⟨F, hFforest, hFU₁, hFU₂⟩ :=
    Erdos547b.ZhaoReinsertFinish2.reinsert_deleted_centers
      D X Y Y₁ f hfU₁ hfU₂ hfQL hfQR hY₁sub hXY₁
        (by simpa [Q] using hfree 0) (by simpa [Q] using hfree 1)
        hXY₁dense hY₁Xdense
  refine ⟨F, ?_, hFU₁, hFU₂⟩
  let rz := sourceVertex D root
  have hrz : (rz : V) = z := rfl
  calc
    F z = F rz := by rw [hrz]
    _ = f rz := hFforest rz
    _ = p ⟨rz, sourceVertex_mem_sourceSet D root⟩ :=
      hfixed ⟨rz, sourceVertex_mem_sourceSet D root⟩
    _ = a := premap_root D P e a

/-- Zhao's Lemma 7.10, including the degenerate subsingleton target branch. -/
theorem zhao_lemma_7_10
    {T : SimpleGraph V} {G : SimpleGraph W}
    [DecidableRel T.Adj] [DecidableRel G.Adj]
    (U₁ U₂ : Finset V) (X Y Y₁ Y₂ : Finset W)
    (l : ℕ) (z : V) (a : W)
    (hT : T.IsTree)
    (hTU : T.IsBipartiteWith (U₁ : Set V) (U₂ : Set V))
    (hTUcover : U₁ ∪ U₂ = Finset.univ)
    (hz : z ∈ U₁)
    (hleaves : #(Erdos547EC2.leafVertices T) ≤ l)
    (hU₁ : 26 * l ≤ #U₁) (hU₂ : 26 * l ≤ #U₂)
    (hG : G.IsBipartiteWith (X : Set W) (Y : Set W))
    (hYsplit : Y₁ ∪ Y₂ = Y) (hYdisj : Disjoint Y₁ Y₂)
    (hX : #U₁ ≤ #X) (hY : #U₂ ≤ #Y)
    (hXY₁ : ∀ x ∈ X, #Y₁ - l ≤ #((G.neighborFinset x) ∩ Y₁))
    (hY₁X : ∀ y ∈ Y₁, #X - l ≤ #((G.neighborFinset y) ∩ X))
    (hY₂ : #Y₂ ≤ l)
    (P : CenteredTwoPathSystem G X Y₂)
    (ha : a ∈ X) (haAvoid : a ∉ P.endpoints) :
    ∃ f : T.Copy G, f z = a ∧
      (∀ v ∈ U₁, f v ∈ X) ∧ (∀ v ∈ U₂, f v ∈ Y) := by
  classical
  by_cases hsub : Subsingleton V
  · exact zhao_lemma_7_10_of_subsingleton T G U₁ U₂ X Y z a
      hsub hTU hz ha
  · let : Nontrivial V := not_subsingleton_iff_nontrivial.mp hsub
    let W₃ := Classical.choice
      (Erdos547b.ZhaoLemma710Alt.zhao_proposition_7_11_part_three
        T U₁ U₂ z l hT hTU hTUcover hz hleaves hU₁ hU₂)
    let D := Classical.choice
      (surgeryData_of_proposition711Part3Witness
        T U₁ U₂ z l (#Y₂) hT hTU hTUcover hz W₃ hY₂)
    exact zhao_lemma_7_10_of_surgeryData U₁ U₂ X Y Y₁ Y₂ l (#Y₂)
      z a D rfl hG hYsplit hYdisj hX hY hXY₁ hY₁X P ha haAvoid

end Erdos547b.ZhaoLemma710ApplicationAlt

#print axioms Erdos547b.ZhaoLemma710ApplicationAlt.zhao_lemma_7_10_of_surgeryData
#print axioms Erdos547b.ZhaoLemma710ApplicationAlt.zhao_lemma_7_10
