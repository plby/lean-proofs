/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import ErdosProblems.Erdos547b.Partite
import Mathlib.Combinatorics.Hall.Basic

/-!
# Zhao's few-leaf counting lemma (Proposition 7.11(1--2))

This is the assumption-free counting engine used in the proof of Zhao's
Lemma 7.10.  For a finite nontrivial tree, the total excess above degree two
is exactly the number of leaves minus two.  Consequently, the union of the
neighborhoods of any vertex set `S` has size at most
`2 * #S + numberOfLeaves - 2`.
-/

open scoped SimpleGraph

namespace Erdos547b.ZhaoLemma710

open Finset SimpleGraph

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The degree-one vertices of a finite graph. -/
def leafVertices (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  Finset.univ.filter fun v => G.degree v = 1

/-- The vertices of degree at least three. -/
def branchVertices (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  Finset.univ.filter fun v => 3 ≤ G.degree v

/-- The sum of `degree - 2` over the branch vertices. -/
def branchExcess (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  ∑ v ∈ branchVertices G, (G.degree v - 2)

/-- The open neighborhood of a finite set, written as a finite union. -/
def openNeighborhood (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) : Finset V :=
  S.biUnion fun v => G.neighborFinset v

private theorem sum_indicator_leaf_eq_card
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∑ v : V, if G.degree v = 1 then 1 else 0) = #(leafVertices G) := by
  classical
  simp [leafVertices]

private theorem sum_indicator_branchExcess_eq
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∑ v : V, if 3 ≤ G.degree v then G.degree v - 2 else 0) = branchExcess G := by
  classical
  rw [branchExcess, branchVertices]
  exact (Finset.sum_filter _ _).symm

/-- Zhao, Proposition 7.11(1), in subtraction-free natural-number form.
The total excess over degree two plus two is the number of leaves. -/
theorem branchExcess_add_two_eq_card_leaves
    (G : SimpleGraph V) [DecidableRel G.Adj] [Nontrivial V]
    (hG : G.IsTree) :
    branchExcess G + 2 = #(leafVertices G) := by
  classical
  have hpos : ∀ v : V, 0 < G.degree v := fun v =>
    hG.preconnected.degree_pos_of_nontrivial v
  have hpoint : ∀ v : V,
      G.degree v + (if G.degree v = 1 then 1 else 0) =
        2 + (if 3 ≤ G.degree v then G.degree v - 2 else 0) := by
    intro v
    specialize hpos v
    split_ifs <;> omega
  have hsum :
      (∑ v : V, (G.degree v + (if G.degree v = 1 then 1 else 0))) =
        ∑ v : V, (2 + (if 3 ≤ G.degree v then G.degree v - 2 else 0)) :=
    Finset.sum_congr rfl (fun v _ => hpoint v)
  have hdegree : (∑ v : V, G.degree v) + 2 = 2 * Fintype.card V := by
    rw [G.sum_degrees_eq_twice_card_edges]
    have hedge := hG.card_edgeFinset
    omega
  have hsum' :
      (∑ v : V, G.degree v) + #(leafVertices G) =
        2 * Fintype.card V + branchExcess G := by
    calc
      (∑ v : V, G.degree v) + #(leafVertices G) =
          (∑ v : V, G.degree v) +
            (∑ v : V, if G.degree v = 1 then 1 else 0) := by
              rw [sum_indicator_leaf_eq_card]
      _ = ∑ v : V, (G.degree v + (if G.degree v = 1 then 1 else 0)) :=
        Finset.sum_add_distrib.symm
      _ = ∑ v : V, (2 + (if 3 ≤ G.degree v then G.degree v - 2 else 0)) := hsum
      _ = (∑ _v : V, 2) +
          (∑ v : V, if 3 ≤ G.degree v then G.degree v - 2 else 0) :=
        Finset.sum_add_distrib
      _ = 2 * Fintype.card V + branchExcess G := by
        rw [sum_indicator_branchExcess_eq]
        simp [mul_comm]
  omega

/-- A finite nontrivial tree has at least two leaves. -/
theorem two_le_card_leafVertices
    (G : SimpleGraph V) [DecidableRel G.Adj] [Nontrivial V]
    (hG : G.IsTree) :
    2 ≤ #(leafVertices G) := by
  rw [← branchExcess_add_two_eq_card_leaves G hG]
  omega

/-- Zhao's integer-looking identity, rendered with truncated subtraction only
after proving the requisite lower bound on the number of leaves. -/
theorem branchExcess_eq_card_leaves_sub_two
    (G : SimpleGraph V) [DecidableRel G.Adj] [Nontrivial V]
    (hG : G.IsTree) :
    branchExcess G = #(leafVertices G) - 2 := by
  rw [← branchExcess_add_two_eq_card_leaves G hG]
  omega

/-- The number of vertices of degree at least three is at most the number of
leaves minus two, the second assertion in Zhao's Proposition 7.11(1). -/
theorem card_branchVertices_le_card_leaves_sub_two
    (G : SimpleGraph V) [DecidableRel G.Adj] [Nontrivial V]
    (hG : G.IsTree) :
    #(branchVertices G) ≤ #(leafVertices G) - 2 := by
  rw [← branchExcess_eq_card_leaves_sub_two G hG]
  calc
    #(branchVertices G) = ∑ _v ∈ branchVertices G, 1 := by simp
    _ ≤ ∑ v ∈ branchVertices G, (G.degree v - 2) :=
      Finset.sum_le_sum fun v hv => by
        have hv' : 3 ≤ G.degree v := (Finset.mem_filter.mp hv).2
        omega
    _ = branchExcess G := rfl

private theorem card_openNeighborhood_le_sum_degrees
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    #(openNeighborhood G S) ≤ ∑ v ∈ S, G.degree v := by
  unfold openNeighborhood
  simpa only [G.card_neighborFinset_eq_degree] using
    (Finset.card_biUnion_le (s := S) (t := fun v => G.neighborFinset v))

private theorem sum_degree_sub_two_eq_branchExcess
    (G : SimpleGraph V) [DecidableRel G.Adj] [Nontrivial V]
    (hG : G.IsTree) :
    (∑ v : V, (G.degree v - 2)) = branchExcess G := by
  classical
  calc
    (∑ v : V, (G.degree v - 2)) =
        ∑ v : V, (if 3 ≤ G.degree v then G.degree v - 2 else 0) := by
      apply Finset.sum_congr rfl
      intro v _
      have hvpos := hG.preconnected.degree_pos_of_nontrivial v
      split_ifs <;> omega
    _ = branchExcess G := sum_indicator_branchExcess_eq G

/-- Zhao, Proposition 7.11(2), in a subtraction-free form.  This form is
often more convenient for later cardinal arithmetic. -/
theorem card_openNeighborhood_add_two_le
    (G : SimpleGraph V) [DecidableRel G.Adj] [Nontrivial V]
    (hG : G.IsTree) (S : Finset V) :
    #(openNeighborhood G S) + 2 ≤ 2 * #S + #(leafVertices G) := by
  have hN := card_openNeighborhood_le_sum_degrees G S
  have hpoint : ∀ v ∈ S, G.degree v ≤ 2 + (G.degree v - 2) := by
    intro v _
    omega
  have hsum : (∑ v ∈ S, G.degree v) ≤
      2 * #S + ∑ v ∈ S, (G.degree v - 2) := by
    calc
      (∑ v ∈ S, G.degree v) ≤ ∑ v ∈ S, (2 + (G.degree v - 2)) :=
        Finset.sum_le_sum fun v hv => hpoint v hv
      _ = 2 * #S + ∑ v ∈ S, (G.degree v - 2) := by
        simp [Finset.sum_add_distrib, mul_comm]
  have hsubsum : (∑ v ∈ S, (G.degree v - 2)) ≤ branchExcess G := by
    rw [← sum_degree_sub_two_eq_branchExcess G hG]
    exact Finset.sum_le_sum_of_subset (Finset.subset_univ S)
  have hexcess := branchExcess_add_two_eq_card_leaves G hG
  omega

/-- Zhao's displayed neighborhood estimate
`|N(S)| ≤ 2|S| + numberOfLeaves - 2`. -/
theorem card_openNeighborhood_le
    (G : SimpleGraph V) [DecidableRel G.Adj] [Nontrivial V]
    (hG : G.IsTree) (S : Finset V) :
    #(openNeighborhood G S) ≤ 2 * #S + #(leafVertices G) - 2 := by
  have h := card_openNeighborhood_add_two_le G hG S
  omega

/-! ## The balanced Hall step used twice at the end of Lemma 7.10 -/

/-- A bipartite graph with equal finite sides and minimum degree at least half
the opposite side has a perfect matching.  This is the exact Hall argument
used twice in the final paragraph of Zhao's proof of Lemma 7.10 (there both
sides have size `4*l` and every degree is at least `2*l`). -/
theorem exists_bijective_matching_of_twice_card_le_degree
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) (hcard : #A = #B)
    (hA : ∀ a : A,
      #A ≤ 2 * #{b : B | G.Adj (a : V) (b : V)})
    (hB : ∀ b : B,
      #B ≤ 2 * #{a : A | G.Adj (a : V) (b : V)}) :
    ∃ f : A → B, Function.Bijective f ∧
      ∀ a : A, G.Adj (a : V) (f a : V) := by
  classical
  let N : A → Finset B := fun a =>
    Finset.univ.filter fun b => G.Adj (a : V) (b : V)
  have hHall : ∀ S : Finset A, #S ≤ #(S.biUnion N) := by
    intro S
    by_cases hSempty : S = ∅
    · simp [hSempty]
    by_cases hsmall : 2 * #S ≤ #A
    · obtain ⟨a, haS⟩ := Finset.nonempty_iff_ne_empty.mpr hSempty
      have hsub : N a ⊆ S.biUnion N := fun b hb =>
        Finset.mem_biUnion.mpr ⟨a, haS, hb⟩
      have hdeg := hA a
      have hNcard : #(N a) = #{b : B | G.Adj (a : V) (b : V)} := by
        rfl
      have := Finset.card_le_card hsub
      rw [hNcard] at this
      omega
    · have hlarge : #A < 2 * #S := Nat.lt_of_not_ge hsmall
      have hScard : #S ≤ #A := by
        simpa using (Finset.card_le_univ S)
      have hfull : S.biUnion N = Finset.univ := by
        apply Finset.eq_univ_of_forall
        intro b
        by_contra hb
        let M : Finset A :=
          Finset.univ.filter fun a => G.Adj (a : V) (b : V)
        have hMsub : M ⊆ Finset.univ \ S := by
          intro a haM
          rw [Finset.mem_sdiff]
          refine ⟨Finset.mem_univ _, ?_⟩
          intro haS
          apply hb
          apply Finset.mem_biUnion.mpr
          refine ⟨a, haS, ?_⟩
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
            (Finset.mem_filter.mp haM).2⟩
        have hMcard : #M ≤ #A - #S := by
          have := Finset.card_le_card hMsub
          rw [Finset.card_sdiff_of_subset (Finset.subset_univ S)] at this
          simpa using this
        have hdeg := hB b
        have hMdef : #M = #{a : A | G.Adj (a : V) (b : V)} := by
          rfl
        rw [← hcard, ← hMdef] at hdeg
        omega
      rw [hfull]
      simp only [Finset.card_univ]
      have hSuniv : #S ≤ Fintype.card A := Finset.card_le_univ S
      calc
        #S ≤ #A := by simpa using hSuniv
        _ = #B := hcard
        _ = Fintype.card B := by simp
  obtain ⟨f, hfinj, hfmem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_exists_injective N).mp hHall
  refine ⟨f, ?_, ?_⟩
  · apply (Fintype.bijective_iff_injective_and_card f).mpr
    refine ⟨hfinj, ?_⟩
    simpa using hcard
  · intro a
    exact (Finset.mem_filter.mp (hfmem a)).2

/-! ## Bundled systems of disjoint host two-paths -/

/-- The path system appearing in hypothesis (3) of Zhao's Lemma 7.10.

The index is the actual midpoint in `Y₂`.  Thus the structure contains
exactly `#Y₂` paths without separately carrying a bijection between an
abstract index type and `Y₂`.  `endpointInjective` says that all `2 * #Y₂`
endpoints are different; when `X` and `Y₂` are disjoint this is precisely the
vertex-disjointness of the paths. -/
structure CenteredTwoPathSystem {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) (X Y₂ : Finset W) where
  left : Y₂ → W
  right : Y₂ → W
  left_mem : ∀ y, left y ∈ X
  right_mem : ∀ y, right y ∈ X
  left_ne_right : ∀ y, left y ≠ right y
  adj_left : ∀ y : Y₂, G.Adj (left y) y
  adj_right : ∀ y : Y₂, G.Adj y (right y)
  endpointInjective : Function.Injective fun p : Y₂ × Fin 2 =>
    if p.2 = 0 then left p.1 else right p.1

namespace CenteredTwoPathSystem

variable {W : Type*} [Fintype W] [DecidableEq W]
variable {G : SimpleGraph W} {X Y₂ : Finset W}

/-- The finite set of all endpoints used by a path system. -/
def endpoints (P : CenteredTwoPathSystem G X Y₂) : Finset W :=
  Finset.univ.image fun p : Y₂ × Fin 2 =>
    if p.2 = 0 then P.left p.1 else P.right p.1

theorem card_endpoints (P : CenteredTwoPathSystem G X Y₂) :
    #P.endpoints = 2 * #Y₂ := by
  classical
  rw [endpoints, Finset.card_image_iff.mpr fun _ _ _ _ h =>
    P.endpointInjective h]
  simp [mul_comm]

theorem endpoints_subset (P : CenteredTwoPathSystem G X Y₂) :
    P.endpoints ⊆ X := by
  classical
  intro w hw
  obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp hw
  by_cases hp : p.2 = 0
  · simpa [hp] using P.left_mem p.1
  · simpa [hp] using P.right_mem p.1

@[simp] theorem left_mem_endpoints (P : CenteredTwoPathSystem G X Y₂)
    (y : Y₂) : P.left y ∈ P.endpoints := by
  classical
  apply Finset.mem_image.mpr
  exact ⟨(y, 0), Finset.mem_univ _, by simp⟩

@[simp] theorem right_mem_endpoints (P : CenteredTwoPathSystem G X Y₂)
    (y : Y₂) : P.right y ∈ P.endpoints := by
  classical
  apply Finset.mem_image.mpr
  exact ⟨(y, 1), Finset.mem_univ _, by simp⟩

theorem left_injective (P : CenteredTwoPathSystem G X Y₂) :
    Function.Injective P.left := by
  intro y y' h
  have hp := P.endpointInjective (a₁ := (y, 0)) (a₂ := (y', 0)) (by simpa using h)
  exact congrArg Prod.fst hp

theorem right_injective (P : CenteredTwoPathSystem G X Y₂) :
    Function.Injective P.right := by
  intro y y' h
  have hp := P.endpointInjective (a₁ := (y, 1)) (a₂ := (y', 1)) (by simpa using h)
  exact congrArg Prod.fst hp

theorem left_ne_right' (P : CenteredTwoPathSystem G X Y₂)
    (y y' : Y₂) : P.left y ≠ P.right y' := by
  intro h
  have hp := P.endpointInjective (a₁ := (y, 0)) (a₂ := (y', 1)) (by simpa using h)
  have := congrArg (fun q : Y₂ × Fin 2 => q.2) hp
  simp at this

end CenteredTwoPathSystem

/-! ## Gluing back a set of degree-two vertices -/

/-- If an independent set `M` has been deleted from a graph and the induced
graph on its complement has already been embedded, then a bijective assignment
of `M` to unused host vertices which respects all attachment edges completes
the embedding.  This is the exact gluing operation after each of the two Hall
matchings in Zhao's proof. -/
theorem copy_of_induce_compl_and_bijective_attachment
    {A W : Type*} [Fintype A] [DecidableEq A]
    [Fintype W] [DecidableEq W]
    (T : SimpleGraph A) (G : SimpleGraph W)
    (M : Finset A) (B : Finset W)
    (hM : T.IsIndepSet (M : Set A))
    (f : (T.induce {v : A | v ∉ M}).Copy G)
    (hfB : ∀ v, f v ∉ B)
    (q : M → B) (hq : Function.Bijective q)
    (hattach : ∀ (m : M) (v : {v : A // v ∉ M}),
      T.Adj (m : A) (v : A) → G.Adj (q m : W) (f v)) :
    ∃ F : T.Copy G,
      (∀ m : M, F m = (q m : W)) ∧
      (∀ v : {v : A // v ∉ M}, F v = f v) := by
  classical
  let F : A → W := fun v =>
    if hv : v ∈ M then (q ⟨v, hv⟩ : W)
    else f ⟨v, by simpa using hv⟩
  have hFmap : ∀ ⦃u v⦄, T.Adj u v → G.Adj (F u) (F v) := by
    intro u v huv
    by_cases hu : u ∈ M
    · by_cases hv : v ∈ M
      · exact False.elim ((hM hu hv huv.ne) huv)
      · have ha := hattach ⟨u, hu⟩ ⟨v, by simpa using hv⟩ huv
        simpa [F, hu, hv] using ha
    · by_cases hv : v ∈ M
      · have ha := hattach ⟨v, hv⟩ ⟨u, by simpa using hu⟩ huv.symm
        simpa [F, hu, hv] using ha.symm
      · have hi : (T.induce (M : Set A)ᶜ).Adj
            ⟨u, by simpa using hu⟩ ⟨v, by simpa using hv⟩ := by
          simpa using huv
        have ha := f.toHom.map_rel hi
        simpa [F, hu, hv] using ha
  have hFinj : Function.Injective F := by
    intro u v huv
    by_cases hu : u ∈ M
    · by_cases hv : v ∈ M
      · have hqv : q ⟨u, hu⟩ = q ⟨v, hv⟩ := by
          apply Subtype.ext
          simpa [F, hu, hv] using huv
        exact congrArg Subtype.val (hq.injective hqv)
      · exfalso
        have hqB : (q ⟨u, hu⟩ : W) ∈ B := (q ⟨u, hu⟩).property
        have hfnot : f ⟨v, by simpa using hv⟩ ∉ B := hfB _
        apply hfnot
        have heq : (q ⟨u, hu⟩ : W) = f ⟨v, by simpa using hv⟩ := by
          simpa [F, hu, hv] using huv
        rw [← heq]
        exact hqB
    · by_cases hv : v ∈ M
      · exfalso
        have hqB : (q ⟨v, hv⟩ : W) ∈ B := (q ⟨v, hv⟩).property
        have hfnot : f ⟨u, by simpa using hu⟩ ∉ B := hfB _
        apply hfnot
        have heq : f ⟨u, by simpa using hu⟩ = (q ⟨v, hv⟩ : W) := by
          simpa [F, hu, hv] using huv
        rw [heq]
        exact hqB
      · have hsub : (⟨u, by simpa using hu⟩ : {v : A // v ∉ M}) =
            ⟨v, by simpa using hv⟩ := by
          apply f.injective
          simpa [F, hu, hv] using huv
        exact Subtype.ext_iff.mp hsub
  let e : T.Copy G := ⟨⟨F, fun {_ _} h => hFmap h⟩, hFinj⟩
  refine ⟨e, ?_, ?_⟩
  · intro m
    simp [e, F, m.property]
  · intro v
    simp [e, F, v.property]

#print axioms Erdos547b.ZhaoLemma710.branchExcess_add_two_eq_card_leaves
#print axioms Erdos547b.ZhaoLemma710.card_openNeighborhood_le
#print axioms Erdos547b.ZhaoLemma710.exists_bijective_matching_of_twice_card_le_degree

end Erdos547b.ZhaoLemma710
