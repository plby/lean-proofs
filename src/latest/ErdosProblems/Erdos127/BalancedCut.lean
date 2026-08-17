import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic

open scoped Sym2
open Finset

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The edges of `G` crossing the vertex cut given by `S`. -/
def cutEdgeFinset (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    Finset (Sym2 V) :=
  G.edgeFinset.filter fun e ↦
    e ∈ Sym2.fromRel (r := fun u v : V ↦ (u ∈ S) ≠ (v ∈ S)) ⟨fun _ _ ↦ ne_comm.mp⟩

@[simp] lemma mem_cutEdgeFinset_mk (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (u v : V) :
    s(u, v) ∈ G.cutEdgeFinset S ↔ G.Adj u v ∧ ((u ∈ S) ≠ (v ∈ S)) := by
  simp [cutEdgeFinset]

lemma edgeFinset_between_compl_eq_cutEdgeFinset (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) :
    (G.between (S : Set V) (S : Set V)ᶜ).edgeFinset = G.cutEdgeFinset S := by
  ext e
  induction e using Sym2.inductionOn with
  | _ u v =>
      simp only [mem_edgeFinset, mem_edgeSet, between_adj, mem_coe, Set.mem_compl_iff,
        mem_cutEdgeFinset_mk]
      tauto

lemma between_compl_isBipartite (G : SimpleGraph V) (S : Finset V) :
    (G.between (S : Set V) (S : Set V)ᶜ).IsBipartite :=
  G.between_isBipartite disjoint_compl_right

private def colorCrosses {q : ℕ} (c : V → Fin q) (A : Finset (Fin q))
    (e : Sym2 V) : Prop :=
  e ∈ Sym2.fromRel (r := fun u v : V ↦ (c u ∈ A) ≠ (c v ∈ A))
    ⟨fun _ _ ↦ ne_comm.mp⟩

@[simp] private lemma colorCrosses_mk {q : ℕ} (c : V → Fin q)
    (A : Finset (Fin q)) (u v : V) :
    colorCrosses c A s(u, v) ↔ ((c u ∈ A) ≠ (c v ∈ A)) := by
  simp [colorCrosses]

private instance colorCrosses_decidablePred {q : ℕ} (c : V → Fin q)
    (A : Finset (Fin q)) : DecidablePred (colorCrosses c A) := fun e ↦ by
  unfold colorCrosses
  infer_instance

private lemma card_powersetCard_filter_mem_notMem {q k : ℕ} (hk : 1 ≤ k)
    {a b : Fin q} (hab : a ≠ b) :
    #((Finset.univ.powersetCard k).filter fun A : Finset (Fin q) ↦ a ∈ A ∧ b ∉ A) =
      (q - 2).choose (k - 1) := by
  have hab' : a ∈ (Finset.univ.erase b : Finset (Fin q)) := by simp [hab]
  have hsingle : ({a} : Finset (Fin q)) ⊆ Finset.univ.erase b := by simpa
  have hcard_single : #({a} : Finset (Fin q)) ≤ k := by simpa using hk
  have heq :
      ((Finset.univ.powersetCard k).filter fun A : Finset (Fin q) ↦ a ∈ A ∧ b ∉ A) =
        (((Finset.univ.erase b).powersetCard k).filter fun A ↦ ({a} : Finset (Fin q)) ⊆ A) := by
    ext A
    simp only [mem_filter, mem_powersetCard, subset_univ, true_and, singleton_subset_iff]
    constructor
    · rintro ⟨hcard, ha, hb⟩
      refine ⟨⟨?_, hcard⟩, ha⟩
      intro x hx
      simp only [mem_erase, mem_univ, and_true]
      rintro rfl
      exact hb hx
    · rintro ⟨⟨hsub, hcard⟩, ha⟩
      refine ⟨hcard, ha, ?_⟩
      intro hb
      have := hsub hb
      simpa using this
  rw [heq, Finset.card_filter_powersetCard_subset _ _ _ hsingle hcard_single]
  simp [Nat.sub_sub]

private lemma card_powersetCard_filter_separates {q k : ℕ} (hk : 1 ≤ k)
    {a b : Fin q} (hab : a ≠ b) :
    #((Finset.univ.powersetCard k).filter fun A : Finset (Fin q) ↦
        (a ∈ A) ≠ (b ∈ A)) = 2 * (q - 2).choose (k - 1) := by
  let L := (Finset.univ.powersetCard k).filter fun A : Finset (Fin q) ↦ a ∈ A ∧ b ∉ A
  let R := (Finset.univ.powersetCard k).filter fun A : Finset (Fin q) ↦ b ∈ A ∧ a ∉ A
  have hsep :
      ((Finset.univ.powersetCard k).filter fun A : Finset (Fin q) ↦
          (a ∈ A) ≠ (b ∈ A)) = L ∪ R := by
    ext A
    simp only [mem_filter, mem_powersetCard_univ, mem_union, L, R]
    tauto
  have hdisj : Disjoint L R := by
    simp only [Finset.disjoint_left, mem_filter, mem_powersetCard_univ, L, R]
    aesop
  rw [hsep, card_union_of_disjoint hdisj,
    card_powersetCard_filter_mem_notMem hk hab,
    card_powersetCard_filter_mem_notMem hk hab.symm]
  omega

private lemma sum_balanced_colorCuts {G : SimpleGraph V} [DecidableRel G.Adj]
    {q k : ℕ} (hk : 1 ≤ k) (c : G.Coloring (Fin q)) :
    ∑ A ∈ (Finset.univ.powersetCard k),
        #(G.edgeFinset.filter (colorCrosses c A)) =
      (2 * (q - 2).choose (k - 1)) * #G.edgeFinset := by
  classical
  calc
    ∑ A ∈ (Finset.univ.powersetCard k),
        #(G.edgeFinset.filter (colorCrosses c A)) =
        ∑ A ∈ (Finset.univ.powersetCard k), ∑ e ∈ G.edgeFinset,
          if colorCrosses c A e then 1 else 0 := by
            apply sum_congr rfl
            intro A hA
            exact (Finset.sum_boole (colorCrosses c A) G.edgeFinset).symm
    _ = ∑ e ∈ G.edgeFinset, ∑ A ∈ (Finset.univ.powersetCard k),
          if colorCrosses c A e then 1 else 0 := by
            rw [Finset.sum_comm]
    _ = ∑ e ∈ G.edgeFinset, (2 * (q - 2).choose (k - 1)) := by
          apply sum_congr rfl
          intro e he
          induction e using Sym2.inductionOn with
          | _ u v =>
              have huv : c u ≠ c v := c.valid (by simpa using he)
              rw [← card_filter]
              exact card_powersetCard_filter_separates hk huv
    _ = (2 * (q - 2).choose (k - 1)) * #G.edgeFinset := by simp [mul_comm]

private lemma central_choose_step (n : ℕ) (hn : 1 ≤ n) :
    (2 * n).choose n = 2 * (2 * n - 1).choose (n - 1) := by
  have hrec :
      (2 * n).choose n =
        (2 * n - 1).choose (n - 1) + (2 * n - 1).choose n := by
    have htop : 2 * n - 1 + 1 = 2 * n := by omega
    have hidx : n - 1 + 1 = n := by omega
    simpa only [htop, hidx] using Nat.choose_succ_succ' (2 * n - 1) (n - 1)
  have hsym : (2 * n - 1).choose (n - 1) = (2 * n - 1).choose n := by
    exact Nat.choose_symm_of_eq_add (by omega)
  omega

private lemma odd_middle_step_le (n : ℕ) (hn : 1 ≤ n) :
    (2 * n - 1).choose (n - 1) ≤ 2 * (2 * n - 2).choose (n - 1) := by
  by_cases hn1 : n = 1
  · subst n
    norm_num
  have hn2 : 2 ≤ n := by omega
  have hrec :
      (2 * n - 1).choose (n - 1) =
        (2 * n - 2).choose (n - 2) + (2 * n - 2).choose (n - 1) := by
    have htop : 2 * n - 2 + 1 = 2 * n - 1 := by omega
    have hidx : n - 2 + 1 = n - 1 := by omega
    simpa only [htop, hidx] using Nat.choose_succ_succ' (2 * n - 2) (n - 2)
  have hmono :
      (2 * n - 2).choose (n - 2) ≤ (2 * n - 2).choose (n - 1) := by
    have hlt : n - 2 < (2 * n - 2) / 2 := by omega
    have h := Nat.choose_le_succ_of_lt_half_left hlt
    simpa only [show n - 2 + 1 = n - 1 by omega] using h
  omega

private lemma balanced_choose_ineq {q : ℕ} (hq : 2 ≤ q) :
    (q + 1) * q.choose (q / 2) ≤
      2 * q * (2 * (q - 2).choose (q / 2 - 1)) := by
  rcases q.even_or_odd' with ⟨n, hqeven | hqodd⟩
  · subst q
    have hn : 1 ≤ n := by omega
    have hdiv : 2 * n / 2 = n := by omega
    rw [hdiv, central_choose_step n hn]
    have hratio := Nat.choose_mul_succ_eq (2 * n - 2) (n - 1)
    have hsub : 2 * n - 2 + 1 - (n - 1) = n := by omega
    have htop : 2 * n - 2 + 1 = 2 * n - 1 := by omega
    rw [hsub, htop] at hratio
    apply Nat.le_of_mul_le_mul_left ?_ hn
    calc
      n * ((2 * n + 1) * (2 * (2 * n - 1).choose (n - 1))) =
          2 * (2 * n + 1) * ((2 * n - 1).choose (n - 1) * n) := by ring
      _ = 2 * (2 * n + 1) * ((2 * n - 2).choose (n - 1) * (2 * n - 1)) := by
            rw [← hratio]
      _ ≤ n * (2 * (2 * n) * (2 * (2 * n - 2).choose (n - 1))) := by
            have hsquare :
                (2 * n + 1) * (2 * n - 1) ≤ (2 * n) * (2 * n) := by
              calc
                (2 * n + 1) * (2 * n - 1) =
                    ((2 * n - 1) + 2) * (2 * n - 1) := by congr 1 <;> omega
                _ ≤ ((2 * n - 1) + 1) * ((2 * n - 1) + 1) := by nlinarith
                _ = (2 * n) * (2 * n) := by congr 1 <;> omega
            have hpoly : 2 * (2 * n + 1) * (2 * n - 1) ≤ 8 * n * n := by
              have h := Nat.mul_le_mul_left 2 hsquare
              convert h using 1 <;> ring
            have hmul := Nat.mul_le_mul_right ((2 * n - 2).choose (n - 1)) hpoly
            convert hmul using 1 <;> ring
  · subst q
    have hn : 1 ≤ n := by omega
    have hdiv : (2 * n + 1) / 2 = n := by omega
    rw [hdiv]
    have hcentral := central_choose_step n hn
    have hratio := Nat.choose_mul_succ_eq (2 * n) n
    have hsub : 2 * n + 1 - n = n + 1 := by omega
    rw [hsub] at hratio
    calc
      (2 * n + 1 + 1) * (2 * n + 1).choose n =
          2 * ((2 * n + 1).choose n * (n + 1)) := by ring
      _ = 2 * ((2 * n).choose n * (2 * n + 1)) := by rw [← hratio]
      _ = 2 * ((2 * (2 * n - 1).choose (n - 1)) * (2 * n + 1)) := by
            rw [hcentral]
      _ ≤ 2 * (2 * n + 1) * (2 * (2 * n + 1 - 2).choose (n - 1)) := by
            apply Eq.le
            rw [show 2 * n + 1 - 2 = 2 * n - 1 by omega]
            ring

/-- A proper coloring by at least two colors has a vertex cut containing at least
`(q + 1) / (2q)` of all edges, stated without division.  Surjectivity is included
to match the usual formulation but is not needed for the estimate. -/
theorem exists_cutEdgeFinset_mul_bound {G : SimpleGraph V} [DecidableRel G.Adj]
    {q : ℕ} (hq : 2 ≤ q) (c : G.Coloring (Fin q))
    (_hc : Function.Surjective c) :
    ∃ S : Finset V,
      (q + 1) * #G.edgeFinset ≤ 2 * q * #(G.cutEdgeFinset S) := by
  classical
  let k := q / 2
  let F := (Finset.univ : Finset (Fin q)).powersetCard k
  have hk : 1 ≤ k := by simp only [k]; omega
  have hkq : k ≤ q := by simp only [k]; omega
  have hF : F.Nonempty := by
    apply Finset.powersetCard_nonempty.mpr
    simpa only [card_univ, Fintype.card_fin] using hkq
  have hcoeff := Nat.mul_le_mul_right (#G.edgeFinset) (balanced_choose_ineq hq)
  have hsum := sum_balanced_colorCuts (G := G) hk c
  have htotal :
      #F * ((q + 1) * #G.edgeFinset) ≤
        2 * q * ∑ A ∈ F, #(G.edgeFinset.filter (colorCrosses c A)) := by
    simp only [F, card_powersetCard, card_univ, Fintype.card_fin]
    rw [hsum]
    convert hcoeff using 1 <;> ring
  have havg :
      (∑ A ∈ F, (q + 1) * #G.edgeFinset) ≤
        ∑ A ∈ F, 2 * q * #(G.edgeFinset.filter (colorCrosses c A)) := by
    rw [Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
    exact htotal
  obtain ⟨A, hAF, hA⟩ := Finset.exists_le_of_sum_le hF havg
  let S : Finset V := Finset.univ.filter fun v ↦ c v ∈ A
  have hcut :
      G.cutEdgeFinset S = G.edgeFinset.filter (colorCrosses c A) := by
    ext e
    induction e using Sym2.inductionOn with
    | _ u v => simp [cutEdgeFinset, colorCrosses, S]
  refine ⟨S, ?_⟩
  rw [hcut]
  exact hA

/-- Graph-valued form of `exists_cutEdgeFinset_mul_bound`: the selected edges are the
standard bipartite `between S Sᶜ` subgraph of `G`. -/
theorem exists_bipartite_cut_mul_bound {G : SimpleGraph V} [DecidableRel G.Adj]
    {q : ℕ} (hq : 2 ≤ q) (c : G.Coloring (Fin q))
    (hc : Function.Surjective c) :
    ∃ S : Finset V,
      G.between (S : Set V) (S : Set V)ᶜ ≤ G ∧
      (G.between (S : Set V) (S : Set V)ᶜ).IsBipartite ∧
      (q + 1) * #G.edgeFinset ≤
        2 * q * #(G.between (S : Set V) (S : Set V)ᶜ).edgeFinset := by
  obtain ⟨S, hS⟩ := exists_cutEdgeFinset_mul_bound hq c hc
  refine ⟨S, G.between_le, G.between_compl_isBipartite S, ?_⟩
  rw [edgeFinset_between_compl_eq_cutEdgeFinset]
  exact hS


end SimpleGraph

