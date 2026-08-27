import Arxiv.Arxiv2411_18291.BoundedGenerators
import Arxiv.Arxiv2411_18291.Basic
import Mathlib.Data.ZMod.Basic

/-!
# Bounded modular generators for unsaturated cliques

For any prescribed clique family in a finite host, choose at most `N*|K|`
generators modulo `N`, while respecting a cap on every face load. Every
clique with no saturated face is generated. Vectors are defined on all
ambient edges; restricting to the host is used only for the counting bound.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [Fintype V] [DecidableEq V] {q r : ℕ}

def modularCliqueVector (N r : ℕ) (Q : Block V q) : Block V r → ZMod N :=
  fun e => if e.val ⊆ Q.val then 1 else 0

def extendModularVector (N : ℕ) (K : Hypergraph V r) :
    (K → ZMod N) →+ (Block V r → ZMod N) where
  toFun := fun Φ e => if he : e ∈ K then Φ ⟨e, he⟩ else 0
  map_zero' := by funext e; simp
  map_add' := by
    intro Φ Ψ
    funext e
    by_cases he : e ∈ K <;> simp [he]

theorem extend_restricted_modularCliqueVector (N : ℕ) (K : Hypergraph V r)
    (Q : Block V q) (hQ : cliqueEdges r Q ⊆ K) :
    extendModularVector N K (fun e : K => modularCliqueVector N r Q e.val) =
      modularCliqueVector N r Q := by
  funext e
  by_cases he : e ∈ K
  · simp [extendModularVector, he]
  · have hnot : ¬e.val ⊆ Q.val := fun h => he (hQ ((mem_cliqueEdges _ _).mpr h))
    simp [extendModularVector, modularCliqueVector, he, hnot]

theorem exists_modular_generating_cliques_with_caps {T : Type*} (N : ℕ) (hN : 0 < N)
    (K : Hypergraph V (r + 1)) (D : Finset (Block V q))
    (hD : ∀ Q ∈ D, cliqueEdges (r + 1) Q ⊆ K)
    (incidence : Block V q → T → Prop) [DecidableRel incidence] (cap : T → ℕ) :
    ∃ G : Finset (Block V q), G ⊆ D ∧
      (∀ t, (G.filter fun Q => incidence Q t).card ≤ cap t) ∧
      G.card ≤ N * K.card ∧
      ∀ Q ∈ D,
        (∀ t, incidence Q t → (G.filter fun R => incidence R t).card < cap t) →
        modularCliqueVector N (r + 1) Q ∈ generatedSubgroup (modularCliqueVector N (r + 1)) G := by
  let : NeZero N := ⟨hN.ne'⟩
  let f : Block V q → K → ZMod N := fun Q e => modularCliqueVector N (r + 1) Q e.val
  obtain ⟨G, hGD, hdegree, hpow, _, hgen⟩ :=
    exists_generating_subfamily_with_caps D f incidence cap
  have hcard : Nat.card (K → ZMod N) = N ^ K.card := by
    simp only [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card, Fintype.card_coe]
  have hambient : Nat.card (generatedSubgroup f G) ≤ Nat.card (K → ZMod N) :=
    Nat.card_le_card_of_injective (fun x : generatedSubgroup f G => x.val) Subtype.coe_injective
  have hsize : G.card ≤ N * K.card := by
    apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    calc
      2 ^ G.card ≤ N ^ K.card := hpow.trans (hcard ▸ hambient)
      _ ≤ 2 ^ (N * K.card) := by
        rw [pow_mul]
        exact Nat.pow_le_pow_left (show N ≤ 2 ^ N from Nat.lt_two_pow_self.le) K.card
  have hrestrict : generatedSubgroup f G ≤
      (generatedSubgroup (modularCliqueVector N (r + 1)) G).comap (extendModularVector N K) := by
    apply (AddSubgroup.closure_le _).mpr
    rintro Φ ⟨Q, hQ, rfl⟩
    change extendModularVector N K (f Q) ∈ generatedSubgroup (modularCliqueVector N (r + 1)) G
    rw [show f Q = (fun e : K => modularCliqueVector N (r + 1) Q e.val) from rfl,
      extend_restricted_modularCliqueVector N K Q (hD Q (hGD hQ))]
    exact mem_generatedSubgroup _ hQ
  refine ⟨G, hGD, hdegree, hsize, ?_⟩
  intro Q hQ hunsaturated
  have h := hrestrict (hgen Q hQ hunsaturated)
  change extendModularVector N K (f Q) ∈ generatedSubgroup (modularCliqueVector N (r + 1)) G at h
  rwa [show f Q = (fun e : K => modularCliqueVector N (r + 1) Q e.val) from rfl,
    extend_restricted_modularCliqueVector N K Q (hD Q hQ)] at h

theorem exists_modular_generating_cliques (N : ℕ) (hN : 0 < N)
    (K : Hypergraph V (r + 1)) (D : Finset (Block V q))
    (hD : ∀ Q ∈ D, cliqueEdges (r + 1) Q ⊆ K) (cap : ℕ) :
    ∃ G : Finset (Block V q), G ⊆ D ∧
      (∀ S : Block V r, (G.filter fun Q => S.val ⊆ Q.val).card ≤ cap) ∧
      G.card ≤ N * K.card ∧
      ∀ Q ∈ D,
        (∀ S : Block V r, S.val ⊆ Q.val → (G.filter fun R => S.val ⊆ R.val).card < cap) →
        modularCliqueVector N (r + 1) Q ∈ generatedSubgroup (modularCliqueVector N (r + 1)) G :=
  exists_modular_generating_cliques_with_caps N hN K D hD
    (fun Q : Block V q => fun S : Block V r => S.val ⊆ Q.val) (fun _ => cap)

end Arxiv2411_18291
