import ErdosProblems.Erdos788.TriangleCounting
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Finset.Max
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos788

open Finset

section Families

variable {V : Type*} [DecidableEq V]

/-- Members of a finite family which are contained in `S`. -/
def containedCount (F : Finset (Finset V)) (S : Finset V) : ℕ :=
  (F.filter ( · ⊆ S)).card

@[simp]
theorem containedCount_empty (S : Finset V) : containedCount ∅ S = 0 := by
  simp [containedCount]

theorem sum_powerset_containedCount
    {U : Finset V} {F : Finset (Finset V)} {k : ℕ}
    (hFsub : ∀ e ∈ F, e ⊆ U)
    (hFcard : ∀ e ∈ F, e.card = k) :
    ∑ S ∈ U.powerset, containedCount F S =
      F.card * 2 ^ (U.card - k) := by
  classical
  have hcount (S : Finset V) :
      containedCount F S = ∑ e ∈ F, if e ⊆ S then 1 else 0 := by
    rw [containedCount, card_eq_sum_ones, sum_filter]
  simp_rw [hcount]
  rw [sum_comm]
  calc
    (∑ e ∈ F, ∑ S ∈ U.powerset, if e ⊆ S then 1 else 0) =
        ∑ _e ∈ F, 2 ^ (U.card - k) := by
      apply sum_congr rfl
      intro e he
      rw [sum_boole]
      change ((U.powerset).filter (e ⊆ ·)).card = _
      rw [← Icc_eq_filter_powerset, card_Icc_finset (hFsub e he), hFcard e he]
    _ = F.card * 2 ^ (U.card - k) := by simp

theorem pow_mul_sum_powerset_containedCount
    {U : Finset V} {F : Finset (Finset V)} {k : ℕ}
    (hFsub : ∀ e ∈ F, e ⊆ U)
    (hFcard : ∀ e ∈ F, e.card = k) :
    2 ^ k * (∑ S ∈ U.powerset, containedCount F S) =
      2 ^ U.card * F.card := by
  rw [sum_powerset_containedCount hFsub hFcard]
  by_cases hF : F = ∅
  · simp [hF]
  · have hFn : F.Nonempty := nonempty_iff_ne_empty.mpr hF
    obtain ⟨e, he⟩ := hFn
    have hk : k ≤ U.card := by
      rw [← hFcard e he]
      exact card_le_card (hFsub e he)
    have hp : 2 ^ k * 2 ^ (U.card - k) = 2 ^ U.card := by
      rw [← pow_add, Nat.add_sub_of_le hk]
    calc
      2 ^ k * (F.card * 2 ^ (U.card - k)) =
          F.card * (2 ^ k * 2 ^ (U.card - k)) := by ac_rfl
      _ = F.card * 2 ^ U.card := by rw [hp]
      _ = 2 ^ U.card * F.card := by ac_rfl

def singletonFamily (U : Finset V) : Finset (Finset V) :=
  U.image ({·} : V → Finset V)

@[simp]
theorem card_singletonFamily (U : Finset V) :
    (singletonFamily U).card = U.card := by
  rw [singletonFamily, card_image_of_injective]
  intro x y h
  simpa using! h

theorem singletonFamily_sub (U : Finset V) :
    ∀ e ∈ singletonFamily U, e ⊆ U := by
  intro e he
  rw [singletonFamily, mem_image] at he
  obtain ⟨v, hv, rfl⟩ := he
  simpa using! hv

theorem singletonFamily_card_one (U : Finset V) :
    ∀ e ∈ singletonFamily U, e.card = 1 := by
  intro e he
  rw [singletonFamily, mem_image] at he
  obtain ⟨v, _hv, rfl⟩ := he
  simp

theorem containedCount_singletonFamily {U S : Finset V} (hS : S ⊆ U) :
    containedCount (singletonFamily U) S = S.card := by
  classical
  have heq : (singletonFamily U).filter ( · ⊆ S) = singletonFamily S := by
    ext e
    simp only [singletonFamily, mem_filter, mem_image]
    constructor
    · rintro ⟨⟨v, hvU, rfl⟩, hvS⟩
      exact ⟨v, hvS (mem_singleton_self v), rfl⟩
    · rintro ⟨v, hvS, rfl⟩
      exact ⟨⟨v, hS hvS, rfl⟩, by simpa⟩
  rw [containedCount, heq, card_singletonFamily]

/-- Restrict a family of finite subsets to those contained in `S`. -/
def restrictFamily (F : Finset (Finset V)) (S : Finset V) : Finset (Finset V) :=
  F.filter (· ⊆ S)

@[simp]
theorem card_restrictFamily (F : Finset (Finset V)) (S : Finset V) :
    (restrictFamily F S).card = containedCount F S := by
  rfl

theorem restrictFamily_sub (F : Finset (Finset V)) (S : Finset V) :
    ∀ e ∈ restrictFamily F S, e ⊆ S := by
  simp [restrictFamily]

theorem restrictFamily_card {F : Finset (Finset V)} {S : Finset V} {k : ℕ}
    (hFcard : ∀ e ∈ F, e.card = k) :
  ∀ e ∈ restrictFamily F S, e.card = k := by
  intro e he
  exact hFcard e (mem_filter.mp he).1

theorem containedCount_restrictFamily {F : Finset (Finset V)} {R S : Finset V}
    (hRS : R ⊆ S) :
    containedCount (restrictFamily F S) R = containedCount F R := by
  simp only [containedCount, restrictFamily]
  congr 1
  ext e
  simp only [mem_filter]
  constructor
  · exact fun h ↦ ⟨h.1.1, h.2⟩
  · exact fun h ↦ ⟨⟨h.1, fun x hx ↦ hRS (h.2 hx)⟩, h.2⟩

/-- A linear score for a sampled subset, penalizing contained two- and
three-element features. -/
def subsetScore (a c d : ℚ) (F₂ F₃ : Finset (Finset V))
    (S : Finset V) : ℚ :=
  a * S.card - c * containedCount F₂ S - d * containedCount F₃ S

/-- One Bernoulli-halving step, proved by averaging over the powerset. -/
theorem exists_subset_score_ge_half
    (U : Finset V) (F₂ F₃ : Finset (Finset V))
    (hF₂sub : ∀ e ∈ F₂, e ⊆ U) (hF₂card : ∀ e ∈ F₂, e.card = 2)
    (hF₃sub : ∀ e ∈ F₃, e ⊆ U) (hF₃card : ∀ e ∈ F₃, e.card = 3)
    (a c d : ℚ) :
    ∃ S ∈ U.powerset,
      a * U.card / 2 - c * F₂.card / 4 - d * F₃.card / 8 ≤
        subsetScore a c d F₂ F₃ S := by
  classical
  have h₁n := pow_mul_sum_powerset_containedCount
    (singletonFamily_sub U) (singletonFamily_card_one U)
  have h₁count :
      (∑ S ∈ U.powerset, containedCount (singletonFamily U) S) =
        ∑ S ∈ U.powerset, S.card := by
    apply sum_congr rfl
    intro S hS
    exact containedCount_singletonFamily (mem_powerset.mp hS)
  rw [h₁count] at h₁n
  norm_num at h₁n
  have h₂n := pow_mul_sum_powerset_containedCount hF₂sub hF₂card
  have h₃n := pow_mul_sum_powerset_containedCount hF₃sub hF₃card
  have h₁ : ∑ S ∈ U.powerset, (S.card : ℚ) =
      (2 ^ U.card : ℚ) * U.card / 2 := by
    have h₁c : (2 : ℚ) * ∑ S ∈ U.powerset, (S.card : ℚ) =
        (2 ^ U.card : ℚ) * U.card := by exact_mod_cast h₁n
    linarith
  have h₂ : ∑ S ∈ U.powerset, (containedCount F₂ S : ℚ) =
      (2 ^ U.card : ℚ) * F₂.card / 4 := by
    norm_num at h₂n
    have h₂c : (4 : ℚ) *
        ∑ S ∈ U.powerset, (containedCount F₂ S : ℚ) =
          (2 ^ U.card : ℚ) * F₂.card := by exact_mod_cast h₂n
    linarith
  have h₃ : ∑ S ∈ U.powerset, (containedCount F₃ S : ℚ) =
      (2 ^ U.card : ℚ) * F₃.card / 8 := by
    norm_num at h₃n
    have h₃c : (8 : ℚ) *
        ∑ S ∈ U.powerset, (containedCount F₃ S : ℚ) =
          (2 ^ U.card : ℚ) * F₃.card := by exact_mod_cast h₃n
    linarith
  have hsum :
      (∑ S ∈ U.powerset, subsetScore a c d F₂ F₃ S) =
        (2 ^ U.card : ℚ) *
          (a * U.card / 2 - c * F₂.card / 4 - d * F₃.card / 8) := by
    calc
      (∑ S ∈ U.powerset, subsetScore a c d F₂ F₃ S) =
          a * (∑ S ∈ U.powerset, (S.card : ℚ)) -
          c * (∑ S ∈ U.powerset, (containedCount F₂ S : ℚ)) -
          d * (∑ S ∈ U.powerset, (containedCount F₃ S : ℚ)) := by
        simp [subsetScore, Finset.mul_sum, Finset.sum_sub_distrib]
      _ = _ := by rw [h₁, h₂, h₃]; ring
  obtain ⟨S, hSU, hSmax⟩ := exists_max_image U.powerset
    (subsetScore a c d F₂ F₃) ⟨∅, empty_mem_powerset U⟩
  refine ⟨S, hSU, ?_⟩
  have hsumle :
      (∑ R ∈ U.powerset, subsetScore a c d F₂ F₃ R) ≤
        U.powerset.card • subsetScore a c d F₂ F₃ S :=
    sum_le_card_nsmul _ _ _ hSmax
  rw [hsum, card_powerset, nsmul_eq_mul] at hsumle
  norm_num [Nat.cast_pow] at hsumle
  linarith

/-- Iterating the exact halving average realizes Bernoulli sampling with
parameter `2⁻ᵗ`, without introducing a probability space. -/
theorem exists_subset_score_ge_pow
    (t : ℕ) (U : Finset V) (F₂ F₃ : Finset (Finset V))
    (hF₂sub : ∀ e ∈ F₂, e ⊆ U) (hF₂card : ∀ e ∈ F₂, e.card = 2)
    (hF₃sub : ∀ e ∈ F₃, e ⊆ U) (hF₃card : ∀ e ∈ F₃, e.card = 3)
    (a c d : ℚ) :
    ∃ S ∈ U.powerset,
      a * U.card / 2 ^ t - c * F₂.card / 4 ^ t - d * F₃.card / 8 ^ t ≤
        subsetScore a c d F₂ F₃ S := by
  induction t generalizing U F₂ F₃ a c d with
  | zero =>
      refine ⟨U, mem_powerset.mpr Subset.rfl, ?_⟩
      have h₂ : containedCount F₂ U = F₂.card := by
        rw [containedCount, filter_eq_self.mpr hF₂sub]
      have h₃ : containedCount F₃ U = F₃.card := by
        rw [containedCount, filter_eq_self.mpr hF₃sub]
      simp [subsetScore, h₂, h₃]
  | succ t ih =>
      obtain ⟨R, hRU, hRbound⟩ := ih U F₂ F₃ hF₂sub hF₂card hF₃sub hF₃card
        (a / 2) (c / 4) (d / 8)
      let F₂R := restrictFamily F₂ R
      let F₃R := restrictFamily F₃ R
      obtain ⟨S, hSR, hSbound⟩ := exists_subset_score_ge_half R F₂R F₃R
        (restrictFamily_sub F₂ R) (restrictFamily_card hF₂card)
        (restrictFamily_sub F₃ R) (restrictFamily_card hF₃card) a c d
      have hSR' : S ⊆ R := mem_powerset.mp hSR
      have hRU' : R ⊆ U := mem_powerset.mp hRU
      refine ⟨S, mem_powerset.mpr (hSR'.trans hRU'), ?_⟩
      have h₂S : containedCount F₂R S = containedCount F₂ S := by
        exact containedCount_restrictFamily hSR'
      have h₃S : containedCount F₃R S = containedCount F₃ S := by
        exact containedCount_restrictFamily hSR'
      have h₂R : F₂R.card = containedCount F₂ R := by rfl
      have h₃R : F₃R.card = containedCount F₃ R := by rfl
      have hSbound' :
          a * R.card / 2 - c * F₂R.card / 4 - d * F₃R.card / 8 ≤
            subsetScore a c d F₂ F₃ S := by
        simpa only [subsetScore, h₂S, h₃S] using! hSbound
      calc
        a * (U.card : ℚ) / 2 ^ (t + 1) -
              c * (F₂.card : ℚ) / 4 ^ (t + 1) -
              d * (F₃.card : ℚ) / 8 ^ (t + 1) =
            (a / 2) * U.card / 2 ^ t -
              (c / 4) * F₂.card / 4 ^ t -
              (d / 8) * F₃.card / 8 ^ t := by
                rw [pow_succ, pow_succ, pow_succ]
                ring
        _ ≤ subsetScore (a / 2) (c / 4) (d / 8) F₂ F₃ R := hRbound
        _ = a * R.card / 2 - c * F₂R.card / 4 - d * F₃R.card / 8 := by
          rw [h₂R, h₃R]
          simp only [subsetScore]
          ring
        _ ≤ subsetScore a c d F₂ F₃ S := hSbound'

end Families

section TwoCliques

variable {W : Type*} [Fintype W] [DecidableEq W]
variable (G : SimpleGraph W) [DecidableRel G.Adj]

/-- The two-cliques of a finite simple graph are its unordered edges. -/
theorem cliqueFinset_two_eq_edge_image :
    G.cliqueFinset 2 =
      G.edgeFinset.attach.image (fun e : G.edgeFinset ↦ e.1.toFinset) := by
  ext s
  simp only [SimpleGraph.mem_cliqueFinset_iff, mem_image, mem_attach, true_and]
  constructor
  · intro hs
    obtain ⟨x, y, hxy, rfl⟩ := card_eq_two.mp hs.card_eq
    have hadj : G.Adj x y := hs.isClique (by simp) (by simp) hxy
    let e : G.edgeFinset := ⟨s(x, y), SimpleGraph.mem_edgeFinset.mpr hadj⟩
    refine ⟨e, ?_⟩
    simp [e, Sym2.toFinset_mk_eq]
  · rintro ⟨e, rfl⟩
    have hcard : e.1.toFinset.card = 2 :=
      G.card_toFinset_mem_edgeFinset e
    constructor
    · rcases e with ⟨e, he⟩
      induction e with
      | _ x y =>
          have hadj : G.Adj x y := SimpleGraph.mem_edgeFinset.mp he
          have hxy : x ≠ y := by
            intro h
            subst y
            exact G.irrefl hadj
          simpa only [Sym2.toFinset_mk_eq, Finset.coe_insert,
            Finset.coe_singleton] using!
            (SimpleGraph.isClique_pair.mpr fun _ ↦ hadj)
    · exact hcard

theorem card_cliqueFinset_two_eq_card_edgeFinset :
    (G.cliqueFinset 2).card = G.edgeFinset.card := by
  rw [cliqueFinset_two_eq_edge_image G]
  rw [card_image_of_injective]
  · simp
  · intro e f hef
    apply Subtype.ext
    apply Sym2.ext
    intro x
    change e.1.toFinset = f.1.toFinset at hef
    rw [← Sym2.mem_toFinset, ← Sym2.mem_toFinset, hef]

end TwoCliques

theorem two_mul_card_twoCliques_sumGraph_le {N : ℕ} (A : Finset ℕ) :
    2 * ((sumGraph N A).cliqueFinset 2).card ≤ N * A.card := by
  rw [card_cliqueFinset_two_eq_card_edgeFinset]
  rw [← SimpleGraph.sum_degrees_eq_twice_card_edges]
  calc
    (∑ v : Fin N, (sumGraph N A).degree v) ≤ ∑ _v : Fin N, A.card := by
      exact sum_le_sum fun v _ ↦ degree_sumGraph_le_card A v
    _ = N * A.card := by simp

section TriangleFreeCore

variable {W : Type*} [Fintype W] [DecidableEq W]
variable (G : SimpleGraph W) [DecidableRel G.Adj]

/-- All vertices lying in a triangle contained in the sampled set. -/
def triangleSupport (S : Finset W) : Finset W :=
  (restrictFamily (G.cliqueFinset 3) S).biUnion id

/-- Delete every vertex that lies in a sampled triangle. -/
def triangleFreeCore (S : Finset W) : Finset W :=
  S \ triangleSupport G S

theorem triangleFreeCore_subset (S : Finset W) :
    triangleFreeCore G S ⊆ S :=
  sdiff_subset

theorem card_triangleSupport_le (S : Finset W) :
    (triangleSupport G S).card ≤
      3 * containedCount (G.cliqueFinset 3) S := by
  classical
  calc
    (triangleSupport G S).card ≤
        ∑ t ∈ restrictFamily (G.cliqueFinset 3) S, t.card := by
      exact card_biUnion_le
    _ = ∑ _t ∈ restrictFamily (G.cliqueFinset 3) S, 3 := by
      apply sum_congr rfl
      intro t ht
      exact (SimpleGraph.mem_cliqueFinset_iff.mp (mem_filter.mp ht).1).card_eq
    _ = 3 * containedCount (G.cliqueFinset 3) S := by
      simp [Nat.mul_comm]

theorem card_sample_le_core_add_triangles (S : Finset W) :
    S.card ≤ (triangleFreeCore G S).card +
      3 * containedCount (G.cliqueFinset 3) S := by
  calc
    S.card ≤ (S \ triangleSupport G S).card + (triangleSupport G S).card :=
      card_le_card_sdiff_add_card
    _ ≤ (S \ triangleSupport G S).card +
        3 * containedCount (G.cliqueFinset 3) S :=
      Nat.add_le_add_left (card_triangleSupport_le G S) _
    _ = _ := rfl

omit [Fintype W] [DecidableEq W] [DecidableRel G.Adj] in
theorem isNClique_map_induce {s : Set W} [DecidablePred (· ∈ s)]
    {n : ℕ} {t : Finset s} (ht : (G.induce s).IsNClique n t) :
    G.IsNClique n (t.map (Function.Embedding.subtype s)) := by
  constructor
  · intro x hx y hy hxy
    change x ∈ t.map (Function.Embedding.subtype s) at hx
    change y ∈ t.map (Function.Embedding.subtype s) at hy
    rw [mem_map] at hx hy
    obtain ⟨x, hx, rfl⟩ := hx
    obtain ⟨y, hy, rfl⟩ := hy
    apply SimpleGraph.induce_adj.mp
    exact ht.isClique hx hy fun h ↦ hxy (congrArg Subtype.val h)
  · simpa using! ht.card_eq

theorem triangleFree_induce_core (S : Finset W) :
    (G.induce (triangleFreeCore G S : Set W)).CliqueFree 3 := by
  classical
  intro t ht
  let t' : Finset W := t.map
    (Function.Embedding.subtype (triangleFreeCore G S : Set W))
  have ht' : G.IsNClique 3 t' := by
    exact isNClique_map_induce G ht
  have ht'sub : t' ⊆ S := by
    intro x hx
    simp only [t', mem_map] at hx
    obtain ⟨x, _hxt, rfl⟩ := hx
    exact triangleFreeCore_subset G S x.2
  have ht'mem : t' ∈ restrictFamily (G.cliqueFinset 3) S := by
    exact mem_filter.mpr
      ⟨SimpleGraph.mem_cliqueFinset_iff.mpr ht', ht'sub⟩
  have ht'pos : 0 < t'.card := by
    rw [ht'.card_eq]
    norm_num
  obtain ⟨x, hx⟩ := card_pos.mp ht'pos
  have hxsupport : x ∈ triangleSupport G S := by
    exact mem_biUnion.mpr ⟨t', ht'mem, hx⟩
  have hxcore : x ∈ triangleFreeCore G S := by
    simp only [t', mem_map] at hx
    obtain ⟨x, _hxt, rfl⟩ := hx
    exact x.2
  exact (mem_sdiff.mp hxcore).2 hxsupport

theorem card_twoCliques_induce_core_le (S : Finset W) :
    ((G.induce (triangleFreeCore G S : Set W)).cliqueFinset 2).card ≤
      containedCount (G.cliqueFinset 2) S := by
  classical
  let emb := Function.Embedding.subtype (triangleFreeCore G S : Set W)
  refine card_le_card_of_injOn (fun e : Finset (triangleFreeCore G S : Set W) ↦
    e.map emb) ?_ ?_
  · intro e he
    have hec : (G.induce (triangleFreeCore G S : Set W)).IsNClique 2 e :=
      SimpleGraph.mem_cliqueFinset_iff.mp (by simpa only [Finset.mem_coe] using! he)
    apply mem_filter.mpr
    constructor
    · exact SimpleGraph.mem_cliqueFinset_iff.mpr (isNClique_map_induce G hec)
    · intro x hx
      rw [mem_map] at hx
      obtain ⟨x, _hxe, rfl⟩ := hx
      exact triangleFreeCore_subset G S x.2
  · intro e _he f _hf hef
    exact Finset.map_injective emb hef

/-- Forget the subtype proof after taking an independent set in an induced
graph. -/
def liftInducedFinset (S : Finset W)
    (C : Finset (S : Set W)) : Finset W :=
  C.map (Function.Embedding.subtype (S : Set W))

omit [Fintype W] [DecidableEq W] in
@[simp]
theorem card_liftInducedFinset (S : Finset W) (C : Finset (S : Set W)) :
    (liftInducedFinset S C).card = C.card := by
  exact card_map _

omit [Fintype W] [DecidableEq W] [DecidableRel G.Adj] in
theorem isIndepSet_liftInducedFinset {S : Finset W}
    {C : Finset (S : Set W)}
    (hC : (G.induce (S : Set W)).IsIndepSet (C : Set (S : Set W))) :
    G.IsIndepSet (liftInducedFinset S C : Set W) := by
  rw [SimpleGraph.isIndepSet_iff] at hC ⊢
  intro x hx y hy hxy
  change x ∈ liftInducedFinset S C at hx
  change y ∈ liftInducedFinset S C at hy
  rw [liftInducedFinset, mem_map] at hx hy
  obtain ⟨x, hx, rfl⟩ := hx
  obtain ⟨y, hy, rfl⟩ := hy
  have hxy' : x ≠ y := fun h ↦ hxy (congrArg Subtype.val h)
  exact hC (by simpa using! hx) (by simpa using! hy) hxy'

omit [DecidableEq W] [DecidableRel G.Adj] in
theorem indepNum_induce_finset_le (S : Finset W) :
    (G.induce (S : Set W)).indepNum ≤ G.indepNum := by
  obtain ⟨C, hC⟩ := SimpleGraph.exists_isNIndepSet_indepNum
    (G := G.induce (S : Set W))
  calc
    (G.induce (S : Set W)).indepNum = C.card := hC.card_eq.symm
    _ = (liftInducedFinset S C).card := (card_liftInducedFinset S C).symm
    _ ≤ G.indepNum := (isIndepSet_liftInducedFinset G hC.isIndepSet).card_le_indepNum

end TriangleFreeCore

theorem sampling_penalty_lower
    {n b e tri q : ℚ}
    (hn : 0 ≤ n) (hb : 0 ≤ b)
    (hq : 0 < q)
    (hedges : 2 * e ≤ n * b)
    (htriangles : 6 * tri ≤ b ^ 3)
    (hscale : 2 * b ^ 3 ≤ n * q ^ 2) :
    n / (2 * q) ≤
      n / q - (q / (2 * (b + 1))) * e / q ^ 2 - 3 * tri / q ^ 3 := by
  have hb1 : 0 < b + 1 := by linarith
  have hq0 : 0 ≤ q := hq.le
  have hedge' : 2 * e ≤ n * (b + 1) := by
    exact hedges.trans (mul_le_mul_of_nonneg_left (by linarith) hn)
  have hedgeMul := mul_le_mul_of_nonneg_right hedge' hq0
  have hedgeTerm : (q / (2 * (b + 1))) * e / q ^ 2 ≤ n / (4 * q) := by
    have hid : (q / (2 * (b + 1))) * e / q ^ 2 =
        e / (2 * (b + 1) * q) := by
      field_simp
    rw [hid, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have htri12 : 12 * tri ≤ n * q ^ 2 := by
    nlinarith
  have htriMul := mul_le_mul_of_nonneg_right htri12 hq0
  have htriTerm : 3 * tri / q ^ 3 ≤ n / (4 * q) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg q]
  have hnid : n / q = n / (2 * q) + n / (2 * q) := by
    field_simp
    ring
  have hquarter : n / (4 * q) + n / (4 * q) = n / (2 * q) := by
    field_simp
    ring
  linarith

/-- Exact finite sampling-and-deletion statement for a normalized sum graph.
The first inequality retains half the expected sample, and the second one
controls the average degree of the triangle-free core. -/
theorem exists_triangleFree_sample {N : ℕ} (A : Finset ℕ) (t : ℕ)
    (hscale : 2 * A.card ^ 3 ≤ N * (2 ^ t) ^ 2) :
    ∃ R : Finset (Fin N),
      ((sumGraph N A).induce (R : Set (Fin N))).CliqueFree 3 ∧
      (N : ℚ) / (2 * (2 : ℚ) ^ t) ≤ (R.card : ℚ) ∧
      (2 ^ t) *
          (((sumGraph N A).induce (R : Set (Fin N))).cliqueFinset 2).card ≤
        2 * (A.card + 1) * R.card := by
  classical
  let G := sumGraph N A
  let F₂ := G.cliqueFinset 2
  let F₃ := G.cliqueFinset 3
  let q : ℚ := (2 : ℚ) ^ t
  have h₂sub : ∀ e ∈ F₂, e ⊆ (Finset.univ : Finset (Fin N)) := by
    intro e _he
    exact subset_univ e
  have h₂card : ∀ e ∈ F₂, e.card = 2 := by
    intro e he
    exact (SimpleGraph.mem_cliqueFinset_iff.mp he).card_eq
  have h₃sub : ∀ e ∈ F₃, e ⊆ (Finset.univ : Finset (Fin N)) := by
    intro e _he
    exact subset_univ e
  have h₃card : ∀ e ∈ F₃, e.card = 3 := by
    intro e he
    exact (SimpleGraph.mem_cliqueFinset_iff.mp he).card_eq
  obtain ⟨S, _hSuniv, hS⟩ := exists_subset_score_ge_pow t
    (Finset.univ : Finset (Fin N)) F₂ F₃ h₂sub h₂card h₃sub h₃card
    1 (q / (2 * (A.card + 1))) 3
  have hpow4 : (4 : ℚ) ^ t = q ^ 2 := by
    calc
      (4 : ℚ) ^ t = ((2 : ℚ) ^ 2) ^ t := by norm_num
      _ = (2 : ℚ) ^ (2 * t) := (pow_mul (2 : ℚ) 2 t).symm
      _ = (2 : ℚ) ^ (t * 2) := by rw [Nat.mul_comm]
      _ = q ^ 2 := pow_mul (2 : ℚ) t 2
  have hpow8 : (8 : ℚ) ^ t = q ^ 3 := by
    calc
      (8 : ℚ) ^ t = ((2 : ℚ) ^ 3) ^ t := by norm_num
      _ = (2 : ℚ) ^ (3 * t) := (pow_mul (2 : ℚ) 3 t).symm
      _ = (2 : ℚ) ^ (t * 3) := by rw [Nat.mul_comm]
      _ = q ^ 3 := pow_mul (2 : ℚ) t 3
  have hedgeNat : 2 * F₂.card ≤ N * A.card := by
    simpa only [G, F₂] using! two_mul_card_twoCliques_sumGraph_le A
  have htriNat : 6 * F₃.card ≤ A.card ^ 3 := by
    calc
      6 * F₃.card ≤ 6 * A.card.choose 3 := by
        exact Nat.mul_le_mul_left 6 (by
          simpa only [G, F₃] using! triangle_count_le_choose A)
      _ ≤ A.card ^ 3 := six_mul_choose_three_le_cube A.card
  have hedgeQ : (2 : ℚ) * F₂.card ≤ (N : ℚ) * A.card := by
    exact_mod_cast hedgeNat
  have htriQ : (6 : ℚ) * F₃.card ≤ (A.card : ℚ) ^ 3 := by
    exact_mod_cast htriNat
  have hscaleQ : (2 : ℚ) * (A.card : ℚ) ^ 3 ≤ (N : ℚ) * q ^ 2 := by
    dsimp only [q]
    exact_mod_cast hscale
  have hpenalty := sampling_penalty_lower
    (n := (N : ℚ)) (b := (A.card : ℚ)) (e := (F₂.card : ℚ))
    (tri := (F₃.card : ℚ)) (q := q)
    (by positivity) (by positivity) (by positivity)
    hedgeQ htriQ hscaleQ
  have hsampleScore :
      (N : ℚ) / (2 * q) ≤ subsetScore 1
        (q / (2 * (A.card + 1))) 3 F₂ F₃ S := by
    apply hpenalty.trans
    convert! hS using 1
    all_goals
      simp only [card_univ, Fintype.card_fin, one_mul, hpow4, hpow8, q]
  let R := triangleFreeCore G S
  have hcardLossNat : S.card ≤ R.card + 3 * containedCount F₃ S := by
    simpa only [R, G, F₃] using! card_sample_le_core_add_triangles G S
  have hcardLossQ : (S.card : ℚ) ≤
      (R.card : ℚ) + 3 * containedCount F₃ S := by
    exact_mod_cast hcardLossNat
  have hcombined :
      (N : ℚ) / (2 * q) +
          (q / (2 * (A.card + 1))) * containedCount F₂ S ≤ R.card := by
    simp only [subsetScore, one_mul] at hsampleScore
    linarith
  have hRcard : (N : ℚ) / (2 * q) ≤ (R.card : ℚ) := by
    have hnonneg : 0 ≤
        (q / (2 * (A.card + 1))) * containedCount F₂ S := by positivity
    linarith
  have hedgeSampleQ : q * containedCount F₂ S ≤
      2 * (A.card + 1) * R.card := by
    have hterm : (q / (2 * (A.card + 1))) * containedCount F₂ S ≤
        (R.card : ℚ) := by
      have hNterm : 0 ≤ (N : ℚ) / (2 * q) := by positivity
      linarith
    have hbpos : (0 : ℚ) < 2 * ((A.card : ℚ) + 1) := by positivity
    calc
      q * containedCount F₂ S =
          (2 * ((A.card : ℚ) + 1)) *
            ((q / (2 * (A.card + 1))) * containedCount F₂ S) := by
              field_simp
      _ ≤ (2 * ((A.card : ℚ) + 1)) * R.card :=
        mul_le_mul_of_nonneg_left hterm hbpos.le
  have hedgeCoreNat :
      (((sumGraph N A).induce (R : Set (Fin N))).cliqueFinset 2).card ≤
        containedCount F₂ S := by
    simpa only [G, F₂, R] using! card_twoCliques_induce_core_le G S
  have hedgeCoreQ : q *
      (((sumGraph N A).induce (R : Set (Fin N))).cliqueFinset 2).card ≤
        2 * (A.card + 1) * R.card := by
    exact (mul_le_mul_of_nonneg_left (by exact_mod_cast hedgeCoreNat)
      (by positivity : 0 ≤ q)).trans hedgeSampleQ
  have hedgeCoreNat' : (2 ^ t) *
      (((sumGraph N A).induce (R : Set (Fin N))).cliqueFinset 2).card ≤
        2 * (A.card + 1) * R.card := by
    have hcast :
        (((2 ^ t) *
          (((sumGraph N A).induce (R : Set (Fin N))).cliqueFinset 2).card : ℕ) : ℚ) ≤
          ((2 * (A.card + 1) * R.card : ℕ) : ℚ) := by
      push_cast
      simpa only [q] using! hedgeCoreQ
    exact_mod_cast hcast
  refine ⟨R, ?_, hRcard, hedgeCoreNat'⟩
  simpa only [G, R] using! triangleFree_induce_core G S

/-- A power-of-two sampling denominator which is minimal up to a factor of
two.  The second inequality is the quantitative information obtained from
minimality. -/
theorem exists_sampling_exponent (N b : ℕ) (hN : 0 < N) :
    ∃ t : ℕ,
      2 * b ^ 3 ≤ N * (2 ^ t) ^ 2 ∧
        (t = 0 ∨ N * (2 ^ t) ^ 2 < 8 * b ^ 3) := by
  let p : ℕ → Prop := fun t ↦ 2 * b ^ 3 ≤ N * (2 ^ t) ^ 2
  have hex : ∃ t, p t := by
    obtain ⟨t, ht⟩ := pow_unbounded_of_one_lt (2 * b ^ 3) (by norm_num : 1 < (2 : ℕ))
    refine ⟨t, ?_⟩
    have hq : 1 ≤ 2 ^ t := Nat.one_le_two_pow
    calc
      2 * b ^ 3 ≤ 2 ^ t := ht.le
      _ ≤ (2 ^ t) ^ 2 := by nlinarith
      _ = 1 * (2 ^ t) ^ 2 := by simp
      _ ≤ N * (2 ^ t) ^ 2 := Nat.mul_le_mul_right _ (Nat.succ_le_iff.mpr hN)
  let t := Nat.find hex
  refine ⟨t, Nat.find_spec hex, ?_⟩
  by_cases ht : t = 0
  · exact Or.inl ht
  · right
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero ht
    have hpred : ¬p k := by
      intro hk
      have hmin : Nat.find hex ≤ k := Nat.find_min' hex hk
      change t ≤ k at hmin
      omega
    simp only [p, not_le] at hpred
    rw [hk]
    simpa only [pow_succ] using!
      (show N * (2 ^ k * 2) ^ 2 < 8 * b ^ 3 by nlinarith)

end Erdos788
