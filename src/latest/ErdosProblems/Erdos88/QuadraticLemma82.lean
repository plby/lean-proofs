import ErdosProblems.Erdos88.QuadraticNumerics

namespace Erdos88
namespace QuadraticCancellation

open Classical

noncomputable def tuplePriorSet {V : Type*} [Fintype V]
    {q : ℕ} (G : SimpleGraph V) (v : Fin q → V) (i : Fin q) : Finset V :=
  Finset.univ.filter fun x ↦ ∀ j : Fin q, j < i → ¬G.Adj (v j) x

noncomputable def tupleNewNeighborCell {V : Type*} [Fintype V]
    {q : ℕ} (G : SimpleGraph V) (v : Fin q → V) (i : Fin q) : Finset V :=
  neighborsIn G (v i) (tuplePriorSet G v i)

noncomputable def tupleRemainingCell {V : Type*} [Fintype V]
    {q : ℕ} (G : SimpleGraph V) (v : Fin q → V) (i : Fin q) : Finset V :=
  tuplePriorSet G v i \ tupleNewNeighborCell G v i

@[simp] lemma mem_tupleRemainingCell {V : Type*} [Fintype V]
    {q : ℕ} {G : SimpleGraph V} {v : Fin q → V} {i : Fin q} {x : V} :
    x ∈ tupleRemainingCell G v i ↔
      x ∈ tuplePriorSet G v i ∧ x ∉ tupleNewNeighborCell G v i := by
  classical
  simp [tupleRemainingCell]

/-- The ambient partition-and-tuples form of the combinatorial conclusion
in KSSS Lemma 8.2. -/
structure Lemma82Witness {n : ℕ} (G : SimpleGraph (Fin n))
    (beta : ℝ) (q ell : ℕ) where
  I : Finset (Fin n)
  J : Finset (Fin n)
  tuple : Fin ell → Fin q → Fin n
  partition : I ∪ J = Finset.univ
  disjoint : Disjoint I J
  card_I : I.card = ell * q
  tuple_mem_I : ∀ a i, tuple a i ∈ I
  tuple_injective : ∀ a, Function.Injective (tuple a)
  tuple_disjoint : ∀ {a b}, a ≠ b → ∀ i j, tuple a i ≠ tuple b j
  newCell_large : ∀ a i,
    (n : ℝ) ^ (1 - beta) <
      ((tupleNewNeighborCell G (tuple a) i ∩ J).card : ℝ)
  remainingCell_large : ∀ a i,
    (n : ℝ) ^ (1 - beta) <
      ((tupleRemainingCell G (tuple a) i ∩ J).card : ℝ)

lemma Lemma82Witness.card_I_add_card_J
    {n q ell : ℕ} {G : SimpleGraph (Fin n)} {beta : ℝ}
    (w : Lemma82Witness G beta q ell) :
    w.I.card + w.J.card = n := by
  rw [← Finset.card_union_of_disjoint w.disjoint, w.partition,
    Finset.card_univ, Fintype.card_fin]

noncomputable def DiverseNeighborhoodFamily.toLemma82Witness
    {n q ell : ℕ} {G : SimpleGraph (Fin n)} {beta rho : ℝ}
    {U : Finset (Fin n)} {allUsed : Finset U}
    (family : DiverseNeighborhoodFamily
      (G.induce (U : Set (Fin n))) rho Finset.univ q ell allUsed)
    (hcells : ∀ (a : Fin ell) (i : Fin q),
      (n : ℝ) ^ (1 - beta) <
          ((((family.chainAt a).chain.newNeighborSet i) \ allUsed).card : ℝ) ∧
        (n : ℝ) ^ (1 - beta) <
          ((((family.chainAt a).chain.remainingSet i) \ allUsed).card : ℝ)) :
    Lemma82Witness G beta q ell := by
  classical
  let I : Finset (Fin n) := allUsed.image Subtype.val
  let J : Finset (Fin n) := Finset.univ \ I
  let tuple : Fin ell → Fin q → Fin n := fun a i ↦
    ((family.chainAt a).chain.vertexAt i).1
  have htuple_mem (a : Fin ell) (i : Fin q) : tuple a i ∈ I := by
    dsimp only [tuple, I]
    apply Finset.mem_image.mpr
    refine ⟨(family.chainAt a).chain.vertexAt i, ?_, rfl⟩
    exact family.chainAt_used_subset a
      ((family.chainAt a).chain.vertexAt_mem_used i)
  have htuple_inj (a : Fin ell) : Function.Injective (tuple a) := by
    intro i j hij
    apply (family.chainAt a).chain.vertexAt_injective
    exact Subtype.ext hij
  have htuple_disjoint {a b : Fin ell} (hab : a ≠ b) (i j : Fin q) :
      tuple a i ≠ tuple b j := by
    intro hij
    have hsub :
        (family.chainAt a).chain.vertexAt i =
          (family.chainAt b).chain.vertexAt j := Subtype.ext hij
    have hdisj := family.chainAt_disjoint hab
    rw [Finset.disjoint_left] at hdisj
    exact hdisj ((family.chainAt a).chain.vertexAt_mem_used i)
      (hsub ▸ (family.chainAt b).chain.vertexAt_mem_used j)
  have hnewSubset (a : Fin ell) (i : Fin q) :
      ((((family.chainAt a).chain.newNeighborSet i) \ allUsed).image Subtype.val) ⊆
        tupleNewNeighborCell G (tuple a) i ∩ J := by
    intro x hx
    obtain ⟨xU, hxU, rfl⟩ := Finset.mem_image.mp hx
    have hxParts := Finset.mem_sdiff.mp hxU
    have hxNew := (mem_neighborsIn.mp hxParts.1)
    have hxPrior := hxNew.1
    have hxAdj : G.Adj (tuple a i) xU.1 := by
      exact (SimpleGraph.induce_adj.mp hxNew.2)
    have hxPriorAmbient : xU.1 ∈ tuplePriorSet G (tuple a) i := by
      rw [tuplePriorSet, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      intro j hji hadj
      have hnot := (Finset.mem_filter.mp hxPrior).2 j hji
      exact hnot (SimpleGraph.induce_adj.mpr hadj)
    have hxJ : xU.1 ∈ J := by
      dsimp only [J]
      rw [Finset.mem_sdiff]
      refine ⟨Finset.mem_univ _, ?_⟩
      intro hxI
      obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp hxI
      apply hxParts.2
      have : y = xU := Subtype.ext hyx
      simpa [this] using hy
    rw [Finset.mem_inter]
    refine ⟨?_, hxJ⟩
    exact mem_neighborsIn.mpr ⟨hxPriorAmbient, hxAdj⟩
  have hremainingSubset (a : Fin ell) (i : Fin q) :
      ((((family.chainAt a).chain.remainingSet i) \ allUsed).image Subtype.val) ⊆
        tupleRemainingCell G (tuple a) i ∩ J := by
    intro x hx
    obtain ⟨xU, hxU, rfl⟩ := Finset.mem_image.mp hx
    have hxParts := Finset.mem_sdiff.mp hxU
    have hxRemaining := Finset.mem_sdiff.mp hxParts.1
    have hxPriorAmbient : xU.1 ∈ tuplePriorSet G (tuple a) i := by
      rw [tuplePriorSet, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      intro j hji hadj
      have hnot := (Finset.mem_filter.mp hxRemaining.1).2 j hji
      exact hnot (SimpleGraph.induce_adj.mpr hadj)
    have hxNotNew : xU.1 ∉ tupleNewNeighborCell G (tuple a) i := by
      intro hxnew
      apply hxRemaining.2
      apply mem_neighborsIn.mpr
      refine ⟨hxRemaining.1, ?_⟩
      exact SimpleGraph.induce_adj.mpr (mem_neighborsIn.mp hxnew).2
    have hxJ : xU.1 ∈ J := by
      dsimp only [J]
      rw [Finset.mem_sdiff]
      refine ⟨Finset.mem_univ _, ?_⟩
      intro hxI
      obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp hxI
      apply hxParts.2
      have : y = xU := Subtype.ext hyx
      simpa [this] using hy
    rw [Finset.mem_inter]
    constructor
    · exact mem_tupleRemainingCell.mpr ⟨hxPriorAmbient, hxNotNew⟩
    · exact hxJ
  have hpartition : I ∪ J = Finset.univ := by
    dsimp only [J]
    exact Finset.union_sdiff_of_subset (Finset.subset_univ I)
  have hdisjointIJ : Disjoint I J := by
    dsimp only [J]
    exact Finset.disjoint_sdiff
  have hcardI : I.card = ell * q := by
    dsimp only [I]
    rw [Finset.card_image_of_injective _ Subtype.val_injective,
      family.used_card]
  refine
    { I := I
      J := J
      tuple := tuple
      partition := hpartition
      disjoint := hdisjointIJ
      card_I := hcardI
      tuple_mem_I := htuple_mem
      tuple_injective := htuple_inj
      tuple_disjoint := htuple_disjoint
      newCell_large := ?_
      remainingCell_large := ?_ }
  · intro a i
    have hcard := Finset.card_le_card (hnewSubset a i)
    have himage :
        (((((family.chainAt a).chain.newNeighborSet i) \ allUsed).image
          Subtype.val).card) =
          (((family.chainAt a).chain.newNeighborSet i) \ allUsed).card :=
      Finset.card_image_of_injective _ Subtype.val_injective
    rw [himage] at hcard
    exact (hcells a i).1.trans_le (by exact_mod_cast hcard)
  · intro a i
    have hcard := Finset.card_le_card (hremainingSubset a i)
    have himage :
        (((((family.chainAt a).chain.remainingSet i) \ allUsed).image
          Subtype.val).card) =
          (((family.chainAt a).chain.remainingSet i) \ allUsed).card :=
      Finset.card_image_of_injective _ Subtype.val_injective
    rw [himage] at hcard
    exact (hcells a i).2.trans_le (by exact_mod_cast hcard)

def Lemma82Witness.mono_beta {n q ell : ℕ} {G : SimpleGraph (Fin n)}
    {beta₀ beta : ℝ} (w : Lemma82Witness G beta₀ q ell)
    (hn : 1 ≤ n) (hbeta : beta₀ ≤ beta) : Lemma82Witness G beta q ell := by
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpow : (n : ℝ) ^ (1 - beta) ≤ (n : ℝ) ^ (1 - beta₀) :=
    Real.rpow_le_rpow_of_exponent_le hnreal (by linarith)
  exact
    { I := w.I
      J := w.J
      tuple := w.tuple
      partition := w.partition
      disjoint := w.disjoint
      card_I := w.card_I
      tuple_mem_I := w.tuple_mem_I
      tuple_injective := w.tuple_injective
      tuple_disjoint := w.tuple_disjoint
      newCell_large := fun a i ↦ hpow.trans_lt (w.newCell_large a i)
      remainingCell_large := fun a i ↦ hpow.trans_lt (w.remainingCell_large a i) }

/-- The canonical-size form produced by the proof of Lemma 8.2.  Exposing
the chosen ceiling, rather than immediately weakening it to an existential
lower bound, is needed in Lemma 8.1 to show that the tuple support is `o(n)`. -/
theorem ksssLemma82_canonical_smallBeta
    (C beta : ℝ) (hC : 0 < C) (hbeta : 0 < beta)
    (hbeta1 : beta ≤ 1 / 2) :
    ∃ zeta : ℝ, 0 < zeta ∧ ∃ N : ℕ, ∀ n ≥ N,
      ∀ G : SimpleGraph (Fin n), RamseyFree C G →
        let q := Nat.floor (zeta * Real.log n)
        Nonempty (Lemma82Witness G beta q
          (Nat.ceil ((n : ℝ) ^ (1 - beta)))) := by
  obtain ⟨rho, zeta, hrho, hrho1, hzeta, N, hpacked⟩ :=
    ksssLemma82_packed C beta hC hbeta hbeta1
  refine ⟨zeta, hzeta, N, ?_⟩
  intro n hn G hG
  let q := Nat.floor (zeta * Real.log n)
  let ell := Nat.ceil ((n : ℝ) ^ (1 - beta))
  obtain ⟨U, allUsed, family, hmU, hell, hcells⟩ := hpacked n hn G hG
  exact ⟨family.toLemma82Witness hcells⟩

theorem ksssLemma82_smallBeta
    (C beta : ℝ) (hC : 0 < C) (hbeta : 0 < beta)
    (hbeta1 : beta ≤ 1 / 2) :
    ∃ zeta : ℝ, 0 < zeta ∧ ∃ N : ℕ, ∀ n ≥ N,
      ∀ G : SimpleGraph (Fin n), RamseyFree C G →
        let q := Nat.floor (zeta * Real.log n)
        ∃ ell : ℕ, (n : ℝ) ^ (1 - beta) ≤ ell ∧
          Nonempty (Lemma82Witness G beta q ell) := by
  obtain ⟨zeta, hzeta, N, hcanonical⟩ :=
    ksssLemma82_canonical_smallBeta C beta hC hbeta hbeta1
  refine ⟨zeta, hzeta, N, ?_⟩
  intro n hn G hG
  let ell := Nat.ceil ((n : ℝ) ^ (1 - beta))
  exact ⟨ell, Nat.le_ceil _, hcanonical n hn G hG⟩

/-- KSSS Lemma 8.2 in its ambient partition-and-tuples form. -/
def KSSSLemma82 : Prop :=
  ∀ (C beta : ℝ), 0 < C → 0 < beta →
    ∃ zeta : ℝ, 0 < zeta ∧ ∃ N : ℕ, ∀ n ≥ N,
      ∀ G : SimpleGraph (Fin n), RamseyFree C G →
        let q := Nat.floor (zeta * Real.log n)
        ∃ ell : ℕ, (n : ℝ) ^ (1 - beta) ≤ ell ∧
          Nonempty (Lemma82Witness G beta q ell)

theorem ksssLemma82 : KSSSLemma82 := by
  intro C beta hC hbeta
  let beta₀ : ℝ := min beta (1 / 2)
  have hbeta₀ : 0 < beta₀ := by
    dsimp only [beta₀]
    exact lt_min hbeta (by norm_num)
  have hbeta₀half : beta₀ ≤ 1 / 2 := by
    exact min_le_right _ _
  have hbeta₀beta : beta₀ ≤ beta := min_le_left _ _
  obtain ⟨zeta, hzeta, N, hsmall⟩ :=
    ksssLemma82_smallBeta C beta₀ hC hbeta₀ hbeta₀half
  refine ⟨zeta, hzeta, max N 1, ?_⟩
  intro n hn G hG
  have hnN : N ≤ n := (le_max_left _ _).trans hn
  have hn1 : 1 ≤ n := (le_max_right _ _).trans hn
  obtain ⟨ell, hell, ⟨w⟩⟩ := hsmall n hnN G hG
  have hpow : (n : ℝ) ^ (1 - beta) ≤ (n : ℝ) ^ (1 - beta₀) := by
    have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    exact Real.rpow_le_rpow_of_exponent_le hnreal (by linarith)
  exact ⟨ell, hpow.trans hell, ⟨w.mono_beta hn1 hbeta₀beta⟩⟩

end QuadraticCancellation
end Erdos88
