import Mathlib
import ErdosProblems.Erdos550.CandidateForestEmbedding
import ErdosProblems.Erdos550.RegularPairTools

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The Hladký--Piguet rooted regular-pair lemma

This is the fully internal version of Lemma 5.12 used by the direct
off--Turán proof.  Unlike the older `regularPair_forest_embedding`, the
capacity hypothesis is local to the one small rooted tree.  Consequently a
regular pair may be filled component by component up to a small terminal
reserve, with no spurious density-squared loss.

The proof is the source proof written as a candidate-set argument.  Fixed
reservoirs `SP,SQ` of common order `L` are chosen inside the currently
available sets.  Every image in one reservoir is kept typical toward the
other.  Regularity deletes fewer than `ε|s|` (respectively `ε|t|`) atypical
vertices, while

`ε |s| + |tree| ≤ (d - 2ε)L`

pays for both that exceptional set and all earlier images.
-/

open SimpleGraph Finset

namespace Erdos550

open Classical

/-- Vertices of the left side typical toward a prescribed significant right
reservoir. -/
noncomputable def hpGoodLeft
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (ε : ℝ) (s t SQ : Finset V) : Finset V :=
  s.filter fun v =>
    ((G.edgeDensity s t : ℝ) - ε) * (SQ.card : ℝ) ≤
      ((SQ.filter fun w => G.Adj v w).card : ℝ)

/-- Vertices of the right side typical toward a prescribed significant left
reservoir. -/
noncomputable def hpGoodRight
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (ε : ℝ) (s t SP : Finset V) : Finset V :=
  t.filter fun v =>
    ((G.edgeDensity s t : ℝ) - ε) * (SP.card : ℝ) ≤
      ((SP.filter fun w => G.Adj v w).card : ℝ)

lemma hpGoodLeft_compl_lt
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    {s t SQ : Finset V} (hs : s.Nonempty)
    (hSQ : SQ ⊆ t) (hSQsig : ε * (t.card : ℝ) ≤ (SQ.card : ℝ))
    (huni : G.IsUniform ε s t) :
    (((s \ hpGoodLeft G ε s t SQ).card : ℕ) : ℝ) <
      ε * (s.card : ℝ) := by
  have hbad :=
    isUniform_few_low_degree_subset G hε0 hε1 hSQ hs hSQsig huni
  rw [show s \ hpGoodLeft G ε s t SQ =
      s.filter (fun a => ((SQ.filter fun b => G.Adj a b).card : ℝ) <
        ((G.edgeDensity s t : ℝ) - ε) * (SQ.card : ℝ)) by
    ext v
    simp only [hpGoodLeft, Finset.mem_sdiff, Finset.mem_filter]
    constructor
    · rintro ⟨hvs, hvbad⟩
      exact ⟨hvs, lt_of_not_ge fun hvdeg => hvbad ⟨hvs, hvdeg⟩⟩
    · rintro ⟨hvs, hvdeg⟩
      exact ⟨hvs, fun hvgood => (not_lt_of_ge hvgood.2) hvdeg⟩]
  exact hbad

lemma hpGoodRight_compl_lt
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    {s t SP : Finset V} (ht : t.Nonempty)
    (hSP : SP ⊆ s) (hSPsig : ε * (s.card : ℝ) ≤ (SP.card : ℝ))
    (huni : G.IsUniform ε s t) :
    (((t \ hpGoodRight G ε s t SP).card : ℕ) : ℝ) <
      ε * (t.card : ℝ) := by
  have hbad :=
    isUniform_few_low_degree_subset G hε0 hε1 hSP ht hSPsig huni.symm
  rw [show t \ hpGoodRight G ε s t SP =
      t.filter (fun a => ((SP.filter fun b => G.Adj a b).card : ℝ) <
        ((G.edgeDensity t s : ℝ) - ε) * (SP.card : ℝ)) by
    ext v
    simp only [hpGoodRight, Finset.mem_sdiff, Finset.mem_filter]
    constructor
    · rintro ⟨hvt, hvbad⟩
      refine ⟨hvt, lt_of_not_ge fun hvdeg => hvbad ⟨hvt, ?_⟩⟩
      simpa only [SimpleGraph.edgeDensity_comm] using! hvdeg
    · rintro ⟨hvt, hvdeg⟩
      refine ⟨hvt, fun hvgood => (not_lt_of_ge ?_) hvdeg⟩
      simpa only [SimpleGraph.edgeDensity_comm] using! hvgood.2]
  exact hbad

/-- Removing a bad set of real cardinality `< bad` from a set of cardinality
at least `supply`, where `bad + need ≤ supply`, leaves at least `need`
vertices. -/
lemma card_sdiff_ge_of_bad_lt
    {V : Type*} [DecidableEq V] (A B : Finset V)
    (bad supply : ℝ) (need : ℕ)
    (hA : supply ≤ (A.card : ℝ))
    (hB : (B.card : ℝ) < bad)
    (hroom : bad + (need : ℝ) ≤ supply) :
    need ≤ (A \ B).card := by
  have hsplit : A.card ≤ (A \ B).card + B.card := by
    calc
      A.card = (A \ B).card + (A ∩ B).card := by
        rw [card_sdiff_add_card_inter]
      _ ≤ (A \ B).card + B.card :=
        Nat.add_le_add_left (card_le_card inter_subset_right) _
  have hsplitR :
      (A.card : ℝ) ≤ ((A \ B).card : ℝ) + (B.card : ℝ) := by
    exact_mod_cast hsplit
  exact_mod_cast (show (need : ℝ) ≤ ((A \ B).card : ℝ) by linarith)

/-- Candidate sets used in the source proof of Hladký--Piguet Lemma 5.12.
The root is allowed to lie in the prescribed root pool `P'`; every other
vertex lies in one of the two fixed reservoirs. -/
noncomputable def hpRootedCandidates
    {A V : Type*} [Fintype V] [DecidableEq V] [DecidableEq A]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (ε : ℝ) (s t SP SQ P' : Finset V)
    (root : A) (col : A → Bool) (a : A) : Finset V :=
  if a = root then P' ∩ hpGoodLeft G ε s t SQ
  else if col a then SQ ∩ hpGoodRight G ε s t SP
  else SP ∩ hpGoodLeft G ε s t SQ

/-- **Hladký--Piguet Lemma 5.12, prescribed-left-root form.**

`parent/rank` encode a rooted tree (or, equivalently for this lemma, a rooted
forest with the displayed unique root).  `false` is the left colour and `true`
the right colour.  The root is embedded in `P'`; every other vertex is embedded
in `SP ∪ SQ`. -/
theorem hp_rootedTree_embedding_left
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {ε d : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hd1 : d ≤ 1)
    {s t SP SQ P' : Finset V}
    (hs : s.Nonempty) (ht : t.Nonempty)
    (huni : G.IsUniform ε s t)
    (hdens : d ≤ (G.edgeDensity s t : ℝ))
    (hSP : SP ⊆ s) (hSQ : SQ ⊆ t) (hP' : P' ⊆ s)
    (L : ℕ) (hSPcard : SP.card = L) (hSQcard : SQ.card = L)
    (hP'card : L ≤ P'.card)
    (hSPsig : ε * (s.card : ℝ) ≤ (L : ℝ))
    (hSQsig : ε * (t.card : ℝ) ≤ (L : ℝ))
    {A : Type*} [Fintype A] [DecidableEq A]
    (parent : A → Option A) (rank : A → ℕ)
    (hrank : ∀ a b, parent a = some b → rank b < rank a)
    (root : A) (hroot : parent root = none)
    (hroot_unique : ∀ a, parent a = none → a = root)
    (col : A → Bool) (hroot_col : col root = false)
    (hcol : ∀ a b, parent a = some b → col a ≠ col b)
    (hroom :
      ε * (max s.card t.card : ℝ) + (Fintype.card A : ℝ)
        ≤ (d - 2 * ε) * (L : ℝ)) :
    ∃ f : A → V, Function.Injective f ∧
      f root ∈ P' ∧
      (∀ a, a ≠ root →
        f a ∈ (if col a then SQ else SP)) ∧
      (∀ a b, parent a = some b → G.Adj (f a) (f b)) := by
  let goodL := hpGoodLeft G ε s t SQ
  let goodR := hpGoodRight G ε s t SP
  let cand := hpRootedCandidates G ε s t SP SQ P' root col
  have hbadL : (((s \ goodL).card : ℕ) : ℝ) < ε * (s.card : ℝ) := by
    apply hpGoodLeft_compl_lt G hε0 hε1 hs hSQ
    · simpa [hSQcard] using! hSQsig
    · exact huni
  have hbadR : (((t \ goodR).card : ℕ) : ℝ) < ε * (t.card : ℝ) := by
    apply hpGoodRight_compl_lt G hε0 hε1 ht hSP
    · simpa [hSPcard] using! hSPsig
    · exact huni
  have hfactor : d - 2 * ε ≤ 1 := by linarith
  have hLroom :
      ε * (max s.card t.card : ℝ) + (Fintype.card A : ℝ) ≤ (L : ℝ) := by
    calc
      _ ≤ (d - 2 * ε) * (L : ℝ) := hroom
      _ ≤ (L : ℝ) := by
        exact mul_le_of_le_one_left (Nat.cast_nonneg _) hfactor
  have hrootCard : ∀ a, parent a = none → Fintype.card A ≤ (cand a).card := by
    intro a ha
    have har : a = root := hroot_unique a ha
    subst a
    have hsdiff : P' \ (s \ goodL) ⊆ cand root := by
      intro v hv
      have hvP := (mem_sdiff.mp hv).1
      have hvs : v ∈ s := hP' hvP
      have hvGoodL : v ∈ goodL := by
        by_contra h
        exact (mem_sdiff.mp hv).2 (mem_sdiff.mpr ⟨hvs, h⟩)
      have hv' : v ∈ P' ∩ hpGoodLeft G ε s t SQ :=
        Finset.mem_inter.mpr
          ⟨hvP, by simpa only [goodL] using! hvGoodL⟩
      simpa only [cand, hpRootedCandidates, if_pos rfl] using! hv'
    have hremain :
        Fintype.card A ≤ (P' \ (s \ goodL)).card := by
      apply card_sdiff_ge_of_bad_lt P' (s \ goodL)
        (ε * (s.card : ℝ)) (L : ℝ)
      · exact_mod_cast hP'card
      · exact hbadL
      · have hsmax :
            (s.card : ℝ) ≤ max (s.card : ℝ) (t.card : ℝ) :=
          le_max_left _ _
        have hsroom :
            ε * (s.card : ℝ) + (Fintype.card A : ℝ) ≤
              ε * max (s.card : ℝ) (t.card : ℝ) +
                (Fintype.card A : ℝ) := by
          gcongr
        exact hsroom.trans hLroom
    exact hremain.trans (card_le_card hsdiff)
  have hchildCard :
      ∀ a b, parent a = some b → ∀ v ∈ cand b,
        Fintype.card A ≤ ((cand a).filter fun w => G.Adj v w).card := by
    intro a b hab v hv
    have har : a ≠ root := by
      rintro rfl
      rw [hroot] at hab
      cases hab
    have hcolne : col a ≠ col b := hcol a b hab
    have hbGood :
        if col b then v ∈ goodR else v ∈ goodL := by
      by_cases hbr : b = root
      · subst b
        have hcroot : col root = false := hroot_col
        simp only [hcroot, Bool.false_eq_true, if_false]
        have := hv
        simp [cand, hpRootedCandidates, goodL] at this
        exact this.2
      · by_cases hcb : col b
        · simp only [hcb, if_true]
          have := hv
          simp [cand, hpRootedCandidates, hbr, hcb, goodR] at this
          exact this.2
        · simp only [hcb, if_false]
          have := hv
          simp [cand, hpRootedCandidates, hbr, hcb, goodL] at this
          exact this.2
    by_cases hca : col a
    · have hcb : col b = false := by
        cases h : col b <;> simp_all
      have hvdeg :
          ((G.edgeDensity s t : ℝ) - ε) * (L : ℝ) ≤
            ((SQ.filter fun w => G.Adj v w).card : ℝ) := by
        have := hbGood
        simp [hcb, goodL, hpGoodLeft, hSQcard] at this
        exact this.2
      let N := SQ.filter fun w => G.Adj v w
      have hremain :
          Fintype.card A ≤ (N \ (t \ goodR)).card := by
        apply card_sdiff_ge_of_bad_lt N (t \ goodR)
          (ε * (t.card : ℝ))
          (((G.edgeDensity s t : ℝ) - ε) * (L : ℝ))
        · exact hvdeg
        · exact hbadR
        · have hLM : ε * (t.card : ℝ) + (Fintype.card A : ℝ) ≤
              ε * max (s.card : ℝ) (t.card : ℝ) +
                (Fintype.card A : ℝ) := by
            gcongr
            exact le_max_right _ _
          have hlast : (d - 2 * ε) * (L : ℝ) ≤
              ((G.edgeDensity s t : ℝ) - ε) * (L : ℝ) := by
            exact mul_le_mul_of_nonneg_right (by linarith)
              (Nat.cast_nonneg L)
          exact hLM.trans (hroom.trans hlast)
      have hsub :
          N \ (t \ goodR) ⊆ (cand a).filter fun w => G.Adj v w := by
        intro w hw
        have hwN := mem_sdiff.mp hw |>.1
        have hwSQ := mem_filter.mp hwN |>.1
        have hwt : w ∈ t := hSQ hwSQ
        have hwGoodR : w ∈ goodR := by
          by_contra h
          exact (mem_sdiff.mp hw).2 (mem_sdiff.mpr ⟨hwt, h⟩)
        apply Finset.mem_filter.mpr
        refine ⟨?_, (mem_filter.mp hwN).2⟩
        have hw' : w ∈ SQ ∩ hpGoodRight G ε s t SP :=
          Finset.mem_inter.mpr
            ⟨hwSQ, by simpa only [goodR] using! hwGoodR⟩
        simpa only [cand, hpRootedCandidates, if_neg har, if_pos hca] using! hw'
      exact hremain.trans (card_le_card hsub)
    · have hcb : col b = true := by
        cases h : col b <;> simp_all
      have hvdeg :
          ((G.edgeDensity s t : ℝ) - ε) * (L : ℝ) ≤
            ((SP.filter fun w => G.Adj v w).card : ℝ) := by
        have := hbGood
        simp [hcb, goodR, hpGoodRight, hSPcard] at this
        exact this.2
      let N := SP.filter fun w => G.Adj v w
      have hremain :
          Fintype.card A ≤ (N \ (s \ goodL)).card := by
        apply card_sdiff_ge_of_bad_lt N (s \ goodL)
          (ε * (s.card : ℝ))
          (((G.edgeDensity s t : ℝ) - ε) * (L : ℝ))
        · exact hvdeg
        · exact hbadL
        · have hLM : ε * (s.card : ℝ) + (Fintype.card A : ℝ) ≤
              ε * max (s.card : ℝ) (t.card : ℝ) +
                (Fintype.card A : ℝ) := by
            gcongr
            exact le_max_left _ _
          have hlast : (d - 2 * ε) * (L : ℝ) ≤
              ((G.edgeDensity s t : ℝ) - ε) * (L : ℝ) := by
            exact mul_le_mul_of_nonneg_right (by linarith)
              (Nat.cast_nonneg L)
          exact hLM.trans (hroom.trans hlast)
      have hsub :
          N \ (s \ goodL) ⊆ (cand a).filter fun w => G.Adj v w := by
        intro w hw
        have hwN := mem_sdiff.mp hw |>.1
        have hwSP := mem_filter.mp hwN |>.1
        have hws : w ∈ s := hSP hwSP
        have hwGoodL : w ∈ goodL := by
          by_contra h
          exact (mem_sdiff.mp hw).2 (mem_sdiff.mpr ⟨hws, h⟩)
        apply Finset.mem_filter.mpr
        refine ⟨?_, (mem_filter.mp hwN).2⟩
        have hw' : w ∈ SP ∩ hpGoodLeft G ε s t SQ :=
          Finset.mem_inter.mpr
            ⟨hwSP, by simpa only [goodL] using! hwGoodL⟩
        simpa only [cand, hpRootedCandidates, if_neg har, if_neg hca] using! hw'
      exact hremain.trans (card_le_card hsub)
  obtain ⟨f, hfinj, hfmem, hfadj⟩ :=
    candidate_forest_embedding G parent rank hrank cand hrootCard hchildCard
  refine ⟨f, hfinj, ?_, ?_, hfadj⟩
  · have hm := hfmem root
    have hm' : f root ∈ P' ∩ goodL := by
      simpa [cand, hpRootedCandidates] using! hm
    exact (Finset.mem_inter.mp hm').1
  · intro a har
    have hm := hfmem a
    by_cases hca : col a
    · have hm' : f a ∈ SQ ∩ goodR := by
        simpa [cand, hpRootedCandidates, har, hca] using! hm
      simpa [hca] using! (Finset.mem_inter.mp hm').1
    · have hm' : f a ∈ SP ∩ goodL := by
        simpa [cand, hpRootedCandidates, har, hca] using! hm
      simpa [hca] using! (Finset.mem_inter.mp hm').1

/-- Symmetric prescribed-right-root form of Hladký--Piguet Lemma 5.12. -/
theorem hp_rootedTree_embedding_right
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {ε d : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hd1 : d ≤ 1)
    {s t SP SQ Q' : Finset V}
    (hs : s.Nonempty) (ht : t.Nonempty)
    (huni : G.IsUniform ε s t)
    (hdens : d ≤ (G.edgeDensity s t : ℝ))
    (hSP : SP ⊆ s) (hSQ : SQ ⊆ t) (hQ' : Q' ⊆ t)
    (L : ℕ) (hSPcard : SP.card = L) (hSQcard : SQ.card = L)
    (hQ'card : L ≤ Q'.card)
    (hSPsig : ε * (s.card : ℝ) ≤ (L : ℝ))
    (hSQsig : ε * (t.card : ℝ) ≤ (L : ℝ))
    {A : Type*} [Fintype A] [DecidableEq A]
    (parent : A → Option A) (rank : A → ℕ)
    (hrank : ∀ a b, parent a = some b → rank b < rank a)
    (root : A) (hroot : parent root = none)
    (hroot_unique : ∀ a, parent a = none → a = root)
    (col : A → Bool) (hroot_col : col root = true)
    (hcol : ∀ a b, parent a = some b → col a ≠ col b)
    (hroom :
      ε * (max s.card t.card : ℝ) + (Fintype.card A : ℝ)
        ≤ (d - 2 * ε) * (L : ℝ)) :
    ∃ f : A → V, Function.Injective f ∧
      f root ∈ Q' ∧
      (∀ a, a ≠ root →
        f a ∈ (if col a then SQ else SP)) ∧
      (∀ a b, parent a = some b → G.Adj (f a) (f b)) := by
  let col' : A → Bool := fun a => !col a
  have hroot_col' : col' root = false := by
    simp [col', hroot_col]
  have hcol' : ∀ a b, parent a = some b → col' a ≠ col' b := by
    intro a b hab
    have h := hcol a b hab
    cases hca : col a <;> cases hcb : col b <;> simp_all [col']
  obtain ⟨f, hfinj, hfroot, hfside, hfadj⟩ :=
    hp_rootedTree_embedding_left G hε0 hε1 hd1 ht hs huni.symm
      (by simpa only [SimpleGraph.edgeDensity_comm] using! hdens)
      hSQ hSP hQ' L hSQcard hSPcard hQ'card hSQsig hSPsig
      parent rank hrank root hroot hroot_unique col' hroot_col' hcol'
      (by simpa only [max_comm] using! hroom)
  refine ⟨f, hfinj, hfroot, ?_, hfadj⟩
  intro a har
  have h := hfside a har
  by_cases hca : col a
  · have h' : f a ∈ SQ := by simpa [col', hca] using! h
    simpa [hca] using! h'
  · have h' : f a ∈ SP := by simpa [col', hca] using! h
    simpa [hca] using! h'

end Erdos550
