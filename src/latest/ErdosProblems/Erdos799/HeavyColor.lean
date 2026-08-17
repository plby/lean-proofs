import ErdosProblems.Erdos753
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Order.Preorder.Finite

open Finset

namespace Erdos799

open Erdos753

/-!
# The heavy-colour reduction

This file proves the deterministic list-colouring lemma used in the solution of
Erdős Problem 799.  If every vertex set of size at least `M` contains an
independent `q`-set, then `G` is `(|V| / q + M)`-choosable.
-/

private def IsHeavyPacking {V : Type*} (G : SimpleGraph V) (q : ℕ)
    (L : V → Finset ℕ) (P : Finset (ℕ × Finset V)) : Prop :=
  (∀ b ∈ P, b.2.card = q ∧ G.IsIndepSet (b.2 : Set V) ∧
      ∀ v ∈ b.2, b.1 ∈ L v) ∧
    Set.InjOn Prod.fst (P : Set (ℕ × Finset V)) ∧
    (P : Set (ℕ × Finset V)).PairwiseDisjoint Prod.snd

private noncomputable def packingUniverse {V : Type*} [Fintype V]
    (L : V → Finset ℕ) : Finset (ℕ × Finset V) := by
  classical
  exact (Finset.univ.biUnion L).product Finset.univ

private noncomputable def heavyPackings {V : Type*} [Fintype V]
    (G : SimpleGraph V) (q : ℕ) (L : V → Finset ℕ) :
    Finset (Finset (ℕ × Finset V)) := by
  classical
  exact (packingUniverse L).powerset.filter (IsHeavyPacking G q L)

/-- Hall's condition follows if every list has at least `M` colours and every
colour occurs in fewer than `M` lists. -/
lemma hall_of_lower_list_size_of_upper_frequency
    {A : Type*} [Fintype A] {M : ℕ} (L : A → Finset ℕ)
    (hM : 0 < M)
    (hsize : ∀ a, M ≤ (L a).card)
    (hfreq : ∀ c, (Finset.univ.filter fun a => c ∈ L a).card < M) :
    ∃ f : A → ℕ, Function.Injective f ∧ ∀ a, f a ∈ L a := by
  rw [← Finset.all_card_le_biUnion_card_iff_exists_injective L]
  intro s
  let C := s.biUnion L
  have hdouble :
      ∑ a ∈ s, (L a).card =
        ∑ c ∈ C, (s.filter fun a => c ∈ L a).card := by
    calc
      ∑ a ∈ s, (L a).card =
          ∑ a ∈ s, ∑ c ∈ C, if c ∈ L a then 1 else 0 := by
            apply Finset.sum_congr rfl
            intro a ha
            have hsub : L a ⊆ C := by
              exact Finset.subset_biUnion_of_mem L ha
            have hfilter : C.filter (fun c => c ∈ L a) = L a := by
              ext c
              simp only [Finset.mem_filter]
              aesop
            rw [← Finset.sum_filter]
            rw [hfilter]
            simp
      _ = ∑ c ∈ C, ∑ a ∈ s, if c ∈ L a then 1 else 0 := by
            rw [Finset.sum_comm]
      _ = ∑ c ∈ C, (s.filter fun a => c ∈ L a).card := by
            apply Finset.sum_congr rfl
            intro c _
            rw [← Finset.sum_filter]
            simp
  have hlower : M * s.card ≤ ∑ a ∈ s, (L a).card := by
    calc
      M * s.card = ∑ a ∈ s, M := by simp [Nat.mul_comm]
      _ ≤ ∑ a ∈ s, (L a).card :=
        Finset.sum_le_sum fun a _ => hsize a
  have hupper :
      ∑ c ∈ C, (s.filter fun a => c ∈ L a).card ≤ (M - 1) * C.card := by
    calc
      ∑ c ∈ C, (s.filter fun a => c ∈ L a).card ≤
          ∑ c ∈ C, (M - 1) := by
            exact Finset.sum_le_sum fun c _ => by
              have hsub : (s.filter fun a => c ∈ L a) ⊆
                  (Finset.univ.filter fun a => c ∈ L a) := by
                intro a ha
                simp only [Finset.mem_filter] at ha ⊢
                exact ⟨Finset.mem_univ _, ha.2⟩
              have := (Finset.card_le_card hsub).trans_lt (hfreq c)
              omega
      _ = (M - 1) * C.card := by simp [Nat.mul_comm]
  by_contra hnot
  change ¬ s.card ≤ C.card at hnot
  have hcard : C.card < s.card := Nat.lt_of_not_ge hnot
  have hstrict : (M - 1) * C.card < M * s.card := by
    calc
      (M - 1) * C.card ≤ (M - 1) * s.card :=
        Nat.mul_le_mul_left _ hcard.le
      _ < M * s.card := by
        exact (Nat.mul_lt_mul_right (by omega : 0 < s.card)).2 (by omega)
  have hle : M * s.card ≤ (M - 1) * C.card :=
    hlower.trans (hdouble.le.trans hupper)
  exact (not_lt_of_ge hle) hstrict

/-- If every set of at least `M` vertices contains an independent set of
cardinality `q > 0`, then `G` is `(|V| / q + M)`-choosable.

The proof first chooses a maximal packing of pairwise disjoint independent
`q`-sets, each supported by a different colour.  Every unused colour then
occurs on fewer than `M` residual vertices.  A double-counting proof of Hall's
condition supplies distinct representatives for the residual lists. -/
theorem isKChoosable_of_independent_subset
    {V : Type*} [Fintype V] (G : SimpleGraph V) (q M : ℕ)
    (hq : 0 < q)
    (hind : ∀ S : Finset V, M ≤ S.card →
      ∃ I : Finset V, I ⊆ S ∧ I.card = q ∧ G.IsIndepSet (I : Set V)) :
    IsKChoosable G (Fintype.card V / q + M) := by
  classical
  have hM : 0 < M := by
    by_contra hnot
    have hMzero : M = 0 := Nat.eq_zero_of_not_pos hnot
    obtain ⟨I, hIsub, hIcard, _⟩ := hind ∅ (by simp [hMzero])
    have hIle : I.card ≤ 0 := by
      simpa using Finset.card_le_card hIsub
    omega
  intro L hL
  let packs := heavyPackings G q L
  have hpacks : packs.Nonempty := by
    refine ⟨∅, ?_⟩
    simp [packs, heavyPackings, packingUniverse, IsHeavyPacking]
  obtain ⟨P, hPmax⟩ := packs.exists_maximal hpacks
  have hP : IsHeavyPacking G q L P := by
    exact (Finset.mem_filter.mp hPmax.1).2
  let used : Finset ℕ := P.image Prod.fst
  let covered : Finset V := P.biUnion Prod.snd
  let R : Finset V := Finset.univ \ covered
  have hused_card : used.card = P.card := by
    apply Finset.card_image_iff.mpr
    exact hP.2.1
  have hcovered_card : covered.card = P.card * q := by
    dsimp [covered]
    rw [Finset.card_biUnion hP.2.2]
    calc
      ∑ x ∈ P, #x.2 = ∑ _x ∈ P, q := by
        exact Finset.sum_congr rfl fun x hx => (hP.1 x hx).1
      _ = P.card * q := by simp
  have hPcard : P.card ≤ Fintype.card V / q := by
    rw [Nat.le_div_iff_mul_le hq]
    rw [← hcovered_card]
    exact Finset.card_le_univ covered
  have hfreq : ∀ c, c ∉ used →
      (R.filter fun v => c ∈ L v).card < M := by
    intro c hc
    by_contra hnot
    have hlarge : M ≤ (R.filter fun v => c ∈ L v).card :=
      Nat.le_of_not_gt hnot
    obtain ⟨I, hIsub, hIcard, hIind⟩ := hind _ hlarge
    have hInonempty : I.Nonempty := Finset.card_pos.mp (hIcard.symm ▸ hq)
    obtain ⟨v, hvI⟩ := hInonempty
    have hvc : c ∈ L v := (Finset.mem_filter.mp (hIsub hvI)).2
    have hcColors : c ∈ Finset.univ.biUnion L := by
      exact Finset.mem_biUnion.mpr ⟨v, Finset.mem_univ _, hvc⟩
    let b : ℕ × Finset V := (c, I)
    have hbUniverse : b ∈ packingUniverse L := by
      simp [b, packingUniverse, hcColors]
    have hbP : b ∉ P := by
      intro hb
      apply hc
      exact Finset.mem_image.mpr ⟨b, hb, rfl⟩
    have hbDisjoint : ∀ a ∈ P, Disjoint I a.2 := by
      intro a ha
      rw [Finset.disjoint_left]
      intro x hxI hxa
      have hxR := Finset.mem_filter.mp (hIsub hxI) |>.1
      have hxCovered : x ∈ covered := Finset.mem_biUnion.mpr ⟨a, ha, hxa⟩
      exact (Finset.mem_sdiff.mp hxR).2 hxCovered
    have hPackInsert : IsHeavyPacking G q L (insert b P) := by
      refine ⟨?_, ?_, ?_⟩
      · intro a ha
        simp only [Finset.mem_insert] at ha
        rcases ha with rfl | ha
        · exact ⟨hIcard, hIind, fun x hx =>
            (Finset.mem_filter.mp (hIsub hx)).2⟩
        · exact hP.1 a ha
      · intro a ha a' ha' heq
        simp only [Finset.coe_insert, Set.mem_insert_iff] at ha ha'
        rcases ha with rfl | ha <;> rcases ha' with rfl | ha'
        · rfl
        · apply False.elim
          apply hc
          exact Finset.mem_image.mpr ⟨a', ha', by simpa [b] using heq.symm⟩
        · apply False.elim
          apply hc
          exact Finset.mem_image.mpr ⟨a, ha, by simpa [b] using heq⟩
        · exact hP.2.1 ha ha' heq
      · intro a ha a' ha' hne
        simp only [Finset.coe_insert, Set.mem_insert_iff] at ha ha'
        rcases ha with rfl | ha <;> rcases ha' with rfl | ha'
        · exact False.elim (hne rfl)
        · exact hbDisjoint a' ha'
        · exact (hbDisjoint a ha).symm
        · exact hP.2.2 ha ha' hne
    have hInsertPacks : insert b P ∈ packs := by
      apply Finset.mem_filter.mpr
      refine ⟨?_, hPackInsert⟩
      apply Finset.mem_powerset.mpr
      intro a ha
      simp only [Finset.mem_insert] at ha
      rcases ha with rfl | ha
      · exact hbUniverse
      · exact (Finset.mem_powerset.mp (Finset.mem_filter.mp hPmax.1).1) ha
    have hle := hPmax.2 hInsertPacks (Finset.subset_insert b P)
    exact hbP (hle (Finset.mem_insert_self b P))
  let RV := {v : V // v ∈ R}
  let Lr : RV → Finset ℕ := fun v => L v.1 \ used
  have hLrsize : ∀ v, M ≤ (Lr v).card := by
    intro v
    have hdiff := Finset.le_card_sdiff used (L v.1)
    rw [hL v.1, hused_card] at hdiff
    dsimp [Lr]
    omega
  have hLrfreq : ∀ c,
      (Finset.univ.filter fun v : RV => c ∈ Lr v).card < M := by
    intro c
    by_cases hc : c ∈ used
    · have hempty : (Finset.univ.filter fun v : RV => c ∈ Lr v) = ∅ := by
        ext v
        simp [Lr, hc]
      simp [hempty, hM]
    · let e : RV ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
      have heq : (Finset.univ.filter fun v : RV => c ∈ Lr v).map e =
          R.filter fun v => c ∈ L v := by
        ext v
        simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨a, ha, rfl⟩
          dsimp [Lr] at ha
          exact ⟨a.property, (Finset.mem_sdiff.mp ha).1⟩
        · rintro ⟨hvR, hcv⟩
          refine ⟨⟨v, hvR⟩, ?_, rfl⟩
          dsimp [Lr]
          exact Finset.mem_sdiff.mpr ⟨hcv, hc⟩
      have hh := hfreq c hc
      rw [← heq, Finset.card_map] at hh
      exact hh
  obtain ⟨f, hf_inj, hf_mem⟩ :=
    hall_of_lower_list_size_of_upper_frequency Lr hM hLrsize hLrfreq
  have hblock_exists : ∀ v ∈ covered, ∃ b ∈ P, v ∈ b.2 := by
    intro v hv
    exact Finset.mem_biUnion.mp hv
  choose block hblockP hblockV using hblock_exists
  let packedColor (v : {v : V // v ∈ covered}) : ℕ := (block v.1 v.2).1
  have hpacked_mem (v : {v : V // v ∈ covered}) : packedColor v ∈ L v.1 := by
    exact (hP.1 (block v.1 v.2) (hblockP v.1 v.2)).2.2 v.1
      (hblockV v.1 v.2)
  have hnotR_covered : ∀ v, v ∉ R → v ∈ covered := by
    intro v hv
    simpa [R] using hv
  let color (v : V) : ℕ :=
    if hv : v ∈ R then f ⟨v, hv⟩
    else packedColor ⟨v, hnotR_covered v hv⟩
  have hcolor_mem : ∀ v, color v ∈ L v := by
    intro v
    simp only [color]
    split
    · exact (Finset.mem_sdiff.mp (hf_mem _)).1
    · exact hpacked_mem _
  have hpacked_used (v : {v : V // v ∈ covered}) : packedColor v ∈ used := by
    apply Finset.mem_image.mpr
    exact ⟨block v.1 v.2, hblockP v.1 v.2, rfl⟩
  have hpacked_ne_of_adj (u v : {v : V // v ∈ covered})
      (hadj : G.Adj u.1 v.1) : packedColor u ≠ packedColor v := by
    intro heq
    have hblockeq : block u.1 u.2 = block v.1 v.2 :=
      hP.2.1 (hblockP u.1 u.2) (hblockP v.1 v.2) heq
    have hvMem : v.1 ∈ (block u.1 u.2).2 := by
      rw [hblockeq]
      exact hblockV v.1 v.2
    have hindBlock := (hP.1 (block u.1 u.2) (hblockP u.1 u.2)).2.1
    have hnotadj := (G.isIndepSet_iff.mp hindBlock)
      (hblockV u.1 u.2) hvMem hadj.ne
    exact hnotadj hadj
  refine ⟨SimpleGraph.Coloring.mk color (fun {u v} hadj => ?_), hcolor_mem⟩
  intro heq
  by_cases hu : u ∈ R <;> by_cases hv : v ∈ R
  · have huv : f ⟨u, hu⟩ = f ⟨v, hv⟩ := by
      simpa [color, hu, hv] using heq
    have hsubeq : (⟨u, hu⟩ : RV) = ⟨v, hv⟩ := hf_inj huv
    exact hadj.ne (congrArg Subtype.val hsubeq)
  · have huv : f ⟨u, hu⟩ = packedColor ⟨v, hnotR_covered v hv⟩ := by
      simpa [color, hu, hv] using heq
    have hunused : f ⟨u, hu⟩ ∉ used := (Finset.mem_sdiff.mp (hf_mem ⟨u, hu⟩)).2
    exact hunused (huv ▸ hpacked_used ⟨v, hnotR_covered v hv⟩)
  · have huv : packedColor ⟨u, hnotR_covered u hu⟩ = f ⟨v, hv⟩ := by
      simpa [color, hu, hv] using heq
    have hunused : f ⟨v, hv⟩ ∉ used := (Finset.mem_sdiff.mp (hf_mem ⟨v, hv⟩)).2
    exact hunused (huv ▸ hpacked_used ⟨u, hnotR_covered u hu⟩)
  · apply hpacked_ne_of_adj ⟨u, hnotR_covered u hu⟩
        ⟨v, hnotR_covered v hv⟩ hadj
    simpa [color, hu, hv] using heq

end Erdos799
