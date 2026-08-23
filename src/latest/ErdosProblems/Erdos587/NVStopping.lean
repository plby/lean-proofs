/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib

namespace Erdos587

def nvFirstUsed {α β : Type*} [DecidableEq α] :
    List (Finset α × Finset β) → Finset α
  | [] => ∅
  | c :: cs => c.1 ∪ nvFirstUsed cs

def nvSecondUsed {α β : Type*} [DecidableEq β] :
    List (Finset α × Finset β) → Finset β
  | [] => ∅
  | c :: cs => c.2 ∪ nvSecondUsed cs

def NVResourceDisjoint {α β : Type*} [DecidableEq α] [DecidableEq β]
    (c d : Finset α × Finset β) : Prop :=
  Disjoint c.1 d.1 ∧ Disjoint c.2 d.2

lemma mem_nvFirstUsed_iff {α β : Type*} [DecidableEq α]
    {x : α} {cs : List (Finset α × Finset β)} :
    x ∈ nvFirstUsed cs ↔ ∃ c ∈ cs, x ∈ c.1 := by
  induction cs with
  | nil => simp [nvFirstUsed]
  | cons c cs ih => simp [nvFirstUsed, ih]

lemma mem_nvSecondUsed_iff {α β : Type*} [DecidableEq β]
    {x : β} {cs : List (Finset α × Finset β)} :
    x ∈ nvSecondUsed cs ↔ ∃ c ∈ cs, x ∈ c.2 := by
  induction cs with
  | nil => simp [nvSecondUsed]
  | cons c cs ih => simp [nvSecondUsed, ih]

/-- Greedy finite packing used in each Nguyen--Vu generation.  Every choice
consumes two family indices and `h` translating elements.  The final greedy
weight bounds every choice supported on resources left after all selections.
This is the formal maximality invariant behind equation (11) of Nguyen--Vu. -/
theorem exists_nvGreedy_resource_choices
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (w : (Finset α × Finset β) → ℕ)
    (I : Finset α) (R : Finset β) (h n : ℕ)
    (hI : 2 * (n + 1) ≤ I.card)
    (hR : h * (n + 1) ≤ R.card) :
    ∃ cs : List (Finset α × Finset β), ∃ b : ℕ,
      cs.length = n + 1 ∧
      (∀ c ∈ cs,
        c.1 ⊆ I ∧ c.1.card = 2 ∧
        c.2 ⊆ R ∧ c.2.card = h) ∧
      cs.Pairwise NVResourceDisjoint ∧
      (∀ c ∈ cs, b ≤ w c) ∧
      (∃ c ∈ cs, w c = b) ∧
      (∀ p ⊆ I, p.card = 2 →
        ∀ T ⊆ R, T.card = h →
          Disjoint p (nvFirstUsed cs) →
          Disjoint T (nvSecondUsed cs) →
          w (p, T) ≤ b) := by
  induction n generalizing I R with
  | zero =>
      have hI2 : 2 ≤ I.card := by simpa using hI
      have hRh : h ≤ R.card := by simpa using hR
      obtain ⟨p, hpI, hpcard⟩ := Finset.exists_subset_card_eq hI2
      obtain ⟨T, hTR, hTcard⟩ := Finset.exists_subset_card_eq hRh
      let C := (I.powersetCard 2).product (R.powersetCard h)
      have hC : C.Nonempty := by
        exact ⟨(p, T), Finset.mem_product.mpr
          ⟨Finset.mem_powersetCard.mpr ⟨hpI, hpcard⟩,
            Finset.mem_powersetCard.mpr ⟨hTR, hTcard⟩⟩⟩
      obtain ⟨c, hcC, hcmax⟩ := Finset.exists_max_image C w hC
      have hc := Finset.mem_product.mp hcC
      have hcp := Finset.mem_powersetCard.mp hc.1
      have hcT := Finset.mem_powersetCard.mp hc.2
      refine ⟨[c], w c, by simp, ?_, by simp [NVResourceDisjoint],
        by simp, ⟨c, by simp⟩, ?_⟩
      · intro d hd
        have hdc : d = c := by simpa using hd
        subst d
        exact ⟨hcp.1, hcp.2, hcT.1, hcT.2⟩
      · intro p hpI hpcard T hTR hTcard _hpd _hTd
        apply hcmax (p, T)
        exact Finset.mem_product.mpr
          ⟨Finset.mem_powersetCard.mpr ⟨hpI, hpcard⟩,
            Finset.mem_powersetCard.mpr ⟨hTR, hTcard⟩⟩
  | succ n ih =>
      have hI2 : 2 ≤ I.card := by omega
      have hRh : h ≤ R.card := by
        have : h ≤ h * (n + 2) := Nat.le_mul_of_pos_right h (by omega)
        exact this.trans hR
      obtain ⟨p, hpI, hpcard⟩ := Finset.exists_subset_card_eq hI2
      obtain ⟨T, hTR, hTcard⟩ := Finset.exists_subset_card_eq hRh
      let C := (I.powersetCard 2).product (R.powersetCard h)
      have hC : C.Nonempty := by
        exact ⟨(p, T), Finset.mem_product.mpr
          ⟨Finset.mem_powersetCard.mpr ⟨hpI, hpcard⟩,
            Finset.mem_powersetCard.mpr ⟨hTR, hTcard⟩⟩⟩
      obtain ⟨c, hcC, hcmax⟩ := Finset.exists_max_image C w hC
      have hc := Finset.mem_product.mp hcC
      have hcp := Finset.mem_powersetCard.mp hc.1
      have hcT := Finset.mem_powersetCard.mp hc.2
      let I' := I \ c.1
      let R' := R \ c.2
      have hIcard : I'.card = I.card - 2 := by
        dsimp only [I']
        rw [Finset.card_sdiff_of_subset hcp.1, hcp.2]
      have hRcard : R'.card = R.card - h := by
        dsimp only [R']
        rw [Finset.card_sdiff_of_subset hcT.1, hcT.2]
      have hI' : 2 * (n + 1) ≤ I'.card := by
        rw [hIcard]
        omega
      have hR' : h * (n + 1) ≤ R'.card := by
        rw [hRcard]
        apply Nat.le_sub_of_add_le
        calc
          h * (n + 1) + h = h * (n + 2) := by ring
          _ ≤ R.card := hR
      obtain ⟨cs, b, hlen, hspec, hpair, hb, hbeq, hterminal⟩ :=
        ih I' R' hI' hR'
      have hcsFirst : ∀ d ∈ cs, Disjoint c.1 d.1 := by
        intro d hd
        have hdsub := (hspec d hd).1
        rw [Finset.disjoint_left]
        intro x hxc hxd
        exact (Finset.mem_sdiff.mp (hdsub hxd)).2 hxc
      have hcsSecond : ∀ d ∈ cs, Disjoint c.2 d.2 := by
        intro d hd
        have hdsub := (hspec d hd).2.2.1
        rw [Finset.disjoint_left]
        intro x hxc hxd
        exact (Finset.mem_sdiff.mp (hdsub hxd)).2 hxc
      have hc_ge_b : b ≤ w c := by
        obtain ⟨d, hd, hwd⟩ := hbeq
        have hdI : d.1 ⊆ I := (hspec d hd).1.trans Finset.sdiff_subset
        have hdR : d.2 ⊆ R :=
          (hspec d hd).2.2.1.trans Finset.sdiff_subset
        have hdC : d ∈ C := Finset.mem_product.mpr
          ⟨Finset.mem_powersetCard.mpr ⟨hdI, (hspec d hd).2.1⟩,
            Finset.mem_powersetCard.mpr
              ⟨hdR, (hspec d hd).2.2.2⟩⟩
        rw [← hwd]
        exact hcmax d hdC
      refine ⟨c :: cs, b, by simp [hlen], ?_, ?_, ?_, ?_, ?_⟩
      · intro d hd
        rw [List.mem_cons] at hd
        rcases hd with rfl | hd
        · exact ⟨hcp.1, hcp.2, hcT.1, hcT.2⟩
        · have hs := hspec d hd
          exact ⟨hs.1.trans Finset.sdiff_subset, hs.2.1,
            hs.2.2.1.trans Finset.sdiff_subset, hs.2.2.2⟩
      · rw [List.pairwise_cons]
        exact ⟨fun d hd => ⟨hcsFirst d hd, hcsSecond d hd⟩, hpair⟩
      · intro d hd
        rw [List.mem_cons] at hd
        rcases hd with rfl | hd
        · exact hc_ge_b
        · exact hb d hd
      · obtain ⟨d, hd, hwd⟩ := hbeq
        exact ⟨d, by simp [hd], hwd⟩
      · intro p hpI hpcard T hTR hTcard hpdis hTdis
        have hpdisParts :
            Disjoint p c.1 ∧ Disjoint p (nvFirstUsed cs) := by
          simpa [nvFirstUsed, Finset.disjoint_union_right] using hpdis
        have hTdisParts :
            Disjoint T c.2 ∧ Disjoint T (nvSecondUsed cs) := by
          simpa [nvSecondUsed, Finset.disjoint_union_right] using hTdis
        have hpI' : p ⊆ I' := by
          intro x hx
          exact Finset.mem_sdiff.mpr
            ⟨hpI hx, Finset.disjoint_left.mp hpdisParts.1 hx⟩
        have hTR' : T ⊆ R' := by
          intro x hx
          exact Finset.mem_sdiff.mpr
            ⟨hTR hx, Finset.disjoint_left.mp hTdisParts.1 hx⟩
        exact hterminal p hpI' hpcard T hTR' hTcard
          hpdisParts.2 hTdisParts.2

end Erdos587
