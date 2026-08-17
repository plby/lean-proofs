import ErdosProblems.Erdos780.External.ZpTuckerDefs
import ErdosProblems.Erdos780.External.Erdos780Helpers

open scoped BigOperators

namespace PrimeResolutionScratch

open ZpTuckerScratch Erdos780Scratch

abbrev TuckerAlphaStatement : Prop :=
  ∀ {p n m alpha : ℕ}, p.Prime → alpha ≤ m →
    (lab : NonzeroSignedVector p n → ZMod p × Fin m) →
    IsEquivariant lab → IsAlphaAdmissible alpha lab →
    n ≤ alpha + (m - alpha) * (p - 1)

def support {p n : ℕ} (x : SignedVector p n) : Finset (Fin n) :=
  Finset.univ.filter fun i ↦ x i ≠ none

@[simp] theorem mem_support {p n : ℕ} {x : SignedVector p n} {i : Fin n} :
    i ∈ support x ↔ x i ≠ none := by simp [support]

theorem support_nonempty {p n : ℕ} (x : NonzeroSignedVector p n) :
    (support x.1).Nonempty := by
  obtain ⟨i, hi⟩ := x.2
  exact ⟨i, mem_support.2 hi⟩

def signAt {p n : ℕ} (x : SignedVector p n) (i : Fin n) : ZMod p :=
  (x i).getD 0

theorem some_signAt_of_mem_support {p n : ℕ} {x : SignedVector p n} {i : Fin n}
    (hi : i ∈ support x) : x i = some (signAt x i) := by
  rcases h : x i with _ | a
  · exact (mem_support.1 hi h).elim
  · simp [signAt, h]

@[simp] theorem support_shift {p n : ℕ} (a : ZMod p) (x : SignedVector p n) :
    support (x.shift a) = support x := by
  ext i
  rcases h : x i with _ | b <;> simp [support, SignedVector.shift, h]

theorem signAt_shift_of_mem {p n : ℕ} (a : ZMod p) (x : SignedVector p n)
    {i : Fin n} (hi : i ∈ support x) :
    signAt (x.shift a) i = a + signAt x i := by
  have hx := some_signAt_of_mem_support hi
  change ((x i).map (a + ·)).getD 0 = a + (x i).getD 0
  rw [hx]
  rfl

def Eligible {p n r : ℕ} (x : SignedVector p n) (e : Edge n r) : Prop :=
  ∃ a : ZMod p, ∀ v ∈ e.1, x v = some a

noncomputable def eligibleEdges {p n r : ℕ} (x : SignedVector p n) : Finset (Edge n r) := by
  classical exact Finset.univ.filter (Eligible x)

@[simp] theorem mem_eligibleEdges {p n r : ℕ} {x : SignedVector p n} {e : Edge n r} :
    e ∈ eligibleEdges x ↔ Eligible x e := by simp [eligibleEdges]

theorem eligible_shift_iff {p n r : ℕ} (a : ZMod p) (x : SignedVector p n)
    (e : Edge n r) : Eligible (x.shift a) e ↔ Eligible x e := by
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨-a + b, ?_⟩
    intro v hv
    have h := hb v hv
    rcases hx : x v with _ | g
    · simp [SignedVector.shift, hx] at h
    · simp only [SignedVector.shift, hx, Option.map_some] at h
      have hab : a + g = b := Option.some.inj h
      have hg : g = -a + b := by rw [← hab]; abel
      simpa [hx, hg]
  · rintro ⟨b, hb⟩
    refine ⟨a + b, ?_⟩
    intro v hv
    simp [SignedVector.shift, hb v hv]

@[simp] theorem eligibleEdges_shift {p n r : ℕ} (a : ZMod p)
    (x : SignedVector p n) : eligibleEdges (r := r) (x.shift a) = eligibleEdges x := by
  ext e
  simp [eligible_shift_iff]

noncomputable def signOnSupport {p n : ℕ} (x : SignedVector p n)
    (i : ↑(support x)) : ZMod p := signAt x i.1

theorem signOnSupport_spec {p n : ℕ} (x : SignedVector p n)
    (i : ↑(support x)) : x i.1 = some (signOnSupport x i) :=
  some_signAt_of_mem_support i.2

theorem exists_eligible_of_large_support {p n r : ℕ} (hp : p.Prime)
    (x : SignedVector p n) (hlarge : p * (r - 1) < (support x).card) :
    (eligibleEdges (r := r) x).Nonempty := by
  classical
  letI : NeZero p := ⟨hp.ne_zero⟩
  let f : ↑(support x) → ZMod p := signOnSupport x
  have hmul : Fintype.card (ZMod p) * (r - 1) < Fintype.card ↑(support x) := by
    rw [ZMod.card, Fintype.card_coe]
    exact hlarge
  obtain ⟨a, ha⟩ := Fintype.exists_lt_card_fiber_of_mul_lt_card f hmul
  let F : Finset ↑(support x) := Finset.univ.filter fun i ↦ f i = a
  have hrF : r ≤ F.card := by
    have : r - 1 < F.card := by simpa [F] using ha
    omega
  obtain ⟨S, hSF, hScard⟩ := Finset.exists_subset_card_eq hrF
  let emb : ↑(support x) ↪ Fin n := Function.Embedding.subtype _
  let e : Edge n r := ⟨S.map emb, by simpa [emb] using hScard⟩
  refine ⟨e, mem_eligibleEdges.2 ⟨a, ?_⟩⟩
  intro v hv
  simp only [e, Finset.mem_map] at hv
  obtain ⟨i, hiS, rfl⟩ := hv
  have hiF := hSF hiS
  have hfa : f i = a := by simpa [F] using hiF
  rw [← hfa]
  exact signOnSupport_spec x i

noncomputable local instance edgeLinearOrder (n r : ℕ) : LinearOrder (Edge n r) :=
  (Fintype.equivFin (Edge n r)).linearOrder

noncomputable def chosenEdge {p n r : ℕ} (hp : p.Prime) (x : SignedVector p n)
    (hlarge : p * (r - 1) < (support x).card) : Edge n r :=
  (eligibleEdges (r := r) x).min' (exists_eligible_of_large_support hp x hlarge)

theorem chosenEdge_eligible {p n r : ℕ} (hp : p.Prime) (x : SignedVector p n)
    (hlarge : p * (r - 1) < (support x).card) :
    Eligible x (chosenEdge hp x hlarge) := by
  exact mem_eligibleEdges.1 (Finset.min'_mem _ _)

@[simp] theorem chosenEdge_shift {p n r : ℕ} (hp : p.Prime) (a : ZMod p)
    (x : SignedVector p n) (hlarge : p * (r - 1) < (support x).card) :
    chosenEdge hp (x.shift a) (by simpa using hlarge) = chosenEdge hp x hlarge := by
  simp [chosenEdge]

theorem chosenEdge_nonempty {p n r : ℕ} (hp : p.Prime) (hr : 1 ≤ r)
    (x : SignedVector p n) (hlarge : p * (r - 1) < (support x).card) :
    (chosenEdge hp x hlarge).1.Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro he
  have := (chosenEdge hp x hlarge).2
  rw [he] at this
  simp at this
  omega

theorem edge_nonempty {n r : ℕ} (hr : 1 ≤ r) (e : Edge n r) : e.1.Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro he
  have hc := e.2
  rw [he] at hc
  simp at hc
  omega

noncomputable def edgeVertex {n r : ℕ} (hr : 1 ≤ r) (e : Edge n r) : Fin n :=
  e.1.min' (edge_nonempty hr e)

noncomputable def lowVertex {p n : ℕ} (x : NonzeroSignedVector p n) : Fin n :=
  (support x.1).min' (support_nonempty x)

@[simp] theorem lowVertex_shift {p n : ℕ} (a : ZMod p)
    (x : NonzeroSignedVector p n) : lowVertex (x.shift a) = lowVertex x := by
  simp [lowVertex]

noncomputable def highVertex {p n r : ℕ} (hp : p.Prime) (hr : 1 ≤ r)
    (x : SignedVector p n) (hlarge : p * (r - 1) < (support x).card) : Fin n :=
  edgeVertex hr (chosenEdge hp x hlarge)

theorem highVertex_mem {p n r : ℕ} (hp : p.Prime) (hr : 1 ≤ r)
    (x : SignedVector p n) (hlarge : p * (r - 1) < (support x).card) :
    highVertex hp hr x hlarge ∈ (chosenEdge hp x hlarge).1 := by
  unfold highVertex edgeVertex
  exact Finset.min'_mem _ _

@[simp] theorem highVertex_shift {p n r : ℕ} (hp : p.Prime) (hr : 1 ≤ r)
    (a : ZMod p) (x : SignedVector p n)
    (hlarge : p * (r - 1) < (support x).card) :
    highVertex hp hr (x.shift a) (by simpa using hlarge) = highVertex hp hr x hlarge := by
  unfold highVertex
  exact congrArg (edgeVertex hr) (chosenEdge_shift hp a x hlarge)

theorem chosenEdge_in_label_fiber {p n r : ℕ} (hp : p.Prime) (hr : 1 ≤ r)
    (x : SignedVector p n) (hlarge : p * (r - 1) < (support x).card) :
    ∀ v ∈ (chosenEdge hp x hlarge).1,
      x v = some (signAt x (highVertex hp hr x hlarge)) := by
  obtain ⟨a, ha⟩ := chosenEdge_eligible hp x hlarge
  have hv := ha (highVertex hp hr x hlarge) (highVertex_mem hp hr x hlarge)
  have hsign : signAt x (highVertex hp hr x hlarge) = a := by simp [signAt, hv]
  intro v hve
  simpa [hsign] using ha v hve

noncomputable def primeLabel {p n r t : ℕ} (hp : p.Prime) (hr : 1 ≤ r)
    (ht : 1 ≤ t) (c : Edge n r → Fin t) :
    NonzeroSignedVector p n → ZMod p × Fin (p * (r - 1) + t) := fun x ↦
  if h : (support x.1).card ≤ p * (r - 1) then
    (signAt x.1 (lowVertex x),
      ⟨(support x.1).card - 1, by
        have hpos := (support_nonempty x).card_pos
        omega⟩)
  else
    let hlarge : p * (r - 1) < (support x.1).card := Nat.lt_of_not_ge h
    let e := chosenEdge hp x.1 hlarge
    (signAt x.1 (highVertex hp hr x.1 hlarge),
      ⟨p * (r - 1) + (c e).val, by omega⟩)

theorem primeLabel_equivariant {p n r t : ℕ} (hp : p.Prime) (hr : 1 ≤ r)
    (ht : 1 ≤ t) (c : Edge n r → Fin t) :
    IsEquivariant (primeLabel hp hr ht c) := by
  classical
  intro a x
  by_cases hlow : (support x.1).card ≤ p * (r - 1)
  · have hlow' : (support (x.shift a).1).card ≤ p * (r - 1) := by simpa using hlow
    simp only [primeLabel, dif_pos hlow, dif_pos hlow']
    have hmem : lowVertex x ∈ support x.1 := Finset.min'_mem _ _
    ext
    · simpa using signAt_shift_of_mem a x.1 hmem
    · simp
  · have hlow' : ¬ (support (x.shift a).1).card ≤ p * (r - 1) := by simpa using hlow
    simp only [primeLabel, dif_neg hlow, dif_neg hlow']
    let hlarge : p * (r - 1) < (support x.1).card := Nat.lt_of_not_ge hlow
    have hv_mem : highVertex hp hr x.1 hlarge ∈ support x.1 := by
      apply mem_support.2
      have hv := chosenEdge_in_label_fiber hp hr x.1 hlarge
        (highVertex hp hr x.1 hlarge) (highVertex_mem hp hr x.1 hlarge)
      simpa [hv]
    ext
    · change signAt (x.1.shift a) (highVertex hp hr (x.1.shift a) _) =
          a + signAt x.1 (highVertex hp hr x.1 hlarge)
      rw [highVertex_shift hp hr a x.1 hlarge]
      exact signAt_shift_of_mem a x.1 hv_mem
    · change p * (r - 1) + (c (chosenEdge hp (x.1.shift a) _)).val =
          p * (r - 1) + (c (chosenEdge hp x.1 hlarge)).val
      rw [chosenEdge_shift hp a x.1 hlarge]

theorem le_of_support_eq_of_le {p n : ℕ} {x y : SignedVector p n}
    (hxy : x ≤ y) (hs : support x = support y) : y ≤ x := by
  intro i g hy
  have hiY : i ∈ support y := mem_support.2 (by simp [hy])
  have hiX : i ∈ support x := by simpa [hs] using hiY
  rcases hx : x i with _ | a
  · exact (mem_support.1 hiX hx).elim
  · have := hxy i a hx
    rw [hy] at this
    simpa [hx] using this.symm

theorem primeLabel_admissible {p n r t : ℕ} (hp : p.Prime) (hr : 1 ≤ r)
    (ht : 1 ≤ t) (c : Edge n r → Fin t) (hno : ¬ HasMonoMatching c p) :
    IsAlphaAdmissible (p * (r - 1)) (primeLabel hp hr ht c) := by
  classical
  constructor
  · intro x y hxy hlabel hlow
    have hxlow : (support x.1).card ≤ p * (r - 1) := by
      by_contra hx
      have hxv : p * (r - 1) ≤ ((primeLabel hp hr ht c x).2).val := by
        simp [primeLabel, hx]
      omega
    have hylow : (support y.1).card ≤ p * (r - 1) := by
      by_contra hy
      have hyv : p * (r - 1) ≤ ((primeLabel hp hr ht c y).2).val := by
        simp [primeLabel, hy]
      rw [← hlabel] at hyv
      omega
    have hcards : (support x.1).card = (support y.1).card := by
      have hxpos := (support_nonempty x).card_pos
      have hypos := (support_nonempty y).card_pos
      have hv := congrArg Fin.val hlabel
      simp [primeLabel, hxlow, hylow] at hv
      omega
    have hsxy : support x.1 ⊆ support y.1 := by
      intro i hi
      obtain ⟨g, hg⟩ := Option.ne_none_iff_exists.mp (mem_support.1 hi)
      apply mem_support.2
      have hy := hxy i g hg.symm
      rw [hy]
      simp
    have hs : support x.1 = support y.1 :=
      Finset.eq_of_subset_of_card_le hsxy (by omega)
    have hval : x.1 = y.1 := SignedVector.le_antisymm hxy (le_of_support_eq_of_le hxy hs)
    have hsub : x = y := Subtype.ext hval
    simpa [hsub]
  · intro xs hmono hcommon hsurj
    letI : NeZero p := ⟨hp.ne_zero⟩
    obtain ⟨j, hjhigh, hj⟩ := hcommon
    have hlarge : ∀ i, p * (r - 1) < (support (xs i).1).card := by
      intro i
      by_contra hi
      have hilow : (support (xs i).1).card ≤ p * (r - 1) := by omega
      have hiv : ((primeLabel hp hr ht c (xs i)).2).val < p * (r - 1) := by
        have hpos := (support_nonempty (xs i)).card_pos
        simp [primeLabel, hilow]
        omega
      rw [hj i] at hiv
      omega
    let es : Fin p → Edge n r := fun i ↦ chosenEdge hp (xs i).1 (hlarge i)
    let sig : Fin p → ZMod p := fun i ↦
      signAt (xs i).1 (highVertex hp hr (xs i).1 (hlarge i))
    have hlabel1 : ∀ i, (primeLabel hp hr ht c (xs i)).1 = sig i := by
      intro i
      simp [primeLabel, Nat.not_le.mpr (hlarge i), sig]
    have hsig_surj : Function.Surjective sig := by
      simpa only [hlabel1] using hsurj
    have hsig_inj : Function.Injective sig :=
      ((Fintype.bijective_iff_surjective_and_card sig).2
        ⟨hsig_surj, by simp [ZMod.card]⟩).1
    have hedge_fiber : ∀ i v, v ∈ (es i).1 → (xs i).1 v = some (sig i) := by
      intro i v hv
      exact chosenEdge_in_label_fiber hp hr (xs i).1 (hlarge i) v hv
    have hp0 : 0 < p := hp.pos
    let lastP : Fin p := ⟨p - 1, by omega⟩
    have hedge_terminal : ∀ i v, v ∈ (es i).1 →
        (xs lastP).1 v = some (sig i) := by
      intro i v hv
      apply hmono (show i ≤ lastP by apply Fin.le_def.mpr; dsimp [lastP]; omega)
      exact hedge_fiber i v hv
    have hdisj : ∀ i k : Fin p, i ≠ k → Disjoint (es i).1 (es k).1 := by
      intro i k hik
      rw [Finset.disjoint_left]
      intro v hvi hvk
      have hi := hedge_terminal i v hvi
      have hk := hedge_terminal k v hvk
      have : sig i = sig k := Option.some.inj (hi.symm.trans hk)
      exact hik (hsig_inj this)
    have hjlt : j.val < p * (r - 1) + t := j.isLt
    have hcolor_lt : j.val - p * (r - 1) < t := by omega
    let color : Fin t := ⟨j.val - p * (r - 1), hcolor_lt⟩
    have hcolor : ∀ i, c (es i) = color := by
      intro i
      have hv : p * (r - 1) + (c (es i)).val = j.val := by
        simpa [primeLabel, Nat.not_le.mpr (hlarge i), es] using congrArg Fin.val (hj i)
      apply Fin.ext
      change (c (es i)).val = j.val - p * (r - 1)
      omega
    apply hno
    refine ⟨color, es, hcolor, hdisj⟩

theorem primeResolution (tucker : TuckerAlphaStatement) {p : ℕ} :
    p.Prime → ResolutionStatement p := by
  intro hp n r t hr ht hn c
  by_contra hno
  let alpha := p * (r - 1)
  let m := alpha + t
  let lab := primeLabel hp hr ht c
  have hbound : n ≤ alpha + (m - alpha) * (p - 1) :=
    tucker hp (by simp [m]) lab
      (primeLabel_equivariant hp hr ht c)
      (primeLabel_admissible hp hr ht c hno)
  have hr' : r - 1 + 1 = r := Nat.sub_add_cancel hr
  have hp1 : 1 ≤ p := hp.one_le
  have hp' : p - 1 + 1 = p := Nat.sub_add_cancel hp1
  have ht' : t - 1 + 1 = t := Nat.sub_add_cancel ht
  dsimp [alpha, m] at hbound
  simp only [Nat.add_sub_cancel_left] at hbound
  nlinarith

#check primeResolution
#print axioms primeResolution

end PrimeResolutionScratch
