import Mathlib

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos336

open scoped Pointwise

variable {H : Type*} [AddCommGroup H] [DecidableEq H]

/-- The fibre of a finite subset of `ℤ × H` above an integer. -/
def integerFiber (A : Finset (ℤ × H)) (z : ℤ) : Finset (ℤ × H) :=
  A.filter fun x => x.1 = z

@[simp] theorem mem_integerFiber {A : Finset (ℤ × H)} {z : ℤ} {x : ℤ × H} :
    x ∈ integerFiber A z ↔ x ∈ A ∧ x.1 = z := by
  simp [integerFiber]

/-- Endpoint fibres and all intermediate occupied fibres give three disjoint
regions in the double sumset.  This is the disjointness core of Lev's basic
endpoint estimate. -/
theorem endpoint_fiber_three_region_bound
    (A : Finset (ℤ × H)) (l : ℤ) (hlpos : 0 < l)
    (h0 : 0 ∈ A.image Prod.fst) (hl : l ∈ A.image Prod.fst)
    (hbounds : ∀ z ∈ A.image Prod.fst, 0 ≤ z ∧ z ≤ l) :
    ((A.image Prod.fst).card - 1) * (integerFiber A 0).card +
        (integerFiber A 0 + integerFiber A l).card +
        ((A.image Prod.fst).card - 1) * (integerFiber A l).card ≤
      (A + A).card := by
  let P : Finset ℤ := A.image Prod.fst
  let A0 : Finset (ℤ × H) := integerFiber A 0
  let Al : Finset (ℤ × H) := integerFiber A l
  let rep : (z : ℤ) → z ∈ P → ℤ × H := fun z hz =>
    (Finset.mem_image.mp hz).choose
  have hrepA (z : ℤ) (hz : z ∈ P) : rep z hz ∈ A :=
    (Finset.mem_image.mp hz).choose_spec.1
  have hrepfst (z : ℤ) (hz : z ∈ P) : (rep z hz).1 = z :=
    (Finset.mem_image.mp hz).choose_spec.2
  have hA0A {x : ℤ × H} (hx : x ∈ A0) : x ∈ A :=
    (mem_integerFiber.mp hx).1
  have hAlA {x : ℤ × H} (hx : x ∈ Al) : x ∈ A :=
    (mem_integerFiber.mp hx).1
  have hA0fst {x : ℤ × H} (hx : x ∈ A0) : x.1 = 0 :=
    (mem_integerFiber.mp hx).2
  have hAlfst {x : ℤ × H} (hx : x ∈ Al) : x.1 = l :=
    (mem_integerFiber.mp hx).2
  let DL := ↥(P.erase l) × ↥A0
  let DC := ↥(A0 + Al)
  let DR := ↥(P.erase 0) × ↥Al
  let D := (DL ⊕ DC) ⊕ DR
  let e : D → ↥(A + A) := fun u =>
    match u with
    | Sum.inl (Sum.inl p) =>
        let z : ℤ := p.1.1
        let hzP : z ∈ P := Finset.mem_of_mem_erase p.1.2
        ⟨rep z hzP + p.2.1,
          Finset.mem_add.mpr ⟨rep z hzP, hrepA z hzP,
            p.2.1, hA0A p.2.2, rfl⟩⟩
    | Sum.inl (Sum.inr c) =>
        ⟨c.1, Finset.add_subset_add
          (fun _ hx => hA0A hx) (fun _ hx => hAlA hx) c.2⟩
    | Sum.inr p =>
        let z : ℤ := p.1.1
        let hzP : z ∈ P := Finset.mem_of_mem_erase p.1.2
        ⟨rep z hzP + p.2.1,
          Finset.mem_add.mpr ⟨rep z hzP, hrepA z hzP,
            p.2.1, hAlA p.2.2, rfl⟩⟩
  have hleftfst (p : DL) :
      (e (Sum.inl (Sum.inl p))).1.1 = p.1.1 := by
    let hzP : p.1.1 ∈ P := Finset.mem_of_mem_erase p.1.2
    change (rep p.1.1 hzP).1 + p.2.1.1 = p.1.1
    rw [hrepfst p.1.1 hzP, hA0fst p.2.2]
    simp
  have hcenterfst (c : DC) :
      (e (Sum.inl (Sum.inr c))).1.1 = l := by
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.mem_add.mp c.2
    simp only [e]
    rw [← hxy, Prod.fst_add, hA0fst hx, hAlfst hy]
    simp
  have hrightfst (p : DR) :
      (e (Sum.inr p)).1.1 = p.1.1 + l := by
    let hzP : p.1.1 ∈ P := Finset.mem_of_mem_erase p.1.2
    change (rep p.1.1 hzP).1 + p.2.1.1 = p.1.1 + l
    rw [hrepfst p.1.1 hzP, hAlfst p.2.2]
  have hleftlt (p : DL) : p.1.1 < l := by
    have hzP : p.1.1 ∈ P := Finset.mem_of_mem_erase p.1.2
    have hzle := (hbounds p.1.1 (by simpa [P] using hzP)).2
    have hzne : p.1.1 ≠ l := (Finset.mem_erase.mp p.1.2).1
    omega
  have hrightpos (p : DR) : 0 < p.1.1 := by
    have hzP : p.1.1 ∈ P := Finset.mem_of_mem_erase p.1.2
    have hz0 := (hbounds p.1.1 (by simpa [P] using hzP)).1
    have hzne : p.1.1 ≠ 0 := (Finset.mem_erase.mp p.1.2).1
    omega
  have hleftinj : Function.Injective
      (fun p : DL => e (Sum.inl (Sum.inl p))) := by
    intro u v huv
    have hfst : u.1.1 = v.1.1 := by
      rw [← hleftfst u, ← hleftfst v]
      exact congrArg (fun x => x.1.1) huv
    have hidx : u.1 = v.1 := Subtype.ext hfst
    have hsum := congrArg Subtype.val huv
    change rep u.1.1 (Finset.mem_of_mem_erase u.1.2) + u.2.1 =
      rep v.1.1 (Finset.mem_of_mem_erase v.1.2) + v.2.1 at hsum
    have hrepEq : rep u.1.1 (Finset.mem_of_mem_erase u.1.2) =
        rep v.1.1 (Finset.mem_of_mem_erase v.1.2) :=
      congrArg (fun z : ↥(P.erase l) =>
        rep z.1 (Finset.mem_of_mem_erase z.2)) hidx
    rw [hrepEq] at hsum
    have hval : u.2.1 = v.2.1 := add_left_cancel hsum
    exact Prod.ext hidx (Subtype.ext hval)
  have hcenterinj : Function.Injective
      (fun c : DC => e (Sum.inl (Sum.inr c))) := by
    intro u v huv
    apply Subtype.ext
    have h := congrArg Subtype.val huv
    simpa [e] using h
  have hrightinj : Function.Injective (fun p : DR => e (Sum.inr p)) := by
    intro u v huv
    have hfst : u.1.1 = v.1.1 := by
      have h := congrArg (fun x => x.1.1) huv
      rw [hrightfst u, hrightfst v] at h
      omega
    have hidx : u.1 = v.1 := Subtype.ext hfst
    have hsum := congrArg Subtype.val huv
    change rep u.1.1 (Finset.mem_of_mem_erase u.1.2) + u.2.1 =
      rep v.1.1 (Finset.mem_of_mem_erase v.1.2) + v.2.1 at hsum
    have hrepEq : rep u.1.1 (Finset.mem_of_mem_erase u.1.2) =
        rep v.1.1 (Finset.mem_of_mem_erase v.1.2) :=
      congrArg (fun z : ↥(P.erase 0) =>
        rep z.1 (Finset.mem_of_mem_erase z.2)) hidx
    rw [hrepEq] at hsum
    have hval : u.2.1 = v.2.1 := add_left_cancel hsum
    exact Prod.ext hidx (Subtype.ext hval)
  have heinj : Function.Injective e := by
    intro u v huv
    rcases u with (u | u) <;> rcases v with (v | v)
    · rcases u with (u | u) <;> rcases v with (v | v)
      · exact congrArg (fun p : DL => Sum.inl (Sum.inl p)) (hleftinj huv)
      · have hfst := congrArg (fun x => x.1.1) huv
        rw [hleftfst u, hcenterfst v] at hfst
        have hu := hleftlt u
        omega
      · have hfst := congrArg (fun x => x.1.1) huv
        rw [hcenterfst u, hleftfst v] at hfst
        have hv := hleftlt v
        omega
      · exact congrArg (fun c : DC => Sum.inl (Sum.inr c)) (hcenterinj huv)
    · rcases u with (u | u)
      · have hfst := congrArg (fun x => x.1.1) huv
        rw [hleftfst u, hrightfst v] at hfst
        have hu := hleftlt u
        have hv := hrightpos v
        omega
      · have hfst := congrArg (fun x => x.1.1) huv
        rw [hcenterfst u, hrightfst v] at hfst
        have hv := hrightpos v
        omega
    · rcases v with (v | v)
      · have hfst := congrArg (fun x => x.1.1) huv
        rw [hrightfst u, hleftfst v] at hfst
        have hu := hrightpos u
        have hv := hleftlt v
        omega
      · have hfst := congrArg (fun x => x.1.1) huv
        rw [hrightfst u, hcenterfst v] at hfst
        have hu := hrightpos u
        omega
    · exact congrArg (fun p : DR => Sum.inr p) (hrightinj huv)
  have hcard := Fintype.card_le_of_injective e heinj
  have hcardEraseL : (P.erase l).card = P.card - 1 := by
    rw [Finset.card_erase_of_mem]
    simpa [P] using hl
  have hcardErase0 : (P.erase 0).card = P.card - 1 := by
    rw [Finset.card_erase_of_mem]
    simpa [P] using h0
  simpa [D, DL, DC, DR, P, A0, Al, Fintype.card_sum,
    Fintype.card_prod, hcardEraseL, hcardErase0,
    add_assoc, add_left_comm, add_comm] using hcard

/-- Two endpoint fibres contribute their union inside the middle sum fibre;
the overlap is exactly a translated intersection. -/
theorem card_add_le_card_add_add_card_shifted_inter
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    (A B : Finset G) (hzero : 0 ∈ A) (δ : G) (hδ : δ ∈ B) :
    A.card + B.card ≤ (A + B).card + (A ∩ (-δ +ᵥ B)).card := by
  let U : Finset G := δ +ᵥ A
  let I : Finset G := A ∩ (-δ +ᵥ B)
  have hshiftI : δ +ᵥ I = U ∩ B := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, hyI, hyx⟩ := Finset.mem_vadd_finset.mp hx
      obtain ⟨hyA, hyB⟩ := Finset.mem_inter.mp hyI
      obtain ⟨z, hzB, hzy⟩ := Finset.mem_vadd_finset.mp hyB
      apply Finset.mem_inter.mpr
      refine ⟨Finset.mem_vadd_finset.mpr ⟨y, hyA, hyx⟩, ?_⟩
      simp only [vadd_eq_add] at hyx hzy
      have : x = z := by rw [← hyx, ← hzy]; abel
      simpa [this] using hzB
    · intro hx
      obtain ⟨hxU, hxB⟩ := Finset.mem_inter.mp hx
      obtain ⟨y, hyA, hyx⟩ := Finset.mem_vadd_finset.mp hxU
      apply Finset.mem_vadd_finset.mpr
      refine ⟨y, Finset.mem_inter.mpr ⟨hyA, ?_⟩, hyx⟩
      apply Finset.mem_vadd_finset.mpr
      refine ⟨x, hxB, ?_⟩
      simp only [vadd_eq_add] at hyx ⊢
      rw [← hyx]
      abel
  have hUsub : U ⊆ A + B := by
    intro x hx
    obtain ⟨a, ha, hax⟩ := Finset.mem_vadd_finset.mp hx
    exact Finset.mem_add.mpr ⟨a, ha, δ, hδ, by
      simpa [vadd_eq_add, add_comm] using hax⟩
  have hBsub : B ⊆ A + B := by
    intro b hb
    exact Finset.mem_add.mpr ⟨0, hzero, b, hb, by simp⟩
  have hUnionSub : U ∪ B ⊆ A + B := Finset.union_subset hUsub hBsub
  have hUnionCard : (U ∪ B).card ≤ (A + B).card :=
    Finset.card_le_card hUnionSub
  have hUcard : U.card = A.card := Finset.card_vadd_finset δ A
  have hIcard : (U ∩ B).card = I.card := by
    rw [← hshiftI, Finset.card_vadd_finset]
  dsimp [I] at hIcard
  have hpartition := Finset.card_union_add_card_inter U B
  omega

/-- Lev's basic endpoint estimate in `ℤ × H`: the double sumset, plus the
overlap between the two endpoint fibres after alignment, dominates the number
of occupied integer fibres times the total endpoint mass. -/
theorem endpoint_fiber_basic_estimate
    (A : Finset (ℤ × H)) (l : ℤ) (hlpos : 0 < l)
    (hzero : (0, 0) ∈ A) (δ : ℤ × H)
    (hδ : δ ∈ integerFiber A l)
    (h0 : 0 ∈ A.image Prod.fst) (hl : l ∈ A.image Prod.fst)
    (hbounds : ∀ z ∈ A.image Prod.fst, 0 ≤ z ∧ z ≤ l) :
    (A.image Prod.fst).card *
        ((integerFiber A 0).card + (integerFiber A l).card) ≤
      (A + A).card +
        (integerFiber A 0 ∩ (-δ +ᵥ integerFiber A l)).card := by
  have hz0 : (0, 0) ∈ integerFiber A 0 := by
    rw [mem_integerFiber]
    exact ⟨hzero, rfl⟩
  have hmiddle := card_add_le_card_add_add_card_shifted_inter
    (integerFiber A 0) (integerFiber A l) hz0 δ hδ
  have hregions := endpoint_fiber_three_region_bound
    A l hlpos h0 hl hbounds
  let s := (A.image Prod.fst).card
  let a0 := (integerFiber A 0).card
  let al := (integerFiber A l).card
  let c := (integerFiber A 0 + integerFiber A l).card
  let e := (integerFiber A 0 ∩ (-δ +ᵥ integerFiber A l)).card
  let d := (A + A).card
  have hspos : 0 < s := by
    dsimp [s]
    rw [Finset.card_pos]
    exact ⟨0, h0⟩
  have hsEq : s = (s - 1) + 1 := by omega
  change s * (a0 + al) ≤ d + e
  change a0 + al ≤ c + e at hmiddle
  change (s - 1) * a0 + c + (s - 1) * al ≤ d at hregions
  have hsA0 := congrArg (fun q : ℕ => q * a0) hsEq
  have hsAl := congrArg (fun q : ℕ => q * al) hsEq
  simp only [add_mul, one_mul] at hsA0 hsAl
  calc
    s * (a0 + al) =
        (s - 1) * a0 + (s - 1) * al + (a0 + al) := by
      rw [mul_add, hsA0, hsAl]
      omega
    _ ≤ (s - 1) * a0 + (s - 1) * al + (c + e) :=
      Nat.add_le_add_left hmiddle _
    _ = ((s - 1) * a0 + c + (s - 1) * al) + e := by ring
    _ ≤ d + e := Nat.add_le_add_right hregions e

/-- Division-free arithmetic form of the endpoint argument: the moderate
torsion threshold and the endpoint estimate force the two sharp deficiency
inequalities used in the induction. -/
theorem moderate_endpoint_arithmetic
    (n a d σ e : ℕ) (hn : 2 ≤ n)
    (he : 2 * e ≤ σ) (hend : n * σ ≤ d + e)
    (hsmall : n * d < 3 * (n - 1) * a) :
    d + σ < 3 * a ∧ d + 2 * e < 3 * a := by
  have hfirst : d + σ < 3 * a := by
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k + 2 := ⟨n - 2, by omega⟩
    simp at hsmall
    have hsbound : (2 * k + 3) * σ ≤ 2 * d := by
      have h2end := Nat.mul_le_mul_left 2 hend
      nlinarith
    have hcoef : (2 * k + 5) * (k + 1) < (k + 2) * (2 * k + 3) := by
      nlinarith
    have ha : 0 < a := by
      by_contra h
      simp at h
      simp [h] at hsmall
    have hmain : ((k + 2) * (2 * k + 3)) * (d + σ) <
        ((k + 2) * (2 * k + 3)) * (3 * a) := by
      calc
        ((k + 2) * (2 * k + 3)) * (d + σ) =
            (k + 2) * ((2 * k + 3) * d + (2 * k + 3) * σ) := by ring
        _ ≤ (k + 2) * ((2 * k + 3) * d + 2 * d) :=
          Nat.mul_le_mul_left (k + 2) (Nat.add_le_add_left hsbound _)
        _ = (2 * k + 5) * ((k + 2) * d) := by ring
        _ < (2 * k + 5) * (3 * (k + 1) * a) :=
          Nat.mul_lt_mul_of_pos_left hsmall (by omega)
        _ = 3 * ((2 * k + 5) * (k + 1)) * a := by ring
        _ < 3 * ((k + 2) * (2 * k + 3)) * a :=
          Nat.mul_lt_mul_of_pos_right
            (Nat.mul_lt_mul_of_pos_left hcoef (by omega)) ha
        _ = ((k + 2) * (2 * k + 3)) * (3 * a) := by ring
    exact Nat.lt_of_mul_lt_mul_left hmain
  exact ⟨hfirst, by omega⟩

/-- Concrete deficiency consequences of the endpoint estimate under the
rectifiable `3n-3` threshold. -/
theorem endpoint_fiber_deficiency_consequences
    (A : Finset (ℤ × H)) (l : ℤ) (hlpos : 0 < l)
    (hzero : (0, 0) ∈ A) (δ : ℤ × H)
    (hδ : δ ∈ integerFiber A l)
    (h0 : 0 ∈ A.image Prod.fst) (hl : l ∈ A.image Prod.fst)
    (hbounds : ∀ z ∈ A.image Prod.fst, 0 ≤ z ∧ z ≤ l)
    (hsmall : (A.image Prod.fst).card * (A + A).card <
      3 * ((A.image Prod.fst).card - 1) * A.card) :
    (A + A).card +
        ((integerFiber A 0).card + (integerFiber A l).card) < 3 * A.card ∧
    (A + A).card +
        2 * (integerFiber A 0 ∩ (-δ +ᵥ integerFiber A l)).card <
      3 * A.card := by
  let n := (A.image Prod.fst).card
  let σ := (integerFiber A 0).card + (integerFiber A l).card
  let e := (integerFiber A 0 ∩ (-δ +ᵥ integerFiber A l)).card
  have hn : 2 ≤ n := by
    have hcard : 1 < (A.image Prod.fst).card :=
      Finset.one_lt_card.mpr ⟨0, h0, l, hl, by omega⟩
    change 2 ≤ (A.image Prod.fst).card
    omega
  have he0 : e ≤ (integerFiber A 0).card := by
    dsimp [e]
    exact Finset.card_le_card Finset.inter_subset_left
  have hel : e ≤ (integerFiber A l).card := by
    dsimp [e]
    calc
      (integerFiber A 0 ∩ (-δ +ᵥ integerFiber A l)).card ≤
          (-δ +ᵥ integerFiber A l).card :=
        Finset.card_le_card Finset.inter_subset_right
      _ = (integerFiber A l).card := Finset.card_vadd_finset _ _
  have he : 2 * e ≤ σ := by
    dsimp [σ]
    omega
  have hend := endpoint_fiber_basic_estimate
    A l hlpos hzero δ hδ h0 hl hbounds
  change n * σ ≤ (A + A).card + e at hend
  change n * (A + A).card < 3 * (n - 1) * A.card at hsmall
  have h := moderate_endpoint_arithmetic n A.card (A + A).card σ e
    hn he hend hsmall
  simpa [σ, e] using h

end Erdos336
