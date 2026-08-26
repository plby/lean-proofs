import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# Sparse forbidden entries under a random permutation

The finite counting estimates here will permit a sparse-list correction of an
ordinary approximate edge coloring. They do not assume a list-coloring theorem.
-/

namespace Erdos19

open Finset

/-- Prescribing a permutation on `S` leaves at most the factorial of the
complement size possible permutations. Inconsistent prescriptions have no
extensions and are allowed. -/
theorem card_permutations_agree_le {A : Type*} [Fintype A] [DecidableEq A]
    (S : Finset A) (g : A → A) :
    Fintype.card {p : Equiv.Perm A // ∀ x ∈ S, p x = g x} ≤
      (Fintype.card A - S.card).factorial := by
  classical
  let P := {p : Equiv.Perm A // ∀ x ∈ S, p x = g x}
  by_cases hP : Nonempty P
  · obtain ⟨p₀⟩ := hP
    have hg : Set.InjOn g S := by
      intro x hx y hy hxy
      apply p₀.val.injective
      rw [p₀.property x hx, p₀.property y hy, hxy]
    have himage : (S.image g).card = S.card := card_image_of_injOn hg
    let restrict : P → ({x : A // x ∉ S} ↪ {y : A // y ∉ S.image g}) :=
      fun p ↦
        { toFun := fun x ↦ ⟨p.val x.val, by
            intro h
            obtain ⟨y, hy, heq⟩ := mem_image.mp h
            have hxy : y = x.val := p.val.injective ((p.property y hy).trans heq)
            exact x.property (hxy ▸ hy)⟩
          inj' := fun x y h ↦ Subtype.ext (p.val.injective (congrArg Subtype.val h)) }
    have hinj : Function.Injective restrict := by
      intro p q hpq
      apply Subtype.ext
      apply Equiv.ext
      intro x
      by_cases hx : x ∈ S
      · exact (p.property x hx).trans (q.property x hx).symm
      · exact congrArg Subtype.val
          (congrArg (fun f : {x : A // x ∉ S} ↪ {y : A // y ∉ S.image g} ↦
            f ⟨x, hx⟩) hpq)
    have hdom : Fintype.card {x : A // x ∉ S} = Fintype.card A - S.card := by
      rw [Fintype.card_subtype_compl, Fintype.card_coe]
    have hcod : Fintype.card {y : A // y ∉ S.image g} = Fintype.card A - S.card := by
      rw [Fintype.card_subtype_compl, Fintype.card_coe, himage]
    calc
      Fintype.card P ≤ Fintype.card ({x : A // x ∉ S} ↪ {y : A // y ∉ S.image g}) :=
        Fintype.card_le_of_injective restrict hinj
      _ = (Fintype.card A - S.card).factorial := by
        rw [Fintype.card_embedding_eq, hdom, hcod, Nat.descFactorial_self]
  · have : IsEmpty P := not_nonempty_iff.mp hP
    change Fintype.card P ≤ _
    simp only [Fintype.card_eq_zero, Nat.zero_le]

/-- A permutation hits specified sets of size at most `f` on all of `S` in at
most `f ^ |S| * (|A| - |S|)!` ways. -/
theorem card_permutations_mem_le {A : Type*} [Fintype A] [DecidableEq A]
    (S : Finset A) (F : A → Finset A) (f : ℕ) (hF : ∀ x ∈ S, (F x).card ≤ f) :
    Fintype.card {p : Equiv.Perm A // ∀ x ∈ S, p x ∈ F x} ≤
      f ^ S.card * (Fintype.card A - S.card).factorial := by
  classical
  let P := {p : Equiv.Perm A // ∀ x ∈ S, p x ∈ F x}
  let L := (x : S) → ↥(F x.val)
  let assign : P → L := fun p x ↦ ⟨p.val x.val, p.property x.val x.property⟩
  have hfiber : ∀ a : L, Fintype.card {p : P // assign p = a} ≤
      (Fintype.card A - S.card).factorial := by
    intro a
    let g : A → A := fun x ↦ if hx : x ∈ S then (a ⟨x, hx⟩).val else x
    let forget : {p : P // assign p = a} →
        {p : Equiv.Perm A // ∀ x ∈ S, p x = g x} := fun p ↦
      ⟨p.val.val, by
        intro x hx
        have h := congrArg (fun b : L ↦ (b ⟨x, hx⟩).val) p.property
        simpa only [assign, g, dif_pos hx] using h⟩
    have hinj : Function.Injective forget := by
      intro p q hpq
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : {p : Equiv.Perm A // ∀ x ∈ S, p x = g x} ↦ z.val) hpq
    exact (Fintype.card_le_of_injective forget hinj).trans
      (card_permutations_agree_le S g)
  have hL : Fintype.card L ≤ f ^ S.card := by
    change Fintype.card ((x : S) → ↥(F x.val)) ≤ _
    rw [Fintype.card_pi]
    calc
      ∏ x : S, Fintype.card ↥(F x.val) ≤ ∏ _x : S, f := by
        apply prod_le_prod (fun _ _ ↦ Nat.zero_le _)
        intro x _
        simpa only [Fintype.card_coe] using hF x.val x.property
      _ = f ^ S.card := by simp
  calc
    Fintype.card P = ∑ a : L, Fintype.card {p : P // assign p = a} := by
      rw [← Fintype.card_sigma]
      exact (Fintype.card_congr (Equiv.sigmaFiberEquiv assign)).symm
    _ ≤ ∑ _a : L, (Fintype.card A - S.card).factorial :=
      sum_le_sum fun a _ ↦ hfiber a
    _ = Fintype.card L * (Fintype.card A - S.card).factorial := by simp
    _ ≤ f ^ S.card * (Fintype.card A - S.card).factorial := Nat.mul_le_mul_right _ hL

/-- The binomial union bound for the number of permutations with at least `s`
forbidden hits among `T`. -/
theorem card_permutations_hits_le {A : Type*} [Fintype A] [DecidableEq A]
    (T : Finset A) (F : A → Finset A) (f s : ℕ)
    (hF : ∀ x ∈ T, (F x).card ≤ f) :
    Fintype.card {p : Equiv.Perm A // s ≤ (T.filter fun x ↦ p x ∈ F x).card} ≤
      T.card.choose s * (f ^ s * (Fintype.card A - s).factorial) := by
  classical
  let P := {p : Equiv.Perm A // s ≤ (T.filter fun x ↦ p x ∈ F x).card}
  let I := ↥(T.powersetCard s)
  have hwitness : ∀ p : P, ∃ S : I, ∀ x ∈ S.val, p.val x ∈ F x := by
    intro p
    obtain ⟨S, hsub, hcard⟩ := exists_subset_card_eq p.property
    refine ⟨⟨S, mem_powersetCard.mpr ⟨hsub.trans (filter_subset _ _), hcard⟩⟩, ?_⟩
    intro x hx
    exact (mem_filter.mp (hsub hx)).2
  choose witness hwitness using hwitness
  let W := (S : I) × {p : Equiv.Perm A // ∀ x ∈ S.val, p x ∈ F x}
  let encode : P → W := fun p ↦ ⟨witness p, p.val, hwitness p⟩
  have hinj : Function.Injective encode := by
    intro p q hpq
    apply Subtype.ext
    exact congrArg (fun z : W ↦ z.2.val) hpq
  have hcount : ∀ S : I, Fintype.card {p : Equiv.Perm A // ∀ x ∈ S.val, p x ∈ F x} ≤
      f ^ s * (Fintype.card A - s).factorial := by
    intro S
    have hS := mem_powersetCard.mp S.property
    simpa only [hS.2] using card_permutations_mem_le S.val F f
      (fun x hx ↦ hF x (hS.1 hx))
  calc
    Fintype.card P ≤ Fintype.card W := Fintype.card_le_of_injective encode hinj
    _ = ∑ S : I, Fintype.card {p : Equiv.Perm A // ∀ x ∈ S.val, p x ∈ F x} :=
      Fintype.card_sigma
    _ ≤ ∑ _S : I, f ^ s * (Fintype.card A - s).factorial :=
      sum_le_sum fun S _ ↦ hcount S
    _ = T.card.choose s * (f ^ s * (Fintype.card A - s).factorial) := by
      simp [I]

/-- Factorial-moment form of the preceding tail bound. It is an integer
inequality and includes `s = 0` and `s > |A|`. -/
theorem card_permutations_hits_mul_factorial_le {A : Type*} [Fintype A] [DecidableEq A]
    (T : Finset A) (F : A → Finset A) (f s : ℕ)
    (hF : ∀ x ∈ T, (F x).card ≤ f) :
    Fintype.card {p : Equiv.Perm A // s ≤ (T.filter fun x ↦ p x ∈ F x).card} *
        s.factorial ≤ f ^ s * (Fintype.card A).factorial := by
  classical
  have h := card_permutations_hits_le T F f s hF
  by_cases hs : s ≤ Fintype.card A
  · have hchoose := Nat.choose_le_choose s (card_le_univ T)
    calc
      _ ≤ (T.card.choose s * (f ^ s * (Fintype.card A - s).factorial)) * s.factorial :=
        Nat.mul_le_mul_right _ h
      _ ≤ ((Fintype.card A).choose s * (f ^ s * (Fintype.card A - s).factorial)) *
          s.factorial := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hchoose)
      _ = f ^ s * ((Fintype.card A).choose s * s.factorial *
          (Fintype.card A - s).factorial) := by ring
      _ = _ := by rw [Nat.choose_mul_factorial_mul_factorial hs]
  · have hsmall : T.card < s := (card_le_univ T).trans_lt (Nat.lt_of_not_ge hs)
    have hzero : Fintype.card
        {p : Equiv.Perm A // s ≤ (T.filter fun x ↦ p x ∈ F x).card} = 0 := by
      apply Nat.eq_zero_of_le_zero
      simpa only [Nat.choose_eq_zero_of_lt hsmall, zero_mul] using h
    rw [hzero, zero_mul]
    exact Nat.zero_le _

/-- Simultaneous sparse-hit control by one permutation. The numerical
criterion is exact: the number of constraints times `f ^ s` is less than `s!`.
No independence between the different constraints is needed. -/
theorem exists_permutation_few_hits {A I : Type*} [Fintype A] [DecidableEq A]
    [Fintype I] (T : I → Finset A) (F : I → A → Finset A) (f s : ℕ)
    (hF : ∀ i x, x ∈ T i → (F i x).card ≤ f)
    (hsmall : Fintype.card I * f ^ s < s.factorial) :
    ∃ p : Equiv.Perm A, ∀ i, ((T i).filter fun x ↦ p x ∈ F i x).card < s := by
  classical
  let bad : I → Finset (Equiv.Perm A) := fun i ↦
    univ.filter fun p ↦ s ≤ ((T i).filter fun x ↦ p x ∈ F i x).card
  have hbad : ∀ i, (bad i).card * s.factorial ≤ f ^ s * (Fintype.card A).factorial := by
    intro i
    simpa only [bad, ← Fintype.card_subtype] using
      card_permutations_hits_mul_factorial_le (T i) (F i) f s (hF i)
  by_contra hnone
  push Not at hnone
  have hcover : (univ : Finset (Equiv.Perm A)) ⊆ univ.biUnion bad := by
    intro p _
    obtain ⟨i, hi⟩ := hnone p
    exact mem_biUnion.mpr ⟨i, mem_univ _, mem_filter.mpr ⟨mem_univ _, hi⟩⟩
  have hcard : (Fintype.card A).factorial ≤ ∑ i : I, (bad i).card := by
    calc
      (Fintype.card A).factorial = (univ : Finset (Equiv.Perm A)).card := by
        rw [card_univ, Fintype.card_perm]
      _ ≤ (univ.biUnion bad).card := card_le_card hcover
      _ ≤ ∑ i : I, (bad i).card := card_biUnion_le
  have hsum : (∑ i : I, (bad i).card) * s.factorial ≤
      (Fintype.card I * f ^ s) * (Fintype.card A).factorial := by
    calc
      _ = ∑ i : I, (bad i).card * s.factorial := sum_mul ..
      _ ≤ ∑ _i : I, f ^ s * (Fintype.card A).factorial := sum_le_sum fun i _ ↦ hbad i
      _ = _ := by simp [mul_assoc]
  have hle := (Nat.mul_le_mul_right s.factorial hcard).trans hsum
  have hlt := Nat.mul_lt_mul_of_pos_right hsmall (Nat.factorial_pos (Fintype.card A))
  exact (Nat.not_lt_of_ge (by simpa only [mul_comm] using hle)) hlt

/-- The same permutation estimate for a family of sets of objects with
distinct initial colors in each set. Forbidden sets belong to the objects,
and may differ between objects of the same initial color. -/
theorem exists_permutation_few_forbidden {A E I : Type*}
    [Fintype A] [DecidableEq A] [DecidableEq E] [Fintype I]
    (T : I → Finset E) (c : E → A) (hc : ∀ i, Set.InjOn c (T i))
    (F : E → Finset A) (f s : ℕ) (hF : ∀ i e, e ∈ T i → (F e).card ≤ f)
    (hsmall : Fintype.card I * f ^ s < s.factorial) :
    ∃ p : Equiv.Perm A, ∀ i,
      ((T i).filter fun e ↦ p (c e) ∈ F e).card < s := by
  classical
  let C : I → Finset A := fun i ↦ (T i).image c
  have hex : ∀ i (a : ↥(C i)), ∃ e, e ∈ T i ∧ c e = a.val := by
    intro i a
    exact mem_image.mp a.property
  choose pre hpre using hex
  let L : I → A → Finset A := fun i a ↦
    if ha : a ∈ C i then F (pre i ⟨a, ha⟩) else ∅
  have hL : ∀ i a, a ∈ C i → (L i a).card ≤ f := by
    intro i a ha
    simpa only [L, dif_pos ha] using hF i (pre i ⟨a, ha⟩) (hpre i ⟨a, ha⟩).1
  have hLc : ∀ i e, e ∈ T i → L i (c e) = F e := by
    intro i e he
    have ha : c e ∈ C i := mem_image_of_mem c he
    have hpre_eq : pre i ⟨c e, ha⟩ = e :=
      hc i (hpre i ⟨c e, ha⟩).1 he (hpre i ⟨c e, ha⟩).2
    simp only [L, dif_pos ha, hpre_eq]
  obtain ⟨p, hp⟩ := exists_permutation_few_hits C L f s hL hsmall
  refine ⟨p, ?_⟩
  intro i
  have himage : (((T i).filter fun e ↦ p (c e) ∈ F e).image c) =
      (C i).filter (fun a ↦ p a ∈ L i a) := by
    ext a
    constructor
    · intro ha
      obtain ⟨e, he, rfl⟩ := mem_image.mp ha
      obtain ⟨he, hforbid⟩ := mem_filter.mp he
      exact mem_filter.mpr ⟨mem_image_of_mem c he, (hLc i e he).symm ▸ hforbid⟩
    · intro ha
      obtain ⟨ha, hforbid⟩ := mem_filter.mp ha
      obtain ⟨e, he, rfl⟩ := mem_image.mp ha
      exact mem_image.mpr ⟨e, mem_filter.mpr ⟨he, hLc i e he ▸ hforbid⟩, rfl⟩
  have hinj : Set.InjOn c ((T i).filter fun e ↦ p (c e) ∈ F e) :=
    (hc i).mono (filter_subset _ _)
  rw [← card_image_of_injOn hinj, himage]
  exact hp i

#print axioms card_permutations_agree_le
#print axioms card_permutations_mem_le
#print axioms card_permutations_hits_mul_factorial_le
#print axioms exists_permutation_few_hits
#print axioms exists_permutation_few_forbidden

end Erdos19
