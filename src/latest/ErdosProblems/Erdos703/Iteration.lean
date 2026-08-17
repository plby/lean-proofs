import Mathlib

open scoped BigOperators
open Finset

namespace Erdos703Iteration

/-!
An axiom-free formalization of the finite coordinate-section part of the
Frankl--Rödl forbidden-intersection iteration.  The two isoperimetric endpoint
estimates are deliberately abstracted as hypotheses at the end of the file.
-/

abbrev Family (m : ℕ) := Finset (Finset (Fin m))

def liftZero {m : ℕ} (A : Finset (Fin m)) : Finset (Fin (m + 1)) :=
  A.map Fin.castSuccEmb

def liftOne {m : ℕ} (A : Finset (Fin m)) : Finset (Fin (m + 1)) :=
  insert (Fin.last m) (liftZero A)

def sectionZero {m : ℕ} (F : Family (m + 1)) : Family m :=
  Finset.univ.filter fun A ↦ liftZero A ∈ F

def sectionOne {m : ℕ} (F : Family (m + 1)) : Family m :=
  Finset.univ.filter fun A ↦ liftOne A ∈ F

def dropLast {m : ℕ} (S : Finset (Fin (m + 1))) : Finset (Fin m) :=
  Finset.univ.filter fun i ↦ i.castSucc ∈ S

@[simp] lemma mem_sectionZero {m : ℕ} {F : Family (m + 1)} {A : Finset (Fin m)} :
    A ∈ sectionZero F ↔ liftZero A ∈ F := by
  simp [sectionZero]

@[simp] lemma mem_sectionOne {m : ℕ} {F : Family (m + 1)} {A : Finset (Fin m)} :
    A ∈ sectionOne F ↔ liftOne A ∈ F := by
  simp [sectionOne]

@[simp] lemma last_not_mem_liftZero {m : ℕ} (A : Finset (Fin m)) :
    Fin.last m ∉ liftZero A := by
  simp [liftZero]

@[simp] lemma dropLast_liftZero {m : ℕ} (A : Finset (Fin m)) :
    dropLast (liftZero A) = A := by
  ext i
  simp [dropLast, liftZero]

@[simp] lemma dropLast_liftOne {m : ℕ} (A : Finset (Fin m)) :
    dropLast (liftOne A) = A := by
  ext i
  simp [dropLast, liftOne, liftZero]

lemma liftZero_dropLast_of_last_not_mem {m : ℕ} {S : Finset (Fin (m + 1))}
    (hS : Fin.last m ∉ S) : liftZero (dropLast S) = S := by
  ext x
  by_cases hx : x = Fin.last m
  · subst x
    simp [hS]
  · obtain ⟨i, rfl⟩ := Fin.eq_castSucc_of_ne_last hx
    simp [dropLast, liftZero]

lemma liftOne_dropLast_of_last_mem {m : ℕ} {S : Finset (Fin (m + 1))}
    (hS : Fin.last m ∈ S) : liftOne (dropLast S) = S := by
  ext x
  by_cases hx : x = Fin.last m
  · subst x
    simp [liftOne, hS]
  · obtain ⟨i, rfl⟩ := Fin.eq_castSucc_of_ne_last hx
    simp [dropLast, liftOne, liftZero]

@[simp] lemma liftZero_injective {m : ℕ} : Function.Injective (@liftZero m) := by
  intro A B h
  exact Finset.map_injective Fin.castSuccEmb h

@[simp] lemma liftZero_inter {m : ℕ} (A B : Finset (Fin m)) :
    liftZero (A ∩ B) = liftZero A ∩ liftZero B := by
  exact Finset.map_inter A B

@[simp] lemma liftZero_inter_liftOne {m : ℕ} (A B : Finset (Fin m)) :
    liftZero A ∩ liftOne B = liftZero (A ∩ B) := by
  calc
    liftZero A ∩ liftOne B = liftZero A ∩ liftZero B := by
      ext x
      by_cases hx : x = Fin.last m <;> simp [liftOne, hx]
    _ = liftZero (A ∩ B) := (liftZero_inter A B).symm

@[simp] lemma liftOne_inter_liftZero {m : ℕ} (A B : Finset (Fin m)) :
    liftOne A ∩ liftZero B = liftZero (A ∩ B) := by
  rw [Finset.inter_comm]
  simpa [Finset.inter_comm] using liftZero_inter_liftOne B A

@[simp] lemma liftOne_inter {m : ℕ} (A B : Finset (Fin m)) :
    liftOne A ∩ liftOne B = liftOne (A ∩ B) := by
  ext x
  by_cases hx : x = Fin.last m
  · simp [liftOne, hx]
  · simp only [liftOne, Finset.mem_inter, Finset.mem_insert, hx, false_or]
    constructor
    · rintro ⟨hA, hB⟩
      have hxmem : x ∈ liftZero A ∩ liftZero B := Finset.mem_inter.mpr ⟨hA, hB⟩
      rw [← liftZero_inter] at hxmem
      exact hxmem
    · intro hxmem
      have : x ∈ liftZero A ∩ liftZero B := by
        rw [← liftZero_inter]
        exact hxmem
      exact Finset.mem_inter.mp this

@[simp] lemma card_liftZero {m : ℕ} (A : Finset (Fin m)) :
    (liftZero A).card = A.card := by
  simp [liftZero]

@[simp] lemma card_liftOne {m : ℕ} (A : Finset (Fin m)) :
    (liftOne A).card = A.card + 1 := by
  simp [liftOne]

@[simp] lemma card_liftZero_inter {m : ℕ} (A B : Finset (Fin m)) :
    (liftZero A ∩ liftZero B).card = (A ∩ B).card := by
  rw [← liftZero_inter, card_liftZero]

@[simp] lemma card_liftZero_inter_liftOne {m : ℕ} (A B : Finset (Fin m)) :
    (liftZero A ∩ liftOne B).card = (A ∩ B).card := by
  rw [liftZero_inter_liftOne, card_liftZero]

@[simp] lemma card_liftOne_inter_liftZero {m : ℕ} (A B : Finset (Fin m)) :
    (liftOne A ∩ liftZero B).card = (A ∩ B).card := by
  rw [liftOne_inter_liftZero, card_liftZero]

@[simp] lemma card_liftOne_inter {m : ℕ} (A B : Finset (Fin m)) :
    (liftOne A ∩ liftOne B).card = (A ∩ B).card + 1 := by
  simp

def CrossAvoids {m : ℕ} (a b : ℕ) (F G : Family m) : Prop :=
  ∀ A ∈ F, ∀ B ∈ G, (A ∩ B).card < a ∨ b < (A ∩ B).card

lemma crossAvoids_mono {m a b a' b' : ℕ} {F G : Family m}
    (h : CrossAvoids a b F G) (ha : a ≤ a') (hb : b' ≤ b) :
    CrossAvoids a' b' F G := by
  intro A hA B hB
  rcases h A hA B hB with hlt | hgt
  · exact Or.inl (lt_of_lt_of_le hlt ha)
  · exact Or.inr (lt_of_le_of_lt hb hgt)

lemma sectionOne_sectionOne_avoids {m a b : ℕ} {F G : Family (m + 1)}
    (h : CrossAvoids (a + 1) (b + 1) F G) :
    CrossAvoids a b (sectionOne F) (sectionOne G) := by
  intro A hA B hB
  have h' := h (liftOne A) (by simpa using hA) (liftOne B) (by simpa using hB)
  simp only [card_liftOne_inter] at h'
  omega

lemma sectionZero_union_avoids {m a b : ℕ} {F G : Family (m + 1)}
    (h : CrossAvoids a b F G) :
    CrossAvoids a b (sectionZero F) (sectionZero G ∪ sectionOne G) := by
  intro A hA B hB
  rw [Finset.mem_union] at hB
  rcases hB with hB | hB
  · simpa using h (liftZero A) (by simpa using hA) (liftZero B) (by simpa using hB)
  · simpa using h (liftZero A) (by simpa using hA) (liftOne B) (by simpa using hB)

lemma sectionOne_inter_avoids {m a b : ℕ} (hab : a + 1 ≤ b)
    {F G : Family (m + 1)} (h : CrossAvoids (a + 1) b F G) :
    CrossAvoids a b (sectionOne F) (sectionZero G ∩ sectionOne G) := by
  intro A hA B hB
  have hB0 : B ∈ sectionZero G := (Finset.mem_inter.mp hB).1
  have hB1 : B ∈ sectionOne G := (Finset.mem_inter.mp hB).2
  have hz := h (liftOne A) (by simpa using hA) (liftZero B) (by simpa using hB0)
  have ho := h (liftOne A) (by simpa using hA) (liftOne B) (by simpa using hB1)
  simp only [card_liftOne_inter_liftZero] at hz
  simp only [card_liftOne_inter] at ho
  by_cases hs : (A ∩ B).card < a
  · exact Or.inl hs
  right
  by_contra hnb
  have hsle : (A ∩ B).card ≤ b := Nat.le_of_not_gt hnb
  have hale : a ≤ (A ∩ B).card := Nat.le_of_not_gt hs
  by_cases heq : (A ∩ B).card = a
  · subst heq
    omega
  · have ha1 : a + 1 ≤ (A ∩ B).card := by omega
    omega

noncomputable def density {m : ℕ} (F : Family m) : ℝ :=
  F.card / (2 : ℝ) ^ m

lemma card_sectionZero {m : ℕ} (F : Family (m + 1)) :
    (sectionZero F).card = (F.filter fun S ↦ Fin.last m ∉ S).card := by
  classical
  apply Finset.card_bij' (fun A _ ↦ liftZero A) (fun S _ ↦ dropLast S)
  · intro A hA
    simp only [Finset.mem_filter]
    exact ⟨(by simpa using hA), last_not_mem_liftZero A⟩
  · intro S hS
    simp only [Finset.mem_filter] at hS
    rw [mem_sectionZero, liftZero_dropLast_of_last_not_mem hS.2]
    exact hS.1
  · intro A hA
    exact dropLast_liftZero A
  · intro S hS
    exact liftZero_dropLast_of_last_not_mem (Finset.mem_filter.mp hS).2

lemma card_sectionOne {m : ℕ} (F : Family (m + 1)) :
    (sectionOne F).card = (F.filter fun S ↦ Fin.last m ∈ S).card := by
  classical
  apply Finset.card_bij' (fun A _ ↦ liftOne A) (fun S _ ↦ dropLast S)
  · intro A hA
    simp only [Finset.mem_filter]
    exact ⟨(by simpa using hA), by simp [liftOne]⟩
  · intro S hS
    simp only [Finset.mem_filter] at hS
    rw [mem_sectionOne, liftOne_dropLast_of_last_mem hS.2]
    exact hS.1
  · intro A hA
    exact dropLast_liftOne A
  · intro S hS
    exact liftOne_dropLast_of_last_mem (Finset.mem_filter.mp hS).2

lemma card_sections_add {m : ℕ} (F : Family (m + 1)) :
    (sectionZero F).card + (sectionOne F).card = F.card := by
  classical
  rw [card_sectionZero, card_sectionOne]
  let F0 := F.filter fun S ↦ Fin.last m ∉ S
  let F1 := F.filter fun S ↦ Fin.last m ∈ S
  have hu : F0 ∪ F1 = F := by
    ext S
    by_cases hSF : S ∈ F <;> by_cases hSl : Fin.last m ∈ S <;> simp [F0, F1, hSF, hSl]
  have hi : F0 ∩ F1 = ∅ := by
    ext S
    by_cases hSF : S ∈ F <;> by_cases hSl : Fin.last m ∈ S <;> simp [F0, F1, hSF, hSl]
  have hcard := Finset.card_union_add_card_inter F0 F1
  rw [hu, hi] at hcard
  simpa using hcard.symm

lemma density_sections_add {m : ℕ} (F : Family (m + 1)) :
    density (sectionZero F) + density (sectionOne F) = 2 * density F := by
  rw [density, density, density]
  have hcast : ((sectionZero F).card : ℝ) + (sectionOne F).card = F.card := by
    exact_mod_cast card_sections_add F
  rw [← add_div, hcast, pow_succ]
  ring

lemma density_union_add_inter {m : ℕ} (F G : Family m) :
    density (F ∪ G) + density (F ∩ G) = density F + density G := by
  rw [density, density, density, density, ← add_div, ← add_div]
  congr 1
  exact_mod_cast Finset.card_union_add_card_inter F G

lemma density_inter_le_left {m : ℕ} (F G : Family m) : density (F ∩ G) ≤ density F := by
  rw [density, density]
  gcongr
  exact show F ∩ G ⊆ F from Finset.inter_subset_left

lemma density_inter_le_right {m : ℕ} (F G : Family m) : density (F ∩ G) ≤ density G := by
  rw [density, density]
  gcongr
  exact show F ∩ G ⊆ G from Finset.inter_subset_right

lemma density_union_ge_left {m : ℕ} (F G : Family m) : density F ≤ density (F ∪ G) := by
  rw [density, density]
  gcongr
  exact show F ⊆ F ∪ G by intro x hx; simp [hx]

lemma density_union_ge_right {m : ℕ} (F G : Family m) : density G ≤ density (F ∪ G) := by
  rw [density, density]
  gcongr
  exact show G ⊆ F ∪ G by intro x hx; simp [hx]

lemma fr_density_algebra_aux {s x y : ℝ}
    (hs0 : 0 ≤ s) (hs : s ≤ 1 / 10) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hsmall : (1 + y) ^ 2 ≤ 1 + s)
    (hfail : (1 + x) * (1 - y) ≤ 1 + s) :
    1 - s - 2 * s ^ 2 ≤ (1 + y) * (1 - x) := by
  have hy2 : 2 * y ≤ s := by
    nlinarith [sq_nonneg y]
  have hy_le : y ≤ 1 / 20 := by nlinarith
  have hone_y : 0 < 1 - y := by nlinarith
  have hxy : x * y ≤ s ^ 2 := by
    have hx_le : x ≤ 2 * s := by
      by_contra hnot
      have hgt : 2 * s < x := lt_of_not_ge hnot
      have hmul : 2 * s * (1 - y) < x * (1 - y) :=
        mul_lt_mul_of_pos_right hgt hone_y
      have hupper : x * (1 - y) ≤ s + y := by nlinarith
      have hlower : s + y ≤ 2 * s * (1 - y) := by
        nlinarith [mul_nonneg hs0 hy]
      linarith
    calc
      x * y ≤ (2 * s) * y := by gcongr
      _ = s * (2 * y) := by ring
      _ ≤ s * s := by gcongr
      _ = s ^ 2 := by ring
  nlinarith

lemma fr_bad_product_of_small_left
    {s f f0 f1 g gu gi : ℝ}
    (hs0 : 0 ≤ s) (hs : s ≤ 1 / 10)
    (hf : 0 < f) (hg : 0 < g)
    (hf0 : 0 ≤ f0) (hf1 : 0 ≤ f1) (hgu : 0 ≤ gu) (hgi : 0 ≤ gi)
    (hfsum : f0 + f1 = 2 * f) (hgsum : gu + gi = 2 * g) (horder : gi ≤ gu)
    (hsmall : f1 ^ 2 ≤ (1 + s) * f ^ 2)
    (hfail : f0 * gu ≤ (1 + s) * f * g) :
    (1 - s - 2 * s ^ 2) * f * g ≤ f1 * gi := by
  let x := gu / g - 1
  let y := f1 / f - 1
  have hfg : 0 < f * g := mul_pos hf hg
  have hf2 : 0 < f ^ 2 := sq_pos_of_pos hf
  have hgu_eq : gu = (1 + x) * g := by
    dsimp [x]
    field_simp
    ring
  have hgi_eq : gi = (1 - x) * g := by
    calc
      gi = 2 * g - gu := by linarith [hgsum]
      _ = (1 - x) * g := by rw [hgu_eq]; ring
  have hf1_eq : f1 = (1 + y) * f := by
    dsimp [y]
    field_simp
    ring
  have hf0_eq : f0 = (1 - y) * f := by
    calc
      f0 = 2 * f - f1 := by linarith [hfsum]
      _ = (1 - y) * f := by rw [hf1_eq]; ring
  have hx : 0 ≤ x := by
    rw [hgu_eq, hgi_eq] at horder
    nlinarith
  by_cases hycase : 0 ≤ y
  · have hsmall' : (1 + y) ^ 2 ≤ 1 + s := by
      rw [hf1_eq, mul_pow] at hsmall
      nlinarith
    have hfail' : (1 + x) * (1 - y) ≤ 1 + s := by
      rw [hf0_eq, hgu_eq] at hfail
      have hscaled : ((1 + x) * (1 - y)) * (f * g) ≤ (1 + s) * (f * g) := by
        simpa [mul_assoc, mul_comm, mul_left_comm] using hfail
      exact le_of_mul_le_mul_right hscaled hfg
    have haux := fr_density_algebra_aux hs0 hs hx hycase hsmall' hfail'
    rw [hf1_eq, hgi_eq]
    have hscaled := mul_le_mul_of_nonneg_right haux (le_of_lt hfg)
    nlinarith
  · have hy : y < 0 := lt_of_not_ge hycase
    have hfail' : ((1 - y) * (1 + x)) * (f * g) ≤ (1 + s) * (f * g) := by
      rw [hf0_eq, hgu_eq] at hfail
      simpa [mul_assoc, mul_comm, mul_left_comm] using hfail
    have hfail'' : (1 - y) * (1 + x) ≤ 1 + s :=
      le_of_mul_le_mul_right hfail' hfg
    have hxy : x * y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hx (le_of_lt hy)
    have hraw : 1 - s - 2 * s ^ 2 ≤ (1 + y) * (1 - x) := by
      nlinarith [sq_nonneg s]
    rw [hf1_eq, hgi_eq]
    have hscaled := mul_le_mul_of_nonneg_right hraw (le_of_lt hfg)
    nlinarith

lemma small_square_or_of_product
    {c f f1 g g1 : ℝ} (hc : 0 < c) (hf : 0 < f) (hg : 0 < g)
    (hf1 : 0 ≤ f1) (hg1 : 0 ≤ g1)
    (hprod : f1 * g1 ≤ c * f * g) :
    f1 ^ 2 ≤ c * f ^ 2 ∨ g1 ^ 2 ≤ c * g ^ 2 := by
  by_contra h
  push_neg at h
  have hf1pos : 0 < f1 := by nlinarith [sq_nonneg f1]
  have hg1pos : 0 < g1 := by nlinarith [sq_nonneg g1]
  have hleft := mul_lt_mul_of_pos_right h.1 (sq_pos_of_pos hg1pos)
  have hright := mul_lt_mul_of_pos_left h.2 (mul_pos hc (sq_pos_of_pos hf))
  have hstrict : (c * f * g) ^ 2 < (f1 * g1) ^ 2 := by
    calc
      (c * f * g) ^ 2 = (c * f ^ 2) * (c * g ^ 2) := by ring
      _ < (c * f ^ 2) * g1 ^ 2 := hright
      _ < f1 ^ 2 * g1 ^ 2 := hleft
      _ = (f1 * g1) ^ 2 := by ring
  have hnonneg : 0 ≤ c * f * g := by positivity
  have hsquare : (f1 * g1) ^ 2 ≤ (c * f * g) ^ 2 :=
    (sq_le_sq₀ (mul_nonneg hf1 hg1) hnonneg).2 hprod
  exact (not_lt_of_ge hsquare hstrict)

lemma density_nonneg {m : ℕ} (F : Family m) : 0 ≤ density F := by
  exact div_nonneg (Nat.cast_nonneg _) (pow_nonneg (by norm_num) _)

lemma density_le_one {m : ℕ} (F : Family m) : density F ≤ 1 := by
  rw [density, div_le_one (by positivity : (0 : ℝ) < 2 ^ m)]
  have h := F.card_le_univ
  exact_mod_cast (by simpa using h)

lemma crossAvoids_comm {m a b : ℕ} {F G : Family m} (h : CrossAvoids a b F G) :
    CrossAvoids a b G F := by
  intro B hB A hA
  simpa [Finset.inter_comm] using h A hA B hB

/-- One coordinate step of the Frankl--Rödl iteration.  A good step either
keeps or shifts the forbidden interval and gains a factor `1+s`; a bad step
widens the interval and loses only the factor `1-s-2*s^2`. -/
lemma fr_one_step {m a b : ℕ} {F G : Family (m + 1)} {s : ℝ}
    (hs0 : 0 ≤ s) (hs : s ≤ 1 / 10) (ha : 0 < a) (hab : a ≤ b)
    (havoid : CrossAvoids a b F G) :
    (∃ F' G' : Family m,
        CrossAvoids (a - 1) (b - 1) F' G' ∧
          (1 + s) * density F * density G ≤ density F' * density G') ∨
    (∃ F' G' : Family m,
        CrossAvoids a b F' G' ∧
          (1 + s) * density F * density G ≤ density F' * density G') ∨
    (∃ F' G' : Family m,
        CrossAvoids (a - 1) b F' G' ∧
          (1 - s - 2 * s ^ 2) * density F * density G ≤
            density F' * density G') := by
  have haeq : a - 1 + 1 = a := by omega
  have hbpos : 0 < b := lt_of_lt_of_le ha hab
  have hbeq : b - 1 + 1 = b := by omega
  have hshiftAvoid :
      CrossAvoids (a - 1) (b - 1) (sectionOne F) (sectionOne G) := by
    rw [← haeq, ← hbeq] at havoid
    exact sectionOne_sectionOne_avoids havoid
  have hsameAvoid :
      CrossAvoids a b (sectionZero F) (sectionZero G ∪ sectionOne G) :=
    sectionZero_union_avoids havoid
  by_cases hfzero : density F = 0
  · right; left
    refine ⟨sectionZero F, sectionZero G ∪ sectionOne G, hsameAvoid, ?_⟩
    have hnonneg := mul_nonneg (density_nonneg (sectionZero F))
      (density_nonneg (sectionZero G ∪ sectionOne G))
    simpa [hfzero] using hnonneg
  by_cases hgzero : density G = 0
  · right; left
    refine ⟨sectionZero F, sectionZero G ∪ sectionOne G, hsameAvoid, ?_⟩
    have hnonneg := mul_nonneg (density_nonneg (sectionZero F))
      (density_nonneg (sectionZero G ∪ sectionOne G))
    simpa [hgzero] using hnonneg
  have hfpos : 0 < density F := lt_of_le_of_ne (density_nonneg F) (Ne.symm hfzero)
  have hgpos : 0 < density G := lt_of_le_of_ne (density_nonneg G) (Ne.symm hgzero)
  let f0 := density (sectionZero F)
  let f1 := density (sectionOne F)
  let g0 := density (sectionZero G)
  let g1 := density (sectionOne G)
  by_cases hshift : (1 + s) * density F * density G ≤ f1 * g1
  · left
    exact ⟨sectionOne F, sectionOne G, hshiftAvoid, hshift⟩
  have hshiftFail : f1 * g1 ≤ (1 + s) * density F * density G :=
    le_of_lt (lt_of_not_ge hshift)
  have hcpos : 0 < 1 + s := by linarith
  have hsmall := small_square_or_of_product hcpos hfpos hgpos
    (density_nonneg (sectionOne F)) (density_nonneg (sectionOne G)) hshiftFail
  rcases hsmall with hsmallF | hsmallG
  · let gu := density (sectionZero G ∪ sectionOne G)
    let gi := density (sectionZero G ∩ sectionOne G)
    have hfsum : f0 + f1 = 2 * density F := density_sections_add F
    have hgsum : gu + gi = 2 * density G := by
      calc
        gu + gi = g0 + g1 := density_union_add_inter _ _
        _ = 2 * density G := density_sections_add G
    have horder : gi ≤ gu :=
      (density_inter_le_left (sectionZero G) (sectionOne G)).trans
        (density_union_ge_left (sectionZero G) (sectionOne G))
    by_cases hgood : (1 + s) * density F * density G ≤ f0 * gu
    · right; left
      exact ⟨sectionZero F, sectionZero G ∪ sectionOne G, hsameAvoid, hgood⟩
    · right; right
      have hwidenAvoid :
          CrossAvoids (a - 1) b (sectionOne F)
            (sectionZero G ∩ sectionOne G) := by
        have hab' : a - 1 + 1 ≤ b := by omega
        rw [← haeq] at havoid
        exact sectionOne_inter_avoids hab' havoid
      have hbad := fr_bad_product_of_small_left hs0 hs hfpos hgpos
        (density_nonneg (sectionZero F)) (density_nonneg (sectionOne F))
        (density_nonneg (sectionZero G ∪ sectionOne G))
        (density_nonneg (sectionZero G ∩ sectionOne G))
        hfsum hgsum horder hsmallF (le_of_lt (lt_of_not_ge hgood))
      exact ⟨sectionOne F, sectionZero G ∩ sectionOne G, hwidenAvoid, hbad⟩
  · let fu := density (sectionZero F ∪ sectionOne F)
    let fi := density (sectionZero F ∩ sectionOne F)
    have hgsum : g0 + g1 = 2 * density G := density_sections_add G
    have hfsum : fu + fi = 2 * density F := by
      calc
        fu + fi = f0 + f1 := density_union_add_inter _ _
        _ = 2 * density F := density_sections_add F
    have horder : fi ≤ fu :=
      (density_inter_le_left (sectionZero F) (sectionOne F)).trans
        (density_union_ge_left (sectionZero F) (sectionOne F))
    by_cases hgood : (1 + s) * density G * density F ≤ g0 * fu
    · right; left
      have hsymm := sectionZero_union_avoids (crossAvoids_comm havoid)
      refine ⟨sectionZero G, sectionZero F ∪ sectionOne F, hsymm, ?_⟩
      nlinarith
    · right; right
      have hwidenAvoid :
          CrossAvoids (a - 1) b (sectionOne G)
            (sectionZero F ∩ sectionOne F) := by
        have hab' : a - 1 + 1 ≤ b := by omega
        have hsymmetric := crossAvoids_comm havoid
        rw [← haeq] at hsymmetric
        exact sectionOne_inter_avoids hab' hsymmetric
      have hbad := fr_bad_product_of_small_left hs0 hs hgpos hfpos
        (density_nonneg (sectionZero G)) (density_nonneg (sectionOne G))
        (density_nonneg (sectionZero F ∪ sectionOne F))
        (density_nonneg (sectionZero F ∩ sectionOne F))
        hgsum hfsum horder hsmallG (le_of_lt (lt_of_not_ge hgood))
      refine ⟨sectionOne G, sectionZero F ∩ sectionOne F, hwidenAvoid, ?_⟩
      nlinarith

inductive FRStep (s : ℝ) {m a b : ℕ} (F G : Family (m + 1)) : Type
  | shifted (F' G' : Family m)
      (avoids : CrossAvoids (a - 1) (b - 1) F' G')
      (gain : (1 + s) * density F * density G ≤ density F' * density G')
  | same (F' G' : Family m)
      (avoids : CrossAvoids a b F' G')
      (gain : (1 + s) * density F * density G ≤ density F' * density G')
  | widened (F' G' : Family m)
      (avoids : CrossAvoids (a - 1) b F' G')
      (gain : (1 - s - 2 * s ^ 2) * density F * density G ≤ density F' * density G')

noncomputable def fr_one_step_data {m a b : ℕ} {F G : Family (m + 1)} {s : ℝ}
    (hs0 : 0 ≤ s) (hs : s ≤ 1 / 10) (ha : 0 < a) (hab : a ≤ b)
    (havoid : CrossAvoids a b F G) : FRStep s (a := a) (b := b) F G :=
  Classical.choice <| by
    rcases fr_one_step hs0 hs ha hab havoid with hshift | hsame | hwiden
    · obtain ⟨F', G', hav, hgain⟩ := hshift
      exact ⟨FRStep.shifted F' G' hav hgain⟩
    · obtain ⟨F', G', hav, hgain⟩ := hsame
      exact ⟨FRStep.same F' G' hav hgain⟩
    · obtain ⟨F', G', hav, hgain⟩ := hwiden
      exact ⟨FRStep.widened F' G' hav hgain⟩

/-- The data carried by a complete iteration path.  `A` counts good steps,
`B` counts widening steps, and `d` counts the good steps which shift the
forbidden interval. -/
structure FRResult (s : ℝ) {m a b : ℕ} (F G : Family m) where
  m' : ℕ
  A : ℕ
  B : ℕ
  d : ℕ
  a' : ℕ
  b' : ℕ
  F' : Family m'
  G' : Family m'
  steps : m' + A + B = m
  shifts : d ≤ A
  upper : b' + d = b
  lower : a' + B + d = a
  interval : a' ≤ b' ∧ b' ≤ m'
  terminal : a' = 0 ∨ b' = m'
  avoids : CrossAvoids a' b' F' G'
  density_gain :
    (1 + s) ^ A * (1 - s - 2 * s ^ 2) ^ B * density F * density G ≤
      density F' * density G'

/-- Iterating `fr_one_step` must reach an endpoint of the interval. -/
noncomputable def fr_iterate {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ 1 / 10) :
    ∀ {m a b : ℕ} (F G : Family m), a ≤ b → b ≤ m → CrossAvoids a b F G →
      FRResult s (a := a) (b := b) F G := by
  have hq0 : 0 ≤ 1 - s - 2 * s ^ 2 := by nlinarith [sq_nonneg s]
  intro m
  induction m with
  | zero =>
      intro a b F G hab hbm havoid
      have ha0 : a = 0 := by omega
      have hb0 : b = 0 := by omega
      exact
        { m' := 0, A := 0, B := 0, d := 0, a' := a, b' := b
          F' := F, G' := G
          steps := by omega
          shifts := by omega
          upper := by omega
          lower := by omega
          interval := ⟨by omega, by omega⟩
          terminal := Or.inl ha0
          avoids := havoid
          density_gain := by simp }
  | succ k ih =>
      intro a b F G hab hbm havoid
      by_cases ha0 : a = 0
      · exact
          { m' := k + 1, A := 0, B := 0, d := 0, a' := a, b' := b
            F' := F, G' := G
            steps := by omega
            shifts := by omega
            upper := by omega
            lower := by omega
            interval := ⟨hab, hbm⟩
            terminal := Or.inl ha0
            avoids := havoid
            density_gain := by simp }
      by_cases hbm' : b = k + 1
      · exact
          { m' := k + 1, A := 0, B := 0, d := 0, a' := a, b' := b
            F' := F, G' := G
            steps := by omega
            shifts := by omega
            upper := by omega
            lower := by omega
            interval := ⟨hab, hbm⟩
            terminal := Or.inr hbm'
            avoids := havoid
            density_gain := by simp }
      have hak : 0 < a := Nat.pos_of_ne_zero ha0
      have hbk : b ≤ k := by omega
      rcases fr_one_step_data hs0 hs hak hab havoid with
        ⟨F1, G1, havoid1, hgain1⟩ | ⟨F1, G1, havoid1, hgain1⟩ |
          ⟨F1, G1, havoid1, hgain1⟩
      ·
        have hab1 : a - 1 ≤ b - 1 := Nat.sub_le_sub_right hab 1
        have hres := ih (a := a - 1) (b := b - 1) F1 G1 hab1 (by omega) havoid1
        exact
          { m' := hres.m', A := hres.A + 1, B := hres.B, d := hres.d + 1
            a' := hres.a', b' := hres.b', F' := hres.F', G' := hres.G'
            steps := by have h := hres.steps; omega
            shifts := by have h := hres.shifts; omega
            upper := by have h := hres.upper; omega
            lower := by have h := hres.lower; omega
            interval := hres.interval
            terminal := hres.terminal
            avoids := hres.avoids
            density_gain := by
              calc
                (1 + s) ^ (hres.A + 1) * (1 - s - 2 * s ^ 2) ^ hres.B *
                      density F * density G =
                    ((1 + s) ^ hres.A * (1 - s - 2 * s ^ 2) ^ hres.B) *
                      ((1 + s) * density F * density G) := by
                        rw [pow_succ]
                        ring
                _ ≤ ((1 + s) ^ hres.A * (1 - s - 2 * s ^ 2) ^ hres.B) *
                      (density F1 * density G1) := by
                        gcongr
                _ ≤ density hres.F' * density hres.G' := by
                  simpa [mul_assoc] using hres.density_gain }
      ·
        have hres := ih (a := a) (b := b) F1 G1 hab hbk havoid1
        exact
          { m' := hres.m', A := hres.A + 1, B := hres.B, d := hres.d
            a' := hres.a', b' := hres.b', F' := hres.F', G' := hres.G'
            steps := by have h := hres.steps; omega
            shifts := hres.shifts.trans (Nat.le_add_right _ _)
            upper := hres.upper
            lower := hres.lower
            interval := hres.interval
            terminal := hres.terminal
            avoids := hres.avoids
            density_gain := by
              calc
                (1 + s) ^ (hres.A + 1) * (1 - s - 2 * s ^ 2) ^ hres.B *
                      density F * density G =
                    ((1 + s) ^ hres.A * (1 - s - 2 * s ^ 2) ^ hres.B) *
                      ((1 + s) * density F * density G) := by
                        rw [pow_succ]
                        ring
                _ ≤ ((1 + s) ^ hres.A * (1 - s - 2 * s ^ 2) ^ hres.B) *
                      (density F1 * density G1) := by
                        gcongr
                _ ≤ density hres.F' * density hres.G' := by
                  simpa [mul_assoc] using hres.density_gain }
      ·
        have hab1 : a - 1 ≤ b := (Nat.sub_le a 1).trans hab
        have hres := ih (a := a - 1) (b := b) F1 G1 hab1 hbk havoid1
        exact
          { m' := hres.m', A := hres.A, B := hres.B + 1, d := hres.d
            a' := hres.a', b' := hres.b', F' := hres.F', G' := hres.G'
            steps := by have h := hres.steps; omega
            shifts := hres.shifts
            upper := hres.upper
            lower := by have h := hres.lower; omega
            interval := hres.interval
            terminal := hres.terminal
            avoids := hres.avoids
            density_gain := by
              calc
                (1 + s) ^ hres.A * (1 - s - 2 * s ^ 2) ^ (hres.B + 1) *
                      density F * density G =
                    ((1 + s) ^ hres.A * (1 - s - 2 * s ^ 2) ^ hres.B) *
                      ((1 - s - 2 * s ^ 2) * density F * density G) := by
                        rw [pow_succ]
                        ring
                _ ≤ ((1 + s) ^ hres.A * (1 - s - 2 * s ^ 2) ^ hres.B) *
                      (density F1 * density G1) := by
                        gcongr
                _ ≤ density hres.F' * density hres.G' := by
                  simpa [mul_assoc] using hres.density_gain }

end Erdos703Iteration
