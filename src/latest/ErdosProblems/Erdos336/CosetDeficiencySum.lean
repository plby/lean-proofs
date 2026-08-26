import ErdosProblems.Erdos336.QuotientImageCard

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos336

open scoped Pointwise BigOperators

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- A finite quotient fibre. -/
noncomputable def quotientFiberFinset
    (K : AddSubgroup G) (A : Finset G) (z : G ⧸ K) : Finset G := by
  classical
  exact A.filter fun x => (QuotientAddGroup.mk' K) x = z

@[simp] theorem mem_quotientFiberFinset
    {K : AddSubgroup G} {A : Finset G} {z : G ⧸ K} {x : G} :
    x ∈ quotientFiberFinset K A z ↔
      x ∈ A ∧ (QuotientAddGroup.mk' K) x = z := by
  classical
  simp [quotientFiberFinset]

/-- Number of missing points from an occupied coset, expressed with an
explicit finite subgroup finset. -/
noncomputable def quotientFiberDeficiency
    (K : AddSubgroup G) (Kfin A : Finset G) (z : G ⧸ K) : ℕ := by
  classical
  exact Kfin.card - (quotientFiberFinset K A z).card

/-- Total occupied-coset deficiency. -/
noncomputable def quotientImage
    (K : AddSubgroup G) (A : Finset G) : Finset (G ⧸ K) := by
  classical
  exact A.image (QuotientAddGroup.mk' K)

noncomputable def quotientDeficiency
    (K : AddSubgroup G) (Kfin A : Finset G) : ℕ := by
  classical
  exact ∑ z ∈ quotientImage K A, quotientFiberDeficiency K Kfin A z

/-- Finite sum of pointwise truncated complements. -/
theorem sum_const_sub_sum_eq_sum_sub
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (c : ℕ) (f : ι → ℕ)
    (hf : ∀ x ∈ S, f x ≤ c) :
    (∑ _x ∈ S, c) - (∑ x ∈ S, f x) = ∑ x ∈ S, (c - f x) := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert x S hx ih =>
      rw [Finset.sum_insert hx, Finset.sum_insert hx,
        Finset.sum_insert hx]
      have hi := ih (fun y hy => hf y (Finset.mem_insert_of_mem hy))
      have hfx := hf x (Finset.mem_insert_self x S)
      have hsum : ∑ y ∈ S, f y ≤ ∑ _y ∈ S, c := by
        exact Finset.sum_le_sum (fun y hy => hf y (Finset.mem_insert_of_mem hy))
      omega

/-- Every quotient fibre injects into the finite subgroup. -/
theorem card_quotient_fiber_le_subgroup
    (K : AddSubgroup G) (Kfin : Finset G)
    (hKfin : ∀ x, x ∈ Kfin ↔ x ∈ K) (A : Finset G) (z : G ⧸ K) :
    (quotientFiberFinset K A z).card ≤ Kfin.card := by
  classical
  by_cases hz : (quotientFiberFinset K A z).Nonempty
  · obtain ⟨a, ha⟩ := hz
    let q : G →+ G ⧸ K := QuotientAddGroup.mk' K
    let f : ↥(quotientFiberFinset K A z) → ↥Kfin := fun x =>
      ⟨x.1 - a, (hKfin _).mpr (by
        apply (QuotientAddGroup.eq_zero_iff (x.1 - a)).mp
        change q (x.1 - a) = 0
        have hxmem : x.1 ∈ A.filter (fun y => q y = z) := by
          simpa [quotientFiberFinset, q] using x.2
        have hxq : q x.1 = z := (Finset.mem_filter.mp hxmem).2
        have hamem : a ∈ A.filter (fun y => q y = z) := by
          simpa [quotientFiberFinset, q] using ha
        have haq : q a = z := (Finset.mem_filter.mp hamem).2
        rw [q.map_sub, hxq, haq, sub_self])⟩
    have hf : Function.Injective f := by
      intro x y hxy
      apply Subtype.ext
      have hv := congrArg (fun k : ↥Kfin => k.1) hxy
      change x.1 - a = y.1 - a at hv
      exact sub_left_injective hv
    simpa [q] using (Fintype.card_le_of_injective f hf)
  · rw [Finset.not_nonempty_iff_eq_empty] at hz
    rw [hz]
    simp

/-- Total deficiency is exactly saturation size minus set size. -/
theorem quotientDeficiency_eq_saturation_sub
    (K : AddSubgroup G) (Kfin : Finset G)
    (hKfin : ∀ x, x ∈ Kfin ↔ x ∈ K) (A : Finset G) :
    quotientDeficiency K Kfin A = (A + Kfin).card - A.card := by
  classical
  let q : G →+ G ⧸ K := QuotientAddGroup.mk' K
  let C := A.image q
  have hpartition : A.card =
      ∑ z ∈ C, (A.filter fun x => q x = z).card := by
    exact Finset.card_eq_sum_card_fiberwise (fun x hx =>
      Finset.mem_image.mpr ⟨x, hx, rfl⟩)
  have hfiberle : ∀ z ∈ C,
      (A.filter fun x => q x = z).card ≤ Kfin.card := by
    intro z hz
    obtain ⟨a, ha, haz⟩ := Finset.mem_image.mp hz
    let f : ↥(A.filter fun x => q x = z) → ↥Kfin := fun x =>
      ⟨x.1 - a, (hKfin _).mpr (by
        apply (QuotientAddGroup.eq_zero_iff (x.1 - a)).mp
        change q (x.1 - a) = 0
        rw [q.map_sub, (Finset.mem_filter.mp x.2).2, haz, sub_self])⟩
    have hf : Function.Injective f := by
      intro x y hxy
      apply Subtype.ext
      have := congrArg (fun k : ↥Kfin => k.1) hxy
      change x.1 - a = y.1 - a at this
      exact sub_left_injective this
    simpa using (Fintype.card_le_of_injective f hf)
  have hsumsub :
      (∑ z ∈ C, Kfin.card) -
          (∑ z ∈ C, (A.filter fun x => q x = z).card) =
        ∑ z ∈ C, (Kfin.card -
          (A.filter fun x => q x = z).card) :=
    sum_const_sub_sum_eq_sum_sub C Kfin.card
      (fun z => (A.filter fun x => q x = z).card) hfiberle
  have hsat := card_add_subgroup_eq_quotient_image_mul K Kfin hKfin A
  calc
    quotientDeficiency K Kfin A =
        ∑ z ∈ C, (Kfin.card -
          (A.filter fun x => q x = z).card) := by
      rfl
    _ = (∑ z ∈ C, Kfin.card) -
          (∑ z ∈ C, (A.filter fun x => q x = z).card) := hsumsub.symm
    _ = C.card * Kfin.card - A.card := by
      rw [← hpartition]
      simp
    _ = (A + Kfin).card - A.card := by rw [hsat]

/-- Number of selected endpoints landing in one quotient fibre. -/
noncomputable def quotientEndpointLoad
    {ι : Type*} [DecidableEq ι]
    (K : AddSubgroup G) (I : Finset ι) (left right : ι → G) (z : G ⧸ K) : ℕ := by
  classical
  exact (I.filter fun i => (QuotientAddGroup.mk' K) (left i) = z).card +
    (I.filter fun i => (QuotientAddGroup.mk' K) (right i) = z).card

/-- Bounding how often each occupied coset is selected bounds the weighted
sum of its deficiencies. -/
theorem weighted_deficiency_le
    {ι : Type*} [DecidableEq ι]
    (K : AddSubgroup G) (Kfin A : Finset G) (I : Finset ι)
    (left right : ι → G)
    (hleft : ∀ i ∈ I, left i ∈ A)
    (hright : ∀ i ∈ I, right i ∈ A)
    (M : ℕ)
    (hload : ∀ z ∈ quotientImage K A,
      quotientEndpointLoad K I left right z ≤ M) :
    (∑ i ∈ I,
        (quotientFiberDeficiency K Kfin A
          ((QuotientAddGroup.mk' K) (left i)) +
        quotientFiberDeficiency K Kfin A
          ((QuotientAddGroup.mk' K) (right i)))) ≤
      M * quotientDeficiency K Kfin A := by
  classical
  let q : G →+ G ⧸ K := QuotientAddGroup.mk' K
  let C := A.image q
  let wgt : G ⧸ K → ℕ := quotientFiberDeficiency K Kfin A
  have hleftMap : ∀ i ∈ I, q (left i) ∈ C := fun i hi =>
    Finset.mem_image.mpr ⟨left i, hleft i hi, rfl⟩
  have hrightMap : ∀ i ∈ I, q (right i) ∈ C := fun i hi =>
    Finset.mem_image.mpr ⟨right i, hright i hi, rfl⟩
  have hleftSum :
      ∑ i ∈ I, wgt (q (left i)) =
        ∑ z ∈ C, (I.filter fun i => q (left i) = z).card * wgt z := by
    rw [← Finset.sum_fiberwise_of_maps_to' hleftMap wgt]
    apply Finset.sum_congr rfl
    intro z hz
    rw [Finset.sum_const_nat]
    intro i hi
    rfl
  have hrightSum :
      ∑ i ∈ I, wgt (q (right i)) =
        ∑ z ∈ C, (I.filter fun i => q (right i) = z).card * wgt z := by
    rw [← Finset.sum_fiberwise_of_maps_to' hrightMap wgt]
    apply Finset.sum_congr rfl
    intro z hz
    rw [Finset.sum_const_nat]
    intro i hi
    rfl
  change (∑ i ∈ I, (wgt (q (left i)) + wgt (q (right i)))) ≤
    M * quotientDeficiency K Kfin A
  have hsplit :
      (∑ i ∈ I, (wgt (q (left i)) + wgt (q (right i)))) =
      (∑ i ∈ I, wgt (q (left i))) +
        (∑ i ∈ I, wgt (q (right i))) := by
    exact Finset.sum_add_distrib
      (s := I) (f := fun i => wgt (q (left i)))
      (g := fun i => wgt (q (right i)))
  rw [hsplit, hleftSum, hrightSum]
  rw [← Finset.sum_add_distrib
    (s := C)
    (f := fun z => (I.filter (fun i => q (left i) = z)).card * wgt z)
    (g := fun z => (I.filter (fun i => q (right i) = z)).card * wgt z)]
  calc
    (∑ z ∈ C,
        ((I.filter (fun i => q (left i) = z)).card * wgt z +
          (I.filter (fun i => q (right i) = z)).card * wgt z)) =
      ∑ z ∈ C,
        ((I.filter (fun i => q (left i) = z)).card +
         (I.filter (fun i => q (right i) = z)).card) * wgt z := by
      apply Finset.sum_congr rfl
      intro z hz
      ring
    _ ≤ ∑ z ∈ C, M * wgt z := by
      apply Finset.sum_le_sum
      intro z hz
      exact Nat.mul_le_mul_right (wgt z) (by
        apply hload z
        simpa [quotientImage, C, q] using hz)
    _ = M * quotientDeficiency K Kfin A := by
      change (∑ z ∈ C, M * wgt z) = M * (∑ z ∈ C, wgt z)
      rw [Finset.mul_sum]

end Erdos336
