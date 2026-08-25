import Mathlib.Algebra.Group.Action.Pointwise.Finset
import Mathlib.GroupTheory.QuotientGroup.Finite
import Mathlib.Tactic

/-!
# Signed products and finite-group concentration

The finite-group argument from the ring-class proof is isolated here so that
it applies to arbitrary quadratic orders without importing the problem axioms.
-/

namespace Bernays

def signedProduct {G : Type*} [CommGroup G] {k : ℕ}
    (sigma : Fin k → Bool) (x : Fin k → G) : G :=
  ∏ i, if sigma i then (x i)⁻¹ else x i

def classSquareSubgroup {G : Type*} [CommGroup G] : Subgroup G :=
  (powMonoidHom 2 : G →* G).range

theorem classSquare_mem {G : Type*} [CommGroup G] (x : G) :
    x ^ 2 ∈ (classSquareSubgroup : Subgroup G) := ⟨x, rfl⟩

section SubsetProductStabilizer

variable {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G]

/-- Left multiplication of a finite subset of a commutative group. -/
def leftMulFinset (a : G) (S : Finset G) : Finset G :=
  S.image fun x => a * x

@[simp] theorem leftMulFinset_one (S : Finset G) :
    leftMulFinset (1 : G) S = S := by
  ext x
  simp [leftMulFinset]

theorem leftMulFinset_mul (a b : G) (S : Finset G) :
    leftMulFinset (a * b) S = leftMulFinset a (leftMulFinset b S) := by
  ext x
  constructor
  · intro hx
    rw [leftMulFinset, Finset.mem_image] at hx
    rcases hx with ⟨y, hy, rfl⟩
    rw [leftMulFinset, Finset.mem_image]
    refine ⟨b * y, ?_, by simp [mul_assoc]⟩
    rw [leftMulFinset, Finset.mem_image]
    exact ⟨y, hy, rfl⟩
  · intro hx
    rw [leftMulFinset, Finset.mem_image] at hx
    rcases hx with ⟨z, hz, rfl⟩
    rw [leftMulFinset, Finset.mem_image] at hz
    rcases hz with ⟨y, hy, rfl⟩
    rw [leftMulFinset, Finset.mem_image]
    exact ⟨y, hy, by simp [mul_assoc]⟩

theorem leftMulFinset_union (a : G) (S T : Finset G) :
    leftMulFinset a (S ∪ T) = leftMulFinset a S ∪ leftMulFinset a T := by
  ext x
  simp only [leftMulFinset, Finset.mem_image, Finset.mem_union]
  constructor
  · rintro ⟨y, hyS | hyT, rfl⟩
    · exact Or.inl ⟨y, hyS, rfl⟩
    · exact Or.inr ⟨y, hyT, rfl⟩
  · rintro (⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩)
    · exact ⟨y, Or.inl hy, rfl⟩
    · exact ⟨y, Or.inr hy, rfl⟩

theorem card_leftMulFinset (a : G) (S : Finset G) :
    (leftMulFinset a S).card = S.card := by
  unfold leftMulFinset
  rw [Finset.card_image_of_injective]
  intro x y hxy
  exact mul_left_cancel hxy

theorem leftMulFinset_injective (a : G) :
    Function.Injective (leftMulFinset a : Finset G → Finset G) := by
  intro S T h
  have h' := congrArg (leftMulFinset a⁻¹) h
  simpa [← leftMulFinset_mul] using h'

/-- The subgroup of multipliers preserving a finite subset. -/
def finsetMulStabilizer (S : Finset G) : Subgroup G where
  carrier := {a | leftMulFinset a S = S}
  one_mem' := leftMulFinset_one S
  mul_mem' := by
    intro a b ha hb
    change leftMulFinset a S = S at ha
    change leftMulFinset b S = S at hb
    change leftMulFinset (a * b) S = S
    rw [leftMulFinset_mul, hb, ha]
  inv_mem' := by
    intro a ha
    change leftMulFinset a S = S at ha
    change leftMulFinset a⁻¹ S = S
    apply leftMulFinset_injective a
    rw [← leftMulFinset_mul]
    simpa [ha]

@[simp] theorem mem_finsetMulStabilizer_iff {S : Finset G} {a : G} :
    a ∈ finsetMulStabilizer S ↔ leftMulFinset a S = S := Iff.rfl

/-- Products of arbitrary sublists, built one coordinate at a time. -/
def subsetProductsList : List G → Finset G
  | [] => {1}
  | a :: l => subsetProductsList l ∪ leftMulFinset a (subsetProductsList l)

@[simp] theorem subsetProductsList_nil :
    subsetProductsList ([] : List G) = {1} := rfl

@[simp] theorem subsetProductsList_cons (a : G) (l : List G) :
    subsetProductsList (a :: l) =
      subsetProductsList l ∪ leftMulFinset a (subsetProductsList l) := rfl

theorem subsetProductsList_nonempty (l : List G) :
    (subsetProductsList l).Nonempty := by
  induction l with
  | nil => simp
  | cons a l ih => exact ih.mono Finset.subset_union_left

/-- The recursive reachable set is exactly the set of products obtained by
choosing any subset of the indexed coordinates. -/
theorem mem_subsetProductsList_ofFn_iff {k : ℕ}
    (x : Fin k → G) (z : G) :
    z ∈ subsetProductsList (List.ofFn x) ↔
      ∃ sigma : Fin k → Bool,
        z = ∏ i, if sigma i then x i else 1 := by
  induction k generalizing z with
  | zero =>
      simp [subsetProductsList]
  | succ k ih =>
      rw [List.ofFn_succ, subsetProductsList_cons, Finset.mem_union]
      constructor
      · intro hz
        rcases hz with hz | hz
        · obtain ⟨sigma, hsigma⟩ :=
            (ih (fun i => x i.succ) z).mp hz
          refine ⟨Fin.cons false sigma, ?_⟩
          rw [Fin.prod_univ_succ]
          simpa using hsigma
        · rw [leftMulFinset, Finset.mem_image] at hz
          rcases hz with ⟨w, hw, hwz⟩
          obtain ⟨sigma, hsigma⟩ :=
            (ih (fun i => x i.succ) w).mp hw
          refine ⟨Fin.cons true sigma, ?_⟩
          rw [Fin.prod_univ_succ]
          simp only [Fin.cons_zero, Fin.cons_succ, if_true]
          rw [← hsigma]
          exact hwz.symm
      · rintro ⟨sigma, rfl⟩
        rw [Fin.prod_univ_succ]
        have htail :
            (∏ i : Fin k, if sigma i.succ then x i.succ else 1) ∈
              subsetProductsList (List.ofFn fun i => x i.succ) := by
          apply (ih (fun i => x i.succ)
            (∏ i : Fin k, if sigma i.succ then x i.succ else 1)).mpr
          exact ⟨fun i => sigma i.succ, rfl⟩
        cases h0 : sigma 0
        · left
          simpa [h0] using htail
        · right
          rw [leftMulFinset, Finset.mem_image]
          refine ⟨∏ i : Fin k, if sigma i.succ then x i.succ else 1, ?_, ?_⟩
          · exact htail
          · simp [h0]

/-- A multiplier stabilizing the old subset-product set continues to
stabilize it after one more coordinate is adjoined. -/
theorem stabilizer_subsetProductsList_mono (a : G) (l : List G) :
    finsetMulStabilizer (subsetProductsList l) ≤
      finsetMulStabilizer (subsetProductsList (a :: l)) := by
  intro g hg
  rw [mem_finsetMulStabilizer_iff] at hg ⊢
  rw [subsetProductsList_cons, leftMulFinset_union, hg]
  rw [← leftMulFinset_mul, mul_comm g a, leftMulFinset_mul, hg]

/-- If adding a coordinate does not enlarge the subset-product set, that
coordinate stabilizes the enlarged set. -/
theorem mem_stabilizer_of_card_subsetProductsList_cons_eq
    (a : G) (l : List G)
    (hcard : (subsetProductsList (a :: l)).card =
      (subsetProductsList l).card) :
    a ∈ finsetMulStabilizer (subsetProductsList (a :: l)) := by
  let S := subsetProductsList l
  let T := subsetProductsList (a :: l)
  have hST : S ⊆ T := by
    dsimp [S, T]
    exact Finset.subset_union_left
  have hTS : T = S := by
    symm
    apply Finset.eq_of_subset_of_card_le hST
    simpa [S, T] using hcard.le
  rw [mem_finsetMulStabilizer_iff]
  change leftMulFinset a T = T
  rw [hTS]
  have haS : leftMulFinset a S ⊆ S := by
    intro z hz
    rw [← hTS]
    dsimp [T, S]
    exact Finset.mem_union_right _ hz
  exact Finset.eq_of_subset_of_card_le haS (by
    rw [card_leftMulFinset])

/-- Number of list coordinates outside a subgroup, with repetitions
counted. -/
noncomputable def countOutsideSubgroup (H : Subgroup G) (l : List G) : ℕ := by
  classical
  exact (l.filter fun a => decide (a ∉ H)).length

@[simp] theorem countOutsideSubgroup_nil (H : Subgroup G) :
    countOutsideSubgroup H ([] : List G) = 0 := by
  simp [countOutsideSubgroup]

theorem countOutsideSubgroup_cons_of_mem (H : Subgroup G)
    (a : G) (l : List G) (ha : a ∈ H) :
    countOutsideSubgroup H (a :: l) = countOutsideSubgroup H l := by
  classical
  simp [countOutsideSubgroup, ha]

theorem countOutsideSubgroup_cons_of_not_mem (H : Subgroup G)
    (a : G) (l : List G) (ha : a ∉ H) :
    countOutsideSubgroup H (a :: l) = countOutsideSubgroup H l + 1 := by
  classical
  simp [countOutsideSubgroup, ha]

/-- Relative to any subgroup containing the stabilizer of the final
subset-product set, fewer than `|R|` coordinates lie outside that subgroup,
where `R` is the final reachable set. -/
theorem length_filter_not_mem_subgroup_lt_card_subsetProductsList
    (l : List G) (H : Subgroup G)
    (hstab : finsetMulStabilizer (subsetProductsList l) ≤ H) :
    countOutsideSubgroup H l < (subsetProductsList l).card := by
  classical
  induction l generalizing H with
  | nil => simp [subsetProductsList]
  | cons a l ih =>
      have hmono := stabilizer_subsetProductsList_mono a l
      have htail : finsetMulStabilizer (subsetProductsList l) ≤ H :=
        hmono.trans hstab
      have ih' := ih H htail
      have hcardle : (subsetProductsList l).card ≤
          (subsetProductsList (a :: l)).card :=
        Finset.card_le_card Finset.subset_union_left
      by_cases ha : a ∈ H
      · rw [countOutsideSubgroup_cons_of_mem H a l ha]
        exact ih'.trans_le hcardle
      · rw [countOutsideSubgroup_cons_of_not_mem H a l ha]
        have hcardlt : (subsetProductsList l).card <
            (subsetProductsList (a :: l)).card := by
          apply lt_of_le_of_ne hcardle
          intro heq
          have hastab := mem_stabilizer_of_card_subsetProductsList_cons_eq
            a l heq.symm
          exact ha (hstab hastab)
        omega

/-- If the reachable subset products do not fill the group, then all but at
most `|G|-1` coordinates lie in one proper stabilizer subgroup. -/
theorem exists_proper_stabilizer_with_few_outside
    (l : List G) (hproper : subsetProductsList l ≠ Finset.univ) :
    ∃ H : Subgroup G, H ≠ ⊤ ∧
      countOutsideSubgroup H l < Fintype.card G := by
  let H := finsetMulStabilizer (subsetProductsList l)
  have hHproper : H ≠ ⊤ := by
    intro htop
    have htrans : ∀ g : G, leftMulFinset g (subsetProductsList l) =
        subsetProductsList l := by
      intro g
      have hg : g ∈ H := by rw [htop]; exact Subgroup.mem_top g
      exact hg
    obtain ⟨z, hz⟩ := subsetProductsList_nonempty l
    have hall : ∀ g : G, g ∈ subsetProductsList l := by
      intro g
      have hgz : g ∈ leftMulFinset (g * z⁻¹)
          (subsetProductsList l) := by
        rw [leftMulFinset, Finset.mem_image]
        refine ⟨z, hz, ?_⟩
        group
      rw [htrans] at hgz
      exact hgz
    apply hproper
    ext g
    simp [hall]
  refine ⟨H, hHproper, ?_⟩
  have hbound := length_filter_not_mem_subgroup_lt_card_subsetProductsList
    l H (le_refl H)
  exact hbound.trans_le (Finset.card_le_univ _)

end SubsetProductStabilizer

section SignedProductConcentration

variable {G : Type*} [CommGroup G]

/-- Product of the coordinate squares selected by a sign pattern. -/
def selectedSquareProduct {k : ℕ}
    (sigma : Fin k → Bool) (x : Fin k → G) : G :=
  ∏ i, if sigma i then x i ^ 2 else 1

theorem signedProduct_mul_selectedSquareProduct {k : ℕ}
    (sigma : Fin k → Bool) (x : Fin k → G) :
    signedProduct sigma x * selectedSquareProduct sigma x = ∏ i, x i := by
  classical
  rw [signedProduct, selectedSquareProduct, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  cases h : sigma i <;> simp [h, pow_two]

theorem signedProduct_eq_iff_selectedSquareProduct_eq {k : ℕ}
    (sigma : Fin k → Bool) (x : Fin k → G) (c : G) :
    signedProduct sigma x = c ↔
      selectedSquareProduct sigma x = (∏ i, x i) / c := by
  have hmul := signedProduct_mul_selectedSquareProduct sigma x
  constructor
  · intro hsigned
    rw [hsigned] at hmul
    calc
      selectedSquareProduct sigma x =
          c⁻¹ * (c * selectedSquareProduct sigma x) := by group
      _ = c⁻¹ * (∏ i, x i) := by rw [hmul]
      _ = (∏ i, x i) / c := by
        rw [div_eq_mul_inv]
        ac_rfl
  · intro hselected
    rw [hselected] at hmul
    calc
      signedProduct sigma x =
          (signedProduct sigma x * ((∏ i, x i) / c)) *
            ((∏ i, x i) / c)⁻¹ := by group
      _ = (∏ i, x i) * ((∏ i, x i) / c)⁻¹ := by rw [hmul]
      _ = c := by
        simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
        calc
          (∏ i, x i) * (c * (∏ i, x i)⁻¹) =
              c * ((∏ i, x i) * (∏ i, x i)⁻¹) := by ac_rfl
          _ = c := by simp

/-- A coordinate square, regarded as an element of the square subgroup. -/
def classSquareElement (x : G) :
    (classSquareSubgroup : Subgroup G) :=
  ⟨x ^ 2, classSquare_mem x⟩

@[simp] theorem classSquareElement_val (x : G) :
    (classSquareElement x : G) = x ^ 2 := rfl

/-- Failure of all sign choices, subject to the necessary square-class
condition, forces all but fewer than `|G²|` coordinate squares into one
proper subgroup of `G²`. -/
theorem exists_proper_squareSubgroup_with_few_coordinates_of_no_signedProduct
    [Fintype G] [DecidableEq G] {k : ℕ}
    (x : Fin k → G) (c : G)
    (hclass :
      (QuotientGroup.mk' (classSquareSubgroup : Subgroup G)) (∏ i, x i) =
        (QuotientGroup.mk' (classSquareSubgroup : Subgroup G)) c)
    (hmiss : ∀ sigma : Fin k → Bool, signedProduct sigma x ≠ c) :
    ∃ H : Subgroup (classSquareSubgroup : Subgroup G), H ≠ ⊤ ∧
      countOutsideSubgroup H
          (List.ofFn fun i => classSquareElement (x i)) <
        Nat.card (classSquareSubgroup : Subgroup G) := by
  classical
  letI : Fintype (classSquareSubgroup : Subgroup G) := Fintype.ofFinite _
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_iff_div_mem] at hclass
  let target : (classSquareSubgroup : Subgroup G) :=
    ⟨(∏ i, x i) / c, hclass⟩
  have htarget : target ∉ subsetProductsList
      (List.ofFn fun i => classSquareElement (x i)) := by
    intro hmem
    obtain ⟨sigma, hsigma⟩ :=
      (mem_subsetProductsList_ofFn_iff
        (fun i => classSquareElement (x i)) target).mp hmem
    have hsigmaVal := congrArg Subtype.val hsigma
    have hselected : selectedSquareProduct sigma x = (∏ i, x i) / c := by
      rw [selectedSquareProduct]
      calc
        (∏ i, if sigma i then x i ^ 2 else 1) =
            ∏ i, ((if sigma i then classSquareElement (x i) else 1 :
              (classSquareSubgroup : Subgroup G)) : G) := by
          apply Finset.prod_congr rfl
          intro i hi
          cases h : sigma i <;> simp [h]
        _ = (∏ i, x i) / c := by
          simpa [target] using hsigmaVal.symm
    exact hmiss sigma
      ((signedProduct_eq_iff_selectedSquareProduct_eq sigma x c).mpr hselected)
  have hproper : subsetProductsList
      (List.ofFn fun i => classSquareElement (x i)) ≠ Finset.univ := by
    intro hall
    exact htarget (by rw [hall]; exact Finset.mem_univ target)
  simpa only [Nat.card_eq_fintype_card] using
    (exists_proper_stabilizer_with_few_outside _ hproper)

end SignedProductConcentration

end Bernays
