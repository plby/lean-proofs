import ErdosProblems.Erdos360.LevCompletion

/-!
# List sums used in Lev's increment theorem

This file records the elementary list-level bookkeeping used by the
modular-fibre proof of Lev's multiple-summand increment theorem.  The empty
sum is the singleton `{0}`.  Thus all recursive identities continue to hold
without separate conventions at the first summand.
-/

open scoped Pointwise

namespace Erdos360

attribute [local instance] Classical.propDecidable

/-- The Minkowski sum of a finite list of finite sets. -/
def levFinsetSum {G : Type*} [AddCommMonoid G] [DecidableEq G] :
    List (Finset G) → Finset G
  | [] => {0}
  | A :: parts => A + levFinsetSum parts

@[simp] lemma levFinsetSum_nil
    {G : Type*} [AddCommMonoid G] [DecidableEq G] :
    levFinsetSum ([] : List (Finset G)) = {0} := rfl

@[simp] lemma levFinsetSum_cons
    {G : Type*} [AddCommMonoid G] [DecidableEq G]
    (A : Finset G) (parts : List (Finset G)) :
    levFinsetSum (A :: parts) = A + levFinsetSum parts := rfl

private lemma singleton_zero_add
    {G : Type*} [AddCommMonoid G] [DecidableEq G] (S : Finset G) :
    ({0} : Finset G) + S = S := by
  ext x
  constructor
  · intro hx
    obtain ⟨z, hz, s, hs, hzs⟩ := Finset.mem_add.mp hx
    simp only [Finset.mem_singleton] at hz
    subst z
    rw [← hzs]
    simpa using hs
  · intro hx
    exact Finset.mem_add.mpr ⟨0, by simp, x, hx, by simp⟩

private lemma add_singleton_zero
    {G : Type*} [AddCommMonoid G] [DecidableEq G] (S : Finset G) :
    S + ({0} : Finset G) = S := by
  rw [add_comm]
  exact singleton_zero_add S

/-- List concatenation becomes Minkowski addition. -/
lemma levFinsetSum_append
    {G : Type*} [AddCommMonoid G] [DecidableEq G]
    (left right : List (Finset G)) :
    levFinsetSum (left ++ right) =
      levFinsetSum left + levFinsetSum right := by
  induction left with
  | nil =>
      simp only [List.nil_append, levFinsetSum]
      exact (singleton_zero_add _).symm
  | cons A left ih =>
      simp only [List.cons_append, levFinsetSum, ih]
      rw [add_assoc]

@[simp] lemma levFinsetSum_singleton
    {G : Type*} [AddCommMonoid G] [DecidableEq G] (A : Finset G) :
    levFinsetSum [A] = A := by
  simp only [levFinsetSum]
  exact add_singleton_zero A

/-- A Minkowski list sum is nonempty when every summand is nonempty. -/
lemma levFinsetSum_nonempty
    {G : Type*} [AddCommMonoid G] [DecidableEq G]
    {parts : List (Finset G)}
    (hne : ∀ A ∈ parts, A.Nonempty) :
    (levFinsetSum parts).Nonempty := by
  induction parts with
  | nil => simp [levFinsetSum]
  | cons A parts ih =>
      rw [levFinsetSum_cons, Finset.add_nonempty]
      refine ⟨hne A (by simp), ih ?_⟩
      intro B hB
      exact hne B (by simp [hB])

/-- Iterated Cauchy--Davenport in the ordered torsion-free monoid `ℕ`.
There is exactly one unit of possible overlap at each merge. -/
theorem sum_card_le_card_levFinsetSum_add
    (parts : List (Finset ℕ))
    (hne : ∀ A ∈ parts, A.Nonempty) :
    (parts.map Finset.card).sum ≤
      (levFinsetSum parts).card + (parts.length - 1) := by
  induction parts with
  | nil => simp [levFinsetSum]
  | cons A parts ih =>
      have hAne : A.Nonempty := hne A (by simp)
      by_cases hparts : parts = []
      · subst parts
        simp [levFinsetSum]
      · have htail : ∀ B ∈ parts, B.Nonempty := by
          intro B hB
          exact hne B (by simp [hB])
        have htailne : (levFinsetSum parts).Nonempty :=
          levFinsetSum_nonempty htail
        have hcauchy :=
          cauchy_davenport_add_of_linearOrder_isCancelAdd hAne htailne
        have hcauchy' :
            A.card + (levFinsetSum parts).card ≤
              (A + levFinsetSum parts).card + 1 := by
          have hApos : 0 < A.card := Finset.card_pos.mpr hAne
          have htailpos : 0 < (levFinsetSum parts).card :=
            Finset.card_pos.mpr htailne
          omega
        have ih' := ih htail
        simp only [List.map_cons, List.sum_cons, List.length_cons,
          levFinsetSum_cons]
        have hlenpos : 0 < parts.length := by
          cases parts with
          | nil => exact (hparts rfl).elim
          | cons B rest => simp
        omega

/-- Reduction modulo `v` commutes with a finite Minkowski sum. -/
lemma modImage_levFinsetSum (parts : List (Finset ℕ)) (v : ℕ) :
    Erdos13Additive.modImage (levFinsetSum parts) v =
      levFinsetSum (parts.map fun A ↦ Erdos13Additive.modImage A v) := by
  induction parts with
  | nil =>
      ext x
      simp [levFinsetSum, Erdos13Additive.modImage]
  | cons A parts ih =>
      simp only [levFinsetSum_cons, List.map_cons]
      rw [Erdos13Additive.modImage_add, ih]

/-- The list sum of subset-sum sets is the previously defined Lev sum. -/
lemma levFinsetSum_subsetSums (parts : List (Finset ℕ)) :
    levFinsetSum (parts.map Finset.subsetSum) =
      levIteratedSubsetSum parts := by
  induction parts with
  | nil => rfl
  | cons A parts ih =>
      simp only [List.map_cons, levFinsetSum_cons,
        levIteratedSubsetSum, ih]

/-! ## Chosen modular fibers -/

/-- The sum of a list of chosen residue classes. -/
def levChoiceSum {v : ℕ} : List (Finset ℕ × ZMod v) → ZMod v
  | [] => 0
  | (_, a) :: choices => a + levChoiceSum choices

/-- Restrict every integer summand to the chosen coset of `H`. -/
def levChosenFibers {v : ℕ} (H : Finset (ZMod v)) :
    List (Finset ℕ × ZMod v) → List (Finset ℕ)
  | [] => []
  | (A, a) :: choices =>
      Erdos13Additive.residueFiberSet A v (a +ᵥ H) ::
        levChosenFibers H choices

@[simp] lemma length_levChosenFibers {v : ℕ} (H : Finset (ZMod v))
    (choices : List (Finset ℕ × ZMod v)) :
    (levChosenFibers H choices).length = choices.length := by
  induction choices with
  | nil => rfl
  | cons choice choices ih =>
      rcases choice with ⟨A, a⟩
      simp [levChosenFibers, ih]

/-- A chosen residue represented by each summand makes every chosen fiber
nonempty. -/
lemma levChosenFibers_nonempty
    {v : ℕ} {H : Finset (ZMod v)}
    {choices : List (Finset ℕ × ZMod v)}
    (hzero : (0 : ZMod v) ∈ H)
    (hchoice : ∀ choice ∈ choices,
      choice.2 ∈ Erdos13Additive.modImage choice.1 v) :
    ∀ R ∈ levChosenFibers H choices, R.Nonempty := by
  intro R hR
  induction choices with
  | nil => simp [levChosenFibers] at hR
  | cons choice choices ih =>
      rcases choice with ⟨A, a⟩
      simp only [levChosenFibers, List.mem_cons] at hR
      rcases hR with rfl | hR
      · obtain ⟨x, hxA, hxa⟩ := Erdos13Additive.mem_modImage.mp
          (hchoice (A, a) (by simp))
        refine ⟨x, Erdos13Additive.mem_residueFiberSet.mpr ⟨hxA, ?_⟩⟩
        apply Finset.mem_vadd_finset.mpr
        refine ⟨0, hzero, ?_⟩
        simpa using hxa.symm
      · apply ih
        · intro choice hmem
          exact hchoice choice (by simp [hmem])
        · exact hR

/-- Adding chosen fibers stays in the coset obtained by adding their chosen
residues.  This is the list-level bridge from the individual saturation
estimates to the exceptional output fiber in the refined lift. -/
lemma levFinsetSum_chosenFibers_subset
    {v : ℕ} {H : Finset (ZMod v)}
    (hzero : (0 : ZMod v) ∈ H)
    (hadd : ∀ x ∈ H, ∀ y ∈ H, x + y ∈ H) :
    ∀ choices : List (Finset ℕ × ZMod v),
      levFinsetSum (levChosenFibers H choices) ⊆
        Erdos13Additive.residueFiberSet
          (levFinsetSum (choices.map Prod.fst)) v
          (levChoiceSum choices +ᵥ H) := by
  intro choices
  induction choices with
  | nil =>
      intro z hz
      simp only [levChosenFibers, levFinsetSum_nil,
        List.map_nil, levChoiceSum] at hz ⊢
      have hz0 : z = 0 := by simpa using hz
      subst z
      apply Erdos13Additive.mem_residueFiberSet.mpr
      refine ⟨by simp, ?_⟩
      apply Finset.mem_vadd_finset.mpr
      exact ⟨0, hzero, by simp⟩
  | cons choice choices ih =>
      rcases choice with ⟨A, a⟩
      intro z hz
      simp only [levChosenFibers, levFinsetSum_cons,
        List.map_cons, levChoiceSum] at hz ⊢
      obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.mp hz
      have hy' := ih hy
      have hx' := Erdos13Additive.mem_residueFiberSet.mp hx
      have hy'' := Erdos13Additive.mem_residueFiberSet.mp hy'
      obtain ⟨h₁, hh₁, ha⟩ := Finset.mem_vadd_finset.mp hx'.2
      obtain ⟨h₂, hh₂, hb⟩ := Finset.mem_vadd_finset.mp hy''.2
      apply Erdos13Additive.mem_residueFiberSet.mpr
      refine ⟨Finset.add_mem_add hx'.1 hy''.1, ?_⟩
      apply Finset.mem_vadd_finset.mpr
      refine ⟨h₁ + h₂, hadd h₁ hh₁ h₂ hh₂, ?_⟩
      change (a + levChoiceSum choices) + (h₁ + h₂) =
        (((x + y : ℕ) : ZMod v))
      push_cast
      change a + h₁ = (x : ZMod v) at ha
      change levChoiceSum choices + h₂ = (y : ZMod v) at hb
      rw [← ha, ← hb]
      abel

/-- The combined saturation/fiber inequality used in Lev's refined lift.
Each modular image is saturated by `H`; the overcount is paid for by the
corresponding chosen integer fiber.  Iterated Cauchy--Davenport loses only
one point per merge. -/
theorem sum_modImage_card_add_mul_card_le_saturation_add_fiber
    {v : ℕ} {H : Finset (ZMod v)}
    {choices : List (Finset ℕ × ZMod v)} {F : Finset ℕ}
    (hzero : (0 : ZMod v) ∈ H)
    (hchoice : ∀ choice ∈ choices,
      choice.2 ∈ Erdos13Additive.modImage choice.1 v)
    (hF : levFinsetSum (levChosenFibers H choices) ⊆ F) :
    (choices.map fun choice ↦
        (Erdos13Additive.modImage choice.1 v).card).sum +
        choices.length * H.card ≤
      (choices.map fun choice ↦
        (Erdos13Additive.modImage choice.1 v + H).card).sum +
        F.card + (choices.length - 1) := by
  have hsat :
      (choices.map fun choice ↦
          (Erdos13Additive.modImage choice.1 v).card).sum +
          choices.length * H.card ≤
          (choices.map fun choice ↦
          (Erdos13Additive.modImage choice.1 v + H).card).sum +
          ((levChosenFibers H choices).map Finset.card).sum := by
    clear hF
    induction choices with
    | nil => simp [levChosenFibers]
    | cons choice choices ih =>
        rcases choice with ⟨A, a⟩
        have ha : a ∈ Erdos13Additive.modImage A v :=
          hchoice (A, a) (by simp)
        have hhead :=
          Erdos13Additive.card_modImage_add_card_le_saturation_add_fiber
            hzero ha
        have htail : ∀ choice ∈ choices,
            choice.2 ∈ Erdos13Additive.modImage choice.1 v := by
          intro choice hmem
          exact hchoice choice (by simp [hmem])
        have ih' := ih htail
        simp only [List.map_cons, List.sum_cons, List.length_cons,
          levChosenFibers, Nat.add_mul, one_mul] at ih' ⊢
        have hcombine := Nat.add_le_add hhead ih'
        omega
  have hne : ∀ R ∈ levChosenFibers H choices, R.Nonempty :=
    levChosenFibers_nonempty hzero hchoice
  have hcauchy :=
    sum_card_le_card_levFinsetSum_add (levChosenFibers H choices) hne
  have hcardF : (levFinsetSum (levChosenFibers H choices)).card ≤ F.card :=
    Finset.card_le_card hF
  rw [length_levChosenFibers] at hcauchy
  omega

/-! ## Generalized Kneser with the final stabilizer -/

/-- Generalized Kneser's inequality for a finite list of nonempty summands.
Every summand is saturated by the stabilizer of the *total* sum.  The proof
merges the first two summands and uses binary Kneser, thereby avoiding any
choice of an order in which intermediate stabilizers grow. -/
theorem sum_card_add_addStab_le_card_levFinsetSum_add
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    (parts : List (Finset G))
    (hne : ∀ A ∈ parts, A.Nonempty) :
    let H := (levFinsetSum parts).addStab
    (parts.map fun A ↦ (A + H).card).sum ≤
      (levFinsetSum parts).card +
        (parts.length - 1) * H.card := by
  induction hlen : parts.length using Nat.strong_induction_on generalizing parts with
  | h n ih =>
      subst n
      cases parts with
      | nil => simp [levFinsetSum]
      | cons A tail =>
          cases tail with
          | nil =>
              simp only [levFinsetSum_singleton, List.map_cons, List.map_nil,
                List.sum_cons, List.sum_nil, List.length_cons, List.length_nil,
                Nat.reduceAdd, Nat.reduceSub, Nat.zero_mul, add_zero]
              rw [Finset.add_addStab]
          | cons B rest =>
              let T := levFinsetSum (A :: B :: rest)
              let H := T.addStab
              let C := A + B
              let R := levFinsetSum rest
              have hA : A.Nonempty := hne A (by simp)
              have hB : B.Nonempty := hne B (by simp)
              have hrest : ∀ D ∈ rest, D.Nonempty := by
                intro D hD
                exact hne D (by simp [hD])
              have hR : R.Nonempty := levFinsetSum_nonempty hrest
              have hC : C.Nonempty := Finset.add_nonempty.mpr ⟨hA, hB⟩
              have hT : T = C + R := by
                simp only [T, C, R, levFinsetSum]
                rw [add_assoc]
              have hHH : H + H = H := by
                dsimp only [H]
                exact Finset.addStab_add_addStab T
              have hTH : T + H = T := by
                dsimp only [H]
                exact Finset.add_addStab T
              have hstab : (C + H).addStab = H := by
                apply Finset.Subset.antisymm
                · have hs := Finset.subset_addStab_add_left (s := C + H) hR
                  change (C + H).addStab ⊆ ((C + H) + R).addStab at hs
                  have heq : (C + H) + R = T := by
                    calc
                      (C + H) + R = (C + R) + H := by ac_rfl
                      _ = T + H := by rw [hT]
                      _ = T := hTH
                  rw [heq] at hs
                  simpa [H] using hs
                · have hs := Finset.subset_addStab_add_right (s := C) (t := H) hC
                  change H.addStab ⊆ (C + H).addStab at hs
                  simpa [H] using hs
              have hpair :
                  (A + H).card + (B + H).card ≤
                    (C + H).card + H.card := by
                have hk := Finset.add_kneser (A + H) (B + H)
                have hsum : (A + H) + (B + H) = C + H := by
                  dsimp only [C]
                  rw [add_add_add_comm, hHH]
                rw [hsum, hstab] at hk
                simpa only [add_assoc, hHH] using hk
              have hmergedParts : ∀ D ∈ C :: rest, D.Nonempty := by
                intro D hD
                simp only [List.mem_cons] at hD
                rcases hD with rfl | hD
                · exact hC
                · exact hrest D hD
              have hlenlt : (C :: rest).length < (A :: B :: rest).length := by
                simp
              have hrec := ih (C :: rest).length hlenlt (C :: rest)
                hmergedParts rfl
              have hmerge : levFinsetSum (C :: rest) = T := by
                simp only [T, C, levFinsetSum]
                rw [add_assoc]
              rw [hmerge] at hrec
              have hrec' :
                  (C + H).card +
                      (rest.map fun D ↦ (D + H).card).sum ≤
                    T.card + rest.length * H.card := by
                simpa only [H, List.map_cons, List.sum_cons, List.length_cons,
                  Nat.add_sub_cancel] using hrec
              dsimp only
              change (A + H).card +
                  ((B + H).card +
                    (rest.map fun D ↦ (D + H).card).sum) ≤
                T.card + ((A :: B :: rest).length - 1) * H.card
              simp only [List.length_cons, Nat.add_sub_cancel, Nat.add_mul,
                one_mul]
              omega

end Erdos360
