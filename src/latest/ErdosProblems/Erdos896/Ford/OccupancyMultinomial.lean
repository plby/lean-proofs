/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos896.Ford.Occupancy

/-!
# Multinomial fibers of occupancy profiles

The placements of labelled balls with a fixed occupancy profile form one
orbit under permutations of the balls.  Orbit--stabilizer therefore counts
this fiber by the usual multinomial coefficient.
-/

namespace Erdos896.Ford.Occupancy

open scoped BigOperators

/-- All placements whose box occupancies are prescribed by `b`. -/
def placementsWithOccupancy {v : ℕ} (b : Fin v → ℕ) : Finset (Fin v → Fin v) :=
  Finset.univ.filter fun f ↦ ∀ j, boxOccupancy f j = b j

/-- The finite occupancy vector of a placement. -/
def occupancyVector {v : ℕ} (f : Fin v → Fin v) : Fin v → ℕ :=
  fun j ↦ boxOccupancy f j

/-- The set of occupancy vectors represented in a finite family of
placements. -/
def occupancyVectors {v : ℕ} (S : Finset (Fin v → Fin v)) :
    Finset (Fin v → ℕ) :=
  S.image occupancyVector

@[simp]
theorem mem_placementsWithOccupancy {v : ℕ} {b : Fin v → ℕ}
    {f : Fin v → Fin v} :
    f ∈ placementsWithOccupancy b ↔ ∀ j, boxOccupancy f j = b j := by
  simp [placementsWithOccupancy]

/-- `boxOccupancy` is the `Fintype.card` of the corresponding fiber. -/
theorem boxOccupancy_eq_card_fiber {v : ℕ} (f : Fin v → Fin v) (j : Fin v) :
    boxOccupancy f j = Fintype.card {i // f i = j} := by
  simp [boxOccupancy, Fintype.card_subtype]

/-- Two placements with the same occupancies differ by a permutation of the
labelled balls. -/
noncomputable def permOfSameOccupancy {v : ℕ}
    (f g : Fin v → Fin v)
    (hfg : ∀ j, boxOccupancy f j = boxOccupancy g j) :
    Equiv.Perm (Fin v) :=
  Equiv.ofFiberEquiv fun j ↦
    Fintype.equivOfCardEq
      ((boxOccupancy_eq_card_fiber f j).symm.trans
        ((hfg j).trans (boxOccupancy_eq_card_fiber g j)))

theorem permOfSameOccupancy_map {v : ℕ}
    (f g : Fin v → Fin v)
    (hfg : ∀ j, boxOccupancy f j = boxOccupancy g j) (i : Fin v) :
    g (permOfSameOccupancy f g hfg i) = f i :=
  Equiv.ofFiberEquiv_map _ _

/-- Precomposing a placement by a permutation of the balls does not change
any box occupancy. -/
theorem boxOccupancy_dom_smul {v : ℕ}
    (p : (Equiv.Perm (Fin v))ᵈᵐᵃ) (f : Fin v → Fin v) (j : Fin v) :
    boxOccupancy (p • f) j = boxOccupancy f j := by
  rw [boxOccupancy_eq_card_fiber, boxOccupancy_eq_card_fiber]
  let e : Equiv.Perm (Fin v) := DomMulAct.mk.symm p
  apply Fintype.card_congr
  exact Equiv.subtypeEquiv e fun i ↦ by
    change f (e i) = j ↔ f (e i) = j
    rfl

/-- The orbit of a placement under permutations of the balls consists
exactly of placements having the same occupancy profile. -/
theorem mem_dom_orbit_iff_sameOccupancy {v : ℕ}
    (f g : Fin v → Fin v) :
    g ∈ MulAction.orbit ((Equiv.Perm (Fin v))ᵈᵐᵃ) f ↔
      ∀ j, boxOccupancy g j = boxOccupancy f j := by
  constructor
  · rintro ⟨p, rfl⟩ j
    exact boxOccupancy_dom_smul p f j
  · intro hgf
    let e := permOfSameOccupancy f g (fun j ↦ (hgf j).symm)
    apply MulAction.mem_orbit_symm.mp
    refine MulAction.mem_orbit_iff.mpr ⟨DomMulAct.mk e, ?_⟩
    funext i
    exact permOfSameOccupancy_map f g (fun j ↦ (hgf j).symm) i

/-- The stabilizer of a placement has one symmetric-group factor for each
box fiber. -/
theorem card_dom_stabilizer {v : ℕ} (f : Fin v → Fin v) :
    Nat.card
        (MulAction.stabilizer ((Equiv.Perm (Fin v))ᵈᵐᵃ) f) =
      ∏ j, (boxOccupancy f j).factorial := by
  classical
  rw [Nat.card_congr MulOpposite.opEquiv,
    Nat.card_congr (DomMulAct.stabilizerMulEquiv f).toEquiv,
    Nat.card_pi]
  apply Finset.prod_congr rfl
  intro j hj
  rw [Nat.card_eq_fintype_card, Fintype.card_perm,
    ← boxOccupancy_eq_card_fiber]

/-- Division-free orbit--stabilizer count for a prescribed occupancy
profile.  No consistency assumption on `b` is needed: the reference
placement itself witnesses consistency. -/
theorem card_placementsWithOccupancy_mul_factorial_eq
    {v : ℕ} (b : Fin v → ℕ) (f₀ : Fin v → Fin v)
    (hf₀ : ∀ j, boxOccupancy f₀ j = b j) :
    (placementsWithOccupancy b).card * ∏ j, (b j).factorial = v.factorial := by
  classical
  have hcard :
      (placementsWithOccupancy b).card =
        Nat.card
          (MulAction.orbit ((Equiv.Perm (Fin v))ᵈᵐᵃ) f₀) := by
    calc
      (placementsWithOccupancy b).card =
          Fintype.card (placementsWithOccupancy b) :=
        (Fintype.card_coe _).symm
      _ = Nat.card (placementsWithOccupancy b) :=
        Nat.card_eq_fintype_card.symm
      _ = Nat.card
          (MulAction.orbit ((Equiv.Perm (Fin v))ᵈᵐᵃ) f₀) := by
        apply Nat.card_congr
        apply Equiv.setCongr
        ext g
        simp only [Finset.mem_coe, mem_placementsWithOccupancy]
        rw [mem_dom_orbit_iff_sameOccupancy]
        constructor
        · intro hg j
          exact (hg j).trans (hf₀ j).symm
        · intro hg j
          exact (hg j).trans (hf₀ j)
  have horbit :
      Nat.card (MulAction.orbit ((Equiv.Perm (Fin v))ᵈᵐᵃ) f₀) *
          Nat.card
            (MulAction.stabilizer ((Equiv.Perm (Fin v))ᵈᵐᵃ) f₀) =
        Nat.card ((Equiv.Perm (Fin v))ᵈᵐᵃ) := by
    rw [← Nat.card_prod,
      Nat.card_congr
        (MulAction.orbitProdStabilizerEquivGroup
          ((Equiv.Perm (Fin v))ᵈᵐᵃ) f₀)]
  have hgroup :
      Nat.card ((Equiv.Perm (Fin v))ᵈᵐᵃ) = v.factorial := by
    rw [Nat.card_congr DomMulAct.mk.symm, Nat.card_perm,
      Nat.card_fin]
  rw [hcard]
  rw [card_dom_stabilizer, hgroup] at horbit
  simpa [hf₀] using horbit

/-- Exact multinomial count when a placement realizing the profile is
provided. -/
theorem card_placementsWithOccupancy_eq_multinomial_of_realized
    {v : ℕ} (b : Fin v → ℕ) (f₀ : Fin v → Fin v)
    (hf₀ : ∀ j, boxOccupancy f₀ j = b j) :
    (placementsWithOccupancy b).card = Nat.multinomial Finset.univ b := by
  have hsumOccupancy : ∑ j, boxOccupancy f₀ j = v := by
    simpa [occupancyList, List.sum_ofFn] using sum_occupancyList f₀
  have hsum : ∑ j, b j = v := by
    calc
      ∑ j, b j = ∑ j, boxOccupancy f₀ j := by
        apply Finset.sum_congr rfl
        intro j hj
        exact (hf₀ j).symm
      _ = v := hsumOccupancy
  have hcount := card_placementsWithOccupancy_mul_factorial_eq b f₀ hf₀
  have hmultinomial := Nat.multinomial_spec Finset.univ b
  rw [hsum] at hmultinomial
  apply Nat.mul_left_cancel (Finset.prod_pos fun j hj ↦ Nat.factorial_pos _)
  calc
    (∏ j, (b j).factorial) * (placementsWithOccupancy b).card =
        (placementsWithOccupancy b).card * ∏ j, (b j).factorial :=
      Nat.mul_comm _ _
    _ = v.factorial := hcount
    _ = (∏ j, (b j).factorial) * Nat.multinomial Finset.univ b :=
      hmultinomial.symm

/-- A family of placements is occupancy-invariant when membership depends
only on the vector of box occupancies. -/
def OccupancyInvariant {v : ℕ} (S : Finset (Fin v → Fin v)) : Prop :=
  ∀ ⦃f g : Fin v → Fin v⦄,
    occupancyVector f = occupancyVector g → (f ∈ S ↔ g ∈ S)

/-- Aggregate multinomial identity.  For an occupancy-invariant family,
the reciprocal factorial mass of its distinct profiles is its density among
all `v ^ v` placements measured on the permutation scale `v!`.

This is the form consumed by the weighted profile sum: each profile fiber
has cardinality `v! / ∏ j, b j!`, and occupancy invariance says that a
fiber is either wholly present or wholly absent. -/
theorem sum_inv_profileFactorial_eq_card_div_factorial
    {v : ℕ} (S : Finset (Fin v → Fin v)) (hS : OccupancyInvariant S) :
    ∑ b ∈ occupancyVectors S, (1 : ℝ) / ∏ j, ((b j).factorial : ℝ) =
      (S.card : ℝ) / v.factorial := by
  classical
  have hfiber (b : Fin v → ℕ) (hb : b ∈ occupancyVectors S) :
      (S.filter fun f ↦ occupancyVector f = b).card *
          ∏ j, (b j).factorial = v.factorial := by
    obtain ⟨f₀, hf₀S, hf₀b⟩ := Finset.mem_image.mp hb
    have hf₀ : ∀ j, boxOccupancy f₀ j = b j := by
      intro j
      exact congrFun hf₀b j
    have hfilter :
        S.filter (fun f ↦ occupancyVector f = b) =
          placementsWithOccupancy b := by
      ext f
      simp only [Finset.mem_filter, mem_placementsWithOccupancy]
      constructor
      · exact fun hf j ↦ congrFun hf.2 j
      · intro hf
        have hvec : occupancyVector f₀ = occupancyVector f := by
          funext j
          exact (hf₀ j).trans (hf j).symm
        exact ⟨(hS hvec).mp hf₀S, by
          funext j
          exact hf j⟩
    rw [hfilter]
    exact card_placementsWithOccupancy_mul_factorial_eq b f₀ hf₀
  have hfiberReal (b : Fin v → ℕ) (hb : b ∈ occupancyVectors S) :
      (1 : ℝ) / ∏ j, ((b j).factorial : ℝ) =
        ((S.filter fun f ↦ occupancyVector f = b).card : ℝ) /
          v.factorial := by
    have hprodpos : (0 : ℝ) < ∏ j, ((b j).factorial : ℝ) := by
      positivity
    have hvpos : (0 : ℝ) < v.factorial := by positivity
    apply (div_eq_div_iff hprodpos.ne' hvpos.ne').2
    norm_cast
    simpa [Nat.mul_comm] using (hfiber b hb).symm
  have hcard :
      S.card = ∑ b ∈ occupancyVectors S,
        (S.filter fun f ↦ occupancyVector f = b).card := by
    exact Finset.card_eq_sum_card_fiberwise fun f hf ↦
      Finset.mem_image.mpr ⟨f, hf, rfl⟩
  calc
    ∑ b ∈ occupancyVectors S, (1 : ℝ) / ∏ j, ((b j).factorial : ℝ) =
        ∑ b ∈ occupancyVectors S,
          ((S.filter fun f ↦ occupancyVector f = b).card : ℝ) /
            v.factorial := by
      apply Finset.sum_congr rfl
      intro b hb
      exact hfiberReal b hb
    _ = (∑ b ∈ occupancyVectors S,
          ((S.filter fun f ↦ occupancyVector f = b).card : ℝ)) /
          v.factorial := by
      rw [Finset.sum_div]
    _ = (S.card : ℝ) / v.factorial := by
      norm_cast
      rw [hcard]

end Erdos896.Ford.Occupancy
