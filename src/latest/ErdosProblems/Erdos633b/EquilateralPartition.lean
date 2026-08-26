import ErdosProblems.Erdos633b.TrapezoidLayers

/-! The three-trapezoid partition of an equilateral coordinate triangle. -/

namespace Erdos633b.EquilateralPartition

inductive Piece
  | first | second | third
  deriving DecidableEq

instance : Fintype Piece := ⟨{.first, .second, .third}, by intro k; cases k <;> simp⟩

noncomputable def region (T : Triangle) (q : ℝ) : Piece → Set Plane
  | .first => {p | 0 ≤ T.coord 1 p ∧ 0 ≤ T.coord 2 p ∧ T.coord 2 p ≤ q ∧
      T.coord 1 p + T.coord 2 p ≤ 2 * q}
  | .second => {p | 0 ≤ T.coord 2 p ∧ q ≤ T.coord 1 p ∧
      2 * q ≤ T.coord 1 p + T.coord 2 p ∧ T.coord 1 p + T.coord 2 p ≤ 3 * q}
  | .third => {p | 0 ≤ T.coord 1 p ∧ T.coord 1 p ≤ q ∧ q ≤ T.coord 2 p ∧
      T.coord 1 p + T.coord 2 p ≤ 3 * q}

theorem first_eq_trapezoid (T : Triangle) (q : ℝ) :
    region T q .first = TrapezoidPartition.trapezoidSet T q q := by
  ext p
  simp only [region, TrapezoidPartition.trapezoidSet, TrapezoidPartition.trapezoid,
    Set.mem_ofPred_eq, two_mul]

theorem regions_cover (T : Triangle) (q : ℝ) (hq : 0 < q) :
    (⋃ k : Piece, region T q k) =
      {p | 0 ≤ T.coord 1 p ∧ 0 ≤ T.coord 2 p ∧ T.coord 1 p + T.coord 2 p ≤ 3 * q} := by
  ext p
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨k, hk⟩
    cases k
    · obtain ⟨hs, ht, htq, hsum⟩ := hk
      exact ⟨hs, ht, by linarith⟩
    · obtain ⟨ht, hs, hlo, hsum⟩ := hk
      exact ⟨by linarith, ht, hsum⟩
    · obtain ⟨hs, hsq, ht, hsum⟩ := hk
      exact ⟨hs, by linarith, hsum⟩
  · rintro ⟨hs, ht, hsum⟩
    by_cases htq : T.coord 2 p ≤ q
    · by_cases h : T.coord 1 p + T.coord 2 p ≤ 2 * q
      · exact ⟨.first, hs, ht, htq, h⟩
      · exact ⟨.second, ht, by linarith, le_of_not_ge h, hsum⟩
    · by_cases hsq : T.coord 1 p ≤ q
      · exact ⟨.third, hs, hsq, le_of_not_ge htq, hsum⟩
      · exact ⟨.second, ht, le_of_not_ge hsq, by linarith, hsum⟩

theorem regions_disjoint_interiors (T : Triangle) (q : ℝ) :
    Pairwise fun k l => Disjoint (interior (region T q k)) (interior (region T q l)) := by
  have h01 : Disjoint (interior (region T q .first)) (interior (region T q .second)) := by
    apply Sixty.disjoint_interiors_of_separator T _ _ 1 1 (2 * q) (Or.inl one_ne_zero)
    · intro p hp
      change T.coordForm 1 1 p ≤ 2 * q
      simpa only [Triangle.coordForm_apply, one_mul] using hp.2.2.2
    · intro p hp
      change 2 * q ≤ T.coordForm 1 1 p
      simpa only [Triangle.coordForm_apply, one_mul] using hp.2.2.1
  have h02 : Disjoint (interior (region T q .first)) (interior (region T q .third)) := by
    apply Sixty.disjoint_interiors_of_separator T _ _ 0 1 q (Or.inr one_ne_zero)
    · intro p hp
      change T.coordForm 0 1 p ≤ q
      simpa only [Triangle.coordForm_apply, zero_mul, one_mul, zero_add] using hp.2.2.1
    · intro p hp
      change q ≤ T.coordForm 0 1 p
      simpa only [Triangle.coordForm_apply, zero_mul, one_mul, zero_add] using hp.2.2.1
  have h21 : Disjoint (interior (region T q .third)) (interior (region T q .second)) := by
    apply Sixty.disjoint_interiors_of_separator T _ _ 1 0 q (Or.inl one_ne_zero)
    · intro p hp
      change T.coordForm 1 0 p ≤ q
      simpa only [Triangle.coordForm_apply, zero_mul, one_mul, add_zero] using hp.2.1
    · intro p hp
      change q ≤ T.coordForm 1 0 p
      simpa only [Triangle.coordForm_apply, zero_mul, one_mul, add_zero] using hp.2.1
  intro k l hkl
  cases k <;> cases l
  · exact (hkl rfl).elim
  · exact h01
  · exact h02
  · exact h01.symm
  · exact (hkl rfl).elim
  · exact h21.symm
  · exact h02.symm
  · exact h21
  · exact (hkl rfl).elim

noncomputable def assemble_patch (T R : Triangle) (q : ℝ) (hq : 0 < q) (n : ℕ)
    (d : ∀ k, Patch R (region T q k) n) :
    Patch R (T.homothetic (T.points 0) (3 * q) (mul_pos (by norm_num) hq).ne').support (3 * n) := by
  have result := Patch.glue R (region T q) (fun _ => n) d (regions_disjoint_interiors T q)
  rw [regions_cover T q hq] at result
  have hs : {p | 0 ≤ T.coord 1 p ∧ 0 ≤ T.coord 2 p ∧ T.coord 1 p + T.coord 2 p ≤ 3 * q} =
      (T.homothetic (T.points 0) (3 * q) (mul_pos (by norm_num) hq).ne').support := by
    ext p
    rw [Triangle.mem_homothetic_support T (3 * q) (mul_pos (by norm_num) hq)]
    rfl
  have hc : (∑ _ : Piece, n) = 3 * n := by
    have hu : (Finset.univ : Finset Piece) = {.first, .second, .third} := rfl
    rw [hu]
    simp
  rw [hs, hc] at result
  exact result

noncomputable def assemble (T R : Triangle) (q : ℝ) (hq : 0 < q) (n : ℕ)
    (d : ∀ k, Patch R (region T q k) n) :
    Tiling (T.homothetic (T.points 0) (3 * q) (mul_pos (by norm_num) hq).ne') (3 * n) :=
  (assemble_patch T R q hq n d).toTiling

end Erdos633b.EquilateralPartition
