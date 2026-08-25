import Util.IncidenceGeometry.UnitCircle
import Util.IncidenceGeometry.UnitCircleCyclicAngleData

open Classical
noncomputable section

lemma UnitCircleCyclicAngleArcRealization
    (p : EuclideanSpace ℝ (Fin 2))
    (S : Finset (EuclideanSpace ℝ (Fin 2)))
    (D : UnitCircleCyclicAngleData p S) :
    ∃ (carrier arcInterior :
        {x : EuclideanSpace ℝ (Fin 2) // x ∈ S} →
          Set (EuclideanSpace ℝ (Fin 2)))
      (γ :
        (x : {x : EuclideanSpace ℝ (Fin 2) // x ∈ S}) →
          Set.Icc (0 : ℝ) 1 → EuclideanSpace ℝ (Fin 2)),
      (∀ x,
        Continuous (γ x) ∧
          Function.Injective (γ x) ∧
            (∀ t, γ x t ∈ UnitCircle p) ∧
              γ x ⟨0, by simp⟩ = x.1 ∧
                γ x ⟨1, by simp⟩ = (D.succ x).1 ∧
                  carrier x = Set.range (γ x) ∧
                    arcInterior x =
                      Set.range
                        (fun t : {t : ℝ // 0 < t ∧ t < 1} =>
                          γ x ⟨t.1, ⟨le_of_lt t.2.1, le_of_lt t.2.2⟩⟩)) ∧
        (∀ x y : {y : EuclideanSpace ℝ (Fin 2) // y ∈ S},
          y.1 ∉ arcInterior x) ∧
          (∀ x y,
            x ≠ y → arcInterior x ∩ arcInterior y = ∅) := by
  let angle :
      {x : EuclideanSpace ℝ (Fin 2) // x ∈ S} →
        Set.Icc (0 : ℝ) 1 → ℝ :=
    fun x t => (1 - t.1) * D.startAngle x + t.1 * D.endAngle x
  let γ :
      (x : {x : EuclideanSpace ℝ (Fin 2) // x ∈ S}) →
        Set.Icc (0 : ℝ) 1 → EuclideanSpace ℝ (Fin 2) :=
    fun x t =>
      p + WithLp.toLp 2
        (fun i : Fin 2 =>
          if i = 0 then Real.cos (angle x t) else Real.sin (angle x t))
  let carrier :
      {x : EuclideanSpace ℝ (Fin 2) // x ∈ S} →
        Set (EuclideanSpace ℝ (Fin 2)) :=
    fun x => Set.range (γ x)
  let arcInterior :
      {x : EuclideanSpace ℝ (Fin 2) // x ∈ S} →
        Set (EuclideanSpace ℝ (Fin 2)) :=
    fun x =>
      Set.range
        (fun t : {t : ℝ // 0 < t ∧ t < 1} =>
          γ x ⟨t.1, ⟨le_of_lt t.2.1, le_of_lt t.2.2⟩⟩)
  refine ⟨carrier, arcInterior, γ, ?_, ?_, ?_⟩
  · intro x
    have hangle_range :
        ∀ t : Set.Icc (0 : ℝ) 1,
          D.startAngle x ≤ angle x t ∧ angle x t ≤ D.endAngle x := by
      intro t
      have hgap_nonneg : 0 ≤ D.endAngle x - D.startAngle x :=
        sub_nonneg.mpr (le_of_lt (D.gap_pos x))
      have h₁ : angle x t = D.startAngle x + t.1 * (D.endAngle x - D.startAngle x) := by
        simp [angle]
        ring
      constructor
      · rw [h₁]
        nlinarith [mul_nonneg t.2.1 hgap_nonneg]
      · rw [h₁]
        have hmul :
            t.1 * (D.endAngle x - D.startAngle x) ≤
              1 * (D.endAngle x - D.startAngle x) := by
          exact mul_le_mul_of_nonneg_right t.2.2 hgap_nonneg
        nlinarith
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · dsimp [γ]
      apply Continuous.add continuous_const
      exact (PiLp.continuous_toLp 2 _).comp (by
        apply continuous_pi
        intro i
        by_cases hi : i = 0
        · simp [hi, angle]
          continuity
        · simp [hi, angle]
          continuity)
    · intro s t hst
      have hvec :
          (WithLp.toLp 2
              (fun i : Fin 2 =>
                if i = 0 then Real.cos (angle x s) else Real.sin (angle x s)) :
            EuclideanSpace ℝ (Fin 2)) =
          WithLp.toLp 2
              (fun i : Fin 2 =>
                if i = 0 then Real.cos (angle x t) else Real.sin (angle x t)) := by
        apply add_left_cancel (a := p)
        simpa [γ] using hst
      have hcos : Real.cos (angle x s) = Real.cos (angle x t) := by
        simpa using congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z (0 : Fin 2)) hvec
      have hsin : Real.sin (angle x s) = Real.sin (angle x t) := by
        simpa using congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z (1 : Fin 2)) hvec
      have hangle_eq : angle x s = angle x t := by
        have hsrange := hangle_range s
        have htrange := hangle_range t
        have hangle : (angle x s : Real.Angle) = (angle x t : Real.Angle) :=
          Real.Angle.cos_sin_inj hcos hsin
        obtain ⟨_, ⟨n, rfl⟩, hnangle⟩ :=
          (QuotientAddGroup.mk'_eq_mk' _).mp hangle
        simp only at hnangle
        have hnangle' :
            angle x s + (n : ℝ) * (2 * Real.pi) = angle x t := by
          simpa [zsmul_eq_mul] using hnangle
        have hn0 : (n : ℝ) = 0 := by
          by_cases hn : n = 0
          · simp [hn]
          have hn_abs_ge : 1 ≤ |(n : ℝ)| := by
            exact_mod_cast Int.one_le_abs hn
          have hdiff :
              angle x t - angle x s = (n : ℝ) * (2 * Real.pi) := by
            linarith
          have habs_lt : |angle x t - angle x s| < 2 * Real.pi := by
            rw [abs_lt]
            constructor <;> linarith [D.gap_short x]
          have hbig : 2 * Real.pi ≤ |angle x t - angle x s| := by
            rw [hdiff, abs_mul, abs_of_pos Real.two_pi_pos]
            nlinarith [hn_abs_ge, Real.two_pi_pos]
          linarith
        simpa [hn0] using hnangle'
      apply Subtype.ext
      have hgap : D.startAngle x < D.endAngle x := D.gap_pos x
      have hlin :
          (D.endAngle x - D.startAngle x) * s.1 =
            (D.endAngle x - D.startAngle x) * t.1 := by
        nlinarith [hangle_eq]
      exact mul_left_cancel₀ (sub_ne_zero.mpr hgap.ne') hlin
    · intro t
      dsimp [γ, UnitCircle]
      rw [dist_eq_norm]
      simp only [add_sub_cancel_left]
      rw [PiLp.norm_eq_of_L2]
      rw [Fin.sum_univ_two]
      simp [Real.cos_sq_add_sin_sq]
    · simpa [γ, angle] using (D.start_point x).symm
    · simpa [γ, angle] using (D.end_point x).symm
    · simp [carrier]
    · simp [arcInterior]
  · intro x y hy
    rcases hy with ⟨t, ht⟩
    exact D.no_S_in_open_gap x y t.1 t.2.1 t.2.2 ht.symm
  · intro x y hxy
    ext z
    constructor
    · intro hz
      rcases hz with ⟨hxz, hyz⟩
      rcases hxz with ⟨s, rfl⟩
      rcases hyz with ⟨t, hzt⟩
      exact False.elim
        (D.open_gaps_disjoint x y s.1 t.1 hxy s.2.1 s.2.2 t.2.1 t.2.2 hzt.symm)
    · intro hz
      exact False.elim hz
