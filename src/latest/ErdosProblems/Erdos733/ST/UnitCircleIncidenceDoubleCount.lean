import ErdosProblems.Erdos733.ST.UnitCircleIncidenceCount
import ErdosProblems.Erdos733.ST.UnitCircle
import ErdosProblems.Erdos733.ST.unitDist

open Classical
noncomputable section

-- [TABLET NODE: UnitCircleIncidenceDoubleCount]
lemma UnitCircleIncidenceDoubleCount (P : Finset (EuclideanSpace ℝ (Fin 2))) :
    UnitCircleIncidenceCount P = 2 * unitDist P := by
-- BODY
  let E : Finset (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) :=
    P.offDiag.filter (fun pq => dist pq.1 pq.2 = 1)
  have hsets :
      ((P.product P).filter (fun pq => pq.2 ∈ UnitCircle pq.1)) = E := by
    ext pq
    constructor
    · intro hpq
      rcases Finset.mem_filter.mp hpq with ⟨hpqprod, hpqcircle⟩
      rcases Finset.mem_product.mp hpqprod with ⟨hp, hq⟩
      have hdist : dist pq.1 pq.2 = 1 := by
        simpa [UnitCircle, dist_comm] using hpqcircle
      have hne : pq.1 ≠ pq.2 := by
        intro hdiag
        have hzero_one : (0 : ℝ) = 1 := by
          rw [hdiag, dist_self] at hdist
          exact hdist
        norm_num at hzero_one
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_offDiag.mpr ⟨hp, hq, hne⟩, hdist⟩
    · intro hpq
      rcases Finset.mem_filter.mp hpq with ⟨hpqoff, hpqdist⟩
      rcases Finset.mem_offDiag.mp hpqoff with ⟨hp, hq, _hne⟩
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨hp, hq⟩, by
          simpa [UnitCircle, dist_comm] using hpqdist⟩
  have htwo_dvd : 2 ∣ E.card := by
    let σ : Equiv.Perm {pq // pq ∈ E} := {
      toFun x := ⟨(x.1.2, x.1.1), by
        rcases Finset.mem_filter.mp x.2 with ⟨hxoff, hxdist⟩
        rcases Finset.mem_offDiag.mp hxoff with ⟨hp, hq, hne⟩
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_offDiag.mpr ⟨hq, hp, hne.symm⟩, by
            simpa [dist_comm] using hxdist⟩⟩
      invFun x := ⟨(x.1.2, x.1.1), by
        rcases Finset.mem_filter.mp x.2 with ⟨hxoff, hxdist⟩
        rcases Finset.mem_offDiag.mp hxoff with ⟨hp, hq, hne⟩
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_offDiag.mpr ⟨hq, hp, hne.symm⟩, by
            simpa [dist_comm] using hxdist⟩⟩
      left_inv x := by
        ext <;> rfl
      right_inv x := by
        ext <;> rfl
    }
    have hσsq : σ ^ 2 = 1 := by
      ext x <;> rfl
    have hsupport_univ : σ.support = Finset.univ := by
      ext x
      rw [Equiv.Perm.mem_support]
      simp only [Finset.mem_univ, iff_true]
      intro hxfix
      have hval : (x.1.2, x.1.1) = x.1 := congrArg Subtype.val hxfix
      have hswap : x.1.2 = x.1.1 := congrArg Prod.fst hval
      have hxoff : x.1 ∈ P.offDiag := (Finset.mem_filter.mp x.2).1
      have hne : x.1.1 ≠ x.1.2 := (Finset.mem_offDiag.mp hxoff).2.2
      exact hne hswap.symm
    have hsupp_dvd : 2 ∣ σ.support.card :=
      Equiv.Perm.two_dvd_card_support hσsq
    rw [hsupport_univ, Finset.card_univ, Fintype.card_coe] at hsupp_dvd
    exact hsupp_dvd
  unfold UnitCircleIncidenceCount unitDist
  rw [hsets]
  exact (Nat.mul_div_cancel' htwo_dvd).symm
