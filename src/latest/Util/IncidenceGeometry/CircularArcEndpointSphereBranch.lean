import Util.IncidenceGeometry.Basic
import Mathlib.Topology.Order.IntermediateValue

open Classical
noncomputable section


lemma CircularArcEndpointSphereBranch
    {c : EuclideanSpace ℝ (Fin 2)} {r : ℝ}
    {γ : Set.Icc (0 : ℝ) 1 → EuclideanSpace ℝ (Fin 2)}
    (hr : 0 < r) (hγcont : Continuous γ) (hγinj : Function.Injective γ)
    (hcircle : ∀ t, dist (γ t) c = r) :
    ∃ ε₀ ε₁ : ℝ, 0 < ε₀ ∧ 0 < ε₁ ∧
      (∀ {ρ : ℝ}, 0 < ρ → ρ < ε₀ →
        ∃! p : EuclideanSpace ℝ (Fin 2),
          p ∈ Metric.sphere (γ ⟨0, by simp⟩) ρ ∧ p ∈ Set.range γ) ∧
      (∀ {ρ : ℝ}, 0 < ρ → ρ < ε₁ →
        ∃! p : EuclideanSpace ℝ (Fin 2),
          p ∈ Metric.sphere (γ ⟨1, by simp⟩) ρ ∧ p ∈ Set.range γ) := by
  have start_branch :
      ∀ {η : Set.Icc (0 : ℝ) 1 → EuclideanSpace ℝ (Fin 2)},
        Continuous η → Function.Injective η → (∀ t, dist (η t) c = r) →
          ∃ ε : ℝ, 0 < ε ∧
            ∀ {ρ : ℝ}, 0 < ρ → ρ < ε →
              ∃! p : EuclideanSpace ℝ (Fin 2),
                p ∈ Metric.sphere (η ⟨0, by simp⟩) ρ ∧ p ∈ Set.range η := by
    intro η hηcont hηinj hηcircle
    let z : Set.Icc (0 : ℝ) 1 := ⟨0, by simp⟩
    let o : EuclideanSpace ℝ (Fin 2) := η z
    have hsmall :
        ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
          ∀ t : Set.Icc (0 : ℝ) 1, t.1 ≤ δ → dist (η t) o < r := by
      have hcontz := hηcont.continuousAt (x := z)
      have hmetric := (Metric.continuousAt_iff.mp hcontz) r hr
      rcases hmetric with ⟨α, hαpos, hα⟩
      let δ : ℝ := min (α / 2) (1 / 2)
      have hδpos : 0 < δ := lt_min (half_pos hαpos) (by norm_num)
      have hδlt1 : δ < 1 :=
        (min_le_right _ _).trans_lt (by norm_num)
      refine ⟨δ, hδpos, hδlt1, ?_⟩
      intro t ht
      have hdist_sub : dist t z < α := by
        have hdist_eq : dist t z = t.1 := by
          simp [Subtype.dist_eq, z, abs_of_nonneg t.2.1]
        rw [hdist_eq]
        exact ht.trans_lt ((min_le_left _ _).trans_lt (half_lt_self hαpos))
      simpa [dist_comm, z, o] using hα hdist_sub
    rcases hsmall with ⟨δ, hδpos, hδlt1, hδclose⟩
    let aI : Set.Icc (0 : ℝ) 1 := ⟨δ, ⟨le_of_lt hδpos, le_of_lt hδlt1⟩⟩
    let oneI : Set.Icc (0 : ℝ) 1 := ⟨1, by simp⟩
    have hz_le_a : z ≤ aI := by
      change (0 : ℝ) ≤ δ
      exact le_of_lt hδpos
    have ha_le_one : aI ≤ oneI := by
      change δ ≤ (1 : ℝ)
      exact le_of_lt hδlt1
    let side : EuclideanSpace ℝ (Fin 2) → ℝ := fun p =>
      (o 0 - c 0) * (p 1 - c 1) - (o 1 - c 1) * (p 0 - c 0)
    have circle_sq :
        ∀ {a p : EuclideanSpace ℝ (Fin 2)} {R : ℝ}, dist p a = R →
          (p 0 - a 0) ^ 2 + (p 1 - a 1) ^ 2 = R ^ 2 := by
      intro a p R hp
      have hsq : dist p a ^ 2 = R ^ 2 := by rw [hp]
      rw [dist_eq_norm] at hsq
      change ‖p - a‖ ^ 2 = R ^ 2 at hsq
      have hnorm := PiLp.norm_sq_eq_of_L2 (fun _ : Fin 2 => ℝ) (p - a)
      rw [hnorm] at hsq
      norm_num at hsq
      simpa [EuclideanSpace, Fin.sum_univ_two, sub_eq_add_neg, sq] using hsq
    have det_zero_close_eq :
        ∀ {p : EuclideanSpace ℝ (Fin 2)},
          dist p c = r → dist p o < r → side p = 0 → p = o := by
      intro p hpc hpclose hside
      let A : ℝ := o 0 - c 0
      let B : ℝ := o 1 - c 1
      let U : ℝ := p 0 - c 0
      let W : ℝ := p 1 - c 1
      have honorm : A ^ 2 + B ^ 2 = r ^ 2 := by
        simpa [A, B, o] using (circle_sq (hηcircle z))
      have hpnorm : U ^ 2 + W ^ 2 = r ^ 2 := by
        simpa [U, W] using (circle_sq hpc)
      have hdet : A * W - B * U = 0 := by
        simpa [A, B, U, W, side] using hside
      have hpclose_sq : dist p o ^ 2 < r ^ 2 := by
        nlinarith [hpclose, (dist_nonneg : 0 ≤ dist p o), hr]
      have hcoord_close : (U - A) ^ 2 + (W - B) ^ 2 < r ^ 2 := by
        have hpo := (circle_sq (a := o) (p := p) (R := dist p o) rfl)
        simpa [A, B, U, W, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
          (show (p 0 - o 0) ^ 2 + (p 1 - o 1) ^ 2 < r ^ 2 by
            nlinarith [hpo, hpclose_sq])
      have hcoords : U = A ∧ W = B := by
        have hlag :
            (A * U + B * W) ^ 2 + (A * W - B * U) ^ 2 =
              (A ^ 2 + B ^ 2) * (U ^ 2 + W ^ 2) := by ring
        rw [hdet, zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero, honorm, hpnorm] at hlag
        have hlag' : (A * U + B * W) ^ 2 = (r ^ 2) ^ 2 := by
          simpa [sq] using hlag
        have hdot_or :
            A * U + B * W = r ^ 2 ∨ A * U + B * W = -(r ^ 2) :=
          sq_eq_sq_iff_eq_or_eq_neg.mp hlag'
        rcases hdot_or with hdot | hdot
        · have hdiff : (U - A) ^ 2 + (W - B) ^ 2 = 0 := by
            calc
              (U - A) ^ 2 + (W - B) ^ 2 =
                  (U ^ 2 + W ^ 2) + (A ^ 2 + B ^ 2) -
                    2 * (A * U + B * W) := by ring
              _ = 0 := by rw [hpnorm, honorm, hdot]; ring
          have hUA : (U - A) ^ 2 = 0 := by
            exact le_antisymm (by linarith [sq_nonneg (W - B)]) (sq_nonneg (U - A))
          have hWB : (W - B) ^ 2 = 0 := by
            exact le_antisymm (by linarith [sq_nonneg (U - A)]) (sq_nonneg (W - B))
          constructor
          · exact sub_eq_zero.mp (sq_eq_zero_iff.mp hUA)
          · exact sub_eq_zero.mp (sq_eq_zero_iff.mp hWB)
        · have hdist_sq : (U - A) ^ 2 + (W - B) ^ 2 = 4 * r ^ 2 := by
            calc
              (U - A) ^ 2 + (W - B) ^ 2 =
                  (U ^ 2 + W ^ 2) + (A ^ 2 + B ^ 2) -
                    2 * (A * U + B * W) := by ring
              _ = 4 * r ^ 2 := by rw [hpnorm, honorm, hdot]; ring
          have hr2pos : 0 < r ^ 2 := sq_pos_of_pos hr
          linarith
      ext i
      fin_cases i
      · change p 0 = o 0
        dsimp [A, U] at hcoords
        linarith [hcoords.1]
      · change p 1 = o 1
        dsimp [B, W] at hcoords
        linarith [hcoords.2]
    have same_side_eq :
        ∀ {p q : EuclideanSpace ℝ (Fin 2)} {ρ : ℝ},
          dist p c = r → dist q c = r →
            dist p o = ρ → dist q o = ρ →
              0 < side p * side q → p = q := by
      intro p q ρ hpc hqc hpo hqo hsame
      let A : ℝ := o 0 - c 0
      let B : ℝ := o 1 - c 1
      let U : ℝ := p 0 - c 0
      let W : ℝ := p 1 - c 1
      let U' : ℝ := q 0 - c 0
      let W' : ℝ := q 1 - c 1
      have honorm : A ^ 2 + B ^ 2 = r ^ 2 := by
        simpa [A, B, o] using (circle_sq (hηcircle z))
      have hpnorm : U ^ 2 + W ^ 2 = r ^ 2 := by
        simpa [U, W] using (circle_sq hpc)
      have hqnorm : U' ^ 2 + W' ^ 2 = r ^ 2 := by
        simpa [U', W'] using (circle_sq hqc)
      have hpdist : (U - A) ^ 2 + (W - B) ^ 2 = ρ ^ 2 := by
        have h := (circle_sq (a := o) (p := p) hpo)
        simpa [A, B, U, W, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h
      have hqdist : (U' - A) ^ 2 + (W' - B) ^ 2 = ρ ^ 2 := by
        have h := (circle_sq (a := o) (p := q) hqo)
        simpa [A, B, U', W', sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h
      have hsame' : 0 < (A * W - B * U) * (A * W' - B * U') := by
        simpa [A, B, U, W, U', W', side] using hsame
      have hdotp : A * U + B * W = r ^ 2 - ρ ^ 2 / 2 := by
        calc
          A * U + B * W =
              ((U ^ 2 + W ^ 2) + (A ^ 2 + B ^ 2) -
                ((U - A) ^ 2 + (W - B) ^ 2)) / 2 := by ring
          _ = (r ^ 2 + r ^ 2 - ρ ^ 2) / 2 := by rw [hpnorm, honorm, hpdist]
          _ = r ^ 2 - ρ ^ 2 / 2 := by ring
      have hdotq : A * U' + B * W' = r ^ 2 - ρ ^ 2 / 2 := by
        calc
          A * U' + B * W' =
              ((U' ^ 2 + W' ^ 2) + (A ^ 2 + B ^ 2) -
                ((U' - A) ^ 2 + (W' - B) ^ 2)) / 2 := by ring
          _ = (r ^ 2 + r ^ 2 - ρ ^ 2) / 2 := by rw [hqnorm, honorm, hqdist]
          _ = r ^ 2 - ρ ^ 2 / 2 := by ring
      let dp : ℝ := A * W - B * U
      let dq : ℝ := A * W' - B * U'
      have hlagp :
          (A * U + B * W) ^ 2 + dp ^ 2 =
            (A ^ 2 + B ^ 2) * (U ^ 2 + W ^ 2) := by
        dsimp [dp]
        ring
      have hlagq :
          (A * U' + B * W') ^ 2 + dq ^ 2 =
            (A ^ 2 + B ^ 2) * (U' ^ 2 + W' ^ 2) := by
        dsimp [dq]
        ring
      have hdpdq_sq : dp ^ 2 = dq ^ 2 := by
        rw [hdotp, honorm, hpnorm] at hlagp
        rw [hdotq, honorm, hqnorm] at hlagq
        linarith
      have hdp_or : dp = dq ∨ dp = -dq :=
        sq_eq_sq_iff_eq_or_eq_neg.mp hdpdq_sq
      have hdp_eq : dp = dq := by
        rcases hdp_or with h | h
        · exact h
        · exfalso
          have hprod_nonpos : dp * dq ≤ 0 := by
            calc
              dp * dq = -(dq * dq) := by rw [h]; ring
              _ ≤ 0 := neg_nonpos.mpr (mul_self_nonneg dq)
          exact not_le_of_gt (by simpa [dp, dq] using hsame') hprod_nonpos
      have hdotdiff : A * (U - U') + B * (W - W') = 0 := by
        calc
          A * (U - U') + B * (W - W') =
              (A * U + B * W) - (A * U' + B * W') := by ring
          _ = 0 := by rw [hdotp, hdotq]; ring
      have hdetdiff : A * (W - W') - B * (U - U') = 0 := by
        dsimp [dp, dq] at hdp_eq
        calc
          A * (W - W') - B * (U - U') =
              (A * W - B * U) - (A * W' - B * U') := by ring
          _ = 0 := by rw [hdp_eq]; ring
      have hcoefpos : 0 < A ^ 2 + B ^ 2 := by
        rw [honorm]
        exact sq_pos_of_pos hr
      have hU : U = U' := by
        have hmul : (A ^ 2 + B ^ 2) * (U - U') = 0 := by
          calc
            (A ^ 2 + B ^ 2) * (U - U') =
                A * (A * (U - U') + B * (W - W')) -
                  B * (A * (W - W') - B * (U - U')) := by ring
            _ = 0 := by rw [hdotdiff, hdetdiff]; ring
        exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left (ne_of_gt hcoefpos))
      have hW : W = W' := by
        have hmul : (A ^ 2 + B ^ 2) * (W - W') = 0 := by
          calc
            (A ^ 2 + B ^ 2) * (W - W') =
                B * (A * (U - U') + B * (W - W')) +
                  A * (A * (W - W') - B * (U - U')) := by ring
            _ = 0 := by rw [hdotdiff, hdetdiff]; ring
        exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left (ne_of_gt hcoefpos))
      ext i
      fin_cases i
      · change p 0 = q 0
        dsimp [U, U'] at hU
        linarith [hU]
      · change p 1 = q 1
        dsimp [W, W'] at hW
        linarith [hW]
    have side_ne_zero :
        ∀ {t : Set.Icc (0 : ℝ) 1}, 0 < t.1 → t ≤ aI → side (η t) ≠ 0 := by
      intro t htpos htle hzero
      have ht_eq_o : η t = o :=
        det_zero_close_eq (hηcircle t) (hδclose t htle) hzero
      have ht_eq_z : t = z := hηinj ht_eq_o
      have ht0 : t.1 = 0 := congrArg Subtype.val ht_eq_z
      linarith
    have hside_cont : Continuous fun t : Set.Icc (0 : ℝ) 1 => side (η t) := by
      have hη0 : Continuous fun t : Set.Icc (0 : ℝ) 1 => η t 0 :=
        (PiLp.continuous_apply (p := (2 : ENNReal)) (β := fun _ : Fin 2 => ℝ)
          (i := 0)).comp hηcont
      have hη1 : Continuous fun t : Set.Icc (0 : ℝ) 1 => η t 1 :=
        (PiLp.continuous_apply (p := (2 : ENNReal)) (β := fun _ : Fin 2 => ℝ)
          (i := 1)).comp hηcont
      dsimp [side]
      exact (continuous_const.mul (hη1.sub continuous_const)).sub
        (continuous_const.mul (hη0.sub continuous_const))
    have side_same_as_a :
        ∀ {t : Set.Icc (0 : ℝ) 1}, 0 < t.1 → t ≤ aI →
          0 < side (η t) * side (η aI) := by
      intro t htpos htle
      have ha_ne : side (η aI) ≠ 0 := side_ne_zero hδpos (le_rfl)
      have ht_ne : side (η t) ≠ 0 := side_ne_zero htpos htle
      by_cases ha_pos : 0 < side (η aI)
      · have ht_pos : 0 < side (η t) := by
          by_contra hnot
          have ht_neg : side (η t) < 0 :=
            lt_of_le_of_ne (le_of_not_gt hnot) ht_ne
          have hzero_mem : (0 : ℝ) ∈ Set.Icc (side (η t)) (side (η aI)) :=
            ⟨le_of_lt ht_neg, le_of_lt ha_pos⟩
          have himage :
              (0 : ℝ) ∈ (fun u : Set.Icc (0 : ℝ) 1 => side (η u)) '' Set.Icc t aI :=
            intermediate_value_Icc htle hside_cont.continuousOn hzero_mem
          rcases himage with ⟨s, hs, hs0⟩
          have hspos : 0 < s.1 := htpos.trans_le hs.1
          exact (side_ne_zero hspos hs.2) hs0
        exact mul_pos ht_pos ha_pos
      · have ha_neg : side (η aI) < 0 :=
          lt_of_le_of_ne (le_of_not_gt ha_pos) ha_ne
        have ht_neg : side (η t) < 0 := by
          by_contra hnot
          have ht_pos : 0 < side (η t) :=
            lt_of_le_of_ne (le_of_not_gt hnot) (Ne.symm ht_ne)
          have hzero_mem : (0 : ℝ) ∈ Set.Icc (side (η aI)) (side (η t)) :=
            ⟨le_of_lt ha_neg, le_of_lt ht_pos⟩
          have himage :
              (0 : ℝ) ∈ (fun u : Set.Icc (0 : ℝ) 1 => side (η u)) '' Set.Icc t aI :=
            intermediate_value_Icc' htle hside_cont.continuousOn hzero_mem
          rcases himage with ⟨s, hs, hs0⟩
          have hspos : 0 < s.1 := htpos.trans_le hs.1
          exact (side_ne_zero hspos hs.2) hs0
        exact mul_pos_of_neg_of_neg ht_neg ha_neg
    let tail : Set (Set.Icc (0 : ℝ) 1) := Set.Icc aI oneI
    let tailImage : Set (EuclideanSpace ℝ (Fin 2)) := η '' tail
    have htail_compact : IsCompact tailImage := by
      dsimp [tailImage, tail]
      exact isCompact_Icc.image hηcont
    have htail_nonempty : tailImage.Nonempty := by
      refine ⟨η aI, ?_⟩
      exact ⟨aI, ⟨le_rfl, ha_le_one⟩, rfl⟩
    have ho_not_tail : o ∉ tailImage := by
      rintro ⟨t, ht, htη⟩
      have ht_eq_z : t = z := hηinj htη
      have ha_le_z : aI ≤ z := by simpa [ht_eq_z] using ht.1
      have : δ ≤ (0 : ℝ) := by
        have hval : aI.1 ≤ z.1 := ha_le_z
        simpa [aI, z] using hval
      linarith
    have htail_inf_pos : 0 < Metric.infDist o tailImage :=
      (htail_compact.isClosed.notMem_iff_infDist_pos htail_nonempty).mp ho_not_tail
    have ha_ne_z : aI ≠ z := by
      intro h
      have : δ = (0 : ℝ) := congrArg Subtype.val h
      linarith
    have hdist_a_pos : 0 < dist (η aI) o := by
      exact dist_pos.mpr (by
        intro h
        exact ha_ne_z (hηinj h))
    let ε : ℝ := min (dist (η aI) o) (Metric.infDist o tailImage) / 2
    have hεpos : 0 < ε := by
      exact half_pos (lt_min hdist_a_pos htail_inf_pos)
    refine ⟨ε, hεpos, ?_⟩
    intro ρ hρpos hρlt
    have hε_lt_min : ε < min (dist (η aI) o) (Metric.infDist o tailImage) := by
      dsimp [ε]
      exact half_lt_self (lt_min hdist_a_pos htail_inf_pos)
    have hρlt_a : ρ < dist (η aI) o :=
      hρlt.trans (hε_lt_min.trans_le (min_le_left _ _))
    have hρlt_tail : ρ < Metric.infDist o tailImage :=
      hρlt.trans (hε_lt_min.trans_le (min_le_right _ _))
    let f : Set.Icc (0 : ℝ) 1 → ℝ := fun u => dist (η u) o
    have hfcont : Continuous f := hηcont.dist continuous_const
    have hρ_mem : ρ ∈ Set.Icc (f z) (f aI) := by
      constructor
      · dsimp [f, o]
        simpa using hρpos.le
      · dsimp [f]
        exact le_of_lt hρlt_a
    have himage : ρ ∈ f '' Set.Icc z aI :=
      intermediate_value_Icc hz_le_a hfcont.continuousOn hρ_mem
    rcases himage with ⟨s, hs, hsρ⟩
    let q₀ : EuclideanSpace ℝ (Fin 2) := η s
    have hs_sphere : q₀ ∈ Metric.sphere o ρ := by
      rw [Metric.mem_sphere]
      simpa [q₀, f] using hsρ
    have hs_range : q₀ ∈ Set.range η := ⟨s, rfl⟩
    refine ⟨q₀, ⟨by simpa [o, z] using hs_sphere, hs_range⟩, ?_⟩
    intro q hq
    rcases hq with ⟨hqSphere, hqRange⟩
    rcases hqRange with ⟨t, rfl⟩
    have ht_dist : dist (η t) o = ρ := by
      simpa [o, z] using Metric.mem_sphere.mp hqSphere
    have ht_not_tail : ¬ aI ≤ t := by
      intro hat
      have ht_le_one : t ≤ oneI := by
        change t.1 ≤ (1 : ℝ)
        exact t.2.2
      have ht_mem : η t ∈ tailImage := ⟨t, ⟨hat, ht_le_one⟩, rfl⟩
      have hinf_le : Metric.infDist o tailImage ≤ dist o (η t) :=
        Metric.infDist_le_dist_of_mem ht_mem
      have hdist_o : dist o (η t) = ρ := by simpa [dist_comm] using ht_dist
      linarith
    have ht_le_a : t ≤ aI := le_of_lt (lt_of_not_ge ht_not_tail)
    have ht_ne_z : t ≠ z := by
      intro htz
      have hρ_zero : ρ = 0 := by
        rw [htz] at ht_dist
        simpa [o, dist_self] using ht_dist.symm
      linarith
    have ht_pos : 0 < t.1 := by
      exact lt_of_le_of_ne t.2.1 (fun h0 => ht_ne_z (Subtype.ext h0.symm))
    have hs_ne_z : s ≠ z := by
      intro hsz
      have hρ_zero : ρ = 0 := by
        have hsρ' : f s = ρ := hsρ
        rw [hsz] at hsρ'
        dsimp [f, o] at hsρ'
        simpa [dist_self] using hsρ'.symm
      linarith
    have hs_pos : 0 < s.1 := by
      exact lt_of_le_of_ne s.2.1 (fun h0 => hs_ne_z (Subtype.ext h0.symm))
    have hs_le_a : s ≤ aI := hs.2
    have hsa : 0 < side (η s) * side (η aI) :=
      side_same_as_a hs_pos hs_le_a
    have hta : 0 < side (η t) * side (η aI) :=
      side_same_as_a ht_pos ht_le_a
    have hst_same : 0 < side (η s) * side (η t) := by
      by_cases ha_pos : 0 < side (η aI)
      · rcases (mul_pos_iff.mp hsa) with hsa' | hsa'
        · rcases (mul_pos_iff.mp hta) with hta' | hta'
          · exact mul_pos hsa'.1 hta'.1
          · linarith
        · linarith
      · have ha_ne : side (η aI) ≠ 0 := side_ne_zero hδpos (le_rfl)
        have ha_neg : side (η aI) < 0 :=
          lt_of_le_of_ne (le_of_not_gt ha_pos) ha_ne
        rcases (mul_pos_iff.mp hsa) with hsa' | hsa'
        · linarith
        · rcases (mul_pos_iff.mp hta) with hta' | hta'
          · linarith
          · exact mul_pos_of_neg_of_neg hsa'.1 hta'.1
    have hq_eq : η t = q₀ := by
      symm
      exact same_side_eq (hηcircle s) (hηcircle t) (by simpa [q₀] using hsρ)
        ht_dist hst_same
    exact hq_eq
  rcases start_branch hγcont hγinj hcircle with ⟨ε₀, hε₀pos, hstart⟩
  let γrev : Set.Icc (0 : ℝ) 1 → EuclideanSpace ℝ (Fin 2) :=
    fun t => γ ⟨1 - t.1, ⟨by linarith [t.2.2], by linarith [t.2.1]⟩⟩
  have hγrev_cont : Continuous γrev := by
    dsimp [γrev]
    apply hγcont.comp
    exact Continuous.subtype_mk (by continuity) _
  have hγrev_inj : Function.Injective γrev := by
    intro s t hst
    apply Subtype.ext
    have hval := congrArg Subtype.val (hγinj hst)
    dsimp at hval
    linarith
  have hγrev_circle : ∀ t, dist (γrev t) c = r := by
    intro t
    dsimp [γrev]
    exact hcircle _
  rcases start_branch hγrev_cont hγrev_inj hγrev_circle with ⟨ε₁, hε₁pos, hend_rev⟩
  refine ⟨ε₀, ε₁, hε₀pos, hε₁pos, hstart, ?_⟩
  intro ρ hρpos hρlt
  rcases hend_rev hρpos hρlt with ⟨p, hp, hpuniq⟩
  refine ⟨p, ?_, ?_⟩
  · constructor
    · simpa [γrev] using hp.1
    · rcases hp.2 with ⟨t, rfl⟩
      refine ⟨⟨1 - t.1, ⟨by linarith [t.2.2], by linarith [t.2.1]⟩⟩, ?_⟩
      rfl
  · intro q hq
    apply hpuniq
    constructor
    · simpa [γrev] using hq.1
    · rcases hq.2 with ⟨t, rfl⟩
      refine ⟨⟨1 - t.1, ⟨by linarith [t.2.2], by linarith [t.2.1]⟩⟩, ?_⟩
      simp [γrev]
