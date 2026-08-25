import Mathlib.Tactic
import Util.IncidenceGeometry.PlanarClockwiseSweptTwoRayEndpointConesInSector
import Util.IncidenceGeometry.PlanarNormalizedAngleRepresentation
import Util.IncidenceGeometry.PlanarRot90ClockwiseWedgeAngleCriterion
import Util.IncidenceGeometry.PlanarRot90CoefficientUniqueness
import Util.IncidenceGeometry.PlanarRot90Decomposition
import Util.IncidenceGeometry.PlanarRot90Norm
import Util.IncidenceGeometry.PlanarRot90Orthogonal
import Util.IncidenceGeometry.PlanarSlitDiskEndpointConesAvoidRay

open Classical
noncomputable section

lemma PlanarRot90ClockwiseWedgeRayPartition {ι : Type*} [Fintype ι] [Nonempty ι]
    [DecidableEq ι]
    (p : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ)
    (u : ι → EuclideanSpace ℝ (Fin 2))
    (θ : ι → ℝ)
    (clockwiseNext : Equiv.Perm ι)
    (clockwiseTurn : ι → ι → ℝ)
    (hρ : 0 < ρ)
    (hu : ∀ i : ι, u i ≠ 0)
    (hposRayDistinct :
      ∀ {i j : ι}, (∃ t : ℝ, 0 < t ∧ u j = t • u i) → i = j)
    (hθ_mem : ∀ i : ι, 0 ≤ θ i ∧ θ i < 2 * Real.pi)
    (hθ_inj : Function.Injective θ)
    (hθ_ray :
      ∀ i : ι, ∃ r : ℝ, 0 < r ∧
        u i =
          r • WithLp.toLp 2
            (fun k : Fin 2 =>
              if k = 0 then Real.cos (θ i) else Real.sin (θ i)))
    (hturn_eq : ∀ i j : ι,
      clockwiseTurn i j =
        if j = i then 2 * Real.pi
        else if θ j < θ i then θ i - θ j
        else θ i - θ j + 2 * Real.pi)
    (hfixed_singleton :
      ∀ i : ι, clockwiseNext i = i ↔ ∀ j : ι, j = i)
    (hangleGapEmpty :
      ∀ i : ι, ∀ α : ℝ,
        0 ≤ α → α < 2 * Real.pi →
          0 <
            (if α = θ i then 2 * Real.pi
             else if α < θ i then θ i - α
             else θ i - α + 2 * Real.pi) →
          (if α = θ i then 2 * Real.pi
           else if α < θ i then θ i - α
           else θ i - α + 2 * Real.pi) <
            clockwiseTurn i (clockwiseNext i) →
          ∀ j : ι, θ j ≠ α)
    (hangleGapCover :
      ∀ α : ℝ,
        0 ≤ α → α < 2 * Real.pi →
          (∀ j : ι, θ j ≠ α) →
            ∃ i : ι,
              0 <
                (if α = θ i then 2 * Real.pi
                 else if α < θ i then θ i - α
                 else θ i - α + 2 * Real.pi) ∧
              (if α = θ i then 2 * Real.pi
               else if α < θ i then θ i - α
               else θ i - α + 2 * Real.pi) <
                clockwiseTurn i (clockwiseNext i)) :
    ∃ sector : ι → Set (EuclideanSpace ℝ (Fin 2)),
      (∀ i : ι,
        if h : clockwiseNext i = i then
          sector i =
            Metric.ball p ρ \
              ({q | ∃ t : ℝ, 0 < t ∧ q = p + t • u i} ∪
                ({p} : Set (EuclideanSpace ℝ (Fin 2))))
        else
          ∃ c s : ℝ,
            (s ≠ 0 ∨ c < 0) ∧
            u (clockwiseNext i) = c • u i - s • PlanarRot90 (u i) ∧
            sector i =
              (let base : EuclideanSpace ℝ (Fin 2) := u i
               let baseChart : EuclideanSpace ℝ (Fin 2) →
                  EuclideanSpace ℝ (Fin 2) :=
                fun z => p + z 0 • base + z 1 • PlanarRot90 base
               if 0 < s then
                 baseChart ''
                  {z : EuclideanSpace ℝ (Fin 2) |
                    z 0 ^ 2 + z 1 ^ 2 < (ρ / ‖base‖) ^ 2 ∧
                    z 1 < 0 ∧ 0 < c * z 1 + s * z 0}
               else if s < 0 then
                 baseChart ''
                  {z : EuclideanSpace ℝ (Fin 2) |
                    z 0 ^ 2 + z 1 ^ 2 < (ρ / ‖base‖) ^ 2 ∧
                    (z 1 < 0 ∨ 0 < c * z 1 + s * z 0)}
               else
                 baseChart ''
                  {z : EuclideanSpace ℝ (Fin 2) |
                    z 0 ^ 2 + z 1 ^ 2 < (ρ / ‖base‖) ^ 2 ∧
                    z 1 < 0})) ∧
      (∀ i : ι, IsOpen (sector i) ∧ IsConnected (sector i)) ∧
      (∀ i : ι, sector i ⊆ Metric.ball p ρ) ∧
      (∀ i j : ι,
        Disjoint (sector i)
          {q | ∃ t : ℝ, 0 < t ∧ q = p + t • u j}) ∧
      (∀ q : EuclideanSpace ℝ (Fin 2),
        q ∈ Metric.ball p ρ →
          q ≠ p →
            (∀ i : ι,
              q ∉ {x | ∃ t : ℝ, 0 < t ∧ x = p + t • u i}) →
              ∃ i : ι, q ∈ sector i) := by
  classical
  let e : ℝ → EuclideanSpace ℝ (Fin 2) :=
    fun a => WithLp.toLp 2
      (fun k : Fin 2 => if k = 0 then Real.cos a else Real.sin a)
  let rayRadius : ι → ℝ := fun i => Classical.choose (hθ_ray i)
  have hray_pos (i : ι) : 0 < rayRadius i :=
    (Classical.choose_spec (hθ_ray i)).1
  have hu_eq (i : ι) : u i = rayRadius i • e (θ i) := by
    simpa [e, rayRadius] using (Classical.choose_spec (hθ_ray i)).2
  let turnTo : ι → ℝ → ℝ := fun i α =>
    if α = θ i then 2 * Real.pi
    else if α < θ i then θ i - α
    else θ i - α + 2 * Real.pi
  have hturnTo_bounds (i : ι) {α : ℝ}
      (hα0 : 0 ≤ α) (hα2 : α < 2 * Real.pi) (hne : α ≠ θ i) :
      0 < turnTo i α ∧ turnTo i α < 2 * Real.pi := by
    dsimp [turnTo]
    rw [if_neg hne]
    by_cases hlt : α < θ i
    · simp [hlt]
      linarith [(hθ_mem i).1, (hθ_mem i).2]
    · simp [hlt]
      have hθlt : θ i < α := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hne)
      constructor <;> linarith [(hθ_mem i).1, (hθ_mem i).2]
  have hturnTo_next_eq (i : ι) (hnext : clockwiseNext i ≠ i) :
      turnTo i (θ (clockwiseNext i)) = clockwiseTurn i (clockwiseNext i) := by
    have hθne : θ (clockwiseNext i) ≠ θ i := by
      intro hθ
      exact hnext (hθ_inj hθ)
    dsimp [turnTo]
    rw [if_neg hθne, hturn_eq i (clockwiseNext i)]
    simp [hnext]
  let cCoeff : ι → ℝ := fun i =>
    inner ℝ (u (clockwiseNext i)) (u i) / (‖u i‖ ^ 2)
  let sCoeff : ι → ℝ := fun i =>
    - inner ℝ (u (clockwiseNext i)) (PlanarRot90 (u i)) / (‖u i‖ ^ 2)
  let sector : ι → Set (EuclideanSpace ℝ (Fin 2)) := fun i =>
    if h : clockwiseNext i = i then
      Metric.ball p ρ \
        ({q | ∃ t : ℝ, 0 < t ∧ q = p + t • u i} ∪
          ({p} : Set (EuclideanSpace ℝ (Fin 2))))
    else
      (let base : EuclideanSpace ℝ (Fin 2) := u i
       let baseChart : EuclideanSpace ℝ (Fin 2) →
          EuclideanSpace ℝ (Fin 2) :=
        fun z => p + z 0 • base + z 1 • PlanarRot90 base
       let c : ℝ := cCoeff i
       let s : ℝ := sCoeff i
       if 0 < s then
         baseChart ''
          {z : EuclideanSpace ℝ (Fin 2) |
            z 0 ^ 2 + z 1 ^ 2 < (ρ / ‖base‖) ^ 2 ∧
            z 1 < 0 ∧ 0 < c * z 1 + s * z 0}
       else if s < 0 then
         baseChart ''
          {z : EuclideanSpace ℝ (Fin 2) |
            z 0 ^ 2 + z 1 ^ 2 < (ρ / ‖base‖) ^ 2 ∧
            (z 1 < 0 ∨ 0 < c * z 1 + s * z 0)}
       else
         baseChart ''
          {z : EuclideanSpace ℝ (Fin 2) |
            z 0 ^ 2 + z 1 ^ 2 < (ρ / ‖base‖) ^ 2 ∧
            z 1 < 0})
  have hdecomp_coeff (i : ι) :
      u (clockwiseNext i) =
        cCoeff i • u i - sCoeff i • PlanarRot90 (u i) := by
    have hdecomp := PlanarRot90Decomposition (u i) (u (clockwiseNext i)) (hu i)
    calc
      u (clockwiseNext i) =
          (inner ℝ (u (clockwiseNext i)) (u i) / (‖u i‖ ^ 2)) • u i +
            (inner ℝ (u (clockwiseNext i)) (PlanarRot90 (u i)) / (‖u i‖ ^ 2)) •
              PlanarRot90 (u i) := hdecomp
      _ = cCoeff i • u i - sCoeff i • PlanarRot90 (u i) := by
        dsimp [cCoeff, sCoeff]
        rw [sub_eq_add_neg]
        congr 1
        rw [← neg_smul]
        congr 1
        ring
  have hnot_posray (i : ι) (hnext : clockwiseNext i ≠ i) :
      sCoeff i ≠ 0 ∨ cCoeff i < 0 := by
    by_contra hbad
    push Not at hbad
    rcases hbad with ⟨hs_zero, hc_nonneg⟩
    have hother_eq := hdecomp_coeff i
    have hc_ne : cCoeff i ≠ 0 := by
      intro hc_zero
      have hzero : u (clockwiseNext i) = 0 := by
        simpa [hc_zero, hs_zero] using hother_eq
      exact hu (clockwiseNext i) hzero
    have hc_pos : 0 < cCoeff i := lt_of_le_of_ne hc_nonneg (Ne.symm hc_ne)
    have hpos :
        ∃ t : ℝ, 0 < t ∧ u (clockwiseNext i) = t • u i := by
      refine ⟨cCoeff i, hc_pos, ?_⟩
      simpa [hs_zero] using hother_eq
    have hi_eq_next : i = clockwiseNext i :=
      hposRayDistinct (i := i) (j := clockwiseNext i) hpos
    exact hnext hi_eq_next.symm
  have hnorm_combo {base : EuclideanSpace ℝ (Fin 2)}
      (x y : ℝ) :
      ‖x • base + y • PlanarRot90 base‖ ^ 2 =
        (x ^ 2 + y ^ 2) * ‖base‖ ^ 2 := by
    have horth : inner ℝ (x • base) (y • PlanarRot90 base) = 0 := by
      rw [inner_smul_left, inner_smul_right, PlanarRot90Orthogonal]
      ring
    have horth' : inner ℝ (y • PlanarRot90 base) (x • base) = 0 := by
      rw [real_inner_comm, horth]
    rw [← real_inner_self_eq_norm_sq]
    rw [inner_add_left, inner_add_right, inner_add_right, horth, horth']
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
    rw [norm_smul, norm_smul, PlanarRot90Norm]
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    nlinarith [sq_abs x, sq_abs y]
  have hchart_mem_ball {base : EuclideanSpace ℝ (Fin 2)} (hbase : base ≠ 0)
      {z : EuclideanSpace ℝ (Fin 2)}
      (hz : z 0 ^ 2 + z 1 ^ 2 < (ρ / ‖base‖) ^ 2) :
      p + z 0 • base + z 1 • PlanarRot90 base ∈ Metric.ball p ρ := by
    have hbase_norm_pos : 0 < ‖base‖ := norm_pos_iff.mpr hbase
    have hbase_sq_pos : 0 < ‖base‖ ^ 2 := sq_pos_of_pos hbase_norm_pos
    have hrep :
        p + z 0 • base + z 1 • PlanarRot90 base - p =
          z 0 • base + z 1 • PlanarRot90 base := by
      abel
    have hR_sq_mul : (ρ / ‖base‖) ^ 2 * ‖base‖ ^ 2 = ρ ^ 2 := by
      field_simp [ne_of_gt hbase_norm_pos]
    have hdist_sq :
        ‖p + z 0 • base + z 1 • PlanarRot90 base - p‖ ^ 2 < ρ ^ 2 := by
      rw [hrep, hnorm_combo]
      have hmul := mul_lt_mul_of_pos_right hz hbase_sq_pos
      simpa [hR_sq_mul] using hmul
    rw [Metric.mem_ball, dist_eq_norm]
    exact (sq_lt_sq₀ (norm_nonneg _) (le_of_lt hρ)).mp hdist_sq
  have hcoord_of_ball {base : EuclideanSpace ℝ (Fin 2)} (hbase : base ≠ 0)
      {z : EuclideanSpace ℝ (Fin 2)}
      (hzball : p + z 0 • base + z 1 • PlanarRot90 base ∈ Metric.ball p ρ) :
      z 0 ^ 2 + z 1 ^ 2 < (ρ / ‖base‖) ^ 2 := by
    have hbase_norm_pos : 0 < ‖base‖ := norm_pos_iff.mpr hbase
    have hbase_sq_pos : 0 < ‖base‖ ^ 2 := sq_pos_of_pos hbase_norm_pos
    have hrep :
        p + z 0 • base + z 1 • PlanarRot90 base - p =
          z 0 • base + z 1 • PlanarRot90 base := by
      abel
    have hdist : ‖p + z 0 • base + z 1 • PlanarRot90 base - p‖ < ρ := by
      simpa [Metric.mem_ball, dist_eq_norm] using hzball
    have hdist_sq :
        ‖p + z 0 • base + z 1 • PlanarRot90 base - p‖ ^ 2 < ρ ^ 2 :=
      (sq_lt_sq₀ (norm_nonneg _) (le_of_lt hρ)).mpr hdist
    have hcoord_mul :
        (z 0 ^ 2 + z 1 ^ 2) * ‖base‖ ^ 2 < ρ ^ 2 := by
      simpa [hrep, hnorm_combo] using hdist_sq
    have hR_sq : (ρ / ‖base‖) ^ 2 = ρ ^ 2 / ‖base‖ ^ 2 := by
      field_simp [ne_of_gt hbase_norm_pos]
    rw [hR_sq]
    exact (lt_div_iff₀ hbase_sq_pos).mpr hcoord_mul
  refine ⟨sector, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    by_cases hnext : clockwiseNext i = i
    · simp [sector, hnext]
    · simp [hnext]
      refine ⟨cCoeff i, sCoeff i, hnot_posray i hnext, hdecomp_coeff i, ?_⟩
      simp [sector, hnext]
  · intro i
    by_cases hnext : clockwiseNext i = i
    · have hslit := PlanarSlitDiskEndpointConesAvoidRay p (u i) ρ hρ (hu i)
      dsimp only at hslit
      exact ⟨by simpa [sector, hnext] using hslit.1,
        by simpa [sector, hnext] using hslit.2.1⟩
    · have hswept :=
        PlanarClockwiseSweptTwoRayEndpointConesInSector p (u i)
          (u (clockwiseNext i)) ρ (cCoeff i) (sCoeff i)
          hρ (hu i) (hu (clockwiseNext i)) (hnot_posray i hnext)
          (hdecomp_coeff i)
      dsimp only at hswept
      exact ⟨by simpa [sector, hnext] using hswept.1,
        by simpa [sector, hnext] using hswept.2.1⟩
  · intro i q hq
    by_cases hnext : clockwiseNext i = i
    · have hq' : q ∈
          Metric.ball p ρ \
            ({q | ∃ t : ℝ, 0 < t ∧ q = p + t • u i} ∪
              ({p} : Set (EuclideanSpace ℝ (Fin 2)))) := by
        simpa [sector, hnext] using hq
      exact hq'.1
    · simp [sector, hnext] at hq
      by_cases hspos : 0 < sCoeff i
      · simp [hspos] at hq
        rcases hq with ⟨z, hz, rfl⟩
        exact hchart_mem_ball (hu i) hz.1
      · by_cases hsneg : sCoeff i < 0
        · simp [hspos, hsneg] at hq
          rcases hq with ⟨z, hz, rfl⟩
          exact hchart_mem_ball (hu i) hz.1
        · simp [hspos, hsneg] at hq
          rcases hq with ⟨z, hz, rfl⟩
          exact hchart_mem_ball (hu i) hz.1
  · intro i j
    by_cases hnext : clockwiseNext i = i
    · have hji : j = i := hfixed_singleton i |>.mp hnext j
      subst j
      rw [Set.disjoint_left]
      intro q hqsector hqray
      have hqsector' : q ∈
          Metric.ball p ρ \
            ({q | ∃ t : ℝ, 0 < t ∧ q = p + t • u i} ∪
              ({p} : Set (EuclideanSpace ℝ (Fin 2)))) := by
        simpa [sector, hnext] using hqsector
      exact hqsector'.2 (Or.inl hqray)
    · rw [Set.disjoint_left]
      intro q hqsector hqray
      rcases hqray with ⟨t, ht, hqray⟩
      simp [sector, hnext] at hqsector
      have hθnext_ne : θ (clockwiseNext i) ≠ θ i := by
        intro hθ
        exact hnext (hθ_inj hθ)
      have hother_angle :
          let e' : ℝ → EuclideanSpace ℝ (Fin 2) :=
            fun a => WithLp.toLp 2
              (fun k : Fin 2 => if k = 0 then Real.cos a else Real.sin a)
          let base' : EuclideanSpace ℝ (Fin 2) := rayRadius i • e' (θ i)
          rayRadius (clockwiseNext i) • e' (θ (clockwiseNext i)) =
            cCoeff i • base' - sCoeff i • PlanarRot90 base' := by
        dsimp
        calc
          rayRadius (clockwiseNext i) • e (θ (clockwiseNext i)) =
              u (clockwiseNext i) := (hu_eq (clockwiseNext i)).symm
          _ = cCoeff i • u i - sCoeff i • PlanarRot90 (u i) := hdecomp_coeff i
          _ = cCoeff i • (rayRadius i • e (θ i)) -
                sCoeff i • PlanarRot90 (rayRadius i • e (θ i)) := by
              rw [hu_eq i]
      have hcontradict_z (z : EuclideanSpace ℝ (Fin 2))
          (hvec : t • u j = z 0 • u i + z 1 • PlanarRot90 (u i))
          (hsign :
            (if 0 < sCoeff i then
                z 1 < 0 ∧ 0 < cCoeff i * z 1 + sCoeff i * z 0
              else if sCoeff i < 0 then
                z 1 < 0 ∨ 0 < cCoeff i * z 1 + sCoeff i * z 0
              else
                z 1 < 0)) : False := by
        by_cases hji : j = i
        · subst j
          have hrep0 :
              t • u i = t • u i + (0 : ℝ) • PlanarRot90 (u i) := by simp
          have hzcoeff :=
            PlanarRot90CoefficientUniqueness (d := u i) (v := t • u i)
              (hu i) hvec
          have htcoeff :=
            PlanarRot90CoefficientUniqueness (d := u i) (v := t • u i)
              (a := t) (b := 0) (hu i) hrep0
          have hz0 : z 0 = t := by linarith [hzcoeff.1, htcoeff.1]
          have hz1 : z 1 = 0 := by linarith [hzcoeff.2, htcoeff.2]
          by_cases hspos : 0 < sCoeff i
          · have hsgn : z 1 < 0 ∧
                0 < cCoeff i * z 1 + sCoeff i * z 0 := by
              simpa [hspos] using hsign
            linarith
          · by_cases hsneg : sCoeff i < 0
            · have hsgn : z 1 < 0 ∨
                  0 < cCoeff i * z 1 + sCoeff i * z 0 := by
                simpa [hspos, hsneg] using hsign
              rcases hsgn with hy | hline
              · linarith
              · have hline' : 0 < sCoeff i * t := by
                  simpa [hz0, hz1] using hline
                have hnegprod : sCoeff i * t < 0 :=
                  mul_neg_of_neg_of_pos hsneg ht
                linarith
            · have hsgn : z 1 < 0 := by simpa [hspos, hsneg] using hsign
              linarith
        · have hθji : θ j ≠ θ i := by
            intro hθ
            exact hji (hθ_inj hθ)
          have hpoint_angle :
              let e' : ℝ → EuclideanSpace ℝ (Fin 2) :=
                fun a => WithLp.toLp 2
                  (fun k : Fin 2 => if k = 0 then Real.cos a else Real.sin a)
              let base' : EuclideanSpace ℝ (Fin 2) := rayRadius i • e' (θ i)
              (t * rayRadius j) • e' (θ j) =
                z 0 • base' + z 1 • PlanarRot90 base' := by
            dsimp
            calc
              (t * rayRadius j) • e (θ j) =
                  t • (rayRadius j • e (θ j)) := by rw [smul_smul]
              _ = t • u j := by rw [hu_eq j]
              _ = z 0 • u i + z 1 • PlanarRot90 (u i) := hvec
              _ = z 0 • (rayRadius i • e (θ i)) +
                    z 1 • PlanarRot90 (rayRadius i • e (θ i)) := by
                  rw [hu_eq i]
          have hcrit :=
            PlanarRot90ClockwiseWedgeAngleCriterion
              (β := θ i) (ν := θ (clockwiseNext i)) (α := θ j)
              (rb := rayRadius i) (rn := rayRadius (clockwiseNext i))
              (ra := t * rayRadius j) (c := cCoeff i) (s := sCoeff i)
              (x := z 0) (y := z 1)
              (hβ0 := (hθ_mem i).1) (hβ2 := (hθ_mem i).2)
              (hν0 := (hθ_mem (clockwiseNext i)).1)
              (hν2 := (hθ_mem (clockwiseNext i)).2)
              (hα0 := (hθ_mem j).1) (hα2 := (hθ_mem j).2)
              (hrb := hray_pos i) (hrn := hray_pos (clockwiseNext i))
              (hra := mul_pos ht (hray_pos j))
              (hαν := hθji) (hνβ := hθnext_ne)
              (hpoint := hpoint_angle) (hother := hother_angle)
          have hlt_tau : turnTo i (θ j) < turnTo i (θ (clockwiseNext i)) := by
            simpa [turnTo] using hcrit.mp hsign
          have hlt_turn : turnTo i (θ j) < clockwiseTurn i (clockwiseNext i) := by
            simpa [hturnTo_next_eq i hnext] using hlt_tau
          have hpos_tau : 0 < turnTo i (θ j) :=
            (hturnTo_bounds i (hθ_mem j).1 (hθ_mem j).2 hθji).1
          have hgap :=
            hangleGapEmpty i (θ j) (hθ_mem j).1 (hθ_mem j).2
              (by simpa [turnTo] using hpos_tau)
              (by simpa [turnTo] using hlt_turn)
          exact (hgap j) rfl
      by_cases hspos : 0 < sCoeff i
      · simp [hspos] at hqsector
        rcases hqsector with ⟨z, hz, hqeq⟩
        have hvec : t • u j = z 0 • u i + z 1 • PlanarRot90 (u i) := by
          have htmp := congrArg (fun x => x - p) hqray
          rw [← hqeq] at htmp
          have hleft :
              p + z 0 • u i + z 1 • PlanarRot90 (u i) - p =
                z 0 • u i + z 1 • PlanarRot90 (u i) := by abel
          have hright : p + t • u j - p = t • u j := by abel
          rw [hleft, hright] at htmp
          exact htmp.symm
        exact hcontradict_z z hvec (by simpa [hspos] using hz.2)
      · by_cases hsneg : sCoeff i < 0
        · simp [hspos, hsneg] at hqsector
          rcases hqsector with ⟨z, hz, hqeq⟩
          have hvec : t • u j = z 0 • u i + z 1 • PlanarRot90 (u i) := by
            have htmp := congrArg (fun x => x - p) hqray
            rw [← hqeq] at htmp
            have hleft :
                p + z 0 • u i + z 1 • PlanarRot90 (u i) - p =
                  z 0 • u i + z 1 • PlanarRot90 (u i) := by abel
            have hright : p + t • u j - p = t • u j := by abel
            rw [hleft, hright] at htmp
            exact htmp.symm
          exact hcontradict_z z hvec (by simpa [hspos, hsneg] using hz.2)
        · simp [hspos, hsneg] at hqsector
          rcases hqsector with ⟨z, hz, hqeq⟩
          have hvec : t • u j = z 0 • u i + z 1 • PlanarRot90 (u i) := by
            have htmp := congrArg (fun x => x - p) hqray
            rw [← hqeq] at htmp
            have hleft :
                p + z 0 • u i + z 1 • PlanarRot90 (u i) - p =
                  z 0 • u i + z 1 • PlanarRot90 (u i) := by abel
            have hright : p + t • u j - p = t • u j := by abel
            rw [hleft, hright] at htmp
            exact htmp.symm
          exact hcontradict_z z hvec (by simpa [hspos, hsneg] using hz.2)
  · intro q hqball hqne hnotray
    have hv : q - p ≠ 0 := by
      intro hv0
      exact hqne (sub_eq_zero.mp hv0)
    let zc : ℂ := ((q - p) 0 : ℂ) + ((q - p) 1 : ℂ) * Complex.I
    let α : ℝ := let a := Complex.arg zc
      if 0 ≤ a then a else a + 2 * Real.pi
    have hnorm := PlanarNormalizedAngleRepresentation (q - p) hv
    have hα0 : 0 ≤ α := by simpa [zc, α] using hnorm.1
    have hα2 : α < 2 * Real.pi := by simpa [zc, α] using hnorm.2.1
    rcases hnorm.2.2 with ⟨rq, hrq, hqvec⟩
    have hqvec' : q - p = rq • e α := by
      simpa [zc, α, e] using hqvec
    have hα_not_listed : ∀ j : ι, θ j ≠ α := by
      intro j hθα
      apply hnotray j
      rcases Classical.choose_spec (hθ_ray j) with ⟨hrj, huj⟩
      refine ⟨rq / rayRadius j, div_pos hrq (hray_pos j), ?_⟩
      have hv_ray : q - p = (rq / rayRadius j) • u j := by
        calc
          q - p = rq • e α := hqvec'
          _ = (rq / rayRadius j) • (rayRadius j • e α) := by
              rw [smul_smul]
              field_simp [ne_of_gt (hray_pos j)]
          _ = (rq / rayRadius j) • u j := by
              rw [hu_eq j, hθα]
      calc
        q = p + (q - p) := by abel
        _ = p + (rq / rayRadius j) • u j := by rw [hv_ray]
    rcases hangleGapCover α hα0 hα2 hα_not_listed with
      ⟨i, hτpos, hτlt⟩
    refine ⟨i, ?_⟩
    by_cases hnext : clockwiseNext i = i
    · have hnotdel :
          q ∉ ({q | ∃ t : ℝ, 0 < t ∧ q = p + t • u i} ∪
              ({p} : Set (EuclideanSpace ℝ (Fin 2)))) := by
        intro h
        rcases h with hray | hp
        · exact hnotray i hray
        · exact hqne hp
      exact by
        simpa [sector, hnext] using
          (show q ∈ Metric.ball p ρ \
            ({q | ∃ t : ℝ, 0 < t ∧ q = p + t • u i} ∪
              ({p} : Set (EuclideanSpace ℝ (Fin 2)))) from ⟨hqball, hnotdel⟩)
    · have hθnext_ne : θ (clockwiseNext i) ≠ θ i := by
        intro hθ
        exact hnext (hθ_inj hθ)
      have hα_ne : α ≠ θ i := (hα_not_listed i).symm
      have hτ_next_eq := hturnTo_next_eq i hnext
      have hlt_tau : turnTo i α < turnTo i (θ (clockwiseNext i)) := by
        simpa [turnTo, hτ_next_eq] using hτlt
      let x : ℝ := (rq / rayRadius i) * Real.cos (α - θ i)
      let y : ℝ := (rq / rayRadius i) * Real.sin (α - θ i)
      let z : EuclideanSpace ℝ (Fin 2) :=
        WithLp.toLp 2 (fun k : Fin 2 => if k = 0 then x else y)
      have hcoord :=
        PlanarRot90AngleCoordinateDecomposition (θ i) α (rayRadius i) rq
          (ne_of_gt (hray_pos i))
      have hpoint_angle :
          let e' : ℝ → EuclideanSpace ℝ (Fin 2) :=
            fun a => WithLp.toLp 2
              (fun k : Fin 2 => if k = 0 then Real.cos a else Real.sin a)
          let base' : EuclideanSpace ℝ (Fin 2) := rayRadius i • e' (θ i)
          rq • e' α = z 0 • base' + z 1 • PlanarRot90 base' := by
        dsimp [z, x, y]
        simpa [e] using hcoord.1
      have hother_angle :
          let e' : ℝ → EuclideanSpace ℝ (Fin 2) :=
            fun a => WithLp.toLp 2
              (fun k : Fin 2 => if k = 0 then Real.cos a else Real.sin a)
          let base' : EuclideanSpace ℝ (Fin 2) := rayRadius i • e' (θ i)
          rayRadius (clockwiseNext i) • e' (θ (clockwiseNext i)) =
            cCoeff i • base' - sCoeff i • PlanarRot90 base' := by
        dsimp
        calc
          rayRadius (clockwiseNext i) • e (θ (clockwiseNext i)) =
              u (clockwiseNext i) := (hu_eq (clockwiseNext i)).symm
          _ = cCoeff i • u i - sCoeff i • PlanarRot90 (u i) := hdecomp_coeff i
          _ = cCoeff i • (rayRadius i • e (θ i)) -
                sCoeff i • PlanarRot90 (rayRadius i • e (θ i)) := by
              rw [hu_eq i]
      have hcrit :=
        PlanarRot90ClockwiseWedgeAngleCriterion
          (β := θ i) (ν := θ (clockwiseNext i)) (α := α)
          (rb := rayRadius i) (rn := rayRadius (clockwiseNext i))
          (ra := rq) (c := cCoeff i) (s := sCoeff i)
          (x := z 0) (y := z 1)
          (hβ0 := (hθ_mem i).1) (hβ2 := (hθ_mem i).2)
          (hν0 := (hθ_mem (clockwiseNext i)).1)
          (hν2 := (hθ_mem (clockwiseNext i)).2)
          (hα0 := hα0) (hα2 := hα2)
          (hrb := hray_pos i) (hrn := hray_pos (clockwiseNext i))
          (hra := hrq) (hαν := hα_ne) (hνβ := hθnext_ne)
          (hpoint := hpoint_angle) (hother := hother_angle)
      have hsign :
          (if 0 < sCoeff i then
              z 1 < 0 ∧ 0 < cCoeff i * z 1 + sCoeff i * z 0
            else if sCoeff i < 0 then
              z 1 < 0 ∨ 0 < cCoeff i * z 1 + sCoeff i * z 0
            else
              z 1 < 0) := by
        exact hcrit.mpr (by simpa [turnTo] using hlt_tau)
      have hvec_chart :
          q = p + z 0 • u i + z 1 • PlanarRot90 (u i) := by
        have hvec :
            q - p = z 0 • u i + z 1 • PlanarRot90 (u i) := by
          calc
            q - p = rq • e α := hqvec'
            _ = z 0 • (rayRadius i • e (θ i)) +
                  z 1 • PlanarRot90 (rayRadius i • e (θ i)) := by
                simpa [e] using hpoint_angle
            _ = z 0 • u i + z 1 • PlanarRot90 (u i) := by
                rw [hu_eq i]
        calc
          q = p + (q - p) := by abel
          _ = p + (z 0 • u i + z 1 • PlanarRot90 (u i)) := by rw [hvec]
          _ = p + z 0 • u i + z 1 • PlanarRot90 (u i) := by abel
      have hzdisk :
          z 0 ^ 2 + z 1 ^ 2 < (ρ / ‖u i‖) ^ 2 := by
        apply hcoord_of_ball (hu i)
        simpa [← hvec_chart] using hqball
      simp [sector, hnext]
      by_cases hspos : 0 < sCoeff i
      · simp [hspos]
        refine ⟨z, ?_, hvec_chart.symm⟩
        exact ⟨hzdisk, by simpa [hspos] using hsign⟩
      · by_cases hsneg : sCoeff i < 0
        · simp [hspos, hsneg]
          refine ⟨z, ?_, hvec_chart.symm⟩
          exact ⟨hzdisk, by simpa [hspos, hsneg] using hsign⟩
        · simp [hspos, hsneg]
          refine ⟨z, ?_, hvec_chart.symm⟩
          exact ⟨hzdisk, by simpa [hspos, hsneg] using hsign⟩
