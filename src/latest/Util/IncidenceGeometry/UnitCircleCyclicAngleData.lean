import Util.IncidenceGeometry.UnitCircle

open Classical
noncomputable section

structure UnitCircleCyclicAngleData
    (p : EuclideanSpace ℝ (Fin 2))
    (S : Finset (EuclideanSpace ℝ (Fin 2))) where
  succ :
    {x : EuclideanSpace ℝ (Fin 2) // x ∈ S} →
      {x : EuclideanSpace ℝ (Fin 2) // x ∈ S}
  startAngle : {x : EuclideanSpace ℝ (Fin 2) // x ∈ S} → ℝ
  endAngle : {x : EuclideanSpace ℝ (Fin 2) // x ∈ S} → ℝ
  succ_bijective : Function.Bijective succ
  succ_ne :
    ∀ x : {x : EuclideanSpace ℝ (Fin 2) // x ∈ S}, x.1 ≠ (succ x).1
  endpoint_unique :
    ∀ x y : {x : EuclideanSpace ℝ (Fin 2) // x ∈ S},
      (Sym2.mk x.1 (succ x).1 :
          Sym2 (EuclideanSpace ℝ (Fin 2))) =
        Sym2.mk y.1 (succ y).1 →
      x = y
  start_mem_fundamental :
    ∀ x : {x : EuclideanSpace ℝ (Fin 2) // x ∈ S},
      0 ≤ startAngle x ∧ startAngle x < 2 * Real.pi
  start_point :
    ∀ x : {x : EuclideanSpace ℝ (Fin 2) // x ∈ S},
      x.1 =
        p + WithLp.toLp 2
          (fun i : Fin 2 =>
            if i = 0 then Real.cos (startAngle x) else Real.sin (startAngle x))
  end_point :
    ∀ x : {x : EuclideanSpace ℝ (Fin 2) // x ∈ S},
      (succ x).1 =
        p + WithLp.toLp 2
          (fun i : Fin 2 =>
            if i = 0 then Real.cos (endAngle x) else Real.sin (endAngle x))
  end_lift :
    ∀ x : {x : EuclideanSpace ℝ (Fin 2) // x ∈ S},
      endAngle x = startAngle (succ x) ∨
        endAngle x = startAngle (succ x) + 2 * Real.pi
  gap_pos :
    ∀ x : {x : EuclideanSpace ℝ (Fin 2) // x ∈ S},
      startAngle x < endAngle x
  gap_short :
    ∀ x : {x : EuclideanSpace ℝ (Fin 2) // x ∈ S},
      endAngle x < startAngle x + 2 * Real.pi
  no_S_in_open_gap :
    ∀ (x y : {x : EuclideanSpace ℝ (Fin 2) // x ∈ S}) (t : ℝ),
      0 < t → t < 1 →
        y.1 ≠
          p + WithLp.toLp 2
            (fun i : Fin 2 =>
              if i = 0 then
                Real.cos ((1 - t) * startAngle x + t * endAngle x)
              else
                Real.sin ((1 - t) * startAngle x + t * endAngle x))
  open_gaps_disjoint :
    ∀ (x y : {x : EuclideanSpace ℝ (Fin 2) // x ∈ S}) (s t : ℝ),
      x ≠ y → 0 < s → s < 1 → 0 < t → t < 1 →
        p + WithLp.toLp 2
            (fun i : Fin 2 =>
              if i = 0 then
                Real.cos ((1 - s) * startAngle x + s * endAngle x)
              else
                Real.sin ((1 - s) * startAngle x + s * endAngle x)) ≠
          p + WithLp.toLp 2
            (fun i : Fin 2 =>
              if i = 0 then
                Real.cos ((1 - t) * startAngle y + t * endAngle y)
              else
                Real.sin ((1 - t) * startAngle y + t * endAngle y))
