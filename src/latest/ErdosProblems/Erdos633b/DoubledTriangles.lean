import ErdosProblems.Erdos633b.DoubledSupports
import ErdosProblems.Erdos633b.BarycentricTriangle

/-! The four actual nondegenerate triangles with the previously certified supports. -/

namespace Erdos633b.DoubledPartition.Layout

noncomputable def abdTriangle (L : Layout) (T : Triangle) : Triangle :=
  T.ofCoords 0 0 1 0 L.u L.v (by simpa using L.v_pos.ne')

noncomputable def bdgTriangle (L : Layout) (T : Triangle) : Triangle :=
  T.ofCoords 1 0 L.u L.v (1 - L.r) L.r (by
    have h : L.r * (L.u + L.v - 1) < 0 :=
      mul_neg_of_pos_of_neg L.r_pos (by linarith [L.uv_lt_one])
    have heq : (L.u - 1) * (L.r - 0) - (1 - L.r - 1) * (L.v - 0) =
        L.r * (L.u + L.v - 1) := by ring
    rw [heq]
    exact h.ne)

noncomputable def aefTriangle (L : Layout) (T : Triangle) : Triangle :=
  T.ofCoords 0 0 (L.ε * L.u) (L.ε * L.v) 0 L.μ (by
    simpa using (mul_pos (mul_pos L.ε_pos L.u_pos) L.μ_pos).ne')

noncomputable def cfgTriangle (L : Layout) (T : Triangle) : Triangle :=
  T.ofCoords 0 1 0 L.μ (1 - L.r) L.r (by
    have h : 0 < (1 - L.r) * (1 - L.μ) :=
      mul_pos (sub_pos.mpr L.r_lt_one) (sub_pos.mpr L.μ_lt_one)
    have heq : (0 - 0) * (L.r - 1) - (1 - L.r - 0) * (L.μ - 1) =
        (1 - L.r) * (1 - L.μ) := by ring
    rw [heq]
    exact h.ne')

theorem abdTriangle_support (L : Layout) (T : Triangle) :
    (L.abdTriangle T).support = region T L.u L.v L.r L.μ L.height .abd :=
  L.abd_support T (L.abdTriangle T) (T.ofCoords_coord_one _ _ _ _ _ _ _)
    (T.ofCoords_coord_two _ _ _ _ _ _ _)

theorem bdgTriangle_support (L : Layout) (T : Triangle) :
    (L.bdgTriangle T).support = region T L.u L.v L.r L.μ L.height .bdg :=
  L.bdg_support T (L.bdgTriangle T) (T.ofCoords_coord_one _ _ _ _ _ _ _)
    (T.ofCoords_coord_two _ _ _ _ _ _ _)

theorem aefTriangle_support (L : Layout) (T : Triangle) :
    (L.aefTriangle T).support = region T L.u L.v L.r L.μ L.height .aef :=
  L.aef_support T (L.aefTriangle T) (T.ofCoords_coord_one _ _ _ _ _ _ _)
    (T.ofCoords_coord_two _ _ _ _ _ _ _)

theorem cfgTriangle_support (L : Layout) (T : Triangle) :
    (L.cfgTriangle T).support = region T L.u L.v L.r L.μ L.height .cfg :=
  L.cfg_support T (L.cfgTriangle T) (T.ofCoords_coord_one _ _ _ _ _ _ _)
    (T.ofCoords_coord_two _ _ _ _ _ _ _)

end Erdos633b.DoubledPartition.Layout
