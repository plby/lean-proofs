import ErdosProblems.Erdos1148.QuadraticRealEmbedding
import ErdosProblems.Erdos1148.DiscriminantPacket

/-! # A primitive closed orbit supplies a nontrivial integral unit -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups NumberField

theorem exists_orderUnit_of_primitive_period {d : ℤ} (hd : 0 < d)
    {t : ℤ × ℤ × ℤ} (ht : PrimitiveIntegralForm t) (htd : discr t = d) (g : SL(2, ℝ))
    (hg : Real.sqrt (d : ℝ) • formAction g (splitForm ℝ) = mapCoeffs (Int.castRingHom ℝ) t)
    (s : ℝ) (hs : s ∈ flowPeriodGroup g) :
    ∃ u : (quadraticOrder d)ˣ,
      quadraticRealEmbedding hd ((u : quadraticOrder d) : QuadraticDiscrAlgebra d) =
        Real.exp (-(s / 2)) := by
  obtain ⟨T, U, hT, hU, hpell, hpar⟩ :=
    (primitive_flowPeriod_iff_discr_coordinates hd ht htd g hg s).mp hs
  refine ⟨pellOrderUnit d T U hpell hpar, ?_⟩
  exact quadraticRealEmbedding_pell_period hd T U s hT hU

theorem exists_integerUnit_of_primitive_period {d : ℤ} [Fact (¬IsSquare d)] (hd : 0 < d)
    {t : ℤ × ℤ × ℤ} (ht : PrimitiveIntegralForm t) (htd : discr t = d) (g : SL(2, ℝ))
    (hg : Real.sqrt (d : ℝ) • formAction g (splitForm ℝ) = mapCoeffs (Int.castRingHom ℝ) t)
    (s : ℝ) (hs : s ∈ flowPeriodGroup g) :
    ∃ u : (𝓞 (QuadraticDiscrAlgebra d))ˣ,
      quadraticRealEmbedding hd ((u : 𝓞 (QuadraticDiscrAlgebra d)) : QuadraticDiscrAlgebra d) =
        Real.exp (-(s / 2)) := by
  obtain ⟨u, hu⟩ := exists_orderUnit_of_primitive_period hd ht htd g hg s hs
  exact ⟨Units.map (quadraticOrderToIntegers htd).toMonoidHom u, hu⟩

theorem exists_integerUnit_log_of_primitive_period {d : ℤ} [Fact (¬IsSquare d)] (hd : 0 < d)
    {t : ℤ × ℤ × ℤ} (ht : PrimitiveIntegralForm t) (htd : discr t = d) (g : SL(2, ℝ))
    (hg : Real.sqrt (d : ℝ) • formAction g (splitForm ℝ) = mapCoeffs (Int.castRingHom ℝ) t)
    (s : ℝ) (hs : s ∈ flowPeriodGroup g) :
    ∃ u : (𝓞 (QuadraticDiscrAlgebra d))ˣ,
      Real.log |quadraticRealEmbedding hd
        ((u : 𝓞 (QuadraticDiscrAlgebra d)) : QuadraticDiscrAlgebra d)| = -(s / 2) := by
  obtain ⟨u, hu⟩ := exists_integerUnit_of_primitive_period hd ht htd g hg s hs
  refine ⟨u, ?_⟩
  rw [hu, abs_of_pos (Real.exp_pos _), Real.log_exp]

theorem ClosedFlowOrbit.exists_integerUnit_abs_log {d : ℤ} [Fact (¬IsSquare d)] (hd : 0 < d)
    {t : ℤ × ℤ × ℤ} (ht : PrimitiveIntegralForm t) (htd : discr t = d)
    (o : ClosedFlowOrbit)
    (ho : Real.sqrt (d : ℝ) • formAction o.lift (splitForm ℝ) = mapCoeffs (Int.castRingHom ℝ) t) :
    ∃ u : (𝓞 (QuadraticDiscrAlgebra d))ˣ,
      |Real.log (|quadraticRealEmbedding hd
        ((u : 𝓞 (QuadraticDiscrAlgebra d)) : QuadraticDiscrAlgebra d)|)| = o.period / 2 := by
  obtain ⟨u, hu⟩ := exists_integerUnit_log_of_primitive_period hd ht htd
    o.lift ho o.period o.period_mem
  refine ⟨u, ?_⟩
  rw [hu, abs_neg, abs_of_pos (half_pos o.period_pos)]

end Erdos1148.DukeArithmetic
