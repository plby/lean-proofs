import Mathlib.Analysis.InnerProductSpace.PiL2

attribute [local instance] Classical.propDecidable

universe u_1

noncomputable def Erdos502.is_s_distance_set :
    {α : Type u_1} → [MetricSpace.{u_1} α] → Set.{u_1} α → Nat → Prop
  := by
  let _ := ULift.{u_1, 0} PUnit
  sorry

theorem Erdos502.bannai_bannai_stanton :
    ∀ (d s : Nat) (A : Set.{0} (EuclideanSpace.{0, 0} Real (Fin d)))
      [inst : Fintype.{0} (@Set.Elem.{0} (EuclideanSpace.{0, 0} Real (Fin d)) A)],
      @Erdos502.is_s_distance_set.{0} (EuclideanSpace.{0, 0} Real (Fin d))
          (@PiLp.instMetricSpace.{0, 0}
            (@OfNat.ofNat.{0} ENNReal (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} ENNReal (nat_lit 2)
                (@AddMonoidWithOne.toNatCast.{0} ENNReal
                  (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal
                    ENNReal.instAddCommMonoidWithOne))
                PiLp.innerProductSpace._proof_1))
            (Fin d) (fun (x : Fin d) ↦ Real) fact_one_le_two_ennreal (Fin.fintype d) fun (i : Fin d) ↦
            Real.metricSpace)
          A s →
        @LE.le.{0} Nat instLENat
          (@Fintype.card.{0} (@Set.Elem.{0} (EuclideanSpace.{0, 0} Real (Fin d)) A) inst)
          ((@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d s).choose s)
  := by
  sorry
