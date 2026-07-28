attribute [local instance] Classical.propDecidable

universe u_1

noncomputable def Erdos1022.erdos_1022 :
    Prop
  := by
  let _ := ULift.{u_1, 0} PUnit
  sorry

theorem Erdos1022.not_erdos_1022 :
    Not Erdos1022.erdos_1022.{u_1}
  := by
  let _ := ULift.{u_1, 0} PUnit
  sorry
