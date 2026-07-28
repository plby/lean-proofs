attribute [local instance] Classical.propDecidable

universe u_1

noncomputable def Erdos1067.erdos_1067 :
    Prop
  := by
  let _ := ULift.{u_1, 0} PUnit
  sorry

theorem Erdos1067.not_erdos_1067 :
    Not Erdos1067.erdos_1067.{1}
  := by
  sorry
