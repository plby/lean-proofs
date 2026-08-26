import ErdosProblems.Erdos750

/-! Kernel dependency checks for the formerly assumed theorem and the final results. -/

/-- info: 'Erdos750.stiebitz_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Erdos750.stiebitz_lower_bound

/--
info: 'Erdos750.finite_oct_profile_with_chromatic' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Erdos750.finite_oct_profile_with_chromatic

/--
info: 'Erdos750.infinite_chromatic_local_oct' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Erdos750.infinite_chromatic_local_oct

/-- info: 'Erdos750.erdos_750_independence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Erdos750.erdos_750_independence

/-- info: 'Erdos750.erdos_750' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Erdos750.erdos_750
