import ErdosProblems.Axioms
import ErdosProblems.Erdos659
import ErdosProblems.Erdos659b

#print bernays
/-- info: 'bernays' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bernays
/-- info: 'Erdos659.erdos_659' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Erdos659.erdos_659
/-- info: 'Erdos659b.erdos_659' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Erdos659b.erdos_659

/-- Both public statements use definitionally the same distance count. -/
example (S : Finset (EuclideanSpace ℝ (Fin 2))) :
    Erdos659.distinctDistances S = Erdos659b.distinctDistances S := rfl
