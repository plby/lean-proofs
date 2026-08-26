import ErdosProblems.Erdos593.TripleSystem.ErdosRado.SourceSystem
import ErdosProblems.Erdos593.TripleSystem.ErdosRado.EndhomogeneousLift

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos593.TripleSystem.TriangleHost.ErdosRado

/-- Every coloring admits a coherent endhomogeneous limit chain through all
proper trace stages. -/
theorem fullEndhomogeneousLimitChainForEveryColoring :
    FullEndhomogeneousLimitChainForEveryColoring :=
  fullEndhomogeneousLimitChain_of_stoppedCoherentTraceSystems
    TraceIteration.stoppedCoherentTraceSystemsForEveryColoring

/-- Every coloring admits a full-height endhomogeneous trace. -/
theorem fullEndhomogeneousTraceForEveryColoring :
    FullEndhomogeneousTraceForEveryColoring :=
  fullEndhomogeneousTrace_of_fullEndhomogeneousLimitChain
    fullEndhomogeneousLimitChainForEveryColoring

/-- The Erdos--Rado carrier has an uncountable homogeneous pair set for every
natural-valued coloring. -/
theorem erdosRadoUncountableHomogeneousPairSet :
    ErdosRadoUncountableHomogeneousPairSet :=
  erdosRadoUncountableHomogeneousPairSet_of_fullEndhomogeneousTrace
    fullEndhomogeneousTraceForEveryColoring

/-- The Erdos--Rado carrier satisfies the local pair-Ramsey interface used by
the triangle-host argument. -/
theorem pairRamseyTriangle_erdosRadoCarrier :
    PairRamseyTriangle ErdosRadoCarrier :=
  pairRamseyTriangle_erdosRadoCarrier_of_fullEndhomogeneousTrace
    fullEndhomogeneousTraceForEveryColoring

end Erdos593.TripleSystem.TriangleHost.ErdosRado
