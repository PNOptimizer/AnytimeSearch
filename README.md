This code deals with the scheduling problem of resource allocation systems (RASs). It proposes a new anytime search method that combines the A$^*$ search with the depth-first search based on place-timed Petri nets (PNs). Within a place-timed PN's reachability graph, the method iteratively searches for transition firing sequences from a start state to a goal one. It usually finds a near-optimal solution quickly and continuously improves the solution until obtaining an optimal one if given more time. More importantly, it needs only one parameter and no deadlock control policy, and it can handle the PNs with flexible routes and the generalized PNs with weighted arcs, both of which are common in the PN models of RASs.

They are developed via C#.

Feb. 1, 2023.
