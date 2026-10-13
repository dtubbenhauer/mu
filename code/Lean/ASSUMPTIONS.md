# Mathematical inputs and trust

The preferred endpoints are `paper_main_faithful`,
`paper_canonicality_faithful` and `paper_unbounded_faithful` in
[FaithfulEndpoint.lean](WebMu/Revised/FaithfulEndpoint.lean).
They are conditional on the following uniform results from prior work,
supplied as explicit theorem parameters.

| Interface | Accepted mathematical content |
| --- | --- |
| `Bar.BarReferences` | Tensor bar, elementary spider intertwiners and naturality for intertwiners |
| `Bar.AtomicCoordinates` | Standard finite bases, linear and tensor coordinate laws, and the primitive vertex, cup and cap tables |
| `AtlasRealization.RibbonFunctorReferences` | The tensor functor on oriented ribbon diagrams and elementary square, digon and isotopy relations |
| `CapDiagram.PositiveRibbonReferences` | The ordinary positive-boundary square, digon and isotopy laws for the graph functor |
| `CapDiagram.BoundaryTripodReferences` | Monoidality for a disjoint positive tripod, with fixed surviving boundary labels |
| `CanonicalReferences` | The uniform bar-fixed leading-lattice characterization of the dual canonical basis |
| `KLReferences` | Ordinary KL degree and diagonal bounds, the alternating parabolic formula and minimal-coset length additivity |
| `FKKReferences` | The uniform tensor/parabolic dictionary, with the C/B/A position permutation and the stated parameter substitution |
| `RSKBumping.CellClassification` | The type-A equal-recording-tableau left-cell criterion |
| `Bruhat.References` | The uniform rank/reduced-subword criterion |

These inputs do not assert the family's canonicality, local cap identities,
selected-row closure or KL coefficient. The local calculations and the
all-parameter induction are proved in the supplied modules. The RSK insertion
and recording algorithms and the rectangular bumping calculation are also
proved; the uniform cell classification remains an input.

The source-coordinate argument uses the full lattice induction, exact interface
cancellation, the original tensor bar and canonical uniqueness. It assumes no
bar compatibility of the interface basis change.

Large finite calculations use `native_decide`. Its `Lean.ofReduceBool`
dependency trusts the pinned native compiler and runtime in addition to the
kernel. The other allowed logical dependencies are `propext`,
`Classical.choice` and `Quot.sound`.

[AuditIndependentMain.lean](AuditIndependentMain.lean) prints the types and
axioms of all three endpoints and checks their proof dependencies. It rejects
unexpected axioms, missing main proof components and the older certificate
routes. The run command builds the supplied library and executes this audit.
