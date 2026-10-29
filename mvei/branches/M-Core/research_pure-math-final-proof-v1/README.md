# M-Core — branch `research/pure-math-final-proof-v1`

Lean sources from the branch `research/pure-math-final-proof-v1` of the private repository `ShantiDraconis/M-Core`, commit `ef31a391b2127be4a51fdf0aa51ccb51a5670cd5` (2026-09-20T11:02:20+01:00), that hold theorems found only on branches (no default branch of any repository has a theorem with the same name). Published here: the files with the theorems the kernel closed, the local files they import and the Lake files of their project.

* Branch state: parada (not in the default branch).
* Theorems only on branches, in this branch: 75 — closed 39, conditional 15, open 0, proof error 0, not reached 20, no result 1.
* History: 82 commit(s) of this branch that are not in the default branch, with date and subject, in `certificate.json`.
* `certificate.json` (SHA-256 of its content: `ad35b1446d9c2e0656233ba973fa64ce43940eb9257058d477cf8f9894dfc9f5`) lists every theorem with its state and the axioms beyond the standard three, and the SHA-256 of every published file. From the repository root: `sha256sum -c mvei/branches/M-Core/research_pure-math-final-proof-v1/SOURCES.sha256`.

Closed means the kernel accepted the proof and it depends only on `propext`, `Classical.choice` and `Quot.sound`; it proves the statement written in the file and is not a claim that an open problem is solved.

| Theorem | File | State |
|---|---|---|
| `MCore.V21.CertificateTests.badHead_fails_closed` | `MCore/V21/CertificateTests.lean`:46 | fechado |
| `MCore.V21.CertificateTests.blockingResidue_fails_closed` | `MCore/V21/CertificateTests.lean`:64 | fechado |
| `MCore.V21.CertificateTests.demo_chain_closes` | `MCore/V21/CertificateTests.lean`:75 | fechado |
| `MCore.V21.CertificateTests.greenControls_closed` | `MCore/V21/CertificateTests.lean`:37 | fechado |
| `MCore.V21.CertificateTests.packed_demo_endpoint` | `MCore/V21/CertificateTests.lean`:90 | fechado |
| `MCore.V21.CertificateTests.packed_demo_identity` | `MCore/V21/CertificateTests.lean`:87 | fechado |
| `MCore.V21.CertificateTests.placebo_fails_closed` | `MCore/V21/CertificateTests.lean`:55 | fechado |
| `MCore.V21.ClosedChain.closes` | `MCore/V21/ClosedChain.lean`:13 | fechado |
| `MCore.V21.ConditionalChain.closes_under` | `MCore/V21/ClosedChain.lean`:36 | fechado |
| `MCore.V21.Examples.logical_two_edge_close` | `MCore/V21/Examples.lean`:5 | fechado |
| `MCore.V21.PackedClosure.endpoint` | `MCore/V21/CoreIdentity.lean`:49 | fechado |
| `MCore.V21.TargetCertificate.endpoint` | `MCore/V21/ClosedChain.lean`:24 | fechado |
| `MCore.V21.classify_target_iff` | `MCore/V21/ResidueClassifier.lean`:28 | fechado |
| `MCore.V21.closed_locus_stable` | `MCore/V21/CoreIdentity.lean`:53 | fechado |
| `MCore.V21.coreIdentity_fixed` | `MCore/V21/CoreIdentity.lean`:46 | fechado |
| `MCore.V21.registered_endpoint` | `MCore/V21/ProblemEmbedding.lean`:34 | fechado |
| `MCore.V22.ExactDecomposition.asIff` | `MCore/V22/RecursiveDecomposition.lean`:12 | nao_alcancado |
| `MCore.V22.ExactDecomposition.child_proof_closes_parent` | `MCore/V22/RecursiveDecomposition.lean`:24 | nao_alcancado |
| `MCore.V22.ProblemInstance.promotion_requires_goal` | `MCore/V22/ProblemInstance.lean`:19 | nao_alcancado |
| `MCore.V22.ResidualSystem.acc_irrefl` | `MCore/V22/ResidualCalculus.lean`:24 | nao_checado |
| `MCore.V22.ResidualSystem.no_step_from_closed` | `MCore/V22/ResidualCalculus.lean`:38 | nao_alcancado |
| `MCore.V22.ResidualSystem.step_irrefl` | `MCore/V22/ResidualCalculus.lean`:33 | nao_alcancado |
| `MCore.V22.Tests.closed_open_classifies` | `MCore/V22/Tests.lean`:11 | fechado |
| `MCore.V22.Tests.false_true_is_both_closed` | `MCore/V22/Tests.lean`:13 | fechado |
| `MCore.V22.Tests.indeterminate_absorbs_left` | `MCore/V22/Tests.lean`:15 | fechado |
| `MCore.V22.Tests.indeterminate_absorbs_right` | `MCore/V22/Tests.lean`:17 | fechado |
| `MCore.V22.Tests.node_count_is_39` | `MCore/V22/Tests.lean`:4 | condicional |
| `MCore.V22.Tests.open_open_classifies` | `MCore/V22/Tests.lean`:9 | fechado |
| `MCore.V22.Tests.relation_count_is_1521` | `MCore/V22/Tests.lean`:6 | condicional |
| `MCore.V22.allDirectedNodePairs_count` | `MCore/V22/Matrix.lean`:17 | condicional |
| `MCore.V22.allNodes_count` | `MCore/V22/Universe.lean`:44 | condicional |
| `MCore.V22.allProblems_count` | `MCore/V22/Universe.lean`:24 | fechado |
| `MCore.V22.allStages_count` | `MCore/V22/Universe.lean`:34 | fechado |
| `MCore.V22.beal_blocker_is_middle` | `MCore/V22/NodeLocator.lean`:53 | fechado |
| `MCore.V22.beal_has_exact_blocker` | `MCore/V22/ExactBlockerNecessity.lean`:29 | nao_alcancado |
| `MCore.V22.beal_has_one_exact_blocker` | `MCore/V22/ExactBlockers.lean`:105 | condicional |
| `MCore.V22.blocker_mem_implies_hasExactBlocker` | `MCore/V22/ExactBlockerNecessity.lean`:15 | nao_alcancado |
| `MCore.V22.blocking_nodes_count` | `MCore/V22/NodeLocator.lean`:39 | condicional |
| `MCore.V22.bsd_blocker_is_middle` | `MCore/V22/NodeLocator.lean`:49 | fechado |
| `MCore.V22.bsd_has_exact_blocker` | `MCore/V22/ExactBlockerNecessity.lean`:25 | nao_alcancado |
| `MCore.V22.bsd_has_one_exact_blocker` | `MCore/V22/ExactBlockers.lean`:101 | condicional |
| `MCore.V22.candidate_record_not_mainCertified` | `MCore/V22/FrontierRegistry.lean`:59 | fechado |
| `MCore.V22.candidate_scope_not_main` | `MCore/V22/FrontierRegistry.lean`:55 | fechado |
| `MCore.V22.certificate_implies_final` | `MCore/V22/ResidualCalculus.lean`:68 | nao_alcancado |
| `MCore.V22.certificate_to_certifiedClosed` | `MCore/V22/ClosureCriterion.lean`:27 | nao_alcancado |
| `MCore.V22.certifiedClosed_implies_goal` | `MCore/V22/ClosureCriterion.lean`:22 | nao_alcancado |
| `MCore.V22.certifiedClosed_to_certificate` | `MCore/V22/ClosureCriterion.lean`:38 | nao_alcancado |
| `MCore.V22.closedDirections_start_iff_final` | `MCore/V22/RecursiveDecomposition.lean`:41 | nao_alcancado |
| `MCore.V22.closure_state_count` | `MCore/V22/BidirectionalClosure.lean`:35 | fechado |
| `MCore.V22.constructor_blocker_count` | `MCore/V22/NodeLocator.lean`:115 | condicional |
| `MCore.V22.constructor_closes_frontier` | `MCore/V22/FrontierKernel.lean`:22 | fechado |
| `MCore.V22.exact_mathematical_blocker_count` | `MCore/V22/ExactBlockers.lean`:78 | fechado |
| `MCore.V22.frontier_constructor_iff_global` | `MCore/V22/FrontierKernel.lean`:36 | fechado |
| `MCore.V22.frontier_subnode_count` | `MCore/V22/NodeLocator.lean`:93 | condicional |
| `MCore.V22.hodge_blocker_is_middle` | `MCore/V22/NodeLocator.lean`:45 | fechado |
| `MCore.V22.hodge_has_exact_blocker` | `MCore/V22/ExactBlockerNecessity.lean`:21 | nao_alcancado |
| `MCore.V22.hodge_has_one_exact_blocker` | `MCore/V22/ExactBlockers.lean`:97 | condicional |
| `MCore.V22.kernel_unassigned_nodes_count` | `MCore/V22/NodeLocator.lean`:42 | condicional |
| `MCore.V22.navierStokes_has_exact_blocker` | `MCore/V22/ExactBlockerNecessity.lean`:45 | nao_alcancado |
| `MCore.V22.ns_blocker_is_middle` | `MCore/V22/NodeLocator.lean`:69 | fechado |
| `MCore.V22.ns_has_two_exact_blockers` | `MCore/V22/ExactBlockers.lean`:93 | condicional |
| `MCore.V22.open_problem_has_registered_exact_blocker` | `MCore/V22/ExactBlockerNecessity.lean`:53 | nao_alcancado |
| `MCore.V22.pnp_blocker_is_middle` | `MCore/V22/NodeLocator.lean`:57 | fechado |
| `MCore.V22.pnp_has_exact_blocker` | `MCore/V22/ExactBlockerNecessity.lean`:33 | nao_alcancado |
| `MCore.V22.pnp_has_one_exact_blocker` | `MCore/V22/ExactBlockers.lean`:109 | condicional |
| `MCore.V22.primary_frontier_count` | `MCore/V22/FrontierRegistry.lean`:170 | fechado |
| `MCore.V22.recursive_frontier_exact` | `MCore/V22/RecursiveDecomposition.lean`:54 | nao_alcancado |
| `MCore.V22.research_direction_count` | `MCore/V22/BidirectionalClosure.lean`:89 | fechado |
| `MCore.V22.rh_blocker_is_middle` | `MCore/V22/NodeLocator.lean`:61 | fechado |
| `MCore.V22.rh_has_two_exact_blockers` | `MCore/V22/ExactBlockers.lean`:85 | condicional |
| `MCore.V22.riemann_has_exact_blocker` | `MCore/V22/ExactBlockerNecessity.lean`:37 | nao_alcancado |
| `MCore.V22.witness_incompatibility` | `MCore/V22/BidirectionalClosure.lean`:97 | fechado |
| `MCore.V22.yangMills_has_exact_blocker` | `MCore/V22/ExactBlockerNecessity.lean`:41 | nao_alcancado |
| `MCore.V22.ym_blocker_is_middle` | `MCore/V22/NodeLocator.lean`:65 | fechado |
| `MCore.V22.ym_has_two_exact_blockers` | `MCore/V22/ExactBlockers.lean`:89 | condicional |
