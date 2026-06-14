# Boundary Semantics in the Connes–Kreimer Hopf Algebra
### A Lean 4 Formalization, a Convolution Proof of the Antipode, and a Boundary-Resolved Graph Carrier

*Working draft — section bodies. Math in inline LaTeX; to be ported to the JAR LaTeX template once content is frozen.*

---

## Abstract

We report a Lean 4 formalization of the Connes–Kreimer Hopf algebra of Feynman graphs, together with a structural finding it produced. The coproduct, counit, coassociativity, and antipode are formalized over a flat graph carrier, `sorry`- and axiom-free, reducing the conditional Hopf structure to exactly two named boundary-semantics interfaces; the right antipode axiom is proved outright in the convolution ring by local nilpotency, eliminating the classical forest-cancellation kernel. We then show both interfaces fail on the flat carrier: four decidable witnesses exhibit the precise multiset collapse they forbid, which arises because the flat notation forgets half-edge and insertion-slot identities. A boundary-resolved carrier with persistent identities inhabits the distilled interfaces, and the forgetful projection identifies the resolved retargeting with the flat collapse maps definitionally, by `rfl`; the repaired and collapsing behaviours differ by exactly the persistent identity. The full unconditional reconstruction over the resolved carrier is left as future work.

*(≈151 words.)*

---

# 1. Introduction

The Connes–Kreimer Hopf algebra of Feynman graphs is the combinatorial core of the algebraic approach to renormalization: it encodes the BPHZ/Zimmermann forest formula as a coproduct and recasts the subtraction of subdivergences as a Birkhoff decomposition in a group of characters [Kre98, CK00, Zim69]. Its coproduct, coassociativity, and antipode are exactly the kind of recursion-and-cancellation combinatorics for which machine-checking is both natural and valuable — the bookkeeping is intricate, and the correctness of the cancellations is the sort of thing a proof assistant is good at certifying. This paper reports a Lean 4 formalization of that combinatorial core, and, more pointedly, what the attempt to formalize it revealed about the standard presentation.

We set out to build the CK Hopf algebra over an explicit carrier of Feynman graphs: a free commutative algebra on graph classes, with the strict-forest coproduct, the counit, the recursive antipode, and coassociativity. Most of this goes through unconditionally and is reported as such. But at the points where the informal proof says "obvious," "by the standard CK argument," or "the quotient remembers the insertion," the type-checker said something else. It said that the contracted quotient does *not* remember which insertion produced it; that a promoted external leg has no canonical preimage; that the right antipode identity is not a forest-cancellation at all but a statement about local nilpotency. Each of these refusals turned out to be correct, and tracking them down is what the paper is about.

None of this is a flaw in Connes and Kreimer's mathematics. In their intended notion of graph, half-edges and insertion slots are distinct objects, and the informal proof uses that distinctness freely and correctly. The refusals are artifacts of the *representation*. A flat encoding that records an internal edge by its endpoints and sector, and an external leg by its attachment and sector, forgets which half-edge or insertion slot each came from; under contraction, structurally distinct boundary objects collapse to equal elements of a multiset, and a multiset cannot be un-merged. What the formalization contributes is to make the tacit assumption precise — it is exactly two boundary-semantics properties — to locate where in the proof it is used, to show that it fails on the flat representation, and to show how it is restored on a representation that keeps the discarded identities.

Concretely, the paper establishes four results, with `sorry`-free, axiom-free Lean proofs (final audit: the standard `propext`, `Classical.choice`, `Quot.sound`; full build 1475 jobs).

- **(A) Factorization.** The CK Hopf-algebraic skeleton closes over any carrier satisfying two named boundary-semantics interfaces — promoted-leg liftability and insertion uniqueness. We present this as a *factorization* of the standard flat proof, isolating the exact semantic obligations it uses, not as an unconditional theorem about the flat carrier.
- **(Antipode).** The right antipode axiom — classically a separate nested-forest cancellation — is proved outright in the convolution ring by local nilpotency of the reduced coproduct, eliminating that kernel. The argument uses only the coalgebra structure, and so transfers to any carrier at no cost.
- **(B) Flat impossibility.** The two interfaces fail on the flat carrier: four decidable witnesses (`by decide`) exhibit the precise multiset collapse they forbid. We establish this concrete collapse rather than a global negation of the interface classes, which would over-reach.
- **(C, D) Repair.** A boundary-resolved carrier, with persistent edge and leg identities, *inhabits* the distilled forms of both interfaces (C), and the forgetful map that discards the identities sends the resolved retargeting to the flat collapse maps *definitionally*, by `rfl` (D). The repaired and collapsing behaviours are therefore the same operation evaluated on the two sides of the forgetful map; what separates them is exactly the persistent identity.

The framing is deliberate, and it shapes what we do and do not claim. The contribution is not to encode known mathematics but to expose, localize, and repair a semantic mismatch between an informal graph notation and a machine-checkable carrier; the central finding is about representation. Accordingly, two boundaries are drawn explicitly. We do not present the conditional instance (A) as an unconditional theorem about the flat carrier — its hypotheses are shown false there (B), and its non-vacuous positive counterpart is the resolved witness (C), tied to it definitionally (D). And we do not attempt the full *unconditional* reconstruction over the resolved carrier — re-deriving the coproduct and coassociativity so that the two interfaces become outright theorems — which is a separate, larger program along an understood path (the antipode, in particular, transfers for free), and is not required for the contribution established here.

The rest of the paper follows the analysis. Section 2 recalls the CK construction at the level of detail the formalization needs, flagging the tacit recovery step. Section 3 describes the Lean architecture and the conditional Hopf instance with its two-interface residual surface. Section 4 gives the convolution proof of the right antipode axiom. Section 5 states the two boundary interfaces and fixes how the factorization (A) must be read. Section 6 exhibits the flat counterexamples (B). Section 7 presents the boundary-resolved carrier, its inhabited witness (C), and the definitional forgetful projection (D). Section 8 draws the claim boundary and describes the resolved reconstruction as future work. Sections 9 and 10 discuss related work and conclude.

---

# 2. Background: The Connes–Kreimer Hopf Algebra

This section fixes notation and recalls the structure of the Connes–Kreimer (CK) Hopf algebra at the level of detail needed for the formalization. We deliberately keep the renormalization physics to a minimum: what matters here is the *combinatorial* shape of the coproduct, counit, and antipode, and — crucially — the points at which the standard arguments quietly assume that contracting a subgraph remembers how that subgraph was embedded. Those assumptions are invisible on paper and become the central objects of Sections 5–7.

## 2.1 Feynman graphs, divergent subgraphs, and admissible forests

A *Feynman graph* $\Gamma$ is a finite graph equipped with the combinatorial data of a perturbative quantum field theory: a set of internal edges (propagators), a set of external legs (half-edges with one free end), and vertices drawn from the interaction terms of the theory. Each edge and leg carries a *sector* label recording the field type it represents. For the purposes of the Hopf algebra we work with isomorphism classes of such graphs, and the algebraically relevant graphs are the *one-particle irreducible* (1PI) ones: connected graphs that remain connected after the deletion of any single internal edge.

To each graph $\Gamma$ one assigns a *superficial degree of divergence* $\omega(\Gamma)$, computed by power counting from the edge and vertex content. A graph is *divergent* when $\omega(\Gamma) \ge 0$. The Hopf algebra is generated by the connected 1PI divergent graphs; the divergent subgraphs of a graph are precisely the pieces that must be subtracted in renormalization, and they are the pieces the coproduct extracts.

A collection of divergent 1PI subgraphs that are pairwise either nested or disjoint is called an *admissible forest*. Forests organize the recursive structure of overlapping divergences. In the formalization the relevant index is the set of *proper* forests of a generator — the nontrivial ways a graph can be decomposed into a divergent subgraph and its contraction — which we denote at the generator level by `forestCoproductProperForestIndex`.

Throughout, we treat the power-counting data abstractly. Rather than commit to a specific $\omega$, the development runs inside an ambient *divergence environment*: a small family of `Prop`-level facts asserting that the superficial degree is invariant under graph isomorphism and vertex permutation, and that it behaves additively under forest contraction (and its reverse). These are the standard Weinberg/CK power-counting facts, and we stress at the outset that they are **not** among the assumptions this paper interrogates; they hold for any reasonable power-counting measure and are abstracted purely to keep the construction independent of a particular theory.

## 2.2 The coproduct

The carrier of the Hopf algebra, written $H$, is the free commutative algebra on the connected 1PI divergent graphs. In the formalization this is realized concretely as a multivariate polynomial algebra, `HopfH = MvPolynomial HopfGen ℚ`, whose generators `HopfGen` are the (canonical representatives of) connected 1PI divergent graph classes. Multiplication is disjoint union of graphs; the unit $1$ is the empty graph.

The CK coproduct $\Delta : H \to H \otimes H$ is defined on a connected generator $\Gamma$ by extracting divergent subgraphs:
$$
\Delta(\Gamma) \;=\; \Gamma \otimes 1 \;+\; 1 \otimes \Gamma \;+\; \sum_{\gamma} \gamma \otimes (\Gamma / \gamma),
$$
where $\gamma$ ranges over the proper divergent (forest) subgraphs of $\Gamma$, and $\Gamma/\gamma$ is the *contracted quotient*: the graph obtained by shrinking each connected component of $\gamma$ to a single vertex. The map is then extended to all of $H$ as an algebra homomorphism. The two boundary terms $\Gamma \otimes 1$ and $1 \otimes \Gamma$ are the *primitive* part; the sum is the *proper* part.

In the Lean development this is the *strict forest* coproduct `coproduct_strict_forest`, with the generator-level identity
$$
\Delta(g) \;=\; g \otimes 1 \;+\; 1 \otimes g \;+\; \sum_{A} A_{\mathrm{toHopfH}} \otimes \mathrm{gen}(\mathrm{right}\,A),
$$
the sum taken over $A \in$ `forestCoproductProperForestIndex` $g$. Here $A_{\mathrm{toHopfH}}$ is the product over the components of the extracted subgraph and $\mathrm{gen}(\mathrm{right}\,A)$ is the class of the contracted quotient. The decomposition of this proper sum into left-boundary, right-boundary, and forest summands — the carrier `forestCoproductChoice` — is the bookkeeping device on which both coassociativity and the antipode ultimately rest.

## 2.3 Counit and antipode

The counit $\varepsilon : H \to \mathbb{Q}$ is the algebra map that projects onto the scalar part: $\varepsilon(1) = 1$ and $\varepsilon(\Gamma) = 0$ for every nonempty graph $\Gamma$. Together with $\Delta$ it makes $H$ a coalgebra; the coassociativity of $\Delta$ is discussed in §2.5.

The antipode $S : H \to H$ is determined recursively. On a generator it satisfies the Bogoliubov-type recursion that solves the left antipode axiom,
$$
S(\Gamma) \;=\; -\,\Gamma \;-\; \sum_{\gamma \subsetneq \Gamma} S(\gamma)\,\bigl(\Gamma/\gamma\bigr),
$$
and is extended multiplicatively. Because $H$ is the free commutative (polynomial) algebra on the generators, the formalization defines the antipode cleanly as an algebra homomorphism: `antipodeAlgHom_forest := MvPolynomial.aeval antipodeGen_forest`, with `antipode_forest` its underlying linear map. The recursive generator map `antipodeGen_forest` is well-founded because the proper coproduct strictly lowers a complexity measure (the internal edge count) on each summand.

## 2.4 The right antipode axiom and forest cancellation

A Hopf algebra requires the antipode to satisfy both convolution identities
$$
m \circ (S \otimes \mathrm{id}) \circ \Delta \;=\; \eta \circ \varepsilon \;=\; m \circ (\mathrm{id} \otimes S) \circ \Delta,
$$
where $m$ is multiplication and $\eta$ the unit. The *left* identity is the one the recursion is built to satisfy, and it falls out of a direct cancellation: expanding $\Delta(g)$ and pushing $m \circ (S \otimes \mathrm{id})$ through each summand, the recursive definition of $S$ is exactly what makes the three groups of terms cancel.

The *right* identity, $m \circ (\mathrm{id} \otimes S) \circ \Delta = \eta\varepsilon$, is the delicate one. Pushing $m \circ (\mathrm{id} \otimes S)$ through a forest summand $A_{\mathrm{toHopfH}} \otimes \mathrm{gen}(\mathrm{right}\,A)$ produces $A_{\mathrm{toHopfH}} \cdot S(\mathrm{gen}(\mathrm{right}\,A))$, in which the antipode is applied to a *single* contracted generator rather than to the structured product that the recursion unfolds on the left. The two shapes do not match under definitional unfolding, so the right identity cannot be closed by `ring` alone. Classically (Connes–Kreimer 1998, §3) it is established by an explicit nested-forest summation identity — a recombination over the forest structure that is similar in spirit to, but mathematically distinct from, the identity underlying coassociativity. This forest-cancellation argument is the historical proof of the right antipode axiom, and it is precisely the argument that Section 4 replaces with a convolution-theoretic one.

## 2.5 Why coassociativity and the antipode are combinatorially delicate

Coassociativity, $(\Delta \otimes \mathrm{id}) \circ \Delta = (\mathrm{id} \otimes \Delta) \circ \Delta$, is the technical heart of the construction. Both sides re-expand the proper coproduct a second time, and the equality amounts to a *forest cover identity*: every way of first extracting a subgraph and then sub-extracting from either the subgraph or the quotient must match, summand for summand, a corresponding two-step extraction on the other side. In the formalization this is the F2i-3q forest cover identity, and discharging it requires partitioning the doubly-extracted terms into left-boundary, right-boundary, and forest contributions and exhibiting a bijection between the two sides.

The subtlety that matters for this paper is the following. Both the coassociativity cover identity and the right-antipode cancellation are bijections between *forest decompositions*, and constructing those bijections requires recovering, from a contracted quotient $\Gamma/\gamma$, enough information about how $\gamma$ was embedded in $\Gamma$ — which external legs of the quotient came from which half-edges of the original, and which vertices of the quotient correspond to which contracted components. On paper this recovery is treated as immediate: one writes "$\Gamma/\gamma$" and tacitly carries along the embedding data needed to invert the contraction. The informal argument never names this data because, in the working mathematician's mental model, the quotient *remembers* it.

It is exactly this tacit "the quotient remembers the insertion" step that a formal carrier forces into the open. When the contraction operation is made explicit on a graph representation that records only attachment and sector data, the recovery is no longer free — and, as we show in Sections 5–6, it is in fact *false*. The combinatorial delicacy of CK is therefore not merely a matter of careful bookkeeping; it is the place where the informal graph notation and a faithful machine-checkable representation come apart. Sections 3–4 formalize everything that does go through unconditionally on the flat representation; Sections 5–7 isolate, falsify, and then repair exactly the step that does not.

---

# 3. The Lean 4 Formalization Architecture

This section describes the formal artifact at the level of modules and objects, and states precisely what is and is not established unconditionally. The summary claim is that the CK Hopf-algebraic skeleton is mechanized over the flat carrier up to an exactly auditable boundary: a conditional `HopfAlgebra ℚ HopfH` instance whose only residual hypotheses are two named boundary-semantics classes (plus the ambient power-counting environment of §2.1), with no `sorry`, no `admit`, and no project-level axioms. This conditional instance is the antecedent of Theorem A; the remainder of the paper concerns its two hypotheses.

## 3.1 Module layout

The development is organized into a flat-carrier layer, an algebraic layer, and a boundary-resolved layer:

- **`QFT/Combinatorial/FeynmanGraphs.lean`** — the flat carrier: `FeynmanGraph`, internal edges, external legs, sectors, and the endpoint-retargeting operations.
- **`QFT/Combinatorial/SubGraph.lean`** — subgraphs, admissible forests, and the single-star contraction `contractWith` together with the quotient/remainder operations.
- **`QFT/HopfAlgebra/Coassoc.lean`** — the coproduct `coproduct_strict_forest`, the forest cover identity, and coassociativity.
- **`QFT/HopfAlgebra/Antipode.lean`** — the recursive antipode `antipodeGen_forest` / `antipode_forest` and the left antipode axiom.
- **`QFT/HopfAlgebra/AntipodeConvolution.lean`** — the convolution / local-nilpotency proof of the right antipode axiom (§4).
- **`QFT/HopfAlgebra/HopfAlgebra.lean`** — the conditional `HopfAlgebra ℚ HopfH` instance and the cross-file certificate assembling it from the two boundary facades alone.
- **`QFT/Combinatorial/ResolvedFeynmanGraphs.lean`** and **`QFT/HopfAlgebra/BoundaryResolved.lean`** — the boundary-resolved carrier, its forgetful map, and the resolved witness (§7).

## 3.2 The flat carrier

A `FeynmanGraph` records a multiset of internal edges and a multiset of external legs over a vertex set, each carrying a sector label. An internal edge is, in essence, a pair of endpoints with a sector; an external leg is an attachment vertex with a sector. Contraction is the single-star operation `contractWith`, with the quotient and remainder packaged by `admissibleSubgraphQuotientRemainderSubgraph`: contracting a divergent subgraph shrinks each of its connected components to a star vertex and reattaches the surrounding edges and legs.

The decisive structural fact about this representation — the one that drives everything in Sections 5–7 — is recorded already at this layer: **single-star contraction on `FeynmanGraph` is lossy.** It forgets boundary incidence and attachment multiplicity. Two distinct external legs sharing an attachment vertex and a sector become indistinguishable after contraction, and the flat leg datum `{ attachedTo, sector }` carries nothing that could tell them apart. We return to this in §5; here we only flag that it is a property of the carrier, visible without any Hopf-algebraic machinery.

## 3.3 The algebraic carrier and coproduct

The carrier algebra is `HopfH = MvPolynomial HopfGen ℚ`, the free commutative algebra on the generator type `HopfGen` of connected 1PI divergent graph classes. Multiplication is polynomial multiplication (disjoint union of graphs); the unit is the empty graph. Realizing $H$ as a polynomial algebra is what later lets us define the antipode as an algebra homomorphism and globalize generator-level identities by polynomial extensionality (`MvPolynomial.algHom_ext`).

The coproduct `coproduct_strict_forest` implements the strict-forest form of §2.2, with counit and the full coalgebra structure established constructively (Sprints A–E). The proper part of the coproduct is decomposed, at the generator level, by `forestCoproductChoice` into left-boundary, right-boundary, and forest summands; `coproductGenClass_strict_forest_eq_choiceSum` records that this choice-sum reproduces the coproduct. Coassociativity is the F2i-3q forest cover identity. Its discharge factors through four structural sub-obligations (the "hBP" Models), three of which are proved constructively; the fourth is semantic and is exactly where the boundary facades enter (§3.5).

## 3.4 The antipode

The antipode is `antipode_forest`, the linear map underlying `antipodeAlgHom_forest := MvPolynomial.aeval antipodeGen_forest`. The generator map `antipodeGen_forest` is the well-founded recursion of §2.3; well-foundedness is the strict decrease of internal-edge count along the proper coproduct.

The **left** antipode axiom is constructive: the generator-level identity `mul_antipode_rTensor_coproduct_strict_forest_X` is proved by the direct cancellation sketched in §2.4 and globalized to the linear-map form via `MvPolynomial.algHom_ext`. The **right** antipode axiom is the historically delicate one; rather than reproduce the CK §3 forest-cancellation argument, the formalization discharges it through the convolution route of §4. The upshot, established in `AntipodeConvolution.lean`, is that the right axiom is a theorem, not an assumption — the former kernel `AntipodeForestRightCoreIdentity` is eliminated rather than deferred.

## 3.5 The conditional Hopf structure and its residual surface

Assembling the algebra, coalgebra, and antipode yields the conditional instance `HopfAlgebra ℚ HopfH`. After the coassociativity reduction (the forest cover identity, the three constructive hBP Models, and the auxiliary tracks for forest-complement supply, mixed-boundary injectivity, and the canonically-discharged cover data) and the convolution discharge of the right antipode axiom, the residual hypotheses collapse to **exactly two** named boundary-semantics classes:

- `PromotedExternalLegsLiftableModel` — promoted external legs of a contracted subgraph lift back consistently to their pre-contraction identities;
- `ForestGraphInsertionUniquenessModel` — a graph is determined by its vertices together with its remnant after star-contraction.

Each is a single `class … : Prop`. The cross-file certificate `hopfAlgebraHopfH_ofBoundaryFacadesAndReflection_convolution` derives the full `HopfAlgebra ℚ HopfH` structure from these two facades and the power-counting reflection environment alone — with no antipode kernel. This certificate *is* Theorem A in the formalization: it factors the standard flat proof skeleton through precisely two boundary obligations.

Two things are deliberately **not** counted among the residual surface. First, the power-counting environment of §2.1 (`IsPermInvariantDivergence`, `IsIsoInvariantDivergence`, `IsAmbientInvariantDivergence`, `IsDivergencePreservedByContract`, and the forest-contraction preservation/reflection classes): these are standard Weinberg/CK power-counting facts, true for any power-counting measure, and the forest-cover divergence obligation is discharged canonically from the reverse-reflection class rather than assumed. Second, the eliminated antipode kernel. The honest residual surface is therefore the single mechanism named in §3.2 — *flat contraction forgets boundary incidence* — expressed as two `Prop` classes.

## 3.6 Audit status

The development is `sorry`-free, `admit`-free, and free of project-level axioms; the only axioms in the final audit are Lean's standard `propext`, `Classical.choice`, and `Quot.sound`. The full build (`lake build Main`) completes 1475 jobs. The component status is summarized below.

| Component                          | Status                                          |
| ---------------------------------- | ----------------------------------------------- |
| Algebra carrier                    | Constructive                                    |
| Coproduct                          | Constructive modulo boundary interfaces         |
| Counit                             | Constructive                                    |
| Coassociativity                    | Reduced to two boundary interfaces              |
| Left antipode axiom                | Constructive                                    |
| Right antipode axiom               | Constructive via convolution / local nilpotency |
| Remaining interfaces               | Exactly two boundary-semantics facades          |
| Resolved boundary-semantics model  | Inhabited (`boundaryResolvedSemanticModel`)     |
| Forgetful projection to flat       | Definitional (`rfl`)                            |
| `sorry` / `admit`                  | 0                                               |
| Project-level axioms               | 0                                               |
| Build status                       | `lake build Main` — 1475 jobs PASS              |
| Full resolved Hopf structure       | Future work (§8)                                |

## 3.7 What the architecture establishes

At the close of the flat-carrier development, there is no remaining open mathematical kernel on the flat carrier: the conditional Hopf structure is closed modulo exactly the two boundary-semantics facades, and those facades are not gaps in CK's algebra but statements about what the flat carrier can represent. Sections 5–6 make this precise by stating the two facades, exhibiting explicit flat counterexamples to each (Theorem B), and Section 7 repairs the underlying collapse on the boundary-resolved carrier (Theorems C–D). Before that, Section 4 presents the convolution proof that removed the third, formerly-separate, antipode kernel.

---

# 4. A Convolution Proof of the Right Antipode Axiom

The contribution of this section is independent of the boundary-semantics story: it is a proof of the right antipode axiom that does not pass through the classical nested-forest cancellation, and that — because it uses only the coalgebra structure — transfers verbatim to any carrier on which the coproduct is defined. It is what reduced the residual surface from three kernels to two.

We give the argument in full, since it is one of the paper's two independent results and a reviewer must be able to check it without reconstructing missing steps. The structure is standard for connected coalgebras (it is the convolution form of the argument that a connected filtered bialgebra is automatically Hopf), but we state it concretely for the CK carrier.

## 4.1 The classical obstruction

As recalled in §2.4, the left antipode axiom $m \circ (S \otimes \mathrm{id}) \circ \Delta = \eta\varepsilon$ closes by direct cancellation, because the recursive definition of $S$ is built to make it close. The right axiom $m \circ (\mathrm{id} \otimes S) \circ \Delta = \eta\varepsilon$ does not: pushing $m \circ (\mathrm{id} \otimes S)$ through a forest summand $A_{\mathrm{toHopfH}} \otimes \mathrm{gen}(\mathrm{right}\,A)$ leaves $A_{\mathrm{toHopfH}} \cdot S(\mathrm{gen}(\mathrm{right}\,A))$, where $S$ is applied to a single contracted generator, whereas the recursion unfolds $S$ as a *product* over components on the left. The two normal forms do not agree under definitional unfolding, so no `ring`-style cancellation is available.

Three standard escape routes do not apply. Mathlib's convolution development provides the ring structure on $\mathrm{Hom}(C, A)$ but no antipode-uniqueness theorem one could invoke off the shelf. The familiar commutative-algebra shortcut — deriving the right inverse from the left one for *cocommutative* coproducts — does not apply, because the CK coproduct is not cocommutative. And the `MonoidAlgebra` Hopf instance in Mathlib proves its two antipode axioms independently, offering no transferable lemma. The classical alternative is to reproduce the CK 1998 §3 forest-summation recombination; we instead give a structural argument resting on a single grading fact.

## 4.2 The convolution ring

Let $H$ be the coalgebra of §3.3, with coproduct $\Delta$ and counit $\varepsilon$. The set $\mathrm{Hom}_{\mathbb{Q}}(H, H)$ of $\mathbb{Q}$-linear endomorphisms carries the *convolution* product
$$
f * g \;=\; m \circ (f \otimes g) \circ \Delta,
$$
with unit $\mathbf{1} := \eta \circ \varepsilon$. Associativity of $*$ is exactly the coassociativity of $\Delta$, and the unit laws $\mathbf{1} * f = f = f * \mathbf{1}$ are exactly the counit laws. Hence $(\mathrm{Hom}_{\mathbb{Q}}(H,H), *, \mathbf{1})$ is a ring — in the formalization, `WithConv (HopfH →ₗ[ℚ] HopfH)` — and, crucially, **its ring structure depends only on the coalgebra structure of $H$**: coassociativity and counitality, nothing more. It does not presuppose the antipode, the bialgebra compatibility, or the Hopf structure we are in the process of establishing. This is what makes the argument non-circular and carrier-independent.

## 4.3 The reduced coproduct and local nilpotency

The carrier $H$ is *connected graded* by internal-edge count: $H = \bigoplus_{n \ge 0} H_n$ with $H_0 = \mathbb{Q}\cdot 1$, and a connected generator lies in $H_n$ for some $n \ge 1$. (This is the same complexity measure that makes the antipode recursion of §3.4 well-founded.) Write the augmentation ideal $H^+ = \bigoplus_{n \ge 1} H_n = \ker\varepsilon$.

Define the *reduced coproduct* $\tilde\Delta : H^+ \to H^+ \otimes H^+$ by
$$
\tilde\Delta(x) \;=\; \Delta(x) - x \otimes 1 - 1 \otimes x .
$$
In Sweedler notation, $\tilde\Delta(x) = \sum x' \otimes x''$ with both $x', x'' \in H^+$. Connectedness gives the essential grading fact: $\tilde\Delta$ maps $H_n$ into $\bigoplus_{p+q=n,\; p,q \ge 1} H_p \otimes H_q$, so **every factor produced by $\tilde\Delta$ has strictly smaller degree** than its input.

Now consider the reduced operator
$$
N \;=\; \mathrm{id} - \mathbf{1} \;=\; \mathrm{id} - \eta\circ\varepsilon .
$$
On the unit, $N(1) = 0$; on a generator $g \in H^+$, $N(g) = g$ (since $\varepsilon(g) = 0$). The $k$-fold convolution power expands as
$$
N^{*k} \;=\; m^{[k]} \circ N^{\otimes k} \circ \Delta^{[k]},
$$
where $\Delta^{[k]} : H \to H^{\otimes k}$ is the $(k{-}1)$-fold iterated coproduct. Because each tensor slot is hit by $N$, which kills the scalar part and retains only the augmentation-ideal component, $N^{*k}(g)$ collects exactly the terms of the iterated coproduct in which all $k$ factors lie in $H^+$ — i.e. the depth-$k$ part of the iterated *reduced* coproduct. Each such factor has degree $\ge 1$, and their degrees sum to $\deg g$. Hence if $k > \deg g$ there are no such terms and
$$
N^{*k}(g) \;=\; 0 .
$$
Thus $N$ is **locally nilpotent on generators**: for each generator the convolution powers of $N$ vanish past its degree. No forest bookkeeping enters; this is purely the connected/graded shape of the coproduct.

## 4.4 The P-trick

Recall from §3.4 that the left axiom, in convolution form, is precisely
$$
S * \mathrm{id} \;=\; \mathbf{1}.
$$
We want the right identity $\mathrm{id} * S = \mathbf{1}$. Measure its failure by
$$
P \;=\; \mathrm{id} * S - \mathbf{1} \;\in\; \mathrm{Hom}_{\mathbb{Q}}(H,H).
$$

**Step 1 ($P * \mathrm{id} = 0$).** Using associativity of $*$ and the left identity,
$$
P * \mathrm{id} \;=\; (\mathrm{id} * S) * \mathrm{id} - \mathbf{1} * \mathrm{id}
\;=\; \mathrm{id} * (S * \mathrm{id}) - \mathrm{id}
\;=\; \mathrm{id} * \mathbf{1} - \mathrm{id}
\;=\; 0 .
$$

**Step 2 ($P = -\,P * N$).** Since $N = \mathrm{id} - \mathbf{1}$ we have $\mathrm{id} = \mathbf{1} + N$, and $P * \mathbf{1} = P$. Therefore
$$
0 \;=\; P * \mathrm{id} \;=\; P * (\mathbf{1} + N) \;=\; P + P * N
\qquad\Longrightarrow\qquad
P \;=\; -\,P * N .
$$

**Step 3 (iteration).** Substituting Step 2 into itself $k$ times gives, by induction,
$$
P \;=\; (-1)^{k}\, P * N^{*k} \qquad (k \ge 0).
$$

**Step 4 (vanishing on generators).** Fix a generator $g$ with $\deg g = n$ and take any $k > n$. Evaluating the convolution product in Sweedler notation,
$$
\bigl(P * N^{*k}\bigr)(g) \;=\; \sum P\bigl(g_{(1)}\bigr)\, N^{*k}\bigl(g_{(2)}\bigr),
$$
where $g_{(2)}$ ranges over coproduct components of $g$, each of degree $\le n$. By §4.3, $N^{*k}(g_{(2)}) = 0$ for every such component once $k > n$. Hence $(P * N^{*k})(g) = 0$, and by Step 3, $P(g) = 0$. So $P$ vanishes on every generator.

**Step 5 (globalization).** It remains to pass from generators to all of $H$. Here the polynomial-algebra structure is used. Both $\mathrm{id} * S$ and $\mathbf{1} = \eta\circ\varepsilon$ are *algebra homomorphisms* $H \to H$: $\eta\circ\varepsilon$ visibly so, and $\mathrm{id} * S = m \circ (\mathrm{id}\otimes S)\circ\Delta$ because in a commutative target the convolution product of two algebra homomorphisms ($\mathrm{id}$ and the algebra map $S$) is again an algebra homomorphism, $\Delta$ being an algebra map. Two algebra homomorphisms out of $H = \mathrm{MvPolynomial}\,\mathrm{HopfGen}\,\mathbb{Q}$ that agree on all generators are equal, by `MvPolynomial.algHom_ext`. Step 4 says exactly that $\mathrm{id} * S$ and $\mathbf{1}$ agree on every generator (both send a nonempty generator to $0$ and $1$ to $1$); therefore
$$
\mathrm{id} * S \;=\; \mathbf{1} \quad\text{on all of } H,
$$
which is the right antipode axiom. (Note that `algHom_ext` is applied to the *algebra maps* $\mathrm{id}*S$ and $\mathbf 1$, not to $P$, which is not itself an algebra map.)

## 4.5 Consequence

In the formalization this argument lives in `AntipodeConvolution.lean`, and the facade `AntipodeStrictForestRightReady` is discharged by `AntipodeStrictForestRightReady_ofConvolution`, bypassing the former kernel `AntipodeForestRightCoreIdentity` entirely. The right antipode axiom is therefore a theorem, and the residual surface of the conditional Hopf structure (§3.5) is the two boundary facades — not three. The earlier connector that derived the axiom from the cancellation kernel is retained in the source but is no longer on the proof path; the final cross-file certificate `hopfAlgebraHopfH_ofBoundaryFacadesAndReflection_convolution` assembles the full Hopf structure from the two boundary facades and the power-counting environment, with no antipode kernel.

## 4.6 Why this is a result, not an implementation trick

Two points deserve emphasis. First, the argument is *mathematical*, not an artifact of Lean. It replaces an explicit, delicate forest-summation cancellation with a single structural observation — local nilpotency of the reduced coproduct (§4.3) — followed by the three-line convolution manipulation of §4.4. The right-inverse property of the antipode follows from the connected/graded shape of the coproduct, not from the combinatorics of nested forests. In hindsight this is the "right" reason the axiom holds: it is the convolution-ring expression of the standard fact that a connected graded bialgebra is automatically a Hopf algebra, with the left antipode supplying the inverse on one side and local nilpotency forcing it to be two-sided.

Second, and importantly for the rest of the paper, the argument is **carrier-independent**. It uses only that $H$ is a connected graded coalgebra whose reduced coproduct lowers degree, together with the polynomial-algebra carrier for the final extensionality step; it never inspects the graph representation underlying the generators. Consequently the same proof discharges the right antipode axiom on the boundary-resolved carrier without modification. When the full resolved reconstruction is undertaken (§8), the antipode is therefore *not* part of the cost: it is inherited. The expensive, carrier-sensitive work in any resolved program is the coproduct and coassociativity — precisely the parts that touch the boundary identities the next sections are about.

---

# 5. The Two Boundary Interfaces

With the antipode discharged, the entire residual surface of the conditional Hopf structure is two named `Prop` classes. This section states them precisely, explains where in the coassociativity proof they are forced, identifies the single carrier mechanism behind both, and — in §5.5 — fixes how Theorem A must be read so that the conditional instance is not mistaken for a vacuous implication. The counterexamples that make the two interfaces *false* on the flat carrier are deferred to §6 (Theorem B); the present section is about what the interfaces say and why they are needed.

## 5.1 Where the two interfaces arise

The interfaces are not bolted on; they are forced by the coassociativity proof at exactly two points. Recall from §2.5 that coassociativity reduces to the F2i-3q forest cover identity: a summand-for-summand bijection between the two ways of doubly extracting subgraphs from a graph. Establishing that bijection requires, at the generator level, reconstructing the first-extraction datum from the doubly-contracted result — what the formalization calls the `q.1` recovery, partitioning each term into left-boundary, right-boundary, and forest-parent contributions.

Three of the four structural sub-obligations of this cover identity (the "hBP" Models) are discharged constructively, as is the mixed-boundary injectivity branch (`mixed_inj`, the product of an eight-sprint free-index campaign) and the forest-cover connected-divergence data (discharged canonically from the power-counting environment). Two branches of the `q.1` recovery, however, cannot be closed on the flat carrier, and each is isolated as a single semantic interface:

- the **internal-edge branch** of the forest injectivity (`forest_inj`) needs to know that a graph is recoverable from its vertices and its post-contraction remnant — this is **Interface 2**;
- the **promoted-external-legs branch** needs to know that legs promoted by contraction lift back consistently to their pre-contraction identities — this is **Interface 1**.

Everything else in coassociativity is a theorem. The two interfaces are the precise residue of the recovery step that §2.5 flagged as tacit on paper.

## 5.2 Interface 1: Promoted external legs liftability

When a divergent subgraph $\gamma$ is contracted inside $\Gamma$, some internal edges of $\Gamma$ that met $\gamma$ become external legs of the contracted graph — they are *promoted* to legs of the quotient. The coassociativity bijection requires that these promoted legs can be lifted back, consistently, to the half-edges they came from: that the promotion is invertible on the relevant boundary data.

Formally this is the class `PromotedExternalLegsLiftableModel` (appearing in `Coassoc.lean` as the promoted-legs branch of the forest cover, `ForestQuotientForestSigmaForestCoverPromotedExternalLegsLiftableModel`). Informally: *after contracting a subgraph, the promoted external legs lift back consistently to their pre-contraction identities.*

The reason this is delicate on the flat carrier is structural, and we state it now though the counterexample waits until §6. A flat external leg is the datum $\{\,\textsf{attachedTo},\ \textsf{sector}\,\}$ — an attachment vertex and a sector label. It carries no record of which half-edge or boundary slot produced it. So two legs that were genuinely distinct before contraction — distinct half-edges of distinct edges — but that happen to share an attachment vertex and a sector become **the same flat leg** after promotion. The lift back is then ill-defined: there is no consistent inverse, because the forward map has already merged data the inverse would need to separate.

## 5.3 Interface 2: Forest graph insertion uniqueness

The second interface concerns the inverse problem for contraction itself. The coassociativity bijection needs that a graph is determined by the combination of its vertex set and the remnant left after star-contraction — equivalently, that knowing what was contracted and what remains pins down the original insertion uniquely.

Formally this is `ForestGraphInsertionUniquenessModel` (in `Coassoc.lean`, gating the internal-edge branch of `forest_inj`). Informally: *a graph is determined by its vertices together with its remnant after star-contraction.*

Again the difficulty is that flat contraction discards the data this uniqueness would need. The single-star contraction `contractWith` collapses each component of the contracted subgraph to a star vertex; the remnant records adjacency and sector, but not which insertion slot of the star a given edge attached to. Two structurally different graphs — differing in how edges were distributed across insertion slots — can therefore produce the *same* vertices-plus-remnant pair. The map from graphs to (vertices, remnant) is not injective on the flat carrier, so insertion is not unique.

## 5.4 The common mechanism

Although the two interfaces concern different objects — promoted legs in one case, internal-edge insertions in the other — they are two faces of a single carrier property, already named in §3.2:

> Single-star contraction on the flat carrier is **lossy**: it forgets boundary incidence and attachment multiplicity.

Both interfaces ask the flat carrier to invert a map that has discarded exactly the identity information needed to invert it. In both cases the obstruction is a **multiset-level collapse of structurally distinct boundary data**: distinct half-edges or insertion slots, carrying no persistent identity, become equal elements of a multiset of flat legs or edges, and a multiset cannot be un-merged. This single phrase — multiset-level collapse of structurally distinct boundary data — is the mechanism behind both interfaces, behind both counterexamples of §6, and behind the repair of §7. It is worth fixing as the paper's organizing diagnosis.

Crucially, this is not a statement about Connes and Kreimer's mathematics. In their intended notion of graph, half-edges and insertion slots are distinct objects; the informal proof uses that distinctness freely. The interfaces are statements about a *representation* — they say that the flat encoding, which represents legs and edges only by attachment and sector, is too coarse to carry the distinctness the proof relies on.

## 5.5 Reading Theorem A correctly

This subsection is load-bearing, and it must precede the counterexamples. It fixes the status of the conditional Hopf instance so that the reader does not mistake it for a vacuous implication once §6 proves its hypotheses false.

Recall the conditional result assembled in §3.5, which we now name:

> **Theorem A (Flat proof-obligation factorization).** If a graph carrier satisfies Promoted External Legs Liftability and Forest Graph Insertion Uniqueness, then the Connes–Kreimer Hopf-algebraic skeleton closes over that carrier — concretely, `HopfAlgebra ℚ HopfH` holds, with the right antipode axiom already supplied by §4. In the formalization this is `hopfAlgebraHopfH_ofBoundaryFacadesAndReflection_convolution`.

The essential point is **how this theorem is used, and how it is not.**

*It is not presented as an unconditional theorem about the flat carrier.* We do not claim that the flat carrier carries a CK Hopf algebra. We claim that the standard flat proof skeleton *factors* through exactly two boundary obligations: it is a decomposition of the classical proof into the part that goes through unconditionally (everything in §§3–4) and the precise semantic residue that does not. Read this way, Theorem A is a statement about *any* carrier — "a carrier satisfying these two interfaces supports the construction" — and is silent about whether the flat carrier is such a carrier.

*Section 6 then answers that silent question in the negative.* The flat carrier does **not** support the recovery the interfaces demand: Theorem B exhibits, by machine-checked and fully concrete witnesses (`by decide`), the exact multiset collapse those interfaces would have to rule out. We establish this concrete collapse rather than a global negation $\lnot P_{\text{flat}}$ of the facade classes themselves — a distinction of formalization hygiene explained in §6.5, and one that strengthens the claim rather than weakening it. Theorem A and Theorem B are therefore presented as a pair. Together they make a single, strong, diagnostic statement:

> The standard flat proof skeleton requires two boundary-semantics properties that the flat carrier cannot satisfy.

This is the anticipated reviewer objection, stated plainly and answered:

> *Objection.* If the two hypotheses are false on the flat carrier, is the conditional Hopf instance not vacuous?
>
> *Answer.* It would be vacuous only if it were advertised as an unconditional theorem about the flat carrier. It is not. The conditional instance is a proof-decomposition (factorization) theorem: its content is that it isolates the exact semantic requirements hidden by the informal flat notation. The non-vacuous *positive* content is supplied separately, by the boundary-resolved carrier of §7, on which the corresponding distilled identity-preservation principles are proved as theorems (Theorem C) and shown to project definitionally onto the flat maps (Theorem D).

Two further points complete the framing.

First, **the failure of the recovery on the flat carrier is one of the paper's findings, not a defect of the formalization.** The decidable collapse witnesses of §6 are the precise, machine-checked form of the observation in §2.5 that the informal proof tacitly assumes the quotient remembers its insertion. The formalization shows that, on the flat representation, it does not — and that this is exactly the recovery the two interfaces would have required. Far from weakening the contribution, this concrete, decidable failure is the contribution's sharpest single statement.

Second, the resolved witness of §7 does **not** instantiate the flat facade classes, and is not claimed to. Those classes are formulated in the flat language and are false there; the forgetful map runs from the resolved carrier to the flat one, not the other way. What §7 provides is the *distilled* content of each interface, proved on the refined carrier, together with a definitional projection (§7.3) showing that the resolved maps forget precisely to the flat collapse maps. The relationship between the false flat hypotheses and the true resolved principles is therefore not asserted rhetorically; it is the subject of Theorem D.

A single sentence, suitable for the abstract or the reviewer response, summarizes the stance:

> The conditional flat-carrier instance is not an unconditional theorem about the flat carrier; it is a factorization theorem identifying the exact two semantic properties the flat carrier would need to support the standard CK proof. We then prove those properties false on the flat carrier and exhibit their distilled forms — with a definitional forgetful projection — on the boundary-resolved carrier.

With Theorem A's status fixed, we turn to the counterexamples that establish Theorem B.

---

# 6. Counterexamples on the Flat Carrier

This section establishes the negative half of the diagnosis: on the flat carrier, the recovery that each boundary interface demands provably fails. We make this concrete and machine-checked — but, as §6.5 explains, we formalize the *collapse mechanism* the interfaces would have to rule out, rather than attempting a global negation of the facade classes themselves. The mechanism behind both failures is the single phenomenon named in §5.4, multiset-level collapse of structurally distinct boundary data, and §6.4 shows that the formalized collapse is the exact mirror of the resolved injectivity of §7.

## 6.1 What Theorem B asserts, and what it deliberately does not

> **Theorem B (Flat collapse).** On the flat carrier there are concrete configurations on which the boundary recovery fails: the flat retargeting maps underlying the two interfaces are not injective, and the failure persists at the multiset level. Formally, four machine-checked theorems witness this — `flatEdgeRetarget_not_injective`, `flatLegRetarget_not_injective`, `flatEdgeRetarget_multiset_collapse`, and `flatLegRetarget_multiset_collapse`.

These live in a self-contained file, `GaugeGeometry/QFT/HopfAlgebra/BoundaryResolvedCounterexamples.lean`, which leaves the existing Hopf and coassociativity proofs untouched and does not instantiate or negate any facade class. The witnesses are fully concrete: the vertex type is the standard `Nat`, the colliding retarget map is the constant `fun _ => 0`, and the two configurations differ only in an endpoint identity. Every statement is closed by `by decide`, so the failures are decided by computation rather than argued.

What Theorem B deliberately does **not** assert is the global negation `¬ ForestGraphInsertionUniquenessModel` or `¬ PromotedExternalLegsLiftableModel`. The reason is discussed in §6.5; in brief, those classes are stated over the abstract divergence environment, and a blanket negation would over-reach. What we need — and what suffices for the diagnosis paired with Theorem A — is the concrete collapse the interfaces are there to forbid.

## 6.2 The promoted-leg collapse

The first interface asks that legs promoted by contraction lift back consistently to their pre-contraction identities. The flat obstruction is that the leg-level retargeting map merges distinct legs. Concretely, take two external legs that differ only in their pre-contraction identity but share attachment and sector, and apply the colliding endpoint map. Their images under `flatLegRetarget` coincide: as flat legs they are both $\{\textsf{attachedTo}, \textsf{sector}\}$ with the identity data gone. This is `flatLegRetarget_not_injective`, decided by `by decide`.

The failure is not an artifact of working with single legs: it survives at the level of the multiset of legs that the coassociativity recovery actually manipulates. Two distinct singleton leg-multisets map to the *same* multiset under leg-retargeting — `flatLegRetarget_multiset_collapse` — so the recovery, which would have to invert this multiset map, cannot exist. Hence the promoted-leg liftability the interface requires fails on the flat carrier, by an explicit decidable witness.

## 6.3 The insertion/edge collapse

The second interface asks that a graph be determined by its vertices and its remnant after star-contraction — equivalently, that distinct edge insertions remain distinguishable. The flat obstruction is the edge-level analogue of §6.2. Two internal edges that differ only in an endpoint identity, sharing sector data, are merged by the colliding endpoint map: their images under `flatEdgeRetarget` coincide. This is `flatEdgeRetarget_not_injective`, again `by decide`, and it lifts to the multiset level as `flatEdgeRetarget_multiset_collapse`, where two distinct singleton edge-multisets collapse to one.

Because the remnant of a star-contraction is exactly such a multiset of edges (with sectors) around the star vertex, the collapse means two structurally distinct insertions produce the same remnant: the map from graphs to (vertices, remnant) is not injective. Insertion uniqueness therefore fails on the flat carrier, witnessed concretely.

## 6.4 The shared mechanism, and its mirror on the resolved carrier

The four witnesses are two phenomena — leg collapse and edge collapse — but a single mechanism. In each case the colliding endpoint map sends structurally distinct boundary objects to equal flat data, and the multiset that the recovery must invert loses the distinction irrecoverably. This is the multiset-level collapse of §5.4, now decided by computation rather than described.

The decisive structural point is the relationship between these collapse theorems and the resolved carrier of §7. The multiset collapse witnesses, `flatEdgeRetarget_multiset_collapse` and `flatLegRetarget_multiset_collapse`, are stated for exactly the same multiset retargeting operations whose injectivity *holds* on the resolved carrier — the submultiset-injectivity fields of `BoundaryResolvedSemanticModel` (§7.2). The same operation that collapses on the flat carrier is injective on the resolved one; the only difference is the persistent identity that the resolved edges and legs carry and the flat ones do not. The counterexamples of this section and the preservation theorems of the next are therefore not two separate investigations — they are the two values of one map, taken before and after forgetting the identities, a correspondence made definitional in §7.3.

## 6.5 Why we formalize the collapse, not the negation of the facade classes

A reviewer may ask why Theorem B does not simply state `¬ ForestGraphInsertionUniquenessModel` and `¬ PromotedExternalLegsLiftableModel`. The answer is a point of formalization hygiene that strengthens, rather than weakens, the claim.

The facade classes are `Prop`-classes formulated over the abstract divergence environment of §2.1 and the ambient graph assumptions. A global negation `¬ Model` asserts that *no* instance can be derived under *any* admissible specialization of that environment. This over-reaches in two ways. First, deciding it would in general require committing to a concrete divergence measure, abandoning the abstraction that the rest of the development is careful to preserve. Second, a sufficiently degenerate specialization could make a class vacuously inhabited, which would make a blanket `¬ Model` outright false — so a proof of `¬ Model`, were one to appear, would be cause for suspicion rather than confidence.

What is both true and useful is the existential statement: there is a concrete flat configuration on which the collapse the interface forbids actually occurs. That is what the four decidable witnesses provide, at exactly the multiset granularity the coassociativity recovery operates on. They pin down *the precise collapse* the facades are there to exclude, without touching the facade classes, without instantiating or negating them, and without disturbing the existing conditional Hopf proof. The new file builds green on its own.

Finally, as in §5.4, none of this is a counterexample to the Connes–Kreimer Hopf algebra. In CK's intended notion of graph, the colliding endpoint map would not identify distinct half-edges, because those carry distinct identities; the informal proof is correct. The witnesses show only that the flat encoding — legs and edges as attachment-plus-sector data — is too coarse to carry that distinctness. Read together with Theorem A, they turn a vague "the flat notation is informal here" into a decidable, machine-checked claim: the standard proof skeleton requires two recovery properties (Theorem A), and on the flat carrier the precise collapse those properties forbid demonstrably occurs (Theorem B). What remains is to restore the lost distinctions without changing CK's mathematics — the content of Section 7.

---

# 7. Boundary-Resolved Graphs: Preservation and Projection

The diagnosis of §§5–6 located the entire residual surface in one mechanism: the flat carrier records boundary objects as attachment-plus-sector multisets, with no persistent identity, so distinct sources collapse and cannot be recovered. The repair is correspondingly simple to state — give edges and legs persistent identities — but its value depends on two things being true at once. The repaired carrier must actually *satisfy* the distilled recovery principles (otherwise the repair is empty), and it must be the *same* mathematics as the flat carrier, recovered by forgetting the identities (otherwise the repair has changed the problem). The first is Theorem C; the second is Theorem D. Together they show that the resolved principles are not cherry-picked analogues of the flat collapse but its boundary-refined versions, differing by exactly the persistent identity.

## 7.1 The resolved carrier

The boundary-resolved carrier `ResolvedFeynmanGraph` is the flat carrier with persistent identities adjoined. Each internal edge carries an identity `edgeId` in addition to its endpoints and sector (`ResolvedFeynmanEdge`); each external leg carries a `legId` alongside its attachment and sector (`ResolvedExternalLeg`). A resolved graph is a multiset of such edges and legs over a vertex set, subject to uniqueness conditions `EdgeIdsUnique` and `LegIdsUnique` that prevent two distinct edges or legs from sharing an identity.

Two operations are central. *Retargeting* `retarget f` rewrites endpoints along a vertex map $f$ while **preserving identities**: the `edgeId`/`legId` of each edge or leg is carried through unchanged. The basic identity lemmas `ResolvedFeynmanEdge.eq_of_retarget_eq_of_id_unique` and its leg analogue record that, under the uniqueness conditions, a retargeted edge is determined by its identity. The *forgetful map* `forget : ResolvedFeynmanGraph → FeynmanGraph` discards the identities, returning each edge to its flat datum $\{\textsf{source}, \textsf{target}, \textsf{sector}\}$ and each leg to $\{\textsf{attachedTo}, \textsf{sector}\}$. The flat carrier is exactly the forgetful image of the resolved one.

## 7.2 Theorem C — resolved preservation (the non-vacuity witness)

The distilled content of the two boundary interfaces is packaged as a single carrier-level structure, `BoundaryResolvedSemanticModel`, with **five fields organized as two pillars**. The first pillar is the subject of this subsection; the second is Theorem D (§7.3).

**Pillar 1 — injectivity before forgetting.** The two fields here are the resolved forms of the recovery properties that failed on the flat carrier:

- `retargetInternalEdges_injective_on_submultisets` — internal-edge retargeting is injective on submultisets;
- `retargetExternalLegs_injective_on_submultisets` — external-leg retargeting is injective on submultisets.

These are exactly the principles whose flat versions collapsed in §6, and they are precisely what is needed to close the two coassociativity branches of §5.1: the first discharges the core of insertion uniqueness (Gap 2), the second the core of promoted-leg liftability (Gap 1). The reason they *hold* on the resolved carrier is the persistent identity. On the flat carrier, the colliding endpoint map of §6 merged edges that differed only in endpoints; on the resolved carrier those edges still carry distinct `edgeId`s, so even when the endpoints coincide the resolved edges remain distinct, and the multiset map cannot collapse them. The single engine behind both fields is a generic count-extensionality lemma, `Multiset.map_eq_of_injOn_le`: once the underlying map is injective on the relevant identities, the induced submultiset map is injective.

**The witness.** The structure is not merely defined; it is *inhabited*:
$$
\texttt{boundaryResolvedSemanticModel} \;:\; \texttt{BoundaryResolvedSemanticModel}.
$$
This is the content of Theorem C, and it is the non-vacuous positive result the conditional flat theorem (Theorem A) cannot supply on its own. Where Theorem A says "a carrier satisfying these interfaces supports the construction" and Theorem B says "the flat carrier does not," Theorem C exhibits a carrier that *does*.

One point must be stated precisely, because it is the crux of the vacuity discussion of §5.5. The witness does **not** instantiate the flat facade classes `PromotedExternalLegsLiftableModel` or `ForestGraphInsertionUniquenessModel`. It cannot: those classes are formulated in the flat language and are false there (§6), and the forgetful map runs from the resolved carrier *to* the flat one, not back. What the witness inhabits is the **distilled** form of each interface — the recovery principle restated for a carrier that carries identities. The relationship between the false flat facades and these true distilled principles is not asserted; it is the subject of Theorem D.

## 7.3 Theorem D — forgetful definitional projection (the bridge)

Pillar 2 of `BoundaryResolvedSemanticModel` records that the resolved retargeting, after forgetting identities, *is* the flat collapse map — not merely related to it, but equal to it definitionally.

First the flat maps are named. `flatEdgeRetarget f` and `flatLegRetarget f` are the flat endpoint/attachment rewrites: $f$ applied to the endpoints of a flat edge, respectively the attachment of a flat leg, with the sector unchanged. These are not new constructions invented for convenience — they are the named form of the endpoint map already appearing in the resolved commuting square `forget_retargetGraph`, and they are the endpoint action underlying the (Finset/star-based) flat retargeting; in particular they are *not* the star-based `FeynmanEdge.retarget`, and choosing the correct target is exactly what makes the next lemma hold by `rfl`. They are also the maps that collapse in §6: the witnesses there are `flatEdgeRetarget`/`flatLegRetarget` non-injectivity and multiset collapse.

The three fields of Pillar 2 are then:

- `edge_forget_retarget_commutes`: $(e.\texttt{retarget}\,f).\texttt{forget} = \texttt{flatEdgeRetarget}\,f\,(e.\texttt{forget})$ — **by `rfl`**;
- `leg_forget_retarget_commutes`: the leg analogue — **by `rfl`**;
- the graph-level square `forget_retargetGraph`: $\texttt{forget} \circ \texttt{retargetGraph}\,f = \texttt{flatEdgeRetarget}\,f \circ \texttt{forget}$ (with the leg component), lifted to multisets by `map_forget_retarget_edges` / `map_forget_retarget_legs` via `Multiset.map_map`.

The force of the result is in the `rfl`. The two sides are not merely provably equal by some constructed chain of rewrites; they are *definitionally* equal — the same term. Computing the left side, retargeting carries the identity through and moves the endpoints by $f$, and forgetting then discards the identity, leaving $\{f(\textsf{source}), f(\textsf{target}), \textsf{sector}\}$; computing the right side, forgetting discards the identity and `flatEdgeRetarget` moves the endpoints by $f$, leaving the same. There is nothing to prove. This is the precise sense in which **the moment the persistent identity is dropped, the resolved retargeting becomes the flat collapse map syntactically.** The difference between the injective resolved behaviour (Pillar 1) and the collapsing flat behaviour (§6) is exactly the persistent identity, and the equality of the two maps modulo that identity is fixed at the type level rather than argued.

## 7.4 Why Theorems C and D together close the cherry-picking objection

The two pillars answer the objection a careful reviewer raises against any "repaired" carrier: that one has simply invented convenient lemmas on a new object and declared them the analogues of the broken ones. The objection has real force in general, and it is answered here not rhetorically but by the structure of the witness.

Pillar 1 (Theorem C) provides injectivity — the resolved carrier genuinely supports the recovery, and the witness is inhabited, so the principles are not vacuous. Pillar 2 (Theorem D) provides the identification — the resolved maps forget, definitionally, to exactly the flat maps that collapse in §6. The collapse witnesses of §6.4 and the injectivity fields of §7.2 are therefore *the same multiset operation evaluated on either side of the forgetful map*: injective with the identities present, collapsing once they are dropped. Their relationship is the `rfl` of Theorem D. A reviewer cannot maintain that the resolved injectivity is an unrelated convenience, because forgetting the identities returns, verbatim, the flat map whose failure was the whole problem.

The summary is the paper's organizing sentence, now earned rather than asserted: the resolved carrier does not change the Connes–Kreimer mathematics; it makes explicit the boundary information the informal notation was already using, and what separates the repaired behaviour from the collapsing one is exactly one persistent identity. The full unconditional reconstruction over this carrier — re-deriving the coproduct and coassociativity so that the two facades become outright theorems rather than distilled witnesses — is a separate program, taken up in §8.

---

# 8. Claim Boundary and Future Work

This section states exactly what the paper establishes, answers the one structural objection the framing invites, and delimits the larger reconstruction that is deliberately out of scope. The boundary is drawn sharply on purpose: the present claim is complete as stated, and the reconstruction beyond it is a separate program, not a missing step.

## 8.1 The present claim

The paper establishes, with `sorry`-free, axiom-free Lean proofs (final audit: the standard `propext`, `Classical.choice`, `Quot.sound`; full build 1475 jobs):

- **(A)** A factorization of the standard flat CK proof skeleton: the conditional `HopfAlgebra ℚ HopfH` holds over any carrier satisfying the two boundary-semantics interfaces, with the right antipode axiom already supplied unconditionally.
- **(Antipode)** An independent convolution / local-nilpotency proof of the right antipode axiom, eliminating the former CK §3 cancellation kernel and carrier-independent by construction (§4).
- **(B)** Machine-checked, fully decidable witnesses (`by decide`) that the precise collapse the two interfaces forbid actually occurs on the flat carrier (§6) — without over-claiming a global negation of the facade classes (§6.5).
- **(C)** An inhabited witness `boundaryResolvedSemanticModel` that the boundary-resolved carrier satisfies the distilled forms of both interfaces (§7.2).
- **(D)** A definitional (`rfl`) forgetful projection identifying the resolved retargeting maps with the flat collapse maps up to the persistent identity (§7.3).

The honest one-line summary of the residual surface: after the antipode is discharged, the entire dependency of the CK Hopf structure on unverified hypotheses is the single mechanism "flat contraction forgets boundary incidence," expressed as two `Prop` classes, shown to fail concretely on the flat carrier and to hold on a carrier that keeps the forgotten identities.

## 8.2 The vacuity objection, answered

Because the conditional instance (A) has hypotheses that the flat carrier does not satisfy, a reviewer may ask whether it is vacuous. The full answer is in §5.5 and §6.5; we restate it here in one place.

The conditional instance is not advertised as an unconditional theorem about the flat carrier — it is a *factorization* of the standard proof, isolating the exact semantic obligations the informal argument uses tacitly. Its hypotheses' failure on the flat carrier is established concretely, by the decidable collapse witnesses of §6, not by a global negation of the facade classes (which would over-reach against the abstract divergence environment; §6.5). The non-vacuous positive content is supplied separately, by the inhabited resolved witness (C); and the relationship between the false flat hypotheses and the true resolved principles is not rhetorical but definitional, via the `rfl` projection (D). A conditional theorem whose antecedent is independently shown unsatisfiable on the flat carrier, paired with a concrete carrier on which the distilled antecedent holds and a definitional bridge between the two, is a localization-and-repair result — not a vacuous implication.

## 8.3 Out of scope: the full resolved reconstruction (R-4-full)

The natural stronger claim — a full *unconditional* CK Hopf algebra over the resolved carrier, with the two facades discharged as outright theorems — is deliberately **not** attempted here, and its absence is not a gap in the present contribution. It is a separate, larger formalization program. We state plainly why excluding it is the right scope decision, and why it is a well-defined program rather than an open problem.

First, the present claim does not depend on it. Theorems A–D form a complete localization-and-repair result on their own: the proof skeleton is factored (A), the flat obstruction is decided (B), the repaired carrier is inhabited (C), and the two are identified definitionally (D). Nothing in this story is left dangling pending R-4-full.

Second, the path is already understood; what remains is re-derivation along known lines, not the resolution of any open mathematical kernel. The reconstruction decomposes cleanly:

- a *resolved subgraph spine* — resolved analogues of subgraphs, admissible subgraphs, the `toFlat`/forget maps, resolved contraction, and the proper forest index, together with the retarget injectivity lemmas (the last already in hand, as Theorem C uses them);
- a *resolved coproduct* — a transcription of the flat coproduct construction, with the collapse-prone steps shortened by the resolved injectivity machinery (the R-3 count-extensionality engine) rather than re-fought;
- *resolved coassociativity* — on which the two boundary facades become theorems, since the identities the flat carrier lacked are now present;
- the *antipode*, which is **inherited at no cost**: the convolution proof of §4 is carrier-independent and applies verbatim once the resolved coproduct is in place.

The genuinely new work is therefore confined to the resolved coproduct and coassociativity re-derivation; the antipode transfers and the injectivity is already proved. This is a substantial engineering effort — realistically a multi-month program — but it is engineering along a mapped route, not a search for a missing idea. There is no remaining open kernel on the flat carrier (§3.7), and the resolved program inherits the hardest non-combinatorial piece for free.

Drawing the boundary here is the honest and the strategically correct choice: it lets the present, self-contained contribution stand on its own terms, and it frames the reconstruction as the natural continuation it is.

## 8.4 Suggested phrasing for the claim boundary

A single passage, suitable for the introduction and the conclusion, fixes the boundary:

> The present work identifies the exact semantic boundary at which the flat carrier ceases to support the informal Connes–Kreimer proof: it factors the standard proof skeleton through two boundary-semantics interfaces, shows those interfaces fail concretely on the flat carrier, and exhibits a boundary-resolved carrier on which their distilled forms hold and which forgets, definitionally, back to the flat maps. The full unconditional reconstruction over the resolved carrier is a natural continuation along an understood path, but it is not required for — and does not diminish — the contribution established here.

---

# 9. Related Work

We position the paper against four bodies of work: the Connes–Kreimer construction itself, the formalization of Hopf-algebraic structures in proof assistants, the convolution approach to antipodes, and the proof-engineering practice of isolating and auditing assumptions.

## 9.1 The Connes–Kreimer Hopf algebra and renormalization

The Hopf algebra of Feynman graphs originates with Kreimer's Hopf algebra of rooted trees and the Connes–Kreimer papers on renormalization and the Riemann–Hilbert problem [Kre98, CK00, CK01], where renormalization is realized as a Birkhoff decomposition of a loop of characters and the coproduct encodes the combinatorics of the BPHZ/Zimmermann forest formula [Zim69]. Subsequent work relates the diverse renormalization schemes through Hopf-algebraic convolution [EGK05] and studies non-diagrammatic and operadic descriptions of the same algebra. Our concern is orthogonal to the physics: we treat only the combinatorial coproduct, counit, and antipode, and specifically the points at which their standard proofs assume that contraction remembers boundary data. We take no position on regularization or the Riemann–Hilbert side of the theory.

## 9.2 Hopf-algebraic structures in proof assistants

The abstract theory of coalgebras, bialgebras, and Hopf algebras has recently been formalized in Lean's Mathlib, including the convolution monoid on $\mathrm{Hom}(C,A)$ and the Hopf structure on monoid algebras [Mathlib; see also the ICMS 2024 formalization of coalgebra/bialgebra/Hopf algebra]. We build directly on this layer — the convolution ring of §4 is Mathlib's — but the present work is of a different kind: rather than developing the general theory, it constructs a *specific, combinatorially defined* Hopf algebra, the CK algebra of Feynman graphs, over an explicit graph carrier. To our knowledge there is no prior machine-checked formalization of the Connes–Kreimer Hopf algebra in any proof assistant; the present skeleton, conditional on exactly two named boundary interfaces, appears to be the first.

## 9.3 The antipode via convolution and connectedness

That the antipode of a connected (graded or filtered) bialgebra exists and is computable by a convolution geometric series is classical: it underlies Takeuchi's construction of free Hopf algebras on coalgebras [Tak71] and is used explicitly in the rooted-tree treatments of renormalization, where antipode images are computed by convolution [EGK05]. Our §4 is the proof-assistant realization of this idea for the Feynman-graph carrier: we phrase the right antipode axiom as the statement that $\mathrm{id}$ is convolution-invertible with the recursively-defined $S$ as inverse, and discharge it by local nilpotency of the reduced coproduct rather than by the explicit CK §3 forest cancellation. The contribution is not the convolution idea, which is standard, but its use to *eliminate a formerly-separate cancellation kernel* in a machine-checked development, and the observation that, being carrier-independent, it transfers without cost to the resolved program.

## 9.4 Formal graph theory and assumption auditing

General graph theory is well represented in proof-assistant libraries (for example Mathlib's `SimpleGraph`), but the half-edge / insertion-slot structure that the CK boundary semantics depends on is not part of these developments, and is exactly what our flat carrier turns out to lack. On the methodological side, the paper sits in the proof-engineering tradition of isolating residual assumptions as named, auditable hypotheses and tracking precisely what a development depends on. What is perhaps less standard is the use of that discipline *diagnostically*: the named facades here are not loose ends to be tidied away but the located output of the analysis, and the decision to formalize the collapse mechanism rather than to negate the facade classes globally (§6.5) is a deliberate choice about where machine-checking should and should not make a claim.

## 9.5 Positioning

The novelty is therefore not primarily that a Hopf algebra has been formalized, but that formalization has *exposed and localized a semantic mismatch* between an informal graph notation and a machine-checkable carrier — and then repaired it, definitionally, on a refined carrier. The paper is as much about what the flat notation silently assumes as about the Hopf algebra it supports; the contribution is a finding about representation, made precise by the discipline of formalization.

---

# 10. Conclusion

Formalizing the Connes–Kreimer Hopf algebra over an explicit Feynman-graph carrier does three things, which the paper has presented along a four-theorem spine.

First, it mechanizes the CK Hopf-algebraic construction over a flat carrier up to an exactly auditable boundary. The algebra, coproduct, counit, coassociativity, and antipode are built with no `sorry`, no `admit`, and no project-level axioms; the conditional `HopfAlgebra ℚ HopfH` is closed modulo precisely two named boundary-semantics interfaces (Theorem A), and the right antipode axiom — historically a separate forest-cancellation obligation — is proved outright by a convolution / local-nilpotency argument that eliminates the former kernel and, being carrier-independent, will transfer to any resolved reconstruction at no cost (§4).

Second, it shows those two interfaces fail on the flat carrier, and shows it concretely: four decidable witnesses exhibit the exact multiset collapse the interfaces forbid (Theorem B), while deliberately stopping short of a global negation of the facade classes, which would over-reach against the abstract divergence environment (§6.5).

Third, it repairs the collapse on a boundary-resolved carrier without altering CK's mathematics: the resolved carrier inhabits the distilled forms of both interfaces (Theorem C), and the forgetful projection identifies the resolved retargeting with the flat collapse maps *definitionally*, by `rfl`, so that the repaired and collapsing behaviours differ by exactly the persistent identity (Theorem D). The flat counterexamples and the resolved preservation theorems are thereby revealed as the same multiset operation, evaluated on the two sides of the forgetful map.

Taken together, the development turns an informal "this step is obvious" — the tacit assumption that a contracted quotient remembers its insertion — into a precise, machine-checked account: the assumption is exactly two boundary-semantics interfaces, it is false on the flat carrier, and it becomes true on a carrier that keeps the identities the flat notation discarded. The remaining work is not to patch the flat proof but to rebuild the construction over the resolved carrier the formalization has now made explicit. What the flat notation called obvious, the resolved carrier makes a theorem — and what separates the two is exactly one persistent identity.

---

# Appendix A. Lean Artifact Overview

This appendix is a navigation aid for re-checking the artifact. It records the module structure, the principal Lean names, the theorem-status table with source locations, and the build/audit facts. The module split mirrors the mathematical layering: a flat combinatorial carrier, an algebraic layer with the Hopf-structure proofs, and a boundary-resolved layer with the repair; the convolution antipode and the flat counterexamples are isolated in their own files so that neither perturbs the conditional Hopf proof.

**A.1 Module dependency graph.**
Verified direct-import edges (each arrow reads "is imported by"), current source:

```
Core.Sector
  └─► FeynmanGraphs.lean
        ├─► SubGraph.lean ──(Coproduct → Counit algebra layer)──► Coassoc.lean
        │                                                    └──► Antipode.lean ──► AntipodeConvolution.lean
        │                                                                                   └──► HopfAlgebra.lean
        └─► ResolvedFeynmanGraphs.lean
              └─► BoundaryResolved.lean ◄── (also imports Coassoc.lean)
                    └─► BoundaryResolvedCounterexamples.lean
```

Direct `import` lines (verbatim, restricted to the nine files):

- `FeynmanGraphs.lean` imports `Core.Sector`.
- `SubGraph.lean` imports `FeynmanGraphs`, `SupportGraph`.
- `ResolvedFeynmanGraphs.lean` imports `FeynmanGraphs`.
- `Coassoc.lean` imports `Counit`; `Antipode.lean` imports `Counit` (both reach `SubGraph` through the intermediate `Coproduct → Counit` algebra-layer files).
- `AntipodeConvolution.lean` imports `Bialgebra`, `Antipode`.
- `HopfAlgebra.lean` imports `Bialgebra`, `Antipode`, `AntipodeConvolution`.
- `BoundaryResolved.lean` imports `Coassoc`, `ResolvedFeynmanGraphs`.
- `BoundaryResolvedCounterexamples.lean` imports `BoundaryResolved`.

`AntipodeConvolution.lean` is imported only by `HopfAlgebra.lean` (it supplies the right-antipode instance) and is independent of the `Coassoc` coproduct proof; `BoundaryResolvedCounterexamples.lean` is a leaf, imported by no other artifact module (only by the top-level `Main.lean` entry point). The resolved layer branches off `FeynmanGraphs.lean` and rejoins the algebraic spine only at `BoundaryResolved.lean`.

**A.2 Principal Lean names.**
| Object | Lean name | file:line | Role |
| --- | --- | --- | --- |
| Generators | `HopfGen` | `StrictGenerators.lean:269` | `{ c : FeynmanGraphClass // c.IsConnectedDivergent }` |
| Carrier algebra | `HopfH` | `StrictGenerators.lean:289` | `noncomputable abbrev HopfH : Type := MvPolynomial HopfGen ℚ` |
| Coproduct | `coproduct_strict_forest` | `Coproduct.lean:3588` | `HopfH →ₐ[ℚ] HopfH ⊗[ℚ] HopfH`, strict-forest CK coproduct |
| Counit | `counit` | `Counit.lean:76` | `HopfH →ₐ[ℚ] ℚ` |
| Antipode | `antipode_forest` | `Antipode.lean:156` | `HopfH →ₗ[ℚ] HopfH` |
| Forest cover identity (F2i-3q) | `coassoc_strict_forest_linearMap` | `Coassoc.lean:39219` | coassociativity of `coproduct_strict_forest` as a `LinearMap` equality |
| Conditional Hopf instance | `instHopfAlgebraHopfHStrictForest` | `HopfAlgebra.lean:82` | conditional `HopfAlgebra ℚ HopfH` (gated on the two facades) |
| Facade 1 | `ForestGraphInsertionUniquenessModel` | `Coassoc.lean:7084` | insertion-uniqueness interface |
| Facade 2 | `ForestQuotientForestSigmaForestCoverPromotedExternalLegsLiftableModel` | `Coassoc.lean:23790` | promoted-leg liftability interface |
| Resolved carrier | `ResolvedFeynmanGraph` | `ResolvedFeynmanGraphs.lean:60` | identity-carrying analogue of `FeynmanGraph` |
| Forgetful map | `ResolvedFeynmanGraph.forget` | `ResolvedFeynmanGraphs.lean:99` | `ResolvedFeynmanGraph → FeynmanGraph` (discards `edgeId`/`legId`) |

**A.3 Theorem-status table.** This is the §3.6 table with exact identifiers and locations.
| Component | Status | Backing Lean identifier (file:line) |
| --- | --- | --- |
| Algebra carrier | Constructive | `HopfH` (`StrictGenerators.lean:289`) |
| Coproduct | Constructive modulo boundary interfaces | `coproduct_strict_forest` (`Coproduct.lean:3588`) |
| Counit | Constructive | `counit` (`Counit.lean:76`) |
| Coassociativity | Reduced to two boundary interfaces | `coassoc_strict_forest_linearMap` (`Coassoc.lean:39219`); certificate `coassocStrictForestH58Ready_ofBoundaryFacadesAndReflection` (`HopfAlgebra.lean:102`) |
| Left antipode axiom | Constructive | `mul_antipode_rTensor_coproduct_strict_forest_X` (`Antipode.lean:332`), globalized `mul_antipode_rTensor_coproduct_strict_forest` (`Antipode.lean:451`) |
| Right antipode axiom | Constructive via convolution / local nilpotency | `AntipodeStrictForestRightReady_ofConvolution` (`AntipodeConvolution.lean:298`) |
| Remaining interfaces | Exactly two boundary-semantics facades | `ForestGraphInsertionUniquenessModel` (`Coassoc.lean:7084`), `ForestQuotientForestSigmaForestCoverPromotedExternalLegsLiftableModel` (`Coassoc.lean:23790`) |
| Resolved boundary-semantics model | Inhabited | `boundaryResolvedSemanticModel` (`BoundaryResolved.lean:192`) |
| Forgetful projection to flat | Definitional (`rfl`) | `forget_retarget_edge` / `forget_retarget_leg` (`BoundaryResolved.lean:102` / `:106`) |
| Conditional Hopf instance | Two-facade certificate | `hopfAlgebraHopfH_ofBoundaryFacadesAndReflection_convolution` (`HopfAlgebra.lean:136`) |

**A.4 Build and audit.**
Verified against the current repository:

- **Build target / job count.** `lake build Main` completes **1476 jobs**, exit 0. (`Main.lean` imports `HopfAlgebra`, `AntipodeConvolution`, `BoundaryResolved`, `BoundaryResolvedCounterexamples`, `AxiomAudit`, `ResolvedFeynmanGraphs` and `#check`s the headline certificates.)
- **`sorry` / `admit`.** 0. The only textual occurrences of these strings in the sources are in prose docstrings ("…both sides admit AlgHom upgrades", "…no `sorry`"); there is no `sorry`/`admit` tactic.
- **Project-level axioms.** 0 (no `axiom` declarations on the proof path).
- **`#print axioms`** of the top cross-file certificate:

```
'GaugeGeometry.QFT.Combinatorial.hopfAlgebraHopfH_ofBoundaryFacadesAndReflection_convolution'
  depends on axioms: [propext, Classical.choice, Quot.sound]
```

i.e. only Lean's three standard axioms; in particular `sorryAx` is absent, and the former antipode kernel `AntipodeForestRightCoreIdentity` does not appear (the convolution instance `AntipodeStrictForestRightReady_ofConvolution` is the one selected).

> **[CC-MISMATCH: §3.6 vs current build]** The frozen §3.6 table states "1475 jobs". The current `lake build Main` reports **1476 jobs**: the extra job is `BoundaryResolvedCounterexamples.lean` (Theorem B / Appendix B), added to `Main` after §3.6 was written. Reconcile §3.6 to 1476, or note that 1475 is the count of the conditional-Hopf closure excluding the counterexample witnesses.

**A.5 Exact statements of the residual surface.**
**Facade 1 — insertion uniqueness** (`Coassoc.lean:7084`):

```lean
class ForestGraphInsertionUniquenessModel : Prop where
  parent_eq_of_remnant_eq :
    ∀ {G : FeynmanGraph} [DivergenceMeasure G]
      (A : AdmissibleSubgraph G) (starOf : FeynmanSubgraph G → VertexId)
      {γ₁ γ₂ : FeynmanSubgraph G},
        γ₁.vertices = γ₂.vertices →
        admissibleSubgraphQuotientRemainderSubgraph A starOf γ₁ =
          admissibleSubgraphQuotientRemainderSubgraph A starOf γ₂ →
        γ₁ = γ₂
```

**Facade 2 — promoted-leg liftability** (`Coassoc.lean:23790`):

```lean
class
    ForestQuotientForestSigmaForestCoverPromotedExternalLegsLiftableModel : Prop where
  promoted_externalLegs_le_plus :
    ∀ [IsDivergencePreservedByAdmissibleForestContract]
      (g : HopfGen)
      (r : {r : forestQuotientForestSigma g //
        r ∈ forestQuotientForestSigmaIndex g})
      (δ : FeynmanSubgraph (forestOuterActualQuotientGraph g r.1.1))
      (η : FeynmanSubgraph (repG g).toFeynmanGraph),
        η ∈ forestQuotientForestSigmaForestCoverPromotedComponents g r δ →
          η.externalLegs ≤
            (forestQuotientForestSigmaForestCoverSourceSubgraphExactPlus
              g r δ).externalLegs
```

**The witness structure** `BoundaryResolvedSemanticModel` (`BoundaryResolved.lean:144`), five fields:

```lean
structure BoundaryResolvedSemanticModel : Prop where
  edge_submultiset_retarget_injective :
    ∀ (G : ResolvedFeynmanGraph), G.EdgeIdsUnique → ∀ (f : VertexId → VertexId)
      {M₁ M₂ : Multiset ResolvedFeynmanEdge},
      M₁ ≤ G.internalEdges → M₂ ≤ G.internalEdges →
      M₁.map (ResolvedFeynmanEdge.retarget f) =
        M₂.map (ResolvedFeynmanEdge.retarget f) →
      M₁ = M₂
  leg_submultiset_retarget_injective :
    ∀ (G : ResolvedFeynmanGraph), G.LegIdsUnique → ∀ (f : VertexId → VertexId)
      {L₁ L₂ : Multiset ResolvedExternalLeg},
      L₁ ≤ G.externalLegs → L₂ ≤ G.externalLegs →
      L₁.map (ResolvedExternalLeg.retarget f) =
        L₂.map (ResolvedExternalLeg.retarget f) →
      L₁ = L₂
  forget_retargetGraph_commutes :
    ∀ (G : ResolvedFeynmanGraph) (f : VertexId → VertexId) (V : Finset VertexId),
      (G.retargetGraph f V).forget =
        { vertices := V
          internalEdges := G.forget.internalEdges.map
            (fun e => { source := f e.source, target := f e.target, sector := e.sector })
          externalLegs := G.forget.externalLegs.map
            (fun ℓ => { attachedTo := f ℓ.attachedTo, sector := ℓ.sector }) }
  edge_forget_retarget_commutes :
    ∀ (f : VertexId → VertexId) (M : Multiset ResolvedFeynmanEdge),
      (M.map (ResolvedFeynmanEdge.retarget f)).map ResolvedFeynmanEdge.forget =
        (M.map ResolvedFeynmanEdge.forget).map (flatEdgeRetarget f)
  leg_forget_retarget_commutes :
    ∀ (f : VertexId → VertexId) (M : Multiset ResolvedExternalLeg),
      (M.map (ResolvedExternalLeg.retarget f)).map ResolvedExternalLeg.forget =
        (M.map ResolvedExternalLeg.forget).map (flatLegRetarget f)
```

---

# Appendix B. Flat Counterexamples (Theorem B)

This appendix gives the formal versions of the four decidable witnesses of §6 and explains, for each, which part of the coassociativity argument it concerns and why the witness configuration is sufficient.

**B.1 The witness configuration.** All four theorems use the concrete vertex type `Nat`, the colliding endpoint map `fun _ => 0`, and two configurations differing only in an endpoint (or leg) identity. The choice of `fun _ => 0` is not a special case chosen for convenience: it is the minimal non-injective endpoint map — it sends every vertex to a single point — so it exhibits the collapse in the simplest configuration that can possibly witness non-injectivity. Anything that collapses under a more elaborate map already collapses under this one. Each statement is closed by `by decide`, so the failure is decided by computation; the file builds green on its own and instantiates or negates no facade class.

**B.2 Edge collapse.**
`flatEdgeRetarget_not_injective` (`BoundaryResolvedCounterexamples.lean:33`) and its multiset form `flatEdgeRetarget_multiset_collapse` (`:56`):

```lean
theorem flatEdgeRetarget_not_injective :
    ∃ (f : VertexId → VertexId) (e₁ e₂ : FeynmanEdge),
      e₁ ≠ e₂ ∧ flatEdgeRetarget f e₁ = flatEdgeRetarget f e₂ :=
  ⟨fun _ => 0,
   (⟨0, 2, .hypercharge⟩ : FeynmanEdge),
   (⟨1, 2, .hypercharge⟩ : FeynmanEdge),
   by decide, by decide⟩

theorem flatEdgeRetarget_multiset_collapse :
    ∃ (f : VertexId → VertexId) (M₁ M₂ : Multiset FeynmanEdge),
      M₁ ≠ M₂ ∧ M₁.map (flatEdgeRetarget f) = M₂.map (flatEdgeRetarget f) :=
  ⟨fun _ => 0,
   {(⟨0, 2, .hypercharge⟩ : FeynmanEdge)},
   {(⟨1, 2, .hypercharge⟩ : FeynmanEdge)},
   by decide, by decide⟩
```

The two edges `⟨0, 2, .hypercharge⟩` and `⟨1, 2, .hypercharge⟩` differ only in their `source` (vertices `0` vs `1`); under `f = fun _ => 0` both retarget to `⟨0, 0, .hypercharge⟩`, and the singleton multisets `{e₁}`, `{e₂}` collapse to the same image.
The non-injectivity is the edge-level obstruction to insertion uniqueness: two internal edges differing only in an endpoint identity have equal images under `flatEdgeRetarget`. The multiset form is the one that matters for the proof, because the remnant of a star-contraction is a *multiset* of edges around the star vertex; its collapse is exactly the failure of the internal-edge branch of `forest_inj` identified in §5.1, i.e. the core of `ForestGraphInsertionUniquenessModel`.

**B.3 Leg collapse.**
`flatLegRetarget_not_injective` (`BoundaryResolvedCounterexamples.lean:44`) and its multiset form `flatLegRetarget_multiset_collapse` (`:66`):

```lean
theorem flatLegRetarget_not_injective :
    ∃ (f : VertexId → VertexId) (ℓ₁ ℓ₂ : ExternalLeg),
      ℓ₁ ≠ ℓ₂ ∧ flatLegRetarget f ℓ₁ = flatLegRetarget f ℓ₂ :=
  ⟨fun _ => 0,
   (⟨0, .hypercharge⟩ : ExternalLeg),
   (⟨1, .hypercharge⟩ : ExternalLeg),
   by decide, by decide⟩

theorem flatLegRetarget_multiset_collapse :
    ∃ (f : VertexId → VertexId) (M₁ M₂ : Multiset ExternalLeg),
      M₁ ≠ M₂ ∧ M₁.map (flatLegRetarget f) = M₂.map (flatLegRetarget f) :=
  ⟨fun _ => 0,
   {(⟨0, .hypercharge⟩ : ExternalLeg)},
   {(⟨1, .hypercharge⟩ : ExternalLeg)},
   by decide, by decide⟩
```

The two legs `⟨0, .hypercharge⟩` and `⟨1, .hypercharge⟩` differ only in their `attachedTo` vertex (`0` vs `1`); under `f = fun _ => 0` both retarget to `⟨0, .hypercharge⟩`, collapsing the singleton multisets. All four theorems are closed by `by decide` over `VertexId = Nat`, so the failure is decided by computation; the file builds green standalone and instantiates or negates no facade class.
Symmetrically, this is the leg-level obstruction to promoted-leg liftability: two legs differing only in identity collapse under `flatLegRetarget`, and the multiset collapse is the failure of the promoted-legs branch of the forest cover (§5.1), i.e. the core of `PromotedExternalLegsLiftableModel`.

**B.4 Why the collapse, not `¬ Model`.** As discussed in §6.5, we do not prove the global negations `¬ ForestGraphInsertionUniquenessModel` or `¬ PromotedExternalLegsLiftableModel`. These classes are stated over the abstract divergence environment; a blanket negation would assert that no admissible specialization can inhabit them, which over-reaches (a sufficiently degenerate measure could make a class vacuously hold, falsifying the negation) and would force a concrete divergence measure, abandoning the abstraction maintained elsewhere. The four witnesses instead pin down, at the exact multiset granularity the coassociativity recovery operates on, the precise collapse the facades are there to exclude — which is what the diagnosis requires.

**B.5 Mirror on the resolved carrier.** The multiset-collapse statements here are the exact mirror of the submultiset-injectivity fields of `BoundaryResolvedSemanticModel` (Appendix D.2): the same multiset operation that collapses here is injective there. The two are related, definitionally, by the forgetful projection of Appendix D.3 — see §7.4.

---

# Appendix C. The Convolution Proof of the Right Antipode Axiom (§4)

This appendix gives the formal version of the §4 argument. The conceptual content — why the standard escape routes fail, why the reduced operator is nilpotent, and how the P-trick globalizes — is recalled here alongside the exact Lean statements.

**C.1 Why off-the-shelf tools do not apply.** As in §4.1: Mathlib's convolution development supplies the ring structure on `Hom(C, A)` but no antipode-uniqueness theorem; the commutative-algebra route from the left inverse to the right inverse requires cocommutativity of the coproduct, which the CK coproduct does not have; and the `MonoidAlgebra` Hopf instance proves its two antipode axioms independently. Hence a direct structural argument.

**C.2 The convolution ring.** The argument lives in the convolution ring on endomorphisms of `HopfH`, whose product is convolution and whose unit is `η∘ε`; its ring structure uses only the coalgebra structure (coassociativity and counitality), not the antipode or the Hopf compatibility.
The carrier is `WithConv HopfHEnd` where `abbrev HopfHEnd := HopfH →ₗ[ℚ] HopfH` (`AntipodeConvolution.lean:52`); its `Ring` structure is Mathlib's `LinearMap.convRing`, which needs only `[Coalgebra ℚ HopfH]` (supplied here by `CoassocStrictForestH58Ready` via `instCoalgebraHopfHStrictForest`), **not** the Hopf structure — so there is no circularity. The two elements used:

```lean
abbrev HopfHEnd := HopfH →ₗ[ℚ] HopfH                          -- :52
noncomputable def convId : WithConv HopfHEnd :=               -- :55
  WithConv.toConv (LinearMap.id : HopfH →ₗ[ℚ] HopfH)
noncomputable def convS : WithConv HopfHEnd :=                -- :59
  WithConv.toConv antipode_forest
```

The product is convolution (`LinearMap.convMul_def`: `f * g = toConv (mul' ∘ map f g ∘ comul)`) and the unit is `η∘ε` (`LinearMap.convOne_def`: `1 = toConv (Algebra.linearMap ℚ HopfH ∘ counit)`).

**C.3 The left identity and the reduced operator.** The left antipode axiom, in convolution form, is `S * id = 1`.
The linear-form left axiom is `mul_antipode_rTensor_coproduct_strict_forest` (`Antipode.lean:451`):

```lean
theorem mul_antipode_rTensor_coproduct_strict_forest :
    (LinearMap.mul' ℚ HopfH).comp
        ((antipode_forest.rTensor HopfH).comp coproduct_strict_forest.toLinearMap)
      = (Algebra.linearMap ℚ HopfH).comp counit.toLinearMap
```

Recast in `WithConv` it is exactly `convS * convId = 1` (`convS_mul_convId_eq_one`, `AntipodeConvolution.lean:74`), proved by `congrArg WithConv.toConv` from the line above.
The reduced operator is `N = id − η∘ε`. It is locally nilpotent on generators, and the reason is a grading fact, not bookkeeping: the carrier is connected graded by internal-edge count, and the reduced coproduct strictly lowers that grading, so the depth-`k` part of the iterated reduced coproduct vanishes once `k` exceeds the degree of a generator. Hence `N^{*k}` annihilates each generator past its degree.
The reduced operator is `reducedConv := convId - 1` (`AntipodeConvolution.lean:103`). Local nilpotency on generators is `reducedConv_pow_gen_eq_zero` (`:151`):

```lean
theorem reducedConv_pow_gen_eq_zero (g : HopfGen) {n : ℕ}
    (h : (repG g).toFeynmanGraph.internalEdges.card + 1 < n) :
    ((reducedConv ^ n : WithConv HopfHEnd)) (MvPolynomial.X g) = 0
```

The grading/complexity measure is the **internal-edge count** `(repG g).toFeynmanGraph.internalEdges.card`; the reduced coproduct strictly lowers it, formalized as `antipodeForestRight_internalEdges_card_lt` (`Antipode.lean:499`), which states that each proper-forest contraction summand has strictly fewer internal edges than `g`. The proof is a strong induction on that count (the `+ 1` slack covers `0`-edge primitive generators, which vanish at power `2`).

**C.4 The P-trick.** Following the five steps of §4.4: with `P = id*S − 1`, (1) `P * id = 0` from associativity and the left identity; (2) since `id = 1 + N`, `P = −P*N`; (3) iterating, `P = (−1)^k P*N^{*k}`; (4) evaluating on a generator and choosing `k` past its degree gives `P = 0` on generators; (5) since both `id*S` and `η∘ε` are algebra homomorphisms (the target is commutative and `Δ` is an algebra map), `MvPolynomial.algHom_ext` upgrades generator-wise agreement to `id*S = 1` on all of `HopfH`. Note that `algHom_ext` is applied to the algebra maps `id*S` and `η∘ε`, not to `P`, which is not an algebra map.
All five steps live in `convId_mul_convS_apply_gen_eq_one` (`AntipodeConvolution.lean:254`) and its helpers:

- **(1) `P * convId = 0`** and **(2)–(3) the iterated form** are packaged by the generic ring lemma `self_eq_mul_pow_of_mul_one_add_eq_zero` (`:234`): from `P * (1 + N) = 0` it derives `P = P * N^(2j)` for all `j` (via `P*N = −P`, so `P*N² = P`). Inside `convId_mul_convS_apply_gen_eq_one`, `P := convId * convS - 1`, the step `P * convId = 0` is `hPconvId` (from `convS_mul_convId_eq_one`), and `convId = 1 + reducedConv` is `hsum`.
- **(4) generator-wise vanishing**: `withConv_mul_reducedConv_pow_gen_eq_zero` (`:199`) applies `reducedConv_pow_gen_eq_zero` under a left multiplier, killing `P (X g)` once `j` exceeds the edge count; this yields `convId_mul_convS_apply_gen_eq_one : (convId * convS)(X g) = 1 (X g)`.
- **(5) globalization**: `rightAxiomLHSAlg_eq` (`:289`) uses `MvPolynomial.algHom_ext` to upgrade the generator equality to `rightAxiomLHSAlg = (Algebra.ofId ℚ HopfH).comp counit`. As the prose notes, `algHom_ext` is applied to the **algebra homomorphisms** `rightAxiomLHSAlg` (the `id ⊗ S` packaging) and `(Algebra.ofId ℚ HopfH).comp counit`, not to `P` (which is not an algebra map). The intermediate generator bridge is `mul_antipode_lTensor_coproduct_strict_forest_X` (`:277`), a definitional (`:= convId_mul_convS_apply_gen_eq_one g`) restatement.

**C.5 Discharge and reuse.** The facade `AntipodeStrictForestRightReady` is discharged via the convolution route, bypassing the former kernel.
The discharge is the instance `AntipodeStrictForestRightReady_ofConvolution` (`AntipodeConvolution.lean:298`):

```lean
noncomputable instance AntipodeStrictForestRightReady_ofConvolution :
    AntipodeStrictForestRightReady where
  mul_antipode_lTensor_coproduct_strict_forest := ...   -- from rightAxiomLHSAlg_eq
```

It carries **no** `AntipodeForestRightCoreIdentity` hypothesis. That former kernel still exists in source (the class is declared at `Antipode.lean:575`, with its own connector instance `[AntipodeForestRightCoreIdentity] → AntipodeStrictForestRightReady` at `:711`), but it is off the proof path: the final certificate `hopfAlgebraHopfH_ofBoundaryFacadesAndReflection_convolution` assumes only the two boundary facades and the power-counting reflection, so instance resolution selects the hypothesis-free convolution instance — confirmed by the `#print axioms` of A.4, which shows only `propext`, `Classical.choice`, `Quot.sound` (no `AntipodeForestRightCoreIdentity`, no `sorryAx`).
Because C.2–C.4 use only the coalgebra structure and the polynomial-algebra carrier, the argument is carrier-independent and transfers unchanged to the resolved reconstruction (Appendix D.4) at no additional cost.

---

# Appendix D. Forgetful Correspondence and Future Resolved Reconstruction (§7, §8)

This appendix records the resolved carrier, the five fields of the witness, the definitional projection, and the scope of the future reconstruction.

**D.1 The resolved carrier.** Edges and legs carry persistent identities; retargeting preserves them; the forgetful map discards them and recovers the flat carrier as its image.
All in `ResolvedFeynmanGraphs.lean`. The identity tags and carriers (`:32`, `:37`, `:43`, `:52`, `:60`):

```lean
structure ResolvedEdgeId where id : Nat                         -- :32  (deriving DecidableEq, Repr)
structure ResolvedLegId where id : Nat                          -- :37
structure ResolvedFeynmanEdge where                             -- :43
  edgeId : ResolvedEdgeId; source : VertexId; target : VertexId; sector : GaugeSector
structure ResolvedExternalLeg where                             -- :52
  legId : ResolvedLegId; attachedTo : VertexId; sector : GaugeSector
structure ResolvedFeynmanGraph where                            -- :60
  vertices : Finset VertexId
  internalEdges : Multiset ResolvedFeynmanEdge
  externalLegs : Multiset ResolvedExternalLeg
```

The forgetful map drops the ids (`:99`); the uniqueness predicates (`:173`, `:178`); the id-preserving edge retarget (`:129`, leg analogue `:153`):

```lean
def ResolvedFeynmanGraph.forget (G : ResolvedFeynmanGraph) : FeynmanGraph :=   -- :99
  { vertices := G.vertices
    internalEdges := G.internalEdges.map ResolvedFeynmanEdge.forget
    externalLegs := G.externalLegs.map ResolvedExternalLeg.forget }
def EdgeIdsUnique (G : ResolvedFeynmanGraph) : Prop :=                          -- :173
  ∀ e₁ ∈ G.internalEdges, ∀ e₂ ∈ G.internalEdges, e₁.edgeId = e₂.edgeId → e₁ = e₂
def LegIdsUnique (G : ResolvedFeynmanGraph) : Prop :=                           -- :178
  ∀ ℓ₁ ∈ G.externalLegs, ∀ ℓ₂ ∈ G.externalLegs, ℓ₁.legId = ℓ₂.legId → ℓ₁ = ℓ₂
def ResolvedFeynmanEdge.retarget (f : VertexId → VertexId) (e) :               -- :129
  ResolvedFeynmanEdge := { edgeId := e.edgeId, source := f e.source, target := f e.target, sector := e.sector }
```

The id-determination lemmas — the heart of the repair — are `ResolvedFeynmanEdge.eq_of_retarget_eq_of_id_unique` (`:187`) and `ResolvedExternalLeg.eq_of_retarget_eq_of_id_unique` (`:198`):

```lean
theorem ResolvedFeynmanEdge.eq_of_retarget_eq_of_id_unique
    {G : ResolvedFeynmanGraph} (hId : G.EdgeIdsUnique)
    {f : VertexId → VertexId} {e₁ e₂ : ResolvedFeynmanEdge}
    (he₁ : e₁ ∈ G.internalEdges) (he₂ : e₂ ∈ G.internalEdges)
    (h : e₁.retarget f = e₂.retarget f) : e₁ = e₂
```

(and `…ExternalLeg…` with `LegIdsUnique`). The proof reads the preserved `edgeId`/`legId` off `h` and applies uniqueness — so even when `f` collapses endpoints, the ids force equality.

**D.2 Pillar 1 — injectivity before forgetting.** These are the resolved forms of the principles that collapse in Appendix B. They hold because the persistent identity survives retargeting: even when endpoints coincide under the colliding map, distinct `edgeId`/`legId` keep the edges/legs distinct, so the submultiset map cannot collapse. The single engine is a generic count-extensionality lemma.
The two resolved injectivity principles (`ResolvedFeynmanGraphs.lean:370`, `:385`):

```lean
theorem ResolvedFeynmanGraph.retargetInternalEdges_injective_on_submultisets
    (G : ResolvedFeynmanGraph) (hId : G.EdgeIdsUnique) {f : VertexId → VertexId}
    {M₁ M₂ : Multiset ResolvedFeynmanEdge}
    (hM₁ : M₁ ≤ G.internalEdges) (hM₂ : M₂ ≤ G.internalEdges)
    (h : M₁.map (ResolvedFeynmanEdge.retarget f) = M₂.map (ResolvedFeynmanEdge.retarget f)) :
    M₁ = M₂

theorem ResolvedFeynmanGraph.retargetExternalLegs_injective_on_submultisets
    (G : ResolvedFeynmanGraph) (hId : G.LegIdsUnique) {f : VertexId → VertexId}
    {M₁ M₂ : Multiset ResolvedExternalLeg}
    (hM₁ : M₁ ≤ G.externalLegs) (hM₂ : M₂ ≤ G.externalLegs)
    (h : M₁.map (ResolvedExternalLeg.retarget f) = M₂.map (ResolvedExternalLeg.retarget f)) :
    M₁ = M₂
```

Both are one-line corollaries of the single engine `Multiset.map_eq_of_injOn_le` (`:339`), fed the id-determination lemma (D.1) as the injectivity-on-`S` hypothesis:

```lean
theorem Multiset.map_eq_of_injOn_le {α β : Type*} [DecidableEq α] [DecidableEq β]
    {f : α → β} {S M₁ M₂ : Multiset α}
    (hInj : Set.InjOn f {x | x ∈ S})
    (hM₁ : M₁ ≤ S) (hM₂ : M₂ ≤ S) (h : M₁.map f = M₂.map f) : M₁ = M₂
```

The proof is `count`-extensionality (`Multiset.count_map_eq_count`): on submultisets of `S`, `count` of an image is `count` of the preimage, so equal images force equal multisets.

**D.3 Pillar 2 — exact projection after forgetting (Theorem D).** The flat maps `flatEdgeRetarget`/`flatLegRetarget` are the named form of the endpoint map already in the resolved commuting square `forget_retargetGraph`; they are *not* the star-based `FeynmanEdge.retarget`, and choosing this correct target is exactly what makes the projection hold by `rfl`. The force of the result is that the equality is *definitional*, not a constructed chain: computing either side yields the same flat datum `{f(source), f(target), sector}`, so there is nothing to prove. This is why the cherry-picking objection is answered (§7.4): forgetting the identities returns, verbatim, the very flat maps whose collapse is the whole problem (Appendix B), so the resolved injectivity (D.2) and the flat collapse (B) are the same operation on the two sides of `forget`.
The flat collapse maps (`BoundaryResolved.lean:94`, `:98`):

```lean
def flatEdgeRetarget (f : VertexId → VertexId) (e : FeynmanEdge) : FeynmanEdge :=
  { source := f e.source, target := f e.target, sector := e.sector }
def flatLegRetarget (f : VertexId → VertexId) (ℓ : ExternalLeg) : ExternalLeg :=
  { attachedTo := f ℓ.attachedTo, sector := ℓ.sector }
```

The projection (Theorem D), **proved by `rfl`** — both sides compute to the same flat datum (`:102`, `:106`):

```lean
theorem forget_retarget_edge (f : VertexId → VertexId) (e : ResolvedFeynmanEdge) :
    (e.retarget f).forget = flatEdgeRetarget f e.forget := rfl
theorem forget_retarget_leg (f : VertexId → VertexId) (ℓ : ResolvedExternalLeg) :
    (ℓ.retarget f).forget = flatLegRetarget f ℓ.forget := rfl
```

Their multiset liftings (`:111`, `:119`), proved by `map_map` + `map_congr` over the `rfl` lemmas:

```lean
theorem map_forget_retarget_edges (f : VertexId → VertexId) (M : Multiset ResolvedFeynmanEdge) :
    (M.map (ResolvedFeynmanEdge.retarget f)).map ResolvedFeynmanEdge.forget =
      (M.map ResolvedFeynmanEdge.forget).map (flatEdgeRetarget f)
theorem map_forget_retarget_legs (f : VertexId → VertexId) (M : Multiset ResolvedExternalLeg) :
    (M.map (ResolvedExternalLeg.retarget f)).map ResolvedExternalLeg.forget =
      (M.map ResolvedExternalLeg.forget).map (flatLegRetarget f)
```

`flatEdgeRetarget`/`flatLegRetarget` are exactly the endpoint/attachment maps appearing in the graph-level commuting square `forget_retargetGraph` (`ResolvedFeynmanGraphs.lean:289`):

```lean
theorem forget_retargetGraph (G : ResolvedFeynmanGraph)
    (f : VertexId → VertexId) (V : Finset VertexId) :
    (G.retargetGraph f V).forget =
      { vertices := V
        internalEdges := G.forget.internalEdges.map
          (fun e => { source := f e.source, target := f e.target, sector := e.sector })
        externalLegs := G.forget.externalLegs.map
          (fun ℓ => { attachedTo := f ℓ.attachedTo, sector := ℓ.sector }) }
```

— distinct from the star-based flat `FeynmanEdge.retarget (γ : Finset) (star)`; choosing this vertex-map target is what makes the projection definitional.
The inhabited witness (`BoundaryResolved.lean:192`):

```lean
theorem boundaryResolvedSemanticModel : BoundaryResolvedSemanticModel := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro G hId _f M₁ M₂ hM₁ hM₂ h
    exact resolved_insertion_internalEdges_unique G hId hM₁ hM₂ h
  · intro G hId _f L₁ L₂ hL₁ hL₂ h
    exact resolved_promotedExternalLegs_unique G hId hL₁ hL₂ h
  · intro G f V
    exact resolved_forget_retargetGraph_commutes G f V
  · intro f M
    exact map_forget_retarget_edges f M
  · intro f M
    exact map_forget_retarget_legs f M
```

The five fields are discharged respectively by the two submultiset-injectivity lemmas (D.2), the graph-level commuting square (`forget_retargetGraph`, D.3), and the two multiset liftings (D.3). So the structure is not merely consistent but provably inhabited on the resolved carrier.

**D.4 R-4-full: a scoped future program.** The full unconditional reconstruction over the resolved carrier is future work, and — per §8.3 — it is well-scoped engineering along a known route, not the resolution of an open kernel. Phase 1 builds the resolved subgraph spine; the retarget injectivity it needs is already proved (D.2). Phase 2 transcribes the flat coproduct, with the collapse-prone steps shortened by the count-extensionality engine of D.2 rather than re-fought. Resolved coassociativity then turns the two facades into theorems; and the antipode is inherited at no cost, since the convolution proof of Appendix C is carrier-independent. The only genuinely new work is the resolved coproduct/coassociativity re-derivation.
Phase 1 of this program is **already formalized**, in `Combinatorial/ResolvedSubGraph.lean` (a standalone module: built by `lake build GaugeGeometry.QFT.Combinatorial.ResolvedSubGraph`, not yet imported by `Main`, so outside the A.4 job count). Present targets:

| Resolved spine target | Lean name (file:line) | Status |
| --- | --- | --- |
| Resolved subgraph | `ResolvedFeynmanSubgraph` (`ResolvedSubGraph.lean:27`) | ✅ present |
| Subgraph forget | `ResolvedFeynmanSubgraph.forget` (`:56`), spine square `forget_toFeynmanGraph` | ✅ present |
| Resolved admissible forest | `ResolvedAdmissibleSubgraph` (`:136`), `forget` (`:174`) | ✅ present |
| Component selection | `componentAt` (`:211`), `retargetVertex` (`:242`) | ✅ present |
| Resolved contraction | `contractWithStars` (`:286`), `forget_contractWithStars` | ✅ present |
| Quotient remainder | `quotientRemainderSubgraph` (`:407`), `retargetSubgraph` (`:376`) | ✅ present |
| Resolved insertion uniqueness | `parent_eq_of_remainder_eq` (`:537`), residual injectivity `retarget_residual_edges_injective` (`:509`) | ✅ present (resolved form of Facade 1) |
| Resolved proper-forest index | `ResolvedAdmissibleSubgraph.IsProperForest`, `ResolvedProperForestFiniteCover` (`ResolvedCoproductIndex.lean`, `ResolvedCoproduct.lean`) | ✅ present |
| Resolved coproduct | `ResolvedHopfPayloadFamily.resolvedCoproduct`, `resolvedCoproduct_toLinearMap_eq_flat` (`ResolvedCoproduct.lean`) | ✅ present (= flat coproduct as a linear map) |
| Resolved coassociativity | `resolvedCoproduct_coassoc_ofReflection` (`ResolvedCoproduct.lean`) | ✅ present (by transfer, gated on the two facades) |
| Payload family inhabited | `resolvedHopfPayloadFamily_exists` (`ResolvedPayloadModel.lean`) | ✅ present (non-vacuity) |
| Hopf-structure certificate | `resolvedHopfStructureCertificate_holds`, `exists_resolvedHopfStructureCertificate` (`ResolvedHopfCertificate.lean`) | ✅ present (coassoc + counit×2 + antipode×2) |

Update (these are now formalized, not future): the retarget submultiset injectivity is exactly D.2; `parent_eq_of_remainder_eq` realizes the resolved Facade 1 at the remainder level; the resolved coproduct equals the flat one as a linear map and inherits coassociativity by transfer; and — closing the vacuity question for the payload itself — **the payload hypothesis is inhabited**: `resolvedHopfPayloadFamily_exists : Nonempty ResolvedHopfPayloadFamily` constructs a canonical witness (the constant-id lift `ofFlatGraph (repG g)`) for every generator, depending only on `propext`/`Classical.choice`/`Quot.sound`.

We do not install a second `HopfAlgebra` instance on `HopfH` (it would clash with the existing flat instance on the same carrier); instead we prove an explicit Hopf-structure *certificate* for the boundary-resolved payload coproduct. The certificate `resolvedHopfStructureCertificate_holds` includes coassociativity, both counit laws, and both antipode axioms, and `exists_resolvedHopfStructureCertificate` exhibits an explicit canonical payload family satisfying them — each transferred for free from the flat coproduct via the linear-map equality. The reply to any vacuity concern is then one line: *the resolved payload family is inhabited, and the inhabited resolved coproduct satisfies the Hopf laws.*
