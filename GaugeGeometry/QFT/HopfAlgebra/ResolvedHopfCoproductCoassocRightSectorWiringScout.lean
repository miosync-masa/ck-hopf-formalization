import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRightImageCorrespondenceScout

/-!
# R-6c-body-224 — right sector wiring scout: the sector inverse is a red herring; `right_sound` / `right_complete` are the floor

Two-hundred-and-twenty-fourth genuine-body step, a scout of whether body-219's `right_sound` / `right_complete` can
be discharged by wiring the abstract region `componentToRight` to the already-proved sector inverse (`rightEquiv` /
`right_surj` / `right_left_inv` / `right_right_inv`).  The audit's verdict: **the sector inverse is the wrong tool** —
three mismatches make it intractable, and `right_sound` / `right_complete` are the honest minimal floor for the
abstract region construction.  This records the negative finding so the sector-inverse direction is not pursued.

## The three mismatches (why the sector inverse does not apply)

* **map disconnect** — body-156's region `componentToRight` is an *abstract field* with only `rightComponentCD` /
  `rightComponentDisjoint` (no soundness / coherence), and `ResolvedRegionConstructionFromSectorSupply` is **never
  instantiated** — so `right_surj` / `componentToRight_spec` cannot even be *named* in a proof about
  `Construction.componentToRight`;
* **outer disconnect** — the sector index `RightPrimitiveIndex D G (fwdMap q)` gives a parent in `(fwdMap q).1.1 =
  (selectedOuterOf q).1` (the *recovered / left-factor* outer), a different `Finset` from `q.1.1` (the *original
  domain* outer); there is no `(selectedOuterOf q).1 = q.1.1`;
* **tag disconnect** — the sector `inl false` witness (`RightPrimitiveIndex.hR = isRight` over `fwdMap q`) is about
  `fwdMap q`'s own `recoverChoice`-derived structure, not `q.2`; `rightPrimSelected q γ` is about `q.2`.

So the sector `inl false` and `q.2`'s `inl false` live over *different outers*; the sector inverse is a red herring.

## The correct (but larger) discharge path — the region `recoverChoice` layer

The genuine bridge between `rightPrimSelected q γ` (`q.2 = inl false`) and the forward image is the **region
`recoverChoice ↔ q.2` machinery** already scaffolded: `ResolvedBackwardChoiceHEqAssemblySupply.outer_partition` /
`choice_component_eq` / `backward_choice_heq` (bodies 192/193), composed with the region tag `right_tag`
(body-152) and a `rightRecovered_eq` glue.  But that reduces `right_sound` / `right_complete` to
`rightPrimSelected q γ ↔ γ ∈ Union.rightRecovered (fwdMap q)` **and still needs `Construction.componentToRight`
concrete** — otherwise there is nothing to prove `∈ Construction.rightRecovered` about.  So discharging (not just
fielding) `right_sound` / `right_complete` requires **concretizing the whole region construction** (a real
`componentToRight` equal to the `recoverChoice`-selected component) — a substantially larger lift entirely inside the
region layer.

## Assessment and plan

* **`right_sound` / `right_complete` are the honest minimal floor** for the abstract region construction: they are
  precisely the two obligations a concrete instantiation would discharge; the sector inverse buys nothing.
* **Do not attempt the sector-inverse wiring** — intractable and misdirected (would re-derive the region
  `recoverChoice` bridge plus an extra parent-index transport).
* **Pivot for near-term progress** to the residuals that do not depend on concretizing the region map: the **forward
  compatibility** (`forestTag` / `recoverChoice_forest_eq` / `promote_collapse`, `forestComponentMem`,
  `represented_cases`), the **pairwise disjointnesses / carrier closure** (bodies 158/159), or the **non-region base**.

The same verdict applies to the other seven sector `sound` / `complete` directions (forest / survivor / remnant):
they are all abstract-region-construction floor obligations, dischargeable only by concretizing the region maps.

Per the HALT: no leaf is proved; the sector inverse / region concretization is not entered; the negative finding and
the pivot are recorded.

This is a documentation / scout anchor (like body-210 / body-218).  The import keeps the map honest against the
source.  No declarations beyond this docstring.  No facade, no flat term, no `forgetHopf`.
-/
