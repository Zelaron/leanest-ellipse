# The ellipse criterion

Lean 4 formalization of Christian Hägg's *An Ellipse Criterion for Exact
Nonuniqueness in the Planar Interior Radon Problem*,
[arXiv:2608.29442](https://arxiv.org/abs/2608.29442). Statement numbers follow the
latest revision of the article.
The project uses Lean and Mathlib **v4.34.1**. All project modules belong to the
single `LeanestEllipse` library, including the supporting analysis, geometry,
operator theory, and Radon-transform modules.

The numbered-statement index covers all 15 numbered results, alongside the
principal intermediate results. The active development also proves the
unnumbered odd-dimensional Radon inversion formula and its local uniqueness
consequence, with all analytic hypotheses derived from smooth compact support.
Coverage of the article's mathematical prose and verification of the expanded
source are recorded separately below. The closed-support endpoint question in
Remark 14 remains open, as in the paper.

## Source layout

The repository root contains the Lake project:

```text
leanest-ellipse/
├── .gitignore
├── README.md
├── LICENSE
├── lakefile.toml
├── lake-manifest.json
├── lean-toolchain
├── LeanestEllipse.lean
├── scripts/
└── LeanestEllipse/
    ├── Analysis/
    ├── EllipseCriterion/
    ├── IntegralGeometry/
    ├── LinearAlgebra/
    ├── MeasureTheory/
    ├── Topology/
    └── PaperStatements.lean
```

`EllipseCriterion/` contains the paper-specific arguments. The other subject
directories contain the supporting mathematics, organized by topic. Every module
can be imported individually, for example
`import LeanestEllipse.Analysis.Convex.Ellipsoid`. These module paths do not
change the declarations' mathematical namespaces, such as `Ellipsoid` or `Matrix`.
The build configuration, toolchain, and documentation live at the project root.

## Build and audit

Install [Lean via elan](https://lean-lang.org/install/) and Git. From the
repository root (the directory containing this README), run:

```sh
lake exe cache get
bash scripts/check.sh
```

`lean-toolchain` selects Lean v4.34.1, and `lake-manifest.json` pins Mathlib and
its dependencies to exact commits. Lake downloads those dependencies; `cache get`
fetches their precompiled artifacts. No dependencies or build caches are bundled.

The check script uses two Lean threads by default, builds with warnings treated
as failures, prints axioms and elaborated types for the paper statements, and audits the transitive
axiom dependencies of every declaration in the imported `LeanestEllipse` modules,
including all supporting mathematics. It first checks that every project `.lean`
source is imported by the root module, rejecting omissions from the audit.
Only `propext`, `Classical.choice`, and
`Quot.sound` are accepted;
`sorryAx` and additional axioms cause failure. Reports are generated under
`.lake/`, which is ignored by Git. A successful audit ends with a `PASS` line.

**Verified (2026-10-17):** this repository passed the complete `scripts/check.sh`
run: the warnings-as-errors build, the transitive axiom audit (1,481 module
declaration entries, representing 1,479 distinct names), kernel replay of all 63
project modules, and replay of the root module with all imports into a fresh kernel
environment.

The script also runs the official `leanchecker` on every project module and then
replays the root module, including its imported declarations, into a fresh kernel
environment.

For a build without the axiom reports, run `lake build`.

The [root module](LeanestEllipse.lean) imports the complete formalization.
[PaperStatements.lean](LeanestEllipse/PaperStatements.lean) provides numbered
aliases under `LeanestEllipse.Paper`, preserving the original theorem types.
Its imports include all supporting modules and all paper-specific modules.

## Mathematical conventions

- The main criterion is stated in any real inner product space of dimension two.
  Coordinate arguments identify that plane with `ℂ`, with its **real** inner product.
- `Ellipsoid E` is the closed nondegenerate disk `c + A(closedBall 0 1)` for a
  continuous linear equivalence `A`. Its shape is `A A*`, so this describes exactly
  the paper's positive-definite-matrix ellipses. `Matrix.ellipseDisk` additionally
  handles the degenerate disks of Lemma 9.
- `radonTransform` integrates against the Euclidean volume measure on the
  orthogonal hyperplane. Unit-sphere surface measure times Lebesgue offset measure
  is used for “almost every line”; in the plane this is arc length times `dp`.
- Fourier transforms use Mathlib's exponential `exp(-2π i ⟪ξ,x⟫)`. For dimension
  `n = 2k + 1`, integration over the full oriented unit sphere gives the inversion
  constant `κₙ = (2 * (2π)^(n - 1))⁻¹`. The factor two accounts for the two
  orientations of each hyperplane.
- Smooth functions use the closed support `tsupport`; integrable functions use
  `essSupport`. Nonzero integrable functions and equality to zero are interpreted
  almost everywhere. `A ⋐ B` means that `closure A` is compact and contained in `B`.
- Mathlib's complex inner product is linear in the **second** variable. The operator
  calculations translate the paper's first-variable convention accordingly.
- The criterion allows empty and unbounded open convex sets. Convexity of the outer
  set is required for necessity, but not for the sufficiency construction.

## Numbered statements

Unqualified declarations in the table have namespace `LeanestEllipse`.
All module links refer to sources in the `LeanestEllipse/` directory.

| Paper | Lean declaration(s) | Module |
|---|---|---|
| Theorem 1: three equivalent conditions | `ellipse_criterion` | [MainTheorem](LeanestEllipse/EllipseCriterion/MainTheorem.lean) |
| Theorem 1: compact containment and real symmetric negative witness | `ellipse_criterion_compactlyContained`, `ellipse_criterion_witness` | [MainTheorem](LeanestEllipse/EllipseCriterion/MainTheorem.lean) |
| Remark 2: connected, non-collinear inner sets | `ellipse_criterion_of_isConnected` | [MainTheorem](LeanestEllipse/EllipseCriterion/MainTheorem.lean) |
| Remark 2: circle data sets | `ellipse_criterion_sphere` | [ConnectedExamples](LeanestEllipse/EllipseCriterion/ConnectedExamples.lean) |
| Remark 2: polygonal boundaries, including nonconvex polygons | `ellipse_criterion_polygonalChain`, `ellipse_criterion_polygon_boundary` | [PolygonalExamples](LeanestEllipse/EllipseCriterion/PolygonalExamples.lean) |
| Remark 3: five-variable feasibility | `ellipseSandwich_iff_five_variable_feasibility`, `ellipseSandwich_iff_quadratic_feasibility` | [Feasibility](LeanestEllipse/EllipseCriterion/Feasibility.lean) |
| Lemma 4: concentric disks, including strict negativity on a neighborhood | `exists_radial_radonTransform_eq_zero` (root namespace) | [ConcentricDisks](LeanestEllipse/IntegralGeometry/Radon/ConcentricDisks.lean) |
| Proposition 5: affine sufficiency and an infinite independent family | `sufficiency`, `sufficiency_linearIndependent` | [Sufficiency](LeanestEllipse/EllipseCriterion/Sufficiency.lean) |
| Lemma 6: unoriented-line transfer | `unoriented_line_transfer` | [UnorientedTransfer](LeanestEllipse/EllipseCriterion/UnorientedTransfer.lean) |
| Lemma 7: Hardy-model reduction | `hardy_model_reduction` | [HardyModel](LeanestEllipse/EllipseCriterion/HardyModel.lean) |
| Lemma 8: common neutral subspace | `exists_common_neutral_subspace`, `exists_common_neutral_subspace_orthogonalProjection` (root namespace) | [NeutralSubspace](LeanestEllipse/Analysis/InnerProductSpace/NeutralSubspace.lean) |
| Lemma 9: matrix center, shape and nondegeneracy | `Matrix.exists_center_shape_fin_two`, `Matrix.posDef_ellipseShape_of_nontrivial` | [HermitianFinTwo](LeanestEllipse/LinearAlgebra/Matrix/HermitianFinTwo.lean) |
| Lemma 9: the possibly degenerate disk, its projection endpoints, and nondegeneracy as a set | `Matrix.ellipseDisk`, `Matrix.spectrum_realPart_eq_endpoints_ellipseDisk`, `Matrix.exists_ellipsoid_eq_ellipseDisk` | [MatrixSpectrum](LeanestEllipse/Analysis/Convex/Ellipsoid/MatrixSpectrum.lean) |
| Theorem 10: spectral gap | `exists_matrix_of_spectrum_gap` (root namespace) | [SpectralGap](LeanestEllipse/Analysis/InnerProductSpace/SpectralGap.lean) |
| Proposition 11: necessary ellipse | `exists_ellipsoid_of_radonVanishesAEOn` | [Necessity](LeanestEllipse/EllipseCriterion/Necessity.lean) |
| Corollary 12: sharp threshold for open squares | `smoothNullExists_openSquare_iff`, `integrableNullExists_openSquare_iff` | [SquareCorollaries](LeanestEllipse/EllipseCriterion/SquareCorollaries.lean) |
| Corollary 13: uniqueness with closed-square support | `ae_eq_zero_of_radonVanishesAEOn_closedSquare` | [SquareCorollaries](LeanestEllipse/EllipseCriterion/SquareCorollaries.lean) |
| Remark 14: unique endpoint ellipse, center and shape | `eq_closedBall_of_closedSquare_subset_of_subset_closedSquare`, `center_eq_zero_and_shape_eq_id_of_closedSquare_subset_of_subset_closedSquare` | [SquareGeometry](LeanestEllipse/EllipseCriterion/SquareGeometry.lean) |
| Remark 14: the disk meets the outer boundary; open-square compact-support nonexistence | `unitDisk_not_subset_openSquare`, `not_smoothNullExists_openSquare_endpoint`, `not_integrableNullExists_openSquare_endpoint` | [SquareCorollaries](LeanestEllipse/EllipseCriterion/SquareCorollaries.lean) |
| Remark 15: the two universal claims are false | `not_bomanClosedSupportConjecture`, `not_bomanSymmetricInteriorAssertion` | [EarlierClaims](LeanestEllipse/EllipseCriterion/EarlierClaims.lean) |
| Remark 15: tending to zero does not imply eventual equality to zero | `exists_positive_tendsto_zero_not_eventually_zero` | [EarlierClaims](LeanestEllipse/EllipseCriterion/EarlierClaims.lean) |

The propositions negated in Remark 15 are stated explicitly in
`BomanClosedSupportConjecture` and `BomanSymmetricInteriorAssertion`, following
their planar descriptions in the paper. The latter includes nonempty bounded
open convex domains, compact nesting and a common center of symmetry. Both
counterexamples use half-side ratio `3/4`; `closedSquare_counterexample` works for
every ratio strictly between `1/√2` and `1`.

## Other conclusions and intermediate results

| Paper content | Lean declaration(s) / module |
|---|---|
| Introduction: joint L¹ class, independence of representative, and the `2π` norm estimate | `Complex.integrable_radonTransform_sphere`, `Complex.radonTransform_sphere_ae_eq_of_ae_eq`, `Complex.radonTransformL1`, `Complex.norm_radonTransformL1_surface_le` in [L1](LeanestEllipse/IntegralGeometry/Radon/L1.lean) |
| Sentence after Proposition 5: the real smooth nullspace is zero or infinite dimensional | `realSmoothNullspace`, `realSmoothNullspace_eq_bot_or_infinite`, `realSmoothNullspace_infinite_iff` in [SmoothNullspace](LeanestEllipse/EllipseCriterion/SmoothNullspace.lean) |
| Section 7: nonzero odd smooth witnesses for a point data set | `exists_smooth_odd_radonTransform_eq_zero_through_point` in [FurtherQuestions](LeanestEllipse/EllipseCriterion/FurtherQuestions.lean), in every nontrivial finite dimension |
| Section 7: odd-dimensional inversion and smooth backprojection | `radon_inversion_odd`, `radonBackprojection_radonTransform_eq_inverseFourierIntegral`, `contDiff_radonBackprojection_radonTransform` in [Inversion](LeanestEllipse/IntegralGeometry/Radon/Inversion.lean) |
| Section 7: vanishing of backprojection and unconditional odd-dimensional local uniqueness | `RadonVanishesOn.backprojection_eqOn_zero`, `eqOn_zero_of_radonVanishesOn_of_odd_finrank` in [FurtherQuestions](LeanestEllipse/EllipseCriterion/FurtherQuestions.lean) |
| Projection endpoints, inclusion criteria and ellipse shape | [SupportFunction](LeanestEllipse/Analysis/Convex/SupportFunction.lean), [Ellipsoid](LeanestEllipse/Analysis/Convex/Ellipsoid.lean), [QuadraticFeasibility](LeanestEllipse/Analysis/Convex/QuadraticFeasibility.lean) |
| Affineness of the five-variable constraints and convexity of the feasible set | `isLinearMap_feasibilityQuadratic_sub_sq`, `convex_setOf_quadratic_feasibility` in [QuadraticFeasibility](LeanestEllipse/Analysis/Convex/QuadraticFeasibility.lean) |
| Abel inversion, smoothness, support and negativity of the radial construction | [Abel](LeanestEllipse/IntegralGeometry/Radon/Abel.lean), [Radial](LeanestEllipse/IntegralGeometry/Radon/Radial.lean), [ConcentricDisks](LeanestEllipse/IntegralGeometry/Radon/ConcentricDisks.lean) |
| Affine covariance of the planar Radon transform | `radonTransform_comp_affine` in [Affine](LeanestEllipse/IntegralGeometry/Radon/Affine.lean) |
| Fourier slice identity, moments and Radon injectivity | [Basic](LeanestEllipse/IntegralGeometry/Radon/Basic.lean), [Injective](LeanestEllipse/IntegralGeometry/Radon/Injective.lean), [PlaneInjective](LeanestEllipse/IntegralGeometry/Radon/PlaneInjective.lean), [Moments](LeanestEllipse/EllipseCriterion/Moments.lean) |
| Continuous compactly supported Radon profiles and pointwise fiber integrability | `Continuous.integrable_radonTransform_fiber`, `Continuous.radonTransform`, `radonTransform_add_of_continuous` in [Continuous](LeanestEllipse/IntegralGeometry/Radon/Continuous.lean) |
| Fourier slices in Mathlib's `2π` normalization and one-dimensional reconstruction | `fourier_radonTransform`, `fourierInv_slice_eq_radonTransform`, `fourierInv_slice_eq_radonTransform_of_contDiff`, `SchwartzMap.integrable_fourier_slice` in [FourierSlice](LeanestEllipse/IntegralGeometry/Radon/FourierSlice.lean); smooth compact support discharges the inverse-slice hypotheses |
| Signed polar coordinates, temperate growth, and the weighted integral formula | `Measure.signedRadial`, `Measure.signedRadial_hasTemperateGrowth`, `Measure.integral_positiveRadial`, `Measure.integral_negativeRadial`, `Measure.integral_signedRadial` in [SignedRadial](LeanestEllipse/MeasureTheory/Constructions/SignedRadial.lean), under `MeasureTheory` |
| Differentiating inverse Fourier integrals and iterating the negative Laplacian | `VectorFourier.inverseFourierIntegral`, `VectorFourier.contDiff_inverseFourierIntegral`, `VectorFourier.neg_laplacian_inverseFourierIntegral`, `VectorFourier.iterate_neg_laplacian_inverseFourierIntegral` in [Fourier Laplacian](LeanestEllipse/Analysis/Fourier/Laplacian.lean) |
| Section 7: symmetric continuous moment tensors, homogeneous diagonal polynomials, and the Radon moment identity in arbitrary finite dimension | `RadonTransform.momentTensor`, `RadonTransform.momentTensor_apply_perm`, `RadonTransform.momentTensor_diagonal_smul`, `RadonTransform.integral_pow_smul_radonTransform_eq_momentTensor` in [Radon moments](LeanestEllipse/IntegralGeometry/Radon/Moments.lean) |
| Passage to the nonzero annihilating measure | `exists_bandMeasure_of_radonVanishesAEOn` in [NecessaryMeasure](LeanestEllipse/EllipseCriterion/NecessaryMeasure.lean) |
| Half-period coordinates cover the Möbius bundle and give a measurable equivalence | `range_unorientedLineCoordsHalf`, `unorientedLineCoordsMeasurableEquiv` in [UnorientedParametrization](LeanestEllipse/EllipseCriterion/UnorientedParametrization.lean) |
| The Möbius quotient topology, base projection, real fibers and sign gluing | `mobiusLineBundleHomeomorph`, `mobiusLineBundleHomeomorph_base`, `mobiusBundle_fiber_eq_realLine`, `mobiusLineBundle_angle_gluing` in [MobiusTopology](LeanestEllipse/EllipseCriterion/MobiusTopology.lean) |
| Representing probability measure and Haar marginal | [UniformAlgebra](LeanestEllipse/Topology/ContinuousMap/UniformAlgebra.lean) |
| Pure isometry, wandering subspace and the Hardy symbol | [Wold](LeanestEllipse/Analysis/InnerProductSpace/Wold.lean), `IsMobiusPair`, `isPureIsometry_hardyShift`, `isHilbertSum_hardy` in [HardyModel](LeanestEllipse/EllipseCriterion/HardyModel.lean) |
| Approximate eigenvalues and retention of fiber support | [ApproxEigenvalue](LeanestEllipse/Analysis/InnerProductSpace/ApproxEigenvalue.lean), `exists_eq_of_mem_spectrum_mobiusSymbol` in `HardyModel` |
| Riesz idempotents, neutral spaces and Schur complements | [RieszIdempotent](LeanestEllipse/Analysis/Normed/Algebra/RieszIdempotent.lean), [NeutralSubspace](LeanestEllipse/Analysis/InnerProductSpace/NeutralSubspace.lean), [SchurComplement](LeanestEllipse/Analysis/InnerProductSpace/SchurComplement.lean) |
| Coordinate/diagonal trace inequalities for the squares | `trace_shape_lt_two`, `trace_shape_le_two`, `four_mul_sq_le_trace_shape` in `SquareGeometry` |
| Figure 2: corner incidences and the exact four outer contact points | `square_corners_subset_sphere`, `unitDisk_inter_frontier_openSquare_eq_sideMidpoints` in [SquareIncidences](LeanestEllipse/EllipseCriterion/SquareIncidences.lean) |

## Generality and scope

Supporting results live in the subject directories under `LeanestEllipse/`, in
mathematical namespaces, with separate imports. The spectral-gap and
neutral-subspace theorems allow infinite-dimensional
complex Hilbert spaces and arbitrary endpoint functions. Approximate eigenvalues
are treated for general normal operators on real or complex Hilbert spaces;
representing probability measures are proved for general uniform algebras.
Ellipsoid feasibility, essential support, backprojection and the basic hyperplane
Radon API work beyond the plane. Triangular evaluations give linear independence
over any division ring. The joint planar L¹ operator allows any finite direction
measure and vector-valued inputs. Moment tensors work on separable real inner
product spaces with any measure; their Radon identities specialize to arbitrary
finite dimension and allow essential compact support.

Polygonal chains are connected in arbitrary real normed spaces. Separate convex
geometry results identify a compact convex set with the convex hull of its
frontier and prove connectedness and non-collinearity of convex-body frontiers
in dimension greater than one. The Möbius identification uses a proper quotient
map on the full unbounded real fiber and preserves the projection to the base
circle.

Signed polar coordinates allow any finite angular measure; the resulting measure
has temperate growth. For Euclidean surface measure, the norm-weighted signed
radial integral is twice the volume integral. Inverse Fourier integrals allow an
arbitrary frequency measure and complex normed target. Moments through order two
suffice for the negative-Laplacian identity; the iterated identity assumes all
norm moments. Odd-dimensional Radon inversion and smoothness of backprojection
hold for complex Banach-valued smooth compactly supported functions. Backprojection
is smooth in every finite dimension; the inversion theorem applies when the real
inner product space has odd dimension, including dimension one. The local
uniqueness consequence requires an open data set and pointwise
vanishing on every hyperplane meeting it.

Some supporting developments intentionally have a narrower scope than the full
literature: Riesz integrals use circular contours; the Wold development supplies
the pure-isometry model rather than all variants of the decomposition theorem;
the Schur complement results use a scalar diagonal block; Abel inversion and the
disk witnesses here are planar. These restrictions are documented, and do not
add hypotheses to the numbered paper results. The module links above lead to the
source documentation for these developments.

## Article coverage and open questions

The [article coverage inventory](scripts/article-coverage.tsv) matches the revised
article's mathematical prose, proof calculations and figure assertions to named
Lean declarations or explicitly identified subproofs. Its 165 entries include
144 proved assertions, with definitions, open questions and historical attributions
recorded separately. The manual comparison records no outstanding mathematical
proof gap. It groups related assertions and includes routine consequences of
stronger formal results; it is not a one-to-one translation of English sentences.
The article follows the formal proofs where simpler arguments suffice, including
the Abel calculation, the Hardy model and the Schur-complement argument.

The inventory documents a human check of hypotheses, quantifiers, conclusions and
proof steps against the Lean statements and proof bodies. The compiler, transitive
axiom audit and kernel replays check the formal development; they do not parse the
article or certify that its English matches the formal specifications.

- The closed-support endpoint existence question in Remark 14 and the open
  questions about disconnected data and higher-dimensional X-ray geometry remain
  open. The X-ray question concerns affine lines and a solid ellipsoid between
  bounded open convex sets; it is distinct from the proved odd-dimensional
  hyperplane-Radon local uniqueness statement.
- Historical attribution and the chronology of choices in the cited variational
  proof. The mathematical failure of the proposed inference is represented by an
  explicit positive sequence tending to zero, not by unprovided definitions of
  that paper's minima.
- Mathematical assertions in figure captions are included in the inventory.
  Bibliographic metadata, acknowledgments and drawings themselves are not
  mathematical propositions. Classical tools already in Mathlib are reused
  with their actual hypotheses; the concentric-disk construction, transfer,
  Hardy reduction and operator argument are proved in this project.

## Repository contents

The repository contains the `LeanestEllipse` library, pinned Lake configuration,
license, this README and the checking/coverage scripts. The article itself is on
[arXiv](https://arxiv.org/abs/2608.29442). Dependencies, build caches and
verification reports are not included; the commands above regenerate them under
`.lake/`.
