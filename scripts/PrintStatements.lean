import LeanestEllipse

/-!
# Definitions and elaborated statement types for comparison with the paper

Run `lake env lean scripts/PrintStatements.lean`. The output records the core
mathematical definitions and every paper alias with its implicit parameters exposed.
-/

set_option format.width 110
set_option pp.proofs false

-- Lemmas 6 and 7 use finite regular complex Borel measures. On the compact
-- metric subtypes used here, regularity of their variation is automatic.
example (X : Set (ℂ × ℂ)) [CompactSpace X] (η : MeasureTheory.ComplexMeasure X) :
    MeasureTheory.Measure.Regular η.variation := inferInstance

#print CompactlyContained
#print MeasureTheory.essSupport
#print radonTransform
#print radonBackprojection
#check @Complex.radonTransformL1
#check @fourier_radonTransform
#check @fourierInv_slice_eq_radonTransform
#check @Continuous.radonTransform
#check @fourierInv_slice_eq_radonTransform_of_contDiff
#check @VectorFourier.neg_laplacian_inverseFourierIntegral
#check @VectorFourier.iterate_neg_laplacian_inverseFourierIntegral
#check @MeasureTheory.Measure.integral_signedRadial
#check @radon_inversion_odd
#print RadonTransform.momentTensor
#print Ellipsoid
#print Ellipsoid.toSet
#print Ellipsoid.shape
#print supportFunction
#print lowerSupportFunction
#print LeanestEllipse.LineMeets
#print LeanestEllipse.RadonVanishesOn
#print LeanestEllipse.RadonVanishesAEOn
#print LeanestEllipse.SmoothNullExists
#print LeanestEllipse.IntegrableNullExists
#print LeanestEllipse.EllipseSandwich
#print LeanestEllipse.planarFeasibilityQuadratic
#print LeanestEllipse.realSmoothNullspace
#print LeanestEllipse.unorientedLineCoords
#print LeanestEllipse.InBand
#print LeanestEllipse.bandSet
#print LeanestEllipse.mobiusBundle
#check @LeanestEllipse.range_unorientedLineCoordsHalf
#check @LeanestEllipse.unorientedLineCoordsMeasurableEquiv
#print LeanestEllipse.mobiusSignSetoid
#check @LeanestEllipse.mobiusLineBundleHomeomorph
#check @LeanestEllipse.mobiusLineBundleHomeomorph_base
#check @LeanestEllipse.mobiusBundle_fiber_eq_realLine
#check @LeanestEllipse.mobiusLineBundle_angle_gluing
#print LeanestEllipse.polygonalChain
#check @LeanestEllipse.square_corners_subset_sphere
#check @LeanestEllipse.unitSphere_inter_frontier_openSquare_eq_sideMidpoints
#check @LeanestEllipse.unitDisk_inter_frontier_openSquare_eq_sideMidpoints
#print LeanestEllipse.openSquare
#print LeanestEllipse.closedSquare
#print LeanestEllipse.BomanClosedSupportConjecture
#print LeanestEllipse.BomanSymmetricInteriorAssertion
#print Matrix.ellipseDisk

#check @LeanestEllipse.Paper.theorem_1
#check @LeanestEllipse.Paper.theorem_1_containment
#check @LeanestEllipse.Paper.theorem_1_witness
#check @LeanestEllipse.Paper.remark_2
#check @LeanestEllipse.Paper.remark_2_circle
#check @LeanestEllipse.Paper.remark_2_polygonalChain
#check @LeanestEllipse.Paper.remark_2_convex_polygon
#check @LeanestEllipse.Paper.remark_3
#check @LeanestEllipse.Paper.remark_3_all_dimensions
#check @LeanestEllipse.Paper.lemma_4
#check @LeanestEllipse.Paper.proposition_5
#check @LeanestEllipse.Paper.proposition_5_independent_family
#check @LeanestEllipse.Paper.after_proposition_5
#check @LeanestEllipse.Paper.lemma_6
#check @LeanestEllipse.Paper.section_2_mobius_bundle
#check @LeanestEllipse.Paper.lemma_7
#check @LeanestEllipse.Paper.lemma_8
#check @LeanestEllipse.Paper.lemma_8_projection
#check @LeanestEllipse.Paper.lemma_9
#check @LeanestEllipse.Paper.lemma_9_disk
#check @LeanestEllipse.Paper.lemma_9_nondegenerate
#check @LeanestEllipse.Paper.lemma_9_ellipse
#check @LeanestEllipse.Paper.theorem_10
#check @LeanestEllipse.Paper.proposition_11
#check @LeanestEllipse.Paper.corollary_12
#check @LeanestEllipse.Paper.corollary_12_integrable
#check @LeanestEllipse.Paper.corollary_13
#check @LeanestEllipse.Paper.remark_14
#check @LeanestEllipse.Paper.remark_14_center_shape
#check @LeanestEllipse.Paper.remark_14_smooth_endpoint
#check @LeanestEllipse.Paper.remark_14_integrable_endpoint
#check @LeanestEllipse.Paper.remark_14_boundary
#check @LeanestEllipse.Paper.figure_2_corners
#check @LeanestEllipse.Paper.figure_2_contacts
#check @LeanestEllipse.Paper.remark_15_conjecture
#check @LeanestEllipse.Paper.remark_15_theorem
#check @LeanestEllipse.Paper.remark_15_limit
#check @LeanestEllipse.Paper.section_6_point
#check @LeanestEllipse.Paper.section_6_backprojection
#check @LeanestEllipse.Paper.section_6_local_inversion
#check @LeanestEllipse.Paper.introduction_joint_integrability
#check @LeanestEllipse.Paper.introduction_representative_independence
#check @LeanestEllipse.Paper.introduction_L1_bound
#check @LeanestEllipse.Paper.introduction_integral_bound
#check @LeanestEllipse.Paper.section_7_moments
#check @LeanestEllipse.Paper.section_7_moments_essentialSupport
#check @LeanestEllipse.Paper.section_7_inversion
#check @LeanestEllipse.Paper.section_7_local_uniqueness
