import MagHK.GaussianOutside
import MagHK.WeakGauge

/-! Both noninteracting theorem items, including the stated function spaces
and the obstruction to almost-everywhere weak gauges, for the same potentials. -/
noncomputable section
namespace MagHK.NoninteractingTheorem
open MeasureTheory
open MagHK.ConstructionData MagHK.PotentialSpaces MagHK.CounterexamplePair
open scoped ContDiff

structure BoundedResult (t : ℝ) : Prop where
  positive_parameter : 0 < t
  vector_smooth : ContDiff ℝ ∞ (bounded3Vector t)
  opposite_smooth : ContDiff ℝ ∞ (-bounded3Vector t)
  scalar_smooth : ContDiff ℝ ∞ (bounded3Scalar t 5)
  scalar_bounded : MemLp (bounded3Scalar t 5) ⊤
  vector_bounded : MemLp (bounded3Vector t) ⊤
  opposite_bounded : MemLp (-bounded3Vector t) ⊤
  scalar_space : ScalarSumSpace (bounded3Scalar t 5)
  vector_space : VectorSumSpace (bounded3Vector t)
  opposite_space : VectorSumSpace (-bounded3Vector t)
  field_nonzero : MagHK.Cartesian.planarCurl (MagHK.Cartesian.boundedVector t) ≠ 0
  pair : PairedGroundStates (MagHK.Cartesian.boundedVector t) (MagHK.Cartesian.boundedScalar t)
    (MagHK.Axial.potential 5) 20 (fun p => MagHK.ConcreteSlater.wave t 5 p.1 p.2)
  not_weak_gauge : ¬ MagHK.WeakGauge.SpatialGaugeEquivalent
    (MagHK.Cartesian.boundedVector t) (-MagHK.Cartesian.boundedVector t)

theorem bounded_counterexample
    (planar : MagHK.PlanarSpectralLibrary.StandardPlanarLibrary)
    (axial : MagHK.AxialRealization.StandardAxialLibrary)
    (tensor : MagHK.TensorRealization.StandardTensorLibrary)
    (fermion : MagHK.FermionRealization.StandardFermionLibrary)
    (reversal : MagHK.OperatorTimeReversal.StandardAntiunitaryLibrary)
    (regularity : MagHK.WeakGauge.StandardGradientRegularityLibrary) :
    ∃ t : ℝ, BoundedResult t := by
  obtain ⟨t, ht, hA, hminus, hV, _, _, hpair⟩ :=
    MagHK.CounterexamplePair.bounded_counterexample planar axial tensor fermion reversal
  obtain ⟨hVs, hAs⟩ := bounded_sum_spaces t 5 ht
  have hAb := bounded_vector_memLp t ht.le
  exact ⟨t, ⟨ht, hA, hminus, hV, bounded_scalar_memLp t 5 ht, hAb, hAb.neg,
    hVs, hAs, ⟨0, -bounded3Vector t, MemLp.zero, hAb.neg, fun x => by simp⟩,
    MagHK.Cartesian.bounded_curl_nonzero t ht, hpair,
    MagHK.WeakGauge.bounded_opposite_not_weak_gauge regularity t ht⟩⟩

structure GaussianResult (t c : ℝ) : Prop where
  positive_parameter : 0 < t
  vector_smooth : ContDiff ℝ ∞ (gaussian3Vector t)
  opposite_smooth : ContDiff ℝ ∞ (-gaussian3Vector t)
  scalar_smooth : ContDiff ℝ ∞ (gaussian3Scalar t c)
  vector_bounded : MemLp (gaussian3Vector t) ⊤
  opposite_bounded : MemLp (-gaussian3Vector t) ⊤
  scalar_outside : ¬ ScalarSumSpace (gaussian3Scalar t c)
  field_nonzero : MagHK.Cartesian.planarCurl (MagHK.Cartesian.gaussianVector t) ≠ 0
  pair : MagHK.GaussianCompactness.CompactPairedGroundStates
    (MagHK.Cartesian.gaussianVector t) (MagHK.Cartesian.gaussianScalar t)
    (MagHK.GaussianAxial.potential c) 2 (fun p => MagHK.GaussianSlater.wave t c p.1 p.2)
  density_formula : ∀ x,
    density (fun p => MagHK.GaussianSlater.wave t c p.1 p.2) x =
      (2 / Real.pi) * Real.sqrt (c / Real.pi) * Real.exp (-‖x.1‖ ^ 2 - c * x.2 ^ 2)
  not_weak_gauge : ¬ MagHK.WeakGauge.SpatialGaugeEquivalent
    (MagHK.Cartesian.gaussianVector t) (-MagHK.Cartesian.gaussianVector t)

theorem gaussian_counterexample
    (planar : MagHK.PlanarSpectralLibrary.StandardPlanarLibrary)
    (axial : MagHK.GaussianAxial.StandardOscillatorLibrary)
    (tensor : MagHK.TensorRealization.StandardTensorLibrary)
    (fermion : MagHK.FermionRealization.StandardFermionLibrary)
    (reversal : MagHK.OperatorTimeReversal.StandardAntiunitaryLibrary)
    (compactness : MagHK.GaussianCompactness.StandardConfiningLibrary)
    (regularity : MagHK.WeakGauge.StandardGradientRegularityLibrary)
    (c : ℝ) (hc : 1 < c) : ∃ t : ℝ, GaussianResult t c := by
  obtain ⟨t, ht, hA, hminus, hV, _, hpair, hρ⟩ :=
    MagHK.GaussianCompactness.gaussian_compact_counterexample planar axial tensor fermion
      reversal compactness c hc
  have hAb := gaussian_vector_memLp t ht.le
  exact ⟨t, ⟨ht, hA, hminus, hV, hAb, hAb.neg,
    MagHK.GaussianOutside.gaussian_scalar_outside t c ht.le hc,
    MagHK.Cartesian.gaussian_curl_nonzero t ht, hpair, hρ,
    MagHK.WeakGauge.gaussian_opposite_not_weak_gauge regularity t ht⟩⟩

end MagHK.NoninteractingTheorem
