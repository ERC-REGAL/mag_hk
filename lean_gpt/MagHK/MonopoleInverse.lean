import MagHK.MonopoleTimeReversal
import MagHK.MonopoleCoordinates
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-! Literal inverse spherical chart and physical Euclidean marginals. The
coordinate changes below preserve the actual measures, including the radial
Jacobian, and do not assume an identification of selected states. -/
noncomputable section
namespace MagHK.MonopoleInverse
open MeasureTheory Set Filter
open MagHK.MonopoleRealization MagHK.MonopoleTrial MagHK.SpinChart
open MagHK.MonopoleGeometry MagHK.MonopoleQuadrature MagHK.MonopoleCoordinates
open scoped ENNReal ComplexConjugate
set_option maxHeartbeats 1000000
abbrev Space := MagHK.SpinChart.Space

def inverse (z : Space) : Chart :=
  (‖z‖, ((WithLp.ofLp z).1 / ‖z‖, Complex.arg (WithLp.ofLp z).2))

theorem inverse_measurable : Measurable inverse := by
  unfold inverse
  apply measurable_norm.prodMk
  apply Measurable.prodMk
  · exact ((WithLp.prod_continuous_ofLp 2 ℝ ℂ).measurable.fst).div measurable_norm
  · exact Complex.measurable_arg.comp (WithLp.prod_continuous_ofLp 2 ℝ ℂ).measurable.snd

theorem inverse_point (x : Chart) (hr : 0 < x.1) (hmu : x.2.1 ∈ Ioo (-1 : ℝ) 1)
    (hphi : x.2.2 ∈ Ioc (-Real.pi) Real.pi) : inverse (point x) = x := by
  have hn : ‖point x‖ = x.1 := by
    rw [point_spherical]
    exact spherical_norm x.1 hr x.2 ⟨hmu.1.le, hmu.2.le⟩
  have hs : 0 < x.1 * Real.sqrt (1 - x.2.1 ^ 2) :=
    mul_pos hr (Real.sqrt_pos.mpr (meridian_root_pos (x.1, x.2.1) ⟨hr, hmu⟩))
  apply Prod.ext
  · exact hn
  · apply Prod.ext
    · change (WithLp.ofLp (point x)).1 / ‖point x‖ = x.2.1
      rw [hn, point_spherical]
      change x.1 * x.2.1 / x.1 = x.2.1
      field_simp [hr.ne']
    · change Complex.arg (WithLp.ofLp (point x)).2 = x.2.2
      rw [point_spherical]
      change Complex.arg (((x.1 * Real.sqrt (1 - x.2.1 ^ 2) : ℝ) : ℂ) * circle x.2.2) = x.2.2
      simpa only [circle, Complex.ofReal_cos, Complex.ofReal_sin] using
        Complex.arg_mul_cos_add_sin_mul_I hs hphi

theorem angle_open_ae : ∀ᵐ p ∂sphereMeasure,
    p.1 ∈ Ioo (-1 : ℝ) 1 ∧ p.2 ∈ Ioo (-Real.pi) Real.pi := by
  rw [sphereMeasure_eq_open]
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae
      (ae_restrict_mem measurableSet_Ioo),
    Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Ioo)] with p hp hq
  exact ⟨hp, hq⟩

theorem inverse_point_ae : (fun x => inverse (point x)) =ᵐ[chartMeasure] id := by
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae MagHK.MonopoleExpectation.radialVolume_ae,
    Measure.quasiMeasurePreserving_snd.ae angle_open_ae] with x hr hx
  exact inverse_point x hr hx.1 ⟨hx.2.1, hx.2.2.le⟩

theorem inverse_measurePreserving : MeasurePreserving inverse (volume : Measure Space) chartMeasure := by
  refine ⟨inverse_measurable, ?_⟩
  rw [← point_measurePreserving.map_eq, Measure.map_map inverse_measurable point_continuous.measurable]
  change Measure.map (fun x => inverse (point x)) chartMeasure = chartMeasure
  rw [Measure.map_congr inverse_point_ae, Measure.map_id]

theorem point_inverse_ae : (fun z => point (inverse z)) =ᵐ[(volume : Measure Space)] id := by
  have hc : ∀ᵐ x ∂chartMeasure, point (inverse (point x)) = point x := by
    filter_upwards [inverse_point_ae] with x hx
    rw [hx]
    rfl
  have hm : MeasurableSet {z : Space | point (inverse z) = z} :=
    measurableSet_eq_fun (point_continuous.measurable.comp inverse_measurable) measurable_id
  have h := (ae_map_iff point_continuous.measurable.aemeasurable hm).mpr hc
  rwa [point_measurePreserving.map_eq] at h

theorem integral_inverse {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (f : Chart → E) (hf : StronglyMeasurable f) :
    (∫ z : Space, f (inverse z)) = ∫ x, f x ∂chartMeasure := by
  rw [← inverse_measurePreserving.map_eq]
  exact (integral_map_of_stronglyMeasurable inverse_measurable hf).symm

def physicalWave (ψ : FermionState) (p : Space × Space) : ℂ :=
  (ψ : PairState) (inverse p.1, inverse p.2)

def physicalDensity (ψ : FermionState) (z : Space) : ℝ :=
  2 * ∫ w : Space, Complex.normSq (physicalWave ψ (z, w))

theorem physicalDensity_eq (ψ : FermionState) (z : Space) :
    physicalDensity ψ z = MagHK.MonopoleTimeReversal.density ψ (inverse z) := by
  unfold physicalDensity physicalWave MagHK.MonopoleTimeReversal.density
  congr 1
  exact integral_inverse (fun y => Complex.normSq ((ψ : PairState) (inverse z, y)))
    (Complex.continuous_normSq.comp_stronglyMeasurable
      ((Lp.stronglyMeasurable (ψ : PairState)).comp_measurable (measurable_const.prodMk measurable_id)))

theorem physicalDensity_chart (ψ : FermionState) :
    (fun x => physicalDensity ψ (point x)) =ᵐ[chartMeasure] MagHK.MonopoleTimeReversal.density ψ := by
  filter_upwards [inverse_point_ae] with x hx
  rw [physicalDensity_eq, hx]
  rfl

theorem physicalDensity_conjugate (ψ : FermionState) :
    physicalDensity (MagHK.MonopoleTimeReversal.conjugation ψ) =ᵐ[volume] physicalDensity ψ := by
  have h := inverse_measurePreserving.quasiMeasurePreserving.ae
    (MagHK.MonopoleTimeReversal.density_conjugate ψ)
  filter_upwards [h] with z hz
  simpa only [physicalDensity_eq] using hz

theorem physicalWave_normSq_integrable (ψ : FermionState) :
    Integrable (fun p => Complex.normSq (physicalWave ψ p))
      ((volume : Measure Space).prod volume) := by
  have hbase : Integrable (fun p => Complex.normSq ((ψ : PairState) p)) pairMeasure := by
    simpa only [real_inner_self_eq_norm_sq, Complex.normSq_eq_norm_sq] using
      (L2.integrable_inner (𝕜 := ℝ) (ψ : PairState) (ψ : PairState))
  exact (inverse_measurePreserving.prod inverse_measurePreserving).integrable_comp_of_integrable hbase

theorem physicalWave_mass (ψ : FermionState) :
    (∫ p : Space × Space, Complex.normSq (physicalWave ψ p)
      ∂(volume : Measure Space).prod volume) = ‖ψ‖ ^ 2 := by
  have hmp := inverse_measurePreserving.prod inverse_measurePreserving
  have hsm := Complex.continuous_normSq.comp_stronglyMeasurable (Lp.stronglyMeasurable (ψ : PairState))
  have hi := integral_map_of_stronglyMeasurable (μ := (volume : Measure Space).prod volume) hmp.measurable hsm
  rw [hmp.map_eq] at hi
  change (∫ p, Complex.normSq ((ψ : PairState) p) ∂pairMeasure) =
    ∫ p : Space × Space, Complex.normSq (physicalWave ψ p) ∂volume.prod volume at hi
  rw [← hi]
  exact pair_mass (ψ : PairState)

theorem physicalDensity_mass (ψ : FermionState) :
    (∫ z : Space, physicalDensity ψ z) = 2 * ‖ψ‖ ^ 2 := by
  unfold physicalDensity
  rw [integral_const_mul, ← integral_prod _ (physicalWave_normSq_integrable ψ), physicalWave_mass]

/-- The actual physical marginal in the orthonormal spherical frame. -/
def physicalCurrent (S : MagneticFormSystem) (ψ : S.domain) (z : Space) : Space :=
  (2 : ℝ) • ∫ w : Space, MagHK.MonopoleCurrent.pairCurrent S ψ (inverse z, inverse w)

theorem pairCurrent_stronglyMeasurable (S : MagneticFormSystem) (ψ : S.domain) :
    StronglyMeasurable (MagHK.MonopoleCurrent.pairCurrent S ψ) := by
  unfold MagHK.MonopoleCurrent.pairCurrent
  apply Finset.stronglyMeasurable_fun_sum
  intro k hk
  have hc : StronglyMeasurable (fun p => (conj ((ψ : PairState) p) * S.pi 0 k ψ p).re) :=
    Complex.continuous_re.comp_stronglyMeasurable
      ((Complex.continuous_conj.comp_stronglyMeasurable (Lp.stronglyMeasurable (ψ : PairState))).mul
        (Lp.stronglyMeasurable (S.pi 0 k ψ)))
  exact hc.smul ((MagHK.MonopoleCurrent.frame_continuous k).comp continuous_fst).stronglyMeasurable

theorem physicalCurrent_eq (S : MagneticFormSystem) (ψ : S.domain) (z : Space) :
    physicalCurrent S ψ z = MagHK.MonopoleCurrent.current S ψ (inverse z) := by
  unfold physicalCurrent MagHK.MonopoleCurrent.current
  congr 1
  exact integral_inverse (fun y => MagHK.MonopoleCurrent.pairCurrent S ψ (inverse z, y))
    ((pairCurrent_stronglyMeasurable S ψ).comp_measurable
      (measurable_const.prodMk measurable_id))

theorem current_stronglyMeasurable (S : MagneticFormSystem) (ψ : S.domain) :
    StronglyMeasurable (MagHK.MonopoleCurrent.current S ψ) :=
  (pairCurrent_stronglyMeasurable S ψ).integral_prod_right'.const_smul (2 : ℝ)

theorem physicalCurrent_measurable (S : MagneticFormSystem) (ψ : S.domain) :
    Measurable (physicalCurrent S ψ) := by
  have he : physicalCurrent S ψ = fun z => MagHK.MonopoleCurrent.current S ψ (inverse z) :=
    funext (physicalCurrent_eq S ψ)
  rw [he]
  exact ((current_stronglyMeasurable S ψ).comp_measurable inverse_measurable).measurable

theorem physicalCurrent_integrable (S : MagneticFormSystem) (ψ : S.domain) :
    Integrable (physicalCurrent S ψ) := by
  have he : physicalCurrent S ψ = fun z => MagHK.MonopoleCurrent.current S ψ (inverse z) :=
    funext (physicalCurrent_eq S ψ)
  rw [he]
  exact inverse_measurePreserving.integrable_comp_of_integrable
    (MagHK.MonopoleCurrent.current_integrable S ψ)

theorem physicalCurrent_chart (S : MagneticFormSystem) (ψ : S.domain) :
    (fun x => physicalCurrent S ψ (point x)) =ᵐ[chartMeasure] MagHK.MonopoleCurrent.current S ψ := by
  filter_upwards [inverse_point_ae] with x hx
  rw [physicalCurrent_eq, hx]
  rfl

theorem physicalCurrent_zero (S : MagneticFormSystem) (ψ : S.domain)
    (h : MagHK.MonopoleCurrent.current S ψ =ᵐ[chartMeasure] 0) :
    physicalCurrent S ψ =ᵐ[volume] 0 := by
  have hi := inverse_measurePreserving.quasiMeasurePreserving.ae h
  filter_upwards [hi] with z hz
  simpa only [physicalCurrent_eq, Pi.zero_apply] using hz

end MagHK.MonopoleInverse
