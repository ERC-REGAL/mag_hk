import MagHK.MonopoleCurrentAveraging

/-! Rotation invariance and radiality of the literal Euclidean density.
Radiality uses the same L¹ vector fixed-space theorem as the current proof,
by embedding a scalar density as its radial vector field. -/
noncomputable section
namespace MagHK.MonopoleDensity
open MeasureTheory Set Filter
open MagHK.MonopoleRealization MagHK.SpinChart MagHK.MonopoleInverse
open MagHK.MonopoleCovariance MagHK.MonopoleCoordinates
open scoped ComplexConjugate
set_option maxHeartbeats 1000000
abbrev Space := MagHK.MonopoleQuadrature.Space

private theorem normSq_integrable (ψ : FermionState) :
    Integrable (fun p => Complex.normSq ((ψ : PairState) p)) pairMeasure := by
  simpa only [real_inner_self_eq_norm_sq, Complex.normSq_eq_norm_sq] using
    (L2.integrable_inner (𝕜 := ℝ) (ψ : PairState) (ψ : PairState))

theorem physicalDensity_integrable (ψ : FermionState) : Integrable (physicalDensity ψ) := by
  exact (physicalWave_normSq_integrable ψ).integral_prod_left.const_mul (2 : ℝ)

theorem physicalDensity_measurable (ψ : FermionState) : Measurable (physicalDensity ψ) := by
  have hm : StronglyMeasurable (fun p : Space × Space => Complex.normSq (physicalWave ψ p)) :=
    Complex.continuous_normSq.comp_stronglyMeasurable
      ((Lp.stronglyMeasurable (ψ : PairState)).comp_measurable
        ((inverse_measurable.comp measurable_fst).prodMk (inverse_measurable.comp measurable_snd)))
  exact (hm.integral_prod_right'.const_smul (2 : ℝ)).measurable

theorem density_rotation (q : ℤ) (R : AngularMomentumAction q) (ψ : FermionState)
    (hfixed : ∀ U, R.pair U ψ = ψ) (U : MagHK.Spin.Group) :
    (fun x => MagHK.MonopoleTimeReversal.density ψ (movedChart U x)) =ᵐ[chartMeasure]
      MagHK.MonopoleTimeReversal.density ψ := by
  have hp : ∀ᵐ p ∂pairMeasure, Complex.normSq ((ψ : PairState) p) =
      Complex.normSq ((ψ : PairState) (movedPair U p)) := by
    have hw := R.pair_formula U ψ
    rw [hfixed U] at hw
    filter_upwards [hw] with p hp
    change (ψ : PairState) p = pairPhase q U p * (ψ : PairState) (movedPair U p) at hp
    rw [hp, Complex.normSq_mul, pairPhase_normSq, one_mul]
  have hpa := Measure.ae_ae_of_ae_prod hp
  have hi := (normSq_integrable ψ).prod_right_ae
  have him := (R.chart_measure U).quasiMeasurePreserving.ae hi
  filter_upwards [hpa, him] with x hx hix
  unfold MagHK.MonopoleTimeReversal.density
  congr 1
  have hm : AEStronglyMeasurable (fun y => Complex.normSq ((ψ : PairState) (movedChart U x, y)))
      (Measure.map (movedChart U) chartMeasure) := by
    rw [(R.chart_measure U).map_eq]
    exact hix.aestronglyMeasurable
  have he := integral_map (R.chart_measure U).measurable.aemeasurable hm
  rw [(R.chart_measure U).map_eq] at he
  exact he.trans (integral_congr_ae hx).symm

theorem physicalDensity_rotation (q : ℤ) (R : AngularMomentumAction q) (ψ : FermionState)
    (hfixed : ∀ U, R.pair U ψ = ψ) (U : MagHK.Spin.Group) :
    (fun z => physicalDensity ψ (R.rotation U⁻¹ z)) =ᵐ[volume] physicalDensity ψ := by
  have hmoved := (R.chart_measure U).quasiMeasurePreserving.ae (physicalDensity_chart ψ)
  have hchart : ∀ᵐ x ∂chartMeasure,
      physicalDensity ψ (R.rotation U⁻¹ (point x)) = physicalDensity ψ (point x) := by
    filter_upwards [hmoved, physicalDensity_chart ψ, density_rotation q R ψ hfixed U,
      Measure.quasiMeasurePreserving_snd.ae MagHK.MonopoleTrial.angle_ae] with x hm hj hc hx
    rw [← moved_point q R U x hx, hm, hc, hj]
  have hs : MeasurableSet {z : Space | physicalDensity ψ (R.rotation U⁻¹ z) = physicalDensity ψ z} :=
    measurableSet_eq_fun ((physicalDensity_measurable ψ).comp (R.rotation U⁻¹).continuous.measurable)
      (physicalDensity_measurable ψ)
  have h := (ae_map_iff point_continuous.measurable.aemeasurable hs).mpr hchart
  rwa [point_measurePreserving.map_eq] at h

theorem physicalDensity_proper_rotation (q : ℤ) (R : AngularMomentumAction q) (ψ : FermionState)
    (hfixed : ∀ U, R.pair U ψ = ψ) (Q : Space ≃ₗᵢ[ℝ] Space)
    (hQ : LinearMap.det Q.toLinearMap = 1) :
    (fun z => physicalDensity ψ (Q z)) =ᵐ[volume] physicalDensity ψ := by
  obtain ⟨V, hV⟩ := R.rotation_cover Q hQ
  simpa only [inv_inv, hV] using physicalDensity_rotation q R ψ hfixed V⁻¹

private theorem normalize_norm (x : Space) (hx : x ≠ 0) :
    ‖MagHK.MonopoleSphere.normalize x‖ = 1 := by
  simp [MagHK.MonopoleSphere.normalize, norm_smul, norm_ne_zero_iff.mpr hx]

private theorem normalize_norm_le (x : Space) : ‖MagHK.MonopoleSphere.normalize x‖ ≤ 1 := by
  by_cases hx : x = 0
  · simp [hx, MagHK.MonopoleSphere.normalize]
  · rw [normalize_norm x hx]

theorem physicalDensity_radial
    (averaging : MagHK.MonopoleCurrentAveraging.StandardRotationFixedSpaceLibrary)
    (q : ℤ) (R : AngularMomentumAction q) (ψ : FermionState)
    (hfixed : ∀ U, R.pair U ψ = ψ) :
    ∃ a : ℝ → ℝ, Measurable a ∧
      physicalDensity ψ =ᵐ[volume] fun x => a ‖x‖ := by
  let J : Space → Space := fun x => physicalDensity ψ x • MagHK.MonopoleSphere.normalize x
  have hJm : Measurable J := (physicalDensity_measurable ψ).smul MagHK.MonopoleSphere.normalize_measurable
  have hJi : Integrable J := by
    apply (physicalDensity_integrable ψ).norm.mono' hJm.aestronglyMeasurable
    filter_upwards [] with x
    change ‖physicalDensity ψ x • MagHK.MonopoleSphere.normalize x‖ ≤ ‖physicalDensity ψ x‖
    rw [norm_smul]
    exact mul_le_of_le_one_right (norm_nonneg _) (normalize_norm_le x)
  have hJR (Q : Space ≃ₗᵢ[ℝ] Space) (hQ : LinearMap.det Q.toLinearMap = 1) :
      (fun x => J (Q x)) =ᵐ[volume] fun x => Q (J x) := by
    filter_upwards [physicalDensity_proper_rotation q R ψ hfixed Q hQ] with x hx
    simp only [J, hx, MagHK.MonopoleSphere.normalize_isometry, map_smul]
  obtain ⟨a, ha, _, hrad⟩ := averaging J hJi hJR
  refine ⟨a, ha, ?_⟩
  have hn : ∀ᵐ x : Space, x ≠ 0 := ae_iff.mpr (by simp)
  filter_upwards [hrad, hn] with x hx hn
  have h := congrArg (inner ℝ (MagHK.MonopoleSphere.normalize x)) hx
  simpa only [J, real_inner_smul_right, real_inner_self_eq_norm_sq, normalize_norm x hn,
    one_pow, mul_one] using h

end MagHK.MonopoleDensity
