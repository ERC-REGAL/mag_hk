import MagHK.MonopoleEndpointDomains

/-! The radial substitution u(r)Y(ω)/r as an actual L² isometry. The result
is derived from the spherical volume element and product integration. -/
noncomputable section
namespace MagHK.MonopoleRadialIsometry
open MeasureTheory Set Filter
open MagHK.MonopoleRealization MagHK.MonopoleTrial MagHK.MonopoleEndpointDomains

def lift (u : ℝ → ℂ) (Y : Angle → ℂ) (x : Chart) : ℂ :=
  u x.1 / (x.1 : ℂ) * Y x.2

/-- The exact cancellation of the radial Jacobian, before taking L² norms. -/
theorem lift_mass (u : ℝ → ℂ) (Y : Angle → ℂ) :
    (∫ x, Complex.normSq (lift u Y x) ∂chartMeasure) =
      (∫ r in Ioi (0 : ℝ), Complex.normSq (u r)) * (∫ p, Complex.normSq (Y p) ∂sphereMeasure) := by
  simp only [lift, Complex.normSq_mul, chartMeasure]
  rw [integral_prod_mul (fun r : ℝ => Complex.normSq (u r / (r : ℂ)))
    (fun p : Angle => Complex.normSq (Y p)), radialVolume_integral]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  dsimp only
  rw [Complex.normSq_div, Complex.normSq_ofReal]
  field_simp [ne_of_gt (show 0 < r from hr)]
  <;> ring

private theorem mass {X : Type*} [MeasurableSpace X] (μ : Measure X) (u : Lp ℂ 2 μ) :
    (∫ x, Complex.normSq (u x) ∂μ) = ‖u‖ ^ 2 := by
  calc
    _ = ∫ x, inner ℝ (u x) (u x) ∂μ := by
      simp only [real_inner_self_eq_norm_sq, Complex.normSq_eq_norm_sq]
    _ = inner ℝ u u := rfl
    _ = ‖u‖ ^ 2 := real_inner_self_eq_norm_sq u

private theorem mass_integrable {X : Type*} [MeasurableSpace X] (μ : Measure X) (u : Lp ℂ 2 μ) :
    Integrable (fun x => Complex.normSq (u x)) μ := by
  simpa only [real_inner_self_eq_norm_sq, Complex.normSq_eq_norm_sq] using
    (L2.integrable_inner (𝕜 := ℝ) u u)

theorem lift_stronglyMeasurable (u : RadialState) (Y : Lp ℂ 2 sphereMeasure) :
    StronglyMeasurable (lift u Y) := by
  exact (((Lp.stronglyMeasurable u).comp_measurable measurable_fst).div
    ((Complex.continuous_ofReal.comp continuous_fst).stronglyMeasurable)).mul
      ((Lp.stronglyMeasurable Y).comp_measurable measurable_snd)

theorem lift_memLp (u : RadialState) (Y : Lp ℂ 2 sphereMeasure) :
    MemLp (lift u Y) 2 chartMeasure := by
  have hm : Measurable (fun r : ℝ => Real.toNNReal (r ^ 2)) := by fun_prop
  have hu : Integrable (fun r => Complex.normSq (u r / (r : ℂ))) radialVolume := by
    apply (integrable_withDensity_iff_integrable_smul hm).mpr
    apply (mass_integrable radialMeasure u).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    simp only [NNReal.smul_def, Real.coe_toNNReal _ (sq_nonneg _), smul_eq_mul,
      Complex.normSq_div, Complex.normSq_ofReal]
    field_simp [ne_of_gt (show 0 < r from hr)]
    <;> ring
  apply (memLp_two_iff_integrable_sq_norm (lift_stronglyMeasurable u Y).aestronglyMeasurable).mpr
  simpa only [lift, Complex.normSq_mul, Complex.normSq_eq_norm_sq, chartMeasure, norm_mul, mul_pow] using
    hu.mul_prod (mass_integrable sphereMeasure Y)

/-- The actual L² vector obtained from the radial substitution. -/
def liftState (u : RadialState) (Y : Lp ℂ 2 sphereMeasure) : State :=
  (lift_memLp u Y).toLp (lift u Y)

theorem liftState_mass (u : RadialState) (Y : Lp ℂ 2 sphereMeasure) :
    ‖liftState u Y‖ ^ 2 = ‖u‖ ^ 2 * ‖Y‖ ^ 2 := by
  rw [← mass chartMeasure]
  have he := (lift_memLp u Y).coeFn_toLp
  have hex : (fun x => Complex.normSq (liftState u Y x)) =ᵐ[chartMeasure]
      (fun x => Complex.normSq (lift u Y x)) := by
    filter_upwards [he] with x hx
    exact congrArg Complex.normSq hx
  rw [integral_congr_ae hex, lift_mass, mass radialMeasure u, mass sphereMeasure Y]

theorem liftState_norm (u : RadialState) (Y : Lp ℂ 2 sphereMeasure) (hY : ‖Y‖ = 1) :
    ‖liftState u Y‖ = ‖u‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [liftState_mass, hY]
  ring

end MagHK.MonopoleRadialIsometry
