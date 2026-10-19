import MagHK.MonopoleQuadrature

/-! Actual rotational quadrature for the explicit monopole angular spinors. -/
noncomputable section
namespace MagHK.MonopolePairLaw

open MeasureTheory Set
open MagHK.MonopoleGeometry MagHK.MonopoleSphere MagHK.MonopoleQuadrature
open scoped ENNReal ComplexConjugate
set_option maxHeartbeats 1000000

abbrev Angle := MagHK.MonopoleTrial.Angle
abbrev sphereMeasure := MagHK.MonopoleTrial.sphereMeasure
abbrev cosineMeasure := MagHK.MonopoleTrial.cosineMeasure
abbrev azimuthMeasure := MagHK.MonopoleTrial.azimuthMeasure

def northPole : Space := WithLp.toLp 2 (1, 0)

theorem northPole_norm : ‖northPole‖ = 1 := by
  simp [northPole]

theorem northPole_inner (p : Angle) : inner ℝ northPole (direction p) = p.1 := by
  simp [northPole, direction, WithLp.prod_inner_apply, spherical]

theorem azimuthMeasure_univ : azimuthMeasure univ = ENNReal.ofReal (2 * Real.pi) := by
  change (volume.restrict (Ioc (-Real.pi) Real.pi)) univ = _
  rw [Measure.restrict_apply_univ, Real.volume_Ioc]
  congr 1
  ring

theorem sphereMeasure_univ : sphereMeasure univ = ENNReal.ofReal (4 * Real.pi) := by
  change (cosineMeasure.prod azimuthMeasure) univ = _
  rw [← univ_prod_univ, Measure.prod_prod, azimuthMeasure_univ]
  change (volume.restrict (Icc (-1 : ℝ) 1)) univ * ENNReal.ofReal (2 * Real.pi) = _
  rw [Measure.restrict_apply_univ, Real.volume_Icc,
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 - -1)]
  congr 1
  ring

theorem northPole_projection :
    Measure.map (fun x : Space => inner ℝ northPole x)
      (Measure.map direction sphereMeasure) =
      ENNReal.ofReal (2 * Real.pi) • cosineMeasure := by
  have hm : Measurable (fun x : Space => inner ℝ northPole x) :=
    (continuous_const.inner continuous_id).measurable
  rw [Measure.map_map hm direction_continuous.measurable]
  have he : (fun x : Space => inner ℝ northPole x) ∘ direction = Prod.fst := by
    funext p
    exact northPole_inner p
  rw [he]
  change Measure.map Prod.fst (cosineMeasure.prod azimuthMeasure) = _
  rw [Measure.map_fst_prod, azimuthMeasure_univ]

theorem unit_projection (n : Space) (hn : ‖n‖ = 1) :
    Measure.map (fun x : Space => inner ℝ n x)
      (Measure.map direction sphereMeasure) =
      ENNReal.ofReal (2 * Real.pi) • cosineMeasure := by
  let R := Submodule.reflection (ℝ ∙ (n - northPole))ᗮ
  have hR : R n = northPole := Submodule.reflection_sub (hn.trans northPole_norm.symm)
  have he : (fun x : Space => inner ℝ northPole x) ∘ R = fun x => inner ℝ n x := by
    funext x
    change inner ℝ northPole (R x) = inner ℝ n x
    rw [← hR, R.inner_map_map]
  have hm : Measurable (fun x : Space => inner ℝ northPole x) :=
    (continuous_const.inner continuous_id).measurable
  calc
    _ = Measure.map (fun x : Space => inner ℝ northPole x)
        (Measure.map R (Measure.map direction sphereMeasure)) := by
      rw [Measure.map_map hm R.continuous.measurable, he]
    _ = _ := by rw [directionMeasure_invariant, northPole_projection]

theorem sqrt_amplitudes (μ : ℝ) (hμ : μ ∈ Icc (-1 : ℝ) 1) :
    2 * Real.sqrt ((1 + μ) / 2) * Real.sqrt ((1 - μ) / 2) = Real.sqrt (1 - μ ^ 2) := by
  have hp : 0 ≤ (1 + μ) / 2 := by linarith [hμ.1]
  have hm : 0 ≤ (1 - μ) / 2 := by linarith [hμ.2]
  have hq : 0 ≤ 1 - μ ^ 2 := by nlinarith [hμ.1, hμ.2]
  apply (sq_eq_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp
  rw [mul_pow, mul_pow, Real.sq_sqrt hp, Real.sq_sqrt hm, Real.sq_sqrt hq]
  ring

theorem circle_eq_star_phase (φ : ℝ) :
    circle φ = star (MagHK.CylindricalOrbitals.phase φ) := by
  simp [circle, MagHK.CylindricalOrbitals.phase, Complex.star_def,
    Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]

theorem direction_complex (p : Angle) (hp : p.1 ∈ Icc (-1 : ℝ) 1) :
    (WithLp.ofLp (direction p)).2 =
      2 * MagHK.MonopoleTrial.spinorPlus p * star (MagHK.MonopoleTrial.spinorMinus p) := by
  simp only [direction, spherical, cylinder, one_mul, WithLp.ofLp_toLp]
  rw [← sqrt_amplitudes p.1 hp, circle_eq_star_phase]
  simp [MagHK.MonopoleTrial.spinorPlus, MagHK.MonopoleTrial.spinorMinus, map_mul]
  ring

theorem pairDot_eq_inner (p q : Angle) (hp : p.1 ∈ Icc (-1 : ℝ) 1)
    (hq : q.1 ∈ Icc (-1 : ℝ) 1) :
    MagHK.MonopoleTrial.pairDot (p, q) = inner ℝ (direction p) (direction q) := by
  rw [WithLp.prod_inner_apply, direction_complex p hp, direction_complex q hq]
  have hpz := MagHK.MonopoleTrial.direction_third p hp
  have hqz := MagHK.MonopoleTrial.direction_third q hq
  rw [MagHK.MonopoleTrial.pairDot_eq_dot, Complex.inner]
  simp only [direction, spherical, WithLp.ofLp_toLp, one_mul, real_inner_comm,
    RCLike.inner_apply, conj_trivial]
  rw [← hpz, ← hqz]
  simp [MagHK.MonopoleTrial.direction, Complex.mul_re, Complex.mul_im, Complex.star_def]
  ring

theorem pairInner_quadrature :
    Measure.map (fun p : Angle × Angle => inner ℝ (direction p.1) (direction p.2))
      (sphereMeasure.prod sphereMeasure) =
      ENNReal.ofReal (8 * Real.pi ^ 2) • cosineMeasure := by
  apply Measure.ext_of_lintegral
  intro f hf
  have hi : Measurable (fun p : Angle × Angle => inner ℝ (direction p.1) (direction p.2)) :=
    ((direction_continuous.comp continuous_fst).inner
      (direction_continuous.comp continuous_snd)).measurable
  rw [lintegral_map hf hi]
  have hfi : Measurable (fun p : Angle × Angle => f (inner ℝ (direction p.1) (direction p.2))) :=
    hf.comp hi
  rw [lintegral_prod _ hfi.aemeasurable]
  have hs : (fun p : Angle => ∫⁻ q, f (inner ℝ (direction p) (direction q)) ∂sphereMeasure) =ᵐ[sphereMeasure]
      fun _ => ENNReal.ofReal (2 * Real.pi) * ∫⁻ μ, f μ ∂cosineMeasure := by
    filter_upwards [MagHK.MonopoleTrial.angle_ae] with p hp
    have hproj := unit_projection (direction p) (direction_norm p hp)
    have hm : Measurable (fun x : Space => inner ℝ (direction p) x) :=
      (continuous_const.inner continuous_id).measurable
    have hfd : Measurable (fun x : Space => f (inner ℝ (direction p) x)) := hf.comp hm
    rw [← lintegral_map hfd direction_continuous.measurable,
      ← lintegral_map hf hm, hproj, lintegral_smul_measure, smul_eq_mul]
  rw [lintegral_congr_ae hs, lintegral_const, sphereMeasure_univ,
    lintegral_smul_measure, smul_eq_mul]
  rw [mul_right_comm, ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  ring

/-- The spherical pair quadrature is a theorem of the literal chart measure. -/
theorem sphericalPairQuadrature : MagHK.MonopoleTrial.SphericalPairQuadrature := by
  unfold MagHK.MonopoleTrial.SphericalPairQuadrature
  change Measure.map MagHK.MonopoleTrial.pairDot (sphereMeasure.prod sphereMeasure) =
    ENNReal.ofReal (8 * Real.pi ^ 2) • cosineMeasure
  rw [← pairInner_quadrature]
  apply Measure.map_congr
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae MagHK.MonopoleTrial.angle_ae,
    Measure.quasiMeasurePreserving_snd.ae MagHK.MonopoleTrial.angle_ae] with p hp hq
  exact pairDot_eq_inner p.1 p.2 hp hq

theorem angularCoulomb_eq_kernel (s t : ℝ) (hs : 0 < s) (ht : 0 < t) :
    MagHK.MonopoleTrial.angularCoulomb s t = MagHK.Monopole.angularKernel s t :=
  MagHK.MonopoleTrial.angularCoulomb_eq_kernel sphericalPairQuadrature s t hs ht

theorem trialCoulombIterated_bound :
    MagHK.MonopoleTrial.trialCoulombIterated ≤ MagHK.Monopole.coulombBound :=
  (MagHK.MonopoleTrial.trialCoulombIterated_bound sphericalPairQuadrature).1

end MagHK.MonopolePairLaw
