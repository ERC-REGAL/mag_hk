import MagHK.MonopoleTrial
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

/-! Concrete equal-area spherical coordinates. The meridian change of variables
is proved before invoking rotational invariance of the ambient volume. -/

noncomputable section
namespace MagHK.MonopoleGeometry

open MeasureTheory Set Filter
open scoped ENNReal NNReal
set_option maxHeartbeats 1000000

abbrev Pair := ℝ × ℝ

def meridianSource : Set Pair := Ioi (0 : ℝ) ×ˢ Ioo (-1 : ℝ) 1
def meridianTarget : Set Pair := Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)
def meridian (p : Pair) : Pair := (p.1 * Real.sqrt (1 - p.2 ^ 2), p.1 * p.2)
def meridianInv (p : Pair) : Pair :=
  (Real.sqrt (p.1 ^ 2 + p.2 ^ 2), p.2 / Real.sqrt (p.1 ^ 2 + p.2 ^ 2))

theorem meridian_root_pos (p : Pair) (hp : p ∈ meridianSource) : 0 < 1 - p.2 ^ 2 := by
  have hl : -1 < p.2 := hp.2.1
  have hu : p.2 < 1 := hp.2.2
  nlinarith

theorem meridian_mapsTo : MapsTo meridian meridianSource meridianTarget := by
  intro p hp
  exact ⟨mul_pos hp.1 (Real.sqrt_pos.mpr (meridian_root_pos p hp)), mem_univ _⟩

theorem meridianInv_mapsTo : MapsTo meridianInv meridianTarget meridianSource := by
  intro p hp
  have hpos : 0 < p.1 ^ 2 := sq_pos_of_pos hp.1
  have hr : 0 < Real.sqrt (p.1 ^ 2 + p.2 ^ 2) := Real.sqrt_pos.mpr (by nlinarith [sq_nonneg p.2])
  have hsq := Real.sq_sqrt (by positivity : 0 ≤ p.1 ^ 2 + p.2 ^ 2)
  have hz : |p.2| < Real.sqrt (p.1 ^ 2 + p.2 ^ 2) :=
    (sq_lt_sq₀ (abs_nonneg _) hr.le).mp (by rw [sq_abs]; nlinarith)
  rcases abs_lt.mp hz with ⟨hzl, hzu⟩
  exact ⟨hr, (lt_div_iff₀ hr).mpr (by linarith), (div_lt_iff₀ hr).mpr (by linarith)⟩

theorem meridian_left_inverse (p : Pair) (hp : p ∈ meridianSource) :
    meridianInv (meridian p) = p := by
  have hsq := Real.sq_sqrt (meridian_root_pos p hp).le
  have hr : (meridian p).1 ^ 2 + (meridian p).2 ^ 2 = p.1 ^ 2 := by
    unfold meridian
    dsimp
    nlinarith [congrArg (fun z : ℝ => p.1 ^ 2 * z) hsq]
  ext
  · change Real.sqrt ((meridian p).1 ^ 2 + (meridian p).2 ^ 2) = p.1
    rw [hr, Real.sqrt_sq hp.1.le]
  · change (meridian p).2 / Real.sqrt ((meridian p).1 ^ 2 + (meridian p).2 ^ 2) = p.2
    rw [hr, Real.sqrt_sq hp.1.le]
    change p.1 * p.2 / p.1 = p.2
    field_simp [ne_of_gt (show 0 < p.1 from hp.1)]

theorem meridian_right_inverse (p : Pair) (hp : p ∈ meridianTarget) :
    meridian (meridianInv p) = p := by
  have hmem := meridianInv_mapsTo hp
  have hr : 0 < Real.sqrt (p.1 ^ 2 + p.2 ^ 2) := hmem.1
  have hsq := Real.sq_sqrt (by positivity : 0 ≤ p.1 ^ 2 + p.2 ^ 2)
  have hroot := Real.sq_sqrt (meridian_root_pos (meridianInv p) hmem).le
  ext
  · apply (sq_eq_sq₀ (meridian_mapsTo hmem).1.le hp.1.le).mp
    change (Real.sqrt (p.1 ^ 2 + p.2 ^ 2) *
      Real.sqrt (1 - (p.2 / Real.sqrt (p.1 ^ 2 + p.2 ^ 2)) ^ 2)) ^ 2 = p.1 ^ 2
    change Real.sqrt (1 - (p.2 / Real.sqrt (p.1 ^ 2 + p.2 ^ 2)) ^ 2) ^ 2 =
      1 - (p.2 / Real.sqrt (p.1 ^ 2 + p.2 ^ 2)) ^ 2 at hroot
    rw [mul_pow, hroot]
    field_simp [hr.ne']
    nlinarith
  · change Real.sqrt (p.1 ^ 2 + p.2 ^ 2) *
      (p.2 / Real.sqrt (p.1 ^ 2 + p.2 ^ 2)) = p.2
    field_simp [hr.ne']

theorem meridian_injOn : InjOn meridian meridianSource := by
  intro p hp q hq he
  rw [← meridian_left_inverse p hp, he, meridian_left_inverse q hq]

theorem meridian_image : meridian '' meridianSource = meridianTarget := by
  apply Subset.antisymm
  · rintro _ ⟨p, hp, rfl⟩
    exact meridian_mapsTo hp
  · intro p hp
    exact ⟨meridianInv p, meridianInv_mapsTo hp, meridian_right_inverse p hp⟩

def meridianDerivative (p : Pair) : Pair →L[ℝ] Pair :=
  (Matrix.toLin (.finTwoProd ℝ) (.finTwoProd ℝ)
    !![Real.sqrt (1 - p.2 ^ 2), -p.1 * p.2 / Real.sqrt (1 - p.2 ^ 2);
      p.2, p.1]).toContinuousLinearMap

theorem meridian_hasFDerivAt (p : Pair) (hp : p ∈ meridianSource) :
    HasFDerivAt meridian (meridianDerivative p) p := by
  have hroot : HasDerivAt (fun μ : ℝ => Real.sqrt (1 - μ ^ 2))
      (-p.2 / Real.sqrt (1 - p.2 ^ 2)) p.2 := by
    convert! (((hasDerivAt_id p.2).pow 2).const_sub 1).sqrt
      (meridian_root_pos p hp).ne' using 1 <;> simp only [id_eq, Pi.pow_apply] <;> ring
  unfold meridianDerivative
  rw [Matrix.toLin_finTwoProd_toContinuousLinearMap]
  convert! HasFDerivAt.prodMk (𝕜 := ℝ)
    ((hasFDerivAt_fst (p := p) (𝕜 := ℝ)).mul
      (hroot.comp_hasFDerivAt p (hasFDerivAt_snd (p := p) (𝕜 := ℝ))))
    ((hasFDerivAt_fst (p := p) (𝕜 := ℝ)).mul (hasFDerivAt_snd (p := p) (𝕜 := ℝ))) using 2 <;>
    simp [meridian, smul_smul, add_comm, neg_mul, smul_neg]
  <;> ring

theorem meridianDerivative_det (p : Pair) (hp : p ∈ meridianSource) :
    (meridianDerivative p).det = p.1 / Real.sqrt (1 - p.2 ^ 2) := by
  have hsq := Real.sq_sqrt (meridian_root_pos p hp).le
  have hne := (Real.sqrt_pos.mpr (meridian_root_pos p hp)).ne'
  unfold meridianDerivative
  simp only [LinearMap.det_toContinuousLinearMap, LinearMap.det_toLin, Matrix.det_fin_two_of]
  field_simp
  nlinarith [congrArg (fun z : ℝ => p.1 * z) hsq]

/-- The cylindrical radius weight becomes r² under the meridian map. -/
theorem lintegral_meridian (f : Pair → ℝ≥0∞) :
    (∫⁻ p in meridianTarget, ENNReal.ofReal p.1 * f p) =
      ∫⁻ p in meridianSource, ENNReal.ofReal (p.1 ^ 2) * f (meridian p) := by
  rw [← meridian_image,
    lintegral_image_eq_lintegral_abs_det_fderiv_mul volume
      (measurableSet_Ioi.prod measurableSet_Ioo)
      (fun p hp => (meridian_hasFDerivAt p hp).hasFDerivWithinAt) meridian_injOn]
  apply setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo)
  intro p hp
  dsimp only
  rw [meridianDerivative_det p hp, abs_of_pos
    (div_pos hp.1 (Real.sqrt_pos.mpr (meridian_root_pos p hp)))]
  change ENNReal.ofReal (p.1 / Real.sqrt (1 - p.2 ^ 2)) *
    (ENNReal.ofReal (p.1 * Real.sqrt (1 - p.2 ^ 2)) * f (meridian p)) = _
  rw [← mul_assoc, ← ENNReal.ofReal_mul (div_nonneg (le_of_lt hp.1) (Real.sqrt_nonneg _))]
  congr 2
  field_simp [(Real.sqrt_pos.mpr (meridian_root_pos p hp)).ne']
  <;> ring

abbrev RawSpace := ℝ × ℂ

def circle (φ : ℝ) : ℂ := (Real.cos φ : ℂ) + (Real.sin φ : ℂ) * Complex.I
def cylinder (u φ : ℝ) : ℂ := (u : ℂ) * circle φ

def spherical (r : ℝ) (p : Pair) : RawSpace :=
  (r * p.1, cylinder (r * Real.sqrt (1 - p.1 ^ 2)) p.2)

theorem circle_continuous : Continuous circle := by unfold circle; fun_prop

theorem cylinder_continuous : Continuous (fun p : Pair => cylinder p.1 p.2) := by
  unfold cylinder
  exact (Complex.continuous_ofReal.comp continuous_fst).mul
    (circle_continuous.comp continuous_snd)

theorem spherical_continuous : Continuous (fun p : ℝ × Pair => spherical p.1 p.2) := by
  unfold spherical cylinder circle
  fun_prop

private theorem reverse_three {X Y Z : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    (μ : Measure X) (ν : Measure Y) (κ : Measure Z)
    [SFinite μ] [SFinite ν] [SFinite κ]
    (g : X × (Y × Z) → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ x, ∫⁻ y, ∫⁻ z, g (x, (y, z)) ∂κ ∂ν ∂μ) =
      ∫⁻ z, ∫⁻ y, ∫⁻ x, g (x, (y, z)) ∂μ ∂ν ∂κ := by
  calc
    _ = ∫⁻ x, ∫⁻ z, ∫⁻ y, g (x, (y, z)) ∂ν ∂κ ∂μ := by
      apply lintegral_congr_ae
      exact Eventually.of_forall (fun x => lintegral_lintegral_swap
        (show Measurable (fun p : Y × Z => g (x, (p.1, p.2))) by fun_prop).aemeasurable)
    _ = ∫⁻ z, ∫⁻ x, ∫⁻ y, g (x, (y, z)) ∂ν ∂μ ∂κ := by
      apply lintegral_lintegral_swap
      exact (show Measurable (fun p : X × Z => ∫⁻ y, g (p.1, (y, p.2)) ∂ν) by fun_prop).aemeasurable
    _ = _ := by
      apply lintegral_congr_ae
      exact Eventually.of_forall (fun z => lintegral_lintegral_swap
        (show Measurable (fun p : X × Y => g (p.1, (p.2, z))) by fun_prop).aemeasurable)

/-- An actual three-dimensional coordinate formula, expressed through two
successive two-dimensional Jacobian calculations. -/
theorem lintegral_spherical_open (f : RawSpace → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x : RawSpace, f x) =
      ∫⁻ r in Ioi (0 : ℝ), ∫⁻ μ in Ioo (-1 : ℝ) 1,
        ∫⁻ φ in Ioo (-Real.pi) Real.pi, ENNReal.ofReal (r ^ 2) * f (spherical r (μ, φ)) := by
  have hp (z : ℝ) : (∫⁻ w : ℂ, f (z, w)) =
      ∫⁻ u in Ioi (0 : ℝ), ∫⁻ φ in Ioo (-Real.pi) Real.pi,
        ENNReal.ofReal u * f (z, cylinder u φ) := by
    rw [← Complex.lintegral_comp_polarCoord_symm]
    simp only [Complex.polarCoord_symm_apply, smul_eq_mul]
    change (∫⁻ p : Pair in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
      ENNReal.ofReal p.1 * f (z, cylinder p.1 p.2)) = _
    rw [Measure.volume_eq_prod ℝ ℝ]
    exact setLIntegral_prod _ (show Measurable (fun p : Pair =>
      ENNReal.ofReal p.1 * f (z, cylinder p.1 p.2)) by
        exact (ENNReal.measurable_ofReal.comp measurable_fst).mul
          (hf.comp (measurable_const.prodMk cylinder_continuous.measurable))).aemeasurable
  have hm (φ : ℝ) :
      (∫⁻ u in Ioi (0 : ℝ), ∫⁻ z : ℝ, ENNReal.ofReal u * f (z, cylinder u φ)) =
        ∫⁻ r in Ioi (0 : ℝ), ∫⁻ μ in Ioo (-1 : ℝ) 1,
          ENNReal.ofReal (r ^ 2) * f (spherical r (μ, φ)) := by
    have h := lintegral_meridian (fun p => f (p.2, cylinder p.1 φ))
    unfold meridianTarget meridianSource at h
    rw [Measure.volume_eq_prod ℝ ℝ] at h
    have hmc : Continuous meridian := by unfold meridian; fun_prop
    have hmg : Measurable (fun p : Pair => f (p.2, cylinder p.1 φ)) := by
      unfold cylinder circle
      fun_prop
    have hml : Measurable (fun p : Pair => ENNReal.ofReal p.1 * f (p.2, cylinder p.1 φ)) :=
      (ENNReal.measurable_ofReal.comp measurable_fst).mul hmg
    have hmr : Measurable (fun p : Pair => ENNReal.ofReal (p.1 ^ 2) *
        f ((meridian p).2, cylinder (meridian p).1 φ)) :=
      (ENNReal.measurable_ofReal.comp (measurable_fst.pow_const 2)).mul (hmg.comp hmc.measurable)
    rw [setLIntegral_prod _ hml.aemeasurable, setLIntegral_prod _ hmr.aemeasurable] at h
    simpa only [setLIntegral_univ, meridian, spherical] using h
  calc
    _ = ∫⁻ z : ℝ, ∫⁻ w : ℂ, f (z, w) := by
      rw [Measure.volume_eq_prod ℝ ℂ, lintegral_prod _ hf.aemeasurable]
    _ = ∫⁻ z : ℝ, ∫⁻ u in Ioi (0 : ℝ), ∫⁻ φ in Ioo (-Real.pi) Real.pi,
        ENNReal.ofReal u * f (z, cylinder u φ) := by simp_rw [hp]
    _ = ∫⁻ φ in Ioo (-Real.pi) Real.pi, ∫⁻ u in Ioi (0 : ℝ), ∫⁻ z : ℝ,
        ENNReal.ofReal u * f (z, cylinder u φ) := by
      exact reverse_three (volume : Measure ℝ) (volume.restrict (Ioi (0 : ℝ)))
        (volume.restrict (Ioo (-Real.pi) Real.pi))
        (fun p : ℝ × (ℝ × ℝ) => ENNReal.ofReal p.2.1 * f (p.1, cylinder p.2.1 p.2.2))
        (by unfold cylinder circle; fun_prop)
    _ = ∫⁻ φ in Ioo (-Real.pi) Real.pi, ∫⁻ r in Ioi (0 : ℝ), ∫⁻ μ in Ioo (-1 : ℝ) 1,
        ENNReal.ofReal (r ^ 2) * f (spherical r (μ, φ)) := by simp_rw [hm]
    _ = ∫⁻ r in Ioi (0 : ℝ), ∫⁻ φ in Ioo (-Real.pi) Real.pi, ∫⁻ μ in Ioo (-1 : ℝ) 1,
        ENNReal.ofReal (r ^ 2) * f (spherical r (μ, φ)) := by
      apply lintegral_lintegral_swap
      apply Measurable.aemeasurable
      unfold spherical cylinder circle
      fun_prop
    _ = _ := by
      apply lintegral_congr_ae
      apply Eventually.of_forall
      intro r
      apply lintegral_lintegral_swap
      apply Measurable.aemeasurable
      unfold spherical cylinder circle
      fun_prop

end MagHK.MonopoleGeometry
