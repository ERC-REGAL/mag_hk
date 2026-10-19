import MagHK.CylindricalOrbitals
import Mathlib.Analysis.SpecialFunctions.PolarCoord

/-! Transport of the actual bounded orbitals to Cartesian Lebesgue measure on
ℂ × ℝ, with ℂ the Euclidean xy plane. -/
noncomputable section
namespace MagHK.CartesianOrbitals
open MeasureTheory Set
open MagHK.Noninteracting MagHK.Axial MagHK.CylindricalOrbitals
open scoped ComplexConjugate ENNReal NNReal
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

theorem polar_symm_continuous : Continuous (Complex.polarCoord.symm : ℝ × ℝ → ℂ) := by
  have h : (Complex.polarCoord.symm : ℝ × ℝ → ℂ) =
      (fun p => (p.1 : ℂ) * ((Real.cos p.2 : ℂ) + (Real.sin p.2 : ℂ) * Complex.I)) :=
    funext Complex.polarCoord_symm_apply
  rw [h]
  fun_prop

theorem radial_angular_measure : radialMeasure.prod angularMeasure =
    (volume.restrict polarCoord.target).withDensity (fun p => ENNReal.ofReal p.1) := by
  unfold radialMeasure angularMeasure
  rw [← restrict_Ioo_eq_restrict_Ioc]
  rw [prod_withDensity_left (measurable_real_toNNReal.coe_nnreal_ennreal),
    Measure.prod_restrict]
  rfl

theorem polar_measure_preserving :
    MeasurePreserving (Complex.polarCoord.symm : ℝ × ℝ → ℂ)
      (radialMeasure.prod angularMeasure) volume := by
  refine ⟨polar_symm_continuous.measurable, ?_⟩
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf polar_symm_continuous.measurable, radial_angular_measure]
  calc
    _ = ∫⁻ p in polarCoord.target,
        ENNReal.ofReal p.1 * f (Complex.polarCoord.symm p) :=
      lintegral_withDensity_eq_lintegral_mul _ (measurable_fst.ennreal_ofReal)
        (hf.comp polar_symm_continuous.measurable)
    _ = _ := Complex.lintegral_comp_polarCoord_symm f

def toCartesian (x : ℝ × (ℝ × ℝ)) : ℂ × ℝ :=
  (Complex.polarCoord.symm (x.1, x.2.1), x.2.2)

theorem toCartesian_measure_preserving :
    MeasurePreserving toCartesian cylindricalMeasure volume := by
  exact (polar_measure_preserving.prod (MeasurePreserving.id volume)).comp
    (MeasurePreserving.symm MeasurableEquiv.prodAssoc
      (measurePreserving_prodAssoc radialMeasure angularMeasure volume))

def orbitalZero (t c : ℝ) (x : ℂ × ℝ) : ℂ :=
  ((normalization t * profileF t ‖x.1‖ * chi c x.2 : ℝ) : ℂ)

def orbitalMinus (t c : ℝ) (x : ℂ × ℝ) : ℂ :=
  ((normalization t * Real.sqrt t * Real.exp (Real.sqrt (1 + ‖x.1‖ ^ 2) - 1) *
    profileF t ‖x.1‖ * chi c x.2 : ℝ) : ℂ) * conj x.1

theorem orbitalZero_continuous (t c : ℝ) (ht : 0 ≤ t) : Continuous (orbitalZero t c) := by
  apply Complex.continuous_ofReal.comp
  exact (continuous_const.mul ((profileF_continuous t ht).comp continuous_fst.norm)).mul
    ((chi_smooth c).continuous.comp continuous_snd)

theorem orbitalMinus_continuous (t c : ℝ) (ht : 0 ≤ t) : Continuous (orbitalMinus t c) := by
  unfold orbitalMinus
  have hf : Continuous (fun x : ℂ × ℝ => profileF t ‖x.1‖) :=
    (profileF_continuous t ht).comp continuous_fst.norm
  have hc : Continuous (fun x : ℂ × ℝ => chi c x.2) :=
    (chi_smooth c).continuous.comp continuous_snd
  fun_prop

theorem orbitalZero_pullback (t c : ℝ) (x : ℝ × (ℝ × ℝ)) (hr : 0 ≤ x.1) :
    orbitalZero t c (toCartesian x) = CylindricalOrbitals.orbitalZero t c x := by
  simp only [orbitalZero, toCartesian, Complex.norm_polarCoord_symm,
    abs_of_nonneg hr, CylindricalOrbitals.orbitalZero, radialZero]

theorem orbitalMinus_pullback (t c : ℝ) (x : ℝ × (ℝ × ℝ)) (hr : 0 ≤ x.1) :
    orbitalMinus t c (toCartesian x) = CylindricalOrbitals.orbitalMinus t c x := by
  simp only [orbitalMinus, toCartesian, Complex.norm_polarCoord_symm, abs_of_nonneg hr]
  simp only [Complex.polarCoord_symm_apply, map_mul, Complex.conj_ofReal,
    CylindricalOrbitals.orbitalMinus, radialMinus, profileR, phase, Complex.exp_mul_I]
  push_cast
  ring

theorem radial_positive_ae : ∀ᵐ r ∂radialMeasure, 0 < r := by
  exact (withDensity_absolutelyContinuous _ _).ae_le
    (self_mem_ae_restrict measurableSet_Ioi)

theorem cylindrical_positive_ae : ∀ᵐ x ∂cylindricalMeasure, 0 < x.1 :=
  Measure.quasiMeasurePreserving_fst.ae radial_positive_ae

theorem cartesian_integral (f : ℂ × ℝ → ℂ) (hf : Continuous f) :
    (∫ x, f x) = ∫ x, f (toCartesian x) ∂cylindricalMeasure := by
  rw [← toCartesian_measure_preserving.map_eq]
  exact integral_map_of_stronglyMeasurable toCartesian_measure_preserving.measurable
    hf.stronglyMeasurable

/-- Concrete Cartesian orbitals, normalized with respect to ordinary Lebesgue
volume on the Euclidean xy plane times the z axis. -/
theorem bounded_orthonormal (t c : ℝ) (ht : 0 < t) (hc : 0 < c)
    (heq : radialNormF t = radialNormG t) :
    MagHK.Slater.OrthonormalPair volume (orbitalZero t c) (orbitalMinus t c) := by
  have h := CylindricalOrbitals.bounded_orthonormal t c ht hc heq
  have hz : (fun x => orbitalZero t c (toCartesian x)) =ᵐ[cylindricalMeasure]
      CylindricalOrbitals.orbitalZero t c := by
    filter_upwards [cylindrical_positive_ae] with x hx
    exact orbitalZero_pullback t c x hx.le
  have hg : (fun x => orbitalMinus t c (toCartesian x)) =ᵐ[cylindricalMeasure]
      CylindricalOrbitals.orbitalMinus t c := by
    filter_upwards [cylindrical_positive_ae] with x hx
    exact orbitalMinus_pullback t c x hx.le
  have hff : (fun x => star (orbitalZero t c (toCartesian x)) * orbitalZero t c (toCartesian x))
      =ᵐ[cylindricalMeasure]
      (fun x => star (CylindricalOrbitals.orbitalZero t c x) *
        CylindricalOrbitals.orbitalZero t c x) := by
    filter_upwards [hz] with x hx
    rw [hx]
  have hgg : (fun x => star (orbitalMinus t c (toCartesian x)) * orbitalMinus t c (toCartesian x))
      =ᵐ[cylindricalMeasure]
      (fun x => star (CylindricalOrbitals.orbitalMinus t c x) *
        CylindricalOrbitals.orbitalMinus t c x) := by
    filter_upwards [hg] with x hx
    rw [hx]
  have hfg : (fun x => star (orbitalZero t c (toCartesian x)) * orbitalMinus t c (toCartesian x))
      =ᵐ[cylindricalMeasure]
      (fun x => star (CylindricalOrbitals.orbitalZero t c x) *
        CylindricalOrbitals.orbitalMinus t c x) := by
    filter_upwards [hz, hg] with x hx hy
    rw [hx, hy]
  have hgf : (fun x => star (orbitalMinus t c (toCartesian x)) * orbitalZero t c (toCartesian x))
      =ᵐ[cylindricalMeasure]
      (fun x => star (CylindricalOrbitals.orbitalMinus t c x) *
        CylindricalOrbitals.orbitalZero t c x) := by
    filter_upwards [hz, hg] with x hx hy
    rw [hx, hy]
  have hzc := orbitalZero_continuous t c ht.le
  have hgc := orbitalMinus_continuous t c ht.le
  have hffc : Continuous (fun x => star (orbitalZero t c x) * orbitalZero t c x) :=
    (Complex.continuous_conj.comp hzc).mul hzc
  have hggc : Continuous (fun x => star (orbitalMinus t c x) * orbitalMinus t c x) :=
    (Complex.continuous_conj.comp hgc).mul hgc
  have hfgc : Continuous (fun x => star (orbitalZero t c x) * orbitalMinus t c x) :=
    (Complex.continuous_conj.comp hzc).mul hgc
  have hgfc : Continuous (fun x => star (orbitalMinus t c x) * orbitalZero t c x) :=
    (Complex.continuous_conj.comp hgc).mul hzc
  constructor
  · exact (toCartesian_measure_preserving.integrable_comp hffc.aestronglyMeasurable).mp
      (h.integrable_ff.congr hff.symm)
  · exact (toCartesian_measure_preserving.integrable_comp hggc.aestronglyMeasurable).mp
      (h.integrable_gg.congr hgg.symm)
  · exact (toCartesian_measure_preserving.integrable_comp hfgc.aestronglyMeasurable).mp
      (h.integrable_fg.congr hfg.symm)
  · exact (toCartesian_measure_preserving.integrable_comp hgfc.aestronglyMeasurable).mp
      (h.integrable_gf.congr hgf.symm)
  · rw [cartesian_integral _ hffc, integral_congr_ae hff]
    exact h.norm_f
  · rw [cartesian_integral _ hggc, integral_congr_ae hgg]
    exact h.norm_g
  · rw [cartesian_integral _ hfgc, integral_congr_ae hfg]
    exact h.orthogonal_fg
  · rw [cartesian_integral _ hgfc, integral_congr_ae hgf]
    exact h.orthogonal_gf

theorem exists_bounded_orthonormal (c : ℝ) (hc : 0 < c) :
    ∃ t : ℝ, 0 < t ∧
      MagHK.Slater.OrthonormalPair volume (orbitalZero t c) (orbitalMinus t c) := by
  obtain ⟨t, ht, heq, _⟩ := exists_bounded_parameter
  exact ⟨t, ht, bounded_orthonormal t c ht hc heq⟩

end MagHK.CartesianOrbitals
